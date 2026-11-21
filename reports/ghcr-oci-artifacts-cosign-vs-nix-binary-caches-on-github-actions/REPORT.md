# GHCR (`ghcr.io`) & OCI Artifacts (`oras` / Cosign) vs. Nix Binary Caches on GitHub Actions

## Summary

- **GHCR authentication, fork visibility, and billing:** Public GHCR packages pull anonymously or with read-only `GITHUB_TOKEN`; public fork PRs cannot push (`GITHUB_TOKEN` is downgraded to read-only), **but** if a public repository is granted Actions access to a *private* GHCR package, forks of that public repo can pull that private package. Making a GHCR package public is irreversible. Container registry storage and bandwidth are currently free (with 1 month's advance notice before policy changes), with hard limits of **10 GB per layer** and **10-minute upload timeout**, and no published numeric public pull rate-limit table.
- **BuildKit `type=registry` dominates `type=gha` and `upload-artifact` + `docker save`/`load`:** `type=registry` (defaulting to `oci-mediatypes=true` and `image-manifest=true` since BuildKit `v0.21`) skips unchanged base/toolchain layers by content digest, streams blobs in parallel, avoids the 10 GB / 7-day GHA Cache cap, and shares layers across PRs, `merge_group`, and local dev. `type=gha` shares the 10 GB / 7-day GHA cache and cannot compose PR → `merge_group`. `upload-artifact` + `docker save`/`load` transfers a monolithic tarball with zero layer deduplication, 2× disk overhead, and shared Packages+Artifacts quota (`$0.25/GB-month` overage).
- **OCI Artifacts (`oras` + Cosign) on GHCR have a live Referrers API gap and concurrency race:** A live probe confirmed `GET https://ghcr.io/v2/<repo>/referrers/<digest>` returns **`HTTP 404`** (`MANIFEST_UNKNOWN`). Both `cosign@v3.1.4` (defaulting to `--new-bundle-format=true` OCI 1.1 referrers via `go-containerregistry@v0.22.1`) and `oras@v1.4.0` fall back to client-side read-modify-write updates on the **`sha256-<hex>`** referrers index tag, which has **no concurrency protection** — parallel matrix jobs attaching to the same subject digest on GHCR can clobber each other. GHCR also lacks native tag immutability, lacks automatic untagged-manifest GC, and permanently blocks API deletion of public package versions with **>5,000 downloads**.
- **Nix binary caches vs. GHCR on `ubuntu-24.04` (14 GB free SSD):** Nix cold install takes ~4–10s (faster than cold-pulling multi-GB OCI images), fetches only each job shard's exact transitive closure onto the 14 GB disk (whereas monolithic Docker images unpack all baked toolchains into `/var/lib/docker/overlay2`), and Attic provides FastCDC chunk-level global deduplication (`64 KiB` avg) with closure-safe GC. Raw S3/R2 object-age lifecycle rules are **unsafe** for Nix caches because expiring old referenced NARs violates the Nix closure invariant.

## Applicability

This report compares GHCR (`ghcr.io`), BuildKit, OCI artifacts (`oras` + Cosign), and Nix binary-cache backends (Attic, Cachix, raw S3/R2) on GitHub-hosted `ubuntu-24.04` runners across the 13 subjects in `REPORT.json`. Protocol observations on `https://ghcr.io` reflect live behavior on `2026-11-21`; billing and feature policies reflect `github/docs@d7487f5debb5a5a2a6e65e6f9fa539266f5f8db6`.

## Findings

### 1. GHCR (`ghcr.io`) Authentication, Limits, and BuildKit Caching

#### 1.1 `GITHUB_TOKEN` Authentication Matrix and Visibility Traps

Basis: documentation (`github/docs@d7487f5d`) + execution (live `ghcr.io` anonymous token probe)

Publishing a GHCR package via `${{ secrets.GITHUB_TOKEN }}` automatically links the workflow's repository with `admin` role; pushing to a pre-existing unlinked package in the same namespace fails until the repository is granted `Write`/`Admin` access in package settings (*Manage Actions access*).

| Trigger Event | Pull **Public** GHCR Package | Pull **Private** GHCR Package (linked to repo) | Push to GHCR (`packages: write`) |
| :--- | :--- | :--- | :--- |
| **`pull_request` (public fork PR)** | **Yes** — anonymous Bearer token (`GET https://ghcr.io/token?service=ghcr.io&scope=repository:<owner>/<pkg>:pull`, verified `HTTP 200`) or read-only `GITHUB_TOKEN`. | **Yes, if the public repo was granted Actions access to the private package** (`public-forks-private-packages.md:1` explicitly warns that forks of a public repo may access private packages granted to that repo). | **No** (`GITHUB_TOKEN` downgraded to read-only). |
| **`pull_request` (same-repo PR)** | **Yes**. | **Yes** (with `packages: read` and repo access). | **Yes** (with `packages: write` and repo Write/Admin role). |
| **`pull_request` (private-repo fork PR)** | **Yes**. | **Yes** (if fork workflows enabled). | **No by default** (requires *"Send write tokens to workflows from pull requests"*). |
| **`merge_group` / `push`** | **Yes**. | **Yes** (with `packages: read` and repo access). | **Yes** (with `packages: write` and repo Write/Admin role). |

- **Irreversible visibility:** Newly published GHCR packages default to Private; once made Public, a GHCR package **cannot be made Private again** (`configuring-a-packages-access-control-and-visibility.md:179-216`).

#### 1.2 Storage, Bandwidth, Pricing, and Hard Transfer Limits

Basis: documentation (`github/docs@d7487f5d`: `github-packages.md`, `github-actions.md`, `working-with-the-container-registry.md:250-251`)

- **Container Registry billing exception (`github-packages.md:64`):** Container image storage and bandwidth on `ghcr.io` are currently free, with GitHub committing to at least **1 month's advance notice** before any policy change.
- **Shared Packages + Actions Artifacts quotas (if billing applies, or for Actions Artifacts):** Public packages are always free; ingress is always free. Private monthly pools: **500 MB / 1 GB** (Free), **2 GB / 10 GB** (Pro/Team), **50 GB / 100 GB** (GHEC); overages are **`$0.25/GB-month`** for shared Packages+Artifacts storage (separate from Actions Cache at `$0.07/GB-month`). Downloading private packages via `GITHUB_TOKEN` is free on both GitHub-hosted and self-hosted runners (PAT downloads are free on GitHub-hosted, billed on self-hosted).
- **Hard GHCR limits:** **10 GB max per individual layer**; **10-minute upload timeout** per upload (`working-with-the-container-registry.md:250-251`). No fixed numeric public pull rate-limit table is published (standard API/secondary abuse limits apply).

#### 1.3 BuildKit `type=registry` vs. `type=gha` vs. `actions/upload-artifact` + `docker save`/`load`

Basis: source + documentation (`moby/buildkit@v0.35.1`, `actions/upload-artifact@v7.0.2`) + derived

| Dimension | BuildKit `type=registry` on GHCR (`mode=max`, `compression=zstd`) | BuildKit `type=gha` (`mode=max`) | `actions/upload-artifact` + `docker save` / `load` |
| :--- | :--- | :--- | :--- |
| **Transfer unit & dedup** | **Per-layer content-addressed OCI blobs:** resolves manifest, skips unchanged base/toolchain layers via digest `HEAD`, streams missing layers in parallel. | **Per-blob GHA Cache keys** (`buildkit-blob-1-<digest>` in `gha.go:177-197, 534`). | **Monolithic tarball:** serializes every layer (including unchanged base layers), zips by default, unpacks sequentially with 2× disk overhead. |
| **Storage cap & TTL** | Outside 10 GB GHA cache; GHCR currently free (10 GB/layer, 10 min upload timeout); no 7-day auto-eviction. | Shares **10 GB/repo** GHA cache + **7-day unused eviction** + LRU thrashing. | Shares **Packages+Artifacts pool** (500 MB Free / 2 GB Team / 50 GB GHEC, `$0.25/GB-mo`); 1–90d TTL (up to 400d private). |
| **GHCR compatibility** | Defaults to `oci-mediatypes=true` and `image-manifest=true` since BuildKit `v0.21` (`README.md:511-513`); `compression=zstd` requires `oci-mediatypes=true`. | Uses GHA Cache API v2 (`ACTIONS_RUNTIME_TOKEN`). | Single workflow-run scope only. |
| **Cross-PR / `merge_group` / local reuse** | **Yes** (PRs pull read-only; `merge_group`/`push` update). | **No** PR → `merge_group` or local dev reuse. | **No** cross-run sharing. |

### 2. OCI Artifacts (`oras` + Cosign) as a Zero-Server Signed CAS on GHCR

#### 2.1 Live GHCR OCI 1.1 Referrers API Gap and Tag-Schema Race Condition

Basis: normative (`opencontainers/distribution-spec@v1.1.1`) + source (`oras-project/oras@v1.4.0`, `sigstore/cosign@v3.1.4`, `google/go-containerregistry@v0.22.1`) + execution (live `ghcr.io` probe)

- GHCR accepts OCI 1.1 Image Manifests carrying `artifactType`, `subject`, and custom layer media types (`oras push` / `oras attach`).
- **Live execution probe (`2026-11-21`):**
  - `GET https://ghcr.io/v2/oras-project/oras/manifests/v1.4.0` → **`HTTP 200`** (`Docker-Content-Digest: sha256:5fabb4e523de1781443c227fca62782a51aeacd044413c07f54dc64935d7f013`).
  - `GET https://ghcr.io/v2/oras-project/oras/referrers/sha256:5fabb4e523de1781443c227fca62782a51aeacd044413c07f54dc64935d7f013` → **`HTTP 404`** (`MANIFEST_UNKNOWN`).
- **Concurrency race condition:** Because GHCR does not implement the OCI 1.1 Referrers API, both `oras@v1.4.0` (`remote.go:615`, also setting `SkipReferrersGC = true`) and `cosign@v3.1.4` (whose new default `--new-bundle-format=true` at `sign.go:161` pushes Sigstore v0.3 bundles as OCI 1.1 referrers via `go-containerregistry@v0.22.1` `writer.commitSubjectReferrers()`) fall back to the **Referrers Tag Schema (`sha256-<64-hex>`)**. Per `distribution-spec@v1.1.1` (`spec.md:737`), updating this tag is an **unprotected client-side read-modify-write**; parallel CI matrix jobs attaching signatures or attestations to the same subject digest on GHCR can silently clobber each other. (Legacy `--new-bundle-format=false` uses `sha256-<hex>.sig` / `.att`, avoiding multi-referrer index merges for single signatures but still read-modify-writing on concurrent writes to the same `.sig` tag.)
- **Cosign signing modes:** Keyless OIDC (`id-token: write`, Fulcio + Rekor, pinned via `--certificate-identity-regexp` and `--certificate-oidc-issuer https://token.actions.githubusercontent.com`) eliminates static keys and naturally excludes public fork PRs; static keys (`--key`, Ed25519/ECDSA/KMS) enable offline verification without Fulcio/Rekor but require secret management.

#### 2.2 GHCR Immutability and Garbage Collection Limits

Basis: documentation (`github/docs@d7487f5d`: `deleting-and-restoring-a-package.md:24-53`) + derived

| Property | Exact GHCR Behavior | CAS Implication |
| :--- | :--- | :--- |
| **Native tag immutability** | **None.** Any `packages: write` caller can overwrite any tag. | Never trust mutable tags as CAS pointers without `@sha256:...` digest pinning or Cosign signature verification binding digest + cache key. |
| **Automatic untagged-manifest GC** | **None.** Overwritten tags and superseded `sha256-<hex>` referrer indexes accumulate indefinitely. | Requires scheduled cleanup via Packages REST API (`admin` role) or `actions/delete-package-versions`. |
| **>5,000-download deletion lock** | **Hard block (`deleting-and-restoring-a-package.md:25-30`):** Public packages/versions with **>5,000 downloads cannot be deleted** via API (requires GitHub Support). | Heavily pulled public cache versions become permanently undeletable via API. |

### 3. Comparison vs. Nix Binary-Cache Substitution on `ubuntu-24.04`

Basis: source (`zhaofengli/attic@7a19204d`) + documentation (`DeterminateSystems/nix-installer-action@v23`, `cachix/install-nix-action@v32.0.0`) + derived

1. **Cold-start latency:** `cachix/install-nix-action@v32.0.0` (~4–10s) and `DeterminateSystems/nix-installer-action@v23` (~4–9s typical, ~15–30s under variance) install Nix faster than cold-pulling a multi-GB GHCR container image (~30–180+s) unless the image eliminates even larger Nix substitutions.
2. **14 GB free SSD budget on standard `ubuntu-24.04`:** Combining multiple Rust toolchains (2–5 GB) + Lean 4 / Mathlib `.olean`s (2–6 GB) + `cargoArtifacts` / `target/` (2–6 GB) totals **6–17 GB unpacked**. Monolithic OCI images unpack all baked toolchains into `/var/lib/docker/overlay2` (plus download buffers or 2× duplication under `docker load`), whereas Nix fetches only each shard's exact transitive closure into `/nix/store`. Reclaiming ~20–30 GB by deleting `/usr/share/dotnet`, `/opt/ghc`, `/usr/local/lib/android`, etc., adds ~15–60s I/O per job and couples workflows to undocumented runner-image paths.
3. **Deduplication and GC comparison:**

| Backend | Deduplication Granularity | Compression | Garbage Collection & Safety |
| :--- | :--- | :--- | :--- |
| **Attic** (`zhaofengli/attic@7a19204d`) | **Global FastCDC chunks** (`config-template.toml`: `nar-size-threshold = 64 KiB`, `min = 16 KiB`, `avg = 64 KiB`, `max = 256 KiB`) across all logical caches. | Zstd (default level 8) | **Closure-safe server-side GC (`gc.rs:35-272`):** periodic (`12h`) retention expiry + `FOR UPDATE SKIP LOCKED` orphan chunk reaping. |
| **Cachix** | **Per-store-path (NAR-level).** | Zstd / XZ | Managed LRU GC when plan cap is hit; supports `cachix pin`. |
| **Raw S3 / R2 (`s3://`)** | **Per-store-path (NAR-level).** | Zstd / XZ | **Object-age TTL lifecycle rules are UNSAFE:** expiring old referenced dependency NARs violates the Nix closure invariant (`404` failures); requires a reachability-aware sweeper. |
| **GHCR + OCI (`docker` / `oras`)** | **Per-layer / per-blob** (no sub-layer chunking in stock GHA `docker`). | Gzip or Zstd (`oci-mediatypes=true`) | **No auto-GC**; manual API cleanup (`admin` role); **>5,000-download public versions undeletable**. |

## Boundaries

- **Live Azure-to-GHCR vs. R2/S3/Cachix download throughput (`not examined`):** Wall-clock MB/s from GitHub-hosted `ubuntu-24.04` runners was not benchmarked; only `ghcr.io` protocol/Referrers API behavior was probed live.
- **Lazy-pull OCI formats (`estargz` / `zstd:chunked` / `nydus`) (`not examined`):** Standard GitHub-hosted `ubuntu-24.04` Docker `28.0.4` does not enable lazy snapshotters by default; custom self-hosted containerd lazy-pull setups were not evaluated.
- **GHCR future pricing (`unknown`):** Container storage/bandwidth is currently free under a revocable 1-month-notice policy.

## Evidence

All evidence was gathered or executed on `2026-11-21`:

- **`github/docs@d7487f5debb5a5a2a6e65e6f9fa539266f5f8db6`:** `working-with-the-container-registry.md` (L91–93, L250–251), `configuring-a-packages-access-control-and-visibility.md` (L179–216), `deleting-and-restoring-a-package.md` (L24–53), `data/reusables/package_registry/public-forks-private-packages.md` (L1), `content/billing/concepts/product-billing/github-packages.md` (L24–77), `github-actions.md` (L169–173).
- **Live `ghcr.io` HTTP probe (`2026-11-21`):** Anonymous token `GET https://ghcr.io/token?service=ghcr.io&scope=repository:oras-project/oras:pull` (`HTTP 200`); `GET https://ghcr.io/v2/oras-project/oras/manifests/v1.4.0` (`HTTP 200`, `sha256:5fabb4e523de1781443c227fca62782a51aeacd044413c07f54dc64935d7f013`); `GET https://ghcr.io/v2/oras-project/oras/referrers/sha256:5fabb4e523de1781443c227fca62782a51aeacd044413c07f54dc64935d7f013` (`HTTP 404`, `MANIFEST_UNKNOWN`).
- **`opencontainers/distribution-spec@v1.1.1` (`a139cc42`):** `spec.md` L499, L733–751 (Referrers Tag Schema non-atomic concurrency warning).
- **`moby/buildkit@v0.35.1` (`412cc86a`):** `README.md` L283–308, L465–579; `cache/remotecache/gha/gha.go` L177–197, L534; `cache/remotecache/registry/registry.go`.
- **`oras-project/oras@v1.4.0` (`fdeb304d`):** `cmd/oras/internal/option/remote.go` L615–617 (`SkipReferrersGC = true`).
- **`sigstore/cosign@v3.1.4` (`0e48502c`) & `google/go-containerregistry@v0.22.1`:** `cosign` `cmd/cosign/cli/options/sign.go` L72–171, `pkg/oci/remote/write.go` L77–96, L314–485, `specs/SIGNATURE_SPEC.md` L153–169; `go-containerregistry` `pkg/v1/remote/write.go` L514–668 (`commitSubjectReferrers`).
- **`zhaofengli/attic@7a19204d`:** `server/src/config.rs` L247–270, L306–325, L441–475; `server/src/config-template.toml` L91–132; `server/src/gc.rs` L35–272.
- **`DeterminateSystems/nix-installer-action@v23` (`3138316d`) & `cachix/install-nix-action@v32.0.0` (`bb0495a1`):** upstream docs.

## Revalidation

1. **GHCR Referrers API support:** Run:
   ```bash
   TOKEN=$(curl -s "https://ghcr.io/token?service=ghcr.io&scope=repository:oras-project/oras:pull" | jq -r .token)
   curl -i -H "Authorization: Bearer $TOKEN" "https://ghcr.io/v2/oras-project/oras/referrers/sha256:5fabb4e523de1781443c227fca62782a51aeacd044413c07f54dc64935d7f013"
   ```
   A `200 OK` OCI Image Index (instead of `404`) indicates GHCR has enabled native OCI 1.1 Referrers API support.
2. **GHCR billing / limits / deletion locks:** Diff `github-packages.md`, `working-with-the-container-registry.md`, and `deleting-and-restoring-a-package.md` in `github/docs` against `d7487f5debb5a5a2a6e65e6f9fa539266f5f8db6`.
3. **Attic CDC & GC defaults:** Diff `server/src/config-template.toml` and `server/src/gc.rs` in `zhaofengli/attic` against `7a19204df10d606c5070e6bb72615c3461900c05`.
