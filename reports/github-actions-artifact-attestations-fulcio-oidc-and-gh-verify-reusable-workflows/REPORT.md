# GitHub Actions Artifact Attestations (`actions/attest`), Fulcio OIDC Certificates, and `gh attestation verify` Semantics for Reusable Workflows

## Summary

- **`actions/attest@v4` unconditionally calls GitHub's Attestations API even when `push-to-registry: false`:** Direct inspection of `actions/attest@v4.2.2` (`1e69f48a`, unchanged on `main@badbb428`) and `@actions/attest@3.2.0` (`actions/toolkit@b679af25`) proves that `actions/attest@v4` **never passes `skipWrite: true`** and unconditionally runs `POST /repos/{owner}/{repo}/attestations` (requiring `attestations: write`, subject to 80/min and 500/hr content-creation secondary rate limits and GHEC plan gating on private repos) *before* writing the local `bundle-path` JSON file. If API persistence fails, **no local bundle is written**. By contrast, invoking `@actions/attest@3.2.0` with `skipWrite: true` (or signing directly via `sigstore/sigstore-rust@0.16.0` `sigstore-sign` `sign_attestation`) executes the **byte-identical** OIDC → Fulcio → Rekor/TSA signing path without `attestations: write` or permanent repository Attestations tab accumulation.
- **Batch `subject-checksums` and `push-to-registry: true` constraints:** Passing multiple subjects via `subject-checksums` produces **one** in-toto v1 Statement, **one** Fulcio+Rekor/TSA DSSE signature, and **one** API call, **but** requires raw hex without `sha256:` prefix (`<64-hex>  <name>`; `sha256:<hex>` throws `Invalid digest`), and `push-to-registry: true` strictly rejects `subjects.length !== 1`.
- **Fulcio X.509 certificates for SHA-pinned external reusable workflows literally terminate SAN and `buildSignerURI` in `@<40-hex-sha>`:** Active Fulcio `ciprovider` templates (`sigstore/fulcio@b01d056a`, confirmed on a real production certificate) populate both X.509 SAN URI and `buildSignerURI` (`.1.9`) with `https://github.com/<job_workflow_ref>` (ending literally in `@<40-hex-sha>`), `buildSignerDigest` (`.1.10`) with `job_workflow_sha`, `buildConfigURI` (`.1.18`) with `workflow_ref`, and `sourceRepository*` (`.1.12`–`.1.17`, `.1.22`) with the calling consumer repository's identity. GitHub's private-repo Sigstore instance (`O=GitHub, Inc.`, RFC 3161 TSA, no Rekor) emits the exact same OIDs (`.1.1`–`.1.6`, `.1.8`–`.1.22`).
- **`gh attestation verify` policy traps across reusable-workflow SHA upgrades (`cli/cli@e1219499` / `v2.103.3`, `sigstore-go@0dfc1633`, 22 live offline probes):**
  1. `--signer-workflow`, `--signer-repo`, `--cert-identity`, and `--cert-identity-regex` are **mutually exclusive**. `--signer-workflow` without `@<sha>` matches **all** historical SHAs and mutable branches/tags (preventing revocation of vulnerable SHAs), while `--signer-digest` takes only a single SHA. Enforcing a multi-SHA allowlist across routine upgrades while revoking bad SHAs requires an **anchored** `--cert-identity-regex '^https://github\.com/<org>/<repo>/\.github/workflows/<file>\.yml@(<sha1>|<sha2>)$'` (`sigstore-go` uses unanchored RE2 `MatchString`!) plus JSON post-checking of `buildSignerDigest`.
  2. `--repo` / `--owner` check only URI strings case-insensitively (never numeric `sourceRepositoryIdentifier` / `sourceRepositoryOwnerIdentifier`), and `--source-ref` checks **exact case-sensitive equality** (cannot match `refs/heads/gh-readonly-queue/main/...` prefixes). Complete policy verification requires parsing `--format json` (`verificationResult.signature.certificate`) or verifying natively via a library such as `sigstore/sigstore-rust@0.16.0` (which parses all `.1.1`–`.1.24`, including `.1.23`/`.1.24` omitted by `sigstore-go@0dfc1633`).
  3. **Three offline verification traps (reproduced live):** Passing a local file + `--bundle` + `--custom-trusted-root` on `github.com` makes **zero network calls**; passing **`oci://...`** ALWAYS calls `remote.Get` over the network even with `--bundle`, `--custom-trusted-root`, and `@sha256:...`; **`trusted_root.jsonl` without a trailing `\n`** silently drops its last line via `reader.ReadBytes('\n')` (`io.EOF`) and fails with `no custom verifier found for issuer "sigstore.dev"`; and `*.ghe.com` tenancy hosts unconditionally call `GET /meta`.

## Applicability

This report examines the interaction of `actions/attest` (`v4.2.2` @ `1e69f48a` and `main` @ `badbb428`), `@actions/attest@3.2.0` (`actions/toolkit@b679af25`), `sigstore/fulcio@b01d056a` (`v1.10.1`), `sigstore/sigstore-go@0dfc1633` (and `v1.3.0`/`v1.4.0`), `cli/cli` (`v2.103.3` local executable, `v2.105.0` @ `e1219499`, `trunk` @ `de06af2c` — zero diff under `pkg/cmd/attestation/` across all three), `sigstore/sigstore-rust@3d2baa8c` (`0.16.0`), `github/docs@d7487f5d`, `github/rest-api-description@c9c95fe3`, and live GitHub OIDC discovery (`2026-11-21`). Findings apply to Sigstore v0.3 DSSE bundles generated in GitHub Actions on github.com (`fpt`/`ghec`); GitHub Artifact Attestations are unsupported on GHES.

## Findings

### 1. `actions/attest@v4` and `@actions/attest@3.2.0` Exact Execution Path

#### 1.1 Unconditional Attestations API Upload Even When `push-to-registry: false`

Basis: source (`actions/attest@1e69f48a`: `action.yml`, `src/{index,main,attest,subject,predicate,sbom,detect}.ts`; `actions/toolkit@b679af25`: `packages/attest/src/{attest,sign,store,endpoints,intoto,oidc,provenance}.ts`; verified byte-equivalent to npm `@actions/attest@3.2.0`)

1. **`skipWrite` is supported in `@actions/attest` but NEVER passed by `actions/attest@v4`:**
   - `actions/attest/src/attest.ts:35-41`:
     ```ts
     const attestation = await attest({
       subjects,
       predicateType: predicate.type,
       predicate: predicate.params,
       sigstore: opts.sigstoreInstance,
       token: opts.githubToken
     })
     ```
     Neither `action.yml` nor `src/index.ts` exposes any input for `skipWrite`.
   - `@actions/attest` `packages/attest/src/attest.ts:38-40, 74-88`:
     ```ts
     const endpoints = signingEndpoints(options.sigstore)
     const bundle = await signPayload(payload, endpoints)

     let attestationID: string | undefined
     if (options.skipWrite !== true) {
       attestationID = await writeAttestation(
         bundleToJSON(bundle),
         options.token,
         {headers: options.headers}
       )
     }
     return toAttestation(bundle, attestationID)
     ```
   - `signPayload` (`sign.ts:58-109`) builds the Sigstore v0.3 DSSE bundle strictly from `FulcioSigner(CIContextProvider('sigstore'))` + `RekorWitness` or `TSAWitness`—using only the GitHub Actions OIDC JWT (`audience = 'sigstore'`), **never `GITHUB_TOKEN`**. Therefore `skipWrite: true` changes **zero bytes** of the emitted Sigstore v0.3 bundle while eliminating `writeAttestation` (`POST /repos/{owner}/{repo}/attestations`, 5 retries, `store.ts:6, 20-53`).
2. **Local `bundle-path` is written ONLY after API persistence succeeds (`actions/attest/src/main.ts:99-116, 148-163`):**
   - `main.ts:99-100` sets `outputPath = path.join(await tempDir(), 'attestation.json')` and calls `core.setOutput('bundle-path', outputPath)` *before* signing.
   - `main.ts:102` calls `createAttestation(...)` (which runs `POST /repos/{owner}/{repo}/attestations`).
   - `main.ts:113` writes `JSON.stringify(att.bundle) + os.EOL` to `outputPath` only if line 102 succeeded. If `attestations: write` is absent, rate-limited, or blocked by plan gating, `main.ts:148-163` fails the step with **no file written at `outputPath`**.
3. **`push-to-registry: true` runs *in addition* to API persistence and rejects >1 subject (`src/attest.ts:45-111`, `src/main.ts:92-94, 277-293`):**
   - `validateRegistrySubjects` throws whenever `subjects.length !== 1` or the digest algorithm is not `sha256`—making `push-to-registry: true` incompatible with multi-subject batch `subject-checksums`.
   - When `push-to-registry: true` and `create-storage-record: true` (default) on an org-owned repo, it also calls `POST /orgs/{owner}/artifacts/metadata/storage-record` (failure downgraded to `core.warning`, `src/attest.ts:105-109`).
4. **`actions/attest` `v4.2.2` (`1e69f48a`) vs. `main` (`badbb428`) diff:** 31 commits ahead, unchanged lockfile (`@actions/attest@3.2.0`, `@sigstore/oci@0.7.2`, `@sigstore/sign@3.1.0`), unchanged `action.yml` (`runs.using: node24`), and only 2 functional `src/` commits (`b60c2628ab94` preserving custom registry ports; `badbb428b005` failing when a literal `subject-path` matches zero files).

#### 1.2 Batch `subject-checksums`, Sigstore Instance Selection, Quotas, and Anti-Pattern Guidance

Basis: source (`actions/attest@1e69f48a`, `@actions/attest@3.2.0`) + normative (`github/rest-api-description@c9c95fe3`) + documentation (`github/docs@d7487f5d`)

- **`subject-checksums` format (`src/subject.ts:13-26, 204-285, 320-329`):** Accepts an existing file path (max `524,288` bytes = `512 KiB`) or inline multiline string. Each line is `<hex_digest> <name>` (also `<hex>  <name>` or `<hex> *<name>`). **Raw hex only (`HEX_STRING_RE = /^[0-9a-fA-F]+$/`)**: passing `sha256:<hex>` throws `Invalid digest`. Algorithm is inferred by hex length (`64` → `sha256`, `128` → `sha512`). All lines fold into one `https://in-toto.io/Statement/v1` (`payloadType: "application/vnd.in-toto+json"`). Client-side `MAX_SUBJECT_COUNT = 1024` is enforced on `subject-path` and `$GITHUB_ARTIFACTS_LIST` (`L60, L127`), whereas `subject-checksums` enforces only the 512 KiB file cap (`L224`) and no count cap on inline strings. Predicates (`predicate`/`predicate-path`/`sbom-path`) cap at **16 MiB** (`src/predicate.ts:11`, `src/sbom.ts:11`).
- **Sigstore instance selection (`src/main.ts:59-66`, `packages/attest/src/endpoints.ts:6-55`):** Selects `'public-good'` (`https://fulcio.sigstore.dev` + `https://rekor.sigstore.dev`) **iff** `github.context.payload.repository?.visibility === 'public' && !inputs.privateSigning` (undocumented input `private-signing`); otherwise selects `'github'` (`https://fulcio.githubapp.com` + `https://timestamp.githubapp.com`, RFC 3161 TSA, no Rekor). In `github/rest-api-description@c9c95fe3`, `webhook-merge-group-checks-requested` embeds `repository-webhooks` where `visibility` is defined but optional (`unknown` whether live `merge_group` always sets it to `'public'`).
- **Plan gating, rate limits, retention, and guidance (`github/docs@d7487f5d`):**
  - Available on public repos (all plans) and private/internal repos only on **GHEC**; unsupported on GHES (`gated-features/attestations.md:1`, `actions/attest` `README.md:35-41`).
  - Rate limits: `GITHUB_TOKEN` primary `1,000 req/hr/repo` (`15,000` GHEC); secondary **content-generating requests: 80/min and 500/hr**, 900 pts/min (`POST` = 5 pts), 100 concurrent (`secondary-rate-limit-rest-graphql.md:5-9, 23`).
  - No automatic expiry is documented for stored repository attestations (records accumulate permanently in the repository Attestations tab), and API version `2026-03-10` removes inline `bundle` objects from list endpoints in favor of `bundle_url` (`breaking-changes-changelog.md:626-636`). Bulk endpoints enforce `maxItems: 1024`.
  - Official guidance (`content/actions/concepts/security/artifact-attestations.md:41-43`) warns verbatim: *"You should **not** sign: Frequent builds that are just for automated testing."*

---

### 2. GitHub Actions OIDC Claims and Fulcio X.509 Certificate Extensions

#### 2.1 Active Fulcio Template Mapping for SHA-Pinned External Reusable Workflows

Basis: source (`sigstore/fulcio@b01d056a`: `pkg/challenges/challenges.go:85-86`, `pkg/identity/ciprovider/principal.go:134-195`, `config/identity/config.yaml:169-175, 209-259`, `pkg/certificate/extensions.go:145-606`; `sigstore/sigstore-go@0dfc1633`; `sigstore/sigstore-rust@3d2baa8c`: `crates/sigstore-crypto/src/x509.rs:345-415`) + execution (live OIDC discovery `2026-11-21` + production certificates in `cli/cli@e1219499`)

Live `GET https://token.actions.githubusercontent.com/.well-known/openid-configuration` confirms 36 `claims_supported` (including `job_workflow_ref`, `job_workflow_sha`, `workflow_ref`, `workflow_sha`, `repository`, `repository_id`, `repository_owner`, `repository_owner_id`, `repository_visibility`, `ref`, `sha`, `event_name`, `runner_environment`, `run_id`, `run_attempt`, `environment`, `enterprise`, `enterprise_id`, `issuer_scope`, `check_run_id`).

In Fulcio's active `ciprovider` mapping (`config.yaml:209-259`, default `url: "https://github.com"`), extensions `.1.8`–`.1.24` are DER `UTF8String` while legacy `.1.1`–`.1.6` are raw UTF-8 byte slices:

| Certificate Field / Extension | OID (`1.3.6.1.4.1.57264.1.*`) | Fulcio Template | Value for `uses: core-org/core-repo/.github/workflows/gate.yml@<40-hex-sha>` Called by `consumer-org/consumer-repo` | Parsed by `sigstore-go@0dfc1633` / `sigstore-rust@0.16.0` |
| :--- | :--- | :--- | :--- | :--- |
| **SAN URI** (`cert.URIs[0]`, critical) | X.509 SAN (`2.5.29.17`) | `{{ .url }}/{{ .job_workflow_ref }}` | `https://github.com/core-org/core-repo/.github/workflows/gate.yml@<40-hex-sha>` | Yes / Yes |
| `Issuer` (raw) / `IssuerV2` (DER) | `.1.1` / `.1.8` | Forced `token.Issuer` (`principal.go:193`) | `https://token.actions.githubusercontent.com` (or `.../<enterpriseSlug>`) | Yes / Yes |
| `BuildSignerURI` | **`.1.9`** | `{{ .url }}/{{ .job_workflow_ref }}` | `https://github.com/core-org/core-repo/.github/workflows/gate.yml@<40-hex-sha>` | Yes / Yes |
| `BuildSignerDigest` | **`.1.10`** | `job_workflow_sha` | `<40-hex-sha>` (called reusable workflow commit SHA) | Yes / Yes |
| `RunnerEnvironment` | **`.1.11`** | `runner_environment` | `"github-hosted"` or `"self-hosted"` | Yes / Yes |
| `SourceRepositoryURI` | **`.1.12`** | `{{ .url }}/{{ .repository }}` | `https://github.com/consumer-org/consumer-repo` | Yes / Yes |
| `SourceRepositoryDigest` | **`.1.13`** | `sha` | `<consumer-commit-sha>` | Yes / Yes |
| `SourceRepositoryRef` | **`.1.14`** | `ref` | e.g., `refs/heads/main`, `refs/heads/gh-readonly-queue/main/pr-...` | Yes / Yes |
| `SourceRepositoryIdentifier` | **`.1.15`** | `repository_id` | `"<numeric-consumer-repo-id>"` | Yes / Yes |
| `SourceRepositoryOwnerURI` | **`.1.16`** | `{{ .url }}/{{ .repository_owner }}` | `https://github.com/consumer-org` | Yes / Yes |
| `SourceRepositoryOwnerIdentifier` | **`.1.17`** | `repository_owner_id` | `"<numeric-consumer-owner-id>"` | Yes / Yes |
| `BuildConfigURI` | **`.1.18`** | `{{ .url }}/{{ .workflow_ref }}` | `https://github.com/consumer-org/consumer-repo/.github/workflows/caller.yml@<ref>` | Yes / Yes |
| `BuildConfigDigest` | **`.1.19`** | `workflow_sha` | `<caller-workflow-commit-sha>` | Yes / Yes |
| `BuildTrigger` | **`.1.20`** | `event_name` | e.g., `merge_group`, `push`, `pull_request` | Yes / Yes |
| `RunInvocationURI` | **`.1.21`** | `{{ .url }}/{{ .repository }}/actions/runs/{{ .run_id }}/attempts/{{ .run_attempt }}` | Run attempt URL in consumer repository | Yes / Yes |
| `SourceRepositoryVisibilityAtSigning` | **`.1.22`** | `repository_visibility` | `"public"`, `"private"`, or `"internal"` | Yes / Yes |
| `DeploymentEnvironment` | `.1.23` | `environment` (omitted if `""`) | GitHub Environment name | **No** / **Yes** |
| `Subject` (raw `sub`) | `.1.24` | Forced `token.Subject` (`principal.go:194`) | Raw JWT `sub` claim | **No** / **Yes** |
| Deprecated GitHub raw extensions | `.1.2`–`.1.6` | `event_name`, `sha`, `workflow`, `repository`, `ref` | Mirrors of `.1.20`, `.1.13`, workflow name, `.1.12` (no host), `.1.14` | Yes / Yes |

- **Production specimen verification (`execution`, `cli/cli@e1219499` fixtures decoded via `openssl x509` and `gh attestation inspect --format json`):**
  1. `reusable-workflow-attestation.sigstore.json` (Public Good `O=sigstore.dev`, 1 Rekor entry, 1 CT SCT): confirmed SAN URI and `buildSignerURI` (`.1.9`) literally equal `https://github.com/github/artifact-attestations-workflows/.github/workflows/attest.yml@09b495c3f12c7881b3cc17209a327792065c1a1d`, `buildSignerDigest` (`.1.10`) = `09b495c3f12c7881b3cc17209a327792065c1a1d`, `buildConfigURI` (`.1.18`) = `https://github.com/malancas/attest-demo/.github/workflows/shared.yml@refs/heads/main`, `sourceRepositoryIdentifier` (`.1.15`) = `"804070735"`, `sourceRepositoryOwnerIdentifier` (`.1.17`) = `"16248153"`.
  2. `github_provenance_demo-0.0.12-py3-none-any-bundle.jsonl` (private repo `O=GitHub, Inc., CN=Fulcio Intermediate l2`, `tlogEntries: 0`, `rfc3161Timestamps: 1`): confirmed identical OIDs `.1.1`–`.1.6`, `.1.8`–`.1.22` with `sourceRepositoryVisibilityAtSigning: "private"`.
- **2026 immutable `sub` & enterprise custom issuer (`oidc.md:168-188, 231-255`):** Repositories created, renamed, or transferred after July 15, 2026 default to `sub = repo:OWNER@OWNER-ID/REPO@REPO-ID:...` (affecting only `.1.24`, not SAN or `.1.9`–`.1.22`). GHEC enterprises enabling `include_enterprise_slug: true` emit `iss = https://token.actions.githubusercontent.com/<enterpriseSlug>` (supported in Fulcio via `meta-issuers: https://token.actions.githubusercontent.com/*`, `config.yaml:209-212`).

---

### 3. `gh attestation verify` and `sigstore-go` Verification Semantics Across SHA Upgrades

#### 3.1 Two-Stage Verification Pipeline and Exact Flag Semantics

Basis: source (`cli/cli@e1219499` / `v2.103.3` / `trunk@de06af2c`: zero diff under `pkg/cmd/attestation/`; `sigstore/sigstore-go@0dfc1633`: `pkg/verify/{signed_entity,certificate,certificate_identity}.go`, `pkg/fulcio/certificate/summarize.go`) + execution (22 live offline probes on `gh 2.103.3`)

`gh attestation verify` runs two stages (`pkg/cmd/attestation/verify/attestation.go:74-95`):
1. **Stage 1 (`sigstore-go`):** Verifies Rekor inclusion proofs / RFC 3161 TSAs, RFC 5280 certificate chain at observer timestamp, CT SCTs (for `sigstore.dev`), DSSE signature + subject digest match, `SubjectAlternativeNameMatcher` against **`cert.URIs[0]` (SAN URI)**, and `RunnerEnvironment` (`"github-hosted"` if `--deny-self-hosted-runners`). `cli/cli` passes wildcard `NewIssuerMatcher("", ".*")` (`verify/policy.go:153`) to defer issuer checks to Stage 2 for case-insensitivity.
2. **Stage 2 (`cli/cli` `verification/extensions.go:43-74`):** Checks `SourceRepositoryOwnerURI` (case-insensitive `EqualFold`, always), `SourceRepositoryURI` (`EqualFold`, if `--repo`), `Issuer` (`EqualFold` against `--cert-oidc-issuer`), `BuildSignerDigest` (`EqualFold`, if `--signer-digest`), `SourceRepositoryDigest` (`EqualFold`, if `--source-digest`), and `SourceRepositoryRef` (**exact case-sensitive `!=`**, if `--source-ref`). Multi-bundle `.jsonl` files use **any-match filtering** (`verification/sigstore.go:290-306`, `extensions.go:24-40`): exiting `0` if at least one bundle matches.

| Flag | Source (`cli/cli@e1219499`) | Exact Matching Semantics | Interactions / Exclusions |
| :--- | :--- | :--- | :--- |
| `--repo` / `--owner` | `verify.go:248-251`, `policy.go:73-127`, `extensions.go:44-51` | Exactly one required. Case-insensitive `EqualFold` on `SourceRepositoryURI` / `SourceRepositoryOwnerURI` only (**never checks numeric `.1.15`/`.1.17`**). If no signer flag is set, defaults `SANRegex` to `(?i)^https://github\.com/<repo-or-owner>/` (**fails on cross-repo reusable workflows**). | Mutually exclusive with each other. |
| `--signer-workflow` | `verify.go:263-264`, `policy.go:28-52, 94-100, 185-204` | If ending in `@(refs/.*\|[0-9a-fA-F]+)$`, matches `^<quoted>$` (exact pinned ref/SHA); otherwise matches `^<quoted>(@(refs/.*\|[0-9a-fA-F]+))?$` (matches **any** ref or SHA; blocks `@evil.yml@refs/...` spoofing). Case-sensitive on SAN. | **Mutually exclusive** with `--cert-identity`, `--cert-identity-regex`, `--signer-repo`. Compatible with `--signer-digest`. |
| `--signer-repo` | `verify.go:262-264`, `policy.go:61-64, 90-93` | Unanchored-right `(?i)^https://github\.com/<owner>/<repo>/` on SAN. | Mutually exclusive with `--cert-identity`, `--cert-identity-regex`, `--signer-workflow`. |
| `--cert-identity` | `verify.go:260, 264`, `certificate_identity.go:130-133` | Exact case-sensitive equality against SAN URI. | Mutually exclusive with `--cert-identity-regex`, `--signer-repo`, `--signer-workflow`. |
| `--cert-identity-regex` (`-i`) | `verify.go:261, 264`, `certificate_identity.go:135-138` | Go RE2 `regexp.MatchString` against SAN URI. **NOT anchored by default!** Callers must wrap in `^...$` and escape `.`. | Mutually exclusive with `--cert-identity`, `--signer-repo`, `--signer-workflow`. **Compatible with `--signer-digest`.** |
| `--signer-digest` | `verify.go:266`, `extensions.go:62-64` | Single-value case-insensitive equality against `BuildSignerDigest` (`.1.10`). | Compatible with all signer flags. |
| `--source-ref` | `verify.go:267`, `extensions.go:69-71` | **Exact case-sensitive equality** against `SourceRepositoryRef` (`.1.14`); cannot match dynamic prefixes like `refs/heads/gh-readonly-queue/main/...`. | Standalone. |
| `--deny-self-hosted-runners` | `verify.go:259`, `policy.go:111-118, 158-160` | Exact equality `RunnerEnvironment == "github-hosted"` (`.1.11`). | Standalone. |
| `--predicate-type` | `verify.go:258`, `api/attestation.go:27-53` | Exact equality on in-toto `predicateType` (default `https://slsa.dev/provenance/v1`). | Standalone. |

**Fields NOT verifiable by `gh attestation verify` CLI flags:** `SourceRepositoryIdentifier` (`.1.15`), `SourceRepositoryOwnerIdentifier` (`.1.17`), `BuildSignerURI` (`.1.9`, checked only indirectly via SAN), `BuildConfigURI` (`.1.18`), `BuildConfigDigest` (`.1.19`), `BuildTrigger` (`.1.20`), `SourceRepositoryVisibilityAtSigning` (`.1.22`), multi-SHA `BuildSignerDigest` allowlists, and `SourceRepositoryRef` prefixes.

#### 3.2 Reusable-Workflow SHA Upgrade & Revocation Policy Pattern

Basis: source + execution + derived

When a consumer upgrades `uses: core-org/core-repo/.github/workflows/gate.yml@<SHA_old>` to `@<SHA_new>`, prior receipts retain `SAN = buildSignerURI = ...@<SHA_old>` and `buildSignerDigest = <SHA_old>`.
- `--signer-workflow <W>` (no `@<sha>`) admits all historical SHAs and mutable branch/tag calls—**cannot revoke vulnerable SHAs**.
- `--signer-workflow <W>@<SHA_new>` or `--signer-digest <SHA_new>` invalidates all receipts signed by `<SHA_old>` on every routine upgrade.
- **Allowlist + revocation pattern:** Invoke `gh attestation verify <local-file> --bundle <bundle.json> --custom-trusted-root <trusted_root.jsonl> -R <owner>/<repo> --cert-identity-regex '^https://github\.com/<core-org>/<core-repo>/\.github/workflows/<file>\.yml@(<SHA_1>|<SHA_2>)$' --deny-self-hosted-runners --predicate-type <type> --format json`, then parse `verificationResult.signature.certificate` to enforce: (1) `buildSignerDigest` ∈ `allowed_shas`, (2) numeric `sourceRepositoryIdentifier` and `sourceRepositoryOwnerIdentifier` equal pinned IDs (preventing rename/squatting), (3) `sourceRepositoryRef` matches allowed branch or merge-queue prefix (`refs/heads/gh-readonly-queue/<branch>/`), and (4) `buildTrigger` ∈ allowed trusted events (`merge_group`, `push`).

#### 3.3 Offline Verification Zero-Network Audit & Native Rust Alternative

Basis: source (`cli/cli@e1219499`: `verify/verify.go:210-211`, `verification/sigstore.go:68-183, 314-392`, `verification/attestation.go:27-34`, `artifact/oci/client.go:49-68`, `tuf.go:36`; `sigstore/sigstore-rust@3d2baa8c`) + execution (22 live probes on `gh 2.103.3` with poisoned `HTTPS_PROXY=http://127.0.0.1:1`, empty `GH_TOKEN`/`GITHUB_TOKEN`, empty `XDG_CACHE_HOME`/`GH_CONFIG_DIR`)

- **Zero-network proof (`execution`):** Local file artifact + `--bundle <file.{json,jsonl}>` (other extensions fail with `ErrUnrecognisedBundleExtension`, `attestation.go:27-34`) + `--custom-trusted-root <trusted_root.jsonl>` on `github.com` exited **`0`** with zero network calls.
- **Four offline pitfalls proven in source and execution:**
  1. **`trusted_root.jsonl` trailing-newline bug (`sigstore.go:113-114`):** `reader.ReadBytes('\n')` aborts on `io.EOF` before parsing a non-newline-terminated final line; live probe without trailing `\n` failed with `exit 1: no custom verifier found for issuer "sigstore.dev"`. (`gh attestation trusted-root` always emits trailing `\n`, `trustedroot.go:164-184`.)
  2. **`oci://` URIs ALWAYS hit the network (`artifact/oci/client.go:49-68`):** `GetImageDigest` unconditionally calls `remote.Get` even when `--bundle`, `--custom-trusted-root`, and `@sha256:...` are given; live probe failed trying to dial `https://ghcr.io/v2/` through the poisoned proxy.
  3. **Omitting `--custom-trusted-root` hits TUF on cold/stale (>1 day) cache (`tuf.go:36`, `sigstore.go:78-98`):** Live probe failed with `no valid Sigstore verifiers could be initialized`.
  4. **GHEC Data Residency (`*.ghe.com` tenancy) unconditionally calls `GET /meta` (`verify.go:210-211`, `api/client.go:291-321`)** even with `--bundle` and `--custom-trusted-root`.
- **Verifier policy inference for `--custom-trusted-root` (`sigstore.go:121-183, 314-392`):** Inspects `lowestCert.Issuer.Organization[0]`: `"sigstore.dev"` requires 1 CT SCT + 1 Rekor entry + 1 observer timestamp; `"GitHub, Inc."` requires 1 RFC 3161 TSA timestamp (no Rekor).
- **Native Rust Sigstore v0.3 status (`sigstore/sigstore-rust@3d2baa8c`, `v0.16.0`, MSRV 1.86):** The official `sigstore` Rust workspace provides `sigstore-sign` (`SigstoreInstance::PublicGood` and `SigstoreInstance::GitHub` with embedded configs, DSSE `signer.sign_attestation(Attestation)` producing `MediaType::Bundle0_3` with no GitHub Attestations API write), `sigstore-verify` (offline `TrustedRoot::from_json` + `verify(&artifact, &bundle, &policy, &trusted_root)`), and `sigstore-crypto::x509::extract_fulcio_ci_claims` parsing **all** Fulcio extensions `.1.1`–`.1.24` (including `.1.23` `deployment_environment` and `.1.24` `token_subject`, which `sigstore-go@0dfc1633` omits).

## Boundaries

- **`unknown` — `workflow_ref` (`buildConfigURI`) / `workflow_sha` (`buildConfigDigest`) under a GHEC Org Ruleset workflow:** `github/docs@d7487f5d` does not document whether `workflow_ref` points to the ruleset source repo (`consumer-org/ci-config/...`) when a ruleset workflow calls an external reusable workflow; verification policies must not assume `buildConfigURI` shares a prefix with `sourceRepositoryURI` until confirmed live.
- **`unknown` — `github.event.repository.visibility` on live `merge_group` events:** `repository-webhooks.visibility` is optional in `github/rest-api-description@c9c95fe3`; not confirmed via live `merge_group` execution whether it is always `'public'` on public repos (determining `actions/attest` `'public-good'` vs. `'github'` selection).
- **`unknown` — Server-side GHEC gating of `fulcio.githubapp.com` independent of Attestations API, and server-side subject/bundle size caps on `POST /repos/{owner}/{repo}/attestations`:** Not documented in OpenAPI schema or public docs and not probed against private non-GHEC repos.
- **`unsupported`:** `actions/attest@v4` and GitHub Artifact Attestations on GHES or non-GHEC private/internal repos; `push-to-registry: true` with >1 subject; CLI-flag verification of numeric repo/owner IDs, ref prefixes, `buildTrigger`, or multi-SHA `buildSignerDigest` in `gh attestation verify`; offline `oci://` and `*.ghe.com` verification in `gh attestation verify`; Fulcio OIDs `.1.23`/`.1.24` in `sigstore-go@0dfc1633`.
- **`not examined`:** Execution/conformance testing of `sigstore/sigstore-rust@0.16.0` against live Fulcio/Rekor or `gh attestation verify` cross-compatibility probes (inspected in source only).

## Evidence

All evidence was gathered or executed on `2026-11-21`:

- **`actions/attest@1e69f48acb82d1966a394da916b4c1698aa569d6` (`v4.2.2`) & `badbb428b0055a04f53d6ce00bda98cf1c04e56e` (`main`):** `action.yml` (L6-103), `src/{index.ts,main.ts,attest.ts,subject.ts,predicate.ts,sbom.ts,detect.ts}`, `README.md` (L35-41).
- **`actions/toolkit@b679af25032f1f40e4dee4143e4ed9422b386073` (`@actions/attest@3.2.0`):** `packages/attest/src/{attest.ts,sign.ts,store.ts,endpoints.ts,intoto.ts,oidc.ts,provenance.ts}` (verified identical to npm `@actions/attest@3.2.0` tarball).
- **`sigstore/fulcio@b01d056a925d1f15d1315676d454adf46b6b6629` (`v1.10.1`):** `pkg/challenges/challenges.go` (L85-86), `pkg/identity/ciprovider/principal.go` (L134-195), `pkg/identity/github/principal.go` (L191-232), `config/identity/config.yaml` (L169-175, L209-259), `pkg/certificate/extensions.go` (L145-606).
- **`sigstore/sigstore-go@0dfc163321ea4e131454380638c76bc3e633d655`:** `pkg/verify/{signed_entity.go,certificate.go,certificate_identity.go}`, `pkg/fulcio/certificate/{summarize.go,extensions.go}`.
- **`cli/cli@e1219499a578b69e3437adaa31cd60614e23c802` (`v2.105.0`), `de06af2c2ea536d5722fda35dc2001565f9b9f64` (`trunk`), & `63837fb778d6a39f02be0ce76ff89f2bc8d74bdc` (`v2.103.3`):** `pkg/cmd/attestation/{verify/verify.go,verify/policy.go,verify/policy_test.go,verify/attestation.go,verification/sigstore.go,verification/extensions.go,verification/attestation.go,verification/tuf.go,artifact/artifact.go,artifact/oci/client.go,api/attestation.go,api/client.go,trustedroot/trustedroot.go}` and fixtures `pkg/cmd/attestation/test/data/{reusable-workflow-attestation.sigstore.json,reusable-workflow-artifact,github_provenance_demo-0.0.12-py3-none-any-bundle.jsonl,trusted_root.json}`.
- **`sigstore/sigstore-rust@3d2baa8ca9b1cde8a31d7cb4927338427417611a` (`0.16.0`):** `Cargo.toml`, `crates/sigstore-sign/src/{lib.rs,sign.rs}`, `crates/sigstore-verify/src/lib.rs`, `crates/sigstore-types/src/bundle.rs`, `crates/sigstore-crypto/src/x509.rs` (L345-415).
- **`github/docs@d7487f5d` & `github/rest-api-description@c9c95fe3`:** `oidc.md` (L48-84, L168-188, L231-255), `oidc-with-reusable-workflows.md` (L40-105), `artifact-attestations.md` (L28-43), `verify-attestations-offline.md` (L54), `data/reusables/gated-features/attestations.md`, `secondary-rate-limit-rest-graphql.md` (L5-23), `breaking-changes-changelog.md` (L626-636), `api.github.com.json` (`POST /repos/{owner}/{repo}/attestations`, `webhook-merge-group-checks-requested`).
- **Execution probes (`2026-11-21`, `gh version 2.103.3`):** 22 isolated offline probes under `HTTPS_PROXY=http://127.0.0.1:1`, `HTTP_PROXY=http://127.0.0.1:1`, `NO_PROXY=""`, empty `GH_TOKEN`/`GITHUB_TOKEN`/`XDG_CACHE_HOME`/`GH_CONFIG_DIR` confirming: zero-network local-file pass, trailing-newline failure, cold-cache TUF failure, exact/wrong SHA `--signer-workflow`, multi-SHA anchored `--cert-identity-regex` allowlist & revocation, unanchored regex substring match hazard, mutual exclusion error across `[cert-identity cert-identity-regex signer-repo signer-workflow]`, `--cert-identity-regex` + `--signer-digest` compatibility, case-insensitive `-R`, exact case-sensitive `--source-ref` (prefix failure), `--deny-self-hosted-runners`, `--format json` extraction of numeric IDs/trigger/ref, and `oci://` network failure.

## Revalidation

1. **Offline `gh attestation verify` behavioral suite:** Fetch `reusable-workflow-artifact`, `reusable-workflow-attestation.sigstore.json`, and `trusted_root.json` (compacted to single-line JSONL with trailing `\n`) from `cli/cli`, set `HTTPS_PROXY=http://127.0.0.1:1 HTTP_PROXY=http://127.0.0.1:1 NO_PROXY="" GH_TOKEN="" GITHUB_TOKEN=""` with fresh `XDG_CACHE_HOME`, and re-run `gh attestation verify` testing: (a) local file + `--cert-identity-regex` allowlist (expect exit `0`), (b) stripping trailing `\n` from `trusted_root.jsonl` (tests whether `sigstore.go:113-114` EOF bug is fixed), and (c) `oci://...` with `--bundle` + `--custom-trusted-root` (tests whether `oci/client.go:57` still dials the registry).
2. **`actions/attest` `skipWrite` check:** Diff `action.yml`, `src/attest.ts`, and `src/main.ts` in `actions/attest` against `badbb428b0055a04f53d6ce00bda98cf1c04e56e` to check whether a `skip-write` input or local-only mode is added.
3. **Fulcio & `sigstore-go` OID parity:** Diff `config/identity/config.yaml` in `sigstore/fulcio` against `b01d056a` and `pkg/fulcio/certificate/extensions.go` in `sigstore/sigstore-go` against `0dfc1633`.
