# Multi-Unit Project Manifest (`anneal.toml`), Batch Verification (`verify --all`), and Item-Level Merkle Claim Cache

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Verifying multi-claim Rust crates with independent single-unit `cargo anneal verify --request <unit>/request.json` runs duplicates `[profiles.<id>]` metadata across $N$ files, spawns $N$ full-crate `anneal-rustc-capture` compiler sessions (`tcx.analysis(())` + `census`), re-verifies untouched claims on every edit, and duplicates the crate-wide `census` array $N$ times in Receipt Schema v3 output (`13.77 MiB` per unit on `zerocopy`'s `52,032`-item crate, or `1.65 GiB` at $N = 100$).

This specification defines three composable, zero-weakening mechanisms (`0` LOC added to `trusted/audit/TrustedBoundary.lean` or `trusted/lean/*.lean`; `~180` LOC in `trusted/rustc-capture`; `~650` LOC in `trusted/cargo-anneal`):
1. **Declarative Multi-Unit Manifest (`anneal.toml`, `schema_version = 1`):** Factors shared compilation profiles (`[profiles.<id>]` with explicit `source_files` allowlists) from per-claim `[[unit]]` tables and projects each unit deterministically to its canonical single-unit `Request` (`schema_version = 1`) digest.
2. **Single-Pass Multi-Unit MIR Capture & Bounded Parallel Scheduler (`verify --all` / `--unit <id>`):** Executes **one** `anneal-rustc-capture capture --units-manifest <batch.json>` session per distinct `ProfileSpec`, memoizes `extract::body(tcx, def)` once per union `LocalDefId`, isolates per-unit `unsupported` / `proof_failed` failures (`exit 1`) from sibling units (`#3735` R07), shares one `Arc<AdmittedToolchain>`, and emits a deduplicated `batch_verification_receipt` (`34.0x` smaller JSON at $N = 4$).
3. **Four-Tier Merkle Cache Hierarchy (`L0`–`L3`):** Pairs `L0` process toolchain admission and `L1` `ProfileCaptureCache` with `#4145` `L2` `OleanCache` and `L3` `ClaimCache` (`anneal-claim-cache-v1`), binding `captured_lean_sha256` (rather than raw `.rs` hashes or span-sensitive `capture_sha256`), `Spec`/`Proof` hashes, locks, `TrustedBoundary.lean`, `ActiveSandbox`, and taint flags. Across 4 real `zerocopy/src/` suites under `linux_bwrap`, measured wall-clock time drops from **`382.94s`** (serial cold) to **`91.32s`** (`4.19x` cold batch), **`19.40s`** (`19.74x` on 1-unit `Proof.lean` edit via `3/4` `L3` hits @ `3 ms/unit`), and **`6.34s`** (`60.37x` on unrelated `.rs` edit via `1x` `rustc` + `4/4` `L3` hits and `0` Lean spawns).

## Applicability

Findings apply to `google/zerocopy` at commit `a68641199cdfa99f96cb62f0cde921c9d36bfb22` (`anneal/` `v0.2.0-alpha.8`, `zerocopy/` `v0.8.64`, `52,032` crate census items, 19 `.rs` modules), pinned `rustc` commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, and tracking issue `google/zerocopy#3735`.

Runtime benchmarks (`B0`–`B5`) and negative controls were executed on a companion `anneal-batch-mvp` prototype linking `cargo_anneal v0.2.0-alpha.8` and `anneal-rustc-capture` against unmodified `zerocopy/src/` under `linux_bwrap` `ExecSeal` (`["propext"]` axiom ceiling). Native `census_sha256` factoring inside `anneal-rustc-capture --units-manifest` and `N = 100` scaling estimates are explicitly marked `[projected]`.

## Findings

### 1. Declarative Manifest (`anneal.toml`) and Native Multi-Unit Capture (`--units-manifest`)

Basis: source + execution (`google/zerocopy@a68641199cdf`).

- **Manifest Schema (`schema_version = 1`, `#[serde(deny_unknown_fields)]` on every table):**
  - `[profiles.<id>]`: `source_root`, `crate_root` (required member of `source_files`), `crate_name`, `edition` (`2015|2018|2021|2024`), `target`, `cfg` (`BTreeSet<String>`), explicit regular-file `source_files` (no globs/symlinks), and `[profiles.<id>.env]`.
  - `[[unit]]`: unique `id` (`[A-Za-z0-9_.-]{1,128}`), `profile` (default `"default"`), `scope` (`"selected_unit"` | `"crate"`), `roots`, `proof_dir`, `specification` (`"Spec.specs"`), `theorem` (`"Proof.verify"`), and optional explicit module list (otherwise walks regular `*.lean` files assigning `Spec`/`Spec.*` → `"specification"`, others → `"proof"`, rejecting reserved `Expected`, `Captured`, `TrustedBoundary`, and `Trusted.*`/`Anneal.*`/`Init.*`/`Std.*`/`Lean.*`/`Lake.*`).
  - Path hygiene rejects `..`, `/`, NUL bytes, and symlinks (`Component::Normal` only).
- **Single-Pass Capture (`capture --units-manifest <batch.json>`):** Runs `rustc_driver` / `tcx.analysis(())` **once** per distinct `ProfileSpec` (whole-crate syntax/type/borrow errors exit with `status = "compiler_failed"` once). Inside `after_analysis`, `tcx.iter_local_def_id()` builds `census_base` and `census_sha256` **once**; `extract::body(tcx, def)` runs at most once per union `LocalDefId` (`BTreeMap<LocalDefId, Result<ir::Body, UnsupportedItem>>`). Each unit is projected in ascending `LocalDefId` order into `<out_dir>/units/<unit_id>/Captured.lean` and `unit_slice.json` (`~3–24 KB`).
- **Byte-for-Byte Projection Equivalence:** Shared union capture produced **100% byte-for-byte identical** `Captured.lean` (`4,927 B`, `4,888 B`, `2,203 B`, `23,407 B`) and normalized `capture.json` SHA-256 digests across `4/4` real `zerocopy` units relative to standalone `anneal-rustc-capture` runs.

### 2. Zero-Weakening Four-Tier Merkle Cache Hierarchy (`L0`–`L3`)

Basis: source + execution + derived.

All digests use domain-separated SHA-256 with `u64` little-endian length prefixes (`feed_len_str`). Cache directories (`0o700`) enforce `O_NOFOLLOW` on every component/open, `st_uid == geteuid()`, `<= 64 MiB` payloads, per-key `flock(LOCK_EX)`, `0o444` files, `fsync`, and atomic sibling rename.

| Tier | Storage & Scope | Preimage Key Contract | Invalidation & Early Cutoff |
| :--- | :--- | :--- | :--- |
| **`L0`** | In-memory `Arc<AdmittedToolchain>` | `lean-toolchain`, `foundation-lock.json`, `library-lock.json`, `lean`, `LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS`, `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`, `SandboxRuntime::probe` | Computed once per `cargo anneal verify` process instead of $O(N)$ per-worker sysroot scans. |
| **`L1`** | `$XDG_CACHE_HOME/anneal/capture-cache/v1/<K_cap>.json` (`"anneal-profile-capture-v1\0"`) | `capture_binary_sha256`, `rustc_binary_sha256`, `sysroot_driver_libs_sha256`, `PINNED_RUSTC_COMMIT`, canonical `ProfileSpec`, sorted `(rel_path, sha256)` of all `profile.source_files`, union `scope` | Any byte change in any `.rs` file forces **1** `anneal-rustc-capture` run (`~4.3s`); `.lean`-only edits hit `L1` (`0` `rustc` spawns). |
| **`L2`** | `$XDG_CACHE_HOME/anneal/olean-cache/v1/<K_olean>/` (`#4145`) | `lean_binary_sha256`, `sysroot_manifest_sha256`, `allow_unpinned_lean`, `module_name`, `source_sha256`, sorted transitive `dep_olean_sha256s` | Reuses bundled `Trusted.*`/`Anneal.*` and unchanged `Captured`/`Spec`/`Expected` `.olean`s; single-flight warmup prevents $J$ parallel cold workers from duplicating `Trusted.MirSemantics` builds. |
| **`L3`** | `$XDG_CACHE_HOME/anneal/claim-cache/v1/<K_claim>/evidence.json` (`"anneal-claim-cache-v1\0"`) | `ClaimEvidenceKeyInput`: `scope`, `captured_lean_sha256`, `specification_decl`, `theorem_decl`, sorted `spec_sources`, sorted `proof_sources`, `model_manifest_sha256`, `foundation_lock_sha256`, `library_lock_sha256`, `sysroot_manifest_sha256`, `lean_binary_sha256`, `inspector_source_sha256`, `correspondence_provenance_sha256`, `replay_posture_sha256`, `active_sandbox` (`linux_bwrap`\|`linux_landlock_seccomp`\|`none`), `allow_unpinned_lean`, `allow_sorry_in_proof` (+ Stage 2 `assumed_callee_contracts_sha256`) | **Early Cutoff #1:** Unrelated `.rs`/comment edit re-runs `L1` (`rustc`), emits unchanged `captured_lean_sha256`, hits `L3` in `~3 ms/unit` (`0` Lean spawns). **Early Cutoff #2:** Single-unit `Spec`/`Proof` edit hits `L1` + `N-1` `L3` units (`~3 ms/unit`). Live SHA-256 TOCTOU check runs on all `.rs`/`.lean` inputs **after** cache lookup; `validate_cached_audit_invariants` re-checks `replay`, `exactType`, non-empty closures, and axioms; live `(request_sha256, capture_sha256)` re-bind into `audit.bindings`. |

### 3. Batch Scheduler, Receipt Envelope, and Empirical Benchmarks (`zerocopy/src/`)

Basis: execution (`anneal-batch-mvp` on `zerocopy/src/` @ `a68641199c`, `--jobs 4`, `linux_bwrap`, `["propext"]` ceiling, 4 units `01`–`04`).

- **Exit Codes & Failure Isolation:** `0` when all units pass; `1` when zero compiler/operational errors occurred and $\ge 1$ unit hit `proof_failed` or `unsupported`; `2` on `compiler_failed`, toolchain/sandbox failure, TOCTOU mutation, or cache corruption. `--jobs <J>` defaults to `min(4, available_parallelism)` and divides host physical RAM across $J$ concurrent `bwrap`+`lean` processes.
- **Batch Envelope (`schema_version = 3`, `kind = "batch_verification_receipt"`):** Stores each profile's `census_count`, `census_sha256`, and `source_files` once under `profiles.<profile_id>` referenced via `profile_census_ref`. `--emit-unit-receipts <dir>` materializes standalone `<dir>/<unit_id>/receipt.json` files with inline `census` for legacy validators (`anneal/ci/verify_zerocopy.py`).

| Scenario | `rustc` Spawns | `L3` Hits | Wall Clock | Speedup vs. `B0` | Speedup vs. `B2` | Stdout Receipt Size |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| **`B0`: Serial N-Captures Cold** (`4x` standalone `--no-cache`) | `4` | `0/4` | `382.94 s` | `1.00x` | `0.13x` | `66,222,467 B` (`63.15 MiB`) |
| **`B1`: Cold `verify --all`** (`1x` capture + cold `.olean` & `L3`) | `1` | `0/4` | `91.32 s` | `4.19x` | `0.56x` | `1,946,874 B` (`1.86 MiB`, `34.0x` smaller) |
| **`B2`: CI Prebuilt-`.olean` Cold Claims** | `1` | `0/4` | `51.42 s` | `7.45x` | `1.00x` | `1,946,874 B` (`34.0x` smaller) |
| **`B3b`: Warm 1-Item `Proof.lean` Edit (`olean-only`)** | `0` | `0/4` | `41.39 s` | `9.25x` | `1.24x` | `1,946,869 B` |
| **`B3a`: Warm 1-Item `Proof.lean` Edit (`full-receipt`)** | `0` | `3/4` | `19.40 s` | `19.74x` | `2.65x` | `1,946,841 B` |
| **`B4`: Warm Unrelated `.rs` Edit (`src/util/mod.rs`)** | `1` | `4/4` | `6.34 s` | `60.37x` | `8.11x` | `1,946,833 B` |
| **`B5`: Warm No-Op `verify --all`** | `0` | `4/4` | `10.59 s`\* | `36.17x` | `4.86x` | `1,946,831 B` |

*\*In `B5`, `4` `L3` hits took `12 ms` (`3 ms/unit`); `7,494 ms` went to prototype cloning of `52,032` `census` JSON values and `~2.9s` to sysroot hashing — native `--units-manifest` `census_sha256` factoring projects `<2.5s` warm no-op latency even at $N = 100$.*

- **Negative Controls (3/3 Fail-Closed):** (A) Mutating `<usize as PointerMetadata>::from_elem_count` invalidated `01` and `04` (`proof_failed`, `rc = 1` in `15.59s`) while `02` and `03` hit `L3` (`3 ms`); (B) adding unsupported raw-pointer `05_unsupported_padding` (`util::padding_needed_for`) isolated `05` (`status = "unsupported"`, `rc = 1`) without failing `01`–`04`; (C) caching `sorry` under `--allow-sorry-in-proof` missed `K_claim` and rejected (`rc = 1`) on subsequent untainted `verify`.

### 4. Eliminated Alternatives and Open Maintainer Decisions

Basis: source + derived.

- **Eliminated alternatives:**
  - *Monolithic union `Captured.program` across all units:* Breaks positional `Captured.body_k` indexing in existing `zerocopy/proofs/*` and destroys per-unit failure isolation and `O(1)` edit invalidation.
  - *Lexical/span Rust slicing to skip `rustc`:* Unsound because Rust macros, `required_consts`, trait coherence, and sibling borrow errors have crate-wide effects.
  - *Keying `K_claim` on raw `capture_sha256` or `request_sha256`:* `capture.json` embeds host staging `PathBuf`s and line/column spans across all `52,032` `census` items (`capture.rs`, `ir.rs`, `verify.rs:1516`), breaking Early Cutoff #1 on blank-line edits in unrelated files.
  - *Lake native `.hash` / hardlink build cache:* Sits outside TCB, skips `TrustedBoundary.lean` axiom/closure checks, and introduces writable hardlink vectors.
  - *Requiring a resident daemon for CI batch verification:* Complicates ephemeral CI cache persistence (`actions/cache`) and concurrency; stateless `L1`–`L3` disk caches serve directly under a future LSP/MCP daemon later.
- **Open maintainer policy decisions (`OD-1`–`OD-4`):**
  - `OD-1`: Standalone `anneal.toml` (auto-discovered in `anneal.toml` / `proofs/anneal.toml`) + optional `[package.metadata.anneal].manifest` pointer in `Cargo.toml` (avoids `crates.io` `Cargo.toml` churn).
  - `OD-2`: `--claim-cache-mode=full-receipt` locally and on PR CI, vs. `--claim-cache-mode=olean-only` / `--no-cache` on `main` post-merge / release qualification.
  - `OD-3`: Canonical `batch_verification_receipt` stdout envelope + `--emit-unit-receipts <dir>` for legacy single-unit receipt consumers.
  - `OD-4`: Explicit `cargo anneal cache {status,clean,gc --max-size-mb 4096 --max-age-days 30}` instead of inline GC during `verify` (keeps parallel `verify` read paths lock-free).

## Boundaries

- **not examined (native `anneal-rustc-capture --units-manifest` landing & `N = 100` live run):** Benchmarks `B0`–`B5` ran on the `anneal-batch-mvp` prototype with `4` real `zerocopy` units; `N = 100` latencies (`~7–8s` unrelated `.rs` edit, `~13–15s` 1-unit proof edit vs. `~460s` with `#4145` alone) and sub-`2.5s` warm no-op latency after moving `census_sha256` factoring into `anneal-rustc-capture` are `[projected]`.
- **unsupported (unauthenticated cross-trust-domain remote shared caches):** Local disk caches assume the single-user trust model (`geteuid()`); shared CI caches across trust boundaries require `--claim-cache-mode=olean-only` or cryptographic attestation.
- **excluded (resident daemon, file watcher, LSP/MCP multiplexing):** Deferred to a stateful-service layer built on top of this stateless manifest, scheduler, and disk cache foundation.

## Evidence

- **Primary inspected baseline:** `google/zerocopy@a68641199cdfa99f96cb62f0cde921c9d36bfb22` (`anneal/trusted/cargo-anneal/src/{lib.rs,verify.rs,stage.rs,target.rs,toolchain.rs,sandbox.rs,olean_cache.rs}`, `anneal/trusted/rustc-capture/src/{main.rs,capture.rs,ir.rs,lean.rs}`, `anneal/ci/verify_zerocopy.py`, `zerocopy/proofs/{01_usize_pointer_metadata,02_unit_pointer_metadata,03_macros_unsafe,04_substantive_and_frombytes_markers}`) and `google/zerocopy#3735`.
- **Pinned toolchain:** `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`.
- **Experimental validation:** `anneal-batch-mvp` benchmark suite (`B0`–`B5`), `verify-projection-identity` (`4/4` units byte-identical), and Negative Controls A–C executed under `linux_bwrap` `ExecSeal` inside a Linux `cgroup v2` workload slice.

## Revalidation

1. Once `capture --units-manifest` lands in `anneal-rustc-capture`, run `verify-projection-identity` across all `zerocopy/proofs/*` units to confirm byte-for-byte identical `Captured.lean` SHA-256 digests against standalone single-unit captures.
2. Re-run the three negative controls (body mutation, `unsupported` sibling isolation, and `--allow-sorry-in-proof` taint key separation) against `cargo anneal verify --all` under `linux_bwrap`.
3. Re-measure `B4` (unrelated `.rs` edit) and `B5` (warm no-op) to verify elimination of the `7.49s` prototype `census` JSON cloning bottleneck.
