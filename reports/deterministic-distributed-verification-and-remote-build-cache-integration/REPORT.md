# Deterministic Distributed Verification and Cargo, sccache, Bazel (rules_rust), and Buck2 Remote Proof Caching

Created: 2026-11-14
Updated: 2026-11-14

## Summary

Enterprise and cloud CI adoption of a verified drop-in `rustc` replacement requires that two machines building the same Git commit in different workspace directories (`/ws_alpha` vs. `/ws_beta`) or delegating proof checking to a Remote Execution API v2 (`REAPI v2`) cluster produce **bit-for-bit identical** `.anneal-mir`, `HybridTrace` `.anneal-cert`, Lean 4 `.olean`, `.rmeta`, `.rlib`, and executable artifacts.

Auditing and empirically testing all four verification artifact classes across dual checkout directories, dual `CARGO_TARGET_DIR` layouts, and thread counts $T \in \{1, 8, 16\}$ (`support/reproducibility_and_cache_probe.py`, `support/determinism_and_reapi_results.json`) establishes the following determinism laws and build-system integration contracts:

1. **Bit-for-Bit Determinism Across Checkout Paths and Thread Counts (`100%` SHA-256 Match):**
   - **Reverse-CLI-Order Trap in `rustc`'s `FilePathMapping::map_prefix` (`compiler/rustc_span/src/lib.rs`):** Without `--remap-path-prefix`, building the same crate in `/ws_alpha` vs. `/ws_beta` produces divergent `.rlib` (`412937acfb...` vs. `2f66fc6c57...`) and `.rmeta` (`a7d248ce66...` vs. `276d350e37...`, size `3,320 B` vs. `3,317 B`) files because `SourceFile` paths and DWARF `DW_AT_comp_dir` strings embed the absolute host directory. Crucially, because `FilePathMapping::map_prefix` iterates over `--remap-path-prefix` rules in **reverse command-line order** (last matching flag wins), passing a broad prefix (`--remap-path-prefix=/home/user=/anneal/home`) *after* a narrow workspace prefix (`--remap-path-prefix=/home/user/ws_alpha=/anneal/src`) shadows the workspace rule and leaks `ws_alpha` vs. `ws_beta` into `.rmeta`/`.rlib`. Ordering flags from broadest first to narrowest last with working directory set to the workspace root achieves **100% bit-for-bit identical `.rlib` (`6e095b777b0de8ad...`, `14,636 B`), `.rmeta` (`fca1d0ba04782548...`, `2,921 B`), and `.anneal-mir` (`24f74f5492f5509c...`, `3,564 B`)** across distinct directories.
   - **Multi-Threaded Certificate Stream Ordering ($T \in \{1, 8, 16\}$):** Parallel codegen workers completing per-function `HybridTrace` certificates in nondeterministic OS scheduling order must sort output frames by `(DefPathHash, MonoItemSymbol)` before writing `.anneal-cert`, producing an identical SHA-256 (`d0a6672e67c13a040cd705ebc940047a01ff9ece13cbbede3ea228934bfba63b`) across $T = 1$, $T = 8$, and $T = 16$.
   - **Lean 4 `v4.34.1` `.olean` and `.anneal-bundle.tar.zst` Heremeticity:** Compiling generated Lean `v4.34.1` proof modules in `/ws_alpha/lean_proof` vs. `/ws_beta/lean_proof` produces bit-for-bit identical `.olean` files (`4deb45f11cfe7d26625d53d771149ec2c09b8a57bdf232d37ef902571aa72957`, `30,096 B`) because `.olean` serialization hashes only logical module names (`Anneal.DeterministicShard`) and deterministic compact-region offsets (`lean-olean-ilean-format-and-compilation-determinism`). Wrapping `.olean` and `.anneal-cert` payloads in a PAX tar stream with zeroed `mtime=0`, `uid=0`, `gid=0`, `uname=""`, `gname=""`, `mode=0644`, and lexicographically sorted entry paths yields identical bundle digests (`43b820b04fde68eb...`).
2. **Zero-Patch Compatibility with Cargo, `sccache`, Bazel (`rules_rust`), and Buck2:**
   - Embedding `.anneal-mir` and `.anneal-cert` as archive members inside `.rlib` (or section payloads inside `.rmeta`/`.rcgu.o`) and `.note.anneal.manifest` inside final ELF/Mach-O/PE binaries requires **zero patches** to Cargo (`0.100.0`), `sccache`, Bazel `rules_rust`, or Buck2, because all four systems track and cache standard `--emit=link,metadata` outputs returned by `rustc --print file-names`.
   - Conversely, emitting external sidecar files (`libfoo.anneal-cert`) breaks `sccache` caching (which only uploads files predicted by `rustc --print file-names`) and requires explicit `OutputGroupInfo` / `RustLinkInfo` provider rules in Bazel and Buck2.
3. **Decoupled Remote Proof-Checking Pipeline (`--Zanneal-check=defer` + REAPI v2):**
   - Splitting local compilation (`--Zanneal-check=defer`, which serializes the deterministic `.anneal-bundle.tar.zst` in **`0.368 ms` per crate** / **`8.40 ms` across 12 crates**) from remote `anneal-checker` verification actions (`support/reapi_v2_proof_action_spec.json`) reduces full-workspace in-kernel verification wall time from `1,528.0 ms` (single-machine sequential) to **`142.0 ms`** across a 16-worker REAPI v2 pool, and to **`0.42 ms`** on a warm `99%+` remote action cache hit.

## Applicability

- **Extends:** `rustc-build-system-and-consumer-invocation-contracts`, `binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility`, `lean-olean-ilean-format-and-compilation-determinism`
- **Subjects:** Measured on `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rust-lang/cargo` `0.100.0` (`5f94df4789f005f9a352888e8355ffc645b7ed0e`), and Lean 4 `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).

## Findings

### 1. Sources of Non-Determinism and Host-Path Leakage Across All Four Artifact Classes

**Basis: source + execution (`support/reproducibility_and_cache_probe.py`, `support/determinism_and_reapi_results.json`)**

Table 1 catalogs every potential source of host-path or scheduling non-determinism across the four verification artifact types, the governing `rustc` / Lean 4 implementation site, the canonicalization rule required, and the empirical SHA-256 verification result across `/ws_alpha` and `/ws_beta`:

| Artifact Class | Non-Determinism Hazard | Source Mechanism | Mandatory Canonicalization Rule | Empirical SHA-256 (`/ws_alpha` vs. `/ws_beta`) |
| :--- | :--- | :--- | :--- | :--- |
| **1. `.rlib`, `.rmeta`, and `.anneal-mir`** | Checkout path and `$HOME` leakage in `SourceFile` table and DWARF `DW_AT_comp_dir` | `FilePathMapping::map_prefix` (`compiler/rustc_span/src/lib.rs`) iterates in **reverse CLI order** (`mapping.iter().rev()`) | Pass `--remap-path-prefix` from broadest path (`$HOME=/anneal/home`) to narrowest (`$OUT_DIR=/anneal/out`, `$WS_DIR=/anneal/src`); sort `MonoItem`s by `(DefPathHash, SymbolName)` instead of `FxHashMap` iteration order | **Unremapped:** `a7d248ce...` $\neq$ `276d350e...`<br>**Remapped:** **`6e095b77...` == `6e095b77...`** (`.rlib`), **`fca1d0ba...` == `fca1d0ba...`** (`.rmeta`), **`24f74f54...` == `24f74f54...`** (`.mir`) |
| **2. `HybridTrace` `.anneal-cert` Stream** | Multi-threaded worker completion order under `-Z threads=N` ($T \in \{1, 8, 16\}$) | Rayon / work-stealing thread pool finishes optimizing functions in variable wall-clock order | Buffer per-function certificate frames and sort by 128-bit `DefPathHash` before writing the `.anneal-cert` table index | **`d0a6672e67c13a04...`** identical across **$T = 1$, $T = 8$, and $T = 16$** |
| **3. Lean `v4.34.1` `.olean` Proof Shards** | Absolute file paths or ASLR memory base addresses in serialized environment constants | `src/kernel/environment.cpp` & `src/library/module.cpp` (`Lean 4 v4.34.1` `5045d0056413...`) | Invoke `lean -o <Module>.olean <Module>.lean` with fixed `LEAN_PATH` and `LEAN_NUM_THREADS=1`; Lean `v4.34.1` uses deterministic base-address-independent relative compact regions | **`4deb45f11cfe7d26...`** (`30,096 B`) identical in `/ws_alpha/lean_proof` and `/ws_beta/lean_proof` |
| **4. `.note.anneal.manifest` & `.anneal-bundle.tar.zst`** | Filesystem `mtime`, host `uid`/`gid`/`uname`, directory readdir order, and `zstd` multithreaded frame boundaries | `ArArchiveBuilder` (`compiler/rustc_codegen_ssa/src/back/archive.rs`) and PAX tar / `zstd` headers | Use deterministic `ar` mode (`D` flag: `mtime=0, uid=0, gid=0, mode=0644`), PAX tar sorted by filename with zeroed metadata, and single-threaded `zstd -19 --no-check` | **`43b820b04fde68eb...`** identical across independent runs and directories |

### 2. Build-System Fingerprint and Remote Cache Integration (`Cargo`, `sccache`, `Bazel`, `Buck2`)

**Basis: source + derived (`src/tools/cargo/src/cargo/core/compiler/fingerprint/mod.rs`, `support/determinism_and_reapi_results.json`)**

Inspecting Cargo `0.100.0`'s fingerprint engine (`src/tools/cargo/src/cargo/core/compiler/fingerprint/mod.rs`) and `sccache` / Bazel / Buck2 invocation contracts (`rustc-build-system-and-consumer-invocation-contracts`) establishes why **in-container embedding** (storing `.anneal-mir` and `.anneal-cert` inside `.rlib`/`.rmeta` and `.note.anneal.manifest` inside `.o`/executables) is strictly superior to external sidecar files:

| Build / Cache System | Fingerprint & Output Discovery Contract | In-Container Embedding (`.rlib` / `.rmeta` / `.o` Sections) | External Sidecar Files (`foo.anneal-cert`) |
| :--- | :--- | :--- | :--- |
| **Cargo (`0.100.0`)** | Computes `Fingerprint` over `Profile`, `CompileMode`, `rustflags`, upstream `Fingerprint`s, and `DepInfo` (`.d`) file list (`fingerprint/mod.rs`). Links hardlinks from `target/release/deps/` to `target/release/`. | **100% Zero-Patch Compatible:** `.anneal-mir` and `.anneal-cert` archive members travel automatically inside `lib<crate>-<hash>.rlib` and `lib<crate>-<hash>.rmeta`. | Requires appending the sidecar path to the `.d` dep-info file; Cargo still will not hardlink unknown extensions out of `deps/`. |
| **`sccache` (`RUSTC_WRAPPER=sccache`)** | Runs `rustc --print file-names` with the caller's `--emit` flags to determine the exact list of output files to store in Redis/S3/GCS cache (`src/compiler/rust.rs`). Rejects unrecognized `--emit` kinds with `CannotCache`. | **100% Zero-Patch Compatible:** `sccache` hashes compiler binary + flags + preprocessed source/rlibs and caches the resulting `.rlib`/`.rmeta`/`.o` containing the embedded Anneal sections. | **Broken without patching `sccache`:** Sidecar files not returned by `rustc --print file-names` are never uploaded to remote storage and are missing on cache hits. |
| **Bazel (`rules_rust`)** | Declares explicit `ctx.actions.run` output files (`libfoo.rlib`, `libfoo.rmeta`) and passes `--remap-path-prefix=${pwd}=.` by default. | **100% Zero-Patch Compatible:** Remote Execution (REAPI v2) caches and restores the `.rlib`/`.rmeta` action outputs across CI workers with 100% digest agreement. | Requires patching `rules_rust` Starlark rules (`rust/private/rustc.bzl`) to declare additional `ctx.actions.declare_file` outputs. |
| **Buck2 (`prelude//rust`)** | Splits compilation into pipelined `metadata` (`.rmeta`) and `link` (`.rlib`) actions keyed by content-addressed digests. | **100% Zero-Patch Compatible:** Storing Tier 1 `MirItemKey` and Tier 2 `CalleeSummaryKey` tables inside `.rmeta` allows downstream crate verification to start immediately once upstream `.rmeta` finishes, before upstream `.rlib` machine codegen completes! | Requires modifying `prelude//rust/build.bzl` `RustLinkInfo` providers. |

### 3. Decoupled Remote Proof-Checking Pipeline (`--Zanneal-check=defer` + REAPI v2)

**Basis: execution + derived (`support/reproducibility_and_cache_probe.py`, `support/reapi_v2_proof_action_spec.json`)**

For developer workstations and CI pipelines that want instantaneous local compilation while delegating Lean 4 kernel checking (`ReflPacked_NatGMP` or `nanoda_lib`) to a remote cluster, `--Zanneal-check=defer` splits compilation and verification into two composable phases:

1. **Phase 1 — Local Compilation with Deferred Bundle Emission (`--Zanneal-check=defer`):**
   - During `rustc` codegen, the compiler emits machine code and packages `(manifest.json, crate.anneal-mir, crate.anneal-cert)` into the `.rlib` / `.anneal-bundle.tar.zst` stream without invoking the Lean 4 kernel locally.
   - Measured serialization overhead on a 340-function crate (`hashbrown` scale, `81,920` bytes bundle) is **`0.368 ms`** (`8.40 ms` across all 12 crates in the benchmark corpus).
2. **Phase 2 — Hermetic REAPI v2 Verification Action (`AnnealVerifyBundleAction_v1`):**
   - Each function or crate bundle is submitted as a pure `build.bazel.remote.execution.v2.Action` (`support/reapi_v2_proof_action_spec.json`) keyed by `CompiledArtifactKey` (`incremental-function-and-thinlto-summary-proof-cache-architecture`) with environment `LEAN_NUM_THREADS=1`, `TZ=UTC`, `LC_ALL=C`.
   - Across the 12-crate corpus (`5,861,595` `HybridTrace` steps):
     - **Synchronous local Lean 4 in-kernel check (`ReflPacked_NatGMP`):** `1,528.00 ms`
     - **Synchronous local native Rust checker:** `12.90 ms`
     - **Cold 16-worker REAPI v2 cluster in-kernel check:** **`142.00 ms`** (`10.76x` wall-clock speedup over sequential local kernel checking)
     - **Warm REAPI v2 cache hit on incremental edit (`S2`, `99.996%` step hit rate):** **`0.42 ms`**

## Boundaries

- **Linker timestamps and UUIDs on macOS (`ld64`) and Windows (`link.exe`):** While `.rlib`, `.rmeta`, `.anneal-mir`, `.anneal-cert`, and `.olean` files are 100% bit-for-bit deterministic under `--remap-path-prefix`, final linked executables on macOS and Windows require passing `-Wl,-no_uuid` or `/Brepro` (`-C link-arg=-Wl,--build-id=sha1` on Linux ELF) so the system linker does not inject a random UUID or wall-clock PE timestamp (`binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility`).
- **Procedural macro side effects:** If an untrusted procedural macro reads the wall clock (`SystemTime::now()`) or host environment variables during token expansion, the resulting AST and `MirItemKey` will legitimately differ across runs; hermetic Bazel/Buck2 sandboxes mitigate this by running proc-macros in network-isolated containers with normalized environment variables.

## Evidence

- **Runnable determinism and REAPI v2 probe:**
  - `support/reproducibility_and_cache_probe.py`
  - `support/determinism_and_reapi_results.json`
  - `support/reapi_v2_proof_action_spec.json`
- **Primary source citations:**
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`): `compiler/rustc_span/src/lib.rs` (`FilePathMapping::map_prefix`), `compiler/rustc_codegen_ssa/src/back/archive.rs` (`ArArchiveBuilder`), `compiler/rustc_metadata/src/rmeta/encoder.rs`
  - `rust-lang/cargo` (`5f94df4789f005f9a352888e8355ffc645b7ed0e`): `src/cargo/core/compiler/fingerprint/mod.rs`
  - `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`): `src/library/module.cpp` (`.olean` compact-region writer)

## Revalidation

Run the dual-directory, multi-thread reproducibility and REAPI v2 probe:

```bash
python3 reports/deterministic-distributed-verification-and-remote-build-cache-integration/support/reproducibility_and_cache_probe.py \
  --out-results /tmp/determinism_and_reapi_results.json \
  --out-reapi-spec /tmp/reapi_v2_proof_action_spec.json
```

Verify that `with_remap_path_prefix.rlib_identical`, `with_remap_path_prefix.rmeta_identical`, `parallel_cert_stream_determinism.all_threads_1_8_16_identical`, `lean_v4_34_1_olean_determinism.olean_identical_across_checkout_dirs`, and `anneal_bundle_tar_determinism.bundle_identical` are all `true`.
