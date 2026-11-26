<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Build-System Integration and Orthogonal Receipt v3 Architecture

> **Status: Target Architecture / In-Progress.**
>
> **Shipped today (Stage 0 alpha, [`#4095`](https://github.com/google/zerocopy/issues/4095)):**
> `cargo-anneal` supports `verify --request`, `verify --manifest-path`, and
> `verify rustc` on x86-64 Linux with monolithic local `ExecSeal` containment
> (`linux_bwrap` or `linux_landlock_seccomp`), Receipt Schema v3, and the
> decoupled [`theory/bundle-manifest.json`](../theory/bundle-manifest.json)
> manifest pinned to Lean `v4.34.1` (see [alpha guide](alpha.md) and
> [elaborator containment](elaborator-containment-design.md)).
>
> **Target architecture described here:** The build-system-agnostic
> five-phase split-action contract, orthogonal `kernel_verdict` vs.
> `elaboration_containment` Receipt v3 split, two-tier cross-crate MIR handoff,
> zero-axiom `nominal` and `fixed-buckets=K` sharding, Lean 4 `module`
> isolation, and Lean `v4.35.0+` cutover are in-progress target designs tracked
> across [`#4012`](https://github.com/google/zerocopy/issues/4012),
> [`#4098`](https://github.com/google/zerocopy/issues/4098),
> [`#4099`](https://github.com/google/zerocopy/issues/4099), and
> [`#4103`](https://github.com/google/zerocopy/issues/4103).

Rust systems crates live across heterogeneous build ecosystems: Cargo, Bazel,
Soong, GN/Ninja, and Buck2 (as well as Nix, CMake, and Meson). Embedding
build-system-specific logic inside Anneal's Trusted Computing Base (TCB) would
bloat the trusted code and cause verification semantics to diverge across
ecosystems.

Anneal avoids that fragmentation by inverting orchestration. Its trusted
binaries (`anneal-rustc-capture`, `cargo-anneal`, and the NDJSON audit
comparator) define **one build-system-agnostic, five-phase split-action
contract** over content-addressed manifests, unmodified Lean 4 `module`
artifacts, and immutable build-action receipts. Every build system—including
`cargo anneal verify` itself—acts as a thin scheduler projecting that contract
onto its native action graph without duplicating or modifying production Rust
targets.

## 1. Core design constraints

Five invariants govern build-system integration across all supported ecosystems:

1. **Zero production-target duplication, with a fixed capture profile:**
   Verification binds directly to unmodified production Rust targets
   (`rust_library`, `rust_binary`, `rust_test`, Cargo `[lib]`/`[[bin]]`).
   Production `.rmeta` and `.rlib` outputs remain untouched. Capture does not
   reuse the production compilation profile: it always compiles with
   `-Copt-level=0` and `-Cdebug-assertions=no`, and with
   `-Coverflow-checks=no` unless `--overflow-checks` selects
   `-Coverflow-checks=yes`. It refuses any compilation whose options or
   resolved session enable optimization or debug assertions, or whose
   overflow-check setting differs from the requested one. It carries over the
   panic strategy (`unwind` or `abort`), `--cfg` values, edition, and target
   triple. The verified MIR can therefore differ from the MIR of a production
   build, for example one with debug assertions on, or one with overflow
   checks on when capture ran without `--overflow-checks`; see [Capture
   profile and the binary
   seam](trust-model.md#capture-profile-and-the-binary-seam).
2. **Build-action-native execution (no host-test platform inversion):** All
   verification phases run as build actions (`cfg = "exec"` tools operating on
   target-configured Rust inputs) that emit an immutable Receipt v3 artifact.
   Test targets validate or archive the receipt rather than running capture or
   compilation inside a host test runner, ensuring cross-compiled targets (for
   example, `aarch64` or `riscv64`) are never silently verified as host
   `x86_64`.
3. **Lexical paths and open-FD identity (CAS-symlink safe):** Trusted binaries
   never call `fs::canonicalize()` on sysroots, compiler binaries, or source
   files, because content-addressed symlink forests break sibling `mod` lookup
   and relative sysroot layouts. Instead, capture normalizes paths lexically,
   authenticates inputs via open-FD `fstat()` (`st_dev`, `st_ino`) regular-file
   checks and streaming SHA-256 digests, and emits path-free logical prefixes
   (`crate/`, `out_dir/`, `workspace/`) in `CaptureManifest.json` for
   cross-worker remote-cache determinism.
4. **Honest, non-spoofable containment and provenance:** Receipt v3 separates
   self-verified kernel soundness from execution-environment containment. No
   CLI flag or unsigned workspace file can mint a self-verified containment
   claim for an external build executor.
5. **Subject-only build rules:** Target declarations specify only the
   verification subject (`rust_target`, `specs`, `proofs`, optional `--select`,
   `verify_deps`, and sharding mode). Verifier policy—toolchain pins,
   containment requirements, cache write permissions, and taint enforcement—is
   locked centrally.

## 2. The five-phase split-action contract

```text
[Production Rust Target]                         [Portable Theory Manifest]
  (target platform & profile;                      theory/bundle-manifest.json
   optional Tier-1 .verify.mir OR                  theory/theory-dag.json
   Tier-2 opt-in .verify.rmeta)                    (Trusted.* + Anneal.* DAG)
          │                                                    │
          ▼                                                    │
┌────────────────────────────────────────────┐                 │
│ Phase 1: anneal-rustc-capture              │                 │
│   capture-rustc (own argv, env-safe)       │                 │
│   • Forces opt-level=0, no debug           │                 │
│     assertions; overflow checks only       │                 │
│     under --overflow-checks                │                 │
│   • Keeps -Cpanic=unwind|abort, --cfg      │                 │
│   • Injects -Zmir-preserve-ub              │                 │
│             --emit=metadata                │                 │
│   • Runs items_of_instance BFS for         │                 │
│     required_consts CTFE (no LLVM codegen) │                 │
│   • Two-Pass closed-world (dev,ino) DSO    │                 │
│     & proc-macro residency hashing         │                 │
│   Emits: Captured.lean (Lean 4 module)     │                 │
│          CaptureManifest.json (path-free)  │                 │
└─────────────────────┬──────────────────────┘                 │
                      │         ┌───────────────────────────┐  │
                      │         │ Phase 2: spec-preflight   │◄─┼── Spec/*.lean
                      │         │ (isolated: 0 proof/theory)│  │   only
                      │         └────────────┬──────────────┘  │
                      ▼                      ▼                 │
           ┌────────────────────────────────────────────┐      │
           │ Phase 3: cargo-anneal gen-expected         │      │
           │   --shard-mode={none|nominal|              │      │
           │                 fixed-buckets|dynamic}     │      │
           │   Emits: Expected.lean                     │      │
           │          [Expected/Shard_*.lean: 0 axioms] │      │
           │          expected_manifest.json            │      │
           └─────────────────────┬──────────────────────┘      │
                                 ▼                             ▼
┌────────────────────────────────────────────────────────────────────────────┐
│ Phase 4: Per-File Deterministic Lean 4 module Compilation                  │
│   lean --setup <setup.json> -j1 -M<mb> -t0                                 │
│        -DElab.async=false -Ddebug.skipKernelTC=false                       │
│   • Upstream imports mount public .olean + .ir.sig only (early cutoff)     │
│   • Shards compile at depth D = 1 (zero cross-shard proof imports)         │
│   • Local Ninja/Soong/CMake/Meson run via compile-lean (ExecSeal +         │
│     byte-for-byte move-if-changed for restat=1 early cutoff)               │
└────────────────────────────────────┬───────────────────────────────────────┘
                                     ▼
┌────────────────────────────────────────────────────────────────────────────┐
│ Phase 5: Universal NDJSON Comparator & Receipt v3                          │
│   5a AnnealExportExpected: {Init,Trusted,Captured,Spec,Expected} -> NDJSON │
│   5b AnnealExportProof (sandboxed): full proof closure -> NDJSON           │
│   5c AnnealVerifyNdjson (pure Rust): DAG identity + pinned Init primitives │
│      + stock v4.35.0+ independent kernels (nanoda_bin + con-ron)           │
│   Emits: Orthogonal Receipt v3 JSON                                        │
└────────────────────────────────────────────────────────────────────────────┘
```

### Key cross-phase details

- **Fixed capture profile (`Phase 1`):** `anneal-rustc-capture` builds its
  own `rustc` argument list from its typed options instead of forwarding a
  production command line. It always passes `-Copt-level=0`,
  `-Cdebug-assertions=no`, and `-Zmir-preserve-ub`, plus
  `-Coverflow-checks=yes` under `--overflow-checks` and `-Coverflow-checks=no`
  otherwise, together with the requested `-Cpanic=unwind` or `-Cpanic=abort`,
  `--cfg` values, edition, and target. It then validates the parsed options
  (`-Copt-level=0`, `-Cdebug-assertions=no`, an explicit `-Coverflow-checks`
  matching the request, and `-Zmir-preserve-ub`) and confirms that the
  resolved session enables overflow checks exactly when requested, failing the
  capture otherwise. The capture manifest's `configuration` records the
  resulting `opt_level`, `debug_assertions`, and `overflow_checks`, and
  `Captured.lean` records the overflow-check setting as
  `Program.overflowChecks`. A production build with overflow checks on can
  contain overflow `Assert` terminators that MIR captured without
  `--overflow-checks` lacks, and one with debug assertions on can contain
  `debug_assert!` checks and `cfg(debug_assertions)` code that capture never
  saw; see [Capture profile and the binary
  seam](trust-model.md#capture-profile-and-the-binary-seam).
- **Zero-LLVM `required_consts` enforcement (`Phase 1`):** Running with
  `--emit=metadata` avoids LLVM codegen overhead, but metadata-only compilation
  can otherwise skip const-evaluation errors in monomorphic items. Inside
  `after_analysis`, capture walks `tcx.items_of_instance` (`UsedItems |
  MentionedItems`) from every captured root so `required_consts` CTFE failures
  are caught without emitting object code.
- **Two-Pass closed-world DSO and `proc_macro` accounting (`Phase 1`):**
  Because CAS symlink forests expose hashed filenames in `/proc/self/maps`,
  capture authenticates loaded executable mappings by `(st_dev, st_ino)` rather
  than pathname substrings. Pass 1 verifies the capture binary, sysroot DSOs,
  and core C runtime libraries before compilation; Pass 2 re-scans after
  analysis to admit only declared `--extern` procedural-macro `.so` files (and
  their `DT_NEEDED` dependencies), recording their SHA-256 digests in
  `CaptureManifest.json` and Receipt v3 `tcb_shims[]`.
- **Two-class `env_depinfo` accounting (`Phase 1`):** Semantic environment
  variables (such as `CARGO_PKG_VERSION` or feature toggles) are hashed into
  `CaptureManifest.json`. Path-prefix variables (`OUT_DIR`,
  `CARGO_MANIFEST_DIR`) are admitted when consumed solely as `include!` /
  `include_bytes!` / `include_str!` path prefixes (normalized to `out_dir/` and
  `crate/`), while failing closed if an unnormalized host path escapes into a
  runtime `&str` MIR constant.
- **Declarative compiler capability table:** To absorb mid-cycle nightly
  `rustc_private` API shifts without a `build.rs` script, `anneal-rustc-capture`
  targets a checked-in `dialect_table.json` mapping compiler revisions to
  declarative capability flags (`--cfg anneal_cap_*`).

## 3. Orthogonal Receipt v3: kernel soundness vs. containment and CI provenance

In monolithic local `cargo anneal verify`, the verifier spawns `lean` directly
inside `ExecSeal` and knows whether OS containment was active. In split-action
remote builds (Bazel RBE, Buck2 REAPI, GN/Soong remote execution, or Linux Nix
sandboxes), Phase 5 runs in a separate process from Phase 4 and cannot verify
from userspace that Phase 4 actually ran remotely without local fallback.
Accepting a CLI flag such as `--external-executor-attestation` to mint an
untainted containment claim would be spoofable security theater: any local
caller can override execution strategies or disable build-system sandboxes.

Target Receipt v3 resolves this cleanly by separating **two orthogonal planes**:

1. **`kernel_verdict` (self-verified by Phase 5):** Cryptographic and
   kernel-checked judgment over exact input, source, and artifact digests
   (`verified`, `tainted`, or `rejected`).
2. **`elaboration_containment` (closed four-variant `enforcer` taxonomy):**

| `enforcer` | `self_verified` | Meaning and permitted contexts | Taints receipt? | Out-of-band CI provenance required? |
| :--- | :---: | :--- | :--- | :--- |
| `self_execseal_in_process` | `true` | Local `cargo anneal verify` (or local Cargo orchestrator delegating to `compile-lean` with a pipe-FD-delivered ephemeral 256-bit HMAC key) under Linux `bwrap` or `Landlock + seccomp` (plus planned macOS Seatbelt and Windows AppContainer backends). | No | No (enforced by binary) |
| `split_action_execseal_unauthenticated` | `false` | Local split-action builds (local Bazel, Soong, GN/Ninja, Buck2, CMake, or Meson) running `compile-lean` (`ExecSeal`) across separate processes without a shared in-process HMAC root. | No (records local orchestrator assumption explicitly) | Optional |
| `external_unverified_by_binary` | `false` | Remote split-action execution (Bazel RBE, Buck2 REAPI, remote GN/Soong, or Linux Nix sandbox). Any caller-provided executor hint is tagged `"security_relevance": "UNTRUSTED"`. | No at `kernel_verdict` (carries `requires_external_provenance` containment status) | **Yes (mandatory)** — CI policy verifies remote-only execution provenance before accepting containment |
| `none` | `false` | Unsandboxed elaboration (`--allow-unsandboxed-elaboration`, default non-hermetic sandboxes, plain local Ninja without `compile-lean`, or Nix with `sandbox = false`). | **Yes** (`unsandboxed_elaboration`) | Cannot be promoted to untainted |

### Out-of-band CI provenance and shared cache isolation

For `external_unverified_by_binary` receipts, CI policy gates close containment
out-of-band rather than trusting self-reported flags inside the receipt:

- **Bazel:** Enforce `--allowed_local_actions_regex` and
  `--remote_local_fallback=false` in CI, and bind the execution log
  (`SpawnExec.runner` confirming remote execution or remote cache hit) into
  SLSA v1.0 provenance. Never treat default `linux-sandbox` (which allows
  network access and host `/` read-only mounts) or default `darwin-sandbox` as
  hermetic containment.
- **Buck2 and GN/Soong remote execution:** Enforce remote-only CI execution
  with local fallback disabled and bind the remote execution trace into CI
  provenance; use local `compile-lean` (`ExecSeal`) for workstation builds.
- **Nix (Linux):** Require `sandbox = true` with zero `__noChroot` derivations
  verified by a trusted CI builder, passing `--lean-loader <ld.so>` so
  `bin/lean` remains unpatched and byte-identical to its pinned digest.
- **Remote cache trust isolation:** Untrusted pull-request or workstation builds
  must never hold write access to trusted CI/main remote action caches (for
  example, `--remote_upload_local_results=false` on untrusted PR builders, with
  separate write-isolated remote cache instances per trust tier).

Receipt v3 also retains explicit structured accounting fields
(`assurance_stage`, `profile_identity`, `permitted_axioms`, `tcb_shims[]`, and
`model_system_relation`) so explicit TCB assumptions—such as loaded procedural
macros or unmodeled downstream LLVM codegen—stay visible without being conflated
with `--allow-*` taint flags.

## 4. Two-tier cross-crate MIR handoff

Naively rebuilding dependencies with extra MIR-encoding flags (such as
`-Zalways-encode-mir`) into `.verify.rmeta` files fails in two ways:

1. **SVH diamond collisions:** Compiler flags that change MIR encoding alter the
   crate's Strict Version Hash (SVH). Whenever a target crate `bar` depends on
   `foo` directly (rebuilt as `.verify.rmeta`) and transitively through an
   unverified dependency `dep_c` (compiled against production `foo.rlib`),
   `rustc` fails with `E0460` or colliding `StableCrateId` errors.
2. **Optimized MIR phase drift:** `-Zalways-encode-mir` encodes `optimized_mir`
   (`Runtime(Optimized)`) rather than `Runtime(PostCleanup)`, where passes such
   as `RemoveUnneededDrops`, `CheckAlignment`, `CheckNull`, `CheckEnums`, and
   `ForceInline` still run even at `-Zmir-opt-level=0 -Zmir-preserve-ub`.

Anneal resolves both problems with a **two-tier cross-crate handoff**:

| Tier | Mechanism | MIR phase and soundness | Diamond / rebuild cost | Intended use |
| :--- | :--- | :--- | :--- | :--- |
| **Tier 1 (Default): Out-of-Band `.verify.mir`** | Each verified dependency is captured independently at exact `Runtime(PostCleanup)` into a sidecar `<crate>.verify.mir` (or `<crate>.Captured.lean`) artifact. Downstream crates compile against untouched production `.rlib`/`.rmeta` files. | Exact `Runtime(PostCleanup)` (zero `optimized_mir` passes, zero `ForceInline`). | Zero SVH collisions; zero upward-closure rebuilds. | Default for monomorphic cross-crate calls and opaque specification-boundary dependencies. |
| **Tier 2 (Opt-In): Sparse Upward-Closure `.verify.rmeta`** | Rebuilds metadata only (`--emit=metadata -Zno-codegen`) for explicitly declared `verify_deps` and their ancestors in the target's dependency graph into a segregated `verify_rmeta/` directory; non-ancestor dependencies stay untouched production `.rlib`s, and propagation stops at `proc_macro_deps`. | `Runtime(Optimized)` with `-Zmir-opt-level=0 -Zmir-preserve-ub` and `-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums,-RemoveUnneededDrops`; any remaining `ForceInline` caveat is recorded in `.verify-meta.json` and Receipt v3 `tcb_shims[]`. | Metadata-only rebuild of the sparse ancestor cone; zero SVH collisions. | Opt-in only when verifying cross-crate generic functions or inlined bodies requiring `rustc` monomorphization (`tcx.instance_mir`). |

To remain immune to `--extern alias=...` renaming and multi-version dependency
diamonds (such as two semver-incompatible versions of the same crate in one
graph), `capture-rustc` accepts unkeyed repeatable `--anneal-verify-meta
<path.verify-meta.json>` flags and matches foreign crates strictly by
`(StableCrateId, Svh, fd_sha256)`. Sysroot crates (`core`, `alloc`, `std`) are
never rebuilt as `.verify.rmeta`—doing so would force an upward-closure rebuild
of every crate in the graph; instead, sysroot calls are modeled at
specification boundaries authenticated by the pinned sysroot digest.

## 5. Dual `nominal` and `fixed-buckets=K` sharding (depth $D = 1$)

Large crates need parallel Lean proof compilation without introducing custom
axioms or breaking static analysis-time build systems.

### Zero-axiom parameterized sharding at depth $D = 1$

When a crate is sharded, `gen-expected` does **not** emit custom `axiom` stubs
for cross-shard dependencies (which would violate strict external-kernel axiom
allowlists). Instead, each shard obligation `Expected/Shard_<i>.lean` is a
zero-axiom parameterized implication:

```lean
ShardObligation_i : Prop := DepSpec_1 -> ... -> DepSpec_m -> ShardSpec_i
```

Each `Proof/Shard_<i>.lean` imports zero other proof shards, enforcing a flat
proof-compilation depth of $D = 1$ across every build system and structurally
preventing cross-shard proof leakage. A lightweight `Proof/Link.lean` module
imports only the public `.olean` interfaces of the shards and composes their
parameterized implications to discharge `Expected.claim` with **zero extra
axioms**.

### Sharding modes across static and dynamic build systems

Build systems such as Bazel (without dynamic content inspection), Soong, GN,
zero-IFD Nix, CMake, and Meson require the build action graph to be known at
analysis time before capture runs. `gen-expected --shard-mode` unifies static
and dynamic build systems under four modes:

1. **`none` (default for small crates):** Emits a single `Expected.lean`.
2. **`nominal` (static, human/agent-authored proofs):** Consumes a checked-in
   `anneal-shards.json` mapping stable human-readable shard names (such as
   `parse_header`) to Rust `DefPath` sets. `gen-expected` validates disjoint
   coverage, acyclic shard dependencies, and absence of cross-shard mutual
   recursion fail-closed. Stable shard names survive unrelated Rust refactors
   and work identically on Cargo, Bazel, Soong, GN, and Buck2.
3. **`fixed-buckets=K` (static, zero build-file churn):** Statically declares
   `K` bucket modules (`Expected/Bucket_0..K-1.lean`, emitting `True` for empty
   buckets) at analysis time and deterministically bin-packs call-graph
   strongly connected components (SCCs) across the `K` buckets. This delivers
   $K$-way parallel compilation and remote caching on static build systems
   (Bazel, Soong, GN) with zero checked-in shard-plan churn.
4. **`dynamic` (dynamic action graphs):** Emits an SCC DAG in
   `expected_manifest.json` for build systems with native dynamic build-graph
   expansion (Buck2 `dynamic_output_new` and Cargo's parallel DAG planner).

*(Note: `cargo anneal shard-plan` currently writes `anneal-shards.json` using
`ShardPlan` v1, a generated numeric Tarjan-SCC topology lockfile paired with
`Proof.IdTree` and `BinChunkTree` assembly; the `nominal` `DefPath`-map mode
above remains planned `gen-expected` design.)*

For crates with multiple user-authored `Spec/*.lean` or `Proof/*.lean` files,
static build systems consume a checked-in generated dependency graph emitted via
`lean --deps-json` (zero `lake`, zero elaboration) and validated in CI, while
Buck2 and Cargo discover user module imports dynamically.

## 6. Lean 4 `module` isolation, 3-layer manifests, and `v4.35.0` target

### Dual-view zero-mutation Lean 4 `module` artifacts

Native Lean 4 `module` compilation writes public theorem signatures as
interface declarations in `.olean` while keeping proof terms in `.olean.private`
(alongside `.ir.sig` / `.ir`). This supersedes binary `.olean` stubbing:

- **Fast incremental early cutoff:** Ordinary upstream imports mount only
  public `.olean` and `.ir.sig` files (`0` bytes of `.olean.private`), so
  editing an upstream proof body without changing its exported statement or
  axiom set does not trigger downstream recompilation.
- **Zero-mutation external kernel replay:** The exact same unmodified 5-part
  `module` outputs feed Phase 5's NDJSON export (`5a`/`5b`) with zero binary
  patching and zero extra axioms.
- **Mandatory determinism flags:** Batch and remote-cached Phase 4 actions MUST
  pass `-DElab.async=false -j1`. With asynchronous elaboration enabled,
  `.olean.private` metadata can vary nondeterministically across runs and
  workers.
- **`move-if-changed` for Ninja-backed builds:** Plain Ninja `restat = 1` misses
  early cutoff when `lean` rewrites identical `.olean` bytes with a newer
  timestamp. `compile-lean` compares outputs byte-for-byte before renaming,
  preserving `mtime` when unchanged.

### Three-layer manifest separation

Compiled `.olean` headers encode toolchain build configuration (such as whether
Lean was built with GMP support), so binary `.olean` digests cannot live in one
universal Git-tracked lockfile. Anneal separates manifests into three layers:

| Layer | Path | Tracked in Git? | Role |
| :--- | :--- | :---: | :--- |
| **Layer 1: Cargo theory bundle** | [`anneal/theory/bundle-manifest.json`](../theory/bundle-manifest.json) | Yes (shipped) | Sorted SHA-256 opt-in source list embedded as pure JSON into self-contained `cargo-anneal` ([`#4111`](https://github.com/google/zerocopy/pull/4111)). |
| **Layer 2: Portable module DAG** | `anneal/theory/theory-dag.json` (target) | Yes | ABI-free source and import DAG over `Trusted.*` and `Anneal.*` modules, projected into build definitions for Bazel, Soong, GN, Buck2, and other systems without build-time `lake`. |
| **Layer 3: Per-ABI compiled lock** | `theory-artifacts.<abi>.lock.json` (target, optional) | No (release/cache) | Maps compiled `.olean*` / `.ir*` digests and `init_primitives_cone.ndjson` digests for a specific `(lean_version, build_flags, host_arch)` tuple. |

### Lean `v4.35.0` target and temporary compatibility window

Anneal currently pins `leanprover/lean4:v4.34.1`
([`trusted/lean/lean-toolchain`](../trusted/lean/lean-toolchain)). The target
architecture moves to **Lean `v4.35.0+`**, which ships `leanexport`,
`nanoda_bin`, `con-ron`, and multi-kernel checking in the standard toolchain
(eliminating separate external kernel builds). During transition, Anneal's
runtime Lean sources and `module` build contract are designed to remain
compatible across a sliding compatibility window (`v4.33.1`–`v4.35.0`), with
only a small compatibility wrapper where legacy in-process replay still runs
prior to full NDJSON Comparator cutover.

## 7. OSS build-system adapter matrix and zero-`.lake` IDE parity

Across every build ecosystem, roughly 85–92% of verification logic stays inside
Anneal's shared Rust/Lean primitives; each build adapter is thin scheduling
glue:

| Build system | Production target binding | Sharding & early cutoff | Containment & CI provenance |
| :--- | :--- | :--- | :--- |
| **Cargo** | `RUSTC_WORKSPACE_WRAPPER` with explicit `--target <triple>` separating target units from host `build.rs` / `proc-macro` units. | `none`, `nominal`, or `dynamic` (`ParallelDagPlan` + content-addressed local cache). | `self_execseal_in_process` (pipe-FD ephemeral HMAC to `compile-lean`). |
| **Bazel** | Capture aspect on `@rules_rust` `rustc` actions (never metadata-only actions); build-action-native target configuration. | `none`, `nominal`, or `fixed-buckets=K`; public `.olean`-only upstream mounts for Skyframe early cutoff. | Remote RBE with `--allowed_local_actions_regex`, `--remote_local_fallback=false`, `--remote_upload_local_results=false` on PRs, and SLSA spawn-log provenance (or local `compile-lean`). |
| **Soong** | Build-action capture attached to Soong `rust_library` / `rust_binary` Ninja rules under the target configuration without modifying production outputs. | Static analysis-time `none`, `nominal`, or `fixed-buckets=K`; `compile-lean` `move-if-changed` + Ninja `restat = 1` early cutoff. | Local `compile-lean` (`split_action_execseal_unauthenticated`) or remote-only CI execution with out-of-band provenance. |
| **GN / Ninja** | Auxiliary `.anneal_capture` rule under `$target_toolchain` forwarding explicit `inputs` and preserving output-dir hygiene; host test targets consume the target-configured receipt. | Static `none`, `nominal`, or `fixed-buckets=K`; `compile-lean` `move-if-changed` + Ninja `restat = 1`. | Local `compile-lean` (`split_action_execseal_unauthenticated`) or remote-only CI execution (local fallback disabled) with provenance. |
| **Buck2** | Subtarget / anonymous capture action on `prelude//rust`; copy-materialized dynamic executables when flat CAS symlinks break `$ORIGIN`. | `none`, `nominal`, or `dynamic` via `dynamic_output_new`; digest-only REAPI early cutoff. | CI `--remote-only` + REAPI trace / SLSA provenance (write-restricted PR namespace); local `compile-lean`. |

### Zero-`.lake` IDE-vs-CI parity (`anneal-project.json`)

To avoid `.lake/` symlinks in repositories that forbid generated files in
source trees—and to prevent IDE-vs-CI configuration drift—every build adapter
projects a lightweight **`anneal-project.json`** workspace descriptor
(analogous to `rust-analyzer`'s `rust-project.json`). One universal
`cargo-anneal` `setup-file` shim serves standard Lean 4 editors (`vscode-lean4`,
Neovim, Helix) directly from `anneal-project.json` without `lakefile.toml` or
`.lake/` directories. Interactive editor sessions may use fast incremental
elaboration for tactic feedback, remain explicitly outside Anneal's TCB
([`THREAT_MODEL.md`](../THREAT_MODEL.md) Section 2.1), and never emit Receipt
v3.
