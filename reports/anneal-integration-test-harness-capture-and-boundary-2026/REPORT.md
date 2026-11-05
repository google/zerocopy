<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Integration Test Harness Architecture, Dual-Profile MIR Capture, and Crate Boundary Validation

## Summary

- **Twelve of nineteen historical `google/zerocopy` Anneal/Hermes integration
  test failure modes are eliminated by construction in `joshlf/anneal`, while
  seven survive or mutate into new forms.** Replacing Charon, Aeneas, Lake, and
  Mathlib with direct `rustc_driver` `Runtime(PostCleanup)` capture
  (`anneal-rustc-capture`), direct `lean` CLI compilation over a 10-module
  prefix, and `.olean` kernel environment inspection (`anneal-audit`) removes
  `.lake/packages/mathlib` disk amplification, Lake lockfile churn, `Lake.DSL`
  elaboration OOMs, and Cargo `RUSTC_WORKSPACE_WRAPPER` cache poisoning.
  However, process-local `BUILT_CAPTURE` and `PREFIX_CACHE` lifetimes, quadratic
  $O(N^2)$ `Proof.lean` reduction scaling under fixture coalescing, opaque
  `Anneal.proveCrate Mir.crate rfl` negative test errors, strict target crate
  file allowlists, and dual-profile (`debug` vs. `release`) MIR divergence
  remain active architectural constraints.
  Basis: Direct source inspection of `joshlf/anneal` at
  `5d2b5702871baf19c1a42d327ed2e80b231f34d2` and `google/zerocopy` at
  `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`, paired with empirical timing and
  memory probes in `support/capture_and_scaling_metrics.json`.

- **`anneal-rustc-capture` emits byte-for-byte deterministic `Mir.lean` files
  across arbitrary filesystem paths without `--remap-path-prefix`.** The
  extractor locks `src/lib.rs` by `(st_dev, st_ino)` via `GuardedFileLoader`,
  hooks `mir_drops_elaborated_and_const_checked` before `Steal<Body>` is stolen
  by `mir_for_ctfe` or `optimized_mir`, keys all item and body tables by
  crate-local `DefIndex` in `BTreeMap`/`BTreeSet` with topological dependency
  sorting, and omits source spans and file paths from `Mir.lean`. Capturing the
  same crate from shallow and deeply nested directory trees produces identical
  792-byte outputs (`SHA-256 =
  44e0972a75b52b1a7a1dd9dab8a8bd0f9366f18b3ab7fe0415de46352e79d594`).
  Basis: Source inspection of
  `trusted/rustc-capture/src/{main,hook,items,lean}.rs` at
  `5d2b5702871baf19c1a42d327ed2e80b231f34d2` and empirical determinism probe in
  `support/capture_and_scaling_metrics.json`.

- **Every `anneal-rustc-capture` invocation runs two sequential in-process
  `rustc_driver::run_compiler` passes (`debug` and `release`) in `21.7–23.2 ms`
  (`78.4 MB` max RSS) and rejects any crate whose captured `Mir.lean` differs
  between profiles.** Checked integer arithmetic (`x + 1`), `debug_assert!`, and
  `#[cfg(debug_assertions)]` fail closed because `-Cdebug-assertions` and
  `-Coverflow-checks` alter `Runtime(PostCleanup)` MIR. By contrast,
  `wrapping_add`, integer division `x / y` (which emits an unconditional
  division-by-zero `TerminatorKind::Assert` in both profiles), and raw pointer
  dereferences produce identical `Mir.lean` across both configurations.
  Basis: Source inspection of
  `trusted/rustc-capture/src/main.rs:342-345,569-578` and empirical dual-profile
  probes in `support/capture_and_scaling_metrics.json`.

- **Diagnostic and unsupported-construct handling splits across five distinct
  layers: four fail-fast `anneal-rustc-capture` layers and one fail-closed Lean
  `MirAst` sentinel layer.** CLI validation (`main.rs`), input detective checks
  (`check_inputs`), crate item inventory (`items.rs`), and doc-comment parsing
  (`spec.rs`) abort capture with `anneal-rustc-capture: unsupported crate: ...`
  and exit code `1`. Conversely, `extract.rs` lowers unsupported types,
  statements, Rvalues, and terminators inside function bodies into `.unmodeled`
  and `.unsupported` `MirAst` constructors so private uncalled helpers do not
  break capture; public functions containing those sentinels fail closed during
  Lean proof checking.
  Basis: Source inspection of
  `trusted/rustc-capture/src/{main,items,spec,extract}.rs` and empirical
  diagnostic probes in `support/capture_and_scaling_metrics.json`.

- **`validate_target_crate` and `check_cargo_boundary` require integration test
  fixtures to materialize into clean temporary crate directories
  (`TempCrateDir`) executed by a zero-dependency Rust test harness.**
  `validate_target_crate` enforces a closed 5-file allowlist (`CRATE_FILES`) and
  `#[serde(deny_unknown_fields)]` on `Cargo.toml`, rejecting any fixture
  directory that contains sidecar test metadata (`anneal.toml`,
  `expected.stderr`, or `target/`). Furthermore, because `BUILT_CAPTURE`
  (`1.90s`) and `PREFIX_CACHE` (`15.13s`) are process-local `static
  Mutex<BTreeMap<...>>` caches and `trusted/root-manifest.sha256` locks the
  129-package `Cargo.lock`, running fixtures in-process through
  `cargo_anneal::run_with_io` inside a single zero-dependency integration test
  binary avoids both `17.03s` per-process cold rebuilds and TCB dependency
  bloat.
  Basis: Source inspection of `trusted/cargo-anneal/src/lib.rs:536-687,860,1076`
  and `trusted/cargo-anneal/tests/verify_id.rs` at
  `5d2b5702871baf19c1a42d327ed2e80b231f34d2`.

## Applicability

| Subject | Kind | Version | Revision |
| :--- | :--- | :--- | :--- |
| `joshlf/anneal` | repository | `simplify-trusted` | `5d2b5702871baf19c1a42d327ed2e80b231f34d2` |
| `google/zerocopy` | repository | `main` | `8fb35253fbc703cb2cd0997f4efcda76cf9062b6` |
| `rust-lang/rust` | repository | `1.98.0-nightly (2026-05-30)` | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` |
| `leanprover/lean4` | repository | `v4.34.1` | `5045d0056413266e57c625dcd7c365b10e377c52` |

These findings apply to `joshlf/anneal`'s `simplify-trusted` architecture at
`5d2b5702871baf19c1a42d327ed2e80b231f34d2` (built atop `main` at
`c00e36ade29c57830f07c934774abb347471060c` and `trusted-core` at
`ebac418ccf7c234ae402cf76a491c903bff3be4f`) under its pinned `rustc
1.98.0-nightly` and Lean `v4.34.1` toolchains (`trusted/toolchain.toml`).

## Boundaries

- This report evaluates `anneal-rustc-capture`, `cargo-anneal`, and
  `anneal-audit` at `5d2b5702871baf19c1a42d327ed2e80b231f34d2`, where proof
  generation is non-extensible (`emit_proof_module` emits a fixed
  `Anneal.proveCrate Mir.crate rfl` script and `cargo-anneal` rejects
  user-supplied `.anneal/Proof.lean` overrides via `check_target_crate_files`).
- Detailed Lean 4 kernel compilation scaling curves ($N = 1..50$), negative
  failure-reason attribution (`Anneal.proveCrateOpt`), concrete `ExecNormal`
  kernel stepping, and TCB semantic mutation testing of
  `Trusted/MirSemantics.lean` are covered in the companion report
  [`anneal-lean-verification-scaling-attribution-and-mutation-oracles-2026`](../anneal-lean-verification-scaling-attribution-and-mutation-oracles-2026/REPORT.md).
- Timing and RSS measurements were recorded on an x86_64 Linux workstation using
  `anneal-lean-run` resource bounds and will vary in absolute wall-clock time on
  other hardware, though structural complexity ratios and cache lifetimes are
  machine-independent.

## Findings

### Six-Generation Historical Retrospective: Eliminated vs. Surviving Failure Modes

Basis: Direct architectural comparison between `google/zerocopy`
(`8fb35253fbc703cb2cd0997f4efcda76cf9062b6`, `cargo-anneal` V1 and V2) and
`joshlf/anneal` (`5d2b5702871baf19c1a42d327ed2e80b231f34d2`,
`trusted/{rustc-capture,cargo-anneal,audit,lean}`).

Across six generations of integration and UI test frameworks in
`google/zerocopy` (Hermes `compiletest_rs` skeleton -> Anneal V1 per-test Lake
sandboxes -> Anneal V1 shared-`.lake` worktrees and `ui-anneal` -> Anneal V1
coalesced `verify_Pass.rs` / `verify_Fail.rs` suites -> Anneal V2 Charon-free
4-tier test pyramid -> `joshlf/anneal`), nineteen distinct failure modes
emerged. Twelve of those nineteen failure modes are eliminated by construction
in `joshlf/anneal`, while seven survive or mutate:

| Historical Failure Mode (`google/zerocopy` V1 & V2) | Status in `joshlf/anneal` (`5d2b5702871baf19c1a42d327ed2e80b231f34d2`) | Mechanism / Architectural Disposition |
| :--- | :--- | :--- |
| 1. `.lake/packages/mathlib` disk amplification (`4.2 GB` per test sandbox, `>100 GB` disk exhaustion) | **Eliminated** | No Mathlib dependency and no per-test `.lake` copies; the 10-module `Trusted.*` + `Anneal.*` prefix compiles once into `17.13 MB` of `.olean`s inside `PREFIX_CACHE` (`trusted/cargo-anneal/src/lib.rs:1076`). |
| 2. `lake build` lockfile (`lake-manifest.json`) churn & git fetch races | **Eliminated** | `cargo-anneal` invokes `lean` directly (`lib.rs:1185-1197`) with explicit `LEAN_PATH` and zero `lake` subprocesses during `cargo anneal verify`. |
| 3. `Lake.DSL` / Mathlib import elaboration OOM (`>8 GB` per worker) | **Eliminated** | All Lean files use `prelude` (`Trusted/*.lean`, `Anneal/*.lean`) with selective `Init` imports; peak prefix compilation RSS is `437.3 MB` (`Anneal.MirLemmas`). |
| 4. Charon + Aeneas single-file `.llbc` serialization bottleneck | **Eliminated** | `anneal-rustc-capture` extracts `Runtime(PostCleanup)` MIR directly in-process via `rustc_driver` in `21.7–23.2 ms`. |
| 5. Cargo `RUSTC_WORKSPACE_WRAPPER` fingerprint caching skipping capture | **Eliminated** | `cargo-anneal` invokes `anneal-rustc-capture` directly on `src/lib.rs` (`lib.rs:956-982`) rather than wrapping `cargo check`. |
| 6. Fragile `Regex` scraping of Lean/Charon human-readable logs | **Eliminated** | `anneal-audit` inspects `.olean` binary kernel `Environment` structures directly via `lean_initialize` and `AnnealAudit.auditImports` (`trusted/audit/src/lib.rs:283-427`). |
| 7. `ANNEAL_FORCE_VERIFY_SUCCESS` / env-var production escape hatches | **Eliminated** | `child_command` (`lib.rs:282-292`) calls `cmd.env_clear()` and sets only `PATH="/usr/bin:/bin"`, `HOME`, `TMPDIR`, and tool-specific library paths. |
| 8. Unsound `axiom` / `sorryAx` smuggling in generated proofs | **Eliminated** | Two-stage `.olean` audit (`TrustedBoundary.olean` + target `Mir.olean`/`Proof.olean`) rejects all non-allowlisted axioms, `sorryAx`, opaque constants, and `implemented_by` overrides. |
| 9. `std` vs. `core` sysroot resolution mismatches in UI tests | **Eliminated** | Target crates are restricted to `#![no_std]` (`items.rs:200-206`) compiled against the pinned toolchain sysroot (`--sysroot <tc/rust>`). |
| 10. Multi-crate workspace dependency resolution drift in test fixtures | **Eliminated** | `validate_target_crate` (`lib.rs:640-675`) rejects any `[dependencies]`, `[dev-dependencies]`, `[build-dependencies]`, or `[workspace]` table in a target crate's `Cargo.toml`. |
| 11. Stale `.anneal/` artifact reuse after source edits | **Eliminated** | `check_target_crate_files` (`lib.rs:596-638`) rejects pre-existing `.anneal/` files unless modified; `write_atomic` (`lib.rs:820-858`) atomically replaces `.anneal/Mir.lean` and `.anneal/Proof.lean` via `O_CREAT | O_EXCL` tempfiles + `fs::rename`. |
| 12. TOCTOU race between `src/lib.rs` validation and `rustc` reading disk | **Eliminated** | `GuardedFileLoader` (`trusted/rustc-capture/src/main.rs:76-226`) verifies `(st_dev, st_ino)` across `lstat` and `fstat` and serves `src/lib.rs` from a locked in-memory buffer across both compiler passes. |
| 13. Process-local `BUILT_CAPTURE` & `PREFIX_CACHE` cold-start penalty | **Survives (Mutated)** | `BUILT_CAPTURE` (`1.90s`) and `PREFIX_CACHE` (`15.13s`) live in in-memory `static Mutex<BTreeMap<...>>` maps backed by ephemeral `TempDir`s (`lib.rs:860,1076`). Subprocess CLI tests or separate `tests/*.rs` binaries pay the full `17.03s` cold build per process. |
| 14. Quadratic $O(N^2)$ verification scaling under fixture coalescing | **Survives (Mutated)** | Coalescing $N$ functions into one crate hits $O(N^2)$ Lean kernel reduction in `checkNoDupIds` (`MirLemmas.lean:4103-4142`) and `proveFnsLoop`: optimal at $N = 10$ (`56.7 ms/fn`), degrading to `5.04s` and `703.1 MB` RSS at $N = 50$. |
| 15. Opaque negative test failure attribution ("passing for the wrong reason") | **Survives (Mutated)** | `Anneal.proveCrate Mir.crate rfl` fails with the identical unreduced type mismatch (`Anneal.checkCrate Mir.crate = []`) regardless of *why* verification failed unless `Anneal.proveCrateOpt Mir.crate` is evaluated via `lean --run`. |
| 16. Strict `validate_target_crate` rejection of sidecar fixture files | **Survives (New)** | `CRATE_FILES` (`lib.rs:587-593`) and `#[serde(deny_unknown_fields)]` forbid sidecar files (`anneal.toml`, `expected.stderr`, `target/`) or custom `Cargo.toml` metadata inside target crate directories. |
| 17. Dual-profile (`debug` vs. `release`) MIR divergence on standard Rust idioms | **Survives (New)** | `anneal-rustc-capture` compiles every crate under both `debug` and `release` flags (`main.rs:342-345`) and rejects checked `+`/`-`/`*`, `debug_assert!`, and `#[cfg(debug_assertions)]`. |
| 18. Silent `.unmodeled` / `.unsupported` lowering in `extract.rs` | **Survives (New)** | `extract.rs` lowers unsupported types, statements, Rvalues, and terminators to `.unmodeled`/`.unsupported` rather than emitting capture errors, deferring failure to Lean kernel checking. |
| 19. Lean 4 CLI root-containment error when `cwd` is outside `/tmp` | **Survives (New)** | Invoking `lean` without `--root` requires the `.lean` input path to reside beneath `cwd` (`input file '...' must be contained in root directory`), requiring `cmd.current_dir("/")` (`lib.rs:285`). |

### `anneal-rustc-capture` Determinism, `GuardedFileLoader`, and Dual-Profile `CONFIGS`

Basis: Source inspection of
`trusted/rustc-capture/src/{main,hook,items,lean}.rs` at
`5d2b5702871baf19c1a42d327ed2e80b231f34d2` and empirical probes in
`support/capture_and_scaling_metrics.json`.

#### Path-Independent Byte-for-Byte Determinism

`anneal-rustc-capture` guarantees deterministic output across arbitrary working
directories and filesystem layouts through four mechanisms:

1. **Inode-Pinned In-Memory Source Loading (`GuardedFileLoader`):**
   `GuardedFileLoader::new` (`trusted/rustc-capture/src/main.rs:102-151`)
   canonicalizes `--src` and `--sysroot`, opens `--src` with `O_RDONLY |
   O_NOFOLLOW`, verifies that `lstat` and `fstat` report a regular file with
   identical `(st_dev, st_ino)`, and reads the bytes into `Arc<[u8]>`. Both
   in-process `rustc_driver` runs read `src/lib.rs` from that pinned buffer
   while rejecting any symlink or non-sysroot file access (`main.rs:159-219`).
2. **Pre-Steal `Runtime(PostCleanup)` Hook:** `override_queries`
   (`trusted/rustc-capture/src/hook.rs:42-78`) overrides
   `queries.mir_drops_elaborated_and_const_checked`—the terminal query of the
   `Runtime(PostCleanup)` phase—cloning `Body<'tcx>` inside `steal.borrow()`
   before downstream `mir_for_ctfe` or `optimized_mir` queries steal the buffer.
   The hook guards against nested or synthetic `TyCtxt` invocations via
   `tcx.sess.opts.unstable_opts.treat_err_as_bug.is_none()` (`hook.rs:64-67`).
3. **`DefIndex`-Ordered Collections and Topological Sorting:**
   `collect_crate_items` (`trusted/rustc-capture/src/items.rs:49-189`) stores
   ADTs, traits, trait implementations, and functions in `BTreeMap`/`BTreeSet`
   keyed by crate-local `DefIndex::as_u32()` (`def_id_index`), and orders
   emitted `BodyDecl` records via deterministic depth-first topological sort
   (`dependency_order`, `items.rs:236-291`).
4. **Span-Free Rendering:** `render_mir_module`
   (`trusted/rustc-capture/src/lean.rs:26-48`) emits pure Lean 4 AST literals
   (`Trusted.Crate`) with zero source spans, file paths, or symbol hashes.

Empirically (`support/capture_and_scaling_metrics.json`), capturing `pub fn
id(x: usize) -> usize { x }` from a shallow path (`det_a/sample/src/lib.rs`) and
a 9-level nested path (`det_b/very/deep/nested/.../src/lib.rs`) produces
byte-for-byte identical 792-byte `Mir.lean` files (`SHA-256 =
44e0972a75b52b1a7a1dd9dab8a8bd0f9366f18b3ab7fe0415de46352e79d594`) in `21.8 ms`
and `23.2 ms`, respectively (`78.46 MB` max RSS). No `--remap-path-prefix` flag
is required for positive `Mir.lean` goldens.

#### Dual-Profile (`debug` vs. `release`) MIR Equivalence Gate

`anneal-rustc-capture` defines two compilation configurations in
`trusted/rustc-capture/src/main.rs:342-345`:

```rust
const CONFIGS: [(&str, &[&str]); 2] = [
    ("debug", &["-Cdebug-assertions=on", "-Coverflow-checks=on"]),
    ("release", &["-Cdebug-assertions=off", "-Coverflow-checks=off"]),
];
```

`run` (`main.rs:514-580`) executes `rustc_driver::run_compiler` sequentially for
`"debug"` and `"release"` inside the same OS process (`~21.7–23.2 ms` total for
both runs combined) and compares the rendered `Mir.lean` strings (`if other !=
rendered`, `main.rs:569-578`). Because both passes pass `-Zmir-opt-level=0`
(`compiler_args` at `main.rs:394`), the only differences between the two passes
are `cfg(debug_assertions)`, `-Cdebug-assertions`, and `-Coverflow-checks`:

| Rust Construct | Capture Result (`rc`) | Wall Time | Empirical Behavior Across `debug` and `release` `CONFIGS` |
| :--- | :--- | :--- | :--- |
| `pub fn add1(x: usize) -> usize { x + 1 }` | `1` (Rejected) | `23.1 ms` | `debug` emits `Rvalue::BinaryOp(AddWithOverflow, ...)` + `TerminatorKind::Assert`; `release` emits `Rvalue::BinaryOp(Add, ...)` + `Goto`. Fails with `its MIR differs between the debug and release configurations`. |
| `pub fn add1(x: usize) -> usize { x.wrapping_add(1) }` | `0` (Accepted) | `23.2 ms` | Both configurations lower `wrapping_add` through the intrinsic call to identical `1,087 B` `Mir.lean`. |
| `pub fn check(x: usize) -> usize { debug_assert!(x != 0); x }` | `1` (Rejected) | `22.9 ms` | `debug_assert!` expands to a conditional panic branch only when `cfg(debug_assertions)` is enabled. |
| `pub fn div(x: usize, y: usize) -> usize { x / y }` | `0` (Accepted) | `23.1 ms` | Both `debug` and `release` emit the unconditional division-by-zero `TerminatorKind::Assert` in `Runtime(PostCleanup)` MIR (`1,699 B` `Mir.lean`), which then fails closed in Lean proof checking because `Terminator.assert` is unproved for unconstrained `y`. |
| `#[cfg(debug_assertions)] pub fn f() {}` | `1` (Rejected) | `21.7 ms` | Item inventory differs between `debug` and `release`. |
| `pub unsafe fn read_ptr(p: *const usize) -> usize { unsafe { *p } }` | `0` (Accepted) | `23.2 ms` | Note that `rustc` only inserts `ub_checks` alignment/null assertions inside `core` library methods (`ptr::read`, `NonNull::new_unchecked`), not on raw built-in `*p` place projections (`825 B` `Mir.lean`). |

### Five-Layer Diagnostic and Unsupported-Construct Taxonomy

Basis: Source inspection of
`trusted/rustc-capture/src/{main,items,spec,extract}.rs` at
`5d2b5702871baf19c1a42d327ed2e80b231f34d2` and empirical probes in
`support/capture_and_scaling_metrics.json`.

Integration tests that assert on negative or unsupported inputs must distinguish
between errors caught during capture (layers 1–4, which exit with code `1` and a
deterministic `anneal-rustc-capture:` stderr prefix) and unsupported MIR body
constructs (layer 5, which succeed during capture with exit code `0` and fail
closed during Lean proof checking):

1. **Layer 1 — CLI & Target File Guards (`main.rs:246-339`):** Missing or
   duplicate CLI flags, non-2024 `--edition`, invalid `--crate-name`, or
   symlinked/disallowed file paths in `GuardedFileLoader` fail with
   `anneal-rustc-capture: <reason>`.
2. **Layer 2 — Source & Attribute Detective Scan (`check_inputs`,
   `main.rs:482-505`):** Scans the parsed AST before HIR/MIR lowering and
   rejects multiple source files, `include!` / `include_str!` / `include_bytes!`
   macros, `#[path = ...]` module redirects, and tool/diagnostic attributes
   (`#[rustc_*]`, `#[diagnostic::*]`).
3. **Layer 3 — Crate Item Inventory (`collect_crate_items`,
   `items.rs:49-234`):** Requires `#![no_std]` (`crate must declare #![no_std]`)
   and rejects unsupported top-level items (`Enum`, `Union`, `Static`, `Const`,
   `ForeignMod`, `GlobalAsm`, `Macro`), `unsafe trait` (`trait ... is unsafe`),
   `unsafe impl` (`impl ... is unsafe`), multi-field structs with `invariant`
   clauses (`declares an Anneal invariant clause, which is only supported on
   single-field usize structs`), and `requires` clauses on safe functions (`safe
   function ... has a requires clause; only unsafe fn items may declare
   preconditions`). Note that `items.rs` diagnostics format `DefId`s with the
   crate disambiguator hash (for example, `DefId(0:3 ~ sample[f687]::E)`), which
   depends on `--crate-name` but not on filesystem path because
   `--remap-path-prefix` / virtual loader paths are fixed.
4. **Layer 4 — Doc-Comment Specification Parser (`parse_anneal_spec`,
   `spec.rs:27-350`):** Rejects unknown thread-safety keywords, duplicate `///
   ```anneal` blocks, malformed `requires` / `ensures` / `invariant` clauses
   (`unsupported Anneal block on ...: unsupported ensures clause ...; expected
   result == <ident>`), and `is_safe` clauses outside trait declarations.
5. **Layer 5 — Fail-Closed MIR Body Lowering (`extract_body`,
   `extract.rs:23-391`):** Unlike layers 1–4, `extract_body` does **not** abort
   `anneal-rustc-capture` when a function body uses an unmodeled type (such as
   `&mut T`, raw pointers `*const T`, arrays, or tuples), an unsupported
   projection (`Deref` or nested fields), an unsupported `Rvalue`
   (`CheckedBinaryOp`, `Cast`, `Discriminant`), or an unsupported
   `TerminatorKind` (`SwitchInt` with $\ge 2$ targets, multi-arg calls, or
   inline `Asm`). Instead, `extract.rs` lowers them to `MirTy.unmodeled`,
   `Place.unsupported`, `Rvalue.unsupported`, `Stmt.unsupported`, or
   `Terminator.unsupported` (`extract.rs:68,94,159,205,361`). This design allows
   a crate to contain private uncalled helper functions using arbitrary Rust
   constructs (`probe_private_uncalled_fn` in
   `support/capture_and_scaling_metrics.json` exits `0` with `1,353 B`
   `Mir.lean`), while any public or reachable function whose body contains an
   unsupported sentinel fails closed inside `Anneal.proveCrate`.

### Two-Stage Boundary Audit, `validate_target_crate`, and Harness Architecture

Basis: Source inspection of `trusted/audit/{TrustedBoundary.lean,src/lib.rs}`,
`trusted/cargo-anneal/src/lib.rs:536-687,860-1315`, and
`trusted/cargo-anneal/tests/verify_id.rs` at
`5d2b5702871baf19c1a42d327ed2e80b231f34d2`.

#### Two-Stage `.olean` Boundary Audit (`anneal-audit`)

`cargo-anneal` enforces Lean trust-boundary integrity in two distinct stages
(`trusted/cargo-anneal/src/lib.rs:1060-1073,1208-1231`):

- **Stage 1 — Prefix Audit (`verify_lean_workspace_In_process`):** Compiles
  `trusted/audit/TrustedBoundary.lean` (which imports `Trusted` and `Anneal`)
  and invokes `anneal_audit::verify_boundary_olean_in_process`. This checks four
  invariants across the entire transitive `Environment` of the 10-module prefix
  (`trusted/audit/src/lib.rs:283-427`):
  1. Every `Trusted.*` module `.olean` matches the fresh compilation of
     `trusted/lean/Trusted/*.lean` byte-for-byte.
  2. Only `propext`, `Quot.sound`, and `Classical.choice` appear as axioms;
     `sorryAx` and custom `axiom` declarations are rejected (`[E-AUDIT-AXIOM]`).
  3. Only Lean stdlib allowlisted `opaque` declarations (`OPAQUE_ALLOWLIST`)
     exist (`[E-AUDIT-OPAQUE]`).
  4. Zero `implemented_by` or `extern` C overrides exist (`[E-AUDIT-CSIMP]`).
- **Stage 2 — Per-Crate Target Audit (`audit_target_crate_oleans`):** After
  compiling `.anneal/Mir.lean` and `.anneal/Proof.lean` into a temporary staging
  directory, `cargo-anneal` audits `[Mir, Proof]` via
  `verify_imported_modules_in_process` and asserts that `Proof.olean` exports
  `Proof.crate_verified : Trusted.CrateTheorem Mir.crate` as a genuine
  `ConstantInfo.thmInfo` (`verify_theorem_constant_in_process`,
  `trusted/audit/src/lib.rs:429-481`), blocking `def`, `axiom`, or `opaque`
  spoofing of `Proof.crate_verified`.

#### `validate_target_crate` Constraints on Test Fixtures

`validate_target_crate` (`trusted/cargo-anneal/src/lib.rs:594-687`) enforces two
strict structural checks before invoking `anneal-rustc-capture`:

1. **Closed 5-File Directory Allowlist (`CRATE_FILES`, `lib.rs:587-638`):**
   Every file under the target crate root is discovered via a recursive walk
   that rejects symlinks and rejects any relative path not in: `["Cargo.toml",
   "Cargo.lock", "src/lib.rs", ".anneal/Mir.lean", ".anneal/Proof.lean"]`.
   Furthermore, if `.anneal/Mir.lean` or `.anneal/Proof.lean` already exists on
   disk before `cargo anneal verify` runs and differs from the freshly generated
   content, `write_verified_outputs` (`lib.rs:761-818`) rejects the run
   (`refusing to overwrite modified file`).
2. **Closed `Cargo.toml` Schema (`#[serde(deny_unknown_fields)]`,
   `lib.rs:536-584`):** `TargetCargoToml` and `TargetPackage` use
   `#[serde(deny_unknown_fields)]` and permit only `package.{name, version,
   edition, publish}` plus `[lib] path = "src/lib.rs"`, rejecting any
   `[package.metadata.*]`, `[dependencies]`, or `[features]` tables.

Consequently, **a checked-in directory of target crates cannot store sidecar
test expectations (`anneal.toml`, `expected.stderr`, `README.md`) or build
artifacts (`target/`) inside the fixture crate directory**. Instead, fixtures
should be stored as single `.rs` source files with structured leading `//~`
expectation headers (for example, `//~ outcome: pass` or `//~ outcome:
fail-proof`, `//~ error-scope: make_nonzero`, `//~ error-msg: unproved safe
NonZeroUsize function`) and materialized on demand into a clean `TempCrateDir`
containing only a synthetic `Cargo.toml` and `src/lib.rs`.

#### Zero-Dependency In-Process Test Harness vs. External Runners

At `5d2b5702871baf19c1a42d327ed2e80b231f34d2`, `Cargo.lock` contains 129
packages (127 from `crates.io-index` plus `anneal-audit` and `cargo-anneal`) and
is SHA-256 locked by `trusted/root-manifest.sha256` (enforced by
`check_cargo_boundary` in `verify_id.rs:647`). Comparing the four candidate Rust
integration test harness architectures:

| Harness Architecture | New Crates in `Cargo.lock` | Shares `BUILT_CAPTURE` (`1.90s`) & `PREFIX_CACHE` (`15.13s`)? | Per-Fixture CLI Filtering (`cargo test <name>`) | Verdict for `joshlf/anneal` |
| :--- | :--- | :--- | :--- | :--- |
| 1. Subprocess CLI per test (`Command::new(CARGO_BIN_EXE_cargo-anneal)`) | `0` | **No** — rebuilds `anneal-rustc-capture` and all 10 Lean prefix modules (`17.03s`) in *every* subprocess | Yes | **Unsuitable** for fixture suites (reserve for 1–2 CLI smoke tests). |
| 2. External `datatest-stable` or `libtest-mimic` (`harness = false`) | `2–9` | Yes (within one binary) | Yes | **Disfavored** by `AGENTS.md` dependency discipline: requires updating `Cargo.lock` and `trusted/root-manifest.sha256` for trivial directory iteration. |
| 3. Single integration test binary (`trusted/cargo-anneal/tests/verify_id.rs` or `litmus.rs`) invoking `cargo_anneal::run_with_io` in-process | `0` | **Yes** — pays the `17.03s` cold build once per binary and `~0.23s` per warm 1-fn crate (`~56.7 ms/fn` when coalesced at $N = 10$) | Yes (via `#[test]` functions or `include_dir` / `build.rs` test generation) | **Recommended** — zero external dependencies, zero `root-manifest.sha256` churn, and full in-process `PREFIX_CACHE` reuse. |

## Evidence

- `joshlf/anneal` at `5d2b5702871baf19c1a42d327ed2e80b231f34d2`:
  - `trusted/rustc-capture/src/main.rs:76-226` (`GuardedFileLoader` `(st_dev,
    st_ino)` verification and path restriction), `L342-345` (`CONFIGS` `"debug"`
    and `"release"`), `L482-505` (`check_inputs`), and `L514-580` (dual-profile
    compiler execution and byte-equality gate).
  - `trusted/rustc-capture/src/hook.rs:42-78`
    (`mir_drops_elaborated_and_const_checked` query override and
    `treat_err_as_bug.is_none()` guard).
  - `trusted/rustc-capture/src/items.rs:49-291` (`DefIndex`-keyed
    `BTreeMap`/`BTreeSet` collection and `dependency_order` topological sort).
  - `trusted/rustc-capture/src/spec.rs:27-350` (`/// ```anneal` doc-comment
    parser).
  - `trusted/rustc-capture/src/extract.rs:23-391` (fail-closed `.unmodeled` and
    `.unsupported` lowering).
  - `trusted/cargo-anneal/src/lib.rs:282-292` (`child_command` with
    `env_clear()` and `current_dir("/")`), `L536-687` (`TargetCargoToml`,
    `CRATE_FILES`, and `validate_target_crate`), `L860` (`BUILT_CAPTURE`), and
    `L1076` (`PREFIX_CACHE`).
  - `trusted/cargo-anneal/tests/verify_id.rs:1-817` (`TempCrateDir`, 20
    in-process integration tests, and `check_cargo_boundary`).
  - `trusted/audit/src/lib.rs:283-481` (`verify_boundary_olean_in_process` and
    `verify_theorem_constant_in_process`).
- Local reproducible data in this package:
  - [`support/capture_and_scaling_metrics.json`](support/capture_and_scaling_metrics.json)
    (path determinism SHA-256 receipts, dual-profile divergence timings,
    diagnostic taxonomy exit codes/stderr strings, and workspace manifest
    metrics).

## Related Reports

- [`anneal-lean-verification-scaling-attribution-and-mutation-oracles-2026`](../anneal-lean-verification-scaling-attribution-and-mutation-oracles-2026/REPORT.md)
- [`anneal-v1-integration-test-disk-amplification-f98458e`](../anneal-v1-integration-test-disk-amplification-f98458e/REPORT.md)
- [`rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary`](../rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/REPORT.md)
- [`anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026`](../anneal-two-stage-preaudit-olean-axiom-stubbing-and-conservativity-2026/REPORT.md)
- [`anneal-structural-external-calls-and-tcb-mutation-testing-2026`](../anneal-structural-external-calls-and-tcb-mutation-testing-2026/REPORT.md)

## Revalidation

Revalidate this report when any of the following change:

1. `trusted/rustc-capture/src/main.rs` modifies `CONFIGS` (`"debug"` vs.
   `"release"` compiler flags) or `GuardedFileLoader`.
2. `trusted/rustc-capture/src/extract.rs` changes how unsupported MIR types,
   statements, or terminators are lowered vs. rejected during capture.
3. `trusted/cargo-anneal/src/lib.rs` changes `CRATE_FILES`, `TargetCargoToml`
   validation, or persists `BUILT_CAPTURE` / `PREFIX_CACHE` to disk across OS
   processes.
4. `trusted/toolchain.toml` updates the pinned `rustc` nightly or Lean 4
   revision.
