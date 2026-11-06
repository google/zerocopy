# `rustc` Const Evaluation, Post-Monomorphization Errors (PMEs), Toolchain Pin Coupling, and Sound MIR Capture

## Summary

This report synthesizes four investigations covering the normative and compiler-internal semantics of `const fn` and Compile-Time Function Evaluation (CTFE), toolchain coupling across Anneal, Aeneas, Charon, and `rustc`, post-monomorphization CTFE and layout errors (PMEs), and the `TyCtxt` invariants required for a sound in-process `rustc_driver` MIR capture stage:

1. **Normative `const fn` Eligibility vs. Mandatory Const Contexts and `CompileTimeMachine`:** In the Rust Reference (`ad35aca481751a06afeb23820a672b0f3b11a476`, `82da570bafd9efed421bdbae0f8603ede8dd308b`) and `rustc` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `const fn` marks a function as eligible for evaluation in a const context (array/repeat lengths, `const`/`static` initializers, enum discriminants, const generic arguments, and `const { ... }` blocks), where evaluation is mandatory at compile time in the **target** environment and any overflow, bounds failure, or panic is a compile-time error (`E0080`). Outside a const context, calling a `const fn` executes normally at runtime. Internally, `rustc` evaluates required constants via `eval_in_interpreter` (`compiler/rustc_const_eval/src/interpret/eval_context.rs`) over `tcx.mir_for_ctfe(def_id)` using `CompileTimeMachine`, which forbids unwinding, enforces CTFE provenance/mutability restrictions, and dispatches `const_eval_select` (`compiler/rustc_const_eval/src/interpret/intrinsics.rs`) to its compile-time target rather than its runtime implementation.
2. **Pre-Monomorphization `--emit=mir` Blindness and Charon `--monomorphize` Bypass:** Standard `rustc --emit=mir` runs inside `tcx.analysis(())` (`compiler/rustc_interface/src/passes.rs`, line 798) over polymorphic `tcx.hir_body_owners()` **before** `tcx.collect_and_partition_mono_items(())` executes (`passes.rs`, line 1197). Empirically across both `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`), `--emit=mir` writes a `2,469`-byte `.mir` file whose first `79` lines are **byte-for-byte identical** across passing (`a1`, `b0`, `unused_b1`) and failing (`b1`, where `RequireNonZero::<0>::VALID` triggers `E0080`) crates, because `--emit=mir` prints polymorphic `ConstKind::Unevaluated` projections before `collect_and_partition_mono_items` evaluates them. Furthermore, Charon `0.1.210` (`--monomorphize`) hooks `after_expansion`, calls `tcx.analysis(())`, performs user-space AST type substitution (`monomorphize.rs`), and invokes `tcx.dcx().abort_if_errors()` without ever calling `collect_and_partition_mono_items` or `tcx.eval_to_const_value_raw`, allowing `RequireNonZero::<0>::VALID` to exit `0` with zero diagnostics.
3. **Complete Six-Category Taxonomy of Post-Monomorphization Errors (PMEs) and 16-Case Reachability Boundary:** Across `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`), and `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), PMEs partition into six architectural categories:
   - *Category 1:* Generic inline `const { ... }` blocks (`DefKind::InlineConst` in `mir::Body::required_consts`), where concrete non-generic panics are caught early in `mir_drops_elaborated_and_const_checked` by `KnownPanicsLint` (`lint_const_expr_unconditional_panic`), while type- or const-generic inline consts survive until `collect_items_rec` calls `tcx.ensure_ok().mir_Constant_val(...)`.
   - *Category 2:* Generic associated constants (`Trait::ASSOC`, `Inherent<T>::ASSOC`, and `zerocopy`'s `static_assert!` / `const_assert!` macros in `google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6`), which enter `body.required_consts` only when evaluated as an operand (`let _ = Check::<T>::VALID` or `_ = Check::<T>::VALID` via `visit_operand`), whereas `let _: () = Check::<T>::VALID;` emits only `PlaceMention` and `FakeRead` in `mir_built`, both stripped before monomorphization so `Check::<u64>::VALID` silently compiles unless forced by an operand read!
   - *Category 3:* Dead-branch CTFE and `mentioned_items`, governed by a 16-case boundary: conditional branches (`if false`, `match 0usize`, `false && ...`, `true || ...`, `while false`) retain their dead basic blocks in `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`), so `RequiredConstsVisitor` and `MentionedItems` record their `required_consts` and `mentioned_items`, triggering PMEs during monomorphization; conversely, statements sequentially following unconditional divergence (`return`, `break`, `continue`, `loop {}`, `panic!()`, `-> !`, `enum Void {}`) are disconnected from `bb0` and pruned by `SimplifyCfg::Initial` before `MentionedItems` (`mir_const`) and `RequiredConstsVisitor` (`mir_drops_elaborated_and_const_checked`) ever run.
   - *Category 4:* Post-monomorphization `LayoutError` (`LayoutError::TooGeneric`, `SizeOverflow`, `NormalizationFailure`, `ReferencesError`, `InvalidSimd`), with a critical pointer-indirection boundary: `check_type_layout` (`collector.rs`, lines 1559–1572) traverses `Ty` via `TypeWalker` without dereferencing `TyKind::Ref` or `TyKind::RawPtr`, so `fn take_ref<T>(_: &Big<T>)` does **not** compute the layout of `Big<T>` unless the body projects a field, dereferences the pointer, or drops `Big<T>`.
   - *Category 5:* Monomorphization recursion limits (`collector.rs`, line 623) and trait normalization overflow (`normalize_erasing_regions`), together with `ImpossibleClauses` (`should_codegen_locally`, lines 387–405) and `ImpossiblePredicates` (`instance_mir`), which return `false` or dummy `unreachable` MIR when an item's `tcx.predicates_of(def_id)` fail to hold after substitution.
   - *Category 6:* Codegen-phase target-feature ABI errors (`E0511` in `fn_abi_new_uncached`), SIMD intrinsic width/element checks, validity intrinsics (`assert_inhabited`, `assert_zero_valid`, `assert_mem_uninitialized_valid` evaluated in `mir_shims` and codegen), and post-monomorphization `asm!` register/constant checks.
4. **Four `TyCtxt` Invariants for Sound In-Process `rustc_driver` Capture and Lean `4.34.1` Admission Proofs:** An in-process capture driver (`anneal-rustc-capture`) verified across `rustc 1.98.0-nightly` and `rustc 1.99.1` ([`support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/driver.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/driver.rs)) and mechanized in Lean `4.34.1` ([`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/MirRepresentationAdmission.lean`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/MirRepresentationAdmission.lean), [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/RealCaptureAudit.lean`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/RealCaptureAudit.lean)) must enforce four invariants: (I1) preserve `Runtime(PostCleanup)` bodies before `optimized_mir` steals them while requiring `tcx.collect_and_partition_mono_items(())` + `tcx.dcx().has_errors().is_none()` on binary/C-ABI crates; (I2) for generic library functions not reachable from a concrete `MonoItem` root (`unused_b1`), evaluate every `ConstOperand` in `body.required_consts` and every mentioned `Used` item via `tcx.const_eval_resolve` / `tcx.eval_to_const_value_raw` under each target concrete substitution `GenericArgsRef`; (I3) evaluate `tcx.layout_of(typing_env.as_query_input(ty))` for every concrete parameter, return, pointee, and local type; and (I4) reject `tcx.impossible_predicates(def_id, args)` (`true`) and validate target-feature ABI and validity intrinsics (`layout.abi.is_uninhabited()`, `is_zero_valid`, `is_uninit_valid`).
5. **Toolchain Pin Coupling Across `google/zerocopy`, Aeneas, Charon, and `rustc`:** In `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`tools/anneal/flake.nix`), the Rust nightly (`nightly`) is not an independent choice: it is derived at Nix evaluation time from `charon-pin/charon/rust-toolchain` inside the pinned Aeneas archive (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` $\to$ `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`), while `CHARON_TOOLCHAIN_IS_IN_PATH=1` instructs Charon to invoke bare `cargo` from `PATH` without verifying the toolchain version, and Anneal's Exocrate cache key hashes `Cargo.toml`/`Cargo.lock` rather than `flake.nix`.

---

## Applicability

This report applies to the following pinned compilers, language references, and verification repositories recorded in `REPORT.json`:

| Component / Subject | Version / Toolchain Date | Commit / Revision | Scope & Role in Report |
| :--- | :--- | :--- | :--- |
| **`rust-lang/rust` (`nightly` source pin)** | `nightly` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Source audit of `CompileTimeMachine`, `eval_in_interpreter`, `mir_for_ctfe`, and `const_eval_select`. |
| **`rust-lang/rust` (`nightly` binary)** | `1.98.0-nightly` (`2026-05-30`) | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | Empirical execution of `--emit=mir`, `collect_and_partition_mono_items`, all 5 PME probe suites, and `pme_capture_probe` (`x86_64-unknown-linux-gnu`, LLVM `22.1.6`). |
| **`rust-lang/rust` (`1.99.0` stable)** | `1.99.0` (`2026-07-30`) | `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` | Multi-version comparison for `const_probe.rs` and `probe.rs` (`x86_64-unknown-linux-gnu`, LLVM `22.1.1`). |
| **`rust-lang/rust` (`1.99.1` stable)** | `1.99.1` | `58cf8f9c35b355199727627d07ae34a4e2846d67` | Source audit and multi-version execution of the 6-category PME taxonomy and `rustc_driver` capture harness. |
| **`rust-lang/reference`** | Normative Reference | `ad35aca481751a06afeb23820a672b0f3b11a476`, `82da570bafd9efed421bdbae0f8603ede8dd308b` | Normative rules for `const` contexts, `const fn`, and inline `const` block evaluation. |
| **`google/zerocopy`** | Workspace & `tools/anneal` | `41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `8fb35253fbc703cb2cd0997f4efcda76cf9062b6` | `tools/anneal/flake.nix` toolchain coupling and `src/macros.rs` (`static_assert!`, `const_assert!`). |
| **`AeneasVerif/aeneas` & `AeneasVerif/charon`** | `nightly-2026.06.03` / `0.1.210` | `ac9f1bc5262a5e4ff1e24ca78617121382202727`, `a535e914f74db4fd9e6be7048f4233270d8945c0` / `1e08453924610c19d74c245a7308f17c1008e2db` | Toolchain pin coupling (`charon-pin`, `CHARON_TOOLCHAIN_IS_IN_PATH=1`) and Charon `--monomorphize` behavior. |
| **`leanprover/lean4` & `joshlf/anneal`** | `4.34.1` / `main` | `5045d0056413266e57c625dcd7c365b10e377c52`, `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b` | Mechanized non-circular MIR admission and post-monomorphization completion-oracle proofs. |

---

## Findings

### 1. Normative `const fn` Semantics vs. `rustc`'s `CompileTimeMachine` Interpreter

`Basis: normative, source`

At `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` (`src/const_eval.md` and `src/items/functions.md`) and `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:
1. **Mandatory Const Contexts vs. Runtime Execution of `const fn`:**
   - Const contexts (array types `[T; N]`, repeat expressions `[expr; N]`, `const` and `static` initializers, enum discriminants, const generic arguments, and inline `const { ... }` blocks) **must** be evaluated at compile time, and any evaluation failure (arithmetic overflow, division by zero, out-of-bounds index, panic) is a mandatory compile-time error (`E0080`).
   - Declaring a function `const fn` makes it callable from a const context; when called outside a const context, it executes at runtime with ordinary runtime semantics.
   - Compile-time evaluation executes in the **target** environment (for example, `usize` width and endianness follow `--target`, not the build host).
2. **`rustc`'s CTFE Interpreter (`CompileTimeMachine` and `mir_for_ctfe`):**
   - `compiler/rustc_const_eval/src/const_eval/eval_queries.rs` (`eval_in_interpreter`) loads the body via `tcx.mir_for_ctfe(def_id)` and steps `InterpCx<CompileTimeMachine>` (`compiler/rustc_const_eval/src/const_eval/machine.rs`).
   - `CompileTimeMachine` rejects calls to non-`const` functions, enforces CTFE memory/provenance rules (forbidding mutation of non-local static allocations or reading raw pointer provenance as integers), converts `Assert` and panic terminators into `ConstEvalErr` diagnostics, and panics on `UnwindAction::Continue` (`"unwinding cannot happen in const-eval"`).
   - In `compiler/rustc_const_eval/src/interpret/intrinsics.rs`, `const_eval_select` explicitly branches to its `called_in_const` function argument during CTFE while lowering to `called_at_rt` during runtime MIR transformations (`remap_mir_for_const_eval_select`). A verification tool therefore cannot equate a `const fn`'s CTFE behavior with its runtime behavior without accounting for `const_eval_select` and CTFE-specific machine checks.

---

### 2. Toolchain Pin Coupling Across `google/zerocopy`, Aeneas, Charon, and `rustc`

`Basis: source`

Inspection of `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`tools/anneal/`), `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`charon-pin`), and `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`rust-toolchain`, `charon/src/bin/charon/cli.rs`) (mapped in [`support/rust-nightly-upgrade-checklist/source-map.json`](support/rust-nightly-upgrade-checklist/source-map.json) and [`support/rust-nightly-upgrade-checklist/upgrade-checklist.json`](support/rust-nightly-upgrade-checklist/upgrade-checklist.json)) establishes five coupling invariants:

1. **Transitive Nightly Derivation (`tools/anneal/flake.nix`, lines 18–57):** Anneal's `flake.nix` pins an Aeneas release tarball (`nightly-2026.06.03`), reads `charon-pin` from that Aeneas source tree to fetch the exact Charon commit (`a535e914f74db4fd9e6be7048f4233270d8945c0`), and parses `charon/rust-toolchain` (`channel = "nightly"`) via `fromTOML` to select the Rust nightly from `rust-overlay`.
2. **Untrusted `PATH` Bypass (`CHARON_TOOLCHAIN_IS_IN_PATH=1`):** Both `tools/anneal/flake.nix` (line 112) and `tools/anneal/src/Cargo.rs` (lines 715–720) set `CHARON_TOOLCHAIN_IS_IN_PATH=1`. In `charon/src/bin/charon/cli.rs` (lines 222–264), that environment variable causes the `charon` wrapper to skip `rustup` toolchain resolution and invoke whichever `cargo` binary is first on `PATH` **without checking that `rustc -Vv` matches `charon-driver`'s compiled host `rustc_driver` dylib**.
3. **Platform-Specific Fixed-Output Hashes (`tools/anneal/flake.nix`, lines 6–15 and 95–107):** Both the Aeneas binary release hashes (`aeneasHashes` for `x86_64-linux`, `aarch64-linux`, `x86_64-darwin`, `aarch64-darwin`) and the `charon-driver` `cargoDeps` vendor hash (`outputHash`) must be updated atomically across all supported platforms whenever the Aeneas or Charon pin changes.
4. **Exocrate Cache Key Blindness (`tools/anneal/src/cache.rs`, lines 23–40):** Anneal's Exocrate `.llbc` / Lean extraction cache hashes `Cargo.toml`, `Cargo.lock`, source files, and Anneal CLI flags, but does **not** include `tools/anneal/flake.nix`, the Charon revision, or the `rustc` version in its cache key. Upgrading the toolchain without clearing `.anneal-cache` or bumping the cache version serves stale `.llbc` artifacts.

---

### 3. Pre-Monomorphization `--emit=mir` vs. Post-Monomorphization CTFE (`1.98.0-nightly` and `1.99.0`)

`Basis: source, execution, derived`

In `compiler/rustc_interface/src/passes.rs` (lines 790–805 and 1190–1205 at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `start_codegen` runs **after** `tcx.analysis(())` completes:
- `tcx.analysis(())` invokes `emit_oz_mir` $\to$ `dump_mir_for_phase_change` (`compiler/rustc_middle/src/mir/pretty.rs`, lines 192–245), which iterates `tcx.hir_body_owners()` and writes `<crate>.mir` BEFORE `start_codegen` calls `tcx.collect_and_partition_mono_items(())`.
- Consequently, for a generic function referencing an associated constant `RequireNonZero::<N>::VALID`:
  ```rust
  pub struct RequireNonZero<const N: usize>;
  impl<const N: usize> RequireNonZero<N> {
      pub const VALID: usize = 1 / N;
  }
  pub fn guarded_add<const N: usize>(x: u32) -> u32 {
      let _ = RequireNonZero::<N>::VALID;
      x + 1
  }
  ```
  the polymorphic `optimized_mir` of `guarded_add` contains `_2 = const RequireNonZero::<N>::VALID` (`Const::Ty(ConstKind::Unevaluated)`), which is not evaluated until `collect_items_rec` (`compiler/rustc_monomorphize/src/collector.rs`, lines 1072–1128) substitutes a concrete `N` for a reachable `MonoItem::Fn` and calls `tcx.ensure_ok().mir_const_qualif` / `eval_to_const_value_raw`.

Executing [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/const_probe.rs`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/const_probe.rs) across both `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`) (receipts in [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/r13-compiler-revalidation.json`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/r13-compiler-revalidation.json)) demonstrates four critical facts:

| `--cfg` Variant on `const_probe.rs` | `rustc --emit=mir,Metadata` Exit | `rustc --emit=mir,link` (or `obj`) Exit | `charon-driver --monomorphize` Exit | Emitted `.mir` File Comparison (`1.98.0-nightly` & `1.99.0`) |
| :--- | :---: | :---: | :---: | :--- |
| **`--cfg variant="a1"`** (`entry` calls `guarded_add::<1>`) | `0` (no CTFE of `VALID`) | `0` (`1 / 1 = 1` succeeds) | `0` | `2,469` bytes (`86` lines); lines `1..=79` **byte-identical** across all 4 variants! |
| **`--cfg variant="b0"`** (`entry` does not call `guarded_add`) | `0` | `0` | `0` | `2,469` bytes (`86` lines); lines `1..=79` **byte-identical** across all 4 variants! |
| **`--cfg variant="b1"`** (`entry` calls `guarded_add::<0>`) | **`0` (silent false positive!)** | **`1` (`E0080`: division by zero in `RequireNonZero::<0>::VALID`)** | **`0` (silent false positive!)** | **Still writes the `2,469`-byte `.mir` file to disk before failing `E0080`!** |
| **`--cfg variant="unused_b1"`** (private dead `dead_caller` calls `guarded_add::<0>`) | `0` | **`0` (because `dead_caller` is not reachable from a root `MonoItem`)** | `0` | `2,718` bytes; `dead_caller` appears in `.mir` (`hir_body_owners`) but is never monomorphized! |

In Lean `4.34.1` ([`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/MirRepresentationAdmission.lean`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/MirRepresentationAdmission.lean), [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/RealCaptureAudit.lean`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/RealCaptureAudit.lean), receipts in [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/r13-lean-revalidation.json`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/r13-lean-revalidation.json)), `prefix79_collision_across_all_four_variants` and `admitCapturedUnit_rejects_b1_even_with_valid_mir_prefix` prove that any admission gate inspecting only `--emit=mir`, `--emit=metadata`, or Charon `--monomorphize` is unsound on `b1` and `unused_b1`; soundness requires an `IndependentCompletionOracle` that enforces post-monomorphization CTFE completion and cross-crate `(crate_name, CrateSvh, DefPathHash)` + `is_mir_available` binding.

---

### 4. Six-Category Taxonomy of Post-Monomorphization Errors (PMEs) and the 16-Case Reachability Matrix (`1.98.0-nightly` and `1.99.1`)

`Basis: source, execution`

Auditing `rustc_mir_build`, `rustc_mir_transform`, `rustc_monomorphize`, `rustc_const_eval`, `rustc_ty_utils`, and `rustc_codegen_ssa` at `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`) and executing the five probe files under [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/) across `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) establishes the complete six-category PME taxonomy:

| PME Category | Compiler Mechanism & Source Location (`1.99.1` `58cf8f9c3`) | Empirical Behavior on `1.98.0-nightly` & `1.99.1` (`support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/`) |
| :--- | :--- | :--- |
| **1. Generic Inline `const { ... }` Blocks** (`p1_inline_const.rs`) | THIR lowers `const { ... }` to `ConstBlock { did: DefId(DefKind::InlineConst), args }` (`builder/expr/as_constant.rs`, lines 189–215). During `mir_drops_elaborated_and_const_checked`, `RequiredConstsVisitor` (`required_consts.rs`, lines 15–51) populates `body.required_consts`, and `KnownPanicsLint` (`known_panics_lint.rs`, lines 135–160) evaluates `ConstOperand`s only when `!v.has_non_region_param()`. Concrete `const { panic!() }` fails in `analysis`, whereas generic `const { assert!(size_of::<T>() <= 4) }` or `const { 1 / N }` is skipped by `KnownPanicsLint` and fails with `E0080` only in `collect_items_rec` (`collector.rs`, lines 1277–1294). | Both `1.98.0-nightly` and `1.99.1` pass `--emit=metadata` on uninstantiated `generic_inline_const_assert<u64>()` and `generic_inline_const_div<0>()`, and emit `E0080` when instantiated by a reachable `MonoItem`. |
| **2. Associated Constants & `zerocopy`'s `static_assert!`** (`p2_assoc_const_zerocopy.rs`) | Named associated constants (`<T as Trait>::ASSOC`, `Struct::<T>::ASSOC`) lower to `ConstKind::Unevaluated(UnevaluatedConst { def, args })`. **Subtle operand vs. place distinction:** `let _ = AssertLe4::<T>::VALID;` (or `zerocopy`'s `const_assert!` in `google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6` `src/macros.rs`, lines 505–576, which binds `const _0: bool = ...; let _ = StaticAssert::<...>::_0;`) lowers via `as_operand` to `_1 = const AssertLe4::<T>::VALID`, which `RequiredConstsVisitor::visit_constant` records in `body.required_consts`. By contrast, `let _: () = AssertLe4::<T>::VALID;` with an explicit type annotation lowers via `as_place` to `PlaceMention(const AssertLe4::<T>::VALID)` + `FakeRead` in `mir_built`; `CleanupPostBorrowck` and `RemovePlaceMention` strip both before `RequiredConstsVisitor` runs, so `body.required_consts` is **empty** and `typed_let_underscore_skips_required_consts::<u64>()` silently compiles without ever evaluating `AssertLe4::<u64>::VALID`! | Identical across `1.98.0-nightly` and `1.99.1`: `untyped_let_underscore::<u64>()` and `_ = AssertLe4::<u64>::VALID;` trigger `E0080`, whereas `let _: () = AssertLe4::<u64>::VALID;` silently succeeds at `--emit=obj`! |
| **3. Dead-Branch CTFE & `mentioned_items`** (`p3_dead_branch_ctfe.rs`, `branch_vs_diverge_probe.rs`) | `MentionedItems` (`mentioned_items.rs`, lines 26–105, run in `mir_const`) and `RequiredConstsVisitor` (run at the end of `mir_drops_elaborated_and_const_checked`) both traverse the basic blocks present in `mir::Body` at their respective phases. In `collect_items_rec` (`collector.rs`, lines 1277–1335), `rustc` evaluates every `body.required_consts()` entry unconditionally **before** running `optimized_mir` (`ConstProp`/`GVN`). | Tested across all 16 control-flow shapes in [`branch_vs_diverge_probe.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/branch_vs_diverge_probe.rs): all 8 conditional forms (`if false`, `match 0`, `if let`, `false &&`, `true \|\|`, `while false`, runtime branch, call argument) retain their dead basic blocks in `Runtime(PostCleanup)` and trigger `E0080` at `--Zmir-opt-level=0` and `2`, whereas all 8 unconditional-divergence forms (`return`, `loop {}`, `while true`, `break`, `continue`, `panic!()`, `-> !`, `enum Void {}`) are pruned by `SimplifyCfg::Initial` before `MentionedItems` and `RequiredConstsVisitor` run, so their trailing `const` expressions never enter `required_consts` and never fail! |
| **4. Post-Monomorphization `LayoutError` & Pointer Indirection** (`p4_layout_and_mono_limits.rs`) | `collect_items_rec` calls `check_type_layout` (`collector.rs`, lines 1559–1572) on the instantiated signature and `MirUsedCollector::visit_ty` on local types in `optimized_mir`. Crucially, `check_type_layout` walks `ty.walk()` and stops at `TyKind::Ref` and `TyKind::RawPtr` without dereferencing pointee types (`if matches!(ty.kind(), ty::Ref(..) \| ty::RawPtr(..)) { return ControlFlow::Skip; }`). | `fn pass_ref_to_oversized<T>(r: &HugeArray<T>) -> *const HugeArray<T> { r as *const _ }` compiles cleanly (`exit 0`) even when `HugeArray<T>` overflows maximum object size (`[T; usize::MAX]`), whereas reading a field, dereferencing `*r`, or taking `HugeArray<T>` by value fails with `E0080` (`values of the type '[u16; usize::MAX]' are too big for the target architecture`). |
| **5. Recursion/Normalization Limits & `ImpossiblePredicates`** (`p4_layout_and_mono_limits.rs`) | Polymorphic recursion (`recurse::<(T, T)>(depth - 1)`) passes `analysis` and hits `reached the recursion limit while instantiating` in `collector.rs` (line 623). Furthermore, `should_codegen_locally` (`collector.rs`, lines 387–405) and `tcx.instance_mir` (`compiler/rustc_middle/src/ty/context.rs`, `impossible_predicates`) check whether an item's `predicates_of(def_id)` are satisfiable after substitution; if a method has a trivial impossible bound (`where u32: CopyTypeEq<u64>`) called from an unreachable branch, `should_codegen_locally` returns `false` and `instance_mir` substitutes a dummy body consisting of `TerminatorKind::Unreachable`. | Verified identically across `1.98.0-nightly` and `1.99.1`. |
| **6. Codegen ABI (`E0511`), SIMD, Validity Intrinsics, & `asm!`** (`p5_codegen_abi_intrinsics_asm.rs`) | Passing a vector type requiring an enabled target feature (`#[repr(simd)] struct SimdU64x4([u64; 4])` passed by value to an `extern "C"` or non-`#[target_feature(enable = "avx")]` function) passes `analysis` and triggers `E0511` during `fn_abi_new_uncached`. Similarly, `core::intrinsics::assert_inhabited::<T>()`, `assert_zero_valid::<T>()`, and `assert_mem_uninitialized_valid::<T>()` (`mem::zeroed::<NonNull<u8>>()`, `mem::uninitialized::<&u8>()`) are evaluated during `mir_shims` / `codegen` when monomorphized. | Verified identically across `1.98.0-nightly` and `1.99.1`. |

---

### 5. Four Invariants for Sound In-Process `rustc_driver` MIR Capture (`pme_capture_probe`)

`Basis: source, execution, derived`

In [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/), the in-process `rustc_driver` prototype [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/driver.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/driver.rs) was executed against [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/src/lib.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/src/lib.rs) (output in [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/driver_output.txt`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/driver_output.txt), compared against `--emit=mir` in [`emitted_opt0.mir`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/emitted_opt0.mir) and [`emitted_opt1.mir`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/emitted_opt1.mir)). A sound Stage 1 `anneal-rustc-capture` driver must enforce four `TyCtxt` invariants:

1. **Invariant 1 (Pre-Steal `Runtime(PostCleanup)` Capture + Reachable Monomorphization Gate):**
   - Intercept `tcx.mir_drops_elaborated_and_const_checked(def_id)` via `override_queries` + active `after_analysis` demand before `tcx.optimized_mir` steals the `Runtime(PostCleanup)` body.
   - Force `tcx.collect_and_partition_mono_items(())` and check `tcx.dcx().has_errors().is_none()` to discharge all reachable `MonoItem` PMEs.
2. **Invariant 2 (Explicit Substituted Evaluation of `body.required_consts` and `mentioned_items` for Generic Library Roots):**
   - Because `Runtime(PostCleanup)` basic blocks match the exact CFG seen by `RequiredConstsVisitor` (`mir_drops_elaborated_and_const_checked`) and `MentionedItems` (`mir_const`), for every concrete instantiation `(def_id, args)` verified by Anneal (even if the function is an uninstantiated generic library item in an `.rlib` crate), instantiate each `ConstOperand` in `body.required_consts()` with `EarlyBinder::bind(c.const_).instantiate(tcx, args)` and evaluate it via `tcx.const_eval_resolve(typing_env, unevaluated, span)` (and recursively check `tcx.mentioned_items(def_id)`).
3. **Invariant 3 (Complete Concrete Type and Pointee Layout Validation):**
   - For every concrete instantiation `(def_id, args)`, query `tcx.layout_of(typing_env.as_query_input(ty))` for all signature types, local variable types in `body.local_decls`, and— whenever the body projects through or dereferences a pointer/reference—the pointee type `ty.builtin_deref(true)`.
4. **Invariant 4 (`impossible_predicates`, Target-Feature `FnAbi`, and Validity Intrinsics):**
   - Verify `!tcx.impossible_predicates(def_id, args)` so functions with unsatisfiable `where` bounds cannot be replaced by `TerminatorKind::Unreachable` stubs, query `tcx.fn_abi_of_instance(typing_env.as_query_input((instance, ty::List::empty())))` to catch `E0511` target-feature ABI errors, and check `assert_inhabited` / `assert_zero_valid` / `assert_mem_uninitialized_valid` against `layout.abi.is_uninhabited()` and validity masks.

---

## Boundaries

1. **Typed `let _: T = ASSOC_CONST;` Associated Constant Caveat:** Because `let _: () = Check::<T>::VALID;` with an explicit type annotation lowers through `as_place` (`PlaceMention` + `FakeRead`) rather than `as_operand`, `rustc` strips the reference before `RequiredConstsVisitor` runs and does **not** evaluate `Check::<T>::VALID` at monomorphization time. Compile-time assertion macros (such as `zerocopy`'s `static_assert!` and `const_assert!`) must therefore always use untyped `let _ = ...;`, `_ = ...;`, or an inline `const { ... }` block.
2. **Generic Library Functions Outside `collect_and_partition_mono_items`:** Running `tcx.collect_and_partition_mono_items(())` only checks monomorphizations reachable from exported non-generic roots of the crate. Generic library functions require per-instantiation checking of `required_consts`, `layout_of`, `fn_abi_of_instance`, and `!impossible_predicates` under each concrete substitution `GenericArgsRef` for which a proof is claimed.
3. **Source-Only vs. Executed Coverage:** The normative `const fn` / `CompileTimeMachine` and `flake.nix` upgrade checklist analyses are source- and documentation-grounded at `nightly`, while the `--emit=mir` blindness, 6-category PME taxonomy, 16-case conditional vs. diverging control-flow matrix, in-process `rustc_driver` capture harness, and Lean `4.34.1` admission proofs are execution-verified across `1.98.0-nightly`, `1.99.0`, and `1.99.1`.

---

## Evidence

All supporting Rust probes, Lean `4.34.1` proof modules, and JSON receipts are preserved under `support/`:

- **Toolchain Coupling & Upgrade Checklist (`support/rust-nightly-upgrade-checklist/`):**
  - [`support/rust-nightly-upgrade-checklist/source-map.json`](support/rust-nightly-upgrade-checklist/source-map.json), [`support/rust-nightly-upgrade-checklist/upgrade-checklist.json`](support/rust-nightly-upgrade-checklist/upgrade-checklist.json).
- **Configured Const Admission, `--emit=mir` Prefix Collision, and Lean `4.34.1` Proofs (`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/`):**
  - Rust probes and compiler receipt: [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/const_probe.rs`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/const_probe.rs), [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/probe.rs`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/probe.rs), [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/r13-compiler-revalidation.json`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/r13-compiler-revalidation.json).
  - Lean `4.34.1` modules and receipt: [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/MirRepresentationAdmission.lean`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/MirRepresentationAdmission.lean), [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/MirRepresentationControls.lean`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/MirRepresentationControls.lean), [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/RealCaptureAudit.lean`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/RealCaptureAudit.lean), [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/RealCaptureControls.lean`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/RealCaptureControls.lean), [`support/rustc-configured-const-admission-and-post-monomorphization-ctfe/r13-lean-revalidation.json`](support/rustc-configured-const-admission-and-post-monomorphization-ctfe/r13-lean-revalidation.json).
- **Six-Category PME Probes, 16-Case Divergence Matrix, and In-Process `rustc_driver` Capture Harness (`support/rustc-post-monomorphization-errors-and-mir-capture-2026/`):**
  - PME probe suites: [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/p1_inline_const.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/p1_inline_const.rs), [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/p2_assoc_const_zerocopy.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/p2_assoc_const_zerocopy.rs), [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/p3_dead_branch_ctfe.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/p3_dead_branch_ctfe.rs), [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/p4_layout_and_mono_limits.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/p4_layout_and_mono_limits.rs), [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/p5_codegen_abi_intrinsics_asm.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/p5_codegen_abi_intrinsics_asm.rs), [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/branch_vs_diverge_probe.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/branch_vs_diverge_probe.rs).
  - In-process `rustc_driver` capture harness and captured outputs: [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/driver.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/driver.rs), [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/src/lib.rs`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/src/lib.rs), [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/driver_output.txt`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/driver_output.txt), [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/emitted_opt0.mir`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/emitted_opt0.mir), [`support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/emitted_opt1.mir`](support/rustc-post-monomorphization-errors-and-mir-capture-2026/pme_capture_probe/emitted_opt1.mir).

---

## Revalidation

Run the following self-contained commands from this package directory to reproduce the `--emit=mir` vs. post-monomorphization CTFE checks, the 6-category PME probe suite, and the Lean `4.34.1` admission proofs:

```bash
# 1. Reproduce the 4-variant `--emit=mir,metadata` vs. `--emit=mir,link` comparison on const_probe.rs
mkdir -p build/const-probe
for v in a1 b0 b1 unused_b1; do
  rustc --edition 2021 --crate-type lib --cfg "variant=\"$v\"" \
    --emit=mir,metadata -o "build/const-probe/${v}.mir" \
    support/rustc-configured-const-admission-and-post-monomorphization-ctfe/const_probe.rs
done
head -n 79 build/const-probe/a1.mir > build/const-probe/a1.prefix79
head -n 79 build/const-probe/b1.mir > build/const-probe/b1.prefix79
cmp -s build/const-probe/a1.prefix79 build/const-probe/b1.prefix79

# Verify that `--emit=link` fails with E0080 on b1 while succeeding on a1, b0, and unused_b1
! rustc --edition 2021 --crate-type bin --cfg 'variant="b1"' \
  -o build/const-probe/b1.bin \
  support/rustc-configured-const-admission-and-post-monomorphization-ctfe/const_probe.rs

# 2. Reproduce the PME probe suites (Categories 1-6 and the 16-case divergence matrix)
rustc --edition 2021 --crate-type lib \
  --emit=metadata -o build/const-probe/branch_vs_diverge.rmeta \
  support/rustc-post-monomorphization-errors-and-mir-capture-2026/probes/branch_vs_diverge_probe.rs

# 3. Re-check the Lean 4.34.1 admission and completion-oracle proof modules
for f in \
  MirRepresentationAdmission.lean \
  MirRepresentationControls.lean \
  RealCaptureAudit.lean \
  RealCaptureControls.lean; do
  lean support/rustc-configured-const-admission-and-post-monomorphization-ctfe/"$f"
done
```
