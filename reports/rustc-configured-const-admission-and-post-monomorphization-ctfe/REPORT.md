# Rustc Configured Target Admission, Polymorphic MIR Emission Before Post-Monomorphization CTFE Failure, and Reachable Monomorphic Const Prerequisites

## Summary

In `rustc` (`1.98.0-nightly f8a08b688` and `1.99.0 b940084d7`), conditional compilation (`#[cfg]`, `#[cfg_attr]`), polymorphic MIR construction and emission (`--emit=mir`), and post-monomorphization compile-time function evaluation (CTFE) execute in distinct compiler phases with asymmetric failure boundaries:

1. **Polymorphic MIR emission precedes post-monomorphization CTFE failure (`E0080`):** When a generic function `checked<T: Bound, const N: usize>()` contains an inline `const { assert!(N <= <T as Bound>::LIMIT); }` block or references a generic associated constant `RequireNonZero::<N>::VALID`, `rustc --emit=mir,llvm-ir` writes the crate's `.mir` file during `after_analysis` *before* running `tcx.collect_and_partition_mono_items(())`. On a failing concrete instantiation (`probe_case="b1"`, calling `checked::<B, 1>()` where `<B as Bound>::LIMIT == 0`), `rustc` exits with code `1` (`error[E0080]`) and emits no `.ll` file, yet leaves an 84-line `probe.mir` on disk whose polymorphic `fn checked` and `checked::{constant#0}` prefix (lines 1–70, SHA-256 `155f0a457e2d9479d6dbe40f41b28cb964b8ec7465246f7476e321f58e61b63b`) is byte-for-byte identical across passing (`a1`, `b0`, `unused_b1`) and failing (`b1`) configurations.
2. **Reachable monomorphic collection (`collect_and_partition_mono_items`) vs. local HIR owner enumeration (`hir_body_owners`):** When a crate defines an uninstantiated generic wrapper `pub fn never_instantiated<U: Bound>() -> usize { checked::<U, 1>() }` (`probe_case="unused_b1"`), `tcx.hir_body_owners()` retains `never_instantiated` (`8` local owners), whereas `tcx.collect_and_partition_mono_items(())` collects only the `4` reachable monomorphic items (`entry`, `checked::<B, 0_usize>`, `<B as Bound>::marker`, `<A as Bound>::marker`), succeeds with exit code `0`, and emits LLVM IR identical to `b0` (SHA-256 `da17913196feb3c9d9f2450c5477197c3b0c79df7f7e53527ae65802e41bf9fa`).
3. **Charon `0.1.210` `--monomorphize` bypasses post-monomorphization associated-const CTFE:** Because Charon stops `rustc` inside `after_analysis` (`Compilation::Stop`) and implements `--monomorphize` as a user-space AST cloning and substitution pass (`charon-lib/src/transform/monomorphize.rs`), invoking `charon rustc --ullbc --monomorphize` on `const_probe.rs` (`RequireNonZero::<0>::VALID = 1 / 0`) exits with code `0` (`has_errors: false`) and emits a `.ullbc` file containing an unevaluated `1usize ub./ 0usize` body, whereas `tcx.collect_and_partition_mono_items(())` fails closed with `error[E0080]: attempt to divide 1_usize by zero`.
4. **Non-circular admission and cross-crate identity:** Sound MIR-based verification separates (a) syntactic/structural well-formedness (`StructurallyWellFormed`, admitting UB-bearing bodies so operational safety theorems are non-vacuous), (b) conditional library theorems over polymorphic MIR (`generic_checked_theorem_holds_under_const_premise`), (c) concrete entry admission gated on an independent post-monomorphization completion oracle (`IndependentCompletionOracle`) and reachable monomorphic `required_consts`, and (d) cross-crate dependency binding by crate Strict Version Hash (`tcx.crate_hash(cnum)`) rather than `DefPathHash` alone.

## Applicability

These findings apply to:

- **`rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-30`, LLVM `22.1.6`)** and **`rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `2026-07-30`, LLVM `22.1.1`)** on `x86_64-unknown-linux-gnu`, specifically the query providers and passes in `compiler/rustc_mir_transform/src/lib.rs`, `compiler/rustc_monomorphize/src/collector.rs`, and `compiler/rustc_interface/src/passes.rs`.
- **The Rust Reference** (`https://github.com/rust-lang/reference`, commit `82da570bafd9efed421bdbae0f8603ede8dd308b`), specifically `src/conditional-compilation.md`, `src/expressions/block-expr.md`, and `src/const-eval.md`.
- **Charon `0.1.210`** (`commit 1e08453924610c19d74c245a7308f17c1008e2db`, pinned to `nightly-2026-05-31` / `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), specifically `charon/src/bin/charon-driver/translate/translate_ctx.rs` and `charon/src/transform/monomorphize.rs`.
- **Lean `4.34.1`** (`commit 5045d0056413266e57c625dcd7c365b10e377c52`), used to mechanize the non-circular admission predicates, completion oracle, cross-crate SVH binding, and negative controls in `support/*.lean`.

## Findings

### 1. Conditional Compilation vs. Post-Monomorphization Const Evaluation in the Rust Reference and `rustc`

**Basis:** `normative`, `source`

- **Conditional compilation (`#[cfg]`, `#[cfg_attr]`):** In the Rust Reference (`src/conditional-compilation.md` at `82da570bafd9efed421bdbae0f8603ede8dd308b`), conditional compilation is defined relative to the active configuration predicate set of a single compilation invocation. Unconfigured items and attributes are stripped prior to name resolution, type checking, MIR construction, and monomorphization; there is no single "all-configurations" HIR or MIR artifact for a crate.
- **Session-dependent MIR lowering and pass gating:** In `rustc` (`compiler/rustc_mir_transform/src/lib.rs`), the MIR pass pipeline (`should_run_pass` and `run_Optimization_passes`) and intrinsic lowering depend directly on session parameters including target layout (`tcx.data_layout()`), `-Z mir-opt-level` (`tcx.sess.mir_opt_level()`), `-Z mir-enable-passes`, `tcx.sess.opts.debug_assertions`, `tcx.sess.overflow_checks()`, and `tcx.sess.ub_checks()`. Consequently, every extracted MIR body is semantically indexed by a concrete compilation configuration (`BuildConfig`: crate identity, active `cfg` set, feature flags, target layout, and relevant compiler flags).
- **Generic `const` blocks and associated constants (`required_consts`):** Under the Rust Reference (`src/expressions/block-expr.md` and `src/const-eval.md`), `const { ... }` blocks and associated constants that depend on generic type or const parameters are not evaluated when the polymorphic function body is type-checked or when polymorphic MIR is emitted. Instead, `rustc` records unevaluated `ConstOperand` entries in `Body::required_consts`. During monomorphization (`compiler/rustc_monomorphize/src/collector.rs`, `collect_items_rec`), `rustc` instantiates each reachable generic item, calls `tcx.ensure_ok().instantiate_and_check_impossible_predicates(instance.def_id(), instance.args)`, and evaluates each entry in `body.required_consts()` via `tcx.const_eval_resolve(ty::TypingEnv::fully_monomorphized(), uv, span)`.

### 2. Polymorphic `--emit=mir` Succeeds Before Post-Monomorphization `E0080` Failure (`probe.rs`)

**Basis:** `source`, `execution`

The probe `support/probe.rs` (SHA-256 `3ada61fe22ea9ee0047c440d76c3a13564f23026fbfdbe37320f0707e083c3fb`) defines:

```rust
pub trait Bound {
    const LIMIT: usize;
    fn marker() -> usize;
}
pub struct A;
pub struct B;
impl Bound for A { const LIMIT: usize = 1; fn marker() -> usize { 10 } }
impl Bound for B { const LIMIT: usize = 0; fn marker() -> usize { 20 } }

pub fn checked<T: Bound, const N: usize>() -> usize {
    const {
        assert!(N <= <T as Bound>::LIMIT);
    };
    <T as Bound>::marker() + N
}
```

Compiling `support/probe.rs` across four `--cfg probe_case="..."` configurations (`a1`, `b0`, `b1`, `unused_b1`) with `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` (`support/r13-compiler-revalidation.json`) establishes the following matrix:

| Configuration | `entry()` target | Extra item | `rustc --emit=mir,llvm-ir` exit | `--driver-stop-after-analysis` exit | `--driver-run-mono-collector` exit | `.mir` emitted (lines) | `.mir` lines 1–70 SHA-256 | `.ll` emitted (SHA-256) |
|---|---|---|---|---|---|---|---|---|
| `a1` | `checked::<A, 1>()` | none | `0` | `0` | `0` | `true` (`84`) | `155f0a45...e61b63b` | `true` (`e68e4f78...dbb7d0b6`) |
| `b0` | `checked::<B, 0>()` | none | `0` | `0` | `0` | `true` (`84`) | `155f0a45...e61b63b` | `true` (`da179131...e41bf9fa`) |
| `b1` | `checked::<B, 1>()` | none | **`1` (`E0080`)** | **`0`** | **`1` (`E0080`)** | **`true` (`84`)** | `155f0a45...e61b63b` | **`false` (`null`)** |
| `unused_b1` | `checked::<B, 0>()` | `never_instantiated<U>() { checked::<U, 1>() }` | `0` | `0` | `0` | `true` (`98`) | `155f0a45...e61b63b` | `true` (`da179131...e41bf9fa`) |

Key observations from `support/r13-compiler-revalidation.json`:

1. **`--emit=mir` on `b1` writes `probe.mir` before failing:** Because `rustc` emits crate-level `.mir` dumps before monomorphization collection, `b1` writes a complete 84-line `probe.mir` (SHA-256 `e35a7dab232b7a2d793f6def42ff3ade6a48eda2a102d6df0fa6ac82e9a59581`) before `collect_and_partition_mono_items` aborts with `error[E0080]: evaluation panicked: assertion failed: N <= <T as Bound>::LIMIT`.
2. **Polymorphic MIR for `checked` is invariant across all four cases:** Lines 1–70 of `probe.mir` (containing `<A as Bound>::LIMIT`, `<A as Bound>::marker`, `<B as Bound>::LIMIT`, `<B as Bound>::marker`, `checked`, and `checked::{constant#0}`) have the exact same SHA-256 (`155f0a457e2d9479d6dbe40f41b28cb964b8ec7465246f7476e321f58e61b63b`) across `a1`, `b0`, `b1`, and `unused_b1`. In `checked`, the inline `const` block appears only as `required_consts: [ConstOperand { span: ..., user_ty: None, const_: Unevaluated(checked::{constant#0}, [T, N]) }]`; `checked`'s basic blocks contain only the call `<T as Bound>::marker()` and checked addition `+ const N`.
3. **Stopping at `after_analysis` masks post-monomorphization failure:** A custom `rustc_driver` callback that stops at `after_analysis` (`--driver-stop-after-analysis`) or writes a provisional artifact before calling `tcx.collect_and_partition_mono_items(())` observes `has_errors_at_after_analysis: false` and exits `0` on `b1`.
4. **Reachable monomorphic collection vs. `hir_body_owners()` on `unused_b1`:** Under `unused_b1`, `tcx.hir_body_owners()` reports `8` owners (`<A as Bound>::LIMIT`, `<A as Bound>::marker`, `<B as Bound>::LIMIT`, `<B as Bound>::marker`, `checked`, `checked::{constant#0}`, `entry`, `never_instantiated`). However, `tcx.collect_and_partition_mono_items(())` collects only the `4` reachable monomorphic items:
   - `Fn(Instance { def: Item(DefId(0:21 ~ probe[f5f6]::entry)), args: [] })`
   - `Fn(Instance { def: Item(DefId(0:16 ~ probe[f5f6]::checked)), args: [B, 0_usize] })`
   - `Fn(Instance { def: Item(DefId(0:15 ~ probe[f5f6]::{impl#1}::marker)), args: [] })`
   - `Fn(Instance { def: Item(DefId(0:12 ~ probe[f5f6]::{impl#0}::marker)), args: [] })`
   Because `never_instantiated<U>` is generic and never instantiated, `checked::<_, 1>` is never monomorphized and `unused_b1` compiles cleanly to the exact same LLVM IR as `b0`.

### 3. Charon `0.1.210` `--monomorphize` Associated-Const CTFE Bypass (`const_probe.rs`)

**Basis:** `source`, `execution`

In `support/const_probe.rs` (SHA-256 `13a15e1e35b658aafd143b9d77aa16a99a863011807ab42be34f6507983f57f9`), a generic function gates execution on an associated constant:

```rust
pub struct RequireNonZero<const N: usize>;
impl<const N: usize> RequireNonZero<N> {
    pub const VALID: usize = 1 / N;
}

pub fn checked_kernel<const N: usize>(x: usize) -> usize {
    let _ = RequireNonZero::<N>::VALID;
    x + N
}

#[cfg(case_fail_reachable)]
pub fn entry_fail(x: usize) -> usize {
    checked_kernel::<0>(x)
}
```

Re-validation on `rustc 1.98.0-nightly (f8a08b688)` and `charon 0.1.210` (`support/r13-compiler-revalidation.json`) demonstrates a divergence between `rustc`'s monomorphization collector and Charon's `--monomorphize` pass:

- **Direct `rustc` / `tcx.collect_and_partition_mono_items(())`:** Exits with code `1` (`mono_collection_completed: false`) and reports `error[E0080]: attempt to divide 1_usize by zero` while evaluating `RequireNonZero::<0>::VALID` during instantiation of `fn checked_kernel::<0>`.
- **`charon rustc --ullbc --monomorphize -- --crate-type=lib --edition=2021 --cfg case_fail_reachable const_probe.rs`:** Exits with code **`0`**, sets `"has_errors": false` in the output `.ullbc` JSON (SHA-256 `a343d809082dc2d7899832385d490a2b50fd956770a4eb7ca85b95c6545ad340`), and emits a monomorphized global body `const const_probe::{const_probe::RequireNonZero<0usize>}::VALID: usize` containing an unevaluated runtime division `assert(move (@3: bool) == true)` followed by `@0 := copy (@1: usize) ub./ copy (@2: usize)` with `@2 := 0: usize`.
- **Root cause in Charon `0.1.210` source:** In `charon/src/bin/charon-driver/translate/translate_ctx.rs`, Charon's `rustc_driver` callback returns `Compilation::Stop` inside `after_analysis` without invoking `tcx.collect_and_partition_mono_items(())`. In `charon/src/transform/monomorphize.rs` (`TransformPass for Monomorphize`), `--monomorphize` clones and substitutes already-translated ULLBC/LLBC AST declarations in user space (`ItemRef::substitute`) rather than asking `rustc`'s CTFE engine (`tcx.const_eval_resolve`) to evaluate monomorphized associated constants.

### 4. Cross-Crate Dependency Binding (`CrateNum` + `SVH` vs. `DefPathHash`) and `.rmeta` vs. `.rlib` MIR Availability

**Basis:** `source`, `execution`, `derived`

- **Insufficiency of `DefPathHash` for cross-crate implementation binding:** In `rustc`, `tcx.def_path_hash(def_id)` computes a deterministic fingerprint from the crate's stable crate ID (crate name and `-C metadata` disambiguator) and the item's `DefPath`. If an external dependency `dep_provider` is recompiled from modified source code (`dep_provider_alt.rs`, changing `ext_add_one(x) { x + 1 }` to `x + 99`) with the same `--crate-name=dep_provider` and flags, `tcx.def_path_hash(callee_def_id)` remains unchanged (`Fingerprint(5455829086666996966, 15111066845238620038)`), whereas `tcx.crate_hash(cnum)` (the crate's Strict Version Hash, `SVH`) changes from `Fingerprint(6291972546840033495, 11104248033824805232)` to `Fingerprint(14250203299809142646, 5459668286407105514)`. Sound cross-crate composition therefore requires binding external callees by `(crate_name, CrateSvh, DefPathHash)` (`crate_svh_binding_distinguishes_substituted_dep`, `def_path_hash_only_dep_binding_control`).
- **Missing cross-crate MIR under `--emit=metadata` (`.rmeta`) or non-inline external functions:** When an upstream crate is compiled with `--emit=metadata` (`cargo check` / `.rmeta` only) or defines a non-generic function without `#[inline]` or `-Z always-encode-mir=yes`, `tcx.is_mir_available(callee_def_id)` returns `false`. Any whole-program or cross-crate operational claim that does not check `is_mir_available` for all reachable external callees is unsound (`rmeta_check_only_missing_dep_body_control`, `non_inline_external_callee_missing_mir_control`).

### 5. Mechanized Non-Circular Admission and Completion Oracle in Lean `4.34.1`

**Basis:** `execution`, `derived`

The Lean `4.34.1` modules in `support/MirRepresentationAdmission.lean`, `support/MirRepresentationControls.lean`, `support/RealCaptureAudit.lean`, and `support/RealCaptureControls.lean` (`support/r13-lean-revalidation.json`, all exiting `0` with only standard `propext` where noted) mechanize four separation principles:

1. **Non-circular structural well-formedness (`StructurallyWellFormed`):** Validates canonical owner identity (`OwnerId`), duplicate-free body tables, entry block existence, and CFG successor closure *without* excluding runtime faults (`Stmt.fault`). Theorem `structural_admission_retains_unsafe_ub_subjects` proves that a UB-bearing program satisfies `StructurallyWellFormed` while violating `Execution.NoUB`, whereas `vacuous_admission_excluding_unsafe_ub_control` shows how embedding fault-freedom into the admission predicate makes operational safety theorems vacuous.
2. **Conditional generic library theorems (`generic_checked_theorem_holds_under_const_premise`):** Proves that the polymorphic body of `checked<T, N>` satisfies `Execution.NoUB` under the explicit hypothesis `evalConstAssert b c = .ok`, matching the division of labor between polymorphic MIR and post-monomorphization CTFE.
3. **Concrete entry admission via reachable monomorphic prerequisites (`IndependentCompletionOracle` and `AdmissibleEntryCapture`):**
   - `concrete_entry_admission_accepts_a1_b0_and_unused_b1` and `concrete_entry_admission_rejects_b1` prove that evaluating `required_consts` over the reachable monomorphic instance closure accepts `a1`, `b0`, and `unused_b1` while rejecting `b1`.
   - `independent_completion_oracle_sound` and `provisional_flag_or_stop_after_analysis_control` prove that gating admission on `mono_collection_completed = true` and `compiler_exit_code = 0` rejects both `stop_after_analysis` runs and post-analysis CTFE failures (`b1`, `case_fail_reachable`).
   - `unused_failing_mention_excluded_by_mono_reachability` and `all_owners_const_prerequisite_overapproximation_control` prove that gating CTFE prerequisites on reachable `MonoItem` instances rather than all `hir_body_owners` avoids false rejection on `unused_b1`.

## Boundaries

- **`known not to apply`:** Polymorphic MIR text emission (`--emit=mir`) or `after_analysis` completion (`Compilation::Stop`, or Charon's `--monomorphize` pass) does **not** imply that a crate's reachable generic `const { ... }` blocks or associated constants (`RequireNonZero::<N>::VALID`) succeed under post-monomorphization CTFE.
- **`known not to apply`:** `DefPathHash` alone does **not** uniquely identify the implementation body of an external crate dependency across source edits that preserve item paths and signatures; crate `SVH` (`tcx.crate_hash(cnum)`) is required.
- **`unsupported`:** Unconfigured `#[cfg(...)]` branches are stripped before HIR/MIR construction; properties of unconfigured target architectures or disabled feature combinations cannot be inferred from a single configured compilation's MIR without running separate configured builds (`cfg_changed_instance_control`, `host_target_pointer_width_confusion_control`).
- **`not examined`:** Interactions between `-Z polymorphize` (experimental codegen deduplication of unused generic parameters) and `collect_and_partition_mono_items` were not examined.
- **`unknown`:** Whether future versions of Charon will invoke `tcx.const_eval_resolve` during `--monomorphize` for associated constants referenced only via discarded bindings (`let _ = Assoc::CONST;`) is unknown.

## Evidence

- **`support/probe.rs`** (SHA-256 `3ada61fe22ea9ee0047c440d76c3a13564f23026fbfdbe37320f0707e083c3fb`): 4-configuration (`a1`, `b0`, `b1`, `unused_b1`) probe demonstrating identical polymorphic MIR emission across passing and failing post-monomorphization `const { assert!(...) }` instantiations and uninstantiated generic wrappers.
- **`support/const_probe.rs`** (SHA-256 `13a15e1e35b658aafd143b9d77aa16a99a863011807ab42be34f6507983f57f9`): Generic associated-constant probe (`RequireNonZero::<N>::VALID = 1 / N`) exposing the divergence between `tcx.collect_and_partition_mono_items(())` (`E0080`) and `charon rustc --ullbc --monomorphize` (`exit_code: 0`, `has_errors: false`).
- **`support/r13-compiler-revalidation.json`**: Fresh execution ledger captured on `2026-10-24` using `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` and `charon 0.1.210`, recording exit codes, `hir_owner_names`, `collected_mono_items`, `.mir` line counts and prefix SHA-256 hashes, `.ll` SHA-256 hashes, and `.ullbc` SHA-256 hashes.
- **`support/MirRepresentationAdmission.lean`** (SHA-256 `1488decb26a2764905384453547c2b50f63f9dacf50340c0657c673f4128f75d`) and **`support/MirRepresentationControls.lean`** (SHA-256 `728c7ee1abfc4bf87f096845ff30ce99eb70c12fbc2b7be5ec9564b8929f76bb`): Lean `4.34.1` mechanization of `StructurallyWellFormed`, `generic_checked_theorem_holds_under_const_premise`, `concrete_entry_admission_accepts_a1_b0_and_unused_b1`, `concrete_entry_admission_rejects_b1`, `two_crate_completeness_transfers_cross_crate_claim`, and six negative controls.
- **`support/RealCaptureAudit.lean`** (SHA-256 `145fbb9eb8a175b13505cf81a8605f8a7af681c9b1e9286050286f352838137e`) and **`support/RealCaptureControls.lean`** (SHA-256 `889db49adc4c4cf4493d5ea758536a8076b7324d98a4b7b83fb7d073101f3637`): Lean `4.34.1` mechanization of `independent_completion_oracle_sound`, `unused_failing_mention_excluded_by_mono_reachability`, `crate_svh_binding_distinguishes_substituted_dep`, `admissible_capture_transfers_entry_safety`, and six negative controls.
- **`support/r13-lean-revalidation.json`**: Fresh Lean `4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`) execution ledger captured on `2026-10-24`, confirming `exit_code: 0` and `#print axioms` output for all theorems.

## Revalidation

To reproduce the compiler, Charon, and Lean `4.34.1` measurements from this package's `support/` directory:

```bash
# 1. Reproduce the 4-configuration probe.rs MIR vs. LLVM-IR emission matrix
for case in a1 b0 b1 unused_b1; do
  rustc +nightly-2026-05-31 --crate-type=lib --edition=2021 \
    --cfg "probe_case=\"${case}\"" support/probe.rs \
    --emit=mir,llvm-ir -o "/tmp/probe_${case}" || true
  head -n 70 "/tmp/probe_${case}.mir" | sha256sum
done

# 2. Reproduce the const_probe.rs rustc E0080 vs. Charon --monomorphize comparison
rustc +nightly-2026-05-31 --crate-type=lib --edition=2021 \
  --cfg case_fail_reachable support/const_probe.rs -o /tmp/libconst_probe.rlib || true

charon rustc --ullbc --monomorphize --dest-file /tmp/const_probe_fail.ullbc \
  -- --crate-type=lib --edition=2021 --cfg case_fail_reachable support/const_probe.rs

# 3. Re-check the Lean 4.34.1 formalization modules
lean -j1 -M768 support/MirRepresentationAdmission.lean
lean -j1 -M768 support/MirRepresentationControls.lean
lean -j1 -M768 support/RealCaptureAudit.lean
lean -j1 -M768 support/RealCaptureControls.lean
```
