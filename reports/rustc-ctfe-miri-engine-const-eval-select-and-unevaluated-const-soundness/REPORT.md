# `rustc` CTFE Miri engine, `const_eval_select`, `is_val_statically_known`, and `Const::Unevaluated` relational soundness

## Summary

`rustc` executes compile-time constant evaluation (`rustc_const_eval`), implicit rvalue promotion (`promote_consts`), MIR global value numbering (`MIR GVN`), and post-monomorphization constant substitution through a shared abstract MIR interpreter (`InterpCx<'tcx, M>`) instantiated with distinct `Machine<'tcx>` implementations (`CompileTimeMachine`, `DummyMachine`, and Miri's `Evaluator`), paired with two compiler intrinsics—`core::intrinsics::const_eval_select` and `core::intrinsics::is_val_statically_known`—whose compile-time and runtime executions intentionally diverge. This report audits the primary implementation at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, LLVM `22.1.6`, plus comparison snapshots `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` and `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), characterizes its behavior across 21 automated live `rustc` and Miri checks plus a 2,472-file sysroot census (`support/probe_ctfe_and_const_eval_select.py`), and provides a standalone Lean `v4.34.1` formalization (`support/CtfeAndConstEvalSelectSoundness.lean`) proving CTFE-to-runtime substitution soundness together with three sharpness counterexamples. Key findings:

1. **Symbolic provenance (`CtfeProvenance`) vs. concrete runtime addresses.** `CompileTimeMachine` packs `(AllocId, immutable, shared_ref)` into `CtfeProvenance` with `Provenance::OFFSET_IS_ADDR = false` and `WILDCARD = None` (`pointer.rs` L91–191). Pointer-to-integer casts fail statically in `check_consts` (`pointers cannot be cast to integers during const eval`) and dynamically in `CompileTimeMachine::expose_provenance` (`const_eval/machine.rs` L862–868); reading pointer bytes through integer-typed memory fails with `ReadPointerAsInt` (`E0080: unable to turn pointer into integer`, `validity.rs` L532). `CompileTimeMachine::ptr_guaranteed_cmp` (`const_eval/machine.rs` L278–387) implements a three-valued decision (`1` equal, `0` unequal, `2` unknown): it decides `GlobalAlloc::Static` pointer pairs (same `AllocId`, or distinct `Static`s with both offsets strictly `< size`), decides misalignment residue mismatches, and returns `2` (`None` in `ptr::guaranteed_eq`) for **all** `GlobalAlloc::Memory` (`const`/promoted), `Function`, `VTable`, and `TypeId` allocations because codegen/CGU constant merging may alias or duplicate read-only allocations (`#73722`, `#128775`). `Basis: source + execution`
2. **Deferred deep validation, recursive interning mutability, and the ZST `UnsafeCell` carve-out.** During stepping, `CompileTimeMachine::enforce_validity` (`const_eval/machine.rs` L410–412) checks only `layout.is_uninhabited()` by default, deferring full `RefTracking` validation to `const_validate_mplace` (`eval_queries.rs` L119–165, L432–460; `validity.rs` L1314–1396) after termination. `intern_const_alloc_recursive` (`intern.rs` L214–240) assigns `(base_mutability, inner_mutability)` as `(Not, Not)` for `Constant` and `Promoted`, `(Mut, Mut)` for `Static(Mut)`, and `(if is_freeze { Not } else { Mut }, Not)` for `Static(Not)`—confirmed in live LLVM IR, where `static FROZEN_STATIC: u64` lowers to `internal constant` (`.rodata`) while `static INTERIOR_MUT_STATIC: SyncUnsafeU64` lowers to writable `internal global` (`.data`). For `const` items, `CtfeValidationMode::Const { allow_immutable_unsafe_cell: !inner }` (`eval_queries.rs` L448) allows outer `UnsafeCell` values (materialized into a fresh local on each mention) while rejecting non-ZST `UnsafeCell` (`size != 0`, `validity.rs` L1383–1394) behind any shared reference (`&Cell<u32>` fails with `E0080: encountered UnsafeCell in read-only memory`, whereas zero-sized `&[Cell<u32>] = &[]` and union-constructed `&Cell<()>` pass validation and Miri). `Basis: source + execution`
3. **`const_eval_select` is rewritten by MIR query pipelines, not interpreted, and its sysroot obligation is relational rather than point-wise equal.** `core::intrinsics::const_eval_select` (`library/core/src/intrinsics/mod.rs` L2401–2408, notably a **safe** `pub const fn` gated by `#![feature(const_eval_select)]`) is preserved with both function arms in `Runtime(PostCleanup)` MIR (`mir_drops_elaborated_and_const_checked`), then statically rewritten by `remap_mir_for_const_eval_select` (`rustc_mir_transform/src/lib.rs` L237–307): `inner_mir_for_ctfe` (L507) rewrites the call to `called_in_const`, whereas `inner_optimized_mir` (L799) rewrites it to `called_at_rt` **unconditionally before any MIR optimization pass**, even at `-C opt-level=0`. Across all 2,472 non-test `.rs` files in the sysroot (`14210df0e` and `58cf8f9c3`), there are exactly **32** `const_eval_select` occurrences (`26` `core`, `5` `alloc`, `1` `stdarch`), comprising `2` macro definitions, `11` runtime UB/precondition guards (`if const { true } else { ... }`, plus `c_str.rs:390`), `7` algorithmic/SIMD/provenance/FFI replacements, `3` contract/Miri hooks, `4` diverging panic formatters, `4` `const_heap` allocator hooks, and `1` SIMD test helper. Crucially, `core/src/str/validations.rs:136` returns `usize::MAX` in `const` vs. `v.as_ptr().align_offset(USIZE_BYTES)` at runtime (`f_ct(v) ≠ f_rt(v)`), proving that raw call-site return equality is too strong for real `libcore`: soundness requires either direct relational refinement under caller preconditions or an encapsulated helper invariant preserved by the enclosing consumer loop. Neither `rustc` nor Miri checks equivalence between the two arms (`CE1_CT=0` vs. `CE1_RT=1` executes with zero diagnostics). `Basis: source + execution + derived`
4. **`is_val_statically_known` has three distinct execution semantics across CTFE, LLVM codegen, and Miri.** `CompileTimeMachine::call_intrinsic` (`const_eval/machine.rs` L548) returns `false` unconditionally; `MIR GVN` treats intrinsic call destinations as `VnOpaque` and never folds it; `rustc_codegen_llvm` (`intrinsic.rs` L246–256) emits `@llvm.is.constant.<ty>` **only** when the argument lowers as `OperandValue::Immediate` (folding to `0` at `-O0` before LLVM inlining and `1` at `-O3` after inlining a constant caller argument, while emitting constant `false` even at `-O3` for non-immediate `OperandValue::Ref` arrays); and standalone Miri (`src/tools/miri/src/intrinsics/mod.rs` L167–178) flips a pseudo-random `bool` (`true` at `-Zmiri-seed=0`, `false` at `-Zmiri-seed=1`) specifically to expose unsound callers. Soundness therefore requires **Oracle-Bit Invariance** across `b ∈ {false, true}`. Sysroot occurrences grow from **7** in `core` at `14210df0e` to **11** at `58cf8f9c3` (`1.99.1`, adding 4 power-of-two `ilog` fast paths). `Basis: source + execution`
5. **`Const::Unevaluated`, post-monomorphization errors (PMEs), implicit `promote_consts`, and `MIR GVN`.** Polymorphic `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR retain generic associated constants (`<T as Cap>::LIMIT`) as `Const::Unevaluated` and const generics (`N`) as `Const::Ty`, while `MIR GVN` (`gvn.rs` L1794–1958) evaluates monomorphic `Const::Unevaluated` (`const { 6 * 7 }`) via `DummyMachine` and folds pure scalar arithmetic (`const 51_u64`) while refusing to fold any value with provenance (`may_have_provenance`, L1816–1827, L1953–1955) or `PointerExposeProvenance`. `RequiredConstsVisitor` (`rustc_mir_transform/src/lib.rs` L465) records `const { ... }` blocks and associated constants in `body.required_consts` *before* dead-branch pruning, and `MirUsedCollector` (`collector.rs` L705–723, L1349–1353) forces evaluation for every reachable monomorphized function—so `if false { generic_pme_gate::<u64>(); }` and `if false { const { 1 / 0 }; }` fail with `E0080` even at `-C opt-level=3`, whereas an uninstantiated generic `impl<T> SizeBound for T` compiles cleanly until `u64` is monomorphized, and `if dead_flag { let _ = &(1 / 0); }` is skipped by `promote_consts` (`promote_consts.rs` L402–520) and compiles without CTFE failure. `Basis: source + execution`
6. **Kernel-checked Lean `v4.34.1` model** (`support/CtfeAndConstEvalSelectSoundness.lean`, `1,668` lines, `24` `theorem` declarations, `568` namespace constants, axiom footprint `[propext]` only, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`/`unsafe` definitions, `0` `._unsafe_rec` helpers):
   - Formalizes `ctfeEval` and `rtEval` over symbolic `(AllocId, Offset)` heaps vs. concrete `ConcreteLayout` placements and non-deterministic `oracle : Nat → Bool`;
   - Proves three-valued `ctfe_guaranteed_ptr_eq_sound` across all `ValidLayout`s plus `const_memory_guaranteed_eq_indeterminate_necessary` (constructing merged and split `ValidLayout` witnesses for `constMemory`);
   - Proves contextual helper-invariant soundness (`constEvalSelect_contextual_helper_sound`), operational refinement (`ctfe_eval_refines_rt_eval`), and the master substitution theorem (`ctfe_to_runtime_substitution_sound`);
   - Proves three sharpness counterexamples: **CE1** (`ce1_unsound_const_eval_select_breaks_gvn_confluence`), **CE2** (`ce2_unsafecell_rodata_interning_ub_and_aliasing`), and **CE3** (`ce3_non_invariant_ivsk_breaks_opt_refinement`). `Basis: execution (Lean kernel) + derived`
7. **Anneal trusted MIR ingestion boundary** (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`): `Trusted/MirAst.lean` (`ConstLit`, L504–518) models only already-evaluated `ConstLit.scalar (BitVec 128)` and `ConstLit.zeroSized`. `Const::Unevaluated`, `Const::Ty`, slice/indirect allocation constants, `StatementKind::ConstEvalCounter`, `Operand::RuntimeChecks`, and `TerminatorKind::Call` (`const_eval_select`, `is_val_statically_known`) fail closed outside the scalar subset. Soundly discharging `Const::Unevaluated` or `const_eval_select` in downstream MIR verification requires the `InternValidFreeze`, `CesRelationalContract` (or contextual `HelperInv`), and `IvskOracleInvariant` side conditions established here. `Basis: source + derived`

> **Scope caution.** `support/CtfeAndConstEvalSelectSoundness.lean` is a standalone clean-room operational model of CTFE vs. runtime evaluation; it does not verify the Rust implementation of `rustc_const_eval` directly, does not import `joshlf/anneal`'s `Trusted.*` modules, and abstracts byte-level sub-word provenance splitting, Stacked/Tree Borrows aliasing tags, unwinding, and `const_heap` dynamic deallocation. See **Boundaries**.

## Applicability

**Subjects and their relationships.**

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, `x86_64-unknown-linux-gnu`, `LLVM version: 22.1.6`) is the primary implementation audited in source and executed live across all 21 checks in `support/probe_ctfe_and_const_eval_select.py` (including the bundled `miri` driver and `rust-src` `library/` tree). Unqualified `compiler/`, `library/`, and `src/tools/miri/` line numbers refer to this revision.
- `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1`, `2026-10-13`) is inspected at source level to compare sysroot `const_eval_select` (`32` sites in both revisions) and `is_val_statically_known` (`7` → `11` sites) call-site evolution.
- `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`) is inspected at source level to verify stability and drift of `CompileTimeMachine`, `intern_const_alloc_recursive`, `validity.rs`, `promote_consts.rs`, and `gvn.rs` (Finding 9).
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` is the Rust Reference submodule pinned by `rust-lang/rust@14210df0e`, providing normative language rules for constant expressions (`src/const_eval.md`), value-copied `const` items (`src/items/constant-items.md`), interior-mutable `static` items (`src/items/static-items.md`), and temporary lifetime extension (`src/destructors.md`).
- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` is audited at `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` and `trusted/audit/TrustedBoundary.lean` to establish how Anneal's trusted MIR semantics and kernel axiom checker interact with CTFE constants and intrinsics (Finding 9).
- `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `x86_64-unknown-linux-gnu`, Release) is the Lean kernel used to verify `support/CtfeAndConstEvalSelectSoundness.lean`.

**Configuration and target scope.** All live compilations and native runs execute on `x86_64-unknown-linux-gnu` (64-bit pointer width, little-endian) with `--edition=2021`, comparing `-C opt-level=0` (`mir-opt-level=1` default, no LLVM inlining) against `-C opt-level=3` (full `MIR GVN` and LLVM `-O3` inlining + `@llvm.is.constant` folding). Specimens exercising internal intrinsics opt into nightly `#![feature(core_intrinsics, const_eval_select)]` or `#![feature(const_raw_ptr_comparison)]`; standalone Miri runs use `#![feature(no_core, lang_items, intrinsics, rustc_attrs)]` so Miri executes directly without requiring an external crates.io sysroot build, testing `-Zmiri-seed=0`, `-Zmiri-seed=1`, `-Zmiri-strict-provenance`, and `--cfg case_rodata_write_ub`.

**Generalization boundaries.** The symbolic provenance invariants of `CtfeProvenance`, `remap_mir_for_const_eval_select`, `intern_const_alloc_recursive`, `RequiredConstsVisitor`, and `promote_consts` are target-independent in `rustc_const_eval` and `rustc_mir_transform`. By contrast, whether `is_val_statically_known(arg)` emits `@llvm.is.constant` vs. constant `false` depends on the backend ABI classification (`OperandValue::Immediate` vs. `OperandValue::Pair` / `OperandValue::Ref` in `rustc_codegen_llvm/src/intrinsic.rs` L246–256), and `-O3` folding of `@llvm.is.constant` depends on LLVM's inlining heuristics.

## Findings

### 1. `CompileTimeMachine` vs. runtime MIR execution: provenance, fuel, UB checks, and `ptr_guaranteed_cmp`

`Basis: normative + source + execution`

`InterpCx<'tcx, M>` (`compiler/rustc_const_eval/src/interpret/eval_context.rs` L27–49) parameterizes stepping (`step.rs`), memory (`memory.rs`), place dereferencing (`place.rs`), and operator evaluation (`operator.rs`) over `M: Machine<'tcx>`. Compile-time evaluation instantiates `M = CompileTimeMachine<'tcx>` (`compiler/rustc_const_eval/src/const_eval/machine.rs` L184–200), imposing four strict restrictions absent from runtime execution:

1. **Symbolic `CtfeProvenance` with zero address exposure (`compiler/rustc_middle/src/mir/interpret/pointer.rs` L91–191):** `CtfeProvenance(NonZero<u64>)` bit-packs a 32-bit `AllocId` together with `immutable` (`bit 62`) and `shared_ref` (`bit 61`) flags, declaring `OFFSET_IS_ADDR = false` (L169) and `WILDCARD = None` (L172). Consequently:
   - Casting a pointer to an integer (`CastKind::PointerExposeProvenance`) is rejected statically in const contexts (`error: pointers cannot be cast to integers during const eval`, Specimen 5 `case_ptr_to_int`) and dynamically in `CompileTimeMachine::expose_provenance` (`const_eval/machine.rs` L862–868: `"exposing pointers is not possible at compile-time"`).
   - Reinterpreting pointer bytes in memory as `usize` (`*(&raw const p as *const usize)`) reaches `InterpCx` scalar validation (`validity.rs` L532; `memory.rs` L1401–1415) and aborts with `ReadPointerAsInt` (`error[E0080]: unable to turn pointer into integer`, Specimen 5 `case_ptr_read_as_int`).
   - Relational raw-pointer comparisons (`p < q`) fail statically in `check_consts` (`error: pointers cannot be reliably compared during const eval`, Specimen 5 `case_raw_ptr_cmp`) and dynamically in `CompileTimeMachine::binary_ptr_op` (`const_eval/machine.rs` L790–797), whereas provenance-preserving in-bounds `BinOp::Offset` (`ptr::add`) is handled before machine fallback in `interpret/operator.rs` L311–344 and `memory.rs` L481–550 (`check_ptr_access_signed`).
   - At runtime (and in permissive Miri, Specimen 6), `expose_provenance` + `with_exposed_provenance` executes deterministically; under `-Zmiri-strict-provenance`, Miri rejects integer-to-pointer casts with `unsupported operation: integer-to-pointer casts and ptr::with_exposed_provenance are not supported with -Zmiri-strict-provenance`.
2. **Three-valued `ptr_guaranteed_cmp` (`const_eval/machine.rs` L278–387):** Invoked by `ptr::guaranteed_eq` / `ptr::guaranteed_ne`, `ptr_guaranteed_cmp` returns `1` (definitely equal), `0` (definitely unequal), or `2` (runtime-dependent / `None`):
   - Two pure integer pointers (`(Err(a), Err(b))`) compare exactly (`(a == b) as u8`, L281).
   - One symbolic pointer vs. an integer (`(Ok(ptr), Err(int))`) returns `0` iff `!ecx.scalar_may_be_null(Scalar::from_pointer(ptr.wrapping_sub(int, ecx), ecx))` (proving e.g. an in-bounds reference is non-null), else `2` (L286–303).
   - Two symbolic pointers (`(Ok(a), Ok(b))`) first check alignment modular arithmetic: if offsets modulo `min(a_align, b_align)` differ, concrete addresses cannot coincide under any aligned placement, returning `0` (L307–318). Next, if **both** `AllocId`s resolve to `GlobalAlloc::Static` (and neither is an `extern static`), `a_allocid == b_allocid` returns `(a_offset == b_offset) as u8`, while distinct statics with **both** offsets strictly in-bounds (`a_offset < a_size && b_offset < b_size`, avoiding adjacent one-past-the-end coincidence) return `0` (L320–359).
   - For **all** `GlobalAlloc::Memory` (constant/promoted allocations), `GlobalAlloc::Function`, `GlobalAlloc::VTable`, and `GlobalAlloc::TypeId` pointers—even with identical `AllocId` and offset!—`ptr_guaranteed_cmp` returns `2` (`None`), citing cross-CGU duplication and LLVM constant merging (`#73722`, `#128775`, L361–384). Specimen 2 confirms `STATIC_SAME=Some(true)`, `STATIC_DIFF=Some(false)`, and `CONST_MEM_EQ=None` on two `b"hello_ctfe"` slices.
3. **Deterministic step fuel (`ctfe_limit.rs` L18–55; `step.rs` L138–140; `const_eval/machine.rs` L33–39, L817–859):** `inner_mir_for_ctfe` (`rustc_mir_transform/src/lib.rs` L508) runs `ctfe_limit::CtfeLimit`, inserting `StatementKind::ConstEvalCounter` at loop backedges and call headers (verified in Specimen 1 `compute_triangular` MIR). `CompileTimeMachine::increment_const_eval_counter` increments `num_evaluated_steps` and triggers the `long_running` lint at multiples of `LINT_TERMINATOR_LIMIT = 2_000_000`.
4. **Compiler-flag-independent UB checks (`const_eval/machine.rs` L781–788 vs. `instsimplify.rs` L461–471):** `CompileTimeMachine::runtime_checks` returns `Ok(true)` unconditionally for `UbChecks`, `ContractChecks`, and `OverflowChecks` (ignoring `-C debug-assertions` / `-Z ub-checks` so `const` evaluation cannot vary across downstream crate flags), whereas `SimplifyUbCheck` folds `Operand::RuntimeChecks(UbChecks)` to `tcx.sess.ub_checks()` in runtime MIR.

### 2. Two-step validity, `intern_const_alloc_recursive`, and `UnsafeCell` vs. `.rodata`

`Basis: normative + source + execution`

Constant evaluation validates and interns values in two distinct steps after `InterpCx` returns (`compiler/rustc_const_eval/src/const_eval/eval_queries.rs` L119–165, L432–460):

- **Step-time vs. final deep validation:** During execution, `CompileTimeMachine::enforce_validity` (`const_eval/machine.rs` L410–412) returns `tcx.sess.opts.unstable_opts.extra_const_ub_checks || layout.is_uninhabited()`, avoiding per-assignment recursive memory walks. Once evaluation terminates, `eval_to_allocation_raw_provider` runs `intern_const_alloc_recursive` followed by `const_validate_mplace` with `RefTracking::new(mplace)` (`eval_queries.rs` L142–163), recursively traversing every reachable reference to enforce initialized scalar bytes (`check_safe_pointer`, `validity.rs` L520–565), non-null aligned in-bounds targets (`validity.rs` L780–868), and `Freeze` rules (`validity.rs` L1314–1396).
- **Mutability matrix in `intern_const_alloc_recursive` (`compiler/rustc_const_eval/src/interpret/intern.rs` L214–240):**

  | `InternKind` | Root `base_mutability` | Nested `inner_mutability` (pointees of references) | Resulting LLVM global kind (Specimen 3) |
  | :--- | :--- | :--- | :--- |
  | `InternKind::Constant` (`const`) | `Mutability::Not` | `Mutability::Not` | Copied per value use; pointees in `.rodata` |
  | `InternKind::Promoted` (`promoted[k]`) | `Mutability::Not` | `Mutability::Not` | Shared `constant` in `.rodata` |
  | `InternKind::Static(Mutability::Not)` (`static`) | `if is_freeze { Not } else { Mut }` | `Mutability::Not` | `FROZEN_STATIC`: `internal constant`; `INTERIOR_MUT_STATIC`: `internal global` (writable `.data`) |
  | `InternKind::Static(Mutability::Mut)` (`static mut`) | `Mutability::Mut` | `Mutability::Mut` | Writable `global` (`.data`) |

- **Three-layer `UnsafeCell` safety gate (verified across Specimens 3, 5, and 6):**
  1. *Outer `const` value (`inner == false`):* `CtfeValidationMode::Const { allow_immutable_unsafe_cell: !inner }` (`eval_queries.rs` L448) permits `pub const CELL_CONST: Cell<u64> = Cell::new(100)` because every mention of `CELL_CONST` in runtime MIR materializes a fresh local copy, and `promote_consts` (`HasMutInterior`) refuses to promote `&CELL_CONST` to `'static` (`exercise_const_cells` emits `0` promoted bodies; `FRESH_SUM=200`, `TEMP_MUT=777`).
  2. *Behind a shared reference (`inner == true`) or in `Promoted`:* `validity.rs` L1383–1394 checks `let zst = ... s.bytes() == 0; if !zst { throw_validation_failure!(... EncounteredUnsafeCellInReadonlyMemory) }`. In Specimen 5 (`case_inner_unsafecell`), transmuting `&'static u32` to `&'static Cell<u32>` inside a `const` fails at `const_validate_mplace` with `error[E0080]: constructing invalid value of type &Cell<u32>: at .<deref>.value, encountered UnsafeCell in read-only memory`. Conversely, zero-sized `pub const EMPTY_CELL_SLICE: &[Cell<u32>] = &[]` and union-constructed `pub const ZST_CELL_REF: &Cell<()>` pass validation (`s.bytes() == 0`, zero mutable bytes in `.rodata`) and execute `ZST_CELL_REF.set(())` cleanly in Specimen 3 (`CompileTimeMachine::before_memory_write` at `machine.rs` L985 explicitly returns `Ok(())` when `size.bytes() == 0`). Note that writing `&Cell::new(())` directly on a temporary in a `const` is rejected earlier by front-end temporary lifetime extension (`E0492`).
  3. *What goes wrong if this gate is bypassed (CE2 in Specimen 6):* Mutating through `*const UnsafeCell<u64>` pointing to an immutable allocation triggers immediate UB in Miri (`error: Undefined Behavior: writing to alloc4 which is read-only`).

### 3. `const_eval_select`: MIR lowering mechanics, 32-site sysroot census, and relational obligation

`Basis: source + execution + derived`

In `library/core/src/intrinsics/mod.rs` L2401–2408, `const_eval_select` has the signature:

```rust
#[rustc_intrinsic]
#[rustc_const_unstable(feature = "const_eval_select", issue = "124625")]
pub const fn const_eval_select<ARG: Tuple, F, G, RET>(
    arg: ARG,
    called_in_const: F,
    called_at_rt: G,
) -> RET
where
    F: const FnOnce<ARG, Output = RET>,
    G: FnOnce<ARG, Output = RET>;
```

Notice that `const_eval_select` is declared as a **safe** `pub const fn` (not `unsafe fn`), gated behind `#![feature(const_eval_select)]`; safety when `F` or `G` wraps `unsafe` operations is enforced by the `const_eval_select!` macro (`intrinsics/mod.rs` L2436–2467), which synthesizes local `fn compiletime(...)` and `fn runtime(...)` items inheriting the enclosing `unsafe` requirement only if callers mark them `unsafe` or wrap unsafe blocks internally.

**MIR pipeline bifurcation (`compiler/rustc_mir_transform/src/lib.rs` L237–307, L507, L799).** `InterpCx` does **not** interpret `const_eval_select` dynamically (`const_eval/machine.rs` has no arm for it). Instead:
- `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)` MIR) preserves the `TerminatorKind::Call` to `const_eval_select((args...), sum_bytes_ct, sum_bytes_rt)` intact so const-checking verifies `F: const FnOnce` while borrow-checking checks tuple capture (confirmed in Specimen 1 `sum_dispatch.runtime-post-cleanup.after.mir`).
- `inner_mir_for_ctfe` (L507) invokes `remap_mir_for_const_eval_select(tcx, body, hir::Constness::Const)`, unpacking the argument tuple `_2` into projected fields `(move (_2.0), move (_2.1), ...)` and rewriting the call target directly to `called_in_const` (`sum_bytes_ct`).
- `inner_optimized_mir` (L799) invokes `remap_mir_for_const_eval_select(tcx, body, hir::Constness::NotConst)` **before running any `mir-opt` pass**—so even at `-C opt-level=0`, `Runtime(Optimized)` MIR calls `sum_bytes_rt` directly with zero residual `const_eval_select` call (confirmed in Specimen 1 `sum_dispatch.runtime-optimized.after.mir`).

**Complete 32-site sysroot census (`14210df0e` and `58cf8f9c3`, `support/probe_output/sysroot_const_eval_census.json`).** Scanning all `2,472` non-test `.rs` files in `library/` finds exactly `32` `const_eval_select` occurrences (`26` in `core`, `5` in `alloc`, `1` in `stdarch`), identical in count and classification across `1.98.0-nightly` (`14210df0e`) and `1.99.1` (`58cf8f9c3`):

| Class | Count | Sites (`library/` relative path : line at `14210df0e`) | Relational relationship between `called_in_const` (`f_ct`) and `called_at_rt` (`f_rt`) |
| :--- | :---: | :--- | :--- |
| **Macro definitions** | `2` | `core/src/intrinsics/mod.rs:2450, 2461` | Desugars `const_eval_select!(@capture ... if const ... else ...)` into `const_eval_select(tuple, compiletime, runtime)`. |
| **Class A: Algorithmic, SIMD, provenance & FFI refinement** | `7` | `core/src/slice/ascii.rs:461, 598`; `core/src/slice/memchr.rs:54`; `core/src/str/validations.rs:136`; `core/src/ptr/const_ptr.rs:26`; `core/src/ptr/mod.rs:1399`; `core/src/ffi/c_str.rs:749` | `ascii`/`memchr`/`swap_nonoverlapping`/`strlen`: byte-by-byte loop in `const` vs. word-aligned `usize`, SSE2 SIMD, untyped chunk copy, or C `extern "C" fn strlen` at runtime. **Two non-point-wise-equal sites:** (1) `str/validations.rs:136` returns sentinel `usize::MAX` in `const` vs. `v.as_ptr().align_offset(USIZE_BYTES)` at runtime (`f_ct(v) ≠ f_rt(v)`!), unified only by the enclosing `run_utf8_validation` loop (`L140–236`); (2) `ptr/const_ptr.rs:26` (`is_null`) matches `ptr.guaranteed_eq(null_mut())`, panicking in `const` on `None` (indeterminate provenance) whereas `f_rt` computes `ptr.addr() == 0` (total asymmetric refinement: `f_ct(p) = Ok(v) ⇒ f_rt(p) = Ok(v)`). |
| **Class B: Runtime UB & safety precondition guards** | `11` | `core/src/ub_checks.rs:98, 136, 166`; `core/src/ptr/const_ptr.rs:357, 707, 837, 943`; `core/src/ptr/mut_ptr.rs:360, 935, 1041`; `core/src/ffi/c_str.rs:390` | `10` sites return `true`/`false` no-ops in `const` (relying on `InterpCx` natively catching misaligned/out-of-bounds/overlapping pointer UB during CTFE!) while checking concrete `ptr.addr()`, `is_aligned_to`, and `this >= origin` at runtime under `ub_checks()`. Inverted `11`th site (`ffi/c_str.rs:390`, `from_bytes_with_nul_unchecked`): `const` scans every byte to panic on missing/interior NUL, while `runtime` performs an unchecked cast assuming the `unsafe` precondition. Conditional equivalence holds **only** on inputs satisfying the enclosing `unsafe` precondition `Pre(args)`. |
| **Class C: Contract & Miri symbolic hooks** | `3` | `core/src/intrinsics/mod.rs:2689, 2721, 3587` | `contract_check_requires`, `contract_check_ensures` (no-op in `const` because closures cannot be called polymorphically without `const Fn`; checked at runtime) and `miri_promise_symbolic_alignment` (no-op in `const`, Miri hook at runtime). |
| **Class D: Diverging panic & allocation error formatters** | `4` | `core/src/panic.rs:167`; `core/src/panicking.rs:96`; `core/src/str/mod.rs:69`; `alloc/src/alloc.rs:557` | Return type `!`: both arms diverge (`panic_fmt` vs. formatting/backtrace/OOM hook), vacuously satisfying value postconditions while differing only in diagnostic side effects. |
| **Class E: `const_heap` allocator dispatch** | `4` | `alloc/src/alloc.rs:332, 344, 362, 379` | `Global::{alloc, deallocate, grow, shrink}`: dispatches to `intrinsics::const_allocate` / `const_deallocate` in `const` vs. `__rust_alloc` / `__rust_dealloc` system allocator at runtime. |
| **Class F: SIMD test assertion helper** | `1` | `stdarch/crates/core_arch/src/test.rs:18` | `assert_eq_const`: byte-wise `assert_eq_ct` vs. `Debug`-formatted `assert_eq_rt`. |

**Unchecked soundness hazard (Specimen 4 & Specimen 6).** Neither `rustc` nor Miri enforces any check that `called_in_const` and `called_at_rt` agree. In Specimen 4 (`divergent_const_eval_select_and_ivsk_hazards.rs`), `buggy_select` returns `0` in `ct_branch` and `if p.addr().is_multiple_of(8) { 1 } else { 2 }` in `rt_branch`; `rustc` compiles it with zero warnings (`CE1_CT=0`, `CE1_RT=1`), and Miri executes it with exit code `0` / witness `11` (`CT_SELECT_VAL=0`, `rt_select_val=1`). Consequently, if `MIR GVN` or `ConstProp` folds a `const_eval_select` call site at `-O3` while `-O0` executes `called_at_rt`, optimization confluence is violated unless `CesRelationalContract` (or contextual `HelperInv` for encapsulated helpers like `str/validations.rs:136`) holds across **all** admissible concrete allocator layouts.

### 4. `is_val_statically_known`: three-way lowering semantics and Oracle-Bit Invariance

`Basis: source + execution`

`core::intrinsics::is_val_statically_known<T: Copy>(val: T) -> bool` (`library/core/src/intrinsics/mod.rs` L2541–2543, also a **safe** `pub const fn`) exhibits three distinct behaviors across the compiler stack:

1. **CTFE (`compiler/rustc_const_eval/src/const_eval/machine.rs` L548):** `"is_val_statically_known" => ecx.write_scalar(Scalar::from_bool(false), dest)?`—always `false`, even on a literal `is_val_statically_known(42_usize)` (`CTFE_IVSK=false` in Specimen 2).
2. **MIR passes (`compiler/rustc_mir_transform/src/gvn.rs`):** `TerminatorKind::Call` assigns a fresh `VnOpaque` value to `destination`, so `is_val_statically_known` is never folded in MIR (`Runtime(Optimized)` MIR retains the intrinsic call).
3. **LLVM codegen (`compiler/rustc_codegen_llvm/src/intrinsic.rs` L246–256):**
   ```rust
   sym::is_val_statically_known => {
       let [arg] = args else { span_bug!(span, "Wrong number of arguments...") };
       if let OperandValue::Immediate(val) = arg.val {
           let intrinsic = bx.get_intrinsic(&format!("llvm.is.constant.{}", ...));
           let res = bx.call(ty, None, None, intrinsic, &[val], None, None);
           ...
       } else {
           bx.const_bool(false)
       }
   }
   ```
   Two immediate consequences verified in Specimen 2 (`gvn_ctfe_boundary_and_statically_known.rs`):
   - For immediate scalars (`usize`), `-C opt-level=0` emits `call i1 @llvm.is.constant.i64(i64 %x)` inside un-inlined `ivsk_observable_oracle`, evaluating to **`0` (`false`)** even when called as `ivsk_observable_oracle(42)` (`KNOWN_CONST=0`); at `-C opt-level=3`, LLVM inlines `ivsk_observable_oracle(42)`, sees constant `i64 42`, folds `@llvm.is.constant.i64(i64 42)` to `true` (eliminating all `@llvm.is.constant` calls from `-O3` LLVM IR), and returns **`1` (`true`)** (`KNOWN_CONST=1`), while `ivsk_observable_oracle(black_box(42))` remains **`0`** at both `-O0` and `-O3` (`KNOWN_OPAQUE=0`).
   - For non-immediate `Copy` types passed indirectly (`[u64; 4]`, `OperandValue::Ref`), `rustc_codegen_llvm` emits `const_bool(false)` unconditionally (`NON_IMM=false` even at `-O3` on literal `[1, 2, 3, 4]`).
4. **Standalone Miri (`src/tools/miri/src/intrinsics/mod.rs` L167–178):** Miri executes `let branch: bool = this.machine.rng.get_mut().random();` at runtime—verified in Specimen 6, where `-Zmiri-seed=0` yields `rt_ivsk_val = true` (exit code `11`) and `-Zmiri-seed=1` yields `rt_ivsk_val = false` (exit code `10`).

**Sysroot census (`7` sites at `14210df0e` → `11` sites at `58cf8f9c3`).** At `14210df0e`, `core` contains `7` call sites: `fmt/mod.rs:898` (`Arguments::as_str` optimization), `int_macros.rs:2513, 3128` and `uint_macros.rs:2906, 3577` (`div_euclid`/`rem_euclid` constant-exponent branch hints), `uint_macros.rs:1825` (`ilog` constant base), and `slice/specialize.rs:55` (`memset`-friendly byte-fill specialization). At `58cf8f9c3` (`1.99.1`), `int_macros.rs` and `uint_macros.rs` add `4` sites (`11` total) specializing `ilog(base)` when `base.is_power_of_two()`. Every sound call site satisfies **Oracle-Bit Invariance**: both arms of `if is_val_statically_known(x)` compute observationally identical outputs (`Specimen 2` `ivsk_scalar_branch(9) == 27` in CTFE and runtime, whereas `Specimen 4` `buggy_ivsk_branch(42)` returns `200` at `-O0` vs. `100` at `-O3`).

### 5. `Const::Unevaluated`, post-monomorphization errors (PMEs), implicit `promote_consts`, and `MIR GVN`

`Basis: normative + source + execution`

- **Three `mir::Const` representations (`compiler/rustc_middle/src/mir/consts.rs` L224–285):**
  1. `Const::Val(ConstValue, Ty)`: already-evaluated `Scalar`, `ZeroSized`, `Slice`, or `Indirect { alloc_id, offset }`;
  2. `Const::Unevaluated(UnevaluatedConst, Ty)`: un-evaluated `DefId` + generic `args` (plus optional `Promoted` index), arising from associated constants (`<T as Cap>::LIMIT`), `const { ... }` inline blocks (`generic_unevaluated::<T, N>::{constant#1}`), and array repeat counts;
  3. `Const::Ty(Ty, ty::Const)`: type-system const generics (`const N: usize`).
  `Const::is_required_const` (L270–280) returns `true` for `Const::Unevaluated` and non-value `Const::Ty`.
- **Why `const { ... }` and associated constants in dead `if false` branches still fail at `-O3` (PME semantics):**
  1. During `mir_const` construction (`rustc_mir_transform/src/lib.rs` L465), `RequiredConstsVisitor` populates `body.required_consts` **before** `promote_consts` or any dead-branch simplification runs.
  2. During monomorphization (`compiler/rustc_monomorphize/src/collector.rs` L705–723, L1349–1362), `collect_items_of_instance` evaluates every entry in `body.required_consts` AND walks `body.mentioned_items()` (recorded by `MentionedItems` before `SimplifyConstCondition` prunes dead blocks!) in `CollectionMode::MentionedItems`.
  3. Specimen 5 empirically confirms all three consequences:
     - When `impl<T> SizeBound for T { const CHECK: usize = { assert!(size_of::<T>() <= 4); ... }; }` is instantiated **only** at `u32` (`case_pme_ok_u32`), compilation succeeds (`rc == 0`) because `<u64 as SizeBound>::CHECK` is never monomorphized.
     - Placing `if false { let _ = generic_pme_gate::<u64>(); }` inside `main` (`case_pme_dead_branch`) fails with **`error[E0080]: evaluation panicked: PME: T exceeds 4 bytes`** at **both `-C opt-level=0` and `-C opt-level=3`** because `mentioned_items` retains `generic_pme_gate::<u64>` across dead-branch elimination and triggers `required_consts` evaluation on it!
     - Placing `if false { let _ = const { 1_u32 / 0 }; }` inside `main` (`case_inline_const_dead_branch`) likewise fails with **`error[E0080]: attempt to divide 1_u32 by zero`** even at `-C opt-level=3`.
- **Implicit rvalue promotion (`compiler/rustc_mir_transform/src/promote_consts.rs` L243–246, L402–520, L660–682) vs. explicit `const { ... }`:**
  - Implicit promotion extracts pure, infallible rvalue borrows into synthetic `promoted[k]` bodies interned in `.rodata` with `'static` lifetime, **never** introducing new compile-time panics in unexecuted code. `Validator::validate_local` / `validate_rvalue` rejects `NeedsDrop`, `HasMutInterior` (**except** zero-length mutable array `&mut []`, explicitly carved out at L411–419 and confirmed as `promoted[0]` in Specimen 1!), `PointerExposeProvenance`, raw-pointer `BinaryOp`, `Div`/`Rem` with zero or non-const divisor, `RuntimeChecks`, and calls to non-`#[rustc_promotable]` functions inside `fn` / `const fn` / `const { ... }` bodies (allowing arbitrary `const fn` promotion only inside `promotion_safe_blocks` of top-level `const`/`static` initializers). Thus in Specimen 1, `&(1_u32 / 0)` inside `if dead_flag` is left in-place on the stack (`_16 = Div(const 1_u32, const 0_u32); _15 = &_16;`) and causes **no** CTFE error.
- **`MIR GVN` vs. `CompileTimeMachine` (`compiler/rustc_mir_transform/src/gvn.rs` L426, L604–606, L682, L1794–1958):**
  - `VnState` instantiates `InterpCx::new(tcx, typing_env, DummyMachine)` (`const_eval/dummy_machine.rs`), marks unevaluated constants non-deterministic (`VnOpaque`) until `eval_mir_constant` succeeds, folds monomorphic `const { 6_u64 * 7_u64 } + 9` into `const 51_u64` (Specimen 2 `GVN.after.mir`), and folds `exposed_addr & 0` into `const 0_usize`, **while refusing to constant-fold**:
    1. Any constant allocation where `may_have_provenance` holds (`gvn.rs` L1816–1827, L1953–1955), preventing GVN from duplicating or forging pointer provenance; and
    2. `CastKind::PointerExposeProvenance` / `PointerWithExposedProvenance`—even on distinct `static` items `(&raw const STATIC_A as usize) != (&raw const STATIC_B as usize)`, which remains symbolic (`_13 = Ne(move _14, move _17)`) in `GVN.after.mir`!

### 6. Formal dual-mode CTFE-to-runtime refinement model (`support/CtfeAndConstEvalSelectSoundness.lean`)

`Basis: execution (Lean kernel) + derived`

`support/CtfeAndConstEvalSelectSoundness.lean` (`1,668` lines, `Init`-only) mechanizes the dual semantics and proves exact conditions under which CTFE evaluation and constant substitution refine runtime execution:

- **Memory, provenance, and layout definitions (`Section 1`–`Section 3`):**
  - `Val` distinguishes `.scalar n`, `.ptr aid off` (`AllocId × Offset`), `.zst`, and `.uninit`. Each `Allocation` carries `kind : AllocKind` (`.staticItem`, `.constMemory`, `.stackLocal`), `mutbl : Mutability` (`.immut`, `.mutWritable`), `align : Nat`, and `slots : List Slot` where each `Slot` tracks `cell : CellKind` (`.frozen` vs. `.unsafeCell`).
  - `ConcreteLayout` maps `baseAddr : AllocId → Nat` with `addrOf aid off := baseAddr aid + off`. `ValidLayout H L` requires: (1) non-null addresses `0 < L.baseAddr aid`, (2) alignment `L.baseAddr aid % a.align = 0`, and (3) pairwise disjointness `[base, base + size)` for distinct `.staticItem` allocations—deliberately omitting disjointness for `.constMemory` (`GlobalAlloc::Memory`).
  - `checkInternValidFreeze H v` (`InternValidFreeze H v`) rejects `.uninit`, dangling/out-of-bounds pointers, writable `.mutWritable` targets, uninitialized slots (`allSlotsInit`), and non-ZST `UnsafeCell` slots (`0 < a.size → allSlotsFrozen a.slots = true`), while preserving the exact `a.size = 0` ZST `UnsafeCell` carve-out (`validity.rs` L1383).
- **Dual evaluators (`Section 4`):** Implemented via total `Nat.repeat` and `List.foldr` (generating **zero** `._unsafe_rec` bytecode helpers in the kernel environment):
  - `ctfeEval` rejects `.ptrAddrMod` with `.unsupportedPtrToInt`, rejects pointer operands in `.add`/`.eqScalar` with `.typeMismatchOrPtrAsInt`, evaluates `.guaranteedPtrEq` via three-valued `ctfeGuaranteedPtrEq` (failing on `none`), dispatches `.constEvalSelect` to `ctArm`, evaluates `.isValStaticallyKnown` with `false`, and gates `.unevalConst` on `checkInternValidFreeze`.
  - `rtEval L oracle` computes `(L.addrOf aid off) % modulus` for `.ptrAddrMod`, compares `decide (L.addrOf a1 o1 = L.addrOf a2 o2)` for `.guaranteedPtrEq`, dispatches `.constEvalSelect` to `rtArm`, and dispatches `.isValStaticallyKnown site` to `kArm (oracle site)`.

| Theorem in `CtfeAndConstEvalSelectSoundness.lean` | Lines | Mechanized Guarantee |
| :--- | :---: | :--- |
| `ctfe_guaranteed_ptr_eq_sound` | L198–260 | Under every `ValidLayout H L`, if `ctfeGuaranteedPtrEq H a1 o1 a2 o2 = some b`, then `decide (L.addrOf a1 o1 = L.addrOf a2 o2) = b`. |
| `const_memory_guaranteed_eq_indeterminate_necessary` | L282–329 | Constructs a two-allocation `.constMemory` heap and two valid layouts (`mergedConstLayout`, `splitConstLayout`) where concrete pointer equality is `true` and `false` respectively, proving `ctfeGuaranteedPtrEq = none` is required for soundness. |
| `static_unsafecell_interned_writable` | L346–349 | Verifies `internBaseMutability .staticImmutDecl false = .mutWritable` vs. `.immut` when `isFreeze = true` (`intern.rs` L224–228). |
| `ctfeEval_preserves_validLayout` | L828–1076 | Every successful `ctfeEval` transition (including `.store` and `.allocLocal` via `Heap.freshId`) preserves `ValidLayout H' L`. |
| `constEvalSelect_contextual_helper_sound` | L1137–1186 | Even when `ctArm vArg ≠ rtArm vArg` (as in `core/src/str/validations.rs:136`), if both arms satisfy `HelperInv L H1 vArg r` and `callerCtx` is invariant across witnesses of `HelperInv`, `letBind (constEvalSelect ...) callerCtx` refines cleanly from `ctfeEval` to `rtEval`. |
| `ctfe_eval_refines_rt_eval` | L1201–1466 | Structural refinement across all 16 `MirExpr` forms: under `ValidLayout H L` and `WellFormedContracts e` (`CesRelationalContract` + `IvskOracleInvariant`), `ctfeEval fuel H e = .ok (v, H') → rtEval L oracle fuel H e = .ok (v, H')`. |
| `ctfe_to_runtime_substitution_sound` | L1500–1542 | **Master Substitution Theorem:** if `ctfeEval constFuel H e = .ok (v, H)` and `InternValidFreeze H v` and `WellFormedContracts e` hold, `substConstIfValid` folds `e` to `.lit v`, `.lit v` and `e` evaluate identically to `.ok (v, H)` in `rtEval L oracle` for **every** `ValidLayout` and **every** `oracle`, and any interned pointer targets an initialized, immutable, `Freeze` (or ZST) allocation. |

### 7. Three kernel-checked sharpness counterexamples (`CE1`, `CE2`, `CE3`)

`Basis: execution (Lean kernel + live rustc/Miri)`

Each major hypothesis of `ctfe_to_runtime_substitution_sound` is proved necessary by a constructive counterexample checked by the Lean kernel (`Section 8`) and mirrored by a live Rust specimen:

1. **CE1 — Unsound `const_eval_select` alignment inspection (`ce1_unsound_const_eval_select_breaks_gvn_confluence`, L1586–1601; Specimen 4 & Specimen 6):**
   - `ce1DivergentSelect` passes `.ptr 1 0` (pointing to 8-byte-aligned static `witnessHeap`) to `constEvalSelect` where `ctArm` returns `.scalar 0` and `rtArm` returns `(L.addrOf 1 0 % 8 == 0) ? 1 : 0`.
   - Lean proves `ValidLayout witnessHeap witnessLayout`, `InternValidFreeze witnessHeap (.scalar 0)`, CTFE-substituted `substConstIfValid` evaluates to `.ok (.scalar 0, witnessHeap)`, and un-folded `rtEval` evaluates to `.ok (.scalar 1, witnessHeap)` (`0 ≠ 1`), breaking `-O0` vs. `-O3` ConstProp/GVN confluence when `CesRelationalContract` is dropped.
2. **CE2 — `UnsafeCell` immutable `.rodata` interning UB and shared-place aliasing (`ce2_unsafecell_rodata_interning_ub_and_aliasing`, L1632–1645; Specimen 3, Specimen 5, & Specimen 6):**
   - Proves four conjuncts on `const CELL_CONST: Cell<u64> = Cell::new(100)`: (A) `checkInternValidFreeze` rejects `.ptr 10 0` targeting a non-ZST `.immut` `UnsafeCell` allocation; (B) mutating that `.rodata` slot at runtime faults with `.err .writeToImmut` (matching Miri's `Undefined Behavior: writing to alloc4 which is read-only`); (C) interning into a single shared `.mutWritable` allocation without per-mention copying causes `CELL_CONST.set(999)` on the first mention to corrupt a second mention from `100` to `999`; and (D) per-mention `.allocLocal` copying succeeds and preserves `.scalar 100`.
3. **CE3 — Non-invariant `is_val_statically_known` branch (`ce3_non_invariant_ivsk_breaks_opt_refinement`, L1656–1667; Specimen 4):**
   - `ce3NonInvariantIvsk` branches on `isValStaticallyKnown` returning `.scalar 100` on `true` and `.scalar 200` on `false`. Lean proves `rtEval` yields `.ok (.scalar 200, witnessHeap)` under `-O0` (`oracle := fun _ => false`) and `.ok (.scalar 100, witnessHeap)` under `-O3` post-inlining (`oracle := fun _ => true`), violating optimization refinement (`200 ≠ 100`) when `IvskOracleInvariant` is omitted.

### 8. Upstream drift (`1.98.0-nightly` → `1.99.1` → `1.102.0-nightly`) and Anneal trusted MIR boundary

`Basis: source`

- **Source drift across `rust-lang/rust` snapshots:**
  - Between `14210df0e` (`1.98.0-nightly`, `2026-05-31`) and `58cf8f9c3` (`1.99.1`, `2026-10-13`), `const_eval_select` remains at exactly `32` sysroot sites with identical per-crate (`26`/`5`/`1`) and per-class (`2`/`7`/`11`/`3`/`4`/`4`/`1`) counts; `is_val_statically_known` expands from `7` to `11` sites in `core/src/num/{int_macros,uint_macros}.rs` (`+4` power-of-two `ilog` fast paths, all satisfying `IvskOracleInvariant`).
  - Between `14210df0e` and `3ef0c22cd` (`1.102.0-nightly`, `2026-11-11`), `intern.rs` (`+7/-6` lines) preserves the exact 4-row `(base_mutability, inner_mutability)` table; `const_eval/machine.rs` (`+230/-36` lines) adds `call_llvm_intrinsic` (explicitly rejecting target LLVM SIMD intrinsics in CTFE) while keeping `ptr_guaranteed_cmp`, `expose_provenance`, `binary_ptr_op`, `runtime_checks -> true`, and `is_val_statically_known -> false` intact; `gvn.rs` (`+110/-41` lines) adds `PassPolicy` (`-Z mir-preserve-ub`) and `ty_may_have_ref` while retaining `DummyMachine` evaluation and `may_have_provenance` folding rejection.
- **Anneal trusted MIR boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
  - `trusted/lean/Trusted/MirAst.lean` (`inductive ConstLit`, L504–518; `inductive Operand`, L557–565; `inductive StatementKind`, L657–666; `inductive TerminatorKind`, L785–796) and `Trusted/MirSemantics.lean` (`evalConstLit`, L883–905; `TerminatorKind.call`, L1693) currently accept only `ConstLit.scalar (BitVec 128)` and `ConstLit.zeroSized`.
  - Any polymorphic `Const::Unevaluated`, const-generic `Const::Ty`, promoted slice/struct `ConstValue::Indirect` / `ConstValue::Slice`, `StatementKind::ConstEvalCounter`, `Operand::RuntimeChecks`, or intrinsic `TerminatorKind::Call` (`const_eval_select`, `is_val_statically_known`) fails closed.
  - Furthermore, `trusted/audit/TrustedBoundary.lean` (L92–95, L1605–1665) bans `sorryAx`, `Lean.ofReduceBool` / `Lean.ofReduceNat` (`native_decide`), `Lean.trustCompiler`, and `unsafe`/`partial` definitions—all of which `CtfeAndConstEvalSelectSoundness.lean` satisfies (`[propext]`-only, `0` `partial`/`unsafe`/`._unsafe_rec`). Extending Anneal's extractor or evaluator to fold post-monomorphization `Const::Unevaluated` constants or verify `libcore` functions containing `const_eval_select` / `is_val_statically_known` must enforce `InternValidFreeze`, `CesRelationalContract` (or contextual `HelperInv`), and `IvskOracleInvariant` at every lowered site.

### 9. Analytical dimensions scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

`Basis: execution + derived`

| ID | Dimension | Basis | Result |
| :--- | :--- | :--- | :--- |
| `L1` | Authoring and proof velocity | execution (artifact size only) | Wall-clock authoring duration: **not measured**. Artifact size (`support/CtfeAndConstEvalSelectSoundness.lean`): `1,668` lines, `76,432` bytes, `24` `theorem`, `34` `def`/`abbrev`, `14` `inductive`/`structure` declarations. |
| `L2` | Toolchain / TCB build time | none | **not measured** (pre-installed released `Lean v4.34.1` and `rustc 1.98.0-nightly` binaries used; `0` external Lean package dependencies beyond `Init`). |
| `L3` | Pass / certificate synthesis latency | execution (probe wall time only) | Full 21-check `rustc` + Miri + 2,472-file sysroot census driver (`support/probe_ctfe_and_const_eval_select.py`) completes end-to-end in `~13 s` wall clock. Per-constant certificate synthesis from live MIR dumps: **not implemented**. |
| `L4` | Generated code performance | execution (static IR + functional checks) | Runtime throughput microbenchmarks: **not measured**. Static IR verified on `x86_64-unknown-linux-gnu`: `remap_mir_for_const_eval_select(NotConst)` eliminates `const_eval_select` wrapper overhead completely before codegen (even at `-O0`); `-O3` folds `@llvm.is.constant.i64` to constant `true` after inlining (`0` residual `@llvm.is.constant` calls in `-O3` LLVM IR) and folds `const { 6 * 7 } + 9` to `const 51_u64` in `MIR GVN`. |
| `L5` | Checking latency and throughput | execution | Synchronous single-threaded `Lean v4.34.1` kernel verification (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`): `6.9807 s` wall clock (`support/lean_check_receipt.json`). Crate-scale translation validation throughput: **not measured**. |
| `L6` | RAM and artifact footprint | execution | Peak resident set size (`ru_maxrss`): `590,936 KiB` (`~577 MiB`) for synchronous Lean kernel verification; zero `.olean` or compiled binary artifacts retained in the published package. |
| `C1` | Specification and assumption auditability | execution (kernel environment audit) | `0` imports beyond `Init`; transitive axiom footprint across all `10` major theorems: `[propext]` only (`static_unsafecell_interned_writable` uses `0` axioms); across all `568` `CtfeAndConstEvalSelectSoundness.*` kernel constants: `0` `sorryAx`, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, `0` `.isUnsafe`, `0` `.isPartial`, `0` `._unsafe_rec` helpers, `0` user `axiom`/`opaque` declarations. |
| `C2` | Orthogonality and simplicity | derived | Single `Nat.repeat` step functor architecture (`ctfeEvalStep` / `rtEvalStep`) and `List.foldr` / `List.set` heap primitives avoid all equation-compiler well-founded/`_unsafe_rec` machinery while keeping concrete counterexample reductions definitional (`rfl`). |
| `V1` | Adequacy, mutation and non-vacuity | execution (Lean kernel + live `rustc`/Miri) | `21 / 21` live `rustc` and Miri checks pass across 6 Rust specimens (MIR dialects, `MIR GVN`, LLVM IR mutability & `@llvm.is.constant`, negative CTFE/PME diagnostics, Miri seed-0/seed-1 PRNG & read-only UB). Lean proves non-vacuous `ValidLayout` witnesses (`witnessHeap_validLayout`, `const_memory_guaranteed_eq_indeterminate_necessary`) plus 3 concrete sharpness counterexamples (`CE1`, `CE2`, `CE3`) falsifying confluence/refinement/memory safety when each hypothesis is dropped. |
| `V2` | Differential fuzzing | none | **not measured**: correspondence between `ctfeEval`/`rtEval` and `rustc`/Miri was tested on 6 targeted Rust specimens (`21` checks), not via randomized MIR fuzzing. |
| `V3` | Weak memory / crash / silicon | derived | **known not to apply** to pure single-threaded compile-time evaluation (`CompileTimeMachine` forbids threads and I/O). Concurrent runtime mutation of `!Freeze` `Sync` `static`s (`INTERIOR_MUT_STATIC` in writable `.data`) under C++20/LLVM weak memory models is **not examined**. |
| `V4` | Held-out ecosystem replay | execution (sysroot census only) | Exhaustive programmatic census executed across all `2,472` non-test `.rs` files in the `rust-lang/rust` standard library (`core`, `alloc`, `std`, `proc_macro`, `stdarch`, classifying all `32` `const_eval_select` and `7`/`11` `is_val_statically_known` sites). External crates.io crates: **not examined**. |

## Boundaries

**Not examined.**

- **Experimental `const_heap` (`intrinsics::const_allocate` / `const_deallocate`):** The 4 Class E sites in `alloc/src/alloc.rs` (L332–379) were cataloged in the sysroot census, and `intern_const_alloc_recursive` (`intern.rs` L280–310) converts surviving heap allocations into static memory, but transient compile-time heap deallocation and dangling-heap-pointer diagnostics were not probed or modeled in Lean.
- **Sub-slot byte-level provenance splitting and union partial overwrites:** `CtfeAndConstEvalSelectSoundness.lean` models memory as typed `Slot` cells rather than raw byte arrays with sub-pointer `ProvenanceMap` fragments; partial byte overwrites of a pointer in a `union` (which strip provenance in `memory.rs` and trigger `ReadPointerAsInt` on subsequent pointer-typed or integer-typed loads depending on layout) were not modeled at sub-slot granularity.
- **Stacked Borrows / Tree Borrows aliasing tags:** Runtime Miri tracks borrow-stack tags (`Retag`), whereas `CompileTimeMachine` ignores aliasing tags beyond `&`/`&mut` mutability flags in `CtfeProvenance` and two-step `RefTracking` validation. Borrow-tag refinement between Miri and LLVM `noalias` is outside this package's scope.
- **Type-level `feature(generic_const_exprs)` (`Const::Unevaluated` inside `Ty`):** Specimen 1 and Specimen 5 exercised stable const generics (`const N: usize`), associated constants (`T::LIMIT`, `T::CHECK`), and `const { ... }` expressions; incomplete `generic_const_exprs` normalization is not examined.
- **Non-LLVM codegen backends (`rustc_codegen_cranelift`, `rustc_codegen_gcc`):** Whether non-LLVM backends lower `is_val_statically_known` to constant `false` unconditionally (never folding to `true` even at `-O3`) was not executed.

**Unknown.**

- Whether any future LLVM pass at `-O3` / ThinLTO can fold `@llvm.is.constant` to `true` across indirect memory loads after SROA promotes an aggregate local, or whether `rustc_codegen_llvm`'s `OperandValue::Immediate` guard permanently prevents all aggregate `is_val_statically_known` calls from ever returning `true`.

**Known not to apply.**

- **Point-wise call-site equality `f_ct(args) = f_rt(args)` does NOT hold across `libcore`'s `const_eval_select` sites:** Falsified directly by `library/core/src/str/validations.rs:136` (`usize::MAX` vs. `align_offset`), `library/core/src/ptr/const_ptr.rs:26` (partial `guaranteed_eq` panic vs. total `ptr.addr() == 0`), and the 11 Class B UB/precondition guards (`true` in `const` vs. alignment/bounds checks at runtime). Verification tools must support precondition-guarded refinement (`CesRelationalContract`) and contextual helper invariants (`constEvalSelect_contextual_helper_sound`).
- **`Const::Unevaluated` inside `if false` is NOT dead-code-eliminated before constant evaluation:** Falsified at both `-O0` and `-O3` by Specimen 5 (`case_pme_dead_branch` and `case_inline_const_dead_branch`, both failing with `E0080`). Any `const { ... }` block or monomorphized generic function's `required_consts` / `mentioned_items` must evaluate without error regardless of runtime branch reachability.
- **`ptr::guaranteed_eq` does NOT return `Some(true)` on identical `const` slice allocations:** Falsified by Specimen 2 (`CONST_MEM_EQ=None`) and `const_eval/machine.rs` L361–384.

**Unsupported.**

- `core::intrinsics::const_eval_select` and `core::intrinsics::is_val_statically_known` are permanently internal nightly intrinsics (`#![feature(core_intrinsics, const_eval_select)]`) intended exclusively for standard-library authoring.
- Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) currently rejects `Const::Unevaluated`, `Const::Ty`, non-scalar constants, and `TerminatorKind::Call` intrinsics fail-closed at the `Trusted.MirAst` boundary.

**Stronger conclusions the evidence does not establish.**

- *"`rustc`'s `CompileTimeMachine` and `libcore`'s 32 `const_eval_select` sites are formally verified."* False: the Lean proof verifies the abstract dual-mode operational model (`CtfeAndConstEvalSelectSoundness`), not the Rust implementation in `compiler/rustc_const_eval` or the concrete SIMD/pointer implementations in `library/core`.
- *"`const_eval_select` is memory-safe whenever both arms are safe Rust functions."* False with respect to downstream `unsafe` consumers: because `const_eval_select` is a **safe** `const fn`, safe code (under `#![feature(const_eval_select)]`) can violate `CesRelationalContract` (`CE1`), causing a `const`-validated invariant checked at compile time to disagree with the value produced at runtime.

## Evidence

**Primary upstream source (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, committed `2026-05-31`, matching `rustc -vV`; all 40 pinned files across 6 commits verified in `support/pin_receipt.json` on `2026-11-21`):**

| Path | Lines | Content |
| :--- | :--- | :--- |
| `compiler/rustc_middle/src/mir/interpret/pointer.rs` | 91–191 | `CtfeProvenance` bit-packed `(AllocId, immutable, shared_ref)`, `OFFSET_IS_ADDR = false`, `WILDCARD = None` |
| `compiler/rustc_middle/src/mir/consts.rs` | 224–285 | `mir::Const::{Ty, Unevaluated, Val}` and `is_required_const` |
| `compiler/rustc_const_eval/src/interpret/eval_context.rs` | 27–49 | `InterpCx<'tcx, M>` core interpreter state |
| `compiler/rustc_const_eval/src/interpret/step.rs` | 138–165 | `StatementKind::ConstEvalCounter` stepping and `eval_rvalue_into_place` |
| `compiler/rustc_const_eval/src/interpret/place.rs` | 100–130, 466–510 | `MPlaceTy<CtfeProvenance>` and `deref_pointer` alignment/bounds checks |
| `compiler/rustc_const_eval/src/interpret/memory.rs` | 481–550, 1401–1420 | `check_ptr_access_signed` and `get_bytes_strip_provenance` (`ReadPointerAsInt`) |
| `compiler/rustc_const_eval/src/interpret/operator.rs` | 311–344 | Provenance-preserving `BinOp::Offset` prior to `M::binary_ptr_op` fallback |
| `compiler/rustc_const_eval/src/interpret/validity.rs` | 265–287, 520–565, 780–868, 1314–1396 | `CtfeValidationMode`, `ReadPointerAsInt`, `RefTracking` traversal, and non-ZST `UnsafeCell` rejection (`L1383–1394`) |
| `compiler/rustc_const_eval/src/interpret/intern.rs` | 203–356 | `InternKind` and `intern_const_alloc_recursive` `(base_mutability, inner_mutability)` assignment (`L214–240`) |
| `compiler/rustc_const_eval/src/const_eval/machine.rs` | 33–39, 184–200, 278–387, 410–412, 548, 781–797, 817–868, 985 | `LINT_TERMINATOR_LIMIT`, `CompileTimeMachine`, 3-valued `ptr_guaranteed_cmp`, deferred `enforce_validity`, `is_val_statically_known -> false`, `runtime_checks -> true`, `binary_ptr_op`, `expose_provenance`, 0-byte write carve-out |
| `compiler/rustc_const_eval/src/const_eval/eval_queries.rs` | 119–165, 432–460 | `eval_to_allocation_raw_provider`, `const_validate_mplace`, `allow_immutable_unsafe_cell: !inner` |
| `compiler/rustc_const_eval/src/const_eval/dummy_machine.rs` | 1–120 | `DummyMachine` used by `MIR GVN` constant evaluation |
| `compiler/rustc_mir_transform/src/lib.rs` | 237–307, 465, 507–509, 799 | `remap_mir_for_const_eval_select`, `RequiredConstsVisitor`, `inner_mir_for_ctfe`, `inner_optimized_mir` |
| `compiler/rustc_mir_transform/src/ctfe_limit.rs` | 18–55 | `CtfeLimit` pass injecting `StatementKind::ConstEvalCounter` |
| `compiler/rustc_mir_transform/src/promote_consts.rs` | 243–246, 402–520, 660–682 | Implicit promotion `Validator`, `&mut []` zero-length carve-out (`L411–419`), `HasMutInterior`, `#[rustc_promotable]` vs. `promotion_safe_blocks` |
| `compiler/rustc_mir_transform/src/gvn.rs` | 426, 604–606, 682, 1794–1958 | `VnOpaque` on `Const::Unevaluated`, `DummyMachine` folding, `may_have_provenance` rejection (`L1816–1827, L1953–1955`) |
| `compiler/rustc_mir_transform/src/instsimplify.rs` | 461–471 | `SimplifyUbCheck` runtime folding to `tcx.sess.ub_checks()` |
| `compiler/rustc_monomorphize/src/collector.rs` | 705–723, 1349–1362 | `required_consts` and `mentioned_items` PME evaluation on monomorphized functions |
| `compiler/rustc_codegen_llvm/src/intrinsic.rs` | 246–256 | `OperandValue::Immediate` `@llvm.is.constant` emission vs. non-immediate `const_bool(false)` |
| `library/core/src/intrinsics/mod.rs` | 2401–2467, 2541–2543 | `const_eval_select`, `const_eval_select!`, and `is_val_statically_known` definitions |
| `library/core/src/str/validations.rs` | 136–236 | `usize::MAX` vs. `align_offset(USIZE_BYTES)` inside `run_utf8_validation` |
| `library/core/src/ptr/const_ptr.rs` | 26–44, 357, 707, 837, 943 | `is_null` (`guaranteed_eq` vs. `addr() == 0`) and Class B pointer precondition guards |
| `library/core/src/ub_checks.rs` | 98, 136, 166 | Class B `check_language_ub`, `is_aligned_and_not_null`, `is_nonoverlapping` guards |
| `src/tools/miri/src/intrinsics/mod.rs` | 167–178 | Miri runtime PRNG coin-flip (`this.machine.rng.get_mut().random()`) for `is_val_statically_known` |

**Comparison & specification sources:**
- `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`): `library/core/src/intrinsics/mod.rs`, `library/core/src/num/{int_macros,uint_macros}.rs`.
- `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`): `compiler/rustc_const_eval/src/const_eval/machine.rs`, `compiler/rustc_const_eval/src/interpret/{intern,validity}.rs`, `compiler/rustc_mir_transform/src/{promote_consts,gvn}.rs`.
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`: `src/const_eval.md`, `src/items/{constant-items,static-items}.md`, `src/destructors.md`.
- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/Trusted/MirAst.lean` (`L504–565, L657–666, L785–796`), `trusted/lean/Trusted/MirSemantics.lean` (`L883–955, L1693`), `trusted/audit/TrustedBoundary.lean` (`L92–95, L1605–1665`).

**Preserved package artifacts (all generated and verified on `2026-11-21` on `x86_64-unknown-linux-gnu`):**

| File | Description & SHA-256 |
| :--- | :--- |
| `support/specimens/mir_const_forms_and_promotion.rs` | Specimen 1: `const`, `const fn` loops (`ConstEvalCounter`), `promoted[0..1]` (`&[10,20,30]` & `&mut []`), unpromoted dead `&(1/0)`, generic `T::LIMIT` & `const { ... }`, `const_eval_select` (sha256 `ceec62b9ada4818ba09c3c25b708b1cbbcb4df69c7013bc694bad8f9cb4686f6`) |
| `support/specimens/gvn_ctfe_boundary_and_statically_known.rs` | Specimen 2: `guaranteed_eq` (`Static` vs. `Memory`), `MIR GVN` scalar folding vs. `PointerExposeProvenance`, `is_val_statically_known` (`-O0` vs. `-O3` vs. CTFE vs. `[u64; 4]`) (sha256 `6b44df7dd3063b52d9ad295951fa90a9e4b28516a89f88c80fad1dfef215528b`) |
| `support/specimens/unsafecell_interning_and_rodata.rs` | Specimen 3: `FROZEN_STATIC` (`constant`) vs. `INTERIOR_MUT_STATIC` (`global`), per-use `const Cell<u64>`, `&[Cell<u32>] = &[]` & ZST `&Cell<()>` (sha256 `95ef8838fb40147409b03ebec52242802f7e05c96a583fd05efedb9d1f3d2e38`) |
| `support/specimens/divergent_const_eval_select_and_ivsk_hazards.rs` | Specimen 4: Unsound `const_eval_select` (`CE1_CT=0` vs. `CE1_RT=1`) and non-invariant `is_val_statically_known` (`200` at `-O0` vs. `100` at `-O3`) (sha256 `d5bdcebd51e75ff904e1d6dd0218a70267156365266b9aa5a559b5485423d7c8`) |
| `support/specimens/negative_ctfe_and_pme_cases.rs` | Specimen 5: 7 `--cfg` negative CTFE and dead-branch PME (`E0080`) compile-fail checks (sha256 `faa73f81f227b779f974746971f4d03ead0ad1bee6d933e17b5396003c4a42be`) |
| `support/specimens/miri_standalone_runtime_vs_ctfe.rs` | Specimen 6: `#![no_core]` Miri specimen testing permissive ptr-to-int, `-Zmiri-seed=0/1` `is_val_statically_known` PRNG, `-Zmiri-strict-provenance`, and `case_rodata_write_ub` (sha256 `9839a9003f0af328535d55ed65a06094f6504c58506e14888a0e26b070a751ea`) |
| `support/probe_ctfe_and_const_eval_select.py` | Python 3.10+ stdlib-only probe driver executing all 21 compiler/Miri/sysroot checks (sha256 `2993607cf2e54ff874cdf89aa2f3be1d94ee230992673ad75ac56afa6c0c3346`) |
| `support/probe_output/{probe_results.json,probe_summary.md,mir_excerpts.txt,llvm_ir_excerpts.txt,sysroot_const_eval_census.json}` | Verbatim live check results (`21 / 21` passed), sanitized MIR/LLVM-IR dumps, and complete 32-site + 7-site sysroot JSON census |
| `support/CtfeAndConstEvalSelectSoundness.lean` | Standalone Lean `v4.34.1` refinement mechanization and `CE1`–`CE3` counterexamples (sha256 `b22b63585333eee33ea63bbbb31ad39cf6690fd89cea3bd7916974ad176b3d6d`) |
| `support/check_lean.py`, `support/lean_check_receipt.json` | Synchronous Lean kernel + `env.constants` hygiene verifier and receipt (`all_checks_passed: true`, `[propext]`, `0` `partial`/`unsafe`/`._unsafe_rec`; driver sha256 `adc5bb4a70d0270efd9522c65b90efaf86551cf1600e3ea9d20d7bb2f3944b78`) |
| `support/verify_pins.py`, `support/pin_receipt.json` | Live GitHub pin verifier and receipt (`40 / 40` files verified across `6` commits; driver sha256 `862c4700f7b42930026fba7d11b6a2d94eabf5c248e374634ca58266118c8b30`) |

**Peer-reviewed literature** (foundational context for Miri, Rust pointer provenance, and constant-folding refinement):

- R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." POPL 2018 (PACMPL 2, Article 66). doi:10.1145/3158154. Semantic type soundness and `UnsafeCell` interior-mutability model underlying Rust's `Freeze` invariant.
- R. Jung, H.-H. Dang, J. Kang, D. Dreyer. "Stacked Borrows: An Aliasing Model for Rust." POPL 2020 (PACMPL 4, Article 41). doi:10.1145/3371109. Operational memory and provenance semantics implemented in Miri's `InterpCx`.
- K. Memarian, V. B. F. Gomes, B. Davis, S. Kell, A. Richardson, R. N. M. Watson, P. Sewell. "Exploring C Semantics and Pointer Provenance." POPL 2019 (PACMPL 3, Article 67). doi:10.1145/3290380. Formal PNVI-ae-udi provenance model motivating Rust's `expose_provenance` / `with_exposed_provenance` split vs. symbolic CTFE provenance.
- J. Kang, C.-K. Hur, W. Mansky, D. Garbuzov, S. Zdancewic, V. Vafeiadis. "A Formal C Memory Model Supporting Integer-Pointer Casts." PLDI 2015, pp. 326–335. doi:10.1145/2737924.2737965. Twin-allocation / symbolic-to-concrete placement model related to `ValidLayout` concretization of `AllocId × Offset` pointers.

## Revalidation

**Fastest discriminating checks, in execution order.**

1. *Verify toolchain revision:* `rustc -vV` must report `commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. When evaluating a newer `rustc` commit, diff `compiler/rustc_const_eval/src/const_eval/{machine,eval_queries}.rs`, `compiler/rustc_const_eval/src/interpret/{intern,validity}.rs`, `compiler/rustc_mir_transform/src/{lib,promote_consts,gvn}.rs`, `compiler/rustc_codegen_llvm/src/intrinsic.rs`, and `library/core/src/intrinsics/mod.rs`.
2. *Rerun the 21-check empirical `rustc`, Miri, and sysroot census probe* (`~13 s`; Python 3.10+ stdlib and nightly `rustc` + `rust-src`):
   ```console
   python3 support/probe_ctfe_and_const_eval_select.py --out /tmp/ctfe_probe_out
   ```
   Exits `0` iff all 21 checks pass (`s1` MIR lowering & promotion, `s2` `guaranteed_eq` / `MIR GVN` / `@llvm.is.constant` `-O0` vs. `-O3`, `s3` `Freeze` vs. `!Freeze` LLVM globals & ZST `Cell`, `s4` `CE1` & `CE3` divergence, `s5` negative CTFE & dead-branch PMEs, `s6` Miri PRNG seeds & read-only UB, and `census` sysroot scan). Note that check `census::sysroot_const_eval_select_32_sites_and_ivsk_sites_classified` asserts the exact `32`-site count of `1.98.0`/`1.99.1`; if upstream `library/` adds or removes `const_eval_select` sites, inspect `/tmp/ctfe_probe_out/sysroot_const_eval_census.json` to classify the delta.
3. *Recheck the Lean `v4.34.1` kernel proof and environment hygiene* (`~7 s` for kernel check, `~13 s` total with environment audit; requires `Lean v4.34.1` on `PATH`):
   ```console
   python3 support/check_lean.py
   ```
   Verifies `0` banned source tokens, runs `lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/CtfeAndConstEvalSelectSoundness.lean`, and walks `env.constants` in a temporary directory to confirm `[propext]`-only axioms and `0` `partial`/`unsafe`/`._unsafe_rec` constants.
4. *Reverify upstream commit and file pins* (`~12 s`; requires `curl` and GitHub access):
   ```console
   python3 support/verify_pins.py --out /tmp/pin_receipt.json
   ```
5. *Check Anneal MIR constant ingestion drift:* inspect `inductive ConstLit`, `inductive StatementKind`, and `inductive TerminatorKind` in `trusted/lean/Trusted/MirAst.lean` at the target `joshlf/anneal` revision; if `Const::Unevaluated` or intrinsic call lowering is added, verify that it enforces `InternValidFreeze`, `CesRelationalContract`, and `IvskOracleInvariant`.

**When manual re-investigation is required.** If `rustc` stabilizes `const_heap` deallocation, replaces `remap_mir_for_const_eval_select` with interpreter-level intrinsic dispatch, or extends `rustc_codegen_llvm` to emit `@llvm.is.constant` for `OperandValue::Pair` / `OperandValue::Ref`, Findings 3–4 and Section 4 of `CtfeAndConstEvalSelectSoundness.lean` must be updated against new MIR and LLVM IR dumps.
