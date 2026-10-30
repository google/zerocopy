<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Rustc Post-Monomorphization Errors (PMEs), Dead-Branch vs. Post-Divergence Lowering, and MIR Capture Representation

## Summary

A Rust crate that passes type checking and borrow checking can still fail to
compile during monomorphization collection or backend code generation. These
failures—**Post-Monomorphization Errors (PMEs)**—make `rustc`'s lowering from
polymorphic MIR to target machine code a partial function over type and
const-generic substitutions $\sigma$.

This report establishes the primary-source taxonomy of PMEs in `rustc` across
two pinned compiler revisions (`58cf8f9c35b355199727627d07ae34a4e2846d67`,
`rustc 1.99.1`, and `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `rustc
1.98.0-nightly 2026-05-30`), resolves the exact MIR lowering difference between
dead conditional branches (`if false`, `match false`) and statements after
unconditional divergence (`return`, `break`, `continue`, `loop {}`), and
documents how PMEs appear in `Runtime(PostCleanup)` MIR
(`tcx.mir_drops_elaborated_and_const_checked`) versus textual `--emit=mir`
output (`tcx.optimized_mir`):

1. **Six-Category PME Taxonomy:** Every PME in `rustc` arises from one of six
   mechanisms:
   - **(1a)** inline `const { ... }` blocks (`DefKind::InlineConst`) recorded in
     `body.required_consts` and evaluated by `MirUsedCollector::eval_constant`
     during `collect_items_of_instance` (whereas reachable concrete `const`
     blocks are caught pre-monomorphization by `KnownPanicsLint` during
     `analysis(())`);
   - **(1b)** associated constants (`DefKind::AssocConst`) in `let _ = ...`,
     value bindings, operands, and `zerocopy`'s `static_assert!` macro
     (`const_assert!(<... as StaticAssert>::ASSERT)`);
   - **(1c)** dead-branch compile-time function evaluation (CTFE) and mentioned
     items (`if false { const { ... } }` in `body.required_consts` and `if false
     { callee::<T>(); }` in `body.mentioned_items`, evaluated in
     `CollectionMode::MentionedItems`);
   - **(1d)** demand-driven `LayoutError` queries (`SizeOverflow`, `InvalidSimd`
     for `ZeroLength` or `TooManyLanes`, `NormalizationFailure`, `Unknown`,
     `ReferencesError`, plus immediate `emit_fatal` on `NonPrimitiveSimdType`);
   - **(1e)** monomorphization recursion depth (`check_recursion_limit`) and
     post-monomorphization alias normalization failure
     (`check_normalization_error` -> `NormalizationErrorInMono`), contrasted
     with PME suppression via `ImpossibleClauses` (`ImpossiblePredicates`) and
     `MonoItem::is_instantiable`; and
   - **(1f)** target-feature ABI checks (`check_feature_dependent_abi`),
     SIMD/scalar intrinsic `InvalidMonomorphization` (`E0511`), validity
     requirement intrinsics (`assert_inhabited`, `assert_zero_valid`,
     `assert_mem_uninitialized_valid`), and `InlineAsm` operands/registers.
2. **Dead Conditional Branches vs. Unconditional Divergence:** In
   `rustc_mir_build`, every conditional branch (`if false`, `match false`,
   `if (const { false })`, `let b = false; if b`) lowers to a
   `TerminatorKind::SwitchInt` whose dead arm has predecessor `bb0`. By
   contrast, unconditional divergence (`return`, `break`, `continue`, and
   `loop {}` without `break`) terminates the active block and calls
   `self.cfg.start_new_block()`, placing subsequent lexical statements into a
   basic block with **zero incoming CFG edges**. `SimplifyCfg::Initial` deletes
   zero-predecessor blocks at the end of `mir_built` (before `mir_promoted`),
   whereas `SimplifyCfg` never folds `switchInt(const false)`. Constant
   `SwitchInt` folding is performed only by `SimplifyConstCondition` at
   `-Z mir-opt-level >= 1` inside `inner_optimized_mir`, *after*
   `RequiredConstsVisitor` (`mir_promoted`) and `MentionedItems` (start of
   `inner_optimized_mir`) have already recorded the dead branch's PME
   obligations. Consequently, the basic blocks present in `Runtime(PostCleanup)`
   MIR (`tcx.mir_drops_elaborated_and_const_checked`) are **identical** to the
   basic blocks visited by `RequiredConstsVisitor` and `MentionedItems`.
3. **Textual `--emit=mir` vs. In-Process `rustc_driver` Capture:** Textual
   `--emit=mir` (`write_mir_fn`) never serializes `body.required_consts` or
   `body.mentioned_items` and defaults to `-Z mir-opt-level=1`
   (`Runtime(Optimized)`), where `RemoveZsts`, `SimplifyLocals`, and
   `SimplifyConstCondition` erase dead `const { ... }`, `let _ = Assoc::CONST;`,
   and `if false { callee::<T>(); }` statements from `body.basic_blocks`. In
   addition, `OutputType::Mir` sets `OutputTypes::should_codegen() == true`, so
   `rustc --emit=mir,metadata` runs `collect_and_partition_mono_items` on
   monomorphic roots after writing the `.mir` file. An in-process `rustc_driver`
   extractor ([pme_capture_probe/driver.rs](pme_capture_probe/driver.rs))
   recovers exact `Runtime(PostCleanup)` MIR and PME obligations provided it
   respects four `TyCtxt` invariants: borrowing
   `mir_drops_elaborated_and_const_checked` before `optimized_mir` steals it;
   reading dead-branch calls directly from `PostCleanup` basic blocks (or
   `optimized_mir.mentioned_items()`); resolving trait associated constants
   (`StaticAssert::ASSERT`) via `ty::Instance::try_resolve` before querying
   `tcx.mir_for_ctfe`; and linking `InlineConst` bodies strictly from
   `required_consts()` rather than from `tcx.mir_keys(())` (which retains orphan
   post-`return` `InlineConst` items).

## Applicability

The findings in this report apply to the following subjects and their
interactions:

- **Rust compiler (`rust-lang/rust` at
  `58cf8f9c35b355199727627d07ae34a4e2846d67`, `rustc 1.99.1`, and
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `rustc 1.98.0-nightly
  2026-05-30`):** Primary subject for MIR construction (`rustc_mir_build`), MIR
  pass ordering and constant/item collection (`rustc_mir_transform`),
  monomorphization collection and ABI/move checks (`rustc_monomorphize`), CTFE
  execution (`rustc_const_eval`), layout calculation (`rustc_middle`,
  `rustc_ty_utils`), and SSA/LLVM backend codegen (`rustc_codegen_ssa`,
  `rustc_codegen_llvm`). All six PME categories and 16 branch-versus-divergence
  probes were executed on `x86_64-unknown-linux-gnu`. Where symbol names or line
  numbers differ between `58cf8f9c3` and `f8a08b688` (notably the rename of
  `ImpossiblePredicates` to `ImpossibleClauses` and `errors.rs` to
  `diagnostics.rs`), both coordinates are recorded.
- **The Rust Reference (`rust-lang/reference` at
  `82da570bafd9efed421bdbae0f8603ede8dd308b`):** Normative baseline for inline
  `const` block evaluation and dead-branch versus unreachable CTFE behavior,
  interpreted alongside `rustc`'s actual CFG reachability implementation in
  `rustc_mir_build` and `rustc_mir_transform`.
- **`zerocopy` (`google/zerocopy` at
  `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`):** Target crate whose
  `static_assert!` and `const_assert!` macros (`zerocopy/src/util/macros.rs`,
  lines 655–685) encode compile-time layout and alignment preconditions via a
  local `trait StaticAssert { const ASSERT: bool; }` implementation on
  `PhantomData` tuples.
- **Anneal verification framework (`joshlf/anneal` at
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):** Consumer of captured MIR via
  `anneal-rustc-capture` (`trusted/rustc-capture/src/lib.rs`). The report
  evaluates how `anneal-rustc-capture`'s subprocess `--emit=mir` pipeline and a
  replacement in-process `rustc_driver` callback interact with `rustc`'s PME
  machinery.

## Findings

### 1. Six-Category Taxonomy of PMEs in `rustc`

`Basis: normative + source + execution`

The table below classifies every Post-Monomorphization Error mechanism in
`rustc` across commits `58cf8f9c35b355199727627d07ae34a4e2846d67` and
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, identifying the compiler phase, the
implementation location, the representation in `rustc_middle::mir::Body`, and
the emitted diagnostic or runtime behavior.

| Category | Sub-mechanism | Compiler Phase & Query | Source Location (`58cf8f9c3` / `f8a08b688`) | Representation in `mir::Body` | Diagnostic / Failure Mode |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1(a) Inline `const { ... }` blocks** | Generic or dead-branch inline `const` block fails CTFE (`panic!`, `assert!`, arithmetic overflow, UB) | Monomorphization collection (`collect_items_rec` -> `collect_items_of_instance` -> `eval_constant` -> `Const::eval`) | `compiler/rustc_monomorphize/src/collector.rs:711-729, 1374-1378` (`58cf8f9c3`) / `:703-721, 1364-1368` (`f8a08b688`) | `body.required_consts` (`Const::Unevaluated` of `DefKind::InlineConst`); erased from `basic_blocks` at `mir-opt-level >= 1` if ZST/unused | `error[E0080]: evaluation panicked: ...` (or CTFE error); `ErrorHandled::Reported` |
| **1(a') Concrete reachable `const { ... }`** | Concrete inline `const` block in reachable code fails CTFE | Analysis (`mir_drops_elaborated_and_const_checked` -> `KnownPanicsLint`) | `compiler/rustc_mir_transform/src/known_panics_lint.rs:190-220`; `rustc_interface/src/passes.rs:1180, 1213-1215` | `body.basic_blocks` (`Assign` / operand) & `body.required_consts` | Pre-mono `error[E0080]` during `analysis(())`; aborts before `--emit=mir` |
| **1(b) Associated constants & `static_assert!`** | `<T as Trait>::CONST` or `Struct::<T>::CONST` fails CTFE when referenced in `let _ = ...`, `let x = ...`, operand, or `assert!(...)` | Monomorphization collection (`collect_items_of_instance` -> `eval_constant` -> `tcx.const_eval_resolve`) | `compiler/rustc_mir_build/src/builder/expr/as_constant.rs:72-97`; `rustc_monomorphize/src/collector.rs:711-729, 1374-1378` | `body.required_consts` (`Const::Unevaluated` of `DefKind::AssocConst`). In `basic_blocks`: erased for `let _ = ...` at `opt-level=1`; retained in `SwitchInt` for `zerocopy`'s `static_assert!` | `error[E0080]: evaluation panicked: ...` + `note: erroneous constant encountered` |
| **1(c) Dead-branch CTFE (`R-CTFE-02`)** | `if false { const { ... } }`, `if false { let _ = T::C; }`, or `if false { callee::<T>(); }` | `mir_promoted` (`RequiredConstsVisitor`) & `inner_optimized_mir` (`MentionedItems`) -> `collect_items_rec` | `compiler/rustc_mir_transform/src/required_consts.rs:9-23`; `mentioned_items.rs:18-120`; `collector.rs:609-618, 1374-1387` | `body.required_consts` (direct) or `body.mentioned_items` (`MentionedItem::Fn` / `Drop` / `UnsizeCast` / `Closure`); erased from `basic_blocks` at `opt-level=1` | **Fails with `error[E0080]`** on monomorphization. By contrast, code after `return;` is deleted by `SimplifyCfg::Initial` and **succeeds** |
| **1(d) Type layout errors (`LayoutError`)** | `SizeOverflow`, `InvalidSimd` (`ZeroLength`, `TooManyLanes`), `NormalizationFailure`, `Unknown`, `ReferencesError` | `mono_checks::move_check` (`collector.rs:1338`), CTFE (`size_of`/`align_of`), or SSA codegen (`fn_abi_of_instance`, `allocate_local`, `codegen_place`, `codegen_rvalue`) | `compiler/rustc_middle/src/ty/layout.rs:58-106, 288-357`; `rustc_ty_utils/src/layout.rs:93-169` | Local declarations (`body.local_decls`), call/return types, or place projections in `body.basic_blocks` (or `size_of` call) | Fatal `SpannedWithLayoutError` (or `error[E0080]` if first queried inside CTFE `SizedTypeProperties::SIZE`) |
| **1(d') Non-primitive SIMD element** | `#[repr(simd)] struct S<T>([T; N])` instantiated with non-scalar `T` (e.g., `()`) | `layout_of_uncached` -> `map_error` -> `LayoutCalculatorError::NonPrimitiveSimdType` | `compiler/rustc_ty_utils/src/layout.rs:162-166` | Any query of `tcx.layout_of(Simd<T>)` during `analysis` or codegen | Immediate `emit_fatal`: `monomorphising SIMD type ... with a non-primitive-scalar ... element type` |
| **1(e) Monomorphization recursion & normalization** | Polymorphic recursion depth $> \text{recursion\_limit}$ (`check_recursion_limit`) or `NormalizationErrorInMono` (`check_normalization_error`) | Monomorphization collection (`collect_items_rec`) | `compiler/rustc_monomorphize/src/collector.rs:479-485, 626-685, 1337` | Recursive generic `Call` / `Drop` in `body.basic_blocks` or unnormalizable type in `body` | Immediate `emit_fatal(RecursionLimit)`: `reached the recursion limit while instantiating ...` |
| **1(e') Impossible clauses / predicates** | Trivial or instantiated impossible clauses (`where u32: Impossible`, `dyn Trait` vtable with impossible principal) | `Analysis(PostCleanup)` (`ImpossibleClauses`) and monomorphization root/vtable filtering (`is_instantiable`) | `compiler/rustc_mir_transform/src/impossible_clauses.rs:68-115` (`impossible_predicates.rs` in `f8a08b688`); `rustc_middle/src/mono.rs:272-282` | `ImpossibleClauses` replaces `body.basic_blocks` with `bb0: { unreachable; }`; `is_instantiable` skips collection | **Suppresses PMEs**: item is replaced with `unreachable` and skipped during monomorphization |
| **1(f.1) Target-feature & ABI checks** | Unsized non-rustic parameter, unsupported/disabled SIMD vector ABI (`AvxVec` without `+avx`), `vectorcall` without `+sse2` | Monomorphization collection (`check_mono_item` -> `abi_check::check_feature_dependent_abi`) and `FnAbiOfHelpers` | `compiler/rustc_monomorphize/src/mono_checks/abi_check.rs:51-265`; `rustc_middle/src/ty/layout.rs:365-432` | Function signature (`local_decls[0..=arg_count]`) or `TerminatorKind::Call` in `body.basic_blocks` | `AbiErrorDisabledVectorType`, `AbiErrorUnsupportedVectorType`, `AbiErrorUnsupportedUnsizedParameter`, `AbiRequiredTargetFeature`, or `FnAbiError` |
| **1(f.2) SIMD & scalar intrinsic PMEs** | `core::intrinsics::simd::*` or `float_to_int_unchecked` / atomic intrinsics instantiated with invalid types or mismatched lane counts | SSA / LLVM intrinsic codegen (`codegen_intrinsic_call`) | `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:90-370`; `rustc_codegen_llvm/src/intrinsic.rs`; `diagnostics.rs:723-980` (`errors.rs:714` in `f8a08b688`) | `TerminatorKind::Call` to intrinsic in `body.basic_blocks` | `error[E0511]: invalid monomorphization of ... intrinsic: ...` (`InvalidMonomorphization`) |
| **1(f.3) Validity requirement intrinsics** | `assert_inhabited::<T>()`, `assert_zero_valid::<T>()`, `assert_mem_uninitialized_valid::<T>()` | Runtime codegen (`codegen_panic_intrinsic`) vs. CTFE (`InterpCx::emulate_intrinsic_by_name`) | `compiler/rustc_codegen_ssa/src/mir/block.rs:868-925`; `rustc_const_eval/src/const_eval/machine.rs:552-585` | `TerminatorKind::Call` in `body.basic_blocks` (or inside `const { ... }`) | **In runtime code:** compiles (`rc=0`) to a runtime `PanicNounwind` call. **In `const { ... }`:** PME `error[E0080]` |
| **1(f.4) `InlineAsm` PMEs** | Generic `asm!("...", const C::<T>::VAL, sym ...)` or register/target-feature mismatch | Monomorphization collection (`required_consts` of promoted asm const) & `codegen_inline_asm` | `compiler/rustc_mir_build/src/builder/expr/stmt.rs`; `rustc_codegen_ssa/src/mir/block.rs:1460-1555`; `rustc_codegen_llvm/src/asm.rs:26-260` | `TerminatorKind::InlineAsm` in `body.basic_blocks` + promoted `ConstOperand` in `body.required_consts` | `error[E0080]` on `const` operand failure, or backend `emit_err` on invalid register/target feature |

---

### 2. Primary-Source Mechanics by PME Category

#### 2.1 Category 1(a): Inline `const { ... }` Blocks and `body.required_consts`

`Basis: source + execution`

When `rustc` lowers an inline `const { ... }` expression:

1. AST lowering creates a nested `hir::ConstBlock { def_id, hir_id, body }` with
   `DefKind::InlineConst` ([`compiler/rustc_ast_lowering/src/expr.rs:491-500`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_ast_lowering/src/expr.rs#L491-L500)).
2. THIR lowering converts `hir::ExprKind::ConstBlock` into
   `thir::ExprKind::ConstBlock { did, args }`, where `args` are the identity
   generic arguments inherited from the enclosing item.
3. During `mir_built` construction, [`Builder::as_constant`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/expr/as_constant.rs#L72-L102)
   converts `ExprKind::ConstBlock { did: def_id, args }` into a
   `mir::ConstOperand`:

```rust
// compiler/rustc_mir_build/src/builder/expr/as_constant.rs:94-101 (58cf8f9c3 & f8a08b688)
ExprKind::ConstBlock { did: def_id, args } => {
    let uneval = mir::UnevaluatedConst::new(def_id, args);
    let const_ = Const::Unevaluated(uneval, ty);
    ConstOperand { user_ty, span, const_ }
}
```

In [`compiler/rustc_middle/src/mir/consts.rs:274-283`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/consts.rs#L274-L283),
`Const::is_required_const(&self)` returns `true` for every
`Const::Unevaluated(..)` and for every `Const::Ty(_, c)` whose kind is not
`ty::ConstKind::Value(_)`. At the start of the `mir_promoted` query—before
`PromoteTemps`, `SimplifyCfg::PromoteConsts`, borrow checking,
`CleanupPostBorrowck`, `RemovePlaceMention`, or any MIR optimization
pass—`rustc` runs
[`RequiredConstsVisitor::compute_required_consts`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/required_consts.rs#L9-L23)
([`compiler/rustc_mir_transform/src/lib.rs:472-474`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L472-L474)
at `58cf8f9c3`; `:468-470` at `f8a08b688`):

```rust
// compiler/rustc_mir_transform/src/required_consts.rs:9-23 (58cf8f9c3 & f8a08b688)
impl<'tcx> RequiredConstsVisitor<'tcx> {
    pub(super) fn compute_required_consts(body: &mut Body<'tcx>) {
        let mut visitor = RequiredConstsVisitor { required_consts: Vec::new() };
        for (bb, bb_data) in traversal::reverse_postorder(&body) {
            visitor.visit_basic_block_data(bb, bb_data);
        }
        body.set_required_consts(visitor.required_consts);
    }
}

impl<'tcx> Visitor<'tcx> for RequiredConstsVisitor<'tcx> {
    fn visit_constant(&mut self, constant: &ConstOperand<'tcx>, _: Location) {
        if constant.const_.is_required_const() {
            self.required_consts.push(*constant);
        }
    }
}
```

Immediately afterward, [`PromoteTemps`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/promote_consts.rs#L974-L1004)
extracts promoted fragments and populates each promoted body's `required_consts`
(pushing the promoted `ConstOperand` into the parent body's `required_consts` if
`add_to_required_consts` is set). When the MIR inliner
([`compiler/rustc_mir_transform/src/inline.rs:1018-1022`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/inline.rs#L1018-L1022))
inlines a callee into a caller, it extends the caller's `required_consts` with
`callee_body.required_consts().into_iter().filter(|ct| ct.const_.is_required_const())`.

`Const::Unevaluated` is evaluated at two distinct points:

1. **Pre-monomorphization (`KnownPanicsLint` in
   `mir_drops_elaborated_and_const_checked`):** During `analysis(())`
   ([`compiler/rustc_interface/src/passes.rs:1180`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_interface/src/passes.rs#L1180)),
   `rustc` runs `mir_drops_elaborated_and_const_checked`, which includes
   `KnownPanicsLint` ([`compiler/rustc_mir_transform/src/lib.rs:665`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L665)).
   For a non-generic function whose `const { ... }` assignment is reached by
   `ConstPropagator::visit_body` (not guarded by `if false`), `KnownPanicsLint`
   calls `tcx.const_eval_resolve`. If CTFE fails, `analysis(())` calls
   `guar.raise_fatal()` (`passes.rs:1214`) before `pretty::emit_mir(tcx)` runs
   (confirmed by [p1_inline_const.rs](probes/p1_inline_const.rs) with
   `--cfg concrete_fail`).
2. **Post-monomorphization (`collect_items_of_instance` in
   `rustc_monomorphize`):** Whenever the monomorphization collector visits an
   `Instance<'tcx>` in either `CollectionMode::UsedItems` or
   `CollectionMode::MentionedItems`,
   [`collect_items_of_instance`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1374-L1378)
   iterates over `body.required_consts()` and calls
   [`MirUsedCollector::eval_constant`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L711-L729):

```rust
// compiler/rustc_monomorphize/src/collector.rs:711-729 (58cf8f9c3) / :703-721 (f8a08b688)
fn eval_constant(&mut self, constant: &mir::ConstOperand<'tcx>) -> Option<mir::ConstValue> {
    let const_ = self.monomorphize(constant.const_);
    let val = match const_.eval(self.tcx, ty::TypingEnv::fully_monomorphized(), constant.span) {
        Ok(v) => v,
        Err(ErrorHandled::Reported(r, ..)) => {
            self.tcx.dcx().span_note(constant.span, "erroneous constant encountered");
            return None;
        }
        Err(ErrorHandled::TooGeneric(..)) => span_bug!(
            constant.span,
            "collection encountered polymorphic constant: {:?}",
            const_
        ),
    };
    collect_const_value(self.tcx, val, &mut self.output);
    Some(val)
}
```

Inside `Const::eval` ([`compiler/rustc_middle/src/mir/consts.rs:336-348`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/consts.rs#L336-L348)),
`Const::Unevaluated(uneval, _)` dispatches to
`tcx.const_eval_resolve(typing_env, uneval, span)`, which invokes
`eval_to_const_value_raw` -> `eval_to_allocation_raw_provider` and emits
`error[E0080]` on CTFE panic, overflow, or undefined behavior.

---

#### 2.2 Category 1(b): Associated Constants and `zerocopy`'s `static_assert!` Pattern

`Basis: source + execution`

In [`Builder::as_constant`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/expr/as_constant.rs#L72-L97),
any reference to a named or associated constant (`thir::ExprKind::NamedConst {
def_id, args, user_ty }` where `!tcx.is_type_const(def_id)`) lowers to the exact
same `Const::Unevaluated` representation as an inline `const { ... }` block:

```rust
// compiler/rustc_mir_build/src/builder/expr/as_constant.rs:84-93 (58cf8f9c3 & f8a08b688)
ExprKind::NamedConst { def_id, args, user_ty } => {
    if tcx.is_type_const(def_id) {
        let uneval = ty::UnevaluatedConst::new(def_id, args);
        let ct = ty::Const::new_unevaluated(tcx, uneval);
        let const_ = Const::Ty(ty, ct);
        ConstOperand { user_ty, span, const_ }
    } else {
        let uneval = mir::UnevaluatedConst::new(def_id, args);
        let const_ = Const::Unevaluated(uneval, ty);
        ConstOperand { user_ty, span, const_ }
    }
}
```

Both branches (`Const::Ty` with `ConstKind::Unevaluated` and
`Const::Unevaluated`) return `true` from `Const::is_required_const()`. However,
how the constant is used in the enclosing function determines whether it
survives in `body.basic_blocks` after MIR optimization (verified in
[p2_assoc_const_zerocopy.rs](probes/p2_assoc_const_zerocopy.rs)):

1. **`let _ = AssertSize4::<T>::OK;`:** In `rustc_mir_build`,
   [`Builder::in_scope`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/block.rs#L269-L271)
   calls `expr_into_pattern(block, &PatKind::Wild, init)`
   ([`matches/mod.rs:630-635`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/mod.rs#L630-L635)),
   which calls `lower_scrutinee` -> `as_place_builder` -> `expr_as_place`
   ([`as_place.rs:575-596`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/expr/as_place.rs#L575-L596)).
   Because `ExprKind::NamedConst` is a value expression rather than a place,
   `expr_as_place` allocates a temporary `_1` via `this.as_temp` and emits:
   ```mir
   StorageLive(_1);
   _1 = const AssertSize4::<T>::OK;
   PlaceMention(_1);
   StorageDead(_1);
   ```
   - In `mir_promoted`, `RequiredConstsVisitor` visits `_1 = const
     AssertSize4::<T>::OK` and records `AssertSize4::<T>::OK` in
     `body.required_consts`.
   - In `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`, where
     `RemovePlaceMention` strips `PlaceMention(_1)`), the assignment `_1 = const
     AssertSize4::<T>::OK;` remains in `bb0` (retained in `--emit=mir` when
     invoked with `-Z mir-opt-level=0`).
   - In `Runtime(Optimized)` (`-Z mir-opt-level=1`, the default for
     `--emit=mir`), `SimplifyLocals` and dead-store elimination delete `_1` and
     its assignment, leaving `bb0: { return; }` in `--emit=mir` with **no
     trace** of `AssertSize4::<T>::OK` in `let_underscore`'s basic blocks while
     `AssertSize4::<T>::OK` remains in `body.required_consts`.
2. **`let x = AssertSize4::<T>::OK; x` and `10 + AssertSize4::<T>::OK`:**
   Because the value of `AssertSize4::<T>::OK` is used by the return place or
   `AddWithOverflow`, the `ConstOperand` `const AssertSize4::<T>::OK` remains
   both in `body.required_consts` and in `body.basic_blocks` at both
   `-Z mir-opt-level=0` and `-Z mir-opt-level=1`.
3. **`zerocopy`'s `static_assert!` Pattern:** In
   [`zerocopy/src/util/macros.rs:655-685`](https://github.com/google/zerocopy/blob/8fb35253fbc703cb2cd0997f4efcda76cf9062b6/zerocopy/src/util/macros.rs#L655-L685)
   (commit `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`), `static_assert!` is
   defined as:
   ```rust
   macro_rules! static_assert {
       ($($tyvar:ident $(: $(? $optbound:ident $(+)?)* $($bound:ident $(+)?)* )?),* => $condition:expr $(, $args:tt)*) => {{
           trait StaticAssert {
               const ASSERT: bool;
           }

           // NOTE: We use `PhantomData` so we can support unsized types.
           impl<$($tyvar $(: $(? $optbound +)* $($bound +)*)?,)*> StaticAssert for ($(core::marker::PhantomData<$tyvar>,)*) {
               const ASSERT: bool = {
                   const_assert!($condition $(, $args)*);
                   $condition
               };
           }

           const_assert!(<($(core::marker::PhantomData<$tyvar>,)*) as StaticAssert>::ASSERT);
       }};
   }
   ```
   Because `static_assert!` wraps the associated constant lookup in
   `const_assert!(<... as StaticAssert>::ASSERT)` (which expands to
   `assert!(<... as StaticAssert>::ASSERT)`), the generic function's MIR body
   contains both:
   - `<(PhantomData<T>,) as StaticAssert>::ASSERT` in `body.required_consts`,
     and
   - `switchInt(const <(PhantomData<T>,) as StaticAssert>::ASSERT) -> [0: bb1,
     otherwise: bb2]` in `body.basic_blocks` **even at `-Z mir-opt-level=1`**.
   The associated constant's own body (`const <impl ...>::ASSERT: bool = { ...
   }`) is also emitted as a top-level MIR item in `--emit=mir`.

---

#### 2.3 Category 1(c) and Complete Resolution of Dead Conditional Branches vs. Unconditional Divergence (`R-CTFE-02`)

`Basis: normative + source + execution`

In [The Rust Reference (`expressions/block-expr.md`)](https://github.com/rust-lang/reference/blob/82da570bafd9efed421bdbae0f8603ede8dd308b/src/expressions/block-expr.md),
a `const` block inside a function body is evaluated when the enclosing function
is instantiated, even if the `const` block lies inside a dead conditional branch
such as `if false { const { ... } }`, **except** when the statement is
CFG-unreachable in initial MIR construction (such as after an unconditional
`return;`).

Inspecting `rustc_mir_build` and `rustc_mir_transform` alongside our 16-case
probe ([probes/branch_vs_diverge_probe.rs](probes/branch_vs_diverge_probe.rs)
and [probes/p3_dead_branch_ctfe.rs](probes/p3_dead_branch_ctfe.rs)) establishes
the exact compiler mechanism behind this boundary:

##### 2.3.1 How `rustc_mir_build` Lowers Conditional Branches (`if false`, `match false`)

- **`if cond { then_blk } else { else_blk }`:** When `Builder::expr_into_dest`
  lowers `ExprKind::If { cond, then, else_opt }`
  ([`compiler/rustc_mir_build/src/builder/expr/into.rs:61-126`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/expr/into.rs#L61-L126)),
  it delegates condition lowering to `Builder::lower_if_condition`
  ([`compiler/rustc_mir_build/src/builder/matches/mod.rs:102-215`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/mod.rs#L102-L215)):
  ```rust
  // compiler/rustc_mir_build/src/builder/matches/mod.rs:206-214 (58cf8f9c3)
  let scrutinee = unpack!(block = this.as_temp(block, TempLifetime::Temporary, cond_expr, Mutability::Mut));
  let then_blk = this.cfg.start_new_block();
  let else_blk = this.cfg.start_new_block();
  let term = TerminatorKind::if_(Operand::Move(scrutinee), then_blk, else_blk);
  let source_info = this.source_info(cond_span);
  this.cfg.terminate(block, source_info, term);
  ```
  Even when `cond_expr` is `false` (or `const { false }`), `as_temp`
  materializes it into a temporary local (`_1 = const false;` or `_1 = const
  fn::{constant#0};`) and terminates `bb0` with
  `TerminatorKind::if_(Operand::Move(_1), then_blk, else_blk)` (`switchInt(move
  _1) -> [0: else_blk, otherwise: then_blk]`). Thus `then_blk` (`bb1`) has a
  direct incoming CFG edge from `bb0`.
- **`match false { true => ..., false => () }`:** When `Builder::expr_into_dest`
  lowers `ExprKind::Match`
  ([`compiler/rustc_mir_build/src/builder/matches/mod.rs:335-388`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/mod.rs#L335-L388)),
  `lower_scrutinee` materializes `false` into a temporary place (`_1 = const
  false; PlaceMention(_1);`) and `match_candidates` classifies the boolean
  pattern test as `TestKind::If`
  ([`compiler/rustc_mir_build/src/builder/matches/test.rs:43`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/matches/test.rs#L43)).
  `Builder::perform_test` (`matches/test.rs:135-141`) then emits
  `TerminatorKind::if_(val, then_block, else_block)`. Both `if false` and `match
  false` therefore produce identical `SwitchInt` terminators in `mir_built`.

##### 2.3.2 How `rustc_mir_build` Lowers Unconditional Divergence (`return`, `break`, `continue`, `loop {}`)

- **`return`, `break`, and `continue`:** When `Builder::stmt_expr` lowers
  `ExprKind::Ret`, `ExprKind::Break`, or `ExprKind::Continue`
  ([`compiler/rustc_mir_build/src/builder/expr/stmt.rs:96-107`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/expr/stmt.rs#L96-L107)),
  it calls `Builder::break_scope`
  ([`compiler/rustc_mir_build/src/builder/scope.rs:746-831`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/scope.rs#L746-L831)):
  ```rust
  // compiler/rustc_mir_build/src/builder/scope.rs:823-830 (58cf8f9c3)
  let source_info = self.source_info(span);
  destination.add_entry(source_info, block);
  self.cfg.terminate(block, source_info, TerminatorKind::UnwindResume);

  self.cfg.start_new_block().unit()
  ```
  `destination.add_entry(source_info, block)` registers the active block in the
  return or break `DropTree` (which `build_exit_tree` patches to end in
  `TerminatorKind::Return` or `TerminatorKind::Goto`), and `break_scope` returns
  `self.cfg.start_new_block().unit()`—a freshly allocated basic block with
  **zero incoming CFG edges**. When `Builder::ast_block_stmts`
  ([`compiler/rustc_mir_build/src/builder/block.rs:70-81`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/block.rs#L70-L81))
  continues iterating over the remaining lexical statements after `return;`,
  `break;`, or `continue;`, it lowers those statements into that disconnected
  basic block.
- **`loop {}` without `break`:** When `Builder::expr_into_dest` lowers
  `ExprKind::Loop` (`into.rs:146-192`), `in_breakable_scope`
  ([`compiler/rustc_mir_build/src/builder/scope.rs:556-567`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_build/src/builder/scope.rs#L556-L567))
  builds the exit `DropTree` from `break` entries inside the loop body. When the
  loop contains no `break`, `build_exit_tree` returns `None`, and
  `in_breakable_scope` allocates a disconnected basic block via
  `exit_block.unwrap_or_else(|| self.cfg.start_new_block())`.

##### 2.3.3 What `SimplifyCfg::Initial` Removes vs. What `SimplifyConstCondition` Removes

At the end of `mir_built`
([`compiler/rustc_mir_transform/src/lib.rs:413-424`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L413-L424)),
`rustc` runs `SimplifyCfg::Initial` (`run_passes_no_validate(tcx, &mut body,
&[&SimplifyCfg::Initial])`):

1. **Zero-predecessor block deletion (`SimplifyCfg::Initial`):** In
   [`compiler/rustc_mir_transform/src/simplify.rs:81-377`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify.rs#L81-L377),
   `CfgSimplifier::new` computes `pred_count` via a preorder traversal from
   `START_BLOCK` (`bb0`), and `SimplifyCfg::run_pass` finishes by calling
   `remove_dead_blocks(body)` (`simplify.rs:87`), which retains only basic
   blocks visited by `traversal::preorder(body)`. Because the block allocated
   after `return;`, `break;`, `continue;`, or `loop {}` has zero predecessors,
   `remove_dead_blocks` deletes it during `SimplifyCfg::Initial`—before
   `mir_promoted` ever runs.
2. **Why `SimplifyCfg` never folds `switchInt(const false)`:** `CfgSimplifier`
   performs only graph-structural simplifications (`strip_nops`,
   `collapse_goto_chain`, `merge_successor`, and converting a `SwitchInt` into a
   `Goto` in `simplify_branch` at `simplify.rs:256` **only if every target in
   `targets.all_targets()` is the same basic block**, which is also disabled
   when `preserve_switch_reads` is `true` in `MirPhase::Built |
   MirPhase::Analysis(_)`). `SimplifyCfg` never inspects the constant value of a
   `SwitchInt` operand.
3. **Where `switchInt(const false)` is folded (`SimplifyConstCondition`) and how
   `MentionedItems` records dead-branch calls:** Evaluating constant `SwitchInt`
   discriminants (`const false` or a promoted constant) and replacing the
   `SwitchInt` with `TerminatorKind::Goto` is performed by
   `SimplifyConstCondition::{AfterConstProp, Final}` in
   [`compiler/rustc_mir_transform/src/simplify_branches.rs:30-98`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/simplify_branches.rs#L30-L98).
   In the MIR pipeline (`compiler/rustc_mir_transform/src/lib.rs:470-850`),
   `SimplifyConstCondition` runs **only** inside `run_optimization_passes`
   (`lib.rs:738, 752, 756`), gated by `o1(...)` (`-Z mir-opt-level >= 1`). That
   occurs in `inner_optimized_mir` **after**:
   - `RequiredConstsVisitor::compute_required_consts(&mut body)` in
     `mir_promoted` (`lib.rs:473`), which populates `body.required_consts`; and
   - `mentioned_items::MentionedItems` at the start of `inner_optimized_mir`
     ([`lib.rs:808-810`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L808-L810),
     implemented in
     [`compiler/rustc_mir_transform/src/mentioned_items.rs:18-120`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/mentioned_items.rs#L18-L120)),
     which walks `traversal::reverse_postorder(body)` and populates
     `body.mentioned_items` with `MentionedItem::Fn(callee_ty)` (for
     `TerminatorKind::Call`, `TailCall`, `InlineAsmOperand::SymFn`, and
     `PointerCoercion::ReifyFnPointer`), `MentionedItem::Drop(ty)` (for
     `TerminatorKind::Drop`), `MentionedItem::UnsizeCast { source_ty, target_ty
     }`, and `MentionedItem::Closure(source_ty)`.

   During monomorphization collection,
   [`collect_items_of_instance`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1382-L1387)
   converts `body.mentioned_items()` into `MonoItem`s and recursively collects
   them in `CollectionMode::MentionedItems` (`collector.rs:609-618`). In
   `CollectionMode::MentionedItems`, `collect_items_of_instance` skips walking
   `body.basic_blocks` for `UsedItems`, **but still executes**
   `check_normalization_error`, `tcx.ensure_ok().check_mono_item(instance)`,
   `for const_op in body.required_consts() { collector.eval_constant(const_op);
   }`, and transitive `body.mentioned_items()`.

##### 2.3.4 16-Case Empirical Verification Table (`probes/branch_vs_diverge_probe.rs`)

Executing `rustc 1.99.1 (58cf8f9c3 2026-10-13)` (`--emit=obj` and
`-Z dump-mir=Built,SimplifyCfg-initial`) across all 16 combinations of
control-flow construct and PME payload (`const { assert!(N <= 1000); }` vs.
`const_bounded_add::<N>(x)` with `N = 2000`) in
[probes/branch_vs_diverge_probe.rs](probes/branch_vs_diverge_probe.rs) confirms
this exact partition:

| Case ID | Construct | Payload (`N = 2000`) | Predecessors of Payload Block in `mir_built` | In `SimplifyCfg-initial.after`? | Recorded in `required_consts` / `mentioned_items`? | `rustc --emit=obj` Result |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 1a | `if false { ... }` | `const { assert!(N <= 1000); }` | 1 (`bb0` via `SwitchInt`) | **Yes** (`bb1`) | **Yes** (`required_consts`) | **FAIL (`E0080`)** |
| 1b | `if false { ... }` | `const_bounded_add::<N>(x)` | 1 (`bb0` via `SwitchInt`) | **Yes** (`bb1`) | **Yes** (`mentioned_items`) | **FAIL (`E0080`)** |
| 2a | `match false { true => ..., false => () }` | `const { assert!(N <= 1000); }` | 1 (`bb0` via `SwitchInt`) | **Yes** (`bb1`) | **Yes** (`required_consts`) | **FAIL (`E0080`)** |
| 2b | `match false { true => ..., false => () }` | `const_bounded_add::<N>(x)` | 1 (`bb0` via `SwitchInt`) | **Yes** (`bb1`) | **Yes** (`mentioned_items`) | **FAIL (`E0080`)** |
| 3a | `if (const { false }) { ... }` | `const { assert!(N <= 1000); }` | 1 (`bb0` via `SwitchInt`) | **Yes** (`bb1`) | **Yes** (`required_consts`) | **FAIL (`E0080`)** |
| 3b | `if (const { false }) { ... }` | `const_bounded_add::<N>(x)` | 1 (`bb0` via `SwitchInt`) | **Yes** (`bb1`) | **Yes** (`mentioned_items`) | **FAIL (`E0080`)** |
| 4a | `let b = false; if b { ... }` | `const { assert!(N <= 1000); }` | 1 (`bb0` via `SwitchInt`) | **Yes** (`bb1`) | **Yes** (`required_consts`) | **FAIL (`E0080`)** |
| 4b | `let b = false; if b { ... }` | `const_bounded_add::<N>(x)` | 1 (`bb0` via `SwitchInt`) | **Yes** (`bb1`) | **Yes** (`mentioned_items`) | **FAIL (`E0080`)** |
| 5a | `return; ...` | `const { assert!(N <= 1000); }` | **0** (`start_new_block`) | **No** (deleted) | **No** | **PASS (`rc = 0`)** |
| 5b | `return; ...` | `const_bounded_add::<N>(x)` | **0** (`start_new_block`) | **No** (deleted) | **No** | **PASS (`rc = 0`)** |
| 6a | `'blk: { break 'blk; ... }` | `const { assert!(N <= 1000); }` | **0** (`start_new_block`) | **No** (deleted) | **No** | **PASS (`rc = 0`)** |
| 6b | `'blk: { break 'blk; ... }` | `const_bounded_add::<N>(x)` | **0** (`start_new_block`) | **No** (deleted) | **No** | **PASS (`rc = 0`)** |
| 7a | `while !done { done = true; continue; ... }` | `const { assert!(N <= 1000); }` | **0** (`start_new_block`) | **No** (deleted) | **No** | **PASS (`rc = 0`)** |
| 7b | `while !done { done = true; continue; ... }` | `const_bounded_add::<N>(x)` | **0** (`start_new_block`) | **No** (deleted) | **No** | **PASS (`rc = 0`)** |
| 8a | `loop {} ...` (no `break`) | `const { assert!(N <= 1000); }` | **0** (`start_new_block`) | **No** (deleted) | **No** | **PASS (`rc = 0`)** |
| 8b | `loop {} ...` (no `break`) | `const_bounded_add::<N>(x)` | **0** (`start_new_block`) | **No** (deleted) | **No** | **PASS (`rc = 0`)** |

**Consequence for `Runtime(PostCleanup)` MIR capture:** Because
`tcx.mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`) runs
*after* `SimplifyCfg::Initial` and *before* `SimplifyConstCondition`, the set of
basic blocks present in a function's `Runtime(PostCleanup)` MIR body is
**identical** to the set of basic blocks visited by `RequiredConstsVisitor` and
`MentionedItems`. No extra reachability filter is required: every `const` block
or function call that survives into `Runtime(PostCleanup)` MIR is a true PME
obligation in `rustc`, and every statement after `return;`, `break;`,
`continue;`, or `loop {}` has already been removed.

---

#### 2.4 Category 1(d): Type Layout Errors (`LayoutError`) and Pointer Indirection Subtlety

`Basis: source + execution`

`LayoutError<'tcx>` is defined in
[`compiler/rustc_middle/src/ty/layout.rs:58-106`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/ty/layout.rs#L58-L106)
with six variants:

- `LayoutError::Unknown(Ty<'tcx>)`: layout cannot be computed (e.g., an
  unsatisfiable predicate on an associated constant array length).
- `LayoutError::SizeOverflow(Ty<'tcx>)`: type size exceeds
  `tcx.data_layout().obj_size_bound()` (`isize::MAX as u64` bytes, i.e.,
  $2^{63} - 1$ bytes on 64-bit targets).
- `LayoutError::InvalidSimd { ty: Ty<'tcx>, kind: SimdLayoutError }`:
  - `SimdLayoutError::ZeroLength`: `#[repr(simd)]` array has 0 lanes
    ([`compiler/rustc_ty_utils/src/layout.rs:154-156`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_ty_utils/src/layout.rs#L154-L156)).
  - `SimdLayoutError::TooManyLanes(Limit)`: `#[repr(simd)]` array exceeds
    `max_lanes` (`32768` lanes;
    `compiler/rustc_ty_utils/src/layout.rs:158-160`).
  - A third SIMD layout failure,
    `LayoutCalculatorError::NonPrimitiveSimdType(field)`, does not return
    `Err(LayoutError)`:
    [`map_error`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_ty_utils/src/layout.rs#L162-L166)
    immediately aborts via `cx.tcx().dcx().emit_fatal(NonPrimitiveSimdType { ty,
    e_ty: field.ty })`.
- `LayoutError::NormalizationFailure(Ty<'tcx>, TypeError<'tcx>)`: an alias type
  inside `Ty<'tcx>` failed to normalize under the current `TypingEnv`.
- `LayoutError::ReferencesError(ErrorGuaranteed)`: `Ty<'tcx>` contains
  `ty::Error`.
- `LayoutError::TooGeneric(Ty<'tcx>)`: `Ty<'tcx>` still contains uninstantiated
  type or const parameters.

`tcx.layout_of(typing_env.as_query_input(ty))` is queried in four post-analysis
locations:

1. **`mono_checks::move_check::check_moves`**
   ([`compiler/rustc_monomorphize/src/mono_checks/move_check.rs:21-90`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/mono_checks/move_check.rs#L21-L90),
   called from `collector.rs:1338`): queries `tcx.layout_of` on moved/assigned
   places when linting `large_assignments` (ignoring `Err` via `let
   Ok(ty_layout) = ...`).
2. **CTFE (`size_of::<T>()`, `align_of::<T>()`, const layout queries):** In
   `core::mem::size_of::<T>()`, `SizedTypeProperties::SIZE` calls the `size_of`
   intrinsic in CTFE, which queries `ecx.layout_of(ty)` and converts
   `LayoutError::SizeOverflow` into `error[E0080]: values of the type ... are
   too big for the target architecture`.
3. **Function ABI computation (`cx.fn_abi_of_instance` / `fn_abi_of_fn_ptr`):**
   [`FnAbiOfHelpers::handle_fn_abi_err`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/ty/layout.rs#L365-L432)
   handles `FnAbiError::Layout(layout_err)` by calling `self.handle_layout_err`
   and emitting a fatal `SpannedWithLayoutError` whenever a parameter or return
   type of a monomorphized function (or function pointer call) has an invalid
   layout.
4. **MIR-to-SSA lowering (`codegen_mir`):**
   [`allocate_local`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_ssa/src/mir/mod.rs#L329-L361)
   calls `start_bx.layout_of(fx.monomorphize(decl.ty))` for every local in
   `mir.local_decls`; [`codegen_place`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_ssa/src/mir/place.rs)
   and [`codegen_rvalue`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_ssa/src/mir/rvalue.rs)
   call `bx.layout_of(...)` on projected place base types (such as `&(*p).1`)
   and rvalue types. Any `Err(layout_err)` invokes
   [`LayoutOfHelpers::handle_layout_err`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/ty/layout.rs#L315-L357),
   which emits a fatal `SpannedWithLayoutError`.

**Indirection subtlety (`*const Big<T>` and `&Big<T>` without field
projection):** Computing `layout_of(*const Big<T>)` or `layout_of(&Big<T>)` only
checks whether `Big<T>` is `Sized` to choose between a thin pointer (8 bytes)
and a wide pointer (16 bytes). When computing pointer metadata for `&Big<T>`,
`pointee_info_at` (`compiler/rustc_ty_utils/src/abi.rs`) calls
`cx.layout_of(pointee_ty).ok()`, silently discarding
`Err(LayoutError::SizeOverflow)`. Consequently, as verified in
[probes/p4_layout_and_mono_limits.rs](probes/p4_layout_and_mono_limits.rs):

- `pub fn ref_only<T>(_p: &Big<T>) {}` and `pub fn ptr_only<T>(_p: *const
  Big<T>) {}` instantiated with `Big<u32>` (`([u32; usize::MAX / 2], u8)`)
  **compile with exit code 0**.
- `pub fn proj_ref<T>(p: &Big<T>) -> &u8 { &p.1 }`, taking `Big<u32>` by value,
  allocating a local of type `Big<u32>`, or calling `size_of::<Big<u32>>()`
  queries `layout_of(Big<u32>)` directly and **fails with a PME**.

---

#### 2.5 Category 1(e): Monomorphization Recursion & Normalization Limits vs. `ImpossibleClauses` Suppression

`Basis: source + execution`

During `collect_items_rec`
([`compiler/rustc_monomorphize/src/collector.rs:465-489`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L465-L489)):

1. **Polymorphic recursion limit (`check_recursion_limit`):**
   [`check_recursion_limit`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L654-L685)
   checks whether the monomorphization recursion depth exceeds
   `tcx.recursion_limit()` (default `128`). If exceeded (e.g., polymorphic
   recursion `poly_rec::<(T,)>(n - 1)` in
   [probes/p4_layout_and_mono_limits.rs](probes/p4_layout_and_mono_limits.rs)),
   it aborts via `tcx.dcx().emit_fatal(RecursionLimit { span, instance, ... })`.
2. **Post-monomorphization normalization overflow
   (`check_normalization_error`):**
   [`check_normalization_error`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L626-L652)
   (called at the start of `collect_items_of_instance`, line 1337) walks every
   type and constant in `body` and normalizes it under
   `TypingEnv::fully_monomorphized()`. If normalization overflows the trait/type
   recursion limit (`Err(NormalizationErrorInMono)`), `collect_items_rec` (line
   483) emits the same fatal `RecursionLimit` diagnostic.
3. **PME suppression via `ImpossibleClauses` (`ImpossiblePredicates` in
   `f8a08b688`) and `MonoItem::is_instantiable`:** In `rustc 1.99.1`
   (`58cf8f9c3`), the pass and query are named `ImpossibleClauses` and
   `instantiate_and_check_impossible_clauses`; in `rustc 1.98.0-nightly`
   (`f8a08b688`), they are named `ImpossiblePredicates` and
   `instantiate_and_check_impossible_predicates`:
   - During `Analysis(PostCleanup)`,
     [`ImpossibleClauses::run_pass`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/impossible_clauses.rs#L99-L115)
     (`compiler/rustc_mir_transform/src/impossible_predicates.rs:56-72` at
     `f8a08b688`) checks whether the item has unsatisfiable `where` clauses (or,
     in `58cf8f9c3`, structurally impossible `Sized` clauses such as `[T]:
     Sized` via `has_structurally_impossible_sized_clause`, lines 51–84). If so,
     it truncates `body.basic_blocks` to a single `bb0: { unreachable; }` block
     and clears `body.required_consts`.
   - During monomorphization root collection,
     [`RootCollector::push_if_root`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/collector.rs#L1589)
     checks `mono_item.is_instantiable(tcx)`
     ([`compiler/rustc_middle/src/mono.rs:272-282`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mono.rs#L272-L282)),
     which calls `!tcx.instantiate_and_check_impossible_clauses((def_id,
     &args))`. If the clauses are impossible, the item is skipped, suppressing
     PMEs inside uncallable items (verified by
     [probes/p4_layout_and_mono_limits.rs](probes/p4_layout_and_mono_limits.rs)
     with `--cfg feature_trivial_bounds`).

---

#### 2.6 Category 1(f): Codegen-Time ABI, SIMD/Scalar Intrinsic, Validity-Requirement Intrinsic, and `InlineAsm` Errors

`Basis: source + execution`

Verified in
[probes/p5_codegen_abi_intrinsics_asm.rs](probes/p5_codegen_abi_intrinsics_asm.rs):

1. **Target-feature ABI checks (`mono_checks::abi_check`):** Called from
   `collect_items_of_instance` -> `tcx.ensure_ok().check_mono_item(instance)`
   ([`compiler/rustc_monomorphize/src/mono_checks/abi_check.rs:131-265`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_monomorphize/src/mono_checks/abi_check.rs#L131-L265)),
   `check_feature_dependent_abi` validates every monomorphized function
   definition and every `TerminatorKind::Call`, emitting:
   - `AbiErrorUnsupportedUnsizedParameter` for non-rustic ABIs (`extern "C"`)
     passing an unsized parameter by value;
   - `AbiErrorUnsupportedVectorType` / `AbiErrorDisabledVectorType`
     (`abi_check.rs:51-106`) when passing or returning a `#[repr(simd)]` vector
     by value requires a target feature (such as `avx` for a 256-bit `[f64; 4]`
     vector on `x86_64`) that is not enabled; and
   - `AbiRequiredTargetFeature` when calling or defining a function whose ABI
     requires a disabled baseline target feature (such as `extern "vectorcall"`
     without `sse2`).
2. **SIMD and scalar intrinsic `InvalidMonomorphization` (`E0511`):** In
   [`compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:90-370`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_ssa/src/mir/intrinsic.rs#L90-L370)
   and
   [`compiler/rustc_codegen_llvm/src/intrinsic.rs`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_llvm/src/intrinsic.rs),
   intrinsics whose type signatures are unconstrained `T` (such as
   `core::intrinsics::simd::simd_add<T>(a: T, b: T) -> T`) check the
   monomorphized type `T` during backend codegen and emit
   `InvalidMonomorphization` (`error[E0511]`, defined in
   `compiler/rustc_codegen_ssa/src/diagnostics.rs:723` at `58cf8f9c3` and
   `errors.rs:714` at `f8a08b688`) if `T` is not a `#[repr(simd)]` type or has
   unsupported element types or mismatched lane counts.
3. **Validity-requirement intrinsics (`assert_inhabited`, `assert_zero_valid`,
   `assert_mem_uninitialized_valid`):**
   - **In runtime codegen (`codegen_panic_intrinsic`,
     [`compiler/rustc_codegen_ssa/src/mir/block.rs:868-925`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_ssa/src/mir/block.rs#L868-L925)):**
     `bx.tcx().check_validity_requirement((requirement,
     bx.typing_env().as_query_input(ty)))` is evaluated. If `Ok(true)`, the call
     is lowered to a no-op `goto -> target`. If `Ok(false)` (e.g.,
     `assert_inhabited::<Void>()`), `rustc` **does not emit a compile-time
     error**; it emits a runtime call to `LangItem::PanicNounwind` with the
     message `"attempted to instantiate uninhabited type ..."` (or `"attempted
     to zero-initialize..."` / `"attempted to leave type ... uninitialized"`),
     and compilation succeeds with exit code `0`.
   - **In CTFE (`InterpCx::emulate_intrinsic_by_name`,
     [`compiler/rustc_const_eval/src/const_eval/machine.rs:552-585`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_const_eval/src/const_eval/machine.rs#L552-L585)):**
     When called inside a `const { ... }` block (or a `const fn` evaluated in
     CTFE), `should_panic = !ecx.tcx.check_validity_requirement(...)` invokes
     `Self::panic_nounwind(ecx, &msg)`, aborting CTFE and emitting a
     compile-time PME (`error[E0080]: evaluation panicked: aborted execution:
     attempted to instantiate uninhabited type ...`).
4. **Inline assembly (`TerminatorKind::InlineAsm`):** An `asm!("...", const
   EXPR)` operand is lowered by `rustc_mir_build` as a promoted `InlineConst`
   (`asm_with_const::{constant#0}`) whose body evaluates `EXPR` and whose
   `ConstOperand` is placed in both `InlineAsmOperand::Const { value }` and
   `body.required_consts`. If evaluating `EXPR` fails after monomorphization,
   `collect_items_of_instance` emits `error[E0080]`. At codegen time
   ([`compiler/rustc_codegen_ssa/src/mir/block.rs:1460-1555`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_ssa/src/mir/block.rs#L1460-L1555)
   and [`compiler/rustc_codegen_llvm/src/asm.rs:26-260`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_codegen_llvm/src/asm.rs#L26-L260)),
   `codegen_inline_asm` validates register classes against monomorphized operand
   types and enabled target features.

---

### 3. Representation in `Runtime(PostCleanup)` vs. `--emit=mir` and In-Process `rustc_driver` Capture

`Basis: source + execution + derived`

#### 3.1 How `rustc --emit=mir` and `anneal-rustc-capture` Interact

In [`trusted/rustc-capture/src/lib.rs:219-243`](https://github.com/joshlf/anneal/blob/e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0/trusted/rustc-capture/src/lib.rs#L219-L243),
`anneal-rustc-capture` invokes `rustc --edition=2024 --crate-name=anneal_target
--crate-type=lib --emit=mir=<mir_path>,metadata=<rmeta_path> <crate_root>`.
Tracing this invocation through `rustc` establishes three architectural facts:

1. **`--emit=mir` prints `tcx.optimized_mir(def_id)` (`Runtime(Optimized)`,
   default `-Z mir-opt-level=1`), not `Runtime(PostCleanup)`
   (`mir_drops_elaborated_and_const_checked`).** In
   [`write_mir_pretty`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs#L342-L359),
   `rustc` calls `tcx.instance_mir(InstanceKind::Item(def_id))` (resolving to
   `tcx.optimized_mir(def_id)`), and for `const fn` items also prints `// MIR
   FOR CTFE` (`tcx.mir_for_ctfe(def_id)`). Without `-Z mir-opt-level=0`,
   `optimized_mir` runs level-1 MIR optimizations (`RemoveZsts`,
   `SimplifyLocals`, `SimplifyConstCondition`, `DeadStoreElimination`), which
   strip unused `const { ... }`, `let _ = Assoc::CONST;`, and `if false {
   callee::<T>(); }` statements from `body.basic_blocks`.
2. **`write_mir_fn` never prints `body.required_consts` or
   `body.mentioned_items`.** In
   [`compiler/rustc_middle/src/mir/pretty.rs:378-658`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/pretty.rs#L378-L658),
   neither `body.required_consts` nor `body.mentioned_items` is formatted.
   However, every inline `const { ... }` block (`DefKind::InlineConst`) and
   every associated constant (`DefKind::AssocConst`) has its own `LocalDefId` in
   `tcx.mir_keys(())`, so its own body is printed as a separate top-level item
   in the `.mir` file.
3. **`OutputType::Mir` sets `should_codegen() == true`, running monomorphization
   collection *after* `pretty::emit_mir(tcx)`.** In
   [`compiler/rustc_driver_impl/src/lib.rs:315-332`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_driver_impl/src/lib.rs#L315-L332),
   line 315 runs `tcx.ensure_ok().analysis(())`, line 326 runs
   `pretty::emit_mir(tcx)` (writing `<mir_path>` to disk), and line 331 runs
   `Linker::codegen_and_build_linker(tcx, codegen_backend)` ->
   `passes::start_codegen`
   ([`compiler/rustc_interface/src/passes.rs:1286-1340`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_interface/src/passes.rs#L1286-L1340)).
   Because [`OutputTypes::should_codegen()`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_session/src/config.rs#L911-L922)
   returns `true` for `OutputType::Mir`, `start_codegen` invokes
   `codegen_backend.codegen_crate(tcx)` even when only `--emit=mir,metadata` was
   requested. Uninstantiated generic functions in a `--crate-type=lib` crate are
   skipped by `RootCollector` (`rc = 0`), whereas a monomorphic root that
   instantiates a generic function with PME-triggering arguments causes
   `pretty::emit_mir(tcx)` to write the `.mir` file first and `start_codegen` to
   fail with `rc = 1`.

#### 3.2 Four `TyCtxt` and MIR Invariants from the In-Process `rustc_driver` Capture Prototype (`pme_capture_probe/`)

To test in-process extraction against all PME and precondition patterns, we
built [pme_capture_probe/driver.rs](pme_capture_probe/driver.rs) (`Callbacks`
implementing `after_analysis`) and executed it on
[pme_capture_probe/src/lib.rs](pme_capture_probe/src/lib.rs), comparing its
output ([pme_capture_probe/driver_output.txt](pme_capture_probe/driver_output.txt))
against `--emit=mir -Z mir-opt-level=0`
([pme_capture_probe/emitted_opt0.mir](pme_capture_probe/emitted_opt0.mir)) and
default `--emit=mir`
([pme_capture_probe/emitted_opt1.mir](pme_capture_probe/emitted_opt1.mir)).
Building and running `driver.rs` established four invariants:

1. **Steal ordering between `mir_drops_elaborated_and_const_checked` and
   `optimized_mir`:** In
   [`compiler/rustc_mir_transform/src/lib.rs:804`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_mir_transform/src/lib.rs#L804),
   `inner_optimized_mir` calls
   `tcx.mir_drops_elaborated_and_const_checked(def).steal()`. Calling
   `tcx.optimized_mir(def_id)` before
   `tcx.mir_drops_elaborated_and_const_checked(local_id).borrow()` panics with
   `attempted to read from stolen value: rustc_middle::mir::Body`. Any extractor
   that reads both phases must borrow and serialize
   `mir_drops_elaborated_and_const_checked` before querying `optimized_mir`.
2. **Population timing of `required_consts` vs. `mentioned_items` (and direct
   presence of dead-branch calls in `Runtime(PostCleanup)`):**
   `body.required_consts()` is populated during `mir_promoted` (`lib.rs:473`),
   so it is already `Some(...)` on `mir_drops_elaborated_and_const_checked`.
   `body.mentioned_items()` is populated by `mentioned_items::MentionedItems` at
   the start of `inner_optimized_mir` (`lib.rs:808`), so `mentioned_items` is
   still `None` on `mir_drops_elaborated_and_const_checked`. However, because
   `SimplifyConstCondition` has not run yet in `Runtime(PostCleanup)`,
   dead-branch calls such as `if false { let _ = const_bounded_add::<N>(x); }`
   in `dead_call_pme` remain present as live `TerminatorKind::Call` terminators
   in `bb1` of `Runtime(PostCleanup)` (`bb_count = 5`), whereas in
   `Runtime(Optimized)` they are folded away (`bb_count = 1`) and survive only
   in `opt_body.mentioned_items()`.
3. **Resolving trait associated constants (`StaticAssert::ASSERT`) via
   `ty::Instance::try_resolve`:** In `transmute_ref_static_assert`,
   `assert!(<(...) as StaticAssert>::ASSERT)` produces a `Const::Unevaluated(uv,
   bool)` entry in `required_consts()` where `uv.def` is the **trait
   declaration item** `transmute_ref_static_assert::StaticAssert::ASSERT`
   (`DefKind::AssocConst`) with `uv.args = [(PhantomData<Src>,
   PhantomData<Dst>)]`—not the `impl` item. Calling `tcx.mir_for_ctfe(uv.def)`
   directly on the trait declaration causes an ICE (`can't type-check body of
   ...::StaticAssert::ASSERT`) because a trait associated constant without a
   default has no body. Resolving `(uv.def, uv.args)` via
   `ty::Instance::try_resolve` in the function's post-analysis `TypingEnv`
   (matching `tcx.const_eval_resolve` in
   [`compiler/rustc_middle/src/mir/interpret/queries.rs:75`](https://github.com/rust-lang/rust/blob/58cf8f9c35b355199727627d07ae34a4e2846d67/compiler/rustc_middle/src/mir/interpret/queries.rs#L75))
   cleanly resolves `(StaticAssert::ASSERT, [(PhantomData<Src>,
   PhantomData<Dst>)])` to the `impl` item `<(PhantomData<S>, PhantomData<D>) as
   StaticAssert>::ASSERT` with `resolved_args = [Src/#0, Dst/#1]`, allowing
   `tcx.mir_for_ctfe(resolved_def)` to return its 10-block
   `Runtime(PostCleanup)` CTFE body.
4. **Orphan `InlineConst` `LocalDefId`s in `tcx.mir_keys(())` after `return;`:**
   In `after_return_no_pme`, `const { assert!(N <= 1000); };` appears after
   `return x;`. Because HIR lowering allocates a `LocalDefId` for every
   `const { ... }` block before MIR construction runs,
   `after_return_no_pme::{constant#0}` still appears in `tcx.mir_keys(())` (and
   is printed as a top-level item at line 424 of
   [pme_capture_probe/emitted_opt1.mir](pme_capture_probe/emitted_opt1.mir)).
   However, `after_return_no_pme`'s `body.required_consts()` is empty (`0`), and
   its `Runtime(PostCleanup)` MIR is `bb0: { _0 = copy _1; return; }`. Attaching
   an `InlineConst` (`{constant#0}`) to its parent function merely because it
   appears in `tcx.mir_keys(())` or `--emit=mir` would be **unsound**; a
   constant body is a PME obligation of `f` if and only if `f`'s
   `required_consts()` (or `Runtime(PostCleanup)` basic blocks) references it.

#### 3.3 Summary of Extracted Functions in `pme_capture_probe/`

| Function | `is_external_entry_fn` (`isPublic`) | `isSafe` | `PostCleanup` BBs | `Optimized` BBs | `required_consts` (`Const::Unevaluated`) | `mentioned_items` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `add` | `false` | `true` | 2 (`AddWithOverflow` + `assert!`) | 2 | `[]` | `[]` |
| `double_bounded` | `true` | `true` | 5 (`Le(x, 1000)` -> `add(x, x)`) | 4 | `[]` | `[Fn(add, [])]` |
| `const_bounded_add<N>` | `true` | `true` | 5 (`_2 = const ...::{constant#0}` in `bb0`) | 5 (`_2` dead-store eliminated) | `[const_bounded_add::{constant#0} args=[N/#0, ()]]` (3 CTFE BBs) | `[]` |
| `transmute_ref<Src, Dst>` | `true` | `true` | 1 (`_2 = const ...::{constant#0}` + raw ptr cast/deref) | 3 (`UbChecks` alignment/null asserts added; `_2` eliminated) | `[transmute_ref::{constant#0} args=[Src/#0, Dst/#1, ()]]` (9 CTFE BBs) | `[]` |
| `transmute_ref_static_assert<Src, Dst>` | `true` | `true` | 3 (`_3 = const <... as StaticAssert>::ASSERT; switchInt(_3)`) | 5 | `[StaticAssert::ASSERT -> resolved impl ASSERT args=[Src/#0, Dst/#1]]` (10 CTFE BBs) | `[Fn(core::panicking::panic, [])]` |
| `dead_call_pme<N>` | `true` | `true` | 5 (`bb0` `switchInt(false)` -> `bb1` calls `const_bounded_add::<N>`) | 1 (`bb1` folded away by `SimplifyConstCondition`) | `[]` | `[Fn(const_bounded_add, [N/#0])]` |
| `after_return_no_pme<N>` | `true` | `true` | 1 (`_0 = copy _1; return;`) | 1 | `[]` (`{constant#0}` is NOT in `required_consts`) | `[]` |

## Boundaries

The findings in this report are subject to the following scope boundaries:

- **Target-Specific Inline Assembly and Backend-Only LLVM Intrinsics (not
  exhaustively enumerated):** While Section 2.6 documents
  `codegen_intrinsic_call` (`InvalidMonomorphization` / `E0511`),
  `codegen_panic_intrinsic`, `check_feature_dependent_abi`, and
  `codegen_inline_asm` on `x86_64-unknown-linux-gnu`, individual
  architecture-specific inline assembly register constraints and target-specific
  LLVM intrinsic lowering errors beyond `simd_add` and `AvxVec` were **not
  examined** per target architecture.
- **Subprocess `--emit=mir` Cannot Soundly Reconstruct Trait Associated Constant
  Resolution or Effective Visibilities (known not to apply):** Even when invoked
  with `-Z mir-opt-level=0` (which preserves `_2 = const ...::{constant#0}` and
  dead-branch `Call` terminators in `body.basic_blocks`, while still running
  `UbChecks` unless `-Z ub-checks=false` is passed), textual `--emit=mir`
  formats the operand in `transmute_ref_static_assert` as `const
  <(PhantomData<Src>, PhantomData<Dst>) as ...::StaticAssert>::ASSERT` while
  emitting the implementation body header as `const ...::<impl at
  file:line>::ASSERT: bool =`. Textual `--emit=mir` also omits module re-export
  reachability (`tcx.effective_visibilities(())`), so full trait associated
  constant resolution (`ty::Instance::try_resolve`) and effective visibility
  queries require in-process `TyCtxt` access.
- **Uninstantiated Generic Functions in `--crate-type=lib` Crates:** Because
  `RootCollector` collects only monomorphic roots, compiling a library crate
  with `rustc --crate-type=lib` does **not** evaluate PMEs in uninstantiated
  generic functions. A passing `rustc` build of a library crate therefore does
  not establish that its generic functions are free of PMEs for all type or
  const-generic substitutions.

## Evidence

### 1. Preserved Support Material in This Package

All empirical probe crates, the `rustc_driver` prototype, and captured MIR
outputs are preserved inside this report package with the following SHA-256
digests:

| Package-Local File | SHA-256 Digest | Lines | Description |
| :--- | :--- | ---: | :--- |
| [probes/p1_inline_const.rs](probes/p1_inline_const.rs) | `a3aceeb0ae4550a4fd0b1bd701a1cbcde3c0e190bca47edb50f6bfa90aa3c494` | 38 | Probe 1: Concrete vs. generic `const { assert!(...); }` blocks (`KnownPanicsLint` vs. monomorphization `E0080`). |
| [probes/p2_assoc_const_zerocopy.rs](probes/p2_assoc_const_zerocopy.rs) | `5655ae4bf348187ebe209e9d0168a0e94b479cf3a635b0659a6a3736d08f424b` | 61 | Probe 2: Associated constant PMEs (`let _ = ...`, `let x = ...`, operand use) and `zerocopy`'s `static_assert!` pattern. |
| [probes/p3_dead_branch_ctfe.rs](probes/p3_dead_branch_ctfe.rs) | `30a753c25768a5e1389e9bdfbf9ec4ef1857efb0e833a7a90e2610a5278f0a6d` | 95 | Probe 3: Dead-branch `if false` (`required_consts` and `mentioned_items`) vs. post-`return` CFG-unreachable blocks. |
| [probes/p4_layout_and_mono_limits.rs](probes/p4_layout_and_mono_limits.rs) | `ceadc1553cc20f59e444135af640b81fad8c8f9cda03bd47ec5b6eef8f579f72` | 72 | Probe 4: `LayoutError::SizeOverflow` (`*const Big<T>` and `&Big<T>` vs. `&p.1` and by-value), `InvalidSimd`, `NonPrimitiveSimdType`, `poly_rec` recursion limit, and `ImpossibleClauses`. |
| [probes/p5_codegen_abi_intrinsics_asm.rs](probes/p5_codegen_abi_intrinsics_asm.rs) | `cde71e960c46ed1d8a547750e1a4b766a93b0b9b4e910a09c704d2ea9df700cb` | 75 | Probe 5: `InlineAsm` `const` operand PME, `AvxVec` target-feature ABI error, `simd_add` `E0511`, and `assert_inhabited::<Void>()` runtime panic vs. CTFE PME. |
| [probes/branch_vs_diverge_probe.rs](probes/branch_vs_diverge_probe.rs) | `4ed7c96ef1c76ecbde7f24dcfb339b84affee0e89a60aa0392c76cafb4c9e6f8` | 231 | 16-case matrix testing `if false`, `match false`, `if (const { false })`, and `let b = false; if b` against `return`, `break`, `continue`, and `loop {}` for both inline `const` and call PME payloads. |
| [pme_capture_probe/src/lib.rs](pme_capture_probe/src/lib.rs) | `671653e597a9867c699b0fcd477a0c2b11faeacea8f8eb6379ace35ecb70c2aa` | 70 | Combined 7-function test crate exercising private helper calls, `const` block PMEs, `transmute_ref`, `transmute_ref_static_assert`, `dead_call_pme`, and `after_return_no_pme`. |
| [pme_capture_probe/driver.rs](pme_capture_probe/driver.rs) | `0780f4b6a94cc538cf6a1113017628c76386d96b80838d167ddd31be8e4505af` | 279 | In-process `rustc_driver` prototype extracting `is_external_entry_fn`, `Runtime(PostCleanup)` vs. `Runtime(Optimized)` MIR, `required_consts` (via `Instance::try_resolve` + `mir_for_ctfe`), and `mentioned_items`. |
| [pme_capture_probe/driver_output.txt](pme_capture_probe/driver_output.txt) | `3a11a22d086fa2a945d3d0c680145385124952f90d02cded091b8c9228436d42` | 496 | Full output of running `driver` on `pme_capture_probe/src/lib.rs` under `rustc 1.99.1 (58cf8f9c3 2026-10-13)`. |
| [pme_capture_probe/emitted_opt0.mir](pme_capture_probe/emitted_opt0.mir) | `d447479df6c3489b529ea6ede6037f36f7cc00b4a17881fc2e41365365c108e9` | 568 | Output of `rustc --emit=mir -Z mir-opt-level=0` on `pme_capture_probe/src/lib.rs`. |
| [pme_capture_probe/emitted_opt1.mir](pme_capture_probe/emitted_opt1.mir) | `f1ecb50c2ef4df3d599a1ec81c689935c1f6ee46e36bbb0ccfbeee10e650fcce` | 455 | Output of default `rustc --emit=mir` (`-Z mir-opt-level=1`) on `pme_capture_probe/src/lib.rs`. |

### 2. Primary Upstream Source Coordinates

All source claims were inspected directly at the pinned revisions recorded in
`REPORT.json` (observed on `2026-10-30`):

- **`rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67` and
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):**
  - `compiler/rustc_ast_lowering/src/expr.rs:491-500` (`lower_expr_const_block`)
  - `compiler/rustc_mir_build/src/builder/expr/as_constant.rs:72-102`
    (`Builder::as_constant` for `ExprKind::NamedConst` and
    `ExprKind::ConstBlock`)
  - `compiler/rustc_mir_build/src/builder/expr/as_place.rs:575-596`
    (`expr_as_place` materializing value expressions into temporaries for
    wildcard patterns)
  - `compiler/rustc_mir_build/src/builder/expr/into.rs:61-126, 146-192`
    (`ExprKind::If` and `ExprKind::Loop` lowering)
  - `compiler/rustc_mir_build/src/builder/expr/stmt.rs:96-107` (`ExprKind::Ret`,
    `ExprKind::Break`, `ExprKind::Continue` lowering)
  - `compiler/rustc_mir_build/src/builder/matches/mod.rs:102-215, 335-388,
    630-635` (`lower_if_condition`, `ExprKind::Match`, `expr_into_pattern`)
  - `compiler/rustc_mir_build/src/builder/matches/test.rs:43, 135-141`
    (`TestKind::If` and `Builder::perform_test`)
  - `compiler/rustc_mir_build/src/builder/scope.rs:556-567, 746-831`
    (`in_breakable_scope` and `break_scope` allocating zero-predecessor blocks
    via `self.cfg.start_new_block()`)
  - `compiler/rustc_mir_transform/src/lib.rs:413-424, 472-478, 665, 738-756,
    804-810` (`mir_built` with `SimplifyCfg::Initial`, `mir_promoted` with
    `RequiredConstsVisitor`, `mir_drops_elaborated_and_const_checked` with
    `KnownPanicsLint`, and `inner_optimized_mir` stealing `PostCleanup` and
    running `MentionedItems` before `SimplifyConstCondition`)
  - `compiler/rustc_mir_transform/src/required_consts.rs:9-23`
    (`RequiredConstsVisitor::compute_required_consts`)
  - `compiler/rustc_mir_transform/src/mentioned_items.rs:18-120`
    (`MentionedItems` visitor)
  - `compiler/rustc_mir_transform/src/simplify.rs:81-377` (`SimplifyCfg`,
    `remove_dead_blocks`, and `simplify_branch`)
  - `compiler/rustc_mir_transform/src/simplify_branches.rs:30-98`
    (`SimplifyConstCondition`)
  - `compiler/rustc_mir_transform/src/known_panics_lint.rs:190-220`
    (`KnownPanicsLint`)
  - `compiler/rustc_mir_transform/src/impossible_clauses.rs:51-115` at
    `58cf8f9c3` (and
    `compiler/rustc_mir_transform/src/impossible_predicates.rs:56-72` at
    `f8a08b688`) (`ImpossibleClauses` / `ImpossiblePredicates`)
  - `compiler/rustc_monomorphize/src/collector.rs:465-489, 609-618, 626-685,
    711-729, 1337-1387, 1589` at `58cf8f9c3` (`:703-721, 1364-1368` at
    `f8a08b688`) (`collect_items_rec`, `check_normalization_error`,
    `check_recursion_limit`, `MirUsedCollector::eval_constant`,
    `collect_items_of_instance`, `RootCollector::push_if_root`)
  - `compiler/rustc_monomorphize/src/mono_checks/abi_check.rs:51-265`
    (`check_feature_dependent_abi`)
  - `compiler/rustc_monomorphize/src/mono_checks/move_check.rs:21-90`
    (`check_moves`)
  - `compiler/rustc_middle/src/mir/consts.rs:274-283, 336-348`
    (`Const::is_required_const` and `Const::eval`)
  - `compiler/rustc_middle/src/mir/interpret/queries.rs:75`
    (`tcx.const_eval_resolve` calling `ty::Instance::try_resolve`)
  - `compiler/rustc_middle/src/mir/pretty.rs:342-658` (`write_mir_pretty` and
    `write_mir_fn`)
  - `compiler/rustc_middle/src/mono.rs:272-282` (`MonoItem::is_instantiable`)
  - `compiler/rustc_middle/src/ty/layout.rs:58-106, 288-432` (`LayoutError`,
    `LayoutOfHelpers::handle_layout_err`, `FnAbiOfHelpers::handle_fn_abi_err`)
  - `compiler/rustc_ty_utils/src/layout.rs:93-169` (`layout_of_uncached` and
    `map_error` for `InvalidSimd` and `NonPrimitiveSimdType`)
  - `compiler/rustc_ty_utils/src/abi.rs` (`pointee_info_at` ignoring pointee
    layout errors via `.ok()`)
  - `compiler/rustc_const_eval/src/const_eval/machine.rs:552-585`
    (`InterpCx::emulate_intrinsic_by_name` handling `assert_inhabited`,
    `assert_zero_valid`, and `assert_mem_uninitialized_valid`)
  - `compiler/rustc_codegen_ssa/src/mir/block.rs:868-925, 1460-1555`
    (`codegen_panic_intrinsic` and `codegen_inline_asm`)
  - `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:90-370` and
    `compiler/rustc_codegen_ssa/src/diagnostics.rs:723-980` (`errors.rs:714` at
    `f8a08b688`) (`codegen_intrinsic_call` and `InvalidMonomorphization`)
  - `compiler/rustc_codegen_ssa/src/mir/mod.rs:329-361` (`allocate_local`)
  - `compiler/rustc_codegen_llvm/src/asm.rs:26-260` (`codegen_inline_asm`)
  - `compiler/rustc_driver_impl/src/lib.rs:315-332` (`run_compiler` ordering of
    `analysis(())`, `pretty::emit_mir(tcx)`, and
    `Linker::codegen_and_build_linker`)
  - `compiler/rustc_session/src/config.rs:911-922`
    (`OutputTypes::should_codegen` returning `true` for `OutputType::Mir`)
- **`rust-lang/reference` (`82da570bafd9efed421bdbae0f8603ede8dd308b`):**
  - `src/expressions/block-expr.md` (const block evaluation rules)
- **`google/zerocopy` (`8fb35253fbc703cb2cd0997f4efcda76cf9062b6`):**
  - `zerocopy/src/util/macros.rs:655-685` (`static_assert!` and `const_assert!`)
- **`joshlf/anneal` (`e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):**
  - `trusted/rustc-capture/src/lib.rs:219-243, 310-335, 371-447, 1141-1305`
    (`invoke_rustc_mir`, `scan_crate_functions`, `parse_mir_bodies`)

## Revalidation

To revalidate the empirical findings on a newer `rustc` toolchain from this
report package directory:

1. **Verify preserved support file integrity:**
   ```bash
   sha256sum probes/*.rs pme_capture_probe/src/lib.rs pme_capture_probe/driver.rs \
     pme_capture_probe/driver_output.txt pme_capture_probe/emitted_opt0.mir \
     pme_capture_probe/emitted_opt1.mir
   ```
2. **Re-run the 5 category probes (`probes/p1_inline_const.rs` ..
   `probes/p5_codegen_abi_intrinsics_asm.rs`):**
   ```bash
   # Probe 1: Generic const block PME vs. concrete pre-mono failure
   rustc --crate-type=lib probes/p1_inline_const.rs
   ! rustc --crate-type=lib --cfg instantiate_fail probes/p1_inline_const.rs

   # Probe 2: Associated constant let _ = ... vs. zerocopy static_assert!
   ! rustc --crate-type=lib --cfg instantiate_fail_let_underscore probes/p2_assoc_const_zerocopy.rs
   ! rustc --crate-type=lib --cfg instantiate_fail_zerocopy probes/p2_assoc_const_zerocopy.rs

   # Probe 3: Dead-branch if false (fails) vs. after-return (passes)
   ! rustc --crate-type=lib --cfg call_if_false_const probes/p3_dead_branch_ctfe.rs
   ! rustc --crate-type=lib --cfg call_if_false_call probes/p3_dead_branch_ctfe.rs
   rustc --crate-type=lib --cfg call_after_return_const probes/p3_dead_branch_ctfe.rs

   # Probe 4: Indirection &Big<u32> (passes) vs. field projection &p.1 (fails)
   rustc --crate-type=lib probes/p4_layout_and_mono_limits.rs
   ! rustc --crate-type=lib --cfg call_size_overflow probes/p4_layout_and_mono_limits.rs
   ! rustc --crate-type=lib --cfg call_proj_ref_big probes/p4_layout_and_mono_limits.rs

   # Probe 5: Runtime assert_inhabited::<Void>() (passes) vs. const assert_inhabited (fails)
   ! rustc --crate-type=lib --cfg call_asm_const_fail probes/p5_codegen_abi_intrinsics_asm.rs
   ```
3. **Re-run the 16-case conditional-branch vs. divergence matrix
   (`probes/branch_vs_diverge_probe.rs`):**
   ```bash
   for cfg in trig_if_false_const trig_match_false_const trig_if_const_false_const \
              trig_let_b_false_if_b_const trig_if_false_call trig_match_false_call \
              trig_if_const_false_call trig_let_b_false_if_b_call; do
     ! rustc --crate-type=lib --emit=obj --cfg "$cfg" probes/branch_vs_diverge_probe.rs
   done
   for cfg in trig_after_return_const trig_after_return_call trig_after_break_const \
              trig_after_break_call trig_after_continue_const trig_after_continue_call \
              trig_after_loop_const trig_after_loop_call; do
     rustc --crate-type=lib --emit=obj --cfg "$cfg" probes/branch_vs_diverge_probe.rs
   done
   ```
4. **Re-run the in-process `rustc_driver` prototype (`pme_capture_probe/`):**
   ```bash
   SYSROOT="$(rustc --print sysroot)"
   rustc --edition=2021 pme_capture_probe/driver.rs \
     -L "$SYSROOT/lib" -C link-args="-Wl,-rpath,$SYSROOT/lib" \
     -o /tmp/pme_capture_driver
   /tmp/pme_capture_driver --edition=2021 --crate-type=lib pme_capture_probe/src/lib.rs
   ```

Revalidate this report when:

- Upstream `rust-lang/rust` modifies `SimplifyCfg::Initial`,
  `RequiredConstsVisitor`, `MentionedItems`, `SimplifyConstCondition`, or
  `collect_items_of_instance`.
- `google/zerocopy` changes the expansion of `static_assert!` or `const_assert!`
  in `zerocopy/src/util/macros.rs`.
- `joshlf/anneal` migrates `trusted/rustc-capture` from subprocess `--emit=mir`
  to in-process `rustc_driver` callbacks.
