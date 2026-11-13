# Construct-by-Construct Operational Semantics of Rust 1.99.1 Runtime MIR Across Miri, MiniRust, Codegen, and Anneal

## Summary

Defining a sound verification model or verified code generator for Rust
`Runtime` MIR requires reconciling four distinct semantic authorities that
consume or formalize MIR at the pinned **Rust 1.99.1** baseline
(`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1` at
`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`): the MIR syntax and phase validator
(`rustc_middle::mir::syntax` and `rustc_mir_transform::validate`), the CTFE and
Miri operational interpreter (`rustc_const_eval::interpret` and `src/tools/miri`),
the SSA codegen lowering (`rustc_codegen_ssa::mir` and `rustc_codegen_llvm`),
MiniRust (`minirust/minirust` `063d784186d3252bee242217f218223205c0b568`), and
Anneal's three MIR verification lineages:

1. **Complete construct-by-construct semantics and phase invariants:**
   `RuntimePhase` comprises three ordered sub-phases—`RuntimePhase::Initial`
   (entered at `RuntimeLowering`), `RuntimePhase::PostCleanup` (entered after
   drop elaboration and borrow-check cleanup in
   `mir_drops_elaborated_and_const_checked`), and `RuntimePhase::Optimized`
   (produced by `optimized_mir`). Across all `12` `StatementKind` variants, `14`
   `TerminatorKind` variants, `4` `UnwindAction` variants, `13` `Rvalue`
   variants, `4` `Operand` variants, `8` `ProjectionElem` (`PlaceElem`)
   variants, `12` `CastKind` variants, `26` `BinOp` variants, `3` `UnOp`
   variants, `7` `AggregateKind` variants, `2` `NonDivergingIntrinsic`
   variants, and `4` `ConstValue` representations, the MIR validator
   (`compiler/rustc_mir_transform/src/validate.rs:L950-L1665`) bans
   analysis-only constructs (`StatementKind::FakeRead`,
   `StatementKind::AscribeUserType`, `BorrowKind::Fake`, `Rvalue::CopyForDeref`,
   `TerminatorKind::FalseEdge`, `TerminatorKind::FalseUnwind`,
   `TerminatorKind::Yield`, `TerminatorKind::CoroutineDrop`, and non-`Unsize`
   `CastKind::PointerCoercion`s other than `ReifyFnPointer`,
   `ClosureFnPointer`, and `UnsafeFnPointer`) upon entering `Runtime` phases,
   while requiring `Runtime` phase for `StatementKind::SetDiscriminant`,
   `Rvalue::UnaryOp(UnOp::PtrMetadata, _)`, `AggregateKind::RawPtr`, and
   `ProjectionElem::OpaqueCast` removal.
2. **bidirectional UB divergences between Miri and `rustc_codegen_ssa`:**
   Codegen and Miri do not implement identical operational semantics:
   - **Where Miri is stricter than codegen:** Miri enforces Stacked Borrows (or
     Tree Borrows under `-Zmiri-tree-borrows`) on `Rvalue::Ref`,
     `Rvalue::RawPtr`, and `Rvalue::Use(_, WithRetag::Yes)`. In particular, in
     `compiler/rustc_const_eval/src/interpret/step.rs:L252-L275`,
     `Rvalue::RawPtr(kind, place)` checks `place_base_raw` (whether the root
     local of an indirect projection is already a raw pointer). When indexing
     through a reference (`_7 = &raw const (*_1)[_6]` where `_1: &[u32; 4]`),
     `place_base_raw` is `false`, so Miri retags `_7` with `RetagMode::Raw` at
     the element type `u32` (`4` bytes); under Stacked Borrows, subsequently
     offsetting `_7` via `BinOp::Offset(_7, 2)` and reading element `2` faults
     with UB (`tag does not exist in the borrow stack`), whereas Tree Borrows
     and all three Tier 1 hardware targets (`x86_64`, `aarch64`, `i686`) at
     `-O0` and `-O3` execute the access without fault. Miri also enforces strict
     int-to-ptr provenance tracking, full recursive validity checking on typed
     copies/assignments, and immediate deallocation on `StorageDead`.
   - **Where `rustc_codegen_ssa` / LLVM assumes stronger invariants than Miri
     detects without a read or branch:** On `ProjectionElem::Index(idx)`
     (`compiler/rustc_codegen_ssa/src/mir/place.rs:L291`), codegen
     unconditionally emits `getelementptr inbounds nuw`, assuming the index is
     non-negative (`nuw`) and in-bounds of an allocated object even when taking
     a raw pointer `&raw const (*ptr)[idx]`. On
     `NonDivergingIntrinsic::CopyNonOverlapping`
     (`compiler/rustc_codegen_ssa/src/mir/statement.rs:L108`), codegen computes
     the byte length via `bx.unchecked_sumul(count, elem_size)` (`mul nuw nsw`),
     making `count * elem_size > isize::MAX` immediate LLVM `poison` before
     `llvm.memcpy`. On `CastKind::Transmute` between scalars at `OptLevel != No`
     (`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:L462, L1164-L1199`),
     `assume_scalar_range` emits an explicit `@llvm.assume` asserting the
     source scalar's `valid_range` and non-nullness on SSA immediates.
3. **Dual-phase empirical census across 12 corpus crates (`1,914` MIR bodies):**
   Running `support/mir_census_tool.rs` on both `Runtime(PostCleanup)`
   (`11,715` basic blocks, `57,152` statements) and `Runtime(Optimized)`
   (`9,691` basic blocks, `45,739` statements) across `12` crates from the
   pinned crate corpus shows that MIR optimizations (`Inline`, `GVN`,
   `InstSimplify`, `CheckAlignment`, `LowerIntrinsics`) drastically shift
   construct frequencies: `StatementKind::Intrinsic(Assume)` rises from `0` to
   `117`, `CopyNonOverlapping` from `0` to `66`, `CastKind::Transmute` from `9`
   to `1,225`, `BinOp::Offset` from `0` to `645`, `BinOp::SubUnchecked` from `0`
   to `94`, `BinOp::AddUnchecked` from `0` to `22`, `BinOp::Cmp` from `0` to
   `27`, and `AggregateKind::RawPtr` from `0` to `148`.

## Applicability

These findings apply to tools, verifiers, and compiler backends consuming or
producing `rustc_middle::mir::Body` in **Rust 1.99.1** (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`) with **LLVM 23.1.1**
(`rust-lang/llvm-project` `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), compared
against **MiniRust** (`minirust/minirust`
`063d784186d3252bee242217f218223205c0b568`), **Miri 0.1.0** (`rust-lang/rust`
`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`), and **Anneal** (`joshlf/anneal` at
`0d2b7f8cc58a305af71b5799c7bcaddc42c472fa`,
`a7ac073219f4ec3c813431be8239a0405014d5c1`, and
`a4e9b0b39e44ee2c7dcd9b2ae9e3e9cd59613ac7`).

- **Exact observation:** All `MirPhase` validator rules, interpreter transitions,
  and SSA codegen methods were extracted directly from the pinned Rust `1.99.1`
  source tree. Custom MIR differential probes
  (`support/custom_mir_differential_probe.rs`) were compiled with `rustc 1.99.1`
  at `-C opt-level=0` and `-C opt-level=3` and executed across
  `x86_64-unknown-linux-gnu` (native), `aarch64-unknown-linux-gnu`
  (`qemu-aarch64`), `i686-unknown-linux-gnu` (`qemu-i386`), and Miri (under both
  Stacked Borrows and `-Zmiri-tree-borrows`).

## Findings

### 1. MIR Phase Progression and Validator Rules (`MirPhase` & `validate.rs`)

Basis: source (`compiler/rustc_middle/src/mir/syntax.rs:L42-L142`,
`compiler/rustc_mir_transform/src/validate.rs:L950-L1665`)

In `rustc 1.99.1`, `MirPhase` (`syntax.rs:L42-L95`) defines three major stages:
- `MirPhase::Built`
- `MirPhase::Analysis(AnalysisPhase::{Initial = 0, PostCleanup = 1})`
- `MirPhase::Runtime(RuntimePhase::{Initial = 0, PostCleanup = 1, Optimized = 2})`

Table 1 summarizes the exact phase-transition invariants enforced by
`CfgChecker` in `compiler/rustc_mir_transform/src/validate.rs`.

| Construct / Feature | Permitted Phases | Validator Rejection Condition in `validate.rs` | Lowering Pass Responsible |
| :--- | :--- | :--- | :--- |
| `StatementKind::FakeRead` | `Built`, `Analysis(*)` | `phase >= Runtime(Initial)` (`L1503`) | `RuntimeLowering` |
| `StatementKind::AscribeUserType` | `Built`, `Analysis(*)` | `phase >= Runtime(Initial)` (`L1495`) | `RuntimeLowering` |
| `BorrowKind::Fake(_)` on `Rvalue::Ref` | `Built`, `Analysis(*)` | `phase >= Runtime(Initial)` (`L1143`) | `RuntimeLowering` |
| `Rvalue::CopyForDeref` | `Built`, `Analysis(*)` | `phase >= Runtime(Initial)` (`L1200`) | `Derefer` / `RuntimeLowering` |
| `ProjectionElem::OpaqueCast` | `Built`, `Analysis(*)` | `phase >= Runtime(Initial)` (`L977`) | `RevealAll` (`RuntimeLowering`) |
| `TerminatorKind::FalseEdge` / `FalseUnwind` | `Built`, `Analysis(*)` | `phase >= Runtime(Initial)` (`L1655`) | `RuntimeLowering` |
| `TerminatorKind::Yield` / `CoroutineDrop` | `Built`..`Runtime(Initial)` | `phase >= Runtime(PostCleanup)` (`L1655`) | `StateTransform` |
| `StatementKind::SetDiscriminant` | `Runtime(*)` | `phase < Runtime(Initial)` (`L1554`) | Introduced by `Deaggregator` / `StateTransform` |
| `Rvalue::UnaryOp(UnOp::PtrMetadata, _)` | `Runtime(*)` | `phase < Runtime(Initial)` (`L1178`) | Introduced by `LowerSliceLen` / `InstSimplify` |
| `AggregateKind::RawPtr` | `Runtime(*)` | `!matches!(phase, Runtime(_))` (`L1101`) | Introduced by `InstSimplify` / intrinsics |
| `CastKind::PointerCoercion(MutToConstPointer \| ArrayToPointer \| ClosureFnPointer(Safe))` | `Built`, `Analysis(Initial)` | `phase >= Analysis(PostCleanup)` (`L1327`) | Borrowck / `CleanupPostBorrowck` / `RuntimeLowering` |
| `ProjectionElem::Deref` in middle of projection | `Built`..`Runtime(Initial)` | `phase >= Runtime(PostCleanup)` if `Deref` is not first projection (`L961`) | `Derefer` |

---

### 2. Construct-by-Construct Semantics: Miri, MiniRust, Codegen, and Anneal

Basis: source + execution (`support/mir_construct_semantics_table.json`,
`support/custom_mir_differential_probe.rs`)

#### 2.1 Statements (`StatementKind<'tcx>`, `syntax.rs:L305-L456`)

| `StatementKind` Variant | Miri (`rustc_const_eval/src/interpret/step.rs`) | MiniRust (`spec/lang/step/statements.md`) | `rustc_codegen_ssa` (`mir/statement.rs`) | Anneal Coverage (`0d2b7f8cc` / `a7ac07321` / `a4e9b0b39`) |
| :--- | :--- | :--- | :--- | :--- |
| `Assign(Box<(Place, Rvalue)>)` | `eval_rvalue_into_place` (`step.rs:L152`). Evaluates destination `Place` first, then `Rvalue`; checks non-overlap on `Copy`/`Move` of in-memory places (`memory.rs:L1385`). | `Statement::Assign` (`statements.md:L13`). Evaluates `PlaceExpr` and `ValueExpr`, stores typed representation bytes into memory. | `cg_rvalue` into `LocalRef::Operand` (SSA immediate/pair) or `store_to_place` (`rvalue.rs:L90`). | Supported in all 3 lineages (`Statement.assign` / `Stmt.assign`). |
| `SetDiscriminant { place, variant_index }` | `write_discriminant` (`discriminant.rs:L28`). For `TagEncoding::Direct`, writes tag bits at `tag_field`. For `TagEncoding::Niche`, writes `niche_value` only if `variant_index != untagged_variant` (nop for `untagged_variant`). | `Statement::SetDiscriminant` (`statements.md:L57`). | `codegen_set_discr` (`place.rs:L258`). Calls `bx.abort()` if variant is uninhabited (`L267`), else stores tag at `tag_field` (or nop for `untagged_variant`). | Rejected in `0d2b7f8cc` (uses enum constant `Use`); supported in `a7ac07321` and `a4e9b0b39`. |
| `StorageLive(Local)` | `storage_live` (`stack.rs:L415`). Marks local live (uninitialized). If already live, deallocates prior backing allocation first. | `Statement::StorageLive` (`statements.md:L160`). UB if local is already live (`!frame.locals.contains_key`). | `cg_place.storage_live(bx)` (`statement.rs:L73`) -> `@llvm.lifetime.start.p0(ptr)` on `LocalRef::Place`. Nop for SSA `LocalRef::Operand`. | Supported in all 3 lineages (`0d2b7f8cc` faults if already live; `a7ac07321` bumps slot generation). |
| `StorageDead(Local)` | `storage_dead` (`stack.rs:L472`). Deallocates local backing store, invalidating all outstanding pointers/tags to that local. | `Statement::StorageDead` (`statements.md:L160`). Deallocates local if live; nop if already dead. | `cg_place.storage_dead(bx)` (`statement.rs:L81`) -> `@llvm.lifetime.end.p0(ptr)`. Nop for SSA `LocalRef::Operand`. | Supported in all 3 lineages. |
| `PlaceMention(Box<Place>)` | `eval_place` (`step.rs:L102`). Checks alignment and bounds of dereferenced pointers along `Place` when `-Zmiri-check-place-mention` is active, without reading bytes. | `Statement::PlaceMention` (`statements.md:L42`). Evaluates `PlaceExpr` (checking deref validity) and discards result. | Complete nop (`statement.rs:L119`) — does not evaluate `Place` or emit GEP! | Rejected in `0d2b7f8cc`; supported as `Stmt.placeMention` in `a7ac07321` and `a4e9b0b39`. |
| `Intrinsic(Assume(Operand))` | Reads `bool` operand; throws `UndefinedBehaviorInfo::AssumeFalse` if `false` (`step.rs:L119`). | `IntrinsicOp::Assume` (`intrinsics.md:L119`). | `bx.assume(op_val.immediate())` (`statement.rs:L91`) -> `call void @llvm.assume(i1)`. | Supported in `a7ac07321` and `a4e9b0b39` (`NonDivergingIntrinsic.assume`). |
| `Intrinsic(CopyNonOverlapping(cno))` | `copy_nonoverlapping` (`step.rs:L125`). Checks `src` and `dst` alignment (`pointee.align`), `count * size <= isize::MAX`, dereferenceability, and disjoint ranges even when `count == 0` (alignment + non-null). | Lowered to memory copy / load-store with disjointness check. | `bytes = bx.unchecked_sumul(count, elem_size)` (`mul nuw nsw`) + `bx.memcpy(dst, align, src, align, bytes)` (`statement.rs:L93-L115`). | Supported in `a7ac07321` and `a4e9b0b39` (`NonDivergingIntrinsic.copyNonOverlapping`). |
| `Coverage` / `ConstEvalCounter` / `Nop` | `ConstEvalCounter` ticks fuel counter; others nop. | Nop / omitted. | `Coverage` emits counter metadata; others nop (`statement.rs:L86, L118, L121`). | `Nop` in all 3; `coverage` and `constEvalCounter` in `a7ac07321` and `a4e9b0b39`. |

#### 2.2 Terminators and Unwind Actions (`TerminatorKind<'tcx>`, `syntax.rs:L683-L1033`)

Every unwinding terminator (`Drop`, `Call`, `Assert`, `FalseUnwind`, `InlineAsm`)
carries an `UnwindAction` (`syntax.rs:L1008-L1022`):
- `UnwindAction::Continue`: unwinds out of the current frame (`resume` in LLVM).
- `UnwindAction::Cleanup(BasicBlock)`: jumps to the cleanup landing pad block
  (`invoke ... to label %target unwind label %cleanup`).
- `UnwindAction::Terminate(UnwindTerminateReason::{Abi, InCleanup})`: calls the
  nounwind termination landing pad (`core::panicking::panic_cannot_unwind` for
  `Abi`, `core::panicking::panic_in_cleanup` for `InCleanup`;
  `compiler/rustc_codegen_ssa/src/mir/block.rs:L1315-L1338`).
- `UnwindAction::Unreachable`: unwinding into this edge is immediate UB;
  `rustc_codegen_ssa` omits the landing pad and marks the call `nounwind` (or
  emits an `unreachable` landing pad).

| `TerminatorKind` Variant | Miri (`rustc_const_eval/src/interpret/terminator.rs`) | MiniRust (`spec/lang/step/terminators.md`) | `rustc_codegen_ssa` (`mir/block.rs`) | Anneal Coverage (`0d2b7f8cc` / `a7ac07321` / `a4e9b0b39`) |
| :--- | :--- | :--- | :--- | :--- |
| `Goto { target }` | Jumps to `target`. | `Terminator::Goto`. | `bx.br(llblock)`. | All 3 lineages. |
| `SwitchInt { discr, targets }` | Evaluates `discr` as scalar int/char/bool (`to_scalar_int`), branches to matching `u128` arm or `otherwise` (`terminator.rs:L51`). | `Terminator::Switch` (`terminators.md:L34`). | `bx.cond_br` (2 targets) or `bx.switch` (`block.rs:L476-L525`). If `discr` is `u8`/`i8` known to be `0..=1`, emits `unchecked_utrunc` to `i1`. | All 3 lineages (`switchInt` / `switchIntGeneral`). |
| `Return` | Validates return place `_0`, pops stack frame, copies return value to caller destination (`stack.rs`). | `Terminator::Return` (`terminators.md:L295`). Checks `_0` initialized and valid. | Packs `_0` according to `FnAbi.ret` (`PassMode::Direct`, `Pair`, `Cast`, `Indirect`) and emits `ret` (`block.rs:L530-L605`). | All 3 lineages (`ret` / `return_`). |
| `Unreachable` | Throws `UndefinedBehaviorInfo::Unreachable` (`terminator.rs:L85`). | `Terminator::Unreachable` (`terminators.md:L50`). Immediate UB. | Emits `bx.unreachable()` (`block.rs:L607`). | All 3 lineages (`unreachable`, faults as UB). |
| `Drop { place, target, unwind, replace, drop }` | Looks up `Instance::resolve_drop_in_place(tcx, ty)` and pushes call frame (`terminator.rs:L93`). | Lowered before MiniRust to `Terminator::Call` of drop glue. | Emits call/invoke to `drop_in_place::<T>(place)` if `ty.needs_drop()`, else `br target` (`block.rs:L610-L660`). | Rejected in `0d2b7f8cc`; modeled in `a7ac07321` and `a4e9b0b39` (`Terminator.drop`). |
| `Call { func, args, destination, target, unwind, .. }` | Resolves `FnDef`/`FnPtr`, checks ABI compatibility (`check_argument_compat`, `call.rs:L231`), evaluates intrinsics or pushes stack frame. | `Terminator::Call` / `Terminator::Intrinsic` (`terminators.md:L60, L458`). | Evaluates `func` and `args`, marshals via `FnAbi` (`PassMode`), emits `call` or `invoke`, writes `destination` or `unreachable` if `target: None`. | Rejected in `0d2b7f8cc`; `call` / `call1` / `callLayout` / `callAtomicLoad` in `a7ac07321` and `a4e9b0b39`. |
| `TailCall { func, args, .. }` | Pops current frame's locals, marshals args into callee frame reusing caller's return destination (`call.rs:L712`). | Modeled as tail frame replacement. | Emits `musttail call` followed immediately by `ret` (`block.rs:L1180-L1255`). | Modeled in `a7ac07321` and `a4e9b0b39` (`Terminator.tailCall`). |
| `Assert { cond, expected, msg, target, unwind }` | Reads `cond` as `bool`. If `cond == expected`, jumps to `target`. Otherwise, for `MisalignedPointerDereference` / `NullPointerDereference` / `InvalidEnumConstruction` throws UB directly; for arithmetic/bounds panics invokes panic hook (`terminator.rs:L125-L215`). | Lowered to `Switch` + panic/UB block. | Emits `icmp eq cond, expected` + `cond_br` to `target` or generated failure block calling `panic_*` / `panic_nounwind` (`block.rs:L665-L795`). | Rejected in `0d2b7f8cc`; `Terminator.assert` with `AssertFailKind::{unwind, abort, ub}` in `a7ac07321` and `a4e9b0b39`. |
| `UnwindResume` / `UnwindTerminate(reason)` | Continues stack unwinding or calls termination lang item (`terminator.rs:L70-L84`). | `Terminator::ResumeUnwind` / `StartUnwind` (`terminators.md:L379-L420`). | `resume` instruction or call to `panic_cannot_unwind` / `panic_in_cleanup` + `unreachable` (`block.rs:L440-L462`). | Modeled in `a7ac07321` and `a4e9b0b39`. |
| `InlineAsm { template, operands, options, targets, unwind, .. }` | Unsupported in CTFE; Miri supports only empty `nop`-style `asm!("")` unless shimmed (`src/tools/miri/src/shims/unix/ischia/` / `inline_asm.rs`). | Outside core MiniRust calculus (requires assembly contract). | `bx.inline_asm_call` (`block.rs:L798-L965`) -> `call asm [sideeffect] [alignstack]` or `callbr` when `Label` operands are present. | Syntactically represented (`Terminator.inlineAsm`), steps to `.unsupported` unless discharged by contract. |

#### 2.3 Operands, Places, Projections, Rvalues, Casts, and Operators

1. **Operands (`Operand<'tcx>`, `syntax.rs:L1282-L1314`):**
   - `Operand::Copy(Place)` and `Operand::Move(Place)`: In `Runtime(PostCleanup)`
     and `Runtime(Optimized)`, `rustc`'s MIR semantics treat `Move` and `Copy`
     identically for `Copy` types (`elaborate_drops` does not rewrite `Move` to
     `Copy` on `Copy` locals; in our 12-crate census, `PostCleanup` has `14,482`
     `Move` operands vs. `5,756` `Copy` operands, whereas `Optimized` rewrites
     many `Move`s to `Copy`s, flipping the ratio to `11,673` `Copy` vs. `9,377`
     `Move`). In Miri (`operand.rs:L715-L760`), `eval_operand` deinitializes the
     source place on `Move` only when `-Zmiri-Track-raw-ptr` / non-`Copy` drop
     flags apply; in `custom_mir_differential_probe.rs` (`mir_move_then_copy`),
     moving `x: i32` and then copying `x: i32` succeeds in Miri (both Stacked
     and Tree Borrows) and across `x86_64`, `aarch64`, and `i686` at `-O0` and
     `-O3`. Anneal's scalar MVP (`0d2b7f8cc`) conservatively overwrites the moved
     local with `.uninit`, whereas Anneal's byte-memory lineage (`a4e9b0b39`)
     matches Miri.
   - `Operand::Constant(Box<ConstOperand>)`: Holds `Const::Val(ConstValue, Ty)`,
     `Const::Unevaluated(UnevaluatedConst, Ty)`, or `Const::Ty(Ty, ty::Const)`
     (`compiler/rustc_middle/src/mir/interpret/value.rs:L36-L88`). `ConstValue`
     has four variants: `Scalar(Scalar)`, `ZeroSized`, `Slice { alloc_id, meta }`,
     and `Indirect { alloc_id, offset }`.
   - `Operand::RuntimeChecks(RuntimeChecks)`: Evaluates to `bool` (`UbChecks`,
     `ContractChecks`, `OverflowChecks`); folded by `RuntimeLowering` /
     `ConstProp` before codegen.

2. **Places and Projections (`ProjectionElem`, `syntax.rs:L1171-L1258`):**
   - `Deref`: Dereferences `&T`, `&mut T`, `*const T`, `*mut T`, or `Box<T>`. In
     `Runtime(PostCleanup)` and `Runtime(Optimized)`, `Deref` may only appear as
     the **first** element `projection[0]` (`validate.rs:L961`).
   - `Field(FieldIdx, Ty)`: Projects to field `idx` using `layout.fields.offset(idx)`.
     In `rustc_codegen_ssa` (`place.rs:L186`), emits `inbounds_ptradd`
     (`getelementptr inbounds nuw i8, ptr, i64 offset`).
   - `Downcast(Option<Symbol>, VariantIdx)`: Narrows `layout` to
     `layout.for_variant(cx, variant_idx)` (`place.rs:L302`) at offset `0`. Does
     **not** check the active discriminant by itself.
   - `Index(Local)` and `ConstantIndex { offset, min_length, from_end }`:
     Projects into `[T; N]` or `[T]`. In `rustc_codegen_ssa` (`place.rs:L291`),
     emits `inbounds_nuw_gep` (`getelementptr inbounds nuw <T>, ptr, i64 %idx`).
   - `Subslice { from, to, from_end }`: Slices `[T; N]` or `[T]` in slice
     patterns.

3. **Rvalues, Casts, and Binary/Unary Operators (`syntax.rs:L1342-L1698`):**
   - `Rvalue::Use(Operand, WithRetag)`: Copies operand; if `WithRetag::Yes`
     (inserted where `Retag` statements used to exist prior to Rust 1.98), Miri
     retags reference values (`step.rs:L179-L184`).
   - `Rvalue::Ref(Region, BorrowKind, Place)` and `Rvalue::RawPtr(RawPtrKind, Place)`:
     Create references or raw pointers. Note `RawPtrKind::FakeForPtrMetadata`
     (`syntax.rs:L191`), which creates a raw pointer for `PtrMetadata` extraction
     without triggering a Miri retag (`step.rs:L266`).
   - `Rvalue::Cast(CastKind, Operand, Ty)`: Covers `IntToInt` (sign/zero extend
     or truncate), `FloatToInt` (saturating round-toward-zero in Rust!),
     `IntToFloat`, `FloatToFloat`, `PtrToPtr`, `FnPtrToPtr`,
     `PointerExposeProvenance`, `PointerWithExposedProvenance`,
     `PointerCoercion(Unsize | ReifyFnPointer | ClosureFnPointer | UnsafeFnPointer)`,
     `Transmute`, `BoxDerefTransmute`, and `Subtype`.
   - `Rvalue::BinaryOp(BinOp, Box<(Operand, Operand)>)`:
     - Wrapping arithmetic (`Add`, `Sub`, `Mul`), checked arithmetic returning
       `(T, bool)` (`AddWithOverflow`, `SubWithOverflow`, `MulWithOverflow` —
       merged into `BinaryOp` in Rust 1.99 rather than a separate
       `CheckedBinaryOp` rvalue!), and UB-on-overflow arithmetic (`AddUnchecked`,
       `SubUnchecked`, `MulUnchecked` -> `add/sub/mul nsw`/`nuw` in
       `rustc_codegen_llvm/src/builder.rs:L536-L541`).
     - Division/remainder (`Div`, `Rem`): integer division by zero or signed
       `INT_MIN / -1` is UB in MIR (`operator.rs:L215-L240`; surface Rust emits
       explicit `Assert` terminators before `Div`/`Rem`).
     - Shifts (`Shl`, `Shr`, `ShlUnchecked`, `ShrUnchecked`): `Shl` and `Shr`
       mask the shift amount by `bit_width - 1` (`rem_euclid(l_bits)` in
       `operator.rs:L131-L137` and `and` mask in `rustc_codegen_ssa`), whereas
       `ShlUnchecked` and `ShrUnchecked` throw UB in Miri (`operator.rs:L160`)
       and emit unmasked LLVM `shl`/`lshr`/`ashr` (returning `poison` when
       `shift >= bit_width`)!
     - Comparisons (`Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`, and three-way `Cmp`
       returning `core::cmp::Ordering` encoded as `-1i8`, `0i8`, `+1i8`).
     - Pointer offset (`BinOp::Offset`): `inbounds` pointer arithmetic by
       `count * size_of::<T>()` bytes (`operator.rs:L352`, `rvalue.rs:L973-L975`).

---

### 3. Empirical Frequency Census Across 12 Corpus Crates (`PostCleanup` vs. `Optimized`)

Basis: execution (`support/mir_census_tool.rs`, `support/mir_construct_census.json`)

Running `support/mir_census_tool.rs` under `rustc 1.99.1` (`-C opt-level=3`) on
`12` crates from the shared corpus (`arrayvec`, `bitflags`, `cfg_if`,
`equivalent`, `hashbrown`, `itoa`, `log`, `memchr`, `once_cell`, `ryu`,
`smallvec`, `unicode_ident`; `1,914` MIR bodies) yields the exact construct
distribution in Table 2.

| Construct Category & Variant | `Runtime(PostCleanup)` Count | `Runtime(PostCleanup)` Share | `Runtime(Optimized)` Count | `Runtime(Optimized)` Share |
| :--- | ---: | ---: | ---: | ---: |
| **Total Basic Blocks** | `11,715` | 100.0% | `9,691` | 100.0% |
| **Statements (`StatementKind`)** | **`57,152`** | **100.0%** | **`45,739`** | **100.0%** |
| — `StorageDead` | `20,383` | 35.66% | `15,349` | 33.56% |
| — `StorageLive` | `18,532` | 32.43% | `13,697` | 29.95% |
| — `Assign` | `18,237` | 31.91% | `16,510` | 36.10% |
| — `Intrinsic(Assume)` | `0` | 0.00% | `117` | 0.26% |
| — `Intrinsic(CopyNonOverlapping)` | `0` | 0.00% | `66` | 0.14% |
| **Terminators (`TerminatorKind`)** | **`11,715`** | **100.0%** | **`9,691`** | **100.0%** |
| — `Call` | `5,153` | 43.99% | `2,525` | 26.05% |
| — `Goto` | `2,079` | 17.75% | `2,675` | 27.60% |
| — `Return` | `1,908` | 16.29% | `1,908` | 19.69% |
| — `SwitchInt` | `1,443` | 12.32% | `1,714` | 17.69% |
| — `Drop` | `429` | 3.66% | `387` | 3.99% |
| — `UnwindResume` | `321` | 2.74% | `172` | 1.77% |
| — `Assert` | `194` | 1.66% | `67` | 0.69% |
| — `Unreachable` | `188` | 1.60% | `243` | 2.51% |
| **Rvalues (`Rvalue`)** | **`18,237`** | **100.0%** | **`16,510`** | **100.0%** |
| — `Use(WithRetag::Yes)` | `8,539` | 46.82% | `4,757` | 28.81% |
| — `Ref(Shared)` | `3,752` | 20.57% | `1,047` | 6.34% |
| — `BinaryOp` | `1,763` | 9.67% | `3,438` | 20.82% |
| — `Aggregate` | `1,431` | 7.85% | `2,202` | 13.34% |
| — `Ref(Mut)` | `1,253` | 6.87% | `486` | 2.94% |
| — `Cast` (`Transmute` / `IntToInt` / `PtrToPtr` / `Unsize`) | `692` | 3.79% | `2,992` | 18.12% |
| — `Use(WithRetag::No)` | `389` | 2.13% | `355` | 2.15% |
| — `Discriminant` | `330` | 1.81% | `491` | 2.97% |
| — `UnaryOp` (`PtrMetadata` / `Not` / `Neg`) | `65` | 0.36% | `264` | 1.60% |
| — `RawPtr(Const \| Mut)` | `20` | 0.11% | `477` | 2.89% |
| — `Repeat` | `3` | 0.02% | `1` | 0.01% |

## Boundaries

- **Inline assembly and coroutine state machines (`not examined` in differential
  execution):** `TerminatorKind::InlineAsm` is target-ISA-specific and rejected
  by Miri unless shimmed; `Yield` and `CoroutineDrop` are lowered by
  `StateTransform` before `Runtime(PostCleanup)`.
- **Unresolved Stacked Borrows vs. Tree Borrows specification:** Rust's aliasing
  model is not yet normatively finalized between Stacked Borrows and Tree
  Borrows; as demonstrated by `Rvalue::RawPtr` on `(*_1)[_6]`, the two models
  disagree on raw-pointer element projection from references.

## Evidence

- **Primary upstream sources:**
  - `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`:
    - `compiler/rustc_middle/src/mir/syntax.rs:L42-L1698` (`MirPhase`,
      `StatementKind`, `TerminatorKind`, `UnwindAction`, `ProjectionElem`,
      `Operand`, `Rvalue`, `CastKind`, `AggregateKind`, `UnOp`, `BinOp`).
    - `compiler/rustc_mir_transform/src/validate.rs:L950-L1665` (`CfgChecker`
      phase and type invariants).
    - `compiler/rustc_const_eval/src/interpret/{step.rs,terminator.rs,operand.rs,place.rs,operator.rs,cast.rs,discriminant.rs,intrinsics.rs}`.
    - `compiler/rustc_codegen_ssa/src/mir/{statement.rs,block.rs,rvalue.rs,operand.rs,place.rs}`
      and `compiler/rustc_codegen_llvm/src/builder.rs:L536-L995`.
  - `minirust/minirust` @ `063d784186d3252bee242217f218223205c0b568`:
    `spec/lang/syntax.md` and `spec/lang/step/{statements.md,terminators.md,expressions.md,operators.md,intrinsics.md}`.
  - `joshlf/anneal` @ `0d2b7f8cc58a305af71b5799c7bcaddc42c472fa`
    (`trusted/lean/Trusted/Mvp/{Syntax.lean,Semantics.lean}`),
    `a7ac073219f4ec3c813431be8239a0405014d5c1`
    (`trusted/lean/Trusted/{MirAst.lean,MirSemantics.lean}`), and
    `a4e9b0b39e44ee2c7dcd9b2ae9e3e9cd59613ac7`
    (`trusted/lean/Trusted/Rustc/V2026_08_01/`).
- **Preserved support artifacts:**
  - [`support/mir_construct_semantics_table.json`](support/mir_construct_semantics_table.json)
  - [`support/mir_construct_census.json`](support/mir_construct_census.json)
  - [`support/mir_census_tool.rs`](support/mir_census_tool.rs)
  - [`support/custom_mir_differential_probe.rs`](support/custom_mir_differential_probe.rs)

## Revalidation

To revalidate the custom-MIR differential suite across Tier 1 targets and Miri:

```bash
SYSROOT=$(rustc +1.99.1-x86_64-unknown-linux-gnu --print sysroot)
LLD="$SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld"
for opt in 0 3; do
  RUSTC_BOOTSTRAP=1 rustc +1.99.1-x86_64-unknown-linux-gnu --edition 2021 \
    --target x86_64-unknown-linux-gnu -C opt-level=$opt -C panic=abort \
    -C linker="$LLD" -C linker-flavor=ld.lld \
    reports/rustc-mir-construct-semantics-miri-minirust-and-codegen/support/custom_mir_differential_probe.rs \
    -o /tmp/cmir_x86_64 && /tmp/cmir_x86_64
done
```
