-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_ast
module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Trusted.MirAst.Types
public import Trusted.MirAst.Places
public import Trusted.MirAst.Rvalues

@[expose] public section

namespace Trusted.MirAst

/-!
# MIR Terminators (`Trusted.MirAst.Terminators`)

Control-flow terminators, switch targets, unwind actions, and assertion kinds
for captured `Runtime(PostCleanup)` MIR.
-/

/-- Branch table for `TerminatorKind.switchInt`
(`rustc_middle::mir::SwitchTargets` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct SwitchTargets {
>     pub(super) values: SmallVec<[Pu128; 1]>,
>     pub(super) targets: SmallVec<[BasicBlock; 2]>,
> }"

Represented explicitly as `branches : List (BitVec 128 × BasicBlockId)` paired
with the fallback target `otherwise : BasicBlockId` (matching the comment in
`syntax.rs`: `normal: SmallVec<[(Pu128, BasicBlock); 1]>, otherwise:
BasicBlock`). -/
structure SwitchTargets where
  branches : List (BitVec 128 × BasicBlockId)
  otherwise : BasicBlockId

/-- Unwind continuation action on panicking terminators
(`rustc_middle::mir::UnwindAction` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum UnwindAction {
>     Continue,
>     Unreachable,
>     Terminate(UnwindTerminateReason),
>     Cleanup(BasicBlock),
> }" -/
inductive UnwindAction where
  | continue_
  | unreachable
  | terminate
  | cleanup (block : BasicBlockId)

/-- Built-in MIR `Assert` condition kind (`rustc_middle::mir::AssertKind` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum AssertKind<O> {
>     BoundsCheck { len: O, index: O },
>     Overflow(BinOp, O, O),
>     OverflowNeg(O),
>     DivisionByZero(O),
>     RemainderByZero(O),
>     ResumedAfterReturn(CoroutineKind),
>     ResumedAfterPanic(CoroutineKind),
>     ResumedAfterDrop(CoroutineKind),
>     MisalignedPointerDereference { required: O, found: O },
>     NullPointerDereference,
>     NullReferenceConstructed,
>     InvalidEnumConstruction(O),
> }"

Constructor correspondence:
- `.overflow op` corresponds to `AssertKind::Overflow(op, _, _)`.
- `.overflowNeg` corresponds to `AssertKind::OverflowNeg(_)`.
- `.divByZero` corresponds to `AssertKind::DivisionByZero(_)`.
- `.remByZero` corresponds to `AssertKind::RemainderByZero(_)`.
- `.boundsCheck` corresponds to `AssertKind::BoundsCheck { .. }`.
- `.misalignedPtrDeref` corresponds to
  `AssertKind::MisalignedPointerDereference { .. }`.
- `.nullPtrDeref` corresponds to `AssertKind::NullPointerDereference`.
- `.unsupported` represents all other `AssertKind` variants
  (`ResumedAfterReturn`, `ResumedAfterPanic`, `ResumedAfterDrop`,
  `NullReferenceConstructed`, and `InvalidEnumConstruction`), as well as
  `AssertKind::Overflow(BinOp::Cmp, _, _)` whose `BinOp` lowers to
  `.unsupported`. -/
inductive AssertKind where
  | overflow (op : BinOp)
  | overflowNeg
  | divByZero
  | remByZero
  | boundsCheck
  | misalignedPtrDeref
  | nullPtrDeref
  | unsupported

/-- Closed set of modeled `core` library calls in Profile v2
(`TerminatorKind.coreCall`). Every unmodeled external `Call` remains
`.unsupported`.

Additional `core::num` entries (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
- `.usizeWrappingSub`: `usize::wrapping_sub`
  (`library/core/src/num/uint_macros.rs#L2620`).
- `.usizeIsPowerOfTwo`: `usize::is_power_of_two`
  (`library/core/src/num/uint_macros.rs#L3859`).
- `.nonZeroGet`: `NonZero::<T>::get`
  (`library/core/src/num/nonzero.rs#L483`).
- `.nonZeroNewUnchecked`: `NonZero::<T>::new_unchecked`
  (`library/core/src/num/nonzero.rs#L421`). -/
inductive CoreCallOp where
  | sliceLen
  | sliceAsPtr
  | sliceAsMutPtr
  | sliceFromRawParts
  | sliceFromRawPartsMut
  | sliceGetUncheckedRangeTo
  | sliceGetUncheckedRangeFrom
  | ptrAdd (mutability : Mutability) (pointee : MirTy)
  | usizeUncheckedSub
  | usizeWrappingSub
  | usizeIsPowerOfTwo
  | nonZeroGet
  | nonZeroNewUnchecked

/-- A MIR basic-block terminator (`rustc_middle::mir::TerminatorKind` in
`compiler/rustc_middle/src/mir/syntax.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum TerminatorKind<'tcx> {
>     Goto { target: BasicBlock, loop_hint_attrs: ThinVec<UnrollAttr> },
>     SwitchInt { discr: Operand<'tcx>, targets: SwitchTargets },
>     UnwindResume,
>     UnwindTerminate(UnwindTerminateReason),
>     Return,
>     Unreachable,
>     Drop { place: Place<'tcx>, target: BasicBlock, unwind: UnwindAction,
>            replace: bool, drop: Option<BasicBlock> },
>     Call { func: Operand<'tcx>, args: Box<[Spanned<Operand<'tcx>>]>,
>            destination: Place<'tcx>, target: Option<BasicBlock>,
>            unwind: UnwindAction, call_source: CallSource, fn_span: Span },
>     TailCall { ... },
>     Assert { cond: Operand<'tcx>, expected: bool,
>              msg: Box<AssertMessage<'tcx>>,
>              target: BasicBlock, unwind: UnwindAction },
>     Yield { ... },
>     CoroutineDrop,
>     FalseEdge { real_target: BasicBlock, imaginary_target: BasicBlock },
>     FalseUnwind { real_target: BasicBlock, unwind: UnwindAction },
>     InlineAsm { ... },
> }"

Constructor correspondence:
- `.goto target` corresponds to `TerminatorKind::Goto { target, .. }`
  (`loop_hint_attrs` are diagnostic/optimization hints with no operational
  effect).
- `.switchInt discr targets` corresponds to
  `TerminatorKind::SwitchInt { discr, targets }`.
- `.return_` corresponds to `TerminatorKind::Return`.
- `.unreachable` corresponds to `TerminatorKind::Unreachable`.
- `.unwindResume` corresponds to `TerminatorKind::UnwindResume`.
- `.assert cond expected msg target unwind` corresponds to
  `TerminatorKind::Assert { cond, expected, msg, target, unwind }`.
- `.call callee args dst target unwind` corresponds to direct `FnDef`
  `TerminatorKind::Call`.
- `.unsupported` represents all other `TerminatorKind` variants
  (`UnwindTerminate`, `Drop`, indirect `Call`, `TailCall`, `Yield`,
  `CoroutineDrop`, `FalseEdge`, `FalseUnwind`, and `InlineAsm`). -/
inductive TerminatorKind where
  | goto (target : BasicBlockId)
  | switchInt (discr : Operand) (targets : SwitchTargets)
  | return_
  | unreachable
  | unwindResume
  | assert (cond : Operand) (expected : Bool) (msg : AssertKind)
      (target : BasicBlockId) (unwind : UnwindAction)
  | call (callee : DefId) (args : List Operand) (dst : Place)
      (target : Option BasicBlockId) (unwind : UnwindAction)
  | coreCall (op : CoreCallOp) (args : List Operand) (dst : Place)
      (target : Option BasicBlockId) (unwind : UnwindAction)
  | unsupported

end Trusted.MirAst

end
