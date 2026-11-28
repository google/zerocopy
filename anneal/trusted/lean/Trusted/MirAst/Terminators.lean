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
`compiler/rustc_middle/src/mir/syntax.rs:1030-1044`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "pub enum UnwindAction {
>     /// No action is to be taken. Continue unwinding.
>     ...
>     Continue,
>     /// Triggers undefined behavior if unwind happens.
>     Unreachable,
>     /// Terminates the execution if unwind happens.
>     ...
>     Terminate(UnwindTerminateReason),
>     /// Cleanups to be done.
>     Cleanup(BasicBlock),
> }"

Constructor correspondence: `.continue_`, `.unreachable`, and `.terminate`
correspond 1:1 to `Continue`, `Unreachable`, and `Terminate(_)`. Capture drops
the `UnwindTerminateReason`, which only selects the panic message. Capture
refuses `Cleanup(_)` on `Assert` and `Call` terminators, so `.cleanup` never
reaches $M_{\text{anneal}}$ from capture. Neither profile ever unwinds:
non-optional failed `Assert`s, failed optional overflow `Assert`s when
`overflowChecks = true`, and diverging `core::panicking::*` calls step to
`.done (.aborted _)` only under `--panic abort` without a crate-local
`#[panic_handler]` and with a non-cleanup unwind action; every other panic path
faults with `.unsupported` or `.undefined`. -/
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
(`TerminatorKind.coreCall`). Capture (`core_call_op` for returning calls and
`terminator` for diverging `.panicAbort` in
`trusted/rustc-capture/src/extract.rs`) maps a direct `FnDef` call to one of
these constructors only when the callee is the sysroot `core` function below.
Every other external `Call` remains `.unsupported`.

- `.sliceLen` is `core::slice::<impl [T]>::len` (`execCoreCallOp`).
- `.sliceGetUncheckedRangeTo` and `.sliceGetUncheckedRangeFrom` are
  `core::slice::<impl [T]>::get_unchecked` with index type
  `core::ops::RangeTo<usize>` and `core::ops::RangeFrom<usize>`
  (`sliceGetUncheckedCheck`). `get_unchecked_mut` is not captured.
- `.ptrAdd mutability pointee` is `core::ptr::const_ptr::<impl *const T>::add`
  (`.shared`) or `core::ptr::mut_ptr::<impl *mut T>::add` (`.mut`) with
  `T = pointee` (`ptrAddInMem`).
- `.usizeUncheckedSub` is `core::num::<impl usize>::unchecked_sub`.
- `.intToLeBytes width signed` is
  `core::num::<impl int>::to_le_bytes`
  (`library/core/src/num/{uint_macros,int_macros}.rs`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "Returns the memory representation of this integer as a byte array in
  > little-endian byte order."
- `.arrayEq elem len` is structural `<[T; N] as PartialEq>::eq`
  (`library/core/src/array/equality.rs`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "Arrays are compared element-wise, and don't add any padding between
  > elements, so when the elements are `BytewiseEq`, we can compare the entire
  > array at once."
- `.sliceIndexRange`, `.sliceIndexRangeFrom`, `.sliceIsEmpty`, `.sliceSplitAt`,
  `.numIsMultipleOf`, `.numCheckedAdd`, `.numCheckedMul`, `.numCheckedSub`,
  `.numSaturatingAdd`, `.numWrappingShl`, `.numWrappingShr`, `.numLeadingZeros`,
  `.numOverflowingAdd`, `.numOverflowingSub`, `.cmpMin`, `.cmpMax`,
  `.memReplace`, `.optionIsSome`, `.optionIsNone`, `.optionTake`, and
  `.optionUnwrap` model the corresponding `core` slice, scalar, `cmp`, `mem`,
  and `Option` operations (`Trusted.MirSemantics.CoreContracts`).
- `.partialEqNe ty` is the provided `core::cmp::PartialEq::ne` method
  (`!self.eq(other)`, quoted at `TerminatorKind.callNe`) on `T = ty`, a
  primitive type or a fixed array thereof, whose `eq` is structural.
- `.panicAbort` is a diverging call (`target = none`) to
  `core::panicking::{panic, panic_nounwind}` taking its evaluated shared
  `&'static str` operand (`args = [expr]`,
  `library/core/src/panicking.rs:138,224`, same pin; see `evalCorePanicAbort`
  and `validatePanicAbortArgs`):

  > "pub const fn panic(expr: &'static str) -> !"
  > "pub const fn panic_nounwind(expr: &'static str) -> !"

Each semantic definition cited above quotes the corresponding `core` safety
contract at `rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`. -/
inductive CoreCallOp where
  | sliceLen
  | sliceGetUncheckedRangeTo
  | sliceGetUncheckedRangeFrom
  | sliceIndexRange (mutability : Mutability) (elem : MirTy)
  | sliceIndexRangeFrom (mutability : Mutability) (elem : MirTy)
  | sliceIsEmpty (elem : MirTy)
  | sliceSplitAt (mutability : Mutability) (elem : MirTy)
  | numIsMultipleOf (width : IntWidth) (signed : Bool)
  | numCheckedAdd (width : IntWidth) (signed : Bool)
  | numCheckedMul (width : IntWidth) (signed : Bool)
  | numCheckedSub (width : IntWidth) (signed : Bool)
  | numSaturatingAdd (width : IntWidth) (signed : Bool)
  | numWrappingShl (width : IntWidth) (signed : Bool)
  | numWrappingShr (width : IntWidth) (signed : Bool)
  | numLeadingZeros (width : IntWidth) (signed : Bool)
  | numOverflowingAdd (width : IntWidth) (signed : Bool)
  | numOverflowingSub (width : IntWidth) (signed : Bool)
  | cmpMin (width : IntWidth) (signed : Bool)
  | cmpMax (width : IntWidth) (signed : Bool)
  | memReplace (ty : MirTy)
  | optionIsSome (inner : MirTy)
  | optionIsNone (inner : MirTy)
  | optionTake (inner : MirTy)
  | optionUnwrap (inner : MirTy)
  | ptrAdd (mutability : Mutability) (pointee : MirTy)
  | usizeUncheckedSub
  | intToLeBytes (width : IntWidth) (signed : Bool)
  | arrayEq (elem : MirTy) (len : Nat)
  | panicAbort
  | vecNew (elem : MirTy)
  | vecWithCapacity (elem : MirTy)
  | vecLen
  | vecPush
  | vecResize
  | vecExtendFromSlice
  | vecIndex
  | vecIndexMut
  | vecDeref
  | vecDerefMut
  | vecReserve
  | boxFromVec
  | boxDeref
  | boxDerefMut
  | boxClone
  | boxNew (pointee : MirTy)
  | partialEqNe (ty : MirTy)

/-- Closed set of `core::num` primitive arithmetic operations supported via
pinned sysroot-body lowering (verified at capture time against `core`'s
`tcx.instance_mir`): checked-UB (`unchecked_{add,sub,mul}`) and wrapping
(`wrapping_{add,sub,mul}`) integer arithmetic.

This is the Profile v1 call path (`TerminatorKind.sysrootCall`). Profile v2
models its `core` calls atomically through `CoreCallOp` instead, and each
profile refuses the other's terminator. -/
inductive SysrootNumKind where
  | uncheckedAdd
  | uncheckedSub
  | uncheckedMul
  | wrappingAdd
  | wrappingSub
  | wrappingMul

/-- Typed `core::num` sysroot call descriptor (`op : SysrootNumOp`), specifying
the operation kind (`SysrootNumKind`) and the integer operand/return width and
signedness. -/
structure SysrootNumOp where
  kind : SysrootNumKind
  width : IntWidth
  signed : Bool

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
- `.call callee args dst target unwind` corresponds to a direct intra-crate
  `FnDef` `TerminatorKind::Call` whose callee is the captured body
  `Program.bodies[callee]`, executed in a new frame.
- `.coreCall op args dst target unwind` corresponds to a direct `FnDef`
  `TerminatorKind::Call` whose callee is the sysroot `core` function that
  `op` names (Profile v2).
- `.sysrootCall op args dst target unwind` corresponds to a pinned `core::num`
  `FnDef` `TerminatorKind::Call` verified against `core`'s `tcx.instance_mir`
  (Profile v1).
- `.callNe eqCallee args dst target unwind` corresponds to a direct `FnDef`
  `TerminatorKind::Call` of the provided `core::cmp::PartialEq::ne` method,
  executed as a call to the captured `PartialEq::eq` body
  `Program.bodies[eqCallee]` whose result is negated (Profile v2;
  `library/core/src/cmp.rs`, `rust-lang/rust`
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "fn ne(&self, other: &Rhs) -> bool {
  >     !self.eq(other)
  > }"
- `.drop place target unwind` corresponds to
  `TerminatorKind::Drop { place, target, unwind, .. }` on a place whose type
  has no drop glue (Profile v2; `compiler/rustc_middle/src/mir/syntax.rs`,
  `rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

  > "After drop elaboration: `Drop` terminators are a complete nop for types
  > that have no drop glue."
- `.unsupported` represents all other `TerminatorKind` variants
  (`UnwindTerminate`, other `Drop`s, indirect or unverified external `Call`,
  `TailCall`, `Yield`, `CoroutineDrop`, `FalseEdge`, `FalseUnwind`, and
  `InlineAsm`). -/
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
  | sysrootCall (op : SysrootNumOp) (args : List Operand) (dst : Place)
      (target : Option BasicBlockId) (unwind : UnwindAction)
  | callNe (eqCallee : DefId) (args : List Operand) (dst : Place)
      (target : Option BasicBlockId) (unwind : UnwindAction)
  | drop (place : Place) (target : BasicBlockId) (unwind : UnwindAction)
  | unsupported

end Trusted.MirAst

end
