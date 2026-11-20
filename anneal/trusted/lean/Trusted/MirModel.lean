-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Trusted.MirAst

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Shared MIR Value and Outcome Model (`Trusted.MirModel`)

Pure boundary data types (`FaultKind`, `StepResult`, `ScalarVal`, `PtrVal`,
`AllocByte`, `Val`, `Allocation`, `CallerMemory`, `Query`, `Out`,
`TerminalOut`, `MemPlace`, `LocalSlot`, `Choice`) and total list lookup/update
helpers (`getElem?`, `setElem?`) shared across $M_{\text{anneal}}$
(`Trusted.MirSemantics.*`) and $M_{\text{ref}}$
(`Trusted.Correspondence.*`).

Separating these pure data types from `Trusted.MirSemantics.*` lets Pass 2
`verifyRefEvaluatorIndependence` enforce module-origin exclusion over all
`Trusted.MirSemantics` and `Trusted.MirSemantics.*` operational rules while
preserving the canonical `Trusted.MirSemantics.*` names.
-/

/-- Operational fault classification in $M_{\text{anneal}}$, corresponding to
`InterpErrorKind` in `compiler/rustc_middle/src/mir/interpret/error.rs`
(`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub enum InterpErrorKind<'tcx> {
>     UndefinedBehavior(UndefinedBehaviorInfo<'tcx>),
>     InvalidProgram(InvalidProgramInfo<'tcx>),
>     Unsupported(UnsupportedOpInfo),
>     ResourceExhaustion(ResourceExhaustionInfo),
>     MachineStop(Box<dyn MachineStopType>),
> }"

- `undefined`: Modeled Rust Undefined Behavior (`UndefinedBehavior`).
- `unsupported`: Unmodeled MIR construct, type, or runtime feature
  (`Unsupported` / `InvalidProgram`).
Both falsify `WellFormed`, while remaining distinct in non-vacuity canaries
and any downstream soundness or refinement reasoning. -/
inductive FaultKind where
  | undefined
  | unsupported

/-- Single-step transition outcome of $M_{\text{anneal}}$. -/
inductive StepResult (State Out : Type) where
  | step (next : State)
  | done (out : Out)
  | fault (kind : FaultKind)

/-- Canonical scalar value with explicit width, signedness, and 128-bit payload,
corresponding to `rustc_middle::ty::ScalarInt` paired with its integer
`TyAndLayout` (`compiler/rustc_middle/src/ty/consts/int.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct ScalarInt { data: u128, size: NonZero<u8> }"

Well-formed scalars satisfy `truncateBits width bits == bits`. -/
structure ScalarVal where
  width : IntWidth
  signed : Bool
  bits : BitVec 128

/-- Canonical pointer/reference value (`AllocId` provenance + byte offset),
corresponding to `rustc_const_eval::interpret::Pointer`
(`compiler/rustc_middle/src/mir/interpret/pointer.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`). -/
structure PtrVal where
  allocId : Option AllocId
  offsetBytes : UInt64
  width : IntWidth := .isize

/-- Abstract byte in memory: uninitialized or initialized `UInt8` with optional
allocation provenance `AllocId`. -/
inductive AllocByte where
  | uninit
  | init (byte : UInt8) (prov : Option AllocId := none)

/-- Canonical boundary value used in `Query`, `Out`, and `TerminalOut` of
$M_{\text{anneal}}$. -/
inductive Val where
  | scalar (v : ScalarVal)
  | ptr (p : PtrVal)
  | bool (b : Bool)
  | unit
  | enumVal (ty : EnumTy) (variant : Nat)
  | tuple (fields : List Val)
  | bytes (data : List AllocByte)

/-- Memory allocation: the caller-visible allocations of `CallerMemory` and the
stack allocations of $M_{\text{anneal}}$'s `Trusted.MirSemantics.MemoryState`,
corresponding to `rustc_middle::mir::interpret::Allocation`
(`compiler/rustc_middle/src/mir/interpret/allocation.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub struct Allocation<Prov: Provenance = CtfeProvenance, Extra = (),
>     Bytes = Box<[u8]>> {
>     /// The actual bytes of the allocation.
>     /// Note that the bytes of a pointer represent the offset of the pointer.
>     bytes: Bytes,
>     /// Maps from byte addresses to extra provenance data for each pointer.
>     ...
>     provenance: ProvenanceMap<Prov>,
>     /// Denotes which part of this allocation is initialized.
>     ...
>     init_mask: InitMask,
>     /// The alignment of the allocation to detect unaligned reads.
>     /// (`Align` guarantees that this is a power of two.)
>     pub align: Align,
>     /// `true` if the allocation is mutable.
>     ...
>     pub mutability: Mutability,
>     ..."

`bytes` combines `rustc`'s `bytes`, `init_mask`, and `provenance` into one
`AllocByte` per byte, so the allocation's size is `bytes.length`. `live` is
`false` once the allocation has been deallocated (`rustc` removes it from
`alloc_map`). -/
structure Allocation where
  allocId : AllocId
  alignLog2 : Nat
  mutability : Mutability
  bytes : List AllocByte
  live : Bool := true

/-- Snapshot of caller-visible allocations. -/
structure CallerMemory where
  allocations : List Allocation := []

/-- Per-invocation input query: function arguments and initial caller-visible
memory. -/
structure Query where
  args : List Val
  callerMem : CallerMemory := ⟨[]⟩

/-- Per-invocation normal return output: return value in `_0` and final
caller-visible memory. -/
structure Out where
  ret : Val
  callerMem : CallerMemory := ⟨[]⟩

/-- Observable terminal outcome of a well-formed execution. -/
inductive TerminalOut where
  | returned (out : Out)
  | unwound (callerMem : CallerMemory := ⟨[]⟩)

/-- Place in memory: the start of the bytes of a value at byte offset `offset`
inside allocation `allocId`, corresponding to the thin (unsized-metadata-free)
case of `rustc_const_eval::interpret::MemPlace`
(`compiler/rustc_const_eval/src/interpret/place.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub(super) struct MemPlace<Prov: Provenance = CtfeProvenance> {
>     /// The pointer can be a pure integer, with the `None` provenance.
>     pub ptr: Pointer<Option<Prov>>,
>     /// Metadata for unsized places. Interpretation is up to the type.
>     ...
>     pub meta: MemPlaceMeta<Prov>,
>     ..."

As in `rustc`, the alignment of an access comes from the layout of the
accessed type, not from the place. -/
structure MemPlace where
  allocId : AllocId
  offset : Nat

/-- Local slot state in an active stack frame, corresponding to `LocalValue`
and `Operand` (`compiler/rustc_const_eval/src/interpret/stack.rs` and
`compiler/rustc_const_eval/src/interpret/operand.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`) and to
`Miri.Interpreter.LocalValue`
(`vendor/lean-miri/Miri/Interpreter/Operand.lean`):

> "pub(super) enum LocalValue<Prov: Provenance = CtfeProvenance> {
>     /// This local is not currently alive, and cannot be used at all.
>     Dead,
>     /// A normal, live local.
>     /// Mostly for convenience, we re-use the `Operand` type here.
>     /// This is an optimization over just always having a pointer here;
>     /// we can thus avoid doing an allocation when the local just stores
>     /// immediate values *and* never has its address taken.
>     Live(Operand<Prov>),
> }"
> (`compiler/rustc_const_eval/src/interpret/stack.rs`)
>
> "pub(super) enum Operand<Prov: Provenance = CtfeProvenance> {
>     Immediate(Immediate<Prov>),
>     Indirect(MemPlace<Prov>),
> }"
> (`compiler/rustc_const_eval/src/interpret/operand.rs`)

- `dead`: storage is not allocated (`LocalValue::Dead`).
- `immediate none`: storage is live (`StorageLive`) but uninitialized
  (`Live(Operand::Immediate(Immediate::Uninit))`).
- `immediate (some val)`: storage is live and holds the value `val`
  (`Live(Operand::Immediate(..))`).
- `indirect place`: storage is live and the value's bytes are in memory at
  `place` (`Live(Operand::Indirect(..))`), after
  `Trusted.MirSemantics.forceAllocation` moved the local into a stack
  allocation. -/
inductive LocalSlot where
  | dead
  | immediate (val : Option Val)
  | indirect (place : MemPlace)

/-- Demonic nondeterministic choice input for a single step. -/
abbrev Choice := Nat

/-- Total list lookup by index without `Decidable` bounds proofs. -/
noncomputable def getElem? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getElem? xs n

/-- Total list update by index, returning `none` when `n` is out of bounds. -/
noncomputable def setElem? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
    match setElem? xs n v with
    | some xs' => some (x :: xs')
    | none => none

end Trusted.MirSemantics
