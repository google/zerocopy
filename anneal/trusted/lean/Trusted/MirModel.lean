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
`TerminalOut`, `LocalSlot`, `Choice`) and total list lookup/update helpers
(`getElem?`, `setElem?`) shared across $M_{\text{anneal}}$
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

/-- Caller-visible memory allocation descriptor. -/
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

/-- Local slot state in an active stack frame
(`compiler/rustc_const_eval/src/interpret/stack.rs`, `rust-lang/rust`
`8144389c895da997dbdecaa635e41d6a50be6ffd`):

> "pub(super) enum LocalValue<Prov: Provenance = CtfeProvenance> {
>     ...
>     Dead,
>     ...
>     Live(Operand<Prov>),
> }"

- `dead`: Storage is not currently allocated (`LocalValue::Dead`).
- `live none`: Storage is allocated (`StorageLive`) but uninitialized
  (`LocalValue::Live(Operand::Immediate(Immediate::Uninit))`).
- `live (some val)`: Storage is allocated and holds initialized value `val`. -/
inductive LocalSlot where
  | dead
  | live (val : Option Val)

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
