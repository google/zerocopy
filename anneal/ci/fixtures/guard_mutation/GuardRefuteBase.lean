-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics.Boundary

/-!
# Shared Helpers for Guard-Mutation Negative Refutation Fixtures

This module supplies minimal, self-contained proof combinators and MIR program
constructors for the guard-mutation fixtures under
`anneal/ci/fixtures/guard_mutation/`.

Why these helpers live outside `anneal/trusted/` and avoid importing
`Anneal.MirWp`:

1. Negative test fixtures do not belong inside the trusted computing base.
2. Importing only `Trusted.MirSemantics.Boundary` (and minimal `Init` modules)
   lets `ci/check_guard_mutation.py` recompile a single mutated semantics
   module and its refutation fixture in fractions of a second without
   rebuilding `theory/Anneal/`.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Prepend a single `Step` transition to a `Reaches` chain. -/
theorem reaches_cons {p : Program} {s₁ s₂ s₃ : State}
    (hStep : Step p s₁ (.step s₂)) (hRest : Reaches p s₂ s₃) :
    Reaches p s₁ s₃ := by
  induction hRest with
  | refl => exact Reaches.tail (Reaches.refl s₁) hStep
  | tail _ hLast ih => exact Reaches.tail ih hLast

/-- Fuel-bounded deterministic (`c = 0`) fault predicate over `evalStep`.

Used by negative refutation theorems so concrete UB programs reduce directly
by `rfl` when every required UB guard is active, and fail to type-check as
soon as the exercised guard is weakened or removed. -/
def execFaultFrom (p : Program) (k : FaultKind) : Nat → State → Prop
  | 0, _ => False
  | fuel + 1, s =>
      match evalStep p 0 s with
      | .step s' => execFaultFrom p k fuel s'
      | .fault k' => k' = k
      | .done _ => False

/-- Fuel-bounded deterministic (`c = 0`) normal-return predicate over
`evalStep`, used by `PositiveSanity` to confirm that mutated semantics
still accept ordinary UB-free programs. -/
def execDoneFrom (p : Program) (expected : TerminalOut) : Nat → State → Prop
  | 0, _ => False
  | fuel + 1, s =>
      match evalStep p 0 s with
      | .step s' => execDoneFrom p expected fuel s'
      | .done out => out = expected
      | .fault _ => False

/-- Whole-program deterministic fault check from `initState p q`. -/
def execFaultProg (p : Program) (fuel : Nat) (q : Query)
    (k : FaultKind) : Prop :=
  match initState p q with
  | .error k' => k' = k
  | .ok s₀ => execFaultFrom p k fuel s₀

/-- Whole-program deterministic normal-return check from `initState p q`. -/
def execDoneProg (p : Program) (fuel : Nat) (q : Query)
    (expected : TerminalOut) : Prop :=
  match initState p q with
  | .error _ => False
  | .ok s₀ => execDoneFrom p expected fuel s₀

/-- Lift `execFaultFrom` into existential `Reaches` + `Step` reachability. -/
theorem reaches_fault_of_execFrom {p : Program} {k : FaultKind} :
    ∀ {fuel : Nat} {s : State},
      execFaultFrom p k fuel s →
      ∃ s', Reaches p s s' ∧ Step p s' (.fault k)
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
      dsimp [execFaultFrom] at h
      cases hStep : evalStep p 0 s with
      | step s1 =>
        rw [hStep] at h
        match reaches_fault_of_execFrom h with
        | ⟨s', hReach, hFault⟩ =>
          exact ⟨s', reaches_cons ⟨0, rfl, hStep⟩ hReach, hFault⟩
      | fault k' =>
        rw [hStep] at h
        subst h
        exact ⟨s, Reaches.refl s, ⟨0, rfl, hStep⟩⟩
      | done _ =>
        rw [hStep] at h
        exact False.elim h

/-- Lift `execFaultProg` into `ReachesResult p q (.fault k)`.

Kept independent of `WellFormed` so `GuardRefuteBase` compiles cleanly even
under `Boundary.lean` mutations that weaken `WellFormed` itself. -/
theorem reachesResult_of_execFault {p : Program} {fuel : Nat} {q : Query}
    {k : FaultKind} (h : execFaultProg p fuel q k) :
    ReachesResult p q (.fault k) := by
  unfold ReachesResult
  unfold execFaultProg at h
  cases hInit : initState p q with
  | error k' =>
    rw [hInit] at h
    subst h
    rfl
  | ok s₀ =>
    rw [hInit] at h
    exact reaches_fault_of_execFrom h

/-- Lift `execDoneFrom` into `Reaches` + `Step (.done expected)`. -/
theorem reaches_done_of_execFrom {p : Program} {expected : TerminalOut} :
    ∀ {fuel : Nat} {s : State},
      execDoneFrom p expected fuel s →
      ∃ s', Reaches p s s' ∧ Step p s' (.done expected)
  | 0, _, h => False.elim h
  | fuel + 1, s, h => by
      dsimp [execDoneFrom] at h
      cases hStep : evalStep p 0 s with
      | step s1 =>
        rw [hStep] at h
        match reaches_done_of_execFrom h with
        | ⟨s', hReach, hDone⟩ =>
          exact ⟨s', reaches_cons ⟨0, rfl, hStep⟩ hReach, hDone⟩
      | done out =>
        rw [hStep] at h
        subst h
        exact ⟨s, Reaches.refl s, ⟨0, rfl, hStep⟩⟩
      | fault _ =>
        rw [hStep] at h
        exact False.elim h

/-- Lift `execDoneProg` into `Behavior p q expected`. -/
theorem behavior_of_execDone {p : Program} {fuel : Nat} {q : Query}
    {expected : TerminalOut} (h : execDoneProg p fuel q expected) :
    Behavior p q expected := by
  unfold Behavior ReachesResult
  unfold execDoneProg at h
  cases hInit : initState p q with
  | error _ =>
    rw [hInit] at h
    exact False.elim h
  | ok s₀ =>
    rw [hInit] at h
    exact reaches_done_of_execFrom h

/-- `u32` type descriptor (`IntWidth.i32`, unsigned). -/
noncomputable def u32Ty : MirTy := .int .i32 false

/-- `u8` type descriptor (`IntWidth.i8`, unsigned). -/
noncomputable def u8Ty : MirTy := .int .i8 false

/-- `i8` type descriptor (`IntWidth.i8`, signed). -/
noncomputable def i8Ty : MirTy := .int .i8 true

/-- Construct a scalar `Val` of width `w` and signedness `s` from `bits`. -/
noncomputable def scalarNatVal (w : IntWidth) (s : Bool) (bits : Nat) : Val :=
  .scalar ⟨w, s, BitVec.ofNat 128 bits⟩

/-- Construct a `u32` scalar `Val`. -/
noncomputable def u32Val (n : Nat) : Val := scalarNatVal .i32 false n

/-- Construct an `i8` scalar `Val` from its raw 8-bit two's-complement bits. -/
noncomputable def i8Val (bits : Nat) : Val := scalarNatVal .i8 true bits

/-- Empty 0-argument query. -/
noncomputable def queryEmpty : Query := { args := [] }

/-- Construct a single-block unit-scope program with the given locals,
argument count, statements, and terminator. -/
noncomputable def mkSingleBlockProg (argCount : Nat) (locals : List MirTy)
    (stmts : List StatementKind) (term : TerminatorKind := .return_) :
    Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := argCount
    locals := locals
    basicBlocks := [{ statements := stmts, terminator := term }]
  }]

/-- Construct a single-block binary-operator program
`_0 = op(copy _1, copy _2); return`. -/
noncomputable def mkBinOpProg (op : BinOp) (retTy lhsTy rhsTy : MirTy) :
    Program :=
  mkSingleBlockProg 2 [retTy, lhsTy, rhsTy]
    [.assign ⟨0, []⟩ (.binaryOp op (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))]

/-- Construct a single-block constant-return program `_0 = const(ty, bits)`. -/
noncomputable def mkConstRetProg (ty : MirTy) (bits : Nat) : Program :=
  mkSingleBlockProg 0 [ty]
    [.assign ⟨0, []⟩ (.use (.constant ⟨ty, .scalar (BitVec.ofNat 128 bits)⟩))]

/-- Fieldless enum `#[repr(u8)] enum ReprU8 { A = 10, B = 20 }` for tag
validation and uninitialized discriminant refutations. -/
noncomputable def reprU8EnumTy : EnumTy := {
  id := 1
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [10, 20]
}

end GuardMutation
