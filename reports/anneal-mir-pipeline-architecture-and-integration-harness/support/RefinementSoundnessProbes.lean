-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanized Soundness Probes for Anneal's MIR Pipeline and Refinement Architecture

Self-contained, zero-`sorry`, zero-axiom Lean 4 mechanization of the five core
soundness and architectural findings in this report:

1. **Path-sensitive `MirVal.uninit` and `isFullyInitFuel`** for partial moves out
   of composite places (`Operand::Move(_1.0)`), contrasting with both the
   non-destructive `Rvalue.field0` translation (`extract.rs:472-485`,
   `MirSemantics.lean:589-597`) and naive root-local deinitialization.
2. **`Stmt.placeMention` semantics** (`-Z mir-preserve-ub` retention vs.
   `RemovePlaceMention` erasure).
3. **Two-stage Post-Monomorphization Error (PME) completeness** (`ConstsTotal`
   and `MonoAdmitted`), contrasting with single-quantifier lockouts on
   `const { assert!(...) }` guards and vacuous implication preconditions on
   unsupported or oversized types.
4. **Compiler-inserted `Terminator.assert` vs. `Callee.panic`**, mechanizing the
   `bad_overflow(x: u8)` soundness counterexample (`x = 255`).
5. **Flat `BodyId` tables, frame-relative `returnRefsOk`, and in-place
   `lowerBody` simulation** with PC-canonicalized `MirReturn`.

Compatible with both `leanprover/lean4:v4.28.0` and `leanprover/lean4:v4.34.1`.
-/

namespace AnnealMirRefinementProbes

/-! ## Section 1: Path-Sensitive `MirVal.uninit` and Partial Moves -/

inductive PlaceElem where
  | deref
  | field (idx : Nat)
  deriving DecidableEq, Repr

structure Place where
  root : Nat
  proj : List PlaceElem := []
  deriving DecidableEq, Repr

inductive MirVal where
  | uninit
  | usize (n : Nat)
  | adt (fields : List MirVal)
  | refVal (target : Place)
  deriving BEq, Repr

mutual
def isFullyInitFuel : Nat → MirVal → Bool
  | 0, _ => false
  | _ + 1, .uninit => false
  | _ + 1, .usize _ => true
  | _ + 1, .refVal _ => true
  | f + 1, .adt fields => isFullyInitListFuel f fields

def isFullyInitListFuel : Nat → List MirVal → Bool
  | _, [] => true
  | f, v :: vs => isFullyInitFuel f v && isFullyInitListFuel f vs
end

def defaultInitFuel : Nat := 16

def listGetOpt : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => listGetOpt xs i

def listSetOpt : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, i + 1, v =>
      match listSetOpt xs i v with
      | some xs' => some (x :: xs')
      | none => none

abbrev Locals := Nat → Option MirVal

def updateLocal (locals : Locals) (idx : Nat) (val : Option MirVal) : Locals :=
  fun i => if i == idx then val else locals i

/-- Contrast 1A (Current Unsound Translation in `extract.rs:472-485` and
`MirSemantics.lean:589-597`): `Operand::Move(_1.0)` is translated to a
non-destructive `Rvalue.field0` read, leaving `_1` intact in `locals`. -/
def evalMoveField0NonDestructive (locals : Locals) (src : Nat) : Option (MirVal × Locals) :=
  match locals src with
  | some (.adt (f0 :: _)) => some (f0, locals)
  | _ => none

/-- Moving field `0` twice from a non-`Copy` struct succeeds under the
non-destructive `Rvalue.field0` translation. -/
theorem nonDestructiveField0_allows_double_move :
    let initLocals : Locals := fun i =>
      if i == 1 then some (.adt [.usize 10, .usize 42]) else none
    (do
      let (v1, locals1) ← evalMoveField0NonDestructive initLocals 1
      let (v2, _) ← evalMoveField0NonDestructive locals1 1
      pure (v1, v2)) = some (.usize 10, .usize 10) := rfl

/-- Contrast 1B (Naive Root-Local Deinitialization): Overwriting the entire
root local `_1` with `none` on `Operand::Move(_1.0)` destroys sibling field
`_1.1`. -/
def evalMoveFieldNaiveRootReset (locals : Locals) (src fieldIdx : Nat) :
    Option (MirVal × Locals) :=
  match locals src with
  | some (.adt fields) =>
      match listGetOpt fields fieldIdx with
      | some v => some (v, updateLocal locals src none)
      | none => none
  | _ => none

/-- Moving `_1.0` and then moving sibling field `_1.1` (`let a = p.0; let b = p.1;`)
fails closed (`none`) under naive root-local deinitialization. -/
theorem naiveRootReset_breaks_sibling_move :
    let initLocals : Locals := fun i =>
      if i == 1 then some (.adt [.usize 10, .usize 42]) else none
    (do
      let (v1, locals1) ← evalMoveFieldNaiveRootReset initLocals 1 0
      let (v2, _) ← evalMoveFieldNaiveRootReset locals1 1 1
      pure (v1, v2)) = none := rfl

/-- Path-sensitive projection evaluation with `isFullyInitFuel` checks at:
(a) terminal `proj = []` (whole-value read gate), and
(b) intermediate `.deref :: rest` (dereferenced aggregate gate). -/
def evalProjFuel (locals : Locals) : Nat → MirVal → List PlaceElem → Option MirVal
  | 0, _, _ => none
  | _ + 1, v, [] =>
      if isFullyInitFuel defaultInitFuel v then some v else none
  | fuel + 1, .adt fields, .field idx :: rest =>
      match listGetOpt fields idx with
      | some fieldVal => evalProjFuel locals fuel fieldVal rest
      | none => none
  | fuel + 1, .refVal target, .deref :: rest =>
      match locals target.root with
      | some rootVal =>
          match evalProjFuel locals fuel rootVal target.proj with
          | some derefVal => evalProjFuel locals fuel derefVal rest
          | none => none
      | none => none
  | _ + 1, _, _ => none

def evalPlaceRead (locals : Locals) (p : Place) : Option MirVal :=
  match locals p.root with
  | some rootVal => evalProjFuel locals 16 rootVal p.proj
  | none => none

/-- Naive deref projection that concatenates `target.proj ++ rest` without
checking `isFullyInitFuel` on the intermediate dereferenced aggregate. -/
def evalProjNaiveConcatDeref (locals : Locals) : Nat → MirVal → List PlaceElem → Option MirVal
  | 0, _, _ => none
  | _ + 1, v, [] =>
      if isFullyInitFuel defaultInitFuel v then some v else none
  | fuel + 1, .adt fields, .field idx :: rest =>
      match listGetOpt fields idx with
      | some fieldVal => evalProjNaiveConcatDeref locals fuel fieldVal rest
      | none => none
  | fuel + 1, .refVal target, .deref :: rest =>
      match locals target.root with
      | some rootVal =>
          evalProjNaiveConcatDeref locals fuel rootVal (target.proj ++ rest)
      | none => none
  | _ + 1, _, _ => none

/-- Path-sensitive projection update (`updateProj`): writes `newVal` (including
`.uninit` on move) at the exact leaf path while preserving sibling fields. -/
def updateProj : MirVal → List PlaceElem → MirVal → Option MirVal
  | _, [], newVal => some newVal
  | .adt fields, .field idx :: rest, newVal =>
      match listGetOpt fields idx with
      | some oldField =>
          match updateProj oldField rest newVal with
          | some newField =>
              match listSetOpt fields idx newField with
              | some fields' => some (.adt fields')
              | none => none
          | none => none
      | none => none
  | _, _, _ => none

def evalPlaceWrite (locals : Locals) (p : Place) (newVal : MirVal) : Option Locals :=
  match locals p.root with
  | some rootVal =>
      match updateProj rootVal p.proj newVal with
      | some rootVal' => some (updateLocal locals p.root (some rootVal'))
      | none => none
  | none => none

/-- Path-sensitive `Operand.move`: reads `p` via `evalPlaceRead` (enforcing
`isFullyInitFuel`) and writes `.uninit` back to `p` via `evalPlaceWrite`. -/
def evalOperandMove (locals : Locals) (p : Place) : Option (MirVal × Locals) :=
  match evalPlaceRead locals p with
  | some v =>
      match evalPlaceWrite locals p .uninit with
      | some locals' => some (v, locals')
      | none => none
  | none => none

/-- Reference target resolution (`Rvalue.ref`) with `isFullyInitFuel` gate (c)
at terminal `proj = []` and intermediate `.deref` hops. -/
def resolveRefTargetFuel (locals : Locals) :
    Nat → Nat → MirVal → List PlaceElem → List PlaceElem → Option Place
  | 0, _, _, _, _ => none
  | _ + 1, root, v, prefixRev, [] =>
      if isFullyInitFuel defaultInitFuel v then
        some { root := root, proj := prefixRev.reverse }
      else
        none
  | fuel + 1, root, .adt fields, prefixRev, .field idx :: rest =>
      match listGetOpt fields idx with
      | some fieldVal =>
          resolveRefTargetFuel locals fuel root fieldVal (.field idx :: prefixRev) rest
      | none => none
  | fuel + 1, _, .refVal target, _, .deref :: rest =>
      match locals target.root with
      | some rootVal =>
          match evalProjFuel locals fuel rootVal target.proj with
          | some derefVal =>
              resolveRefTargetFuel locals fuel target.root derefVal
                target.proj.reverse rest
          | none => none
      | none => none
  | _ + 1, _, _, _, _ => none

def evalRvalueRef (locals : Locals) (p : Place) : Option MirVal :=
  match locals p.root with
  | some rootVal =>
      match resolveRefTargetFuel locals 16 p.root rootVal [] p.proj with
      | some target => some (.refVal target)
      | none => none
  | none => none

def samplePairLocals : Locals :=
  fun i => if i == 1 then some (.adt [.usize 10, .usize 42]) else none

/-- Theorem 1.1: Moving `_1.0` and then moving sibling field `_1.1` succeeds
and yields `(.usize 10, .usize 42)`. -/
theorem pathSensitive_allows_sibling_field_move :
    (do
      let (v0, locals1) ← evalOperandMove samplePairLocals { root := 1, proj := [.field 0] }
      let (v1, _) ← evalOperandMove locals1 { root := 1, proj := [.field 1] }
      pure (v0, v1)) = some (.usize 10, .usize 42) := rfl

/-- Theorem 1.2: Reading or moving `_1.0` a second time after `Operand.move (_1.0)`
fails closed (`none`). -/
theorem pathSensitive_rejects_removed_field :
    (do
      let (_, locals1) ← evalOperandMove samplePairLocals { root := 1, proj := [.field 0] }
      evalOperandMove locals1 { root := 1, proj := [.field 0] }) = none := rfl

/-- Theorem 1.3: Reading or moving the whole struct `_1` (`proj = []`) after
moving `_1.0` fails closed (`none`) via `isFullyInitFuel`. -/
theorem pathSensitive_rejects_whole_aggregate_read :
    (do
      let (_, locals1) ← evalOperandMove samplePairLocals { root := 1, proj := [.field 0] }
      evalPlaceRead locals1 { root := 1, proj := [] }) = none := rfl

/-- Theorem 1.4: Borrowing the whole struct `&_1` after moving `_1.0` fails
closed (`none`), whereas borrowing the initialized sibling field `&(_1.1)`
succeeds. -/
theorem pathSensitive_rejects_whole_aggregate_ref_but_allows_sibling_ref :
    (do
      let (_, locals1) ← evalOperandMove samplePairLocals { root := 1, proj := [.field 0] }
      pure (
        evalRvalueRef locals1 { root := 1, proj := [] },
        evalRvalueRef locals1 { root := 1, proj := [.field 1] }
      )) = some (none, some (.refVal { root := 1, proj := [.field 1] })) := rfl

/-- Theorem 1.5: Projecting `(*r).1` through a whole-struct reference `r = &_1`
after `_1.0` has been moved fails closed under Gate (b) (`evalProjFuel`),
whereas naive path concatenation (`evalProjNaiveConcatDeref`) unsoundly
returns `some (.usize 42)`. -/
theorem pathSensitive_rejects_deref_projection_through_partially_moved_struct :
    let localsAfterPartialMove : Locals := fun i =>
      if i == 1 then some (.adt [.uninit, .usize 42])
      else if i == 2 then some (.refVal { root := 1, proj := [] })
      else none
    let refVal := MirVal.refVal { root := 1, proj := [] }
    (evalProjFuel localsAfterPartialMove 16 refVal [.deref, .field 1],
     evalProjNaiveConcatDeref localsAfterPartialMove 16 refVal [.deref, .field 1]) =
      (none, some (.usize 42)) := rfl


/-! ## Section 2: `Stmt.placeMention` Semantics (`-Z mir-preserve-ub`) -/

inductive Stmt where
  | nop
  | placeMention (p : Place)
  deriving DecidableEq, Repr

def evalStmt (locals : Locals) : Stmt → Option Locals
  | .nop => some locals
  | .placeMention p =>
      match evalPlaceRead locals p with
      | some _ => some locals
      | none => none

/-- Theorem 2.1: When `RemovePlaceMention` erases `PlaceMention((*_1))` to
`.nop`, dangling dereferences and partially moved aggregates step to `some`,
whereas preserving `Stmt.placeMention` via `-Z mir-preserve-ub` steps both to
`none` (`.failed`). -/
theorem placeMention_rejects_dangling_and_partially_moved :
    let localsWithDanglingAndPartial : Locals := fun i =>
      if i == 1 then some (.refVal { root := 99, proj := [] }) -- dangling target
      else if i == 2 then some (.adt [.uninit, .usize 42])     -- partially moved
      else none
    let derefPlace : Place := { root := 1, proj := [.deref] }
    let partialPlace : Place := { root := 2, proj := [] }
    ((evalStmt localsWithDanglingAndPartial .nop).isSome,
     evalStmt localsWithDanglingAndPartial (.placeMention derefPlace),
     evalStmt localsWithDanglingAndPartial (.placeMention partialPlace)) =
      (true, none, none) := rfl


/-! ## Section 3: Post-Monomorphization Error (PME) Completeness -/

inductive MirTy where
  | u8
  | u64
  | param (idx : Nat)
  | array (elem : MirTy) (len : Nat)
  | unsupported
  deriving DecidableEq, Repr

def maxTypeSize64 : Nat := 9223372036854775807 -- isize::MAX on 64-bit targets

def evalTyByteSize (maxTypeSize : Nat) (tySizes : Nat → Nat) : MirTy → Option Nat
  | .u8 => some 1
  | .u64 => some 8
  | .param idx =>
      if tySizes idx ≤ maxTypeSize then some (tySizes idx) else none
  | .array elem len =>
      match evalTyByteSize maxTypeSize tySizes elem with
      | some elemSz =>
          if elemSz * len ≤ maxTypeSize then some (elemSz * len) else none
      | none => none
  | .unsupported => none

def ValidTySizes (maxTypeSize paramCount : Nat) (tySizes : Nat → Nat) : Prop :=
  ∀ idx, idx < paramCount → tySizes idx ≤ maxTypeSize

inductive ConstOutcome where
  | succeeds
  | unwinds
  | fails
  deriving DecidableEq, Repr

/-- `const { assert!(core::mem::size_of::<T>() == 8); }` (`Fail::<T>::C`):
succeeds when `size_of::<T>() = 8` and unwinds (panics) otherwise. -/
def sizeEq8Const (argByteSize : Nat) : ConstOutcome :=
  if argByteSize = 8 then .succeeds else .unwinds

/-- Pitfall 3A: Single-quantifier `ConstsTotal` requiring `ConstSucceeds` over
all `ValidTySizes` (without `ConstUnwinds` + `MonoAdmitted`). -/
def SingleQuantifierStrictConstsTotal
    (maxTypeSize paramCount : Nat) (tyArg : MirTy) (c : Nat → ConstOutcome) : Prop :=
  ∀ tySizes, ValidTySizes maxTypeSize paramCount tySizes →
    ∃ sz, evalTyByteSize maxTypeSize tySizes tyArg = some sz ∧ c sz = .succeeds

/-- Theorem 3.1: `SingleQuantifierStrictConstsTotal` is false on
`const { assert!(size_of::<T>() == 8); }`, locking out valid compile-time PME
guards and making `initMirState` empty. -/
theorem SingleQuantifierStrictConstsTotal_locks_out_pme_guard :
    ¬ SingleQuantifierStrictConstsTotal maxTypeSize64 1 (.param 0) sizeEq8Const := by
  intro h
  have hValid : ValidTySizes maxTypeSize64 1 (fun _ => 1) := by
    intro _ _
    show 1 ≤ maxTypeSize64
    decide
  rcases h (fun _ => 1) hValid with ⟨sz, hSz, hSucc⟩
  have hSzEq : sz = 1 := by
    change (if 1 ≤ maxTypeSize64 then some 1 else none) = some sz at hSz
    injection hSz with hEq
    exact hEq.symm
  subst hSzEq
  revert hSucc
  decide

/-- Pitfall 3B: Placing `evalTyByteSize ... = some sz` on the left-hand side of
an implication makes `ConstsTotal` vacuously true when `tyArg` is `.unsupported`
or exceeds `maxTypeSize`. -/
def ImplicationLHSConstsTotal
    (maxTypeSize paramCount : Nat) (tyArg : MirTy) (c : Nat → ConstOutcome) : Prop :=
  ∀ tySizes, ValidTySizes maxTypeSize paramCount tySizes →
    ∀ sz, evalTyByteSize maxTypeSize tySizes tyArg = some sz →
      (c sz = .succeeds ∨ c sz = .unwinds)

/-- Theorem 3.2: `ImplicationLHSConstsTotal` is vacuously satisfied on an
`.unsupported` type argument even when the constant body unconditionally fails
with CTFE Undefined Behavior (`.fails`). -/
theorem ImplicationLHSConstsTotal_vacuous_on_unsupported_ty :
    ImplicationLHSConstsTotal maxTypeSize64 1 .unsupported (fun _ => .fails) := by
  intro _ _ sz hSz
  simp [evalTyByteSize] at hSz

/-- Sound Two-Stage PME Predicate, Stage 1 (`ConstsTotal`): Over all
`ValidTySizes`, type-argument byte-size evaluation must positively succeed
(`∃ sz`) and constant evaluation must terminate cleanly (`.succeeds` or
`.unwinds`, never `.fails`). -/
def TwoStageConstsTotal
    (maxTypeSize paramCount : Nat) (tyArg : MirTy) (c : Nat → ConstOutcome) : Prop :=
  ∀ tySizes, ValidTySizes maxTypeSize paramCount tySizes →
    ∃ sz, evalTyByteSize maxTypeSize tySizes tyArg = some sz ∧
      (c sz = .succeeds ∨ c sz = .unwinds)

/-- Sound Two-Stage PME Predicate, Stage 2 (`MonoAdmitted`): At the active
monomorphization's `tySizes`, type layouts must be bounded by `maxTypeSize` and
every required or mentioned constant must evaluate to `.succeeds`. -/
def MonoAdmitted
    (maxTypeSize : Nat) (tySizes : Nat → Nat) (tyArg : MirTy) (c : Nat → ConstOutcome) : Prop :=
  ∃ sz, evalTyByteSize maxTypeSize tySizes tyArg = some sz ∧ c sz = .succeeds

/-- Theorem 3.3: `TwoStageConstsTotal` accepts `sizeEq8Const`, rejects
`.unsupported` type arguments, and rejects CTFE UB (`.fails`), while
`MonoAdmitted` is non-vacuously satisfiable (witnessed by `tySizes 0 = 8`) and
entails `tySizes 0 = 8` for runtime verification. -/
theorem twoStagePme_sound_and_nonvacuous :
    TwoStageConstsTotal maxTypeSize64 1 (.param 0) sizeEq8Const ∧
    ¬ TwoStageConstsTotal maxTypeSize64 1 .unsupported sizeEq8Const ∧
    ¬ TwoStageConstsTotal maxTypeSize64 1 (.param 0) (fun _ => .fails) ∧
    MonoAdmitted maxTypeSize64 (fun _ => 8) (.param 0) sizeEq8Const ∧
    (∀ tySizes,
      MonoAdmitted maxTypeSize64 tySizes (.param 0) sizeEq8Const →
      tySizes 0 = 8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro tySizes hValid
    have hBound : tySizes 0 ≤ maxTypeSize64 := hValid 0 (by decide)
    refine ⟨tySizes 0, ?_, ?_⟩
    · simp [evalTyByteSize, hBound]
    · unfold sizeEq8Const
      split <;> simp
  · intro hUnsup
    have hValid : ValidTySizes maxTypeSize64 1 (fun _ => 8) := by
      intro _ _
      show 8 ≤ maxTypeSize64
      decide
    rcases hUnsup (fun _ => 8) hValid with ⟨sz, hSz, _⟩
    simp [evalTyByteSize] at hSz
  · intro hFails
    have hValid : ValidTySizes maxTypeSize64 1 (fun _ => 8) := by
      intro _ _
      show 8 ≤ maxTypeSize64
      decide
    rcases hFails (fun _ => 8) hValid with ⟨_, _, hOut⟩
    cases hOut <;> contradiction
  · refine ⟨8, by decide, by decide⟩
  · intro tySizes hMono
    rcases hMono with ⟨sz, hSz, hSucc⟩
    dsimp [evalTyByteSize] at hSz
    split at hSz
    · injection hSz with hEq
      subst hEq
      dsimp [sizeEq8Const] at hSucc
      split at hSucc
      · rename_i hEq8
        exact hEq8
      · contradiction
    · contradiction


/-! ## Section 4: Compiler-Inserted `Terminator.assert` vs. `Callee.panic` -/

inductive ExecOutcome where
  | normal (ret : Nat)
  | unwind
  | failed
  deriving DecidableEq, Repr

/-- Matches `PrefixOutcome.isSafe` in `trusted/lean/Trusted/StepResult.lean:59-63`:
`.unwind` is safe, while `.failed` is Undefined Behavior / assertion violation. -/
def ExecOutcome.isSafe (o : ExecOutcome) : Prop :=
  o ≠ .failed

/-- Naive evaluation of `bad_overflow(x: u8)` where compiler-inserted
`Terminator.assert` failure steps to `.unwind` (like user `panic!`).
In debug mode (`overflowChecks = true`), `x = 255` overflows `x + 1` and takes
the `Terminator.assert` failure branch. In release mode (`overflowChecks = false`),
`x + 1` wraps modulo 256 to `0` and hits `unreachable_unchecked()` (`.failed`). -/
def evalBadOverflowNaive (overflowChecks : Bool) (x : Nat) : ExecOutcome :=
  if overflowChecks then
    if 255 < x + 1 then .unwind
    else if x + 1 == 0 then .failed
    else .normal (x + 1)
  else
    let y := (x + 1) % 256
    if y == 0 then .failed else .normal y

/-- Fixed evaluation of `bad_overflow(x: u8)` where compiler-inserted
`Terminator.assert` failure steps to `.failed`. -/
def evalBadOverflowFixed (overflowChecks : Bool) (x : Nat) : ExecOutcome :=
  if overflowChecks then
    if 255 < x + 1 then .failed
    else if x + 1 == 0 then .failed
    else .normal (x + 1)
  else
    let y := (x + 1) % 256
    if y == 0 then .failed else .normal y

/-- Theorem 4.1 (`bad_overflow` Soundness Counterexample): Under naive
`Terminator.assert -> .unwind` semantics, `bad_overflow` is verified safe for
all `x ≤ 255` under `overflowChecks = true`, yet executes Undefined Behavior
(`.failed`) at `x = 255` under `overflowChecks = false` (`--release`). -/
theorem naiveAssertUnwind_unsound_on_bad_overflow :
    (∀ x, x ≤ 255 → (evalBadOverflowNaive true x).isSafe) ∧
    evalBadOverflowNaive false 255 = .failed := by
  refine ⟨?_, rfl⟩
  intro x _
  change (if 255 < x + 1 then ExecOutcome.unwind
    else if x + 1 == 0 then ExecOutcome.failed
    else ExecOutcome.normal (x + 1)) ≠ ExecOutcome.failed
  split
  · decide
  · have hNeZero : (x + 1 == 0) = false := by
      cases x <;> rfl
    simp [hNeZero]

/-- Theorem 4.2: Under fixed `Terminator.assert -> .failed` semantics,
`bad_overflow(255)` steps to `.failed` in both debug and release modes, and
every input `x ≤ 255` that is safe under `overflowChecks = true` produces the
exact same normal return in release mode (`overflowChecks = false`). -/
theorem fixedAssertFailed_sound_across_profiles :
    evalBadOverflowFixed true 255 = .failed ∧
    evalBadOverflowFixed false 255 = .failed ∧
    (∀ x, x ≤ 255 →
      (evalBadOverflowFixed true x).isSafe →
      evalBadOverflowFixed false x = evalBadOverflowFixed true x) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x _ hSafe
  change (if 255 < x + 1 then ExecOutcome.failed
    else if x + 1 == 0 then ExecOutcome.failed
    else ExecOutcome.normal (x + 1)) ≠ ExecOutcome.failed at hSafe
  change (if ((x + 1) % 256 == 0) then ExecOutcome.failed
    else ExecOutcome.normal ((x + 1) % 256)) =
    (if 255 < x + 1 then ExecOutcome.failed
    else if x + 1 == 0 then ExecOutcome.failed
    else ExecOutcome.normal (x + 1))
  split at hSafe
  · contradiction
  · rename_i hNotLt
    have hLt256 : x + 1 < 256 := Nat.lt_succ_of_le (Nat.le_of_not_lt hNotLt)
    have hMod : (x + 1) % 256 = x + 1 := Nat.mod_eq_of_lt hLt256
    simp [hNotLt, hMod]


/-! ## Section 5: Flat `BodyId` Table, Frame-Relative `returnRefsOk`, and
In-Place `lowerBody` Simulation with PC-Canonicalized `MirReturn` -/

/-- Frame-relative `returnRefsOk` (`Bool`):
At root frame (`frameId == 0`), a returned reference must target frame `0` at a
caller-owned slot (`localCount ≤ targetLocalIdx`).
At an inline callee frame (`frameId > 0`), any reference targeting a strictly
older caller frame (`targetFrameId < frameId`) survives callee frame exit, even
when `targetLocalIdx < calleeLocalCount`. -/
def returnRefsOk (frameId localCount targetFrameId targetLocalIdx : Nat) : Bool :=
  if frameId == 0 then
    targetFrameId == 0 && decide (localCount ≤ targetLocalIdx)
  else
    decide (targetFrameId < frameId)

/-- Naive frame-insensitive `returnRefsOk` that checks `localCount ≤ targetLocalIdx`
regardless of whether `targetFrameId < frameId`. -/
def returnRefsOkNaive (localCount targetLocalIdx : Nat) : Bool :=
  decide (localCount ≤ targetLocalIdx)

/-- Theorem 5.1: When an inline callee (`frameId = 1`, `localCount = 3`) returns
a reference to its caller's local 0 (`targetFrameId = 0`, `targetLocalIdx = 0`),
frame-relative `returnRefsOk` returns `true`, whereas frame-insensitive
`returnRefsOkNaive` falsely rejects it (`false`), while both reject returning a
reference to the callee's own local (`targetFrameId = 1`, `targetLocalIdx = 0`)
or a root function returning its own local (`frameId = 0`, `targetLocalIdx = 0`). -/
theorem returnRefsOk_frame_relative_correctness :
    returnRefsOk 1 3 0 0 = true ∧
    returnRefsOkNaive 3 0 = false ∧
    returnRefsOk 1 3 1 0 = false ∧
    returnRefsOk 0 3 0 0 = false ∧
    returnRefsOk 0 3 0 3 = true := by
  decide

/-- Flat `BodyId`-indexed instruction and block model (no `mutual inductive`
embedding of `MirBody` inside `Terminator`). -/
inductive FlatStmt where
  | nop
  | addImm (dst src imm : Nat)
  deriving DecidableEq, Repr

inductive FlatTerminator where
  | return_ (src : Nat)
  | call (callee : Nat) (arg dst targetBlock : Nat)
  deriving DecidableEq, Repr

structure FlatBlock where
  stmts : List FlatStmt
  term : FlatTerminator
  deriving DecidableEq, Repr

structure FlatBody where
  id : Nat
  blocks : List FlatBlock
  deriving DecidableEq, Repr

/-- Because `FlatBody` does not embed callee `FlatBody` trees inside
`FlatTerminator.call`, structural equality is total without a fuel bound (unlike
`beqMirBodyFuel 8` in `theory/Anneal/MirLemmas.lean:3549`). -/
theorem flatBody_decidableEq_refl (b : FlatBody) : (b == b) = true := by
  simp

/-- In-place Stage 3 lowering (`lowerBody`): strips `.nop` statements inside
each block while preserving `blocks.length` and all `BlockId` indices. -/
def lowerBlock (blk : FlatBlock) : FlatBlock :=
  { blk with stmts := blk.stmts.filter (fun s => s != .nop) }

def lowerBody (b : FlatBody) : FlatBody :=
  { b with blocks := b.blocks.map lowerBlock }

theorem lowerBody_preserves_block_count (b : FlatBody) :
    (lowerBody b).blocks.length = b.blocks.length := by
  simp [lowerBody]

structure BlockState where
  reg : Nat
  stmtIdx : Nat
  deriving DecidableEq, Repr

def stepStmt (st : BlockState) : FlatStmt → BlockState
  | .nop => { st with stmtIdx := st.stmtIdx + 1 }
  | .addImm _ _ imm => { reg := st.reg + imm, stmtIdx := st.stmtIdx + 1 }

def execStmts (st : BlockState) : List FlatStmt → BlockState
  | [] => st
  | s :: ss => execStmts (stepStmt st s) ss

/-- Raw return state (without PC canonicalization) exposes `stmtIdx`, which
changes when `.nop` is stripped. -/
def evalSingleBlockRaw (blk : FlatBlock) (initReg : Nat) : BlockState :=
  execStmts { reg := initReg, stmtIdx := 0 } blk.stmts

/-- PC-canonicalized return state resets `stmtIdx := 0` on normal return, so
stripping `.nop` preserves the exact observable `BlockState`. -/
def evalSingleBlockCanonical (blk : FlatBlock) (initReg : Nat) : BlockState :=
  let finalSt := execStmts { reg := initReg, stmtIdx := 0 } blk.stmts
  { finalSt with stmtIdx := 0 }

/-- Theorem 5.2: Without PC canonicalization, stripping `.nop` changes the
returned `BlockState` (`stmtIdx = 1` vs. `stmtIdx = 2`). -/
theorem rawReturn_distinguishes_nop_stripping :
    let blk : FlatBlock := { stmts := [.nop, .addImm 0 0 5], term := .return_ 0 }
    evalSingleBlockRaw (lowerBlock blk) 10 ≠ evalSingleBlockRaw blk 10 := by
  decide

theorem execStmts_filter_nop_reg (st : BlockState) (stmts : List FlatStmt) :
    (execStmts st (stmts.filter (fun s => s != .nop))).reg =
      (execStmts st stmts).reg ∧
    ∀ st2 : BlockState, st2.reg = st.reg →
      (execStmts st2 stmts).reg = (execStmts st stmts).reg := by
  induction stmts generalizing st with
  | nil =>
      refine ⟨rfl, ?_⟩
      intro st2 hReg
      exact hReg
  | cons s ss ih =>
      cases s with
      | nop =>
          dsimp [List.filter, execStmts, stepStmt]
          have ih1 := (ih st).1
          have ih2 := (ih { st with stmtIdx := st.stmtIdx + 1 }).2 st rfl
          refine ⟨ih1.trans ih2, ?_⟩
          intro st2 hReg
          exact (ih { st with stmtIdx := st.stmtIdx + 1 }).2
            { st2 with stmtIdx := st2.stmtIdx + 1 } hReg
      | addImm dst src imm =>
          dsimp [List.filter, execStmts, stepStmt]
          have ihStep := ih { reg := st.reg + imm, stmtIdx := st.stmtIdx + 1 }
          refine ⟨ihStep.1, ?_⟩
          intro st2 hReg
          apply ihStep.2
          simp [hReg]

/-- Theorem 5.3: With PC canonicalization at `return_`, `lowerBlock` preserves
the exact `BlockState` for every initial register value and statement list. -/
theorem canonicalReturn_preserves_lowerBlock (blk : FlatBlock) (initReg : Nat) :
    evalSingleBlockCanonical (lowerBlock blk) initReg =
      evalSingleBlockCanonical blk initReg := by
  unfold evalSingleBlockCanonical lowerBlock
  have hReg := (execStmts_filter_nop_reg { reg := initReg, stmtIdx := 0 } blk.stmts).1
  cases h1 : execStmts { reg := initReg, stmtIdx := 0 } (blk.stmts.filter (fun s => s != .nop))
  cases h2 : execStmts { reg := initReg, stmtIdx := 0 } blk.stmts
  simp only [h1, h2] at hReg
  subst hReg
  rfl

end AnnealMirRefinementProbes
