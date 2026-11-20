-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Trusted
import Trusted.MirAst
import Trusted.MirSemantics
import Anneal.MirWp
import Anneal.PureLift.Lens
import Anneal.PureLift.PermTree
import Anneal.PureLift.LoanGraph
import Anneal.PureLift.SpatialPin
import Anneal.PureLift.Plan
import Anneal.PureLift.BlockCfg
import Anneal.PureLift.Adapter

namespace Anneal.PureLift

open Trusted.MirAst Trusted.MirSemantics

/-!
# Bridge Between `PureLift` and `Trusted` MIR Semantics (`MirBridge.lean`)

Connects the language- and MIR-agnostic `Anneal.PureLift` functional lifting
transformation to the authoritative post-cleanup runtime MIR syntax
(`Trusted/MirAst.lean`), small-step operational semantics
(`Trusted/MirSemantics.lean`), fuel-bounded weakest precondition
(`Anneal/MirWp.lean`), and the `lean-miri` reference correspondence bridge
(`Trusted/Correspondence.lean`):

1. **Depth-Parametric Value Algebra and Lawful Field Lenses (`mirValAlgAt`,
   `mirValAlg`):** instantiates `ValAlgebra Trusted.MirSemantics.Val` for any
   tuple nesting bound `d : Nat` (defaulting `mirValAlg := mirValAlgAt 7`,
   aggregate depth 8), including leaf handling for `Val.enumVal` and
   width-masked scalar truthiness in `mirAsBool`, proves the five lens,
   separation, and commutation laws (`mir_getField_setField` through
   `mir_setField_setField_comm`), and derives lawful single-field and nested
   sub-path lenses (`mirFieldLensAt_lawful`, `mirFieldLens_lawful`,
   `mirSubPathLensAt_lawful`, `mirSubPathLens_lawful`).
2. **Unified `MirWp` Execution Predicates and Small-Step Operational Adapter
   (`MirStepsDone`, `MirRunsDone`, `MirRunsFault`, `MirArgsMatch`,
   `MirRunsTo`, `MirExecutesTo`, `mirOperationalAdapter`,
   `mir_pure_lift_sound`, `mir_pure_lift_satisfiesPost`,
   `bodyVerified_of_pure_lift`):** defines `MirStepsDone`, `MirRunsDone`, and
   `MirRunsFault` directly as abbreviations over
   `Anneal.MirWp.{execState, execProg, execFaultProg}`,
   connects genuine 1-step `MirExecutesTo` transitions (`step_next`,
   `step_ret`) to `evalFnValue` via `mirOperationalAdapter`, enforces `.byVal`
   entry modes, empty `q.callerMem = ⟨[]⟩`, and `ValidEntryArgs body q.args` in
   `MirArgsMatch`, and connects per-input `PureLift` verification (paired with
   an explicit per-input `MirRunsTo` simulation proof `hSim`, since no
   automatic MIR-to-`PureLift` simulation theorem is claimed here) to
   multi-body `BodyVerified` at arbitrary `defId`.
3. **Certified Computable MIR Helpers, Straight-Line Lifter, and `lean-miri`
   Transfer (`liftStraightLineMir`, `MirStraightLineLiftsTo`,
   `mir_pure_lift_correspondence_transfer`,
   `mir_fault_correspondence_transfer`):** proves kernel agreement theorems
   (`mirBodyStaticAdmitted_eq`, `mirCheckVal_eq`, `mirEvalConstLit_eq`,
   `mirEvalBinOpVal_eq`, `mirEvalUnOpVal_eq`, `mirLiveUninitSlot_eq`)
   certifying those computable `mir*` evaluators against
   `Trusted.MirSemantics` (the lifter's other mirrors—`mirTyBeq`,
   `mirIsPrimitiveReadableTy`, `mirHasStorageAnnotation`, and
   `mirEvalDiscrVal`—have no agreement theorem; every transfer still checks
   the run against `Trusted.MirSemantics` through `hSim` or `MirRunsFault`),
   translates single-block bodies (`StorageLive`, `StorageDead`, `Assign`,
   `Operand.copy`, `Operand.move`, `ConstOperand`, `UnOp`, `BinOp`,
   `Rvalue.discriminant`, `Return`) into `FlowPlan Val`, and transfers verified
   termination and exclusive faults (with guaranteed non-faulting `initState`)
   across `CorrespondenceClaim` and `FaultEquivalenceClaim` to `lean-miri`
   ($M_{\text{ref}}$).
4. **Verified Workloads (`W-1` through `W-5`):**
   - `W-1` (`compute_linear` and `add_assign`): concrete-input end-to-end
     $M_{\text{anneal}}$ / $M_{\text{ref}}$ verification and correspondence
     transfer of `progComputeLinearU32` via both `liftStraightLineMir` and the
     explicit mutable-borrow plan `mirComputeLinearPlan`, plus standalone
     `&mut` writeback (`mirAddAssignPlan`).
   - `W-2` (`swap_fields` and `select_add`): standalone disjoint tuple-field
     borrow check (`mirSwapFieldsPlan`), plus 4-block `SwitchInt` branching
     (`progSelectAddU32`) verified for all `flag : Bool` (with fixed operands
     `(10, 100, 5)`) and transferred to $M_{\text{ref}}$.
   - `W-3` (`loop_accumulate`): concrete-input 4-block `while` loop
     (`progLoopAccumulateU32`) paired with `.whileLoop`
     (`mirLoopAccumulatePlan`) and transferred to $M_{\text{ref}}$.
   - `W-4` (`use_after_move`, `use_after_storage_dead`, and standalone borrow
     canaries): coupled `liftStraightLineMir` + $M_{\text{anneal}}$ +
     $M_{\text{ref}}$ fault transfer on `progUseAfterMoveUb` and
     `progUseAfterStorageDeadUb`, plus standalone borrow-discipline rejection
     checks (`mirDanglingRefPlan`, `mirOverwriteWhileBorrowedPlan`).
   - `W-5` (`enum_discriminant`): concrete-input straight-line `#[repr(u8)]`
     fieldless enum constant + `Rvalue.discriminant` lifting and transfer via
     `liftStraightLineMir`, paired with coupled invalid-enum-tag UB rejection.
-/

/-! ## Computable List Lookup and Update (`mirListGet?` / `mirListSet?`) -/

/-- Total list lookup by index via `List.foldr`, emitting zero compiler
`_unsafe_rec` helpers while reducing by `rfl` on concrete lists. -/
def mirListGet? {α : Type} (xs : List α) (idx : Nat) : Option α :=
  xs.foldr
    (fun x ih k =>
      match k with
      | 0 => some x
      | k' + 1 => ih k')
    (fun _ => none)
    idx

/-- Total list update by index via `natFold`, returning `none` when `idx` is
out of bounds. -/
def mirListSet? {α : Type} (xs : List α) (idx : Nat) (v : α) :
    Option (List α) :=
  natFold
    (fun ys =>
      match ys with
      | [] => none
      | _ :: ys' => some (v :: ys'))
    (fun _ ih ys =>
      match ys with
      | [] => none
      | y :: ys' =>
        match ih ys' with
        | some rest' => some (y :: rest')
        | none => none)
    idx xs

/-- `mirListGet?` agrees with `Trusted.MirSemantics.getElem?` at every index. -/
theorem mirListGet?_eq_getElem? {α : Type} :
    ∀ (xs : List α) (idx : Nat),
      mirListGet? xs idx = Trusted.MirSemantics.getElem? xs idx
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, n + 1 => mirListGet?_eq_getElem? xs n

/-- `mirListGet?` followed by `mirListSet?` with the retrieved element restores
the original list. -/
theorem getElem?_setElem? {α : Type} :
    ∀ (xs : List α) (f : Nat) (a : α),
      mirListGet? xs f = some a →
      mirListSet? xs f a = some xs
  | [], _, _, hGet => nomatch hGet
  | _ :: xs, 0, _, hGet => by
    change some _ = some _ at hGet
    injection hGet with hEq
    subst hEq
    rfl
  | x :: xs, f + 1, a, hGet => by
    change mirListGet? xs f = some a at hGet
    change (match mirListSet? xs f a with
      | some xs' => some (x :: xs')
      | none => none) = some (x :: xs)
    rw [getElem?_setElem? xs f a hGet]

/-- `mirListSet?` followed by `mirListGet?` at the same index returns the
written element. -/
theorem setElem?_getElem? {α : Type} :
    ∀ (xs : List α) (f : Nat) (a : α) (xs' : List α),
      mirListSet? xs f a = some xs' →
      mirListGet? xs' f = some a
  | [], 0, _, _, hSet => nomatch hSet
  | [], _ + 1, _, _, hSet => nomatch hSet
  | _ :: xs, 0, a, _, hSet => by
    change some (a :: xs) = some _ at hSet
    injection hSet with hEq
    subst hEq
    rfl
  | x :: xs, f + 1, a, _, hSet => by
    change (match mirListSet? xs f a with
      | some xs1 => some (x :: xs1)
      | none => none) = some _ at hSet
    revert hSet
    cases hRec : mirListSet? xs f a with
    | none =>
      intro hFalse
      nomatch hFalse
    | some xs1 =>
      intro hSet
      injection hSet with hEq
      subst hEq
      change mirListGet? xs1 f = some a
      exact setElem?_getElem? xs f a xs1 hRec

/-- Two consecutive `mirListSet?` updates at the same index equal the second
update alone. -/
theorem setElem?_setElem? {α : Type} :
    ∀ (xs : List α) (f : Nat) (a1 a2 : α) (xs1 : List α),
      mirListSet? xs f a1 = some xs1 →
      mirListSet? xs1 f a2 = mirListSet? xs f a2
  | [], 0, _, _, _, hSet => nomatch hSet
  | [], _ + 1, _, _, _, hSet => nomatch hSet
  | _ :: xs, 0, _, _, _, hSet => by
    change some (_ :: xs) = some _ at hSet
    injection hSet with hEq
    subst hEq
    rfl
  | x :: xs, f + 1, a1, a2, _, hSet => by
    change (match mirListSet? xs f a1 with
      | some xs' => some (x :: xs')
      | none => none) = some _ at hSet
    revert hSet
    cases hRec : mirListSet? xs f a1 with
    | none =>
      intro hFalse
      nomatch hFalse
    | some xs' =>
      intro hSet
      injection hSet with hEq
      subst hEq
      change (match mirListSet? xs' f a2 with
        | some ys => some (x :: ys)
        | none => none) =
        (match mirListSet? xs f a2 with
        | some ys => some (x :: ys)
        | none => none)
      rw [setElem?_setElem? xs f a1 a2 xs' hRec]

/-- `mirListSet?` at index `f` leaves the element at every other index `g ≠ f`
unchanged. -/
theorem getElem?_setElem?_other {α : Type} :
    ∀ (xs : List α) (f g : Nat) (a : α) (xs' : List α),
      f ≠ g →
      mirListSet? xs f a = some xs' →
      mirListGet? xs' g = mirListGet? xs g
  | [], 0, _, _, _, _, hSet => nomatch hSet
  | [], _ + 1, _, _, _, _, hSet => nomatch hSet
  | _ :: xs, 0, g, a, _, hNe, hSet => by
    change some (a :: xs) = some _ at hSet
    injection hSet with hEq
    subst hEq
    cases g with
    | zero => exact False.elim (hNe rfl)
    | succ g' => rfl
  | x :: xs, f + 1, g, a, _, hNe, hSet => by
    change (match mirListSet? xs f a with
      | some xs1 => some (x :: xs1)
      | none => none) = some _ at hSet
    revert hSet
    cases hRec : mirListSet? xs f a with
    | none =>
      intro hFalse
      nomatch hFalse
    | some xs1 =>
      intro hSet
      injection hSet with hEq
      subst hEq
      cases g with
      | zero => rfl
      | succ g' =>
        change mirListGet? xs1 g' = mirListGet? xs g'
        exact getElem?_setElem?_other xs f g' a xs1
          (fun hEq => hNe (congrArg Nat.succ hEq)) hRec

/-- `mirListSet?` updates at distinct indices `f ≠ g` commute. -/
theorem setElem?_setElem?_comm {α : Type} :
    ∀ (xs : List α) (f g : Nat) (a b : α) (xs1 xs2 : List α),
      f ≠ g →
      mirListSet? xs f a = some xs1 →
      mirListSet? xs1 g b = some xs2 →
      Exists fun xs1' =>
        mirListSet? xs g b = some xs1' ∧
        mirListSet? xs1' f a = some xs2
  | [], 0, _, _, _, _, _, _, h1, _ => nomatch h1
  | [], _ + 1, _, _, _, _, _, _, h1, _ => nomatch h1
  | x :: xs, 0, g, a, b, _, xs2, hNe, h1, h2 => by
    change some (a :: xs) = some _ at h1
    injection h1 with hEq1
    subst hEq1
    cases g with
    | zero => exact False.elim (hNe rfl)
    | succ g' =>
      change (match mirListSet? xs g' b with
        | some xsG => some (a :: xsG)
        | none => none) = some _ at h2
      revert h2
      cases hG : mirListSet? xs g' b with
      | none =>
        intro hFalse
        nomatch hFalse
      | some xsG =>
        intro h2
        injection h2 with hEq2
        subst hEq2
        refine ⟨x :: xsG, ?_, rfl⟩
        change (match mirListSet? xs g' b with
          | some ys => some (x :: ys)
          | none => none) = some (x :: xsG)
        rw [hG]
  | x :: xs, f + 1, g, a, b, _, xs2, hNe, h1, h2 => by
    change (match mirListSet? xs f a with
      | some xsF => some (x :: xsF)
      | none => none) = some _ at h1
    revert h1
    cases hF : mirListSet? xs f a with
    | none =>
      intro hFalse
      nomatch hFalse
    | some xsF =>
      intro h1
      injection h1 with hEq1
      subst hEq1
      cases g with
      | zero =>
        change some (b :: xsF) = some _ at h2
        injection h2 with hEq2
        subst hEq2
        refine ⟨b :: xs, rfl, ?_⟩
        change (match mirListSet? xs f a with
          | some ys => some (b :: ys)
          | none => none) = some (b :: xsF)
        rw [hF]
      | succ g' =>
        change (match mirListSet? xsF g' b with
          | some xsFG => some (x :: xsFG)
          | none => none) = some _ at h2
        revert h2
        cases hG : mirListSet? xsF g' b with
        | none =>
          intro hFalse
          nomatch hFalse
        | some xsFG =>
          intro h2
          injection h2 with hEq2
          subst hEq2
          cases setElem?_setElem?_comm xs f g' a b xsF xsFG
              (fun hEq => hNe (congrArg Nat.succ hEq)) hF hG with
          | intro xsG hPair =>
            refine ⟨x :: xsG, ?_, ?_⟩
            · change (match mirListSet? xs g' b with
                | some ys => some (x :: ys)
                | none => none) = some (x :: xsG)
              rw [hPair.1]
            · change (match mirListSet? xsG f a with
                | some ys => some (x :: ys)
                | none => none) = some (x :: xsFG)
              rw [hPair.2]

/-! ## Value Algebra and Lawful Field Lenses for `Trusted.MirSemantics.Val` -/

/-- True iff `v` has tuple nesting depth at most `d` (`d = 0` admits all
non-tuple `Val` leaves; `d + 1` admits `.tuple fields` whose elements each have
tuple nesting depth at most `d`). Defined via `natFold` and `List.foldr`. -/
def valDepthOk (d : Nat) (v : Val) : Bool :=
  natFold
    (fun x =>
      match x with
      | .tuple _ => false
      | _ => true)
    (fun _ ih x =>
      match x with
      | .tuple fields => fields.foldr (fun c acc => ih c && acc) true
      | _ => true)
    d v

theorem list_foldr_and_mono {α : Type} (p q : α → Bool)
    (hImp : ∀ x, p x = true → q x = true) :
    ∀ (xs : List α),
      xs.foldr (fun c acc => p c && acc) true = true →
      xs.foldr (fun c acc => q c && acc) true = true
  | [], _ => rfl
  | c :: cs, h => by
    change (p c && cs.foldr (fun x acc => p x && acc) true) = true at h
    change (q c && cs.foldr (fun x acc => q x && acc) true) = true
    cases hP : p c with
    | false =>
      rw [hP] at h
      nomatch h
    | true =>
      rw [hP] at h
      change cs.foldr (fun x acc => p x && acc) true = true at h
      rw [hImp c hP, list_foldr_and_mono p q hImp cs h]
      rfl

theorem valDepthOk_mono :
    ∀ (k : Nat) (v : Val), valDepthOk k v = true → valDepthOk (k + 1) v = true
  | 0, v, h => by
    cases v with
    | tuple _ => nomatch h
    | scalar _ => rfl
    | ptr _ => rfl
    | bool _ => rfl
    | unit => rfl
    | enumVal _ _ => rfl
    | bytes _ => rfl
  | k + 1, v, h => by
    cases v with
    | tuple fields =>
      exact list_foldr_and_mono (valDepthOk k) (valDepthOk (k + 1))
        (valDepthOk_mono k) fields h
    | scalar _ => rfl
    | ptr _ => rfl
    | bool _ => rfl
    | unit => rfl
    | enumVal _ _ => rfl
    | bytes _ => rfl

/-- Read field `f` of a `Val.tuple` aggregate admitting child values up to
tuple nesting depth `d` (aggregate depth `d + 1` at the enclosing tuple). -/
def getMirFieldAt (d : Nat) (f : FieldIdx) : Val → Option Val
  | .tuple fields =>
    match mirListGet? fields f with
    | some c => if valDepthOk d c then some c else none
    | none => none
  | _ => none

/-- Update field `f` of a `Val.tuple` aggregate to `child` when `valDepthOk d
child` holds. -/
def setMirFieldAt (d : Nat) (f : FieldIdx) (v child : Val) : Option Val :=
  match v with
  | .tuple fields =>
    if valDepthOk d child then
      match mirListSet? fields f child with
      | some fields' => some (.tuple fields')
      | none => none
    else
      none
  | _ => none

/-- Lens law `get_put` for `getMirFieldAt d` and `setMirFieldAt d`. -/
theorem mir_getField_setField {d : Nat} (f : FieldIdx) (s a : Val)
    (hGet : getMirFieldAt d f s = some a) :
    setMirFieldAt d f s a = some s := by
  cases s with
  | tuple fields =>
    dsimp [getMirFieldAt] at hGet
    cases hLookup : mirListGet? fields f with
    | none =>
      rw [hLookup] at hGet
      nomatch hGet
    | some c =>
      rw [hLookup] at hGet
      dsimp at hGet
      cases hOk : valDepthOk d c with
      | false =>
        rw [hOk] at hGet
        nomatch hGet
      | true =>
        rw [hOk] at hGet
        injection hGet with hEq
        subst hEq
        dsimp [setMirFieldAt]
        rw [hOk]
        dsimp
        rw [getElem?_setElem? fields f c hLookup]
  | scalar _ => nomatch hGet
  | ptr _ => nomatch hGet
  | bool _ => nomatch hGet
  | unit => nomatch hGet
  | enumVal _ _ => nomatch hGet
  | bytes _ => nomatch hGet

/-- Lens law `put_get` for `getMirFieldAt d` and `setMirFieldAt d`. -/
theorem mir_setField_getField {d : Nat} (f : FieldIdx) (s a s' : Val)
    (hPut : setMirFieldAt d f s a = some s') :
    getMirFieldAt d f s' = some a := by
  cases s with
  | tuple fields =>
    dsimp [setMirFieldAt] at hPut
    cases hOk : valDepthOk d a with
    | false =>
      rw [hOk] at hPut
      nomatch hPut
    | true =>
      rw [hOk] at hPut
      dsimp at hPut
      cases hRec : mirListSet? fields f a with
      | none =>
        rw [hRec] at hPut
        nomatch hPut
      | some fields' =>
        rw [hRec] at hPut
        injection hPut with hEq
        subst hEq
        dsimp [getMirFieldAt]
        rw [setElem?_getElem? fields f a fields' hRec]
        dsimp
        rw [hOk]
        rfl
  | scalar _ => nomatch hPut
  | ptr _ => nomatch hPut
  | bool _ => nomatch hPut
  | unit => nomatch hPut
  | enumVal _ _ => nomatch hPut
  | bytes _ => nomatch hPut

/-- Lens law `put_put` for `setMirFieldAt d`. -/
theorem mir_setField_setField {d : Nat} (f : FieldIdx) (s a1 a2 s1 : Val)
    (hPut1 : setMirFieldAt d f s a1 = some s1) :
    setMirFieldAt d f s1 a2 = setMirFieldAt d f s a2 := by
  cases s with
  | tuple fields =>
    dsimp [setMirFieldAt] at hPut1
    cases hOk1 : valDepthOk d a1 with
    | false =>
      rw [hOk1] at hPut1
      nomatch hPut1
    | true =>
      rw [hOk1] at hPut1
      dsimp at hPut1
      cases hRec : mirListSet? fields f a1 with
      | none =>
        rw [hRec] at hPut1
        nomatch hPut1
      | some fields1 =>
        rw [hRec] at hPut1
        injection hPut1 with hEq
        subst hEq
        dsimp [setMirFieldAt]
        cases valDepthOk d a2 with
        | false => rfl
        | true =>
          dsimp
          rw [setElem?_setElem? fields f a1 a2 fields1 hRec]
  | scalar _ => nomatch hPut1
  | ptr _ => nomatch hPut1
  | bool _ => nomatch hPut1
  | unit => nomatch hPut1
  | enumVal _ _ => nomatch hPut1
  | bytes _ => nomatch hPut1

/-- Separation law `getField_setField_other` for `getMirFieldAt d` and
`setMirFieldAt d`. -/
theorem mir_getField_setField_other {d : Nat} (f g : FieldIdx) (s a s' : Val)
    (hNe : f ≠ g) (hPut : setMirFieldAt d f s a = some s') :
    getMirFieldAt d g s' = getMirFieldAt d g s := by
  cases s with
  | tuple fields =>
    dsimp [setMirFieldAt] at hPut
    cases hOk : valDepthOk d a with
    | false =>
      rw [hOk] at hPut
      nomatch hPut
    | true =>
      rw [hOk] at hPut
      dsimp at hPut
      cases hRec : mirListSet? fields f a with
      | none =>
        rw [hRec] at hPut
        nomatch hPut
      | some fields' =>
        rw [hRec] at hPut
        injection hPut with hEq
        subst hEq
        dsimp [getMirFieldAt]
        rw [getElem?_setElem?_other fields f g a fields' hNe hRec]
  | scalar _ => nomatch hPut
  | ptr _ => nomatch hPut
  | bool _ => nomatch hPut
  | unit => nomatch hPut
  | enumVal _ _ => nomatch hPut
  | bytes _ => nomatch hPut

/-- Commutation law `setField_setField_comm` for `setMirFieldAt d`. -/
theorem mir_setField_setField_comm {d : Nat} (f g : FieldIdx)
    (s a b s1 s2 : Val)
    (hNe : f ≠ g)
    (h1 : setMirFieldAt d f s a = some s1)
    (h2 : setMirFieldAt d g s1 b = some s2) :
    Exists fun s1' =>
      setMirFieldAt d g s b = some s1' ∧
      setMirFieldAt d f s1' a = some s2 := by
  cases s with
  | tuple fields =>
    dsimp [setMirFieldAt] at h1
    cases hOkA : valDepthOk d a with
    | false =>
      rw [hOkA] at h1
      nomatch h1
    | true =>
      rw [hOkA] at h1
      dsimp at h1
      cases hF : mirListSet? fields f a with
      | none =>
        rw [hF] at h1
        nomatch h1
      | some fields1 =>
        rw [hF] at h1
        injection h1 with hEq1
        subst hEq1
        dsimp [setMirFieldAt] at h2
        cases hOkB : valDepthOk d b with
        | false =>
          rw [hOkB] at h2
          nomatch h2
        | true =>
          rw [hOkB] at h2
          dsimp at h2
          cases hG : mirListSet? fields1 g b with
          | none =>
            rw [hG] at h2
            nomatch h2
          | some fields2 =>
            rw [hG] at h2
            injection h2 with hEq2
            subst hEq2
            cases setElem?_setElem?_comm fields f g a b fields1 fields2 hNe hF
                hG with
            | intro fields1' hPair =>
              refine ⟨.tuple fields1', ?_, ?_⟩
              · dsimp [setMirFieldAt]
                rw [hOkB]
                dsimp
                rw [hPair.1]
              · dsimp [setMirFieldAt]
                rw [hOkA]
                dsimp
                rw [hPair.2]
  | scalar _ => nomatch h1
  | ptr _ => nomatch h1
  | bool _ => nomatch h1
  | unit => nomatch h1
  | enumVal _ _ => nomatch h1
  | bytes _ => nomatch h1

/-- Bit width (`8`, `16`, `32`, `64`, or `128`) of `IntWidth` on 64-bit
targets. -/
def mirBitWidth : IntWidth → Nat
  | .i8 => 8
  | .i16 => 16
  | .i32 => 32
  | .i64 | .isize => 64
  | .i128 => 128

/-- Computable width truncation on `BitVec 128`, matching
`Trusted.MirSemantics.truncateBits` (`mirTruncateBits_eq_truncateBits`). -/
def mirTruncateBits (w : IntWidth) (value : BitVec 128) : BitVec 128 :=
  let low : BitVec (mirBitWidth w - 1 - 0 + 1) :=
    BitVec.ofNat (mirBitWidth w - 1 - 0 + 1) (Nat.shiftRight value.toNat 0)
  BitVec.ofNat 128 low.toNat

/-- `mirTruncateBits` agrees with `Trusted.MirSemantics.truncateBits` across all
`IntWidth` variants. -/
theorem mirTruncateBits_eq_truncateBits (w : IntWidth) (value : BitVec 128) :
    mirTruncateBits w value = truncateBits w value := by
  cases w <;> rfl

/-- Concrete boolean extraction on `Trusted.MirSemantics.Val` for `PureLift`
branch and loop conditions: `.bool b` extracts `b`, `.scalar sv` masks `sv.bits`
to `sv.width` via `mirTruncateBits sv.width sv.bits` (matching
`Trusted.MirSemantics.evalSwitchBranches` and `decodeScalar`) and tests whether
the masked bits are nonzero, and all other values return `some false` because
`Trusted.MirSemantics.Val` is a concrete value domain with no symbolic choice
constructor. Branch and loop conditions in `FlowPlan`s should guard non-boolean,
non-scalar values via `mirBoolOrScalarVal` so invalid guard types fail closed
with `.fail`. -/
def mirAsBool (v : Val) : Option Bool :=
  match v with
  | .bool b => some b
  | .scalar sv => some (!Nat.beq (mirTruncateBits sv.width sv.bits).toNat 0)
  | _ => some false

/-- Strict boolean/scalar condition filter for `FlowPlan` branch and loop
guards: preserves `.bool` and `.scalar` values and returns `none` (causing
`evalRval` to fail closed with `.fail`) on `.unit`, `.tuple`, `.enumVal`,
`.ptr`, and encoded `.bytes` borrow handles. -/
def mirBoolOrScalarVal : Val → Option Val
  | .bool b => some (.bool b)
  | .scalar sv => some (.scalar sv)
  | _ => none

/-- Conditional branch value selector on `Trusted.MirSemantics.Val`. -/
def mirZipVal (cond vt vf : Val) : Val :=
  match mirAsBool cond with
  | some true => vt
  | _ => vf

/-- `mirAsBool` never returns `none` because `Trusted.MirSemantics.Val` has no
symbolic choice constructor, so the `ValAlgebra` laws guarded by
`asBool cond = none` hold vacuously for `mirValAlgAt d`. -/
theorem mirAsBool_ne_none (v : Val) : mirAsBool v ≠ none := by
  intro h
  cases v <;> nomatch h

/-- Encode a `SubPath` as provenance-tagged `AllocByte` entries inside
`Val.bytes` for `PureLift` first-order reference handle tracking. -/
def encodeSubPathBytes (path : SubPath) : List AllocByte :=
  path.foldr (fun f ih => .init 0 (some f) :: ih) []

/-- Decode a `SubPath` from provenance-tagged `AllocByte` entries. -/
def decodeSubPathBytes (bytes : List AllocByte) : Option SubPath :=
  bytes.foldr
    (fun b0 ih =>
      match b0 with
      | .init b (some f) =>
        if b == 0 then
          match ih with
          | some fs => some (f :: fs)
          | none => none
        else
          none
      | _ => none)
    (some [])

theorem decodeSubPathBytes_encodeSubPathBytes :
    ∀ (path : SubPath),
      decodeSubPathBytes (encodeSubPathBytes path) = some path
  | [] => rfl
  | f :: rest => by
    change (match decodeSubPathBytes (encodeSubPathBytes rest) with
      | some fs => some (f :: fs)
      | none => none) = some (f :: rest)
    rw [decodeSubPathBytes_encodeSubPathBytes rest]

/-- Encode a mutable borrow handle `(lid, path)` as a `Val.bytes` leaf. -/
def mirEncodeRef (lid : LoanId) (path : SubPath) : Val :=
  .bytes (.init 0 (some lid) :: encodeSubPathBytes path)

/-- Encode a shared borrow handle `(lid, path)` as a `Val.bytes` leaf. -/
def mirEncodeSharedRef (lid : LoanId) (path : SubPath) : Val :=
  .bytes (.init 1 (some lid) :: encodeSubPathBytes path)

/-- Decode a borrow handle `(lid, path)` from a `Val.bytes` leaf. -/
def mirDecodeRef : Val → Option (LoanId × SubPath)
  | .bytes (.init tag (some lid) :: rest) =>
    if tag == 0 || tag == 1 then
      match decodeSubPathBytes rest with
      | some path => some (lid, path)
      | none => none
    else
      none
  | _ => none

/-- Distinguish shared (`tag == 1`) from mutable (`tag == 0`) encoded borrow
handles. -/
def mirDecodeRefIsShared : Val → Bool
  | .bytes (.init tag (some _) :: _) => tag == 1
  | _ => false

theorem mir_decodeRef_encodeRef (lid : LoanId) (path : SubPath) :
    mirDecodeRef (mirEncodeRef lid path) = some (lid, path) := by
  dsimp [mirEncodeRef, mirDecodeRef]
  rw [decodeSubPathBytes_encodeSubPathBytes path]

theorem mir_decodeRef_encodeSharedRef (lid : LoanId) (path : SubPath) :
    mirDecodeRef (mirEncodeSharedRef lid path) = some (lid, path) := by
  dsimp [mirEncodeSharedRef, mirDecodeRef]
  rw [decodeSubPathBytes_encodeSubPathBytes path]

theorem mir_decodeRef_getField {d : Nat} (f : FieldIdx) (v : Val)
    (r : LoanId × SubPath)
    (hDec : mirDecodeRef v = some r) :
    getMirFieldAt d f v = none := by
  cases v with
  | bytes _ => rfl
  | scalar _ => nomatch hDec
  | ptr _ => nomatch hDec
  | bool _ => nomatch hDec
  | unit => nomatch hDec
  | enumVal _ _ => nomatch hDec
  | tuple _ => nomatch hDec

/-- Rename `oldLid` to `newLid` in an encoded borrow-handle byte list. -/
def remapMirBytes (oldLid newLid : LoanId) (data : List AllocByte) :
    List AllocByte :=
  match data with
  | .init tag (some lid) :: rest =>
    if tag == 0 || tag == 1 then
      match decodeSubPathBytes rest with
      | some _ =>
        .init tag (some (if lid == oldLid then newLid else lid)) :: rest
      | none => data
    else
      data
  | _ => data

/-- Depth-indexed loan-ID remapping across `Val` via `natFold` and
`List.foldr`. -/
def remapMirValAt (oldLid newLid : LoanId) (d : Nat) (v : Val) : Val :=
  natFold
    (fun x =>
      match x with
      | .bytes data => .bytes (remapMirBytes oldLid newLid data)
      | other => other)
    (fun k ih x =>
      match x with
      | .tuple fields =>
        .tuple
          (fields.foldr
            (fun c acc => (if valDepthOk k c then ih c else c) :: acc)
            [])
      | .bytes data => .bytes (remapMirBytes oldLid newLid data)
      | other => other)
    d v

/-- Rename loan `oldLid` to `newLid` in every encoded reference handle inside
`v` up to child tuple depth `d` (enclosing tuple depth `d + 1`). -/
def remapMirValAtDepth (d : Nat) (oldLid newLid : LoanId) (v : Val) : Val :=
  remapMirValAt oldLid newLid (d + 1) v

theorem mirListGet?_foldr_map {α : Type} (g : α → α) :
    ∀ (xs : List α) (f : Nat),
      mirListGet? (xs.foldr (fun c acc => g c :: acc) []) f =
        (mirListGet? xs f).map g
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, f + 1 => mirListGet?_foldr_map g xs f

theorem valDepthOk_remapMirValAt (oldLid newLid : LoanId) :
    ∀ (k : Nat) (v : Val),
      valDepthOk k (remapMirValAt oldLid newLid k v) = valDepthOk k v
  | 0, v => by
    cases v <;> rfl
  | k + 1, v => by
    cases v with
    | tuple fields =>
      change (fields.foldr
        (fun c acc =>
          (if valDepthOk k c then remapMirValAt oldLid newLid k c else c) ::
            acc)
        []).foldr (fun c acc => valDepthOk k c && acc) true =
        fields.foldr (fun c acc => valDepthOk k c && acc) true
      induction fields with
      | nil => rfl
      | cons c cs ihCs =>
        change (valDepthOk k
          (if valDepthOk k c then remapMirValAt oldLid newLid k c else c) &&
          _) = (valDepthOk k c && _)
        rw [ihCs]
        cases hOk : valDepthOk k c with
        | false =>
          dsimp
          rw [hOk]
        | true =>
          dsimp
          rw [valDepthOk_remapMirValAt oldLid newLid k c, hOk]
    | scalar _ => rfl
    | ptr _ => rfl
    | bool _ => rfl
    | unit => rfl
    | enumVal _ _ => rfl
    | bytes _ => rfl

theorem remapMirValAt_eq_succ (oldLid newLid : LoanId) :
    ∀ (k : Nat) (v : Val),
      valDepthOk k v = true →
      remapMirValAt oldLid newLid (k + 1) v = remapMirValAt oldLid newLid k v
  | 0, v, hOk => by
    cases v with
    | tuple _ => nomatch hOk
    | scalar _ => rfl
    | ptr _ => rfl
    | bool _ => rfl
    | unit => rfl
    | enumVal _ _ => rfl
    | bytes _ => rfl
  | k + 1, v, hOk => by
    cases v with
    | tuple fields =>
      change Val.tuple _ = Val.tuple _
      apply congrArg Val.tuple
      induction fields with
      | nil => rfl
      | cons c cs ihCs =>
        change (valDepthOk k c &&
          cs.foldr (fun x acc => valDepthOk k x && acc) true) = true at hOk
        cases hC : valDepthOk k c with
        | false =>
          rw [hC] at hOk
          nomatch hOk
        | true =>
          rw [hC] at hOk
          change cs.foldr (fun x acc => valDepthOk k x && acc) true = true
            at hOk
          have hC1 : valDepthOk (k + 1) c = true := valDepthOk_mono k c hC
          change (if valDepthOk (k + 1) c then
              remapMirValAt oldLid newLid (k + 1) c else c) :: _ =
            (if valDepthOk k c then
              remapMirValAt oldLid newLid k c else c) :: _
          rw [hC1, hC]
          dsimp
          rw [remapMirValAt_eq_succ oldLid newLid k c hC, ihCs hOk]
    | scalar _ => rfl
    | ptr _ => rfl
    | bool _ => rfl
    | unit => rfl
    | enumVal _ _ => rfl
    | bytes _ => rfl

theorem mir_decodeRef_remapRefInVal {d : Nat} (oldLid newLid : LoanId)
    (v : Val) :
    mirDecodeRef (remapMirValAtDepth d oldLid newLid v) =
      (mirDecodeRef v).map
        (fun r => (if r.1 == oldLid then newLid else r.1, r.2)) := by
  cases v with
  | scalar _ => rfl
  | ptr _ => rfl
  | bool _ => rfl
  | unit => rfl
  | enumVal _ _ => rfl
  | tuple _ => rfl
  | bytes data =>
    cases data with
    | nil => rfl
    | cons b0 rest =>
      cases b0 with
      | uninit => rfl
      | init tag prov =>
        cases prov with
        | none => rfl
        | some lid =>
          change mirDecodeRef (.bytes (remapMirBytes oldLid newLid
            (.init tag (some lid) :: rest))) =
            (mirDecodeRef (.bytes (.init tag (some lid) :: rest))).map
              (fun r => (if r.1 == oldLid then newLid else r.1, r.2))
          dsimp [remapMirBytes, mirDecodeRef]
          cases hTag : (tag == 0 || tag == 1) with
          | false =>
            dsimp [mirDecodeRef]
            rw [hTag]
            rfl
          | true =>
            dsimp
            cases hPath : decodeSubPathBytes rest with
            | none =>
              dsimp [mirDecodeRef]
              rw [hTag, hPath]
              rfl
            | some path =>
              dsimp [mirDecodeRef]
              rw [hTag, hPath]
              rfl

/-- Remap child value `c` at tuple depth `d` when `valDepthOk d c` holds. -/
def remapChildAt (d : Nat) (oldLid newLid : LoanId) (c : Val) : Val :=
  if valDepthOk d c then remapMirValAt oldLid newLid d c else c

theorem remapChildAt_of_false {d : Nat} (oldLid newLid : LoanId) (c : Val)
    (hOk : valDepthOk d c = false) :
    remapChildAt d oldLid newLid c = c := by
  dsimp [remapChildAt]
  rw [hOk]
  rfl

theorem remapChildAt_of_true {d : Nat} (oldLid newLid : LoanId) (c : Val)
    (hOk : valDepthOk d c = true) :
    remapChildAt d oldLid newLid c = remapMirValAt oldLid newLid d c := by
  dsimp [remapChildAt]
  rw [hOk]
  rfl

theorem mir_getField_remapRefInVal {d : Nat} (oldLid newLid : LoanId)
    (f : FieldIdx) (v : Val) :
    getMirFieldAt d f (remapMirValAtDepth d oldLid newLid v) =
      (getMirFieldAt d f v).map (remapMirValAtDepth d oldLid newLid) := by
  cases v with
  | scalar _ => rfl
  | ptr _ => rfl
  | bool _ => rfl
  | unit => rfl
  | enumVal _ _ => rfl
  | bytes _ => rfl
  | tuple fields =>
    change getMirFieldAt d f
      (.tuple (fields.foldr (fun c acc => remapChildAt d oldLid newLid c :: acc)
        [])) =
      (getMirFieldAt d f (.tuple fields)).map
        (remapMirValAtDepth d oldLid newLid)
    dsimp [getMirFieldAt]
    rw [mirListGet?_foldr_map (remapChildAt d oldLid newLid) fields f]
    cases mirListGet? fields f with
    | none => rfl
    | some c =>
      dsimp [Option.map]
      cases hOk : valDepthOk d c with
      | false =>
        rw [remapChildAt_of_false oldLid newLid c hOk, hOk]
        rfl
      | true =>
        rw [remapChildAt_of_true oldLid newLid c hOk]
        rw [valDepthOk_remapMirValAt oldLid newLid d c, hOk]
        dsimp [remapMirValAtDepth]
        rw [remapMirValAt_eq_succ oldLid newLid d c hOk]

theorem foldr_keep_of_getMirField_none {d : Nat} (oldLid newLid : LoanId) :
    ∀ (fields : List Val),
      (∀ f, getMirFieldAt d f (.tuple fields) = none) →
      fields.foldr
        (fun c acc =>
          (if valDepthOk d c then remapMirValAt oldLid newLid d c else c) ::
            acc)
        [] = fields
  | [], _ => rfl
  | c :: cs, hNone => by
    have h0 : getMirFieldAt d 0 (.tuple (c :: cs)) = none := hNone 0
    change (if valDepthOk d c then some c else none) = none at h0
    have hTail : ∀ f, getMirFieldAt d f (.tuple cs) = none :=
      fun f => hNone (f + 1)
    change (if valDepthOk d c then remapMirValAt oldLid newLid d c else c) ::
      _ = c :: cs
    rw [foldr_keep_of_getMirField_none oldLid newLid cs hTail]
    cases hOk : valDepthOk d c with
    | false => rfl
    | true =>
      rw [hOk] at h0
      nomatch h0

theorem mir_remapRefInVal_leaf {d : Nat} (oldLid newLid : LoanId) (v : Val)
    (hDec : mirDecodeRef v = none)
    (hFields : ∀ f, getMirFieldAt d f v = none) :
    remapMirValAtDepth d oldLid newLid v = v := by
  cases v with
  | scalar _ => rfl
  | ptr _ => rfl
  | bool _ => rfl
  | unit => rfl
  | enumVal _ _ => rfl
  | tuple fields =>
    change Val.tuple _ = Val.tuple fields
    exact congrArg Val.tuple
      (foldr_keep_of_getMirField_none oldLid newLid fields hFields)
  | bytes data =>
    cases data with
    | nil => rfl
    | cons b0 rest =>
      cases b0 with
      | uninit => rfl
      | init tag prov =>
        cases prov with
        | none => rfl
        | some lid =>
          dsimp [mirDecodeRef] at hDec
          change Val.bytes (remapMirBytes oldLid newLid
            (.init tag (some lid) :: rest)) =
            .bytes (.init tag (some lid) :: rest)
          dsimp [remapMirBytes]
          cases hTag : (tag == 0 || tag == 1) with
          | false => rfl
          | true =>
            rw [hTag] at hDec
            dsimp at hDec
            cases hPath : decodeSubPathBytes rest with
            | none => rfl
            | some _ =>
              rw [hPath] at hDec
              nomatch hDec

/-- Depth-indexed structural size bound on `Val` via `natFold` and
`List.foldr`. -/
def valSizeBoundAt (d : Nat) (v : Val) : Nat :=
  natFold
    (fun _ => 1)
    (fun _ ih x =>
      match x with
      | .tuple fields => fields.foldr (fun c acc => ih c + acc + 1) 0 + 1
      | _ => 1)
    d v

/-- Strict upper bound on field indices and aggregate nesting depth of `v` up
to child tuple depth `d` (enclosing tuple depth `d + 1`). -/
def valSizeBoundAtDepth (d : Nat) (v : Val) : Nat :=
  valSizeBoundAt (d + 1) v

theorem valSizeBoundAt_eq_succ :
    ∀ (k : Nat) (v : Val),
      valDepthOk k v = true →
      valSizeBoundAt (k + 1) v = valSizeBoundAt k v
  | 0, v, hOk => by
    cases v with
    | tuple _ => nomatch hOk
    | scalar _ => rfl
    | ptr _ => rfl
    | bool _ => rfl
    | unit => rfl
    | enumVal _ _ => rfl
    | bytes _ => rfl
  | k + 1, v, hOk => by
    cases v with
    | tuple fields =>
      change _ + 1 = _ + 1
      apply congrArg (fun n => n + 1)
      induction fields with
      | nil => rfl
      | cons c cs ihCs =>
        change (valDepthOk k c &&
          cs.foldr (fun x acc => valDepthOk k x && acc) true) = true at hOk
        cases hC : valDepthOk k c with
        | false =>
          rw [hC] at hOk
          nomatch hOk
        | true =>
          rw [hC] at hOk
          change cs.foldr (fun x acc => valDepthOk k x && acc) true = true
            at hOk
          change valSizeBoundAt (k + 1) c + _ + 1 =
            valSizeBoundAt k c + _ + 1
          rw [valSizeBoundAt_eq_succ k c hC, ihCs hOk]
    | scalar _ => rfl
    | ptr _ => rfl
    | bool _ => rfl
    | unit => rfl
    | enumVal _ _ => rfl
    | bytes _ => rfl

theorem mirListGet?_lt_foldr_size (sz : Val → Nat) :
    ∀ (fields : List Val) (f : FieldIdx) (c : Val),
      mirListGet? fields f = some c →
      f < fields.foldr (fun x acc => sz x + acc + 1) 0 + 1 ∧
      sz c < fields.foldr (fun x acc => sz x + acc + 1) 0 + 1
  | [], _, _, hGet => nomatch hGet
  | x :: xs, 0, c, hGet => by
    change some x = some c at hGet
    injection hGet with hEq
    subst hEq
    let tailSum := xs.foldr (fun y acc => sz y + acc + 1) 0
    change 0 < (sz x + tailSum + 1) + 1 ∧ sz x < (sz x + tailSum + 1) + 1
    refine ⟨Nat.zero_lt_succ _, ?_⟩
    exact Nat.lt_succ_of_le (Nat.le_succ_of_le (Nat.le_add_right _ _))
  | x :: xs, f + 1, c, hGet => by
    change mirListGet? xs f = some c at hGet
    have hSub := mirListGet?_lt_foldr_size sz xs f c hGet
    let tailSum := xs.foldr (fun y acc => sz y + acc + 1) 0
    change f + 1 < (sz x + tailSum + 1) + 1 ∧
      sz c < (sz x + tailSum + 1) + 1
    have hLe : tailSum + 1 ≤ sz x + tailSum + 1 :=
      Nat.succ_le_succ (Nat.le_add_left tailSum (sz x))
    refine ⟨Nat.succ_lt_succ (Nat.lt_of_lt_of_le hSub.1 hLe), ?_⟩
    exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt hSub.2) hLe)

theorem mir_getField_lt_sizeBound {d : Nat} (f : FieldIdx) (v c : Val)
    (hGet : getMirFieldAt d f v = some c) :
    f < valSizeBoundAtDepth d v ∧
    valSizeBoundAtDepth d c < valSizeBoundAtDepth d v := by
  cases v with
  | tuple fields =>
    dsimp [getMirFieldAt] at hGet
    cases hLookup : mirListGet? fields f with
    | none =>
      rw [hLookup] at hGet
      nomatch hGet
    | some c0 =>
      rw [hLookup] at hGet
      dsimp at hGet
      cases hOk : valDepthOk d c0 with
      | false =>
        rw [hOk] at hGet
        nomatch hGet
      | true =>
        rw [hOk] at hGet
        injection hGet with hEq
        subst hEq
        have hBounds :=
          mirListGet?_lt_foldr_size (valSizeBoundAt d) fields f c0 hLookup
        dsimp [valSizeBoundAtDepth]
        rw [valSizeBoundAt_eq_succ d c0 hOk]
        exact hBounds
  | scalar _ => nomatch hGet
  | ptr _ => nomatch hGet
  | bool _ => nomatch hGet
  | unit => nomatch hGet
  | enumVal _ _ => nomatch hGet
  | bytes _ => nomatch hGet

/-- Depth-parametric instantiation of `PureLift.ValAlgebra` for
`Trusted.MirSemantics.Val` at arbitrary child tuple depth `d : Nat` (enclosing
tuple depth `d + 1`). -/
def mirValAlgAt (d : Nat) : ValAlgebra Val where
  defaultVal := .unit
  asBool := mirAsBool
  zipVal := mirZipVal
  projectBranchVal_concrete _ _ _ _ _ := rfl
  projectBranchVal_zip_true cond _ _ h := absurd h (mirAsBool_ne_none cond)
  projectBranchVal_zip_false cond _ _ h := absurd h (mirAsBool_ne_none cond)
  getField := getMirFieldAt d
  getField_projectBranchVal _ _ _ _ _ h := h
  setField := setMirFieldAt d
  getField_setField := mir_getField_setField
  setField_getField := mir_setField_getField
  setField_setField := mir_setField_setField
  getField_setField_other := mir_getField_setField_other
  setField_setField_comm := mir_setField_setField_comm
  encodeRef := mirEncodeRef
  encodeSharedRef := mirEncodeSharedRef
  decodeRef := mirDecodeRef
  decodeRefIsShared := mirDecodeRefIsShared
  decodeRef_encodeRef := mir_decodeRef_encodeRef
  decodeRef_encodeSharedRef := mir_decodeRef_encodeSharedRef
  decodeRefIsShared_encodeSharedRef _ _ := rfl
  decodeRefIsShared_encodeRef _ _ := Or.inr rfl
  decodeRef_getField := mir_decodeRef_getField
  branchSplit _ := none
  decodeRef_branchSplit _ _ _ := rfl
  branchSplit_zipVal cond _ _ h := absurd h (mirAsBool_ne_none cond)
  sameCond _ _ := false
  sameCond_eq _ _ h := nomatch h
  remapRefInVal := remapMirValAtDepth d
  decodeRef_remapRefInVal := mir_decodeRef_remapRefInVal
  getField_remapRefInVal := mir_getField_remapRefInVal
  branchSplit_remapRefInVal _ _ _ := rfl
  remapRefInVal_leaf oldLid newLid v hDec hFields _ :=
    mir_remapRefInVal_leaf oldLid newLid v hDec hFields
  sizeBound := valSizeBoundAtDepth d
  getField_lt_sizeBound := mir_getField_lt_sizeBound
  sameAggregateShape _ _ := false
  sameAggregateShape_ext _ _ hShape _ := nomatch hShape
  sameAggregateShape_setField _ _ _ _ _ hShape _ := nomatch hShape

/-- Default instantiation of `PureLift.ValAlgebra` for
`Trusted.MirSemantics.Val` (`d = 7`, aggregate depth `8`). -/
def mirValAlg : ValAlgebra Val := mirValAlgAt 7

/-- `fieldLens (mirValAlgAt d) f` satisfies the three bidirectional lens laws
for every depth bound `d : Nat` and field index `f : FieldIdx`. -/
theorem mirFieldLensAt_lawful (d : Nat) (f : FieldIdx) :
    LawfulLens Val Val (fieldLens (mirValAlgAt d) f) :=
  fieldLens_lawful (mirValAlgAt d) f

/-- Every nested sub-place path lens `subPathLens (mirValAlgAt d) path` is
lawful at arbitrary depth bound `d : Nat`. -/
theorem mirSubPathLensAt_lawful (d : Nat) (path : SubPath) :
    LawfulLens Val Val (subPathLens (mirValAlgAt d) path) :=
  subPathLens_lawful (mirValAlgAt d) path

/-- `fieldLens mirValAlg f` satisfies the three bidirectional lens laws
(`get_put`, `put_get`, and `put_put`) for every field index `f : FieldIdx`. -/
theorem mirFieldLens_lawful (f : FieldIdx) :
    LawfulLens Val Val (fieldLens mirValAlg f) :=
  mirFieldLensAt_lawful 7 f

/-- Every nested sub-place path lens `subPathLens mirValAlg path` is lawful. -/
theorem mirSubPathLens_lawful (path : SubPath) :
    LawfulLens Val Val (subPathLens mirValAlg path) :=
  mirSubPathLensAt_lawful 7 path

/-! ## Unified `MirWp` Operational Execution Predicates and Adapter Bridge -/

/-- Multi-step fuel-bounded normal-completion predicate from an in-flight
`State`, unified directly as an abbreviation of `Anneal.MirWp.execState`. -/
abbrev MirStepsDone (p : Program) (out : TerminalOut) (fuel : Nat)
    (s : State) : Prop :=
  Anneal.MirWp.execState p fuel s (fun out' => out' = out)

/-- Whole-program fuel-bounded normal-completion predicate starting from
`Trusted.MirSemantics.initState p q`, unified directly as an abbreviation of
`Anneal.MirWp.execProg`. -/
abbrev MirRunsDone (p : Program) (q : Query) (fuel : Nat)
    (out : TerminalOut) : Prop :=
  Anneal.MirWp.execProg p fuel q (fun out' => out' = out)

/-- Proving `MirRunsDone p q fuel out` with `post out` establishes
`WellFormed p q`, `Behavior p q out`, `¬ Diverges p q`, and
`SatisfiesPost p q post` in $M_{\text{anneal}}$ (a restatement of
`Anneal.MirWp.spec_and_behavior_of_wp_eq`). -/
theorem satisfiesPost_and_behavior_of_mirRunsDone
    (p : Program) (q : Query) (fuel : Nat) (out : TerminalOut)
    (post : TerminalOut → Prop)
    (hRun : MirRunsDone p q fuel out)
    (hPost : post out) :
    WellFormed p q ∧
    Behavior p q out ∧
    ¬ Diverges p q ∧
    SatisfiesPost p q post :=
  let h := Anneal.MirWp.spec_and_behavior_of_wp_eq
    (Anneal.MirWp.wpProg_of_execProg hRun)
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 post hPost⟩

/-- Whole-program fuel-bounded fault-reachability predicate starting from
`Trusted.MirSemantics.initState p q`, unified directly as an abbreviation of
`Anneal.MirWp.execFaultProg`. -/
abbrev MirRunsFault (p : Program) (q : Query) (fuel : Nat)
    (expected : FaultKind) : Prop :=
  Anneal.MirWp.execFaultProg p fuel q expected

/-- Proving `MirRunsFault p q fuel expected` establishes
`ReachesResult p q (.fault expected)`, rules out any other fault kind
`k ≠ expected`, rules out normal `Behavior` and `Diverges`, and refutes
`WellFormed p q`. -/
theorem reachesFault_of_mirRunsFault (p : Program) (q : Query) (fuel : Nat)
    (expected : FaultKind)
    (hRun : MirRunsFault p q fuel expected) :
    ReachesResult p q (.fault expected) ∧
    (∀ k : FaultKind, k ≠ expected → ¬ ReachesResult p q (.fault k)) ∧
    (∀ out : TerminalOut, ¬ Behavior p q out) ∧
    ¬ Diverges p q ∧
    ¬ WellFormed p q := by
  exact Anneal.MirWp.reaches_fault_and_exclusive_of_wpFault p q fuel expected
    (Anneal.MirWp.wpFaultProg_of_execFaultProg hRun)

/-! ## By-Value Operational Adapter and `CorrespondenceClaim` Bridge -/

/-- True iff every `PureLift` entry parameter uses `.byVal` passing mode,
matching `Trusted.MirSemantics` v1 top-level entry execution where
`callerMem = ⟨[]⟩` and reference/tuple parameter types are outside the
supported entry fragment. -/
def mirAllByValParams (params : List (ParamInput Val)) : Bool :=
  params.foldr
    (fun p ih =>
      (match p.mode with
       | .byVal => true
       | _ => false) && ih)
    true

/-- Extract the runtime argument values from a `PureLift` parameter list. -/
def mirParamVals (params : List (ParamInput Val)) : List Val :=
  params.foldr (fun p ih => p.val :: ih) []

/-- Lift a list of runtime MIR entry arguments into `.byVal` `PureLift`
parameter descriptors via `List.foldr`. -/
def mirByValParams (args : List Val) : List (ParamInput Val) :=
  args.foldr (fun v acc => ⟨.byVal, v⟩ :: acc) []

theorem mirAllByValParams_byValParams :
    ∀ (args : List Val), mirAllByValParams (mirByValParams args) = true
  | [] => rfl
  | _ :: rest => by
    change (true && mirAllByValParams (mirByValParams rest)) = true
    rw [mirAllByValParams_byValParams rest]
    rfl

theorem mirParamVals_byValParams :
    ∀ (args : List Val), mirParamVals (mirByValParams args) = args
  | [] => rfl
  | v :: rest => by
    change v :: mirParamVals (mirByValParams rest) = v :: rest
    rw [mirParamVals_byValParams rest]

theorem length_mirByValParams :
    ∀ (args : List Val), (mirByValParams args).length = args.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (length_mirByValParams rest)

theorem list_length_take_of_le {α : Type} :
    ∀ (k : Nat) (xs : List α), k ≤ xs.length → (xs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => nomatch h
  | k + 1, _ :: xs, h =>
    congrArg Nat.succ
      (list_length_take_of_le k xs (Nat.le_of_succ_le_succ h))

/-- Parameter-alignment predicate connecting `PureLift` `params` to `(p, q)` at
entry: every parameter uses `.byVal` passing mode, `q.args` matches the
parameter values in `params`, `q.callerMem = ⟨[]⟩`, and the entry body of `p`
satisfies `params.length = body.argumentCount` and `ValidEntryArgs body q.args`.
Requiring `q.callerMem = ⟨[]⟩` and `ValidEntryArgs` rules out entry argument
and caller-memory `.unsupported` faults before the body begins executing
(`initState` also checks `pointerWidthBits = 64`, `mirProfileVersion = 1`,
non-empty `basicBlocks`, `argumentCount < locals.length`, in-bounds storage
annotations, and supported local types, though it does not check
`body.identity` as `BodyStaticAdmitted` does). -/
def MirArgsMatch (p : Program) (q : Query)
    (params : List (ParamInput Val)) : Prop :=
  mirAllByValParams params = true ∧
  q.args = mirParamVals params ∧
  q.callerMem = ⟨[]⟩ ∧
  match Trusted.MirSemantics.getElem? p.bodies p.entryDefId with
  | some body =>
    params.length = body.argumentCount ∧
    ValidEntryArgs body q.args
  | none => False

/-- Construct `MirArgsMatch` for `mirByValParams args` from `ValidEntryArgs` on
any body with `argumentCount < locals.length`. -/
theorem mirArgsMatch_byValParams {p : Program} {body : Body} {args : List Val}
    (hBody : Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body)
    (hBlt : Nat.blt body.argumentCount body.locals.length = true)
    (hValid : ValidEntryArgs body args) :
    MirArgsMatch p { args := args } (mirByValParams args) := by
  refine ⟨mirAllByValParams_byValParams args,
    (mirParamVals_byValParams args).symm, rfl, ?_⟩
  rw [hBody]
  refine ⟨?_, hValid⟩
  rw [length_mirByValParams args]
  rw [Anneal.MirWp.checkArgsMatch_length hValid]
  cases hLocs : body.locals with
  | nil =>
    rw [hLocs] at hBlt
    nomatch hBlt
  | cons _ rest =>
    rw [hLocs] at hBlt
    have hLe : body.argumentCount ≤ rest.length :=
      Nat.le_of_succ_le_succ (Nat.le_of_ble_eq_true hBlt)
    exact list_length_take_of_le body.argumentCount rest hLe

/-- `MirRunsTo p q fuel out` holds when `out` carries no mutable reference
writebacks (`out.mutFinals = []`, matching `callerMem = ⟨[]⟩` at top-level MIR
entry) and `MirRunsDone p q fuel (.returned ⟨out.ret, ⟨[]⟩⟩)` holds. -/
def MirRunsTo (p : Program) (q : Query) (fuel : Nat)
    (out : FuncOut Val) : Prop :=
  out.mutFinals = [] ∧
  MirRunsDone p q fuel (.returned ⟨out.ret, ⟨[]⟩⟩)

/-- Small-step transition relation over `M1MachState State Val` driven by
`Trusted.MirSemantics.evalStep p 0`. -/
inductive MirExecutesTo (p : Program) :
    M1MachState State Val → Nat → M1MachState State Val → Prop where
  | refl (m : M1MachState State Val) :
      MirExecutesTo p m 0 m
  | trans {m1 m2 m3 : M1MachState State Val} {k1 k2 : Nat} :
      MirExecutesTo p m1 k1 m2 →
      MirExecutesTo p m2 k2 m3 →
      MirExecutesTo p m1 (k1 + k2) m3
  | step_next {s s' : State} :
      evalStep p 0 s = .step s' →
      MirExecutesTo p (.running s) 1 (.running s')
  | step_ret {s : State} {out : FuncOut Val} :
      out.mutFinals = [] →
      evalStep p 0 s = .done (.returned ⟨out.ret, ⟨[]⟩⟩) →
      MirExecutesTo p (.running s) 1 (.returned out)

/-- Convert a fuel-bounded `MirStepsDone` run into an exact small-step
`MirExecutesTo` derivation. -/
theorem mirExecutesTo_of_mirStepsDone (p : Program) :
    ∀ (fuel : Nat) (s0 : State) (out : FuncOut Val),
      out.mutFinals = [] →
      MirStepsDone p (.returned ⟨out.ret, ⟨[]⟩⟩) fuel s0 →
      Exists fun steps => MirExecutesTo p (.running s0) steps (.returned out)
  | 0, _, _, _, hRun => False.elim hRun
  | fuel + 1, s0, out, hMut, hRun => by
    change (match evalStep p 0 s0 with
      | .step st' => MirStepsDone p (.returned ⟨out.ret, ⟨[]⟩⟩) fuel st'
      | .done out' => out' = .returned ⟨out.ret, ⟨[]⟩⟩
      | .fault _ => False) at hRun
    cases hStep : evalStep p 0 s0 with
    | step s1 =>
      rw [hStep] at hRun
      dsimp only at hRun
      cases mirExecutesTo_of_mirStepsDone p fuel s1 out hMut hRun with
      | intro steps hRest =>
        exact ⟨1 + steps,
          MirExecutesTo.trans (MirExecutesTo.step_next hStep) hRest⟩
    | done out' =>
      rw [hStep] at hRun
      dsimp only at hRun
      subst hRun
      exact ⟨1, MirExecutesTo.step_ret hMut hStep⟩
    | fault _ =>
      rw [hStep] at hRun
      exact False.elim hRun

/-- `OperationalAdapter` connecting `Trusted.MirAst.Program` and
`Trusted.MirSemantics.State` to `PureLift`. -/
def mirOperationalAdapter (p : Program) (q : Query)
    (params : List (ParamInput Val)) :
    OperationalAdapter (M1MachState State Val) Val where
  ExecutesTo := MirExecutesTo p
  StateRel symSt m :=
    match m with
    | .running s0 =>
      initFnState mirValAlg params = .ok symSt ∧
      MirArgsMatch p q params ∧
      initState p q = .ok s0
    | _ => False
  FinalLoansRel out m := m = .returned out
  exec_zero := MirExecutesTo.refl
  exec_trans := MirExecutesTo.trans

/-- Adequacy bridge specializing `pure_lift_sound` to `mirOperationalAdapter`:
given entry state `s0` (`initState p q = .ok s0`), parameter alignment
`MirArgsMatch p q params`, a `PureLift` specification proof
`HoldsFnSpec (evalFnValue mirValAlg params plan retExpr) post`, and explicit
simulation `hSim`, the operational machine reaches `.returned out` via
small-step `MirExecutesTo` transitions satisfying `post out` with
`out.mutFinals = []`. -/
theorem mir_pure_lift_sound
    (p : Program) (q : Query)
    (params : List (ParamInput Val))
    (plan : FlowPlan Val)
    (retExpr : RvalOp Val)
    (post : FuncOut Val → Prop)
    (s0 : State)
    (hArgs : MirArgsMatch p q params)
    (hInitSym : Exists fun sym0 => initFnState mirValAlg params = .ok sym0)
    (hInitMir : initState p q = .ok s0)
    (hSpec : HoldsFnSpec (evalFnValue mirValAlg params plan retExpr) post)
    (hSim : ∀ out, evalFnValue mirValAlg params plan retExpr = .ok out →
      Exists fun k => MirRunsTo p q k out) :
    Exists fun k => Exists fun mFinal => Exists fun out =>
      (mirOperationalAdapter p q params).ExecutesTo (.running s0) k mFinal ∧
      (mirOperationalAdapter p q params).FinalLoansRel out mFinal ∧
      post out := by
  cases hInitSym with
  | intro sym0 hSym0 =>
    exact pure_lift_sound
      (mirOperationalAdapter p q params)
      mirValAlg params plan retExpr post (.running s0)
      ⟨sym0, hSym0, ⟨hSym0, hArgs, hInitMir⟩⟩
      hSpec
      (by
        intro _ out _ _ hEval
        cases hSim out hEval with
        | intro fuel hk =>
          have hStep := hk.2
          unfold MirRunsDone Anneal.MirWp.execProg at hStep
          rw [hInitMir] at hStep
          dsimp only at hStep
          cases mirExecutesTo_of_mirStepsDone p fuel s0 out hk.1 hStep with
          | intro steps hExec =>
            exact ⟨steps, ⟨.returned out, hExec, rfl⟩⟩)

/-- Whole-program `PureLift` + `MirRunsTo` -> $M_{\text{anneal}}$ bridge:
given by-value parameter alignment `MirArgsMatch p q params`,
`HoldsFnSpec (evalFnValue mirValAlg params plan retExpr) post`, and explicit
per-invocation simulation `hSim`, establishes `WellFormed p q`,
`Behavior p q (.returned ⟨out.ret, ⟨[]⟩⟩)`, `¬ Diverges p q`, and
`SatisfiesPost p q` in `Trusted.MirSemantics`. -/
theorem mir_pure_lift_satisfiesPost
    (p : Program) (q : Query)
    (params : List (ParamInput Val))
    (plan : FlowPlan Val)
    (retExpr : RvalOp Val)
    (post : FuncOut Val → Prop)
    (hArgs : MirArgsMatch p q params)
    (hSpec : HoldsFnSpec (evalFnValue mirValAlg params plan retExpr) post)
    (hSim : ∀ out, evalFnValue mirValAlg params plan retExpr = .ok out →
      Exists fun fuel => MirRunsTo p q fuel out) :
    Exists fun out =>
      MirArgsMatch p q params ∧
      evalFnValue mirValAlg params plan retExpr = .ok out ∧
      out.mutFinals = [] ∧
      post out ∧
      WellFormed p q ∧
      Behavior p q (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ Diverges p q ∧
      SatisfiesPost p q
        (fun tOut => tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out) := by
  cases hEval : evalFnValue mirValAlg params plan retExpr with
  | fail =>
    rw [hEval] at hSpec
    nomatch hSpec
  | ok out =>
    rw [hEval] at hSpec
    dsimp [HoldsFnSpec] at hSpec
    cases hSim out hEval with
    | intro fuel hRun =>
      have hMir :=
        satisfiesPost_and_behavior_of_mirRunsDone p q fuel
          (.returned ⟨out.ret, ⟨[]⟩⟩)
          (fun tOut => tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out)
          hRun.2 ⟨rfl, hSpec⟩
      exact ⟨out, hArgs, rfl, hRun.1, hSpec, hMir.1, hMir.2.1, hMir.2.2.1,
        hMir.2.2.2⟩

/-- Compositional multi-body bridge discharging `BodyVerified p defId body
safetyPre` at any `defId` from per-input `PureLift` verification (`hSpec`) and
an explicit per-input `MirRunsTo` simulation proof (`hSim`) on
`entryProgForBody p defId`. -/
theorem bodyVerified_of_pure_lift
    {p : Program} {defId : DefId} {body : Body}
    {safetyPre : List Val → Prop}
    (planOf : List Val → FlowPlan Val)
    (retOf : List Val → RvalOp Val)
    (postOf : List Val → FuncOut Val → Prop)
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hAdm : BodyStaticAdmitted p body = true)
    (hSpec : ∀ args : List Val,
      ValidEntryArgs body args →
      (body.isUnsafe = true → safetyPre args) →
      HoldsFnSpec
        (evalFnValue mirValAlg (mirByValParams args) (planOf args) (retOf args))
        (postOf args))
    (hSim : ∀ (args : List Val) (out : FuncOut Val),
      ValidEntryArgs body args →
      (body.isUnsafe = true → safetyPre args) →
      evalFnValue mirValAlg (mirByValParams args) (planOf args) (retOf args) =
        .ok out →
      Exists fun fuel =>
        MirRunsTo (entryProgForBody p defId) { args := args } fuel out) :
    BodyVerified p defId body safetyPre := by
  have hBlt : Nat.blt body.argumentCount body.locals.length = true := by
    unfold BodyStaticAdmitted at hAdm
    cases hB : Nat.blt body.argumentCount body.locals.length with
    | true => rfl
    | false =>
      rw [hB, Bool.and_false, Bool.false_and, Bool.false_and,
        Bool.false_and] at hAdm
      cases hAdm
  refine ⟨hBody, hAdm, fun args hValid hSafe => ?_⟩
  have hEntryBody :
      Trusted.MirSemantics.getElem? (entryProgForBody p defId).bodies
        (entryProgForBody p defId).entryDefId = some body := hBody
  have hArgs :
      MirArgsMatch (entryProgForBody p defId) { args := args }
        (mirByValParams args) :=
    mirArgsMatch_byValParams hEntryBody hBlt hValid
  cases mir_pure_lift_satisfiesPost (entryProgForBody p defId) { args := args }
      (mirByValParams args) (planOf args) (retOf args) (postOf args) hArgs
      (hSpec args hValid hSafe)
      (fun out hEv => hSim args out hValid hSafe hEv) with
  | intro _ hRes => exact hRes.2.2.2.2.1

/-- Abstract interface of `Trusted.Correspondence.CorrespondenceClaim`,
parameterized over `(RefProg, encodeProg, RefWellFormed, RefBehavior,
RefDiverges)`. When instantiated with the definitions in
`Trusted.Correspondence`, `MirCorrespondenceBridge encodeProg RefWellFormed
RefBehavior RefDiverges` is definitionally equal (`rfl`) to
`Trusted.Correspondence.CorrespondenceClaim` (proved by
`Anneal.MirCorrespondenceProof.correspondence_claim_holds`). -/
def MirCorrespondenceBridge
    {RefProg : Type}
    (encodeProg : Program → RefProg)
    (RefWellFormed : RefProg → Query → Prop)
    (RefBehavior : RefProg → Query → TerminalOut → Prop)
    (RefDiverges : RefProg → Query → Prop) : Prop :=
  ∀ (p : Program) (q : Query),
    WellFormed p q →
    RefWellFormed (encodeProg p) q ∧
    (∀ (out : TerminalOut),
      Behavior p q out ↔ RefBehavior (encodeProg p) q out) ∧
    (Diverges p q ↔ RefDiverges (encodeProg p) q)

/-- Abstract interface of `Trusted.Correspondence.FaultEquivalenceClaim`,
definitionally equal (`rfl`) to `Trusted.Correspondence.FaultEquivalenceClaim`
when instantiated with `Trusted.Correspondence`. -/
def MirFaultCorrespondenceBridge
    {RefProg RefOutcome : Type}
    (encodeProg : Program → RefProg)
    (faultToRefOutcome : FaultKind → RefOutcome)
    (RefReachesOutcome : RefProg → Query → Nat → RefOutcome → Prop) : Prop :=
  ∀ (p : Program) (q : Query) (k : FaultKind),
    ReachesResult p q (.fault k) ↔
    ∃ maxSteps,
      RefReachesOutcome (encodeProg p) q maxSteps (faultToRefOutcome k)

/-- End-to-end transfer theorem across `CorrespondenceClaim` to the `lean-miri`
reference machine $M_{\text{ref}}$, transferring well-formedness, unique
terminal behavior, postcondition satisfaction, and non-divergence (`¬ Diverges`
and `¬ RefDiverges`), given an explicit `MirRunsTo` simulation proof `hSim`
(no automatic MIR-to-`PureLift` simulation theorem is claimed). -/
theorem mir_pure_lift_correspondence_transfer
    {RefProg : Type}
    (encodeProg : Program → RefProg)
    (RefWellFormed : RefProg → Query → Prop)
    (RefBehavior : RefProg → Query → TerminalOut → Prop)
    (RefDiverges : RefProg → Query → Prop)
    (hCorr : MirCorrespondenceBridge encodeProg RefWellFormed RefBehavior
      RefDiverges)
    (p : Program) (q : Query)
    (params : List (ParamInput Val))
    (plan : FlowPlan Val)
    (retExpr : RvalOp Val)
    (post : FuncOut Val → Prop)
    (hArgs : MirArgsMatch p q params)
    (hSpec : HoldsFnSpec (evalFnValue mirValAlg params plan retExpr) post)
    (hSim : ∀ out, evalFnValue mirValAlg params plan retExpr = .ok out →
      Exists fun fuel => MirRunsTo p q fuel out) :
    Exists fun out =>
      MirArgsMatch p q params ∧
      evalFnValue mirValAlg params plan retExpr = .ok out ∧
      out.mutFinals = [] ∧
      post out ∧
      WellFormed p q ∧
      Behavior p q (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ Diverges p q ∧
      SatisfiesPost p q
        (fun tOut => tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out) ∧
      RefWellFormed (encodeProg p) q ∧
      RefBehavior (encodeProg p) q (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ RefDiverges (encodeProg p) q ∧
      (∀ tOut, RefBehavior (encodeProg p) q tOut →
        tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out) := by
  have hBase :=
    mir_pure_lift_satisfiesPost p q params plan retExpr post hArgs hSpec hSim
  cases hBase with
  | intro out hOut =>
    have hWf : WellFormed p q := hOut.2.2.2.2.1
    have hBeh : Behavior p q (.returned ⟨out.ret, ⟨[]⟩⟩) := hOut.2.2.2.2.2.1
    have hNoDiv : ¬ Diverges p q := hOut.2.2.2.2.2.2.1
    have hSat := hOut.2.2.2.2.2.2.2
    have hRef := hCorr p q hWf
    have hRefWf : RefWellFormed (encodeProg p) q := hRef.1
    have hRefBeh :
        RefBehavior (encodeProg p) q (.returned ⟨out.ret, ⟨[]⟩⟩) :=
      (hRef.2.1 (.returned ⟨out.ret, ⟨[]⟩⟩)).mp hBeh
    have hNoRefDiv : ¬ RefDiverges (encodeProg p) q :=
      fun hRD => hNoDiv (hRef.2.2.mpr hRD)
    refine ⟨out, hOut.1, hOut.2.1, hOut.2.2.1, hOut.2.2.2.1, hWf, hBeh,
      hNoDiv, hSat, hRefWf, hRefBeh, hNoRefDiv, ?_⟩
    intro tOut hRB
    have hAB : Behavior p q tOut := (hRef.2.1 tOut).mpr hRB
    exact hSat.2 tOut hAB

/-! ## Computable MIR Type, Constant, and Operator Evaluation Helpers -/

/-- Universal list predicate via `List.foldr`. -/
def mirListAll {α : Type} (pred : α → Bool) (xs : List α) : Bool :=
  xs.foldr (fun x ih => pred x && ih) true

/-- Existential list predicate via `List.foldr`. -/
def mirListAny {α : Type} (pred : α → Bool) (xs : List α) : Bool :=
  xs.foldr (fun x ih => pred x || ih) false

/-- Computable structural equality on `IntWidth`. -/
def mirIntWidthBeq : IntWidth → IntWidth → Bool
  | .i8, .i8 => true
  | .i16, .i16 => true
  | .i32, .i32 => true
  | .i64, .i64 => true
  | .i128, .i128 => true
  | .isize, .isize => true
  | _, _ => false

/-- Computable structural equality on `Mutability`. -/
def mirMutabilityBeq : Mutability → Mutability → Bool
  | .shared, .shared => true
  | .mut, .mut => true
  | _, _ => false

/-- Computable elementwise equality on `List Nat` via `List.foldr`. -/
def mirNatListBeq (xs ys : List Nat) : Bool :=
  xs.foldr
    (fun x ih rs =>
      match rs with
      | [] => false
      | y :: rs' => Nat.beq x y && ih rs')
    (fun rs => rs.isEmpty)
    ys

/-- Computable non-membership test on `List Nat`. -/
def mirNatNotElem (x : Nat) (ys : List Nat) : Bool :=
  mirListAll (fun y => !Nat.beq x y) ys

/-- Computable pairwise-distinctness test on `List Nat` via `List.foldr`. -/
def mirNatListPairwiseNe (xs : List Nat) : Bool :=
  (xs.foldr
    (fun x (acc : List Nat × Bool) =>
      (x :: acc.1, mirNatNotElem x acc.1 && acc.2))
    ([], true)).2

/-- Computable structural equality on `EnumTagRepr`. -/
def mirEnumTagReprBeq : EnumTagRepr → EnumTagRepr → Bool
  | .zeroSized, .zeroSized => true
  | .scalar w₁ s₁, .scalar w₂ s₂ => mirIntWidthBeq w₁ w₂ && (s₁ == s₂)
  | _, _ => false

/-- Computable structural equality on `EnumTy`. -/
def mirEnumTyBeq (a b : EnumTy) : Bool :=
  Nat.beq a.id b.id &&
    mirIntWidthBeq a.discrWidth b.discrWidth &&
    (a.discrSigned == b.discrSigned) &&
    mirEnumTagReprBeq a.tagRepr b.tagRepr &&
    mirNatListBeq a.discriminants b.discriminants

/-- Computable structural equality on `MirTy` via `natFold` and `List.foldr`. -/
def mirTyBeqAt (d : Nat) (a b : MirTy) : Bool :=
  natFold
    (fun x y =>
      match x, y with
      | .bool, .bool => true
      | .int w₁ s₁, .int w₂ s₂ => mirIntWidthBeq w₁ w₂ && (s₁ == s₂)
      | .unit, .unit => true
      | .never, .never => true
      | .enum ety₁, .enum ety₂ => mirEnumTyBeq ety₁ ety₂
      | .unsupported, .unsupported => true
      | _, _ => false)
    (fun _ ih x y =>
      match x, y with
      | .bool, .bool => true
      | .int w₁ s₁, .int w₂ s₂ => mirIntWidthBeq w₁ w₂ && (s₁ == s₂)
      | .unit, .unit => true
      | .never, .never => true
      | .enum ety₁, .enum ety₂ => mirEnumTyBeq ety₁ ety₂
      | .tuple fs₁, .tuple fs₂ =>
        fs₁.foldr
          (fun t₁ ihFs rs =>
            match rs with
            | [] => false
            | t₂ :: rs' => ih t₁ t₂ && ihFs rs')
          (fun rs => rs.isEmpty)
          fs₂
      | .ref m₁ p₁, .ref m₂ p₂ => mirMutabilityBeq m₁ m₂ && ih p₁ p₂
      | .rawPtr m₁ p₁, .rawPtr m₂ p₂ => mirMutabilityBeq m₁ m₂ && ih p₁ p₂
      | .unsupported, .unsupported => true
      | _, _ => false)
    d a b

/-- Computable structural equality on `MirTy` up to nesting depth 8. -/
def mirTyBeq (a b : MirTy) : Bool :=
  mirTyBeqAt 8 a b

/-- Unsigned modulus $2^{\text{bitWidth}}$ for `IntWidth`. -/
def mirModulus (w : IntWidth) : Nat :=
  Nat.pow 2 (mirBitWidth w)

/-- Computable Euclidean integer modulo (`x % m` with `m > 0`). -/
def mirIntEmod : Int → Int → Int
  | .ofNat m, n => .ofNat (Nat.mod m (Int.natAbs n))
  | .negSucc m, n =>
    Int.subNatNat (Int.natAbs n) (Nat.succ (Nat.mod m (Int.natAbs n)))

/-- Computable truncated integer division towards zero. -/
def mirIntTdiv : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (Nat.div m n)
  | .ofNat m, .negSucc n => Int.neg (.ofNat (Nat.div m (Nat.succ n)))
  | .negSucc m, .ofNat n => Int.neg (.ofNat (Nat.div (Nat.succ m) n))
  | .negSucc m, .negSucc n => .ofNat (Nat.div (Nat.succ m) (Nat.succ n))

/-- Computable truncated integer remainder towards zero. -/
def mirIntTmod : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (Nat.mod m n)
  | .ofNat m, .negSucc n => .ofNat (Nat.mod m (Nat.succ n))
  | .negSucc m, .ofNat n => Int.neg (.ofNat (Nat.mod (Nat.succ m) n))
  | .negSucc m, .negSucc n =>
    Int.neg (.ofNat (Nat.mod (Nat.succ m) (Nat.succ n)))

/-- Computable arithmetic right shift on `Int`. -/
def mirIntShiftRight : Int → Nat → Int
  | .ofNat n, s => .ofNat (Nat.shiftRight n s)
  | .negSucc n, s => .negSucc (Nat.shiftRight n s)

/-- Computable left shift on `Int`. -/
def mirIntShiftLeft : Int → Nat → Int
  | .ofNat n, s => .ofNat (Nat.shiftLeft n s)
  | .negSucc n, s => .negSucc ((Nat.shiftLeft (n + 1) s) - 1)

/-- Computable bitwise complement (`!x = -x - 1`) on `Int`. -/
def mirIntNot : Int → Int
  | .ofNat n => .negSucc n
  | .negSucc n => .ofNat n

/-- Computable two's-complement signed interpretation of `BitVec n`. -/
def mirBvToInt {n : Nat} (x : BitVec n) : Int :=
  if 2 * x.toNat < Nat.pow 2 n then
    Int.ofNat x.toNat
  else
    Int.ofNat x.toNat - Int.ofNat (Nat.pow 2 n)

/-- Computable wrapping conversion from `Int` to `BitVec n`. -/
def mirBvOfInt (n : Nat) (i : Int) : BitVec n :=
  BitVec.ofNat n (mirIntEmod i (Int.ofNat (Nat.pow 2 n))).toNat

/-- Computable sign-extension of the low `mirBitWidth w` bits of `value`. -/
def mirSignExtendBits (w : IntWidth) (value : BitVec 128) : Int :=
  let b := mirBitWidth w - 1 - 0 + 1
  let low : BitVec b := BitVec.ofNat b (Nat.shiftRight value.toNat 0)
  mirBvToInt (mirBvOfInt 128 (mirBvToInt low))

/-- Computable bitwise AND on `BitVec 128`. -/
def mirBvAnd (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.land x.toNat y.toNat)

/-- Computable bitwise OR on `BitVec 128`. -/
def mirBvOr (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.lor x.toNat y.toNat)

/-- Computable bitwise XOR on `BitVec 128`. -/
def mirBvXor (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.xor x.toNat y.toNat)

/-- Computable minimum signed integer at width `w`. -/
def mirSignedMinInt : IntWidth → Int
  | .i8 => Neg.neg (HPow.hPow (2 : Int) 7)
  | .i16 => Neg.neg (HPow.hPow (2 : Int) 15)
  | .i32 => Neg.neg (HPow.hPow (2 : Int) 31)
  | .i64 | .isize => Neg.neg (HPow.hPow (2 : Int) 63)
  | .i128 => Neg.neg (HPow.hPow (2 : Int) 127)

/-- Computable tag-to-discriminant extension/truncation matching
`Trusted.MirSemantics.tagBitsToDiscrBits`. -/
def mirTagBitsToDiscrBits (tagW : IntWidth) (tagS : Bool) (discrW : IntWidth)
    (tagBits : BitVec 128) : BitVec 128 :=
  let extended :=
    if tagS then
      mirBvOfInt 128 (mirSignExtendBits tagW tagBits)
    else
      mirTruncateBits tagW tagBits
  mirTruncateBits discrW extended

/-- Computable static admission check for fieldless `EnumTy` descriptors,
matching `Trusted.MirSemantics.enumAdmitted`. -/
def mirEnumAdmitted (ety : EnumTy) : Bool :=
  !ety.discriminants.isEmpty &&
    Nat.blt ety.discriminants.length (Nat.pow 2 32) &&
    mirListAll (fun d => Nat.blt d (mirModulus ety.discrWidth))
      ety.discriminants &&
    mirNatListPairwiseNe ety.discriminants &&
    match ety.tagRepr with
    | .zeroSized => Nat.beq ety.discriminants.length 1
    | .scalar tagW tagS =>
      mirListAll (fun d =>
        let dBits := BitVec.ofNat 128 d
        mirTagBitsToDiscrBits tagW tagS ety.discrWidth
          (mirTruncateBits tagW dBits) == dBits)
        ety.discriminants

/-- Computable check for admitted 0-byte ZST 1-variant fieldless enums. -/
def mirIsZstEnumTy (ety : EnumTy) : Bool :=
  match ety.tagRepr with
  | .zeroSized => mirEnumAdmitted ety
  | .scalar _ _ => false

/-- Computable linear search from `idx` for the variant index matching
`discrBits`. -/
def mirFindDiscrVariantAux (discrBits : BitVec 128) (ds : List Nat)
    (idx : Nat) : Option Nat :=
  ds.foldr
    (fun d ih cur =>
      if BitVec.ofNat 128 d == discrBits then
        some cur
      else
        ih (cur + 1))
    (fun _ => none)
    idx

/-- Computable linear search for the variant index matching `discrBits`. -/
def mirFindDiscrVariant? (discrBits : BitVec 128) (ds : List Nat) :
    Option Nat :=
  mirFindDiscrVariantAux discrBits ds 0

/-- Computable width-fit check on `ScalarVal`. -/
def mirScalarWf (sv : ScalarVal) : Bool :=
  mirTruncateBits sv.width sv.bits == sv.bits

/-- Computable intrinsic runtime type check matching
`Trusted.MirSemantics.Val.ty?`. -/
def mirValTy? : Val → Option MirTy
  | .scalar sv =>
    if mirScalarWf sv then some (.int sv.width sv.signed) else none
  | .bool _ => some .bool
  | .unit => some .unit
  | .enumVal ety v =>
    if mirEnumAdmitted ety && Nat.blt v ety.discriminants.length then
      some (.enum ety)
    else
      none
  | _ => none

/-- Computable value-type check matching `Trusted.MirSemantics.checkVal`. -/
def mirCheckVal (v : Val) (ty : MirTy) : Bool :=
  match mirValTy? v with
  | some vTy => mirTyBeq vTy ty
  | none => false

/-- Computable local-type support check matching
`Trusted.MirSemantics.isSupportedScalarOrUnitTy`. -/
def mirIsSupportedScalarOrUnitTy : MirTy → Bool
  | .bool | .int _ _ | .unit | .never => true
  | .enum ety => mirEnumAdmitted ety
  | _ => false

/-- Computable primitive-readable type check mirroring
`Trusted.MirSemantics.isPrimitiveReadableTy` (no agreement theorem). -/
def mirIsPrimitiveReadableTy : MirTy → Bool
  | .bool | .int _ _ => true
  | _ => false

/-- Computable initial live-uninitialized slot state matching
`Trusted.MirSemantics.liveUninitSlot`. -/
def mirLiveUninitSlot : MirTy → LocalSlot
  | .unit => .live (some .unit)
  | .enum ety =>
    if mirIsZstEnumTy ety then .live (some (.enumVal ety 0)) else .live none
  | _ => .live none

/-- Computable storage-marker check for a single `StatementKind`. -/
def mirStmtHasStorageMarker (localId : LocalId) : StatementKind → Bool
  | .storageLive id | .storageDead id => Nat.beq id localId
  | _ => false

/-- Computable check for whether `body` contains a `StorageLive` or
`StorageDead` annotation on `localId`. -/
def mirHasStorageAnnotation (body : Body) (localId : LocalId) : Bool :=
  mirListAny
    (fun bb => mirListAny (mirStmtHasStorageMarker localId) bb.statements)
    body.basicBlocks

/-- Computable bounds check on all `StorageLive` and `StorageDead` annotations
in `body`. -/
def mirStorageAnnotationsInBounds (body : Body) : Bool :=
  let numLocals := body.locals.length
  mirListAll
    (fun bb =>
      mirListAll
        (fun stmt =>
          match stmt with
          | .storageLive id | .storageDead id => Nat.blt id numLocals
          | _ => true)
        bb.statements)
    body.basicBlocks

/-- Computable discriminant destination type check matching
`Trusted.MirSemantics.discriminantTypesValid`. -/
def mirDiscriminantTypesValid (body : Body) : Bool :=
  mirListAll
    (fun bb =>
      mirListAll
        (fun stmt =>
          match stmt with
          | .assign dst rv =>
            match rv with
            | .discriminant src =>
              if dst.projection.isEmpty && src.projection.isEmpty then
                match mirListGet? body.locals src.localId with
                | some srcTy =>
                  match srcTy with
                  | .enum ety =>
                    match mirListGet? body.locals dst.localId with
                    | some dstTy =>
                      if mirEnumAdmitted ety then
                        mirTyBeq dstTy (.int ety.discrWidth ety.discrSigned)
                      else
                        true
                    | none => true
                  | _ => true
                | none => true
              else
                true
            | _ => true
          | _ => true)
        bb.statements)
    body.basicBlocks

/-- Computable static body admission check matching the 2-argument
`Trusted.MirSemantics.BodyStaticAdmitted`. -/
def mirBodyStaticAdmitted (p : Program) (body : Body) : Bool :=
  Nat.beq p.pointerWidthBits 64 &&
    Nat.beq p.mirProfileVersion 1 &&
    !body.identity.toByteArray.data.toList.isEmpty &&
    !body.basicBlocks.isEmpty &&
    Nat.blt body.argumentCount body.locals.length &&
    mirStorageAnnotationsInBounds body &&
    mirDiscriminantTypesValid body &&
    mirListAll mirIsSupportedScalarOrUnitTy body.locals

/-- Computable constant-literal evaluator matching
`Trusted.MirSemantics.evalConstLit` (preserving the exact distinction between
static `.error .unsupported` ill-typed constants and runtime `.error .undefined`
UB bit patterns). -/
def mirEvalConstLit : MirTy → ConstLit → Except FaultKind Val
  | .int w s, .scalar bits =>
    if mirTruncateBits w bits != bits then
      .error .unsupported
    else
      .ok (.scalar ⟨w, s, mirTruncateBits w bits⟩)
  | .bool, .scalar bits =>
    if mirTruncateBits .i8 bits != bits then
      .error .unsupported
    else
      let v := UInt8.ofNat (mirTruncateBits .i8 bits).toNat
      if v == 0 then
        .ok (.bool false)
      else if v == 1 then
        .ok (.bool true)
      else
        .error .undefined
  | .unit, .zeroSized => .ok .unit
  | .enum ety, .zeroSized =>
    if mirIsZstEnumTy ety then .ok (.enumVal ety 0) else .error .unsupported
  | .enum ety, .scalar bits =>
    match ety.tagRepr with
    | .zeroSized => .error .unsupported
    | .scalar tagW tagS =>
      if !mirEnumAdmitted ety || mirTruncateBits tagW bits != bits then
        .error .unsupported
      else
        let discrBits := mirTagBitsToDiscrBits tagW tagS ety.discrWidth bits
        match mirFindDiscrVariant? discrBits ety.discriminants with
        | some v => .ok (.enumVal ety v)
        | none => .error .undefined
  | _, _ => .error .unsupported

/-- Computable fieldless-enum discriminant reader mirroring the `.discriminant`
arm of `Trusted.MirSemantics.evalRvalue` (no agreement theorem). -/
def mirEvalDiscrVal (ety : EnumTy) : Val → Option Val
  | .enumVal ety' v =>
    if mirEnumTyBeq ety ety' && Nat.blt v ety.discriminants.length then
      match mirListGet? ety.discriminants v with
      | some disc =>
        some (.scalar ⟨ety.discrWidth, ety.discrSigned,
          mirTruncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩)
      | none => none
    else
      none
  | _ => none

/-- Computable shift-operator classification matching `BinOp.isShift`. -/
def mirBinOpIsShift : BinOp → Bool
  | .shl | .shlUnchecked | .shr | .shrUnchecked => true
  | _ => false

/-- Computable unchecked-operator classification matching
`BinOp.isUnchecked`. -/
def mirBinOpIsUnchecked : BinOp → Bool
  | .addUnchecked | .subUnchecked | .mulUnchecked
  | .shlUnchecked | .shrUnchecked => true
  | _ => false

/-- Computable scalar integer decoder matching
`Trusted.MirSemantics.decodeScalar`. -/
def mirDecodeScalar (sv : ScalarVal) : Int :=
  let trunc := mirTruncateBits sv.width sv.bits
  if sv.signed then
    mirSignExtendBits sv.width trunc
  else
    Int.ofNat trunc.toNat

/-- Computable integer truncation with lossiness flag matching
`Trusted.MirSemantics.truncateScalar`. -/
def mirTruncateScalar (w : IntWidth) (s : Bool) (value : Int) :
    Option (ScalarVal × Bool) :=
  if s then
    let wrapped := mirBvToInt (mirBvOfInt 128 value)
    if decide (wrapped < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (wrapped ≥ HPow.hPow (2 : Int) 127) then
      none
    else
      let raw := mirBvOfInt 128 wrapped
      let trunc := mirTruncateBits w raw
      let decoded := mirSignExtendBits w trunc
      some (⟨w, s, trunc⟩, decoded != wrapped)
  else
    let raw := mirBvOfInt 128 value
    let trunc := mirTruncateBits w raw
    some (⟨w, s, trunc⟩, trunc != raw)

/-- Computable shift evaluation matching `Trusted.MirSemantics.evalShiftOp`. -/
def mirEvalShiftOp (op : BinOp) (w : IntWidth) (s : Bool) (l r : Int) :
    Option Val :=
  let amount := mirIntEmod r (Int.ofNat (mirBitWidth w))
  let overflow := amount != r
  let result :=
    match op with
    | .shl | .shlUnchecked => mirIntShiftLeft l amount.toNat
    | _ => mirIntShiftRight l amount.toNat
  match mirTruncateScalar w s result with
  | none => none
  | some (res, _) =>
    if overflow && mirBinOpIsUnchecked op then
      none
    else
      some (.scalar res)

/-- Computable integer arithmetic evaluation matching
`Trusted.MirSemantics.evalArithOp`. -/
def mirEvalArithOp (op : BinOp) (w : IntWidth) (s : Bool) (l r : Int) :
    Option Val :=
  let isDivOrRem := match op with | .div | .rem => true | _ => false
  if isDivOrRem && r == 0 then
    none
  else if s && isDivOrRem && (l == mirSignedMinInt w && r == Neg.neg 1) then
    none
  else
    let res? : Option Int :=
      match op with
      | .add | .addUnchecked => some (l + r)
      | .sub | .subUnchecked => some (l - r)
      | .mul | .mulUnchecked => some (l * r)
      | .div => some (mirIntTdiv l r)
      | .rem => some (mirIntTmod l r)
      | _ => none
    match res? with
    | none => none
    | some result =>
      let hostOverflow : Bool :=
        if s then
          decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide (result ≥ HPow.hPow (2 : Int) 127)
        else
          decide (result < 0) || decide (result ≥ HPow.hPow (2 : Int) 128)
      match mirTruncateScalar w s result with
      | none => none
      | some (val, lossy) =>
        if (hostOverflow || lossy) && mirBinOpIsUnchecked op then
          none
        else
          some (.scalar val)

/-- Computable binary operator evaluator matching
`Trusted.MirSemantics.evalBinOp` for `RvalOp.binary`. -/
def mirEvalBinOpVal (op : BinOp) (lhs rhs : Val) : Option Val :=
  match lhs, rhs with
  | .scalar l, .scalar r =>
    let lInt := mirDecodeScalar l
    let rInt := mirDecodeScalar r
    let w := l.width
    let s := l.signed
    if mirBinOpIsShift op then
      mirEvalShiftOp op w s lInt rInt
    else if !(mirIntWidthBeq l.width r.width && (l.signed == r.signed)) then
      none
    else
      match op with
      | .eq => some (.bool (lInt == rInt))
      | .ne => some (.bool (lInt != rInt))
      | .lt => some (.bool (decide (lInt < rInt)))
      | .le => some (.bool (decide (lInt ≤ rInt)))
      | .gt => some (.bool (decide (lInt > rInt)))
      | .ge => some (.bool (decide (lInt ≥ rInt)))
      | .bitAnd =>
        let lb := mirTruncateBits w l.bits
        let rb := mirTruncateBits r.width r.bits
        some (.scalar ⟨w, s, mirTruncateBits w (mirBvAnd lb rb)⟩)
      | .bitOr =>
        let lb := mirTruncateBits w l.bits
        let rb := mirTruncateBits r.width r.bits
        some (.scalar ⟨w, s, mirTruncateBits w (mirBvOr lb rb)⟩)
      | .bitXor =>
        let lb := mirTruncateBits w l.bits
        let rb := mirTruncateBits r.width r.bits
        some (.scalar ⟨w, s, mirTruncateBits w (mirBvXor lb rb)⟩)
      | .add | .sub | .mul | .div | .rem
      | .addUnchecked | .subUnchecked | .mulUnchecked =>
        mirEvalArithOp op w s lInt rInt
      | _ => none
  | .bool l, .bool r =>
    match op with
    | .eq => some (.bool (l == r))
    | .ne => some (.bool (l != r))
    | .lt => some (.bool (!l && r))
    | .le => some (.bool (!l || r))
    | .gt => some (.bool (l && !r))
    | .ge => some (.bool (l || !r))
    | .bitAnd => some (.bool (l && r))
    | .bitOr => some (.bool (l || r))
    | .bitXor => some (.bool (bne l r))
    | _ => none
  | _, _ => none

/-- Computable unary operator evaluator matching
`Trusted.MirSemantics.evalUnOp` for `RvalOp.unary`. -/
def mirEvalUnOpVal (op : UnOp) (v : Val) : Option Val :=
  match op, v with
  | .not, .bool b => some (.bool (!b))
  | .not, .scalar sv =>
    let integer := mirDecodeScalar sv
    match mirTruncateScalar sv.width sv.signed (mirIntNot integer) with
    | some (res, _) => some (.scalar res)
    | none => none
  | .neg, .scalar sv =>
    let integer := mirDecodeScalar sv
    if sv.signed then
      match mirTruncateScalar sv.width sv.signed (Neg.neg integer) with
      | some (res, _) => some (.scalar res)
      | none => none
    else
      none
  | _, _ => none

/-! ### Kernel Agreement Certifying Computable `mir*` Helpers Against
`Trusted.MirSemantics` -/

theorem mirListAll_eq {α : Type} (p q : α → Bool)
    (hpq : ∀ x, p x = q x) :
    ∀ (xs : List α), mirListAll p xs = xs.all q
  | [] => rfl
  | x :: xs => by
    change (p x && mirListAll p xs) = (q x && xs.all q)
    rw [hpq x, mirListAll_eq p q hpq xs]

theorem mirIntWidthBeq_eq (w₁ w₂ : IntWidth) :
    mirIntWidthBeq w₁ w₂ = IntWidth.beq w₁ w₂ := by
  cases w₁ <;> cases w₂ <;> rfl

theorem mirNatListBeq_eq :
    ∀ (xs ys : List Nat), mirNatListBeq xs ys = natListBeq xs ys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    change (Nat.beq x y && mirNatListBeq xs ys) =
      (Nat.beq x y && natListBeq xs ys)
    rw [mirNatListBeq_eq xs ys]

theorem mirEnumTagReprBeq_eq (r₁ r₂ : EnumTagRepr) :
    mirEnumTagReprBeq r₁ r₂ = EnumTagRepr.beq r₁ r₂ := by
  cases r₁ with
  | zeroSized => cases r₂ <;> rfl
  | scalar w₁ s₁ =>
    cases r₂ with
    | zeroSized => rfl
    | scalar w₂ s₂ =>
      dsimp only [mirEnumTagReprBeq, EnumTagRepr.beq]
      rw [mirIntWidthBeq_eq w₁ w₂]

theorem mirEnumTyBeq_eq (a b : EnumTy) :
    mirEnumTyBeq a b = EnumTy.beq a b := by
  unfold mirEnumTyBeq EnumTy.beq
  rw [mirIntWidthBeq_eq, mirEnumTagReprBeq_eq, mirNatListBeq_eq]

theorem mirBitWidth_eq (w : IntWidth) : mirBitWidth w = w.bitWidth := by
  cases w <;> rfl

theorem mirModulus_eq (w : IntWidth) :
    mirModulus w = Nat.pow 2 w.bitWidth := by
  cases w <;> rfl

theorem mirIntEmod_eq (a b : Int) : mirIntEmod a b = intEmod a b := by
  cases a <;> rfl

theorem mirIntTdiv_eq (a b : Int) : mirIntTdiv a b = intTdiv a b := by
  cases a <;> cases b <;> rfl

theorem mirIntTmod_eq (a b : Int) : mirIntTmod a b = intTmod a b := by
  cases a <;> cases b <;> rfl

theorem mirIntShiftRight_eq (a : Int) (s : Nat) :
    mirIntShiftRight a s = intShiftRight a s := by
  cases a <;> rfl

theorem mirIntShiftLeft_eq (a : Int) (s : Nat) :
    mirIntShiftLeft a s = intShiftLeft a s := by
  cases a <;> rfl

theorem mirIntNot_eq (a : Int) : mirIntNot a = intNot a := by
  cases a <;> rfl

theorem mirBvToInt_eq {n : Nat} (x : BitVec n) :
    mirBvToInt x = bvToInt x := rfl

theorem mirBvOfInt_eq (n : Nat) (i : Int) :
    mirBvOfInt n i = bvOfInt n i := by
  unfold mirBvOfInt bvOfInt
  rw [mirIntEmod_eq]

theorem mirSignExtendBits_eq (w : IntWidth) (value : BitVec 128) :
    mirSignExtendBits w value = signExtendBits w value := by
  unfold mirSignExtendBits signExtendBits bvSignExtend bvExtractLsb
    bvExtractLsb'
  simp only [mirBvOfInt_eq, mirBvToInt_eq]
  cases w <;> rfl

theorem mirTagBitsToDiscrBits_eq (tagW : IntWidth) (tagS : Bool)
    (discrW : IntWidth) (tagBits : BitVec 128) :
    mirTagBitsToDiscrBits tagW tagS discrW tagBits =
      tagBitsToDiscrBits tagW tagS discrW tagBits := by
  unfold mirTagBitsToDiscrBits tagBitsToDiscrBits
  simp only [mirTruncateBits_eq_truncateBits, mirSignExtendBits_eq,
    mirBvOfInt_eq]

theorem mirNatNotElem_eq (x : Nat) :
    ∀ (ys : List Nat), mirNatNotElem x ys = natNotElem x ys
  | [] => rfl
  | y :: ys => by
    change (!Nat.beq x y && mirNatNotElem x ys) =
      (!Nat.beq x y && natNotElem x ys)
    rw [mirNatNotElem_eq x ys]

theorem mirNatListPairwiseNe_foldr :
    ∀ (xs : List Nat),
      xs.foldr
        (fun x (acc : List Nat × Bool) =>
          (x :: acc.1, mirNatNotElem x acc.1 && acc.2))
        ([], true) =
      (xs, natListPairwiseNe xs)
  | [] => rfl
  | x :: xs => by
    let pair := xs.foldr
      (fun y (acc : List Nat × Bool) =>
        (y :: acc.1, mirNatNotElem y acc.1 && acc.2))
      ([], true)
    change (x :: pair.1, mirNatNotElem x pair.1 && pair.2) =
      (x :: xs, natNotElem x xs && natListPairwiseNe xs)
    have ih := mirNatListPairwiseNe_foldr xs
    change pair = (xs, natListPairwiseNe xs) at ih
    rw [ih]
    dsimp only
    rw [mirNatNotElem_eq x xs]

theorem mirNatListPairwiseNe_eq (xs : List Nat) :
    mirNatListPairwiseNe xs = natListPairwiseNe xs := by
  unfold mirNatListPairwiseNe
  rw [mirNatListPairwiseNe_foldr xs]

theorem mirEnumAdmitted_eq (ety : EnumTy) :
    mirEnumAdmitted ety = enumAdmitted ety := by
  unfold mirEnumAdmitted enumAdmitted
  rw [mirListAll_eq _ _ (fun d => by rw [mirModulus_eq]) ety.discriminants,
      mirNatListPairwiseNe_eq ety.discriminants]
  cases ety.tagRepr with
  | zeroSized => rfl
  | scalar tagW tagS =>
    dsimp only
    rw [mirListAll_eq _ _
      (fun d => by
        rw [mirTagBitsToDiscrBits_eq, mirTruncateBits_eq_truncateBits])
      ety.discriminants]

theorem mirIsZstEnumTy_eq (ety : EnumTy) :
    mirIsZstEnumTy ety = isZstEnumTy ety := by
  unfold mirIsZstEnumTy isZstEnumTy
  cases ety.tagRepr with
  | zeroSized => exact mirEnumAdmitted_eq ety
  | scalar _ _ => rfl

theorem mirScalarWf_eq (sv : ScalarVal) :
    mirScalarWf sv = sv.wf := by
  unfold mirScalarWf ScalarVal.wf
  rw [mirTruncateBits_eq_truncateBits]

theorem mirValTy?_eq (v : Val) : mirValTy? v = v.ty? := by
  cases v with
  | scalar sv =>
    dsimp only [mirValTy?, Val.ty?]
    rw [mirScalarWf_eq sv]
  | enumVal ety idx =>
    dsimp only [mirValTy?, Val.ty?]
    rw [mirEnumAdmitted_eq ety]
  | ptr _ | bool _ | unit | tuple _ | bytes _ => rfl

/-- Exact unconditional agreement between `mirCheckVal` and
`Trusted.MirSemantics.checkVal` across all runtime `Val`s and all `MirTy`s. -/
theorem mirCheckVal_eq (v : Val) (ty : MirTy) :
    mirCheckVal v ty = checkVal v ty := by
  unfold mirCheckVal checkVal
  rw [mirValTy?_eq v]
  cases v with
  | scalar sv =>
    dsimp only [Val.ty?]
    cases sv.wf with
    | false => rfl
    | true =>
      cases ty with
      | int w₂ s₂ =>
        change (mirIntWidthBeq sv.width w₂ && (sv.signed == s₂)) =
          (IntWidth.beq sv.width w₂ && (sv.signed == s₂))
        rw [mirIntWidthBeq_eq]
      | bool | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _
      | unsupported => rfl
  | bool _ =>
    dsimp only [Val.ty?]
    cases ty <;> rfl
  | unit =>
    dsimp only [Val.ty?]
    cases ty <;> rfl
  | enumVal ety idx =>
    dsimp only [Val.ty?]
    cases (enumAdmitted ety && Nat.blt idx ety.discriminants.length) with
    | false => rfl
    | true =>
      cases ty with
      | enum ety₂ => exact mirEnumTyBeq_eq ety ety₂
      | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _
      | unsupported => rfl
  | ptr _ | tuple _ | bytes _ => rfl

theorem mirIsSupportedScalarOrUnitTy_eq (ty : MirTy) :
    mirIsSupportedScalarOrUnitTy ty = isSupportedScalarOrUnitTy ty := by
  cases ty with
  | enum ety => exact mirEnumAdmitted_eq ety
  | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _
  | unsupported => rfl

theorem mirLiveUninitSlot_eq (ty : MirTy) :
    mirLiveUninitSlot ty = liveUninitSlot ty := by
  cases ty with
  | enum ety =>
    dsimp only [mirLiveUninitSlot, liveUninitSlot]
    rw [mirIsZstEnumTy_eq ety]
  | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _
  | unsupported => rfl

theorem mirStorageAnnotationsInBounds_eq (body : Body) :
    mirStorageAnnotationsInBounds body = storageAnnotationsInBounds body := by
  unfold mirStorageAnnotationsInBounds storageAnnotationsInBounds
  exact mirListAll_eq _ _
    (fun bb => mirListAll_eq _ _ (fun _ => rfl) bb.statements)
    body.basicBlocks

theorem mirDiscriminantTypesValid_eq (body : Body) :
    mirDiscriminantTypesValid body = discriminantTypesValid body := by
  unfold mirDiscriminantTypesValid discriminantTypesValid
  refine mirListAll_eq _ _ (fun bb =>
    mirListAll_eq _ _ (fun stmt => ?_) bb.statements) body.basicBlocks
  cases stmt with
  | assign dst rv =>
    cases rv with
    | discriminant src =>
      change
        (if (dst.projection.isEmpty && src.projection.isEmpty) = true then
          match mirListGet? body.locals src.localId with
          | some srcTy =>
            match srcTy with
            | .enum ety =>
              match mirListGet? body.locals dst.localId with
              | some dstTy =>
                if mirEnumAdmitted ety then
                  mirTyBeq dstTy (.int ety.discrWidth ety.discrSigned)
                else true
              | none => true
            | _ => true
          | none => true
        else true) =
        (if (dst.projection.isEmpty && src.projection.isEmpty) = true then
          match Trusted.MirSemantics.getElem? body.locals src.localId with
          | some srcTy =>
            match srcTy with
            | .enum ety =>
              match Trusted.MirSemantics.getElem? body.locals dst.localId with
              | some dstTy =>
                if enumAdmitted ety then
                  MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
                else true
              | none => true
            | _ => true
          | none => true
        else true)
      cases (dst.projection.isEmpty && src.projection.isEmpty) with
      | false => rfl
      | true =>
        rw [mirListGet?_eq_getElem?, mirListGet?_eq_getElem?]
        cases Trusted.MirSemantics.getElem? body.locals src.localId with
        | none => rfl
        | some srcTy =>
          cases srcTy with
          | enum ety =>
            cases Trusted.MirSemantics.getElem? body.locals dst.localId with
            | none => rfl
            | some dstTy =>
              change
                (if mirEnumAdmitted ety = true then
                  mirTyBeq dstTy (.int ety.discrWidth ety.discrSigned)
                else true) =
                (if enumAdmitted ety = true then
                  MirTy.beq dstTy (.int ety.discrWidth ety.discrSigned)
                else true)
              rw [mirEnumAdmitted_eq ety]
              cases enumAdmitted ety with
              | false => rfl
              | true =>
                cases dstTy with
                | int w s =>
                  change (mirIntWidthBeq w ety.discrWidth &&
                    (s == ety.discrSigned)) =
                    (IntWidth.beq w ety.discrWidth &&
                      (s == ety.discrSigned))
                  rw [mirIntWidthBeq_eq]
                | bool | unit | never | enum _ | tuple _ | ref _ _
                | rawPtr _ _ | unsupported => rfl
          | bool | int _ _ | unit | never | tuple _ | ref _ _ | rawPtr _ _
          | unsupported => rfl
    | use _ | binaryOp _ _ _ | unaryOp _ _ | ref _ _ | addressOf _ _
    | aggregateTuple _ | unsupported => rfl
  | storageLive _ | storageDead _ | nop | unsupported => rfl

/-- Exact kernel agreement between computable `mirBodyStaticAdmitted` and
`Trusted.MirSemantics.BodyStaticAdmitted`. -/
theorem mirBodyStaticAdmitted_eq (p : Program) (body : Body) :
    mirBodyStaticAdmitted p body = BodyStaticAdmitted p body := by
  unfold mirBodyStaticAdmitted BodyStaticAdmitted
  have hStr :
      body.identity.toByteArray.data.toList.isEmpty =
      stringBeq body.identity "" := by
    unfold stringBeq
    have hEmpty : "".toByteArray.data.toList = [] := rfl
    rw [hEmpty]
    cases body.identity.toByteArray.data.toList <;> rfl
  rw [hStr, mirStorageAnnotationsInBounds_eq body,
      mirDiscriminantTypesValid_eq body,
      mirListAll_eq _ _ mirIsSupportedScalarOrUnitTy_eq body.locals]

theorem mirFindDiscrVariantAux_eq (discrBits : BitVec 128) :
    ∀ (ds : List Nat) (idx : Nat),
      mirFindDiscrVariantAux discrBits ds idx =
      findDiscrVariantAux idx discrBits ds
  | [], _ => rfl
  | d :: ds, idx => by
    change (if BitVec.ofNat 128 d == discrBits then some idx
      else mirFindDiscrVariantAux discrBits ds (idx + 1)) =
      (if BitVec.ofNat 128 d == discrBits then some idx
      else findDiscrVariantAux (idx + 1) discrBits ds)
    rw [mirFindDiscrVariantAux_eq discrBits ds (idx + 1)]

theorem mirFindDiscrVariant?_eq (discrBits : BitVec 128) (ds : List Nat) :
    mirFindDiscrVariant? discrBits ds = findDiscrVariant? discrBits ds :=
  mirFindDiscrVariantAux_eq discrBits ds 0

/-- Exact kernel agreement between computable `mirEvalConstLit` and
`Trusted.MirSemantics.evalConstLit`. -/
theorem mirEvalConstLit_eq (ty : MirTy) (lit : ConstLit) :
    mirEvalConstLit ty lit = evalConstLit ty lit := by
  cases ty with
  | int w s =>
    cases lit with
    | scalar bits =>
      dsimp only [mirEvalConstLit, evalConstLit]
      rw [mirTruncateBits_eq_truncateBits]
    | zeroSized => rfl
  | bool =>
    cases lit with
    | scalar bits =>
      dsimp only [mirEvalConstLit, evalConstLit]
      rw [mirTruncateBits_eq_truncateBits]
    | zeroSized => rfl
  | unit =>
    cases lit <;> rfl
  | enum ety =>
    cases lit with
    | zeroSized =>
      dsimp only [mirEvalConstLit, evalConstLit]
      rw [mirIsZstEnumTy_eq ety]
    | scalar bits =>
      dsimp only [mirEvalConstLit, evalConstLit]
      cases ety.tagRepr with
      | zeroSized => rfl
      | scalar tagW tagS =>
        dsimp only
        rw [mirEnumAdmitted_eq ety, mirTruncateBits_eq_truncateBits,
            mirTagBitsToDiscrBits_eq, mirFindDiscrVariant?_eq]
        rfl
  | never | tuple _ | ref _ _ | rawPtr _ _ | unsupported =>
    cases lit <;> rfl

theorem mirDecodeScalar_eq (sv : ScalarVal) :
    mirDecodeScalar sv = decodeScalar sv := by
  unfold mirDecodeScalar decodeScalar
  simp only [mirTruncateBits_eq_truncateBits, mirSignExtendBits_eq]

theorem mirSignedMinInt_eq (w : IntWidth) :
    mirSignedMinInt w = signedMinInt w := by
  cases w <;> rfl

theorem mirTruncateScalar_eq (w : IntWidth) (s : Bool) (value : Int) :
    mirTruncateScalar w s value =
      match truncateScalar w s value with
      | .ok pair => some pair
      | .error _ => none := by
  unfold mirTruncateScalar truncateScalar
  simp only [mirBvOfInt_eq, mirBvToInt_eq, mirTruncateBits_eq_truncateBits,
    mirSignExtendBits_eq]
  cases s with
  | false => rfl
  | true =>
    cases (decide (bvToInt (bvOfInt 128 value) <
        Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (bvToInt (bvOfInt 128 value) ≥
        HPow.hPow (2 : Int) 127)) <;> rfl

/-- Success/failure agreement between computable `mirEvalUnOpVal` and
`Trusted.MirSemantics.evalUnOp` (collapsing error fault kinds to `none`). -/
theorem mirEvalUnOpVal_eq (op : UnOp) (v : Val) :
    mirEvalUnOpVal op v =
      match evalUnOp op v with
      | .ok res => some res
      | .error _ => none := by
  cases op with
  | not =>
    cases v with
    | bool _ => rfl
    | scalar sv =>
      dsimp only [mirEvalUnOpVal, evalUnOp]
      rw [mirDecodeScalar_eq sv, mirIntNot_eq (decodeScalar sv),
          mirTruncateScalar_eq sv.width sv.signed (intNot (decodeScalar sv))]
      cases truncateScalar sv.width sv.signed (intNot (decodeScalar sv)) with
      | error _ => rfl
      | ok pair => cases pair; rfl
    | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
  | neg =>
    cases v with
    | scalar sv =>
      dsimp only [mirEvalUnOpVal, evalUnOp]
      rw [mirDecodeScalar_eq sv]
      cases sv.signed with
      | false => rfl
      | true =>
        rw [mirTruncateScalar_eq sv.width true (Neg.neg (decodeScalar sv))]
        cases truncateScalar sv.width true (Neg.neg (decodeScalar sv)) with
        | error _ => rfl
        | ok pair => cases pair; rfl
    | bool _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
  | ptrMetadata =>
    cases v <;> rfl

theorem mirEvalShiftOp_eq (op : BinOp) (w : IntWidth) (s : Bool) (l r : Int) :
    mirEvalShiftOp op w s l r =
      match evalShiftOp op w s l r with
      | .ok res => some res
      | .error _ => none := by
  have hUnch : mirBinOpIsUnchecked op = op.isUnchecked := by
    cases op <;> rfl
  unfold mirEvalShiftOp evalShiftOp
  rw [mirBitWidth_eq w, mirIntEmod_eq, hUnch]
  cases op with
  | shl | shlUnchecked =>
    dsimp only
    rw [mirIntShiftLeft_eq, mirTruncateScalar_eq]
    cases truncateScalar w s
        (intShiftLeft l (intEmod r (Int.ofNat w.bitWidth)).toNat) with
    | error _ => rfl
    | ok pair =>
      cases pair
      dsimp only
      cases (intEmod r (Int.ofNat w.bitWidth) != r && _) <;> rfl
  | add | addUnchecked | addWithOverflow | sub | subUnchecked
  | subWithOverflow | mul | mulUnchecked | mulWithOverflow | div | rem
  | bitXor | bitAnd | bitOr | shr | shrUnchecked | eq | lt | le | ne | ge | gt
  | offset =>
    dsimp only
    rw [mirIntShiftRight_eq, mirTruncateScalar_eq]
    cases truncateScalar w s
        (intShiftRight l (intEmod r (Int.ofNat w.bitWidth)).toNat) with
    | error _ => rfl
    | ok pair =>
      cases pair
      dsimp only
      cases (intEmod r (Int.ofNat w.bitWidth) != r && _) <;> rfl

theorem mirEvalArithOp_eq (op : BinOp) (w : IntWidth) (s : Bool) (l r : Int) :
    mirEvalArithOp op w s l r =
      match evalArithOp op w s l r with
      | .ok res => some res
      | .error _ => none := by
  have hUnch : mirBinOpIsUnchecked op = op.isUnchecked := by
    cases op <;> rfl
  unfold mirEvalArithOp evalArithOp
  rw [mirSignedMinInt_eq w, hUnch]
  cases op with
  | add | sub | mul | addUnchecked | subUnchecked | mulUnchecked =>
    dsimp only
    cases (s && false && (l == signedMinInt w && r == Neg.neg 1)) with
    | true => rfl
    | false =>
      rw [mirTruncateScalar_eq]
      cases truncateScalar w s _ with
      | error _ => rfl
      | ok pair =>
        cases pair
        dsimp only
        cases ((_ || _) && _) <;> rfl
  | div =>
    dsimp only
    cases (true && r == 0) with
    | true => rfl
    | false =>
      cases (s && true && (l == signedMinInt w && r == Neg.neg 1)) with
      | true => rfl
      | false =>
        rw [mirIntTdiv_eq, mirTruncateScalar_eq]
        cases truncateScalar w s (intTdiv l r) with
        | error _ => rfl
        | ok pair =>
          cases pair
          dsimp only
          cases (_ && _) <;> rfl
  | rem =>
    dsimp only
    cases (true && r == 0) with
    | true => rfl
    | false =>
      cases (s && true && (l == signedMinInt w && r == Neg.neg 1)) with
      | true => rfl
      | false =>
        rw [mirIntTmod_eq, mirTruncateScalar_eq]
        cases truncateScalar w s (intTmod l r) with
        | error _ => rfl
        | ok pair =>
          cases pair
          dsimp only
          cases (_ && _) <;> rfl
  | addWithOverflow | subWithOverflow | mulWithOverflow
  | bitXor | bitAnd | bitOr | shl | shlUnchecked | shr | shrUnchecked
  | eq | lt | le | ne | ge | gt | offset =>
    dsimp only
    cases (false && r == 0) with
    | true => rfl
    | false =>
      cases (s && false && (l == signedMinInt w && r == Neg.neg 1)) <;> rfl

/-- Success/failure agreement between computable `mirEvalBinOpVal` and
`Trusted.MirSemantics.evalBinOp` (collapsing error fault kinds to `none`). -/
theorem mirEvalBinOpVal_eq (op : BinOp) (lhs rhs : Val) :
    mirEvalBinOpVal op lhs rhs =
      match evalBinOp op lhs rhs with
      | .ok res => some res
      | .error _ => none := by
  have hShift : mirBinOpIsShift op = op.isShift := by
    cases op <;> rfl
  cases lhs with
  | scalar l =>
    cases rhs with
    | scalar r =>
      dsimp only [mirEvalBinOpVal, evalBinOp]
      rw [mirDecodeScalar_eq l, mirDecodeScalar_eq r, hShift,
          mirIntWidthBeq_eq l.width r.width]
      cases op.isShift with
      | true =>
        exact mirEvalShiftOp_eq op l.width l.signed
          (decodeScalar l) (decodeScalar r)
      | false =>
        cases (!(IntWidth.beq l.width r.width && (l.signed == r.signed))) with
        | true => rfl
        | false =>
          cases op with
          | eq | ne | lt | le | gt | ge => rfl
          | bitAnd | bitOr | bitXor =>
            dsimp only
            rw [mirTruncateBits_eq_truncateBits,
                mirTruncateBits_eq_truncateBits,
                mirTruncateBits_eq_truncateBits]
            rfl
          | add | sub | mul | div | rem
          | addUnchecked | subUnchecked | mulUnchecked =>
            rw [mirEvalArithOp_eq]
            rfl
          | addWithOverflow | subWithOverflow | mulWithOverflow
          | shl | shlUnchecked | shr | shrUnchecked | offset => rfl
    | ptr _ | bool _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
  | bool l =>
    cases rhs with
    | bool r =>
      cases op <;> rfl
    | scalar _ | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl
  | ptr _ | unit | enumVal _ _ | tuple _ | bytes _ => rfl

/-! ## Algorithmic Straight-Line MIR Lifter (`liftStraightLineMir`)

Translates single-block `Trusted.MirAst.Program` bodies (`bb0` ending in
`TerminatorKind.return_`) into `FlowPlan Val` plans that track each MIR local
`l < L`'s storage liveness (`SlotCapState.hasLive`) and represent active
initialization (`mirInitCap L l`, mutably borrowing `mirValSlot argCnt l`)
directly inside `PureLift`'s loan graph:
- `StatementKind.storageLive l` retires any prior active loan on `l` and marks
  `l`'s storage live (allocating `mirInitCap L l` immediately when
  `mirLiveUninitSlot ty` is inhabited, e.g. `MirTy.unit`).
- `StatementKind.storageDead l` retires `mirInitCap L l` if active and marks
  `l` dead, causing any subsequent read or write of `l` (without a fresh
  `StorageLive`) to dereference an ended/unit handle and fail closed with
  `.fail`.
- `Operand.copy ⟨l, []⟩` unconditionally reads `*mirInitCap L l`, failing with
  `.fail` if `l` is dead or uninitialized.
- `Operand.move ⟨l, []⟩` unconditionally reads `*mirInitCap L l` and, for
  non-ZST types (`mirLiveUninitSlot ty = .live none`), ends `mirInitCap L l` via
  `.endLoanAtLocal` so any subsequent read before reassignment fails with
  `.fail` (matching `Trusted.MirSemantics.evalOperandToSlot`).
-/

/-- Merge adjacent pairs from the right via `List.foldr` (turning even-length
lists `[p1, p2, p3, p4, ...]` into `[.seq p1 p2, .seq p3 p4, ...]` and
odd-length lists into `[p1, .seq p2 p3, ...]`) in a single pass while
preserving left-to-right sequencing order. -/
def mergePlanPairs (ps : List (FlowPlan Val)) : List (FlowPlan Val) :=
  let step :=
    ps.foldr
      (fun p (acc : Option (FlowPlan Val) × List (FlowPlan Val)) =>
        match acc.1 with
        | none => (some p, acc.2)
        | some pNext => (none, .seq p pNext :: acc.2))
      (none, [])
  match step.1 with
  | none => step.2
  | some pFirst => pFirst :: step.2

/-- Assemble a list of `PrimAction Val` steps into a balanced `.seq` tree via
bottom-up pairwise merging (`natFold` + `List.foldr`) so evaluation closure
depth scales logarithmically without duplicating recursive continuations. -/
def actionsToPlan (acts : List (PrimAction Val)) : FlowPlan Val :=
  let plans0 : List (FlowPlan Val) :=
    acts.foldr (fun a acc => .act a :: acc) []
  let merged : List (FlowPlan Val) :=
    natFold
      plans0
      (fun _ acc =>
        match acc with
        | [] => []
        | [p] => [p]
        | _ => mergePlanPairs acc)
      8
  match merged with
  | [] => .skip
  | [p] => p
  | ps => ps.foldr .seq .skip

/-- Generate `count` consecutive fresh `PureLift` local assignments starting at
`start`, each initialized to `initVal`, via `natFold`. -/
def allocFreshLocalActions (start count : Nat) (initVal : Val) :
    List (PrimAction Val) :=
  natFold
    (fun _ => [])
    (fun _ ih cur =>
      .assign (.localSub cur []) (.constVal initVal) :: ih (cur + 1))
    count start

/-- Backing `PureLift` local register for MIR local `l` in a body with `argCnt`
entry parameters (`_1 .. _argCnt` occupy `0 .. argCnt - 1`, `_0` occupies
`argCnt`, and temporaries `> argCnt` occupy `l`). -/
def mirValSlot (argCnt l : Nat) : LocalId :=
  if l == 0 then argCnt
  else if Nat.ble l argCnt then l - 1
  else l

/-- Initialization capability handle slot (`&mut mirValSlot argCnt l`) for MIR
local `l`. -/
def mirInitCap (numLocals l : Nat) : LocalId :=
  numLocals + l

/-- Scratch local register for the first evaluated operand or Rvalue result, and
for holding the return value read from `_0` in the epilogue. -/
def mirOp1Slot (numLocals : Nat) : LocalId :=
  2 * numLocals

/-- Scratch local register for the second evaluated binary operand. -/
def mirOp2Slot (numLocals : Nat) : LocalId :=
  2 * numLocals + 1

/-- Compile-time capability state of a MIR local during straight-line lifting:
tracks storage liveness (`hasLive`) and whether `mirInitCap` currently holds an
active loan (`hasInit`), while all reads and writes resolve through
`mirInitCap` / `mirValSlot` inside `PureLift` (failing closed on uninitialized,
moved-from, or dead locals). -/
structure SlotCapState where
  hasLive : Bool
  hasInit : Bool

/-- Read `SlotCapState` for MIR local `l` (defaulting to inactive). -/
def getSlotCap (caps : List SlotCapState) (l : Nat) : SlotCapState :=
  match mirListGet? caps l with
  | some c => c
  | none => ⟨false, false⟩

/-- Update `SlotCapState` for MIR local `l`. -/
def setSlotCap (caps : List SlotCapState) (l : Nat) (c : SlotCapState) :
    List SlotCapState :=
  match mirListSet? caps l c with
  | some caps' => caps'
  | none => caps

/-- Retire an active `mirInitCap` loan on `l` and mark `l` dead. -/
def retireSlotCapActions (numLocals l : Nat) (caps : List SlotCapState) :
    List (PrimAction Val) × List SlotCapState :=
  let c := getSlotCap caps l
  let initActs : List (PrimAction Val) :=
    if c.hasInit then [.endLoanAtLocal (mirInitCap numLocals l)] else []
  (initActs, setSlotCap caps l ⟨false, false⟩)

/-- Allocate fresh live storage for MIR local `l` of type `ty`, matching
`Trusted.MirSemantics.liveUninitSlot ty`. -/
def allocLiveUninitActions (argCnt numLocals l : Nat) (ty : MirTy) :
    List (PrimAction Val) × SlotCapState :=
  match mirLiveUninitSlot ty with
  | .live (some zstVal) =>
    ([ .assign (.localSub (mirValSlot argCnt l) []) (.constVal zstVal),
       .borrow (mirInitCap numLocals l) .mutBorrow
         (.localSub (mirValSlot argCnt l) []) ],
     ⟨true, true⟩)
  | .live none => ([], ⟨true, false⟩)
  | .dead => ([], ⟨false, false⟩)

/-- Initialize storage and initialization capabilities for all MIR locals at
entry in lockstep with `Trusted.MirSemantics.initLocalsLoop` (enforcing
`mirCheckVal` on parameter slots `1 .. argCnt` so standalone `evalFnValue`
calls fail closed on ill-typed or uninhabited `MirTy.never` arguments). -/
def mirInitEntryLocalsLoop (body : Body) (argCnt numLocals idx : Nat)
    (tys : List MirTy) : List (PrimAction Val) × List SlotCapState :=
  tys.foldr
    (fun ty ih curIdx =>
      let cur : List (PrimAction Val) × SlotCapState :=
        if Nat.beq curIdx 0 then
          allocLiveUninitActions argCnt numLocals 0 ty
        else if Nat.ble curIdx argCnt then
          ([ .assign (.localSub (mirValSlot argCnt curIdx) [])
               (.unary (fun v => if mirCheckVal v ty then some v else none)
                 (.localSub (mirValSlot argCnt curIdx) [])),
             .borrow (mirInitCap numLocals curIdx) .mutBorrow
               (.localSub (mirValSlot argCnt curIdx) []) ],
           ⟨true, true⟩)
        else if mirHasStorageAnnotation body curIdx then
          ([], ⟨false, false⟩)
        else
          allocLiveUninitActions argCnt numLocals curIdx ty
      let tail := ih (curIdx + 1)
      (cur.1 ++ tail.1, cur.2 :: tail.2))
    (fun _ => ([], []))
    idx

/-- Retire all remaining active local capability loans across `idx .. idx +
count - 1` at `Return` via `natFold`. -/
def retireRangeActions (numLocals idx count : Nat)
    (caps : List SlotCapState) : List (PrimAction Val) :=
  natFold
    (fun _ _ => [])
    (fun _ ih curIdx curCaps =>
      let step := retireSlotCapActions numLocals curIdx curCaps
      step.1 ++ ih (curIdx + 1) step.2)
    count idx caps

/-- Lift a single MIR `Operand` into `scratch` in left-to-right order, enforcing
`mirIsPrimitiveReadableTy` when `requirePrimitive = true`, rejecting static
`.unsupported` constants with `none`, mapping runtime `.undefined` constant UB
to `.fail`, and retiring `mirInitCap` on non-ZST `Operand.move`. -/
def liftMirOperand (bodyLocals : List MirTy) (numLocals scratch : Nat)
    (requirePrimitive : Bool) (caps : List SlotCapState) (opnd : Operand) :
    Option (MirTy × List (PrimAction Val) × List SlotCapState) :=
  match opnd with
  | .copy place =>
    if !place.projection.isEmpty then none
    else
      match mirListGet? bodyLocals place.localId with
      | none => none
      | some ty =>
        if requirePrimitive && !mirIsPrimitiveReadableTy ty then none
        else
          some (ty,
            [.assign (.localSub scratch [])
              (.use (.derefSub (mirInitCap numLocals place.localId) []))],
            caps)
  | .move place =>
    if !place.projection.isEmpty then none
    else
      match mirListGet? bodyLocals place.localId with
      | none => none
      | some ty =>
        if requirePrimitive && !mirIsPrimitiveReadableTy ty then none
        else
          let readAct : PrimAction Val :=
            .assign (.localSub scratch [])
              (.use (.derefSub (mirInitCap numLocals place.localId) []))
          match mirLiveUninitSlot ty with
          | .live (some zstVal) =>
            let reinitAct : PrimAction Val :=
              .assign (.derefSub (mirInitCap numLocals place.localId) [])
                (.constVal zstVal)
            some (ty, [readAct, reinitAct], caps)
          | _ =>
            let c := getSlotCap caps place.localId
            let endActs : List (PrimAction Val) :=
              if c.hasInit then
                [.endLoanAtLocal (mirInitCap numLocals place.localId)]
              else []
            let caps' := setSlotCap caps place.localId ⟨c.hasLive, false⟩
            some (ty, readAct :: endActs, caps')
  | .constant c =>
    if requirePrimitive && !mirIsPrimitiveReadableTy c.ty then none
    else
      match mirEvalConstLit c.ty c.lit with
      | .ok v =>
        some (c.ty, [.assign (.localSub scratch []) (.constVal v)], caps)
      | .error .undefined =>
        some (c.ty,
          [.assign (.localSub scratch [])
            (.unary (fun _ => none) (.localSub scratch []))],
          caps)
      | .error .unsupported => none

/-- Lift an `Rvalue` (including `Rvalue.discriminant` on admitted fieldless
enums) so its evaluated result lands in `mirOp1Slot numLocals`. -/
def liftMirRvalue (numLocals : Nat) (bodyLocals : List MirTy) (dstTy : MirTy)
    (caps : List SlotCapState) (rval : Rvalue) :
    Option (List (PrimAction Val) × List SlotCapState) :=
  match rval with
  | .use opnd =>
    match liftMirOperand bodyLocals numLocals (mirOp1Slot numLocals) false caps
        opnd with
    | none => none
    | some (srcTy, opActs, caps1) =>
      if !mirTyBeq srcTy dstTy then none
      else some (opActs, caps1)
  | .binaryOp op lhs rhs =>
    match liftMirOperand bodyLocals numLocals (mirOp1Slot numLocals) true caps
        lhs with
    | none => none
    | some (_, lhsActs, caps1) =>
      match liftMirOperand bodyLocals numLocals (mirOp2Slot numLocals) true
          caps1 rhs with
      | none => none
      | some (_, rhsActs, caps2) =>
        let computeAct : PrimAction Val :=
          .assign (.localSub (mirOp1Slot numLocals) [])
            (.binary (mirEvalBinOpVal op)
              (.localSub (mirOp1Slot numLocals) [])
              (.localSub (mirOp2Slot numLocals) []))
        some (lhsActs ++ rhsActs ++ [computeAct], caps2)
  | .unaryOp op opnd =>
    match liftMirOperand bodyLocals numLocals (mirOp1Slot numLocals) true caps
        opnd with
    | some (_, opActs, caps1) =>
      let computeAct : PrimAction Val :=
        .assign (.localSub (mirOp1Slot numLocals) [])
          (.unary (mirEvalUnOpVal op) (.localSub (mirOp1Slot numLocals) []))
      some (opActs ++ [computeAct], caps1)
    | none => none
  | .discriminant place =>
    if !place.projection.isEmpty then none
    else
      match mirListGet? bodyLocals place.localId with
      | some (.enum ety) =>
        if !mirEnumAdmitted ety ||
            !mirTyBeq (.int ety.discrWidth ety.discrSigned) dstTy then
          none
        else
          let readAct : PrimAction Val :=
            .assign (.localSub (mirOp1Slot numLocals) [])
              (.use (.derefSub (mirInitCap numLocals place.localId) []))
          let discrAct : PrimAction Val :=
            .assign (.localSub (mirOp1Slot numLocals) [])
              (.unary (mirEvalDiscrVal ety)
                (.localSub (mirOp1Slot numLocals) []))
          some ([readAct, discrAct], caps)
      | _ => none
  | _ => none

/-- Write `mirOp1Slot numLocals` into destination MIR local `dstLocal` of type
`dstTy`, checking `mirCheckVal` and requiring `dstLocal` to have active storage
(writing through `mirInitCap` when dead so `PureLift` rejects writes to dead
locals). -/
def writeDstLocalActions (argCnt numLocals dstLocal : Nat) (dstTy : MirTy)
    (caps : List SlotCapState) : List (PrimAction Val) × List SlotCapState :=
  let checkedRhs : RvalOp Val :=
    .unary (fun v => if mirCheckVal v dstTy then some v else none)
      (.localSub (mirOp1Slot numLocals) [])
  let c := getSlotCap caps dstLocal
  if !c.hasLive || c.hasInit then
    ([.assign (.derefSub (mirInitCap numLocals dstLocal) []) checkedRhs], caps)
  else
    ([ .assign (.localSub (mirValSlot argCnt dstLocal) []) checkedRhs,
       .borrow (mirInitCap numLocals dstLocal) .mutBorrow
         (.localSub (mirValSlot argCnt dstLocal) []) ],
     setSlotCap caps dstLocal ⟨true, true⟩)

/-- Lift a single `StatementKind` in a straight-line MIR basic block. -/
def liftMirStmt (argCnt numLocals : Nat) (bodyLocals : List MirTy)
    (caps : List SlotCapState) (stmt : StatementKind) :
    Option (List (PrimAction Val) × List SlotCapState) :=
  match stmt with
  | .nop => some ([], caps)
  | .storageLive l =>
    match mirListGet? bodyLocals l with
    | some ty =>
      let retired := retireSlotCapActions numLocals l caps
      let allocated := allocLiveUninitActions argCnt numLocals l ty
      some (retired.1 ++ allocated.1, setSlotCap retired.2 l allocated.2)
    | none => none
  | .storageDead l =>
    if Nat.beq l 0 || !Nat.blt l numLocals then none
    else some (retireSlotCapActions numLocals l caps)
  | .assign dst rval =>
    if !dst.projection.isEmpty then none
    else
      match mirListGet? bodyLocals dst.localId with
      | none => none
      | some dstTy =>
        match liftMirRvalue numLocals bodyLocals dstTy caps rval with
        | some (rvalActs, caps1) =>
          let written :=
            writeDstLocalActions argCnt numLocals dst.localId dstTy caps1
          some (rvalActs ++ written.1, written.2)
        | none => none
  | .unsupported => none

/-- Lift a sequence of MIR statements into `PrimAction Val` steps via
`List.foldr`. -/
def liftMirStmtList (argCnt numLocals : Nat) (bodyLocals : List MirTy)
    (caps : List SlotCapState) (stmts : List StatementKind) :
    Option (List (PrimAction Val) × List SlotCapState) :=
  stmts.foldr
    (fun stmt ih curCaps =>
      match liftMirStmt argCnt numLocals bodyLocals curCaps stmt with
      | none => none
      | some (stmtActs, caps1) =>
        match ih caps1 with
        | none => none
        | some (restActs, caps2) => some (stmtActs ++ restActs, caps2))
    (fun curCaps => some ([], curCaps))
    caps

/-- Algorithmically translate a single-block straight-line
`Trusted.MirAst.Program` (`bb0` terminating with `TerminatorKind.return_`) into
`(plan, retExpr)`. -/
def liftStraightLineMir (p : Program) :
    Option (FlowPlan Val × RvalOp Val) :=
  match mirListGet? p.bodies p.entryDefId with
  | none => none
  | some body =>
    if !mirBodyStaticAdmitted p body then none
    else
      match body.basicBlocks with
      | [bb] =>
        let isCleanReturn : Bool :=
          !bb.cleanup &&
          match bb.terminator with
          | .return_ => true
          | _ => false
        if !isCleanReturn then none
        else
          let argCnt := body.argumentCount
          let numLocals := body.locals.length
          let freshActs :=
            allocFreshLocalActions argCnt (2 * numLocals + 2 - argCnt) .unit
          let entryInit :=
            mirInitEntryLocalsLoop body argCnt numLocals 0 body.locals
          match liftMirStmtList argCnt numLocals body.locals entryInit.2
              bb.statements with
          | none => none
          | some (stmtActs, finalCaps) =>
            let epilogueActs : List (PrimAction Val) :=
              .assign (.localSub (mirOp1Slot numLocals) [])
                (.use (.derefSub (mirInitCap numLocals 0) [])) ::
              retireRangeActions numLocals 0 numLocals finalCaps
            let allActs :=
              freshActs ++ entryInit.1 ++ stmtActs ++ epilogueActs
            some (actionsToPlan allActs,
              .use (.localSub (mirOp1Slot numLocals) []))
      | _ => none

/-- Unpack `liftStraightLineMir p` with a dummy fallback; coupling predicates
always require `liftStraightLineMir p = some (plan, retExpr)`, which refutes the
`none` case. -/
def liftedPlanOrSkip (p : Program) : FlowPlan Val × RvalOp Val :=
  match liftStraightLineMir p with
  | some pair => pair
  | none => (.skip, .constVal .unit)

/-- Structural coupling predicate tying `(p, q)` to `(params, plan, retExpr)`:
`params` aligns with `(p, q)` via `MirArgsMatch` (including `q.callerMem = ⟨[]⟩`
and `ValidEntryArgs body q.args`) and `(plan, retExpr)` is the exact `FlowPlan`
produced by `liftStraightLineMir p` (which implies `BodyStaticAdmitted p body =
true` via `mirBodyStaticAdmitted_eq`). -/
def MirStraightLineLiftsTo (p : Program) (q : Query)
    (params : List (ParamInput Val))
    (plan : FlowPlan Val) (retExpr : RvalOp Val) : Prop :=
  MirArgsMatch p q params ∧
  liftStraightLineMir p = some (plan, retExpr)

/-- Any successful `liftStraightLineMir p = some (plan, retExpr)` implies that
the entry body exists and satisfies `Trusted.MirSemantics.BodyStaticAdmitted`.
-/
theorem bodyStaticAdmitted_of_liftStraightLineMir
    {p : Program} {plan : FlowPlan Val} {retExpr : RvalOp Val}
    (hLift : liftStraightLineMir p = some (plan, retExpr)) :
    Exists fun body =>
      Trusted.MirSemantics.getElem? p.bodies p.entryDefId = some body ∧
      BodyStaticAdmitted p body = true := by
  unfold liftStraightLineMir at hLift
  cases hGet : mirListGet? p.bodies p.entryDefId with
  | none =>
    rw [hGet] at hLift
    nomatch hLift
  | some body =>
    rw [hGet] at hLift
    dsimp only at hLift
    cases hAdm : mirBodyStaticAdmitted p body with
    | false =>
      rw [hAdm] at hLift
      nomatch hLift
    | true =>
      rw [mirListGet?_eq_getElem?] at hGet
      rw [mirBodyStaticAdmitted_eq] at hAdm
      exact ⟨body, hGet, hAdm⟩

/-- Every `MirStraightLineLiftsTo p q params plan retExpr` guarantees successful
entry initialization `initState p q = .ok s₀`, so an entry-validation error from
`initState` (ill-typed arguments, nonempty `callerMem`, or an unadmitted entry
body) can never satisfy `MirRunsFault p q fuel expected`. -/
theorem initState_ok_of_mirStraightLineLiftsTo
    {p : Program} {q : Query} {params : List (ParamInput Val)}
    {plan : FlowPlan Val} {retExpr : RvalOp Val}
    (hLift : MirStraightLineLiftsTo p q params plan retExpr) :
    Exists fun s₀ => initState p q = .ok s₀ := by
  cases bodyStaticAdmitted_of_liftStraightLineMir hLift.2 with
  | intro body hPair =>
    have hArgs := hLift.1
    unfold MirArgsMatch at hArgs
    cases q with
    | mk args cm =>
      have hCm : cm = ⟨[]⟩ := hArgs.2.2.1
      subst hCm
      have hRest := hArgs.2.2.2
      rw [hPair.1] at hRest
      exact ⟨_, Anneal.MirWp.initState_eq_ok hPair.1 hPair.2 hRest.2⟩

/-- Coupled fault transfer theorem across `FaultEquivalenceClaim`:
when `(params, plan, retExpr)` is the algorithmically lifted plan of `(p, q)`
(`MirStraightLineLiftsTo p q params plan retExpr`), `PureLift` rejects that
lifted plan (`evalFnValue ... = .fail`), and `MirRunsFault p q fuel expected`
holds, `(p, q)` passes `initState` (`∃ s₀, initState p q = .ok s₀`), is
rejected by `PureLift`, faults exclusively with `expected` during body
execution in $M_{\text{anneal}}$, admits neither `Behavior` nor `Diverges`, is
not `WellFormed`, and reaches `faultToRefOutcome expected` in $M_{\text{ref}}$
(`lean-miri`). -/
theorem mir_fault_correspondence_transfer
    {RefProg RefOutcome : Type}
    (encodeProg : Program → RefProg)
    (faultToRefOutcome : FaultKind → RefOutcome)
    (RefReachesOutcome : RefProg → Query → Nat → RefOutcome → Prop)
    (hFaultCorr : MirFaultCorrespondenceBridge encodeProg faultToRefOutcome
      RefReachesOutcome)
    (p : Program) (q : Query) (fuel : Nat)
    (expected : FaultKind)
    (params : List (ParamInput Val))
    (plan : FlowPlan Val)
    (retExpr : RvalOp Val)
    (hLift : MirStraightLineLiftsTo p q params plan retExpr)
    (hPureFail : evalFnValue mirValAlg params plan retExpr = .fail)
    (hMirFault : MirRunsFault p q fuel expected) :
    MirStraightLineLiftsTo p q params plan retExpr ∧
    (Exists fun s₀ => initState p q = .ok s₀) ∧
    (∀ post, ¬ HoldsFnSpec (evalFnValue mirValAlg params plan retExpr) post) ∧
    ReachesResult p q (.fault expected) ∧
    (∀ k : FaultKind, k ≠ expected → ¬ ReachesResult p q (.fault k)) ∧
    (∀ out : TerminalOut, ¬ Behavior p q out) ∧
    ¬ Diverges p q ∧
    ¬ WellFormed p q ∧
    (∃ maxSteps,
      RefReachesOutcome (encodeProg p) q maxSteps
        (faultToRefOutcome expected)) := by
  have hInitOk := initState_ok_of_mirStraightLineLiftsTo hLift
  have hFault := reachesFault_of_mirRunsFault p q fuel expected hMirFault
  have hRefFault := (hFaultCorr p q expected).mp hFault.1
  refine ⟨hLift, hInitOk, fun post hSpec => ?_, hFault.1, hFault.2.1,
    hFault.2.2.1, hFault.2.2.2.1, hFault.2.2.2.2, hRefFault⟩
  rw [hPureFail] at hSpec
  nomatch hSpec

/-! ## Verified MIR and `PureLift` Workloads (`W-1` through `W-5`) -/

/-- Computable `u32` type descriptor (`IntWidth.i32`, unsigned), definitionally
equal (`rfl`) to `Trusted.MirSemantics.u32Ty`. -/
def mirU32Ty : MirTy := .int .i32 false

/-- Computable `u32` scalar constructor, definitionally equal (`rfl`) to
`Trusted.MirSemantics.u32Val`. -/
def mirU32Val (n : Nat) : Val :=
  .scalar ⟨.i32, false, BitVec.ofNat 128 n⟩

/-- Pure `u32` wrapping addition on `Trusted.MirSemantics.Val`, matching
`Trusted.MirSemantics.evalBinOp .add` on `u32` scalars. -/
def mirAddU32Val (v1 v2 : Val) : Option Val :=
  mirEvalBinOpVal .add v1 v2

/-- Pure `u32` wrapping subtraction on `Trusted.MirSemantics.Val`, matching
`Trusted.MirSemantics.evalBinOp .sub` on `u32` scalars. -/
def mirSubU32Val (v1 v2 : Val) : Option Val :=
  mirEvalBinOpVal .sub v1 v2

/-- Pure `>` comparison on `Trusted.MirSemantics.Val`, matching
`Trusted.MirSemantics.evalBinOp .gt`. -/
def mirGtU32Val (v1 v2 : Val) : Option Val :=
  mirEvalBinOpVal .gt v1 v2

/-- Construct a `u32` constant operand (`ConstOperand`). -/
def u32Const (n : Nat) : Operand :=
  .constant ⟨mirU32Ty, .scalar (BitVec.ofNat 128 n)⟩

/-! ### Workload W-1: Straight-Line Arithmetic, Local Lifecycle, and Move Deinit

Rust equivalent for `progComputeLinearU32`:
```rust
fn compute_linear(x: u32, delta: u32) -> u32 {
    let mut tmp = x;
    tmp = tmp + delta;
    let out = tmp; // MIR Operand.move (_3 -> _4; u32 is Copy in surface Rust)
    out + delta
}
```
Exercises `StorageLive`, `StorageDead`, `Operand.copy`, `Operand.move`
(runtime move deinitialization of `_3` into `_4` and `_4` into `_0`), and
`BinOp.add`. Verified end-to-end across `CorrespondenceClaim` to `lean-miri`
($M_{\text{ref}}$) using both the algorithmic `liftStraightLineMir` plan and the
explicit mutable-borrow plan `mirComputeLinearPlan`. Also includes a separate
standalone `PureLift` mutable-reference writeback check (`mirAddAssignPlan`,
evaluated in `PureLift` alone because `Trusted.MirSemantics` v1 rejects `.ref`
at entry).
-/

/-- Authoritative `Trusted.MirAst.Program` for `compute_linear(x: u32, delta:
u32) -> u32`. -/
def progComputeLinearU32 : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "compute_linear_u32"
    argumentCount := 2
    locals := [mirU32Ty, mirU32Ty, mirU32Ty, mirU32Ty, mirU32Ty]
    basicBlocks := [{
      statements := [
        .storageLive 3,
        .assign ⟨3, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨2, []⟩)),
        .storageLive 4,
        .assign ⟨4, []⟩ (.use (.move ⟨3, []⟩)),
        .storageDead 3,
        .assign ⟨0, []⟩ (.binaryOp .add (.move ⟨4, []⟩) (.copy ⟨2, []⟩)),
        .storageDead 4
      ]
      terminator := .return_
    }]
  }]

/-- Explicit `PureLift` `FlowPlan` for `compute_linear`: local `0` is `x`, local
`1` is `delta`, local `2` is `tmp = x`, local `3` is `r = &mut tmp` (loan `0`),
`*r = *r + delta`, loan `0` ends, and local `4` receives `out = tmp`. -/
def mirComputeLinearPlan : FlowPlan Val :=
  .seq
    (.act (.assign (.localSub 2 []) (.use (.localSub 0 []))))
    (.seq
      (.act (.borrow 3 .mutBorrow (.localSub 2 [])))
      (.seq
        (.act (.assign (.derefSub 3 [])
          (.binary mirAddU32Val (.derefSub 3 []) (.localSub 1 []))))
        (.seq
          (.act (.endLoan 0))
          (.act (.assign (.localSub 4 []) (.use (.localSub 2 [])))))))

/-- Standalone `PureLift` `FlowPlan` for `add_assign(p: &mut u32, delta: u32) ->
u32`: reborrows `r = &mut *p` (loan `1`), updates `*r = *r + delta`, and ends
loan `1`. -/
def mirAddAssignPlan : FlowPlan Val :=
  .seq
    (.act (.borrow 2 .mutBorrow (.derefSub 0 [])))
    (.seq
      (.act (.assign (.derefSub 2 [])
        (.binary mirAddU32Val (.derefSub 2 []) (.localSub 1 []))))
      (.act (.endLoan 1)))

/-- Standalone `PureLift` verification of mutable-reference writeback in
`mirAddAssignPlan` (`out.mutFinals = [u32Val 36]`, evaluated in `PureLift` over
`mirValAlg` rather than `Trusted.MirSemantics`). -/
theorem pure_lift_add_assign_verified :
    evalFnValue mirValAlg
      [⟨.mutRef 0 [], u32Val 30⟩, ⟨.byVal, u32Val 6⟩]
      mirAddAssignPlan
      (.use (.derefSub 0 [])) =
    .ok ⟨u32Val 36, [u32Val 36]⟩ := rfl

/-- Input query `(30u32, 6u32)` for `progComputeLinearU32` (`30 + 6 + 6 = 42`).
-/
def queryComputeLinear30_6 : Query :=
  { args := [mirU32Val 30, mirU32Val 6] }

/-- Standalone kernel evaluation of the algorithmically lifted `FlowPlan` for
`progComputeLinearU32` on `(30u32, 6u32)` so downstream proofs reuse the
verified equality without re-reducing `evalFnValue`. -/
theorem mir_compute_linear_lifted_eval :
    evalFnValue mirValAlg [⟨.byVal, u32Val 30⟩, ⟨.byVal, u32Val 6⟩]
      (liftedPlanOrSkip progComputeLinearU32).1
      (liftedPlanOrSkip progComputeLinearU32).2 =
      .ok ⟨u32Val 42, []⟩ := rfl

/-- Standalone kernel evaluation of `MirRunsTo` for `progComputeLinearU32` on
`(30u32, 6u32)`. -/
theorem mir_compute_linear_runs :
    MirRunsTo progComputeLinearU32 queryComputeLinear30_6 9
      ⟨u32Val 42, []⟩ := ⟨rfl, rfl⟩

/-- End-to-end verification of `progComputeLinearU32` on `(30u32, 6u32)` via
both `liftStraightLineMir` and `mirComputeLinearPlan`, discharging `MirRunsTo`
(`hSim`) and transferring `WellFormed`, `Behavior`, `¬ Diverges`, and
`SatisfiesPost` for both plans across `CorrespondenceClaim` to `lean-miri`
($M_{\text{ref}}$). -/
theorem mir_compute_linear_verified
    {RefProg : Type}
    (encodeProg : Program → RefProg)
    (RefWellFormed : RefProg → Query → Prop)
    (RefBehavior : RefProg → Query → TerminalOut → Prop)
    (RefDiverges : RefProg → Query → Prop)
    (hCorr : MirCorrespondenceBridge encodeProg RefWellFormed RefBehavior
      RefDiverges) :
    let params : List (ParamInput Val) :=
      [⟨.byVal, u32Val 30⟩, ⟨.byVal, u32Val 6⟩]
    let lifted := liftedPlanOrSkip progComputeLinearU32
    let explicitRet : RvalOp Val :=
      .binary mirAddU32Val (.localSub 4 []) (.localSub 1 [])
    let post (out : FuncOut Val) : Prop :=
      out = ⟨u32Val 42, []⟩
    -- 1. Algorithmic `liftStraightLineMir` translation succeeds and evaluates
    -- to `42u32`:
    MirStraightLineLiftsTo progComputeLinearU32 queryComputeLinear30_6
      params lifted.1 lifted.2 ∧
    evalFnValue mirValAlg params lifted.1 lifted.2 =
      .ok ⟨u32Val 42, []⟩ ∧
    -- 2. Explicit mutable-borrow plan `mirComputeLinearPlan` also evaluates to
    -- `42u32`:
    evalFnValue mirValAlg params mirComputeLinearPlan explicitRet =
      .ok ⟨u32Val 42, []⟩ ∧
    -- 3. Authoritative `Trusted.MirSemantics` multi-step run yields `42u32`
    -- with `mutFinals = []`:
    MirRunsTo progComputeLinearU32 queryComputeLinear30_6 9
      ⟨u32Val 42, []⟩ ∧
    -- 4. End-to-end transfer of the algorithmically lifted plan across
    -- `CorrespondenceClaim` to `lean-miri` ($M_{\text{ref}}$):
    (Exists fun out =>
      MirArgsMatch progComputeLinearU32 queryComputeLinear30_6 params ∧
      evalFnValue mirValAlg params lifted.1 lifted.2 = .ok out ∧
      out.mutFinals = [] ∧
      post out ∧
      WellFormed progComputeLinearU32 queryComputeLinear30_6 ∧
      Behavior progComputeLinearU32 queryComputeLinear30_6
        (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ Diverges progComputeLinearU32 queryComputeLinear30_6 ∧
      SatisfiesPost progComputeLinearU32 queryComputeLinear30_6
        (fun tOut => tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out) ∧
      RefWellFormed (encodeProg progComputeLinearU32) queryComputeLinear30_6 ∧
      RefBehavior (encodeProg progComputeLinearU32) queryComputeLinear30_6
        (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ RefDiverges (encodeProg progComputeLinearU32) queryComputeLinear30_6 ∧
      (∀ tOut,
        RefBehavior (encodeProg progComputeLinearU32) queryComputeLinear30_6
          tOut →
        tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out)) ∧
    -- 5. End-to-end transfer of the explicit `mirComputeLinearPlan` across
    -- `CorrespondenceClaim` to `lean-miri` ($M_{\text{ref}}$):
    (Exists fun out =>
      MirArgsMatch progComputeLinearU32 queryComputeLinear30_6 params ∧
      evalFnValue mirValAlg params mirComputeLinearPlan explicitRet = .ok out ∧
      out.mutFinals = [] ∧
      post out ∧
      WellFormed progComputeLinearU32 queryComputeLinear30_6 ∧
      Behavior progComputeLinearU32 queryComputeLinear30_6
        (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ Diverges progComputeLinearU32 queryComputeLinear30_6 ∧
      SatisfiesPost progComputeLinearU32 queryComputeLinear30_6
        (fun tOut => tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out) ∧
      RefWellFormed (encodeProg progComputeLinearU32) queryComputeLinear30_6 ∧
      RefBehavior (encodeProg progComputeLinearU32) queryComputeLinear30_6
        (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ RefDiverges (encodeProg progComputeLinearU32) queryComputeLinear30_6 ∧
      (∀ tOut,
        RefBehavior (encodeProg progComputeLinearU32) queryComputeLinear30_6
          tOut →
        tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out)) := by
  have hArgs :
      MirArgsMatch progComputeLinearU32 queryComputeLinear30_6
        [⟨.byVal, u32Val 30⟩, ⟨.byVal, u32Val 6⟩] :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hExplicitEval :
      evalFnValue mirValAlg [⟨.byVal, u32Val 30⟩, ⟨.byVal, u32Val 6⟩]
        mirComputeLinearPlan
        (.binary mirAddU32Val (.localSub 4 []) (.localSub 1 [])) =
      .ok ⟨u32Val 42, []⟩ := rfl
  refine ⟨⟨hArgs, rfl⟩, mir_compute_linear_lifted_eval, hExplicitEval,
    mir_compute_linear_runs, ?_, ?_⟩
  · exact mir_pure_lift_correspondence_transfer
      encodeProg RefWellFormed RefBehavior RefDiverges hCorr
      progComputeLinearU32 queryComputeLinear30_6
      [⟨.byVal, u32Val 30⟩, ⟨.byVal, u32Val 6⟩]
      (liftedPlanOrSkip progComputeLinearU32).1
      (liftedPlanOrSkip progComputeLinearU32).2
      (fun out => out = ⟨u32Val 42, []⟩)
      hArgs
      (by
        rw [mir_compute_linear_lifted_eval]
        rfl)
      (by
        intro out hEval
        rw [mir_compute_linear_lifted_eval] at hEval
        injection hEval with hOut
        subst hOut
        exact ⟨9, mir_compute_linear_runs⟩)
  · exact mir_pure_lift_correspondence_transfer
      encodeProg RefWellFormed RefBehavior RefDiverges hCorr
      progComputeLinearU32 queryComputeLinear30_6
      [⟨.byVal, u32Val 30⟩, ⟨.byVal, u32Val 6⟩]
      mirComputeLinearPlan
      (.binary mirAddU32Val (.localSub 4 []) (.localSub 1 []))
      (fun out => out = ⟨u32Val 42, []⟩)
      hArgs
      rfl
      (by
        intro out hEval
        rw [hExplicitEval] at hEval
        injection hEval with hOut
        subst hOut
        exact ⟨9, mir_compute_linear_runs⟩)

/-! ### Workload W-2: Disjoint Tuple Field Borrows (`swap_fields`) and 4-Block
Conditional Branching (`select_add`)

1. `mirSwapFieldsPlan` (`PureLift`-only): borrows `.derefSub 0 [0]` and
   `.derefSub 0 [1]` of a 2-element `Val.tuple [a, b]` simultaneously, swaps
   them, and ends both loans (exercising `mirValAlg`'s field get/set through
   disjoint sub-place borrows; `Trusted.MirSemantics` v1 rejects `.tuple` and
   `.ref` at MIR entry).
2. `progSelectAddU32` ($M_{\text{anneal}}$ + $M_{\text{ref}}$): 4-block scalar
   MIR CFG with `SwitchInt` branching on `flag : Bool` (`bb0 -> bb1` when
   `flag = true`, `bb0 -> bb2` when `flag = false`, joining at `bb3`), paired
   with `mirSelectAddByValPlan` via per-branch `hSim` (`cases flag`) and
   transferred across `CorrespondenceClaim` to `lean-miri` ($M_{\text{ref}}$).
-/

/-- Standalone `PureLift` `FlowPlan` for `swap_fields` on `Val.tuple [a, b]`:
local `0` is `s: &mut (Val, Val)`, local `1` is `p0 = &mut (*s).0` (loan `1`),
local `2` is `p1 = &mut (*s).1` (loan `2`), and local `3` is `tmp = *p0`. -/
def mirSwapFieldsPlan : FlowPlan Val :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [0])))
    (.seq
      (.act (.borrow 2 .mutBorrow (.derefSub 0 [1])))
      (.seq
        (.act (.assign (.localSub 3 []) (.use (.derefSub 1 []))))
        (.seq
          (.act (.assign (.derefSub 1 []) (.use (.derefSub 2 []))))
          (.seq
            (.act (.assign (.derefSub 2 []) (.use (.localSub 3 []))))
            (.seq
              (.act (.endLoan 2))
              (.act (.endLoan 1)))))))

/-- Standalone `PureLift` verification of `mirSwapFieldsPlan` for any
`a, b : ScalarVal`: simultaneous disjoint sub-place borrows `[0]` and `[1]` swap
`.tuple [.scalar a, .scalar b]` into `.tuple [.scalar b, .scalar a]` and return
`.scalar b`. -/
theorem mir_swap_fields_verified (a b : ScalarVal) :
    evalFnValue mirValAlg
      [⟨.mutRef 0 [], .tuple [.scalar a, .scalar b]⟩]
      mirSwapFieldsPlan
      (.use (.derefSub 0 [0])) =
    .ok ⟨.scalar b, [.tuple [.scalar b, .scalar a]]⟩ := rfl

/-- 4-block authoritative `Trusted.MirAst.Program` for
`select_add(flag: bool, x: u32, y: u32, v: u32) -> u32`. -/
def progSelectAddU32 : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "select_add_u32"
    argumentCount := 4
    locals := [mirU32Ty, .bool, mirU32Ty, mirU32Ty, mirU32Ty, mirU32Ty]
    basicBlocks := [
      -- bb0: StorageLive(_5); SwitchInt(copy _1) [0 -> bb2, otherwise -> bb1]
      {
        statements := [.storageLive 5]
        terminator := .switchInt (.copy ⟨1, []⟩) {
          branches := [(BitVec.ofNat 128 0, 2)]
          otherwise := 1
        }
      },
      -- bb1 (flag = true): _5 = Add(copy _2, copy _4); Goto(bb3)
      {
        statements := [
          .assign ⟨5, []⟩ (.binaryOp .add (.copy ⟨2, []⟩) (.copy ⟨4, []⟩))
        ]
        terminator := .goto 3
      },
      -- bb2 (flag = false): _5 = Add(copy _3, copy _4); Goto(bb3)
      {
        statements := [
          .assign ⟨5, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (.copy ⟨4, []⟩))
        ]
        terminator := .goto 3
      },
      -- bb3 (join): _0 = move _5; StorageDead(_5); Return
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.move ⟨5, []⟩)),
          .storageDead 5
        ]
        terminator := .return_
      }
    ]
  }]

/-- `PureLift` `FlowPlan` paired with `progSelectAddU32`:
local `0` is `flag: bool`, local `1` is `x: u32`, local `2` is `y: u32`,
local `3` is `v: u32`, local `4` is the branch-selected borrow `r = if flag {
&x } else { &y }` joined via `.branchExplicitJoin`, and local `5` receives
`*r + v` before the joined loan `0` ends. -/
def mirSelectAddByValPlan : FlowPlan Val :=
  .seq
    (.branchExplicitJoin (.unary mirBoolOrScalarVal (.localSub 0 []))
      (.act (.borrow 4 .shared (.localSub 1 [])))
      (.act (.borrow 4 .shared (.localSub 2 [])))
      [(0, 0)])
    (.seq
      (.act (.assign (.localSub 5 [])
        (.binary mirAddU32Val (.derefSub 4 []) (.localSub 3 []))))
      (.act (.endLoan 0)))

/-- Input query for `progSelectAddU32` with symbolic `flag : Bool` and concrete
operands `(10u32, 100u32, 5u32)`. -/
def querySelectAdd (flag : Bool) : Query :=
  { args := [.bool flag, mirU32Val 10, mirU32Val 100, mirU32Val 5] }

/-- End-to-end verification of the 4-block `progSelectAddU32` across all
`flag : Bool`, pairing `mirSelectAddByValPlan` with explicit `MirRunsTo` case
analysis (`cases flag`) and transferring `WellFormed`, `Behavior`, and
`SatisfiesPost` across `CorrespondenceClaim` to `lean-miri` ($M_{\text{ref}}$).
-/
theorem mir_select_add_verified
    {RefProg : Type}
    (encodeProg : Program → RefProg)
    (RefWellFormed : RefProg → Query → Prop)
    (RefBehavior : RefProg → Query → TerminalOut → Prop)
    (RefDiverges : RefProg → Query → Prop)
    (hCorr : MirCorrespondenceBridge encodeProg RefWellFormed RefBehavior
      RefDiverges)
    (flag : Bool) :
    let params : List (ParamInput Val) :=
      [ ⟨.byVal, .bool flag⟩
      , ⟨.byVal, u32Val 10⟩
      , ⟨.byVal, u32Val 100⟩
      , ⟨.byVal, u32Val 5⟩ ]
    let expectedVal : Val := if flag then u32Val 15 else u32Val 105
    let post (out : FuncOut Val) : Prop := out = ⟨expectedVal, []⟩
    evalFnValue mirValAlg params mirSelectAddByValPlan (.use (.localSub 5 [])) =
      .ok ⟨expectedVal, []⟩ ∧
    MirRunsTo progSelectAddU32 (querySelectAdd flag) 7 ⟨expectedVal, []⟩ ∧
    (Exists fun out =>
      MirArgsMatch progSelectAddU32 (querySelectAdd flag) params ∧
      evalFnValue mirValAlg params mirSelectAddByValPlan
        (.use (.localSub 5 [])) = .ok out ∧
      out.mutFinals = [] ∧
      post out ∧
      WellFormed progSelectAddU32 (querySelectAdd flag) ∧
      Behavior progSelectAddU32 (querySelectAdd flag)
        (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ Diverges progSelectAddU32 (querySelectAdd flag) ∧
      SatisfiesPost progSelectAddU32 (querySelectAdd flag)
        (fun tOut => tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out) ∧
      RefWellFormed (encodeProg progSelectAddU32) (querySelectAdd flag) ∧
      RefBehavior (encodeProg progSelectAddU32) (querySelectAdd flag)
        (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ RefDiverges (encodeProg progSelectAddU32) (querySelectAdd flag) ∧
      (∀ tOut,
        RefBehavior (encodeProg progSelectAddU32) (querySelectAdd flag) tOut →
        tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out)) := by
  have hPure :
      evalFnValue mirValAlg
        [ ⟨.byVal, .bool flag⟩
        , ⟨.byVal, u32Val 10⟩
        , ⟨.byVal, u32Val 100⟩
        , ⟨.byVal, u32Val 5⟩ ]
        mirSelectAddByValPlan (.use (.localSub 5 [])) =
      .ok ⟨if flag then u32Val 15 else u32Val 105, []⟩ := by
    cases flag <;> rfl
  have hMir :
      MirRunsTo progSelectAddU32 (querySelectAdd flag) 7
        ⟨if flag then u32Val 15 else u32Val 105, []⟩ := by
    cases flag <;> exact ⟨rfl, rfl⟩
  refine ⟨hPure, hMir, ?_⟩
  exact mir_pure_lift_correspondence_transfer
    encodeProg RefWellFormed RefBehavior RefDiverges hCorr
    progSelectAddU32 (querySelectAdd flag)
    [ ⟨.byVal, .bool flag⟩
    , ⟨.byVal, u32Val 10⟩
    , ⟨.byVal, u32Val 100⟩
    , ⟨.byVal, u32Val 5⟩ ]
    mirSelectAddByValPlan
    (.use (.localSub 5 []))
    (fun out => out = ⟨if flag then u32Val 15 else u32Val 105, []⟩)
    ⟨rfl, rfl, rfl, rfl, rfl⟩
    (by cases flag <;> rfl)
    (by
      intro out hEval
      rw [hPure] at hEval
      injection hEval with hOut
      subst hOut
      exact ⟨7, hMir⟩)

/-! ### Workload W-3: Multi-Block Loop Accumulation (`loop_accumulate`)

Rust equivalent:
```rust
fn loop_accumulate(acc: u32, mut n: u32) -> u32 {
    let mut cur = acc;
    while n > 0 {
        cur = cur + 1;
        n = n - 1;
    }
    cur
}
```
4-block scalar MIR CFG (`progLoopAccumulateU32`) with loop header `bb1`, loop
body `bb2`, and exit block `bb3`, paired with `.whileLoop`
(`mirLoopAccumulatePlan`, explicit `MirRunsTo` simulation on `(39u32, 3u32)`)
and transferred across `CorrespondenceClaim` to `lean-miri` ($M_{\text{ref}}$).
-/

/-- 4-block authoritative `Trusted.MirAst.Program` for
`loop_accumulate(acc: u32, n: u32) -> u32`. -/
def progLoopAccumulateU32 : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "loop_accumulate_u32"
    argumentCount := 2
    locals := [mirU32Ty, mirU32Ty, mirU32Ty, mirU32Ty, .bool]
    basicBlocks := [
      -- bb0: StorageLive(_3); _3 = copy _1; StorageLive(_4); Goto(bb1)
      {
        statements := [
          .storageLive 3,
          .assign ⟨3, []⟩ (.use (.copy ⟨1, []⟩)),
          .storageLive 4
        ]
        terminator := .goto 1
      },
      -- bb1 (header): _4 = Gt(copy _2, const 0u32);
      -- SwitchInt(copy _4) [0 (false) -> bb3, otherwise -> bb2]
      {
        statements := [
          .assign ⟨4, []⟩ (.binaryOp .gt (.copy ⟨2, []⟩) (u32Const 0))
        ]
        terminator := .switchInt (.copy ⟨4, []⟩) {
          branches := [(BitVec.ofNat 128 0, 3)]
          otherwise := 2
        }
      },
      -- bb2 (body): _3 = Add(copy _3, const 1u32);
      -- _2 = Sub(copy _2, const 1u32); Goto(bb1)
      {
        statements := [
          .assign ⟨3, []⟩ (.binaryOp .add (.copy ⟨3, []⟩) (u32Const 1)),
          .assign ⟨2, []⟩ (.binaryOp .sub (.copy ⟨2, []⟩) (u32Const 1))
        ]
        terminator := .goto 1
      },
      -- bb3 (exit): _0 = move _3; StorageDead(_4); StorageDead(_3); Return
      {
        statements := [
          .assign ⟨0, []⟩ (.use (.move ⟨3, []⟩)),
          .storageDead 4,
          .storageDead 3
        ]
        terminator := .return_
      }
    ]
  }]

/-- `PureLift` `.whileLoop` plan paired with `progLoopAccumulateU32`:
local `0` is `acc: u32`, local `1` is `n: u32`, local `2` is `cur = acc`, and
local `3` is a per-iteration mutable borrow `r = &mut cur` retired via
`.endLoanAtLocal 3`. -/
def mirLoopAccumulatePlan : FlowPlan Val :=
  .seq
    (.act (.assign (.localSub 2 []) (.use (.localSub 0 []))))
    (.whileLoop 4
      (.unary (fun v => mirGtU32Val v (mirU32Val 0)) (.localSub 1 []))
      (.seq
        (.act (.borrow 3 .mutBorrow (.localSub 2 [])))
        (.seq
          (.act (.assign (.derefSub 3 [])
            (.unary (fun v => mirAddU32Val v (mirU32Val 1)) (.derefSub 3 []))))
          (.seq
            (.act (.endLoanAtLocal 3))
            (.act (.assign (.localSub 1 [])
              (.unary (fun v => mirSubU32Val v (mirU32Val 1))
                (.localSub 1 []))))))))

/-- Input query `(39u32, 3u32)` for `progLoopAccumulateU32` (`39 + 3 = 42`). -/
def queryLoopAccumulate39_3 : Query :=
  { args := [mirU32Val 39, mirU32Val 3] }

/-- End-to-end verification of `progLoopAccumulateU32` on `(39u32, 3u32)`
(3 loop iterations -> `42u32`), discharging `MirRunsTo` (`hSim`) and
transferring `WellFormed`, `Behavior`, and `SatisfiesPost` across
`CorrespondenceClaim` to `lean-miri` ($M_{\text{ref}}$). -/
theorem mir_loop_accumulate_verified
    {RefProg : Type}
    (encodeProg : Program → RefProg)
    (RefWellFormed : RefProg → Query → Prop)
    (RefBehavior : RefProg → Query → TerminalOut → Prop)
    (RefDiverges : RefProg → Query → Prop)
    (hCorr : MirCorrespondenceBridge encodeProg RefWellFormed RefBehavior
      RefDiverges) :
    let params : List (ParamInput Val) :=
      [⟨.byVal, u32Val 39⟩, ⟨.byVal, u32Val 3⟩]
    let post (out : FuncOut Val) : Prop := out = ⟨u32Val 42, []⟩
    evalFnValue mirValAlg params mirLoopAccumulatePlan (.use (.localSub 2 [])) =
      .ok ⟨u32Val 42, []⟩ ∧
    MirRunsTo progLoopAccumulateU32 queryLoopAccumulate39_3 25
      ⟨u32Val 42, []⟩ ∧
    (Exists fun out =>
      MirArgsMatch progLoopAccumulateU32 queryLoopAccumulate39_3 params ∧
      evalFnValue mirValAlg params mirLoopAccumulatePlan
        (.use (.localSub 2 [])) = .ok out ∧
      out.mutFinals = [] ∧
      post out ∧
      WellFormed progLoopAccumulateU32 queryLoopAccumulate39_3 ∧
      Behavior progLoopAccumulateU32 queryLoopAccumulate39_3
        (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ Diverges progLoopAccumulateU32 queryLoopAccumulate39_3 ∧
      SatisfiesPost progLoopAccumulateU32 queryLoopAccumulate39_3
        (fun tOut => tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out) ∧
      RefWellFormed (encodeProg progLoopAccumulateU32)
        queryLoopAccumulate39_3 ∧
      RefBehavior (encodeProg progLoopAccumulateU32) queryLoopAccumulate39_3
        (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
      ¬ RefDiverges (encodeProg progLoopAccumulateU32)
        queryLoopAccumulate39_3 ∧
      (∀ tOut,
        RefBehavior (encodeProg progLoopAccumulateU32) queryLoopAccumulate39_3
          tOut →
        tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out)) := by
  refine ⟨rfl, ⟨rfl, rfl⟩, ?_⟩
  exact mir_pure_lift_correspondence_transfer
    encodeProg RefWellFormed RefBehavior RefDiverges hCorr
    progLoopAccumulateU32 queryLoopAccumulate39_3
    [⟨.byVal, u32Val 39⟩, ⟨.byVal, u32Val 3⟩]
    mirLoopAccumulatePlan
    (.use (.localSub 2 []))
    (fun out => out = ⟨u32Val 42, []⟩)
    ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl
    (by
      intro out hEval
      change EvalOutcome.ok ⟨u32Val 42, []⟩ = EvalOutcome.ok out at hEval
      injection hEval with hOut
      subst hOut
      exact ⟨25, rfl, rfl⟩)

/-! ### Workload W-4: Coupled Straight-Line MIR Fault Transfer and Standalone
`PureLift` Borrow Rejection Canaries

1. **Coupled `liftStraightLineMir` + $M_{\text{anneal}}$ + $M_{\text{ref}}$
   fault transfer (`mir_negative_ub_fault_transfer_verified`):**
   - `progUseAfterMoveUb` on `(42u32)`: `liftStraightLineMir` translates
     `_2 = move _1` into ending `_1`'s initialization loan (`mirInitCap`), so
     the subsequent `_0 = copy _1` fails closed in `PureLift` (`.fail`) while
     `(progUseAfterMoveUb, [42u32])` faults with `FaultKind.undefined` in
     $M_{\text{anneal}}$ and transfers to $M_{\text{ref}}$ via
     `FaultEquivalenceClaim`.
   - `progUseAfterStorageDeadUb` on `()`: `liftStraightLineMir` translates
     `StorageDead(_1)` into ending `_1`'s initialization loan, so
     the subsequent `_0 = copy _1` fails closed in `PureLift` (`.fail`) while
     `(progUseAfterStorageDeadUb, [])` faults with `FaultKind.undefined` in
     $M_{\text{anneal}}$ and transfers to $M_{\text{ref}}$.
2. **Standalone `PureLift` borrow-discipline canaries
   (`pure_lift_borrow_rejection_canaries`):**
   - `mirDanglingRefPlan` (use-after-`endLoan`) and
     `mirOverwriteWhileBorrowedPlan` (owner overwrite while borrowed) verify
     `PureLift`'s intra-procedural borrow graph rejection directly on
     `mirValAlg`.
-/

/-- Authoritative `Trusted.MirAst.Program` that moves `_1` into `_2`
(`Operand.move`, deinitializing `_1`) and then attempts to read `_1` again. -/
def progUseAfterMoveUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "use_after_move_ub"
    argumentCount := 1
    locals := [mirU32Ty, mirU32Ty, mirU32Ty]
    basicBlocks := [{
      statements := [
        .storageLive 2,
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)),
        .storageDead 2
      ]
      terminator := .return_
    }]
  }]

/-- Named `Trusted.MirAst.Program` that initializes `_1`, retires `_1` with
`StorageDead`, and then attempts to read `_1` into `_0`. -/
def progUseAfterStorageDeadUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "use_after_storage_dead_ub"
    argumentCount := 0
    locals := [mirU32Ty, mirU32Ty]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩
          (.use (.constant ⟨mirU32Ty, .scalar (BitVec.ofNat 128 7)⟩)),
        .storageDead 1,
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Coupled negative fault-transfer canary: `liftStraightLineMir` succeeds on
`progUseAfterMoveUb` and `progUseAfterStorageDeadUb` with their aligned
`.byVal` inputs (`MirStraightLineLiftsTo`), `PureLift` rejects both lifted
plans, and both programs fault with `FaultKind.undefined` in
$M_{\text{anneal}}$ and reach `faultToRefOutcome .undefined` in
$M_{\text{ref}}$. -/
theorem mir_negative_ub_fault_transfer_verified
    {RefProg RefOutcome : Type}
    (encodeProg : Program → RefProg)
    (faultToRefOutcome : FaultKind → RefOutcome)
    (RefReachesOutcome : RefProg → Query → Nat → RefOutcome → Prop)
    (hFaultCorr : MirFaultCorrespondenceBridge encodeProg faultToRefOutcome
      RefReachesOutcome) :
    let moveParams : List (ParamInput Val) := [⟨.byVal, u32Val 42⟩]
    let moveLifted := liftedPlanOrSkip progUseAfterMoveUb
    let deadLifted := liftedPlanOrSkip progUseAfterStorageDeadUb
    -- 1. Coupled use-after-move rejection (`progUseAfterMoveUb`):
    (MirStraightLineLiftsTo progUseAfterMoveUb { args := [u32Val 42] }
        moveParams moveLifted.1 moveLifted.2 ∧
      (Exists fun s₀ =>
        initState progUseAfterMoveUb { args := [u32Val 42] } = .ok s₀) ∧
      (∀ post,
        ¬ HoldsFnSpec
          (evalFnValue mirValAlg moveParams moveLifted.1 moveLifted.2) post) ∧
      ReachesResult progUseAfterMoveUb { args := [u32Val 42] }
        (.fault .undefined) ∧
      (∀ k : FaultKind, k ≠ .undefined →
        ¬ ReachesResult progUseAfterMoveUb { args := [u32Val 42] }
            (.fault k)) ∧
      (∀ out : TerminalOut,
        ¬ Behavior progUseAfterMoveUb { args := [u32Val 42] } out) ∧
      ¬ Diverges progUseAfterMoveUb { args := [u32Val 42] } ∧
      ¬ WellFormed progUseAfterMoveUb { args := [u32Val 42] } ∧
      (∃ maxSteps,
        RefReachesOutcome (encodeProg progUseAfterMoveUb)
          { args := [u32Val 42] } maxSteps (faultToRefOutcome .undefined))) ∧
    -- 2. Coupled use-after-`StorageDead` rejection
    -- (`progUseAfterStorageDeadUb`):
    (MirStraightLineLiftsTo progUseAfterStorageDeadUb queryEmpty
        [] deadLifted.1 deadLifted.2 ∧
      (Exists fun s₀ =>
        initState progUseAfterStorageDeadUb queryEmpty = .ok s₀) ∧
      (∀ post,
        ¬ HoldsFnSpec
          (evalFnValue mirValAlg [] deadLifted.1 deadLifted.2) post) ∧
      ReachesResult progUseAfterStorageDeadUb queryEmpty (.fault .undefined) ∧
      (∀ k : FaultKind, k ≠ .undefined →
        ¬ ReachesResult progUseAfterStorageDeadUb queryEmpty (.fault k)) ∧
      (∀ out : TerminalOut,
        ¬ Behavior progUseAfterStorageDeadUb queryEmpty out) ∧
      ¬ Diverges progUseAfterStorageDeadUb queryEmpty ∧
      ¬ WellFormed progUseAfterStorageDeadUb queryEmpty ∧
      (∃ maxSteps,
        RefReachesOutcome (encodeProg progUseAfterStorageDeadUb) queryEmpty
          maxSteps (faultToRefOutcome .undefined))) := by
  refine ⟨?_, ?_⟩
  · exact mir_fault_correspondence_transfer
      encodeProg faultToRefOutcome RefReachesOutcome hFaultCorr
      progUseAfterMoveUb { args := [u32Val 42] } 3 .undefined
      [⟨.byVal, u32Val 42⟩]
      (liftedPlanOrSkip progUseAfterMoveUb).1
      (liftedPlanOrSkip progUseAfterMoveUb).2
      ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      rfl
      rfl
  · exact mir_fault_correspondence_transfer
      encodeProg faultToRefOutcome RefReachesOutcome hFaultCorr
      progUseAfterStorageDeadUb queryEmpty 4 .undefined
      []
      (liftedPlanOrSkip progUseAfterStorageDeadUb).1
      (liftedPlanOrSkip progUseAfterStorageDeadUb).2
      ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      rfl
      rfl

/-- Standalone `PureLift` plan that borrows `local 1 = &mut local 0` (loan `0`),
ends loan `0`, and then attempts to read `*local 1`. -/
def mirDanglingRefPlan : FlowPlan Val :=
  .seq
    (.act (.assign (.localSub 0 []) (.constVal (mirU32Val 42))))
    (.seq
      (.act (.borrow 1 .mutBorrow (.localSub 0 [])))
      (.seq
        (.act (.endLoan 0))
        (.act (.assign (.localSub 2 []) (.use (.derefSub 1 []))))))

/-- Standalone `PureLift` plan that borrows `local 1 = &mut (*local 0)` (loan
`1`), overwrites `*local 0` while loan `1` is active, and then reads `*local 1`.
-/
def mirOverwriteWhileBorrowedPlan : FlowPlan Val :=
  .seq
    (.act (.borrow 1 .mutBorrow (.derefSub 0 [])))
    (.seq
      (.act (.assign (.derefSub 0 []) (.constVal (mirU32Val 99))))
      (.seq
        (.act (.assign (.localSub 2 []) (.use (.derefSub 1 []))))
        (.act (.endLoan 1))))

/-- Standalone `PureLift` borrow-discipline rejection canaries over `mirValAlg`
(independent of `Trusted.MirSemantics` entry execution). -/
theorem pure_lift_borrow_rejection_canaries :
    evalFnValue mirValAlg [] mirDanglingRefPlan (.use (.localSub 2 [])) =
      .fail ∧
    evalFnValue mirValAlg [⟨.mutRef 0 [], u32Val 42⟩]
      mirOverwriteWhileBorrowedPlan (.use (.localSub 2 [])) = .fail :=
  ⟨rfl, rfl⟩

/-! ### Workload W-5: Straight-Line `#[repr(u8)]` Fieldless Enum Constant and
`Rvalue.discriminant` Lifting + Invalid-Tag UB Rejection -/

/-- Computable `#[repr(u8)]` fieldless enum descriptor `{ A = 10, B = 20 }`. -/
def mirReprU8EnumTy : EnumTy where
  id := 101
  discrWidth := .i8
  discrSigned := false
  tagRepr := .scalar .i8 false
  discriminants := [10, 20]

/-- Computable `u8` type descriptor. -/
def mirU8Ty : MirTy := .int .i8 false

/-- Computable `u8` scalar constructor. -/
def mirU8Val (n : Nat) : Val :=
  .scalar ⟨.i8, false, BitVec.ofNat 128 n⟩

/-- Straight-line MIR program decoding `ReprU8::B` (`20u8`) via `ConstOperand`
and reading its `u8` discriminant into `_0` via `Rvalue.discriminant`. -/
def progEnumDiscriminantU8 : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "enum_discriminant_u8"
    argumentCount := 0
    locals := [mirU8Ty, .enum mirReprU8EnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩
          (.use (.constant
            ⟨.enum mirReprU8EnumTy, .scalar (BitVec.ofNat 128 20)⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

/-- Straight-line MIR program attempting to decode invalid tag `1u8` into
`ReprU8 { A = 10, B = 20 }`, triggering `FaultKind.undefined`. -/
def progEnumInvalidTagUb : Program where
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "enum_invalid_tag_ub"
    argumentCount := 0
    locals := [mirU8Ty, .enum mirReprU8EnumTy]
    basicBlocks := [{
      statements := [
        .storageLive 1,
        .assign ⟨1, []⟩
          (.use (.constant
            ⟨.enum mirReprU8EnumTy, .scalar (BitVec.ofNat 128 1)⟩)),
        .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩),
        .storageDead 1
      ]
      terminator := .return_
    }]
  }]

/-- End-to-end verification of `progEnumDiscriminantU8` (`20u8`) and coupled
fault transfer of `progEnumInvalidTagUb` (`FaultKind.undefined`) via
`liftStraightLineMir`. -/
theorem mir_enum_discriminant_lifted_verified
    {RefProg RefOutcome : Type}
    (encodeProg : Program → RefProg)
    (RefWellFormed : RefProg → Query → Prop)
    (RefBehavior : RefProg → Query → TerminalOut → Prop)
    (RefDiverges : RefProg → Query → Prop)
    (faultToRefOutcome : FaultKind → RefOutcome)
    (RefReachesOutcome : RefProg → Query → Nat → RefOutcome → Prop)
    (hCorr : MirCorrespondenceBridge encodeProg RefWellFormed RefBehavior
      RefDiverges)
    (hFaultCorr : MirFaultCorrespondenceBridge encodeProg faultToRefOutcome
      RefReachesOutcome) :
    let okLifted := liftedPlanOrSkip progEnumDiscriminantU8
    let ubLifted := liftedPlanOrSkip progEnumInvalidTagUb
    let post (out : FuncOut Val) : Prop := out = ⟨mirU8Val 20, []⟩
    (MirStraightLineLiftsTo progEnumDiscriminantU8 queryEmpty []
        okLifted.1 okLifted.2 ∧
      Exists fun out =>
        MirArgsMatch progEnumDiscriminantU8 queryEmpty [] ∧
        evalFnValue mirValAlg [] okLifted.1 okLifted.2 = .ok out ∧
        out.mutFinals = [] ∧
        post out ∧
        WellFormed progEnumDiscriminantU8 queryEmpty ∧
        Behavior progEnumDiscriminantU8 queryEmpty
          (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
        ¬ Diverges progEnumDiscriminantU8 queryEmpty ∧
        SatisfiesPost progEnumDiscriminantU8 queryEmpty
          (fun tOut => tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out) ∧
        RefWellFormed (encodeProg progEnumDiscriminantU8) queryEmpty ∧
        RefBehavior (encodeProg progEnumDiscriminantU8) queryEmpty
          (.returned ⟨out.ret, ⟨[]⟩⟩) ∧
        ¬ RefDiverges (encodeProg progEnumDiscriminantU8) queryEmpty ∧
        (∀ tOut,
          RefBehavior (encodeProg progEnumDiscriminantU8) queryEmpty tOut →
          tOut = .returned ⟨out.ret, ⟨[]⟩⟩ ∧ post out)) ∧
    (MirStraightLineLiftsTo progEnumInvalidTagUb queryEmpty []
        ubLifted.1 ubLifted.2 ∧
      (Exists fun s₀ => initState progEnumInvalidTagUb queryEmpty = .ok s₀) ∧
      (∀ pSpec,
        ¬ HoldsFnSpec
          (evalFnValue mirValAlg [] ubLifted.1 ubLifted.2) pSpec) ∧
      ReachesResult progEnumInvalidTagUb queryEmpty (.fault .undefined) ∧
      (∀ k : FaultKind, k ≠ .undefined →
        ¬ ReachesResult progEnumInvalidTagUb queryEmpty (.fault k)) ∧
      (∀ out : TerminalOut,
        ¬ Behavior progEnumInvalidTagUb queryEmpty out) ∧
      ¬ Diverges progEnumInvalidTagUb queryEmpty ∧
      ¬ WellFormed progEnumInvalidTagUb queryEmpty ∧
      (∃ maxSteps,
        RefReachesOutcome (encodeProg progEnumInvalidTagUb) queryEmpty
          maxSteps (faultToRefOutcome .undefined))) := by
  have hOkEval :
      evalFnValue mirValAlg []
        (liftedPlanOrSkip progEnumDiscriminantU8).1
        (liftedPlanOrSkip progEnumDiscriminantU8).2 =
      .ok ⟨mirU8Val 20, []⟩ := rfl
  refine ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, ?_⟩, ?_⟩
  · exact mir_pure_lift_correspondence_transfer
      encodeProg RefWellFormed RefBehavior RefDiverges hCorr
      progEnumDiscriminantU8 queryEmpty []
      (liftedPlanOrSkip progEnumDiscriminantU8).1
      (liftedPlanOrSkip progEnumDiscriminantU8).2
      (fun out => out = ⟨mirU8Val 20, []⟩)
      ⟨rfl, rfl, rfl, rfl, rfl⟩
      (by rw [hOkEval]; rfl)
      (by
        intro out hEv
        rw [hOkEval] at hEv
        injection hEv with hOut
        subst hOut
        exact ⟨5, rfl, rfl⟩)
  · exact mir_fault_correspondence_transfer
      encodeProg faultToRefOutcome RefReachesOutcome hFaultCorr
      progEnumInvalidTagUb queryEmpty 2 .undefined []
      (liftedPlanOrSkip progEnumInvalidTagUb).1
      (liftedPlanOrSkip progEnumInvalidTagUb).2
      ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      rfl
      rfl

end Anneal.PureLift
