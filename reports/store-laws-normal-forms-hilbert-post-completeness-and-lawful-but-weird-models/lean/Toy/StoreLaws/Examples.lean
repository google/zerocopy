import Toy.StoreLaws.Witnesses

/-!
# Store laws: positive and negative examples for the definitions

For each definition, intended instances it must admit and instances it must
reject, fully proved.
-/

namespace Toy.StoreLaws

open Prog

/-! ## `run`, `bind`, `canon`, `nf` -/

/-- `run`: writing `true` and then reading returns `true` and leaves `true`. -/
theorem ex_run : run (put true (get ret) : Prog Bool Bool) false = (true, true) := rfl

/-- `bind` substitutes at returns: `(get ret).bind (fun b => put b (ret b))`
is `get (fun s => put s (ret s))`. -/
theorem ex_bind :
    (get ret : Prog Bool Bool).bind (fun b => put b (ret b)) = get (fun s => put s (ret s)) :=
  rfl

/-- `nf` of a constant observation is the canonical program writing and
returning constants. -/
theorem ex_nf :
    nf (run (put true (ret false) : Prog Bool Bool)) = canon (fun _ => true) (fun _ => false) :=
  rfl

/-! ## `ObsEq` -/

theorem ex_obsEq_pos :
    ObsEq (put true (put false (ret true)) : Prog Bool Bool) (put false (ret true)) := rfl

theorem ex_obsEq_neg : ¬ ObsEq (ret true : Prog Bool Bool) (ret false) := by
  intro h
  exact absurd (congrFun h false) (by decide)

/-! ## The four laws and `Lawful` -/

theorem ex_getGet_pos : GetGet (intended Bool Bool) := intended_lawful.1
theorem ex_getGet_neg : ¬ GetGet (readToClear Bool Bool false) := readToClear_not_getGet

theorem ex_getPut_pos : GetPut (intended Bool Bool) := intended_lawful.2.1
theorem ex_getPut_neg : ¬ GetPut (dirtyBit Bool Bool) := dirtyBit_not_getPut

theorem ex_putGet_pos : PutGet (intended Bool Bool) := intended_lawful.2.2.1
theorem ex_putGet_neg : ¬ PutGet (writesIgnored Bool Bool) := writesIgnored_not_putGet

theorem ex_putPut_pos : PutPut (intended Bool Bool) := intended_lawful.2.2.2
theorem ex_putPut_neg : ¬ PutPut (changeLog Bool Bool) := changeLog_not_putPut

theorem ex_lawful_pos : Lawful (intended Bool Bool) ∧ Lawful (valueOnly Bool Bool) ∧
    Lawful (inertHidden Bool Bool Bool) :=
  ⟨intended_lawful, valueOnly_lawful, inertHidden_lawful⟩

theorem ex_lawful_neg : ¬ Lawful (writeLog Bool Bool) := fun h => writeLog_not_putPut h.2.2.2

/-! ## `SatisfiesAll`, `EntailsBool` -/

theorem ex_satisfiesAll_pos : SatisfiesAll (lawsExcept .putPut) (changeLog Bool Bool) := by
  intro l hl
  cases l with
  | getGet => exact changeLog_getGet
  | getPut => exact changeLog_getPut
  | putGet => exact changeLog_putGet
  | putPut => exact absurd rfl hl

theorem ex_satisfiesAll_neg : ¬ SatisfiesAll allLaws (changeLog Bool Bool) :=
  fun h => changeLog_not_putPut (h .putPut trivial)

theorem ex_entailsBool_pos : EntailsBool (fun l => l = .getPut ∨ l = .putGet) .getGet :=
  (entailsBool_iff _ _).2 (Or.inr ⟨rfl, Or.inl rfl, Or.inr rfl⟩)

theorem ex_entailsBool_neg : ¬ EntailsBool (lawsExcept .getPut) .getPut := by
  intro h
  rcases (entailsBool_iff _ _).1 h with h' | ⟨h', _⟩
  · exact h' rfl
  · cases h'

/-! ## Observational satisfaction -/

theorem ex_via_pos :
    GetPutVia dropLog (writeLog Bool Bool) ∧ PutPutVia dropLog (writeLog Bool Bool) :=
  ⟨writeLog_laws_via_dropLog.2.1, writeLog_laws_via_dropLog.2.2.2⟩

/-- Through the identity observation (which keeps the log), the write log
fails get–put and put–put. -/
theorem ex_via_neg :
    ¬ GetPutVia id (writeLog Bool Bool) ∧ ¬ PutPutVia id (writeLog Bool Bool) :=
  ⟨fun h => writeLog_not_getPut h, fun h => writeLog_not_putPut h⟩

theorem ex_getGetVia_neg : ¬ GetGetVia id (readToClear Bool Bool false) :=
  fun h => readToClear_not_getGet h

theorem ex_putGetVia_neg : ¬ PutGetVia id (writesIgnored Bool Bool) :=
  fun h => writesIgnored_not_putGet h

/-- A non-injective observation (`Prod.fst`) rejecting a model: `fstViaModel`
fails get–get through `Prod.fst`. -/
theorem ex_getGetVia_neg_fst : ¬ GetGetVia Prod.fst fstViaModel :=
  getGetVia_not_entailed_by_getPutVia_putGetVia.2.2

/-- A non-injective observation (`dropLog`) rejecting a model: a read-only
device with a log component (writes are dropped) fails put–get through
`dropLog`. -/
theorem ex_putGetVia_neg_dropLog :
    ¬ PutGetVia dropLog
      ({ get := fun k s => k s s, put := fun _ x => x } :
        Model Bool (Bool → Bool × Bool × List Bool)) := by
  intro h
  have := congrFun (h true (fun s => fun _ => (s, s, []))) false
  exact absurd this (by decide)

/-- Through the identity observation the `...Via` laws are the strict laws. -/
theorem ex_via_id_eq_strict (M : Model Bool Bool) :
    GetGetVia id M = GetGet M ∧ GetPutVia id M = GetPut M ∧
    PutGetVia id M = PutGet M ∧ PutPutVia id M = PutPut M :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## `Derivable`, `ExtDerivable` -/

theorem ex_derivable_pos :
    Derivable allLaws (put true (put false (ret ())) : Prog Bool Unit) (put false (ret ())) :=
  .putPut trivial true false (ret ())

theorem ex_derivable_neg : ¬ Derivable allLaws (ret true : Prog Bool Bool) (ret false) := by
  intro h
  exact absurd (congrFun h.run_eq false) (by decide)

theorem ex_extDerivable_pos :
    ExtDerivable (ret true : Prog Bool Bool) (ret false) (ret true) (ret false) :=
  ExtDerivable.base _ _

theorem ex_extDerivable_neg :
    ¬ ExtDerivable (ret true : Prog Bool Bool) (ret true) (ret true) (ret false) := by
  intro h
  have := h.run_eq_of (fun _ => rfl)
  exact absurd (congrFun this false) (by decide)

theorem ex_extDerivableNoSubst_pos :
    ExtDerivableNoSubst (ret true : Prog Bool Bool) (ret false) (ret true) (ret false) :=
  .base

theorem ex_extDerivableNoSubst_neg :
    ¬ ExtDerivableNoSubst (ret true : Prog Bool Bool) (ret false)
      (put true (ret true)) (put false (ret true)) :=
  extDerivableNoSubst_not_total.2

/-! ## `IsHom`, `Model.fromObs` -/

theorem ex_isHom_pos : IsHom (intended Bool Bool) intendedRet (fun o => o) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem ex_isHom_neg :
    ¬ IsHom (intended Bool Bool) intendedRet (fun _ => intendedRet true) := by
  intro ⟨hret, _, _⟩
  exact absurd (congrFun (hret false) false) (by decide)

/-- For the intended model, the comparison map is the identity. -/
theorem ex_fromObs_intended (o : Bool → Bool × Bool) :
    (intended Bool Bool).fromObs intendedRet o = o := rfl

end Toy.StoreLaws
