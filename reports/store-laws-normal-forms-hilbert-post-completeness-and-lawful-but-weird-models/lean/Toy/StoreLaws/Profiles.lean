import Toy.StoreLaws.Models

/-!
# Store laws: law profiles of the concrete models

For each model of `Toy.StoreLaws.Models`, which of the four laws hold
strictly (as carrier equations) and which fail.  Positive facts are proved for
all `S`, `V` where they hold generically; failures are proved on a Boolean cell
(`S = Bool`) with Boolean results, by evaluating both sides at a concrete
initial state.
-/

namespace Toy.StoreLaws

section Lawful

variable {S H V : Type}

theorem valueOnly_lawful : Lawful (valueOnly S V) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem unitModel_lawful : Lawful (unitModel S) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem inertHidden_lawful : Lawful (inertHidden S H V) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

end Lawful

section WriteLog

theorem writeLog_getGet {S V : Type} : GetGet (writeLog S V) := fun _ => rfl

theorem writeLog_putGet {S V : Type} : PutGet (writeLog S V) := fun _ _ => rfl

theorem writeLog_not_getPut : ¬ GetPut (writeLog Bool Bool) := by
  intro h
  have := congrFun (h (logRet true)) false
  exact absurd this (by decide)

theorem writeLog_not_putPut : ¬ PutPut (writeLog Bool Bool) := by
  intro h
  have := congrFun (h true false (logRet true)) false
  exact absurd this (by decide)

end WriteLog

section ChangeLog

theorem changeLog_getGet {S V : Type} [DecidableEq S] : GetGet (changeLog S V) := fun _ => rfl

theorem changeLog_getPut {S V : Type} [DecidableEq S] : GetPut (changeLog S V) := by
  intro x
  funext s₀
  simp [changeLog]

theorem changeLog_putGet {S V : Type} [DecidableEq S] : PutGet (changeLog S V) :=
  fun _ _ => rfl

theorem changeLog_not_putPut : ¬ PutPut (changeLog Bool Bool) := by
  intro h
  have := congrFun (h true false (logRet true)) false
  exact absurd this (by decide)

end ChangeLog

section WritesIgnored

theorem writesIgnored_getGet {S V : Type} : GetGet (writesIgnored S V) := fun _ => rfl

theorem writesIgnored_getPut {S V : Type} : GetPut (writesIgnored S V) := fun _ => rfl

theorem writesIgnored_putPut {S V : Type} : PutPut (writesIgnored S V) := fun _ _ _ => rfl

theorem writesIgnored_not_putGet : ¬ PutGet (writesIgnored Bool Bool) := by
  intro h
  have := congrFun (h true (fun s => intendedRet s)) false
  exact absurd this (by decide)

end WritesIgnored

section DirtyBit

theorem dirtyBit_getGet {S V : Type} : GetGet (dirtyBit S V) := fun _ => rfl

theorem dirtyBit_putGet {S V : Type} : PutGet (dirtyBit S V) := fun _ _ => rfl

theorem dirtyBit_putPut {S V : Type} : PutPut (dirtyBit S V) := fun _ _ _ => rfl

theorem dirtyBit_not_getPut : ¬ GetPut (dirtyBit Bool Bool) := by
  intro h
  have := congrFun (h (pairRet true)) (false, false)
  exact absurd this (by decide)

end DirtyBit

section ReadToClear

theorem readToClear_getPut {S V : Type} (d : S) : GetPut (readToClear S V d) := fun _ => rfl

theorem readToClear_putPut {S V : Type} (d : S) : PutPut (readToClear S V d) :=
  fun _ _ _ => rfl

theorem readToClear_not_getGet : ¬ GetGet (readToClear Bool Bool false) := by
  intro h
  have := congrFun (h (fun _ s' => intendedRet s')) true
  exact absurd this (by decide)

theorem readToClear_not_putGet : ¬ PutGet (readToClear Bool Bool false) := by
  intro h
  have := congrFun (h true (fun s => intendedRet s)) false
  exact absurd this (by decide)

end ReadToClear

section FaultingCounter

theorem faultingCounter_putGet {S V : Type} : PutGet (faultingCounter S V) := fun _ _ => rfl

theorem faultingCounter_putPut {S V : Type} : PutPut (faultingCounter S V) :=
  fun _ _ _ => rfl

theorem faultingCounter_not_getGet : ¬ GetGet (faultingCounter Bool Bool) := by
  intro h
  have := congrFun (h (fun _ s' => faultingRet s')) false
  exact absurd this (by decide)

theorem faultingCounter_not_getPut : ¬ GetPut (faultingCounter Bool Bool) := by
  intro h
  have := congrFun (h (faultingRet true)) false
  exact absurd this (by decide)

end FaultingCounter

section ReadCounter

theorem readCounter_putPut {S V : Type} : PutPut (readCounter S V) := fun _ _ _ => rfl

theorem readCounter_not_getGet : ¬ GetGet (readCounter Bool Bool) := by
  intro h
  have := congrFun (h (fun _ s' => counterRet s')) false
  exact absurd this (by decide)

theorem readCounter_not_getPut : ¬ GetPut (readCounter Bool Bool) := by
  intro h
  have := congrFun (h (counterRet true)) false
  exact absurd this (by decide)

theorem readCounter_not_putGet : ¬ PutGet (readCounter Bool Bool) := by
  intro h
  have := congrFun (h true (fun s => counterRet s)) false
  exact absurd this (by decide)

end ReadCounter

section CoupledHidden

/-- The coupled hidden bit is compatible with all four laws strictly. -/
theorem coupledHidden_lawful {V : Type} : Lawful (coupledHidden V) := by
  refine ⟨fun _ => rfl, ?_, fun _ _ => rfl, ?_⟩
  · intro x; funext ⟨s, h⟩; cases s <;> cases h <;> rfl
  · intro s s' x; funext ⟨s₀, h⟩; cases s <;> cases s' <;> cases s₀ <;> cases h <;> rfl

end CoupledHidden

section FstVia

/-- Through the non-injective observation `Prod.fst`, `fstViaModel` satisfies
get–put and put–get but not get–get: observational satisfaction does not
inherit the entailment `getGet_of_getPut_of_putGet` of strict satisfaction. -/
theorem getGetVia_not_entailed_by_getPutVia_putGetVia :
    GetPutVia Prod.fst fstViaModel ∧ PutGetVia Prod.fst fstViaModel ∧
    ¬ GetGetVia Prod.fst fstViaModel := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    funext s
    cases s <;> rfl
  · intro t k
    rfl
  · intro h
    have := congrFun (h (fun _ s' => (fun _ => false, fun _ => s'))) false
    exact absurd this (by decide)

end FstVia

end Toy.StoreLaws
