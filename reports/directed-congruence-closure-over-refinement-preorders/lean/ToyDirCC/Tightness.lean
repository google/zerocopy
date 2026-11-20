import ToyDirCC.Necessity
import ToyDirCC.Extract

/-!
# Tightness of the hypotheses of the checker and extraction results

Hypotheses of `check_sound`, `check_sound_of_admissible`,
`extract_refines_of_chosenOriented_mono`, `extract_refines_of_oriented_mono` and
`extract_total_and_sound_of_wfBelow_oriented_mono`. Each theorem states, for one hypothesis,
a concrete instance in which **all other hypotheses hold and the conclusion fails**.
-/

namespace Toy.DirCC

/-! ## `check_sound` -/

/-- The empty relation on `Unit`. -/
abbrev emptyRelModel : Model UOp where
  C := Unit
  le _ _ := False
  interp _ _ := ()

/-- `check_sound` needs `LeRefl`: with the empty relation, `refl x₀` is accepted and
`x₀ ≤ x₀` is false; transitivity holds vacuously, the all-opaque profile imposes nothing,
and the empty fact list holds. -/
theorem check_sound_needs_refl :
    LeTrans emptyRelModel ∧ MonoAt (allOpaque UOp) emptyRelModel ∧
    KerAt (allOpaque UOp) emptyRelModel ∧ FactsHold emptyRelModel (fun _ => ()) [] ∧
    check Policy.standard (allOpaque UOp) [] (.refl (.var 0)) (.var 0) (.var 0) = true ∧
    ¬ emptyRelModel.le (eval emptyRelModel (fun _ => ()) (.var 0))
      (eval emptyRelModel (fun _ => ()) (.var 0)) :=
  ⟨fun _ _ _ h _ => h, monoAt_allOpaque _, kerAt_allOpaque _, fun _ _ h => by simp at h,
    by decide, id⟩

/-- `check_sound` needs `LeTrans`: with "differs by at most one" on `Nat` and `xᵢ ↦ i`, the
facts `x₀ ≤ x₁`, `x₁ ≤ x₂` hold, their chain is accepted, and `x₀ ≤ x₂` is false. -/
theorem check_sound_needs_trans :
    LeRefl natNearModel ∧ MonoAt (allOpaque UOp) natNearModel ∧
    KerAt (allOpaque UOp) natNearModel ∧
    FactsHold natNearModel (fun n => n) [(.var 0, .var 1), (.var 1, .var 2)] ∧
    check Policy.standard (allOpaque UOp) [(.var 0, .var 1), (.var 1, .var 2)]
      (.trans (.fact 0) (.fact 1)) (.var 0) (.var 2) = true ∧
    ¬ natNearModel.le (eval natNearModel (fun n => n) (.var 0))
      (eval natNearModel (fun n => n) (.var 2)) := by
  refine ⟨fun x => ⟨Nat.le_succ x, Nat.le_succ x⟩, monoAt_allOpaque _, kerAt_allOpaque _, ?_,
    by decide, by decide⟩
  intro s t h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- `check_sound` needs `MonoAt`: declaring every position of the outcome model `mono`
(false for `pickMin`), the one-sided congruence certificate for `pickMin x₀ ≤ pickMin x₁`
is accepted, all other hypotheses hold, and the conclusion is false. -/
theorem check_sound_needs_monoAt :
    LeRefl oModel ∧ LeTrans oModel ∧ KerAt (allMono OOp) oModel ∧
    FactsHold oModel oVal [(.var 0, .var 1)] ∧
    check Policy.standard (allMono OOp) [(.var 0, .var 1)] (.cong .pickMin [] [] (.fact 0))
      (.app .pickMin [.var 0]) (.app .pickMin [.var 1]) = true ∧
    ¬ oModel.le (eval oModel oVal (.app .pickMin [.var 0]))
      (eval oModel oVal (.app .pickMin [.var 1])) := by
  refine ⟨oModel_refl, oModel_trans, kerAt_allMono _, ?_, by decide, by decide⟩
  intro s t h
  simp only [List.mem_singleton, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  decide

/-- `MonoAt` transfers to a profile with fewer `mono` positions. -/
theorem monoAt_of_mono_imp {Op : Type} {P P' : Profile Op} {M : Model Op}
    (h : ∀ f i, P' f i = .mono → P f i = .mono) (hM : MonoAt P M) : MonoAt P' M :=
  fun f pre post x y hP hxy => hM f pre post x y (h _ _ hP) hxy

theorem oModel_monoAt_oProfileEq : MonoAt oProfileEq oModel := by
  refine monoAt_of_mono_imp (fun f i h => ?_) oModel_monoAt
  cases f <;> cases i <;> simp_all [oProfile, oProfileEq]

/-- `check_sound` needs `KerAt`: declaring `pickFirst`'s argument `eqOnly` (false), the
two-sided congruence certificate for `pickFirst x₀ ≤ pickFirst x₂` is accepted, all other
hypotheses hold, and the conclusion is false. -/
theorem check_sound_needs_kerAt :
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfileEq oModel ∧
    FactsHold oModel oVal [(.var 0, .var 2), (.var 2, .var 0)] ∧
    check Policy.standard oProfileEq [(.var 0, .var 2), (.var 2, .var 0)]
      (.congEq .pickFirst [] [] (.fact 0) (.fact 1))
      (.app .pickFirst [.var 0]) (.app .pickFirst [.var 2]) = true ∧
    ¬ oModel.le (eval oModel oVal (.app .pickFirst [.var 0]))
      (eval oModel oVal (.app .pickFirst [.var 2])) := by
  refine ⟨oModel_refl, oModel_trans, oModel_monoAt_oProfileEq, ?_, by decide, by decide⟩
  intro s t h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Valuation `x₀ ↦ [0]`, `x₁ ↦ [1]`. -/
def oVal01 : Nat → List Nat := fun n => [[0], [1]].getD n []

/-- `check_sound` needs `FactsHold`: with the false fact `x₀ ≤ x₁` (`[1]` does not refine
`[0]`), the certificate `fact 0` is accepted and the conclusion is false. -/
theorem check_sound_needs_factsHold :
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧
    ¬ FactsHold oModel oVal01 [(.var 0, .var 1)] ∧
    check Policy.standard oProfile [(.var 0, .var 1)] (.fact 0) (.var 0) (.var 1) = true ∧
    ¬ oModel.le (eval oModel oVal01 (.var 0)) (eval oModel oVal01 (.var 1)) :=
  ⟨oModel_refl, oModel_trans, oModel_monoAt, oModel_kerAt,
    fun h => absurd (h (.var 0) (.var 1) (by simp)) (by decide), by decide, by decide⟩

/-- `check_sound` needs acceptance: all laws and (empty) facts hold, the certificate
`refl x₀` is rejected for the claim `x₀ ≤ x₁`, and the claim is false. -/
theorem check_sound_needs_check :
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧
    FactsHold oModel oVal01 [] ∧
    check Policy.standard oProfile [] (.refl (.var 0)) (.var 0) (.var 1) = false ∧
    ¬ oModel.le (eval oModel oVal01 (.var 0)) (eval oModel oVal01 (.var 1)) :=
  ⟨oModel_refl, oModel_trans, oModel_monoAt, oModel_kerAt, fun _ _ h => by simp at h,
    by decide, by decide⟩

/-! ## `check_sound_of_admissible` -/

/-- `check_sound_of_admissible` needs `AdmissibleFor`: the permissive policy (one-sided
congruence everywhere) is not admissible for `oProfile`; all other hypotheses hold, the
permissive checker accepts `pickMin x₀ ≤ pickMin x₁` from `x₀ ≤ x₁`, and the conclusion is
false. -/
theorem check_sound_of_admissible_needs_admissible :
    ¬ Policy.permissive.AdmissibleFor oProfile ∧
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧
    FactsHold oModel oVal [(.var 0, .var 1)] ∧
    check Policy.permissive oProfile [(.var 0, .var 1)] (.cong .pickMin [] [] (.fact 0))
      (.app .pickMin [.var 0]) (.app .pickMin [.var 1]) = true ∧
    ¬ oModel.le (eval oModel oVal (.app .pickMin [.var 0]))
      (eval oModel oVal (.app .pickMin [.var 1])) := by
  obtain ⟨hR, hT, hM, hK, hF, hcPerm, _, hbad⟩ := pickMin_monoCong_counterexample
  refine ⟨fun h => ?_, hR, hT, hM, hK, hF, hcPerm, hbad⟩
  have := h.1 .pickMin 0 rfl
  simp [oProfile] at this

/-- `check_sound_of_admissible` needs `LeRefl` (instance of `check_sound_needs_refl` with
the standard policy, which is admissible for every profile). -/
theorem check_sound_of_admissible_needs_refl :
    Policy.standard.AdmissibleFor (allOpaque UOp) ∧
    LeTrans emptyRelModel ∧ MonoAt (allOpaque UOp) emptyRelModel ∧
    KerAt (allOpaque UOp) emptyRelModel ∧ FactsHold emptyRelModel (fun _ => ()) [] ∧
    check Policy.standard (allOpaque UOp) [] (.refl (.var 0)) (.var 0) (.var 0) = true ∧
    ¬ emptyRelModel.le (eval emptyRelModel (fun _ => ()) (.var 0))
      (eval emptyRelModel (fun _ => ()) (.var 0)) :=
  ⟨Policy.standard_admissibleFor _, check_sound_needs_refl⟩

/-- `check_sound_of_admissible` needs `LeTrans`. -/
theorem check_sound_of_admissible_needs_trans :
    Policy.standard.AdmissibleFor (allOpaque UOp) ∧
    LeRefl natNearModel ∧ MonoAt (allOpaque UOp) natNearModel ∧
    KerAt (allOpaque UOp) natNearModel ∧
    FactsHold natNearModel (fun n => n) [(.var 0, .var 1), (.var 1, .var 2)] ∧
    check Policy.standard (allOpaque UOp) [(.var 0, .var 1), (.var 1, .var 2)]
      (.trans (.fact 0) (.fact 1)) (.var 0) (.var 2) = true ∧
    ¬ natNearModel.le (eval natNearModel (fun n => n) (.var 0))
      (eval natNearModel (fun n => n) (.var 2)) :=
  ⟨Policy.standard_admissibleFor _, check_sound_needs_trans⟩

/-- `check_sound_of_admissible` needs `MonoAt`. -/
theorem check_sound_of_admissible_needs_monoAt :
    Policy.standard.AdmissibleFor (allMono OOp) ∧
    LeRefl oModel ∧ LeTrans oModel ∧ KerAt (allMono OOp) oModel ∧
    FactsHold oModel oVal [(.var 0, .var 1)] ∧
    check Policy.standard (allMono OOp) [(.var 0, .var 1)] (.cong .pickMin [] [] (.fact 0))
      (.app .pickMin [.var 0]) (.app .pickMin [.var 1]) = true ∧
    ¬ oModel.le (eval oModel oVal (.app .pickMin [.var 0]))
      (eval oModel oVal (.app .pickMin [.var 1])) :=
  ⟨Policy.standard_admissibleFor _, check_sound_needs_monoAt⟩

/-- `check_sound_of_admissible` needs `KerAt`. -/
theorem check_sound_of_admissible_needs_kerAt :
    Policy.standard.AdmissibleFor oProfileEq ∧
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfileEq oModel ∧
    FactsHold oModel oVal [(.var 0, .var 2), (.var 2, .var 0)] ∧
    check Policy.standard oProfileEq [(.var 0, .var 2), (.var 2, .var 0)]
      (.congEq .pickFirst [] [] (.fact 0) (.fact 1))
      (.app .pickFirst [.var 0]) (.app .pickFirst [.var 2]) = true ∧
    ¬ oModel.le (eval oModel oVal (.app .pickFirst [.var 0]))
      (eval oModel oVal (.app .pickFirst [.var 2])) :=
  ⟨Policy.standard_admissibleFor _, check_sound_needs_kerAt⟩

/-- `check_sound_of_admissible` needs `FactsHold`. -/
theorem check_sound_of_admissible_needs_factsHold :
    Policy.standard.AdmissibleFor oProfile ∧
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧
    ¬ FactsHold oModel oVal01 [(.var 0, .var 1)] ∧
    check Policy.standard oProfile [(.var 0, .var 1)] (.fact 0) (.var 0) (.var 1) = true ∧
    ¬ oModel.le (eval oModel oVal01 (.var 0)) (eval oModel oVal01 (.var 1)) :=
  ⟨Policy.standard_admissibleFor _, check_sound_needs_factsHold⟩

/-- `check_sound_of_admissible` needs acceptance. -/
theorem check_sound_of_admissible_needs_check :
    Policy.standard.AdmissibleFor oProfile ∧
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧
    FactsHold oModel oVal01 [] ∧
    check Policy.standard oProfile [] (.refl (.var 0)) (.var 0) (.var 1) = false ∧
    ¬ oModel.le (eval oModel oVal01 (.var 0)) (eval oModel oVal01 (.var 1)) :=
  ⟨Policy.standard_admissibleFor _, check_sound_needs_check⟩

/-! ## Extraction -/

theorem extract_chChoose_eq (fuel : Nat) (t : Term OOp) (h : extract chChoose fuel 0 = some t) :
    t = .app .choose [.app (.lit 0) [], .app (.lit 1) []] := by
  match fuel, h with
  | 0, h => simp [extract] at h
  | 1, h => simp [extract, chChoose, allSome] at h
  | n + 2, h =>
    simp [extract, chChoose, allSome] at h
    exact h.symm

theorem chLit_in_egOriented : ChoiceIn egOriented chLit := by
  intro c n h
  match c, h with
  | 0, h => simp [chLit] at h; subst h; simp [egOriented]
  | 1, h => simp [chLit] at h; subst h; simp [egOriented]
  | 2, h => simp [chLit] at h; subst h; simp [egOriented]
  | _ + 3, h => simp [chLit] at h

/-- Positive example (`ChosenOriented`); `extract_unoriented_counterexample` contains the
negative example `chChoose`. -/
theorem chLit_chosenOriented : ChosenOriented oModel (fun _ => []) denLit chLit :=
  chosenOriented_of_oriented egOriented_oriented chLit_in_egOriented

theorem chLit_chosenMono : ChosenMono oProfile chLit := by
  intro c f ks h i hi
  match c, h with
  | 0, h => simp [chLit] at h; obtain ⟨rfl, rfl⟩ := h; simp at hi
  | 1, h => simp [chLit] at h; obtain ⟨rfl, rfl⟩ := h; simp at hi
  | 2, h => simp [chLit] at h; obtain ⟨rfl, rfl⟩ := h; simp at hi
  | _ + 3, h => simp [chLit] at h

/-- Both extraction-soundness forms need the extraction hypothesis `extract ch fuel c =
some t`: with `egOriented` and `chLit` every other hypothesis of
`extract_refines_of_chosenOriented_mono` and of `extract_refines_of_oriented_mono` holds,
the term `lit 1` is not extracted from class 0 at any fuel, and it does not refine `[0]`. -/
theorem extract_needs_extract_some :
    LeTrans oModel ∧ MonoAt oProfile oModel ∧
    Oriented oModel (fun _ => []) egOriented denLit ∧ ChoiceIn egOriented chLit ∧
    ChosenOriented oModel (fun _ => []) denLit chLit ∧ ChosenMono oProfile chLit ∧
    (∀ fuel, extract chLit fuel 0 ≠ some (.app (.lit 1) [])) ∧
    ¬ oModel.le (denLit 0) (eval oModel (fun _ => []) (.app (.lit 1) [])) := by
  refine ⟨oModel_trans, oModel_monoAt, egOriented_oriented, chLit_in_egOriented,
    chLit_chosenOriented, chLit_chosenMono, fun fuel => ?_, by decide⟩
  cases fuel with
  | zero => simp [extract]
  | succ n => simp [extract, chLit, allSome]

/-- `extract_refines_of_oriented_mono` (and `chosenOriented_of_oriented`) needs `ChoiceIn`:
`egOriented` is oriented, but the choice picks `choose(1, 2)`, which is not in class 0; all
other hypotheses hold, the choice is not chosen-oriented, and the extracted `choose(0, 1)`
does not refine `[0]`. -/
theorem extract_needs_choiceIn :
    LeTrans oModel ∧ MonoAt oProfile oModel ∧
    Oriented oModel (fun _ => []) egOriented denLit ∧ ¬ ChoiceIn egOriented chChoose ∧
    ¬ ChosenOriented oModel (fun _ => []) denLit chChoose ∧
    ChosenMono oProfile chChoose ∧
    extract chChoose 2 0 = some (.app .choose [.app (.lit 0) [], .app (.lit 1) []]) ∧
    ¬ oModel.le (denLit 0)
      (eval oModel (fun _ => []) (.app .choose [.app (.lit 0) [], .app (.lit 1) []])) :=
  ⟨oModel_trans, oModel_monoAt, egOriented_oriented, chChoose_not_in_egOriented,
    fun h => absurd (h 0 _ rfl) (by decide), chChoose_chosenMono, extract_chChoose, by decide⟩

/-- `extract_refines_of_oriented_mono` needs `Oriented`: in `egUnoriented` the choice stays
inside the classes and descends through `mono` positions, all other hypotheses hold, the
e-graph is not oriented, and the extracted `choose(0, 1)` does not refine `[0]`. -/
theorem extract_oriented_needs_oriented :
    LeTrans oModel ∧ MonoAt oProfile oModel ∧
    ¬ Oriented oModel (fun _ => []) egUnoriented denLit ∧
    ChoiceIn egUnoriented chChoose ∧ ChosenMono oProfile chChoose ∧
    extract chChoose 2 0 = some (.app .choose [.app (.lit 0) [], .app (.lit 1) []]) ∧
    ¬ oModel.le (denLit 0)
      (eval oModel (fun _ => []) (.app .choose [.app (.lit 0) [], .app (.lit 1) []])) :=
  ⟨oModel_trans, oModel_monoAt, egUnoriented_not_oriented, chChoose_in_egUnoriented,
    chChoose_chosenMono, extract_chChoose, by decide⟩

/-- Class 0: `{pickMin(class 1)}`; class 1: `{x₀, x₁}`. -/
def egPick : EGraph OOp where
  nodes
    | 0 => [.app .pickMin [1]]
    | 1 => [.var 0, .var 1]
    | _ => []

/-- Class denotations: class 0 `↦ [0]` (`pickMin [0, 1]`), class 1 `↦ [0, 1]` (`x₀`). -/
def denPick : Nat → List Nat := fun c => [[0], [0, 1]].getD c []

theorem egPick_oriented : Oriented oModel oVal egPick denPick := by
  intro c n h
  match c, h with
  | 0, h => simp [egPick] at h; subst h; decide
  | 1, h => simp [egPick] at h; rcases h with rfl | rfl <;> decide
  | _ + 2, h => simp [egPick] at h

theorem chPick_in_egPick : ChoiceIn egPick chPick := by
  intro c n h
  match c, h with
  | 0, h => simp [chPick] at h; subst h; simp [egPick]
  | 1, h => simp [chPick] at h; subst h; simp [egPick]
  | _ + 2, h => simp [chPick] at h

theorem extract_chPick : extract chPick 2 0 = some (.app .pickMin [.var 1]) := by decide

theorem chPick_chosenOriented : ChosenOriented oModel oVal denPick chPick :=
  chosenOriented_of_oriented egPick_oriented chPick_in_egPick

/-- Both extraction-soundness forms need `ChosenMono`: the choice descends through `pickMin`
(declared `eqOnly`) into class 1, picking `x₁ = [1]`, which refines `x₀ = [0, 1]`; the
e-graph is oriented, the choice stays inside it (hence is chosen-oriented), every other
hypothesis holds, and the extracted `pickMin x₁ = [1]` does not refine class 0's denotation
`[0]`. -/
theorem extract_needs_chosenMono :
    LeTrans oModel ∧ MonoAt oProfile oModel ∧
    Oriented oModel oVal egPick denPick ∧ ChoiceIn egPick chPick ∧
    ChosenOriented oModel oVal denPick chPick ∧
    ¬ ChosenMono oProfile chPick ∧
    extract chPick 2 0 = some (.app .pickMin [.var 1]) ∧
    ¬ oModel.le (denPick 0) (eval oModel oVal (.app .pickMin [.var 1])) :=
  ⟨oModel_trans, oModel_monoAt, egPick_oriented, chPick_in_egPick, chPick_chosenOriented,
    chPick_not_chosenMono, extract_chPick, by decide⟩

/-- Both extraction-soundness forms need `MonoAt`: with every position declared `mono`
(so `ChosenMono` holds) the outcome model is not monotone for `pickMin`; the e-graph is
oriented, the choice stays inside it, all other hypotheses hold and the conclusion fails. -/
theorem extract_needs_monoAt :
    LeTrans oModel ∧ ¬ MonoAt (allMono OOp) oModel ∧
    Oriented oModel oVal egPick denPick ∧ ChoiceIn egPick chPick ∧
    ChosenOriented oModel oVal denPick chPick ∧
    ChosenMono (allMono OOp) chPick ∧
    extract chPick 2 0 = some (.app .pickMin [.var 1]) ∧
    ¬ oModel.le (denPick 0) (eval oModel oVal (.app .pickMin [.var 1])) :=
  ⟨oModel_trans, oModel_not_monoAt_allMono, egPick_oriented, chPick_in_egPick,
    chPick_chosenOriented, fun _ _ _ _ _ _ => rfl, extract_chPick, by decide⟩

/-- Class 0: `{succ(class 1)}`; class 1: `{x₁}`. -/
def egSucc : EGraph UOp where
  nodes
    | 0 => [.app .succ [1]]
    | 1 => [.var 1]
    | _ => []

/-- The choice for `egSucc`. -/
def chSucc : Choice UOp
  | 0 => some (.app .succ [1])
  | 1 => some (.var 1)
  | _ => none

theorem natNearModel_monoAt_allMono : MonoAt (allMono UOp) natNearModel := by
  intro f pre post x y _ hxy
  cases f
  cases pre with
  | nil => simp only [List.nil_append, List.headD_cons]; exact ⟨by omega, by omega⟩
  | cons p _ => simp only [List.cons_append, List.headD_cons]; exact ⟨by omega, by omega⟩

/-- Both extraction-soundness forms need `LeTrans`: with "differs by at most one", class
denotations `1, 1` and `x₁ ↦ 2`, the e-graph is oriented (`1 ~ succ 1 = 2`, `1 ~ 2`), the
model is monotone for `succ`, and the extracted `succ x₁ = 3` is not within one of `1`. -/
theorem extract_needs_trans :
    ¬ LeTrans natNearModel ∧ MonoAt (allMono UOp) natNearModel ∧
    Oriented natNearModel (fun n => n + 1) egSucc (fun _ => 1) ∧
    ChoiceIn egSucc chSucc ∧ ChosenOriented natNearModel (fun n => n + 1) (fun _ => 1) chSucc ∧
    ChosenMono (allMono UOp) chSucc ∧
    extract chSucc 2 0 = some (.app .succ [.var 1]) ∧
    ¬ natNearModel.le 1 (eval natNearModel (fun n => n + 1) (.app .succ [.var 1])) := by
  have hO : Oriented natNearModel (fun n => n + 1) egSucc (fun _ => 1) := by
    intro c n h
    match c, h with
    | 0, h => simp [egSucc] at h; subst h; decide
    | 1, h => simp [egSucc] at h; subst h; decide
    | _ + 2, h => simp [egSucc] at h
  have hC : ChoiceIn egSucc chSucc := by
    intro c n h
    match c, h with
    | 0, h => simp [chSucc] at h; subst h; simp [egSucc]
    | 1, h => simp [chSucc] at h; subst h; simp [egSucc]
    | _ + 2, h => simp [chSucc] at h
  exact ⟨natNearModel_not_trans, natNearModel_monoAt_allMono, hO, hC,
    chosenOriented_of_oriented hO hC, fun _ _ _ _ _ _ => rfl, by decide, by decide⟩

theorem extract_chPick_eq (fuel : Nat) (t : Term OOp) (h : extract chPick fuel 0 = some t) :
    t = .app .pickMin [.var 1] := by
  match fuel, h with
  | 0, h => simp [extract] at h
  | 1, h => simp [extract, chPick, allSome] at h
  | n + 2, h =>
    simp [extract, chPick, allSome] at h
    exact h.symm

theorem extract_chSucc_eq (fuel : Nat) (t : Term UOp) (h : extract chSucc fuel 0 = some t) :
    t = .app .succ [.var 1] := by
  match fuel, h with
  | 0, h => simp [extract] at h
  | 1, h => simp [extract, chSucc, allSome] at h
  | n + 2, h =>
    simp [extract, chSucc, allSome] at h
    exact h.symm

theorem wfBelow_chChoose : WFBelow chChoose 0 :=
  .app (f := .choose) (ks := [1, 2]) rfl (fun k hk => by
    simp at hk
    rcases hk with rfl | rfl
    · exact .app (f := .lit 0) (ks := []) rfl (fun _ h => by simp at h)
    · exact .app (f := .lit 1) (ks := []) rfl (fun _ h => by simp at h))

theorem wfBelow_chPick : WFBelow chPick 0 :=
  .app (f := .pickMin) (ks := [1]) rfl (fun k hk => by
    simp at hk; subst hk; exact .var (x := 1) rfl)

theorem wfBelow_chSucc : WFBelow chSucc 0 :=
  .app (f := .succ) (ks := [1]) rfl (fun k hk => by
    simp at hk; subst hk; exact .var (x := 1) rfl)

/-- `extract_total_and_sound_of_wfBelow_oriented_mono` needs `ChosenOriented`: well-founded choice of
`choose(1, 2)` in the unoriented e-graph; all other hypotheses hold and no extraction
refines `[0]`. -/
theorem extractWF_needs_chosenOriented :
    LeTrans oModel ∧ MonoAt oProfile oModel ∧
    ¬ ChosenOriented oModel (fun _ => []) denLit chChoose ∧
    ChosenMono oProfile chChoose ∧ WFBelow chChoose 0 ∧
    ¬ ∃ fuel t, extract chChoose fuel 0 = some t ∧
      oModel.le (denLit 0) (eval oModel (fun _ => []) t) := by
  refine ⟨oModel_trans, oModel_monoAt, fun h => absurd (h 0 _ rfl) (by decide),
    chChoose_chosenMono, wfBelow_chChoose, ?_⟩
  rintro ⟨fuel, t, h, hle⟩
  rw [extract_chChoose_eq fuel t h] at hle
  exact absurd hle (by decide)

/-- `extract_total_and_sound_of_wfBelow_oriented_mono` needs `ChosenMono`. -/
theorem extractWF_needs_chosenMono :
    LeTrans oModel ∧ MonoAt oProfile oModel ∧ ChosenOriented oModel oVal denPick chPick ∧
    ¬ ChosenMono oProfile chPick ∧ WFBelow chPick 0 ∧
    ¬ ∃ fuel t, extract chPick fuel 0 = some t ∧ oModel.le (denPick 0) (eval oModel oVal t) := by
  refine ⟨oModel_trans, oModel_monoAt, chPick_chosenOriented, chPick_not_chosenMono,
    wfBelow_chPick, ?_⟩
  rintro ⟨fuel, t, h, hle⟩
  rw [extract_chPick_eq fuel t h] at hle
  exact absurd hle (by decide)

/-- `extract_total_and_sound_of_wfBelow_oriented_mono` needs `MonoAt`. -/
theorem extractWF_needs_monoAt :
    LeTrans oModel ∧ ¬ MonoAt (allMono OOp) oModel ∧ ChosenOriented oModel oVal denPick chPick ∧
    ChosenMono (allMono OOp) chPick ∧ WFBelow chPick 0 ∧
    ¬ ∃ fuel t, extract chPick fuel 0 = some t ∧ oModel.le (denPick 0) (eval oModel oVal t) := by
  refine ⟨oModel_trans, oModel_not_monoAt_allMono, chPick_chosenOriented,
    fun _ _ _ _ _ _ => rfl, wfBelow_chPick, ?_⟩
  rintro ⟨fuel, t, h, hle⟩
  rw [extract_chPick_eq fuel t h] at hle
  exact absurd hle (by decide)

/-- `extract_total_and_sound_of_wfBelow_oriented_mono` needs `LeTrans`. -/
theorem extractWF_needs_trans :
    ¬ LeTrans natNearModel ∧ MonoAt (allMono UOp) natNearModel ∧
    ChosenOriented natNearModel (fun n => n + 1) (fun _ => 1) chSucc ∧
    ChosenMono (allMono UOp) chSucc ∧ WFBelow chSucc 0 ∧
    ¬ ∃ fuel t, extract chSucc fuel 0 = some t ∧
      natNearModel.le 1 (eval natNearModel (fun n => n + 1) t) := by
  obtain ⟨h1, h2, _, _, h5, h6, _, _⟩ := extract_needs_trans
  refine ⟨h1, h2, h5, h6, wfBelow_chSucc, ?_⟩
  rintro ⟨fuel, t, h, hle⟩
  rw [extract_chSucc_eq fuel t h] at hle
  exact absurd hle (by decide)

/-- `extract_total_and_sound_of_wfBelow_oriented_mono` needs `WFBelow`: in the cyclic class all other
hypotheses hold and extraction never returns a term. -/
theorem extractWF_needs_wfBelow (ρ : Nat → List Nat) :
    LeTrans oModel ∧ MonoAt oProfile oModel ∧ ChosenOriented oModel ρ (fun _ => ρ 0) chCycle ∧
    ChosenMono oProfile chCycle ∧ ¬ WFBelow chCycle 0 ∧
    ¬ ∃ fuel t, extract chCycle fuel 0 = some t ∧ oModel.le (ρ 0) (eval oModel ρ t) := by
  obtain ⟨h1, h2, _, h4, _, _, h7, h8, h9, _⟩ := extract_cycle_counterexample ρ
  refine ⟨h1, h2, h4, h7, h8, ?_⟩
  rintro ⟨fuel, t, h, _⟩
  rw [h9 fuel] at h
  cases h

end Toy.DirCC
