import ToyDirCC.Tightness
import ToyDirCC.DupTightness

/-!
# Non-vacuity: every main result's hypotheses hold together in an intended instance
-/

namespace Toy.DirCC

/-- Facts `x₀ ≤ x₁`, `x₀ ≤ x₂`, `x₂ ≤ x₀` (true under `oVal`). -/
def nvFacts : List (Term OOp × Term OOp) := [(.var 0, .var 1), (.var 0, .var 2), (.var 2, .var 0)]

/-- A certificate using `trans`, one-sided congruence under `choose` (both positions) and
two-sided congruence under `pickMin`. -/
def nvCert : Cert OOp :=
  .trans (.cong .choose [] [.var 0] (.congEq .pickMin [] [] (.fact 1) (.fact 2)))
    (.cong .choose [.app .pickMin [.var 2]] [] (.fact 0))

/-- Non-vacuity of `check_sound`: in the outcome model with `oProfile` all four laws hold,
the facts hold under `oVal`, and the checker accepts
`choose(pickMin x₀, x₀) ≤ choose(pickMin x₂, x₁)`. -/
theorem check_sound_nonvacuous :
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧
    FactsHold oModel oVal nvFacts ∧
    check Policy.standard oProfile nvFacts nvCert
      (.app .choose [.app .pickMin [.var 0], .var 0])
      (.app .choose [.app .pickMin [.var 2], .var 1]) = true := by
  refine ⟨oModel_refl, oModel_trans, oModel_monoAt, oModel_kerAt, ?_, by decide⟩
  intro s t h
  simp only [nvFacts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Non-vacuity of `check_sound_of_admissible`: the standard policy is admissible for
`oProfile`, and the instance of `check_sound_nonvacuous` satisfies every other
hypothesis. -/
theorem check_sound_of_admissible_nonvacuous :
    Policy.standard.AdmissibleFor oProfile ∧
    LeRefl oModel ∧ LeTrans oModel ∧ MonoAt oProfile oModel ∧ KerAt oProfile oModel ∧
    FactsHold oModel oVal nvFacts ∧
    check Policy.standard oProfile nvFacts nvCert
      (.app .choose [.app .pickMin [.var 0], .var 0])
      (.app .choose [.app .pickMin [.var 2], .var 1]) = true :=
  ⟨Policy.standard_admissibleFor _, check_sound_nonvacuous⟩

/-- Non-vacuity of `monoCong_refuted_at_nonMono`: `pickMin`'s argument is not `mono` in
`oProfile`. -/
theorem monoCong_refuted_nonvacuous : oProfile .pickMin ([] : List (Term OOp)).length ≠ .mono := by
  decide

/-- Non-vacuity of `eqCong_refuted_at_opaque`: `pickFirst`'s argument is `opaqueArg`. -/
theorem eqCong_refuted_nonvacuous :
    oProfile .pickFirst ([] : List (Term OOp)).length = .opaqueArg := rfl

/-- Non-vacuity of the positive controls: `choose`'s first argument is `mono`, `pickMin`'s
argument is not `opaqueArg`, and the outcome model satisfies `MonoAt` and `KerAt`. -/
theorem controls_nonvacuous :
    oProfile .choose ([] : List (Term OOp)).length = .mono ∧
    oProfile .pickMin ([] : List (Term OOp)).length ≠ .opaqueArg ∧
    MonoAt oProfile oModel ∧ KerAt oProfile oModel :=
  ⟨rfl, by decide, oModel_monoAt, oModel_kerAt⟩

/-- Both sides of `policySound_iff_admissibleFor` are inhabited: the standard policy is
admissible for `oProfile`, the permissive one is not. -/
theorem policySound_nonvacuous :
    Policy.standard.AdmissibleFor oProfile ∧ ¬ Policy.permissive.AdmissibleFor oProfile := by
  refine ⟨Policy.standard_admissibleFor _, fun h => ?_⟩
  have := h.1 .pickMin 0 rfl
  simp [oProfile] at this

/-- Class 0: `{choose(class 1, class 2)}`; class 1: `{0}`; class 2: `{2}`. -/
def egStrict : EGraph OOp where
  nodes
    | 0 => [.app .choose [1, 2]]
    | 1 => [litN 0]
    | 2 => [litN 2]
    | _ => []

/-- Class denotations `[0, 1, 2]`, `[0, 1]`, `[1, 2]`: each class's e-nodes strictly refine
its denotation. -/
def denStrict : Nat → List Nat := fun c => [[0, 1, 2], [0, 1], [1, 2]].getD c []

/-- The choice of the only e-node in each class of `egStrict`. -/
def chStrict : Choice OOp
  | 0 => some (.app .choose [1, 2])
  | 1 => some (litN 0)
  | 2 => some (litN 2)
  | _ => none

theorem egStrict_oriented : Oriented oModel (fun _ => []) egStrict denStrict := by
  intro c n h
  match c, h with
  | 0, h => simp [egStrict] at h; subst h; decide
  | 1, h => simp [egStrict] at h; subst h; decide
  | 2, h => simp [egStrict] at h; subst h; decide
  | _ + 3, h => simp [egStrict] at h

theorem chStrict_in_egStrict : ChoiceIn egStrict chStrict := by
  intro c n h
  match c, h with
  | 0, h => simp [chStrict] at h; subst h; simp [egStrict]
  | 1, h => simp [chStrict] at h; subst h; simp [egStrict]
  | 2, h => simp [chStrict] at h; subst h; simp [egStrict]
  | _ + 3, h => simp [chStrict] at h

theorem chStrict_chosenMono : ChosenMono oProfile chStrict := by
  intro c f ks h i hi
  match c, h with
  | 0, h => simp [chStrict] at h; obtain ⟨rfl, rfl⟩ := h; simp [oProfile]
  | 1, h => simp [chStrict] at h; obtain ⟨rfl, rfl⟩ := h; simp at hi
  | 2, h => simp [chStrict] at h; obtain ⟨rfl, rfl⟩ := h; simp at hi
  | _ + 3, h => simp [chStrict] at h

theorem wfBelow_chStrict : WFBelow chStrict 0 :=
  .app (f := .choose) (ks := [1, 2]) rfl (fun k hk => by
    simp at hk
    rcases hk with rfl | rfl
    · exact .app (f := .lit 0) (ks := []) rfl (fun _ h => by simp at h)
    · exact .app (f := .lit 2) (ks := []) rfl (fun _ h => by simp at h))

/-- Non-vacuity of `extract_refines_of_chosenOriented_mono` and of its e-graph form
`extract_refines_of_oriented_mono`, at depth two with a non-empty `mono` argument list: all
hypotheses of both theorems hold for `egStrict` and `chStrict`, extraction returns
`choose(0, 2)` (outcomes `[0, 2]`), which strictly refines class 0's denotation
`[0, 1, 2]`. -/
theorem extract_refines_nonvacuous :
    LeTrans oModel ∧ MonoAt oProfile oModel ∧
    Oriented oModel (fun _ => []) egStrict denStrict ∧ ChoiceIn egStrict chStrict ∧
    ChosenOriented oModel (fun _ => []) denStrict chStrict ∧
    ChosenMono oProfile chStrict ∧
    extract chStrict 2 0 = some (.app .choose [.app (.lit 0) [], .app (.lit 2) []]) ∧
    oModel.le (denStrict 0)
      (eval oModel (fun _ => []) (.app .choose [.app (.lit 0) [], .app (.lit 2) []])) ∧
    ¬ oModel.le
      (eval oModel (fun _ => []) (.app .choose [.app (.lit 0) [], .app (.lit 2) []]))
      (denStrict 0) :=
  ⟨oModel_trans, oModel_monoAt, egStrict_oriented, chStrict_in_egStrict,
    chosenOriented_of_oriented egStrict_oriented chStrict_in_egStrict, chStrict_chosenMono,
    by decide, by decide, by decide⟩

theorem chAcyclic_in_egCycle : ChoiceIn egCycle chAcyclic := by
  intro c n h
  match c, h with
  | 0, h => simp [chAcyclic] at h; subst h; simp [egCycle]
  | _ + 1, h => simp [chAcyclic] at h

theorem chAcyclic_chosenMono : ChosenMono oProfile chAcyclic := by
  intro c f ks h
  match c, h with
  | 0, h => simp [chAcyclic] at h
  | _ + 1, h => simp [chAcyclic] at h

/-- Non-vacuity of `extract_total_and_sound_of_wfBelow_oriented_mono`, in two instances:
(1) `egStrict` with `chStrict` (depth two, a `WFBelow.app` step, strict refinement);
(2) the *cyclic* class of `egCycle` with the acyclic choice `x₀` (cyclic e-classes are
allowed; only the choice must be well-founded). -/
theorem extract_wf_nonvacuous (ρ : Nat → List Nat) :
    (LeTrans oModel ∧ MonoAt oProfile oModel ∧
      ChosenOriented oModel (fun _ => []) denStrict chStrict ∧
      ChosenMono oProfile chStrict ∧ WFBelow chStrict 0) ∧
    (Oriented oModel ρ egCycle (fun _ => ρ 0) ∧ ChoiceIn egCycle chAcyclic ∧
      ChosenOriented oModel ρ (fun _ => ρ 0) chAcyclic ∧
      ChosenMono oProfile chAcyclic ∧ WFBelow chAcyclic 0 ∧
      extract chAcyclic 1 0 = some (.var 0)) := by
  obtain ⟨_, _, h3, _⟩ := extract_cycle_counterexample ρ
  exact ⟨⟨oModel_trans, oModel_monoAt,
      chosenOriented_of_oriented egStrict_oriented chStrict_in_egStrict, chStrict_chosenMono,
      wfBelow_chStrict⟩,
    ⟨h3, chAcyclic_in_egCycle, chosenOriented_of_oriented h3 chAcyclic_in_egCycle,
      chAcyclic_chosenMono, wfBelow_chAcyclic, rfl⟩⟩

end Toy.DirCC

namespace Toy.DirCC.Dup

/-- Non-vacuity of `hcSem_iff_tagSem_of_letFree_wellTagged`. -/
theorem hcSem_iff_tagSem_nonvacuous :
    LetFree dupProgTagged = true ∧ WellTagged dupProgTagged ∧
    LetFree dupProg = true ∧ WellTagged dupProg := by decide

/-- Non-vacuity of `tagSem_iff_indep_of_uniqueTags`. -/
theorem tagSem_iff_indep_nonvacuous : UniqueTags dupProgTagged ∧ UniqueTags letProg := by
  decide

/-- Non-vacuity of `hashcons_inline_sound_of_uniqueTags` and
`wellTagged_inline_of_uniqueTags`: the shared program has unique tags (and inlines to the
untagged duplicate, whose hash-consed table therefore represents it faithfully). -/
theorem hashcons_inline_sound_nonvacuous :
    UniqueTags letProg ∧ inline letProg = dupProg ∧ UniqueTags dupProgTagged := by decide

end Toy.DirCC.Dup
