import Toy.Obs.Defs
import Toy.Obs.Machines
import Toy.Obs.Examples

/-!
# Non-Vacuity Witnesses, Tightness Counterexamples, and Positive Controls

Every declaration in this module is fully proved without `sorry` and without
importing `Toy.Obs.Results`.
- Non-vacuity witnesses (`nv_*`) establish that concrete intended instances
  satisfy all hypotheses of each main result.
- Tightness counterexamples (`ce_*`) establish in canonical form that dropping
  any single `tight` hypothesis while keeping all other hypotheses allows the
  conclusion to fail.
- Positive controls (`pc_*`) establish that restoring the missing structural
  hypothesis eliminates the impossibility counterexample.
-/

namespace Toy.Obs

/-! ## Helper Lemmas for Concrete Machines -/

private theorem constFalse_beh (q : Unit) (w : List Unit) :
    constFalseMachine.beh q w = false := by
  induction w with
  | nil => rfl
  | cons _ w ih => exact ih

private theorem constTrue_beh (q : Unit) (w : List Unit) :
    constTrueMachine.beh q w = true := by
  induction w with
  | nil => rfl
  | cons _ w ih => exact ih

private theorem idBool_beh (b : Bool) (w : List Unit) :
    idBoolMachine.beh b w = b := by
  induction w with
  | nil => rfl
  | cons _ w ih => exact ih

private theorem redundantToggle_beh (b : Bool) (w : List Unit) :
    redundantToggleMachine.beh b w = false := by
  induction w generalizing b with
  | nil => rfl
  | cons _ w ih => exact ih (!b)

private theorem constFalse_allReachable : AllReachable constFalseMachine () :=
  fun _ => ⟨[], rfl⟩

private theorem constTrue_allReachable : AllReachable constTrueMachine () :=
  fun _ => ⟨[], rfl⟩

private theorem constFalse_behInjective : BehInjective constFalseMachine :=
  fun _ _ _ => rfl

private theorem constTrue_behInjective : BehInjective constTrueMachine :=
  fun _ _ _ => rfl

private theorem idBool_behInjective : BehInjective idBoolMachine := by
  intro q₁ q₂ h
  exact congrFun h []

private theorem dualToggle_allReachable : AllReachable dualToggleMachine true := by
  intro q
  cases q
  · exact ⟨[()], rfl⟩
  · exact ⟨[], rfl⟩

private theorem dualToggle_behInjective : BehInjective dualToggleMachine := by
  intro q₁ q₂ h
  have h0 := congrFun h []
  cases q₁ <;> cases q₂ <;> first | rfl | contradiction

private theorem redundantToggle_allReachable : AllReachable redundantToggleMachine false := by
  intro q
  cases q
  · exact ⟨[], rfl⟩
  · exact ⟨[()], rfl⟩

private theorem no_bijection_bool_unit (f : Bool → Unit) (g : Unit → Bool)
    (hleft : ∀ b, g (f b) = b) : False := by
  have hft : f false = f true := rfl
  have hEq : false = true := (hleft false).symm.trans ((congrArg g hft).trans (hleft true))
  contradiction

private theorem no_bijection_unit_bool (f : Unit → Bool) (g : Bool → Unit)
    (hright : ∀ b, f (g b) = b) : False := by
  have hft : g false = g true := rfl
  have hEq : false = true := (hright false).symm.trans ((congrArg f hft).trans (hright true))
  contradiction

/-! ## 1. Bisimulation Proof Principle (`bisim_subset_obsEq`, `obsEq_is_greatest_bisim`) -/

theorem nv_bisim_subset_obsEq :
    RelPreservesOut threeStateToggle threeStateBisimRel ∧
    RelStepClosed threeStateToggle threeStateBisimRel ∧
    threeStateBisimRel .s0 .s1 ∧
    ThreeState.s0 ≠ ThreeState.s1 :=
  ⟨ex_pos_isBisim.1.1, ex_pos_isBisim.1.2, ex_pos_isBisim.2, by decide⟩

theorem ce_bisim_subset_obsEq_no_out :
    RelStepClosed toggleMachine (fun _ _ => True) ∧
    ¬ (∀ q₁ q₂, (fun _ _ => True) q₁ q₂ → ObsEq toggleMachine q₁ q₂) := by
  refine ⟨fun _ _ _ _ => trivial, ?_⟩
  intro h
  have h01 := congrFun (h false true trivial) []
  contradiction

theorem ce_bisim_subset_obsEq_no_step :
    RelPreservesOut delayedDiffMachine
      (fun q₁ q₂ => delayedDiffMachine.out q₁ = delayedDiffMachine.out q₂) ∧
    ¬ (∀ q₁ q₂, delayedDiffMachine.out q₁ = delayedDiffMachine.out q₂ →
        ObsEq delayedDiffMachine q₁ q₂) := by
  refine ⟨ex_pos_relPreservesOut, ?_⟩
  intro h
  exact ex_neg_obsEq.2 (h .s0 .s1 rfl)

theorem nv_obsEq_is_greatest_bisim :
    ThreeState.s0 ≠ ThreeState.s1 ∧
    ObsEq threeStateToggle .s0 .s1 ∧
    ¬ ObsEq threeStateToggle .s0 .s2 := by
  refine ⟨ex_pos_obsEq.1, ex_pos_obsEq.2, ?_⟩
  intro h
  have h0 := congrFun h []
  contradiction

/-! ## 2. Finality (`hom_to_final_eq_beh`, `finalMachine_is_final`) -/

/-- Closed-form parity behavior map for `toggleMachine`: syntactically distinct
from `toggleMachine.beh`, so `nv_hom_to_final_eq_beh` exercises homomorphism
uniqueness rather than plugging in the right-hand side verbatim. -/
def toggleClosedForm : Bool → List Unit → Bool :=
  fun q w => if w.length % 2 = 0 then q else !q

theorem nv_hom_to_final_eq_beh :
    PreservesOut toggleMachine (finalMachine Unit Bool) toggleClosedForm ∧
    PreservesStep toggleMachine (finalMachine Unit Bool) toggleClosedForm := by
  refine ⟨fun q => by simp [toggleClosedForm, finalMachine, toggleMachine], ?_⟩
  intro q i
  funext w
  show toggleClosedForm (!q) w = toggleClosedForm q (i :: w)
  simp only [toggleClosedForm, List.length_cons]
  by_cases h : w.length % 2 = 0
  · have h1 : (w.length + 1) % 2 ≠ 0 := by omega
    simp [h, h1]
  · have h1 : (w.length + 1) % 2 = 0 := by omega
    simp [h, h1]

theorem ce_hom_to_final_no_out :
    PreservesStep constFalseMachine (finalMachine Unit Bool) (fun _ _ => true) ∧
    (fun _ _ => true) ≠ constFalseMachine.beh := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro h
  have h0 := congrFun (congrFun h ()) []
  contradiction

theorem ce_hom_to_final_no_step :
    PreservesOut toggleMachine (finalMachine Unit Bool) (fun q _ => q) ∧
    (fun q _ => q) ≠ toggleMachine.beh := by
  refine ⟨fun _ => rfl, ?_⟩
  intro h
  have h1 := congrFun (congrFun h false) [()]
  contradiction

theorem nv_finalMachine_is_final :
    toggleMachine.beh false ≠ toggleMachine.beh true := by
  intro h
  have h0 := congrFun h []
  contradiction

/-! ## 3. Minimality and Uniqueness (`minimalMachine_spec`, `reachable_maps_onto_minimalMachine`, `reachable_behInjective_iso`) -/

theorem nv_minimalMachine_spec :
    ¬ BehInjective threeStateToggle ∧
    threeStateToggle.beh .s0 [] = false ∧
    threeStateToggle.beh .s0 [()] = true := by
  refine ⟨?_, rfl, rfl⟩
  intro hInj
  exact ex_pos_obsEq.1 (hInj .s0 .s1 ex_pos_obsEq.2)

theorem nv_reachable_maps_onto_minimalMachine :
    AllReachable threeStateToggle .s0 ∧
    threeStateToggle.beh .s0 = toggleMachine.beh false := by
  refine ⟨ex_pos_threeStateToggle_allReachable, ?_⟩
  funext w
  exact threeStateToggle_beh_eq_toggle .s0 w

theorem ce_reachable_maps_onto_minimal_no_reach :
    idBoolMachine.beh false = constFalseMachine.beh () ∧
    ¬ ∃ φ : Bool → ReachableBeh constFalseMachine (),
        IsHom idBoolMachine (minimalMachine constFalseMachine ()) φ := by
  refine ⟨?_, ?_⟩
  · funext w
    rw [idBool_beh false w, constFalse_beh () w]
  · rintro ⟨φ, hOut, _⟩
    have hTrueOut : (φ true).1 [] = true := hOut true
    rcases (φ true).2 with ⟨w, hw⟩
    have hVal : (φ true).1 [] = false := by
      rw [← hw, Moore.beh_run, constFalse_beh ()]
    rw [hVal] at hTrueOut
    contradiction

theorem ce_reachable_maps_onto_minimal_no_initBeh :
    AllReachable constTrueMachine () ∧
    ¬ ∃ φ : Unit → ReachableBeh constFalseMachine (),
        IsHom constTrueMachine (minimalMachine constFalseMachine ()) φ := by
  refine ⟨constTrue_allReachable, ?_⟩
  rintro ⟨φ, hOut, _⟩
  have hTrueOut : (φ ()).1 [] = true := hOut ()
  rcases (φ ()).2 with ⟨w, hw⟩
  have hVal : (φ ()).1 [] = false := by
    rw [← hw, Moore.beh_run, constFalse_beh ()]
  rw [hVal] at hTrueOut
  contradiction

theorem nv_reachable_behInjective_iso :
    AllReachable toggleMachine false ∧
    AllReachable dualToggleMachine true ∧
    BehInjective toggleMachine ∧
    BehInjective dualToggleMachine ∧
    toggleMachine.beh false = dualToggleMachine.beh true := by
  refine ⟨ex_pos_allReachable, dualToggle_allReachable,
    ex_pos_behInjective, dualToggle_behInjective, ?_⟩
  funext w
  rw [dualToggleMachine_beh true w]
  rfl

theorem ce_minimal_iso_no_reach1 :
    AllReachable constFalseMachine () ∧
    BehInjective idBoolMachine ∧
    BehInjective constFalseMachine ∧
    idBoolMachine.beh false = constFalseMachine.beh () ∧
    ¬ ∃ (f : Bool → Unit) (g : Unit → Bool),
        IsIso idBoolMachine constFalseMachine f g := by
  refine ⟨constFalse_allReachable, idBool_behInjective, constFalse_behInjective, ?_, ?_⟩
  · funext w
    rw [idBool_beh false w, constFalse_beh () w]
  · rintro ⟨f, g, _, _, hleft, _⟩
    exact no_bijection_bool_unit f g hleft

theorem ce_minimal_iso_no_reach2 :
    AllReachable constFalseMachine () ∧
    BehInjective constFalseMachine ∧
    BehInjective idBoolMachine ∧
    constFalseMachine.beh () = idBoolMachine.beh false ∧
    ¬ ∃ (f : Unit → Bool) (g : Bool → Unit),
        IsIso constFalseMachine idBoolMachine f g := by
  refine ⟨constFalse_allReachable, constFalse_behInjective, idBool_behInjective, ?_, ?_⟩
  · funext w
    rw [constFalse_beh () w, idBool_beh false w]
  · rintro ⟨f, g, _, _, _, hright⟩
    exact no_bijection_unit_bool f g hright

theorem ce_minimal_iso_no_inj1 :
    AllReachable redundantToggleMachine false ∧
    AllReachable constFalseMachine () ∧
    BehInjective constFalseMachine ∧
    redundantToggleMachine.beh false = constFalseMachine.beh () ∧
    ¬ ∃ (f : Bool → Unit) (g : Unit → Bool),
        IsIso redundantToggleMachine constFalseMachine f g := by
  refine ⟨redundantToggle_allReachable, constFalse_allReachable, constFalse_behInjective, ?_, ?_⟩
  · funext w
    rw [redundantToggle_beh false w, constFalse_beh () w]
  · rintro ⟨f, g, _, _, hleft, _⟩
    exact no_bijection_bool_unit f g hleft

theorem ce_minimal_iso_no_inj2 :
    AllReachable constFalseMachine () ∧
    AllReachable redundantToggleMachine false ∧
    BehInjective constFalseMachine ∧
    constFalseMachine.beh () = redundantToggleMachine.beh false ∧
    ¬ ∃ (f : Unit → Bool) (g : Bool → Unit),
        IsIso constFalseMachine redundantToggleMachine f g := by
  refine ⟨constFalse_allReachable, redundantToggle_allReachable, constFalse_behInjective, ?_, ?_⟩
  · funext w
    rw [constFalse_beh () w, redundantToggle_beh false w]
  · rintro ⟨f, g, _, _, _, hright⟩
    exact no_bijection_unit_bool f g hright

theorem ce_minimal_iso_no_initBeh :
    AllReachable constFalseMachine () ∧
    AllReachable constTrueMachine () ∧
    BehInjective constFalseMachine ∧
    BehInjective constTrueMachine ∧
    ¬ ∃ (f : Unit → Unit) (g : Unit → Unit),
        IsIso constFalseMachine constTrueMachine f g := by
  refine ⟨constFalse_allReachable, constTrue_allReachable,
    constFalse_behInjective, constTrue_behInjective, ?_⟩
  rintro ⟨f, _, ⟨hOut, _⟩, _, _, _⟩
  have h0 := hOut ()
  contradiction

/-- Exact characterization of when `toMinimalQuotient` is injective (backing
the boundary note on `reachable_maps_onto_minimalMachine`). -/
theorem toMinimalQuotient_injective_iff
    {I : Type v} {O : Type w} {Q : Type u₁} {Q' : Type u₂}
    (M : Moore I O Q) (q₀ : Q)
    (M' : Moore I O Q') (q₀' : Q')
    (hReach : AllReachable M' q₀')
    (hInitBeh : M'.beh q₀' = M.beh q₀) :
    (∀ x y, toMinimalQuotient M q₀ M' q₀' hReach hInitBeh x =
      toMinimalQuotient M q₀ M' q₀' hReach hInitBeh y → x = y) ↔
    BehInjective M' :=
  ⟨fun h x y hxy => h x y (Subtype.ext hxy),
   fun h x y hxy => h x y (congrArg Subtype.val hxy)⟩

/-- Boundary witness for `reachable_behInjective_iso`: dropping `AllReachable`
allows a counterexample (`ce_minimal_iso_no_reach1`), yet does not make every
non-all-reachable pair non-isomorphic (`idBoolMachine` at `false` is isomorphic
to itself via `id`). -/
theorem iso_without_reachability :
    ¬ AllReachable idBoolMachine false ∧
    BehInjective idBoolMachine ∧
    idBoolMachine.beh false = idBoolMachine.beh false ∧
    IsIso idBoolMachine idBoolMachine id id :=
  ⟨ex_neg_allReachable, idBool_behInjective, rfl,
   ⟨fun _ => rfl, fun _ _ => rfl⟩, ⟨fun _ => rfl, fun _ _ => rfl⟩,
   fun _ => rfl, fun _ => rfl⟩

/-! ## 4. Erasable Hidden State (`stepwise_nondependence_*`, `isBisim_sameFst_iff`, `redundantTagMachine_*`, `behIgnoresHidden_iff_stepwise_of_obsInjectiveFst`) -/

theorem not_stepFst_delayedChannel2 : ¬ StepFstIgnoresHidden delayedChannel2 := by
  intro h
  have h01 := h (false, false) false true ()
  injection h01 with _ h2
  contradiction

theorem nv_stepwise_nondependence_implies_behIgnoresHidden :
    OutIgnoresHidden syntacticIndependentMachine ∧
    StepFstIgnoresHidden syntacticIndependentMachine ∧
    OutIgnoresHidden emptyHiddenMachine ∧
    StepFstIgnoresHidden emptyHiddenMachine :=
  ⟨ex_pos_outIgnoresHidden, ex_pos_stepFstIgnoresHidden,
   (fun _ h₁ _ => nomatch h₁), (fun _ h₁ _ _ => nomatch h₁)⟩

theorem ce_stepwise_no_out :
    StepFstIgnoresHidden leakyOutMachine ∧
    ¬ BehIgnoresHidden leakyOutMachine := by
  refine ⟨fun _ _ _ _ => rfl, ?_⟩
  intro h
  have h01 := congrFun (h () false true) []
  contradiction

theorem ce_stepwise_no_stepFst :
    OutIgnoresHidden delayedChannel2 ∧
    ¬ BehIgnoresHidden delayedChannel2 :=
  ⟨fun _ _ _ => rfl, ex_neg_behIgnoresHidden⟩

theorem nv_stepwise_nondependence_preserves_beh :
    OutIgnoresHidden syntacticIndependentMachine ∧
    StepFstIgnoresHidden syntacticIndependentMachine :=
  ⟨ex_pos_outIgnoresHidden, ex_pos_stepFstIgnoresHidden⟩

theorem ce_stepwise_erase_no_out :
    StepFstIgnoresHidden leakyOutMachine ∧
    ¬ IsHom leakyOutMachine (eraseHidden leakyOutMachine false) Prod.fst ∧
    ¬ (∀ a h, (eraseHidden leakyOutMachine false).beh a = leakyOutMachine.beh (a, h)) ∧
    ¬ BehIgnoresHidden leakyOutMachine := by
  refine ⟨fun _ _ _ _ => rfl, ?_, ?_, ce_stepwise_no_out.2⟩
  · rintro ⟨hOut, _⟩
    have h1 := hOut ((), true)
    contradiction
  · intro h
    have h1 := congrFun (h () true) []
    contradiction

theorem ce_stepwise_erase_no_stepFst :
    OutIgnoresHidden delayedChannel2 ∧
    ¬ IsHom delayedChannel2 (eraseHidden delayedChannel2 false) Prod.fst ∧
    ¬ (∀ a h, (eraseHidden delayedChannel2 false).beh a = delayedChannel2.beh (a, h)) ∧
    ¬ BehIgnoresHidden delayedChannel2 := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ex_neg_behIgnoresHidden⟩
  · rintro ⟨_, hStep⟩
    have h1 := hStep ((false, false), true) ()
    injection h1 with _ hft
    contradiction
  · intro h
    exact ex_neg_eraseHidden (h (false, false) true)

theorem ce_erase_empty_hidden :
    OutIgnoresHidden emptyHiddenMachine ∧
    StepFstIgnoresHidden emptyHiddenMachine ∧
    BehIgnoresHidden emptyHiddenMachine ∧
    ¬ ∃ M' : Moore Unit Empty Unit, ∀ a h, M'.beh a = emptyHiddenMachine.beh (a, h) := by
  refine ⟨(fun _ h₁ _ => nomatch h₁), (fun _ h₁ _ _ => nomatch h₁),
    (fun _ h₁ _ => nomatch h₁), ?_⟩
  rintro ⟨M', _⟩
  exact nomatch M'.out ()

theorem nv_isBisim_sameFst_iff :
    IsBisim syntacticIndependentMachine SameFst ∧
    ¬ IsBisim redundantTagMachine SameFst := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨a₁, _⟩ ⟨a₂, _⟩ (hp : a₁ = a₂)
    cases hp
    rfl
  · rintro ⟨a₁, _⟩ ⟨a₂, _⟩ (hp : a₁ = a₂) _
    cases hp
    rfl
  · rintro ⟨_, hStep⟩
    have h01 := hStep ((false, false), false) ((false, false), true) rfl false
    change (true, false) = (true, true) at h01
    injection h01 with _ hft
    contradiction

theorem nv_redundantTagMachine_nontrivial :
    redundantTagMachine.beh ((false, false), false) [] = false ∧
    redundantTagMachine.beh ((false, false), false) [false] = true :=
  ⟨rfl, rfl⟩

/-- Boundary witness for `redundantTagMachine_erasable_despite_step_dependence`:
while `Prod.fst` fails to be a homomorphism onto any machine on `A`, another
homomorphism `((x, _t), _h) ↦ (x, false)` onto `eraseHidden redundantTagMachine false`
does exist. -/
theorem redundantTag_has_other_hom :
    IsHom redundantTagMachine (eraseHidden redundantTagMachine false)
      (fun p => (p.1.1, false)) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem nv_behIgnoresHidden_iff_stepwise_of_obsInjectiveFst :
    ObsInjectiveFst syntacticIndependentMachine ∧
    BehIgnoresHidden syntacticIndependentMachine ∧
    ObsInjectiveFst delayedChannel2 ∧
    ¬ StepFstIgnoresHidden delayedChannel2 :=
  ⟨ex_pos_obsInjectiveFst, ex_pos_behIgnoresHidden,
   ex_pos_obsInjectiveFst_delayedChannel2, not_stepFst_delayedChannel2⟩

theorem ce_stepwise_iff_no_obsInjectiveFst :
    ¬ ObsInjectiveFst redundantTagMachine ∧
    ¬ (BehIgnoresHidden redundantTagMachine ↔
        OutIgnoresHidden redundantTagMachine ∧ StepFstIgnoresHidden redundantTagMachine) := by
  refine ⟨ex_neg_obsInjectiveFst, ?_⟩
  intro hIff
  have hBeh : BehIgnoresHidden redundantTagMachine := by
    intro ⟨x, t⟩ h₁ h₂
    funext w
    rw [redundantTag_beh x t h₁ w, redundantTag_beh x t h₂ w]
  exact ex_neg_stepFstIgnoresHidden (hIff.mp hBeh).2

/-! ## 5. Hidden Channel Past One Step and Unwinding Criteria -/

theorem nv_no_leak_under_stepwise_nondependence :
    (OutIgnoresHidden syntacticIndependentMachine ∧
      StepFstIgnoresHidden syntacticIndependentMachine) ∧
    (OutIgnoresHidden delayedChannel2 ∧ ¬ BehIgnoresHidden delayedChannel2) :=
  ⟨⟨ex_pos_outIgnoresHidden, ex_pos_stepFstIgnoresHidden⟩,
   ⟨fun _ _ _ => rfl, ex_neg_behIgnoresHidden⟩⟩

/-- Positive control for `no_leak_under_stepwise_nondependence`: dropping
`StepFstIgnoresHidden` while keeping `OutIgnoresHidden` (and even
`OneStepOutIgnoresHidden`) allows hidden state to leak into `beh`. -/
theorem pc_leak_when_stepFst_dropped :
    OutIgnoresHidden delayedChannel2 ∧
    OneStepOutIgnoresHidden delayedChannel2 ∧
    ¬ StepFstIgnoresHidden delayedChannel2 ∧
    ¬ BehIgnoresHidden delayedChannel2 :=
  ⟨fun _ _ _ => rfl, ex_pos_oneStepOutIgnoresHidden,
   not_stepFst_delayedChannel2, ex_neg_behIgnoresHidden⟩

theorem nv_delayedChannel2_nontrivial :
    delayedChannel2.beh ((true, false), false) [] = true ∧
    delayedChannel2.beh ((true, false), false) [()] = false :=
  ⟨rfl, rfl⟩

/-- Boundary witness for uniform vs. per-`h` erasure: for each fixed hidden bit
`h`, `eraseHidden delayedChannel2 h` reproduces `delayedChannel2.beh (a, h)` for
every `a`, even though no single machine on `A` works uniformly for both `h`. -/
theorem delayedChannel2_erasable_for_each_fixed_h (h : Bool) :
    ∃ M' : Moore Unit Bool (Bool × Bool),
      ∀ a, M'.beh a = delayedChannel2.beh (a, h) := by
  refine ⟨eraseHidden delayedChannel2 h, ?_⟩
  intro a
  funext w
  induction w generalizing a with
  | nil => rfl
  | cons _ w ih => exact ih (a.2, h)

/-- Boundary witness for global vs. reachable erasability: in `gatedLeak`,
every state reachable from `(false, h)` keeps `a = false` and `beh (false, h)`
is independent of `h`, yet global `BehIgnoresHidden` fails at `a = true`. -/
theorem gatedLeak_reachable_erasable_but_not_global :
    (∀ h q, Reachable gatedLeak (false, h) q → q.1 = false) ∧
    (∀ h₁ h₂, gatedLeak.beh (false, h₁) = gatedLeak.beh (false, h₂)) ∧
    ¬ BehIgnoresHidden gatedLeak := by
  have hrun : ∀ (p : Bool × Bool) (u : List Unit), gatedLeak.run p u = p := by
    intro p u
    induction u with
    | nil => rfl
    | cons _ u ih => exact ih
  refine ⟨?_, ?_, ?_⟩
  · intro h q ⟨w, hw⟩
    rw [hrun (false, h) w] at hw
    rw [← hw]
  · intro h₁ h₂
    funext w
    show gatedLeak.out (gatedLeak.run (false, h₁) w) = gatedLeak.out (gatedLeak.run (false, h₂) w)
    rw [hrun, hrun]
    rfl
  · intro h
    have h0 := congrFun (h true false true) []
    contradiction

theorem nv_no_machine_independent_horizon :
    BoundedBehIgnoresHidden (delayedChannel 3) 5 ∧
    (delayedChannel 3).beh (fun _ => false, false) [(), (), (), (), ()] ≠
      (delayedChannel 3).beh (fun _ => false, true) [(), (), (), (), ()] := by
  refine ⟨?_, by decide⟩
  intro a h₁ h₂ w hlen
  rw [delayedChannel_beh_formula, delayedChannel_beh_formula]
  split
  · rfl
  · omega

/-- Primary positive control for `no_machine_independent_horizon_certifies_behIgnoresHidden`:
allowing the horizon to depend on the machine (`k + 3` for `delayedChannel k`)
detects the leak for every `k`. -/
theorem pc_machine_dependent_horizon_detects_leak (k : Nat) :
    ¬ BoundedBehIgnoresHidden (delayedChannel k) (k + 3) := by
  intro hBound
  have hEq := hBound (fun _ => false) false true (List.replicate (k + 2) ()) (by simp)
  have hNotLt : ¬ ((List.replicate (k + 2) ()).length < k + 2) := by simp
  rw [delayedChannel_beh_formula, delayedChannel_beh_formula] at hEq
  split at hEq
  · exact hNotLt ‹_›
  · exact Bool.noConfusion hEq

private theorem delayedChannelFixed_run_formula (k : Nat)
    (reg : Fin (k + 2) → Bool) (h : Bool) (w : List Unit) :
    ∀ j : Fin (k + 2),
      ((delayedChannelFixed k).run (reg, h) w).1 j =
        if hlt : j.val + w.length < k + 2 then reg ⟨j.val + w.length, hlt⟩ else false := by
  induction w generalizing reg with
  | nil =>
    intro j
    simp
  | cons _ w ih =>
    let reg' : Fin (k + 2) → Bool :=
      fun j => if hlt : j.val + 1 < k + 2 then reg ⟨j.val + 1, hlt⟩ else false
    intro j
    change ((delayedChannelFixed k).run (reg', h) w).1 j = _
    rw [ih reg' j]
    simp only [List.length_cons]
    split
    · dsimp only [reg']
      split <;> split
      · congr 1
      · omega
      · omega
      · rfl
    · split
      · omega
      · rfl

private theorem eraseHidden_delayedChannelFixed_run_formula (k : Nat) (h₀ : Bool)
    (reg : Fin (k + 2) → Bool) (w : List Unit) :
    ∀ j : Fin (k + 2),
      ((eraseHidden (delayedChannelFixed k) h₀).run reg w) j =
        if hlt : j.val + w.length < k + 2 then reg ⟨j.val + w.length, hlt⟩ else false := by
  induction w generalizing reg with
  | nil =>
    intro j
    simp
  | cons _ w ih =>
    let reg' : Fin (k + 2) → Bool :=
      fun j => if hlt : j.val + 1 < k + 2 then reg ⟨j.val + 1, hlt⟩ else false
    intro j
    change ((eraseHidden (delayedChannelFixed k) h₀).run reg' w) j = _
    rw [ih reg' j]
    simp only [List.length_cons]
    split
    · dsimp only [reg']
      split <;> split
      · congr 1
      · omega
      · omega
      · rfl
    · split
      · omega
      · rfl

/-- Companion positive control for
`no_machine_independent_horizon_certifies_behIgnoresHidden`: replacing the
hidden feed into slot `k + 1` with the constant `false` in
`delayedChannelFixed k` restores `StepFstIgnoresHidden`, and `BehIgnoresHidden`
plus global erasure via `eraseHidden` then hold for all word lengths. -/
theorem pc_bounded_horizon_with_step_consistency (k : Nat) :
    OutIgnoresHidden (delayedChannelFixed k) ∧
    OneStepOutIgnoresHidden (delayedChannelFixed k) ∧
    StepFstIgnoresHidden (delayedChannelFixed k) ∧
    BehIgnoresHidden (delayedChannelFixed k) ∧
    (∀ h₀ a h, (eraseHidden (delayedChannelFixed k) h₀).beh a =
      (delayedChannelFixed k).beh (a, h)) := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_, ?_⟩
  · intro a h₁ h₂
    funext w
    change ((delayedChannelFixed k).run (a, h₁) w).1 ⟨0, Nat.zero_lt_succ _⟩ =
      ((delayedChannelFixed k).run (a, h₂) w).1 ⟨0, Nat.zero_lt_succ _⟩
    rw [delayedChannelFixed_run_formula k a h₁ w, delayedChannelFixed_run_formula k a h₂ w]
  · intro h₀ a h
    funext w
    change ((eraseHidden (delayedChannelFixed k) h₀).run a w) ⟨0, Nat.zero_lt_succ _⟩ =
      ((delayedChannelFixed k).run (a, h) w).1 ⟨0, Nat.zero_lt_succ _⟩
    rw [eraseHidden_delayedChannelFixed_run_formula k h₀ a w,
      delayedChannelFixed_run_formula k a h w]

theorem nv_behIgnoresHidden_iff_erasable :
    BehIgnoresHidden redundantTagMachine ∧
    ¬ StepFstIgnoresHidden redundantTagMachine := by
  refine ⟨?_, ex_neg_stepFstIgnoresHidden⟩
  intro ⟨x, t⟩ h₁ h₂
  funext w
  rw [redundantTag_beh x t h₁ w, redundantTag_beh x t h₂ w]

/-- Concrete unwinding bisimulation on `redundantTagMachine`: relates states
with the same observable toggling bit `x`, ignoring both the redundant tag
bit `t` and the hidden bit `h`. -/
def redundantTagUnwindingRel (p₁ p₂ : (Bool × Bool) × Bool) : Prop :=
  p₁.1.1 = p₂.1.1

theorem nv_unwinding_bisim_implies_behIgnoresHidden :
    CoversHidden redundantTagUnwindingRel ∧
    RelPreservesOut redundantTagMachine redundantTagUnwindingRel ∧
    RelStepClosed redundantTagMachine redundantTagUnwindingRel ∧
    ¬ StepFstIgnoresHidden redundantTagMachine := by
  refine ⟨fun _ _ _ => rfl, fun _ _ h => h, ?_, ex_neg_stepFstIgnoresHidden⟩
  intro p₁ p₂ h _
  exact congrArg Bool.not h

theorem ce_unwinding_no_coversHidden :
    RelPreservesOut leakyOutMachine Eq ∧
    RelStepClosed leakyOutMachine Eq ∧
    ¬ BehIgnoresHidden leakyOutMachine :=
  ⟨fun _ _ h => congrArg leakyOutMachine.out h,
   fun _ _ h i => congrArg (fun p => leakyOutMachine.step p i) h,
   ce_stepwise_no_out.2⟩

theorem ce_unwinding_no_out :
    CoversHidden (fun _ _ : Unit × Bool => True) ∧
    RelStepClosed leakyOutMachine (fun _ _ => True) ∧
    ¬ BehIgnoresHidden leakyOutMachine :=
  ⟨fun _ _ _ => trivial, fun _ _ _ _ => trivial, ce_stepwise_no_out.2⟩

theorem ce_unwinding_no_step :
    CoversHidden (SameFst : ((Bool × Bool) × Bool) → ((Bool × Bool) × Bool) → Prop) ∧
    RelPreservesOut delayedChannel2 SameFst ∧
    ¬ BehIgnoresHidden delayedChannel2 :=
  ⟨fun _ _ _ => rfl, fun _ _ h => congrArg Prod.fst h, ex_neg_behIgnoresHidden⟩

theorem nv_behIgnoresHidden_iff_exists_unwinding_bisim :
    (∃ R : ((Bool × Bool) × Bool) → ((Bool × Bool) × Bool) → Prop,
      CoversHidden R ∧
      RelPreservesOut redundantTagMachine R ∧
      RelStepClosed redundantTagMachine R) ∧
    ¬ StepFstIgnoresHidden redundantTagMachine :=
  ⟨⟨redundantTagUnwindingRel,
    nv_unwinding_bisim_implies_behIgnoresHidden.1,
    nv_unwinding_bisim_implies_behIgnoresHidden.2.1,
    nv_unwinding_bisim_implies_behIgnoresHidden.2.2.1⟩,
   ex_neg_stepFstIgnoresHidden⟩

end Toy.Obs
