import Toy.Obs.Defs
import Toy.Obs.Machines
import Toy.Obs.Examples

/-!
# Main Results

This module states the 18 main results of the package:
- Section 1 (`bisim_subset_obsEq`, `obsEq_is_greatest_bisim`): bisimulation
  soundness (unbundled) and observational equivalence as the greatest
  bisimulation.
- Section 2 (`hom_to_final_eq_beh`, `finalMachine_is_final`): homomorphism
  uniqueness into `finalMachine` (unbundled) and finality of `finalMachine`.
- Section 3 (`minimalMachine_spec`, `reachable_maps_onto_minimalMachine`,
  `reachable_behInjective_iso`): minimality, universal surjective quotient, and
  uniqueness up to canonical isomorphism of minimal realizations.
- Section 4 (`stepwise_nondependence_implies_behIgnoresHidden`,
  `stepwise_nondependence_preserves_beh`, `isBisim_sameFst_iff`,
  `redundantTagMachine_erasable_despite_step_dependence`,
  `behIgnoresHidden_iff_stepwise_of_obsInjectiveFst`): one-step extensional
  non-dependence, its equivalence to `SameFst` bisimulation, failure of its
  converse when `A` has observationally redundant states, and exactness when
  `A` is observationally injective (`ObsInjectiveFst`).
- Section 5 (`no_leak_under_stepwise_nondependence`,
  `delayedChannel2_leaks_at_step_two`,
  `no_machine_independent_horizon_certifies_behIgnoresHidden`,
  `behIgnoresHidden_iff_erasable`, `unwinding_bisim_implies_behIgnoresHidden`,
  `behIgnoresHidden_iff_exists_unwinding_bisim`): impossibility of hidden
  leaks under full stepwise non-dependence, multi-step channels defeating
  output-only and machine-independent bounded-horizon checks, exact uniform
  erasure via `eraseHidden`, and two-level deterministic nonleakage unwinding.
-/

namespace Toy.Obs

universe u u₁ u₂ v w

/-! ## Private Proof Helpers -/

private theorem hom_beh {I : Type v} {O : Type w} {Q₁ : Type u₁} {Q₂ : Type u₂}
    {M₁ : Moore I O Q₁} {M₂ : Moore I O Q₂}
    {f : Q₁ → Q₂} (hf : IsHom M₁ M₂ f) (q : Q₁) : M₂.beh (f q) = M₁.beh q := by
  funext x
  induction x generalizing q with
  | nil => exact hf.1 q
  | cons i x ih =>
    show M₂.beh (M₂.step (f q) i) x = M₁.beh (M₁.step q i) x
    rw [← hf.2 q i]
    exact ih (M₁.step q i)

private theorem minimal_run_val {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q₀ : Q) (s : ReachableBeh M q₀)
    (x : List I) : ((minimalMachine M q₀).run s x).1 = fun y => s.1 (x ++ y) := by
  induction x generalizing s with
  | nil => rfl
  | cons i x ih => exact ih _

private theorem minimal_beh {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q₀ : Q) (s : ReachableBeh M q₀) :
    (minimalMachine M q₀).beh s = s.1 := by
  funext x
  show ((minimalMachine M q₀).run s x).1 [] = s.1 x
  rw [minimal_run_val]
  show s.1 (x ++ []) = s.1 x
  rw [List.append_nil]

/-! ## 1. Bisimulation Proof Principle -/

/-- **Result 1a (Bisimulation soundness, unbundled).** Any state relation `R`
on a Moore machine `M` that preserves immediate outputs (`RelPreservesOut M R`)
and is closed under single-step transitions (`RelStepClosed M R`) is contained
in observational equivalence (`ObsEq M`). Unbundled soundness half of
`obsEq_is_greatest_bisim`, exposing the two hypotheses separately; `R` need not
be reflexive, symmetric, or transitive. -/
theorem bisim_subset_obsEq
    {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (R : Q → Q → Prop)
    (hOut : RelPreservesOut M R)
    (hStep : RelStepClosed M R) :
    ∀ q₁ q₂, R q₁ q₂ → ObsEq M q₁ q₂ := by
  intro q₁ q₂ hR
  funext x
  induction x generalizing q₁ q₂ with
  | nil => exact hOut q₁ q₂ hR
  | cons i x ih => exact ih _ _ (hStep q₁ q₂ hR i)

/-- **Result 1b (Observational equivalence is the greatest bisimulation).**
For every Moore machine `M`, observational equivalence `ObsEq M` is itself a
bisimulation and contains every bisimulation on `M`. -/
theorem obsEq_is_greatest_bisim
    {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) :
    IsBisim M (ObsEq M) ∧
    (∀ R : Q → Q → Prop, IsBisim M R → ∀ q₁ q₂, R q₁ q₂ → ObsEq M q₁ q₂) :=
  ⟨⟨fun _ _ h => congrFun h [], fun _ _ h i => funext fun x => congrFun h (i :: x)⟩,
   fun R hR => bisim_subset_obsEq M R hR.1 hR.2⟩

/-! ## 2. Finality of the Behavior Coalgebra -/

/-- **Result 2a (Uniqueness of homomorphisms into the final machine,
unbundled).** Any state map `h : Q → (List I → O)` into `finalMachine I O` that
preserves immediate outputs (`PreservesOut`) and commutes with transitions
(`PreservesStep`) is equal to `M.beh`. Unbundled uniqueness half of
`finalMachine_is_final`. -/
theorem hom_to_final_eq_beh
    {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (h : Q → (List I → O))
    (hOut : PreservesOut M (finalMachine I O) h)
    (hStep : PreservesStep M (finalMachine I O) h) :
    h = M.beh := by
  funext q x
  induction x generalizing q with
  | nil => exact hOut q
  | cons i x ih => exact (congrFun (hStep q i) x).symm.trans (ih (M.step q i))

/-- **Result 2b (Finality of `finalMachine`).** For every Moore machine `M`,
`M.beh` is a homomorphism `M → finalMachine I O`, and it is the unique
homomorphism from `M` into `finalMachine I O`. -/
theorem finalMachine_is_final
    {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) :
    IsHom M (finalMachine I O) M.beh ∧
    (∀ h : Q → (List I → O), IsHom M (finalMachine I O) h → h = M.beh) :=
  ⟨⟨fun _ => rfl, fun _ _ => rfl⟩, fun h hh => hom_to_final_eq_beh M h hh.1 hh.2⟩

/-! ## 3. Minimality and Uniqueness up to Isomorphism -/

/-- **Result 3a (Minimal realization properties).** For any Moore machine `M`
with an initial state `q₀`, the reachable behavior image
`(minimalMachine M q₀, minimalInit M q₀)` has the same initial behavior
`M.beh q₀`, is globally reachable from `minimalInit M q₀`, and is
behavior-injective. -/
theorem minimalMachine_spec
    {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q₀ : Q) :
    (minimalMachine M q₀).beh (minimalInit M q₀) = M.beh q₀ ∧
    AllReachable (minimalMachine M q₀) (minimalInit M q₀) ∧
    BehInjective (minimalMachine M q₀) := by
  refine ⟨minimal_beh M q₀ _, ?_, ?_⟩
  · rintro ⟨f, x, rfl⟩
    refine ⟨x, Subtype.ext ?_⟩
    rw [minimal_run_val]
    funext y
    exact (Moore.beh_run M q₀ x y).symm
  · intro s₁ s₂ h
    rw [minimal_beh, minimal_beh] at h
    exact Subtype.ext h

/-- **Result 3b (Universal quotient property of `minimalMachine`).** Every
all-reachable Moore machine `(M', q₀')` sharing the initial behavior
`M.beh q₀` maps onto `minimalMachine M q₀` by the explicit homomorphism
`toMinimalQuotient M q₀ M' q₀' hReach hInitBeh`, which preserves the initial
state, is surjective, and is the unique homomorphism
`M' → minimalMachine M q₀`. -/
theorem reachable_maps_onto_minimalMachine
    {I : Type v} {O : Type w} {Q : Type u₁} {Q' : Type u₂}
    (M : Moore I O Q) (q₀ : Q)
    (M' : Moore I O Q') (q₀' : Q')
    (hReach : AllReachable M' q₀')
    (hInitBeh : M'.beh q₀' = M.beh q₀) :
    let φ := toMinimalQuotient M q₀ M' q₀' hReach hInitBeh
    IsHom M' (minimalMachine M q₀) φ ∧
    PreservesInit q₀' (minimalInit M q₀) φ ∧
    Surjective φ ∧
    (∀ ψ : Q' → ReachableBeh M q₀, IsHom M' (minimalMachine M q₀) ψ → ψ = φ) := by
  intro φ
  refine ⟨⟨fun _ => rfl, fun _ _ => Subtype.ext rfl⟩, Subtype.ext hInitBeh, ?_, ?_⟩
  · rintro ⟨f, x, rfl⟩
    refine ⟨M'.run q₀' x, Subtype.ext ?_⟩
    funext y
    show M'.beh (M'.run q₀' x) y = M.beh (M.run q₀ x) y
    rw [Moore.beh_run, Moore.beh_run, hInitBeh]
  · intro ψ hψ
    funext q'
    apply Subtype.ext
    have h := hom_beh hψ q'
    rw [minimal_beh] at h
    exact h

/-- **Result 3c (Uniqueness of minimal realizations up to canonical
isomorphism).** Any two all-reachable, behavior-injective Moore machines
`(M₁, q₁)` and `(M₂, q₂)` with the same initial behavior are canonically
isomorphic via the exhibited pair
`(minimalIsoFun M₁ q₁ M₂ q₂ hReach₁, minimalIsoFun M₂ q₂ M₁ q₁ hReach₂)`,
which preserves initial states, maps `M₁.run q₁ w` to `M₂.run q₂ w` for
every word `w`, and is the unique homomorphism `M₁ → M₂`. -/
theorem reachable_behInjective_iso
    {I : Type v} {O : Type w} {Q₁ : Type u₁} {Q₂ : Type u₂}
    (M₁ : Moore I O Q₁) (q₁ : Q₁)
    (M₂ : Moore I O Q₂) (q₂ : Q₂)
    (hReach₁ : AllReachable M₁ q₁)
    (hReach₂ : AllReachable M₂ q₂)
    (hInj₁ : BehInjective M₁)
    (hInj₂ : BehInjective M₂)
    (hInitBeh : M₁.beh q₁ = M₂.beh q₂) :
    let f := minimalIsoFun M₁ q₁ M₂ q₂ hReach₁
    let g := minimalIsoFun M₂ q₂ M₁ q₁ hReach₂
    IsIso M₁ M₂ f g ∧
    PreservesInit q₁ q₂ f ∧
    PreservesInit q₂ q₁ g ∧
    (∀ w : List I, f (M₁.run q₁ w) = M₂.run q₂ w) ∧
    (∀ φ : Q₁ → Q₂, IsHom M₁ M₂ φ → φ = f) := by
  intro f g
  have hf : ∀ q, M₂.beh (f q) = M₁.beh q := by
    intro q
    have key : ∀ x, M₁.run q₁ x = q → M₂.beh (M₂.run q₂ x) = M₁.beh q := by
      intro x hx
      subst hx
      funext y
      rw [Moore.beh_run, Moore.beh_run, hInitBeh]
    exact key _ (Classical.choose_spec (hReach₁ q))
  have hg : ∀ q, M₁.beh (g q) = M₂.beh q := by
    intro q
    have key : ∀ x, M₂.run q₂ x = q → M₁.beh (M₁.run q₁ x) = M₂.beh q := by
      intro x hx
      subst hx
      funext y
      rw [Moore.beh_run, Moore.beh_run, hInitBeh]
    exact key _ (Classical.choose_spec (hReach₂ q))
  refine ⟨⟨⟨fun q => congrFun (hf q) [], fun q i => ?_⟩,
      ⟨fun q => congrFun (hg q) [], fun q i => ?_⟩,
      fun q => hInj₁ _ _ (by rw [hg, hf]), fun q => hInj₂ _ _ (by rw [hf, hg])⟩,
    hInj₂ _ _ (by rw [hf, hInitBeh]), hInj₁ _ _ (by rw [hg, hInitBeh]), ?_, ?_⟩
  · apply hInj₂
    rw [hf]
    funext y
    show M₁.beh q (i :: y) = M₂.beh (f q) (i :: y)
    rw [hf]
  · apply hInj₁
    rw [hg]
    funext y
    show M₂.beh q (i :: y) = M₁.beh (g q) (i :: y)
    rw [hg]
  · intro x
    apply hInj₂
    rw [hf]
    funext y
    rw [Moore.beh_run, Moore.beh_run, hInitBeh]
  · intro φ hφ
    funext q
    exact hInj₂ _ _ ((hom_beh hφ q).trans (hf q).symm)

/-! ## 4. Erasable Hidden State: Stepwise Sufficiency, `SameFst` Bridge, and Reduced-`A` Exactness -/

/-- **Result 4a-i (Stepwise non-dependence implies behavioral non-dependence,
inhabitant-free).** For any split-state Moore machine `M : Moore I O (A × H)`
(including when `H` is empty), one-step extensional non-dependence of `out`
(`OutIgnoresHidden M`) and of the `A`-component of `step`
(`StepFstIgnoresHidden M`) implies `BehIgnoresHidden M` (two-level
deterministic nonleakage of `H`). -/
theorem stepwise_nondependence_implies_behIgnoresHidden
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H))
    (hOut : OutIgnoresHidden M)
    (hStepFst : StepFstIgnoresHidden M) :
    BehIgnoresHidden M := by
  have hRun : ∀ w (a : A) (h₁ h₂ : H),
      (M.run (a, h₁) w).1 = (M.run (a, h₂) w).1 := by
    intro w
    induction w with
    | nil => intros; rfl
    | cons i w ih =>
      intro a h₁ h₂
      change (M.run ((M.step (a, h₁) i).1, (M.step (a, h₁) i).2) w).1 =
        (M.run ((M.step (a, h₂) i).1, (M.step (a, h₂) i).2) w).1
      rw [hStepFst a h₁ h₂ i]
      exact ih (M.step (a, h₂) i).1 (M.step (a, h₁) i).2 (M.step (a, h₂) i).2
  intro a h₁ h₂
  funext w
  show M.out ((M.run (a, h₁) w).1, (M.run (a, h₁) w).2) =
    M.out ((M.run (a, h₂) w).1, (M.run (a, h₂) w).2)
  rw [hRun w a h₁ h₂]
  exact hOut (M.run (a, h₂) w).1 (M.run (a, h₁) w).2 (M.run (a, h₂) w).2

/-- **Result 4a-ii (Stepwise non-dependence implies behavior-preserving
erasure).** For a split-state machine `M : Moore I O (A × H)` with a dummy
value `h₀ : H` (needed only to form `eraseHidden M h₀`), if `OutIgnoresHidden M`
and `StepFstIgnoresHidden M` hold, then `Prod.fst` is a homomorphism
`M → eraseHidden M h₀`, `eraseHidden M h₀` preserves behavior for all
`(a, h)`, `BehIgnoresHidden M` holds, and `eraseHidden M h₁` is independent
of the dummy value `h₁ : H`. -/
theorem stepwise_nondependence_preserves_beh
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) (h₀ : H)
    (hOut : OutIgnoresHidden M)
    (hStepFst : StepFstIgnoresHidden M) :
    IsHom M (eraseHidden M h₀) Prod.fst ∧
    (∀ a h, (eraseHidden M h₀).beh a = M.beh (a, h)) ∧
    BehIgnoresHidden M ∧
    (∀ h₁, eraseHidden M h₁ = eraseHidden M h₀) := by
  have hHom : IsHom M (eraseHidden M h₀) Prod.fst :=
    ⟨fun q => hOut q.1 h₀ q.2, fun q i => hStepFst q.1 q.2 h₀ i⟩
  have hBeh : ∀ a h, (eraseHidden M h₀).beh a = M.beh (a, h) :=
    fun a h => hom_beh hHom (a, h)
  refine ⟨hHom, hBeh, fun a h₁ h₂ => (hBeh a h₁).symm.trans (hBeh a h₂), ?_⟩
  intro h₁
  show Moore.mk _ _ = Moore.mk _ _
  congr 1
  · funext a i
    exact hStepFst a h₁ h₀ i
  · funext a
    exact hOut a h₁ h₀

/-- **Result 4a-iii (`SameFst` bisimulation characterization of stepwise
non-dependence).** The observable-projection relation `SameFst` on `A × H`
satisfies `CoversHidden SameFst`, and `SameFst` is a bisimulation on `M` if
and only if `OutIgnoresHidden M` and `StepFstIgnoresHidden M` both hold.
Formalizes that stepwise non-dependence is exactly unwinding with fixed
relation `R = SameFst`. -/
theorem isBisim_sameFst_iff
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) :
    CoversHidden (SameFst : (A × H) → (A × H) → Prop) ∧
    (IsBisim M SameFst ↔ OutIgnoresHidden M ∧ StepFstIgnoresHidden M) := by
  refine ⟨fun _ _ _ => rfl, ?_⟩
  constructor
  · rintro ⟨hO, hS⟩
    exact ⟨fun a h₁ h₂ => hO (a, h₁) (a, h₂) rfl,
      fun a h₁ h₂ i => hS (a, h₁) (a, h₂) rfl i⟩
  · rintro ⟨hO, hS⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨a₁, h₁⟩ ⟨a₂, h₂⟩ (hp : a₁ = a₂)
      cases hp
      exact hO a₁ h₁ h₂
    · rintro ⟨a₁, h₁⟩ ⟨a₂, h₂⟩ (hp : a₁ = a₂) i
      cases hp
      exact hS a₁ h₁ h₂ i

/-- **Result 4b (Converse of stepwise non-dependence fails when `A` has
observationally redundant states).** In `redundantTagMachine`,
`OutIgnoresHidden` holds, `H` actively influences the `A`-component of `step`
(failing `StepFstIgnoresHidden`, even on pairs of states reachable from
`((false, false), false)`), and `Prod.fst` is not a homomorphism to any
reduced machine on `A`; yet `BehIgnoresHidden` and global behavior-preserving
erasure via `eraseHidden` still hold for every `(a, h)` and every dummy `h₀`. -/
theorem redundantTagMachine_erasable_despite_step_dependence :
    OutIgnoresHidden redundantTagMachine ∧
    ¬ StepFstIgnoresHidden redundantTagMachine ∧
    BehIgnoresHidden redundantTagMachine ∧
    (∀ h₀ a h, (eraseHidden redundantTagMachine h₀).beh a = redundantTagMachine.beh (a, h)) ∧
    (¬ ∃ M' : Moore Bool Bool (Bool × Bool), IsHom redundantTagMachine M' Prod.fst) ∧
    (∃ a h₁ h₂ i,
      Reachable redundantTagMachine ((false, false), false) (a, h₁) ∧
      Reachable redundantTagMachine ((false, false), false) (a, h₂) ∧
      (redundantTagMachine.step (a, h₁) i).1 ≠ (redundantTagMachine.step (a, h₂) i).1) := by
  refine ⟨?_, ex_neg_stepFstIgnoresHidden, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    rfl
  · intro ⟨x, t⟩ h₁ h₂
    funext w
    rw [redundantTag_beh x t h₁ w, redundantTag_beh x t h₂ w]
  · intro h₀ ⟨x, t⟩ h
    funext w
    rw [eraseHidden_redundantTag_beh h₀ x t w, redundantTag_beh x t h w]
  · rintro ⟨M', _, hStep⟩
    have h1 := hStep ((false, false), false) false
    have h2 := hStep ((false, false), true) false
    have hEq : (true, false) = (true, true) := h1.trans h2.symm
    injection hEq with _ hft
    contradiction
  · refine ⟨(false, false), false, true, false,
      ⟨[false, false], rfl⟩, ⟨[false, true], rfl⟩, ?_⟩
    intro hEq
    injection hEq with _ hft
    contradiction

/-- **Result 4c (Exactness of stepwise non-dependence when `A` is
observationally reduced).** When the observable component `A` has no
observationally equivalent distinct states at any hidden state
(`ObsInjectiveFst M`), behavioral non-dependence (`BehIgnoresHidden M`) is
equivalent to the per-step pair `OutIgnoresHidden M ∧ StepFstIgnoresHidden M`.
Thus the converse failure in `redundantTagMachine_erasable_despite_step_dependence`
arises only when `A` itself carries observationally redundant states. -/
theorem behIgnoresHidden_iff_stepwise_of_obsInjectiveFst
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H))
    (hInjA : ObsInjectiveFst M) :
    BehIgnoresHidden M ↔ OutIgnoresHidden M ∧ StepFstIgnoresHidden M := by
  constructor
  · intro hBeh
    refine ⟨fun a h₁ h₂ => congrFun (hBeh a h₁ h₂) [], ?_⟩
    intro a h₁ h₂ i
    have hSucc : M.beh (M.step (a, h₁) i) = M.beh (M.step (a, h₂) i) := by
      funext w
      exact congrFun (hBeh a h₁ h₂) (i :: w)
    have hAlign : M.beh ((M.step (a, h₂) i).1, (M.step (a, h₂) i).2) =
        M.beh ((M.step (a, h₂) i).1, (M.step (a, h₁) i).2) :=
      hBeh (M.step (a, h₂) i).1 (M.step (a, h₂) i).2 (M.step (a, h₁) i).2
    exact hInjA (M.step (a, h₁) i).1 (M.step (a, h₂) i).1 (M.step (a, h₁) i).2
      (hSucc.trans hAlign)
  · rintro ⟨hOut, hStepFst⟩
    exact stepwise_nondependence_implies_behIgnoresHidden M hOut hStepFst

/-! ## 5. Hidden Channels Past One Step and Exact / Unwinding Criteria -/

/-- **Result 5a-0 (No hidden leak under full stepwise non-dependence).** No
Moore machine `M : Moore I O (A × H)` can satisfy both `OutIgnoresHidden M`
and `StepFstIgnoresHidden M` while failing `BehIgnoresHidden M`. Consequently,
every multi-step hidden-channel machine necessarily violates
`StepFstIgnoresHidden`; what fails are checks on the output alone at any
machine-independent depth, or checks that `H` is never written. -/
theorem no_leak_under_stepwise_nondependence
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂} :
    ¬ ∃ M : Moore I O (A × H),
      OutIgnoresHidden M ∧ StepFstIgnoresHidden M ∧ ¬ BehIgnoresHidden M :=
  fun ⟨M, hOut, hStepFst, hNotBeh⟩ =>
    hNotBeh (stepwise_nondependence_implies_behIgnoresHidden M hOut hStepFst)

/-- **Result 5a-i (Two-step hidden channel defeating output-only checks).** In
`delayedChannel2`, `out` ignores `H` (`OutIgnoresHidden`), 1-step `out`
ignores `H` (`OneStepOutIgnoresHidden`), `BoundedBehIgnoresHidden` holds for
length `< 2`, `eraseHidden` agrees with `delayedChannel2` on all words of
length `< 2`, and `H` is read-only (`step.2 = h`), while
`StepFstIgnoresHidden` fails because `H` flows into `A` at step 1 and surfaces
at `out` after two steps `[(), ()]`, refuting `BehIgnoresHidden` and uniform
global erasure on `Bool × Bool`. -/
theorem delayedChannel2_leaks_at_step_two :
    OutIgnoresHidden delayedChannel2 ∧
    OneStepOutIgnoresHidden delayedChannel2 ∧
    ¬ StepFstIgnoresHidden delayedChannel2 ∧
    BoundedBehIgnoresHidden delayedChannel2 2 ∧
    (∀ h₀ a h w, w.length < 2 →
      (eraseHidden delayedChannel2 h₀).beh a w = delayedChannel2.beh (a, h) w) ∧
    (∀ a h i, (delayedChannel2.step (a, h) i).2 = h) ∧
    ¬ BehIgnoresHidden delayedChannel2 ∧
    (¬ ∃ M' : Moore Unit Bool (Bool × Bool),
      ∀ a h, M'.beh a = delayedChannel2.beh (a, h)) ∧
    delayedChannel2.beh ((false, false), false) [(), ()] ≠
      delayedChannel2.beh ((false, false), true) [(), ()] := by
  refine ⟨fun _ _ _ => rfl, ex_pos_oneStepOutIgnoresHidden, ?_,
    ex_pos_boundedBehIgnoresHidden, ?_, fun _ _ _ => rfl,
    ex_neg_behIgnoresHidden, ?_, by decide⟩
  · intro hStepFst
    have h01 := hStepFst (false, false) false true ()
    injection h01 with _ hft
    contradiction
  · intro h₀ a h w hlen
    match w with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ =>
      simp only [List.length_cons] at hlen
      omega
  · rintro ⟨M', hM'⟩
    have hEq : delayedChannel2.beh ((false, false), false) =
        delayedChannel2.beh ((false, false), true) :=
      (hM' (false, false) false).symm.trans (hM' (false, false) true)
    have h2 := congrFun hEq [(), ()]
    contradiction

/-- **Result 5a-ii (No machine-independent bounded horizon certifies
`BehIgnoresHidden`).** For every `k : Nat`, the `(k + 2)`-slot shift register
`delayedChannel k` passes `OutIgnoresHidden`, `OneStepOutIgnoresHidden`,
`BoundedBehIgnoresHidden (k + 2)`, and agreement with `eraseHidden` on all
words of length `< k + 2`, while failing `StepFstIgnoresHidden`, failing
`BehIgnoresHidden` at length `k + 2`, and admitting no uniform reduced machine
on `Fin (k + 2) → Bool`. -/
theorem no_machine_independent_horizon_certifies_behIgnoresHidden (k : Nat) :
    OutIgnoresHidden (delayedChannel k) ∧
    OneStepOutIgnoresHidden (delayedChannel k) ∧
    ¬ StepFstIgnoresHidden (delayedChannel k) ∧
    BoundedBehIgnoresHidden (delayedChannel k) (k + 2) ∧
    (∀ h₀ a h w, w.length < k + 2 →
      (eraseHidden (delayedChannel k) h₀).beh a w = (delayedChannel k).beh (a, h) w) ∧
    ¬ BehIgnoresHidden (delayedChannel k) ∧
    (¬ ∃ M' : Moore Unit Bool (Fin (k + 2) → Bool),
      ∀ a h, M'.beh a = (delayedChannel k).beh (a, h)) := by
  have hBound : BoundedBehIgnoresHidden (delayedChannel k) (k + 2) := by
    intro a h₁ h₂ w hlen
    rw [delayedChannel_beh_formula, delayedChannel_beh_formula]
    split
    · rfl
    · omega
  have hLeak :
      (delayedChannel k).beh (fun _ => false, false) (List.replicate (k + 2) ()) ≠
      (delayedChannel k).beh (fun _ => false, true) (List.replicate (k + 2) ()) := by
    have hNotLt : ¬ ((List.replicate (k + 2) ()).length < k + 2) := by
      simp
    rw [delayedChannel_beh_formula, delayedChannel_beh_formula]
    split
    · exact absurd ‹_› hNotLt
    · decide
  have hNotBeh : ¬ BehIgnoresHidden (delayedChannel k) :=
    fun hBeh => hLeak (congrFun (hBeh (fun _ => false) false true) (List.replicate (k + 2) ()))
  refine ⟨fun _ _ _ => rfl, ?_, ?_, hBound, ?_, hNotBeh, ?_⟩
  · intro a h₁ h₂ i
    exact hBound a h₁ h₂ [i] (by simp)
  · intro hStepFst
    exact hNotBeh (stepwise_nondependence_implies_behIgnoresHidden
      (delayedChannel k) (fun _ _ _ => rfl) hStepFst)
  · intro h₀ a h w hlen
    rw [eraseHidden_delayedChannel_beh_formula, delayedChannel_beh_formula]
    split
    · rfl
    · omega
  · rintro ⟨M', hM'⟩
    have hEq := (hM' (fun _ => false) false).symm.trans (hM' (fun _ => false) true)
    exact hLeak (congrFun hEq (List.replicate (k + 2) ()))

/-- **Result 5b (Exact behavioral criterion for uniform global erasability).**
Given a split-state machine `M : Moore I O (A × H)` and an inhabitant `h₀ : H`,
`BehIgnoresHidden M` holds if and only if the concrete erased machine
`eraseHidden M h₀` preserves behavior for every `(a, h)`, and also if and
only if there exists some reduced machine `M' : Moore I O A` preserving
behavior uniformly for every `(a, h)` (with identity state correspondence on `A`). -/
theorem behIgnoresHidden_iff_erasable
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) (h₀ : H) :
    (BehIgnoresHidden M ↔ ∀ a h, (eraseHidden M h₀).beh a = M.beh (a, h)) ∧
    (BehIgnoresHidden M ↔ ∃ M' : Moore I O A, ∀ a h, M'.beh a = M.beh (a, h)) := by
  have hFwd : BehIgnoresHidden M → ∀ a h, (eraseHidden M h₀).beh a = M.beh (a, h) := by
    intro hBeh a h
    funext w
    induction w generalizing a h with
    | nil =>
      change M.out (a, h₀) = M.out (a, h)
      exact congrFun (hBeh a h₀ h) []
    | cons i w ih =>
      have hStep := ih (M.step (a, h₀) i).1 (M.step (a, h₀) i).2
      change (eraseHidden M h₀).beh (M.step (a, h₀) i).1 w = M.beh (a, h) (i :: w)
      rw [hStep]
      have hEta : ((M.step (a, h₀) i).1, (M.step (a, h₀) i).2) = M.step (a, h₀) i := rfl
      rw [hEta]
      change M.beh (a, h₀) (i :: w) = M.beh (a, h) (i :: w)
      exact congrFun (hBeh a h₀ h) (i :: w)
  refine ⟨⟨hFwd, ?_⟩, ⟨fun hBeh => ⟨eraseHidden M h₀, hFwd hBeh⟩, ?_⟩⟩
  · intro hErase a h₁ h₂
    exact (hErase a h₁).symm.trans (hErase a h₂)
  · rintro ⟨M', hM'⟩ a h₁ h₂
    exact (hM' a h₁).symm.trans (hM' a h₂)

/-- Definitional identity: `BehIgnoresHidden M` is judgmentally equal to
`CoversHidden (ObsEq M)`. -/
theorem behIgnoresHidden_iff_coversHidden_obsEq
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) :
    BehIgnoresHidden M ↔ CoversHidden (ObsEq M) :=
  Iff.rfl

/-- **Result 5c-i (Nonleakage unwinding soundness: bisimulation covering
`SameFst`).** If a relation `R` on `A × H` covers `SameFst` (`CoversHidden R`),
preserves immediate outputs (`RelPreservesOut M R`), and is closed under
single-step transitions (`RelStepClosed M R`), then `BehIgnoresHidden M`
holds. Split-state corollary of `bisim_subset_obsEq` (`R` need not be an
equivalence relation, as in von Oheimb 2004). -/
theorem unwinding_bisim_implies_behIgnoresHidden
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H))
    (R : (A × H) → (A × H) → Prop)
    (hCov : CoversHidden R)
    (hOut : RelPreservesOut M R)
    (hStep : RelStepClosed M R) :
    BehIgnoresHidden M := by
  have hRel : ∀ w (p₁ p₂ : A × H), R p₁ p₂ → M.beh p₁ w = M.beh p₂ w := by
    intro w
    induction w with
    | nil =>
      intro p₁ p₂ hp
      exact hOut p₁ p₂ hp
    | cons i w ih =>
      intro p₁ p₂ hp
      exact ih (M.step p₁ i) (M.step p₂ i) (hStep p₁ p₂ hp i)
  intro a h₁ h₂
  funext w
  exact hRel w (a, h₁) (a, h₂) (hCov a h₁ h₂)

/-- **Result 5c-ii (Exactness of nonleakage unwinding: `BehIgnoresHidden` iff
some bisimulation contains `SameFst`).** For every split-state Moore machine
`M : Moore I O (A × H)`, `BehIgnoresHidden M` holds if and only if there
exists a state relation `R` satisfying `CoversHidden R`, `RelPreservesOut M R`,
and `RelStepClosed M R`. Split-state corollary of `obsEq_is_greatest_bisim`
(the completeness witness `R = ObsEq M` is definitional via
`behIgnoresHidden_iff_coversHidden_obsEq`). -/
theorem behIgnoresHidden_iff_exists_unwinding_bisim
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) :
    BehIgnoresHidden M ↔
      ∃ R : (A × H) → (A × H) → Prop,
        CoversHidden R ∧ RelPreservesOut M R ∧ RelStepClosed M R := by
  constructor
  · intro hBeh
    refine ⟨ObsEq M, hBeh, ?_, ?_⟩
    · intro p₁ p₂ hp
      exact congrFun hp []
    · intro p₁ p₂ hp i
      funext w
      exact congrFun hp (i :: w)
  · rintro ⟨R, hCov, hOut, hStep⟩
    exact unwinding_bisim_implies_behIgnoresHidden M R hCov hOut hStep

end Toy.Obs
