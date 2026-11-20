import ToyPredTrans.Main
import ToyPredTrans.SmallStateSpaces

/-!
# Consequences of the main statements

Most theorems in this file are derived from the results in `Main` (and, where indicated,
from `SmallStateSpaces`).  `wlp_injective` is proved directly and does not depend on `Main`.
-/

namespace Toy.PredTrans

universe u

variable {σ : Type u}

/-! ## Consequences of the characterization of `wlp` -/

/-- `wlp` is injective: a universally conjunctive transformer has at most one relational
representation.  Proved directly (test the postconditions `R s` and `R' s`); it does not
depend on `Main`. -/
theorem wlp_injective {R R' : Rel σ} (h : wlp R = wlp R') : R = R' := by
  apply rel_ext
  intro s s'
  constructor
  · intro hr
    have h1 : wlp R' (R' s) s := fun _ h' => h'
    have h2 : wlp R (R' s) s := (congrFun (congrFun h (R' s)) s).mpr h1
    exact h2 s' hr
  · intro hr
    have h1 : wlp R (R s) s := fun _ h' => h'
    have h2 : wlp R' (R s) s := (congrFun (congrFun h (R s)) s).mp h1
    exact h2 s' hr

/-- Existence-and-uniqueness form: a transformer is universally conjunctive if and only if it
is the `wlp` of some relation, and then that relation is unique. -/
theorem conjAll_iff_exists_unique_wlp (T : Transformer σ) :
    ConjAll T ↔ ∃ R : Rel σ, T = wlp R ∧ ∀ R' : Rel σ, T = wlp R' → R' = R := by
  constructor
  · intro h
    have hT := (conjAll_iff_eq_wlp_relOf T).mp h
    refine ⟨relOf T, hT, ?_⟩
    intro R' hR'
    exact wlp_injective (hR'.symm.trans hT)
  · intro h
    obtain ⟨R, hR, _⟩ := h
    rw [hR]
    exact conjAll_wlp R

/-- Strictness of a `wlp`: every state has a successor. -/
theorem strict_wlp_iff (R : Rel σ) : Strict (wlp R) ↔ ∀ s, ∃ s', R s s' := by
  rw [wlp_eq_wp_true, strict_wp_iff_totalOn]
  exact ⟨fun h s => h s trivial, fun h s _ => h s⟩

/-- ω-continuity of a `wlp`: every state has a finite image. -/
theorem omegaContinuous_wlp_iff (R : Rel σ) :
    OmegaContinuous (wlp R) ↔ ∀ s, FiniteImage R s := by
  rw [wlp_eq_wp_true, omegaContinuous_wp_iff_finiteImage_on_term]
  exact ⟨fun h s => h s trivial, fun h s _ => h s⟩

/-- Refinement of `wlp`s is reverse inclusion of relations. -/
theorem refinedBy_wlp_iff (R₁ R₂ : Rel σ) :
    RefinedBy (wlp R₁) (wlp R₂) ↔ ∀ s s', R₂ s s' → R₁ s s' := by
  rw [wlp_eq_wp_true, wlp_eq_wp_true, refinedBy_wp_iff]
  exact ⟨fun h s s' => h.2 s trivial s', fun h => ⟨fun _ _ => trivial, fun s _ s' => h s s'⟩⟩

/-! ## Consequences of the characterization of `wp` -/

/-- Existential form: a transformer is positively conjunctive if and only if it is the `wp`
of some relational program. -/
theorem conjNonempty_iff_exists_wp (T : Transformer σ) :
    ConjNonempty T ↔ ∃ (R : Rel σ) (term : Pred σ), T = wp R term := by
  constructor
  · intro h
    exact ⟨relOf T, termOf T, (conjNonempty_iff_eq_wp_relOf_termOf T).mp h⟩
  · intro h
    obtain ⟨R, term, hR⟩ := h
    rw [hR]
    exact conjNonempty_wp R term

/-- For a pair in chaos normal form, `relOf` recovers the relation exactly.  Uses excluded
middle, which it implies (`lem_of_relOf_wp_of_chaosNormal`). -/
theorem relOf_wp_of_chaosNormal {R : Rel σ} {term : Pred σ} (h : ChaosNormal R term) :
    relOf (wp R term) = R := by
  rw [relOf_wp]
  apply rel_ext
  intro s s'
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hR
    by_cases ht : term s
    · exact hR (hh ht)
    · exact hR (h s ht s')
  · intro hR _
    exact hR

/-- Uniqueness in chaos normal form: two pairs in chaos normal form with the same `wp` are
equal.  Uses excluded middle, which it implies (`lem_of_chaosNormal_unique_of_wp_eq`). -/
theorem chaosNormal_unique_of_wp_eq {R R' : Rel σ} {term term' : Pred σ}
    (hn : ChaosNormal R term) (hn' : ChaosNormal R' term') (h : wp R term = wp R' term') :
    R = R' ∧ term = term' := by
  have hR : relOf (wp R term) = relOf (wp R' term') := congrArg relOf h
  rw [relOf_wp_of_chaosNormal hn, relOf_wp_of_chaosNormal hn'] at hR
  have ht : termOf (wp R term) = termOf (wp R' term') := congrArg termOf h
  rw [termOf_wp, termOf_wp] at ht
  exact ⟨hR, ht⟩

/-- Normal-form theorem: a transformer is positively conjunctive if and only if it is the
`wp` of a pair in chaos normal form, and that pair is unique. -/
theorem conjNonempty_iff_exists_unique_chaosNormal_wp (T : Transformer σ) :
    ConjNonempty T ↔
      ∃ (R : Rel σ) (term : Pred σ), ChaosNormal R term ∧ T = wp R term ∧
        ∀ (R' : Rel σ) (term' : Pred σ), ChaosNormal R' term' → T = wp R' term' →
          R' = R ∧ term' = term := by
  constructor
  · intro h
    have hT := (conjNonempty_iff_eq_wp_relOf_termOf T).mp h
    refine ⟨relOf T, termOf T,
      chaosNormal_relOf_termOf_of_monotone (monotone_of_conjNonempty h), hT, ?_⟩
    intro R' term' hn' hT'
    exact chaosNormal_unique_of_wp_eq hn'
      (chaosNormal_relOf_termOf_of_monotone (monotone_of_conjNonempty h)) (hT'.symm.trans hT)
  · intro h
    obtain ⟨R, term, _, hR, _⟩ := h
    rw [hR]
    exact conjNonempty_wp R term

/-! ## Consequences of the refinement correspondence -/

/-- With the refined program in chaos normal form, refinement is inclusion of non-abortion
predicates together with *global* reverse inclusion of relations.  Uses excluded middle, which
it implies (`lem_of_refinedBy_wp_iff_of_chaosNormal`). -/
theorem refinedBy_wp_iff_of_chaosNormal {R₁ R₂ : Rel σ} {t₁ t₂ : Pred σ}
    (h : ChaosNormal R₁ t₁) :
    RefinedBy (wp R₁ t₁) (wp R₂ t₂) ↔
      (∀ s, t₁ s → t₂ s) ∧ (∀ s s', R₂ s s' → R₁ s s') := by
  rw [refinedBy_wp_iff]
  constructor
  · intro hh
    refine ⟨hh.1, ?_⟩
    intro s s' hr
    by_cases ht : t₁ s
    · exact hh.2 s ht s' hr
    · exact h s ht s'
  · intro hh
    exact ⟨hh.1, fun s _ s' hr => hh.2 s s' hr⟩

/-! ## Finite state types -/

/-- **On a finite state type, the binary conjunctive transformers are exactly the `wp`s.** -/
theorem conjBin_iff_exists_wp_of_finiteState (hσ : FiniteState σ) (T : Transformer σ) :
    ConjBin T ↔ ∃ (R : Rel σ) (term : Pred σ), T = wp R term := by
  constructor
  · intro h
    exact (conjNonempty_iff_exists_wp T).mp (conjNonempty_of_conjBin_of_finiteState hσ h)
  · intro h
    obtain ⟨R, term, hR⟩ := h
    rw [hR]
    exact conjBin_wp R term

/-- **On a finite state type, binary conjunctivity plus top preservation characterize the
`wlp`s.** -/
theorem conjBin_topPreserving_iff_exists_wlp_of_finiteState (hσ : FiniteState σ)
    (T : Transformer σ) :
    ConjBin T ∧ TopPreserving T ↔ ∃ R : Rel σ, T = wlp R := by
  constructor
  · intro h
    have hn := conjNonempty_of_conjBin_of_finiteState hσ h.1
    have hall : ConjAll T := (conjAll_iff_conjNonempty_and_topPreserving T).mpr ⟨hn, h.2⟩
    exact ⟨relOf T, (conjAll_iff_eq_wlp_relOf T).mp hall⟩
  · intro h
    obtain ⟨R, hR⟩ := h
    rw [hR]
    exact ⟨conjBin_wlp R, topPreserving_wlp R⟩

/-! ## Dijkstra-style healthiness on state types of at most continuum cardinality -/

/-- **On a state type that injects into `Nat → Bool` (for example a countable one), binary
conjunctivity plus ω-continuity characterize the `wp`s of boundedly nondeterministic
relational programs.** -/
theorem conjBin_omegaContinuous_iff_wp_finiteImage_of_continuumState
    (hσ : ContinuumState σ) (T : Transformer σ) :
    ConjBin T ∧ OmegaContinuous T ↔
      ∃ (R : Rel σ) (term : Pred σ), T = wp R term ∧ ∀ s, term s → FiniteImage R s := by
  constructor
  · intro h
    obtain ⟨hb, hc⟩ := h
    have hn := conjNonempty_of_conjBin_of_omegaContinuous_of_continuumState hσ hb hc
    have hT := (conjNonempty_iff_eq_wp_relOf_termOf T).mp hn
    refine ⟨relOf T, termOf T, hT, ?_⟩
    rw [hT] at hc
    exact (omegaContinuous_wp_iff_finiteImage_on_term _ _).mp hc
  · intro h
    obtain ⟨R, term, hR, hfin⟩ := h
    rw [hR]
    exact ⟨conjBin_wp R term, (omegaContinuous_wp_iff_finiteImage_on_term R term).mpr hfin⟩

/-- The same with strictness added: on a state type that injects into `Nat → Bool`, a
transformer is strict, binary conjunctive and ω-continuous if and only if it is the `wp` of a
relational program that is boundedly nondeterministic (`FiniteImage`) and free of miracles
(`TotalOn`) on its non-aborting start states. -/
theorem strict_conjBin_omegaContinuous_iff_wp_finiteImage_totalOn_of_continuumState
    (hσ : ContinuumState σ) (T : Transformer σ) :
    Strict T ∧ ConjBin T ∧ OmegaContinuous T ↔
      ∃ (R : Rel σ) (term : Pred σ), T = wp R term ∧
        (∀ s, term s → FiniteImage R s) ∧ TotalOn R term := by
  constructor
  · intro h
    obtain ⟨hs, hb, hc⟩ := h
    obtain ⟨R, term, hR, hfin⟩ :=
      (conjBin_omegaContinuous_iff_wp_finiteImage_of_continuumState hσ T).mp ⟨hb, hc⟩
    refine ⟨R, term, hR, hfin, ?_⟩
    rw [hR] at hs
    exact (strict_wp_iff_totalOn R term).mp hs
  · intro h
    obtain ⟨R, term, hR, hfin, htot⟩ := h
    have hbc := (conjBin_omegaContinuous_iff_wp_finiteImage_of_continuumState hσ T).mpr
      ⟨R, term, hR, hfin⟩
    refine ⟨?_, hbc.1, hbc.2⟩
    rw [hR]
    exact (strict_wp_iff_totalOn R term).mpr htot

/-! ## Directed continuity on an arbitrary state type -/

/-- **On every state type, a binary conjunctive transformer that is continuous over directed
families is the `wp` of a relational program.** -/
theorem exists_wp_of_conjBin_of_dirContinuous {T : Transformer σ} (hb : ConjBin T)
    (hd : DirContinuous T) : ∃ (R : Rel σ) (term : Pred σ), T = wp R term :=
  (conjNonempty_iff_exists_wp T).mp (conjNonempty_of_conjBin_of_dirContinuous hb hd)

end Toy.PredTrans
