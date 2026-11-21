import ToyTwoPhase.Prog

/-!
# Decidability of the path-defined notions

Each walk-defined notion of `Prog.lean` is proved equivalent to a `PathVia` formulation (or is
already stated with `PathVia`), giving `Decidable` instances that `decide` can evaluate.
-/

namespace Toy.TwoPhase

variable {n : Nat}

theorem maybeActive_iff (p : Prog n) (L : Fin n) :
    MaybeActive p L ↔ PathVia p.edges (fun _ => true) p.entry p.A ∧
      ∃ y ∈ p.edges p.A, PathVia p.edges (fun x => !p.isKill x) y L := by
  constructor
  · rintro ⟨pre, mid, hw, hh, hmid⟩
    refine ⟨⟨pre, isWalk_prefix p.A _ pre hw, ?_, by simp⟩, ?_⟩
    · rw [← head?_append_cons pre (mid ++ [L])]; exact hh
    · have hs := isWalk_suffix p.A (mid ++ [L]) pre hw
      cases mid with
      | nil => exact ⟨L, hs.1, [], trivial, rfl, by simp⟩
      | cons c t =>
        refine ⟨c, hs.1, c :: t, hs.2, rfl, ?_⟩
        intro x hx; simp [hmid x hx]
  · rintro ⟨⟨π₁, hw₁, hh₁, _⟩, y, hy, π₂, hw₂, hh₂, hall₂⟩
    refine ⟨π₁, π₂, ?_, ?_, ?_⟩
    · apply isWalk_join p.A (π₂ ++ [L]) _ π₁ hw₁
      cases π₂ with
      | nil => simp at hh₂; subst hh₂; exact ⟨hy, trivial⟩
      | cons c t => simp at hh₂; subst hh₂; exact ⟨hy, hw₂⟩
    · rw [head?_append_cons]; exact hh₁
    · intro x hx; have := hall₂ x hx; simpa using this

instance (p : Prog n) (L : Fin n) : Decidable (MaybeActive p L) :=
  decidable_of_iff _ (maybeActive_iff p L).symm

theorem loanLive_iff (p : Prog n) (L : Fin n) :
    LoanLive p L ↔ ∃ U : Fin n, p.isUse U = true ∧ PathVia p.edges (fun x => !p.isKill x) L U := by
  constructor
  · rintro ⟨π, U, hU, hw, hh, hall⟩
    exact ⟨U, hU, π, hw, hh, fun x hx => by simp [hall x hx]⟩
  · rintro ⟨U, hU, π, hw, hh, hall⟩
    exact ⟨π, U, hU, hw, hh, fun x hx => by simpa using hall x hx⟩

instance (p : Prog n) (L : Fin n) : Decidable (LoanLive p L) :=
  decidable_of_iff _ (loanLive_iff p L).symm

theorem sharedLive_iff (p : Prog n) (s : SRef) (L : Fin n) :
    SharedLive p s L ↔ ∃ U : Fin n, p.op U = .useShared s ∧
      PathVia p.edges (fun x => p.op x != .borrowShared s) L U := by
  constructor
  · rintro ⟨π, U, hU, hw, hh, hall⟩
    exact ⟨U, hU, π, hw, hh, fun x hx => by simp [hall x hx]⟩
  · rintro ⟨U, hU, π, hw, hh, hall⟩
    exact ⟨π, U, hU, hw, hh, fun x hx => by simpa using hall x hx⟩

instance (p : Prog n) (s : SRef) (L : Fin n) : Decidable (SharedLive p s L) :=
  decidable_of_iff _ (sharedLive_iff p s L).symm

instance (p : Prog n) (L : Fin n) : Decidable (IsActiveDom p L) := by
  unfold IsActiveDom; infer_instance

instance (p : Prog n) : Decidable (NoUnwind p) := by
  unfold NoUnwind; infer_instance

theorem reentryFree_iff (p : Prog n) :
    ReentryFree p ↔ ∀ y ∈ p.succ p.A, ¬ PathVia p.succ (fun x => x != p.R) y p.A := by
  constructor
  · rintro h y hy ⟨π, hw, hh, hall⟩
    have hR : p.R ∈ π := by
      apply h π
      cases π with
      | nil => simp at hh; subst hh; exact ⟨hy, trivial⟩
      | cons c t => simp at hh; subst hh; exact ⟨hy, hw⟩
    have := hall p.R hR; simp at this
  · intro h mid hw
    apply Classical.byContradiction
    intro hR
    cases mid with
    | nil => exact h p.A hw.1 ⟨[], trivial, rfl, by simp⟩
    | cons c t =>
      apply h c hw.1 ⟨c :: t, hw.2, rfl, ?_⟩
      intro x hx; simp only [bne_iff_ne, ne_eq]; intro hxR; subst hxR; exact hR hx

instance (p : Prog n) : Decidable (ReentryFree p) :=
  decidable_of_iff _ (reentryFree_iff p).symm

instance (p : Prog n) : Decidable (ActivationStaysReachable p) := by
  unfold ActivationStaysReachable; infer_instance

instance (p : Prog n) : Decidable (DomRegionReachesA p) := by
  unfold DomRegionReachesA; infer_instance

instance (p : Prog n) (L : Fin n) : Decidable (IsCleanup p L) := by
  unfold IsCleanup; infer_instance

instance (p : Prog n) : Decidable (CleanupReadsUnderDeadLoan p) := by
  unfold CleanupReadsUnderDeadLoan; infer_instance

end Toy.TwoPhase
