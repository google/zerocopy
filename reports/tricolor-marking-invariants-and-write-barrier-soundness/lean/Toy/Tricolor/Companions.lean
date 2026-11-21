import Toy.Tricolor.Termination

/-!
# Companion lemmas

Proof-only corollaries of results stated in the other modules.
-/

namespace Toy.Tricolor

/-- Enabled scans cannot be dropped from the infinitely-often corollary either (an infinite
execution over a 2-object heap): the execution of `unenabledScans_collectorFair_never_noGrey`,
which scans the black object `1` forever, satisfies the state equations, collector fairness and
both allocation assumptions and is not an `InfRun`; every one of its states has a grey object,
so states with no grey object do not occur infinitely often (they never occur). -/
theorem unenabledScans_collectorFair_not_infinitely_often_noGrey :
    (∀ i, badScanStates (i + 1) = (badScanOps i).apply cfgD (badScanStates i)) ∧
      ¬ InfRun cfgD badScanOps badScanStates ∧
      CollectorFair badScanOps badScanStates ∧ EventuallyOnlyBlackAllocs badScanOps ∧
      WhiteTargetAllocs badScanOps badScanStates ∧
      (∀ i, ¬ NoGrey (badScanStates i)) ∧
      ¬ ∀ M, ∃ i, M ≤ i ∧ NoGrey (badScanStates i) := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := unenabledScans_collectorFair_never_noGrey
  have hgrey : ∀ i, ¬ NoGrey (badScanStates i) := fun _ => (by decide : ¬ NoGrey sGreyAndBlack)
  refine ⟨h1, h2, h3, h4, h5, hgrey, fun h => ?_⟩
  obtain ⟨i, _, hi⟩ := h 0
  exact hgrey i hi

end Toy.Tricolor
