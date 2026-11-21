import Toy.Tricolor.Tightness

/-!
# Examples for the step relation, runs and the termination definitions

Proved positive and negative examples (and concrete evaluations) for `Step`, `Run`,
`ScansOnly`, `markMeasure`, `Op.allocWeight`, `InfRun`, `CollectorFair`,
`EventuallyOnlyBlackAllocs`, `WhiteTargetAllocs` and `AllocTargetsWhite`.
-/

namespace Toy.Tricolor

/-! ### `Step` -/

/-- A scan of the grey root is a step. -/
example : Step cfgNone sGreyWhite (scan sGreyWhite 0) := ⟨.scan 0, rfl, rfl⟩

/-- Negative: no step blackens the white object `1` of `sGreyWhite` (a scan of `1` is not
enabled because `1` is not grey, and no other step blackens a white object). -/
theorem not_step_sGreyWhite_scan_one : ¬ Step cfgNone sGreyWhite (scan sGreyWhite 1) := by
  rintro ⟨op, hen, heq⟩
  have hblk : (scan sGreyWhite 1).color 1 = .black := rfl
  rw [heq] at hblk
  cases op with
  | scan g =>
    have hg0 : g = 0 := (by decide : ∀ u : Fin 2, sGreyWhite.color u = .grey → u = 0) g hen
    subst hg0
    exact absurd hblk (by decide)
  | store x y => exact absurd ((shadeLe_store .none sGreyWhite x y).black hblk) (by decide)
  | erase x z => exact absurd ((shadeLe_erase .none sGreyWhite x z).black hblk) (by decide)
  | load y => exact absurd ((shadeLe_load false sGreyWhite y).black hblk) (by decide)
  | drop r =>
    have hd : (Op.apply cfgNone (Op.drop r) sGreyWhite).color 1 = sGreyWhite.color 1 := rfl
    rw [hd] at hblk
    exact absurd hblk (by decide)
  | alloc a c =>
    by_cases ha1 : (1 : Fin 2) = a
    · subst ha1
      exact absurd hen.2.2 (by decide)
    · simp only [Op.apply, Tricolor.alloc, ha1, ite_false] at hblk
      exact absurd hblk (by decide)

/-! ### `Run` -/

example : Run cfgD sGreyWhite [.scan 0, .scan 1] (scan (scan sGreyWhite 0) 1) :=
  Run.cons rfl (Run.cons rfl (Run.nil _))

/-- Negative: a run may not scan a non-grey object. -/
theorem not_run_sDone_scan_zero : ¬ Run cfgNone sDone [.scan 0] (scan sDone 0) := by
  intro h
  cases h with
  | cons hen _ => exact absurd hen (by decide : ¬ sDone.color 0 = .grey)

/-- Negative: a run must end in the state its steps produce. -/
theorem not_run_wrong_final_state : ¬ Run cfgD sGreyWhite [.scan 0] sGreyWhite := by
  intro h
  have := congrArg (fun t => t.color 0) (Run.eq_runOps h)
  exact absurd this (by decide)

/-! ### `ScansOnly` -/

example : ScansOnly [(Op.scan 0 : Op 2), .scan 1] := by simp [ScansOnly, Op.isScan]
example : ¬ ScansOnly [(Op.scan 0 : Op 2), .drop 0] := by
  intro h
  exact absurd (h (.drop 0) (by simp)) (by decide)

/-! ### `markMeasure` and `Op.allocWeight` -/

example : markMeasure sGreyWhite = 3 ∧ markMeasure sDone = 2 ∧ markMeasure sOneBlack = 0 := by
  decide
example : (Op.alloc (0 : Fin 1) .white).allocWeight = 2 ∧
    (Op.alloc (0 : Fin 1) .grey).allocWeight = 1 ∧
    (Op.alloc (0 : Fin 1) .black).allocWeight = 0 ∧ (Op.scan (0 : Fin 1)).allocWeight = 0 := by
  decide

/-! ### `InfRun` -/

example : InfRun cfgD starveOps starveStates := starvedCollector_never_noGrey.1
/-- Negative: scanning a black object forever is not an infinite execution. -/
example : ¬ InfRun cfgD badScanOps badScanStates := unenabledScans_collectorFair_never_noGrey.2.1

/-! ### `CollectorFair` -/

example : CollectorFair cycOps cycStates := greyAllocCycle_collectorFair_never_noGrey.2.1
example : ¬ CollectorFair starveOps starveStates := starvedCollector_never_noGrey.2.2.2.1

/-! ### `EventuallyOnlyBlackAllocs` -/

example : EventuallyOnlyBlackAllocs starveOps := starvedCollector_never_noGrey.2.1
example : ¬ EventuallyOnlyBlackAllocs cycOps := greyAllocCycle_collectorFair_never_noGrey.2.2.1

/-! ### `WhiteTargetAllocs` -/

example : WhiteTargetAllocs wOps wStates :=
  eventually_always_noGrey_of_collectorFair_of_whiteTargetAllocs_nonvacuous.2.2.1
/-- Negative: the grey-allocation cycle re-colors black cells. -/
example : ¬ WhiteTargetAllocs cycOps cycStates := greyAllocCycle_collectorFair_never_noGrey.2.2.2.1

/-! ### `AllocTargetsWhite` -/

/-- Allocating the white free cell `1` of `initMark hAlloc` (any color) takes a white cell. -/
example : AllocTargetsWhite cfgDW (initMark hAlloc) [.alloc 1 .grey, .scan 0] := by
  refine ⟨fun a c h => ?_, ?_⟩
  · cases h; rfl
  · exact ⟨(fun _ _ h => by cases h), trivial⟩
/-- Negative: allocating the same cell again after it was colored grey re-colors a grey cell. -/
example : ¬ AllocTargetsWhite cfgDW (initMark hAlloc) [.alloc 1 .grey, .drop 1, .alloc 1 .grey] := by
  intro h
  have := h.2.2.1 1 .grey rfl
  exact absurd this (by decide)

end Toy.Tricolor
