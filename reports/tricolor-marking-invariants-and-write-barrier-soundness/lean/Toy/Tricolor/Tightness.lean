import Toy.Tricolor.Termination

/-!
# Further tightness counterexamples

Canonical-form counterexamples ("all other hypotheses hold and the conclusion fails") for
hypotheses not already covered next to the corresponding results.
-/

namespace Toy.Tricolor

/-- The premise of `weak_of_strong` cannot be dropped (a 2-object state): a black root pointing
to a white object, nothing
grey, violates the weak invariant. -/
theorem not_weak_sBlackWhite : ¬ Weak sBlackWhite := fun h =>
  not_greyProtected_of_noGrey (s := sBlackWhite) (by decide) (h 0 1 rfl rfl rfl)

/-- White root `0`; object `1` isolated, not a root. -/
def sWhiteRootFree : St 2 := mk 2 [] [0] [.white, .white]

/-- The premise `RootsProtected s` of the allocation-color characterization cannot be dropped
(a 2-object state): with
an unprotected white root already present, black allocation does not yield
`RootsProtected`. -/
theorem isolated_and_not_rootsProtected_alloc_black :
    Isolated sWhiteRootFree 1 ∧ (Color.black ≠ .white) ∧
      ¬ RootsProtected (alloc sWhiteRootFree 1 .black) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  exact not_greyProtected_of_noGrey (s := alloc sWhiteRootFree 1 .black) (by decide)
    (h 0 rfl rfl)

/-- Grey root `0` pointing to the non-isolated object `1`. -/
def sGreyToOne : St 2 := mk 2 [(0, 1)] [0] [.grey, .white]

/-- Isolation cannot be dropped from the allocation-color characterization (a 2-object state):
an object reached from a
grey object can be "allocated" white into the roots and stay grey protected. -/
theorem rootsProtected_alloc_white_of_not_isolated :
    RootsProtected sGreyToOne ∧ ¬ Isolated sGreyToOne 1 ∧
      RootsProtected (alloc sGreyToOne 1 .white) := by
  refine ⟨rootsProtected_of_rootsNonWhite (by decide), by decide, ?_⟩
  intro r hr hw
  have : r = 1 := by revert r; decide
  subst this
  exact GreyProtected.direct (g := 0) rfl rfl rfl

/-- Any configuration: at the start of a marking cycle a live object is white while a grey
object remains. -/
theorem run_from_initMark_with_grey_not_allLiveBlack (cfg : Config) :
    Run cfg (initMark hChain) [] (initMark hChain) ∧ ¬ NoGrey (initMark hChain) ∧
      ¬ AllLiveBlack (initMark hChain) :=
  ⟨Run.nil _, by decide,
    fun h => absurd (h 1 (Live.step (x := 0) (Live.root rfl) rfl)) (by decide)⟩

/-- The scans-only drain cannot be dropped from the remark lemma (a 3-object heap and a 3-step
drain with mutator steps). -/
theorem strong_rescan_then_mutator_not_allLiveBlack :
    Strong sAfterScan0 ∧ Run cfgD0 (rescan sAfterScan0) drainWithMutator sDrainLost ∧
      ¬ ScansOnly drainWithMutator ∧ NoGrey sDrainLost ∧ ¬ AllLiveBlack sDrainLost :=
  ⟨by decide, dijkstra_rescan_then_mutator_not_allLiveBlack.2.2.1,
    dijkstra_rescan_then_mutator_not_allLiveBlack.2.2.2.1,
    dijkstra_rescan_then_mutator_not_allLiveBlack.2.2.2.2.1,
    dijkstra_rescan_then_mutator_not_allLiveBlack.2.2.2.2.2⟩

/-- The finished drain (`NoGrey`) cannot be dropped from the remark lemma (a 3-object root
snapshot and an empty drain). -/
theorem strong_rescan_with_grey_not_allLiveBlack :
    Strong (initMark hChain) ∧ Run cfgD (rescan (initMark hChain)) [] (rescan (initMark hChain)) ∧
      ScansOnly ([] : List (Op 3)) ∧ ¬ AllLiveBlack (rescan (initMark hChain)) :=
  ⟨strong_initMark _, Run.nil _, fun _ h => absurd h List.not_mem_nil,
    dijkstra_rescan_with_grey_not_allLiveBlack.2.2.2.2⟩

/-- Shaded loads cannot be dropped from load-barrier preservation (a 3-object state and one
step): loading a white live object into the roots
without shading it breaks `RootsNonWhite` (here without a heap barrier). -/
theorem unshadedLoad_breaks_rootsNonWhite :
    cfgN0.shadeLoads = false ∧ (∀ c, cfgN0.allocOk c = true → c ≠ .white) ∧
      Strong sChain ∧ RootsNonWhite sChain ∧ Step cfgN0 sChain (load false sChain 2) ∧
      ¬ RootsNonWhite (load false sChain 2) :=
  ⟨rfl, blackOnly_nonWhite, by decide, by decide, ⟨.load 2, live_two_sChain, rfl⟩, by decide⟩

/-- Non-white allocation cannot be dropped from load-barrier preservation (a 2-object state and
one step). -/
theorem shadeLoads_whiteAlloc_breaks_rootsNonWhite :
    cfgDW.shadeLoads = true ∧ cfgDW.allocOk .white = true ∧
      Strong sFree ∧ RootsNonWhite sFree ∧ Step cfgDW sFree (alloc sFree 1 .white) ∧
      ¬ RootsNonWhite (alloc sFree 1 .white) :=
  ⟨rfl, rfl, by decide, by decide, ⟨.alloc 1 .white, ⟨rfl, rfl, by decide⟩, rfl⟩, by decide⟩

/-- The strong invariant in the pre-state cannot be dropped from load-barrier preservation (a
2-object state and one step). -/
theorem shadeLoads_step_from_nonStrong_not_strong :
    cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      ¬ Strong sBlackWhite ∧ RootsNonWhite sBlackWhite ∧
      Step cfgU sBlackWhite (drop sBlackWhite 0) ∧ ¬ Strong (drop sBlackWhite 0) :=
  ⟨rfl, blackOnly_nonWhite, by decide, by decide, ⟨.drop 0, trivial, rfl⟩, by decide⟩

/-- Greyness of the scanned object cannot be dropped from the measure decrease (a 3-object
state): scanning a black object whose
successors are black leaves the measure unchanged. -/
theorem scan_black_markMeasure_eq :
    sDone.color 0 = .black ∧ markMeasure (scan sDone 0) = markMeasure sDone := by
  refine ⟨rfl, ?_⟩
  decide

/-- Seven root drops. -/
def sevenDrops : List (Op 3) := [.drop 0, .drop 0, .drop 0, .drop 0, .drop 0, .drop 0, .drop 0]

/-- Scans only cannot be dropped from the paused-mutator length bound (a 3-object state): seven
root drops from a state of measure
two on three objects exceed both the measure and `2·n = 6`. -/
theorem drops_run_longer_than_markMeasure :
    Run cfgD sDone sevenDrops (runOps cfgD sevenDrops sDone) ∧ ¬ ScansOnly sevenDrops ∧
      ¬ (sevenDrops.length ≤ markMeasure sDone ∨ sevenDrops.length ≤ 2 * 3) := by
  refine ⟨Run.cons trivial (Run.cons trivial (Run.cons trivial (Run.cons trivial
    (Run.cons trivial (Run.cons trivial (Run.cons trivial (Run.nil _))))))), ?_, by decide⟩
  intro h
  exact absurd (h (.drop 0) (by simp [sevenDrops])) (by decide)

/-- `NoGrey` at the end of the run cannot be dropped from Yuasa marking safety (an empty run
from a 3-object root snapshot). -/
theorem yuasa_run_from_initMark_with_grey_not_allLiveBlack :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Run cfgY (initMark hChain) [] (initMark hChain) ∧ ¬ AllLiveBlack (initMark hChain) :=
  ⟨rfl, blackOnly_nonWhite, Run.nil _, (run_from_initMark_with_grey_not_allLiveBlack cfgY).2.2⟩

/-- `NoGrey` at the end of the run cannot be dropped from load-barrier marking safety (an empty
run from a 3-object root snapshot). -/
theorem shadeLoads_run_from_initMark_with_grey_not_allLiveBlack :
    cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Run cfgU (initMark hChain) [] (initMark hChain) ∧ ¬ AllLiveBlack (initMark hChain) :=
  ⟨rfl, blackOnly_nonWhite, Run.nil _, (run_from_initMark_with_grey_not_allLiveBlack cfgU).2.2⟩

theorem not_live_one_sFree : ¬ Live sFree 1 := by
  intro h
  have := Live.subset (s := sFree) (fun x => x.val ≠ 1) (by decide) (by decide) h
  exact this rfl

/-- The condition on stored pointers cannot be dropped from Yuasa preservation (a 2-object
state; holding the pointer in the roots, or at least its liveness, suffices):
storing the unreachable white object `1` into the black root `0` (all other hypotheses hold)
breaks the weak invariant. -/
theorem yuasa_store_of_unreachable_breaks_weak :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Weak sFree ∧ RootsProtected sFree ∧ ¬ Live sFree 1 ∧
      ¬ (Op.store 0 1).Enabled cfgY sFree ∧ ¬ Weak ((Op.store 0 1).apply cfgY sFree) := by
  refine ⟨rfl, blackOnly_nonWhite, weak_of_strong (by decide),
    rootsProtected_of_rootsNonWhite (by decide), not_live_one_sFree,
    by show ¬ sFree.root 1 = true; decide, ?_⟩
  intro h
  exact not_greyProtected_of_noGrey (s := (Op.store 0 1).apply cfgY sFree) (by decide)
    (h 0 1 rfl rfl rfl)

/-- The liveness condition on root loads cannot be dropped from Yuasa preservation (a 2-object
state): loading the unreachable white
object `1` into the roots (all other hypotheses hold) breaks the root clause. -/
theorem load_of_unreachable_breaks_rootsProtected :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Weak sFree ∧ RootsProtected sFree ∧ ¬ (Op.load 1).Enabled cfgY sFree ∧
      ¬ RootsProtected ((Op.load 1).apply cfgY sFree) := by
  refine ⟨rfl, blackOnly_nonWhite, weak_of_strong (by decide),
    rootsProtected_of_rootsNonWhite (by decide), not_live_one_sFree, ?_⟩
  intro h
  exact not_greyProtected_of_noGrey (s := (Op.load 1).apply cfgY sFree) (by decide) (h 1 rfl rfl)

end Toy.Tricolor
