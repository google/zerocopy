import Toy.Tricolor.Marking

/-!
# Counterexamples, interleavings and positive controls

Concrete configurations, states and step sequences that show that no barrier hypothesis can
be dropped (each counterexample is a heap of at most 3 objects with a step or a finite trace;
"cannot be dropped" below always means only this), that marking with neither a heap barrier nor a load barrier leaves a live object white
at the end of marking, and how allocation color and root loads interact with the Dijkstra
barrier.
-/

namespace Toy.Tricolor

/-! ## Configurations -/

/-- No heap barrier; root loads shaded (a load barrier); black allocation only. -/
def cfgU : Config := { barrier := .none, shadeLoads := true, allocOk := fun c => c == .black }
/-- No heap barrier; root loads not shaded; black allocation only. -/
def cfgN0 : Config :=
  { barrier := .none, shadeLoads := false, allocOk := fun c => c == .black }
/-- Dijkstra barrier; root loads shaded; black allocation only. -/
def cfgD : Config := { barrier := .dijkstra, shadeLoads := true, allocOk := fun c => c == .black }
/-- Dijkstra barrier; root loads not shaded; black allocation only. -/
def cfgD0 : Config :=
  { barrier := .dijkstra, shadeLoads := false, allocOk := fun c => c == .black }
/-- Dijkstra barrier; root loads shaded; every allocation color allowed. -/
def cfgDW : Config := { barrier := .dijkstra, shadeLoads := true, allocOk := fun _ => true }
/-- Yuasa barrier; root loads not shaded; black allocation only. -/
def cfgY : Config := { barrier := .yuasa, shadeLoads := false, allocOk := fun c => c == .black }
/-- Yuasa barrier; root loads not shaded; every allocation color allowed. -/
def cfgYW : Config := { barrier := .yuasa, shadeLoads := false, allocOk := fun _ => true }

theorem blackOnly_nonWhite : ∀ c : Color, (c == .black) = true → c ≠ .white := by
  intro c h hc; subst hc; exact absurd h (by decide)

/-! ## States -/

/-- Heap shape: root `0` points to `1`, which points to `2` (colors irrelevant before
`initMark`). -/
def hChain : St 3 := mk 3 [(0, 1), (1, 2)] [0] []
/-- Mid-marking: black root `0`, grey `1`, white `2` along `0 → 1 → 2`. -/
def sChain : St 3 := mk 3 [(0, 1), (1, 2)] [0] [.black, .grey, .white]
/-- Heap shape: root `0`; object `1` isolated and not a root (free for allocation). -/
def hAlloc : St 2 := mk 2 [] [0] []

/-- Mid-marking: black root `0`, grey `1`, and the white object `2`, which is held in the roots
and grey protected through `1 → 2`. -/
def sChainR : St 3 := mk 3 [(0, 1), (1, 2)] [0, 2] [.black, .grey, .white]
/-- As `sChainR`, but `2` was shaded when it was loaded into the roots. -/
def sChainShaded : St 3 := mk 3 [(0, 1), (1, 2)] [0, 2] [.black, .grey, .grey]

theorem live_two_sChain : Live sChain 2 :=
  Live.step (x := 1) (Live.step (x := 0) (Live.root rfl) rfl) rfl

/-- Closure check for concrete states: every live object is black. -/
theorem allLiveBlack_of_closed {n : Nat} (s : St n)
    (h1 : ∀ r, s.root r = true → s.color r = .black)
    (h2 : ∀ x y, s.color x = .black → s.edge x y = true → s.color y = .black) :
    AllLiveBlack s :=
  fun _ hy => Live.subset (s := s) (fun x => s.color x = .black) h1 h2 hy

/-! ## The barrier hypothesis of Dijkstra soundness -/

/-- Without a barrier, a store of a white object held in the roots into a black object breaks
the strong invariant. -/
theorem store_unbarriered_breaks_strong :
    cfgN0.barrier ≠ .dijkstra ∧ Strong sChainR ∧ Step cfgN0 sChainR (store .none sChainR 0 2) ∧
      ¬ Strong (store .none sChainR 0 2) :=
  ⟨by decide, by decide, ⟨.store 0 2, rfl, rfl⟩, by decide⟩

/-- **The Yuasa barrier does not preserve the strong invariant** (it preserves the weak one):
from a strong state with a grey-protected white root, the same store under the Yuasa barrier
creates a black-to-white edge. -/
theorem store_yuasa_breaks_strong :
    cfgY.barrier = .yuasa ∧ Strong sChainR ∧ RootsProtected sChainR ∧
      Step cfgY sChainR (store .yuasa sChainR 0 2) ∧
      ¬ Strong (store .yuasa sChainR 0 2) ∧
      Weak (store .yuasa sChainR 0 2) ∧ RootsProtected (store .yuasa sChainR 0 2) := by
  have hstep : Step cfgY sChainR (store .yuasa sChainR 0 2) := ⟨.store 0 2, rfl, rfl⟩
  have hrp : RootsProtected sChainR := by
    intro r hr hw
    have : r = 2 := by revert r; decide
    subst this
    exact GreyProtected.direct (g := 1) rfl rfl rfl
  have hw := weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc rfl blackOnly_nonWhite
    (weak_of_strong (s := sChainR) (by decide)) hrp hstep
  exact ⟨rfl, by decide, hrp, hstep, by decide, hw.1, hw.2⟩

/-- The invariant premise of Dijkstra soundness cannot be dropped (a 2-object state and one
step): a step does not repair it. -/
theorem dijkstra_step_from_nonStrong_not_strong :
    cfgD.barrier = .dijkstra ∧ ¬ Strong sBlackWhite ∧ Step cfgD sBlackWhite (drop sBlackWhite 0) ∧
      ¬ Strong (drop sBlackWhite 0) :=
  ⟨rfl, by decide, ⟨.drop 0, trivial, rfl⟩, by decide⟩

/-! ## The hypotheses of Yuasa soundness -/

theorem not_weak_erase_sWeakNotStrong (b : Barrier) (hb : b ≠ .yuasa) :
    ¬ Weak (erase b sWeakNotStrong 1 2) := by
  have hc : (erase b sWeakNotStrong 1 2).color = sWeakNotStrong.color := by
    simp [erase, hb]
  intro h
  have hgp := h 0 2 (by cases b <;> decide) (by rw [hc]; rfl) (by rw [hc]; rfl)
  refine GreyProtected.subset (s := erase b sWeakNotStrong 1 2) (fun _ => False) ?_ ?_ hgp
  · intro g y hg he _
    rw [hc] at hg
    revert g y
    cases b <;> decide
  · intro _ _ h _ _; exact h

/-- Without a barrier, erasing the only grey-protected path to a white object pointed to by a
black object breaks the weak invariant. -/
theorem erase_unbarriered_breaks_weak :
    cfgU.barrier ≠ .yuasa ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Weak sWeakNotStrong ∧ RootsProtected sWeakNotStrong ∧
      Step cfgU sWeakNotStrong (erase .none sWeakNotStrong 1 2) ∧
      ¬ Weak (erase .none sWeakNotStrong 1 2) :=
  ⟨by decide, blackOnly_nonWhite, weak_sWeakNotStrong, rootsProtected_of_rootsNonWhite (by decide), ⟨.erase 1 2, trivial, rfl⟩,
    not_weak_erase_sWeakNotStrong .none (by decide)⟩

/-- **The Dijkstra barrier does not preserve the weak invariant** (from a weak, non-strong
state): the same erase under the Dijkstra barrier. -/
theorem erase_dijkstra_breaks_weak :
    cfgD.barrier ≠ .yuasa ∧ (∀ c, cfgD.allocOk c = true → c ≠ .white) ∧
      Weak sWeakNotStrong ∧ RootsProtected sWeakNotStrong ∧
      Step cfgD sWeakNotStrong (erase .dijkstra sWeakNotStrong 1 2) ∧
      ¬ Weak (erase .dijkstra sWeakNotStrong 1 2) :=
  ⟨by decide, blackOnly_nonWhite, weak_sWeakNotStrong, rootsProtected_of_rootsNonWhite (by decide), ⟨.erase 1 2, trivial, rfl⟩,
    not_weak_erase_sWeakNotStrong .dijkstra (by decide)⟩

/-- Black root `0`; object `1` isolated, not a root, white. -/
def sFree : St 2 := mk 2 [] [0] [.black, .white]

/-- White allocation into the roots breaks the root clause under the Yuasa barrier. -/
theorem alloc_white_yuasa_breaks_rootsProtected :
    cfgYW.barrier = .yuasa ∧ cfgYW.allocOk .white = true ∧
      Weak sFree ∧ RootsProtected sFree ∧ Step cfgYW sFree (alloc sFree 1 .white) ∧
      ¬ RootsProtected (alloc sFree 1 .white) := by
  refine ⟨rfl, rfl, weak_of_strong (by decide), rootsProtected_of_rootsNonWhite (by decide),
    ⟨.alloc 1 .white, ⟨rfl, rfl, by decide⟩, rfl⟩, ?_⟩
  intro h
  have hgp := h 1 rfl rfl
  exact GreyProtected.subset (s := alloc sFree 1 .white) (fun _ => False) (by decide)
    (fun _ _ h _ _ => h) hgp

/-- Black root `0` and white root `1`, no edges: the weak invariant holds, its root clause
fails. -/
def sWhiteRootUnprotected : St 2 := mk 2 [] [0, 1] [.black, .white]

/-- The root clause cannot be dropped (a 2-object state and one step): a store of an
unprotected white root into a black object breaks the weak invariant under the Yuasa barrier. -/
theorem yuasa_store_without_rootsProtected_breaks_weak :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Weak sWhiteRootUnprotected ∧ ¬ RootsProtected sWhiteRootUnprotected ∧
      Step cfgY sWhiteRootUnprotected (store .yuasa sWhiteRootUnprotected 0 1) ∧
      ¬ Weak (store .yuasa sWhiteRootUnprotected 0 1) := by
  refine ⟨rfl, blackOnly_nonWhite, weak_of_strong (by decide), ?_, ⟨.store 0 1, rfl, rfl⟩, ?_⟩
  · intro h
    exact not_greyProtected_of_noGrey (s := sWhiteRootUnprotected) (by decide) (h 1 rfl rfl)
  · intro h
    exact not_greyProtected_of_noGrey (s := store .yuasa sWhiteRootUnprotected 0 1) (by decide)
      (h 0 1 rfl rfl rfl)

/-- The invariant premise of Yuasa soundness cannot be dropped (a 2-object state and one
step). -/
theorem yuasa_step_from_nonWeak_not_weak :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      ¬ Weak sBlackWhite ∧ RootsProtected sBlackWhite ∧
      Step cfgY sBlackWhite (drop sBlackWhite 0) ∧ ¬ Weak (drop sBlackWhite 0) := by
  refine ⟨rfl, blackOnly_nonWhite, ?_, rootsProtected_sBlackWhite, ⟨.drop 0, trivial, rfl⟩, ?_⟩
  · intro h
    exact not_greyProtected_of_noGrey (s := sBlackWhite) (by decide) (h 0 1 rfl rfl rfl)
  · intro h
    exact not_greyProtected_of_noGrey (s := drop sBlackWhite 0) (by decide) (h 0 1 rfl rfl rfl)

/-! ## No barrier and unshaded loads: a live object is left white -/

/-- Scan the root `0`; load the white object `2` into the roots; store it into the black root
`0`; drop it from the roots; erase its other path `1 → 2`; scan `1`. -/
def traceLostObject : List (Op 3) := [.scan 0, .load 2, .store 0 2, .drop 2, .erase 1 2, .scan 1]

theorem run_traceLostObject (cfg : Config) :
    Run cfg (initMark hChain) traceLostObject (runOps cfg traceLostObject (initMark hChain)) := by
  obtain ⟨b, sh, ok⟩ := cfg
  cases b <;> cases sh <;>
    exact Run.cons rfl (Run.cons (Live.step (x := 1) (Live.step (x := 0) (Live.root rfl) rfl) rfl)
      (Run.cons rfl (Run.cons trivial (Run.cons trivial (Run.cons rfl (Run.nil _))))))

theorem runOps_traceLostObject_of_none_of_unshaded (cfg : Config) (hb : cfg.barrier = .none)
    (hsh : cfg.shadeLoads = false) :
    runOps cfg traceLostObject (initMark hChain) = runOps cfgN0 traceLostObject (initMark hChain) := by
  obtain ⟨b, sh, ok⟩ := cfg
  simp only at hb hsh
  subst hb; subst hsh
  rfl

/-- The final state of `traceLostObject` without a heap barrier and without load shading. -/
def sLost : St 3 := runOps cfgN0 traceLostObject (initMark hChain)

/-- **No heap barrier and unshaded root loads are unsound.** Under any configuration without a
heap barrier and without load shading, the enabled interleaving `traceLostObject` from the start
of a marking cycle on the heap `0 (root) → 1 → 2` reaches a state with no grey object in which
the object `2` is live (through the edge `0 → 2` from the black root) and white. -/
theorem unbarriered_unshadedLoads_traceLostObject_leaves_live_white (cfg : Config)
    (hb : cfg.barrier = .none) (hsh : cfg.shadeLoads = false) :
    Run cfg (initMark hChain) traceLostObject (runOps cfg traceLostObject (initMark hChain)) ∧
      NoGrey (runOps cfg traceLostObject (initMark hChain)) ∧
      Live (runOps cfg traceLostObject (initMark hChain)) 2 ∧
      (runOps cfg traceLostObject (initMark hChain)).color 2 = .white := by
  refine ⟨run_traceLostObject cfg, ?_⟩
  rw [runOps_traceLostObject_of_none_of_unshaded cfg hb hsh]
  exact ⟨by decide, Live.step (x := 0) (Live.root rfl) rfl, rfl⟩

theorem run_sLost : Run cfgN0 (initMark hChain) traceLostObject sLost :=
  run_traceLostObject cfgN0

/-- `traceLostObject` with every heap write made through a held pointer: `1` is loaded before
the erase and dropped afterwards. -/
def traceLostObjectHeld : List (Op 3) :=
  [.scan 0, .load 2, .store 0 2, .drop 2, .load 1, .erase 1 2, .drop 1, .scan 1]

/-- The register-disciplined variant reaches the same final state `sLost` without a heap
barrier and without load shading. -/
theorem unbarriered_unshadedLoads_heldTrace_reaches_sLost :
    Run cfgN0 (initMark hChain) traceLostObjectHeld sLost := by
  have h : Run cfgN0 (initMark hChain) traceLostObjectHeld
      (runOps cfgN0 traceLostObjectHeld (initMark hChain)) :=
    Run.cons rfl (Run.cons (Live.step (x := 1) (Live.step (x := 0) (Live.root rfl) rfl) rfl)
      (Run.cons rfl (Run.cons trivial (Run.cons (Live.step (x := 0) (Live.root rfl) rfl)
        (Run.cons trivial (Run.cons trivial (Run.cons rfl (Run.nil _))))))))
  have heq : runOps cfgN0 traceLostObjectHeld (initMark hChain) = sLost :=
    St.ext' (by funext u v; revert u v; decide) (by funext r; revert r; decide)
      (by funext x; revert x; decide)
  rw [heq] at h
  exact h

theorem not_allLiveBlack_sLost : ¬ AllLiveBlack sLost :=
  fun h => absurd (h 2 (Live.step (x := 0) (Live.root rfl) rfl)) (by decide)

/-- The heap-barrier hypothesis of `unbarriered_unshadedLoads_traceLostObject_leaves_live_white`
cannot be dropped from that counterexample: with unshaded loads and the Dijkstra barrier the
same 3-object, 6-step trace ends with `2` grey. -/
theorem traceLostObject_dijkstra_unshadedLoads_not_lost :
    cfgD0.shadeLoads = false ∧ cfgD0.barrier ≠ .none ∧
      ¬ (Run cfgD0 (initMark hChain) traceLostObject (runOps cfgD0 traceLostObject (initMark hChain)) ∧
        NoGrey (runOps cfgD0 traceLostObject (initMark hChain)) ∧
        Live (runOps cfgD0 traceLostObject (initMark hChain)) 2 ∧
        (runOps cfgD0 traceLostObject (initMark hChain)).color 2 = .white) :=
  ⟨rfl, by decide, fun h => absurd h.2.1 (by decide)⟩

/-- The same with unshaded loads and the Yuasa barrier. -/
theorem traceLostObject_yuasa_unshadedLoads_not_lost :
    cfgY.shadeLoads = false ∧ cfgY.barrier ≠ .none ∧
      ¬ (Run cfgY (initMark hChain) traceLostObject (runOps cfgY traceLostObject (initMark hChain)) ∧
        NoGrey (runOps cfgY traceLostObject (initMark hChain)) ∧
        Live (runOps cfgY traceLostObject (initMark hChain)) 2 ∧
        (runOps cfgY traceLostObject (initMark hChain)).color 2 = .white) :=
  ⟨rfl, by decide, fun h => absurd h.2.1 (by decide)⟩

/-- The unshaded-loads hypothesis of the lost-object counterexample cannot be dropped: without a
heap barrier but with shaded loads the same 3-object, 6-step trace ends with `2` grey. -/
theorem traceLostObject_unbarriered_shadeLoads_not_lost :
    cfgU.barrier = .none ∧ cfgU.shadeLoads ≠ false ∧
      ¬ (Run cfgU (initMark hChain) traceLostObject (runOps cfgU traceLostObject (initMark hChain)) ∧
        NoGrey (runOps cfgU traceLostObject (initMark hChain)) ∧
        Live (runOps cfgU traceLostObject (initMark hChain)) 2 ∧
        (runOps cfgU traceLostObject (initMark hChain)).color 2 = .white) :=
  ⟨rfl, by decide, fun h => absurd h.2.1 (by decide)⟩

/-- Positive control: under the Dijkstra barrier (unshaded loads) the same interleaving,
followed by scanning the object the barrier greyed, ends with every live object black. -/
theorem dijkstra_traceLostObject_then_scan_safe :
    Run cfgD0 (initMark hChain) (traceLostObject ++ [.scan 2])
        (runOps cfgD0 (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgD0 (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      AllLiveBlack (runOps cfgD0 (traceLostObject ++ [.scan 2]) (initMark hChain)) :=
  ⟨Run.append (run_traceLostObject cfgD0) (Run.cons rfl (Run.nil _)), by decide,
    allLiveBlack_of_closed _ (by decide) (by decide)⟩

/-- Positive control: the same under the Yuasa barrier (unshaded loads). -/
theorem yuasa_traceLostObject_then_scan_safe :
    Run cfgY (initMark hChain) (traceLostObject ++ [.scan 2])
        (runOps cfgY (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgY (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      AllLiveBlack (runOps cfgY (traceLostObject ++ [.scan 2]) (initMark hChain)) :=
  ⟨Run.append (run_traceLostObject cfgY) (Run.cons rfl (Run.nil _)), by decide,
    allLiveBlack_of_closed _ (by decide) (by decide)⟩

/-- Positive control: the same without any heap barrier but with shaded loads. -/
theorem shadeLoads_traceLostObject_then_scan_safe :
    Run cfgU (initMark hChain) (traceLostObject ++ [.scan 2])
        (runOps cfgU (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgU (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      AllLiveBlack (runOps cfgU (traceLostObject ++ [.scan 2]) (initMark hChain)) :=
  ⟨Run.append (run_traceLostObject cfgU) (Run.cons rfl (Run.nil _)), by decide,
    allLiveBlack_of_closed _ (by decide) (by decide)⟩

/-- The barrier hypothesis of Yuasa marking safety cannot be dropped (a 3-object heap and a
6-step run; no barrier, unshaded loads, black-only allocation). -/
theorem unbarriered_unshadedLoads_blackAlloc_run_from_initMark_not_allLiveBlack :
    cfgN0.barrier ≠ .yuasa ∧ (∀ c, cfgN0.allocOk c = true → c ≠ .white) ∧
      Run cfgN0 (initMark hChain) traceLostObject sLost ∧ NoGrey sLost ∧ ¬ AllLiveBlack sLost :=
  ⟨by decide, blackOnly_nonWhite, run_sLost, by decide, not_allLiveBlack_sLost⟩

/-- The barrier hypothesis of Dijkstra marking with a final rescan cannot be dropped (a
3-object heap, a 6-step run and an empty drain): without a barrier
(and without load shading) the rescan finds no white root, the drain is empty, and the live
object `2` is still white. -/
theorem unbarriered_run_rescan_not_allLiveBlack :
    cfgN0.barrier ≠ .dijkstra ∧ Run cfgN0 (initMark hChain) traceLostObject sLost ∧
      Run cfgN0 (rescan sLost) [] (rescan sLost) ∧ ScansOnly ([] : List (Op 3)) ∧
      NoGrey (rescan sLost) ∧ ¬ AllLiveBlack (rescan sLost) := by
  refine ⟨by decide, run_sLost, Run.nil _, fun _ h => absurd h (List.not_mem_nil), by decide, ?_⟩
  intro h
  exact absurd (h 2 (Live.step (x := 0) (Live.root rfl) rfl)) (by decide)

/-! ## Dijkstra barrier, root loads and allocation color -/

/-- Scan the root; load the white object `2` into the roots; erase its heap path `1 → 2`;
scan `1`. -/
def traceLoadLost : List (Op 3) := [.scan 0, .load 2, .erase 1 2, .scan 1]

theorem run_traceLoadLost (cfg : Config) :
    Run cfg (initMark hChain) traceLoadLost (runOps cfg traceLoadLost (initMark hChain)) := by
  obtain ⟨b, sh, ok⟩ := cfg
  cases b <;> cases sh <;>
    exact Run.cons rfl (Run.cons (Live.step (x := 1) (Live.step (x := 0) (Live.root rfl) rfl) rfl)
      (Run.cons trivial (Run.cons rfl (Run.nil _))))

/-- The final state of `traceLoadLost` under the Dijkstra barrier without load shading. -/
def sLoadLost : St 3 := runOps cfgD0 traceLoadLost (initMark hChain)

theorem not_allLiveBlack_sLoadLost : ¬ AllLiveBlack sLoadLost :=
  fun h => absurd (h 2 (Live.root rfl)) (by decide)

/-- **Unshaded root loads defeat Dijkstra marking without a rescan, even with black
allocation.** Under the Dijkstra barrier with unshaded loads and black-only allocation, the
interleaving `traceLoadLost` from the start of a marking cycle on the heap `0 (root) → 1 → 2`
reaches a state with no grey object in which the live root `2` is white. -/
theorem dijkstra_unshadedLoads_run_from_initMark_leaves_live_white :
    cfgD0.barrier = .dijkstra ∧ cfgD0.shadeLoads = false ∧
      (∀ c, cfgD0.allocOk c = true → c ≠ .white) ∧
      Run cfgD0 (initMark hChain) traceLoadLost sLoadLost ∧ NoGrey sLoadLost ∧
      Live sLoadLost 2 ∧ sLoadLost.color 2 = .white :=
  ⟨rfl, rfl, blackOnly_nonWhite, run_traceLoadLost cfgD0, by decide, Live.root rfl, rfl⟩

/-- Positive control: with shaded loads the same interleaving leaves `2` grey; scanning it
ends with every live object black. -/
theorem dijkstra_shadeLoads_traceLoadLost_then_scan_safe :
    Run cfgD (initMark hChain) (traceLoadLost ++ [.scan 2])
        (runOps cfgD (traceLoadLost ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgD (traceLoadLost ++ [.scan 2]) (initMark hChain)) ∧
      AllLiveBlack (runOps cfgD (traceLoadLost ++ [.scan 2]) (initMark hChain)) :=
  ⟨Run.append (run_traceLoadLost cfgD) (Run.cons rfl (Run.nil _)), by decide,
    allLiveBlack_of_closed _ (by decide) (by decide)⟩

/-- Positive control: under the Yuasa barrier unshaded loads are harmless here (the erase
shades `2`). -/
theorem yuasa_traceLoadLost_then_scan_safe :
    Run cfgY (initMark hChain) (traceLoadLost ++ [.scan 2])
        (runOps cfgY (traceLoadLost ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgY (traceLoadLost ++ [.scan 2]) (initMark hChain)) ∧
      AllLiveBlack (runOps cfgY (traceLoadLost ++ [.scan 2]) (initMark hChain)) :=
  ⟨Run.append (run_traceLoadLost cfgY) (Run.cons rfl (Run.nil _)), by decide,
    allLiveBlack_of_closed _ (by decide) (by decide)⟩

/-- The rescan cannot be dropped from Dijkstra marking (a 3-object heap, a 4-step run with
unshaded loads, and an empty drain): the drain runs from the un-rescanned state. All other
hypotheses of the rescan theorem hold. -/
theorem dijkstra_run_without_rescan_scansOnly_not_allLiveBlack :
    cfgD0.barrier = .dijkstra ∧ Run cfgD0 (initMark hChain) traceLoadLost sLoadLost ∧
      Run cfgD0 sLoadLost [] sLoadLost ∧ ScansOnly ([] : List (Op 3)) ∧
      NoGrey sLoadLost ∧ ¬ AllLiveBlack sLoadLost :=
  ⟨rfl, run_traceLoadLost cfgD0, Run.nil _, fun _ h => absurd h List.not_mem_nil,
    by decide, not_allLiveBlack_sLoadLost⟩

/-- After the first scan of `traceLoadLost`. -/
def sAfterScan0 : St 3 := runOps cfgD0 [.scan 0] (initMark hChain)
/-- Mutator steps during the drain after a remark. -/
def drainWithMutator : List (Op 3) := [.load 2, .erase 1 2, .scan 1]
def sDrainLost : St 3 := runOps cfgD0 drainWithMutator (rescan sAfterScan0)

/-- The drain after the remark must be collector-only: mutator steps between the rescan and
the end of marking can again hide a live white root. -/
theorem dijkstra_rescan_then_mutator_not_allLiveBlack :
    cfgD0.barrier = .dijkstra ∧ Run cfgD0 (initMark hChain) [.scan 0] sAfterScan0 ∧
      Run cfgD0 (rescan sAfterScan0) drainWithMutator sDrainLost ∧
      ¬ ScansOnly drainWithMutator ∧ NoGrey sDrainLost ∧ ¬ AllLiveBlack sDrainLost := by
  refine ⟨rfl, Run.cons rfl (Run.nil _), ?_, ?_, by decide, ?_⟩
  · exact Run.cons (Live.step (x := 1) (Live.step (x := 0) (Live.root rfl) rfl) rfl)
      (Run.cons trivial (Run.cons rfl (Run.nil _)))
  · intro h; exact absurd (h (.load 2) (by simp [drainWithMutator])) (by decide)
  · intro h; exact absurd (h 2 (Live.root rfl)) (by decide)

/-- Before marking has finished, live objects may be white. -/
theorem dijkstra_rescan_with_grey_not_allLiveBlack :
    cfgD.barrier = .dijkstra ∧ Run cfgD (initMark hChain) [] (initMark hChain) ∧
      Run cfgD (rescan (initMark hChain)) [] (rescan (initMark hChain)) ∧
      ScansOnly ([] : List (Op 3)) ∧ ¬ AllLiveBlack (rescan (initMark hChain)) := by
  refine ⟨rfl, Run.nil _, Run.nil _, fun _ h => absurd h (List.not_mem_nil), ?_⟩
  intro h
  exact absurd (h 1 (Live.step (x := 0) (Live.root rfl) rfl)) (by decide)

/-- Allocate `1` white into the roots, then scan the root. -/
def traceWhiteAlloc : List (Op 2) := [.alloc 1 .white, .scan 0]

theorem run_traceWhiteAlloc (cfg : Config) (hok : cfg.allocOk .white = true) :
    Run cfg (initMark hAlloc) traceWhiteAlloc (runOps cfg traceWhiteAlloc (initMark hAlloc)) :=
  Run.cons ⟨hok, rfl, by decide⟩ (Run.cons rfl (Run.nil _))

def sWhiteAlloc : St 2 := runOps cfgDW traceWhiteAlloc (initMark hAlloc)

theorem not_allLiveBlack_sWhiteAlloc : ¬ AllLiveBlack sWhiteAlloc :=
  fun h => absurd (h 1 (Live.root rfl)) (by decide)

/-- **White allocation defeats Dijkstra marking without a rescan, even with shaded loads.**
On the heap `0 (root)`, `1` (isolated, free), allocating `1` white into the roots and scanning
the root reaches a state with no grey object in which the live root `1` is white. -/
theorem dijkstra_whiteAlloc_run_from_initMark_leaves_live_white :
    cfgDW.barrier = .dijkstra ∧ cfgDW.shadeLoads = true ∧ cfgDW.allocOk .white = true ∧
      Run cfgDW (initMark hAlloc) traceWhiteAlloc sWhiteAlloc ∧ NoGrey sWhiteAlloc ∧
      Live sWhiteAlloc 1 ∧ sWhiteAlloc.color 1 = .white :=
  ⟨rfl, rfl, rfl, run_traceWhiteAlloc cfgDW rfl, by decide, Live.root rfl, rfl⟩

/-- Positive control: with a final rescan (then a scan of the greyed root) the same white
allocation is safe. -/
theorem dijkstra_whiteAlloc_then_rescan_safe :
    Run cfgDW (rescan sWhiteAlloc) [.scan 1] (scan (rescan sWhiteAlloc) 1) ∧
      NoGrey (scan (rescan sWhiteAlloc) 1) ∧ AllLiveBlack (scan (rescan sWhiteAlloc) 1) :=
  ⟨Run.cons rfl (Run.nil _), by decide, allLiveBlack_of_closed _ (by decide) (by decide)⟩

def sWhiteAllocY : St 2 := runOps cfgYW traceWhiteAlloc (initMark hAlloc)

/-- The allocation-color hypothesis of Yuasa marking safety cannot be dropped (a 2-object heap
and a 2-step run). -/
theorem yuasa_whiteAlloc_run_from_initMark_not_allLiveBlack :
    cfgYW.barrier = .yuasa ∧ cfgYW.allocOk .white = true ∧
      Run cfgYW (initMark hAlloc) traceWhiteAlloc sWhiteAllocY ∧ NoGrey sWhiteAllocY ∧
      ¬ AllLiveBlack sWhiteAllocY :=
  ⟨rfl, rfl, run_traceWhiteAlloc cfgYW rfl, by decide,
    fun h => absurd (h 1 (Live.root rfl)) (by decide)⟩

/-- Not every state is the start of a marking cycle: `initMark` greys every root. -/
theorem sBlackWhite_ne_initMark : ∀ s₀ : St 2, sBlackWhite ≠ initMark s₀ := by
  intro s₀ heq
  have hc : sBlackWhite.color 0 = (initMark s₀).color 0 := by rw [heq]
  simp only [initMark] at hc
  split at hc <;> exact absurd hc (by decide)

/-- The start at `initMark` cannot be dropped from Yuasa marking safety (a 2-object state):
all other hypotheses hold for an
empty run from a black-to-white state that is not of the form `initMark s₀`. -/
theorem yuasa_run_not_from_initMark_not_allLiveBlack :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      (∀ s₀, sBlackWhite ≠ initMark s₀) ∧
      Run cfgY sBlackWhite [] sBlackWhite ∧ NoGrey sBlackWhite ∧ ¬ AllLiveBlack sBlackWhite :=
  ⟨rfl, blackOnly_nonWhite, sBlackWhite_ne_initMark, Run.nil _, by decide,
    not_allLiveBlack_sBlackWhite⟩

/-- The start at `initMark` cannot be dropped from load-barrier marking safety (an empty run
from a 2-object state). -/
theorem shadeLoads_run_not_from_initMark_not_allLiveBlack :
    cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      (∀ s₀, sBlackWhite ≠ initMark s₀) ∧
      Run cfgU sBlackWhite [] sBlackWhite ∧ NoGrey sBlackWhite ∧ ¬ AllLiveBlack sBlackWhite :=
  ⟨rfl, blackOnly_nonWhite, sBlackWhite_ne_initMark, Run.nil _, by decide,
    not_allLiveBlack_sBlackWhite⟩

/-- The start at `initMark` cannot be dropped from the rescan theorem under the Dijkstra
barrier (a 2-object state): a black-to-white state is not reachable that way, and rescanning it is not enough. -/
theorem rescan_from_nonStrong_not_allLiveBlack :
    cfgD.barrier = .dijkstra ∧ (∀ s₀ ops, ¬ Run cfgD (initMark s₀) ops sBlackWhite) ∧
      Run cfgD (rescan sBlackWhite) [] (rescan sBlackWhite) ∧ ScansOnly ([] : List (Op 2)) ∧
      NoGrey (rescan sBlackWhite) ∧ ¬ AllLiveBlack (rescan sBlackWhite) := by
  refine ⟨rfl, ?_, Run.nil _, fun _ h => absurd h List.not_mem_nil, by decide,
    fun h => absurd (h 1 (Live.step (x := 0) (Live.root rfl) rfl)) (by decide)⟩
  intro s₀ ops hrun
  exact absurd (strong_run_of_dijkstra rfl (strong_initMark s₀) hrun) (by decide)

/-! ## The enabling conditions of the step relation cannot be dropped from the preservation
theorems (2- and 3-object states, one non-enabled step each) -/

/-- `Isolated s a` on allocation cannot be dropped from Dijkstra preservation (a 3-object
state): re-coloring the non-isolated
object `1` white and making it a root (all other enabling conditions hold) breaks the strong
invariant. -/
theorem dijkstra_unisolated_alloc_breaks_strong :
    cfgDW.barrier = .dijkstra ∧ Strong sDone ∧ cfgDW.allocOk .white = true ∧
      sDone.root 1 = false ∧ ¬ Isolated sDone 1 ∧
      ¬ (Op.alloc 1 .white).Enabled cfgDW sDone ∧
      ¬ Strong ((Op.alloc 1 .white).apply cfgDW sDone) :=
  ⟨rfl, by decide, rfl, rfl, by decide, fun h => absurd h.2.2 (by decide), by decide⟩

/-- `Isolated s a` on allocation cannot be dropped from Yuasa preservation, even for black
allocation (a 3-object state):
re-coloring the protecting grey object `1` black leaves `2` unprotected. -/
theorem yuasa_nonWhiteAlloc_unisolated_alloc_breaks_weak :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Weak sWeakNotStrong ∧ RootsProtected sWeakNotStrong ∧ cfgY.allocOk .black = true ∧
      sWeakNotStrong.root 1 = false ∧ ¬ Isolated sWeakNotStrong 1 ∧
      ¬ (Op.alloc 1 .black).Enabled cfgY sWeakNotStrong ∧
      ¬ Weak ((Op.alloc 1 .black).apply cfgY sWeakNotStrong) := by
  refine ⟨rfl, blackOnly_nonWhite, weak_sWeakNotStrong,
    rootsProtected_of_rootsNonWhite (by decide), rfl, rfl, by decide,
    fun h => absurd h.2.2 (by decide), ?_⟩
  intro hw
  exact not_greyProtected_of_noGrey (s := (Op.alloc 1 .black).apply cfgY sWeakNotStrong)
    (by decide) (hw 0 2 rfl rfl rfl)

/-- `Isolated s a` on allocation cannot be dropped from load-barrier preservation, even for
black allocation (a 3-object state):
an object allocated black with a pointer to a white object creates a black-to-white edge. -/
theorem shadeLoads_nonWhiteAlloc_unisolated_alloc_breaks_strong :
    cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Strong sChain ∧ RootsNonWhite sChain ∧ cfgU.allocOk .black = true ∧
      sChain.root 1 = false ∧ ¬ Isolated sChain 1 ∧
      ¬ (Op.alloc 1 .black).Enabled cfgU sChain ∧
      ¬ Strong ((Op.alloc 1 .black).apply cfgU sChain) :=
  ⟨rfl, blackOnly_nonWhite, by decide, by decide, rfl, rfl, by decide,
    fun h => absurd h.2.2 (by decide), by decide⟩

/-- The held-pointer condition on stores cannot be dropped from load-barrier preservation (a
3-object state): if the mutator
could store the live but unheld white object `2` into the black root `0` (bypassing the load
barrier), the strong invariant would break without a heap barrier. -/
theorem shadeLoads_nonWhiteAlloc_store_of_unheld_value_breaks_strong :
    cfgU.barrier = .none ∧ cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Strong sChain ∧ RootsNonWhite sChain ∧ Live sChain 2 ∧
      ¬ (Op.store 0 2).Enabled cfgU sChain ∧
      ¬ Strong ((Op.store 0 2).apply cfgU sChain) :=
  ⟨rfl, rfl, blackOnly_nonWhite, by decide, by decide, live_two_sChain,
    by show ¬ sChain.root 2 = true; decide, by decide⟩

/-- `RootsNonWhite` in the pre-state cannot be dropped from load-barrier preservation (a
2-object state): storing a white root into
a black object (no heap barrier) breaks the strong invariant. -/
theorem shadeLoads_store_of_whiteRoot_breaks_strong :
    cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Strong sWhiteRootUnprotected ∧ ¬ RootsNonWhite sWhiteRootUnprotected ∧
      Step cfgU sWhiteRootUnprotected (store .none sWhiteRootUnprotected 0 1) ∧
      ¬ Strong (store .none sWhiteRootUnprotected 0 1) :=
  ⟨rfl, blackOnly_nonWhite, by decide, by decide, ⟨.store 0 1, rfl, rfl⟩, by decide⟩

/-! ## Concrete final states -/

/-- The final state of `traceLostObject` without barrier or load shading: edges `0 → 1` and
`0 → 2`, root `0`, colors black, black, white. -/
theorem sLost_eq : sLost = mk 3 [(0, 1), (0, 2)] [0] [.black, .black, .white] :=
  St.ext' (by funext u v; revert u v; decide) (by funext r; revert r; decide)
    (by funext x; revert x; decide)

/-- The final state of `traceLoadLost` under `cfgD0`: edge `0 → 1`, roots `0` and `2`, colors
black, black, white. -/
theorem sLoadLost_eq : sLoadLost = mk 3 [(0, 1)] [0, 2] [.black, .black, .white] :=
  St.ext' (by funext u v; revert u v; decide) (by funext r; revert r; decide)
    (by funext x; revert x; decide)

/-- The final state of `traceWhiteAlloc` under `cfgDW`: no edges, roots `0` and `1`, colors
black, white. -/
theorem sWhiteAlloc_eq : sWhiteAlloc = mk 2 [] [0, 1] [.black, .white] :=
  St.ext' (by funext u v; revert u v; decide) (by funext r; revert r; decide)
    (by funext x; revert x; decide)

/-! ## Floating garbage -/

/-- `AllLiveBlack` is soundness, not completeness: a Yuasa run from the start of a marking
cycle that allocates `1` black and drops it ends with no grey object, every live object black,
and the unreachable object `1` black (floating garbage that this cycle does not free). -/
theorem floatingGarbage_yuasa_run :
    Run cfgY (initMark hAlloc) [.alloc 1 .black, .drop 1, .scan 0]
        (runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc)) ∧
      NoGrey (runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc)) ∧
      AllLiveBlack (runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc)) ∧
      ¬ Live (runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc)) 1 ∧
      (runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc)).color 1 = .black := by
  refine ⟨Run.cons ⟨rfl, rfl, by decide⟩ (Run.cons trivial (Run.cons rfl (Run.nil _))),
    by decide, allLiveBlack_of_closed _ (by decide) (by decide), ?_, rfl⟩
  intro h
  have := Live.subset (s := runOps cfgY [.alloc 1 .black, .drop 1, .scan 0] (initMark hAlloc))
    (fun x => x.val ≠ 1) (by decide) (by decide) h
  exact this rfl

/-! ## Non-vacuity of the soundness theorems -/

theorem strong_preserved_of_dijkstra_nonvacuous :
    cfgD.barrier = .dijkstra ∧ Strong sChainR ∧ Step cfgD sChainR (store .dijkstra sChainR 0 2) :=
  ⟨rfl, by decide, ⟨.store 0 2, rfl, rfl⟩⟩

theorem weak_rootsProtected_preserved_of_yuasa_of_nonWhiteAlloc_nonvacuous :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Weak sWeakNotStrong ∧ RootsProtected sWeakNotStrong ∧
      Step cfgY sWeakNotStrong (erase .yuasa sWeakNotStrong 1 2) :=
  ⟨rfl, blackOnly_nonWhite, weak_sWeakNotStrong, rootsProtected_of_rootsNonWhite (by decide),
    ⟨.erase 1 2, trivial, rfl⟩⟩

/-- Non-vacuity of load-barrier preservation with no heap barrier, exercising a store of a
pointer that was shaded when loaded. -/
theorem strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc_nonvacuous :
    cfgU.barrier = .none ∧ cfgU.shadeLoads = true ∧
      (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧ Strong sChainShaded ∧
      RootsNonWhite sChainShaded ∧ Step cfgU sChainShaded (store .none sChainShaded 0 2) :=
  ⟨rfl, rfl, blackOnly_nonWhite, by decide, by decide, ⟨.store 0 2, rfl, rfl⟩⟩

theorem rootsProtected_alloc_iff_ne_white_nonvacuous :
    RootsProtected sFree ∧ Isolated sFree 1 :=
  ⟨rootsProtected_of_rootsNonWhite (by decide), by decide⟩

theorem allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark_nonvacuous :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Run cfgY (initMark hChain) (traceLostObject ++ [.scan 2])
        (runOps cfgY (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgY (traceLostObject ++ [.scan 2]) (initMark hChain)) :=
  ⟨rfl, blackOnly_nonWhite, yuasa_traceLostObject_then_scan_safe.1,
    yuasa_traceLostObject_then_scan_safe.2.1⟩

theorem allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run_nonvacuous :
    cfgDW.barrier = .dijkstra ∧ cfgDW.allocOk .white = true ∧
      Run cfgDW (initMark hAlloc) traceWhiteAlloc sWhiteAlloc ∧
      Run cfgDW (rescan sWhiteAlloc) [.scan 1] (scan (rescan sWhiteAlloc) 1) ∧
      ScansOnly [(Op.scan 1 : Op 2)] ∧ NoGrey (scan (rescan sWhiteAlloc) 1) :=
  ⟨rfl, rfl, run_traceWhiteAlloc cfgDW rfl, dijkstra_whiteAlloc_then_rescan_safe.1,
    by simp [ScansOnly, Op.isScan], dijkstra_whiteAlloc_then_rescan_safe.2.1⟩

/-- Non-vacuity of load-barrier marking with no heap barrier: the lost-object interleaving
under shaded loads, followed by a scan of the shaded object. -/
theorem allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark_nonvacuous :
    cfgU.barrier = .none ∧ cfgU.shadeLoads = true ∧
      (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Run cfgU (initMark hChain) (traceLostObject ++ [.scan 2])
        (runOps cfgU (traceLostObject ++ [.scan 2]) (initMark hChain)) ∧
      NoGrey (runOps cfgU (traceLostObject ++ [.scan 2]) (initMark hChain)) :=
  ⟨rfl, rfl, blackOnly_nonWhite, shadeLoads_traceLostObject_then_scan_safe.1,
    shadeLoads_traceLostObject_then_scan_safe.2.1⟩

/-! ## Whole-cycle role of the enabling conditions inside `Run`

Each theorem below runs from the root snapshot `initMark hChain` (root `0` → `1` → `2`) and
breaks exactly one enabling condition of one step: the step sequence is therefore not a `Run`,
while every other hypothesis of the corresponding marking theorem holds and its conclusion
fails. -/

/-- An enabled scan of `0`, then a black allocation of the object `1`, which is not isolated
(it still points to the white object `2`). -/
def traceUnisolatedBlackAlloc : List (Op 3) := [.scan 0, .alloc 1 .black]

/-- An enabled scan of `0`, a heap store `0 → 2` of the object `2`, which is reachable but not
held in the roots (it was never loaded), then an erase of `1 → 2` and an enabled scan of `1`. -/
def traceUnheldStore : List (Op 3) := [.scan 0, .store 0 2, .erase 1 2, .scan 1]

theorem not_run_traceUnisolatedBlackAlloc (cfg : Config) (s : St 3) :
    ¬ Run cfg (initMark hChain) traceUnisolatedBlackAlloc s := by
  intro h
  cases h with
  | cons _ h2 =>
    cases h2 with
    | cons hen _ =>
      have hiso : Isolated (scan (initMark hChain) 0) 1 := hen.2.2
      exact absurd hiso (by decide)

theorem not_run_traceUnheldStore (cfg : Config) (s : St 3) :
    ¬ Run cfg (initMark hChain) traceUnheldStore s := by
  intro h
  cases h with
  | cons _ h2 =>
    cases h2 with
    | cons hen _ =>
      have hroot : (scan (initMark hChain) 0).root 2 = true := hen
      exact absurd hroot (by decide)

/-- `Isolated s a` on allocation inside `Run` cannot be dropped from load-barrier marking safety,
even for black allocation (a 3-object root snapshot and a 2-step sequence): with no heap barrier, shaded loads and black allocation, the scan of `0` is a run
from the root snapshot, the allocation of `1` satisfies every enabling condition except
isolation, and the final state has no grey object while the reachable object `2` is white. -/
theorem shadeLoads_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack :
    cfgU.barrier = .none ∧ cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Run cfgU (initMark hChain) [.scan 0] (runOps cfgU [.scan 0] (initMark hChain)) ∧
      cfgU.allocOk .black = true ∧ (runOps cfgU [.scan 0] (initMark hChain)).root 1 = false ∧
      ¬ Isolated (runOps cfgU [.scan 0] (initMark hChain)) 1 ∧
      (∀ s, ¬ Run cfgU (initMark hChain) traceUnisolatedBlackAlloc s) ∧
      NoGrey (runOps cfgU traceUnisolatedBlackAlloc (initMark hChain)) ∧
      ¬ AllLiveBlack (runOps cfgU traceUnisolatedBlackAlloc (initMark hChain)) := by
  refine ⟨rfl, rfl, blackOnly_nonWhite, Run.cons rfl (Run.nil _), rfl, rfl, by decide,
    not_run_traceUnisolatedBlackAlloc cfgU, by decide, ?_⟩
  intro hall
  exact absurd (hall 2 (Live.step (x := 1) (Live.root rfl) rfl)) (by decide)

/-- The held-pointer condition on stores inside `Run` cannot be dropped from load-barrier marking
safety (a 3-object root snapshot and a 4-step sequence): with no
heap barrier, shaded loads and black allocation, storing the reachable but unheld white object
`2` (skipping the shaded load of `traceLostObject`) is the only non-enabled step, and the final
state has no grey object while the reachable object `2` is white. -/
theorem shadeLoads_nonWhiteAlloc_unheld_store_cycle_not_allLiveBlack :
    cfgU.barrier = .none ∧ cfgU.shadeLoads = true ∧ (∀ c, cfgU.allocOk c = true → c ≠ .white) ∧
      Run cfgU (initMark hChain) [.scan 0] (runOps cfgU [.scan 0] (initMark hChain)) ∧
      Live (runOps cfgU [.scan 0] (initMark hChain)) 2 ∧
      (runOps cfgU [.scan 0] (initMark hChain)).root 2 = false ∧
      Run cfgU (runOps cfgU [.scan 0, .store 0 2] (initMark hChain)) [.erase 1 2, .scan 1]
        (runOps cfgU traceUnheldStore (initMark hChain)) ∧
      (∀ s, ¬ Run cfgU (initMark hChain) traceUnheldStore s) ∧
      NoGrey (runOps cfgU traceUnheldStore (initMark hChain)) ∧
      ¬ AllLiveBlack (runOps cfgU traceUnheldStore (initMark hChain)) := by
  refine ⟨rfl, rfl, blackOnly_nonWhite, Run.cons rfl (Run.nil _),
    Live.step (x := 1) (Live.step (x := 0) (Live.root rfl) rfl) rfl, rfl,
    Run.cons trivial (Run.cons rfl (Run.nil _)), not_run_traceUnheldStore cfgU, by decide, ?_⟩
  intro hall
  exact absurd (hall 2 (Live.step (x := 0) (Live.root rfl) rfl)) (by decide)

/-- `Isolated s a` on allocation inside `Run` cannot be dropped from Yuasa marking safety, even
for black allocation (a 3-object root snapshot and a 2-step sequence): the scan of `0` is a run from the root snapshot, the allocation of `1` satisfies
every enabling condition except isolation, and the final state has no grey object while the
reachable object `2` is white. -/
theorem yuasa_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Run cfgY (initMark hChain) [.scan 0] (runOps cfgY [.scan 0] (initMark hChain)) ∧
      cfgY.allocOk .black = true ∧ (runOps cfgY [.scan 0] (initMark hChain)).root 1 = false ∧
      ¬ Isolated (runOps cfgY [.scan 0] (initMark hChain)) 1 ∧
      (∀ s, ¬ Run cfgY (initMark hChain) traceUnisolatedBlackAlloc s) ∧
      NoGrey (runOps cfgY traceUnisolatedBlackAlloc (initMark hChain)) ∧
      ¬ AllLiveBlack (runOps cfgY traceUnisolatedBlackAlloc (initMark hChain)) := by
  refine ⟨rfl, blackOnly_nonWhite, Run.cons rfl (Run.nil _), rfl, rfl, by decide,
    not_run_traceUnisolatedBlackAlloc cfgY, by decide, ?_⟩
  intro hall
  exact absurd (hall 2 (Live.step (x := 1) (Live.root rfl) rfl)) (by decide)

/-- `Isolated s a` on allocation inside the concurrent `Run` cannot be dropped from Dijkstra
marking with a final rescan (a 3-object root snapshot, a 2-step sequence and an empty drain): the scan of `0` is a run from the root snapshot, the black allocation of `1`
satisfies every enabling condition except isolation, and after the rescan (both roots are
already black) the empty drain ends with no grey object while the reachable object `2` is
white. -/
theorem dijkstra_unisolated_alloc_cycle_rescan_not_allLiveBlack :
    cfgD.barrier = .dijkstra ∧
      Run cfgD (initMark hChain) [.scan 0] (runOps cfgD [.scan 0] (initMark hChain)) ∧
      cfgD.allocOk .black = true ∧ (runOps cfgD [.scan 0] (initMark hChain)).root 1 = false ∧
      ¬ Isolated (runOps cfgD [.scan 0] (initMark hChain)) 1 ∧
      (∀ s, ¬ Run cfgD (initMark hChain) traceUnisolatedBlackAlloc s) ∧
      Run cfgD (rescan (runOps cfgD traceUnisolatedBlackAlloc (initMark hChain))) []
        (rescan (runOps cfgD traceUnisolatedBlackAlloc (initMark hChain))) ∧
      ScansOnly ([] : List (Op 3)) ∧
      NoGrey (rescan (runOps cfgD traceUnisolatedBlackAlloc (initMark hChain))) ∧
      ¬ AllLiveBlack (rescan (runOps cfgD traceUnisolatedBlackAlloc (initMark hChain))) := by
  refine ⟨rfl, Run.cons rfl (Run.nil _), rfl, rfl, by decide,
    not_run_traceUnisolatedBlackAlloc cfgD, Run.nil _, fun _ h => absurd h List.not_mem_nil,
    by decide, ?_⟩
  intro hall
  exact absurd (hall 2 (Live.step (x := 1) (Live.root rfl) rfl)) (by decide)

/-- `Isolated s a` on allocation cannot be dropped from Dijkstra preservation even for black
allocation (a 3-object state): the allocation step runs no heap barrier, so re-coloring the
object `1`, which points to the white object `2`, black creates a black-to-white edge. -/
theorem dijkstra_unisolated_blackAlloc_breaks_strong :
    cfgD.barrier = .dijkstra ∧ Strong sChain ∧ cfgD.allocOk .black = true ∧
      sChain.root 1 = false ∧ ¬ Isolated sChain 1 ∧
      ¬ (Op.alloc 1 .black).Enabled cfgD sChain ∧
      ¬ Strong ((Op.alloc 1 .black).apply cfgD sChain) :=
  ⟨rfl, by decide, rfl, rfl, by decide, fun h => absurd h.2.2 (by decide), by decide⟩

theorem not_live_one_initMark_hAlloc : ¬ Live (initMark hAlloc) 1 := by
  intro h
  have := Live.subset (s := initMark hAlloc) (fun x => x.val ≠ 1) (by decide) (by decide) h
  exact this rfl

theorem not_live_one_scan_initMark_hAlloc : ¬ Live (runOps cfgY [.scan 0] (initMark hAlloc)) 1 := by
  intro h
  have := Live.subset (s := runOps cfgY [.scan 0] (initMark hAlloc)) (fun x => x.val ≠ 1)
    (by decide) (by decide) h
  exact this rfl

/-- The liveness condition on root loads inside `Run` cannot be dropped from Yuasa marking safety
(a 2-object root snapshot and a 2-step sequence): loading the unreachable white object `1`
(unshaded) is the only non-enabled step, and after the scan of the root `0` no object is grey
while the root `1` is white. -/
theorem yuasa_load_of_unreachable_cycle_not_allLiveBlack :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      ¬ Live (initMark hAlloc) 1 ∧
      Run cfgY (runOps cfgY [.load 1] (initMark hAlloc)) [.scan 0]
        (runOps cfgY [.load 1, .scan 0] (initMark hAlloc)) ∧
      (∀ s, ¬ Run cfgY (initMark hAlloc) [.load 1, .scan 0] s) ∧
      NoGrey (runOps cfgY [.load 1, .scan 0] (initMark hAlloc)) ∧
      ¬ AllLiveBlack (runOps cfgY [.load 1, .scan 0] (initMark hAlloc)) := by
  refine ⟨rfl, blackOnly_nonWhite, not_live_one_initMark_hAlloc, Run.cons rfl (Run.nil _), ?_,
    by decide, ?_⟩
  · intro s h
    cases h with
    | cons hen _ => exact not_live_one_initMark_hAlloc hen
  · intro hall
    exact absurd (hall 1 (Live.root rfl)) (by decide)

/-- The condition on stored pointers inside `Run` cannot be dropped from Yuasa marking safety (a
2-object root snapshot and a 2-step sequence): after the scan of the root `0`, storing the
unreachable white object `1` into `0` is the only non-enabled step, and the final state has no
grey object while the reachable object `1` is white. -/
theorem yuasa_store_of_unreachable_cycle_not_allLiveBlack :
    cfgY.barrier = .yuasa ∧ (∀ c, cfgY.allocOk c = true → c ≠ .white) ∧
      Run cfgY (initMark hAlloc) [.scan 0] (runOps cfgY [.scan 0] (initMark hAlloc)) ∧
      ¬ Live (runOps cfgY [.scan 0] (initMark hAlloc)) 1 ∧
      (∀ s, ¬ Run cfgY (initMark hAlloc) [.scan 0, .store 0 1] s) ∧
      NoGrey (runOps cfgY [.scan 0, .store 0 1] (initMark hAlloc)) ∧
      ¬ AllLiveBlack (runOps cfgY [.scan 0, .store 0 1] (initMark hAlloc)) := by
  refine ⟨rfl, blackOnly_nonWhite, Run.cons rfl (Run.nil _), not_live_one_scan_initMark_hAlloc,
    ?_, by decide, ?_⟩
  · intro s h
    cases h with
    | cons _ h2 =>
      cases h2 with
      | cons hen _ =>
        have hroot : (scan (initMark hAlloc) 0).root 1 = true := hen
        exact absurd hroot (by decide)
  · intro hall
    exact absurd (hall 1 (Live.step (x := 0) (Live.root rfl) rfl)) (by decide)

end Toy.Tricolor
