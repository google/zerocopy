import Toy.Tricolor.Preservation

/-!
# Whole marking cycles

A marking cycle starts from `initMark s₀` (every root shaded at once, everything else white:
a stop-the-world root snapshot) and runs enabled steps. These theorems combine the preservation results with end-of-marking safety.
-/

namespace Toy.Tricolor

variable {n : Nat}

theorem strong_initMark (s : St n) : Strong (initMark s) := by
  intro x y _ hx _
  simp only [initMark] at hx
  split at hx <;> cases hx

theorem weak_initMark (s : St n) : Weak (initMark s) := weak_of_strong (strong_initMark s)

theorem rootsNonWhite_initMark (s : St n) : RootsNonWhite (initMark s) := by
  intro r hr hw
  have hr' : s.root r = true := hr
  simp [initMark, hr'] at hw

theorem rootsProtected_initMark (s : St n) : RootsProtected (initMark s) :=
  rootsProtected_of_rootsNonWhite (rootsNonWhite_initMark s)

/-- `ScansOnly ops`: every step in `ops` is a collector scan (the mutator is paused). -/
def ScansOnly (ops : List (Op n)) : Prop := ∀ op ∈ ops, op.isScan = true

theorem Op.eq_scan_of_isScan {op : Op n} (h : op.isScan = true) : ∃ g, op = .scan g := by
  cases op <;> first | exact ⟨_, rfl⟩ | cases h

theorem strong_rootsNonWhite_of_scansOnly_run {cfg : Config} {s s' : St n} {ops : List (Op n)}
    (hs : Strong s) (hr : RootsNonWhite s) (hrun : Run cfg s ops s') (hscan : ScansOnly ops) :
    Strong s' ∧ RootsNonWhite s' := by
  induction hrun with
  | nil => exact ⟨hs, hr⟩
  | @cons s _ op _ _ _ ih =>
    obtain ⟨g, rfl⟩ := Op.eq_scan_of_isScan (hscan _ (List.mem_cons_self ..))
    exact ih (strong_scan hs g) (rootsNonWhite_scan hr g)
      (fun op h => hscan op (List.mem_cons_of_mem _ h))

/-- **Paused-mutator marking from a root snapshot.** Under any configuration, a scans-only run
from the start of a marking cycle that reaches a state with no grey object ends with every live
object black. -/
theorem allLiveBlack_of_noGrey_of_scansOnly_run_from_initMark {cfg : Config} {s₀ s : St n}
    {ops : List (Op n)} (hrun : Run cfg (initMark s₀) ops s) (hscan : ScansOnly ops)
    (hng : NoGrey s) : AllLiveBlack s := by
  obtain ⟨hs, hr⟩ := strong_rootsNonWhite_of_scansOnly_run (strong_initMark s₀)
    (rootsNonWhite_initMark s₀) hrun hscan
  exact allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite hng hs hr

/-- **Yuasa marking safety (non-white allocation, root snapshot).** With the Yuasa barrier and
an allocator that never allocates white, any run of `Run cfg` from the start of a marking cycle
(`initMark`: every root shaded at once) that reaches a state with no grey object ends with every
live object black. `Run` admits only enabled steps: heap stores of pointers held in the roots,
root loads of live objects and allocations of isolated non-root objects (dropping isolation:
`yuasa_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack`). There is no hypothesis on
root-load shading and no root rescan. -/
theorem allLiveBlack_of_noGrey_of_yuasa_of_nonWhiteAlloc_run_from_initMark {cfg : Config}
    (hb : cfg.barrier = .yuasa)
    (halloc : ∀ c, cfg.allocOk c = true → c ≠ .white) {s₀ s : St n} {ops : List (Op n)}
    (hrun : Run cfg (initMark s₀) ops s) (hng : NoGrey s) : AllLiveBlack s := by
  obtain ⟨hw, hr⟩ := weak_rootsProtected_run_of_yuasa_of_nonWhiteAlloc hb halloc (weak_initMark s₀)
    (rootsProtected_initMark s₀) hrun
  exact allLiveBlack_of_noGrey_of_weak_of_rootsProtected hng hw hr

/-- **Remark phase.** From any state satisfying the strong invariant, rescanning the roots and
then draining grey objects with collector scans only (mutator paused) until no grey object
remains ends with every live object black, whatever the root colors were. -/
theorem allLiveBlack_of_strong_of_rescan_of_scansOnly_run {cfg : Config} {s s' : St n}
    {ops : List (Op n)} (hs : Strong s) (hrun : Run cfg (rescan s) ops s')
    (hscan : ScansOnly ops) (hng : NoGrey s') : AllLiveBlack s' := by
  obtain ⟨hs', hr'⟩ := strong_rootsNonWhite_of_scansOnly_run (strong_rescan hs)
    (rootsNonWhite_rescan s) hrun hscan
  exact allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite hng hs' hr'

/-- **Dijkstra marking with a final rescan and a paused drain, for every allocation color.**
With the Dijkstra barrier (any root-load discipline, any allocation colors), a concurrent run of
`Run cfg` from the start of a marking cycle (enabled steps only; allocations take isolated
non-root objects, and dropping isolation fails:
`dijkstra_unisolated_alloc_cycle_rescan_not_allLiveBlack`) followed by a root rescan and a
scans-only run of `Run cfg` that reaches a state with no grey object ends with every live
object black. -/
theorem allLiveBlack_of_noGrey_of_dijkstra_run_of_rescan_of_scansOnly_run {cfg : Config}
    (hb : cfg.barrier = .dijkstra) {s₀ s s' : St n} {ops ops₂ : List (Op n)}
    (hrun : Run cfg (initMark s₀) ops s) (hrem : Run cfg (rescan s) ops₂ s')
    (hscan : ScansOnly ops₂) (hng : NoGrey s') : AllLiveBlack s' :=
  allLiveBlack_of_strong_of_rescan_of_scansOnly_run
    (strong_run_of_dijkstra hb (strong_initMark s₀) hrun) hrem hscan hng

/-- **Load-barrier marking without a rescan, under any heap barrier.** With shaded root loads
and an allocator that never allocates white (any heap barrier, including none), any run of
`Run cfg` from the start of a marking cycle that reaches a state with no grey object ends with
every live object black. `Run` admits only enabled steps; the load-bearing enabling conditions
are that heap stores write pointers held in the roots
(`shadeLoads_nonWhiteAlloc_unheld_store_cycle_not_allLiveBlack`) and that allocations take
isolated objects (`shadeLoads_nonWhiteAlloc_unisolated_alloc_cycle_not_allLiveBlack`). -/
theorem allLiveBlack_of_noGrey_of_shadeLoads_of_nonWhiteAlloc_run_from_initMark {cfg : Config}
    (hsh : cfg.shadeLoads = true)
    (halloc : ∀ c, cfg.allocOk c = true → c ≠ .white) {s₀ s : St n} {ops : List (Op n)}
    (hrun : Run cfg (initMark s₀) ops s) (hng : NoGrey s) : AllLiveBlack s := by
  obtain ⟨hs, hr⟩ := Run.invariant (fun t => Strong t ∧ RootsNonWhite t)
    (fun _ _ h hst =>
      strong_rootsNonWhite_preserved_of_shadeLoads_of_nonWhiteAlloc hsh halloc h.1 h.2 hst)
    hrun ⟨strong_initMark s₀, rootsNonWhite_initMark s₀⟩
  exact allLiveBlack_of_noGrey_of_strong_of_rootsNonWhite hng hs hr

end Toy.Tricolor
