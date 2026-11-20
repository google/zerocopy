import ToyParMove.Lanes
import ToyParMove.Basic

/-!
Moves into sub-register lanes inside a parallel move. With lane destinations, "distinct
destinations" is not enough: distinct `(register, lane)` pairs can still overlap, and then the
parallel move depends on the order of its entries. Pairwise disjoint destination lanes per
register (`LaneWF`) suffice; for positive-width lanes `LaneWF` implies distinct destinations.
-/
set_option linter.unusedSectionVars false

namespace Toy.ParMove

/-- A lane move copies `wid` bits from bit `soff` of register `sreg` into bit `doff` of register
`dreg` (a `preserveUpper` write). -/
structure LaneMove (R : Type) where
  dreg : R
  doff : Nat
  sreg : R
  soff : Nat
  wid : Nat
deriving DecidableEq, Repr

/-- The destination lane of a lane move. -/
def LaneMove.dst {R : Type} (m : LaneMove R) : Lane := ⟨m.doff, m.wid⟩
/-- The source lane of a lane move. -/
def LaneMove.src {R : Type} (m : LaneMove R) : Lane := ⟨m.soff, m.wid⟩

section LaneMoveDefs
variable {R : Type} [DecidableEq R] {n : Nat}

/-- The write performed by lane move `m` with the lane value read from register file `reads`,
applied to register file `τ`. -/
def laneWrite (reads : R → BitVec n) (τ : R → BitVec n) (m : LaneMove R) : R → BitVec n :=
  upd τ m.dreg (putLane m.dst (getLane m.src (reads m.sreg)) (τ m.dreg))

/-- One sequential lane move: read the source lane from the *current* register file. -/
def laneStep (ρ : R → BitVec n) (m : LaneMove R) : R → BitVec n := laneWrite ρ ρ m

/-- Left-to-right execution of lane moves. -/
def runLanes (ms : List (LaneMove R)) (ρ : R → BitVec n) : R → BitVec n := ms.foldl laneStep ρ

/-- **Parallel lane-move semantics** (list-order reading): every source lane is read from the
*old* register file `ρ`; the destination-lane writes are then applied in list order. When two
destination lanes overlap, the later entry's bits win at the overlap (the opposite tie-break
from the whole-register `pmove`, where the first entry wins). -/
def lanePMove (M : List (LaneMove R)) (ρ : R → BitVec n) : R → BitVec n :=
  M.foldl (laneWrite ρ) ρ

/-- **Lane well-formedness:** destination lanes of moves into the same register are pairwise
disjoint. -/
def LaneWF (M : List (LaneMove R)) : Prop :=
  M.Pairwise fun m₁ m₂ => m₁.dreg = m₂.dreg → m₁.dst.Disjoint m₂.dst

/-- The naive lifting of "distinct destinations": the `(register, lane)` pairs are distinct. -/
def DistinctDstLanes (M : List (LaneMove R)) : Prop :=
  (M.map fun m => (m.dreg, m.dst)).Nodup

/-- **Lane-topological order:** no move writes bits that a later move reads. -/
def LaneTopological (ms : List (LaneMove R)) : Prop :=
  ms.Pairwise fun e l => e.dreg = l.sreg → e.dst.Disjoint l.src

instance (M : List (LaneMove R)) : Decidable (LaneWF M) := inferInstanceAs (Decidable (M.Pairwise _))
instance (M : List (LaneMove R)) : Decidable (DistinctDstLanes M) :=
  inferInstanceAs (Decidable (List.Nodup _))
instance (M : List (LaneMove R)) : Decidable (LaneTopological M) :=
  inferInstanceAs (Decidable (M.Pairwise _))

end LaneMoveDefs

section LaneMoveProofs
variable {R : Type} [DecidableEq R] {n : Nat}

theorem disjoint_symm {L₁ L₂ : Lane} (h : L₁.Disjoint L₂) : L₂.Disjoint L₁ := by
  unfold Lane.Disjoint at *; omega

/-- Two writes whose destination lanes are disjoint whenever they hit the same register commute. -/
theorem laneWrite_comm (reads τ : R → BitVec n) {m₁ m₂ : LaneMove R}
    (h : m₁.dreg = m₂.dreg → m₁.dst.Disjoint m₂.dst) :
    laneWrite reads (laneWrite reads τ m₁) m₂ = laneWrite reads (laneWrite reads τ m₂) m₁ := by
  funext r
  by_cases hr : m₁.dreg = m₂.dreg
  · have hd := h hr
    simp only [laneWrite, upd]
    by_cases h1 : r = m₂.dreg
    · have h1' : r = m₁.dreg := h1.trans hr.symm
      simp only [h1, ite_true, ← hr]
      exact (putLane_comm_of_disjoint hd _ _ _).symm
    · have h1' : ¬ r = m₁.dreg := fun e => h1 (e.trans hr)
      simp [h1, h1']
  · simp only [laneWrite, upd]
    by_cases h1 : r = m₂.dreg
    · have h1' : ¬ r = m₁.dreg := fun e => hr (e.symm.trans h1)
      simp [h1, Ne.symm hr]
    · by_cases h2 : r = m₁.dreg
      · simp [h2, hr]
      · simp [h1, h2]

theorem foldl_laneWrite_perm (reads : R → BitVec n) {M M' : List (LaneMove R)}
    (hp : M.Perm M') : LaneWF M → ∀ (τ : R → BitVec n),
    M.foldl (laneWrite reads) τ = M'.foldl (laneWrite reads) τ := by
  induction hp with
  | nil => intro _ _; rfl
  | cons x _ ih =>
    intro hwf τ
    exact ih (List.pairwise_cons.1 hwf).2 _
  | swap x y l =>
    intro hwf τ
    have h1 := List.pairwise_cons.1 hwf
    have hyx : y.dreg = x.dreg → y.dst.Disjoint x.dst := h1.1 x (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    rw [laneWrite_comm reads τ hyx]
  | trans h₁₂ _ ih₁ ih₂ =>
    intro hwf τ
    have hwf₂ : LaneWF _ := h₁₂.pairwise hwf (fun h e => disjoint_symm (h e.symm))
    exact (ih₁ hwf τ).trans (ih₂ hwf₂ τ)

/-- **Order independence for disjoint destination lanes.** If destination lanes of moves into the
same register are pairwise disjoint, reordering the lane moves does not change the parallel
lane-move semantics. -/
theorem lanePMove_perm_invariant_of_laneWF {M M' : List (LaneMove R)} (hwf : LaneWF M)
    (hp : M.Perm M') (ρ : R → BitVec n) : lanePMove M ρ = lanePMove M' ρ :=
  foldl_laneWrite_perm ρ hp hwf ρ

theorem foldl_laneWrite_congr_reads {reads₁ reads₂ : R → BitVec n} :
    ∀ (ms : List (LaneMove R)),
      (∀ l ∈ ms, getLane l.src (reads₁ l.sreg) = getLane l.src (reads₂ l.sreg)) →
      ∀ τ : R → BitVec n, ms.foldl (laneWrite reads₁) τ = ms.foldl (laneWrite reads₂) τ
  | [], _, _ => rfl
  | m :: ms, h, τ => by
    simp only [List.foldl_cons]
    have hm : laneWrite reads₁ τ m = laneWrite reads₂ τ m := by
      simp only [laneWrite, h m (List.mem_cons_self ..)]
    rw [hm]
    exact foldl_laneWrite_congr_reads ms (fun l hl => h l (List.mem_cons_of_mem _ hl)) _

/-- Lane-topological order realizes the list-order parallel reading (no disjointness needed). -/
theorem runLanes_eq_lanePMove_of_topological :
    ∀ {ms : List (LaneMove R)}, LaneTopological ms → ∀ ρ : R → BitVec n,
      runLanes ms ρ = lanePMove ms ρ
  | [], _, _ => rfl
  | m :: ms, htop, ρ => by
    have ht := List.pairwise_cons.1 htop
    show runLanes ms (laneStep ρ m) = ms.foldl (laneWrite ρ) (laneWrite ρ ρ m)
    rw [runLanes_eq_lanePMove_of_topological ht.2]
    unfold lanePMove laneStep
    apply foldl_laneWrite_congr_reads
    intro l hl
    simp only [laneWrite, upd]
    by_cases hr : l.sreg = m.dreg
    · simp only [hr, ite_true]
      exact getLane_putLane_of_disjoint (disjoint_symm (disjoint_symm (ht.1 l hl hr.symm))) _ _
    · simp [hr]

/-- **Soundness for disjoint destination lanes.** If the parallel lane move `M` has pairwise
disjoint destination lanes (per register) and `ms` is a reordering of `M` in which no move writes
bits read by a later move, then executing `ms` sequentially yields exactly the parallel lane
move `M`. -/
theorem runLanes_eq_lanePMove_of_laneWF_of_topological {M ms : List (LaneMove R)}
    (hwf : LaneWF M) (hp : ms.Perm M) (htop : LaneTopological ms) (ρ : R → BitVec n) :
    runLanes ms ρ = lanePMove M ρ := by
  rw [runLanes_eq_lanePMove_of_topological htop]
  exact (lanePMove_perm_invariant_of_laneWF hwf hp.symm ρ).symm

end LaneMoveProofs

/-- For positive-width lane moves, `LaneWF` implies distinct `(register, lane)` destinations. -/
theorem laneWF_implies_distinctDstLanes_of_pos_wid {R : Type} [DecidableEq R]
    {M : List (LaneMove R)} (hwf : LaneWF M) (hpos : ∀ m ∈ M, 0 < m.wid) :
    DistinctDstLanes M := by
  unfold DistinctDstLanes
  induction M with
  | nil => simp
  | cons m rest ih =>
    have hwf' := List.pairwise_cons.1 hwf
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hwf'.2 (fun x hx => hpos x (List.mem_cons_of_mem _ hx))⟩
    intro hmem
    obtain ⟨m', hm', heq⟩ := List.mem_map.1 hmem
    have hdreg : m.dreg = m'.dreg := (Prod.mk.inj heq).1.symm
    have hdst : m.dst = m'.dst := (Prod.mk.inj heq).2.symm
    have hdisj := hwf'.1 m' hm' hdreg
    rw [← hdst] at hdisj
    unfold Lane.Disjoint LaneMove.dst at hdisj
    dsimp only at hdisj
    have hp := hpos m (List.mem_cons_self ..)
    omega

/-- A self-copy (same register, same lane) leaves the register file unchanged. -/
theorem laneWrite_self_copy {R : Type} [DecidableEq R] {n : Nat} (ρ : R → BitVec n)
    {m : LaneMove R} (hr : m.sreg = m.dreg) (ho : m.soff = m.doff) : laneWrite ρ ρ m = ρ := by
  obtain ⟨dreg, doff, sreg, soff, wid⟩ := m
  dsimp only at hr ho
  subst hr
  subst ho
  funext r
  simp only [laneWrite, upd]
  split
  · next h => subst h; exact putLane_getPut _ _
  · rfl

/-! ### Examples, counterexamples, non-vacuity for lane moves (registers `Nat`, 16-bit words) -/

/-- `r.al ← s.al` style constructor for examples: copy `wid` bits. -/
def lm (dreg doff sreg soff wid : Nat) : LaneMove Nat := ⟨dreg, doff, sreg, soff, wid⟩

/-- Register file for examples: register 0 holds `0x1234`, register 1 holds `0xABCD`, others 0. -/
def regs16 : Nat → BitVec 16 := fun r => if r = 0 then 0x1234#16 else if r = 1 then 0xABCD#16 else 0#16

/-- Positive example (`lanePMove`): the parallel byte swap within register 0. -/
theorem lanePMove_byte_swap_example :
    lanePMove [lm 0 0 0 8 8, lm 0 8 0 0 8] regs16 0 = 0x3412#16 := by decide

/-- Negative example (`runLanes` is not the parallel reading): executing the byte swap
sequentially copies the high byte into both bytes. -/
theorem runLanes_byte_swap_naive :
    runLanes [lm 0 0 0 8 8, lm 0 8 0 0 8] regs16 0 = 0x1212#16 := by decide

/-- Positive / negative examples (`LaneWF`). -/
theorem laneWF_examples :
    LaneWF [lm 0 0 1 0 8, lm 0 8 1 8 8] ∧ ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 1 0 16] := by decide

/-- Positive / negative examples (`DistinctDstLanes`): two moves into the same lane of the same
register are not distinct destinations. -/
theorem distinctDstLanes_examples :
    DistinctDstLanes [lm 0 0 1 0 8, lm 0 8 2 0 8] ∧ ¬ DistinctDstLanes [lm 0 0 1 0 8, lm 0 0 2 0 8] := by
  decide

/-- Positive / negative examples (`LaneTopological`). -/
theorem laneTopological_examples :
    LaneTopological [lm 2 0 1 0 8, lm 1 0 0 0 8] ∧ ¬ LaneTopological [lm 1 0 0 0 8, lm 2 0 1 0 8] := by
  decide

/-- **Counterexample: distinct `(register, lane)` destinations are not enough.** Writing the low
byte and the low 16 bits of register 0 are distinct destinations, but they overlap, and the two
orders of the parallel move give different results (on the register file `regs16`). -/
theorem lanePMove_distinct_dst_lanes_not_enough :
    DistinctDstLanes [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧ ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧
    lanePMove [lm 0 0 1 0 8, lm 0 0 2 0 16] regs16 0 ≠
      lanePMove [lm 0 0 2 0 16, lm 0 0 1 0 8] regs16 0 := by decide

/-- Counterexample (hypothesis `LaneWF` of `runLanes_eq_lanePMove_of_laneWF_of_topological`). -/
theorem runLanes_needs_laneWF :
    ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧
    List.Perm [lm 0 0 2 0 16, lm 0 0 1 0 8] [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧
    LaneTopological [lm 0 0 2 0 16, lm 0 0 1 0 8] ∧
    runLanes [lm 0 0 2 0 16, lm 0 0 1 0 8] regs16 ≠ lanePMove [lm 0 0 1 0 8, lm 0 0 2 0 16] regs16 :=
  ⟨by decide, List.Perm.swap _ _ _, by decide, fun h => absurd (congrFun h 0) (by decide)⟩

/-- Counterexample (hypothesis `LaneTopological`): the byte swap emitted in its given order. -/
theorem runLanes_needs_topological :
    LaneWF [lm 0 0 0 8 8, lm 0 8 0 0 8] ∧
    List.Perm [lm 0 0 0 8 8, lm 0 8 0 0 8] [lm 0 0 0 8 8, lm 0 8 0 0 8] ∧
    ¬ LaneTopological [lm 0 0 0 8 8, lm 0 8 0 0 8] ∧
    runLanes [lm 0 0 0 8 8, lm 0 8 0 0 8] regs16 ≠ lanePMove [lm 0 0 0 8 8, lm 0 8 0 0 8] regs16 :=
  ⟨by decide, List.Perm.refl _, by decide, fun h => absurd (congrFun h 0) (by decide)⟩

/-- Counterexample (hypothesis `ms.Perm M`): a topological sequence for a different move. -/
theorem runLanes_needs_perm :
    LaneWF [lm 0 0 1 0 8] ∧ ¬ List.Perm ([] : List (LaneMove Nat)) [lm 0 0 1 0 8] ∧
    LaneTopological ([] : List (LaneMove Nat)) ∧
    runLanes ([] : List (LaneMove Nat)) regs16 ≠ lanePMove [lm 0 0 1 0 8] regs16 := by
  refine ⟨by decide, fun h => absurd h.length_eq (by decide), by decide,
    fun h => absurd (congrFun h 0) (by decide)⟩

/-- Non-claim witness: at width `0`, `LaneWF` does not imply distinct destinations (two empty
moves into the same lane are disjoint, having no bits, but their `(register, lane)` pairs are
equal). -/
theorem laneWF_not_implies_distinctDstLanes_width_zero :
    LaneWF [lm 0 4 1 0 0, lm 0 4 2 0 0] ∧ ¬ DistinctDstLanes [lm 0 4 1 0 0, lm 0 4 2 0 0] := by
  decide

/-- Counterexample (hypothesis `M.Perm M'` of `lanePMove_perm_invariant_of_laneWF`): a list that
is not a reordering of `M` has a different meaning. -/
theorem lanePMove_perm_needs_perm :
    LaneWF [lm 0 0 1 0 8] ∧
    ¬ List.Perm [lm 0 0 1 0 8] ([] : List (LaneMove Nat)) ∧
    lanePMove [lm 0 0 1 0 8] regs16 ≠ lanePMove ([] : List (LaneMove Nat)) regs16 := by
  refine ⟨by decide, fun h => absurd h.length_eq (by decide), fun h => ?_⟩
  exact absurd (congrFun h 0) (by decide)

/-- Counterexample (hypothesis `LaneWF` of `lanePMove_perm_invariant_of_laneWF`). -/
theorem lanePMove_perm_needs_laneWF :
    ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧
    List.Perm [lm 0 0 1 0 8, lm 0 0 2 0 16] [lm 0 0 2 0 16, lm 0 0 1 0 8] ∧
    lanePMove [lm 0 0 1 0 8, lm 0 0 2 0 16] regs16 ≠ lanePMove [lm 0 0 2 0 16, lm 0 0 1 0 8] regs16 :=
  ⟨by decide, List.Perm.swap _ _ _, fun h => absurd (congrFun h 0) (by decide)⟩

/-- Non-vacuity of `lanePMove_perm_invariant_of_laneWF`: the in-register byte swap. -/
theorem nonvacuity_lanePMove_perm :
    LaneWF [lm 0 0 0 8 8, lm 0 8 0 0 8] ∧
    List.Perm [lm 0 0 0 8 8, lm 0 8 0 0 8] [lm 0 8 0 0 8, lm 0 0 0 8 8] :=
  ⟨by decide, List.Perm.swap _ _ _⟩

/-- Non-vacuity of `runLanes_eq_lanePMove_of_laneWF_of_topological` inside one register: shift
the bytes of register 0 down (`[0,8) ← [8,16)`, `[8,16) ← [16,24)`), emitted reader-first; here
`Lane.Disjoint` is exercised in both `LaneWF` and `LaneTopological`, and the given order of `M`
is not lane-topological. -/
theorem nonvacuity_runLanes_same_register :
    LaneWF [lm 0 8 0 16 8, lm 0 0 0 8 8] ∧
    List.Perm [lm 0 0 0 8 8, lm 0 8 0 16 8] [lm 0 8 0 16 8, lm 0 0 0 8 8] ∧
    LaneTopological [lm 0 0 0 8 8, lm 0 8 0 16 8] ∧
    ¬ LaneTopological [lm 0 8 0 16 8, lm 0 0 0 8 8] :=
  ⟨by decide, List.Perm.swap _ _ _, by decide, by decide⟩

/-- Non-vacuity of `runLanes_eq_lanePMove_of_laneWF_of_topological`: copy the low byte of
register 1 into register 2, and the low byte of register 0 into register 1, emitted reader-first. -/
theorem nonvacuity_runLanes :
    LaneWF [lm 1 0 0 0 8, lm 2 0 1 0 8] ∧
    List.Perm [lm 2 0 1 0 8, lm 1 0 0 0 8] [lm 1 0 0 0 8, lm 2 0 1 0 8] ∧
    LaneTopological [lm 2 0 1 0 8, lm 1 0 0 0 8] :=
  ⟨by decide, List.Perm.swap _ _ _, by decide⟩

/-! ### `LaneWF` is sufficient, not necessary -/

theorem perm_pair_self {α : Type} {m : α} {M' : List α} (hp : M'.Perm [m, m]) : M' = [m, m] := by
  have hl := hp.length_eq
  match M', hl with
  | [x, y], _ =>
    have hx : x = m := by
      have := hp.mem_iff.1 (List.mem_cons_self ..)
      simpa using this
    have hy : y = m := by
      have := hp.mem_iff.1 (show y ∈ [x, y] by simp)
      simpa using this
    subst hx; subst hy; rfl

/-- Non-claim witness: the exact duplicate `[lm 0 0 1 0 8, lm 0 0 1 0 8]` violates `LaneWF`, yet
every reordering has the same meaning on every 16-bit register file (one concrete list). -/
theorem lanePMove_perm_invariant_duplicate_not_laneWF :
    ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 1 0 8] ∧
    ∀ (M' : List (LaneMove Nat)), M'.Perm [lm 0 0 1 0 8, lm 0 0 1 0 8] →
      ∀ ρ : Nat → BitVec 16, lanePMove M' ρ = lanePMove [lm 0 0 1 0 8, lm 0 0 1 0 8] ρ :=
  ⟨by decide, fun _ hp _ => by rw [perm_pair_self hp]⟩

/-- Non-claim witness: two overlapping lane moves that copy aligned bits from the same source
register (`[0,8) ← r1[0,8)` and `[0,16) ← r1[0,16)`) violate `LaneWF`, yet both orders agree on
every register file. -/
theorem lanePMove_same_source_overlap_not_laneWF :
    ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 1 0 16] ∧
    ∀ ρ : Nat → BitVec 16,
      lanePMove [lm 0 0 1 0 8, lm 0 0 1 0 16] ρ = lanePMove [lm 0 0 1 0 16, lm 0 0 1 0 8] ρ := by
  refine ⟨by decide, fun ρ => ?_⟩
  funext r
  simp only [lanePMove, List.foldl, laneWrite, upd, lm, LaneMove.dst, LaneMove.src]
  by_cases hr : r = 0
  · subst hr
    simp only [ite_true]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [getLsbD_putLane _ _ _ hi, getLsbD_getLane]
    by_cases h8 : i < 8
    · simp [h8, show i < 16 by omega]
    · simp [h8, hi]
  · simp [hr]

/-- Non-claim witness: in an 8-bit register, destination lanes `[6,10)` and `[8,12)` overlap only
beyond the register; the two moves violate `LaneWF`, yet both orders agree on every register
file. -/
theorem lanePMove_beyond_register_overlap_not_laneWF :
    ¬ LaneWF [lm 0 6 1 0 4, lm 0 8 1 0 4] ∧
    ∀ ρ : Nat → BitVec 8,
      lanePMove [lm 0 6 1 0 4, lm 0 8 1 0 4] ρ = lanePMove [lm 0 8 1 0 4, lm 0 6 1 0 4] ρ := by
  refine ⟨by decide, fun ρ => ?_⟩
  have hc := (putLane_comm_iff_disjointIn (n := 8) ⟨6, 4⟩ ⟨8, 4⟩).2 (by decide)
  funext r
  simp only [lanePMove, List.foldl, laneWrite, upd, lm, LaneMove.dst, LaneMove.src]
  by_cases hr : r = 0
  · subst hr
    simp only [ite_true]
    exact (hc _ _ _).symm
  · simp [hr]

/-- Non-claim witness: `LaneTopological` rejects a harmless self-copy placed before a reader of
its lane, although the sequence still realizes its parallel reading on every register file. -/
theorem laneTopological_rejects_benign_self_copy :
    ¬ LaneTopological [lm 0 0 0 0 8, lm 1 0 0 0 8] ∧
    ∀ ρ : Nat → BitVec 16,
      runLanes [lm 0 0 0 0 8, lm 1 0 0 0 8] ρ = lanePMove [lm 0 0 0 0 8, lm 1 0 0 0 8] ρ := by
  refine ⟨by decide, fun ρ => ?_⟩
  have h0 : laneWrite ρ ρ (lm 0 0 0 0 8) = ρ := laneWrite_self_copy ρ rfl rfl
  show laneStep (laneStep ρ (lm 0 0 0 0 8)) (lm 1 0 0 0 8) =
    laneWrite ρ (laneWrite ρ ρ (lm 0 0 0 0 8)) (lm 1 0 0 0 8)
  unfold laneStep
  rw [h0]

end Toy.ParMove
