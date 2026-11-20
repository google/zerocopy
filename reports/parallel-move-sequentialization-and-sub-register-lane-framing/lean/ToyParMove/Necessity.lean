import ToyParMove.Sequentialize
import ToyParMove.Readings

/-!
Which side conditions of sequentialization are necessary.

* `sequentialize_agrees_off_tmp` needs functionality and "not both a destination and a source"
  for the scratch location (counterexamples below), but **not** full scratch freshness.
* When the scratch location is a destination, its own assignment can be lost.
* Concatenating two sequentializations is sound only if the first block writes neither a
  location that the second block reads nor the scratch location that the second block reads.
* A plain move list realizes its own parallel reading when it is ordered so that no move
  overwrites a later move's source (`Topological`); the naive order of a chain fails.
-/
set_option linter.unusedSectionVars false

namespace Toy.ParMove

/-! ### Tightness of `sequentialize_agrees_off_tmp` -/

/-- Counterexample (hypothesis `Functional`): `[(0,0),(0,1),(0,0)]` with the fresh scratch
location `2`. Both the first-entry and the last-entry readings leave the old value of `0` at
`0`, but the produced sequence copies the old value of `1` there. -/
theorem sequentialize_needs_functional :
    ¬ Functional [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)] ∧
    ((2 : Nat) ∉ dsts [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)] ∨
      (2 : Nat) ∉ srcs [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)]) ∧
    ¬ (∀ l, l ≠ 2 → runSeq (sequentialize 2 [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)])
        (id : Nat → Nat) l = pmove [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)] id l) ∧
    ¬ (∀ l, l ≠ 2 → runSeq (sequentialize 2 [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)])
        (id : Nat → Nat) l = pmoveLast [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)] id l) := by
  refine ⟨fun h => absurd (h 0 0 1 (by simp) (by simp)) (by decide), Or.inl (by decide),
    fun h => absurd (h 0 (by decide)) (by decide +kernel),
    fun h => absurd (h 0 (by decide)) (by decide +kernel)⟩

/-- Counterexample (hypothesis `tmp ∉ dsts M ∨ tmp ∉ srcs M`): the swap `[(0,1),(1,0)]` with
scratch location `0`, which is both a destination and a source. Location `1 ≠ tmp` ends with its
own old value instead of the old value of `0`. -/
theorem sequentialize_needs_tmp_not_dst_or_not_src :
    Functional [((0 : Nat), (1 : Nat)), (1, 0)] ∧
    ¬ ((0 : Nat) ∉ dsts [((0 : Nat), (1 : Nat)), (1, 0)] ∨
        (0 : Nat) ∉ srcs [((0 : Nat), (1 : Nat)), (1, 0)]) ∧
    ¬ (∀ l, l ≠ 0 → runSeq (sequentialize 0 [((0 : Nat), (1 : Nat)), (1, 0)])
        (id : Nat → Nat) l = pmove [((0 : Nat), (1 : Nat)), (1, 0)] id l) := by
  refine ⟨functional_of_wellFormed (by decide), by decide,
    fun h => absurd (h 1 (by decide)) (by decide +kernel)⟩

/-- Non-claim witness: when the scratch location is a destination but not a source, the soundness
theorem applies off `tmp`, yet the parallel move's own assignment to `tmp` can be lost: on
`[(0,3),(1,2),(2,1)]` with scratch `0`, location `0` ends with the old value of `1` (not of `3`). -/
theorem sequentialize_loses_tmp_destination :
    Functional [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    (0 : Nat) ∈ dsts [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    (0 : Nat) ∉ srcs [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    runSeq (sequentialize 0 [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)]) (id : Nat → Nat) 0 = 1 ∧
    pmove [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] (id : Nat → Nat) 0 = 3 := by
  refine ⟨functional_of_wellFormed (by decide), by decide, by decide, by decide +kernel,
    by decide⟩

/-- Non-claim witness: on the 2-cycle `[(1,2),(2,1)]` the fresh scratch location `0` is changed, so
the exclusion of `tmp` from the conclusion cannot be dropped (one concrete instance). -/
theorem sequentialize_clobbers_tmp :
    (0 : Nat) ∉ dsts [((1 : Nat), (2 : Nat)), (2, 1)] ∧
    (0 : Nat) ∉ srcs [((1 : Nat), (2 : Nat)), (2, 1)] ∧
    runSeq (sequentialize 0 [((1 : Nat), (2 : Nat)), (2, 1)]) (id : Nat → Nat) 0 = 1 ∧
    pmove [((1 : Nat), (2 : Nat)), (2, 1)] (id : Nat → Nat) 0 = 0 := by
  refine ⟨by decide, by decide, by decide +kernel, by decide⟩

/-- Non-claim witness: `htmp` is tight but not necessary: on `[(0,0),(1,2),(2,1)]` the scratch
location `0` is both a destination and a source only through the self-move `(0,0)`, and the
conclusion still holds, because self-moves are dropped first (one concrete instance). -/
theorem sequentialize_works_with_tmp_self_move :
    Functional [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)] ∧
    ¬ ((0 : Nat) ∉ dsts [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)] ∨
       (0 : Nat) ∉ srcs [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)]) ∧
    ∀ (σ : Nat → Nat) (l : Nat), l ≠ 0 →
      runSeq (sequentialize 0 [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)]) σ l =
        pmove [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)] σ l := by
  refine ⟨functional_of_wellFormed (by decide), by decide, ?_⟩
  intro σ l hl
  have h1 := sequentialize_agrees_off_tmp (M := [((1 : Nat), (2 : Nat)), (2, 1)]) (tmp := 0)
    (functional_of_wellFormed (by decide)) (Or.inl (by decide)) σ l hl
  have hseq : sequentialize 0 [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)] =
      sequentialize 0 [((1 : Nat), (2 : Nat)), (2, 1)] := by decide +kernel
  rw [hseq, h1]
  simp [pmove, lookupSrc, hl]

/-- Non-vacuity of `sequentialize_agrees_off_tmp`, in a case outside the customary freshness
condition: the scratch location `0` is read by the move `3 := 0`. The emitted sequence is
`3 := 0; 0 := 1; 1 := 2; 2 := 0`, i.e. the reader of `0` is served before `0` is overwritten. -/
theorem nonvacuity_sequentialize_tmp_is_source :
    Functional [((1 : Nat), (2 : Nat)), (2, 1), (3, 0)] ∧
    ((0 : Nat) ∉ dsts [((1 : Nat), (2 : Nat)), (2, 1), (3, 0)] ∨
      (0 : Nat) ∉ srcs [((1 : Nat), (2 : Nat)), (2, 1), (3, 0)]) ∧
    (0 : Nat) ∈ srcs [((1 : Nat), (2 : Nat)), (2, 1), (3, 0)] ∧
    sequentialize 0 [((1 : Nat), (2 : Nat)), (2, 1), (3, 0)] = [(3, 0), (0, 1), (1, 2), (2, 0)] :=
  ⟨functional_of_wellFormed (by decide), Or.inl (by decide), by decide, by decide +kernel⟩

/-- Non-vacuity of `sequentialize_agrees_off_tmp` with the scratch location a destination but
not a source. -/
theorem nonvacuity_sequentialize_tmp_is_destination :
    Functional [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    ((0 : Nat) ∉ dsts [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∨
      (0 : Nat) ∉ srcs [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)]) :=
  ⟨functional_of_wellFormed (by decide), Or.inr (by decide)⟩

/-! ### Composition of two sequentialized blocks -/

section Composition
variable {Loc V : Type} [DecidableEq Loc]

theorem lookupSrc_append_of_not_mem_left {M₁ M₂ : List (Loc × Loc)} {l : Loc}
    (h : l ∉ dsts M₁) : lookupSrc (M₁ ++ M₂) l = lookupSrc M₂ l := by
  induction M₁ with
  | nil => rfl
  | cons m M₁ ih =>
    have hl : l ≠ m.1 := fun e => h (by simp [e])
    simp only [List.cons_append, lookupSrc, hl, ite_false]
    exact ih (fun h' => h (by simp [h']))

theorem lookupSrc_append_of_not_mem_right {M₁ M₂ : List (Loc × Loc)} {l : Loc}
    (h : l ∉ dsts M₂) : lookupSrc (M₁ ++ M₂) l = lookupSrc M₁ l := by
  induction M₁ with
  | nil => exact lookupSrc_eq_none_iff.2 h
  | cons m M₁ ih =>
    by_cases hl : l = m.1
    · simp [lookupSrc, hl]
    · simp only [List.cons_append, lookupSrc, hl, ite_false]
      exact ih

/-- **Composition of sequentialized blocks.** Suppose `ms₁` realizes the parallel move `M₁` and
`ms₂` realizes `M₂`, both at every location other than the scratch location `tmp` and from every
store. If the blocks have disjoint destinations, no source of `M₂` is a destination of `M₁`, and
`tmp` is not a source of `M₂`, then `ms₁ ++ ms₂` realizes `M₁ ++ M₂` off `tmp`. -/
theorem runSeq_append_realizes_off_tmp {M₁ M₂ ms₁ ms₂ : List (Loc × Loc)} {tmp : Loc}
    (h₁ : ∀ τ : Loc → V, ∀ l, l ≠ tmp → runSeq ms₁ τ l = pmove M₁ τ l)
    (h₂ : ∀ τ : Loc → V, ∀ l, l ≠ tmp → runSeq ms₂ τ l = pmove M₂ τ l)
    (hdisj : ∀ x ∈ dsts M₁, x ∉ dsts M₂)
    (hread : ∀ x ∈ srcs M₂, x ∉ dsts M₁)
    (htmp : tmp ∉ srcs M₂) :
    ∀ τ : Loc → V, ∀ l, l ≠ tmp → runSeq (ms₁ ++ ms₂) τ l = pmove (M₁ ++ M₂) τ l := by
  intro τ l hl
  rw [runSeq_append, h₂ _ l hl]
  by_cases hl2 : l ∈ dsts M₂
  · have hl1 : l ∉ dsts M₁ := fun h => hdisj l h hl2
    simp only [pmove, lookupSrc_append_of_not_mem_left hl1]
    cases hlk : lookupSrc M₂ l with
    | none => exact absurd hl2 (lookupSrc_eq_none_iff.1 hlk)
    | some s =>
      have hsM : s ∈ srcs M₂ := mem_srcs.2 ⟨l, mem_of_lookupSrc_eq_some hlk⟩
      have hst : s ≠ tmp := fun e => htmp (e ▸ hsM)
      simp only
      rw [h₁ τ s hst, pmove_of_not_mem_dsts (hread s hsM)]
  · rw [pmove_of_not_mem_dsts hl2, h₁ τ l hl]
    simp only [pmove, lookupSrc_append_of_not_mem_right hl2]

end Composition

/-- Counterexample (hypothesis `tmp ∉ srcs M₂` of `runSeq_append_realizes_off_tmp`): breaking
the cycle `[(1,2),(2,1)]` with scratch `0` *before* emitting the reader `3 := 0` clobbers the value
that reader needs. This is the order a cycle-first strategy may choose. -/
theorem runSeq_append_needs_tmp_not_src :
    (∀ τ : Nat → Nat, ∀ l, l ≠ 0 →
      runSeq [(0, 1), (1, 2), (2, 0)] τ l = pmove [((1 : Nat), (2 : Nat)), (2, 1)] τ l) ∧
    (∀ τ : Nat → Nat, ∀ l, l ≠ 0 → runSeq [(3, 0)] τ l = pmove [((3 : Nat), (0 : Nat))] τ l) ∧
    (∀ x ∈ dsts [((1 : Nat), (2 : Nat)), (2, 1)], x ∉ dsts [((3 : Nat), (0 : Nat))]) ∧
    (∀ x ∈ srcs [((3 : Nat), (0 : Nat))], x ∉ dsts [((1 : Nat), (2 : Nat)), (2, 1)]) ∧
    (0 : Nat) ∈ srcs [((3 : Nat), (0 : Nat))] ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 0 → runSeq ([(0, 1), (1, 2), (2, 0)] ++ [(3, 0)]) τ l =
        pmove ([((1 : Nat), (2 : Nat)), (2, 1)] ++ [(3, 0)]) τ l) := by
  refine ⟨?_, ?_, by decide, by decide, by decide, fun h => absurd (h id 3 (by decide)) (by decide)⟩
  · intro τ l hl
    have := sequentialize_agrees_off_tmp (M := [((1 : Nat), (2 : Nat)), (2, 1)]) (tmp := 0)
      (functional_of_wellFormed (by decide)) (Or.inl (by decide)) τ l hl
    rwa [show sequentialize 0 [((1 : Nat), (2 : Nat)), (2, 1)] = [(0, 1), (1, 2), (2, 0)] by
      decide +kernel] at this
  · intro τ l _
    simp only [runSeq, List.foldl, seqStep, pmove, lookupSrc, upd]
    split <;> simp_all

/-- Counterexample (hypothesis "no source of `M₂` is a destination of `M₁`"): emitting the chain
`[(1,0),(2,1)]` in its given order overwrites `1` before `2 := 1` reads it. -/
theorem runSeq_append_needs_sources_not_overwritten :
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [(1, 0)] τ l = pmove [((1 : Nat), (0 : Nat))] τ l) ∧
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [(2, 1)] τ l = pmove [((2 : Nat), (1 : Nat))] τ l) ∧
    (∀ x ∈ dsts [((1 : Nat), (0 : Nat))], x ∉ dsts [((2 : Nat), (1 : Nat))]) ∧
    (1 : Nat) ∈ srcs [((2 : Nat), (1 : Nat))] ∧ (1 : Nat) ∈ dsts [((1 : Nat), (0 : Nat))] ∧
    (9 : Nat) ∉ srcs [((2 : Nat), (1 : Nat))] ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq ([(1, 0)] ++ [(2, 1)]) τ l =
        pmove ([((1 : Nat), (0 : Nat))] ++ [(2, 1)]) τ l) := by
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide,
    fun h => absurd (h id 2 (by decide)) (by decide)⟩ <;>
  · intro τ l _
    simp only [runSeq, List.foldl, seqStep, pmove, lookupSrc, upd]
    split <;> simp_all

/-- Counterexample (hypothesis "disjoint destinations"): two blocks writing the same location;
the second write wins in the sequence, the first entry wins in the adopted reading. -/
theorem runSeq_append_needs_disjoint_dsts :
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [(0, 1)] τ l = pmove [((0 : Nat), (1 : Nat))] τ l) ∧
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [(0, 2)] τ l = pmove [((0 : Nat), (2 : Nat))] τ l) ∧
    (0 : Nat) ∈ dsts [((0 : Nat), (1 : Nat))] ∧ (0 : Nat) ∈ dsts [((0 : Nat), (2 : Nat))] ∧
    (∀ x ∈ srcs [((0 : Nat), (2 : Nat))], x ∉ dsts [((0 : Nat), (1 : Nat))]) ∧
    (9 : Nat) ∉ srcs [((0 : Nat), (2 : Nat))] ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq ([(0, 1)] ++ [(0, 2)]) τ l =
        pmove ([((0 : Nat), (1 : Nat))] ++ [(0, 2)]) τ l) := by
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide,
    fun h => absurd (h id 0 (by decide)) (by decide)⟩ <;>
  · intro τ l _
    simp only [runSeq, List.foldl, seqStep, pmove, lookupSrc, upd]
    split <;> simp_all

/-- Counterexample (hypothesis `h₁` of `runSeq_append_realizes_off_tmp`): the empty sequence
does not realize `[(1,0)]`; every other hypothesis holds (with scratch `9`), and the conclusion
fails. -/
theorem runSeq_append_needs_first_realization :
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [] τ l = pmove [((1 : Nat), (0 : Nat))] τ l) ∧
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [] τ l = pmove ([] : List (Nat × Nat)) τ l) ∧
    (∀ x ∈ dsts [((1 : Nat), (0 : Nat))], x ∉ dsts ([] : List (Nat × Nat))) ∧
    (∀ x ∈ srcs ([] : List (Nat × Nat)), x ∉ dsts [((1 : Nat), (0 : Nat))]) ∧
    (9 : Nat) ∉ srcs ([] : List (Nat × Nat)) ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq ([] ++ []) τ l =
        pmove ([((1 : Nat), (0 : Nat))] ++ []) τ l) :=
  ⟨fun h => absurd (h id 1 (by decide)) (by decide), fun _ _ _ => rfl,
    by decide, by decide, by decide, fun h => absurd (h id 1 (by decide)) (by decide)⟩

/-- Counterexample (hypothesis `h₂` of `runSeq_append_realizes_off_tmp`): every other hypothesis
holds (with scratch `9`), and the conclusion fails. -/
theorem runSeq_append_needs_second_realization :
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [] τ l = pmove ([] : List (Nat × Nat)) τ l) ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [] τ l = pmove [((1 : Nat), (0 : Nat))] τ l) ∧
    (∀ x ∈ dsts ([] : List (Nat × Nat)), x ∉ dsts [((1 : Nat), (0 : Nat))]) ∧
    (∀ x ∈ srcs [((1 : Nat), (0 : Nat))], x ∉ dsts ([] : List (Nat × Nat))) ∧
    (9 : Nat) ∉ srcs [((1 : Nat), (0 : Nat))] ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq ([] ++ []) τ l =
        pmove (([] : List (Nat × Nat)) ++ [(1, 0)]) τ l) :=
  ⟨fun _ _ _ => rfl, fun h => absurd (h id 1 (by decide)) (by decide),
    by decide, by decide, by decide, fun h => absurd (h id 1 (by decide)) (by decide)⟩

/-- Non-vacuity of `runSeq_append_realizes_off_tmp`: drain the reader of `0` first, then break
the cycle `[(1,2),(2,1)]` through `0`. -/
theorem nonvacuity_runSeq_append_realizes_off_tmp :
    (∀ τ : Nat → Nat, ∀ l, l ≠ 0 → runSeq [(3, 0)] τ l = pmove [((3 : Nat), (0 : Nat))] τ l) ∧
    (∀ τ : Nat → Nat, ∀ l, l ≠ 0 →
      runSeq [(0, 1), (1, 2), (2, 0)] τ l = pmove [((1 : Nat), (2 : Nat)), (2, 1)] τ l) ∧
    (∀ x ∈ dsts [((3 : Nat), (0 : Nat))], x ∉ dsts [((1 : Nat), (2 : Nat)), (2, 1)]) ∧
    (∀ x ∈ srcs [((1 : Nat), (2 : Nat)), (2, 1)], x ∉ dsts [((3 : Nat), (0 : Nat))]) ∧
    (0 : Nat) ∉ srcs [((1 : Nat), (2 : Nat)), (2, 1)] :=
  ⟨runSeq_append_needs_tmp_not_src.2.1, runSeq_append_needs_tmp_not_src.1, by decide, by decide,
    by decide⟩

/-! ### Topological emission order for plain moves (no scratch) -/

section Topological
variable {Loc V : Type} [DecidableEq Loc]

/-- An emission order is **topological** when no move overwrites the source of a move emitted
after it (for list positions `i < j`, `ms[i].dst ≠ ms[j].src`). -/
def Topological (ms : List (Loc × Loc)) : Prop :=
  ms.Pairwise fun earlier later => earlier.1 ≠ later.2

instance (ms : List (Loc × Loc)) : Decidable (Topological ms) :=
  inferInstanceAs (Decidable (ms.Pairwise _))

/-- **Topological order soundness.** A functional list of moves emitted in a topological order,
executed sequentially, produces exactly (at every location) the parallel reading of the same
list. -/
theorem runSeq_eq_pmove_of_topological {ms : List (Loc × Loc)} (hF : Functional ms)
    (htop : Topological ms) (σ : Loc → V) : runSeq ms σ = pmove ms σ := by
  induction ms generalizing σ with
  | nil => rfl
  | cons m ms ih =>
    have htop' := List.pairwise_cons.1 htop
    have hF' : Functional ms := functional_of_subset hF (List.subset_cons_self _ _)
    rw [runSeq_cons, ih hF' htop'.2]
    funext l
    by_cases hl : l ∈ dsts ms
    · obtain ⟨s, hs⟩ := mem_dsts.1 hl
      rw [pmove_of_mem hF' hs, pmove_of_mem hF (List.mem_cons_of_mem _ hs)]
      have hne : s ≠ m.1 := fun e => htop'.1 (l, s) hs e.symm
      simp [seqStep, upd, hne]
    · rw [pmove_of_not_mem_dsts hl]
      by_cases hlm : l = m.1
      · subst hlm
        rw [pmove_of_mem hF (show (m.1, m.2) ∈ m :: ms by simp)]
        simp [seqStep, upd]
      · rw [pmove_of_not_mem_dsts (by simp [hlm, hl])]
        simp [seqStep, upd, hlm]

end Topological

/-- Positive example (`Topological`): the chain `[(1,0),(2,1)]` in reverse order. -/
theorem topological_example : Topological [((2 : Nat), (1 : Nat)), (1, 0)] := by decide

/-- Negative example (`Topological`): the chain in its given order. -/
theorem not_topological_example : ¬ Topological [((1 : Nat), (0 : Nat)), (2, 1)] := by decide

/-- Counterexample (hypothesis `Topological` of `runSeq_eq_pmove_of_topological`): emitting the
acyclic chain `[(1,0),(2,1)]` in its given (non-topological) order. -/
theorem runSeq_eq_pmove_needs_topological :
    Functional [((1 : Nat), (0 : Nat)), (2, 1)] ∧ ¬ Topological [((1 : Nat), (0 : Nat)), (2, 1)] ∧
    runSeq [((1 : Nat), (0 : Nat)), (2, 1)] (id : Nat → Nat) ≠
      pmove [((1 : Nat), (0 : Nat)), (2, 1)] id :=
  ⟨functional_of_wellFormed (by decide), by decide,
    fun h => absurd (congrFun h 2) (by decide)⟩

/-- Counterexample (hypothesis `Functional` of `runSeq_eq_pmove_of_topological`). -/
theorem runSeq_eq_pmove_needs_functional :
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] ∧ Topological [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    runSeq [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) ≠
      pmove [((0 : Nat), (1 : Nat)), (0, 2)] id :=
  ⟨not_functional_two_sources, by decide, fun h => absurd (congrFun h 0) (by decide)⟩

/-- Non-vacuity of `runSeq_eq_pmove_of_topological`. -/
theorem nonvacuity_runSeq_eq_pmove_of_topological :
    Functional [((2 : Nat), (1 : Nat)), (1, 0)] ∧ Topological [((2 : Nat), (1 : Nat)), (1, 0)] :=
  ⟨functional_of_wellFormed (by decide), topological_example⟩

/-- Non-claim witness: `Topological` also rejects a harmless self-move placed before a reader of
its location, although the sequence still realizes its parallel reading on every store. -/
theorem topological_rejects_benign_self_move :
    ¬ Topological [((1 : Nat), (1 : Nat)), (2, 1)] ∧
    ∀ (V : Type) (σ : Nat → V),
      runSeq [((1 : Nat), (1 : Nat)), (2, 1)] σ = pmove [((1 : Nat), (1 : Nat)), (2, 1)] σ := by
  refine ⟨by decide, fun V σ => runSeq_eq_pmove_of_id (funext fun l => ?_) σ⟩
  by_cases h1 : l = 1
  · subst h1; decide
  · by_cases h2 : l = 2
    · subst h2; decide
    · simp [runSeq, seqStep, upd, pmove, lookupSrc, h1, h2]

section NoTopological
variable {Loc : Type} [DecidableEq Loc]

/-- **No topological order for cyclic dependencies.** If a nonempty collection `C` of moves of
`ms` has the property that every destination in `C` is read by another move of `C` (for example
the moves of a cycle), then `ms` is not topological. -/
theorem not_topological_of_dsts_read {ms C : List (Loc × Loc)} (hC : C ≠ [])
    (hsub : ∀ m ∈ C, m ∈ ms) (hread : ∀ m ∈ C, ∃ m' ∈ C, m' ≠ m ∧ m'.2 = m.1) :
    ¬ Topological ms := by
  induction ms with
  | nil =>
    cases C with
    | nil => exact absurd rfl hC
    | cons c _ => exact absurd (hsub c (List.mem_cons_self ..)) (by simp)
  | cons x rest ih =>
    intro htop
    have ht := List.pairwise_cons.1 htop
    by_cases hx : x ∈ C
    · obtain ⟨m', hm'C, hne, he⟩ := hread x hx
      have hm'r : m' ∈ rest := by
        rcases List.mem_cons.1 (hsub m' hm'C) with h | h
        · exact absurd h hne
        · exact h
      exact ht.1 m' hm'r he.symm
    · refine ih (fun m hm => ?_) ht.2
      rcases List.mem_cons.1 (hsub m hm) with h | h
      · exact absurd (h ▸ hm) hx
      · exact h

end NoTopological

/-- **A cycle with an outgoing copy needs no scratch location.** The parallel move
`[(3,1),(2,1),(1,2)]` exchanges `1` and `2` and also copies the old value of `1` into `3`. No
reordering of it is topological, yet the three plain moves `3 := 1; 1 := 2; 2 := 3` realize it
exactly, at every location and from every store: the copy already written to `3` serves as the
saved value of `1`. -/
theorem cycle_with_outgoing_copy_realized_without_scratch :
    (∀ ms : List (Nat × Nat), ms.Perm [(3, 1), (2, 1), (1, 2)] → ¬ Topological ms) ∧
    ∀ (V : Type) (σ : Nat → V),
      runSeq [((3 : Nat), (1 : Nat)), (1, 2), (2, 3)] σ = pmove [((3 : Nat), (1 : Nat)), (2, 1), (1, 2)] σ := by
  refine ⟨fun ms hp => ?_, fun V σ => runSeq_eq_pmove_of_id (funext fun l => ?_) σ⟩
  · refine not_topological_of_dsts_read (C := [(2, 1), (1, 2)]) (by simp)
      (fun m hm => hp.mem_iff.2 (by simp at hm; rcases hm with rfl | rfl <;> simp)) ?_
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨(1, 2), by simp, by decide, rfl⟩
    · exact ⟨(2, 1), by simp, by decide, rfl⟩
  · by_cases h1 : l = 1
    · subst h1; decide
    · by_cases h2 : l = 2
      · subst h2; decide
      · by_cases h3 : l = 3
        · subst h3; decide
        · simp [runSeq, seqStep, upd, pmove, lookupSrc, h1, h2, h3]

section LastReading
variable {Loc V : Type} [DecidableEq Loc]

private theorem lookupSrc_append_of_mem_left {A B : List (Loc × Loc)} {l : Loc}
    (h : l ∈ dsts A) : lookupSrc (A ++ B) l = lookupSrc A l := by
  induction A with
  | nil => simp [dsts] at h
  | cons a rest ih =>
    by_cases hl : l = a.1
    · simp [lookupSrc, hl]
    · simp only [List.cons_append, lookupSrc, hl, ite_false]
      apply ih
      simp only [dsts_cons, List.mem_cons] at h
      exact h.resolve_left hl

/-- With the last-entry reading, a topological list realizes its parallel reading without any
functionality hypothesis (sequential execution also lets the last write win). -/
theorem runSeq_eq_pmoveLast_of_topological :
    ∀ {ms : List (Loc × Loc)}, Topological ms → ∀ σ : Loc → V, runSeq ms σ = pmoveLast ms σ
  | [], _, _ => rfl
  | m :: ms, htop, σ => by
    have htop' := List.pairwise_cons.1 htop
    rw [runSeq_cons, runSeq_eq_pmoveLast_of_topological htop'.2]
    funext l
    unfold pmoveLast
    rw [List.reverse_cons]
    by_cases hl : l ∈ dsts ms.reverse
    · simp only [pmove, lookupSrc_append_of_mem_left hl]
      cases hlk : lookupSrc ms.reverse l with
      | none => exact absurd hl (lookupSrc_eq_none_iff.1 hlk)
      | some s =>
        have hsm : (l, s) ∈ ms := List.mem_reverse.1 (mem_of_lookupSrc_eq_some hlk)
        have hne : s ≠ m.1 := fun e => htop'.1 (l, s) hsm e.symm
        simp [seqStep, upd, hne]
    · simp only [pmove, lookupSrc_eq_none_iff.2 hl, lookupSrc_append_of_not_mem_left hl,
        lookupSrc]
      by_cases hlm : l = m.1
      · subst hlm; simp [seqStep, upd]
      · simp [seqStep, upd, hlm]

end LastReading

end Toy.ParMove
