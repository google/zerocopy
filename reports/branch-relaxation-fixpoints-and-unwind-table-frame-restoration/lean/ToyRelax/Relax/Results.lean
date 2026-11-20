import ToyRelax.Relax.Examples

/-!
# Results: grow-only relaxation, monotonicity, oscillation, optimality, and
# encoding equivalence
-/

namespace Toy.Relax

variable {prm : Params} {p : Prog}

/-! ## Result 1: grow-only relaxation terminates, is valid, and is least -/

theorem relaxLoop_spec (prm : Params) (p : Prog) : ∀ (fuel : Nat) (a : Asg),
    shortCount p a < fuel →
    ∃ k, k ≤ shortCount p a ∧ relaxLoop prm p fuel a = some (iter (step prm p) k a) ∧
      Valid prm p (iter (step prm p) k a)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, a, h => by
    unfold relaxLoop
    by_cases hc : changed prm p a = true
    · simp only [hc, ↓reduceIte]
      have hlt := shortCount_step_lt hc
      obtain ⟨k, hk, he, hv⟩ := relaxLoop_spec prm p fuel (step prm p a) (by omega)
      exact ⟨k + 1, by omega, he, hv⟩
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨0, Nat.zero_le _, rfl, (changed_eq_false_iff.mp hc : Valid prm p a)⟩

theorem relax_eq_loop_result (prm : Params) (p : Prog) (a : Asg) :
    ∃ k, relaxLoop prm p (numBranches p + 1) a = some (iter (step prm p) k a) ∧
      relax prm p a = iter (step prm p) k a ∧ Valid prm p (iter (step prm p) k a) := by
  have hsc := shortCount_le_numBranches (p := p) a
  obtain ⟨k, hk, he, hv⟩ := relaxLoop_spec prm p (numBranches p + 1) a (by omega)
  refine ⟨k, he, ?_, hv⟩
  unfold relax
  rw [show numBranches p = k + (numBranches p - k) by omega, iter_add,
    iter_fix (step_eq_of_valid hv)]

/-- **Result 1a (termination bound, witness exposed).**  For every program,
every encoding parameters and every start assignment, the grow-only relaxation
loop stops within `numBranches p + 1` passes, and what it returns is exactly
`relax prm p a`, the `numBranches p`-fold iterate of the grow-only step. -/
theorem relaxLoop_returns_relax_within_numBranches_succ (prm : Params) (p : Prog) (a : Asg) :
    relaxLoop prm p (numBranches p + 1) a = some (relax prm p a) := by
  obtain ⟨k, he, hr, _⟩ := relax_eq_loop_result prm p a
  rw [he, hr]

/-- **Result 1b (validity, above the start).**  The grow-only relaxation result
is valid and lies above the start assignment, with no hypothesis on the size
function. -/
theorem relax_valid_and_above_start (prm : Params) (p : Prog) (a : Asg) :
    Valid prm p (relax prm p a) ∧ Asg.Le a (relax prm p a) := by
  obtain ⟨k, _, hr, hv⟩ := relax_eq_loop_result prm p a
  exact ⟨hr ▸ hv, le_iter_step a _⟩

theorem step_le_of_valid_of_le (hmono : DistMonotone prm p) {a b : Asg}
    (hb : Valid prm p b) (hab : Asg.Le a b) : Asg.Le (step prm p a) b := by
  intro i hi
  unfold step at hi
  cases ha : a i
  · rw [ha, Bool.false_or] at hi
    obtain ⟨t, hpi, hai, hlt⟩ := outOfReach_eq_true_iff.mp hi
    cases hbi : b i
    · exfalso
      have h1 := dist_le_reach_of_valid hb hpi hbi
      have h2 := hmono a b hab i t hpi
      omega
    · rfl
  · exact hab i ha

/-- **Result 1c (leastness under monotone distances).**  If every branch's
distance is monotone in the assignment, the grow-only relaxation result from
`a` is below every valid assignment above `a`: it is the least valid
assignment above the start.  The order is `Asg.Le`, which compares every index
`i : Nat`, including non-branch positions (where `relax` keeps the values of
`a`); the branch-restricted form is
`relax_leOnBranches_of_valid_of_leOnBranches_of_distMonotone`. -/
theorem relax_le_of_valid_of_le_of_distMonotone (hmono : DistMonotone prm p) {a b : Asg}
    (hb : Valid prm p b) (hab : Asg.Le a b) : Asg.Le (relax prm p a) b := by
  unfold relax
  generalize numBranches p = n
  induction n generalizing a with
  | zero => exact hab
  | succ n ih => exact ih (step_le_of_valid_of_le hmono hb hab)

/-- **Leastness, restricted to branch positions.**  Values at non-branch
positions do not affect validity, so the leastness of Result 1c also holds in
the order that compares branch positions only. -/
theorem relax_leOnBranches_of_valid_of_leOnBranches_of_distMonotone (hmono : DistMonotone prm p)
    {a b : Asg} (hb : Valid prm p b) (hab : Asg.LeOnBranches p a b) :
    Asg.LeOnBranches p (relax prm p a) b := by
  let b' : Asg := fun i => if isBranchAt p i then b i else a i
  have hagree : ∀ i, isBranchAt p i = true → b' i = b i := fun i hi => by simp [b', hi]
  have hb' : Valid prm p b' := (valid_congr_of_eqOnBranches hagree).mpr hb
  have hab' : Asg.Le a b' := by
    intro i hai
    by_cases hi : isBranchAt p i = true
    · simp only [b', hi, ↓reduceIte]
      exact hab i hi hai
    · simp only [b', hi, Bool.false_eq_true, ↓reduceIte]
      exact hai
  have hle := relax_le_of_valid_of_le_of_distMonotone hmono hb' hab'
  intro i hi hri
  rw [← hagree i hi]
  exact hle i hri

/-- The `numBranches p + 1` bound of Result 1a is attained: with only
`numBranches p` passes the loop has not yet confirmed a fixpoint (the
`numBranches p`-th pass already reaches the fixpoint; one more pass is needed
to observe that nothing changes). -/
theorem relaxLoop_numBranches_passes_insufficient :
    numBranches chainProg = 2 ∧ relaxLoop chainPrm chainProg (numBranches chainProg) allShort = none ∧
    Valid chainPrm chainProg (iter (step chainPrm chainProg) 2 allShort) := by
  decide

/-- Non-vacuity for Result 1a/1b: on the two-branch chain, all-short is invalid
and the relaxation result from all-short has both branches long. -/
theorem relax_nonvacuity_chain :
    relaxLoop chainPrm chainProg (numBranches chainProg + 1) allShort =
      some (relax chainPrm chainProg allShort) ∧
    relax chainPrm chainProg allShort 1 = true ∧ relax chainPrm chainProg allShort 2 = true ∧
    ¬ Valid chainPrm chainProg allShort := by
  refine ⟨relaxLoop_returns_relax_within_numBranches_succ _ _ _, by decide, by decide, by decide⟩

/-! ## Result 2: monotonicity is what makes leastness work -/

/-- **Result 2a (displacement monotonicity).**  The distance between a branch
and its target depends only on the sizes of the instructions between them
(half-open interval `[min i t, max i t)`), and is monotone in those sizes. -/
theorem dist_le_dist_of_size_le_between {a b : Asg} {i t : Nat}
    (h : ∀ j, min i t ≤ j → j < max i t → size prm p a j ≤ size prm p b j) :
    dist prm p a i t ≤ dist prm p b i t := by
  unfold dist
  split
  · exact addr_sub_le_addr_sub (by omega) (fun j h1 h2 => h j (by omega) (by omega))
  · exact addr_sub_le_addr_sub (by omega) (fun j h1 h2 => h j (by omega) (by omega))

/-- **Result 2b (monotone sizes give monotone distances).** -/
theorem distMonotone_of_sizesMonotone (h : SizesMonotone prm p) : DistMonotone prm p :=
  fun a b hab _ _ _ => dist_le_dist_of_size_le_between (fun j _ _ => h a b hab j)

/-- A one-branch program whose all-short assignment is valid. -/
def oneProg : Prog := [.fixed 1, .branch 0]

/-- Canonical counterexample for the hypothesis `Valid prm p b` of Result 1c
(and of its corollary `relax_le_of_valid_of_le_of_noAlign_of_short_le_long`):
with monotone sizes and `a ≤ b`, but `b` (all-short) invalid, the relaxation
result is not below `b`. -/
theorem leastness_needs_valid_upper_bound :
    NoAlign chainProg ∧ chainPrm.shortSize ≤ chainPrm.longSize ∧
    DistMonotone chainPrm chainProg ∧ Asg.Le allShort allShort ∧
    ¬ Asg.Le (relax chainPrm chainProg allShort) allShort := by
  refine ⟨by decide, by decide, distMonotone_of_sizesMonotone sizesMonotone_example_pos,
    Asg.Le.refl _, ?_⟩
  intro h
  have := h 1 (by decide)
  revert this
  decide

/-- Canonical counterexample for the hypothesis `Asg.Le a b` of Result 1c
(and of its corollary `relax_le_of_valid_of_le_of_noAlign_of_short_le_long`):
`b` (all-short) is valid, but the start (branch 1 long) is not below it, and
neither is the relaxation result. -/
theorem leastness_needs_upper_bound_above_start :
    NoAlign oneProg ∧ chainPrm.shortSize ≤ chainPrm.longSize ∧
    DistMonotone chainPrm oneProg ∧ Valid chainPrm oneProg allShort ∧
    ¬ Asg.Le (relax chainPrm oneProg (promote allShort 1)) allShort := by
  refine ⟨by decide, by decide,
    distMonotone_of_sizesMonotone (sizesMonotone_of_noAlign_of_short_le_long (by decide) (by decide)),
    by decide, ?_⟩
  intro h
  have := h 1 (by decide)
  revert this
  decide

/-- Non-vacuity for Result 1c: monotone distances, a valid assignment
`chainExtraB` (positions 1–3 long, all others short) above the start
(all-short); the conclusion is not trivial there, because the relaxation
result keeps branch 3 short while `chainExtraB` has it long. -/
theorem relax_least_nonvacuity :
    DistMonotone chainPrm chainExtraProg ∧ Valid chainPrm chainExtraProg chainExtraB ∧
    Asg.Le allShort chainExtraB ∧
    relax chainPrm chainExtraProg allShort 3 = false ∧ chainExtraB 3 = true :=
  ⟨distMonotone_of_sizesMonotone (sizesMonotone_of_noAlign_of_short_le_long (by decide) (by decide)),
    by decide, Asg.Le.allShort _, by decide, by decide⟩

/-- Canonical counterexample for the hypothesis of Result 2a: an in-between
size decreases (the alignment padding at index 1), and so does the distance of
the branch at index 2 to its target 1. -/
theorem dist_decreases_when_size_between_decreases :
    size alignPrm alignProg alignB 1 < size alignPrm alignProg allShort 1 ∧
    dist alignPrm alignProg alignB 2 1 < dist alignPrm alignProg allShort 2 1 := by
  decide

/-- Canonical counterexample for `NoAlign` in
`sizesMonotone_of_noAlign_of_short_le_long`: the other hypothesis holds and
sizes are not monotone. -/
theorem noAlign_needed_for_sizesMonotone :
    alignPrm.shortSize ≤ alignPrm.longSize ∧ ¬ SizesMonotone alignPrm alignProg :=
  ⟨by decide, sizesMonotone_example_neg_align⟩

/-- Canonical counterexample for `shortSize ≤ longSize` in
`sizesMonotone_of_noAlign_of_short_le_long`. -/
theorem short_le_long_needed_for_sizesMonotone :
    NoAlign invProg ∧ ¬ SizesMonotone invPrm invProg :=
  ⟨by decide, sizesMonotone_example_neg_inverted⟩

/-- Non-vacuity for `sizesMonotone_of_noAlign_of_short_le_long`. -/
theorem sizesMonotone_nonvacuity :
    NoAlign chainProg ∧ chainPrm.shortSize ≤ chainPrm.longSize ∧
    size chainPrm chainProg allShort 1 < size chainPrm chainProg (promote allShort 1) 1 :=
  ⟨by decide, by decide, by decide⟩

/-- Non-vacuity for Result 2b: a program with monotone sizes on which some
distance actually grows. -/
theorem distMonotone_nonvacuity :
    SizesMonotone chainPrm chainProg ∧
    dist chainPrm chainProg allShort 2 1 < dist chainPrm chainProg (promote allShort 1) 2 1 :=
  ⟨sizesMonotone_example_pos, by decide⟩

/-- **Concrete sufficient condition for leastness** (corollary of Results 1c,
2b and 2c).  Without alignment directives and with `shortSize ≤ longSize`, the
grow-only relaxation result is the least valid assignment above the start. -/
theorem relax_le_of_valid_of_le_of_noAlign_of_short_le_long (hna : NoAlign p)
    (hsl : prm.shortSize ≤ prm.longSize) {a b : Asg} (hb : Valid prm p b) (hab : Asg.Le a b) :
    Asg.Le (relax prm p a) b :=
  relax_le_of_valid_of_le_of_distMonotone
    (distMonotone_of_sizesMonotone (sizesMonotone_of_noAlign_of_short_le_long hna hsl)) hb hab

/-- **Counterexample (alignment padding breaks leastness).**  For
`[branch 1, align 4, branch 1]` with short size 1, long size 2, reach 2:
relaxation from all-short terminates with a valid result (Result 1a/1b), but
that result promotes branch 2, while promoting branch 0 instead is also valid
(it shrinks the padding by one byte and brings branch 2 into reach).  So the
relaxation result is not below this valid assignment.  Every hypothesis of
`relax_le_of_valid_of_le_of_noAlign_of_short_le_long` except `NoAlign` holds. -/
theorem align_padding_breaks_leastness :
    alignPrm.shortSize ≤ alignPrm.longSize ∧ Valid alignPrm alignProg alignB ∧
    Asg.Le allShort alignB ∧ ¬ Asg.Le (relax alignPrm alignProg allShort) alignB := by
  refine ⟨by decide, by decide, Asg.Le.allShort _, ?_⟩
  intro h
  have := h 2 (by decide)
  revert this
  decide

/-- **Counterexample (a long form smaller than the short form breaks
leastness).**  Every hypothesis of
`relax_le_of_valid_of_le_of_noAlign_of_short_le_long` except
`shortSize ≤ longSize` holds. -/
theorem inverted_sizes_break_leastness :
    NoAlign invProg ∧ Valid invPrm invProg (promote allShort 0) ∧
    Asg.Le allShort (promote allShort 0) ∧
    ¬ Asg.Le (relax invPrm invProg allShort) (promote allShort 0) := by
  refine ⟨by decide, by decide, Asg.Le.allShort _, ?_⟩
  intro h
  have := h 1 (by decide)
  revert this
  decide

/-- Termination and validity still hold on the alignment counterexample: what
fails without monotonicity is leastness (and minimality of total size), not
convergence. -/
theorem align_counterexample_still_terminates_valid :
    relaxLoop alignPrm alignProg (numBranches alignProg + 1) allShort =
      some (relax alignPrm alignProg allShort) ∧
    Valid alignPrm alignProg (relax alignPrm alignProg allShort) :=
  ⟨relaxLoop_returns_relax_within_numBranches_succ _ _ _,
    (relax_valid_and_above_start _ _ _).1⟩

/-- Non-vacuity for `relax_le_of_valid_of_le_of_noAlign_of_short_le_long`. -/
theorem noAlign_short_le_long_nonvacuity :
    NoAlign chainProg ∧ chainPrm.shortSize ≤ chainPrm.longSize ∧
    Valid chainPrm chainProg (fun _ => true) ∧ Asg.Le allShort (fun _ => true) :=
  ⟨by decide, by decide, by decide, Asg.Le.allShort _⟩

/-- Non-vacuity for Result 2a: sizes between branch and target grow, and so
does the distance (strictly). -/
theorem dist_mono_nonvacuity :
    (∀ j, min 2 1 ≤ j → j < max 2 1 →
      size chainPrm chainProg allShort j ≤ size chainPrm chainProg (promote allShort 1) j) ∧
    dist chainPrm chainProg allShort 2 1 < dist chainPrm chainProg (promote allShort 1) 2 1 := by
  refine ⟨?_, by decide⟩
  intro j h1 h2
  have : j = 1 := by omega
  subst this
  decide

end Toy.Relax
