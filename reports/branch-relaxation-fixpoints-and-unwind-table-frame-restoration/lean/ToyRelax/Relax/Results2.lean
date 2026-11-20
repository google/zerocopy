import ToyRelax.Relax.Results

/-!
# Results: grow-and-shrink oscillation, optimality, encoding equivalence
-/

namespace Toy.Relax

variable {prm : Params} {p : Prog}

/-! ## Result 3: grow-and-shrink can oscillate; grow-only cannot -/

/-- The start of the oscillation: only branch 1 long. -/
def oscStart : Asg := promote allShort 1

/-- The other state of the oscillation: only branch 2 long. -/
def oscOther : Asg := promote allShort 2

theorem stepGS_osc_cycle :
    stepGS oscPrm oscProg oscStart = oscOther ∧ stepGS oscPrm oscProg oscOther = oscStart := by
  constructor
  · funext i
    match i with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | n + 3 => rfl
  · funext i
    match i with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | n + 3 => rfl

theorem iter_of_two_cycle {f : Asg → Asg} {x y : Asg} (hxy : f x = y) (hyx : f y = x) :
    ∀ n, iter f (2 * n) x = x ∧ iter f (2 * n + 1) x = y
  | 0 => ⟨rfl, hxy⟩
  | n + 1 => by
    obtain ⟨h0, h1⟩ := iter_of_two_cycle hxy hyx n
    have e0 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    refine ⟨?_, ?_⟩
    · rw [e0, iter_succ', h1, hyx]
    · rw [e0, iter_succ', iter_succ', h1, hyx, hxy]

/-- **Result 3a (grow-and-shrink oscillates forever from a non-bottom start,
monotone sizes).**  Grow-and-shrink decides each branch `i` from the
counterfactual layout `setShort a i` (see `stepGS`).  On
`[fixed 1, branch 3, branch 0]` with short size 1, long size 2, reach 2 (no
alignment, `shortSize ≤ longSize`, hence monotone sizes), grow-and-shrink
relaxation started from "branch 1 long" alternates forever between
`oscStart` (branch 1 long, branch 2 short) and `oscOther` (branch 1 short,
branch 2 long): every even iterate is `oscStart`, every odd iterate is
`oscOther`, and the two differ. -/
theorem growShrink_two_cycle_from_nonbottom_start :
    SizesMonotone oscPrm oscProg ∧ oscStart ≠ oscOther ∧
    ∀ n, iter (stepGS oscPrm oscProg) (2 * n) oscStart = oscStart ∧
      iter (stepGS oscPrm oscProg) (2 * n + 1) oscStart = oscOther := by
  refine ⟨sizesMonotone_of_noAlign_of_short_le_long (by decide) (by decide), ?_,
    iter_of_two_cycle stepGS_osc_cycle.1 stepGS_osc_cycle.2⟩
  intro h
  have := congrFun h 1
  revert this
  decide

/-- `stepGS` reads the counterfactual layout `setShort a i`, not the current
layout `a`: from `oscStart`, the long branch 1 is out of short reach when its
distance is read from the current layout (its own long size lies in its
forward span), yet `stepGS` demotes it because a short encoding of it would
reach. -/
theorem stepGS_decides_from_counterfactual_layout :
    oscStart 1 = true ∧ oscPrm.reach < dist oscPrm oscProg oscStart 1 3 ∧
    dist oscPrm oscProg (setShort oscStart 1) 1 3 ≤ oscPrm.reach ∧
    stepGS oscPrm oscProg oscStart 1 = false := by
  decide

/-- On the same program, grow-only relaxation from the same start converges
(both branches long) and grow-and-shrink from all-short is already at a
fixpoint (both branches short): the oscillation needs both the demotion and
the non-bottom start. -/
theorem growShrink_two_cycle_controls :
    relax oscPrm oscProg oscStart 1 = true ∧ relax oscPrm oscProg oscStart 2 = true ∧
    Valid oscPrm oscProg (relax oscPrm oscProg oscStart) ∧
    stepGS oscPrm oscProg allShort = allShort := by
  refine ⟨by decide, by decide, (relax_valid_and_above_start _ _ _).1, ?_⟩
  funext i
  match i with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | n + 3 => rfl

/-- Every long branch of `a` would be out of reach if it alone were made
short. -/
def Justified (prm : Params) (p : Prog) (a : Asg) : Prop :=
  ∀ i t, p[i]? = some (.branch t) → a i = true → prm.reach < dist prm p (setShort a i) i t

theorem setShort_eq_self {a : Asg} {i : Nat} (h : a i = false) : setShort a i = a := by
  funext j
  unfold setShort
  by_cases hj : j = i
  · subst hj; simp [h]
  · simp [hj]

theorem stepGS_eq_step_of_justified {a : Asg} (hJ : Justified prm p a) :
    stepGS prm p a = step prm p a := by
  funext i
  unfold stepGS step outOfReach
  rcases hp : p[i]? with _ | ins
  · simp
  · cases ins with
    | fixed s => simp
    | align k => simp
    | branch t =>
      cases ha : a i
      · simp [setShort_eq_self ha]
      · simp [hJ i t hp ha]

theorem justified_step (hmono : DistMonotone prm p) {a : Asg} (hJ : Justified prm p a) :
    Justified prm p (step prm p a) := by
  intro i t hp hs
  have hle : Asg.Le (setShort a i) (setShort (step prm p a) i) := by
    intro j hj
    unfold setShort at hj ⊢
    by_cases hji : j = i
    · simp [hji] at hj
    · simp only [hji, ↓reduceIte] at hj ⊢
      exact le_step a j hj
  have hmon := hmono _ _ hle i t hp
  cases ha : a i
  · have hout : outOfReach prm p a i = true := by simpa [step, ha] using hs
    obtain ⟨t', hp', _, hlt⟩ := outOfReach_eq_true_iff.mp hout
    rw [hp] at hp'
    simp only [Option.some.injEq, Instr.branch.injEq] at hp'
    subst hp'
    rw [setShort_eq_self ha] at hmon
    omega
  · have := hJ i t hp ha
    omega

theorem iter_stepGS_eq_iter_step_of_justified (hmono : DistMonotone prm p) :
    ∀ (n : Nat) (a : Asg), Justified prm p a →
      iter (stepGS prm p) n a = iter (step prm p) n a
  | 0, _, _ => rfl
  | n + 1, a, hJ => by
    show iter (stepGS prm p) n (stepGS prm p a) = iter (step prm p) n (step prm p a)
    rw [stepGS_eq_step_of_justified hJ]
    exact iter_stepGS_eq_iter_step_of_justified hmono n _ (justified_step hmono hJ)

/-- **Result 3b (from all-short, grow-and-shrink is grow-only under monotone
distances).**  If distances are monotone in the assignment, every iterate of
grow-and-shrink relaxation started from all-short equals the corresponding
iterate of grow-only relaxation; in particular it never demotes a branch and
reaches the grow-only fixpoint `relax prm p allShort` after `numBranches p`
steps. -/
theorem iter_stepGS_allShort_eq_iter_step_of_distMonotone (hmono : DistMonotone prm p)
    (n : Nat) : iter (stepGS prm p) n allShort = iter (step prm p) n allShort :=
  iter_stepGS_eq_iter_step_of_justified hmono n allShort (fun _ _ _ h => by cases h)

/-- Non-vacuity for Result 3b. -/
theorem growShrink_allShort_nonvacuity :
    DistMonotone chainPrm chainProg ∧
    iter (stepGS chainPrm chainProg) 2 allShort 2 = true :=
  ⟨distMonotone_of_sizesMonotone sizesMonotone_example_pos, by decide⟩

/-- Two alignment directives between two backward branches. -/
def demoteProg : Prog := [.fixed 1, .align 4, .branch 0, .align 4, .branch 3]

/-- **Counterexample (alignment: grow-and-shrink from all-short demotes and
stops at a different valid assignment).**  On
`[fixed 1, align 4, branch 0, align 4, branch 3]` (short 1, long 2, reach 2)
both branches start out of reach; once branch 2 is long, the second padding
shrinks and branch 4 fits short again, so grow-and-shrink demotes it while
grow-only keeps it.  After two steps the grow-and-shrink iterate is a valid
fixpoint of `stepGS` that differs from the grow-only iterate at branch 4. -/
theorem align_growShrink_differs_from_growOnly :
    ¬ DistMonotone alignPrm demoteProg ∧
    iter (stepGS alignPrm demoteProg) 2 allShort 4 = false ∧
    iter (step alignPrm demoteProg) 2 allShort 4 = true ∧
    stepGS alignPrm demoteProg (iter (stepGS alignPrm demoteProg) 2 allShort) =
      iter (stepGS alignPrm demoteProg) 2 allShort ∧
    Valid alignPrm demoteProg (iter (stepGS alignPrm demoteProg) 2 allShort) := by
  refine ⟨?_, by decide, by decide, ?_, by decide⟩
  rotate_left
  · funext i
    match i with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | n + 5 => rfl
  intro h
  have := h (promote allShort 4) (fun i => i == 2 || i == 4)
    (by
      intro i hi
      unfold promote at hi
      split at hi
      · simp_all
      · simp [allShort] at hi) 4 3 rfl
  revert this
  decide

theorem iter_of_four_cycle {f : Asg → Asg} {s0 s1 s2 s3 : Asg}
    (h01 : f s0 = s1) (h12 : f s1 = s2) (h23 : f s2 = s3) (h30 : f s3 = s0) :
    ∀ n, iter f (4 * n) s0 = s0 ∧ iter f (4 * n + 1) s0 = s1 ∧
         iter f (4 * n + 2) s0 = s2 ∧ iter f (4 * n + 3) s0 = s3
  | 0 => ⟨rfl, h01, by show iter f 1 (f s0) = s2; rw [h01]; exact h12,
          by show iter f 2 (f s0) = s3; rw [h01]; show iter f 1 (f s1) = s3; rw [h12]; exact h23⟩
  | n + 1 => by
    obtain ⟨_, _, _, a3⟩ := iter_of_four_cycle h01 h12 h23 h30 n
    have e0 : 4 * (n + 1) = (4 * n + 3) + 1 := by omega
    have h4 : iter f (4 * (n + 1)) s0 = s0 := by rw [e0, iter_succ', a3, h30]
    refine ⟨h4, ?_, ?_, ?_⟩
    · rw [iter_succ', h4, h01]
    · rw [iter_succ', iter_succ', h4, h01, h12]
    · rw [iter_succ', iter_succ', iter_succ', h4, h01, h12, h23]

/-- If every state of an `f`-invariant set is moved by `f`, iteration from a
state of that set never reaches a fixpoint. -/
theorem iter_succ_ne_of_invariant_of_no_fixpoint {f : Asg → Asg} {P : Asg → Prop}
    (hinv : ∀ x, P x → P (f x)) (hmove : ∀ x, P x → f x ≠ x) {s : Asg} (hs : P s) :
    ∀ n, iter f (n + 1) s ≠ iter f n s := by
  have hP : ∀ n, P (iter f n s) := by
    intro n
    induction n with
    | zero => exact hs
    | succ n ih => rw [iter_succ']; exact hinv _ ih
  intro n
  rw [iter_succ']
  exact hmove _ (hP n)

theorem stepGS_alignOsc_cycle :
    stepGS alignPrm alignOscProg allShort = promote allShort 1 ∧
    stepGS alignPrm alignOscProg (promote allShort 1) = promote (promote allShort 1) 0 ∧
    stepGS alignPrm alignOscProg (promote (promote allShort 1) 0) = promote allShort 0 ∧
    stepGS alignPrm alignOscProg (promote allShort 0) = allShort := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;>
    match i with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | n + 3 => rfl

/-- **Result 3c (without monotone distances, grow-and-shrink started from
all-short can oscillate forever).**  Grow-and-shrink decides each branch `i`
from the counterfactual layout `setShort a i` (see `stepGS`).  On
`[branch 2, branch 3, align 4]` with short size 1, long size 2, reach 2 (so
`shortSize ≤ longSize`; distances are not monotone because of the alignment
directive), grow-and-shrink relaxation started from all-short cycles with
period 4 through all-short → {1} → {0, 1} → {0} → all-short, and no iterate is
a fixpoint.  The step {0} → all-short relies on the counterfactual reading:
reading the current layout instead stops at the valid fixpoint {0}
(`alignOsc_counterfactual_vs_current`,
`alignOsc_stepGSCurrent_reaches_valid_fixpoint`). -/
theorem align_growShrink_four_cycle_from_allShort :
    alignPrm.shortSize ≤ alignPrm.longSize ∧ ¬ DistMonotone alignPrm alignOscProg ∧
    (∀ n, iter (stepGS alignPrm alignOscProg) (n + 1) allShort ≠
      iter (stepGS alignPrm alignOscProg) n allShort) ∧
    ∀ n, iter (stepGS alignPrm alignOscProg) (4 * n) allShort = allShort ∧
      iter (stepGS alignPrm alignOscProg) (4 * n + 1) allShort = promote allShort 1 ∧
      iter (stepGS alignPrm alignOscProg) (4 * n + 2) allShort = promote (promote allShort 1) 0 ∧
      iter (stepGS alignPrm alignOscProg) (4 * n + 3) allShort = promote allShort 0 := by
  obtain ⟨c0, c1, c2, c3⟩ := stepGS_alignOsc_cycle
  refine ⟨by decide, ?_, ?_, iter_of_four_cycle c0 c1 c2 c3⟩
  · intro h
    have := h allShort (promote allShort 0) (Asg.Le.allShort _) 1 3 rfl
    revert this
    decide
  · refine iter_succ_ne_of_invariant_of_no_fixpoint
      (P := fun x => x = allShort ∨ x = promote allShort 1 ∨
        x = promote (promote allShort 1) 0 ∨ x = promote allShort 0) ?_ ?_ (Or.inl rfl)
    · rintro x (rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inl c0)
      · exact Or.inr (Or.inr (Or.inl c1))
      · exact Or.inr (Or.inr (Or.inr c2))
      · exact Or.inl c3
    · rintro x (rfl | rfl | rfl | rfl) h
      · rw [c0] at h; exact absurd (congrFun h 1) (by decide)
      · rw [c1] at h; exact absurd (congrFun h 0) (by decide)
      · rw [c2] at h; exact absurd (congrFun h 1) (by decide)
      · rw [c3] at h; exact absurd (congrFun h 0) (by decide)

theorem stepGS_invOsc_cycle :
    stepGS invOscPrm invOscProg allShort = promote (promote allShort 1) 2 ∧
    stepGS invOscPrm invOscProg (promote (promote allShort 1) 2) = allShort := by
  refine ⟨?_, ?_⟩ <;> funext i <;>
    match i with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | n + 3 => rfl

/-- **Result 3c, second instance (inverted sizes, no alignment).**  On
`[fixed 2, branch 3, branch 0]` with short size 2, long size 1, reach 3 (no
alignment directive, but `shortSize > longSize`, so distances are not
monotone), grow-and-shrink relaxation `stepGS` (counterfactual layout
`setShort a i`) started from all-short alternates forever between all-short
and {1, 2}.  This 2-cycle also occurs when distances are read from the current
layout (`invOsc_stepGSCurrent_two_cycle`). -/
theorem inverted_growShrink_two_cycle_from_allShort :
    NoAlign invOscProg ∧ invOscPrm.longSize < invOscPrm.shortSize ∧
    ¬ DistMonotone invOscPrm invOscProg ∧ allShort ≠ promote (promote allShort 1) 2 ∧
    ∀ n, iter (stepGS invOscPrm invOscProg) (2 * n) allShort = allShort ∧
      iter (stepGS invOscPrm invOscProg) (2 * n + 1) allShort = promote (promote allShort 1) 2 := by
  refine ⟨by decide, by decide, ?_, ?_,
    iter_of_two_cycle stepGS_invOsc_cycle.1 stepGS_invOsc_cycle.2⟩
  · intro h
    have := h allShort (promote allShort 1) (Asg.Le.allShort _) 2 0 rfl
    revert this
    decide
  · intro h
    exact absurd (congrFun h 1) (by decide)

/-! ### Result 3: dependence on the counterfactual reading of `stepGS`

`stepGS` re-decides branch `i` from the counterfactual layout `setShort a i`.
The lemmas below compare it with the contrast step `stepGSCurrent`, which reads
the current layout `a`. -/

/-- The aligned 4-cycle of Result 3c is closed by the counterfactual reading.
At `{0}` (only branch 0 long) on `[branch 2, branch 3, align 4]`
(short 1, long 2, reach 2), branch 0's distance to its target is 3 in the
current layout, out of short reach, but 2 in the counterfactual layout
`setShort {0} 0`, within reach; so `stepGS` demotes branch 0 (and returns to
all-short) while `stepGSCurrent` keeps it long. -/
theorem alignOsc_counterfactual_vs_current :
    promote allShort 0 0 = true ∧ alignPrm.reach = 2 ∧
    dist alignPrm alignOscProg (promote allShort 0) 0 2 = 3 ∧
    dist alignPrm alignOscProg (setShort (promote allShort 0) 0) 0 2 = 2 ∧
    stepGS alignPrm alignOscProg (promote allShort 0) 0 = false ∧
    stepGSCurrent alignPrm alignOscProg (promote allShort 0) 0 = true := by
  decide

/-- With the current-layout reading, the aligned program of Result 3c does not
oscillate from all-short: `stepGSCurrent` follows
all-short → {1} → {0, 1} → {0} and then stays at `{0}`, which is valid. -/
theorem alignOsc_stepGSCurrent_reaches_valid_fixpoint :
    stepGSCurrent alignPrm alignOscProg allShort = promote allShort 1 ∧
    stepGSCurrent alignPrm alignOscProg (promote allShort 1) = promote (promote allShort 1) 0 ∧
    stepGSCurrent alignPrm alignOscProg (promote (promote allShort 1) 0) = promote allShort 0 ∧
    stepGSCurrent alignPrm alignOscProg (promote allShort 0) = promote allShort 0 ∧
    Valid alignPrm alignOscProg (promote allShort 0) ∧
    ∀ n, iter (stepGSCurrent alignPrm alignOscProg) (n + 3) allShort = promote allShort 0 := by
  have s0 : stepGSCurrent alignPrm alignOscProg allShort = promote allShort 1 := by
    funext i; match i with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => rfl
  have s1 : stepGSCurrent alignPrm alignOscProg (promote allShort 1) =
      promote (promote allShort 1) 0 := by
    funext i; match i with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => rfl
  have s2 : stepGSCurrent alignPrm alignOscProg (promote (promote allShort 1) 0) =
      promote allShort 0 := by
    funext i; match i with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => rfl
  have s3 : stepGSCurrent alignPrm alignOscProg (promote allShort 0) = promote allShort 0 := by
    funext i; match i with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => rfl
  refine ⟨s0, s1, s2, s3, by decide, ?_⟩
  intro n
  have h3 : iter (stepGSCurrent alignPrm alignOscProg) 3 allShort = promote allShort 0 := by
    rw [iter_succ', iter_succ', iter_succ']
    show stepGSCurrent alignPrm alignOscProg (stepGSCurrent alignPrm alignOscProg
      (stepGSCurrent alignPrm alignOscProg allShort)) = _
    rw [s0, s1, s2]
  rw [Nat.add_comm n 3, iter_add, h3, iter_fix s3]

/-- The inverted-size instance of Result 3c oscillates under either reading:
`stepGSCurrent` also alternates forever between all-short and {1, 2}. -/
theorem invOsc_stepGSCurrent_two_cycle :
    ∀ n, iter (stepGSCurrent invOscPrm invOscProg) (2 * n) allShort = allShort ∧
      iter (stepGSCurrent invOscPrm invOscProg) (2 * n + 1) allShort =
        promote (promote allShort 1) 2 := by
  have c0 : stepGSCurrent invOscPrm invOscProg allShort = promote (promote allShort 1) 2 := by
    funext i; match i with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => rfl
  have c1 : stepGSCurrent invOscPrm invOscProg (promote (promote allShort 1) 2) = allShort := by
    funext i; match i with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => rfl
  exact iter_of_two_cycle c0 c1

/-- With the current-layout reading, the instance of Result 3a does not
oscillate either: from `oscStart` (branch 1 long), `stepGSCurrent` makes both
branches long, which is a valid fixpoint of `stepGSCurrent`. -/
theorem osc_stepGSCurrent_reaches_valid_fixpoint :
    stepGSCurrent oscPrm oscProg oscStart = promote oscStart 2 ∧
    stepGSCurrent oscPrm oscProg (promote oscStart 2) = promote oscStart 2 ∧
    Valid oscPrm oscProg (promote oscStart 2) := by
  refine ⟨?_, ?_, by decide⟩ <;> funext i <;>
    match i with | 0 => decide | 1 => decide | 2 => decide | _ + 3 => rfl

/-! ## Result 4: optimality of the grow-only fixpoint from all-short -/

/-- **Result 4a (minimum total size under monotone distances and
`shortSize ≤ longSize`).**  If every branch's distance is monotone in the
assignment and a long branch is at least as large as a short one, the
grow-only relaxation result from all-short has the minimum total size among
all valid assignments.  Alignment directives are allowed: the end of an
alignment directive is monotone in its start address. -/
theorem relax_allShort_totalSize_le_of_valid_of_distMonotone_of_short_le_long
    (hmono : DistMonotone prm p) (hsl : prm.shortSize ≤ prm.longSize) {b : Asg}
    (hb : Valid prm p b) :
    totalSize prm p (relax prm p allShort) ≤ totalSize prm p b :=
  addr_le_addr_of_short_le_long hsl
    (relax_le_of_valid_of_le_of_distMonotone hmono hb (Asg.Le.allShort b)) _

/-- The same conclusion under the single hypothesis `SizesMonotone` (which
gives monotone distances by Result 2b and monotone addresses directly). -/
theorem relax_allShort_totalSize_le_of_valid_of_sizesMonotone (h : SizesMonotone prm p)
    {b : Asg} (hb : Valid prm p b) :
    totalSize prm p (relax prm p allShort) ≤ totalSize prm p b :=
  addr_le_addr_of_sizesMonotone h
    (relax_le_of_valid_of_le_of_distMonotone (distMonotone_of_sizesMonotone h) hb
      (Asg.Le.allShort b)) _

/-- `DistMonotone ∧ shortSize ≤ longSize` admits programs that violate
`SizesMonotone`: a trailing alignment directive shrinks when the branch before
it grows, but no branch spans it. -/
def trailingAlignProg : Prog := [.fixed 2, .branch 0, .align 4]

theorem distMonotone_short_le_long_without_sizesMonotone :
    DistMonotone chainPrm trailingAlignProg ∧ chainPrm.shortSize ≤ chainPrm.longSize ∧
    ¬ SizesMonotone chainPrm trailingAlignProg := by
  refine ⟨?_, by decide, ?_⟩
  · intro a b _ i t hp
    rcases i with _ | _ | i
    · cases hp
    · simp only [trailingAlignProg, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Instr.branch.injEq] at hp
      subst hp
      simp [dist, addr, trailingAlignProg, instrSize]
    · rcases i with _ | i
      · cases hp
      · simp [trailingAlignProg] at hp
  · intro h
    have := h allShort (promote allShort 1) (Asg.Le.allShort _) 2
    revert this
    decide

/-- **Counterexample (alignment: the grow-only fixpoint is not of minimum
size).**  On the alignment program `[branch 1, align 4, branch 1]` (short 1,
long 2, reach 2) the grow-only result from all-short has total size 6, while
the valid assignment with only branch 0 long has total size 5. -/
theorem align_padding_breaks_size_optimality :
    alignPrm.shortSize ≤ alignPrm.longSize ∧ Valid alignPrm alignProg alignB ∧
    totalSize alignPrm alignProg alignB = 5 ∧
    totalSize alignPrm alignProg (relax alignPrm alignProg allShort) = 6 := by
  decide

/-- Canonical counterexample for the hypothesis `DistMonotone prm p` of
Result 4a: the other hypotheses hold and the conclusion fails. -/
theorem size_optimality_needs_distMonotone :
    alignPrm.shortSize ≤ alignPrm.longSize ∧ Valid alignPrm alignProg alignB ∧
    ¬ totalSize alignPrm alignProg (relax alignPrm alignProg allShort) ≤
      totalSize alignPrm alignProg alignB := by
  decide

theorem distMonotone_selfProg (prm : Params) : DistMonotone prm selfProg := by
  intro a b _ i t hp
  rcases i with _ | i
  · simp only [selfProg, List.getElem?_cons_zero, Option.some.injEq, Instr.branch.injEq] at hp
    subst hp
    simp [dist]
  · simp [selfProg] at hp

/-- Canonical counterexample for the hypothesis `shortSize ≤ longSize` of
Result 4a: a single self-branch has distance 0 in every layout (so distances
are monotone), all-short is valid and is the relaxation result, but the long
form is smaller. -/
theorem size_optimality_needs_short_le_long :
    DistMonotone invPrm selfProg ∧ Valid invPrm selfProg (promote allShort 0) ∧
    ¬ totalSize invPrm selfProg (relax invPrm selfProg allShort) ≤
      totalSize invPrm selfProg (promote allShort 0) :=
  ⟨distMonotone_selfProg _, by decide, by decide⟩

/-- Canonical counterexample for the hypothesis `Valid prm p b` of
Result 4a: the invalid all-short assignment is smaller than the relaxation
result. -/
theorem size_optimality_needs_valid :
    DistMonotone chainPrm chainProg ∧ chainPrm.shortSize ≤ chainPrm.longSize ∧
    ¬ Valid chainPrm chainProg allShort ∧
    ¬ totalSize chainPrm chainProg (relax chainPrm chainProg allShort) ≤
      totalSize chainPrm chainProg allShort :=
  ⟨distMonotone_of_sizesMonotone sizesMonotone_example_pos, by decide, by decide, by decide⟩

/-- Non-vacuity for Result 4a, with a strict inequality: the relaxation result
keeps branch 3 short and is strictly smaller than the valid `chainExtraB`. -/
theorem size_optimality_nonvacuity :
    DistMonotone chainPrm chainExtraProg ∧ chainPrm.shortSize ≤ chainPrm.longSize ∧
    Valid chainPrm chainExtraProg chainExtraB ∧
    totalSize chainPrm chainExtraProg (relax chainPrm chainExtraProg allShort) = 7 ∧
    totalSize chainPrm chainExtraProg chainExtraB = 8 :=
  ⟨distMonotone_of_sizesMonotone (sizesMonotone_of_noAlign_of_short_le_long (by decide) (by decide)),
    by decide, by decide, by decide, by decide⟩

/-! ## Result 5: re-relaxation after promotion keeps every branch encodable and
landing on its target -/

/-- Layout injectivity: with positive sizes under every assignment, the
displacement computed for `t` lands on `k` iff `t` and `k` name the same
instruction (indices past the end name the end).  This holds for *any*
assignment `c`; it does not involve validity, promotion or relaxation. -/
theorem jumpsTo_disp_iff_min_eq (hpos : AllSizesPositive prm p) (c : Asg) (i t k : Nat) :
    JumpsTo prm p c i (disp prm p c i t) k ↔ min t p.length = min k p.length := by
  rw [← addr_eq_iff_min_eq hpos c t k]
  unfold JumpsTo disp
  constructor <;> intro h <;> omega

theorem jumpsTo_disp_iff_eq_min_of_sizesPositiveAt {c : Asg} (hpos : SizesPositiveAt prm p c)
    (i t k : Nat) (hk : k ≤ p.length) :
    JumpsTo prm p c i (disp prm p c i t) k ↔ k = min t p.length := by
  have h1 : JumpsTo prm p c i (disp prm p c i t) k ↔ addr prm p c t = addr prm p c k := by
    unfold JumpsTo disp
    constructor <;> intro h <;> omega
  rw [h1, addr_eq_iff_min_eq_of_sizesPositiveAt hpos, Nat.min_eq_left hk]
  exact eq_comm

theorem emitDisp_eq_some_of_valid {c : Asg} (hv : Valid prm p c) {i t : Nat}
    (hp : p[i]? = some (.branch t)) : emitDisp prm p c i = some (disp prm p c i t) := by
  unfold emitDisp
  rw [hp]
  cases hc : c i
  · have hle := dist_le_reach_of_valid hv hp hc
    simp [hle]
  · simp

/-- In a valid layout with positive instruction sizes, every branch has an
encodable displacement that lands exactly on its target. -/
theorem landsExactly_of_valid_of_sizesPositiveAt {c : Asg} (hv : Valid prm p c)
    (hpos : SizesPositiveAt prm p c) {i t : Nat} (hp : p[i]? = some (.branch t)) :
    LandsExactly prm p c i t :=
  ⟨disp prm p c i t, emitDisp_eq_some_of_valid hv hp,
    fun k hk => jumpsTo_disp_iff_eq_min_of_sizesPositiveAt hpos i t k hk⟩

/-- Two layouts in which a branch lands exactly on its target land on the
same instruction indices. -/
theorem landsExactly_same_landing_index {a r : Asg} {i t : Nat}
    (ha : LandsExactly prm p a i t) (hr : LandsExactly prm p r i t) :
    ∃ d₁ d₂, emitDisp prm p a i = some d₁ ∧ emitDisp prm p r i = some d₂ ∧
      ∀ k, k ≤ p.length → (JumpsTo prm p a i d₁ k ↔ JumpsTo prm p r i d₂ k) := by
  obtain ⟨d₁, h₁, k₁⟩ := ha
  obtain ⟨d₂, h₂, k₂⟩ := hr
  exact ⟨d₁, d₂, h₁, h₂, fun k hk => by rw [k₁ k hk, k₂ k hk]⟩

/-- **Result 5 (promote, re-relax: every branch stays encodable and lands on
its target).**  Let `a` be a valid assignment, promote any position `j` to
long and re-run grow-only relaxation, obtaining `r = relax prm p (promote a j)`.
If every instruction has positive size in layout `a` and in layout `r`, then
for every branch `i` with target `t`, in both layouts the branch has an
encodable displacement (`emitDisp`, which requires a short branch to be within
reach) and that displacement, recomputed from its own layout, lands on an
instruction index `k ≤ p.length` exactly when `k = min t p.length`.  The
conclusion for `r` uses only that `r` is valid (Result 1b) and has positive
sizes; see `promote_without_relax_breaks_emitDisp` and
`stale_displacement_lands_elsewhere` for what fails without re-relaxation or
without recomputing displacements. -/
theorem promote_relax_landsExactly_of_valid_of_sizesPositiveAt {a : Asg} {j : Nat}
    (hv : Valid prm p a) (hposA : SizesPositiveAt prm p a)
    (hposR : SizesPositiveAt prm p (relax prm p (promote a j))) :
    ∀ i t, p[i]? = some (.branch t) →
      LandsExactly prm p a i t ∧ LandsExactly prm p (relax prm p (promote a j)) i t :=
  fun _ _ hp => ⟨landsExactly_of_valid_of_sizesPositiveAt hv hposA hp,
    landsExactly_of_valid_of_sizesPositiveAt (relax_valid_and_above_start _ _ _).1 hposR hp⟩

/-- Canonical counterexample for the hypothesis `Valid prm p a` of Result 5:
in the invalid all-short layout of the chain program, branch 1 is out of reach
and has no encodable displacement. -/
theorem promote_relax_landsExactly_needs_valid :
    SizesPositiveAt chainPrm chainProg allShort ∧
    SizesPositiveAt chainPrm chainProg (relax chainPrm chainProg (promote allShort 1)) ∧
    ¬ (∀ i t, chainProg[i]? = some (.branch t) →
      LandsExactly chainPrm chainProg allShort i t ∧
      LandsExactly chainPrm chainProg (relax chainPrm chainProg (promote allShort 1)) i t) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  obtain ⟨⟨d, hd, _⟩, _⟩ := h 1 0 rfl
  rw [emitDisp_example_neg_reach] at hd
  cases hd

/-- Canonical counterexample for the hypothesis `SizesPositiveAt prm p a` of
Result 5: with a zero-size short branch, the branch's displacement in the
all-short layout also lands on instruction 1. -/
theorem promote_relax_landsExactly_needs_sizesPositiveAt_before :
    Valid zeroPrm zeroProg allShort ∧
    SizesPositiveAt zeroPrm zeroProg (relax zeroPrm zeroProg (promote allShort 0)) ∧
    ¬ (∀ i t, zeroProg[i]? = some (.branch t) →
      LandsExactly zeroPrm zeroProg allShort i t ∧
      LandsExactly zeroPrm zeroProg (relax zeroPrm zeroProg (promote allShort 0)) i t) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  obtain ⟨⟨d, hd, hk⟩, _⟩ := h 0 0 rfl
  have he : emitDisp zeroPrm zeroProg allShort 0 = some 0 := by decide
  rw [he] at hd
  cases hd
  have := (hk 1 (by decide)).mp (by decide)
  revert this
  decide

/-- Canonical counterexample for the hypothesis
`SizesPositiveAt prm p (relax prm p (promote a j))` of Result 5: promoting the
branch makes the alignment padding 0 bytes, so in the re-relaxed layout the
displacement to the alignment directive (index 1) also lands on index 2. -/
theorem promote_relax_landsExactly_needs_sizesPositiveAt_after :
    Valid fwdPrm alignZeroProg allShort ∧ SizesPositiveAt fwdPrm alignZeroProg allShort ∧
    ¬ (∀ i t, alignZeroProg[i]? = some (.branch t) →
      LandsExactly fwdPrm alignZeroProg allShort i t ∧
      LandsExactly fwdPrm alignZeroProg (relax fwdPrm alignZeroProg (promote allShort 0)) i t) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  obtain ⟨_, ⟨d, hd, hk⟩⟩ := h 0 1 rfl
  have he : emitDisp fwdPrm alignZeroProg (relax fwdPrm alignZeroProg (promote allShort 0)) 0 =
      some 2 := by decide
  rw [he] at hd
  cases hd
  have := (hk 2 (by decide)).mp (by decide)
  revert this
  decide

/-- **Positive control (promotion without re-relaxation).**  On
`[fixed 1, branch 0, branch 1]` (short 1, long 2, reach 1) all-short is valid;
promoting branch 1 without re-relaxing leaves branch 2 out of reach (no
encodable displacement); re-relaxing restores an encodable displacement. -/
theorem promote_without_relax_breaks_emitDisp :
    Valid chainPrm cascadeValidProg allShort ∧
    emitDisp chainPrm cascadeValidProg allShort 2 = some (-1) ∧
    emitDisp chainPrm cascadeValidProg (promote allShort 1) 2 = none ∧
    emitDisp chainPrm cascadeValidProg (relax chainPrm cascadeValidProg (promote allShort 1)) 2 =
      some (-2) := by
  decide

/-- **Positive control (stale displacements).**  On `[branch 2, fixed 1,
fixed 1]` (short 1, long 2, reach 5), all-short is valid; promoting branch 0
and re-relaxing gives a valid layout, but the displacement computed in the old
layout lands on instruction 1 instead of the target 2 in the new layout. -/
theorem stale_displacement_lands_elsewhere :
    Valid fwdPrm fwdProg allShort ∧
    Valid fwdPrm fwdProg (relax fwdPrm fwdProg (promote allShort 0)) ∧
    ¬ JumpsTo fwdPrm fwdProg (relax fwdPrm fwdProg (promote allShort 0)) 0
        (disp fwdPrm fwdProg allShort 0 2) 2 ∧
    JumpsTo fwdPrm fwdProg (relax fwdPrm fwdProg (promote allShort 0)) 0
        (disp fwdPrm fwdProg allShort 0 2) 1 := by
  decide

/-- Non-vacuity for Result 5: all hypotheses hold for `a = allShort`, `j = 0`
on `[branch 2, fixed 1, fixed 1]` (short 1, long 2, reach 5), and the
promotion is not a no-op. -/
theorem promote_relax_nonvacuity :
    Valid fwdPrm fwdProg allShort ∧ SizesPositiveAt fwdPrm fwdProg allShort ∧
    SizesPositiveAt fwdPrm fwdProg (relax fwdPrm fwdProg (promote allShort 0)) ∧
    allShort 0 = false ∧ relax fwdPrm fwdProg (promote allShort 0) 0 = true := by
  decide

/-- Two self-branches before an alignment directive. -/
def alignGlobalProg : Prog := [.branch 0, .branch 1, .align 4]

/-- Non-vacuity for Result 5 on a program with an alignment directive: the
per-layout positivity hypotheses hold although `AllSizesPositive` (positivity
under every assignment) fails. -/
theorem promote_relax_nonvacuity_aligned :
    Valid fwdPrm alignGlobalProg allShort ∧ SizesPositiveAt fwdPrm alignGlobalProg allShort ∧
    SizesPositiveAt fwdPrm alignGlobalProg (relax fwdPrm alignGlobalProg (promote allShort 0)) ∧
    ¬ AllSizesPositive fwdPrm alignGlobalProg := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro h
  have := h (fun _ => true) 2 (by decide)
  revert this
  decide

end Toy.Relax
