/-
Toy.SCT.Results
===============

Main statements and their non-vacuity witnesses, all fully proved. The proofs use the supporting
modules `Toy.SCT.Ramsey` (infinite Ramsey for pairs), `Toy.SCT.Threads` (thread semantics of
composition), `Toy.SCT.Soundness`, `Toy.SCT.Exactness` and `Toy.SCT.CheckCorrect`.

Cards:
* `ramsey`                    : `infinite_ramsey_pairs_of_finite_colors` (auxiliary)
* `closure-iff-sct`           : `sizeChangeTerminating_of_closureCriterion`,
                                `closureCriterion_of_sizeChangeTerminating`
* `sct-sound-nat`             : `no_consistent_nat_run_of_sizeChangeTerminating`
* `closure-criterion-sound`   : `no_consistent_nat_run_of_closureCriterion`
* `closure-criterion-sound-model` : `terminates_of_stepRespects_of_closureCriterion`
* `closure-criterion-exact`   : `consistent_nat_run_of_not_closureCriterion`
* `checker-correct`           : `closureCriterion_of_checkSCT_eq_true`,
                                `checkSCT_eq_true_of_closureCriterion`
* `lex-implies-closure-criterion` : `closureCriterion_of_lexProjDecreases`
-/
import Toy.SCT.Examples
import Toy.SCT.Soundness
import Toy.SCT.Exactness
import Toy.SCT.CheckCorrect

namespace Toy.SCT

/-! ### Card `ramsey` -/

/-- **Infinite Ramsey theorem for pairs** (auxiliary). If every pair `m < n` of naturals is
coloured by `col m n`, and all colours of such pairs lie in a finite list `S`, then there is a
strictly increasing `h : Nat → Nat` whose pairs all have one and the same colour `a`.
Lee, Jones and Ben-Amram's proof of the closure-criterion direction
`sizeChangeTerminating_of_closureCriterion` uses exactly this principle (colouring a pair of
positions by the composite of the graphs between them). -/
theorem infinite_ramsey_pairs_of_finite_colors {α : Type} (S : List α) (col : Nat → Nat → α)
    (hS : ∀ m n, m < n → col m n ∈ S) :
    ∃ h : Nat → Nat, (∀ m n, m < n → h m < h n) ∧
      ∃ a : α, ∀ m n, m < n → col (h m) (h n) = a :=
  RamseyProof.ramsey S col hS

/-- Non-vacuity of `infinite_ramsey_pairs_of_finite_colors`: the parity colouring
`(m + n) % 2` takes its values in `[0, 1]`; and indeed `h n = 2 n` is homogeneous of colour `0`. -/
theorem infinite_ramsey_nonvacuous :
    (∀ m n : Nat, m < n → (m + n) % 2 ∈ [0, 1]) ∧
    (∀ m n : Nat, m < n → (2 * m < 2 * n ∧ (2 * m + 2 * n) % 2 = 0)) := by
  refine ⟨fun m n _ => ?_, fun m n h => ⟨by omega, by omega⟩⟩
  rcases Nat.mod_two_eq_zero_or_one (m + n) with h | h <;> simp [h]

/-! ### Card `closure-iff-sct` -/

/-- **Closure criterion ⇒ size-change termination** (Lee, Jones and Ben-Amram): if every
idempotent loop graph in the composition closure has a strict self-arc, then every infinite path
through the program's call sites has an infinitely descending thread. -/
theorem sizeChangeTerminating_of_closureCriterion {nf k : Nat} (P : Prog nf k)
    (h : ClosureCriterion P) : SizeChangeTerminating P :=
  sizeChangeTerminating_of_closureCriterion_proof P h

/-- **Size-change termination ⇒ closure criterion** (Lee, Jones and Ben-Amram): if every infinite
path through the program's call sites has an infinitely descending thread, then every idempotent
loop graph in the composition closure has a strict self-arc. -/
theorem closureCriterion_of_sizeChangeTerminating {nf k : Nat} (P : Prog nf k)
    (h : SizeChangeTerminating P) : ClosureCriterion P :=
  -- via exactness: a failing criterion yields a consistent run over `Nat`, which size-change
  -- termination rules out
  Classical.byContradiction fun hnc =>
    no_consistent_nat_run_of_sizeChangeTerminating_proof P h
      (consistent_nat_run_of_not_closureCriterion_proof P hnc)

/-- Size-change termination of the permuting call `f(x, y) = f(y, x - 1)`, proved directly: its
only infinite path is `gSwap, gSwap, …`, which has the thread `x, y, x, y, …`. -/
theorem sizeChangeTerminating_swapDec : SizeChangeTerminating swapDec := by
  intro Gs hpath
  have hG : Gs = fun _ => gSwap :=
    funext fun n => by simpa [swapDec] using (hpath n).1
  rw [hG]
  exact hasInfDescThread_pos

/-- Non-vacuity of card `closure-iff-sct`: the hypotheses of both directions hold for the
permuting call `swapDec` (and for `decLoop`). -/
theorem closure_iff_sct_nonvacuous :
    ClosureCriterion swapDec ∧ SizeChangeTerminating swapDec ∧ SizeChangeTerminating decLoop :=
  ⟨closureCriterion_swapDec, sizeChangeTerminating_swapDec, sizeChangeTerminating_decLoop⟩

/-! ### Card `sct-sound-nat` -/

/-- **Size-change termination is sound over `Nat`**: if every infinite path through the call sites
has an infinitely descending thread, then there is no infinite call sequence with natural-number
argument values consistent with the program's graphs. -/
theorem no_consistent_nat_run_of_sizeChangeTerminating {nf k : Nat} (P : Prog nf k)
    (h : SizeChangeTerminating P) : ¬ ConsistentRunIn Nat P :=
  no_consistent_nat_run_of_sizeChangeTerminating_proof P h

/-- Non-vacuity of card `sct-sound-nat`. -/
theorem sct_sound_nat_nonvacuous : SizeChangeTerminating swapDec := sizeChangeTerminating_swapDec

/-! ### Card `closure-criterion-sound` -/

/-- **Soundness of the closure criterion over `Nat`**: if every idempotent loop graph `G = G ; G`
in the composition closure of the program's graphs has a strict self-arc `(i, i, <)`, then there
is no infinite call sequence with natural-number argument values consistent with the graphs. -/
theorem no_consistent_nat_run_of_closureCriterion {nf k : Nat} (P : Prog nf k)
    (h : ClosureCriterion P) : ¬ ConsistentRunIn Nat P :=
  no_consistent_nat_run_of_sizeChangeTerminating P (sizeChangeTerminating_of_closureCriterion P h)

/-- Non-vacuity of card `closure-criterion-sound`: the criterion holds for the permuting call, for
two mutually recursive functions, and for the Ackermann call structure. -/
theorem closure_criterion_sound_nonvacuous :
    ClosureCriterion swapDec ∧ ClosureCriterion mutProg ∧ ClosureCriterion ackProg :=
  ⟨closureCriterion_swapDec, closureCriterion_mutProg, closureCriterion_ackProg⟩

/-! ### Card `closure-criterion-sound-model` -/

/-- **Soundness for a semantic model**: if a call relation `step` on states (function, argument
vector over `Nat`) makes only calls that are justified by some call-site graph of `P` with matching
endpoints (`StepRespects P step`), and `P` satisfies the closure criterion, then `step` has no
infinite call sequence. -/
theorem terminates_of_stepRespects_of_closureCriterion {nf k : Nat} (P : Prog nf k)
    (step : State nf k → State nf k → Prop) (hstep : StepRespects P step)
    (h : ClosureCriterion P) : Terminates step := by
  rintro ⟨s, hs⟩
  exact no_consistent_nat_run_of_closureCriterion P h
    ⟨fun n => (s n).1, fun n => (s n).2, fun n => Classical.choose (hstep _ _ (hs n)),
      fun n => Classical.choose_spec (hstep _ _ (hs n))⟩

/-- Non-vacuity of card `closure-criterion-sound-model`: the model of
`f(x, y) = if x = 0 then 0 else f(y, x - 1)` respects `swapDec`, which satisfies the criterion. -/
theorem closure_criterion_sound_model_nonvacuous :
    StepRespects swapDec swapStep ∧ ClosureCriterion swapDec :=
  ⟨stepRespects_swapStep, closureCriterion_swapDec⟩

/-! ### Card `closure-criterion-exact` -/

/-- **Exactness of the closure criterion for the abstraction**: if some idempotent loop graph in the
closure has no strict self-arc, then there is an infinite call sequence with natural-number
argument values consistent with the program's graphs. (Failure of the check is never caused by the
check itself; it is caused by the graphs.) -/
theorem consistent_nat_run_of_not_closureCriterion {nf k : Nat} (P : Prog nf k)
    (h : ¬ ClosureCriterion P) : ConsistentRunIn Nat P :=
  consistent_nat_run_of_not_closureCriterion_proof P h

/-- Non-vacuity of card `closure-criterion-exact`: the criterion fails for `f(x, y) = f(x, x - 1)`
and for the alternating program `altProg`. -/
theorem closure_criterion_exact_nonvacuous :
    ¬ ClosureCriterion stallProg ∧ ¬ ClosureCriterion altProg :=
  ⟨not_closureCriterion_stallProg, not_closureCriterion_altProg⟩

/-! ### Card `checker-correct` -/

/-- **The checker is sound**: if `checkSCT P = true` then `P` satisfies the closure criterion. -/
theorem closureCriterion_of_checkSCT_eq_true {nf k : Nat} (P : Prog nf k)
    (h : checkSCT P = true) : ClosureCriterion P :=
  closureCriterion_of_checkSCT_eq_true_proof P h

/-- **The checker is complete**: if `P` satisfies the closure criterion then `checkSCT P = true`
(in particular the fixpoint iteration never runs out of the fuel `closureFuel nf k`). -/
theorem checkSCT_eq_true_of_closureCriterion {nf k : Nat} (P : Prog nf k)
    (h : ClosureCriterion P) : checkSCT P = true :=
  checkSCT_eq_true_of_closureCriterion_proof P h

/-- Non-vacuity of card `checker-correct`: both hypotheses hold for `swapDec`. -/
theorem checker_correct_nonvacuous : checkSCT swapDec = true ∧ ClosureCriterion swapDec :=
  ⟨by decide, closureCriterion_swapDec⟩

/-! ### Card `lex-implies-closure-criterion` -/

/-- The lexicographic order on `L`-tuples of naturals has no infinite descending sequence. -/
theorem lexLt_no_infinite_descent :
    ∀ {L : Nat} (a : Nat → Fin L → Nat), (∀ n, LexLt (a (n + 1)) (a n)) → False
  | 0, _, h => let ⟨l, _⟩ := h 0; l.elim0
  | L + 1, a, h => by
    have hhead_le : ∀ n, a (n + 1) 0 ≤ a n 0 := fun n => lexLt_head_le (h n)
    have hhead_not_inf : ¬ ∀ N, ∃ n, N ≤ n ∧ a (n + 1) 0 < a n 0 :=
      fun hlt => nat_no_inf_weak_descent (fun n => a n 0) hhead_le hlt
    have hstab : ∃ N, ∀ n, N ≤ n → a (n + 1) 0 = a n 0 := by
      have ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n → ¬ (a (n + 1) 0 < a n 0) :=
        Classical.byContradiction fun hne => hhead_not_inf fun N =>
          Classical.byContradiction fun hno => hne ⟨N, fun n hNn hlt => hno ⟨n, hNn, hlt⟩⟩
      exact ⟨N, fun n hNn => Nat.le_antisymm (hhead_le n) (Nat.le_of_not_lt (hN n hNn))⟩
    obtain ⟨N, hN⟩ := hstab
    apply lexLt_no_infinite_descent (L := L) (fun t i => a (N + t) i.succ)
    intro t
    obtain ⟨l, hpre, hlt⟩ := h (N + t)
    have hl0 : l.val ≠ 0 := by
      intro hz
      have e : l = 0 := Fin.ext hz
      subst e
      have heq := hN (N + t) (by omega)
      omega
    let l' : Fin L := ⟨l.val - 1, by omega⟩
    have hl' : l'.succ = l := Fin.ext (by show l.val - 1 + 1 = l.val; omega)
    refine ⟨l', fun i hi => ?_, ?_⟩
    · have hi' : i.succ.val < l.val := by
        show i.val + 1 < l.val
        have : i.val < l.val - 1 := hi
        omega
      have h1 := hpre i.succ hi'
      simpa [Nat.add_assoc] using h1
    · dsimp only
      rw [hl']
      simpa [Nat.add_assoc] using hlt

/-- **Lexicographic projection measures imply the closure criterion**: if some lexicographic
measure built from parameter projections (`ord`, one `L`-tuple of parameters per function)
decreases on every call for all argument values consistent with the call's graph, then the program
satisfies the closure criterion. (Hence `checkSCT` accepts it, by
`checkSCT_eq_true_of_closureCriterion`.) -/
theorem closureCriterion_of_lexProjDecreases {nf k L : Nat} (P : Prog nf k)
    (ord : Fin nf → Fin L → Fin k) (h : LexProjDecreases P ord) : ClosureCriterion P :=
  Classical.byContradiction fun hnc => by
    obtain ⟨fs, vs, Gs, hrun⟩ := consistent_nat_run_of_not_closureCriterion P hnc
    apply lexLt_no_infinite_descent (fun n l => vs n (ord (fs n) l))
    intro n
    obtain ⟨hm, hsrc, hdst, hr⟩ := hrun n
    have hlt := h (Gs n) hm (vs n) (vs (n + 1)) hr
    rw [hsrc, hdst] at hlt
    exact hlt

/-- Non-vacuity of card `lex-implies-closure-criterion`: `(x, y)` decreases lexicographically on
both calls of the Ackermann call structure. -/
theorem lex_implies_closure_criterion_nonvacuous : LexProjDecreases ackProg ackOrd :=
  lexProjDecreases_ackProg

end Toy.SCT
