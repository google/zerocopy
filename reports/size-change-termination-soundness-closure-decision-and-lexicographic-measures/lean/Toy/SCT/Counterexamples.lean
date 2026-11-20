/-
Toy.SCT.Counterexamples
=======================

Counterexample results and hypothesis-tightness witnesses, all fully proved. Each is stated in
canonical form: a concrete instance satisfies every hypothesis that is kept, and the conclusion of
the corresponding main statement fails.

Cards:
* `ramsey` tightness            : `ramsey_infinite_colors_counterexample`
* `sct-not-lex`                 : `swapDec_closureCriterion_and_no_lexProjDecreases`
                                  (positive control `sct_not_lex_positive_control`)
* `nonstrict-self-arcs-insufficient` : `stall_weakSelfArcCriterion_counterexample`
* `generators-insufficient`     : `alt_generatorCriterion_counterexample`
* `composition-tracks-strictness` : `overStrict_composition_counterexample`,
                                  `forget_composition_rejects_mutProg`
* `graphs-must-be-sound`        : `misfit_graphs_counterexample`
* `no-run-length-bound`         : `ackProg_unbounded_finite_runs`
                                  (positive control `no_run_length_bound_positive_control`)
* `sct-incomplete-for-termination` : `countUp_terminates_and_no_sound_prog_passes`
                                  (positive controls `sct_incomplete_positive_control`,
                                  `countUp_size_norm_positive_control`)
* further tightness witnesses   : `decLoop_closureCriterion_consistent_int_run`,
                                  `decLoop_int_model_counterexample`,
                                  `idLoop_runStep_counterexample`, `idLoop_decLoop_contrast`,
                                  `checker_premise_contrast`,
                                  `idLoop_no_lexProjDecreases_not_criterion`,
                                  `loop_guard_needed_for_converse`,
                                  `idempotence_needed_for_converse`
* supporting facts for non-claims : `mutProg_closureCriterion_no_lexProjDecreases`,
                                  `acycProg_closureCriterion_no_lexProjDecreases`,
                                  `swapDec_order_ranking`, `stepRespects_ackLinStep`
-/
import Toy.SCT.Results

namespace Toy.SCT

/-- Every program's most permissive model respects the program. -/
theorem stepRespects_runStep {nf k : Nat} (P : Prog nf k) : StepRespects P (runStep P) :=
  fun _ _ h => h

/-! ### Tightness for `infinite_ramsey_pairs_of_finite_colors` -/

/-- Ramsey needs finitely many colours: the colouring `col m n = m` is covered by no finite list,
and no infinite strictly increasing sequence is homogeneous for it. -/
theorem ramsey_infinite_colors_counterexample :
    (∀ S : List Nat, ¬ ∀ m n : Nat, m < n → m ∈ S) ∧
    ¬ ∃ h : Nat → Nat, (∀ m n, m < n → h m < h n) ∧
      ∃ a : Nat, ∀ m n, m < n → (fun m (_ : Nat) => m) (h m) (h n) = a := by
  constructor
  · intro S hS
    have bound : ∀ (T : List Nat) (x : Nat), x ∈ T → x ≤ T.foldr (· + ·) 0 := by
      intro T x hx
      induction T with
      | nil => simp at hx
      | cons y ys ih =>
        simp only [List.mem_cons] at hx
        simp only [List.foldr_cons]
        rcases hx with rfl | hx
        · omega
        · have := ih hx
          omega
    have hm := hS (S.foldr (· + ·) 0 + 1) (S.foldr (· + ·) 0 + 2) (by omega)
    have := bound S _ hm
    omega
  · rintro ⟨h, hmono, a, ha⟩
    have h0 := ha 0 2 (by decide)
    have h1 := ha 1 2 (by decide)
    have := hmono 0 1 (by decide)
    simp only at h0 h1
    omega

/-! ### Card `sct-not-lex` -/

/-- **The closure criterion accepts a program that has no graph-consistent single-step
lexicographic projection measure.** The permuting call `f(x, y) = f(y, x - 1)` (for `x > 0`;
program `swapDec`):
* satisfies the closure criterion, and `checkSCT` accepts it;
* its intended model `swapStep` (`f(x, y) = if x = 0 then 0 else f(y, x - 1)`) respects the graph
  and terminates (its argument sum decreases);
* yet no lexicographic measure built from parameter projections, of any length `L`, decreases on
  its call for all argument values consistent with the graph; nor does any such measure decrease
  on every call of the model `swapStep` itself. -/
theorem swapDec_closureCriterion_and_no_lexProjDecreases :
    ClosureCriterion swapDec ∧ checkSCT swapDec = true ∧
    StepRespects swapDec swapStep ∧ Terminates swapStep ∧
    (∀ (L : Nat) (ord : Fin 1 → Fin L → Fin 2), ¬ LexProjDecreases swapDec ord) ∧
    (∀ (L : Nat) (ord : Fin 1 → Fin L → Fin 2),
      ¬ ∀ s t, swapStep s t → LexLt (fun l => t.2 (ord t.1 l)) (fun l => s.2 (ord s.1 l))) := by
  refine ⟨closureCriterion_swapDec, by decide, stepRespects_swapStep, terminates_swapStep, ?_, ?_⟩
  · intro L ord h
    cases L with
    | zero =>
      obtain ⟨l, -⟩ := h gSwap (by decide) (vec2 1 2) (vec2 2 0) (by decide)
      exact l.elim0
    | succ L =>
      -- the first component of the measure is a single parameter `ord f0 0`; it can increase
      match hp : ord f0 0 with
      | ⟨0, _⟩ =>
        have hle := lexLt_head_le (h gSwap (by decide) (vec2 1 2) (vec2 2 0) (by decide))
        have e : ord gSwap.dst 0 = 0 := hp
        have e' : ord gSwap.src 0 = 0 := hp
        simp only [e, e'] at hle
        revert hle; decide
      | ⟨1, _⟩ =>
        have hle := lexLt_head_le (h gSwap (by decide) (vec2 2 0) (vec2 0 1) (by decide))
        have e : ord gSwap.dst 0 = 1 := hp
        have e' : ord gSwap.src 0 = 1 := hp
        simp only [e, e'] at hle
        revert hle; decide
  · intro L ord h
    have step1 : swapStep (f0, vec2 1 2) (f0, vec2 2 0) := ⟨rfl, by decide, rfl, rfl⟩
    have step2 : swapStep (f0, vec2 2 0) (f0, vec2 0 1) := ⟨rfl, by decide, rfl, rfl⟩
    cases L with
    | zero =>
      obtain ⟨l, -⟩ := h _ _ step1
      exact l.elim0
    | succ L =>
      match hp : ord f0 0 with
      | ⟨0, _⟩ =>
        have hle := lexLt_head_le (h _ _ step1)
        simp [hp, vec2] at hle
      | ⟨1, _⟩ =>
        have hle := lexLt_head_le (h _ _ step2)
        simp [hp, vec2] at hle

/-- Positive control for card `sct-not-lex`: the Ackermann call structure does have a decreasing
lexicographic projection measure, `(x, y)`. -/
theorem sct_not_lex_positive_control : LexProjDecreases ackProg ackOrd ∧ ClosureCriterion ackProg :=
  ⟨lexProjDecreases_ackProg, closureCriterion_ackProg⟩

/-- An order-based measure for `swapDec` without adding different parameters: `max (2x, 2y + 1)`
(the lexicographic maximum of `⟨x, 0⟩` and `⟨y, 1⟩`, encoded in `Nat`) decreases on every
graph-consistent step. -/
theorem swapDec_order_ranking (u v : Fin 2 → Nat) (h : Respects gSwap u v) :
    max (2 * v 0) (2 * v 1 + 1) < max (2 * u 0) (2 * u 1 + 1) := by
  rw [respects_gSwap_iff] at h
  omega

/-- `LexProjDecreases` requires a decrease on every single call site, so it rejects mutual
recursion that decreases only around a cycle: `mutProg` (`f0(x) = f1(x - 1)`, `f1(y) = f0(y)`)
passes the criterion and the checker but has no graph-consistent lexicographic projection
measure of any length. -/
theorem mutProg_closureCriterion_no_lexProjDecreases :
    ClosureCriterion mutProg ∧ checkSCT mutProg = true ∧
    ∀ (L : Nat) (ord : Fin 2 → Fin L → Fin 1), ¬ LexProjDecreases mutProg ord := by
  refine ⟨closureCriterion_mutProg, by decide, fun L ord h => ?_⟩
  have hr : Respects gMut10 (fun _ => 0) (fun _ => 0) := by decide
  obtain ⟨l, -, hlt⟩ := h gMut10 (by decide) _ _ hr
  exact Nat.lt_irrefl 0 hlt

/-- Arc-free padding slots break `LexProjDecreases`: in the non-recursive `acycProg` the callee
`f1` has no constrained parameter, so no lexicographic projection measure decreases, although the
program trivially satisfies the criterion and is size-change terminating. -/
theorem acycProg_closureCriterion_no_lexProjDecreases :
    ClosureCriterion acycProg ∧ SizeChangeTerminating acycProg ∧
    ∀ (L : Nat) (ord : Fin 2 → Fin L → Fin 1), ¬ LexProjDecreases acycProg ord := by
  refine ⟨loop_guard_example.1, loop_guard_example.2.1, fun L ord h => ?_⟩
  have hr : Respects gAcyc (fun _ => 0) (fun _ => 1) := by decide
  obtain ⟨l, -, hlt⟩ := h gAcyc (List.mem_singleton_self _) _ _ hr
  exact Nat.not_lt_zero _ hlt

/-! ### Card `nonstrict-self-arcs-insufficient` -/

theorem gStall_present_src (a b : Fin 2) (h : gStall.lab a b ≠ Label.absent) : a = 0 := by
  revert a b; decide

/-- `f(x, y) = f(x, x - 1)` is not size-change terminating: along `gStall, gStall, …` a thread
must stay on `x`, whose self-arc is only nonstrict. -/
theorem not_sizeChangeTerminating_stallProg : ¬ SizeChangeTerminating stallProg := by
  intro h
  obtain ⟨n0, p, hpres, hs⟩ := h (fun _ => gStall) (fun _ => ⟨List.mem_singleton_self _, rfl⟩)
  obtain ⟨n, -, hn0, hn⟩ := hs 0
  have hp : p n = 0 := gStall_present_src _ _ (hpres n hn0)
  have hp' : p (n + 1) = 0 := gStall_present_src _ _ (hpres (n + 1) (by omega))
  simp only [hp, hp'] at hn
  revert hn; decide

/-- **Nonstrict self-arcs on idempotents do not suffice.** For `f(x, y) = f(x, x - 1)`
(`stallProg`), every idempotent loop graph in the closure has a self-arc (only nonstrict ones;
the graph also has a strict arc `x → y'`), yet the program is not size-change terminating, there
is an infinite consistent run over `Nat`, and its most permissive model does not terminate. -/
theorem stall_weakSelfArcCriterion_counterexample :
    WeakSelfArcCriterion stallProg ∧ ¬ ClosureCriterion stallProg ∧
    ¬ SizeChangeTerminating stallProg ∧ ConsistentRunIn Nat stallProg ∧
    StepRespects stallProg (runStep stallProg) ∧ ¬ Terminates (runStep stallProg) :=
  ⟨weakSelfArcCriterion_stallProg, not_closureCriterion_stallProg,
    not_sizeChangeTerminating_stallProg, stall_consistentRun, stepRespects_runStep _,
    (consistentRunIn_nat_iff_not_terminates_runStep _).mp stall_consistentRun⟩

/-! ### Card `generators-insufficient` -/

theorem gX_present (a b : Fin 2) (h : gX.lab a b ≠ Label.absent) : a = 0 ∧ b = 0 := by
  revert a b; decide

theorem gY_present (a b : Fin 2) (h : gY.lab a b ≠ Label.absent) : a = 1 ∧ b = 1 := by
  revert a b; decide

/-- The alternating program has an infinite call path without any infinite thread. -/
theorem not_sizeChangeTerminating_altProg : ¬ SizeChangeTerminating altProg := by
  intro h
  have hpath : IsCallPath altProg (fun n => if n % 2 = 0 then gX else gY) := by
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have hn' : (n + 1) % 2 = 1 := by omega
      simp only [hn, hn', ite_true, Nat.one_ne_zero, ite_false]
      decide
    · have hn' : (n + 1) % 2 = 0 := by omega
      simp only [hn, hn', ite_true, Nat.one_ne_zero, ite_false]
      decide
  obtain ⟨n0, p, hpres, -⟩ := h _ hpath
  have h1 := hpres (2 * n0) (by omega)
  have h2 := hpres (2 * n0 + 1) (by omega)
  have e1 : (2 * n0) % 2 = 0 := by omega
  have e2 : (2 * n0 + 1) % 2 = 1 := by omega
  simp only [e1, e2, ite_true, Nat.one_ne_zero, ite_false] at h1 h2
  have := (gX_present _ _ h1).2
  have := (gY_present _ _ h2).1
  simp_all

/-- **Checking only the call-site graphs is unsound.** In `altProg` (calls `f(x - 1, ?)` and
`f(?, y - 1)`) every call-site graph has a strict self-arc and every idempotent call-site graph
passes the test, yet the composite `gX ; gY` is the empty idempotent graph: the program is not
size-change terminating, there is an infinite consistent run over `Nat`, and its most permissive
model does not terminate. -/
theorem alt_generatorCriterion_counterexample :
    (∀ G ∈ altProg.calls, G.HasStrictSelfArc) ∧ GeneratorCriterion altProg ∧
    ¬ ClosureCriterion altProg ∧ ¬ SizeChangeTerminating altProg ∧ ConsistentRunIn Nat altProg ∧
    StepRespects altProg (runStep altProg) ∧ ¬ Terminates (runStep altProg) :=
  ⟨by decide, generatorCriterion_altProg, not_closureCriterion_altProg,
    not_sizeChangeTerminating_altProg, alt_consistentRun, stepRespects_runStep _,
    (consistentRunIn_nat_iff_not_terminates_runStep _).mp alt_consistentRun⟩

/-! ### Card `composition-tracks-strictness` -/

/-- **Over-claiming strictness in composition is unsound.** With the sequencing
`seqOverStrict` (`≤ ; ≤ = <`), the criterion accepts `f(x) = f(x)` (`idLoop`), which fails the
standard criterion, is not size-change terminating, has an infinite consistent run over `Nat`,
and whose most permissive model does not terminate. -/
theorem overStrict_composition_counterexample :
    CriterionWith Label.seqOverStrict idLoop ∧ ¬ ClosureCriterion idLoop ∧
    ¬ SizeChangeTerminating idLoop ∧
    ConsistentRunIn Nat idLoop ∧ StepRespects idLoop (runStep idLoop) ∧
    ¬ Terminates (runStep idLoop) :=
  ⟨criterionWith_overStrict_idLoop, not_closureCriterion_idLoop, not_sizeChangeTerminating_idLoop,
    consistentRun_idLoop, stepRespects_runStep _, not_terminates_runStep_idLoop⟩

/-- **Forgetting mixed strictness in composition loses completeness.** With either lossy
sequencing, `seqForgetLeft` (`≤ ; < = ≤`) or `seqForgetRight` (`< ; ≤ = ≤`), the criterion
rejects the mutually recursive `mutProg` (`f0(x) = f1(x - 1)` for `x > 0`, `f1(y) = f0(y)`),
although `mutProg` satisfies the standard criterion, is size-change terminating and has no
infinite consistent run over `Nat`. (Both lossy sequencings still accept `decLoop` and `swapDec`:
`criterionWith_forgetLeft_pos`, `criterionWith_forgetRight_pos`.) -/
theorem forget_composition_rejects_mutProg :
    ¬ CriterionWith Label.seqForgetLeft mutProg ∧ ¬ CriterionWith Label.seqForgetRight mutProg ∧
    ClosureCriterion mutProg ∧ SizeChangeTerminating mutProg ∧ ¬ ConsistentRunIn Nat mutProg :=
  ⟨not_criterionWith_forgetLeft_mutProg, not_criterionWith_forgetRight_mutProg,
    closureCriterion_mutProg, sizeChangeTerminating_of_closureCriterion _ closureCriterion_mutProg,
    no_consistent_nat_run_of_closureCriterion _ closureCriterion_mutProg⟩

/-- The loop guard is needed for the converse of the characterization: the non-recursive
`acycProg` is size-change terminating and satisfies the criterion, but the guard-free variant
rejects it. -/
theorem loop_guard_needed_for_converse :
    SizeChangeTerminating acycProg ∧ ClosureCriterion acycProg ∧ ¬ NoLoopGuardCriterion acycProg :=
  ⟨loop_guard_example.2.1, loop_guard_example.1, not_noLoopGuardCriterion_acycProg⟩

/-- Idempotence is needed for the converse of the characterization: `swapDec` is size-change
terminating and satisfies the criterion, but its loop graph `gSwap` (not idempotent) has no
strict self-arc, so the idempotence-free variant rejects it. -/
theorem idempotence_needed_for_converse :
    SizeChangeTerminating swapDec ∧ ClosureCriterion swapDec ∧ ¬ AllLoopsCriterion swapDec :=
  ⟨sizeChangeTerminating_swapDec, closureCriterion_swapDec, not_allLoopsCriterion_swapDec⟩

/-! ### Tightness of the `Nat` value domain -/

/-- **Soundness needs well-founded values.** `f(x) = f(x - 1)` satisfies the closure criterion and
is size-change terminating, but over the integers it has the infinite consistent run
`0, -1, -2, …`. -/
theorem decLoop_closureCriterion_consistent_int_run :
    ClosureCriterion decLoop ∧ SizeChangeTerminating decLoop ∧ ConsistentRunIn Int decLoop := by
  refine ⟨closureCriterion_decLoop, sizeChangeTerminating_decLoop,
    fun _ => f0, fun n _ => -(n : Int), fun _ => gDec, fun n => ⟨List.mem_singleton_self _, rfl, rfl, ?_⟩⟩
  exact respects_gDec_iff.mpr (by simp only; omega)

/-- The model `x ↦ x - 1` over integer states (no guard) respects the graph `x' < x` of `decLoop`
on every call, `decLoop` satisfies the criterion, and the model does not terminate: the
`Nat`-valued states of `terminates_of_stepRespects_of_closureCriterion` are needed. -/
theorem decLoop_int_model_counterexample :
    ClosureCriterion decLoop ∧
    (∀ s t : Fin 1 × (Fin 1 → Int), (t.1 = s.1 ∧ t.2 0 = s.2 0 - 1) →
      ∃ G ∈ decLoop.calls, G.src = s.1 ∧ G.dst = t.1 ∧ RespectsIn G s.2 t.2) ∧
    ¬ Terminates (fun s t : Fin 1 × (Fin 1 → Int) => t.1 = s.1 ∧ t.2 0 = s.2 0 - 1) := by
  refine ⟨closureCriterion_decLoop, fun s t ⟨_, h2⟩ => ?_, fun hT => hT ?_⟩
  · exact ⟨gDec, List.mem_singleton_self _, fin_one_eq _ _, fin_one_eq _ _,
      respects_gDec_iff.mpr (by omega)⟩
  · exact ⟨fun n => (f0, fun _ => -(n : Int)), fun n => ⟨rfl, by simp only; omega⟩⟩

/-! ### Card `graphs-must-be-sound` -/

/-- The model of `f(x) = f(x - 1)` with the guard forgotten: truncated subtraction, so `0` calls
`0` forever. -/
def unguardedDecStep : State 1 1 → State 1 1 → Prop :=
  fun s t => t.1 = s.1 ∧ t.2 0 = s.2 0 - 1

/-- **A passed check licenses nothing about calls the graphs do not describe.** `decLoop` (graph
`x' < x`) satisfies the criterion and `checkSCT` accepts it. The model of `f(x) = f(x - 1)` with
the base-case guard forgotten (`unguardedDecStep`, truncated subtraction) respects that graph on
every call with `x > 0`, but not on the call `0 ↦ 0 - 1 = 0`, and it does not terminate; nor does
the model `idStep` of `f(x) = f(x)`. -/
theorem misfit_graphs_counterexample :
    ClosureCriterion decLoop ∧ checkSCT decLoop = true ∧
    (∀ s t, unguardedDecStep s t → 0 < s.2 0 → Respects gDec s.2 t.2) ∧
    ¬ StepRespects decLoop unguardedDecStep ∧ ¬ Terminates unguardedDecStep ∧
    ¬ StepRespects decLoop idStep ∧ ¬ Terminates idStep := by
  refine ⟨closureCriterion_decLoop, by decide, fun s t ⟨_, h2⟩ hpos => ?_, fun h => ?_,
    fun hT => hT ⟨fun _ => (f0, fun _ => 0), fun _ => ⟨rfl, rfl⟩⟩,
    not_stepRespects_idStep, not_terminates_idStep⟩
  · exact respects_gDec_iff.mpr (by omega)
  · obtain ⟨G, hG, -, -, hr⟩ := h (f0, fun _ => 0) (f0, fun _ => 0) ⟨rfl, rfl⟩
    have e : G = gDec := by simpa [decLoop] using hG
    subst e
    have := respects_gDec_iff.mp hr
    exact Nat.lt_irrefl 0 this

/-- Tightness of the criterion for `terminates_of_stepRespects_of_closureCriterion`: `idLoop`'s most
permissive model respects `idLoop`, the criterion fails, and the model does not terminate. -/
theorem idLoop_runStep_counterexample :
    StepRespects idLoop (runStep idLoop) ∧ ¬ ClosureCriterion idLoop ∧
    ¬ Terminates (runStep idLoop) :=
  ⟨stepRespects_runStep _, not_closureCriterion_idLoop, not_terminates_runStep_idLoop⟩

/-- Tightness of `¬ ClosureCriterion P` in `consistent_nat_run_of_not_closureCriterion`, and of
`SizeChangeTerminating P` in `closureCriterion_of_sizeChangeTerminating`, and of the hypothesis of
`no_consistent_nat_run_of_sizeChangeTerminating`: `idLoop` fails the criterion, is not
size-change terminating and has a run; `decLoop` satisfies the criterion and has none. -/
theorem idLoop_decLoop_contrast :
    ¬ ClosureCriterion idLoop ∧ ¬ SizeChangeTerminating idLoop ∧ ConsistentRunIn Nat idLoop ∧
    ClosureCriterion decLoop ∧ ¬ ConsistentRunIn Nat decLoop :=
  ⟨not_closureCriterion_idLoop, not_sizeChangeTerminating_idLoop, consistentRun_idLoop,
    closureCriterion_decLoop, not_consistentRun_decLoop⟩

/-- Tightness of the premises of card `checker-correct`: for `idLoop` the checker rejects and the
criterion fails. -/
theorem checker_premise_contrast : checkSCT idLoop = false ∧ ¬ ClosureCriterion idLoop :=
  ⟨by decide, not_closureCriterion_idLoop⟩

/-- Tightness of `LexProjDecreases P ord` in `closureCriterion_of_lexProjDecreases`: no
lexicographic projection measure decreases on `f(x) = f(x)`, and the criterion fails. -/
theorem idLoop_no_lexProjDecreases_not_criterion :
    (∀ (L : Nat) (ord : Fin 1 → Fin L → Fin 1), ¬ LexProjDecreases idLoop ord) ∧
    ¬ ClosureCriterion idLoop := by
  refine ⟨fun L ord h => ?_, not_closureCriterion_idLoop⟩
  have hr : Respects gId (fun _ => 0) (fun _ => 0) := by decide
  obtain ⟨l, -, hlt⟩ := h gId (List.mem_singleton_self _) _ _ hr
  exact Nat.lt_irrefl 0 hlt

/-! ### Card `no-run-length-bound` -/

/-- **No bound on run length in the abstraction.** The Ackermann call structure `ackProg`
satisfies the closure criterion and even has a decreasing lexicographic projection measure, yet
from the single start state `f(1, 0)` there are consistent finite runs of every length `N`: for
`N ≥ 1`, first the call `f(0, N - 1)` (allowed because `gX` leaves the second argument
unconstrained), then `N - 1` calls decreasing `y` to `0`. The unboundedness comes from that
unconstrained argument, i.e. from infinitely many possible successors of one state; the criterion
and the measure do not bound the number of calls in terms of the start state of the abstraction. -/
theorem ackProg_unbounded_finite_runs :
    ClosureCriterion ackProg ∧ LexProjDecreases ackProg ackOrd ∧
    ∀ N : Nat, FiniteRunFrom ackProg f0 (vec2 1 0) N := by
  refine ⟨closureCriterion_ackProg, lexProjDecreases_ackProg, fun N => ?_⟩
  refine ⟨fun _ => f0, fun n => if n = 0 then vec2 1 0 else vec2 0 (N - n),
    fun n => if n = 0 then gX else gKeepX, rfl, rfl, fun n hn => ?_⟩
  cases n with
  | zero =>
    simp only [ite_true, Nat.add_one_ne_zero, ite_false]
    exact ⟨by decide, rfl, rfl, respects_gX_iff.mpr (by simp [vec2])⟩
  | succ m =>
    simp only [Nat.add_one_ne_zero, ite_false]
    exact ⟨by decide, rfl, rfl, respects_gKeepX_iff.mpr ⟨by simp [vec2], by simp [vec2]; omega⟩⟩

/-- Positive control for card `no-run-length-bound`: for `f(x) = f(x - 1)` every consistent run from
argument `u 0` has at most `u 0` steps. -/
theorem no_run_length_bound_positive_control (u : Fin 1 → Nat) (N : Nat)
    (h : FiniteRunFrom decLoop f0 u N) : N ≤ u 0 :=
  decLoop_finiteRun_length_le u N h

/-- The deterministic, linear-time program
`f(x, y) = if x > 0 then f(x - 1, y + 1) else if y > 0 then f(x, y - 1) else 0` is described by the
same graphs `ackProg` as the Ackermann call structure. -/
def ackLinStep : State 1 2 → State 1 2 → Prop :=
  fun s t => t.1 = s.1 ∧
    ((0 < s.2 0 ∧ t.2 0 = s.2 0 - 1 ∧ t.2 1 = s.2 1 + 1) ∨
     (s.2 0 = 0 ∧ 0 < s.2 1 ∧ t.2 0 = s.2 0 ∧ t.2 1 = s.2 1 - 1))

theorem stepRespects_ackLinStep : StepRespects ackProg ackLinStep := by
  rintro s t ⟨h1, (⟨h2, h3, -⟩ | ⟨h2, h3, h4, h5⟩)⟩
  · exact ⟨gX, by decide, fin_one_eq _ _, fin_one_eq _ _, respects_gX_iff.mpr (by omega)⟩
  · exact ⟨gKeepX, by decide, fin_one_eq _ _, fin_one_eq _ _,
      respects_gKeepX_iff.mpr ⟨by omega, by omega⟩⟩

/-! ### Card `sct-incomplete-for-termination` -/

/-- **Failing the check does not mean non-termination.** `f(x) = if x < 100 then f(x + 1) else 0`
(model `countUpStep`, one function, one parameter slot holding the raw argument `x`) terminates,
yet every program `P : Prog 1 1` whose graphs describe all of its calls (`StepRespects`) fails the
closure criterion: the call `0 ↦ 1` forces some call-site graph without arcs. -/
theorem countUp_terminates_and_no_sound_prog_passes :
    Terminates countUpStep ∧
    ∀ P : Prog 1 1, StepRespects P countUpStep → ¬ ClosureCriterion P := by
  refine ⟨terminates_countUpStep, fun P hstep hcrit => ?_⟩
  obtain ⟨G, hGmem, -, -, hr⟩ := hstep (f0, fun _ => 0) (f0, fun _ => 1) ⟨rfl, by decide, rfl⟩
  have hlab : G.lab 0 0 = Label.absent := by
    have h00 := hr 0 0
    revert h00
    cases G.lab 0 0 <;> simp
  have hGe : G = gEmpty1 := by
    refine SCG.ext_iff'.mpr ⟨fin_one_eq _ _, fin_one_eq _ _, fun i j => ?_⟩
    rw [fin_one_eq i 0, fin_one_eq j 0, hlab]
    decide
  subst hGe
  have := hcrit gEmpty1 (.gen hGmem) rfl (by decide)
  revert this; decide

/-- Positive control (escape hatch) for card `sct-incomplete-for-termination`: measured by the size
norm `100 - x` instead of the raw argument, every call of `countUpStep` respects the graph `x' < x`
of `decLoop`, which passes the criterion. -/
theorem countUp_size_norm_positive_control :
    (∀ s t, countUpStep s t → Respects gDec (fun _ => 100 - s.2 0) (fun _ => 100 - t.2 0)) ∧
    ClosureCriterion decLoop := by
  refine ⟨fun s t ⟨_, h2, h3⟩ => respects_gDec_iff.mpr (by omega),
    closureCriterion_decLoop⟩

/-- Positive control for card `sct-incomplete-for-termination`: for `f(x) = f(x - 1)` the sound
graph `x' < x` passes and the model terminates. -/
theorem sct_incomplete_positive_control :
    StepRespects decLoop decStep ∧ ClosureCriterion decLoop ∧ Terminates decStep := by
  refine ⟨?_, closureCriterion_decLoop, ?_⟩
  · rintro s t ⟨h1, h2, h3⟩
    exact ⟨gDec, List.mem_singleton_self _, fin_one_eq _ _, fin_one_eq _ _,
      respects_gDec_iff.mpr (by omega)⟩
  · rintro ⟨s, hs⟩
    apply nat_no_infinite_descent (fun n => (s n).2 0)
    intro n
    obtain ⟨-, h2, h3⟩ := hs n
    omega

end Toy.SCT
