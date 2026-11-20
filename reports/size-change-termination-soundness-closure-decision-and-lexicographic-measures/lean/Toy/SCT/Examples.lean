/-
Toy.SCT.Examples
================

Helper lemmas about the fixtures, and the proved positive and negative examples of every
definition. Everything in this module is fully proved.
-/
import Toy.SCT.Fixtures

namespace Toy.SCT

/-! ### Small helpers -/

theorem forall_fin_two {p : Fin 2 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 :=
  ⟨fun h => ⟨h 0, h 1⟩, fun ⟨h0, h1⟩ i => match i with | ⟨0, _⟩ => h0 | ⟨1, _⟩ => h1⟩

theorem forall_fin_one {p : Fin 1 → Prop} : (∀ i, p i) ↔ p 0 :=
  ⟨fun h => h 0, fun h0 i => match i with | ⟨0, _⟩ => h0⟩

theorem fin_one_eq (a b : Fin 1) : a = b :=
  Fin.ext (by have := a.isLt; have := b.isLt; omega)

/-- A sequence of naturals cannot decrease strictly forever. -/
theorem nat_no_infinite_descent (m : Nat → Nat) (h : ∀ n, m (n + 1) < m n) : False := by
  have key : ∀ n, m n + n ≤ m 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := h n; omega
  have := key (m 0 + 1)
  omega

theorem respects_gDec_iff {α : Type} [LT α] [LE α] {u v : Fin 1 → α} :
    RespectsIn gDec u v ↔ v 0 < u 0 := by
  simp +decide only [RespectsIn, forall_fin_one, true_implies, false_implies, and_true]

theorem respects_gId_iff {α : Type} [LT α] [LE α] {u v : Fin 1 → α} :
    RespectsIn gId u v ↔ v 0 ≤ u 0 := by
  simp +decide only [RespectsIn, forall_fin_one, true_implies, false_implies, true_and]

theorem respects_gSwap_iff {u v : Fin 2 → Nat} :
    Respects gSwap u v ↔ v 0 ≤ u 1 ∧ v 1 < u 0 := by
  simp +decide only [Respects, RespectsIn, forall_fin_two, true_implies, false_implies, and_true,
    true_and]
  try exact And.comm

theorem respects_gX_iff {u v : Fin 2 → Nat} : Respects gX u v ↔ v 0 < u 0 := by
  simp +decide only [Respects, RespectsIn, forall_fin_two, true_implies, false_implies, and_true]

theorem respects_gKeepX_iff {u v : Fin 2 → Nat} :
    Respects gKeepX u v ↔ v 0 ≤ u 0 ∧ v 1 < u 1 := by
  simp +decide only [Respects, RespectsIn, forall_fin_two, true_implies, false_implies, and_true,
    true_and]
  try exact And.comm

theorem respects_gStall_iff {u v : Fin 2 → Nat} :
    Respects gStall u v ↔ v 0 ≤ u 0 ∧ v 1 < u 0 := by
  simp +decide only [Respects, RespectsIn, forall_fin_two, true_implies, false_implies, and_true,
    true_and]
  try exact And.comm

/-- The first component of a lexicographically smaller tuple is no larger. -/
theorem lexLt_head_le {L : Nat} {a b : Fin (L + 1) → Nat} (h : LexLt a b) : a 0 ≤ b 0 := by
  obtain ⟨l, hpre, hlt⟩ := h
  by_cases hl : l.val = 0
  · have : l = 0 := Fin.ext hl
    subst this
    omega
  · have := hpre 0 (by simp; omega)
    omega

/-- A consistent infinite run over `Nat` is the same as non-termination of the most permissive
model `runStep P`. -/
theorem consistentRunIn_nat_iff_not_terminates_runStep {nf k : Nat} (P : Prog nf k) :
    ConsistentRunIn Nat P ↔ ¬ Terminates (runStep P) := by
  constructor
  · rintro ⟨fs, vs, Gs, h⟩ hT
    exact hT ⟨fun n => (fs n, vs n), fun n =>
      ⟨Gs n, (h n).1, (h n).2.1, (h n).2.2.1, (h n).2.2.2⟩⟩
  · intro hT
    have hs : ∃ s : Nat → State nf k, ∀ n, runStep P (s n) (s (n + 1)) :=
      Classical.byContradiction hT
    obtain ⟨s, hs⟩ := hs
    refine ⟨fun n => (s n).1, fun n => (s n).2, fun n => Classical.choose (hs n), fun n => ?_⟩
    obtain ⟨hm, h1, h2, h3⟩ := Classical.choose_spec (hs n)
    exact ⟨hm, h1, h2, h3⟩

/-! ### Concrete closures -/

theorem closure_swapDec_sub {G : SCG 1 2} (h : InClosure swapDec G) :
    G ∈ [gSwap, gSwap2, gSwap3] :=
  inClosureWith_mem_of_closed (by decide) (by decide) h

theorem closure_stallProg_sub {G : SCG 1 2} (h : InClosure stallProg G) : G = gStall := by
  have := inClosureWith_mem_of_closed (S := [gStall]) (by decide) (by decide) h
  simpa using this

theorem closure_idLoop_sub {G : SCG 1 1} (h : InClosure idLoop G) : G = gId := by
  have := inClosureWith_mem_of_closed (S := [gId]) (by decide) (by decide) h
  simpa using this

theorem inClosure_altProg_empty : InClosure altProg gEmpty2 := by
  have h : InClosure altProg (gX.compWith Label.seq gY) :=
    .comp (.gen (by decide)) (.gen (by decide)) rfl
  have e : gX.compWith Label.seq gY = gEmpty2 := by decide
  rw [e] at h
  exact h

/-! ### `Label.seq`, `Label.join` and the alternative sequencings -/

theorem seq_pos : Label.seq .nonstrict .strict = .strict ∧ Label.seq .strict .nonstrict = .strict ∧
    Label.seq .nonstrict .nonstrict = .nonstrict := by decide
theorem seq_neg : Label.seq .nonstrict .nonstrict ≠ .strict ∧ Label.seq .absent .strict = .absent ∧
    Label.seq .strict .absent = .absent := by decide

theorem join_pos : Label.join .nonstrict .strict = .strict ∧ Label.join .absent .nonstrict = .nonstrict :=
  by decide
theorem join_neg : Label.join .nonstrict .absent ≠ .absent ∧ Label.join .absent .absent = .absent := by
  decide

theorem seqOverStrict_pos : Label.seqOverStrict .nonstrict .nonstrict = .strict := by decide
theorem seqOverStrict_neg : Label.seqOverStrict .nonstrict .absent = .absent := by decide
theorem seqForgetLeft_pos : Label.seqForgetLeft .nonstrict .strict = .nonstrict ∧
    Label.seqForgetLeft .strict .nonstrict = .strict := by decide
theorem seqForgetLeft_neg : Label.seqForgetLeft .nonstrict .strict ≠ .strict ∧
    Label.seqForgetLeft .absent .strict = .absent := by decide
theorem seqForgetRight_pos : Label.seqForgetRight .strict .nonstrict = .nonstrict ∧
    Label.seqForgetRight .nonstrict .strict = .strict := by decide
theorem seqForgetRight_neg : Label.seqForgetRight .strict .nonstrict ≠ .strict ∧
    Label.seqForgetRight .strict .absent = .absent := by decide

/-! ### Composition -/

/-- `f(x, y) = f(y, x - 1)` twice: both parameters strictly decrease. -/
theorem comp_pos : gSwap.comp gSwap = gSwap2 ∧ gX.comp gY = gEmpty2 ∧ gSwap2.comp gSwap = gSwap3 := by
  decide
/-- Composition is not the identity on `gSwap`, and it records strictness: `gId ; gId` stays
nonstrict. -/
theorem comp_neg : gSwap.comp gSwap ≠ gSwap ∧ gId.comp gId ≠ gDec := by decide

/-- With over-strict sequencing, `≤ ; ≤` becomes `<`. -/
theorem compWith_overStrict_gId : gId.compWith Label.seqOverStrict gId = gDec := by decide
/-- With the left-forgetful sequencing `Label.seqForgetLeft`, the nonstrict-then-strict thread
`≤ ; <` (`gMut10`, then `gMut01`) composes to `≤`, so the two-call cycle of `mutProg` loses its
strict self-arc. (`< ; <` still composes to `<` under both lossy sequencings.) -/
theorem compWith_forgetLeft_mut : gMut10.compWith Label.seqForgetLeft gMut01 = arcsG 1 1 [(0, 0, .nonstrict)] := by
  decide
/-- With the right-forgetful sequencing `Label.seqForgetRight`, the strict-then-nonstrict thread
`< ; ≤` (`gMut01`, then `gMut10`) composes to `≤`. -/
theorem compWith_forgetRight_mut : gMut01.compWith Label.seqForgetRight gMut10 = arcsG 0 0 [(0, 0, .nonstrict)] := by
  decide

/-! ### Self-arcs -/

theorem hasStrictSelfArc_pos : gSwap2.HasStrictSelfArc ∧ gKeepX.HasStrictSelfArc := by decide
theorem hasStrictSelfArc_neg : ¬ gSwap.HasStrictSelfArc ∧ ¬ gStall.HasStrictSelfArc := by decide
theorem hasSelfArc_pos : gStall.HasSelfArc := by decide
theorem hasSelfArc_neg : ¬ gSwap.HasSelfArc ∧ ¬ gEmpty2.HasSelfArc := by decide

/-! ### Closure -/

theorem inClosure_pos : InClosure swapDec gSwap2 ∧ InClosure swapDec gSwap3 := by
  have h1 : InClosure swapDec (gSwap.compWith Label.seq gSwap) :=
    .comp (.gen (by decide)) (.gen (by decide)) rfl
  have e1 : gSwap.compWith Label.seq gSwap = gSwap2 := by decide
  rw [e1] at h1
  have h2 : InClosure swapDec (gSwap2.compWith Label.seq gSwap) :=
    .comp h1 (.gen (by decide)) rfl
  have e2 : gSwap2.compWith Label.seq gSwap = gSwap3 := by decide
  rw [e2] at h2
  exact ⟨h1, h2⟩

theorem inClosure_neg : ¬ InClosure swapDec gStall ∧ ¬ InClosure swapDec gEmpty2 := by
  constructor
  · intro h; have := closure_swapDec_sub h; revert this; decide
  · intro h; have := closure_swapDec_sub h; revert this; decide

/-! ### The closure criterion and its variants -/

theorem closureCriterion_swapDec : ClosureCriterion swapDec :=
  criterionWith_of_closed [gSwap, gSwap2, gSwap3] (by decide) (by decide) (by decide)

theorem closureCriterion_decLoop : ClosureCriterion decLoop :=
  criterionWith_of_closed [gDec] (by decide) (by decide) (by decide)

theorem closureCriterion_ackProg : ClosureCriterion ackProg :=
  criterionWith_of_closed [gX, gKeepX] (by decide) (by decide) (by decide)

theorem closureCriterion_mutProg : ClosureCriterion mutProg :=
  criterionWith_of_closed [gMut01, gMut10, gMut00, gMut11, gMut10s] (by decide) (by decide)
    (by decide)

theorem not_closureCriterion_idLoop : ¬ ClosureCriterion idLoop := by
  intro h
  have := h gId (.gen (by decide)) rfl (by decide)
  revert this; decide

theorem not_closureCriterion_stallProg : ¬ ClosureCriterion stallProg := by
  intro h
  have := h gStall (.gen (by decide)) rfl (by decide)
  revert this; decide

theorem not_closureCriterion_altProg : ¬ ClosureCriterion altProg := by
  intro h
  have := h gEmpty2 inClosure_altProg_empty rfl (by decide)
  revert this; decide

theorem weakSelfArcCriterion_stallProg : WeakSelfArcCriterion stallProg := by
  intro G hG _ _
  rw [closure_stallProg_sub hG]
  decide

theorem not_weakSelfArcCriterion_altProg : ¬ WeakSelfArcCriterion altProg := by
  intro h
  have := h gEmpty2 inClosure_altProg_empty rfl (by decide)
  revert this; decide

theorem generatorCriterion_altProg : GeneratorCriterion altProg := by
  unfold GeneratorCriterion; decide

theorem not_generatorCriterion_idLoop : ¬ GeneratorCriterion idLoop := by
  unfold GeneratorCriterion; decide

theorem criterionWith_overStrict_idLoop : CriterionWith Label.seqOverStrict idLoop :=
  criterionWith_of_closed [gId, gDec] (by decide) (by decide) (by decide)

theorem not_criterionWith_overStrict_altProg : ¬ CriterionWith Label.seqOverStrict altProg := by
  intro h
  have hc : InClosureWith Label.seqOverStrict altProg (gX.compWith Label.seqOverStrict gY) :=
    .comp (.gen (by decide)) (.gen (by decide)) rfl
  have e : gX.compWith Label.seqOverStrict gY = gEmpty2 := by decide
  rw [e] at hc
  have := h gEmpty2 hc rfl (by decide)
  revert this; decide

/-- The lossy sequencings are not degenerate: both accept `f(x) = f(x - 1)` and the permuting
call `f(x, y) = f(y, x - 1)`. -/
theorem criterionWith_forgetLeft_pos :
    CriterionWith Label.seqForgetLeft decLoop ∧ CriterionWith Label.seqForgetLeft swapDec :=
  ⟨criterionWith_of_closed [gDec] (by decide) (by decide) (by decide),
    criterionWith_of_closed
      [gSwap, arcsG f0 f0 [(0, 0, .strict), (1, 1, .nonstrict)],
       arcsG f0 f0 [(0, 1, .strict), (1, 0, .nonstrict)]]
      (by decide) (by decide) (by decide)⟩

theorem criterionWith_forgetRight_pos :
    CriterionWith Label.seqForgetRight decLoop ∧ CriterionWith Label.seqForgetRight swapDec :=
  ⟨criterionWith_of_closed [gDec] (by decide) (by decide) (by decide),
    criterionWith_of_closed
      [gSwap, arcsG f0 f0 [(0, 0, .nonstrict), (1, 1, .strict)]]
      (by decide) (by decide) (by decide)⟩

/-- Both lossy sequencings reject the mutually recursive `mutProg`: the two-call cycle
`f1 → f0 → f1` (resp. `f0 → f1 → f0`) composes `≤ ; <` (resp. `< ; ≤`) to `≤`, giving an
idempotent loop with only a nonstrict self-arc. -/
theorem not_criterionWith_forgetLeft_mutProg : ¬ CriterionWith Label.seqForgetLeft mutProg := by
  intro h
  have h11 : InClosureWith Label.seqForgetLeft mutProg (gMut10.compWith Label.seqForgetLeft gMut01) :=
    .comp (.gen (by decide)) (.gen (by decide)) rfl
  have hidem : (gMut10.compWith Label.seqForgetLeft gMut01).compWith Label.seqForgetLeft
      (gMut10.compWith Label.seqForgetLeft gMut01) = gMut10.compWith Label.seqForgetLeft gMut01 := by
    decide
  have hs := h _ h11 rfl hidem
  revert hs; decide

theorem not_criterionWith_forgetRight_mutProg : ¬ CriterionWith Label.seqForgetRight mutProg := by
  intro h
  have h00 : InClosureWith Label.seqForgetRight mutProg (gMut01.compWith Label.seqForgetRight gMut10) :=
    .comp (.gen (by decide)) (.gen (by decide)) rfl
  have hidem : (gMut01.compWith Label.seqForgetRight gMut10).compWith Label.seqForgetRight
      (gMut01.compWith Label.seqForgetRight gMut10) = gMut01.compWith Label.seqForgetRight gMut10 := by
    decide
  have hs := h _ h00 rfl hidem
  revert hs; decide

/-- Why the criterion only tests loops (`G.src = G.dst`): in the non-recursive program `acycProg`
the closure contains a graph `G` with `G ; G = G` (as label matrices, composition being total) and
no strict self-arc, but `G` goes from `f0` to `f1`. The criterion holds, the program is
size-change terminating (it has no infinite call path) and has no infinite run; testing that graph
would wrongly reject the program. -/
theorem loop_guard_example :
    ClosureCriterion acycProg ∧ SizeChangeTerminating acycProg ∧ ¬ ConsistentRunIn Nat acycProg ∧
    InClosure acycProg gAcyc ∧ gAcyc.comp gAcyc = gAcyc ∧ ¬ gAcyc.HasStrictSelfArc := by
  refine ⟨criterionWith_of_closed [gAcyc] (by decide) (by decide) (by decide), ?_, ?_,
    .gen (List.mem_singleton_self _), by decide, by decide⟩
  · intro Gs hpath
    have e0 : Gs 0 = gAcyc := by simpa [acycProg] using (hpath 0).1
    have e1 : Gs 1 = gAcyc := by simpa [acycProg] using (hpath 1).1
    have hlink := (hpath 0).2
    rw [e0, e1] at hlink
    have hne : gAcyc.dst ≠ gAcyc.src := by decide
    exact absurd hlink hne
  · rintro ⟨fs, vs, Gs, h⟩
    obtain ⟨hm0, -, hd0, -⟩ := h 0
    obtain ⟨hm1, hs1, -, -⟩ := h 1
    have e0 : Gs 0 = gAcyc := by simpa [acycProg] using hm0
    have e1 : Gs 1 = gAcyc := by simpa [acycProg] using hm1
    rw [e0] at hd0
    rw [e1] at hs1
    have : (gAcyc.dst : Fin 2) = gAcyc.src := hd0.trans hs1.symm
    revert this; decide

theorem closure_decLoop_sub {G : SCG 1 1} (h : InClosure decLoop G) : G = gDec := by
  have := inClosureWith_mem_of_closed (S := [gDec]) (by decide) (by decide) h
  simpa using this

/-- Positive and negative examples of the guard-free and idempotence-free variants of the
criterion. -/
theorem noLoopGuardCriterion_decLoop : NoLoopGuardCriterion decLoop := by
  intro G hG _
  rw [closure_decLoop_sub hG]
  decide

theorem not_noLoopGuardCriterion_acycProg : ¬ NoLoopGuardCriterion acycProg := by
  intro h
  have := h gAcyc (.gen (List.mem_singleton_self _)) (by decide)
  revert this; decide

theorem allLoopsCriterion_decLoop : AllLoopsCriterion decLoop := by
  intro G hG _
  rw [closure_decLoop_sub hG]
  decide

theorem not_allLoopsCriterion_swapDec : ¬ AllLoopsCriterion swapDec := by
  intro h
  have := h gSwap (.gen (List.mem_singleton_self _)) rfl
  revert this; decide

/-! ### `RespectsIn` -/

theorem respects_pos : Respects gSwap (vec2 1 2) (vec2 2 0) := by decide
theorem respects_neg : ¬ Respects gSwap (vec2 1 2) (vec2 3 0) ∧ ¬ Respects gSwap (vec2 1 2) (vec2 2 1) :=
  by decide

/-! ### Consistent runs -/

/-- `f(x) = f(x)` has the constant run. -/
theorem consistentRun_idLoop : ConsistentRunIn Nat idLoop := by
  have hr : RespectsIn gId (fun _ => (0 : Nat)) (fun _ => 0) := by decide
  exact ⟨fun _ => f0, fun _ _ => 0, fun _ => gId, fun _ => ⟨List.mem_singleton_self _, rfl, rfl, hr⟩⟩

/-- `f(x) = f(x)` has the constant run, also in the step-relation form. -/
theorem not_terminates_runStep_idLoop : ¬ Terminates (runStep idLoop) :=
  (consistentRunIn_nat_iff_not_terminates_runStep idLoop).mp consistentRun_idLoop

/-- `f(x) = f(x - 1)` has no infinite consistent run over `Nat`. -/
theorem not_consistentRun_decLoop : ¬ ConsistentRunIn Nat decLoop := by
  rintro ⟨fs, vs, Gs, h⟩
  apply nat_no_infinite_descent (fun n => vs n 0)
  intro n
  obtain ⟨hm, -, -, hr⟩ := h n
  have hG : Gs n = gDec := by simpa [decLoop] using hm
  rw [hG] at hr
  exact respects_gDec_iff.mp hr

theorem stall_consistentRun : ConsistentRunIn Nat stallProg := by
  have hr : Respects gStall (vec2 1 0) (vec2 1 0) := by decide
  exact ⟨fun _ => f0, fun _ => vec2 1 0, fun _ => gStall,
    fun _ => ⟨List.mem_singleton_self _, rfl, rfl, hr⟩⟩

theorem alt_consistentRun : ConsistentRunIn Nat altProg := by
  refine ⟨fun _ => f0, fun n => if n % 2 = 0 then vec2 1 0 else vec2 0 1,
    fun n => if n % 2 = 0 then gX else gY, fun n => ?_⟩
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h' : (n + 1) % 2 = 1 := by omega
    simp only [h, h', ite_true, Nat.one_ne_zero, ite_false]
    decide
  · have h' : (n + 1) % 2 = 0 := by omega
    simp only [h, h', ite_true, Nat.one_ne_zero, ite_false]
    decide

/-! ### Finite runs -/

/-- Every consistent finite run of `f(x) = f(x - 1)` from argument `u 0` has at most `u 0` steps. -/
theorem decLoop_finiteRun_length_le (u : Fin 1 → Nat) (N : Nat)
    (h : FiniteRunFrom decLoop f0 u N) : N ≤ u 0 := by
  obtain ⟨fs, vs, Gs, -, hv0, h⟩ := h
  have key : ∀ n, n ≤ N → vs n 0 + n ≤ u 0 := by
    intro n
    induction n with
    | zero => intro _; rw [hv0]; simp
    | succ n ih =>
      intro hn
      obtain ⟨hm, -, -, hr⟩ := h n (by omega)
      have hG : Gs n = gDec := by simpa [decLoop] using hm
      rw [hG] at hr
      have := respects_gDec_iff.mp hr
      have := ih (by omega)
      omega
  have := key N (Nat.le_refl _)
  omega

theorem finiteRunFrom_pos : FiniteRunFrom decLoop f0 (fun _ => 3) 3 := by
  refine ⟨fun _ => f0, fun n _ => 3 - n, fun _ => gDec, rfl, rfl, fun n hn => ⟨List.mem_singleton_self _, rfl, rfl, ?_⟩⟩
  exact respects_gDec_iff.mpr (by simp; omega)

theorem finiteRunFrom_neg : ¬ FiniteRunFrom decLoop f0 (fun _ => 3) 4 := by
  intro h
  have := decLoop_finiteRun_length_le _ _ h
  simp at this

/-! ### Step relations -/

theorem stepRespects_swapStep : StepRespects swapDec swapStep := by
  rintro s t ⟨h1, h2, h3, h4⟩
  refine ⟨gSwap, by decide, fin_one_eq _ _, fin_one_eq _ _, ?_⟩
  exact respects_gSwap_iff.mpr (by omega)

theorem not_stepRespects_idStep : ¬ StepRespects decLoop idStep := by
  intro h
  obtain ⟨G, hG, -, -, hr⟩ := h (f0, fun _ => 0) (f0, fun _ => 0) rfl
  have hG' : G = gDec := by simpa [decLoop] using hG
  rw [hG'] at hr
  exact Nat.lt_irrefl 0 (respects_gDec_iff.mp hr)

theorem terminates_swapStep : Terminates swapStep := by
  rintro ⟨s, hs⟩
  apply nat_no_infinite_descent (fun n => (s n).2 0 + (s n).2 1)
  intro n
  obtain ⟨-, h2, h3, h4⟩ := hs n
  omega

theorem not_terminates_idStep : ¬ Terminates idStep :=
  fun h => h ⟨fun _ => (f0, fun _ => 0), fun _ => rfl⟩

theorem terminates_countUpStep : Terminates countUpStep := by
  rintro ⟨s, hs⟩
  apply nat_no_infinite_descent (fun n => 100 - (s n).2 0)
  intro n
  obtain ⟨-, h2, h3⟩ := hs n
  omega

/-! ### Call paths and threads -/

theorem isCallPath_pos : IsCallPath swapDec (fun _ => gSwap) :=
  fun _ => ⟨List.mem_singleton_self _, rfl⟩
theorem isCallPath_neg : ¬ IsCallPath swapDec (fun _ => gStall) := fun h => by
  have := (h 0).1; revert this; decide

/-- The thread `x, y, x, y, …` through `gSwap, gSwap, …` alternates a strict arc `x → y'` and a
nonstrict arc `y → x'`; it is infinitely descending. -/
theorem hasInfDescThread_pos : HasInfDescThread (fun _ => gSwap) := by
  refine ⟨0, fun n => ⟨n % 2, Nat.mod_lt _ (by decide)⟩, ?_, ?_⟩
  · intro n _
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      have e1 : (⟨n % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := Fin.ext h
      have e2 : (⟨(n + 1) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 1 := Fin.ext h'
      simp only [e1, e2]
      decide
    · have h' : (n + 1) % 2 = 0 := by omega
      have e1 : (⟨n % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 1 := Fin.ext h
      have e2 : (⟨(n + 1) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := Fin.ext h'
      simp only [e1, e2]
      decide
  · intro N
    refine ⟨2 * N, by omega, Nat.zero_le _, ?_⟩
    have e1 : (⟨2 * N % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := Fin.ext (by simp)
    have e2 : (⟨(2 * N + 1) % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 1 :=
      Fin.ext (by show (2 * N + 1) % 2 = 1; omega)
    simp only [e1, e2]
    decide

/-- `gId, gId, …` has no infinitely descending thread: its only arc is nonstrict. -/
theorem hasInfDescThread_neg : ¬ HasInfDescThread (fun _ => gId) := by
  rintro ⟨n0, p, -, hs⟩
  obtain ⟨n, -, -, hn⟩ := hs 0
  have : ∀ a b : Fin 1, gId.lab a b ≠ Label.strict := by decide
  exact this _ _ hn

theorem sizeChangeTerminating_decLoop : SizeChangeTerminating decLoop := by
  intro Gs hpath
  have hG : ∀ n, Gs n = gDec := fun n => by simpa [decLoop] using (hpath n).1
  refine ⟨0, fun _ => 0, fun n _ => ?_, fun N => ⟨N, Nat.le_refl _, Nat.zero_le _, ?_⟩⟩
  · rw [hG n]; exact (by decide : gDec.lab 0 0 ≠ Label.absent)
  · rw [hG N]; exact (by decide : gDec.lab 0 0 = Label.strict)

theorem not_sizeChangeTerminating_idLoop : ¬ SizeChangeTerminating idLoop := by
  intro h
  exact hasInfDescThread_neg (h (fun _ => gId) (fun _ => ⟨List.mem_singleton_self _, rfl⟩))

/-! ### Lexicographic order and measures -/

theorem lexLt_pos : LexLt (vec2 0 5) (vec2 1 0) ∧ LexLt (vec2 1 0) (vec2 1 1) := by decide
theorem lexLt_neg : ¬ LexLt (vec2 1 0) (vec2 0 5) ∧ ¬ LexLt (vec2 1 1) (vec2 1 1) := by decide

/-- The Ackermann call structure decreases in the lexicographic measure `(x, y)`. -/
theorem lexProjDecreases_ackProg : LexProjDecreases ackProg ackOrd := by
  intro G hG u v hr
  have hG' : G = gX ∨ G = gKeepX := by simpa [ackProg] using hG
  rcases hG' with rfl | rfl
  · have := respects_gX_iff.mp hr
    exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), this⟩
  · have := respects_gKeepX_iff.mp hr
    by_cases h0 : v 0 < u 0
    · exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), h0⟩
    · refine ⟨1, fun i hi => ?_, this.2⟩
      change i.val < 1 at hi
      have : i = 0 := Fin.ext (by show i.val = 0; omega)
      subst this
      show v 0 = u 0
      omega

/-- The single-component measure `x` does not decrease on `f(x, y) = f(y, x - 1)`. -/
theorem lexProjDecreases_neg : ¬ LexProjDecreases swapDec (fun _ (_ : Fin 1) => (0 : Fin 2)) := by
  intro h
  have := h gSwap (by decide) (vec2 1 2) (vec2 2 0) (by decide)
  revert this; decide

/-! ### The checker -/

theorem checkSCT_pos : checkSCT swapDec = true ∧ checkSCT mutProg = true ∧ checkSCT ackProg = true ∧
    checkSCT decLoop = true := by decide
theorem checkSCT_neg : checkSCT idLoop = false ∧ checkSCT altProg = false ∧
    checkSCT stallProg = false := by decide

/-- The fixpoint iteration on `swapDec` stops with the three-graph closure. -/
theorem closureIter_pos :
    closureIter (closureFuel 1 2) (dedupGraphs swapDec.calls) = some [gSwap, gSwap2, gSwap3] := by
  decide
/-- With too little fuel the iteration gives up (and `checkSCT` would reject). -/
theorem closureIter_neg : closureIter 1 (dedupGraphs swapDec.calls) = none := by decide

end Toy.SCT
