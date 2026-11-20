import ToyCT.Examples

/-
Main results, non-vacuity witnesses, positive controls, and canonical tightness
counterexamples for constant-time preservation under compilation.
-/

namespace Toy.CT

/-! ## Functional Correctness Does Not Preserve Constant Time -/

/-- **Counterexample (canonical form).** A transition-deterministic, terminating,
constant-time source selector (`branchlessSelect`) and a functionally equivalent
transition-deterministic, terminating target selector (`branchingSelect`) satisfy
`FunctionallyCorrect` while `branchingSelect` violates `ConstantTime`. -/
theorem functional_correctness_does_not_preserve_ct :
    Deterministic branchlessSelect ∧
    Terminates branchlessSelect ∧
    Deterministic branchingSelect ∧
    Terminates branchingSelect ∧
    ConstantTime branchlessSelect ∧
    FunctionallyCorrect branchlessSelect branchingSelect ∧
    ¬ ConstantTime branchingSelect :=
  ⟨branchlessSelect_deterministic,
   branchlessSelect_terminates,
   branchingSelect_deterministic,
   branchingSelect_terminates,
   branchlessSelect_constantTime,
   branchless_branching_functionallyCorrect,
   branchingSelect_not_constantTime⟩

/-- **Positive control for `functional_correctness_does_not_preserve_ct` and
`secret_dependent_leak_map_breaks_ct`.** Lowering `branchlessSelect` to the
two-instruction straight-line target `branchlessLowered` satisfies `FunctionallyCorrect`
together with `LeakageDetermined` (`selectToLoweredLeakMap`), and preserves `ConstantTime`. -/
theorem branchless_lowering_preserves_ct :
    Deterministic branchlessSelect ∧
    Terminates branchlessSelect ∧
    Deterministic branchlessLowered ∧
    Terminates branchlessLowered ∧
    ConstantTime branchlessSelect ∧
    FunctionallyCorrect branchlessSelect branchlessLowered ∧
    LeakageDetermined branchlessSelect branchlessLowered selectToLoweredLeakMap ∧
    ConstantTime branchlessLowered := by
  refine ⟨branchlessSelect_deterministic,
    branchlessSelect_terminates,
    branchlessLowered_deterministic,
    branchlessLowered_terminates,
    branchlessSelect_constantTime,
    ?_,
    leakageDetermined_pos_example,
    branchlessLowered_constantTime⟩
  intro pub sec out
  constructor
  · rintro ⟨trS, hexS⟩
    have hout := ((branchlessSelect_executes_iff pub sec out trS).mp hexS).1
    exact ⟨[10, 11], (branchlessLowered_executes_iff pub sec out [10, 11]).mpr ⟨hout, rfl⟩⟩
  · rintro ⟨trT, hexT⟩
    have hout := ((branchlessLowered_executes_iff pub sec out trT).mp hexT).1
    exact ⟨[0], (branchlessSelect_executes_iff pub sec out [0]).mpr ⟨hout, rfl⟩⟩

/-! ## Leakage-Determined Compilation Preserves Constant Time -/

/-- If the halting traces of `S` and `T` satisfy `LeakageDetermined S T leakMap` for a
secret-independent trace transformer `leakMap : Pub → List SrcLeak → List TgtLeak`, then
`ConstantTime S` implies `ConstantTime T` without requiring `FunctionallyCorrect`,
`Deterministic`, or `Terminates`. -/
theorem leakage_determined_preserves_ct
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak)
    (leakMap : Pub → List SrcLeak → List TgtLeak)
    (hLD : LeakageDetermined S T leakMap)
    (hCT : ConstantTime S) :
    ConstantTime T := by
  intro pub s₁ s₂ tr
  rw [hLD, hLD]
  constructor
  · rintro ⟨trS, hS, rfl⟩
    exact ⟨trS, (hCT pub s₁ s₂ trS).mp hS, rfl⟩
  · rintro ⟨trS, hS, rfl⟩
    exact ⟨trS, (hCT pub s₁ s₂ trS).mpr hS, rfl⟩

/-- **Non-vacuity witness for `leakage_determined_preserves_ct`.** `branchlessSelect`
lowered to `branchlessLowered` via `selectToLoweredLeakMap` satisfies both hypotheses of
`leakage_determined_preserves_ct`. -/
theorem leakage_determined_preserves_ct_nonvacuous :
    LeakageDetermined branchlessSelect branchlessLowered selectToLoweredLeakMap ∧
    ConstantTime branchlessSelect :=
  ⟨leakageDetermined_pos_example, branchlessSelect_constantTime⟩

/-- **Tightness counterexample for `hCT` in `leakage_determined_preserves_ct`.** Identity
compilation on `branchingSelect` satisfies `LeakageDetermined` while `ConstantTime` fails
for the target when `ConstantTime S` is omitted. -/
theorem leakage_determined_drop_ct_counterexample :
    LeakageDetermined branchingSelect branchingSelect (fun _ tr => tr) ∧
    ¬ ConstantTime branchingSelect := by
  refine ⟨?_, branchingSelect_not_constantTime⟩
  intro pub sec trT
  exact ⟨fun h => ⟨trT, h, rfl⟩, fun ⟨_, h, heq⟩ => heq ▸ h⟩

/-! ## Single-Pair Characterization of `LeakageDetermined` -/

/-- **Characterization of single-pair `LeakageDetermined` existence.** For a single pair
`(S, T)` whose source satisfies `ConstantTime S` and whose target satisfies `TraceUnique T`
(in particular any `Deterministic T`), the existence of *some* secret-independent trace
transformer `leakMap` with `LeakageDetermined S T leakMap` is equivalent to
`ConstantTime T ∧ HaltAgree S T`. Thus `LeakageDetermined` provides proof-engineering
leverage only when `leakMap` is constructed independently of the security proof (such as
`liftStepLeak stepLeak` from a step simulation or a compiler-generated leakage transformer). -/
theorem exists_leakage_determined_iff_of_ct_traceUnique
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak)
    (hCTS : ConstantTime S)
    (hTgtUnique : TraceUnique T) :
    (∃ leakMap, LeakageDetermined S T leakMap) ↔
      (ConstantTime T ∧ HaltAgree S T) := by
  constructor
  · rintro ⟨leakMap, hLD⟩
    exact ⟨leakage_determined_preserves_ct S T leakMap hLD hCTS,
      haltAgree_of_leakageDetermined hLD⟩
  · rintro ⟨hCTT, hHalt⟩
    classical
    -- Choose one halting target trace per public input (from any secret); `ConstantTime T`
    -- makes it a halting trace for every secret on which `T` halts.
    let pick : Pub → List TgtLeak := fun pub =>
      if h : ∃ p : Sec × List TgtLeak, HasTrace T pub p.1 p.2 then (Classical.choose h).2 else []
    have hpick : ∀ pub sec trT, HasTrace T pub sec trT → HasTrace T pub sec (pick pub) := by
      intro pub sec trT hT
      have h : ∃ p : Sec × List TgtLeak, HasTrace T pub p.1 p.2 := ⟨(sec, trT), hT⟩
      have hc := Classical.choose_spec h
      have hp : pick pub = (Classical.choose h).2 := by simp only [pick, h, ↓reduceDIte]
      rw [hp]
      exact (hCTT pub _ sec _).mp hc
    refine ⟨fun pub _ => pick pub, ?_⟩
    intro pub sec trT
    constructor
    · intro hT
      obtain ⟨trS, hS⟩ := (hHalt pub sec).mpr ⟨trT, hT⟩
      exact ⟨trS, hS, hTgtUnique pub sec _ _ hT (hpick pub sec trT hT)⟩
    · rintro ⟨trS, hS, rfl⟩
      obtain ⟨trT', hT'⟩ := (hHalt pub sec).mp ⟨trS, hS⟩
      exact hpick pub sec trT' hT'

/-- **Non-vacuity witness for `exists_leakage_determined_iff_of_ct_traceUnique`.** -/
theorem exists_leakage_determined_iff_of_ct_traceUnique_nonvacuous :
    ConstantTime branchlessSelect ∧
    TraceUnique branchlessLowered :=
  ⟨branchlessSelect_constantTime, branchlessLowered_deterministic.traceUnique⟩

/-- Both sides of `exists_leakage_determined_iff_of_ct_traceUnique` can be false together:
`(branchlessSelect, branchingSelect)` satisfies both hypotheses, admits no secret-independent
`LeakageDetermined` map, and its target is not `ConstantTime`. -/
theorem exists_leakage_determined_iff_of_ct_traceUnique_both_sides_false :
    ConstantTime branchlessSelect ∧ TraceUnique branchingSelect ∧
    ¬ (∃ leakMap, LeakageDetermined branchlessSelect branchingSelect leakMap) ∧
    ¬ (ConstantTime branchingSelect ∧ HaltAgree branchlessSelect branchingSelect) :=
  ⟨branchlessSelect_constantTime, branchingSelect_deterministic.traceUnique,
   fun ⟨f, h⟩ => leakageDetermined_neg_example f h,
   fun ⟨h, _⟩ => branchingSelect_not_constantTime h⟩

/-- Both sides of `exists_leakage_determined_iff_of_ct_traceUnique` hold on the non-vacuity
witness `(branchlessSelect, branchlessLowered)`. -/
theorem exists_leakage_determined_iff_of_ct_traceUnique_both_sides_true :
    (∃ leakMap, LeakageDetermined branchlessSelect branchlessLowered leakMap) ∧
    (ConstantTime branchlessLowered ∧ HaltAgree branchlessSelect branchlessLowered) :=
  ⟨⟨_, leakageDetermined_pos_example⟩, branchlessLowered_constantTime,
   haltAgree_of_terminates branchlessSelect_terminates branchlessLowered_terminates⟩

/-- **Tightness counterexample for `hCTS` in `exists_leakage_determined_iff_of_ct_traceUnique`.**
Dropping `ConstantTime S` on `S = T = abortOnSecret` leaves `TraceUnique T` true and
`∃ leakMap, LeakageDetermined S T leakMap` true (via the identity map), while
`ConstantTime T` fails. -/
theorem exists_ld_iff_drop_src_ct_counterexample :
    TraceUnique abortOnSecret ∧
    ¬ ((∃ leakMap, LeakageDetermined abortOnSecret abortOnSecret leakMap) ↔
        (ConstantTime abortOnSecret ∧ HaltAgree abortOnSecret abortOnSecret)) := by
  refine ⟨abortOnSecret_traceUnique, ?_⟩
  intro hIff
  have hLD : ∃ leakMap, LeakageDetermined abortOnSecret abortOnSecret leakMap :=
    ⟨fun _ tr => tr, fun _ _ tr => ⟨fun h => ⟨tr, h, rfl⟩, fun ⟨_, h, heq⟩ => heq ▸ h⟩⟩
  exact constantTime_abort_neg_example (hIff.mp hLD).1

/-- **Tightness counterexample for `hTgtUnique` in `exists_leakage_determined_iff_of_ct_traceUnique`.**
Dropping `TraceUnique T` on `S = constOneStep` (trace `{[0]}`) and `T = coinFlip` (traces
`{[0], [1]}`) leaves `ConstantTime S` true and `ConstantTime T ∧ HaltAgree S T` true, while
no functional `leakMap` maps the singleton source trace onto both `[0]` and `[1]`. -/
theorem exists_ld_iff_drop_tgt_traceUnique_counterexample :
    ConstantTime constOneStep ∧
    ¬ ((∃ leakMap, LeakageDetermined constOneStep coinFlip leakMap) ↔
        (ConstantTime coinFlip ∧ HaltAgree constOneStep coinFlip)) := by
  refine ⟨constOneStep_constantTime, ?_⟩
  intro hIff
  have hHalt : HaltAgree constOneStep coinFlip := by
    intro _ sec
    exact ⟨fun _ => ⟨[0], (coinFlip_hasTrace_iff () sec [0]).mpr (Or.inl rfl)⟩,
           fun _ => ⟨[0], (constOneStep_hasTrace_iff () sec [0]).mpr rfl⟩⟩
  rcases hIff.mpr ⟨coinFlip_constantTime, hHalt⟩ with ⟨f, hf⟩
  rcases (hf () false [0]).mp ((coinFlip_hasTrace_iff () false [0]).mpr (Or.inl rfl)) with
    ⟨tr₀, hS₀, heq₀⟩
  rcases (hf () false [1]).mp ((coinFlip_hasTrace_iff () false [1]).mpr (Or.inr rfl)) with
    ⟨tr₁, hS₁, heq₁⟩
  have h₀ : tr₀ = [0] := (constOneStep_hasTrace_iff () false tr₀).mp hS₀
  have h₁ : tr₁ = [0] := (constOneStep_hasTrace_iff () false tr₁).mp hS₁
  subst h₀; subst h₁
  rw [← heq₀] at heq₁
  cases heq₁

/-! ## Step-Wise Leakage Simulation on Deterministic Targets Implies `LeakageDetermined` -/

/-- Output-free variant of `StepLeakSim`: source and target may have different output types,
and a related target configuration is only required to halt with *some* output whenever the
source configuration halts. Every `StepLeakSim` is an `OutputFreeStepLeakSim`
(`StepLeakSim.toOutputFree`). -/
structure OutputFreeStepLeakSim {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak)
    (measure : S.State → Nat)
    (R : Pub → Sec → S.State → T.State → Prop) : Prop where
  init_sim : ∀ pub sec s₀, S.init pub sec s₀ → ∃ t₀, T.init pub sec t₀ ∧ R pub sec s₀ t₀
  halted_sim : ∀ pub sec s t out, R pub sec s t → S.halted s out → ∃ out', T.halted t out'
  step_sim : ∀ pub sec s ls s' t, R pub sec s t → S.step s ls s' →
    (∃ t', Steps T t (stepLeak pub ls) t' ∧ R pub sec s' t') ∧
    (stepLeak pub ls = [] → measure s' < measure s)

/-- Forgetting output agreement turns a `StepLeakSim` into an `OutputFreeStepLeakSim`. -/
theorem StepLeakSim.toOutputFree {Pub Sec Out SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec Out SrcLeak} {T : Machine Pub Sec Out TgtLeak}
    {stepLeak : Pub → SrcLeak → List TgtLeak} {measure : S.State → Nat}
    {R : Pub → Sec → S.State → T.State → Prop}
    (h : StepLeakSim S T stepLeak measure R) :
    OutputFreeStepLeakSim S T stepLeak measure R where
  init_sim := h.init_sim
  halted_sim := fun pub sec s t out hR hH => ⟨out, h.halted_sim pub sec s t out hR hH⟩
  step_sim := h.step_sim

/-- Forward stitching: a source run from a related pair is matched by a target run emitting
the lifted trace and ending in a related pair. -/
theorem OutputFreeStepLeakSim.forward {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak} {T : Machine Pub Sec TgtOut TgtLeak}
    {stepLeak : Pub → SrcLeak → List TgtLeak} {measure : S.State → Nat}
    {R : Pub → Sec → S.State → T.State → Prop}
    (hSim : OutputFreeStepLeakSim S T stepLeak measure R) (pub : Pub) (sec : Sec) :
    ∀ {s sf : S.State} {trS : List SrcLeak}, Steps S s trS sf →
      ∀ t, R pub sec s t →
        ∃ t', Steps T t (liftStepLeak stepLeak pub trS) t' ∧ R pub sec sf t' := by
  intro s sf trS h
  induction h with
  | nil s => intro t hR; exact ⟨t, Steps.nil (M := T) t, hR⟩
  | cons hstep _ ih =>
    intro t hR
    obtain ⟨⟨t1, h1, hR1⟩, _⟩ := hSim.step_sim pub sec _ _ _ t hR hstep
    obtain ⟨t', h2, hR'⟩ := ih t1 hR1
    refine ⟨t', ?_, hR'⟩
    rw [liftStepLeak_cons]
    exact Steps.append h1 h2

/-- On a `Deterministic` machine, any run reaching a halted configuration extends every run
prefix from the same start: the halting trace is the prefix's trace followed by a remainder
that the machine emits from the prefix's end state. -/
theorem Deterministic.halting_run_extends {Pub Sec Out Leak : Type}
    {M : Machine Pub Sec Out Leak} (hDet : Deterministic M) :
    ∀ {t t' : M.State} {p : List Leak}, Steps M t p t' →
      ∀ {tr : List Leak} {tf : M.State} {o : Out}, Steps M t tr tf → M.halted tf o →
        ∃ rest, tr = p ++ rest ∧ Steps M t' rest tf := by
  intro t t' p h
  induction h with
  | nil t => intro tr tf o h2 _; exact ⟨tr, rfl, h2⟩
  | cons hstep _ ih =>
    intro tr tf o h2 hH
    cases h2 with
    | nil _ => exact absurd hstep (hDet.halted_nostep _ _ _ _ hH)
    | cons hstep2 hrest2 =>
      obtain ⟨hl, hs⟩ := hDet.step_det _ _ _ _ _ hstep hstep2
      subst hl; subst hs
      obtain ⟨rest, hEq, hR⟩ := ih hrest2 hH
      exact ⟨rest, by rw [hEq]; rfl, hR⟩

/-- Backward direction of the simulation argument: a halting target run from a related pair
`(s, t)` with `s` reachable is the lifted image of a halting source run from `s`. By
induction on the target trace length and, for stuttering source steps, on the measure. -/
theorem OutputFreeStepLeakSim.backward {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak} {T : Machine Pub Sec TgtOut TgtLeak}
    {stepLeak : Pub → SrcLeak → List TgtLeak} {measure : S.State → Nat}
    {R : Pub → Sec → S.State → T.State → Prop}
    (hSim : OutputFreeStepLeakSim S T stepLeak measure R) (hSafe : Safe S)
    (hDet : Deterministic T)
    (pub : Pub) (sec : Sec) {tf : T.State} {o : TgtOut} (hHalt : T.halted tf o) :
    ∀ n (trT : List TgtLeak), trT.length < n → ∀ m (s : S.State) (t : T.State),
      measure s < m → Reachable S pub sec s → R pub sec s t → Steps T t trT tf →
      ∃ trS, (∃ sf out, Steps S s trS sf ∧ S.halted sf out) ∧
        trT = liftStepLeak stepLeak pub trS := by
  intro n
  induction n with
  | zero => intro trT h; exact absurd h (Nat.not_lt_zero _)
  | succ n ihn =>
    intro trT hlen m
    induction m with
    | zero => intro s t h; exact absurd h (Nat.not_lt_zero _)
    | succ m ihm =>
      intro s t hm hReach hR hSteps
      rcases hSafe pub sec s hReach with ⟨out, hH⟩ | ⟨ls, s', hstep⟩
      · obtain ⟨_, hT⟩ := hSim.halted_sim pub sec s t out hR hH
        cases hSteps with
        | nil _ => exact ⟨[], ⟨s, out, Steps.nil (M := S) s, hH⟩, rfl⟩
        | cons hstepT _ => exact absurd hstepT (hDet.halted_nostep _ _ _ _ hT)
      · obtain ⟨⟨t1, h1, hR1⟩, hmeas⟩ := hSim.step_sim pub sec s ls s' t hR hstep
        obtain ⟨rest, hEq, hRest⟩ := hDet.halting_run_extends h1 hSteps hHalt
        have hReach' : Reachable S pub sec s' := by
          obtain ⟨s₀, trp, hi, hp⟩ := hReach
          exact ⟨s₀, trp ++ [ls], hi,
            Steps.append hp (Steps.cons hstep (Steps.nil (M := S) s'))⟩
        by_cases hnil : stepLeak pub ls = []
        · have hlt : measure s' < m := by have := hmeas hnil; omega
          rw [hnil, List.nil_append] at hEq
          rw [← hEq] at hRest
          obtain ⟨trS', ⟨sf, out, hS', hH'⟩, hE⟩ := ihm s' t1 hlt hReach' hR1 hRest
          refine ⟨ls :: trS', ⟨sf, out, Steps.cons hstep hS', hH'⟩, ?_⟩
          rw [liftStepLeak_cons, hnil, List.nil_append]
          exact hE
        · have hne : (stepLeak pub ls).length ≠ 0 :=
            fun h0 => hnil (List.eq_nil_of_length_eq_zero h0)
          have hlenRest : rest.length < n := by
            rw [hEq, List.length_append] at hlen
            omega
          obtain ⟨trS', ⟨sf, out, hS', hH'⟩, hE⟩ :=
            ihn rest hlenRest (measure s' + 1) s' t1 (Nat.lt_succ_self _) hReach' hR1 hRest
          refine ⟨ls :: trS', ⟨sf, out, Steps.cons hstep hS', hH'⟩, ?_⟩
          rw [liftStepLeak_cons, hEq, hE]

/-- Output-free form of `step_leakage_sim_det_target_implies_leakage_determined`: the same
conclusion holds for source and target machines with different output types, under the
weaker `OutputFreeStepLeakSim` (the target only has to halt, with any output, when the related
source configuration halts). -/
theorem outputFree_step_leakage_sim_det_target_implies_leakage_determined
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak)
    (measure : S.State → Nat)
    (R : Pub → Sec → S.State → T.State → Prop)
    (hSim : OutputFreeStepLeakSim S T stepLeak measure R)
    (hSrcInit : HasInit S)
    (hSrcSafe : Safe S)
    (hTgtDet : Deterministic T) :
    LeakageDetermined S T (liftStepLeak stepLeak) := by
  intro pub sec trT
  constructor
  · rintro ⟨o, t₀, tf, hiT, hSteps, hH⟩
    obtain ⟨s₀, hiS⟩ := hSrcInit pub sec
    obtain ⟨t₀', hiT', hR⟩ := hSim.init_sim pub sec s₀ hiS
    have ht : t₀' = t₀ := hTgtDet.init_det pub sec _ _ hiT' hiT
    subst ht
    obtain ⟨trS, ⟨sf, out, hS, hHS⟩, hE⟩ :=
      hSim.backward hSrcSafe hTgtDet pub sec hH (trT.length + 1) trT (Nat.lt_succ_self _)
        (measure s₀ + 1) s₀ t₀' (Nat.lt_succ_self _) ⟨s₀, [], hiS, Steps.nil (M := S) s₀⟩
        hR hSteps
    exact ⟨trS, ⟨out, s₀, sf, hiS, hS, hHS⟩, hE⟩
  · rintro ⟨trS, ⟨out, s₀, sf, hiS, hS, hHS⟩, rfl⟩
    obtain ⟨t₀, hiT, hR⟩ := hSim.init_sim pub sec s₀ hiS
    obtain ⟨t', hT, hR'⟩ := hSim.forward pub sec hS t₀ hR
    obtain ⟨o', hHT⟩ := hSim.halted_sim pub sec sf t' out hR' hHS
    exact ⟨o', t₀, t', hiT, hT, hHT⟩

/-- A step-wise forward leakage simulation `StepLeakSim S T stepLeak measure R` from a
source machine `S` satisfying `HasInit S` and `Safe S` to a transition-deterministic target
machine `Deterministic T` implies `LeakageDetermined S T (liftStepLeak stepLeak)` (exposing
the homomorphic trace transformer `liftStepLeak stepLeak`). -/
theorem step_leakage_sim_det_target_implies_leakage_determined
    {Pub Sec Out SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec Out SrcLeak)
    (T : Machine Pub Sec Out TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak)
    (measure : S.State → Nat)
    (R : Pub → Sec → S.State → T.State → Prop)
    (hSim : StepLeakSim S T stepLeak measure R)
    (hSrcInit : HasInit S)
    (hSrcSafe : Safe S)
    (hTgtDet : Deterministic T) :
    LeakageDetermined S T (liftStepLeak stepLeak) :=
  outputFree_step_leakage_sim_det_target_implies_leakage_determined S T stepLeak measure R
    hSim.toOutputFree hSrcInit hSrcSafe hTgtDet

/-- **Non-vacuity witness for `step_leakage_sim_det_target_implies_leakage_determined`.**
`branchlessWithNop` simulated by `branchlessLowered` under `nopToLoweredStepLeak`
(stuttering on PC `0` with strict measure decrease `1 < 2` and expanding PC `1` into
`[10, 11]`) satisfies every hypothesis. -/
theorem step_leakage_sim_det_target_implies_leakage_determined_nonvacuous :
    StepLeakSim branchlessWithNop branchlessLowered
      nopToLoweredStepLeak nopSelectMeasure nopToLoweredRel ∧
    HasInit branchlessWithNop ∧
    Safe branchlessWithNop ∧
    Deterministic branchlessLowered := by
  have hInitSafe := hasInit_and_safe_of_det_terminates
    branchlessWithNop_deterministic branchlessWithNop_terminates
  exact ⟨stepLeakSim_pos_example, hInitSafe.1, hInitSafe.2, branchlessLowered_deterministic⟩

/-- **Tightness counterexample for `hSim` in `step_leakage_sim_det_target_implies_leakage_determined`.**
Without `StepLeakSim`, `HasInit branchlessSelect`, `Safe branchlessSelect`,
`ConstantTime branchlessSelect`, and `Deterministic branchingSelect` all hold while both
`LeakageDetermined` and `ConstantTime branchingSelect` fail. -/
theorem step_sim_drop_sim_counterexample :
    HasInit branchlessSelect ∧
    Safe branchlessSelect ∧
    ConstantTime branchlessSelect ∧
    Deterministic branchingSelect ∧
    ¬ LeakageDetermined branchlessSelect branchingSelect (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime branchingSelect := by
  have hInitSafe := hasInit_and_safe_of_det_terminates
    branchlessSelect_deterministic branchlessSelect_terminates
  exact ⟨hInitSafe.1, hInitSafe.2, branchlessSelect_constantTime,
    branchingSelect_deterministic,
    leakageDetermined_neg_example (liftStepLeak (fun _ l => [l])),
    branchingSelect_not_constantTime⟩

/-- **Tightness counterexample for `hSrcInit` in `step_leakage_sim_det_target_implies_leakage_determined`.**
When `HasInit S` is dropped (`emptyInitMachine` simulated by `haltIfTrue`), `StepLeakSim`,
`Safe S`, `ConstantTime S`, and `Deterministic T` all hold while both `LeakageDetermined`
and `ConstantTime T` fail. -/
theorem step_sim_drop_src_init_counterexample :
    StepLeakSim emptyInitMachine haltIfTrue
      (fun _ l => [l]) (fun _ => 0) (fun _ _ _ _ => False) ∧
    Safe emptyInitMachine ∧
    ConstantTime emptyInitMachine ∧
    Deterministic haltIfTrue ∧
    ¬ LeakageDetermined emptyInitMachine haltIfTrue (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime haltIfTrue := by
  refine ⟨?_, ?_, ?_, haltIfTrue_deterministic, ?_, haltIfTrue_not_constantTime⟩
  · exact {
      init_sim := fun _ _ _ h => False.elim h
      halted_sim := fun _ _ _ _ _ hR _ => False.elim hR
      step_sim := fun _ _ _ _ _ _ hR _ => False.elim hR
    }
  · intro _ _ _ ⟨_, _, hInit, _⟩
    exact False.elim hInit
  · intro _ _ _ _
    exact ⟨fun ⟨_, _, _, hInit, _, _⟩ => False.elim hInit,
           fun ⟨_, _, _, hInit, _, _⟩ => False.elim hInit⟩
  · intro hLD
    have hT : HasTrace haltIfTrue () true [] := (haltIfTrue_hasTrace_iff true []).mpr ⟨rfl, rfl⟩
    rcases (hLD () true []).mp hT with ⟨_, ⟨_, _, _, hInitS, _, _⟩, _⟩
    exact hInitS

/-- **Tightness counterexample for `hSrcSafe` in `step_leakage_sim_det_target_implies_leakage_determined`.**
When `Safe S` is dropped (`stuckMachine` simulated by `haltIfTrue`), `StepLeakSim`,
`HasInit S`, `ConstantTime S`, and `Deterministic T` all hold while both
`LeakageDetermined` and `ConstantTime T` fail. -/
theorem step_sim_drop_src_safe_counterexample :
    StepLeakSim stuckMachine haltIfTrue
      (fun _ l => [l]) (fun _ => 0) (fun _ _ _ _ => True) ∧
    HasInit stuckMachine ∧
    ConstantTime stuckMachine ∧
    Deterministic haltIfTrue ∧
    ¬ LeakageDetermined stuckMachine haltIfTrue (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime haltIfTrue := by
  refine ⟨?_, fun _ _ => ⟨(), rfl⟩, ?_, haltIfTrue_deterministic, ?_, haltIfTrue_not_constantTime⟩
  · exact {
      init_sim := fun _ sec _ _ => ⟨sec, rfl, trivial⟩
      halted_sim := fun _ _ _ _ _ _ hHalt => False.elim hHalt
      step_sim := fun _ _ _ _ _ _ _ hStep => False.elim hStep
    }
  · intro _ _ _ _
    exact ⟨fun ⟨_, _, _, _, _, hHalt⟩ => False.elim hHalt,
           fun ⟨_, _, _, _, _, hHalt⟩ => False.elim hHalt⟩
  · intro hLD
    have hT : HasTrace haltIfTrue () true [] := (haltIfTrue_hasTrace_iff true []).mpr ⟨rfl, rfl⟩
    rcases (hLD () true []).mp hT with ⟨_, ⟨_, _, _, _, _, hHaltS⟩, _⟩
    exact hHaltS

/-- **Tightness counterexample for the stuttering measure in `StepLeakSim`.**
Dropping the strict decrease `measure s' < measure s` on silent/eliminated source steps
(`UnmeasuredStepLeakSim`) allows `silentLoopSource` (`HasInit`, `Safe`, `Deterministic`,
and `ConstantTime`) to be forward-simulated by deterministic `haltIfTrue`, breaking both
`LeakageDetermined` and `ConstantTime` preservation. -/
theorem unmeasured_stutter_sim_breaks_leakage_determined :
    UnmeasuredStepLeakSim silentLoopSource haltIfTrue
      (fun _ _ => []) (fun _ _ _ _ => True) ∧
    HasInit silentLoopSource ∧
    Safe silentLoopSource ∧
    Deterministic silentLoopSource ∧
    ConstantTime silentLoopSource ∧
    Deterministic haltIfTrue ∧
    ¬ LeakageDetermined silentLoopSource haltIfTrue (liftStepLeak (fun _ _ => [])) ∧
    ¬ ConstantTime haltIfTrue := by
  refine ⟨?_,
    fun _ _ => ⟨(), rfl⟩,
    safe_nonterminating_pos_example,
    silentLoopSource_deterministic,
    ?_,
    haltIfTrue_deterministic,
    ?_,
    haltIfTrue_not_constantTime⟩
  · exact {
      init_sim := fun _ sec _ _ => ⟨sec, rfl, trivial⟩
      halted_sim := fun _ _ _ _ _ _ hHalt => False.elim hHalt
      step_sim := fun _ _ _ _ _ t _ _ => ⟨t, Steps.nil (M := haltIfTrue) t, trivial⟩
    }
  · intro _ _ _ _
    exact ⟨fun ⟨_, _, _, _, _, hHalt⟩ => False.elim hHalt,
           fun ⟨_, _, _, _, _, hHalt⟩ => False.elim hHalt⟩
  · intro hLD
    have hT : HasTrace haltIfTrue () true [] := (haltIfTrue_hasTrace_iff true []).mpr ⟨rfl, rfl⟩
    rcases (hLD () true []).mp hT with ⟨_, ⟨_, _, _, _, _, hHaltS⟩, _⟩
    exact hHaltS

/-- **Counterexample for single-run state-dependent stuttering (`OptionStepLeakSim`).**
When a single-run forward simulation permits choosing from internal state `(s, t)` (without
a relational 2-simulation invariant across secret pairs) whether a source step emits
`stepLeak pub ls` or stutters with `measure s' < measure s`, `twoStepConstSource`
(deterministic, terminating, safe, and `ConstantTime`) simulates deterministic
`secretStutterTarget`, breaking both `LeakageDetermined` and `ConstantTime`. -/
theorem option_stutter_sim_breaks_ct :
    OptionStepLeakSim twoStepConstSource secretStutterTarget
      (fun _ l => [l]) twoStepMeasure optionStutterRel ∧
    HasInit twoStepConstSource ∧
    Safe twoStepConstSource ∧
    Deterministic twoStepConstSource ∧
    Terminates twoStepConstSource ∧
    ConstantTime twoStepConstSource ∧
    Deterministic secretStutterTarget ∧
    (∀ f, ¬ LeakageDetermined twoStepConstSource secretStutterTarget f) ∧
    ¬ ConstantTime secretStutterTarget := by
  have hInitSafe := hasInit_and_safe_of_det_terminates
    twoStepConstSource_deterministic twoStepConstSource_terminates
  refine ⟨optionStepLeakSim_pos_example, hInitSafe.1, hInitSafe.2,
    twoStepConstSource_deterministic, twoStepConstSource_terminates,
    twoStepConstSource_constantTime, secretStutterTarget_deterministic, ?_,
    secretStutterTarget_not_constantTime⟩
  intro f hLD
  have hT : HasTrace secretStutterTarget () true [0] :=
    (secretStutterTarget_hasTrace_iff () true [0]).mpr rfl
  have hF : HasTrace secretStutterTarget () false [0, 0] :=
    (secretStutterTarget_hasTrace_iff () false [0, 0]).mpr rfl
  rcases (hLD () true [0]).mp hT with ⟨tr₁, hS₁, heq₁⟩
  rcases (hLD () false [0, 0]).mp hF with ⟨tr₂, hS₂, heq₂⟩
  have h₁ : tr₁ = [0, 0] := (twoStepConstSource_hasTrace_iff () true tr₁).mp hS₁
  have h₂ : tr₂ = [0, 0] := (twoStepConstSource_hasTrace_iff () false tr₂).mp hS₂
  subst h₁; subst h₂
  rw [← heq₁] at heq₂
  cases heq₂

/-- **Per-clause tightness of `Deterministic.init_det` in
`step_leakage_sim_det_target_implies_leakage_determined`.** Dropping only `init_det` on
`secretTwoInitTarget` (while preserving `step_det` and `halted_nostep`) breaks both
`LeakageDetermined` and `ConstantTime`. -/
theorem step_sim_drop_tgt_init_det_counterexample :
    StepLeakSim constOneStep secretTwoInitTarget (fun _ l => [l]) (fun _ => 0)
      (fun _ _ s t => (s = false ∧ t = TwoInitState.a) ∨ (s = true ∧ t = TwoInitState.fin)) ∧
    HasInit constOneStep ∧
    Safe constOneStep ∧
    ConstantTime constOneStep ∧
    (∀ s l₁ s₁ l₂ s₂, secretTwoInitTarget.step s l₁ s₁ → secretTwoInitTarget.step s l₂ s₂ →
      l₁ = l₂ ∧ s₁ = s₂) ∧
    (∀ s out l s', secretTwoInitTarget.halted s out → ¬ secretTwoInitTarget.step s l s') ∧
    ¬ (∀ pub sec s₁ s₂, secretTwoInitTarget.init pub sec s₁ →
        secretTwoInitTarget.init pub sec s₂ → s₁ = s₂) ∧
    ¬ LeakageDetermined constOneStep secretTwoInitTarget (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime secretTwoInitTarget := by
  have hIS := hasInit_and_safe_of_det_terminates constOneStep_deterministic constOneStep_terminates
  refine ⟨?_, hIS.1, hIS.2, constOneStep_constantTime, ?_, ?_, ?_, ?_, ?_⟩
  · refine { init_sim := ?_, halted_sim := ?_, step_sim := ?_ }
    · intro _ _ s₀ hs₀
      exact ⟨TwoInitState.a, Or.inl rfl, Or.inl ⟨hs₀, rfl⟩⟩
    · intro _ _ s t out hR hHalt
      rcases hHalt with ⟨rfl, rfl⟩
      rcases hR with ⟨h, _⟩ | ⟨_, ht⟩
      · cases h
      · exact ⟨ht, rfl⟩
    · intro _ _ s ls s' t hR hStep
      rcases hStep with ⟨rfl, rfl, rfl⟩
      rcases hR with ⟨_, ht⟩ | ⟨h, _⟩
      · subst ht
        exact ⟨⟨TwoInitState.fin, Steps.cons (M := secretTwoInitTarget) ⟨rfl, rfl⟩
          (Steps.nil (M := secretTwoInitTarget) _), Or.inr ⟨rfl, rfl⟩⟩, fun h => by cases h⟩
      · cases h
  · intro s l₁ s₁ l₂ s₂ h₁ h₂
    cases s with
    | a => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | b => exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
    | fin => exact False.elim h₁
  · intro s out l s' hHalt hStep
    rw [hHalt.1] at hStep
    exact hStep
  · intro h
    have heq := h () true TwoInitState.a TwoInitState.b (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩)
    cases heq
  · intro hLD
    have hT : HasTrace secretTwoInitTarget () true [1] :=
      ⟨(), TwoInitState.b, TwoInitState.fin, Or.inr ⟨rfl, rfl⟩,
        Steps.cons (M := secretTwoInitTarget) ⟨rfl, rfl⟩
          (Steps.nil (M := secretTwoInitTarget) _), ⟨rfl, rfl⟩⟩
    rcases (hLD () true [1]).mp hT with ⟨trS, hS, heq⟩
    have htr : trS = [0] := (constOneStep_hasTrace_iff () true trS).mp hS
    subst htr
    cases heq
  · intro hCT
    have hT : HasTrace secretTwoInitTarget () true [1] :=
      ⟨(), TwoInitState.b, TwoInitState.fin, Or.inr ⟨rfl, rfl⟩,
        Steps.cons (M := secretTwoInitTarget) ⟨rfl, rfl⟩
          (Steps.nil (M := secretTwoInitTarget) _), ⟨rfl, rfl⟩⟩
    rcases (hCT () true false [1]).mp hT with ⟨_, s₀, sf, hs₀, hSteps, _⟩
    rcases hs₀ with rfl | ⟨hf, _⟩
    · rcases (Steps.cons_iff (M := secretTwoInitTarget)).mp hSteps with ⟨_, ⟨hl, _⟩, _⟩
      cases hl
    · cases hf

/-- **Per-clause tightness of successor-state uniqueness in `Deterministic.step_det` for
`step_leakage_sim_det_target_implies_leakage_determined`.** Dropping only `s₁ = s₂` inside
`step_det` on `secretForkTarget` (while preserving `init_det`, step-leakage uniqueness
`l₁ = l₂`, and `halted_nostep`) breaks both `LeakageDetermined` and `ConstantTime`. -/
theorem step_sim_drop_tgt_step_state_det_counterexample :
    StepLeakSim constOneStep secretForkTarget (fun _ l => [l]) (fun _ => 0)
      (fun _ sec s t =>
        (s = false ∧ t = SecretForkState.start sec) ∨ (s = true ∧ t = SecretForkState.a)) ∧
    HasInit constOneStep ∧
    Safe constOneStep ∧
    ConstantTime constOneStep ∧
    (∀ pub sec s₁ s₂, secretForkTarget.init pub sec s₁ →
      secretForkTarget.init pub sec s₂ → s₁ = s₂) ∧
    (∀ s l₁ s₁ l₂ s₂, secretForkTarget.step s l₁ s₁ →
      secretForkTarget.step s l₂ s₂ → l₁ = l₂) ∧
    (∀ s out l s', secretForkTarget.halted s out → ¬ secretForkTarget.step s l s') ∧
    ¬ (∀ s l₁ s₁ l₂ s₂, secretForkTarget.step s l₁ s₁ →
        secretForkTarget.step s l₂ s₂ → s₁ = s₂) ∧
    ¬ LeakageDetermined constOneStep secretForkTarget (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime secretForkTarget := by
  have hIS := hasInit_and_safe_of_det_terminates constOneStep_deterministic constOneStep_terminates
  refine ⟨?_, hIS.1, hIS.2, constOneStep_constantTime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine { init_sim := ?_, halted_sim := ?_, step_sim := ?_ }
    · intro _ sec s₀ hs₀
      exact ⟨SecretForkState.start sec, rfl, Or.inl ⟨hs₀, rfl⟩⟩
    · intro _ _ s t out hR hHalt
      rcases hHalt with ⟨rfl, rfl⟩
      rcases hR with ⟨h, _⟩ | ⟨_, ht⟩
      · cases h
      · exact ⟨Or.inl ht, rfl⟩
    · intro _ sec s ls s' t hR hStep
      rcases hStep with ⟨rfl, rfl, rfl⟩
      rcases hR with ⟨_, ht⟩ | ⟨h, _⟩
      · subst ht
        exact ⟨⟨SecretForkState.a, Steps.cons (M := secretForkTarget) ⟨rfl, Or.inl rfl⟩
          (Steps.nil (M := secretForkTarget) _), Or.inr ⟨rfl, rfl⟩⟩, fun h => by cases h⟩
      · cases h
  · intro _ _ _ _ h₁ h₂
    exact h₁.trans h₂.symm
  · intro s l₁ s₁ l₂ s₂ h₁ h₂
    cases s with
    | start _ => exact h₁.1.trans h₂.1.symm
    | a => exact False.elim h₁
    | b => exact h₁.1.trans h₂.1.symm
    | fin => exact False.elim h₁
  · intro s out l s' hHalt hStep
    rcases hHalt.1 with rfl | rfl <;> exact hStep
  · intro h
    have heq := h (SecretForkState.start true) 0 SecretForkState.a 0 SecretForkState.b
      ⟨rfl, Or.inl rfl⟩ ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
    cases heq
  · intro hLD
    have hT : HasTrace secretForkTarget () true [0, 1] :=
      ⟨(), .start true, .fin, rfl,
        Steps.cons (M := secretForkTarget) ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
          (Steps.cons (M := secretForkTarget) ⟨rfl, rfl⟩
            (Steps.nil (M := secretForkTarget) _)), ⟨Or.inr rfl, rfl⟩⟩
    rcases (hLD () true [0, 1]).mp hT with ⟨trS, hS, heq⟩
    have htr : trS = [0] := (constOneStep_hasTrace_iff () true trS).mp hS
    subst htr
    cases heq
  · intro hCT
    have hT : HasTrace secretForkTarget () true [0, 1] :=
      ⟨(), .start true, .fin, rfl,
        Steps.cons (M := secretForkTarget) ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
          (Steps.cons (M := secretForkTarget) ⟨rfl, rfl⟩
            (Steps.nil (M := secretForkTarget) _)), ⟨Or.inr rfl, rfl⟩⟩
    rcases (hCT () true false [0, 1]).mp hT with ⟨_, s₀, sf, hs₀, hSteps, _⟩
    subst hs₀
    rcases (Steps.cons_iff (M := secretForkTarget)).mp hSteps with ⟨s₁, ⟨_, hs₁⟩, hrest⟩
    rcases hs₁ with rfl | ⟨hf, _⟩
    · rcases (Steps.cons_iff (M := secretForkTarget)).mp hrest with ⟨_, hstep₂, _⟩
      exact hstep₂
    · cases hf

/-- **Per-clause tightness of `Deterministic.halted_nostep` in
`step_leakage_sim_det_target_implies_leakage_determined`.** Dropping only `halted_nostep`
on `secretHaltOrStepTarget` (while preserving `init_det` and `step_det`) breaks both
`LeakageDetermined` and `ConstantTime`. -/
theorem step_sim_drop_tgt_halted_nostep_counterexample :
    StepLeakSim trivialHaltedMachine secretHaltOrStepTarget (fun _ l => [l]) (fun _ => 0)
      (fun _ sec _ t => t = (false, sec)) ∧
    HasInit trivialHaltedMachine ∧
    Safe trivialHaltedMachine ∧
    ConstantTime trivialHaltedMachine ∧
    (∀ pub sec s₁ s₂, secretHaltOrStepTarget.init pub sec s₁ →
      secretHaltOrStepTarget.init pub sec s₂ → s₁ = s₂) ∧
    (∀ s l₁ s₁ l₂ s₂, secretHaltOrStepTarget.step s l₁ s₁ →
      secretHaltOrStepTarget.step s l₂ s₂ → l₁ = l₂ ∧ s₁ = s₂) ∧
    ¬ (∀ s out l s', secretHaltOrStepTarget.halted s out →
        ¬ secretHaltOrStepTarget.step s l s') ∧
    ¬ LeakageDetermined trivialHaltedMachine secretHaltOrStepTarget
        (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime secretHaltOrStepTarget := by
  refine ⟨?_, fun _ _ => ⟨(), rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact {
      init_sim := fun _ sec _ _ => ⟨(false, sec), rfl, rfl⟩
      halted_sim := fun _ _ _ _ _ _ hHalt => hHalt.2
      step_sim := fun _ _ _ _ _ _ _ hStep => False.elim hStep
    }
  · intro _ _ _ _
    exact Or.inl ⟨(), rfl, rfl⟩
  · intro pub s₁ s₂ tr
    rw [trivialHaltedMachine_hasTrace_iff, trivialHaltedMachine_hasTrace_iff]
  · intro _ _ _ _ h₁ h₂
    exact h₁.trans h₂.symm
  · intro _ _ _ _ _ h₁ h₂
    exact ⟨h₁.2.2.1.trans h₂.2.2.1.symm, h₁.2.2.2.trans h₂.2.2.2.symm⟩
  · intro h
    exact h (false, true) () 1 (true, true) rfl ⟨rfl, rfl, rfl, rfl⟩
  · intro hLD
    have hT : HasTrace secretHaltOrStepTarget () true [1] :=
      ⟨(), (false, true), (true, true), rfl,
        Steps.cons (M := secretHaltOrStepTarget) ⟨rfl, rfl, rfl, rfl⟩
          (Steps.nil (M := secretHaltOrStepTarget) _), rfl⟩
    rcases (hLD () true [1]).mp hT with ⟨trS, hS, heq⟩
    have htr : trS = [] := (trivialHaltedMachine_hasTrace_iff () true trS).mp hS
    subst htr
    cases heq
  · intro hCT
    have hT : HasTrace secretHaltOrStepTarget () true [1] :=
      ⟨(), (false, true), (true, true), rfl,
        Steps.cons (M := secretHaltOrStepTarget) ⟨rfl, rfl, rfl, rfl⟩
          (Steps.nil (M := secretHaltOrStepTarget) _), rfl⟩
    rcases (hCT () true false [1]).mp hT with ⟨_, s₀, _, hs₀, hSteps, _⟩
    subst hs₀
    rcases (Steps.cons_iff (M := secretHaltOrStepTarget)).mp hSteps with ⟨_, ⟨_, hf, _⟩, _⟩
    cases hf

/-! ## Tightness — Dropping Secret-Independence of the Leakage Function -/

/-- **Tightness counterexample for `hLD` in `leakage_determined_preserves_ct`.**
Permitting the trace leakage transformer to inspect `Sec` (`SecretDependentLeakageDetermined`)
vacates the condition on any deterministic terminating pair (see
`exists_secretDependentLeakageDetermined_of_det_terminates`): in particular,
`branchlessSelect` and `branchingSelect` satisfy `SecretDependentLeakageDetermined` under
`secretBranchLeakMap` together with `FunctionallyCorrect`, while no secret-independent
`f` satisfies `LeakageDetermined` and `branchingSelect` violates `ConstantTime`. -/
theorem secret_dependent_leak_map_breaks_ct :
    Deterministic branchlessSelect ∧
    Terminates branchlessSelect ∧
    Deterministic branchingSelect ∧
    Terminates branchingSelect ∧
    ConstantTime branchlessSelect ∧
    FunctionallyCorrect branchlessSelect branchingSelect ∧
    SecretDependentLeakageDetermined branchlessSelect branchingSelect secretBranchLeakMap ∧
    (∀ f, ¬ LeakageDetermined branchlessSelect branchingSelect f) ∧
    ¬ ConstantTime branchingSelect :=
  ⟨branchlessSelect_deterministic,
   branchlessSelect_terminates,
   branchingSelect_deterministic,
   branchingSelect_terminates,
   branchlessSelect_constantTime,
   branchless_branching_functionallyCorrect,
   secretDependentLeakageDetermined_pos_example,
   leakageDetermined_neg_example,
   branchingSelect_not_constantTime⟩

/-! ## Tightness — Dropping Determinism of the Target Machine -/

/-- Simulation relation matching `constOneStep` to `nondetSecretBranchTarget` (and to its
determinized counterpart `determinizedSecretBranchTarget`). -/
def constNondetRel (_pub : Unit) (sec : Bool) (s : Bool) (t : NondetTargetState) : Prop :=
  if s then t = .done else t = .start sec

/-- **Tightness counterexample for `hTgtDet` in
`step_leakage_sim_det_target_implies_leakage_determined` (canonical form).**
When `Deterministic T` fails (`¬ Deterministic nondetSecretBranchTarget`), `constOneStep`
(deterministic, terminating, safe, and constant-time) admits a secret-independent lockstep
simulation `StepLeakSim` to `nondetSecretBranchTarget` (which also terminates and satisfies
`FunctionallyCorrect`), yet both `LeakageDetermined` and `ConstantTime` fail on the target
because `sec = true` admits an unsimulated transition emitting `[1]`. -/
theorem nondeterministic_target_sim_breaks_leakage_determined :
    StepLeakSim constOneStep nondetSecretBranchTarget
      (fun _ l => [l]) (fun _ => 0) constNondetRel ∧
    HasInit constOneStep ∧
    Safe constOneStep ∧
    Deterministic constOneStep ∧
    Terminates constOneStep ∧
    Terminates nondetSecretBranchTarget ∧
    ¬ Deterministic nondetSecretBranchTarget ∧
    ConstantTime constOneStep ∧
    FunctionallyCorrect constOneStep nondetSecretBranchTarget ∧
    ¬ LeakageDetermined constOneStep nondetSecretBranchTarget
        (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime nondetSecretBranchTarget := by
  have hInitSafe := hasInit_and_safe_of_det_terminates
    constOneStep_deterministic constOneStep_terminates
  refine ⟨?_, hInitSafe.1, hInitSafe.2, constOneStep_deterministic,
    constOneStep_terminates, nondetSecretBranchTarget_terminates,
    deterministic_neg_example,
    constOneStep_constantTime, ?_, ?_, ?_⟩
  · refine {
      init_sim := ?_
      halted_sim := ?_
      step_sim := ?_
    }
    · intro _ sec s₀ hs₀
      subst hs₀
      exact ⟨NondetTargetState.start sec, rfl, rfl⟩
    · intro _ _ s t out hR hHalt
      rcases hHalt with ⟨rfl, rfl⟩
      exact ⟨hR, rfl⟩
    · intro _ sec s ls s' t hR hStep
      rcases hStep with ⟨rfl, rfl, rfl⟩
      have ht : t = NondetTargetState.start sec := hR
      subst ht
      refine ⟨⟨NondetTargetState.done, ?_, rfl⟩, fun hNil => by cases hNil⟩
      cases sec with
      | false =>
        exact Steps.cons (M := nondetSecretBranchTarget) ⟨rfl, rfl⟩
          (Steps.nil (M := nondetSecretBranchTarget) NondetTargetState.done)
      | true =>
        exact Steps.cons (M := nondetSecretBranchTarget) ⟨Or.inl rfl, rfl⟩
          (Steps.nil (M := nondetSecretBranchTarget) NondetTargetState.done)
  · intro _ sec out
    constructor
    · rintro ⟨trS, hexS⟩
      have hout := ((constOneStep_executes_iff () sec out trS).mp hexS).1
      subst hout
      cases sec with
      | false =>
        exact ⟨[0], NondetTargetState.start false, NondetTargetState.done, rfl,
          Steps.cons (M := nondetSecretBranchTarget) ⟨rfl, rfl⟩
            (Steps.nil (M := nondetSecretBranchTarget) NondetTargetState.done), ⟨rfl, rfl⟩⟩
      | true =>
        exact ⟨[0], NondetTargetState.start true, NondetTargetState.done, rfl,
          Steps.cons (M := nondetSecretBranchTarget) ⟨Or.inl rfl, rfl⟩
            (Steps.nil (M := nondetSecretBranchTarget) NondetTargetState.done), ⟨rfl, rfl⟩⟩
    · rintro ⟨trT, _, _, _, _, _, hout⟩
      subst hout
      exact ⟨[0], (constOneStep_executes_iff () sec () [0]).mpr ⟨rfl, rfl⟩⟩
  · intro hLD
    have hLeaked : HasTrace nondetSecretBranchTarget () true [1] :=
      ⟨(), NondetTargetState.start true, NondetTargetState.done, rfl,
        Steps.cons (M := nondetSecretBranchTarget) ⟨Or.inr rfl, rfl⟩
          (Steps.nil (M := nondetSecretBranchTarget) NondetTargetState.done), ⟨rfl, rfl⟩⟩
    rcases (hLD () true [1]).mp hLeaked with ⟨trS, hS, heq⟩
    have htrS : trS = [0] := (constOneStep_hasTrace_iff () true trS).mp hS
    subst htrS
    cases heq
  · intro hCT
    have hTrue1 : HasTrace nondetSecretBranchTarget () true [1] :=
      ⟨(), NondetTargetState.start true, NondetTargetState.done, rfl,
        Steps.cons (M := nondetSecretBranchTarget) ⟨Or.inr rfl, rfl⟩
          (Steps.nil (M := nondetSecretBranchTarget) NondetTargetState.done), ⟨rfl, rfl⟩⟩
    rcases (hCT () true false [1]).mp hTrue1 with ⟨_, s₀, _, hs₀, hSteps, _⟩
    subst hs₀
    rcases (Steps.cons_iff (M := nondetSecretBranchTarget)).mp hSteps with ⟨_, ⟨hl, _⟩, _⟩
    cases hl

/-- **Positive control for `nondeterministic_target_sim_breaks_leakage_determined`.**
Removing the extra `l = 1` branch on `.start true` yields `determinizedSecretBranchTarget`
over the same `NondetTargetState` state space, restoring `Deterministic`, `StepLeakSim`
under the exact same relation `constNondetRel`, `LeakageDetermined`, and `ConstantTime`. -/
theorem determinized_target_sim_positive_control :
    StepLeakSim constOneStep determinizedSecretBranchTarget
      (fun _ l => [l]) (fun _ => 0) constNondetRel ∧
    HasInit constOneStep ∧
    Safe constOneStep ∧
    Deterministic determinizedSecretBranchTarget ∧
    LeakageDetermined constOneStep determinizedSecretBranchTarget (liftStepLeak (fun _ l => [l])) ∧
    ConstantTime determinizedSecretBranchTarget := by
  have hInitSafe := hasInit_and_safe_of_det_terminates
    constOneStep_deterministic constOneStep_terminates
  refine ⟨?_, hInitSafe.1, hInitSafe.2, determinizedSecretBranchTarget_deterministic,
    ?_, determinizedSecretBranchTarget_constantTime⟩
  · refine {
      init_sim := fun _ sec s₀ hs₀ => ?_
      halted_sim := fun _ _ s t out hR hHalt => ?_
      step_sim := fun _ sec s ls s' t hR hStep => ?_
    }
    · subst hs₀
      exact ⟨NondetTargetState.start sec, rfl, rfl⟩
    · rcases hHalt with ⟨rfl, rfl⟩
      exact ⟨hR, rfl⟩
    · rcases hStep with ⟨rfl, rfl, rfl⟩
      have ht : t = NondetTargetState.start sec := hR
      subst ht
      exact ⟨⟨NondetTargetState.done,
        Steps.cons (M := determinizedSecretBranchTarget) ⟨rfl, rfl⟩
          (Steps.nil (M := determinizedSecretBranchTarget) .done), rfl⟩,
        fun hNil => by cases hNil⟩
  · intro pub sec trT
    rw [determinizedSecretBranchTarget_hasTrace_iff]
    constructor
    · rintro rfl
      exact ⟨[0], (constOneStep_hasTrace_iff pub sec [0]).mpr rfl, rfl⟩
    · rintro ⟨trS, hS, rfl⟩
      have htrS : trS = [0] := (constOneStep_hasTrace_iff pub sec trS).mp hS
      subst htrS
      rfl

/-! ## Composition of `LeakageDetermined` Relations -/

/-- Vertical composition of `LeakageDetermined` relations (reference point): if `M₂` is
`LeakageDetermined` from `M₁` via `f` and `M₃` is `LeakageDetermined` from `M₂` via `g`,
then `M₃` is `LeakageDetermined` from `M₁` via `composeLeakMap f g`. -/
theorem leakage_determined_comp
    {Pub Sec Out₁ Out₂ Out₃ Leak₁ Leak₂ Leak₃ : Type}
    (M₁ : Machine Pub Sec Out₁ Leak₁)
    (M₂ : Machine Pub Sec Out₂ Leak₂)
    (M₃ : Machine Pub Sec Out₃ Leak₃)
    (f : Pub → List Leak₁ → List Leak₂)
    (g : Pub → List Leak₂ → List Leak₃)
    (h₁₂ : LeakageDetermined M₁ M₂ f)
    (h₂₃ : LeakageDetermined M₂ M₃ g) :
    LeakageDetermined M₁ M₃ (composeLeakMap f g) := by
  intro pub sec tr₃
  rw [h₂₃]
  constructor
  · rintro ⟨tr₂, h₂, rfl⟩
    obtain ⟨tr₁, h₁, rfl⟩ := (h₁₂ pub sec tr₂).mp h₂
    exact ⟨tr₁, h₁, rfl⟩
  · rintro ⟨tr₁, h₁, rfl⟩
    exact ⟨f pub tr₁, (h₁₂ pub sec _).mpr ⟨tr₁, h₁, rfl⟩, rfl⟩

/-- **Non-vacuity witness for `leakage_determined_comp`.** The two-pass pipeline
`branchlessSelect` -> `branchlessLowered` -> `branchlessEncoded` satisfies both hypotheses
of `leakage_determined_comp` with public-input-dependent second-pass transformer
`loweredToEncodedLeakMap`. -/
theorem leakage_determined_comp_nonvacuous :
    LeakageDetermined branchlessSelect branchlessLowered selectToLoweredLeakMap ∧
    LeakageDetermined branchlessLowered branchlessEncoded loweredToEncodedLeakMap := by
  refine ⟨leakageDetermined_pos_example, ?_⟩
  intro pub sec tr₃
  rw [branchlessEncoded_hasTrace_iff]
  constructor
  · rintro rfl
    exact ⟨[10, 11], (branchlessLowered_hasTrace_iff pub sec [10, 11]).mpr rfl, rfl⟩
  · rintro ⟨tr₂, h₂, rfl⟩
    have htr₂ : tr₂ = [10, 11] := (branchlessLowered_hasTrace_iff pub sec tr₂).mp h₂
    subst htr₂
    rfl

/-- **Tightness counterexample for `h₁₂` in `leakage_determined_comp`.** Dropping the
first-pass `LeakageDetermined` assumption while keeping the second pass `LeakageDetermined`
breaks `LeakageDetermined` for the composed pipeline. -/
theorem leakage_determined_comp_drop_first_counterexample :
    LeakageDetermined branchingSelect branchingSelect (fun _ tr => tr) ∧
    ¬ LeakageDetermined branchlessSelect branchingSelect
        (composeLeakMap (fun _ tr => tr) (fun _ tr => tr)) :=
  ⟨leakage_determined_drop_ct_counterexample.1,
   leakageDetermined_neg_example (composeLeakMap (fun _ tr => tr) (fun _ tr => tr))⟩

/-- **Tightness counterexample for `h₂₃` in `leakage_determined_comp`.** Dropping the
second-pass `LeakageDetermined` assumption while keeping the first pass `LeakageDetermined`
breaks `LeakageDetermined` for the composed pipeline. -/
theorem leakage_determined_comp_drop_second_counterexample :
    LeakageDetermined branchlessSelect branchlessSelect (fun _ tr => tr) ∧
    ¬ LeakageDetermined branchlessSelect branchingSelect
        (composeLeakMap (fun _ tr => tr) (fun _ tr => tr)) := by
  refine ⟨?_, leakageDetermined_neg_example (composeLeakMap (fun _ tr => tr) (fun _ tr => tr))⟩
  intro pub sec tr
  exact ⟨fun h => ⟨tr, h, rfl⟩, fun ⟨_, h, heq⟩ => heq ▸ h⟩

end Toy.CT
