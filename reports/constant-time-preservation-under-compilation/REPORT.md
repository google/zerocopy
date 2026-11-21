# Constant-time preservation under compilation: a mechanized small-step leakage model (Lean 4)

## Summary

This package is a kernel-checked Lean 4 theory (namespace `Toy.CT`, core Lean only) of when a compilation step preserves constant-time security. A program is a small-step machine whose every transition emits one leakage event; `ConstantTime M` means that for every public input the *set* of leakage traces of complete halting runs is the same for every secret. A compilation step is modeled as one (source machine, target machine) pair; no result quantifies over a compiler. Seven results:

- **Result 1 (counterexample).** Functional correctness does not preserve constant time: the concrete transition-deterministic, terminating machines `branchlessSelect` (constant-time) and `branchingSelect` have the same halting outputs on every input (`FunctionallyCorrect`), yet `branchingSelect` violates `ConstantTime` under program-counter leakage.
- **Result 2 (theorem).** For any machines `S`, `T` and any secret-independent trace map `leakMap : Pub → List SrcLeak → List TgtLeak`, if `LeakageDetermined S T leakMap` holds (on every `(pub, sec)`, the halting traces of `T` are exactly the `leakMap pub`-images of the halting traces of `S`) and `ConstantTime S` holds, then `ConstantTime T` holds; no determinism, termination, or functional correctness is assumed.
- **Result 2b (characterization).** If `S` is `ConstantTime` and `T` is `TraceUnique` (at most one halting trace per input, e.g. any `Deterministic` target), then *some* secret-independent `leakMap` with `LeakageDetermined S T leakMap` exists if and only if `T` is `ConstantTime` and `S`, `T` halt on exactly the same inputs (`HaltAgree S T`); for a single pair, merely asserting that some such map exists is therefore logically equivalent to `ConstantTime T ∧ HaltAgree S T`, so `LeakageDetermined` gives leverage only when `leakMap` is supplied independently of the target's security argument (for example by Result 3 as `liftStepLeak stepLeak`).
- **Result 3 (theorem).** If a forward step simulation `StepLeakSim S T stepLeak measure R` holds, in which each source step with event `ls` is matched by target steps emitting exactly `stepLeak pub ls` (a list fixed by the public input and the source event) and `measure` strictly decreases on source steps mapped to `[]`, and the source satisfies `HasInit` and `Safe` and the target is `Deterministic`, then `LeakageDetermined S T (liftStepLeak stepLeak)` holds; hence, by Result 2, a constant-time source then has a constant-time target.
- **Result 4a (counterexample).** Concretely, on `branchlessSelect`/`branchingSelect` a trace map that reads the secret satisfies `SecretDependentLeakageDetermined`, while no secret-independent map satisfies `LeakageDetermined` and the target is not `ConstantTime`; in general, letting the map read the secret makes the condition satisfiable for every trace-unique target with matching halting domain.
- **Result 4b (counterexample).** Concretely, the deterministic constant-time source `constOneStep` is forward-simulated (`StepLeakSim`, identity step map) by the nondeterministic target `nondetSecretBranchTarget`, with `FunctionallyCorrect`, yet `LeakageDetermined` and `ConstantTime` of the target both fail; the determinized target satisfies both.
- **Result 5 (theorem, reference point).** `LeakageDetermined` composes: from `M₁` to `M₂` via `f` and from `M₂` to `M₃` via `g` gives `M₁` to `M₃` via `fun pub tr => g pub (f pub tr)`; the proof is definitional.

What these results do **not** show is listed per result at the start of `## Boundaries`; read the relevant non-claims before relying on any result.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

### Model fidelity

This is a **toy model**. Every definition is stated directly in core Lean over an abstract `Machine` structure; nothing here is a formalization of a production compiler, ISA, or hardware model.

What the definitions are meant to capture:

- **Programs** as small-step operational semantics (source IRs, intermediate representations, or assembly) in which every transition emits one observation, as in the program-counter security model (Molnar et al., ICISC 2005; the event is the program counter) or structured-leakage models (Barthe et al., CCS 2021; the event is a leakage record).
- **Constant-time security** as indistinguishability of the observable leakage of complete runs across secrets that share the same public input.
- **A compilation step** as one (source, target) pair. To apply a result to a compiler pass, the hypotheses must be discharged for each program the pass produces.

Known gaps between the model and real systems:

1. **Halting runs only.** `ConstantTime` quantifies over complete halting executions. A machine with no halting run on some input is constant-time on that input whatever it leaks before diverging (`Toy.CT.leakyLoop_constantTime_despite_diverging_step_leak`). This differs from the prefix-based (step-indexed) definition of Barthe, Grégoire and Laporte (CSF 2018).
2. **Possibilistic, not probabilistic.** `ConstantTime` compares sets of traces and gives no weight to transition probabilities; single-trace behavior is the separate property `TraceUnique`. A secret-oblivious coin flip is accepted (`coinFlip`).
3. **Termination-sensitive and not refinement-closed.** Secret-dependent halting versus non-halting is rejected (`Toy.CT.constantTime_abort_neg_example`), and a target whose halting traces are a subset of a constant-time source's can fail to be constant-time (`Toy.CT.constantTime_not_refinement_closed`). So the classical preservation of subset-closed hyperproperties under refinement (Clarkson and Schneider 2010; Abate et al., ESOP 2020) does not apply.
4. **Two-sided may-halting functional correctness.** `FunctionallyCorrect` equates the sets of outputs of halting runs. It implies one-sided inclusion of halting outputs, but it constrains complete halting runs only: on an input where neither machine halts it imposes no condition, even when both machines are deterministic, so one machine may diverge there while the other is stuck (for example `silentLoopSource` and `stuckMachine`, whose `halted` predicates are both `False`). It is therefore not a strengthening of CompCert-style backward simulation, which for a safe source also rules out a stuck target; this comparison is unproved commentary (see the Result 1 non-claims), and no formal relation to backward simulation is proved here.
5. **Leakage-functional simulation.** `StepLeakSim` fixes the target leakage of each source step from `(pub, ls)` alone. It is a special case of the relational constant-time simulations of Barthe, Grégoire and Laporte (CSF 2018), which allow state-dependent step counts guarded by an invariant over pairs of executions.
6. **Exactly one event per step.** Every transition emits one `Leak` value; eliminated source steps are modeled by `stepLeak pub ls = []`. Trace equality therefore requires equal step counts and equal per-step values.
7. **No environment interaction.** Events are pure observations: there are no inputs read during execution, so CompCert's receptiveness condition and `match_traces` have no counterpart.
8. **No hardware model.** Variable-latency instructions, caches, and speculative execution are represented only if the user puts them into `Leak`.

### Subjects and their relation

- **Lean 4 toolchain `v4.34.1`** (repository `leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`) is the checker for every theorem. The Lake project uses core Lean only: **no Mathlib**, no `Std` import, no `[[require]]` (the stand-alone audit program `lean/RevalidationAudit.lean` additionally imports Lean's own `Lean` module).
- **CompCert `common/Smallstep.v` at tag `v3.18`** (commit `14d616046360a0b2611ebdfc2f98368af402e1f7`) is a comparison point: its `determinate` record is compared with `Deterministic` below, and its `forward_to_backward_simulation` lemma is the argument that Result 3 re-derives for leakage. Nothing in this package is mechanically linked to CompCert.
- **The papers** listed as subjects are prior art that the results re-derive in this vocabulary (tiers T0/T1). No claim is made about the papers' own formal artifacts beyond the quoted records.

### Core definitions

All definitions are in `lean/ToyCT/Defs.lean` (quoted without doc comments).

```lean
structure Machine (Pub Sec Out Leak : Type) where
  State : Type
  init : Pub → Sec → State → Prop
  step : State → Leak → State → Prop
  halted : State → Out → Prop

inductive Steps {Pub Sec Out Leak : Type} (M : Machine Pub Sec Out Leak) :
    M.State → List Leak → M.State → Prop where
  | nil (s : M.State) : Steps M s [] s
  | cons {s s' s'' : M.State} {l : Leak} {tr : List Leak} :
      M.step s l s' → Steps M s' tr s'' → Steps M s (l :: tr) s''

def Executes (M : Machine Pub Sec Out Leak) (pub : Pub) (sec : Sec) (out : Out) (tr : List Leak) : Prop :=
  ∃ s₀ sf, M.init pub sec s₀ ∧ Steps M s₀ tr sf ∧ M.halted sf out

def HasTrace (M : Machine Pub Sec Out Leak) (pub : Pub) (sec : Sec) (tr : List Leak) : Prop :=
  ∃ out, Executes M pub sec out tr

def Reachable (M : Machine Pub Sec Out Leak) (pub : Pub) (sec : Sec) (s : M.State) : Prop :=
  ∃ s₀ tr, M.init pub sec s₀ ∧ Steps M s₀ tr s

def HasInit (M : Machine Pub Sec Out Leak) : Prop := ∀ pub sec, ∃ s₀, M.init pub sec s₀

def Safe (M : Machine Pub Sec Out Leak) : Prop :=
  ∀ pub sec s, Reachable M pub sec s → (∃ out, M.halted s out) ∨ (∃ l s', M.step s l s')

def Terminates (M : Machine Pub Sec Out Leak) : Prop := ∀ pub sec, ∃ out tr, Executes M pub sec out tr

structure Deterministic (M : Machine Pub Sec Out Leak) : Prop where
  init_det : ∀ pub sec s₁ s₂, M.init pub sec s₁ → M.init pub sec s₂ → s₁ = s₂
  step_det : ∀ s l₁ s₁ l₂ s₂, M.step s l₁ s₁ → M.step s l₂ s₂ → l₁ = l₂ ∧ s₁ = s₂
  halted_nostep : ∀ s out l s', M.halted s out → ¬ M.step s l s'

def OutputDeterministic (M : Machine Pub Sec Out Leak) : Prop :=
  ∀ s out₁ out₂, M.halted s out₁ → M.halted s out₂ → out₁ = out₂

def TraceUnique (M : Machine Pub Sec Out Leak) : Prop :=
  ∀ pub sec tr₁ tr₂, HasTrace M pub sec tr₁ → HasTrace M pub sec tr₂ → tr₁ = tr₂

def HaltAgree (S : Machine Pub Sec SrcOut SrcLeak) (T : Machine Pub Sec TgtOut TgtLeak) : Prop :=
  ∀ pub sec, (∃ trS, HasTrace S pub sec trS) ↔ (∃ trT, HasTrace T pub sec trT)

def ConstantTime (M : Machine Pub Sec Out Leak) : Prop :=
  ∀ pub s₁ s₂ tr, HasTrace M pub s₁ tr ↔ HasTrace M pub s₂ tr

def FunctionallyCorrect (S : Machine Pub Sec Out SrcLeak) (T : Machine Pub Sec Out TgtLeak) : Prop :=
  ∀ pub sec out, (∃ trS, Executes S pub sec out trS) ↔ (∃ trT, Executes T pub sec out trT)

def LeakageDetermined (S : Machine Pub Sec SrcOut SrcLeak) (T : Machine Pub Sec TgtOut TgtLeak)
    (leakMap : Pub → List SrcLeak → List TgtLeak) : Prop :=
  ∀ pub sec trT, HasTrace T pub sec trT ↔ ∃ trS, HasTrace S pub sec trS ∧ trT = leakMap pub trS

def WeakLeakageDetermined (S : Machine Pub Sec SrcOut SrcLeak) (T : Machine Pub Sec TgtOut TgtLeak)
    (leakMap : Pub → List SrcLeak → List TgtLeak) : Prop :=
  (∀ pub sec trT, HasTrace T pub sec trT → ∃ trS, HasTrace S pub sec trS ∧ trT = leakMap pub trS) ∧
  (∀ pub sec trS, HasTrace S pub sec trS → ∃ trT, HasTrace T pub sec trT)

def SecretDependentLeakageDetermined (S : Machine Pub Sec SrcOut SrcLeak) (T : Machine Pub Sec TgtOut TgtLeak)
    (leakMap : Pub → Sec → List SrcLeak → List TgtLeak) : Prop :=
  ∀ pub sec trT, HasTrace T pub sec trT ↔ ∃ trS, HasTrace S pub sec trS ∧ trT = leakMap pub sec trS

def liftStepLeak (stepLeak : Pub → SrcLeak → List TgtLeak) (pub : Pub) (tr : List SrcLeak) : List TgtLeak :=
  match tr with
  | [] => []
  | l :: rest => stepLeak pub l ++ liftStepLeak stepLeak pub rest

structure StepLeakSim (S : Machine Pub Sec Out SrcLeak) (T : Machine Pub Sec Out TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak) (measure : S.State → Nat)
    (R : Pub → Sec → S.State → T.State → Prop) : Prop where
  init_sim : ∀ pub sec s₀, S.init pub sec s₀ → ∃ t₀, T.init pub sec t₀ ∧ R pub sec s₀ t₀
  halted_sim : ∀ pub sec s t out, R pub sec s t → S.halted s out → T.halted t out
  step_sim : ∀ pub sec s ls s' t, R pub sec s t → S.step s ls s' →
    (∃ t', Steps T t (stepLeak pub ls) t' ∧ R pub sec s' t') ∧
    (stepLeak pub ls = [] → measure s' < measure s)

structure UnmeasuredStepLeakSim (S : Machine Pub Sec Out SrcLeak) (T : Machine Pub Sec Out TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak) (R : Pub → Sec → S.State → T.State → Prop) : Prop where
  init_sim : ∀ pub sec s₀, S.init pub sec s₀ → ∃ t₀, T.init pub sec t₀ ∧ R pub sec s₀ t₀
  halted_sim : ∀ pub sec s t out, R pub sec s t → S.halted s out → T.halted t out
  step_sim : ∀ pub sec s ls s' t, R pub sec s t → S.step s ls s' →
    ∃ t', Steps T t (stepLeak pub ls) t' ∧ R pub sec s' t'

structure OptionStepLeakSim (S : Machine Pub Sec Out SrcLeak) (T : Machine Pub Sec Out TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak) (measure : S.State → Nat)
    (R : Pub → Sec → S.State → T.State → Prop) : Prop where
  init_sim : ∀ pub sec s₀, S.init pub sec s₀ → ∃ t₀, T.init pub sec t₀ ∧ R pub sec s₀ t₀
  halted_sim : ∀ pub sec s t out, R pub sec s t → S.halted s out → T.halted t out
  step_sim : ∀ pub sec s ls s' t, R pub sec s t → S.step s ls s' →
    (∃ t', Steps T t (stepLeak pub ls) t' ∧ R pub sec s' t') ∨ (measure s' < measure s ∧ R pub sec s' t)

def composeLeakMap (f : Pub → List Leak₁ → List Leak₂) (g : Pub → List Leak₂ → List Leak₃) :
    Pub → List Leak₁ → List Leak₃ :=
  fun pub tr₁ => g pub (f pub tr₁)
```

(Each definition's implicit type arguments, e.g. `{Pub Sec Out Leak : Type}`, are elided above; the Lean source binds them explicitly.)

What each definition is meant to capture, with its proved adequacy examples (all in `lean/ToyCT/Examples.lean` unless noted):

| Definition | Intended meaning | Proved positive / negative examples |
| :-- | :-- | :-- |
| `Steps`, `Executes`, `HasTrace`, `Reachable` | Finite runs; a complete halting run with output and trace; the set of halting traces; reachable configurations. | `steps_pos_example` / `steps_neg_example`; `executes_pos_example` / `executes_neg_example`; `hasTrace_pos_example` / `hasTrace_neg_example`; `reachable_pos_example` / `reachable_neg_example` |
| `HasInit` | Every input has an initial configuration. | `hasInit_pos_example` / `hasInit_neg_example` |
| `Safe` | Reachable configurations never get stuck (they halt or step); non-terminating machines are allowed. | `safe_pos_example`, `safe_nonterminating_pos_example` / `safe_neg_example` |
| `Terminates` | May-termination: every input has at least one halting run. For nondeterministic machines diverging runs may coexist (`haltOrLeak`); only `Deterministic M ∧ Terminates M` makes every run halt. | `terminates_pos_example` / `terminates_neg_example` |
| `Deterministic` | Small-step determinism: unique initial configuration, unique event and successor per step, halted configurations do not step. | `deterministic_pos_example` / `deterministic_neg_example` |
| `OutputDeterministic` | A halted configuration has at most one output. | `outputDeterministic_pos_example` / `outputDeterministic_neg_example` |
| `TraceUnique` | At most one halting trace per input (`Deterministic.traceUnique` in `Defs.lean`). | `traceUnique_pos_example` / `traceUnique_neg_example` |
| `HaltAgree` | Source and target halt on the same inputs. | `haltAgree_pos_example` / `haltAgree_neg_example` |
| `ConstantTime` | Halting-trace-set equality across secrets for each public input. | `constantTime_pos_example` (`branchlessSelect`), `constantTime_nondet_pos_example` (`coinFlip`) / `constantTime_neg_example` (`branchingSelect`), `constantTime_abort_neg_example` (`abortOnSecret`) |
| `FunctionallyCorrect` | Equal sets of halting outputs per input. | `functionallyCorrect_pos_example` / `functionallyCorrect_neg_example` |
| `LeakageDetermined` | Target halting traces are exactly the images of source halting traces under a map that sees only the public input. | `leakageDetermined_pos_example` / `leakageDetermined_neg_example` |
| `WeakLeakageDetermined` | One-way image inclusion plus "the target halts whenever the source halts". | `weakLeakageDetermined_pos_example` / `weakLeakageDetermined_neg_example` |
| `SecretDependentLeakageDetermined` | `LeakageDetermined` with a map that may also read the secret. | `secretDependentLeakageDetermined_pos_example` / `secretDependentLeakageDetermined_neg_example` |
| `liftStepLeak` | Homomorphic extension of a per-step leakage map to traces. | `liftStepLeak_pos_example` / `liftStepLeak_neg_example` |
| `StepLeakSim`, `UnmeasuredStepLeakSim`, `OptionStepLeakSim` | Forward step simulation with per-step leakage map and anti-stuttering measure; the same without the measure; a single-run variant whose step-or-stutter choice may depend on configurations. | `stepLeakSim_pos_example` / `stepLeakSim_neg_example`; `unmeasuredStepLeakSim_pos_example` / `unmeasuredStepLeakSim_neg_example`; `optionStepLeakSim_pos_example` / `optionStepLeakSim_neg_example` |
| `composeLeakMap` | Sequential composition of trace maps. | `composeLeakMap_pos_example` / `composeLeakMap_neg_example` |

Further proved facts about these definitions, all in `lean/ToyCT/Defs.lean` (statements quoted without proofs or doc comments):

```lean
-- lean/ToyCT/Defs.lean:373-377
theorem constantTime_and_traceUnique_iff {Pub Sec Out Leak : Type}
    (M : Machine Pub Sec Out Leak) :
    (ConstantTime M ∧ TraceUnique M) ↔
      (∀ pub s₁ s₂ tr₁, HasTrace M pub s₁ tr₁ →
        ∀ tr₂, (HasTrace M pub s₂ tr₂ ↔ tr₂ = tr₁))
-- lean/ToyCT/Defs.lean:395-398
theorem constantTime_iff_trace_eq_of_terminates_traceUnique {Pub Sec Out Leak : Type}
    {M : Machine Pub Sec Out Leak} (hTerm : Terminates M) (hUnique : TraceUnique M) :
    ConstantTime M ↔
      (∀ pub s₁ s₂ tr₁ tr₂, HasTrace M pub s₁ tr₁ → HasTrace M pub s₂ tr₂ → tr₁ = tr₂)
-- lean/ToyCT/Defs.lean:416-420
theorem haltAgree_of_terminates {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak}
    {T : Machine Pub Sec TgtOut TgtLeak}
    (hTermS : Terminates S) (hTermT : Terminates T) :
    HaltAgree S T
-- lean/ToyCT/Defs.lean:427-432
theorem haltAgree_of_leakageDetermined {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak}
    {T : Machine Pub Sec TgtOut TgtLeak}
    {leakMap : Pub → List SrcLeak → List TgtLeak}
    (hLD : LeakageDetermined S T leakMap) :
    HaltAgree S T
-- lean/ToyCT/Defs.lean:444-452
theorem leakageDetermined_of_terminates_trace_eq
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak}
    {T : Machine Pub Sec TgtOut TgtLeak}
    {leakMap : Pub → List SrcLeak → List TgtLeak}
    (hTermS : Terminates S) (hTermT : Terminates T)
    (hEq : ∀ pub sec trS trT, HasTrace S pub sec trS → HasTrace T pub sec trT →
      trT = leakMap pub trS) :
    LeakageDetermined S T leakMap
-- lean/ToyCT/Defs.lean:542-544
theorem hasInit_and_safe_of_det_terminates {Pub Sec Out Leak : Type}
    {S : Machine Pub Sec Out Leak} (hDet : Deterministic S) (hTerm : Terminates S) :
    HasInit S ∧ Safe S
```

`haltAgree_of_leakageDetermined` gives the forward direction of Result 2b; `haltAgree_of_terminates` is used in the proofs of `haltAgree_pos_example` and `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_both_sides_true`; `hasInit_and_safe_of_det_terminates` is cited in Result 3.

### Correspondence of `Deterministic` with CompCert's `determinate`

CompCert's record, quoted from `common/Smallstep.v` at commit `14d616046360a0b2611ebdfc2f98368af402e1f7` (lines 1058–1071):

```coq
Record determinate (L: semantics) : Prop :=
  Determinate {
    sd_determ: forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces (symbolenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces:
      single_events L;
    sd_initial_determ: forall s1 s2,
      initial_state L s1 -> initial_state L s2 -> s1 = s2;
    sd_final_nostep: forall s r,
      final_state L s r -> Nostep L s;
    sd_final_determ: forall s r1 r2,
      final_state L s r1 -> final_state L s r2 -> r1 = r2
  }.
```

`Deterministic` corresponds to three of these five fields: `step_det` to `sd_determ` (strengthened: the two single leakage events must be *equal*, not merely related by `match_traces`, and then the successors are equal), `init_det` to `sd_initial_determ` (per input `(pub, sec)`), and `halted_nostep` to `sd_final_nostep`. `OutputDeterministic` corresponds to `sd_final_determ`. `sd_traces` (`single_events L`, i.e. every step emits at most one event, lines 1047–1048) has no separate counterpart because the model builds it in: every step emits exactly one event. Basis: source (quoted record) + derived (field-by-field comparison above).

## Findings

Results are numbered as in the Summary. Every Lean name below is in namespace `Toy.CT` and is defined in `lean/ToyCT/{Defs,Machines,Examples,Results}.lean`. Each main theorem, counterexample, non-vacuity witness, and positive control is fully proved; the per-theorem axiom record is in `## Evidence`.

| Result | Card id | Lean name | Kind | Tier | Depth |
| :-- | :-- | :-- | :-- | :-- | :-- |
| 1 | `functional-correctness-does-not-preserve-ct` | `Toy.CT.functional_correctness_does_not_preserve_ct` | counterexample | T0 | shallow |
| 2 | `leakage-determined-preserves-ct` | `Toy.CT.leakage_determined_preserves_ct` | theorem | T0 | shallow |
| 2b | `single-pair-leakage-determined-characterization` | `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique` | characterization | T1 | shallow |
| 3 | `step-leakage-simulation-implies-leakage-determined` | `Toy.CT.step_leakage_sim_det_target_implies_leakage_determined` | theorem | T0 | substantive |
| 4a | `secret-dependent-leakage-map-breaks-ct` | `Toy.CT.secret_dependent_leak_map_breaks_ct` | counterexample | T0 | shallow |
| 4b | `nondeterministic-target-breaks-step-simulation-ct` | `Toy.CT.nondeterministic_target_sim_breaks_leakage_determined` | counterexample | T0 | shallow |
| 5 | `leakage-determined-composes` | `Toy.CT.leakage_determined_comp` | theorem | T0 | definitional |

### Concrete machines, maps, and relations

Every witness, counterexample, and positive control is built from these definitions (quoted from `lean/ToyCT/Machines.lean`, `Examples.lean`, and `Results.lean`). In the selector machines the leakage event is the program counter of the executed instruction. `wrongOutputSelect` and `ambiguousOutputMachine` are used only by the adequacy examples `functionallyCorrect_neg_example` and `outputDeterministic_neg_example`.

```lean
inductive SelectState where
  | entry (a b : Nat) (cond : Bool)
  | done (result : Nat)
  deriving DecidableEq, Repr

def branchlessSelect : Machine (Nat × Nat) Bool Nat Nat where
  State := SelectState
  init pub sec s := s = .entry pub.1 pub.2 sec
  step s pc s' :=
    match s with
    | .entry a b cond => pc = 0 ∧ s' = .done (if cond then a else b)
    | .done _ => False
  halted s out := s = .done out

inductive BranchSelectState where
  | entry (a b : Nat) (cond : Bool)
  | thenBlock (a : Nat)
  | elseBlock (b : Nat)
  | done (result : Nat)
  deriving DecidableEq, Repr

def branchingSelect : Machine (Nat × Nat) Bool Nat Nat where
  State := BranchSelectState
  init pub sec s := s = .entry pub.1 pub.2 sec
  step s pc s' :=
    match s with
    | .entry a b cond =>
        pc = 0 ∧ s' = (if cond then .thenBlock a else .elseBlock b)
    | .thenBlock a => pc = 1 ∧ s' = .done a
    | .elseBlock b => pc = 2 ∧ s' = .done b
    | .done _ => False
  halted s out := s = .done out

inductive NopSelectState where
  | nop (a b : Nat) (cond : Bool)
  | select (a b : Nat) (cond : Bool)
  | done (result : Nat)
  deriving DecidableEq, Repr

def branchlessWithNop : Machine (Nat × Nat) Bool Nat Nat where
  State := NopSelectState
  init pub sec s := s = .nop pub.1 pub.2 sec
  step s pc s' :=
    match s with
    | .nop a b cond => pc = 0 ∧ s' = .select a b cond
    | .select a b cond => pc = 1 ∧ s' = .done (if cond then a else b)
    | .done _ => False
  halted s out := s = .done out

inductive LoweredSelectState where
  | mask (a b : Nat) (cond : Bool)
  | combine (chosen : Nat)
  | done (result : Nat)
  deriving DecidableEq, Repr

def branchlessLowered : Machine (Nat × Nat) Bool Nat Nat where
  State := LoweredSelectState
  init pub sec s := s = .mask pub.1 pub.2 sec
  step s pc s' :=
    match s with
    | .mask a b cond => pc = 10 ∧ s' = .combine (if cond then a else b)
    | .combine v => pc = 11 ∧ s' = .done v
    | .done _ => False
  halted s out := s = .done out

inductive EncodedSelectState where
  | instr0 (base : Nat) (a b : Nat) (cond : Bool)
  | instr1 (base : Nat) (chosen : Nat)
  | done (result : Nat)
  deriving DecidableEq, Repr

def branchlessEncoded : Machine (Nat × Nat) Bool Nat Nat where
  State := EncodedSelectState
  init pub sec s := s = .instr0 (pub.1 % 2) pub.1 pub.2 sec
  step s pc s' :=
    match s with
    | .instr0 base a b cond =>
        pc = 100 + base ∧ s' = .instr1 base (if cond then a else b)
    | .instr1 base v =>
        pc = 101 + base ∧ s' = .done v
    | .done _ => False
  halted s out := s = .done out

def abortOnSecret : Machine Unit Bool Unit Nat where
  State := Bool
  init _ sec s := s = sec
  step _ _ _ := False
  halted s out := s = false ∧ out = ()

def haltIfTrue : Machine Unit Bool Unit Nat where
  State := Bool
  init _ sec s := s = sec
  step _ _ _ := False
  halted s out := s = true ∧ out = ()

def allHalt : Machine Unit Bool Unit Nat where
  State := Unit
  init _ _ s := s = ()
  step _ _ _ := False
  halted _ out := out = ()

def coinFlip : Machine Unit Bool Unit Nat where
  State := Bool
  init _ _ s := s = false
  step s l s' := s = false ∧ (l = 0 ∨ l = 1) ∧ s' = true
  halted s out := s = true ∧ out = ()

def leakyLoop : Machine Unit Bool Unit Nat where
  State := Bool
  init _ sec s := s = sec
  step s l s' := l = (if s then 1 else 0) ∧ s' = s
  halted _ _ := False

inductive HaltOrLeakState where
  | start (sec : Bool)
  | loop (sec : Bool)
  deriving DecidableEq, Repr

def haltOrLeak : Machine Unit Bool Unit Nat where
  State := HaltOrLeakState
  init _ sec s := s = .start sec
  step s l s' :=
    match s with
    | .start b => l = (if b then 1 else 0) ∧ s' = .loop b
    | .loop b => l = (if b then 1 else 0) ∧ s' = .loop b
  halted s out :=
    match s with
    | .start _ => out = ()
    | .loop _ => False

def emptyInitMachine : Machine Unit Bool Unit Nat where
  State := Unit
  init _ _ _ := False
  step _ _ _ := False
  halted _ out := out = ()

def stuckMachine : Machine Unit Bool Unit Nat where
  State := Unit
  init _ _ s := s = ()
  step _ _ _ := False
  halted _ _ := False

def trivialHaltedMachine : Machine Unit Bool Unit Nat where
  State := Unit
  init _ _ s := s = ()
  step _ _ _ := False
  halted s out := s = () ∧ out = ()

def constOneStep : Machine Unit Bool Unit Nat where
  State := Bool
  init _ _ s := s = false
  step s l s' := s = false ∧ l = 0 ∧ s' = true
  halted s out := s = true ∧ out = ()

inductive NondetTargetState where
  | start (sec : Bool)
  | done
  deriving DecidableEq, Repr

def nondetSecretBranchTarget : Machine Unit Bool Unit Nat where
  State := NondetTargetState
  init _ sec s := s = .start sec
  step s l s' :=
    match s with
    | .start false => l = 0 ∧ s' = .done
    | .start true => (l = 0 ∨ l = 1) ∧ s' = .done
    | .done => False
  halted s out := s = .done ∧ out = ()

def determinizedSecretBranchTarget : Machine Unit Bool Unit Nat where
  State := NondetTargetState
  init _ sec s := s = .start sec
  step s l s' :=
    match s with
    | .start _ => l = 0 ∧ s' = .done
    | .done => False
  halted s out := s = .done ∧ out = ()

def silentLoopSource : Machine Unit Bool Unit Nat where
  State := Unit
  init _ _ s := s = ()
  step s l s' := s = () ∧ l = 0 ∧ s' = ()
  halted _ _ := False

def wrongOutputSelect : Machine (Nat × Nat) Bool Nat Nat where
  State := Bool
  init _ _ s := s = false
  step s pc s' := s = false ∧ pc = 0 ∧ s' = true
  halted s out := s = true ∧ out = 0

def ambiguousOutputMachine : Machine Unit Bool Bool Nat where
  State := Unit
  init _ _ s := s = ()
  step _ _ _ := False
  halted _ _ := True

inductive TwoInitState where
  | a
  | b
  | fin
  deriving DecidableEq, Repr

def secretTwoInitTarget : Machine Unit Bool Unit Nat where
  State := TwoInitState
  init _ sec s := s = .a ∨ (sec = true ∧ s = .b)
  step s l s' :=
    match s with
    | .a => l = 0 ∧ s' = .fin
    | .b => l = 1 ∧ s' = .fin
    | .fin => False
  halted s out := s = .fin ∧ out = ()

inductive SecretForkState where
  | start (sec : Bool)
  | a
  | b
  | fin
  deriving DecidableEq, Repr

def secretForkTarget : Machine Unit Bool Unit Nat where
  State := SecretForkState
  init _ sec s := s = .start sec
  step s l s' :=
    match s with
    | .start sec => l = 0 ∧ (s' = .a ∨ (sec = true ∧ s' = .b))
    | .a => False
    | .b => l = 1 ∧ s' = .fin
    | .fin => False
  halted s out := (s = .a ∨ s = .fin) ∧ out = ()

def secretHaltOrStepTarget : Machine Unit Bool Unit Nat where
  State := Bool × Bool
  init _ sec s := s = (false, sec)
  step s l s' := s.1 = false ∧ s.2 = true ∧ l = 1 ∧ s' = (true, s.2)
  halted _ out := out = ()

inductive TwoStepState where
  | s2
  | s1
  | s0
  deriving DecidableEq, Repr

def twoStepMeasure : TwoStepState → Nat
  | .s2 => 2
  | .s1 => 1
  | .s0 => 0

def twoStepConstSource : Machine Unit Bool Unit Nat where
  State := TwoStepState
  init _ _ s := s = .s2
  step s l s' :=
    match s with
    | .s2 => l = 0 ∧ s' = .s1
    | .s1 => l = 0 ∧ s' = .s0
    | .s0 => False
  halted s out := s = .s0 ∧ out = ()

def secretStutterTarget : Machine Unit Bool Unit Nat where
  State := TwoStepState
  init _ sec s := s = if sec then .s1 else .s2
  step s l s' :=
    match s with
    | .s2 => l = 0 ∧ s' = .s1
    | .s1 => l = 0 ∧ s' = .s0
    | .s0 => False
  halted s out := s = .s0 ∧ out = ()

def selectToLoweredLeakMap : (Nat × Nat) → List Nat → List Nat :=
  fun _ tr =>
    match tr with
    | [0] => [10, 11]
    | _ => []

def loweredToEncodedLeakMap : (Nat × Nat) → List Nat → List Nat :=
  fun pub tr =>
    match tr with
    | [10, 11] => [100 + pub.1 % 2, 101 + pub.1 % 2]
    | _ => []

def secretBranchLeakMap : (Nat × Nat) → Bool → List Nat → List Nat :=
  fun _ sec tr =>
    match tr with
    | [0] => [0, if sec then 1 else 2]
    | _ => []

def nopToLoweredStepLeak : (Nat × Nat) → Nat → List Nat :=
  fun _ pc =>
    match pc with
    | 0 => []
    | 1 => [10, 11]
    | _ => [pc]

def nopSelectMeasure : NopSelectState → Nat
  | .nop _ _ _ => 2
  | .select _ _ _ => 1
  | .done _ => 0

def nopToLoweredRel (_pub : Nat × Nat) (_sec : Bool)
    (s : NopSelectState) (t : LoweredSelectState) : Prop :=
  match s with
  | .nop a b cond => t = .mask a b cond
  | .select a b cond => t = .mask a b cond
  | .done v => t = .done v

def constNondetRel (_pub : Unit) (sec : Bool) (s : Bool) (t : NondetTargetState) : Prop :=
  if s then t = .done else t = .start sec

def optionStutterRel (_pub : Unit) (sec : Bool) (s t : TwoStepState) : Prop :=
  if sec then
    (s = .s2 ∧ t = .s1) ∨ (s = .s1 ∧ t = .s1) ∨ (s = .s0 ∧ t = .s0)
  else
    s = t
```

Key trace facts. Proved as `*_hasTrace_iff` lemmas in `Machines.lean`: `branchlessSelect` has the single halting trace `[0]`; `branchingSelect` has `[0, if sec then 1 else 2]` (always two steps, `Toy.CT.branchingSelect_trace_length`); `branchlessLowered` has `[10, 11]`; `branchlessEncoded` has `[100 + pub.1 % 2, 101 + pub.1 % 2]`; `constOneStep` has `[0]`; `coinFlip` has `[0]` and `[1]` for every secret; `haltIfTrue` has `[]` when `sec = true` and no halting trace otherwise. Read off the definitions (used inside proofs, not stated as separate lemmas): `nondetSecretBranchTarget` has `[0]` for `sec = false` and both `[0]` and `[1]` for `sec = true`; `abortOnSecret` halts (trace `[]`) only when `sec = false`.

### Result 1: `functional-correctness-does-not-preserve-ct`

- **Lean:** `Toy.CT.functional_correctness_does_not_preserve_ct` — kind `counterexample`.
- **Tier:** T0 — re-derivation, in program-counter leakage form (Molnar et al., ICISC 2005), of the conditional-move-to-branch compilation counterexample of Barthe, Grégoire and Laporte (CSF 2018): compiling a branchless selection into a conditional branch preserves input/output behavior and introduces a control-flow side channel.
- **Depth:** shallow (direct computation of the two machines' halting traces and outputs).
- **Plain claim:** There exist concrete transition-deterministic, terminating small-step machines `branchlessSelect` and `branchingSelect` such that `branchlessSelect` satisfies `ConstantTime`, the pair satisfies `FunctionallyCorrect` (equating halting output sets on every input), and `branchingSelect` violates `ConstantTime`.

```lean
-- lean/ToyCT/Results.lean:16-23
theorem functional_correctness_does_not_preserve_ct :
    Deterministic branchlessSelect ∧
    Terminates branchlessSelect ∧
    Deterministic branchingSelect ∧
    Terminates branchingSelect ∧
    ConstantTime branchlessSelect ∧
    FunctionallyCorrect branchlessSelect branchingSelect ∧
    ¬ ConstantTime branchingSelect
```

Unfolded key clauses (prose):

```text
  (∀ pub s₁ s₂ tr, HasTrace branchlessSelect pub s₁ tr ↔ HasTrace branchlessSelect pub s₂ tr)
∧ (∀ pub sec out, (∃ trS, Executes branchlessSelect pub sec out trS) ↔
                  (∃ trT, Executes branchingSelect pub sec out trT))
∧ ¬ (∀ pub s₁ s₂ tr, HasTrace branchingSelect pub s₁ tr ↔ HasTrace branchingSelect pub s₂ tr)
```

- **Hypothesis ledger:** none (an unconditional statement about concrete machines).
- **Non-vacuity witness:** the pair itself, over `Pub = Nat × Nat`, `Sec = Bool`, `Out = Nat`, `Leak = Nat`: `branchlessSelect` computes `if sec then pub.1 else pub.2` in one step with trace `[0]`; `branchingSelect` branches at PC 0 to PC 1 (trace `[0, 1]`) or PC 2 (trace `[0, 2]`) (`Toy.CT.functional_correctness_does_not_preserve_ct`).
- **Positive control:** `Toy.CT.branchless_lowering_preserves_ct` — lowering the same source to the straight-line machine `branchlessLowered` is deterministic, terminating, `FunctionallyCorrect`, `LeakageDetermined` under `selectToLoweredLeakMap`, and `ConstantTime`:

```lean
-- lean/ToyCT/Results.lean:36-44
theorem branchless_lowering_preserves_ct :
    Deterministic branchlessSelect ∧ Terminates branchlessSelect ∧
    Deterministic branchlessLowered ∧ Terminates branchlessLowered ∧
    ConstantTime branchlessSelect ∧
    FunctionallyCorrect branchlessSelect branchlessLowered ∧
    LeakageDetermined branchlessSelect branchlessLowered selectToLoweredLeakMap ∧
    ConstantTime branchlessLowered
```

- **Related proved fact:** `Toy.CT.branchingSelect_trace_length : ∀ pub sec tr, HasTrace branchingSelect pub sec tr → tr.length = 2`.
- **Prior art:** Barthe, Grégoire, Laporte, CSF 2018, DOI 10.1109/CSF.2018.00031 (conditional-move-to-branch counterexample); Molnar, Piotrowski, Schultz, Wagner, ICISC 2005, LNCS 3935, pp. 156–168, DOI 10.1007/11734727_14 (program-counter model); Clarkson and Schneider, JCS 18(6), pp. 1157–1210, 2010, DOI 10.3233/JCS-2009-0393; Abate et al., ESOP 2020, LNCS 12075, pp. 1–28, DOI 10.1007/978-3-030-44914-8_1; D'Silva, Payer, Song, IEEE SPW 2015, pp. 73–87, DOI 10.1109/SPW.2015.33; Kaufmann, Pelletier, Vaudenay, Villegas, CANS 2016, LNCS 10052, pp. 573–582, DOI 10.1007/978-3-319-48965-0_36; Simon, Chisnall, Anderson, IEEE EuroS&P 2018, pp. 1–15, DOI 10.1109/EuroSP.2018.00009; Gerlach, Pietsch, Schwarz, FC 2025, LNCS 15752, pp. 327–344, Springer 2026, DOI 10.1007/978-3-032-07035-7_20. Full records are in `results.json`.
- **Design question:** Does a standard functional-correctness proof on a compiler pass (input/output equivalence) suffice to preserve constant-time side-channel guarantees? (Answer in this model: no.)

Basis: execution (Lean kernel check).
Basis: derived (modeling bridge) — `branchlessSelect` and `branchingSelect` are program-counter-transcript models of a conditional-move (or masking) selection and of the same selection compiled to a conditional branch. The theorem shows that, for these models, preservation of input/output behavior does not imply preservation of constant time. That the same phenomenon occurs in real compilers is reported by the cited compiler studies, not shown here.

### Result 2: `leakage-determined-preserves-ct`

- **Lean:** `Toy.CT.leakage_determined_preserves_ct` — kind `theorem`.
- **Tier:** T0 — re-derivation, over halting-trace-set `ConstantTime`, of the secret-independent leakage-transformer preservation principle of Barthe, Grégoire, Laporte and Priya (CCS 2021) and Barthe et al. (CSF 2018; ePrint 2026/2510).
- **Depth:** shallow (rewrite both sides of the target `↔` with `hLD`, then transport each source trace with `hCT`).
- **Plain claim:** For all small-step machines `S` and `T` sharing public and secret input types (with possibly distinct output and leakage types) and any secret-independent trace transformer `leakMap : Pub -> List SrcLeak -> List TgtLeak`, if `LeakageDetermined S T leakMap` holds (the halting traces of `T` on every `(pub, sec)` are exactly the images under `leakMap pub` of the halting traces of `S` on `(pub, sec)`) and `S` satisfies `ConstantTime`, then `T` satisfies `ConstantTime`.

```lean
-- lean/ToyCT/Results.lean:68-75
theorem leakage_determined_preserves_ct
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak)
    (leakMap : Pub → List SrcLeak → List TgtLeak)
    (hLD : LeakageDetermined S T leakMap)
    (hCT : ConstantTime S) :
    ConstantTime T
```

Unfolded:

```lean
∀ {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type} (S : Machine Pub Sec SrcOut SrcLeak)
  (T : Machine Pub Sec TgtOut TgtLeak) (leakMap : Pub → List SrcLeak → List TgtLeak),
  (∀ pub sec trT, (∃ outT, Executes T pub sec outT trT) ↔
                  (∃ trS, (∃ outS, Executes S pub sec outS trS) ∧ trT = leakMap pub trS)) →
  (∀ pub s₁ s₂ trS, (∃ o, Executes S pub s₁ o trS) ↔ (∃ o, Executes S pub s₂ o trS)) →
  (∀ pub s₁ s₂ trT, (∃ o, Executes T pub s₁ o trT) ↔ (∃ o, Executes T pub s₂ o trT))
```

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
| :-- | :-- | :-- | :-- |
| `hLD : LeakageDetermined S T leakMap` | Requires the halting target leakage traces of `T` on every `(pub, sec)` to be exactly the images under secret-independent `leakMap pub` of the halting source leakage traces of `S`. | tight | `Toy.CT.secret_dependent_leak_map_breaks_ct` (`ConstantTime branchlessSelect` holds, `∀ f, ¬ LeakageDetermined branchlessSelect branchingSelect f`, and `¬ ConstantTime branchingSelect`) |
| `hCT : ConstantTime S` | Requires the source machine `S` to satisfy `ConstantTime` (halting-trace-set equality across secrets). | tight | `Toy.CT.leakage_determined_drop_ct_counterexample` (`LeakageDetermined branchingSelect branchingSelect (fun _ tr => tr) ∧ ¬ ConstantTime branchingSelect`) |

`FunctionallyCorrect`, `Deterministic`, and `Terminates` are not hypotheses. Conversely, when both machines satisfy `Terminates`, `Toy.CT.leakageDetermined_of_terminates_trace_eq` reduces `LeakageDetermined` to the one-way condition `HasTrace S pub sec trS → HasTrace T pub sec trT → trT = leakMap pub trS`.

- **Non-vacuity witness:** `Toy.CT.leakage_determined_preserves_ct_nonvacuous : LeakageDetermined branchlessSelect branchlessLowered selectToLoweredLeakMap ∧ ConstantTime branchlessSelect` (source trace `[0]`, target trace `[10, 11]`).
- **Related proved facts (cited in the non-claims):**

```lean
-- lean/ToyCT/Defs.lean:468-476
theorem weakLeakageDetermined_preserves_ct_of_traceUnique
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak} {T : Machine Pub Sec TgtOut TgtLeak}
    {leakMap : Pub → List SrcLeak → List TgtLeak}
    (hWeak : WeakLeakageDetermined S T leakMap) (hUniqueS : TraceUnique S)
    (hCT : ConstantTime S) : ConstantTime T
-- lean/ToyCT/Examples.lean:359-362
theorem weakLeakageDetermined_fails_without_traceUnique :
    WeakLeakageDetermined coinFlip nondetSecretBranchTarget (fun _ tr => tr) ∧
    ConstantTime coinFlip ∧ ¬ ConstantTime nondetSecretBranchTarget
-- lean/ToyCT/Examples.lean:259-263
theorem terminates_and_constantTime_unconstrained_diverging_branch :
    Terminates haltOrLeak ∧ ConstantTime haltOrLeak ∧
    (∀ sec, haltOrLeak.step (.start sec) (if sec then 1 else 0) (.loop sec)) ∧
    (∀ sec tr sf, Steps haltOrLeak (.loop sec) tr sf → ¬ haltOrLeak.halted sf ())
-- lean/ToyCT/Examples.lean:238-240
theorem leakyLoop_constantTime_despite_diverging_step_leak :
    ConstantTime leakyLoop ∧
    (∀ (sec : Bool) l s', leakyLoop.step sec l s' → l = if sec then 1 else 0)
-- lean/ToyCT/Examples.lean:246-249
theorem constantTime_not_refinement_closed :
    (∀ sec tr, HasTrace haltIfTrue () sec tr → HasTrace allHalt () sec tr) ∧
    ConstantTime allHalt ∧ ¬ ConstantTime haltIfTrue
```

- **Prior art:** Barthe, Grégoire, Laporte, Priya, CCS 2021, pp. 462–476, DOI 10.1145/3460120.3484761; Barthe, Grégoire, Laporte, CSF 2018, DOI 10.1109/CSF.2018.00031; Abate et al., ESOP 2020, DOI 10.1007/978-3-030-44914-8_1; Barthe, Cassiers, Dohmen, Gourjon, Grégoire, Khayata, Schneider, Schubert, "Secure Compilation of Probabilistic Side-Channel Countermeasures," Cryptology ePrint Archive 2026/2510; Knothe and Bringmann, ITP 2025, LIPIcs 352, 31:1–31:19, DOI 10.4230/LIPIcs.ITP.2025.31 (secret control-flow elimination, which lies outside `LeakageDetermined`); Arranz Olmos, Barthe, Blatter, Grégoire, Laporte, "Preservation of Speculative Constant-Time by Compilation," PACMPL 9(POPL), 2025, DOI 10.1145/3704880.
- **Design question:** When a compiler pass or simulation proof supplies an explicit secret-independent trace transformer `leakMap` (without assuming functional equivalence, determinism, or termination), does `LeakageDetermined` suffice to transfer `ConstantTime` from source to target? (Answer in this model: yes.)

Basis: execution (Lean kernel check).
Basis: derived (modeling bridge) — if, for a given program, the observable leakage of the compiled program's halting runs is exactly the image of the source program's halting-run leakage under a map that sees only public inputs, then constant time (in the sense of `ConstantTime`, for the observations encoded in `Leak`) transfers from source to target. The bridge requires the real leakage model to be captured by the per-step events (gaps 1, 6 and 8 in `## Applicability`).

### Result 2b: `single-pair-leakage-determined-characterization`

- **Lean:** `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique` — kind `characterization`.
- **Tier:** T1 — an elementary observation made precise and mechanized. No novelty is claimed, and no published statement of this single-pair equivalence was located; the two prior-art entries are background on leakage transformers and trace-relating compilation, not sources that state the equivalence.
- **Depth:** shallow. Forward direction: Result 2 plus `haltAgree_of_leakageDetermined`. Backward direction: choose (by `Classical.choice`) one halting target trace per public input, from any secret on which `T` halts; `ConstantTime T` makes it a halting trace for every secret on which `T` halts, `HaltAgree` matches the halting domains, and `TraceUnique T` makes it the only one. The backward direction uses neither `hCTS` nor the source-trace argument of the constructed map.
- **Plain claim:** For any source machine `S` satisfying `ConstantTime` and any target machine `T` satisfying `TraceUnique` (in particular any `Deterministic` target), the existence of some secret-independent trace transformer `leakMap` satisfying `LeakageDetermined S T leakMap` is equivalent to `ConstantTime T ∧ HaltAgree S T`.

```lean
-- lean/ToyCT/Results.lean:111-118
theorem exists_leakage_determined_iff_of_ct_traceUnique
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak)
    (T : Machine Pub Sec TgtOut TgtLeak)
    (hCTS : ConstantTime S)
    (hTgtUnique : TraceUnique T) :
    (∃ leakMap, LeakageDetermined S T leakMap) ↔
      (ConstantTime T ∧ HaltAgree S T)
```

Unfolded:

```lean
(∀ pub s₁ s₂ trS, HasTrace S pub s₁ trS ↔ HasTrace S pub s₂ trS) →
(∀ pub sec tr₁ tr₂, HasTrace T pub sec tr₁ → HasTrace T pub sec tr₂ → tr₁ = tr₂) →
((∃ leakMap : Pub → List SrcLeak → List TgtLeak,
    ∀ pub sec trT, HasTrace T pub sec trT ↔ ∃ trS, HasTrace S pub sec trS ∧ trT = leakMap pub trS) ↔
 ((∀ pub s₁ s₂ trT, HasTrace T pub s₁ trT ↔ HasTrace T pub s₂ trT) ∧
  (∀ pub sec, (∃ trS, HasTrace S pub sec trS) ↔ (∃ trT, HasTrace T pub sec trT))))
```

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
| :-- | :-- | :-- | :-- |
| `hCTS : ConstantTime S` | Requires the source machine `S` to satisfy `ConstantTime` so the forward direction of the equivalence yields `ConstantTime T`. | tight | `Toy.CT.exists_ld_iff_drop_src_ct_counterexample` (`S = T = abortOnSecret`: `TraceUnique` holds, the identity map gives `LeakageDetermined`, `ConstantTime` fails, so the `↔` fails) |
| `hTgtUnique : TraceUnique T` | Requires `T` to admit at most one halting trace per `(pub, sec)` so a functional trace map `leakMap pub` can cover `T`'s halting trace set whenever `ConstantTime T` and `HaltAgree S T` hold. | tight | `Toy.CT.exists_ld_iff_drop_tgt_traceUnique_counterexample` (`S = constOneStep`, `T = coinFlip`: `ConstantTime S` holds, the right side holds, but no function maps the single source trace `[0]` onto both `[0]` and `[1]`) |

The statements of the two counterexamples and of the two both-sides theorems cited below:

```lean
-- lean/ToyCT/Results.lean:175-178
theorem exists_ld_iff_drop_src_ct_counterexample :
    TraceUnique abortOnSecret ∧
    ¬ ((∃ leakMap, LeakageDetermined abortOnSecret abortOnSecret leakMap) ↔
        (ConstantTime abortOnSecret ∧ HaltAgree abortOnSecret abortOnSecret))
-- lean/ToyCT/Results.lean:189-192
theorem exists_ld_iff_drop_tgt_traceUnique_counterexample :
    ConstantTime constOneStep ∧
    ¬ ((∃ leakMap, LeakageDetermined constOneStep coinFlip leakMap) ↔
        (ConstantTime coinFlip ∧ HaltAgree constOneStep coinFlip))
-- lean/ToyCT/Results.lean:165-167
theorem exists_leakage_determined_iff_of_ct_traceUnique_both_sides_true :
    (∃ leakMap, LeakageDetermined branchlessSelect branchlessLowered leakMap) ∧
    (ConstantTime branchlessLowered ∧ HaltAgree branchlessSelect branchlessLowered)
-- lean/ToyCT/Results.lean:155-158
theorem exists_leakage_determined_iff_of_ct_traceUnique_both_sides_false :
    ConstantTime branchlessSelect ∧ TraceUnique branchingSelect ∧
    ¬ (∃ leakMap, LeakageDetermined branchlessSelect branchingSelect leakMap) ∧
    ¬ (ConstantTime branchingSelect ∧ HaltAgree branchlessSelect branchingSelect)
```

- **Non-vacuity witness:** `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_nonvacuous : ConstantTime branchlessSelect ∧ TraceUnique branchlessLowered`. On this pair both sides of the `↔` hold (`Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_both_sides_true`); on `(branchlessSelect, branchingSelect)`, which also satisfies both hypotheses, both sides fail (`Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_both_sides_false`), so the equivalence is not one-sided.
- **Prior art (background):** Barthe, Grégoire, Laporte, Priya, CCS 2021, DOI 10.1145/3460120.3484761; Abate et al., ESOP 2020, DOI 10.1007/978-3-030-44914-8_1.
- **Design question:** For a single compiled program pair, is existentially asserting some secret-independent leakage transformer any stronger or easier to prove than directly proving the target constant-time with matching halting domain? (Answer in this model, for trace-unique targets: neither; the two are equivalent.)

Basis: execution (Lean kernel check).
Basis: derived (modeling bridge) — for one compiled program with deterministic target semantics, a proof obligation of the form "some leakage transformer exists" is equivalent to "the target is constant-time and halts exactly when the source does". `LeakageDetermined` therefore gives proof-engineering leverage only when the map is supplied independently of the target's security argument (by the design of a pass, or by Result 3 as `liftStepLeak stepLeak`).

### Result 3: `step-leakage-simulation-implies-leakage-determined`

- **Lean:** `Toy.CT.step_leakage_sim_det_target_implies_leakage_determined` — kind `theorem`.
- **Tier:** T0 — re-derivation, in leakage-functional small-step form, of the forward-to-backward simulation argument for deterministic targets (Leroy, JAR 2009; CompCert `Smallstep.forward_to_backward_simulation`), with an anti-stuttering measure (Trieu, FCS 2018), specialized to per-step leakage maps; a special case of the constant-time simulations of Barthe, Grégoire and Laporte (CSF 2018).
- **Depth:** substantive. Forward direction: stitch the target runs matched to each source step (`Steps.append`). Backward direction: on a deterministic target every halting run extends every run prefix from the same start (`Toy.CT.Deterministic.halting_run_extends`); a nested induction on the remaining target trace length and then on the source measure pulls a halting target run back to a halting source run, using `Safe S` at each reachable source configuration.
- **Plain claim:** For all small-step machines `S` and `T` sharing public input, secret input, and output types, any secret-independent step leakage map `stepLeak : Pub -> SrcLeak -> List TgtLeak`, source anti-stuttering measure `measure : S.State -> Nat`, and relation `R`, if forward step simulation `StepLeakSim S T stepLeak measure R` holds together with `HasInit S`, `Safe S`, and transition determinism `Deterministic T`, then `LeakageDetermined S T (liftStepLeak stepLeak)` holds for the homomorphic trace transformer `liftStepLeak stepLeak`.

```lean
-- lean/ToyCT/Results.lean:371-382
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
    LeakageDetermined S T (liftStepLeak stepLeak)
```

Unfolded (prose):

```text
((∀ pub sec s₀, S.init pub sec s₀ → ∃ t₀, T.init pub sec t₀ ∧ R pub sec s₀ t₀) ∧
 (∀ pub sec s t out, R pub sec s t → S.halted s out → T.halted t out) ∧
 (∀ pub sec s ls s' t, R pub sec s t → S.step s ls s' →
    (∃ t', Steps T t (stepLeak pub ls) t' ∧ R pub sec s' t') ∧
    (stepLeak pub ls = [] → measure s' < measure s))) →
(∀ pub sec, ∃ s₀, S.init pub sec s₀) →
(∀ pub sec s, Reachable S pub sec s → (∃ out, S.halted s out) ∨ (∃ l s', S.step s l s')) →
((∀ pub sec t₁ t₂, T.init pub sec t₁ → T.init pub sec t₂ → t₁ = t₂) ∧
 (∀ t l₁ t₁ l₂ t₂, T.step t l₁ t₁ → T.step t l₂ t₂ → l₁ = l₂ ∧ t₁ = t₂) ∧
 (∀ t out l t', T.halted t out → ¬ T.step t l t')) →
∀ pub sec trT, HasTrace T pub sec trT ↔
  ∃ trS, HasTrace S pub sec trS ∧ trT = liftStepLeak stepLeak pub trS
```

| Hypothesis | Purpose | Tightness | Counterexamples (all other hypotheses hold, conclusion fails) |
| :-- | :-- | :-- | :-- |
| `hSim : StepLeakSim S T stepLeak measure R` | Provides the forward step-wise simulation relation `R` matching initial and halted configurations and mapping each source step's leakage `ls` to `stepLeak pub ls` target steps, with `measure s' < measure s` whenever `stepLeak pub ls = []`. | tight | `Toy.CT.step_sim_drop_sim_counterexample` (whole simulation dropped: `branchlessSelect` to `branchingSelect`); `Toy.CT.unmeasured_stutter_sim_breaks_leakage_determined` (only the measure clause dropped: `UnmeasuredStepLeakSim silentLoopSource haltIfTrue (fun _ _ => []) (fun _ _ _ _ => True)`) |
| `hSrcInit : HasInit S` | Guarantees that every `(pub, sec)` input has at least one initial configuration in `S` so halting executions of deterministic `T` pull back to `S`. | tight | `Toy.CT.step_sim_drop_src_init_counterexample` (`emptyInitMachine` to `haltIfTrue`) |
| `hSrcSafe : Safe S` | Guarantees progress (either halting or stepping) at every reachable configuration of `S` so a stuck source configuration cannot vacuously simulate a halting target configuration. | tight | `Toy.CT.step_sim_drop_src_safe_counterexample` (`stuckMachine` to `haltIfTrue`) |
| `hTgtDet : Deterministic T` | Guarantees transition determinism of `T` (unique initial state, unique step leakage and next state, no transitions from halted states) so forward simulation uniquely pins down every halting execution of `T`. | tight | one per sub-clause: `Toy.CT.nondeterministic_target_sim_breaks_leakage_determined` (event half of `step_det`; `nondetSecretBranchTarget`), `Toy.CT.step_sim_drop_tgt_init_det_counterexample` (`init_det`; `secretTwoInitTarget`), `Toy.CT.step_sim_drop_tgt_step_state_det_counterexample` (successor half of `step_det`; `secretForkTarget`), `Toy.CT.step_sim_drop_tgt_halted_nostep_counterexample` (`halted_nostep`; `secretHaltOrStepTarget`). The three `step_sim_drop_tgt_*` theorems state the kept sub-clauses as conjuncts and negate only the dropped one. `nondeterministic_target_sim_breaks_leakage_determined` states only `¬ Deterministic nondetSecretBranchTarget`; that `init_det`, the successor half of `step_det`, and `halted_nostep` hold for `nondetSecretBranchTarget` (so that only the event half fails) is read off its quoted definition and is not part of the theorem's statement. |

Every listed counterexample also has `ConstantTime S` and `¬ ConstantTime T`, so each hypothesis is necessary for constant-time preservation and not only for `LeakageDetermined`. Neither `Deterministic S`, `Terminates S`, nor `OutputDeterministic T` is assumed; `Toy.CT.hasInit_and_safe_of_det_terminates` derives `HasInit S ∧ Safe S` from `Deterministic S ∧ Terminates S`. The statements of the counterexamples:

```lean
-- lean/ToyCT/Results.lean:404-410
theorem step_sim_drop_sim_counterexample :
    HasInit branchlessSelect ∧ Safe branchlessSelect ∧ ConstantTime branchlessSelect ∧
    Deterministic branchingSelect ∧
    ¬ LeakageDetermined branchlessSelect branchingSelect (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime branchingSelect
-- lean/ToyCT/Results.lean:477-486
theorem unmeasured_stutter_sim_breaks_leakage_determined :
    UnmeasuredStepLeakSim silentLoopSource haltIfTrue (fun _ _ => []) (fun _ _ _ _ => True) ∧
    HasInit silentLoopSource ∧ Safe silentLoopSource ∧ Deterministic silentLoopSource ∧
    ConstantTime silentLoopSource ∧ Deterministic haltIfTrue ∧
    ¬ LeakageDetermined silentLoopSource haltIfTrue (liftStepLeak (fun _ _ => [])) ∧
    ¬ ConstantTime haltIfTrue
-- lean/ToyCT/Results.lean:422-429
theorem step_sim_drop_src_init_counterexample :
    StepLeakSim emptyInitMachine haltIfTrue (fun _ l => [l]) (fun _ => 0) (fun _ _ _ _ => False) ∧
    Safe emptyInitMachine ∧ ConstantTime emptyInitMachine ∧ Deterministic haltIfTrue ∧
    ¬ LeakageDetermined emptyInitMachine haltIfTrue (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime haltIfTrue
-- lean/ToyCT/Results.lean:450-457
theorem step_sim_drop_src_safe_counterexample :
    StepLeakSim stuckMachine haltIfTrue (fun _ l => [l]) (fun _ => 0) (fun _ _ _ _ => True) ∧
    HasInit stuckMachine ∧ ConstantTime stuckMachine ∧ Deterministic haltIfTrue ∧
    ¬ LeakageDetermined stuckMachine haltIfTrue (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime haltIfTrue
-- lean/ToyCT/Results.lean:548-560
theorem step_sim_drop_tgt_init_det_counterexample :
    StepLeakSim constOneStep secretTwoInitTarget (fun _ l => [l]) (fun _ => 0)
      (fun _ _ s t => (s = false ∧ t = TwoInitState.a) ∨ (s = true ∧ t = TwoInitState.fin)) ∧
    HasInit constOneStep ∧ Safe constOneStep ∧ ConstantTime constOneStep ∧
    (∀ s l₁ s₁ l₂ s₂, secretTwoInitTarget.step s l₁ s₁ → secretTwoInitTarget.step s l₂ s₂ →
      l₁ = l₂ ∧ s₁ = s₂) ∧
    (∀ s out l s', secretTwoInitTarget.halted s out → ¬ secretTwoInitTarget.step s l s') ∧
    ¬ (∀ pub sec s₁ s₂, secretTwoInitTarget.init pub sec s₁ →
        secretTwoInitTarget.init pub sec s₂ → s₁ = s₂) ∧
    ¬ LeakageDetermined constOneStep secretTwoInitTarget (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime secretTwoInitTarget
-- lean/ToyCT/Results.lean:613-628
theorem step_sim_drop_tgt_step_state_det_counterexample :
    StepLeakSim constOneStep secretForkTarget (fun _ l => [l]) (fun _ => 0)
      (fun _ sec s t =>
        (s = false ∧ t = SecretForkState.start sec) ∨ (s = true ∧ t = SecretForkState.a)) ∧
    HasInit constOneStep ∧ Safe constOneStep ∧ ConstantTime constOneStep ∧
    (∀ pub sec s₁ s₂, secretForkTarget.init pub sec s₁ →
      secretForkTarget.init pub sec s₂ → s₁ = s₂) ∧
    (∀ s l₁ s₁ l₂ s₂, secretForkTarget.step s l₁ s₁ →
      secretForkTarget.step s l₂ s₂ → l₁ = l₂) ∧
    (∀ s out l s', secretForkTarget.halted s out → ¬ secretForkTarget.step s l s') ∧
    ¬ (∀ s l₁ s₁ l₂ s₂, secretForkTarget.step s l₁ s₁ →
        secretForkTarget.step s l₂ s₂ → s₁ = s₂) ∧
    ¬ LeakageDetermined constOneStep secretForkTarget (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime secretForkTarget
-- lean/ToyCT/Results.lean:688-702
theorem step_sim_drop_tgt_halted_nostep_counterexample :
    StepLeakSim trivialHaltedMachine secretHaltOrStepTarget (fun _ l => [l]) (fun _ => 0)
      (fun _ sec _ t => t = (false, sec)) ∧
    HasInit trivialHaltedMachine ∧ Safe trivialHaltedMachine ∧ ConstantTime trivialHaltedMachine ∧
    (∀ pub sec s₁ s₂, secretHaltOrStepTarget.init pub sec s₁ →
      secretHaltOrStepTarget.init pub sec s₂ → s₁ = s₂) ∧
    (∀ s l₁ s₁ l₂ s₂, secretHaltOrStepTarget.step s l₁ s₁ →
      secretHaltOrStepTarget.step s l₂ s₂ → l₁ = l₂ ∧ s₁ = s₂) ∧
    ¬ (∀ s out l s', secretHaltOrStepTarget.halted s out →
        ¬ secretHaltOrStepTarget.step s l s') ∧
    ¬ LeakageDetermined trivialHaltedMachine secretHaltOrStepTarget
        (liftStepLeak (fun _ l => [l])) ∧
    ¬ ConstantTime secretHaltOrStepTarget
```

(`nondeterministic_target_sim_breaks_leakage_determined` is quoted under Result 4b.)

- **Non-vacuity witness:** `Toy.CT.step_leakage_sim_det_target_implies_leakage_determined_nonvacuous : StepLeakSim branchlessWithNop branchlessLowered nopToLoweredStepLeak nopSelectMeasure nopToLoweredRel ∧ HasInit branchlessWithNop ∧ Safe branchlessWithNop ∧ Deterministic branchlessLowered`. It exercises both an eliminated (stuttering) source step (PC `0` maps to `[]`, measure `2` to `1`) and instruction expansion (PC `1` maps to `[10, 11]`).
- **Output-free generalization (proved).** The conclusion does not use output agreement. `OutputFreeStepLeakSim` is `StepLeakSim` with separate output types and a weaker halting clause:

```lean
-- lean/ToyCT/Results.lean:216-226
structure OutputFreeStepLeakSim {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak) (T : Machine Pub Sec TgtOut TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak) (measure : S.State → Nat)
    (R : Pub → Sec → S.State → T.State → Prop) : Prop where
  init_sim : ∀ pub sec s₀, S.init pub sec s₀ → ∃ t₀, T.init pub sec t₀ ∧ R pub sec s₀ t₀
  halted_sim : ∀ pub sec s t out, R pub sec s t → S.halted s out → ∃ out', T.halted t out'
  step_sim : ∀ pub sec s ls s' t, R pub sec s t → S.step s ls s' →
    (∃ t', Steps T t (stepLeak pub ls) t' ∧ R pub sec s' t') ∧
    (stepLeak pub ls = [] → measure s' < measure s)

-- lean/ToyCT/Results.lean:229-234
theorem StepLeakSim.toOutputFree {Pub Sec Out SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec Out SrcLeak} {T : Machine Pub Sec Out TgtLeak}
    {stepLeak : Pub → SrcLeak → List TgtLeak} {measure : S.State → Nat}
    {R : Pub → Sec → S.State → T.State → Prop}
    (h : StepLeakSim S T stepLeak measure R) : OutputFreeStepLeakSim S T stepLeak measure R

-- lean/ToyCT/Results.lean:337-348
theorem outputFree_step_leakage_sim_det_target_implies_leakage_determined
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak) (T : Machine Pub Sec TgtOut TgtLeak)
    (stepLeak : Pub → SrcLeak → List TgtLeak) (measure : S.State → Nat)
    (R : Pub → Sec → S.State → T.State → Prop)
    (hSim : OutputFreeStepLeakSim S T stepLeak measure R)
    (hSrcInit : HasInit S) (hSrcSafe : Safe S) (hTgtDet : Deterministic T) :
    LeakageDetermined S T (liftStepLeak stepLeak)
```

  Result 3 is proved as the composition of these two theorems.
- **Related proved fact (cited in the non-claims):**

```lean
-- lean/ToyCT/Results.lean:514-524
theorem option_stutter_sim_breaks_ct :
    OptionStepLeakSim twoStepConstSource secretStutterTarget
      (fun _ l => [l]) twoStepMeasure optionStutterRel ∧
    HasInit twoStepConstSource ∧ Safe twoStepConstSource ∧ Deterministic twoStepConstSource ∧
    Terminates twoStepConstSource ∧ ConstantTime twoStepConstSource ∧
    Deterministic secretStutterTarget ∧
    (∀ f, ¬ LeakageDetermined twoStepConstSource secretStutterTarget f) ∧
    ¬ ConstantTime secretStutterTarget
```

- **Prior art:** Leroy, "A Formally Verified Compiler Back-end," JAR 43(4), pp. 363–446, 2009, DOI 10.1007/s10817-009-9155-4, and CompCert `common/Smallstep.v`, `Lemma forward_to_backward_simulation: forall L1 L2, forward_simulation L1 L2 -> receptive L1 -> determinate L2 -> backward_simulation L1 L2` (lines 1863–1866 at commit `14d616046360a0b2611ebdfc2f98368af402e1f7`); Trieu, "A Study on the Preservation of Cryptographic Constant-Time Security in the CompCert Compiler," FCS 2018 (anti-stuttering measure; silent infinite loop compiled to skip); Barthe, Grégoire, Laporte, CSF 2018, DOI 10.1109/CSF.2018.00031; Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, Trieu, "Formal Verification of a Constant-Time Preserving C Compiler," PACMPL 4(POPL), Article 7, 2020, DOI 10.1145/3371075; Barthe et al., ePrint 2026/2510; Desharnais-Schäfer, "A Generic Framework for Verified Compilers," AFP entry `VeriComp`, 2020; Murray, Sison, Pierzchalski, Rizkallah, "Compositional Security-Preserving Refinement for Concurrent Imperative Programs," AFP entry `Dependent_SIFUM_Refinement`, 2016; Sison and Murray, ITP 2019, LIPIcs 141, 27:1–27:19, DOI 10.4230/LIPIcs.ITP.2019.27.
- **Design question:** Which local, step-by-step forward simulation condition on deterministic targets (accounting for eliminated/stuttering steps and expanded instructions) suffices to construct an explicit trace transformer `liftStepLeak stepLeak` satisfying `LeakageDetermined` without proving a backward simulation by hand? (Answer in this model: `StepLeakSim` plus `HasInit S`, `Safe S`, `Deterministic T`, each necessary.)

Basis: execution (Lean kernel check).
Basis: derived (modeling bridge) — a compiler-pass correctness proof by forward simulation into a deterministic target semantics, in which each source instruction is matched by target instructions whose leakage is a fixed function of the public input and the source instruction's leakage, and eliminated instructions decrease a measure, yields for that program the trace map `liftStepLeak stepLeak` and, with Result 2, constant-time preservation. The bridge assumes the pass's simulation diagram has this leakage-functional shape (gap 5) and that the real target semantics is deterministic in the sense of `Deterministic`.

### Result 4a: `secret-dependent-leakage-map-breaks-ct`

- **Lean:** `Toy.CT.secret_dependent_leak_map_breaks_ct` — kind `counterexample`.
- **Tier:** T0 — direct corollary of Result 1, the contrapositive of Result 2, and the general lemma `Toy.CT.exists_secretDependentLeakageDetermined_of_traceUnique_haltAgree`.
- **Depth:** shallow.
- **Plain claim:** Concretely, for the program-counter selector machines `branchlessSelect` and `branchingSelect`: both are transition-deterministic and terminating; `branchlessSelect` satisfies `ConstantTime`; the pair satisfies `FunctionallyCorrect`; the pair satisfies `SecretDependentLeakageDetermined` under the secret-reading trace map `secretBranchLeakMap`; no secret-independent trace map `f` satisfies `LeakageDetermined branchlessSelect branchingSelect f`; and `branchingSelect` violates `ConstantTime`. (The general phenomenon is a separate lemma: letting the map read `Sec` makes `SecretDependentLeakageDetermined` satisfiable for every `TraceUnique` target whose halting domain agrees with the source's, `Toy.CT.exists_secretDependentLeakageDetermined_of_traceUnique_haltAgree`; it is `SecretDependentLeakageDetermined`, not `LeakageDetermined`, that becomes trivially satisfiable.)

```lean
-- lean/ToyCT/Results.lean:747-756
theorem secret_dependent_leak_map_breaks_ct :
    Deterministic branchlessSelect ∧
    Terminates branchlessSelect ∧
    Deterministic branchingSelect ∧
    Terminates branchingSelect ∧
    ConstantTime branchlessSelect ∧
    FunctionallyCorrect branchlessSelect branchingSelect ∧
    SecretDependentLeakageDetermined branchlessSelect branchingSelect secretBranchLeakMap ∧
    (∀ f, ¬ LeakageDetermined branchlessSelect branchingSelect f) ∧
    ¬ ConstantTime branchingSelect
```

Unfolded key clauses (with `secretBranchLeakMap _ sec [0] = [0, if sec then 1 else 2]`) (prose):

```text
  (∀ pub sec trT, HasTrace branchingSelect pub sec trT ↔
       ∃ trS, HasTrace branchlessSelect pub sec trS ∧ trT = secretBranchLeakMap pub sec trS)
∧ (∀ f : (Nat × Nat) → List Nat → List Nat, ¬ ∀ pub sec trT,
       HasTrace branchingSelect pub sec trT ↔
       ∃ trS, HasTrace branchlessSelect pub sec trS ∧ trT = f pub trS)
∧ ¬ (∀ pub s₁ s₂ tr, HasTrace branchingSelect pub s₁ tr ↔ HasTrace branchingSelect pub s₂ tr)
```

- **Hypothesis ledger:** none (unconditional statement about concrete machines). This theorem is also the `hLD` counterexample of Result 2.
- **Non-vacuity witness:** the triple `(branchlessSelect, branchingSelect, secretBranchLeakMap)` (`Toy.CT.secret_dependent_leak_map_breaks_ct`).
- **Positive control:** `Toy.CT.branchless_lowering_preserves_ct` (quoted under Result 1): with a secret-independent map and a constant-time target, `LeakageDetermined` holds.
- **Related proved facts:**

```lean
-- lean/ToyCT/Defs.lean:502-508
theorem exists_secretDependentLeakageDetermined_of_traceUnique_haltAgree
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    {S : Machine Pub Sec SrcOut SrcLeak} {T : Machine Pub Sec TgtOut TgtLeak}
    (hUniqueT : TraceUnique T) (hHalt : HaltAgree S T) :
    ∃ m, SecretDependentLeakageDetermined S T m
-- lean/ToyCT/Defs.lean:490-496
theorem secretDependentLeakageDetermined_const_sec_iff
    {Pub Sec SrcOut TgtOut SrcLeak TgtLeak : Type}
    (S : Machine Pub Sec SrcOut SrcLeak) (T : Machine Pub Sec TgtOut TgtLeak)
    (leakMap : Pub → List SrcLeak → List TgtLeak) :
    SecretDependentLeakageDetermined S T (fun pub _ trS => leakMap pub trS) ↔
      LeakageDetermined S T leakMap
```

- **Prior art:** Barthe, Grégoire, Laporte, CSF 2018, DOI 10.1109/CSF.2018.00031; Barthe, Grégoire, Laporte, Priya, CCS 2021, DOI 10.1145/3460120.3484761.
- **Design question:** What happens to `LeakageDetermined` when the trace transformer is allowed to read `Sec` — does it remain a meaningful restriction or become trivially satisfiable on deterministic targets? (Answer: it becomes trivially satisfiable for every trace-unique target with matching halting domain.)

Basis: execution (Lean kernel check).
Basis: derived (modeling bridge) — a "leakage transformer" for a compiler pass certifies nothing about constant time unless it is independent of secrets: by the general lemma, any compiled program with deterministic (trace-unique) semantics and the source's halting domain admits a secret-reading transformer.

### Result 4b: `nondeterministic-target-breaks-step-simulation-ct`

- **Lean:** `Toy.CT.nondeterministic_target_sim_breaks_leakage_determined` — kind `counterexample`.
- **Tier:** T0 — re-derivation of the necessity of target determinacy in the forward-to-backward simulation argument (Leroy, JAR 2009; CompCert `Smallstep.forward_to_backward_simulation`, which assumes `determinate L2`).
- **Depth:** shallow.
- **Plain claim:** For the transition-deterministic, terminating, safe, constant-time source machine `constOneStep` and the terminating, nondeterministic target machine `nondetSecretBranchTarget` (satisfying `¬ Deterministic nondetSecretBranchTarget`), forward simulation `StepLeakSim` holds under the secret-independent identity step-leakage map `fun _ l => [l]` and zero measure together with `FunctionallyCorrect`, yet both `LeakageDetermined constOneStep nondetSecretBranchTarget (liftStepLeak (fun _ l => [l]))` and `ConstantTime nondetSecretBranchTarget` fail.

```lean
-- lean/ToyCT/Results.lean:781-794
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
    ¬ ConstantTime nondetSecretBranchTarget
```

Unfolded (prose) key clauses: the target's halting traces are `{[0]}` for `sec = false` and `{[0], [1]}` for `sec = true`, while the source's are `{[0]}` for both, so

```text
  ¬ (∀ pub sec trT, HasTrace nondetSecretBranchTarget pub sec trT ↔
       ∃ trS, HasTrace constOneStep pub sec trS ∧ trT = liftStepLeak (fun _ l => [l]) pub trS)
∧ ¬ (∀ pub s₁ s₂ tr, HasTrace nondetSecretBranchTarget pub s₁ tr ↔
                     HasTrace nondetSecretBranchTarget pub s₂ tr)
```

- **Hypothesis ledger:** none (unconditional). Result 3 also lists this theorem as the `hTgtDet` counterexample for the event half of `Deterministic.step_det`; the theorem itself states only `¬ Deterministic nondetSecretBranchTarget`, and that the other sub-clauses of `Deterministic` hold for this target is read off its quoted definition.
- **Non-vacuity witness:** `(constOneStep, nondetSecretBranchTarget, constNondetRel)`: the source emits `[0]` on every secret; the target emits `[0]` on `sec = false` and, on `sec = true`, either `[0]` (the run the forward simulation follows) or `[1]` (breaking `LeakageDetermined` and `ConstantTime`), always returning `()`.
- **Positive control:** `Toy.CT.determinized_target_sim_positive_control` — removing the `l = 1` transition gives `determinizedSecretBranchTarget` on the same state space, which with the same relation `constNondetRel` satisfies:

```lean
-- lean/ToyCT/Results.lean:864-871
theorem determinized_target_sim_positive_control :
    StepLeakSim constOneStep determinizedSecretBranchTarget
      (fun _ l => [l]) (fun _ => 0) constNondetRel ∧
    HasInit constOneStep ∧ Safe constOneStep ∧
    Deterministic determinizedSecretBranchTarget ∧
    LeakageDetermined constOneStep determinizedSecretBranchTarget (liftStepLeak (fun _ l => [l])) ∧
    ConstantTime determinizedSecretBranchTarget
```

- **Prior art:** Leroy, JAR 2009, DOI 10.1007/s10817-009-9155-4, and CompCert `common/Smallstep.v` (`forward_to_backward_simulation`, `determinate`; quoted in `## Applicability`); Barthe, Grégoire, Laporte, CSF 2018, DOI 10.1109/CSF.2018.00031.
- **Design question:** Does a forward constant-time step simulation suffice when the target IR or assembly semantics is not transition-deterministic? (Answer in this model: no.)

Basis: execution (Lean kernel check).
Basis: derived (modeling bridge) — a forward simulation proof says nothing about target behaviors it does not follow; if the real target semantics has nondeterministic transitions not covered by the simulation, a forward simulation does not establish constant-time preservation. The concrete nondeterminism here is hand-built and secret-dependent; it does not model a specific real source of nondeterminism.

### Result 5: `leakage-determined-composes`

- **Lean:** `Toy.CT.leakage_determined_comp` — kind `theorem`, labeled a **reference point**.
- **Tier:** T0 — reference-point re-derivation of vertical composition of trace-image transformers (Barthe et al., CCS 2021; Barthe et al., POPL 2020; Leroy, JAR 2009).
- **Depth:** definitional (rewrite with `h₂₃`, then with `h₁₂`).
- **Plain claim:** For all small-step machines `M1`, `M2`, and `M3` sharing public and secret input types (with possibly distinct output and leakage types) and secret-independent trace transformers `f : Pub -> List Leak1 -> List Leak2` and `g : Pub -> List Leak2 -> List Leak3`, if `LeakageDetermined M1 M2 f` and `LeakageDetermined M2 M3 g` hold, then `LeakageDetermined M1 M3 (composeLeakMap f g)` holds for the composed transformer `composeLeakMap f g := fun pub tr1 => g pub (f pub tr1)`.

```lean
-- lean/ToyCT/Results.lean:907-916
theorem leakage_determined_comp
    {Pub Sec Out₁ Out₂ Out₃ Leak₁ Leak₂ Leak₃ : Type}
    (M₁ : Machine Pub Sec Out₁ Leak₁)
    (M₂ : Machine Pub Sec Out₂ Leak₂)
    (M₃ : Machine Pub Sec Out₃ Leak₃)
    (f : Pub → List Leak₁ → List Leak₂)
    (g : Pub → List Leak₂ → List Leak₃)
    (h₁₂ : LeakageDetermined M₁ M₂ f)
    (h₂₃ : LeakageDetermined M₂ M₃ g) :
    LeakageDetermined M₁ M₃ (composeLeakMap f g)
```

Unfolded:

```lean
(∀ pub sec tr₂, HasTrace M₂ pub sec tr₂ ↔ ∃ tr₁, HasTrace M₁ pub sec tr₁ ∧ tr₂ = f pub tr₁) →
(∀ pub sec tr₃, HasTrace M₃ pub sec tr₃ ↔ ∃ tr₂, HasTrace M₂ pub sec tr₂ ∧ tr₃ = g pub tr₂) →
(∀ pub sec tr₃, HasTrace M₃ pub sec tr₃ ↔ ∃ tr₁, HasTrace M₁ pub sec tr₁ ∧ tr₃ = g pub (f pub tr₁))
```

| Hypothesis | Purpose | Tightness | Counterexample (all other hypotheses hold, conclusion fails) |
| :-- | :-- | :-- | :-- |
| `h₁₂ : LeakageDetermined M₁ M₂ f` | Establishes that the first pass from `M1` to `M2` is `LeakageDetermined` via secret-independent trace transformer `f`. | tight | `Toy.CT.leakage_determined_comp_drop_first_counterexample` (`M₁ = branchlessSelect`, `M₂ = M₃ = branchingSelect`, `f = g = id`) |
| `h₂₃ : LeakageDetermined M₂ M₃ g` | Establishes that the second pass from `M2` to `M3` is `LeakageDetermined` via secret-independent trace transformer `g`. | tight | `Toy.CT.leakage_determined_comp_drop_second_counterexample` (`M₁ = M₂ = branchlessSelect`, `M₃ = branchingSelect`, `f = g = id`) |

```lean
-- lean/ToyCT/Results.lean:947-950
theorem leakage_determined_comp_drop_first_counterexample :
    LeakageDetermined branchingSelect branchingSelect (fun _ tr => tr) ∧
    ¬ LeakageDetermined branchlessSelect branchingSelect
        (composeLeakMap (fun _ tr => tr) (fun _ tr => tr))
-- lean/ToyCT/Results.lean:957-960
theorem leakage_determined_comp_drop_second_counterexample :
    LeakageDetermined branchlessSelect branchlessSelect (fun _ tr => tr) ∧
    ¬ LeakageDetermined branchlessSelect branchingSelect
        (composeLeakMap (fun _ tr => tr) (fun _ tr => tr))
```

- **Non-vacuity witness:** `Toy.CT.leakage_determined_comp_nonvacuous : LeakageDetermined branchlessSelect branchlessLowered selectToLoweredLeakMap ∧ LeakageDetermined branchlessLowered branchlessEncoded loweredToEncodedLeakMap` — instruction expansion (`[0]` to `[10, 11]`) followed by public-input-dependent relocation (`[10, 11]` to `[100 + pub.1 % 2, 101 + pub.1 % 2]`).
- **Prior art:** Barthe, Grégoire, Laporte, Priya, CCS 2021, DOI 10.1145/3460120.3484761; Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, Trieu, PACMPL 4(POPL), 2020, DOI 10.1145/3371075; Leroy, JAR 2009, DOI 10.1007/s10817-009-9155-4.
- **Design question:** Reference point: how do trace-level `LeakageDetermined` witnesses compose across sequential passes with distinct leakage alphabets, and how does per-pass trace composition differ from composing forward `StepLeakSim` diagrams directly?

Basis: execution (Lean kernel check).
Basis: derived (modeling bridge) — per-pass leakage transformers for a pipeline of compiler passes compose into a transformer for the whole pipeline (for one program); combined with Result 2 this transfers constant time end to end. It gives no help in obtaining the per-pass transformers.

## Boundaries

### Non-claims

For each result, what it does **not** show (verbatim from `results.json`):

**Result 1 (`functional-correctness-does-not-preserve-ct`).**

- Does not claim that every functionally correct compilation breaks ConstantTime. Toy.CT.branchless_lowering_preserves_ct exhibits one functionally correct compilation of the same source (branchlessSelect to branchlessLowered) that also satisfies LeakageDetermined and preserves ConstantTime; that theorem is a single instance. The general sufficient condition is Result 2 (Toy.CT.leakage_determined_preserves_ct), in which LeakageDetermined alone suffices and FunctionallyCorrect plays no role.
- The two machines are hand-constructed. The result does not show that any particular compiler performs this transformation; for empirical evidence see the cited compiler studies.
- branchingSelect executes exactly two steps for every secret (Toy.CT.branchingSelect_trace_length). The violation is of the program-counter (control-flow) leakage model; under an observer that sees only the number of steps (execution time in this model), the target is indistinguishable across secrets.
- FunctionallyCorrect here is two-sided equality of halting-output sets: for every input and output, S has a halting run returning that output iff T has one. It implies one-sided inclusion of halting outputs, but it constrains complete halting runs only: on an input where neither machine halts it imposes no condition, even when both machines are deterministic. For example, silentLoopSource loops forever and is Safe (Toy.CT.safe_nonterminating_pos_example), while stuckMachine is stuck at its unique initial configuration and is not Safe (Toy.CT.safe_neg_example); both have halted := False, so FunctionallyCorrect holds between them trivially (read off the quoted definitions; not stated as a separate Lean theorem). FunctionallyCorrect is therefore not a strengthening of CompCert-style backward simulation, which for a safe source also rules out a stuck target; this comparison is unproved commentary, and no formal relation to backward simulation is proved here. The counterexample pair satisfies Deterministic and Terminates (conjuncts of the theorem), hence HasInit and Safe (Toy.CT.hasInit_and_safe_of_det_terminates), so the failure of ConstantTime does not rely on stuck runs or on inputs without a halting run.
- Models instruction-address (program-counter) leakage in an abstract small-step machine rather than cycle-accurate microarchitectural, speculative, or cache state (for speculative constant-time preservation failures in compilers, see Arranz Olmos et al., POPL 2025).
- All results relate one source machine to one target machine. No result quantifies over a compiler (a map from all source programs to target programs); applying them to a compiler pass means discharging the hypotheses for each program the pass produces.

**Result 2 (`leakage-determined-preserves-ct`).**

- For a single source/target pair whose source is ConstantTime and whose target is TraceUnique (for example Deterministic), the existence of some secret-independent leakMap with LeakageDetermined S T leakMap is equivalent to the target being ConstantTime and halting on exactly the same inputs (Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique). LeakageDetermined is therefore not an easier per-program obligation than proving the target constant-time; its value lies in a leakMap supplied independently of the security argument (for example by liftStepLeak from Result 3, or by a compiler-produced leakage transformer).
- On TraceUnique (for example Deterministic) sources, LeakageDetermined is sufficient but not minimal: one-way inclusion of target traces in the image plus 'the target halts whenever the source halts' (WeakLeakageDetermined) already suffices for preservation (Toy.CT.weakLeakageDetermined_preserves_ct_of_traceUnique), whereas without TraceUnique S that one-way weakening fails (Toy.CT.weakLeakageDetermined_fails_without_traceUnique).
- Terminates asserts only that some run halts. For nondeterministic machines, ConstantTime (and LeakageDetermined) place no constraint on diverging runs even when Terminates holds (example: haltOrLeak, Toy.CT.terminates_and_constantTime_unconstrained_diverging_branch); only Deterministic M ∧ Terminates M ensures that every run halts.
- When the source never halts on a public input, LeakageDetermined forces the target never to halt there, and the conclusion ConstantTime T holds vacuously on that input.
- ConstantTime quantifies over complete halting executions only. A machine with no halting execution on some public input is constant-time on that input whatever it leaks before diverging (example: leakyLoop, Toy.CT.leakyLoop_constantTime_despite_diverging_step_leak). This differs from the prefix-based definition of Barthe, Gregoire and Laporte (CSF 2018).
- ConstantTime is termination-sensitive and is not preserved by trace-inclusion refinement: a target whose halting traces are a subset of a constant-time source's can fail to be constant-time (example: haltIfTrue refining allHalt, Toy.CT.constantTime_not_refinement_closed).
- ConstantTime equates halting trace sets possibilistically without weighting transition probabilities; single-trace-per-input behavior is captured separately by TraceUnique (example: coinFlip satisfies ConstantTime and violates TraceUnique).
- Does not establish FunctionallyCorrect between S and T: SrcOut and TgtOut need not even coincide, because ConstantTime constrains halting leakage traces rather than return values.
- Does not guarantee freedom from physical or speculative hardware timing channels (variable-latency arithmetic, speculative execution, cache contention) that are not represented in TgtLeak (see Arranz Olmos et al., POPL 2025).
- LeakageDetermined is a sufficient condition for preserving ConstantTime, not a necessary condition for T to be ConstantTime (for example, Partial Control-Flow Linearization compiles a non-constant-time source into a constant-time target; Knothe and Bringmann, ITP 2025).

**Result 2b (`single-pair-leakage-determined-characterization`).**

- All results relate one source machine to one target machine. No result quantifies over a compiler (a map from all source programs to target programs); applying them to a compiler pass means discharging the hypotheses for each program the pass produces.
- The backward implication (ConstantTime T ∧ HaltAgree S T -> ∃ leakMap, LeakageDetermined S T leakMap) constructs leakMap non-constructively via Classical.choice from T's own halting traces and ignores its source-trace argument; it does not produce a computable compiler-level leakage transformer.
- Without TraceUnique T, ConstantTime T ∧ HaltAgree S T no longer implies ∃ leakMap, LeakageDetermined S T leakMap when S has fewer traces per input than T (Toy.CT.exists_ld_iff_drop_tgt_traceUnique_counterexample).
- No novelty is claimed, and no published statement of this single-pair equivalence was located; it is recorded as an elementary observation (tier T1), and the prior_art entries are background on leakage transformers and trace-relating compilation, not sources that state the equivalence.

**Result 3 (`step-leakage-simulation-implies-leakage-determined`).**

- StepLeakSim is a leakage-functional special case of the constant-time simulations of Barthe, Gregoire and Laporte (CSF 2018), which allow the number of target steps to depend on source and target configurations and establish security through a relational invariant. Passes that need state-dependent step counts are not covered by Result 3, and this package does not formalize the more general condition.
- Covers passes whose step-level leakage map stepLeak : Pub -> SrcLeak -> List TgtLeak fixes target step leakages (including 0-step stuttering [] and multi-step expansion) from (pub, ls) alone; non-local pass transformations such as instruction scheduling or loop reordering that permute leakage events across non-adjacent steps need not factor through liftStepLeak and must establish LeakageDetermined directly.
- In a single-run forward option simulation without a relational pair invariant across secrets (OptionStepLeakSim), allowing the step-versus-stutter choice to depend on internal configurations breaks both LeakageDetermined and ConstantTime (Toy.CT.option_stutter_sim_breaks_ct); whether a state-dependent step count leaks in general depends on whether it depends on secrets, which Barthe, Gregoire and Laporte (CSF 2018) handle via a relational 2-simulation rather than (pub, ls) functionality.
- Each of HasInit S, Safe S, and the stuttering measure is also necessary for constant-time preservation: see Toy.CT.step_sim_drop_src_init_counterexample, Toy.CT.step_sim_drop_src_safe_counterexample, and Toy.CT.unmeasured_stutter_sim_breaks_leakage_determined.
- Result 3 is the leakage instance of the forward-to-backward simulation argument for deterministic targets (Leroy 2009; CompCert Smallstep.forward_to_backward_simulation); it is not a new proof technique.
- Output agreement is not used by the conclusion. StepLeakSim requires related halted configurations to return the same output (halted_sim : S.halted s out -> T.halted t out) over a shared Out type, but the proved generalization Toy.CT.outputFree_step_leakage_sim_det_target_implies_leakage_determined reaches the same LeakageDetermined conclusion for distinct source and target output types under OutputFreeStepLeakSim, whose halted_sim only requires the target to halt with some output whenever the related source configuration halts (every StepLeakSim is an OutputFreeStepLeakSim: Toy.CT.StepLeakSim.toOutputFree). Result 3 therefore says nothing about preservation of return values.

**Result 4a (`secret-dependent-leakage-map-breaks-ct`).**

- Dropping secret-independence does not merely weaken the condition, it empties it: SecretDependentLeakageDetermined S T m holds for some m whenever T is Deterministic (or TraceUnique) and halts on exactly the inputs where S halts (Toy.CT.exists_secretDependentLeakageDetermined_of_traceUnique_haltAgree). The ∀ f, ¬ LeakageDetermined conjunct follows from Result 2 and the constant-time conjuncts.
- A function of signature Pub -> Sec -> List SrcLeak -> List TgtLeak that ignores its Sec argument reduces definitionally to LeakageDetermined (Toy.CT.secretDependentLeakageDetermined_const_sec_iff).

**Result 4b (`nondeterministic-target-breaks-step-simulation-ct`).**

- This package does not show whether any backward (target-to-source) simulation condition suffices for nondeterministic targets; backward simulation alone yields only inclusion of target traces in the image, not LeakageDetermined.
- nondeterministic_target_sim_breaks_leakage_determined states ¬ Deterministic nondetSecretBranchTarget as a whole; its statement does not say which sub-clause fails. By inspection of the quoted definition of nondetSecretBranchTarget, only the step-leakage uniqueness half of Deterministic.step_det fails (init_det, successor-state uniqueness, and halted_nostep hold), but these kept sub-clauses are not conjuncts of the theorem. For Deterministic.init_det, successor-state uniqueness in Deterministic.step_det, and Deterministic.halted_nostep, necessity with the other sub-clauses stated as conjuncts is proved in Toy.CT.step_sim_drop_tgt_init_det_counterexample, Toy.CT.step_sim_drop_tgt_step_state_det_counterexample, and Toy.CT.step_sim_drop_tgt_halted_nostep_counterexample.
- The nondeterminism in nondetSecretBranchTarget is itself secret-dependent (the extra transition exists only when sec = true); the result does not model a specific real source of target nondeterminism.
- Does not require source determinism to fail: constOneStep is fully deterministic, showing the vulnerability arises strictly from unsimulated nondeterministic transitions in the target semantics.

**Result 5 (`leakage-determined-composes`).**

- The statement is composition of relational images and is definitional; it is a reference point, not evidence that constant-time-preserving compilers are easy to build modularly.
- Composition of StepLeakSim (proving a step simulation for the whole pipeline and applying Result 3 once, as CompCert composes forward simulations before flipping them) is not proved here. Applying Result 3 per pass instead requires HasInit and Safe for every intermediate machine (as the source of the next pass) and Deterministic for every intermediate and final machine (as the target of a pass).
- Establishes vertical sequential composition on a whole machine (M1 -> M2 -> M3), not horizontal linking of compiled constant-time modules with unverified external callers or libraries.

### Escape hatches for the counterexample results

Results 1, 4a and 4b are counterexamples ("this property does not suffice"). The following changes defeat them, each witnessed by a proved positive control or theorem:

- **Result 1** (functional correctness does not preserve constant time) is defeated by adding `LeakageDetermined` with a secret-independent map (Result 2; instance `Toy.CT.branchless_lowering_preserves_ct`). It is also not a counterexample for an observer that sees only the number of steps (`Toy.CT.branchingSelect_trace_length`).
- **Result 4a** (secret-reading maps certify nothing) is defeated by requiring the map to ignore the secret (`Toy.CT.secretDependentLeakageDetermined_const_sec_iff`, then Result 2).
- **Result 4b** (forward simulation into a nondeterministic target) is defeated by a deterministic target (Result 3; instance `Toy.CT.determinized_target_sim_positive_control`).

### Tightness status

Every hypothesis of Results 2, 2b, 3 and 5 is `tight`, with a fully proved counterexample listed in its ledger. No hypothesis has tightness `unknown`, and no hypothesis is labeled `harmless`.

### Disproved, dropped, or unresolved statements

None. All seven results were proved exactly as stated; no statement was found false, weakened, or left unproved.

### Not examined

- Prefix-based (step-indexed) or divergence-sensitive constant time, probabilistic or speculative constant time, and microarchitectural leakage models.
- Relational simulations with state-dependent step counts (the general constant-time simulations of Barthe, Grégoire and Laporte, CSF 2018).
- Backward-simulation or other conditions for nondeterministic targets.
- Compilers as functions over all programs, separate compilation and linking, and environment interaction during execution.
- Any connection to the formal artifacts (Coq, Isabelle, Jasmin) of the cited works beyond the quoted CompCert record and lemma.

## Evidence

### Kernel-check record

Toolchain: Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library only. Every declaration of the `ToyCT` library (585 declarations, recorded in `audit/axioms.json`) depends only on axioms among `propext`, `Classical.choice`, and `Quot.sound`. Statement and definition-closure hashes (SHA-256, as defined under `## Revalidation`) are recorded in `audit/statements.json`; the table lists every Lean name referenced by `results.json`. Observed 2026-11-20.

| Lean name | Role | Axioms (`#print axioms`) | Statement SHA-256 | Closure SHA-256 (size) |
| :-- | :-- | :-- | :-- | :-- |
| `Toy.CT.StepLeakSim.toOutputFree` | R3 cited | (none) | `72452ff1237735c1a58a69968bb0bcf0d6542bd4b39919a3c1ab5cbce3328b92` | `b674ee4e02c043c3f2df26d1c013f1a15471c86e751ce79e4da5aca4ab20de30` (13) |
| `Toy.CT.branchingSelect_trace_length` | R1 cited | (none) | `cace4a8b40a831fbfd557c97f28f779e968280be1af911fae6a236b45d2c2afe` | `d034e61e30cfbfaec0849dc75d26b2f9dae67d8dfae93d2b6e4df96bb48a87c9` (20) |
| `Toy.CT.branchless_lowering_preserves_ct` | R1 positive control; R4a positive control | `propext` | `094e9fa268161f761318a9a37b3081414cdc9aeab3c7d40be6c1a72935540829` | `f2c275605a58c232e33619c38ee5e87244d19511f8b4e5917db631744d900956` (36) |
| `Toy.CT.constantTime_not_refinement_closed` | R2 cited | `propext` | `599d451b6341ba48c5ebee870795e918717c3a73606968fbbbb6e90e9f51a9f4` | `5bf7f3ea87f07208d4f730506622780984e834671af3e7f2bd2685e49e63e6bc` (14) |
| `Toy.CT.determinized_target_sim_positive_control` | R4b positive control | `propext` | `37f3f03eaf61e4707a201ddeb2dae5d620e33a17d1a6753ad2602640e4063a50` | `254cddaf0860f1712488687c6e79cdb518914ae252e167f06bb53a9abc33509c` (32) |
| `Toy.CT.exists_ld_iff_drop_src_ct_counterexample` | R2b counterexample `hCTS` | (none) | `33ce7aed01cf147e7f5b6bf2c4c2c5568da273656a343229cc3fb4edd2de83e7` | `628a5d76655d0318f32ff088d882716f0e0bb30c963da29183a4a81c59f19d3e` (16) |
| `Toy.CT.exists_ld_iff_drop_tgt_traceUnique_counterexample` | R2b counterexample `hTgtUnique` | `propext` | `ca17f311349ea232a6c271222fa9eafbda5249e6ef86624af67ab84ef2f4f38d` | `1ea34c4b7a7663c773b322e46ebf764e78f3485b78b34a9ec0bfa5755ab567d5` (16) |
| `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique` | R2b main | `Classical.choice`, `Quot.sound`, `propext` | `4738bcf21d917bdb96cabdcc4effaa111d6f93edc51847844563fb9ae598342b` | `337fd748c1afc5d65b743cfcc71698157d4198f6734d6be35e78fee9bb784ea8` (15) |
| `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_both_sides_false` | R2b cited | `propext` | `c77cade1e53dbae68ae8289436b2d682072cabf0296b050212431cb7fa4115a8` | `c7992eaa8ac8279afb2e897233954955aade367cdfa9d33893857e16eee8328d` (31) |
| `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_both_sides_true` | R2b cited | `propext` | `1ec033626323976e5353fa16c61e6c7f36dda94736983944e5a2d82c40491ffd` | `ea18290fc365b45429008bcf0f36d6e1d97e1ff05ec2a6575ef6849f07ad6f55` (29) |
| `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_nonvacuous` | R2b witness | `propext` | `41adf78e5aba845b6cd89e77658042a4ff2c3ed3ef31f21db149df0a969666eb` | `3789abaab38691058de15cac1856a97e41b1abe3f0b62ad25ec3ad82ed59f4b7` (28) |
| `Toy.CT.exists_secretDependentLeakageDetermined_of_traceUnique_haltAgree` | R4a cited | `Classical.choice`, `Quot.sound`, `propext` | `ab71b27d27b143e68804f672f506ddd7d3d7d8d71b28d0d1ccda0cda61645459` | `2cc62f96459129247edd55aa2044fb9768d16a4b4409887ff5d0d59fd7ad0fd8` (14) |
| `Toy.CT.functional_correctness_does_not_preserve_ct` | R1 main; R1 witness | `propext` | `5dfc05533bc16bc67e5ac99e59f85ac26537c28aab343a61c9d1c6815190b32d` | `ef0e57a0e2d582474750bc509c4595ec3c623c3e5880558e22d67c195cb3be91` (32) |
| `Toy.CT.leakage_determined_comp` | R5 main | `propext` | `7a5c5cbc1fd01617e741d5c2568655e959591aa34d6c1062976c883cfb24903e` | `2e5f6cff2698b2d450ae66b52f5108ebe5fee8f1fd900a75fd17d77248d8f704` (13) |
| `Toy.CT.leakage_determined_comp_drop_first_counterexample` | R5 counterexample `h₁₂` | `propext` | `21dbed0a87aea551ccffee22e33babce90ab832ea663eda308d78794d541bea4` | `752e240a4942de2e0b339d21b9cb3664505d241291c2a65a63949ac66cfa03e7` (29) |
| `Toy.CT.leakage_determined_comp_drop_second_counterexample` | R5 counterexample `h₂₃` | `propext` | `a1182fc8666688bf737c7038ac0faf47210bb54660d8b301b7e5ec16badef54c` | `752e240a4942de2e0b339d21b9cb3664505d241291c2a65a63949ac66cfa03e7` (29) |
| `Toy.CT.leakage_determined_comp_nonvacuous` | R5 witness | `propext` | `510e368ac6eadb1941a69864faebc2ac84e24878b059213fcaf38b2ef9700708` | `4e5ecc72a851cef928e0f40d886d52d7042a6ac725c02d850783b2843fbbc40a` (41) |
| `Toy.CT.leakage_determined_drop_ct_counterexample` | R2 counterexample `hCT` | `propext` | `e0a7535cd56ecc86494a23cba890c9a737f31c3f491768be02f168f226f7e14f` | `844183c24ddff0c2ed75f06d7ca65215270041c49dab44a80bb271f24ffc731b` (22) |
| `Toy.CT.leakage_determined_preserves_ct` | R2 main | `propext` | `9ba959eecb2e062bffabdcf5cd477dc650286c77db05c7ab7b03f9e63f3ff20c` | `2ab1e01cd88403da4137cd979a5833aa18e07e374ec389ddffafa2c0b51b9ed2` (13) |
| `Toy.CT.leakage_determined_preserves_ct_nonvacuous` | R2 witness | `propext` | `9da706a22bf1b234173f00d55687052d6cf2f9570ed9bbb5fe8da98abe097f67` | `75462c5db5074286fd41cd701e353e5e952ac44618d46e7f51cc18804fef9f83` (32) |
| `Toy.CT.leakyLoop_constantTime_despite_diverging_step_leak` | R2 cited | (none) | `f9416da9d93a666ea68dc31ea320457b40ace77160899c1642b5167af1a40259` | `7283d136ffab6fcd47d3f34dfa6a27ed627063004fa7c610f4c6a86d31beded3` (13) |
| `Toy.CT.nondeterministic_target_sim_breaks_leakage_determined` | R3 counterexample `hTgtDet`; R4b main; R4b witness | `propext` | `859338c5ea9d4f7c001951da98e8eea21dde04f286fbc3a7a1f381e9b1a2ceb4` | `822ba7d31a66fd86a92ccd6007ee52da9261417f673c1e16a0c0aef45491da14` (34) |
| `Toy.CT.option_stutter_sim_breaks_ct` | R3 cited | `propext` | `c6f3ed1762f1cf5961f4db005828db3c35f8acd084cfbedccb57452dbc280b15` | `3f8ad0be5d964b5475b29ce05736c9ccdcc5bb19591da58f5bccc9c12b739c7a` (32) |
| `Toy.CT.outputFree_step_leakage_sim_det_target_implies_leakage_determined` | R3 cited | `Quot.sound`, `propext` | `1bf917ba3a2e7880a82ee9405417dcb6aec93eae8729c8e14ae4e45ea3b53aa0` | `0c9d80220ba71f87ad2e2af1ef6951ecf45821f9b89e68facd693e943dbd5ccb` (22) |
| `Toy.CT.secretDependentLeakageDetermined_const_sec_iff` | R4a cited | (none) | `cabd6dc672384ad2c43d1a18ba296d3318576bcdbccad378c934a77a34e5ba4a` | `de875b24834aa6e941a7942e96dbb58a3a278951cd86b5ce04d248ac329a0448` (13) |
| `Toy.CT.secret_dependent_leak_map_breaks_ct` | R2 counterexample `hLD`; R4a main; R4a witness | `propext` | `6637f044216185917827b0b37333af82b0f76687b5f868957bc6c17abb68961e` | `dfc84371ac4f280eb08072a2eb166a43e6799e8098b095ebf931e3529d4b322d` (38) |
| `Toy.CT.step_leakage_sim_det_target_implies_leakage_determined` | R3 main | `Quot.sound`, `propext` | `2bcc2b069084d9c842a78b6d7d4e441e0b373bc1b6e5dbd0113696a2f93317a7` | `2660d4f9c3d68b9d3196b26267e23c884c122fe436e0393818bd018175d6d9f0` (22) |
| `Toy.CT.step_leakage_sim_det_target_implies_leakage_determined_nonvacuous` | R3 witness | (none) | `3104d5523168cff0a63b9b8cd299cdd357d77028a331194e1a25ccfa47da2ea8` | `738c522e1b51bdc1274eaeab1f673f9bd14b78de44e9e9cab05f437933d3ad19` (37) |
| `Toy.CT.step_sim_drop_sim_counterexample` | R3 counterexample `hSim` | `propext` | `02237c4002baa9775a920c7bd6924e2b9f7512df55f8f3fcb44ceda23fa5e259` | `c80da9b1c0f3d5c04a0eb6b1f073a4d8b5e2bbf5b33637ddcefd7db2f456097f` (37) |
| `Toy.CT.step_sim_drop_src_init_counterexample` | R3 counterexample `hSrcInit` | (none) | `16f26fba054247880b6763d518cd621f9295c9a064d39c5fe9edae115b4f1019` | `71a4b8f4d91a6d22ef4e818d5b1c7064958cf6708011e803b20d253f3a82b529` (24) |
| `Toy.CT.step_sim_drop_src_safe_counterexample` | R3 counterexample `hSrcSafe` | (none) | `a1b1f768c00eca9732a757722375868c7bdb8bc66f5a44dd15df663408985f13` | `7240be6edae30a9ab92e8e6ed1f1342e49016b18b50bceb0b215d221aefaf3f6` (23) |
| `Toy.CT.step_sim_drop_tgt_halted_nostep_counterexample` | R3 counterexample `hTgtDet` | `propext` | `34c09e249bdcbd316f4d181ecfaa310ef6c3041f9261f14cc751812837db83a4` | `77f4aa50cdc30d52489646f05fd2da4cfe6638b06d84258160267039f38d607d` (23) |
| `Toy.CT.step_sim_drop_tgt_init_det_counterexample` | R3 counterexample `hTgtDet` | `propext` | `9c3356e84be0d2819ce0ce2b8f0adb6610a5cd0ca0b7498c1013693e3f2174ba` | `6299fd78513f147ebd375b09dba1e2a70be54f936d7e14e927b43ca9ffa12a6b` (30) |
| `Toy.CT.step_sim_drop_tgt_step_state_det_counterexample` | R3 counterexample `hTgtDet` | `propext` | `255b83d92e31c47afdb060f34595df425d4007978ee432b4b3f56b1f47cef3f8` | `1ee9f36d349df7d542e6d0148641bb70ba4387bdc978c35af3d4253dc77f4328` (31) |
| `Toy.CT.terminates_and_constantTime_unconstrained_diverging_branch` | R2 cited | `propext` | `c65b169e76b9d30e77439ca190597c555f0b6d5fbc28ce394b28ee34b9163d4e` | `a5aa38d066be7e8b734475125597f7a536e9bbf75ac7a934e8635b681ce2b6bd` (20) |
| `Toy.CT.unmeasured_stutter_sim_breaks_leakage_determined` | R3 counterexample `hSim` | (none) | `7d0a6f5e7d01752fa7e0491a01630ba87ebdfc18feb633e9d186fcfbc899d662` | `698df1287f13dab53a198c0506161a29bbe08a2f43784cd73785e422db7ba991` (25) |
| `Toy.CT.weakLeakageDetermined_fails_without_traceUnique` | R2 cited | (none) | `e65ffff07c6dfa6ad5074cc1d1f468681c366e6c972dc3229a9aec639beb3b2c` | `b48ed68b9527f7dd96682aaea4f2ca1e7a90415257cdfe0388d3b140b60d2c4f` (21) |
| `Toy.CT.weakLeakageDetermined_preserves_ct_of_traceUnique` | R2 cited | (none) | `ae88ae34ba408c79454aff966da010f2e651a2bcb5c81e6cbfe59dca63a87c10` | `eb4458403851ebfe5f9e58611a62276f65c95325ebf69c007ccd46cccdf37983` (14) |

Supporting theorems in the table beyond the cards' main statements, witnesses, controls, and counterexamples: `Toy.CT.outputFree_step_leakage_sim_det_target_implies_leakage_determined` and `Toy.CT.StepLeakSim.toOutputFree` (output-free form of Result 3), and `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_both_sides_true` / `_both_sides_false` (both sides of Result 2b can hold and can fail).

### Primary sources and exact records

Bibliographic records below were checked on 2026-11-20 against the DOI registration metadata (Crossref for ACM, IEEE, IOS Press, and Springer DOIs; DataCite for the LIPIcs DOIs) or against the source page named.

- **CompCert**, repository `AbsInt/CompCert`, tag `v3.18`, commit `14d616046360a0b2611ebdfc2f98368af402e1f7`, file `common/Smallstep.v` (SHA-256 of the file at that commit: `3279079eafb097a919f1e774a44200a59017a7f7edc665cc708b30c026c3e1b3`): `Definition single_events` (lines 1047–1048), `Record determinate` (lines 1058–1071, quoted in `## Applicability`), and

  ```coq
  Lemma forward_to_backward_simulation:
    forall L1 L2,
    forward_simulation L1 L2 -> receptive L1 -> determinate L2 ->
    backward_simulation L1 L2.
  ```

  (lines 1863–1866). Rendered documentation: https://compcert.org/doc/html/compcert.common.Smallstep.html.
- Xavier Leroy, "A Formally Verified Compiler Back-end," *Journal of Automated Reasoning* 43(4), pp. 363–446, 2009. DOI 10.1007/s10817-009-9155-4.
- Gilles Barthe, Benjamin Grégoire, Vincent Laporte, "Secure Compilation of Side-Channel Countermeasures: The Case of Cryptographic 'Constant-Time'," *2018 IEEE 31st Computer Security Foundations Symposium (CSF)*, pp. 328–343, 2018. DOI 10.1109/CSF.2018.00031.
- David Molnar, Matt Piotrowski, David Schultz, David Wagner, "The Program Counter Security Model: Automatic Detection and Removal of Control-Flow Side Channel Attacks," *ICISC 2005*, LNCS 3935, pp. 156–168, Springer, 2006. DOI 10.1007/11734727_14.
- Gilles Barthe, Benjamin Grégoire, Vincent Laporte, Swarn Priya, "Structured Leakage and Applications to Cryptographic Constant-Time and Cost," *CCS '21*, pp. 462–476, 2021. DOI 10.1145/3460120.3484761.
- Gilles Barthe, Gaëtan Cassiers, Henri Dohmen, Marc Gourjon, Benjamin Grégoire, Nora Khayata, Thomas Schneider, Finn Schubert, "Secure Compilation of Probabilistic Side-Channel Countermeasures," Cryptology ePrint Archive, Paper 2026/2510 (received 2026-10-16), https://eprint.iacr.org/2026/2510. The abstract describes "a deterministic leakage-preservation relation that implies preservation of probabilistic security notions, including d-NI and d-SNI for masking and cryptographic constant-time".
- Alix Trieu, "A Study on the Preservation of Cryptographic Constant-Time Security in the CompCert Compiler," Workshop on Foundations of Computer Security (FCS 2018), https://www.andrew.cmu.edu/user/liminjia/events/fcs2018/papers/s31.pdf (title and author confirmed from the PDF). FCS 2018 was held in Oxford, UK, on 8 July 2018, affiliated with FLoC 2018, and had informal proceedings only: the workshop page, https://www.andrew.cmu.edu/user/liminjia/events/fcs2018/, states "The workshop has no published proceedings" and that presented papers "will be made available to workshop participants, but this does not constitute an official proceedings." The paper therefore has no DOI or archival publisher record, and no content hash of the PDF is recorded; the organizer-hosted URL is the strongest available identity and may not be durable. Only the attribution of the anti-stuttering measure in Result 3 rests on this source; no theorem depends on it.
- Gilles Barthe, Sandrine Blazy, Benjamin Grégoire, Rémi Hutin, Vincent Laporte, David Pichardie, Alix Trieu, "Formal Verification of a Constant-Time Preserving C Compiler," *PACMPL* 4(POPL), Article 7, pp. 1–30, 2020. DOI 10.1145/3371075.
- Michael R. Clarkson, Fred B. Schneider, "Hyperproperties," *Journal of Computer Security* 18(6), pp. 1157–1210, 2010. DOI 10.3233/JCS-2009-0393.
- Carmine Abate, Roberto Blanco, Ștefan Ciobâcă, Adrien Durier, Deepak Garg, Cătălin Hrițcu, Marco Patrignani, Éric Tanter, Jérémy Thibault, "Trace-Relating Compiler Correctness and Secure Compilation," *ESOP 2020*, LNCS 12075, pp. 1–28, 2020. DOI 10.1007/978-3-030-44914-8_1.
- Vijay D'Silva, Mathias Payer, Dawn Song, "The Correctness-Security Gap in Compiler Optimization," *2015 IEEE Security and Privacy Workshops*, pp. 73–87, 2015. DOI 10.1109/SPW.2015.33.
- Thierry Kaufmann, Hervé Pelletier, Serge Vaudenay, Karine Villegas, "When Constant-Time Source Yields Variable-Time Binary: Exploiting Curve25519-donna Built with MSVC 2015," *CANS 2016*, LNCS 10052, pp. 573–582, 2016. DOI 10.1007/978-3-319-48965-0_36.
- Laurent Simon, David Chisnall, Ross Anderson, "What You Get is What You C: Controlling Side Effects in Mainstream C Compilers," *2018 IEEE European Symposium on Security and Privacy (EuroS&P)*, pp. 1–15, 2018. DOI 10.1109/EuroSP.2018.00009.
- Lukas Gerlach, Robert Pietsch, Michael Schwarz, "Do Compilers Break Constant-Time Guarantees?," *Financial Cryptography and Data Security (FC 2025)*, LNCS 15752, pp. 327–344, Springer, 2026. DOI 10.1007/978-3-032-07035-7_20.
- David Knothe, Oliver Bringmann, "On Verifying Secret Control Flow Elimination," *ITP 2025*, LIPIcs 352, pp. 31:1–31:19, 2025. DOI 10.4230/LIPIcs.ITP.2025.31.
- Santiago Arranz Olmos, Gilles Barthe, Lionel Blatter, Benjamin Grégoire, Vincent Laporte, "Preservation of Speculative Constant-Time by Compilation," *PACMPL* 9(POPL), pp. 1293–1325, 2025. DOI 10.1145/3704880.
- Robert Sison, Toby Murray, "Verifying That a Compiler Preserves Concurrent Value-Dependent Information-Flow Security," *ITP 2019*, LIPIcs 141, pp. 27:1–27:19, 2019. DOI 10.4230/LIPIcs.ITP.2019.27.
- Martin Desharnais-Schäfer, "A Generic Framework for Verified Compilers," Archive of Formal Proofs, entry `VeriComp`, 2020-02-10, https://www.isa-afp.org/entries/VeriComp.html.
- Toby Murray, Robert Sison, Edward Pierzchalski, Christine Rizkallah, "Compositional Security-Preserving Refinement for Concurrent Imperative Programs," Archive of Formal Proofs, entry `Dependent_SIFUM_Refinement`, 2016-06-28, https://www.isa-afp.org/entries/Dependent_SIFUM_Refinement.html.

The Lean source of this package is the primary evidence for every theorem: `lean/ToyCT/Defs.lean` (definitions and general lemmas), `lean/ToyCT/Machines.lean` (concrete machines and their trace facts), `lean/ToyCT/Examples.lean` (adequacy examples), and `lean/ToyCT/Results.lean` (main results, witnesses, controls, counterexamples).

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No network access is needed beyond the toolchain download; the project has no dependencies.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified) and checks, printing one line per check and `REVALIDATED` on success:

1. `lake build` of the Lean project succeeds.
2. No Lean source contains `sorry`, `admit`, or `native_decide`, or declares an `axiom`.
3. Every declaration of the `ToyCT` library depends only on `propext`, `Classical.choice`, and `Quot.sound` (computed with Lean's `collectAxioms`).
4. For every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample`s) and every name recorded in `audit/statements.json`, the statement hash and the closure hash equal the recorded values. Exactly what is hashed: the statement hash is SHA-256 of Lean's `repr` of the declaration's type; the closure hash is SHA-256 of the newline-joined, sorted lines `name : repr(type)` (with ` := repr(value)` appended for non-theorems) for every `ToyCT` constant reachable from the statement's type through types, non-theorem values, and inductive constructors. Theorem bodies are excluded, so a proof can change without changing any hash, but any change to a statement or to a definition it depends on changes a hash.

**Manual equivalent.** The same audit with only `lake`, `lean`, and `python3`:

```sh
cd lean
lake build                                   # must succeed with no `sorry` warnings
lake env lean RevalidationAudit.lean > /tmp/ct_audit.txt
cd ..
python3 - <<'EOF'
import hashlib, json, re
a = json.loads(re.search(r"AUDIT_JSON (\{.*\})", open("/tmp/ct_audit.txt").read()).group(1))
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = [d["name"] for d in a["decls"] if set(d["axioms"]) - allowed]
print("declarations:", len(a["decls"]), "with non-standard axioms:", bad)
rec = json.load(open("audit/statements.json"))["statements"]
for s in a["stmts"]:
    assert not s.get("missing"), s["name"]
    got = {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
           "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
           "closure_size": len(s["closure"])}
    print("ok  " if rec.get(s["name"]) == got else "FAIL", s["name"])
EOF
```

`lean/RevalidationAudit.lean` is outside the library target (it is not imported by `ToyCT.lean` and is not built by `lake build`). It imports `ToyCT`, prints the axioms of every `ToyCT` declaration, and prints the statement `repr` and definition closure of every card-referenced name, as described in its header comment.

**Single-theorem spot check.** To inspect one result directly, add a scratch file next to `lakefile.toml` containing, for example,

```lean
import ToyCT
#check @Toy.CT.leakage_determined_preserves_ct
#print axioms Toy.CT.leakage_determined_preserves_ct
```

and run `lake env lean <file>`.

What revalidation does not establish: a passing run shows that the statements quoted in this report are kernel-checked under standard axioms and unchanged. It does not re-check the prose cards, the modeling bridges, or the literature records; those must be re-read against the Lean statements and sources.
