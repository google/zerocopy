# Reduction soundness by property class, and where scheduler and fairness assumptions live: mechanized POR, stutter invariance, TLA reduction, mover calculi and IronFleet

## Summary

A reduction gives a theorem about the real system only for the property class that its correctness relation preserves. That relation, and every scheduler or fairness assumption, must also appear somewhere a reader can find it. The developments examined here differ sharply on both counts:

- **Ample-set partial-order reduction (POR)** preserves *next-free* LTL over infinite runs. The mechanized theorem in the Archive of Formal Proofs is `reduction_correct`: `S.language ⊆ F.language ⟷ R.language ⊆ F.language`, for any formula satisfying `next_free φ` (`Partial_Order_Reduction/Ample_Correctness.thy`).
  - Its ample conditions are locale assumptions: subset, non-empty, independent, invisible, and a cycle proviso phrased as a **well-founded relation** on states.
  - The executable CAVA model checker's end-to-end theorem `cava_sm_correct` discharges those assumptions for its input language. It **checks next-freeness at run time**, answering `TY_ERR` otherwise. It also makes the system total by stutter extension.
  - No fairness constraint appears anywhere in this chain.
- **Stutter invariance and next-freeness coincide for PLTL.** This is mechanized as `pltl_stutter_invariant` in `Stuttering_Equivalence/PLTL.thy`. The standard citation for it is Peled and Wilke (1997), whose full text was not read.
- **Branching time needs more than the LTL conditions.** In a toy model (labelled as such), an ample set that satisfies C0–C3 preserved every stutter-free visible trace but changed `EF(p ∧ EF r1 ∧ EF r2)` from true to false. A singleton requirement on proper ample sets rejects that ample set. Gerth, Kuiper, Peled and Penczek (1999) give conditions for CTL* without next-time; their exact condition was not read.
- **TLA reduction (Cohen and Lamport, 1998)** comes in three versions:
  - *Theorem 1* needs a liveness hypothesis `Q` even to conclude a safety-form result.
  - *Corollary 2* replaces `Q` with an enabledness condition: after the non-mover, it is always possible to finish. With that, safety properties transfer.
  - *Theorem 3 / Corollary 5* transfer weak and strong fairness, but need extra commutativity, enabledness and an infinitely-often hypothesis `O`.
  - **Armada** encodes the Corollary-2 style: `LeftMoversAlwaysEnabled` plus commutativity and phase predicates. Its trusted notion of refinement quantifies over **finite** behaviors only, so its guarantees are safety only. The Armada paper says so ("can prove safety but not liveness properties").
- **Mover calculi (QED, CIVL).** CIVL reduces refinement to safety of checker programs. At the pinned Boogie revision, `MoverCheck.cs` checks commutativity and gate preservation for every pair involving a right or left mover, and failure preservation for pairs involving a left mover. It checks *non-blocking* of a left mover only when the left mover contains an `assume`. Left-mover termination is not checked. Inductive sequentialization adds a *cooperation* condition precisely because non-blocking alone is unsound there.
- **IronFleet** places its assumptions in three different kinds of place:
  - The *network* model (drop, duplication, reordering; no tampering) is trusted specification text in `Environment.s.dfy`.
  - The *atomicity reduction* obligation is asserted in the trusted `Main.s.dfy` loop. The paper says the reduction argument itself is informal ("A machine-checked proof that this obligation enables reduction is future work").
  - The *liveness* assumptions (synchrony after a start time, bounded clock error, no Zeno behavior, bounded delivery rate, a periodically executing host scheduler) are hypotheses of a protocol-level lemma in an untrusted `.i.dfy` file. The top-level trusted theorem is safety refinement over finite behaviors.

The practical rule: before relying on a reduction-based or scheduler-relative result, recover (1) the relation it proves (finite-trace inclusion, stutter-equivalent infinite languages, or a branching equivalence), (2) the logic closed under that relation, and (3) where each fairness, scheduler and environment assumption is written, and whether it is trusted text, a theorem hypothesis, or prose. §10 gives a checklist for these steps.

## Applicability

- **Mechanized subjects** (pinned in `REPORT.json`), examined from source only:
  - the Isabelle/HOL theories in the Archive of Formal Proofs mirror;
  - Armada's reduction strategy in Dafny;
  - CIVL's checkers inside Boogie (C#);
  - IronFleet's trusted framework and IronRSL liveness files in Dafny.
- None of these was built or run. Statements about what the theories prove come from reading their statements, not from rechecking proofs.
- The AFP mirror is a read-only mirror of the Archive. The Ironclad pin is the repository's latest commit (2023-06-03) and the Armada pin its latest commit (2024-01-17), both observed on 2026-11-21.
- **Literature** comes from copies read on 2026-11-21. Several of them are preprints, technical reports or manuscripts, so page numbers follow those copies (see Evidence).
- Four works were available only as abstracts: Peled 1993, Peled–Wilke 1997, Gerth et al. 1999, and Elmas–Qadeer–Tasiran 2009. Claims about their contents are limited to the abstracts.
- **The toy model** (`support/probes/por_toy.py`) is a hand-written explicit-state program. Its results are statements about three tiny transition systems and illustrate known phenomena. They are not measurements of any real model checker.
- **Relationship among subjects.** This is a comparison. Each development is read for the same three questions: which relation it establishes, which property class follows, and where it states its assumptions.

## Findings

### 1. Property-class matrix

| Reduction or method | Relation established | Property class preserved | Extra conditions | Mechanized? | Where the assumptions live |
|---|---|---|---|---|---|
| Ample-set POR (AFP `Ample_Abstract`) | every run of S has a stutter-equivalent run of R, and R ⊆ S | next-free PLTL over infinite runs | independence, non-empty, invisible, well-founded cycle proviso | yes (Isabelle/HOL) | locale assumptions `ample_abstract`, `formula_next_free` |
| CAVA end-to-end | as above, for the SM input language | next-free LTL; non-next-free formulas get `TY_ERR` | static independence approximation; sticky edges break cycles | yes, down to generated SML | discharged by the theorem except trust in Isabelle and its code generation |
| Branching-time POR (Gerth et al. 1999) | per the abstract, conditions that "guarantee reduction that preserves CTL* properties", with next-time removed | CTL and CTL* without next-time; Hennessy–Milner logic with τ | beyond C0–C3; the exact form was not read | not examined | — |
| Lipton 1975 | relaxed indivisibility | "properties such as halting" (Crossref abstract) | not read | no | — |
| Cohen–Lamport Thm 1 | `S ∧ Q ⇒ ∃∃ v̄ : □I ∧ S̄^R` | reasoning about the reduced spec | phase conditions; `R·E ⇒ E·R`, `E·L ⇒ L·E`; liveness hypothesis `Q` | no (paper proof) | theorem hypotheses |
| Cohen–Lamport Cor 2 | as Thm 1 without `Q` | safety properties | `L ⇒ Enabled(L⁺ ∧ ¬L′)` | no | theorem hypotheses |
| Cohen–Lamport Cor 5 | adds `∀i: XF(Ā_i^R)` | WF/SF fairness of reduced actions | 2(c)–(g), 3(a)–(c), `Q`, `O` | no | theorem hypotheses; "we expect the specification's fairness properties to imply Q ∧ O" |
| Armada reduction | `BehaviorRefinesBehavior` over `seq<State>` | safety (finite behaviors) | `ValidCohenLamportReductionRequest` (16 conjuncts) | yes (Dafny), generated per program | request predicate; trusted `refinement.s.dfy` |
| CIVL / layered programs | `Safe(P_1)` from per-layer checks | safety (no failing gate) | commutativity, forward and backward preservation, non-blocking left movers, atomicity automaton | soundness proved on paper; checks emitted as verification conditions | checker programs generated by Boogie |
| Inductive sequentialization | summary inclusion plus failure | safety, and properties of terminating states | left movers plus *cooperation* | paper proof (Theorem 4.4) | proof-rule premises |
| IronFleet safety | `RefinementProof` over `seq<DS_State>` | safety refinement of the service spec | IO-ordering obligation for reduction | yes, except the reduction step (informal) | `Main.s.dfy` and `Environment.s.dfy` (trusted) |
| IronFleet (IronRSL) liveness | `lemma_EventuallyLiveReplicaExecutesClientRequest` | a client request is eventually executed | `LivenessAssumptions` | yes (Dafny), protocol layer | hypothesis of an `.i.dfy` lemma that uses trusted `.s.dfy` predicates |

Basis: source (AFP, Armada, Boogie, Ironclad) + documentation (papers) + derived (the column "property class" for Armada and IronFleet follows from the finite-sequence types).

### 2. The mechanized POR theorem and its hypotheses

**Statement** (`thys/Partial_Order_Reduction/Ample_Correctness.thy`, locale `ample_correctness`):

```text
theorem reduction_correct: "S.language ⊆ F.language ⟷ R.language ⊆ F.language"
```

The locale imports four pieces:
- `transition_system_complete` twice: S uses the enabledness `en` and R uses the reduced `ren`;
- `formula_next_free φ`, which assumes `next_free φ`;
- `ample_abstract`, which assumes `reduction_ample: q ∈ nodes ⟹ ample_set q {a. ren a q}`.

`language` is `{smap int (p ## trace w p) | p w. init p ∧ run w p}` over action **streams** (`Transition_System_Extensions.thy:105-106`). Only infinite runs count.

**Ample condition as formalized** (`Ample_Abstract.thy:28-34`). `ample_set q A` holds iff all of the following hold:
1. A ⊆ enabled;
2. if proper, A ≠ ∅;
3. if proper, every `a ∈ A` satisfies `src (ex a q) q`, for a well-founded `src`;
4. if proper, A ⊆ invisible;
5. if proper, every path `w` from `q` that avoids A satisfies `Ind A (set w)`.

The source comments map these to "condition C0 in [2]", "condition C2 in [1, 2]" (well-founded), "condition C3' in [1], not needed in [2]" (invisible), and "condition C1 in [1, 2]" (independent). Here [1] is Peled, FMSD 1996 and [2] is Chou and Peled, TACAS 1996.

*Numbering hazard:* other presentations call invisibility C2 and the cycle proviso C3. The toy model in §4 uses that second numbering.

**Independence** is a locale assumption (`Transition_System_Traces.thy:53-54`). For independent `a`, `b`, executing `a` neither enables nor disables `b`, and the two orders commute. `transition_system_interpreted_traces` adds `independence_invisible`: two visible actions are never independent.

**End-to-end** (`thys/CAVA_LTL_Modelchecker/CAVA_Impl.thy:1223-1272`). `cava_sm cfg prog φ` returns `TY_ERR` unless `ty_program prog ∧ ltlc_next_free φ`. `cava_sm_correct` states:
- `SAT ⇒ Collect (ap_accept prog) ⊆ language_ltlc φ`;
- `UNSAT` and `UNSAT_CE` give the negation, with the counterexample related to a run of the reference semantics.

The bridge is `ample_reduction_correct` (`SM/Impl/SM_Wrapup.thy:37-40`), which assumes `ty_program prog` and `ltlc_next_free φ`. Finite executions are made infinite by "stutter extension" (`SM/RefPoint/Gen_Scheduler.thy:69-70`). This is how the "complete transition system" premise is met without a deadlock special case.

Basis: source.

**What remains outside the theorem** (Brunner–Lammich manuscript):
- trust in Isabelle/HOL ("the correctness of the model checker only depends on the correctness of Isabelle/HOL");
- Isabelle's code generation to SML;
- the SML compiler; no separate statement about it was found.

The independence approximation is deliberately crude. A process's statically enabled actions may not touch globals, and no sticky edge may be involved (§3.8). The authors chose static POR because it "ensures condition wellfounded by performing some static analysis initially, identifying a set of sticky edges which break every cycle". While formalizing, they "discovered a counterexample for one of the lemmata used in" the published proof of the dynamic on-the-fly algorithm. Basis: documentation.

### 3. Stutter invariance is exactly next-freeness (PLTL)

`thys/Stuttering_Equivalence/PLTL.thy` proves two directions:
- `next_free_stutter_invariant: next_free φ ⟹ stutter_invariant φ` (`:186`), by induction on formulas;
- `stutter_invariant_next_free` (`:742`): every stutter-invariant `φ` has an equivalent next-free `ψ` over the same atoms.

They combine into `pltl_stutter_invariant` (`:779`). `ltlc_next_free_stutter_invariant` (`:825`) carries this to the LTL syntax that CAVA uses. The POR proof uses only the first direction (`Formula.thy`, `stutter_equivalent_entails`). This is the content attributed to Peled and Wilke (1997). The IPL text was not read, so the size of the translation is unknown. Basis: source.

**Toy case 2.** Process P0 has an invisible step, and P1 makes `p` true. The ample set {τ} satisfies C0–C3. The full graph violates `A(¬X p)`, because P1 can move first, but the reduced graph satisfies it. Next-time distinguishes stutter-equivalent traces, so any POR that preserves only stutter-equivalence must exclude it. Basis: execution (toy model, not a real model checker).

### 4. The cycle proviso and the ignoring problem

**Toy case 1.** P0 spins forever on an invisible self-loop, and P1 can make `p` true once. The proper ample set {spin}, chosen again at every revisit, satisfies non-emptiness, independence and invisibility. Its only cycle, however, consists of states with a proper ample set. The reduced graph never reaches `p`, so `G ¬p` is wrongly reported as true. Basis: execution (toy model).

The AFP formalization makes the proviso a ranking argument: actions in a proper ample set must strictly decrease a well-founded relation. The Brunner–Lammich gloss reads: "every cycle in the system automaton contains at least one state where no reduction is performed". Basis: source + documentation.

### 5. Branching time

**Toy case 3.** P0 chooses invisibly between `a1` and `a2`, which later lead to visible `r1` and `r2`; P1 independently sets `p`. The ample set {a1, a2} at the initial state satisfies C0–C3, and the two graphs have equal sets of stutter-free visible traces. Even so, `EF(p ∧ EF r1 ∧ EF r2)` is true in the full graph and false in the reduced one: in the reduced graph, every `p`-state has already committed to one branch. A singleton requirement on proper ample sets (the toy's "C4") rejects this ample set, and the only valid choice left is full expansion. Basis: execution (toy model).

Gerth et al. (1999) state in their abstract that they give "Conditions on the selection of subset of successors from each state ... which guarantee reduction that preserves CTL* properties", for CTL and CTL* "with the next time operator removed". Whether their condition is exactly the singleton rule used in the toy was **not verified**: the full text could not be read.

### 6. TLA reduction, and the Armada encoding

**Lamport (1994).**
- "It is easy to check that TLA formulas are invariant under stuttering" (§8.2).
- Fairness is written as `WF_f(A)` and `SF_f(A)`.
- `Init ∧ □[N]_v ∧ F` is *machine closed* when `F` adds no safety property. That holds when `F` is a conjunction of WF and SF conditions on subactions of `N`.
- Reduction is only sketched: "The precise statement of the theorem is somewhat complicated, and will be given elsewhere" (§9.3).

Basis: documentation (preprint copy).

**Cohen and Lamport (1998).** Take `N = M ∨ E` (M is the operation being reduced, E the other actions), phase predicates `R` (before the non-mover X) and `L` (after it), and hypotheses 1(a)–(d): no phase initially; E preserves phases; no direct `L → R` step of M; phases disjoint.
- Theorem 1 additionally needs `R·E ⇒ E·R`, `E·L ⇒ L·E`, and the liveness hypothesis `Q`: "either (i) M must eventually terminate after the X step has occurred, or (ii) the entire system halts in a state in which execution of a finite number of L steps can complete the execution of M". The reason given is: "even though □I ∧ S̄^R is necessarily a safety property, ∃∃ v̄ : □I ∧ S̄^R need not be one".
- Corollary 2 drops `Q` for safety properties Π, given `L ⇒ Enabled(L⁺ ∧ ¬L′)`.
- Corollary 5 transfers fairness only under more commutativity, enabledness and `O ≜ ∀i: □◇⟨A_i ∧ M⟩_v ⇒ □◇⟨X⟩_v`. The authors write that hypothesis 3(a) "most severely limits the class of actions Ai to which we can apply the corollary".

Basis: documentation.

**Armada encoding** (`Armada/strategies/reduction/CohenLamportReductionSpec.i.dfy:308-328`). `ValidCohenLamportReductionRequest` conjoins 16 predicates. They correspond to the paper as follows:

| Armada predicate | Cohen–Lamport counterpart (derived mapping) |
|---|---|
| no phase in `init`; `phase1 ⇒ ¬phase2`; `CantGoDirectlyFromPhase2ToPhase1`; `PhaseUnaffectedByOtherActors` | 1(a)–(d) |
| `RightMoversCommute`, `LeftMoversCommute` (`:106`, `:137`) | 2(a), 2(b) |
| `LeftMoversAlwaysEnabled` (`:162-175`): from any reachable non-crashed `phase2` state, some sequence of the same actor's steps leaves `phase2` or crashes | Corollary 2's enabledness condition |
| `RefinementRelationReflexive`, `RefinementRelationTransitive`, `RightMoversPreserveStateRefinement`, `LeftMoversPreserveStateRefinement`, `ActionSequencesLiftable` | coupling to the refinement relation (the paper's coupling invariant `I`) |
| `NoStepsAfterCrash`, `LeftMoversEnabledBeforeCrash`, `RightMoverCrashPreservation`, `LeftMoverSelfCrashPreservation` | Armada-specific: undefined behavior is modelled as a crash |

`lemma_PerformCohenLamportReduction` (`CohenLamportReduction.i.dfy:29-44`) takes a behavior `lb` satisfying the spec and returns `hb`. In `hb` no non-crashed state is in either phase, `hb` satisfies the same spec, and `BehaviorRefinesBehavior(lb.states, hb.states, relation)` holds. The trusted refinement notion is defined in `Armada/spec/refinement.s.dfy:11-16, 45-70`: `BehaviorSatisfiesSpec(b:seq<State>, …)` and `SpecRefinesSpec` (`forall lb :: BehaviorSatisfiesSpec(lb, l_spec) ==> BehaviorRefinesSpec(lb, h_spec, relation)`). Behaviors are **finite sequences**, so the guarantee is safety. No `Q`, `O` or fairness transfer is needed, or available. The Armada paper confirms this: "Because Armada currently emits proofs about finite behaviors, it can prove safety but not liveness properties" (§8). It adds that refinement proofs "are meaningless if (1) the spec ever exhibits undefined behavior, or (2) the refinement relation R allows the low-level program to exhibit undefined behavior when the high-level program does not" (§3.2.3).

Basis: source + documentation + derived (the mapping table).

### 7. Mover types and yield sufficiency in CIVL

**Checks emitted** (`Source/Concurrency/MoverCheck.cs:50-121`). For every pair of mover actions whose layer ranges overlap:
- if `first` is a right mover: a commutativity checker and a gate-preservation checker (`CreateRightMoverCheckers`, `:143-147`);
- if `second` is an unconditional left mover: commutativity, gate preservation and failure preservation (`CreateLeftMoverCheckers`, `:149-154`);
- conditional left movers get the same three checks under their preconditions;
- every left mover gets a non-blocking checker, but `CreateNonblockingChecker` returns immediately `if (!action.HasAssumeCmd)` (`:378`). Only actions that can block by `assume` are checked.

The checkers are emitted as Boogie procedures, so verification conditions discharge them. No termination check for left movers appears among these checkers. Basis: source.

**Yield sufficiency** (`Source/Concurrency/YieldSufficiencyChecker.cs:23-57, 150-224`). Each yielding procedure is abstracted into a labelled graph with labels Y (yield), B, L, R, N (mover types), P (private), M (global modification) and A (async). The graph is checked by simulation against two automata:
- the **atomicity automaton** (states RM and LM): right and both movers stay in RM; L or N moves to LM; only Y returns to RM. Its error message is "Transactions must be separated by yields";
- the **async automaton**: no global modification between an async call and the next yield.

A loop whose back edge carries a yield label must have a yielding header, and a yielding inner loop requires a yielding parent loop header ("Loop header must be yielding at layer …", `:173`, `:188`). Basis: source.

**Soundness statements** (Kragl and Qadeer, 2018, author PDF):
- Safety is defined as "there is no failing execution, i.e., an execution that executes an atomic action whose gate evaluates to false".
- Theorem 1: "If MSafe(P) and CSafe(P), then Safe(P)".
- Corollary 2 chains this over the layers.
- The listed mover checks are commutativity, forward preservation, backward preservation, and "Nonblocking: If A is a left mover, then A cannot block". Termination is not among them.
- Liveness is outside the method: the paper contrasts CIVL with TLA+, which "is more general because it supports liveness specifications".

Basis: documentation.

**Inductive sequentialization** (Kragl et al., 2020):
- Refinement is summary inclusion plus failure propagation. Safety of arbitrary reachable states follows because "any non-terminating program can be abstracted by one that terminates after a nondeterministically chosen number of steps".
- The rule adds a *cooperation* premise (CO) that "strengthens the standard non-blocking conditions of left movers".
- The paper's counterexample is an async that re-spawns itself. It "satisfies all conditions except cooperation", and applying IS anyway "would result in a program that cannot fail, which is unsound".
- The implementation was about 2,500 lines of C#.
- GitHub code search for "cooperation" in `boogie-org/boogie` (default branch, 2026-11-21) returned no hits. Whether the pinned revision still contains the IS rule under another name was **not examined**.

Basis: documentation + source search.

**Elmas, Qadeer and Tasiran (2009).** From the abstract only: QED targets "the static verification of assertions and procedure specifications". It alternates abstraction and reduction "to compute larger atomic code blocks in a sound manner". The rules and the soundness theorem were not read.

### 8. IronFleet: where each assumption is written

| Assumption | Location | Status |
|---|---|---|
| Network may drop, duplicate, reorder and delay packets; receive only previously sent packets | `Common/Framework/Environment.s.dfy:22-25` (`sentPackets` is a `set`), `:69-78` (`LEnvironment_PerformIos`: every received packet is in `e.sentPackets`) | trusted spec |
| Network does not tamper, and packet header addresses are trustworthy | paper §2.5 | prose |
| Host step IO ordering that enables reduction: receives before sends, at most one time-dependent operation | `Environment.s.dfy:36-49` (`LIoOpOrderingOKForAction`: `io1.LIoOpReceive? \|\| io2.LIoOpSend?`); asserted in `Main.s.dfy:46-51` ("These obligations enable us to apply reduction"; `\|clocks\| <= 1`) | obligation machine-checked; **reduction argument informal** (paper §3.6) |
| Safety theorem | `Main.s.dfy:56-63` `RefinementProof(config, db:seq<DS_State>)`: each step maps to `Service_Next` or stutter | trusted statement over finite behaviors |
| Synchrony after `synchrony_start` within `latency_bound` | `EnvironmentSynchrony.s.dfy:149-159` `NetworkSynchronousForHosts` | predicate in trusted file, used as a hypothesis |
| No Zeno behavior; clock error at most `max_clock_ambiguity`; bounded delivery rate | `EnvironmentSynchrony.s.dfy:175-181`, `:210-219`, `:261-271` | same |
| Host scheduler runs each live replica at least every `host_period` | `Protocol/RSL/LivenessProof/Assumptions.i.dfy:126-135` `HostExecutesPeriodically` | hypothesis (untrusted file) |
| Conjunction of all of the above, plus a persistent client that never gets a reply | `Assumptions.i.dfy:202-258` `LivenessAssumptions` | hypothesis of `lemma_EventuallyLiveReplicaExecutesClientRequest` (`LivenessProof.i.dfy:38-60`) |
| Trusted toolchain: Dafny, .NET compiler and runtime, Windows | paper §2.5 | prose |

Basis: source + documentation.

**Consequences** (derived).
- A reader who audits only the trusted `.s.dfy` files sees a safety theorem and the definitions of the synchrony predicates. They do not see the liveness claim or which predicates it assumes. Those live in `Assumptions.i.dfy` and `LivenessProof.i.dfy`.
- The liveness lemma is phrased with a persistent client that "never receives a reply" among its hypotheses, and it concludes that a live replica executes the request. To read it as "eventually replies", the reader must also accept the reply-delivery steps elsewhere in the proof.
- IronFleet does not use WF/SF. It "adopt[s] always-enabled actions" and acknowledges that this "can admit specifications that are not machine closed", arguing that an existing implementation shows the property is implementable (§4.2).
- Scheduler fairness is discharged by structure: the round-robin `HostNext` makes each of `n` actions run "with frequency F/n" (§4.3).

### 9. Fairness notions differ in strength and behavior

- **Apt, Francez and Katz (1988; technical-report copy)** propose three criteria for appraising a fairness notion:
  - *feasibility*: every finite prefix extends to a fair computation;
  - *equivalence robustness*: invariance under interchanging independent actions;
  - *liveness enhancement*: some program with an infinite computation has only finite fair computations.
- Fairness assumptions "are known not to affect partial correctness or, more generally, safety properties".
- Their results for CSP: "although all six possibilities are feasible, only Strong Process fairness is both equivalence robust and liveness enhancing". "None of the commonly used notions" is fully acceptable with n-way synchronization.
- *Equivalence robustness* is the fairness-side counterpart of POR: a fairness notion that is not equivalence robust can make two trace-equivalent interleavings disagree. That would break a reduction that keeps only one representative (derived).
- Brunner and Lammich note that the only earlier mechanization of POR (Chou and Peled 1996) "is restricted to a specific fairness assumption". Peled's 1993 abstract says the method "allows model checking under fairness assumptions".

Basis: documentation + derived.

### 10. Audit checklist for a published concurrency result

1. **Relation.** What is proved between the real system and the reduced or abstract one? The options include finite-behavior inclusion (Armada, IronFleet safety, CIVL), stutter-equivalent infinite languages (AFP POR), and a branching equivalence. Is the relation stated in a trusted file or theorem, or only in prose?
2. **Property class.** Is the conclusion's logic closed under that relation? Checks: next-free for stutter equivalence; safety for finite-behavior inclusion; next-free branching-time logic only with a branching-preserving condition.
3. **Infinite versus finite.** Are runs infinite? If so, how are deadlocks handled (stutter extension, a totality assumption)? If finite, liveness is out of scope.
4. **Cycle proviso.** For state-space reductions, how is "no ignored action forever" ensured (well-founded rank, sticky edges, a stack proviso)? Is it inside the theorem?
5. **Mover side conditions.** Are left movers non-blocking (all of them, or only those with `assume`)? Is termination or cooperation required, and where is it checked?
6. **Scheduler model.** Is the scheduler a parameter of every theorem? Does the result hold for all schedules or for a restricted one, and is the restriction named in the statement?
7. **Fairness.** WF, SF, always-enabled, or "infinitely often"? Is it machine closed or otherwise implementable? Does it pass the Apt–Francez–Katz equivalence-robustness test where reduction is used?
8. **Environment.** Network (loss, duplication, tampering), clocks, synchrony after a start time, rate bounds: is each a trusted definition, a lemma hypothesis, or prose?
9. **Informal steps.** Which proof steps are informal (IronFleet's reduction), paper-only (Cohen–Lamport, CIVL soundness), or mechanized?
10. **TCB.** Proof assistant, code generator, compiler, OS, and memory model (Armada: x86-TSO, with "We currently assume that the CompCertTSO model refines our own").

### 11. Cost and resource footprint (L1–L6)

| Level | Quantity | Value | Basis |
|---|---|---|---|
| L1 | Brunner–Lammich POR formalization | about 15 person-months; about 13k lines (6k abstract POR, 7k SM language and analysis); about 1,000 lines for the abstract correctness theorem | cited (manuscript §3.6, §3.10) |
| L1 | IronFleet | Spec 1,400, Impl 5,114, Proof 39,253 SLOC; proof-to-code 3.6:1; about 3.7 person-years for the methodology and two systems | cited (paper Fig. 12, §7.1) |
| L1 | Armada | proof library 5,618 SLOC; 24,540 SLOC of generated proof across recipes; queue case about 6 person-days | cited (paper §5–6) |
| L1 | Inductive sequentialization benchmarks | 225–1,168 total LOC per example; IS-specific 65–534 LOC | cited (Table 1) |
| L3 | IronFleet verification | 395 minutes in total (hardware not named in the parts read) | cited |
| L3 | IS benchmarks | 0.9–4.2 s per example (hardware not named) | cited |
| L3 | Armada verification time; CIVL layered examples | not found in the text read | — |
| L4 | IronRSL vs Go MultiPaxos baseline | peak throughput "within 2.4×" | cited |
| L4 | IronKV vs Redis | "competitive" | cited |
| L4 | Armada queue (CompCertTSO) vs liblfds (GCC) | 70% throughput | cited |
| L4 | CAVA vs SPIN, Mulog n=3, states without → with POR | CAVA 5,205,376 → 2,779,218 (×1.87); SPIN 2,376,180 → 1,171,578 (×2.03); SPIN "shorter execution times (roughly factor 400)" | cited (Fig. 3) |
| L6 | Source size at the pins | AFP `Partial_Order_Reduction`: 24 files, 5,758 lines; `Stuttering_Equivalence`: 3 files, 1,665 lines; `CAVA_LTL_Modelchecker/SM`: 24 files, 6,375 lines; Armada `strategies/reduction`: 9 files, 10,292 lines; IronFleet trusted framework `.s.dfy`: 6 files, 636 lines; IronRSL `LivenessProof`: 36 files, 12,389 lines; Boogie `Source/Concurrency`: 21 files, 7,251 lines | measured (`probes/tree_sizes.py`) |
| L2, L5 | Toolchain build time; independent proof-checking throughput or memory | not measured | — |

The AFP line count (5,758) is close to the "6k lines for abstract partial order reduction" reported in the manuscript. That consistency is derived; the two may not cover identical file sets.

### 12. Comprehensibility (C1) and model refinement (C2)

**C1.** The cognitive load sits in the *relation*, not in the reduction algorithm. A reader must keep three things apart: which logic is closed under which equivalence; whether runs are finite or infinite; and which file, trusted or not, states each assumption. The mechanized developments differ in how legible they make these:
- **AFP/CAVA** is the most legible: the property class appears in the statement (`next_free φ`), and the tool enforces it (`TY_ERR`).
- **Armada and IronFleet** encode the class only through a type (`seq<State>`). That is easy to miss, so the paper prose is needed.
- **CIVL's** guarantees are spread across C# checker generators. Reading `MoverCheck.cs`, one finds, for example, that non-blocking is checked only for actions with `assume`.

Diagnostics also differ:
- CIVL reports which commutativity or gate check failed, with locations.
- Armada reports a failed Dafny lemma inside a generated proof.
- The AFP chain reports only `TY_ERR` for an unsupported formula; it gives no explanation of which subformula used next-time.

**C2, one model for all of them.** Every development here proves a simulation *up to stuttering* between the original and the reduced system, for an observation (visible propositions or a refinement relation). The preserved property class is the class of properties invariant under that relation:

| Relation | Preserved properties |
|---|---|
| finite-prefix stuttering simulation | safety (Armada, IronFleet safety, CIVL) |
| stutter-equivalence of infinite traces | next-free LTL (AFP POR, TLA formulas) |
| stuttering bisimulation-style relation | next-free branching-time logic (Gerth et al.) |

Scheduler and fairness assumptions are restrictions of the behavior set on one side of the relation. With that view, the special cases become parameters:
- the cycle proviso is what makes the infinite-trace relation hold;
- `Q` and `O` in Cohen–Lamport are what make the existentially projected spec closed under the relation;
- the singleton condition is what lifts trace equivalence to a branching relation.

Making the relation and the behavior restriction explicit arguments of the top-level theorem would turn the audit checklist into type checking. The complexity does not disappear, though: it moves into proving the relation, which is where the 13k AFP lines and the 10k Armada lines go.

### 13. Validation (V1–V4)

- **V1 (adequacy of statements).**
  - Brunner and Lammich found a counterexample to a lemma in the published proof of the dynamic ample-set algorithm while mechanizing it.
  - Brunner's dissertation reports that related problems "later found out to also cause incorrect behavior of the algorithm and affect results of the Spin model checker". This is cited second-hand ([Sie19] there) and was not examined.
  - Armada's caveat about undefined behavior in the spec is an adequacy limit stated by its authors.
- **V2 (checker and lowering).** CAVA's chain covers generated SML, but the SML compiler is outside it. IronFleet trusts Dafny, .NET and Windows. Armada trusts Dafny, Boogie, Z3 and the CompCertTSO-refines-Armada assumption. No differential testing of these reductions was found.
- **V3 (concurrency reality).** IronFleet's atomicity reduction from real interleaved IO to atomic host steps is informal. Armada assumes x86-TSO and is "not directly applicable to other architectures, like ARM and Power".
- **V4 (empirical).** IronFleet and Armada report runtime performance measurements (§11). No study of how readers interpret where these assumptions are placed was found.

## Boundaries

- **Not examined (full text unavailable to the tools used):**
  - Peled 1993: condition wording; the restriction to next-free LTL; counterexamples.
  - Peled–Wilke 1997: theorem statement and translation size.
  - Gerth et al. 1999: the exact branching-time condition and equivalence.
  - Elmas–Qadeer–Tasiran 2009: proof rules, soundness theorem, benchmarks.
  - Lipton 1975: beyond the Crossref abstract.
- **Not built or rechecked:** no Isabelle, Dafny or Boogie run was performed. That the theorems are proved at the pinned revisions is assumed from their presence in the AFP, and from the repositories' own verification processes. It was not re-established here.
- **Toy model:** the three cases show that particular condition violations change a verdict on hand-built systems. They do not show that any real tool has these defects. The toy's C4 is the singleton rule. It is used as a hypothesis, not as Gerth et al.'s verified condition.
- **CIVL at the pinned revision:**
  - Whether inductive sequentialization and its cooperation check exist under another name: unknown.
  - Whether some other component checks termination of left movers: not found in `MoverCheck.cs`, `YieldSufficiencyChecker.cs`, `CivlTypeChecker.cs` or `NoninterferenceChecker.cs`, and not searched exhaustively.
- **IronFleet's IronKV liveness assumptions** (`Protocol/LiveSHT/LivenessProof/Assumptions.i.dfy`): not examined beyond the paper's summary.
- **Paper copies:** Lamport's TOPLAS paper (1993 preprint), Apt–Francez–Katz (1988 technical report) and Brunner–Lammich (dissertation manuscript) may differ from the published versions in pagination and minor text.
- **Attractive but unsupported conclusions:**
  - "POR is sound for LTL." It is sound for next-free LTL, under the cycle proviso, over infinite runs.
  - "Armada/CIVL verify liveness." Both are safety-only by construction.
  - "IronFleet's top-level theorem includes liveness." It does not; liveness is a separate lemma under explicit hypotheses.
  - "Non-blocking left movers suffice for every mover-based rule." Inductive sequentialization shows otherwise.

## Evidence

All observations were made on 2026-11-21 (UTC). Source revisions are listed in `REPORT.json`.

**Source.**
- `isabelle-prover/mirror-afp-devel@523cdc72b5ae4a91c9ab8e1025d4a30b40472720`:
  - `thys/Partial_Order_Reduction/Ample_Correctness.thy:1-39`; `Ample_Abstract.thy:18-80, 681-703`; `Formula.thy:1-32`; `Transition_System_Traces.thy:46-54`; `Transition_System_Interpreted_Traces.thy:9-17`; `Transition_System_Extensions.thy:96-106`; `ROOT`.
  - `thys/Stuttering_Equivalence/PLTL.thy:150, 186, 742, 779, 825`; `StutterEquivalence.thy:13`.
  - `thys/CAVA_LTL_Modelchecker/CAVA_Impl.thy:1223-1272`; `SM/Impl/SM_Wrapup.thy:37-40`; `SM/RefPoint/Gen_Scheduler.thy:69-70`; `SM/RefPoint/SM_LTL.thy:12-13`.
- `microsoft/Armada@da7497dcf506417df1899ac58850706a31e3acd5`:
  - `Armada/strategies/reduction/CohenLamportReduction.i.dfy:1-46`; `CohenLamportReductionSpec.i.dfy:35-60, 106, 137, 151-175, 308-328`; `AtomicReduction.i.dfy:42-79`; `AtomicReductionSpec.i.dfy:446-471`; `RefinementViaReduction.i.dfy:1-20`.
  - `Armada/spec/refinement.s.dfy:1-72`; `Armada/strategies/refinement/AnnotatedBehavior.i.dfy:12-15`.
- `boogie-org/boogie@99eebd60b8fc42c0ad3c95b6160ad88ac4f124dc`: `Source/Concurrency/MoverCheck.cs:50-154, 374-429`; `Source/Concurrency/YieldSufficiencyChecker.cs:13-57, 150-224`.
- `microsoft/Ironclad@2fe4dcdc323b92e93f759cc3e373521366b7f691`, all under `ironfleet/src/Dafny/Distributed/`:
  - `Common/Framework/Main.s.dfy:14-63`; `DistributedSystem.s.dfy:31-60`; `Environment.s.dfy:8-128`; `EnvironmentSynchrony.s.dfy:84-271`;
  - `Protocol/RSL/LivenessProof/Assumptions.i.dfy:126-258`; `Protocol/RSL/LivenessProof/LivenessProof.i.dfy:38-60`.
- Code searches used GitHub code search (default branches) to locate files. Every cited line was then read at the pinned revision.

**Literature.** All DOIs in `REPORT.json` were checked against Crossref metadata on 2026-11-21 (title, authors, venue, pages):
- Read in full or in substantial part:
  - Lamport 1994 (author preprint, lamport.azurewebsites.net; preprint pages);
  - Cohen–Lamport 1998 (author copy; LNCS pages 317–331);
  - Kragl–Qadeer 2018 (author PDF at civl-verifier.github.io; pages 1–23);
  - Kragl et al. 2020 (author PDF; proceedings pages 227–242);
  - Hawblitzel et al. 2015 (author PDF; pages 1–17);
  - Lorch et al. 2020 (author PDF; proceedings pages 197–210);
  - Brunner–Lammich 2018 (author manuscript in J. Brunner's TUM dissertation, mediatum.ub.tum.de document 1622049; manuscript pages 1–19);
  - Apt–Francez–Katz 1988 (University of Texas at Austin technical report TR-88-10).
- Abstract or metadata only: Peled 1993; Peled–Wilke 1997; Gerth et al. 1999; Elmas et al. 2009; Lipton 1975.
- Secondary context: Siegel and Yan, CAV 2020, DOI `10.1007/978-3-030-53291-8_6` (abstract).

**Execution.**
- `support/probes/por_toy.py` (toy model, standard-library Python): recorded output in `support/outputs/por_toy.txt`, run with Python 3.13.15.
- `support/probes/tree_sizes.py` (counts lines and bytes of files fetched at the pins through the GitHub API and raw file host): output in `support/outputs/tree_sizes.txt`.

## Revalidation

- **AFP POR scope:** at a new AFP revision, check `Ample_Correctness.thy` for the locale parameters (`formula_next_free`, `ample_abstract`) and the statement of `reduction_correct`, and check `ample_set_def` in `Ample_Abstract.thy`. Then check `cava_sm_def` in `CAVA_Impl.thy`: the `ltlc_next_free` guard must still yield `TY_ERR`.
- **Armada:** check that `refinement.s.dfy` still defines behaviors as `seq<State>`; an `imap` or stream type would signal liveness support. Diff `ValidCohenLamportReductionRequest`.
- **CIVL:** in `MoverCheck.cs`, check the `HasAssumeCmd` early return in `CreateNonblockingChecker` and the set of checkers emitted per mover pair. Search the tree for "Cooperation" or "InductiveSequentialization" to locate the IS rule.
- **IronFleet:** check whether a liveness statement has moved into `Main.s.dfy`. Diff `LivenessAssumptions` and the four synchrony predicates. Check whether the reduction obligation is still only asserted in `Main.s.dfy`.
- **Toy phenomena:** rerun `python3 support/probes/por_toy.py`. The expected verdict pairs are (False, True), (False, True) and (True, False), with C3, C0–C3 and C4 flags as recorded. To test a real POR tool, encode the same three systems in its input language and compare full and reduced verdicts.
- **Literature gaps:** the cheapest next step is to obtain the Gerth et al. (1999) and Peled–Wilke (1997) full texts and confirm the branching-time condition and the translation result.
