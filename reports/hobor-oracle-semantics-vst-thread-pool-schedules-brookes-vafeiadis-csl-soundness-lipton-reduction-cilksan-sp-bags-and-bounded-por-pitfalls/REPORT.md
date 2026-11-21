# Scheduler and interleaving completeness: oracle and explicit-schedule machines, CSL parallel composition, reduction and determinacy theorems, series–parallel race detection, and the soundness limits of reduced and bounded exploration

## Summary

- **"For every schedule" is only as strong as the schedule space.** Each examined system makes its completeness argument in one of four ways:
  - **Interleaving by construction.** Iris's thread-pool step relation lets *any* thread at *any* list position step, and the VST fine-grained machine accepts *any* finite list of thread ids as a schedule.
  - **A proved reduction theorem.** VST's `x86SC_safe` derives fine-grained safety for every schedule from coarse-grained safety for every schedule.
  - **An assumption.** Hobor–Appel–Zappa Nardelli interleave only at lock, unlock and fork. They justify this by race-freedom and explicitly defer the equivalence with preemptive execution.
  - **An environment parameter.** CCAL quantifies over environment contexts that satisfy a rely condition.

  Basis: source + documentation.
- **Nested parallel composition needs an independent choice at every nesting level.** Brookes's trace semantics (a "mutex fairmerge" of the two arms) and Vafeiadis's operational rules (`Par1`/`Par2`: either arm may step) place no restriction on which arm of a nested `∥` may step. A step rule that passes *one* scheduler bit down through every nested `∥` node violates `Par1`/`Par2` at inner nodes. In a self-written toy model, such a scheduler generates 24 of the 90 interleavings of `(a ∥ b) ∥ c` (two actions per arm). It also lowers the maximum number of simultaneously live cells from 3 to 2. The final memory is unchanged for race-free arms. Under a per-node path selector, all 90 interleavings come back. Basis: documentation + execution (toy model, not any published system).
- **Reduction and determinacy theorems license fewer schedules only for particular observables.**
  - Lipton reduction preserves "halting" (abstract), or partial correctness and deadlock-freedom (Lamport–Schneider's restatement). It does not preserve liveness.
  - The SP-bags theorem (Feng–Leiserson) detects a determinacy race "if and only if a determinacy race exists" for the given input under one serial execution.
  - DPOR (Flanagan–Godefroid) preserves deadlocks and safety violations on acyclic state spaces.
  - Source-set/optimal DPOR explores at least one (optimal: exactly one) execution per Mazurkiewicz trace.

  None of these results is about peak resource use read off explored states. A license for final states or fault-freedom does not transfer to such quantities without a separate argument. Basis: documentation + derived.
- **Reduced and bounded exploration has documented failure modes, and two of them were reproduced on real tools.**
  - **Spin 6.5.3 (built from the pinned source).** With its default makefile (`CFLAGS?=-O2 -DNXT ...`), Spin accepts the next-time operator in an inline `ltl` formula. Its stutter-invariance warning is compiled out when `HAS_LTL` is defined. On a two-process model, the default partial-order-reduced search reports `errors: 0` for `X (g == 0)`, while `-DNOREDUCE` reports the violation. No warning is printed. The release notes say that `-DNXT` "jeopardizes compatibility with the partial order reductions".
  - **Loom (pinned revision).** With `LOOM_MAX_PREEMPTIONS=1`, a bug that needs two preemptions passes silently after 21 executions. It is found with bound 2, and the unbounded search explores 234 executions.
  - **Naive DPOR with preemption bounding (Coons et al.).** It "misses parts of the state space reachable in the bound". Loom's source adds the conservative extra backtracking point that Coons et al. propose as the fix.

  Basis: source + execution + documentation.
- **A published, mechanized model excluded a behaviour that real hardware exhibits.** The POPL 2009 x86-CC model forbade test `n6`. Its own in-press addendum reports a witness "approximately one witness in 2 ∗ 10^6 executions" on an Intel Core 2. x86-CC also allowed IRIW, which the vendors then moved to forbid. The replacement was x86-TSO. Basis: documentation.

## Applicability

The report compares independent subjects; it does not study their combination. All scheduling statements assume sequential consistency unless they explicitly mention x86-CC, x86-TSO or CompCertTSO.

- **Mechanized concurrent semantics, read at source.**
  - VST: `PrincetonUniversity/VST` at the pinned revision. Files: `concurrency/common/HybridMachineSig.v`, `threadPool.v`, `scheduler.v`, `concurrency/sc_drf/Coarse2Fine_safety.v` and `concurrency/main.v`.
  - Iris: the GitHub mirror `rocq-iris/iris`, whose repository description says it "is a mirror of https://gitlab.mpi-sws.org/iris/iris", at the pinned revision. Files: `iris/program_logic/language.v`, `adequacy.v` and `iris_heap_lang/lang.v`.

  These are the studied snapshots. Behaviour at other revisions is not claimed.
- **Race detection and exploration tools, read at source and executed.**
  - OpenCilk Cilksan: `OpenCilk/productivity-tools`, source only. It was not built, because it needs the OpenCilk compiler.
  - Spin: `nimble-code/Spin`, built from source, version string `Spin Version 6.5.3 -- 3 November 2026`. To build it without a system `yacc`, the pinned `ThomasDickey/byacc-snapshots` revision was used as the parser generator. byacc plays no other role.
  - Loom: `tokio-rs/loom`, used as a git dependency at the pinned revision.

  Execution host: x86-64 Linux (kernel 7.1.6), 96-core Intel Xeon @ 2.60 GHz, gcc 15.2.0, rustc 1.102.0-nightly (3ef0c22cd 2026-11-11).
- **Literature.** The papers listed in `REPORT.json` and **Evidence** were read in the versions stated there. Lipton 1975, Steele 1990 and Valmari 1991 are known here only through abstracts and secondary restatements. For CompCertTSO and Source Sets, the POPL conference versions were read, not the journal versions whose DOIs are cited. Numbers from those papers are labelled accordingly.
- **Toy model.** `support/toy/nested_par_schedulers.py` is a self-written model of three ways to resolve `∥` nondeterminism. Its results characterise schedulers of that shape. They are not measurements of VST, Iris, or any published semantics.

## Findings

### 1. How mechanized semantics represent scheduling, and what connects it to all interleavings

| System | Representation of nondeterminism | Thread creation / nesting | What connects modelled schedules to every interleaving | Status |
|---|---|---|---|---|
| VST hybrid machines | Explicit `schedule := seq nat` (list of thread ids) consumed by `machine_step` | Flat pool; `addThread`/`latestThread`; spawn is a sync step | Fine machine: any `seq nat` is a schedule, and a missing tid is skipped (`schedfail`). Coarse machine: `csafe` quantifies `forall U''` after every sync step. `x86SC_safe` derives erased fine-grained safety under an arbitrary schedule `U` from coarse safety for all schedules | Proved, but conditional on the hypotheses below |
| Hobor–Appel–Zappa Nardelli (ESOP 2008) | An oracle that "contains the state of all the other threads (and the schedule)". The machine state has a schedule given as "a (finite) list of thread-ids" | `fork e (e)`; no join primitive | Quantifies over all schedules, but switches threads only at concurrent operations. The paper itself calls this "coroutine model" "in general … not equivalent to execution on a real machine". Equivalence for well-synchronized programs is asserted, not proved | Assumed |
| Iris (JFP 2018; mirror source) | Nondeterministic `step` on a configuration `(list expr * state)` | `prim_step` returns forked threads `efs`, which are appended to the pool. HeapLang has only `Fork`; there is no primitive `∥` | `step_atomic` picks `e1` at an arbitrary split `t1 ++ e1 :: t2`. Adequacy quantifies over `rtc erased_step` | By construction |
| CCAL (Gu et al., PLDI 2018) | Environment contexts `E ∈ Id ⇀ Strategy`, which include a scheduler strategy, over a global log | Participants in a set `A`; the rest is environment | Soundness `L′[D] ⊢R M : L[D] ⇒ ∀P, [[P ⊕ M]] ⊑R [[P]]` quantifies over *valid* environment contexts (rely conditions such as a fair scheduler) | Relative to rely |
| CompCertTSO (POPL 2011 version read) | Thread-local labelled semantics composed with one TSO machine | Threads of a TSO machine | "We use the TSO semantics for software threads, not hardware threads, which is sound provided that the scheduler flushes the buffer during task switching" | Assumed (stated proviso) |

Basis: source (VST, Iris) + documentation (papers).

**1.1 VST explicit schedules (source).** `HybridMachineSig.v` defines:

```coq
Definition schedule := (seq nat).                                (* line 250 *)
Definition schedPeek sch: option nat:= match sch with nil => None | cons hd tl => Some hd end.
Definition schedSkip sch: (seq nat):= List.tl sch.               (* line 259 *)
Class Scheduler := { isCoarse : bool; yield: schedule -> schedule}.  (* 314-316 *)
```

Every constructor of `machine_step` (lines 319–364) reads `schedPeek U = Some tid`:
- `start_step`, `resume_step` and `thread_step` move to `yield U`.
- `suspend_step` and `sync_step` move to `schedSkip U`.
- `schedfail` (lines 357–364) skips a tid that is not in the pool.

The coarse machine sets `yield := fun x => x` (lines 571–573). A thread therefore runs until its next synchronization step, so schedules choose only *which thread resumes after a sync*. The fine machine sets `yield := fun x => schedSkip x` (lines 761–763), which consumes one list entry per step. The coarse safety predicate quantifies over every continuation schedule at each sync point:

```coq
| AngelSafe: forall tp' m' n (tr: event_trace)
    (Hstep: MachStep st m (schedSkip (fst (fst st)),(snd (fst st)) ++ tr,tp') m')
    (Hsafe: forall U'', csafe (U'',(snd (fst st)) ++ tr,tp') m' n),   (* lines 599-601 *)
  csafe st m (S n).
```

The source comment at lines 729–730 says so directly: "csafe guarantees safety for any rearrangement of the schedule at synchronization points, while this fixes a particular schedule."

**1.2 The VST coarse-to-fine theorem and its hypotheses (source).** `concurrency/sc_drf/Coarse2Fine_safety.v`, `Lemma x86SC_safe` (lines 68–93), takes this hypothesis:

```coq
(Hcsafe: forall n sched, csafe ... (sched, nil, init_tpc_target) ... n)
```

and concludes `forall n, fsafe ... init_tp_bare ... U n`. Here `U` is a section variable (line 51), so it is universally quantified. The theorem is the formal bridge from "safe for every coarse schedule" to "safe for every fine-grained schedule of the erased machine". Its hypotheses are not all discharged:
- **Unproved section context.** Lines 59–61: "We don't really have an instance for that, it would require to prove that the initial memory has no invalid pointers", followed by `Context {FI : FineInit}`. Line 62 adds `Variable em : ClassicalFacts.excluded_middle`.
- **The end-to-end theorem rests on axioms.** In `concurrency/main.v`, `top2bottom_correct` (lines 68–95) ends with `forall (U:schedule), exists ... spinlock_safe U tgt_cpm tgt_m`. It rests on `Axiom CompCert_compiler` and `Axiom simpl_clight_semantic_preservation` (lines 11–16). In the same file, `entry_point_problem` is closed with `Admitted` (line 60), under the comment "Initial states are inconsistent" (line 37) and "TODO: fix initial state inconsistenciees and unify" (line 80).
- **Not part of the default build.** In the `Makefile`, the `vst` target is `vst: _CoqProject msl veric floyd simpleconc` (line 768). CI (`.github/workflows/coq-action.yml`) builds `make_target: vst`. `concurrency/sc_drf` appears only in the `coqdep` dependency scan (line 929), not in any file list that a default target builds. Whether `x86SC_safe` and `top2bottom_correct` check with the pinned toolchain is **not examined**.

Basis: source.

**1.3 Hobor oracle semantics (documentation, ESOP 2008, author full text).**
- **The oracle.** "The oracle contains the state of all the other threads (and the schedule) and calculates what they do when control is yielded. Since our programs are (proved) race-free, preemptive schedules will yield equivalent results."
- **The concurrent machine state.** "A concurrent machine state S = (… ; ~θ; L; m) has a schedule …, a (finite) list of thread-ids", and "We will be quantifying over all schedules".
- **The completeness argument is explicitly incomplete.** The paper calls its interleaving-at-concurrent-operations model a "coroutine model of concurrency" that "in general … is not equivalent to execution on a real machine". It justifies the model by well-synchronization and leaves the proof as future work.
- **Mechanization.** "All definitions and claims have been fully machine-checked, except that the Coq proofs for Sections 8 and 9 are incomplete; these sections have been proved by hand." The concurrent and oracle machines take 1,331 lines of specification and 14,430 lines of proof, out of 42,277 lines in total.

**1.4 Iris thread pool (source).** `iris/program_logic/language.v` lines 105–110:

```coq
Inductive step (ρ1 : cfg Λ) (κ : list (observation Λ)) (ρ2 : cfg Λ) : Prop :=
  | step_atomic e1 σ1 e2 σ2 efs t1 t2 :
     ρ1 = (t1 ++ e1 :: t2, σ1) →
     ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
     prim_step e1 σ1 κ e2 σ2 efs →
     step ρ1 κ ρ2.
```

`adequacy.v` lines 180–188 define `adequate` by quantifying over `rtc erased_step ([e1], σ1) (t2, σ2)`, so the theorem covers every interleaving at `prim_step` granularity. HeapLang's only concurrency primitive is `ForkS` (`lang.v` lines 716–717: `base_step (Fork e) σ [] (Val $ LitV LitUnit) σ [e]`). Nested parallelism is therefore a library construction over a flat pool, and no nested scheduler exists to get wrong. Basis: source.

### 2. Nested parallel composition in CSL semantics and the one-choice-per-step pitfall

**2.1 Normative rules (documentation).**
- **Brookes (TCS 2007).** The grammar allows nested `c1∥c2`. The paper says it reformulates O'Hearn's rules "allowing nested resource declarations and nested parallel compositions". `∥` denotes the set of "mutex fairmerges". The inductive clause is `(λ1α1)A1 ∥A2 (λ2α2) = {abort | λ1 ⋈ λ2} ∪ {λ1β | …} ∪ {λ2β | …}`, so the next action may come from either arm, and an interfering pair aborts. The Parallel rule splits the precondition as `p1 ∗ p2` under side conditions on free and written variables. The proof is a paper proof; the examined text mentions no mechanization.
- **Vafeiadis (MFPS 2011).** The rules are `(Par1) C1,σ → C1′,σ′ ⟹ (C1∥C2),σ → (C1′∥C2),σ′`, the symmetric `(Par2)`, and `(Par3) (skip∥skip),σ → skip,σ`, with abort propagation in `ParA1`/`ParA2`. The multiple-resource variant adds `(RaceDetect)`, which aborts when accesses intersect writes. Safety `safe_n` is step-indexed, and the soundness proof is "formalised in Isabelle/HOL". The Par case is Lemma 4.9 ("The operational semantics has three possible transitions for C1∥C2").

**2.2 What a one-bit scheduler violates (derived).** Suppose each step supplies one bit `b`, and every `∥` node routes to its left child when `b = 0` and to its right child when `b = 1`, using the same `b` at every nesting level. A finished side forces the other side. Then in `(a ∥ b) ∥ c` with both `a` and `c` unfinished, bit 0 always reaches `a` and bit 1 always reaches `c`. Arm `b` can step only after `a` or `c` has finished. This is a direct violation of `Par2` at the inner node. The inner configuration `(a′ ∥ b)` can never take the `b` step while the outer sibling is unfinished, although `Par2` licenses it.

**2.3 Toy-model measurements.** Basis: execution (toy model of three scheduler shapes, not of any published system). Command: `python3 support/toy/nested_par_schedulers.py`. Output, also in `support/toy/output.txt`:

| Program (each arm's actions) | Scheduler | Distinct traces | Final memories | Peak simultaneously live cells | Traces missing vs. full |
|---|---|---|---|---|---|
| `(a∥b)∥c`, each arm alloc+free its own cell | full interleaving | 90 | 1 | 3 | 0 |
| same | one bit per step | 24 | 1 | **2** | 66 |
| same | per-node path selector | 90 | 1 | 3 | 0 |
| `a∥(b∥c)`, same arms | one bit per step | 24 | 1 | 2 | 66 |
| `(a∥b)∥c`, three racy writes to one cell | full / one bit / path | 6 / 4 / 6 | {1,2,3} in all three | — | 0 / 2 / 0 |
| `((a∥b)∥c)∥d`, disjoint writes | full / one bit / path | 24 / 8 / 24 | 1 | — | 0 / 16 / 0 |

Derived checks: 90 = 6!/(2!)³ interleavings of three 2-action arms, and 24 = 4! orders of four single-action arms. In these examples, the one-bit scheduler kept every *final state*, including the racy case, but lost the *peak* and two thirds or more of the traces. The missing traces include every order that starts with `b` in the racy example. Two consequences follow.
- **Robust vs. non-robust quantities.** A safety or final-state theorem quantified over the one-bit scheduler can coincide with the full-interleaving statement for race-free partitioned arms. A quantity read off the explored state space, such as the peak resident set or dynamic memory peak, is not robust. **Unknown:** whether the final-state coincidence holds in general.
- **Associativity.** The one-bit scheduler is not invariant under re-association of `∥` in general, because which traces it drops depends on the tree shape. Here the two shapes lose the same number of traces. A semantics whose `∥` is meant to be associative should exhibit identical trace sets for both shapes, and a trace-set comparison across shapes is a cheap adequacy test.
- **Remedies.** Either give each `∥` node an independent choice (the path selector), or flatten `∥` into a thread pool as Iris and VST do. Both recover all 90 traces here.

### 3. Theorems that license considering fewer schedules

| Result | Hypotheses | Conclusion (what is preserved) | Licenses replacing "every interleaving" by a restricted schedule set for race-free partitioned `∥`? | Final state | Fault freedom | Peak resources |
|---|---|---|---|---|---|---|
| Lipton 1975 (via Lamport–Schneider 1989) | `S = S1;…;Sk`: `S1…Si−1` right movers, `Si+1…Sk` left movers. From any started state, `S` can terminate using only its own actions | Π and Π/S "satisfy the same partial correctness and deadlock-freedom properties". The abstract says "properties such as halting". Hypothesis 3 is not needed for partial correctness. Liveness is **not** preserved (Lamport–Schneider's semaphore counterexample) | Yes, for atomicity coarsening, if each arm's actions are movers relative to the others. Disjoint footprints make all non-synchronizing actions both-movers | Yes (partial correctness) | Deadlock-freedom yes; abort/race freedom needs a separate argument | No statement |
| Steele 1990 (secondary sources only) | Operations that are not causally related "must commute or are prohibited" | Determinacy. Enforcement is dynamic ("Violations … can only be detected during a program's execution") | Yes, in principle: if all concurrent operations commute, every schedule gives the same result | Yes | — | No statement |
| Feng–Leiserson 1997 (SP-bags) | "Pure" Cilk programs (spawn/sync only), one input, one serial depth-first execution | "Theorem 10 The SP-bags algorithm detects a determinacy race in a Cilk program if and only if a determinacy race exists." `O(T α(v,v))` time, `O(v)` space | It certifies race-freedom *for that input*, and race-free SP programs are determinate. The paper adds: "not a program verifier … cannot certify that the program is race free for all inputs" | For that input | For that input | No statement |
| VST `x86SC_safe` | Coarse `csafe` for all schedules, plus `FineInit` (assumed) and excluded middle | Erased fine machine `fsafe` under any schedule `U` | Yes, for safety of the erased SC machine | Not stated | Yes (fsafe) | No |
| DPOR (Flanagan–Godefroid 2005) | Finite process set, deterministic processes, acyclic state space, only visible operations block | "guaranteed to detect every deadlock and safety-property violation in any acyclic state space" (persistent sets, Theorem 1) | Yes, for safety and deadlock on acyclic spaces | Yes (local states reachable) | Yes | No |
| Source-DPOR / optimal-DPOR (Abdulla et al.; POPL 2014 version read) | Acyclic, bounded-length executions; for presentation, processes do not disable each other | Some execution in every Mazurkiewicz trace is explored; optimal-DPOR "explores exactly one interleaving per Mazurkiewicz trace" | Yes, for trace-invariant properties | Yes | Yes | Only if the quantity is a function of the Mazurkiewicz trace |

Basis: documentation + derived. The derived column assignments follow from each conclusion. A property is licensed only if it is preserved by the stated equivalence (same trace, same partial-correctness behaviour, or local-state reachability). A peak over *intermediate* states is in general not a function of the final state, and two linearizations of one Mazurkiewicz trace can visit different intermediate global states. The peak is invariant only if the quantity is computed per trace, for example from the happens-before graph, not from the visited linearization.

**3.1 Cilksan's SP-bags implementation (source).**
- **Bags.** `spbag.h` defines `enum class BagType_t { SBag = 0, PBag = 1 };` (line 16) and stores the bag type in bit 63 of a payload (lines 28–40).
- **Merging on return from a spawn.** `cilksan.cpp` `merge_bag_from_returning_child` merges a returning child's S-bag into the parent's P-bag ("Combine child S-bag into parent P-bag.", lines 186–193).
- **Merging at sync.** `complete_sync` merges the P-bag into the S-bag (`f->Sbag->combine(f->Pbags[sync_reg]);`, line 377).
- **The race test.** `dictionary.h` lines 236–250:

  ```cpp
  // Check if the given previous MemoryAccess_t is logically in
  // parallel with the current strand.
  ... SBag_t *LCASbagOrNull = Func->get_sbag_or_null();
  return (nullptr == LCASbagOrNull) ||
         f->check_parallel_iter(LCASbagOrNull, version);
  ```

  A previous access races iff its disjoint-set representative is a P-bag, or it belongs to a different iteration of a parallel loop (`check_parallel_iter`). `disjointset.h` `find_set` (line 263) performs path compression. `simple_shadow_mem.h` `check_race` (lines 1511–1523) reports a race when `previousAccessInParallel`. `dataRaceWithPreviousAccesses` (lines 1456–1469) additionally intersects locksets, which extends the analysis beyond pure SP programs.

Basis: source.

### 4. Reduced and bounded exploration: soundness conditions, provisos, and pitfalls

**4.1 Ignoring problem and the cycle proviso (documentation + source).**
- **Origin of the term.** Secondary sources attribute the term "ignoring problem" to Valmari 1991. Holzmann–Peled (FORTE 1994) write: "The need for such a proviso was first recognized by Valmari in [V90]", which is a CAV 1990 paper, not LNCS 483.
- **The proviso as defined.** Godefroid's thesis (preceding LNCS 1032) states the cycle proviso as follows. Either some selected transition not in the sleep set leads to a successor that is not on the DFS stack, or the selected set is all enabled transitions.
- **Spin's implementation of the proviso.** In Spin's generated verifier (`Src/pangen1.h`, pinned revision):
  - line 3079: `/* Look for a process with only safe transitions */`;
  - line 3122: `/* attempt Partial Order Reduction as preselect moves */`;
  - lines 3915–3924 (`SAFETY` mode): `/* preselected move - no successors outside stack */` undoes the selection (`From = FROM_P; To = UPTO_P;`) and resumes full expansion;
  - lines 3943–3970 (liveness mode): set the proviso bit and `goto Again; /* do full search */`.
- **Which statements count as "safe".** These are computed statically in `Src/pangen2.c`. The comment at lines 3409–3415 records a known approximation: "an xr or xs reference to an array element becomes an exclusion tag on the array itself - which could result in invalidly labeling operations on other elements of this array to be also safe under the partial order reduction".

**4.2 Spin measurements (execution, real tool).** Spin 6.5.3 was built from the pinned source (`make -j8`, 1.69 s wall; `make -j1`, 7.26 s; peak RSS 60,628 KiB; `spin` binary 1,374,392 bytes). Each `pan` was compiled with `gcc -O2` and run. Command: `support/spin/run_spin.sh <spin> <outdir>`. Outputs are in `support/spin/output/`.

| Model | Reduction | States stored | Transitions | Errors | Wall (pan) |
|---|---|---|---|---|---|
| `indep.pml`, N=2,K=3 | POR / `-DNOREDUCE` | 11 / 31 | 11 / 51 | 0 / 0 | 0.03 s / 0.04 s |
| N=3 | POR / none | 16 / 156 | 16 / 376 | 0 / 0 | 0.03 / 0.03 |
| N=4 | POR / none | 21 / 781 | 21 / 2,501 | 0 / 0 | 0.03 / 0.03 |
| N=5 | POR / none | 26 / 3,906 | 26 / 15,626 | 0 / 0 | 0.03 / 0.03 |
| N=6 | POR / none | 31 / 19,531 | 31 / 93,751 | 0 / 0 | 0.03 / 0.04 |
| `ignoring.pml` (infinite local loop ∥ failing global assertion) | POR / none | 4 / 2 | 6 / 2 | **1 / 1** | 0.03 / 0.03 |
| `nexttime.pml`, `ltl p { X (g == 0) }` | POR (default) / none | 2 (4 visited) / 2 | 4 / 2 | **0 / 1** | 0.05 / 0.03 |

- **Independent model.** The measured counts fit `5N+1` (reduced) and `(5^(N+1)−1)/4` (unreduced) for N = 2…6. This closed form is derived from the five data points, not from Spin documentation. At N=6 the reduction is about 630× in states. Basis: execution + derived.
- **Ignoring model.** The proviso works here: the reduced search still schedules `B` and finds the assertion violation. Basis: execution.
- **Next-time model.** The reduced search misses the violation silently. `spin -a` prints only `ltl p: X ((g==0))`, and `pan` prints no warning. These source facts explain why:
  - `Src/makefile` line 8 is `CFLAGS?=-O2 -DNXT -Wall -pedantic`;
  - `pangen1.h` line 46 guards the warning "for p.o. reduction to be valid the never claim must be stutter-invariant" (lines 55–58) with `#if defined(VERI) && !defined(NOREDUCE) && !defined(NP) && !defined(BFS) && !defined(HAS_LTL)`. It is therefore compiled out whenever the property is an inline `ltl` formula.

  The release notes document the incompatibility:
  - `Doc/V2.Updates` lines 936–940: "note that when partial order reduction is used this operator cannot be used … when you use it, you must compile pan.c with -DNOREDUCE";
  - `Doc/V3.Updates` lines 97–101, under "Version 3.0.6": `-DNXT` "is not enabled by default, because it jeopardizes compatibility with the partial order reductions".

  At the pinned revision the makefile default enables `-DNXT`. This report does not establish when that changed. Basis: source + execution + documentation.

**4.3 Catalogue of POR soundness fixes recorded in Spin's own release notes (documentation).**

| Release-note location | Version header | Omitted behaviour | Fix |
|---|---|---|---|
| `Doc/V2.Updates` lines 787–797 | 2.8.1, 12 April 1996 | The "liveness proviso" acted on different states in the first and second nested DFS, which "could affect the basic reachability properties of states" | Corrected, and `-DSAFETY` was introduced |
| `Doc/V3.Updates` lines 172–174 | 3.1.0 section | Weak fairness combined with POR in models with rendezvous (example by Dennis Dams) | Declared incompatible |
| `Doc/V6.Updates` lines 158–160 | 6.1.0, 4 May 2011 | An `else` combined with i/o under `xr`/`xs` assertions "could make the partial order reduction unsound" | Made an error |
| `Doc/V6.Updates` lines 898–899 | 6.4.9 section | Liveness checking with `-DMA` and POR "can lead to incompleteness" | Warning added |
| `Src/pangen2.c` lines 2208–2212 | (source comment) | A jump from an atomic sequence without globals into one with globals ("example by Claus Traulsen, 22 June 2007") | Handled in `scan_seq` |

**4.4 Dynamic POR and its optimal successors (documentation).**
- **Flanagan–Godefroid.** Assumes acyclic state spaces; "in the presence of cycles, the depth of the search has to be bounded somehow". The examined text has no Mazurkiewicz-trace completeness theorem; the guarantee is stated in persistent-set terms. The metric reported is transitions explored, with no absolute times.
- **Source sets / wakeup trees (POPL 2014 version).** Source sets "are provably minimal, in the sense that the set of explored processes from some scheduling point must be a source set in order to guarantee exploration of all Mazurkiewicz traces". Table 1 there (Concuerror, Erlang): `indexer(15)` explored 341,832 / 4,096 / 4,096 traces in 56m20s / 50.24s / 52.35s (classic / source / optimal).

**4.5 Preemption bounding and its interaction with DPOR (documentation + source + execution).**
- **Context bounding (Musuvathi–Qadeer 2007).**
  - The bound is formal: "there are at most C(nk,c)·(nb + c)! executions of P with c preemptions", against up to `(nk)!/(k!)^n` unbounded.
  - Coverage claims are bounded: "when the search runs out of resources after exploring all executions with c preemptions, the algorithm guarantees that any error in the program requires at least c+1 preemptions."
  - The headline "at most 2 preempting context switches" covers the 9 new bugs. One of the 7 seeded known bugs needed 3.
  - The Table 2 caption says 14 bugs, but its rows sum to 16.
- **Naive DPOR + preemption bound is unsound for bounded coverage (Coons–Musuvathi–McKinley 2013).** "if DPOR simply uses the preemption bound to prune the state space … it misses parts of the state space reachable in the bound and is therefore unsound. The bound essentially induces dependences between otherwise independent transitions". The fix, bound persistent sets, "conservatively backtracks to a previous point in the execution where the backtracked transition does not require a preemption".
- **Loom's implementation follows that fix (source).** `src/rt/path.rs` lines 362–386 read `if self.preemption_bound.is_some() { loop { // Preemption bounded DPOR requires conservatively adding // another backtrack point to cover cases missed by the bounds.` and walk back to the previous point where the active thread changed. `Schedule::backtrack` refuses to add a backtracking point once `self.preemptions == bound` (lines 493–506). The bound comes from `LOOM_MAX_PREEMPTIONS` (`src/model.rs` lines 39–42, 108–110).
- **Loom probe (execution, real tool).** `support/loom/`. Thread A stores 1 then 2; thread B loads twice and asserts `!(r1 == 1 && r2 == 2)`. Output, also in `support/loom/output.txt`:

| `LOOM_MAX_PREEMPTIONS` | 0 | 1 | 2 | 3 | unset |
|---|---|---|---|---|---|
| Failing interleaving found | no | **no (passes silently)** | yes | yes | yes |
| Executions until stop (assertion on) | 3 | 21 | 30 | 49 | 73 |
| Total executions explored (assertion off) | 3 | 21 | 69 | 150 | 234 |

With bound 1 the model completes without any message about truncated coverage; stderr was inspected. The unbounded passing run took 0.01 s wall and 2,372 KiB peak RSS. An incremental release build of the probe took 0.63 s. Basis: execution.

### 5. Published models later found to exclude real behaviour

- **x86-CC (Sarkar et al., POPL 2009) was wrong in both directions, and its own in-press addendum says so.**
  - *Too weak:* x86-CC allows IRIW (test `amd6`). "future specifications by both Intel and AMD will exclude the amd6 (IRIW) example".
  - *Excludes real behaviour:* test `n6` (due to Paul Loewenstein), with final state `0:EAX=1 ∧ 0:EBX=0 ∧ [100]=1`, is "disallowed by our x86-CC formal model … but … allowed by at least one Intel processor (we find approximately one witness in 2 ∗ 10^6 executions, reproducibly, on an Intel Core 2, with our litmus tool). It is also allowed by TSO."
  - The same paper's earlier testing had found no witnesses for `n1`, `amd6` and `n3`, and observed the SC-violating `iwp2.4/amd9` "between 5 and 5000 times out of 200000 runs".
  - The model was replaced by x86-TSO (Owens–Sarkar–Sewell, TPHOLs 2009; Sewell et al., CACM 2010).
- **Discovery mechanism.** Litmus testing on hardware at rates around 1 in 2×10^6 combined with vendor manual revisions. A model checked only against documentation would not have exposed `n6`. Basis: documentation.

**5.1 Proposed catalogue entry format for omitted-behaviour defects (derived).** Each entry records:
- the model and its pinned identity;
- the quantifier that was too narrow (schedules, environments, memory events);
- a minimal witness (a litmus test or interleaving);
- how it was found (hardware testing, a different semantics, a counting mismatch such as a measured peak exceeding a proved bound);
- the observables affected (final state, fault freedom, trace properties, resource peaks);
- the theorems whose statements must be relativized;
- the fix (a widened quantifier, a reduction theorem, or a renamed theorem).

The x86-CC `n6` entry fills these fields: model = x86-CC HOL; quantifier = memory events permitted; witness = `n6`; found by hardware litmus at about 1 in 2×10^6; observable = final state; fix = x86-TSO. The Spin entries in §4.3 fill them with "found by user example" and "fix = declared incompatible or warning". The one-bit nested-`∥` scheduler of §2 fills them with "found by counting mismatch".

### 6. Performance and resource footprint (L1–L6)

Every cell is measured (on the host in **Applicability**), cited, derived, or `not measured`.

| Subject | L1 authoring / size | L2 toolchain build | L3 analysis / exploration latency | L4 runtime effect | L5 proof / check | L6 memory / size |
|---|---|---|---|---|---|---|
| VST hybrid machines | `HybridMachineSig.v` 801 lines, `threadPool.v` 2,123, `SC_erasure.v` 2,867, `executions.v` 4,211 (measured, `wc -l`). `concurrency/sc_drf`: 12 `.v` files, 1,309,168 bytes. `concurrency/common`: 32 files, 729,217 bytes (measured, git tree sizes) | not measured | n/a | n/a | not measured (not built) | not measured |
| Hobor et al. 2008 | 1,331 spec + 14,430 proof lines; 42,277 total (cited). Proof/spec = 10.8 (derived) | not measured | n/a | n/a | not measured | not measured |
| CompCertTSO (POPL 2011) | about 36 man-months (cited); listed phases 19,832 spec / 23,230 proof lines (derived sum of cited table) | not measured | not measured | 75% of gcc -O1; 69% on a lock-free skiplist (cited) | not measured | not measured |
| CCAL 2018 | not measured | not measured | n/a | not measured | not measured | not measured |
| Iris | `language.v` 334 lines, `adequacy.v` 281 (measured) | not measured | n/a | n/a | not measured | not measured |
| Cilksan / SP-bags | `spbag.h` 265, `disjointset.h` 666, `cilksan.cpp` 1,109, `simple_shadow_mem.h` 2,034 lines (measured) | not measured (needs OpenCilk) | — | Nondeterminator slowdowns 2.41× (knapsack) to 11.09× (multisort) (cited, Feng–Leiserson Fig. 15). Cilksan's slowdown not measured | `O(T α(v,v))` time (cited) | `O(v)` space (cited) |
| Spin 6.5.3 | `pangen1.h` 240,040 bytes (git tree) | 1.69 s (`-j8`), 7.26 s (`-j1`), 60,628 KiB peak RSS (measured) | `indep` N=6: 31 vs 19,531 states (measured); FORTE'94 Tpc: 3,918,286 → 391,534 states, 630.6 s → 30.6 s (cited, Sparc-10) | n/a | n/a | `pan` peak RSS 132,972–138,208 KiB; `pan` itself reports 128 MB for its default `-w24` hash table (measured); FORTE'94 Tpc 268.4 → 26.2 MB (cited) |
| DPOR / source sets | not measured | not measured | `indexer(15)`: 56m20s → 50.24s classic → source (cited, POPL'14) | n/a | n/a | not measured |
| Loom | `path.rs` 547 lines (measured) | 0.63 s incremental probe build (measured); clean build not measured | 234 executions, 0.01 s (measured) | n/a | n/a | 2,372 KiB peak RSS; probe binary 1,921,192 bytes (measured) |
| Toy model | 1 file (support) | n/a | under 1 s (measured, not timed precisely) | n/a | n/a | not measured |

### 7. Human comprehensibility and conceptual simplicity (C1–C2)

- **Concept count for a reader checking schedule completeness (C1, derived from the cited definitions).**
  - Iris: 1 concept (a nondeterministic step over a thread list).
  - VST fine machine: 2 (a schedule list, plus `schedfail` skipping).
  - VST coarse machine: 4 (schedule list, `yield = id`, `AngelSafe`'s universal re-quantification, and the coarse-to-fine theorem with its `FineInit` context).
  - Hobor oracle: 3, plus an unproved equivalence.
  - CCAL: 3 (logs, environment contexts, rely validity).

  The coarse/fine split is the only design whose completeness argument is *non-local*: it lives in a theorem in a separate, unbuilt directory.
- **Failure legibility (C1).** A restricted scheduler does not fail loudly. In the toy model, final states agreed, and only trace counting or a peak comparison revealed the gap. In Spin and Loom, the reduced or bounded search reported success with no diagnostic. Bounded results are therefore not human-auditable unless the bound appears in the claim, for example "no error with ≤ c preemptions".
- **Minimal universal abstraction (C2).** A flat pool of threads with a step that picks any enabled thread (Iris, VST fine) makes nested `∥`, fork and join ordinary cases. A reduction theorem (VST coarse-to-fine, Lipton) then recovers efficiency without changing the schedule space. Per-node choice in a tree-structured `∥` is equivalent in the toy model, at the cost of depth-many bits per step.
- **Hidden complexity (C2).** Moving the completeness obligation into "the scheduler flushes buffers" (CompCertTSO), "valid environment contexts" (CCAL) or "well-synchronized programs" (Hobor) does not remove it. It moves it into adapters and assumptions that a reviewer must check separately.

### 8. How completeness claims are validated (V1–V4)

- **V1: specification adequacy and non-vacuity.**
  - Counting interleavings against a closed form (90 = 6!/(2!)³) and comparing peaks across schedulers caught the toy gap.
  - Comparing a reduced search with `-DNOREDUCE` on a seeded violation caught the Spin next-time miss.
  - Comparing bounded with unbounded Loom runs caught the silent bounded pass.
  - Re-association tests of `∥` (§2.3) are a cheap non-vacuity check for associativity claims.
- **V2: checker soundness.**
  - Spin's release history (§4.3) shows POR soundness defects found by user-supplied examples, not by systematic differential testing.
  - Coons et al. note that the optimizations used in their Table 1 are unproved.
  - Systematic differential testing of reduced against unreduced exploration across tools was **not examined**.
- **V3: concurrency and silicon.**
  - Hardware litmus testing exposed `n6` at about 1 in 2×10^6 runs.
  - Stateless model checkers (DPOR, Loom) validate implementations only within their acyclicity and bound assumptions.
- **V4: human mental models.** No study of how engineers read "for every schedule" claims was examined.

## Boundaries

- **Not examined:**
  - whether VST's `concurrency/sc_drf` and `concurrency/main.v` compile at the pinned revision with the CI Coq versions;
  - the full text of Lipton 1975, Steele 1990 and Valmari 1991, including whether Lipton's paper itself states a non-preserved property;
  - the JACM versions of CompCertTSO and Source Sets, and the Nidhugg results;
  - CCAL's proof sizes;
  - building or running Cilksan;
  - the Coons et al. companion proofs;
  - GenMC, Nidhugg and CHESS sources;
  - weak-memory scheduling beyond the x86-CC and CompCertTSO statements.
- **Unknown:**
  - whether the one-bit scheduler preserves final states for *all* race-free partitioned programs (the toy model checked four programs);
  - when Spin's makefile default began to include `-DNXT`;
  - Cilksan's measured overhead on current hardware.
- **Known not to apply:** the toy model's numbers are not properties of VST, Iris or any published semantics. Neither VST nor Iris has a nested `∥` scheduler; both use flat pools.
- **Unsupported (by the subject):**
  - Flanagan–Godefroid DPOR on cyclic state spaces without a depth bound;
  - the SP-bags guarantee across inputs;
  - Spin's POR with next-time properties (per its own release notes).
- **Attractive stronger conclusions not established:**
  - that Spin's default build is "unsound" in general (only next-time inline LTL was shown);
  - that Loom's bounded mode misses executions *within* its bound (the probe exercised only bounded coverage, not the Coons within-bound failure);
  - that any reduction theorem in §3 licenses claims about peak memory.

## Evidence

Observation date for all evidence: 2026-11-21 (UTC). Pinned revisions are in `REPORT.json`.

- **VST** (`PrincetonUniversity/VST` @ `d50ac1969f9f6586621895eb043ccf08a165f731`):
  - `concurrency/common/HybridMachineSig.v` lines 250–259, 314–364, 571–573, 592–602, 729–730, 761–780;
  - `concurrency/common/threadPool.v` lines 44–60;
  - `concurrency/sc_drf/Coarse2Fine_safety.v` lines 51, 59–62, 68–93;
  - `concurrency/main.v` lines 10–18, 36–60, 68–95, 102;
  - `Makefile` lines 768, 797, 929;
  - `.github/workflows/coq-action.yml` (`make_target: vst`).
- **Iris** (`rocq-iris/iris` @ `2fe2f450add5678d9a2492343c638ccdb428a677`): `iris/program_logic/language.v` lines 105–110; `iris/program_logic/adequacy.v` lines 180–188; `iris_heap_lang/lang.v` lines 716–717.
- **Cilksan** (`OpenCilk/productivity-tools` @ `3049053b784bc37d2ce9ff4449c7985703957006`): `cilksan/spbag.h` lines 16–40; `cilksan/cilksan.cpp` lines 163–215, 364–384; `cilksan/dictionary.h` lines 236–250; `cilksan/disjointset.h` lines 263, 396–403; `cilksan/simple_shadow_mem.h` lines 1456–1469, 1511–1523.
- **Spin** (`nimble-code/Spin` @ `e21106ff7e58afe79275b3ca10179556afa97aa2`):
  - `Src/version.h`, `Src/makefile` line 8;
  - `Src/pangen1.h` lines 46–59, 3079, 3122, 3915–3924, 3943–3970;
  - `Src/pangen2.c` lines 816–823, 2208–2212, 3409–3415;
  - `Doc/V2.Updates` lines 787–797, 936–940;
  - `Doc/V3.Updates` lines 97–101, 172–174;
  - `Doc/V6.Updates` lines 158–160, 898–899.

  Built with byacc (`ThomasDickey/byacc-snapshots` @ `7856d035dd27104782612818630adc5011214c31`, `yacc - 2.0 20260126`).
- **Loom** (`tokio-rs/loom` @ `9d549cd5357a5485900f4c53951fc1726319659f`): `src/rt/path.rs` lines 362–386, 484–506; `src/model.rs` lines 39–42, 108–110. The probe's `Cargo.lock` resolves `git+https://github.com/tokio-rs/loom?rev=…#9d549cd5357a5485900f4c53951fc1726319659f`.
- **Execution artefacts** (text, in `support/`):
  - `toy/nested_par_schedulers.py` + `toy/output.txt`;
  - `spin/*.pml`, `spin/run_spin.sh`, `spin/output/*.txt`;
  - `loom/Cargo.toml`, `loom/src/main.rs`, `loom/run.sh`, `loom/output.txt`.
- **Literature** (DOIs verified against Crossref metadata on 2026-11-21; version read in brackets):
  - Lipton, CACM 18(12):717–721, 1975, 10.1145/361227.361234 [abstract + Lamport–Schneider 1989 restatement].
  - Steele, POPL 1990, 10.1145/96709.96731 [secondary sources only].
  - Valmari, LNCS 483, 1991, 10.1007/3-540-53863-1_36 [abstract + secondary].
  - Feng–Leiserson, SPAA 1997, 10.1145/258492.258493 [full text].
  - Flanagan–Godefroid, POPL 2005, 10.1145/1040305.1040315 [full text].
  - Brookes, TCS 375, 2007, 10.1016/j.tcs.2006.12.034 [author's revised manuscript].
  - Musuvathi–Qadeer, PLDI 2007, 10.1145/1250734.1250785 [full text].
  - Hobor–Appel–Zappa Nardelli, ESOP 2008 (LNCS 4960), 10.1007/978-3-540-78739-6_27 [author preprint].
  - Sarkar et al., POPL 2009, 10.1145/1480881.1480929 [full text with in-press addendum].
  - Owens–Sarkar–Sewell, TPHOLs 2009, 10.1007/978-3-642-03359-9_27.
  - Sewell et al., CACM 53(7), 2010, 10.1145/1785414.1785443.
  - Vafeiadis, ENTCS 276, 2011, 10.1016/j.entcs.2011.09.029 [full text].
  - Ševčík et al., JACM 60(3), 2013, 10.1145/2487241.2487248 [abstract; numbers from POPL 2011, 10.1145/1926385.1926393].
  - Coons–Musuvathi–McKinley, OOPSLA 2013, 10.1145/2509136.2509556 [full text, proofs not included].
  - Abdulla et al., JACM 64(4), 2017, 10.1145/3073408 [abstract; numbers from POPL 2014, 10.1145/2535838.2535845].
  - Gu et al., PLDI 2018, 10.1145/3192366.3192381 [full text].
  - Jung et al., JFP 28, 2018, 10.1017/S0956796818000151 [full text to p. 67 of 73].
  - Holzmann–Peled, FORTE 1994 (Crossref issued 1995), 10.1007/978-0-387-34878-0_13 [author version].
  - Godefroid, LNCS 1032, 1996, 10.1007/3-540-60761-7 [preceding thesis].
- **Source facts vs. synthesis.** The tables in §3, §5.1 and §7 are this report's synthesis. The quoted lines and the numeric outputs are the source facts.

## Revalidation

- **VST.** Re-read `HybridMachineSig.v` around `Class Scheduler`, `machine_step` and `AngelSafe`. Grep `Coarse2Fine_safety.v` for `FineInit` and `main.v` for `Admitted`. Check whether `Makefile`'s `vst` target or CI now builds `concurrency/sc_drf`. To test compilation, build `concurrency/sc_drf/Coarse2Fine_safety.vo` with the CI Coq version.
- **Iris.** Diff `step_atomic` in `iris/program_logic/language.v`. If the pool is still `t1 ++ e1 :: t2` and `efs` are appended, the by-construction argument holds.
- **Spin.** Rebuild from a new revision and run `support/spin/run_spin.sh <spin> <dir>`. The discriminating rows are `nexttime_por` (`errors: 0`) vs `nexttime_nored` (`errors: 1`), and `grep -n 'HAS_LTL' Src/pangen1.h` plus `grep -n NXT Src/makefile`. A fix would show a warning, a nonzero error count, or `-DNXT` removed from the default flags.
- **Loom.** Change the `rev` in `support/loom/Cargo.toml` and run `support/loom/run.sh`. Compare the bound/executions table. Diff `src/rt/path.rs` around "Preemption bounded DPOR requires conservatively adding".
- **Cilksan.** Diff `previousAccessInParallel` in `cilksan/dictionary.h`, and `merge_bag_from_returning_child`/`complete_sync` in `cilksan.cpp`.
- **Toy model.** `python3 support/toy/nested_par_schedulers.py`. Any new scheduler design can be added as a successor function, and its trace count and peak compared with `full`.
- **Literature claims.** These hold for the cited versions. Only the x86-CC addendum and the Spin release notes record defects. Re-verify the DOIs through the Crossref REST API.
