# Scheduler-aware probabilistic noninterference, probability–nondeterminism monads, and presampling tapes for concurrent randomized programs

## Summary

- **Where the scheduler lives decides what a probabilistic-noninterference theorem is worth after implementation.** Definitions that bake one scheduler into the semantics (uniform choice among threads: Volpano–Smith 1998/1999; Popescu–Hölzl–Nipkow 2013) describe a Markov chain and say nothing about any other scheduling policy. The definition of Sabelfeld–Sands 2000 quantifies over schedulers and therefore survives when an implementation fixes one, at the price of rejecting (or padding) every command whose branching or step count depends on a secret. Possibilistic noninterference survives neither: choosing a scheduler is a refinement, and refinement can create a leak.
- **Probability and nondeterminism do not combine by a distributive law.** Three repairs are in use, and they keep different equations: (a) convex sets of distributions (the convex powerset, obtainable from a *weak* distributive law, mechanized as the `gcmAP` model of monae's `altProbMonad`) keep idempotence of both choices and "probabilistic choice distributes over nondeterministic choice", but not the converse and not right-distributivity of bind over probabilistic choice; (b) indexed valuations (Varacca–Winskel, the specification monad of Polaris) keep the plain powerset by giving up idempotence of probabilistic choice; (c) an operational, scheduler-indexed family of Markov chains (the concurrent logics in clutch) never forms the set at all and states theorems as "for all schedulers".
- **A sample and an adversarial choice do not commute.** A choice resolved after a sample may depend on it. monae proves `coinarb p = arb` but `arbcoin p = bcoin p [~] bcoin (1-p)`.
- **Presampling tapes move a sample earlier as ghost state; their soundness is an erasure theorem.** In the concurrent logics of clutch, erasure is proved only for schedulers whose decision is a function of scheduler state, thread pool and heap but *not* of tape contents (`TapeOblivious`). Every mechanized concurrent adequacy theorem carries that hypothesis.
- **Presampling is unsound on the angelic (specification) side of a concurrent refinement.** clutch contains a mechanized refutation (`presample_RHS_is_unsound`).
- **A tape is an exclusive resource.** No inspected rule divides a tape's contents; threads either own separate tapes or share one through an invariant with atomic reads.
- **Polaris has no tapes.** Its adequacy theorem holds per deterministic, full-history scheduler under which the program terminates within a known number of steps, and bounds expectations between the extrema of a set of indexed valuations.

## Applicability

The report concerns languages that have both random sampling and parallel composition (or any other scheduler-resolved choice), and three questions about them: which information-flow definitions remain valid after scheduling is fixed, which semantic domain can interpret both effects, and under which side conditions a sample may be drawn "early" in a proof.

Subjects and how they relate:

- **Three mechanized developments, read at pinned revisions (source inspection only; nothing was compiled):** `logsem/clutch` at `cc81450edd699bfcd9fa806d628a57d16c48f75d` (Rocq; sequential `prob_lang` and concurrent `con_prob_lang`, the Clutch, Eris, Coneris and Foxtrot logics), `jtassarotti/polaris` at `c7873f05214351d54cacf3d8482625ee33ad3288` (Coq 8.8.2-era; Iris 3.1 fork with indexed valuations), `affeldt-aist/monae` at `66f2b98c7cb29059f88380245e1d43046780d523` (Rocq; equational monad hierarchy and models).
- **Papers, read as text:** the corrected CSFW 1998 version of Volpano–Smith (the journal version, JCS 7(2–3), 1999, was not separately read); Popescu–Hölzl–Nipkow; Russo–Sabelfeld; the Sabelfeld–Myers survey; Tassarotti–Harper; Zwart–Marsden; and the Clutch, Eris and Coneris papers (arXiv versions). For Goy–Petrişan only the abstract was read. **For Sabelfeld–Sands 2000 only the publication record and abstract were retrieved**; statements about its definition and type system are taken from that abstract and from three later papers that describe it (two co-authored by Sabelfeld). They are marked as such.
- **Three Python probes written for this report.** They are toy models, not executions of any artifact above. Every number they produce is a property of the toy and is labelled so.

Scope limits that change meaning: all languages discussed sample from discrete distributions; "scheduler" means a thread-selection function inside an interleaving semantics, not an operating-system scheduler; "timing" means step counts of an abstract machine. The clutch and monae revisions are recent development heads; the Polaris revision dates from 2018 and corresponds to its POPL 2019 artifact. Nothing here was established for weak-memory concurrency, continuous distributions, or hardware timing.

## Findings

### 1. Scheduler models in published definitions of probabilistic noninterference

| Work | Scheduler in the semantics | Probabilistic steps in threads | Security statement | Mechanized |
| :--- | :--- | :--- | :--- | :--- |
| Smith–Volpano 1998 (as described by Volpano–Smith) | purely nondeterministic thread choice | no | possibilistic: the *set* of possible low results is independent of high inputs | no |
| Volpano–Smith 1998/1999 | uniform: a global step picks a thread of pool `O` with probability `1/\|O\|` ("our semantics prescribes a uniform distribution for simplicity") | no | "the probability distribution of the final values of low variables is independent of the initial values of high variables"; Theorem 5.6 states that equivalent well-typed protected probabilistic states stay equivalent under the transition matrix | no |
| Sabelfeld–Sands 2000 (abstract; secondary accounts) | any scheduler in a class that includes probabilistic ones: "robust security with respect to any particular scheduler used" | scheduler only | probabilistic bisimulation, scheduler-independent, compositional | no |
| Russo–Sabelfeld 2006 | scheduler is a program that receives `hide`/`unhide`/`hfork` events and must itself be noninterferent (their Definition 3); example: round-robin over separate low and high thread lists | scheduler only | noninterference of threads plus scheduler against internal timing leaks | no (prototype in GNU Pth) |
| Popescu–Hölzl–Nipkow 2013 | uniform over all threads (`Par`) or over unfinished threads (`ParT`) | yes (`Ch` choice command) | resumption-based (`siso`, `discr`, strong and 01-bisimilarity) and trace-based ("end security", "any-moment security") notions, with implications between them | Isabelle/HOL, "about 8000 lines" |

Basis: documentation (paper texts as listed under Evidence). The Sabelfeld–Sands row is second-hand except for the quoted abstract phrase.

Two details of the uniform-scheduler definitions are easy to miss. First, whether a *finished* thread still receives scheduler probability changes the timing of the others; Popescu–Hölzl–Nipkow model both variants and their compositionality results differ (parallel composition with termination-sensitive scheduling needs the weaker 01-bisimilarity). Second, their step from the resumption-based notion to trace-based end security assumes almost-everywhere termination.

### 2. What each enforcement mechanism rejects, and whether the guarantee survives a concrete scheduler

| Mechanism | Rejected or rewritten program patterns | Holds after the implementation fixes a scheduler? |
| :--- | :--- | :--- |
| Possibilistic typing | assignments from high to low, low effects under high guards | **No.** Subject to "refinement attacks" (Sabelfeld–Myers): some refinements obtained by choosing a scheduler are insecure. |
| Volpano–Smith | "every total command with a high guard" must execute atomically: a conditional with a high guard is wrapped in `protect`; no `while` inside a protected section; protected sections not nested; loops with high guards lie outside the treated class (later work by Smith is described as the first to accept some of them) | Only for the uniform scheduler the theorem is stated for. |
| Sabelfeld–Sands (per Popescu et al., per Sabelfeld–Myers, per Russo–Sabelfeld) | commands whose branching depends on high data unless both branches behave identically step for step (the criterion Popescu et al. call self-isomorphism); branches of a high conditional are equalized by cross-copying dummy commands (a padding transformation after Agat) | **Yes, for every scheduler of the class**; the attacker model includes external timing (step counts). |
| Smith 2001/2003 (per Russo–Sabelfeld and Sabelfeld–Myers; not read) | a `while` with a high guard is accepted only if no assignment to a low variable follows it | uniform scheduler only |
| Russo–Sabelfeld | high-dependent regions must be bracketed by `hide`/`unhide`; threads created in a high context use `hfork` | for schedulers that satisfy their noninterference condition and honour the events |
| Popescu–Hölzl–Nipkow syntactic criteria | e.g. `d4 = (if h = 0 then h := 1; h := 2 else h := 3); l := 4` is "rejected by all the syntactic criteria" because the timing of the low assignment depends on `h` | uniform scheduler only |

Basis: documentation.

The classic two-thread illustration (Russo–Sabelfeld) is `d1: (if h > 0 then sleep(100) else skip); l := 1` in parallel with `d2: sleep(50); l := 0`; each thread is secure alone, and the pool "will leak whether the initial value of h was positive into l under many reasonable schedulers".

**Probe A** (toy interpreter, not any published artifact; code and full output under Evidence) computes exact final distributions of `l` for this shape of program:

| Program (toy; `sleep(k)` = k silent steps; branch test = 1 step) | uniform over live threads | round-robin, quantum 1 | possibilistic result set |
| :--- | :--- | :--- | :--- |
| race with `sleep(4)` / `sleep(2)` | h=0: Pr[l=1] = 1/2; h=1: Pr[l=1] = 219/256 | h=0: l=0; h=1: l=1 (the secret bit is copied) | {0,1} for both h |
| race with `sleep(100)` / `sleep(50)` | h=0: Pr[l=1] ≈ 1.6e-13; h=1: Pr[l=0] ≈ 1.5e-5 | l = [h>0] | {0,1} for both h |
| branches padded to equal length | identical for h=0,1 (219/256) | identical | {0,1} |
| conditional executed as one atomic step | identical for h=0,1 (5/16) | identical | {0,1} |
| `d4`-shaped thread against `l := 5` (branch test 1 step) | Pr[l=5]: 1/16 vs 1/8 | no difference at quantum 1; at quantum 3 the final `l` is 4 vs 5 | {4,5} |

Basis: execution (toy model of an interleaving semantics, not of any cited system). What the probe establishes: (i) the possibilistic view is blind to all of these leaks; (ii) a deterministic scheduler can turn a probabilistic bias into a deterministic copy of the secret; (iii) absence of a leak under one scheduler (round-robin, quantum 1, last row) does not transfer to another (quantum 3, or uniform); (iv) padding and atomic execution each remove the dependence in the toy under all three schedulers tried, which is the behaviour the scheduler-independent definitions demand and the uniform-scheduler theorems do not promise.

A discrepancy is preserved rather than resolved: Popescu et al. write of their `d5 = d4 ∥T l := 5` that "if h = 0, then 1 out of 4 executions yields l = 4; otherwise, only 1 out of 8". The toy gives the pair {1/8, 1/4} only for the event `l = 5` when the branch test costs no step, and then with `h = 0` (the longer branch) on 1/8. The qualitative claim (the distribution of the final `l` depends on `h`) is reproduced; the stated fractions are not, and the Isabelle development was not run to decide which reading is intended.

### 3. Probability with nondeterminism: the missing distributive law and the three repairs

- Zwart–Marsden recall that "there is no distributive law combining the powerset and finite probability distribution monads" (Varacca–Winskel 2006, by a proof credited to Plotkin), later strengthened (Dahlqvist–Neves 2018) to "the composite functor carries no monad structure at all", and generalize the argument into no-go theorems. Basis: documentation.
- Goy–Petrişan: the problem "stems from the absence of a distributive law of the powerset monad over the distribution monad"; they "prove the existence of a weak distributive law of the powerset monad over the finite distribution monad" and "retrieve the well-known convex powerset monad as a weak lifting of the powerset monad to the category of convex algebras". Basis: documentation (abstract only).
- Tassarotti–Harper on indexed valuations: the usual equation that identifies `A ⊕p A` with `A` is dropped because "subsequent non-determinism in the computation can be resolved differently on the basis of this seemingly irrelevant probabilistic choice"; with that law gone a distributive law with (non-empty) nondeterministic choice exists. Basis: documentation + source (Polaris `ival` record, section 6).

| Law (`⊓` nondeterministic, `⊕p` probabilistic) | plain distributions | plain powerset of distributions | convex sets of distributions | indexed valuations with nondeterminism |
| :--- | :--- | :--- | :--- | :--- |
| `A ⊓ A = A` | n/a | holds | holds | holds |
| `A ⊕p A = A` | holds | **fails** (toy: `{0,1} ⊕½ {0,1} = {0, ½, 1}`) | holds | **given up by design** |
| `A ⊕p (B ⊓ C) = (A ⊕p B) ⊓ (A ⊕p C)` | n/a | — | holds (toy: 10125/10125; monae axiom `choiceDr`, proved in the model as `choicealtDr`) | holds (the distributive law) |
| `A ⊓ (B ⊕p C) = (A ⊓ B) ⊕p (A ⊓ C)` | n/a | — | **fails** (toy: 7731/10125 instances hold; first counterexample `p = 1/4, A = [0,1/4], B = [0,0], C = [0,1/2]`) | not examined |
| `A ⊓ B = (A ⊓ B) ⊓ (A ⊕p B)` (convexity) | n/a | fails | holds (toy 675/675; monae `alt_absorbs_choice`) | fails by design |

Basis: execution (Probe B: toy model of the convex-powerset construction at outcome type Bool, where a convex set of distributions is an interval of Pr[True]; not monae's model) + source (monae lemma names) + documentation. Cells marked "—" were not evaluated.

### 4. monae's mechanized interface and model

`theories/core/hierarchy.v` builds `altProbMonad` from `altCIMonad` (associative, commutative, idempotent nondeterministic choice `[~]`) and `probMonad` (convex-space structure on each `M T` plus left-distributivity of bind over probabilistic choice) by one extra axiom:

```coq
HB.mixin Record isMonadAltProb {R : realType} (M : UU0 -> UU0)
    of MonadAltCI M & MonadProb R M :=
  { choiceDr : forall T p, right_distributive
      (@choice R M p T) (fun a b => a [~] b) }.
```

The same file defines `isMonadConvexDr` (bind distributes *rightwards* over probabilistic choice) with the comment "WARNING: this should not be asserted as an axiom in conjunction with altCI; see also counterexample_altconvexdr.v". That file (`theories/applications/counterexample_altconvexdr.v`, titled "collapse of the probabilistic choice in altConvexDrMonad") proves `choiceDalt`: in any monad with both structures, nondeterministic choice distributes over probabilistic choice. `theories/lib/proba_lib.v` then shows what that unwanted law implies (`keimel_plotkin_instance`): for all `p q`, the fair mixture of `p` and `q` equals the fair mixture of itself with `p [~] q` — an equation Probe B finds false in 210 of 225 interval instances.

`theories/models/gcm_model.v` (797 lines) constructs the "geometrically convex monad" as a composite of three adjunctions (choice types, convex spaces, semi-complete semilattice convex spaces; elements are non-empty convex sets of finitely supported distributions), and `theories/models/altprob_model.v` (216 lines) instantiates the interface (`gcmAP`), proving `choicealtDr` and a non-triviality example `gcmAP_choice_nontrivial`: for `p ≠ q`, the biased coins with bias `p` and `q` are different elements. Basis: source.

### 5. Order of resolution: sampling and adversarial choice do not commute

monae (`theories/lib/proba_lib.v`, section `mixing_choices`), for a demon bit `a`, a coin `c` of bias `p`, and result `a == c`:

- `arbcoin_spec`: demon first, coin second: `arbcoin p = bcoin p [~] bcoin (1-p)`;
- `coinarb_spec`: coin first, demon second: `coinarb p = arb`.

Probe B reproduces this in the interval toy for `p = 1/3`: demon-then-coin gives `[1/3, 2/3]`, coin-then-demon gives `[0, 1]`. Basis: source + execution (toy).

This single asymmetry is the common root of the remaining findings. A scheduler is a demon. Whatever is sampled before a scheduling decision, and is visible to the scheduler, enlarges the set of reachable outcome distributions. Moving a sample earlier is therefore sound exactly when the intervening choices cannot observe it. Basis: derived (from the two lemmas above and sections 7–9).

### 6. Operational models: scheduler-indexed Markov chains

**clutch, concurrent language.** `theories/prob/mdp.v`:

```coq
Record scheduler:= {
    scheduler_f :> (sch_state * mdpstate δ) -> distr (sch_state * mdpaction δ)
  }.
```

A scheduler is stateful and probabilistic, sees the whole configuration (thread pool and state), and returns a distribution over its next internal state and the thread to step. The Coneris paper calls this notion "quite strong" for exactly these two reasons. Execution `sch_exec sch n` and its limit `sch_lim_exec sch` are distributions over values of thread 0.

**Polaris.** `theories/program_logic/prob_language.v`:

```coq
Definition trace := list (cfg prob_lang).
Definition scheduler := trace → nat.
```

A scheduler is a deterministic function of the entire history of configurations; if it names a thread that cannot step, the configuration stutters. Program-level randomness is a Bernoulli primitive added to the Iris heap language. Specification computations are sets of indexed valuations:

```coq
Record ival X := { idx : countType; ind: idx → X; val: idx → R; val_nonneg: ∀ i, val i >= 0 }.  (* layout condensed *)
Record pival (X: Type) := { choices :> ival X → Prop; nonempty : ∃ I, choices I }.
```

and the relation between program and specification is a coupling "up to irrelevance" (`irrel_ivd`, which closes equality of indexed valuations under prepending an unused computation: `irrel_ivd X I1 (x ← I0; I1)`). Basis: source.

### 7. Presampling tapes: semantics, ownership, rules

In both `prob_lang` and `con_prob_lang` the state is a heap plus a finite map from labels to tapes, a tape being a bound `N` and a list of values below `N+1`. From `theories/con_prob_lang/lang.v`:

- `AllocTape N` returns a fresh label with the empty tape;
- `Rand N α` on a **non-empty** tape with matching bound pops the head deterministically ("the tape is non-empty so we consume the first number");
- on an **empty** tape it samples uniformly from `0..N` ("the tape is allocated but empty, so we sample");
- with a **mismatching bound** it ignores the tape and samples uniformly ("bound did not match the bound of the tape");
- `state_step σ α` appends one uniform sample to tape `α`. No program instruction performs it; only proof rules do.

So tapes exist in the operational semantics, but an execution that starts with empty tapes never observes a non-empty one. The Clutch paper states that tapes "remain a proof-device as tapes can be erased through refinement".

Logic-level facts (Coneris; `theories/coneris/primitive_laws.v`, `error_rules.v`, `wp_update.v`):

| Rule | Statement (abridged) |
| :--- | :--- |
| `wp_alloc_tape` | `{True} alloc #z {α. α ↪N (N; [])}` |
| `wp_rand_tape` | `{α ↪N (N; n :: ns)} rand(#lbl:α) #z {RET #n; α ↪N (N; ns) ∗ ⌜n ≤ N⌝}` |
| `wp_rand_tape_empty` | with `α ↪N (N; [])` the result is an arbitrary `n ≤ N` and the tape stays empty |
| `state_update_presample_exp` | from `α ↪N (N; ns)` and error credit `↯ ε1`, with `Σ_n ε2(n)/(N+1) ≤ ε1`, obtain under the `state_update E E` modality some `n` with `α ↪N (N; ns ++ [n]) ∗ ↯ (ε2 n)` |
| exclusivity | `l ↪N (N; ns) -∗ l ↪N (M; ms) -∗ False` |

- **Division and sharing.** `α ↪N (N; ns)` is defined from the full-ownership ghost-map element (`DfracOwn 1`). Notations for fractional and discarded tape ownership are declared, but every primitive rule listed above takes the full assertion, and no inspected rule splits the *contents* of a tape between two owners; consumption is strictly first-in-first-out. Two threads can therefore use randomness prepared in advance in two ways: each allocates its own tape (the Coneris paper's "local tape" principle: "Each thread uses a separate and local tape which does not need to be shared"), or one tape is placed in an invariant and read by an atomic step. The repository's Coneris notes add a restriction for the second way: a sampler specification with atomic tape reads is satisfied by a rejection sampler but not by an implementation that simulates `rand 3` with two `rand 1` steps, "since the randomness is not performed atomically".
- **Presampling while an invariant is open.** In the earlier sequential logics presampling was only a program-logic rule. Coneris makes it an update modality so that, in one logically atomic step, a proof can open an invariant, take error credits out, presample, redistribute credits by outcome, and close the invariant.
- **Not prophecy variables.** The Clutch paper shows that prophecy variables "as previously developed in the context of Iris ... are unsound for the (synchronous) coupling logic".

Basis: source + documentation.

### 8. Side conditions of the soundness theorems

| Theorem (file) | Hypotheses beyond the proved triple | Conclusion |
| :--- | :--- | :--- |
| Clutch `wp_refRcoupl` (`theories/clutch/adequacy.v`) | none on scheduling (sequential language) | `exec n (e, σ) ≾ lim_exec (e', σ') : φ` (a left-partial coupling of the n-step run with the full run of the specification program) |
| Eris `wp_pgl_lim` (`theories/eris/adequacy.v`) | `0 <= ε` | `pgl (lim_exec (e, σ)) φ ε`: the result violates `φ` with probability at most `ε` |
| Coneris `wp_pgl_lim` (`theories/coneris/adequacy.v`) | `0 <= ε`; countable scheduler state; **`TapeOblivious sch`** | `pgl (sch_lim_exec sch (ζ, ([e], σ))) φ ε` |
| Coneris `wp_safety` | as above plus **`sch_mass_1 sch`** (the scheduler's choice distribution has total mass 1 in every configuration) | after any `n` steps the non-stuck mass is at least `1 - ε` |
| Foxtrot `foxtrot_rel_adequacy` (`theories/foxtrot/binary_rel/binary_adequacy_rel.v`) | `0 <= ε`; for **every** tape-oblivious scheduler of the implementation and every `ε' > 0` | there **exists** a tape-oblivious scheduler of the specification with an approximate coupling of budget `ε + ε'`; corollary: least-upper-bound termination probabilities are ordered up to `ε` |
| Polaris `heap_prob_adequacy` (`theories/heap_lang/adequacy.v`) | **`terminates sch [([e], σ)] n`** for the scheduler considered | a coupling up to irrelevance between the n-step indexed distribution and the specification set; corollaries `heap_prob_adequacy_Ex_max/min` bound the expectation of `f` between `Ex_min g Is` and `Ex_max g Is` when `g` is bounded on the support |

The tape side condition, from `theories/con_prob_lang/lang.v`:

```coq
Class TapeOblivious `{Countable sch_int_σ} (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) : Prop :=
  tape_oblivious :
   ∀ ζ ρ ρ', ρ.1 = ρ'.1 -> heap ρ.2 = heap ρ'.2 -> sch (ζ, ρ) = sch (ζ, ρ').
```

and the erasure notion the weakest precondition is built on (`theories/common/sch_erasable.v`, instantiated with `P := TapeOblivious`):

```coq
Definition sch_erasable (μ : distr (state Λ)) σ:=
  ∀ (sch_state:Type) `(H:Countable sch_state) (sch : scheduler (con_lang_mdp Λ) sch_state) es ζ m,
  P sch_state sch ->
  dmap (λ x, x.2.1) (μ ≫= (λ σ', sch_pexec sch m (ζ, (es, σ')))) = dmap (λ x, x.2.1) (sch_pexec sch m (ζ, (es, σ))).
```

Documentation and source differ in emphasis. The Coneris paper's Theorem 4.1 reads "for all schedulers ζ" and its section on the operational semantics stresses that a scheduler may depend on "the entire view of the thread pool and the memory state"; the restriction appears later, in the model section: "Recall that the operational semantics requires schedulers to be invariant under changes to presampling tapes". The mechanized statement is the authority: tape contents are excluded from what a scheduler may read. For executions that begin with empty tapes this costs little, because program steps never fill a tape; whether every scheduler on such executions can be replaced by a tape-oblivious one with the same behaviour is plausible but was not found as a lemma. Basis: source + documentation; the last sentence is a hypothesis.

Polaris's bounded-termination hypothesis is acknowledged in its paper ("This result only holds for schedulers under which the program is guaranteed to terminate in some number of steps; this is not that surprising, since the original Iris is a partial correctness logic"), and the repository README notes one more gap between paper and proof: the paper states adequacy "as if the indexed valuation interpretation of the concrete program always returned a non-empty list and always returned a value", whereas the Coq statement returns dummy values otherwise. Basis: documentation.

### 9. Presampling on the specification side is unsound

`theories/foxtrot/examples/presample_rhs.v` ("Counter example of presampling on the RHS") defines, with `nodet` a scheduler-resolved value built from a racing forked thread:

```coq
Definition prog0 : expr :=  #().
Definition prog1 : expr := if:  nodet #() = rand #1  then #() else diverge #().
Definition prog2 : expr := let: "α":=alloc #1 in
  if:  (rand("α") #1 )= nodet #() then #() else diverge #().
Definition prog3 : expr := if: rand #1 = #1 then #() else diverge #().
```

Operands are evaluated right to left, so `prog1` samples and then lets the scheduler choose, while `prog2` chooses and then samples. The file proves `prog0_termination` (best-case termination probability at least 1), `prog3_termination` (at most 1/2), and `presample_RHS_is_unsound`: if a rule let the *specification* side append a fresh sample to its tape when the implementation samples, the refinement chain `prog0 ≤ prog1 ≤ prog2 ≤ prog3` would be derivable and `1 ≤ 1/2` would follow. On the specification side the scheduler is chosen existentially, so a presampled value would hand the angel knowledge of a future coin. Basis: source.

**Probe C** (toy; three hand-encoded programs, not the Rocq terms) computes the best-case termination probability over schedulers: sample-then-choose 1; choose-then-sample 1/2; presample-then-choose-then-read 1/2 for a scheduler that cannot read the tape and 1 for one that can. Presampling is erasable in the toy exactly for the tape-oblivious scheduler. Basis: execution (toy).

### 10. What a language with sampling and parallel composition needs (synthesis)

| If the intended theorem is ... | sufficient carrier | scheduling is ... | cost |
| :--- | :--- | :--- | :--- |
| a distributional property under one documented scheduler | distributions over configurations (Markov chain) | part of the semantics | void for any other scheduler (section 2) |
| a bound that must hold whatever the scheduler does | family of chains indexed by schedulers; statement `∀ scheduler` | demonic; must be told what it may observe | every proof rule that reorders sampling needs an erasure lemma relative to that observation (section 8) |
| a refinement between two concurrent programs | the same family on both sides; `∀ scheduler ∃ scheduler` | demonic left, angelic right | asymmetry of rules between the sides (section 9) |
| equational reasoning about programs as values | convex sets of distributions | a nondeterministic-choice operator | no right-distributivity of bind over `⊕`; `⊓` does not distribute over `⊕` |
| a specification that keeps "which coin was flipped" observable to later choices | indexed valuations with nondeterminism | choice operator | `A ⊕p A ≠ A`; equality only up to irrelevance |

Basis: derived from sections 1–9. The carrier therefore has to reach scheduling as soon as (a) the property is distributional and (b) the scheduling policy is not part of the specification. Confining probability to sampling expressions and treating thread choice as an unrelated, purely possibilistic effect reproduces the refinement attack of section 2.

### 11. Cost and footprint

| Level | Observation | Basis |
| :--- | :--- | :--- |
| Authoring effort | clutch: 294,385 lines in 673 `.v` files under `theories/`; shared probability library 21,139; `con_prob_lang` 7,630; Coneris 21,643 (5,211 outside `examples/` and `lib/`); Foxtrot 22,044 (11,176 core). A 6-line program (`two_add_prog'`: two threads each `FAA l (rand #3)`) is verified in a 391-line file (about 65 proof lines per program line). The specification-side counterexample occupies 642 lines for four one-line programs. Polaris: probability library 48,963 lines (indexed valuations 14,976); the three `prob_*.v` program-logic files 1,783; approximate counter 2,637; skip list 4,412. monae: 20,355 lines in total. Popescu et al.: about 8,000 lines of Isabelle. | source (line counts by `wc -l` at the pinned revisions); documentation |
| Agent or person-time, repair cost on change | no figures in any examined source | unknown |
| Toolchain build | clutch states Rocq 9.1.1, Iris 4.5.0, Coquelicot 3.4.4, MathComp 2.5.0, MathComp Analysis 1.14; Polaris states Coq 8.8.2 and warns "the examples can take a long time to build". No build was run. | documentation; not examined |
| Elaboration / interactive latency | not measured | not examined |
| Execution cost of the verified programs | A tape label on `rand` changes nothing at run time when the tape is empty (section 7), so annotations cost nothing after erasure (derived). Padding executes the longer branch length on every path: in Probe A the short path of the padded thread grows from 3 to 6 steps (toy). Atomic `protect` sections exclude all other threads for their duration. Overhead of the modified GNU Pth scheduler is not quantified in the text read. | derived; execution (toy); unknown |
| Proof-checking speed, compiled artifact size, peak memory | not measured | not examined |
| Source footprint | unpacked trees: clutch 13 MB, Polaris 3.8 MB, monae 1.3 MB | execution (`du -sh`) |
| Probe cost | each probe runs in under 2 s of CPython, including the exact 100/50-step race | execution |

### 12. Comprehensibility and conceptual economy

- **Concepts a reader must hold to read one concurrent adequacy theorem** (Coneris): scheduler record, scheduler state, configuration, `TapeOblivious`, n-step execution and its limit, `pgl`, error credit, weakest precondition — eight, of which `TapeOblivious` is the one a reader of the paper's headline theorem would not expect. Basis: derived from the quoted statements.
- **Nonlocal reasoning.** Whether `prog1` or `prog2` gives the scheduler the advantage depends on right-to-left operand evaluation, a property of the language definition rather than of the program text. Whether a uniform-scheduler noninterference proof applies depends on a deployment fact (the scheduler) recorded nowhere in the program. Type-system enforcement (Volpano–Smith, the self-isomorphism criterion) is local and syntax-directed; the bisimulation definitions it is sound for are not.
- **Diagnostics.** A rejected program under the padding discipline has an explanation a programmer can act on (unequal branches). A failed erasure side condition has none at the level of the program.
- **One invariant behind several mechanisms.** "A choice may depend only on what has been revealed to the chooser so far" accounts for: convex closure (a chooser that may randomize); the failure of `⊓` over `⊕`; `coinarb ≠ arbcoin`; the tape-obliviousness condition; the unsoundness of specification-side presampling; and scheduler-independent noninterference (the schedule the attacker can observe may not depend on high data). Indexed valuations are the variant in which every coin is revealed to every later choice. Stating the observation relation of the scheduler explicitly, once, would make these ordinary instances; in the examined artifacts it is instead distributed over a type class on schedulers, an erasure predicate inside the weakest precondition, and per-rule side conditions. Basis: derived.
- **Where complexity moves.** The scheduler-indexed operational model keeps the program logic simple and moves the burden into erasure lemmas (`theories/con_prob_lang/erasure.v`, 761 lines). The convex-powerset model keeps equational reasoning simple and moves the burden into the model construction (three adjunctions). Indexed valuations keep the monad simple and move the burden into the coupling relation.

### 13. How the examined results are validated

| Validation concern | What exists in the examined material | Gap |
| :--- | :--- | :--- |
| Specification adequacy and non-vacuity | monae proves its combined model non-trivial (`gcmAP_choice_nontrivial`) and mechanizes the collapse caused by a tempting extra axiom; clutch mechanizes the refutation of a tempting rule; Popescu et al. exercise each security notion on six small programs, including two that must be rejected | no mutation of specifications; the noninterference papers before 2013 are unmechanized |
| Checker and toolchain soundness | clutch and Polaris list the axioms reported by `Print Assumptions` (classical logic, reals, functional extensionality, indefinite description); Polaris warns that Coq 8.8.1 lists spurious assumptions | no independent checker run, no differential testing of the proof tools |
| Concurrency, timing and hardware | all results are about interleavings of an abstract machine with sequentially consistent memory; "time" is a step count | no stateless model checking, no weak-memory semantics, no measurement on a real scheduler; Russo–Sabelfeld's prototype is the only implementation-level evidence and its measurements were not found |
| Operator and programmer comprehension | none | no study of whether users of these definitions predict leaks or side conditions correctly |

Basis: source + documentation; the right-hand column records absence within the material read, not absence in the literature.

## Boundaries

- **Not examined:** the full text of Sabelfeld–Sands 2000 (abstract only); Smith 2001/2003 and Mantel–Sudbrock 2010 (known here only through other papers' descriptions); the journal version of Volpano–Smith; the body of Goy–Petrişan and of Varacca–Winskel (DOI `10.1017/S0960129505005074`), McIver–Morgan's monograph (DOI `10.1007/b138392`) and Affeldt et al.'s article on monae's combined monad (DOI `10.1017/S0956796821000137`), which are cited by the sources read but were not themselves read. Build times, checking times, memory use and compiled sizes of all three developments. Any logic in clutch other than Clutch, Eris, Coneris and Foxtrot.
- **Unknown:** whether every scheduler, restricted to executions that start with empty tapes, is behaviourally equal to a tape-oblivious one (section 8); whether the fractions quoted for Popescu et al.'s `d5` are a slip or reflect a step-counting convention not captured by the toy (section 2); run-time overhead of scheduler-cooperative enforcement.
- **Known not to apply:** uniform-scheduler noninterference theorems to round-robin or priority schedulers; possibilistic noninterference to any deterministic or probabilistic refinement of the scheduler; the sequential erasure lemma (`erasable`, no scheduler) to the concurrent language; specification-side presampling in Foxtrot.
- **Unsupported by the tools:** dividing the contents of one tape between threads; Polaris adequacy for schedulers under which the program does not terminate within a fixed bound; continuous distributions in the examined logics.
- **Attractive conclusions the evidence does not support:** that "for all schedulers" in a paper's headline theorem includes schedulers that can read ghost state; that padding or atomic sections make a program secure on real hardware (step counts are not time); that the toy probes say anything quantitative about the cited systems; that convex sets of distributions and scheduler-indexed families are interchangeable (their relation, via randomizing schedulers, is standard but was not checked here).

## Evidence

All repository material was read on 2026-11-19 (US Pacific time; 2026-11-20 UTC) from source archives of the pinned revisions; all papers were retrieved on the same day.

Source locations (path, then the items used):

- `logsem/clutch` @ `cc81450edd699bfcd9fa806d628a57d16c48f75d`: `theories/con_prob_lang/lang.v` (`head_step` cases for `AllocTape`/`Rand`, `state_step`, class `TapeOblivious`); `theories/prob/mdp.v` (`scheduler`); `theories/common/sch_erasable.v`; `theories/common/erasable.v`; `theories/con_prob_lang/erasure.v`; `theories/coneris/weakestpre.v` (comment "we allow big state steps which are sch_erasable to tape oblivious schedulers"); `theories/coneris/primitive_laws.v`; `theories/coneris/error_rules.v` (`state_update_presample_exp`); `theories/coneris/wp_update.v` (`state_update_def`); `theories/coneris/adequacy.v` (`wp_pgl_multi`, `wp_pgl_lim`, `sch_mass_1`, `wp_safety`); `theories/coneris/README.md`; `theories/coneris/examples/con_two_add.v`; `theories/foxtrot/examples/presample_rhs.v`; `theories/foxtrot/binary_rel/binary_adequacy_rel.v`; `theories/clutch/adequacy.v`; `theories/eris/adequacy.v`; `theories/prob_lang/erasure.v`; `README.md` (publications, dependency versions, axioms).
- `jtassarotti/polaris` @ `c7873f05214351d54cacf3d8482625ee33ad3288`: `theories/program_logic/prob_language.v` (`trace`, `scheduler`, `trace_step`); `theories/heap_lang/adequacy.v`; `proba/theories/idxval/ival.v`, `pival.v`, `pival_dist.v`, `irrel_equiv.v`; `theories/tests/prob_fork_flip.v`; `README.md`.
- `affeldt-aist/monae` @ `66f2b98c7cb29059f88380245e1d43046780d523`: `theories/core/hierarchy.v` (`isMonadProb`, `isMonadConvexDr`, `isMonadAltProb`); `theories/applications/counterexample_altconvexdr.v`; `theories/lib/proba_lib.v` (`arbcoin_spec`, `coinarb_spec`, `alt_absorbs_choice`, `keimel_plotkin_instance`); `theories/models/gcm_model.v`; `theories/models/altprob_model.v`.

Papers (identifiers checked against registry metadata): Volpano–Smith, corrected CSFW 1998 text at `https://hdl.handle.net/10945/7187` (journal DOI `10.3233/JCS-1999-72-305`); Sabelfeld–Sands, DOI `10.1109/CSFW.2000.856937`; Sabelfeld–Myers, DOI `10.1109/JSAC.2002.806121`; Russo–Sabelfeld, DOI `10.1109/CSFW.2006.29`; Popescu–Hölzl–Nipkow, DOI `10.1007/978-3-319-03545-1_17`; Tassarotti–Harper, DOI `10.1145/3290377` (arXiv 1802.02951); Zwart–Marsden, DOI `10.1109/LICS.2019.8785707` (arXiv 1811.06460v2); Goy–Petrişan, DOI `10.1145/3373718.3394795`; Gregersen et al., DOI `10.1145/3632868` (arXiv 2301.10061); Aguirre et al., DOI `10.1145/3674635` (arXiv 2404.14223); Li et al., DOI `10.1145/3747514` (arXiv 2503.04512); the Foxtrot paper is identified in the clutch README as DOI `10.1145/3808265` and was not read (its Rocq sources were).

### Probe A: scheduler-dependent leaks (toy interpreter)

Run with `python3 sched_leak.py` (CPython 3, standard library only).

```python
#!/usr/bin/env python3
"""Toy thread-pool interpreter (NOT any published artifact): exact distribution of the
final value of low variable l for two-thread programs under several schedulers.
A thread is a list of atomic steps; a step is ('skip',) or ('set', value)."""
from fractions import Fraction as Fr
from functools import lru_cache

def run(threads, sched, quantum=1):
    T = [tuple(t) for t in threads]
    n = len(T)
    @lru_cache(None)
    def go(pcs, l, turn, used):
        live = [i for i in range(n) if pcs[i] < len(T[i])]
        if not live:
            return ((l, Fr(1)),)
        if sched == 'uniform-live':          # uniform over unfinished threads
            picks = [(i, Fr(1, len(live)), 0, 0) for i in live]
        elif sched == 'round-robin':         # deterministic, `quantum` steps per turn
            i = turn
            while i not in live:
                i, used = (i + 1) % n, 0
            nu = used + 1
            nxt = (i, nu) if nu < quantum else ((i + 1) % n, 0)
            picks = [(i, Fr(1), nxt[0], nxt[1])]
        out = {}
        for i, p, nt, nu in picks:
            step = T[i][pcs[i]]
            l2 = step[1] if step[0] == 'set' else l
            pcs2 = pcs[:i] + (pcs[i] + 1,) + pcs[i + 1:]
            for v, q in go(pcs2, l2, nt, nu):
                out[v] = out.get(v, Fr(0)) + p * q
        return tuple(sorted(out.items()))
    return dict(go((0,) * n, None, 0, 0))

def possibilistic(threads):
    """Set of final l values reachable under SOME interleaving."""
    return sorted(run(threads, 'uniform-live'))

skip = ('skip',)
def sleep(k): return [skip] * k

def d1(h, a, pad=False, protect=False):
    # (if h>0 then sleep(a) else skip); l := 1      [branch test costs one step]
    if protect:  body = [skip]                       # whole conditional is one atomic step
    elif h > 0:  body = [skip] + sleep(a)
    else:        body = [skip] + (sleep(a) if pad else [skip])
    return body + [('set', 1)]
def d2(b): return sleep(b) + [('set', 0)]

def show(name, mk):
    print(f'--- {name}')
    for sched, q in (('uniform-live', 1), ('round-robin', 1), ('round-robin', 3)):
        r = {h: run(mk(h), sched, q) for h in (0, 1)}
        g = lambda v: str(v) if v.denominator < 10**6 else f'{float(v):.3g}'
        f = lambda d: '{' + ', '.join(f'l={k}: {g(v)}' for k, v in sorted(d.items())) + '}'
        tag = sched + (f'(q={q})' if sched == 'round-robin' else '')
        print(f'  {tag:18s} h=0 {f(r[0]):28s} h=1 {f(r[1]):28s} leak={r[0] != r[1]}')
    print('  possibilistic      h=0', possibilistic(mk(0)), ' h=1', possibilistic(mk(1)))

for a, b in ((4, 2), (100, 50)):
    show(f'timing race, sleep({a}) vs sleep({b})', lambda h: [d1(h, a), d2(b)])
show('same, high branches padded to equal length (4/2)', lambda h: [d1(h, 4, pad=True), d2(2)])
show('same, high conditional made atomic ("protect") (4/2)', lambda h: [d1(h, 4, protect=True), d2(2)])
# d5 of Popescu-Hoelzl-Nipkow Example 3: ((if h=0 then h:=1;h:=2 else h:=3); l:=4) || l:=5
for ifstep in (1, 0):
    mk = lambda h: [[skip] * (ifstep + (2 if h == 0 else 1)) + [('set', 4)], [('set', 5)]]
    show(f'd5-shaped race, branch test costs {ifstep} step(s)', mk)
```

Output:

```text
--- timing race, sleep(4) vs sleep(2)
  uniform-live       h=0 {l=0: 1/2, l=1: 1/2}         h=1 {l=0: 37/256, l=1: 219/256}  leak=True
  round-robin(q=1)   h=0 {l=0: 1}                     h=1 {l=1: 1}                     leak=True
  round-robin(q=3)   h=0 {l=0: 1}                     h=1 {l=1: 1}                     leak=True
  possibilistic      h=0 [0, 1]  h=1 [0, 1]
--- timing race, sleep(100) vs sleep(50)
  uniform-live       h=0 {l=0: 1, l=1: 1.59e-13}      h=1 {l=0: 1.49e-05, l=1: 1}      leak=True
  round-robin(q=1)   h=0 {l=0: 1}                     h=1 {l=1: 1}                     leak=True
  round-robin(q=3)   h=0 {l=0: 1}                     h=1 {l=1: 1}                     leak=True
  possibilistic      h=0 [0, 1]  h=1 [0, 1]
--- same, high branches padded to equal length (4/2)
  uniform-live       h=0 {l=0: 37/256, l=1: 219/256}  h=1 {l=0: 37/256, l=1: 219/256}  leak=False
  round-robin(q=1)   h=0 {l=1: 1}                     h=1 {l=1: 1}                     leak=False
  round-robin(q=3)   h=0 {l=1: 1}                     h=1 {l=1: 1}                     leak=False
  possibilistic      h=0 [0, 1]  h=1 [0, 1]
--- same, high conditional made atomic ("protect") (4/2)
  uniform-live       h=0 {l=0: 11/16, l=1: 5/16}      h=1 {l=0: 11/16, l=1: 5/16}      leak=False
  round-robin(q=1)   h=0 {l=0: 1}                     h=1 {l=0: 1}                     leak=False
  round-robin(q=3)   h=0 {l=0: 1}                     h=1 {l=0: 1}                     leak=False
  possibilistic      h=0 [0, 1]  h=1 [0, 1]
--- d5-shaped race, branch test costs 1 step(s)
  uniform-live       h=0 {l=4: 15/16, l=5: 1/16}      h=1 {l=4: 7/8, l=5: 1/8}         leak=True
  round-robin(q=1)   h=0 {l=4: 1}                     h=1 {l=4: 1}                     leak=False
  round-robin(q=3)   h=0 {l=4: 1}                     h=1 {l=5: 1}                     leak=True
  possibilistic      h=0 [4, 5]  h=1 [4, 5]
--- d5-shaped race, branch test costs 0 step(s)
  uniform-live       h=0 {l=4: 7/8, l=5: 1/8}         h=1 {l=4: 3/4, l=5: 1/4}         leak=True
  round-robin(q=1)   h=0 {l=4: 1}                     h=1 {l=4: 1}                     leak=False
  round-robin(q=3)   h=0 {l=5: 1}                     h=1 {l=5: 1}                     leak=False
  possibilistic      h=0 [4, 5]  h=1 [4, 5]
```

### Probe B: equations of convex sets of distributions over Bool (toy)

Run with `python3 convex_laws.py`.

```python
#!/usr/bin/env python3
"""Toy model (NOT monae's Rocq model): the convex-powerset construction restricted to
outcome type Bool. A distribution on Bool is q = Pr[True]; a computation is a non-empty
convex set of distributions, i.e. an interval (lo, hi) with 0 <= lo <= hi <= 1."""
from fractions import Fraction as Fr
from itertools import product

G = [Fr(i, 4) for i in range(5)]
IV = [(a, b) for a in G for b in G if a <= b]            # 15 intervals
P = [Fr(1, 4), Fr(1, 2), Fr(3, 4)]

alt = lambda A, B: (min(A[0], B[0]), max(A[1], B[1]))                    # convex hull of union
ch  = lambda p, A, B: (p*A[0] + (1-p)*B[0], p*A[1] + (1-p)*B[1])         # Minkowski mixture

def count(name, law, dom):
    bad = [x for x in dom if not law(*x)]
    print(f'{name:58s} holds {len(dom)-len(bad):5d}/{len(dom):5d}' + (f'   first counterexample {bad[0]}' if bad else ''))

T3 = list(product(IV, IV, IV)); PT3 = [(p,)+t for p in P for t in T3]
count('alt idempotent  A[]A = A',               lambda A: alt(A, A) == A, [(A,) for A in IV])
count('choice idempotent  A<p>A = A',           lambda p, A: ch(p, A, A) == A, [(p, A) for p in P for A in IV])
count('choice distributes over alt  A<p>(B[]C) = (A<p>B)[](A<p>C)',
      lambda p, A, B, C: ch(p, A, alt(B, C)) == alt(ch(p, A, B), ch(p, A, C)), PT3)
count('alt distributes over choice  A[](B<p>C) = (A[]B)<p>(A[]C)',
      lambda p, A, B, C: alt(A, ch(p, B, C)) == ch(p, alt(A, B), alt(A, C)), PT3)
count('alt absorbs choice  A[]B = (A[]B)[](A<p>B)',
      lambda p, A, B: alt(A, B) == alt(alt(A, B), ch(p, A, B)), [(p, A, B) for p in P for A in IV for B in IV])
h = Fr(1, 2)
count('consequence of the failed law  A<1/2>B = (A<1/2>B)<1/2>(A[]B)',
      lambda A, B: ch(h, A, B) == ch(h, ch(h, A, B), alt(A, B)), [(A, B) for A in IV for B in IV])

# Non-convex "plain powerset of distributions": finite sets of points, pointwise mixture.
S = frozenset({Fr(0), Fr(1)})
mix = frozenset(h*a + (1-h)*b for a in S for b in S)
print('plain powerset, no convex closure: {0,1} <1/2> {0,1} =', sorted(map(str, mix)), '-> choice idempotent:', mix == S)

# Order of resolution: demon chooses a bit, coin c ~ Bernoulli(p), result (a == c).
p = Fr(1, 3)
arbcoin = alt((p, p), (1-p, 1-p))                # demon first: a=True gives Pr=p, a=False gives 1-p
strategies = [(f_t, f_f) for f_t in (True, False) for f_f in (True, False)]   # a as a function of c
pts = [p*(f_t == True) + (1-p)*(f_f == False) for f_t, f_f in strategies]
coinarb = (min(pts), max(pts))
print(f'p={p}: demon-then-coin = [{arbcoin[0]}, {arbcoin[1]}]   coin-then-demon = [{coinarb[0]}, {coinarb[1]}]')
```

Output:

```text
alt idempotent  A[]A = A                                   holds    15/   15
choice idempotent  A<p>A = A                               holds    45/   45
choice distributes over alt  A<p>(B[]C) = (A<p>B)[](A<p>C) holds 10125/10125
alt distributes over choice  A[](B<p>C) = (A[]B)<p>(A[]C)  holds  7731/10125   first counterexample (Fraction(1, 4), (Fraction(0, 1), Fraction(1, 4)), (Fraction(0, 1), Fraction(0, 1)), (Fraction(0, 1), Fraction(1, 2)))
alt absorbs choice  A[]B = (A[]B)[](A<p>B)                 holds   675/  675
consequence of the failed law  A<1/2>B = (A<1/2>B)<1/2>(A[]B) holds    15/  225   first counterexample ((Fraction(0, 1), Fraction(0, 1)), (Fraction(0, 1), Fraction(1, 4)))
plain powerset, no convex closure: {0,1} <1/2> {0,1} = ['0', '1', '1/2'] -> choice idempotent: False
p=1/3: demon-then-coin = [1/3, 2/3]   coin-then-demon = [0, 1]
```

### Probe C: presampling against tape-reading and tape-oblivious schedulers (toy)

Run with `python3 tape_sched.py`.

```python
#!/usr/bin/env python3
"""Toy model (NOT Rocq code from any artifact): best-case termination probability over
schedulers for three two-step programs. `nodet` is a bit resolved by the scheduler;
`rand` is a fair bit; the program terminates iff the two bits agree, else diverges.
A scheduler is a function from what it observes to the bit it picks."""
from fractions import Fraction as Fr
from itertools import product
half = Fr(1, 2)

def best(prob_term):                      # sup over deterministic scheduler strategies
    return max(prob_term(s) for s in product((0, 1), repeat=2))   # s[obs] = bit chosen on observation obs

# A: rand first, then nodet. Scheduler observes the sampled bit x (it is in the thread pool).
A = best(lambda s: sum(half * (s[x] == x) for x in (0, 1)))
# B: nodet first, then rand on an EMPTY tape. Nothing about the future sample is observable.
B = best(lambda s: sum(half * (s[0] == x) for x in (0, 1)))
# C: nodet first, then rand reads a tape that was PRESAMPLED with bit t before nodet runs.
C_oblivious = best(lambda s: sum(half * (s[0] == t) for t in (0, 1)))   # scheduler ignores tape
C_tapeaware = best(lambda s: sum(half * (s[t] == t) for t in (0, 1)))   # scheduler reads tape
print('A  rand ; nodet                     sup Pr[terminate] =', A)
print('B  nodet ; rand(empty tape)         sup Pr[terminate] =', B)
print('C  presample ; nodet ; rand(tape)   tape-oblivious scheduler =', C_oblivious, '  tape-reading scheduler =', C_tapeaware)
print('presampling erasable (C == B)?  oblivious:', C_oblivious == B, '  tape-reading:', C_tapeaware == B)
```

Output:

```text
A  rand ; nodet                     sup Pr[terminate] = 1
B  nodet ; rand(empty tape)         sup Pr[terminate] = 1/2
C  presample ; nodet ; rand(tape)   tape-oblivious scheduler = 1/2   tape-reading scheduler = 1
presampling erasable (C == B)?  oblivious: True   tape-reading: False
```

## Revalidation

- **Tape side condition still present?** In a newer clutch tree, search `theories/con_prob_lang/lang.v` for `Class TapeOblivious` and `theories/coneris/adequacy.v` for the hypotheses of `wp_pgl_lim`. If the class is gone or generalized, sections 7–9 need rereading; if a lemma now converts arbitrary schedulers to tape-oblivious ones for empty initial tapes, the hypothesis in section 8 is resolved.
- **Specification-side presampling still refuted?** Check that `theories/foxtrot/examples/presample_rhs.v` still ends in `presample_RHS_is_unsound` and that the definitions of `prog1` and `prog2` keep their operand order.
- **Tape division.** Search the Coneris and Foxtrot directories for rules whose precondition holds a fractional tape assertion (`↪{#`) or whose postcondition contains two tape assertions for one label. Any hit changes the statement that tapes are indivisible.
- **monae interface.** Confirm that `isMonadAltProb` still consists of `choiceDr` alone and that `isMonadConvexDr` still carries its warning; rerun Probe B (it must report full agreement for "choice distributes over alt" and failures for the converse).
- **Scheduler dependence of a noninterference claim.** For a new program, adapt Probe A: encode each thread as a list of steps and compare the final low distributions under the uniform and round-robin schedulers for two secrets. Equality under these three schedulers is evidence only for them; inequality under any one is a counterexample to scheduler independence.
- **Polaris** is frozen at its artifact revision; its side conditions need rechecking only against a different fork.
- There is no cheap check for the second-hand rows on Sabelfeld–Sands; obtaining the paper and reading its security definition and type system is the required step.
