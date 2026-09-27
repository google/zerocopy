# Reasoning about nontermination: behaviors, simulations, and proof obligations

## Summary

Nontermination is an infinite-execution property, not a syntactic property of loops or recursion and not a synonym for Rust's broader term *divergence*. A useful verification model must say which infinite behaviors exist, which observable effects they can produce, and which proof relation preserves them. A proof that only characterizes final return values cannot by itself say anything about an execution that never returns.

CompCert 3.18 gives a concrete mature model. Its whole-program semantics separates finite termination, silent divergence after a finite observable trace, reactive divergence with an infinite observable trace, and going wrong. Its compiler-correctness development contains dedicated infinite-execution simulation lemmas, so semantic preservation does not stop at finite runs. This distinction matters: a program that spins forever after producing no further I/O and a program that continues producing observable I/O forever are both nonterminating, but they do not have the same observable behavior.

The current Anneal stack illustrates a different but compatible technique. Aeneas can give supported recursive computations a partial denotation through Lean `partial_fixpoint` and a distinct `Result.div` bottom. Translation can therefore assign semantics before proving termination. A later standard `WP.spec` proof rules out `Result.div` for the invocation being proved. Termination is consequently a separate proof obligation, not something implied by successful translation or by the existence of a recursive definition.

Three practical rules follow. First, prove or preserve nontermination at the semantic level, not from surface syntax or conservative flags such as Aeneas `can_diverge`. Second, distinguish partial correctness from termination: a postcondition conditional on normal return is compatible with every execution running forever. Third, require translation/refinement arguments to cover infinite executions explicitly whenever the source contract permits them; final-state or final-value agreement is insufficient.

This report is a reusable verification-theory reference. It does not claim that CompCert's sequential behavior taxonomy is the right complete semantics for Rust, concurrency, blocking I/O, fairness, deadlock, cancellation, or operating-system termination. It also does not claim complete Aeneas coverage of Rust nontermination. The current corpus already establishes a concrete Aeneas boundary: some supported partial recursive computations can denote `Result.div`, while unconditional `NoBreak` loops are rejected at the selected Aeneas revision.

## Applicability

The CompCert subject is `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, version 3.18. Its `Behaviors.v` and `Complements.v` files are used as an exact, executable-semantics example of how a verification system represents and preserves infinite executions.

The Aeneas subject is release `nightly-2026.06.03`, commit `ac9f1bc5262a5e4ff1e24ca78617121382202727`, selected by current Anneal. Rather than duplicate its implementation inventory, this report relies on the current reference corpus's exact-pin reports for Aeneas partial functions, recursion/termination, and infinite/diverging execution.

The Rust terminology subject is the Reference revision `ad35aca481751a06afeb23820a672b0f3b11a476` associated in this corpus with nightly-2026-05-31. That evidence is used only to keep *semantic nontermination* distinct from Rust's broader source-language notion of a diverging expression.

The report is about proof structure and semantic contracts. It does not establish termination or divergence of any new Anneal or zerocopy program. No compiler, theorem prover, or translated program was freshly executed for this report.

## Findings

### Nontermination is an infinite semantic execution, not merely recursive or cyclic syntax

A recursive function, a loop, or a cyclic control-flow graph may terminate on every reachable input. Conversely, a nonrecursive program can fail to terminate because it calls a partial operation, waits forever on an environment, or repeatedly follows behavior supplied elsewhere.

The current Rust terminology report captures the same boundary from the language side: Rust's *diverging expression* means an expression that does not complete normally, which includes finite exceptional control flow such as `panic!`. This report therefore uses **nontermination** narrowly for execution that continues indefinitely rather than reaching a finite terminal outcome.

A verifier should consequently avoid treating any of the following as a proof of semantic nontermination or termination by themselves:

- the presence or absence of recursion;
- the presence or absence of a loop;
- a bottom-like result constructor in a target model;
- a conservative static flag that says a function *may* diverge;
- a function type such as Rust `!`, which excludes normal return but does not determine why.

The proof target has to quantify over executions or over a denotation whose semantics already accounts for infinite computation.

### Observable nontermination has more than one useful shape

CompCert's `program_behavior` distinguishes four whole-program outcomes. Two are infinite:

- `Diverges t`: after the finite trace `t`, execution continues forever without further observable I/O;
- `Reacts T`: execution continues forever while producing the infinite trace `T` of observable events.

The distinction is semantically useful. An implementation that turns an endlessly reactive server into an infinite silent loop has preserved nontermination in the coarse sense that neither returns, but it has not preserved the program's observable behavior.

CompCert makes the distinction operational. `state_behaves` derives silent divergence from a finite prefix followed by `Forever_silent`, and reactive divergence from `Forever_reactive`. Both infinite relations are coinductive-style execution predicates rather than terminal states.

The general lesson is not that every verifier must use these exact constructors. It is that a nontermination claim must preserve whichever observations matter to the source contract. If I/O, protocol progress, fairness events, or other effects are observable, “does not terminate” is usually too coarse a complete behavioral specification.

### Infinite executions require proof rules that are not reducible to finite-result correspondence

CompCert's simulation library has dedicated cases for infinite execution. Forward simulation transports `Forever_silent` and `Forever_reactive`; backward simulation has separate lemmas for both. The whole-program behavior theorems then preserve or relate divergence alongside termination.

That structure exposes a common proof error. A translator can agree with a source program on every terminating final value and still be wrong on an input where the source runs forever. For example, the target could terminate spuriously, silently spin instead of continuing observable interaction, or go wrong after a finite prefix. None of those failures is detectable by comparing only final states of source runs that happen to terminate.

Accordingly, a source-to-model adequacy theorem or translation-validation relation needs an explicit rule for infinite behavior whenever infinite executions are in scope. Possible techniques include coinductive simulation, trace-based behavior refinement, or a denotational partiality model with a proved correspondence. The choice of technique can vary; omitting the infinite case cannot be repaired by a strong theorem about final results.

### Partial correctness leaves nontermination unconstrained unless the contract says otherwise

A conventional partial-correctness statement says, in effect, that if an in-scope execution reaches the specified return point, its result satisfies the postcondition. Such a theorem can be true even when no execution ever returns.

The current Rust correctness/termination report makes this explicit for Anneal's domain: normal-return partial correctness does not require termination, while normal-return total correctness adds the finite-normal-return obligation. Rust-level UB-freedom is another independent requirement rather than an acceptable outcome of a terminating/nonterminating dichotomy.

For nontermination reasoning, this means a proof obligation should say which of these properties it intends to establish:

- a postcondition on terminating executions only;
- absence of semantic nontermination;
- guaranteed normal return in finite time;
- a broader liveness property, such as continued observable reaction;
- an explicitly allowed partial computation in which divergence is part of the denotation.

Using only the label “correct” hides these different obligations.

### Aeneas separates a partial program denotation from a later termination proof

At `nightly-2026.06.03`, Aeneas gives supported recursive Lean definitions a semantics through `partial_fixpoint`. Its `Result α` has separate `ok`, `fail`, and `div` cases; `div` is the bottom element used by the relevant partial-order/CCPO construction, and monadic bind propagates it.

This permits translation of supported partial recursive computations without first proving source termination. The generated definition can denote divergence instead of pretending to be total.

Termination returns at the specification boundary. The selected Aeneas WP layer makes `spec div P` false and proves its standard specification equivalent to existence of an `ok` result satisfying the postcondition. Thus a proof of the ordinary `WP.spec` shape for a particular invocation rules out modeled divergence for that invocation.

There are two separate obligations here:

1. **semantic definition:** construct a sound partial meaning for the translated program, including a divergence case;
2. **successful-use theorem:** prove that the specific invocation of interest lands in the successful part of that meaning.

A recursive specification proof may additionally have to pass Lean's own termination checker. That is a proof-term well-foundedness obligation, distinct from whether the translated Rust computation itself was defined with `partial_fixpoint`.

### A “may diverge” analysis is not a termination theorem

Aeneas `can_diverge` is deliberately conservative. Direct/mutual recursion, loops, and calls to already-known potentially divergent functions can set it. The current exact-pin report also records a trait-method propagation limitation.

Therefore both interpretations would be unsound:

- `can_diverge = true` ⇒ this invocation actually runs forever;
- `can_diverge = false` ⇒ this invocation is proven to terminate.

The flag is an analysis fact used to choose translation machinery. A semantic termination theorem needs stronger evidence: a well-founded argument, a successful total-correctness/WP theorem, a model-specific proof excluding bottom/divergence, or another sound proof rule appropriate to the semantics.

### A model can represent some nontermination while rejecting other infinite source forms

The existence of a divergence value in a target language does not imply complete source-language nontermination coverage.

The current Aeneas corpus gives a concrete example. Supported recursive computations can use `partial_fixpoint`/`Result.div`, but the exact selected revision rejects symbolic loops whose computed break context is `NoBreak` with an explicit unsupported-loop error. An unconditional Rust loop is therefore not automatically translated into a Lean computation equal to `div`.

This difference matters for adequacy. “The target model has a bottom element” is only a semantic mechanism. Coverage still depends on the frontend actually mapping each relevant source behavior into that mechanism. Unsupported translation is a different outcome from represented nontermination.

### Translation preservation must keep divergence distinct from “going wrong”

CompCert's behavior relation makes a second distinction important for unsafe-language work. `Diverges` and `Reacts` are valid program behaviors; `Goes_wrong` is the erroneous/stuck behavior. The compiler's behavior-improvement relation permits a target to improve upon a source behavior that goes wrong, but safe source behaviors—including divergence—are preserved directly by the simulation corollaries.

This is a useful template for Anneal-style contracts. A proof system should not erase semantic nontermination merely because the program never returns. Nontermination, panic/failure, unsupported translation, undefined behavior, and verifier/model error are different states of knowledge and different semantic outcomes.

The exact categories for Rust/Aeneas need not match CompCert's. The transferable principle is to define them before proving preservation, so that the theorem cannot accidentally validate a target that replaces one class with another.

### Reactive/nonreactive distinctions become even more important with external effects

CompCert's sequential trace semantics already distinguishes silent divergence from infinite observable reaction. Rust systems with I/O, concurrency, blocking operations, callbacks, signals, or external models need at least as much care.

A function waiting forever on a socket, a deadlocked pair of threads, an infinite CPU loop, and a service producing responses forever are all nonterminating at a coarse level. Their liveness and observability properties differ substantially. A sequential pure target model that maps them all to one bottom value may be adequate only for claims that intentionally discard those distinctions and have a separate proof that doing so is conservative for the property being verified.

This report does not supply that proof for Anneal. It records the requirement that any such abstraction make the lost observations explicit.

## Boundaries

- No fresh CompCert, Aeneas, Lean, Rust, or Anneal execution was performed.
- CompCert 3.18 is used as a mature verification example, not as a claim that C and Rust require identical semantic categories.
- CompCert's `Diverges`/`Reacts` distinction is sequential trace semantics. It does not by itself model scheduler fairness, deadlock, thread progress, blocking system calls, cancellation, signals, or all operating-system behavior.
- This report does not prove that current Anneal or Aeneas preserves Rust nontermination end to end.
- Aeneas's `Result.div` is a semantic value in the selected functional model. It is not asserted to distinguish all source-level ways Rust can fail to terminate.
- Aeneas's `can_diverge` is not treated as a proof oracle in either direction.
- The source-level `NoBreak` loop rejection is an exact-pin Aeneas limitation, not a theorem that every loop without syntactic `break` is semantically infinite under Rust.
- Rust's term *diverging expression* remains broader than semantic nontermination; panic and other non-normal control flow must not be silently reclassified as infinite execution.
- Partial correctness, normal-return total correctness, UB-freedom, panic-freedom, and liveness are distinct obligations. This report does not choose a single Anneal result taxonomy among them.
- The report does not prescribe whether a future Anneal model should use coinduction, partiality monads/domains, fuel, well-founded recursion, temporal logic, or another technique. It records what each technique must account for semantically.

## Evidence

**CompCert 3.18 exact source.** `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`:

- `common/Behaviors.v`, blob `822b08832f491e82fefc5b60251c13a63ef71301`: `program_behavior`; `Diverges`, `Reacts`, and `Goes_wrong`; `state_behaves`; behavior existence; forward/backward simulation results for silent and reactive infinite executions.
- `driver/Complements.v`, blob `d3974c2f7c2e5d04f2a3293fa6cfdb1215e5a217`: whole-program compiler-preservation/refinement corollaries, behavior-level specifications, and big-step preservation of terminating and diverging/reactive source executions.
- `common/Events.v`, blob `ac8d1bb42e4e9d2e04bc6d7c1c27ea87fbc95564`: finite/infinite event traces and external-call semantics used by the behavior model.

**Current reference corpus, Aeneas.** On `google/zerocopy` `reference` as observed 2026-09-27:

- `reports/aeneas-infinite-diverging-execution-nightly-2026-06-03/REPORT.md`, blob `1213aeed36bf66dee315521d8df35ab75b6edbe3`: exact-pin `can_diverge` analysis, `partial_fixpoint`/`Result.div`, trait-method limitation, and `NoBreak` unsupported-loop boundary.
- `reports/aeneas-partial-functions-nightly-2026-06-03/REPORT.md`, blob `0e26ea4d4efb818f7d6cd037dd35bf9fd12b4df3`: default partial-function semantics and the distinction between semantic partiality and later proof of successful termination.
- `reports/aeneas-recursion-termination-nightly-2026-06-03/REPORT.md`, blob `b220c5537bff84096b0f2d00972576f9f4eb4507`: recursion classification, Lean `partial_fixpoint`, `Result.div`, standard `WP.spec`, and proof-level termination boundary.

**Current reference corpus, Rust terminology.** `reports/rust-correctness-termination-terminology-nightly-2026-05-31/REPORT.md`, blob `7fed0a82cd0a6d6dd807a44e6b5bc299714bd8eb`: semantic nontermination versus Rust divergence; normal-return partial versus total correctness; independence of panic-freedom, UB-freedom, and termination.

The underlying Rust Reference evidence named by that report is `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, including `src/divergence.md` blob `5e25d6d0d944ae8a62236ce7e46f347ded3fbfcc`, `src/types/never.md` blob `fe30bce74d6ab02eb06b9d6a852f9dc3e523eec2`, and `src/expressions/loop-expr.md` blob `8e67295482c3826c841585172560d93b2823510f`.

## Revalidation

For a different verification system or a future Anneal model, revalidate nontermination with a small semantic checklist before relying on any total-correctness or preservation claim:

1. Enumerate finite and infinite execution outcomes. Identify which effects are observable during infinite execution.
2. Check whether infinite internal execution and infinite externally visible reaction are distinguished when that distinction matters to specifications.
3. Locate the actual proof rule for infinite runs: coinductive simulation, denotational bottom/partiality, temporal/liveness theorem, or another explicit mechanism. Do not infer it from finite-result preservation.
4. Check whether the source-to-target relation preserves, refines, overapproximates, or intentionally erases each infinite behavior class.
5. Separate partial-correctness theorems from proofs that exclude nontermination. Record the additional well-foundedness, progress, or semantic-exclusion obligation.
6. For Aeneas specifically, re-read `FunsAnalysis.ml`, loop handling, `ExtractBase.ml`, `Primitives.lean`, and `WP.lean`; verify whether unsupported infinite source shapes have changed and whether `Result.div` remains the fixed-point bottom excluded by the standard specification.
7. If execution evidence is needed, preserve one terminating recursive case, one input-dependent nonterminating recursive case, one loop with a reachable exit and a potentially infinite path, and one unconditional infinite loop. Record source, LLBC, generated Lean or translation error, stderr, and exact tool revisions.

A future result should be considered stronger only if it answers both questions: **what infinite behaviors does the source semantics permit?** and **what theorem or model relation accounts for those behaviors after translation?**