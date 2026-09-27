# Operational semantics versus functional translation

## Summary

Operational semantics and functional translation solve different parts of a verification problem. An operational semantics describes how a program executes: states step or evaluate, effects become observable behavior, and failure, divergence, nondeterminism, memory, or resources can remain explicit. A functional translation instead maps the supported source computation into a proof-oriented target function or term. That translation can remove much of the operational machinery from day-to-day proofs, but it creates a correspondence obligation: a theorem about the target function is a theorem about the source only to the extent that the translation and its models preserve the source behaviors relevant to the claim.

Aeneas illustrates the tradeoff directly. Its 2022 design gives LLBC an ownership-centric, value-based functional semantics and translates LLBC to a pure lambda calculus. Mutable borrows are handled by backward functions that return reconstructed values rather than by exposing source memory to the proof engineer. This can turn verification into ordinary functional reasoning. The same paper treats the generated pure translation as trusted rather than emitting a per-program refinement proof, so the simpler proof surface does not by itself discharge the source-to-target semantic bridge.

The 2024 Aeneas work supplies a complementary operational foundation. It proves that LLBC is a correct high-level view of a lower-level heap-and-address execution model, that symbolic LLBC execution abstracts concrete LLBC execution, and that successfully symbolically checked programs do not get stuck in the lower-level model. Those results show how an ownership-centric proof model can be justified against a more operational model. They do not, by themselves, turn the production LLBC-to-Lean translator into a mechanically verified compiler.

CompCert provides the contrasting verified-compiler pattern. Its source and target languages have formal dynamic semantics, compiler passes are connected by simulations, and those simulations compose into a whole-compiler semantic-preservation result. The proof therefore keeps the execution relation central even though the compiler itself is implemented functionally.

For Anneal, the useful distinction is not "operational semantics or functions." A functional proof model can be an excellent interface, while an operational semantics supplies the behavior against which that model must be justified. The soundness question is where the connecting simulation, refinement, validation result, or explicit trust assumption lives.

No fresh Aeneas, Charon, Lean, CompCert, Rocq, or Rust execution was performed for this report.

## Applicability

This report is a conceptual comparison for verification pipelines that translate source programs into proof-oriented functional models. It uses three concrete reference points:

- *Aeneas: Rust Verification by Functional Translation* (ICFP 2022, DOI `10.1145/3547647`), which defines an ownership-centric LLBC semantics and a functional translation;
- *Sound Borrow-Checking for Rust via Symbolic Semantics* (ICFP 2024, DOI `10.1145/3674640`), which proves simulation/abstraction properties relating LLBC and a lower-level pointer semantics; and
- CompCert 3.18 at `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, whose correctness development composes simulations between formal dynamic semantics.

The current Anneal comparison point is `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, which selects Aeneas `nightly-2026.06.03`. Exact implementation details for that release are intentionally left to the existing Aeneas reports in this corpus; this report explains the semantic design space those details inhabit.

Here, **operational semantics** means a formal execution relation over program configurations, whether given as small steps, big steps, traces, or another behavior-producing relation. It does not imply one particular proof assistant or one particular memory model.

Here, **functional translation** means a transformation from the source representation into a function-oriented target representation intended for verification. The target may still contain explicit result/error types, state parameters, monads, recursion, or other encodings of non-pure behavior. "Functional" therefore does not mean "the source program was pure" or "all effects disappeared without proof."

## Findings

### The two approaches put complexity in different places

An operational semantics keeps the program's execution structure visible to the logic. A state can contain memory, local variables, resources, an environment, or other machine components. A step or evaluation judgment can directly distinguish normal progress, failure, divergence, nondeterministic choices, and externally visible events.

That directness gives a natural source of truth for semantic preservation. If a compiler or abstraction is correct, a simulation or refinement can connect executions in one semantics to executions in another. The cost is proof burden: program proofs may need to carry state relations, invariants, memory correspondence, or resource reasoning that are incidental to the functional property a user actually cares about.

Functional translation moves some of that burden into the translator. It produces a target term whose ordinary inputs, outputs, recursion, and algebraic data types encode source behavior. Proofs over that target can then use the theorem prover's native functional reasoning instead of repeatedly reconstructing low-level state relationships.

The complexity has not vanished. It has moved from every user proof into the definition and justification of the translation. That relocation is valuable when the translation is reusable across many proofs, but the source-to-target relation remains part of the end-to-end argument.

Basis: Aeneas 2022 **design** + CompCert **semantic-preservation architecture** + **derived comparison**.

### Aeneas functionalizes ownership rather than exposing source memory

The 2022 Aeneas design starts from LLBC, a Rust-oriented intermediate language whose semantics is value-based and ownership-centric. Its verification-facing model deliberately avoids ordinary addresses and pointer arithmetic for the supported safe-Rust fragment. Borrows and loans remain semantic objects, but the user is not asked to prove properties directly over a concrete heap for every function.

The LLBC-to-pure translation goes further. In particular, a mutable borrow cannot be modeled simply as an immutable target value because source execution can later return an updated value to the owner. Aeneas addresses this with backward functions: the forward computation can return a function or reconstructed value that represents what flows back when a borrow ends. State mutation is therefore represented as functional data flow.

This is an example of a general technique, not evidence that stateful source semantics are unnecessary. The translation is useful precisely because its construction is intended to preserve the source ownership behavior while presenting a simpler target interface.

Basis: Aeneas 2022 **formal design**.

### Functionalization changes the proof surface, not the required theorem strength

Suppose a target theorem proves `P` about a generated function `f_t`. That theorem can be completely correct in the target logic while still failing to establish `P` about the source function `f_s` if the translation from `f_s` to `f_t` omitted a source behavior, modeled an effect too narrowly, or mistranslated a control-flow path.

A complete source-level argument therefore has two logically distinct pieces:

1. a theorem about the target model; and
2. a correspondence result that lets the target theorem be transported back to the source behavior.

The correspondence can be a global compiler-correctness proof, a proof-producing translation, a translation validator, a source/target simulation, or an explicitly trusted assumption. What matters is that it is present and scoped accurately.

Aeneas 2022 makes this distinction especially visible. It demonstrates substantial functional proofs over generated code, but its implemented translator is on the trusted side of that result rather than producing a machine-checked refinement certificate for each run. The current corpus's Aeneas formal-results report records that boundary separately from the strength of the target proofs.

Basis: Aeneas 2022 **paper scope** + current reference-corpus **trust-boundary analysis** + **derived proof decomposition**.

### Operational semantics naturally records behaviors that final-value equality misses

A source program's semantics can depend on more than its terminating return value. Relevant distinctions include whether it diverges, panics, gets stuck, performs I/O, mutates memory visible to a caller, interacts nondeterministically with an environment, or reaches undefined behavior.

An operational semantics can place those distinctions directly in states, traces, or behavior judgments. CompCert, for example, defines observable events and traces and gives external calls a relational semantics over arguments, memory, traces, results, and post-state. Its compiler-correctness theorem is phrased in terms of program behaviors rather than equality of final scalar values.

A functional translation can preserve the same distinctions, but only if its target representation contains enough structure. Failure may need an explicit result type; mutable state may need to be threaded through outputs; I/O may need a trace or environment model; nondeterminism may require a relation or set of results; divergence may require recursion, coinduction, partiality, or a theorem that intentionally limits the claim to partial correctness.

Therefore "translate it to a function" is not itself a semantic specification. The target type and evaluation model determine which source behaviors can still be represented.

Basis: CompCert 3.18 **source semantics** + **derived representation principle**.

### The 2024 Aeneas results show how a higher-level model can be justified operationally

The 2024 Aeneas paper does not merely assert that LLBC is an intuitive model of Rust borrowing. It relates multiple semantic levels.

First, it connects LLBC to a lower-level model with a heap and addresses, showing LLBC to be a correct high-level view within the formalized language. Second, it proves that the symbolic semantics used by the analysis correctly abstracts concrete LLBC execution. Third, it establishes the borrow-checking consequence: programs accepted by the symbolic semantics do not get stuck in the lower-level execution model, under the modeled assumptions. The join operation used for control-flow merging is included in the preservation story.

This structure is important for the operational-versus-functional comparison. A high-level, ownership-centric semantics gains credibility not because it resembles the source intuitively, but because a simulation or abstraction theorem relates it to a lower-level execution semantics. Once that relation is established, the high-level representation can support easier reasoning without pretending the lower-level behaviors never existed.

The result is still scoped to the formal languages and theorem chain of the paper. It does not automatically certify every production Charon or Aeneas implementation path.

Basis: Aeneas 2024 **proved results** + **scope boundary**.

### CompCert illustrates the direct simulation route

CompCert's correctness development gives formal dynamic semantics to its source, intermediate, and target languages. Individual compiler passes establish simulation results, and the whole compiler composes them. At version 3.18, the top-level theorem states a backward simulation from CompCert C semantics to generated assembly semantics when compilation succeeds. `Complements.v` derives the familiar behavioral statement: each behavior of the generated assembly is matched by a source behavior, modulo the treatment of undefined behavior; for safe source programs, generated behaviors refine source behaviors directly.

This architecture has a different proof interface from Aeneas's functional translation. A CompCert client can reason from source semantics and rely on the verified compiler theorem to transport allowed behaviors to assembly. Aeneas instead aims to make the generated functional program itself the convenient object of program proof.

Neither pattern dominates universally. CompCert spends major proof effort proving transformations between operationally defined languages. Aeneas spends semantic design effort turning ownership-heavy programs into a functional form that is much easier for downstream theorem proving. The relevant comparison is where users pay proof cost and where the source/target bridge is established.

Basis: CompCert 3.18 **verified compiler source** and **manual** + **derived comparison**.

### Operational and functional models can coexist in one soundness chain

The categories are not exclusive. The same system can use an operational semantics as its source model, a symbolic interpreter as an abstraction, a functional translation as its proof interface, and a theorem prover as the final checker.

A useful abstract chain is:

`source operational behavior → abstract operational/symbolic behavior → functional target evaluation → proved target property`.

Each arrow can have a different justification. One may be a simulation theorem; another may be a verified compiler pass; another may be trusted engineering; another may be checked by the target kernel. End-to-end assurance is only as strong as the weakest unacknowledged arrow relevant to the final claim.

This is the right mental model for Anneal. The presence of Lean at the end of the pipeline says a great deal about the target theorem. It says nothing automatically about an earlier arrow that has no proof, validator, or explicit assumption.

Basis: Aeneas 2022/2024 **composition** + CompCert **simulation architecture** + **derived pipeline model**.

### Functional models are especially valuable when ownership determines state flow

Rust's ownership discipline makes functionalization more attractive than it would be for an unrestricted shared-memory language. If the semantic model can establish which owner regains a value when a mutable borrow ends, the translator can return that value explicitly instead of exposing arbitrary heap aliasing to the target proof.

This does not mean Rust ownership removes all resource semantics. Interior mutability, unsafe code, concurrency, raw pointers, FFI, and other operations can cross the boundary of the ordinary functional model. A pipeline must either reject those operations, extend the semantic model, or make the resulting assumptions explicit.

For supported code, however, the payoff is substantial: the user's specification can often talk about ordinary functional inputs and outputs while the ownership machinery remains behind the translation boundary.

Basis: Aeneas 2022 **supported-fragment design** + current corpus **implementation boundary**.

### Control flow exposes a common mismatch between the models

Operational semantics can represent a loop by repeated transition steps without requiring the semantic function itself to be structurally recursive. Functional targets must choose a representation that the theorem prover accepts: recursion with a termination argument, a partial function, a fuel parameter, a monadic/coinductive representation, or another encoding.

That difference can alter the statement users prove. A total target function may require termination that the source semantics does not guarantee. Conversely, a partial-correctness theorem can intentionally say only that if the source terminates, the result satisfies a postcondition.

A translation is therefore not semantically adequate merely because terminating examples return the same values. Its handling of nontermination, failure, and recursive control flow must match the strength of the source-level theorem being claimed.

Basis: general semantic consequence, with Aeneas loop/formal-results reports as **adjacent evidence**.

### A practical comparison should name the bridge, not just the target representation

When evaluating a proof architecture, the most informative questions are:

- What is the authoritative source semantics?
- What behaviors can that semantics express: state, divergence, panic, I/O, nondeterminism, unsafe effects?
- What does the functional target retain, encode, abstract, or reject?
- What theorem or assumption relates each source execution to the target model?
- Is the translator itself verified, validated per run, proof-producing, or trusted?
- Which models or opaque operations add independent assumptions?
- Does the final proof establish partial correctness, total correctness, refinement, equivalence, or only a target-local property?

Answering those questions makes "operational versus functional" a concrete trust decomposition rather than a style preference.

Basis: **derived** synthesis.

## Boundaries

- No fresh Aeneas, Charon, Lean, CompCert, Rocq, or Rust execution was performed.
- This report is a conceptual comparison. It does not replace the current exact-revision Aeneas translation, formal-results, external-model, or resource-semantics reports.
- "Operational semantics" is not assumed to be more faithful merely because it is lower-level. A formal operational model can itself omit or abstract relevant source behavior.
- "Functional translation" is not assumed to be less sound merely because it changes representation. A proved refinement from source semantics to the function can give very strong assurance.
- The 2022 Aeneas paper is not characterized as lacking formal semantics; it provides substantial formal semantic definitions. The narrower implementation boundary is that the production translator is not thereby a mechanically verified compiler.
- The 2024 Aeneas results are not strengthened into end-to-end Rust-to-Lean compiler correctness. They establish semantic relationships for their modeled languages.
- CompCert's theorem is not treated as arbitrary-source equivalence. Its formal statement is conditional on successful compilation and accounts for source undefined behavior through its behavior-improvement/refinement relation.
- Functionalization does not imply totality. The appropriate target encoding depends on whether the desired source theorem covers termination, divergence, failure, and effects.
- This report does not prescribe Anneal's future architecture. It supplies distinctions needed to evaluate such an architecture.

## Evidence

**Aeneas functional-translation design.** Son Ho and Jonathan Protzenko, *Aeneas: Rust Verification by Functional Translation*, PACMPL 6 (ICFP 2022), DOI `10.1145/3547647`, long version `arXiv:2206.07185`. The abstract identifies the value-based ownership-centric LLBC semantics and the LLBC-to-pure-lambda-calculus translation; the paper introduces backward functions to handle borrow termination and uses the translated program as the downstream verification object.

**Aeneas operational/simulation foundation.** Son Ho, Aymeric Fromherz, and Jonathan Protzenko, *Sound Borrow-Checking for Rust via Symbolic Semantics*, PACMPL 8 (ICFP 2024), DOI `10.1145/3674640`, long version `arXiv:2404.02680`. The authors state the three results used here: LLBC correctness relative to a low-level pointer model, correctness of symbolic abstraction, and borrow-checking/non-stuckness for symbolically checked programs; they also state preservation results for the join operation.

**CompCert 3.18.** `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`.

- `driver/Compiler.v`: composition of pass simulations and whole-compiler semantic preservation.
- `driver/Complements.v`, blob `d3974c2f7c2e5d04f2a3293fa6cfdb1215e5a217`: `transf_c_program_preservation` and `transf_c_program_is_refinement` behavioral consequences.
- `common/Events.v`, blob `ac8d1bb42e4e9d2e04bc6d7c1c27ea87fbc95564`: observable traces and relational external-call semantics used by CompCert languages.
- CompCert 3.18 user manual, August 2026: high-level semantic-preservation statement and explanation that pass proofs compose into the whole compiler result.

**Current Anneal reference corpus.** At `google/zerocopy@e1ef8f81d5e12ea48c35023ef8da740ca9dbfd10` on `reference`, `reports/aeneas-formal-results-literature-2026-09-27` records the precise formal-results/trust boundary used here, while `reports/aeneas-rust-to-lean-translation-nightly-2026-06-03` records the concrete functional interface generated by Anneal's selected Aeneas release.

No evidence above is fresh **execution**.

## Revalidation

Revalidate this conceptual report only when a source changes its relevant correctness story rather than on every Anneal code revision.

For Aeneas, check later publications and mechanization for a new theorem connecting the functional translation itself to LLBC, or for proof-producing/validation machinery that removes the translator from the trusted boundary. If such a theorem appears, distinguish the formal translator from the exact production implementation and record whatever implementation-conformance bridge is proved.

For the 2024 LLBC line, check whether the lower-level-to-LLBC and symbolic-simulation results have been extended to new language features relevant to Anneal, especially unsafe operations, concurrency, interior mutability, or richer effects. Do not assume that an implementation accepting a new feature means the published semantic theorem covers it.

For CompCert, a future report should keep the same comparison only if whole-compiler correctness remains expressed through composed semantic simulations/refinement with materially similar behavior treatment. Version-specific theorem names or intermediate languages may change without changing the conceptual lesson.

For an Anneal architecture review, instantiate the comparison rather than citing it abstractly. For every stage from Rust through Charon, Aeneas, generated Lean, and the final theorem, record the source model, target model, preserved behavior relation, unsupported/effectful cases, and whether the connecting arrow is proved, validated, tested, or trusted. A target proof should be treated as a source proof only after that chain has been made explicit.