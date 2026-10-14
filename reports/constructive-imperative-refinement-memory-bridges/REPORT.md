# Constructive imperative refinement and memory bridges

## Summary

Fiat-to-Facade, Rupicola, and Sepref generate low-level code by constructing proofs. Their useful guarantees depend on the relation being proved: safety plus partial postconditions, terminating weakest preconditions, and separation assertions for a modeled heap have different endpoints. None of these mechanisms alone verifies a Rust-to-model parser or the final executable toolchain.

## Applicability

The paper comparison covers Fiat-to-Facade IJCAR2020, Rupicola PLDI2022, and Isabelle-LLVM ITP2019. Current source observations are narrowly limited to pinned Fiat `Core.v`, its extraction README, Rupicola's compilation lemmas, and the Isabelle-LLVM README. Paper snapshots and selected current files are compared, without assuming uninterrupted theorem or feature continuity. This primarily addresses P011–P013, with partial adjacent coverage of P026.

## Findings

### Fiat: safety is an explicit conjunct

**Basis: documentation from IJCAR2020 §§3–5, PDF pp.4–12.** Extraction produces a Facade program safe from proper initial states and, when it terminates, an allowed nondeterministic result. Facade's linear ADT semantics prohibits aliasing and leakage. A separate separation-logic abstraction relation connects abstract ADT values to mutable byte memories; implementations of foreign ADTs discharge specifications. Later verified stages bridge Facade to Cito and Bedrock assembly. Thus the functional-to-imperative certificate and the concrete ADT implementation proof are different obligations. [Author paper](https://adam.chlipala.net/papers/FiatIJCAR20/FiatIJCAR20.pdf).

**Basis: source.** At `mit-plv/fiat@b7757d28f68c39c3c58192a27f217064b0b35e3b`, `src/CertifiedExtraction/Core.v:92–98` defines:

```text
ProgOk ext env prog initial final :=
  forall s, represented(s, initial ∪ ext) ->
    Safe env prog s /\
    forall s', RunsTo env prog s s' -> represented(s', final ∪ ext).
```

Here `represented` abbreviates the file's telescope/state relation `≲`, not an invented implementation relation. The definition includes `Safe` separately from the implication over `RunsTo`. An implication about successful final states alone would omit this safety conjunct. The file imports the underlying facade semantics; that imported safety predicate and concrete Bedrock backend were not rebuilt or exhaustively audited.

The pinned extraction README still specifies Coq8.4pl6 and setup commands involving `github.mit.edu` repository branches. This is a reproducibility limitation in the inspected documentation. It does not negate the paper's verified pipeline; it also does not establish that a fresh public checkout will build under a modern Rocq version.

### Rupicola: the program is a witness in a proof

**Basis: documentation from PLDI2022 §2–§3, PDF pp.3–8.** Relational compilation searches for a witness target program satisfying a semantic relation, rather than first fixing a monolithic total compiler. Rupicola specializes this approach to Gallina models and Bedrock2, with total-correctness certificates, customizable rules, monads, and representation choices. Proof search can fail or loop. Proving that the input model meets its higher-level specification remains the programmer's responsibility. The paper distinguishes its shallow-to-deep bridge from the subsequent assembly compiler. [Author paper](https://jamner.net/papers/rupicola-PLDI22.pdf).

**Basis: source.** At `mit-plv/rupicola@d33f7024a7a03c9e0f05f746dff8434d450a4f6e`, `src/Rupicola/Lib/Compiler.v:95–117` proves a sequencing compilation lemma: the first command establishes `pred0`; for every resulting trace, memory, and locals satisfying `pred0`, the second command establishes `pred1`; the combined command establishes `pred1`. Its proof invokes the imported weakening rule for Bedrock2 weakest preconditions. `compile_skip:85–93` preserves a predicate, and `compile_copy_pointer` is a separate rule. These concrete rules expose state components and semantic postconditions, rather than certifying only membership in a syntactic translation relation.

The inspected current compiler file is one rule library, not a complete execution-path audit. The paper artifact is Zenodo6330612; it was identified from the paper and was not downloaded or executed here.

### Sepref and Isabelle-LLVM: successful termination in the model

**Basis: documentation from ITP2019 §§2.1/3.2/3.5/6, printed pp.22:2–3,22:9–12,22:16.** The state-error monad distinguishes nontermination, failure, and successful results. `wp c Q s` requires a successful terminating run and its postcondition. A Hoare triple universally preserves a separating frame; refinement assertions connect mathematical values to machine words and heap structures, with representability preconditions. The paper explicitly trusts its translation from shallow Isabelle-LLVM equations to LLVM text and leaves a deep target embedding to future work. It assumes unbounded memory and omits some LLVM concepts, including poison. [Publisher paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.22/LIPIcs.ITP.2019.22.pdf).

The paper's endpoint is therefore total correctness in its Isabelle-LLVM model plus an additional trusted code-generation boundary. The separately pinned `lammich/isabelle_llvm@6be37a9c3cae74a1134dbef2979e312abb5f7f42` README establishes source identity and project purpose only. Its current generator and all refinements were not inspected deeply enough to transfer the historical trust boundary unchanged.

### Derived Anneal choices and extension costs

**Basis: derived.** For a future Anneal representation relation, define both the relation over concrete state and the obligations that authorize each operation. A telescope representation may implement a nondeterministic mathematical ADT, while separation assertions explain which mutable region implements it. These layers should remain separately reviewable. New aliasing or reclamation semantics require new relation and operation proofs; a different layout theorem cannot discharge them implicitly.

A practical proof-producing design can leave search untrusted while requiring kernel-checked local rules to construct the final theorem. It still needs a specification for failure and termination. Choosing `Safe ∧ partial-postcondition` permits nontermination while excluding modeled bad operations. Choosing a terminating `wp` requires termination proof and representable resources. Anneal's intended partial specification should not silently inherit total-correctness obligations merely because a code generator happens to use terminating HOL functions.

Model-side safety also has a direction. A synthesized safe implementation does not show that an independently supplied unsafe Rust source was safe. To use these mechanisms for program-to-model translation, Anneal would need a relation that exposes source failure and a theorem connecting the input program's operations to those modeled transitions. A source model chosen after the fact is insufficient.

Maintenance divides into input normalization, translation-rule coverage, memory representation proofs, effects/foreign-call specifications, proof automation, and serialization to the target. Failure of proof search should produce an explicit non-acceptance outcome, with an unmet obligation preserved. A successfully generated artifact must remain bound to the exact target syntax or bytes it certifies.

## Boundaries

No Coq/Rocq, Isabelle, Bedrock, or LLVM build was performed. No new verified program was generated. Dependencies, source reification, extraction, target printers, runtime behavior, and final assemblers have not been independently validated here. The report does not claim full higher-order Gallina extraction, arbitrary aliasing, concurrency, or unsafe Rust support. Immutable current pins and immutable paper artifact references establish identities, not executable compatibility.

P026 is addressed only at the design level: constructing a semantic witness differs from deriving a decision procedure for an inductive relation. The related PLDI2022 checker paper is a lead, not an inspected current checker implementation in this package.

## Evidence

- Pit-Claudel et al., *Extensible Extraction of Efficient Imperative Programs with Foreign Functions, Manually Managed Memory, and Proofs*, IJCAR2020, primary author PDF, 19 pages, §§3–5.
- Pit-Claudel/Philipoom/Jamner/Erbsen/Chlipala, *Relational Compilation for Performance-Critical Applications*, PLDI2022, DOI `10.1145/3519939.3523706`, author PDF, 16 pages, §§2–3; identified artifact `10.5281/zenodo.6330612`.
- Lammich, *Generating Verified LLVM from Isabelle/HOL*, ITP2019 article22, DOI `10.4230/LIPIcs.ITP.2019.22`, 19-page publisher PDF, narrow coordinates above.
- Fiat core blob `800d49d93ff57cc00a0d710a85bf3a454c3fc988`; extraction README blob `95d1982a30451b3c2a32cf4a7d465d2fb8c264d8`; Rupicola compiler-rule blob `e3e684b873da9dffb6523d3026344bfedac02eb7`; Isabelle-LLVM README blob `0b6b9e35f52a82b79521e9c4477f58ef58dcda7b`.
- Acquired2026-10-14 through web paper extraction and GitHub pinned-file retrieval. No PDF bytes or private source mirrors were stored. Metadata pins identify selected current source observations separately from paper claims.

## Revalidation

Read the cited definitions and imported semantic predicates at the exact pins, then check a small generated theorem using compatible dependencies. Independently identify the final code serialization and compiler boundary. For an Anneal pilot, use an operation whose layout is correct but whose authority precondition fails; require the proposed translation theorem to preserve or expose that failure. This would discriminate a value correspondence from a source-safety argument.

*Authored by an AI agent acting on joshlf's behalf.*
