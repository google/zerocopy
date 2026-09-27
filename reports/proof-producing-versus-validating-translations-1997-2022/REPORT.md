# Proof-producing and validating translations: evidence architecture and trust boundaries

## Summary

Proof-producing translation and translation validation differ mainly in **where the evidence lives and what must be trusted at acceptance time**.

A validator can inspect a concrete source/target pair and return an acceptance decision. If the validator itself has a machine-checked soundness theorem, as in Tristan and Leroy's verified-validator pattern, the compiler implementation can remain unverified: acceptance is enough to establish the validator's stated semantic relation. No per-translation proof object has to leave the validator.

A proof-producing or certifying translator instead makes evidence for the particular translation an explicit artifact. The producer may emit a derivation, proof term, certificate, or annotations from which such a proof is reconstructed. A separate checker verifies that artifact against the concrete program and the stated policy or source/target relation. Necula's proof-carrying code established the producer/checker split for target-code safety. Blech and Poetzsch-Heffter applied the same idea to compilation correctness by generating a correctness proof for each code-generation run. Krijnen et al.'s translation-certification architecture makes the source-to-target connection especially explicit: the certificate can contain every intermediate AST plus proof terms witnessing the translation relation of every compiler pass, with semantic-preservation results instantiated on top.

These architectures are not mutually exclusive. A validator can **produce** a proof. A proof-producing certifier can internally use proof search, a boolean decision procedure, or proof by reflection to **validate** each pass. The important distinctions are instead:

- whether acceptance leaves behind independently checkable evidence for the concrete translation;
- whether the checker or validator is itself trusted, verified, or kernel-checked;
- whether the evidence proves a source/target translation relation, a target-only safety policy, or a stronger semantic-preservation theorem; and
- whether inability to construct or check evidence fails closed.

The strongest transferable lesson for Anneal is a boundary rule, not a specific implementation recommendation. A Lean proof of a theorem about generated Lean code certifies that target theorem. It does **not** by itself certify that the generated model faithfully represents the Rust input. To make a proof-producing source-to-model story, the carried evidence must cover the source/target correspondence itself, or that correspondence must be supplied by a separately verified translator theorem. A target proof and a translation certificate solve different proof obligations.

No fresh proof assistant, compiler, or certificate checker was executed for this report. The report uses published primary sources and author/publisher copies.

## Applicability

This report addresses the #3720 subject **Proof-producing versus validating translations**. It compares external assurance architectures rather than prescribing an Anneal design.

The four concrete reference points serve different roles:

- Necula, POPL 1997, establishes proof-carrying code: an untrusted producer supplies code plus a proof that the code satisfies a consumer-defined safety policy; the consumer checks the proof.
- Blech and Poetzsch-Heffter, ENTCS 2007, applies per-run proof generation to compiler code generation: each compilation run emits a proof intended to establish that the run was correct, and a separate theorem prover checks it.
- Tristan and Leroy, POPL 2008, provides the verified-validator contrast: a validator need only return acceptance, provided there is a formal proof that acceptance implies the required source/target semantic relation.
- Krijnen et al., FLOPS 2022, gives a modern translation-certification architecture in which per-pass translation relations are represented as proof-relevant inductive relations and a complete certificate can include intermediate ASTs plus proofs linking every adjacent pair.

“Proof-producing” in this report means that a concrete translation run leaves behind a proof-like artifact that an independent checker can validate later. “Validating” means that a checker analyzes the concrete translation and decides whether it satisfies the required relation. These are architectural roles, not disjoint implementation categories.

The report distinguishes **translation correctness** from **target safety**. Proof-carrying code demonstrates the proof-artifact and small-checker pattern, but its classic claim is adherence to a safety policy for the supplied target code. That is not automatically evidence that the target code is a faithful translation of some source program.

## Findings

### A proof artifact moves trust from the producer to the checker, but only for the proposition the artifact states

Proof-carrying code's core contract is asymmetric. The code producer need not be trusted. The producer supplies a safety proof with the code; the consumer validates that proof against a previously defined safety policy before execution.

This architecture removes the producer's implementation from the acceptance-time trust decision only because the proof checker verifies the claimed property independently. The property is part of the trusted boundary. A perfect proof checker is useless if the policy formalizes the wrong requirement.

The same point matters for compiler certificates. “This target program is memory safe” and “this target program is a faithful translation of source S” are different propositions. A proof artifact can establish the first without saying anything about the second. Source-level verification only transfers through compilation when the certificate, or an independently verified compiler theorem, connects source semantics to target semantics.

Necula's original PCC paper therefore provides the checker architecture, not by itself a translation-correctness theorem. Its target property is a host safety policy.

Basis: **published result** — Necula, POPL 1997; **derived** — distinction between target-only policy evidence and source/target correspondence.

### Certifying compilation makes correctness evidence specific to one compiler run

Blech and Poetzsch-Heffter describe certifying compilation as generating, for each run, a proof that the code-generation phase translated that input correctly. The proof is checked in a separate theorem prover.

This changes the failure surface relative to a once-and-for-all compiler proof. The compiler implementation may contain defects, but a defect can only lead to an accepted output if it also produces a proof that the independent checker accepts for the incorrect translation. If the compiler cannot produce a valid proof, the run is not certified.

Per-run evidence has a provenance advantage. The proof can be stored with the concrete source and target identities and rechecked later. A bare “validator returned true” outcome can also be stored, but independent later audit normally requires rerunning the validator or trusting the recorded decision and the integrity of the validator execution environment.

The cost is that proof generation and proof checking become part of every accepted compilation path. Blech and Poetzsch-Heffter report certificate checking itself as a performance bottleneck in their implementation and introduce a proof schema to reduce the cost. Proof artifacts therefore change trust placement, not the fundamental computational cost of establishing correctness.

Basis: **published result** — Blech and Poetzsch-Heffter, ENTCS 2007; **derived** — provenance comparison with decision-only validation.

### A verified validator can obtain the same pass-level assurance without exporting a proof object

Tristan and Leroy model a compiler pass as:

```text
C : L1 → L2 + Error
```

and a validator as:

```text
V : L1 × L2 → boolean.
```

They prove validator soundness:

```text
V(c1, c2) = true → c1 ≤ c2
```

for the desired semantic relation `≤`. The wrapper runs the unverified transformer, then the validator. It returns the transformed program only if the validator accepts; otherwise it returns `Error`.

The important point is that the *theorem about the validator* is reusable across runs. The accepted run does not need to carry a separate derivation of `c1 ≤ c2` outside the validator. The validator's computation plus its once-and-for-all soundness proof supplies the pass-level correctness fact.

This can be smaller and operationally simpler than materializing large proof terms for every run. Its trust boundary is different, though. The deployed validator computation must be the computation covered by the soundness theorem, and any extraction, runtime, or implementation path between proved definition and executable checker belongs in the assurance story.

Both architectures can be sound. The proof-producing design externalizes the per-run evidence; the verified-validator design internalizes the evidence search/check into a verified decision procedure.

Basis: **published result** — Tristan and Leroy, POPL 2008, §2.1 and Theorem 1; **derived** — comparison of evidence persistence and execution-path trust.

### Translation certification shows that proof-producing and validating are compatible layers

Krijnen et al. model each compiler pass by a translation relation `Ri(ti, ti+1)`. The relation describes admissible translations rather than implementing the compiler heuristic. A certifier receives successive ASTs from the actual compiler and tries to construct a derivation that they satisfy `Ri`.

Their development explicitly presents several implementation levels for this search:

1. tactic-based proof search;
2. a decision procedure returning `option (R t1 t2)`, which directly constructs a proof term; and
3. a boolean decision procedure paired with a soundness proof, in the proof-by-reflection style.

The third form looks like a verified validator, while the overall system remains proof-producing because the certification layer can retain explicit relation evidence and combine it into a whole-compilation certificate. The two labels therefore describe different axes: how the relation is established and whether an independently checkable artifact is retained.

This matters when comparing system designs. “Validator” does not imply “no proof term,” and “proof-producing compiler” does not imply that the compiler's main transformation algorithm itself constructs a low-level derivation. Proof search can live in a separate certifier.

Basis: **published result** — Krijnen et al., FLOPS 2022, §§2.1–2.4.

### A translation-relation certificate and a semantic-preservation proof are separate layers

Krijnen et al. make a distinction that is easy to lose in informal descriptions of certification.

A translation relation `Ri(ti, ti+1)` says that the concrete source and target trees are related by the pass specification. The relation can be purely syntactic. Establishing it proves that this compiler run stayed within the admissible transformations described by `Ri`.

Semantic correctness requires another theorem connecting that relation to program meaning:

```text
Ri(ti, ti+1)
→ ⟦ti⟧i ∼i ⟦ti+1⟧i+1.
```

The paper states that a complete translation certificate contains at least the intermediate ASTs and proofs of the translation relations, and that semantic-preservation results can additionally be instantiated and included as proofs over the semantic objects.

This yields a three-layer architecture:

1. **artifact identity** — the certificate is tied to the actual source, intermediates, and target;
2. **translation conformance** — each adjacent pair satisfies its pass relation; and
3. **semantic consequence** — proved theorems about those relations imply the desired preservation property.

A system can have layer 2 without layer 3. That may still provide useful regression evidence, but it is not the same as semantic preservation.

Basis: **published result** — Krijnen et al., FLOPS 2022, §§2.3–2.4.

### Whole-pipeline certificates improve provenance only if they cover every relevant boundary

The FLOPS 2022 certificate form includes the sequence of intermediate ASTs:

```text
t1, …, tn
```

and a conjunction of pass relations:

```text
R1(t1,t2) ∧ … ∧ Rn−1(tn−1,tn).
```

This is stronger provenance than a final-target proof whose source identity is only informal. A checker can see which concrete artifacts each proof leg relates.

The guarantee is still exactly as complete as the represented chain. If preprocessing, parsing, desugaring, foreign interfaces, generated support code, linking, or serialization sit outside the certificate, the certificate does not silently certify them. The proof object's explicit structure makes such gaps easier to enumerate, but it does not eliminate them.

For Anneal, this is the most important source-to-model distinction. A certificate over `LLBC → generated Lean` would not, without another leg, certify `Rust source → LLBC`. A Lean kernel proof about generated functions would not certify either translation leg merely because it was produced at the end of the pipeline.

Basis: **published result** — Krijnen et al., FLOPS 2022, §2.4; **derived** — application to multi-stage source-to-model pipelines.

### Proof artifacts support independent later checking, but artifact identity becomes part of the security boundary

A retained proof is useful only if the checker verifies it against the exact artifact whose acceptance is at stake.

PCC makes this binding obvious: the safety proof accompanies the code to be executed. Translation certification similarly bundles source, intermediates, target, and relation proofs into a concrete certificate.

This creates an additional engineering obligation absent from an abstract mathematical theorem: parsing, serialization, hashing, artifact naming, and reconstruction must not let a valid proof for artifact A be replayed as evidence for artifact B. A certificate format should therefore make identities and interpretation deterministic enough that the checker and downstream consumer agree about the bytes or syntax being certified.

This is not an argument that certificates are weaker. It is an accounting point. Proof-producing systems shrink trust in the evidence generator but increase the importance of the evidence-to-artifact binding path.

Basis: **published result** — Necula 1997 producer/consumer contract; Krijnen et al. 2022 source/intermediate/target certificate structure; **derived** — artifact-binding requirement.

### Incompleteness is compatible with soundness when failure is fail-closed

Both validator and certificate architectures can be incomplete.

A verified validator can return false because its analysis cannot establish the relation even when the transformation is actually correct. A proof-generating certifier can fail to find a derivation even when one exists. Neither threatens soundness if ordinary success requires a successful check.

The mistake is to treat “certificate generation failed” or “validator returned unknown” as an ordinary verified result. That converts an automation limitation into an unstated trust assumption.

This is particularly relevant for extensible verification pipelines. Unsupported constructs, resource exhaustion, solver `unknown`, certificate search failure, parser mismatch, and kernel rejection are all semantically different internal causes, but they share one external property: the requested proof obligation was not established.

Basis: **published result** — Tristan and Leroy 2008 on validator incompleteness and fail-closed wrapper; Krijnen et al. 2022 on proof-search procedures that may fail; **derived** — unified external failure rule.

### A proof-producing target prover does not automatically make the translator proof-producing

Lean tactics normally produce proof terms that the kernel checks. That is a proof-producing architecture **inside the target logic**. The proof term establishes the proposition encoded in Lean.

If the proposition is about a function generated from Rust, the target proof says nothing on its own about whether the generator modeled the Rust function correctly. The missing statement is a translation relation or semantic-preservation theorem connecting the source artifact to the target artifact.

There are therefore two independent opportunities for proof-producing evidence in an Anneal-like pipeline:

- a **translation certificate** that proves the exact Rust/LLBC/generated-Lean artifacts are related appropriately; and
- a **program-property proof** that proves the desired theorem about the generated Lean model.

The second cannot substitute for the first. A perfectly kernel-checked theorem about an incorrectly translated model remains a perfectly checked theorem about the wrong model.

Basis: **derived** from proof-carrying/translation-certification architecture and the distinction between translation relation and semantic consequence.

## Boundaries

This report does not argue that proof-producing translation is always preferable to a verified validator. A verified decision procedure can provide equivalent semantic assurance with less per-run proof material when its execution path and theorem are acceptable.

It does not treat “proof-producing compiler,” “certifying compiler,” “proof-carrying code,” and “translation certification” as exact synonyms. The literature uses these terms for related but different claims. PCC commonly certifies target safety; certifying compilation can certify correctness of a particular compilation; translation certification explicitly relates concrete source and target programs.

The report does not establish that the published Plutus translation relations in FLOPS 2022 all have full semantic-preservation theorems. The paper explicitly presents semantic preservation as a separate layer and says stronger semantic equivalence for the relevant languages requires techniques beyond that paper's scope.

No claim is made that a stored proof object alone solves provenance. The checker must parse and bind the proof to the correct source/target artifacts and the correct formal definitions.

No claim is made about proof-object size or checking performance for Anneal. The Blech and Poetzsch-Heffter implementation found certificate checking expensive; other proof systems and proof-by-reflection designs have different tradeoffs.

The report does not survey SNARK/STARK proof systems, proof-carrying data, typed assembly language, foundational PCC in detail, or modern proof-producing SMT solvers. Those can change evidence size and TCB structure without changing the basic distinction described here.

## Evidence

### George C. Necula — Proof-Carrying Code

George C. Necula, “Proof-Carrying Code,” POPL 1997, pp. 106–119, DOI `10.1145/263699.263712`.

Publisher abstract: `https://doi.org/10.1145/263699.263712`.

The paper establishes the producer/consumer pattern: an untrusted producer supplies code plus a proof that the code satisfies a previously defined safety policy; the host validates the proof before execution.

Evidence role: **published result**.

### Jan Olaf Blech and Arnd Poetzsch-Heffter — A Certifying Code Generation Phase

Jan Olaf Blech and Arnd Poetzsch-Heffter, “A Certifying Code Generation Phase,” Electronic Notes in Theoretical Computer Science 190(4), 2007, pp. 65–82, DOI `10.1016/j.entcs.2007.09.008`.

Author copy: `https://jblech.net/wp-content/uploads/2013/07/BlechPoetzsch-HeffterCOCV07.pdf`.

The paper defines certifying compilation operationally as generating a correctness proof for each compilation run and checking that proof in a separate theorem prover. It also reports proof-checking cost as a practical bottleneck and introduces a proof schema to improve it.

Evidence role: **published result**.

### Jean-Baptiste Tristan and Xavier Leroy — verified translation validators

Jean-Baptiste Tristan and Xavier Leroy, “Formal Verification of Translation Validators: A Case Study on Instruction Scheduling Optimizations,” POPL 2008, pp. 17–27, DOI `10.1145/1328438.1328444`.

Author copy: `https://xavierleroy.org/publi/validation-scheduling.pdf`.

Section 2.1 defines compiler-pass correctness, validator soundness, and the fail-closed wrapper. Theorem 1 establishes that a sound validator turns an otherwise unverified transformation into a formally verified wrapped pass.

Evidence role: **published result**.

### Jacco O. G. Krijnen et al. — Translation Certification for Smart Contracts

Jacco O. G. Krijnen, Manuel M. T. Chakravarty, Gabriele Keller, and Wouter Swierstra, “Translation Certification for Smart Contracts,” FLOPS 2022, LNCS 13215, pp. 94–111, DOI `10.1007/978-3-030-99461-7_6`.

Publisher-version PDF in Utrecht University's repository: `https://research-portal.uu.nl/ws/files/121604772/Krijnen2022_Chapter_TranslationCertificationForSma.pdf`.

Relevant sections:

- §2: compiler pass modeled separately from a Coq translation relation;
- §2.2: tactic proof search, direct proof-producing decision procedures, and boolean reflected checkers;
- §2.3: semantic preservation as a theorem about the translation relation rather than the relation itself;
- §2.4: complete certificate containing intermediate ASTs and proof terms for adjacent translation relations, independently checkable by a trusted kernel.

Evidence role: **published result**.

### Derived synthesis

The distinctions among target-property proofs, source/target translation certificates, and target theorem proofs are derived from the primary architectures above. The Anneal-specific discussion is a consequence of those distinctions, not a claim made by the cited papers.

Evidence role: **derived**.

## Revalidation

This report is primarily about architectural distinctions in published work, so ordinary software version drift does not invalidate it. Revalidate if the report is used to justify a concrete Anneal mechanism.

For a proposed **verified validator**, identify the exact acceptance function, its soundness theorem, the semantic relation proved by acceptance, and the deployed execution path from theorem to running checker. Confirm that every non-accepting outcome fails closed.

For a proposed **proof-producing translator**, identify the exact proposition encoded by the certificate, the proof checker/kernel, the artifact identity bound into the proposition, and all parsing/serialization steps before checking. Confirm that modifying the source or target cannot leave a certificate valid for the wrong pair.

For a proposed **translation-certification chain**, list every intermediate artifact and relation. Check whether each relation only characterizes an admissible syntactic transformation or also has a semantic-preservation theorem. Do not infer the latter from the existence of the former.

For a proposed **Lean target proof**, state explicitly whether the theorem is only a property of the generated Lean model or also contains/checks source-to-model correspondence evidence. If no source/target relation appears in the theorem chain, classify the translation boundary separately rather than calling the target proof a translation certificate.

The cheapest literature recheck is:

1. Tristan and Leroy 2008 §2.1 for verified-validator soundness and fail-closed wrapping;
2. Krijnen et al. 2022 §§2.2–2.4 for the spectrum from proof-producing search to reflected checking and for the separation of translation relations from semantic preservation; and
3. Necula 1997 for the producer/checker trust split and target-policy nature of classic PCC.