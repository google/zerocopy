# Trusted-computing-base accounting patterns in verification systems

## Summary

A useful trusted-computing-base (TCB) account is **claim-relative**. The components that must be trusted to accept a theorem inside a proof assistant are not the same components that must be trusted to interpret that theorem as a fact about source code, and neither set is identical to what must be trusted for a deployed machine binary to exhibit the proved behavior. Mature verification systems make those boundaries explicit instead of treating “verified” as one undifferentiated property.

Four recurring patterns are especially relevant to Anneal.

First, **small-kernel proof checking** removes proof search, tactics, and most elaboration from the logical TCB. Rocq documents this as the de Bruijn criterion: tactics construct proof terms, while the kernel type-checks them. Rocq separately exposes the assumptions on which a theorem depends through `Print Assumptions`. This separates generator correctness from checker correctness and repository-wide admissions from theorem-specific dependencies.

Second, **verified transformation** can remove a compiler pass or an entire compiler implementation from the source-to-target trust boundary, but only relative to a proved semantic-preservation theorem. CompCert writes most compiler passes in Coq and proves their correctness. Its current project documentation also uses a “verified verifier” pattern for harder optimizations: untrusted code proposes a result, while a proved checker validates that concrete result. CompCert explicitly treats extraction and runtime support as separate trusted execution paths rather than assuming that a theorem about an in-logic function automatically certifies every executable route.

Third, **proof-boundary extension** can shrink an existing TCB without changing the higher-level proof. seL4's original C-level verification assumed correctness of the compiler, assembly, hardware, and boot code. Its later binary translation-validation work checks the compiler/linker output for the concrete kernel binary, removing the compiler and linker from the trust assumptions for covered configurations. Handwritten assembly, hardware behavior, hardware-management assumptions, and boot remain explicit assumptions. This is a concrete example of TCB accounting as a versioned boundary, not a permanent list.

Fourth, **end-to-end verified checkers and bootstrapping** can remove large implementation stacks from an automated-reasoning TCB while preserving a small specification and machine-model boundary. CakeML's verified-checker documentation identifies the remaining trust explicitly: the HOL definitions of the proof system and parser, the formal machine/FFI/memory model and its correspondence to reality, and the HOL4 theorem prover and execution environment. CakeML also bootstraps its compiler inside HOL, producing a binary proved to implement the compiler itself. Self-hosting therefore reduces host-compiler trust; it does not eliminate the theorem prover, specification, or real-machine correspondence assumptions.

The reusable lesson is to account for trust in layers. For Anneal, a durable result should distinguish at least: **logical checker trust**, **theorem-specific assumptions**, **source/model correspondence**, **compiler or translator validation**, **execution-platform assumptions**, and **artifact/tool identity**. A component should leave one layer of the TCB only when an independently checked theorem, certificate, or concrete-result validator crosses that exact boundary.

## Applicability

This report addresses the #3720 item **TCB accounting patterns in other verification systems**. It is a technique/reference report rather than an inventory of the current Anneal stack. The neighboring `aeneas-trusted-base-nightly-2026-06-03` package applies trust accounting to the pinned Aeneas/Lean path; the present report extracts reusable accounting patterns from Rocq, CompCert, seL4, and CakeML.

The evidence is pinned where the source provides a stable version or publication identity:

- Rocq documentation 8.20.1 for kernel/assumption behavior, with 8.19.2 documentation for the de Bruijn-criterion explanation;
- CompCert 3.18, released 2026-08-31, plus its current research description;
- seL4's SOSP 2009 functional-correctness result, PLDI 2013 binary translation-validation result, and current project assumption documentation;
- CakeML's current project and verified-proof-checking documentation, plus its published binary-extraction TCB analysis.

This report does not claim that these systems have identical assurance goals. The point is the accounting structure: what evidence moves a component outside a claim's TCB, what assumptions remain, and how those assumptions are exposed.

## Findings

### 1. A TCB is defined by a claim, not by a repository

“Which code is trusted?” is underspecified until the claimed result is stated. At least three claims recur in the systems examined here:

1. a logical theorem is valid relative to declared assumptions;
2. a target model or generated program preserves the meaning of a source program;
3. a deployed binary on real hardware exhibits the modeled behavior.

Each claim adds a different bridge. A proof-assistant kernel can establish the first without knowing anything about Rust, C, machine code, or hardware. A compiler-correctness theorem can establish the second without proving that a physical processor implements the target ISA model. A binary-level verification can remove the compiler from the third claim while still depending on hardware and handwritten low-level code.

The accounting consequence is simple: TCB entries should be attached to a **claim boundary** and an **evidence edge**. “Lean is trusted” or “Aeneas is trusted” is less useful than “Lean's kernel and the theorem's admitted assumptions are trusted for target-level theorem validity; Charon/Aeneas correspondence remains trusted for a Rust-level interpretation unless separately validated.”

### 2. Small proof kernels move tactics and proof search out of the logical TCB

Rocq's reference manual describes its kernel as a type checker for proof terms. Tactics incrementally construct those terms; the kernel checks that the resulting term has the theorem's type. The documentation identifies this split with the de Bruijn criterion: keep a small, well-delimited trusted kernel while permitting much larger elaborators, plugins, and tactics outside that trusted core.

This is a powerful accounting pattern because it classifies tools by **what artifact they produce**. A tactic can be buggy and still fail safely if its only authority is to propose a proof term that the kernel checks. The tactic becomes part of the logical TCB only when it can bypass or extend checking through a trusted primitive.

The same pattern generalizes beyond theorem provers. If Anneal can turn a complicated inference step into a checkable certificate, witness, or proof term whose semantics are smaller and independently checked, then the generator need not be trusted for the property certified by that artifact.

Basis: Rocq 8.19.2 core-language documentation.

### 3. Assumption auditing should be theorem-specific, not package-wide

Rocq's `Print Assumptions` command reports the axioms, parameters, and variables on which a particular theorem or definition depends. The documentation also exposes unsafe typing-check bypasses through assumption reporting. Lean has a closely analogous transitive axiom audit, but Rocq is sufficient to establish the cross-system pattern: admissions and axioms are not usefully summarized merely by asking whether a library contains any.

A large verified library may contain optional axioms that do not occur in one theorem's dependency closure. Conversely, a tiny imported model may introduce the one assumption on which the final theorem depends. The trustworthy unit of accounting is therefore the **transitive dependency closure of the claimed result**, with an allowlist policy for intentional axioms or primitives.

For Anneal, this argues for preserving theorem-specific assumption evidence alongside proof results. A repository scan for `axiom` or `sorry` is useful discovery evidence; it is not a substitute for the final theorem's dependency audit.

Basis: Rocq 8.20.1 commands documentation and primitive-object documentation.

### 4. Verified compilers replace implementation trust with theorem and semantic-model trust

CompCert is written largely in Coq and proves semantic preservation between its source, intermediate, and target languages. In the ordinary verified-pass pattern, the compiler implementation is not trusted merely because it is the compiler: its correctness is a theorem checked by Coq.

That removal is not free. Trust moves to the proof checker, the formal source and target semantics, the correctness theorem actually established, and any axioms or trusted primitives used by the development. The execution route must also match the verified object. CompCert's project documentation explicitly calls out Coq extraction as the route from in-logic functions to executable Caml and separately studies verified extraction or per-run extraction validation. It also gives an example where a runtime system remained unverified even though the compiler path was proved.

This is an important accounting discipline for Anneal. A theorem about a transformation algorithm does not by itself certify an executable translator, serializer, code generator, or runtime wrapper unless the proof boundary reaches that implementation or an independent validator checks the produced artifact.

Basis: CompCert 3.18 documentation and current research objectives.

### 5. A verified verifier can remove an optimizer or generator from the TCB without verifying it

CompCert's research description gives a second pattern: difficult optimizations can run as untrusted Caml code, followed by a verifier proved correct in Coq. The verifier checks the concrete optimization result a posteriori. Only the verifier needs the proof of correctness for that boundary.

This pattern separates two engineering questions:

- **soundness:** every accepted result satisfies the preservation relation;
- **completeness/performance:** how often the untrusted generator finds a result the verifier accepts.

Bugs in the generator can cause rejection or missed optimization without invalidating accepted outputs, provided the verifier, its parser/decoder, and its semantic model are correct. A verified validator can therefore be much smaller than a verified optimizing implementation.

For Anneal, this is the strongest general argument for preferring independently checkable certificates or post-hoc validation at unstable translation boundaries. The trust reduction comes from the checker's soundness theorem, not from the generator's quality.

Basis: CompCert current research documentation.

### 6. seL4 demonstrates that the TCB can shrink when the proof boundary moves downward

The original seL4 functional-correctness result proved refinement from an abstract specification to the C implementation and explicitly assumed correctness of the compiler, assembly code, hardware, and boot code. The later binary-verification work validates the concrete compiled kernel binary against the C-level model, including compilation and linking for covered functions.

Current seL4 documentation states the resulting trust consequence directly: on architectures/configurations with binary verification, the compiler and linker no longer need to be trusted. The assumption inventory still names handwritten assembly, hardware, hardware-management behavior, boot code, and modeled information-channel limits.

This is valuable because it shows what good TCB accounting looks like in a changing system. The project does not relabel the entire stack “verified.” It records which configurations have which proof layers and lists the assumptions that remain after each layer.

For Anneal, the analogous practice is to make trust claims conditional on the exact pipeline and evidence. If one path has a checked translation certificate and another path does not, those two paths have different TCBs even if they use the same source language and final prover.

Basis: seL4 SOSP 2009, PLDI 2013 binary translation validation, current seL4 assumptions and verified-configuration documentation.

### 7. Binary verification removes compiler trust only for the concrete covered binary/configuration

seL4's binary translation validation is deliberately concrete. The PLDI 2013 work checks refinement from C semantics to the machine binary produced for seL4, and current project documentation limits binary-correctness claims to supported verified configurations. The same documentation also identifies unverified features and platform/configuration differences.

That gives a reusable boundary rule: a per-artifact validator removes a tool from the TCB **for artifacts that were actually validated under the validator's assumptions**. It does not prove the compiler globally correct, and it does not authorize transferring the result to a different compiler version, flags, architecture, or unvalidated build shape.

This is directly relevant to any future Anneal post-hoc validation. A validated LLBC or generated-Lean artifact should carry its exact producer identity, input identity, checker version, semantic-model version, and validation result. “The tool was validated once” is not a durable substitute for “this artifact is covered by this validation evidence.”

Basis: seL4 PLDI 2013 and current verified-configuration documentation.

### 8. CakeML accounts separately for formal specification, checker implementation, and real-machine correspondence

CakeML's verified-proof-checking project gives an unusually explicit end-to-end TCB statement. For its verified checkers, the project says users need to trust little more than:

- the HOL definitions of input parsers and formal semantics for the proof system/problem;
- the formal model of binary execution and its correspondence to the real ISA, FFI, and memory layout;
- the HOL4 theorem prover, including its logic, LCF-style kernel, and execution environment.

This partition is useful because it does not confuse a verified checker implementation with a verified **specification**. If the formal parser or logic accepts the wrong language, the implementation can be perfectly proved and still establish the wrong property. Likewise, a machine-code theorem depends on the adequacy of the ISA/FFI/memory model for the real platform.

For Anneal, specifications and models should therefore be first-class TCB entries, not background prose. A trusted Rust operation model, external-function model, or source-to-Lean correspondence rule deserves an explicit identity and rationale even if all code manipulating that model is verified.

Basis: CakeML verified-proof-checking documentation.

### 9. Verified bootstrapping removes host-compiler trust but not theorem-prover or machine-model trust

CakeML's compiler is bootstrapped inside HOL: the compiler compiles itself, and the project describes the result as a verified binary that provably implements the compiler. This closes a common “who compiled the verified compiler?” gap by connecting the generated compiler binary back to the verified compiler semantics.

Bootstrapping does not make the TCB empty. CakeML's own TCB analyses retain the theorem prover, the specification, the binary-extraction/output path, and correspondence between formal machine/FFI models and the environment in which the binary runs. The general pattern is that bootstrapping can eliminate one implementation dependency while leaving the logical and physical-world boundaries intact.

This distinction matters for Anneal release tooling. Reproducible builds or self-hosting improve provenance and can remove some producer trust, but they do not replace semantic evidence. Conversely, a semantic proof can be undermined operationally if the binary used in production is not tied to the proved implementation.

Basis: CakeML project documentation, verified-proof-checking documentation, and the published binary-extraction TCB analysis.

### 10. TCB accounting should preserve the difference between trusted code and trusted assumptions

The systems above repeatedly separate **code that could make the checker accept a false result** from **assumptions that define the meaning of the result**. These categories fail differently.

A kernel implementation bug is an implementation-trust failure. An incorrect ISA model is a specification/correspondence failure. An axiom is an explicit logical assumption. An unvalidated compiler is a translation/correspondence assumption. A bootloader outside the proof is an execution-boundary assumption. Collapsing all of them into one flat “TCB” list loses the information needed to reduce or audit trust.

A practical account should therefore record, for every entry:

- the claim it can invalidate;
- whether it is code, logic, a semantic model, an axiom, an environment assumption, or artifact identity;
- the evidence that justifies excluding adjacent components;
- whether the dependency is global or theorem/artifact-specific;
- the version/configuration for which the account applies.

This structure makes trust reducible. One can replace “trust compiler” with “trust validator + target semantics” without rewriting the rest of the account.

### 11. The strongest reusable Anneal model is a layered trust ledger

The cross-system evidence suggests six layers for Anneal results:

**Logical checker.** What decides whether a target theorem/proof artifact is valid? This includes the proof kernel and any deliberately trusted evaluation primitive.

**Theorem-specific assumptions.** Which axioms, admissions, opaque models, or primitive assumptions are in the final theorem's transitive closure?

**Source/model correspondence.** Why do the definitions proved in Lean denote the relevant Rust behavior? This includes Charon/Aeneas transformations and external/builtin models unless an independently checked relation removes them.

**Transformation validation.** Which translators are globally verified, which are checked per run, and which remain trusted? If a validator exists, what exact relation does it establish?

**Execution correspondence.** If the claim reaches an executable artifact, what ties formal target semantics to the actual binary, runtime, OS/FFI, and hardware?

**Artifact identity.** Which exact source, tool, configuration, generated artifact, proof environment, and checker invocation does the evidence cover?

These layers should be recorded independently. A clean target-level axiom audit can coexist with an unproved Rust-to-Lean bridge. A verified source transformation can coexist with an unmodeled FFI. A reproducible artifact can faithfully reproduce an unverified translator. The ledger prevents evidence in one layer from being silently promoted into another.

## Boundaries

This report is a comparative technique survey, not a complete TCB audit of Rocq, CompCert, seL4, or CakeML. Each system has additional version-specific primitives, runtime components, configuration constraints, and formal assumptions that are outside the narrow accounting patterns extracted here.

The report does not treat project marketing language as a proof statement. Where a boundary matters, it relies on versioned reference documentation, named proof publications, or project pages that explicitly enumerate assumptions. Even so, current project web documentation can change; the named versions/publications are the durable anchors for revalidation.

No proof artifacts, theorem-prover kernels, compilers, validators, or binaries were executed. This report therefore does not independently reproduce any cited verification result.

“Outside the TCB” always means outside the TCB **for the stated claim under the checker/validator assumptions**. It does not mean that a component is bug-free or irrelevant to availability, performance, diagnostics, reproducibility, or unsupported inputs.

This report deliberately does not restate Anneal's current pinned trusted-base inventory. That belongs to the Aeneas/Anneal-specific reports. The output here is the reusable accounting discipline those reports can apply.

## Evidence

**Rocq kernel/de Bruijn criterion.** Rocq 8.19.2, “Core language”: the kernel checks proof terms constructed by tactics and the documentation explicitly presents this as the de Bruijn criterion for a small trusted code base. Source: `https://rocq-prover.org/doc/V8.19.2/refman/language/core/index.html`.

**Rocq assumption accounting.** Rocq 8.20.1, “Commands”: `Print Assumptions` reports a theorem's transitive assumptions, and unsafe typing-check bypasses appear in assumption reporting. Source: `https://rocq-prover.org/doc/v8.20/refman/proof-engine/vernacular-commands.html`. Rocq 8.20.0 primitive-object documentation additionally states that primitive declarations are axioms and are listed by `Print Assumptions`.

**CompCert verified compiler.** CompCert 3.18 commented development, dated 2026-08-31, states that the compiler is mostly written in Coq and its semantic-equivalence correctness is proved in Coq. Source: `https://compcert.org/doc/`.

**CompCert verified-verifier and trusted execution paths.** Current CompCert research documentation says advanced optimizations can be performed by untrusted Caml code and checked by a proved verifier; it separately discusses Coq extraction, verified extraction/per-run extraction validation, and an example whose runtime system remained unverified. Source: `https://compcert.org/research.html`.

**seL4 C-level proof boundary.** Klein et al., “seL4: Formal verification of an OS kernel,” SOSP 2009. The abstract states that the proof goes from abstract specification to C and assumes compiler, assembly, and hardware correctness. Project record: `https://trustworthy.systems/publications/papers/Klein_EHACDEEKNSTW_09.abstract`.

**seL4 binary validation.** Sewell, Myreen, and Klein, “Translation validation for a verified OS kernel,” PLDI 2013. The work validates compilation and linking from the verified C program to the concrete binary while omitting assembly routines and volatile hardware accesses. Project record: `https://trustworthy.systems/publications/nictaabstracts/Sewell_MK_13.abstract`.

**seL4 current assumption ledger.** The seL4 “What the Proofs Assume” page explicitly lists assembly, hardware, hardware-management, boot, and model/channel assumptions and states that compiler/linker trust is removed on architectures covered by binary verification. Source: `https://sel4.systems/Verification/assumptions.html`. The verified-configurations page records which architecture/configuration combinations carry which proof layers.

**CakeML verified compilation and bootstrapping.** The CakeML project page describes a verified backend to concrete machine code and a compiler bootstrapped inside HOL to produce a verified binary implementing the compiler. Source: `https://www.cakeml.org/`.

**CakeML explicit checker TCB.** The CakeML verified-proof-checking page lists the remaining trust for end-to-end verified checkers: HOL parser/semantic definitions, formal binary-execution and real-machine correspondence, and HOL4's logic/kernel/execution environment. Source: `https://cakeml.org/checkers.html`.

**CakeML binary-extraction TCB analysis.** “Software Verification with ITPs Should Use Binary Code Extraction to Reduce the TCB” includes a dedicated TCB analysis distinguishing theorem-prover trust, specification trust, and the extraction/execution boundary. Source: `https://cakeml.org/itp18-short.pdf`.

## Revalidation

Revalidate this report when one of the named systems materially changes its trust architecture, not for ordinary implementation releases. In particular:

1. For Rocq, re-check the kernel/proof-term boundary, `Print Assumptions`, and any newly trusted primitive or bypass mechanism.
2. For CompCert, identify whether compiler passes, extraction, validation, or runtime assumptions have changed and whether the semantic-preservation theorem's statement has changed.
3. For seL4, use the current verified-configuration matrix and assumptions page; binary verification is configuration-specific and expands over time.
4. For CakeML, use the current compiler/checker correctness statements and explicit TCB documentation; distinguish proof-checked source definitions from the binary/execution correspondence assumptions.
5. For Anneal use, map every current evidence artifact into the six-layer ledger above. A tool or model should leave a layer only when a theorem, certificate, or concrete-result validator crosses that exact boundary.