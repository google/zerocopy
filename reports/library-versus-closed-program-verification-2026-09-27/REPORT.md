# Library verification versus closed-program verification

## Summary

Library verification and closed-program verification answer different questions.

A **closed-program** theorem fixes the components inside a semantic boundary and proves a property of their composition. This shape is well suited to global statements: the program has no bad behavior, compilation preserves its observable behavior, or the assembled system refines one whole-system specification. The theorem can still model input, output, nondeterminism, or external calls, but those interactions occur through an environment model chosen by the theorem. Closure is therefore relative to a semantic boundary, not synonymous with “no outside world.”

A **library or open-module** theorem leaves some code outside that boundary. It proves that one component satisfies an interface or refinement judgment for every client or environment that meets stated assumptions. That extra quantification enables reuse and separate verification, but it also creates additional obligations: the component contract must capture the client-relevant behavior, the caller must establish the contract’s preconditions, and the logic must justify linking or composing independently proved components.

RustBelt and the CompCert line illustrate the distinction from different directions. RustBelt verifies an unsafe implementation against the semantic meaning of its public interface, then lets syntactically typed safe clients use that interface without reopening the implementation proof. Standard CompCert 3.18 proves semantic preservation for whole programs. The CompCert documentation explicitly limits its formal separate-object guarantee: object files may be linked with other code, but the semantic-preservation guarantee applies to programs compiled as a whole. Compositional CompCert was needed because the original whole-program simulation relations were too weak for verified separate compilation.

The distinction is not a ranking. An open theorem is not automatically stronger because it quantifies over clients, and a closed theorem is not automatically stronger because it describes the final system. They expose different proof boundaries. A typical end-to-end verification can use both: verify components under open contracts, compose them with linking theorems, and finally close the system to obtain a concrete whole-program property.

Basis: **source/publication** + **documentation** + **derived** synthesis. No fresh verifier or compiler execution was performed.

## Applicability

This report compares four precise subjects.

**RustBelt, POPL 2018, DOI `10.1145/3158154`.** RustBelt provides the unsafe-library example. It gives λRust types semantic interpretations, proves a fundamental theorem for syntactically typed code, and requires each unsafe implementation to satisfy the semantic interpretation of its public interface before it can participate in the safe-client theorem.

**CompCert 3.18, revision `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`.** This is the whole-program compiler-correctness example. `driver/Compiler.v` describes itself as “the whole compiler and its proof of semantic preservation” and defines translations for whole programs. The current CompCert manual says the formal semantic-preservation guarantee applies to whole programs compiled as a whole, even though the emitted object files can be linked with separately produced libraries.

**Compositional CompCert, POPL 2015, DOI `10.1145/2676726.2676985`.** This provides a direct contrast. Its authors characterize ordinary CompCert’s proof as a whole-program proof whose simulation relations are insufficient to prove separately compiled modules. Their replacement introduces linking semantics and structured simulations that support module-local invariants.

**Fully Composable and Adequate Verified Compilation with Direct Refinements between Open Modules, arXiv `2302.12990`.** This later work makes the open-module goal explicit: compiler-correctness refinements directly relate native semantics of modules whose behavior depends on other modules, and those refinements are designed to compose horizontally and vertically.

The report uses “library verification” broadly for proofs whose verified subject has an explicit client/context boundary. The subject may be a source library, a compilation unit, an abstract data type, or another open module. “Closed-program verification” means the theorem has already fixed the component composition inside the semantic program boundary. Neither term says whether the proof is automated, interactive, foundational, functional-correctness-oriented, or safety-only.

The report does not claim that RustBelt, CompCert, and the compositional-compilation papers use the same logic or prove the same property. Their different theorem shapes are the point of comparison.

## Findings

### Closure is relative to the theorem’s semantic boundary

A closed-program theorem fixes the program components that the semantics treats as the program. It may still interact with an environment.

CompCert’s behavior semantics, for example, includes observable events and external interactions. Its compiler theorem relates the behaviors of a source program to the behaviors of the compiled target. That theorem is still a whole-program theorem because the compiled subject is the complete program represented by the source and target program values.

This distinction prevents a common category error. “Closed program” does not mean “deterministic,” “pure,” “single-file,” or “has no I/O.” It means that the theorem does not leave an arbitrary program module to be supplied later under a linking contract.

Basis: **source** — CompCert 3.18 `driver/Compiler.v`; **documentation** — CompCert 3.18 manual; **derived** for the boundary terminology.

### An open theorem replaces fixed code with assumptions and guarantees

When a component is verified before its client or peer modules are fixed, the theorem needs a semantic description of allowed interactions.

That description may take several forms: a function specification, a semantic type, a rely/guarantee condition, a contextual refinement, or an open transition-system interface. The notation differs, but the role is stable. The component promises a guarantee provided the surrounding code respects the assumptions at the boundary.

This shifts proof work rather than removing it. A future composition must show that each side satisfies the other side’s required interface conditions. A linking or composition theorem must then establish that the individually proved judgments survive composition.

Basis: **publication** — RustBelt, Compositional CompCert, and arXiv `2302.12990`; **derived** synthesis.

### RustBelt verifies an unsafe library once at its semantic interface

RustBelt separates two proof obligations.

First, its fundamental theorem justifies ordinary syntactically typed λRust code under the semantic interpretation of Rust types. Second, a library implementation that uses unsafe operations must separately prove that it semantically inhabits its claimed public interface.

Once that implementation proof exists, a safe client can use the abstract interface through the same semantic typing theorem. The client does not need to reopen the library internals at each call site. The abstraction remains sound because the unsafe implementation has discharged the stronger semantic obligation behind the interface.

This is library verification in a strong sense: the verified artifact is reusable across clients that respect the interface, and the client theorem depends on the interface proof rather than on a fixed closed-program pairing with one client.

The guarantee is still conditional on RustBelt’s model. The theorem covers λRust and its modeled features; it is not a proof that every present-day Rust library with a safe API is sound.

Basis: **publication** — RustBelt, DOI `10.1145/3158154`, especially its semantic typing, unsafe-library verification conditions, fundamental theorem, and adequacy result.

### Ordinary CompCert’s semantic-preservation theorem is whole-program

CompCert 3.18’s compiler development composes translation passes over program values and proves whole-compiler semantic preservation. The official manual gives the high-level theorem: when compiling source program `S` succeeds and produces code `C`, the observable behavior of `C` improves on an allowed observable behavior of `S`.

That statement supports powerful end-to-end reasoning for a fixed compiled program. If a source-level proof establishes a behavior property preserved by the theorem, the compiler proof carries the property to the generated code under CompCert’s assumptions.

It does not, by itself, establish a theorem about compiling one module and later linking it against an arbitrary separately verified module. The current CompCert C documentation states this boundary directly: standard assembler/linker interoperability is useful, but “the formal guarantees of semantic preservation apply only to whole programs that have been compiled as a whole by CompCert C.”

Basis: **source** — `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, `driver/Compiler.v`; **documentation** — CompCert 3.18 manual and compiler page.

### Separate compilation needs stronger composition structure than a whole-program theorem supplies automatically

Compositional CompCert exists because a whole-program compiler proof does not automatically factor into separate module proofs.

The 2015 paper states the problem sharply: CompCert’s then-existing whole-program simulation relations were too weak to specify or prove separately compiled modules. Compiler optimizations can create private state such as stack-frame regions, while C code can expose addresses to other modules. A module-local compiler proof must control what the environment may observe or modify without pretending that the module owns the entire machine state.

Compositional CompCert adds two kinds of structure that the closed theorem did not need to expose in the same way:

1. semantics for linking independently described modules; and
2. structured simulations that can carry module-local invariants across interactions.

The later direct-refinement work pushes the same idea further. It aims for compiler-correctness theorems whose statements directly relate open source and target modules, so external users can compose the result without knowing the compiler’s internal pass structure.

Basis: **publication** — Compositional CompCert, DOI `10.1145/2676726.2676985`; arXiv `2302.12990`.

### Open verification requires the contract to be adequate for future clients

A reusable interface is useful only for properties that it actually specifies.

Suppose a library proof establishes memory safety but says nothing about the functional relationship between inputs and outputs. A future client may safely call the library, but it cannot derive a missing functional theorem from the safety contract. Conversely, a functional specification that abstracts away an effect relevant to clients can make composition fail to establish the desired whole-system property even if the implementation proof is correct relative to that underspecified interface.

Library verification therefore adds a specification-design obligation: the interface must preserve enough observable behavior and resource information for the intended clients. This is why semantic types, module-local invariants, and open refinements are substantive proof objects rather than mere API documentation.

Basis: **publication** — RustBelt and compositional-compilation subjects; **derived** consequence of their interface-based theorem structure.

### Closed verification can use global invariants that do not decompose cleanly

A closed system can sometimes prove properties by exploiting facts about the complete composition.

If all callers are known, a proof may use a global invariant that mentions several modules at once. It may reason about a fixed allocation discipline, a fixed scheduler, a fixed set of callbacks, or a fixed relation among global data structures. Such a theorem can be perfectly valid while offering no reusable contract for replacing one module.

Turning that result into library verification generally requires finding an interface that decomposes the global invariant into assumptions and guarantees. The difficulty is mathematical, not just organizational. Compositional CompCert’s module-local state invariants illustrate why the ordinary whole-program simulation proof could not simply be reused unchanged.

Basis: **publication** — Compositional CompCert; **derived** synthesis.

### Open verification does not eliminate the final closed-system proof

Open component theorems are often intermediate results.

After separately verifying modules, a system proof still has to establish that they can be linked, that their assumptions are mutually satisfied, and that the composed semantics yields the property of interest. At that point the final theorem may again be closed with respect to the application’s chosen boundary.

This gives a useful three-stage pattern:

1. prove each component under an explicit open contract;
2. compose those contracts with a sound linking theorem; and
3. close the remaining environment assumptions to derive a concrete whole-system result.

The stages can use different techniques. RustBelt’s semantic library proof and safe-client theorem already demonstrate one version of the first two stages. Verified compositional compilation provides analogous machinery for compiler boundaries.

Basis: **publication** + **derived** synthesis.

### Source modularity and compiler modularity are independent axes

A source program can have modular function or library proofs while still relying on a compiler theorem that is only whole-program. Conversely, a compiler can preserve open-module refinements even when the source-level correctness theorem for a particular application is stated globally.

The proof boundary must therefore be recorded at each layer:

- Is the source property proved for one component or for the final linked program?
- Does compiler correctness preserve a module judgment or only a whole-program behavior?
- Does the linker have a verified composition theorem?
- What environment or runtime assumptions remain after linking?

Calling an overall workflow “modular verification” without answering those questions can hide a closed boundary at a lower layer.

Basis: **documentation/publication** — CompCert, Compositional CompCert, arXiv `2302.12990`; **derived** synthesis.

### An external-call model is not automatically a library-composition theorem

Whole-program semantics often leave some operations abstract. CompCert, for example, models observable events and external functions. That abstraction is necessary for I/O and interaction, but it does not by itself provide the same guarantee as verified separate compilation.

The difference is the quantified object and the composition rule. An external-call relation can describe what an environment operation may do. A verified library theorem must additionally connect a concrete separately proved implementation to the boundary contract and show that linking preserves the relevant semantics.

This is why “the semantics already has externals” does not collapse the open-versus-closed distinction.

Basis: **source/documentation** — CompCert semantics and whole-program guarantee; **publication** — Compositional CompCert; **derived** comparison.

### For unsafe abstractions, library verification isolates the proof obligation rather than isolating trust

RustBelt supplies an especially important example. Hiding unsafe code behind a safe signature does not make the implementation trusted by theorem. The implementation must prove that it satisfies the semantic contract of the exported safe abstraction.

After that proof, clients can reason abstractly. Before it, the safe interface is only a claim.

This separates two ideas that are easy to conflate:

- **proof isolation:** clients should not repeat the unsafe implementation proof; and
- **trust isolation:** the implementation can be assumed correct because it is hidden.

RustBelt supports the first and rejects the second. The unsafe implementation becomes reusable only after its semantic interface proof is established.

Basis: **publication** — RustBelt, DOI `10.1145/3158154`.

### Neither theorem shape dominates the other

Open and closed proofs optimize for different reuse boundaries.

Open proofs are well suited to independently evolving components, reusable libraries, and heterogeneous linking. Their cost is explicit interface design and composition machinery.

Closed proofs are well suited to concrete end-to-end statements about a fixed system. Their cost is that a component theorem may not survive replacement or reuse without reconstructing the global proof.

A verification stack can combine them. The useful question is not “which is stronger?” but “where does each theorem quantify over an unknown context, where does it fix the composition, and what theorem connects those boundaries?”

Basis: **derived**, supported by all examined subjects.

## Boundaries

- **Known not to apply:** RustBelt’s theorem is about λRust and its modeled features, not full current Rust. This report does not extend the POPL 2018 result to unmodeled present-day features.
- **Known not to apply:** standard CompCert’s whole-program semantic-preservation guarantee does not become a verified separate-compilation guarantee merely because its object files can be linked with external code. The official documentation explicitly limits the formal guarantee.
- **Not examined:** this report does not audit the current implementation or proof status of Compositional CompCert or rerun its Coq development.
- **Not examined:** this report does not prove that arXiv `2302.12990` has been integrated into current upstream CompCert.
- **Not examined:** dynamic loading, plugins, JIT compilation, adversarial linking, secure compilation, and concurrency introduce additional open-world obligations beyond the sequential module distinction summarized here.
- **Not examined:** this report does not compare every modular program logic or every library-verification framework.
- **Unknown:** how much of the open-module compilation literature can be transferred directly to Rust’s current provenance, unwinding, concurrency, trait, and dynamic-dispatch semantics without additional semantic structure.
- A whole-program theorem may still contain abstract environment actions. This report does not use “closed” to mean “no environment.”
- An open theorem may quantify over contexts but still be weak if its interface omits properties needed by a client. Context quantification and specification strength are separate dimensions.
- No fresh proof assistant, compiler, linker, or executable probe was run. The report is based on immutable publications, exact CompCert source, and current official documentation.

## Evidence

### RustBelt

Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, and Derek Dreyer. “RustBelt: Securing the Foundations of the Rust Programming Language.” *Proceedings of the ACM on Programming Languages* 2, POPL, Article 66, 2018. DOI `10.1145/3158154`.

Stable project page: `https://plv.mpi-sws.org/rustbelt/popl18/`

Evidence role: **publication/source**.

High-signal claims:

- the safety proof is extensible;
- each new unsafe library has a verification condition;
- unsafe implementations are checked against semantic interpretations of their public types;
- syntactically typed clients compose with semantically justified components through the fundamental theorem and adequacy result.

### CompCert 3.18

Repository: `AbsInt/CompCert`  
Revision: `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`  
Version file blob: `5fd2882f6f042e89ce617586ce5041f5762c1766`  
`driver/Compiler.v` blob: `60fc74fec1411216425004f6d63567354e146e9c`

`VERSION` records `version=3.18`. `driver/Compiler.v` identifies its subject as the whole compiler and whole-program semantic-preservation proof and defines whole-program translation functions.

Current commented development: `https://compcert.org/doc/`  
Current manual/compiler page: `https://compcert.org/compcert-C.html`

The compiler page states that separately emitted object files can be linked with other libraries, but the formal semantic-preservation guarantees apply only to whole programs compiled as a whole.

Evidence role: **source** + **documentation**.

### Compositional CompCert

Gordon Stewart, Lennart Beringer, Santiago Cuellar, and Andrew W. Appel. “Compositional CompCert.” POPL 2015. DOI `10.1145/2676726.2676985`.

Publication record: `https://collaborate.princeton.edu/en/publications/compositional-compcert/`

The abstract states that original CompCert’s correctness proofs were whole-program proofs and that their simulation relations were too weak for separately compiled modules. It identifies language-independent linking and structured simulations as key additions.

Evidence role: **publication**.

### Direct refinements between open modules

Ling Zhang, Yuting Wang, Jinhua Wu, Jérémie Koenig, and Zhong Shao. “Fully Composable and Adequate Verified Compilation with Direct Refinements between Open Modules.” Technical report, arXiv `2302.12990`, 2023.

Record: `https://arxiv.org/abs/2302.12990`

The paper defines the target problem as verified compilation of open modules whose behavior depends on other modules. It seeks direct source/target module refinements that support compositionality and adequacy without exposing compiler-internal intermediate structure to users.

Evidence role: **publication**.

### Additional background used for terminology

Andrew W. Appel. “Verified Software Toolchain.” DOI `10.1007/978-3-642-28891-3_2`, 2012.

Project page: `https://vst.cs.princeton.edu/`

This source is used only for the broader observation that an end-to-end verification stack can combine modular component proofs with a final machine-level theorem. It is not a primary subject in `REPORT.json`.

Evidence role: **publication/documentation**.

No **execution** evidence was produced.

## Revalidation

For the immutable papers, revalidation is mainly about interpretation rather than version drift.

1. Recheck RustBelt DOI `10.1145/3158154`, especially its unsafe-library verification conditions, fundamental theorem, and adequacy theorem. Confirm that any reused claim remains scoped to λRust.
2. Recheck Compositional CompCert DOI `10.1145/2676726.2676985` for the explicit contrast between original whole-program simulations and verified separate compilation.
3. Recheck arXiv `2302.12990` when relying on the stronger direct-open-module formulation; record a newer immutable publication identity if the work is later superseded by a version of record.

For current CompCert, the cheapest discriminating check is narrower:

1. read `VERSION`;
2. inspect the whole-compiler theorem in `driver/Compiler.v`;
3. inspect the current manual’s separate-compilation/linking statement; and
4. determine whether upstream now ships a verified separate-compilation theorem for the exact release being used.

If the fourth answer changes, add a new version-specific report rather than silently generalizing this CompCert 3.18 observation.

For a new verifier or compiler, classify its theorem by asking five questions:

1. What code is fixed inside the theorem’s program boundary?
2. What code or environment is universally quantified or represented by assumptions?
3. What semantic contract connects the verified component to that context?
4. What theorem justifies linking independently proved components?
5. After composition, what assumptions remain before deriving the final whole-system property?

Those five checks usually distinguish a reusable library/open-module theorem from a whole-program theorem without reconstructing the entire proof development.