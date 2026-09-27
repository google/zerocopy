# RustBelt’s unsafe-abstraction model and safe-client composition

## Summary

RustBelt gives `unsafe` Rust libraries a semantic proof obligation rather than treating `unsafe` as a trusted escape from the type system. In its formal language, λRust, ordinary syntactically well-typed code is covered by a one-time fundamental theorem. A library whose implementation uses operations that the syntactic type system cannot justify must instead prove that the implementation satisfies the semantic interpretation of its public interface. That interface interpretation is the library-specific verification condition.

The two obligations compose. RustBelt’s fundamental theorem can combine syntactically typed code with components that are only semantically typed, and its adequacy theorem says that a semantically well-typed closed λRust program has no execution that ends in a stuck state. In the model, this entails memory safety and data-race freedom. Thus a syntactically typed client can use multiple unsafe-implemented libraries without re-proving each client against those libraries’ internals, provided each exceptional component has separately established the semantic typing required by its interface.

The abstraction boundary is semantic, not merely lexical. For an interior-mutable type such as `Cell<T>`, RustBelt chooses ownership and sharing predicates that describe what owning `T` and sharing `&T` mean, then proves the exported operations against those predicates. A shared reference therefore need not mean “read-only bytes”; its meaning depends on the type’s verified abstraction.

This result is an extensible soundness architecture for a realistic Rust subset, not a proof of all Rust. λRust omits or simplifies important features, including traits, relaxed atomics, panic unwinding and automatic destruction, proper type polymorphism, and unsized types. The verified libraries are λRust ports. RustBelt should therefore be reused as a precise model of how safe clients and verified unsafe abstractions compose, not as evidence that current Rust or any particular current unsafe library is already proved sound.

## Applicability

The primary subject is Jung, Jourdan, Krebbers, and Dreyer, “RustBelt: Securing the Foundations of the Rust Programming Language,” POPL 2018, DOI `10.1145/3158154`. The paper defines λRust, its semantic type interpretation in Iris, the library-verification method, the fundamental theorem, and adequacy.

The second subject is the accompanying Zenodo artifact record, DOI `10.5281/zenodo.1115560`, version `v1`, published 2017-12-13. The record states that its archive contains the `popl18` tag of the LambdaRust Coq development, both as a source tarball and as a virtual-machine image. This report inspected the artifact record but did not download or rerun the 1.5 GB artifact.

“Safe client” below means code justified by λRust’s syntactic typing rules, composed with semantically verified exceptional components. It does not mean that arbitrary code accepted by a current Rust compiler inherits the paper’s theorem. Likewise, “unsafe library” means a λRust component whose implementation needs semantic rather than purely syntactic justification; the paper’s verified examples are ports of Rust libraries to λRust.

The report answers two issue #3720 inventory items together because the same theorem structure defines both:

- RustBelt’s unsafe-abstraction model.
- RustBelt’s treatment of unsafe libraries and safe clients.

It does not select an Anneal proof architecture or claim that Anneal must adopt Iris, RustBelt, or separation logic.

## Findings

### RustBelt turns an unsafe abstraction into a semantic extension obligation

The paper motivates Rust’s problem as open-world composition. A fixed syntactic progress-and-preservation proof assumes a closed set of typing rules, while Rust libraries can internally use operations outside the safe typing discipline and expose new safe abstractions. RustBelt therefore does not attempt to make every unsafe implementation syntactically typable.

Instead, λRust types receive semantic interpretations expressed in Iris. A term can satisfy the semantic meaning of a type even when its implementation uses features the syntactic typing rules cannot derive. For a library that uses unsafe operations, the semantic interpretation of its public interface determines what the implementation must prove.

The paper summarizes the soundness argument in three obligations:

1. prove that every λRust syntactic typing rule is sound under the semantic interpretation;
2. prove adequacy from semantic typing to operational safety; and
3. for each unsafe-implemented library, prove that its implementation satisfies the predicate denoted by the semantic interpretation of its interface.

The third obligation is the extensibility point. Adding another unsafe abstraction does not require adding an unproved typing rule or redoing the core metatheory. It requires a new proof that the implementation meets the already-defined semantic contract for the interface.

Basis: **source** — paper §§1.1–1.2.

### The public type/interface is the verified boundary

RustBelt does not justify an unsafe library merely because its unsafe operations are hidden in a module. The proof must connect the implementation to the semantics promised by the exported abstraction.

For the interior-mutability case studies, the paper describes the method concretely: first choose semantic interpretations for the abstract types exported by the library, then prove that each publicly exported function satisfies the semantic interpretation of its type. The abstract type predicates therefore carry the invariant that clients may rely on, while the exported-function proofs establish that the implementation preserves that invariant.

This makes the verification boundary stronger than “unsafe code is encapsulated syntactically.” The library is a sound extension only when its implementation establishes the semantic facts that the client-facing types and functions mean.

Basis: **source** — paper §6.

### Syntactically typed clients do not need library-internal proofs repeated at each call site

Theorem 7.1, the fundamental theorem of logical relations, states that λRust’s syntactic inference rules remain valid when interpreted semantically. The paper calls out a stronger consequence than the usual “syntactically typed implies semantically typed” corollary: the theorem can glue together a program that is syntactically well-typed except for components that have been established only semantically.

Theorem 7.2 then relates semantic typing to execution: a semantically well-typed closed λRust program has no execution that ends stuck. The paper identifies invalid memory accesses and data races as stuck behaviors in the model, so this adequacy result yields memory and thread safety for semantically well-typed programs.

Consequently, once an unsafe-implemented library has proved the semantic typing demanded by its interface, ordinary syntactically typed client code can be composed with it through the same semantic theorem. The client does not need a new proof about the library’s internal unsafe operations at each use site. Multiple semantically justified components can be combined in the same argument because the fundamental theorem reasons about the semantic typing of the assembled program.

Basis: **source** — paper §7, Theorems 7.1 and 7.2; **derived** for the explicit client-proof reuse consequence.

### The client guarantee depends on the semantic interface, not on a default “shared means read-only” rule

Rust’s interior mutability is a central example of why the semantic interpretation must be extensible. RustBelt interprets a type `T` with separate ownership and sharing predicates. The sharing predicate describes what it means to own a shared reference `&T`. It must be duplicable, because shared references can be copied, but it need not denote read-only access.

That freedom lets the semantics of `&Cell<T>`, `&Mutex<T>`, and other abstractions differ from the default read-only interpretation used for simpler types. The paper’s `Cell` case, for example, uses a thread-relative persistent-borrow construction so that code holding a shared reference can temporarily gain the access needed for `get` and `set` while still reflecting `Cell`’s non-`Sync` restriction.

Thus the safe-client story is not “clients can only perform operations derivable from a fixed shallow ownership rule.” Clients operate through types whose semantic interpretations can encode richer, library-specific ownership disciplines. The unsafe implementation is responsible for proving that those richer meanings are sound.

Basis: **source** — paper §§1.2, 4, and 6.

### RustBelt’s verified examples are library proofs under one common model

The paper reports proofs for λRust ports of `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex`, `RwLock`, `mem::swap`, `thread::spawn`, `rayon::join`, and `take_mut`. Section 6 focuses on the interior-mutability examples and explains the semantic predicates used for `Cell` and `Mutex`.

These examples matter because the model is not a one-off specification for a single library. The core logical relation, lifetime logic, semantic type interpretation, and adequacy result form a common framework; each library contributes its own verification condition proof inside that framework. That is the sense in which RustBelt calls the safety proof extensible.

The examples should not be read as proofs of the exact contemporary Rust standard-library implementations. The paper explicitly describes them as λRust ports, and its operational model simplifies important Rust behaviors.

Basis: **source** — paper §§1.2 and 6.

### “Safe” in the theorem is operational safety, not unrestricted functional correctness

The adequacy theorem excludes executions that end in λRust’s stuck state. The model arranges for illegal memory accesses and data races to be able to reach that state. The paper therefore derives memory safety and thread safety from semantic typing.

This is narrower than proving every functional property a library or client may care about. Establishing that an implementation semantically inhabits an interface is the soundness condition RustBelt needs for the type system; the paper is not a general proof that each verified library meets every higher-level behavioral specification one might attach to it.

The distinction is important when reusing RustBelt as a verification pattern: the interface interpretation states the safety/resource contract required for type soundness. Additional functional-correctness properties require additional specifications and proofs.

Basis: **source** — paper §7; **derived** for the distinction from arbitrary functional specifications.

### The proof is open to new unsafe libraries without making unsafe code trusted by default

RustBelt’s extensibility is conditional. A new unsafe library may be added to the soundness story when its implementation is proved to satisfy the semantic interpretation of its interface. Merely using `unsafe` does not grant that status.

This preserves two separate trust decisions:

- the one-time metatheory says what syntactic typing, semantic typing, and adequacy mean; and
- each exceptional implementation supplies a proof that it belongs in the semantic model at its claimed interface.

For future verification work, this separation is the reusable fact: client typing, unsafe-abstraction verification, and the adequacy theorem are distinct obligations that compose. Collapsing them into “safe callers are safe” would hide the per-abstraction proof on which that statement depends.

Basis: **source** — paper §§1.2 and 7; **derived** synthesis.

### The result is machine-checked, but its formal subject is λRust rather than full Rust

The paper states that its fundamental theorem, adequacy result, and library verification conditions were formalized in Coq. The project page links both the Coq formalization and a Zenodo artifact. The artifact record says version `v1` contains the repository’s `popl18` tag as a source tarball and as a virtual machine with dependencies.

The model is intentionally not full Rust. λRust is a custom continuation-passing language designed to capture central ownership, borrowing, and lifetime mechanisms in a MIR-inspired form. The paper explicitly omits traits in its core model and uses only non-atomic and sequentially consistent atomic operations rather than Rust’s relaxed-memory behaviors.

The conclusion records further concessions: it does not model trait objects, panic unwinding, automatic destruction, proper type-polymorphic functions, or unsized types; the verified atomic-library examples are simplified relative to Rust’s weaker atomics. These omissions limit what can be transported from the theorem to current Rust without another correspondence argument.

Basis: **source** — paper §§1.2 and 9; **documentation** — project and Zenodo artifact records.

## Boundaries

- **Known not to apply:** the paper does not establish soundness for full current Rust. Its theorem is about λRust and the features modeled there.
- **Known not to apply:** traits are omitted from the core λRust presentation, and trait objects are listed among the unmodeled features.
- **Known not to apply:** relaxed atomics are not modeled; the memory model uses non-atomic and sequentially consistent atomic operations.
- **Known not to apply:** panic unwinding and automatic destruction are not covered by the reported soundness result, even though destructors of the verified libraries were proved safe in the model.
- **Known not to apply:** proper type polymorphism and unsized types are among the reported omissions.
- **Not examined:** this report did not audit the current Rust standard library or determine whether any current unsafe implementation satisfies a RustBelt-style verification condition.
- **Not examined:** this report did not compare λRust operational semantics with the current Rust abstract machine, Stacked Borrows, Tree Borrows, or compiler behavior.
- **Not examined:** this report did not rerun the Coq development or inspect the full 1.5 GB Zenodo artifact.
- **Not examined:** the report does not characterize later RustBelt work, later Iris developments, RustHorn, RefinedRust, Aeneas separation logic, or other subsequent Rust verification systems.
- **Unknown:** whether the original `popl18` artifact can still be rebuilt unmodified on a modern host outside its preserved VM. The Zenodo record supplies a preserved artifact, but no fresh build was attempted.
- The phrase “safe client” is deliberately scoped to λRust’s syntactic typing discipline. No adjacent-version or present-day Rust continuity is inferred.

## Evidence

**Primary paper.**

Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, and Derek Dreyer. “RustBelt: Securing the Foundations of the Rust Programming Language.” *Proceedings of the ACM on Programming Languages* 2, POPL, Article 66 (January 2018), 34 pages. DOI `10.1145/3158154`.

Stable project page: `https://plv.mpi-sws.org/rustbelt/popl18/`  
Paper: `https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf`

High-signal locations:

- abstract: the proof is machine-checked and extensible; each unsafe library has a verification condition;
- §1.1, pp. 2–3: safe/unsafe library motivation and the open-world limitation of closed syntactic soundness proofs;
- §1.2, pp. 3–5: semantic type interpretation, the three-part soundness decomposition, library-specific verification conditions, and the ownership/sharing-predicate model;
- §6, pp. 25–28: interior-mutability case studies; select semantic interpretations for exported abstract types and prove each public function against its semantic type;
- §7, p. 29 in the article pagination: Theorems 7.1 and 7.2 and their explicit composition consequence;
- §9, p. 31 in the article pagination: modeling concessions and omitted Rust features.

Evidence role: **source**. The paper is the defining technical account of the model and theorems reported here.

**Technical appendix.**

“RustBelt: Securing the Foundations of the Rust Programming Language – Technical appendix,” November 9, 2017.

`https://plv.mpi-sws.org/rustbelt/popl18/appendix.pdf`

The appendix gives the full λRust syntax, operational semantics, typing rules, lifetime logic, model, and theorem statements omitted from the paper’s main exposition. This run used it only to confirm the model’s operational framing and did not reconstruct the full proof from the appendix.

Evidence role: **source**.

**Artifact record.**

Zenodo record `10.5281/zenodo.1115560`, “RustBelt: Securing the Foundations of the Rust Programming Language -- Artifact,” version `v1`, published 2017-12-13.

`https://zenodo.org/records/1115560`

The record says the 1.5 GB `popl18-artifact.zip` contains the LambdaRust Coq repository’s `popl18` tag in two forms: a virtual machine with dependencies and a source tarball without dependencies. It reports MD5 `c4b564643cd7425179185ad39a044898` for the archive. This run did not independently download or hash the archive.

Evidence role: **documentation** about the preserved machine-checked artifact.

No fresh **execution** evidence was produced.

## Revalidation

For the original POPL 2018 subject, the cheapest revalidation is documentary because the paper and DOI are immutable:

1. check §§1.2, 6, and 7 of DOI `10.1145/3158154` for the three-part proof structure, the interface-derived library verification condition, and Theorems 7.1/7.2;
2. check §9 before carrying any claim from λRust to a feature omitted by the model;
3. use Zenodo DOI `10.5281/zenodo.1115560` to recover the preserved `popl18` artifact if machine-checking evidence must be rerun.

To apply the pattern to a newer Rust verification system, do not ask only whether it “supports unsafe Rust.” Check the three interfaces separately:

- what theorem justifies ordinary syntactically typed or translated client code;
- what semantic contract an unsafe abstraction must prove at its public boundary; and
- what adequacy/correspondence theorem connects the semantic judgment to the source-level safety property of interest.

Then check whether the model covers the source features used by the abstraction: pointer/provenance semantics, lifetimes, trait machinery, unwinding/destruction, concurrency and atomics, unsized types, and any other behavior material to the client guarantee.

If any of those are outside the model, preserve the gap as a separate proof obligation rather than treating the existence of a verified library interface as evidence for full-Rust soundness.
