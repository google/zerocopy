# Modular foreign contracts and open execution

## Summary

A foreign interface needs both a representation connection and a behavior contract. VeriFFI connects pure functional models and dependent types to VST specifications whose C implementations must be proved. Open simulations additionally relate external queries, replies, and resumed continuations. Neither an ABI-compatible representation nor a local value theorem covers arbitrary callbacks or environmental mutation without those obligations.

## Applicability

The comparison uses the primary VeriFFI POPL 2025 publication abstract/interface description and current selected source at CertiRocq/VeriFFI 7e8cd8e7b631be066407f86c82ff60b6fc63ae0b. The current open-simulation interface is independently inspected in SJTU-PLV/CompCert e3d03ed822a7aaf452b7022c347187ed1efc1c12, separately from its RustCompCert short paper. VST's exact source safety statement is an adjacent subject.

This addresses the contract/interface mechanism behind P039/P103/P104/P105/P109/P110 and the FFI part of R078. Generics, trait selection, dynamic dispatch, recursion closure, MMIO/DMA, and concurrency are discussed as derived obligations where no concrete implementation was examined; their research questions are not declared complete.

## Findings

### Pure models and C specifications are separate artifacts

**Basis: primary publication.** VeriFFI translates Coq function/constructor types and functional models into VST function specifications. A user proves that C implementations satisfy those specifications; functional clients can then rely on their modeled behavior. Hybrid deep/shallow descriptions allow dependent structure to participate in interface generation. This is a connection between proof interfaces, rather than automatic correctness of an arbitrary foreign implementation. [POPL 2025 publication](https://doi.org/10.1145/3704860).

**Basis: source.** Current library/modelled.v:11–31 separates a primary/model type, secondary/foreign type, graph representation, and an Isomorphism. Its transparent and opaque annotations assemble different representations. Subsequent functions distinguish reflected model-function types from foreign-function types. The annotation thus identifies the intended representation bridge; it does not eliminate the need for the C operation's behavior proof.

This separation directly answers an important design question: a typed foreign value and an agreed ABI do not automatically mean that its implementation denotes the chosen pure model.

### Current source supplies local proofs and explicit unfinished work

**Basis: source.** c/spec_int63.v defines tagged integer encoding and VST function specifications. c/verif_int63.v:16 and 39 states semax_body proofs for addition and multiplication against those specifications, with proof scripts rather than a mere interface declaration. Their scope is the selected Clight functions and VST specifications, not a whole installed mixed-language application.

The pinned README explicitly calls a fully foundational connection proof work in progress. generator/FnDesc.v:88–89 contains an active admitted InGraph_list instance. This is a concrete unfinished declaration in the selected generator source; no dependency audit established that every exported local theorem uses it. The paper interface claim, current generator status, local body proofs, and complete runtime/compiler composition must remain distinct.

No current whole-pipeline theorem is inferred from the project's name or the presence of a proved primitive. Conversely, a local proved primitive is useful evidence even while other composition work remains unfinished.

### Open simulations quantify over compatible foreign interaction

**Basis: source.** SJTU common/Smallstep.v:1572–1603 defines backward-simulation obligations. Related calls must agree on validity. Initial states and final replies are related. On target external-call exposure, a related safe source state must reach a source external query; query and symbol environments must match. For every matched reply pair, the resumed continuations must again satisfy the state relation.

The step clause then matches each target transition with source Plus/Star transitions under safe-source premises. This interface exposes what compatibility means; it does not assume that every unknown foreign library has the contract or silently replace foreign execution with a pure result.

The selected current Rustlight compilation statement uses this source/target ordering. It supplies semantic preservation under the modeled calling convention, not proof that all possible foreign callers obey it or that arbitrary source code was safe.

### VST keeps external behavior in its safety proposition

**Basis: source.** VST semax_prog_rule at veric/semax_prog.v:1967–1989 concludes safety under OK_spec Espec, along with function-specification matching and initial-memory conditions. Thus the whole-program result remains relative to its external specification. Proving a callee body and proving that the chosen world satisfies Espec are different obligations.

The same distinction applies to callback execution. A callback address must be paired with the contract of the actual callable implementation, and the caller must regain the resources/invariants its continuation expects after that callback returns.

### Derived interface requirements for a future Anneal certificate

A reusable function certificate should identify the source and generated body; formal input/output representation; allowed failures; owned resources; assumptions about imports and caller states; and the proposition that resumes the caller after each external interaction. A layout equation or type tag does not establish permission to read, write, free, or retain an alias.

For a safe API, caller coverage is an explicit quantifier. Every input obtainable from permitted safe callers must satisfy the certificate's precondition. A hidden stronger alignment, initialization, lifetime, or disjointness assumption cannot be introduced by shrinking the model domain. For an unsafe API, legitimate caller requirements may appear in the contract, but the caller's proof must show where each was established.

Cross-language composition needs representation and authority together. An FFI byte slice requires length/content correspondence and appropriate lifetime/access permissions. A callback may transfer ownership or invoke reentrant code; its invariant cannot be held closed merely by assuming the callback is external. An environment that may mutate memory asynchronously requires a suitable concurrent protocol or a stated exclusion contract.

### Linking, specialization, and cycles require evidence closure

**Basis: derived.** Open-world reasoning ranges over compatible environments, not arbitrary uncontracted code. At linking time, each import must bind to a proved implementation under the same relation and ABI. An implementation selected by a trait dictionary, vtable, function pointer, or specialization needs an identity and a proof matching the abstract specification.

Generic and const-generic certificates can be parameterized over representation and arithmetic laws; per-instantiation certificates may instead specialize those obligations. Neither form removes target/layout-sensitive premises. This investigation has not compared concrete generic or dynamic-dispatch artifacts.

Mutually recursive functions need a simultaneous proof principle or a sound fixed-point/induction argument. A set of local certificates that simply assume one another's safety is not a closure argument. The Aeneas function-environment premise and VST function-specification environment point to the obligation, but do not themselves implement a new Anneal cycle checker.

For MMIO, volatile accesses, DMA, assembly, and external mutation, state which events are observable, what the environment may change, and which resources remain stable. A heap frame theorem cannot preserve a region that the contract allows external hardware to overwrite. These hardware cases remain concrete unexamined research in this wave.

### Maintenance and adoption gates

Separate interface schema generation from verification of the generated schema's meaning. Changes in type layout, calling conventions, model encodings, exception behavior, allocation/GC, external implementation, or callback protocol can invalidate a previously usable certificate without changing a local mathematical theorem.

A useful pilot would pair one independently stated pure model with a concrete foreign implementation and a caller that uses the postcondition after return. Add a callback or ownership transfer whose omission changes safety. Check the entire query/reply/resource relation, then bind it to exact linked artifacts. This is a future engineering gate; no such prototype was executed here.

## Boundaries

No Coq/Rocq, VST, VeriFFI, compiler, GC, linker, callback, or FFI executable was run. The full VeriFFI paper body was not acquired; the primary publication abstract/interface text and narrow current source support the reported mechanism. Selected proof scripts were not replayed, and transitive assumptions were not audited.

This report does not establish universal safe Rust caller coverage, native ABI correctness, complete CertiRocq runtime correctness, concurrent Rust provenance, or sound hardware access. It does not classify every VeriFFI proof as admitted. The active generator instance, the separate local C proofs, and the work-in-progress documentation are precise scoped observations.

## Evidence

- VeriFFI, Korkut/Stark/Appel, POPL 2025 article 24, DOI 10.1145/3704860; publication abstract/interface description,31-page paper identity.
- Current VeriFFI paths/blobs: README.md, 008e29f029b831407ea387854d09674c5f94c6b8; library/modelled.v, 5bfbeae5a773a0c3a4414857d7a752cb5b961881; generator/FnDesc.v, 074d71b74f7f3576e86f9e714a309627d0e72c66; c/spec_int63.v, 83f86d9968834e15a77b0333c00e8a9ab0473cdd; c/verif_int63.v, 32ba449d0cbaf4decbb0f2ae800e8e7c97e86f99.
- SJTU common/Smallstep.v, blob 027630ae27eaeb805bd1d4e86b2ef70a5bb8d77e, external/query/reply/backward clauses1572–1603; driver/Compiler.v, blob 7e793bc9dced27222ae7091769f255289745ad6b, Rustlight statement1309–1315.
- VST veric/semax_prog.v, blob 874d708d61f1d25c6ae2c1f7be263806cceec1f3 at 3c37c2e2b574e23aee8fdd1684aa0ffed227491e.
- Public primary/source acquisition 2026-10-14. Exact repository/paper identities are in metadata. No upstream mirrors or executable results were produced.

## Revalidation

Acquire the complete VeriFFI paper and replay selected body, representation, and composition proofs at compatible pins. Audit generator assumptions independently from final theorem dependencies. Instantiate an actual foreign environment and prove every query/reply/resource obligation before asserting a linked-program result. For hardware or callbacks, add the relevant environmental events and invariant protocol rather than silently inheriting ordinary heap framing.


*Authored by an AI agent acting on joshlf's behalf.*
