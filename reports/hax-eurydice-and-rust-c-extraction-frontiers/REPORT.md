# hax, Eurydice, and Rust-to-C extraction frontiers

## Summary

Alternative extraction changes the frontend and proof-facing program; it does not automatically remove the source/model bridge. Current hax's Lean route delegates to Charon/Aeneas, while its F* route runs a phase pipeline and OCaml printer. Eurydice translates Charon output through KaRaMeL and states an informal guarantee conditional on non-panicking Rust termination. A separately inspected RustCompCert artifact states standard target-to-source backward matching, but its source and safety-verification boundaries remain explicit.

## Applicability

The source subjects are cryspen/hax cc6da074ca754ca9d406ec922daad3221aacbce5, AeneasVerif/eurydice 7332393a18a20baae808d8783266acd15121ddd2, and SJTU-PLV/CompCert e3d03ed822a7aaf452b7022c347187ed1efc1c12 (rust-verified-compiler branch when observed). Main branches were resolved to these immutable pins; no claim is made about future heads.

AeneasVerif/hax is an archived former fork and was not substituted for current hax. The current route observations do not establish a universal hax or Eurydice preservation theorem. They answer R050/R051's architecture, handling, and trust-boundary comparison; concrete preservation measurements and the complete target/compiler proof chain remain separate work.

## Findings

### hax has distinct backend routes

**Basis: source and primary documentation.** The hax frontend documentation describes export of rustc's typed AST and backend-dependent simplification. Its custom driver README identifies a rustc driver invoked by cargo-hax. The current README lists Lean via Aeneas, F*, and Rocq, among other backends. This is backend availability documentation, not semantic equivalence evidence. [Frontend documentation](https://hax.cryspen.com/frontend/), [Pinned source](https://github.com/cryspen/hax/tree/cc6da074ca754ca9d406ec922daad3221aacbce5).

Current cli/cargo-hax/src/aeneas.rs:269–280 runs Charon and Aeneas for the Lean route. The resulting layout distinguishes generated Extraction files, externally modeled Assumptions, and handwritten Verification files (391–402). It rejects Charon flags that would sever the selected LLBC handoff and warns when Aeneas output-layout overrides prevent package-file checks or cleanup. These are real invocation/identity controls; they do not prove the LLBC-to-Lean correspondence.

The F* backend in rust-engine/src/backends/fstar.rs:15–51 enumerates transformations and reuses legacy OCaml phases. These include reconstruction of assertions and loops, mutation/reference lowering, control-flow normalization, functionalization of loops, trait specifications, and cycle bundling. The OCaml printer remains part of this path. The separate OCaml backend file exposes its own implementation and phase application.

### Unsupported constructs are explicit phase outcomes

**Basis: source.** The F* pipeline invokes RejectRawOrMutPointer first. Its implementation in engine/lib/phases/phase_reject.ml:64–84 rejects the internal raw_pointer and mutable_pointer feature cases. Other mutation is handled by subsequent phases; those internal feature names should not be generalized into a statement that every syntactic Rust mutable reference is unsupported. The file also has rejection gates for remaining question marks, dynamic constructs, and unsafe-feature cases; actual backend coverage depends on which gates that backend invokes.

Type-shaped intermediate languages and rejection gates make the accepted fragment inspectable. They do not supply a semantics theorem for the transformations, source imports, or opaque library models. A target proof establishes a proposition about the produced program and its assumptions unless a separate source relation connects it to Rust.

### Eurydice's documented guarantee is deliberately conditional

**Basis: primary documentation.** The pinned README:21–27 calls its guarantee informal: a Rust program terminating without panic is intended to yield C computing the same result without UB; if Rust panics, it makes no guarantee for the generated C behavior. Lines35–41 describe Charon-to-KaRaMeL AST translation followed by more than thirty lowering passes, mixing reused and Eurydice-specific work. These are implementation intentions, not a machine-checked translation theorem. [Pinned README](https://github.com/AeneasVerif/eurydice/blob/7332393a18a20baae808d8783266acd15121ddd2/README.md).

That condition matters for a source-safety goal. A route that constrains only non-panicking source executions cannot show that a Rust execution never panics. Downstream C verification must be composed with a source failure/panic relation or an independently proved source admission argument.

### Borrowing, drops, and representation have concrete lowering seams

**Basis: source.** Eurydice AstOfLlbc.ml:603–605 maps both TRef and TRawPtr to pointer types, choosing C constness from reference kind. Its place lowering includes actual dereference cases, unlike the inspected Aeneas source interpreter. Casts and aggregate raw pointers have additional branches; dynamic-trait types are rejected at595.

The same file:2308–2328 lowers storage markers and Borrowck statements to unit. Its residual Drop branch also returns unit and carries an implementation comment about drops. This is a narrow observation of that branch. Charon's normal pass sequence can desugar drops into calls before Eurydice sees them; the observation must not be expanded into a claim that all destructors in the full pipeline are erased. A preservation argument must identify the imported representation and pass configuration, then account for either explicit Drop or its normalized calls.

Mapping references to pointer types explains representation but does not prove Rust access authority, lifetime, provenance, drop order, or compatibility with C aliasing rules. A C proof can establish a property of the emitted C operations and its C memory model. The Rust-to-C seam still has to justify that the required Rust observations and failures have that meaning.

### A current RustCompCert statement resolves direction separately from its paper

**Basis: source.** At the separately pinned SJTU artifact, driver/Compiler.v:1309–1315 states successful transf_rustlight_program yields backward_simulation with Rustlightown semantics as L1 and Asm semantics as L2, and the source closes the proof with Qed. common/Smallstep.v:1597–1603 matches every target L2 step with source L1 Plus/Star transitions under a related safe L1 state. Its external-call clause 1572–1596 relates queries and replies through calling conventions and continuation relations.

This uses the ordinary target-to-source backward matching direction. It is separate evidence from the short paper's conflicting inclusion prose. It is also a formal Rustlight endpoint rather than a proof that an arbitrary surface Rust file, parser, runtime, or foreign environment meets those semantics.

The proposed partial-to-total safety theorem at Compiler.v:1337–1417 is commented out in this pin; its internal Admitted is not an active axiom. BorrowCheckSound.v:101–135 does contain active admitted type/variance lemmas. No full dependency audit or fresh Rocq checking determined whether particular exported claims depend on them. The selected artifact therefore must not be promoted to a blanket completed borrow-checking or end-to-end safety verdict.

### Derived Anneal comparison and adoption gates

For hax, the first decision is which actual route is being evaluated. Its current Lean route inherits the Charon/Aeneas semantic seams; changing a frontend label does not create independent evidence. The F*/Rocq route offers a different AST and library encoding, whose imports, mutation lowering, failure handling, and emitted definitions need their own correspondence argument.

For a C route, separate source admission from target verification. A usable certificate should bind original Rust/configuration, imported body, each relevant transformation, emitted C, its verified function contract, and the compiled artifact. It must preserve the chosen failure relation before proving a no-failure specification. A target safely computing the expected value for a narrower input domain does not establish safety for every permitted Rust caller.

Maintenance follows backend choice: rustc export changes, phase ordering, accepted feature gates, library/model registry, layout and drop lowering, printer/extraction code, C parsing, ABI, and compiler configurations. A real route comparison should use the same unsafe operation and caller contract, then ask which concrete obligations each route proves, assumes, rejects, or leaves unexamined.

## Boundaries

No hax, Eurydice, RustCompCert, rustc, F*, Rocq, C compiler, or target executable was built or run. Selected source statements and implementation branches are direct inspection, not fresh proof replay or an exhaustive feature matrix. No claim is made that hax emits semantic certificates for every pass, or that Eurydice's informal guarantee is formally verified. The residual Drop observation is conditional on the intermediate input that reaches that branch.

The RustCompCert paper's model labeling of division-by-zero as UB is not adopted as normative Rust: ordinary Rust integer division by zero panics. This report's direction result is tied to the current formal artifact and its safe-source premises.

## Evidence

- hax paths/blobs: README.md, 9f0f7b0fbb25d88a83cdbb342650e4ed80d82a44; cli/driver/README.md, 199b5db628e92cbe0e11b1be6dcc1d1324b9f125; cli/cargo-hax/src/aeneas.rs, d84c6cfe2c247f2dec822085ec4cf189d0b6068c; rust-engine/src/backends/fstar.rs, 6d3d751e55cf4753a7efd6217b2fbcf6752760de; engine/backends/fstar/fstar_backend.ml, cba0a45ecb3c3a700a8c6ba0aa61d9dbdacc7bbb; engine/lib/phases/phase_reject.ml, 4e314e915e3f8486bc7856d140c27e8ca8a373ba.
- Eurydice paths/blobs: README.md, ffcf11efcaa9db0263570bd367f2caf3aa113a37; lib/AstOfLlbc.ml, a56fa4fdb2b38730bad7a418a5fafc9416e883b1.
- SJTU paths/blobs: driver/Compiler.v, 7e793bc9dced27222ae7091769f255289745ad6b; common/Smallstep.v, 027630ae27eaeb805bd1d4e86b2ef70a5bb8d77e; rustfrontend/BorrowCheckSound.v, 98f8a23c003079f68f7b57f5a44638d005ca4ed0.
- Public source and primary documentation acquired 2026-10-14. No upstream source mirrors, compiled artifacts, or measurement results were created. Exact pins are recorded in metadata.

## Revalidation

Fetch exact source paths and compare blob identities. Trace the concrete backend dispatch and selected passes before interpreting support. For Eurydice, preserve the actual pre-normalization and normalized drop representation and test failure cases separately from normal termination. For RustCompCert, audit transitive assumptions and replay the selected theorem before making a checked implementation claim. A downstream C verification theorem requires its own Rust/C simulation and foreign-call contracts.


*Authored by an AI agent acting on joshlf's behalf.*
