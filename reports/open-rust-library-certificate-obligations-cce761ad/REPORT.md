# Open Rust library closure and source-bound certificate obligations

## Summary

A function proof for values admitted by a mathematical decoder does not establish safety for every native safe caller. An open-library result needs entry coverage, invariant preservation for every reachable access path, exact trait/callback selection and a source-to-model safety relation that preserves forbidden finite prefixes. RustBelt and RefinedRust provide concrete semantic interfaces for this reasoning; neither examined interface silently supplies correspondence to arbitrary compiled Rust. The cce761ad zerocopy pointer case exposes why visibility, unsafe trait laws, callback error recovery and layout dictionaries belong in the certificate boundary.

## Applicability

The case subject is google/zerocopy `cce761ad53785973ec2f4a6b13715b770b340c87`. Local inspected files were verified byte-identical to Git objects. The bounded access-path inventory covers `pointer/ptr.rs`, `pointer/inner.rs`, their reexports, invariant definitions, projection traits and selected error-law implementations. It is not a full expanded/cfg-specific inventory of the crate or downstream clients.

The semantic comparison uses exact archive bytes: LambdaRust popl18 SHA-256 `b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`; RefinedRust's 2026-07-28 Zenodo record 21636474 archive SHA-256 `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`. The recorded members were inspected directly. They are different formal languages and dependency combinations. No combined proof or actual rustc correspondence theorem was run.

A safe native control ran under rustc 1.99.0, commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, aarch64-apple-darwin, LLVM 23.1.1, edition 2021, debug defaults. It concerns ordinary trait/generic/callback/drop behavior, not a zerocopy counterexample.

## Findings

### F1. Native entry domain and semantic abstraction

Basis: **source**, **normative**, **execution**, **derived**.

RustBelt's type interface separates `ty_own(thread,values)` and persistent `ty_shr(lifetime,thread,location)`. `ty_share` consumes an appropriate full borrow and live lifetime fraction under a mask containing the lifetime namespace, and returns shared ownership and that fraction; `ty_shr_mono` permits lifetime shortening. The `typed_body` interface consumes interpreted type/lifetime/continuation contexts. Its `type_soundness` theorem assumes a semantically typed empty-argument, unit-returning main for every type-ghost-state instance; executions in LambdaRust then remain nonracing and each thread is a value or reducible. Thus ordinary client typing must establish the semantic judgment before the adequacy theorem applies.

RefinedRust's `typed_function` in `functions.v:136–164` universally quantifies lifetimes, semantic types, specification parameters, call duration and stack frame. It requires actual argument-layout matching, arbitrary argument locations, initialized owned resources, the precondition and side conditions, and returns owned result resources/postconditions with restored resources. Universal semantic parameters do not mean every arbitrary machine layout is admitted: the explicit layout premise remains.

For native safe clients, an entry lemma must show that every permitted concrete input has a related semantic state, or that ordinary Rust/library preconditions legitimately exclude it. The current `RustModel.decode : Raw -> Option Model` admits only values with a witness. A hidden decoder restriction cannot justify an unsafe action on an otherwise permitted safe input unless a public precondition or invariant-establishing path enforces it. Public safe mutation, downstream modules and unannotated paths must preserve that domain.

### F2. Bounded pointer access-path inventory

The package retains 71 lexical function declarations from Ptr/PtrInner, with source lines and syntactic visibility. This is a reproducible inventory aid, not a semantic reachability result: trait methods are public by trait visibility even when their declaration lacks `pub`, and macro expansion/cfg selection may add or remove items.

| Access class | Examined source paths | Required invariant/resource relation |
|---|---|---|
| Ordinary reference entry | Ptr/PtrInner `from_ref`, `from_mut` | Derive lifetime, allocation, alignment and semantic validity from a real incoming reference |
| Raw/external entry | PtrInner `new`; Ptr `from_inner`, assumed alignment/validity and unchecked casts | Caller establishes the documented unsafe premises; inaccessible fields prevent arbitrary safe reconstruction |
| Duplication/reborrow | Ptr shared-only Copy/Clone, `as_inner`, `reborrow`, shared reborrow | Track whether aliasing is shared or exclusive; raw extraction does not transfer safe dereference permission |
| Typed observation/transfer | `as_ref`, `as_mut`, read, byte/slice conversion, get_mut | Establish the exact Read/Immutable/validity/alignment facts for each observed representation |
| Projection/cast | transmute, recall/unify/forget invariants, cast/project/tag | Preserve address/provenance/range and mutation-compatible validity; bind actual selected trait implementation |
| DST/slice iteration | metadata change, split/slice, trailing slice, cast with leftovers, iter/len | Preserve metadata, bounds, disjointness or shared compatibility and restoration on failure |
| Callback/error recovery | `try_with`, unchecked variant, `TryWithError::map` | Callback/frame contract plus ownership of the single restored pointer; no escaping exclusive alias |
| Layout/projection dictionaries | KnownLayout, HasField/HasTag/ProjectField, Project/Cast/CastExact | Exact associated outputs, const IDs and per-implementation semantic laws |

Ptr's private `ptr` and phantom fields and crate-private unsafe constructor support an abstraction boundary. They do not finish it: pointer APIs are reexported through a public module. `lib.rs:356–358` hides that module only in documentation under a cfg attribute. The [Rust visibility rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/visibility-and-privacy.md) define access through ancestors/reexports; documentation hiding is not language privacy. The bounded certificate must include these accessible paths and state its cfg/module domain.

### F3. Unsafe trait laws and callback restoration

The [Rust unsafe-trait rule](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/unsafe-keyword.md) places extra safety obligations on implementations. An unsafe implementation asserts their discharge; a verifier must establish them or make that implementation an explicit assumption.

In `pointer/mod.rs:49–83`, `Project` requires the result's byte region to be a subset with unchanged provenance, `Cast` preserves address, and `CastExact` preserves the full region. In lib.rs, KnownLayout and projection traits supply associated metadata, type and invariant information. A selected implementation is evidence-bearing; matching a trait name alone is insufficient. The “only derive” associated method on public unsafe traits is a documented implementation restriction, not a sealed language barrier against all manual unsafe implementations.

Ptr's safe `try_with` requires shared aliasing. The crate-private unsafe variant additionally requires that an error from an exclusive callback leaves no argument copy outside the error. It saves the old inner pointer, calls the callback, maps the error, drops the old owning Ptr and reconstructs it. The unsafe `TryWithError` law requires exactly one inner value and no other non-ZST fields, and transfer of that inner to the mapping closure. Selected ValidityError and CastError implementations in `error.rs:658–670,797–812` delegate through source-mapping methods and justify that single-inner shape. These facts are exactly the restoration premise; “FnOnce” alone does not express the exclusive nonescape law.

The current Validity documentation defines its permitted set using bit validity alone, whereas Safe's description includes library safety invariants and its implementation comment again mentions bit validity alone. This source-contract tension remains unresolved. A certificate must not silently choose one interpretation, and this report does not infer a source unsafety verdict.

### F4. Exact dictionaries, const generics and indirect calls

Current admission/trait binding source at cce761ad checks original/final generic applications, native dictionary identity, implementation owner and law selection. Ten selected controls were executed in the companion diagnostics package; exact array usize const parameters are retained and altered/dropped const identity is rejected. This is evidence for the selected checks, not for all generic Rust.

In RefinedRust `generics.v:65`, `spec_with` maps lifetime vectors and semantic type lists to a specification. `function_ptr:173–177` owns an actual function-table entry, matching argument layouts and a later `typed_function` obligation. `type_call_fnptr:240–284` checks the current-thread/mask, actual argument ownership/subtyping, syntactic-type matching, precondition, side conditions and live lifetime context before exposing returned resources. This is a concrete indirect-call certificate shape, not a direct-call assumption generalized by name.

The [Rust trait-object rule](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/types/trait-object.md) selects a method implementation through an object's vtable. A corresponding certificate needs the concrete vtable entries or a universally quantified law for every permitted entry, plus object ownership/lifetime and ABI/layout. A generic certificate similarly quantifies retained type/lifetime/const parameters and law dictionaries, or declares an explicit finite set of monomorphic instances. It must record associated types/constants, parent traits, blanket-implementation substitution and exact method body identity. GATs, specialization and coinductive trait selection were not fully researched here; they cannot be inferred covered from these basic dictionary checks.

### F5. Safe native controls and cleanup domain

The retained native control permits a safe trait implementation returning zero alongside another returning one; both generic and dynamic calls select it correctly. It admits array lengths zero and three, public-field mutation to zero, callback mutation to two, ordinary Drop exactly once, and safe forget without another Drop. Output is `generic=1,0; dynamic=0; const_lengths=0,3; callback=2; drops=1; forget=1`, exit zero.

The control discriminates several tempting domain mistakes: a safe trait bound alone does not imply a stronger value law, a positive-length invariant needs a real premise, public fields allow native writes, callbacks can alter their permitted state, and safety cannot depend on every value eventually being dropped. The [destructor specification](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/destructors.md) also identifies partial initialization and drop scopes. This control does not exercise panic unwinding, FFI, packed layout, specialization or zerocopy itself.

Current admission intentionally rejects general drops, callbacks, foreign ABIs and raw storage in the documented fragment. Rejecting their extraction is a correct bounded-domain result; extending it requires new effect/correspondence obligations.

### F6. Feasible certificate shapes and reuse conditions

Basis: **derived design**, informed by the exact interfaces above. These records are proposals, not implemented Anneal certificates.

| Record | Minimum content | Check at composition |
|---|---|---|
| Source domain | Repository/tree, compiler/dependencies, target, feature/cfg/panic settings, roots and expanded access paths | Every accessible native entry belongs to the declared domain |
| Type abstraction | Concrete ownership/shared predicate, decoder identity, lifetime/layout parameters, constructor and mutation laws | Establish entry coverage and preserve abstraction across all safe paths |
| Dictionary | Compiler-selected impl/body/associated items, original substitutions, parent laws, const values, checked law proof | Match the actual call dictionary and instantiated source owner |
| Function | Operational/model relation, pre/normal/unwind/abort effects, footprint/frame and safety-prefix preservation | Callee contract follows from native implementation under stated premises |
| Indirect call | Function table/vtable or quantified callback set, ABI, ownership and effect contract | Every selected target satisfies the same required relation |
| Recursive component | Dependency SCC, guarded/inductive proof rule, invariant resources and all component obligations | No law or safety conclusion is admitted by circular reuse |
| Link composition | Exact object/source bindings, imported symbol contracts and preservation theorem for relevant transformations | Reuse only when dictionary, target, layout and source meanings remain equal |

Separate checking is feasible when each record exposes assumptions and their checked discharge, so unrelated functions can reuse a stable semantic abstraction or dictionary law. Hashes detect identity changes but do not prove preservation under linking, specialization or optimization. FFI requires a separate ABI/resource bridge and foreign implementation evidence; the inspected fragment excludes it. Recursive functions/invariants require a simultaneous sound rule, not separately assumed mutually dependent correctness claims.

## Boundaries

Answered with constraints: entry-domain necessity, bounded Ptr access classes, callback and unsafe-trait laws, semantic polymorphism/function-pointer premises, and feasible certificate composition shapes. Not established: safety of the current pipeline for arbitrary safe clients, closure of the whole zerocopy crate, all downstream unsafe implementations, or compiled Rust correspondence.

Remaining research: complete cfg/macro-expanded access inventory; GAT/associated-item/coinductive/specialization selection; a complete vtable/closure source bridge; recursive unsafe-type/law compatibility; actual ABI and linking preservation. Future engineering: build and check the proposed records and prove/measure the source-to-model relation. These gaps are kept distinct in coverage.json.

## Evidence

Observed 2026-10-14. `source-evidence.json` contains full Git revisions/blobs/SHA-256 identities, semantic archive/member hashes and narrow symbol endpoints. `ptr-lexical-inventory.json` records its exact lexical scope. `client_domain_probe.rs` and `client-probe-results.json` retain executable control and toolchain/output identity; the binary is not necessary for revalidation. No unsafe-invalid native program was run. The [LambdaRust archive](https://gitlab.mpi-sws.org/iris/lambda-rust/-/archive/popl18/lambda-rust-popl18.tar.gz) and [RefinedRust archive](https://zenodo.org/records/21636474) are bound by the hashes above; moving download labels do not replace those hashes.

Recorded command paths are normalized to package-relative paths or `<pinned-checkout>`; raw observation hashes and the normalization scope are retained in `observation-path-normalization.json`. Program outputs, statuses and source identities retain their observed meaning.

## Revalidation

Enumerate the configured expanded exports and selected implementations, then compare each entry against a semantic ownership/validity law. Rerun the safe native control on the declared target, and replay exact dictionary/const rejection controls separately from kernel proof checks. Diff the RefinedRust function-table/layout premises and RustBelt type/adequacy endpoints. For any extension, first show entry coverage and forbidden-prefix preservation; a decoder success theorem alone cannot supply either.

*Authored by an AI agent acting on joshlf's behalf.*
