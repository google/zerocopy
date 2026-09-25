# Aeneas lifetime erasure and resource-semantics boundary at nightly-2026.06.03

## Summary

At `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the ordinary functional translation selected by Anneal deliberately avoids a heap/resource model by relying on Rust's safe ownership discipline before translation. References become values, mutable-borrow effects become backward functions, `Box<T>` becomes `T`, and lifetime parameters disappear from the pure output language after they have guided region grouping and borrow translation.

That design preserves useful value-flow information, but it does not preserve the operational resources that unsafe-Rust reasoning commonly needs. The pure model does not represent allocation identity, ordinary reference identity, a Rust pointer-provenance relation, or a heap whose aliasing and initialization state can be reasoned about directly. The source itself describes the functional translation as covering a subset of safe Rust and says unsafe and concurrent code require ongoing separation-logic work.

Raw pointers make the boundary explicit. A raw-pointer type survives into the pure AST as a dedicated marker carrying const/mut information and pointee type, but `Pure.ml` says raw pointers “don't make sense in the pure world” and are retained only so signatures can be represented while ensuring the relevant functions are not actually used. The symbolic interpreter rejects raw-pointer dereference with the diagnostic “Aeneas does not yet support dereferencing raw pointers,” which is also preserved in a checked-in known-failure artifact.

The existing lifetime report in this corpus establishes when region information influences translation and when it is erased. The key resource-semantics consequence is that lifetime erasure is not merely removal of names: the functional backend relies on safe-Rust borrow discipline to justify replacing memory resources with pure values and backward value flow. A Rust-level proof about unsafe aliasing, pointer provenance, initialization, allocation identity, or concurrency therefore needs additional semantics; those properties cannot be recovered from the final pure value types alone.

No fresh Aeneas, Charon, Lean, or Rust execution was performed. The report uses exact pinned source, upstream documentation, and checked-in failure/generated artifacts.

## Applicability

Primary subject:

- repository: `AeneasVerif/aeneas`
- revision: `ac9f1bc5262a5e4ff1e24ca78617121382202727`
- release: `nightly-2026.06.03`
- relationship: this is the Aeneas release selected by current Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

This report concerns Aeneas's ordinary functional translation pipeline and pure target AST. It does not characterize unpublished work or prove the status of every separation-logic component in the repository. The upstream README at this exact revision distinguishes the current functional safe-Rust subset from ongoing work intended to support unsafe and concurrent Rust.

The companion report `rust-lifetimes-charon-aeneas-nightly-2026-05-31` establishes the detailed region path through rustc, Charon, and Aeneas. The companion report `aeneas-rust-to-lean-translation-nightly-2026-06-03` establishes the concrete type/function/backward-function translation. This report focuses on what those transformations do and do not retain as resource semantics.

“Provenance” is potentially ambiguous here. Aeneas's pure AST contains an `mplace` metadata type described as provenance information used to generate variable names. That source-location/value-origin metadata is not a Rust pointer-provenance model. This report uses “pointer provenance” only for the latter operational concept.

## Findings

### The functional translation intentionally eliminates ordinary memory reasoning

The pinned overview describes the central approach directly: Aeneas leverages Rust's ownership discipline to translate Rust programs to pure functional programs “by leveraging Rust's ownership discipline to eliminate memory reasoning entirely.” It states that mutable-reference uniqueness lets the translator replace references with plain values and backward continuations so “no heap model” is needed.

This is not merely a printing choice in the Lean backend. `SymbolicToPureTypes.ml` removes the reference constructor from forward types, and `Pure.ml` has no ordinary reference type in the pure target language.

The abstraction is therefore strongest for code whose memory behavior is already constrained by the safe Rust type/borrow system.

Basis: upstream **documentation** + **source**.

### Regions affect symbolic borrow translation before disappearing from pure types

The pinned source does not erase region information at the beginning of translation. It computes region hierarchies and uses region groups to decide the shape of generated backward functions. That behavior is established in detail by the existing lifetime report.

When the translation constructs pure types, however, generic region parameters are omitted and `TRef (_, rty, _)` translates recursively to `rty`. The pure generic-parameter structure retains types, const generics, and trait information, but not lifetime parameters.

This means the final type language records an effect of lifetime structure only indirectly through the generated functional interface. A later consumer cannot reconstruct the original lifetime relation simply by inspecting the pure type constructors.

Basis: **source** + existing corpus synthesis.

### Mutable-borrow ownership becomes value flow, not a persistent ownership token

For a mutable borrow, the forward translation works with the borrowed value. If the borrow must outlive a call boundary, Aeneas can generate backward functions whose inputs and outputs reconstruct the original owners when the borrow ends.

That mechanism preserves a specific semantic relationship: which values must flow back to which owners according to the symbolic borrow abstractions. It does not preserve an explicit ownership capability, loan object, allocation identifier, or reference identity in the final pure program.

The distinction is important for Anneal. The backward function can support functional reasoning about mutation through safe references. It is not a general memory-resource witness that can justify arbitrary raw-pointer operations.

Basis: **source** + upstream **documentation** + **derived** distinction.

### Shared references also become values

A shared Rust reference translates to the referent's pure type. In backward-type traversal, Aeneas stops below a shared reference rather than generating mutable update paths through it, because the shared borrow freezes what lies below it.

Thus the safe-Rust freeze rule influences translation, but the final value itself does not carry a reference identity or a runtime alias set.

For source-level claims that depend only on safe shared-borrow behavior, this abstraction may be exactly the intended one. For claims about unsafe aliases to the same storage, the pure value alone is insufficient evidence.

Basis: **source**.

### `Box<T>` erases heap indirection and allocation identity

The pure translation treats `Box<T>` as the translated `T`. `Pure.ml` explicitly documents Box removal as an identity simplification, and `SymbolicToPureTypes.ml` eliminates the Box wrapper in both forward and backward-type processing.

Consequently, the ordinary functional model does not expose the allocation identity or heap location associated with a Rust `Box`. A proof over the resulting `T` cannot distinguish two executions solely by which heap allocation held the source value.

This does not make Box translation incorrect for safe functional behavior. It marks the abstraction boundary: allocation identity has been intentionally quotiented away.

Basis: **source** + **derived** consequence.

### Raw-pointer types survive only as a marked boundary

Unlike ordinary references and boxes, a raw-pointer type is not erased to its pointee. The pure AST has a `TRawPtr` builtin carrying const/mut information.

The comment defining that builtin is unusually explicit: raw pointers “don't make sense in the pure world,” the translator does not yet know how to translate them, and the dedicated type exists so functions with raw pointers in their signatures can be represented while ensuring those functions are not actually used in translation.

Type representability is therefore not operational support.

Basis: **source**.

### Raw-pointer dereference is rejected, not approximated

`InterpPaths.ml` checks raw-pointer dereference before symbolic-value expansion and raises an error stating that Aeneas does not yet support dereferencing raw pointers.

The repository preserves a concrete Rust fixture that reads and writes through raw pointers and a corresponding `.lean.out` failure artifact with that diagnostic. The failure points to `InterpPaths.ml`.

For this exact pin, an ordinary functional-translation proof cannot silently assign safe-reference semantics to a raw-pointer dereference: the interpreter rejects the operation. This is a useful fail-closed boundary, but it also means the functional backend cannot directly verify unsafe code whose semantics require such dereferences.

Basis: **source** + preserved upstream failure artifact.

### Aeneas's `mplace` “provenance” is naming metadata, not pointer provenance

`Pure.ml` defines an `mplace` structure and describes it as metadata retrieved from symbolic execution that “gives provenance information about the values.” The next sentence states its purpose: generating names for introduced variables.

That field should not be confused with Rust pointer provenance. It records source/symbolic-place origin useful to extraction and naming; it is not a relation governing which allocation a pointer may access, which operations expose or preserve provenance, or when two pointer values may alias.

A future source-correspondence report may rely on `mplace` as origin metadata. A memory-soundness proof must not treat it as the missing pointer-provenance semantics.

Basis: **source** + **derived** terminology distinction.

### The ordinary pure model has no general heap state to carry initialization or aliasing facts

Because references and boxes are functionalized away and raw-pointer dereference is unsupported, the pure target representation does not expose a general heap object whose cells carry byte-level initialization, allocation identity, or arbitrary alias relations.

Safe-Rust mutation is represented by functional updates and backward continuations instead. This is enough to explain how value changes are propagated through accepted borrow structures, but it cannot directly state properties such as:

- two raw pointers carry provenance for the same allocation;
- a byte range is allocated but partly uninitialized;
- two unsafe aliases overlap while a reference exists;
- a deallocation invalidates a previously derived raw pointer.

Those are examples of stronger operational-resource facts absent from this functional representation, not claims that Aeneas has no possible future model for them.

Basis: **derived** from **source** and upstream **documentation**.

### The upstream support statement is safe-Rust scoped

The pinned README labels the implemented target as a “subset of safe Rust.” It separately lists unsafe code and concurrency as limitations expected to be lifted by ongoing separation-logic work.

That wording sets the applicability boundary more clearly than individual accepted syntax does. A raw-pointer type appearing in a signature or an internal Box-manipulation path does not expand the advertised functional semantics into a complete unsafe-Rust model.

For Anneal, the relevant conclusion is not “Aeneas is unsound for unsafe Rust.” The supported conclusion is narrower: the selected functional backend does not itself provide the resource semantics needed to justify general unsafe-Rust memory operations.

Basis: upstream **documentation** + **source**.

### Internal symbolic execution has richer borrow state than the final pure output

The Aeneas interpreter tracks loans, mutable/shared/reserved borrows, path-access restrictions, borrow endings, and symbolic values while translating. `InterpPaths.ml`, for example, distinguishes read, write, and move access and controls whether traversal may enter loans or borrows.

That internal machinery is evidence that the translator does not naively erase memory structure before reasoning about safe borrows. It uses a richer symbolic state to justify the functional program it synthesizes.

But those internal loan IDs and borrow records are translation machinery. They are not emitted as a general resource model in the final pure AST. Once translation succeeds, later Lean proofs ordinarily see the functionalized values rather than the interpreter's borrow graph.

Basis: **source** + **derived** pipeline distinction.

### The existing lifetime result and this resource boundary are complementary

The existing corpus already establishes that Aeneas uses signature regions before erasing them and that lifetime erasure can hide distinctions a Rust-level proof may care about. This report adds the corresponding memory-resource statement: after safe-borrow functionalization, the proof-facing model retains effects as value flow but not the original reference/heap/resource identities.

Together these facts constrain any Rust-level verification claim that crosses this boundary. A claim can rely on erased information only when there is a justified theorem or abstraction argument showing that the retained functional semantics are sufficient for that claim.

Basis: **derived** from the two pinned reports and current Anneal principles.

## Boundaries

- No fresh execution was performed.
- The report concerns the ordinary functional translation selected by Anneal. It does not inventory or evaluate all ongoing separation-logic implementation work.
- It does not claim that the functional translation is unsound for its advertised safe-Rust subset.
- It does not claim that raw pointers are absent from all target syntax. Raw-pointer *types* are deliberately representable; raw-pointer dereference is the unsupported operation established here.
- It does not prove that every possible unsafe operation fails explicitly. The broader unsupported/failure matrix remains a separate inventory.
- It does not treat internal loan/borrow IDs as useless; they are essential translation state. The narrower claim is that they are not a general proof-facing resource model in the final pure AST.
- It does not equate Aeneas `mplace` origin metadata with Rust pointer provenance.
- It does not establish semantics for allocation, deallocation, uninitialized memory, concurrency, atomics, I/O, or nondeterminism beyond noting that the ordinary functional abstraction does not expose the operational resources needed for general reasoning about them.
- Formal results published by the Aeneas project are not used here as a blanket theorem about all unsafe Rust or this exact implementation revision.
- Current Anneal design is not inferred from this report. The report establishes a boundary that a future design must account for.

## Evidence

**Source — primary Aeneas revision.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`.

- `src/symbolic/SymbolicToPureTypes.ml`, blob `d35b6d67a65af220fdb56614ab1b51edc029b06f`: region omission, reference erasure, Box erasure, raw-pointer target type, backward-type traversal.
- `src/pure/Pure.ml`, blob `acde8579d6861a08efae086c72f3156283110342`: pure target types; raw-pointer marker rationale; Box/reference differences; `mplace` origin metadata.
- `src/interp/InterpPaths.ml`, blob `ec23375a5ca0680500daea0248d2372c9901156e`: borrow/loan path access, read/write/move distinctions, raw-pointer-dereference rejection.
- `src/interp/InterpBorrows.ml`, blob `f3dcde1455af1402a1099ae1d9651c4ba8aea46e`, and `src/interp/InterpBorrowsCore.ml`, blob `9232a193ed20fbeb989624187663f2ef464a3406`: internal borrow/loan symbolic machinery.

**Documentation — same revision.**

- `README.md`, blob `f331650bd4291d27ba6cee736ce51cf31da9cac1`: functional subset of safe Rust; unsafe/concurrency limitation; ongoing separation-logic direction.
- `documentation/aeneas-overview.md`, blob `439076012c1ba93c7ec1bf25aca42e0f1ec14756`: ownership-driven elimination of memory reasoning, value/backward-continuation model, no-heap-model explanation.

**Preserved failure artifact — same revision.**

- `tests/src/raw_pointers.rs`, blob `c77fa4735d4e6616fe4450747e4f3a4d108ca624`.
- `tests/src/raw_pointers.lean.out`, blob `74eb81fcad39eaa685249c66d129e6b01ba5a883`: preserved failure for raw-pointer dereference.

**Related current corpus evidence.**

- `reports/rust-lifetimes-charon-aeneas-nightly-2026-05-31/`: detailed lifetime/region propagation and erasure.
- `reports/aeneas-rust-to-lean-translation-nightly-2026-06-03/`: exact value/reference/backward-function translation.

No evidence gathered by this report is fresh **execution**.

## Revalidation

For a later Aeneas pin, first check the support statement in the root README and then inspect four narrow source regions:

1. `SymbolicToPureTypes.ml`: whether ordinary references and regions are still erased and whether Box remains identity-like;
2. `Pure.ml`: whether the target type language now has an explicit resource/heap/reference model and what `TRawPtr` means;
3. `InterpPaths.ml`: whether raw-pointer dereference is still rejected or has acquired semantics;
4. the ordinary extraction path: whether proofs now receive resource assertions, heap state, pointer-provenance objects, or another separation-logic interface.

On a capable execution surface, regenerate three exact-pin fixtures and preserve LLBC, generated Lean, diagnostics, and hashes:

- a safe mutable-borrow function that returns a borrow and exercises a backward continuation;
- a `Box<T>` allocation/manipulation whose safe observable result is independent of allocation identity;
- a pair of raw-pointer functions, one merely passing a pointer through a signature and one dereferencing it.

The key discriminator is whether the proof-facing output now contains explicit resources that can distinguish allocation/pointer identities and justify the dereference, rather than only values/backward functions plus a marker raw-pointer type. If a newer separation-logic backend is selected, treat that as a new subject and report its semantics separately instead of extending this functional-backend report by assumption.
