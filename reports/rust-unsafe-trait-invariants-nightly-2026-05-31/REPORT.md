# Rust unsafe-trait invariants at nightly-2026-05-31

## Summary

At the Rust toolchain selected by current Anneal, an `unsafe trait` is an **implementation-side proof obligation**. The trait declaration defines extra safety conditions that implementations must uphold; an `unsafe impl` is the programmer's assertion that those obligations have been discharged. The compiler checks that this assertion is syntactically present for an unsafe trait and rejects `unsafe impl` for an ordinary safe trait, but it does not prove the documented invariant itself.

This boundary is intentionally different from an `unsafe fn`. An unsafe trait does not make use of a correctly implemented trait unsafe. The pinned Rust Reference says it is safe to use a correctly implemented unsafe trait. Associated functions keep their own safety classification: a safe method on an unsafe trait remains callable from safe code, while an `unsafe fn` remains caller-unsafe whether its containing trait is safe or unsafe.

That design lets unsafe code rely on semantic properties that cannot be encoded in ordinary trait signatures. `Send` and `Sync` are the canonical stable examples. Both are `unsafe auto trait`s at the pinned compiler revision, so a manual implementation promises thread-safety properties that unsafe code may rely on, while the compiler can also synthesize implementations using its structural auto-trait rules. `TrustedLen` is an even clearer library example: its safety contract requires an accurate iterator length, and downstream consumers are permitted to rely on that contract when using unsafe code.

For verification, an unsafe-trait bound therefore carries more meaning than method availability. A proof system must represent the **semantic contract attached to the trait implementation**, or conservatively treat that contract as an assumption. Merely translating the trait's associated methods and dictionary/vtable shape loses the obligation that makes the implementation safe to trust. The neighboring Charon preservation report already establishes that pinned Charon does not structurally preserve the source `unsafe trait`/`unsafe impl` marker; this report owns the Rust-side meaning of that missing marker rather than redoing downstream preservation analysis.

## Applicability

Current Anneal selects Rust nightly `2026-05-31`. The compiler source used here is `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the same exact compiler identity used by the current reference corpus for pinned Rust language/compiler behavior.

The language-rule source is `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`. At that revision:

- `src/unsafe-keyword.md`, blob `7658c1f5c5425d03e2183e89b55260e5e9fd889b`, defines unsafe traits as extra safety conditions on implementations and `unsafe impl` as the assertion that those obligations are discharged;
- `src/items/traits.md`, blob `fe1a985f5390b0b7edf15db28cd717ce44c3945b`, states that implementing an unsafe trait may be unsafe and that using a correctly implemented unsafe trait is safe.

The compiler-side enforcement is pinned to `compiler/rustc_hir_analysis/src/coherence/unsafety.rs`, blob `8114106a2a4117a1e8e1d706afff753ff834f263`.

The standard-library examples are pinned to the same compiler revision. `library/core/src/marker.rs`, blob `53141aabacc453e3781bbe9593618e26c06ca732`, defines `Send` and `Sync` as unsafe auto traits. `library/core/src/iter/traits/marker.rs`, blob `542d283fe95abab901534fd21e38bddaa6a28823`, defines `TrustedLen` and documents its safety contract.

This report concerns the language and standard-library contract at that pin. It does not attempt to prove that any particular third-party unsafe-trait implementation is sound.

## Findings

### 1. `unsafe trait` creates an obligation for implementors, not callers

The pinned Rust Reference describes `unsafe` as either creating a safety obligation or asserting that an existing obligation has been met. `unsafe trait` belongs to the first category: the trait declaration defines extra safety conditions that implementations must uphold. `unsafe impl` belongs to the second: the implementation states that the programmer has discharged those conditions.

The trait chapter makes the caller-side consequence explicit: it is safe to use a **correctly implemented** unsafe trait. This is the key semantic distinction from `unsafe fn`. The safety boundary sits at implementation, so safe downstream code is allowed to rely on the existence of a sound implementation without surrounding ordinary method calls with `unsafe`.

A verifier should therefore model an unsafe-trait implementation as evidence for a semantic predicate, not as permission to execute unsafe syntax at each call site.

Basis: pinned Rust Reference **normative documentation**.

### 2. `unsafe impl` is a proof assertion, not a compiler proof

The pinned compiler's coherence unsafety checker compares the trait definition's `Safety` with the implementation header's `Safety`. If an unsafe trait has an ordinary `impl`, rustc emits E0200 and explains that the trait “enforces invariants that the compiler can't check.” It instructs the programmer to review the trait documentation before adding `unsafe`.

The reverse is also checked: an `unsafe impl` of an ordinary safe trait is rejected with E0199 and a suggestion to remove `unsafe`.

The compiler therefore enforces **where the proof assertion must appear**. It does not inspect arbitrary semantic documentation and prove that the implementation satisfies it. Adding the `unsafe` keyword satisfies the compiler's syntactic gate, not the trait's semantic contract.

This distinction is essential for automation. Treating “rustc accepted the unsafe impl” as evidence that the contract is true would convert a programmer assertion into a theorem the compiler never established.

Basis: pinned rustc **source**.

### 3. Trait safety and method safety are independent axes

An unsafe trait can contain safe associated functions, unsafe associated functions, or no functions at all. The trait's `unsafe` qualifier governs the soundness obligation on implementations. An `unsafe fn` governs the obligation on each caller.

The Reference's split makes this compositional. A safe method of a correctly implemented unsafe trait is safe to call because the implementation-side invariant is already assumed to hold. If a method has additional preconditions that callers must discharge, the method itself must be `unsafe fn` regardless of whether its trait is unsafe.

For verification, these obligations should not be collapsed. A trait implementation proof may establish a global representation, concurrency, or iterator invariant. A particular unsafe method may still impose a separate per-call precondition. Conversely, a safe method may rely internally on the trait invariant without exposing a caller-side unsafe obligation.

Basis: pinned Rust Reference **normative documentation** + **derived** separation of the two explicit obligation forms.

### 4. A broken unsafe-trait implementation can make safe clients unsound

The purpose of an unsafe trait is that unsafe implementation code elsewhere cannot in general defend itself against a lying implementation. The Rustonomicon uses `Send` and `Sync` as the canonical examples: other unsafe code may assume these traits are implemented correctly, and an incorrect implementation can lead to undefined behavior.

This failure mode explains why an unsafe-trait contract belongs in the proof state even when the immediate client contains only safe syntax. Once a type is accepted as implementing the trait, safe generic code can compose it with abstractions whose unsafe internals rely on the contract.

For Anneal, a theorem about a safe generic function with a bound such as `T: SomeUnsafeTrait` is therefore conditional on the semantic meaning of that bound. Modeling only method resolution is insufficient if the function or its dependencies rely on the trait's safety invariant.

Basis: Rust Reference **normative rule** + Rustonomicon **non-normative rationale**.

### 5. `Send` and `Sync` show that an unsafe trait may be a pure semantic marker

At `rust-lang/rust@14210df...`, `Send` is declared `pub unsafe auto trait Send {}` and `Sync` is declared `pub unsafe auto trait Sync {}`. Neither needs associated methods for its safety contract to matter. Their meaning is a semantic property of the implementing type: transfer across threads for `Send`, sharing through references for `Sync`.

This is a useful counterexample to any representation that infers a trait's verification meaning solely from associated-item bodies or signatures. The entire contract can live in the trait's safety documentation and language/library semantics.

The core source also has explicit negative implementations for raw pointers and a hand-written `unsafe impl<T: Sync> Send for &T`, illustrating that the structural auto-trait mechanism is not just “all fields recurse blindly.” Language/library rules can add positive and negative edges that participate in the invariant.

Basis: pinned core **source**.

### 6. Unsafe auto traits use compiler reasoning to discharge some implementations

`Send` and `Sync` are both unsafe **auto traits**. Their documentation says the compiler implements them automatically when appropriate. In those compiler-synthesized cases, there is no user-written `unsafe impl` to audit. Instead, correctness of the language's auto-trait derivation rules is what justifies treating the synthesized implementation as satisfying the unsafe contract.

This creates two distinct implementation provenance classes:

- **compiler-derived implementation:** trust or verify the auto-trait solver/rules that establish the contract from the type's structure and explicit positive/negative rules;
- **user-written implementation:** trust or verify the programmer's `unsafe impl` argument.

The distinction matters for proof attribution. A verifier should not report a compiler-derived `Send` fact as though a source author manually asserted it, and should not treat a manual `unsafe impl Send` as though it had been structurally derived by rustc.

The neighboring unsafe-fields report provides a concrete example of rustc suppressing automatic candidates for unsafe auto traits when a type contains unsafe fields, showing that auto-trait derivation can depend on additional compiler-maintained safety metadata.

Basis: pinned core **source** + neighboring pinned compiler report.

### 7. `TrustedLen` shows the contract flowing into unsafe consumers

The pinned core library defines `TrustedLen` as an unsafe trait for iterators whose `size_hint` has an exactness contract. Its documentation says the iterator must produce exactly the reported number of elements or diverge before reaching the end, with a specific saturated case for lengths above `usize::MAX`.

The safety section states that the trait must be implemented only when this contract is upheld. This is not an aesthetic marker. It exists so consumers can use the trusted length to justify unsafe implementation techniques that would be unsound for an arbitrary `Iterator`.

`TrustedStep` in the same file makes the dependency even more explicit: consumers are free to rely on its invariants in unsafe code.

For verification, the reusable pattern is that an unsafe-trait predicate can be a **logical premise consumed later by unsafe code**. The implementation site and the unsafe consumer may be in different crates and separated by generic abstraction. A local proof system that checks only syntactic unsafe blocks can therefore miss the actual provenance of a safety argument.

Basis: pinned core iterator **source/documentation**.

### 8. Generic bounds carry a semantic witness, not just an interface constraint

Ordinary trait bounds determine which associated items and implementations are available. For an unsafe trait, the same bound additionally implies that the selected implementation claims the trait's safety contract.

The compiler does not attach a runtime proof object for this contract. Monomorphization, vtables, and trait selection choose an implementation according to Rust's normal trait machinery. Soundness depends on the invariant having been established at the implementation boundary.

Thus a verification IR should ideally distinguish at least:

- the trait identity;
- whether the trait is unsafe;
- the selected implementation or implementation provenance where knowable;
- the semantic safety predicate attached to that trait;
- whether the implementation is compiler-derived, built-in, or manually asserted.

Without those fields, a translated generic bound can preserve dispatch while erasing the reason unsafe consumers are permitted to trust the implementation.

Basis: pinned Reference trait/unsafe rules + pinned core examples + **derived** verification consequence.

### 9. Trait objects do not create a new unsafe-call boundary

The pinned Reference says using a correctly implemented unsafe trait is safe and separately defines when a trait is dyn compatible. Nothing in the unsafe-trait rule makes dynamic dispatch itself an unsafe operation.

A `dyn UnsafeTrait` value therefore relies on the same implementation contract as a statically dispatched bound. The vtable selects methods for some implementing type; it does not dynamically revalidate the unsafe invariant.

For a verifier, changing static dispatch into an existential/dictionary/vtable representation must preserve the invariant witness. The proof obligation is tied to the implementation behind the object, not to whether dispatch is static or dynamic.

Basis: pinned Reference **normative documentation** + **derived** consequence.

### 10. Supertraits compose obligations through ordinary trait bounds

A trait can require supertraits. Anywhere the subtrait is used as a generic bound or trait object, its supertrait requirements are also available. If a supertrait is unsafe, the existence of the required supertrait implementation carries that supertrait's safety contract.

This does not mean every subtrait must itself be declared unsafe. A safe trait can require an unsafe supertrait because implementing the safe subtrait does not create the unsafe-supertrait implementation; rustc separately requires an already-valid implementation of the supertrait bound. The source of trust remains the unsafe supertrait's implementation.

The accounting rule is therefore dependency-oriented rather than keyword-oriented: a proof for `T: Child` may depend transitively on unsafe-trait contracts reachable through supertrait bounds even when `Child` itself is a safe trait.

Basis: pinned Reference supertrait and unsafe-trait rules + **derived** obligation composition.

### 11. The useful verification boundary is contract provenance

Unsafe traits expose a broader pattern in Rust's safety model. The language provides a syntactic place where a semantic claim enters the trusted abstraction boundary, while downstream safe code is allowed to rely on that claim.

For each unsafe-trait fact used in an Anneal proof, a durable representation should answer:

1. **What is the contract?** The semantic property documented for the trait.
2. **Who asserted or derived it?** A user `unsafe impl`, a standard-library impl, or compiler auto-trait reasoning.
3. **What evidence supports it?** A manual proof, structural rule, modeled theorem, or accepted assumption.
4. **Who consumes it?** Unsafe code, verified models, or higher-level safe abstractions whose soundness depends on the trait.
5. **Does the translation preserve it?** Trait-method translation alone is not enough if the marker and contract disappear.

That is the level at which an unsafe-trait invariant should enter a source-to-model adequacy argument.

## Boundaries

No fresh rustc, Cargo, Miri, or runtime execution was performed. Compiler behavior is derived from exact pinned source and language/reference documentation.

The Rust Reference specifies where unsafe-trait obligations are created and discharged, but it cannot mechanically encode arbitrary prose contracts written by trait authors. This report does not claim that rustdoc safety sections are machine-readable specifications.

The Rustonomicon is used only for rationale about why unsafe code may depend on `Send`/`Sync`; it is not treated as normative language specification.

This report does not inventory every standard-library unsafe trait. `Send`, `Sync`, and `TrustedLen` are examples selected to expose distinct patterns: compiler-derived marker contracts and library-defined contracts consumed by unsafe code.

The report does not specify trait-solver completeness, specialization, negative-impl stabilization, or coherence beyond what is needed to identify implementation provenance.

The report does not redo Charon/Aeneas preservation analysis. The current corpus separately records that pinned Charon does not structurally preserve source unsafe-trait/unsafe-impl markers. That downstream omission should be reconciled with the Rust-side contract described here when Anneal's proof model is designed.

No particular unsafe-trait implementation in zerocopy is proved sound here.

## Evidence

**Rust Reference — exact revision `ad35aca481751a06afeb23820a672b0f3b11a476`**

- `src/unsafe-keyword.md`, blob `7658c1f5c5425d03e2183e89b55260e5e9fd889b`: `unsafe trait` defines extra safety conditions on implementations; `unsafe impl` asserts they have been discharged; unsafe functions and blocks form separate caller-side obligations.
- `src/items/traits.md`, blob `fe1a985f5390b0b7edf15db28cd717ce44c3945b`: implementing an unsafe trait may be unsafe; using a correctly implemented unsafe trait is safe; supertrait and dyn-compatibility rules are ordinary trait mechanisms around that boundary.
- `src/unsafety.md`: implementing an unsafe trait is one of the language-level operations excluded from the safe subset.

**rustc — `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`**

- `compiler/rustc_hir_analysis/src/coherence/unsafety.rs`, blob `8114106a2a4117a1e8e1d706afff753ff834f263`: E0199 rejects `unsafe impl` for a safe trait; E0200 rejects a safe impl for an unsafe trait and explicitly describes the invariant as something the compiler cannot check.

**core library — same compiler revision**

- `library/core/src/marker.rs`, blob `53141aabacc453e3781bbe9593618e26c06ca732`: `Send` and `Sync` are `unsafe auto trait`s; raw pointers have explicit negative impls; `&T` has an explicit unsafe `Send` impl conditional on `T: Sync`; the same file also contains internal unsafe auto traits whose safety is part of compiler behavior.
- `library/core/src/iter/traits/marker.rs`, blob `542d283fe95abab901534fd21e38bddaa6a28823`: `TrustedLen` documents a precise iterator-length safety contract and is declared `unsafe trait`; `TrustedStep` explicitly states that consumers may rely on its invariants in unsafe code.

**Non-normative rationale**

- Rustonomicon, “How Safe and Unsafe Interact”: explains the intended division between unsafe-trait implementors and unsafe consumers, using `Send`, `Sync`, and allocator-style contracts as examples.
- Rustonomicon, “Send and Sync”: states that incorrect implementations can cause undefined behavior because unsafe code may rely on them.

## Revalidation

For another Rust toolchain pin, first resolve the exact compiler and Reference revisions. Re-read the Reference's unsafe-trait and unsafe-impl sections, then diff `rustc_hir_analysis/src/coherence/unsafety.rs` for changes to the implementation-safety gate.

For stable examples, re-read the exact `Send`/`Sync` declarations and any explicit positive/negative implementations that affect structural derivation. For library-contract examples, re-read `TrustedLen` or whichever unsafe trait the analyzed code actually relies on; the trait documentation is part of the semantic proof obligation.

For an Anneal integration change, separately inspect Charon/Aeneas preservation of trait safety metadata and implementation identity. A passing source-level rustc check only shows that the `unsafe impl` assertion was present; it does not establish the contract. If the translator erases the unsafe marker, preserve an explicit side table or model-level predicate tying each selected unsafe impl to its safety contract and provenance.

On a capable execution surface, a compile-only fixture can confirm the syntax gate: safe impl of unsafe trait should fail with E0200; unsafe impl of safe trait should fail with E0199; safe and unsafe methods inside an unsafe trait should retain their independent call-site requirements. Such a fixture validates observable compiler gating, not the semantic truth of any implementation contract.