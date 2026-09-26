# Rust validity versus well-defined execution at nightly-2026-05-31

## Summary

At the Rust revision behind the nightly-2026-05-31 toolchain, **type validity is a necessary condition for well-defined execution, not a complete definition of it**. The Rust Reference makes producing an invalid typed value immediate undefined behavior. It separately defines other undefined behaviors that can occur while every produced value remains type-valid: accessing dangling or misaligned memory, violating pointer-aliasing rules, mutating immutable bytes, racing non-atomic accesses, calling through the wrong ABI, misusing inline assembly, or violating runtime assumptions.

Three uses of the word “valid” must therefore remain distinct. A **valid value** satisfies the validity invariant of its Rust type. A raw pointer that is **valid for a particular access** has the permissions and memory properties required for that operation; the core pointer documentation explicitly says there is no useful context-free question “is this pointer valid?”. A value can also be required to satisfy a **library invariant** that is stronger than the compiler’s type-validity invariant. The pinned `MaybeUninit` documentation gives `Vec<T>` as the canonical example: a bit-pattern can satisfy what the compiler currently knows about `Vec<T>` without satisfying the invariants needed by safe `Vec` operations or destruction.

Initialization is one component of validity, not a synonym for it. Rust’s abstract memory distinguishes initialized bytes from uninitialized bytes. Some typed values, including integers and raw pointers, require initialization even though they accept broad bit patterns; other types additionally restrict the allowed representation or referent. Conversely, uninitialized bytes can exist inside `MaybeUninit<T>`, union storage, or padding without thereby producing a value of `T`.

References expose the distinction most sharply. Producing a reference requires alignment, non-nullness, non-dangling storage, and a valid pointee under the Reference’s current rules, while using memory through a pointer is also constrained by provenance, aliasing, access size, mutability, lifetime, and synchronization. The exact provenance and aliasing models are intentionally not fully specified at this revision. A verifier cannot replace those unresolved operational rules with “all values are valid” and thereby establish UB-freedom.

rustc contains a validity checker used by interpretation and const evaluation, but its own source says that const validation goes further to approximate “const safety.” That implementation is evidence about this compiler revision; it is not a complete normative runtime semantics.

No fresh compiler, Miri, CTFE, Charon, or Aeneas execution was performed. This report synthesizes the exact pinned Reference, core-library documentation, and rustc source. The separate corpus report on Rust UB and operational models covers the authority boundary around Miri, Stacked Borrows, Tree Borrows, and the absence of a complete formal Rust operational semantics.

## Applicability

This report applies to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler and core-library source used by the Rust nightly associated with the pinned Charon toolchain;
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference revision bundled by that Rust source tree.

The report uses “validity” in three deliberately separate senses:

1. **Type/value validity**: whether a produced value satisfies the invariant attached to its Rust type.
2. **Pointer validity for an access**: whether a pointer may perform one particular read, write, offset, or conversion, with a specified size and operation.
3. **Library invariant**: a semantic requirement imposed by an abstraction such as `Vec<T>`, beyond the compiler-known validity of its representation.

It also distinguishes runtime validity from CTFE restrictions. The Reference imposes additional provenance-related validity conditions in const contexts, and rustc’s const interpreter performs extra checks. Those restrictions do not automatically become runtime validity rules.

The exact aliasing and provenance rules are incomplete at these revisions. Findings below preserve that uncertainty instead of treating rustc or Miri implementation choices as a complete language definition.

## Findings

### Producing an invalid typed value is immediate undefined behavior

The Reference states that rustc assumes all values produced during execution are valid. “Producing” includes assigning a value to a place, reading one from a place, passing it to a function or primitive operation, and returning it.

This is stronger than a rule about later use. If an operation produces an invalid reference or invalid `bool`, the program has already invoked undefined behavior even if no later operation observes the value.

The rule is nevertheless about values of Rust types. It does not say that arbitrary bytes in storage always constitute a produced value of the type that might later occupy that storage.

Basis: **normative**.

### Initialization is an abstract memory property and only one component of validity

The Reference’s memory model treats memory as abstract bytes, each of which may be initialized with a `u8` value and optional provenance or may be uninitialized. It warns that even this abstract-byte model is not guaranteed to be exhaustive.

For the validity rules, integers, floating-point values, raw pointers, and `str` bytes must be initialized. Types such as `bool`, `char`, function pointers, references, enums, and valid-range types impose additional restrictions.

Thus “initialized” does not imply “valid”. An initialized byte pattern can be invalid for `bool`, `char`, an enum discriminant, a non-null type, a function pointer, or a reference. Conversely, uninitialized bytes are permitted in storage positions that are not being produced as a restricted typed value, notably union storage and padding.

Basis: **normative**.

### `MaybeUninit<T>` changes which typed value is being represented

The pinned `MaybeUninit` documentation explains the intended boundary directly. A `MaybeUninit<T>` may contain bytes that would be invalid if they were currently a `T`; creating `MaybeUninit::<&i32>::uninit()` is therefore allowed. Calling `assume_init` before the bytes satisfy `T`’s requirements instead produces the invalid `T` and invokes UB.

The documentation also notes that padding bytes do not need to be initialized before `assume_init`. This is consistent with the Reference’s distinction between data represented by a type and padding gaps.

The durable fact is not that “uninitialized memory is allowed” or “uninitialized memory is UB.” The relevant question is whether the program has produced a typed value whose validity invariant requires those bytes to be initialized.

Basis: **documentation** + **normative**.

### Aggregate validity is recursive, with explicit unresolved cases

For ordinary structs, tuples, and arrays, all fields or elements must be valid at their respective types. For enums, the discriminant must select a valid variant and that variant’s fields must be valid.

References and `Box<T>` have representation and referent requirements: they must be aligned, non-null, non-dangling, and point to a valid value according to the current Reference text. Wide references and boxes additionally require metadata appropriate for the unsized tail. Slice metadata must not imply an object larger than `isize::MAX`, and trait-object metadata must refer to a compiler-generated vtable for the expected trait.

The Reference explicitly leaves some cases unresolved. Union validity is not fully decided. It also says the rule requiring references and boxes to point to a valid value remains subject to debate. These are boundaries in the language account, not gaps that may be filled by assuming the strictest convenient rule.

Basis: **normative**.

### A raw-pointer value can be type-valid while being unusable for memory access

The invalid-value rules require raw-pointer values to be initialized, but do not require every raw pointer to be non-null, aligned, dereferenceable, or backed by live memory merely for the pointer value to exist.

The core pointer documentation therefore defines safety relative to an operation. It says that asking whether a pointer is simply “valid” is insufficient: validity depends on whether the operation is a read or write and on the number of bytes accessed.

This separates representation from permission. A null, dangling, out-of-bounds, or provenance-less raw pointer can exist as a raw-pointer value. A later non-zero-sized access through it can still be UB.

Basis: **normative** + **documentation**.

### Dereferenceability is necessary but not sufficient for a raw-pointer access

At the pinned core-library revision, a non-zero-sized access requires the pointer’s range to lie within the allocation identified by its provenance. The documentation calls that property *dereferenceability*.

It immediately qualifies the concept: dereferenceability is necessary, but not always sufficient, for a read or write. Additional requirements can include alignment for operations that demand it, aliasing constraints, mutability permissions, and concurrency rules. Different operations deliberately have different requirements: `read_unaligned` and `write_unaligned` are explicit exceptions to ordinary alignment requirements, and zero-sized operations have special cases.

A verifier therefore cannot discharge an arbitrary pointer-access obligation by showing only “address is within allocation.”

Basis: **documentation**.

### Producing a reference requires more than proving a raw pointer is in bounds

The core pointer documentation lists several conditions for converting a raw pointer to a reference:

- proper alignment;
- non-nullness;
- dereferenceability for the pointee;
- a valid pointee of type `T`;
- satisfaction of the applicable aliasing rules.

It deliberately uses the phrase “convertible to a reference” to avoid conflating the reference value’s requirements with the validity of the value it points to.

The Reference reaches the same boundary from the UB side: producing an invalid reference is UB, while aliasing violations and invalid pointer accesses are independently listed UB categories. Reference formation can therefore require both representation/referent validity and operational permissions.

Basis: **documentation** + **normative**.

### Provenance is semantic access authority, not just an address annotation

The pinned `core::ptr` documentation states that a pointer semantically contains an address plus provenance. Provenance determines which memory the pointer has permission to access and can constrain spatial extent, temporal extent, and mutability.

This explains why equal numeric addresses do not imply interchangeable access rights. A use-after-free pointer does not regain authority merely because a later allocation reuses the same address. Similarly, `wrapping_offset` can preserve provenance even while the numerical address temporarily lies outside the original allocation.

The exact structure of provenance is not specified at this revision, and the documentation links that uncertainty to unresolved aliasing rules. The stable conclusion is therefore that provenance matters to whether accesses are permitted; it is not that one particular experimental provenance calculus is normative.

Basis: **documentation** + **normative** relation to pointer-access UB.

### Aliasing is an execution rule independent of type-valid bit patterns

The Reference lists breaking pointer aliasing rules as UB separately from producing invalid values. Its current outline says shared references generally prohibit mutation of reachable memory except through `UnsafeCell`, while mutable references require exclusivity against non-derived accesses while live.

It also says the exact rules and exact liveness duration are not fully determined.

This means a memory state can contain individually well-formed reference values and still participate in an execution that violates aliasing. Validity of each reference’s representation and pointee does not prove that the collection of accesses through those references is legal.

Basis: **normative**.

### Well-defined execution is strictly stronger than maintaining type-valid values

The Reference enumerates UB categories that do not reduce to invalid-value production. Relevant examples at this revision include:

- data races;
- loads or stores through dangling or misaligned places;
- out-of-bounds place projections;
- aliasing violations;
- writes to immutable bytes;
- UB-triggering intrinsics;
- execution of code requiring unavailable target features;
- calls with the wrong ABI or unwinding through a frame that forbids it;
- incorrect inline assembly;
- violations of Rust runtime assumptions.

Consequently, a proof that every produced value satisfies its type-validity invariant is insufficient to conclude that an execution is UB-free. It establishes one necessary class of conditions among several.

Basis: **normative** + **derived** implication.

### Library invariants can be stronger than compiler-known type validity

The pinned `MaybeUninit` documentation warns that many types impose invariants beyond what the compiler currently knows as initialization or validity.

Its example is `Vec<T>`. The documentation says that a `Vec<T>` whose bytes are initialized to `1` can, under the current implementation, satisfy the compiler-known representation requirement that the data pointer be non-null. Creating that representation is therefore not necessarily immediate invalid-value UB. Most safe operations on it, including destruction, will nevertheless cause UB because the representation does not satisfy `Vec`’s semantic invariants.

The documentation marks the exact compiler-known fact as an implementation detail rather than a stable guarantee. The general distinction is durable: a library abstraction may require semantic relationships among otherwise type-valid fields, and safe library code can rely on the unsafe constructor or mutator having established those requirements.

For verification, “valid Rust value” must not silently be upgraded to “valid instance of every library abstraction whose type it inhabits.”

Basis: **documentation** + **derived** consequence.

### CTFE adds validity restrictions that are not general runtime rules

The Reference adds provenance-related validity requirements specifically in const contexts. Values containing integer-like data may not carry provenance, while values containing pointer data must contain either no provenance or correctly ordered fragments of one original pointer.

rustc’s `rustc_const_eval::interpret::validity` source makes the implementation distinction explicit. Its module comment says it checks a value’s validity invariant and, in const contexts, “goes even further” to approximate const safety. `CtfeValidationMode` distinguishes statics, promoted values, and consts, and the visitor contains checks for pointer fragments and metadata that matter during interpretation.

This is strong evidence about the pinned compiler’s CTFE validation path. It is not evidence that every extra CTFE rejection is runtime UB, nor that this one implementation checker is a complete validator for arbitrary runtime Rust executions.

Basis: **normative** + **source**.

### Verification boundaries must account for both values and operations

A source-to-proof pipeline concerned with UB cannot soundly replace the Rust side of the problem with a predicate that says only “all modeled values are valid.”

At minimum, the evidence above distinguishes obligations about:

- whether a typed value may exist;
- whether memory backing a pointer is live and in bounds;
- whether an operation has the required alignment;
- whether provenance authorizes the access;
- whether aliasing and concurrency permit the access;
- whether an abstraction’s library invariants hold;
- whether ABI, unwinding, target, assembly, and runtime constraints are respected.

Some of those rules are precisely stated; some are intentionally unresolved in current Rust semantics. A verifier can model, prove, reject, or explicitly trust those boundaries, but it cannot make them disappear without weakening the Rust-level claim.

This is a derived semantic constraint, not a choice of Anneal proof architecture. Current Anneal design separately decides how any such evidence is represented.

Basis: **derived** from the normative and documentation evidence above.

## Boundaries

- No fresh rustc, CTFE, Miri, Charon, Aeneas, or generated-code execution was performed.
- The Reference says its UB inventory is non-exhaustive and that Rust has no complete formal unsafe-code semantics. This report therefore does not claim to enumerate every condition for well-defined Rust execution.
- Exact aliasing rules are unresolved at the examined revision. The broad reference-uniqueness principles recorded here are not a substitute for a complete aliasing model.
- The exact structure of provenance is unresolved. This report establishes that provenance participates in memory-access legality, not one complete provenance calculus.
- Union validity remains explicitly unsettled.
- The Reference’s requirement that references and boxes point to valid values is itself marked as partly debated.
- The report does not inventory invariants for `Vec`, `String`, collections, synchronization primitives, or other standard-library abstractions. `Vec` is used only as pinned documentation evidence for the general distinction between compiler-known validity and stronger library invariants.
- The rustc interpreter validity checker is implementation evidence for this compiler revision. Its CTFE checks must not be generalized to runtime language semantics without separate normative support.
- Miri, Stacked Borrows, Tree Borrows, and the Unsafe Code Guidelines process are not re-inventoried here. See the separate `rust-ub-and-operational-models-nightly-2026-05-31` report for their authority and experimental status.
- The report does not choose how Anneal should encode validity, provenance, aliasing, library invariants, or operational semantics. It only preserves distinctions that a Rust-level UB-freedom claim cannot conflate.
- Adjacent Rust or Reference revisions are outside the applicability of this report unless revalidated.

## Evidence

**Normative — Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`: invalid-value production; per-type validity; reference/`Box` requirements; union and reference-pointee uncertainty; dangling and misaligned accesses; aliasing; immutable memory; data races; ABI/unwinding; inline assembly; runtime assumptions.
- `src/memory-model.md`, blob `cc3cf02ec0adba12134ad6cb82e51a4b864da784`: initialized bytes, uninitialized bytes, optional provenance, and the explicit incompleteness of the memory model.

**Documentation — pinned core library.** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `library/core/src/mem/maybe_uninit.rs`, blob `7e2c6b9b3bcb2d66af376243d95c541e5bd4024d`: initialization invariant, invalid `assume_init`, permitted uninitialized storage, padding, and the distinction between compiler-known validity and stronger type/library invariants.
- `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`: operation-relative pointer validity, dereferenceability, alignment, pointer-to-reference conversion, allocations, provenance, Strict Provenance, and explicit unresolved pointer/aliasing rules.

**Source — rustc const/interpreter validity checking.** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `compiler/rustc_const_eval/src/interpret/validity.rs`, blob `249a65e22824521af9e4bd433235c667a6fd94a4`: validity visitor, reference/box checks, CTFE validation modes, pointer-fragment errors, metadata validation, and the source-level statement that const validation goes beyond ordinary validity to approximate const safety.

**Related corpus evidence.**

- `rust-ub-and-operational-models-nightly-2026-05-31` establishes the separate authority boundary among the Reference, Miri, experimental aliasing models, and UCG/t-opsem work.
- `rust-safety-boundary-completeness-nightly-2026-05-31` establishes the separate distinction between syntactically unsafe operations and semantic obligations that safe syntax or library abstractions can rely on.

No evidence above is fresh **execution**.

## Revalidation

For a later Rust pin, the cheapest source-level revalidation is to diff the rules that define the distinctions rather than repeat broad compiler archaeology:

1. the Reference’s `behavior-considered-undefined.md`, especially invalid values, dangling/misaligned pointer access, aliasing, immutable memory, and runtime assumptions;
2. the Reference’s `memory-model.md` abstract-byte and provenance text;
3. `core::mem::MaybeUninit`’s initialization-invariant documentation and library-invariant example;
4. `core::ptr`’s Safety, pointer-to-reference, allocation, provenance, and pointer/integer sections;
5. rustc’s `rustc_const_eval/src/interpret/validity.rs`, especially `CtfeValidationMode`, reference/box validation, wide metadata, and pointer-fragment checks.

If any of those areas changes materially, update or add a report for the new precise revision rather than assuming adjacent-version continuity.

On a capable execution surface, a small pinned discriminator can complement the source review:

- construct uninitialized storage with `MaybeUninit<i32>` and separately attempt `assume_init`;
- construct null, dangling, and provenance-less raw pointers without accessing them, then attempt representative non-zero-sized accesses in Miri;
- compare aligned and unaligned operations using `read` versus `read_unaligned`;
- run one const-context pointer/integer provenance case and the analogous runtime code;
- preserve compiler/Miri versions and exact diagnostics.

Such a probe establishes how the selected tools diagnose those fixtures. It does **not** resolve the Reference’s intentionally open aliasing/provenance questions or make Miri’s experimental model normative.
