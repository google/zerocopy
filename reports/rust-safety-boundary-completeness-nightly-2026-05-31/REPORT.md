# Rust unsafe syntax and abstraction invariants at nightly-2026-05-31

## Summary

At Rust nightly-2026-05-31, `unsafe` syntax marks a fixed set of language operations whose use requires additional proof obligations. It is not a general marker for every state transition that can matter to an unsafe abstraction's invariant.

Safe Rust can perform operations that unsafe code must account for. Ordinary assignment can replace a value and run the old value's destructor. `Cell::set` mutates through a shared reference. `UnsafeCell::get` safely produces a mutable raw pointer. `MaybeUninit::uninit` and `MaybeUninit::write` safely move storage between uninitialized and initialized states. `mem::forget` safely prevents a destructor from running, and its own documentation explicitly says unsafe code may not assume callers will run destructors.

These operations are not loopholes in Rust's safety model. A sound abstraction must arrange its visibility, types, ownership, state machine, and unsafe implementation so that every operation exposed to safe callers preserves the conditions needed before later unsafe code relies on them. If a safe transition can establish a state that makes later internal unsafe code invoke undefined behavior, the abstraction is unsound even though that transition contains no source `unsafe` token.

For Anneal, scanning source unsafe operations is therefore necessary for locating explicit language-level proof obligations, but it is not a complete way to find the transitions relevant to an unsafe abstraction proof. The proof boundary must follow invariant producers, safe and unsafe transitions, and consumers.

No fresh rustc, Miri, Charon, or executable experiment was performed.

## Applicability

This report applies to:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler/library source behind the Anneal-era nightly-2026-05-31 toolchain.
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference pinned by that Rust source revision.

An **unsafe operation** here means an operation the Reference excludes from Rust's safe subset. An **abstraction invariant** means a condition an implementation relies on to make its unsafe operations valid. The report is concerned with memory-safety-relevant invariants; ordinary application invariants can matter to developer-defined verification goals but are not automatically Rust soundness obligations.

## Findings

### Rust's unsafe-operation list is an authorization boundary, not a complete invariant language

The pinned Reference lists the language features that require unsafe context: raw-pointer dereference, mutable or unsafe external static access, union-field reads, unsafe calls, certain target-feature calls, unsafe trait implementation, unsafe extern declarations, and unsafe attributes.

That list answers which source operations need extra authorization. It does not claim that every operation capable of changing state relevant to an unsafe implementation must itself be syntactically unsafe.

Basis: **normative**.

### Ordinary assignment can change invariant-bearing state in safe code

The Reference defines assignment as moving or copying a value into a mutable place after dropping the previous value when required. Assignment is an ordinary expression, not one of the language's unsafe operations.

An abstraction may therefore not use "all writes are inside unsafe blocks" as a substitute for proving that its state remains valid. If safe code can reach the relevant place through a permitted API or visibility boundary, ordinary assignment can be part of the invariant transition graph.

This does not mean arbitrary private fields are writable by safe callers. Rust's visibility and borrowing rules are part of how abstractions prevent invalid transitions.

Basis: **normative** + **derived**.

### Interior mutation can be exposed by a safe API

`Cell<T>` is documented as enabling mutation inside an otherwise immutable structure. Its safe `set(&self, val)` method replaces the contained value.

`UnsafeCell<T>` is the primitive that opts out of the usual immutability guarantee for data reached through `&T`. Its safe `get(&self) -> *mut T` method returns a mutable raw pointer.

The safety boundary is therefore not "mutation requires unsafe syntax." Rust permits safe APIs to expose controlled mutation, while the implementation is responsible for ensuring that later uses satisfy the language's aliasing and validity requirements.

Basis: **source/documentation**.

### Creating a raw pointer can be safe even when using it later requires stronger conditions

The core pointer module exposes safe operations that create raw pointers, including reference-to-pointer conversion and pointers without provenance. The documentation separates pointer construction/manipulation from operations that require the pointer to be valid for an access or convertible to a reference.

`UnsafeCell::get` is a concrete safe pointer-producing API. A downstream proof must therefore track when a pointer is created, what provenance/lifetime facts remain available, and where a later dereference or reference construction consumes those facts. Looking only for the later unsafe syntax loses part of that data flow.

Basis: **source/documentation** + **derived**.

### `MaybeUninit` makes transitional representation states safe to construct

`MaybeUninit::uninit()` safely creates uninitialized storage. `MaybeUninit::write` safely writes a valid `T` into that storage and returns a reference to the initialized value.

By contrast, `assume_init` and related methods are unsafe because the caller must establish that the contents are initialized and satisfy the relevant type requirements before treating the storage as a `T`.

This cleanly separates a safe state transition from the later proof-consuming operation. An abstraction that uses partially initialized storage must reason about the safe operations that establish or modify initialization state, not merely the unsafe assertion that consumes it.

Basis: **source/documentation**.

### Safe code may suppress destruction, so unsafe code cannot make Drop a soundness precondition

`mem::forget` is a safe function. Its documentation explains why: Rust's safety guarantees do not promise that destructors always run. It then states the direct consequence for unsafe code: unsafe code must allow for forgetting and cannot return a value while assuming the caller will necessarily run its destructor.

This is a strong example of a lifecycle condition that cannot be protected merely by placing teardown code in `Drop`. If memory safety depends on cleanup always running, the abstraction must obtain that guarantee some other way.

Basis: **source/documentation**.

### Safe callers can invoke APIs whose implementations contain unsafe code

A safe function or method may internally use unsafe operations after establishing their preconditions. The caller does not need an unsafe block merely because the implementation does.

This is the point of a safe abstraction: the implementation discharges the extra proof obligation and exposes a safe contract. For verification, however, the absence of unsafe syntax at a call site does not mean the call is irrelevant to unsafe-code reasoning. A safe method can be a producer or transition for state later consumed by unsafe code, or can itself encapsulate an unsafe consumer.

Basis: **derived** from Rust's unsafe-abstraction model and the concrete library examples above.

### Visibility and types, not unsafe syntax alone, enforce abstraction boundaries

Private fields, module visibility, ownership, borrowing, typestate, and safe API design can prevent callers from performing invalid state transitions. Conversely, a public safe setter or mutation path deliberately enlarges the set of states the implementation must tolerate.

The soundness question is therefore not "can safe callers execute an unsafe operation?" It is "can safe callers, while obeying every safe API contract, establish state for which the implementation's unsafe operations no longer satisfy their preconditions?"

Basis: **derived**.

### An unsafe-code proof must follow producers, transitions, and consumers

For an invariant used by unsafe code, a complete proof must identify:

1. where the invariant is first established;
2. every safe and unsafe transition that can change the relevant state;
3. every point where an unsafe operation relies on the invariant;
4. visibility, ownership, synchronization, and type-system facts that exclude other transitions.

Source `unsafe` tokens are useful landmarks for explicit language-level consumers, but they are not a sufficient slice of the program for this proof.

This is the key consequence for Anneal: a design that verifies only syntax inside unsafe blocks can miss safe state transitions that determine whether the unsafe operation is valid.

Basis: **derived**.

## Boundaries

- No fresh compiler, Miri, or runtime experiment was performed.
- This report does not claim that safe Rust can cause undefined behavior in a sound library. If a safe client can trigger UB while respecting the safe API contract, that is evidence the abstraction is unsound.
- It does not claim every safe mutation affects a soundness invariant. Relevance depends on the abstraction being proved.
- It does not replace the language's explicit unsafe-operation inventory; that inventory remains necessary for identifying language-level proof obligations.
- It does not exhaustively catalogue every safe standard-library operation that can matter to unsafe code.
- It does not cover unsafe-field semantics, unsafe auto-trait solving, FFI, concurrency, panic/unwind, or detailed pointer semantics; those are separate report subjects.
- It does not prescribe Anneal's annotation language or verification boundary. It establishes a constraint any sound abstraction-oriented proof strategy must accommodate.

## Evidence

**Normative — Rust Reference.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`:

- `src/unsafety.md`, blob `7353bcc6004d74b9e8698c71c093b35eebe05a70`: language-level unsafe-operation inventory.
- `src/expressions/operator-expr.md`, blob `6c5e4ffbf1532597c3ffe9a800ca80e0fb3cec8a`: assignment evaluation, drop of the old value, and copy/move into the assigned place.

**Source/documentation — core library** at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:

- `library/core/src/mem/mod.rs`, blob `62c612e7ba2a65bb1645faaa669abd2a1d35a6c2`: safe `mem::forget` and its explicit requirement that unsafe code tolerate destructor suppression.
- `library/core/src/cell.rs`, blob `1c79cf6bfcb36c2a814155bce8f8ea32afb2c191`: safe interior mutation through `Cell`, `UnsafeCell` semantics, and safe `UnsafeCell::get`.
- `library/core/src/mem/maybe_uninit.rs`, blob `7e2c6b9b3bcb2d66af376243d95c541e5bd4024d`: safe `uninit`/`write` and unsafe `assume_init*` boundary.
- `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`: pointer validity/provenance documentation and safe raw-pointer construction APIs.

No evidence above is fresh **execution**.

## Revalidation

For a later Rust pin, first diff the Reference unsafe-operation inventory and assignment rules. Then recheck the signatures and safety documentation of `mem::forget`, `Cell::set`, `UnsafeCell::get`, `MaybeUninit::{uninit, write, assume_init}`, and the raw-pointer construction APIs.

A minimal future regression fixture can encode an unsafe abstraction whose internal proof depends separately on mutation control, initialization state, pointer use, and guaranteed destruction. Exercise every exposed safe transition and confirm the proof obligations remain attached to the invariant transitions rather than merely to source unsafe blocks. Such a fixture can test a verifier's coverage strategy; it does not make the library examples above empirical rather than source-defined.
