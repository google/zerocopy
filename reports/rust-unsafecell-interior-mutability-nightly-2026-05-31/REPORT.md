# `UnsafeCell` and interior mutability at nightly-2026-05-31

## Summary

`UnsafeCell<T>` is Rust's core language/library primitive for interior mutability. At the selected nightly, its special power is narrow: bytes inside an `UnsafeCell` are exempt from the ordinary rule that data reached through a live shared reference must remain immutable. That exemption does **not** relax the uniqueness of `&mut`, does not make data races legal, and does not turn the pointer returned by `UnsafeCell::get` into an automatically valid reference.

For verification, treat `UnsafeCell` as a change to the shared-reference mutation invariant, not as a general aliasing escape hatch. A `&UnsafeCell<T>` may coexist with mutation of the wrapped storage, but any `&T` or `&mut T` later created for the contents reintroduces the ordinary reference obligations for its lifetime. `UnsafeCell` itself is `!Sync`; cross-thread mutation still needs synchronization.

`UnsafeCell<T>` has the same in-memory representation as `T`, but this fact does not lift compositionally through arbitrary outer types. In particular, `UnsafeCell` disables niche optimizations, so an `Outer<T>` and `Outer<UnsafeCell<T>>` can differ in size or representation even when `T` and `UnsafeCell<T>` do not.

## Applicability

This report covers `core::cell::UnsafeCell` in `rust-lang/rust` revision `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the Rust revision used for the Anneal-era `nightly-2026-05-31` toolchain, interpreted together with Rust Reference revision `ad35aca481751a06afeb23820a672b0f3b11a476`.

The evidence is source and upstream documentation at those immutable revisions. No fresh rustc, Miri, code-generation, or multithreaded execution was run. The Rust Reference explicitly says the exact aliasing rules are not fully determined. This report therefore preserves the common contract stated by the Reference and the pinned `UnsafeCell` documentation rather than claiming a complete formal memory model.

The report is about the primitive itself. `Cell`, `RefCell`, mutexes, atomics, and other abstractions can build safe APIs around interior mutability, but their additional dynamic or synchronization invariants are separate subjects.

## Findings

### `UnsafeCell` removes shared-reference immutability only for its covered storage

The pinned core documentation defines `UnsafeCell<T>` as the core primitive for interior mutability. Ordinary `&T` permits compiler reasoning that the referenced data is immutable. `&UnsafeCell<T>` is the exception: the wrapped storage may be mutated even while shared references to the cell exist.

The pinned Rust Reference states the same rule in its undefined-behavior summary. A live `&T` ordinarily protects the pointed-to memory from mutation, except for data inside an `UnsafeCell<U>`. The Reference separately exempts bytes that are part of an `UnsafeCell` from the rule that bytes owned by immutable bindings or immutable statics are immutable.

This exception is spatial, not a capability to mutate arbitrary reachable memory. It applies to bytes inside the cell. Code must still justify writes to other bytes under the ordinary aliasing and immutability rules.

Basis: documentation + normative Reference.

### The exception does not weaken `&mut` uniqueness

The pinned `UnsafeCell` documentation explicitly says that only the immutability guarantee for shared references changes. The uniqueness guarantee for mutable references does not. There is no legal way to have aliasing live `&mut` references merely because an `UnsafeCell` is involved.

This distinction is central for verification. Multiple `&UnsafeCell<T>` values can coexist while the cell's contents change, provided the abstraction enforces all remaining rules. But if code creates an `&mut T` for the contents and releases it to safe code, no conflicting access to those contents may occur until that exclusive reference expires. Likewise, multiple live `&mut UnsafeCell<T>` aliases remain forbidden.

The safe `get_mut(&mut self) -> &mut T` API illustrates the rule. It can be safe precisely because the exclusive borrow of the cell establishes the ordinary exclusive access needed for its contents.

Basis: documentation + normative Reference.

### `get` yields a raw pointer; reference formation is a separate unsafe transition

`UnsafeCell::get(&self)` returns `*mut T`. Its documentation does not promise that the pointer can be turned into any reference at any time. Instead, it points back to the type-level aliasing contract and requires callers to uphold the reference rules when creating references.

At the selected revision, the core raw-pointer documentation describes reference formation as requiring alignment, non-nullness, dereferenceability, pointee validity, and the applicable aliasing rule. For a shared reference, mutation is forbidden for its live interval except inside nested `UnsafeCell` storage. For a mutable reference, conflicting accesses are forbidden for the live interval.

The unstable `UnsafeCell::as_ref_unchecked` and `as_mut_unchecked` APIs make this boundary explicit. `as_ref_unchecked` is UB if a mutable reference to the wrapped value is live or if the value is mutated while the returned shared reference is live. `as_mut_unchecked` is UB if any other reference to the wrapped value is live or if the value is mutated through another route while the returned mutable reference is live.

A verifier should therefore model `get` as exposing a raw access path and model the later raw-pointer-to-reference operation as the point where ordinary reference obligations must be proved. The mere presence of `UnsafeCell` discharges only the shared-reference immutability restriction for the cell-covered bytes.

Basis: documentation + source.

### `raw_get` exists to avoid creating an invalid temporary reference

`UnsafeCell::raw_get` takes `*const UnsafeCell<T>` rather than `&UnsafeCell<T>` and returns `*mut T`. The pinned docs use gradual initialization as the motivating example: given `MaybeUninit<UnsafeCell<i32>>`, calling `get` would first require constructing `&UnsafeCell<i32>` to uninitialized storage, while `raw_get` can reach the field without creating that temporary reference.

This is a useful verifier boundary. `get` carries the preconditions required to create and use its shared receiver reference. `raw_get` deliberately avoids that reference-formation event; it does not, by itself, make a later dereference or reference construction safe.

Basis: documentation + source.

### Shared-cell mutation does not make data races legal

`UnsafeCell` does not provide synchronization. Its pinned documentation says data races remain undefined behavior and directs conflicting cross-thread access to atomic or otherwise synchronized APIs. The type has an explicit negative `Sync` implementation.

The `Sync` documentation reinforces the architecture: non-thread-safe interior-mutability types such as `Cell` and `RefCell` are not `Sync`, while thread-safe interior mutability requires atomics or synchronization such as mutexes and reader-writer locks. Those abstractions can use `UnsafeCell` internally and add the synchronization proof that `UnsafeCell` itself lacks.

Thus, for concurrent verification, `UnsafeCell` changes the aliasing/immutability story but contributes no happens-before relation, atomicity, race freedom, or lock discipline.

Basis: documentation + source.

### `UnsafeCell` participates in the compiler's `Freeze` distinction

The selected core source defines the internal `Freeze` lang-item trait as indicating that a type does not contain an `UnsafeCell` internally, ignoring indirections, and provides `impl !Freeze for UnsafeCell<T>`. The comments connect this property to whether a static may live in read-only versus writable storage.

`Freeze` is unstable compiler machinery rather than a stable user-facing semantic API. Still, it is direct source evidence that the compiler tracks the presence of interior-mutability storage as a property relevant to immutability assumptions.

Basis: source.

### Deallocation through a shared reference has a narrow `UnsafeCell` exception

The pinned type documentation records a subtle lifetime exception. Ordinarily, data reached by `&T` or `&mut T` may not be deallocated while the reference remains live. Given an `&T`, however, a portion inside `UnsafeCell` may be deallocated after the last use of the reference. Because allocation cannot generally be deallocated in arbitrary pieces, the documentation concludes that the whole allocation reachable through the shared reference can be deallocated this way only if every byte, including padding, is inside `UnsafeCell`.

This does not make dangling `&UnsafeCell<T>` references valid. Whenever a `&UnsafeCell<T>` is constructed or dereferenced, it must still point to live memory, and the compiler may insert spurious reads where it can prove the memory has not been deallocated.

For proofs, this is not a general "interior mutability permits early free" rule. It is a precisely bounded exception whose premises include byte coverage and last use.

Basis: documentation.

### `UnsafeCell<T>` and `T` have the same representation, but outer niche behavior can differ

The selected implementation is `#[repr(transparent)]`, and its documentation guarantees that `UnsafeCell<T>` has the same in-memory representation as `T`. The docs use this fact to justify direct conversions such as `&mut T -> &mut UnsafeCell<T>`.

The guarantee is not compositional through arbitrary enclosing types. `UnsafeCell` disables niche optimizations so that the interior-mutability property does not accidentally spread from `T` into an outer type. The pinned documentation gives the concrete example that `Option<NonNull<u8>>` is typically one pointer wide on 64-bit platforms, while `Option<UnsafeCell<NonNull<u8>>>` takes two pointer widths. Therefore, transmuting an arbitrary `Outer<T>` to `Outer<UnsafeCell<T>>` is not justified merely from the transparent representation of the inner pair.

This distinction matters for layout proofs: direct `T`/`UnsafeCell<T>` representation equivalence and outer-container representation equivalence are different propositions.

Basis: documentation + source.

### Same-layout casts do not bypass the designated shared-cell access path

The pinned documentation states that the valid ways to obtain a mutable raw pointer to the contents of a **shared** `UnsafeCell<T>` are `get` and `raw_get`. It gives a compile-fail/UB example that casts `&UnsafeCell<T>` through raw pointer types to `*mut T` and then creates `&mut T`; identical layout does not make that pattern valid. The documented replacement uses `ptr.get()` and then performs the reference formation under the required exclusivity proof.

Conversely, converting an exclusive `&mut T` to `&UnsafeCell<T>` is documented as allowed, relying on the representation guarantee. This asymmetry is about reference/access semantics, not bytes alone.

Basis: documentation + source.

### `UnsafeCell` does not itself discharge the wrapped type's validity obligations

The special contract documented for `UnsafeCell` concerns mutation through shared access. The APIs that expose the contents either return a raw pointer or, when returning a reference, attach ordinary reference safety conditions. The Rust Reference separately requires produced references to point to valid values of their pointee type.

Accordingly, a proof should not infer that arbitrary bit patterns become valid `T` merely because the storage sits inside `UnsafeCell<T>`. Temporary raw-memory manipulation, initialization, and typed reads remain governed by their own operation-specific contracts. This report does not try to settle every possible intermediate raw-memory state.

Basis: normative Reference + documentation; derived boundary.

## Boundaries

The exact Rust aliasing model remains unsettled at these revisions. The report preserves explicit common rules from the pinned Reference and core documentation and does not claim a complete Stacked Borrows, Tree Borrows, LLVM, or formal-language account.

No fresh execution was performed. Existing checked-in Miri tests at the selected rustc revision exercise interior-mutability aliasing cases, including two-phase borrows and deallocation, but this report uses them only as corroborating implementation test coverage, not as the language definition.

The report does not establish thread-safe behavior for `Cell`, `RefCell`, mutexes, atomics, or custom wrappers. `UnsafeCell` supplies the low-level mutation exception; each safe abstraction must separately establish its own runtime and concurrency invariants.

The report does not claim that all bytes stored inside `UnsafeCell<T>` may temporarily violate `T`'s validity rules. Raw initialization and representation manipulation require their own operation-specific analysis.

No behavior is projected to an adjacent Rust revision. Revalidate before using the findings for a different compiler/library pair.

## Evidence

Primary Rust core source at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:

- `library/core/src/cell.rs`, blob `1c79cf6bfcb36c2a814155bce8f8ea32afb2c191`, especially the `UnsafeCell` type documentation and implementation around lines 2141-2565. This is the primary source for the shared-reference exception, retained `&mut` uniqueness, race boundary, deallocation rule, representation/niche behavior, `get`, `get_mut`, `raw_get`, and the unchecked reference accessors.
- `library/core/src/marker.rs`, blob `53141aabacc453e3781bbe9593618e26c06ca732`, especially the `Sync` documentation around lines 516-566 and `Freeze` around lines 890-909.
- `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`, especially lines 70-88 describing raw-pointer conversion to references and the `UnsafeCell` exception for shared references.
- `compiler/rustc_lint/src/reference_casting.rs`, blob `6052a16a7f117a302f6f76143b1d6020f406d2f6`, which describes `UnsafeCell` as the designated route for aliasable data considered mutable and detects invalid reference casting outside interior mutability.
- `src/tools/miri/tests/pass/both_borrows/interior_mutability.rs`, blob `b7dbd3ff172938860782bcf804031d66d42dafc2`, checked-in implementation tests for aliasing/interior-mutability behavior. These tests were inspected but not executed.

Primary Rust Reference source at `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`:

- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`, especially the aliasing rule at lines 36-48 and immutable-byte rule at lines 50-57. The same document records that the UB list and exact aliasing model are not exhaustive/final.

Evidence was materially revalidated on 2026-09-27.

## Revalidation

For a newer Rust revision, first diff the `UnsafeCell` type documentation and implementation in `library/core/src/cell.rs`. Recheck the exact text governing shared-reference mutation, `&mut` uniqueness, deallocation, `get`/`raw_get`, `Sync`, and the representation/niche caveat. Then diff the Reference's aliasing and immutable-byte rules.

If those regions are unchanged, most semantic findings can be revalidated without a broad compiler crawl. If they changed, inspect the corresponding `marker.rs` `Sync`/`Freeze` definitions and raw-pointer reference-formation documentation before carrying any conclusion forward.

If an engineering decision depends on a subtle aliasing case beyond these documented common rules, add a separately scoped exact-revision Miri/rustc probe and preserve the program and output. Treat such execution as implementation evidence, not as a replacement for the language contract.
