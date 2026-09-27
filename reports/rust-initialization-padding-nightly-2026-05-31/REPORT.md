# Rust initialization, padding, and typed-copy semantics at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, corresponding to Anneal's `nightly-2026-05-31`, initialization is a property of Rust's abstract memory bytes, while validity is a property of produced typed values. The bundled Rust Reference permits uninitialized bytes in padding even when the enclosing value is otherwise valid. Padding contributes to storage size and layout, but it is not required to hold initialized value bytes merely because a `T` exists there.

A typed move or copy therefore preserves a Rust value without promising to preserve the value's complete byte representation. The pinned `MaybeUninit<T>` documentation states the useful contract directly: a typed copy preserves the contents and provenance of `T`'s **non-padding** bytes, while initialized bytes at padding offsets may lose their values. The documentation applies the same warning to an ordinary generic identity function, so this is not a `MaybeUninit`-only curiosity. Copying a value containing references may additionally perform implicit reborrows, so even preserved semantic values do not imply a byte-for-byte or provenance-identity operation.

This distinction has concrete consequences. A field-by-field initialized struct may be converted to `T` without initializing its padding. `mem::zeroed::<T>()` and `MaybeUninit::<T>::zeroed()` do not guarantee that padding remains zero in the returned typed value. A round trip through a type whose padding overlaps bytes that the original type requires to be initialized can lose those bytes and make the round trip undefined behavior. Conversely, an **untyped** `ptr::copy` or `ptr::copy_nonoverlapping` preserves byte initialization state exactly; at this pin, `ptr::swap_nonoverlapping` deliberately uses such copies because typed `read`/`write` can lose padding.

For Anneal, value state and representation-byte state must therefore remain separate. Proving that a typed value is valid does not prove that every byte in its storage is initialized. Proving that an ordinary Rust move/copy preserves the value does not prove that padding bytes, their initialization state, or their byte values survive. Any proof that exposes, hashes, compares, serializes, or otherwise observes complete object representations needs an explicit byte-level argument rather than a value-level typed-copy argument.

This report combines the #3720 subjects **Initialization and padding** and **Typed copies and padding initialization** because the pinned public contract defines them through one boundary: padding is permitted to be uninitialized, and typed copies preserve semantic value rather than complete padding state. It is source/specification based; no fresh rustc, Miri, Charon, Aeneas, or Lean execution was performed.

## Applicability

The directly examined subjects are:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the compiler and core-library revision behind the Anneal-era `nightly-2026-05-31`; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference revision examined with that compiler tree.

The report concerns the relationship among four exact-pin interfaces:

1. the Reference's abstract initialized/uninitialized byte model;
2. the Reference's invalid-value rules, including its explicit exception for uninitialized bytes in unions and padding;
3. the core library's `MaybeUninit<T>` contract for typed copies, padding, and zero initialization; and
4. the core pointer library's distinction between typed `read`/`write` and untyped byte copies.

The report uses **typed copy** in the sense used by the pinned `MaybeUninit` documentation: moving or copying a Rust value according to its type, including an ordinary `fn identity<T>(t: T) -> T { t }`. It uses **untyped copy** for operations such as `ptr::copy` and `ptr::copy_nonoverlapping`, whose contracts explicitly permit invalid or uninitialized `T` representations and preserve the initialization state of the copied bytes exactly.

Padding positions are type- and layout-relative. For `repr(C)` structs, the Reference specifies inter-field alignment padding and trailing padding through the layout algorithm. For the default Rust representation, only limited layout guarantees apply and field order can differ. This report does not infer a stable padding map where the Reference does not provide one.

The current native corpus report `rust-validity-well-defined-execution-nightly-2026-05-31` already establishes the broader value-validity versus byte-initialization distinction. This report refines the separate question that report intentionally leaves open: what happens to padding and byte initialization across value construction and typed copies. Separate candidate work covers `MaybeUninit` as an API, raw-pointer bulk copies, raw pointer access, transmutation, and aggregate layout in greater breadth; those are cited only where their contracts define this boundary.

## Findings

### Rust memory distinguishes initialized bytes from uninitialized bytes

The pinned Reference describes memory in terms of abstract bytes. An abstract byte may be initialized with a `u8` value and optional provenance or may be uninitialized; the Reference also warns that this list and Rust's memory model remain incomplete.

Uninitialized is not shorthand for “some arbitrary but fixed byte value.” The pinned `MaybeUninit` documentation states that uninitialized memory does not have a fixed value and that repeated reads may produce different results. That is why producing an uninitialized integer is invalid even though every fixed integer bit pattern is otherwise accepted.

For verification, an initialization mask is therefore semantic state. Replacing an uninitialized byte with an unconstrained but stable `u8` changes the model: it admits observations and equalities that Rust does not promise.

Basis: **normative** Reference memory/validity rules + **documentation** in `core::mem::MaybeUninit`.

### A valid typed value does not require initialized padding

The Reference says producing an invalid value is immediate undefined behavior and then gives per-type validity requirements. Integers, floating-point values, raw pointers, and `str` bytes must be initialized; structs, tuples, and arrays require their fields/elements to be valid. The same section explicitly states that uninitialized memory is permitted inside unions and in padding—the gaps between fields of a type.

The pinned `MaybeUninit` field-by-field construction example demonstrates the intended aggregate boundary. It initializes each field through raw pointers, never initializes the struct's padding, and then calls `assume_init`; the documentation states that leaving padding uninitialized is fine.

Thus a verifier must not use the rule “a valid `T` implies all `size_of::<T>()` bytes are initialized.” The correct obligation is type-directed: bytes that participate in the value's validity must satisfy the relevant rules; padding need not be initialized merely to produce or hold the value.

Basis: **normative** Reference validity rules + **documentation** in `MaybeUninit`.

### Padding is storage in the layout, not stable value content

The Reference defines a type's size as the stride between adjacent array elements, including alignment padding. For `repr(C)` structs, it specifies how padding is inserted before fields to satisfy alignment and how the final size is rounded up to the struct alignment. The `repr(packed)` rules can reduce or eliminate inter-field padding, but they do not redefine the layouts of nested fields.

These layout rules explain where storage gaps can exist; they do not grant those gaps stable value semantics. A padding byte can be part of the `size_of::<T>()` storage range while remaining outside the initialized data required for a valid `T`.

For default `repr(Rust)`, field order and exact offsets are not generally stable across compilations. A byte-level proof that depends on padding locations must therefore name the representation and exact subject for which those locations are established.

Basis: **normative** Reference layout rules + **derived** verification consequence.

### Converting fully initialized fields into `T` can still produce uninitialized padding

The pinned field-by-field `MaybeUninit<Foo>` example goes beyond saying padding need not be initialized. It states that even if code initialized the padding inside the `MaybeUninit<Foo>`, those bytes are lost when the result is copied into `foo`; the padding in `foo` is uninitialized.

This is a useful discriminator for verification models. “Every source byte was initialized immediately before producing `T`” does not imply “every destination byte in the resulting `T` is initialized.” A typed value-producing boundary can discard padding state while preserving the value.

Basis: **documentation** in `library/core/src/mem/maybe_uninit.rs`.

### Typed copies preserve non-padding value bytes, not the complete object representation

The pinned `MaybeUninit<T>` validity documentation states that moving or copying a `MaybeUninit<T>` as a typed value exactly preserves the contents, including provenance, of `T`'s non-padding bytes. It then gives the complementary warning: moving or copying a value whose representation has initialized bytes at offsets where its type has padding may lose those byte values. The semantic value can remain unchanged while its complete byte representation changes.

The documentation says the same caveat applies to the ordinary function:

```rust
fn trivial_identity<T>(t: T) -> T { t }
```

The rule is therefore not limited to a special `MaybeUninit` API. A generic typed move/copy is a value-preservation operation, not a byte-preservation primitive.

For Anneal, any theorem that upgrades value equality across a typed copy to equality of all `size_of::<T>()` representation bytes is too strong unless a separate premise establishes that the relevant type has no padding, that only non-padding bytes are observed, or that the particular operation is specified to preserve the raw byte state.

Basis: **documentation** in `MaybeUninit` + **derived** proof obligation.

### Typed copies can also alter reference provenance through implicit reborrowing

The same pinned documentation warns that copying a value containing references may implicitly reborrow them, causing the provenance of the returned value to differ from the original; it again says this applies to the trivial identity function.

This is a separate axis from padding. Even where non-padding bytes carry a reference-like value and the semantic referent is preserved, a verifier must not equate “copy” with a bit-for-bit, provenance-identity transfer without consulting the relevant pointer/reference semantics.

This report does not attempt to define the still-unsettled complete Rust aliasing/provenance model. The durable point is narrower: the core-library contract itself rejects the inference that ordinary typed copying is necessarily provenance-identical.

Basis: **documentation**; broader provenance semantics are **unknown/incomplete** at the pinned Reference revision.

### A typed round trip through another layout can lose required initialized bytes

The pinned `MaybeUninit` documentation gives a direct round-trip criterion. Converting a `T` through `MaybeUninit<U>` and back can preserve the original value when `T` and `U` have equal size and every byte offset that is padding in `U` corresponds to an uninitialized byte in the original representation. It highlights `[u8; size_of::<T>()]` as a useful no-padding intermediate.

It also gives the failure mode. If `U` has padding at an offset where the original representation requires an initialized byte, the typed `MaybeUninit<U>` copy can discard that byte. Converting back can then produce undefined behavior if `T` requires that byte initialized, or can produce a different value when `T` itself admits uninitialized bytes there.

The important relation is not merely equal size. It is **which offsets the intermediate copy type treats as padding** versus **which offsets the final type requires to carry initialized semantic data**.

Basis: **documentation** in `MaybeUninit`; the relation above is a direct restatement of its sound/unsound examples.

### “Zeroed value” does not imply zero padding after the typed boundary

`MaybeUninit::<T>::zeroed()` first writes zero bytes into the storage, but its documentation warns that if `T` has padding, those bytes are not preserved when the `MaybeUninit<T>` value is returned, so the padding need not remain zero. `mem::zeroed::<T>()` repeats the same warning explicitly: for example, the padding byte of `(u8, u16)` is not necessarily zeroed.

This separates two propositions:

- zero is a valid representation for every non-padding part of `T`; and
- every byte of the final `T` object representation is observable as zero.

The first can justify `zeroed::<T>()` for suitable types. The second is not promised.

For hashing, serialization, deterministic-build checks, FFI byte comparison, or cryptographic use, do not infer stable all-zero padding merely from `zeroed()`.

Basis: **documentation** in `core::mem::MaybeUninit` and `core::mem::zeroed`.

### Untyped raw copies preserve initialization state exactly

`ptr::copy` and `ptr::copy_nonoverlapping` draw the opposite boundary. Their pinned contracts state that the copy is “untyped”: source bytes may be uninitialized or otherwise violate `T`'s validity requirements, and the initialization state is preserved exactly. The type parameter determines size/alignment and participates in access preconditions, but it does not turn the byte range into a sequence of valid `T` values for purposes of the copy.

This makes an untyped copy suitable for moving raw storage whose padding state must survive, provided the operation's pointer validity, alignment, overlap, and ownership requirements are met. It also means a verifier must not impose typed-value validity on every source byte range of such a copy.

This does **not** make arbitrary later typed reads safe. If the copied destination is subsequently produced or read as a `T`, the `T` validity rules apply at that later boundary.

Basis: **documentation/source** in `core::ptr`.

### The pinned library deliberately avoids typed `read`/`write` when padding must survive

The implementation of `ptr::swap_nonoverlapping` at the selected revision contains an explicit comment that it is critical to use `copy_nonoverlapping` rather than `read`/`write` “to avoid #134713 if `T` has padding.” The loop copies through `MaybeUninit<T>` storage with untyped byte copies.

The linked regression, fixed before this pin, arose because an implementation that used `T` as a typed value could fail to swap all representation bytes for a padded type even though `swap_nonoverlapping` promises an untyped byte swap. The eventual fix returned to byte-oriented copying.

This history is useful because it demonstrates that typed versus untyped copy is not merely documentation terminology: the distinction changed observable padding behavior and required an implementation correction.

Basis: **source** at the pinned revision + **source-history** in rust-lang/rust issue #134713 and fix commit `0fe8f3454dbe9dda52a254991347e96bec579a6f`.

### `ptr::read` and `ptr::write` are typed operations even when their implementations resemble copies

At the selected pin, `ptr::read<T>` uses a dedicated intrinsic that lowers to a typed MIR load. Its source comment says an earlier implementation using `copy_nonoverlapping` plus `MaybeUninit::assume_init` did not convey enough information to make the operation typed for optimization purposes. `ptr::write<T>` similarly lowers to a typed move assignment in MIR.

The library notes that raw untyped copies can be semantically useful implementation building blocks, but a public typed operation carries the stronger value-level boundary. In particular, do not use the untyped `copy*` initialization-preservation guarantee as if it automatically applied to `read`, `write`, assignment, return, or argument passing of `T`.

Basis: **source** in `core::ptr`; the general padding consequence is **derived** from the pinned typed-copy contract.

### Verification needs separate value and representation-state judgments

A compact proof model for this boundary needs at least these distinctions:

| Operation/state | Required initialization before the boundary | Padding result promised by the pinned contract | Additional note |
| --- | --- | --- | --- |
| Hold/produce a valid ordinary `T` | All bytes required by `T`'s validity; padding may remain uninitialized | No promise that padding is initialized | Validity may impose restrictions beyond initializedness |
| Field-by-field `MaybeUninit<T>` → `T` | Fields/data needed for valid `T`; padding need not be initialized | Padding can emerge uninitialized even if source padding was initialized | `assume_init` is safe only once `T` itself is valid |
| Ordinary typed move/copy of `T` | Source is a valid `T` | Semantic value preserved; initialized padding may be lost | Reference-containing values may be implicitly reborrowed |
| Typed move/copy of `MaybeUninit<T>` | No `T`-validity requirement on contained bytes | Non-padding contents/provenance preserved; padding may be lost | Useful for representation round trips only under padding conditions |
| `ptr::copy*` | Source/destination ranges satisfy raw access contract; source bytes need not form valid `T` | Initialization state preserved exactly | Alignment/overlap/ownership obligations remain |
| `zeroed::<T>()` | All-zero data representation must be valid for `T` | Final typed padding is not guaranteed zero | Equal byte values across the full object are not promised |
| Read complete representation as `[u8]` | Every byte read as `u8` must be initialized | Uninitialized padding makes a typed `u8` read invalid | Byte inspection needs an API/model that can represent uninitialized bytes |

For Anneal, a useful state decomposition is therefore:

1. **layout** — which byte offsets belong to fields/value representation versus padding for the exact subject;
2. **initialization** — which abstract bytes are initialized;
3. **byte/provenance contents** — the contents of initialized bytes, including provenance where applicable;
4. **typed validity** — whether producing a value of the relevant type is allowed; and
5. **operation semantics** — whether a particular operation is typed/value-level or untyped/byte-level.

Collapsing these into a single “valid memory” predicate loses behavior that the pinned Rust contracts distinguish.

Basis: **derived** from the normative/documented contracts above.

## Boundaries

**The Rust memory model is explicitly incomplete.** The pinned Reference warns that its abstract-byte model is not fully decided or exhaustive. This report records the contracts that are stated at the selected revision; it does not invent a complete operational model for every optimizer transformation.

**No fresh execution evidence.** No rustc/Miri probe was run. The report relies on exact pinned Reference text, core-library public contracts, and implementation/source history. A probe can strengthen implementation observations, but it cannot replace these contracts.

**No complete padding map for arbitrary types.** `repr(C)` supplies a concrete struct padding algorithm; the default Rust representation deliberately leaves more freedom. Enums, niche optimizations, DSTs, and target-specific ABI details can require additional layout research. This report does not treat a guessed layout as semantic evidence.

**Padding is not a universal set of byte offsets independent of the copy type.** The round-trip examples specifically compare offsets that one type treats as padding with offsets another type treats as semantic data. A verification rule must classify padding relative to the type/operation being modeled.

**No claim that every typed copy always rewrites every padding byte to uninitialized.** The public contract says padding values may be lost and gives specific examples where returned padding is uninitialized. The durable guarantee is the lack of full-representation preservation, not a stronger universal postcondition for every compiler lowering.

**No general provenance or aliasing model.** The report preserves the explicit typed-copy reborrow warning but does not resolve Rust's still-open pointer/provenance/aliasing questions.

**No ownership shortcut.** Untyped copies preserve initialization state but can duplicate representations of non-`Copy` resource-owning values. Correct use still needs the ownership/lifetime protocol described by the relevant pointer operation.

**No claim that `repr(C)` or `repr(packed)` initializes padding.** Representation attributes constrain layout. They do not by themselves provide a byte-initialization guarantee. `repr(packed)` can also create unaligned-field hazards outside this report's scope.

**No claim that valid values have deterministic byte encodings.** Padding, provenance, niches, and representation freedom can all matter. Value equality, semantic identity, and byte equality remain separate questions.

## Evidence

Evidence was materially revalidated on 2026-09-27.

**Normative language reference:** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`.

- `src/memory-model.md`, blob `cc3cf02ec0adba12134ad6cb82e51a4b864da784` — abstract initialized/uninitialized bytes, optional provenance, explicit incompleteness.
- `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284` — invalid-value production, initializedness requirements, aggregate validity, and explicit permission for uninitialized bytes in unions and padding.
- `src/type-layout.md`, blob `2ee902aef043f4d299e009f6a69d1815d862e69e` — size/stride including alignment padding, default-layout guarantees, `repr(C)` inter-field/trailing padding algorithm, and `repr(packed)` padding behavior.

**Core-library documentation/source:** `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

- `library/core/src/mem/maybe_uninit.rs`, blob `7e2c6b9b3bcb2d66af376243d95c541e5bd4024d` — initialization invariant; field-by-field initialization with uninitialized padding; typed-copy preservation of non-padding contents/provenance; loss of initialized padding; reference-reborrow caveat; sound and unsound representation round trips; byte views that retain `MaybeUninit<u8>` for potentially uninitialized padding.
- `library/core/src/mem/mod.rs`, blob `62c612e7ba2a65bb1645faaa669abd2a1d35a6c2` — `size_of` padding explanation and `mem::zeroed` warning that padding is not necessarily zeroed.
- `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2` — untyped `copy`/`copy_nonoverlapping` initialization-state preservation; typed `read`/`write` implementation boundary; `swap_nonoverlapping`'s deliberate untyped-copy implementation for padded types.

**Source history:** rust-lang/rust issue #134713, “`std::ptr::swap_nonoverlapping` is not always untyped,” and fix commit `0fe8f3454dbe9dda52a254991347e96bec579a6f`, “Ensure `swap_nonoverlapping` is really always untyped.” The fix predates and is incorporated into the selected Rust revision.

**Current native corpus boundary:** `google/zerocopy` `reference@b6c1ba9f891840fc95a1de167bc17ebc38f5cf07` contains 105 catalogued reports. Its existing `rust-validity-well-defined-execution-nightly-2026-05-31` report covers the broad validity/initialization distinction but does not supply the typed-copy/padding preservation contract developed here.

There is no fresh **execution** evidence in this package.

## Revalidation

For another Rust revision or toolchain pin, the cheapest reliable revalidation is a narrow contract/source diff:

1. Recheck the bundled Reference's `memory-model.md` abstract-byte states and incompleteness warning.
2. Recheck `behavior-considered-undefined.md` for invalid-value production, scalar initializedness, aggregate validity, union validity, and the explicit padding exception.
3. Recheck `type-layout.md` for default-representation freedom and the exact `repr(C)`/`repr(packed)` padding rules Anneal relies on.
4. Diff `MaybeUninit`'s **Initialization invariant** and **Validity** sections, especially the typed-copy guarantee for non-padding bytes, the initialized-padding-loss caveat, reference reborrowing, and the cross-layout round-trip examples.
5. Recheck `MaybeUninit::zeroed` and `mem::zeroed` for any changed promise about padding.
6. Recheck `ptr::copy` and `ptr::copy_nonoverlapping` for the “untyped” and “initialization state is preserved exactly” contract.
7. Recheck `ptr::read`, `ptr::write`, and `swap_nonoverlapping` implementation/comments only if Anneal relies on their precise typed/untyped boundary rather than the public contracts alone.
8. If the target type's exact padding offsets matter, determine them for that exact type/representation/target instead of carrying forward an offset map from another compilation.

On an execution-capable surface, a small Miri probe suite can provide useful regression evidence without replacing the source contracts:

- initialize every byte of a padded `repr(C)` struct inside `MaybeUninit`, then materialize/copy the typed struct and inspect bytes through a `MaybeUninit<u8>` representation to show that initialized padding is not a stable typed-copy invariant;
- round-trip `[u8; 4]` through the report's `repr(C) U(u8, u16)` shape and confirm the invalid/uninitialized-byte failure under Miri;
- compare an ordinary typed identity with `ptr::copy_nonoverlapping` for a padded type while recording an initialization-aware observation rather than performing UB by reading uninitialized padding as `u8`; and
- retain the historical `swap_nonoverlapping` regression fixture as a golden discriminator against accidentally reintroducing typed copying into an untyped byte operation.

Preserve exact commands, target triple, rustc/Miri versions, source, and output with any such execution result. A passing probe establishes only the tested implementation/configuration; it does not strengthen the language contract beyond the pinned evidence above.
