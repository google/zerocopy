# `MaybeUninit` semantics at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `MaybeUninit<T>` is Rust's type-level escape hatch from `T`'s ordinary value-validity invariant. A `MaybeUninit<T>` may contain any initialized or uninitialized byte sequence of the appropriate size. The wrapper carries **no runtime initialized/uninitialized tag** and dropping it never runs `T`'s destructor. Safety is recovered only when code crosses back to `T`, `&T`, `&mut T`, or `Drop` through an operation whose caller asserts that the required initialization and validity conditions now hold.

That boundary is narrower and more precise than “all bytes have been written.” Padding may remain uninitialized. Conversely, integers and raw pointers still may not be produced from uninitialized bytes merely because all fixed bit patterns would otherwise be accepted. `assume_init` requires a valid `T`, not just allocated storage; `assume_init_ref` and `assume_init_mut` require validity before the reference is formed and therefore cannot themselves be used to initialize the object.

`MaybeUninit<T>` has the same size, alignment, and ABI as `T`, but substituting it inside a containing type can change that containing type's layout because `MaybeUninit<T>` accepts all representations and therefore cannot offer `T`'s niches. ABI compatibility also does not make `&mut T -> &mut MaybeUninit<T>` a sound safe abstraction: safe code could overwrite the wrapper with `MaybeUninit::uninit()` and leave the original `T` invalid.

The wrapper is also not a byte-preservation primitive for padding. The pinned documentation guarantees that a typed move/copy of `MaybeUninit<T>` preserves the contents and provenance of `T`'s **non-padding** bytes. Padding can lose initialized contents during typed copies. `zeroed()` likewise does not guarantee that padding bytes remain zero in the returned value. Code that needs to preserve every representation byte must reason at the byte-storage layer rather than infer a stronger guarantee from `MaybeUninit<T>`'s size/ABI equivalence.

For verification, the useful state split is: **storage may hold arbitrary initialization state while typed as `MaybeUninit<T>`; every transition that produces or uses a `T` must re-establish the validity and ownership conditions of the specific transition.** `write` establishes a fresh `T` without dropping prior contents; `assume_init` transfers one initialized value out; `assume_init_read` duplicates representation and therefore can duplicate ownership; `assume_init_drop` destroys in place and requires whatever invariants `Drop` may rely on; and raw-pointer access must obey the pointer operation's own access and aliasing rules.

This report is based on exact pinned core-library source/documentation and the bundled Rust Reference. No fresh rustc or Miri execution was performed.

## Applicability

This report applies to the Rust toolchain subject selected by the current Anneal/Charon pin:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, corresponding to the Anneal-era `nightly-2026-05-31`; and
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, the Reference revision examined with that compiler tree.

The primary implementation/documentation subject is `core::mem::MaybeUninit<T>` in `library/core/src/mem/maybe_uninit.rs`. The report covers the semantic boundary around `new`, `uninit`, `zeroed`, `write`, pointer accessors, the `assume_init*` family, partial aggregate initialization, layout/ABI guarantees, typed-copy behavior, and the stable slice conveniences present at this pin where they materially clarify the model.

This report does not attempt to replace the separate corpus subjects for general Rust validity, raw-pointer provenance/access, pointer reads/writes, bulk copies, aggregate padding, typed copies and padding initialization, `mem::transmute`, or niche semantics. Those subjects share facts with `MaybeUninit`, but each has additional contracts. Here they appear only where necessary to define `MaybeUninit`'s boundary.

The Reference explicitly says Rust's overall memory model and exact aliasing rules remain incomplete. This report therefore preserves the public API contracts and the Reference's pinned validity rules without inventing a complete operational semantics.

## Findings

### `MaybeUninit<T>` suspends `T`'s value-validity invariant without tracking state

The type documentation states that the compiler ordinarily assumes every produced value is valid for its type. It gives three canonical counterexamples:

- a null reference is invalid even if never dereferenced;
- an uninitialized `bool` is invalid because only `0` and `1` are valid values; and
- an uninitialized integer is invalid even though every fixed integer bit pattern is otherwise accepted, because an uninitialized byte is not an ordinary fixed byte value.

The bundled Reference matches this boundary. Producing an invalid value is immediate UB; integer, floating-point, and raw-pointer values must be initialized; and uninitialized memory is permitted only where the type's representation admits it, notably inside unions and padding.

`MaybeUninit<T>` is the dedicated wrapper that suspends those assumptions. Its pinned type documentation says it has **no validity requirements**: any initialized or uninitialized byte sequence of the appropriate length is a valid `MaybeUninit<T>` representation. The implementation is a union containing either `()` or `ManuallyDrop<T>`, so Rust does not require the `T` field to be a valid active value merely because the wrapper exists.

There is no dynamic initialization bit in the value. `MaybeUninit::uninit()` and `MaybeUninit::new(value)` have the same Rust type. Whether later `assume_init*` operations are sound is therefore a proof obligation carried by the surrounding unsafe code, not a state check performed by `MaybeUninit`.

Basis: **documentation/source** in `library/core/src/mem/maybe_uninit.rs` + **normative** bundled Reference invalid-value rules.

### “Initialized enough for `T`” is not the same as “every representation byte is initialized”

The type documentation explicitly permits padding to remain uninitialized when `assume_init` is called. Its field-by-field struct example initializes each field but not padding and then extracts the struct.

This follows the Reference's value model: padding is not itself a typed field value that must be initialized. In contrast, bytes that contribute to an integer, raw pointer, discriminant, reference, or other value component must meet that component's validity requirements when a `T` is produced.

The durable verification rule is therefore not “mark the entire object byte range initialized.” Instead, prove that the representation satisfies the validity requirements of `T`; uninitialized bytes are permitted only at positions where `T` permits them, such as padding.

For aggregate initialization this usually means establishing every field/element that contributes to the value while allowing padding to remain indeterminate. A future model that tracks initialization bytewise should not require padding initialization as a precondition for producing the aggregate.

Basis: **documentation** + **normative** Reference validity rules; byte-level proof formulation is **derived**.

### Uninitialized bytes are semantically distinct from arbitrary initialized bytes

The pinned documentation warns that uninitialized memory does not have a fixed ordinary value: reading the same uninitialized byte multiple times can conceptually yield different results. The bundled Reference's memory-model chapter likewise distinguishes an initialized byte carrying a `u8` value (and possibly provenance) from an uninitialized byte.

This distinction matters for `MaybeUninit`. `MaybeUninit::<u32>::uninit()` is a valid wrapper, but `assume_init()` is not justified merely because every *initialized* 32-bit pattern would be a valid `u32`. The missing proposition is initialization itself.

Similarly, an uninitialized raw-pointer representation cannot be produced as a raw-pointer value merely because raw pointers accept many bit patterns. The Reference explicitly requires raw pointers to be initialized.

Basis: **documentation** + **normative** bundled Reference.

### `new`, `uninit`, and `zeroed` establish three different facts

`MaybeUninit::new(val)` stores a real `T`; the result may immediately be passed to `assume_init`. The wrapper suppresses automatic destruction, however, so dropping the wrapper itself still does not drop `val`.

`MaybeUninit::uninit()` establishes only that the wrapper itself is valid. It establishes nothing about whether the contents may be interpreted as `T`.

`MaybeUninit::zeroed()` writes zero bytes across the storage but still returns `MaybeUninit<T>`. Whether that state is a valid `T` depends on `T`. Zero is valid for examples such as ordinary integers and `false`, but not for types whose validity excludes zero, such as references or an enum with no zero discriminant.

There is an additional representation caveat: if `T` has padding, the documentation says those padding bytes are not guaranteed to remain zero when the `MaybeUninit<T>` value is returned. A typed return/move may lose padding contents.

For verification, model these constructors as:

- `new(T)`: initialized `T` stored, destructor responsibility deferred;
- `uninit()`: arbitrary initialization state allowed by the wrapper;
- `zeroed()`: non-padding bytes are zero-initialized enough to reason about the eventual `T`, but extraction still requires proving zero is valid for `T`, and padding-byte equality is not guaranteed.

The last line is a semantic summary, not a claim that the implementation exposes a per-byte postcondition for every optimization. When exact representation bytes matter, use a byte-level argument rather than `zeroed()`'s high-level intent.

Basis: **documentation/source** in `MaybeUninit::{new,uninit,zeroed}`; final verification formulation is **derived**.

### Dropping `MaybeUninit<T>` never drops `T`

The wrapper stores `T` in `ManuallyDrop<T>` and has no automatic inner destruction. The type documentation repeatedly states that leaving an initialized `MaybeUninit<T>` to go out of scope does not call `T`'s destructor.

This makes partial construction memory-safe in the presence of panic but not leak-free by default. If an array or struct has some resource-owning fields initialized and construction then aborts, dropping the surrounding `MaybeUninit` does not know which fields are live and therefore does not clean them up. The caller needs an explicit initialized-prefix count, guard, or equivalent cleanup protocol if leaks matter.

Leaks are not automatically Rust UB. They can still violate higher-level resource requirements and are often operationally undesirable. A verifier should keep “memory-safety proof” distinct from “all owned resources are eventually destroyed.”

Basis: **documentation/source**; cleanup distinction is **derived**.

### `write` initializes without reading or dropping the prior contents

`MaybeUninit::write(&mut self, val)` replaces the wrapper with `MaybeUninit::new(val)` and then returns `&mut T`. Because the prior contents are held as possibly uninitialized storage, the operation intentionally does not run a destructor for whatever bytes were previously there.

This is exactly what is needed for first-time initialization. It also means that calling `write` twice on an already initialized resource-owning value leaks the first value unless the caller extracted or dropped it first.

The mutable reference returned by `write` is different: once the value has been safely initialized, assigning through that `&mut T` has ordinary Rust assignment behavior and therefore drops the previous `T` as usual.

This distinction is useful for proof state:

1. `MaybeUninit` storage has no live-`T` destruction obligation merely because bytes exist there;
2. successful `write(val)` creates one live initialized `T` in the storage;
3. the returned `&mut T` can be manipulated as an ordinary initialized mutable reference; and
4. ownership/destruction still must eventually be transferred through `assume_init`, performed through `assume_init_drop`, or intentionally leaked.

Basis: **source/documentation** in `MaybeUninit::write`; proof-state decomposition is **derived**.

### Raw pointer access is permitted before initialization, typed access is not

`as_mut_ptr()` returns a raw `*mut T` to the storage. This pointer is the intended bridge for out-pointers and field-by-field initialization: raw writes can initialize the backing storage without first creating a `T` or `&mut T`.

`as_ptr()` similarly returns `*const T`, but the documentation says reading from it or turning it into a reference is UB unless the wrapper is initialized. In addition, because `as_ptr()` is derived from `&self`, writing directly to the memory it non-transitively points to is UB except through `UnsafeCell<T>`; callers needing initialization should obtain mutable access and use `as_mut_ptr()` instead.

The pointer accessors do not themselves assert initializedness. The unsafe boundary occurs at the later operation: raw write, raw read, reference creation, field projection that causes a load, and so on each carry their own pointer/access obligations.

Basis: **documentation/source** in `MaybeUninit::{as_ptr,as_mut_ptr}` plus the bundled Reference's access/aliasing boundary.

### `assume_init` transfers one `T`; it is not a validity check

`assume_init(self) -> T` is unsafe because the caller must establish that the wrapper currently contains a value valid for `T`. The implementation asserts that `T` is inhabited, then performs a raw read of the union's `T` storage.

Calling `assume_init` on uninitialized `i32` is UB even though integers accept every fixed initialized bit pattern. Calling it on zeroed storage for a reference or restricted discriminant is UB because that representation is invalid for the target type.

The method does not dynamically inspect or validate the bytes. “Assume” is literal: it converts the caller's proof obligation into a typed value.

The documentation also distinguishes compiler-level validity from stronger library invariants. It notes that some representations can satisfy the compiler's current immediate validity assumptions for a type such as `Vec<T>` while still making most safe operations, including dropping, UB. Thus a verification system should not collapse “`assume_init` does not immediately violate rustc's value-validity rules” into “all safe operations on the resulting value are sound.”

Basis: **documentation/source** + **normative** invalid-value rule.

### `assume_init_read` is a typed copy and can duplicate ownership

`assume_init_read(&self) -> T` requires initialized contents, then performs `self.as_ptr().read()`. Like `ptr::read`, it makes a bitwise copy regardless of whether `T: Copy`.

The source bytes remain in the wrapper. Calling `assume_init_read` multiple times on a resource-owning `T`, or calling it once and later extracting/dropping the original, can therefore create two logical owners of the same underlying resource and lead to double free or other invariant violations.

The documentation gives a precise safe-looking contrast: repeatedly reading `u32` is fine; repeatedly reading a `None` variant of `Option<Vec<_>>` can also be fine because that particular value carries no vector ownership; repeatedly reading `Some(Vec<_>)` creates duplicate owners and is invalid.

A verifier should therefore model `assume_init_read` as “copy the initialized `T` representation” rather than “move `T` out.” Whether that copy may subsequently be used/dropped more than once depends on the actual value's ownership semantics, not solely on the trait bound because the method has no `T: Copy` requirement.

Basis: **documentation/source**; ownership interpretation is **derived**.

### `assume_init_ref` and `assume_init_mut` cannot be used to finish initialization

`assume_init_ref(&self) -> &T` and `assume_init_mut(&mut self) -> &mut T` both require the `T` to be fully initialized **before the reference is created**. The implementation simply forms `&*self.as_ptr()` or `&mut *self.as_mut_ptr()` after checking inhabitedness.

The documentation explicitly rejects tempting patterns such as:

- calling `assume_init_mut()` on uninitialized `bool` and then assigning `true` through the reference;
- converting an uninitialized byte array to `&mut [u8; N]` and asking `Read::read_exact` to fill it; and
- using `assume_init_mut()` to take ordinary field references during gradual struct construction.

Each fails before the subsequent write can help: producing a reference already requires a valid initialized referent.

The correct gradual-initialization pattern uses raw pointers, especially `&raw mut (*ptr).field` followed by raw-pointer `write`, and only forms ordinary references after all required fields are initialized.

Basis: **documentation/source** in `assume_init_ref` and `assume_init_mut`; raw-field pattern documented at the type level.

### `assume_init_drop` has a stronger practical obligation because `Drop` can inspect invariants

`assume_init_drop(&mut self)` destroys the stored `T` in place using `ptr::drop_in_place`. The caller must guarantee both that the representation is initialized and that any additional invariants relied upon by `T`'s destructor are satisfied.

The pinned documentation calls this distinction out directly with `Vec<T>`: a representation may satisfy rustc's current minimal immediate validity assumption while containing an unusable pointer. Destroying such a vector can still be UB because `Drop` follows that pointer according to the vector's library invariant.

This is a concrete example of why a verifier may need two layers:

- language/compiler value validity sufficient to produce a `T`; and
- operation-specific library invariants sufficient for the safe operation being performed, including destruction.

Basis: **documentation/source** in `assume_init_drop`; two-layer formulation is **derived**.

### Partial aggregate construction requires raw field writes and an external initialization protocol

The pinned type documentation provides field-by-field struct construction:

1. allocate `MaybeUninit<Foo>::uninit()`;
2. obtain `*mut Foo` with `as_mut_ptr()`;
3. use `&raw mut (*ptr).field` and raw-pointer `write` for each field; and
4. call `assume_init()` only after every field needed for a valid `Foo` is initialized.

Using ordinary `&mut (*ptr).field` through `assume_init_mut()` would first create a reference to an invalid not-yet-initialized `Foo`, so it is not a substitute.

The same principle scales to arrays. `[MaybeUninit<T>; N]` permits an initialized prefix and uninitialized remainder. Because the wrapper's destructor does not clean initialized elements automatically, the caller tracks the initialized prefix and calls `assume_init_drop` on those elements if construction aborts.

The stable slice helper `write_clone_of_slice` demonstrates the same protocol internally: it uses a guard that counts initialized elements and drops them if cloning panics, then forgets the guard once initialization succeeds. The existence of that guard is useful evidence that panic cleanup is a separate state transition, not something `MaybeUninit` supplies automatically.

Basis: **documentation/source**; generalized state-machine description is **derived**.

### `MaybeUninit<T>` has `T`'s size, alignment, and ABI, but not `T`'s niche contract

The pinned documentation guarantees that `MaybeUninit<T>` always has the same size, alignment, and ABI as `T`. It also states that if `T` is FFI-safe, then `MaybeUninit<T>` is FFI-safe.

That guarantee does **not** imply that a containing generic or aggregate type has the same layout when `T` is replaced by `MaybeUninit<T>`. Because every byte pattern is valid for `MaybeUninit<T>`, the compiler cannot reuse invalid `T` patterns as niches around the wrapper. The documentation's example is exact: `Option<bool>` is one byte, while `Option<MaybeUninit<bool>>` is two at this revision.

Therefore transformations such as `Outer<T> -> Outer<MaybeUninit<T>>` are not generally layout preserving even though the leaf types have identical size/alignment/ABI.

Likewise, the leaf ABI guarantee does not make a safe mutable-reference reinterpretation valid. The documentation explicitly shows `&mut T -> &mut MaybeUninit<T>` as unsound when exposed to safe code: the receiver can safely assign `MaybeUninit::uninit()`, after which the original `&mut T` names invalid storage.

Basis: **documentation/source**; transformation consequence is **derived**.

### Typed copies preserve non-padding contents, not arbitrary padding bytes

The pinned `MaybeUninit` validity section gives an unusually strong and useful guarantee: moving or copying `MaybeUninit<T>` as a typed value preserves the contents, including provenance, of all **non-padding bytes of `T`**.

The qualifier is essential. Typed moves/copies are allowed to lose initialized contents at padding byte offsets. The documentation notes the same phenomenon for ordinary typed identity: the logical value can be preserved while its padding representation changes or becomes uninitialized.

This means `MaybeUninit<T>` is suitable for preserving arbitrary state in positions where `T` itself has meaningful representation bytes, but it is not a promise to preserve every byte of an allocation or object representation. Code that stores information in `T`'s padding and expects it to survive a typed move has no such guarantee.

The documentation derives a useful round-trip condition for transmuting `T -> MaybeUninit<U> -> T`:

- `T` and `U` must have the same size; and
- every byte position that is padding in `U` must already be uninitialized in the original representation.

If `U` has padding where the original `T` carries initialized meaningful bytes, the intermediate typed copy may discard those bytes; transmuting back can then be UB or produce a different value. By contrast, `MaybeUninit<[u8; size_of::<T>()]>` uses a no-padding byte array and can preserve the original non-padding representation in the documented round-trip.

For verification, this is a warning against modeling typed `MaybeUninit<T>` moves as a byte-for-byte `memcpy` over all `size_of::<T>()` bytes. Preserve initialization/provenance for `T`'s non-padding bytes; treat padding as semantically unstable unless the operation is explicitly byte-oriented.

Basis: **documentation/source**; verifier rule is **derived**.

### `zeroed()` does not contradict padding instability

`MaybeUninit::zeroed()` calls `write_bytes(0, 1)` on the backing storage, but its documentation immediately warns that padding bytes are not preserved when the wrapper value is returned. This is consistent with the typed-copy rule above: the implementation can write those bytes, yet the language-level move/return of the typed wrapper need not preserve them.

A test that inspects padding after `zeroed()` therefore cannot elevate an observed compiler behavior into a portable semantic guarantee. The public contract is explicitly weaker.

Basis: **source + documentation**.

### Stable slice helpers encode useful initialization-state transitions

At this pin, `[MaybeUninit<T>]` has stable helpers that expose common safe transitions:

- `write_copy_of_slice` copies initialized `T: Copy` values into the destination and returns `&mut [T]`;
- `write_clone_of_slice` clones values, cleans up the initialized prefix on panic, and returns `&mut [T]` on success;
- slice `assume_init_ref` / `assume_init_mut` convert only when every element is initialized; and
- slice `assume_init_drop` destroys only under the caller's assertion that every element is initialized and satisfies `Drop`'s required invariants.

These methods do not change the underlying model. They package proofs that a whole slice has transitioned from “may contain uninitialized elements” to “all elements are valid `T`,” while retaining explicit unsafe boundaries where the library cannot establish that state itself.

Unstable array/byte-view helpers also exist at the selected revision. Their presence is implementation evidence but should not be assumed as stable Anneal-facing API without separately deciding whether nightly-only standard-library APIs are acceptable.

Basis: **source/documentation** in the selected core revision.

### A verifier should model initialization and ownership as separate state dimensions

A compact proof state for `MaybeUninit<T>` needs at least two independent dimensions:

1. **representation validity / initialization state** — whether the storage currently meets the compiler-level requirements for producing `T`; and
2. **ownership/destruction state** — whether a live `T` resource exists in the storage and which operation is responsible for moving, copying, or destroying it.

Examples show why one bit is insufficient:

- `MaybeUninit::uninit()` is wrapper-valid but not `T`-valid and owns no `T` to destroy;
- after `write(Vec::new())`, the bytes are `T`-valid and a vector resource exists, yet dropping the wrapper still does not destroy it;
- after `assume_init_read()` on a resource-owning value, both the returned `T` and source representation can describe the same resource, so validity alone does not prevent double destruction;
- after `assume_init()`, ownership has moved into the returned `T`, and the consumed wrapper is gone;
- after `assume_init_drop()`, the in-place resource is destroyed, but treating the old storage as a live `T` again would require reinitialization.

For partial arrays/structs, initialization is finer-grained than a whole-object boolean. A prefix or subset of fields may own live resources while the aggregate as a `T` is still invalid. Panic cleanup needs to know that finer state even though the wrapper itself remains valid throughout.

Basis: **derived synthesis** from the pinned constructors, extraction methods, and partial-initialization examples.

## Boundaries

**No fresh execution.** No rustc, Miri, sanitizer, Charon, Aeneas, or Lean probe was run. The report records pinned public contracts/source and the bundled Reference's validity model.

**No complete Rust memory model.** The bundled Reference explicitly says the memory model and exact aliasing rules remain incomplete. This report does not infer a complete provenance or aliasing semantics from `MaybeUninit`.

**No general padding survey.** This report records the padding facts that are part of `MaybeUninit`'s contract: padding need not be initialized for `assume_init`, and typed copies need not preserve padding contents. It does not attempt to enumerate padding creation, aggregate assignment, ABI, or every typed-copy rule. Those remain separate corpus subjects.

**No claim that “initialized” implies every library invariant.** The pinned documentation itself distinguishes compiler-recognized value validity from additional invariants of types such as `Vec<T>`. Some safe operations or `Drop` may require stronger conditions.

**No claim that arbitrary raw writes initialize a `T`.** `as_mut_ptr()` makes raw initialization possible; the caller must still ensure that the final representation is valid for `T` before a typed value/reference is produced.

**No guarantee that zeroed padding stays zero.** The documentation explicitly denies that guarantee.

**No byte-for-byte preservation guarantee for typed moves.** The stable guarantee covers non-padding bytes of `T`; padding can change or become uninitialized.

**No blanket FFI layout substitution for containers.** `MaybeUninit<T>` itself shares `T`'s ABI when `T` is FFI-safe, but a larger type containing `MaybeUninit<T>` can lay out differently because niches differ.

**No stable-API promise for nightly-only helpers.** Unstable array/byte-view/fill helpers observed in the selected nightly are evidence about that subject, not a stable cross-version interface.

**No automatic panic cleanup.** Partial initialization without a guard can leak initialized fields/elements. This is not automatically language-level UB, but it matters to resource-correctness claims.

## Evidence

Evidence was materially revalidated on 2026-09-27.

Primary compiler/core subject:

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
  - `library/core/src/mem/maybe_uninit.rs`, blob `7e2c6b9b3bcb2d66af376243d95c541e5bd4024d`: type-level initialization invariant, layout/ABI and validity guarantees, typed-copy/padding semantics, constructors, pointer accessors, extraction/reference/drop APIs, partial aggregate examples, and slice helpers.

Bundled normative language subject:

- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`
  - `src/behavior-considered-undefined.md`, blob `373052061c50fc2f6d1c07a91960d40bac505284`: invalid-value rule, scalar/raw-pointer initializedness, reference/box validity, aggregate validity, aliasing uncertainty, and the limited places where uninitialized memory is permitted.
  - `src/memory-model.md`, blob `cc3cf02ec0adba12134ad6cb82e51a4b864da784`: explicit distinction between initialized and uninitialized abstract bytes and warning that the model is incomplete.

Current corpus boundaries checked while selecting/drafting this report:

- `rust-validity-well-defined-execution-nightly-2026-05-31` supplies the broader value-validity/execution distinction.
- Current uncommitted candidates for raw-pointer validity, pointer read/write, bulk copy, pointer arithmetic, pointer casts/provenance, and wide-pointer metadata cover adjacent questions. Their own prose explicitly leaves `MaybeUninit` and/or padding as separate subjects; they were not treated as current native fulfillment.

Evidence roles are **normative**, **documentation**, **source**, and **derived**. There is no fresh **execution** evidence.

## Revalidation

For a different Rust revision, the cheapest high-value revalidation is source/documentation diffing rather than a broad compiler survey:

1. Diff `library/core/src/mem/maybe_uninit.rs` around the type-level **Initialization invariant**, **Layout**, and **Validity** sections. These carry the deepest semantic guarantees.
2. Recheck the representation of `MaybeUninit<T>` and the explicit guarantee that size, alignment, and ABI equal `T`.
3. Recheck `new`, `uninit`, `zeroed`, and `write`, paying special attention to zeroed padding and overwrite-without-drop wording.
4. Recheck `as_ptr` / `as_mut_ptr` for changed aliasing/reference-formation guidance.
5. Recheck `assume_init`, `assume_init_read`, `assume_init_ref`, `assume_init_mut`, and `assume_init_drop` for validity, duplication, and additional-invariant requirements.
6. Recheck the typed-copy guarantee for non-padding bytes and provenance. This language is especially important for any Anneal reasoning about padding or representation preservation.
7. Recheck stable slice/array helpers only if Anneal relies on those API surfaces.
8. Diff the bundled Reference's invalid-value and memory-byte sections. If the Reference has strengthened or changed initialization, union, reference, or provenance rules, revisit every derived claim rather than carrying forward this report mechanically.

A small exact-nightly execution probe can strengthen diagnostics but cannot replace the source contracts. Useful cases include:

- `MaybeUninit::<bool>::uninit().assume_init()` under Miri, expected to be rejected as invalid/uninitialized;
- `MaybeUninit::<&u8>::zeroed().assume_init()` under Miri, expected to be rejected as an invalid null reference;
- field-by-field raw initialization of a padded struct followed by `assume_init`, expected to succeed without padding initialization;
- repeated `assume_init_read` of `Some(Vec<_>)`, expected to expose duplicate-ownership failure if both copies are dropped; and
- a padding-observation fixture demonstrating that initialized padding is not a portable typed-move invariant.

Preserve commands, exact toolchain, and outputs if such probes are run. A successful or failing Miri experiment establishes behavior of that checked configuration; it does not supersede the pinned public contract or resolve the Reference's explicitly open memory-model questions.
