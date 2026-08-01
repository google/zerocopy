# Unsafe Rust audit: `opaque-byte-tools` 0.1.0

## Claim and verdict

- **Claim:** For the exact snapshot, Rust 1.85.0, every supported target and
  ordinary profile, and both values of `debug_assertions`, every well-typed
  safe use and every unsafe use satisfying its documented contract is free of
  Rust undefined behavior.
- **Soundness verdict:** **UNSOUND** — four independently valid safe uses reach
  UB (`F-01`–`F-04`).
- **Documented-postcondition verdict:** **CONTRACT-BROKEN** —
  `item_unchecked` does not return the documented element (`F-05`).
- **Proof-artifact status:** **UNPROVED** — the snapshot has no valid adjacent
  proof for any unsafe block (`F-06`).
- **Combined result:** **UNSOUND + CONTRACT-BROKEN**.
- No build, test, macro expansion tool, or target code was executed.

## Findings

### F-01 — `decode_flag` creates invalid `bool` values

**Status:** UNSOUND

The entirely safe call `decode_flag(2)` reaches
`mem::transmute::<u8, bool>(2)`. Rust 1.85 guarantees `bool` size 1 but permits
only bit patterns `0x00` and `0x01`; any other pattern is UB. `transmute`
additionally requires its result to be valid at the destination type.
[Rust 1.85 Boolean
Reference](https://doc.rust-lang.org/1.85.0/reference/types/boolean.html#r-type.bool.repr),
[`transmute`
contract](https://doc.rust-lang.org/1.85.0/std/mem/fn.transmute.html).

Minimum resolution: avoid `transmute`; explicitly map or reject values.

### F-02 — Safe `AddressSource` implementations can supply unreadable pointers

**Status:** UNSOUND

A downstream safe witness is:

```rust
struct Null;

impl AddressSource for Null {
    fn address(&self) -> *const u8 {
        core::ptr::null()
    }
}

load_source(&Null);
```

`AddressSource` is not an unsafe or sealed trait, so its implementations cannot
carry an unenforced soundness obligation. `ptr::read` requires a pointer valid
for reads, properly aligned, and pointing to initialized `T`; Rust 1.85 states
a null pointer is never valid for a non-zero-sized access.
[`ptr::read`
safety](https://doc.rust-lang.org/1.85.0/core/ptr/fn.read.html#safety),
[`core::ptr`
validity](https://doc.rust-lang.org/1.85.0/core/ptr/index.html#safety),
[unsafe-trait
boundary](https://doc.rust-lang.org/1.85.0/reference/items/traits.html#unsafe-traits).

Minimum resolution: return `&u8` from the safe trait method, or make and fully
document an unsafe sealed boundary whose implementations guarantee
accessibility, initialization, lifetime, and permitted concurrent access.

### F-03 — Public `ByteHandle` construction does not establish its read
invariant

**Status:** UNSOUND

This is valid safe code:

```rust
ByteHandle {
    address: core::ptr::NonNull::dangling(),
}
.load();
```

`NonNull` guarantees non-nullness, not dereferenceability. Rust 1.85 explicitly
describes `NonNull::dangling()` as dangling but well-aligned, while `read`
requires validity for a non-zero-sized `u8` access.
[`NonNull::dangling`](https://doc.rust-lang.org/1.85.0/core/ptr/struct.NonNull.html#method.dangling),
[`ptr::read`
safety](https://doc.rust-lang.org/1.85.0/core/ptr/fn.read.html#safety).

The required invariant—live, readable, initialized storage for the entire
call—is unowned because the field is public and safely replaceable.

### F-04 — `profile_index` relies on `debug_assert!` for memory safety

**Status:** UNSOUND when `debug_assertions = false`; no UB from this path when
it is true

The private macro generates the public safe function `profile_index`. In the
explicitly supported `debug_assertions = false` configurations, this safe call
reaches UB:

```rust
profile_index(&[], 0);
```

Rust 1.85 says optimized builds do not execute `debug_assert!` unless debug
assertions are enabled. `slice::get_unchecked` states that calling it with an
out-of-bounds index is UB even if its returned reference is unused.
[`debug_assert!`
configuration](https://doc.rust-lang.org/1.85.0/core/macro.debug_assert.html#uses),
[`slice::get_unchecked`
safety](https://doc.rust-lang.org/1.85.0/core/primitive.slice.html#method.get_unchecked).

### F-05 — `item_unchecked` ignores its `index`

**Status:** CONTRACT-BROKEN; its UB-freedom derivation closes under the
published safety precondition

The contract says the function returns `bytes[index]`, but the implementation
always reads index `0`.

For example, `unsafe { item_unchecked(&[0x10, 0x20], 1) }` satisfies
`index < bytes.len()` but returns `0x10` rather than `0x20`.

The safety precondition implies the slice is nonempty, so index `0` is in
bounds; no UB counterexample was established for contract-satisfying calls.

### F-06 — Missing or invalid local safety proofs

**Status:** UNPROVED proof artifact; not an additional UB witness

Five unsafe blocks have no adjacent `SAFETY` derivation. The sole comment
argues that because `u8` occupies one byte, every `[u8]` has an element. That
proposition is false and does not prove the bounds obligation.

`checked_first` itself has a valid independent derivation: reaching the
unchecked access means `is_empty()` returned false, so the length is nonzero
and index `0` is in bounds.
[`slice::is_empty`](https://doc.rust-lang.org/1.85.0/core/primitive.slice.html#method.is_empty),
[`slice::get_unchecked`](https://doc.rust-lang.org/1.85.0/core/primitive.slice.html#method.get_unchecked).

## Boundary and obligation coverage

| Public surface | Boundary | Result |
|---|---|---|
| `decode_flag(u8) -> bool` | Safe function | UNSOUND (`F-01`) |
| `AddressSource::address` | Caller-implementable safe trait method | Unenforced pointer invariant (`F-02`) |
| `load_source` | Safe generic function | UNSOUND (`F-02`) |
| `ByteHandle` and public `address` field | Safe literal construction/replacement | Unowned invariant (`F-03`) |
| `ByteHandle::load` | Safe method | UNSOUND (`F-03`) |
| `item_unchecked` | Unsafe function | UB obligation closes under `index < len`; CONTRACT-BROKEN (`F-05`) |
| Macro-generated `profile_index` | Safe function | UNSOUND when assertions are disabled (`F-04`) |
| `checked_first` | Safe function | Source derivation closes; local proof invalid (`F-06`) |

There are no other files, reexports, hidden APIs, dependencies, custom `Drop`
implementations, unsafe traits/impls, FFI, assembly, allocators, or concurrency
surfaces. The declarative macro is private but its single expansion creates the
public `profile_index` API.

## Configuration closure

`Supported(c)` is Rust/compiler/core/std 1.85.0, edition 2021, every Rust 1.85
target on which this dependency-free library is accepted, every ordinary build
profile, `debug_assertions ∈ {true, false}`, and no Cargo features or
dependency-feature axes.

The pointer, validity, and `item_unchecked` findings are
target/profile-parametric. F-04 specifically covers every supported
configuration with debug assertions disabled. Panic strategy does not repair
it.

## TCB audit log

Consumed entries are only the exact Rust 1.85 official propositions linked
above:

- boolean representation and validity;
- `transmute` source/destination validity;
- raw-pointer read validity, alignment, and initialization;
- null and dangling pointer rules;
- `NonNull::dangling`;
- `slice::get_unchecked`;
- `slice::is_empty`;
- `debug_assert!` configuration behavior; and
- unsafe-trait boundary semantics.

Each citation was opened at its exact version and verified. There are no
dependency, external-specification, implementation, deployment, probabilistic,
or tool assumptions. No independent human TCB acceptance was performed, so
this report issues no positive whole-crate `PROVED` certification; that
limitation does not weaken the concrete **UNSOUND** and
**CONTRACT-BROKEN** counterexamples.

## Residual scope and re-audit triggers

This is a source-level Rust abstract-semantics audit, not a
backend/binary/security audit. Re-audit after any source or public-contract
change, support-policy expansion, Rust/toolchain change, macro change,
dependency introduction, or authoritative-documentation change.
