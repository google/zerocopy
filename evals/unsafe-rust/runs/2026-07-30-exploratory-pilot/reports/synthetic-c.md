# Audit report

Source-only review; no target code was built, tested, modified, or executed.

## High — `decode_flag` creates invalid `bool` values from safe code

`decode_flag(2)` is a safe call, but `transmute` produces a `bool` with an
invalid bit pattern. Rust 1.85 permits only `0x00` and `0x01`; any other
pattern is undefined behavior.

Replace the transmute with explicit decoding, returning `Option`/`Result` for
invalid inputs or using `raw != 0` if all nonzero values intentionally mean
true.

Reference: [Rust 1.85 Boolean
representation](https://doc.rust-lang.org/1.85.0/reference/types/boolean.html#representation)

## High — `profile_index` relies on a removable assertion for memory safety

The public safe function checks bounds only with `debug_assert!`, then calls
`get_unchecked`. With debug assertions disabled—explicitly supported by
`SUPPORT.md`—a safe call such as `profile_index(&[], 0)` performs an
out-of-bounds unchecked access and causes undefined behavior.

Use ordinary indexing, `get`, or an unconditional `assert!` before
`get_unchecked`.

References: [Rust 1.85
`debug_assert!`](https://doc.rust-lang.org/1.85.0/std/macro.debug_assert.html),
[Rust 1.85
`slice::get_unchecked`](https://doc.rust-lang.org/1.85.0/std/primitive.slice.html#method.get_unchecked)

## High — Safe `AddressSource` implementations can make `load_source`
dereference arbitrary pointers

`AddressSource::address` has no safety contract and can be implemented entirely
in safe code to return null, dangling, uninitialized, or otherwise unreadable
memory. `load_source` then dereferences that pointer from a safe API.

Prefer returning `&u8`. Otherwise, make the implementation invariant explicit
through an `unsafe trait` or make `load_source` unsafe with a complete validity,
lifetime, initialization, and concurrency contract.

Reference: [Rust 1.85 `ptr::read` safety
requirements](https://doc.rust-lang.org/1.85.0/std/ptr/fn.read.html#safety)

## High — Public `ByteHandle` construction does not establish the invariant
required by `load`

`NonNull<u8>` guarantees non-nullness, not that the pointer is live,
initialized, or readable. Because the field is public, this entirely safe
expression creates a handle whose safe `load` causes undefined behavior:

```rust
ByteHandle {
    address: NonNull::dangling(),
}.load();
```

Encode the lifetime with `&'a u8`, or make the field private and provide an
unsafe constructor with documented invariants. Making `load` unsafe is another,
less ergonomic option.

References: [Rust 1.85
`NonNull::dangling`](https://doc.rust-lang.org/1.85.0/std/ptr/struct.NonNull.html#method.dangling),
[Rust 1.85
`ptr::read`](https://doc.rust-lang.org/1.85.0/std/ptr/fn.read.html#safety)

## Medium — `item_unchecked` ignores its requested index

The contract says the function returns `bytes[index]`, but it always accesses
index zero. For example, valid input `([10, 20], 1)` returns `10`, not `20`.
The stated precondition guarantees the slice is nonempty, so this is a
correctness failure rather than additional undefined behavior.

Use `bytes.get_unchecked(index)`.

## Informational — Misleading safety rationale

`checked_first` is currently sound because the preceding empty-slice branch
establishes `0 < bytes.len()`. Its safety comment is nevertheless false:
element size does not imply every slice contains an element. The comment should
cite the preceding emptiness check to prevent future maintenance mistakes.
