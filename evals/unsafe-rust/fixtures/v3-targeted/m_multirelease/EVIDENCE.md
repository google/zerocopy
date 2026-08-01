# Submitted evidence and applicability

## `acknowledge`

The submitted source material for this claim is its exact empty body. No
Rust-version-specific library page is submitted. `TCB.md` contains accepted
entry `SEM-EMPTY-BLOCK-180-182`.

## `store_word`

The submitted authorities are:

- [`std::ptr::write`, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html):
  the description says that `write` overwrites without reading or dropping the
  old value, and its Safety section requires `dst` to be valid for writes and
  properly aligned.
- [`std::ptr::write`, Rust 1.81.0](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html):
  the same description and Safety propositions apply to the 1.81.0 case.

## `copy_byte`

The submitted authorities are:

- [`std::ptr::copy_nonoverlapping`, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html):
  its description says that it copies `count * size_of::<T>()` bytes and does
  not permit overlap. Its Safety section requires the source and destination
  regions to be valid for the corresponding read and write, both pointers to
  be properly aligned, and the regions not to overlap. For `T = u8` and
  `count = 1`, these are the exact caller-side clauses in `lib.rs`.
- [Rust 1.80.0 primitive data layout](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout):
  `u8` has size 1.
- [`u8: Copy`, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8):
  `u8` implements `Copy`.
- [`Copy` semantics, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html):
  values of a `Copy` type are duplicated by a simple bitwise copy rather than
  moved.

`TCB.md` contains accepted entry `COMPAT-COPY-180-182`.

## `load_word`

The submitted authorities are:

- [`std::ptr::read`, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html):
  the description says that `read` reads without moving and leaves the source
  unchanged. Its Safety section requires a non-ZST source to be valid for
  reads, properly aligned, and properly initialized.
- [`std::ptr::read`, Rust 1.82.0](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html):
  the same description and Safety propositions are supplied for the 1.82.0
  case.
- [`u32: Copy`, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32):
  `u32` implements `Copy` in the 1.80.0 endpoint case.
- [`Copy` semantics, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html):
  the corresponding copy rather than move semantics apply at that endpoint.
- [`u32: Copy`, Rust 1.82.0](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32):
  `u32` implements `Copy` in the 1.82.0 endpoint case.
- [`Copy` semantics, Rust 1.82.0](https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html):
  the corresponding copy rather than move semantics apply at that endpoint.

These are all submitted authorities and TCB entries for `load_word`.
