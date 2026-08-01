# Submitted evidence and applicability

## `acknowledge`

The submitted material for this claim is its exact empty body. It has no
statements, calls, unsafe blocks, raw-pointer accesses, or state transitions.
No Rust-version-specific library proposition is submitted for this claim. The
semantic bridge from that syntactic fact to the multi-release claim is exactly
accepted entry `SEM-EMPTY-BLOCK-180-182` in `TCB.md`.

## `store_word`

The submitted authorities form two exact applicable cases:

- [`std::ptr::write`, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html):
  the description says that `write` overwrites without reading or dropping the
  old value, and its Safety section requires `dst` to be valid for writes and
  properly aligned.
- [`std::ptr::write`, Rust 1.81.0](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html):
  the same description and Safety propositions apply to the 1.81.0 case.

No compatibility premise is needed or supplied for this two-member domain.

## `copy_byte`

One exact base authority is supplied:

- [`std::ptr::copy_nonoverlapping`, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html):
  its description says that it copies `count * size_of::<T>()` bytes and does
  not permit overlap. Its Safety section requires the source and destination
  regions to be valid for the corresponding read and write, both pointers to
  be properly aligned, and the regions not to overlap. For `T = u8` and
  `count = 1`, these are the exact caller-side clauses in `lib.rs`.
- [Rust 1.80.0 primitive data layout](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout):
  `u8` has size and alignment 1.
- [`u8: Copy`, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8):
  `u8` implements `Copy`.

The applicability of this authority beyond 1.80.0 is only the exact accepted
compatibility proposition in `TCB.md`; no stability badge or sampled later
page is submitted.

## `load_word`

Only the two endpoint authorities are supplied:

- [`std::ptr::read`, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html):
  the description says that `read` reads without moving and leaves the source
  unchanged. Its Safety section requires a non-ZST source to be valid for
  reads, properly aligned, and properly initialized.
- [`std::ptr::read`, Rust 1.82.0](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html):
  the same description and Safety propositions are supplied for the 1.82.0
  case.
- [`u32: Copy`, Rust 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32):
  `u32` implements `Copy` in the 1.80.0 endpoint case.
- [`u32: Copy`, Rust 1.82.0](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32):
  `u32` implements `Copy` in the 1.82.0 endpoint case.

No `ptr::read` authority for 1.80.1 or 1.81.0, compatibility premise, semantic
continuity theorem, or exhaustive interior partition is supplied. Evidence for
`ptr::write`, `copy_nonoverlapping`, or the empty `acknowledge` body establishes
no proposition about `ptr::read` on those two releases.
