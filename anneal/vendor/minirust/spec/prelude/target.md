# MiniRust target specification

Some properties of the semantics are defined by the target.
Generally MiniRust programs are not portable to other targets, in particular, the size of a type and hence well-formedness is target-dependent.

We are using a trait with constants here because Rust has good support for parameterizing a block of code with a trait, less so with a value.

```rust
pub trait Target {
    /// The size and align of a pointer.
    const PTR_SIZE: Size;
    const PTR_ALIGN: Align;

    /// The maximum alignment of integer types.
    /// Smaller types are aligned to their size.
    const INT_MAX_ALIGN: Align;

    /// The endianess used for encoding multi-byte integer values (and pointers).
    const ENDIANNESS: Endianness;

    /// Maximum size of an atomic operation.
    const MAX_ATOMIC_SIZE: Size;

    /// Checks that `size` is not too large for this target.
    fn valid_size(size: Size) -> bool;
}
```

Here's an example target, mostly used for testing:

```rust
#[allow(non_camel_case_types)]
pub struct x86_64;

impl Target for x86_64 {
    const PTR_SIZE: Size = Size::from_bits_const(64).unwrap();
    const PTR_ALIGN: Align = Align::from_bits_const(64).unwrap();
    const INT_MAX_ALIGN: Align = Align::from_bits_const(128).unwrap();
    const ENDIANNESS: Endianness = LittleEndian;

    const MAX_ATOMIC_SIZE: Size = Size::from_bits_const(64).unwrap();

    fn valid_size(size: Size) -> bool {
        size.bytes().in_bounds(Signed, Self::PTR_SIZE)
    }
}
```
