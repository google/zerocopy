# Elain

Set the minimum alignments of types using const generics, rather
than `#[repr(align(N))]`.

## Basic Use
The type [`Align<N>`](Align) is a zero-sized-type with alignment
equal to `N`:
```rust
use elain::Align;
use core::mem::{align_of, align_of_val};

assert_eq!(align_of::<Align<1>>(), 1);
assert_eq!(align_of::<Align<2>>(), 2);
assert_eq!(align_of::<Align<4>>(), 4);

const FOO_ALIGN: usize = 8;

#[repr(C)]
struct Foo {
    _align: Align<FOO_ALIGN>,
}

let foo: Foo = Foo { _align: Align::NEW };

assert_eq!(align_of_val(&foo), 8);
```

Valid alignments are powers of two less-than-or-equal to 2<sup>28</sup>.
Supplying an *invalid* alignment to [`Align`] is a type error:
```rust
use elain::Align;

struct Foo(Align<3>); // Compile Error
```

## Generic Use
Because only *some* integers are valid alignments, supplying the
alignment of a type generically requires some extra work:
```rust
use elain::Align;

struct Foo<const N: usize> {
    _align: Align<N>,
}
```
To resolve this error, add a `where` bound like so, using the
[`Alignment`] trait to check that `Align<N>` is valid.

```rust
use elain::{Align, Alignment};
use core::mem::align_of;

struct Foo<const MIN_ALIGNMENT: usize>
where
    Align<MIN_ALIGNMENT>: Alignment
{
    _align: Align<MIN_ALIGNMENT>,
    bar: u8,
    baz: u16,
}

assert_eq!(align_of::<Foo<1>>(), 2);
assert_eq!(align_of::<Foo<2>>(), 2);
assert_eq!(align_of::<Foo<4>>(), 4);
``` 