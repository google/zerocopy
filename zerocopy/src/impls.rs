// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2024 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use core::{
    cell::{Cell, UnsafeCell},
    mem::MaybeUninit as CoreMaybeUninit,
    ptr::NonNull,
};

use super::*;
use crate::pointer::cast::{CastSizedExact, CastUnsized};

// SAFETY: Per the reference [1], "the unit tuple (`()`) ... is guaranteed as a
// zero-sized type to have a size of 0 and an alignment of 1."
// - `Immutable`: `()` self-evidently does not contain any `UnsafeCell`s.
// - `TryFromBytes` (with no validator), `FromZeros`, `FromBytes`: There is only
//   one possible sequence of 0 bytes, and `()` is inhabited.
// - `IntoBytes`: Since `()` has size 0, it contains no padding bytes.
// - `Unaligned`: `()` has alignment 1.
//
// [1] https://doc.rust-lang.org/1.81.0/reference/type-layout.html#tuple-layout
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    unsafe_impl!((): Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
    assert_unaligned!(());
};

// SAFETY:
// - `Immutable`: These types self-evidently do not contain any `UnsafeCell`s.
// - `TryFromBytes` (with no validator), `FromZeros`, `FromBytes`: all bit
//   patterns are valid for numeric types [1]
// - `IntoBytes`: numeric types have no padding bytes [1]
// - `Unaligned` (`u8` and `i8` only): The reference [2] specifies the size of
//   `u8` and `i8` as 1 byte. We also know that:
//   - Alignment is >= 1 [3]
//   - Size is an integer multiple of alignment [4]
//   - The only value >= 1 for which 1 is an integer multiple is 1 Therefore,
//   the only possible alignment for `u8` and `i8` is 1.
//
// [1] Per https://doc.rust-lang.org/1.81.0/reference/types/numeric.html#bit-validity:
//
//     For every numeric type, `T`, the bit validity of `T` is equivalent to
//     the bit validity of `[u8; size_of::<T>()]`. An uninitialized byte is
//     not a valid `u8`.
//
// [2] https://doc.rust-lang.org/1.81.0/reference/type-layout.html#primitive-data-layout
//
// [3] Per https://doc.rust-lang.org/1.81.0/reference/type-layout.html#size-and-alignment:
//
//     Alignment is measured in bytes, and must be at least 1.
//
// [4] Per https://doc.rust-lang.org/1.81.0/reference/type-layout.html#size-and-alignment:
//
//     The size of a value is always a multiple of its alignment.
//
// FIXME(#278): Once we've updated the trait docs to refer to `u8`s rather than
// bits or bytes, update this comment, especially the reference to [1].
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    unsafe_impl!(u8: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
    unsafe_impl!(i8: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
    assert_unaligned!(u8, i8);
    unsafe_impl!(u16: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(i16: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(u32: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(i32: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(u64: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(i64: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(u128: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(i128: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(usize: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(isize: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(f32: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(f64: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    #[cfg(feature = "float-nightly")]
    unsafe_impl!(#[cfg_attr(doc_cfg, doc(cfg(feature = "float-nightly")))] f16: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
    #[cfg(feature = "float-nightly")]
    unsafe_impl!(#[cfg_attr(doc_cfg, doc(cfg(feature = "float-nightly")))] f128: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes);
};

// SAFETY:
// - `Immutable`: `bool` self-evidently does not contain any `UnsafeCell`s.
// - `FromZeros`: Valid since "[t]he value false has the bit pattern 0x00" [1].
// - `IntoBytes`: Since "the boolean type has a size and alignment of 1 each"
//   and "The value false has the bit pattern 0x00 and the value true has the
//   bit pattern 0x01" [1]. Thus, the only byte of the bool is always
//   initialized.
// - `Unaligned`: Per the reference [1], "[a]n object with the boolean type has
//   a size and alignment of 1 each."
//
// [1] https://doc.rust-lang.org/1.81.0/reference/types/boolean.html
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe { unsafe_impl!(bool: Immutable, FromZeros, IntoBytes, Unaligned) };
assert_unaligned!(bool);

// SAFETY: The impl must only return `true` for its argument if the original
// `Maybe<bool>` refers to a valid `bool`. We only return true if the `u8` value
// is 0 or 1, and both of these are valid values for `bool` [1].
//
// [1] Per https://doc.rust-lang.org/1.81.0/reference/types/boolean.html:
//
//   The value false has the bit pattern 0x00 and the value true has the bit
//   pattern 0x01.
const _: () = unsafe {
    unsafe_impl!(=> TryFromBytes for bool; |byte| {
        let byte = byte.transmute_with::<u8, invariant::Valid, CastSizedExact, BecauseImmutable>();
        *byte.unaligned_as_ref() < 2
    })
};

// SAFETY:
// - `Immutable`: `char` self-evidently does not contain any `UnsafeCell`s.
// - `FromZeros`: Per reference [1], "[a] value of type char is a Unicode scalar
//   value (i.e. a code point that is not a surrogate), represented as a 32-bit
//   unsigned word in the 0x0000 to 0xD7FF or 0xE000 to 0x10FFFF range" which
//   contains 0x0000.
// - `IntoBytes`: `char` is per reference [1] "represented as a 32-bit unsigned
//   word" (`u32`) which is `IntoBytes`. Note that unlike `u32`, not all bit
//   patterns are valid for `char`.
//
// [1] https://doc.rust-lang.org/1.81.0/reference/types/textual.html
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe { unsafe_impl!(char: Immutable, FromZeros, IntoBytes) };

// SAFETY: The impl must only return `true` for its argument if the original
// `Maybe<char>` refers to a valid `char`. `char::from_u32` guarantees that it
// returns `None` if its input is not a valid `char` [1].
//
// [1] Per https://doc.rust-lang.org/core/primitive.char.html#method.from_u32:
//
//   `from_u32()` will return `None` if the input is not a valid value for a
//   `char`.
const _: () = unsafe {
    unsafe_impl!(=> TryFromBytes for char; |c| {
        let c = c.transmute_with::<Unalign<u32>, invariant::Valid, CastSizedExact, BecauseImmutable>();
        let c = c.read().into_inner();
        char::from_u32(c).is_some()
    });
};

// SAFETY: Per the Reference [1], `str` has the same layout as `[u8]`.
// - `Immutable`: `[u8]` does not contain any `UnsafeCell`s.
// - `FromZeros`, `IntoBytes`, `Unaligned`: `[u8]` is `FromZeros`, `IntoBytes`,
//   and `Unaligned`.
//
// Note that we don't `assert_unaligned!(str)` because `assert_unaligned!` uses
// `align_of`, which only works for `Sized` types.
//
// FIXME(#429): Improve safety proof for `FromZeros` and `IntoBytes`; having the same
// layout as `[u8]` isn't sufficient.
//
// [1] Per https://doc.rust-lang.org/1.81.0/reference/type-layout.html#str-layout:
//
//   String slices are a UTF-8 representation of characters that have the same
//   layout as slices of type `[u8]`.
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe { unsafe_impl!(str: Immutable, FromZeros, IntoBytes, Unaligned) };

// SAFETY: The impl must only return `true` for its argument if the original
// `Maybe<str>` refers to a valid `str`. `str::from_utf8` guarantees that it
// returns `Err` if its input is not a valid `str` [1].
//
// [1] Per https://doc.rust-lang.org/core/str/fn.from_utf8.html#errors:
//
//   Returns `Err` if the slice is not UTF-8.
const _: () = unsafe {
    unsafe_impl!(=> TryFromBytes for str; |c| {
        let c = c.transmute_with::<[u8], invariant::Valid, CastUnsized, BecauseImmutable>();
        let c = c.unaligned_as_ref();
        core::str::from_utf8(c).is_ok()
    })
};

macro_rules! unsafe_impl_try_from_bytes_for_nonzero {
    ($($nonzero:ident[$prim:ty]),*) => {
        $(
            unsafe_impl!(=> TryFromBytes for $nonzero; |n| {
                let n = n.transmute_with::<Unalign<$prim>, invariant::Valid, CastSizedExact, BecauseImmutable>();
                $nonzero::new(n.read().into_inner()).is_some()
            });
        )*
    }
}

// `NonZeroXxx` is `IntoBytes`, but not `FromZeros` or `FromBytes`.
//
// SAFETY:
// - `IntoBytes`: `NonZeroXxx` has the same layout as its associated primitive.
//    Since it is the same size, this guarantees it has no padding - integers
//    have no padding, and there's no room for padding if it can represent all
//    of the same values except 0.
// - `Unaligned`: `NonZeroU8` and `NonZeroI8` document that `Option<NonZeroU8>`
//   and `Option<NonZeroI8>` both have size 1. [1] [2] This is worded in a way
//   that makes it unclear whether it's meant as a guarantee, but given the
//   purpose of those types, it's virtually unthinkable that that would ever
//   change. `Option` cannot be smaller than its contained type, which implies
//   that, and `NonZeroX8` are of size 1 or 0. `NonZeroX8` can represent
//   multiple states, so they cannot be 0 bytes, which means that they must be 1
//   byte. The only valid alignment for a 1-byte type is 1.
//
// FIXME(#429):
// - Add quotes from documentation.
// - Add safety comment for `Immutable`. How can we prove that `NonZeroXxx`
//   doesn't contain any `UnsafeCell`s? It's obviously true, but it's not clear
//   how we'd prove it short of adding text to the stdlib docs that says so
//   explicitly, which likely wouldn't be accepted.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/num/type.NonZeroU8.html:
//
//     `NonZeroU8` is guaranteed to have the same layout and bit validity as `u8` with
//     the exception that 0 is not a valid instance.
//
// [2] Per https://doc.rust-lang.org/1.81.0/std/num/type.NonZeroI8.html:
//
//     `NonZeroI8` is guaranteed to have the same layout and bit validity as `i8` with
//     the exception that 0 is not a valid instance.
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    unsafe_impl!(NonZeroU8: Immutable, IntoBytes, Unaligned);
    unsafe_impl!(NonZeroI8: Immutable, IntoBytes, Unaligned);
    assert_unaligned!(NonZeroU8, NonZeroI8);
    unsafe_impl!(NonZeroU16: Immutable, IntoBytes);
    unsafe_impl!(NonZeroI16: Immutable, IntoBytes);
    unsafe_impl!(NonZeroU32: Immutable, IntoBytes);
    unsafe_impl!(NonZeroI32: Immutable, IntoBytes);
    unsafe_impl!(NonZeroU64: Immutable, IntoBytes);
    unsafe_impl!(NonZeroI64: Immutable, IntoBytes);
    unsafe_impl!(NonZeroU128: Immutable, IntoBytes);
    unsafe_impl!(NonZeroI128: Immutable, IntoBytes);
    unsafe_impl!(NonZeroUsize: Immutable, IntoBytes);
    unsafe_impl!(NonZeroIsize: Immutable, IntoBytes);
    unsafe_impl_try_from_bytes_for_nonzero!(
        NonZeroU8[u8],
        NonZeroI8[i8],
        NonZeroU16[u16],
        NonZeroI16[i16],
        NonZeroU32[u32],
        NonZeroI32[i32],
        NonZeroU64[u64],
        NonZeroI64[i64],
        NonZeroU128[u128],
        NonZeroI128[i128],
        NonZeroUsize[usize],
        NonZeroIsize[isize]
    );
};

// SAFETY:
// - `TryFromBytes` (with no validator), `FromZeros`, `FromBytes`, `IntoBytes`:
//   The Rust compiler reuses `0` value to represent `None`, so
//   `size_of::<Option<NonZeroXxx>>() == size_of::<xxx>()`; see `NonZeroXxx`
//   documentation.
// - `Unaligned`: `NonZeroU8` and `NonZeroI8` document that `Option<NonZeroU8>`
//   and `Option<NonZeroI8>` both have size 1. [1] [2] This is worded in a way
//   that makes it unclear whether it's meant as a guarantee, but given the
//   purpose of those types, it's virtually unthinkable that that would ever
//   change. The only valid alignment for a 1-byte type is 1.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/num/type.NonZeroU8.html:
//
//     `Option<NonZeroU8>` is guaranteed to be compatible with `u8`, including in FFI.
//
//     Thanks to the null pointer optimization, `NonZeroU8` and `Option<NonZeroU8>`
//     are guaranteed to have the same size and alignment:
//
// [2] Per https://doc.rust-lang.org/1.81.0/std/num/type.NonZeroI8.html:
//
//     `Option<NonZeroI8>` is guaranteed to be compatible with `i8`, including in FFI.
//
//     Thanks to the null pointer optimization, `NonZeroI8` and `Option<NonZeroI8>`
//     are guaranteed to have the same size and alignment:
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    unsafe_impl!(Option<NonZeroU8>: TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
    unsafe_impl!(Option<NonZeroI8>: TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
    assert_unaligned!(Option<NonZeroU8>, Option<NonZeroI8>);
    unsafe_impl!(Option<NonZeroU16>: TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(Option<NonZeroI16>: TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(Option<NonZeroU32>: TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(Option<NonZeroI32>: TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(Option<NonZeroU64>: TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(Option<NonZeroI64>: TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(Option<NonZeroU128>: TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(Option<NonZeroI128>: TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(Option<NonZeroUsize>: TryFromBytes, FromZeros, FromBytes, IntoBytes);
    unsafe_impl!(Option<NonZeroIsize>: TryFromBytes, FromZeros, FromBytes, IntoBytes);
};

// SAFETY: While it's not fully documented, the consensus is that `Box<T>` does
// not contain any `UnsafeCell`s for `T: Sized` [1]. This is not a complete
// proof, but we are accepting this as a known risk per #1358.
//
// [1] https://github.com/rust-lang/unsafe-code-guidelines/issues/492
#[cfg(feature = "alloc")]
const _: () = unsafe {
    unsafe_impl!(
        #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
        T: Sized => Immutable for Box<T>
    )
};

// SAFETY: The following types can be transmuted from `[0u8; size_of::<T>()]`. [1]
//
// [1] Per https://doc.rust-lang.org/1.89.0/core/option/index.html#representation:
//
//   Rust guarantees to optimize the following types `T` such that [`Option<T>`]
//   has the same size and alignment as `T`. In some of these cases, Rust
//   further guarantees that `transmute::<_, Option<T>>([0u8; size_of::<T>()])`
//   is sound and produces `Option::<T>::None`. These cases are identified by
//   the second column:
//
//   | `T`                               | `transmute::<_, Option<T>>([0u8; size_of::<T>()])` sound? |
//   |-----------------------------------|-----------------------------------------------------------|
//   | [`Box<U>`]                        | when `U: Sized`                                           |
//   | `&U`                              | when `U: Sized`                                           |
//   | `&mut U`                          | when `U: Sized`                                           |
//   | [`ptr::NonNull<U>`]               | when `U: Sized`                                           |
//   | `fn`, `extern "C" fn`[^extern_fn] | always                                                    |
//
//   [^extern_fn]: this remains true for `unsafe` variants, any argument/return
//     types, and any other ABI: `[unsafe] extern "abi" fn` (_e.g._, `extern
//     "system" fn`)
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    #[cfg(feature = "alloc")]
    unsafe_impl!(
        #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
        T => TryFromBytes for Option<Box<T>>; |c| pointer::is_zeroed(c)
    );
    #[cfg(feature = "alloc")]
    unsafe_impl!(
        #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
        T => FromZeros for Option<Box<T>>
    );
    unsafe_impl!(
        T => TryFromBytes for Option<&'_ T>; |c| pointer::is_zeroed(c)
    );
    unsafe_impl!(T => FromZeros for Option<&'_ T>);
    unsafe_impl!(
            T => TryFromBytes for Option<&'_ mut T>; |c| pointer::is_zeroed(c)
    );
    unsafe_impl!(T => FromZeros for Option<&'_ mut T>);
    unsafe_impl!(
        T => TryFromBytes for Option<NonNull<T>>; |c| pointer::is_zeroed(c)
    );
    unsafe_impl!(T => FromZeros for Option<NonNull<T>>);
    unsafe_impl_for_power_set!(A, B, C, D, E, F, G, H, I, J, K, L -> M => FromZeros for opt_fn!(...));
    unsafe_impl_for_power_set!(
        A, B, C, D, E, F, G, H, I, J, K, L -> M => TryFromBytes for opt_fn!(...);
        |c| pointer::is_zeroed(c)
    );
    unsafe_impl_for_power_set!(A, B, C, D, E, F, G, H, I, J, K, L -> M => FromZeros for opt_unsafe_fn!(...));
    unsafe_impl_for_power_set!(
        A, B, C, D, E, F, G, H, I, J, K, L -> M => TryFromBytes for opt_unsafe_fn!(...);
        |c| pointer::is_zeroed(c)
    );
    unsafe_impl_for_power_set!(A, B, C, D, E, F, G, H, I, J, K, L -> M => FromZeros for opt_extern_c_fn!(...));
    unsafe_impl_for_power_set!(
        A, B, C, D, E, F, G, H, I, J, K, L -> M => TryFromBytes for opt_extern_c_fn!(...);
        |c| pointer::is_zeroed(c)
    );
    unsafe_impl_for_power_set!(A, B, C, D, E, F, G, H, I, J, K, L -> M => FromZeros for opt_unsafe_extern_c_fn!(...));
    unsafe_impl_for_power_set!(
        A, B, C, D, E, F, G, H, I, J, K, L -> M => TryFromBytes for opt_unsafe_extern_c_fn!(...);
        |c| pointer::is_zeroed(c)
    );
};

// SAFETY: `[unsafe] [extern "C"] fn()` self-evidently do not contain
// `UnsafeCell`s. This is not a proof, but we are accepting this as a known risk
// per #1358.
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    unsafe_impl_for_power_set!(A, B, C, D, E, F, G, H, I, J, K, L -> M => Immutable for opt_fn!(...));
    unsafe_impl_for_power_set!(A, B, C, D, E, F, G, H, I, J, K, L -> M => Immutable for opt_unsafe_fn!(...));
    unsafe_impl_for_power_set!(A, B, C, D, E, F, G, H, I, J, K, L -> M => Immutable for opt_extern_c_fn!(...));
    unsafe_impl_for_power_set!(A, B, C, D, E, F, G, H, I, J, K, L -> M => Immutable for opt_unsafe_extern_c_fn!(...));
};

#[cfg(all(
    not(no_zerocopy_target_has_atomics_1_60_0),
    any(
        target_has_atomic = "8",
        target_has_atomic = "16",
        target_has_atomic = "32",
        target_has_atomic = "64",
        target_has_atomic = "ptr"
    )
))]
#[cfg_attr(doc_cfg, doc(cfg(rust = "1.60.0")))]
mod atomics {
    use super::*;

    macro_rules! impl_traits_for_atomics {
        ($($atomics:tt [$primitives:ty]),* $(,)?) => {
            $(
                impl_known_layout!($atomics);
                impl_for_transmute_from!(=> FromZeros for $atomics [$primitives]);
                impl_for_transmute_from!(=> FromBytes for $atomics [$primitives]);
                impl_for_transmute_from!(=> TryFromBytes for $atomics [$primitives]);
                impl_for_transmute_from!(=> IntoBytes for $atomics [$primitives]);
            )*
        };
    }

    /// Implements `TransmuteFrom` for `$atomic`, `$prim`, and
    /// `UnsafeCell<$prim>`.
    ///
    /// # Safety
    ///
    /// `$atomic` must have the same size and bit validity as `$prim`.
    macro_rules! unsafe_impl_transmute_from_for_atomic {
        ($($($tyvar:ident)? => $atomic:ty [$prim:ty]),*) => {{
            crate::util::macros::__unsafe();

            use crate::pointer::{SizeEq, TransmuteFrom, invariant::Valid};

            $(
                // SAFETY: The caller promised that `$atomic` and `$prim` have
                // the same size and bit validity.
                unsafe impl<$($tyvar)?> TransmuteFrom<$atomic, Valid, Valid> for $prim {}
                // SAFETY: The caller promised that `$atomic` and `$prim` have
                // the same size and bit validity.
                unsafe impl<$($tyvar)?> TransmuteFrom<$prim, Valid, Valid> for $atomic {}

                impl<$($tyvar)?> SizeEq<ReadOnly<$atomic>> for ReadOnly<$prim> {
                    type CastFrom = $crate::pointer::cast::CastSizedExact;
                }

                // SAFETY: The caller promised that `$atomic` and `$prim` have
                // the same bit validity. `UnsafeCell<T>` has the same bit
                // validity as `T` [1].
                //
                // [1] Per https://doc.rust-lang.org/1.85.0/std/cell/struct.UnsafeCell.html#memory-layout:
                //
                //   `UnsafeCell<T>` has the same in-memory representation as
                //   its inner type `T`. A consequence of this guarantee is that
                //   it is possible to convert between `T` and `UnsafeCell<T>`.
                unsafe impl<$($tyvar)?> TransmuteFrom<$atomic, Valid, Valid> for core::cell::UnsafeCell<$prim> {}
                // SAFETY: See previous safety comment.
                unsafe impl<$($tyvar)?> TransmuteFrom<core::cell::UnsafeCell<$prim>, Valid, Valid> for $atomic {}
            )*
        }};
    }

    #[cfg(target_has_atomic = "8")]
    #[cfg_attr(doc_cfg, doc(cfg(target_has_atomic = "8")))]
    mod atomic_8 {
        use core::sync::atomic::{AtomicBool, AtomicI8, AtomicU8};

        use super::*;

        impl_traits_for_atomics!(AtomicU8[u8], AtomicI8[i8]);

        impl_known_layout!(AtomicBool);
        impl_for_transmute_from!(=> FromZeros for AtomicBool [bool]);
        impl_for_transmute_from!(=> TryFromBytes for AtomicBool [bool]);
        impl_for_transmute_from!(=> IntoBytes for AtomicBool [bool]);

        // SAFETY: Per [1], `AtomicBool`, `AtomicU8`, and `AtomicI8` have the
        // same size as `bool`, `u8`, and `i8` respectively. Since a type's
        // alignment cannot be smaller than 1 [2], and since its alignment
        // cannot be greater than its size [3], the only possible value for the
        // alignment is 1. Thus, it is sound to implement `Unaligned`.
        //
        // [1] Per (for example) https://doc.rust-lang.org/1.81.0/std/sync/atomic/struct.AtomicU8.html:
        //
        //   This type has the same size, alignment, and bit validity as the
        //   underlying integer type
        //
        // [2] Per https://doc.rust-lang.org/1.81.0/reference/type-layout.html#size-and-alignment:
        //
        //     Alignment is measured in bytes, and must be at least 1.
        //
        // [3] Per https://doc.rust-lang.org/1.81.0/reference/type-layout.html#size-and-alignment:
        //
        //     The size of a value is always a multiple of its alignment.
        #[allow(clippy::multiple_unsafe_ops_per_block)]
        const _: () = unsafe {
            unsafe_impl!(AtomicBool: Unaligned);
            unsafe_impl!(AtomicU8: Unaligned);
            unsafe_impl!(AtomicI8: Unaligned);
            assert_unaligned!(AtomicBool, AtomicU8, AtomicI8);
        };

        // SAFETY: `AtomicU8`, `AtomicI8`, and `AtomicBool` have the same size
        // and bit validity as `u8`, `i8`, and `bool` respectively [1][2][3].
        //
        // [1] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU8.html:
        //
        //   This type has the same size, alignment, and bit validity as the
        //   underlying integer type, `u8`.
        //
        // [2] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI8.html:
        //
        //   This type has the same size, alignment, and bit validity as the
        //   underlying integer type, `i8`.
        //
        // [3] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicBool.html:
        //
        //   This type has the same size, alignment, and bit validity a `bool`.
        #[allow(clippy::multiple_unsafe_ops_per_block)]
        const _: () = unsafe {
            unsafe_impl_transmute_from_for_atomic!(
                => AtomicU8 [u8],
                => AtomicI8 [i8],
                => AtomicBool [bool]
            )
        };
    }

    #[cfg(target_has_atomic = "16")]
    #[cfg_attr(doc_cfg, doc(cfg(target_has_atomic = "16")))]
    mod atomic_16 {
        use core::sync::atomic::{AtomicI16, AtomicU16};

        use super::*;

        impl_traits_for_atomics!(AtomicU16[u16], AtomicI16[i16]);

        // SAFETY: `AtomicU16` and `AtomicI16` have the same size and bit
        // validity as `u16` and `i16` respectively [1][2].
        //
        // [1] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU16.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type, `u16`.
        //
        // [2] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI16.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type, `i16`.
        #[allow(clippy::multiple_unsafe_ops_per_block)]
        const _: () = unsafe {
            unsafe_impl_transmute_from_for_atomic!(=> AtomicU16 [u16], => AtomicI16 [i16])
        };
    }

    #[cfg(target_has_atomic = "32")]
    #[cfg_attr(doc_cfg, doc(cfg(target_has_atomic = "32")))]
    mod atomic_32 {
        use core::sync::atomic::{AtomicI32, AtomicU32};

        use super::*;

        impl_traits_for_atomics!(AtomicU32[u32], AtomicI32[i32]);

        // SAFETY: `AtomicU32` and `AtomicI32` have the same size and bit
        // validity as `u32` and `i32` respectively [1][2].
        //
        // [1] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU32.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type, `u32`.
        //
        // [2] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI32.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type, `i32`.
        #[allow(clippy::multiple_unsafe_ops_per_block)]
        const _: () = unsafe {
            unsafe_impl_transmute_from_for_atomic!(=> AtomicU32 [u32], => AtomicI32 [i32])
        };
    }

    #[cfg(target_has_atomic = "64")]
    #[cfg_attr(doc_cfg, doc(cfg(target_has_atomic = "64")))]
    mod atomic_64 {
        use core::sync::atomic::{AtomicI64, AtomicU64};

        use super::*;

        impl_traits_for_atomics!(AtomicU64[u64], AtomicI64[i64]);

        // SAFETY: `AtomicU64` and `AtomicI64` have the same size and bit
        // validity as `u64` and `i64` respectively [1][2].
        //
        // [1] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicU64.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type, `u64`.
        //
        // [2] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicI64.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type, `i64`.
        #[allow(clippy::multiple_unsafe_ops_per_block)]
        const _: () = unsafe {
            unsafe_impl_transmute_from_for_atomic!(=> AtomicU64 [u64], => AtomicI64 [i64])
        };
    }

    #[cfg(target_has_atomic = "ptr")]
    #[cfg_attr(doc_cfg, doc(cfg(target_has_atomic = "ptr")))]
    mod atomic_ptr {
        use core::sync::atomic::{AtomicIsize, AtomicPtr, AtomicUsize};

        use super::*;

        impl_traits_for_atomics!(AtomicUsize[usize], AtomicIsize[isize]);

        // FIXME(#170): Implement `FromBytes` and `IntoBytes` once we implement
        // those traits for `*mut T`.
        impl_known_layout!(T => AtomicPtr<T>);
        impl_for_transmute_from!(T => TryFromBytes for AtomicPtr<T> [*mut T]);
        impl_for_transmute_from!(T => FromZeros for AtomicPtr<T> [*mut T]);

        // SAFETY: `AtomicUsize` and `AtomicIsize` have the same size and bit
        // validity as `usize` and `isize` respectively [1][2].
        //
        // [1] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicUsize.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type, `usize`.
        //
        // [2] Per https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicIsize.html:
        //
        //   This type has the same size and bit validity as the underlying
        //   integer type, `isize`.
        #[allow(clippy::multiple_unsafe_ops_per_block)]
        const _: () = unsafe {
            unsafe_impl_transmute_from_for_atomic!(=> AtomicUsize [usize], => AtomicIsize [isize])
        };

        // SAFETY: Per
        // https://doc.rust-lang.org/1.85.0/std/sync/atomic/struct.AtomicPtr.html:
        //
        //   This type has the same size and bit validity as a `*mut T`.
        #[allow(clippy::multiple_unsafe_ops_per_block)]
        const _: () = unsafe { unsafe_impl_transmute_from_for_atomic!(T => AtomicPtr<T> [*mut T]) };
    }
}

// SAFETY: Per reference [1]: "For all T, the following are guaranteed:
// size_of::<PhantomData<T>>() == 0 align_of::<PhantomData<T>>() == 1". This
// gives:
// - `Immutable`: `PhantomData` has no fields.
// - `TryFromBytes` (with no validator), `FromZeros`, `FromBytes`: There is only
//   one possible sequence of 0 bytes, and `PhantomData` is inhabited.
// - `IntoBytes`: Since `PhantomData` has size 0, it contains no padding bytes.
// - `Unaligned`: Per the preceding reference, `PhantomData` has alignment 1.
//
// [1] https://doc.rust-lang.org/1.81.0/std/marker/struct.PhantomData.html#layout-1
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    unsafe_impl!(T: ?Sized => Immutable for PhantomData<T>);
    unsafe_impl!(T: ?Sized => TryFromBytes for PhantomData<T>);
    unsafe_impl!(T: ?Sized => FromZeros for PhantomData<T>);
    unsafe_impl!(T: ?Sized => FromBytes for PhantomData<T>);
    unsafe_impl!(T: ?Sized => IntoBytes for PhantomData<T>);
    unsafe_impl!(T: ?Sized => Unaligned for PhantomData<T>);
    assert_unaligned!(PhantomData<()>, PhantomData<u8>, PhantomData<u64>);
};

impl_for_transmute_from!(T: TryFromBytes => TryFromBytes for Wrapping<T>[T]);
impl_for_transmute_from!(T: FromZeros => FromZeros for Wrapping<T>[T]);
impl_for_transmute_from!(T: FromBytes => FromBytes for Wrapping<T>[T]);
impl_for_transmute_from!(T: IntoBytes => IntoBytes for Wrapping<T>[T]);
assert_unaligned!(Wrapping<()>, Wrapping<u8>);

// SAFETY: Per [1], `Wrapping<T>` has the same layout as `T`. Since its single
// field (of type `T`) is public, it would be a breaking change to add or remove
// fields. Thus, we know that `Wrapping<T>` contains a `T` (as opposed to just
// having the same size and alignment as `T`) with no pre- or post-padding.
// Thus, `Wrapping<T>` must have `UnsafeCell`s covering the same byte ranges as
// `Inner = T`.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/num/struct.Wrapping.html#layout-1:
//
//   `Wrapping<T>` is guaranteed to have the same layout and ABI as `T`
const _: () = unsafe { unsafe_impl!(T: Immutable => Immutable for Wrapping<T>) };

// SAFETY: Per [1] in the preceding safety comment, `Wrapping<T>` has the same
// alignment as `T`.
const _: () = unsafe { unsafe_impl!(T: Unaligned => Unaligned for Wrapping<T>) };

// SAFETY: `TryFromBytes` (with no validator), `FromZeros`, `FromBytes`:
// `MaybeUninit<T>` has no restrictions on its contents.
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    unsafe_impl!(T => TryFromBytes for CoreMaybeUninit<T>);
    unsafe_impl!(T => FromZeros for CoreMaybeUninit<T>);
    unsafe_impl!(T => FromBytes for CoreMaybeUninit<T>);
};

// SAFETY: `MaybeUninit<T>` has `UnsafeCell`s covering the same byte ranges as
// `Inner = T`. This is not explicitly documented, but it can be inferred. Per
// [1], `MaybeUninit<T>` has the same size as `T`. Further, note the signature
// of `MaybeUninit::assume_init_ref` [2]:
//
//   pub unsafe fn assume_init_ref(&self) -> &T
//
// If the argument `&MaybeUninit<T>` and the returned `&T` had `UnsafeCell`s at
// different offsets, this would be unsound. Its existence is proof that this is
// not the case.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#layout-1:
//
// `MaybeUninit<T>` is guaranteed to have the same size, alignment, and ABI as
// `T`.
//
// [2] https://doc.rust-lang.org/1.81.0/std/mem/union.MaybeUninit.html#method.assume_init_ref
const _: () = unsafe { unsafe_impl!(T: Immutable => Immutable for CoreMaybeUninit<T>) };

// SAFETY: Per [1] in the preceding safety comment, `MaybeUninit<T>` has the
// same alignment as `T`.
const _: () = unsafe { unsafe_impl!(T: Unaligned => Unaligned for CoreMaybeUninit<T>) };
assert_unaligned!(CoreMaybeUninit<()>, CoreMaybeUninit<u8>);

// SAFETY: `ManuallyDrop<T>` has the same layout as `T` [1]. This strongly
// implies, but does not guarantee, that it contains `UnsafeCell`s covering the
// same byte ranges as in `T`. However, it also implements `Defer<Target = T>`
// [2], which provides the ability to convert `&ManuallyDrop<T> -> &T`. This,
// combined with having the same size as `T`, implies that `ManuallyDrop<T>`
// exactly contains a `T` with the same fields and `UnsafeCell`s covering the
// same byte ranges, or else the `Deref` impl would permit safe code to obtain
// different shared references to the same region of memory with different
// `UnsafeCell` coverage, which would in turn permit interior mutation that
// would violate the invariants of a shared reference.
//
// [1] Per https://doc.rust-lang.org/1.85.0/std/mem/struct.ManuallyDrop.html:
//
//   `ManuallyDrop<T>` is guaranteed to have the same layout and bit validity as
//   `T`
//
// [2] https://doc.rust-lang.org/1.85.0/std/mem/struct.ManuallyDrop.html#impl-Deref-for-ManuallyDrop%3CT%3E
const _: () = unsafe { unsafe_impl!(T: ?Sized + Immutable => Immutable for ManuallyDrop<T>) };

impl_for_transmute_from!(T: ?Sized + TryFromBytes => TryFromBytes for ManuallyDrop<T>[T]);
impl_for_transmute_from!(T: ?Sized + FromZeros => FromZeros for ManuallyDrop<T>[T]);
impl_for_transmute_from!(T: ?Sized + FromBytes => FromBytes for ManuallyDrop<T>[T]);
impl_for_transmute_from!(T: ?Sized + IntoBytes => IntoBytes for ManuallyDrop<T>[T]);
// SAFETY: `ManuallyDrop<T>` has the same layout as `T` [1], and thus has the
// same alignment as `T`.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/mem/struct.ManuallyDrop.html:
//
//   `ManuallyDrop<T>` is guaranteed to have the same layout and bit validity as
//   `T`
const _: () = unsafe { unsafe_impl!(T: ?Sized + Unaligned => Unaligned for ManuallyDrop<T>) };
assert_unaligned!(ManuallyDrop<()>, ManuallyDrop<u8>);

const _: () = {
    #[allow(
        non_camel_case_types,
        missing_copy_implementations,
        missing_debug_implementations,
        missing_docs
    )]
    pub enum value {}

    // SAFETY: See safety comment on `ProjectToTag`.
    unsafe impl<T: ?Sized> HasTag for ManuallyDrop<T> {
        #[inline]
        fn only_derive_is_allowed_to_implement_this_trait()
        where
            Self: Sized,
        {
        }

        type Tag = ();

        // SAFETY: It is trivially sound to project any pointer to a pointer to
        // a type of size zero and alignment 1 (which `()` is [1]). Such a
        // pointer will trivially satisfy its aliasing and validity requirements
        // (since it has a zero-sized referent), and its alignment requirement
        // (since it is aligned to 1).
        //
        // [1] Per https://doc.rust-lang.org/1.92.0/reference/type-layout.html#r-layout.tuple.unit:
        //
        //     [T]he unit tuple (`()`)... is guaranteed as a zero-sized type to
        //     have a size of 0 and an alignment of 1.
        type ProjectToTag = crate::pointer::cast::CastToUnit;
    }

    // SAFETY: `ManuallyDrop<T>` has a field of type `T` at offset `0` without
    // any safety invariants beyond those of `T`.  Its existence is not
    // explicitly documented, but it can be inferred; per [1] `ManuallyDrop<T>`
    // has the same size and bit validity as `T`. This field is not literally
    // public, but is effectively so; the field can be transparently:
    //
    //  - initialized via `ManuallyDrop::new`
    //  - moved via `ManuallyDrop::into_inner`
    //  - referenced via `ManuallyDrop::deref`
    //  - exclusively referenced via `ManuallyDrop::deref_mut`
    //
    // We call this field `value`, both because that is both the name of this
    // private field, and because it is the name it is referred to in the public
    // documentation of `ManuallyDrop::new`, `ManuallyDrop::into_inner`,
    // `ManuallyDrop::take` and `ManuallyDrop::drop`.
    unsafe impl<T: ?Sized>
        HasField<value, { crate::STRUCT_VARIANT_ID }, { crate::ident_id!(value) }>
        for ManuallyDrop<T>
    {
        #[inline]
        fn only_derive_is_allowed_to_implement_this_trait()
        where
            Self: Sized,
        {
        }

        type Type = T;

        #[inline(always)]
        fn project(slf: PtrInner<'_, Self>) -> *mut T {
            // SAFETY: `ManuallyDrop<T>` has the same layout and bit validity as
            // `T` [1].
            //
            // [1] Per https://doc.rust-lang.org/1.85.0/std/mem/struct.ManuallyDrop.html:
            //
            //   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
            //   validity as `T`
            #[allow(clippy::as_conversions)]
            return slf.as_ptr() as *mut T;
        }
    }
};

impl_for_transmute_from!(T: ?Sized + TryFromBytes => TryFromBytes for Cell<T>[T]);
impl_for_transmute_from!(T: ?Sized + FromZeros => FromZeros for Cell<T>[T]);
impl_for_transmute_from!(T: ?Sized + FromBytes => FromBytes for Cell<T>[T]);
impl_for_transmute_from!(T: ?Sized + IntoBytes => IntoBytes for Cell<T>[T]);
// SAFETY: `Cell<T>` has the same in-memory representation as `T` [1], and thus
// has the same alignment as `T`.
//
// [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.Cell.html#memory-layout:
//
//   `Cell<T>` has the same in-memory representation as its inner type `T`.
const _: () = unsafe { unsafe_impl!(T: ?Sized + Unaligned => Unaligned for Cell<T>) };

impl_for_transmute_from!(T: ?Sized + FromZeros => FromZeros for UnsafeCell<T>[T]);
impl_for_transmute_from!(T: ?Sized + FromBytes => FromBytes for UnsafeCell<T>[T]);
impl_for_transmute_from!(T: ?Sized + IntoBytes => IntoBytes for UnsafeCell<T>[T]);
// SAFETY: `UnsafeCell<T>` has the same in-memory representation as `T` [1], and
// thus has the same alignment as `T`.
//
// [1] Per https://doc.rust-lang.org/1.81.0/core/cell/struct.UnsafeCell.html#memory-layout:
//
//   `UnsafeCell<T>` has the same in-memory representation as its inner type
//   `T`.
const _: () = unsafe { unsafe_impl!(T: ?Sized + Unaligned => Unaligned for UnsafeCell<T>) };
assert_unaligned!(UnsafeCell<()>, UnsafeCell<u8>);

// SAFETY: See safety comment in `is_bit_valid` impl.
unsafe impl<T: TryFromBytes + ?Sized> TryFromBytes for UnsafeCell<T> {
    #[allow(clippy::missing_inline_in_public_items)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
    }

    #[inline(always)]
    fn is_bit_valid<A>(candidate: Maybe<'_, Self, A>) -> bool
    where
        A: invariant::Alignment,
    {
        T::is_bit_valid(candidate.transmute::<_, _, BecauseImmutable>())
    }
}

// SAFETY: Per the reference [1]:
//
//   An array of `[T; N]` has a size of `size_of::<T>() * N` and the same
//   alignment of `T`. Arrays are laid out so that the zero-based `nth` element
//   of the array is offset from the start of the array by `n * size_of::<T>()`
//   bytes.
//
//   ...
//
//   Slices have the same layout as the section of the array they slice.
//
// In other words, the layout of a `[T]` or `[T; N]` is a sequence of `T`s laid
// out back-to-back with no bytes in between. Therefore, `[T]` or `[T; N]` are
// `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, and `IntoBytes` if `T`
// is (respectively). Furthermore, since an array/slice has "the same alignment
// of `T`", `[T]` and `[T; N]` are `Unaligned` if `T` is.
//
// Note that we don't `assert_unaligned!` for slice types because
// `assert_unaligned!` uses `align_of`, which only works for `Sized` types.
//
// [1] https://doc.rust-lang.org/1.81.0/reference/type-layout.html#array-layout
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    unsafe_impl!(const N: usize, T: Immutable => Immutable for [T; N]);
    unsafe_impl!(const N: usize, T: TryFromBytes => TryFromBytes for [T; N]; |c| {
        let c: Ptr<'_, [ReadOnly<T>; N], _> = c.cast::<_, crate::pointer::cast::CastSized, _>();
        let c: Ptr<'_, [ReadOnly<T>], _> = c.as_slice();
        let c: Ptr<'_, ReadOnly<[T]>, _> = c.cast::<_, crate::pointer::cast::CastUnsized, _>();

        // Note that this call may panic, but it would still be sound even if it
        // did. `is_bit_valid` does not promise that it will not panic (in fact,
        // it explicitly warns that it's a possibility), and we have not
        // violated any safety invariants that we must fix before returning.
        <[T] as TryFromBytes>::is_bit_valid(c)
    });
    unsafe_impl!(const N: usize, T: FromZeros => FromZeros for [T; N]);
    unsafe_impl!(const N: usize, T: FromBytes => FromBytes for [T; N]);
    unsafe_impl!(const N: usize, T: IntoBytes => IntoBytes for [T; N]);
    unsafe_impl!(const N: usize, T: Unaligned => Unaligned for [T; N]);
    assert_unaligned!([(); 0], [(); 1], [u8; 0], [u8; 1]);
    unsafe_impl!(T: Immutable => Immutable for [T]);
    unsafe_impl!(T: TryFromBytes => TryFromBytes for [T]; |c| {
        let c: Ptr<'_, [ReadOnly<T>], _> = c.cast::<_, crate::pointer::cast::CastUnsized, _>();

        // SAFETY: Per the reference [1]:
        //
        //   An array of `[T; N]` has a size of `size_of::<T>() * N` and the
        //   same alignment of `T`. Arrays are laid out so that the zero-based
        //   `nth` element of the array is offset from the start of the array by
        //   `n * size_of::<T>()` bytes.
        //
        //   ...
        //
        //   Slices have the same layout as the section of the array they slice.
        //
        // In other words, the layout of a `[T] is a sequence of `T`s laid out
        // back-to-back with no bytes in between. If all elements in `candidate`
        // are `is_bit_valid`, so too is `candidate`.
        //
        // Note that any of the below calls may panic, but it would still be
        // sound even if it did. `is_bit_valid` does not promise that it will
        // not panic (in fact, it explicitly warns that it's a possibility), and
        // we have not violated any safety invariants that we must fix before
        // returning.
        c.iter().all(<T as TryFromBytes>::is_bit_valid)
    });
    unsafe_impl!(T: FromZeros => FromZeros for [T]);
    unsafe_impl!(T: FromBytes => FromBytes for [T]);
    unsafe_impl!(T: IntoBytes => IntoBytes for [T]);
    unsafe_impl!(T: Unaligned => Unaligned for [T]);
};

// SAFETY:
// - `Immutable`: Raw pointers do not contain any `UnsafeCell`s.
// - `FromZeros`: For thin pointers (note that `T: Sized`), the zero pointer is
//   considered "null". [1] No operations which require provenance are legal on
//   null pointers, so this is not a footgun.
// - `TryFromBytes`: By the same reasoning as for `FromZeroes`, we can implement
//   `TryFromBytes` for thin pointers provided that
//   [`TryFromByte::is_bit_valid`] only produces `true` for zeroed bytes.
//
// NOTE(#170): Implementing `FromBytes` and `IntoBytes` for raw pointers would
// be sound, but carries provenance footguns. We want to support `FromBytes` and
// `IntoBytes` for raw pointers eventually, but we are holding off until we can
// figure out how to address those footguns.
//
// [1] Per https://doc.rust-lang.org/1.81.0/std/ptr/fn.null.html:
//
//   Creates a null raw pointer.
//
//   This function is equivalent to zero-initializing the pointer:
//   `MaybeUninit::<*const T>::zeroed().assume_init()`.
//
//   The resulting pointer has the address 0.
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    unsafe_impl!(T: ?Sized => Immutable for *const T);
    unsafe_impl!(T: ?Sized => Immutable for *mut T);
    unsafe_impl!(T => TryFromBytes for *const T; |c| pointer::is_zeroed(c));
    unsafe_impl!(T => FromZeros for *const T);
    unsafe_impl!(T => TryFromBytes for *mut T; |c| pointer::is_zeroed(c));
    unsafe_impl!(T => FromZeros for *mut T);
};

// SAFETY: `NonNull<T>` self-evidently does not contain `UnsafeCell`s. This is
// not a proof, but we are accepting this as a known risk per #1358.
const _: () = unsafe { unsafe_impl!(T: ?Sized => Immutable for NonNull<T>) };

// SAFETY: Reference types do not contain any `UnsafeCell`s.
#[allow(clippy::multiple_unsafe_ops_per_block)]
const _: () = unsafe {
    unsafe_impl!(T: ?Sized => Immutable for &'_ T);
    unsafe_impl!(T: ?Sized => Immutable for &'_ mut T);
};

// SAFETY: `Option` is not `#[non_exhaustive]` [1], which means that the types
// in its variants cannot change, and no new variants can be added. `Option<T>`
// does not contain any `UnsafeCell`s outside of `T`. [1]
//
// [1] https://doc.rust-lang.org/core/option/enum.Option.html
const _: () = unsafe { unsafe_impl!(T: Immutable => Immutable for Option<T>) };

mod tuples {
    use super::*;

    /// Generates various trait implementations for tuples.
    ///
    /// # Safety
    ///
    /// `impl_tuple!` should be provided name-number pairs, where each number is
    /// the ordinal of the preceding type name.
    macro_rules! impl_tuple {
        // Entry point.
        ($($T:ident $I:tt),+ $(,)?) => {
            crate::util::macros::__unsafe();
            impl_tuple!(@all [] [$($T $I)+]);
        };

        // Build up the set of tuple types (i.e., `(A,)`, `(A, B)`, `(A, B, C)`,
        // etc.) Trait implementations that do not depend on field index may be
        // added to this branch.
        (@all [$($head_T:ident $head_I:tt)*] [$next_T:ident $next_I:tt $($tail:tt)*]) => {
            // SAFETY: If all fields of the tuple `Self` are `Immutable`, so too is `Self`.
            unsafe_impl!($($head_T: Immutable,)* $next_T: Immutable => Immutable for ($($head_T,)* $next_T,));

            // SAFETY: If all fields in `c` are `is_bit_valid`, so too is `c`.
            unsafe_impl!($($head_T: TryFromBytes,)* $next_T: TryFromBytes => TryFromBytes for ($($head_T,)* $next_T,); |c| {
                let mut c = c;
                $(TryFromBytes::is_bit_valid(into_inner!(c.reborrow().project::<_, { crate::STRUCT_VARIANT_ID }, { crate::ident_id!($head_I) }>())) &&)*
                    TryFromBytes::is_bit_valid(into_inner!(c.reborrow().project::<_, { crate::STRUCT_VARIANT_ID }, { crate::ident_id!($next_I) }>()))
            });

            // SAFETY: If all fields in `Self` are `FromZeros`, so too is `Self`.
            unsafe_impl!($($head_T: FromZeros,)* $next_T: FromZeros => FromZeros for ($($head_T,)* $next_T,));

            // SAFETY: If all fields in `Self` are `FromBytes`, so too is `Self`.
            unsafe_impl!($($head_T: FromBytes,)* $next_T: FromBytes => FromBytes for ($($head_T,)* $next_T,));

            // SAFETY: See safety comment on `ProjectToTag`.
            unsafe impl<$($head_T,)* $next_T> crate::HasTag for ($($head_T,)* $next_T,) {
                #[inline]
                fn only_derive_is_allowed_to_implement_this_trait()
                where
                    Self: Sized
                {}

                type Tag = ();

                // SAFETY: It is trivially sound to project any pointer to a
                // pointer to a type of size zero and alignment 1 (which `()` is
                // [1]). Such a pointer will trivially satisfy its aliasing and
                // validity requirements (since it has a zero-sized referent),
                // and its alignment requirement (since it is aligned to 1).
                //
                // [1] Per https://doc.rust-lang.org/1.92.0/reference/type-layout.html#r-layout.tuple.unit:
                //
                //     [T]he unit tuple (`()`)... is guaranteed as a zero-sized
                //     type to have a size of 0 and an alignment of 1.
                type ProjectToTag = crate::pointer::cast::CastToUnit;
            }

            // Generate impls that depend on tuple index.
            impl_tuple!(@variants
                [$($head_T $head_I)* $next_T $next_I]
                []
                [$($head_T $head_I)* $next_T $next_I]
            );

            // Recurse to next tuple size
            impl_tuple!(@all [$($head_T $head_I)* $next_T $next_I] [$($tail)*]);
        };
        (@all [$($head_T:ident $head_I:tt)*] []) => {};

        // Emit trait implementations that depend on field index.
        (@variants
            // The full tuple definition in type–index pairs.
            [$($AllT:ident $AllI:tt)+]
            // Types before the current index.
            [$($BeforeT:ident)*]
            // The types and indices at and after the current index.
            [$CurrT:ident $CurrI:tt $($AfterT:ident $AfterI:tt)*]
        ) => {
            // SAFETY:
            // - `Self` is a struct (albeit anonymous), so `VARIANT_ID` is
            //   `STRUCT_VARIANT_ID`.
            // - `$CurrI` is the field at index `$CurrI`, so `FIELD_ID` is
            //   `zerocopy::ident_id!($CurrI)`
            // - `()` has the same visibility as the `.$CurrI` field (ie, `.0`,
            //   `.1`, etc)
            // - `Type` has the same type as `$CurrI`; i.e., `$CurrT`.
            unsafe impl<$($AllT),+> crate::HasField<
                (),
                { crate::STRUCT_VARIANT_ID },
                { crate::ident_id!($CurrI)}
            > for ($($AllT,)+) {
                #[inline]
                fn only_derive_is_allowed_to_implement_this_trait()
                where
                    Self: Sized
                {}

                type Type = $CurrT;

                #[inline(always)]
                fn project(slf: crate::PtrInner<'_, Self>) -> *mut Self::Type {
                    let slf = slf.as_non_null().as_ptr();
                    // SAFETY: `PtrInner` promises it references either a zero-sized
                    // byte range, or else will reference a byte range that is
                    // entirely contained within an allocated object. In either
                    // case, this guarantees that `(*slf).$CurrI` is in-bounds of
                    // `slf`.
                    unsafe { core::ptr::addr_of_mut!((*slf).$CurrI) }
                }
            }

            // SAFETY: See comments on items.
            unsafe impl<Aliasing, Alignment, $($AllT),+> crate::ProjectField<
                (),
                (Aliasing, Alignment, crate::invariant::Uninit),
                { crate::STRUCT_VARIANT_ID },
                { crate::ident_id!($CurrI)}
            > for ($($AllT,)+)
            where
                Aliasing: crate::invariant::Aliasing,
                Alignment: crate::invariant::Alignment,
            {
                #[inline]
                fn only_derive_is_allowed_to_implement_this_trait()
                where
                    Self: Sized
                {}

                // SAFETY: Tuples are product types whose fields are
                // well-aligned, so projection preserves both the alignment and
                // validity invariants of the outer pointer.
                type Invariants = (Aliasing, Alignment, crate::invariant::Uninit);

                // SAFETY: Tuples are product types and so projection is infallible;
                type Error = core::convert::Infallible;
            }

            // SAFETY: See comments on items.
            unsafe impl<Aliasing, Alignment, $($AllT),+> crate::ProjectField<
                (),
                (Aliasing, Alignment, crate::invariant::Initialized),
                { crate::STRUCT_VARIANT_ID },
                { crate::ident_id!($CurrI)}
            > for ($($AllT,)+)
            where
                Aliasing: crate::invariant::Aliasing,
                Alignment: crate::invariant::Alignment,
            {
                #[inline]
                fn only_derive_is_allowed_to_implement_this_trait()
                where
                    Self: Sized
                {}

                // SAFETY: Tuples are product types whose fields are
                // well-aligned, so projection preserves both the alignment and
                // validity invariants of the outer pointer.
                type Invariants = (Aliasing, Alignment, crate::invariant::Initialized);

                // SAFETY: Tuples are product types and so projection is infallible;
                type Error = core::convert::Infallible;
            }

            // SAFETY: See comments on items.
            unsafe impl<Aliasing, Alignment, $($AllT),+> crate::ProjectField<
                (),
                (Aliasing, Alignment, crate::invariant::Valid),
                { crate::STRUCT_VARIANT_ID },
                { crate::ident_id!($CurrI)}
            > for ($($AllT,)+)
            where
                Aliasing: crate::invariant::Aliasing,
                Alignment: crate::invariant::Alignment,
            {
                #[inline]
                fn only_derive_is_allowed_to_implement_this_trait()
                where
                    Self: Sized
                {}

                // SAFETY: Tuples are product types whose fields are
                // well-aligned, so projection preserves both the alignment and
                // validity invariants of the outer pointer.
                type Invariants = (Aliasing, Alignment, crate::invariant::Valid);

                // SAFETY: Tuples are product types and so projection is infallible;
                type Error = core::convert::Infallible;
            }

            // Recurse to the next index.
            impl_tuple!(@variants [$($AllT $AllI)+] [$($BeforeT)* $CurrT] [$($AfterT $AfterI)*]);
        };
        (@variants [$($AllT:ident $AllI:tt)+] [$($BeforeT:ident)*] []) => {};
    }

    // SAFETY: `impl_tuple` is provided name-number pairs, where number is the
    // ordinal of the name.
    #[allow(clippy::multiple_unsafe_ops_per_block)]
    const _: () = unsafe {
        impl_tuple! {
            A 0,
            B 1,
            C 2,
            D 3,
            E 4,
            F 5,
            G 6,
            H 7,
            I 8,
            J 9,
            K 10,
            L 11,
            M 12,
            N 13,
            O 14,
            P 15,
            Q 16,
            R 17,
            S 18,
            T 19,
            U 20,
            V 21,
            W 22,
            X 23,
            Y 24,
            Z 25,
        };
    };
}

// SIMD support
//
// Per the Unsafe Code Guidelines Reference [1]:
//
//   Packed SIMD vector types are `repr(simd)` homogeneous tuple-structs
//   containing `N` elements of type `T` where `N` is a power-of-two and the
//   size and alignment requirements of `T` are equal:
//
//   ```rust
//   #[repr(simd)]
//   struct Vector<T, N>(T_0, ..., T_(N - 1));
//   ```
//
//   ...
//
//   The size of `Vector` is `N * size_of::<T>()` and its alignment is an
//   implementation-defined function of `T` and `N` greater than or equal to
//   `align_of::<T>()`.
//
//   ...
//
//   Vector elements are laid out in source field order, enabling random access
//   to vector elements by reinterpreting the vector as an array:
//
//   ```rust
//   union U {
//      vec: Vector<T, N>,
//      arr: [T; N]
//   }
//
//   assert_eq!(size_of::<Vector<T, N>>(), size_of::<[T; N]>());
//   assert!(align_of::<Vector<T, N>>() >= align_of::<[T; N]>());
//
//   unsafe {
//     let u = U { vec: Vector<T, N>(t_0, ..., t_(N - 1)) };
//
//     assert_eq!(u.vec.0, u.arr[0]);
//     // ...
//     assert_eq!(u.vec.(N - 1), u.arr[N - 1]);
//   }
//   ```
//
// Given this background, we can observe that:
// - The size and bit pattern requirements of a SIMD type are equivalent to the
//   equivalent array type. Thus, for any SIMD type whose primitive `T` is
//   `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, or `IntoBytes`, that
//   SIMD type is also `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, or
//   `IntoBytes` respectively.
// - Since no upper bound is placed on the alignment, no SIMD type can be
//   guaranteed to be `Unaligned`.
//
// Also per [1]:
//
//   This chapter represents the consensus from issue #38. The statements in
//   here are not (yet) "guaranteed" not to change until an RFC ratifies them.
//
// See issue #38 [2]. While this behavior is not technically guaranteed, the
// likelihood that the behavior will change such that SIMD types are no longer
// `TryFromBytes`, `FromZeros`, `FromBytes`, or `IntoBytes` is next to zero, as
// that would defeat the entire purpose of SIMD types. Nonetheless, we put this
// behavior behind the `simd` Cargo feature, which requires consumers to opt
// into this stability hazard.
//
// [1] https://rust-lang.github.io/unsafe-code-guidelines/layout/packed-simd-vectors.html
// [2] https://github.com/rust-lang/unsafe-code-guidelines/issues/38
#[cfg(feature = "simd")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "simd")))]
mod simd {
    /// Defines a module which implements `TryFromBytes`, `FromZeros`,
    /// `FromBytes`, and `IntoBytes` for a set of types from a module in
    /// `core::arch`.
    ///
    /// `$arch` is both the name of the defined module and the name of the
    /// module in `core::arch`, and `$typ` is the list of items from that module
    /// to implement `FromZeros`, `FromBytes`, and `IntoBytes` for.
    #[allow(unused_macros)] // `allow(unused_macros)` is needed because some
                            // target/feature combinations don't emit any impls
                            // and thus don't use this macro.
    macro_rules! simd_arch_mod {
        ($(#[cfg $cfg:tt])* $(#[cfg_attr $cfg_attr:tt])? $arch:ident, $mod:ident, $($typ:ident),*) => {
            $(#[cfg $cfg])*
            #[cfg_attr(doc_cfg, doc(cfg $($cfg)*))]
            $(#[cfg_attr $cfg_attr])?
            mod $mod {
                use core::arch::$arch::{$($typ),*};

                use crate::*;
                impl_known_layout!($($typ),*);
                // SAFETY: See comment on module definition for justification.
                #[allow(clippy::multiple_unsafe_ops_per_block)]
                const _: () = unsafe {
                    $( unsafe_impl!($typ: Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes); )*
                };
            }
        };
    }

    #[rustfmt::skip]
    const _: () = {
        simd_arch_mod!(
            #[cfg(target_arch = "x86")]
            x86, x86, __m128, __m128d, __m128i, __m256, __m256d, __m256i
        );
        #[cfg(not(no_zerocopy_simd_x86_avx12_1_89_0))]
        simd_arch_mod!(
            #[cfg(target_arch = "x86")]
            #[cfg_attr(doc_cfg, doc(cfg(rust = "1.89.0")))]
            x86, x86_nightly, __m512bh, __m512, __m512d, __m512i
        );
        simd_arch_mod!(
            #[cfg(target_arch = "x86_64")]
            x86_64, x86_64, __m128, __m128d, __m128i, __m256, __m256d, __m256i
        );
        #[cfg(not(no_zerocopy_simd_x86_avx12_1_89_0))]
        simd_arch_mod!(
            #[cfg(target_arch = "x86_64")]
            #[cfg_attr(doc_cfg, doc(cfg(rust = "1.89.0")))]
            x86_64, x86_64_nightly, __m512bh, __m512, __m512d, __m512i
        );
        simd_arch_mod!(
            #[cfg(target_arch = "wasm32")]
            wasm32, wasm32, v128
        );
        simd_arch_mod!(
            #[cfg(all(feature = "simd-nightly", target_arch = "powerpc"))]
            powerpc, powerpc, vector_bool_long, vector_double, vector_signed_long, vector_unsigned_long
        );
        simd_arch_mod!(
            #[cfg(all(feature = "simd-nightly", target_arch = "powerpc64"))]
            powerpc64, powerpc64, vector_bool_long, vector_double, vector_signed_long, vector_unsigned_long
        );
        // NOTE: NEON intrinsics were broken on big-endian platforms from their stabilization up to
        // Rust 1.87. (Context in https://github.com/rust-lang/stdarch/issues/1484). Support is
        // split in two different version ranges on top of the base configuration, requiring either
        // little endian or the more recent version to be detected as well.
        #[cfg(not(no_zerocopy_aarch64_simd_1_59_0))]
        simd_arch_mod!(
            #[cfg(all(
                target_arch = "aarch64",
                any(
                    target_endian = "little",
                    not(no_zerocopy_aarch64_simd_be_1_87_0)
                )
            ))]
            #[cfg_attr(
                doc_cfg,
                doc(cfg(all(target_arch = "aarch64", any(
                    all(rust = "1.59.0", target_endian = "little"),
                    rust = "1.87.0",
                ))))
            )]
            aarch64, aarch64, float32x2_t, float32x4_t, float64x1_t, float64x2_t, int8x8_t, int8x8x2_t,
            int8x8x3_t, int8x8x4_t, int8x16_t, int8x16x2_t, int8x16x3_t, int8x16x4_t, int16x4_t,
            int16x8_t, int32x2_t, int32x4_t, int64x1_t, int64x2_t, poly8x8_t, poly8x8x2_t, poly8x8x3_t,
            poly8x8x4_t, poly8x16_t, poly8x16x2_t, poly8x16x3_t, poly8x16x4_t, poly16x4_t, poly16x8_t,
            poly64x1_t, poly64x2_t, uint8x8_t, uint8x8x2_t, uint8x8x3_t, uint8x8x4_t, uint8x16_t,
            uint8x16x2_t, uint8x16x3_t, uint8x16x4_t, uint16x4_t, uint16x4x2_t, uint16x4x3_t,
            uint16x4x4_t, uint16x8_t, uint32x2_t, uint32x4_t, uint64x1_t, uint64x2_t
        );
    };
}

#[cfg(kani)]
mod proofs {
    #[cfg(feature = "alloc")]
    use alloc::boxed::Box;
    use core::{mem, num::NonZeroU16, ptr::NonNull};

    use crate::{
        pointer::{cast::CastUnsized, invariant::Initialized, BecauseImmutable, Ptr},
        proof_support::{
            all_zero_byte_policy_oracle, assert_same_bool, assert_same_u8_elements, bool_from_byte,
            char_from_ne_bytes, nonzero_u16_from_ne_bytes, validate_and_read_sized,
        },
        wrappers::ReadOnly,
        TryFromBytes,
    };

    // Configuration: Every harness in this module uses the common Kani CI
    // configuration documented in `agent_docs/validation.md`: the CI-pinned
    // Kani release and its bundled x86_64-unknown-linux-gnu compiler (64-bit,
    // little-endian), the stable-compatible feature bundle,
    // `-Zfunction-contracts`, and one layout selected by `--randomize-layout`
    // per invocation.
    //
    // Domain: Every exactly sized initialized source representation for `bool`,
    // `char`, `NonZeroU16`, `Option<NonZeroU16>`, and `[bool; 4]` on Kani's
    // target. The raw validator receives each representation at two controlled
    // physical placements: byte offsets zero and one within separate
    // 16-aligned `repr(C)` storage objects.
    //
    // Storage and bounds: All five harnesses use one fixed stack input of at
    // most four bytes. The `Unaligned` specialization runs at both physical
    // placements. The `Aligned` specialization runs at offset zero and also at
    // offset one when the destination has alignment one. A separate
    // zero-offset `Unaligned` check invokes `Wrapping<T>`'s validator, exactly
    // the non-materializing adapter used by the public read path after it
    // forgets its candidate's type-level alignment. Compiler alignment queries
    // and the standard raw-pointer `is_aligned` operation check the source
    // type's alignment, the destination bound, and both actual addresses before
    // any zerocopy validator runs. The public read makes its own aligned
    // candidate. The harnesses perform no dynamic allocation and contain no
    // explicit proof loop. Each carries `#[kani::unwind(5)]`, which permits any
    // modeled bytewise operation or the target array validator to examine four
    // bytes or elements and terminate, with Kani's unwinding checks enforcing
    // the bound.
    //
    // Establishes: Both the destination's non-materializing raw-byte validator
    // over the exact marker/placement matrix and the public path's
    // `Wrapping<T>` adapter check agree with the validity oracle on every
    // candidate, including invalid candidates. On this target, offset one is
    // physically misaligned for `char`, `NonZeroU16`, and
    // `Option<NonZeroU16>`; each harness asserts its required nontrivial
    // alignment. `bool` and `[bool; 4]` have alignment one, so no physically
    // misaligned placement exists for them; both controlled
    // addresses exercise both type-level markers. Those numeric alignment
    // assertions are fail-closed facts of the pinned compiler and target, not
    // claims that Rust's general primitive-layout rules universally fix these
    // alignments; the independent placement oracle is raw-pointer `is_aligned`
    // on each actual address. On independently oracle-valid inputs, the public
    // read API succeeds and returns the oracle's value.
    //
    // Oracle: Safe standard-library constructors define `char` and nonzero
    // integer validity. `char_from_ne_bytes` and
    // `nonzero_u16_from_ne_bytes` respectively centralize the exact safe
    // `u32::from_ne_bytes`/`char::from_u32` and
    // `u16::from_ne_bytes`/`NonZeroU16::new` bridges, with their Rust 1.93.0
    // contracts documented next to those helpers. `bool_from_byte` is the one
    // centralized manual Rust language oracle because Rust has no safe checked
    // `u8`-to-`bool` conversion. The documented `char` representation,
    // `NonZero` layout, and `Option` null-pointer optimization establish the
    // byte-level mappings used by those oracles [1][2][3]. For `[bool; 4]`, the
    // compiler-checked one-byte element size and the array layout rule map the
    // four checked elements to the exact four candidate bytes [4]. The three
    // equality checks over compiler `align_of`/`size_of` results use shared
    // `assert_same_usize`; its `assert_eq!`/`usize::PartialEq` mechanics make a
    // mismatch fail closed [6], while the language rules or pinned target facts
    // above supply the expected operands. The remaining greater-than-one
    // alignment guards use primitive `usize` ordering [7]. Physical placement
    // is classified independently of zerocopy: raw-pointer `is_aligned` reports
    // whether the candidate address is properly aligned for its destination
    // type [5].
    //
    // Excludes: Other types and array lengths, source lengths other than the
    // exact destination size, non-native byte order, and physical placements
    // other than the two selected offsets. In particular, this does not
    // quantify over arbitrary absolute addresses. It also excludes validity or
    // provenance behavior not modeled by Kani. The public read API's invalid
    // input path is deliberately not invoked; both its `Wrapping<T>` adapter
    // and the direct validator prove non-materializing rejection without
    // risking production of an invalid `T` in a model that does not completely
    // check that operation.
    //
    // [1] Per https://doc.rust-lang.org/1.93.0/reference/types/textual.html#character-type:
    //
    //     A value of type `char` is a Unicode scalar value (i.e. a code point
    //     that is not a surrogate), represented as a 32-bit unsigned word in
    //     the 0x0000 to 0xD7FF or 0xE000 to 0x10FFFF range.
    //
    // [2] Per https://doc.rust-lang.org/1.93.0/std/num/struct.NonZero.html#layout:
    //
    //     `NonZero<T>` is guaranteed to have the same layout and bit validity
    //     as `T` with the exception that the all-zero bit pattern is invalid.
    //
    // [3] Per https://doc.rust-lang.org/1.93.0/std/option/index.html#representation,
    // whose guarantee table includes `num::NonZero*`:
    //
    //     transmute a value `t` of type `T` to type `Option<T>` (producing the
    //     value `Some(t)`)
    //
    //     `transmute::<_, Option<T>>([0u8; size_of::<T>()])` is sound and
    //     produces `Option::<T>::None`.
    //
    // [4] Per https://doc.rust-lang.org/1.93.0/reference/type-layout.html#array-layout:
    //
    //     Arrays are laid out so that the zero-based `nth` element of the
    //     array is offset from the start of the array by
    //     `n * size_of::<T>()` bytes.
    //
    // [5] Per https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.is_aligned:
    //
    //     Returns whether the pointer is properly aligned for `T`.
    //
    // [6] https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#tymethod.eq
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialEq-for-usize
    //
    // [7] https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialOrd.html#method.gt
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialOrd-for-usize

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_bool_try_read_from_bytes() {
        crate::proof_support::assert_same_usize(core::mem::align_of::<bool>(), 1);
        let bytes: [u8; 1] = kani::any();
        let expected = bool_from_byte(bytes[0]);
        let expected_valid = expected.is_some();
        let result = validate_and_read_sized!(bool, bytes, expected);

        kani::cover!(expected_valid);
        kani::cover!(!expected_valid);
        if let Some(value) = result {
            assert_eq!(Some(value), expected);
        }
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_char_try_read_from_bytes() {
        assert!(core::mem::align_of::<char>() > 1);
        let bytes: [u8; 4] = kani::any();
        let scalar = u32::from_ne_bytes(bytes);
        let expected = char_from_ne_bytes(bytes);
        let expected_valid = expected.is_some();
        let result = validate_and_read_sized!(char, bytes, expected);

        kani::cover!(expected_valid);
        kani::cover!((0xD800..=0xDFFF).contains(&scalar));
        kani::cover!(scalar > 0x10FFFF);
        if let Some(value) = result {
            assert_eq!(Some(value), expected);
        }
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_nonzero_u16_try_read_from_bytes() {
        assert!(core::mem::align_of::<NonZeroU16>() > 1);
        let bytes: [u8; 2] = kani::any();
        let expected = nonzero_u16_from_ne_bytes(bytes);
        let expected_valid = expected.is_some();
        let result = validate_and_read_sized!(NonZeroU16, bytes, expected);

        kani::cover!(expected_valid);
        kani::cover!(!expected_valid);
        if let Some(value) = result {
            assert_eq!(Some(value), expected);
        }
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_option_nonzero_u16_try_read_from_bytes() {
        assert!(core::mem::align_of::<Option<NonZeroU16>>() > 1);
        let bytes: [u8; 2] = kani::any();
        let expected = nonzero_u16_from_ne_bytes(bytes);
        let result = validate_and_read_sized!(Option<NonZeroU16>, bytes, Some(expected)).unwrap();

        kani::cover!(expected.is_none());
        kani::cover!(expected.is_some());
        assert_eq!(result, expected);
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_bool_array_try_read_from_bytes() {
        crate::proof_support::assert_same_usize(core::mem::align_of::<[bool; 4]>(), 1);
        crate::proof_support::assert_same_usize(
            core::mem::size_of::<bool>(),
            core::mem::size_of::<u8>(),
        );
        let bytes: [u8; 4] = kani::any();
        let expected = [
            bool_from_byte(bytes[0]),
            bool_from_byte(bytes[1]),
            bool_from_byte(bytes[2]),
            bool_from_byte(bytes[3]),
        ];
        let expected_value = match expected {
            [Some(a), Some(b), Some(c), Some(d)] => Some([a, b, c, d]),
            _ => None,
        };
        let expected_valid = expected_value.is_some();
        let result = validate_and_read_sized!([bool; 4], bytes, expected_value);

        kani::cover!(expected_valid);
        kani::cover!(expected[0].is_none());
        kani::cover!(expected[1].is_none());
        kani::cover!(expected[2].is_none());
        kani::cover!(expected[3].is_none());
        if let Some(values) = result {
            assert_eq!(Some(values[0]), expected[0]);
            assert_eq!(Some(values[1]), expected[1]);
            assert_eq!(Some(values[2]), expected[2]);
            assert_eq!(Some(values[3]), expected[3]);
        }
    }

    // Domain: Every initialized eight-byte source sequence for the thin
    // pointer-bearing monomorphizations below. Eight bytes is the pointer size
    // of the common 64-bit Kani CI target documented above.
    //
    // Storage and bounds: Every harness uses one fixed eight-byte stack input.
    // Separate copies at byte offsets zero and one within 16-aligned `repr(C)`
    // storage exercise the `Unaligned` specialization at both addresses. The
    // `Aligned` specialization runs at offset zero; the offset-one address is
    // independently confirmed physically misaligned and is therefore not
    // passed under that marker. Compiler alignment queries and the standard
    // raw-pointer `is_aligned` operation check this matrix before any zerocopy
    // validator runs. The asserted nontrivial destination alignment is a
    // fail-closed fact of the pinned compiler and target, not a claim that
    // Rust's general pointer-layout rules universally fix that alignment; the
    // independent placement oracle is `is_aligned` on each actual address. The
    // public API makes its own aligned candidate. None dynamically allocates.
    // In particular, the
    // `Option<Box<u8>>` harness constructs and reads only `None`, never a
    // `Box`, so it exercises the null niche without exercising allocation. The
    // proof source contains no explicit loop. No harness uses `kani::assume`;
    // every initialized eight-byte input is unconstrained. The fixed pointer
    // width and same-size premises use compiler `size_of` values compared
    // through shared `assert_same_usize` [5]; that helper supplies equality
    // mechanics, while the expected width is pinned configuration and the
    // same-size relation is a fail-closed case premise. The destination
    // greater-than-one guards use primitive `usize` ordering [6].
    // `#[kani::unwind(9)]` permits each modeled oracle array comparison or
    // target scan to examine eight bytes and terminate, with Kani's unwinding
    // checks enforcing the bound.
    //
    // Establishes: At the aligned placement, both `Unaligned` and `Aligned`
    // type-level markers, and at the deliberately physically misaligned
    // placement, the `Unaligned` marker, make the non-materializing raw-byte
    // validator implement zerocopy's conservative policy of accepting exactly
    // the all-zero byte sequence. On that independently known-valid input, the
    // public read API succeeds; a raw-pointer read is null and a niche `Option`
    // read is `None`.
    //
    // Oracle: The shared `all_zero_byte_policy_oracle` compares the complete
    // candidate with a Rust repeat-array expression through safe iteration and
    // primitive equality; its adjacent documentation supplies the exact Rust
    // 1.93 contracts. A true result therefore establishes that every candidate
    // byte is zero without manually reconstructing an integer or calling a
    // zerocopy target. This family separately adopts that classification as its
    // explicit representation-policy oracle, evaluated before the target byte
    // scan rather than inferred from agreement with that scan.
    // `validate_and_read_sized!` compares the
    // target with this predicate at every in-scope placement and only
    // materializes an oracle-valid candidate. The standard library guarantees
    // that zero-initializing a thin raw pointer produces null [1] and that an
    // all-zero representation produces `None` for every optional pointer
    // family instantiated below [2]. The safe `is_null` [3] and `is_none` [4]
    // operations then independently classify the already-valid result. These
    // output oracles do not themselves establish representation validity.
    //
    // Excludes: This does not claim that rejected nonzero bytes are invalid
    // Rust pointers, and it does not quantify over arbitrary absolute
    // addresses or offsets other than zero and one in the controlled storage.
    // It also excludes the public read API's rejected-input path, fat pointers,
    // other pointees, function signatures and ABIs, and non-Kani targets.
    // Reference aliasing, raw-pointer provenance, invalid-value production, and
    // uninitialized-memory handling along the composite cast/validation/read
    // path remain TOOL/TCB premises because Kani does not completely check
    // those semantics. The initialized source storage and independently valid
    // accepted representation do not establish those unmodeled obligations.
    //
    // [1] Per https://doc.rust-lang.org/1.93.0/std/ptr/fn.null.html and
    // https://doc.rust-lang.org/1.93.0/std/ptr/fn.null_mut.html:
    //
    //     Creates a null raw pointer.
    //
    //     This function is equivalent to zero-initializing the pointer:
    //     `MaybeUninit::<*const T>::zeroed().assume_init()`. The resulting
    //     pointer has the address 0.
    //
    //     Creates a null mutable raw pointer.
    //
    //     This function is equivalent to zero-initializing the pointer:
    //     `MaybeUninit::<*mut T>::zeroed().assume_init()`. The resulting pointer
    //     has the address 0.
    //
    // [2] Per https://doc.rust-lang.org/1.93.0/std/option/index.html#representation,
    // whose guarantee table includes references, `NonNull`, function pointers,
    // and `Box<U>` (specifically `Box<U, Global>`) when `U: Sized`:
    //
    //     `transmute::<_, Option<T>>([0u8; size_of::<T>()])` is sound and
    //     produces `Option::<T>::None`.
    //
    // [3] Per https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#method.is_null:
    //
    //     `is_null` returns `true` when the raw pointer is null.
    //
    // [4] Per https://doc.rust-lang.org/1.93.0/std/option/enum.Option.html#method.is_none:
    //
    //     `is_none` returns `true` when the option is `None`.
    //
    // [5] https://doc.rust-lang.org/1.93.0/std/mem/fn.size_of.html
    // https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#tymethod.eq
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialEq-for-usize
    //
    // [6] https://doc.rust-lang.org/1.93.0/std/mem/fn.align_of.html
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialOrd.html#method.gt
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialOrd-for-usize
    macro_rules! zero_only_pointer_proof {
        ($proof:ident, $ty:ty, $zero:expr, $value:ident => $assertion:expr) => {
            #[kani::proof]
            #[kani::unwind(9)]
            fn $proof() {
                crate::proof_support::assert_same_usize(mem::size_of::<usize>(), 8);
                crate::proof_support::assert_same_usize(
                    mem::size_of::<$ty>(),
                    mem::size_of::<usize>(),
                );
                assert!(mem::align_of::<$ty>() > 1);
                let bytes: [u8; mem::size_of::<$ty>()] = kani::any();
                let expected_valid = all_zero_byte_policy_oracle(&bytes);
                let expected = if expected_valid { Some($zero) } else { None };
                let result = validate_and_read_sized!($ty, bytes, expected);
                kani::cover!(expected_valid);
                kani::cover!(!expected_valid);
                if let Some($value) = result {
                    $assertion;
                }
            }
        };
    }

    zero_only_pointer_proof!(
        prove_const_pointer_try_read_from_bytes,
        *const u8,
        core::ptr::null(),
        value => assert!(value.is_null())
    );
    zero_only_pointer_proof!(
        prove_mut_pointer_try_read_from_bytes,
        *mut u8,
        core::ptr::null_mut(),
        value => assert!(value.is_null())
    );
    zero_only_pointer_proof!(
        prove_option_non_null_try_read_from_bytes,
        Option<NonNull<u8>>,
        None,
        value => assert!(value.is_none())
    );
    zero_only_pointer_proof!(
        prove_option_ref_try_read_from_bytes,
        Option<&'static u8>,
        None,
        value => assert!(value.is_none())
    );
    zero_only_pointer_proof!(
        prove_option_mut_ref_try_read_from_bytes,
        Option<&'static mut u8>,
        None,
        value => assert!(value.is_none())
    );
    #[cfg(feature = "alloc")]
    zero_only_pointer_proof!(
        prove_option_box_try_read_from_bytes,
        Option<Box<u8>>,
        None,
        value => assert!(value.is_none())
    );
    zero_only_pointer_proof!(
        prove_option_fn_try_read_from_bytes,
        Option<fn()>,
        None,
        value => assert!(value.is_none())
    );
    zero_only_pointer_proof!(
        prove_option_unsafe_fn_try_read_from_bytes,
        Option<unsafe fn()>,
        None,
        value => assert!(value.is_none())
    );
    zero_only_pointer_proof!(
        prove_option_extern_c_fn_try_read_from_bytes,
        Option<extern "C" fn()>,
        None,
        value => assert!(value.is_none())
    );
    zero_only_pointer_proof!(
        prove_option_unsafe_extern_c_fn_try_read_from_bytes,
        Option<unsafe extern "C" fn()>,
        None,
        value => assert!(value.is_none())
    );

    // Domain: Two independently selectable proof families each cover every
    // byte sequence of lengths zero through four. This includes the empty DST
    // boundary, every single UTF-8 scalar encoding, and every mixture whose
    // total encoded length fits the bound. The direct-validator family checks
    // both alignment-marker implementations sealed by the current pointer
    // model: `Unaligned`, which `transmute_with` produces, and `Aligned`, which
    // `bikeshed_recall_aligned` safely recalls because `str: Unaligned`.
    //
    // Storage and bounds: Each harness uses one fixed stack array of zero to
    // four bytes and performs no dynamic allocation. Only the array elements
    // are symbolic inputs. The local source object's placement and allocation
    // identity are fixed by the harness rather than quantified by Kani, so
    // every conclusion below is restricted to that modeled stack-object
    // placement. Every checking helper receives a shared slice borrow of that
    // array; none copies it into a second array. The non-materializing
    // validator helper's safe zerocopy conversion from `&[u8]` to
    // `&ReadOnly<[u8]>` creates only another shared reference, not wrapper
    // storage. That conversion is target-path setup rather than an independent
    // oracle: the harness relies on the Rust/Kani model to preserve the
    // referent through it, then tests the resulting validator plumbing against
    // the independent grammar oracle below. No harness uses `kani::assume`.
    // The oracle's sole explicit loop consumes at least one and at most four
    // bytes per iteration. Every harness carries `#[kani::unwind(5)]`, which
    // permits all iterations for an initial length of at most four and makes
    // Kani check that the bound suffices.
    //
    // Establishes: At each harness's fixed modeled source placement, its five
    // direct proofs establish that the non-materializing
    // `is_bit_valid::<Unaligned>` and `is_bit_valid::<Aligned>` specializations
    // accept exactly when the external-specification oracle does. At the same
    // modeled placements, five separate harnesses pass each grammar-accepted
    // input to the public borrowed read API, which succeeds and returns the
    // same ordered bytes and length. `str::as_bytes` provides the safe
    // byte-slice view used by the shared elementwise observer [7]. That
    // observer obtains both counts with `slice::len`, compares them through
    // the shared equality helpers, and then compares ordered bytes through safe
    // iteration [8]. The four syntactically nonempty public harnesses
    // unconditionally check that the result retains that fixed input address
    // within Kani's pointer model; pointer equality is only an address
    // observation, not a provenance or aliasing theorem. No address identity is
    // claimed for empty slices.
    //
    // External-specification validity oracle: Rust requires every `str` to
    // contain valid UTF-8 [1]. Unicode 17 definitions D85, D86, D89, and D92
    // define a valid UTF-8 string through well-formed UTF-8 code-unit sequences
    // and the UTF-8 encoding form; Unicode's authoritative Table 3-7 then lists
    // every well-formed byte sequence and declares values outside its listed
    // ranges ill-formed [2]. The nine source alternatives in
    // `utf8_suffix_after_scalar`, in order, correspond one-for-one to Table
    // 3-7's nine rows. In each matching slice pattern, `rest @ ..` binds the
    // untouched suffix after that one well-formed scalar encoding.
    //
    // The loop invariant is that the original input equals a sequence of
    // already consumed well-formed scalar prefixes followed by `bytes`. Every
    // `Some(rest)` step shortens that suffix by one through four bytes;
    // `None` rejects immediately, and the tail `true` is reached exactly when
    // the suffix is empty. This gives the repeated-prefix decomposition needed
    // by D85/D86/D89. We admit both the bridge from Rust 1.93's term “valid
    // UTF-8” to those Unicode definitions and the manual Table-3-7 transcription
    // as EXTERNAL-SPEC/TCB premises, not conclusions proved by Kani. The oracle
    // calls neither zerocopy nor the standard library's UTF-8 validator. It is
    // code-path independent, though intentionally not algorithmically diverse:
    // this smallest manual rule has no decoder arithmetic or indexing surface.
    //
    // Rust's safe slice, inclusive-range, or-pattern, binding, match, and loop
    // semantics give the grammar transcription its executable meaning [9].
    // Each harness's array-to-slice coercion is compiler-checked [3]. On a
    // nonempty valid input, `slice::as_ptr` supplies the address of the borrowed
    // source buffer [4], `str::as_ptr` supplies the address of the returned
    // string's first byte [5], and `ptr::addr_eq` compares those addresses while
    // discarding pointer metadata [6]. The expected address therefore comes
    // from the original modeled storage, not from the validity oracle. These
    // harnesses exercise the stated functional observations of zerocopy's
    // validator/cast plumbing at those modeled placements.
    //
    // Excludes: Arbitrary absolute source addresses, allocation identities, and
    // relative or subobject placement offsets—including heap/static sources and
    // other valid data-pointer choices for an empty slice—are outside the one
    // fixed local object modeled by each harness. Also excluded are strings
    // longer than four bytes, a machine proof of the admitted Rust-to-Unicode
    // bridge or Table-3-7 transcription, and the public borrowed API's
    // invalid-input path.
    // The latter is not invoked because a bug which materialized invalid `str`
    // would be undefined before its `Result` could safely be inspected. Kani
    // does not completely check reference aliasing, pointer provenance, invalid
    // values, or uninitialized memory, so those obligations—including whether
    // an observed equal address carries the required provenance—remain explicit
    // tool/TCB premises rather than conclusions of these harnesses.
    //
    // [1] https://doc.rust-lang.org/1.93.0/reference/types/textual.html#r-type.text.str-value
    // [2] https://www.unicode.org/versions/Unicode17.0.0/core-spec/chapter-3/#G32849
    // https://www.unicode.org/versions/Unicode17.0.0/core-spec/chapter-3/#G32854
    // https://www.unicode.org/versions/Unicode17.0.0/core-spec/chapter-3/#G32860
    // https://www.unicode.org/versions/Unicode17.0.0/core-spec/chapter-3/#G27817
    // https://www.unicode.org/versions/Unicode17.0.0/core-spec/chapter-3/#G27506
    // [3] https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#unsized-coercions
    // [4] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.as_ptr
    // [5] https://doc.rust-lang.org/1.93.0/std/primitive.str.html#method.as_ptr
    // [6] https://doc.rust-lang.org/1.93.0/std/ptr/fn.addr_eq.html
    // [7] https://doc.rust-lang.org/1.93.0/std/primitive.str.html#method.as_bytes
    // [8] https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.len
    // https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
    // https://doc.rust-lang.org/1.93.0/std/cmp/trait.PartialEq.html#tymethod.eq
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-PartialEq-for-usize
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.iter
    // https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.copied
    // https://doc.rust-lang.org/1.93.0/std/iter/trait.Iterator.html#method.eq
    // https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-PartialEq-for-u8
    // https://doc.rust-lang.org/1.93.0/std/primitive.bool.html#impl-PartialEq-for-bool
    // [9] https://doc.rust-lang.org/1.93.0/reference/patterns.html#slice-patterns
    // https://doc.rust-lang.org/1.93.0/reference/patterns.html#range-patterns
    // https://doc.rust-lang.org/1.93.0/reference/patterns.html#or-patterns
    // https://doc.rust-lang.org/1.93.0/reference/patterns.html#identifier-patterns
    // https://doc.rust-lang.org/1.93.0/std/option/enum.Option.html
    // https://doc.rust-lang.org/1.93.0/reference/expressions/match-expr.html
    // https://doc.rust-lang.org/1.93.0/reference/expressions/return-expr.html
    // https://doc.rust-lang.org/1.93.0/reference/expressions/block-expr.html#r-expr.block.result
    // https://doc.rust-lang.org/1.93.0/reference/expressions/loop-expr.html#predicate-loops
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.is_empty

    fn utf8_suffix_after_scalar(bytes: &[u8]) -> Option<&[u8]> {
        match bytes {
            [0x00..=0x7F, rest @ ..]
            | [0xC2..=0xDF, 0x80..=0xBF, rest @ ..]
            | [0xE0, 0xA0..=0xBF, 0x80..=0xBF, rest @ ..]
            | [0xE1..=0xEC, 0x80..=0xBF, 0x80..=0xBF, rest @ ..]
            | [0xED, 0x80..=0x9F, 0x80..=0xBF, rest @ ..]
            | [0xEE..=0xEF, 0x80..=0xBF, 0x80..=0xBF, rest @ ..]
            | [0xF0, 0x90..=0xBF, 0x80..=0xBF, 0x80..=0xBF, rest @ ..]
            | [0xF1..=0xF3, 0x80..=0xBF, 0x80..=0xBF, 0x80..=0xBF, rest @ ..]
            | [0xF4, 0x80..=0x8F, 0x80..=0xBF, 0x80..=0xBF, rest @ ..] => Some(rest),
            _ => None,
        }
    }

    fn utf8_oracle(mut bytes: &[u8]) -> bool {
        while !bytes.is_empty() {
            bytes = match utf8_suffix_after_scalar(bytes) {
                Some(rest) => rest,
                None => return false,
            };
        }
        true
    }

    fn assert_str_validators_match(bytes: &[u8], expected_valid: bool) {
        let source: &ReadOnly<[u8]> = bytes.into();
        let mut candidate = Ptr::from_ref(source)
            .transmute_with::<ReadOnly<str>, Initialized, CastUnsized, BecauseImmutable>();
        let unaligned_valid = <str as TryFromBytes>::is_bit_valid(candidate.reborrow_shared());
        let aligned_candidate = candidate.reborrow_shared().bikeshed_recall_aligned();
        let aligned_valid = <str as TryFromBytes>::is_bit_valid(aligned_candidate);
        assert_same_bool(unaligned_valid, expected_valid);
        assert_same_bool(aligned_valid, expected_valid);
    }

    fn assert_empty_valid_str_borrow(bytes: &[u8]) {
        match str::try_ref_from_bytes(bytes) {
            Ok(value) => assert_same_u8_elements(value.as_bytes(), bytes),
            Err(_) => assert_same_bool(false, true),
        }
    }

    fn assert_nonempty_valid_str_borrow(bytes: &[u8]) {
        match str::try_ref_from_bytes(bytes) {
            Ok(value) => {
                assert_same_u8_elements(value.as_bytes(), bytes);
                assert_same_bool(core::ptr::addr_eq(value.as_ptr(), bytes.as_ptr()), true);
            }
            Err(_) => assert_same_bool(false, true),
        }
    }

    macro_rules! str_validator_proof {
        ($proof:ident, $len:expr) => {
            #[kani::proof]
            #[kani::unwind(5)]
            fn $proof() {
                let bytes: [u8; $len] = kani::any();
                let expected_valid = utf8_oracle(&bytes);
                match expected_valid {
                    true => kani::cover!(true, "independent grammar accepts this byte sequence"),
                    false => kani::cover!(true, "independent grammar rejects this byte sequence"),
                }
                assert_str_validators_match(&bytes, expected_valid);
            }
        };
    }

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_empty_str_validators() {
        let bytes: [u8; 0] = [];
        let expected_valid = utf8_oracle(&bytes);
        assert_same_bool(expected_valid, true);
        assert_str_validators_match(&bytes, expected_valid);
    }

    str_validator_proof!(prove_one_byte_str_validators, 1);
    str_validator_proof!(prove_two_byte_str_validators, 2);
    str_validator_proof!(prove_three_byte_str_validators, 3);
    str_validator_proof!(prove_four_byte_str_validators, 4);

    #[kani::proof]
    #[kani::unwind(5)]
    fn prove_empty_str_try_ref_from_bytes() {
        let bytes: [u8; 0] = [];
        match utf8_oracle(&bytes) {
            true => assert_empty_valid_str_borrow(&bytes),
            false => assert_same_bool(false, true),
        }
    }

    macro_rules! nonempty_str_borrow_proof {
        ($proof:ident, $len:expr) => {
            #[kani::proof]
            #[kani::unwind(5)]
            fn $proof() {
                let bytes: [u8; $len] = kani::any();
                match utf8_oracle(&bytes) {
                    true => {
                        kani::cover!(true, "independent grammar accepts this byte sequence");
                        assert_nonempty_valid_str_borrow(&bytes);
                    }
                    false => {
                        kani::cover!(true, "independent grammar rejects this byte sequence");
                    }
                }
            }
        };
    }

    nonempty_str_borrow_proof!(prove_one_byte_str_try_ref_from_bytes, 1);
    nonempty_str_borrow_proof!(prove_two_byte_str_try_ref_from_bytes, 2);
    nonempty_str_borrow_proof!(prove_three_byte_str_try_ref_from_bytes, 3);
    nonempty_str_borrow_proof!(prove_four_byte_str_try_ref_from_bytes, 4);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_impls() {
        // A type that can supply test cases for testing
        // `TryFromBytes::is_bit_valid`. All types passed to `assert_impls!`
        // must implement this trait; that macro uses it to generate runtime
        // tests for `TryFromBytes` impls.
        //
        // All `T: FromBytes` types are provided with a blanket impl. Other
        // types must implement `TryFromBytesTestable` directly (ie using
        // `impl_try_from_bytes_testable!`).
        trait TryFromBytesTestable {
            fn with_passing_test_cases<F: Fn(Box<ReadOnly<Self>>)>(f: F);
            fn with_failing_test_cases<F: Fn(&mut [u8])>(f: F);
        }

        impl<T: FromBytes> TryFromBytesTestable for T {
            fn with_passing_test_cases<F: Fn(Box<ReadOnly<Self>>)>(f: F) {
                // Test with a zeroed value.
                f(ReadOnly::<Self>::new_box_zeroed().unwrap());

                let ffs = {
                    let mut t = ReadOnly::new(Self::new_zeroed());
                    let ptr: *mut T = ReadOnly::as_mut(&mut t);
                    // SAFETY: `T: FromBytes`
                    unsafe { ptr::write_bytes(ptr.cast::<u8>(), 0xFF, mem::size_of::<T>()) };
                    t
                };

                // Test with a value initialized with 0xFF.
                f(Box::new(ffs));
            }

            fn with_failing_test_cases<F: Fn(&mut [u8])>(_f: F) {}
        }

        macro_rules! impl_try_from_bytes_testable_for_null_pointer_optimization {
            ($($tys:ty),*) => {
                $(
                    impl TryFromBytesTestable for Option<$tys> {
                        fn with_passing_test_cases<F: Fn(Box<ReadOnly<Self>>)>(f: F) {
                            // Test with a zeroed value.
                            f(Box::new(ReadOnly::new(None)));
                        }

                        fn with_failing_test_cases<F: Fn(&mut [u8])>(f: F) {
                            for pos in 0..mem::size_of::<Self>() {
                                let mut bytes = [0u8; mem::size_of::<Self>()];
                                bytes[pos] = 0x01;
                                f(&mut bytes[..]);
                            }
                        }
                    }
                )*
            };
        }

        // Implements `TryFromBytesTestable`.
        macro_rules! impl_try_from_bytes_testable {
            // Base case for recursion (when the list of types has run out).
            (=> @success $($success_case:expr),* $(, @failure $($failure_case:expr),*)?) => {};
            // Implements for type(s) with no type parameters.
            ($ty:ty $(,$tys:ty)* => @success $($success_case:expr),* $(, @failure $($failure_case:expr),*)?) => {
                impl TryFromBytesTestable for $ty {
                    impl_try_from_bytes_testable!(
                        @methods     @success $($success_case),*
                                 $(, @failure $($failure_case),*)?
                    );
                }
                impl_try_from_bytes_testable!($($tys),* => @success $($success_case),* $(, @failure $($failure_case),*)?);
            };
            // Implements for multiple types with no type parameters.
            ($($($ty:ty),* => @success $($success_case:expr), * $(, @failure $($failure_case:expr),*)?;)*) => {
                $(
                    impl_try_from_bytes_testable!($($ty),* => @success $($success_case),* $(, @failure $($failure_case),*)*);
                )*
            };
            // Implements only the methods; caller must invoke this from inside
            // an impl block.
            (@methods @success $($success_case:expr),* $(, @failure $($failure_case:expr),*)?) => {
                fn with_passing_test_cases<F: Fn(Box<ReadOnly<Self>>)>(_f: F) {
                    $(
                        let bx = Box::<Self>::from($success_case);
                        let ro: Box<ReadOnly<_>> = {
                            let raw = Box::into_raw(bx);
                            // SAFETY: `ReadOnly<T>` has the same layout and bit
                            // validity as `T`.
                            #[allow(clippy::as_conversions)]
                            unsafe { Box::from_raw(raw as *mut _) }
                        };
                        _f(ro);
                    )*
                }

                fn with_failing_test_cases<F: Fn(&mut [u8])>(_f: F) {
                    $($(
                        let mut case = $failure_case;
                        _f(case.as_mut_bytes());
                    )*)?
                }
            };
        }

        impl_try_from_bytes_testable_for_null_pointer_optimization!(
            Box<UnsafeCell<NotZerocopy>>,
            &'static UnsafeCell<NotZerocopy>,
            &'static mut UnsafeCell<NotZerocopy>,
            NonNull<UnsafeCell<NotZerocopy>>,
            fn(),
            FnManyArgs,
            extern "C" fn(),
            ECFnManyArgs
        );

        macro_rules! bx {
            ($e:expr) => {
                Box::new($e)
            };
        }

        // Note that these impls are only for types which are not `FromBytes`.
        // `FromBytes` types are covered by a preceding blanket impl.
        impl_try_from_bytes_testable!(
            bool => @success true, false,
                    @failure 2u8, 3u8, 0xFFu8;
            char => @success '\u{0}', '\u{D7FF}', '\u{E000}', '\u{10FFFF}',
                    @failure 0xD800u32, 0xDFFFu32, 0x110000u32;
            str  => @success "", "hello", "❤️🧡💛💚💙💜",
                    @failure [0, 159, 146, 150];
            [u8] => @success vec![].into_boxed_slice(), vec![0, 1, 2].into_boxed_slice();
            NonZeroU8, NonZeroI8, NonZeroU16, NonZeroI16, NonZeroU32,
            NonZeroI32, NonZeroU64, NonZeroI64, NonZeroU128, NonZeroI128,
            NonZeroUsize, NonZeroIsize
                => @success Self::new(1).unwrap(),
                   // Doing this instead of `0` ensures that we always satisfy
                   // the size and alignment requirements of `Self` (whereas `0`
                   // may be any integer type with a different size or alignment
                   // than some `NonZeroXxx` types).
                   @failure Option::<Self>::None;
            [bool; 0] => @success [];
            [bool; 1]
                => @success [true], [false],
                   @failure [2u8], [3u8], [0xFFu8];
            [bool]
                => @success vec![true, false].into_boxed_slice(), vec![false, true].into_boxed_slice(),
                    @failure [2u8], [3u8], [0xFFu8], [0u8, 1u8, 2u8];
            Unalign<bool>
                => @success Unalign::new(false), Unalign::new(true),
                   @failure 2u8, 0xFFu8;
            ManuallyDrop<bool>
                => @success ManuallyDrop::new(false), ManuallyDrop::new(true),
                   @failure 2u8, 0xFFu8;
            ManuallyDrop<[u8]>
                => @success bx!(ManuallyDrop::new([])), bx!(ManuallyDrop::new([0u8])), bx!(ManuallyDrop::new([0u8, 1u8]));
            ManuallyDrop<[bool]>
                => @success bx!(ManuallyDrop::new([])), bx!(ManuallyDrop::new([false])), bx!(ManuallyDrop::new([false, true])),
                   @failure [2u8], [3u8], [0xFFu8], [0u8, 1u8, 2u8];
            ManuallyDrop<[UnsafeCell<u8>]>
                => @success bx!(ManuallyDrop::new([UnsafeCell::new(0)])), bx!(ManuallyDrop::new([UnsafeCell::new(0), UnsafeCell::new(1)]));
            ManuallyDrop<[UnsafeCell<bool>]>
                => @success bx!(ManuallyDrop::new([UnsafeCell::new(false)])), bx!(ManuallyDrop::new([UnsafeCell::new(false), UnsafeCell::new(true)])),
                @failure [2u8], [3u8], [0xFFu8], [0u8, 1u8, 2u8];
            Wrapping<bool>
                => @success Wrapping(false), Wrapping(true),
                    @failure 2u8, 0xFFu8;
            *const NotZerocopy
                => @success ptr::null::<NotZerocopy>(),
                   @failure [0x01; mem::size_of::<*const NotZerocopy>()];
            *mut NotZerocopy
                => @success ptr::null_mut::<NotZerocopy>(),
                   @failure [0x01; mem::size_of::<*mut NotZerocopy>()];
        );

        // Use the trick described in [1] to allow us to call methods
        // conditional on certain trait bounds.
        //
        // In all of these cases, methods return `Option<R>`, where `R` is the
        // return type of the method we're conditionally calling. The "real"
        // implementations (the ones defined in traits using `&self`) return
        // `Some`, and the default implementations (the ones defined as inherent
        // methods using `&mut self`) return `None`.
        //
        // [1] https://github.com/dtolnay/case-studies/blob/master/autoref-specialization/README.md
        mod autoref_trick {
            use super::*;

            pub(super) struct AutorefWrapper<T: ?Sized>(pub(super) PhantomData<T>);

            pub(super) trait TestIsBitValidShared<T: ?Sized> {
                #[allow(clippy::needless_lifetimes)]
                fn test_is_bit_valid_shared<'ptr>(&self, candidate: Maybe<'ptr, T>)
                    -> Option<bool>;
            }

            impl<T: TryFromBytes + Immutable + ?Sized> TestIsBitValidShared<T> for AutorefWrapper<T> {
                #[allow(clippy::needless_lifetimes)]
                fn test_is_bit_valid_shared<'ptr>(
                    &self,
                    candidate: Maybe<'ptr, T>,
                ) -> Option<bool> {
                    Some(T::is_bit_valid(candidate))
                }
            }

            pub(super) trait TestTryFromRef<T: ?Sized> {
                #[allow(clippy::needless_lifetimes)]
                fn test_try_from_ref<'bytes>(
                    &self,
                    bytes: &'bytes [u8],
                ) -> Option<Option<&'bytes T>>;
            }

            impl<T: TryFromBytes + Immutable + KnownLayout + ?Sized> TestTryFromRef<T> for AutorefWrapper<T> {
                #[allow(clippy::needless_lifetimes)]
                fn test_try_from_ref<'bytes>(
                    &self,
                    bytes: &'bytes [u8],
                ) -> Option<Option<&'bytes T>> {
                    Some(T::try_ref_from_bytes(bytes).ok())
                }
            }

            pub(super) trait TestTryFromMut<T: ?Sized> {
                #[allow(clippy::needless_lifetimes)]
                fn test_try_from_mut<'bytes>(
                    &self,
                    bytes: &'bytes mut [u8],
                ) -> Option<Option<&'bytes mut T>>;
            }

            impl<T: TryFromBytes + IntoBytes + KnownLayout + ?Sized> TestTryFromMut<T> for AutorefWrapper<T> {
                #[allow(clippy::needless_lifetimes)]
                fn test_try_from_mut<'bytes>(
                    &self,
                    bytes: &'bytes mut [u8],
                ) -> Option<Option<&'bytes mut T>> {
                    Some(T::try_mut_from_bytes(bytes).ok())
                }
            }

            pub(super) trait TestTryReadFrom<T> {
                fn test_try_read_from(&self, bytes: &[u8]) -> Option<Option<T>>;
            }

            impl<T: TryFromBytes> TestTryReadFrom<T> for AutorefWrapper<T> {
                fn test_try_read_from(&self, bytes: &[u8]) -> Option<Option<T>> {
                    Some(T::try_read_from_bytes(bytes).ok())
                }
            }

            pub(super) trait TestAsBytes<T: ?Sized> {
                #[allow(clippy::needless_lifetimes)]
                fn test_as_bytes<'slf, 't>(&'slf self, t: &'t ReadOnly<T>) -> Option<&'t [u8]>;
            }

            impl<T: IntoBytes + Immutable + ?Sized> TestAsBytes<T> for AutorefWrapper<T> {
                #[allow(clippy::needless_lifetimes)]
                fn test_as_bytes<'slf, 't>(&'slf self, t: &'t ReadOnly<T>) -> Option<&'t [u8]> {
                    Some(t.as_bytes())
                }
            }
        }

        use autoref_trick::*;

        // Asserts that `$ty` is one of a list of types which are allowed to not
        // provide a "real" implementation for `$fn_name`. Since the
        // `autoref_trick` machinery fails silently, this allows us to ensure
        // that the "default" impls are only being used for types which we
        // expect.
        //
        // Note that, since this is a runtime test, it is possible to have an
        // allowlist which is too restrictive if the function in question is
        // never called for a particular type. For example, if `as_bytes` is not
        // supported for a particular type, and so `test_as_bytes` returns
        // `None`, methods such as `test_try_from_ref` may never be called for
        // that type. As a result, it's possible that, for example, adding
        // `as_bytes` support for a type would cause other allowlist assertions
        // to fail. This means that allowlist assertion failures should not
        // automatically be taken as a sign of a bug.
        macro_rules! assert_on_allowlist {
            ($fn_name:ident($ty:ty) $(: $($tys:ty),*)?) => {{
                use core::any::TypeId;

                let allowlist: &[TypeId] = &[ $($(TypeId::of::<$tys>()),*)? ];
                let allowlist_names: &[&str] = &[ $($(stringify!($tys)),*)? ];

                let id = TypeId::of::<$ty>();
                assert!(allowlist.contains(&id), "{} is not on allowlist for {}: {:?}", stringify!($ty), stringify!($fn_name), allowlist_names);
            }};
        }

        // Asserts that `$ty` implements any `$trait` and doesn't implement any
        // `!$trait`. Note that all `$trait`s must come before any `!$trait`s.
        //
        // For `T: TryFromBytes`, uses `TryFromBytesTestable` to test success
        // and failure cases.
        macro_rules! assert_impls {
            ($ty:ty: TryFromBytes) => {
                // "Default" implementations that match the "real"
                // implementations defined in the `autoref_trick` module above.
                #[allow(unused, non_local_definitions)]
                impl AutorefWrapper<$ty> {
                    #[allow(clippy::needless_lifetimes)]
                    fn test_is_bit_valid_shared<'ptr>(
                        &mut self,
                        candidate: Maybe<'ptr, $ty>,
                    ) -> Option<bool> {
                        assert_on_allowlist!(
                            test_is_bit_valid_shared($ty):
                            ManuallyDrop<UnsafeCell<()>>,
                            ManuallyDrop<[UnsafeCell<u8>]>,
                            ManuallyDrop<[UnsafeCell<bool>]>,
                            CoreMaybeUninit<NotZerocopy>,
                            CoreMaybeUninit<UnsafeCell<()>>,
                            Wrapping<UnsafeCell<()>>
                        );

                        None
                    }

                    #[allow(clippy::needless_lifetimes)]
                    fn test_try_from_ref<'bytes>(&mut self, _bytes: &'bytes [u8]) -> Option<Option<&'bytes $ty>> {
                        assert_on_allowlist!(
                            test_try_from_ref($ty):
                            ManuallyDrop<[UnsafeCell<bool>]>
                        );

                        None
                    }

                    #[allow(clippy::needless_lifetimes)]
                    fn test_try_from_mut<'bytes>(&mut self, _bytes: &'bytes mut [u8]) -> Option<Option<&'bytes mut $ty>> {
                        assert_on_allowlist!(
                            test_try_from_mut($ty):
                            Option<Box<UnsafeCell<NotZerocopy>>>,
                            Option<&'static UnsafeCell<NotZerocopy>>,
                            Option<&'static mut UnsafeCell<NotZerocopy>>,
                            Option<NonNull<UnsafeCell<NotZerocopy>>>,
                            Option<fn()>,
                            Option<FnManyArgs>,
                            Option<extern "C" fn()>,
                            Option<ECFnManyArgs>,
                            *const NotZerocopy,
                            *mut NotZerocopy
                        );

                        None
                    }

                    fn test_try_read_from(&mut self, _bytes: &[u8]) -> Option<Option<&$ty>> {
                        assert_on_allowlist!(
                            test_try_read_from($ty):
                            str,
                            ManuallyDrop<[u8]>,
                            ManuallyDrop<[bool]>,
                            ManuallyDrop<[UnsafeCell<bool>]>,
                            [u8],
                            [bool]
                        );

                        None
                    }

                    fn test_as_bytes(&mut self, _t: &ReadOnly<$ty>) -> Option<&[u8]> {
                        assert_on_allowlist!(
                            test_as_bytes($ty):
                            Option<&'static UnsafeCell<NotZerocopy>>,
                            Option<&'static mut UnsafeCell<NotZerocopy>>,
                            Option<NonNull<UnsafeCell<NotZerocopy>>>,
                            Option<Box<UnsafeCell<NotZerocopy>>>,
                            Option<fn()>,
                            Option<FnManyArgs>,
                            Option<extern "C" fn()>,
                            Option<ECFnManyArgs>,
                            CoreMaybeUninit<u8>,
                            CoreMaybeUninit<NotZerocopy>,
                            CoreMaybeUninit<UnsafeCell<()>>,
                            ManuallyDrop<UnsafeCell<()>>,
                            ManuallyDrop<[UnsafeCell<u8>]>,
                            ManuallyDrop<[UnsafeCell<bool>]>,
                            Wrapping<UnsafeCell<()>>,
                            *const NotZerocopy,
                            *mut NotZerocopy
                        );

                        None
                    }
                }

                <$ty as TryFromBytesTestable>::with_passing_test_cases(|mut val| {
                    // FIXME(#494): These tests only get exercised for types
                    // which are `IntoBytes`. Once we implement #494, we should
                    // be able to support non-`IntoBytes` types by zeroing
                    // padding.

                    // We define `w` and `ww` since, in the case of the inherent
                    // methods, Rust thinks they're both borrowed mutably at the
                    // same time (given how we use them below). If we just
                    // defined a single `w` and used it for multiple operations,
                    // this would conflict.
                    //
                    // We `#[allow(unused_mut]` for the cases where the "real"
                    // impls are used, which take `&self`.
                    #[allow(unused_mut)]
                    let (mut w, mut ww) = (AutorefWrapper::<$ty>(PhantomData), AutorefWrapper::<$ty>(PhantomData));

                    let c = Ptr::from_ref(&*val);
                    let c = c.forget_aligned();
                    // SAFETY: FIXME(#899): This is unsound. `$ty` is not
                    // necessarily `IntoBytes`, but that's the corner we've
                    // backed ourselves into by using `Ptr::from_ref`.
                    let c = unsafe { c.assume_initialized() };
                    let res = w.test_is_bit_valid_shared(c);
                    if let Some(res) = res {
                        assert!(res, "{}::is_bit_valid (shared `Ptr`): got false, expected true", stringify!($ty));
                    }

                    let c = Ptr::from_mut(&mut *val);
                    let c = c.forget_aligned();
                    // SAFETY: FIXME(#899): This is unsound. `$ty` is not
                    // necessarily `IntoBytes`, but that's the corner we've
                    // backed ourselves into by using `Ptr::from_ref`.
                    let mut c = unsafe { c.assume_initialized() };
                    let res = <$ty as TryFromBytes>::is_bit_valid(c.reborrow_shared());
                    assert!(res, "{}::is_bit_valid (exclusive `Ptr`): got false, expected true", stringify!($ty));

                    // `bytes` is `Some(val.as_bytes())` if `$ty: IntoBytes +
                    // Immutable` and `None` otherwise.
                    let bytes = w.test_as_bytes(&*val);

                    // The inner closure returns
                    // `Some($ty::try_ref_from_bytes(bytes))` if `$ty:
                    // Immutable` and `None` otherwise.
                    let res = bytes.and_then(|bytes| ww.test_try_from_ref(bytes));
                    if let Some(res) = res {
                        assert!(res.is_some(), "{}::try_ref_from_bytes: got `None`, expected `Some`", stringify!($ty));
                    }

                    if let Some(bytes) = bytes {
                        // We need to get a mutable byte slice, and so we clone
                        // into a `Vec`. However, we also need these bytes to
                        // satisfy `$ty`'s alignment requirement, which isn't
                        // guaranteed for `Vec<u8>`. In order to get around
                        // this, we create a `Vec` which is twice as long as we
                        // need. There is guaranteed to be an aligned byte range
                        // of size `size_of_val(val)` within that range.
                        let val = &*val;
                        let size = mem::size_of_val(val);
                        let align = mem::align_of_val(val);

                        let mut vec = bytes.to_vec();
                        vec.extend(bytes);
                        let slc = vec.as_slice();
                        let offset = slc.as_ptr().align_offset(align);
                        let bytes_mut = &mut vec.as_mut_slice()[offset..offset+size];
                        bytes_mut.copy_from_slice(bytes);

                        let res = ww.test_try_from_mut(bytes_mut);
                        if let Some(res) = res {
                            assert!(res.is_some(), "{}::try_mut_from_bytes: got `None`, expected `Some`", stringify!($ty));
                        }
                    }

                    let res = bytes.and_then(|bytes| ww.test_try_read_from(bytes));
                    if let Some(res) = res {
                        assert!(res.is_some(), "{}::try_read_from_bytes: got `None`, expected `Some`", stringify!($ty));
                    }
                });
                #[allow(clippy::as_conversions)]
                <$ty as TryFromBytesTestable>::with_failing_test_cases(|c| {
                    #[allow(unused_mut)] // For cases where the "real" impls are used, which take `&self`.
                    let mut w = AutorefWrapper::<$ty>(PhantomData);

                    // This is `Some($ty::try_ref_from_bytes(c))` if `$ty:
                    // Immutable` and `None` otherwise.
                    let res = w.test_try_from_ref(c);
                    if let Some(res) = res {
                        assert!(res.is_none(), "{}::try_ref_from_bytes({:?}): got Some, expected None", stringify!($ty), c);
                    }

                    let res = w.test_try_from_mut(c);
                    if let Some(res) = res {
                        assert!(res.is_none(), "{}::try_mut_from_bytes({:?}): got Some, expected None", stringify!($ty), c);
                    }


                    let res = w.test_try_read_from(c);
                    if let Some(res) = res {
                        assert!(res.is_none(), "{}::try_read_from_bytes({:?}): got Some, expected None", stringify!($ty), c);
                    }
                });

                #[allow(dead_code)]
                const _: () = { static_assertions::assert_impl_all!($ty: TryFromBytes); };
            };
            ($ty:ty: $trait:ident) => {
                #[allow(dead_code)]
                const _: () = { static_assertions::assert_impl_all!($ty: $trait); };
            };
            ($ty:ty: !$trait:ident) => {
                #[allow(dead_code)]
                const _: () = { static_assertions::assert_not_impl_any!($ty: $trait); };
            };
            ($ty:ty: $($trait:ident),* $(,)? $(!$negative_trait:ident),*) => {
                $(
                    assert_impls!($ty: $trait);
                )*

                $(
                    assert_impls!($ty: !$negative_trait);
                )*
            };
        }

        // NOTE: The negative impl assertions here are not necessarily
        // prescriptive. They merely serve as change detectors to make sure
        // we're aware of what trait impls are getting added with a given
        // change. Of course, some impls would be invalid (e.g., `bool:
        // FromBytes`), and so this change detection is very important.

        assert_impls!(
            (): KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            Unaligned
        );
        assert_impls!(
            u8: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            Unaligned
        );
        assert_impls!(
            i8: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            Unaligned
        );
        assert_impls!(
            u16: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            i16: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            u32: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            i32: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            u64: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            i64: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            u128: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            i128: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            usize: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            isize: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        #[cfg(feature = "float-nightly")]
        assert_impls!(
            f16: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            f32: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            f64: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        #[cfg(feature = "float-nightly")]
        assert_impls!(
            f128: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            !Unaligned
        );
        assert_impls!(
            bool: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            IntoBytes,
            Unaligned,
            !FromBytes
        );
        assert_impls!(
            char: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );
        assert_impls!(
            str: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            IntoBytes,
            Unaligned,
            !FromBytes
        );

        assert_impls!(
            NonZeroU8: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            Unaligned,
            !FromZeros,
            !FromBytes
        );
        assert_impls!(
            NonZeroI8: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            Unaligned,
            !FromZeros,
            !FromBytes
        );
        assert_impls!(
            NonZeroU16: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );
        assert_impls!(
            NonZeroI16: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );
        assert_impls!(
            NonZeroU32: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );
        assert_impls!(
            NonZeroI32: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );
        assert_impls!(
            NonZeroU64: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );
        assert_impls!(
            NonZeroI64: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );
        assert_impls!(
            NonZeroU128: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );
        assert_impls!(
            NonZeroI128: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );
        assert_impls!(
            NonZeroUsize: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );
        assert_impls!(
            NonZeroIsize: KnownLayout,
            Immutable,
            TryFromBytes,
            IntoBytes,
            !FromBytes,
            !Unaligned
        );

        assert_impls!(Option<NonZeroU8>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
        assert_impls!(Option<NonZeroI8>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
        assert_impls!(Option<NonZeroU16>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned);
        assert_impls!(Option<NonZeroI16>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned);
        assert_impls!(Option<NonZeroU32>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned);
        assert_impls!(Option<NonZeroI32>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned);
        assert_impls!(Option<NonZeroU64>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned);
        assert_impls!(Option<NonZeroI64>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned);
        assert_impls!(Option<NonZeroU128>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned);
        assert_impls!(Option<NonZeroI128>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned);
        assert_impls!(Option<NonZeroUsize>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned);
        assert_impls!(Option<NonZeroIsize>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned);

        // Implements none of the ZC traits.
        struct NotZerocopy;

        #[rustfmt::skip]
        type FnManyArgs = fn(
            NotZerocopy, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8,
        ) -> (NotZerocopy, NotZerocopy);

        // Allowed, because we're not actually using this type for FFI.
        #[allow(improper_ctypes_definitions)]
        #[rustfmt::skip]
        type ECFnManyArgs = extern "C" fn(
            NotZerocopy, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8,
        ) -> (NotZerocopy, NotZerocopy);

        #[cfg(feature = "alloc")]
        assert_impls!(Option<Box<UnsafeCell<NotZerocopy>>>: KnownLayout, Immutable, TryFromBytes, FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<Box<[UnsafeCell<NotZerocopy>]>>: KnownLayout, !Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<&'static UnsafeCell<NotZerocopy>>: KnownLayout, Immutable, TryFromBytes, FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<&'static [UnsafeCell<NotZerocopy>]>: KnownLayout, Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<&'static mut UnsafeCell<NotZerocopy>>: KnownLayout, Immutable, TryFromBytes, FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<&'static mut [UnsafeCell<NotZerocopy>]>: KnownLayout, Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<NonNull<UnsafeCell<NotZerocopy>>>: KnownLayout, TryFromBytes, FromZeros, Immutable, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<NonNull<[UnsafeCell<NotZerocopy>]>>: KnownLayout, Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<fn()>: KnownLayout, Immutable, TryFromBytes, FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<FnManyArgs>: KnownLayout, Immutable, TryFromBytes, FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<extern "C" fn()>: KnownLayout, Immutable, TryFromBytes, FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Option<ECFnManyArgs>: KnownLayout, Immutable, TryFromBytes, FromZeros, !FromBytes, !IntoBytes, !Unaligned);

        assert_impls!(PhantomData<NotZerocopy>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
        assert_impls!(PhantomData<UnsafeCell<()>>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
        assert_impls!(PhantomData<[u8]>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);

        assert_impls!(ManuallyDrop<u8>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
        // This test is important because it allows us to test our hand-rolled
        // implementation of `<ManuallyDrop<T> as TryFromBytes>::is_bit_valid`.
        assert_impls!(ManuallyDrop<bool>: KnownLayout, Immutable, TryFromBytes, FromZeros, IntoBytes, Unaligned, !FromBytes);
        assert_impls!(ManuallyDrop<[u8]>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
        // This test is important because it allows us to test our hand-rolled
        // implementation of `<ManuallyDrop<T> as TryFromBytes>::is_bit_valid`.
        assert_impls!(ManuallyDrop<[bool]>: KnownLayout, Immutable, TryFromBytes, FromZeros, IntoBytes, Unaligned, !FromBytes);
        assert_impls!(ManuallyDrop<NotZerocopy>: !Immutable, !TryFromBytes, !KnownLayout, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(ManuallyDrop<[NotZerocopy]>: KnownLayout, !Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(ManuallyDrop<UnsafeCell<()>>: KnownLayout, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned, !Immutable);
        assert_impls!(ManuallyDrop<[UnsafeCell<u8>]>: KnownLayout, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned, !Immutable);
        assert_impls!(ManuallyDrop<[UnsafeCell<bool>]>: KnownLayout, TryFromBytes, FromZeros, IntoBytes, Unaligned, !Immutable, !FromBytes);

        assert_impls!(CoreMaybeUninit<u8>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, Unaligned, !IntoBytes);
        assert_impls!(CoreMaybeUninit<NotZerocopy>: KnownLayout, TryFromBytes, FromZeros, FromBytes, !Immutable, !IntoBytes, !Unaligned);
        assert_impls!(CoreMaybeUninit<UnsafeCell<()>>: KnownLayout, TryFromBytes, FromZeros, FromBytes, Unaligned, !Immutable, !IntoBytes);

        assert_impls!(Wrapping<u8>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
        // This test is important because it allows us to test our hand-rolled
        // implementation of `<Wrapping<T> as TryFromBytes>::is_bit_valid`.
        assert_impls!(Wrapping<bool>: KnownLayout, Immutable, TryFromBytes, FromZeros, IntoBytes, Unaligned, !FromBytes);
        assert_impls!(Wrapping<NotZerocopy>: KnownLayout, !Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(Wrapping<UnsafeCell<()>>: KnownLayout, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned, !Immutable);

        assert_impls!(Unalign<u8>: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, Unaligned);
        // This test is important because it allows us to test our hand-rolled
        // implementation of `<Unalign<T> as TryFromBytes>::is_bit_valid`.
        assert_impls!(Unalign<bool>: KnownLayout, Immutable, TryFromBytes, FromZeros, IntoBytes, Unaligned, !FromBytes);
        assert_impls!(Unalign<NotZerocopy>: KnownLayout, Unaligned, !Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes);

        assert_impls!(
            [u8]: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            Unaligned
        );
        assert_impls!(
            [bool]: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            IntoBytes,
            Unaligned,
            !FromBytes
        );
        assert_impls!([NotZerocopy]: KnownLayout, !Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(
            [u8; 0]: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            Unaligned,
        );
        assert_impls!(
            [NotZerocopy; 0]: KnownLayout,
            !Immutable,
            !TryFromBytes,
            !FromZeros,
            !FromBytes,
            !IntoBytes,
            !Unaligned
        );
        assert_impls!(
            [u8; 1]: KnownLayout,
            Immutable,
            TryFromBytes,
            FromZeros,
            FromBytes,
            IntoBytes,
            Unaligned,
        );
        assert_impls!(
            [NotZerocopy; 1]: KnownLayout,
            !Immutable,
            !TryFromBytes,
            !FromZeros,
            !FromBytes,
            !IntoBytes,
            !Unaligned
        );

        assert_impls!(*const NotZerocopy: KnownLayout, Immutable, TryFromBytes, FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(*mut NotZerocopy: KnownLayout, Immutable, TryFromBytes, FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(*const [NotZerocopy]: KnownLayout, Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(*mut [NotZerocopy]: KnownLayout, Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(*const dyn Debug: KnownLayout, Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);
        assert_impls!(*mut dyn Debug: KnownLayout, Immutable, !TryFromBytes, !FromZeros, !FromBytes, !IntoBytes, !Unaligned);

        #[cfg(feature = "simd")]
        {
            #[allow(unused_macros)]
            macro_rules! test_simd_arch_mod {
                ($arch:ident, $($typ:ident),*) => {
                    {
                        use core::arch::$arch::{$($typ),*};
                        use crate::*;
                        $( assert_impls!($typ: KnownLayout, Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes, !Unaligned); )*
                    }
                };
            }
            #[cfg(target_arch = "x86")]
            test_simd_arch_mod!(x86, __m128, __m128d, __m128i, __m256, __m256d, __m256i);

            #[cfg(all(not(no_zerocopy_simd_x86_avx12_1_89_0), target_arch = "x86"))]
            test_simd_arch_mod!(x86, __m512bh, __m512, __m512d, __m512i);

            #[cfg(target_arch = "x86_64")]
            test_simd_arch_mod!(x86_64, __m128, __m128d, __m128i, __m256, __m256d, __m256i);

            #[cfg(all(not(no_zerocopy_simd_x86_avx12_1_89_0), target_arch = "x86_64"))]
            test_simd_arch_mod!(x86_64, __m512bh, __m512, __m512d, __m512i);

            #[cfg(target_arch = "wasm32")]
            test_simd_arch_mod!(wasm32, v128);

            #[cfg(all(feature = "simd-nightly", target_arch = "powerpc"))]
            test_simd_arch_mod!(
                powerpc,
                vector_bool_long,
                vector_double,
                vector_signed_long,
                vector_unsigned_long
            );

            #[cfg(all(feature = "simd-nightly", target_arch = "powerpc64"))]
            test_simd_arch_mod!(
                powerpc64,
                vector_bool_long,
                vector_double,
                vector_signed_long,
                vector_unsigned_long
            );
            #[cfg(all(target_arch = "aarch64", not(no_zerocopy_aarch64_simd_1_59_0)))]
            #[rustfmt::skip]
            test_simd_arch_mod!(
                aarch64, float32x2_t, float32x4_t, float64x1_t, float64x2_t, int8x8_t, int8x8x2_t,
                int8x8x3_t, int8x8x4_t, int8x16_t, int8x16x2_t, int8x16x3_t, int8x16x4_t, int16x4_t,
                int16x8_t, int32x2_t, int32x4_t, int64x1_t, int64x2_t, poly8x8_t, poly8x8x2_t, poly8x8x3_t,
                poly8x8x4_t, poly8x16_t, poly8x16x2_t, poly8x16x3_t, poly8x16x4_t, poly16x4_t, poly16x8_t,
                poly64x1_t, poly64x2_t, uint8x8_t, uint8x8x2_t, uint8x8x3_t, uint8x8x4_t, uint8x16_t,
                uint8x16x2_t, uint8x16x3_t, uint8x16x4_t, uint16x4_t, uint16x4x2_t, uint16x4x3_t,
                uint16x4x4_t, uint16x8_t, uint32x2_t, uint32x4_t, uint64x1_t, uint64x2_t
            );
        }
    }
}
