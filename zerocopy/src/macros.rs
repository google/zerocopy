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

/// Safely transmutes a value of one type to a value of another type of the same
/// size.
///
/// This macro behaves like an invocation of this function:
///
/// ```ignore
/// const fn transmute<Src, Dst>(src: Src) -> Dst
/// where
///     Src: IntoBytes,
///     Dst: FromBytes,
///     size_of::<Src>() == size_of::<Dst>(),
/// {
/// # /*
///     ...
/// # */
/// }
/// ```
///
/// However, unlike a function, this macro can only be invoked when the types of
/// `Src` and `Dst` are completely concrete. The types `Src` and `Dst` are
/// inferred from the calling context; they cannot be explicitly specified in
/// the macro invocation.
///
/// Note that the `Src` produced by the expression `$e` will *not* be dropped.
/// Semantically, its bits will be copied into a new value of type `Dst`, the
/// original `Src` will be forgotten, and the value of type `Dst` will be
/// returned.
///
/// # `#![allow(shrink)]`
///
/// If `#![allow(shrink)]` is provided, `transmute!` additionally supports
/// transmutations that shrink the size of the value; e.g.:
///
/// ```
/// # use zerocopy::transmute;
/// let u: u32 = transmute!(#![allow(shrink)] 0u64);
/// assert_eq!(u, 0u32);
/// ```
///
/// # Examples
///
/// ```
/// # use zerocopy::transmute;
/// let one_dimensional: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
///
/// let two_dimensional: [[u8; 4]; 2] = transmute!(one_dimensional);
///
/// assert_eq!(two_dimensional, [[0, 1, 2, 3], [4, 5, 6, 7]]);
/// ```
///
/// # Use in `const` contexts
///
/// This macro can be invoked in `const` contexts.
///
#[doc = codegen_section!(
    header = "h2",
    bench = "transmute",
    format = "coco_static_size",
)]
#[macro_export]
macro_rules! transmute {
    // NOTE: This must be a macro (rather than a function with trait bounds)
    // because there's no way, in a generic context, to enforce that two types
    // have the same size. `core::mem::transmute` uses compiler magic to enforce
    // this so long as the types are concrete.
    (#![allow(shrink)] $e:expr) => {{
        let mut e = $e;
        if false {
            // This branch, though never taken, ensures that the type of `e` is
            // `IntoBytes` and that the type of the  outer macro invocation
            // expression is `FromBytes`.

            fn transmute<Src, Dst>(src: Src) -> Dst
            where
                Src: $crate::IntoBytes,
                Dst: $crate::FromBytes,
            {
                let _ = src;
                loop {}
            }
            loop {}
            #[allow(unreachable_code)]
            transmute(e)
        } else {
            use $crate::util::macro_util::core_reexport::mem::ManuallyDrop;

            // NOTE: `repr(packed)` is important! It ensures that the size of
            // `Transmute` won't be rounded up to accommodate `Src`'s or `Dst`'s
            // alignment, which would break the size comparison logic below.
            //
            // As an example of why this is problematic, consider `Src = [u8;
            // 5]`, `Dst = u32`. The total size of `Transmute<Src, Dst>` would
            // be 8, and so we would reject a `[u8; 5]` to `u32` transmute as
            // being size-increasing, which it isn't.
            #[repr(C, packed)]
            union Transmute<Src, Dst> {
                src: ManuallyDrop<Src>,
                dst: ManuallyDrop<Dst>,
            }

            // SAFETY: `Transmute` is a `repr(C)` union whose `src` field has
            // type `ManuallyDrop<Src>`. Thus, the `src` field starts at byte
            // offset 0 within `Transmute` [1]. `ManuallyDrop<T>` has the same
            // layout and bit validity as `T`, so it is sound to transmute `Src`
            // to `Transmute`.
            //
            // [1] https://doc.rust-lang.org/1.85.0/reference/type-layout.html#reprc-unions
            //
            // [2] Per https://doc.rust-lang.org/1.85.0/std/mem/struct.ManuallyDrop.html:
            //
            //   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
            //   validity as `T`
            let u: Transmute<_, _> = unsafe {
                // Clippy: We can't annotate the types; this macro is designed
                // to infer the types from the calling context.
                #[allow(clippy::missing_transmute_annotations)]
                $crate::util::macro_util::core_reexport::mem::transmute(e)
            };

            if false {
                // SAFETY: This code is never executed.
                e = ManuallyDrop::into_inner(unsafe { u.src });
                // Suppress the `unused_assignments` lint on the previous line.
                let _ = e;
                loop {}
            } else {
                // SAFETY: Per the safety comment on `let u` above, the `dst`
                // field in `Transmute` starts at byte offset 0, and has the
                // same layout and bit validity as `Dst`.
                //
                // Transmuting `Src` to `Transmute<Src, Dst>` above using
                // `core::mem::transmute` ensures that `size_of::<Src>() ==
                // size_of::<Transmute<Src, Dst>>()`. A `#[repr(C, packed)]`
                // union has the maximum size of all of its fields [1], so this
                // is equivalent to `size_of::<Src>() >= size_of::<Dst>()`.
                //
                // The outer `if`'s `false` branch ensures that `Src: IntoBytes`
                // and `Dst: FromBytes`. This, combined with the size bound,
                // ensures that this transmute is sound.
                //
                // [1] Per https://doc.rust-lang.org/1.85.0/reference/type-layout.html#reprc-unions:
                //
                //   The union will have a size of the maximum size of all of
                //   its fields rounded to its alignment
                let dst = unsafe { u.dst };
                $crate::util::macro_util::must_use(ManuallyDrop::into_inner(dst))
            }
        }
    }};
    ($e:expr) => {{
        let e = $e;
        if false {
            // This branch, though never taken, ensures that the type of `e` is
            // `IntoBytes` and that the type of the  outer macro invocation
            // expression is `FromBytes`.

            fn transmute<Src, Dst>(src: Src) -> Dst
            where
                Src: $crate::IntoBytes,
                Dst: $crate::FromBytes,
            {
                let _ = src;
                loop {}
            }
            loop {}
            #[allow(unreachable_code)]
            transmute(e)
        } else {
            // SAFETY: `core::mem::transmute` ensures that the type of `e` and
            // the type of this macro invocation expression have the same size.
            // We know this transmute is safe thanks to the `IntoBytes` and
            // `FromBytes` bounds enforced by the `false` branch.
            let u = unsafe {
                // Clippy: We can't annotate the types; this macro is designed
                // to infer the types from the calling context.
                #[allow(clippy::missing_transmute_annotations, unnecessary_transmutes)]
                $crate::util::macro_util::core_reexport::mem::transmute(e)
            };
            $crate::util::macro_util::must_use(u)
        }
    }};
}

/// Safely transmutes a mutable or immutable reference of one type to an
/// immutable reference of another type of the same size and compatible
/// alignment.
///
/// This macro behaves like an invocation of this function:
///
/// ```ignore
/// fn transmute_ref<'src, 'dst, Src, Dst>(src: &'src Src) -> &'dst Dst
/// where
///     'src: 'dst,
///     Src: IntoBytes + Immutable + ?Sized,
///     Dst: FromBytes + Immutable + ?Sized,
///     align_of::<Src>() >= align_of::<Dst>(),
///     size_compatible::<Src, Dst>(),
/// {
/// # /*
///     ...
/// # */
/// }
/// ```
///
/// The types `Src` and `Dst` are inferred from the calling context; they cannot
/// be explicitly specified in the macro invocation.
///
/// # Size compatibility
///
/// `transmute_ref!` supports transmuting between `Sized` types, between unsized
/// (i.e., `?Sized`) types, and from a `Sized` type to an unsized type. It
/// supports any transmutation that preserves the number of bytes of the
/// referent, even if doing so requires updating the metadata stored in an
/// unsized "fat" reference:
///
/// ```
/// # use zerocopy::transmute_ref;
/// # use core::mem::size_of_val; // Not in the prelude on our MSRV
/// let src: &[[u8; 2]] = &[[0, 1], [2, 3]][..];
/// let dst: &[u8] = transmute_ref!(src);
///
/// assert_eq!(src.len(), 2);
/// assert_eq!(dst.len(), 4);
/// assert_eq!(dst, [0, 1, 2, 3]);
/// assert_eq!(size_of_val(src), size_of_val(dst));
/// ```
///
/// # Errors
///
/// Violations of the alignment and size compatibility checks are detected
/// *after* the compiler performs monomorphization. This has two important
/// consequences.
///
/// First, it means that generic code will *never* fail these conditions:
///
/// ```
/// # use zerocopy::{transmute_ref, FromBytes, IntoBytes, Immutable};
/// fn transmute_ref<Src, Dst>(src: &Src) -> &Dst
/// where
///     Src: IntoBytes + Immutable,
///     Dst: FromBytes + Immutable,
/// {
///     transmute_ref!(src)
/// }
/// ```
///
/// Instead, failures will only be detected once generic code is instantiated
/// with concrete types:
///
/// ```compile_fail,E0080
/// # use zerocopy::{transmute_ref, FromBytes, IntoBytes, Immutable};
/// #
/// # fn transmute_ref<Src, Dst>(src: &Src) -> &Dst
/// # where
/// #     Src: IntoBytes + Immutable,
/// #     Dst: FromBytes + Immutable,
/// # {
/// #     transmute_ref!(src)
/// # }
/// let src: &u16 = &0;
/// let dst: &u8 = transmute_ref(src);
/// ```
///
/// Second, the fact that violations are detected after monomorphization means
/// that `cargo check` will usually not detect errors, even when types are
/// concrete. Instead, `cargo build` must be used to detect such errors.
///
/// # Examples
///
/// Transmuting between `Sized` types:
///
/// ```
/// # use zerocopy::transmute_ref;
/// let one_dimensional: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
///
/// let two_dimensional: &[[u8; 4]; 2] = transmute_ref!(&one_dimensional);
///
/// assert_eq!(two_dimensional, &[[0, 1, 2, 3], [4, 5, 6, 7]]);
/// ```
///
/// Transmuting between unsized types:
///
/// ```
/// # use {zerocopy::*, zerocopy_derive::*};
/// # type u16 = zerocopy::byteorder::native_endian::U16;
/// # type u32 = zerocopy::byteorder::native_endian::U32;
/// #[derive(KnownLayout, FromBytes, IntoBytes, Immutable)]
/// #[repr(C)]
/// struct SliceDst<T, U> {
///     t: T,
///     u: [U],
/// }
///
/// type Src = SliceDst<u32, u16>;
/// type Dst = SliceDst<u16, u8>;
///
/// let src = Src::ref_from_bytes(&[0, 1, 2, 3, 4, 5, 6, 7]).unwrap();
/// let dst: &Dst = transmute_ref!(src);
///
/// assert_eq!(src.t.as_bytes(), [0, 1, 2, 3]);
/// assert_eq!(src.u.len(), 2);
/// assert_eq!(src.u.as_bytes(), [4, 5, 6, 7]);
///
/// assert_eq!(dst.t.as_bytes(), [0, 1]);
/// assert_eq!(dst.u, [2, 3, 4, 5, 6, 7]);
/// ```
///
/// # Use in `const` contexts
///
/// This macro can be invoked in `const` contexts only when `Src: Sized` and
/// `Dst: Sized`.
///
#[doc = codegen_section!(
    header = "h2",
    bench = "transmute_ref",
    format = "coco",
    arity = 2,
    [
        open
        @index 1
        @title "Sized"
        @variant "static_size"
    ],
    [
        @index 2
        @title "Unsized"
        @variant "dynamic_size"
    ]
)]
#[macro_export]
macro_rules! transmute_ref {
    ($e:expr) => {{
        // NOTE: This must be a macro (rather than a function with trait bounds)
        // because there's no way, in a generic context, to enforce that two
        // types have the same size or alignment.

        // Ensure that the source type is a reference or a mutable reference
        // (note that mutable references are implicitly reborrowed here).
        let e: &_ = $e;

        #[allow(unused, clippy::diverging_sub_expression)]
        if false {
            // This branch, though never taken, ensures that the type of `e` is
            // `&T` where `T: IntoBytes + Immutable`, and that the type of this
            // macro expression is `&U` where `U: FromBytes + Immutable`.

            struct AssertSrcIsIntoBytes<'a, T: ?::core::marker::Sized + $crate::IntoBytes>(&'a T);
            struct AssertSrcIsImmutable<'a, T: ?::core::marker::Sized + $crate::Immutable>(&'a T);
            struct AssertDstIsFromBytes<'a, U: ?::core::marker::Sized + $crate::FromBytes>(&'a U);
            struct AssertDstIsImmutable<'a, T: ?::core::marker::Sized + $crate::Immutable>(&'a T);

            let _ = AssertSrcIsIntoBytes(e);
            let _ = AssertSrcIsImmutable(e);

            if true {
                #[allow(unused, unreachable_code)]
                let u = AssertDstIsFromBytes(loop {});
                u.0
            } else {
                #[allow(unused, unreachable_code)]
                let u = AssertDstIsImmutable(loop {});
                u.0
            }
        } else {
            use $crate::util::macro_util::TransmuteRefDst;
            let t = $crate::util::macro_util::Wrap::new(e);

            if false {
                // This branch exists solely to force the compiler to infer the
                // type of `Dst` *before* it attempts to resolve the method call
                // to `transmute_ref` in the `else` branch.
                //
                // Without this, if `Src` is `Sized` but `Dst` is `!Sized`, the
                // compiler will eagerly select the inherent impl of
                // `transmute_ref` (which requires `Dst: Sized`) because inherent
                // methods take priority over trait methods. It does this before
                // it realizes `Dst` is `!Sized`, leading to a compile error when
                // it checks the bounds later.
                //
                // By calling this helper (which returns `&Dst`), we force `Dst`
                // to be fully resolved. By the time it gets to the `else`
                // branch, the compiler knows `Dst` is `!Sized`, properly
                // disqualifies the inherent method, and falls back to the trait
                // implementation.
                t.transmute_ref_inference_helper()
            } else {
                // SAFETY: The outer `if false` branch ensures that:
                // - `Src: IntoBytes + Immutable`
                // - `Dst: FromBytes + Immutable`
                unsafe {
                    t.transmute_ref()
                }
            }
        }
    }}
}

/// Safely transmutes a mutable reference of one type to a mutable reference of
/// another type of the same size and compatible alignment.
///
/// This macro behaves like an invocation of this function:
///
/// ```ignore
/// const fn transmute_mut<'src, 'dst, Src, Dst>(src: &'src mut Src) -> &'dst mut Dst
/// where
///     'src: 'dst,
///     Src: FromBytes + IntoBytes + ?Sized,
///     Dst: FromBytes + IntoBytes + ?Sized,
///     align_of::<Src>() >= align_of::<Dst>(),
///     size_compatible::<Src, Dst>(),
/// {
/// # /*
///     ...
/// # */
/// }
/// ```
///
/// The types `Src` and `Dst` are inferred from the calling context; they cannot
/// be explicitly specified in the macro invocation.
///
/// # Size compatibility
///
/// `transmute_mut!` supports transmuting between `Sized` types, between unsized
/// (i.e., `?Sized`) types, and from a `Sized` type to an unsized type. It
/// supports any transmutation that preserves the number of bytes of the
/// referent, even if doing so requires updating the metadata stored in an
/// unsized "fat" reference:
///
/// ```
/// # use zerocopy::transmute_mut;
/// # use core::mem::size_of_val; // Not in the prelude on our MSRV
/// let src: &mut [[u8; 2]] = &mut [[0, 1], [2, 3]][..];
/// let dst: &mut [u8] = transmute_mut!(src);
///
/// assert_eq!(dst.len(), 4);
/// assert_eq!(dst, [0, 1, 2, 3]);
/// let dst_size = size_of_val(dst);
/// assert_eq!(src.len(), 2);
/// assert_eq!(size_of_val(src), dst_size);
/// ```
///
/// # Errors
///
/// Violations of the alignment and size compatibility checks are detected
/// *after* the compiler performs monomorphization. This has two important
/// consequences.
///
/// First, it means that generic code will *never* fail these conditions:
///
/// ```
/// # use zerocopy::{transmute_mut, FromBytes, IntoBytes, Immutable};
/// fn transmute_mut<Src, Dst>(src: &mut Src) -> &mut Dst
/// where
///     Src: FromBytes + IntoBytes,
///     Dst: FromBytes + IntoBytes,
/// {
///     transmute_mut!(src)
/// }
/// ```
///
/// Instead, failures will only be detected once generic code is instantiated
/// with concrete types:
///
/// ```compile_fail,E0080
/// # use zerocopy::{transmute_mut, FromBytes, IntoBytes, Immutable};
/// #
/// # fn transmute_mut<Src, Dst>(src: &mut Src) -> &mut Dst
/// # where
/// #     Src: FromBytes + IntoBytes,
/// #     Dst: FromBytes + IntoBytes,
/// # {
/// #     transmute_mut!(src)
/// # }
/// let src: &mut u16 = &mut 0;
/// let dst: &mut u8 = transmute_mut(src);
/// ```
///
/// Second, the fact that violations are detected after monomorphization means
/// that `cargo check` will usually not detect errors, even when types are
/// concrete. Instead, `cargo build` must be used to detect such errors.
///
///
/// # Examples
///
/// Transmuting between `Sized` types:
///
/// ```
/// # use zerocopy::transmute_mut;
/// let mut one_dimensional: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
///
/// let two_dimensional: &mut [[u8; 4]; 2] = transmute_mut!(&mut one_dimensional);
///
/// assert_eq!(two_dimensional, &[[0, 1, 2, 3], [4, 5, 6, 7]]);
///
/// two_dimensional.reverse();
///
/// assert_eq!(one_dimensional, [4, 5, 6, 7, 0, 1, 2, 3]);
/// ```
///
/// Transmuting between unsized types:
///
/// ```
/// # use {zerocopy::*, zerocopy_derive::*};
/// # type u16 = zerocopy::byteorder::native_endian::U16;
/// # type u32 = zerocopy::byteorder::native_endian::U32;
/// #[derive(KnownLayout, FromBytes, IntoBytes, Immutable)]
/// #[repr(C)]
/// struct SliceDst<T, U> {
///     t: T,
///     u: [U],
/// }
///
/// type Src = SliceDst<u32, u16>;
/// type Dst = SliceDst<u16, u8>;
///
/// let mut bytes = [0, 1, 2, 3, 4, 5, 6, 7];
/// let src = Src::mut_from_bytes(&mut bytes[..]).unwrap();
/// let dst: &mut Dst = transmute_mut!(src);
///
/// assert_eq!(dst.t.as_bytes(), [0, 1]);
/// assert_eq!(dst.u, [2, 3, 4, 5, 6, 7]);
///
/// assert_eq!(src.t.as_bytes(), [0, 1, 2, 3]);
/// assert_eq!(src.u.len(), 2);
/// assert_eq!(src.u.as_bytes(), [4, 5, 6, 7]);
/// ```
#[macro_export]
macro_rules! transmute_mut {
    ($e:expr) => {{
        // NOTE: This must be a macro (rather than a function with trait bounds)
        // because, for backwards-compatibility on v0.8.x, we use the autoref
        // specialization trick to dispatch to different `transmute_mut`
        // implementations: one which doesn't require `Src: KnownLayout + Dst:
        // KnownLayout` when `Src: Sized + Dst: Sized`, and one which requires
        // `KnownLayout` bounds otherwise.

        // Ensure that the source type is a mutable reference.
        let e: &mut _ = $e;

        #[allow(unused)]
        use $crate::util::macro_util::TransmuteMutDst as _;
        let t = $crate::util::macro_util::Wrap::new(e);
        if false {
            // This branch exists solely to force the compiler to infer the type
            // of `Dst` *before* it attempts to resolve the method call to
            // `transmute_mut` in the `else` branch.
            //
            // Without this, if `Src` is `Sized` but `Dst` is `!Sized`, the
            // compiler will eagerly select the inherent impl of `transmute_mut`
            // (which requires `Dst: Sized`) because inherent methods take
            // priority over trait methods. It does this before it realizes
            // `Dst` is `!Sized`, leading to a compile error when it checks the
            // bounds later.
            //
            // By calling this helper (which returns `&mut Dst`), we force `Dst`
            // to be fully resolved. By the time it gets to the `else` branch,
            // the compiler knows `Dst` is `!Sized`, properly disqualifies the
            // inherent method, and falls back to the trait implementation.
            t.transmute_mut_inference_helper()
        } else {
            t.transmute_mut()
        }
    }}
}

/// Conditionally transmutes a value of one type to a value of another type of
/// the same size.
///
/// This macro behaves like an invocation of this function:
///
/// ```ignore
/// fn try_transmute<Src, Dst>(src: Src) -> Result<Dst, ValidityError<Src, Dst>>
/// where
///     Src: IntoBytes,
///     Dst: TryFromBytes,
///     size_of::<Src>() == size_of::<Dst>(),
/// {
/// # /*
///     ...
/// # */
/// }
/// ```
///
/// However, unlike a function, this macro can only be invoked when the types of
/// `Src` and `Dst` are completely concrete. The types `Src` and `Dst` are
/// inferred from the calling context; they cannot be explicitly specified in
/// the macro invocation.
///
/// Note that the `Src` produced by the expression `$e` will *not* be dropped.
/// Semantically, its bits will be copied into a new value of type `Dst`, the
/// original `Src` will be forgotten, and the value of type `Dst` will be
/// returned.
///
/// # Examples
///
/// ```
/// # use zerocopy::*;
/// // 0u8 → bool = false
/// assert_eq!(try_transmute!(0u8), Ok(false));
///
/// // 1u8 → bool = true
///  assert_eq!(try_transmute!(1u8), Ok(true));
///
/// // 2u8 → bool = error
/// assert!(matches!(
///     try_transmute!(2u8),
///     Result::<bool, _>::Err(ValidityError { .. })
/// ));
/// ```
///
#[doc = codegen_section!(
    header = "h2",
    bench = "try_transmute",
    format = "coco_static_size",
)]
#[macro_export]
macro_rules! try_transmute {
    ($e:expr) => {{
        // NOTE: This must be a macro (rather than a function with trait bounds)
        // because there's no way, in a generic context, to enforce that two
        // types have the same size. `core::mem::transmute` uses compiler magic
        // to enforce this so long as the types are concrete.

        let e = $e;
        if false {
            // Check that the sizes of the source and destination types are
            // equal.

            // SAFETY: This code is never executed.
            Ok(unsafe {
                // Clippy: We can't annotate the types; this macro is designed
                // to infer the types from the calling context.
                #[allow(clippy::missing_transmute_annotations)]
                $crate::util::macro_util::core_reexport::mem::transmute(e)
            })
        } else {
            $crate::util::macro_util::try_transmute::<_, _>(e)
        }
    }}
}

/// Conditionally transmutes a mutable or immutable reference of one type to an
/// immutable reference of another type of the same size and compatible
/// alignment.
///
/// *Note that while the **value** of the referent is checked for validity at
/// runtime, the **size** and **alignment** are checked at compile time. For
/// conversions which are fallible with respect to size and alignment, see the
/// methods on [`TryFromBytes`].*
///
/// This macro behaves like an invocation of this function:
///
/// ```ignore
/// fn try_transmute_ref<Src, Dst>(src: &Src) -> Result<&Dst, ValidityError<&Src, Dst>>
/// where
///     Src: IntoBytes + Immutable + ?Sized,
///     Dst: TryFromBytes + Immutable + ?Sized,
///     align_of::<Src>() >= align_of::<Dst>(),
///     size_compatible::<Src, Dst>(),
/// {
/// # /*
///     ...
/// # */
/// }
/// ```
///
/// The types `Src` and `Dst` are inferred from the calling context; they cannot
/// be explicitly specified in the macro invocation.
///
/// [`TryFromBytes`]: crate::TryFromBytes
///
/// # Size compatibility
///
/// `try_transmute_ref!` supports transmuting between `Sized` types, between
/// unsized (i.e., `?Sized`) types, and from a `Sized` type to an unsized type.
/// It supports any transmutation that preserves the number of bytes of the
/// referent, even if doing so requires updating the metadata stored in an
/// unsized "fat" reference:
///
/// ```
/// # use zerocopy::try_transmute_ref;
/// # use core::mem::size_of_val; // Not in the prelude on our MSRV
/// let src: &[[u8; 2]] = &[[0, 1], [2, 3]][..];
/// let dst: &[u8] = try_transmute_ref!(src).unwrap();
///
/// assert_eq!(src.len(), 2);
/// assert_eq!(dst.len(), 4);
/// assert_eq!(dst, [0, 1, 2, 3]);
/// assert_eq!(size_of_val(src), size_of_val(dst));
/// ```
///
/// # Examples
///
/// Transmuting between `Sized` types:
///
/// ```
/// # use zerocopy::*;
/// // 0u8 → bool = false
/// assert_eq!(try_transmute_ref!(&0u8), Ok(&false));
///
/// // 1u8 → bool = true
///  assert_eq!(try_transmute_ref!(&1u8), Ok(&true));
///
/// // 2u8 → bool = error
/// assert!(matches!(
///     try_transmute_ref!(&2u8),
///     Result::<&bool, _>::Err(ValidityError { .. })
/// ));
/// ```
///
/// Transmuting between unsized types:
///
/// ```
/// # use {zerocopy::*, zerocopy_derive::*};
/// # type u16 = zerocopy::byteorder::native_endian::U16;
/// # type u32 = zerocopy::byteorder::native_endian::U32;
/// #[derive(KnownLayout, FromBytes, IntoBytes, Immutable)]
/// #[repr(C)]
/// struct SliceDst<T, U> {
///     t: T,
///     u: [U],
/// }
///
/// type Src = SliceDst<u32, u16>;
/// type Dst = SliceDst<u16, bool>;
///
/// let src = Src::ref_from_bytes(&[0, 1, 0, 1, 0, 1, 0, 1]).unwrap();
/// let dst: &Dst = try_transmute_ref!(src).unwrap();
///
/// assert_eq!(src.t.as_bytes(), [0, 1, 0, 1]);
/// assert_eq!(src.u.len(), 2);
/// assert_eq!(src.u.as_bytes(), [0, 1, 0, 1]);
///
/// assert_eq!(dst.t.as_bytes(), [0, 1]);
/// assert_eq!(dst.u, [false, true, false, true, false, true]);
/// ```
///
#[doc = codegen_section!(
    header = "h2",
    bench = "try_transmute_ref",
    format = "coco",
    arity = 2,
    [
        open
        @index 1
        @title "Sized"
        @variant "static_size"
    ],
    [
        @index 2
        @title "Unsized"
        @variant "dynamic_size"
    ]
)]
#[macro_export]
macro_rules! try_transmute_ref {
    ($e:expr) => {{
        // Ensure that the source type is a reference or a mutable reference
        // (note that mutable references are implicitly reborrowed here).
        let e: &_ = $e;

        #[allow(unused_imports)]
        use $crate::util::macro_util::TryTransmuteRefDst as _;
        let t = $crate::util::macro_util::Wrap::new(e);
        if false {
            // This branch exists solely to force the compiler to infer the type
            // of `Dst` *before* it attempts to resolve the method call to
            // `try_transmute_ref` in the `else` branch.
            //
            // Without this, if `Src` is `Sized` but `Dst` is `!Sized`, the
            // compiler will eagerly select the inherent impl of
            // `try_transmute_ref` (which requires `Dst: Sized`) because
            // inherent methods take priority over trait methods. It does this
            // before it realizes `Dst` is `!Sized`, leading to a compile error
            // when it checks the bounds later.
            //
            // By calling this helper (which returns `&Dst`), we force `Dst`
            // to be fully resolved. By the time it gets to the `else`
            // branch, the compiler knows `Dst` is `!Sized`, properly
            // disqualifies the inherent method, and falls back to the trait
            // implementation.
            Ok(t.transmute_ref_inference_helper())
        } else {
            t.try_transmute_ref()
        }
    }}
}

/// Conditionally transmutes a mutable reference of one type to a mutable
/// reference of another type of the same size and compatible alignment.
///
/// *Note that while the **value** of the referent is checked for validity at
/// runtime, the **size** and **alignment** are checked at compile time. For
/// conversions which are fallible with respect to size and alignment, see the
/// methods on [`TryFromBytes`].*
///
/// This macro behaves like an invocation of this function:
///
/// ```ignore
/// fn try_transmute_mut<Src, Dst>(src: &mut Src) -> Result<&mut Dst, ValidityError<&mut Src, Dst>>
/// where
///     Src: FromBytes + IntoBytes + ?Sized,
///     Dst: TryFromBytes + IntoBytes + ?Sized,
///     align_of::<Src>() >= align_of::<Dst>(),
///     size_compatible::<Src, Dst>(),
/// {
/// # /*
///     ...
/// # */
/// }
/// ```
///
/// The types `Src` and `Dst` are inferred from the calling context; they cannot
/// be explicitly specified in the macro invocation.
///
/// [`TryFromBytes`]: crate::TryFromBytes
///
/// # Size compatibility
///
/// `try_transmute_mut!` supports transmuting between `Sized` types, between
/// unsized (i.e., `?Sized`) types, and from a `Sized` type to an unsized type.
/// It supports any transmutation that preserves the number of bytes of the
/// referent, even if doing so requires updating the metadata stored in an
/// unsized "fat" reference:
///
/// ```
/// # use zerocopy::try_transmute_mut;
/// # use core::mem::size_of_val; // Not in the prelude on our MSRV
/// let src: &mut [[u8; 2]] = &mut [[0, 1], [2, 3]][..];
/// let dst: &mut [u8] = try_transmute_mut!(src).unwrap();
///
/// assert_eq!(dst.len(), 4);
/// assert_eq!(dst, [0, 1, 2, 3]);
/// let dst_size = size_of_val(dst);
/// assert_eq!(src.len(), 2);
/// assert_eq!(size_of_val(src), dst_size);
/// ```
///
/// # Examples
///
/// Transmuting between `Sized` types:
///
/// ```
/// # use zerocopy::*;
/// // 0u8 → bool = false
/// let src = &mut 0u8;
/// assert_eq!(try_transmute_mut!(src), Ok(&mut false));
///
/// // 1u8 → bool = true
/// let src = &mut 1u8;
///  assert_eq!(try_transmute_mut!(src), Ok(&mut true));
///
/// // 2u8 → bool = error
/// let src = &mut 2u8;
/// assert!(matches!(
///     try_transmute_mut!(src),
///     Result::<&mut bool, _>::Err(ValidityError { .. })
/// ));
/// ```
///
/// Transmuting between unsized types:
///
/// ```
/// # use {zerocopy::*, zerocopy_derive::*};
/// # type u16 = zerocopy::byteorder::native_endian::U16;
/// # type u32 = zerocopy::byteorder::native_endian::U32;
/// #[derive(KnownLayout, FromBytes, IntoBytes, Immutable)]
/// #[repr(C)]
/// struct SliceDst<T, U> {
///     t: T,
///     u: [U],
/// }
///
/// type Src = SliceDst<u32, u16>;
/// type Dst = SliceDst<u16, bool>;
///
/// let mut bytes = [0, 1, 0, 1, 0, 1, 0, 1];
/// let src = Src::mut_from_bytes(&mut bytes).unwrap();
///
/// assert_eq!(src.t.as_bytes(), [0, 1, 0, 1]);
/// assert_eq!(src.u.len(), 2);
/// assert_eq!(src.u.as_bytes(), [0, 1, 0, 1]);
///
/// let dst: &Dst = try_transmute_mut!(src).unwrap();
///
/// assert_eq!(dst.t.as_bytes(), [0, 1]);
/// assert_eq!(dst.u, [false, true, false, true, false, true]);
/// ```
#[macro_export]
macro_rules! try_transmute_mut {
    ($e:expr) => {{
        // Ensure that the source type is a mutable reference.
        let e: &mut _ = $e;

        #[allow(unused_imports)]
        use $crate::util::macro_util::TryTransmuteMutDst as _;
        let t = $crate::util::macro_util::Wrap::new(e);
        if false {
            // This branch exists solely to force the compiler to infer the type
            // of `Dst` *before* it attempts to resolve the method call to
            // `try_transmute_mut` in the `else` branch.
            //
            // Without this, if `Src` is `Sized` but `Dst` is `!Sized`, the
            // compiler will eagerly select the inherent impl of
            // `try_transmute_mut` (which requires `Dst: Sized`) because
            // inherent methods take priority over trait methods. It does this
            // before it realizes `Dst` is `!Sized`, leading to a compile error
            // when it checks the bounds later.
            //
            // By calling this helper (which returns `&Dst`), we force `Dst`
            // to be fully resolved. By the time it gets to the `else`
            // branch, the compiler knows `Dst` is `!Sized`, properly
            // disqualifies the inherent method, and falls back to the trait
            // implementation.
            Ok(t.transmute_mut_inference_helper())
        } else {
            t.try_transmute_mut()
        }
    }}
}

/// Includes a file and safely transmutes it to a value of an arbitrary type.
///
/// The file will be included as a byte array, `[u8; N]`, which will be
/// transmuted to another type, `T`. `T` is inferred from the calling context,
/// and must implement [`FromBytes`].
///
/// The file is located relative to the current file (similarly to how modules
/// are found). The provided path is interpreted in a platform-specific way at
/// compile time. So, for instance, an invocation with a Windows path containing
/// backslashes `\` would not compile correctly on Unix.
///
/// `include_value!` is ignorant of byte order. For byte order-aware types, see
/// the [`byteorder`] module.
///
/// [`FromBytes`]: crate::FromBytes
/// [`byteorder`]: crate::byteorder
///
/// # Examples
///
/// Assume there are two files in the same directory with the following
/// contents:
///
/// File `data` (no trailing newline):
///
/// ```text
/// abcd
/// ```
///
/// File `main.rs`:
///
/// ```rust
/// use zerocopy::include_value;
/// # macro_rules! include_value {
/// # ($file:expr) => { zerocopy::include_value!(concat!("../testdata/include_value/", $file)) };
/// # }
///
/// fn main() {
///     let as_u32: u32 = include_value!("data");
///     assert_eq!(as_u32, u32::from_ne_bytes([b'a', b'b', b'c', b'd']));
///     let as_i32: i32 = include_value!("data");
///     assert_eq!(as_i32, i32::from_ne_bytes([b'a', b'b', b'c', b'd']));
/// }
/// ```
///
/// # Use in `const` contexts
///
/// This macro can be invoked in `const` contexts.
#[doc(alias("include_bytes", "include_data", "include_type"))]
#[macro_export]
macro_rules! include_value {
    ($file:expr $(,)?) => {
        $crate::transmute!(*::core::include_bytes!($file))
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! cryptocorrosion_derive_traits {
    (
        #[repr($repr:ident)]
        $(#[$attr:meta])*
        $vis:vis struct $name:ident $(<$($tyvar:ident),*>)?
        $(
            (
                $($tuple_field_vis:vis $tuple_field_ty:ty),*
            );
        )?

        $(
            {
                $($field_vis:vis $field_name:ident: $field_ty:ty,)*
            }
        )?
    ) => {
        $crate::cryptocorrosion_derive_traits!(@assert_allowed_struct_repr #[repr($repr)]);

        $(#[$attr])*
        #[repr($repr)]
        $vis struct $name $(<$($tyvar),*>)?
        $(
            (
                $($tuple_field_vis $tuple_field_ty),*
            );
        )?

        $(
            {
                $($field_vis $field_name: $field_ty,)*
            }
        )?

        // SAFETY: See inline.
        unsafe impl $(<$($tyvar),*>)? $crate::TryFromBytes for $name$(<$($tyvar),*>)?
        where
            $(
                $($tuple_field_ty: $crate::FromBytes,)*
            )?

            $(
                $($field_ty: $crate::FromBytes,)*
            )?
        {
            #[inline(always)]
            fn is_bit_valid<A>(_: $crate::Maybe<'_, Self, A>) -> bool
            where
                A: $crate::invariant::Alignment,
            {
                // SAFETY: This macro only accepts `#[repr(C)]` and
                // `#[repr(transparent)]` structs, and this `impl` block
                // requires all field types to be `FromBytes`. Thus, all
                // initialized byte sequences constitutes valid instances of
                // `Self`.
                true
            }

            fn only_derive_is_allowed_to_implement_this_trait() {}
        }

        // SAFETY: This macro only accepts `#[repr(C)]` and
        // `#[repr(transparent)]` structs, and this `impl` block requires all
        // field types to be `FromBytes`, which is a sub-trait of `FromZeros`.
        unsafe impl $(<$($tyvar),*>)? $crate::FromZeros for $name$(<$($tyvar),*>)?
        where
            $(
                $($tuple_field_ty: $crate::FromBytes,)*
            )?

            $(
                $($field_ty: $crate::FromBytes,)*
            )?
        {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }

        // SAFETY: This macro only accepts `#[repr(C)]` and
        // `#[repr(transparent)]` structs, and this `impl` block requires all
        // field types to be `FromBytes`.
        unsafe impl $(<$($tyvar),*>)? $crate::FromBytes for $name$(<$($tyvar),*>)?
        where
            $(
                $($tuple_field_ty: $crate::FromBytes,)*
            )?

            $(
                $($field_ty: $crate::FromBytes,)*
            )?
        {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }

        // SAFETY: This macro only accepts `#[repr(C)]` and
        // `#[repr(transparent)]` structs, this `impl` block requires all field
        // types to be `IntoBytes`, and a padding check is used to ensures that
        // there are no padding bytes.
        unsafe impl $(<$($tyvar),*>)? $crate::IntoBytes for $name$(<$($tyvar),*>)?
        where
            $(
                $($tuple_field_ty: $crate::IntoBytes,)*
            )?

            $(
                $($field_ty: $crate::IntoBytes,)*
            )?

            (): $crate::util::macro_util::PaddingFree<
                Self,
                {
                    $crate::cryptocorrosion_derive_traits!(
                        @struct_padding_check #[repr($repr)]
                        $(($($tuple_field_ty),*))?
                        $({$($field_ty),*})?
                    )
                },
            >,
        {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }

        // SAFETY: This macro only accepts `#[repr(C)]` and
        // `#[repr(transparent)]` structs, and this `impl` block requires all
        // field types to be `Immutable`.
        unsafe impl $(<$($tyvar),*>)? $crate::Immutable for $name$(<$($tyvar),*>)?
        where
            $(
                $($tuple_field_ty: $crate::Immutable,)*
            )?

            $(
                $($field_ty: $crate::Immutable,)*
            )?
        {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }
    };
    (@assert_allowed_struct_repr #[repr(transparent)]) => {};
    (@assert_allowed_struct_repr #[repr(C)]) => {};
    (@assert_allowed_struct_repr #[$_attr:meta]) => {
        compile_error!("repr must be `#[repr(transparent)]` or `#[repr(C)]`");
    };
    (
        @struct_padding_check #[repr(transparent)]
        $(($($tuple_field_ty:ty),*))?
        $({$($field_ty:ty),*})?
    ) => {
        // SAFETY: `#[repr(transparent)]` structs cannot have the same layout as
        // their single non-zero-sized field, and so cannot have any padding
        // outside of that field.
        0
    };
    (
        @struct_padding_check #[repr(C)]
        $(($($tuple_field_ty:ty),*))?
        $({$($field_ty:ty),*})?
    ) => {
        $crate::struct_padding!(
            Self,
            None,
            None,
            [
                $($($tuple_field_ty),*)?
                $($($field_ty),*)?
            ]
        )
    };
    (
        #[repr(C)]
        $(#[$attr:meta])*
        $vis:vis union $name:ident {
            $(
                $field_name:ident: $field_ty:ty,
            )*
        }
    ) => {
        $(#[$attr])*
        #[repr(C)]
        $vis union $name {
            $(
                $field_name: $field_ty,
            )*
        }

        // SAFETY: See inline.
        unsafe impl $crate::TryFromBytes for $name
        where
            $(
                $field_ty: $crate::FromBytes,
            )*
        {
            #[inline(always)]
            fn is_bit_valid<A>(_: $crate::Maybe<'_, Self, A>) -> bool
            where
                A: $crate::invariant::Alignment,
            {
                // SAFETY: This macro only accepts `#[repr(C)]` unions, and this
                // `impl` block requires all field types to be `FromBytes`.
                // Thus, all initialized byte sequences constitutes valid
                // instances of `Self`.
                true
            }

            fn only_derive_is_allowed_to_implement_this_trait() {}
        }

        // SAFETY: This macro only accepts `#[repr(C)]` unions, and this `impl`
        // block requires all field types to be `FromBytes`, which is a
        // sub-trait of `FromZeros`.
        unsafe impl $crate::FromZeros for $name
        where
            $(
                $field_ty: $crate::FromBytes,
            )*
        {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }

        // SAFETY: This macro only accepts `#[repr(C)]` unions, and this `impl`
        // block requires all field types to be `FromBytes`.
        unsafe impl $crate::FromBytes for $name
        where
            $(
                $field_ty: $crate::FromBytes,
            )*
        {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }

        // SAFETY: This macro only accepts `#[repr(C)]` unions, this `impl`
        // block requires all field types to be `IntoBytes`, and a padding check
        // is used to ensures that there are no padding bytes before or after
        // any field.
        unsafe impl $crate::IntoBytes for $name
        where
            $(
                $field_ty: $crate::IntoBytes,
            )*
            (): $crate::util::macro_util::PaddingFree<
                Self,
                {
                    $crate::union_padding!(
                        Self,
                        None::<usize>,
                        None::<usize>,
                        [$($field_ty),*]
                    )
                },
            >,
        {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }

        // SAFETY: This macro only accepts `#[repr(C)]` unions, and this `impl`
        // block requires all field types to be `Immutable`.
        unsafe impl $crate::Immutable for $name
        where
            $(
                $field_ty: $crate::Immutable,
            )*
        {
            fn only_derive_is_allowed_to_implement_this_trait() {}
        }
    };
}

#[cfg(kani)]
mod proofs {
    use crate::{
        proof_support::{
            all_zero_byte_policy_oracle, assert_same_u8_elements, assert_same_usize,
            bool_from_byte, copy_snapshot,
        },
        TryFromBytes, ValidityError,
    };

    #[derive(TryFromBytes)]
    #[repr(C, align(16))]
    struct PaddedPointer {
        pointer: *const u8,
    }

    fn checked_bool_oracle(src: u8) -> Option<bool> {
        bool_from_byte(src)
    }

    fn cover_bool_oracle(expected: Option<bool>) {
        kani::cover!(expected == Some(false));
        kani::cover!(expected == Some(true));
        kani::cover!(expected.is_none());
    }

    // Configuration: Uses the common Kani CI configuration documented in
    // `agent_docs/validation.md`: the CI-pinned Kani release and its bundled
    // x86_64-unknown-linux-gnu compiler, the stable-compatible feature bundle,
    // `-Zfunction-contracts`, and one layout selected by `--randomize-layout`
    // per invocation.
    //
    // Bool domain and oracle: `checked_bool_oracle` delegates only to the
    // shared safe-Rust `bool_from_byte`, whose `u8::from(bool)` construction
    // [1] and exhaustive language representation [2] are documented next to
    // that helper. It neither invokes zerocopy nor consults the result under
    // proof. Kani explores all 256 `u8` values, with covers for false, true,
    // and invalid inputs. The value and reference macros are invoked only for
    // the two independently valid representations; they check the decoded
    // value and the explicit zerocopy same-address policy. `addr_of!` /
    // `addr_of_mut!` obtain a raw pointer to the source place without creating
    // an intermediate reference [5]. Rust's reference-to-raw coercions, sized
    // pointer casts, and raw-pointer equality independently specify how both
    // modeled addresses are observed [6][7]. Requiring them to match is a
    // zerocopy policy oracle, not a Rust-language requirement, and establishes
    // no provenance property.
    //
    // Before the mutable macro is called, logical `!` derives a replacement
    // solely from the independently decoded `expected` bool [13], and [1]
    // converts that replacement to its expected source byte. The target result
    // cannot influence either value. On success, dereference observes the bool
    // at the returned reference's location [14], assignment copies or moves
    // the precomputed replacement into that location [15], and `assert_eq!`
    // plus primitive `u8` equality compares the source with the precomputed
    // byte after the mutable borrow ends [16]. This chain proves only modeled
    // value propagation; the reference obligations remain in the TOOL/TCB
    // boundary below.
    //
    // Owned-value pointer policy: Two independent harnesses exercise the
    // owned-value macro. The first covers every `usize` as a direct
    // `*const u8` candidate. Safe `usize::to_ne_bytes` obtains its exact memory
    // representation [8], and the shared `all_zero_byte_policy_oracle`
    // classifies the complete eight-byte array through a Rust repeat array,
    // safe iteration, and primitive equality. The helper's adjacent docs give
    // those exact Rust 1.93 contracts; it never reconstructs an integer or
    // calls zerocopy. This family separately adopts all-zero acceptance as the
    // explicit conservative zerocopy pointer policy under test. Before the
    // macro consumes `src`, the shared safe-Rust `copy_snapshot` records its
    // `Copy` value using the concrete `usize: Copy` implementation [17] and
    // the dereference, value-expression, and copied-place rules documented
    // next to that helper. On `Err`, the shared
    // `assert_same_usize` observes the directly projected error field against
    // that snapshot using `assert_eq!` and primitive `usize` equality. Neither
    // helper calls zerocopy or consults its result while constructing the
    // expectation. This recovery check establishes abstract `usize` equality,
    // not byte preservation, independent storage, or provenance.
    //
    // The second harness covers every `[u8; 16]` source and transmutes to
    // `PaddedPointer`. Pinned compiler observations require an eight-byte thin
    // pointer at offset zero in a 16-byte, 16-aligned `repr(C)` destination;
    // the remaining eight bytes are therefore genuine destination tail
    // padding [10][11]. Safe `slice::first_chunk` obtains exactly the first
    // eight source bytes, with `Option::expect` making a missing chunk fail
    // closed [9]. The same shared all-zero classifier supplies the
    // pointer-field policy while deliberately ignoring the padding bytes. The
    // derived `TryFromBytes` validator is part of the target path; it is not
    // an oracle. The end-to-end harness proves, rather than assumes, that macro
    // acceptance matches that field policy and is independent of the padding.
    // Its covers witness acceptance and rejection with nonzero padding without
    // constraining the universal input domain. On every rejection, the shared
    // ordered-byte observer compares all 16 returned source bytes with a safe
    // pre-call snapshot. It projects the crate-visible error field rather than
    // calling `ValidityError::into_src`, preventing accessor and macro defects
    // from compensating.
    //
    // Destination validity and accepted value: Rust guarantees that every
    // integer representation can validly produce a thin raw pointer [3]. Rust
    // also states both that padding need not be initialized and that a struct's
    // validity requires its fields to be valid at their respective types [12].
    // `PaddedPointer` has exactly one field; [3] proves that field valid, while
    // [10][11] identify every remaining destination byte as tail padding.
    // Therefore those remaining bytes add no validity obligation. This
    // derivation is independent of the derived validator and Kani's padding
    // model. Thus an erroneous acceptance in either pointer harness still
    // cannot materialize an invalid destination. On the accepted all-zero
    // field, safe `core::ptr::null()` independently supplies the expected
    // pointer by its standard-library contract [4]. Neither harness
    // dereferences the result.
    //
    // Storage and bounds: Each bool harness uses one stack `u8`; the direct
    // pointer harness uses one `usize`, its safe `Copy` value snapshot, and its
    // eight-byte representation. The padded harness uses one 16-byte source
    // plus its safe snapshot; all other values are fixed-size compiler
    // temporaries. No harness allocates, contains an explicit source loop, or
    // uses `kani::assume`; every symbolic input is unconstrained. Bool
    // harnesses use unwind one. The direct pointer harness uses unwind nine for
    // an eight-byte target/helper scan plus termination. The padded harness
    // uses unwind 17 for its 16-byte recovery comparison plus termination.
    // Kani's unwinding checks enforce each bound.
    //
    // Scope and TOOL/TCB boundary: These are end-to-end proofs only for the
    // listed `u8`-to-`bool`, `usize`-to-`*const u8`, and
    // `[u8; 16]`-to-`PaddedPointer` instantiations on the pinned target. They
    // do not prove other types, padding shapes, sizes, alignments, macro arms,
    // or toolchains. Because Kani does not completely check invalid-value
    // production, invalid-bool public paths remain uninvoked. Reading and
    // writing reference-macro results presupposes live, dereferenceable
    // references with valid lifetime, aliasing, and provenance; Kani does not
    // completely check those obligations, so they remain TOOL/TCB premises
    // rather than proof conclusions. Its uninitialized-memory/padding model is
    // likewise a premise for the padded recovery result. In particular, it
    // also verifies when the target body is locally replaced with the typed
    // `MaybeUninit<ReadOnly<Dst>>` implementation immediately before
    // 94f0da71; Kani does not expose that implementation's compiler-permitted
    // destination-padding loss. The theorem therefore observes every
    // initialized source byte on `Err` in Kani's selected execution model, but
    // is not regression evidence for #3632/#3634 or a proof over every
    // compiler-permitted padding behavior. It does not observe destination
    // padding after `Ok`. Reference-arm error recovery is not exercised.
    //
    // [1] Per https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-From%3Cbool%3E-for-u8:
    //
    //     Converts from `bool` to `u8`, by turning `false` into `0` and `true`
    //     into `1`.
    //
    // [2] Per https://doc.rust-lang.org/1.93.0/reference/types/boolean.html#representation:
    //
    //     The value false has the bit pattern `0x00` and the value true has the
    //     bit pattern `0x01`. It is undefined behavior for an object with the
    //     boolean type to have any other bit pattern.
    //
    // [3] Per https://doc.rust-lang.org/1.93.0/reference/types/pointer.html#bit-validity:
    //
    //     For thin raw pointers (i.e., for `P = *const T` or `P = *mut T` for
    //     `T: Sized`), the inverse direction (transmuting from an integer or
    //     array of integers to `P`) is always valid. However, the pointer
    //     produced via such a transmutation may not be dereferenced (not even
    //     if `T` has size zero).
    //
    // [4] Per https://doc.rust-lang.org/1.93.0/std/ptr/fn.null.html:
    //
    //     Creates a null raw pointer.
    //
    //     This function is equivalent to zero-initializing the pointer:
    //     `MaybeUninit::<*const T>::zeroed().assume_init()`. The resulting
    //     pointer has the address 0.
    //
    // [5] Per https://doc.rust-lang.org/1.93.0/std/ptr/macro.addr_of.html and
    // https://doc.rust-lang.org/1.93.0/std/ptr/macro.addr_of_mut.html:
    //
    //     Creates a `const` raw pointer to a place, without creating an
    //     intermediate reference.
    //
    //     Creates a `mut` raw pointer to a place, without creating an
    //     intermediate reference.
    //
    // [6] Rust 1.93 lists the coercions “`&T` to `*const T`” and “`&mut T` to
    // `*mut T`”:
    // https://doc.rust-lang.org/1.93.0/reference/type-coercions.html#coercion-types
    //
    // [7] For sized pointer-to-pointer casts, Rust 1.93 says “the pointer is
    // returned unchanged”; raw-pointer `PartialEq` says “Pointer equality is
    // by address”:
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#pointer-to-pointer-cast
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#impl-PartialEq-for-*const+T
    // https://doc.rust-lang.org/1.93.0/std/primitive.pointer.html#impl-PartialEq-for-*mut+T
    //
    // [8] Per https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#method.to_ne_bytes:
    //
    //     Returns the memory representation of this integer as a byte array in
    //     native byte order.
    //
    // [9] Rust 1.93 specifies that `first_chunk` returns a reference to the
    // first `N` items, or `None` when the slice is shorter; `Option::expect`
    // returns `Some` and panics for `None`:
    // https://doc.rust-lang.org/1.93.0/std/primitive.slice.html#method.first_chunk
    // https://doc.rust-lang.org/1.93.0/std/option/enum.Option.html#method.expect
    //
    // [10] Rust 1.93 specifies the `repr(C)` struct layout algorithm and that
    // `align(N)` raises a type's alignment to at least `N`:
    // https://doc.rust-lang.org/1.93.0/reference/type-layout.html#reprc-structs
    // https://doc.rust-lang.org/1.93.0/reference/type-layout.html#the-alignment-modifiers
    //
    // [11] Rust 1.93 specifies the compiler layout observations used by the
    // fail-closed pinned-target assertions:
    // https://doc.rust-lang.org/1.93.0/core/mem/fn.size_of.html
    // https://doc.rust-lang.org/1.93.0/core/mem/fn.align_of.html
    // https://doc.rust-lang.org/1.93.0/core/mem/macro.offset_of.html
    //
    // [12] Rust 1.93 states that padding bytes need not be initialized, and
    // states a struct's validity requirement in terms of its fields:
    // https://doc.rust-lang.org/1.93.0/core/mem/union.MaybeUninit.html#initialization-invariant
    // https://doc.rust-lang.org/1.93.0/reference/behavior-considered-undefined.html#invalid-values
    //
    //     Padding bytes do not have to be initialized.
    //
    //     A struct, tuple, and array requires all fields/elements to be valid
    //     at their respective type.
    //
    // [13] Rust 1.93 classifies `!` on a primitive `bool` as logical NOT and
    // evaluates its operand in value-expression context:
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#negation-operators
    //
    // [14] Per Rust 1.93, dereferencing a pointer denotes its pointed-to
    // location, and the location resulting from dereferencing `&mut T` can be
    // assigned to:
    // https://doc.rust-lang.org/1.93.0/reference/expressions/operator-expr.html#the-dereference-operator
    //
    // [15] Rust 1.93 says that an assignment next copies or moves its assigned
    // value to its assigned place:
    // https://doc.rust-lang.org/1.93.0/reference/expressions/assignment-expr.html#basic-assignments
    //
    // [16] `assert_eq!` asserts equality of its operands, and primitive `bool`
    // and `u8` supply the two equality operations used by the mutable harness:
    // https://doc.rust-lang.org/1.93.0/std/macro.assert_eq.html
    // https://doc.rust-lang.org/1.93.0/std/primitive.bool.html#impl-PartialEq-for-bool
    // https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-PartialEq-for-u8
    //
    // [17] Rust 1.93 lists the primitive `usize` implementation of `Copy`:
    // https://doc.rust-lang.org/1.93.0/std/primitive.usize.html#impl-Copy-for-usize

    #[kani::proof]
    #[kani::unwind(1)]
    fn prove_try_transmute_u8_to_bool() {
        let src: u8 = kani::any();
        let expected = checked_bool_oracle(src);
        cover_bool_oracle(expected);
        if let Some(expected) = expected {
            let result: Result<bool, ValidityError<u8, bool>> = crate::try_transmute!(src);
            match result {
                Ok(dst) => assert_eq!(dst, expected),
                Err(_) => panic!("transmute rejected an independently valid bool"),
            }
        }
    }

    #[kani::proof]
    #[kani::unwind(1)]
    fn prove_try_transmute_ref_u8_to_bool() {
        let src: u8 = kani::any();
        let src_ptr = core::ptr::addr_of!(src);
        let expected = checked_bool_oracle(src);
        cover_bool_oracle(expected);
        if let Some(expected) = expected {
            let result: Result<&bool, ValidityError<&u8, bool>> = crate::try_transmute_ref!(&src);
            match result {
                Ok(dst) => {
                    assert_eq!((dst as *const bool).cast::<u8>(), src_ptr);
                    assert_eq!(*dst, expected);
                }
                Err(_) => panic!("reference transmute rejected an independently valid bool"),
            }
        }
    }

    #[kani::proof]
    #[kani::unwind(1)]
    fn prove_try_transmute_mut_u8_to_bool() {
        let mut src: u8 = kani::any();
        let src_ptr = core::ptr::addr_of_mut!(src);
        let expected = checked_bool_oracle(src);
        cover_bool_oracle(expected);
        if let Some(expected) = expected {
            let replacement = !expected;
            let replacement_byte = u8::from(replacement);
            let result: Result<&mut bool, ValidityError<&mut u8, bool>> =
                crate::try_transmute_mut!(&mut src);
            match result {
                Ok(dst) => {
                    assert_eq!((dst as *mut bool).cast::<u8>(), src_ptr);
                    assert_eq!(*dst, expected);
                    *dst = replacement;
                }
                Err(_) => panic!("mutable transmute rejected an independently valid bool"),
            }
            assert_eq!(src, replacement_byte);
        }
    }

    #[kani::proof]
    #[kani::unwind(9)]
    // This transmutation is the operation under proof. The resulting pointer
    // is valid to produce by [3] and is never dereferenced. Safe
    // `usize::to_ne_bytes` [8] plus the shared complete-array classifier supply
    // the independently observed bytes to which this family applies its
    // explicit zero-only pointer policy. Safe `core::ptr::null()` is the
    // expected result on that branch by [4]. On rejection, direct projection
    // of the crate-visible error field and the shared `usize` observer compare
    // the restored source with the safe pre-call snapshot without calling
    // `ValidityError::into_src`, so accessor and macro defects cannot
    // compensate.
    // `#[allow(unknown_lints)]` is for `integer_to_ptr_transmutes` on the MSRV.
    #[allow(unknown_lints)]
    #[allow(integer_to_ptr_transmutes)]
    fn prove_try_transmute_usize_to_pointer_policy_and_recovery() {
        let src: usize = kani::any();
        let snapshot = copy_snapshot(&src);
        let src_bytes = snapshot.to_ne_bytes();
        let expected_valid = all_zero_byte_policy_oracle(&src_bytes);
        let result: Result<*const u8, ValidityError<usize, *const u8>> = crate::try_transmute!(src);

        kani::cover!(expected_valid);
        kani::cover!(!expected_valid);
        match result {
            Ok(pointer) => {
                assert!(expected_valid);
                assert_eq!(pointer, core::ptr::null());
            }
            Err(error) => {
                assert!(!expected_valid);
                assert_same_usize(error.src, snapshot);
            }
        }
    }

    #[kani::proof]
    #[kani::unwind(17)]
    fn prove_try_transmute_padded_pointer_policy_and_recovery() {
        const POINTER_BYTES: usize = 8;
        const OBJECT_BYTES: usize = 16;

        assert_same_usize(core::mem::size_of::<*const u8>(), POINTER_BYTES);
        assert_same_usize(core::mem::align_of::<PaddedPointer>(), OBJECT_BYTES);
        assert_same_usize(core::mem::size_of::<PaddedPointer>(), OBJECT_BYTES);
        assert_same_usize(core::mem::offset_of!(PaddedPointer, pointer), 0);
        assert!(core::mem::size_of::<PaddedPointer>() > core::mem::size_of::<*const u8>());

        let src: [u8; OBJECT_BYTES] = kani::any();
        let snapshot = copy_snapshot(&src);
        let pointer_bytes = snapshot
            .first_chunk::<POINTER_BYTES>()
            .expect("a 16-byte source must contain its eight-byte pointer field");
        let expected_valid = all_zero_byte_policy_oracle(pointer_bytes);
        let result: Result<PaddedPointer, ValidityError<[u8; OBJECT_BYTES], PaddedPointer>> =
            crate::try_transmute!(src);

        kani::cover!(expected_valid);
        kani::cover!(!expected_valid);
        kani::cover!(expected_valid && snapshot[POINTER_BYTES] != 0);
        kani::cover!(!expected_valid && snapshot[POINTER_BYTES] != 0);
        match result {
            Ok(dst) => {
                assert!(expected_valid);
                assert_eq!(dst.pointer, core::ptr::null());
            }
            Err(error) => {
                assert!(!expected_valid);
                assert_same_u8_elements(&error.src, &snapshot);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        byteorder::native_endian::{U16, U32},
        util::testutil::*,
        *,
    };

    #[derive(KnownLayout, Immutable, FromBytes, IntoBytes, PartialEq, Debug)]
    #[repr(C)]
    struct SliceDst<T, U> {
        a: T,
        b: [U],
    }

    #[test]
    fn test_transmute() {
        // Test that memory is transmuted as expected.
        let array_of_u8s = [0u8, 1, 2, 3, 4, 5, 6, 7];
        let array_of_arrays = [[0, 1], [2, 3], [4, 5], [6, 7]];
        let x: [[u8; 2]; 4] = transmute!(array_of_u8s);
        assert_eq!(x, array_of_arrays);
        let x: [u8; 8] = transmute!(array_of_arrays);
        assert_eq!(x, array_of_u8s);

        // Test that memory is transmuted as expected when shrinking.
        let x: [[u8; 2]; 3] = transmute!(#![allow(shrink)] array_of_u8s);
        assert_eq!(x, [[0u8, 1], [2, 3], [4, 5]]);

        // Test that the source expression's value is forgotten rather than
        // dropped.
        #[derive(IntoBytes)]
        #[repr(transparent)]
        struct PanicOnDrop(());
        impl Drop for PanicOnDrop {
            fn drop(&mut self) {
                panic!("PanicOnDrop::drop");
            }
        }
        #[allow(clippy::let_unit_value)]
        let _: () = transmute!(PanicOnDrop(()));
        #[allow(clippy::let_unit_value)]
        let _: () = transmute!(#![allow(shrink)] PanicOnDrop(()));

        // Test that `transmute!` is legal in a const context.
        const ARRAY_OF_U8S: [u8; 8] = [0u8, 1, 2, 3, 4, 5, 6, 7];
        const ARRAY_OF_ARRAYS: [[u8; 2]; 4] = [[0, 1], [2, 3], [4, 5], [6, 7]];
        const X: [[u8; 2]; 4] = transmute!(ARRAY_OF_U8S);
        assert_eq!(X, ARRAY_OF_ARRAYS);
        const X_SHRINK: [[u8; 2]; 3] = transmute!(#![allow(shrink)] ARRAY_OF_U8S);
        assert_eq!(X_SHRINK, [[0u8, 1], [2, 3], [4, 5]]);

        // Test that `transmute!` works with `!Immutable` types.
        let x: usize = transmute!(UnsafeCell::new(1usize));
        assert_eq!(x, 1);
        let x: UnsafeCell<usize> = transmute!(1usize);
        assert_eq!(x.into_inner(), 1);
        let x: UnsafeCell<isize> = transmute!(UnsafeCell::new(1usize));
        assert_eq!(x.into_inner(), 1);
    }

    // A `Sized` type which doesn't implement `KnownLayout` (it is "not
    // `KnownLayout`", or `Nkl`).
    //
    // This permits us to test that `transmute_ref!` and `transmute_mut!` work
    // for types which are `Sized + !KnownLayout`. When we added support for
    // slice DSTs in #1924, this new support relied on `KnownLayout`, but we
    // need to make sure to remain backwards-compatible with code which uses
    // these macros with types which are `!KnownLayout`.
    #[derive(FromBytes, IntoBytes, Immutable, PartialEq, Eq, Debug)]
    #[repr(transparent)]
    struct Nkl<T>(T);

    #[test]
    fn test_transmute_ref() {
        // Test that memory is transmuted as expected.
        let array_of_u8s = [0u8, 1, 2, 3, 4, 5, 6, 7];
        let array_of_arrays = [[0, 1], [2, 3], [4, 5], [6, 7]];
        let x: &[[u8; 2]; 4] = transmute_ref!(&array_of_u8s);
        assert_eq!(*x, array_of_arrays);
        let x: &[u8; 8] = transmute_ref!(&array_of_arrays);
        assert_eq!(*x, array_of_u8s);

        // Test that `transmute_ref!` is legal in a const context.
        const ARRAY_OF_U8S: [u8; 8] = [0u8, 1, 2, 3, 4, 5, 6, 7];
        const ARRAY_OF_ARRAYS: [[u8; 2]; 4] = [[0, 1], [2, 3], [4, 5], [6, 7]];
        #[allow(clippy::redundant_static_lifetimes)]
        const X: &'static [[u8; 2]; 4] = transmute_ref!(&ARRAY_OF_U8S);
        assert_eq!(*X, ARRAY_OF_ARRAYS);

        // Test sized -> unsized transmutation.
        let array_of_u8s = [0u8, 1, 2, 3, 4, 5, 6, 7];
        let array_of_arrays = [[0, 1], [2, 3], [4, 5], [6, 7]];
        let slice_of_arrays = &array_of_arrays[..];
        let x: &[[u8; 2]] = transmute_ref!(&array_of_u8s);
        assert_eq!(x, slice_of_arrays);

        // Before 1.61.0, we can't define the `const fn transmute_ref` function
        // that we do on and after 1.61.0.
        #[cfg(no_zerocopy_generic_bounds_in_const_fn_1_61_0)]
        {
            // Test that `transmute_ref!` supports non-`KnownLayout` `Sized`
            // types.
            const ARRAY_OF_NKL_U8S: Nkl<[u8; 8]> = Nkl([0u8, 1, 2, 3, 4, 5, 6, 7]);
            const ARRAY_OF_NKL_ARRAYS: Nkl<[[u8; 2]; 4]> = Nkl([[0, 1], [2, 3], [4, 5], [6, 7]]);
            const X_NKL: &Nkl<[[u8; 2]; 4]> = transmute_ref!(&ARRAY_OF_NKL_U8S);
            assert_eq!(*X_NKL, ARRAY_OF_NKL_ARRAYS);
        }

        #[cfg(not(no_zerocopy_generic_bounds_in_const_fn_1_61_0))]
        {
            // Call through a generic function to make sure our autoref
            // specialization trick works even when types are generic.
            const fn transmute_ref<T, U>(t: &T) -> &U
            where
                T: IntoBytes + Immutable,
                U: FromBytes + Immutable,
            {
                transmute_ref!(t)
            }

            // Test that `transmute_ref!` supports non-`KnownLayout` `Sized`
            // types.
            const ARRAY_OF_NKL_U8S: Nkl<[u8; 8]> = Nkl([0u8, 1, 2, 3, 4, 5, 6, 7]);
            const ARRAY_OF_NKL_ARRAYS: Nkl<[[u8; 2]; 4]> = Nkl([[0, 1], [2, 3], [4, 5], [6, 7]]);
            const X_NKL: &Nkl<[[u8; 2]; 4]> = transmute_ref(&ARRAY_OF_NKL_U8S);
            assert_eq!(*X_NKL, ARRAY_OF_NKL_ARRAYS);
        }

        // Test that `transmute_ref!` works on slice DSTs in and that memory is
        // transmuted as expected.
        let slice_dst_of_u8s =
            SliceDst::<U16, [u8; 2]>::ref_from_bytes(&[0, 1, 2, 3, 4, 5][..]).unwrap();
        let slice_dst_of_u16s =
            SliceDst::<U16, U16>::ref_from_bytes(&[0, 1, 2, 3, 4, 5][..]).unwrap();
        let x: &SliceDst<U16, U16> = transmute_ref!(slice_dst_of_u8s);
        assert_eq!(x, slice_dst_of_u16s);

        let slice_dst_of_u8s =
            SliceDst::<U16, u8>::ref_from_bytes(&[0, 1, 2, 3, 4, 5][..]).unwrap();
        let x: &[u8] = transmute_ref!(slice_dst_of_u8s);
        assert_eq!(x, [0, 1, 2, 3, 4, 5]);

        let x: &[u8] = transmute_ref!(slice_dst_of_u16s);
        assert_eq!(x, [0, 1, 2, 3, 4, 5]);

        let x: &[U16] = transmute_ref!(slice_dst_of_u16s);
        let slice_of_u16s: &[U16] = <[U16]>::ref_from_bytes(&[0, 1, 2, 3, 4, 5][..]).unwrap();
        assert_eq!(x, slice_of_u16s);

        // Test that transmuting from a type with larger trailing slice offset
        // and larger trailing slice element works.
        let bytes = &[0, 1, 2, 3, 4, 5, 6, 7][..];
        let slice_dst_big = SliceDst::<U32, U16>::ref_from_bytes(bytes).unwrap();
        let slice_dst_small = SliceDst::<U16, u8>::ref_from_bytes(bytes).unwrap();
        let x: &SliceDst<U16, u8> = transmute_ref!(slice_dst_big);
        assert_eq!(x, slice_dst_small);

        // Test that it's legal to transmute a reference while shrinking the
        // lifetime (note that `X` has the lifetime `'static`).
        let x: &[u8; 8] = transmute_ref!(X);
        assert_eq!(*x, ARRAY_OF_U8S);

        // Test that `transmute_ref!` supports decreasing alignment.
        let u = AU64(0);
        let array = [0, 0, 0, 0, 0, 0, 0, 0];
        let x: &[u8; 8] = transmute_ref!(&u);
        assert_eq!(*x, array);

        // Test that a mutable reference can be turned into an immutable one.
        let mut x = 0u8;
        #[allow(clippy::useless_transmute)]
        let y: &u8 = transmute_ref!(&mut x);
        assert_eq!(*y, 0);
    }

    #[test]
    fn test_try_transmute() {
        // Test that memory is transmuted with `try_transmute` as expected.
        let array_of_bools = [false, true, false, true, false, true, false, true];
        let array_of_arrays = [[0, 1], [0, 1], [0, 1], [0, 1]];
        let x: Result<[[u8; 2]; 4], _> = try_transmute!(array_of_bools);
        assert_eq!(x, Ok(array_of_arrays));
        let x: Result<[bool; 8], _> = try_transmute!(array_of_arrays);
        assert_eq!(x, Ok(array_of_bools));

        // Test that `try_transmute!` works with `!Immutable` types.
        let x: Result<usize, _> = try_transmute!(UnsafeCell::new(1usize));
        assert_eq!(x.unwrap(), 1);
        let x: Result<UnsafeCell<usize>, _> = try_transmute!(1usize);
        assert_eq!(x.unwrap().into_inner(), 1);
        let x: Result<UnsafeCell<isize>, _> = try_transmute!(UnsafeCell::new(1usize));
        assert_eq!(x.unwrap().into_inner(), 1);

        #[derive(FromBytes, IntoBytes, Debug, PartialEq)]
        #[repr(transparent)]
        struct PanicOnDrop<T>(T);

        impl<T> Drop for PanicOnDrop<T> {
            fn drop(&mut self) {
                panic!("PanicOnDrop dropped");
            }
        }

        // Since `try_transmute!` semantically moves its argument on failure,
        // the `PanicOnDrop` is not dropped, and thus this shouldn't panic.
        let x: Result<usize, _> = try_transmute!(PanicOnDrop(1usize));
        assert_eq!(x, Ok(1));

        // Since `try_transmute!` semantically returns ownership of its argument
        // on failure, the `PanicOnDrop` is returned rather than dropped, and
        // thus this shouldn't panic.
        let y: Result<bool, _> = try_transmute!(PanicOnDrop(2u8));
        // We have to use `map_err` instead of comparing against
        // `Err(PanicOnDrop(2u8))` because the latter would create and then drop
        // its `PanicOnDrop` temporary, which would cause a panic.
        assert_eq!(y.as_ref().map_err(|p| &p.src.0), Err::<&bool, _>(&2u8));
        mem::forget(y);

        #[derive(Debug, TryFromBytes)]
        #[repr(C, align(8))]
        struct PaddedBool(bool);

        // A failed transmutation must return every source byte, including
        // bytes which would be padding in the destination type.
        let src = [2u8, 1, 2, 3, 4, 5, 6, 7];
        let x: Result<PaddedBool, _> = try_transmute!(src);
        assert_eq!(x.unwrap_err().into_src(), src);

        let x: Result<PaddedBool, _> = try_transmute!([0u8; 8]);
        assert!(!x.unwrap().0);
    }

    #[test]
    fn test_try_transmute_ref() {
        // Test that memory is transmuted with `try_transmute_ref` as expected.
        let array_of_bools = &[false, true, false, true, false, true, false, true];
        let array_of_arrays = &[[0, 1], [0, 1], [0, 1], [0, 1]];
        let x: Result<&[[u8; 2]; 4], _> = try_transmute_ref!(array_of_bools);
        assert_eq!(x, Ok(array_of_arrays));
        let x: Result<&[bool; 8], _> = try_transmute_ref!(array_of_arrays);
        assert_eq!(x, Ok(array_of_bools));

        // Test that it's legal to transmute a reference while shrinking the
        // lifetime.
        {
            let x: Result<&[[u8; 2]; 4], _> = try_transmute_ref!(array_of_bools);
            assert_eq!(x, Ok(array_of_arrays));
        }

        // Test that `try_transmute_ref!` supports decreasing alignment.
        let u = AU64(0);
        let array = [0u8, 0, 0, 0, 0, 0, 0, 0];
        let x: Result<&[u8; 8], _> = try_transmute_ref!(&u);
        assert_eq!(x, Ok(&array));

        // Test that a mutable reference can be turned into an immutable one.
        let mut x = 0u8;
        #[allow(clippy::useless_transmute)]
        let y: Result<&u8, _> = try_transmute_ref!(&mut x);
        assert_eq!(y, Ok(&0));

        // Test that sized types work which don't implement `KnownLayout`.
        let array_of_nkl_u8s = Nkl([0u8, 1, 2, 3, 4, 5, 6, 7]);
        let array_of_nkl_arrays = Nkl([[0, 1], [2, 3], [4, 5], [6, 7]]);
        let x: Result<&Nkl<[[u8; 2]; 4]>, _> = try_transmute_ref!(&array_of_nkl_u8s);
        assert_eq!(x, Ok(&array_of_nkl_arrays));

        // Test sized -> unsized transmutation.
        let array_of_u8s = [0u8, 1, 2, 3, 4, 5, 6, 7];
        let array_of_arrays = [[0, 1], [2, 3], [4, 5], [6, 7]];
        let slice_of_arrays = &array_of_arrays[..];
        let x: Result<&[[u8; 2]], _> = try_transmute_ref!(&array_of_u8s);
        assert_eq!(x, Ok(slice_of_arrays));

        // Test unsized -> unsized transmutation.
        let slice_dst_of_u8s =
            SliceDst::<U16, [u8; 2]>::ref_from_bytes(&[0, 1, 2, 3, 4, 5][..]).unwrap();
        let slice_dst_of_u16s =
            SliceDst::<U16, U16>::ref_from_bytes(&[0, 1, 2, 3, 4, 5][..]).unwrap();
        let x: Result<&SliceDst<U16, U16>, _> = try_transmute_ref!(slice_dst_of_u8s);
        assert_eq!(x, Ok(slice_dst_of_u16s));
    }

    #[test]
    fn test_try_transmute_mut() {
        // Test that memory is transmuted with `try_transmute_mut` as expected.
        let array_of_u8s = &mut [0u8, 1, 0, 1, 0, 1, 0, 1];
        let array_of_arrays = &mut [[0u8, 1], [0, 1], [0, 1], [0, 1]];
        let x: Result<&mut [[u8; 2]; 4], _> = try_transmute_mut!(array_of_u8s);
        assert_eq!(x, Ok(array_of_arrays));

        let array_of_bools = &mut [false, true, false, true, false, true, false, true];
        let array_of_arrays = &mut [[0u8, 1], [0, 1], [0, 1], [0, 1]];
        let x: Result<&mut [bool; 8], _> = try_transmute_mut!(array_of_arrays);
        assert_eq!(x, Ok(array_of_bools));

        // Test that it's legal to transmute a reference while shrinking the
        // lifetime.
        let array_of_bools = &mut [false, true, false, true, false, true, false, true];
        let array_of_arrays = &mut [[0u8, 1], [0, 1], [0, 1], [0, 1]];
        {
            let x: Result<&mut [bool; 8], _> = try_transmute_mut!(array_of_arrays);
            assert_eq!(x, Ok(array_of_bools));
        }

        // Test that `try_transmute_mut!` supports decreasing alignment.
        let u = &mut AU64(0);
        let array = &mut [0u8, 0, 0, 0, 0, 0, 0, 0];
        let x: Result<&mut [u8; 8], _> = try_transmute_mut!(u);
        assert_eq!(x, Ok(array));

        // Test that a mutable reference can be turned into an immutable one.
        let mut x = 0u8;
        #[allow(clippy::useless_transmute)]
        let y: Result<&mut u8, _> = try_transmute_mut!(&mut x);
        assert_eq!(y, Ok(&mut 0));

        // Test that sized types work which don't implement `KnownLayout`.
        let mut array_of_nkl_u8s = Nkl([0u8, 1, 2, 3, 4, 5, 6, 7]);
        let mut array_of_nkl_arrays = Nkl([[0, 1], [2, 3], [4, 5], [6, 7]]);
        let x: Result<&mut Nkl<[[u8; 2]; 4]>, _> = try_transmute_mut!(&mut array_of_nkl_u8s);
        assert_eq!(x, Ok(&mut array_of_nkl_arrays));

        // Test sized -> unsized transmutation.
        let mut array_of_u8s = [0u8, 1, 2, 3, 4, 5, 6, 7];
        let mut array_of_arrays = [[0, 1], [2, 3], [4, 5], [6, 7]];
        let slice_of_arrays = &mut array_of_arrays[..];
        let x: Result<&mut [[u8; 2]], _> = try_transmute_mut!(&mut array_of_u8s);
        assert_eq!(x, Ok(slice_of_arrays));

        // Test unsized -> unsized transmutation.
        let mut bytes = [0, 1, 2, 3, 4, 5, 6];
        let slice_dst_of_u8s = SliceDst::<u8, [u8; 2]>::mut_from_bytes(&mut bytes[..]).unwrap();
        let mut bytes = [0, 1, 2, 3, 4, 5, 6];
        let slice_dst_of_u16s = SliceDst::<u8, U16>::mut_from_bytes(&mut bytes[..]).unwrap();
        let x: Result<&mut SliceDst<u8, U16>, _> = try_transmute_mut!(slice_dst_of_u8s);
        assert_eq!(x, Ok(slice_dst_of_u16s));
    }

    #[test]
    fn test_transmute_mut() {
        // Test that memory is transmuted as expected.
        let mut array_of_u8s = [0u8, 1, 2, 3, 4, 5, 6, 7];
        let mut array_of_arrays = [[0, 1], [2, 3], [4, 5], [6, 7]];
        let x: &mut [[u8; 2]; 4] = transmute_mut!(&mut array_of_u8s);
        assert_eq!(*x, array_of_arrays);
        let x: &mut [u8; 8] = transmute_mut!(&mut array_of_arrays);
        assert_eq!(*x, array_of_u8s);

        {
            // Test that it's legal to transmute a reference while shrinking the
            // lifetime.
            let x: &mut [u8; 8] = transmute_mut!(&mut array_of_arrays);
            assert_eq!(*x, array_of_u8s);
        }

        // Test that `transmute_mut!` supports non-`KnownLayout` types.
        let mut array_of_u8s = Nkl([0u8, 1, 2, 3, 4, 5, 6, 7]);
        let mut array_of_arrays = Nkl([[0, 1], [2, 3], [4, 5], [6, 7]]);
        let x: &mut Nkl<[[u8; 2]; 4]> = transmute_mut!(&mut array_of_u8s);
        assert_eq!(*x, array_of_arrays);
        let x: &mut Nkl<[u8; 8]> = transmute_mut!(&mut array_of_arrays);
        assert_eq!(*x, array_of_u8s);

        // Test that `transmute_mut!` supports decreasing alignment.
        let mut u = AU64(0);
        let array = [0, 0, 0, 0, 0, 0, 0, 0];
        let x: &[u8; 8] = transmute_mut!(&mut u);
        assert_eq!(*x, array);

        // Test that a mutable reference can be turned into an immutable one.
        let mut x = 0u8;
        #[allow(clippy::useless_transmute)]
        let y: &u8 = transmute_mut!(&mut x);
        assert_eq!(*y, 0);

        // Test that `transmute_mut!` works on slice DSTs in and that memory is
        // transmuted as expected.
        let mut bytes = [0, 1, 2, 3, 4, 5, 6];
        let slice_dst_of_u8s = SliceDst::<u8, [u8; 2]>::mut_from_bytes(&mut bytes[..]).unwrap();
        let mut bytes = [0, 1, 2, 3, 4, 5, 6];
        let slice_dst_of_u16s = SliceDst::<u8, U16>::mut_from_bytes(&mut bytes[..]).unwrap();
        let x: &mut SliceDst<u8, U16> = transmute_mut!(slice_dst_of_u8s);
        assert_eq!(x, slice_dst_of_u16s);

        // Test that `transmute_mut!` works on slices that memory is transmuted
        // as expected.
        let array_of_u16s: &mut [u16] = &mut [0u16, 1, 2];
        let array_of_i16s: &mut [i16] = &mut [0i16, 1, 2];
        let x: &mut [i16] = transmute_mut!(array_of_u16s);
        assert_eq!(x, array_of_i16s);

        // Test that transmuting from a type with larger trailing slice offset
        // and larger trailing slice element works.
        let mut bytes = [0, 1, 2, 3, 4, 5, 6, 7];
        let slice_dst_big = SliceDst::<U32, U16>::mut_from_bytes(&mut bytes[..]).unwrap();
        let mut bytes = [0, 1, 2, 3, 4, 5, 6, 7];
        let slice_dst_small = SliceDst::<U16, u8>::mut_from_bytes(&mut bytes[..]).unwrap();
        let x: &mut SliceDst<U16, u8> = transmute_mut!(slice_dst_big);
        assert_eq!(x, slice_dst_small);

        // Test sized -> unsized transmutation.
        let mut array_of_u8s = [0u8, 1, 2, 3, 4, 5, 6, 7];
        let mut array_of_arrays = [[0, 1], [2, 3], [4, 5], [6, 7]];
        let slice_of_arrays = &mut array_of_arrays[..];
        let x: &mut [[u8; 2]] = transmute_mut!(&mut array_of_u8s);
        assert_eq!(x, slice_of_arrays);
    }

    #[test]
    fn test_macros_evaluate_args_once() {
        let mut ctr = 0;
        #[allow(clippy::useless_transmute)]
        let _: usize = transmute!({
            ctr += 1;
            0usize
        });
        assert_eq!(ctr, 1);

        let mut ctr = 0;
        let _: &usize = transmute_ref!({
            ctr += 1;
            &0usize
        });
        assert_eq!(ctr, 1);

        let mut ctr: usize = 0;
        let _: &mut usize = transmute_mut!({
            ctr += 1;
            &mut ctr
        });
        assert_eq!(ctr, 1);

        let mut ctr = 0;
        #[allow(clippy::useless_transmute)]
        let _: usize = try_transmute!({
            ctr += 1;
            0usize
        })
        .unwrap();
        assert_eq!(ctr, 1);
    }

    #[test]
    fn test_include_value() {
        const AS_U32: u32 = include_value!("../testdata/include_value/data");
        assert_eq!(AS_U32, u32::from_ne_bytes([b'a', b'b', b'c', b'd']));
        const AS_I32: i32 = include_value!("../testdata/include_value/data");
        assert_eq!(AS_I32, i32::from_ne_bytes([b'a', b'b', b'c', b'd']));
    }

    #[test]
    #[allow(non_camel_case_types, unreachable_pub, dead_code)]
    fn test_cryptocorrosion_derive_traits() {
        // Test the set of invocations added in
        // https://github.com/cryptocorrosion/cryptocorrosion/pull/85

        fn assert_impls<T: FromBytes + IntoBytes + Immutable>() {}

        cryptocorrosion_derive_traits! {
            #[repr(C)]
            #[derive(Clone, Copy)]
            pub union vec128_storage {
                d: [u32; 4],
                q: [u64; 2],
            }
        }

        assert_impls::<vec128_storage>();

        cryptocorrosion_derive_traits! {
            #[repr(transparent)]
            #[derive(Copy, Clone, Debug, PartialEq)]
            pub struct u32x4_generic([u32; 4]);
        }

        assert_impls::<u32x4_generic>();

        cryptocorrosion_derive_traits! {
            #[repr(transparent)]
            #[derive(Copy, Clone, Debug, PartialEq)]
            pub struct u64x2_generic([u64; 2]);
        }

        assert_impls::<u64x2_generic>();

        cryptocorrosion_derive_traits! {
            #[repr(transparent)]
            #[derive(Copy, Clone, Debug, PartialEq)]
            pub struct u128x1_generic([u128; 1]);
        }

        assert_impls::<u128x1_generic>();

        cryptocorrosion_derive_traits! {
            #[repr(transparent)]
            #[derive(Copy, Clone, Default)]
            #[allow(non_camel_case_types)]
            pub struct x2<W, G>(pub [W; 2], PhantomData<G>);
        }

        enum NotZerocopy {}
        assert_impls::<x2<(), NotZerocopy>>();

        cryptocorrosion_derive_traits! {
            #[repr(transparent)]
            #[derive(Copy, Clone, Default)]
            #[allow(non_camel_case_types)]
            pub struct x4<W>(pub [W; 4]);
        }

        assert_impls::<x4<()>>();

        #[cfg(feature = "simd")]
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            #[cfg(target_arch = "x86")]
            use core::arch::x86::{__m128i, __m256i};
            #[cfg(target_arch = "x86_64")]
            use core::arch::x86_64::{__m128i, __m256i};

            cryptocorrosion_derive_traits! {
                #[repr(C)]
                #[derive(Copy, Clone)]
                pub struct X4(__m128i, __m128i, __m128i, __m128i);
            }

            assert_impls::<X4>();

            cryptocorrosion_derive_traits! {
                #[repr(C)]
                /// Generic wrapper for unparameterized storage of any of the
                /// possible impls. Converting into and out of this type should
                /// be essentially free, although it may be more aligned than a
                /// particular impl requires.
                #[allow(non_camel_case_types)]
                #[derive(Copy, Clone)]
                pub union vec128_storage {
                    u32x4: [u32; 4],
                    u64x2: [u64; 2],
                    u128x1: [u128; 1],
                    sse2: __m128i,
                }
            }

            assert_impls::<vec128_storage>();

            cryptocorrosion_derive_traits! {
                #[repr(transparent)]
                #[allow(non_camel_case_types)]
                #[derive(Copy, Clone)]
                pub struct vec<S3, S4, NI> {
                    x: __m128i,
                    s3: PhantomData<S3>,
                    s4: PhantomData<S4>,
                    ni: PhantomData<NI>,
                }
            }

            assert_impls::<vec<NotZerocopy, NotZerocopy, NotZerocopy>>();

            cryptocorrosion_derive_traits! {
                #[repr(transparent)]
                #[derive(Copy, Clone)]
                pub struct u32x4x2_avx2<NI> {
                    x: __m256i,
                    ni: PhantomData<NI>,
                }
            }

            assert_impls::<u32x4x2_avx2<NotZerocopy>>();
        }

        // Make sure that our derive works for `#[repr(C)]` structs even though
        // cryptocorrosion doesn't currently have any.
        cryptocorrosion_derive_traits! {
            #[repr(C)]
            #[derive(Copy, Clone, Debug, PartialEq)]
            pub struct ReprC(u8, u8, u16);
        }
    }
}
