// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use dissimilar::Chunk;
use proc_macro2::TokenStream;

macro_rules! use_as_trait_name {
    ($($alias:ident => $derive:ident),* $(,)?) => {
        $(use super::$derive as $alias;)*
    };
}

// This permits invocations of `test!` to be more ergonomic, passing the name of
// the trait under test rather than the name of the inner derive function.
use_as_trait_name!(
    KnownLayout => derive_known_layout_inner,
    Immutable => derive_no_cell_inner,
    TryFromBytes => derive_try_from_bytes_inner,
    FromZeros => derive_from_zeros_inner,
    FromBytes => derive_from_bytes_inner,
    IntoBytes => derive_into_bytes_inner,
    Unaligned => derive_unaligned_inner,
);

/// Test that the given derive input expands to the expected output.
///
/// Equality is tested by formatting both token streams using `prettyplease` and
/// performing string equality on the results. This has the effect of making the
/// tests less brittle and robust against meaningless formatting changes.
// Adapted from https://github.com/joshlf/synstructure/blob/400499aaf54840056ff56718beb7810540e6be59/src/macros.rs#L212-L317
macro_rules! test {
    ($name:path { $($i:tt)* } expands to { $($o:tt)* }) => {
        {
            #[allow(dead_code)]
            fn ensure_compiles() {
                $($i)*
                $($o)*
            }

            test!($name { $($i)* } expands to { $($o)* } no_build);
        }
    };

    ($name:path { $($i:tt)* } expands to { $($o:tt)* } no_build) => {
        {
            let ts: proc_macro2::TokenStream = quote::quote!( $($i)* );
            let ast = syn::parse2::<syn::DeriveInput>(ts).unwrap();
            let res = $name(super::Ctx::new(&ast));
            let expected_toks = quote::quote!( $($o)* );
            assert_eq_streams(expected_toks.into(), res.into());
        }
    };
}

fn assert_eq_streams(expect: TokenStream, res: TokenStream) {
    let pretty =
        |ts: TokenStream| prettyplease::unparse(&syn::parse_file(&ts.to_string()).unwrap());

    let expect = pretty(expect.clone());
    let res = pretty(res.clone());
    if expect != res {
        let diff = dissimilar::diff(&expect, &res)
            .into_iter()
            .flat_map(|chunk| {
                let (prefix, chunk) = match chunk {
                    Chunk::Equal(chunk) => (" ", chunk),
                    Chunk::Delete(chunk) => ("-", chunk),
                    Chunk::Insert(chunk) => ("+", chunk),
                };
                [prefix, chunk, "\n"]
            })
            .collect::<String>();

        panic!(
            "\
test failed:
got:
```
{}
```

diff (expected vs got):
```
{}
```\n",
            res, diff
        );
    }
}

#[test]
fn test_known_layout() {
    test! {
        KnownLayout {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl ::zerocopy::KnownLayout for Foo
            where
                Self: ::zerocopy::util::macro_util::core_reexport::marker::Sized,
            {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                type PointerMetadata = ();

                const LAYOUT: ::zerocopy::DstLayout = ::zerocopy::DstLayout::for_type::<Self>();

                #[inline(always)]
                fn raw_from_ptr_len(
                    bytes: ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<u8>,
                    _meta: (),
                ) -> ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<Self> {
                    bytes.cast::<Self>()
                }

                #[inline(always)]
                fn pointer_to_metadata(
                    _ptr: ::zerocopy::util::macro_util::core_reexport::ptr::NonNull<Self>,
                ) -> () {
                }
            }
        } no_build
    }
}

#[test]
fn test_immutable() {
    test! {
        Immutable {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl ::zerocopy::Immutable for Foo {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_try_from_bytes() {
    test! {
        TryFromBytes {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl ::zerocopy::TryFromBytes for Foo {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                fn is_bit_valid<
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>,
                >(
                    mut candidate: ::zerocopy::Maybe<Self, A>,
                ) -> bool {
                    true
                }
            }
        } no_build
    }
}

#[test]
fn test_from_zeros() {
    test! {
        FromZeros {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl ::zerocopy::TryFromBytes for Foo {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                fn is_bit_valid<
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>,
                >(
                    mut candidate: ::zerocopy::Maybe<Self, A>,
                ) -> bool {
                    true
                }
            }

            #[allow(deprecated)]
            unsafe impl ::zerocopy::FromZeros for Foo {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_from_bytes() {
    test! {
        FromBytes {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl ::zerocopy::TryFromBytes for Foo {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                fn is_bit_valid<
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>,
                >(
                    mut candidate: ::zerocopy::Maybe<Self, A>,
                ) -> bool {
                    true
                }
            }

            #[allow(deprecated)]
            unsafe impl ::zerocopy::FromZeros for Foo {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }

            #[allow(deprecated)]
            unsafe impl ::zerocopy::FromBytes for Foo {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_into_bytes() {
    test! {
        IntoBytes {
            #[repr(C)]
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl ::zerocopy::IntoBytes for Foo {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }

    test! {
        IntoBytes {
            #[repr(C)]
            struct Foo {
                a: u8,
                b: u8,
            }
        } expands to {
            #[allow(deprecated)]
            unsafe impl ::zerocopy::IntoBytes for Foo
            where
                u8: ::zerocopy::IntoBytes,
                u8: ::zerocopy::IntoBytes,
                (): ::zerocopy::util::macro_util::PaddingFree<
                    Foo,
                    { ::zerocopy::struct_has_padding!(Foo, [u8, u8]) },
                >,
            {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_unaligned() {
    test! {
        Unaligned {
            #[repr(C)]
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl ::zerocopy::Unaligned for Foo {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_try_from_bytes_enum() {
    test! {
        TryFromBytes {
            #[repr(u8)]
            enum ComplexWithGenerics<'a: 'static, const N: usize, X, Y: Deref>
            where
                X: Deref<Target = &'a [(X, Y); N]>,
            {
                UnitLike,
                StructLike { a: u8, b: X, c: X::Target, d: Y::Target, e: [(X, Y); N] },
                TupleLike(bool, Y, PhantomData<&'a [(X, Y); N]>),
            }
        } expands to {
            #[allow(deprecated)]
            unsafe impl<'a: 'static, const N: usize, X, Y: Deref> ::zerocopy::TryFromBytes
                for ComplexWithGenerics<'a, { N }, X, Y>
            where
                X: Deref<Target = &'a [(X, Y); N]>,
                u8: ::zerocopy::TryFromBytes,
                X: ::zerocopy::TryFromBytes,
                X::Target: ::zerocopy::TryFromBytes,
                Y::Target: ::zerocopy::TryFromBytes,
                [(X, Y); N]: ::zerocopy::TryFromBytes,
                bool: ::zerocopy::TryFromBytes,
                Y: ::zerocopy::TryFromBytes,
                PhantomData<&'a [(X, Y); N]>: ::zerocopy::TryFromBytes,
            {
                fn only_derive_is_allowed_to_implement_this_trait() {}
                fn is_bit_valid<___ZEROCOPY_Aliasing_0>(
                    mut candidate: ::zerocopy::Maybe<'_, Self, ___ZEROCOPY_Aliasing_0>,
                ) -> ::zerocopy::util::macro_util::core_reexport::primitive::bool
                where
                    ___ZEROCOPY_Aliasing_0: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>,
                {
                    use ::zerocopy::util::macro_util::core_reexport;
                    #[repr(u8)]
                    #[allow(dead_code)]
                    enum ___ZEROCOPY_Tag_0 {
                        UnitLike,
                        StructLike,
                        TupleLike,
                    }
                    type ___ZEROCOPY_TagPrimitive_0 = ::zerocopy::util::macro_util::SizeToTag<
                        { core_reexport::mem::size_of::<___ZEROCOPY_Tag_0>() },
                    >;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_UnitLike_0: ___ZEROCOPY_TagPrimitive_0 =
                        ___ZEROCOPY_Tag_0::UnitLike as ___ZEROCOPY_TagPrimitive_0;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_StructLike_0: ___ZEROCOPY_TagPrimitive_0 =
                        ___ZEROCOPY_Tag_0::StructLike as ___ZEROCOPY_TagPrimitive_0;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_TupleLike_0: ___ZEROCOPY_TagPrimitive_0 =
                        ___ZEROCOPY_Tag_0::TupleLike as ___ZEROCOPY_TagPrimitive_0;
                    type ___ZEROCOPY_OuterTag_0 = ();
                    type ___ZEROCOPY_InnerTag_0 = ___ZEROCOPY_Tag_0;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(::zerocopy_derive::TryFromBytes)]
                    struct ___ZEROCOPY_VariantStruct_StructLike_0<'a: 'static, const N: usize, X, Y: Deref>(
                        core_reexport::mem::MaybeUninit<___ZEROCOPY_InnerTag_0>,
                        u8,
                        X,
                        X::Target,
                        Y::Target,
                        [(X, Y); N],
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y>>,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(::zerocopy_derive::TryFromBytes)]
                    struct ___ZEROCOPY_VariantStruct_TupleLike_0<'a: 'static, const N: usize, X, Y: Deref>(
                        core_reexport::mem::MaybeUninit<___ZEROCOPY_InnerTag_0>,
                        bool,
                        Y,
                        PhantomData<&'a [(X, Y); N]>,
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y>>,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    union ___ZEROCOPY_Variants_0<'a: 'static, const N: usize, X, Y: Deref> {
                        ___ZEROCOPY_field_StructLike_0: core_reexport::mem::ManuallyDrop<
                            ___ZEROCOPY_VariantStruct_StructLike_0<'a, N, X, Y>,
                        >,
                        ___ZEROCOPY_field_TupleLike_0: core_reexport::mem::ManuallyDrop<
                            ___ZEROCOPY_VariantStruct_TupleLike_0<'a, N, X, Y>,
                        >,
                        ___ZEROCOPY_nonempty_0: (),
                    }
                    #[repr(C)]
                    struct ___ZEROCOPY_RawEnum_0<'a: 'static, const N: usize, X, Y: Deref> {
                        tag: ___ZEROCOPY_OuterTag_0,
                        variants: ___ZEROCOPY_Variants_0<'a, N, X, Y>,
                    }
                    let tag = {
                        let tag_ptr = unsafe {
                            candidate
                                .reborrow()
                                .cast_unsized(|p: *mut Self| { p as *mut ___ZEROCOPY_TagPrimitive_0 })
                        };
                        let tag_ptr = unsafe { tag_ptr.assume_initialized() };
                        tag_ptr.bikeshed_recall_valid().read_unaligned()
                    };
                    let raw_enum = unsafe {
                        candidate.cast_unsized(|p: *mut Self| { p as *mut ___ZEROCOPY_RawEnum_0<'a, N, X, Y> })
                    };
                    let raw_enum = unsafe { raw_enum.assume_initialized() };
                    let variants = unsafe {
                        raw_enum.project(|p: *mut ___ZEROCOPY_RawEnum_0<'a, N, X, Y>| {
                            core_reexport::ptr::addr_of_mut!((*p).variants)
                        })
                    };
                    #[allow(non_upper_case_globals)]
                    match tag {
                        ___ZEROCOPY_TAG_UnitLike_0 => true,
                        ___ZEROCOPY_TAG_StructLike_0 => {
                            let variant = unsafe {
                                variants.cast_unsized(|p: *mut ___ZEROCOPY_Variants_0<'a, N, X, Y>| {
                                    p as *mut ___ZEROCOPY_VariantStruct_StructLike_0<'a, N, X, Y>
                                })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            <___ZEROCOPY_VariantStruct_StructLike_0<
                                'a,
                                N,
                                X,
                                Y,
                            > as ::zerocopy::TryFromBytes>::is_bit_valid(variant)
                        }
                        ___ZEROCOPY_TAG_TupleLike_0 => {
                            let variant = unsafe {
                                variants.cast_unsized(|p: *mut ___ZEROCOPY_Variants_0<'a, N, X, Y>| {
                                    p as *mut ___ZEROCOPY_VariantStruct_TupleLike_0<'a, N, X, Y>
                                })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            <___ZEROCOPY_VariantStruct_TupleLike_0<
                                'a,
                                N,
                                X,
                                Y,
                            > as ::zerocopy::TryFromBytes>::is_bit_valid(variant)
                        }
                        _ => false,
                    }
                }
            }
        } no_build
    }

    test! {
        TryFromBytes {
            #[repr(u32)]
            enum ComplexWithGenerics<'a: 'static, const N: usize, X, Y: Deref>
            where
                X: Deref<Target = &'a [(X, Y); N]>,
            {
                UnitLike,
                StructLike { a: u8, b: X, c: X::Target, d: Y::Target, e: [(X, Y); N] },
                TupleLike(bool, Y, PhantomData<&'a [(X, Y); N]>),
            }
        } expands to {
            #[allow(deprecated)]
            unsafe impl<'a: 'static, const N: usize, X, Y: Deref> ::zerocopy::TryFromBytes
                for ComplexWithGenerics<'a, { N }, X, Y>
            where
                X: Deref<Target = &'a [(X, Y); N]>,
                u8: ::zerocopy::TryFromBytes,
                X: ::zerocopy::TryFromBytes,
                X::Target: ::zerocopy::TryFromBytes,
                Y::Target: ::zerocopy::TryFromBytes,
                [(X, Y); N]: ::zerocopy::TryFromBytes,
                bool: ::zerocopy::TryFromBytes,
                Y: ::zerocopy::TryFromBytes,
                PhantomData<&'a [(X, Y); N]>: ::zerocopy::TryFromBytes,
            {
                fn only_derive_is_allowed_to_implement_this_trait() {}
                fn is_bit_valid<___ZEROCOPY_Aliasing_0>(
                    mut candidate: ::zerocopy::Maybe<'_, Self, ___ZEROCOPY_Aliasing_0>,
                ) -> ::zerocopy::util::macro_util::core_reexport::primitive::bool
                where
                    ___ZEROCOPY_Aliasing_0: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>,
                {
                    use ::zerocopy::util::macro_util::core_reexport;
                    #[repr(u8)]
                    #[allow(dead_code)]
                    enum ___ZEROCOPY_Tag_0 {
                        UnitLike,
                        StructLike,
                        TupleLike,
                    }
                    type ___ZEROCOPY_TagPrimitive_0 = ::zerocopy::util::macro_util::SizeToTag<
                        { core_reexport::mem::size_of::<___ZEROCOPY_Tag_0>() },
                    >;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_UnitLike_0: ___ZEROCOPY_TagPrimitive_0 =
                        ___ZEROCOPY_Tag_0::UnitLike as ___ZEROCOPY_TagPrimitive_0;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_StructLike_0: ___ZEROCOPY_TagPrimitive_0 =
                        ___ZEROCOPY_Tag_0::StructLike as ___ZEROCOPY_TagPrimitive_0;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_TupleLike_0: ___ZEROCOPY_TagPrimitive_0 =
                        ___ZEROCOPY_Tag_0::TupleLike as ___ZEROCOPY_TagPrimitive_0;
                    type ___ZEROCOPY_OuterTag_0 = ();
                    type ___ZEROCOPY_InnerTag_0 = ___ZEROCOPY_Tag_0;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(::zerocopy_derive::TryFromBytes)]
                    struct ___ZEROCOPY_VariantStruct_StructLike_0<'a: 'static, const N: usize, X, Y: Deref>(
                        core_reexport::mem::MaybeUninit<___ZEROCOPY_InnerTag_0>,
                        u8,
                        X,
                        X::Target,
                        Y::Target,
                        [(X, Y); N],
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y>>,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(::zerocopy_derive::TryFromBytes)]
                    struct ___ZEROCOPY_VariantStruct_TupleLike_0<'a: 'static, const N: usize, X, Y: Deref>(
                        core_reexport::mem::MaybeUninit<___ZEROCOPY_InnerTag_0>,
                        bool,
                        Y,
                        PhantomData<&'a [(X, Y); N]>,
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y>>,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    union ___ZEROCOPY_Variants_0<'a: 'static, const N: usize, X, Y: Deref> {
                        ___ZEROCOPY_field_StructLike_0: core_reexport::mem::ManuallyDrop<
                            ___ZEROCOPY_VariantStruct_StructLike_0<'a, N, X, Y>,
                        >,
                        ___ZEROCOPY_field_TupleLike_0: core_reexport::mem::ManuallyDrop<
                            ___ZEROCOPY_VariantStruct_TupleLike_0<'a, N, X, Y>,
                        >,
                        ___ZEROCOPY_nonempty_0: (),
                    }
                    #[repr(C)]
                    struct ___ZEROCOPY_RawEnum_0<'a: 'static, const N: usize, X, Y: Deref> {
                        tag: ___ZEROCOPY_OuterTag_0,
                        variants: ___ZEROCOPY_Variants_0<'a, N, X, Y>,
                    }
                    let tag = {
                        let tag_ptr = unsafe {
                            candidate
                                .reborrow()
                                .cast_unsized(|p: *mut Self| { p as *mut ___ZEROCOPY_TagPrimitive_0 })
                        };
                        let tag_ptr = unsafe { tag_ptr.assume_initialized() };
                        tag_ptr.bikeshed_recall_valid().read_unaligned()
                    };
                    let raw_enum = unsafe {
                        candidate.cast_unsized(|p: *mut Self| { p as *mut ___ZEROCOPY_RawEnum_0<'a, N, X, Y> })
                    };
                    let raw_enum = unsafe { raw_enum.assume_initialized() };
                    let variants = unsafe {
                        raw_enum.project(|p: *mut ___ZEROCOPY_RawEnum_0<'a, N, X, Y>| {
                            core_reexport::ptr::addr_of_mut!((*p).variants)
                        })
                    };
                    #[allow(non_upper_case_globals)]
                    match tag {
                        ___ZEROCOPY_TAG_UnitLike_0 => true,
                        ___ZEROCOPY_TAG_StructLike_0 => {
                            let variant = unsafe {
                                variants.cast_unsized(|p: *mut ___ZEROCOPY_Variants_0<'a, N, X, Y>| {
                                    p as *mut ___ZEROCOPY_VariantStruct_StructLike_0<'a, N, X, Y>
                                })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            <___ZEROCOPY_VariantStruct_StructLike_0<
                                'a,
                                N,
                                X,
                                Y,
                            > as ::zerocopy::TryFromBytes>::is_bit_valid(variant)
                        }
                        ___ZEROCOPY_TAG_TupleLike_0 => {
                            let variant = unsafe {
                                variants.cast_unsized(|p: *mut ___ZEROCOPY_Variants_0<'a, N, X, Y>| {
                                    p as *mut ___ZEROCOPY_VariantStruct_TupleLike_0<'a, N, X, Y>
                                })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            <___ZEROCOPY_VariantStruct_TupleLike_0<
                                'a,
                                N,
                                X,
                                Y,
                            > as ::zerocopy::TryFromBytes>::is_bit_valid(variant)
                        }
                        _ => false,
                    }
                }
            }
        } no_build
    }

    test! {
        TryFromBytes {
            #[repr(C)]
            enum ComplexWithGenerics<'a: 'static, const N: usize, X, Y: Deref>
            where
                X: Deref<Target = &'a [(X, Y); N]>,
            {
                UnitLike,
                StructLike { a: u8, b: X, c: X::Target, d: Y::Target, e: [(X, Y); N] },
                TupleLike(bool, Y, PhantomData<&'a [(X, Y); N]>),
            }
        } expands to {
            #[allow(deprecated)]
            unsafe impl<'a: 'static, const N: usize, X, Y: Deref> ::zerocopy::TryFromBytes
            for ComplexWithGenerics<'a, { N }, X, Y>
            where
                X: Deref<Target = &'a [(X, Y); N]>,
                u8: ::zerocopy::TryFromBytes,
                X: ::zerocopy::TryFromBytes,
                X::Target: ::zerocopy::TryFromBytes,
                Y::Target: ::zerocopy::TryFromBytes,
                [(X, Y); N]: ::zerocopy::TryFromBytes,
                bool: ::zerocopy::TryFromBytes,
                Y: ::zerocopy::TryFromBytes,
                PhantomData<&'a [(X, Y); N]>: ::zerocopy::TryFromBytes,
            {
                fn only_derive_is_allowed_to_implement_this_trait() {}
                fn is_bit_valid<___ZEROCOPY_Aliasing_0>(
                    mut candidate: ::zerocopy::Maybe<'_, Self, ___ZEROCOPY_Aliasing_0>,
                ) -> ::zerocopy::util::macro_util::core_reexport::primitive::bool
                where
                    ___ZEROCOPY_Aliasing_0: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<
                            ::zerocopy::pointer::invariant::Shared,
                        >,
                {
                    use ::zerocopy::util::macro_util::core_reexport;
                    #[repr(u32)]
                    #[allow(dead_code)]
                    enum ___ZEROCOPY_Tag_0 {
                        UnitLike,
                        StructLike,
                        TupleLike,
                    }
                    type ___ZEROCOPY_TagPrimitive_0 = ::zerocopy::util::macro_util::SizeToTag<
                        { core_reexport::mem::size_of::<___ZEROCOPY_Tag_0>() },
                    >;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_UnitLike_0: ___ZEROCOPY_TagPrimitive_0 = ___ZEROCOPY_Tag_0::UnitLike
                        as ___ZEROCOPY_TagPrimitive_0;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_StructLike_0: ___ZEROCOPY_TagPrimitive_0 = ___ZEROCOPY_Tag_0::StructLike
                        as ___ZEROCOPY_TagPrimitive_0;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_TupleLike_0: ___ZEROCOPY_TagPrimitive_0 = ___ZEROCOPY_Tag_0::TupleLike
                        as ___ZEROCOPY_TagPrimitive_0;
                    type ___ZEROCOPY_OuterTag_0 = ();
                    type ___ZEROCOPY_InnerTag_0 = ___ZEROCOPY_Tag_0;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(::zerocopy_derive::TryFromBytes)]
                    struct ___ZEROCOPY_VariantStruct_StructLike_0<
                        'a: 'static,
                        const N: usize,
                        X,
                        Y: Deref,
                    >(
                        core_reexport::mem::MaybeUninit<___ZEROCOPY_InnerTag_0>,
                        u8,
                        X,
                        X::Target,
                        Y::Target,
                        [(X, Y); N],
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y>>,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(::zerocopy_derive::TryFromBytes)]
                    struct ___ZEROCOPY_VariantStruct_TupleLike_0<
                        'a: 'static,
                        const N: usize,
                        X,
                        Y: Deref,
                    >(
                        core_reexport::mem::MaybeUninit<___ZEROCOPY_InnerTag_0>,
                        bool,
                        Y,
                        PhantomData<&'a [(X, Y); N]>,
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y>>,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    union ___ZEROCOPY_Variants_0<'a: 'static, const N: usize, X, Y: Deref> {
                        ___ZEROCOPY_field_StructLike_0: core_reexport::mem::ManuallyDrop<
                            ___ZEROCOPY_VariantStruct_StructLike_0<'a, N, X, Y>,
                        >,
                        ___ZEROCOPY_field_TupleLike_0: core_reexport::mem::ManuallyDrop<
                            ___ZEROCOPY_VariantStruct_TupleLike_0<'a, N, X, Y>,
                        >,
                        ___ZEROCOPY_nonempty_0: (),
                    }
                    #[repr(C)]
                    struct ___ZEROCOPY_RawEnum_0<'a: 'static, const N: usize, X, Y: Deref> {
                        tag: ___ZEROCOPY_OuterTag_0,
                        variants: ___ZEROCOPY_Variants_0<'a, N, X, Y>,
                    }
                    let tag = {
                        let tag_ptr = unsafe {
                            candidate
                                .reborrow()
                                .cast_unsized(|p: *mut Self| {
                                    p as *mut ___ZEROCOPY_TagPrimitive_0
                                })
                        };
                        let tag_ptr = unsafe { tag_ptr.assume_initialized() };
                        tag_ptr.bikeshed_recall_valid().read_unaligned()
                    };
                    let raw_enum = unsafe {
                        candidate
                            .cast_unsized(|p: *mut Self| {
                                p as *mut ___ZEROCOPY_RawEnum_0<'a, N, X, Y>
                            })
                    };
                    let raw_enum = unsafe { raw_enum.assume_initialized() };
                    let variants = unsafe {
                        raw_enum
                            .project(|p: *mut ___ZEROCOPY_RawEnum_0<'a, N, X, Y>| {
                                core_reexport::ptr::addr_of_mut!((* p).variants)
                            })
                    };
                    #[allow(non_upper_case_globals)]
                    match tag {
                        ___ZEROCOPY_TAG_UnitLike_0 => true,
                        ___ZEROCOPY_TAG_StructLike_0 => {
                            let variant = unsafe {
                                variants
                                    .cast_unsized(|p: *mut ___ZEROCOPY_Variants_0<'a, N, X, Y>| {
                                        p as *mut ___ZEROCOPY_VariantStruct_StructLike_0<'a, N, X, Y>
                                    })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            <___ZEROCOPY_VariantStruct_StructLike_0<
                                'a,
                                N,
                                X,
                                Y,
                            > as ::zerocopy::TryFromBytes>::is_bit_valid(variant)
                        }
                        ___ZEROCOPY_TAG_TupleLike_0 => {
                            let variant = unsafe {
                                variants
                                    .cast_unsized(|p: *mut ___ZEROCOPY_Variants_0<'a, N, X, Y>| {
                                        p as *mut ___ZEROCOPY_VariantStruct_TupleLike_0<'a, N, X, Y>
                                    })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            <___ZEROCOPY_VariantStruct_TupleLike_0<
                                'a,
                                N,
                                X,
                                Y,
                            > as ::zerocopy::TryFromBytes>::is_bit_valid(variant)
                        }
                        _ => false,
                    }
                }
            }
        } no_build
    }
}
