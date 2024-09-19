// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use synstructure::test_derive;

macro_rules! impl_synstructure_derive {
    ($($outer:ident => $inner:ident),* $(,)?) => {
        $(
            #[allow(non_snake_case)]
            fn $outer(s: synstructure::Structure) -> proc_macro2::TokenStream {
                super::$inner(s.ast())
            }
        )*
    };
}

impl_synstructure_derive!(
    KnownLayout => derive_known_layout_inner,
    Immutable => derive_no_cell_inner,
    TryFromBytes => derive_try_from_bytes_inner,
    FromZeros => derive_from_zeros_inner,
    FromBytes => derive_from_bytes_inner,
    IntoBytes => derive_into_bytes_inner,
    Unaligned => derive_unaligned_inner,
);

#[test]
fn test_known_layout() {
    test_derive! {
        KnownLayout {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::KnownLayout for Foo<>
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
    test_derive! {
        Immutable {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::Immutable for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_try_from_bytes() {
    test_derive! {
        TryFromBytes {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::TryFromBytes for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                fn is_bit_valid<
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>
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
    test_derive! {
        FromZeros {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::TryFromBytes for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                fn is_bit_valid<
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>
                >(
                    mut candidate: ::zerocopy::Maybe<Self, A>,
                ) -> bool {
                    true
                }
            }

            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::FromZeros for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_from_bytes() {
    test_derive! {
        FromBytes {
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::TryFromBytes for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}

                fn is_bit_valid<
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>
                >(
                    mut candidate: ::zerocopy::Maybe<Self, A>,
                ) -> bool {
                    true
                }
            }

            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::FromZeros for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }

            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::FromBytes for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_into_bytes() {
    test_derive! {
        IntoBytes {
            #[repr(C)]
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::IntoBytes for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_unaligned() {
    test_derive! {
        Unaligned {
            #[repr(C)]
            struct Foo;
        } expands to {
            #[allow(deprecated)]
            unsafe impl<> ::zerocopy::Unaligned for Foo<> where {
                fn only_derive_is_allowed_to_implement_this_trait() {}
            }
        } no_build
    }
}

#[test]
fn test_try_from_bytes_enum() {
    test_derive! {
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
                fn is_bit_valid<A>(
                    mut candidate: ::zerocopy::Maybe<'_, Self, A>,
                ) -> ::zerocopy::util::macro_util::core_reexport::primitive::bool
                where
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>,
                {
                    use ::zerocopy::util::macro_util::core_reexport;
                    #[repr(u8)]
                    #[allow(dead_code)]
                    enum ___ZerocopyTag {
                        UnitLike,
                        StructLike,
                        TupleLike,
                    }
                    type ___ZerocopyTagPrimitive = ::zerocopy::util::macro_util::SizeToTag<
                        { core_reexport::mem::size_of::<___ZerocopyTag>() },
                    >;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_UnitLike: ___ZerocopyTagPrimitive =
                        ___ZerocopyTag::UnitLike as ___ZerocopyTagPrimitive;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_StructLike: ___ZerocopyTagPrimitive =
                        ___ZerocopyTag::StructLike as ___ZerocopyTagPrimitive;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_TupleLike: ___ZerocopyTagPrimitive =
                        ___ZerocopyTag::TupleLike as ___ZerocopyTagPrimitive;
                    type ___ZerocopyOuterTag = ();
                    type ___ZerocopyInnerTag = ___ZerocopyTag;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(:: zerocopy_derive :: TryFromBytes)]
                    struct ___ZerocopyVariantStruct_StructLike<'a: 'static, const N: usize, X, Y: Deref>(
                        core_reexport::mem::MaybeUninit<___ZerocopyInnerTag>,
                        u8,
                        X,
                        X::Target,
                        Y::Target,
                        [(X, Y); N],
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y> >,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>,;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(:: zerocopy_derive :: TryFromBytes)]
                    struct ___ZerocopyVariantStruct_TupleLike<'a: 'static, const N: usize, X, Y: Deref>(
                        core_reexport::mem::MaybeUninit<___ZerocopyInnerTag>,
                        bool,
                        Y,
                        PhantomData<&'a [(X, Y); N]>,
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y> >,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>,;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    union ___ZerocopyVariants<'a: 'static, const N: usize, X, Y: Deref> {
                        __field_StructLike:
                            core_reexport::mem::ManuallyDrop<___ZerocopyVariantStruct_StructLike<'a, N, X, Y> >,
                        __field_TupleLike:
                            core_reexport::mem::ManuallyDrop<___ZerocopyVariantStruct_TupleLike<'a, N, X, Y> >,
                        __nonempty: (),
                    }
                    #[repr(C)]
                    struct ___ZerocopyRawEnum<'a: 'static, const N: usize, X, Y: Deref> {
                        tag: ___ZerocopyOuterTag,
                        variants: ___ZerocopyVariants<'a, N, X, Y>,
                    }
                    let tag = {
                        let tag_ptr = unsafe {
                            candidate.reborrow().cast_unsized(|p: *mut Self| { p as *mut ___ZerocopyTagPrimitive })
                        };
                        let tag_ptr = unsafe { tag_ptr.assume_initialized() };
                        tag_ptr.bikeshed_recall_valid().read_unaligned()
                    };
                    let raw_enum = unsafe {
                        candidate.cast_unsized(|p: *mut Self| { p as *mut ___ZerocopyRawEnum<'a, N, X, Y> })
                    };
                    let raw_enum = unsafe { raw_enum.assume_initialized() };
                    let variants = unsafe {
                        raw_enum.project(|p: *mut ___ZerocopyRawEnum<'a, N, X, Y>| {
                            core_reexport::ptr::addr_of_mut!((*p).variants)
                        })
                    };
                    #[allow(non_upper_case_globals)]
                    match tag {
                        ___ZEROCOPY_TAG_UnitLike => true,
                        ___ZEROCOPY_TAG_StructLike => {
                            let variant = unsafe {
                                variants.cast_unsized(|p: *mut ___ZerocopyVariants<'a, N, X, Y>| {
                                    p as *mut ___ZerocopyVariantStruct_StructLike<'a, N, X, Y>
                                })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            < ___ZerocopyVariantStruct_StructLike < 'a , N , X , Y > as :: zerocopy :: TryFromBytes > :: is_bit_valid (
                                variant)
                        },
                        ___ZEROCOPY_TAG_TupleLike => {
                            let variant = unsafe {
                                variants.cast_unsized(|p: *mut ___ZerocopyVariants<'a, N, X, Y>| {
                                    p as *mut ___ZerocopyVariantStruct_TupleLike<'a, N, X, Y>
                                })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            < ___ZerocopyVariantStruct_TupleLike < 'a , N , X , Y > as :: zerocopy :: TryFromBytes > :: is_bit_valid (
                                variant)
                        },
                        _ => false,
                    }
                }
            }
        } no_build
    }

    test_derive! {
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
                fn is_bit_valid<A>(
                    mut candidate: ::zerocopy::Maybe<'_, Self, A>,
                ) -> ::zerocopy::util::macro_util::core_reexport::primitive::bool
                where
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>,
                {
                    use ::zerocopy::util::macro_util::core_reexport;
                    #[repr(u32)]
                    #[allow(dead_code)]
                    enum ___ZerocopyTag {
                        UnitLike,
                        StructLike,
                        TupleLike,
                    }
                    type ___ZerocopyTagPrimitive = ::zerocopy::util::macro_util::SizeToTag<
                        { core_reexport::mem::size_of::<___ZerocopyTag>() },
                    >;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_UnitLike: ___ZerocopyTagPrimitive =
                        ___ZerocopyTag::UnitLike as ___ZerocopyTagPrimitive;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_StructLike: ___ZerocopyTagPrimitive =
                        ___ZerocopyTag::StructLike as ___ZerocopyTagPrimitive;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_TupleLike: ___ZerocopyTagPrimitive =
                        ___ZerocopyTag::TupleLike as ___ZerocopyTagPrimitive;
                    type ___ZerocopyOuterTag = ();
                    type ___ZerocopyInnerTag = ___ZerocopyTag;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(:: zerocopy_derive :: TryFromBytes)]
                    struct ___ZerocopyVariantStruct_StructLike<'a: 'static, const N: usize, X, Y: Deref>(
                        core_reexport::mem::MaybeUninit<___ZerocopyInnerTag>,
                        u8,
                        X,
                        X::Target,
                        Y::Target,
                        [(X, Y); N],
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y> >,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>,;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(:: zerocopy_derive :: TryFromBytes)]
                    struct ___ZerocopyVariantStruct_TupleLike<'a: 'static, const N: usize, X, Y: Deref>(
                        core_reexport::mem::MaybeUninit<___ZerocopyInnerTag>,
                        bool,
                        Y,
                        PhantomData<&'a [(X, Y); N]>,
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y> >,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>,;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    union ___ZerocopyVariants<'a: 'static, const N: usize, X, Y: Deref> {
                        __field_StructLike:
                            core_reexport::mem::ManuallyDrop<___ZerocopyVariantStruct_StructLike<'a, N, X, Y> >,
                        __field_TupleLike:
                            core_reexport::mem::ManuallyDrop<___ZerocopyVariantStruct_TupleLike<'a, N, X, Y> >,
                        __nonempty: (),
                    }
                    #[repr(C)]
                    struct ___ZerocopyRawEnum<'a: 'static, const N: usize, X, Y: Deref> {
                        tag: ___ZerocopyOuterTag,
                        variants: ___ZerocopyVariants<'a, N, X, Y>,
                    }
                    let tag = {
                        let tag_ptr = unsafe {
                            candidate.reborrow().cast_unsized(|p: *mut Self| { p as *mut ___ZerocopyTagPrimitive })
                        };
                        let tag_ptr = unsafe { tag_ptr.assume_initialized() };
                        tag_ptr.bikeshed_recall_valid().read_unaligned()
                    };
                    let raw_enum = unsafe {
                        candidate.cast_unsized(|p: *mut Self| { p as *mut ___ZerocopyRawEnum<'a, N, X, Y> })
                    };
                    let raw_enum = unsafe { raw_enum.assume_initialized() };
                    let variants = unsafe {
                        raw_enum.project(|p: *mut ___ZerocopyRawEnum<'a, N, X, Y>| {
                            core_reexport::ptr::addr_of_mut!((*p).variants)
                        })
                    };
                    #[allow(non_upper_case_globals)]
                    match tag {
                        ___ZEROCOPY_TAG_UnitLike => true,
                        ___ZEROCOPY_TAG_StructLike => {
                            let variant = unsafe {
                                variants.cast_unsized(|p: *mut ___ZerocopyVariants<'a, N, X, Y>| {
                                    p as *mut ___ZerocopyVariantStruct_StructLike<'a, N, X, Y>
                                })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            < ___ZerocopyVariantStruct_StructLike < 'a , N , X , Y > as :: zerocopy :: TryFromBytes > :: is_bit_valid (
                                variant)
                        },
                        ___ZEROCOPY_TAG_TupleLike => {
                            let variant = unsafe {
                                variants.cast_unsized(|p: *mut ___ZerocopyVariants<'a, N, X, Y>| {
                                    p as *mut ___ZerocopyVariantStruct_TupleLike<'a, N, X, Y>
                                })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            < ___ZerocopyVariantStruct_TupleLike < 'a , N , X , Y > as :: zerocopy :: TryFromBytes > :: is_bit_valid (
                                variant)
                        },
                        _ => false,
                    }
                }
            }
        } no_build
    }

    test_derive! {
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
                fn is_bit_valid<A>(
                    mut candidate: ::zerocopy::Maybe<'_, Self, A>,
                ) -> ::zerocopy::util::macro_util::core_reexport::primitive::bool
                where
                    A: ::zerocopy::pointer::invariant::Aliasing
                        + ::zerocopy::pointer::invariant::AtLeast<::zerocopy::pointer::invariant::Shared>,
                {
                    use ::zerocopy::util::macro_util::core_reexport;
                    #[repr(C)]
                    #[allow(dead_code)]
                    enum ___ZerocopyTag {
                        UnitLike,
                        StructLike,
                        TupleLike,
                    }
                    type ___ZerocopyTagPrimitive = ::zerocopy::util::macro_util::SizeToTag<
                        { core_reexport::mem::size_of::<___ZerocopyTag>() },
                    >;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_UnitLike: ___ZerocopyTagPrimitive =
                        ___ZerocopyTag::UnitLike as ___ZerocopyTagPrimitive;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_StructLike: ___ZerocopyTagPrimitive =
                        ___ZerocopyTag::StructLike as ___ZerocopyTagPrimitive;
                    #[allow(non_upper_case_globals)]
                    const ___ZEROCOPY_TAG_TupleLike: ___ZerocopyTagPrimitive =
                        ___ZerocopyTag::TupleLike as ___ZerocopyTagPrimitive;
                    type ___ZerocopyOuterTag = ___ZerocopyTag;
                    type ___ZerocopyInnerTag = ();
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(:: zerocopy_derive :: TryFromBytes)]
                    struct ___ZerocopyVariantStruct_StructLike<'a: 'static, const N: usize, X, Y: Deref>(
                        core_reexport::mem::MaybeUninit<___ZerocopyInnerTag>,
                        u8,
                        X,
                        X::Target,
                        Y::Target,
                        [(X, Y); N],
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y> >,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>,;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    #[derive(:: zerocopy_derive :: TryFromBytes)]
                    struct ___ZerocopyVariantStruct_TupleLike<'a: 'static, const N: usize, X, Y: Deref>(
                        core_reexport::mem::MaybeUninit<___ZerocopyInnerTag>,
                        bool,
                        Y,
                        PhantomData<&'a [(X, Y); N]>,
                        core_reexport::marker::PhantomData<ComplexWithGenerics<'a, N, X, Y> >,
                    )
                    where
                        X: Deref<Target = &'a [(X, Y); N]>,;
                    #[repr(C)]
                    #[allow(non_snake_case)]
                    union ___ZerocopyVariants<'a: 'static, const N: usize, X, Y: Deref> {
                        __field_StructLike:
                            core_reexport::mem::ManuallyDrop<___ZerocopyVariantStruct_StructLike<'a, N, X, Y> >,
                        __field_TupleLike:
                            core_reexport::mem::ManuallyDrop<___ZerocopyVariantStruct_TupleLike<'a, N, X, Y> >,
                        __nonempty: (),
                    }
                    #[repr(C)]
                    struct ___ZerocopyRawEnum<'a: 'static, const N: usize, X, Y: Deref> {
                        tag: ___ZerocopyOuterTag,
                        variants: ___ZerocopyVariants<'a, N, X, Y>,
                    }
                    let tag = {
                        let tag_ptr = unsafe {
                            candidate.reborrow().cast_unsized(|p: *mut Self| { p as *mut ___ZerocopyTagPrimitive })
                        };
                        let tag_ptr = unsafe { tag_ptr.assume_initialized() };
                        tag_ptr.bikeshed_recall_valid().read_unaligned()
                    };
                    let raw_enum = unsafe {
                        candidate.cast_unsized(|p: *mut Self| { p as *mut ___ZerocopyRawEnum<'a, N, X, Y> })
                    };
                    let raw_enum = unsafe { raw_enum.assume_initialized() };
                    let variants = unsafe {
                        raw_enum.project(|p: *mut ___ZerocopyRawEnum<'a, N, X, Y>| {
                            core_reexport::ptr::addr_of_mut!((*p).variants)
                        })
                    };
                    #[allow(non_upper_case_globals)]
                    match tag {
                        ___ZEROCOPY_TAG_UnitLike => true,
                        ___ZEROCOPY_TAG_StructLike => {
                            let variant = unsafe {
                                variants.cast_unsized(|p: *mut ___ZerocopyVariants<'a, N, X, Y>| {
                                    p as *mut ___ZerocopyVariantStruct_StructLike<'a, N, X, Y>
                                })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            < ___ZerocopyVariantStruct_StructLike < 'a , N , X , Y > as :: zerocopy :: TryFromBytes > :: is_bit_valid (
                                variant)
                        },
                        ___ZEROCOPY_TAG_TupleLike => {
                            let variant = unsafe {
                                variants.cast_unsized(|p: *mut ___ZerocopyVariants<'a, N, X, Y>| {
                                    p as *mut ___ZerocopyVariantStruct_TupleLike<'a, N, X, Y>
                                })
                            };
                            let variant = unsafe { variant.assume_initialized() };
                            < ___ZerocopyVariantStruct_TupleLike < 'a , N , X , Y > as :: zerocopy :: TryFromBytes > :: is_bit_valid (
                                variant)
                        },
                        _ => false,
                    }
                }
            }
        } no_build
    }
}
