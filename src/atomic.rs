// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! TODO

use core::{
    marker::PhantomData,
    sync::atomic::{AtomicU16, AtomicU32, AtomicU64, AtomicU8, Ordering},
};

/// TODO
///
/// # Safety
///
/// TODO
pub unsafe trait HasAtomic {
    #[doc(hidden)]
    type Atomic: Send + Sync + AtomicOps;
    #[doc(hidden)]
    const PADDING: usize;

    /// # Safety
    ///
    /// `atomic` must be bit-valid for `Self`.
    #[doc(hidden)]
    unsafe fn from_atomic(atomic: <Self::Atomic as AtomicOps>::Value) -> Self;
    #[doc(hidden)]
    fn into_atomic(slf: Self) -> <Self::Atomic as AtomicOps>::Value;
}

/// # Safety
///
/// TODO
#[doc(hidden)]
pub unsafe trait AtomicSelector<const N: usize> {
    type AtomicType;
}

/// # Safety
///
/// TODO
#[doc(hidden)]
pub unsafe trait AtomicOps {
    type Value;

    fn new(value: Self::Value) -> Self;
    fn load(&self, ordering: Ordering) -> Self::Value;
    fn store(&self, value: Self::Value, ordering: Ordering);
}

macro_rules! impl_atomic_selector {
    ($atomic:ty [$value:ty]; $($size:expr),+) => {
        // SAFETY: TODO
        unsafe impl AtomicOps for $atomic {
            type Value = $value;

            #[inline(always)]
            fn new(value: Self::Value) -> Self {
                Self::new(value)
            }

            #[inline(always)]
            fn load(&self, ordering: Ordering) -> Self::Value {
                self.load(ordering)
            }

            #[inline(always)]
            fn store(&self, value: Self::Value, ordering: Ordering) {
                self.store(value, ordering)
            }
        }

        $(
            // SAFETY: TODO
            unsafe impl AtomicSelector<$size> for () {
                type AtomicType = $atomic;
            }
        )+
    };
}

impl_atomic_selector!(AtomicU8 [u8]; 1);
impl_atomic_selector!(AtomicU16 [u16]; 2);
impl_atomic_selector!(AtomicU32 [u32]; 3, 4);
impl_atomic_selector!(AtomicU64 [u64]; 5, 6, 7, 8);

/// TODO
#[macro_export]
macro_rules! impl_atomic {
    ($t:ty) => {
        const _: () = {
            #[repr(C, packed)]
            struct __ZerocopyPadded {
                v: [u8; core::mem::size_of::<$t>()],
                _padding: [u8; <$t as $crate::atomic::HasAtomic>::PADDING],
            }

            // SAFETY: By the `IntoBytes` bounds, all fields are `IntoBytes`.
            // `__ZerocopyPadded` is `#[repr(packed)]`, and so it has no padding
            // bytes outside of its fields.
            unsafe impl $crate::IntoBytes for __ZerocopyPadded
            where
                $t: $crate::IntoBytes,
                [u8; <$t as $crate::atomic::HasAtomic>::PADDING]: $crate::IntoBytes,
            {
                fn only_derive_is_allowed_to_implement_this_trait()
                where
                    Self: Sized,
                {
                }
            }

            // SAFETY: By the `FromBytes` bounds, all fields are `FromBytes`, so
            // `is_bit_valid` unconditionally returning `true` is sound.
            unsafe impl $crate::TryFromBytes for __ZerocopyPadded
            where
                $t: $crate::FromBytes,
                [u8; <$t as $crate::atomic::HasAtomic>::PADDING]: $crate::FromBytes,
            {
                fn only_derive_is_allowed_to_implement_this_trait()
                where
                    Self: Sized,
                {
                }

                fn is_bit_valid(_c: $crate::pointer::Maybe<'_, Self>) -> bool {
                    true
                }
            }

            // SAFETY: By the `FromBytes` bounds, all fields are `FromBytes:
            // FromZeros`.
            unsafe impl $crate::FromZeros for __ZerocopyPadded
            where
                $t: $crate::FromBytes,
                [u8; <$t as $crate::atomic::HasAtomic>::PADDING]: $crate::FromBytes,
            {
                fn only_derive_is_allowed_to_implement_this_trait()
                where
                    Self: Sized,
                {
                }
            }

            // SAFETY: By the `FromBytes` bounds, all fields are `FromBytes`.
            unsafe impl $crate::FromBytes for __ZerocopyPadded
            where
                $t: $crate::FromBytes,
                [u8; <$t as $crate::atomic::HasAtomic>::PADDING]: $crate::FromBytes,
            {
                fn only_derive_is_allowed_to_implement_this_trait()
                where
                    Self: Sized,
                {
                }
            }

            // SAFETY: TODO
            unsafe impl $crate::atomic::HasAtomic for $t
            where
                Self: $crate::IntoBytes,
            {
                type Atomic = <() as AtomicSelector<{ core::mem::size_of::<$t>() }>>::AtomicType;

                const PADDING: usize =
                    core::mem::size_of::<Self::Atomic>() - core::mem::size_of::<Self>();

                #[inline(always)]
                unsafe fn from_atomic(atomic: <Self::Atomic as AtomicOps>::Value) -> Self {
                    let value: __ZerocopyPadded = $crate::transmute!(atomic);

                    // SAFETY: The caller promises that the leading bytes of
                    // `atomic` are bit-valid for `Self`.
                    #[allow(unnecessary_transmutes)]
                    unsafe {
                        $crate::util::macro_util::core_reexport::mem::transmute(value.v)
                    }
                }

                #[inline(always)]
                fn into_atomic(slf: Self) -> <Self::Atomic as AtomicOps>::Value {
                    $crate::transmute!(__ZerocopyPadded {
                        v: $crate::transmute!(slf),
                        _padding: [0; <$t as $crate::atomic::HasAtomic>::PADDING]
                    })
                }
            }
        };
    };
}

impl_atomic!(u8);

/// TODO
#[repr(transparent)]
#[allow(missing_copy_implementations, missing_debug_implementations)]
pub struct Atomic<T: HasAtomic> {
    // INVARIANT: The first `size_of::<T>()` bytes of `atomic` have the same
    // validity as `T`, and logically own a `T`.
    atomic: T::Atomic,
    _marker: PhantomData<T>,
}

// TODO: Impl traits (Copy, Clone, Debug, Send, Sync, etc).

impl<T: HasAtomic> Atomic<T> {
    /// TODO
    #[inline(always)]
    #[must_use]
    pub fn new(v: T) -> Self {
        let atomic = T::Atomic::new(T::into_atomic(v));
        Self { atomic, _marker: PhantomData }
    }

    /// TODO
    #[inline]
    #[must_use]
    pub fn load(&self, ordering: Ordering) -> T {
        let v = self.atomic.load(ordering);
        // SAFETY: TODO
        unsafe { T::from_atomic(v) }
    }

    /// TODO
    #[inline]
    pub fn store(&self, v: T, ordering: Ordering) {
        let atomic = T::into_atomic(v);
        self.atomic.store(atomic, ordering)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Immutable, IntoBytes, KnownLayout};

    #[derive(IntoBytes, KnownLayout, Immutable, Clone, Copy, Debug, PartialEq)]
    #[repr(C)]
    struct MyStruct {
        a: u32,
    }

    #[derive(IntoBytes, KnownLayout, Immutable, Clone, Copy, Debug, PartialEq)]
    #[repr(u8)]
    enum MyEnum {
        A = 0,
        B = 1,
    }

    #[test]
    fn test_atomic_u32() {
        let a = Atomic::new(10u32);
        assert_eq!(a.load(Ordering::SeqCst), 10);
        a.store(20, Ordering::SeqCst);
        assert_eq!(a.load(Ordering::SeqCst), 20);
        assert_eq!(a.swap(30, Ordering::SeqCst), 20);
        assert_eq!(a.load(Ordering::SeqCst), 30);
    }

    #[test]
    fn test_atomic_struct() {
        let s1 = MyStruct { a: 10 };
        let s2 = MyStruct { a: 20 };
        let a = Atomic::new(s1);
        assert_eq!(a.load(Ordering::SeqCst), s1);
        a.store(s2, Ordering::SeqCst);
        assert_eq!(a.load(Ordering::SeqCst), s2);
    }

    #[test]
    fn test_atomic_enum() {
        let a = Atomic::new(MyEnum::A);
        assert_eq!(a.load(Ordering::SeqCst), MyEnum::A);
        a.store(MyEnum::B, Ordering::SeqCst);
        assert_eq!(a.load(Ordering::SeqCst), MyEnum::B);
    }

    #[test]
    fn test_compare_exchange() {
        let a = Atomic::new(10u32);
        let res = a.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
        assert_eq!(res, Ok(10));
        assert_eq!(a.load(Ordering::SeqCst), 20);
        let res = a.compare_exchange(10, 30, Ordering::SeqCst, Ordering::SeqCst);
        assert_eq!(res, Err(20));
        assert_eq!(a.load(Ordering::SeqCst), 20);
    }

    #[test]
    fn test_fetch_update() {
        let a = Atomic::new(10u32);
        let res = a.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |v| Some(v + 1));
        assert_eq!(res, Ok(10));
        assert_eq!(a.load(Ordering::SeqCst), 11);
    }
}
