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
    mem::{ManuallyDrop, MaybeUninit},
    sync::atomic::{AtomicU16, AtomicU32, AtomicU64, AtomicU8, Ordering},
};

use crate::{FromBytes, IntoBytes};

enum SupportedSize {
    B0 = 0,
    B1 = 1,
    B2 = 2,
    B3 = 3,
    B4 = 4,
    B5 = 5,
    B6 = 6,
    B7 = 7,
    B8 = 8,
}

impl SupportedSize {
    const fn try_for_type<T>() -> Option<Self> {
        match core::mem::size_of::<T>() {
            0 => Some(Self::B0),
            1 => Some(Self::B1),
            2 => Some(Self::B2),
            3 => Some(Self::B3),
            4 => Some(Self::B4),
            5 => Some(Self::B5),
            6 => Some(Self::B6),
            7 => Some(Self::B7),
            8 => Some(Self::B8),
            _ => None,
        }
    }
}

const fn selector_for_type<T>() -> usize {
    #[allow(clippy::as_conversions)]
    match SupportedSize::try_for_type::<T>() {
        Some(size) => size as usize,
        None => 0,
    }
}

fn into_atomic<T: IntoBytes + Kl>(t: T) -> <T::Atomic as AtomicOps>::Value {
    static_assert!(T => SupportedSize::try_for_type::<T>().is_some(), "type is too large for atomic operations");

    #[repr(C)]
    union Transmute<T: Kl> {
        t: ManuallyDrop<T>,
        prim: <T::Atomic as AtomicOps>::Value,
    }

    let mut u = Transmute { prim: Default::default() };
    u.t = ManuallyDrop::new(t);
    // SAFETY: TODO
    unsafe { u.prim }
}

fn from_atomic<T: Kl>(v: <T::Atomic as AtomicOps>::Value) -> MaybeUninit<T> {
    static_assert!(T => SupportedSize::try_for_type::<T>().is_some(), "type is too large for atomic operations");

    #[repr(C)]
    union Transmute<T: Kl> {
        t: ManuallyDrop<MaybeUninit<T>>,
        prim: <T::Atomic as AtomicOps>::Value,
    }

    let u = Transmute { prim: v };
    // SAFETY: TODO
    ManuallyDrop::into_inner(unsafe { u.t })
}

trait Kl {
    type Atomic: Send + Sync + AtomicOps;
}

/// # Safety
///
/// TODO
#[doc(hidden)]
pub unsafe trait AtomicSelector<const N: usize> {
    type AtomicType;
    const PADDING: usize;
}

/// # Safety
///
/// TODO
#[doc(hidden)]
pub unsafe trait AtomicOps {
    type Value: Copy + Default;

    fn new(value: Self::Value) -> Self;
    fn load(&self, ordering: Ordering) -> Self::Value;
    fn store(&self, value: Self::Value, ordering: Ordering);
}

unsafe impl AtomicSelector<0> for () {
    type AtomicType = ();
    const PADDING: usize = 0;
}

unsafe impl AtomicOps for () {
    type Value = ();

    fn new(_: ()) -> Self {}
    fn load(&self, _: Ordering) -> Self::Value {}
    fn store(&self, _: Self::Value, _: Ordering) {}
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
                const PADDING: usize = core::mem::size_of::<$atomic>() - $size;
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
            impl Kl for $t {
                type Atomic = <() as AtomicSelector<{ selector_for_type::<Self>() }>>::AtomicType;
            }
        };
    };
    ($($t:ty),+ $(,)?) => {
        $($crate::impl_atomic!($t);)+
    };
}

impl_atomic!(u8, u16, u32, u64);
impl_atomic!([u8; 1], [u8; 2], [u8; 3], [u8; 4], [u8; 5], [u8; 6], [u8; 7], [u8; 8], [u8; 64]);

/// TODO
#[repr(transparent)]
#[allow(missing_copy_implementations, missing_debug_implementations)]
pub struct Atomic<T: Kl> {
    // INVARIANT: The first `size_of::<T>()` bytes of `atomic` have the same
    // validity as `T`, and logically own a `T`.
    atomic: T::Atomic,
    _marker: PhantomData<T>,
}

// TODO: Impl traits (Copy, Clone, Debug, Send, Sync, etc).

impl<T: IntoBytes + Kl> Atomic<T> {
    /// TODO
    #[inline(always)]
    #[must_use]
    pub fn new(v: T) -> Self {
        let prim = into_atomic(v);
        let atomic = T::Atomic::new(prim);
        Self { atomic, _marker: PhantomData }
    }

    /// TODO
    #[inline]
    pub fn store(&self, v: T, ordering: Ordering) {
        let prim = into_atomic(v);
        self.atomic.store(prim, ordering);
    }
}

impl<T: Kl> Atomic<T> {
    /// TODO
    #[inline]
    #[must_use]
    pub fn load(&self, ordering: Ordering) -> T {
        let v = self.atomic.load(ordering);
        let mu = from_atomic(v);
        // SAFETY: TODO
        unsafe { mu.assume_init() }
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

#[allow(dead_code)]
#[doc(hidden)]
pub mod doctests {
    /// ```compile_fail,E0080
    /// use core::sync::atomic::Ordering;
    /// let a = zerocopy::atomic::Atomic::new([0u8; 64]);
    /// a.load(Ordering::SeqCst);
    /// ```
    enum OversizedTypesPme {}
}
