// Copyright 2025 The Fuchsia Authors
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
        // SAFETY: TODO
        unsafe impl HasAtomic for $t
        where
            Self: $crate::IntoBytes,
        {
            type Atomic = <() as AtomicSelector<{ core::mem::size_of::<$t>() }>>::AtomicType;

            #[inline(always)]
            unsafe fn from_atomic(_atomic: <Self::Atomic as AtomicOps>::Value) -> Self {
                todo!()
            }

            #[inline(always)]
            fn into_atomic(_slf: Self) -> <Self::Atomic as AtomicOps>::Value {
                todo!()
            }
        }
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

// #[cfg(feature = "std")]
// impl<T: IntoBytes> Atomic<T> {
//     /// Creates a new `Atomic<T>`.
//     pub const fn new(v: T) -> Self {
//         Self(UnsafeCell::new(v))
//     }

//     /// Loads a value from the atomic integer.
//     ///
//     /// `load` takes an `Ordering` argument which describes the memory ordering
//     /// of this operation. Possible values are `SeqCst`, `Acquire` and `Relaxed`.
//     ///
//     /// # Panics
//     ///
//     /// Panics if `order` is `Release` or `AcqRel`.
//     pub fn load(&self, order: Ordering) -> T {
//         // SAFETY: We verify at compile time that T has a compatible size and alignment.
//         // The pointer cast is valid because Atomic<T> is repr(transparent) over UnsafeCell<T>,
//         // and we cast to the corresponding AtomicU* type which is also repr(transparent) over UnsafeCell<u*>.
//         match size_of::<T>() {
//             1 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU8>());
//                 let ptr = Ptr::from_ref(self);
//                 // SAFETY: We checked size and alignment.
//                 // We use a raw cast here via `cast` machinery if possible, but for now we manually cast because
//                 // we don't have easy access to `AtomicU8` named casts without `define_cast!`.
//                 // However, user asked to use Ptr APIs.
//                 // We can use `ptr.cast_unchecked` if we have a Cast impl.
//                 // Let's rely on standard pointer casting for the implementation details to avoid defined_cast boilerplate export issues?
//                 // Actually, `Ptr::from_ref` gives us a Ptr.
//                 // We can just use `as_ptr()` validation.
//                 // But let's try to stick to Ptr as much as reasonable.
//                 // Since this is inside `zerocopy`, we can use `ptr.as_inner().as_ptr().cast::<AtomicU8>()`.
//                 // But `as_inner` is crate-private. We are in `zerocopy` crate.
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU8>();
//                 // SAFETY: Ptr guarantees valid pointer. Size matches.
//                 let val = unsafe { (*raw).load(order) };
//                 unsafe { mem::transmute_copy(&val) }
//             }

// #[cfg(feature = "std")]
// impl<T: IntoBytes> Atomic<T> {
//     /// Creates a new `Atomic<T>`.
//     pub const fn new(v: T) -> Self {
//         Self(UnsafeCell::new(v))
//     }

//     /// Loads a value from the atomic integer.
//     ///
//     /// `load` takes an `Ordering` argument which describes the memory ordering
//     /// of this operation. Possible values are `SeqCst`, `Acquire` and `Relaxed`.
//     ///
//     /// # Panics
//     ///
//     /// Panics if `order` is `Release` or `AcqRel`.
//     pub fn load(&self, order: Ordering) -> T {
//         // SAFETY: We verify at compile time that T has a compatible size and alignment.
//         // The pointer cast is valid because Atomic<T> is repr(transparent) over UnsafeCell<T>,
//         // and we cast to the corresponding AtomicU* type which is also repr(transparent) over UnsafeCell<u*>.
//         match size_of::<T>() {
//             1 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU8>());
//                 let ptr = Ptr::from_ref(self);
//                 // SAFETY: We checked size and alignment.
//                 // We use a raw cast here via `cast` machinery if possible, but for now we manually cast because
//                 // we don't have easy access to `AtomicU8` named casts without `define_cast!`.
//                 // However, user asked to use Ptr APIs.
//                 // We can use `ptr.cast_unchecked` if we have a Cast impl.
//                 // Let's rely on standard pointer casting for the implementation details to avoid defined_cast boilerplate export issues?
//                 // Actually, `Ptr::from_ref` gives us a Ptr.
//                 // We can just use `as_ptr()` validation.
//                 // But let's try to stick to Ptr as much as reasonable.
//                 // Since this is inside `zerocopy`, we can use `ptr.as_inner().as_ptr().cast::<AtomicU8>()`.
//                 // But `as_inner` is crate-private. We are in `zerocopy` crate.
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU8>();
//                 // SAFETY: Ptr guarantees valid pointer. Size matches.
//                 let val = unsafe { (*raw).load(order) };
//                 unsafe { mem::transmute_copy(&val) }
//             }
//             2 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU16>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU16>();
//                 let val = unsafe { (*raw).load(order) };
//                 unsafe { mem::transmute_copy(&val) }
//             }
//             4 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU32>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU32>();
//                 let val = unsafe { (*raw).load(order) };
//                 unsafe { mem::transmute_copy(&val) }
//             }
//             8 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU64>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU64>();
//                 let val = unsafe { (*raw).load(order) };
//                 unsafe { mem::transmute_copy(&val) }
//             }
//             _ => {
//                 if size_of::<T>() == size_of::<usize>() {
//                     static_assert!(T => align_of::<T>() >= align_of::<AtomicUsize>());
//                     let ptr = Ptr::from_ref(self);
//                     let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicUsize>();
//                     let val = unsafe { (*raw).load(order) };
//                     unsafe { mem::transmute_copy(&val) }
//                 } else {
//                     // This branch should be unreachable at compile time if we could enforce it,
//                     // but `size_of` is const, so `static_assert!` on the outer level might be better.
//                     // But we can't static assert "one of 1, 2, 4, 8" easily without recursion.
//                     // We'll just panic at runtime (and hopefully compile time if const eval works well)
//                     // or use a static assert failure.
//                     panic!("Unsupported size for Atomic<T>");
//                 }
//             }
//         }
//     }

//     /// Stores a value into the atomic integer.
//     pub fn store(&self, val: T, order: Ordering) {
//         match size_of::<T>() {
//             1 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU8>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU8>();
//                 let val_u8: u8 = unsafe { mem::transmute_copy(&val) };
//                 unsafe { (*raw).store(val_u8, order) };
//             }
//             2 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU16>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU16>();
//                 let val_u16: u16 = unsafe { mem::transmute_copy(&val) };
//                 unsafe { (*raw).store(val_u16, order) };
//             }
//             4 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU32>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU32>();
//                 let val_u32: u32 = unsafe { mem::transmute_copy(&val) };
//                 unsafe { (*raw).store(val_u32, order) };
//             }
//             8 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU64>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU64>();
//                 let val_u64: u64 = unsafe { mem::transmute_copy(&val) };
//                 unsafe { (*raw).store(val_u64, order) };
//             }
//             _ => {
//                 if size_of::<T>() == size_of::<usize>() {
//                     static_assert!(T => align_of::<T>() >= align_of::<AtomicUsize>());
//                     let ptr = Ptr::from_ref(self);
//                     let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicUsize>();
//                     let val_usize: usize = unsafe { mem::transmute_copy(&val) };
//                     unsafe { (*raw).store(val_usize, order) };
//                 } else {
//                     panic!("Unsupported size for Atomic<T>");
//                 }
//             }
//         }
//     }

//     /// Stores a value into the atomic integer, returning the previous value.
//     pub fn swap(&self, val: T, order: Ordering) -> T {
//         match size_of::<T>() {
//             1 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU8>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU8>();
//                 let val_u8: u8 = unsafe { mem::transmute_copy(&val) };
//                 let prev = unsafe { (*raw).swap(val_u8, order) };
//                 unsafe { mem::transmute_copy(&prev) }
//             }
//             2 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU16>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU16>();
//                 let val_u16: u16 = unsafe { mem::transmute_copy(&val) };
//                 let prev = unsafe { (*raw).swap(val_u16, order) };
//                 unsafe { mem::transmute_copy(&prev) }
//             }
//             4 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU32>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU32>();
//                 let val_u32: u32 = unsafe { mem::transmute_copy(&val) };
//                 let prev = unsafe { (*raw).swap(val_u32, order) };
//                 unsafe { mem::transmute_copy(&prev) }
//             }
//             8 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU64>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU64>();
//                 let val_u64: u64 = unsafe { mem::transmute_copy(&val) };
//                 let prev = unsafe { (*raw).swap(val_u64, order) };
//                 unsafe { mem::transmute_copy(&prev) }
//             }
//             _ => {
//                 if size_of::<T>() == size_of::<usize>() {
//                     static_assert!(T => align_of::<T>() >= align_of::<AtomicUsize>());
//                     let ptr = Ptr::from_ref(self);
//                     let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicUsize>();
//                     let val_usize: usize = unsafe { mem::transmute_copy(&val) };
//                     let prev = unsafe { (*raw).swap(val_usize, order) };
//                     unsafe { mem::transmute_copy(&prev) }
//                 } else {
//                     panic!("Unsupported size for Atomic<T>");
//                 }
//             }
//         }
//     }

//     /// Stores a value into the atomic integer if the current value is the same as the `current` value.
//     pub fn compare_exchange(
//         &self,
//         current: T,
//         new: T,
//         success: Ordering,
//         failure: Ordering,
//     ) -> Result<T, T> {
//         match size_of::<T>() {
//             1 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU8>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU8>();
//                 let current_u8: u8 = unsafe { mem::transmute_copy(&current) };
//                 let new_u8: u8 = unsafe { mem::transmute_copy(&new) };
//                 match unsafe { (*raw).compare_exchange(current_u8, new_u8, success, failure) } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             2 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU16>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU16>();
//                 let current_u16: u16 = unsafe { mem::transmute_copy(&current) };
//                 let new_u16: u16 = unsafe { mem::transmute_copy(&new) };
//                 match unsafe { (*raw).compare_exchange(current_u16, new_u16, success, failure) } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             4 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU32>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU32>();
//                 let current_u32: u32 = unsafe { mem::transmute_copy(&current) };
//                 let new_u32: u32 = unsafe { mem::transmute_copy(&new) };
//                 match unsafe { (*raw).compare_exchange(current_u32, new_u32, success, failure) } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             8 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU64>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU64>();
//                 let current_u64: u64 = unsafe { mem::transmute_copy(&current) };
//                 let new_u64: u64 = unsafe { mem::transmute_copy(&new) };
//                 match unsafe { (*raw).compare_exchange(current_u64, new_u64, success, failure) } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             _ => {
//                 if size_of::<T>() == size_of::<usize>() {
//                     static_assert!(T => align_of::<T>() >= align_of::<AtomicUsize>());
//                     let ptr = Ptr::from_ref(self);
//                     let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicUsize>();
//                     let current_usize: usize = unsafe { mem::transmute_copy(&current) };
//                     let new_usize: usize = unsafe { mem::transmute_copy(&new) };
//                     match unsafe {
//                         (*raw).compare_exchange(current_usize, new_usize, success, failure)
//                     } {
//                         Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                         Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                     }
//                 } else {
//                     panic!("Unsupported size for Atomic<T>");
//                 }
//             }
//         }
//     }

//     /// Stores a value into the atomic integer if the current value is the same as the `current` value.
//     pub fn compare_exchange_weak(
//         &self,
//         current: T,
//         new: T,
//         success: Ordering,
//         failure: Ordering,
//     ) -> Result<T, T> {
//         match size_of::<T>() {
//             1 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU8>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU8>();
//                 let current_u8: u8 = unsafe { mem::transmute_copy(&current) };
//                 let new_u8: u8 = unsafe { mem::transmute_copy(&new) };
//                 match unsafe { (*raw).compare_exchange_weak(current_u8, new_u8, success, failure) }
//                 {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             2 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU16>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU16>();
//                 let current_u16: u16 = unsafe { mem::transmute_copy(&current) };
//                 let new_u16: u16 = unsafe { mem::transmute_copy(&new) };
//                 match unsafe {
//                     (*raw).compare_exchange_weak(current_u16, new_u16, success, failure)
//                 } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             4 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU32>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU32>();
//                 let current_u32: u32 = unsafe { mem::transmute_copy(&current) };
//                 let new_u32: u32 = unsafe { mem::transmute_copy(&new) };
//                 match unsafe {
//                     (*raw).compare_exchange_weak(current_u32, new_u32, success, failure)
//                 } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             8 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU64>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU64>();
//                 let current_u64: u64 = unsafe { mem::transmute_copy(&current) };
//                 let new_u64: u64 = unsafe { mem::transmute_copy(&new) };
//                 match unsafe {
//                     (*raw).compare_exchange_weak(current_u64, new_u64, success, failure)
//                 } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             _ => {
//                 if size_of::<T>() == size_of::<usize>() {
//                     static_assert!(T => align_of::<T>() >= align_of::<AtomicUsize>());
//                     let ptr = Ptr::from_ref(self);
//                     let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicUsize>();
//                     let current_usize: usize = unsafe { mem::transmute_copy(&current) };
//                     let new_usize: usize = unsafe { mem::transmute_copy(&new) };
//                     match unsafe {
//                         (*raw).compare_exchange_weak(current_usize, new_usize, success, failure)
//                     } {
//                         Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                         Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                     }
//                 } else {
//                     panic!("Unsupported size for Atomic<T>");
//                 }
//             }
//         }
//     }

//     /// Fetches the value, and applies a function to it that may modify it.
//     pub fn fetch_update<F>(
//         &self,
//         set_order: Ordering,
//         fetch_order: Ordering,
//         mut f: F,
//     ) -> Result<T, T>
//     where
//         F: FnMut(T) -> Option<T>,
//     {
//         match size_of::<T>() {
//             1 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU8>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU8>();
//                 // We need to wrap the closure to map U -> U
//                 let mut mapping = |v: u8| -> Option<u8> {
//                     let val: T = unsafe { mem::transmute_copy(&v) };
//                     f(val).map(|new_val| unsafe { mem::transmute_copy(&new_val) })
//                 };
//                 match unsafe { (*raw).fetch_update(set_order, fetch_order, mapping) } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             2 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU16>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU16>();
//                 let mut mapping = |v: u16| -> Option<u16> {
//                     let val: T = unsafe { mem::transmute_copy(&v) };
//                     f(val).map(|new_val| unsafe { mem::transmute_copy(&new_val) })
//                 };
//                 match unsafe { (*raw).fetch_update(set_order, fetch_order, mapping) } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             4 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU32>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU32>();
//                 let mut mapping = |v: u32| -> Option<u32> {
//                     let val: T = unsafe { mem::transmute_copy(&v) };
//                     f(val).map(|new_val| unsafe { mem::transmute_copy(&new_val) })
//                 };
//                 match unsafe { (*raw).fetch_update(set_order, fetch_order, mapping) } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             8 => {
//                 static_assert!(T => align_of::<T>() >= align_of::<AtomicU64>());
//                 let ptr = Ptr::from_ref(self);
//                 let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicU64>();
//                 let mut mapping = |v: u64| -> Option<u64> {
//                     let val: T = unsafe { mem::transmute_copy(&v) };
//                     f(val).map(|new_val| unsafe { mem::transmute_copy(&new_val) })
//                 };
//                 match unsafe { (*raw).fetch_update(set_order, fetch_order, mapping) } {
//                     Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                     Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                 }
//             }
//             _ => {
//                 if size_of::<T>() == size_of::<usize>() {
//                     static_assert!(T => align_of::<T>() >= align_of::<AtomicUsize>());
//                     let ptr = Ptr::from_ref(self);
//                     let raw = ptr.as_inner().as_non_null().as_ptr().cast::<AtomicUsize>();
//                     let mut mapping = |v: usize| -> Option<usize> {
//                         let val: T = unsafe { mem::transmute_copy(&v) };
//                         f(val).map(|new_val| unsafe { mem::transmute_copy(&new_val) })
//                     };
//                     match unsafe { (*raw).fetch_update(set_order, fetch_order, mapping) } {
//                         Ok(v) => Ok(unsafe { mem::transmute_copy(&v) }),
//                         Err(v) => Err(unsafe { mem::transmute_copy(&v) }),
//                     }
//                 } else {
//                     panic!("Unsupported size for Atomic<T>");
//                 }
//             }
//         }
//     }
// }

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
