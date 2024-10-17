// Copyright 2024 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Support for unsafe fields.
//!
//! This crate provides the [`Unsafe`] wrapper type. An `Unsafe<T>` is intended
//! to be used to for struct, enum, or union fields which carry safety
//! invariants. All accessors are `unsafe`, which requires any use of an
//! `Unsafe` field to be inside an `unsafe` block.
//!
//! # Examples
//!
//! ```
//! use unsafe_fields::Unsafe;
//!
//! /// A `usize` which is guaranteed to be even.
//! pub struct EvenUsize {
//!     // INVARIANT: `n` is even.
//!     n: Unsafe<usize>,
//! }
//!
//! impl EvenUsize {
//!     /// Constructs a new `EvenUsize`.
//!     ///
//!     /// Returns `None` if `n` is odd.
//!     pub fn new(n: usize) -> Option<EvenUsize> {
//!         if n % 2 != 0 {
//!             return None;
//!         }
//!         // SAFETY: We just confirmed that `n` is even.
//!         let n = unsafe { Unsafe::new(n) };
//!         Some(EvenUsize { n })
//!     }
//! }
//! ```

/// A field with safety invariants.
///
/// An `Unsafe<T>` is intended to be used to for struct, enum, or union fields
/// which carry safety invariants. All accessors are `unsafe`, which requires
/// any use of an `Unsafe` field to be inside an `unsafe` block.
///
/// # Examples
///
/// ```
/// use unsafe_fields::Unsafe;
///
/// /// A `usize` which is guaranteed to be even.
/// pub struct EvenUsize {
///     // INVARIANT: `n` is even.
///     n: Unsafe<usize>,
/// }
///
/// impl EvenUsize {
///     /// Constructs a new `EvenUsize`.
///     ///
///     /// Returns `None` if `n` is odd.
///     pub fn new(n: usize) -> Option<EvenUsize> {
///         if n % 2 != 0 {
///             return None;
///         }
///         // SAFETY: We just confirmed that `n` is even.
///         let n = unsafe { Unsafe::new(n) };
///         Some(EvenUsize { n })
///     }
/// }
/// ```
#[derive(Copy, Clone)] // TODO: We need Copy in case user types need to be Copy. Is this sound?
#[repr(transparent)]
pub struct Unsafe<T: ?Sized>(T);

impl<T: ?Sized> Unsafe<T> {
    /// Gets a reference to the inner value.
    ///
    /// # Safety
    ///
    /// The caller is responsible for upholding any safety invariants associated
    /// with this field.
    #[inline(always)]
    pub const unsafe fn as_ref(&self) -> &T {
        &self.0
    }

    /// Gets a mutable reference to the inner value.
    ///
    /// # Safety
    ///
    /// The caller is responsible for upholding any safety invariants associated
    /// with this field.
    #[inline(always)]
    pub unsafe fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T> Unsafe<T> {
    /// Constructs a new `Unsafe<T>`.
    ///
    /// # Safety
    ///
    /// The caller is responsible for upholding any safety invariants associated
    /// with this field.
    #[inline(always)]
    pub const unsafe fn new(t: T) -> Unsafe<T> {
        Unsafe(t)
    }

    /// Extracts the inner `T` from `self`.
    ///
    /// # Safety
    ///
    /// The caller is responsible for upholding any safety invariants associated
    /// with this field.
    #[inline(always)]
    pub const unsafe fn into(self) -> T {
        use core::mem::ManuallyDrop;

        let slf = ManuallyDrop::new(self);

        #[repr(C)]
        union Transmute<T> {
            src: ManuallyDrop<Unsafe<T>>,
            dst: ManuallyDrop<T>,
        }

        // SAFETY: `ManuallyDrop<Unsafe<T>>` has the same size and bit validity
        // as `Unsafe<T>`. [1] `Unsafe<T>` is `#[repr(transparent)]` and has no
        // other fields, and so it has the same size and bit validity as `T`.
        //
        // [1] Per https://doc.rust-lang.org/1.81.0/core/mem/struct.ManuallyDrop.html:
        //
        //   `ManuallyDrop<T>` is guaranteed to have the same layout and bit
        //   validity as `T`
        let dst = unsafe { Transmute { src: slf }.dst };
        ManuallyDrop::into_inner(dst)
    }
}
