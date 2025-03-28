// Copyright 2025 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use super::*;
#[cfg(doc)]
use invariant::Exclusive;

/// Types that can be split in two.
///
/// # Implementation
///
/// **Do not implement this trait yourself!** Instead, use
/// [`#[derive(SplitAt)]`][derive]; e.g.:
///
/// ```
/// # use zerocopy_derive::{SplitAt, KnownLayout};
/// #[derive(SplitAt, KnownLayout)]
/// #[repr(C)]
/// struct MyStruct<T: ?Sized> {
/// # /*
///     ...,
/// # */
///     // `SplitAt` types must have at least one field.
///     field: T,
/// }
/// ```
///
/// This derive performs a sophisticated, compile-time safety analysis to
/// determine whether a type is `SplitAt`.
///
/// # Safety
///
/// This trait does not convey any safety guarantees to code outside this crate.
///
/// You must not rely on the `#[doc(hidden)]` internals of `SplitAt`. Future
/// releases of zerocopy may make backwards-breaking changes to these items,
/// including changes that only affect soundness, which may cause code which
/// uses those items to silently become unsound.
///
#[cfg_attr(feature = "derive", doc = "[derive]: zerocopy_derive::SplitAt")]
#[cfg_attr(
    not(feature = "derive"),
    doc = concat!("[derive]: https://docs.rs/zerocopy/", env!("CARGO_PKG_VERSION"), "/zerocopy/derive.SplitAt.html"),
)]
#[cfg_attr(
    zerocopy_diagnostic_on_unimplemented_1_78_0,
    diagnostic::on_unimplemented(note = "Consider adding `#[derive(SplitAt)]` to `{Self}`")
)]
// # Safety
//
// The trailing slice is well-aligned for its element type.
pub unsafe trait SplitAt: KnownLayout<PointerMetadata = usize> {
    /// The element type of the trailing slice.
    type Elem;

    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;

    /// Unsafely splits `self` in two.
    ///
    /// # Safety
    ///
    /// The caller promises that `l_len` is not greater than the length of
    /// `self`'s trailing slice.
    #[inline]
    #[must_use]
    unsafe fn split_at_unchecked(&self, l_len: usize) -> (&Self, &[Self::Elem])
    where
        Self: Immutable,
    {
        // SAFETY: `&self` is an instance of `&Self` for which the caller has
        // promised that `l_len` is not greater than the length of `self`'s
        // trailing slice.
        let l_len = unsafe { MetadataOf::new_unchecked(l_len) };
        let ptr = Ptr::from_ref(self);
        // SAFETY:
        // 0. The caller promises that `l_len` is not greater than the length of
        //    `self`'s trailing slice.
        // 1. `ptr`'s aliasing is `Shared` and does not permit interior mutation
        //    because `Self: Immutable`.
        let (left, right) = unsafe { ptr_split_at_unchecked(ptr, l_len) };
        (left.as_ref(), right.as_ref())
    }

    /// Attempts to split `self` in two.
    ///
    /// Returns `None` if `l_len` is greater than the length of `self`'s
    /// trailing slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, Immutable)]
    /// #[repr(C)]
    /// struct Packet {
    ///     length: u8,
    ///     body: [u8],
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let bytes = &[4, 1, 2, 3, 4, 5, 6, 7, 8, 9][..];
    ///
    /// let packet = Packet::ref_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// let (packet, rest) = packet.split_at(packet.length as usize).unwrap();
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4]);
    /// assert_eq!(rest, [5, 6, 7, 8, 9]);
    /// ```
    #[inline]
    #[must_use = "has no side effects"]
    fn split_at(&self, l_len: usize) -> Option<(&Self, &[Self::Elem])>
    where
        Self: Immutable,
    {
        if l_len <= Ptr::from_ref(self).len() {
            // SAFETY: We have checked that `l_len` is not greater than the
            // length of `self`'s trailing slice.
            Some(unsafe { self.split_at_unchecked(l_len) })
        } else {
            None
        }
    }

    /// Unsafely splits `self` in two.
    ///
    /// # Safety
    ///
    /// The caller promises that:
    /// 0. `l_len` is not greater than the length of `self`'s trailing slice.
    /// 1. The trailing padding bytes of the left portion will not overlap the
    ///    right portion. For some dynamically sized types, the padding that
    ///    appears after the trailing slice field [is a dynamic function of the
    ///    trailing slice length](KnownLayout#slice-dst-layout). Thus, for some
    ///    types, this condition is dependent on the value of `l_len`.
    #[inline]
    #[must_use]
    unsafe fn split_at_mut_unchecked(&mut self, l_len: usize) -> (&mut Self, &mut [Self::Elem]) {
        // SAFETY: `&mut self` is an instance of `&mut Self` for which the
        // caller has promised that `l_len` is not greater than the length of
        // `self`'s trailing slice.
        let l_len = unsafe { MetadataOf::new_unchecked(l_len) };
        let ptr = Ptr::from_mut(self);
        // SAFETY:
        // 0. The caller promises that `l_len` is not greater than the length of
        //    `self`'s trailing slice.
        // 1. `ptr`'s aliasing is `Exclusive`; the caller promises that
        //    `l_len.padding_needed_for() == 0`.
        let (left, right) = unsafe { ptr_split_at_unchecked(ptr, l_len) };
        (left.as_mut(), right.as_mut())
    }

    /// Attempts to split `self` in two.
    ///
    /// Returns `None` if `l_len` is greater than the length of `self`'s
    /// trailing slice, or if the given `l_len` would result in [the trailing
    /// padding](KnownLayout#slice-dst-layout) of the left portion overlapping
    /// the right portion.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use zerocopy::{SplitAt, FromBytes};
    /// # use zerocopy_derive::*;
    ///
    /// #[derive(SplitAt, FromBytes, KnownLayout, Immutable, IntoBytes)]
    /// #[repr(C)]
    /// struct Packet<B: ?Sized> {
    ///     length: u8,
    ///     body: B,
    /// }
    ///
    /// // These bytes encode a `Packet`.
    /// let mut bytes = &mut [4, 1, 2, 3, 4, 5, 6, 7, 8, 9][..];
    ///
    /// let packet = Packet::<[u8]>::mut_from_bytes(bytes).unwrap();
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// {
    ///     let (packet, rest) = packet.split_at_mut(packet.length as usize).unwrap();
    ///     assert_eq!(packet.length, 4);
    ///     assert_eq!(packet.body, [1, 2, 3, 4]);
    ///     assert_eq!(rest, [5, 6, 7, 8, 9]);
    ///
    ///     rest.fill(0);
    /// }
    ///
    /// assert_eq!(packet.length, 4);
    /// assert_eq!(packet.body, [1, 2, 3, 4, 0, 0, 0, 0, 0]);
    /// ```
    #[inline]
    fn split_at_mut(&mut self, l_len: usize) -> Option<(&mut Self, &mut [Self::Elem])> {
        match MetadataOf::new_in_bounds(self, l_len) {
            Some(l_len) if l_len.padding_needed_for() == 0 => {
                // SAFETY: We have ensured both that:
                // 0. `l_len <= self.len()` (by post-condition on
                //    `MetadataOf::new_in_bounds`)
                // 1. `l_len.padding_needed_for() == 0` (by guard on match arm)
                Some(unsafe { self.split_at_mut_unchecked(l_len.get()) })
            }
            _ => None,
        }
    }
}

// SAFETY: `[T]`'s trailing slice is `[T]`, which is trivially aligned.
unsafe impl<T> SplitAt for [T] {
    type Elem = T;

    #[inline]
    #[allow(dead_code)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized,
    {
    }
}

/// Splits `T` in two.
///
/// # Safety
///
/// The caller promises that:
/// 0. `l_len.get()` is not greater than the length of `ptr`'s trailing slice.
/// 1. if `I::Aliasing` is [`Exclusive`] or `T` permits interior mutation, then
///    `l_len.padding_needed_for() == 0`.
#[inline(always)]
unsafe fn ptr_split_at_unchecked<'a, T, I, R>(
    ptr: Ptr<'a, T, I>,
    l_len: MetadataOf<T>,
) -> (Ptr<'a, T, I>, Ptr<'a, [T::Elem], I>)
where
    I: invariant::Invariants,
    T: ?Sized + pointer::Read<I::Aliasing, R> + SplitAt,
{
    let inner = ptr.as_inner();

    // SAFETY: The caller promises that `l_len.get()` is not greater than the
    // length of `self`'s trailing slice.
    let (left, right) = unsafe { inner.split_at_unchecked(l_len) };

    // Lemma 0: `left` and `right` conform to the aliasing invariant
    // `I::Aliasing`. Proof: If `I::Aliasing` is `Exclusive` or `T` permits
    // interior mutation, the caller promises that `l_len.padding_needed_for()
    // == 0`. Consequently, by post-condition on `PtrInner::split_at_unchecked`,
    // there is no trailing padding after `left`'s final element that would
    // overlap into `right`. If `I::Aliasing` is shared and `T` forbids interior
    // mutation, then overlap between their referents is permissible.

    // SAFETY:
    // 0. `left` conforms to the aliasing invariant of `I::Aliasing, by Lemma 0.
    // 1. `left` conforms to the alignment invariant of `I::Alignment, because
    //    the referents of `left` and `Self` have the same address and type
    //    (and, thus, alignment requirement).
    // 2. `left` conforms to the validity invariant of `I::Validity`, neither
    //    the type nor bytes of `left`'s referent have been changed.
    let left = unsafe { Ptr::from_inner(left) };

    // SAFETY:
    // 0. `right` conforms to the aliasing invariant of `I::Aliasing, by Lemma
    //    0.
    // 1. `right` conforms to the alignment invariant of `I::Alignment, because
    //    if `ptr` with `I::Alignment = Aligned`, then by invariant on `T:
    //    SplitAt`, the trailing slice of `ptr` (from which `right` is derived)
    //    will also be well-aligned.
    // 2. `right` conforms to the validity invariant of `I::Validity`, because
    //    `right: [T::Elem]` is derived from the trailing slice of `ptr`, which,
    //    by contract on `T: SplitAt::Elem`, has type `[T::Elem]`.
    let right = unsafe { Ptr::from_inner(right) };

    (left, right)
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "derive")]
    #[test]
    fn test_split_at() {
        use crate::{FromBytes, Immutable, IntoBytes, KnownLayout, SplitAt};

        #[derive(FromBytes, KnownLayout, SplitAt, IntoBytes, Immutable)]
        #[repr(C)]
        struct SliceDst<const OFFSET: usize> {
            prefix: [u8; OFFSET],
            trailing: [u8],
        }

        #[allow(clippy::as_conversions)]
        fn test_split_at<const OFFSET: usize, const BUFFER_SIZE: usize>() {
            // Test `split_at`
            let n: usize = BUFFER_SIZE - OFFSET;
            let arr = [1; BUFFER_SIZE];
            let dst = SliceDst::<OFFSET>::ref_from_bytes(&arr[..]).unwrap();
            for i in 0..=n {
                let (l, r) = dst.split_at(i).unwrap();
                let l_sum: u8 = l.trailing.iter().sum();
                let r_sum: u8 = r.iter().sum();
                assert_eq!(l_sum, i as u8);
                assert_eq!(r_sum, (n - i) as u8);
                assert_eq!(l_sum + r_sum, n as u8);
            }

            // Test `split_at_mut`
            let n: usize = BUFFER_SIZE - OFFSET;
            let mut arr = [1; BUFFER_SIZE];
            let dst = SliceDst::<OFFSET>::mut_from_bytes(&mut arr[..]).unwrap();
            for i in 0..=n {
                let (l, r) = dst.split_at_mut(i).unwrap();
                let l_sum: u8 = l.trailing.iter().sum();
                let r_sum: u8 = r.iter().sum();
                assert_eq!(l_sum, i as u8);
                assert_eq!(r_sum, (n - i) as u8);
                assert_eq!(l_sum + r_sum, n as u8);
            }
        }

        test_split_at::<0, 16>();
        test_split_at::<1, 17>();
        test_split_at::<2, 18>();
    }
}
