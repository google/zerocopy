// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

//! A migration facade with RfL method names and zerocopy implementations.

use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

/// Legacy reference/copy conversion, implemented without handwritten unsafe.
///
/// Interior-mutable types do not satisfy the facade:
///
/// ```compile_fail
/// use rfl_zerocopy_experiments::conversions::LegacyFromBytes;
/// let _ = <core::cell::Cell<u32> as LegacyFromBytes>::from_bytes_copy(&[0; 4]);
/// ```
pub trait LegacyFromBytes: FromBytes + Immutable {
    fn from_bytes(bytes: &[u8]) -> Option<&Self>
    where
        Self: Sized + KnownLayout,
    {
        Self::ref_from_bytes(bytes).ok()
    }

    fn from_bytes_prefix(bytes: &[u8]) -> Option<(&Self, &[u8])>
    where
        Self: Sized + KnownLayout,
    {
        Self::ref_from_prefix(bytes).ok()
    }

    fn from_bytes_mut(bytes: &mut [u8]) -> Option<&mut Self>
    where
        Self: Sized + KnownLayout + IntoBytes,
    {
        Self::mut_from_bytes(bytes).ok()
    }

    fn from_bytes_mut_prefix(bytes: &mut [u8]) -> Option<(&mut Self, &mut [u8])>
    where
        Self: Sized + KnownLayout + IntoBytes,
    {
        Self::mut_from_prefix(bytes).ok()
    }

    fn from_bytes_copy(bytes: &[u8]) -> Option<Self>
    where
        Self: Sized,
    {
        Self::read_from_bytes(bytes).ok()
    }

    fn from_bytes_copy_prefix(bytes: &[u8]) -> Option<(Self, &[u8])>
    where
        Self: Sized,
    {
        Self::read_from_prefix(bytes).ok()
    }
}
impl<T: ?Sized + FromBytes + Immutable> LegacyFromBytes for T {}

pub trait LegacyAsBytes: IntoBytes + Immutable {
    fn as_bytes(&self) -> &[u8] {
        IntoBytes::as_bytes(self)
    }

    fn as_bytes_mut(&mut self) -> &mut [u8]
    where
        Self: FromBytes,
    {
        IntoBytes::as_mut_bytes(self)
    }
}
impl<T: ?Sized + IntoBytes + Immutable> LegacyAsBytes for T {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rfl_transmute;

    #[repr(C, align(8))]
    struct Aligned([u8; 24]);

    #[test]
    fn agrees_with_original_rfl_for_size_alignment_and_copy() {
        let bytes = Aligned(core::array::from_fn(|i| i as u8));
        for start in 0..=16 {
            for len in 0..=8 {
                let source = &bytes.0[start..start + len];
                assert_eq!(
                    <u32 as LegacyFromBytes>::from_bytes(source),
                    <u32 as rfl_transmute::FromBytes>::from_bytes(source)
                );
                assert_eq!(
                    <u32 as LegacyFromBytes>::from_bytes_copy(source),
                    <u32 as rfl_transmute::FromBytes>::from_bytes_copy(source)
                );
                assert_eq!(
                    <u32 as LegacyFromBytes>::from_bytes_prefix(source),
                    <u32 as rfl_transmute::FromBytes>::from_bytes_prefix(source)
                );
                assert_eq!(
                    <u32 as LegacyFromBytes>::from_bytes_copy_prefix(source),
                    <u32 as rfl_transmute::FromBytes>::from_bytes_copy_prefix(source)
                );
            }
        }
    }

    #[test]
    fn mutable_prefix_and_slice_conversions() {
        let mut bytes = Aligned([0; 24]);
        let (word, remainder) =
            <u32 as LegacyFromBytes>::from_bytes_mut_prefix(&mut bytes.0).unwrap();
        *word = 0x12345678;
        assert_eq!(remainder.len(), 20);
        assert_eq!(&bytes.0[..4], &0x12345678_u32.to_ne_bytes());
        let words = [1_u32, 2, 3];
        assert_eq!(
            LegacyAsBytes::as_bytes(&words[..]),
            rfl_transmute::AsBytes::as_bytes(&words[..])
        );
        let mut value = 0_u32;
        LegacyAsBytes::as_bytes_mut(&mut value).copy_from_slice(&42_u32.to_ne_bytes());
        assert_eq!(value, 42);
    }

    #[test]
    fn derived_dma_record_needs_no_legacy_unsafe_impls() {
        #[derive(FromBytes, IntoBytes, Immutable, KnownLayout)]
        #[repr(C)]
        struct Descriptor {
            head: u32,
            body: u32,
        }
        let descriptor = Descriptor { head: 1, body: 2 };
        let copy =
            <Descriptor as LegacyFromBytes>::from_bytes_copy(LegacyAsBytes::as_bytes(&descriptor))
                .unwrap();
        assert_eq!((copy.head, copy.body), (1, 2));
    }
}
