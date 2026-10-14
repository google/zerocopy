// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

//! Raw-address projections, with an adapter for allocation-backed `PtrInner`.

use core::{marker::PhantomData, ops::Range};

use zerocopy::pointer::{cast::Project, PtrInner};

/// A projection that also accepts addresses outside Rust allocations.
///
/// # Safety
///
/// `project` must not access memory or change provenance. For an allocation-
/// backed source, its output must address a subset of the source's bytes. For
/// any other source, it must apply the same layout-defined address calculation
/// without dereferencing the source. The output need not be aligned.
pub unsafe trait AddressProject<Src: ?Sized, Dst: ?Sized> {
    fn project(src: *mut Src) -> *mut Dst;
}

/// Turns a raw-address descriptor into an existing zerocopy `Project`.
pub struct InAllocation<P>(PhantomData<P>);

// SAFETY: AddressProject requires preservation of provenance and the subset
// relationship on allocation-backed sources, exactly the Project postcondition.
unsafe impl<Src: ?Sized, Dst: ?Sized, P: AddressProject<Src, Dst>> Project<Src, Dst>
    for InAllocation<P>
{
    fn project(src: PtrInner<'_, Src>) -> *mut Dst {
        P::project(src.as_ptr())
    }
}

/// Defines a sized field descriptor; no dummy allocation or Deref inference.
///
/// A mistaken field type is rejected at compile time:
///
/// ```compile_fail
/// use rfl_zerocopy_experiments::field_descriptor;
/// struct Registers { status: u32 }
/// field_descriptor!(Status, Registers, status, u64);
/// ```
///
/// Deref-based field access is rejected by `offset_of!`:
///
/// ```compile_fail
/// use rfl_zerocopy_experiments::field_descriptor;
/// struct Registers { status: u32 }
/// field_descriptor!(Status, Box<Registers>, status, u32);
/// ```
#[macro_export]
macro_rules! field_descriptor {
    ($vis:vis $name:ident, $src:ty, $field:tt, $dst:ty) => {
        $vis struct $name;
        impl $name {
            $vis const OFFSET: usize = core::mem::offset_of!($src, $field);

            $vis const fn project_const(src: *mut $src) -> *mut $dst {
                src.cast::<u8>().wrapping_add(Self::OFFSET).cast::<$dst>()
            }
        }
        // Check the field type without ever calling the raw-borrow closure.
        const _: fn(*mut $src) -> *mut $dst = |src| {
            // SAFETY: This closure is only a type-checking witness and is never
            // called. offset_of! separately requires a real field, not Deref.
            unsafe { &raw mut (*src).$field }
        };
        // SAFETY: offset_of! gives the offset of this actual field. The type
        // witness equates the destination with the field type. Its storage is
        // contained in the source; wrapping_add does not access memory and
        // preserves provenance. Packed fields are allowed, without alignment.
        unsafe impl $crate::address_projection::AddressProject<$src, $dst> for $name {
            fn project(src: *mut $src) -> *mut $dst {
                Self::project_const(src)
            }
        }
    };
}

/// Bounds-checked runtime indexing, including address-only MMIO pointers.
pub fn index<T>(slice: *mut [T], index: usize) -> Option<*mut T> {
    (index < slice.len()).then(|| slice.cast::<T>().wrapping_add(index))
}

/// Bounds-checked runtime range projection; accepts an empty range at the end.
pub fn range<T>(slice: *mut [T], range: Range<usize>) -> Option<*mut [T]> {
    let len = range.end.checked_sub(range.start)?;
    if range.end > slice.len() {
        return None;
    }
    Some(core::ptr::slice_from_raw_parts_mut(slice.cast::<T>().wrapping_add(range.start), len))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[repr(C)]
    struct Registers {
        control: u32,
        status: u32,
        counters: [u32; 4],
    }
    field_descriptor!(Status, Registers, status, u32);
    field_descriptor!(Counters, Registers, counters, [u32; 4]);

    #[repr(C, packed)]
    struct Packed {
        tag: u8,
        word: u32,
    }
    field_descriptor!(Word, Packed, word, u32);

    #[test]
    fn projects_mmio_and_null_addresses_without_access() {
        for addr in [0, 0x1000, usize::MAX - 2] {
            let src = core::ptr::without_provenance_mut::<Registers>(addr);
            assert_eq!(Status::project(src).addr(), addr.wrapping_add(4));
            assert_eq!(
                Status::project(src).cast_const(),
                rfl_projection_baseline::ptr::project!(src, .status)
            );
            let counters = Counters::project(src);
            let slice = core::ptr::slice_from_raw_parts_mut(counters.cast::<u32>(), 4);
            assert_eq!(index(slice, 3).unwrap().addr(), addr.wrapping_add(20));
            assert_eq!(
                index(slice, 3).unwrap().cast_const(),
                rfl_projection_baseline::ptr::project!(slice, [panic: 3])
            );
            assert!(index(slice, 4).is_none());
        }
    }

    #[test]
    fn adapter_preserves_real_allocation_provenance() {
        let mut registers = Registers { control: 0, status: 42, counters: [0; 4] };
        let ptr = PtrInner::from_mut(&mut registers).project::<_, InAllocation<Status>>();
        // SAFETY: The adapter selects the initialized u32 status field in this
        // live, exclusively borrowed Registers allocation. repr(C) aligns it.
        assert_eq!(unsafe { ptr.as_ptr().read() }, 42);
    }

    #[test]
    fn packed_fields_and_range_edges() {
        let mut packed = Packed { tag: 1, word: 42 };
        let ptr = PtrInner::from_mut(&mut packed).project::<_, InAllocation<Word>>();
        // SAFETY: The projected field is initialized and in the borrowed
        // allocation; read_unaligned does not require its packed address aligned.
        assert_eq!(unsafe { ptr.as_ptr().read_unaligned() }, 42);
        let raw = core::ptr::slice_from_raw_parts_mut(core::ptr::dangling_mut::<u8>(), 4);
        assert_eq!(range(raw, 4..4).unwrap().len(), 0);
        assert!(range(raw, Range { start: 3, end: 2 }).is_none());
        assert!(range(raw, 0..5).is_none());
        assert!(index(core::ptr::slice_from_raw_parts_mut(core::ptr::dangling_mut::<()>(), 0), 0)
            .is_none());
    }
}
