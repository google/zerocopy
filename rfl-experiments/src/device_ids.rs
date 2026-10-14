// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

//! A PCI-shaped const ID table with a typed context-field descriptor.

use core::mem::{align_of, size_of, MaybeUninit};

use zerocopy::{pointer::cast::CastSizedExact, FromBytes, Immutable, IntoBytes, KnownLayout, Ptr};

#[derive(Clone, Copy, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct RawPciId {
    pub vendor: u32,
    pub device: u32,
    pub subvendor: u32,
    pub subdevice: u32,
    pub class: u32,
    pub class_mask: u32,
    driver_data: usize,
}

crate::field_descriptor!(ContextField, RawPciId, driver_data, usize);

#[derive(FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(transparent)]
pub struct DeviceId(RawPciId);

impl DeviceId {
    pub const fn new(vendor: u32, device: u32) -> Self {
        Self(RawPciId {
            vendor,
            device,
            subvendor: u32::MAX,
            subdevice: u32::MAX,
            class: 0,
            class_mask: 0,
            driver_data: 0,
        })
    }

    /// Exact runtime wrapper conversion uses the existing cast/transmute layer.
    pub fn raw(&self) -> &RawPciId {
        Ptr::from_ref(self)
            .transmute_with::<RawPciId, zerocopy::invariant::Initialized, CastSizedExact, zerocopy::BecauseImmutable>()
            .recall_validity::<zerocopy::invariant::Safe, zerocopy::BecauseImmutable>()
            .try_into_aligned().unwrap().as_ref()
    }
}

pub struct Context {
    pub name: &'static str,
}

/// Context pointers are kept inside MaybeUninit so CTFE does not have to
/// reinterpret pointers as integer values. Construction and fields are sealed.
#[repr(C)]
pub struct IdTable<const N: usize> {
    entries: [MaybeUninit<RawPciId>; N],
    sentinel: MaybeUninit<RawPciId>,
}

impl<const N: usize> IdTable<N> {
    /// Concrete const construction avoids non-const trait calls/transmute_copy.
    pub const fn new(ids: [(DeviceId, &'static Context); N]) -> Self {
        assert!(size_of::<usize>() == size_of::<Option<&Context>>());
        assert!(align_of::<usize>() == align_of::<Option<&Context>>());
        let mut entries = [const { MaybeUninit::uninit() }; N];
        let mut i = 0;
        while i < N {
            entries[i] = MaybeUninit::new(ids[i].0 .0);
            let context = ContextField::project_const(entries[i].as_mut_ptr());
            // SAFETY: The descriptor selects the actual usize field. The size
            // and alignment assertions match Option<&Context>; this store is
            // in the initialized MaybeUninit allocation, and preserves the
            // supplied static reference's provenance. Other fields are untouched.
            unsafe { context.cast::<Option<&'static Context>>().write(Some(ids[i].1)) };
            i += 1;
        }
        Self { entries, sentinel: MaybeUninit::zeroed() }
    }

    pub fn context(&self, index: usize) -> Option<&'static Context> {
        let entry = self.entries.get(index)?;
        let field = ContextField::project_const(entry.as_ptr().cast_mut());
        // SAFETY: new wrote Some(static reference) at exactly this field, with
        // matching size/alignment. The private table has no mutating methods.
        // The reference is read from its provenance-carrying representation,
        // rather than reconstructing a pointer from an integer address.
        unsafe { field.cast::<Option<&'static Context>>().read() }
    }

    pub fn as_raw_ptr(&self) -> *const RawPciId {
        // Start with the complete table, retaining access to its sentinel.
        core::ptr::from_ref(self).cast()
    }

    pub fn sentinel_is_zero(&self) -> bool {
        // SAFETY: The sentinel is constructed with all-zero bytes, which are
        // valid for every integer field of RawPciId. It is never mutated.
        let raw = unsafe { self.sentinel.assume_init_ref() };
        raw.vendor == 0
            && raw.device == 0
            && raw.subvendor == 0
            && raw.subdevice == 0
            && raw.class == 0
            && raw.class_mask == 0
            && raw.driver_data == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    static FIRST: Context = Context { name: "first" };
    static SECOND: Context = Context { name: "second" };
    const TABLE: IdTable<2> =
        IdTable::new([(DeviceId::new(0x1234, 1), &FIRST), (DeviceId::new(0x1234, 2), &SECOND)]);

    #[test]
    fn const_table_retains_context_provenance_and_sentinel() {
        let table = TABLE;
        assert!(core::ptr::eq(table.context(0).unwrap(), &FIRST));
        assert!(core::ptr::eq(table.context(1).unwrap(), &SECOND));
        assert!(table.context(2).is_none());
        assert!(table.sentinel_is_zero());
        assert_eq!(size_of::<IdTable<2>>(), 3 * size_of::<RawPciId>());
        // SAFETY: Table starts with N live RawPciId-sized entries, followed by
        // the initialized sentinel; read only the integer vendor field.
        assert_eq!(unsafe { (*table.as_raw_ptr()).vendor }, 0x1234);
    }

    #[test]
    fn exact_wrapper_cast_and_empty_table() {
        let id = DeviceId::new(0xabcd, 42);
        assert_eq!((id.raw().vendor, id.raw().device), (0xabcd, 42));
        assert!(IdTable::<0>::new([]).sentinel_is_zero());
    }
}
