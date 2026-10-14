// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

//! Typed field slots with real RfL pin-init, rollback, and structural pinning.

use core::{
    cell::Cell,
    marker::{PhantomData, PhantomPinned},
    mem::MaybeUninit,
    pin::Pin,
};
use std::rc::Rc;

use pin_init::{pin_data, pin_init_from_closure, InPlaceInit, PinInit};
use zerocopy::{
    invariant::{Aligned, Exclusive, Safe, Uninit},
    pointer::{cast::Projection, BecauseExclusive},
    Project, Ptr,
};

struct Unpinned;
struct Pinned;

/// The pointer carries allocation, exclusivity, alignment, and validity. `P`
/// separately carries structural pinning; zerocopy does not establish pinning.
struct Slot<'a, P, T> {
    ptr: Ptr<'a, T, (Exclusive, Aligned, Uninit)>,
    marker: PhantomData<P>,
}

struct Guard<'a, P, T> {
    ptr: Ptr<'a, T, (Exclusive, Aligned, Safe)>,
    marker: PhantomData<P>,
}

impl<'a, T> Slot<'a, Unpinned, T> {
    fn write(self, value: T) -> Guard<'a, Unpinned, T> {
        let storage =
            self.ptr.transmute::<MaybeUninit<T>, Safe, _>().try_into_aligned().unwrap().as_mut();
        Guard { ptr: Ptr::from_mut(storage.write(value)), marker: PhantomData }
    }
}

impl<'a, T> Slot<'a, Pinned, T> {
    fn pin_init<E>(self, init: impl PinInit<T, E>) -> Result<Guard<'a, Pinned, T>, E> {
        let raw = self.ptr.as_inner().as_ptr();
        // SAFETY: This Slot comes only from split_record inside a PinInit
        // closure. Its Ptr supplies the writable aligned exclusive storage;
        // split_record supplies structural pinning. On Err the slot is never
        // accessed again. PinInit owns cleanup of its partial initialization.
        unsafe { init.__init(raw)? };
        // SAFETY: Successful PinInit establishes a valid T at raw. The slot's
        // lifetime, alignment and exclusivity remain unchanged.
        let ptr = unsafe { self.ptr.assume_safe() };
        Ok(Guard { ptr, marker: PhantomData })
    }
}

impl<T> Guard<'_, Pinned, T> {
    fn as_pin_mut(&mut self) -> Pin<&mut T> {
        // SAFETY: The structurally pinned field stays in its parent's pinned
        // allocation. The reborrow prevents competing access for this lifetime.
        unsafe { Pin::new_unchecked(self.ptr.reborrow().as_mut()) }
    }
}

impl<P, T> Drop for Guard<'_, P, T> {
    fn drop(&mut self) {
        // SAFETY: The guard owns one initialized, aligned T in its exclusive
        // Ptr for this lifetime. It is dropped once, in place, also for Pinned.
        unsafe { self.ptr.as_inner().as_ptr().drop_in_place() };
    }
}

struct Resource(Rc<Cell<usize>>);
impl Drop for Resource {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}

struct AddressSensitive {
    address: *const Self,
    drops: Rc<Cell<usize>>,
    _pin: PhantomPinned,
}

impl Drop for AddressSensitive {
    fn drop(&mut self) {
        assert_eq!(self.address, core::ptr::from_ref(self));
        self.drops.set(self.drops.get() + 1);
    }
}

#[pin_data]
#[derive(Project)]
#[repr(C)]
pub struct Record {
    resource: Resource,
    #[pin]
    address_sensitive: AddressSensitive,
}

impl Record {
    pub fn address_is_stable(self: Pin<&Self>) -> bool {
        self.address_sensitive.address == core::ptr::from_ref(&self.address_sensitive)
    }
}

/// A concrete generated-field-split prototype. Generic splitting would need
/// derive support to ensure callers cannot select overlapping/repeated fields.
///
/// # Safety
///
/// The record storage must be structurally pinned until successfully initialized
/// fields are dropped or their ownership is transferred to the completed Record.
unsafe fn split_record<'a>(
    ptr: Ptr<'a, Record, (Exclusive, Aligned, Uninit)>,
) -> (Slot<'a, Unpinned, Resource>, Slot<'a, Pinned, AddressSensitive>) {
    fn consume(
        ptr: Ptr<'_, Record, (Exclusive, Aligned, Uninit)>,
    ) -> zerocopy::pointer::PtrInner<'_, Record> {
        ptr.as_inner()
    }
    // Consume the whole-record capability before issuing field capabilities.
    let inner = consume(ptr);
    let resource = inner.project::<_, Projection<
        zerocopy::project_clients::ProjectDerive,
        _,
        { zerocopy::STRUCT_VARIANT_ID },
        { zerocopy::ident_id!(resource) },
    >>();
    let address = inner.project::<_, Projection<
        zerocopy::project_clients::ProjectDerive,
        _,
        { zerocopy::STRUCT_VARIANT_ID },
        { zerocopy::ident_id!(address_sensitive) },
    >>();
    // SAFETY: The two repr(C) fields have disjoint storage, are in the original
    // allocation for 'a, and inherit its alignment. MaybeUninit permits their
    // Uninit state and has each field's size and alignment. No parent pointer
    // is used until both guards relinquish their ownership. Structural pinning
    // is supplied by the caller and the #[pin] field annotation.
    let (resource, address) = unsafe {
        (
            &mut *resource.as_ptr().cast::<MaybeUninit<Resource>>(),
            &mut *address.as_ptr().cast::<MaybeUninit<AddressSensitive>>(),
        )
    };
    (
        Slot {
            ptr: Ptr::from_mut(resource)
                .transmute::<Resource, Uninit, (_, (_, BecauseExclusive))>()
                .try_into_aligned()
                .unwrap(),
            marker: PhantomData,
        },
        Slot {
            ptr: Ptr::from_mut(address)
                .transmute::<AddressSensitive, Uninit, (_, (_, BecauseExclusive))>()
                .try_into_aligned()
                .unwrap(),
            marker: PhantomData,
        },
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Failure {
    None,
    Error,
    Panic,
}

#[derive(Debug, PartialEq, Eq)]
pub struct InitError;

impl From<core::convert::Infallible> for InitError {
    fn from(value: core::convert::Infallible) -> Self {
        match value {}
    }
}

/// Initializes a pinned allocation, with two field guards alive simultaneously.
/// The completed record cannot be moved out of its pinned allocation:
///
/// ```compile_fail
/// use rfl_zerocopy_experiments::typed_init::{initialize, Failure};
/// use std::{cell::Cell, rc::Rc, pin::Pin};
/// let value = initialize(Failure::None, Rc::new(Cell::new(0)), Rc::new(Cell::new(0))).unwrap();
/// let movable = Pin::into_inner(value);
/// ```
pub fn initialize(
    failure: Failure,
    resource_drops: Rc<Cell<usize>>,
    address_drops: Rc<Cell<usize>>,
) -> Result<Pin<Box<Record>>, InitError> {
    // SAFETY: The closure initializes every Record field before Ok. Guards
    // destroy initialized fields on Err or unwind. On success, forgetting both
    // guards transfers ownership to the Record returned by InPlaceInit.
    let initializer = unsafe {
        pin_init_from_closure(move |raw: *mut Record| {
            // SAFETY: PinInit supplies aligned, exclusively accessed writable
            // storage that remains pinned until initialization or cleanup ends.
            let storage = &mut *raw.cast::<MaybeUninit<Record>>();
            let root = Ptr::from_mut(storage)
                .transmute::<Record, Uninit, (_, (_, BecauseExclusive))>()
                .try_into_aligned()
                .unwrap();
            let (resource, address) = split_record(root);
            let resource = resource.write(Resource(resource_drops));
            let address_initializer = pin_init_from_closure(move |raw: *mut AddressSensitive| {
                match failure {
                    Failure::Error => return Err(InitError),
                    Failure::Panic => panic!("second field panicked"),
                    Failure::None => {}
                }
                // SAFETY: The inner PinInit supplies aligned exclusive
                // uninitialized storage. write initializes every field without
                // reading or dropping the prior contents, at its final address.
                raw.write(AddressSensitive {
                    address: raw,
                    drops: address_drops,
                    _pin: PhantomPinned,
                });
                Ok(())
            });
            let mut address = address.pin_init(address_initializer)?;
            let expected = address.ptr.as_inner().as_ptr();
            assert_eq!(address.as_pin_mut().address, expected);
            core::mem::forget(resource);
            core::mem::forget(address);
            Ok(())
        })
    };
    Box::try_pin_init(initializer)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn success_keeps_address_and_transfers_drop_ownership() {
        let resource = Rc::new(Cell::new(0));
        let address = Rc::new(Cell::new(0));
        let value = initialize(Failure::None, resource.clone(), address.clone()).unwrap();
        assert!(value.as_ref().address_is_stable());
        assert_eq!((resource.get(), address.get()), (0, 0));
        drop(value);
        assert_eq!((resource.get(), address.get()), (1, 1));
    }

    #[test]
    fn second_field_error_drops_only_first_field() {
        let resource = Rc::new(Cell::new(0));
        let address = Rc::new(Cell::new(0));
        assert!(initialize(Failure::Error, resource.clone(), address.clone()).is_err());
        assert_eq!((resource.get(), address.get()), (1, 0));
    }

    #[test]
    fn second_field_unwind_drops_only_first_field() {
        let resource = Rc::new(Cell::new(0));
        let address = Rc::new(Cell::new(0));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = initialize(Failure::Panic, resource.clone(), address.clone());
        }));
        assert!(outcome.is_err());
        assert_eq!((resource.get(), address.get()), (1, 0));
    }
}
