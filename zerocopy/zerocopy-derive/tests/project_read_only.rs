// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(warnings)]

include!("include.rs");

type SharedAligned<V> = (imp::invariant::Shared, imp::invariant::Aligned, V);

#[derive(imp::Project, imp::TryFromBytes, imp::IntoBytes, imp::KnownLayout)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum Overlapping {
    A(imp::core::cell::Cell<u8>),
    B(u8),
}

// Regression for #3757: these impls would allow coexisting `&Cell<u8>` and
// `&u8` to the same byte, without checking the enum's active variant.
macro_rules! assert_no_unchecked_shared_projection {
    ($client:ty, $variant:ident) => {
        util_assert_not_impl_any!(Overlapping:
            imp::ProjectField<$client, (), SharedAligned<imp::invariant::Uninit>, { imp::ident_id!($variant) }, 0>,
            imp::ProjectField<$client, (), SharedAligned<imp::invariant::Initialized>, { imp::ident_id!($variant) }, 0>,
        );
    };
}

assert_no_unchecked_shared_projection!(imp::project_clients::ProjectDerive, A);
assert_no_unchecked_shared_projection!(imp::project_clients::ProjectDerive, B);
assert_no_unchecked_shared_projection!(imp::project_clients::TryFromBytesDerive, A);
assert_no_unchecked_shared_projection!(imp::project_clients::TryFromBytesDerive, B);

macro_rules! check_read_only_projections {
    ($client:ty, $ptr:expr) => {{
        let ptr = $ptr;
        let cell: imp::Ptr<
            '_,
            imp::ReadOnly<imp::core::cell::Cell<u8>>,
            SharedAligned<imp::invariant::Initialized>,
        > = ptr.project::<$client, _, { imp::ident_id!(A) }, 0>().unwrap();
        let byte: imp::Ptr<'_, imp::ReadOnly<u8>, SharedAligned<imp::invariant::Initialized>> =
            ptr.project::<$client, _, { imp::ident_id!(B) }, 0>().unwrap();
        let cell = cell.recall_validity::<imp::invariant::Safe, imp::BecauseImmutable>();
        let byte = byte.recall_validity::<imp::invariant::Safe, imp::BecauseImmutable>();
        imp::assert_eq!(imp::IntoBytes::as_bytes(cell.as_ref()), &[42]);
        imp::assert_eq!(**byte.as_ref(), 42);

        let uninit = ptr.recall_validity::<imp::invariant::Uninit, imp::BecauseImmutable>();
        let _: imp::Ptr<'_, imp::ReadOnly<u8>, SharedAligned<imp::invariant::Uninit>> =
            uninit.project::<$client, _, { imp::ident_id!(B) }, 0>().unwrap();
    }};
}

#[test]
fn overlapping_fields_remain_read_only() {
    for tag in [0u8, 1, 255] {
        let bytes = [tag, 42];
        let ptr = imp::Ptr::from_ref(&bytes[..])
            .try_cast_into_no_leftover::<imp::ReadOnly<Overlapping>, imp::BecauseImmutable>(
                imp::None,
            )
            .unwrap();
        check_read_only_projections!(imp::project_clients::ProjectDerive, ptr);
        check_read_only_projections!(imp::project_clients::TryFromBytesDerive, ptr);

        // Validation must still support interior-mutable enums through its
        // shared `ReadOnly` candidate, including rejection of invalid tags.
        imp::assert_eq!(<Overlapping as imp::TryFromBytes>::is_safe(ptr), tag < 2);
    }
}

#[test]
fn read_only_uninit_projection_does_not_read_tag() {
    let mut storage = imp::MaybeUninit::<imp::ReadOnly<Overlapping>>::uninit();
    let mut ptr = imp::Ptr::from_mut(&mut storage)
        .transmute::<
            imp::ReadOnly<Overlapping>,
            imp::invariant::Uninit,
            (_, (_, imp::BecauseExclusive)),
        >()
        .try_into_aligned()
        .unwrap();
    let ptr = ptr.reborrow_shared();
    let _: imp::Ptr<
        '_,
        imp::ReadOnly<imp::core::cell::Cell<u8>>,
        SharedAligned<imp::invariant::Uninit>,
    > = ptr.project::<imp::project_clients::ProjectDerive, _, { imp::ident_id!(A) }, 0>().unwrap();
    let _: imp::Ptr<'_, imp::ReadOnly<u8>, SharedAligned<imp::invariant::Uninit>> = ptr
        .project::<imp::project_clients::TryFromBytesDerive, _, { imp::ident_id!(B) }, 0>()
        .unwrap();
}

#[test]
fn read_only_safe_projection_checks_tag() {
    let value = imp::ReadOnly::new(Overlapping::B(42));
    let ptr = imp::Ptr::from_ref(&value);
    let byte: imp::core::result::Result<
        imp::Ptr<'_, imp::ReadOnly<u8>, SharedAligned<imp::invariant::Safe>>,
        (),
    > = ptr.project::<imp::project_clients::ProjectDerive, _, { imp::ident_id!(B) }, 0>();
    imp::assert_eq!(**byte.unwrap().as_ref(), 42);
    imp::assert!(ptr
        .project::<imp::project_clients::ProjectDerive, _, { imp::ident_id!(A) }, 0>()
        .is_err());

    let value = Overlapping::A(imp::core::cell::Cell::new(1));
    let ptr = imp::Ptr::from_ref(&value);
    let cell =
        ptr.project::<imp::project_clients::ProjectDerive, _, { imp::ident_id!(A) }, 0>().unwrap();
    cell.as_ref().set(42);
    imp::assert_eq!(cell.as_ref().get(), 42);
    imp::assert!(ptr
        .project::<imp::project_clients::ProjectDerive, _, { imp::ident_id!(B) }, 0>()
        .is_err());
}

#[derive(imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C, packed)]
struct Packed {
    byte: u8,
    word: u32,
}

#[test]
fn read_only_projection_preserves_output_alignment() {
    let value = imp::ReadOnly::new(Packed { byte: 1, word: 42 });
    let word: imp::Ptr<
        '_,
        imp::ReadOnly<u32>,
        (imp::invariant::Shared, imp::invariant::Unaligned, imp::invariant::Safe),
    > = imp::Ptr::from_ref(&value)
        .project::<imp::project_clients::ProjectDerive, _, { imp::STRUCT_VARIANT_ID }, { imp::ident_id!(word) }>()
        .unwrap();
    imp::assert_eq!(imp::ReadOnly::into_inner(word.read::<imp::BecauseImmutable>()), 42);
}

#[derive(imp::Project)]
#[zerocopy(crate = "zerocopy_renamed")]
struct Unsized<T: ?imp::Sized> {
    head: u8,
    tail: T,
}

#[test]
fn read_only_projection_preserves_unsized_metadata_and_exclusivity() {
    let mut value = imp::ReadOnly::new(Unsized { head: 0, tail: [1u8, 2, 3] });
    let value: &mut imp::ReadOnly<Unsized<[u8]>> = &mut value;
    let tail: imp::Ptr<
        '_,
        imp::ReadOnly<[u8]>,
        (imp::invariant::Exclusive, imp::invariant::Aligned, imp::invariant::Safe),
    > = imp::Ptr::from_mut(value)
        .project::<imp::project_clients::ProjectDerive, _, { imp::STRUCT_VARIANT_ID }, { imp::ident_id!(tail) }>()
        .unwrap();
    let tail = tail.as_mut();
    imp::assert_eq!(&**tail, &[1, 2, 3]);
    tail[1] = 42;
    imp::assert_eq!(&**tail, &[1, 42, 3]);
}
