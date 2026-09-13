// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// See comment in `include.rs` for why we disable the prelude.
#![no_implicit_prelude]
#![allow(dead_code)]
#![cfg(zerocopy_unstable_ptr)]

include!("include.rs");

// Read through the existing pointer APIs so these tests focus on which field
// bindings are in scope, independently of conveniences for reading them.
fn read<T: imp::Copy + imp::Immutable, A: imp::invariant::Alignment>(
    field: imp::Ptr<'_, imp::ReadOnly<T>, (imp::invariant::Shared, A, imp::invariant::Safe)>,
) -> T {
    field.transmute::<T, _, imp::BecauseImmutable>().read()
}

#[derive(imp::TryFromBytes, imp::KnownLayout, imp::Immutable)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C, packed)]
struct Foo {
    a: u8,
    #[zerocopy(invariant((read(a) % 2) == (read(b) as u8)))]
    b: bool,
    #[zerocopy(invariant(read(c) > 0))]
    c: i16,
}

#[test]
fn current_and_previous_fields() {
    use imp::TryFromBytes as _;

    for (a, b, c, valid) in [
        (2, 0, 1i16, true),
        (3, 1, 1, true),
        (2, 1, 1, false),
        (3, 0, 1, false),
        (2, 0, 0, false),
        (2, 0, -1, false),
        (2, 2, 1, false),
    ] {
        let c = c.to_ne_bytes();
        let bytes = [a, b, c[0], c[1]];
        imp::assert_eq!(Foo::try_ref_from_bytes(&bytes).is_ok(), valid);
    }
}

mod order {
    use super::{imp, read, util};

    static CALLS: imp::core::sync::atomic::AtomicUsize =
        imp::core::sync::atomic::AtomicUsize::new(0);

    fn check(expected: usize, result: bool) -> bool {
        imp::assert_eq!(CALLS.fetch_add(1, imp::core::sync::atomic::Ordering::SeqCst), expected);
        result
    }

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    struct Ordered {
        #[zerocopy(invariant(check(0, read(a))))]
        #[zerocopy(invariant(check(1, true)), invariant(check(2, true)))]
        a: bool,
        #[zerocopy(invariant(check(3, read(a) == read(b))))]
        b: bool,
    }

    #[test]
    fn bit_validity_and_short_circuiting() {
        for (bytes, valid, calls) in [
            ([1u8, 1], true, 4),
            ([2, 1], false, 0),
            ([0, 1], false, 1),
            ([1, 2], false, 3),
            ([1, 0], false, 4),
        ] {
            CALLS.store(0, imp::core::sync::atomic::Ordering::SeqCst);
            util::test_is_safe::<Ordered, _>(bytes, valid);
            imp::assert_eq!(CALLS.load(imp::core::sync::atomic::Ordering::SeqCst), calls);
        }
    }
}

#[derive(imp::TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct EarlyReturn {
    #[zerocopy(invariant(return read(a)))]
    a: bool,
    b: bool,
}

#[test]
fn return_does_not_bypass_later_fields() {
    util::test_is_safe::<EarlyReturn, _>([1u8, 1], true);
    util::test_is_safe::<EarlyReturn, _>([0u8, 1], false);
    util::test_is_safe::<EarlyReturn, _>([1u8, 2], false);
}

#[derive(imp::TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(u8)]
enum Enum {
    A {
        a: u8,
        #[zerocopy(invariant(read(a) == read(b)))]
        b: u8,
    },
    B {
        a: u8,
        #[zerocopy(invariant(read(a) != read(b)))]
        b: u8,
    },
    Tuple(bool, bool),
    Unit,
}

#[test]
fn selected_variant() {
    for (bytes, valid) in [
        ([0u8, 5, 5], true),
        ([0, 5, 6], false),
        ([1, 5, 6], true),
        ([1, 5, 5], false),
        ([2, 1, 1], true),
        ([2, 2, 1], false),
        ([3, 2, 2], true),
        ([4, 0, 0], false),
    ] {
        util::test_is_safe::<Enum, _>(bytes, valid);
    }
}

#[derive(imp::TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
enum CEnum {
    A {
        #[zerocopy(invariant(read(a) > 0))]
        a: u32,
    },
}

#[test]
fn c_enum() {
    util::test_is_safe::<CEnum, _>([0u32, 1], true);
    util::test_is_safe::<CEnum, _>([0u32, 0], false);
    util::test_is_safe::<CEnum, _>([1u32, 1], false);
}

// These names must still bind to fields, even in the presence of outer
// constants with the same names and generated source-pointer bindings.
#[allow(non_upper_case_globals)]
const candidate_: u8 = 42;
#[allow(non_upper_case_globals)]
const r#type: u8 = 42;

#[derive(imp::TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct Names {
    candidate: u8,
    #[zerocopy(invariant(read(candidate) == read(candidate_)))]
    candidate_: u8,
    #[zerocopy(invariant(read(r#type) == read(candidate)))]
    r#type: u8,
}

#[test]
fn field_names() {
    util::test_is_safe::<Names, _>([1u8, 1, 1], true);
    util::test_is_safe::<Names, _>([1u8, 2, 1], false);
    util::test_is_safe::<Names, _>([1u8, 1, 2], false);
}

#[derive(imp::TryFromBytes)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct Generic<T: imp::Copy + imp::Immutable + imp::PartialEq> {
    a: T,
    #[zerocopy(invariant(read(a) == read(b)))]
    b: T,
}

#[test]
fn generic() {
    util::test_is_safe::<Generic<u8>, _>([1u8, 1], true);
    util::test_is_safe::<Generic<u8>, _>([1u8, 2], false);
    util::test_is_safe::<Generic<bool>, _>([1u8, 2], false);
}

#[derive(imp::TryFromBytes, imp::KnownLayout, imp::Immutable)]
#[zerocopy(crate = "zerocopy_renamed")]
#[repr(C)]
struct Unsized {
    #[zerocopy(invariant(read(a) > 0))]
    a: u8,
    b: [bool],
}

#[test]
fn unsized_tail() {
    use imp::TryFromBytes as _;

    imp::assert!(Unsized::try_ref_from_bytes(&[1, 0, 1]).is_ok());
    imp::assert!(Unsized::try_ref_from_bytes(&[0, 0, 1]).is_err());
    imp::assert!(Unsized::try_ref_from_bytes(&[1, 2, 1]).is_err());
}

#[derive(imp::TryFromBytes, imp::FromBytes, imp::FromZeros)]
#[zerocopy(crate = "zerocopy_renamed", on_error = "skip")]
struct SkipInfallibleDerives {
    #[zerocopy(invariant(read(a) > 0))]
    a: u8,
}

util_assert_impl_all!(SkipInfallibleDerives: imp::TryFromBytes);
util_assert_not_impl_any!(SkipInfallibleDerives: imp::FromBytes, imp::FromZeros);

#[test]
fn skipped_derives_preserve_invariants() {
    util::test_is_safe::<SkipInfallibleDerives, _>([1u8], true);
    util::test_is_safe::<SkipInfallibleDerives, _>([0u8], false);
}

mod unions {
    use super::{imp, read, util};

    static CALLS: imp::core::sync::atomic::AtomicUsize =
        imp::core::sync::atomic::AtomicUsize::new(0);

    fn record(mark: usize, result: bool) -> bool {
        let order = imp::core::sync::atomic::Ordering::SeqCst;
        CALLS.store(CALLS.load(order) * 10 + mark, order);
        result
    }

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    union Ordered {
        #[zerocopy(invariant(record(1, read(a))))]
        #[zerocopy(invariant(record(2, true)))]
        a: bool,
        #[zerocopy(invariant(record(3, read(b) == 2)))]
        b: u8,
    }

    #[test]
    fn field_validity_invariants_and_fallback() {
        for (byte, valid, calls) in [(0u8, false, 13), (1, true, 12), (2, true, 3), (3, false, 3)] {
            CALLS.store(0, imp::core::sync::atomic::Ordering::SeqCst);
            util::test_is_safe::<Ordered, _>([byte], valid);
            imp::assert_eq!(CALLS.load(imp::core::sync::atomic::Ordering::SeqCst), calls);
        }
    }

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    union EarlyReturn {
        #[zerocopy(invariant(return true))]
        #[zerocopy(invariant(false))]
        a: u8,
        #[zerocopy(invariant(return read(b) == 7))]
        b: u8,
    }

    #[test]
    fn return_is_local_to_each_hook() {
        // The first hook's `return true` must not bypass its field's second
        // hook. Rejecting that field must still allow the second field to pass.
        util::test_is_safe::<EarlyReturn, _>([0u8], false);
        util::test_is_safe::<EarlyReturn, _>([7u8], true);
    }

    #[allow(non_upper_case_globals)]
    const candidate_: u8 = 42;
    #[allow(non_upper_case_globals)]
    const r#type: u8 = 42;

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    union Names {
        #[zerocopy(invariant(read(candidate) == 1))]
        candidate: u8,
        #[zerocopy(invariant(read(candidate_) == 2))]
        candidate_: u8,
        #[zerocopy(invariant(read(r#type) == 3))]
        r#type: u8,
    }

    #[test]
    fn field_names() {
        for byte in 0u8..=4 {
            util::test_is_safe::<Names, _>([byte], (1..=3).contains(&byte));
        }
    }

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    union Generic<T: imp::Copy + imp::Immutable + imp::PartialEq + imp::Default> {
        #[zerocopy(invariant(read(a) == T::default()))]
        a: T,
    }

    #[test]
    fn generic() {
        util::test_is_safe::<Generic<bool>, _>([0u8], true);
        util::test_is_safe::<Generic<bool>, _>([1u8], false);
        util::test_is_safe::<Generic<bool>, _>([2u8], false);
        util::test_is_safe::<Generic<u8>, _>([0u8], true);
        util::test_is_safe::<Generic<u8>, _>([1u8], false);
    }

    #[derive(imp::TryFromBytes)]
    #[zerocopy(crate = "zerocopy_renamed")]
    #[repr(C)]
    union InteriorMutable {
        #[zerocopy(invariant(true))]
        a: imp::ManuallyDrop<imp::UnsafeCell<bool>>,
    }

    #[test]
    fn field_need_not_be_immutable() {
        util::test_is_safe::<InteriorMutable, _>([0u8], true);
        util::test_is_safe::<InteriorMutable, _>([1u8], true);
        util::test_is_safe::<InteriorMutable, _>([2u8], false);
    }
}
