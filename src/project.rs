// Copyright 2024 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use crate::pointer::{
    invariant::{Aliasing, Aligned, Alignment, AlignmentMapping, MappedAlignment, Valid},
    Ptr,
};

// NOTE: `NAME_HASH` is not semver-stable - it just needs to be consistent
// within a single compilation.
//
// TODO: `#[diagnostic::on_unimplemented]`
#[doc(hidden)]
pub unsafe trait Field<const NAME_HASH: u128> {
    type Type;
    const OFFSET: isize;

    // Basically, `Preserved` unless the struct is `#[repr(packed)]`. TODO:
    // Confirm that this is the correct behavior.
    type AlignmentMapping: AlignmentMapping;
}

pub unsafe trait Projectable {
    type Of<T>;
    type Inner;
}

unsafe impl<T> Projectable for core::mem::ManuallyDrop<T> {
    type Of<U> = core::mem::ManuallyDrop<U>;
    type Inner = T;
}

// TODO: Use `Ptr` to make this generic over `&`, `&mut`, `Box`, etc.
#[doc(hidden)]
#[allow(clippy::must_use_candidate)]
#[inline(never)]
pub const fn project<'a, P, A, AA, const NAME_HASH: u128>(
    // ptr: *const P,
    ptr: Ptr<'a, P, (A, AA, Valid)>,
) -> Ptr<
    'a,
    P::Of<<P::Inner as Field<{ NAME_HASH }>>::Type>,
    (A, MappedAlignment<AA, <P::Inner as Field<{ NAME_HASH }>>::AlignmentMapping>, Valid),
>
where
    P: Projectable,
    P::Inner: Field<{ NAME_HASH }>,
    A: Aliasing,
    AA: Alignment,
{
    // NOTE: Doing the actual cast inside this function makes the `project!`
    // macro simpler, but it also means that we can't handle both const code and
    // unsized types at the same time. In order to be const, we can't call trait
    // methods, but in order to support unsized types, we'd need to provide a
    // trait method to perform certain pointer casts (if we were using unsized
    // types, Rust wouldn't be smart enough to know that all of these casts had
    // the same vtable kinds).
    //
    // An alternative is to perform the casts in the macro body itself, but that
    // turns out to be unsound. In particular, despite `Field` guaranteeing that
    // `P::Inner` has a field of the given name, if we use the `addr_of!` macro
    // to perform field projection, it could still be the case that:
    // - The field is private, and so inaccessible
    // - The type implements `Deref`
    // - The `Deref::Target` type has a field of the same name
    //
    // In this case, implicit deref still happens despite our fancy `Field`
    // machinery. This is demonstrated in practice in [1].
    //
    // Here, we perform the casts manually using the associated `OFFSET` const,
    // which is not vulnerable to this issue. Note that we *could* use the
    // `OFFSET` const directly in the macro instead, but it would still not
    // allow us to support unsized types, as `offset_of!` doesn't support taking
    // the offset of unsized fields.
    //
    // [1] https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=978de749dca4f67ed24707ac049a5e4f

    let inner = unsafe { ptr.cast::<P::Inner>() };
    let field_inner = inner.project_foo::<<P as Projectable>::Inner, { NAME_HASH }>();
    unsafe { field_inner.cast() }
}

// TODO: Implement a stronger hash function so we can basically just ignore
// collisions. If users encounter collisions in practice, we can just deal with
// it then, publish a new version, and tell them to upgrade.
#[doc(hidden)]
#[must_use]
#[inline(always)]
#[allow(clippy::as_conversions, clippy::indexing_slicing, clippy::arithmetic_side_effects)]
pub const fn hash_field_name(field_name: &str) -> u128 {
    let field_name = field_name.as_bytes();
    let mut hash = 0u64;
    let mut i = 0;
    while i < field_name.len() {
        const K: u64 = 0x517cc1b727220a95;
        hash = (hash.rotate_left(5) ^ (field_name[i] as u64)).wrapping_mul(K);
        i += 1;
    }
    hash as u128
}

#[macro_export]
macro_rules! projectable {
    // It's unlikely that anyone would ever call this macro on a field-less
    // struct, but might as well support it for completeness.
    ($(#[$attr:meta])* $vis:vis struct $name:ident;) => {};
    ($(#[$attr:meta])* $vis:vis struct $name:ident {
        $($field:ident: $field_ty:ty),* $(,)?
    }) => {
        $(#[$attr])*
        $vis struct $name {
            $($field: $field_ty,)*
        }

        $(
            $crate::projectable!(@inner $name . $field: $field_ty);
        )*
    };
    ($(#[$attr:meta])* $vis:vis struct $name:ident (
        $($field_ty:ty),* $(,)?
    );) => {
        $(#[$attr])*
        $vis struct $name (
            $($field_ty,)*
        );

        // TODO: How to generate the idents `0`, `1`, etc in order to call
        // `projectable!(@inner ...)`?
    };
    (@inner $name:ident . $field:ident: $field_ty:ty) => {
        unsafe impl $crate::project::Field<{
            $crate::project::hash_field_name(stringify!($field))
        }> for $name {
            type Type = $field_ty;
            const OFFSET: isize = $crate::util::macro_util::core_reexport::mem::offset_of!($name, $field) as isize;
            // TODO: Change this if we detect `#[repr(packed)]` structs.
            type AlignmentMapping = $crate::pointer::invariant::Preserved;
        }
    };
}

#[macro_export]
macro_rules! project {
    ($outer:ident $(. $field:ident)*) => { $crate::project!(($outer) . $field) };
    (($outer:expr) . $field:ident) => {{
        let outer: &_ = $outer;
        let outer: *const _ = outer;
        let field = $crate::project::project::<_, {
            $crate::project::hash_field_name(stringify!($field))
        }>(outer);
        unsafe { &*field }
    }};
    (($outer:expr) $(. $field:ident)+) => {{
        let outer = $outer;
        $(
            let outer = project!((outer).$field);
        )+
        outer
    }};
}

#[cfg(test)]
mod tests {
    projectable! {
        struct Foo {
            a: u8,
            b: u16,
            c: u32,
        }
    }

    #[test]
    fn test_project() {
        use core::mem::ManuallyDrop;

        let f = ManuallyDrop::new(Foo { a: 0, b: 1, c: 2 });
        let p = project!((&f).c);
        assert_eq!(p, &ManuallyDrop::new(2));
    }
}
