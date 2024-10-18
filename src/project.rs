// Copyright 2024 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// NOTE: `NAME_HASH` is not semver-stable - it just needs to be consistent
// within a single compilation.
//
// TODO: `#[diagnostic::on_unimplemented]`
#[doc(hidden)]
pub unsafe trait Field<const NAME_HASH: u128> {
    type Type: ?Sized;
}

// TODO: Also add `ProjectableSized` which only supports `Of<T>` where `T:
// Sized`. Is it possible to use autoref specialization to disambiguate inside
// of `project!`?
pub unsafe trait Projectable {
    type Of<T: ?Sized>: ?Sized;
    type Inner: ?Sized;
}

unsafe impl<T: ?Sized> Projectable for core::mem::ManuallyDrop<T> {
    type Of<U: ?Sized> = core::mem::ManuallyDrop<U>;
    type Inner = T;
}

#[doc(hidden)]
#[allow(clippy::must_use_candidate)]
#[inline(never)]
pub const fn foobar<P: Projectable>(_ptr: *const P) -> *const P::Inner {
    unreachable!()
}

#[doc(hidden)]
#[allow(clippy::must_use_candidate)]
#[inline(never)]
pub const fn project_field_inference_hint<P, const NAME_HASH: u128>(
    _ptr: *const P,
) -> *const P::Of<<P::Inner as Field<{ NAME_HASH }>>::Type>
where
    P: Projectable,
    P::Inner: Field<{ NAME_HASH }>,
{
    unreachable!()
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
        }
    };
}

#[macro_export]
macro_rules! project {
    ($outer:ident $(. $field:ident)*) => { $crate::project!(($outer) . $field) };
    (($outer:expr) . $field:ident) => {{
        let outer: &_ = $outer;
        let outer: *const _ = outer;
        let field_inner = if false {
            // This branch, though never taken, ensures that the outer type
            // implements `Field<HASH>` where `HASH` is the hash of `$field`. In
            // other words, it ensures that the outer type has a field named
            // `$field`, and thus that we are not performing an implicit deref.
            //
            // TODO: Can this be broken if `$field` is private, the outer type
            // implements `Deref`, and the deref target has its own (public)
            // `$field` type?
            //
            // Yes :( https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=978de749dca4f67ed24707ac049a5e4f
            $crate::project::project_field_inference_hint::<_, {
                $crate::project::hash_field_name(stringify!($field))
            }>(outer)
        } else {
            // NOTE: The casts in this branch must be `as` casts (not `<*const
            // T>::cast`) in order to support unsized types. They must be here
            // (rather than in a `const fn` that we call from this macro
            // expansion) because, in order to support unsized types, Rust has
            // to know that the vtable kinds match, which it can't know in a
            // generic context.

            let inner = if false {
                // This branch, though never taken, ensures that `outer`'s type
                // is inferred as `*const P` where `P: Projectable`, and that
                // `inner`'s type is inferred as `*const P::Inner`.
                $crate::project::foobar(outer)
            } else {
                outer as *const _
            };
            // At this pointer, `inner: *const P::Inner`, so we can perform the
            // actual projection operation. `field_inner` has type `*const
            // <P::Inner as Field<_>>::Type`.
            let field_inner: *const _ = unsafe { $crate::util::macro_util::core_reexport::ptr::addr_of!((*inner).$field) };
            // This converts back to the wrapped type - in other words, from
            // `*const <P::Inner as Field<_>>::Type` to `*const P::Of<<P::Inner
            // as Field<_>>::Type>`.
            field_inner as *const _
        };
        unsafe { &*field_inner }
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
