// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Field projection inside of any container type.
//!
//! # How to use this module (for container users)
//!
//! Just call `project!(&a.b.c)`. It's that easy!
//!
//! Okay, maybe you want a bit more detail...
//!
//! ## The quick version
//!
//! Here's a quick, very dense explanation. If you want a friendlier
//! explanation, skip to the next section.
//!
//! Given a container type, `C`, an inner type, `I`, and a field in `I`, `f: F`,
//! if `C<I>` implements the [`Projectable`] trait, then `project!` allows you
//! to project from a `&C<I>` to a `&C<F>` which points to the `f` field within
//! the original `C<I>`. For `c: &C<I>`, this is invoked as `project!(&c.f)`.
//!
//! ## The long version
//!
//! Let's say you're using a crate which provides a container type like the
//! following:
//!
//! ```rust
//! /// An unaligned `T`.
//! ///
//! /// `Unalign<T>` has the same layout as `T`, except that its alignment
//! /// is always 1 regardless of `T`'s alignment.
//! #[repr(C, packed)]
//! pub struct Unalign<T>{
//! #    t: T,   
//! # }
//! ```
//!
//! You're using it with a type from your crate:
//!
//! ```rust
//! #[repr(C)]
//! struct UdpHeader {
//!     src_port: u16,
//!     dst_port: u16,
//!     length: u16,
//!     checksum: u16,
//! }
//! ```
//!
//! Let's say you're reading UDP packets off the network. `UdpHeader` contains
//! `u16`s, and so (on some platforms) it has an alignment of 2. But you don't
//! have any control of where your packets are stored in memory, so you can't
//! construct a `&UdpHeader` from the bytes you've received off the network.
//! Instead, you construct an `&Unalign<UdpHeader>`.
//!
//! That's all well and good, but what if you want to hand out a reference to a
//! packet's source port? It's a `u16` that might not be validly-aligned, so you
//! can't just create a `&u16` like you would be able to do if you just had a
//! `&UdpHeader`. What you'd really like to do is take your
//! `&Unalign<UdpHeader>` and take a reference to the `src_port`... and get back
//! an `&Unalign<u16>`. That's what `project!` lets you do:
//!
//! ```rust
//! # use zerocopy::project;
//! # struct UdpHeader {
//! #     src_port: u16,
//! #     dst_port: u16,
//! #     length: u16,
//! #     checksum: u16,
//! # }
//! # #[repr(C, packed)]
//! # struct Unalign<T>{
//! #    t: T,
//! # }
//! # unsafe impl<T, F> zerocopy::project::Projectable<F, Unalign<F>> for Unalign<T> {
//! #     type Inner = T;
//! # }
//! # fn read_udp_header() -> &'static Unalign<UdpHeader> { todo!() }
//! # fn __main() {
//! let packet = read_udp_header();
//! // SAFETY: We don't perform projection through any references or other
//! // fields that implement `Deref` or `DerefMut`.
//! let src_port = unsafe { project!(&packet.src_port) };
//! # }
//! ```
//!
//! # How to use this module (for container authors)
//!
//! TODO(#196): Fill this section in before removing `#[doc(hidden)]` from this
//! module.

/// A container which supports field projection of its contained type.
///
/// # Example
///
/// ```rust
/// # use zerocopy::project::Projectable;
/// #[repr(transparent)]
/// struct Wrapper<T: ?Sized>(T);
///
/// unsafe impl<T: ?Sized, F: ?Sized> Projectable<F, Wrapper<F>> for Wrapper<T> {
///     type Inner = T;
/// }
/// ```
///
/// # Safety
///
/// If `P: Projectable<F, W>`, then the following must hold:
/// - Given `p: *const P` or `p: *mut P`, it is valid to perform `let i = p as
///   *const P::Inner` or `let i = p as *mut P::Inner`. The size of the
///   referents of `p` and `i` must be identical (e.g. as reported by
///   `size_of_val_raw`).
/// - If the following hold:
///   - `p: &P` or `p: &mut P`.
///   - Given an `i: P::Inner` of size `size_of_val(p)`, there exists an `F` at
///     byte range `f` within `i`.
///
///   ...then it is sound to materialize a `&W` or `&mut W` which points to range
///   `f` within `p`.
///
/// Note that this definition holds regardless of whether `P`, `P::Inner`, or
/// `F` are sized or unsized.
///
// TODO(#196): Can we relax this safety requirement to support other types?
// E.g., what about `PhantomData`? If we can relax this requirement, it must be
// the case that, for DSTs, the prefix and tail-slice-element sizes must be the
// same (put another way, given a reference to the outer type with a certain
// number of tail elements, a reference to the inner type with the same number
// of tail elements will reference the same memory region). This is trivially
// true of the current safety requirement, but might need to be explicitly
// called out depending on how we relax that requirement.
pub unsafe trait Projectable<F: ?Sized, W: ?Sized> {
    /// The inner type.
    type Inner: ?Sized;
}

// TODO(#196): Once we expose this module in our public API (not
// `#[doc(hidden)]`), expose this for implementors to use?
macro_rules! unsafe_impl_projectable {
    ($($c:ident)::* $(: ?$sized:ident)?) => {
        unsafe impl<T $(: ?$sized)?, F $(: ?$sized)?> Projectable<F, $($c)::*<F>> for $($c)::*<T> {
            type Inner = T;
        }
    };
}

safety_comment! {
    /// SAFETY:
    /// `MaybeUninit<T>` and `Wrapping<T>` are both documented to have the same
    /// layout as `T`.
    unsafe_impl_projectable!(core::mem::MaybeUninit);
    unsafe_impl_projectable!(core::num::Wrapping);
}

/// Performs field projection on `outer`, projecting into the field of type `F`
/// at the address provided by `inner_to_field`.
///
/// # Safety
///
/// `outer_to_inner(o)` must return a pointer, `i`, which has the same address
/// as `o`. It must be the case that `size_of_val(o) == size_of_val(i)`.
///
/// `inner_to_field(i)` must return a pointer, `f`, with the following property:
/// If `i` points to a validly-initialized `P::Inner`, then `f` points to a
/// validly-initialized `F` which lives within the memory region addressed by
/// `i`. `inner_to_field` may NOT assume that `i` *does* actually point to a
/// validly-initialized `P::Inner`. `inner_to_field` may also NOT assume that
/// `i` is aligned. More specifically, `inner_to_field` may only assume that it
/// is sound to invoke `core::ptr::addr_of!(*i)`; it may not assume anything
/// that is not logically deducible from that assumption.
///
/// TODO: Maybe this safety requirement is too weak. While the "lives in the
/// same memory region" constraint is meant to prevent dereferencing inside
/// `inner_to_field`, it would technically permit dereferencing a
/// self-referential pointer - after all, it's allowed to assume that `i` points
/// to a validly-initialized `P::Inner`. What we really want to say is that `i`
/// isn't necessarily initialized, but still has the correct field offsets, but
/// how do we articulate that?
///
/// `field_to_wrapped_field(f)` must return a pointer, `w`, which has the same
/// address as `f`. It must be the case that `size_of_val(f) == size_of_val(w)`.
#[doc(hidden)]
#[inline(always)]
pub fn project<P, F, W, OuterToInner, InnerToField, FieldToWrappedField>(
    _unsafe: unsafe_token::UnsafeToken,
    outer: &P,
    outer_to_inner: OuterToInner,
    inner_to_field: InnerToField,
    field_to_wrapped_field: FieldToWrappedField,
) -> &W
where
    P: Projectable<F, W> + ?Sized,
    // TODO(#196), TODO(https://github.com/rust-lang/reference/pull/1387),
    // TODO(https://github.com/rust-lang/rust/pull/114330): Remove this bound
    // once we support unsized projection (see comment on `Unalign` for more
    // details).
    P::Inner: Sized,
    F: ?Sized,
    W: ?Sized,
    OuterToInner: FnOnce(*const P) -> *const Unalign<P::Inner>,
    InnerToField: FnOnce(*const Unalign<P::Inner>) -> *const F,
    FieldToWrappedField: FnOnce(*const F) -> *const W,
{
    let outer: *const P = outer;
    let inner = outer_to_inner(outer);
    // SAFETY: We promise to only call `inner_to_field` with a value `inner`
    // such that it is sound to call `addr_of!(*inner)`. Since this `inner` is
    // derived from a vanilla reference, it is guaranteed to be non-zero. Since
    // it is of type `*const Unalign<_>`, which is a `repr(packed)` type (and
    // thus has alignment 1), it is trivially aligned. Those are the only two
    // safety preconditions required in order to call `addr_of!(*inner)`.
    let field = inner_to_field(inner);
    let wrapped_field = field_to_wrapped_field(field);
    // SAFETY:
    // - Since `outer: *const P` is derived from the `outer` argument, which is
    //   a `&P`, `outer: *const P` points to a valid `P`.
    // - Since `P: Projectable`, `P` has the same size and field offsets as
    //   `P::Inner`.
    // - By safety precondition, `inner` points to the same memory region as
    //   `outer`. Based on the preceding premises, `inner` points to a valid
    //   `P::Inner`.
    // - By safety precondition, since `inner_to_field` is invoked with a
    //   pointer to a valid `P::Inner`, it returns a pointer to a valid `F`
    //   which lives in the same memory region. Thus, `field` points to a valid
    //   `F`. TODO: Is this actually sufficient to prove that `field` points to
    //   a valid `F`? See the TODO in the doc comment on this function.
    // - Since `P: Projectable<F, W>`, `F` has the same size and field offsets
    //   as `W`.
    // - By safety precondition, `wrapped_field` points to the same memory
    //   region as `field`, which we know points to a valid `F`. Since `F` has
    //   the same size and field offsets as `W`, `wrapped_field` also points to
    //   a valid `W`. Thus, it is sound to dereference `wrapped_field`.
    unsafe { &*wrapped_field }
}

/// Performs field projection on `outer`, projecting into the field of type `F`
/// at the address provided by `inner_to_field`.
///
/// # Safety
///
/// `project_mut` has the same safety requirements as `project`.
#[doc(hidden)]
#[inline(always)]
pub fn project_mut<P, F, W, OuterToInner, InnerToField, FieldToWrappedField>(
    _unsafe: unsafe_token::UnsafeToken,
    outer: &mut P,
    outer_to_inner: OuterToInner,
    inner_to_field: InnerToField,
    field_to_wrapped_field: FieldToWrappedField,
) -> &mut W
where
    P: Projectable<F, W> + ?Sized,
    // TODO(#196), TODO(https://github.com/rust-lang/reference/pull/1387),
    // TODO(https://github.com/rust-lang/rust/pull/114330): Remove this bound
    // once we support unsized projection (see comment on `Unalign` for more
    // details).
    P::Inner: Sized,
    F: ?Sized,
    W: ?Sized,
    OuterToInner: FnOnce(*mut P) -> *mut Unalign<P::Inner>,
    InnerToField: FnOnce(*mut Unalign<P::Inner>) -> *mut F,
    FieldToWrappedField: FnOnce(*mut F) -> *mut W,
{
    let outer: *mut P = outer;
    let inner = outer_to_inner(outer);
    let field = inner_to_field(inner);
    let wrapped_field = field_to_wrapped_field(field);
    // SAFETY: See the safety comment in `project`. The same arguments apply
    // here.
    unsafe { &mut *wrapped_field }
}

/// Performs field projection.
///
/// Given a wrapper, `w: W<T>`, and a field type in `T`, `f: F`,
/// `project!(&w.f)` returns a reference to a `W<F>` (this works for mutable
/// references too).
///
/// # Safety
///
/// It is unsound to project using a sequence of accesses that invoke
/// [`Deref::deref`] or [`DerefMut::deref_mut`].
///
/// [`Deref::deref`]: core::ops::Deref::deref
/// [`DerefMut::deref_mut`]: core::ops::DerefMut::deref_mut
// TODO(#196): Is there any way to teach Rust about when references are
// non-overlapping so you can borrow multiple fields mutably at a time?
#[doc(hidden)] // `#[macro_export]` bypasses this module's `#[doc(hidden)]`.
#[macro_export]
macro_rules! project {
    // Note that it's very important that the `mut` branches comes first! If it
    // came after the immutable branches, then a `mut` token could be matched by
    // `$c:ident` in those branches.
    (&mut $c:ident $($f:tt)*) => {
        $crate::project!(&mut ($c) $($f)*)
    };
    (&mut ($c:expr) $($f:tt)*) => {
        $crate::project!(
            @inner
            BorrowMut,
            borrow_mut,
            project_mut,
            *mut _,
            inner,
            &mut *inner,
            addr_of_mut,
            $c,
            $($f)*
        )
    };

    (&$c:ident $($f:tt)*) => {
        $crate::project!(&($c) $($f)*)
    };
    (&($c:expr) $($f:tt)*) => {
        $crate::project!(
            @inner
            Borrow,
            borrow,
            project,
            *const _,
            inner,
            &*inner,
            addr_of,
            $c,
            $($f)*
        )
    };

    (
        @inner
        $borrow_trait:ident,
        $borrow_method:ident,
        $project_fn:ident,
        $ptr_ty:ty,
        $inner_name:ident,
        $convert_inner_raw_to_ref:expr,
        $addr_of:ident,
        $c:expr,
        $($f:tt)*
    ) => {{
        // This function does nothing, but is unsafe to call, and so has the
        // effect of requiring that the caller only invoke `project!` inside of
        // an `unsafe` block.
        $crate::project::promise_no_deref();
        // We generate an `UnsafeToken` so that `$project_fn` can itself be
        // safe, and thus we don't need to put the entire call to `$project_fn`
        // in an `unsafe` block. This, in turn, is done so that the
        // meta-variables `$c` and `$($f)*` are not expanded inside of an
        // `unsafe` block, which would allow safe Rust code to smuggle in unsafe
        // code via a call to `project!` without needing to write the `unsafe`
        // keyword.
        //
        // TODO:
        // - Slicing seems to be bounds-checked at runtime if need be, but is
        //   this guaranteed by the reference/stdlib docs?
        //
        // SAFETY:
        // - The arguments passed for `outer_to_inner` and
        //   `field_to_wrapped_field` are just `as` casts, so they return
        //   pointers to the same memory region as their arguments.
        // - The argument passed for `inner_to_field` uses `addr_of!` (or
        //   `addr_of_mut!`) to take the address of a sequence of field
        //   accesses. By safety precondition of this macro, none of those field
        //   accesses can go through a dereference. The only other types of
        //   field accesses produce "places" which live entirely within the
        //   memory region of the argument to `inner_to_field` as required by
        //   the safety precondition of `project`/`project_mut`.
        //
        // Some older versions of Clippy have a bug in which they don't
        // recognize the preceding safety comment.
        #[allow(clippy::undocumented_unsafe_blocks)]
        #[allow(unused_unsafe)]
        let token = unsafe { $crate::project::unsafe_token::UnsafeToken::new() };
        use ::core::borrow::$borrow_trait as _;
        $crate::project::$project_fn(
            token,
            // We call `borrow` or `borrow_mut` so that this macro works
            // regardless of whether `$c` is owned or borrowed.
            //
            // TODO(#196): Is there any way to make sure this calls
            // `Borrow::borrow` or `BorrowMut::borrow_mut` even if the type has
            // an inherent method of the same name?
            $c.$borrow_method(),
            // Older versions of Clippy complain about this `as` cast; newer
            // versions seem to know it's okay.
            #[allow(clippy::as_conversions)]
            |outer| outer as $ptr_ty,
            |inner| if false {
                // This branch is never executed, but allows us to ensure that
                // `$($f)*` doesn't contain any unsafe code that isn't wrapped
                // in an `unsafe` block. If it does, then wrapping it in
                // `unsafe` - as we do in the `else` branch - would allow users
                // to write unsafe code without needing to write `unsafe`.
                //
                // The way we accomplish this is to generate a reference from
                // `inner` (which is a raw pointer). That allows us to extract
                // the unsafe operation of converting to a reference and wrap it
                // in an `unsafe` block on its own, while leaving the `$($f)*`
                // not wrapped in an `unsafe` block. Note that this is NOT sound
                // to execute in the general case, but that's okay because we're
                // in an `if false` branch. For example, if the wrapper type is
                // `#[repr(packed)]`, then `inner_ref` may not be validly
                // aligned, which is unsound.
                let $inner_name = inner;
                // SAFETY: This code is never executed.
                //
                // Some older versions of Clippy have a bug in which they don't
                // recognize the preceding safety comment.
                #[allow(clippy::undocumented_unsafe_blocks)]
                #[allow(unused_unsafe)]
                let inner_ref = unsafe { $convert_inner_raw_to_ref };
                ::core::ptr::$addr_of!(inner_ref .0 $($f)*)
            } else {
                // SAFETY: By safety invariant of `project`/project_mut`, it is
                // sound to call `addr_of!`/`addr_of_mut!` on `*inner`. By
                // safety precondition of this macro, none of the field accesses
                // go through a dereference, and so no loads are generated.
                // Thus, even if `inner` does not point to a validly-initialized
                // value, this call is still sound.
                //
                // Some older versions of Clippy have a bug in which they don't
                // recognize the preceding safety comment.
                #[allow(clippy::undocumented_unsafe_blocks)]
                #[allow(unused_unsafe)]
                unsafe { ::core::ptr::$addr_of!((*inner) .0 $($f)* ) }
            },
            // Older versions of Clippy complain about this `as` cast; newer
            // versions seem to know it's okay.
            #[allow(clippy::as_conversions)]
            |field| field as $ptr_ty,
        )
    }};
}

#[doc(hidden)]
#[inline(always)]
pub const unsafe fn promise_no_deref() {}

// TODO(#196), TODO(https://github.com/rust-lang/reference/pull/1387),
// TODO(https://github.com/rust-lang/rust/pull/114330): Remove this once it is
// no longer UB to use `addr_of!` with an unaligned pointer, and once Miri knows
// that this isn't UB. Note that this struct is the only reason that `project!`
// doesn't support unsized types, so removing this will also address that
// limitation.
#[allow(missing_debug_implementations)]
#[doc(hidden)]
#[repr(packed)]
pub struct Unalign<T>(pub T);

#[doc(hidden)]
pub mod unsafe_token {
    /// A token used to prove that the `unsafe` keyword has been written
    /// somewhere.
    #[allow(missing_copy_implementations, missing_debug_implementations)]
    pub struct UnsafeToken(());

    impl UnsafeToken {
        /// Constructs a new `UnsafeToken`.
        ///
        /// # Safety
        ///
        /// The caller is responsible for ensuring that they uphold the safety
        /// invariants of any APIs which consume this token.
        pub unsafe fn new() -> UnsafeToken {
            UnsafeToken(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Copy)]
    #[repr(C, packed)]
    struct Unalign<T>(T);

    safety_comment! {
        /// SAFETY:
        /// `Unalign<T>` has the same layout as `T`.
        unsafe_impl_projectable!(Unalign);
    }

    impl<T: Copy> Clone for Unalign<T> {
        fn clone(&self) -> Unalign<T> {
            *self
        }
    }

    #[derive(Eq, PartialEq, Debug)]
    #[repr(transparent)]
    struct Wrapper<T: ?Sized>(T);
    safety_comment! {
        /// SAFETY:
        /// `Wrapper<T>` has the same layout as `T`.
        unsafe_impl_projectable!(Wrapper: ?Sized);
    }

    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    struct Foo<T> {
        a: u8,
        b: u16,
        c: T,
    }

    macro_rules! test_project {
        (($c:ident $($f:tt)*) => $expect:expr) => {{
            // SAFETY: None of the tests in this module use fields which
            // implement `Deref` or `DerefMut`.
            //
            // Some older versions of Clippy have a bug in which they don't
            // recognize the preceding safety comment.
            #[allow(clippy::undocumented_unsafe_blocks)]
            #[allow(unused_unsafe)]
            unsafe {
                // Test with an immutable reference.
                let f = project!(&$c $($f)*);
                assert_eq!({ f.0 }, $expect);
                // Test with a mutable reference.
                let f = project!(&mut $c $($f)*);
                assert_eq!({ f.0 }, $expect);

                // Run the same tests with `$c` in parentheses.
                test_project!((($c) $($f)*) => $expect);
            }
        }};
        ((($c:expr) $($f:tt)*) => $expect:expr) => {{
            // SAFETY: None of the tests in this module use fields which
            // implement `Deref` or `DerefMut`.
            //
            // Some older versions of Clippy have a bug in which they don't
            // recognize the preceding safety comment.
            #[allow(clippy::undocumented_unsafe_blocks)]
            #[allow(unused_unsafe)]
            unsafe {
                // Test with an immutable reference.
                let f = project!(&($c) $($f)*);
                assert_eq!({ f.0 }, $expect);
                // Test with a mutable reference.
                let f = project!(&mut ($c) $($f)*);
                assert_eq!({ f.0 }, $expect);
            }
        }};
    }

    #[test]
    fn test_project() {
        let mut u = Unalign(Foo::<u32> { a: 1, b: 2, c: 3 });

        test_project!((u.a) => 1);
        test_project!((u.b) => 2);
        test_project!((u.c) => 3);
    }

    #[test]
    fn test_project_complex() {
        // Test projection using a complex expression rather than just the
        // identifier of a local variable.

        let mut u = Unalign(Foo::<u32> { a: 1, b: 2, c: 3 });

        fn ident<T>(t: T) -> T {
            t
        }

        // SAFETY: None of these projections go through a field which implements
        // `Deref` or `DerefMut`.
        unsafe {
            let ua = project!(&(ident(&u)).a);
            let ub = project!(&(ident(&u)).b);
            assert_eq!({ ua.0 }, 1);
            assert_eq!({ ub.0 }, 2);

            let uc = project!(&mut (ident(&mut u)).c);
            assert_eq!({ uc.0 }, 3);
        }
    }

    #[test]
    fn test_project_complex_access() {
        let mut u = Unalign(Foo::<Foo<u32>> { a: 1, b: 2, c: Foo { a: 3, b: 4, c: 5 } });
        test_project!((u.c) => Foo { a: 3, b: 4, c: 5 });
        test_project!((u.c.a) => 3);

        let mut u = Unalign(Foo::<[u32; 3]> { a: 1, b: 2, c: [3, 4, 5] });
        test_project!((u.c) => [3, 4, 5]);
        test_project!((u.c[0]) => 3);

        let mut u = Unalign([0u8, 1, 2]);
        test_project!((u[0]) => 0);
        test_project!((u[1]) => 1);
        test_project!((u[2]) => 2);

        // Test that indexing works using variables rather than literals.
        for i in 0u8..3 {
            test_project!((u[usize::from(i)]) => i);
        }

        let mut u = Unalign([[0u8, 1, 2], [3, 4, 5], [6, 7, 8]]);
        test_project!((u[0][0]) => 0);
        test_project!((u[1][1]) => 4);
        test_project!((u[2][2]) => 8);

        // Test that indexing works using variables rather than literals.
        for (i, elem) in [(0usize, 0u8), (1, 4), (2, 8)] {
            test_project!((u[i][i]) => elem);
        }
    }

    // TODO(#196), TODO(https://github.com/rust-lang/reference/pull/1387),
    // TODO(https://github.com/rust-lang/rust/pull/114330): Uncomment this once
    // unsized projection is supported.
    //
    // #[test]
    // fn test_project_unsized() {
    //     let inner = [0u8, 1, 2];
    //     let inner_ref: &[u8] = &inner[..];
    //     let wrapper_ref: &Wrapper<([u8],)> = unsafe { &*(inner_ref as *const _ as *const _) };

    //     let first = project!(&wrapper_ref.0[1]);
    //     assert_eq!(first, &Wrapper(1u8));
    //     let first_two = project!(&wrapper_ref.0[0..2]);
    //     assert_eq!(&first_two.0, &[0, 1]);
    // }

    #[test]
    #[should_panic(expected = "index out of bounds: the len is 3 but the index is 3")]
    fn test_project_out_of_bounds() {
        let u = Unalign([0u8, 1, 2]);

        // SAFETY: None of these projections go through a field which implements
        // `Deref` or `DerefMut`.
        unsafe {
            let u0 = project!(&u[0]);
            assert_eq!({ u0.0 }, 0);
            let _ = project!(&u[3]);
        }
    }

    #[test]
    #[should_panic(expected = "index out of bounds: the len is 3 but the index is 3")]
    fn test_project_out_of_bounds_variable() {
        let u = Unalign([0u8, 1, 2]);

        // SAFETY: None of these projections go through a field which implements
        // `Deref` or `DerefMut`.
        unsafe {
            let u0 = project!(&u[0]);
            assert_eq!({ u0.0 }, 0);
            let i = 3;
            let _ = project!(&u[i]);
        }
    }

    #[test]
    #[should_panic(expected = "range end index 4 out of range for slice of length 3")]
    fn test_project_out_of_bounds_range() {
        let u = Wrapper([0u8, 1, 2]);

        // SAFETY: None of these projections go through a field which implements
        // `Deref` or `DerefMut`.
        unsafe {
            let u0 = project!(&u[0]);
            assert_eq!({ u0.0 }, 0);
            // Good catch, Clippy! But we do need to be able to test this, so
            // shhh....
            #[allow(clippy::out_of_bounds_indexing)]
            let _ = project!(&u[0..4]);
        }
    }
}
