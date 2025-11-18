// Copyright 2025 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! In-place initialization.
//!
//! # Examples
//!
//! ```
//! # use zerocopy_derive::*;
//! # use zerocopy::{init::*, init};
//! # use core::mem::MaybeUninit;
//! #[derive(Inhabited, Eq, PartialEq, Debug)]
//! struct Bar {
//!     a: u8,
//!     b: u16,
//!     c: u32,
//! }
//!
//! let mut storage = MaybeUninit::<Bar>::uninit();
//! let bar = storage.init(|p| {
//!     let p = init!(p.a, 0);
//!     let p = init!(p.b, 1);
//!     init!(p.c, 2)
//! });
//! assert_eq!(bar, &Bar { a: 0, b: 1, c: 2 });
//!
//! let mut boxed = Box::<Bar>::new_uninit();
//! let bar = boxed.init(|p| {
//!     let p = init!(p.a, 0);
//!     let p = init!(p.b, 1);
//!     init!(p.c, 2)
//! });
//! assert_eq!(&*bar, &Bar { a: 0, b: 1, c: 2 });
//!
//! let mut storage = MaybeUninit::<[(u8, u16); 3]>::uninit();
//! let arr = storage.init(|p| {
//!     // Initialize the .0 field of each tuple
//!     let p = p.init_each(|p, prefix| init!(p.0, prefix.len() as u8));
//!     // Initialize the .1 field of each tuple
//!     p.init_each(|p, prefix| init!(p.1, prefix.len() as u16))
//! });
//! assert_eq!(arr, &[(0u8, 0u16), (1, 1), (2, 2)]);
//!
//! #[derive(Inhabited, Eq, PartialEq, Debug)]
//! struct Baz(u8, Bar);
//!
//! let mut storage = MaybeUninit::<Baz>::uninit();
//! let baz = storage.init(|p| {
//!     let p = init!(p.0, 0);
//!     let p = init!(p.1.a, 1);
//!     let p = init!(p.1.b, |p| p.init(2));
//!     init!(p.1.c, move |p| p.init(3))
//! });
//! assert_eq!(baz, &Baz(0, Bar { a: 1, b: 2, c: 3 }));
//! ```

#[cfg(feature = "alloc")]
use alloc::boxed::Box;
use core::{
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr::{addr_of_mut, NonNull},
};

// TODO: If we end up deriving `Inhabited` on enum types by setting `Init =
// Init` and `Uninit = Uninit`, change these doc comments – as it will no longer
// be the case that only primitive types use these.

/// The state of a [`PartiallyUninit<T>`] which is entirely uninitialized, where
/// `T` is a primitive type.
#[derive(Copy, Clone, Debug)]
#[doc(hidden)]
pub enum Uninit {}

/// The state of a [`PartiallyUninit<T>`] which is entirely initialized, where
/// `T` is a primitive type.
#[derive(Copy, Clone, Debug)]
#[doc(hidden)]
pub enum Init {}

// TODO: How to make the custom derive also gated by the `init-unstable`
// feature? That will matter once we add a `TryFromBytes: Inhabited` super-trait
// bound.

/// Types that have values.
///
/// Any "inhabited" type – that is, any type which can be constructed at runtime
/// – can implement `Inhabited`.
///
/// TODO: Warning about deriving rather than manually implementing this trait.
pub unsafe trait Inhabited {
    /// The state of a [`PartiallyUninit<Self>`] which is entirely uninitialized.
    ///
    /// See the [`PartiallyUninit`] docs for more information.
    type Uninit;

    // /// The state of a [`PartiallyUninit<Self>`] which is entirely initialized.
    // ///
    // /// A [`PartiallyUninit<Self, Self::Init>`] can be converted into a `&mut
    // /// Self` using [`PartiallyUninit::into_mut`].
    // ///
    // /// See the [`PartiallyUninit`] docs for more information.
    // type Init;
}

/// States for which `Self` is initialized.
///
/// # Safety
///
/// `T: Initialized<S>` if [`PartiallyUninit<'_, T, S>`] points to a bit-valid
/// `T`.
pub unsafe trait Initialized<S: ?Sized> {}

// unsafe impl<T: ?Sized> Initialized<Init> for T {}

macro_rules! impl_foo_for_primitive {
    ($($ty:ty),*) => {
        $(
            unsafe impl Inhabited for $ty {
                type Uninit = Uninit;
                // type Init = Init;
            }

            unsafe impl Initialized<Init> for $ty {}
        )*
    };
}

impl_foo_for_primitive!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, f32, f64, char, bool
);

macro_rules! impl_foo_for_tuple {
    ($(($($tyvar:ident: $init_tyvar:ident),* $(,)?)),*) => {
        $(
            unsafe impl<$($tyvar: Inhabited),*> Inhabited for ($($tyvar,)*) {
                type Uninit = ($($tyvar::Uninit,)*);
                // type Init = ($($tyvar::Init,)*);
            }

            unsafe impl<$($tyvar),*> Initialized<Init> for ($($tyvar,)*) {}

            unsafe impl<$($tyvar, $init_tyvar),*> Initialized<($($init_tyvar,)*)> for ($($tyvar,)*)
            where
                $($tyvar: Initialized<$init_tyvar>),*
            {}
        )*
    };
}

impl_foo_for_tuple!(
    (A: AI,),
    (A: AI, B: BI),
    (A: AI, B: BI, C: CI),
    (A: AI, B: BI, C: CI, D: DI),
    (A: AI, B: BI, C: CI, D: DI, E: EI),
    (A: AI, B: BI, C: CI, D: DI, E: EI, F: FI),
    (A: AI, B: BI, C: CI, D: DI, E: EI, F: FI, G: GI),
    (A: AI, B: BI, C: CI, D: DI, E: EI, F: FI, G: GI, H: HI),
    (A: AI, B: BI, C: CI, D: DI, E: EI, F: FI, G: GI, H: HI, I: II),
    (A: AI, B: BI, C: CI, D: DI, E: EI, F: FI, G: GI, H: HI, I: II, J: JI),
    (A: AI, B: BI, C: CI, D: DI, E: EI, F: FI, G: GI, H: HI, I: II, J: JI, K: KI),
    (A: AI, B: BI, C: CI, D: DI, E: EI, F: FI, G: GI, H: HI, I: II, J: JI, K: KI, L: LI)
);

unsafe impl<T: Inhabited> Inhabited for [T] {
    type Uninit = T::Uninit;
    // type Init = [T::Init];
}

unsafe impl<I, T: Initialized<I>> Initialized<I> for [T] {}

unsafe impl<T: Inhabited, const N: usize> Inhabited for [T; N] {
    type Uninit = T::Uninit;
    // type Init = [T::Init; N];
}

unsafe impl<I, T: Initialized<I>, const N: usize> Initialized<I> for [T; N] {}

// TODO: Does this need to be invariant in `'a` in order to prevent smuggling/swapping?

/// A reference to a `T` which may not be fully initialized.
///
/// `S` tracks the initialization state of the referent. If `T: Initialized<S>`,
/// then the referent is a fully initialized, bit-valid `T`.
pub struct PartiallyUninit<'a, T: ?Sized, S: ?Sized> {
    // NOTE: We use `NonNull<T>` instead of `&'a mut MaybeUninit<T>` because
    // `MaybeUninit<T>` requires `T: Sized`.
    ptr: NonNull<T>,
    _marker: PhantomData<&'a S>,
}

impl<'a, T: ?Sized, I: ?Sized> PartiallyUninit<'a, T, I> {
    unsafe fn new(ptr: NonNull<T>) -> PartiallyUninit<'a, T, I> {
        PartiallyUninit { ptr, _marker: PhantomData }
    }

    unsafe fn assume_state<J: ?Sized>(self) -> PartiallyUninit<'a, T, J> {
        PartiallyUninit { ptr: self.ptr, _marker: PhantomData }
    }

    #[inline(always)]
    #[doc(hidden)]
    pub fn init_field<const VARIANT_HASH: u128, const FIELD_HASH: u128, FieldInitOut>(
        p: Self,
        init: impl for<'b> FnOnce(
            PartiallyUninit<'b, T::Type, T::FieldInit>,
        ) -> PartiallyUninit<'b, T::Type, FieldInitOut>,
    ) -> PartiallyUninit<'a, T, T::Overwrite<FieldInitOut>>
    where
        I: State,
        T: HasField<VARIANT_HASH, FIELD_HASH, I>,
    {
        // NOTE: This is a no-op if `I` guarantees that we've already
        // initialized the tag.
        unsafe { T::init_tag(p.ptr) };

        let field_ptr = T::project(p.ptr);
        let _ = init(unsafe { PartiallyUninit::new(field_ptr) });

        // SAFETY:
        unsafe { p.assume_state() }
    }
}

// TODO: Consider adding the option to one-shot initialize from an arbitrary
// state by zeroing any as-yet uninitialized fields (assuming T: FromZeros for
// all field types, T).

#[allow(variant_size_differences)]
enum Foo {
    A(u8, u16),
    B { u: u32, v: u64 },
}

struct __Foo_A;
struct __Foo_B;

unsafe impl<A, B> Initialized<(__Foo_A, A, B)> for Foo
where
    u8: Initialized<A>,
    u16: Initialized<B>,
{
}

unsafe impl<A, B> Initialized<(__Foo_B, A, B)> for Foo
where
    u32: Initialized<A>,
    u64: Initialized<B>,
{
}

// TODO: Is it possible to reduce duplication of `HasField` impls?

unsafe impl HasField<{ macro_util::hash_name("A") }, 0, Uninit> for Foo {
    type Type = u8;

    type FieldInit = Uninit;
    type Overwrite<This> = (__Foo_A, (This, Uninit));

    fn project(outer: NonNull<Self>) -> NonNull<Self::Type> {
        todo!()
    }

    unsafe fn init_tag(outer: NonNull<Self>) {
        // TODO: Initialize to `A` tag
        todo!()
    }
}

unsafe impl<I: State> HasField<{ macro_util::hash_name("A") }, 0, (__Foo_A, I)> for Foo {
    type Type = u8;

    type FieldInit = I::Index0;
    type Overwrite<This> = (__Foo_A, I::Replace0<This>);

    fn project(outer: NonNull<Self>) -> NonNull<Self::Type> {
        todo!()
    }

    // NOTE: Intentionally doing nothing – the incoming initialization state
    // guarantees that the tag is already initialized.
    unsafe fn init_tag(_outer: NonNull<Self>) {}
}

unsafe impl HasField<{ macro_util::hash_name("A") }, 1, Uninit> for Foo {
    type Type = u16;

    type FieldInit = Uninit;
    type Overwrite<This> = (__Foo_A, (Uninit, This));

    fn project(outer: NonNull<Self>) -> NonNull<Self::Type> {
        todo!()
    }

    unsafe fn init_tag(outer: NonNull<Self>) {
        // TODO: Initialize to `A` tag
        todo!()
    }
}

unsafe impl<I: State> HasField<{ macro_util::hash_name("A") }, 1, (__Foo_A, I)> for Foo {
    type Type = u16;

    type FieldInit = I::Index1;
    type Overwrite<This> = (__Foo_A, I::Replace1<This>);

    fn project(outer: NonNull<Self>) -> NonNull<Self::Type> {
        todo!()
    }

    // NOTE: Intentionally doing nothing – the incoming initialization state
    // guarantees that the tag is already initialized.
    unsafe fn init_tag(_outer: NonNull<Self>) {}
}

unsafe impl HasField<{ macro_util::hash_name("B") }, { macro_util::hash_name("u") }, Uninit>
    for Foo
{
    type Type = u32;

    type FieldInit = Uninit;
    type Overwrite<This> = (__Foo_B, (This, Uninit));

    fn project(outer: NonNull<Self>) -> NonNull<Self::Type> {
        todo!()
    }

    unsafe fn init_tag(outer: NonNull<Self>) {
        // TODO: Initialize to `A` tag
        todo!()
    }
}

unsafe impl<I: State>
    HasField<{ macro_util::hash_name("B") }, { macro_util::hash_name("u") }, (__Foo_B, I)> for Foo
{
    type Type = u32;

    type FieldInit = I::Index0;
    type Overwrite<This> = (__Foo_B, I::Replace0<This>);

    fn project(outer: NonNull<Self>) -> NonNull<Self::Type> {
        todo!()
    }

    // NOTE: Intentionally doing nothing – the incoming initialization state
    // guarantees that the tag is already initialized.
    unsafe fn init_tag(_outer: NonNull<Self>) {}
}

unsafe impl HasField<{ macro_util::hash_name("B") }, { macro_util::hash_name("v") }, Uninit>
    for Foo
{
    type Type = u64;

    type FieldInit = Uninit;
    type Overwrite<This> = (__Foo_B, (Uninit, This));

    fn project(outer: NonNull<Self>) -> NonNull<Self::Type> {
        todo!()
    }

    unsafe fn init_tag(outer: NonNull<Self>) {
        // TODO: Initialize to `A` tag
        todo!()
    }
}

unsafe impl<I: State>
    HasField<{ macro_util::hash_name("B") }, { macro_util::hash_name("v") }, (__Foo_B, I)> for Foo
{
    type Type = u64;

    type FieldInit = I::Index1;
    type Overwrite<This> = (__Foo_B, I::Replace1<This>);

    fn project(outer: NonNull<Self>) -> NonNull<Self::Type> {
        todo!()
    }

    // NOTE: Intentionally doing nothing – the incoming initialization state
    // guarantees that the tag is already initialized.
    unsafe fn init_tag(_outer: NonNull<Self>) {}
}

impl<'a, T: Inhabited> PartiallyUninit<'a, T, T::Uninit> {
    fn from_maybe_uninit(mu: &'a mut MaybeUninit<T>) -> PartiallyUninit<'a, T, T::Uninit> {
        unsafe { PartiallyUninit::new(NonNull::from(mu).cast()) }
    }
}

impl<'a, const N: usize, T, I> PartiallyUninit<'a, [T; N], I> {
    #[inline(always)]
    fn into_slice(self) -> PartiallyUninit<'a, [T], I> {
        unsafe { PartiallyUninit::new(NonNull::slice_from_raw_parts(self.ptr.cast(), N)) }
    }

    #[inline(always)]
    pub fn init_each<O>(
        self,
        init_elem: impl for<'b> FnMut(
            PartiallyUninit<'b, T, I>,
            PartiallyUninit<'a, [T], O>,
        ) -> PartiallyUninit<'b, T, O>,
    ) -> PartiallyUninit<'a, [T; N], O>
    where
        T: Inhabited,
    {
        let ptr = self.ptr;
        self.into_slice().init_each(init_elem);
        unsafe { PartiallyUninit::new(ptr) }
    }
}

impl<'a, T, I> PartiallyUninit<'a, [T], I> {
    #[must_use]
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.ptr.len()
    }

    #[must_use]
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline(always)]
    pub fn init_each<O>(
        self,
        mut init_elem: impl for<'b> FnMut(
            PartiallyUninit<'b, T, I>,
            PartiallyUninit<'a, [T], O>,
        ) -> PartiallyUninit<'b, T, O>,
    ) -> PartiallyUninit<'a, [T], O>
    where
        T: Inhabited,
    {
        let data = self.ptr.cast::<T>();
        let len = self.ptr.len();

        for i in 0..len {
            let prefix = unsafe { PartiallyUninit::new(NonNull::slice_from_raw_parts(data, i)) };
            let cur = unsafe { self.ptr.get_unchecked_mut(i) };
            let cur = unsafe { PartiallyUninit::new(cur) };
            let _ = init_elem(cur, prefix);
        }

        unsafe { self.assume_state() }
    }
}

impl<'a, T: ?Sized + Inhabited> PartiallyUninit<'a, T, T::Uninit> {
    // NOTE: It's fine to have this take a `self` receiver rather than `p: Self`
    // because the initialization type is `T::Uninit`, so this won't `Deref`.
    //
    // TODO: Maybe put back the associated `Init` type on `Inhabited` so we can
    // use it here (ie, `T::Init`) instead of `Init`? That will save us from the
    // weirdness of doing `Initialized<[I]> for [T]` and `Initialized<[I; N]>
    // for [T; N]`.
    #[inline(always)]
    pub fn init(self, t: T) -> PartiallyUninit<'a, T, Init>
    where
        T: Sized,
    {
        unsafe { self.ptr.write(t) };
        unsafe { self.assume_state() }
    }
}

impl<'a, I: ?Sized, T: ?Sized + Inhabited + Initialized<I>> PartiallyUninit<'a, T, I> {
    #[inline(always)]
    #[must_use]
    pub fn into_mut(mut p: Self) -> &'a mut T {
        unsafe { p.ptr.as_mut() }
    }
}

impl<'a, I: ?Sized, T: ?Sized + Inhabited + Initialized<I>> Deref for PartiallyUninit<'a, T, I> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<'a, I: ?Sized, T: ?Sized + Inhabited + Initialized<I>> DerefMut for PartiallyUninit<'a, T, I> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

#[doc(hidden)]
pub unsafe trait HasField<const VARIANT_HASH: u128, const FIELD_HASH: u128, I: ?Sized> {
    type Type;
    // TODO: Thanks to GAT, this won't work on our MSRV. We'll want to version
    // gate this on the toolchain version that stabilized GATs.

    // Given an initialization of the entire outer type, extract the
    // initialization of just this field.
    type FieldInit; //<OuterInit: State>;
                    // Given an original initialization of the entire outer type and a new
                    // initialization of just this field, produce a new initialization of the
                    // entire outer type.
    type Overwrite<This>; //<OuterInit: State, This>;

    // TODO: Does this need to be unsafe?
    fn project(outer: NonNull<Self>) -> NonNull<Self::Type>;

    unsafe fn init_tag(outer: NonNull<Self>);
}

#[macro_export]
#[doc(hidden)]
macro_rules! init {
    // Distinguish between a closure and a value by matching on the closure
    // literal syntax. It'd be ideal to instead support this via trait, but I've
    // been unable to get that to work. Here's a (minified) example of the
    // failure:
    // https://play.rust-lang.org/?version=stable&mode=debug&edition=2024&gist=cf37f1bb738aeae864f3c444fd24ac08

    ($p:tt . $first_field:tt $(. $rest_fields:tt)+, $($move:ident)? |$pp:ident $(: $ty:ty)?| $body:expr) => {
        init!(@inner $p . $first_field, move |p| {
            init!(p $(. $rest_fields)+, $($move)? |$pp $(: $ty)?| $body)
        })
    };
    ($p:tt . $first_field:tt $(. $rest_fields:tt)+, $val:expr) => {
        init!(@inner $p . $first_field, move |p| {
            init!(p $(. $rest_fields)+, $val)
        })
    };

    ($p:tt . $field:tt, $($move:ident)? |$pp:ident $(: $ty:ty)?| $body:expr) => {
        init!(@inner $p . $field, $($move)? |$pp $(: $ty)?| $body)
    };
    ($p:tt . $field:tt, $val:expr) => {
        init!(@inner $p . $field, move |p| PartiallyUninit::init(p, $val))
    };

    (@inner $p:tt . $field:ident, $init:expr) => {
        PartiallyUninit::init_field::<0, { $crate::init::macro_util::hash_name(stringify!($field)) }, _>(
            $p, $init,
        )
    };
    (@inner $p:tt . $field:literal, $init:expr) => {
        PartiallyUninit::init_field::<0, $field, _>(
            $p, $init,
        )
    };
}

/// Pointers that reference uninitialized memory.
pub trait Storage: DerefMut<Target = MaybeUninit<Self::Inner>> {
    /// The type of the referent of [`Self::Initialized`].
    type Inner: Inhabited;

    /// The ultimate type of the initialized pointer to [`Self::Initialized`].
    type Initialized;

    /// Attests that the storage's referent is initialized.
    ///
    /// # Safety
    ///
    /// The caller promises that `s.deref_mut()` has been initialized to a
    /// bit-valid [`Self::Inner`]. `assume_init` promises to return a pointer
    /// which addresses the same bytes as `s`.
    ///
    /// Note that it is not immediately unsound to invoke this method when the
    /// referent is a bit-valid but not a library-valid instance of
    /// [`Self::Inner`], however subsequent uses of the returned pointer may be
    /// unsound.
    #[doc(hidden)]
    unsafe fn assume_init(s: Self) -> Self::Initialized;

    /// Incrementally initializes this allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// # use zerocopy_derive::*;
    /// use zerocopy::{init::*, init};
    /// use core::mem::MaybeUninit;
    ///
    /// #[derive(Inhabited, Eq, PartialEq, Debug)]
    /// struct Bar {
    ///     a: u8,
    ///     b: u16,
    ///     c: u32,
    /// }
    ///
    /// let mut storage = MaybeUninit::<Bar>::uninit();
    /// let bar = storage.init(|p| {
    ///     let p = init!(p.a, 0);
    ///     let p = init!(p.b, 1);
    ///     init!(p.c, 2)
    /// });
    ///
    /// assert_eq!(bar, &Bar { a: 0, b: 1, c: 2 });
    /// ```
    // TODO: Figure out how to remove the Sized bound (e.g. by using KnownLayout
    // and our MaybeUninit polyfill).
    #[inline(always)]
    fn init<I>(
        mut self,
        init: impl for<'a> FnOnce(
            PartiallyUninit<'a, Self::Inner, <Self::Inner as Inhabited>::Uninit>,
        ) -> PartiallyUninit<'a, Self::Inner, I>,
    ) -> Self::Initialized
    where
        Self: Sized,
        Self::Inner: Initialized<I>,
    {
        init(PartiallyUninit::from_maybe_uninit(&mut *self));
        unsafe { Self::assume_init(self) }
    }
}

impl<'a, T: Inhabited> Storage for &'a mut MaybeUninit<T> {
    type Inner = T;
    type Initialized = &'a mut T;

    #[inline(always)]
    unsafe fn assume_init(p: Self) -> &'a mut T {
        let p: *mut MaybeUninit<T> = p;
        unsafe { &mut *p.cast::<T>() }
    }
}

#[cfg(feature = "alloc")]
impl<T: Inhabited> Storage for Box<MaybeUninit<T>> {
    type Inner = T;
    type Initialized = Box<T>;

    #[inline(always)]
    unsafe fn assume_init(p: Self) -> Box<T> {
        let inner = Box::into_raw(p);
        unsafe { Box::from_raw(inner.cast::<T>()) }
    }
}

#[doc(hidden)]
pub mod macro_util {
    // NOTE(#2749) on hash collisions: This function's output only needs to be
    // deterministic within a particular compilation. Thus, if a user ever
    // reports a hash collision (very unlikely given the <= 16-byte special
    // case), we can strengthen the hash function at that point and publish a
    // new version. Since this is computed at compile time on small strings, we
    // can easily use more expensive and higher-quality hash functions if need
    // be.
    #[inline(always)]
    #[must_use]
    #[allow(clippy::as_conversions, clippy::indexing_slicing, clippy::arithmetic_side_effects)]
    pub const fn hash_name(name: &str) -> u128 {
        let name = name.as_bytes();

        // We guarantee freedom from hash collisions between any two strings of
        // length 16 or less by having the hashes of such strings be equal to
        // their value. There is still a possibility that such strings will have
        // the same value as the hash of a string of length > 16.
        if name.len() <= size_of::<u128>() {
            let mut bytes = [0u8; 16];

            let mut i = 0;
            while i < name.len() {
                bytes[i] = name[i];
                i += 1;
            }

            return u128::from_ne_bytes(bytes);
        };

        // An implementation of FxHasher, although returning a u128. Probably
        // not as strong as it could be, but probably more collision resistant
        // than normal 64-bit FxHasher.
        let mut hash = 0u128;
        let mut i = 0;
        while i < name.len() {
            // This is just FxHasher's `0x517cc1b727220a95` constant
            // concatenated back-to-back.
            const K: u128 = 0x517cc1b727220a95517cc1b727220a95;
            hash = (hash.rotate_left(5) ^ (name[i] as u128)).wrapping_mul(K);
            i += 1;
        }
        hash
    }
}

pub use tuple::State;
#[doc(hidden)]
mod tuple {
    use core::convert::Infallible as Never;

    trait Sealed {}

    /// A marker for initialization states.
    pub trait State: Sealed {
        /// The state of the 1st field.
        type Index0;

        /// The state of the 2nd field.
        type Index1;

        /// The state of the 3rd field.
        type Index2;

        /// The state of the 4th field.
        type Index3;

        /// The state of the 5th field.
        type Index4;

        /// The state of the 6th field.
        type Index5;

        /// The state of the 7th field.
        type Index6;

        /// The state of the 8th field.
        type Index7;

        /// The state of the 9th field.
        type Index8;

        /// The state of the 10th field.
        type Index9;

        /// The state of the 11th field.
        type Index10;

        /// The state of the 12th field.
        type Index11;

        /// The state after replacing the state of the 1st field with `S`.
        type Replace0<S>;

        /// The state after replacing the state of the 2nd field with `S`.
        type Replace1<S>;

        /// The state after replacing the state of the 3rd field with `S`.
        type Replace2<S>;

        /// The state after replacing the state of the 4th field with `S`.
        type Replace3<S>;

        /// The state after replacing the state of the 5th field with `S`.
        type Replace4<S>;

        /// The state after replacing the state of the 6th field with `S`.
        type Replace5<S>;

        /// The state after replacing the state of the 7th field with `S`.
        type Replace6<S>;

        /// The state after replacing the state of the 8th field with `S`.
        type Replace7<S>;

        /// The state after replacing the state of the 9th field with `S`.
        type Replace8<S>;

        /// The state after replacing the state of the 10th field with `S`.
        type Replace9<S>;

        /// The state after replacing the state of the 11th field with `S`.
        type Replace10<S>;

        /// The state after replacing the state of the 12th field with `S`.
        type Replace11<S>;
    }

    // --- Implementations (1-12) ---

    impl<A> Sealed for (A,) {}

    impl<A> State for (A,) {
        type Index0 = A;
        type Index1 = Never;
        type Index2 = Never;
        type Index3 = Never;
        type Index4 = Never;
        type Index5 = Never;
        type Index6 = Never;
        type Index7 = Never;
        type Index8 = Never;
        type Index9 = Never;
        type Index10 = Never;
        type Index11 = Never;

        type Replace0<X> = (X,);
        type Replace1<X> = Never;
        type Replace2<X> = Never;
        type Replace3<X> = Never;
        type Replace4<X> = Never;
        type Replace5<X> = Never;
        type Replace6<X> = Never;
        type Replace7<X> = Never;
        type Replace8<X> = Never;
        type Replace9<X> = Never;
        type Replace10<X> = Never;
        type Replace11<X> = Never;
    }

    impl<A, B> Sealed for (A, B) {}

    impl<A, B> State for (A, B) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = Never;
        type Index3 = Never;
        type Index4 = Never;
        type Index5 = Never;
        type Index6 = Never;
        type Index7 = Never;
        type Index8 = Never;
        type Index9 = Never;
        type Index10 = Never;
        type Index11 = Never;

        type Replace0<X> = (X, B);
        type Replace1<X> = (A, X);
        type Replace2<X> = Never;
        type Replace3<X> = Never;
        type Replace4<X> = Never;
        type Replace5<X> = Never;
        type Replace6<X> = Never;
        type Replace7<X> = Never;
        type Replace8<X> = Never;
        type Replace9<X> = Never;
        type Replace10<X> = Never;
        type Replace11<X> = Never;
    }

    impl<A, B, C> Sealed for (A, B, C) {}

    impl<A, B, C> State for (A, B, C) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = C;
        type Index3 = Never;
        type Index4 = Never;
        type Index5 = Never;
        type Index6 = Never;
        type Index7 = Never;
        type Index8 = Never;
        type Index9 = Never;
        type Index10 = Never;
        type Index11 = Never;

        type Replace0<X> = (X, B, C);
        type Replace1<X> = (A, X, C);
        type Replace2<X> = (A, B, X);
        type Replace3<X> = Never;
        type Replace4<X> = Never;
        type Replace5<X> = Never;
        type Replace6<X> = Never;
        type Replace7<X> = Never;
        type Replace8<X> = Never;
        type Replace9<X> = Never;
        type Replace10<X> = Never;
        type Replace11<X> = Never;
    }

    impl<A, B, C, D> Sealed for (A, B, C, D) {}

    impl<A, B, C, D> State for (A, B, C, D) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = C;
        type Index3 = D;
        type Index4 = Never;
        type Index5 = Never;
        type Index6 = Never;
        type Index7 = Never;
        type Index8 = Never;
        type Index9 = Never;
        type Index10 = Never;
        type Index11 = Never;

        type Replace0<X> = (X, B, C, D);
        type Replace1<X> = (A, X, C, D);
        type Replace2<X> = (A, B, X, D);
        type Replace3<X> = (A, B, C, X);
        type Replace4<X> = Never;
        type Replace5<X> = Never;
        type Replace6<X> = Never;
        type Replace7<X> = Never;
        type Replace8<X> = Never;
        type Replace9<X> = Never;
        type Replace10<X> = Never;
        type Replace11<X> = Never;
    }

    impl<A, B, C, D, E> Sealed for (A, B, C, D, E) {}

    impl<A, B, C, D, E> State for (A, B, C, D, E) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = C;
        type Index3 = D;
        type Index4 = E;
        type Index5 = Never;
        type Index6 = Never;
        type Index7 = Never;
        type Index8 = Never;
        type Index9 = Never;
        type Index10 = Never;
        type Index11 = Never;

        type Replace0<X> = (X, B, C, D, E);
        type Replace1<X> = (A, X, C, D, E);
        type Replace2<X> = (A, B, X, D, E);
        type Replace3<X> = (A, B, C, X, E);
        type Replace4<X> = (A, B, C, D, X);
        type Replace5<X> = Never;
        type Replace6<X> = Never;
        type Replace7<X> = Never;
        type Replace8<X> = Never;
        type Replace9<X> = Never;
        type Replace10<X> = Never;
        type Replace11<X> = Never;
    }

    impl<A, B, C, D, E, F> Sealed for (A, B, C, D, E, F) {}

    impl<A, B, C, D, E, F> State for (A, B, C, D, E, F) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = C;
        type Index3 = D;
        type Index4 = E;
        type Index5 = F;
        type Index6 = Never;
        type Index7 = Never;
        type Index8 = Never;
        type Index9 = Never;
        type Index10 = Never;
        type Index11 = Never;

        type Replace0<X> = (X, B, C, D, E, F);
        type Replace1<X> = (A, X, C, D, E, F);
        type Replace2<X> = (A, B, X, D, E, F);
        type Replace3<X> = (A, B, C, X, E, F);
        type Replace4<X> = (A, B, C, D, X, F);
        type Replace5<X> = (A, B, C, D, E, X);
        type Replace6<X> = Never;
        type Replace7<X> = Never;
        type Replace8<X> = Never;
        type Replace9<X> = Never;
        type Replace10<X> = Never;
        type Replace11<X> = Never;
    }

    impl<A, B, C, D, E, F, G> Sealed for (A, B, C, D, E, F, G) {}

    impl<A, B, C, D, E, F, G> State for (A, B, C, D, E, F, G) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = C;
        type Index3 = D;
        type Index4 = E;
        type Index5 = F;
        type Index6 = G;
        type Index7 = Never;
        type Index8 = Never;
        type Index9 = Never;
        type Index10 = Never;
        type Index11 = Never;

        type Replace0<X> = (X, B, C, D, E, F, G);
        type Replace1<X> = (A, X, C, D, E, F, G);
        type Replace2<X> = (A, B, X, D, E, F, G);
        type Replace3<X> = (A, B, C, X, E, F, G);
        type Replace4<X> = (A, B, C, D, X, F, G);
        type Replace5<X> = (A, B, C, D, E, X, G);
        type Replace6<X> = (A, B, C, D, E, F, X);
        type Replace7<X> = Never;
        type Replace8<X> = Never;
        type Replace9<X> = Never;
        type Replace10<X> = Never;
        type Replace11<X> = Never;
    }

    impl<A, B, C, D, E, F, G, H> Sealed for (A, B, C, D, E, F, G, H) {}

    impl<A, B, C, D, E, F, G, H> State for (A, B, C, D, E, F, G, H) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = C;
        type Index3 = D;
        type Index4 = E;
        type Index5 = F;
        type Index6 = G;
        type Index7 = H;
        type Index8 = Never;
        type Index9 = Never;
        type Index10 = Never;
        type Index11 = Never;

        type Replace0<X> = (X, B, C, D, E, F, G, H);
        type Replace1<X> = (A, X, C, D, E, F, G, H);
        type Replace2<X> = (A, B, X, D, E, F, G, H);
        type Replace3<X> = (A, B, C, X, E, F, G, H);
        type Replace4<X> = (A, B, C, D, X, F, G, H);
        type Replace5<X> = (A, B, C, D, E, X, G, H);
        type Replace6<X> = (A, B, C, D, E, F, X, H);
        type Replace7<X> = (A, B, C, D, E, F, G, X);
        type Replace8<X> = Never;
        type Replace9<X> = Never;
        type Replace10<X> = Never;
        type Replace11<X> = Never;
    }

    impl<A, B, C, D, E, F, G, H, I> Sealed for (A, B, C, D, E, F, G, H, I) {}

    impl<A, B, C, D, E, F, G, H, I> State for (A, B, C, D, E, F, G, H, I) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = C;
        type Index3 = D;
        type Index4 = E;
        type Index5 = F;
        type Index6 = G;
        type Index7 = H;
        type Index8 = I;
        type Index9 = Never;
        type Index10 = Never;
        type Index11 = Never;

        type Replace0<X> = (X, B, C, D, E, F, G, H, I);
        type Replace1<X> = (A, X, C, D, E, F, G, H, I);
        type Replace2<X> = (A, B, X, D, E, F, G, H, I);
        type Replace3<X> = (A, B, C, X, E, F, G, H, I);
        type Replace4<X> = (A, B, C, D, X, F, G, H, I);
        type Replace5<X> = (A, B, C, D, E, X, G, H, I);
        type Replace6<X> = (A, B, C, D, E, F, X, H, I);
        type Replace7<X> = (A, B, C, D, E, F, G, X, I);
        type Replace8<X> = (A, B, C, D, E, F, G, H, X);
        type Replace9<X> = Never;
        type Replace10<X> = Never;
        type Replace11<X> = Never;
    }

    impl<A, B, C, D, E, F, G, H, I, J> Sealed for (A, B, C, D, E, F, G, H, I, J) {}

    impl<A, B, C, D, E, F, G, H, I, J> State for (A, B, C, D, E, F, G, H, I, J) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = C;
        type Index3 = D;
        type Index4 = E;
        type Index5 = F;
        type Index6 = G;
        type Index7 = H;
        type Index8 = I;
        type Index9 = J;
        type Index10 = Never;
        type Index11 = Never;

        type Replace0<X> = (X, B, C, D, E, F, G, H, I, J);
        type Replace1<X> = (A, X, C, D, E, F, G, H, I, J);
        type Replace2<X> = (A, B, X, D, E, F, G, H, I, J);
        type Replace3<X> = (A, B, C, X, E, F, G, H, I, J);
        type Replace4<X> = (A, B, C, D, X, F, G, H, I, J);
        type Replace5<X> = (A, B, C, D, E, X, G, H, I, J);
        type Replace6<X> = (A, B, C, D, E, F, X, H, I, J);
        type Replace7<X> = (A, B, C, D, E, F, G, X, I, J);
        type Replace8<X> = (A, B, C, D, E, F, G, H, X, J);
        type Replace9<X> = (A, B, C, D, E, F, G, H, I, X);
        type Replace10<X> = Never;
        type Replace11<X> = Never;
    }

    impl<A, B, C, D, E, F, G, H, I, J, K> Sealed for (A, B, C, D, E, F, G, H, I, J, K) {}

    impl<A, B, C, D, E, F, G, H, I, J, K> State for (A, B, C, D, E, F, G, H, I, J, K) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = C;
        type Index3 = D;
        type Index4 = E;
        type Index5 = F;
        type Index6 = G;
        type Index7 = H;
        type Index8 = I;
        type Index9 = J;
        type Index10 = K;
        type Index11 = Never;

        type Replace0<X> = (X, B, C, D, E, F, G, H, I, J, K);
        type Replace1<X> = (A, X, C, D, E, F, G, H, I, J, K);
        type Replace2<X> = (A, B, X, D, E, F, G, H, I, J, K);
        type Replace3<X> = (A, B, C, X, E, F, G, H, I, J, K);
        type Replace4<X> = (A, B, C, D, X, F, G, H, I, J, K);
        type Replace5<X> = (A, B, C, D, E, X, G, H, I, J, K);
        type Replace6<X> = (A, B, C, D, E, F, X, H, I, J, K);
        type Replace7<X> = (A, B, C, D, E, F, G, X, I, J, K);
        type Replace8<X> = (A, B, C, D, E, F, G, H, X, J, K);
        type Replace9<X> = (A, B, C, D, E, F, G, H, I, X, K);
        type Replace10<X> = (A, B, C, D, E, F, G, H, I, J, X);
        type Replace11<X> = Never;
    }

    impl<A, B, C, D, E, F, G, H, I, J, K, L> Sealed for (A, B, C, D, E, F, G, H, I, J, K, L) {}

    impl<A, B, C, D, E, F, G, H, I, J, K, L> State for (A, B, C, D, E, F, G, H, I, J, K, L) {
        type Index0 = A;
        type Index1 = B;
        type Index2 = C;
        type Index3 = D;
        type Index4 = E;
        type Index5 = F;
        type Index6 = G;
        type Index7 = H;
        type Index8 = I;
        type Index9 = J;
        type Index10 = K;
        type Index11 = L;

        type Replace0<X> = (X, B, C, D, E, F, G, H, I, J, K, L);
        type Replace1<X> = (A, X, C, D, E, F, G, H, I, J, K, L);
        type Replace2<X> = (A, B, X, D, E, F, G, H, I, J, K, L);
        type Replace3<X> = (A, B, C, X, E, F, G, H, I, J, K, L);
        type Replace4<X> = (A, B, C, D, X, F, G, H, I, J, K, L);
        type Replace5<X> = (A, B, C, D, E, X, G, H, I, J, K, L);
        type Replace6<X> = (A, B, C, D, E, F, X, H, I, J, K, L);
        type Replace7<X> = (A, B, C, D, E, F, G, X, I, J, K, L);
        type Replace8<X> = (A, B, C, D, E, F, G, H, X, J, K, L);
        type Replace9<X> = (A, B, C, D, E, F, G, H, I, X, K, L);
        type Replace10<X> = (A, B, C, D, E, F, G, H, I, J, X, L);
        type Replace11<X> = (A, B, C, D, E, F, G, H, I, J, K, X);
    }
}

mod has_field_tuple_impls {
    use super::*;

    macro_rules! impl_methods {
        ($idx:tt) => {
            #[inline(always)]
            fn project(outer: NonNull<Self>) -> NonNull<Self::Type> {
                unsafe { NonNull::new_unchecked(addr_of_mut!((*outer.as_ptr()).$idx)) }
            }

            #[inline(always)]
            unsafe fn init_tag(_outer: NonNull<Self>) {}
        };
    }

    // --- State 1 ---
    // unsafe impl<A> Initialized<Init> for (A,) {}

    unsafe impl<A, II: State> HasField<0, 0, II> for (A,) {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }

    // --- State 2 ---

    unsafe impl<A, B, II: State> HasField<0, 0, II> for (A, B) {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }

    unsafe impl<A, B, II: State> HasField<0, 1, II> for (A, B) {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }

    // --- State 3 ---

    unsafe impl<A, B, C, II: State> HasField<0, 0, II> for (A, B, C) {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }
    unsafe impl<A, B, C, II: State> HasField<0, 1, II> for (A, B, C) {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }
    unsafe impl<A, B, C, II: State> HasField<0, 2, II> for (A, B, C) {
        type Type = C;
        type FieldInit = II::Index2;
        type Overwrite<This> = II::Replace2<This>;

        impl_methods!(2);
    }

    // --- State 4 ---

    unsafe impl<A, B, C, D, II: State> HasField<0, 0, II> for (A, B, C, D) {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }
    unsafe impl<A, B, C, D, II: State> HasField<0, 1, II> for (A, B, C, D) {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }
    unsafe impl<A, B, C, D, II: State> HasField<0, 2, II> for (A, B, C, D) {
        type Type = C;
        type FieldInit = II::Index2;
        type Overwrite<This> = II::Replace2<This>;

        impl_methods!(2);
    }
    unsafe impl<A, B, C, D, II: State> HasField<0, 3, II> for (A, B, C, D) {
        type Type = D;
        type FieldInit = II::Index3;
        type Overwrite<This> = II::Replace3<This>;

        impl_methods!(3);
    }

    // --- State 5 ---

    unsafe impl<A, B, C, D, E, II: State> HasField<0, 0, II> for (A, B, C, D, E) {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }
    unsafe impl<A, B, C, D, E, II: State> HasField<0, 1, II> for (A, B, C, D, E) {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }
    unsafe impl<A, B, C, D, E, II: State> HasField<0, 2, II> for (A, B, C, D, E) {
        type Type = C;
        type FieldInit = II::Index2;
        type Overwrite<This> = II::Replace2<This>;

        impl_methods!(2);
    }
    unsafe impl<A, B, C, D, E, II: State> HasField<0, 3, II> for (A, B, C, D, E) {
        type Type = D;
        type FieldInit = II::Index3;
        type Overwrite<This> = II::Replace3<This>;

        impl_methods!(3);
    }
    unsafe impl<A, B, C, D, E, II: State> HasField<0, 4, II> for (A, B, C, D, E) {
        type Type = E;
        type FieldInit = II::Index4;
        type Overwrite<This> = II::Replace4<This>;

        impl_methods!(4);
    }

    // --- State 6 ---

    unsafe impl<A, B, C, D, E, F, II: State> HasField<0, 0, II> for (A, B, C, D, E, F) {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }
    unsafe impl<A, B, C, D, E, F, II: State> HasField<0, 1, II> for (A, B, C, D, E, F) {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }
    unsafe impl<A, B, C, D, E, F, II: State> HasField<0, 2, II> for (A, B, C, D, E, F) {
        type Type = C;
        type FieldInit = II::Index2;
        type Overwrite<This> = II::Replace2<This>;

        impl_methods!(2);
    }
    unsafe impl<A, B, C, D, E, F, II: State> HasField<0, 3, II> for (A, B, C, D, E, F) {
        type Type = D;
        type FieldInit = II::Index3;
        type Overwrite<This> = II::Replace3<This>;

        impl_methods!(3);
    }
    unsafe impl<A, B, C, D, E, F, II: State> HasField<0, 4, II> for (A, B, C, D, E, F) {
        type Type = E;
        type FieldInit = II::Index4;
        type Overwrite<This> = II::Replace4<This>;

        impl_methods!(4);
    }
    unsafe impl<A, B, C, D, E, F, II: State> HasField<0, 5, II> for (A, B, C, D, E, F) {
        type Type = F;
        type FieldInit = II::Index5;
        type Overwrite<This> = II::Replace5<This>;

        impl_methods!(5);
    }

    // --- State 7 ---

    unsafe impl<A, B, C, D, E, F, G, II: State> HasField<0, 0, II> for (A, B, C, D, E, F, G) {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }
    unsafe impl<A, B, C, D, E, F, G, II: State> HasField<0, 1, II> for (A, B, C, D, E, F, G) {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }
    unsafe impl<A, B, C, D, E, F, G, II: State> HasField<0, 2, II> for (A, B, C, D, E, F, G) {
        type Type = C;
        type FieldInit = II::Index2;
        type Overwrite<This> = II::Replace2<This>;

        impl_methods!(2);
    }
    unsafe impl<A, B, C, D, E, F, G, II: State> HasField<0, 3, II> for (A, B, C, D, E, F, G) {
        type Type = D;
        type FieldInit = II::Index3;
        type Overwrite<This> = II::Replace3<This>;

        impl_methods!(3);
    }
    unsafe impl<A, B, C, D, E, F, G, II: State> HasField<0, 4, II> for (A, B, C, D, E, F, G) {
        type Type = E;
        type FieldInit = II::Index4;
        type Overwrite<This> = II::Replace4<This>;

        impl_methods!(4);
    }
    unsafe impl<A, B, C, D, E, F, G, II: State> HasField<0, 5, II> for (A, B, C, D, E, F, G) {
        type Type = F;
        type FieldInit = II::Index5;
        type Overwrite<This> = II::Replace5<This>;

        impl_methods!(5);
    }
    unsafe impl<A, B, C, D, E, F, G, II: State> HasField<0, 6, II> for (A, B, C, D, E, F, G) {
        type Type = G;
        type FieldInit = II::Index6;
        type Overwrite<This> = II::Replace6<This>;

        impl_methods!(6);
    }

    // --- State 8 ---

    unsafe impl<A, B, C, D, E, F, G, H, II: State> HasField<0, 0, II> for (A, B, C, D, E, F, G, H) {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }
    unsafe impl<A, B, C, D, E, F, G, H, II: State> HasField<0, 1, II> for (A, B, C, D, E, F, G, H) {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }
    unsafe impl<A, B, C, D, E, F, G, H, II: State> HasField<0, 2, II> for (A, B, C, D, E, F, G, H) {
        type Type = C;
        type FieldInit = II::Index2;
        type Overwrite<This> = II::Replace2<This>;

        impl_methods!(2);
    }
    unsafe impl<A, B, C, D, E, F, G, H, II: State> HasField<0, 3, II> for (A, B, C, D, E, F, G, H) {
        type Type = D;
        type FieldInit = II::Index3;
        type Overwrite<This> = II::Replace3<This>;

        impl_methods!(3);
    }
    unsafe impl<A, B, C, D, E, F, G, H, II: State> HasField<0, 4, II> for (A, B, C, D, E, F, G, H) {
        type Type = E;
        type FieldInit = II::Index4;
        type Overwrite<This> = II::Replace4<This>;

        impl_methods!(4);
    }
    unsafe impl<A, B, C, D, E, F, G, H, II: State> HasField<0, 5, II> for (A, B, C, D, E, F, G, H) {
        type Type = F;
        type FieldInit = II::Index5;
        type Overwrite<This> = II::Replace5<This>;

        impl_methods!(5);
    }
    unsafe impl<A, B, C, D, E, F, G, H, II: State> HasField<0, 6, II> for (A, B, C, D, E, F, G, H) {
        type Type = G;
        type FieldInit = II::Index6;
        type Overwrite<This> = II::Replace6<This>;

        impl_methods!(6);
    }
    unsafe impl<A, B, C, D, E, F, G, H, II: State> HasField<0, 7, II> for (A, B, C, D, E, F, G, H) {
        type Type = H;
        type FieldInit = II::Index7;
        type Overwrite<This> = II::Replace7<This>;

        impl_methods!(7);
    }

    // --- State 9 ---

    unsafe impl<A, B, C, D, E, F, G, H, I, II: State> HasField<0, 0, II>
        for (A, B, C, D, E, F, G, H, I)
    {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, II: State> HasField<0, 1, II>
        for (A, B, C, D, E, F, G, H, I)
    {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, II: State> HasField<0, 2, II>
        for (A, B, C, D, E, F, G, H, I)
    {
        type Type = C;
        type FieldInit = II::Index2;
        type Overwrite<This> = II::Replace2<This>;

        impl_methods!(2);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, II: State> HasField<0, 3, II>
        for (A, B, C, D, E, F, G, H, I)
    {
        type Type = D;
        type FieldInit = II::Index3;
        type Overwrite<This> = II::Replace3<This>;

        impl_methods!(3);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, II: State> HasField<0, 4, II>
        for (A, B, C, D, E, F, G, H, I)
    {
        type Type = E;
        type FieldInit = II::Index4;
        type Overwrite<This> = II::Replace4<This>;

        impl_methods!(4);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, II: State> HasField<0, 5, II>
        for (A, B, C, D, E, F, G, H, I)
    {
        type Type = F;
        type FieldInit = II::Index5;
        type Overwrite<This> = II::Replace5<This>;

        impl_methods!(5);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, II: State> HasField<0, 6, II>
        for (A, B, C, D, E, F, G, H, I)
    {
        type Type = G;
        type FieldInit = II::Index6;
        type Overwrite<This> = II::Replace6<This>;

        impl_methods!(6);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, II: State> HasField<0, 7, II>
        for (A, B, C, D, E, F, G, H, I)
    {
        type Type = H;
        type FieldInit = II::Index7;
        type Overwrite<This> = II::Replace7<This>;

        impl_methods!(7);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, II: State> HasField<0, 8, II>
        for (A, B, C, D, E, F, G, H, I)
    {
        type Type = I;
        type FieldInit = II::Index8;
        type Overwrite<This> = II::Replace8<This>;

        impl_methods!(8);
    }

    // --- State 10 ---

    unsafe impl<A, B, C, D, E, F, G, H, I, J, II: State> HasField<0, 0, II>
        for (A, B, C, D, E, F, G, H, I, J)
    {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, II: State> HasField<0, 1, II>
        for (A, B, C, D, E, F, G, H, I, J)
    {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, II: State> HasField<0, 2, II>
        for (A, B, C, D, E, F, G, H, I, J)
    {
        type Type = C;
        type FieldInit = II::Index2;
        type Overwrite<This> = II::Replace2<This>;

        impl_methods!(2);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, II: State> HasField<0, 3, II>
        for (A, B, C, D, E, F, G, H, I, J)
    {
        type Type = D;
        type FieldInit = II::Index3;
        type Overwrite<This> = II::Replace3<This>;

        impl_methods!(3);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, II: State> HasField<0, 4, II>
        for (A, B, C, D, E, F, G, H, I, J)
    {
        type Type = E;
        type FieldInit = II::Index4;
        type Overwrite<This> = II::Replace4<This>;

        impl_methods!(4);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, II: State> HasField<0, 5, II>
        for (A, B, C, D, E, F, G, H, I, J)
    {
        type Type = F;
        type FieldInit = II::Index5;
        type Overwrite<This> = II::Replace5<This>;

        impl_methods!(5);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, II: State> HasField<0, 6, II>
        for (A, B, C, D, E, F, G, H, I, J)
    {
        type Type = G;
        type FieldInit = II::Index6;
        type Overwrite<This> = II::Replace6<This>;

        impl_methods!(6);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, II: State> HasField<0, 7, II>
        for (A, B, C, D, E, F, G, H, I, J)
    {
        type Type = H;
        type FieldInit = II::Index7;
        type Overwrite<This> = II::Replace7<This>;

        impl_methods!(7);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, II: State> HasField<0, 8, II>
        for (A, B, C, D, E, F, G, H, I, J)
    {
        type Type = I;
        type FieldInit = II::Index8;
        type Overwrite<This> = II::Replace8<This>;

        impl_methods!(8);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, II: State> HasField<0, 9, II>
        for (A, B, C, D, E, F, G, H, I, J)
    {
        type Type = J;
        type FieldInit = II::Index9;
        type Overwrite<This> = II::Replace9<This>;

        impl_methods!(9);
    }

    // --- State 11 ---

    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 0, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 1, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 2, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = C;
        type FieldInit = II::Index2;
        type Overwrite<This> = II::Replace2<This>;

        impl_methods!(2);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 3, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = D;
        type FieldInit = II::Index3;
        type Overwrite<This> = II::Replace3<This>;

        impl_methods!(3);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 4, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = E;
        type FieldInit = II::Index4;
        type Overwrite<This> = II::Replace4<This>;

        impl_methods!(4);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 5, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = F;
        type FieldInit = II::Index5;
        type Overwrite<This> = II::Replace5<This>;

        impl_methods!(5);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 6, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = G;
        type FieldInit = II::Index6;
        type Overwrite<This> = II::Replace6<This>;

        impl_methods!(6);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 7, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = H;
        type FieldInit = II::Index7;
        type Overwrite<This> = II::Replace7<This>;

        impl_methods!(7);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 8, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = I;
        type FieldInit = II::Index8;
        type Overwrite<This> = II::Replace8<This>;

        impl_methods!(8);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 9, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = J;
        type FieldInit = II::Index9;
        type Overwrite<This> = II::Replace9<This>;

        impl_methods!(9);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, II: State> HasField<0, 10, II>
        for (A, B, C, D, E, F, G, H, I, J, K)
    {
        type Type = K;
        type FieldInit = II::Index10;
        type Overwrite<This> = II::Replace10<This>;

        impl_methods!(10);
    }

    // --- State 12 ---

    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 0, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = A;
        type FieldInit = II::Index0;
        type Overwrite<This> = II::Replace0<This>;

        impl_methods!(0);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 1, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = B;
        type FieldInit = II::Index1;
        type Overwrite<This> = II::Replace1<This>;

        impl_methods!(1);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 2, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = C;
        type FieldInit = II::Index2;
        type Overwrite<This> = II::Replace2<This>;

        impl_methods!(2);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 3, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = D;
        type FieldInit = II::Index3;
        type Overwrite<This> = II::Replace3<This>;

        impl_methods!(3);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 4, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = E;
        type FieldInit = II::Index4;
        type Overwrite<This> = II::Replace4<This>;

        impl_methods!(4);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 5, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = F;
        type FieldInit = II::Index5;
        type Overwrite<This> = II::Replace5<This>;

        impl_methods!(5);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 6, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = G;
        type FieldInit = II::Index6;
        type Overwrite<This> = II::Replace6<This>;

        impl_methods!(6);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 7, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = H;
        type FieldInit = II::Index7;
        type Overwrite<This> = II::Replace7<This>;

        impl_methods!(7);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 8, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = I;
        type FieldInit = II::Index8;
        type Overwrite<This> = II::Replace8<This>;

        impl_methods!(8);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 9, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = J;
        type FieldInit = II::Index9;
        type Overwrite<This> = II::Replace9<This>;

        impl_methods!(9);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 10, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = K;
        type FieldInit = II::Index10;
        type Overwrite<This> = II::Replace10<This>;

        impl_methods!(10);
    }
    unsafe impl<A, B, C, D, E, F, G, H, I, J, K, L, II: State> HasField<0, 11, II>
        for (A, B, C, D, E, F, G, H, I, J, K, L)
    {
        type Type = L;
        type FieldInit = II::Index11;
        type Overwrite<This> = II::Replace11<This>;

        impl_methods!(11);
    }
}

// TODO: Tests
