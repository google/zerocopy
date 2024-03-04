//! Machinery for statically proving the 'cell-safety' of a `Ptr`.

use crate::{invariant, NoCell};

/// Marks 'cell-safe' types.
///
/// # Safety
///
/// `T: CellSafe<A, R>` if it is statically provable that for all `Ptr<'a, T,
/// I>` such that `I::Aliasing = A`:
///
/// > 11. During the lifetime `'a``, no live reference or live `Ptr` will exist
/// >     to this memory which treats `UnsafeCell`s as existing at different
/// >     ranges than they exist in `T`.
#[doc(hidden)]
pub unsafe trait CellSafe<A: invariant::Aliasing, R: CellSafeReason> {}

/// Used to prevent user implementations of `CellSafeReason`.
mod sealed {
    pub trait Sealed {}

    impl Sealed for super::BecauseExclusive {}
    impl Sealed for super::BecauseNoCell {}
}

#[doc(hidden)]
pub trait CellSafeReason: sealed::Sealed {}

/// `T` is [`CellSafe`] because it is the sole live references and live `Ptr` to
/// its bytes.
#[derive(Copy, Clone, Debug)]
#[doc(hidden)]
pub enum BecauseExclusive {}
impl CellSafeReason for BecauseExclusive {}

/// `T` is [`CellSafe`] because all live references and live `Ptr` agree that
/// its bytes contains no `UnsafeCell`s.
#[derive(Copy, Clone, Debug)]
#[doc(hidden)]
pub enum BecauseNoCell {}
impl CellSafeReason for BecauseNoCell {}

/// # Safety
///
/// `T: CellSafe<Exclusive, BecauseExclusive>` because for all `Ptr<'a, T, I>`
/// such that `I::Aliasing = Exclusive`, there cannot exist other live
/// references to the memory referenced by `Ptr`.
#[doc(hidden)]
unsafe impl<T: ?Sized> CellSafe<invariant::Exclusive, BecauseExclusive> for T {}

/// # Safety
///
/// `T: CellSafe<A, BecauseNoCell>` because for all `Ptr<'a, T, I>` such that
/// `I::Aliasing = A`, all live references and live `Ptr`s agree, by invariant
/// on `NoCell`, that the referenced bytes contain no `UnsafeCell`s.
unsafe impl<A, T: ?Sized> CellSafe<A, BecauseNoCell> for T
where
    A: invariant::Aliasing,
    T: NoCell,
{
}
