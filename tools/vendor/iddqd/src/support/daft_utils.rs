use core::ops::{Deref, DerefMut};
use daft::{Diffable, Leaf};

/// A leaf type similar to [`daft::Leaf`], which statically guarantees that the
/// before and after values have the same key or keys.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IdLeaf<T> {
    before: T,
    after: T,
}

impl<T> IdLeaf<T> {
    pub(crate) fn new(before: T, after: T) -> Self {
        IdLeaf { before, after }
    }

    /// Returns the `before` value.
    #[inline]
    pub fn before(&self) -> &T {
        &self.before
    }

    /// Returns the `after` value.
    #[inline]
    pub fn after(&self) -> &T {
        &self.after
    }

    /// Converts self into a [`daft::Leaf`].
    #[inline]
    pub fn into_leaf(self) -> Leaf<T> {
        Leaf { before: self.before, after: self.after }
    }

    /// Converts from `&IdLeaf<T>` to `IdLeaf<&T>`.
    #[inline]
    pub fn as_ref(&self) -> IdLeaf<&T> {
        IdLeaf { before: &self.before, after: &self.after }
    }

    /// Converts from `&mut IdLeaf<T>` to `IdLeaf<&mut T>`.
    #[inline]
    pub fn as_mut(&mut self) -> IdLeaf<&mut T> {
        IdLeaf { before: &mut self.before, after: &mut self.after }
    }

    /// Converts from `IdLeaf<T>` or `&IdLeaf<T>` to `IdLeaf<&T::Target>`.
    #[inline]
    pub fn as_deref(&self) -> IdLeaf<&T::Target>
    where
        T: Deref,
    {
        IdLeaf { before: &*self.before, after: &*self.after }
    }

    /// Converts from `IdLeaf<T>` or `&mut IdLeaf<T>` to `IdLeaf<&mut
    /// T::Target>`.
    #[inline]
    pub fn as_deref_mut(&mut self) -> IdLeaf<&mut T::Target>
    where
        T: DerefMut,
    {
        IdLeaf { before: &mut *self.before, after: &mut *self.after }
    }

    /// Return true if before is the same as after.
    ///
    /// This is the same as `self.before() == self.after()`, but is easier to
    /// use in a chained series of method calls.
    #[inline]
    pub fn is_unchanged(&self) -> bool
    where
        T: Eq,
    {
        self.before == self.after
    }

    /// Return true if before is different from after.
    ///
    /// This is the same as `self.before != self.after`, but is easier to use in
    /// a chained series of method calls.
    #[inline]
    pub fn is_modified(&self) -> bool
    where
        T: Eq,
    {
        self.before != self.after
    }
}

impl<'daft, T: ?Sized + Diffable> IdLeaf<&'daft T> {
    /// Perform a diff on [`before`][Self::before] and [`after`][Self::after],
    /// returning `T::Diff`.
    ///
    /// This is useful when `T::Diff` is not a leaf node.
    #[inline]
    pub fn diff_pair(self) -> T::Diff<'daft> {
        self.before.diff(self.after)
    }
}

impl<T> IdLeaf<&T> {
    /// Create a clone of the `IdLeaf` with owned values.
    #[inline]
    pub fn cloned(self) -> IdLeaf<T>
    where
        T: Clone,
    {
        IdLeaf { before: self.before.clone(), after: self.after.clone() }
    }

    /// Create a copy of the leaf with owned values.
    #[inline]
    pub fn copied(self) -> IdLeaf<T>
    where
        T: Copy,
    {
        IdLeaf { before: *self.before, after: *self.after }
    }
}
