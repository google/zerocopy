use super::IdOrdItem;
use crate::support::map_hash::MapHash;
use core::{
    fmt,
    hash::Hash,
    ops::{Deref, DerefMut},
};

/// A mutable reference to an [`IdOrdMap`] entry.
///
/// This is a wrapper around a `&mut T` that panics when dropped, if the
/// borrowed value's key has changed since the wrapper was created.
///
/// # Change detection
///
/// It is illegal to change the keys of a borrowed `&mut T`. `RefMut` attempts
/// to enforce this invariant, and as part of that, it requires that the key
/// type implement [`Hash`].
///
/// `RefMut` stores the `Hash` output of keys at creation time, and recomputes
/// these hashes when it is dropped or when [`Self::into_ref`] is called. If a
/// key changes, there's a small but non-negligible chance that its hash value
/// stays the same[^collision-chance]. In that case, the map will no longer
/// function correctly and might panic on access. This will not introduce memory
/// safety issues, however.
///
/// It is also possible to deliberately write pathological `Hash`
/// implementations that collide more often. (Don't do this.)
///
/// Also, `RefMut`'s hash detection will not function if [`mem::forget`] is
/// called on it. If a key is changed and `mem::forget` is then called on the
/// `RefMut`, the [`IdOrdMap`] will no longer function correctly and might panic
/// on access. This will not introduce memory safety issues, however.
///
/// The issues here are similar to using interior mutability (e.g. `RefCell` or
/// `Mutex`) to mutate keys in a regular `HashMap`.
///
/// [`mem::forget`]: std::mem::forget
///
/// [^collision-chance]: The output of `Hash` is a [`u64`], so the probability
/// of an individual hash colliding by chance is 1/2⁶⁴. Due to the [birthday
/// problem], the probability of a collision by chance reaches 10⁻⁶ within
/// around 6 × 10⁶ elements.
///
/// [`IdOrdMap`]: crate::IdOrdMap
/// [birthday problem]: https://en.wikipedia.org/wiki/Birthday_problem#Probability_table
pub struct RefMut<'a, T: IdOrdItem>
where
    T::Key<'a>: Hash,
{
    inner: Option<RefMutInner<'a, T>>,
}

impl<'a, T: IdOrdItem> RefMut<'a, T>
where
    T::Key<'a>: Hash,
{
    pub(super) fn new(
        state: foldhash::fast::FixedState,
        hash: MapHash,
        borrowed: &'a mut T,
    ) -> Self {
        let inner = RefMutInner { state, hash, borrowed };
        Self { inner: Some(inner) }
    }

    /// Converts this `RefMut` into a `&'a T`.
    pub fn into_ref(mut self) -> &'a T {
        let inner = self.inner.take().unwrap();
        inner.into_ref()
    }
}

impl<'a, T: for<'k> IdOrdItemMut<'k>> RefMut<'a, T> {
    /// Borrows self into a shorter-lived `RefMut`.
    ///
    /// This `RefMut` will also check hash equality on drop.
    pub fn reborrow<'b>(&'b mut self) -> RefMut<'b, T> {
        let inner = self.inner.as_mut().unwrap();
        let borrowed = &mut *inner.borrowed;
        RefMut::new(inner.state.clone(), inner.hash.clone(), borrowed)
    }
}

impl<'a, T: IdOrdItem> Drop for RefMut<'a, T>
where
    T::Key<'a>: Hash,
{
    fn drop(&mut self) {
        if let Some(inner) = self.inner.take() {
            inner.into_ref();
        }
    }
}

impl<'a, T: IdOrdItem> Deref for RefMut<'a, T>
where
    T::Key<'a>: Hash,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.inner.as_ref().unwrap().borrowed
    }
}

impl<'a, T: IdOrdItem> DerefMut for RefMut<'a, T>
where
    T::Key<'a>: Hash,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner.as_mut().unwrap().borrowed
    }
}

impl<'a, T: IdOrdItem + fmt::Debug> fmt::Debug for RefMut<'a, T>
where
    T::Key<'a>: Hash,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.inner {
            Some(ref inner) => inner.fmt(f),
            None => {
                f.debug_struct("RefMut").field("borrowed", &"missing").finish()
            }
        }
    }
}

struct RefMutInner<'a, T: IdOrdItem> {
    state: foldhash::fast::FixedState,
    hash: MapHash,
    borrowed: &'a mut T,
}

impl<'a, T: IdOrdItem> RefMutInner<'a, T>
where
    T::Key<'a>: Hash,
{
    fn into_ref(self) -> &'a T {
        let key: T::Key<'_> = self.borrowed.key();
        // SAFETY: The key is borrowed, then dropped immediately. T is valid for
        // 'a so T::Key is valid for 'a.
        let key: T::Key<'a> =
            unsafe { std::mem::transmute::<T::Key<'_>, T::Key<'a>>(key) };
        if !self.hash.is_same_hash(&self.state, &key) {
            panic!("key changed during RefMut borrow");
        }

        self.borrowed
    }
}

impl<T: IdOrdItem + fmt::Debug> fmt::Debug for RefMutInner<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.borrowed.fmt(f)
    }
}

/// A trait for mutable access to items in an [`IdOrdMap`].
///
/// This is a non-public trait used to work around a Rust borrow checker
/// limitation. [This will produce a documentation warning if it becomes
/// public].
///
/// This is automatically implemented whenever `T::Key` implements [`Hash`].
///
/// [`IdOrdMap`]: crate::IdOrdMap
pub trait IdOrdItemMut<'a>: IdOrdItem<Key<'a>: Hash> + 'a {}

impl<'a, T> IdOrdItemMut<'a> for T where T: 'a + IdOrdItem<Key<'a>: Hash> {}
