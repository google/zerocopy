use crate::{DefaultHashBuilder, IdHashItem, support::map_hash::MapHash};
use core::{
    fmt,
    hash::BuildHasher,
    ops::{Deref, DerefMut},
};

/// A mutable reference to an [`IdHashMap`] item.
///
/// This is a wrapper around a `&mut T` that panics when dropped, if the
/// borrowed value's keys have changed since the wrapper was created.
///
/// # Change detection
///
/// It is illegal to change the key of a borrowed `&mut T`. `RefMut` attempts to
/// enforce this invariant.
///
/// `RefMut` stores the `Hash` output of the key at creation time, and
/// recomputes this hash when it is dropped or when [`Self::into_ref`] is
/// called. If a key changes, there's a small but non-negligible chance that its
/// hash value stays the same[^collision-chance]. In that case, as long as the
/// new key is not the same as another existing one, internal invariants are not
/// violated and the [`IdHashMap`] will continue to work correctly. (But don't
/// rely on this!)
///
/// It is also possible to deliberately write pathological `Hash`
/// implementations that collide more often. (Don't do this either.)
///
/// Also, `RefMut`'s hash detection will not function if [`mem::forget`] is
/// called on it. If the key is changed and `mem::forget` is then called on the
/// `RefMut`, the [`IdHashMap`] will stop functioning correctly. This will not
/// introduce memory safety issues, however.
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
/// [`IdHashMap`]: crate::IdHashMap
/// [birthday problem]: https://en.wikipedia.org/wiki/Birthday_problem#Probability_table
pub struct RefMut<
    'a,
    T: IdHashItem,
    S: Clone + BuildHasher = DefaultHashBuilder,
> {
    inner: Option<RefMutInner<'a, T, S>>,
}

impl<'a, T: IdHashItem, S: Clone + BuildHasher> RefMut<'a, T, S> {
    pub(super) fn new(state: S, hash: MapHash, borrowed: &'a mut T) -> Self {
        Self { inner: Some(RefMutInner { state, hash, borrowed }) }
    }

    /// Borrows self into a shorter-lived `RefMut`.
    ///
    /// This `RefMut` will also check hash equality on drop.
    pub fn reborrow(&mut self) -> RefMut<'_, T, S> {
        let inner = self.inner.as_mut().unwrap();
        let borrowed = &mut *inner.borrowed;
        RefMut::new(inner.state.clone(), inner.hash.clone(), borrowed)
    }

    /// Converts this `RefMut` into a `&'a T`.
    pub fn into_ref(mut self) -> &'a T {
        let inner = self.inner.take().unwrap();
        inner.into_ref()
    }
}

impl<T: IdHashItem, S: Clone + BuildHasher> Drop for RefMut<'_, T, S> {
    fn drop(&mut self) {
        if let Some(inner) = self.inner.take() {
            inner.into_ref();
        }
    }
}

impl<T: IdHashItem, S: Clone + BuildHasher> Deref for RefMut<'_, T, S> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.inner.as_ref().unwrap().borrowed
    }
}

impl<T: IdHashItem, S: Clone + BuildHasher> DerefMut for RefMut<'_, T, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner.as_mut().unwrap().borrowed
    }
}

impl<T: IdHashItem + fmt::Debug, S: Clone + BuildHasher> fmt::Debug
    for RefMut<'_, T, S>
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

struct RefMutInner<'a, T: IdHashItem, S> {
    state: S,
    hash: MapHash,
    borrowed: &'a mut T,
}

impl<'a, T: IdHashItem, S: BuildHasher> RefMutInner<'a, T, S> {
    fn into_ref(self) -> &'a T {
        if !self.hash.is_same_hash(&self.state, self.borrowed.key()) {
            panic!("key changed during RefMut borrow");
        }

        self.borrowed
    }
}

impl<T: IdHashItem + fmt::Debug, S> fmt::Debug for RefMutInner<'_, T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.borrowed.fmt(f)
    }
}
