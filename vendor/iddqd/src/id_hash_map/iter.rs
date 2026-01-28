use super::{RefMut, tables::IdHashMapTables};
use crate::{
    DefaultHashBuilder, IdHashItem,
    support::{
        alloc::{AllocWrapper, Allocator, Global},
        item_set::ItemSet,
    },
};
use core::{hash::BuildHasher, iter::FusedIterator};
use hashbrown::hash_map;

/// An iterator over the elements of a [`IdHashMap`] by shared reference.
/// Created by [`IdHashMap::iter`].
///
/// Similar to [`HashMap`], the iteration order is arbitrary and not guaranteed
/// to be stable.
///
/// [`IdHashMap`]: crate::IdHashMap
/// [`IdHashMap::iter`]: crate::IdHashMap::iter
/// [`HashMap`]: std::collections::HashMap
#[derive(Clone, Debug, Default)]
pub struct Iter<'a, T: IdHashItem> {
    inner: hash_map::Values<'a, usize, T>,
}

impl<'a, T: IdHashItem> Iter<'a, T> {
    pub(crate) fn new<A: Allocator>(items: &'a ItemSet<T, A>) -> Self {
        Self { inner: items.values() }
    }
}

impl<'a, T: IdHashItem> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<T: IdHashItem> ExactSizeIterator for Iter<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

// hash_map::Iter is a FusedIterator, so Iter is as well.
impl<T: IdHashItem> FusedIterator for Iter<'_, T> {}

/// An iterator over the elements of a [`IdHashMap`] by mutable reference.
/// Created by [`IdHashMap::iter_mut`].
///
/// This iterator returns [`RefMut`] instances.
///
/// Similar to [`HashMap`], the iteration order is arbitrary and not guaranteed
/// to be stable.
///
/// [`IdHashMap`]: crate::IdHashMap
/// [`IdHashMap::iter_mut`]: crate::IdHashMap::iter_mut
/// [`HashMap`]: std::collections::HashMap
#[derive(Debug)]
pub struct IterMut<
    'a,
    T: IdHashItem,
    S = DefaultHashBuilder,
    A: Allocator = Global,
> {
    tables: &'a IdHashMapTables<S, A>,
    inner: hash_map::ValuesMut<'a, usize, T>,
}

impl<'a, T: IdHashItem, S: BuildHasher, A: Allocator> IterMut<'a, T, S, A> {
    pub(super) fn new(
        tables: &'a IdHashMapTables<S, A>,
        items: &'a mut ItemSet<T, A>,
    ) -> Self {
        Self { tables, inner: items.values_mut() }
    }
}

impl<'a, T: IdHashItem, S: Clone + BuildHasher, A: Allocator> Iterator
    for IterMut<'a, T, S, A>
{
    type Item = RefMut<'a, T, S>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.inner.next()?;
        let hashes = self.tables.make_hash(next);
        Some(RefMut::new(self.tables.state.clone(), hashes, next))
    }
}

impl<T: IdHashItem, S: Clone + BuildHasher, A: Allocator> ExactSizeIterator
    for IterMut<'_, T, S, A>
{
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

// hash_map::IterMut is a FusedIterator, so IterMut is as well.
impl<T: IdHashItem, S: Clone + BuildHasher, A: Allocator> FusedIterator
    for IterMut<'_, T, S, A>
{
}

/// An iterator over the elements of a [`IdHashMap`] by ownership. Created by
/// [`IdHashMap::into_iter`].
///
/// Similar to [`HashMap`], the iteration order is arbitrary and not guaranteed
/// to be stable.
///
/// [`IdHashMap`]: crate::IdHashMap
/// [`IdHashMap::into_iter`]: crate::IdHashMap::into_iter
/// [`HashMap`]: std::collections::HashMap
#[derive(Debug)]
pub struct IntoIter<T: IdHashItem, A: Allocator = Global> {
    inner: hash_map::IntoValues<usize, T, AllocWrapper<A>>,
}

impl<T: IdHashItem, A: Allocator> IntoIter<T, A> {
    pub(crate) fn new(items: ItemSet<T, A>) -> Self {
        Self { inner: items.into_values() }
    }
}

impl<T: IdHashItem, A: Allocator> Iterator for IntoIter<T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<T: IdHashItem, A: Allocator> ExactSizeIterator for IntoIter<T, A> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

// hash_map::IterMut is a FusedIterator, so IterMut is as well.
impl<T: IdHashItem, A: Allocator> FusedIterator for IntoIter<T, A> {}
