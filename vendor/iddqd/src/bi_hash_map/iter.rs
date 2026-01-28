use super::{RefMut, tables::BiHashMapTables};
use crate::{
    BiHashItem, DefaultHashBuilder,
    support::{
        alloc::{AllocWrapper, Allocator, Global},
        item_set::ItemSet,
    },
};
use core::{hash::BuildHasher, iter::FusedIterator};
use hashbrown::hash_map;

/// An iterator over the elements of a [`BiHashMap`] by shared reference.
/// Created by [`BiHashMap::iter`].
///
/// Similar to [`HashMap`], the iteration order is arbitrary and not guaranteed
/// to be stable.
///
/// [`BiHashMap`]: crate::BiHashMap
/// [`BiHashMap::iter`]: crate::BiHashMap::iter
/// [`HashMap`]: std::collections::HashMap
#[derive(Clone, Debug, Default)]
pub struct Iter<'a, T: BiHashItem> {
    inner: hash_map::Values<'a, usize, T>,
}

impl<'a, T: BiHashItem> Iter<'a, T> {
    pub(crate) fn new<A: Allocator>(items: &'a ItemSet<T, A>) -> Self {
        Self { inner: items.values() }
    }
}

impl<'a, T: BiHashItem> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<T: BiHashItem> ExactSizeIterator for Iter<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

// hash_map::Iter is a FusedIterator, so Iter is as well.
impl<T: BiHashItem> FusedIterator for Iter<'_, T> {}

/// An iterator over the elements of a [`BiHashMap`] by mutable reference.
/// Created by [`BiHashMap::iter_mut`].
///
/// This iterator returns [`RefMut`] instances.
///
/// Similar to [`HashMap`], the iteration order is arbitrary and not guaranteed
/// to be stable.
///
/// [`BiHashMap`]: crate::BiHashMap
/// [`BiHashMap::iter_mut`]: crate::BiHashMap::iter_mut
/// [`HashMap`]: std::collections::HashMap
#[derive(Debug)]
pub struct IterMut<
    'a,
    T: BiHashItem,
    S = DefaultHashBuilder,
    A: Allocator = Global,
> {
    tables: &'a BiHashMapTables<S, A>,
    inner: hash_map::ValuesMut<'a, usize, T>,
}

impl<'a, T: BiHashItem, S: Clone + BuildHasher, A: Allocator>
    IterMut<'a, T, S, A>
{
    pub(super) fn new(
        tables: &'a BiHashMapTables<S, A>,
        items: &'a mut ItemSet<T, A>,
    ) -> Self {
        Self { tables, inner: items.values_mut() }
    }
}

impl<'a, T: BiHashItem, S: Clone + BuildHasher, A: Allocator> Iterator
    for IterMut<'a, T, S, A>
{
    type Item = RefMut<'a, T, S>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.inner.next()?;
        let hashes = self.tables.make_hashes::<T>(&next.key1(), &next.key2());
        Some(RefMut::new(self.tables.state.clone(), hashes, next))
    }
}

impl<T: BiHashItem, S: Clone + BuildHasher, A: Allocator> ExactSizeIterator
    for IterMut<'_, T, S, A>
{
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

// hash_map::IterMut is a FusedIterator, so IterMut is as well.
impl<T: BiHashItem, S: Clone + BuildHasher, A: Allocator> FusedIterator
    for IterMut<'_, T, S, A>
{
}

/// An iterator over the elements of a [`BiHashMap`] by ownership. Created by
/// [`BiHashMap::into_iter`].
///
/// Similar to [`HashMap`], the iteration order is arbitrary and not guaranteed
/// to be stable.
///
/// [`BiHashMap`]: crate::BiHashMap
/// [`BiHashMap::into_iter`]: crate::BiHashMap::into_iter
/// [`HashMap`]: std::collections::HashMap
#[derive(Debug)]
pub struct IntoIter<T: BiHashItem, A: Allocator = Global> {
    inner: hash_map::IntoValues<usize, T, AllocWrapper<A>>,
}

impl<T: BiHashItem, A: Allocator> IntoIter<T, A> {
    pub(crate) fn new(items: ItemSet<T, A>) -> Self {
        Self { inner: items.into_values() }
    }
}

impl<T: BiHashItem, A: Allocator> Iterator for IntoIter<T, A> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<T: BiHashItem, A: Allocator> ExactSizeIterator for IntoIter<T, A> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

// hash_map::IterMut is a FusedIterator, so IterMut is as well.
impl<T: BiHashItem, A: Allocator> FusedIterator for IntoIter<T, A> {}
