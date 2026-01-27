use super::{IdOrdItem, RefMut, tables::IdOrdMapTables};
use crate::support::{
    alloc::Global, borrow::DormantMutRef, btree_table, item_set::ItemSet,
};
use core::{hash::Hash, iter::FusedIterator};

/// An iterator over the elements of an [`IdOrdMap`] by shared reference.
///
/// Created by [`IdOrdMap::iter`], and ordered by keys.
///
/// [`IdOrdMap`]: crate::IdOrdMap
/// [`IdOrdMap::iter`]: crate::IdOrdMap::iter
#[derive(Clone, Debug)]
pub struct Iter<'a, T: IdOrdItem> {
    items: &'a ItemSet<T, Global>,
    iter: btree_table::Iter<'a>,
}

impl<'a, T: IdOrdItem> Iter<'a, T> {
    pub(super) fn new(
        items: &'a ItemSet<T, Global>,
        tables: &'a IdOrdMapTables,
    ) -> Self {
        Self { items, iter: tables.key_to_item.iter() }
    }
}

impl<'a, T: IdOrdItem> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let index = self.iter.next()?;
        Some(&self.items[index])
    }
}

impl<T: IdOrdItem> ExactSizeIterator for Iter<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

// btree_set::Iter is a FusedIterator, so Iter is as well.
impl<T: IdOrdItem> FusedIterator for Iter<'_, T> {}

/// An iterator over the elements of a [`IdOrdMap`] by mutable reference.
///
/// This iterator returns [`RefMut`] instances.
///
/// Created by [`IdOrdMap::iter_mut`], and ordered by keys.
///
/// [`IdOrdMap`]: crate::IdOrdMap
/// [`IdOrdMap::iter_mut`]: crate::IdOrdMap::iter_mut
#[derive(Debug)]
pub struct IterMut<'a, T: IdOrdItem>
where
    T::Key<'a>: Hash,
{
    items: &'a mut ItemSet<T, Global>,
    tables: &'a IdOrdMapTables,
    iter: btree_table::Iter<'a>,
}

impl<'a, T: IdOrdItem> IterMut<'a, T>
where
    T::Key<'a>: Hash,
{
    pub(super) fn new(
        items: &'a mut ItemSet<T, Global>,
        tables: &'a IdOrdMapTables,
    ) -> Self {
        Self { items, tables, iter: tables.key_to_item.iter() }
    }
}

impl<'a, T: IdOrdItem + 'a> Iterator for IterMut<'a, T>
where
    T::Key<'a>: Hash,
{
    type Item = RefMut<'a, T>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let index = self.iter.next()?;

        let item = &mut self.items[index];

        // SAFETY: This lifetime extension from self to 'a is safe based on two
        // things:
        //
        // 1. We never repeat indexes, i.e. for an index i, once we've handed
        //    out an item at i, creating `&mut T`, we'll never get the index i
        //    again. (This is guaranteed from the set-based nature of the
        //    iterator.) This means that we don't ever create a mutable alias to
        //    the same memory.
        //
        //    In particular, unlike all the other places we look up data from a
        //    btree table, we don't pass a lookup function into
        //    self.iter.next(). If we did, then it is possible the lookup
        //    function would have been called with an old index i. But we don't
        //    need to do that.
        //
        // 2. All mutable references to data within self.items are derived from
        //    self.items. So, the rule described at [1] is upheld:
        //
        //    > When creating a mutable reference, then while this reference
        //    > exists, the memory it points to must not get accessed (read or
        //    > written) through any other pointer or reference not derived from
        //    > this reference.
        //
        // [1]:
        //     https://doc.rust-lang.org/std/ptr/index.html#pointer-to-reference-conversion
        let item = unsafe { core::mem::transmute::<&mut T, &'a mut T>(item) };

        let (hash, dormant) = {
            let (item, dormant) = DormantMutRef::new(item);
            let hash = self.tables.make_hash(item);
            (hash, dormant)
        };

        // SAFETY: item is dropped above, and self is no longer used after this
        // point.
        let item = unsafe { dormant.awaken() };

        Some(RefMut::new(self.tables.state().clone(), hash, item))
    }
}

impl<'a, T: IdOrdItem + 'a> ExactSizeIterator for IterMut<'a, T>
where
    T::Key<'a>: Hash,
{
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

// hash_map::IterMut is a FusedIterator, so IterMut is as well.
impl<'a, T: IdOrdItem + 'a> FusedIterator for IterMut<'a, T> where
    T::Key<'a>: Hash
{
}

/// An iterator over the elements of a [`IdOrdMap`] by ownership.
///
/// Created by [`IdOrdMap::into_iter`], and ordered by keys.
///
/// [`IdOrdMap`]: crate::IdOrdMap
/// [`IdOrdMap::into_iter`]: crate::IdOrdMap::into_iter
#[derive(Debug)]
pub struct IntoIter<T: IdOrdItem> {
    items: ItemSet<T, Global>,
    iter: btree_table::IntoIter,
}

impl<T: IdOrdItem> IntoIter<T> {
    pub(super) fn new(
        items: ItemSet<T, Global>,
        tables: IdOrdMapTables,
    ) -> Self {
        Self { items, iter: tables.key_to_item.into_iter() }
    }
}

impl<T: IdOrdItem> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let index = self.iter.next()?;
        let next = self
            .items
            .remove(index)
            .unwrap_or_else(|| panic!("index {index} not found in items"));
        Some(next)
    }
}
