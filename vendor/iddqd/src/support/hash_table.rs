//! A wrapper around a hash table with some random state.

use super::{
    alloc::{AllocWrapper, Allocator},
    map_hash::MapHash,
};
use crate::internal::{TableValidationError, ValidateCompact};
use alloc::{collections::BTreeSet, vec::Vec};
use core::{
    borrow::Borrow,
    fmt,
    hash::{BuildHasher, Hash},
};
use equivalent::Equivalent;
use hashbrown::{
    HashTable,
    hash_table::{AbsentEntry, Entry, OccupiedEntry},
};

#[derive(Clone, Default)]
pub(crate) struct MapHashTable<A: Allocator> {
    pub(super) items: HashTable<usize, AllocWrapper<A>>,
}

impl<A: Allocator> fmt::Debug for MapHashTable<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MapHashTable").field("items", &self.items).finish()
    }
}

impl<A: Allocator> MapHashTable<A> {
    pub(crate) const fn new_in(alloc: A) -> Self {
        Self { items: HashTable::new_in(AllocWrapper(alloc)) }
    }

    pub(crate) fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self {
            items: HashTable::with_capacity_in(capacity, AllocWrapper(alloc)),
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.items.len()
    }

    pub(crate) fn validate(
        &self,
        expected_len: usize,
        compactness: ValidateCompact,
    ) -> Result<(), TableValidationError> {
        if self.len() != expected_len {
            return Err(TableValidationError::new(format!(
                "expected length {expected_len}, was {}",
                self.len()
            )));
        }

        match compactness {
            ValidateCompact::Compact => {
                // All items between 0 (inclusive) and self.len() (exclusive)
                // are expected to be present, and there are no duplicates.
                let mut values: Vec<_> = self.items.iter().copied().collect();
                values.sort_unstable();
                for (i, value) in values.iter().enumerate() {
                    if *value != i {
                        return Err(TableValidationError::new(format!(
                            "expected value at index {i} to be {i}, was {value}"
                        )));
                    }
                }
            }
            ValidateCompact::NonCompact => {
                // There should be no duplicates.
                let values: Vec<_> = self.items.iter().copied().collect();
                let value_set: BTreeSet<_> = values.iter().copied().collect();
                if value_set.len() != values.len() {
                    return Err(TableValidationError::new(format!(
                        "expected no duplicates, but found {} duplicates \
                         (values: {:?})",
                        values.len() - value_set.len(),
                        values,
                    )));
                }
            }
        }

        Ok(())
    }

    pub(crate) fn compute_hash<S: BuildHasher, K: Hash + Eq>(
        &self,
        state: &S,
        key: K,
    ) -> MapHash {
        MapHash { hash: state.hash_one(key) }
    }

    // Ensure that K has a consistent hash.
    pub(crate) fn find_index<S: BuildHasher, K, Q, F>(
        &self,
        state: &S,
        key: &Q,
        lookup: F,
    ) -> Option<usize>
    where
        F: Fn(usize) -> K,
        Q: ?Sized + Hash + Equivalent<K>,
    {
        let hash = state.hash_one(key);
        self.items.find(hash, |index| key.equivalent(&lookup(*index))).copied()
    }

    pub(crate) fn entry<S: BuildHasher, K: Hash + Eq, F>(
        &mut self,
        state: &S,
        key: K,
        lookup: F,
    ) -> Entry<'_, usize, AllocWrapper<A>>
    where
        F: Fn(usize) -> K,
    {
        let hash = state.hash_one(&key);
        self.items.entry(
            hash,
            |index| lookup(*index) == key,
            |v| state.hash_one(lookup(*v)),
        )
    }

    pub(crate) fn find_entry<S: BuildHasher, K, Q, F>(
        &mut self,
        state: &S,
        key: &Q,
        lookup: F,
    ) -> Result<
        OccupiedEntry<'_, usize, AllocWrapper<A>>,
        AbsentEntry<'_, usize, AllocWrapper<A>>,
    >
    where
        F: Fn(usize) -> K,
        K: Hash + Eq + Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        let hash = state.hash_one(key);
        self.items.find_entry(hash, |index| lookup(*index).borrow() == key)
    }

    pub(crate) fn find_entry_by_hash<F>(
        &mut self,
        hash: u64,
        mut f: F,
    ) -> Result<
        OccupiedEntry<'_, usize, AllocWrapper<A>>,
        AbsentEntry<'_, usize, AllocWrapper<A>>,
    >
    where
        F: FnMut(usize) -> bool,
    {
        self.items.find_entry(hash, |index| f(*index))
    }

    pub(crate) fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(usize) -> bool,
    {
        self.items.retain(|index| f(*index));
    }

    /// Clears the hash table, removing all items.
    #[inline]
    pub(crate) fn clear(&mut self) {
        self.items.clear();
    }

    /// Reserves capacity for at least `additional` more items.
    #[inline]
    pub(crate) fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional, |_| 0);
    }

    /// Shrinks the capacity of the hash table as much as possible.
    #[inline]
    pub(crate) fn shrink_to_fit(&mut self) {
        self.items.shrink_to_fit(|_| 0);
    }

    /// Shrinks the capacity of the hash table with a lower limit.
    #[inline]
    pub(crate) fn shrink_to(&mut self, min_capacity: usize) {
        self.items.shrink_to(min_capacity, |_| 0);
    }

    /// Tries to reserve capacity for at least `additional` more items.
    #[inline]
    pub(crate) fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), hashbrown::TryReserveError> {
        self.items.try_reserve(additional, |_| 0)
    }
}
