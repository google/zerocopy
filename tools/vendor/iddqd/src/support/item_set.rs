use super::alloc::AllocWrapper;
use crate::{
    internal::{ValidateCompact, ValidationError},
    support::alloc::{Allocator, Global, global_alloc},
};
use core::{
    fmt,
    ops::{Index, IndexMut},
};
use hashbrown::{HashMap, hash_map};
use rustc_hash::FxBuildHasher;

/// A map of items stored by integer index.
#[derive(Clone)]
pub(crate) struct ItemSet<T, A: Allocator> {
    // rustc-hash's FxHashMap is custom-designed for compact-ish integer keys.
    items: HashMap<usize, T, FxBuildHasher, AllocWrapper<A>>,
    // The next index to use. This only ever goes up, not down.
    //
    // An alternative might be to use a free list of indexes, but that's
    // unnecessarily complex.
    next_index: usize,
}

impl<T: fmt::Debug, A: Allocator> fmt::Debug for ItemSet<T, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ItemSet")
            .field("items", &self.items)
            .field("next_index", &self.next_index)
            .finish()
    }
}

impl<T> ItemSet<T, Global> {
    #[inline]
    pub(crate) const fn new() -> Self {
        Self::new_in(global_alloc())
    }
}

impl<T, A: Allocator> ItemSet<T, A> {
    #[inline]
    pub(crate) const fn new_in(alloc: A) -> Self {
        Self {
            items: HashMap::with_hasher_in(FxBuildHasher, AllocWrapper(alloc)),
            next_index: 0,
        }
    }

    pub(crate) fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self {
            items: HashMap::with_capacity_and_hasher_in(
                capacity,
                Default::default(),
                AllocWrapper(alloc),
            ),
            next_index: 0,
        }
    }

    pub(crate) fn allocator(&self) -> &A {
        &self.items.allocator().0
    }

    /// Validates the item set.
    pub(crate) fn validate(
        &self,
        compactness: ValidateCompact,
    ) -> Result<(), ValidationError> {
        // If the map is expected to be compact, then ensure that all keys
        // between 0 and next_index are present.
        match compactness {
            ValidateCompact::Compact => {
                for i in 0..self.next_index {
                    if !self.items.contains_key(&i) {
                        return Err(ValidationError::General(format!(
                            "ItemSet is not compact: missing index {i}"
                        )));
                    }
                }
            }
            ValidateCompact::NonCompact => {
                // No real checks can be done in this case.
            }
        }

        Ok(())
    }

    pub(crate) fn capacity(&self) -> usize {
        self.items.capacity()
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.items.len()
    }

    #[inline]
    pub(crate) fn iter(&self) -> hash_map::Iter<'_, usize, T> {
        self.items.iter()
    }

    #[inline]
    #[expect(dead_code)]
    pub(crate) fn iter_mut(&mut self) -> hash_map::IterMut<'_, usize, T> {
        self.items.iter_mut()
    }

    #[inline]
    pub(crate) fn values(&self) -> hash_map::Values<'_, usize, T> {
        self.items.values()
    }

    #[inline]
    pub(crate) fn values_mut(&mut self) -> hash_map::ValuesMut<'_, usize, T> {
        self.items.values_mut()
    }

    #[inline]
    pub(crate) fn into_values(
        self,
    ) -> hash_map::IntoValues<usize, T, AllocWrapper<A>> {
        self.items.into_values()
    }

    #[inline]
    pub(crate) fn get(&self, index: usize) -> Option<&T> {
        self.items.get(&index)
    }

    #[inline]
    pub(crate) fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.items.get_mut(&index)
    }

    #[inline]
    pub(crate) fn get_disjoint_mut<const N: usize>(
        &mut self,
        indexes: [&usize; N],
    ) -> [Option<&mut T>; N] {
        self.items.get_many_mut(indexes)
    }

    // This is only used by IdOrdMap.
    #[cfg_attr(not(feature = "std"), expect(dead_code))]
    #[inline]
    pub(crate) fn next_index(&self) -> usize {
        self.next_index
    }

    #[inline]
    pub(crate) fn insert_at_next_index(&mut self, value: T) -> usize {
        let index = self.next_index;
        self.items.insert(index, value);
        self.next_index += 1;
        index
    }

    #[inline]
    pub(crate) fn remove(&mut self, index: usize) -> Option<T> {
        let entry = self.items.remove(&index);
        if entry.is_some() && index == self.next_index - 1 {
            // If we removed the last entry, decrement next_index. Not strictly
            // necessary but a nice optimization.
            //
            // This does not guarantee compactness, since it's possible for the
            // following set of operations to occur:
            //
            // 0. start at next_index = 0
            // 1. insert 0, next_index = 1
            // 2. insert 1, next_index = 2
            // 3. remove 0, next_index = 2
            // 4. remove 1, next_index = 1 (not 0, even though the map is empty)
            //
            // Compactness would require a heap acting as a free list. But that
            // seems generally unnecessary.
            self.next_index -= 1;
        }
        entry
    }

    /// Clears the item set, removing all items.
    #[inline]
    pub(crate) fn clear(&mut self) {
        self.items.clear();
        self.next_index = 0;
    }

    // This method assumes that value has the same ID. It also asserts that
    // `index` is valid (and panics if it isn't).
    #[inline]
    pub(crate) fn replace(&mut self, index: usize, value: T) -> T {
        self.items
            .insert(index, value)
            .unwrap_or_else(|| panic!("EntrySet index not found: {index}"))
    }

    /// Reserves capacity for at least `additional` more items.
    #[inline]
    pub(crate) fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional);
    }

    /// Shrinks the capacity of the item set as much as possible.
    #[inline]
    pub(crate) fn shrink_to_fit(&mut self) {
        self.items.shrink_to_fit();
    }

    /// Shrinks the capacity of the item set with a lower limit.
    #[inline]
    pub(crate) fn shrink_to(&mut self, min_capacity: usize) {
        self.items.shrink_to(min_capacity);
    }

    /// Tries to reserve capacity for at least `additional` more items.
    #[inline]
    pub(crate) fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), hashbrown::TryReserveError> {
        self.items.try_reserve(additional)
    }
}

#[cfg(feature = "serde")]
mod serde_impls {
    use super::ItemSet;
    use crate::support::alloc::Allocator;
    use serde_core::{Serialize, Serializer};

    impl<T: Serialize, A: Allocator> Serialize for ItemSet<T, A> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            // Serialize just the items -- don't serialize the map keys. We'll
            // rebuild the map keys on deserialization.
            serializer.collect_seq(self.items.values())
        }
    }
}

impl<T, A: Allocator> Index<usize> for ItemSet<T, A> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.items
            .get(&index)
            .unwrap_or_else(|| panic!("ItemSet index not found: {index}"))
    }
}

impl<T, A: Allocator> IndexMut<usize> for ItemSet<T, A> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.items
            .get_mut(&index)
            .unwrap_or_else(|| panic!("ItemSet index not found: {index}"))
    }
}
