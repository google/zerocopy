use crate::{
    IdHashItem,
    internal::{ValidateCompact, ValidationError},
    support::{alloc::Allocator, hash_table::MapHashTable, map_hash::MapHash},
};
use core::hash::BuildHasher;

#[derive(Clone, Debug, Default)]
pub(super) struct IdHashMapTables<S, A: Allocator> {
    pub(super) state: S,
    pub(super) key_to_item: MapHashTable<A>,
}

impl<S: BuildHasher, A: Allocator> IdHashMapTables<S, A> {
    #[cfg(feature = "daft")]
    pub(crate) fn hasher(&self) -> &S {
        &self.state
    }

    pub(super) const fn with_hasher_in(hasher: S, alloc: A) -> Self {
        Self { state: hasher, key_to_item: MapHashTable::new_in(alloc) }
    }

    pub(super) fn with_capacity_and_hasher_in(
        capacity: usize,
        hasher: S,
        alloc: A,
    ) -> Self {
        Self {
            state: hasher,
            key_to_item: MapHashTable::with_capacity_in(capacity, alloc),
        }
    }

    pub(super) fn validate(
        &self,
        expected_len: usize,
        compactness: ValidateCompact,
    ) -> Result<(), ValidationError> {
        self.key_to_item.validate(expected_len, compactness).map_err(
            |error| ValidationError::Table { name: "key_to_table", error },
        )?;

        Ok(())
    }

    pub(super) fn make_hash<T: IdHashItem>(&self, item: &T) -> MapHash {
        let k1 = item.key();
        self.key_to_item.compute_hash(&self.state, k1)
    }

    pub(super) fn make_key_hash<T: IdHashItem>(
        &self,
        key: &T::Key<'_>,
    ) -> MapHash {
        self.key_to_item.compute_hash(&self.state, key)
    }
}
