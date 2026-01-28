use crate::{
    BiHashItem,
    internal::{ValidateCompact, ValidationError},
    support::{
        alloc::{Allocator, Global, global_alloc},
        hash_table::MapHashTable,
        map_hash::MapHash,
    },
};
use core::hash::BuildHasher;

#[derive(Clone, Debug, Default)]
pub(super) struct BiHashMapTables<S, A: Allocator> {
    pub(super) state: S,
    pub(super) k1_to_item: MapHashTable<A>,
    pub(super) k2_to_item: MapHashTable<A>,
}

impl<S: BuildHasher> BiHashMapTables<S, Global> {
    pub(super) const fn with_hasher(hasher: S) -> Self {
        Self {
            state: hasher,
            k1_to_item: MapHashTable::new_in(global_alloc()),
            k2_to_item: MapHashTable::new_in(global_alloc()),
        }
    }
}

impl<S: BuildHasher, A: Clone + Allocator> BiHashMapTables<S, A> {
    pub(super) fn with_capacity_and_hasher_in(
        capacity: usize,
        hasher: S,
        alloc: A,
    ) -> Self {
        Self {
            state: hasher,
            k1_to_item: MapHashTable::with_capacity_in(capacity, alloc.clone()),
            k2_to_item: MapHashTable::with_capacity_in(capacity, alloc),
        }
    }
}

impl<S: Clone + BuildHasher, A: Allocator> BiHashMapTables<S, A> {
    #[cfg(feature = "daft")]
    pub(super) fn hasher(&self) -> &S {
        &self.state
    }

    pub(super) fn validate(
        &self,
        expected_len: usize,
        compactness: ValidateCompact,
    ) -> Result<(), ValidationError> {
        // Check that all the maps are of the right size.
        self.k1_to_item.validate(expected_len, compactness).map_err(
            |error| ValidationError::Table { name: "k1_to_table", error },
        )?;
        self.k2_to_item.validate(expected_len, compactness).map_err(
            |error| ValidationError::Table { name: "k2_to_table", error },
        )?;

        Ok(())
    }

    pub(super) fn make_hashes<T: BiHashItem>(
        &self,
        k1: &T::K1<'_>,
        k2: &T::K2<'_>,
    ) -> [MapHash; 2] {
        let h1 = self.k1_to_item.compute_hash(&self.state, k1);
        let h2 = self.k2_to_item.compute_hash(&self.state, k2);

        [h1, h2]
    }
}
