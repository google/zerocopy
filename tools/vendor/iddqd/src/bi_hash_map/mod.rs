//! A hash map where values are uniquely indexed by two keys.
//!
//! For more information, see [`BiHashMap`].

#[cfg(feature = "daft")]
mod daft_impls;
mod entry;
mod entry_indexes;
pub(crate) mod imp;
mod iter;
#[cfg(feature = "proptest")]
mod proptest_impls;
mod ref_mut;
#[cfg(feature = "schemars08")]
mod schemars_impls;
#[cfg(feature = "serde")]
mod serde_impls;
mod tables;
pub(crate) mod trait_defs;

#[cfg(feature = "daft")]
pub use daft_impls::{ByK1, ByK2, Diff, MapLeaf};
pub use entry::{
    Entry, OccupiedEntry, OccupiedEntryMut, OccupiedEntryRef, VacantEntry,
};
pub use imp::BiHashMap;
pub use iter::{IntoIter, Iter, IterMut};
#[cfg(all(feature = "proptest", feature = "default-hasher"))]
pub use proptest_impls::prop_strategy;
#[cfg(feature = "proptest")]
pub use proptest_impls::{
    BiHashMapStrategy, BiHashMapValueTree, prop_strategy_with_hasher,
    prop_strategy_with_hasher_in,
};
pub use ref_mut::RefMut;
#[cfg(feature = "serde")]
pub use serde_impls::BiHashMapAsMap;
pub use trait_defs::BiHashItem;
