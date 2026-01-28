//! A hash map where keys are part of the values.
//!
//! For more information, see [`IdHashMap`].

#[cfg(feature = "daft")]
mod daft_impls;
mod entry;
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
pub use daft_impls::Diff;
pub use entry::{Entry, OccupiedEntry, VacantEntry};
pub use imp::IdHashMap;
pub use iter::{IntoIter, Iter, IterMut};
#[cfg(all(feature = "proptest", feature = "default-hasher"))]
pub use proptest_impls::prop_strategy;
#[cfg(feature = "proptest")]
pub use proptest_impls::{
    IdHashMapStrategy, IdHashMapValueTree, prop_strategy_with_hasher,
    prop_strategy_with_hasher_in,
};
pub use ref_mut::RefMut;
#[cfg(feature = "serde")]
pub use serde_impls::IdHashMapAsMap;
pub use trait_defs::IdHashItem;
