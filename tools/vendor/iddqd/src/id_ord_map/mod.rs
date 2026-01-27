//! An ordered map where the keys are part of the values, based on a B-Tree.
//!
//! For more information, see [`IdOrdMap`].

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
pub use imp::IdOrdMap;
pub use iter::{IntoIter, Iter, IterMut};
#[cfg(feature = "proptest")]
pub use proptest_impls::{IdOrdMapStrategy, IdOrdMapValueTree, prop_strategy};
pub use ref_mut::RefMut;
#[cfg(feature = "serde")]
pub use serde_impls::IdOrdMapAsMap;
pub use trait_defs::IdOrdItem;
