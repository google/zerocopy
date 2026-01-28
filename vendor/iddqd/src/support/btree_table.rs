//! A "table" of b-tree-based indexes.
//!
//! Similar to [`super::hash_table::MapHashTable`], b-tree based tables store
//! integers (that are indexes corresponding to items), but use an external
//! comparator.

use super::map_hash::MapHash;
use crate::internal::{TableValidationError, ValidateCompact};
use alloc::{
    collections::{BTreeSet, btree_set},
    vec::Vec,
};
use core::{
    cell::Cell,
    cmp::Ordering,
    hash::{BuildHasher, Hash},
    marker::PhantomData,
};
use equivalent::Comparable;

thread_local! {
    /// Stores an external comparator function to provide dynamic scoping.
    ///
    /// std's BTreeMap doesn't allow passing an external comparator, so we make
    /// do with this function that's passed in through dynamic scoping.
    ///
    /// This works by:
    ///
    /// * We store an `Index` in the BTreeSet which knows how to call this
    ///   dynamic comparator.
    /// * When we need to compare two `Index` values, we create a CmpDropGuard.
    ///   This struct is responsible for managing the lifetime of the
    ///   comparator.
    /// * When the CmpDropGuard is dropped (including due to a panic), we reset
    ///   the comparator to None.
    ///
    /// This is not great! (For one, thread-locals and no-std don't really mix.)
    /// Some alternatives:
    ///
    /// * Using `Borrow` as described in
    ///   https://github.com/sunshowers-code/borrow-complex-key-example. While
    ///   hacky, this actually works for the find operation. But the insert
    ///   operation currently requires a concrete `Index`.
    ///
    ///   If and when https://github.com/rust-lang/rust/issues/133549 lands,
    ///   this should become a viable option. Worth looking out for!
    ///
    /// * Using a third-party BTreeSet implementation that allows passing in
    ///   external comparators. As of 2025-05, there appear to be two options:
    ///
    ///   1. copse (https://docs.rs/copse), which doesn't seem like a good fit
    ///      here.
    ///   2. btree_monstrousity (https://crates.io/crates/btree_monstrousity),
    ///      which has an API perfect for this but is, uhh, not really
    ///      production-ready.
    ///
    ///   Third-party implementations also run the risk of being relatively
    ///   untested.
    ///
    /// * Using some other kind of sorted set. We've picked B-trees here as the
    ///   default choice to balance cache locality, but other options are worth
    ///   benchmarking. We do need to provide a comparator, though, so radix
    ///   trees and such are out of the question.
    static CMP: Cell<Option<&'static dyn Fn(Index, Index) -> Ordering>>
        = const { Cell::new(None) };
}

/// A B-tree-based table with an external comparator.
#[derive(Clone, Debug, Default)]
pub(crate) struct MapBTreeTable {
    items: BTreeSet<Index>,
    // We use foldhash directly here because we allow compiling with std but
    // without the default-hasher. std turns on foldhash but not the default
    // hasher.
    hash_state: foldhash::fast::FixedState,
}

impl MapBTreeTable {
    pub(crate) const fn new() -> Self {
        Self {
            items: BTreeSet::new(),
            // FixedState::with_seed XORs the passed in seed with a fixed
            // high-entropy value.
            hash_state: foldhash::fast::FixedState::with_seed(0),
        }
    }

    #[doc(hidden)]
    pub(crate) fn len(&self) -> usize {
        self.items.len()
    }

    #[doc(hidden)]
    pub(crate) fn validate(
        &self,
        expected_len: usize,
        compactness: ValidateCompact,
    ) -> Result<(), TableValidationError> {
        if self.len() != expected_len {
            return Err(TableValidationError::new(format!(
                "expected length {expected_len}, was {}",
                self.len(),
            )));
        }

        match compactness {
            ValidateCompact::Compact => {
                // All items between 0 (inclusive) and self.len() (exclusive)
                // are present, and there are no duplicates. Also, the sentinel
                // value should not be stored.
                let mut indexes: Vec<_> = Vec::with_capacity(expected_len);
                for index in &self.items {
                    match index.0 {
                        Index::SENTINEL_VALUE => {
                            return Err(TableValidationError::new(
                                "sentinel value should not be stored in map",
                            ));
                        }
                        v => {
                            indexes.push(v);
                        }
                    }
                }
                indexes.sort_unstable();
                for (i, index) in indexes.iter().enumerate() {
                    if *index != i {
                        return Err(TableValidationError::new(format!(
                            "value at index {i} should be {i}, was {index}",
                        )));
                    }
                }
            }
            ValidateCompact::NonCompact => {
                // There should be no duplicates, and the sentinel value
                // should not be stored.
                let indexes: Vec<_> = self.items.iter().copied().collect();
                let index_set: BTreeSet<usize> =
                    indexes.iter().map(|ix| ix.0).collect();
                if index_set.len() != indexes.len() {
                    return Err(TableValidationError::new(format!(
                        "expected no duplicates, but found {} duplicates \
                         (values: {:?})",
                        indexes.len() - index_set.len(),
                        indexes,
                    )));
                }
                if index_set.contains(&Index::SENTINEL_VALUE) {
                    return Err(TableValidationError::new(
                        "sentinel value should not be stored in map",
                    ));
                }
            }
        }

        Ok(())
    }

    #[inline]
    pub(crate) fn first(&self) -> Option<usize> {
        self.items.first().map(|ix| ix.0)
    }

    #[inline]
    pub(crate) fn last(&self) -> Option<usize> {
        self.items.last().map(|ix| ix.0)
    }

    pub(crate) fn find_index<K, Q, F>(
        &self,
        key: &Q,
        lookup: F,
    ) -> Option<usize>
    where
        K: Ord,
        Q: ?Sized + Comparable<K>,
        F: Fn(usize) -> K,
    {
        let f = find_cmp(key, lookup);

        let guard = CmpDropGuard::new(&f);

        let ret = match self.items.get(&Index::SENTINEL) {
            Some(Index(v)) if *v == Index::SENTINEL_VALUE => {
                panic!("internal map shouldn't store sentinel value")
            }
            Some(Index(v)) => Some(*v),
            None => {
                // The key is not in the table.
                None
            }
        };

        // drop(guard) isn't necessary, but we make it explicit
        drop(guard);
        ret
    }

    pub(crate) fn insert<K, Q, F>(&mut self, index: usize, key: &Q, lookup: F)
    where
        K: Ord,
        Q: ?Sized + Comparable<K>,
        F: Fn(usize) -> K,
    {
        let f = insert_cmp(index, key, lookup);
        let guard = CmpDropGuard::new(&f);

        self.items.insert(Index::new(index));

        // drop(guard) isn't necessary, but we make it explicit
        drop(guard);
    }

    pub(crate) fn remove<K, F>(&mut self, index: usize, key: K, lookup: F)
    where
        F: Fn(usize) -> K,
        K: Ord,
    {
        let f = insert_cmp(index, &key, lookup);
        let guard = CmpDropGuard::new(&f);

        self.items.remove(&Index::new(index));

        // drop(guard) isn't necessary, but we make it explicit
        drop(guard);
    }

    pub(crate) fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(usize) -> bool,
    {
        // We don't need to set up a comparator in the environment because
        // `retain` doesn't do any comparisons as part of its operation.
        self.items.retain(|index| f(index.0));
    }

    /// Clears the B-tree table, removing all items.
    #[inline]
    pub(crate) fn clear(&mut self) {
        self.items.clear();
    }

    pub(crate) fn iter(&self) -> Iter<'_> {
        Iter::new(self.items.iter())
    }

    pub(crate) fn into_iter(self) -> IntoIter {
        IntoIter::new(self.items.into_iter())
    }

    pub(crate) fn state(&self) -> &foldhash::fast::FixedState {
        &self.hash_state
    }

    pub(crate) fn compute_hash<K: Hash>(&self, key: K) -> MapHash {
        MapHash { hash: self.hash_state.hash_one(key) }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Iter<'a> {
    inner: btree_set::Iter<'a, Index>,
}

impl<'a> Iter<'a> {
    fn new(inner: btree_set::Iter<'a, Index>) -> Self {
        Self { inner }
    }

    pub(crate) fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|index| index.0)
    }
}

#[derive(Debug)]
pub(crate) struct IntoIter {
    inner: btree_set::IntoIter<Index>,
}

impl IntoIter {
    fn new(inner: btree_set::IntoIter<Index>) -> Self {
        Self { inner }
    }
}

impl Iterator for IntoIter {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|index| index.0)
    }
}

fn find_cmp<'a, K, Q, F>(
    key: &'a Q,
    lookup: F,
) -> impl Fn(Index, Index) -> Ordering + 'a
where
    Q: ?Sized + Comparable<K>,
    F: 'a + Fn(usize) -> K,
    K: Ord,
{
    move |a: Index, b: Index| {
        if a.0 == b.0 {
            // This is potentially load-bearing! It means that even if the Eq
            // implementation on map items is wrong, we treat items at the same
            // index as equal.
            //
            // Unsafe code relies on this to ensure that we don't return
            // multiple mutable references to the same index.
            return Ordering::Equal;
        }
        match (a.0, b.0) {
            (Index::SENTINEL_VALUE, v) => key.compare(&lookup(v)),
            (v, Index::SENTINEL_VALUE) => key.compare(&lookup(v)).reverse(),
            (a, b) => lookup(a).cmp(&lookup(b)),
        }
    }
}

fn insert_cmp<'a, K, Q, F>(
    index: usize,
    key: &'a Q,
    lookup: F,
) -> impl Fn(Index, Index) -> Ordering + 'a
where
    Q: ?Sized + Comparable<K>,
    F: 'a + Fn(usize) -> K,
    K: Ord,
{
    move |a: Index, b: Index| {
        if a.0 == b.0 {
            // This is potentially load-bearing! It means that even if the Eq
            // implementation on map items is wrong, we treat items at the same
            // index as equal.
            //
            // Unsafe code relies on this to ensure that we don't return
            // multiple mutable references to the same index.
            return Ordering::Equal;
        }
        match (a.0, b.0) {
            // The sentinel value should not be invoked at all, because it's not
            // passed in during insert and not stored in the table.
            (Index::SENTINEL_VALUE, _) | (_, Index::SENTINEL_VALUE) => {
                panic!("sentinel value should not be invoked in insert path")
            }
            (a, b) if a == index => key.compare(&lookup(b)),
            (a, b) if b == index => key.compare(&lookup(a)).reverse(),
            (a, b) => lookup(a).cmp(&lookup(b)),
        }
    }
}

struct CmpDropGuard<'a> {
    _marker: PhantomData<&'a ()>,
}

impl<'a> CmpDropGuard<'a> {
    fn new(f: &'a dyn Fn(Index, Index) -> Ordering) -> Self {
        // CMP lasts only as long as this function and is immediately reset to
        // None once this scope is left.
        let ret = Self { _marker: PhantomData };

        // SAFETY: This is safe because we are not storing the reference
        // anywhere, and it is only used for the lifetime of this CmpDropGuard.
        let as_static = unsafe {
            std::mem::transmute::<
                &'a dyn Fn(Index, Index) -> Ordering,
                &'static dyn Fn(Index, Index) -> Ordering,
            >(f)
        };
        CMP.set(Some(as_static));

        ret
    }
}

impl Drop for CmpDropGuard<'_> {
    fn drop(&mut self) {
        CMP.set(None);
    }
}

#[derive(Clone, Copy, Debug)]
struct Index(usize);

impl Index {
    const SENTINEL_VALUE: usize = usize::MAX;
    const SENTINEL: Self = Self(Self::SENTINEL_VALUE);

    #[inline]
    fn new(value: usize) -> Self {
        if value == Self::SENTINEL_VALUE {
            panic!("btree map overflow, index with value {value:?} was added")
        }
        Self(value)
    }
}

impl PartialEq for Index {
    fn eq(&self, other: &Self) -> bool {
        // For non-sentinel indexes, two values are the same iff their indexes
        // are the same. This is ensured by the fact that our key types
        // implement Eq (as part of implementing Ord).
        if self.0 != Self::SENTINEL_VALUE && other.0 != Self::SENTINEL_VALUE {
            return self.0 == other.0;
        }

        // If any of the two indexes is the sentinel, we're required to perform
        // a lookup.
        CMP.with(|cmp| {
            let cmp = cmp.get().expect("cmp should be set");
            cmp(*self, *other) == Ordering::Equal
        })
    }
}

impl Eq for Index {}

impl Ord for Index {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        // Ord should only be called if we're doing lookups within the table,
        // which should have set the thread local.
        CMP.with(|cmp| {
            let cmp = cmp.get().expect("cmp should be set");
            cmp(*self, *other)
        })
    }
}

impl PartialOrd for Index {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
