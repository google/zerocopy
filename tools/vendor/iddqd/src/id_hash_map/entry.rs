use super::{IdHashItem, IdHashMap, RefMut};
use crate::{
    DefaultHashBuilder,
    support::{
        alloc::{Allocator, Global},
        borrow::DormantMutRef,
        map_hash::MapHash,
    },
};
use core::{fmt, hash::BuildHasher};

/// An implementation of the Entry API for [`IdHashMap`].
pub enum Entry<'a, T: IdHashItem, S = DefaultHashBuilder, A: Allocator = Global>
{
    /// A vacant entry.
    Vacant(VacantEntry<'a, T, S, A>),
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, T, S, A>),
}

impl<'a, T: IdHashItem, S, A: Allocator> fmt::Debug for Entry<'a, T, S, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Entry::Vacant(entry) => {
                f.debug_tuple("Vacant").field(entry).finish()
            }
            Entry::Occupied(entry) => {
                f.debug_tuple("Occupied").field(entry).finish()
            }
        }
    }
}

impl<'a, T: IdHashItem, S: Clone + BuildHasher, A: Allocator>
    Entry<'a, T, S, A>
{
    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns a mutable reference to the value in the entry.
    ///
    /// # Panics
    ///
    /// Panics if the key hashes to a different value than the one passed
    /// into [`IdHashMap::entry`].
    #[inline]
    pub fn or_insert(self, default: T) -> RefMut<'a, T, S> {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in the
    /// entry.
    ///
    /// # Panics
    ///
    /// Panics if the key hashes to a different value than the one passed
    /// into [`IdHashMap::entry`].
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> T>(
        self,
        default: F,
    ) -> RefMut<'a, T, S> {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    #[inline]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(RefMut<'_, T, S>),
    {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

/// A vacant entry.
pub struct VacantEntry<
    'a,
    T: IdHashItem,
    S = DefaultHashBuilder,
    A: Allocator = Global,
> {
    map: DormantMutRef<'a, IdHashMap<T, S, A>>,
    hash: MapHash,
}

impl<'a, T: IdHashItem, S, A: Allocator> fmt::Debug
    for VacantEntry<'a, T, S, A>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VacantEntry")
            .field("hash", &self.hash)
            .finish_non_exhaustive()
    }
}

impl<'a, T: IdHashItem, S: Clone + BuildHasher, A: Allocator>
    VacantEntry<'a, T, S, A>
{
    pub(super) unsafe fn new(
        map: DormantMutRef<'a, IdHashMap<T, S, A>>,
        hash: MapHash,
    ) -> Self {
        VacantEntry { map, hash }
    }

    /// Sets the entry to a new value, returning a mutable reference to the
    /// value.
    pub fn insert(self, value: T) -> RefMut<'a, T, S> {
        // SAFETY: The safety assumption behind `Self::new` guarantees that the
        // original reference to the map is not used at this point.
        let map = unsafe { self.map.awaken() };
        let state = &map.tables.state;
        if !self.hash.is_same_hash(state, value.key()) {
            panic!("key hashes do not match");
        }
        let Ok(index) = map.insert_unique_impl(value) else {
            panic!("key already present in map");
        };
        map.get_by_index_mut(index).expect("index is known to be valid")
    }

    /// Sets the value of the entry, and returns an `OccupiedEntry`.
    #[inline]
    pub fn insert_entry(mut self, value: T) -> OccupiedEntry<'a, T, S, A> {
        let index = {
            // SAFETY: The safety assumption behind `Self::new` guarantees that the
            // original reference to the map is not used at this point.
            let map = unsafe { self.map.reborrow() };
            let state = &map.tables.state;
            if !self.hash.is_same_hash(state, value.key()) {
                panic!("key hashes do not match");
            }
            let Ok(index) = map.insert_unique_impl(value) else {
                panic!("key already present in map");
            };
            index
        };

        // SAFETY: map, as well as anything that was borrowed from it, is
        // dropped once the above block exits.
        unsafe { OccupiedEntry::new(self.map, index) }
    }
}

/// A view into an occupied entry in an [`IdHashMap`]. Part of the [`Entry`]
/// enum.
pub struct OccupiedEntry<
    'a,
    T: IdHashItem,
    S = DefaultHashBuilder,
    A: Allocator = Global,
> {
    map: DormantMutRef<'a, IdHashMap<T, S, A>>,
    // index is a valid index into the map's internal hash table.
    index: usize,
}

impl<'a, T: IdHashItem, S, A: Allocator> fmt::Debug
    for OccupiedEntry<'a, T, S, A>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("index", &self.index)
            .finish_non_exhaustive()
    }
}

impl<'a, T: IdHashItem, S: Clone + BuildHasher, A: Allocator>
    OccupiedEntry<'a, T, S, A>
{
    /// # Safety
    ///
    /// After self is created, the original reference created by
    /// `DormantMutRef::new` must not be used.
    pub(super) unsafe fn new(
        map: DormantMutRef<'a, IdHashMap<T, S, A>>,
        index: usize,
    ) -> Self {
        OccupiedEntry { map, index }
    }

    /// Gets a reference to the value.
    ///
    /// If you need a reference to `T` that may outlive the destruction of the
    /// `Entry` value, see [`into_ref`](Self::into_ref).
    pub fn get(&self) -> &T {
        // SAFETY: The safety assumption behind `Self::new` guarantees that the
        // original reference to the map is not used at this point.
        unsafe { self.map.reborrow_shared() }
            .get_by_index(self.index)
            .expect("index is known to be valid")
    }

    /// Gets a mutable reference to the value.
    ///
    /// If you need a reference to `T` that may outlive the destruction of the
    /// `Entry` value, see [`into_mut`](Self::into_mut).
    pub fn get_mut(&mut self) -> RefMut<'_, T, S> {
        // SAFETY: The safety assumption behind `Self::new` guarantees that the
        // original reference to the map is not used at this point.
        unsafe { self.map.reborrow() }
            .get_by_index_mut(self.index)
            .expect("index is known to be valid")
    }

    /// Converts self into a reference to the value.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see
    /// [`get`](Self::get).
    pub fn into_ref(self) -> &'a T {
        // SAFETY: The safety assumption behind `Self::new` guarantees that the
        // original reference to the map is not used at this point.
        unsafe { self.map.awaken() }
            .get_by_index(self.index)
            .expect("index is known to be valid")
    }

    /// Converts self into a mutable reference to the value.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see
    /// [`get_mut`](Self::get_mut).
    pub fn into_mut(self) -> RefMut<'a, T, S> {
        // SAFETY: The safety assumption behind `Self::new` guarantees that the
        // original reference to the map is not used at this point.
        unsafe { self.map.awaken() }
            .get_by_index_mut(self.index)
            .expect("index is known to be valid")
    }

    /// Sets the entry to a new value, returning the old value.
    ///
    /// # Panics
    ///
    /// Panics if `value.key()` is different from the key of the entry.
    pub fn insert(&mut self, value: T) -> T {
        // SAFETY: The safety assumption behind `Self::new` guarantees that the
        // original reference to the map is not used at this point.
        //
        // Note that `replace_at_index` panics if the keys don't match.
        unsafe { self.map.reborrow() }.replace_at_index(self.index, value)
    }

    /// Takes ownership of the value from the map.
    pub fn remove(mut self) -> T {
        // SAFETY: The safety assumption behind `Self::new` guarantees that the
        // original reference to the map is not used at this point.
        unsafe { self.map.reborrow() }
            .remove_by_index(self.index)
            .expect("index is known to be valid")
    }
}
