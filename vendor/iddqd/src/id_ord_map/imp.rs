use super::{
    Entry, IdOrdItem, IntoIter, Iter, IterMut, OccupiedEntry, RefMut,
    VacantEntry, tables::IdOrdMapTables,
};
use crate::{
    errors::DuplicateItem,
    internal::{ValidateChaos, ValidateCompact, ValidationError},
    support::{
        alloc::{Global, global_alloc},
        borrow::DormantMutRef,
        item_set::ItemSet,
        map_hash::MapHash,
    },
};
use alloc::collections::BTreeSet;
use core::{
    fmt,
    hash::{BuildHasher, Hash},
};
use equivalent::{Comparable, Equivalent};

/// An ordered map where the keys are part of the values, based on a B-Tree.
///
/// The storage mechanism is a fast hash table of integer indexes to items, with
/// the indexes stored in a B-Tree map.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
///
/// // Define a struct with a key.
/// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
/// struct MyItem {
///     id: String,
///     value: u32,
/// }
///
/// // Implement IdOrdItem for the struct.
/// impl IdOrdItem for MyItem {
///     // Keys can borrow from the item.
///     type Key<'a> = &'a str;
///
///     fn key(&self) -> Self::Key<'_> {
///         &self.id
///     }
///
///     id_upcast!();
/// }
///
/// // Create an IdOrdMap and insert items.
/// let mut map = IdOrdMap::new();
/// map.insert_unique(MyItem { id: "foo".to_string(), value: 42 }).unwrap();
/// map.insert_unique(MyItem { id: "bar".to_string(), value: 20 }).unwrap();
///
/// // Look up items by their keys.
/// assert_eq!(map.get("foo").unwrap().value, 42);
/// assert_eq!(map.get("bar").unwrap().value, 20);
/// assert!(map.get("baz").is_none());
/// # }
/// ```
#[derive(Clone)]
pub struct IdOrdMap<T> {
    // We don't expose an allocator trait here because it isn't stable with
    // std's BTreeMap.
    pub(super) items: ItemSet<T, Global>,
    // Invariant: the values (usize) in these tables are valid indexes into
    // `items`, and are a 1:1 mapping.
    pub(super) tables: IdOrdMapTables,
}

impl<T: IdOrdItem> Default for IdOrdMap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: IdOrdItem> IdOrdMap<T> {
    /// Creates a new, empty `IdOrdMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let map: IdOrdMap<Item> = IdOrdMap::new();
    /// assert!(map.is_empty());
    /// assert_eq!(map.len(), 0);
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self { items: ItemSet::new(), tables: IdOrdMapTables::new() }
    }

    /// Creates a new `IdOrdMap` with the given capacity.
    ///
    /// The capacity will be used to initialize the underlying hash table.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let map: IdOrdMap<Item> = IdOrdMap::with_capacity(10);
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, global_alloc()),
            tables: IdOrdMapTables::new(),
        }
    }

    /// Returns the currently allocated capacity of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let map: IdOrdMap<Item> = IdOrdMap::with_capacity(10);
    /// assert!(map.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        // There's no self.tables.capacity.
        self.items.capacity()
    }

    /// Constructs a new `IdOrdMap` from an iterator of values, rejecting
    /// duplicates.
    ///
    /// To overwrite duplicates instead, use [`IdOrdMap::from_iter`].
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let items = vec![
    ///     Item { id: "foo".to_string(), value: 42 },
    ///     Item { id: "bar".to_string(), value: 99 },
    /// ];
    ///
    /// // Successful creation with unique keys
    /// let map = IdOrdMap::from_iter_unique(items).unwrap();
    /// assert_eq!(map.len(), 2);
    /// assert_eq!(map.get("foo").unwrap().value, 42);
    ///
    /// // Error with duplicate keys
    /// let duplicate_items = vec![
    ///     Item { id: "foo".to_string(), value: 42 },
    ///     Item { id: "foo".to_string(), value: 99 },
    /// ];
    /// assert!(IdOrdMap::from_iter_unique(duplicate_items).is_err());
    /// ```
    pub fn from_iter_unique<I: IntoIterator<Item = T>>(
        iter: I,
    ) -> Result<Self, DuplicateItem<T>> {
        let mut map = IdOrdMap::new();
        for value in iter {
            // It would be nice to use insert_overwrite here, but that would
            // return a `DuplicateItem<T, &T>`, which can only be converted into
            // an owned value if T: Clone. Doing this via the Entry API means we
            // can return a `DuplicateItem<T>` without requiring T to be Clone.
            match map.entry(value.key()) {
                Entry::Occupied(entry) => {
                    let duplicate = entry.remove();
                    return Err(DuplicateItem::__internal_new(
                        value,
                        vec![duplicate],
                    ));
                }
                Entry::Vacant(entry) => {
                    entry.insert_ref(value);
                }
            }
        }

        Ok(map)
    }

    /// Returns true if the map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// assert!(!map.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Returns the number of items in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 99 }).unwrap();
    /// assert_eq!(map.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Clears the map, removing all items.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 99 }).unwrap();
    /// assert_eq!(map.len(), 2);
    ///
    /// map.clear();
    /// assert!(map.is_empty());
    /// assert_eq!(map.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.items.clear();
        self.tables.key_to_item.clear();
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `IdOrdMap`. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// Note: This only reserves capacity in the item storage. The internal
    /// [`BTreeSet`] used for key-to-item mapping does not support capacity
    /// reservation.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`isize::MAX`] bytes, and
    /// [`abort`]s the program in case of an allocation error.
    ///
    /// [`isize::MAX`]: https://doc.rust-lang.org/std/primitive.isize.html
    /// [`abort`]: https://doc.rust-lang.org/alloc/alloc/fn.handle_alloc_error.html
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map: IdOrdMap<Item> = IdOrdMap::new();
    /// map.reserve(100);
    /// assert!(map.capacity() >= 100);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional);
    }

    /// Shrinks the capacity of the map as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// Note: This only shrinks the item storage capacity. The internal
    /// [`BTreeSet`] used for key-to-item mapping does not support capacity
    /// control.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map: IdOrdMap<Item> = IdOrdMap::with_capacity(100);
    /// map.insert_unique(Item { id: "foo".to_string(), value: 1 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 2 }).unwrap();
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.items.shrink_to_fit();
    }

    /// Shrinks the capacity of the map with a lower limit. It will drop
    /// down no lower than the supplied limit while maintaining the internal
    /// rules and possibly leaving some space in accordance with the resize
    /// policy.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// Note: This only shrinks the item storage capacity. The internal
    /// [`BTreeSet`] used for key-to-item mapping does not support capacity
    /// control.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map: IdOrdMap<Item> = IdOrdMap::with_capacity(100);
    /// map.insert_unique(Item { id: "foo".to_string(), value: 1 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 2 }).unwrap();
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// map.shrink_to(0);
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.items.shrink_to(min_capacity);
    }

    /// Iterates over the items in the map.
    ///
    /// Similar to [`BTreeMap`], the iteration is ordered by [`T::Key`].
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "charlie".to_string(), value: 30 }).unwrap();
    /// map.insert_unique(Item { id: "alice".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bob".to_string(), value: 99 }).unwrap();
    ///
    /// // Iteration is ordered by key
    /// let mut iter = map.iter();
    /// let item = iter.next().unwrap();
    /// assert_eq!(item.id, "alice");
    /// let item = iter.next().unwrap();
    /// assert_eq!(item.id, "bob");
    /// let item = iter.next().unwrap();
    /// assert_eq!(item.id, "charlie");
    /// assert!(iter.next().is_none());
    /// ```
    ///
    /// [`BTreeMap`]: std::collections::BTreeMap
    /// [`T::Key`]: crate::IdOrdItem::Key
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(&self.items, &self.tables)
    }

    /// Iterates over the items in the map, allowing for mutation.
    ///
    /// Similar to [`BTreeMap`], the iteration is ordered by [`T::Key`].
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 99 }).unwrap();
    ///
    /// // Modify values through the mutable iterator
    /// for mut item in map.iter_mut() {
    ///     item.value *= 2;
    /// }
    ///
    /// assert_eq!(map.get("foo").unwrap().value, 84);
    /// assert_eq!(map.get("bar").unwrap().value, 198);
    /// ```
    ///
    /// [`BTreeMap`]: std::collections::BTreeMap
    /// [`T::Key`]: crate::IdOrdItem::Key
    #[inline]
    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, T>
    where
        T::Key<'a>: Hash,
    {
        IterMut::new(&mut self.items, &self.tables)
    }

    /// Checks general invariants of the map.
    ///
    /// The code below always upholds these invariants, but it's useful to have
    /// an explicit check for tests.
    #[doc(hidden)]
    pub fn validate(
        &self,
        compactness: ValidateCompact,
        chaos: ValidateChaos,
    ) -> Result<(), ValidationError>
    where
        T: fmt::Debug,
    {
        self.items.validate(compactness)?;
        self.tables.validate(self.len(), compactness)?;

        // Check that the indexes are all correct.

        for (&ix, item) in self.items.iter() {
            let key = item.key();
            let ix1 = match chaos {
                ValidateChaos::Yes => {
                    // Fall back to a linear search.
                    self.linear_search_index(&key)
                }
                ValidateChaos::No => {
                    // Use the B-Tree table to find the index.
                    self.find_index(&key)
                }
            };
            let Some(ix1) = ix1 else {
                return Err(ValidationError::general(format!(
                    "item at index {ix} has no key1 index"
                )));
            };

            if ix1 != ix {
                return Err(ValidationError::General(format!(
                    "item at index {ix} has mismatched indexes: ix1: {ix1}",
                )));
            }
        }

        Ok(())
    }

    /// Inserts a value into the set, returning an error if any duplicates were
    /// added.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    ///
    /// // Successful insertion
    /// assert!(
    ///     map.insert_unique(Item { id: "foo".to_string(), value: 42 }).is_ok()
    /// );
    /// assert!(
    ///     map.insert_unique(Item { id: "bar".to_string(), value: 99 }).is_ok()
    /// );
    ///
    /// // Duplicate key
    /// assert!(
    ///     map.insert_unique(Item { id: "foo".to_string(), value: 100 }).is_err()
    /// );
    /// ```
    pub fn insert_unique(
        &mut self,
        value: T,
    ) -> Result<(), DuplicateItem<T, &T>> {
        let _ = self.insert_unique_impl(value)?;
        Ok(())
    }

    /// Inserts a value into the map, removing and returning the conflicting
    /// item, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    ///
    /// // First insertion - no conflict
    /// let old = map.insert_overwrite(Item { id: "foo".to_string(), value: 42 });
    /// assert!(old.is_none());
    ///
    /// // Overwrite existing key - returns old value
    /// let old = map.insert_overwrite(Item { id: "foo".to_string(), value: 99 });
    /// assert!(old.is_some());
    /// assert_eq!(old.unwrap().value, 42);
    ///
    /// // Verify new value is in the map
    /// assert_eq!(map.get("foo").unwrap().value, 99);
    /// ```
    #[doc(alias = "insert")]
    pub fn insert_overwrite(&mut self, value: T) -> Option<T> {
        // Trying to write this function for maximal efficiency can get very
        // tricky, requiring delicate handling of indexes. We follow a very
        // simple approach instead:
        //
        // 1. Remove the item corresponding to the key that is already in the map.
        // 2. Add the item to the map.

        let duplicate = self.remove(&value.key());

        if self.insert_unique(value).is_err() {
            // We should never get here, because we just removed all the
            // duplicates.
            panic!("insert_unique failed after removing duplicates");
        }

        duplicate
    }

    /// Returns true if the map contains the given `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    ///
    /// assert!(map.contains_key("foo"));
    /// assert!(!map.contains_key("bar"));
    /// ```
    pub fn contains_key<'a, Q>(&'a self, key: &Q) -> bool
    where
        Q: ?Sized + Comparable<T::Key<'a>>,
    {
        self.find_index(key).is_some()
    }

    /// Gets a reference to the value associated with the given `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    ///
    /// assert_eq!(map.get("foo").unwrap().value, 42);
    /// assert!(map.get("bar").is_none());
    /// ```
    pub fn get<'a, Q>(&'a self, key: &Q) -> Option<&'a T>
    where
        Q: ?Sized + Comparable<T::Key<'a>>,
    {
        self.find(key)
    }

    /// Gets a mutable reference to the item associated with the given `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    ///
    /// if let Some(mut item) = map.get_mut("foo") {
    ///     item.value = 99;
    /// }
    ///
    /// assert_eq!(map.get("foo").unwrap().value, 99);
    /// ```
    pub fn get_mut<'a, Q>(&'a mut self, key: &Q) -> Option<RefMut<'a, T>>
    where
        Q: ?Sized + Comparable<T::Key<'a>>,
        T::Key<'a>: Hash,
    {
        let (dormant_map, index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let index = map.find_index(key)?;
            (dormant_map, index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };
        let item = &mut awakened_map.items[index];
        let state = awakened_map.tables.state().clone();
        let (hash, dormant) = {
            let (item, dormant) = DormantMutRef::new(item);
            let hash = awakened_map.tables.make_hash(item);
            (hash, dormant)
        };

        // SAFETY: the original item is not used after this point.
        let item = unsafe { dormant.awaken() };
        Some(RefMut::new(state, hash, item))
    }

    /// Removes an item from the map by its `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    ///
    /// let removed = map.remove("foo");
    /// assert!(removed.is_some());
    /// assert_eq!(removed.unwrap().value, 42);
    /// assert!(map.is_empty());
    ///
    /// // Removing a non-existent key returns None
    /// assert!(map.remove("bar").is_none());
    /// ```
    pub fn remove<'a, Q>(&'a mut self, key: &Q) -> Option<T>
    where
        Q: ?Sized + Comparable<T::Key<'a>>,
    {
        let (dormant_map, remove_index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let remove_index = map.find_index(key)?;
            (dormant_map, remove_index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };
        awakened_map.remove_by_index(remove_index)
    }

    /// Retrieves an entry by its `key`.
    ///
    /// Due to borrow checker limitations, this always accepts an owned key rather
    /// than a borrowed form.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_ord_map, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    ///
    /// // Insert via vacant entry
    /// match map.entry("foo") {
    ///     id_ord_map::Entry::Vacant(entry) => {
    ///         entry.insert(Item { id: "foo".to_string(), value: 42 });
    ///     }
    ///     id_ord_map::Entry::Occupied(_) => {}
    /// }
    ///
    /// // Update via occupied entry
    /// match map.entry("foo") {
    ///     id_ord_map::Entry::Occupied(mut entry) => {
    ///         entry.get_mut().value = 99;
    ///     }
    ///     id_ord_map::Entry::Vacant(_) => {}
    /// }
    ///
    /// assert_eq!(map.get("foo").unwrap().value, 99);
    /// ```
    pub fn entry<'a>(&'a mut self, key: T::Key<'_>) -> Entry<'a, T> {
        // Why does this always take an owned key? Well, it would seem like we
        // should be able to pass in any Q that is equivalent. That results in
        // *this* code compiling fine, but callers have trouble using it because
        // the borrow checker believes the keys are borrowed for the full 'a
        // rather than a shorter lifetime.
        //
        // By accepting owned keys, we can use the upcast functions to convert
        // them to a shorter lifetime (so this function accepts T::Key<'_>
        // rather than T::Key<'a>).
        //
        // Really, the solution here is to allow GATs to require covariant
        // parameters. If that were allowed, the borrow checker should be able
        // to figure out that keys don't need to be borrowed for the full 'a,
        // just for some shorter lifetime.
        let (map, dormant_map) = DormantMutRef::new(self);
        let key = T::upcast_key(key);
        {
            // index is explicitly typed to show that it has a trivial Drop impl
            // that doesn't capture anything from map.
            let index: Option<usize> = map
                .tables
                .key_to_item
                .find_index(&key, |index| map.items[index].key());
            if let Some(index) = index {
                drop(key);
                return Entry::Occupied(
                    // SAFETY: `map` is not used after this point.
                    unsafe { OccupiedEntry::new(dormant_map, index) },
                );
            }
        }
        Entry::Vacant(
            // SAFETY: `map` is not used after this point.
            unsafe { VacantEntry::new(dormant_map) },
        )
    }

    /// Returns the first item in the map. The key of this item is the minimum
    /// key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "charlie".to_string(), value: 30 }).unwrap();
    /// map.insert_unique(Item { id: "alice".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bob".to_string(), value: 99 }).unwrap();
    ///
    /// // First item has the minimum key.
    /// let first = map.first().unwrap();
    /// assert_eq!(first.id, "alice");
    /// assert_eq!(first.value, 42);
    ///
    /// // Empty map returns None.
    /// let empty_map: IdOrdMap<Item> = IdOrdMap::new();
    /// assert!(empty_map.first().is_none());
    /// ```
    #[inline]
    pub fn first(&self) -> Option<&T> {
        self.tables.key_to_item.first().map(|index| &self.items[index])
    }

    /// Returns the first entry in the map for in-place manipulation. The key of
    /// this entry is the minimum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "charlie".to_string(), value: 30 }).unwrap();
    /// map.insert_unique(Item { id: "alice".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bob".to_string(), value: 99 }).unwrap();
    ///
    /// // Modify the first entry.
    /// if let Some(mut entry) = map.first_entry() {
    ///     entry.get_mut().value = 100;
    /// }
    ///
    /// assert_eq!(map.get("alice").unwrap().value, 100);
    /// ```
    pub fn first_entry(&mut self) -> Option<OccupiedEntry<'_, T>> {
        let index = self.tables.key_to_item.first()?;
        let (_, dormant_map) = DormantMutRef::new(self);
        Some(
            // SAFETY: `map` is dropped immediately while creating the
            // DormantMutRef.
            unsafe { OccupiedEntry::new(dormant_map, index) },
        )
    }

    /// Removes and returns the first element in the map. The key of this
    /// element is the minimum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "charlie".to_string(), value: 30 }).unwrap();
    /// map.insert_unique(Item { id: "alice".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bob".to_string(), value: 99 }).unwrap();
    ///
    /// // Remove the first element.
    /// let first = map.pop_first().unwrap();
    /// assert_eq!(first.id, "alice");
    /// assert_eq!(first.value, 42);
    /// assert_eq!(map.len(), 2);
    ///
    /// // Remove the next element.
    /// let first = map.pop_first().unwrap();
    /// assert_eq!(first.id, "bob");
    ///
    /// // Empty map returns None.
    /// map.pop_first();
    /// assert!(map.pop_first().is_none());
    /// ```
    pub fn pop_first(&mut self) -> Option<T> {
        let index = self.tables.key_to_item.first()?;
        self.remove_by_index(index)
    }

    /// Returns the last item in the map. The key of this item is the maximum
    /// key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "charlie".to_string(), value: 30 }).unwrap();
    /// map.insert_unique(Item { id: "alice".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bob".to_string(), value: 99 }).unwrap();
    ///
    /// // Last item has the maximum key.
    /// let last = map.last().unwrap();
    /// assert_eq!(last.id, "charlie");
    /// assert_eq!(last.value, 30);
    ///
    /// // Empty map returns None.
    /// let empty_map: IdOrdMap<Item> = IdOrdMap::new();
    /// assert!(empty_map.last().is_none());
    /// ```
    #[inline]
    pub fn last(&self) -> Option<&T> {
        self.tables.key_to_item.last().map(|index| &self.items[index])
    }

    /// Returns the last entry in the map for in-place manipulation. The key of
    /// this entry is the maximum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "charlie".to_string(), value: 30 }).unwrap();
    /// map.insert_unique(Item { id: "alice".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bob".to_string(), value: 99 }).unwrap();
    ///
    /// // Modify the last entry.
    /// if let Some(mut entry) = map.last_entry() {
    ///     entry.get_mut().value = 200;
    /// }
    ///
    /// assert_eq!(map.get("charlie").unwrap().value, 200);
    /// ```
    pub fn last_entry(&mut self) -> Option<OccupiedEntry<'_, T>> {
        let index = self.tables.key_to_item.last()?;
        let (_, dormant_map) = DormantMutRef::new(self);
        Some(
            // SAFETY: `map` is dropped immediately while creating the
            // DormantMutRef.
            unsafe { OccupiedEntry::new(dormant_map, index) },
        )
    }

    /// Removes and returns the last element in the map. The key of this
    /// element is the maximum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "charlie".to_string(), value: 30 }).unwrap();
    /// map.insert_unique(Item { id: "alice".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bob".to_string(), value: 99 }).unwrap();
    ///
    /// // Remove the last element.
    /// let last = map.pop_last().unwrap();
    /// assert_eq!(last.id, "charlie");
    /// assert_eq!(last.value, 30);
    /// assert_eq!(map.len(), 2);
    ///
    /// // Remove the next element.
    /// let last = map.pop_last().unwrap();
    /// assert_eq!(last.id, "bob");
    ///
    /// // Empty map returns None.
    /// map.pop_last();
    /// assert!(map.pop_last().is_none());
    /// ```
    pub fn pop_last(&mut self) -> Option<T> {
        let index = self.tables.key_to_item.last()?;
        self.remove_by_index(index)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all items `T` for which `f(RefMut<T>)` returns
    /// false. The elements are visited in ascending key order.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdOrdItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdOrdMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 20 }).unwrap();
    /// map.insert_unique(Item { id: "baz".to_string(), value: 99 }).unwrap();
    ///
    /// // Retain only items where value is greater than 30
    /// map.retain(|item| item.value > 30);
    ///
    /// assert_eq!(map.len(), 2);
    /// assert_eq!(map.get("foo").unwrap().value, 42);
    /// assert_eq!(map.get("baz").unwrap().value, 99);
    /// assert!(map.get("bar").is_none());
    /// ```
    pub fn retain<'a, F>(&'a mut self, mut f: F)
    where
        F: FnMut(RefMut<'a, T>) -> bool,
        T::Key<'a>: Hash,
    {
        let hash_state = self.tables.state().clone();
        let (_, mut dormant_items) = DormantMutRef::new(&mut self.items);

        self.tables.key_to_item.retain(|index| {
            let (item, dormant_items) = {
                // SAFETY: All uses of `items` ended in the previous iteration.
                let items = unsafe { dormant_items.reborrow() };
                let (items, dormant_items) = DormantMutRef::new(items);
                let item: &'a mut T = items
                    .get_mut(index)
                    .expect("all indexes are present in self.items");
                (item, dormant_items)
            };

            let (hash, dormant_item) = {
                let (item, dormant_item): (&'a mut T, _) =
                    DormantMutRef::new(item);
                // Use T::key(item) rather than item.key() to force the key
                // trait function to be called for T rather than &mut T.
                let key = T::key(item);
                let hash = hash_state.hash_one(key);
                (MapHash::new(hash), dormant_item)
            };

            let retain = {
                // SAFETY: The original item is no longer used after the second
                // block above. dormant_items, from which item is derived, is
                // currently dormant.
                let item = unsafe { dormant_item.awaken() };

                let ref_mut = RefMut::new(hash_state.clone(), hash, item);
                f(ref_mut)
            };

            if retain {
                true
            } else {
                // SAFETY: The original items is no longer used after the first
                // block above, and item + dormant_item have been dropped after
                // being used above.
                let items = unsafe { dormant_items.awaken() };
                items.remove(index);
                false
            }
        });
    }

    fn find<'a, Q>(&'a self, k: &Q) -> Option<&'a T>
    where
        Q: ?Sized + Comparable<T::Key<'a>>,
    {
        self.find_index(k).map(|ix| &self.items[ix])
    }

    fn linear_search_index<'a, Q>(&'a self, k: &Q) -> Option<usize>
    where
        Q: ?Sized + Ord + Equivalent<T::Key<'a>>,
    {
        self.items.iter().find_map(|(index, item)| {
            (k.equivalent(&item.key())).then_some(*index)
        })
    }

    fn find_index<'a, Q>(&'a self, k: &Q) -> Option<usize>
    where
        Q: ?Sized + Comparable<T::Key<'a>>,
    {
        self.tables.key_to_item.find_index(k, |index| self.items[index].key())
    }

    pub(super) fn get_by_index(&self, index: usize) -> Option<&T> {
        self.items.get(index)
    }

    pub(super) fn get_by_index_mut<'a>(
        &'a mut self,
        index: usize,
    ) -> Option<RefMut<'a, T>>
    where
        T::Key<'a>: Hash,
    {
        let state = self.tables.state().clone();
        let (hash, dormant) = {
            let item: &'a mut T = self.items.get_mut(index)?;
            let (item, dormant) = DormantMutRef::new(item);
            let hash = self.tables.make_hash(item);
            (hash, dormant)
        };

        // SAFETY: item is no longer used after the above point.
        let item = unsafe { dormant.awaken() };
        Some(RefMut::new(state, hash, item))
    }

    pub(super) fn insert_unique_impl(
        &mut self,
        value: T,
    ) -> Result<usize, DuplicateItem<T, &T>> {
        let mut duplicates = BTreeSet::new();

        // Check for duplicates *before* inserting the new item, because we
        // don't want to partially insert the new item and then have to roll
        // back.
        let key = value.key();

        if let Some(index) = self
            .tables
            .key_to_item
            .find_index(&key, |index| self.items[index].key())
        {
            duplicates.insert(index);
        }

        if !duplicates.is_empty() {
            drop(key);
            return Err(DuplicateItem::__internal_new(
                value,
                duplicates.iter().map(|ix| &self.items[*ix]).collect(),
            ));
        }

        let next_index = self.items.next_index();
        self.tables
            .key_to_item
            .insert(next_index, &key, |index| self.items[index].key());
        drop(key);
        self.items.insert_at_next_index(value);

        Ok(next_index)
    }

    pub(super) fn remove_by_index(&mut self, remove_index: usize) -> Option<T> {
        let value = self.items.remove(remove_index)?;

        // Remove the value from the table.
        self.tables.key_to_item.remove(remove_index, value.key(), |index| {
            if index == remove_index {
                value.key()
            } else {
                self.items[index].key()
            }
        });

        Some(value)
    }

    pub(super) fn replace_at_index(&mut self, index: usize, value: T) -> T {
        // We check the key before removing it, to avoid leaving the map in an
        // inconsistent state.
        let old_key =
            self.get_by_index(index).expect("index is known to be valid").key();
        if T::upcast_key(old_key) != value.key() {
            panic!(
                "must insert a value with \
                 the same key used to create the entry"
            );
        }

        // Now that we know the key is the same, we can replace the value
        // directly without needing to tweak any tables.
        self.items.replace(index, value)
    }
}

impl<'a, T: IdOrdItem> fmt::Debug for IdOrdMap<T>
where
    T: fmt::Debug,
    T::Key<'a>: fmt::Debug,
    T: 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();

        for item in self.iter() {
            let key = item.key();

            // SAFETY:
            //
            // * Lifetime extension: for a type T and two lifetime params 'a and
            //   'b, T<'a> and T<'b> aren't guaranteed to have the same layout,
            //   but (a) that is true today and (b) it would be shocking and
            //   break half the Rust ecosystem if that were to change in the
            //   future.
            // * We only use key within the scope of this block before immediately
            //   dropping it. In particular, map.entry calls key.fmt() without
            //   holding a reference to it.
            let key: T::Key<'a> =
                unsafe { core::mem::transmute::<T::Key<'_>, T::Key<'a>>(key) };

            map.entry(&key, &item);
        }
        map.finish()
    }
}

impl<T: IdOrdItem + PartialEq> PartialEq for IdOrdMap<T> {
    fn eq(&self, other: &Self) -> bool {
        // Items are stored in sorted order, so we can just walk over both
        // iterators.
        if self.items.len() != other.items.len() {
            return false;
        }

        self.iter().zip(other.iter()).all(|(item1, item2)| {
            // Check that the items are equal.
            item1 == item2
        })
    }
}

// The Eq bound on T ensures that the IdOrdMap forms an equivalence class.
impl<T: IdOrdItem + Eq> Eq for IdOrdMap<T> {}

/// The `Extend` implementation overwrites duplicates. In the future, there will
/// also be an `extend_unique` method that will return an error.
impl<T: IdOrdItem> Extend<T> for IdOrdMap<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        // Keys may already be present in the map, or multiple times in the
        // iterator. Reserve the entire hint lower bound if the map is empty.
        // Otherwise reserve half the hint (rounded up), so the map will only
        // resize twice in the worst case.
        let iter = iter.into_iter();
        let reserve = if self.is_empty() {
            iter.size_hint().0
        } else {
            iter.size_hint().0.div_ceil(2)
        };
        self.reserve(reserve);
        for item in iter {
            self.insert_overwrite(item);
        }
    }
}

impl<'a, T: IdOrdItem> IntoIterator for &'a IdOrdMap<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: IdOrdItem> IntoIterator for &'a mut IdOrdMap<T>
where
    T::Key<'a>: Hash,
{
    type Item = RefMut<'a, T>;
    type IntoIter = IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: IdOrdItem> IntoIterator for IdOrdMap<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self.items, self.tables)
    }
}

/// The `FromIterator` implementation for `IdOrdMap` overwrites duplicate
/// items.
///
/// To reject duplicates, use [`IdOrdMap::from_iter_unique`].
impl<T: IdOrdItem> FromIterator<T> for IdOrdMap<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut map = IdOrdMap::new();
        for value in iter {
            map.insert_overwrite(value);
        }
        map
    }
}
