use super::{
    Entry, IdHashItem, IntoIter, Iter, IterMut, OccupiedEntry, RefMut,
    VacantEntry, tables::IdHashMapTables,
};
use crate::{
    DefaultHashBuilder,
    errors::DuplicateItem,
    internal::{ValidateCompact, ValidationError},
    support::{
        alloc::{Allocator, Global, global_alloc},
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
use equivalent::Equivalent;
use hashbrown::hash_table;

/// A hash map where the key is part of the value.
///
/// The storage mechanism is a fast hash table of integer indexes to items, with
/// these indexes stored in a hash table. This allows for efficient lookups by
/// the key and prevents duplicates.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{IdHashItem, IdHashMap, id_upcast};
///
/// // Define a struct with a key.
/// #[derive(Debug, PartialEq, Eq, Hash)]
/// struct MyItem {
///     id: String,
///     value: u32,
/// }
///
/// // Implement IdHashItem for the struct.
/// impl IdHashItem for MyItem {
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
/// // Create an IdHashMap and insert items.
/// let mut map = IdHashMap::new();
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
pub struct IdHashMap<T, S = DefaultHashBuilder, A: Allocator = Global> {
    pub(super) items: ItemSet<T, A>,
    pub(super) tables: IdHashMapTables<S, A>,
}

impl<T: IdHashItem, S: Default, A: Allocator + Default> Default
    for IdHashMap<T, S, A>
{
    fn default() -> Self {
        Self {
            items: ItemSet::with_capacity_in(0, A::default()),
            tables: IdHashMapTables::default(),
        }
    }
}

#[cfg(feature = "default-hasher")]
impl<T: IdHashItem> IdHashMap<T> {
    /// Creates a new, empty `IdHashMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let map: IdHashMap<Item> = IdHashMap::new();
    /// assert!(map.is_empty());
    /// assert_eq!(map.len(), 0);
    /// # }
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self { items: ItemSet::new(), tables: IdHashMapTables::default() }
    }

    /// Creates a new `IdHashMap` with the given capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let map: IdHashMap<Item> = IdHashMap::with_capacity(10);
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, global_alloc()),
            tables: IdHashMapTables::with_capacity_and_hasher_in(
                capacity,
                DefaultHashBuilder::default(),
                global_alloc(),
            ),
        }
    }
}

impl<T: IdHashItem, S: BuildHasher> IdHashMap<T, S> {
    /// Creates a new, empty `IdHashMap` with the given hasher.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    /// use std::collections::hash_map::RandomState;
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let hasher = RandomState::new();
    /// let map: IdHashMap<Item, _> = IdHashMap::with_hasher(hasher);
    /// assert!(map.is_empty());
    /// ```
    pub const fn with_hasher(hasher: S) -> Self {
        Self {
            items: ItemSet::new(),
            tables: IdHashMapTables::with_hasher_in(hasher, global_alloc()),
        }
    }

    /// Creates a new `IdHashMap` with the given capacity and hasher.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    /// use std::collections::hash_map::RandomState;
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let hasher = RandomState::new();
    /// let map: IdHashMap<Item, _> =
    ///     IdHashMap::with_capacity_and_hasher(10, hasher);
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, global_alloc()),
            tables: IdHashMapTables::with_capacity_and_hasher_in(
                capacity,
                hasher,
                global_alloc(),
            ),
        }
    }
}

#[cfg(feature = "default-hasher")]
impl<T: IdHashItem, A: Clone + Allocator> IdHashMap<T, DefaultHashBuilder, A> {
    /// Creates a new empty `IdHashMap` using the given allocator.
    ///
    /// Requires the `allocator-api2` feature to be enabled.
    ///
    /// # Examples
    ///
    /// Using the [`bumpalo`](https://docs.rs/bumpalo) allocator:
    ///
    /// ```
    /// # #[cfg(all(feature = "default-hasher", feature = "allocator-api2"))] {
    /// use iddqd::{IdHashMap, IdHashItem, id_upcast};
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> { &self.id }
    ///     id_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// // Create a new IdHashMap using the allocator.
    /// let map: IdHashMap<Item, _, &bumpalo::Bump> = IdHashMap::new_in(&bump);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn new_in(alloc: A) -> Self {
        Self {
            items: ItemSet::with_capacity_in(0, alloc.clone()),
            tables: IdHashMapTables::with_capacity_and_hasher_in(
                0,
                DefaultHashBuilder::default(),
                alloc,
            ),
        }
    }

    /// Creates an empty `IdHashMap` with the specified capacity using the given
    /// allocator.
    ///
    /// Requires the `allocator-api2` feature to be enabled.
    ///
    /// # Examples
    ///
    /// Using the [`bumpalo`](https://docs.rs/bumpalo) allocator:
    ///
    /// ```
    /// # #[cfg(all(feature = "default-hasher", feature = "allocator-api2"))] {
    /// use iddqd::{IdHashMap, IdHashItem, id_upcast};
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> { &self.id }
    ///     id_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// // Create a new IdHashMap with capacity using the allocator.
    /// let map: IdHashMap<Item, _, &bumpalo::Bump> = IdHashMap::with_capacity_in(10, &bump);
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, alloc.clone()),
            tables: IdHashMapTables::with_capacity_and_hasher_in(
                capacity,
                DefaultHashBuilder::default(),
                alloc,
            ),
        }
    }
}

impl<T: IdHashItem, S: BuildHasher, A: Clone + Allocator> IdHashMap<T, S, A> {
    /// Creates a new, empty `IdHashMap` with the given hasher and allocator.
    ///
    /// Requires the `allocator-api2` feature to be enabled.
    ///
    /// # Examples
    ///
    /// Using the [`bumpalo`](https://docs.rs/bumpalo) allocator:
    ///
    /// ```
    /// # #[cfg(feature = "allocator-api2")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    /// use std::collections::hash_map::RandomState;
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// let hasher = RandomState::new();
    /// // Create a new IdHashMap with hasher using the allocator.
    /// let map: IdHashMap<Item, _, &bumpalo::Bump> =
    ///     IdHashMap::with_hasher_in(hasher, &bump);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn with_hasher_in(hasher: S, alloc: A) -> Self {
        Self {
            items: ItemSet::new_in(alloc.clone()),
            tables: IdHashMapTables::with_hasher_in(hasher, alloc),
        }
    }

    /// Creates a new, empty `IdHashMap` with the given capacity, hasher, and
    /// allocator.
    ///
    /// Requires the `allocator-api2` feature to be enabled.
    ///
    /// # Examples
    ///
    /// Using the [`bumpalo`](https://docs.rs/bumpalo) allocator:
    ///
    /// ```
    /// # #[cfg(feature = "allocator-api2")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    /// use std::collections::hash_map::RandomState;
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// let hasher = RandomState::new();
    /// // Create a new IdHashMap with capacity and hasher using the allocator.
    /// let map: IdHashMap<Item, _, &bumpalo::Bump> =
    ///     IdHashMap::with_capacity_and_hasher_in(10, hasher, &bump);
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn with_capacity_and_hasher_in(
        capacity: usize,
        hasher: S,
        alloc: A,
    ) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, alloc.clone()),
            tables: IdHashMapTables::with_capacity_and_hasher_in(
                capacity, hasher, alloc,
            ),
        }
    }
}

impl<T: IdHashItem, S: Clone + BuildHasher, A: Allocator> IdHashMap<T, S, A> {
    #[cfg(feature = "daft")]
    pub(crate) fn hasher(&self) -> &S {
        self.tables.hasher()
    }

    /// Returns the allocator.
    ///
    /// Requires the `allocator-api2` feature to be enabled.
    ///
    /// # Examples
    ///
    /// Using the [`bumpalo`](https://docs.rs/bumpalo) allocator:
    ///
    /// ```
    /// # #[cfg(all(feature = "default-hasher", feature = "allocator-api2"))] {
    /// use iddqd::{IdHashMap, IdHashItem, id_upcast};
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> { &self.id }
    ///     id_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// // Create a new IdHashMap using the allocator.
    /// let map: IdHashMap<Item, _, &bumpalo::Bump> = IdHashMap::new_in(&bump);
    /// let _allocator = map.allocator();
    /// # }
    /// ```
    pub fn allocator(&self) -> &A {
        self.items.allocator()
    }

    /// Returns the currently allocated capacity of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let map: IdHashMap<Item> = IdHashMap::with_capacity(10);
    /// assert!(map.capacity() >= 10);
    /// # }
    /// ```
    pub fn capacity(&self) -> usize {
        // items and tables.capacity might theoretically diverge: use
        // items.capacity.
        self.items.capacity()
    }

    /// Returns true if the map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// assert!(!map.is_empty());
    /// # }
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
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// assert_eq!(map.len(), 1);
    ///
    /// map.insert_unique(Item { id: "bar".to_string(), value: 20 }).unwrap();
    /// assert_eq!(map.len(), 2);
    /// # }
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
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 20 }).unwrap();
    /// assert_eq!(map.len(), 2);
    ///
    /// map.clear();
    /// assert!(map.is_empty());
    /// assert_eq!(map.len(), 0);
    /// # }
    /// ```
    pub fn clear(&mut self) {
        self.items.clear();
        self.tables.key_to_item.clear();
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `IdHashMap`. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`isize::MAX`] bytes, and
    /// [`abort`]s the program in case of an allocation error. Use
    /// [`try_reserve`](Self::try_reserve) instead if you want to handle memory
    /// allocation failure.
    ///
    /// [`isize::MAX`]: https://doc.rust-lang.org/std/primitive.isize.html
    /// [`abort`]: https://doc.rust-lang.org/alloc/alloc/fn.handle_alloc_error.html
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map: IdHashMap<Item> = IdHashMap::new();
    /// map.reserve(100);
    /// assert!(map.capacity() >= 100);
    /// # }
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional);
        self.tables.key_to_item.reserve(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be
    /// inserted in the `IdHashMap`. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling `try_reserve`,
    /// capacity will be greater than or equal to `self.len() + additional` if
    /// it returns `Ok(())`. Does nothing if capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an
    /// error is returned.
    ///
    /// # Notes
    ///
    /// If reservation fails partway through, some internal structures may have
    /// already increased their capacity. The map remains in a valid state but
    /// may have uneven capacities across its internal structures.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map: IdHashMap<Item> = IdHashMap::new();
    /// map.try_reserve(100).expect("allocation should succeed");
    /// assert!(map.capacity() >= 100);
    /// # }
    /// ```
    pub fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), crate::errors::TryReserveError> {
        self.items
            .try_reserve(additional)
            .map_err(crate::errors::TryReserveError::from_hashbrown)?;
        self.tables
            .key_to_item
            .try_reserve(additional)
            .map_err(crate::errors::TryReserveError::from_hashbrown)?;
        Ok(())
    }

    /// Shrinks the capacity of the map as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map: IdHashMap<Item> = IdHashMap::with_capacity(100);
    /// map.insert_unique(Item { id: "foo".to_string(), value: 1 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 2 }).unwrap();
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// # }
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.items.shrink_to_fit();
        self.tables.key_to_item.shrink_to_fit();
    }

    /// Shrinks the capacity of the map with a lower limit. It will drop
    /// down no lower than the supplied limit while maintaining the internal
    /// rules and possibly leaving some space in accordance with the resize
    /// policy.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map: IdHashMap<Item> = IdHashMap::with_capacity(100);
    /// map.insert_unique(Item { id: "foo".to_string(), value: 1 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 2 }).unwrap();
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// map.shrink_to(0);
    /// assert!(map.capacity() >= 2);
    /// # }
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.items.shrink_to(min_capacity);
        self.tables.key_to_item.shrink_to(min_capacity);
    }

    /// Iterates over the items in the map.
    ///
    /// Similar to [`HashMap`], the iteration order is arbitrary and not
    /// guaranteed to be stable.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 20 }).unwrap();
    ///
    /// let mut values: Vec<u32> = map.iter().map(|item| item.value).collect();
    /// values.sort();
    /// assert_eq!(values, vec![20, 42]);
    /// # }
    /// ```
    ///
    /// [`HashMap`]: std::collections::HashMap
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(&self.items)
    }

    /// Iterates over the items in the map, allowing for mutation.
    ///
    /// Similar to [`HashMap`], the iteration order is arbitrary and not
    /// guaranteed to be stable.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 20 }).unwrap();
    ///
    /// for mut item in map.iter_mut() {
    ///     item.value *= 2;
    /// }
    ///
    /// assert_eq!(map.get("foo").unwrap().value, 84);
    /// assert_eq!(map.get("bar").unwrap().value, 40);
    /// # }
    /// ```
    ///
    /// [`HashMap`]: std::collections::HashMap
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T, S, A> {
        IterMut::new(&self.tables, &mut self.items)
    }

    /// Checks general invariants of the map.
    ///
    /// The code below always upholds these invariants, but it's useful to have
    /// an explicit check for tests.
    #[doc(hidden)]
    pub fn validate(
        &self,
        compactness: ValidateCompact,
    ) -> Result<(), ValidationError>
    where
        T: fmt::Debug,
    {
        self.items.validate(compactness)?;
        self.tables.validate(self.len(), compactness)?;

        // Check that the indexes are all correct.
        for (&ix, item) in self.items.iter() {
            let key = item.key();
            let Some(ix1) = self.find_index(&key) else {
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

    /// Inserts a value into the map, removing and returning the conflicting
    /// item, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    ///
    /// // First insertion returns None
    /// let old = map.insert_overwrite(Item { id: "foo".to_string(), value: 42 });
    /// assert!(old.is_none());
    ///
    /// // Second insertion with same key returns the old value
    /// let old = map.insert_overwrite(Item { id: "foo".to_string(), value: 100 });
    /// assert_eq!(old.unwrap().value, 42);
    /// assert_eq!(map.get("foo").unwrap().value, 100);
    /// # }
    /// ```
    #[doc(alias = "insert")]
    pub fn insert_overwrite(&mut self, value: T) -> Option<T> {
        // Trying to write this function for maximal efficiency can get very
        // tricky, requiring delicate handling of indexes. We follow a very
        // simple approach instead:
        //
        // 1. Remove items corresponding to the key that is already in the map.
        // 2. Add the item to the map.

        let duplicate = self.remove(&value.key());

        if self.insert_unique(value).is_err() {
            // We should never get here, because we just removed all the
            // duplicates.
            panic!("insert_unique failed after removing duplicates");
        }

        duplicate
    }

    /// Inserts a value into the set, returning an error if any duplicates were
    /// added.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    ///
    /// // First insertion succeeds
    /// assert!(
    ///     map.insert_unique(Item { id: "foo".to_string(), value: 42 }).is_ok()
    /// );
    ///
    /// // Second insertion with different key succeeds
    /// assert!(
    ///     map.insert_unique(Item { id: "bar".to_string(), value: 20 }).is_ok()
    /// );
    ///
    /// // Third insertion with duplicate key fails
    /// assert!(
    ///     map.insert_unique(Item { id: "foo".to_string(), value: 100 }).is_err()
    /// );
    /// # }
    /// ```
    pub fn insert_unique(
        &mut self,
        value: T,
    ) -> Result<(), DuplicateItem<T, &T>> {
        let _ = self.insert_unique_impl(value)?;
        Ok(())
    }

    /// Returns true if the map contains the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    ///
    /// assert!(map.contains_key("foo"));
    /// assert!(!map.contains_key("bar"));
    /// # }
    /// ```
    pub fn contains_key<'a, Q>(&'a self, key1: &Q) -> bool
    where
        Q: ?Sized + Hash + Equivalent<T::Key<'a>>,
    {
        self.find_index(key1).is_some()
    }

    /// Gets a reference to the value associated with the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    ///
    /// assert_eq!(map.get("foo").unwrap().value, 42);
    /// assert!(map.get("bar").is_none());
    /// # }
    /// ```
    pub fn get<'a, Q>(&'a self, key: &Q) -> Option<&'a T>
    where
        Q: ?Sized + Hash + Equivalent<T::Key<'a>>,
    {
        self.find_index(key).map(|ix| &self.items[ix])
    }

    /// Gets a mutable reference to the value associated with the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    ///
    /// if let Some(mut item) = map.get_mut("foo") {
    ///     item.value = 100;
    /// }
    ///
    /// assert_eq!(map.get("foo").unwrap().value, 100);
    /// assert!(map.get_mut("bar").is_none());
    /// # }
    /// ```
    pub fn get_mut<'a, Q>(&'a mut self, key: &Q) -> Option<RefMut<'a, T, S>>
    where
        Q: ?Sized + Hash + Equivalent<T::Key<'a>>,
    {
        let (dormant_map, index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let index = map.find_index(key)?;
            (dormant_map, index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };
        let item = &mut awakened_map.items[index];
        let state = awakened_map.tables.state.clone();
        let hashes = awakened_map.tables.make_hash(item);
        Some(RefMut::new(state, hashes, item))
    }

    /// Removes an item from the map by its key.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    ///
    /// let removed = map.remove("foo");
    /// assert_eq!(removed.unwrap().value, 42);
    /// assert!(map.is_empty());
    ///
    /// // Removing non-existent key returns None
    /// assert!(map.remove("bar").is_none());
    /// # }
    /// ```
    pub fn remove<'a, Q>(&'a mut self, key: &Q) -> Option<T>
    where
        Q: ?Sized + Hash + Equivalent<T::Key<'a>>,
    {
        let (dormant_map, remove_index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let remove_index = map.find_index(key)?;
            (dormant_map, remove_index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };

        let value = awakened_map
            .items
            .remove(remove_index)
            .expect("items missing key1 that was just retrieved");

        // Remove the value from the tables.
        let state = &awakened_map.tables.state;
        let Ok(item1) = awakened_map.tables.key_to_item.find_entry(
            state,
            &value.key(),
            |index| {
                if index == remove_index {
                    value.key()
                } else {
                    awakened_map.items[index].key()
                }
            },
        ) else {
            // The item was not found.
            panic!("we just looked this item up");
        };

        item1.remove();

        Some(value)
    }

    /// Retrieves an entry by its key.
    ///
    /// Due to borrow checker limitations, this always accepts an owned key
    /// rather than a borrowed form of it.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    ///
    /// // Use entry API for conditional insertion
    /// map.entry("foo").or_insert(Item { id: "foo".to_string(), value: 42 });
    /// map.entry("bar").or_insert(Item { id: "bar".to_string(), value: 20 });
    ///
    /// assert_eq!(map.len(), 2);
    /// # }
    /// ```
    pub fn entry<'a>(&'a mut self, key: T::Key<'_>) -> Entry<'a, T, S, A> {
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
            let index: Option<usize> = map.tables.key_to_item.find_index(
                &map.tables.state,
                &key,
                |index| map.items[index].key(),
            );
            if let Some(index) = index {
                drop(key);
                return Entry::Occupied(
                    // SAFETY: `map` is not used after this point.
                    unsafe { OccupiedEntry::new(dormant_map, index) },
                );
            }
        }
        let hash = map.make_key_hash(&key);
        Entry::Vacant(
            // SAFETY: `map` is not used after this point.
            unsafe { VacantEntry::new(dormant_map, hash) },
        )
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all items `T` for which `f(RefMut<T>)` returns
    /// false. The elements are visited in an arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
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
    /// # }
    /// ```
    pub fn retain<'a, F>(&'a mut self, mut f: F)
    where
        F: FnMut(RefMut<'a, T, S>) -> bool,
    {
        let hash_state = self.tables.state.clone();
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
                // block above, and item + dormant item have been used above.
                let items = unsafe { dormant_items.awaken() };
                items.remove(index);
                false
            }
        });
    }

    fn find_index<'a, Q>(&'a self, k: &Q) -> Option<usize>
    where
        Q: Hash + Equivalent<T::Key<'a>> + ?Sized,
    {
        self.tables
            .key_to_item
            .find_index(&self.tables.state, k, |index| self.items[index].key())
    }

    fn make_hash(&self, item: &T) -> MapHash {
        self.tables.make_hash(item)
    }

    fn make_key_hash(&self, key: &T::Key<'_>) -> MapHash {
        self.tables.make_key_hash::<T>(key)
    }

    pub(super) fn get_by_index(&self, index: usize) -> Option<&T> {
        self.items.get(index)
    }

    pub(super) fn get_by_index_mut(
        &mut self,
        index: usize,
    ) -> Option<RefMut<'_, T, S>> {
        let state = self.tables.state.clone();
        let hashes = self.make_hash(&self.items[index]);
        let item = &mut self.items[index];
        Some(RefMut::new(state, hashes, item))
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
        let state = &self.tables.state;

        let entry = match self
            .tables
            .key_to_item
            .entry(state, key, |index| self.items[index].key())
        {
            hash_table::Entry::Occupied(slot) => {
                duplicates.insert(*slot.get());
                None
            }
            hash_table::Entry::Vacant(slot) => Some(slot),
        };

        if !duplicates.is_empty() {
            return Err(DuplicateItem::__internal_new(
                value,
                duplicates.iter().map(|ix| &self.items[*ix]).collect(),
            ));
        }

        let next_index = self.items.insert_at_next_index(value);
        entry.unwrap().insert(next_index);

        Ok(next_index)
    }

    pub(super) fn remove_by_index(&mut self, remove_index: usize) -> Option<T> {
        let value = self.items.remove(remove_index)?;

        // Remove the value from the tables.
        let state = &self.tables.state;
        let Ok(item) =
            self.tables.key_to_item.find_entry(state, &value.key(), |index| {
                if index == remove_index {
                    value.key()
                } else {
                    self.items[index].key()
                }
            })
        else {
            // The item was not found.
            panic!("we just looked this item up");
        };

        item.remove();

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

impl<'a, T, S: Clone + BuildHasher, A: Allocator> fmt::Debug
    for IdHashMap<T, S, A>
where
    T: IdHashItem + fmt::Debug,
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

            map.entry(&key, item);
        }
        map.finish()
    }
}

impl<T: IdHashItem + PartialEq, S: Clone + BuildHasher, A: Allocator> PartialEq
    for IdHashMap<T, S, A>
{
    fn eq(&self, other: &Self) -> bool {
        // Implementing PartialEq for IdHashMap is tricky because IdHashMap is
        // not semantically like an IndexMap: two maps are equivalent even if
        // their items are in a different order. In other words, any permutation
        // of items is equivalent.
        //
        // We also can't sort the items because they're not necessarily Ord.
        //
        // So we write a custom equality check that checks that each key in one
        // map points to the same item as in the other map.

        if self.items.len() != other.items.len() {
            return false;
        }

        // Walk over all the items in the first map and check that they point to
        // the same item in the second map.
        for item in self.items.values() {
            let k1 = item.key();

            // Check that the indexes are the same in the other map.
            let Some(other_ix) = other.find_index(&k1) else {
                return false;
            };

            // Check that the other map's item is the same as this map's
            // item. (This is what we use the `PartialEq` bound on T for.)
            //
            // Because we've checked that other_ix is Some, we know that it is
            // valid and points to the expected item.
            let other_item = &other.items[other_ix];
            if item != other_item {
                return false;
            }
        }

        true
    }
}

// The Eq bound on T ensures that the TriHashMap forms an equivalence class.
impl<T: IdHashItem + Eq, S: Clone + BuildHasher, A: Allocator> Eq
    for IdHashMap<T, S, A>
{
}

/// The `Extend` implementation overwrites duplicates. In the future, there will
/// also be an `extend_unique` method that will return an error.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{IdHashItem, IdHashMap, id_upcast};
///
/// #[derive(Debug, PartialEq, Eq, Hash)]
/// struct Item {
///     id: String,
///     value: u32,
/// }
///
/// impl IdHashItem for Item {
///     type Key<'a> = &'a str;
///     fn key(&self) -> Self::Key<'_> {
///         &self.id
///     }
///     id_upcast!();
/// }
///
/// let mut map = IdHashMap::new();
/// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
///
/// let new_items = vec![
///     Item { id: "foo".to_string(), value: 100 }, // overwrites existing
///     Item { id: "bar".to_string(), value: 20 },  // new item
/// ];
///
/// map.extend(new_items);
/// assert_eq!(map.len(), 2);
/// assert_eq!(map.get("foo").unwrap().value, 100); // overwritten
/// assert_eq!(map.get("bar").unwrap().value, 20); // new
///
/// # }
/// ```
impl<T: IdHashItem, S: Clone + BuildHasher, A: Allocator> Extend<T>
    for IdHashMap<T, S, A>
{
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

impl<'a, T: IdHashItem, S: Clone + BuildHasher, A: Allocator> IntoIterator
    for &'a IdHashMap<T, S, A>
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    /// Creates an iterator over references to the items in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 20 }).unwrap();
    ///
    /// let mut values: Vec<u32> =
    ///     (&map).into_iter().map(|item| item.value).collect();
    /// values.sort();
    /// assert_eq!(values, vec![20, 42]);
    /// # }
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: IdHashItem, S: Clone + BuildHasher, A: Allocator> IntoIterator
    for &'a mut IdHashMap<T, S, A>
{
    type Item = RefMut<'a, T, S>;
    type IntoIter = IterMut<'a, T, S, A>;

    /// Creates an iterator over mutable references to the items in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 20 }).unwrap();
    ///
    /// for mut item in &mut map {
    ///     item.value *= 2;
    /// }
    ///
    /// assert_eq!(map.get("foo").unwrap().value, 84);
    /// assert_eq!(map.get("bar").unwrap().value, 40);
    /// # }
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: IdHashItem, S: Clone + BuildHasher, A: Allocator> IntoIterator
    for IdHashMap<T, S, A>
{
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    /// Consumes the map and creates an iterator over the owned items.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{IdHashItem, IdHashMap, id_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: String,
    ///     value: u32,
    /// }
    ///
    /// impl IdHashItem for Item {
    ///     type Key<'a> = &'a str;
    ///     fn key(&self) -> Self::Key<'_> {
    ///         &self.id
    ///     }
    ///     id_upcast!();
    /// }
    ///
    /// let mut map = IdHashMap::new();
    /// map.insert_unique(Item { id: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: "bar".to_string(), value: 20 }).unwrap();
    ///
    /// let mut values: Vec<u32> = map.into_iter().map(|item| item.value).collect();
    /// values.sort();
    /// assert_eq!(values, vec![20, 42]);
    /// # }
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self.items)
    }
}

/// The `FromIterator` implementation for `IdHashMap` overwrites duplicate
/// items.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{IdHashItem, IdHashMap, id_upcast};
///
/// #[derive(Debug, PartialEq, Eq, Hash)]
/// struct Item {
///     id: String,
///     value: u32,
/// }
///
/// impl IdHashItem for Item {
///     type Key<'a> = &'a str;
///     fn key(&self) -> Self::Key<'_> {
///         &self.id
///     }
///     id_upcast!();
/// }
///
/// let items = vec![
///     Item { id: "foo".to_string(), value: 42 },
///     Item { id: "bar".to_string(), value: 20 },
///     Item { id: "foo".to_string(), value: 100 }, // duplicate key, overwrites
/// ];
///
/// let map: IdHashMap<Item> = items.into_iter().collect();
/// assert_eq!(map.len(), 2);
/// assert_eq!(map.get("foo").unwrap().value, 100); // last value wins
/// assert_eq!(map.get("bar").unwrap().value, 20);
/// # }
/// ```
impl<T: IdHashItem, S: Default + Clone + BuildHasher, A: Allocator + Default>
    FromIterator<T> for IdHashMap<T, S, A>
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut map = IdHashMap::default();
        for item in iter {
            map.insert_overwrite(item);
        }
        map
    }
}
