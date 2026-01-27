use super::{
    Entry, IntoIter, Iter, IterMut, OccupiedEntry, RefMut, VacantEntry,
    entry::OccupiedEntryRef,
    entry_indexes::{DisjointKeys, EntryIndexes},
    tables::BiHashMapTables,
};
use crate::{
    BiHashItem, DefaultHashBuilder,
    bi_hash_map::entry::OccupiedEntryMut,
    errors::DuplicateItem,
    internal::{ValidateCompact, ValidationError},
    support::{
        alloc::{AllocWrapper, Allocator, Global, global_alloc},
        borrow::DormantMutRef,
        fmt_utils::StrDisplayAsDebug,
        item_set::ItemSet,
        map_hash::MapHash,
    },
};
use alloc::{collections::BTreeSet, vec::Vec};
use core::{
    fmt,
    hash::{BuildHasher, Hash},
};
use equivalent::Equivalent;
use hashbrown::hash_table;

/// A 1:1 (bijective) map for two keys and a value.
///
/// The storage mechanism is a fast hash table of integer indexes to items, with
/// these indexes stored in two hash tables. This allows for efficient lookups
/// by either of the two keys and prevents duplicates.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
///
/// // Define a struct with two keys and a value.
/// #[derive(Debug, PartialEq, Eq)]
/// struct MyItem {
///     id: u32,
///     name: &'static str,
///     value: i32,
/// }
///
/// // Implement BiHashItem for the struct.
/// impl BiHashItem for MyItem {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///     fn key2(&self) -> Self::K2<'_> {
///         self.name
///     }
///
///     bi_upcast!();
/// }
///
/// // Create a new BiHashMap and insert items.
/// let mut map = BiHashMap::new();
/// map.insert_unique(MyItem { id: 1, name: "foo", value: 42 }).unwrap();
/// map.insert_unique(MyItem { id: 2, name: "bar", value: 99 }).unwrap();
///
/// // Look up by the first key.
/// assert_eq!(map.get1(&1).unwrap().value, 42);
/// assert_eq!(map.get1(&2).unwrap().value, 99);
/// assert!(map.get1(&3).is_none());
///
/// // Look up by the second key.
/// assert_eq!(map.get2(&"foo").unwrap().value, 42);
/// assert_eq!(map.get2(&"bar").unwrap().value, 99);
/// assert!(map.get2(&"baz").is_none());
/// # }
/// ```
#[derive(Clone)]
pub struct BiHashMap<T, S = DefaultHashBuilder, A: Allocator = Global> {
    pub(super) items: ItemSet<T, A>,
    // Invariant: the values (usize) in these tables are valid indexes into
    // `items`, and are a 1:1 mapping.
    pub(super) tables: BiHashMapTables<S, A>,
}

impl<T: BiHashItem, S: Default, A: Allocator + Default> Default
    for BiHashMap<T, S, A>
{
    fn default() -> Self {
        Self {
            items: ItemSet::with_capacity_in(0, A::default()),
            tables: BiHashMapTables::default(),
        }
    }
}

#[cfg(feature = "default-hasher")]
impl<T: BiHashItem> BiHashMap<T> {
    /// Creates a new, empty `BiHashMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let map: BiHashMap<Item> = BiHashMap::new();
    /// assert!(map.is_empty());
    /// assert_eq!(map.len(), 0);
    /// # }
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self { items: ItemSet::new(), tables: BiHashMapTables::default() }
    }

    /// Creates a new `BiHashMap` with the given capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let map: BiHashMap<Item> = BiHashMap::with_capacity(10);
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, global_alloc()),
            tables: BiHashMapTables::with_capacity_and_hasher_in(
                capacity,
                DefaultHashBuilder::default(),
                global_alloc(),
            ),
        }
    }
}

impl<T: BiHashItem, S: BuildHasher> BiHashMap<T, S> {
    /// Creates a new `BiHashMap` with the given hasher.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    /// use std::collections::hash_map::RandomState;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let hasher = RandomState::new();
    /// let map: BiHashMap<Item, RandomState> = BiHashMap::with_hasher(hasher);
    /// assert!(map.is_empty());
    /// ```
    pub const fn with_hasher(hasher: S) -> Self {
        Self {
            items: ItemSet::new(),
            tables: BiHashMapTables::with_hasher(hasher),
        }
    }

    /// Creates a new `BiHashMap` with the given capacity and hasher.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    /// use std::collections::hash_map::RandomState;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let hasher = RandomState::new();
    /// let map: BiHashMap<Item, _> =
    ///     BiHashMap::with_capacity_and_hasher(10, hasher);
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, global_alloc()),
            tables: BiHashMapTables::with_capacity_and_hasher_in(
                capacity,
                hasher,
                global_alloc(),
            ),
        }
    }
}

#[cfg(feature = "default-hasher")]
impl<T: BiHashItem, A: Clone + Allocator> BiHashMap<T, DefaultHashBuilder, A> {
    /// Creates a new empty `BiHashMap` using the given allocator.
    ///
    /// Requires the `allocator-api2` feature to be enabled.
    ///
    /// # Examples
    ///
    /// Using the [`bumpalo`](https://docs.rs/bumpalo) allocator:
    ///
    /// ```
    /// # #[cfg(all(feature = "default-hasher", feature = "allocator-api2"))] {
    /// use iddqd::{BiHashMap, BiHashItem, bi_upcast};
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// // Create a new BiHashMap using the allocator.
    /// let map: BiHashMap<Item, _, &bumpalo::Bump> = BiHashMap::new_in(&bump);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn new_in(alloc: A) -> Self {
        Self {
            items: ItemSet::with_capacity_in(0, alloc.clone()),
            tables: BiHashMapTables::with_capacity_and_hasher_in(
                0,
                DefaultHashBuilder::default(),
                alloc,
            ),
        }
    }

    /// Creates an empty `BiHashMap` with the specified capacity using the given
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
    /// use iddqd::{BiHashMap, BiHashItem, bi_upcast};
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// // Create a new BiHashMap with capacity using the allocator.
    /// let map: BiHashMap<Item, _, &bumpalo::Bump> = BiHashMap::with_capacity_in(10, &bump);
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, alloc.clone()),
            tables: BiHashMapTables::with_capacity_and_hasher_in(
                capacity,
                DefaultHashBuilder::default(),
                alloc,
            ),
        }
    }
}

impl<T: BiHashItem, S: Clone + BuildHasher, A: Clone + Allocator>
    BiHashMap<T, S, A>
{
    /// Creates a new, empty `BiHashMap` with the given hasher and allocator.
    ///
    /// Requires the `allocator-api2` feature to be enabled.
    ///
    /// # Examples
    ///
    /// Using the [`bumpalo`](https://docs.rs/bumpalo) allocator:
    ///
    /// ```
    /// # #[cfg(feature = "allocator-api2")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    /// use std::collections::hash_map::RandomState;
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// let hasher = RandomState::new();
    /// // Create a new BiHashMap with hasher using the allocator.
    /// let map: BiHashMap<Item, _, &bumpalo::Bump> =
    ///     BiHashMap::with_hasher_in(hasher, &bump);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn with_hasher_in(hasher: S, alloc: A) -> Self {
        Self {
            items: ItemSet::with_capacity_in(0, alloc.clone()),
            tables: BiHashMapTables::with_capacity_and_hasher_in(
                0, hasher, alloc,
            ),
        }
    }

    /// Creates a new, empty `BiHashMap` with the given capacity, hasher, and
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
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    /// use std::collections::hash_map::RandomState;
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// let hasher = RandomState::new();
    /// // Create a new BiHashMap with capacity and hasher using the allocator.
    /// let map: BiHashMap<Item, _, &bumpalo::Bump> =
    ///     BiHashMap::with_capacity_and_hasher_in(10, hasher, &bump);
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
            tables: BiHashMapTables::with_capacity_and_hasher_in(
                capacity, hasher, alloc,
            ),
        }
    }
}

impl<T: BiHashItem, S: Clone + BuildHasher, A: Allocator> BiHashMap<T, S, A> {
    /// Returns the hasher.
    #[cfg(feature = "daft")]
    #[inline]
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
    /// use iddqd::{BiHashMap, BiHashItem, bi_upcast};
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// // Create a new BiHashMap using the allocator.
    /// let map: BiHashMap<Item, _, &bumpalo::Bump> = BiHashMap::new_in(&bump);
    /// let _allocator = map.allocator();
    /// # }
    /// ```
    #[inline]
    pub fn allocator(&self) -> &A {
        self.items.allocator()
    }

    /// Returns the currently allocated capacity of the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let map: BiHashMap<Item> = BiHashMap::with_capacity(10);
    /// assert!(map.capacity() >= 10);
    ///
    /// let empty_map: BiHashMap<Item> = BiHashMap::new();
    /// assert!(empty_map.capacity() >= 0);
    /// # }
    /// ```
    pub fn capacity(&self) -> usize {
        // items and tables.capacity might theoretically diverge: use
        // items.capacity.
        self.items.capacity()
    }

    /// Returns true if the map contains no items.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
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
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
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
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
    /// assert_eq!(map.len(), 2);
    ///
    /// map.clear();
    /// assert!(map.is_empty());
    /// assert_eq!(map.len(), 0);
    /// # }
    /// ```
    pub fn clear(&mut self) {
        self.items.clear();
        self.tables.k1_to_item.clear();
        self.tables.k2_to_item.clear();
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `BiHashMap`. The collection may reserve more space to
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
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map: BiHashMap<Item> = BiHashMap::new();
    /// map.reserve(100);
    /// assert!(map.capacity() >= 100);
    /// # }
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional);
        self.tables.k1_to_item.reserve(additional);
        self.tables.k2_to_item.reserve(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be
    /// inserted in the `BiHashMap`. The collection may reserve more space to
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
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map: BiHashMap<Item> = BiHashMap::new();
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
            .k1_to_item
            .try_reserve(additional)
            .map_err(crate::errors::TryReserveError::from_hashbrown)?;
        self.tables
            .k2_to_item
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
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map: BiHashMap<Item> = BiHashMap::with_capacity(100);
    /// map.insert_unique(Item { id: 1, name: "foo".to_string() }).unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string() }).unwrap();
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// # }
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.items.shrink_to_fit();
        self.tables.k1_to_item.shrink_to_fit();
        self.tables.k2_to_item.shrink_to_fit();
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
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map: BiHashMap<Item> = BiHashMap::with_capacity(100);
    /// map.insert_unique(Item { id: 1, name: "foo".to_string() }).unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string() }).unwrap();
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// map.shrink_to(0);
    /// assert!(map.capacity() >= 2);
    /// # }
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.items.shrink_to(min_capacity);
        self.tables.k1_to_item.shrink_to(min_capacity);
        self.tables.k2_to_item.shrink_to(min_capacity);
    }

    /// Returns an iterator over all items in the map.
    ///
    /// Similar to [`HashMap`], the iteration order is arbitrary and not
    /// guaranteed to be stable.
    ///
    /// [`HashMap`]: std::collections::HashMap
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
    ///
    /// let mut values: Vec<i32> = map.iter().map(|item| item.value).collect();
    /// values.sort();
    /// assert_eq!(values, vec![42, 99]);
    /// # }
    /// ```
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
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
    ///
    /// for mut item in map.iter_mut() {
    ///     item.value += 10;
    /// }
    ///
    /// assert_eq!(map.get1(&1).unwrap().value, 52);
    /// assert_eq!(map.get1(&2).unwrap().value, 109);
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
            let key1 = item.key1();
            let key2 = item.key2();

            let Some(ix1) = self.find1_index(&key1) else {
                return Err(ValidationError::general(format!(
                    "item at index {ix} has no key1 index"
                )));
            };
            let Some(ix2) = self.find2_index(&key2) else {
                return Err(ValidationError::general(format!(
                    "item at index {ix} has no key2 index"
                )));
            };

            if ix1 != ix || ix2 != ix {
                return Err(ValidationError::general(format!(
                    "item at index {ix} has inconsistent indexes: {ix1}/{ix2}"
                )));
            }
        }

        Ok(())
    }

    /// Inserts a value into the map, removing any conflicting items and
    /// returning a list of those items.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
    ///
    /// // Insert an item with conflicting key1
    /// let removed = map.insert_overwrite(Item {
    ///     id: 1,
    ///     name: "baz".to_string(),
    ///     value: 100,
    /// });
    /// assert_eq!(removed.len(), 1);
    /// assert_eq!(removed[0].name, "foo");
    /// assert_eq!(removed[0].value, 42);
    ///
    /// assert_eq!(map.len(), 2);
    /// assert_eq!(map.get1(&1).unwrap().name, "baz");
    /// # }
    /// ```
    #[doc(alias = "insert")]
    pub fn insert_overwrite(&mut self, value: T) -> Vec<T> {
        // Trying to write this function for maximal efficiency can get very
        // tricky, requiring delicate handling of indexes. We follow a very
        // simple approach instead:
        //
        // 1. Remove items corresponding to keys that are already in the map.
        // 2. Add the item to the map.

        let mut duplicates = Vec::new();
        duplicates.extend(self.remove1(&value.key1()));
        duplicates.extend(self.remove2(&value.key2()));

        if self.insert_unique(value).is_err() {
            // We should never get here, because we just removed all the
            // duplicates.
            panic!("insert_unique failed after removing duplicates");
        }

        duplicates
    }

    /// Inserts a value into the set, returning an error if any duplicates were
    /// added.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    ///
    /// // Successful insertion
    /// assert!(
    ///     map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///         .is_ok()
    /// );
    /// assert!(
    ///     map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///         .is_ok()
    /// );
    ///
    /// // Duplicate key1
    /// assert!(
    ///     map.insert_unique(Item { id: 1, name: "baz".to_string(), value: 100 })
    ///         .is_err()
    /// );
    ///
    /// // Duplicate key2
    /// assert!(
    ///     map.insert_unique(Item { id: 3, name: "foo".to_string(), value: 200 })
    ///         .is_err()
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

    /// Returns true if the map contains a single item that matches both `key1` and `key2`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 }).unwrap();
    ///
    /// assert!(map.contains_key_unique(&1, &"foo"));
    /// assert!(map.contains_key_unique(&2, &"bar"));
    /// assert!(!map.contains_key_unique(&1, &"bar")); // key1 exists but key2 doesn't match
    /// assert!(!map.contains_key_unique(&3, &"baz")); // neither key exists
    /// # }
    /// ```
    pub fn contains_key_unique<'a, Q1, Q2>(
        &'a self,
        key1: &Q1,
        key2: &Q2,
    ) -> bool
    where
        Q1: Hash + Equivalent<T::K1<'a>> + ?Sized,
        Q2: Hash + Equivalent<T::K2<'a>> + ?Sized,
    {
        self.get_unique(key1, key2).is_some()
    }

    /// Gets a reference to the unique item associated with the given `key1` and
    /// `key2`, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 }).unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 }).unwrap();
    ///
    /// assert_eq!(map.get_unique(&1, &"foo").unwrap().value, 42);
    /// assert_eq!(map.get_unique(&2, &"bar").unwrap().value, 99);
    /// assert!(map.get_unique(&1, &"bar").is_none()); // key1 exists but key2 doesn't match
    /// assert!(map.get_unique(&3, &"baz").is_none()); // neither key exists
    /// # }
    /// ```
    pub fn get_unique<'a, Q1, Q2>(
        &'a self,
        key1: &Q1,
        key2: &Q2,
    ) -> Option<&'a T>
    where
        Q1: Hash + Equivalent<T::K1<'a>> + ?Sized,
        Q2: Hash + Equivalent<T::K2<'a>> + ?Sized,
    {
        let index = self.find1_index(key1)?;
        let item = &self.items[index];
        if key2.equivalent(&item.key2()) { Some(item) } else { None }
    }

    /// Gets a mutable reference to the unique item associated with the given
    /// `key1` and `key2`, if it exists.
    pub fn get_mut_unique<'a, Q1, Q2>(
        &'a mut self,
        key1: &Q1,
        key2: &Q2,
    ) -> Option<RefMut<'a, T, S>>
    where
        Q1: Hash + Equivalent<T::K1<'a>> + ?Sized,
        Q2: Hash + Equivalent<T::K2<'a>> + ?Sized,
    {
        let (dormant_map, index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let index = map.find1_index(key1)?;
            // Check key2 match before proceeding
            if !key2.equivalent(&map.items[index].key2()) {
                return None;
            }
            (dormant_map, index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };
        let item = &mut awakened_map.items[index];
        let state = awakened_map.tables.state.clone();
        let hashes =
            awakened_map.tables.make_hashes::<T>(&item.key1(), &item.key2());
        Some(RefMut::new(state, hashes, item))
    }

    /// Removes the item uniquely identified by `key1` and `key2`, if it exists.
    pub fn remove_unique<'a, Q1, Q2>(
        &'a mut self,
        key1: &Q1,
        key2: &Q2,
    ) -> Option<T>
    where
        Q1: Hash + Equivalent<T::K1<'a>> + ?Sized,
        Q2: Hash + Equivalent<T::K2<'a>> + ?Sized,
    {
        let (dormant_map, remove_index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let remove_index = map.find1_index(key1)?;
            if !key2.equivalent(&map.items[remove_index].key2()) {
                return None;
            }
            (dormant_map, remove_index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };

        awakened_map.remove_by_index(remove_index)
    }

    /// Returns true if the map contains the given `key1`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
    ///
    /// assert!(map.contains_key1(&1));
    /// assert!(map.contains_key1(&2));
    /// assert!(!map.contains_key1(&3));
    /// # }
    /// ```
    pub fn contains_key1<'a, Q>(&'a self, key1: &Q) -> bool
    where
        Q: Hash + Equivalent<T::K1<'a>> + ?Sized,
    {
        self.find1_index(key1).is_some()
    }

    /// Gets a reference to the value associated with the given `key1`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
    ///
    /// assert_eq!(map.get1(&1).unwrap().value, 42);
    /// assert_eq!(map.get1(&2).unwrap().value, 99);
    /// assert!(map.get1(&3).is_none());
    /// # }
    /// ```
    pub fn get1<'a, Q>(&'a self, key1: &Q) -> Option<&'a T>
    where
        Q: Hash + Equivalent<T::K1<'a>> + ?Sized,
    {
        self.find1(key1)
    }

    /// Gets a mutable reference to the value associated with the given `key1`.
    pub fn get1_mut<'a, Q>(&'a mut self, key1: &Q) -> Option<RefMut<'a, T, S>>
    where
        Q: Hash + Equivalent<T::K1<'a>> + ?Sized,
    {
        let (dormant_map, index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let index = map.find1_index(key1)?;
            (dormant_map, index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };
        let item = &mut awakened_map.items[index];
        let state = awakened_map.tables.state.clone();
        let hashes =
            awakened_map.tables.make_hashes::<T>(&item.key1(), &item.key2());
        Some(RefMut::new(state, hashes, item))
    }

    /// Removes an item from the map by its `key1`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
    ///
    /// let removed = map.remove1(&1);
    /// assert_eq!(removed.unwrap().value, 42);
    /// assert_eq!(map.len(), 1);
    /// assert!(map.get1(&1).is_none());
    /// assert!(map.remove1(&3).is_none());
    /// # }
    /// ```
    pub fn remove1<'a, Q>(&'a mut self, key1: &Q) -> Option<T>
    where
        Q: Hash + Equivalent<T::K1<'a>> + ?Sized,
    {
        let (dormant_map, remove_index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let remove_index = map.find1_index(key1)?;
            (dormant_map, remove_index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };

        awakened_map.remove_by_index(remove_index)
    }

    /// Returns true if the map contains the given `key2`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
    ///
    /// assert!(map.contains_key2(&"foo"));
    /// assert!(map.contains_key2(&"bar"));
    /// assert!(!map.contains_key2(&"baz"));
    /// # }
    /// ```
    pub fn contains_key2<'a, Q>(&'a self, key2: &Q) -> bool
    where
        Q: Hash + Equivalent<T::K2<'a>> + ?Sized,
    {
        self.find2_index(key2).is_some()
    }

    /// Gets a reference to the value associated with the given `key2`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
    ///
    /// assert_eq!(map.get2(&"foo").unwrap().value, 42);
    /// assert_eq!(map.get2(&"bar").unwrap().value, 99);
    /// assert!(map.get2(&"baz").is_none());
    /// # }
    /// ```
    pub fn get2<'a, Q>(&'a self, key2: &Q) -> Option<&'a T>
    where
        Q: Hash + Equivalent<T::K2<'a>> + ?Sized,
    {
        self.find2(key2)
    }

    /// Gets a mutable reference to the value associated with the given `key2`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    ///
    /// if let Some(mut item_ref) = map.get2_mut(&"foo") {
    ///     item_ref.value = 100;
    /// }
    ///
    /// assert_eq!(map.get2(&"foo").unwrap().value, 100);
    /// # }
    /// ```
    pub fn get2_mut<'a, Q>(&'a mut self, key2: &Q) -> Option<RefMut<'a, T, S>>
    where
        Q: Hash + Equivalent<T::K2<'a>> + ?Sized,
    {
        let (dormant_map, index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let index = map.find2_index(key2)?;
            (dormant_map, index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };
        let item = &mut awakened_map.items[index];
        let state = awakened_map.tables.state.clone();
        let hashes =
            awakened_map.tables.make_hashes::<T>(&item.key1(), &item.key2());
        Some(RefMut::new(state, hashes, item))
    }

    /// Removes an item from the map by its `key2`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
    ///     .unwrap();
    ///
    /// let removed = map.remove2(&"foo");
    /// assert_eq!(removed.unwrap().value, 42);
    /// assert_eq!(map.len(), 1);
    /// assert!(map.get2(&"foo").is_none());
    /// assert!(map.remove2(&"baz").is_none());
    /// # }
    /// ```
    pub fn remove2<'a, Q>(&'a mut self, key2: &Q) -> Option<T>
    where
        Q: Hash + Equivalent<T::K2<'a>> + ?Sized,
    {
        let (dormant_map, remove_index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let remove_index = map.find2_index(key2)?;
            (dormant_map, remove_index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };

        awakened_map.remove_by_index(remove_index)
    }

    /// Retrieves an entry by its keys.
    ///
    /// Due to borrow checker limitations, this always accepts owned keys rather
    /// than a borrowed form of them.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{BiHashItem, BiHashMap, bi_hash_map, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: i32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    ///
    /// // Get existing entry
    /// match map.entry(1, "foo") {
    ///     bi_hash_map::Entry::Occupied(entry) => {
    ///         assert_eq!(entry.get().as_unique().unwrap().value, 42);
    ///     }
    ///     bi_hash_map::Entry::Vacant(_) => panic!("Should be occupied"),
    /// }
    ///
    /// // Try to get a non-existing entry
    /// match map.entry(2, "bar") {
    ///     bi_hash_map::Entry::Occupied(_) => panic!("Should be vacant"),
    ///     bi_hash_map::Entry::Vacant(entry) => {
    ///         entry.insert(Item { id: 2, name: "bar".to_string(), value: 99 });
    ///     }
    /// }
    ///
    /// assert_eq!(map.len(), 2);
    /// # }
    /// ```
    pub fn entry<'a>(
        &'a mut self,
        key1: T::K1<'_>,
        key2: T::K2<'_>,
    ) -> Entry<'a, T, S, A> {
        // Why does this always take owned keys? Well, it would seem like we
        // should be able to pass in any Q1 and Q2 that are equivalent. That
        // results in *this* code compiling fine, but callers have trouble using
        // it because the borrow checker believes the keys are borrowed for the
        // full 'a rather than a shorter lifetime.
        //
        // By accepting owned keys, we can use the upcast functions to convert
        // them to a shorter lifetime (so this function accepts T::K1<'_> rather
        // than T::K1<'a>).
        //
        // Really, the solution here is to allow GATs to require covariant
        // parameters. If that were allowed, the borrow checker should be able
        // to figure out that keys don't need to be borrowed for the full 'a,
        // just for some shorter lifetime.
        let (map, dormant_map) = DormantMutRef::new(self);
        let key1 = T::upcast_key1(key1);
        let key2 = T::upcast_key2(key2);
        let (index1, index2) = {
            // index1 and index2 are explicitly typed to show that it has a
            // trivial Drop impl that doesn't capture anything from map.
            let index1: Option<usize> = map.tables.k1_to_item.find_index(
                &map.tables.state,
                &key1,
                |index| map.items[index].key1(),
            );
            let index2: Option<usize> = map.tables.k2_to_item.find_index(
                &map.tables.state,
                &key2,
                |index| map.items[index].key2(),
            );
            (index1, index2)
        };

        match (index1, index2) {
            (Some(index1), Some(index2)) if index1 == index2 => {
                // The item is already in the map.
                drop(key1);
                Entry::Occupied(
                    // SAFETY: `map` is not used after this point.
                    unsafe {
                        OccupiedEntry::new(
                            dormant_map,
                            EntryIndexes::Unique(index1),
                        )
                    },
                )
            }
            (None, None) => {
                let hashes = map.tables.make_hashes::<T>(&key1, &key2);
                Entry::Vacant(
                    // SAFETY: `map` is not used after this point.
                    unsafe { VacantEntry::new(dormant_map, hashes) },
                )
            }
            (index1, index2) => Entry::Occupied(
                // SAFETY: `map` is not used after this point.
                unsafe {
                    OccupiedEntry::new(
                        dormant_map,
                        EntryIndexes::NonUnique { index1, index2 },
                    )
                },
            ),
        }
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
    /// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     value: u32,
    /// }
    ///
    /// impl BiHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///
    ///     bi_upcast!();
    /// }
    ///
    /// let mut map = BiHashMap::new();
    /// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 2, name: "bar".to_string(), value: 20 })
    ///     .unwrap();
    /// map.insert_unique(Item { id: 3, name: "baz".to_string(), value: 99 })
    ///     .unwrap();
    ///
    /// // Retain only items where value is greater than 30
    /// map.retain(|item| item.value > 30);
    ///
    /// assert_eq!(map.len(), 2);
    /// assert_eq!(map.get1(&1).unwrap().value, 42);
    /// assert_eq!(map.get1(&3).unwrap().value, 99);
    /// assert!(map.get1(&2).is_none());
    /// # }
    /// ```
    pub fn retain<'a, F>(&'a mut self, mut f: F)
    where
        F: FnMut(RefMut<'a, T, S>) -> bool,
    {
        let hash_state = self.tables.state.clone();
        let (_, mut dormant_items) = DormantMutRef::new(&mut self.items);

        self.tables.k1_to_item.retain(|index| {
            let (item, dormant_items) = {
                // SAFETY: All uses of `items` ended in the previous iteration.
                let items = unsafe { dormant_items.reborrow() };
                let (items, dormant_items) = DormantMutRef::new(items);
                let item: &'a mut T = items
                    .get_mut(index)
                    .expect("all indexes are present in self.items");
                (item, dormant_items)
            };

            let (hashes, dormant_item) = {
                let (item, dormant_item): (&'a mut T, _) =
                    DormantMutRef::new(item);
                // Use T::k1(item) rather than item.key() to force the key
                // trait function to be called for T rather than &mut T.
                let key1 = T::key1(item);
                let key2 = T::key2(item);
                let hash1 = hash_state.hash_one(key1);
                let hash2 = hash_state.hash_one(key2);
                ([MapHash::new(hash1), MapHash::new(hash2)], dormant_item)
            };

            let hash2 = hashes[1].hash();
            let retain = {
                // SAFETY: The original item is no longer used after the second
                // block above. dormant_items, from which item is derived, is
                // currently dormant.
                let item = unsafe { dormant_item.awaken() };

                let ref_mut = RefMut::new(hash_state.clone(), hashes, item);
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
                let k2_entry = self
                    .tables
                    .k2_to_item
                    .find_entry_by_hash(hash2, |map2_index| {
                        map2_index == index
                    });
                match k2_entry {
                    Ok(entry) => {
                        entry.remove();
                    }
                    Err(_) => {
                        // This happening means there's an inconsistency between
                        // the maps.
                        panic!(
                            "inconsistency between k1_to_item and k2_to_item"
                        );
                    }
                }

                false
            }
        });
    }

    fn find1<'a, Q>(&'a self, k: &Q) -> Option<&'a T>
    where
        Q: Hash + Equivalent<T::K1<'a>> + ?Sized,
    {
        self.find1_index(k).map(|ix| &self.items[ix])
    }

    fn find1_index<'a, Q>(&'a self, k: &Q) -> Option<usize>
    where
        Q: Hash + Equivalent<T::K1<'a>> + ?Sized,
    {
        self.tables
            .k1_to_item
            .find_index(&self.tables.state, k, |index| self.items[index].key1())
    }

    fn find2<'a, Q>(&'a self, k: &Q) -> Option<&'a T>
    where
        Q: Hash + Equivalent<T::K2<'a>> + ?Sized,
    {
        self.find2_index(k).map(|ix| &self.items[ix])
    }

    fn find2_index<'a, Q>(&'a self, k: &Q) -> Option<usize>
    where
        Q: Hash + Equivalent<T::K2<'a>> + ?Sized,
    {
        self.tables
            .k2_to_item
            .find_index(&self.tables.state, k, |index| self.items[index].key2())
    }

    pub(super) fn get_by_entry_index(
        &self,
        indexes: EntryIndexes,
    ) -> OccupiedEntryRef<'_, T> {
        match indexes {
            EntryIndexes::Unique(index) => OccupiedEntryRef::Unique(
                self.items.get(index).expect("index is valid"),
            ),
            EntryIndexes::NonUnique { index1, index2 } => {
                let by_key1 = index1
                    .map(|k| self.items.get(k).expect("key1 index is valid"));
                let by_key2 = index2
                    .map(|k| self.items.get(k).expect("key2 index is valid"));
                OccupiedEntryRef::NonUnique { by_key1, by_key2 }
            }
        }
    }

    pub(super) fn get_by_entry_index_mut(
        &mut self,
        indexes: EntryIndexes,
    ) -> OccupiedEntryMut<'_, T, S> {
        match indexes.disjoint_keys() {
            DisjointKeys::Unique(index) => {
                let item = self.items.get_mut(index).expect("index is valid");
                let state = self.tables.state.clone();
                let hashes =
                    self.tables.make_hashes::<T>(&item.key1(), &item.key2());
                OccupiedEntryMut::Unique(RefMut::new(state, hashes, item))
            }
            DisjointKeys::Key1(index1) => {
                let item =
                    self.items.get_mut(index1).expect("key1 index is valid");
                let state = self.tables.state.clone();
                let hashes =
                    self.tables.make_hashes::<T>(&item.key1(), &item.key2());
                OccupiedEntryMut::NonUnique {
                    by_key1: Some(RefMut::new(state, hashes, item)),
                    by_key2: None,
                }
            }
            DisjointKeys::Key2(index2) => {
                let item =
                    self.items.get_mut(index2).expect("key2 index is valid");
                let state = self.tables.state.clone();
                let hashes =
                    self.tables.make_hashes::<T>(&item.key1(), &item.key2());
                OccupiedEntryMut::NonUnique {
                    by_key1: None,
                    by_key2: Some(RefMut::new(state, hashes, item)),
                }
            }
            DisjointKeys::Key12(indexes) => {
                let state = self.tables.state.clone();
                let mut items = self.items.get_disjoint_mut(indexes);
                let item1 = items[0].take().expect("key1 index is valid");
                let item2 = items[1].take().expect("key2 index is valid");
                let hashes1 =
                    self.tables.make_hashes::<T>(&item1.key1(), &item1.key2());
                let hashes2 =
                    self.tables.make_hashes::<T>(&item2.key1(), &item2.key2());

                OccupiedEntryMut::NonUnique {
                    by_key1: Some(RefMut::new(state.clone(), hashes1, item1)),
                    by_key2: Some(RefMut::new(state, hashes2, item2)),
                }
            }
        }
    }

    pub(super) fn get_by_index_mut(
        &mut self,
        index: usize,
    ) -> Option<RefMut<'_, T, S>> {
        let borrowed = self.items.get_mut(index)?;
        let state = self.tables.state.clone();
        let hashes =
            self.tables.make_hashes::<T>(&borrowed.key1(), &borrowed.key2());
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
        let state = &self.tables.state;
        let (e1, e2) = {
            let k1 = value.key1();
            let k2 = value.key2();

            let e1 = detect_dup_or_insert(
                self.tables
                    .k1_to_item
                    .entry(state, k1, |index| self.items[index].key1()),
                &mut duplicates,
            );
            let e2 = detect_dup_or_insert(
                self.tables
                    .k2_to_item
                    .entry(state, k2, |index| self.items[index].key2()),
                &mut duplicates,
            );
            (e1, e2)
        };

        if !duplicates.is_empty() {
            return Err(DuplicateItem::__internal_new(
                value,
                duplicates.iter().map(|ix| &self.items[*ix]).collect(),
            ));
        }

        let next_index = self.items.insert_at_next_index(value);
        // e1 and e2 are all Some because if they were None, duplicates
        // would be non-empty, and we'd have bailed out earlier.
        e1.unwrap().insert(next_index);
        e2.unwrap().insert(next_index);

        Ok(next_index)
    }

    pub(super) fn remove_by_entry_index(
        &mut self,
        indexes: EntryIndexes,
    ) -> Vec<T> {
        match indexes {
            EntryIndexes::Unique(index) => {
                // Since all keys match, we can simply replace the item.
                let old_item =
                    self.remove_by_index(index).expect("index is valid");
                vec![old_item]
            }
            EntryIndexes::NonUnique { index1, index2 } => {
                let mut old_items = Vec::new();
                if let Some(index1) = index1 {
                    old_items.push(
                        self.remove_by_index(index1).expect("index1 is valid"),
                    );
                }
                if let Some(index2) = index2 {
                    old_items.push(
                        self.remove_by_index(index2).expect("index2 is valid"),
                    );
                }

                old_items
            }
        }
    }

    pub(super) fn remove_by_index(&mut self, remove_index: usize) -> Option<T> {
        let value = self.items.remove(remove_index)?;

        // Remove the value from the tables.
        let state = &self.tables.state;
        let Ok(item1) =
            self.tables.k1_to_item.find_entry(state, &value.key1(), |index| {
                if index == remove_index {
                    value.key1()
                } else {
                    self.items[index].key1()
                }
            })
        else {
            // The item was not found.
            panic!("remove_index {remove_index} not found in k1_to_item");
        };
        let Ok(item2) =
            self.tables.k2_to_item.find_entry(state, &value.key2(), |index| {
                if index == remove_index {
                    value.key2()
                } else {
                    self.items[index].key2()
                }
            })
        else {
            // The item was not found.
            panic!("remove_index {remove_index} not found in k2_to_item")
        };

        item1.remove();
        item2.remove();

        Some(value)
    }

    pub(super) fn replace_at_indexes(
        &mut self,
        indexes: EntryIndexes,
        value: T,
    ) -> (usize, Vec<T>) {
        match indexes {
            EntryIndexes::Unique(index) => {
                let old_item = &self.items[index];
                if old_item.key1() != value.key1() {
                    panic!("key1 mismatch");
                }
                if old_item.key2() != value.key2() {
                    panic!("key2 mismatch");
                }

                // Since all keys match, we can simply replace the item.
                let old_item = self.items.replace(index, value);
                (index, vec![old_item])
            }
            EntryIndexes::NonUnique { index1, index2 } => {
                let mut old_items = Vec::new();
                if let Some(index1) = index1 {
                    let old_item = &self.items[index1];
                    if old_item.key1() != value.key1() {
                        panic!("key1 mismatch");
                    }
                    old_items.push(self.remove_by_index(index1).unwrap());
                }
                if let Some(index2) = index2 {
                    let old_item = &self.items[index2];
                    if old_item.key2() != value.key2() {
                        panic!("key2 mismatch");
                    }
                    old_items.push(self.remove_by_index(index2).unwrap());
                }

                // Insert the new item.
                let Ok(next_index) = self.insert_unique_impl(value) else {
                    unreachable!(
                        "insert_unique cannot fail after removing duplicates"
                    );
                };
                (next_index, old_items)
            }
        }
    }
}

impl<'a, T, S, A> fmt::Debug for BiHashMap<T, S, A>
where
    T: BiHashItem + fmt::Debug,
    T::K1<'a>: fmt::Debug,
    T::K2<'a>: fmt::Debug,
    T: 'a,
    A: Allocator,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        for item in self.items.values() {
            let key: KeyMap<'_, T> =
                KeyMap { key1: item.key1(), key2: item.key2() };

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
            let key: KeyMap<'a, T> = unsafe {
                core::mem::transmute::<KeyMap<'_, T>, KeyMap<'a, T>>(key)
            };

            map.entry(&key as &dyn fmt::Debug, item);
        }
        map.finish()
    }
}

struct KeyMap<'a, T: BiHashItem + 'a> {
    key1: T::K1<'a>,
    key2: T::K2<'a>,
}

impl<'a, T: BiHashItem + 'a> fmt::Debug for KeyMap<'a, T>
where
    T::K1<'a>: fmt::Debug,
    T::K2<'a>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // We don't want to show key1 and key2 as a tuple since it's
        // misleading (suggests maps of tuples). The best we can do
        // instead is to show "{k1: "abc", k2: "xyz"}"
        f.debug_map()
            .entry(&StrDisplayAsDebug("k1"), &self.key1)
            .entry(&StrDisplayAsDebug("k2"), &self.key2)
            .finish()
    }
}

/// The `PartialEq` implementation for `BiHashMap` checks that both maps have
/// the same items, regardless of insertion order.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
///
/// #[derive(Debug, PartialEq, Eq)]
/// struct Item {
///     id: u32,
///     name: String,
///     value: i32,
/// }
///
/// impl BiHashItem for Item {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///     fn key2(&self) -> Self::K2<'_> {
///         &self.name
///     }
///     bi_upcast!();
/// }
///
/// let mut map1 = BiHashMap::new();
/// map1.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
///     .unwrap();
/// map1.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
///     .unwrap();
///
/// let mut map2 = BiHashMap::new();
/// map2.insert_unique(Item { id: 2, name: "bar".to_string(), value: 99 })
///     .unwrap();
/// map2.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 })
///     .unwrap();
///
/// // Maps are equal even if items were inserted in different order
/// assert_eq!(map1, map2);
///
/// map2.insert_unique(Item { id: 3, name: "baz".to_string(), value: 200 })
///     .unwrap();
/// assert_ne!(map1, map2);
/// # }
/// ```
impl<T: BiHashItem + PartialEq, S: Clone + BuildHasher, A: Allocator> PartialEq
    for BiHashMap<T, S, A>
{
    fn eq(&self, other: &Self) -> bool {
        // Implementing PartialEq for BiHashMap is tricky because BiHashMap is
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
            let k1 = item.key1();
            let k2 = item.key2();

            // Check that the indexes are the same in the other map.
            let Some(other_ix1) = other.find1_index(&k1) else {
                return false;
            };
            let Some(other_ix2) = other.find2_index(&k2) else {
                return false;
            };

            if other_ix1 != other_ix2 {
                // All the keys were present but they didn't point to the same
                // item.
                return false;
            }

            // Check that the other map's item is the same as this map's
            // item. (This is what we use the `PartialEq` bound on T for.)
            //
            // Because we've checked that other_ix1 and other_ix2 are
            // Some, we know that it is valid and points to the expected item.
            let other_item = &other.items[other_ix1];
            if item != other_item {
                return false;
            }
        }

        true
    }
}

// The Eq bound on T ensures that the BiHashMap forms an equivalence class.
impl<T: BiHashItem + Eq, S: Clone + BuildHasher, A: Allocator> Eq
    for BiHashMap<T, S, A>
{
}

fn detect_dup_or_insert<'a, A: Allocator>(
    item: hash_table::Entry<'a, usize, AllocWrapper<A>>,
    duplicates: &mut BTreeSet<usize>,
) -> Option<hash_table::VacantEntry<'a, usize, AllocWrapper<A>>> {
    match item {
        hash_table::Entry::Vacant(slot) => Some(slot),
        hash_table::Entry::Occupied(slot) => {
            duplicates.insert(*slot.get());
            None
        }
    }
}

/// The `Extend` implementation overwrites duplicates. In the future, there will
/// also be an `extend_unique` method that will return an error.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
///
/// #[derive(Debug, PartialEq, Eq)]
/// struct Item {
///     id: u32,
///     name: String,
///     value: i32,
/// }
///
/// impl BiHashItem for Item {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///     fn key2(&self) -> Self::K2<'_> {
///         &self.name
///     }
///     bi_upcast!();
/// }
///
/// let mut map = BiHashMap::new();
/// map.insert_unique(Item { id: 1, name: "foo".to_string(), value: 42 }).unwrap();
///
/// let new_items = vec![
///     Item { id: 2, name: "bar".to_string(), value: 99 },
///     Item { id: 1, name: "baz".to_string(), value: 100 }, // overwrites existing
/// ];
///
/// map.extend(new_items);
/// assert_eq!(map.len(), 2);
/// assert_eq!(map.get1(&1).unwrap().name, "baz"); // overwritten
/// assert_eq!(map.get1(&1).unwrap().value, 100);
/// # }
/// ```
impl<T: BiHashItem, S: Clone + BuildHasher, A: Allocator> Extend<T>
    for BiHashMap<T, S, A>
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

impl<'a, T: BiHashItem, S: Clone + BuildHasher, A: Allocator> IntoIterator
    for &'a BiHashMap<T, S, A>
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: BiHashItem, S: Clone + BuildHasher, A: Allocator> IntoIterator
    for &'a mut BiHashMap<T, S, A>
{
    type Item = RefMut<'a, T, S>;
    type IntoIter = IterMut<'a, T, S, A>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: BiHashItem, S: Clone + BuildHasher, A: Allocator> IntoIterator
    for BiHashMap<T, S, A>
{
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self.items)
    }
}

/// The `FromIterator` implementation for `BiHashMap` overwrites duplicate
/// items.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
///
/// #[derive(Debug, PartialEq, Eq)]
/// struct Item {
///     id: u32,
///     name: String,
///     value: i32,
/// }
///
/// impl BiHashItem for Item {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///     fn key2(&self) -> Self::K2<'_> {
///         &self.name
///     }
///     bi_upcast!();
/// }
///
/// let items = vec![
///     Item { id: 1, name: "foo".to_string(), value: 42 },
///     Item { id: 2, name: "bar".to_string(), value: 99 },
///     Item { id: 1, name: "baz".to_string(), value: 100 }, // overwrites first item
/// ];
///
/// let map: BiHashMap<Item> = items.into_iter().collect();
/// assert_eq!(map.len(), 2);
/// assert_eq!(map.get1(&1).unwrap().name, "baz"); // overwritten
/// assert_eq!(map.get1(&1).unwrap().value, 100);
/// assert_eq!(map.get1(&2).unwrap().value, 99);
/// # }
/// ```
impl<T: BiHashItem, S: Clone + BuildHasher + Default, A: Default + Allocator>
    FromIterator<T> for BiHashMap<T, S, A>
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut map = BiHashMap::default();
        for item in iter {
            map.insert_overwrite(item);
        }
        map
    }
}
