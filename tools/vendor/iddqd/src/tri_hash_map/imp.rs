use super::{IntoIter, Iter, IterMut, RefMut, tables::TriHashMapTables};
use crate::{
    DefaultHashBuilder, TriHashItem,
    errors::DuplicateItem,
    internal::ValidationError,
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
use hashbrown::hash_table::{Entry, VacantEntry};

/// A 1:1:1 (trijective) map for three keys and a value.
///
/// The storage mechanism is a fast hash table of integer indexes to items, with
/// these indexes stored in three hashmaps. This allows for efficient lookups by
/// any of the three keys, while preventing duplicates.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
///
/// #[derive(Debug, PartialEq, Eq)]
/// struct Person {
///     id: u32,
///     email: String,
///     phone: String,
///     name: String,
/// }
///
/// // Implement TriHashItem to define the three key types.
/// impl TriHashItem for Person {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///     type K3<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///
///     fn key2(&self) -> Self::K2<'_> {
///         &self.email
///     }
///
///     fn key3(&self) -> Self::K3<'_> {
///         &self.phone
///     }
///
///     tri_upcast!();
/// }
///
/// // Create a TriHashMap and insert items.
/// let mut people = TriHashMap::new();
/// people
///     .insert_unique(Person {
///         id: 1,
///         email: "alice@example.com".to_string(),
///         phone: "555-1234".to_string(),
///         name: "Alice".to_string(),
///     })
///     .unwrap();
///
/// // Lookup by any of the three keys.
/// let person = people.get1(&1).unwrap();
/// assert_eq!(person.name, "Alice");
///
/// let person = people.get2("alice@example.com").unwrap();
/// assert_eq!(person.id, 1);
///
/// let person = people.get3("555-1234").unwrap();
/// assert_eq!(person.email, "alice@example.com");
/// # }
/// ```
#[derive(Clone)]
pub struct TriHashMap<T, S = DefaultHashBuilder, A: Allocator = Global> {
    pub(super) items: ItemSet<T, A>,
    // Invariant: the values (usize) in these tables are valid indexes into
    // `items`, and are a 1:1 mapping.
    tables: TriHashMapTables<S, A>,
}

impl<T: TriHashItem, S: Default, A: Allocator + Default> Default
    for TriHashMap<T, S, A>
{
    fn default() -> Self {
        Self {
            items: ItemSet::with_capacity_in(0, A::default()),
            tables: TriHashMapTables::default(),
        }
    }
}

#[cfg(feature = "default-hasher")]
impl<T: TriHashItem> TriHashMap<T> {
    /// Creates a new, empty `TriHashMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let map: TriHashMap<Person> = TriHashMap::new();
    /// assert!(map.is_empty());
    /// assert_eq!(map.len(), 0);
    /// # }
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self { items: ItemSet::new(), tables: TriHashMapTables::default() }
    }

    /// Creates a new `TriHashMap` with the given capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let map: TriHashMap<Person> = TriHashMap::with_capacity(10);
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, global_alloc()),
            tables: TriHashMapTables::with_capacity_and_hasher_in(
                capacity,
                DefaultHashBuilder::default(),
                global_alloc(),
            ),
        }
    }
}

impl<T: TriHashItem, S: BuildHasher> TriHashMap<T, S> {
    /// Creates a new, empty `TriHashMap` with the given hasher.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    /// use std::collections::hash_map::RandomState;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let map: TriHashMap<Person, RandomState> =
    ///     TriHashMap::with_hasher(RandomState::new());
    /// assert!(map.is_empty());
    /// ```
    pub const fn with_hasher(hasher: S) -> Self {
        Self {
            items: ItemSet::new(),
            tables: TriHashMapTables::with_hasher(hasher),
        }
    }

    /// Creates a new `TriHashMap` with the given capacity and hasher.
    ///
    /// # Examples
    ///
    /// ```
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    /// use std::collections::hash_map::RandomState;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let map: TriHashMap<Person, RandomState> =
    ///     TriHashMap::with_capacity_and_hasher(10, RandomState::new());
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hasher: S) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, global_alloc()),
            tables: TriHashMapTables::with_capacity_and_hasher_in(
                capacity,
                hasher,
                global_alloc(),
            ),
        }
    }
}

#[cfg(feature = "default-hasher")]
impl<T: TriHashItem, A: Clone + Allocator>
    TriHashMap<T, DefaultHashBuilder, A>
{
    /// Creates a new empty `TriHashMap` using the given allocator.
    ///
    /// Requires the `allocator-api2` feature to be enabled.
    ///
    /// # Examples
    ///
    /// Using the [`bumpalo`](https://docs.rs/bumpalo) allocator:
    ///
    /// ```
    /// # #[cfg(all(feature = "default-hasher", feature = "allocator-api2"))] {
    /// use iddqd::{TriHashMap, TriHashItem, tri_upcast};
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// // Create a new TriHashMap using the allocator.
    /// let map: TriHashMap<Person, _, &bumpalo::Bump> = TriHashMap::new_in(&bump);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn new_in(alloc: A) -> Self {
        Self {
            items: ItemSet::with_capacity_in(0, alloc.clone()),
            tables: TriHashMapTables::with_capacity_and_hasher_in(
                0,
                DefaultHashBuilder::default(),
                alloc,
            ),
        }
    }

    /// Creates an empty `TriHashMap` with the specified capacity using the given
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
    /// use iddqd::{TriHashMap, TriHashItem, tri_upcast};
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// // Create a new TriHashMap with capacity using the allocator.
    /// let map: TriHashMap<Person, _, &bumpalo::Bump> = TriHashMap::with_capacity_in(10, &bump);
    /// assert!(map.capacity() >= 10);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self {
            items: ItemSet::with_capacity_in(capacity, alloc.clone()),
            tables: TriHashMapTables::with_capacity_and_hasher_in(
                capacity,
                DefaultHashBuilder::default(),
                alloc,
            ),
        }
    }
}

impl<T: TriHashItem, S: Clone + BuildHasher, A: Clone + Allocator>
    TriHashMap<T, S, A>
{
    /// Creates a new, empty `TriHashMap` with the given hasher and allocator.
    ///
    /// Requires the `allocator-api2` feature to be enabled.
    ///
    /// # Examples
    ///
    /// Using the [`bumpalo`](https://docs.rs/bumpalo) allocator:
    ///
    /// ```
    /// # #[cfg(feature = "allocator-api2")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    /// use std::collections::hash_map::RandomState;
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// let hasher = RandomState::new();
    /// // Create a new TriHashMap with hasher using the allocator.
    /// let map: TriHashMap<Person, _, &bumpalo::Bump> =
    ///     TriHashMap::with_hasher_in(hasher, &bump);
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn with_hasher_in(hasher: S, alloc: A) -> Self {
        Self {
            items: ItemSet::with_capacity_in(0, alloc.clone()),
            tables: TriHashMapTables::with_capacity_and_hasher_in(
                0,
                hasher.clone(),
                alloc,
            ),
        }
    }

    /// Creates a new `TriHashMap` with the given capacity, hasher, and
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    /// use std::collections::hash_map::RandomState;
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// let hasher = RandomState::new();
    /// // Create a new TriHashMap with capacity and hasher using the allocator.
    /// let map: TriHashMap<Person, _, &bumpalo::Bump> =
    ///     TriHashMap::with_capacity_and_hasher_in(10, hasher, &bump);
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
            tables: TriHashMapTables::with_capacity_and_hasher_in(
                capacity, hasher, alloc,
            ),
        }
    }
}

impl<T: TriHashItem, S: Clone + BuildHasher, A: Allocator> TriHashMap<T, S, A> {
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
    /// use iddqd::{TriHashMap, TriHashItem, tri_upcast};
    /// # use iddqd_test_utils::bumpalo;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// // Define a new allocator.
    /// let bump = bumpalo::Bump::new();
    /// // Create a new TriHashMap using the allocator.
    /// let map: TriHashMap<Person, _, &bumpalo::Bump> = TriHashMap::new_in(&bump);
    /// // Access the allocator.
    /// let allocator = map.allocator();
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let map: TriHashMap<Person> = TriHashMap::with_capacity(10);
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    /// map.insert_unique(Person {
    ///     id: 2,
    ///     email: "bob@example.com".to_string(),
    ///     phone: "555-5678".to_string(),
    ///     name: "Bob".to_string(),
    /// })
    /// .unwrap();
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    /// assert_eq!(map.len(), 1);
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
        self.tables.k3_to_item.clear();
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `TriHashMap`. The collection may reserve more space to
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     email: String,
    /// }
    ///
    /// impl TriHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.email
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map: TriHashMap<Item> = TriHashMap::new();
    /// map.reserve(100);
    /// assert!(map.capacity() >= 100);
    /// # }
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional);
        self.tables.k1_to_item.reserve(additional);
        self.tables.k2_to_item.reserve(additional);
        self.tables.k3_to_item.reserve(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be
    /// inserted in the `TriHashMap`. The collection may reserve more space to
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     email: String,
    /// }
    ///
    /// impl TriHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.email
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map: TriHashMap<Item> = TriHashMap::new();
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
        self.tables
            .k3_to_item
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     email: String,
    /// }
    ///
    /// impl TriHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.email
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map: TriHashMap<Item> = TriHashMap::with_capacity(100);
    /// map.insert_unique(Item {
    ///     id: 1,
    ///     name: "foo".to_string(),
    ///     email: "foo@example.com".to_string(),
    /// })
    /// .unwrap();
    /// map.insert_unique(Item {
    ///     id: 2,
    ///     name: "bar".to_string(),
    ///     email: "bar@example.com".to_string(),
    /// })
    /// .unwrap();
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// # }
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.items.shrink_to_fit();
        self.tables.k1_to_item.shrink_to_fit();
        self.tables.k2_to_item.shrink_to_fit();
        self.tables.k3_to_item.shrink_to_fit();
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     email: String,
    /// }
    ///
    /// impl TriHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.email
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map: TriHashMap<Item> = TriHashMap::with_capacity(100);
    /// map.insert_unique(Item {
    ///     id: 1,
    ///     name: "foo".to_string(),
    ///     email: "foo@example.com".to_string(),
    /// })
    /// .unwrap();
    /// map.insert_unique(Item {
    ///     id: 2,
    ///     name: "bar".to_string(),
    ///     email: "bar@example.com".to_string(),
    /// })
    /// .unwrap();
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
        self.tables.k3_to_item.shrink_to(min_capacity);
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    /// map.insert_unique(Person {
    ///     id: 2,
    ///     email: "bob@example.com".to_string(),
    ///     phone: "555-5678".to_string(),
    ///     name: "Bob".to_string(),
    /// })
    /// .unwrap();
    ///
    /// let mut count = 0;
    /// for person in map.iter() {
    ///     assert!(person.id == 1 || person.id == 2);
    ///     count += 1;
    /// }
    /// assert_eq!(count, 2);
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// for mut person in map.iter_mut() {
    ///     person.name.push_str(" Updated");
    /// }
    ///
    /// let person = map.get1(&1).unwrap();
    /// assert_eq!(person.name, "Alice Updated");
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
        compactness: crate::internal::ValidateCompact,
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
            let key3 = item.key3();

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
            let Some(ix3) = self.find3_index(&key3) else {
                return Err(ValidationError::general(format!(
                    "item at index {ix} has no key3 index"
                )));
            };

            if ix1 != ix || ix2 != ix || ix3 != ix {
                return Err(ValidationError::general(format!(
                    "item at index {ix} has inconsistent indexes: {ix1}/{ix2}/{ix3}"
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    ///
    /// // First insertion - no conflicts
    /// let overwritten = map.insert_overwrite(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// });
    /// assert!(overwritten.is_empty());
    ///
    /// // Overwrite with same id - returns the old item
    /// let overwritten = map.insert_overwrite(Person {
    ///     id: 1,
    ///     email: "alice.new@example.com".to_string(),
    ///     phone: "555-9999".to_string(),
    ///     name: "Alice New".to_string(),
    /// });
    /// assert_eq!(overwritten.len(), 1);
    /// assert_eq!(overwritten[0].name, "Alice");
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
        duplicates.extend(self.remove3(&value.key3()));

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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    ///
    /// // Successful insertion
    /// assert!(
    ///     map.insert_unique(Person {
    ///         id: 1,
    ///         email: "alice@example.com".to_string(),
    ///         phone: "555-1234".to_string(),
    ///         name: "Alice".to_string(),
    ///     })
    ///     .is_ok()
    /// );
    /// assert!(
    ///     map.insert_unique(Person {
    ///         id: 2,
    ///         email: "bob@example.com".to_string(),
    ///         phone: "555-5678".to_string(),
    ///         name: "Bob".to_string(),
    ///     })
    ///     .is_ok()
    /// );
    ///
    /// // Duplicate key1
    /// assert!(
    ///     map.insert_unique(Person {
    ///         id: 1,
    ///         email: "charlie@example.com".to_string(),
    ///         phone: "555-9999".to_string(),
    ///         name: "Charlie".to_string(),
    ///     })
    ///     .is_err()
    /// );
    ///
    /// // Duplicate key2
    /// assert!(
    ///     map.insert_unique(Person {
    ///         id: 3,
    ///         email: "alice@example.com".to_string(),
    ///         phone: "555-7777".to_string(),
    ///         name: "Alice2".to_string(),
    ///     })
    ///     .is_err()
    /// );
    ///
    /// // Duplicate key3
    /// assert!(
    ///     map.insert_unique(Person {
    ///         id: 4,
    ///         email: "dave@example.com".to_string(),
    ///         phone: "555-1234".to_string(),
    ///         name: "Dave".to_string(),
    ///     })
    ///     .is_err()
    /// );
    /// # }
    /// ```
    pub fn insert_unique(
        &mut self,
        value: T,
    ) -> Result<(), DuplicateItem<T, &T>> {
        let mut duplicates = BTreeSet::new();

        // Check for duplicates *before* inserting the new item, because we
        // don't want to partially insert the new item and then have to roll
        // back.
        let state = &self.tables.state;
        let (e1, e2, e3) = {
            let k1 = value.key1();
            let k2 = value.key2();
            let k3 = value.key3();

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
            let e3 = detect_dup_or_insert(
                self.tables
                    .k3_to_item
                    .entry(state, k3, |index| self.items[index].key3()),
                &mut duplicates,
            );
            (e1, e2, e3)
        };

        if !duplicates.is_empty() {
            return Err(DuplicateItem::__internal_new(
                value,
                duplicates.iter().map(|ix| &self.items[*ix]).collect(),
            ));
        }

        let next_index = self.items.insert_at_next_index(value);
        // e1, e2 and e3 are all Some because if they were None, duplicates
        // would be non-empty, and we'd have bailed out earlier.
        e1.unwrap().insert(next_index);
        e2.unwrap().insert(next_index);
        e3.unwrap().insert(next_index);

        Ok(())
    }

    /// Returns true if the map contains a single item that matches all three
    /// keys.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// }).unwrap();
    /// map.insert_unique(Person {
    ///     id: 2,
    ///     email: "bob@example.com".to_string(),
    ///     phone: "555-5678".to_string(),
    ///     name: "Bob".to_string(),
    /// }).unwrap();
    ///
    /// assert!(map.contains_key_unique(&1, &"alice@example.com", &"555-1234"));
    /// assert!(map.contains_key_unique(&2, &"bob@example.com", &"555-5678"));
    /// assert!(!map.contains_key_unique(&1, &"bob@example.com", &"555-1234")); // key1 exists but key2 doesn't match
    /// assert!(!map.contains_key_unique(&3, &"charlie@example.com", &"555-9999")); // none of the keys exist
    /// # }
    /// ```
    pub fn contains_key_unique<'a, Q1, Q2, Q3>(
        &'a self,
        key1: &Q1,
        key2: &Q2,
        key3: &Q3,
    ) -> bool
    where
        Q1: Hash + Equivalent<T::K1<'a>> + ?Sized,
        Q2: Hash + Equivalent<T::K2<'a>> + ?Sized,
        Q3: Hash + Equivalent<T::K3<'a>> + ?Sized,
    {
        self.get_unique(key1, key2, key3).is_some()
    }

    /// Gets a reference to the unique item associated with the given `key1`,
    /// `key2`, and `key3`, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// // All three keys must match
    /// assert_eq!(
    ///     map.get_unique(&1, &"alice@example.com", &"555-1234").unwrap().name,
    ///     "Alice"
    /// );
    ///
    /// // If any key doesn't match, returns None
    /// assert!(map.get_unique(&1, &"wrong@example.com", &"555-1234").is_none());
    /// assert!(map.get_unique(&2, &"alice@example.com", &"555-1234").is_none());
    /// # }
    /// ```
    pub fn get_unique<'a, Q1, Q2, Q3>(
        &'a self,
        key1: &Q1,
        key2: &Q2,
        key3: &Q3,
    ) -> Option<&'a T>
    where
        Q1: Hash + Equivalent<T::K1<'a>> + ?Sized,
        Q2: Hash + Equivalent<T::K2<'a>> + ?Sized,
        Q3: Hash + Equivalent<T::K3<'a>> + ?Sized,
    {
        let index = self.find1_index(key1)?;
        let item = &self.items[index];
        if key2.equivalent(&item.key2()) && key3.equivalent(&item.key3()) {
            Some(item)
        } else {
            None
        }
    }

    /// Gets a mutable reference to the unique item associated with the given
    /// `key1`, `key2`, and `key3`, if it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// // Modify the item through the mutable reference
    /// if let Some(mut person) =
    ///     map.get_mut_unique(&1, &"alice@example.com", &"555-1234")
    /// {
    ///     person.name = "Alice Updated".to_string();
    /// }
    ///
    /// // Verify the change
    /// assert_eq!(map.get1(&1).unwrap().name, "Alice Updated");
    /// # }
    /// ```
    pub fn get_mut_unique<'a, Q1, Q2, Q3>(
        &'a mut self,
        key1: &Q1,
        key2: &Q2,
        key3: &Q3,
    ) -> Option<RefMut<'a, T, S>>
    where
        Q1: Hash + Equivalent<T::K1<'a>> + ?Sized,
        Q2: Hash + Equivalent<T::K2<'a>> + ?Sized,
        Q3: Hash + Equivalent<T::K3<'a>> + ?Sized,
    {
        let (dormant_map, index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let index = map.find1_index(key1)?;
            let item = &map.items[index];
            if !key2.equivalent(&item.key2()) || !key3.equivalent(&item.key3())
            {
                return None;
            }
            (dormant_map, index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };
        let item = &mut awakened_map.items[index];
        let state = awakened_map.tables.state.clone();
        let hashes = awakened_map.tables.make_hashes(&item);
        Some(RefMut::new(state, hashes, item))
    }

    /// Removes the item uniquely identified by `key1`, `key2`, and `key3`, if
    /// it exists.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// // Remove the item using all three keys
    /// let removed = map.remove_unique(&1, &"alice@example.com", &"555-1234");
    /// assert!(removed.is_some());
    /// assert_eq!(removed.unwrap().name, "Alice");
    ///
    /// // Map is now empty
    /// assert!(map.is_empty());
    ///
    /// // Trying to remove again returns None
    /// assert!(map.remove_unique(&1, &"alice@example.com", &"555-1234").is_none());
    /// # }
    /// ```
    pub fn remove_unique<'a, Q1, Q2, Q3>(
        &'a mut self,
        key1: &Q1,
        key2: &Q2,
        key3: &Q3,
    ) -> Option<T>
    where
        Q1: Hash + Equivalent<T::K1<'a>> + ?Sized,
        Q2: Hash + Equivalent<T::K2<'a>> + ?Sized,
        Q3: Hash + Equivalent<T::K3<'a>> + ?Sized,
    {
        let (dormant_map, remove_index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let remove_index = map.find1_index(key1)?;
            let item = &map.items[remove_index];
            if !key2.equivalent(&item.key2()) && !key3.equivalent(&item.key3())
            {
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// assert!(map.contains_key1(&1));
    /// assert!(!map.contains_key1(&2));
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// assert_eq!(map.get1(&1).unwrap().name, "Alice");
    /// assert!(map.get1(&2).is_none());
    /// # }
    /// ```
    pub fn get1<'a, Q>(&'a self, key1: &Q) -> Option<&'a T>
    where
        Q: Hash + Equivalent<T::K1<'a>> + ?Sized,
    {
        self.find1(key1)
    }

    /// Gets a mutable reference to the value associated with the given `key1`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// if let Some(mut person) = map.get1_mut(&1) {
    ///     person.name = "Alice Updated".to_string();
    /// }
    ///
    /// assert_eq!(map.get1(&1).unwrap().name, "Alice Updated");
    /// # }
    /// ```
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
        let hashes = awakened_map.tables.make_hashes(&item);
        Some(RefMut::new(state, hashes, item))
    }

    /// Removes an item from the map by its `key1`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// let removed = map.remove1(&1);
    /// assert!(removed.is_some());
    /// assert_eq!(removed.unwrap().name, "Alice");
    /// assert!(map.is_empty());
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// assert!(map.contains_key2("alice@example.com"));
    /// assert!(!map.contains_key2("bob@example.com"));
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// assert_eq!(map.get2("alice@example.com").unwrap().name, "Alice");
    /// assert!(map.get2("bob@example.com").is_none());
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
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// if let Some(mut person) = map.get2_mut("alice@example.com") {
    ///     person.name = "Alice Updated".to_string();
    /// }
    ///
    /// assert_eq!(map.get2("alice@example.com").unwrap().name, "Alice Updated");
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
        let hashes = awakened_map.tables.make_hashes(&item);
        Some(RefMut::new(state, hashes, item))
    }

    /// Removes an item from the map by its `key2`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// let removed = map.remove2("alice@example.com");
    /// assert!(removed.is_some());
    /// assert_eq!(removed.unwrap().name, "Alice");
    /// assert!(map.is_empty());
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

    /// Returns true if the map contains the given `key3`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// assert!(map.contains_key3("555-1234"));
    /// assert!(!map.contains_key3("555-5678"));
    /// # }
    /// ```
    pub fn contains_key3<'a, Q>(&'a self, key3: &Q) -> bool
    where
        Q: Hash + Equivalent<T::K3<'a>> + ?Sized,
    {
        self.find3_index(key3).is_some()
    }

    /// Gets a reference to the value associated with the given `key3`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// assert_eq!(map.get3("555-1234").unwrap().name, "Alice");
    /// assert!(map.get3("555-5678").is_none());
    /// # }
    /// ```
    pub fn get3<'a, Q>(&'a self, key3: &Q) -> Option<&'a T>
    where
        Q: Hash + Equivalent<T::K3<'a>> + ?Sized,
    {
        self.find3(key3)
    }

    /// Gets a mutable reference to the value associated with the given `key3`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// if let Some(mut person) = map.get3_mut("555-1234") {
    ///     person.name = "Alice Updated".to_string();
    /// }
    ///
    /// assert_eq!(map.get3("555-1234").unwrap().name, "Alice Updated");
    /// # }
    /// ```
    pub fn get3_mut<'a, Q>(&'a mut self, key3: &Q) -> Option<RefMut<'a, T, S>>
    where
        Q: Hash + Equivalent<T::K3<'a>> + ?Sized,
    {
        let (dormant_map, index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let index = map.find3_index(key3)?;
            (dormant_map, index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };
        let item = &mut awakened_map.items[index];
        let state = awakened_map.tables.state.clone();
        let hashes = awakened_map.tables.make_hashes(&item);
        Some(RefMut::new(state, hashes, item))
    }

    /// Removes an item from the map by its `key3`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct Person {
    ///     id: u32,
    ///     email: String,
    ///     phone: String,
    ///     name: String,
    /// }
    ///
    /// impl TriHashItem for Person {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.email
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.phone
    ///     }
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Person {
    ///     id: 1,
    ///     email: "alice@example.com".to_string(),
    ///     phone: "555-1234".to_string(),
    ///     name: "Alice".to_string(),
    /// })
    /// .unwrap();
    ///
    /// let removed = map.remove3("555-1234");
    /// assert!(removed.is_some());
    /// assert_eq!(removed.unwrap().name, "Alice");
    /// assert!(map.is_empty());
    /// # }
    /// ```
    pub fn remove3<'a, Q>(&'a mut self, key3: &Q) -> Option<T>
    where
        Q: Hash + Equivalent<T::K3<'a>> + ?Sized,
    {
        let (dormant_map, remove_index) = {
            let (map, dormant_map) = DormantMutRef::new(self);
            let remove_index = map.find3_index(key3)?;
            (dormant_map, remove_index)
        };

        // SAFETY: `map` is not used after this point.
        let awakened_map = unsafe { dormant_map.awaken() };

        awakened_map.remove_by_index(remove_index)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all items `T` for which `f(RefMut<T>)` returns
    /// false. The elements are visited in an arbitrary order.
    ///
    /// The `RefMut<T, S>` wrapper allows mutable access to the item while
    /// enforcing that the three keys (`K1`, `K2`, `K3`) remain unchanged. If
    /// a key is modified during iteration, the method will panic.
    ///
    /// # Performance considerations
    ///
    /// This method may leave the internal storage fragmented. If you need
    /// compact storage afterward, call `make_compact()`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "default-hasher")] {
    /// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
    ///
    /// #[derive(Debug, PartialEq, Eq, Hash)]
    /// struct Item {
    ///     id: u32,
    ///     name: String,
    ///     code: String,
    ///     value: u32,
    /// }
    ///
    /// impl TriHashItem for Item {
    ///     type K1<'a> = u32;
    ///     type K2<'a> = &'a str;
    ///     type K3<'a> = &'a str;
    ///
    ///     fn key1(&self) -> Self::K1<'_> {
    ///         self.id
    ///     }
    ///     fn key2(&self) -> Self::K2<'_> {
    ///         &self.name
    ///     }
    ///     fn key3(&self) -> Self::K3<'_> {
    ///         &self.code
    ///     }
    ///
    ///     tri_upcast!();
    /// }
    ///
    /// let mut map = TriHashMap::new();
    /// map.insert_unique(Item {
    ///     id: 1,
    ///     name: "foo".to_string(),
    ///     code: "x".to_string(),
    ///     value: 42,
    /// })
    /// .unwrap();
    /// map.insert_unique(Item {
    ///     id: 2,
    ///     name: "bar".to_string(),
    ///     code: "y".to_string(),
    ///     value: 20,
    /// })
    /// .unwrap();
    /// map.insert_unique(Item {
    ///     id: 3,
    ///     name: "baz".to_string(),
    ///     code: "z".to_string(),
    ///     value: 99,
    /// })
    /// .unwrap();
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
                let key3 = T::key3(item);
                let hash1 = hash_state.hash_one(key1);
                let hash2 = hash_state.hash_one(key2);
                let hash3 = hash_state.hash_one(key3);
                (
                    [
                        MapHash::new(hash1),
                        MapHash::new(hash2),
                        MapHash::new(hash3),
                    ],
                    dormant_item,
                )
            };

            let hash2 = hashes[1].hash();
            let hash3 = hashes[2].hash();
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
                let k3_entry = self
                    .tables
                    .k3_to_item
                    .find_entry_by_hash(hash3, |map3_index| {
                        map3_index == index
                    });

                let mut is_inconsistent = false;
                if let Ok(k2_entry) = k2_entry {
                    k2_entry.remove();
                } else {
                    is_inconsistent = true;
                }
                if let Ok(k3_entry) = k3_entry {
                    k3_entry.remove();
                } else {
                    is_inconsistent = true;
                }
                if is_inconsistent {
                    // This happening means there's an inconsistency among
                    // the maps.
                    panic!(
                        "inconsistency among k1_to_item, k2_to_item, k3_to_item"
                    );
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

    fn find3<'a, Q>(&'a self, k: &Q) -> Option<&'a T>
    where
        Q: Hash + Equivalent<T::K3<'a>> + ?Sized,
    {
        self.find3_index(k).map(|ix| &self.items[ix])
    }

    fn find3_index<'a, Q>(&'a self, k: &Q) -> Option<usize>
    where
        Q: Hash + Equivalent<T::K3<'a>> + ?Sized,
    {
        self.tables
            .k3_to_item
            .find_index(&self.tables.state, k, |index| self.items[index].key3())
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
        let Ok(item3) =
            self.tables.k3_to_item.find_entry(state, &value.key3(), |index| {
                if index == remove_index {
                    value.key3()
                } else {
                    self.items[index].key3()
                }
            })
        else {
            // The item was not found.
            panic!("remove_index {remove_index} not found in k3_to_item")
        };

        item1.remove();
        item2.remove();
        item3.remove();

        Some(value)
    }
}

impl<'a, T, S, A: Allocator> fmt::Debug for TriHashMap<T, S, A>
where
    T: TriHashItem + fmt::Debug,
    T::K1<'a>: fmt::Debug,
    T::K2<'a>: fmt::Debug,
    T::K3<'a>: fmt::Debug,
    T: 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        for item in self.items.values() {
            let key: KeyMap<'_, T> = KeyMap {
                key1: item.key1(),
                key2: item.key2(),
                key3: item.key3(),
            };

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

            map.entry(&key, item);
        }
        map.finish()
    }
}

struct KeyMap<'a, T: TriHashItem + 'a> {
    key1: T::K1<'a>,
    key2: T::K2<'a>,
    key3: T::K3<'a>,
}

impl<'a, T: TriHashItem> fmt::Debug for KeyMap<'a, T>
where
    T::K1<'a>: fmt::Debug,
    T::K2<'a>: fmt::Debug,
    T::K3<'a>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // We don't want to show key1 and key2 as a tuple since it's
        // misleading (suggests maps of tuples). The best we can do
        // instead is to show "{k1: abc, k2: xyz, k3: def}"
        f.debug_map()
            .entry(&StrDisplayAsDebug("k1"), &self.key1)
            .entry(&StrDisplayAsDebug("k2"), &self.key2)
            .entry(&StrDisplayAsDebug("k3"), &self.key3)
            .finish()
    }
}

impl<T: TriHashItem + PartialEq, S: Clone + BuildHasher, A: Allocator> PartialEq
    for TriHashMap<T, S, A>
{
    fn eq(&self, other: &Self) -> bool {
        // Implementing PartialEq for TriHashMap is tricky because TriHashMap is
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
            let k3 = item.key3();

            // Check that the indexes are the same in the other map.
            let Some(other_ix1) = other.find1_index(&k1) else {
                return false;
            };
            let Some(other_ix2) = other.find2_index(&k2) else {
                return false;
            };
            let Some(other_ix3) = other.find3_index(&k3) else {
                return false;
            };

            if other_ix1 != other_ix2 || other_ix1 != other_ix3 {
                // All the keys were present but they didn't point to the same
                // item.
                return false;
            }

            // Check that the other map's item is the same as this map's
            // item. (This is what we use the `PartialEq` bound on T for.)
            //
            // Because we've checked that other_ix1, other_ix2 and other_ix3 are
            // Some, we know that it is valid and points to the expected item.
            let other_item = &other.items[other_ix1];
            if item != other_item {
                return false;
            }
        }

        true
    }
}

// The Eq bound on T ensures that the TriHashMap forms an equivalence class.
impl<T: TriHashItem + Eq, S: Clone + BuildHasher, A: Allocator> Eq
    for TriHashMap<T, S, A>
{
}

/// The `Extend` implementation overwrites duplicates. In the future, there will
/// also be an `extend_unique` method that will return an error.
impl<T: TriHashItem, S: Clone + BuildHasher, A: Allocator> Extend<T>
    for TriHashMap<T, S, A>
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

fn detect_dup_or_insert<'a, A: Allocator>(
    item: Entry<'a, usize, AllocWrapper<A>>,
    duplicates: &mut BTreeSet<usize>,
) -> Option<VacantEntry<'a, usize, AllocWrapper<A>>> {
    match item {
        Entry::Vacant(slot) => Some(slot),
        Entry::Occupied(slot) => {
            duplicates.insert(*slot.get());
            None
        }
    }
}

impl<'a, T: TriHashItem, S: Clone + BuildHasher, A: Allocator> IntoIterator
    for &'a TriHashMap<T, S, A>
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: TriHashItem, S: Clone + BuildHasher, A: Allocator> IntoIterator
    for &'a mut TriHashMap<T, S, A>
{
    type Item = RefMut<'a, T, S>;
    type IntoIter = IterMut<'a, T, S, A>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: TriHashItem, S: Clone + BuildHasher, A: Allocator> IntoIterator
    for TriHashMap<T, S, A>
{
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self.items)
    }
}

/// The `FromIterator` implementation for `TriHashMap` overwrites duplicate
/// items.
impl<T: TriHashItem, S: Default + Clone + BuildHasher, A: Default + Allocator>
    FromIterator<T> for TriHashMap<T, S, A>
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut map = TriHashMap::default();
        for item in iter {
            map.insert_overwrite(item);
        }
        map
    }
}
