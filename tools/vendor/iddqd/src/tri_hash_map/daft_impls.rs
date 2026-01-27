// `Diffable` implementation.

use super::{TriHashItem, TriHashMap};
use crate::{
    DefaultHashBuilder, IdHashItem, id_hash_map,
    support::{
        alloc::{Allocator, Global},
        daft_utils::IdLeaf,
    },
};
use core::{
    fmt,
    hash::{BuildHasher, Hash},
};
use daft::Diffable;
use equivalent::Equivalent;
use ref_cast::RefCast;

impl<T: TriHashItem, S: Clone + BuildHasher, A: Allocator> Diffable
    for TriHashMap<T, S, A>
{
    type Diff<'a>
        = MapLeaf<'a, T, S, A>
    where
        T: 'a,
        S: 'a,
        A: 'a;

    fn diff<'daft>(&'daft self, other: &'daft Self) -> Self::Diff<'daft> {
        MapLeaf { before: self, after: other }
    }
}

/// A leaf diff of two [`TriHashMap`]s.
///
/// This diff is lazy and has not been evaluated yet. To evaluate the diff,
/// call:
///
/// * [`Self::by_key1`] to get a diff indexed by `key1`.
/// * [`Self::by_key2`] to get a diff indexed by `key2`.
/// * [`Self::by_key3`] to get a diff indexed by `key3`.
/// * [`Self::by_unique`] to get a diff indexed by `key1`, `key2`, and `key3`.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use daft::Diffable;
/// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
///
/// #[derive(Eq, PartialEq)]
/// struct Item {
///     id: u32,
///     name: String,
///     email: String,
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
///
///     fn key2(&self) -> Self::K2<'_> {
///         &self.name
///     }
///
///     fn key3(&self) -> Self::K3<'_> {
///         &self.email
///     }
///
///     tri_upcast!();
/// }
///
/// // Create two TriHashMaps with overlapping items.
/// let mut map1 = TriHashMap::new();
/// map1.insert_unique(Item {
///     id: 1,
///     name: "alice".to_string(),
///     email: "alice@example.com".to_string(),
///     value: 10,
/// });
/// map1.insert_unique(Item {
///     id: 2,
///     name: "bob".to_string(),
///     email: "bob@example.com".to_string(),
///     value: 20,
/// });
///
/// let mut map2 = TriHashMap::new();
/// map2.insert_unique(Item {
///     id: 2,
///     name: "bob".to_string(),
///     email: "bob@example.com".to_string(),
///     value: 30,
/// });
/// map2.insert_unique(Item {
///     id: 3,
///     name: "charlie".to_string(),
///     email: "charlie@example.com".to_string(),
///     value: 40,
/// });
///
/// // Compute the diff between the two maps.
/// let map_leaf = map1.diff(&map2);
///
/// // Get diff by key1 (id).
/// let diff_by_id = map_leaf.by_key1();
/// // alice removed, bob modified, charlie added.
/// assert!(diff_by_id.removed.contains_key(&1));
/// assert!(diff_by_id.is_modified(&2));
/// assert!(diff_by_id.added.contains_key(&3));
///
/// // Get diff by key2 (name).
/// let diff_by_name = map_leaf.by_key2();
/// // alice removed, bob modified, charlie added.
/// assert!(diff_by_name.removed.contains_key("alice"));
/// assert!(diff_by_name.is_modified("bob"));
/// assert!(diff_by_name.added.contains_key("charlie"));
///
/// // Get diff by key3 (email).
/// let diff_by_email = map_leaf.by_key3();
/// // alice's email removed, bob's email modified, charlie's email added.
/// assert!(diff_by_email.removed.contains_key("alice@example.com"));
/// assert!(diff_by_email.is_modified("bob@example.com"));
/// assert!(diff_by_email.added.contains_key("charlie@example.com"));
///
/// // Get diff by unique combination of all three keys.
/// let diff_unique = map_leaf.by_unique();
/// // alice removed (by id, name and email)
/// assert!(diff_unique.removed.contains_key1(&1));
/// assert!(diff_unique.removed.contains_key2("alice"));
/// assert!(diff_unique.removed.contains_key3("alice@example.com"));
/// // bob modified (by id, name and email)
/// assert!(diff_unique.is_modified1(&2));
/// assert!(diff_unique.is_modified2("bob"));
/// assert!(diff_unique.is_modified3("bob@example.com"));
/// // charlie added (by id, name and email)
/// assert!(diff_unique.added.contains_key1(&3));
/// assert!(diff_unique.added.contains_key2("charlie"));
/// assert!(diff_unique.added.contains_key3("charlie@example.com"));
/// # }
/// ```
pub struct MapLeaf<
    'daft,
    T: TriHashItem,
    S = DefaultHashBuilder,
    A: Allocator = Global,
> {
    /// The before map.
    pub before: &'daft TriHashMap<T, S, A>,

    /// The after map.
    pub after: &'daft TriHashMap<T, S, A>,
}

impl<'a, 'daft, T: TriHashItem + fmt::Debug, S, A: Allocator> fmt::Debug
    for MapLeaf<'daft, T, S, A>
where
    T::K1<'a>: fmt::Debug,
    T::K2<'a>: fmt::Debug,
    T::K3<'a>: fmt::Debug,
    T: 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MapLeaf")
            .field("before", &self.before)
            .field("after", &self.after)
            .finish()
    }
}

impl<'daft, T: TriHashItem, S, A: Allocator> Clone for MapLeaf<'daft, T, S, A> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'daft, T: TriHashItem, S, A: Allocator> Copy for MapLeaf<'daft, T, S, A> {}

impl<'daft, T: TriHashItem + PartialEq, S: Clone + BuildHasher, A: Allocator>
    PartialEq for MapLeaf<'daft, T, S, A>
{
    fn eq(&self, other: &Self) -> bool {
        self.before == other.before && self.after == other.after
    }
}

impl<'daft, T: TriHashItem + Eq, S: Clone + BuildHasher, A: Allocator> Eq
    for MapLeaf<'daft, T, S, A>
{
}

impl<'daft, T: TriHashItem, S: Clone + BuildHasher, A: Clone + Allocator>
    MapLeaf<'daft, T, S, A>
{
    /// Returns a diff of two [`TriHashMap`]s, indexed by `key1`.
    ///
    /// Note that the return type is a [`Diff`].
    pub fn by_key1(self) -> id_hash_map::Diff<'daft, ByK1<T>, S, A> {
        impl_diff_ref_cast!(
            self,
            id_hash_map::Diff::<'daft, ByK1<T>, S, A>,
            key1,
            get1,
            contains_key1,
            ByK1<T>
        )
    }

    /// Returns a diff of two [`TriHashMap`]s, indexed by `key2`.
    ///
    /// Note that the return type is a [`Diff`].
    pub fn by_key2(self) -> id_hash_map::Diff<'daft, ByK2<T>, S, A> {
        impl_diff_ref_cast!(
            self,
            id_hash_map::Diff::<'daft, ByK2<T>, S, A>,
            key2,
            get2,
            contains_key2,
            ByK2<T>
        )
    }

    /// Returns a diff of two [`TriHashMap`]s, indexed by `key3`.
    ///
    /// Note that the return type is a [`Diff`].
    pub fn by_key3(self) -> id_hash_map::Diff<'daft, ByK3<T>, S, A> {
        impl_diff_ref_cast!(
            self,
            id_hash_map::Diff::<'daft, ByK3<T>, S, A>,
            key3,
            get3,
            contains_key3,
            ByK3<T>
        )
    }

    /// Returns a diff of two [`TriHashMap`]s, indexed by `key1`, `key2`, and `key3`.
    ///
    /// The return type is a [`Diff`].
    pub fn by_unique(self) -> Diff<'daft, T, S, A> {
        let mut diff = Diff::with_hasher_in(
            self.before.hasher().clone(),
            self.before.allocator().clone(),
        );
        for item in self.before {
            if let Some(after_item) =
                self.after.get_unique(&item.key1(), &item.key2(), &item.key3())
            {
                diff.common.insert_overwrite(IdLeaf::new(item, after_item));
            } else {
                diff.removed.insert_overwrite(item);
            }
        }
        for item in self.after {
            if !self.before.contains_key_unique(
                &item.key1(),
                &item.key2(),
                &item.key3(),
            ) {
                diff.added.insert_overwrite(item);
            }
        }
        diff
    }
}

/// A diff of two [`TriHashMap`]s, indexed by `key1`, `key2`, and `key3`.
pub struct Diff<
    'daft,
    T: ?Sized + TriHashItem,
    S = DefaultHashBuilder,
    A: Allocator = Global,
> {
    /// Entries common to both maps.
    ///
    /// Items are stored as [`IdLeaf`]s to references.
    pub common: TriHashMap<IdLeaf<&'daft T>, S, A>,

    /// Added entries.
    pub added: TriHashMap<&'daft T, S, A>,

    /// Removed entries.
    pub removed: TriHashMap<&'daft T, S, A>,
}

impl<'daft, T: ?Sized + TriHashItem, S: Default, A: Allocator + Default> Default
    for Diff<'daft, T, S, A>
{
    fn default() -> Self {
        Self {
            common: TriHashMap::default(),
            added: TriHashMap::default(),
            removed: TriHashMap::default(),
        }
    }
}

impl<'a, 'daft, T, S, A: Allocator> fmt::Debug for Diff<'daft, T, S, A>
where
    T: ?Sized + TriHashItem + fmt::Debug,
    T::K1<'a>: fmt::Debug,
    T::K2<'a>: fmt::Debug,
    T::K3<'a>: fmt::Debug,
    T: 'a,
    'daft: 'a,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Diff")
            .field("common", &self.common)
            .field("added", &self.added)
            .field("removed", &self.removed)
            .finish()
    }
}

#[cfg(all(feature = "default-hasher", feature = "allocator-api2"))]
impl<'daft, T: ?Sized + TriHashItem> Diff<'daft, T> {
    /// Creates a new, empty `Diff`.
    pub fn new() -> Self {
        Self {
            common: TriHashMap::new(),
            added: TriHashMap::new(),
            removed: TriHashMap::new(),
        }
    }
}

#[cfg(feature = "allocator-api2")]
impl<'daft, T: ?Sized + TriHashItem, S: Clone + BuildHasher> Diff<'daft, T, S> {
    /// Creates a new, empty `Diff` with the given hasher.
    pub fn with_hasher(hasher: S) -> Self {
        Self {
            common: TriHashMap::with_hasher(hasher.clone()),
            added: TriHashMap::with_hasher(hasher.clone()),
            removed: TriHashMap::with_hasher(hasher),
        }
    }
}

impl<
    'daft,
    T: ?Sized + TriHashItem,
    S: Clone + BuildHasher,
    A: Clone + Allocator,
> Diff<'daft, T, S, A>
{
    /// Creates a new, empty `Diff` with the given hasher and allocator.
    pub fn with_hasher_in(hasher: S, alloc: A) -> Self {
        Self {
            common: TriHashMap::with_hasher_in(hasher.clone(), alloc.clone()),
            added: TriHashMap::with_hasher_in(hasher.clone(), alloc.clone()),
            removed: TriHashMap::with_hasher_in(hasher, alloc),
        }
    }
}

impl<'daft, T: ?Sized + TriHashItem + Eq, S: Clone + BuildHasher, A: Allocator>
    Diff<'daft, T, S, A>
{
    /// Returns an iterator over unchanged keys and values.
    pub fn unchanged(&self) -> impl Iterator<Item = &'daft T> + '_ {
        self.common
            .iter()
            .filter_map(|leaf| leaf.is_unchanged().then_some(*leaf.before()))
    }

    /// Returns true if the item corresponding to `key1` is unchanged.
    pub fn is_unchanged1<'a, Q>(&'a self, key1: &Q) -> bool
    where
        Q: ?Sized + Hash + Equivalent<T::K1<'a>>,
    {
        self.common.get1(key1).is_some_and(|leaf| leaf.is_unchanged())
    }

    /// Returns true if the item corresponding to `key2` is unchanged.
    pub fn is_unchanged2<'a, Q>(&'a self, key2: &Q) -> bool
    where
        Q: ?Sized + Hash + Equivalent<T::K2<'a>>,
    {
        self.common.get2(key2).is_some_and(|leaf| leaf.is_unchanged())
    }

    /// Returns true if the item corresponding to `key3` is unchanged.
    pub fn is_unchanged3<'a, Q>(&'a self, key3: &Q) -> bool
    where
        Q: ?Sized + Hash + Equivalent<T::K3<'a>>,
    {
        self.common.get3(key3).is_some_and(|leaf| leaf.is_unchanged())
    }

    /// Returns the value associated with `key1` if it is unchanged,
    /// otherwise `None`.
    pub fn get_unchanged1<'a, Q>(&'a self, key: &Q) -> Option<&'daft T>
    where
        Q: ?Sized + Hash + Equivalent<T::K1<'a>>,
    {
        self.common
            .get1(key)
            .and_then(|leaf| leaf.is_unchanged().then_some(*leaf.before()))
    }

    /// Returns the value associated with `key2` if it is unchanged,
    /// otherwise `None`.
    pub fn get_unchanged2<'a, Q>(&'a self, key: &Q) -> Option<&'daft T>
    where
        Q: ?Sized + Hash + Equivalent<T::K2<'a>>,
    {
        self.common
            .get2(key)
            .and_then(|leaf| leaf.is_unchanged().then_some(*leaf.before()))
    }

    /// Returns the value associated with `key3` if it is unchanged,
    /// otherwise `None`.
    pub fn get_unchanged3<'a, Q>(&'a self, key: &Q) -> Option<&'daft T>
    where
        Q: ?Sized + Hash + Equivalent<T::K3<'a>>,
    {
        self.common
            .get3(key)
            .and_then(|leaf| leaf.is_unchanged().then_some(*leaf.before()))
    }

    /// Returns an iterator over modified keys and values.
    pub fn modified(&self) -> impl Iterator<Item = IdLeaf<&'daft T>> + '_ {
        self.common
            .iter()
            .filter_map(|leaf| leaf.is_modified().then_some(*leaf))
    }

    /// Returns true if the value corresponding to `key1` is modified.
    pub fn is_modified1<'a, Q>(&'a self, key1: &Q) -> bool
    where
        Q: ?Sized + Hash + Equivalent<T::K1<'a>>,
    {
        self.common.get1(key1).is_some_and(|leaf| leaf.is_modified())
    }

    /// Returns true if the value corresponding to `key2` is modified.
    pub fn is_modified2<'a, Q>(&'a self, key2: &Q) -> bool
    where
        Q: ?Sized + Hash + Equivalent<T::K2<'a>>,
    {
        self.common.get2(key2).is_some_and(|leaf| leaf.is_modified())
    }

    /// Returns true if the value corresponding to `key3` is modified.
    pub fn is_modified3<'a, Q>(&'a self, key3: &Q) -> bool
    where
        Q: ?Sized + Hash + Equivalent<T::K3<'a>>,
    {
        self.common.get3(key3).is_some_and(|leaf| leaf.is_modified())
    }

    /// Returns the [`IdLeaf`] associated with `key1` if it is modified,
    /// otherwise `None`.
    pub fn get_modified1<'a, Q>(&'a self, key: &Q) -> Option<IdLeaf<&'daft T>>
    where
        Q: ?Sized + Hash + Equivalent<T::K1<'a>>,
    {
        self.common
            .get1(key)
            .and_then(|leaf| leaf.is_modified().then_some(*leaf))
    }

    /// Returns the [`IdLeaf`] associated with `key2` if it is modified,
    /// otherwise `None`.
    pub fn get_modified2<'a, Q>(&'a self, key: &Q) -> Option<IdLeaf<&'daft T>>
    where
        Q: ?Sized + Hash + Equivalent<T::K2<'a>>,
    {
        self.common
            .get2(key)
            .and_then(|leaf| leaf.is_modified().then_some(*leaf))
    }

    /// Returns the [`IdLeaf`] associated with `key3` if it is modified,
    /// otherwise `None`.
    pub fn get_modified3<'a, Q>(&'a self, key: &Q) -> Option<IdLeaf<&'daft T>>
    where
        Q: ?Sized + Hash + Equivalent<T::K3<'a>>,
    {
        self.common
            .get3(key)
            .and_then(|leaf| leaf.is_modified().then_some(*leaf))
    }

    /// Returns an iterator over modified keys and values, performing a diff on
    /// the values.
    ///
    /// This is useful when `T::Diff` is a complex type, not just a
    /// [`daft::Leaf`].
    pub fn modified_diff(&self) -> impl Iterator<Item = T::Diff<'daft>> + '_
    where
        T: Diffable,
    {
        self.modified().map(|leaf| leaf.diff_pair())
    }
}

impl<T: TriHashItem> TriHashItem for IdLeaf<T> {
    type K1<'a>
        = T::K1<'a>
    where
        T: 'a;
    type K2<'a>
        = T::K2<'a>
    where
        T: 'a;
    type K3<'a>
        = T::K3<'a>
    where
        T: 'a;

    fn key1(&self) -> Self::K1<'_> {
        let before_key = self.before().key1();
        if before_key != self.after().key1() {
            panic!("key1 is different between before and after");
        }
        before_key
    }

    fn key2(&self) -> Self::K2<'_> {
        let before_key = self.before().key2();
        if before_key != self.after().key2() {
            panic!("key2 is different between before and after");
        }
        before_key
    }

    fn key3(&self) -> Self::K3<'_> {
        let before_key = self.before().key3();
        if before_key != self.after().key3() {
            panic!("key3 is different between before and after");
        }
        before_key
    }

    #[inline]
    fn upcast_key1<'short, 'long: 'short>(
        long: Self::K1<'long>,
    ) -> Self::K1<'short> {
        T::upcast_key1(long)
    }

    #[inline]
    fn upcast_key2<'short, 'long: 'short>(
        long: Self::K2<'long>,
    ) -> Self::K2<'short> {
        T::upcast_key2(long)
    }

    #[inline]
    fn upcast_key3<'short, 'long: 'short>(
        long: Self::K3<'long>,
    ) -> Self::K3<'short> {
        T::upcast_key3(long)
    }
}

/// Maps a [`TriHashItem`] to an [`IdHashItem`], indexed by `key1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, RefCast)]
#[repr(transparent)]
pub struct ByK1<T>(pub T);

impl<T> ByK1<T> {
    /// Converts a `&T` to a `&ByK1<T>`.
    #[inline]
    pub fn ref_cast(item: &T) -> &Self {
        RefCast::ref_cast(item)
    }

    /// Converts a `&mut T` to a `&mut ByK1<T>`.
    #[inline]
    pub fn ref_cast_mut(item: &mut T) -> &mut Self {
        RefCast::ref_cast_mut(item)
    }
}

impl<T: TriHashItem> IdHashItem for ByK1<T> {
    type Key<'a>
        = T::K1<'a>
    where
        T: 'a;

    #[inline]
    fn key(&self) -> Self::Key<'_> {
        self.0.key1()
    }

    #[inline]
    fn upcast_key<'short, 'long: 'short>(
        long: Self::Key<'long>,
    ) -> Self::Key<'short> {
        T::upcast_key1(long)
    }
}

/// Maps a [`TriHashItem`] to an [`IdHashItem`], indexed by `key2`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, RefCast)]
#[repr(transparent)]
pub struct ByK2<T>(pub T);

impl<T> ByK2<T> {
    /// Converts a `&T` to a `&ByK2<T>`.
    #[inline]
    pub fn ref_cast(item: &T) -> &Self {
        RefCast::ref_cast(item)
    }

    /// Converts a `&mut T` to a `&mut ByK2<T>`.
    #[inline]
    pub fn ref_cast_mut(item: &mut T) -> &mut Self {
        RefCast::ref_cast_mut(item)
    }
}

impl<T: TriHashItem> IdHashItem for ByK2<T> {
    type Key<'a>
        = T::K2<'a>
    where
        T: 'a;

    #[inline]
    fn key(&self) -> Self::Key<'_> {
        self.0.key2()
    }

    #[inline]
    fn upcast_key<'short, 'long: 'short>(
        long: Self::Key<'long>,
    ) -> Self::Key<'short> {
        T::upcast_key2(long)
    }
}

/// Maps a [`TriHashItem`] to an [`IdHashItem`], indexed by `key3`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, RefCast)]
#[repr(transparent)]
pub struct ByK3<T>(pub T);

impl<T> ByK3<T> {
    /// Converts a `&T` to a `&ByK3<T>`.
    #[inline]
    pub fn ref_cast(item: &T) -> &Self {
        RefCast::ref_cast(item)
    }

    /// Converts a `&mut T` to a `&mut ByK3<T>`.
    #[inline]
    pub fn ref_cast_mut(item: &mut T) -> &mut Self {
        RefCast::ref_cast_mut(item)
    }
}

impl<T: TriHashItem> IdHashItem for ByK3<T> {
    type Key<'a>
        = T::K3<'a>
    where
        T: 'a;

    #[inline]
    fn key(&self) -> Self::Key<'_> {
        self.0.key3()
    }

    #[inline]
    fn upcast_key<'short, 'long: 'short>(
        long: Self::Key<'long>,
    ) -> Self::Key<'short> {
        T::upcast_key3(long)
    }
}
