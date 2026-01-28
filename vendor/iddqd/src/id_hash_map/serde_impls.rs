use crate::{
    DefaultHashBuilder, IdHashItem, IdHashMap,
    support::alloc::{Allocator, Global},
};
use core::{fmt, hash::BuildHasher, marker::PhantomData};
use serde_core::{
    Deserialize, Deserializer, Serialize, Serializer,
    de::{MapAccess, SeqAccess, Visitor},
    ser::SerializeMap,
};

/// An `IdHashMap` serializes to the list of items. Items are serialized in
/// arbitrary order.
///
/// Serializing as a list of items rather than as a map works around the lack of
/// non-string keys in formats like JSON.
///
/// To serialize as a map instead, see [`IdHashMapAsMap`].
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{IdHashItem, IdHashMap, id_upcast};
/// # use iddqd_test_utils::serde_json;
/// use serde::{Deserialize, Serialize};
///
/// #[derive(Debug, Serialize)]
/// struct Item {
///     id: u32,
///     name: String,
///     email: String,
/// }
///
/// // This is a complex key, so it can't be a JSON map key.
/// #[derive(Eq, Hash, PartialEq)]
/// struct ComplexKey<'a> {
///     id: u32,
///     email: &'a str,
/// }
///
/// impl IdHashItem for Item {
///     type Key<'a> = ComplexKey<'a>;
///     fn key(&self) -> Self::Key<'_> {
///         ComplexKey { id: self.id, email: &self.email }
///     }
///     id_upcast!();
/// }
///
/// let mut map = IdHashMap::<Item>::new();
/// map.insert_unique(Item {
///     id: 1,
///     name: "Alice".to_string(),
///     email: "alice@example.com".to_string(),
/// })
/// .unwrap();
///
/// // The map is serialized as a list of items.
/// let serialized = serde_json::to_string(&map).unwrap();
/// assert_eq!(
///     serialized,
///     r#"[{"id":1,"name":"Alice","email":"alice@example.com"}]"#,
/// );
/// # }
/// ```
impl<T: IdHashItem, S: Clone + BuildHasher, A: Allocator> Serialize
    for IdHashMap<T, S, A>
where
    T: Serialize,
{
    fn serialize<Ser: Serializer>(
        &self,
        serializer: Ser,
    ) -> Result<Ser::Ok, Ser::Error> {
        // Serialize just the items -- don't serialize the indexes. We'll
        // rebuild the indexes on deserialization.
        self.items.serialize(serializer)
    }
}

/// The `Deserialize` impl for `IdHashMap` deserializes from either a sequence
/// or a map of items, then rebuilds the indexes and produces an error if there
/// are any duplicates.
///
/// In case a map is deserialized, the key is not deserialized or verified
/// against the value. (In general, verification is not possible because the key
/// type has a lifetime parameter embedded in it.)
///
/// The `fmt::Debug` bound on `T` ensures better error reporting.
impl<
    'de,
    T: IdHashItem + fmt::Debug,
    S: Clone + BuildHasher + Default,
    A: Default + Clone + Allocator,
> Deserialize<'de> for IdHashMap<T, S, A>
where
    T: Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Self, D::Error> {
        deserializer.deserialize_any(SeqVisitor {
            _marker: PhantomData,
            hasher: S::default(),
            alloc: A::default(),
        })
    }
}

impl<
    'de,
    T: IdHashItem + fmt::Debug + Deserialize<'de>,
    S: Clone + BuildHasher,
    A: Clone + Allocator,
> IdHashMap<T, S, A>
{
    /// Deserializes from a list of items, allocating new storage within the
    /// provided allocator.
    pub fn deserialize_in<D: Deserializer<'de>>(
        deserializer: D,
        alloc: A,
    ) -> Result<Self, D::Error>
    where
        S: Default,
    {
        deserializer.deserialize_any(SeqVisitor {
            _marker: PhantomData,
            hasher: S::default(),
            alloc,
        })
    }

    /// Deserializes from a list of items, with the given hasher, using the
    /// default allocator.
    pub fn deserialize_with_hasher<D: Deserializer<'de>>(
        deserializer: D,
        hasher: S,
    ) -> Result<Self, D::Error>
    where
        A: Default,
    {
        deserializer.deserialize_any(SeqVisitor {
            _marker: PhantomData,
            hasher,
            alloc: A::default(),
        })
    }

    /// Deserializes from a list of items, with the given hasher, and allocating
    /// new storage within the provided allocator.
    pub fn deserialize_with_hasher_in<D: Deserializer<'de>>(
        deserializer: D,
        hasher: S,
        alloc: A,
    ) -> Result<Self, D::Error> {
        // First, deserialize the items.
        deserializer.deserialize_any(SeqVisitor {
            _marker: PhantomData,
            hasher,
            alloc,
        })
    }
}

struct SeqVisitor<T, S, A> {
    _marker: PhantomData<fn() -> T>,
    hasher: S,
    alloc: A,
}

impl<'de, T, S, A> Visitor<'de> for SeqVisitor<T, S, A>
where
    T: IdHashItem + Deserialize<'de> + fmt::Debug,
    S: Clone + BuildHasher,
    A: Clone + Allocator,
{
    type Value = IdHashMap<T, S, A>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .write_str("a sequence or map of items representing an IdHashMap")
    }

    fn visit_seq<Access>(
        self,
        mut seq: Access,
    ) -> Result<Self::Value, Access::Error>
    where
        Access: SeqAccess<'de>,
    {
        let mut map = match seq.size_hint() {
            Some(size) => IdHashMap::with_capacity_and_hasher_in(
                size,
                self.hasher,
                self.alloc,
            ),
            None => IdHashMap::with_hasher_in(self.hasher, self.alloc),
        };

        while let Some(element) = seq.next_element()? {
            map.insert_unique(element)
                .map_err(serde_core::de::Error::custom)?;
        }

        Ok(map)
    }

    fn visit_map<Access>(
        self,
        mut map_access: Access,
    ) -> Result<Self::Value, Access::Error>
    where
        Access: MapAccess<'de>,
    {
        let mut map = match map_access.size_hint() {
            Some(size) => IdHashMap::with_capacity_and_hasher_in(
                size,
                self.hasher,
                self.alloc,
            ),
            None => IdHashMap::with_hasher_in(self.hasher, self.alloc),
        };

        while let Some((_, value)) =
            map_access.next_entry::<serde_core::de::IgnoredAny, T>()?
        {
            map.insert_unique(value).map_err(serde_core::de::Error::custom)?;
        }

        Ok(map)
    }
}

/// Marker type for [`IdHashMap`] serialized as a map, for use with serde's
/// `with` attribute.
///
/// # Examples
///
/// Use with serde's `with` attribute:
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{
///     IdHashItem, IdHashMap, id_hash_map::IdHashMapAsMap, id_upcast,
/// };
/// use serde::{Deserialize, Serialize};
///
/// #[derive(Debug, Serialize, Deserialize)]
/// struct Item {
///     id: u32,
///     name: String,
/// }
///
/// impl IdHashItem for Item {
///     type Key<'a> = u32;
///     fn key(&self) -> Self::Key<'_> {
///         self.id
///     }
///     id_upcast!();
/// }
///
/// #[derive(Serialize, Deserialize)]
/// struct Config {
///     #[serde(with = "IdHashMapAsMap")]
///     items: IdHashMap<Item>,
/// }
/// # }
/// ```
///
/// # Requirements
///
/// - For serialization, the key type must implement [`Serialize`].
/// - For JSON serialization, the key should be string-like or convertible to a string key.
pub struct IdHashMapAsMap<T, S = DefaultHashBuilder, A: Allocator = Global> {
    #[expect(clippy::type_complexity)]
    _marker: PhantomData<fn() -> (T, S, A)>,
}

struct MapVisitorAsMap<T, S, A> {
    _marker: PhantomData<fn() -> T>,
    hasher: S,
    alloc: A,
}

impl<'de, T, S, A> Visitor<'de> for MapVisitorAsMap<T, S, A>
where
    T: IdHashItem + Deserialize<'de> + fmt::Debug,
    S: Clone + BuildHasher,
    A: Clone + Allocator,
{
    type Value = IdHashMap<T, S, A>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a map with items representing an IdHashMap")
    }

    fn visit_map<Access>(
        self,
        mut map_access: Access,
    ) -> Result<Self::Value, Access::Error>
    where
        Access: MapAccess<'de>,
    {
        let mut map = match map_access.size_hint() {
            Some(size) => IdHashMap::with_capacity_and_hasher_in(
                size,
                self.hasher,
                self.alloc,
            ),
            None => IdHashMap::with_hasher_in(self.hasher, self.alloc),
        };

        while let Some((_, value)) =
            map_access.next_entry::<serde_core::de::IgnoredAny, T>()?
        {
            map.insert_unique(value).map_err(serde_core::de::Error::custom)?;
        }

        Ok(map)
    }
}

impl<T, S, A> IdHashMapAsMap<T, S, A>
where
    S: Clone + BuildHasher,
    A: Allocator,
{
    /// Serializes an `IdHashMap` as a JSON object/map using `key()` as keys.
    pub fn serialize<'a, Ser>(
        map: &IdHashMap<T, S, A>,
        serializer: Ser,
    ) -> Result<Ser::Ok, Ser::Error>
    where
        T: 'a + IdHashItem + Serialize,
        T::Key<'a>: Serialize,
        Ser: Serializer,
    {
        let mut ser_map = serializer.serialize_map(Some(map.len()))?;
        for item in map.iter() {
            let key = item.key();
            // SAFETY:
            //
            // * Lifetime extension: for a type T and two lifetime params 'a and
            //   'b, T<'a> and T<'b> aren't guaranteed to have the same layout,
            //   but (a) that is true today and (b) it would be shocking and
            //   break half the Rust ecosystem if that were to change in the
            //   future.
            // * We only use key within the scope of this block before
            //   immediately dropping it. In particular, ser_map.serialize_entry
            //   serializes the key without holding a reference to it.
            let key1 =
                unsafe { core::mem::transmute::<T::Key<'_>, T::Key<'a>>(key) };
            ser_map.serialize_entry(&key1, item)?;
        }
        ser_map.end()
    }

    /// Deserializes an `IdHashMap` from a JSON object/map.
    pub fn deserialize<'de, D>(
        deserializer: D,
    ) -> Result<IdHashMap<T, S, A>, D::Error>
    where
        T: IdHashItem + Deserialize<'de> + fmt::Debug,
        S: Default,
        A: Clone + Default,
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(MapVisitorAsMap {
            _marker: PhantomData,
            hasher: S::default(),
            alloc: A::default(),
        })
    }
}
