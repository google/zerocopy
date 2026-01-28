use super::{IdOrdItem, IdOrdMap};
use core::{fmt, marker::PhantomData};
use serde_core::{
    Deserialize, Deserializer, Serialize, Serializer,
    de::{MapAccess, SeqAccess, Visitor},
    ser::{SerializeMap, SerializeSeq},
};

/// An `IdOrdMap` serializes to the list of items. Items are serialized in
/// order of their keys.
///
/// Serializing as a list of items rather than as a map works around the lack of
/// non-string keys in formats like JSON.
///
/// # Examples
///
/// ```
/// use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
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
/// #[derive(Eq, PartialEq, PartialOrd, Ord)]
/// struct ComplexKey<'a> {
///     id: u32,
///     email: &'a str,
/// }
///
/// impl IdOrdItem for Item {
///     type Key<'a> = ComplexKey<'a>;
///     fn key(&self) -> Self::Key<'_> {
///         ComplexKey { id: self.id, email: &self.email }
///     }
///     id_upcast!();
/// }
///
/// let mut map = IdOrdMap::<Item>::new();
/// map.insert_unique(Item {
///     id: 1,
///     name: "Alice".to_string(),
///     email: "alice@example.com".to_string(),
/// })
/// .unwrap();
///
/// // The map is serialized as a list of items in order of their keys.
/// let serialized = serde_json::to_string(&map).unwrap();
/// assert_eq!(
///     serialized,
///     r#"[{"id":1,"name":"Alice","email":"alice@example.com"}]"#,
/// );
/// ```
impl<T: IdOrdItem> Serialize for IdOrdMap<T>
where
    T: Serialize,
{
    fn serialize<S: Serializer>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for item in self {
            seq.serialize_element(item)?;
        }
        seq.end()
    }
}

/// The `Deserialize` impl deserializes from either a sequence or a map of items,
/// rebuilding the indexes and producing an error if there are any duplicates.
///
/// The `fmt::Debug` bound on `T` ensures better error reporting.
impl<'de, T: IdOrdItem + fmt::Debug> Deserialize<'de> for IdOrdMap<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(SeqVisitor { _marker: PhantomData })
    }
}

struct SeqVisitor<T> {
    _marker: PhantomData<fn() -> T>,
}

impl<'de, T> Visitor<'de> for SeqVisitor<T>
where
    T: IdOrdItem + Deserialize<'de> + fmt::Debug,
{
    type Value = IdOrdMap<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .write_str("a sequence or map of items representing an IdOrdMap")
    }

    fn visit_seq<Access>(
        self,
        mut seq: Access,
    ) -> Result<Self::Value, Access::Error>
    where
        Access: SeqAccess<'de>,
    {
        let mut map = match seq.size_hint() {
            Some(size) => IdOrdMap::with_capacity(size),
            None => IdOrdMap::new(),
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
        let mut map = IdOrdMap::new();

        while let Some((_, value)) =
            map_access.next_entry::<serde_core::de::IgnoredAny, T>()?
        {
            map.insert_unique(value).map_err(serde_core::de::Error::custom)?;
        }

        Ok(map)
    }
}

/// Marker type for [`IdOrdMap`] serialized as a map, for use with serde's
/// `with` attribute.
///
/// # Examples
///
/// Use with serde's `with` attribute:
///
/// ```
/// use iddqd::{IdOrdItem, IdOrdMap, id_ord_map::IdOrdMapAsMap, id_upcast};
/// use serde::{Deserialize, Serialize};
///
/// #[derive(Debug, Serialize, Deserialize)]
/// struct Item {
///     id: u32,
///     name: String,
/// }
///
/// impl IdOrdItem for Item {
///     type Key<'a> = u32;
///     fn key(&self) -> Self::Key<'_> {
///         self.id
///     }
///     id_upcast!();
/// }
///
/// #[derive(Serialize, Deserialize)]
/// struct Config {
///     #[serde(with = "IdOrdMapAsMap")]
///     items: IdOrdMap<Item>,
/// }
/// ```
///
/// # Requirements
///
/// - For serialization, the key type must implement [`Serialize`].
/// - For JSON serialization, the key should be string-like or convertible to a string key.
pub struct IdOrdMapAsMap<T> {
    _marker: PhantomData<fn() -> T>,
}

struct MapVisitorAsMap<T> {
    _marker: PhantomData<fn() -> T>,
}

impl<'de, T> Visitor<'de> for MapVisitorAsMap<T>
where
    T: IdOrdItem + Deserialize<'de> + fmt::Debug,
{
    type Value = IdOrdMap<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a map with items representing an IdOrdMap")
    }

    fn visit_map<Access>(
        self,
        mut map_access: Access,
    ) -> Result<Self::Value, Access::Error>
    where
        Access: MapAccess<'de>,
    {
        let mut map = IdOrdMap::new();

        while let Some((_, value)) =
            map_access.next_entry::<serde_core::de::IgnoredAny, T>()?
        {
            map.insert_unique(value).map_err(serde_core::de::Error::custom)?;
        }

        Ok(map)
    }
}

impl<T> IdOrdMapAsMap<T> {
    /// Serializes an `IdOrdMap` as a JSON object/map using `key()` as keys.
    pub fn serialize<'a, Ser>(
        map: &IdOrdMap<T>,
        serializer: Ser,
    ) -> Result<Ser::Ok, Ser::Error>
    where
        T: 'a + IdOrdItem + Serialize,
        T::Key<'a>: Serialize,
        Ser: Serializer,
    {
        let mut ser_map = serializer.serialize_map(Some(map.len()))?;
        for item in map.iter() {
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
            let key1 = unsafe {
                core::mem::transmute::<T::Key<'_>, T::Key<'a>>(item.key())
            };
            ser_map.serialize_entry(&key1, item)?;
        }
        ser_map.end()
    }

    /// Deserializes an `IdOrdMap` from a JSON object/map.
    pub fn deserialize<'de, D>(deserializer: D) -> Result<IdOrdMap<T>, D::Error>
    where
        T: IdOrdItem + Deserialize<'de> + fmt::Debug,
        D: Deserializer<'de>,
    {
        deserializer.deserialize_map(MapVisitorAsMap { _marker: PhantomData })
    }
}
