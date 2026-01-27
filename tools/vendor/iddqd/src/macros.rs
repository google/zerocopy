//! Macros for this crate.

/// Creates an [`IdHashMap`](crate::IdHashMap) from a list of items.
///
/// An optional [`BuildHasher`](core::hash::BuildHasher) that implements
/// `Default` can be provided as the first argument, followed by a semicolon.
///
/// # Panics
///
/// Panics if the list of items has duplicate keys. For better error handling,
/// the item is required to implement `Debug`.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{IdHashItem, id_hash_map, id_upcast};
///
/// #[derive(Debug)]
/// struct User {
///     id: u32,
///     name: String,
/// }
///
/// impl IdHashItem for User {
///     type Key<'a> = u32;
///     fn key(&self) -> Self::Key<'_> {
///         self.id
///     }
///     id_upcast!();
/// }
///
/// let map = id_hash_map! {
///     User { id: 1, name: "Alice".to_string() },
///     User { id: 2, name: "Bob".to_string() },
/// };
/// assert_eq!(map.get(&1).unwrap().name, "Alice");
/// assert_eq!(map.get(&2).unwrap().name, "Bob");
///
/// // With a custom hasher:
/// let map = id_hash_map! {
///     foldhash::quality::RandomState;
///     User { id: 3, name: "Charlie".to_string() },
///     User { id: 4, name: "Eve".to_string() },
/// };
/// assert_eq!(map.get(&3).unwrap().name, "Charlie");
/// assert_eq!(map.get(&4).unwrap().name, "Eve");
/// # }
/// ```
#[macro_export]
macro_rules! id_hash_map {
    ($($item:expr,)+) => { $crate::id_hash_map!($($item),+) };
    ($($item:expr),*) => {
        {
            // Note: `stringify!($key)` is just here to consume the repetition,
            // but we throw away that string literal during constant evaluation.
            const CAP: usize = <[()]>::len(&[$({ stringify!($item); }),*]);
            let mut map = $crate::IdHashMap::with_capacity(CAP);
            $(
                map.insert_unique($item).unwrap();
            )*
            map
        }
    };
    ($H:ty; $($item:expr,)+) => { $crate::id_hash_map!($H; $($item),+) };
    ($H:ty; $($item:expr),*) => {
        {
            // Note: `stringify!($key)` is just here to consume the repetition,
            // but we throw away that string literal during constant evaluation.
            const CAP: usize = <[()]>::len(&[$({ stringify!($item); }),*]);
            let mut map = $crate::IdHashMap::with_capacity_and_hasher(CAP, <$H>::default());
            $(
                map.insert_unique($item).unwrap();
            )*
            map
        }
    };
}

/// Creates an [`IdOrdMap`](crate::IdOrdMap) from a list of items.
///
/// # Panics
///
/// Panics if the list of items has duplicate keys. For better error handling,
/// the item is required to implement `Debug`.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "std")] {
/// use iddqd::{IdOrdItem, id_ord_map, id_upcast};
///
/// #[derive(Debug)]
/// struct User {
///     id: u32,
///     name: String,
/// }
///
/// impl IdOrdItem for User {
///     type Key<'a> = u32;
///     fn key(&self) -> Self::Key<'_> {
///         self.id
///     }
///     id_upcast!();
/// }
///
/// let map = id_ord_map! {
///     User { id: 1, name: "Alice".to_string() },
///     User { id: 2, name: "Bob".to_string() },
/// };
/// assert_eq!(map.get(&1).unwrap().name, "Alice");
/// assert_eq!(map.get(&2).unwrap().name, "Bob");
/// # }
/// ```
#[cfg(feature = "std")]
#[macro_export]
macro_rules! id_ord_map {
    ($($item:expr,)+) => { $crate::id_ord_map!($($item),+) };
    ($($item:expr),*) => {
        {
            // Note: `stringify!($key)` is just here to consume the repetition,
            // but we throw away that string literal during constant evaluation.
            const CAP: usize = <[()]>::len(&[$({ stringify!($item); }),*]);
            let mut map = $crate::IdOrdMap::with_capacity(CAP);
            $(
                map.insert_unique($item).unwrap();
            )*
            map
        }
    };
}

/// Creates a [`BiHashMap`](crate::BiHashMap) from a list of items.
///
/// An optional [`BuildHasher`](core::hash::BuildHasher) that implements
/// `Default` can be provided as the first argument, followed by a semicolon.
///
/// # Panics
///
/// Panics if the list of items has duplicate keys. For better error handling,
/// the item is required to implement `Debug`.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{BiHashItem, bi_hash_map, bi_upcast};
///
/// #[derive(Debug)]
/// struct User {
///     id: u32,
///     name: String,
/// }
///
/// impl BiHashItem for User {
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
/// let map = bi_hash_map! {
///     User { id: 1, name: "Alice".to_string() },
///     User { id: 2, name: "Bob".to_string() },
/// };
/// assert_eq!(map.get1(&1).unwrap().name, "Alice");
/// assert_eq!(map.get2("Bob").unwrap().id, 2);
///
/// // With a custom hasher:
/// let map = bi_hash_map! {
///     foldhash::quality::RandomState;
///     User { id: 3, name: "Charlie".to_string() },
///     User { id: 4, name: "Eve".to_string() },
/// };
/// assert_eq!(map.get1(&3).unwrap().name, "Charlie");
/// assert_eq!(map.get2("Eve").unwrap().id, 4);
/// # }
/// ```
#[macro_export]
macro_rules! bi_hash_map {
    ($($item:expr,)+) => { $crate::bi_hash_map!($($item),+) };
    ($($item:expr),*) => {
        {
            // Note: `stringify!($key)` is just here to consume the repetition,
            // but we throw away that string literal during constant evaluation.
            const CAP: usize = <[()]>::len(&[$({ stringify!($item); }),*]);
            let mut map = $crate::BiHashMap::with_capacity(CAP);
            $(
                map.insert_unique($item).unwrap();
            )*
            map
        }
    };
    ($H:ty; $($item:expr,)+) => { $crate::bi_hash_map!($H; $($item),+) };
    ($H:ty; $($item:expr),*) => {
        {
            // Note: `stringify!($key)` is just here to consume the repetition,
            // but we throw away that string literal during constant evaluation.
            const CAP: usize = <[()]>::len(&[$({ stringify!($item); }),*]);
            let mut map = $crate::BiHashMap::with_capacity_and_hasher(CAP, <$H>::default());
            $(
                map.insert_unique($item).unwrap();
            )*
            map
        }
    };
}

/// Creates a [`TriHashMap`](crate::TriHashMap) from a list of items.
///
/// An optional [`BuildHasher`](core::hash::BuildHasher) that implements
/// `Default` can be provided as the first argument, followed by a semicolon.
///
/// # Panics
///
/// Panics if the list of items has duplicate keys. For better error handling,
/// the item is required to implement `Debug`.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{TriHashItem, tri_hash_map, tri_upcast};
///
/// #[derive(Debug)]
/// struct Person {
///     id: u32,
///     name: String,
///     email: String,
/// }
///
/// impl TriHashItem for Person {
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
/// let map = tri_hash_map! {
///     Person { id: 1, name: "Alice".to_string(), email: "alice@example.com".to_string() },
///     Person { id: 2, name: "Bob".to_string(), email: "bob@example.com".to_string() },
/// };
/// assert_eq!(map.get1(&1).unwrap().name, "Alice");
/// assert_eq!(map.get2("Bob").unwrap().id, 2);
/// assert_eq!(map.get3("alice@example.com").unwrap().name, "Alice");
///
/// // With a custom hasher:
/// let map = tri_hash_map! {
///     foldhash::quality::RandomState;
///     Person { id: 3, name: "Charlie".to_string(), email: "charlie@example.com".to_string() },
///     Person { id: 4, name: "Eve".to_string(), email: "eve@example.com".to_string() },
/// };
/// assert_eq!(map.get1(&3).unwrap().name, "Charlie");
/// assert_eq!(map.get2("Eve").unwrap().id, 4);
/// # }
/// ```
#[macro_export]
macro_rules! tri_hash_map {
    ($($item:expr,)+) => { $crate::tri_hash_map!($($item),+) };
    ($($item:expr),*) => {
        {
            // Note: `stringify!($key)` is just here to consume the repetition,
            // but we throw away that string literal during constant evaluation.
            const CAP: usize = <[()]>::len(&[$({ stringify!($item); }),*]);
            let mut map = $crate::TriHashMap::with_capacity(CAP);
            $(
                map.insert_unique($item).unwrap();
            )*
            map
        }
    };
    ($H:ty; $($item:expr,)+) => { $crate::tri_hash_map!($H; $($item),+) };
    ($H:ty; $($item:expr),*) => {
        {
            // Note: `stringify!($key)` is just here to consume the repetition,
            // but we throw away that string literal during constant evaluation.
            const CAP: usize = <[()]>::len(&[$({ stringify!($item); }),*]);
            let mut map = $crate::TriHashMap::with_capacity_and_hasher(CAP, <$H>::default());
            $(
                map.insert_unique($item).unwrap();
            )*
            map
        }
    };
}

/// Implement upcasts for [`IdOrdMap`] or [`IdHashMap`].
///
/// The maps in this crate require that the key types' lifetimes are covariant.
/// This macro assists with implementing this requirement.
///
/// The macro is optional, and these implementations can be written by hand as
/// well.
///
/// [`IdOrdMap`]: crate::IdOrdMap
/// [`IdHashMap`]: crate::IdHashMap
#[macro_export]
macro_rules! id_upcast {
    () => {
        #[inline]
        fn upcast_key<'short, 'long: 'short>(
            long: Self::Key<'long>,
        ) -> Self::Key<'short>
        where
            Self: 'long,
        {
            long
        }
    };
}

/// Implement upcasts for [`BiHashMap`].
///
/// The maps in this crate require that the key types' lifetimes are covariant.
/// This macro assists with implementing this requirement.
///
/// The macro is optional, and these implementations can be written by hand as
/// well.
///
/// [`BiHashMap`]: crate::BiHashMap
#[macro_export]
macro_rules! bi_upcast {
    () => {
        #[inline]
        fn upcast_key1<'short, 'long: 'short>(
            long: Self::K1<'long>,
        ) -> Self::K1<'short>
        where
            Self: 'long,
        {
            long
        }

        #[inline]
        fn upcast_key2<'short, 'long: 'short>(
            long: Self::K2<'long>,
        ) -> Self::K2<'short>
        where
            Self: 'long,
        {
            long
        }
    };
}

/// Implement upcasts for [`TriHashMap`].
///
/// The maps in this crate require that the key types' lifetimes are covariant.
/// This macro assists with implementing this requirement.
///
/// The macro is optional, and these implementations can be written by hand as
/// well.
///
/// [`TriHashMap`]: crate::TriHashMap
#[macro_export]
macro_rules! tri_upcast {
    () => {
        #[inline]
        fn upcast_key1<'short, 'long: 'short>(
            long: Self::K1<'long>,
        ) -> Self::K1<'short>
        where
            Self: 'long,
        {
            long
        }

        #[inline]
        fn upcast_key2<'short, 'long: 'short>(
            long: Self::K2<'long>,
        ) -> Self::K2<'short>
        where
            Self: 'long,
        {
            long
        }

        #[inline]
        fn upcast_key3<'short, 'long: 'short>(
            long: Self::K3<'long>,
        ) -> Self::K3<'short>
        where
            Self: 'long,
        {
            long
        }
    };
}

// Internal macro to implement diffs.
#[cfg(feature = "daft")]
macro_rules! impl_diff_ref_cast {
    ($self: ident, $diff_ty: ty, $key_method: ident, $get_method: ident, $contains_method: ident, $ref_cast_ty: ty) => {{
        let hasher = $self.before.hasher().clone();
        let alloc = $self.before.allocator().clone();
        let mut diff = <$diff_ty>::with_hasher_in(hasher, alloc);
        for before_item in $self.before {
            if let Some(after_item) =
                $self.after.$get_method(&before_item.$key_method())
            {
                diff.common.insert_overwrite(IdLeaf::new(
                    <$ref_cast_ty>::ref_cast(before_item),
                    <$ref_cast_ty>::ref_cast(after_item),
                ));
            } else {
                diff.removed
                    .insert_overwrite(<$ref_cast_ty>::ref_cast(before_item));
            }
        }
        for after_item in $self.after {
            if !$self.before.$contains_method(&after_item.$key_method()) {
                diff.added
                    .insert_overwrite(<$ref_cast_ty>::ref_cast(after_item));
            }
        }
        diff
    }};
}
