//! Trait definitions for `TriHashMap`.

use alloc::{boxed::Box, rc::Rc, sync::Arc};
use core::hash::Hash;

/// An item in a [`TriHashMap`].
///
/// This trait is used to define the keys.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{TriHashItem, TriHashMap, tri_upcast};
///
/// // Define a struct with three keys.
/// #[derive(Debug, PartialEq, Eq, Hash)]
/// struct Person {
///     id: u32,
///     name: String,
///     email: String,
/// }
///
/// // Implement TriHashItem for the struct.
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
/// // Create a TriHashMap and insert items.
/// let mut map = TriHashMap::new();
/// map.insert_unique(Person {
///     id: 1,
///     name: "Alice".to_string(),
///     email: "alice@example.com".to_string(),
/// })
/// .unwrap();
/// map.insert_unique(Person {
///     id: 2,
///     name: "Bob".to_string(),
///     email: "bob@example.com".to_string(),
/// })
/// .unwrap();
/// # }
/// ```
///
/// [`TriHashMap`]: crate::TriHashMap
pub trait TriHashItem {
    /// The first key type.
    type K1<'a>: Eq + Hash
    where
        Self: 'a;

    /// The second key type.
    type K2<'a>: Eq + Hash
    where
        Self: 'a;

    /// The third key type.
    type K3<'a>: Eq + Hash
    where
        Self: 'a;

    /// Retrieves the first key.
    fn key1(&self) -> Self::K1<'_>;

    /// Retrieves the second key.
    fn key2(&self) -> Self::K2<'_>;

    /// Retrieves the third key.
    fn key3(&self) -> Self::K3<'_>;

    /// Upcasts the first key to a shorter lifetime, in effect asserting that
    /// the lifetime `'a` on [`TriHashItem::K1`] is covariant.
    ///
    /// Typically implemented via the [`tri_upcast`] macro.
    ///
    /// [`tri_upcast`]: crate::tri_upcast
    fn upcast_key1<'short, 'long: 'short>(
        long: Self::K1<'long>,
    ) -> Self::K1<'short>;

    /// Upcasts the second key to a shorter lifetime, in effect asserting that
    /// the lifetime `'a` on [`TriHashItem::K2`] is covariant.
    ///
    /// Typically implemented via the [`tri_upcast`] macro.
    ///
    /// [`tri_upcast`]: crate::tri_upcast
    fn upcast_key2<'short, 'long: 'short>(
        long: Self::K2<'long>,
    ) -> Self::K2<'short>;

    /// Upcasts the third key to a shorter lifetime, in effect asserting that
    /// the lifetime `'a` on [`TriHashItem::K3`] is covariant.
    ///
    /// Typically implemented via the [`tri_upcast`] macro.
    ///
    /// [`tri_upcast`]: crate::tri_upcast
    fn upcast_key3<'short, 'long: 'short>(
        long: Self::K3<'long>,
    ) -> Self::K3<'short>;
}

macro_rules! impl_for_ref {
    ($type:ty) => {
        impl<'b, T: 'b + ?Sized + TriHashItem> TriHashItem for $type {
            type K1<'a>
                = T::K1<'a>
            where
                Self: 'a;
            type K2<'a>
                = T::K2<'a>
            where
                Self: 'a;
            type K3<'a>
                = T::K3<'a>
            where
                Self: 'a;

            fn key1(&self) -> Self::K1<'_> {
                (**self).key1()
            }

            fn key2(&self) -> Self::K2<'_> {
                (**self).key2()
            }

            fn key3(&self) -> Self::K3<'_> {
                (**self).key3()
            }

            fn upcast_key1<'short, 'long: 'short>(
                long: Self::K1<'long>,
            ) -> Self::K1<'short>
            where
                Self: 'long,
            {
                T::upcast_key1(long)
            }

            fn upcast_key2<'short, 'long: 'short>(
                long: Self::K2<'long>,
            ) -> Self::K2<'short>
            where
                Self: 'long,
            {
                T::upcast_key2(long)
            }

            fn upcast_key3<'short, 'long: 'short>(
                long: Self::K3<'long>,
            ) -> Self::K3<'short>
            where
                Self: 'long,
            {
                T::upcast_key3(long)
            }
        }
    };
}

impl_for_ref!(&'b T);
impl_for_ref!(&'b mut T);

macro_rules! impl_for_box {
    ($type:ty) => {
        impl<T: ?Sized + TriHashItem> TriHashItem for $type {
            type K1<'a>
                = T::K1<'a>
            where
                Self: 'a;

            type K2<'a>
                = T::K2<'a>
            where
                Self: 'a;

            type K3<'a>
                = T::K3<'a>
            where
                Self: 'a;

            fn key1(&self) -> Self::K1<'_> {
                (**self).key1()
            }

            fn key2(&self) -> Self::K2<'_> {
                (**self).key2()
            }

            fn key3(&self) -> Self::K3<'_> {
                (**self).key3()
            }

            fn upcast_key1<'short, 'long: 'short>(
                long: Self::K1<'long>,
            ) -> Self::K1<'short> {
                T::upcast_key1(long)
            }

            fn upcast_key2<'short, 'long: 'short>(
                long: Self::K2<'long>,
            ) -> Self::K2<'short> {
                T::upcast_key2(long)
            }

            fn upcast_key3<'short, 'long: 'short>(
                long: Self::K3<'long>,
            ) -> Self::K3<'short> {
                T::upcast_key3(long)
            }
        }
    };
}

impl_for_box!(Box<T>);
impl_for_box!(Rc<T>);
impl_for_box!(Arc<T>);
