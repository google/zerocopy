//! Trait definitions for `BiHashMap`.

use alloc::{boxed::Box, rc::Rc, sync::Arc};
use core::hash::Hash;

/// An item in a [`BiHashMap`].
///
/// This trait is used to define the keys.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "default-hasher")] {
/// use iddqd::{BiHashItem, BiHashMap, bi_upcast};
///
/// // Define a struct with two keys.
/// #[derive(Debug, PartialEq, Eq, Hash)]
/// struct MyPair {
///     id: u32,
///     name: String,
/// }
///
/// // Implement BiHashItem for the struct.
/// impl BiHashItem for MyPair {
///     type K1<'a> = u32;
///     type K2<'a> = &'a str;
///
///     fn key1(&self) -> Self::K1<'_> {
///         self.id
///     }
///
///     fn key2(&self) -> Self::K2<'_> {
///         &self.name
///     }
///
///     bi_upcast!();
/// }
///
/// // Create a BiHashMap and insert items.
/// let mut map = BiHashMap::new();
/// map.insert_unique(MyPair { id: 1, name: "Alice".to_string() }).unwrap();
/// map.insert_unique(MyPair { id: 2, name: "Bob".to_string() }).unwrap();
/// # }
/// ```
///
/// [`BiHashMap`]: crate::BiHashMap
pub trait BiHashItem {
    /// The first key type.
    type K1<'a>: Eq + Hash
    where
        Self: 'a;

    /// The second key type.
    type K2<'a>: Eq + Hash
    where
        Self: 'a;

    /// Retrieves the first key.
    fn key1(&self) -> Self::K1<'_>;

    /// Retrieves the second key.
    fn key2(&self) -> Self::K2<'_>;

    /// Upcasts the first key to a shorter lifetime, in effect asserting that
    /// the lifetime `'a` on [`BiHashItem::K1`] is covariant.
    ///
    /// Typically implemented via the [`bi_upcast`] macro.
    ///
    /// [`bi_upcast`]: crate::bi_upcast
    fn upcast_key1<'short, 'long: 'short>(
        long: Self::K1<'long>,
    ) -> Self::K1<'short>;

    /// Upcasts the second key to a shorter lifetime, in effect asserting that
    /// the lifetime `'a` on [`BiHashItem::K2`] is covariant.
    ///
    /// Typically implemented via the [`bi_upcast`] macro.
    ///
    /// [`bi_upcast`]: crate::bi_upcast
    fn upcast_key2<'short, 'long: 'short>(
        long: Self::K2<'long>,
    ) -> Self::K2<'short>;
}

macro_rules! impl_for_ref {
    ($type:ty) => {
        impl<'b, T: 'b + ?Sized + BiHashItem> BiHashItem for $type {
            type K1<'a>
                = T::K1<'a>
            where
                Self: 'a;
            type K2<'a>
                = T::K2<'a>
            where
                Self: 'a;

            fn key1(&self) -> Self::K1<'_> {
                (**self).key1()
            }

            fn key2(&self) -> Self::K2<'_> {
                (**self).key2()
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
        }
    };
}

impl_for_ref!(&'b T);
impl_for_ref!(&'b mut T);

macro_rules! impl_for_box {
    ($type:ty) => {
        impl<T: ?Sized + BiHashItem> BiHashItem for $type {
            type K1<'a>
                = T::K1<'a>
            where
                Self: 'a;

            type K2<'a>
                = T::K2<'a>
            where
                Self: 'a;

            fn key1(&self) -> Self::K1<'_> {
                (**self).key1()
            }

            fn key2(&self) -> Self::K2<'_> {
                (**self).key2()
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
        }
    };
}

impl_for_box!(Box<T>);
impl_for_box!(Rc<T>);
impl_for_box!(Arc<T>);
