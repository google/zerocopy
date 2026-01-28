//! A newtype wrapper around [`Uuid`].
//!
//! # Motivation
//!
//! Many large systems use UUIDs as unique identifiers for various entities. However, the [`Uuid`]
//! type does not carry information about the kind of entity it identifies, which can lead to mixing
//! up different types of UUIDs at runtime.
//!
//! This crate provides a wrapper type around [`Uuid`] that allows you to specify the kind of entity
//! the UUID identifies.
//!
//! # Example
//!
//! ```
//! use newtype_uuid::{GenericUuid, TypedUuid, TypedUuidKind, TypedUuidTag};
//!
//! // First, define a type that represents the kind of UUID this is.
//! enum MyKind {}
//!
//! impl TypedUuidKind for MyKind {
//!     fn tag() -> TypedUuidTag {
//!         // Tags are required to be ASCII identifiers, with underscores
//!         // and dashes also supported. The validity of a tag can be checked
//!         // at compile time by assigning it to a const, like so:
//!         const TAG: TypedUuidTag = TypedUuidTag::new("my_kind");
//!         TAG
//!     }
//! }
//!
//! // Now, a UUID can be created with this kind.
//! let uuid: TypedUuid<MyKind> = "dffc3068-1cd6-47d5-b2f3-636b41b07084".parse().unwrap();
//!
//! // The Display (and therefore ToString) impls still show the same value.
//! assert_eq!(uuid.to_string(), "dffc3068-1cd6-47d5-b2f3-636b41b07084");
//!
//! // The Debug impl will show the tag as well.
//! assert_eq!(
//!     format!("{:?}", uuid),
//!     "dffc3068-1cd6-47d5-b2f3-636b41b07084 (my_kind)"
//! );
//! ```
//!
//! If you have a large number of UUID kinds, consider using
//! [`newtype-uuid-macros`] which comes with several convenience features.
//!
//! ```
//! use newtype_uuid_macros::impl_typed_uuid_kinds;
//!
//! // Invoke this macro with:
//! impl_typed_uuid_kinds! {
//!     kinds = {
//!         User = {},
//!         Project = {},
//!         // ...
//!     },
//! }
//! ```
//!
//! See [`newtype-uuid-macros`] for more information.
//!
//! [`newtype-uuid-macros`]: https://docs.rs/newtype-uuid-macros
//!
//! For simpler cases, you can also write your own declarative macro. Use this
//! template to get started:
//!
//! ```rust
//! # use newtype_uuid::{TypedUuidKind, TypedUuidTag};
//! macro_rules! impl_kinds {
//!     ($($kind:ident => $tag:literal),* $(,)?) => {
//!         $(
//!             pub enum $kind {}
//!
//!             impl TypedUuidKind for $kind {
//!                 #[inline]
//!                 fn tag() -> TypedUuidTag {
//!                     const TAG: TypedUuidTag = TypedUuidTag::new($tag);
//!                     TAG
//!                 }
//!             }
//!         )*
//!     };
//! }
//!
//! // Invoke this macro with:
//! impl_kinds! {
//!     UserKind => "user",
//!     ProjectKind => "project",
//! }
//! ```
//!
//! # Implementations
//!
//! In general, [`TypedUuid`] uses the same wire and serialization formats as [`Uuid`]. This means
//! that persistent representations of [`TypedUuid`] are the same as [`Uuid`]; [`TypedUuid`] is
//! intended to be helpful within Rust code, not across serialization boundaries.
//!
//! - The `Display` and `FromStr` impls are forwarded to the underlying [`Uuid`].
//! - If the `serde` feature is enabled, `TypedUuid` will serialize and deserialize using the same
//!   format as [`Uuid`].
//! - If the `schemars08` feature is enabled, [`TypedUuid`] will implement `JsonSchema` if the
//!   corresponding [`TypedUuidKind`] implements `JsonSchema`.
//!
//! To abstract over typed and untyped UUIDs, the [`GenericUuid`] trait is provided. This trait also
//! permits conversions between typed and untyped UUIDs.
//!
//! # Dependencies
//!
//! - The only required dependency is the [`uuid`] crate. Optional features may add further
//!   dependencies.
//!
//! # Features
//!
//! - `default`: Enables default features in the newtype-uuid crate.
//! - `std`: Enables the use of the standard library. *Enabled by default.*
//! - `serde`: Enables serialization and deserialization support via Serde. *Not enabled by
//!   default.*
//! - `v4`: Enables the `new_v4` method for generating UUIDs. *Not enabled by default.*
//! - `schemars08`: Enables support for generating JSON schemas via schemars 0.8. *Not enabled by
//!   default.* Note that the format of the generated schema is **not currently part** of the stable
//!   API, though we hope to stabilize it in the future.
//! - `proptest1`: Enables support for generating `proptest::Arbitrary` instances of UUIDs. *Not enabled by default.*
//!
//! # Minimum supported Rust version (MSRV)
//!
//! The MSRV of this crate is **Rust 1.79.** In general, this crate will follow the MSRV of the
//! underlying `uuid` crate or of dependencies, with an aim to be conservative.
//!
//! Within the 1.x series, MSRV updates will be accompanied by a minor version bump. The MSRVs for
//! each minor version are:
//!
//! * Version **1.0.x**: Rust 1.60.
//! * Version **1.1.x**: Rust 1.61. This permits `TypedUuid<T>` to have `const fn` methods.
//! * Version **1.2.x**: Rust 1.67, required by some dependency updates.
//! * Version **1.3.x**: Rust 1.79, required by some dependency updates.
//!
//! # Alternatives
//!
//! - [`typed-uuid`](https://crates.io/crates/typed-uuid): generally similar, but with a few design
//!   decisions that are different.

#![forbid(unsafe_code)]
#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(doc_cfg, feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;

/// Macro support for [`newtype-uuid-macros`].
///
/// This module re-exports types needed for [`newtype-uuid-macros`] to work.
///
/// [`newtype-uuid-macros`]: https://docs.rs/newtype-uuid-macros
#[doc(hidden)]
pub mod macro_support {
    #[cfg(feature = "schemars08")]
    pub use schemars as schemars08;
    #[cfg(feature = "schemars08")]
    pub use serde_json;
}

use core::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    str::FromStr,
};
#[cfg(feature = "v7")]
pub use uuid::Timestamp;
use uuid::{Uuid, Version};

/// A UUID with type-level information about what it's used for.
///
/// For more, see [the library documentation](crate).
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent, bound = ""))]
pub struct TypedUuid<T: TypedUuidKind> {
    uuid: Uuid,
    _phantom: PhantomData<T>,
}

impl<T: TypedUuidKind> TypedUuid<T> {
    /// The 'nil UUID' (all zeros).
    ///
    /// The nil UUID is a special form of UUID that is specified to have all
    /// 128 bits set to zero.
    ///
    /// # References
    ///
    /// * [Nil UUID in RFC4122](https://tools.ietf.org/html/rfc4122.html#section-4.1.7)
    #[inline]
    #[must_use]
    pub const fn nil() -> Self {
        Self {
            uuid: Uuid::nil(),
            _phantom: PhantomData,
        }
    }

    /// The 'max UUID' (all ones).
    ///
    /// The max UUID is a special form of UUID that is specified to have all
    /// 128 bits set to one.
    ///
    /// # References
    ///
    /// * [Max UUID in Draft RFC: New UUID Formats, Version 4](https://datatracker.ietf.org/doc/html/draft-peabody-dispatch-new-uuid-format-04#section-5.4)
    #[inline]
    #[must_use]
    pub const fn max() -> Self {
        Self {
            uuid: Uuid::max(),
            _phantom: PhantomData,
        }
    }

    /// Creates a UUID from four field values.
    #[inline]
    #[must_use]
    pub const fn from_fields(d1: u32, d2: u16, d3: u16, d4: [u8; 8]) -> Self {
        Self {
            uuid: Uuid::from_fields(d1, d2, d3, &d4),
            _phantom: PhantomData,
        }
    }

    /// Creates a UUID from four field values in little-endian order.
    ///
    /// The bytes in the `d1`, `d2` and `d3` fields will be flipped to convert into big-endian
    /// order. This is based on the endianness of the UUID, rather than the target environment so
    /// bytes will be flipped on both big and little endian machines.
    #[inline]
    #[must_use]
    pub const fn from_fields_le(d1: u32, d2: u16, d3: u16, d4: [u8; 8]) -> Self {
        Self {
            uuid: Uuid::from_fields_le(d1, d2, d3, &d4),
            _phantom: PhantomData,
        }
    }

    /// Creates a UUID from a 128bit value.
    #[inline]
    #[must_use]
    pub const fn from_u128(value: u128) -> Self {
        Self {
            uuid: Uuid::from_u128(value),
            _phantom: PhantomData,
        }
    }

    /// Creates a UUID from a 128bit value in little-endian order.
    ///
    /// The entire value will be flipped to convert into big-endian order. This is based on the
    /// endianness of the UUID, rather than the target environment so bytes will be flipped on both
    /// big and little endian machines.
    #[inline]
    #[must_use]
    pub const fn from_u128_le(value: u128) -> Self {
        Self {
            uuid: Uuid::from_u128_le(value),
            _phantom: PhantomData,
        }
    }

    /// Creates a UUID from two 64bit values.
    #[inline]
    #[must_use]
    pub const fn from_u64_pair(d1: u64, d2: u64) -> Self {
        Self {
            uuid: Uuid::from_u64_pair(d1, d2),
            _phantom: PhantomData,
        }
    }

    /// Creates a UUID using the supplied bytes.
    #[inline]
    #[must_use]
    pub const fn from_bytes(bytes: uuid::Bytes) -> Self {
        Self {
            uuid: Uuid::from_bytes(bytes),
            _phantom: PhantomData,
        }
    }

    /// Creates a UUID using the supplied bytes in little-endian order.
    ///
    /// The individual fields encoded in the buffer will be flipped.
    #[inline]
    #[must_use]
    pub const fn from_bytes_le(bytes: uuid::Bytes) -> Self {
        Self {
            uuid: Uuid::from_bytes_le(bytes),
            _phantom: PhantomData,
        }
    }

    /// Creates a new, random UUID v4 of this type.
    #[inline]
    #[cfg(feature = "v4")]
    #[must_use]
    pub fn new_v4() -> Self {
        Self::from_untyped_uuid(Uuid::new_v4())
    }

    /// Creates a new, random UUID v7 of this type.
    #[inline]
    #[cfg(feature = "v7")]
    #[must_use]
    pub fn new_v7(ts: uuid::Timestamp) -> Self {
        Self::from_untyped_uuid(Uuid::new_v7(ts))
    }

    /// Returns the version number of the UUID.
    ///
    /// This represents the algorithm used to generate the value.
    /// This method is the future-proof alternative to [`Self::get_version`].
    ///
    /// # References
    ///
    /// * [Version Field in RFC 9562](https://www.ietf.org/rfc/rfc9562.html#section-4.2)
    #[inline]
    pub const fn get_version_num(&self) -> usize {
        self.uuid.get_version_num()
    }

    /// Returns the version of the UUID.
    ///
    /// This represents the algorithm used to generate the value.
    /// If the version field doesn't contain a recognized version then `None`
    /// is returned. If you're trying to read the version for a future extension
    /// you can also use [`Uuid::get_version_num`] to unconditionally return a
    /// number. Future extensions may start to return `Some` once they're
    /// standardized and supported.
    ///
    /// # References
    ///
    /// * [Version Field in RFC 9562](https://www.ietf.org/rfc/rfc9562.html#section-4.2)
    #[inline]
    pub fn get_version(&self) -> Option<Version> {
        self.uuid.get_version()
    }

    /// Returns true if the UUID is nil (all zeros).
    #[inline]
    pub const fn is_nil(&self) -> bool {
        self.uuid.is_nil()
    }

    /// Returns true if the UUID is the max value (all ones).
    #[inline]
    pub const fn is_max(&self) -> bool {
        self.uuid.is_max()
    }

    /// Returns the four field values of the UUID.
    ///
    /// These values can be passed to [`Self::from_fields`] to reconstruct the
    /// original UUID. The first field represents the initial eight hex digits
    /// as a big-endian `u32`. The second and third fields represent subsequent
    /// hex digit groups as `u16` values. The final field contains the last two
    /// groups of hex digits as an 8-byte array.
    ///
    /// # Examples
    ///
    /// ```
    /// # use newtype_uuid::TypedUuid;
    /// # enum ExampleKind {}
    /// # impl newtype_uuid::TypedUuidKind for ExampleKind {
    /// #     fn tag() -> newtype_uuid::TypedUuidTag {
    /// #         const TAG: newtype_uuid::TypedUuidTag = newtype_uuid::TypedUuidTag::new("example");
    /// #         TAG
    /// #     }
    /// # }
    /// let uuid: TypedUuid<ExampleKind> =
    ///     "a1a2a3a4-b1b2-c1c2-d1d2-d3d4d5d6d7d8".parse().unwrap();
    ///
    /// assert_eq!(
    ///     uuid.as_fields(),
    ///     (
    ///         0xa1a2a3a4,
    ///         0xb1b2,
    ///         0xc1c2,
    ///         &[0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8],
    ///     )
    /// );
    /// ```
    #[inline]
    pub fn as_fields(&self) -> (u32, u16, u16, &[u8; 8]) {
        self.uuid.as_fields()
    }

    /// Returns the four field values in little-endian order.
    ///
    /// The bytes within integer fields are converted from big-endian order.
    /// This is based on the endianness of the UUID rather than the target
    /// environment, so bytes will be flipped on both big and little endian
    /// machines.
    ///
    /// # Examples
    ///
    /// ```
    /// # use newtype_uuid::TypedUuid;
    /// # enum ExampleKind {}
    /// # impl newtype_uuid::TypedUuidKind for ExampleKind {
    /// #     fn tag() -> newtype_uuid::TypedUuidTag {
    /// #         const TAG: newtype_uuid::TypedUuidTag = newtype_uuid::TypedUuidTag::new("example");
    /// #         TAG
    /// #     }
    /// # }
    /// let uuid: TypedUuid<ExampleKind> =
    ///     "a1a2a3a4-b1b2-c1c2-d1d2-d3d4d5d6d7d8".parse().unwrap();
    ///
    /// assert_eq!(
    ///     uuid.to_fields_le(),
    ///     (
    ///         0xa4a3a2a1,
    ///         0xb2b1,
    ///         0xc2c1,
    ///         &[0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8],
    ///     )
    /// );
    /// ```
    #[inline]
    pub fn to_fields_le(&self) -> (u32, u16, u16, &[u8; 8]) {
        self.uuid.to_fields_le()
    }

    /// Returns a 128-bit value containing the UUID bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use newtype_uuid::TypedUuid;
    /// # enum ExampleKind {}
    /// # impl newtype_uuid::TypedUuidKind for ExampleKind {
    /// #     fn tag() -> newtype_uuid::TypedUuidTag {
    /// #         const TAG: newtype_uuid::TypedUuidTag = newtype_uuid::TypedUuidTag::new("example");
    /// #         TAG
    /// #     }
    /// # }
    /// let uuid: TypedUuid<ExampleKind> =
    ///     "a1a2a3a4-b1b2-c1c2-d1d2-d3d4d5d6d7d8".parse().unwrap();
    ///
    /// assert_eq!(
    ///     uuid.as_u128(),
    ///     0xa1a2a3a4b1b2c1c2d1d2d3d4d5d6d7d8u128,
    /// );
    /// ```
    #[inline]
    pub const fn as_u128(&self) -> u128 {
        self.uuid.as_u128()
    }

    /// Returns a 128-bit little-endian value.
    ///
    /// The bytes in the `u128` will be flipped to convert into big-endian order.
    /// This is based on the endianness of the UUID, rather than the target
    /// environment so bytes will be flipped on both big and little endian
    /// machines.
    ///
    /// Note that this will produce a different result than
    /// [`Self::to_fields_le`], because the entire UUID is reversed, rather than
    /// reversing the individual fields in-place.
    ///
    /// # Examples
    ///
    /// ```
    /// # use newtype_uuid::TypedUuid;
    /// # enum ExampleKind {}
    /// # impl newtype_uuid::TypedUuidKind for ExampleKind {
    /// #     fn tag() -> newtype_uuid::TypedUuidTag {
    /// #         const TAG: newtype_uuid::TypedUuidTag = newtype_uuid::TypedUuidTag::new("example");
    /// #         TAG
    /// #     }
    /// # }
    /// let uuid: TypedUuid<ExampleKind> =
    ///     "a1a2a3a4-b1b2-c1c2-d1d2-d3d4d5d6d7d8".parse().unwrap();
    ///
    /// assert_eq!(
    ///     uuid.to_u128_le(),
    ///     0xd8d7d6d5d4d3d2d1c2c1b2b1a4a3a2a1u128,
    /// );
    /// ```
    #[inline]
    pub fn to_u128_le(&self) -> u128 {
        self.uuid.to_u128_le()
    }

    /// Returns two 64-bit values representing the UUID.
    ///
    /// The first `u64` contains the most significant 64 bits; the second
    /// contains the least significant bits.
    ///
    /// # Examples
    ///
    /// ```
    /// # use newtype_uuid::TypedUuid;
    /// # enum ExampleKind {}
    /// # impl newtype_uuid::TypedUuidKind for ExampleKind {
    /// #     fn tag() -> newtype_uuid::TypedUuidTag {
    /// #         const TAG: newtype_uuid::TypedUuidTag = newtype_uuid::TypedUuidTag::new("example");
    /// #         TAG
    /// #     }
    /// # }
    /// let uuid: TypedUuid<ExampleKind> =
    ///     "a1a2a3a4-b1b2-c1c2-d1d2-d3d4d5d6d7d8".parse().unwrap();
    ///
    /// assert_eq!(
    ///     uuid.as_u64_pair(),
    ///     (0xa1a2a3a4b1b2c1c2, 0xd1d2d3d4d5d6d7d8),
    /// );
    /// ```
    #[inline]
    pub const fn as_u64_pair(&self) -> (u64, u64) {
        self.uuid.as_u64_pair()
    }

    /// Returns a slice of 16 octets containing the value.
    ///
    /// This method borrows the underlying byte value of the UUID.
    ///
    /// # Examples
    ///
    /// ```
    /// # use newtype_uuid::TypedUuid;
    /// # enum ExampleKind {}
    /// # impl newtype_uuid::TypedUuidKind for ExampleKind {
    /// #     fn tag() -> newtype_uuid::TypedUuidTag {
    /// #         const TAG: newtype_uuid::TypedUuidTag = newtype_uuid::TypedUuidTag::new("example");
    /// #         TAG
    /// #     }
    /// # }
    /// let bytes = [
    ///     0xa1, 0xa2, 0xa3, 0xa4,
    ///     0xb1, 0xb2,
    ///     0xc1, 0xc2,
    ///     0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8,
    /// ];
    ///
    /// let uuid = TypedUuid::<ExampleKind>::from_bytes(bytes);
    /// let bytes2 = uuid.as_bytes();
    ///
    /// assert_eq!(&bytes, bytes2);
    /// ```
    #[inline]
    pub const fn as_bytes(&self) -> &uuid::Bytes {
        self.uuid.as_bytes()
    }

    /// Consumes self and returns the underlying byte value of the UUID.
    ///
    /// # Examples
    ///
    /// ```
    /// # use newtype_uuid::TypedUuid;
    /// # enum ExampleKind {}
    /// # impl newtype_uuid::TypedUuidKind for ExampleKind {
    /// #     fn tag() -> newtype_uuid::TypedUuidTag {
    /// #         const TAG: newtype_uuid::TypedUuidTag = newtype_uuid::TypedUuidTag::new("example");
    /// #         TAG
    /// #     }
    /// # }
    /// let bytes = [
    ///     0xa1, 0xa2, 0xa3, 0xa4,
    ///     0xb1, 0xb2,
    ///     0xc1, 0xc2,
    ///     0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8,
    /// ];
    ///
    /// let uuid = TypedUuid::<ExampleKind>::from_bytes(bytes);
    ///
    /// assert_eq!(bytes, uuid.into_bytes());
    /// ```
    #[inline]
    #[must_use]
    pub const fn into_bytes(self) -> uuid::Bytes {
        self.uuid.into_bytes()
    }

    /// Returns the bytes of the UUID in little-endian order.
    ///
    /// The bytes will be flipped to convert into little-endian order. This is
    /// based on the endianness of the UUID, rather than the target environment
    /// so bytes will be flipped on both big and little endian machines.
    ///
    /// # Examples
    ///
    /// ```
    /// # use newtype_uuid::TypedUuid;
    /// # enum ExampleKind {}
    /// # impl newtype_uuid::TypedUuidKind for ExampleKind {
    /// #     fn tag() -> newtype_uuid::TypedUuidTag {
    /// #         const TAG: newtype_uuid::TypedUuidTag = newtype_uuid::TypedUuidTag::new("example");
    /// #         TAG
    /// #     }
    /// # }
    /// let uuid: TypedUuid<ExampleKind> =
    ///     "a1a2a3a4-b1b2-c1c2-d1d2-d3d4d5d6d7d8".parse().unwrap();
    ///
    /// assert_eq!(
    ///     uuid.to_bytes_le(),
    ///     [
    ///         0xa4, 0xa3, 0xa2, 0xa1,
    ///         0xb2, 0xb1,
    ///         0xc2, 0xc1,
    ///         0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8,
    ///     ]
    /// );
    /// ```
    #[inline]
    pub fn to_bytes_le(&self) -> uuid::Bytes {
        self.uuid.to_bytes_le()
    }

    /// Converts the UUID to one with looser semantics.
    ///
    /// By default, UUID kinds are considered independent, and conversions
    /// between them must happen via the [`GenericUuid`] interface. But in some
    /// cases, there may be a relationship between two different UUID kinds, and
    /// you may wish to easily convert UUIDs from one kind to another.
    ///
    /// Typically, a conversion from `TypedUuid<T>` to `TypedUuid<U>` is most
    /// useful when `T`'s semantics are a superset of `U`'s, or in other words,
    /// when every `TypedUuid<T>` is logically also a `TypedUuid<U>`.
    ///
    /// For instance:
    ///
    /// * Imagine you have [`TypedUuidKind`]s for different types of
    ///   database connections, where `DbConnKind` is the general type
    ///   and `PgConnKind` is a specific kind for Postgres.
    /// * Since every Postgres connection is also a database connection,
    ///   a cast from `TypedUuid<PgConnKind>` to `TypedUuid<DbConnKind>`
    ///   makes sense.
    /// * The inverse cast would not make sense, as a database connection may not
    ///   necessarily be a Postgres connection.
    ///
    /// This interface provides an alternative, safer way to perform this
    /// conversion. Indicate your intention to allow a conversion between kinds
    /// by implementing `From<T> for U`, as shown in the example below.
    ///
    /// # Examples
    ///
    /// ```
    /// use newtype_uuid::{TypedUuid, TypedUuidKind, TypedUuidTag};
    ///
    /// // Let's say that these UUIDs represent repositories for different
    /// // version control systems, such that you have a generic RepoKind:
    /// pub enum RepoKind {}
    /// impl TypedUuidKind for RepoKind {
    ///     fn tag() -> TypedUuidTag {
    ///         const TAG: TypedUuidTag = TypedUuidTag::new("repo");
    ///         TAG
    ///     }
    /// }
    ///
    /// // You also have more specific kinds:
    /// pub enum GitRepoKind {}
    /// impl TypedUuidKind for GitRepoKind {
    ///     fn tag() -> TypedUuidTag {
    ///         const TAG: TypedUuidTag = TypedUuidTag::new("git_repo");
    ///         TAG
    ///     }
    /// }
    /// // (and HgRepoKind, JujutsuRepoKind, etc...)
    ///
    /// // First, define a `From` impl. This impl indicates your desire
    /// // to convert from one kind to another.
    /// impl From<GitRepoKind> for RepoKind {
    ///     fn from(value: GitRepoKind) -> Self {
    ///         match value {}
    ///     }
    /// }
    ///
    /// // Now you can convert between them:
    /// let git_uuid: TypedUuid<GitRepoKind> =
    ///     TypedUuid::from_u128(0xe9245204_34ea_4ca7_a1c6_2e94fa49df61);
    /// let repo_uuid: TypedUuid<RepoKind> = git_uuid.upcast();
    /// ```
    #[inline]
    #[must_use]
    pub const fn upcast<U: TypedUuidKind>(self) -> TypedUuid<U>
    where
        T: Into<U>,
    {
        TypedUuid {
            uuid: self.uuid,
            _phantom: PhantomData,
        }
    }
}

// ---
// Trait impls
// ---

impl<T: TypedUuidKind> PartialEq for TypedUuid<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.uuid.eq(&other.uuid)
    }
}

impl<T: TypedUuidKind> Eq for TypedUuid<T> {}

impl<T: TypedUuidKind> PartialOrd for TypedUuid<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: TypedUuidKind> Ord for TypedUuid<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.uuid.cmp(&other.uuid)
    }
}

impl<T: TypedUuidKind> Hash for TypedUuid<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.uuid.hash(state);
    }
}

impl<T: TypedUuidKind> fmt::Debug for TypedUuid<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.uuid.fmt(f)?;
        write!(f, " ({})", T::tag())
    }
}

impl<T: TypedUuidKind> fmt::Display for TypedUuid<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.uuid.fmt(f)
    }
}

impl<T: TypedUuidKind> Clone for TypedUuid<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: TypedUuidKind> Copy for TypedUuid<T> {}

impl<T: TypedUuidKind> FromStr for TypedUuid<T> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let uuid = Uuid::from_str(s).map_err(|error| ParseError {
            error,
            tag: T::tag(),
        })?;
        Ok(Self::from_untyped_uuid(uuid))
    }
}

impl<T: TypedUuidKind> Default for TypedUuid<T> {
    #[inline]
    fn default() -> Self {
        Self::from_untyped_uuid(Uuid::default())
    }
}

impl<T: TypedUuidKind> AsRef<[u8]> for TypedUuid<T> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.uuid.as_ref()
    }
}

#[cfg(feature = "alloc")]
impl<T: TypedUuidKind> From<TypedUuid<T>> for alloc::vec::Vec<u8> {
    #[inline]
    fn from(typed_uuid: TypedUuid<T>) -> Self {
        typed_uuid.into_untyped_uuid().into_bytes().to_vec()
    }
}

#[cfg(feature = "schemars08")]
mod schemars08_imp {
    use super::*;
    use schemars::{
        schema::{InstanceType, Schema, SchemaObject},
        schema_for, JsonSchema, SchemaGenerator,
    };

    const CRATE_NAME: &str = "newtype-uuid";
    const CRATE_VERSION: &str = "1";
    const CRATE_PATH: &str = "newtype_uuid::TypedUuid";

    /// Implements `JsonSchema` for `TypedUuid<T>`, if `T` implements `JsonSchema`.
    ///
    /// * `schema_name` is set to `"TypedUuidFor"`, concatenated by the schema name of `T`.
    /// * `schema_id` is set to `format!("newtype_uuid::TypedUuid<{}>", T::schema_id())`.
    /// * `json_schema` is the same as the one for `Uuid`, with the `x-rust-type` extension
    ///   to allow automatic replacement in typify and progenitor.
    impl<T> JsonSchema for TypedUuid<T>
    where
        T: TypedUuidKind + JsonSchema,
    {
        #[inline]
        fn schema_name() -> String {
            // Use the alias if available, otherwise generate our own schema name.
            if let Some(alias) = T::alias() {
                alias.to_owned()
            } else {
                format!("TypedUuidFor{}", T::schema_name())
            }
        }

        #[inline]
        fn schema_id() -> std::borrow::Cow<'static, str> {
            std::borrow::Cow::Owned(format!("newtype_uuid::TypedUuid<{}>", T::schema_id()))
        }

        #[inline]
        fn json_schema(generator: &mut SchemaGenerator) -> Schema {
            // Look at the schema for `T`. If it has `x-rust-type`, *and* if an
            // alias is available, we can lift up the `x-rust-type` into our own schema.
            //
            // We use a new schema generator for `T` to avoid T's schema being
            // added to the list of schemas in `generator` in case the lifting
            // is successful.
            let t_schema = schema_for!(T);
            if let Some(schema) = lift_json_schema(&t_schema.schema, T::alias()) {
                return schema.into();
            }

            SchemaObject {
                instance_type: Some(InstanceType::String.into()),
                format: Some("uuid".to_string()),
                extensions: [(
                    "x-rust-type".to_string(),
                    serde_json::json!({
                        "crate": CRATE_NAME,
                        "version": CRATE_VERSION,
                        "path": CRATE_PATH,
                        "parameters": [generator.subschema_for::<T>()]
                    }),
                )]
                .into_iter()
                .collect(),
                ..Default::default()
            }
            .into()
        }
    }

    // ? on Option is too easy to make mistakes with, so we use `let Some(..) =
    // .. else` instead.
    #[allow(clippy::question_mark)]
    fn lift_json_schema(schema: &SchemaObject, alias: Option<&str>) -> Option<SchemaObject> {
        let Some(alias) = alias else {
            return None;
        };

        let Some(v) = schema.extensions.get("x-rust-type") else {
            return None;
        };

        // The crate, version and path must all be present.
        let Some(crate_) = v.get("crate") else {
            return None;
        };
        let Some(version) = v.get("version") else {
            return None;
        };
        let Some(path) = v.get("path").and_then(|p| p.as_str()) else {
            return None;
        };
        let Some((module_path, _)) = path.rsplit_once("::") else {
            return None;
        };

        // The preconditions are all met. We can lift the schema by appending
        // the alias to the module path.
        let alias_path = format!("{module_path}::{alias}");

        Some(SchemaObject {
            instance_type: Some(InstanceType::String.into()),
            format: Some("uuid".to_string()),
            extensions: [(
                "x-rust-type".to_string(),
                serde_json::json!({
                    "crate": crate_,
                    "version": version,
                    "path": alias_path,
                }),
            )]
            .into_iter()
            .collect(),
            ..Default::default()
        })
    }
}

#[cfg(feature = "proptest1")]
mod proptest1_imp {
    use super::*;
    use proptest::{
        arbitrary::{any, Arbitrary},
        strategy::{BoxedStrategy, Strategy},
    };

    /// Parameters for use with `proptest` instances.
    ///
    /// This is currently not exported as a type because it has no options. But
    /// it's left in as an extension point for the future.
    #[derive(Clone, Debug, Default)]
    pub struct TypedUuidParams(());

    /// Generates random `TypedUuid<T>` instances.
    ///
    /// Currently, this always returns a version 4 UUID. Support for other kinds
    /// of UUIDs might be added via [`Self::Parameters`] in the future.
    impl<T> Arbitrary for TypedUuid<T>
    where
        T: TypedUuidKind,
    {
        type Parameters = TypedUuidParams;
        type Strategy = BoxedStrategy<Self>;

        fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
            let bytes = any::<[u8; 16]>();
            bytes
                .prop_map(|b| {
                    let uuid = uuid::Builder::from_random_bytes(b).into_uuid();
                    TypedUuid::<T>::from_untyped_uuid(uuid)
                })
                .boxed()
        }
    }
}

/// Represents marker types that can be used as a type parameter for [`TypedUuid`].
///
/// Generally, an implementation of this will be a zero-sized type that can never be constructed. An
/// empty struct or enum works well for this.
///
/// # Implementations
///
/// If the `schemars08` feature is enabled, and [`JsonSchema`] is implemented for a kind `T`, then
/// [`TypedUuid`]`<T>` will also implement [`JsonSchema`].
///
/// If you have a large number of UUID kinds, consider using
/// [`newtype-uuid-macros`] which comes with several convenience features.
///
/// ```
/// use newtype_uuid_macros::impl_typed_uuid_kinds;
///
/// // Invoke this macro with:
/// impl_typed_uuid_kinds! {
///     kinds = {
///         User = {},
///         Project = {},
///         // ...
///     },
/// }
/// ```
///
/// See [`newtype-uuid-macros`] for more information.
///
/// [`newtype-uuid-macros`]: https://docs.rs/newtype-uuid-macros
/// [`JsonSchema`]: schemars::JsonSchema
pub trait TypedUuidKind: Send + Sync + 'static {
    /// Returns the corresponding tag for this kind.
    ///
    /// The tag forms a runtime representation of this type.
    ///
    /// The tag is required to be a static string.
    fn tag() -> TypedUuidTag;

    /// Returns a string that corresponds to a type alias for `TypedUuid<Self>`,
    /// if one is defined.
    ///
    /// The type alias must be defined in the same module as `Self`. This
    /// function is used by the schemars integration to refer to embed a
    /// reference to that alias in the schema, if available.
    ///
    /// This is usually defined by the [`newtype-uuid-macros`] crate.
    ///
    /// [`newtype-uuid-macros`]: https://docs.rs/newtype-uuid-macros
    #[inline]
    fn alias() -> Option<&'static str> {
        None
    }
}

/// Describes what kind of [`TypedUuid`] something is.
///
/// This is the runtime equivalent of [`TypedUuidKind`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypedUuidTag(&'static str);

impl TypedUuidTag {
    /// Creates a new `TypedUuidTag` from a static string.
    ///
    /// The string must be non-empty, and consist of:
    /// - ASCII letters
    /// - digits (only after the first character)
    /// - underscores
    /// - hyphens (only after the first character)
    ///
    /// # Panics
    ///
    /// Panics if the above conditions aren't met. Use [`Self::try_new`] to handle errors instead.
    #[must_use]
    pub const fn new(tag: &'static str) -> Self {
        match Self::try_new_impl(tag) {
            Ok(tag) => tag,
            Err(message) => panic!("{}", message),
        }
    }

    /// Attempts to create a new `TypedUuidTag` from a static string.
    ///
    /// The string must be non-empty, and consist of:
    /// - ASCII letters
    /// - digits (only after the first character)
    /// - underscores
    /// - hyphens (only after the first character)
    ///
    /// # Errors
    ///
    /// Returns a [`TagError`] if the above conditions aren't met.
    pub const fn try_new(tag: &'static str) -> Result<Self, TagError> {
        match Self::try_new_impl(tag) {
            Ok(tag) => Ok(tag),
            Err(message) => Err(TagError {
                input: tag,
                message,
            }),
        }
    }

    const fn try_new_impl(tag: &'static str) -> Result<Self, &'static str> {
        if tag.is_empty() {
            return Err("tag must not be empty");
        }

        let bytes = tag.as_bytes();
        if !(bytes[0].is_ascii_alphabetic() || bytes[0] == b'_') {
            return Err("first character of tag must be an ASCII letter or underscore");
        }

        let mut bytes = match bytes {
            [_, rest @ ..] => rest,
            [] => panic!("already checked that it's non-empty"),
        };
        while let [rest @ .., last] = &bytes {
            if !(last.is_ascii_alphanumeric() || *last == b'_' || *last == b'-') {
                break;
            }
            bytes = rest;
        }

        if !bytes.is_empty() {
            return Err("tag must only contain ASCII letters, digits, underscores, or hyphens");
        }

        Ok(Self(tag))
    }

    /// Returns the tag as a string.
    pub const fn as_str(&self) -> &'static str {
        self.0
    }
}

impl fmt::Display for TypedUuidTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl AsRef<str> for TypedUuidTag {
    fn as_ref(&self) -> &str {
        self.0
    }
}

/// An error that occurred while creating a [`TypedUuidTag`].
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct TagError {
    /// The input string.
    pub input: &'static str,

    /// The error message.
    pub message: &'static str,
}

impl fmt::Display for TagError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "error creating tag from '{}': {}",
            self.input, self.message
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TagError {}

/// An error that occurred while parsing a [`TypedUuid`].
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct ParseError {
    /// The underlying error.
    pub error: uuid::Error,

    /// The tag of the UUID that failed to parse.
    pub tag: TypedUuidTag,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error parsing UUID ({})", self.tag)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

/// A trait abstracting over typed and untyped UUIDs.
///
/// This can be used to write code that's generic over [`TypedUuid`], [`Uuid`], and other types that
/// may wrap [`TypedUuid`] (due to e.g. orphan rules).
///
/// This trait is similar to `From`, but a bit harder to get wrong -- in general, the conversion
/// from and to untyped UUIDs should be careful and explicit.
pub trait GenericUuid {
    /// Creates a new instance of `Self` from an untyped [`Uuid`].
    #[must_use]
    fn from_untyped_uuid(uuid: Uuid) -> Self
    where
        Self: Sized;

    /// Converts `self` into an untyped [`Uuid`].
    #[must_use]
    fn into_untyped_uuid(self) -> Uuid
    where
        Self: Sized;

    /// Returns the inner [`Uuid`].
    ///
    /// Generally, [`into_untyped_uuid`](Self::into_untyped_uuid) should be preferred. However,
    /// in some cases it may be necessary to use this method to satisfy lifetime constraints.
    fn as_untyped_uuid(&self) -> &Uuid;
}

impl GenericUuid for Uuid {
    #[inline]
    fn from_untyped_uuid(uuid: Uuid) -> Self {
        uuid
    }

    #[inline]
    fn into_untyped_uuid(self) -> Uuid {
        self
    }

    #[inline]
    fn as_untyped_uuid(&self) -> &Uuid {
        self
    }
}

impl<T: TypedUuidKind> GenericUuid for TypedUuid<T> {
    #[inline]
    fn from_untyped_uuid(uuid: Uuid) -> Self {
        Self {
            uuid,
            _phantom: PhantomData,
        }
    }

    #[inline]
    fn into_untyped_uuid(self) -> Uuid {
        self.uuid
    }

    #[inline]
    fn as_untyped_uuid(&self) -> &Uuid {
        &self.uuid
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_tags() {
        for &valid_tag in &[
            "a", "a-", "a_", "a-b", "a_b", "a1", "a1-", "a1_", "a1-b", "a1_b", "_a",
        ] {
            TypedUuidTag::try_new(valid_tag).expect("tag is valid");
            // Should not panic
            _ = TypedUuidTag::new(valid_tag);
        }

        for invalid_tag in &["", "1", "-", "a1b!", "a1-b!", "a1_b:", "\u{1f4a9}"] {
            TypedUuidTag::try_new(invalid_tag).unwrap_err();
        }
    }

    // This test just ensures that `GenericUuid` is object-safe.
    #[test]
    #[cfg(all(feature = "v4", feature = "std"))]
    fn test_generic_uuid_object_safe() {
        let uuid = Uuid::new_v4();
        let box_uuid = Box::new(uuid) as Box<dyn GenericUuid>;
        assert_eq!(box_uuid.as_untyped_uuid(), &uuid);
    }
}
