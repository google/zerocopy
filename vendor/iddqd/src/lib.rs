//! Maps where keys are borrowed from values.
//!
//! This crate consists of several map types, collectively called **ID maps**:
//!
//! - [`IdOrdMap`]: A B-Tree based map where keys are borrowed from values.
//! - [`IdHashMap`]: A hash map where keys are borrowed from values.
//! - [`BiHashMap`]: A bijective (1:1) hash map with two keys, borrowed from
//!   values.
//! - [`TriHashMap`]: A trijective (1:1:1) hash map with three keys, borrowed
//!   from values.
//!
//! # Usage
//!
//! * Pick your ID map type.
//! * Depending on the ID map type, implement [`IdOrdItem`], [`IdHashItem`],
//!   [`BiHashItem`], or [`TriHashItem`] for your value type.
//! * Store values in the ID map type.
//!
//! ## Features
//!
//! This crate was built out a practical need for map types, and addresses
//! issues encountered using Rust's default map types in practice at Oxide.
//!
//! * Keys are retrieved from values, not stored separately from them. Separate
//!   storage has been a recurring pain point in our codebases: if keys are
//!   duplicated within values, it's proven to be hard to maintain consistency
//!   between keys and values. This crate addresses that need.
//! * Keys may be borrowed from values, which allows for more flexible
//!   implementations. (They don't have to be borrowed, but they can be.)
//! * There's no `insert` method; insertion must be through either
//!   `insert_overwrite` or `insert_unique`. You must pick an insertion
//!   behavior.
//! * For hash maps, the default hasher is [`foldhash`], which is much faster
//!   than SipHash. However, foldhash does *not provide the same level of HashDoS
//!   resistance* as SipHash. If that is important to you, you can use a different
//!   hasher. (Disable the `default-hasher` feature to require a hash
//!   builder type parameter to be passed in.)
//! * The serde implementations reject duplicate keys.
//!
//! We've also sometimes needed to index a set of data by more than one key, or
//! perhaps map one key to another. For that purpose, this crate provides
//! [`BiHashMap`] and [`TriHashMap`].
//!
//! * [`BiHashMap`] has two keys, and provides a bijection (1:1 relationship)
//!   between the keys.
//! * [`TriHashMap`] has three keys, and provides a trijection (1:1:1
//!   relationship) between the keys.
//!
//! As a consequence of the general API structure, maps can have arbitrary
//! non-key data associated with them as well.
//!
//! ## Examples
//!
//! An example for [`IdOrdMap`]:
//!
//! ```
//! # #[cfg(feature = "std")] {
//! use iddqd::{IdOrdItem, IdOrdMap, id_upcast};
//!
//! #[derive(Debug)]
//! struct User {
//!     name: String,
//!     age: u8,
//! }
//!
//! // Implement IdOrdItem so the map knows how to get the key from the value.
//! impl IdOrdItem for User {
//!     // The key type can borrow from the value.
//!     type Key<'a> = &'a str;
//!
//!     fn key(&self) -> Self::Key<'_> {
//!         &self.name
//!     }
//!
//!     id_upcast!();
//! }
//!
//! let mut users = IdOrdMap::<User>::new();
//!
//! // You must pick an insertion behavior. insert_unique returns an error if
//! // the key already exists.
//! users.insert_unique(User { name: "Alice".to_string(), age: 30 }).unwrap();
//! users.insert_unique(User { name: "Bob".to_string(), age: 35 }).unwrap();
//!
//! // Lookup by name:
//! assert_eq!(users.get("Alice").unwrap().age, 30);
//! assert_eq!(users.get("Bob").unwrap().age, 35);
//!
//! // Iterate over users:
//! for user in &users {
//!     println!("User {}: {}", user.name, user.age);
//! }
//! # }
//! ```
//!
//! Keys don't have to be borrowed from the value. For smaller `Copy` types,
//! it's recommended that you use owned keys. Here's an example of using
//! [`IdOrdMap`] with a small integer key:
//!
//! ```
//! # #[cfg(feature = "std")] {
//! # use iddqd::{IdOrdMap, IdOrdItem, id_upcast};
//! struct Record {
//!     id: u32,
//!     data: String,
//! }
//!
//! impl IdOrdItem for Record {
//!     // The key type is small, so an owned key is preferred.
//!     type Key<'a> = u32;
//!
//!     fn key(&self) -> Self::Key<'_> {
//!         self.id
//!     }
//!
//!     id_upcast!();
//! }
//!
//! // ...
//! # }
//! ```
//!
//! An example for [`IdHashMap`], showing a complex borrowed key. Here,
//! "complex" means that the key is not a reference itself, but a struct that
//! returns references to more than one field from the value.
//!
//! ```
//! # #[cfg(feature = "default-hasher")] {
//! use iddqd::{IdHashItem, id_hash_map, id_upcast};
//!
//! #[derive(Debug)]
//! struct Artifact {
//!     name: String,
//!     version: String,
//!     data: Vec<u8>,
//! }
//!
//! // The key type is a borrowed form of the name and version. It needs to
//! // implement `Eq + Hash`.
//! #[derive(Eq, Hash, PartialEq)]
//! struct ArtifactKey<'a> {
//!     name: &'a str,
//!     version: &'a str,
//! }
//!
//! impl IdHashItem for Artifact {
//!     // The key type can borrow from the value.
//!     type Key<'a> = ArtifactKey<'a>;
//!
//!     fn key(&self) -> Self::Key<'_> {
//!         ArtifactKey { name: &self.name, version: &self.version }
//!     }
//!
//!     id_upcast!();
//! }
//!
//! // Create a new `IdHashMap` with the given artifacts. This uses the
//! // `id_hash_map!` macro that comes with iddqd.
//! let artifacts = id_hash_map! {
//!     Artifact {
//!         name: "artifact1".to_owned(),
//!         version: "1.0".to_owned(),
//!         data: b"data1".to_vec(),
//!     },
//!     Artifact {
//!         name: "artifact2".to_owned(),
//!         version: "1.0".to_owned(),
//!         data: b"data2".to_vec(),
//!     },
//! };
//!
//! // Look up artifacts by name and version.
//! assert_eq!(
//!     artifacts
//!         .get(&ArtifactKey { name: "artifact1", version: "1.0" })
//!         .unwrap()
//!         .data,
//!     b"data1",
//! );
//! # }
//! ```
//!
//! For more examples, see the
//! [examples](https://github.com/oxidecomputer/iddqd/tree/main/crates/iddqd/examples)
//! and [extended
//! examples](https://github.com/oxidecomputer/iddqd/tree/main/crates/iddqd-extended-examples/examples)
//! directories.
//!
//! ### `Equivalent` and `Comparable`
//!
//! An important feature of the standard library's maps is that they allow any
//! borrowed form of the key type to be used for lookups; for example, a
//! `HashMap<String, T>` type can be looked up with a `&str` key. This is done
//! through the [`Borrow`] trait.
//!
//! But the [`Borrow`] trait is a bit too restrictive for complex keys such as
//! `ArtifactKey` above, requiring workarounds such as [dynamic
//! dispatch](https://github.com/sunshowers-code/borrow-complex-key-example). To
//! address this, the crates.io ecosystem has standardized on the [`Equivalent`]
//! and [`Comparable`] traits as generalizations of `Borrow`. The map types in
//! this crate require these traits.
//!
//! For a key type `T::Key<'_>` and a lookup type `L`:
//!
//! * The hash map types require `L: Hash + Equivalent<T::Key<'_>>`. Also, `L`
//!   must hash in the same way as `T::Key<'_>`. Typically, this is done by
//!   ensuring that enum variants and struct fields are in the same
//!   order[^proptest].
//! * [`IdOrdMap`] requires `L: Comparable<T::Key<'_>>`, which in turn requires
//!   `Equivalent<T::Key<'_>>`. (There's no need for `L` to implement `Ord` or
//!   `Eq` itself.)
//!
//! [^proptest]: We recommend that you test this with e.g. a property-based
//!   test: see [this
//!   example](https://github.com/sunshowers-code/borrow-complex-key-example/blob/a6f17699/src/lib.rs#L233).
//!
//! Continuing the `ArtifactKey` example from above, we can perform a lookup
//! using a key of this owned form:
//!
//! ```
//! # #[cfg(feature = "default-hasher")] {
//! use equivalent::Equivalent;
//! # use iddqd::{id_hash_map, IdHashItem, id_upcast};
//! # #[derive(Debug)]
//! # struct Artifact {
//! #     name: String,
//! #     version: String,
//! #     data: Vec<u8>,
//! # }
//! # #[derive(Eq, Hash, PartialEq)]
//! # struct ArtifactKey<'a> {
//! #     name: &'a str,
//! #     version: &'a str,
//! # }
//! # impl IdHashItem for Artifact {
//! #     type Key<'a> = ArtifactKey<'a>;
//! #     fn key(&self) -> Self::Key<'_> {
//! #         ArtifactKey {
//! #             name: &self.name,
//! #             version: &self.version,
//! #         }
//! #     }
//! #     id_upcast!();
//! # }
//! # let artifacts = id_hash_map! {
//! #     Artifact {
//! #         name: "artifact1".to_owned(),
//! #         version: "1.0".to_owned(),
//! #         data: b"data1".to_vec(),
//! #     }
//! # };
//!
//! // This is an owned form of ArtifactKey. The fields are in the same
//! // order as ArtifactKey's fields, so it hashes the same way.
//! #[derive(Hash)]
//! struct OwnedArtifactKey {
//!     name: String,
//!     version: String,
//! }
//!
//! impl Equivalent<ArtifactKey<'_>> for OwnedArtifactKey {
//!     fn equivalent(&self, other: &ArtifactKey<'_>) -> bool {
//!         self.name == other.name && self.version == other.version
//!     }
//! }
//!
//! // Now you can use OwnedArtifactKey to look up the artifact.
//! let owned_key = OwnedArtifactKey {
//!     name: "artifact1".to_owned(),
//!     version: "1.0".to_owned(),
//! };
//! assert_eq!(artifacts.get(&owned_key).unwrap().data, b"data1",);
//! # }
//! ```
//!
//! There's a blanket implementation of [`Equivalent`] and [`Comparable`] for
//! [`Borrow`], so if your type already implements [`Borrow`], there aren't any
//! extra steps to take.
//!
//! # Testing
//!
//! This crate is validated through a combination of:
//!
//! * Unit tests
//! * Property-based tests using a naive map as an oracle
//! * Chaos tests for several kinds of buggy `Eq` and `Ord` implementations
//! * Miri tests for unsafe code
//!
//! If you see a gap in testing, new tests are welcome. Thank you!
//!
//! # No-std compatibility
//!
//! Most of this crate is no-std compatible, though [`alloc`] is required.
//!
//! The [`IdOrdMap`] type is not currently no-std compatible due to its use of a
//! thread-local. This thread-local is just a way to work around a limitation in
//! std's `BTreeMap` API, though. Either a custom B-Tree implementation, or a
//! platform-specific notion of thread locals, would suffice to make
//! [`IdOrdMap`] no-std compatible.
//!
//! # Optional features
//!
//! - `allocator-api2`: Enables support for custom allocators via the
//!   [`allocator_api2`] crate. Both global and scoped/arena allocators
//!   (such as `bumpalo`) are supported. Custom allocators are not currently
//!   supported by `IdOrdMap`.
//! - `daft`: Enables [`daft`] support for all ID map types. *Not enabled by
//!   default.*
//! - `default-hasher`: Enables the `DefaultHashBuilder` type. Disable this
//!   feature to require a hash builder type parameter to be passed into
//!   [`IdHashMap`], [`BiHashMap`], and [`TriHashMap`]. *Enabled by default.*
//! - `proptest`: Enables [`proptest`] support for all ID map types, providing
//!   [`Arbitrary`] implementations and strategies for property-based testing.
//!   *Not enabled by default.*
//! - `schemars08`: Enables [`schemars`] support for all ID map types,
//!   including support for [automatic replacement] through [`typify`] or
//!   [`dropshot`]. *Not enabled by default.*
//! - `serde`: Enables serde support for all ID map types. *Not enabled by
//!   default.*
//! - `std`: Enables std support. *Enabled by default.*
//!
//! # Related work
//!
//! - [`bimap`](https://docs.rs/bimap) provides a bijective map, but does not
//!   have a way to associate arbitrary values with each pair of keys. However,
//!   it does support an ordered map type without the need for std.
//!
//! - [`multi_index_map`](https://crates.io/crates/multi_index_map) provides
//!   maps with arbitrary indexes on fields, and is more flexible than this
//!   crate. However, it doesn't expose generic traits for map types, and it
//!   requires key types to be `Clone`. In `iddqd`, we pick a somewhat different
//!   point in the design space, but we think `multi_index_map` is also great.
//!
//! - In general, this is similar to relational database records with
//!   indexes. For sufficiently complex use cases, consider an embedded
//!   database like [SQLite](https://www.sqlite.org/), or even a networked
//!   database like [PostgreSQL](https://www.postgresql.org/). `iddqd` is a
//!   good fit for simple in-memory caches of data stored in these databases.
//!
//! # Minimum supported Rust version (MSRV)
//!
//! This crate's MSRV is **Rust 1.81**. In general we aim for 6 months of Rust
//! compatibility.
//!
//! # What does iddqd mean?
//!
//! The name `iddqd` is a reference to [a cheat
//! code](https://doomwiki.org/wiki/Doom_cheat_codes) in the classic video game
//! _Doom_. It has `id` in the name, and is short and memorable.
//!
//! [`Borrow`]: core::borrow::Borrow
//! [JSON Schema]: https://json-schema.org/
//! [OpenAPI]: https://www.openapis.org/
//! [`schemars`]: https://crates.io/crates/schemars
//! [automatic replacement]: https://github.com/oxidecomputer/iddqd/blob/main/crates/iddqd-extended-examples/examples/typify-types.rs
//! [`typify`]: https://crates.io/crates/typify
//! [`dropshot`]: https://crates.io/crates/dropshot
//! [`Arbitrary`]: proptest::arbitrary::Arbitrary

#![no_std]
#![cfg_attr(doc_cfg, feature(doc_cfg))]
#![warn(missing_docs)]

#[cfg_attr(not(feature = "std"), macro_use)] // for `format!`
extern crate alloc;
#[cfg(feature = "std")]
#[macro_use]
extern crate std;

// This must go first so macros can be used in the rest of the crate.
#[macro_use]
mod macros;

pub mod bi_hash_map;
pub mod errors;
pub mod id_hash_map;
#[cfg(feature = "std")]
pub mod id_ord_map;
#[doc(hidden)]
pub mod internal;
mod support;
pub mod tri_hash_map;

pub use bi_hash_map::{imp::BiHashMap, trait_defs::BiHashItem};
// Re-exports of equivalent traits. Comparable is only used by IdOrdMap, hence
// is restricted to std.
#[cfg(feature = "std")]
#[doc(no_inline)]
pub use equivalent::Comparable;
#[doc(no_inline)]
pub use equivalent::Equivalent;
pub use id_hash_map::{imp::IdHashMap, trait_defs::IdHashItem};
#[cfg(feature = "std")]
pub use id_ord_map::{imp::IdOrdMap, trait_defs::IdOrdItem};
#[cfg(feature = "daft")]
pub use support::daft_utils::IdLeaf;
pub use support::hash_builder::DefaultHashBuilder;
pub use tri_hash_map::{imp::TriHashMap, trait_defs::TriHashItem};
