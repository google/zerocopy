<!-- cargo-sync-rdme title [[ -->
# newtype-uuid
<!-- cargo-sync-rdme ]] -->
<!-- cargo-sync-rdme badge [[ -->
![License: MIT OR Apache-2.0](https://img.shields.io/crates/l/newtype-uuid.svg?)
[![crates.io](https://img.shields.io/crates/v/newtype-uuid.svg?logo=rust)](https://crates.io/crates/newtype-uuid)
[![docs.rs](https://img.shields.io/docsrs/newtype-uuid.svg?logo=docs.rs)](https://docs.rs/newtype-uuid)
[![Rust: ^1.79.0](https://img.shields.io/badge/rust-^1.79.0-93450a.svg?logo=rust)](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field)
<!-- cargo-sync-rdme ]] -->
<!-- cargo-sync-rdme rustdoc [[ -->
A newtype wrapper around [`Uuid`](https://docs.rs/uuid/1.17.0/uuid/struct.Uuid.html).

## Motivation

Many large systems use UUIDs as unique identifiers for various entities. However, the [`Uuid`](https://docs.rs/uuid/1.17.0/uuid/struct.Uuid.html)
type does not carry information about the kind of entity it identifies, which can lead to mixing
up different types of UUIDs at runtime.

This crate provides a wrapper type around [`Uuid`](https://docs.rs/uuid/1.17.0/uuid/struct.Uuid.html) that allows you to specify the kind of entity
the UUID identifies.

## Example

````rust
use newtype_uuid::{GenericUuid, TypedUuid, TypedUuidKind, TypedUuidTag};

// First, define a type that represents the kind of UUID this is.
enum MyKind {}

impl TypedUuidKind for MyKind {
    fn tag() -> TypedUuidTag {
        // Tags are required to be ASCII identifiers, with underscores
        // and dashes also supported. The validity of a tag can be checked
        // at compile time by assigning it to a const, like so:
        const TAG: TypedUuidTag = TypedUuidTag::new("my_kind");
        TAG
    }
}

// Now, a UUID can be created with this kind.
let uuid: TypedUuid<MyKind> = "dffc3068-1cd6-47d5-b2f3-636b41b07084".parse().unwrap();

// The Display (and therefore ToString) impls still show the same value.
assert_eq!(uuid.to_string(), "dffc3068-1cd6-47d5-b2f3-636b41b07084");

// The Debug impl will show the tag as well.
assert_eq!(
    format!("{:?}", uuid),
    "dffc3068-1cd6-47d5-b2f3-636b41b07084 (my_kind)"
);
````

If you have a large number of UUID kinds, consider using
[`newtype-uuid-macros`] which comes with several convenience features.

````rust
use newtype_uuid_macros::impl_typed_uuid_kinds;

// Invoke this macro with:
impl_typed_uuid_kinds! {
    kinds = {
        User = {},
        Project = {},
        // ...
    },
}
````

See [`newtype-uuid-macros`] for more information.

For simpler cases, you can also write your own declarative macro. Use this
template to get started:

````rust
macro_rules! impl_kinds {
    ($($kind:ident => $tag:literal),* $(,)?) => {
        $(
            pub enum $kind {}

            impl TypedUuidKind for $kind {
                #[inline]
                fn tag() -> TypedUuidTag {
                    const TAG: TypedUuidTag = TypedUuidTag::new($tag);
                    TAG
                }
            }
        )*
    };
}

// Invoke this macro with:
impl_kinds! {
    UserKind => "user",
    ProjectKind => "project",
}
````

## Implementations

In general, [`TypedUuid`](https://docs.rs/newtype-uuid/1.2.4/newtype_uuid/struct.TypedUuid.html) uses the same wire and serialization formats as [`Uuid`](https://docs.rs/uuid/1.17.0/uuid/struct.Uuid.html). This means
that persistent representations of [`TypedUuid`](https://docs.rs/newtype-uuid/1.2.4/newtype_uuid/struct.TypedUuid.html) are the same as [`Uuid`](https://docs.rs/uuid/1.17.0/uuid/struct.Uuid.html); [`TypedUuid`](https://docs.rs/newtype-uuid/1.2.4/newtype_uuid/struct.TypedUuid.html) is
intended to be helpful within Rust code, not across serialization boundaries.

* The `Display` and `FromStr` impls are forwarded to the underlying [`Uuid`](https://docs.rs/uuid/1.17.0/uuid/struct.Uuid.html).
* If the `serde` feature is enabled, `TypedUuid` will serialize and deserialize using the same
  format as [`Uuid`](https://docs.rs/uuid/1.17.0/uuid/struct.Uuid.html).
* If the `schemars08` feature is enabled, [`TypedUuid`](https://docs.rs/newtype-uuid/1.2.4/newtype_uuid/struct.TypedUuid.html) will implement `JsonSchema` if the
  corresponding [`TypedUuidKind`](https://docs.rs/newtype-uuid/1.2.4/newtype_uuid/trait.TypedUuidKind.html) implements `JsonSchema`.

To abstract over typed and untyped UUIDs, the [`GenericUuid`](https://docs.rs/newtype-uuid/1.2.4/newtype_uuid/trait.GenericUuid.html) trait is provided. This trait also
permits conversions between typed and untyped UUIDs.

## Dependencies

* The only required dependency is the [`uuid`](https://docs.rs/uuid/1.17.0/uuid/index.html) crate. Optional features may add further
  dependencies.

## Features

* `default`: Enables default features in the newtype-uuid crate.
* `std`: Enables the use of the standard library. *Enabled by default.*
* `serde`: Enables serialization and deserialization support via Serde. *Not enabled by
  default.*
* `v4`: Enables the `new_v4` method for generating UUIDs. *Not enabled by default.*
* `schemars08`: Enables support for generating JSON schemas via schemars 0.8. *Not enabled by
  default.* Note that the format of the generated schema is **not currently part** of the stable
  API, though we hope to stabilize it in the future.
* `proptest1`: Enables support for generating `proptest::Arbitrary` instances of UUIDs. *Not enabled by default.*

## Minimum supported Rust version (MSRV)

The MSRV of this crate is **Rust 1.79.** In general, this crate will follow the MSRV of the
underlying `uuid` crate or of dependencies, with an aim to be conservative.

Within the 1.x series, MSRV updates will be accompanied by a minor version bump. The MSRVs for
each minor version are:

* Version **1.0.x**: Rust 1.60.
* Version **1.1.x**: Rust 1.61. This permits `TypedUuid<T>` to have `const fn` methods.
* Version **1.2.x**: Rust 1.67, required by some dependency updates.
* Version **1.3.x**: Rust 1.79, required by some dependency updates.

## Alternatives

* [`typed-uuid`](https://crates.io/crates/typed-uuid): generally similar, but with a few design
  decisions that are different.

[`newtype-uuid-macros`]: https://docs.rs/newtype-uuid-macros
<!-- cargo-sync-rdme ]] -->

## License

This project is available under the terms of either the [Apache 2.0 license](LICENSE-APACHE) or the [MIT
license](LICENSE-MIT).
