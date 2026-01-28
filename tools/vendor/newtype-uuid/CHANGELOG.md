# Changelog

## [1.3.2] - 2025-11-06

### Added

- `as_fields`, `to_fields_le`, `as_u128`, `to_u128_le`, `as_u64_pair`, `as_bytes`, `into_bytes`, `to_bytes_le`, `is_nil`, and `is_max` methods to mirror corresponding methods on upstream `Uuid`.

## [1.3.1] - 2025-09-30

### Added

- New `v7` feature allows for v7 UUIDs to be created. Thanks [davidbarsky](https://github.com/davidbarsky) for your first contribution!

### Fixed

Replaced obsolete `doc_auto_cfg` with `doc_cfg`, to fix Rust nightly builds with the `doc_cfg` flag enabled.

## [1.3.0] - 2025-08-19

### Added

- For schemars integration, automatic replacement support with [`typify`] and [`progenitor`] via the new `x-rust-type` extension.
- The `TypedUuidKind` trait has a new optional method called `alias`, which represents a type alias. `alias` is used by schemars integration in a few ways: for the schema name of `TypedUuid<T>`, as well as for automatic replacement support.

[`typify`]: https://github.com/oxidecomputer/typify
[`progenitor`]: https://github.com/oxidecomputer/progenitor

### Changed

- MSRV updated to Rust 1.79.

## [1.2.4] - 2025-06-17

### Added

New `upcast` method enables safer conversion of one typed UUID to another. To opt into an upcast from `TypedUuid<T>` to `TypedUuid<U>`, implement `From<T> for U`.

## [1.2.3] - 2025-06-16

(This release was yanked because `cast` was renamed to `upcast`.)

## [1.2.2] - 2025-05-24

### Added

Added the following implementations:

- `AsRef<[u8]>` for `TypedUuid<T>`.
- `From<TypedUuid<T>> for Vec<u8>`.

## [1.2.1] - 2025-01-14

Updated MSRV in readme.

## [1.2.0] - 2025-01-14

### Added

- New, optional feature `proptest1` enables support for generating random instances of UUIDs. Currently, v4 UUIDs are always generated.

### Changed

- MSRV updated to Rust 1.67.

## [1.1.3] - 2024-11-07

### Added

- Add a `Default` implementation for `TypedUuid`. This implementation resolves
  to `TypedUuid::nil()`.

## [1.1.2] - 2024-10-07

### Added

More const constructors for typed UUIDs, mirrored from the `uuid` crate: `from_fields`,
`from_fields_le`, `from_u128`, `from_u128_le`, `from_u64_pair`, `from_bytes`, and `from_bytes_le`.

### Fixed

Correct doc for `as_untyped_uuid`. Thanks [@Dr-Emann](https://github.com/Dr-Emann) for your first contribution!

## [1.1.1] - 2024-10-07

(This version was not released due to a publishing issue.)

## [1.1.0] - 2024-04-12

### Added

- `TypedUuid::nil()` and `max()` constructors.
- `TypedUuid` is now `#[repr(transparent)]`.

### Changed

- MSRV updated to Rust 1.61.

## [1.0.1] - 2024-02-15

### Breaking changes

- `GenericUuid::to_generic_uuid` has been renamed to `GenericUuid::into_generic_uuid`.

### Changed

- Added `#[must_use]` annotations to constructors.

## [1.0.0] - 2024-02-15

(This version was not published due to a CI issue.)

## [0.3.0] - 2024-02-02

### Breaking changes

- `TypedUuidTag::try_new` returns a new `TagError` type rather than just a raw `&'static str`.

### Changed

- `TypedUuidTag::as_str` is now a `const fn`.

## [0.2.1] - 2024-02-02

Documentation improvements.

## [0.2.0] - 2024-02-01

### Breaking changes

- `TypedUuidTag`s are now required to be valid ASCII identifiers, with hyphens also supported.

### Misc

- Added `#[forbid(unsafe_code)]`. Thanks [Robert Lynch](https://github.com/rob0rt) for the contribution!

## [0.1.0] - 2024-01-30

Initial release.

[1.3.2]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.3.2
[1.3.1]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.3.1
[1.3.0]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.3.0
[1.2.4]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.2.4
[1.2.3]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.2.3
[1.2.2]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.2.2
[1.2.1]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.2.1
[1.2.0]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.2.0
[1.1.3]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.1.3
[1.1.2]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.1.2
[1.1.1]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.1.1
[1.1.0]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.1.0
[1.0.1]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.0.1
[1.0.0]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-1.0.0
[0.3.0]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-0.3.0
[0.2.1]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-0.2.1
[0.2.0]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-0.2.0
[0.1.0]: https://github.com/oxidecomputer/newtype-uuid/releases/newtype-uuid-0.1.0
