# Changelog

All notable changes to this project will be documented in this file.

This project adheres to [Semantic Versioning](https://semver.org).

## [1.1.2] - 2025-10-02

Simplify `Buf::chunks_vectored` implementations for `BufList` and `Cursor<T>`.

## [1.1.1] - 2025-10-01

### Added

`bytes::Buf` implementations for `Cursor<BufList>` and `Cursor<&BufList>`, to go with the existing `bytes::Buf` implementation for `BufList` itself. This way, the same `BufList` can have multiple cursors over it that all use the `bytes::Buf` implementation.

## [1.1.0] - 2025-09-29

### Changed

- With `Cursor::read_exact`, if there aren't enough bytes remaining, the position will be set to the end of the buffer. This mirrors the same behavior change in `std::io::Cursor` introduced in Rust 1.80 (see [rust-lang/rust#125404]).
- MSRV updated to Rust 1.70.
- Internal improvement: computed start positions for chunks are now stored in a `OnceLock` on the `BufList` rather than being recomputed each time a `Cursor` is constructed. In the case where there might be many `Cursor` instances on the same `&BufList`, this allows for start positions to be shared. Thanks to [inanna-malick](https://github.com/inanna-malick) for your first cntribution!

### Fixed

- Replaced obsolete `doc_auto_cfg` with `doc_cfg`, to fix Rust nightly builds with the `doc_cfg` flag enabled.

[rust-lang/rust#125404]: https://github.com/rust-lang/rust/pull/125404

## [1.0.3] - 2023-04-09

- Documentation improvements.

## [1.0.2] - 2023-04-09

### Added

- A new type `Cursor` which wraps a `BufList` or `&BufList`, and implements `Seek`, `Read` and `BufRead`.
- `BufList` implements `From<T>` for any `T` that can be converted to `Bytes`. This creates a
  `BufList` with a single chunk.
- `BufList::get_chunk` returns the chunk at the provided index.
- New optional features:
  - `tokio1`: makes `Cursor` implement tokio's `AsyncSeek`, `AsyncRead` and `AsyncBufRead`
  - `futures03`: makes `Cursor` implement futures's `AsyncSeek`, `AsyncRead` and `AsyncBufRead`.

## [1.0.1] - 2023-02-16

### Added

- Add recipes for converting a `BufList` into a `Stream` or a `TryStream`.

## [1.0.0] - 2023-01-06

### Added

- `BufList` now implements `Extend<B: Buf>`. This means you can now collect a stream of `Bytes`, or other `Buf` chunks, directly into a `BufList` via [`StreamExt::collect`](https://docs.rs/futures/latest/futures/stream/trait.StreamExt.html#method.collect).
  - Collecting a fallible stream is also possible, via [`TryStreamExt::try_collect`](https://docs.rs/futures/latest/futures/stream/trait.TryStreamExt.html#method.try_collect).

### Changed

- `push_chunk` now has a type parameter `B: Buf` rather than `impl Buf`.

## [0.1.3] - 2022-12-11

- Fix license indication in README: this crate is Apache-2.0 only, not MIT OR Apache-2.0.

## [0.1.2] - 2022-12-10

- Fix intradoc links.

## [0.1.1] - 2022-12-10

- Fixes to README.
- Add MSRV policy.

## [0.1.0] - 2022-12-10

- Initial release.

[1.1.2]: https://github.com/sunshowers-code/buf-list/releases/tag/1.1.2
[1.1.1]: https://github.com/sunshowers-code/buf-list/releases/tag/1.1.1
[1.1.0]: https://github.com/sunshowers-code/buf-list/releases/tag/1.1.0
[1.0.3]: https://github.com/sunshowers-code/buf-list/releases/tag/1.0.3
[1.0.2]: https://github.com/sunshowers-code/buf-list/releases/tag/1.0.2
[1.0.1]: https://github.com/sunshowers-code/buf-list/releases/tag/1.0.1
[1.0.0]: https://github.com/sunshowers-code/buf-list/releases/tag/1.0.0
[0.1.3]: https://github.com/sunshowers-code/buf-list/releases/tag/0.1.3
[0.1.2]: https://github.com/sunshowers-code/buf-list/releases/tag/0.1.2
[0.1.1]: https://github.com/sunshowers-code/buf-list/releases/tag/0.1.1
[0.1.0]: https://github.com/sunshowers-code/buf-list/releases/tag/0.1.0
