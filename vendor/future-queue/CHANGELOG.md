# Changelog

## [0.4.0] - 2025-02-12

### Added

- Added the ability to get global and group *slot numbers* for each future. Slot numbers are *unique* for as long as the future lives and are freed once the future is complete. Slot numbers are also *compact* because they start from 0, and the smallest possible number is assigned to them.

### Changed

- As a result of the ability to get slot numbers, the stream must now return a closure of `FnOnce(FutureQueueContext) -> impl Future`.

## [0.3.0] - 2023-03-18

### Changed

- Changed definitions of `future_queue` and `future_queue_grouped` such that weights can no longer be
  exceeded. This is easier to explain and enables certain additional use cases in nextest.

## [0.2.2] - 2022-12-27

### Added

- Added documentation link to Cargo.toml metadata.

## [0.2.1] - 2022-12-27

## Changed

- Internal change: switch to `FnvHashMap` for `future_queue_grouped`.

## [0.2.0] - 2022-12-27

## Added

- New adaptor `future_queue_grouped` is similar to `future_queue`, except it allows an additional *group* to be specified.

## Changed

- Crate renamed to `future_queue`.
- `buffer_unordered_weighted` renamed to `future_queue`.

## [0.1.2] - 2022-11-01

- Add repository link.

## [0.1.1] - 2022-10-29

- Documentation updates.

## [0.1.0] - 2022-10-28

- Initial release.

[0.4.0]: https://github.com/nextest-rs/future-queue/releases/tag/0.4.0
[0.3.0]: https://github.com/nextest-rs/future-queue/releases/tag/0.3.0
[0.2.2]: https://github.com/nextest-rs/future-queue/releases/tag/0.2.2
[0.2.1]: https://github.com/nextest-rs/future-queue/releases/tag/0.2.1
[0.2.0]: https://github.com/nextest-rs/future-queue/releases/tag/0.2.0
[0.1.2]: https://github.com/nextest-rs/future-queue/releases/tag/0.1.2
[0.1.1]: https://github.com/nextest-rs/future-queue/releases/tag/0.1.1
[0.1.0]: https://github.com/nextest-rs/future-queue/releases/tag/0.1.0
