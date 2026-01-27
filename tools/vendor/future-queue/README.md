# future-queue

[![future-queue on crates.io](https://img.shields.io/crates/v/future-queue)](https://crates.io/crates/future-queue)
[![Documentation (latest release)](https://img.shields.io/badge/docs-latest-brightgreen.svg)](https://docs.rs/future-queue/)
[![Documentation (main)](https://img.shields.io/badge/docs-main-purple)](https://nextest-rs.github.io/future-queue/rustdoc/future_queue)
[![Changelog](https://img.shields.io/badge/changelog-latest-blue)](CHANGELOG.md)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](LICENSE-APACHE)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE-MIT)

`future_queue` provides ways to run several futures:

* concurrently
* in the order they're spawned
* with global limits
* and with an optional group specified for each future, with its own limits.

This crate is part of the [nextest organization](https://github.com/nextest-rs) on GitHub, and
is designed to serve the needs of [cargo-nextest](https://nexte.st).

## Motivation

Async programming in Rust often uses an adaptor called
[`buffer_unordered`](https://docs.rs/futures/latest/futures/stream/trait.StreamExt.html#method.buffer_unordered):
this adaptor takes a stream of futures[^1], and executes all the futures limited to a maximum
amount of concurrency.

* Futures are started in the order the stream returns them in.
* Once started, futures are polled simultaneously, and completed future outputs are returned in
  arbitrary order (hence the `unordered`).

Common use cases for `buffer_unordered` include:

* Sending network requests concurrently, but limiting the amount of concurrency to avoid
  overwhelming the remote server.
* Running tests with a tool like [cargo-nextest](https://nexte.st).

`buffer_unordered` works well for many use cases. However, one issue with it is that it treats
all futures as equally taxing: there's no way to say that some futures consume more resources
than others, or that some subsets of futures should be mutually excluded from others.

For nextest in particular, some tests can be much heavier than others, and fewer of those tests
should be run simultaneously. Also, some tests need to be mutually excluded from others, or
other concurrency limits placed on them.

[^1]: This adaptor takes a stream of futures for maximum generality. In practice this is often
    an *iterator* of futures, converted over using
    [`stream::iter`](https://docs.rs/futures/latest/futures/stream/fn.iter.html).

## About this crate

This crate provides two adaptors on streams.

### 1. The `future_queue` adaptor

The [`future_queue`](StreamExt::future_queue) adaptor can run several futures simultaneously,
limiting the concurrency to a maximum *weight*.

Rather than taking a stream of futures, this adaptor takes a stream of
`(usize, F)` pairs, where the `usize` indicates the weight of each future,
and `F` is `FnOnce(FutureQueueContext) -> impl Future`. This adaptor will
schedule and buffer futures to be run until queueing the next future will
exceed the maximum weight.

* The maximum weight is never exceeded while futures are being run.
* If the weight of an individual future is greater than the maximum weight, its weight will be
  set to the maximum weight.

Once all possible futures are scheduled, this adaptor will wait until some of the currently
executing futures complete, and the current weight of running futures drops below the maximum
weight, before scheduling new futures.

The weight of a future can be zero, in which case it doesn't count towards the maximum weight.

If all weights are 1, then `future_queue` is exactly the same as `buffer_unordered`.

#### Examples

```rust
use futures::{channel::oneshot, stream, StreamExt as _};
use future_queue::{StreamExt as _};

let (send_one, recv_one) = oneshot::channel();
let (send_two, recv_two) = oneshot::channel();

let stream_of_futures = stream::iter(
    vec![(1, recv_one), (2, recv_two)],
).map(|(weight, future)| {
    (weight, move |_cx| future)
});
let mut queue = stream_of_futures.future_queue(10);

send_two.send("hello")?;
assert_eq!(queue.next().await, Some(Ok("hello")));

send_one.send("world")?;
assert_eq!(queue.next().await, Some(Ok("world")));

assert_eq!(queue.next().await, None);
```

### 2. The `future_queue_grouped` adaptor

The [`future_queue_grouped`](StreamExt::future_queue_grouped) adaptor is like `future_queue`,
except it is possible to specify an optional *group* for each future. Each group has a maximum
weight, and a future will only be scheduled if both the maximum weight and the group weight
aren't exceeded.

The adaptor is as fair as possible under the given constraints: it will schedule futures in the
order they're returned by the stream, without doing any reordering based on weight. When a
future from a group completes, queued up futures in this group will be preferentially scheduled
before any other futures from the provided stream.

Like with [`future_queue`](StreamExt::future_queue):

* The maximum global and group weights is never exceeded while futures are being run.
* While accounting against global weights, if the weight of an individual future is greater than
  the maximum weight, its weight will be set to the maximum weight.
* *If a future belongs to a group:* While accounting against the group weight, if its weight is
  greater than the maximum group weight, its weight will be set to the maximum group weight.

#### Examples

```rust
use futures::{channel::oneshot, stream, StreamExt as _};
use future_queue::{FutureQueueContext, StreamExt as _};

let (send_one, recv_one) = oneshot::channel();
let (send_two, recv_two) = oneshot::channel();

let stream_of_futures = stream::iter(
    vec![
        (1, Some("group1"), recv_one),
        (2, None, recv_two),
    ],
).map(|(weight, group, future)| {
    (weight, group, move |_cx| future)
});
let mut queue = stream_of_futures.future_queue_grouped(10, [("group1", 5)]);

send_two.send("hello")?;
assert_eq!(queue.next().await, Some(Ok("hello")));

send_one.send("world")?;
assert_eq!(queue.next().await, Some(Ok("world")));

assert_eq!(queue.next().await, None);
```

## Minimum supported Rust version (MSRV)

The minimum supported Rust version is **Rust 1.70.** At any time, at least the last six months
of Rust stable releases are supported.

While this crate is a pre-release (0.x.x) it may have its MSRV bumped in a patch release. Once
this crate has reached 1.x, any MSRV bump will be accompanied with a new minor version.

## Notes

This crate used to be called `buffer-unordered-weighted`. It was renamed to `future-queue` to be
more descriptive about what the crate does rather than how it's implemented.

## Contributing

See the [CONTRIBUTING](CONTRIBUTING.md) file for how to help out.

## License

This project is available under the terms of either the [Apache 2.0 license](LICENSE-APACHE) or
the [MIT license](LICENSE-MIT).

The code is derived from [futures-rs](https://github.com/rust-lang/futures-rs), and is used under
the Apache 2.0 and MIT licenses.

<!--
README.md is generated from README.tpl by cargo readme. To regenerate, run from the repository root:

./scripts/regenerate-readmes.sh
-->
