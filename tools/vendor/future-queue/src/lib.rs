// Copyright (c) The future-queue Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

#![warn(missing_docs)]

//! `future_queue` provides ways to run several futures:
//!
//! * concurrently
//! * in the order they're spawned
//! * with global limits
//! * and with an optional group specified for each future, with its own limits.
//!
//! This crate is part of the [nextest organization](https://github.com/nextest-rs) on GitHub, and
//! is designed to serve the needs of [cargo-nextest](https://nexte.st).
//!
//! # Motivation
//!
//! Async programming in Rust often uses an adaptor called
//! [`buffer_unordered`](https://docs.rs/futures/latest/futures/stream/trait.StreamExt.html#method.buffer_unordered):
//! this adaptor takes a stream of futures[^1], and executes all the futures limited to a maximum
//! amount of concurrency.
//!
//! * Futures are started in the order the stream returns them in.
//! * Once started, futures are polled simultaneously, and completed future outputs are returned in
//!   arbitrary order (hence the `unordered`).
//!
//! Common use cases for `buffer_unordered` include:
//!
//! * Sending network requests concurrently, but limiting the amount of concurrency to avoid
//!   overwhelming the remote server.
//! * Running tests with a tool like [cargo-nextest](https://nexte.st).
//!
//! `buffer_unordered` works well for many use cases. However, one issue with it is that it treats
//! all futures as equally taxing: there's no way to say that some futures consume more resources
//! than others, or that some subsets of futures should be mutually excluded from others.
//!
//! For nextest in particular, some tests can be much heavier than others, and fewer of those tests
//! should be run simultaneously. Also, some tests need to be mutually excluded from others, or
//! other concurrency limits placed on them.
//!
//! [^1]: This adaptor takes a stream of futures for maximum generality. In practice this is often
//!     an *iterator* of futures, converted over using
//!     [`stream::iter`](https://docs.rs/futures/latest/futures/stream/fn.iter.html).
//!
//! # About this crate
//!
//! This crate provides two adaptors on streams.
//!
//! ## 1. The `future_queue` adaptor
//!
//! The [`future_queue`](StreamExt::future_queue) adaptor can run several futures simultaneously,
//! limiting the concurrency to a maximum *weight*.
//!
//! Rather than taking a stream of futures, this adaptor takes a stream of
//! `(usize, F)` pairs, where the `usize` indicates the weight of each future,
//! and `F` is `FnOnce(FutureQueueContext) -> impl Future`. This adaptor will
//! schedule and buffer futures to be run until queueing the next future will
//! exceed the maximum weight.
//!
//! * The maximum weight is never exceeded while futures are being run.
//! * If the weight of an individual future is greater than the maximum weight, its weight will be
//!   set to the maximum weight.
//!
//! Once all possible futures are scheduled, this adaptor will wait until some of the currently
//! executing futures complete, and the current weight of running futures drops below the maximum
//! weight, before scheduling new futures.
//!
//! The weight of a future can be zero, in which case it doesn't count towards the maximum weight.
//!
//! If all weights are 1, then `future_queue` is exactly the same as `buffer_unordered`.
//!
//! ### Examples
//!
//! ```rust
//! # futures::executor::block_on(async {
//! use futures::{channel::oneshot, stream, StreamExt as _};
//! use future_queue::{StreamExt as _};
//!
//! let (send_one, recv_one) = oneshot::channel();
//! let (send_two, recv_two) = oneshot::channel();
//!
//! let stream_of_futures = stream::iter(
//!     vec![(1, recv_one), (2, recv_two)],
//! ).map(|(weight, future)| {
//!     (weight, move |_cx| future)
//! });
//! let mut queue = stream_of_futures.future_queue(10);
//!
//! send_two.send("hello")?;
//! assert_eq!(queue.next().await, Some(Ok("hello")));
//!
//! send_one.send("world")?;
//! assert_eq!(queue.next().await, Some(Ok("world")));
//!
//! assert_eq!(queue.next().await, None);
//! # Ok::<(), &'static str>(()) }).unwrap();
//! ```
//!
//! ## 2. The `future_queue_grouped` adaptor
//!
//! The [`future_queue_grouped`](StreamExt::future_queue_grouped) adaptor is like `future_queue`,
//! except it is possible to specify an optional *group* for each future. Each group has a maximum
//! weight, and a future will only be scheduled if both the maximum weight and the group weight
//! aren't exceeded.
//!
//! The adaptor is as fair as possible under the given constraints: it will schedule futures in the
//! order they're returned by the stream, without doing any reordering based on weight. When a
//! future from a group completes, queued up futures in this group will be preferentially scheduled
//! before any other futures from the provided stream.
//!
//! Like with [`future_queue`](StreamExt::future_queue):
//!
//! * The maximum global and group weights is never exceeded while futures are being run.
//! * While accounting against global weights, if the weight of an individual future is greater than
//!   the maximum weight, its weight will be set to the maximum weight.
//! * *If a future belongs to a group:* While accounting against the group weight, if its weight is
//!   greater than the maximum group weight, its weight will be set to the maximum group weight.
//!
//! ### Examples
//!
//! ```rust
//! # futures::executor::block_on(async {
//! use futures::{channel::oneshot, stream, StreamExt as _};
//! use future_queue::{FutureQueueContext, StreamExt as _};
//!
//! let (send_one, recv_one) = oneshot::channel();
//! let (send_two, recv_two) = oneshot::channel();
//!
//! let stream_of_futures = stream::iter(
//!     vec![
//!         (1, Some("group1"), recv_one),
//!         (2, None, recv_two),
//!     ],
//! ).map(|(weight, group, future)| {
//!     (weight, group, move |_cx| future)
//! });
//! let mut queue = stream_of_futures.future_queue_grouped(10, [("group1", 5)]);
//!
//! send_two.send("hello")?;
//! assert_eq!(queue.next().await, Some(Ok("hello")));
//!
//! send_one.send("world")?;
//! assert_eq!(queue.next().await, Some(Ok("world")));
//!
//! assert_eq!(queue.next().await, None);
//! # Ok::<(), &'static str>(()) }).unwrap();
//! ```
//!
//! # Minimum supported Rust version (MSRV)
//!
//! The minimum supported Rust version is **Rust 1.70.** At any time, at least the last six months
//! of Rust stable releases are supported.
//!
//! While this crate is a pre-release (0.x.x) it may have its MSRV bumped in a patch release. Once
//! this crate has reached 1.x, any MSRV bump will be accompanied with a new minor version.
//!
//! # Notes
//!
//! This crate used to be called `buffer-unordered-weighted`. It was renamed to `future-queue` to be
//! more descriptive about what the crate does rather than how it's implemented.

mod future_queue;
mod future_queue_grouped;
mod global_weight;
mod peekable_fused;
mod slots;

pub use crate::future_queue::FutureQueue;
pub use future_queue_grouped::FutureQueueGrouped;

/// Traits to aid in type definitions.
///
/// These traits are normally not required by end-user code, but may be necessary for some generic
/// code.
pub mod traits {
    pub use crate::{future_queue::WeightedFuture, future_queue_grouped::GroupedWeightedFuture};
}

use futures_util::{Future, Stream};
use std::{borrow::Borrow, hash::Hash};

impl<T: ?Sized> StreamExt for T where T: Stream {}

/// An extension trait for `Stream`s that provides
/// [`future_queue`](StreamExt::future_queue).
pub trait StreamExt: Stream {
    /// An adaptor for creating a queue of pending futures (unordered), where each future has a
    /// different weight.
    ///
    /// This stream must return values of type `(usize, impl Future)`, where the `usize` indicates
    /// the weight of each future. This adaptor will buffer futures up to weight `max_weight`, and
    /// then return the outputs in the order in which they complete.
    ///
    /// * The maximum weight is never exceeded while futures are being run.
    /// * If the weight of an individual future is greater than the maximum weight, its weight will
    ///   be set to the maximum weight.
    ///
    /// The adaptor will schedule futures in the order they're returned by the stream, without doing
    /// any reordering based on weight.
    ///
    /// The weight of a future can be zero, in which case it will not count towards the total weight.
    ///
    /// The returned stream will be a stream of each future's output.
    ///
    /// # Examples
    ///
    /// See [the crate documentation](crate#examples) for an example.
    fn future_queue<F, Fut>(self, max_weight: usize) -> FutureQueue<Self>
    where
        Self: Sized + Stream<Item = (usize, F)>,
        F: FnOnce(FutureQueueContext) -> Fut,
        Fut: Future,
    {
        assert_stream::<Fut::Output, _>(FutureQueue::new(self, max_weight))
    }

    /// An adaptor for creating a queue of pending futures, where each future has a different weight
    /// and optional group.
    ///
    /// This method accepts a maximum global weight, as well as a set of *groups* of type `K`. Each
    /// group has a defined maximum weight. This stream must return values of type `(usize,
    /// Option<Q>, F)`, where `K` is `Borrow<Q>`, and `F` is `FnOnce(FutureQueueContext) -> impl Future)`.
    ///
    /// This adapter will buffer futures up to weight `max_weight`. If the optional group is
    /// specified for a future, it will also check that the weight of futures in that group does not
    /// exceed the specified limit. Any futures that exceed the group's weight limit will be queued
    /// up, but not scheduled until the weight of futures in that group falls below the limit.
    ///
    /// Like with [`future_queue`](Self::future_queue):
    ///
    /// * The maximum global and group weights is never exceeded while futures are being run.
    /// * While accounting against global weights, if the weight of an individual future is greater
    ///   than the maximum weight, its weight will be set to the maximum weight.
    /// * *If a future belongs to a group:* While accounting against the group weight, if its weight
    ///   is greater than the maximum group weight, its weight will be set to the maximum group
    ///   weight.
    ///
    /// The adaptor is as fair as possible under the given constraints: it will schedule futures in
    /// the order they're returned by the stream, without doing any reordering based on weight. When
    /// a future from a group completes, queued up futures in this group will be preferentially
    /// scheduled before any other futures from the provided stream.
    ///
    /// The weight of a future can be zero, in which case it will not count towards the total weight.
    ///
    /// The returned stream will be a stream of each future's output.
    ///
    /// # Panics
    ///
    /// The stream panics if the optional group provided by a stream element isn't in the set of
    /// known groups.
    fn future_queue_grouped<F, Fut, I, K, Q>(
        self,
        max_global_weight: usize,
        groups: I,
    ) -> FutureQueueGrouped<Self, K>
    where
        I: IntoIterator<Item = (K, usize)>,
        K: Eq + Hash + Borrow<Q> + std::fmt::Debug,
        Q: Eq + Hash + std::fmt::Debug,
        Self: Sized + Stream<Item = (usize, Option<Q>, F)>,
        F: FnOnce(FutureQueueContext) -> Fut,
        Fut: Future,
    {
        assert_stream::<Fut::Output, _>(FutureQueueGrouped::new(self, max_global_weight, groups))
    }
}

/// Context for a function in a [`FutureQueue`] or [`FutureQueueGrouped`].
#[derive(Clone, Debug)]
pub struct FutureQueueContext {
    global_slot: u64,
    group_slot: Option<u64>,
}

impl FutureQueueContext {
    /// Returns a global slot number: an integer that is unique for the lifetime
    /// of the future, within the context of the [`FutureQueue`] or
    /// [`FutureQueueGrouped`] it is running in.
    ///
    /// The slot number is *compact*: it starts from 0, and is always the
    /// smallest possible number that could be assigned to the future at the
    /// moment the function is called.
    #[inline]
    pub fn global_slot(&self) -> u64 {
        self.global_slot
    }

    /// Returns a group slot number: an integer that is unique for the lifetime
    /// of the future within a group.
    ///
    /// The slot number is *compact*: it starts from 0, and is always the
    /// smallest possible number that could be assigned to the future at the
    /// moment the function is called.
    ///
    /// Only set in case [`FutureQueueGrouped`] is used, and the future is part
    /// of a group.
    #[inline]
    pub fn group_slot(&self) -> Option<u64> {
        self.group_slot
    }
}

pub(crate) fn assert_stream<T, S>(stream: S) -> S
where
    S: Stream<Item = T>,
{
    stream
}
