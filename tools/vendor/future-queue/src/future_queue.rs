// Copyright (c) The future-queue Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    global_weight::GlobalWeight, peekable_fused::PeekableFused, slots::SlotReservations,
    FutureQueueContext,
};
use futures_util::{
    stream::{Fuse, FuturesUnordered},
    Future, Stream, StreamExt as _,
};
use pin_project_lite::pin_project;
use std::{
    fmt,
    pin::Pin,
    task::{Context, Poll},
};

pin_project! {
    /// Stream for the [`future_queue`](crate::StreamExt::future_queue) method.
    #[must_use = "streams do nothing unless polled"]
    pub struct FutureQueue<St>
    where
        St: Stream,
        St::Item: WeightedFuture,
     {
        #[pin]
        stream: PeekableFused<Fuse<St>>,
        in_progress_queue: FuturesUnordered<FutureWithWeight<<St::Item as WeightedFuture>::Future>>,
        slots: SlotReservations,
        global_weight: GlobalWeight,
    }
}

impl<St> fmt::Debug for FutureQueue<St>
where
    St: Stream + fmt::Debug,
    St::Item: WeightedFuture,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FutureQueue")
            .field("stream", &self.stream)
            .field("in_progress_queue", &self.in_progress_queue)
            .field("slots", &self.slots)
            .field("global_weight", &self.global_weight)
            .finish()
    }
}

impl<St> FutureQueue<St>
where
    St: Stream,
    St::Item: WeightedFuture,
{
    pub(crate) fn new(stream: St, max_weight: usize) -> Self {
        Self {
            stream: PeekableFused::new(stream.fuse()),
            in_progress_queue: FuturesUnordered::new(),
            slots: SlotReservations::with_capacity(max_weight),
            global_weight: GlobalWeight::new(max_weight),
        }
    }

    /// Sets a mode where extra internal verifications are performed.
    #[doc(hidden)]
    pub fn set_extra_verify(&mut self, verify: bool) {
        self.slots.set_check_reserved(verify);
    }

    /// Returns the maximum weight of futures allowed to be run by this adaptor.
    pub fn max_weight(&self) -> usize {
        self.global_weight.max()
    }

    /// Returns the currently running weight of futures.
    pub fn current_weight(&self) -> usize {
        self.global_weight.current()
    }

    /// Acquires a reference to the underlying sink or stream that this combinator is
    /// pulling from.
    pub fn get_ref(&self) -> &St {
        self.stream.get_ref().get_ref()
    }

    /// Acquires a mutable reference to the underlying sink or stream that this
    /// combinator is pulling from.
    ///
    /// Note that care must be taken to avoid tampering with the state of the
    /// sink or stream which may otherwise confuse this combinator.
    pub fn get_mut(&mut self) -> &mut St {
        self.stream.get_mut().get_mut()
    }

    /// Acquires a pinned mutable reference to the underlying sink or stream that this
    /// combinator is pulling from.
    ///
    /// Note that care must be taken to avoid tampering with the state of the
    /// sink or stream which may otherwise confuse this combinator.
    pub fn get_pin_mut(self: Pin<&mut Self>) -> core::pin::Pin<&mut St> {
        self.project().stream.get_pin_mut().get_pin_mut()
    }

    /// Consumes this combinator, returning the underlying sink or stream.
    ///
    /// Note that this may discard intermediate state of this combinator, so
    /// care should be taken to avoid losing resources when this is called.
    pub fn into_inner(self) -> St {
        self.stream.into_inner().into_inner()
    }
}

impl<St> Stream for FutureQueue<St>
where
    St: Stream,
    St::Item: WeightedFuture,
{
    type Item = <<St::Item as WeightedFuture>::Future as Future>::Output;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let mut this = self.project();

        // First up, try to spawn off as many futures as possible by filling up
        // our queue of futures.
        while let Poll::Ready(Some(weighted_future)) = this.stream.as_mut().poll_peek(cx) {
            if !this.global_weight.has_space_for(weighted_future.weight()) {
                // Global limits would be exceeded, break out of the loop. Consider this
                // item next time.
                break;
            }

            let (weight, future_fn) = match this.stream.as_mut().poll_next(cx) {
                Poll::Ready(Some(weighted_future)) => weighted_future.into_components(),
                _ => unreachable!("we just peeked at this item"),
            };
            this.global_weight.add_weight(weight);
            let global_slot = this.slots.reserve();

            let cx = FutureQueueContext {
                global_slot,
                group_slot: None,
            };
            let future = future_fn(cx);

            this.in_progress_queue
                .push(FutureWithWeight::new(weight, global_slot, future));
        }

        // Attempt to pull the next value from the in_progress_queue.
        match this.in_progress_queue.poll_next_unpin(cx) {
            Poll::Pending => return Poll::Pending,
            Poll::Ready(Some((weight, slot, output))) => {
                this.global_weight.sub_weight(weight);
                this.slots.release(slot);
                return Poll::Ready(Some(output));
            }
            Poll::Ready(None) => {}
        }

        // If more values are still coming from the stream, we're not done yet
        if this.stream.is_done() {
            Poll::Ready(None)
        } else {
            Poll::Pending
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let queue_len = self.in_progress_queue.len();
        let (lower, upper) = self.stream.size_hint();
        let lower = lower.saturating_add(queue_len);
        let upper = match upper {
            Some(x) => x.checked_add(queue_len),
            None => None,
        };
        (lower, upper)
    }
}

/// A trait for types which can be converted into a `Future` and a weight.
///
/// Provided in case it's necessary. This trait is only implemented for `(usize, impl Future)`.
pub trait WeightedFuture: private::Sealed {
    /// The function to obtain the future from
    type F: FnOnce(FutureQueueContext) -> Self::Future;

    /// The associated `Future` type.
    type Future: Future;

    /// The weight of the future.
    fn weight(&self) -> usize;

    /// Turns self into its components.
    fn into_components(self) -> (usize, Self::F);
}

mod private {
    pub trait Sealed {}
}

impl<F, Fut> private::Sealed for (usize, F)
where
    F: FnOnce(FutureQueueContext) -> Fut,
    Fut: Future,
{
}

impl<F, Fut> WeightedFuture for (usize, F)
where
    F: FnOnce(FutureQueueContext) -> Fut,
    Fut: Future,
{
    type F = F;
    type Future = Fut;

    #[inline]
    fn weight(&self) -> usize {
        self.0
    }

    #[inline]
    fn into_components(self) -> (usize, Self::F) {
        self
    }
}

pin_project! {
    #[must_use = "futures do nothing unless polled"]
    struct FutureWithWeight<Fut> {
        #[pin]
        future: Fut,
        weight: usize,
        slot: u64,
    }
}

impl<Fut> FutureWithWeight<Fut> {
    pub fn new(weight: usize, slot: u64, future: Fut) -> Self {
        Self {
            future,
            weight,
            slot,
        }
    }
}

impl<Fut> Future for FutureWithWeight<Fut>
where
    Fut: Future,
{
    type Output = (usize, u64, Fut::Output);
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.project();

        match this.future.poll(cx) {
            Poll::Pending => Poll::Pending,
            Poll::Ready(output) => Poll::Ready((*this.weight, *this.slot, output)),
        }
    }
}
