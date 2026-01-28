// Copyright (c) The buffer-unordered-weighted Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use futures_util::{stream::FusedStream, Stream};
use pin_project_lite::pin_project;
use std::{
    fmt,
    pin::Pin,
    task::{Context, Poll},
};

pin_project! {
    /// A variant on `Peekable` that only works on fused streams.
    ///
    /// The standard `Peekable` doesn't work on examples like `FuturesUnordered`, because the standard
    /// `Peekable` uses `Fuse<St>` internally, and `FuturesUnordered` can have new elements added to it.
    ///
    /// See [issue #2678](https://github.com/rust-lang/futures-rs/issues/2678) on the futures-rs
    /// repo for more information.
    pub(crate) struct PeekableFused<St: FusedStream> {
        #[pin]
        stream: St,
        peeked: Option<St::Item>,
    }
}

impl<St> fmt::Debug for PeekableFused<St>
where
    St: FusedStream + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PeekableFused")
            .field("stream", &self.stream)
            .field("peeked", &self.peeked.as_ref().map(|_| "..."))
            .finish()
    }
}

#[allow(dead_code)]
impl<St: FusedStream> PeekableFused<St> {
    pub(super) fn new(stream: St) -> Self {
        Self {
            stream,
            peeked: None,
        }
    }

    /// Acquires a reference to the underlying sink or stream that this combinator is
    /// pulling from.
    pub fn get_ref(&self) -> &St {
        &self.stream
    }

    /// Acquires a mutable reference to the underlying sink or stream that this
    /// combinator is pulling from.
    ///
    /// Note that care must be taken to avoid tampering with the state of the
    /// sink or stream which may otherwise confuse this combinator.
    pub fn get_mut(&mut self) -> &mut St {
        &mut self.stream
    }

    /// Acquires a pinned mutable reference to the underlying sink or stream that this
    /// combinator is pulling from.
    ///
    /// Note that care must be taken to avoid tampering with the state of the
    /// sink or stream which may otherwise confuse this combinator.
    pub fn get_pin_mut(self: Pin<&mut Self>) -> Pin<&mut St> {
        self.project().stream
    }

    /// Consumes this combinator, returning the underlying sink or stream.
    ///
    /// Note that this may discard intermediate state of this combinator, so
    /// care should be taken to avoid losing resources when this is called.
    pub fn into_inner(self) -> St {
        self.stream
    }

    /// Returns whether the combinator is done.
    pub fn is_done(&self) -> bool {
        self.stream.is_terminated()
    }

    // TODO: implement the rest of the API if necessary.

    /// Peek retrieves a reference to the next item in the stream.
    ///
    /// This method polls the underlying stream and return either a reference
    /// to the next item if the stream is ready or passes through any errors.
    pub fn poll_peek(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<&St::Item>> {
        let mut this = self.project();

        Poll::Ready(loop {
            if this.peeked.is_some() {
                break this.peeked.as_ref();
            } else if let Some(item) = futures_util::ready!(this.stream.as_mut().poll_next(cx)) {
                *this.peeked = Some(item);
            } else {
                break None;
            }
        })
    }
}

impl<St: FusedStream> Stream for PeekableFused<St> {
    type Item = St::Item;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.project();
        if let Some(item) = this.peeked.take() {
            return Poll::Ready(Some(item));
        }
        this.stream.poll_next(cx)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let peek_len = usize::from(self.peeked.is_some());
        let (lower, upper) = self.stream.size_hint();
        let lower = lower.saturating_add(peek_len);
        let upper = match upper {
            Some(x) => x.checked_add(peek_len),
            None => None,
        };
        (lower, upper)
    }
}

impl<St: FusedStream> FusedStream for PeekableFused<St> {
    fn is_terminated(&self) -> bool {
        self.peeked.is_none() && self.stream.is_terminated()
    }
}
