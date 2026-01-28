// Copyright (c) 2018 the linkerd2-proxy authors
// Copyright (c) The buf-list Contributors
// SPDX-License-Identifier: Apache-2.0

use bytes::{Buf, BufMut, Bytes, BytesMut};
use std::{
    collections::VecDeque,
    io::IoSlice,
    iter::{FromIterator, FusedIterator},
    sync::OnceLock,
};

/// Data composed of a list of [`Bytes`] chunks.
///
/// For more, see the [crate documentation](crate).
#[derive(Clone, Debug, Default)]
pub struct BufList {
    // Invariant: none of the bufs in this queue are zero-length.
    bufs: VecDeque<Bytes>,

    /// An index of chunks and their start positions. There's an additional index at the end, which
    /// is the length of the list (list.num_bytes()).
    start_pos: OnceLock<Box<[u64]>>,
}

impl BufList {
    /// Creates a new, empty, `BufList`.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub(crate) fn get_start_pos(&self) -> &[u64] {
        self.start_pos.get_or_init(|| {
            let mut start_pos = Vec::with_capacity(self.bufs.len() + 1);
            let mut next = 0u64;
            for chunk in self.bufs.iter() {
                start_pos.push(next);
                next += chunk.len() as u64;
            }
            // Add the length of the chunk at the end.
            start_pos.push(next);
            start_pos.into_boxed_slice()
        })
    }

    /// Creates a new, empty, `BufList` with the given capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            bufs: VecDeque::with_capacity(capacity),
            start_pos: OnceLock::new(),
        }
    }

    /// Returns the total number of chunks in this `BufList`.
    ///
    /// # Examples
    ///
    /// ```
    /// use buf_list::BufList;
    ///
    /// let buf_list = vec![&b"hello"[..], &b"world"[..]].into_iter().collect::<BufList>();
    /// assert_eq!(buf_list.num_chunks(), 2);
    /// ```
    #[inline]
    pub fn num_chunks(&self) -> usize {
        self.bufs.len()
    }

    /// Returns the total number of bytes across all chunks.
    ///
    /// # Examples
    ///
    /// ```
    /// use buf_list::BufList;
    ///
    /// let buf_list = vec![&b"hello"[..], &b"world"[..]].into_iter().collect::<BufList>();
    /// assert_eq!(buf_list.num_bytes(), 10);
    /// ```
    #[inline]
    pub fn num_bytes(&self) -> usize {
        self.remaining()
    }

    /// Provides a reference to the chunk at the given index.
    ///
    /// # Examples
    ///
    /// ```
    /// use buf_list::BufList;
    /// use bytes::Bytes;
    ///
    /// let buf_list = vec![&b"hello"[..], &b"world"[..]].into_iter().collect::<BufList>();
    /// assert_eq!(buf_list.get_chunk(1), Some(&Bytes::from(&b"world"[..])));
    /// ```
    #[inline]
    pub fn get_chunk(&self, index: usize) -> Option<&Bytes> {
        self.bufs.get(index)
    }

    /// Iterates over the chunks in this list.
    #[inline]
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            iter: self.bufs.iter(),
        }
    }

    /// Adds a new chunk to this list.
    ///
    /// If the provided [`Buf`] is zero-length, it will not be added to the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use buf_list::BufList;
    /// use bytes::{Buf, Bytes};
    ///
    /// let mut buf_list = BufList::new();
    ///
    /// // &'static [u8] implements Buf.
    /// buf_list.push_chunk(&b"hello"[..]);
    /// assert_eq!(buf_list.chunk(), &b"hello"[..]);
    ///
    /// // Bytes also implements Buf.
    /// buf_list.push_chunk(Bytes::from_static(&b"world"[..]));
    /// assert_eq!(buf_list.num_chunks(), 2);
    ///
    /// // A zero-length `Buf` will not be added to the list.
    /// buf_list.push_chunk(Bytes::new());
    /// assert_eq!(buf_list.num_chunks(), 2);
    /// ```
    pub fn push_chunk<B: Buf>(&mut self, mut data: B) -> Bytes {
        // mutable borrow acquired, invalidate the OnceLock
        self.start_pos = OnceLock::new();

        let len = data.remaining();
        // `data` is (almost) certainly a `Bytes`, so `copy_to_bytes` should
        // internally be a cheap refcount bump almost all of the time.
        // But, if it isn't, this will copy it to a `Bytes` that we can
        // now clone.
        let bytes = data.copy_to_bytes(len);

        // Buffer a clone. Don't push zero-length bufs to uphold the invariant.
        if len > 0 {
            self.bufs.push_back(bytes.clone());
        }

        // Return the bytes
        bytes
    }
}

impl<B: Buf> Extend<B> for BufList {
    fn extend<T: IntoIterator<Item = B>>(&mut self, iter: T) {
        // mutable borrow acquired, invalidate the OnceLock
        self.start_pos = OnceLock::new();

        for buf in iter.into_iter() {
            self.push_chunk(buf);
        }
    }
}

impl<B: Buf> FromIterator<B> for BufList {
    fn from_iter<T: IntoIterator<Item = B>>(iter: T) -> Self {
        let mut buf_list = BufList::new();
        for buf in iter.into_iter() {
            buf_list.push_chunk(buf);
        }
        buf_list
    }
}

impl IntoIterator for BufList {
    type Item = Bytes;
    type IntoIter = IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            iter: self.bufs.into_iter(),
        }
    }
}

impl<'a> IntoIterator for &'a BufList {
    type Item = &'a Bytes;
    type IntoIter = Iter<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl AsRef<BufList> for BufList {
    fn as_ref(&self) -> &BufList {
        self
    }
}

impl Buf for BufList {
    fn remaining(&self) -> usize {
        self.bufs.iter().map(Buf::remaining).sum()
    }

    fn chunk(&self) -> &[u8] {
        self.bufs.front().map(Buf::chunk).unwrap_or(&[])
    }

    fn chunks_vectored<'iovs>(&'iovs self, iovs: &mut [IoSlice<'iovs>]) -> usize {
        // Are there more than zero iovecs to write to?
        if iovs.is_empty() {
            return 0;
        }

        let to_fill = (iovs.len()).min(self.bufs.len());
        for (i, iov) in iovs.iter_mut().enumerate().take(to_fill) {
            *iov = IoSlice::new(&self.bufs[i]);
        }

        to_fill
    }

    fn advance(&mut self, mut amt: usize) {
        // mutable borrow acquired, invalidate the OnceLock
        self.start_pos = OnceLock::new();

        while amt > 0 {
            let rem = self.bufs[0].remaining();
            // If the amount to advance by is less than the first buffer in
            // the buffer list, advance that buffer's cursor by `amt`,
            // and we're done.
            if rem > amt {
                self.bufs[0].advance(amt);
                return;
            }

            // Otherwise, advance the first buffer to its end, and
            // continue.
            self.bufs[0].advance(rem);
            amt -= rem;

            self.bufs.pop_front();
        }
    }

    fn copy_to_bytes(&mut self, len: usize) -> Bytes {
        // mutable borrow acquired, invalidate the OnceLock
        self.start_pos = OnceLock::new();

        // If the length of the requested `Bytes` is <= the length of the front
        // buffer, we can just use its `copy_to_bytes` implementation (which is
        // just a reference count bump).
        match self.bufs.front_mut() {
            Some(first) if len <= first.remaining() => {
                let buf = first.copy_to_bytes(len);
                // If we consumed the first buffer, also advance our "cursor" by
                // popping it.
                if first.remaining() == 0 {
                    self.bufs.pop_front();
                }

                buf
            }
            _ => {
                assert!(
                    len <= self.remaining(),
                    "`len` ({}) greater than remaining ({})",
                    len,
                    self.remaining()
                );
                let mut buf = BytesMut::with_capacity(len);
                buf.put(self.take(len));
                buf.freeze()
            }
        }
    }
}

impl<T: Into<Bytes>> From<T> for BufList {
    fn from(value: T) -> Self {
        let mut buf_list = BufList::with_capacity(1);
        buf_list.push_chunk(value.into());
        buf_list
    }
}

/// An owned iterator over chunks in a [`BufList`].
///
/// Returned by the [`IntoIterator`] implementation for [`BufList`].
#[derive(Clone, Debug)]
pub struct IntoIter {
    iter: std::collections::vec_deque::IntoIter<Bytes>,
}

impl Iterator for IntoIter {
    type Item = Bytes;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl DoubleEndedIterator for IntoIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl ExactSizeIterator for IntoIter {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl FusedIterator for IntoIter {}

/// A borrowed iterator over chunks in a [`BufList`].
///
/// Returned by [`BufList::iter`], and by the [`IntoIterator`] implementation for `&'a BufList`.
#[derive(Clone, Debug)]
pub struct Iter<'a> {
    iter: std::collections::vec_deque::Iter<'a, Bytes>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Bytes;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    // These methods are implemented manually to forward to the underlying
    // iterator.

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    // fold has a special implementation, so forward it.
    #[inline]
    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.iter.fold(init, f)
    }

    // Can't implement try_fold as it uses `std::ops::Try` which isn't stable yet, as of Rust 1.67

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.iter.nth(n)
    }

    #[inline]
    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.iter.last()
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }

    #[inline]
    fn rfold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.iter.rfold(init, f)
    }

    // Can't implement try_rfold as it uses `std::ops::Try` which isn't stable yet, as of Rust 1.67.
}

impl<'a> ExactSizeIterator for Iter<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<'a> FusedIterator for Iter<'a> {}
