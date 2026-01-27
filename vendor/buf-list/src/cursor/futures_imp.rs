// Copyright (c) The buf-list Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{BufList, Cursor};
use futures_io_03::{AsyncBufRead, AsyncRead, AsyncSeek};
use std::{
    io::{self, IoSliceMut, SeekFrom},
    pin::Pin,
    task::{Context, Poll},
};

impl<T: AsRef<BufList> + Unpin> AsyncSeek for Cursor<T> {
    fn poll_seek(
        mut self: Pin<&mut Self>,
        _: &mut Context<'_>,
        pos: SeekFrom,
    ) -> Poll<io::Result<u64>> {
        Poll::Ready(io::Seek::seek(&mut *self, pos))
    }
}

impl<T: AsRef<BufList> + Unpin> AsyncRead for Cursor<T> {
    fn poll_read(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        buf: &mut [u8],
    ) -> Poll<io::Result<usize>> {
        Poll::Ready(io::Read::read(&mut *self, buf))
    }

    fn poll_read_vectored(
        mut self: Pin<&mut Self>,
        _: &mut Context<'_>,
        bufs: &mut [IoSliceMut<'_>],
    ) -> Poll<io::Result<usize>> {
        Poll::Ready(io::Read::read_vectored(&mut *self, bufs))
    }
}

impl<T: AsRef<BufList> + Unpin> AsyncBufRead for Cursor<T> {
    fn poll_fill_buf(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<&[u8]>> {
        Poll::Ready(io::BufRead::fill_buf(self.get_mut()))
    }

    fn consume(mut self: Pin<&mut Self>, amt: usize) {
        io::BufRead::consume(&mut *self, amt)
    }
}
