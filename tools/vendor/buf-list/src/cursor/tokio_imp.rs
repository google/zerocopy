// Copyright (c) The buf-list Contributors
// SPDX-License-Identifier: Apache-2.0

use super::CursorData;
use crate::{BufList, Cursor};
use std::{
    io::{self, SeekFrom},
    pin::Pin,
    task::{Context, Poll},
};
use tokio::io::{AsyncBufRead, AsyncRead, AsyncSeek, ReadBuf};

impl<T: AsRef<BufList> + Unpin> AsyncSeek for Cursor<T> {
    fn start_seek(mut self: Pin<&mut Self>, pos: SeekFrom) -> io::Result<()> {
        io::Seek::seek(&mut *self, pos).map(drop)
    }

    fn poll_complete(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<u64>> {
        Poll::Ready(Ok(self.get_mut().position()))
    }
}

impl<T: AsRef<BufList> + Unpin> AsyncRead for Cursor<T> {
    fn poll_read(
        mut self: Pin<&mut Self>,
        _: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let this = &mut *self;
        this.data.tokio_poll_read_impl(this.inner.as_ref(), buf)
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

impl CursorData {
    fn tokio_poll_read_impl(
        &mut self,
        list: &BufList,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        // This is really similar to Self::read_impl, except it's written against the ReadBuf API.
        while buf.remaining() > 0 {
            let (chunk, chunk_pos) = match self.get_chunk_and_pos(list) {
                Some(value) => value,
                None => break,
            };
            // The number of bytes to copy is the smaller of the two:
            // - the length of the chunk - the position in it.
            // - the number of bytes remaining.
            let n_to_copy = (chunk.len() - chunk_pos).min(buf.remaining());
            let chunk_bytes = chunk.as_ref();

            let bytes_to_copy = &chunk_bytes[chunk_pos..(chunk_pos + n_to_copy)];
            buf.put_slice(bytes_to_copy);

            // Increment the position.
            self.pos += n_to_copy as u64;
            // If we've finished reading through the chunk, move to the next chunk.
            if n_to_copy == chunk.len() - chunk_pos {
                self.chunk += 1;
            }
        }

        Poll::Ready(Ok(()))
    }
}
