use std::io::{Result, SeekFrom};
use std::pin::Pin;
use std::task::{Context, Poll};

use tokio::io::{AsyncBufRead, AsyncSeek, AsyncWrite};
use tokio::io::{AsyncRead, ReadBuf};

use crate::Counter;

impl<R: AsyncRead + Unpin> AsyncRead for Counter<R> {
    fn poll_read(
        self: Pin<&mut Self>,
        ctx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<Result<()>> {
        let counter = self.get_mut();

        let pin = Pin::new(&mut counter.inner);
        let bytes = buf.filled().len();
        let poll = pin.poll_read(ctx, buf);
        let bytes = buf.filled().len() - bytes;

        if matches!(poll, Poll::Ready(Ok(()))) {
            counter.reader_bytes += bytes;
        }

        poll
    }
}

impl<R: AsyncBufRead + Unpin> AsyncBufRead for Counter<R> {
    fn poll_fill_buf(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Result<&[u8]>> {
        let counter = self.get_mut();

        let pin = Pin::new(&mut counter.inner);
        pin.poll_fill_buf(ctx)
    }

    fn consume(self: Pin<&mut Self>, amt: usize) {
        let counter = self.get_mut();
        counter.reader_bytes += amt;

        let pin = Pin::new(&mut counter.inner);
        pin.consume(amt);
    }
}

impl<W: AsyncWrite + Unpin> AsyncWrite for Counter<W> {
    fn poll_write(self: Pin<&mut Self>, ctx: &mut Context<'_>, buf: &[u8]) -> Poll<Result<usize>> {
        let counter = self.get_mut();

        let pin = Pin::new(&mut counter.inner);
        let poll = pin.poll_write(ctx, buf);

        if let Poll::Ready(Ok(bytes)) = poll {
            counter.writer_bytes += bytes;
        }

        poll
    }

    fn poll_flush(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Result<()>> {
        let counter = self.get_mut();
        let pin = Pin::new(&mut counter.inner);
        pin.poll_flush(ctx)
    }

    fn poll_shutdown(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Result<()>> {
        let counter = self.get_mut();
        let pin = Pin::new(&mut counter.inner);
        pin.poll_shutdown(ctx)
    }
}

impl<D: AsyncSeek + Unpin> AsyncSeek for Counter<D> {
    fn start_seek(self: Pin<&mut Self>, position: SeekFrom) -> Result<()> {
        let counter = self.get_mut();
        let pin = Pin::new(&mut counter.inner);
        pin.start_seek(position)
    }

    fn poll_complete(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Result<u64>> {
        let counter = self.get_mut();
        let pin = Pin::new(&mut counter.inner);
        pin.poll_complete(ctx)
    }
}

#[cfg(test)]
mod tests {
    use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
    use tokio::io::{AsyncReadExt, BufReader, BufWriter};

    use super::*;

    #[tokio::test]
    async fn reader() -> Result<()> {
        let reader = "Hello World!".as_bytes();
        let mut reader = Counter::new(reader);

        let mut buf = Vec::new();
        let len = reader.read_to_end(&mut buf).await?;

        assert_eq!(len, reader.reader_bytes());
        assert_eq!(len, reader.total_bytes());

        Ok(())
    }

    #[tokio::test]
    async fn buf_reader() -> Result<()> {
        let reader = "Hello World!".as_bytes();
        let reader = BufReader::new(reader);
        let mut reader = Counter::new(reader);

        let mut buf = String::new();
        let len = reader.read_line(&mut buf).await?;

        assert_eq!(len, reader.reader_bytes());
        assert_eq!(len, reader.total_bytes());

        Ok(())
    }

    #[tokio::test]
    async fn writer() -> Result<()> {
        let writer = Vec::new();
        let writer = BufWriter::new(writer);
        let mut writer = Counter::new(writer);

        let buf = "Hello World!".as_bytes();
        let len = writer.write(buf).await?;
        writer.flush().await?;

        assert_eq!(len, writer.writer_bytes());
        assert_eq!(len, writer.total_bytes());

        Ok(())
    }
}
