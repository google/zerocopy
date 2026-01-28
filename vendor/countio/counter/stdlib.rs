use std::fmt;
use std::io::{BufRead, Read, Seek, Write};
use std::io::{Result, SeekFrom};

use crate::Counter;

impl<R: Read> Read for Counter<R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let bytes = self.inner.read(buf)?;
        self.reader_bytes += bytes;
        Ok(bytes)
    }
}

impl<R: BufRead> BufRead for Counter<R> {
    fn fill_buf(&mut self) -> Result<&[u8]> {
        self.inner.fill_buf()
    }

    fn consume(&mut self, amt: usize) {
        self.reader_bytes += amt;
        self.inner.consume(amt);
    }
}

impl<W: Write> Write for Counter<W> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        let bytes = self.inner.write(buf)?;
        self.writer_bytes += bytes;
        Ok(bytes)
    }

    #[inline]
    fn flush(&mut self) -> Result<()> {
        self.inner.flush()
    }
}

impl<D: Seek> Seek for Counter<D> {
    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        self.inner.seek(pos)
    }
}

impl<D: fmt::Debug> fmt::Debug for Counter<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Counter")
            .field("inner", &self.inner)
            .field("read", &self.reader_bytes)
            .field("written", &self.writer_bytes)
            .finish()
    }
}

#[cfg(test)]
mod test {
    use std::io::{BufReader, BufWriter};

    use super::*;

    #[test]
    fn reader() -> Result<()> {
        let reader = "Hello World!".as_bytes();
        let mut reader = Counter::new(reader);

        let mut buf = Vec::new();
        let len = reader.read_to_end(&mut buf)?;

        assert_eq!(len, reader.reader_bytes());
        assert_eq!(len, reader.total_bytes());

        Ok(())
    }

    #[test]
    fn buf_reader() -> Result<()> {
        let reader = "Hello World!".as_bytes();
        let reader = BufReader::new(reader);
        let mut reader = Counter::new(reader);

        let mut buf = String::new();
        let len = reader.read_line(&mut buf)?;

        assert_eq!(len, reader.reader_bytes());
        assert_eq!(len, reader.total_bytes());

        Ok(())
    }

    #[test]
    fn writer() -> Result<()> {
        let writer = Vec::new();
        let writer = BufWriter::new(writer);
        let mut writer = Counter::new(writer);

        let buf = "Hello World!".as_bytes();
        let len = writer.write(buf)?;
        writer.flush()?;

        assert_eq!(len, writer.writer_bytes());
        assert_eq!(len, writer.total_bytes());

        Ok(())
    }

    #[test]
    fn debug() {
        let writer = Vec::<u8>::new();
        let writer = Counter::new(writer);

        let fmt = "Counter { inner: [], read: 0, written: 0 }";
        assert_eq!(format!("{writer:?}"), fmt);
    }
}
