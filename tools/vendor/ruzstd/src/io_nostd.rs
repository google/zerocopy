//! Manual implementations of representations for `#![no_std]`

use alloc::boxed::Box;

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum ErrorKind {
    Interrupted,
    UnexpectedEof,
    WouldBlock,
    Other,
    WriteAllEof,
}

impl ErrorKind {
    fn as_str(&self) -> &'static str {
        use ErrorKind::*;
        match *self {
            Interrupted => "operation interrupted",
            UnexpectedEof => "unexpected end of file",
            WouldBlock => "operation would block",
            Other => "other error",
            WriteAllEof => "write_all hit EOF",
        }
    }
}

impl core::fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.as_str())
    }
}

pub struct Error {
    kind: ErrorKind,
    err: Option<Box<dyn core::fmt::Display + Send + Sync + 'static>>,
}

impl alloc::fmt::Debug for Error {
    fn fmt(&self, f: &mut alloc::fmt::Formatter<'_>) -> Result<(), alloc::fmt::Error> {
        let mut s = f.debug_struct("Error");
        s.field("kind", &self.kind);
        if let Some(err) = self.err.as_ref() {
            s.field("err", &alloc::format!("{err}"));
        }
        s.finish()
    }
}

impl Error {
    pub fn new(kind: ErrorKind, err: Box<dyn core::fmt::Display + Send + Sync + 'static>) -> Self {
        Self {
            kind,
            err: Some(err),
        }
    }

    pub fn from(kind: ErrorKind) -> Self {
        Self { kind, err: None }
    }

    pub fn kind(&self) -> ErrorKind {
        self.kind
    }

    pub fn is_interrupted(&self) -> bool {
        matches!(self.kind, ErrorKind::Interrupted)
    }

    pub fn get_ref(&self) -> Option<&(dyn core::fmt::Display + Send + Sync)> {
        self.err.as_ref().map(|e| e.as_ref())
    }

    pub fn into_inner(self) -> Option<Box<dyn core::fmt::Display + Send + Sync + 'static>> {
        self.err
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.kind.as_str())?;

        if let Some(ref e) = self.err {
            e.fmt(f)?;
        }

        Ok(())
    }
}

impl From<ErrorKind> for Error {
    fn from(value: ErrorKind) -> Self {
        Self::from(value)
    }
}

pub trait Read {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error>;

    fn read_exact(&mut self, mut buf: &mut [u8]) -> Result<(), Error> {
        while !buf.is_empty() {
            match self.read(buf) {
                Ok(0) => break,
                Ok(n) => {
                    let tmp = buf;
                    buf = &mut tmp[n..];
                }
                Err(ref e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        if !buf.is_empty() {
            Err(Error::from(ErrorKind::UnexpectedEof))
        } else {
            Ok(())
        }
    }

    fn read_to_end(&mut self, output: &mut alloc::vec::Vec<u8>) -> Result<(), Error> {
        let mut buf = [0u8; 1024 * 16];
        loop {
            let bytes = self.read(&mut buf)?;
            if bytes == 0 {
                break;
            }
            output.extend_from_slice(&buf[..bytes]);
        }
        Ok(())
    }

    fn take(self, limit: u64) -> Take<Self>
    where
        Self: Sized,
    {
        Take { inner: self, limit }
    }
}

impl Read for &[u8] {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error> {
        let size = core::cmp::min(self.len(), buf.len());
        let (to_copy, rest) = self.split_at(size);

        if size == 1 {
            buf[0] = to_copy[0];
        } else {
            buf[..size].copy_from_slice(to_copy);
        }

        *self = rest;
        Ok(size)
    }
}

impl<T> Read for &mut T
where
    T: Read,
{
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error> {
        (*self).read(buf)
    }
}

pub struct Take<R: Read> {
    inner: R,
    limit: u64,
}

impl<R: Read> Take<R> {
    pub fn limit(&self) -> u64 {
        self.limit
    }

    pub fn set_limit(&mut self, limit: u64) {
        self.limit = limit;
    }

    pub fn get_ref(&self) -> &R {
        &self.inner
    }

    pub fn get_mut(&mut self) -> &mut R {
        &mut self.inner
    }

    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R: Read> Read for Take<R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Error> {
        if self.limit == 0 {
            return Ok(0);
        }

        let at_most = (self.limit as usize).min(buf.len());
        let bytes = self.inner.read(&mut buf[..at_most])?;
        self.limit -= bytes as u64;
        Ok(bytes)
    }
}

pub trait Write {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error>;
    fn flush(&mut self) -> Result<(), Error>;
    fn write_all(&mut self, mut buf: &[u8]) -> Result<(), Error> {
        while !buf.is_empty() {
            match self.write(buf) {
                Ok(0) => {
                    return Err(Error::from(ErrorKind::WriteAllEof));
                }
                Ok(n) => buf = &buf[n..],
                Err(ref e) if e.is_interrupted() => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
}

impl<T> Write for &mut T
where
    T: Write,
{
    fn write(&mut self, buf: &[u8]) -> Result<usize, Error> {
        (*self).write(buf)
    }

    fn flush(&mut self) -> Result<(), Error> {
        (*self).flush()
    }
}

impl Write for &mut [u8] {
    #[inline]
    fn write(&mut self, data: &[u8]) -> Result<usize, Error> {
        let amt = core::cmp::min(data.len(), self.len());
        let (a, b) = core::mem::take(self).split_at_mut(amt);
        a.copy_from_slice(&data[..amt]);
        *self = b;
        Ok(amt)
    }

    fn flush(&mut self) -> Result<(), Error> {
        Ok(())
    }
}

impl Write for alloc::vec::Vec<u8> {
    #[inline]
    fn write(&mut self, data: &[u8]) -> Result<usize, Error> {
        self.extend_from_slice(data);
        Ok(data.len())
    }

    fn flush(&mut self) -> Result<(), Error> {
        Ok(())
    }
}
