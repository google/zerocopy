#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod stdlib;

#[cfg(feature = "futures")]
#[cfg_attr(docsrs, doc(cfg(feature = "futures")))]
mod futures;

#[cfg(feature = "tokio")]
#[cfg_attr(docsrs, doc(cfg(feature = "tokio")))]
mod tokio;

/// The `Counter<D>` struct adds byte counting to any reader or writer.
pub struct Counter<D> {
    pub(crate) inner: D,
    /// Total bytes read from the `inner` reader.
    pub(crate) reader_bytes: usize,
    /// Total bytes written to the `inner` writer.
    pub(crate) writer_bytes: usize,
}

impl<D> Counter<D> {
    /// Creates a new `Counter<D>` with zero read/written bytes.
    #[inline]
    pub const fn new(inner: D) -> Self {
        Self::with_bytes(0, 0, inner)
    }

    /// Creates a new `Counter<D>` with the specified read/written bytes.
    #[inline]
    pub const fn with_bytes(reader_bytes: usize, writer_bytes: usize, inner: D) -> Self {
        Self {
            inner,
            reader_bytes,
            writer_bytes,
        }
    }

    /// Returns the sum of read and written bytes by the underlying reader/writer.
    #[inline]
    pub const fn total_bytes(&self) -> usize {
        self.reader_bytes + self.writer_bytes
    }

    /// Returns the total amount of read bytes by the underlying reader.
    #[inline]
    pub const fn reader_bytes(&self) -> usize {
        self.reader_bytes
    }

    /// Returns the total amount of written bytes by the underlying writer.
    #[inline]
    pub const fn writer_bytes(&self) -> usize {
        self.writer_bytes
    }

    /// Consumes `Counter<D>` returning the underlying reader/writer.
    #[inline]
    pub fn into_inner(self) -> D {
        self.inner
    }

    /// Gets a reference to the underlying reader/writer.
    #[inline]
    pub fn get_ref(&self) -> &D {
        &self.inner
    }

    /// Gets a mutable reference to the underlying reader/writer.
    #[inline]
    pub fn get_mut(&mut self) -> &mut D {
        &mut self.inner
    }
}

impl<D> From<D> for Counter<D> {
    #[inline]
    fn from(inner: D) -> Self {
        Self::new(inner)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inner() {
        let mut writer = Vec::<u8>::new();
        writer.push(8);
        assert_eq!(writer.len(), 1);

        let mut writer = Counter::new(writer);
        writer.get_mut().clear();
        assert_eq!(writer.get_ref().len(), 0);

        let writer = writer.into_inner();
        assert_eq!(writer.len(), 0);
    }

    #[test]
    fn from() {
        let _: Counter<_> = Vec::<u8>::new().into();
    }
}
