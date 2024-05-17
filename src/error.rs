//! Types related to error reporting.
//!
//! ## Single failure mode errors
//!
//! Generally speaking, zerocopy's conversions may fail for one of up to three reasons:
//! - [`AlignmentError`]: the conversion source was improperly aligned
//! - [`SizeError`]: the conversion source was of incorrect size
//! - [`ValidityError`]: the conversion source contained invalid data
//!
//! Methods that only have one failure mode, like [`Ref::unaligned_from_bytes`],
//! return that mode's corresponding error type directly.
//!
//! ## Compound errors
//!
//! Conversion methods that have either two or three possible failure modes
//! return one of these error types:
//! - [`CastError`]: the error type of reference conversions
//! - [`TryCastError`]: the error type of fallible reference conversions
//! - [`TryReadError`]: the error type of fallible read conversions
//!
//! ## Accessing the conversion source
//!
//! All error types provide an `into_src` method that converts the error into
//! the source value underlying the failed conversion.

use core::{convert::Infallible, fmt, marker::PhantomData, ops::Deref};

use crate::TryFromBytes;
#[cfg(doc)]
use crate::{FromBytes, Ref};

/// Zerocopy's generic error type.
///
/// Generally speaking, zerocopy's conversions may fail for one of up to three
/// reasons:
/// - [`AlignmentError`]: the conversion source was improperly aligned
/// - [`SizeError`]: the conversion source was of incorrect size
/// - [`ValidityError`]: the conversion source contained invalid data
///
/// However, not all conversions produce all errors. For instance,
/// [`FromBytes::ref_from_bytes`] may fail due to alignment or size issues, but
/// not validity issues. This generic error type captures these
/// (im)possibilities via parameterization: `A` is parameterized with
/// [`AlignmentError`], `S` is parameterized with [`SizeError`], and `V` is
/// parameterized with [`Infallible`].
///
/// Zerocopy never uses this type directly in its API. Rather, we provide three
/// pre-parameterized aliases:
/// - [`CastError`]: the error type of reference conversions
/// - [`TryCastError`]: the error type of fallible reference conversions
/// - [`TryReadError`]: the error type of fallible read conversions
#[derive(PartialEq, Eq)]
pub enum ConvertError<A, S, V> {
    /// The conversion source was improperly aligned.
    Alignment(A),
    /// The conversion source was of incorrect size.
    Size(S),
    /// The conversion source contained invalid data.
    Validity(V),
}

impl<A: fmt::Debug, S: fmt::Debug, V: fmt::Debug> fmt::Debug for ConvertError<A, S, V> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Alignment(e) => f.debug_tuple("Alignment").field(e).finish(),
            Self::Size(e) => f.debug_tuple("Size").field(e).finish(),
            Self::Validity(e) => f.debug_tuple("Validity").field(e).finish(),
        }
    }
}

/// Produces a human-readable error message.
impl<A: fmt::Display, S: fmt::Display, V: fmt::Display> fmt::Display for ConvertError<A, S, V> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Alignment(e) => e.fmt(f),
            Self::Size(e) => e.fmt(f),
            Self::Validity(e) => e.fmt(f),
        }
    }
}

/// The error emitted if the conversion source is improperly aligned.
#[derive(PartialEq, Eq)]
pub struct AlignmentError<Src, Dst: ?Sized> {
    /// The source value involved in the conversion.
    src: Src,
    /// The inner destination type inolved in the conversion.
    dst: PhantomData<Dst>,
}

impl<Src, Dst: ?Sized> AlignmentError<Src, Dst> {
    pub(crate) fn new(src: Src) -> Self {
        Self { src, dst: PhantomData }
    }

    /// Produces the source underlying the failed conversion.
    #[inline]
    pub fn into_src(self) -> Src {
        self.src
    }

    pub(crate) fn with_src<NewSrc>(self, new_src: NewSrc) -> AlignmentError<NewSrc, Dst> {
        AlignmentError { src: new_src, dst: PhantomData }
    }

    pub(crate) fn map_src<NewSrc>(self, f: impl Fn(Src) -> NewSrc) -> AlignmentError<NewSrc, Dst> {
        AlignmentError { src: f(self.src), dst: PhantomData }
    }

    pub(crate) fn into<S, V>(self) -> ConvertError<Self, S, V> {
        ConvertError::Alignment(self)
    }
}

impl<Src, Dst: ?Sized> fmt::Debug for AlignmentError<Src, Dst> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AlignmentError").finish()
    }
}

/// Produces a human-readable error message.
// The bounds on this impl are intentionally conservative, and can be relaxed
// either once a `?Sized` alignment accessor is stabilized, or by storing the
// alignment as a runtime value.
impl<Src, Dst> fmt::Display for AlignmentError<Src, Dst>
where
    Src: Deref,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        #[cfg_attr(__INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS, allow(lossy_provenance_casts))]
        #[allow(clippy::as_conversions)]
        let addr = self.src.deref() as *const _ as *const () as usize;
        let addr_align = 2usize.pow(addr.trailing_zeros());
        f.write_str("the conversion failed because the address of the source (a multiple of ")?;
        addr_align.fmt(f)?;
        f.write_str(") is not a multiple of the alignment (")?;
        core::mem::align_of::<Dst>().fmt(f)?;
        f.write_str(") of the destination type: ")?;
        f.write_str(core::any::type_name::<Dst>())?;
        Ok(())
    }
}

impl<Src, Dst, S, V> From<AlignmentError<Src, Dst>>
    for ConvertError<AlignmentError<Src, Dst>, S, V>
{
    #[inline]
    fn from(err: AlignmentError<Src, Dst>) -> Self {
        Self::Alignment(err)
    }
}

/// The error emitted if the conversion source is of incorrect size.
#[derive(PartialEq, Eq)]
pub struct SizeError<Src, Dst: ?Sized> {
    /// The source value involved in the conversion.
    src: Src,
    /// The inner destination type inolved in the conversion.
    dst: PhantomData<Dst>,
}

impl<Src, Dst: ?Sized> SizeError<Src, Dst> {
    pub(crate) fn new(src: Src) -> Self {
        Self { src, dst: PhantomData }
    }

    /// Produces the source underlying the failed conversion.
    #[inline]
    pub fn into_src(self) -> Src {
        self.src
    }

    /// Sets the source value associated with the conversion error.
    pub(crate) fn with_src<NewSrc>(self, new_src: NewSrc) -> SizeError<NewSrc, Dst> {
        SizeError { src: new_src, dst: PhantomData }
    }

    /// Maps the source value associated with the conversion error.
    pub(crate) fn map_src<NewSrc>(self, f: impl Fn(Src) -> NewSrc) -> SizeError<NewSrc, Dst> {
        SizeError { src: f(self.src), dst: PhantomData }
    }

    /// Sets the destination type associated with the conversion error.
    pub(crate) fn with_dst<NewDst: ?Sized>(self) -> SizeError<Src, NewDst> {
        SizeError { src: self.src, dst: PhantomData }
    }

    /// Converts the error into a general [`ConvertError`].
    pub(crate) fn into<A, V>(self) -> ConvertError<A, Self, V> {
        ConvertError::Size(self)
    }
}

impl<Src, Dst: ?Sized> fmt::Debug for SizeError<Src, Dst> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SizeError").finish()
    }
}

/// Produces a human-readable error message.
impl<Src, Dst: ?Sized> fmt::Display for SizeError<Src, Dst>
where
    Src: Deref,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("the conversion failed because the source was incorrectly sized to complete the conversion into the destination type: ")?;
        f.write_str(core::any::type_name::<Dst>())?;
        Ok(())
    }
}

impl<Src, Dst, A, V> From<SizeError<Src, Dst>> for ConvertError<A, SizeError<Src, Dst>, V> {
    #[inline]
    fn from(err: SizeError<Src, Dst>) -> Self {
        Self::Size(err)
    }
}

/// The error emitted if the conversion source contains invalid data.
#[derive(PartialEq, Eq)]
pub struct ValidityError<Src, Dst: ?Sized + TryFromBytes> {
    /// The source value involved in the conversion.
    pub(crate) src: Src,
    /// The inner destination type inolved in the conversion.
    dst: PhantomData<Dst>,
}

impl<Src, Dst: ?Sized + TryFromBytes> ValidityError<Src, Dst> {
    pub(crate) fn new(src: Src) -> Self {
        Self { src, dst: PhantomData }
    }

    /// Produces the source underlying the failed conversion.
    #[inline]
    pub fn into_src(self) -> Src {
        self.src
    }

    /// Maps the source value associated with the conversion error.
    pub(crate) fn map_src<NewSrc>(self, f: impl Fn(Src) -> NewSrc) -> ValidityError<NewSrc, Dst> {
        ValidityError { src: f(self.src), dst: PhantomData }
    }

    /// Converts the error into a general [`ConvertError`].
    pub(crate) fn into<A, S>(self) -> ConvertError<A, S, Self> {
        ConvertError::Validity(self)
    }
}

impl<Src, Dst: ?Sized + TryFromBytes> fmt::Debug for ValidityError<Src, Dst> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ValidityError").finish()
    }
}

/// Produces a human-readable error message.
impl<Src, Dst: ?Sized + TryFromBytes> fmt::Display for ValidityError<Src, Dst>
where
    Src: Deref,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("the conversion failed because the source bytes are not a valid value of the destination type: ")?;
        f.write_str(core::any::type_name::<Dst>())?;
        Ok(())
    }
}

impl<Src, Dst: ?Sized + TryFromBytes, A, S> From<ValidityError<Src, Dst>>
    for ConvertError<A, S, ValidityError<Src, Dst>>
{
    #[inline]
    fn from(err: ValidityError<Src, Dst>) -> Self {
        Self::Validity(err)
    }
}

/// The error type of reference conversions.
///
/// Reference conversions, like [`FromBytes::ref_from_bytes`] may emit
/// [alignment](AlignmentError) and [size](SizeError) errors.
// Bounds on generic parameters are not enforced in type aliases, but they do
// appear in rustdoc.
#[allow(type_alias_bounds)]
pub type CastError<Src, Dst: ?Sized> =
    ConvertError<AlignmentError<Src, Dst>, SizeError<Src, Dst>, Infallible>;

impl<Src, Dst: ?Sized> CastError<Src, Dst> {
    /// Produces the source underlying the failed conversion.
    #[inline]
    pub fn into_src(self) -> Src {
        match self {
            Self::Alignment(e) => e.src,
            Self::Size(e) => e.src,
            Self::Validity(i) => match i {},
        }
    }

    /// Sets the source value associated with the conversion error.
    pub(crate) fn with_src<NewSrc>(self, new_src: NewSrc) -> CastError<NewSrc, Dst> {
        match self {
            Self::Alignment(e) => CastError::Alignment(e.with_src(new_src)),
            Self::Size(e) => CastError::Size(e.with_src(new_src)),
            Self::Validity(i) => match i {},
        }
    }

    /// Maps the source value associated with the conversion error.
    pub(crate) fn map_src<NewSrc>(self, f: impl Fn(Src) -> NewSrc) -> CastError<NewSrc, Dst> {
        match self {
            Self::Alignment(e) => CastError::Alignment(e.map_src(f)),
            Self::Size(e) => CastError::Size(e.map_src(f)),
            Self::Validity(i) => match i {},
        }
    }

    /// Converts the error into a general [`ConvertError`].
    pub(crate) fn into(self) -> TryCastError<Src, Dst>
    where
        Dst: TryFromBytes,
    {
        match self {
            Self::Alignment(e) => TryCastError::Alignment(e),
            Self::Size(e) => TryCastError::Size(e),
            Self::Validity(i) => match i {},
        }
    }
}

/// The error type of fallible reference conversions.
///
/// Fallible reference conversions, like [`TryFromBytes::try_ref_from`] may emit
/// [alignment](AlignmentError), [size](SizeError), and
/// [validity](ValidityError) errors.
// Bounds on generic parameters are not enforced in type aliases, but they do
// appear in rustdoc.
#[allow(type_alias_bounds)]
pub type TryCastError<Src, Dst: ?Sized + TryFromBytes> =
    ConvertError<AlignmentError<Src, Dst>, SizeError<Src, Dst>, ValidityError<Src, Dst>>;

// TODO(#1139): Remove the `TryFromBytes` here and in other downstream locations
// (all the way to `ValidityError`) if we determine it's not necessary for rich
// validity errors.
impl<Src, Dst: ?Sized + TryFromBytes> TryCastError<Src, Dst> {
    /// Produces the source underlying the failed conversion.
    #[inline]
    pub fn into_src(self) -> Src {
        match self {
            Self::Alignment(e) => e.src,
            Self::Size(e) => e.src,
            Self::Validity(e) => e.src,
        }
    }
}

impl<Src, Dst: ?Sized + TryFromBytes> From<CastError<Src, Dst>> for TryCastError<Src, Dst> {
    #[inline]
    fn from(value: CastError<Src, Dst>) -> Self {
        match value {
            CastError::Alignment(e) => Self::Alignment(e),
            CastError::Size(e) => Self::Size(e),
            CastError::Validity(i) => match i {},
        }
    }
}

/// The error type of fallible read-conversions.
///
/// Fallible read-conversions, like [`TryFromBytes::try_read_from`] may emit
/// [size](SizeError) and [validity](ValidityError) errors, but not alignment errors.
// Bounds on generic parameters are not enforced in type aliases, but they do
// appear in rustdoc.
#[allow(type_alias_bounds)]
pub type TryReadError<Src, Dst: ?Sized + TryFromBytes> =
    ConvertError<Infallible, SizeError<Src, Dst>, ValidityError<Src, Dst>>;

impl<Src, Dst: ?Sized + TryFromBytes> TryReadError<Src, Dst> {
    /// Produces the source underlying the failed conversion.
    #[inline]
    pub fn into_src(self) -> Src {
        match self {
            Self::Alignment(i) => match i {},
            Self::Size(e) => e.src,
            Self::Validity(e) => e.src,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn alignment_display() {
        #[repr(C, align(128))]
        struct Aligned {
            bytes: [u8; 128],
        }

        let aligned = Aligned { bytes: [0; 128] };

        assert_eq!(
            AlignmentError::<_, elain::Align::<8>>::new(&aligned.bytes[1..]).to_string(),
            "the conversion failed because the address of the source (a multiple of 1) is not a multiple of the alignment (8) of the destination type: elain::Align<8>"
        );

        assert_eq!(
            AlignmentError::<_, elain::Align::<8>>::new(&aligned.bytes[2..]).to_string(),
            "the conversion failed because the address of the source (a multiple of 2) is not a multiple of the alignment (8) of the destination type: elain::Align<8>"
        );

        assert_eq!(
            AlignmentError::<_, elain::Align::<8>>::new(&aligned.bytes[3..]).to_string(),
            "the conversion failed because the address of the source (a multiple of 1) is not a multiple of the alignment (8) of the destination type: elain::Align<8>"
        );

        assert_eq!(
            AlignmentError::<_, elain::Align::<8>>::new(&aligned.bytes[4..]).to_string(),
            "the conversion failed because the address of the source (a multiple of 4) is not a multiple of the alignment (8) of the destination type: elain::Align<8>"
        );
    }

    #[test]
    fn size_display() {
        assert_eq!(
            SizeError::<_, [u8]>::new(&[0u8; 1][..]).to_string(),
            "the conversion failed because the source was incorrectly sized to complete the conversion into the destination type: [u8]"
        );
    }

    #[test]
    fn validity_display() {
        assert_eq!(
            ValidityError::<_, bool>::new(&[2u8; 1][..]).to_string(),
            "the conversion failed because the source bytes are not a valid value of the destination type: bool"
        );
    }
}
