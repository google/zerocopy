//! Types related to error reporting.

use core::{
    convert::Infallible,
    fmt::{self, Debug, Display},
    marker::PhantomData,
};

#[cfg(doc)]
use crate::{FromBytes, Ref, TryFromBytes};

#[derive(PartialEq, Eq, Copy, Clone)]
pub struct Error<Src, Dst: ?Sized, E> {
    pub(crate) src: Src,
    pub(crate) dst: PhantomData<Dst>,
    pub(crate) error: E,
}

impl<Src, Dst: ?Sized, E: Default> Error<Src, Dst, E> {
    pub(crate) fn new(src: Src) -> Error<Src, Dst, E> {
        Error::with_error(src, E::default())
    }
}

impl<Src, Dst: ?Sized, E> Error<Src, Dst, E> {
    pub(crate) fn with_error<EE: Into<E>>(src: Src, error: EE) -> Error<Src, Dst, E> {
        Error { src, dst: PhantomData, error: error.into() }
    }

    pub(crate) fn map_src<SS, F: FnOnce(Src) -> SS>(self, f: F) -> Error<SS, Dst, E> {
        let Error { src, dst, error } = self;
        Error { src: f(src), dst, error }
    }

    pub(crate) fn map_err<EE, F: FnOnce(E) -> EE>(self, f: F) -> Error<Src, Dst, EE> {
        let Error { src, dst, error } = self;
        Error { src, dst, error: f(error) }
    }
}

impl<Src, Dst: ?Sized, E: Debug> Debug for Error<Src, Dst, E> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Error").field("error", &self.error).finish()
    }
}

/// Produces a human-readable error message.
impl<Src, Dst: ?Sized, E: Display> Display for Error<Src, Dst, E> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "the conversion ({} -> {}) failed: {}",
            core::any::type_name::<Src>(),
            core::any::type_name::<Dst>(),
            self.error
        )
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum ConvertError<A, S, V> {
    /// The conversion source was improperly aligned.
    Alignment(A),
    /// The conversion source was of incorrect size.
    Size(S),
    /// The conversion source contained invalid data.
    Validity(V),
}

/// Produces a human-readable error message.
impl<A: Display, S: Display, V: Display> Display for ConvertError<A, S, V> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Alignment(e) => e.fmt(f),
            Self::Size(e) => e.fmt(f),
            Self::Validity(e) => e.fmt(f),
        }
    }
}

impl<S, V> From<Alignment> for ConvertError<Alignment, S, V> {
    fn from(e: Alignment) -> ConvertError<Alignment, S, V> {
        ConvertError::Alignment(e)
    }
}

impl<A, V> From<Size> for ConvertError<A, Size, V> {
    fn from(e: Size) -> ConvertError<A, Size, V> {
        ConvertError::Size(e)
    }
}

impl<A, S> From<Validity> for ConvertError<A, S, Validity> {
    fn from(e: Validity) -> ConvertError<A, S, Validity> {
        ConvertError::Validity(e)
    }
}

/// The error emitted if the conversion source is improperly aligned.
#[derive(PartialEq, Eq, Debug, Default, Copy, Clone)]
pub struct Alignment;

/// Produces a human-readable error message.
// The bounds on this impl are intentionally conservative, and can be relaxed
// either once a `?Sized` alignment accessor is stabilized, or by storing the
// alignment as a runtime value.
impl Display for Alignment {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(
            "the address of the source is not a multiple of the alignment of the destination type",
        )
    }
}

/// The error emitted if the conversion source is of incorrect size.
#[derive(PartialEq, Eq, Debug, Default, Copy, Clone)]
pub struct Size;

/// Produces a human-readable error message.
impl Display for Size {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(
            "the source is incorrectly sized to complete the conversion into the destination type",
        )
    }
}

/// The error emitted if the conversion source contains invalid data.
#[derive(PartialEq, Eq, Debug, Default, Copy, Clone)]
pub struct Validity;

/// Produces a human-readable error message.
impl Display for Validity {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("the source is not a valid value of the destination type")
    }
}

pub type AlignmentError<Src, Dst> = Error<Src, Dst, Alignment>;
pub type SizeError<Src, Dst> = Error<Src, Dst, Size>;
pub type ValidityError<Src, Dst> = Error<Src, Dst, Validity>;

pub type CastError<Src, Dst> = Error<Src, Dst, ConvertError<Alignment, Size, Infallible>>;

pub type TryCastError<Src, Dst> = Error<Src, Dst, ConvertError<Alignment, Size, Validity>>;

pub type TryReadError<Src, Dst> = Error<Src, Dst, ConvertError<Infallible, Size, Validity>>;
