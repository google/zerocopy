// Copyright 2024 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

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
//!
//! ## Display formatting
//!
//! All error types provide a `Display` implementation that produces a
//! human-readable error message. When `debug_assertions` are enabled, these
//! error messages are verbose and may include potentially sensitive
//! information, including:
//!
//! - the names of the involved types
//! - the sizes of the involved types
//! - the addresses of the involved types
//! - the contents of the involved types
//!
//! When `debug_assertions` are disabled (as is default for `release` builds),
//! such potentially sensitive information is excluded.
//!
//! In the future, we may support manually configuring this behavior. If you are
//! interested in this feature, [let us know on GitHub][issue-1457] so we know
//! to prioritize it.
//!
//! [issue-1457]: https://github.com/google/zerocopy/issues/1457
//!
//! ## Validation order
//!
//! Our conversion methods typically check alignment, then size, then bit
//! validity. However, we do not guarantee that this is always the case, and
//! this behavior may change between releases.

use core::{
    convert::Infallible,
    fmt::{self, Debug, Write},
    ops::Deref,
};

use crate::{util::SendSyncPhantomData, KnownLayout, TryFromBytes};
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
///
/// The message differs between debug and release builds. When
/// `debug_assertions` are enabled, this message is verbose and includes
/// potentially sensitive information.
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

#[cfg(any(feature = "std", test))]
#[allow(clippy::std_instead_of_core)]
impl<A, S, V> std::error::Error for ConvertError<A, S, V>
where
    A: fmt::Display + fmt::Debug,
    S: fmt::Display + fmt::Debug,
    V: fmt::Display + fmt::Debug,
{
}

/// The error emitted if the conversion source is improperly aligned.
#[derive(PartialEq, Eq)]
pub struct AlignmentError<Src, Dst: ?Sized> {
    /// The source value involved in the conversion.
    src: Src,
    /// The inner destination type inolved in the conversion.
    dst: SendSyncPhantomData<Dst>,
}

impl<Src, Dst: ?Sized> AlignmentError<Src, Dst> {
    pub(crate) fn new(src: Src) -> Self {
        Self { src, dst: SendSyncPhantomData::default() }
    }

    /// Produces the source underlying the failed conversion.
    #[inline]
    pub fn into_src(self) -> Src {
        self.src
    }

    pub(crate) fn with_src<NewSrc>(self, new_src: NewSrc) -> AlignmentError<NewSrc, Dst> {
        AlignmentError { src: new_src, dst: SendSyncPhantomData::default() }
    }

    pub(crate) fn map_src<NewSrc>(self, f: impl Fn(Src) -> NewSrc) -> AlignmentError<NewSrc, Dst> {
        AlignmentError { src: f(self.src), dst: SendSyncPhantomData::default() }
    }

    pub(crate) fn into<S, V>(self) -> ConvertError<Self, S, V> {
        ConvertError::Alignment(self)
    }

    /// Format extra details for a verbose, human-readable error message.
    ///
    /// This formatting may include potentially sensitive information.
    fn display_verbose_extras(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        Src: Deref,
        Dst: KnownLayout,
    {
        #[allow(clippy::as_conversions)]
        let addr = self.src.deref() as *const _ as *const ();
        let addr_align = 2usize.pow((crate::util::AsAddress::addr(addr)).trailing_zeros());

        f.write_str("\n\nSource type: ")?;
        f.write_str(core::any::type_name::<Src>())?;

        f.write_str("\nSource address: ")?;
        addr.fmt(f)?;
        f.write_str(" (a multiple of ")?;
        addr_align.fmt(f)?;
        f.write_str(")")?;

        f.write_str("\nDestination type: ")?;
        f.write_str(core::any::type_name::<Dst>())?;

        f.write_str("\nDestination alignment: ")?;
        <Dst as KnownLayout>::LAYOUT.align.get().fmt(f)?;

        Ok(())
    }
}

impl<Src, Dst: ?Sized> fmt::Debug for AlignmentError<Src, Dst> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AlignmentError").finish()
    }
}

/// Produces a human-readable error message.
///
/// The message differs between debug and release builds. When
/// `debug_assertions` are enabled, this message is verbose and includes
/// potentially sensitive information.
impl<Src, Dst: ?Sized> fmt::Display for AlignmentError<Src, Dst>
where
    Src: Deref,
    Dst: KnownLayout,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("The conversion failed because the address of the source is not a multiple of the alignment of the destination type.")?;

        if cfg!(debug_assertions) {
            self.display_verbose_extras(f)
        } else {
            Ok(())
        }
    }
}

#[cfg(any(feature = "std", test))]
#[allow(clippy::std_instead_of_core)]
impl<Src, Dst: ?Sized> std::error::Error for AlignmentError<Src, Dst>
where
    Src: Deref,
    Dst: KnownLayout,
{
}

impl<Src, Dst: ?Sized, S, V> From<AlignmentError<Src, Dst>>
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
    dst: SendSyncPhantomData<Dst>,
}

impl<Src, Dst: ?Sized> SizeError<Src, Dst> {
    pub(crate) fn new(src: Src) -> Self {
        Self { src, dst: SendSyncPhantomData::default() }
    }

    /// Produces the source underlying the failed conversion.
    #[inline]
    pub fn into_src(self) -> Src {
        self.src
    }

    /// Sets the source value associated with the conversion error.
    pub(crate) fn with_src<NewSrc>(self, new_src: NewSrc) -> SizeError<NewSrc, Dst> {
        SizeError { src: new_src, dst: SendSyncPhantomData::default() }
    }

    /// Maps the source value associated with the conversion error.
    pub(crate) fn map_src<NewSrc>(self, f: impl Fn(Src) -> NewSrc) -> SizeError<NewSrc, Dst> {
        SizeError { src: f(self.src), dst: SendSyncPhantomData::default() }
    }

    /// Sets the destination type associated with the conversion error.
    pub(crate) fn with_dst<NewDst: ?Sized>(self) -> SizeError<Src, NewDst> {
        SizeError { src: self.src, dst: SendSyncPhantomData::default() }
    }

    /// Converts the error into a general [`ConvertError`].
    pub(crate) fn into<A, V>(self) -> ConvertError<A, Self, V> {
        ConvertError::Size(self)
    }

    /// Format extra details for a verbose, human-readable error message.
    ///
    /// This formatting may include potentially sensitive information.
    fn display_verbose_extras(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        Src: Deref,
        Dst: KnownLayout,
    {
        // include the source type
        f.write_str("\nSource type: ")?;
        f.write_str(core::any::type_name::<Src>())?;

        // include the source.deref() size
        let src_size = core::mem::size_of_val(&*self.src);
        f.write_str("\nSource size: ")?;
        src_size.fmt(f)?;
        f.write_str(" byte")?;
        if src_size != 1 {
            f.write_char('s')?;
        }

        // if `Dst` is `Sized`, include the `Dst` size
        if let crate::SizeInfo::Sized { size } = Dst::LAYOUT.size_info {
            f.write_str("\nDestination size: ")?;
            size.fmt(f)?;
            f.write_str(" byte")?;
            if size != 1 {
                f.write_char('s')?;
            }
        }

        // include the destination type
        f.write_str("\nDestination type: ")?;
        f.write_str(core::any::type_name::<Dst>())?;

        Ok(())
    }
}

impl<Src, Dst: ?Sized> fmt::Debug for SizeError<Src, Dst> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SizeError").finish()
    }
}

/// Produces a human-readable error message.
///
/// The message differs between debug and release builds. When
/// `debug_assertions` are enabled, this message is verbose and includes
/// potentially sensitive information.
impl<Src, Dst: ?Sized> fmt::Display for SizeError<Src, Dst>
where
    Src: Deref,
    Dst: KnownLayout,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("The conversion failed because the source was incorrectly sized to complete the conversion into the destination type.")?;
        if cfg!(debug_assertions) {
            f.write_str("\n")?;
            self.display_verbose_extras(f)?;
        }
        Ok(())
    }
}

#[cfg(any(feature = "std", test))]
#[allow(clippy::std_instead_of_core)]
impl<Src, Dst: ?Sized> std::error::Error for SizeError<Src, Dst>
where
    Src: Deref,
    Dst: KnownLayout,
{
}

impl<Src, Dst: ?Sized, A, V> From<SizeError<Src, Dst>> for ConvertError<A, SizeError<Src, Dst>, V> {
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
    dst: SendSyncPhantomData<Dst>,
}

impl<Src, Dst: ?Sized + TryFromBytes> ValidityError<Src, Dst> {
    pub(crate) fn new(src: Src) -> Self {
        Self { src, dst: SendSyncPhantomData::default() }
    }

    /// Produces the source underlying the failed conversion.
    #[inline]
    pub fn into_src(self) -> Src {
        self.src
    }

    /// Maps the source value associated with the conversion error.
    pub(crate) fn map_src<NewSrc>(self, f: impl Fn(Src) -> NewSrc) -> ValidityError<NewSrc, Dst> {
        ValidityError { src: f(self.src), dst: SendSyncPhantomData::default() }
    }

    /// Converts the error into a general [`ConvertError`].
    pub(crate) fn into<A, S>(self) -> ConvertError<A, S, Self> {
        ConvertError::Validity(self)
    }

    /// Format extra details for a verbose, human-readable error message.
    ///
    /// This formatting may include potentially sensitive information.
    fn display_verbose_extras(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result
    where
        Src: Deref,
        Dst: KnownLayout,
    {
        f.write_str("Destination type: ")?;
        f.write_str(core::any::type_name::<Dst>())?;
        Ok(())
    }
}

impl<Src, Dst: ?Sized + TryFromBytes> fmt::Debug for ValidityError<Src, Dst> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ValidityError").finish()
    }
}

/// Produces a human-readable error message.
///
/// The message differs between debug and release builds. When
/// `debug_assertions` are enabled, this message is verbose and includes
/// potentially sensitive information.
impl<Src, Dst: ?Sized> fmt::Display for ValidityError<Src, Dst>
where
    Src: Deref,
    Dst: KnownLayout + TryFromBytes,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("The conversion failed because the source bytes are not a valid value of the destination type.")?;
        if cfg!(debug_assertions) {
            f.write_str("\n\n")?;
            self.display_verbose_extras(f)?;
        }
        Ok(())
    }
}

#[cfg(any(feature = "std", test))]
#[allow(clippy::std_instead_of_core)]
impl<Src, Dst: ?Sized> std::error::Error for ValidityError<Src, Dst>
where
    Src: Deref,
    Dst: KnownLayout + TryFromBytes,
{
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
mod tests {
    use super::*;

    #[test]
    fn test_send_sync() {
        // Test that all error types are `Send + Sync` even if `Dst: !Send +
        // !Sync`.

        #[allow(dead_code)]
        fn is_send_sync<T: Send + Sync>(_t: T) {}

        #[allow(dead_code)]
        fn alignment_err_is_send_sync<Src: Send + Sync, Dst>(err: AlignmentError<Src, Dst>) {
            is_send_sync(err)
        }

        #[allow(dead_code)]
        fn size_err_is_send_sync<Src: Send + Sync, Dst>(err: SizeError<Src, Dst>) {
            is_send_sync(err)
        }

        #[allow(dead_code)]
        fn validity_err_is_send_sync<Src: Send + Sync, Dst: TryFromBytes>(
            err: ValidityError<Src, Dst>,
        ) {
            is_send_sync(err)
        }

        #[allow(dead_code)]
        fn convert_error_is_send_sync<Src: Send + Sync, Dst: TryFromBytes>(
            err: ConvertError<
                AlignmentError<Src, Dst>,
                SizeError<Src, Dst>,
                ValidityError<Src, Dst>,
            >,
        ) {
            is_send_sync(err)
        }
    }

    #[test]
    fn alignment_display() {
        #[repr(C, align(128))]
        struct Aligned {
            bytes: [u8; 128],
        }

        impl_known_layout!(elain::Align::<8>);

        let aligned = Aligned { bytes: [0; 128] };

        let bytes = &aligned.bytes[1..];
        let addr = crate::util::AsAddress::addr(bytes);
        assert_eq!(
            AlignmentError::<_, elain::Align::<8>>::new(bytes).to_string(),
            format!("The conversion failed because the address of the source is not a multiple of the alignment of the destination type.\n\
            \nSource type: &[u8]\
            \nSource address: 0x{:x} (a multiple of 1)\
            \nDestination type: elain::Align<8>\
            \nDestination alignment: 8", addr)
        );

        let bytes = &aligned.bytes[2..];
        let addr = crate::util::AsAddress::addr(bytes);
        assert_eq!(
            AlignmentError::<_, elain::Align::<8>>::new(bytes).to_string(),
            format!("The conversion failed because the address of the source is not a multiple of the alignment of the destination type.\n\
            \nSource type: &[u8]\
            \nSource address: 0x{:x} (a multiple of 2)\
            \nDestination type: elain::Align<8>\
            \nDestination alignment: 8", addr)
        );

        let bytes = &aligned.bytes[3..];
        let addr = crate::util::AsAddress::addr(bytes);
        assert_eq!(
            AlignmentError::<_, elain::Align::<8>>::new(bytes).to_string(),
            format!("The conversion failed because the address of the source is not a multiple of the alignment of the destination type.\n\
            \nSource type: &[u8]\
            \nSource address: 0x{:x} (a multiple of 1)\
            \nDestination type: elain::Align<8>\
            \nDestination alignment: 8", addr)
        );

        let bytes = &aligned.bytes[4..];
        let addr = crate::util::AsAddress::addr(bytes);
        assert_eq!(
            AlignmentError::<_, elain::Align::<8>>::new(bytes).to_string(),
            format!("The conversion failed because the address of the source is not a multiple of the alignment of the destination type.\n\
            \nSource type: &[u8]\
            \nSource address: 0x{:x} (a multiple of 4)\
            \nDestination type: elain::Align<8>\
            \nDestination alignment: 8", addr)
        );
    }

    #[test]
    fn size_display() {
        assert_eq!(
            SizeError::<_, [u8]>::new(&[0u8; 2][..]).to_string(),
            "The conversion failed because the source was incorrectly sized to complete the conversion into the destination type.\n\
            \nSource type: &[u8]\
            \nSource size: 2 bytes\
            \nDestination type: [u8]"
        );

        assert_eq!(
            SizeError::<_, [u8; 2]>::new(&[0u8; 1][..]).to_string(),
            "The conversion failed because the source was incorrectly sized to complete the conversion into the destination type.\n\
            \nSource type: &[u8]\
            \nSource size: 1 byte\
            \nDestination size: 2 bytes\
            \nDestination type: [u8; 2]"
        );
    }

    #[test]
    fn validity_display() {
        assert_eq!(
            ValidityError::<_, bool>::new(&[2u8; 1][..]).to_string(),
            "The conversion failed because the source bytes are not a valid value of the destination type.\n\
            \n\
            Destination type: bool"
        );
    }
}
