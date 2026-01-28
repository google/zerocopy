#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]
#![forbid(unsafe_code)]
#![allow(unknown_lints)]
#![warn(absolute_paths_not_starting_with_crate)]
#![warn(elided_lifetimes_in_paths)]
#![warn(explicit_outlives_requirements)]
#![warn(meta_variable_misuse)]
#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(non_ascii_idents)]
#![warn(noop_method_call)]
#![warn(rust_2021_idioms)]
#![warn(single_use_lifetimes)]
#![warn(trivial_casts)]
#![warn(unreachable_pub)]
#![warn(unused_crate_dependencies)]
#![warn(unused_extern_crates)]
#![warn(unused_lifetimes)]
#![warn(unused_results)]
#![allow(clippy::enum_variant_names)]
#![doc = include_str!("../README.md")]

mod constants;
pub mod sign;
#[cfg(any(feature = "sign-zip", feature = "unsign-zip"))]
mod sign_unsign_zip;
pub mod unsign;
pub mod verify;
#[cfg(any(feature = "verify-tar", feature = "unsign-tar"))]
mod verify_unsign_tar;

use std::fmt;
use std::io::{self, Read};

#[doc(no_inline)]
pub use ed25519_dalek::{
    KEYPAIR_LENGTH, PUBLIC_KEY_LENGTH, SIGNATURE_LENGTH, Signature, SignatureError, SigningKey,
    VerifyingKey,
};

/// The unsigned hash of an input file
///
/// Use [`io::Write`] to update the prehash.
#[derive(Clone, Default)]
pub struct Prehash(ed25519_dalek::Sha512);

impl fmt::Debug for Prehash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Prehash").finish_non_exhaustive()
    }
}

impl Prehash {
    /// Instantiate a new prehash
    pub fn new() -> Self {
        Self(ed25519_dalek::Sha512::default())
    }

    /// Combination of [`Prehash::new()`] and [`io::Write`]
    pub fn calculate<I>(input: &mut I) -> io::Result<Self>
    where
        I: ?Sized + Read,
    {
        let mut this = Self::new();
        let _: u64 = io::copy(input, &mut this.0)?;
        Ok(this)
    }
}

impl io::Write for Prehash {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf)
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
    }
}

/// A collection of all errors this library can return
#[non_exhaustive]
#[derive(Debug, thiserror::Error)]
#[error(transparent)]
pub enum ZipsignError {
    /// An error returned by [`gather_signature_data()`][self::sign::gather_signature_data]
    GatherSignatureData(#[from] self::sign::GatherSignatureDataError),
    /// An error returned by [`read_signing_keys()`][self::sign::read_signing_keys]
    ReadSigningKeys(#[from] self::sign::ReadSigningKeysError),
    /// An error returned by [`copy_and_sign_tar()`][self::sign::copy_and_sign_tar]
    #[cfg(feature = "sign-tar")]
    #[cfg_attr(docsrs, doc(cfg(feature = "sign-tar")))]
    SignTar(#[from] self::sign::SignTarError),
    /// An error returned by [`copy_and_sign_zip()`][self::sign::copy_and_sign_zip]
    #[cfg(feature = "sign-zip")]
    #[cfg_attr(docsrs, doc(cfg(feature = "sign-zip")))]
    SignZip(#[from] self::sign::SignZipError),

    /// No matching key/signature pair found
    NoMatch(#[from] self::verify::NoMatch),
    /// An error returned by [`collect_keys()`][self::verify::collect_keys]
    CollectKeys(#[from] self::verify::CollectKeysError),
    /// An error returned by [`read_signatures()`][self::verify::read_signatures]
    ReadSignatures(#[from] self::verify::ReadSignaturesError),
    /// An error returned by [`verify_tar()`][self::verify::verify_tar]
    #[cfg(feature = "verify-tar")]
    #[cfg_attr(docsrs, doc(cfg(feature = "verify-tar")))]
    VerifyTar(#[from] self::verify::VerifyTarError),
    /// An error returned by [`verify_zip()`][self::verify::verify_zip]
    #[cfg(feature = "verify-zip")]
    #[cfg_attr(docsrs, doc(cfg(feature = "verify-zip")))]
    VerifyZip(#[from] self::verify::VerifyZipError),

    /// An error returned by [`copy_and_unsign_tar()`][self::unsign::copy_and_unsign_tar]
    #[cfg(feature = "unsign-tar")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unsign-tar")))]
    UnsignTar(#[from] self::unsign::UnsignTarError),
    /// An error returned by [`copy_and_unsign_zip()`][self::unsign::copy_and_unsign_zip]
    #[cfg(feature = "unsign-zip")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unsign-zip")))]
    UnsignZip(#[from] self::unsign::UnsignZipError),

    /// An I/O occurred
    Io(#[from] io::Error),
}

macro_rules! Error {
    (
        $(#[$meta:meta])+
        $vis:vis struct $outer:ident($inner:ident) { $(
            $(#[$field_meta:meta])+
            $field:ident $(( $(
                $(#[$ty_meta:meta])*
                $field_type:ty
            ),+ $(,)? ))?
        ),+ $(,)? }
    ) => {
        $(#[$meta])+
        $vis struct $outer(Box<$inner>);

        #[derive(Debug, thiserror::Error)]
        enum $inner { $(
            $(#[$field_meta])+
            $field $(( $(
                $(#[$ty_meta])* $field_type,
            )+ ))?,
        )+ }

        const _: () = {
            impl std::fmt::Debug for $outer {
                #[inline]
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    std::fmt::Debug::fmt(&*self.0, f)
                }
            }

            impl std::fmt::Display for $outer {
                #[inline]
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    std::fmt::Display::fmt(&*self.0, f)
                }
            }

            impl From<$inner> for $outer {
                #[inline]
                fn from(value: $inner) -> Self {
                    Self(Box::new(value))
                }
            }

            impl std::error::Error for $outer {
                #[inline]
                fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
                    self.0.source()
                }
            }
        };
    };
}

pub(crate) use Error;
