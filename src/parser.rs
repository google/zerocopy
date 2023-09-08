//! Provides a way to easily decode types from a `&[u8]`.

use crate::{FromBytes, Ref, Unaligned};
use core::mem::size_of;

/// Parses values and types
#[derive(Debug, Clone)]
pub struct Parser<'a> {
    /// The bytes that have not yet been decoded.
    rest: &'a [u8],
}

/// This type is returned by Parser methods.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct ParserError;

impl core::fmt::Display for ParserError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Could not parse item from parser buffer")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParserError {}

impl<'a> Parser<'a> {
    /// Creates a new one
    pub fn new(rest: &'a [u8]) -> Self {
        Self { rest }
    }

    /// Extracts the byte slice
    pub fn into_rest(self) -> &'a [u8] {
        self.rest
    }

    /// Gets a reference to the bytes that have not yet been decoded.
    #[inline(always)]
    pub fn rest(&self) -> &'a [u8] {
        self.rest
    }

    /// Returns `true` if there are no more bytes to decode.
    pub fn is_empty(&self) -> bool {
        self.rest.is_empty()
    }

    /// Gets a reference to a value at the start of the bytes and advances the decode pointer to
    /// after the value.
    #[inline(always)]
    pub fn get_ref<T>(&mut self) -> Result<&'a T, ParserError>
    where
        T: FromBytes + Unaligned,
    {
        if let Some((prefix, rest)) = Ref::<&[u8], T>::new_unaligned_from_prefix(self.rest) {
            self.rest = rest;
            Ok(prefix.into_ref())
        } else {
            Err(ParserError)
        }
    }

    /// Copies a value from the head of the buffer.
    ///
    /// `T` does not need to be `Unaligned`.
    #[inline(always)]
    pub fn copy<T>(&mut self) -> Result<T, ParserError>
    where
        T: FromBytes,
    {
        if let Some(value) = T::read_from_prefix(self.rest) {
            self.rest = &self.rest[size_of::<T>()..];
            Ok(value)
        } else {
            Err(ParserError)
        }
    }

    /// Parses a slice of items
    #[inline(always)]
    pub fn slice<T>(&mut self, len: usize) -> Result<&'a [u8], ParserError> {
        if let Some((prefix, rest)) = Ref::new_slice_unaligned_from_prefix(self.rest, len) {
            self.rest = rest;
            Ok(prefix.into_slice())
        } else {
            Err(ParserError)
        }
    }

    /// Parses the most whole items
    #[inline(always)]
    pub fn maximal_slice<T>(&mut self) -> Result<&'a [u8], ParserError> {
        let len = self.rest.len() / size_of::<T>();
        if let Some((prefix, rest)) = Ref::new_slice_unaligned_from_prefix(self.rest, len) {
            self.rest = rest;
            Ok(prefix.into_slice())
        } else {
            Err(ParserError)
        }
    }

    /// Parses a single item
    #[inline(always)]
    pub fn bytes(&mut self, len: usize) -> Result<&'a [u8], ParserError> {
        if len <= self.rest.len() {
            let (lo, hi) = self.rest.split_at(len);
            self.rest = hi;
            Ok(lo)
        } else {
            Err(ParserError)
        }
    }

    /// Parses a single item
    #[inline(always)]
    pub fn bytes_array<const N: usize>(&mut self) -> Result<&'a [u8; N], ParserError> {
        if N <= self.rest.len() {
            let (lo, hi) = self.rest.split_at(N);
            self.rest = hi;
            Ok(lo.try_into().unwrap())
        } else {
            Err(ParserError)
        }
    }

    /// Parses a single item
    #[inline(always)]
    pub fn u8(&mut self) -> Result<u8, ParserError> {
        if !self.rest.is_empty() {
            let b = self.rest[0];
            self.rest = &self.rest[1..];
            Ok(b)
        } else {
            Err(ParserError)
        }
    }

    /// Parses a single NUL-terminated sequence, such as a string.
    #[inline(always)]
    pub fn strz_raw(&mut self) -> Result<&'a [u8], ParserError> {
        if let Some(i) = self.rest.iter().position(|&b| b == 0) {
            let s = &self.rest[..i];
            self.rest = &self.rest[i + 1..];
            Ok(s)
        } else {
            Err(ParserError)
        }
    }

    /// Parses a single NUL-terminated UTF-8 string.
    #[inline(always)]
    pub fn strz(&mut self) -> Result<&'a str, ParserError> {
        if let Ok(s) = core::str::from_utf8(self.strz_raw()?) {
            Ok(s)
        } else {
            Err(ParserError)
        }
    }
}

macro_rules! parser_ints {
    (
        $(
            $t:ty, $func_name:ident, $from_xx_bytes:ident ;
        )*
    ) => {
        impl<'a> Parser<'a> {
            $(
                /// Parses a single item
                #[inline(always)]
                pub fn $func_name(&mut self) -> Result<$t, ParserError> {
                    Ok(<$t>::$from_xx_bytes(*self.bytes_array()?))
                }
            )*
        }
    }
}

parser_ints! {
    u16, u16_le, from_le_bytes;
    u32, u32_le, from_le_bytes;
    u64, u64_le, from_le_bytes;
    u128, u128_le, from_le_bytes;

    i16, i16_le, from_le_bytes;
    i32, i32_le, from_le_bytes;
    i64, i64_le, from_le_bytes;
    i128, i128_le, from_le_bytes;

    u16, u16_be, from_be_bytes;
    u32, u32_be, from_be_bytes;
    u64, u64_be, from_be_bytes;
    u128, u128_be, from_be_bytes;

    i16, i16_be, from_be_bytes;
    i32, i32_be, from_be_bytes;
    i64, i64_be, from_be_bytes;
    i128, i128_be, from_be_bytes;

    f32, f32_le, from_le_bytes;
    f64, f64_le, from_le_bytes;

    f32, f32_be, from_be_bytes;
    f64, f64_be, from_be_bytes;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ints() {
        let mut p = Parser::new(&[4, 5, 6, 7]);
        assert_eq!(p.u8(), Ok(4));
        assert_eq!(p.u16_le(), Ok(0x605));
        assert_eq!(p.u32_le(), Err(ParserError));
    }

    #[test]
    fn strz() {
        let mut p = Parser::new(b"hello\0world\0");
        assert_eq!(p.strz(), Ok("hello"));
        assert_eq!(p.strz(), Ok("world"));
        assert!(p.is_empty());

        let mut p = Parser::new(b"no nuls");
        assert_eq!(p.strz(), Err(ParserError));
    }
}
