//! `ByteSize` is a semantic wrapper for byte count representations.
//!
//! Features:
//!
//! - Pre-defined constants for various size units (e.g., B, KB, KiB, MB, MiB, ... EB, EiB).
//! - `ByteSize` type which presents size units convertible to different size units.
//! - Arithmetic operations for `ByteSize`.
//! - `FromStr` impl for `ByteSize`, allowing for parsing string size representations like "1.5KiB"
//!   and "521TiB".
//! - Serde support for binary and human-readable deserializers like JSON.
//!
//! # Examples
//!
//! Construction using SI or IEC helpers.
//!
//! ```
//! use bytesize::ByteSize;
//!
//! assert!(ByteSize::kib(4) > ByteSize::kb(4));
//! ```
//!
//! Display as human-readable string.
//!
//! ```
//! use bytesize::ByteSize;
//!
//! assert_eq!("518.0 GiB", ByteSize::gib(518).display().iec().to_string());
//! assert_eq!("556.2 GB", ByteSize::gib(518).display().si().to_string());
//! assert_eq!("518.0G", ByteSize::gib(518).display().iec_short().to_string());
//! ```
//!
//! Arithmetic operations are supported.
//!
//! ```
//! use bytesize::ByteSize;
//!
//! let plus = ByteSize::mb(1) + ByteSize::kb(100);
//! println!("{plus}");
//!
//! let minus = ByteSize::tb(1) - ByteSize::gb(4);
//! assert_eq!(ByteSize::gb(996), minus);
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use alloc::string::ToString as _;
use core::{fmt, ops};

#[cfg(feature = "arbitrary")]
mod arbitrary;
mod display;
mod parse;
#[cfg(feature = "serde")]
mod serde;

pub use self::display::Display;
use self::display::Format;
pub use self::parse::{Unit, UnitParseError};

/// Number of bytes in 1 kilobyte.
pub const KB: u64 = 1_000;
/// Number of bytes in 1 megabyte.
pub const MB: u64 = 1_000_000;
/// Number of bytes in 1 gigabyte.
pub const GB: u64 = 1_000_000_000;
/// Number of bytes in 1 terabyte.
pub const TB: u64 = 1_000_000_000_000;
/// Number of bytes in 1 petabyte.
pub const PB: u64 = 1_000_000_000_000_000;
/// Number of bytes in 1 exabyte.
pub const EB: u64 = 1_000_000_000_000_000_000;

/// Number of bytes in 1 kibibyte.
pub const KIB: u64 = 1_024;
/// Number of bytes in 1 mebibyte.
pub const MIB: u64 = 1_048_576;
/// Number of bytes in 1 gibibyte.
pub const GIB: u64 = 1_073_741_824;
/// Number of bytes in 1 tebibyte.
pub const TIB: u64 = 1_099_511_627_776;
/// Number of bytes in 1 pebibyte.
pub const PIB: u64 = 1_125_899_906_842_624;
/// Number of bytes in 1 exbibyte.
pub const EIB: u64 = 1_152_921_504_606_846_976;

/// IEC (binary) units.
///
/// See <https://en.wikipedia.org/wiki/Kilobyte>.
const UNITS_IEC: &str = "KMGTPE";

/// SI (decimal) units.
///
/// See <https://en.wikipedia.org/wiki/Kilobyte>.
const UNITS_SI: &str = "kMGTPE";

/// `ln(1024) ~= 6.931`
const LN_KIB: f64 = 6.931_471_805_599_453;

/// `ln(1000) ~= 6.908`
const LN_KB: f64 = 6.907_755_278_982_137;

/// Converts a quantity of kilobytes to bytes.
pub fn kb(size: impl Into<u64>) -> u64 {
    size.into() * KB
}

/// Converts a quantity of kibibytes to bytes.
pub fn kib<V: Into<u64>>(size: V) -> u64 {
    size.into() * KIB
}

/// Converts a quantity of megabytes to bytes.
pub fn mb<V: Into<u64>>(size: V) -> u64 {
    size.into() * MB
}

/// Converts a quantity of mebibytes to bytes.
pub fn mib<V: Into<u64>>(size: V) -> u64 {
    size.into() * MIB
}

/// Converts a quantity of gigabytes to bytes.
pub fn gb<V: Into<u64>>(size: V) -> u64 {
    size.into() * GB
}

/// Converts a quantity of gibibytes to bytes.
pub fn gib<V: Into<u64>>(size: V) -> u64 {
    size.into() * GIB
}

/// Converts a quantity of terabytes to bytes.
pub fn tb<V: Into<u64>>(size: V) -> u64 {
    size.into() * TB
}

/// Converts a quantity of tebibytes to bytes.
pub fn tib<V: Into<u64>>(size: V) -> u64 {
    size.into() * TIB
}

/// Converts a quantity of petabytes to bytes.
pub fn pb<V: Into<u64>>(size: V) -> u64 {
    size.into() * PB
}

/// Converts a quantity of pebibytes to bytes.
pub fn pib<V: Into<u64>>(size: V) -> u64 {
    size.into() * PIB
}

/// Converts a quantity of exabytes to bytes.
pub fn eb<V: Into<u64>>(size: V) -> u64 {
    size.into() * EB
}

/// Converts a quantity of exbibytes to bytes.
pub fn eib<V: Into<u64>>(size: V) -> u64 {
    size.into() * EIB
}

/// Byte size representation.
#[derive(Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash, Default)]
pub struct ByteSize(pub u64);

impl ByteSize {
    /// Constructs a byte size wrapper from a quantity of bytes.
    #[inline(always)]
    pub const fn b(size: u64) -> ByteSize {
        ByteSize(size)
    }

    /// Constructs a byte size wrapper from a quantity of kilobytes.
    #[inline(always)]
    pub const fn kb(size: u64) -> ByteSize {
        ByteSize(size * KB)
    }

    /// Constructs a byte size wrapper from a quantity of kibibytes.
    #[inline(always)]
    pub const fn kib(size: u64) -> ByteSize {
        ByteSize(size * KIB)
    }

    /// Constructs a byte size wrapper from a quantity of megabytes.
    #[inline(always)]
    pub const fn mb(size: u64) -> ByteSize {
        ByteSize(size * MB)
    }

    /// Constructs a byte size wrapper from a quantity of mebibytes.
    #[inline(always)]
    pub const fn mib(size: u64) -> ByteSize {
        ByteSize(size * MIB)
    }

    /// Constructs a byte size wrapper from a quantity of gigabytes.
    #[inline(always)]
    pub const fn gb(size: u64) -> ByteSize {
        ByteSize(size * GB)
    }

    /// Constructs a byte size wrapper from a quantity of gibibytes.
    #[inline(always)]
    pub const fn gib(size: u64) -> ByteSize {
        ByteSize(size * GIB)
    }

    /// Constructs a byte size wrapper from a quantity of terabytes.
    #[inline(always)]
    pub const fn tb(size: u64) -> ByteSize {
        ByteSize(size * TB)
    }

    /// Constructs a byte size wrapper from a quantity of tebibytes.
    #[inline(always)]
    pub const fn tib(size: u64) -> ByteSize {
        ByteSize(size * TIB)
    }

    /// Constructs a byte size wrapper from a quantity of petabytes.
    #[inline(always)]
    pub const fn pb(size: u64) -> ByteSize {
        ByteSize(size * PB)
    }

    /// Constructs a byte size wrapper from a quantity of pebibytes.
    #[inline(always)]
    pub const fn pib(size: u64) -> ByteSize {
        ByteSize(size * PIB)
    }

    /// Constructs a byte size wrapper from a quantity of exabytes.
    #[inline(always)]
    pub const fn eb(size: u64) -> ByteSize {
        ByteSize(size * EB)
    }

    /// Constructs a byte size wrapper from a quantity of exbibytes.
    #[inline(always)]
    pub const fn eib(size: u64) -> ByteSize {
        ByteSize(size * EIB)
    }

    /// Returns byte count.
    #[inline(always)]
    pub const fn as_u64(&self) -> u64 {
        self.0
    }

    /// Returns byte count as kilobytes.
    #[inline(always)]
    pub fn as_kb(&self) -> f64 {
        self.0 as f64 / KB as f64
    }

    /// Returns byte count as kibibytes.
    #[inline(always)]
    pub fn as_kib(&self) -> f64 {
        self.0 as f64 / KIB as f64
    }

    /// Returns byte count as megabytes.
    #[inline(always)]
    pub fn as_mb(&self) -> f64 {
        self.0 as f64 / MB as f64
    }

    /// Returns byte count as mebibytes.
    #[inline(always)]
    pub fn as_mib(&self) -> f64 {
        self.0 as f64 / MIB as f64
    }

    /// Returns byte count as gigabytes.
    #[inline(always)]
    pub fn as_gb(&self) -> f64 {
        self.0 as f64 / GB as f64
    }

    /// Returns byte count as gibibytes.
    #[inline(always)]
    pub fn as_gib(&self) -> f64 {
        self.0 as f64 / GIB as f64
    }

    /// Returns byte count as terabytes.
    #[inline(always)]
    pub fn as_tb(&self) -> f64 {
        self.0 as f64 / TB as f64
    }

    /// Returns byte count as tebibytes.
    #[inline(always)]
    pub fn as_tib(&self) -> f64 {
        self.0 as f64 / TIB as f64
    }

    /// Returns byte count as petabytes.
    #[inline(always)]
    pub fn as_pb(&self) -> f64 {
        self.0 as f64 / PB as f64
    }

    /// Returns byte count as pebibytes.
    #[inline(always)]
    pub fn as_pib(&self) -> f64 {
        self.0 as f64 / PIB as f64
    }

    /// Returns byte count as exabytes.
    #[inline(always)]
    pub fn as_eb(&self) -> f64 {
        self.0 as f64 / EB as f64
    }

    /// Returns byte count as exbibytes.
    #[inline(always)]
    pub fn as_eib(&self) -> f64 {
        self.0 as f64 / EIB as f64
    }

    /// Returns a formatting display wrapper.
    pub fn display(&self) -> Display {
        Display {
            byte_size: *self,
            format: Format::Iec,
        }
    }
}

impl fmt::Display for ByteSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let display = self.display();

        if f.width().is_none() {
            // allocation-free fast path for when no formatting options are specified
            fmt::Display::fmt(&display, f)
        } else {
            f.pad(&display.to_string())
        }
    }
}

impl fmt::Debug for ByteSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ({} bytes)", self, self.0)
    }
}

macro_rules! commutative_op {
    ($t:ty) => {
        impl ops::Add<ByteSize> for $t {
            type Output = ByteSize;
            #[inline(always)]
            fn add(self, rhs: ByteSize) -> ByteSize {
                ByteSize(rhs.0 + (self as u64))
            }
        }

        impl ops::Mul<ByteSize> for $t {
            type Output = ByteSize;
            #[inline(always)]
            fn mul(self, rhs: ByteSize) -> ByteSize {
                ByteSize(rhs.0 * (self as u64))
            }
        }
    };
}

commutative_op!(u64);
commutative_op!(u32);
commutative_op!(u16);
commutative_op!(u8);

impl ops::Add<ByteSize> for ByteSize {
    type Output = ByteSize;

    #[inline(always)]
    fn add(self, rhs: ByteSize) -> ByteSize {
        ByteSize(self.0 + rhs.0)
    }
}

impl ops::AddAssign<ByteSize> for ByteSize {
    #[inline(always)]
    fn add_assign(&mut self, rhs: ByteSize) {
        self.0 += rhs.0
    }
}

impl<T> ops::Add<T> for ByteSize
where
    T: Into<u64>,
{
    type Output = ByteSize;
    #[inline(always)]
    fn add(self, rhs: T) -> ByteSize {
        ByteSize(self.0 + (rhs.into()))
    }
}

impl<T> ops::AddAssign<T> for ByteSize
where
    T: Into<u64>,
{
    #[inline(always)]
    fn add_assign(&mut self, rhs: T) {
        self.0 += rhs.into();
    }
}

impl ops::Sub<ByteSize> for ByteSize {
    type Output = ByteSize;

    #[inline(always)]
    fn sub(self, rhs: ByteSize) -> ByteSize {
        ByteSize(self.0 - rhs.0)
    }
}

impl ops::SubAssign<ByteSize> for ByteSize {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: ByteSize) {
        self.0 -= rhs.0
    }
}

impl<T> ops::Sub<T> for ByteSize
where
    T: Into<u64>,
{
    type Output = ByteSize;
    #[inline(always)]
    fn sub(self, rhs: T) -> ByteSize {
        ByteSize(self.0 - (rhs.into()))
    }
}

impl<T> ops::SubAssign<T> for ByteSize
where
    T: Into<u64>,
{
    #[inline(always)]
    fn sub_assign(&mut self, rhs: T) {
        self.0 -= rhs.into();
    }
}

impl<T> ops::Mul<T> for ByteSize
where
    T: Into<u64>,
{
    type Output = ByteSize;
    #[inline(always)]
    fn mul(self, rhs: T) -> ByteSize {
        ByteSize(self.0 * rhs.into())
    }
}

impl<T> ops::MulAssign<T> for ByteSize
where
    T: Into<u64>,
{
    #[inline(always)]
    fn mul_assign(&mut self, rhs: T) {
        self.0 *= rhs.into();
    }
}

#[cfg(test)]
mod property_tests {
    use alloc::string::{String, ToString as _};

    use super::*;

    impl quickcheck::Arbitrary for ByteSize {
        fn arbitrary(g: &mut quickcheck::Gen) -> Self {
            Self(u64::arbitrary(g))
        }
    }

    quickcheck::quickcheck! {
        fn parsing_never_panics(size: String) -> bool {
            let _ = size.parse::<ByteSize>();
            true
        }

        fn to_string_never_blank(size: ByteSize) -> bool {
            !size.to_string().is_empty()
        }

        fn to_string_never_large(size: ByteSize) -> bool {
            size.to_string().len() < 11
        }

        fn string_round_trip(size: ByteSize) -> bool {
            // currently fails on many inputs above the pebibyte level
            if size > ByteSize::pib(1) {
                return true;
            }

            size.to_string().parse::<ByteSize>().unwrap() == size
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::format;

    use super::*;

    #[test]
    fn test_arithmetic_op() {
        let mut x = ByteSize::mb(1);
        let y = ByteSize::kb(100);

        assert_eq!((x + y).as_u64(), 1_100_000u64);

        assert_eq!((x - y).as_u64(), 900_000u64);

        assert_eq!((x + (100 * 1000) as u64).as_u64(), 1_100_000);

        assert_eq!((x * 2u64).as_u64(), 2_000_000);

        x += y;
        assert_eq!(x.as_u64(), 1_100_000);
        x *= 2u64;
        assert_eq!(x.as_u64(), 2_200_000);
    }

    #[allow(clippy::unnecessary_cast)]
    #[test]
    fn test_arithmetic_primitives() {
        let mut x = ByteSize::mb(1);

        assert_eq!((x + MB as u64).as_u64(), 2_000_000);
        assert_eq!((x + MB as u32).as_u64(), 2_000_000);
        assert_eq!((x + KB as u16).as_u64(), 1_001_000);
        assert_eq!((x - MB as u64).as_u64(), 0);
        assert_eq!((x - MB as u32).as_u64(), 0);
        assert_eq!((x - KB as u32).as_u64(), 999_000);

        x += MB as u64;
        x += MB as u32;
        x += 10u16;
        x += 1u8;
        assert_eq!(x.as_u64(), 3_000_011);
    }

    #[test]
    fn test_comparison() {
        assert!(ByteSize::mb(1) == ByteSize::kb(1000));
        assert!(ByteSize::mib(1) == ByteSize::kib(1024));
        assert!(ByteSize::mb(1) != ByteSize::kib(1024));
        assert!(ByteSize::mb(1) < ByteSize::kib(1024));
        assert!(ByteSize::b(0) < ByteSize::tib(1));
        assert!(ByteSize::pib(1) < ByteSize::eb(1));
    }

    #[test]
    fn as_unit_conversions() {
        assert_eq!(41992187.5, ByteSize::gb(43).as_kib());
        assert_eq!(0.028311552, ByteSize::mib(27).as_gb());
        assert_eq!(0.0380859375, ByteSize::tib(39).as_pib());
        assert_eq!(961.482752, ByteSize::kib(938948).as_mb());
        assert_eq!(4.195428726649908, ByteSize::pb(4837).as_eib());
        assert_eq!(2.613772153284117, ByteSize::b(2873872874893).as_tib());
    }

    #[track_caller]
    fn assert_display(expected: &str, b: ByteSize) {
        assert_eq!(expected, format!("{b}"));
    }

    #[test]
    fn test_display() {
        assert_display("215 B", ByteSize::b(215));
        assert_display("1.0 KiB", ByteSize::kib(1));
        assert_display("301.0 KiB", ByteSize::kib(301));
        assert_display("419.0 MiB", ByteSize::mib(419));
        assert_display("518.0 GiB", ByteSize::gib(518));
        assert_display("815.0 TiB", ByteSize::tib(815));
        assert_display("609.0 PiB", ByteSize::pib(609));
        assert_display("15.0 EiB", ByteSize::eib(15));
    }

    #[test]
    fn test_display_alignment() {
        assert_eq!("|357 B     |", format!("|{:10}|", ByteSize(357)));
        assert_eq!("|     357 B|", format!("|{:>10}|", ByteSize(357)));
        assert_eq!("|357 B     |", format!("|{:<10}|", ByteSize(357)));
        assert_eq!("|  357 B   |", format!("|{:^10}|", ByteSize(357)));

        assert_eq!("|-----357 B|", format!("|{:->10}|", ByteSize(357)));
        assert_eq!("|357 B-----|", format!("|{:-<10}|", ByteSize(357)));
        assert_eq!("|--357 B---|", format!("|{:-^10}|", ByteSize(357)));
    }

    #[test]
    fn test_default() {
        assert_eq!(ByteSize::b(0), ByteSize::default());
    }
}
