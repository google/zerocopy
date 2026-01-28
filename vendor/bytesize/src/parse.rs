use alloc::{borrow::ToOwned as _, format, string::String};
use core::{fmt, str};

use super::ByteSize;

impl str::FromStr for ByteSize {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if let Ok(v) = value.parse::<u64>() {
            return Ok(Self(v));
        }
        let number = take_while(value, |c| c.is_ascii_digit() || c == '.');
        match number.parse::<f64>() {
            Ok(v) => {
                let suffix = skip_while(&value[number.len()..], char::is_whitespace);
                match suffix.parse::<Unit>() {
                    Ok(u) => Ok(Self((v * u) as u64)),
                    Err(error) => Err(format!(
                        "couldn't parse {suffix:?} into a known SI unit, {error}"
                    )),
                }
            }
            Err(error) => Err(format!("couldn't parse {value:?} into a ByteSize, {error}")),
        }
    }
}

fn take_while<P>(s: &str, mut predicate: P) -> &str
where
    P: FnMut(char) -> bool,
{
    let offset = s
        .chars()
        .take_while(|ch| predicate(*ch))
        .map(|ch| ch.len_utf8())
        .sum();
    &s[..offset]
}

fn skip_while<P>(s: &str, mut predicate: P) -> &str
where
    P: FnMut(char) -> bool,
{
    let offset: usize = s
        .chars()
        .skip_while(|ch| predicate(*ch))
        .map(|ch| ch.len_utf8())
        .sum();
    &s[(s.len() - offset)..]
}

/// Scale unit.
///
/// ```
/// use bytesize::Unit;
///
/// assert_eq!(
///     "GiB".parse::<Unit>().unwrap(),
///     Unit::GibiByte,
/// );
///
/// "gibibyte".parse::<Unit>().unwrap_err();
/// ```
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq)]
pub enum Unit {
    /// Single byte.
    Byte,

    // power of tens
    /// Kilobyte (10^3 bytes).
    KiloByte,

    /// Megabyte (10^6 bytes)
    MegaByte,

    /// Gigabyte (10^9 bytes)
    GigaByte,

    /// Terabyte (10^12 bytes)
    TeraByte,

    /// Petabyte (10^15 bytes)
    PetaByte,

    /// Exabyte (10^18 bytes)
    ExaByte,

    // power of twos
    /// Kibibyte (2^10 bytes)
    KibiByte,

    /// Mebibyte (2^20 bytes)
    MebiByte,

    /// Gibibyte (2^30 bytes)
    GibiByte,

    /// Tebibyte (2^40 bytes)
    TebiByte,

    /// Pebibyte (2^50 bytes)
    PebiByte,

    /// Exbibyte (2^60 bytes)
    ExbiByte,
}

impl Unit {
    fn factor(&self) -> u64 {
        match self {
            Self::Byte => 1,
            // decimal units
            Self::KiloByte => crate::KB,
            Self::MegaByte => crate::MB,
            Self::GigaByte => crate::GB,
            Self::TeraByte => crate::TB,
            Self::PetaByte => crate::PB,
            Self::ExaByte => crate::EB,
            // binary units
            Self::KibiByte => crate::KIB,
            Self::MebiByte => crate::MIB,
            Self::GibiByte => crate::GIB,
            Self::TebiByte => crate::TIB,
            Self::PebiByte => crate::PIB,
            Self::ExbiByte => crate::EIB,
        }
    }
}

mod impl_ops {
    use super::Unit;
    use core::ops;

    impl ops::Add<u64> for Unit {
        type Output = u64;

        fn add(self, other: u64) -> Self::Output {
            self.factor() + other
        }
    }

    impl ops::Add<Unit> for u64 {
        type Output = u64;

        fn add(self, other: Unit) -> Self::Output {
            self + other.factor()
        }
    }

    impl ops::Mul<u64> for Unit {
        type Output = u64;

        fn mul(self, other: u64) -> Self::Output {
            self.factor() * other
        }
    }

    impl ops::Mul<Unit> for u64 {
        type Output = u64;

        fn mul(self, other: Unit) -> Self::Output {
            self * other.factor()
        }
    }

    impl ops::Add<f64> for Unit {
        type Output = f64;

        fn add(self, other: f64) -> Self::Output {
            self.factor() as f64 + other
        }
    }

    impl ops::Add<Unit> for f64 {
        type Output = f64;

        fn add(self, other: Unit) -> Self::Output {
            other.factor() as f64 + self
        }
    }

    impl ops::Mul<f64> for Unit {
        type Output = f64;

        fn mul(self, other: f64) -> Self::Output {
            self.factor() as f64 * other
        }
    }

    impl ops::Mul<Unit> for f64 {
        type Output = f64;

        fn mul(self, other: Unit) -> Self::Output {
            other.factor() as f64 * self
        }
    }
}

impl str::FromStr for Unit {
    type Err = UnitParseError;

    fn from_str(unit: &str) -> Result<Self, Self::Err> {
        match () {
            _ if unit.eq_ignore_ascii_case("b") => Ok(Self::Byte),
            _ if unit.eq_ignore_ascii_case("k") | unit.eq_ignore_ascii_case("kb") => {
                Ok(Self::KiloByte)
            }
            _ if unit.eq_ignore_ascii_case("m") | unit.eq_ignore_ascii_case("mb") => {
                Ok(Self::MegaByte)
            }
            _ if unit.eq_ignore_ascii_case("g") | unit.eq_ignore_ascii_case("gb") => {
                Ok(Self::GigaByte)
            }
            _ if unit.eq_ignore_ascii_case("t") | unit.eq_ignore_ascii_case("tb") => {
                Ok(Self::TeraByte)
            }
            _ if unit.eq_ignore_ascii_case("p") | unit.eq_ignore_ascii_case("pb") => {
                Ok(Self::PetaByte)
            }
            _ if unit.eq_ignore_ascii_case("e") | unit.eq_ignore_ascii_case("eb") => {
                Ok(Self::ExaByte)
            }
            _ if unit.eq_ignore_ascii_case("ki") | unit.eq_ignore_ascii_case("kib") => {
                Ok(Self::KibiByte)
            }
            _ if unit.eq_ignore_ascii_case("mi") | unit.eq_ignore_ascii_case("mib") => {
                Ok(Self::MebiByte)
            }
            _ if unit.eq_ignore_ascii_case("gi") | unit.eq_ignore_ascii_case("gib") => {
                Ok(Self::GibiByte)
            }
            _ if unit.eq_ignore_ascii_case("ti") | unit.eq_ignore_ascii_case("tib") => {
                Ok(Self::TebiByte)
            }
            _ if unit.eq_ignore_ascii_case("pi") | unit.eq_ignore_ascii_case("pib") => {
                Ok(Self::PebiByte)
            }
            _ if unit.eq_ignore_ascii_case("ei") | unit.eq_ignore_ascii_case("eib") => {
                Ok(Self::ExbiByte)
            }
            _ => Err(UnitParseError(to_string_truncate(unit))),
        }
    }
}

/// Safely truncates
fn to_string_truncate(unit: &str) -> String {
    const MAX_UNIT_LEN: usize = 3;

    if unit.len() > MAX_UNIT_LEN {
        // TODO(MSRV 1.91): use ceil_char_boundary

        if unit.is_char_boundary(3) {
            format!("{}...", &unit[..3])
        } else if unit.is_char_boundary(4) {
            format!("{}...", &unit[..4])
        } else if unit.is_char_boundary(5) {
            format!("{}...", &unit[..5])
        } else if unit.is_char_boundary(6) {
            format!("{}...", &unit[..6])
        } else {
            unreachable!("char boundary will be within 4 bytes")
        }
    } else {
        unit.to_owned()
    }
}

/// Error returned when parsing a [`Unit`] fails.
#[derive(Debug)]
pub struct UnitParseError(String);

impl fmt::Display for UnitParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Failed to parse unit \"{}\"", self.0)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for UnitParseError {}

#[cfg(test)]
mod tests {
    use alloc::string::ToString as _;

    use super::*;

    #[test]
    fn truncating_error_strings() {
        assert_eq!("", to_string_truncate(""));
        assert_eq!("b", to_string_truncate("b"));
        assert_eq!("ob", to_string_truncate("ob"));
        assert_eq!("foo", to_string_truncate("foo"));

        assert_eq!("foo...", to_string_truncate("foob"));
        assert_eq!("foo...", to_string_truncate("foobar"));
    }

    #[test]
    fn when_ok() {
        // shortcut for writing test cases
        fn parse(s: &str) -> u64 {
            s.parse::<ByteSize>().unwrap().0
        }

        assert_eq!("0".parse::<ByteSize>().unwrap().0, 0);
        assert_eq!(parse("0"), 0);
        assert_eq!(parse("500"), 500);
        assert_eq!(parse("1K"), Unit::KiloByte * 1);
        assert_eq!(parse("1Ki"), Unit::KibiByte * 1);
        assert_eq!(parse("1.5Ki"), (1.5 * Unit::KibiByte) as u64);
        assert_eq!(parse("1KiB"), 1 * Unit::KibiByte);
        assert_eq!(parse("1.5KiB"), (1.5 * Unit::KibiByte) as u64);
        assert_eq!(parse("3 MB"), Unit::MegaByte * 3);
        assert_eq!(parse("4 MiB"), Unit::MebiByte * 4);
        assert_eq!(parse("6 GB"), 6 * Unit::GigaByte);
        assert_eq!(parse("4 GiB"), 4 * Unit::GibiByte);
        assert_eq!(parse("88TB"), 88 * Unit::TeraByte);
        assert_eq!(parse("521TiB"), 521 * Unit::TebiByte);
        assert_eq!(parse("8 PB"), 8 * Unit::PetaByte);
        assert_eq!(parse("8P"), 8 * Unit::PetaByte);
        assert_eq!(parse("12 PiB"), 12 * Unit::PebiByte);
    }

    #[test]
    fn when_err() {
        // shortcut for writing test cases
        fn parse(s: &str) -> Result<ByteSize, String> {
            s.parse::<ByteSize>()
        }

        assert!(parse("").is_err());
        assert!(parse("a124GB").is_err());
        assert!(parse("1.3 42.0 B").is_err());
        assert!(parse("1.3 ... B").is_err());
        // The original implementation did not account for the possibility that users may
        // use whitespace to visually separate digits, thus treat it as an error
        assert!(parse("1 000 B").is_err());
    }

    #[test]
    fn to_and_from_str() {
        // shortcut for writing test cases
        fn parse(s: &str) -> u64 {
            s.parse::<ByteSize>().unwrap().0
        }

        assert_eq!(parse(&parse("128GB").to_string()), 128 * Unit::GigaByte);
        assert_eq!(
            parse(&ByteSize(parse("128.000 GiB")).to_string()),
            128 * Unit::GibiByte,
        );
    }
}
