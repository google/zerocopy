use core::{fmt, write};

use crate::ByteSize;

/// Format / style to use when displaying a [`ByteSize`].
#[derive(Debug, Clone, Copy)]
pub(crate) enum Format {
    Iec,
    IecShort,
    Si,
    SiShort,
}

impl Format {
    fn unit(self) -> u64 {
        match self {
            Format::Iec | Format::IecShort => crate::KIB,
            Format::Si | Format::SiShort => crate::KB,
        }
    }

    fn unit_base(self) -> f64 {
        match self {
            Format::Iec | Format::IecShort => crate::LN_KIB,
            Format::Si | Format::SiShort => crate::LN_KB,
        }
    }

    fn unit_prefixes(self) -> &'static [u8] {
        match self {
            Format::Iec | Format::IecShort => crate::UNITS_IEC.as_bytes(),
            Format::Si | Format::SiShort => crate::UNITS_SI.as_bytes(),
        }
    }

    fn unit_separator(self) -> &'static str {
        match self {
            Format::Iec | Format::Si => " ",
            Format::IecShort | Format::SiShort => "",
        }
    }

    fn unit_suffix(self) -> &'static str {
        match self {
            Format::Iec => "iB",
            Format::Si => "B",
            Format::IecShort | Format::SiShort => "",
        }
    }
}

/// Formatting display wrapper for [`ByteSize`].
///
/// Supports various styles, see methods. By default, the [`iec()`](Self::iec()) style is used.
///
/// # Examples
///
/// ```
/// # use bytesize::ByteSize;
/// assert_eq!(
///     "1.0 MiB",
///     ByteSize::mib(1).display().iec().to_string(),
/// );
///
/// assert_eq!(
///     "42.0k",
///     ByteSize::kb(42).display().si_short().to_string(),
/// );
/// ```
#[derive(Debug, Clone)]
pub struct Display {
    pub(crate) byte_size: ByteSize,
    pub(crate) format: Format,
}

impl Display {
    /// Format using IEC (binary) units.
    ///
    /// E.g., `11.8 MiB`.
    #[must_use]
    #[doc(alias = "binary")]
    pub fn iec(mut self) -> Self {
        self.format = Format::Iec;
        self
    }

    /// Format using a short style and IEC (binary) units.
    ///
    /// E.g., `11.8M`.
    ///
    /// Designed to produce output compatible with `sort -h`.
    #[must_use]
    #[doc(alias = "binary")]
    pub fn iec_short(mut self) -> Self {
        self.format = Format::IecShort;
        self
    }

    /// Format using SI (decimal) units.
    ///
    /// E.g., `12.3 MB`.
    #[must_use]
    #[doc(alias = "decimal")]
    pub fn si(mut self) -> Self {
        self.format = Format::Si;
        self
    }

    /// Format using a short style and SI (decimal) units.
    ///
    /// E.g., `12.3M`.
    #[must_use]
    #[doc(alias = "decimal")]
    pub fn si_short(mut self) -> Self {
        self.format = Format::SiShort;
        self
    }
}

impl fmt::Display for Display {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bytes = self.byte_size.as_u64();

        let unit = self.format.unit();
        #[allow(unused_variables)] // used in std contexts
        let unit_base = self.format.unit_base();

        let unit_prefixes = self.format.unit_prefixes();
        let unit_separator = self.format.unit_separator();
        let unit_suffix = self.format.unit_suffix();
        let precision = f.precision().unwrap_or(1);

        if bytes < unit {
            write!(f, "{bytes}{unit_separator}B")?;
        } else {
            let size = bytes as f64;

            #[cfg(feature = "std")]
            let exp = ideal_unit_std(size, unit_base);

            #[cfg(not(feature = "std"))]
            let exp = ideal_unit_no_std(size, unit);

            let unit_prefix = unit_prefixes[exp - 1] as char;

            write!(
                f,
                "{:.precision$}{unit_separator}{unit_prefix}{unit_suffix}",
                (size / unit.pow(exp as u32) as f64),
            )?;
        }

        Ok(())
    }
}

#[allow(dead_code)] // used in no-std contexts
fn ideal_unit_no_std(size: f64, unit: u64) -> usize {
    assert!(size >= unit as f64, "only called when bytes >= unit");

    let mut ideal_prefix = 0;
    let mut ideal_size = size;

    loop {
        ideal_prefix += 1;
        ideal_size /= unit as f64;

        if ideal_size < unit as f64 {
            break;
        }
    }

    ideal_prefix
}

#[cfg(feature = "std")]
#[allow(dead_code)] // used in std contexts
fn ideal_unit_std(size: f64, unit_base: f64) -> usize {
    assert!(size.ln() >= unit_base, "only called when bytes >= unit");

    match (size.ln() / unit_base) as usize {
        0 => unreachable!(),
        e => e,
    }
}

#[cfg(test)]
mod tests {
    use alloc::{format, string::ToString as _};

    use super::*;

    #[cfg(feature = "std")]
    quickcheck::quickcheck! {
        #[test]
        fn ideal_unit_selection_std_no_std_iec(bytes: ByteSize) -> bool {
            if bytes.0 < 1025 {
                return true;
            }

            let size = bytes.0 as f64;

            ideal_unit_std(size, crate::LN_KIB) == ideal_unit_no_std(size, crate::KIB)
        }

        #[test]
        fn ideal_unit_selection_std_no_std_si(bytes: ByteSize) -> bool {
            if bytes.0 < 1025 {
                return true;
            }

            let size = bytes.0 as f64;

            ideal_unit_std(size, crate::LN_KB) == ideal_unit_no_std(size, crate::KB)
        }
    }

    #[test]
    fn to_string_iec() {
        let display = Display {
            byte_size: ByteSize::gib(1),
            format: Format::Iec,
        };
        assert_eq!("1.0 GiB", display.to_string());

        let display = Display {
            byte_size: ByteSize::gb(1),
            format: Format::Iec,
        };
        assert_eq!("953.7 MiB", display.to_string());
    }

    #[test]
    fn to_string_si() {
        let display = Display {
            byte_size: ByteSize::gib(1),
            format: Format::Si,
        };
        assert_eq!("1.1 GB", display.to_string());

        let display = Display {
            byte_size: ByteSize::gb(1),
            format: Format::Si,
        };
        assert_eq!("1.0 GB", display.to_string());
    }

    #[test]
    fn to_string_short() {
        let display = Display {
            byte_size: ByteSize::gib(1),
            format: Format::IecShort,
        };
        assert_eq!("1.0G", display.to_string());

        let display = Display {
            byte_size: ByteSize::gb(1),
            format: Format::IecShort,
        };
        assert_eq!("953.7M", display.to_string());
    }

    #[track_caller]
    fn assert_to_string(expected: &str, byte_size: ByteSize, format: Format) {
        assert_eq!(expected, Display { byte_size, format }.to_string());
    }

    #[test]
    fn test_to_string_as() {
        assert_to_string("215 B", ByteSize::b(215), Format::Iec);
        assert_to_string("215 B", ByteSize::b(215), Format::Si);

        assert_to_string("1.0 KiB", ByteSize::kib(1), Format::Iec);
        assert_to_string("1.0 kB", ByteSize::kib(1), Format::Si);

        assert_to_string("293.9 KiB", ByteSize::kb(301), Format::Iec);
        assert_to_string("301.0 kB", ByteSize::kb(301), Format::Si);

        assert_to_string("1.0 MiB", ByteSize::mib(1), Format::Iec);
        assert_to_string("1.0 MB", ByteSize::mib(1), Format::Si);

        assert_to_string("1.9 GiB", ByteSize::mib(1907), Format::Iec);
        assert_to_string("2.0 GB", ByteSize::mib(1908), Format::Si);

        assert_to_string("399.6 MiB", ByteSize::mb(419), Format::Iec);
        assert_to_string("419.0 MB", ByteSize::mb(419), Format::Si);

        assert_to_string("482.4 GiB", ByteSize::gb(518), Format::Iec);
        assert_to_string("518.0 GB", ByteSize::gb(518), Format::Si);

        assert_to_string("741.2 TiB", ByteSize::tb(815), Format::Iec);
        assert_to_string("815.0 TB", ByteSize::tb(815), Format::Si);

        assert_to_string("540.9 PiB", ByteSize::pb(609), Format::Iec);
        assert_to_string("609.0 PB", ByteSize::pb(609), Format::Si);
    }

    #[test]
    fn precision() {
        let size = ByteSize::mib(1908);
        assert_eq!("1.9 GiB".to_string(), format!("{size}"));
        assert_eq!("2 GiB".to_string(), format!("{size:.0}"));
        assert_eq!("1.86328 GiB".to_string(), format!("{size:.5}"));
    }
}
