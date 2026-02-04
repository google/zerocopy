//! Formatting for various types.

pub(crate) mod formattable;

use std::io;

pub use self::formattable::Formattable;
use crate::format_description::{modifier, Component};
use crate::{error, Date, Time, UtcOffset};

#[allow(clippy::missing_docs_in_private_items)]
const MONTH_NAMES: [&[u8]; 12] = [
    b"January",
    b"February",
    b"March",
    b"April",
    b"May",
    b"June",
    b"July",
    b"August",
    b"September",
    b"October",
    b"November",
    b"December",
];

#[allow(clippy::missing_docs_in_private_items)]
const WEEKDAY_NAMES: [&[u8]; 7] = [
    b"Monday",
    b"Tuesday",
    b"Wednesday",
    b"Thursday",
    b"Friday",
    b"Saturday",
    b"Sunday",
];

// region: extension trait
/// A trait that indicates the formatted width of the value can be determined.
///
/// Note that this should not be implemented for any signed integers. This forces the caller to
/// write the sign if desired.
pub(crate) trait DigitCount {
    /// The number of digits in the stringified value.
    fn num_digits(self) -> u8;
}
impl DigitCount for u8 {
    fn num_digits(self) -> u8 {
        // Using a lookup table as with u32 is *not* faster in standalone benchmarks.
        if self < 10 {
            1
        } else if self < 100 {
            2
        } else {
            3
        }
    }
}
impl DigitCount for u16 {
    fn num_digits(self) -> u8 {
        // Using a lookup table as with u32 is *not* faster in standalone benchmarks.
        if self < 10 {
            1
        } else if self < 100 {
            2
        } else if self < 1_000 {
            3
        } else if self < 10_000 {
            4
        } else {
            5
        }
    }
}

impl DigitCount for u32 {
    fn num_digits(self) -> u8 {
        /// Lookup table
        const TABLE: &[u64] = &[
            0x0001_0000_0000,
            0x0001_0000_0000,
            0x0001_0000_0000,
            0x0001_FFFF_FFF6,
            0x0002_0000_0000,
            0x0002_0000_0000,
            0x0002_FFFF_FF9C,
            0x0003_0000_0000,
            0x0003_0000_0000,
            0x0003_FFFF_FC18,
            0x0004_0000_0000,
            0x0004_0000_0000,
            0x0004_0000_0000,
            0x0004_FFFF_D8F0,
            0x0005_0000_0000,
            0x0005_0000_0000,
            0x0005_FFFE_7960,
            0x0006_0000_0000,
            0x0006_0000_0000,
            0x0006_FFF0_BDC0,
            0x0007_0000_0000,
            0x0007_0000_0000,
            0x0007_0000_0000,
            0x0007_FF67_6980,
            0x0008_0000_0000,
            0x0008_0000_0000,
            0x0008_FA0A_1F00,
            0x0009_0000_0000,
            0x0009_0000_0000,
            0x0009_C465_3600,
            0x000A_0000_0000,
            0x000A_0000_0000,
        ];
        ((self as u64 + TABLE[31_u32.saturating_sub(self.leading_zeros()) as usize]) >> 32) as _
    }
}
// endregion extension trait

/// Format a number with the provided padding and width.
///
/// The sign must be written by the caller.
pub(crate) fn format_number(
    output: &mut impl io::Write,
    value: impl itoa::Integer + DigitCount + Copy,
    padding: modifier::Padding,
    width: u8,
) -> Result<usize, io::Error> {
    match padding {
        modifier::Padding::Space => format_number_pad_space(output, value, width),
        modifier::Padding::Zero => format_number_pad_zero(output, value, width),
        modifier::Padding::None => itoa::write(output, value),
    }
}

/// Format a number with the provided width and spaces as padding.
///
/// The sign must be written by the caller.
pub(crate) fn format_number_pad_space(
    output: &mut impl io::Write,
    value: impl itoa::Integer + DigitCount + Copy,
    width: u8,
) -> Result<usize, io::Error> {
    let mut bytes = 0;
    for _ in 0..(width.saturating_sub(value.num_digits())) {
        bytes += output.write(&[b' '])?;
    }
    bytes += itoa::write(output, value)?;
    Ok(bytes)
}

/// Format a number with the provided width and zeros as padding.
///
/// The sign must be written by the caller.
pub(crate) fn format_number_pad_zero(
    output: &mut impl io::Write,
    value: impl itoa::Integer + DigitCount + Copy,
    width: u8,
) -> Result<usize, io::Error> {
    let mut bytes = 0;
    for _ in 0..(width.saturating_sub(value.num_digits())) {
        bytes += output.write(&[b'0'])?;
    }
    bytes += itoa::write(output, value)?;
    Ok(bytes)
}

/// Format the provided component into the designated output. An `Err` will be returned if the
/// component requires information that it does not provide or if the value cannot be output to the
/// stream.
pub(crate) fn format_component(
    output: &mut impl io::Write,
    component: Component,
    date: Option<Date>,
    time: Option<Time>,
    offset: Option<UtcOffset>,
) -> Result<usize, error::Format> {
    use Component::*;
    Ok(match (component, date, time, offset) {
        (Day(modifier), Some(date), ..) => fmt_day(output, date, modifier)?,
        (Month(modifier), Some(date), ..) => fmt_month(output, date, modifier)?,
        (Ordinal(modifier), Some(date), ..) => fmt_ordinal(output, date, modifier)?,
        (Weekday(modifier), Some(date), ..) => fmt_weekday(output, date, modifier)?,
        (WeekNumber(modifier), Some(date), ..) => fmt_week_number(output, date, modifier)?,
        (Year(modifier), Some(date), ..) => fmt_year(output, date, modifier)?,
        (Hour(modifier), _, Some(time), _) => fmt_hour(output, time, modifier)?,
        (Minute(modifier), _, Some(time), _) => fmt_minute(output, time, modifier)?,
        (Period(modifier), _, Some(time), _) => fmt_period(output, time, modifier)?,
        (Second(modifier), _, Some(time), _) => fmt_second(output, time, modifier)?,
        (Subsecond(modifier), _, Some(time), _) => fmt_subsecond(output, time, modifier)?,
        (OffsetHour(modifier), .., Some(offset)) => fmt_offset_hour(output, offset, modifier)?,
        (OffsetMinute(modifier), .., Some(offset)) => fmt_offset_minute(output, offset, modifier)?,
        (OffsetSecond(modifier), .., Some(offset)) => fmt_offset_second(output, offset, modifier)?,
        _ => return Err(error::Format::InsufficientTypeInformation),
    })
}

// region: date formatters
/// Format the day into the designated output.
fn fmt_day(
    output: &mut impl io::Write,
    date: Date,
    modifier::Day { padding }: modifier::Day,
) -> Result<usize, io::Error> {
    format_number(output, date.day(), padding, 2)
}

/// Format the month into the designated output.
fn fmt_month(
    output: &mut impl io::Write,
    date: Date,
    modifier::Month {
        padding,
        repr,
        case_sensitive: _case_sensitive, // no effect on formatting
    }: modifier::Month,
) -> Result<usize, io::Error> {
    match repr {
        modifier::MonthRepr::Numerical => format_number(output, date.month() as u8, padding, 2),
        modifier::MonthRepr::Long => output.write(MONTH_NAMES[date.month() as usize - 1]),
        modifier::MonthRepr::Short => output.write(&MONTH_NAMES[date.month() as usize - 1][..3]),
    }
}

/// Format the ordinal into the designated output.
fn fmt_ordinal(
    output: &mut impl io::Write,
    date: Date,
    modifier::Ordinal { padding }: modifier::Ordinal,
) -> Result<usize, io::Error> {
    format_number(output, date.ordinal(), padding, 3)
}

/// Format the weekday into the designated output.
fn fmt_weekday(
    output: &mut impl io::Write,
    date: Date,
    modifier::Weekday {
        repr,
        one_indexed,
        case_sensitive: _case_sensitive, // no effect on formatting
    }: modifier::Weekday,
) -> Result<usize, io::Error> {
    match repr {
        modifier::WeekdayRepr::Short => {
            output.write(&WEEKDAY_NAMES[date.weekday().number_days_from_monday() as usize][..3])
        }
        modifier::WeekdayRepr::Long => {
            output.write(WEEKDAY_NAMES[date.weekday().number_days_from_monday() as usize])
        }
        modifier::WeekdayRepr::Sunday => format_number(
            output,
            date.weekday().number_days_from_sunday() + one_indexed as u8,
            modifier::Padding::None,
            1,
        ),
        modifier::WeekdayRepr::Monday => format_number(
            output,
            date.weekday().number_days_from_monday() + one_indexed as u8,
            modifier::Padding::None,
            1,
        ),
    }
}

/// Format the week number into the designated output.
fn fmt_week_number(
    output: &mut impl io::Write,
    date: Date,
    modifier::WeekNumber { padding, repr }: modifier::WeekNumber,
) -> Result<usize, io::Error> {
    format_number(
        output,
        match repr {
            modifier::WeekNumberRepr::Iso => date.iso_week(),
            modifier::WeekNumberRepr::Sunday => date.sunday_based_week(),
            modifier::WeekNumberRepr::Monday => date.monday_based_week(),
        },
        padding,
        2,
    )
}

/// Format the year into the designated output.
fn fmt_year(
    output: &mut impl io::Write,
    date: Date,
    modifier::Year {
        padding,
        repr,
        iso_week_based,
        sign_is_mandatory,
    }: modifier::Year,
) -> Result<usize, io::Error> {
    let full_year = if iso_week_based {
        date.iso_year_week().0
    } else {
        date.year()
    };
    let value = match repr {
        modifier::YearRepr::Full => full_year,
        modifier::YearRepr::LastTwo => (full_year % 100).abs(),
    };
    let width = match repr {
        #[cfg(feature = "large-dates")]
        modifier::YearRepr::Full if value.abs() >= 100_000 => 6,
        #[cfg(feature = "large-dates")]
        modifier::YearRepr::Full if value.abs() >= 10_000 => 5,
        modifier::YearRepr::Full => 4,
        modifier::YearRepr::LastTwo => 2,
    };
    let mut bytes = 0;
    if repr != modifier::YearRepr::LastTwo {
        if full_year < 0 {
            bytes += output.write(&[b'-'])?;
        } else if sign_is_mandatory || cfg!(feature = "large-dates") && full_year >= 10_000 {
            bytes += output.write(&[b'+'])?;
        }
    }
    bytes += format_number(output, value.wrapping_abs() as u32, padding, width)?;
    Ok(bytes)
}
// endregion date formatters

// region: time formatters
/// Format the hour into the designated output.
fn fmt_hour(
    output: &mut impl io::Write,
    time: Time,
    modifier::Hour {
        padding,
        is_12_hour_clock,
    }: modifier::Hour,
) -> Result<usize, io::Error> {
    #[allow(clippy::unnested_or_patterns)]
    let value = match (time.hour(), is_12_hour_clock) {
        (hour, false) => hour,
        (0, true) | (12, true) => 12,
        (hour, true) if hour < 12 => hour,
        (hour, true) => hour - 12,
    };
    format_number(output, value, padding, 2)
}

/// Format the minute into the designated output.
fn fmt_minute(
    output: &mut impl io::Write,
    time: Time,
    modifier::Minute { padding }: modifier::Minute,
) -> Result<usize, io::Error> {
    format_number(output, time.minute(), padding, 2)
}

/// Format the period into the designated output.
fn fmt_period(
    output: &mut impl io::Write,
    time: Time,
    modifier::Period {
        is_uppercase,
        case_sensitive: _case_sensitive, // no effect on formatting
    }: modifier::Period,
) -> Result<usize, io::Error> {
    match (time.hour() >= 12, is_uppercase) {
        (false, false) => output.write(b"am"),
        (false, true) => output.write(b"AM"),
        (true, false) => output.write(b"pm"),
        (true, true) => output.write(b"PM"),
    }
}

/// Format the second into the designated output.
fn fmt_second(
    output: &mut impl io::Write,
    time: Time,
    modifier::Second { padding }: modifier::Second,
) -> Result<usize, io::Error> {
    format_number(output, time.second(), padding, 2)
}

/// Format the subsecond into the designated output.
fn fmt_subsecond(
    output: &mut impl io::Write,
    time: Time,
    modifier::Subsecond { digits }: modifier::Subsecond,
) -> Result<usize, io::Error> {
    let (value, width) = match digits {
        modifier::SubsecondDigits::One => (time.nanosecond() / 100_000_000, 1),
        modifier::SubsecondDigits::Two => (time.nanosecond() / 10_000_000, 2),
        modifier::SubsecondDigits::Three => (time.nanosecond() / 1_000_000, 3),
        modifier::SubsecondDigits::Four => (time.nanosecond() / 100_000, 4),
        modifier::SubsecondDigits::Five => (time.nanosecond() / 10_000, 5),
        modifier::SubsecondDigits::Six => (time.nanosecond() / 1_000, 6),
        modifier::SubsecondDigits::Seven => (time.nanosecond() / 100, 7),
        modifier::SubsecondDigits::Eight => (time.nanosecond() / 10, 8),
        modifier::SubsecondDigits::Nine => (time.nanosecond(), 9),
        modifier::SubsecondDigits::OneOrMore => match time.nanosecond() {
            nanos if nanos % 10 != 0 => (nanos, 9),
            nanos if (nanos / 10) % 10 != 0 => (nanos / 10, 8),
            nanos if (nanos / 100) % 10 != 0 => (nanos / 100, 7),
            nanos if (nanos / 1_000) % 10 != 0 => (nanos / 1_000, 6),
            nanos if (nanos / 10_000) % 10 != 0 => (nanos / 10_000, 5),
            nanos if (nanos / 100_000) % 10 != 0 => (nanos / 100_000, 4),
            nanos if (nanos / 1_000_000) % 10 != 0 => (nanos / 1_000_000, 3),
            nanos if (nanos / 10_000_000) % 10 != 0 => (nanos / 10_000_000, 2),
            nanos => (nanos / 100_000_000, 1),
        },
    };
    format_number_pad_zero(output, value, width)
}
// endregion time formatters

// region: offset formatters
/// Format the offset hour into the designated output.
fn fmt_offset_hour(
    output: &mut impl io::Write,
    offset: UtcOffset,
    modifier::OffsetHour {
        padding,
        sign_is_mandatory,
    }: modifier::OffsetHour,
) -> Result<usize, io::Error> {
    let mut bytes = 0;
    if offset.is_negative() {
        bytes += output.write(&[b'-'])?;
    } else if sign_is_mandatory {
        bytes += output.write(&[b'+'])?;
    }
    bytes += format_number(
        output,
        offset.whole_hours().wrapping_abs() as u8,
        padding,
        2,
    )?;
    Ok(bytes)
}

/// Format the offset minute into the designated output.
fn fmt_offset_minute(
    output: &mut impl io::Write,
    offset: UtcOffset,
    modifier::OffsetMinute { padding }: modifier::OffsetMinute,
) -> Result<usize, io::Error> {
    format_number(
        output,
        offset.minutes_past_hour().wrapping_abs() as u8,
        padding,
        2,
    )
}

/// Format the offset second into the designated output.
fn fmt_offset_second(
    output: &mut impl io::Write,
    offset: UtcOffset,
    modifier::OffsetSecond { padding }: modifier::OffsetSecond,
) -> Result<usize, io::Error> {
    format_number(
        output,
        offset.seconds_past_minute().wrapping_abs() as u8,
        padding,
        2,
    )
}
// endregion offset formatters
