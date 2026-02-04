//! Parsing implementations for all [`Component`](crate::format_description::Component)s.

use core::num::{NonZeroU16, NonZeroU8};

use crate::format_description::modifier;
#[cfg(feature = "large-dates")]
use crate::parsing::combinator::n_to_m_digits_padded;
use crate::parsing::combinator::{
    any_digit, exactly_n_digits, exactly_n_digits_padded, first_match, opt, sign,
};
use crate::parsing::ParsedItem;
use crate::{Month, Weekday};

// region: date components
/// Parse the "year" component of a `Date`.
pub(crate) fn parse_year(input: &[u8], modifiers: modifier::Year) -> Option<ParsedItem<'_, i32>> {
    match modifiers.repr {
        modifier::YearRepr::Full => {
            let ParsedItem(input, sign) = opt(sign)(input);
            #[cfg(not(feature = "large-dates"))]
            let ParsedItem(input, year) =
                exactly_n_digits_padded::<u32>(4, modifiers.padding)(input)?;
            #[cfg(feature = "large-dates")]
            let ParsedItem(input, year) =
                n_to_m_digits_padded::<u32>(4, 6, modifiers.padding)(input)?;
            match sign {
                Some(b'-') => Some(ParsedItem(input, -(year as i32))),
                None if modifiers.sign_is_mandatory || year >= 10_000 => None,
                _ => Some(ParsedItem(input, year as i32)),
            }
        }
        modifier::YearRepr::LastTwo => {
            Some(exactly_n_digits_padded::<u32>(2, modifiers.padding)(input)?.map(|v| v as i32))
        }
    }
}

/// Parse the "month" component of a `Date`.
pub(crate) fn parse_month(
    input: &[u8],
    modifiers: modifier::Month,
) -> Option<ParsedItem<'_, Month>> {
    use Month::*;
    let ParsedItem(remaining, value) = first_match(
        match modifiers.repr {
            modifier::MonthRepr::Numerical => {
                return exactly_n_digits_padded(2, modifiers.padding)(input)?
                    .flat_map(|n| Month::from_number(n).ok());
            }
            modifier::MonthRepr::Long => [
                ("January", January),
                ("February", February),
                ("March", March),
                ("April", April),
                ("May", May),
                ("June", June),
                ("July", July),
                ("August", August),
                ("September", September),
                ("October", October),
                ("November", November),
                ("December", December),
            ]
            .iter(),
            modifier::MonthRepr::Short => [
                ("Jan", January),
                ("Feb", February),
                ("Mar", March),
                ("Apr", April),
                ("May", May),
                ("Jun", June),
                ("Jul", July),
                ("Aug", August),
                ("Sep", September),
                ("Oct", October),
                ("Nov", November),
                ("Dec", December),
            ]
            .iter(),
        },
        modifiers.case_sensitive,
    )(input)?;
    Some(ParsedItem(remaining, value))
}

/// Parse the "week number" component of a `Date`.
pub(crate) fn parse_week_number(
    input: &[u8],
    modifiers: modifier::WeekNumber,
) -> Option<ParsedItem<'_, u8>> {
    exactly_n_digits_padded(2, modifiers.padding)(input)
}

/// Parse the "weekday" component of a `Date`.
pub(crate) fn parse_weekday(
    input: &[u8],
    modifiers: modifier::Weekday,
) -> Option<ParsedItem<'_, Weekday>> {
    first_match(
        match (modifiers.repr, modifiers.one_indexed) {
            (modifier::WeekdayRepr::Short, _) => [
                ("Mon", Weekday::Monday),
                ("Tue", Weekday::Tuesday),
                ("Wed", Weekday::Wednesday),
                ("Thu", Weekday::Thursday),
                ("Fri", Weekday::Friday),
                ("Sat", Weekday::Saturday),
                ("Sun", Weekday::Sunday),
            ]
            .iter(),
            (modifier::WeekdayRepr::Long, _) => [
                ("Monday", Weekday::Monday),
                ("Tuesday", Weekday::Tuesday),
                ("Wednesday", Weekday::Wednesday),
                ("Thursday", Weekday::Thursday),
                ("Friday", Weekday::Friday),
                ("Saturday", Weekday::Saturday),
                ("Sunday", Weekday::Sunday),
            ]
            .iter(),
            (modifier::WeekdayRepr::Sunday, false) => [
                ("1", Weekday::Monday),
                ("2", Weekday::Tuesday),
                ("3", Weekday::Wednesday),
                ("4", Weekday::Thursday),
                ("5", Weekday::Friday),
                ("6", Weekday::Saturday),
                ("0", Weekday::Sunday),
            ]
            .iter(),
            (modifier::WeekdayRepr::Sunday, true) => [
                ("2", Weekday::Monday),
                ("3", Weekday::Tuesday),
                ("4", Weekday::Wednesday),
                ("5", Weekday::Thursday),
                ("6", Weekday::Friday),
                ("7", Weekday::Saturday),
                ("1", Weekday::Sunday),
            ]
            .iter(),
            (modifier::WeekdayRepr::Monday, false) => [
                ("0", Weekday::Monday),
                ("1", Weekday::Tuesday),
                ("2", Weekday::Wednesday),
                ("3", Weekday::Thursday),
                ("4", Weekday::Friday),
                ("5", Weekday::Saturday),
                ("6", Weekday::Sunday),
            ]
            .iter(),
            (modifier::WeekdayRepr::Monday, true) => [
                ("1", Weekday::Monday),
                ("2", Weekday::Tuesday),
                ("3", Weekday::Wednesday),
                ("4", Weekday::Thursday),
                ("5", Weekday::Friday),
                ("6", Weekday::Saturday),
                ("7", Weekday::Sunday),
            ]
            .iter(),
        },
        modifiers.case_sensitive,
    )(input)
}

/// Parse the "ordinal" component of a `Date`.
pub(crate) fn parse_ordinal(
    input: &[u8],
    modifiers: modifier::Ordinal,
) -> Option<ParsedItem<'_, NonZeroU16>> {
    exactly_n_digits_padded(3, modifiers.padding)(input)
}

/// Parse the "day" component of a `Date`.
pub(crate) fn parse_day(
    input: &[u8],
    modifiers: modifier::Day,
) -> Option<ParsedItem<'_, NonZeroU8>> {
    exactly_n_digits_padded(2, modifiers.padding)(input)
}
// endregion date components

// region: time components
/// Indicate whether the hour is "am" or "pm".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Period {
    #[allow(clippy::missing_docs_in_private_items)]
    Am,
    #[allow(clippy::missing_docs_in_private_items)]
    Pm,
}

/// Parse the "hour" component of a `Time`.
pub(crate) fn parse_hour(input: &[u8], modifiers: modifier::Hour) -> Option<ParsedItem<'_, u8>> {
    exactly_n_digits_padded(2, modifiers.padding)(input)
}

/// Parse the "minute" component of a `Time`.
pub(crate) fn parse_minute(
    input: &[u8],
    modifiers: modifier::Minute,
) -> Option<ParsedItem<'_, u8>> {
    exactly_n_digits_padded(2, modifiers.padding)(input)
}

/// Parse the "second" component of a `Time`.
pub(crate) fn parse_second(
    input: &[u8],
    modifiers: modifier::Second,
) -> Option<ParsedItem<'_, u8>> {
    exactly_n_digits_padded(2, modifiers.padding)(input)
}

/// Parse the "period" component of a `Time`. Required if the hour is on a 12-hour clock.
pub(crate) fn parse_period(
    input: &[u8],
    modifiers: modifier::Period,
) -> Option<ParsedItem<'_, Period>> {
    first_match(
        if modifiers.is_uppercase {
            [("AM", Period::Am), ("PM", Period::Pm)].iter()
        } else {
            [("am", Period::Am), ("pm", Period::Pm)].iter()
        },
        modifiers.case_sensitive,
    )(input)
}

/// Parse the "subsecond" component of a `Time`.
pub(crate) fn parse_subsecond(
    input: &[u8],
    modifiers: modifier::Subsecond,
) -> Option<ParsedItem<'_, u32>> {
    Some(match modifiers.digits {
        modifier::SubsecondDigits::One => exactly_n_digits(1)(input)?.map(|v: u32| v * 100_000_000),
        modifier::SubsecondDigits::Two => exactly_n_digits(2)(input)?.map(|v: u32| v * 10_000_000),
        modifier::SubsecondDigits::Three => exactly_n_digits(3)(input)?.map(|v: u32| v * 1_000_000),
        modifier::SubsecondDigits::Four => exactly_n_digits(4)(input)?.map(|v: u32| v * 100_000),
        modifier::SubsecondDigits::Five => exactly_n_digits(5)(input)?.map(|v: u32| v * 10_000),
        modifier::SubsecondDigits::Six => exactly_n_digits(6)(input)?.map(|v: u32| v * 1_000),
        modifier::SubsecondDigits::Seven => exactly_n_digits(7)(input)?.map(|v: u32| v * 100),
        modifier::SubsecondDigits::Eight => exactly_n_digits(8)(input)?.map(|v: u32| v * 10),
        modifier::SubsecondDigits::Nine => exactly_n_digits(9)(input)?,
        modifier::SubsecondDigits::OneOrMore => {
            let ParsedItem(mut input, mut value) =
                any_digit(input)?.map(|v| (v - b'0') as u32 * 100_000_000);

            let mut multiplier = 10_000_000;
            while let Some(ParsedItem(new_input, digit)) = any_digit(input) {
                value += (digit - b'0') as u32 * multiplier;
                input = new_input;
                multiplier /= 10;
            }

            ParsedItem(input, value)
        }
    })
}
// endregion time components

// region: offset components
/// Parse the "hour" component of a `UtcOffset`.
pub(crate) fn parse_offset_hour(
    input: &[u8],
    modifiers: modifier::OffsetHour,
) -> Option<ParsedItem<'_, i8>> {
    let ParsedItem(input, sign) = opt(sign)(input);
    let ParsedItem(input, hour) = exactly_n_digits_padded::<u8>(2, modifiers.padding)(input)?;
    match sign {
        Some(b'-') => Some(ParsedItem(input, -(hour as i8))),
        None if modifiers.sign_is_mandatory => None,
        _ => Some(ParsedItem(input, hour as i8)),
    }
}

/// Parse the "minute" component of a `UtcOffset`.
pub(crate) fn parse_offset_minute(
    input: &[u8],
    modifiers: modifier::OffsetMinute,
) -> Option<ParsedItem<'_, u8>> {
    exactly_n_digits_padded(2, modifiers.padding)(input)
}

/// Parse the "second" component of a `UtcOffset`.
pub(crate) fn parse_offset_second(
    input: &[u8],
    modifiers: modifier::OffsetSecond,
) -> Option<ParsedItem<'_, u8>> {
    exactly_n_digits_padded(2, modifiers.padding)(input)
}
// endregion offset components
