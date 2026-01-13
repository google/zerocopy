//! Various modifiers for components.

#[cfg(feature = "alloc")]
use alloc::string::String;
#[cfg(feature = "alloc")]
use core::mem;

#[cfg(feature = "alloc")]
use crate::{error::InvalidFormatDescription, format_description::helper};

// region: date modifiers
/// Day of the month.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Day {
    /// The padding to obtain the minimum width.
    pub padding: Padding,
}

/// The representation of a month.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MonthRepr {
    /// The number of the month (January is 1, December is 12).
    Numerical,
    /// The long form of the month name (e.g. "January").
    Long,
    /// The short form of the month name (e.g. "Jan").
    Short,
}

/// Month of the year.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Month {
    /// The padding to obtain the minimum width.
    pub padding: Padding,
    /// What form of representation should be used?
    pub repr: MonthRepr,
    /// Is the value case sensitive when parsing?
    pub case_sensitive: bool,
}

/// Ordinal day of the year.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ordinal {
    /// The padding to obtain the minimum width.
    pub padding: Padding,
}

/// The representation used for the day of the week.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WeekdayRepr {
    /// The short form of the weekday (e.g. "Mon").
    Short,
    /// The long form of the weekday (e.g. "Monday").
    Long,
    /// A numerical representation using Sunday as the first day of the week.
    ///
    /// Sunday is either 0 or 1, depending on the other modifier's value.
    Sunday,
    /// A numerical representation using Monday as the first day of the week.
    ///
    /// Monday is either 0 or 1, depending on the other modifier's value.
    Monday,
}

/// Day of the week.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Weekday {
    /// What form of representation should be used?
    pub repr: WeekdayRepr,
    /// When using a numerical representation, should it be zero or one-indexed?
    pub one_indexed: bool,
    /// Is the value case sensitive when parsing?
    pub case_sensitive: bool,
}

/// The representation used for the week number.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WeekNumberRepr {
    /// Week 1 is the week that contains January 4.
    Iso,
    /// Week 1 begins on the first Sunday of the calendar year.
    Sunday,
    /// Week 1 begins on the first Monday of the calendar year.
    Monday,
}

/// Week within the year.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WeekNumber {
    /// The padding to obtain the minimum width.
    pub padding: Padding,
    /// What kind of representation should be used?
    pub repr: WeekNumberRepr,
}

/// The representation used for a year value.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum YearRepr {
    /// The full value of the year.
    Full,
    /// Only the last two digits of the year.
    LastTwo,
}

/// Year of the date.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Year {
    /// The padding to obtain the minimum width.
    pub padding: Padding,
    /// What kind of representation should be used?
    pub repr: YearRepr,
    /// Whether the value based on the ISO week number.
    pub iso_week_based: bool,
    /// Whether the `+` sign is present when a positive year contains fewer than five digits.
    pub sign_is_mandatory: bool,
}
// endregion date modifiers

// region: time modifiers
/// Hour of the day.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Hour {
    /// The padding to obtain the minimum width.
    pub padding: Padding,
    /// Is the hour displayed using a 12 or 24-hour clock?
    pub is_12_hour_clock: bool,
}

/// Minute within the hour.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Minute {
    /// The padding to obtain the minimum width.
    pub padding: Padding,
}

/// AM/PM part of the time.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Period {
    /// Is the period uppercase or lowercase?
    pub is_uppercase: bool,
    /// Is the value case sensitive when parsing?
    ///
    /// Note that when `false`, the `is_uppercase` field has no effect on parsing behavior.
    pub case_sensitive: bool,
}

/// Second within the minute.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Second {
    /// The padding to obtain the minimum width.
    pub padding: Padding,
}

/// The number of digits present in a subsecond representation.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubsecondDigits {
    /// Exactly one digit.
    One,
    /// Exactly two digits.
    Two,
    /// Exactly three digits.
    Three,
    /// Exactly four digits.
    Four,
    /// Exactly five digits.
    Five,
    /// Exactly six digits.
    Six,
    /// Exactly seven digits.
    Seven,
    /// Exactly eight digits.
    Eight,
    /// Exactly nine digits.
    Nine,
    /// Any number of digits (up to nine) that is at least one. When formatting, the minimum digits
    /// necessary will be used.
    OneOrMore,
}

/// Subsecond within the second.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Subsecond {
    /// How many digits are present in the component?
    pub digits: SubsecondDigits,
}
// endregion time modifiers

// region: offset modifiers
/// Hour of the UTC offset.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OffsetHour {
    /// Whether the `+` sign is present on positive values.
    pub sign_is_mandatory: bool,
    /// The padding to obtain the minimum width.
    pub padding: Padding,
}

/// Minute within the hour of the UTC offset.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OffsetMinute {
    /// The padding to obtain the minimum width.
    pub padding: Padding,
}

/// Second within the minute of the UTC offset.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OffsetSecond {
    /// The padding to obtain the minimum width.
    pub padding: Padding,
}
// endregion offset modifiers

/// Type of padding to ensure a minimum width.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Padding {
    /// A space character (` `) should be used as padding.
    Space,
    /// A zero character (`0`) should be used as padding.
    Zero,
    /// There is no padding. This can result in a width below the otherwise minimum number of
    /// characters.
    None,
}

// Every modifier should use this macro rather than a derived `Default`. This ensures that it is
// const-compatible, albeit with a slight hack.
macro_rules! impl_const_default {
    ($($type:ty => $default:expr;)*) => {$(
        impl $type {
            /// A hack to work around the lack of const traits. Once const traits are stabilized,
            /// this method will be removed in favor of `impl const Default`. As the `Default` trait
            /// is in the prelude, this should not cause any resolution failures. Regardless, this
            /// method is explicitly **not** part of the stable API of the time crate. It exists
            /// solely for use in macros.
            #[doc(hidden)]
            pub const fn default() -> Self {
                $default
            }
        }

        impl Default for $type {
            fn default() -> Self {
                $default
            }
        }
    )*};
}

impl_const_default! {
    Day => Self { padding: Padding::default() };
    MonthRepr => Self::Numerical;
    Month => Self {
        padding: Padding::default(),
        repr: MonthRepr::default(),
        case_sensitive: true,
    };
    Ordinal => Self { padding: Padding::default() };
    WeekdayRepr => Self::Long;
    Weekday => Self {
        repr: WeekdayRepr::default(),
        one_indexed: true,
        case_sensitive: true,
    };
    WeekNumberRepr => Self::Iso;
    WeekNumber => Self {
        padding: Padding::default(),
        repr: WeekNumberRepr::default(),
    };
    YearRepr => Self::Full;
    Year => Self {
        padding: Padding::default(),
        repr: YearRepr::default(),
        iso_week_based: false,
        sign_is_mandatory: false,
    };
    Hour => Self {
        padding: Padding::default(),
        is_12_hour_clock: false,
    };
    Minute => Self { padding: Padding::default() };
    Period => Self {
        is_uppercase: true,
        case_sensitive: true,
    };
    Second => Self { padding: Padding::default() };
    SubsecondDigits => Self::OneOrMore;
    Subsecond => Self { digits: SubsecondDigits::default() };
    OffsetHour => Self {
        sign_is_mandatory: true,
        padding: Padding::default(),
    };
    OffsetMinute => Self { padding: Padding::default() };
    OffsetSecond => Self { padding: Padding::default() };
    Padding => Self::Zero;
}

/// The modifiers parsed for any given component. `None` indicates the modifier was not present.
#[allow(clippy::missing_docs_in_private_items)] // fields
#[derive(Debug, Default)]
pub(crate) struct Modifiers {
    pub(crate) padding: Option<Padding>,
    pub(crate) hour_is_12_hour_clock: Option<bool>,
    pub(crate) period_is_uppercase: Option<bool>,
    pub(crate) month_repr: Option<MonthRepr>,
    pub(crate) subsecond_digits: Option<SubsecondDigits>,
    pub(crate) weekday_repr: Option<WeekdayRepr>,
    pub(crate) weekday_is_one_indexed: Option<bool>,
    pub(crate) week_number_repr: Option<WeekNumberRepr>,
    pub(crate) year_repr: Option<YearRepr>,
    pub(crate) year_is_iso_week_based: Option<bool>,
    pub(crate) sign_is_mandatory: Option<bool>,
    pub(crate) case_sensitive: Option<bool>,
}

impl Modifiers {
    /// Parse the modifiers of a given component.
    #[cfg(feature = "alloc")]
    #[allow(clippy::too_many_lines)]
    pub(crate) fn parse(
        component_name: &[u8],
        mut bytes: &[u8],
        index: &mut usize,
    ) -> Result<Self, InvalidFormatDescription> {
        let mut modifiers = Self::default();

        while !bytes.is_empty() {
            // Trim any whitespace between modifiers.
            bytes = helper::consume_whitespace(bytes, index);

            let modifier;
            if let Some(whitespace_loc) = bytes.iter().position(u8::is_ascii_whitespace) {
                *index += whitespace_loc;
                modifier = &bytes[..whitespace_loc];
                bytes = &bytes[whitespace_loc..];
            } else {
                modifier = mem::take(&mut bytes);
            }

            if modifier.is_empty() {
                break;
            }

            #[allow(clippy::unnested_or_patterns)]
            match (component_name, modifier) {
                (b"day", b"padding:space")
                | (b"hour", b"padding:space")
                | (b"minute", b"padding:space")
                | (b"month", b"padding:space")
                | (b"offset_hour", b"padding:space")
                | (b"offset_minute", b"padding:space")
                | (b"offset_second", b"padding:space")
                | (b"ordinal", b"padding:space")
                | (b"second", b"padding:space")
                | (b"week_number", b"padding:space")
                | (b"year", b"padding:space") => modifiers.padding = Some(Padding::Space),
                (b"day", b"padding:zero")
                | (b"hour", b"padding:zero")
                | (b"minute", b"padding:zero")
                | (b"month", b"padding:zero")
                | (b"offset_hour", b"padding:zero")
                | (b"offset_minute", b"padding:zero")
                | (b"offset_second", b"padding:zero")
                | (b"ordinal", b"padding:zero")
                | (b"second", b"padding:zero")
                | (b"week_number", b"padding:zero")
                | (b"year", b"padding:zero") => modifiers.padding = Some(Padding::Zero),
                (b"day", b"padding:none")
                | (b"hour", b"padding:none")
                | (b"minute", b"padding:none")
                | (b"month", b"padding:none")
                | (b"offset_hour", b"padding:none")
                | (b"offset_minute", b"padding:none")
                | (b"offset_second", b"padding:none")
                | (b"ordinal", b"padding:none")
                | (b"second", b"padding:none")
                | (b"week_number", b"padding:none")
                | (b"year", b"padding:none") => modifiers.padding = Some(Padding::None),
                (b"hour", b"repr:24") => modifiers.hour_is_12_hour_clock = Some(false),
                (b"hour", b"repr:12") => modifiers.hour_is_12_hour_clock = Some(true),
                (b"month", b"case_sensitive:true")
                | (b"period", b"case_sensitive:true")
                | (b"weekday", b"case_sensitive:true") => modifiers.case_sensitive = Some(true),
                (b"month", b"case_sensitive:false")
                | (b"period", b"case_sensitive:false")
                | (b"weekday", b"case_sensitive:false") => modifiers.case_sensitive = Some(false),
                (b"month", b"repr:numerical") => modifiers.month_repr = Some(MonthRepr::Numerical),
                (b"month", b"repr:long") => modifiers.month_repr = Some(MonthRepr::Long),
                (b"month", b"repr:short") => modifiers.month_repr = Some(MonthRepr::Short),
                (b"offset_hour", b"sign:automatic") | (b"year", b"sign:automatic") => {
                    modifiers.sign_is_mandatory = Some(false);
                }
                (b"offset_hour", b"sign:mandatory") | (b"year", b"sign:mandatory") => {
                    modifiers.sign_is_mandatory = Some(true);
                }
                (b"period", b"case:upper") => modifiers.period_is_uppercase = Some(true),
                (b"period", b"case:lower") => modifiers.period_is_uppercase = Some(false),
                (b"subsecond", b"digits:1") => {
                    modifiers.subsecond_digits = Some(SubsecondDigits::One);
                }
                (b"subsecond", b"digits:2") => {
                    modifiers.subsecond_digits = Some(SubsecondDigits::Two);
                }
                (b"subsecond", b"digits:3") => {
                    modifiers.subsecond_digits = Some(SubsecondDigits::Three);
                }
                (b"subsecond", b"digits:4") => {
                    modifiers.subsecond_digits = Some(SubsecondDigits::Four);
                }
                (b"subsecond", b"digits:5") => {
                    modifiers.subsecond_digits = Some(SubsecondDigits::Five);
                }
                (b"subsecond", b"digits:6") => {
                    modifiers.subsecond_digits = Some(SubsecondDigits::Six);
                }
                (b"subsecond", b"digits:7") => {
                    modifiers.subsecond_digits = Some(SubsecondDigits::Seven);
                }
                (b"subsecond", b"digits:8") => {
                    modifiers.subsecond_digits = Some(SubsecondDigits::Eight);
                }
                (b"subsecond", b"digits:9") => {
                    modifiers.subsecond_digits = Some(SubsecondDigits::Nine);
                }
                (b"subsecond", b"digits:1+") => {
                    modifiers.subsecond_digits = Some(SubsecondDigits::OneOrMore);
                }
                (b"weekday", b"repr:short") => modifiers.weekday_repr = Some(WeekdayRepr::Short),
                (b"weekday", b"repr:long") => modifiers.weekday_repr = Some(WeekdayRepr::Long),
                (b"weekday", b"repr:sunday") => modifiers.weekday_repr = Some(WeekdayRepr::Sunday),
                (b"weekday", b"repr:monday") => modifiers.weekday_repr = Some(WeekdayRepr::Monday),
                (b"weekday", b"one_indexed:true") => modifiers.weekday_is_one_indexed = Some(true),
                (b"weekday", b"one_indexed:false") => {
                    modifiers.weekday_is_one_indexed = Some(false);
                }
                (b"week_number", b"repr:iso") => {
                    modifiers.week_number_repr = Some(WeekNumberRepr::Iso);
                }
                (b"week_number", b"repr:sunday") => {
                    modifiers.week_number_repr = Some(WeekNumberRepr::Sunday);
                }
                (b"week_number", b"repr:monday") => {
                    modifiers.week_number_repr = Some(WeekNumberRepr::Monday);
                }
                (b"year", b"repr:full") => modifiers.year_repr = Some(YearRepr::Full),
                (b"year", b"repr:last_two") => modifiers.year_repr = Some(YearRepr::LastTwo),
                (b"year", b"base:calendar") => modifiers.year_is_iso_week_based = Some(false),
                (b"year", b"base:iso_week") => modifiers.year_is_iso_week_based = Some(true),
                _ => {
                    return Err(InvalidFormatDescription::InvalidModifier {
                        value: String::from_utf8_lossy(modifier).into_owned(),
                        index: *index,
                    });
                }
            }
        }

        Ok(modifiers)
    }
}
