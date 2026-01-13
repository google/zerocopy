use proc_macro::TokenStream;

use crate::format_description::error::InvalidFormatDescription;
use crate::format_description::modifier;
use crate::format_description::modifier::Modifiers;
use crate::to_tokens::ToTokens;

pub(crate) enum Component {
    Day(modifier::Day),
    Month(modifier::Month),
    Ordinal(modifier::Ordinal),
    Weekday(modifier::Weekday),
    WeekNumber(modifier::WeekNumber),
    Year(modifier::Year),
    Hour(modifier::Hour),
    Minute(modifier::Minute),
    Period(modifier::Period),
    Second(modifier::Second),
    Subsecond(modifier::Subsecond),
    OffsetHour(modifier::OffsetHour),
    OffsetMinute(modifier::OffsetMinute),
    OffsetSecond(modifier::OffsetSecond),
}

impl ToTokens for Component {
    fn into_token_stream(self) -> TokenStream {
        quote! {
            ::time::format_description::Component::#(match self {
                Self::Day(modifier) => quote! { Day(#(modifier)) },
                Self::Month(modifier) => quote! { Month(#(modifier)) },
                Self::Ordinal(modifier) => quote! { Ordinal(#(modifier)) },
                Self::Weekday(modifier) => quote! { Weekday(#(modifier)) },
                Self::WeekNumber(modifier) => quote! { WeekNumber(#(modifier)) },
                Self::Year(modifier) => quote! { Year(#(modifier)) },
                Self::Hour(modifier) => quote! { Hour(#(modifier)) },
                Self::Minute(modifier) => quote! { Minute(#(modifier)) },
                Self::Period(modifier) => quote! { Period(#(modifier)) },
                Self::Second(modifier) => quote! { Second(#(modifier)) },
                Self::Subsecond(modifier) => quote! { Subsecond(#(modifier)) },
                Self::OffsetHour(modifier) => quote! { OffsetHour(#(modifier)) },
                Self::OffsetMinute(modifier) => quote! { OffsetMinute(#(modifier)) },
                Self::OffsetSecond(modifier) => quote! { OffsetSecond(#(modifier)) },
            })
        }
    }
}

pub(crate) enum NakedComponent {
    Day,
    Month,
    Ordinal,
    Weekday,
    WeekNumber,
    Year,
    Hour,
    Minute,
    Period,
    Second,
    Subsecond,
    OffsetHour,
    OffsetMinute,
    OffsetSecond,
}

impl NakedComponent {
    pub(crate) fn parse(
        component_name: &[u8],
        component_index: usize,
    ) -> Result<Self, InvalidFormatDescription> {
        match component_name {
            b"day" => Ok(Self::Day),
            b"month" => Ok(Self::Month),
            b"ordinal" => Ok(Self::Ordinal),
            b"weekday" => Ok(Self::Weekday),
            b"week_number" => Ok(Self::WeekNumber),
            b"year" => Ok(Self::Year),
            b"hour" => Ok(Self::Hour),
            b"minute" => Ok(Self::Minute),
            b"period" => Ok(Self::Period),
            b"second" => Ok(Self::Second),
            b"subsecond" => Ok(Self::Subsecond),
            b"offset_hour" => Ok(Self::OffsetHour),
            b"offset_minute" => Ok(Self::OffsetMinute),
            b"offset_second" => Ok(Self::OffsetSecond),
            b"" => Err(InvalidFormatDescription::MissingComponentName {
                index: component_index,
            }),
            _ => Err(InvalidFormatDescription::InvalidComponentName {
                name: String::from_utf8_lossy(component_name).into_owned(),
                index: component_index,
            }),
        }
    }

    pub(crate) fn attach_modifiers(self, modifiers: Modifiers) -> Component {
        match self {
            Self::Day => Component::Day(modifier::Day {
                padding: modifiers.padding.unwrap_or_default(),
            }),
            Self::Month => Component::Month(modifier::Month {
                padding: modifiers.padding.unwrap_or_default(),
                repr: modifiers.month_repr.unwrap_or_default(),
            }),
            Self::Ordinal => Component::Ordinal(modifier::Ordinal {
                padding: modifiers.padding.unwrap_or_default(),
            }),
            Self::Weekday => Component::Weekday(modifier::Weekday {
                repr: modifiers.weekday_repr.unwrap_or_default(),
                one_indexed: modifiers.weekday_is_one_indexed.unwrap_or(true),
            }),
            Self::WeekNumber => Component::WeekNumber(modifier::WeekNumber {
                padding: modifiers.padding.unwrap_or_default(),
                repr: modifiers.week_number_repr.unwrap_or_default(),
            }),
            Self::Year => Component::Year(modifier::Year {
                padding: modifiers.padding.unwrap_or_default(),
                repr: modifiers.year_repr.unwrap_or_default(),
                iso_week_based: modifiers.year_is_iso_week_based.unwrap_or_default(),
                sign_is_mandatory: modifiers.sign_is_mandatory.unwrap_or_default(),
            }),
            Self::Hour => Component::Hour(modifier::Hour {
                padding: modifiers.padding.unwrap_or_default(),
                is_12_hour_clock: modifiers.hour_is_12_hour_clock.unwrap_or_default(),
            }),
            Self::Minute => Component::Minute(modifier::Minute {
                padding: modifiers.padding.unwrap_or_default(),
            }),
            Self::Period => Component::Period(modifier::Period {
                is_uppercase: modifiers.period_is_uppercase.unwrap_or(true),
            }),
            Self::Second => Component::Second(modifier::Second {
                padding: modifiers.padding.unwrap_or_default(),
            }),
            Self::Subsecond => Component::Subsecond(modifier::Subsecond {
                digits: modifiers.subsecond_digits.unwrap_or_default(),
            }),
            Self::OffsetHour => Component::OffsetHour(modifier::OffsetHour {
                sign_is_mandatory: modifiers.sign_is_mandatory.unwrap_or_default(),
                padding: modifiers.padding.unwrap_or_default(),
            }),
            Self::OffsetMinute => Component::OffsetMinute(modifier::OffsetMinute {
                padding: modifiers.padding.unwrap_or_default(),
            }),
            Self::OffsetSecond => Component::OffsetSecond(modifier::OffsetSecond {
                padding: modifiers.padding.unwrap_or_default(),
            }),
        }
    }
}
