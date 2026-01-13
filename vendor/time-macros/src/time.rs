use std::iter::Peekable;

use proc_macro::{token_stream, Span, TokenStream};

use crate::helpers::{consume_any_ident, consume_number, consume_punct};
use crate::to_tokens::ToTokens;
use crate::Error;

enum Period {
    Am,
    Pm,
    _24,
}

pub(crate) struct Time {
    pub(crate) hour: u8,
    pub(crate) minute: u8,
    pub(crate) second: u8,
    pub(crate) nanosecond: u32,
}

impl Time {
    pub(crate) fn parse(chars: &mut Peekable<token_stream::IntoIter>) -> Result<Self, Error> {
        let (hour_span, hour) = consume_number("hour", chars)?;
        consume_punct(':', chars)?;
        let (minute_span, minute) = consume_number::<u8>("minute", chars)?;
        let (second_span, second): (_, f64) = if consume_punct(':', chars).is_ok() {
            consume_number("second", chars)?
        } else {
            (Span::mixed_site(), 0.)
        };
        let (period_span, period) = if let Ok(span) = consume_any_ident(&["am", "AM"], chars) {
            (Some(span), Period::Am)
        } else if let Ok(span) = consume_any_ident(&["pm", "PM"], chars) {
            (Some(span), Period::Pm)
        } else {
            (None, Period::_24)
        };

        #[allow(clippy::unnested_or_patterns)]
        let hour = match (hour, period) {
            (12, Period::Am) => 0,
            (12, Period::Pm) => 12,
            (hour, Period::Am) | (hour, Period::_24) => hour,
            (hour, Period::Pm) => hour + 12,
        };

        if hour >= 24 {
            Err(Error::InvalidComponent {
                name: "hour",
                value: hour.to_string(),
                span_start: Some(hour_span),
                span_end: Some(period_span.unwrap_or(hour_span)),
            })
        } else if minute >= 60 {
            Err(Error::InvalidComponent {
                name: "minute",
                value: minute.to_string(),
                span_start: Some(minute_span),
                span_end: Some(minute_span),
            })
        } else if second >= 60. {
            Err(Error::InvalidComponent {
                name: "second",
                value: second.to_string(),
                span_start: Some(second_span),
                span_end: Some(second_span),
            })
        } else {
            Ok(Self {
                hour,
                minute,
                second: second.trunc() as _,
                nanosecond: (second.fract() * 1_000_000_000.).round() as _,
            })
        }
    }
}

impl ToTokens for Time {
    fn into_token_stream(self) -> TokenStream {
        quote! {{
            const TIME: ::time::Time = ::time::Time::__from_hms_nanos_unchecked(
                #(self.hour),
                #(self.minute),
                #(self.second),
                #(self.nanosecond),
            );
            TIME
        }}
    }
}
