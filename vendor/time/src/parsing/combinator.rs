//! Implementations of the low-level parser combinators.

use crate::format_description::modifier::Padding;
use crate::parsing::shim::{Integer, IntegerParseBytes};
use crate::parsing::{strip_prefix, ParsedItem};

/// Parse a "+" or "-" sign. Returns the ASCII byte representing the sign, if present.
pub(crate) const fn sign(input: &[u8]) -> Option<ParsedItem<'_, u8>> {
    match input {
        [b'-', remaining @ ..] => Some(ParsedItem(remaining, b'-')),
        [b'+', remaining @ ..] => Some(ParsedItem(remaining, b'+')),
        _ => None,
    }
}

/// Consume the first matching item, returning its associated value.
// Due to compiler limitations, we must accept a `&str` instead of `&[u8]`.
pub(crate) fn first_match<'a, 'b: 'a, T: Copy + 'a>(
    mut options: impl Iterator<Item = &'a (&'b str, T)>,
    case_sensitive: bool,
) -> impl FnMut(&'b [u8]) -> Option<ParsedItem<'b, T>> {
    move |input| {
        options.find_map(|&(expected, t)| {
            if case_sensitive {
                Some(ParsedItem(strip_prefix(input, expected.as_bytes())?, t))
            } else {
                let n = expected.len();
                if n <= input.len() {
                    let (head, tail) = input.split_at(n);
                    if head.eq_ignore_ascii_case(expected.as_bytes()) {
                        return Some(ParsedItem(tail, t));
                    }
                }
                None
            }
        })
    }
}

/// Consume between `n` and `m` instances of the provided parser.
pub(crate) fn n_to_m<'a, T>(
    n: u8,
    m: u8,
    parser: impl Fn(&'a [u8]) -> Option<ParsedItem<'a, T>>,
) -> impl Fn(&'a [u8]) -> Option<ParsedItem<'a, &'a [u8]>> {
    debug_assert!(m >= n);
    move |mut input| {
        // We need to keep this to determine the total length eventually consumed.
        let orig_input = input;

        // Mandatory
        for _ in 0..n {
            input = parser(input)?.0;
        }

        // Optional
        for _ in n..m {
            match parser(input) {
                Some(parsed) => input = parsed.0,
                None => break,
            }
        }

        Some(ParsedItem(
            input,
            &orig_input[..(orig_input.len() - input.len())],
        ))
    }
}

/// Consume between `n` and `m` digits, returning the numerical value.
pub(crate) fn n_to_m_digits<'a, T: Integer>(
    n: u8,
    m: u8,
) -> impl Fn(&'a [u8]) -> Option<ParsedItem<'a, T>> {
    debug_assert!(m >= n);
    move |input| n_to_m(n, m, any_digit)(input)?.flat_map(|value| value.parse_bytes())
}

/// Consume exactly `n` digits, returning the numerical value.
pub(crate) fn exactly_n_digits<'a, T: Integer>(
    n: u8,
) -> impl Fn(&'a [u8]) -> Option<ParsedItem<'a, T>> {
    n_to_m_digits(n, n)
}

/// Consume exactly `n` digits, returning the numerical value.
pub(crate) fn exactly_n_digits_padded<'a, T: Integer>(
    n: u8,
    padding: Padding,
) -> impl Fn(&'a [u8]) -> Option<ParsedItem<'a, T>> {
    n_to_m_digits_padded(n, n, padding)
}

/// Consume between `n` and `m` digits, returning the numerical value.
pub(crate) fn n_to_m_digits_padded<'a, T: Integer>(
    n: u8,
    m: u8,
    padding: Padding,
) -> impl Fn(&'a [u8]) -> Option<ParsedItem<'a, T>> {
    debug_assert!(m >= n);
    move |input| match padding {
        Padding::None => n_to_m_digits(1, m)(input),
        Padding::Space => {
            let ParsedItem(input, value) = n_to_m(0, n - 1, ascii_char(b' '))(input)?;
            let pad_width = value.len() as u8;
            n_to_m_digits(n - pad_width, m - pad_width)(input)
        }
        Padding::Zero => n_to_m_digits(n, m)(input),
    }
}

/// Consume exactly one digit.
#[allow(clippy::missing_const_for_fn)] // const fn from 1.47
pub(crate) fn any_digit(input: &[u8]) -> Option<ParsedItem<'_, u8>> {
    match input {
        [c, remaining @ ..] if c.is_ascii_digit() => Some(ParsedItem(remaining, *c)),
        _ => None,
    }
}

/// Consume exactly one of the provided ASCII characters.
pub(crate) fn ascii_char(char: u8) -> impl Fn(&[u8]) -> Option<ParsedItem<'_, ()>> {
    debug_assert!(char.is_ascii_graphic() || char.is_ascii_whitespace());
    move |input| match input {
        [c, remaining @ ..] if *c == char => Some(ParsedItem(remaining, ())),
        _ => None,
    }
}

/// Consume exactly one of the provided ASCII characters, case-insensitive.
pub(crate) fn ascii_char_ignore_case(char: u8) -> impl Fn(&[u8]) -> Option<ParsedItem<'_, ()>> {
    debug_assert!(char.is_ascii_graphic() || char.is_ascii_whitespace());
    move |input| match input {
        [c, remaining @ ..] if c.eq_ignore_ascii_case(&char) => Some(ParsedItem(remaining, ())),
        _ => None,
    }
}

/// Optionally consume an input with a given parser.
pub(crate) fn opt<'a, T>(
    parser: impl Fn(&'a [u8]) -> Option<ParsedItem<'a, T>>,
) -> impl Fn(&'a [u8]) -> ParsedItem<'a, Option<T>> {
    move |input| match parser(input) {
        Some(value) => value.map(Some),
        None => ParsedItem(input, None),
    }
}
