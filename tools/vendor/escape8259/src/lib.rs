//! `escape8259` performs RFC8259-compliant string escaping and un-escaping.
//!
//! [RFC8259] is a JSON encoding standard.  Many JSON encoders exist, but other
//! RFCs use the same string escaping mechanism, so it's useful to be able to
//! access the string escaping functions by themselves.
//!
//! # Examples
//!
//! ```
//! use escape8259::{escape, unescape};
//!
//! let s = "A null (\0) and a double-quote (\")";
//! assert_eq!(escape(s), r#"A null (\u0000) and a double-quote (\")"#);
//!
//! let crab = r#"This is a crab: \ud83e\udd80"#;
//! assert_eq!(unescape(crab).unwrap(), "This is a crab: 🦀");
//!
//! // We accept encodings that weren't really necessary.
//! assert_eq!(unescape(r#"\u0041\n"#).unwrap(), "A\n");
//!
//! let multiline = r#"hello
//!  world"#;
//! assert_eq!(escape(multiline), r#"hello\n world"#);
//! ```
//!
//! [RFC8259]: https://tools.ietf.org/html/rfc8259

#![warn(missing_docs)]
#![forbid(unsafe_code)]
#![warn(clippy::cast_possible_truncation)]

use std::char::decode_utf16;
use std::fmt::{Display, Write};

/// An error occurred while unescaping.
#[allow(clippy::empty_structs_with_brackets)] // FIXME: correct this if releasing a new major version.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct UnescapeError {}

impl Display for UnescapeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("failed rfc8259 unescape")
    }
}

impl std::error::Error for UnescapeError {}

type UnescapeResult<T> = Result<T, UnescapeError>;

// Used to collect output characters and queue u16 values for translation.
struct UnescapeState {
    // The accumulated characters
    out: String,
    // Store a fragment of a large character for later decoding
    stash: u16,
}

impl UnescapeState {
    fn new() -> UnescapeState {
        UnescapeState {
            out: String::new(),
            stash: 0,
        }
    }

    // Collect a new character
    fn push_char(&mut self, c: char) -> UnescapeResult<()> {
        if self.stash != 0 {
            return Err(UnescapeError {});
        }
        self.out.push(c);
        Ok(())
    }

    // Collect a new UTF16 word.  This can either be one whole character,
    // or part of a larger character.
    fn push_u16(&mut self, x: u16) -> UnescapeResult<()> {
        let surrogate = (0xD800..=0xDFFF).contains(&x);
        match (self.stash, surrogate) {
            (0, false) => {
                // The std library only provides utf16 decode of an iterator,
                // so to decode a single character we wrap it in an array.
                // Hopefully the compiler will elide most of this extra work.
                let words = [x];
                match decode_utf16(words.iter().copied()).next() {
                    Some(Ok(c)) => {
                        self.out.push(c);
                    }
                    _ => return Err(UnescapeError {}),
                }
            }
            (0, true) => self.stash = x,
            (_, false) => {
                return Err(UnescapeError {});
            }
            (w, true) => {
                let words = [w, x];
                match decode_utf16(words.iter().copied()).next() {
                    Some(Ok(c)) => {
                        self.out.push(c);
                        self.stash = 0;
                    }
                    _ => return Err(UnescapeError {}),
                }
            }
        }
        Ok(())
    }

    // If we queued up part of a UTF-16 encoded word but didn't
    // finish it, return an error.  Otherwise, consume self and
    // return the accumulated String.
    fn finalize(self) -> UnescapeResult<String> {
        if self.stash != 0 {
            return Err(UnescapeError {});
        }
        Ok(self.out)
    }
}

fn parse_u16<S>(s: &mut S) -> UnescapeResult<u16>
where
    S: Iterator<Item = char>,
{
    // Placeholder character in case the input doesn't have the 4 chars we want.
    let placeholders = std::iter::repeat('\0');
    let hexnum: String = s.chain(placeholders).take(4).collect();
    u16::from_str_radix(&hexnum, 16).map_err(|_| UnescapeError {})
}

// RFC8259 says non-escaped characters must be in one of the following ranges:
// %x20-21 / %x23-5B / %x5D-10FFFF
fn is_safe_char(c: char) -> bool {
    let safe_ranges = [(0x20..=0x21), (0x23..=0x5B), (0x5D..=0x10FFFF)];
    let cv = c as u32;

    safe_ranges.iter().any(|range| range.contains(&cv))
}

/// Un-escape a string, following RFC8259 rules.
///
/// The only allowed single-character escapes are:
/// `\" \\ \/ /b /f /n /r /t`
///
/// Any other character may be escaped in UTF-16 form:
/// `\uXXXX` or `\uXXXX\uXXXX`
///
/// Characters in the ranges `0x20-21`, `0x23-5B`, `0x5D-10FFFF`
/// may appear un-escaped in the input.
#[inline]
pub fn unescape<S>(s: S) -> UnescapeResult<String>
where
    S: AsRef<str>,
{
    unescape_inner(s.as_ref())
}

fn unescape_inner(s: &str) -> UnescapeResult<String> {
    let mut state = UnescapeState::new();
    let mut ins = s.chars();

    while let Some(c) = ins.next() {
        if c == '\\' {
            match ins.next() {
                None => {
                    return Err(UnescapeError {});
                }
                Some(d) => {
                    match d {
                        '"' | '\\' | '/' => state.push_char(d)?,
                        'b' => state.push_char('\x08')?, // backspace
                        'f' => state.push_char('\x0C')?, // formfeed
                        'n' => state.push_char('\n')?,   // linefeed
                        'r' => state.push_char('\r')?,   // carriage return
                        't' => state.push_char('\t')?,   // tab
                        'u' => {
                            let val = parse_u16(&mut ins)?;
                            state.push_u16(val)?;
                        }
                        _ => {
                            return Err(UnescapeError {});
                        }
                    }
                }
            }
        } else if is_safe_char(c) {
            state.push_char(c)?;
        } else {
            return Err(UnescapeError {});
        }
    }

    state.finalize()
}

// %x22 /          ; "    quotation mark  U+0022
// %x5C /          ; \    reverse solidus U+005C
// %x2F /          ; /    solidus         U+002F
// %x62 /          ; b    backspace       U+0008
// %x66 /          ; f    form feed       U+000C
// %x6E /          ; n    line feed       U+000A
// %x72 /          ; r    carriage return U+000D
// %x74 /          ; t    tab             U+0009
// %x75 4HEXDIG )  ; uXXXX                U+XXXX

fn force_escape(c: char, out: &mut String) {
    let c = c as u32;
    match c {
        0x08 => out.push_str("\\b"),
        0x09 => out.push_str("\\t"),
        0x0A => out.push_str("\\n"),
        0x0C => out.push_str("\\f"),
        0x0D => out.push_str("\\r"),
        0x22 => out.push_str("\\\""),
        0x5C => out.push_str("\\\\"),
        _ => {
            // RFC8259 allows unicode characters natively, so there is no need
            // to convert everything into \uXXXX form.  The only thing that's
            // required to use that form are the ASCII control characters,
            // which will never require more than one \uXXXX value.
            if c >= 0x20 {
                panic!("force_escape unnecessary encoding requested");
            }
            write!(out, "\\u{:04x}", c).unwrap();
        }
    }
}

/// Escape a string, following RFC8259 rules.
///
/// Only characters that require escaping will be escaped:
/// quotation mark `?`,
/// reverse solidus `\` (backslash),
/// and the control characters (`0x00-1F`).
#[inline]
pub fn escape<S>(s: S) -> String
where
    S: AsRef<str>,
{
    escape_inner(s.as_ref())
}

fn escape_inner(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        if is_safe_char(c) {
            out.push(c);
        } else {
            force_escape(c, &mut out);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[rustversion::attr(since(1.46), track_caller)]
    fn assert_round_trip(s: &str) {
        assert_eq!(s, unescape(&escape(s)).unwrap());
    }

    #[test]
    fn test_round_trip() {
        assert_round_trip("abc");
        assert_round_trip("\n\r\t\x08\x0C\x00");
        assert_round_trip(r#"\"#);
        assert_round_trip(r#"""#);
        assert_round_trip("Σ𝄞");
        assert_round_trip(r#"\𝄞"#);
        assert_round_trip(r#"(╯°□°）╯︵ ┻━┻"#);
    }

    #[test]
    fn test_escape() {
        assert_eq!(escape("\0"), r#"\u0000"#);
        assert_eq!(escape("\n"), r#"\n"#);
        assert_eq!(escape(r#"\"#), r#"\\"#);
        assert_eq!(escape(r#"""#), r#"\""#);
        assert_eq!(escape("Σ"), "Σ"); // U+03A3
        assert_eq!(escape("𝄞"), "𝄞"); // U+1D11E
    }

    #[test]
    fn test_unescape() {
        assert_eq!(unescape(&r#"abc"#), Ok("abc".into()));
        assert_eq!(unescape(&r#"ab\nc"#), Ok("ab\nc".into()));
        assert_eq!(unescape(r#"ab\zc"#), Err(UnescapeError {}));
        assert_eq!(unescape(r#" \"abc\" "#), Ok(" \"abc\" ".into()));
        assert_eq!(unescape(r#"𝄞"#), Ok("𝄞".into()));
        assert_eq!(unescape(r#"\𝄞"#), Err(UnescapeError {}));
        assert_eq!(unescape(r#"\uD834\uDD1E"#), Ok("𝄞".into()));
        assert_eq!(unescape(r#"\uD834"#), Err(UnescapeError {}));
        assert_eq!(unescape(r#"\uDD1E"#), Err(UnescapeError {}));
        assert_eq!(unescape("\t"), Err(UnescapeError {}));
    }

    #[test]
    fn test_generic_asref() {
        assert_eq!(escape("\n"), r#"\n"#);
        assert_eq!(escape(String::from("\n")), r#"\n"#);
        assert_eq!(escape(&String::from("\n")), r#"\n"#);

        assert_eq!(unescape("abc"), Ok("abc".into()));
        assert_eq!(unescape(String::from("abc")), Ok("abc".into()));
        assert_eq!(unescape(&String::from("abc")), Ok("abc".into()));
    }

    #[test]
    fn test_error_impl() {
        // This won't compile if UnescapeError doesn't impl Display + Error.
        let e = UnescapeError {};
        let _x: Box<dyn std::error::Error> = e.into();
    }
}
