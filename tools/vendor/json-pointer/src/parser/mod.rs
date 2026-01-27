mod string_repr;
mod uri_fragment;

use crate::JsonPointer;

/// A parser for JSON pointers. If the string starts with a `#`, it is parsed
/// as a URI fragment. Otherwise, it is parsed in the string representation.
pub fn parse(s: &str) -> Result<JsonPointer<String, Vec<String>>, ParseError> {
    if s.chars().next() == Some('#') {
        let s = uri_fragment::UnescapeIter::new(s.chars().skip(1)).collect::<Result<String, _>>()?;
        string_repr::parse(s.chars())
    } else {
        string_repr::parse(s.chars())
    }
}

/// An error that can be encountered when parsing.
#[derive(Clone, Debug, PartialEq)]
pub enum ParseError {
    /// An invalid escape sequence was encountered, either a `~` escape or a
    /// `%` escape.
    InvalidEscape(String),
    /// An error caused by not having a leading slash on the JSON pointer.
    ///
    /// For example, the string `a/b/c` is not a valid JSON pointer, while
    /// `/a/b/c` is.
    NoLeadingSlash,
}
