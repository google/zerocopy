//! A parser for JSON pointers.

use crate::JsonPointer;
use crate::parser::ParseError;

/// A single token encountered when parsing a JSON pointer.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Token {
    /// An (unescaped) `/` character was encountered. This separates parts of
    /// the JSON pointer.
    Slash,
    /// An (unescaped) literal character.
    Literal(char),
    /// An escaped character. See Escape for details.
    Escaped(Escape),
}

/// An escape character.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Escape {
    /// The `~` character, which is escaped as `~0`.
    Tilde = 0,
    /// The `/` character, which is escaped as `~1`.
    Slash = 1,
}

impl Into<char> for Escape {
    fn into(self) -> char {
        match self {
            Escape::Tilde => '~',
            Escape::Slash => '/',
        }
    }
}

/// A parser for JSON pointers. Note that this parser does *not* handle URI
/// Fragment Identifier Representation (part 6 of RFC 6901).
pub fn parse<II: IntoIterator<Item=char>>(ii: II) -> Result<JsonPointer<String, Vec<String>>, ParseError> {
    // Tokenize the input.
    let toks = Tokenizer::new(ii).collect::<Result<Vec<_>, _>>()?;

    // Split the tokens into "reference tokens". (As named in section 3 of the RFC)
    let mut iter = toks.split(|t| t == &Token::Slash);

    // Check to be sure that the JSON pointer started with a slash.
    if iter.next().map(|s| s.len() > 0).unwrap_or(false) {
        return Err(ParseError::NoLeadingSlash);
    }

    let mut parts = Vec::new();
    for s in iter {
        let mut part = String::new();
        for ch in s {
            part.push(match *ch {
                // Slash is unreachable because we're splitting on it.
                Token::Slash => unreachable!(),
                Token::Literal(c) => c,
                Token::Escaped(e) => e.into(),
            });
        }
        parts.push(part);
    }
    Ok(JsonPointer::new(parts.into_iter().collect()))
}

/// The tokenizer for the parser.
pub struct Tokenizer<I: Iterator<Item=char>> {
    iter: I,
}

impl<I: Iterator<Item=char>> Tokenizer<I> {
    /// Creates a new Tokenizer.
    pub fn new<II: IntoIterator<Item=char, IntoIter=I>>(ii: II) -> Tokenizer<I> {
        Tokenizer {
            iter: ii.into_iter(),
        }
    }
}

impl<I: Iterator<Item=char>> Iterator for Tokenizer<I> {
    type Item = Result<Token, ParseError>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some('/') => Some(Ok(Token::Slash)),
            Some('~') => match self.iter.next() {
                Some('0') => Some(Ok(Token::Escaped(Escape::Tilde))),
                Some('1') => Some(Ok(Token::Escaped(Escape::Slash))),
                Some(c) => Some(Err(ParseError::InvalidEscape(format!("~{}", c)))),
                None => Some(Err(ParseError::InvalidEscape("~".to_string()))),
            },
            Some(c) => Some(Ok(Token::Literal(c))),
            None => None,
        }
    }
}
