use crate::parser::ParseError;

/// An iterator that unescapes URI fragments.
pub struct UnescapeIter<I: Iterator<Item=char>> {
    iter: I,
}

impl<I: Iterator<Item=char>> UnescapeIter<I> {
    /// Creates a new UnescapeIter.
    pub fn new<II: IntoIterator<Item=char, IntoIter=I>>(ii: II) -> UnescapeIter<I> {
        UnescapeIter {
            iter: ii.into_iter(),
        }
    }
}

impl<I: Iterator<Item=char>> Iterator for UnescapeIter<I> {
    type Item = Result<char, ParseError>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some('%') => match self.iter.next().map(as_hex_digit) {
                Some(Ok(a)) => match self.iter.next().map(as_hex_digit) {
                    Some(Ok(b)) => Some(Ok((b + 16 * a) as char)),
                    Some(Err(e)) => Some(Err(ParseError::InvalidEscape(format!("%{:x}{}", a, e)))),
                    None => Some(Err(ParseError::InvalidEscape(format!("%{:x}", a)))),
                },
                Some(Err(e)) => Some(Err(ParseError::InvalidEscape(format!("%{}", e)))),
                None => Some(Err(ParseError::InvalidEscape("%".to_string()))),
            },
            Some(c) => Some(Ok(c)),
            None => None,
        }
    }
}

fn as_hex_digit(ch: char) -> Result<u8, char> {
    match ch {
        '0' => Ok(0),
        '1' => Ok(1),
        '2' => Ok(2),
        '3' => Ok(3),
        '4' => Ok(4),
        '5' => Ok(5),
        '6' => Ok(6),
        '7' => Ok(7),
        '8' => Ok(8),
        '9' => Ok(9),
        'a' | 'A' => Ok(10),
        'b' | 'B' => Ok(11),
        'c' | 'C' => Ok(12),
        'd' | 'D' => Ok(13),
        'e' | 'E' => Ok(14),
        'f' | 'F' => Ok(15),
        c => Err(c),
    }
}
