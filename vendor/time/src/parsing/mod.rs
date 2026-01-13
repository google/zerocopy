//! Parsing for various types.

pub(crate) mod combinator;
mod component;
pub(crate) mod parsable;
mod parsed;
mod shim;

pub use self::parsable::Parsable;
pub use self::parsed::Parsed;

/// Strip the prefix of the provided slice.
fn strip_prefix<'a>(slice: &'a [u8], prefix: &[u8]) -> Option<&'a [u8]> {
    let n = prefix.len();
    if n <= slice.len() {
        let (head, tail) = slice.split_at(n);
        if head == prefix {
            return Some(tail);
        }
    }
    None
}

/// An item that has been parsed. Represented as a `(remaining, value)` pair.
#[derive(Debug, Clone)]
pub(crate) struct ParsedItem<'a, T>(pub(crate) &'a [u8], pub(crate) T);

impl<'a, T> ParsedItem<'a, T> {
    /// Map the value to a new value, preserving the remaining input.
    pub(crate) fn map<U>(self, f: impl FnOnce(T) -> U) -> ParsedItem<'a, U> {
        ParsedItem(self.0, f(self.1))
    }

    /// Map the value to a new, optional value, preserving the remaining input.
    pub(crate) fn flat_map<U>(self, f: impl FnOnce(T) -> Option<U>) -> Option<ParsedItem<'a, U>> {
        Some(ParsedItem(self.0, f(self.1)?))
    }

    /// Map the value to a new, optional value, preserving the remaining input.
    pub(crate) fn flat_map_res<U, V>(
        self,
        f: impl FnOnce(T) -> Result<U, V>,
    ) -> Result<ParsedItem<'a, U>, V> {
        Ok(ParsedItem(self.0, f(self.1)?))
    }

    /// Assign the stored value to the provided target. The remaining input is returned.
    pub(crate) fn assign_value_to(self, target: &mut Option<T>) -> &'a [u8] {
        *target = Some(self.1);
        self.0
    }
}

impl<'a> ParsedItem<'a, ()> {
    /// Discard the unit value, returning the remaining input.
    pub(crate) const fn into_inner(self) -> &'a [u8] {
        self.0
    }
}
