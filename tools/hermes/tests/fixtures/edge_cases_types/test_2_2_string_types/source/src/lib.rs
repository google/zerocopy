
use std::borrow::Cow;

pub struct Strings<'a> {
    pub a: String,
    pub b: &'a str,
    pub c: Box<str>,
    pub d: Cow<'a, str>,
    pub e: char,
}

/// ```lean, hermes
/// proof (h_progress):
///   sorry
/// proof context:
///   unfold check_strings at *
///   simp_all
/// ```
pub fn check_strings(s: String) -> String {
    s
}
