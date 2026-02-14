
use std::borrow::Cow;

pub struct Strings<'a> {
    pub a: String,
    pub b: &'a str,
    pub c: Box<str>,
    pub d: Cow<'a, str>,
    pub e: char,
}

pub fn check_strings(s: String) -> String {
    s
}
