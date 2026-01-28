#[macro_use]
mod macros;

use json_pointer::JsonPointer;
use lazy_static::lazy_static;
use quickcheck::{quickcheck, TestResult};
use regex::Regex;

lazy_static! {
    static ref JSON_POINTER_REGEX: Regex = Regex::new("^(/([^/~]|~[01])*)*$").unwrap();
    static ref URI_FRAGMENT_REGEX: Regex =
        Regex::new("^#(/([^A-Za-z0-9._!$&'()*+,;=@/?-]|~[01]|%[0-9a-fA-F]{2})*)*$").unwrap();
}

quickcheck! {

/// Essentially, `unparse(parse("..."))` should be a no-op.
fn faithful_parse(s: String) -> TestResult {
    // TODO: This could probably be refactored to look much nicer.

    let ok = match s.parse::<JsonPointer<_, _>>() {
        Ok(ptr) => if s.chars().next() == Some('#') {
            if URI_FRAGMENT_REGEX.is_match(&s) {
                s == ptr.uri_fragment()
            } else {
                return TestResult::discard();
            }
        } else {
            s == ptr.to_string()
        },
        Err(_) => return TestResult::discard(),
    };

    if ok {
        TestResult::passed()
    } else {
        TestResult::failed()
    }
}

/// Ensuring that parsing succeeds for all strings that match the regex for
/// JSON pointers.
fn parses_all_valid(s: String) -> bool {
    let matches_regex = JSON_POINTER_REGEX.is_match(&s) || URI_FRAGMENT_REGEX.is_match(&s);
    let parses = s.parse::<JsonPointer<_, _>>().is_ok();

    matches_regex == parses
}

}

/// Checks for known past failures, to prevent regressions.
#[test]
fn regressions() {
    assert_unparse!(uri "#/per%25/%25cent");
}
