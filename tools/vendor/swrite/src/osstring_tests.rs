use std::ffi::OsString;

use crate::{swrite, swriteln, SWrite};

#[test]
fn test_swrite() {
    let mut buf = OsString::new();
    swrite!(buf, "Hello, {}!", "world");
    assert_eq!(buf, "Hello, world!");
}

#[test]
fn test_swriteln() {
    let mut buf = OsString::new();
    swriteln!(buf, "Hello, {}!", "world");
    assert_eq!(buf, "Hello, world!\n");
}

#[test]
fn test_swriteln_appends() {
    let mut buf = OsString::new();
    swrite!(buf, "Hello, {}", "world");
    assert_eq!(buf, "Hello, world");
    swriteln!(buf, "!");
    assert_eq!(buf, "Hello, world!\n");
}

#[test]
fn test_swriteln_empty() {
    let mut buf = OsString::new();
    swriteln!(buf);
    assert_eq!(buf, "\n");
    let mut buf = OsString::new();
    swriteln!(buf,);
    assert_eq!(buf, "\n");
}
