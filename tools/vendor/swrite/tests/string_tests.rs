extern crate swrite;
use swrite::{swrite, swriteln, SWrite};

#[test]
fn test_swrite() {
    let mut buf = String::new();
    swrite!(buf, "Hello, {}!", "world");
    assert_eq!(buf, "Hello, world!");
}

#[test]
fn test_swriteln() {
    let mut buf = String::new();
    swriteln!(buf, "Hello, {}!", "world");
    assert_eq!(buf, "Hello, world!\n");
}

#[test]
fn test_swriteln_appends() {
    let mut buf = String::new();
    swrite!(buf, "Hello, {}", "world");
    assert_eq!(buf, "Hello, world");
    swriteln!(buf, "!");
    assert_eq!(buf, "Hello, world!\n");
}

#[test]
fn test_swriteln_empty() {
    let mut buf = String::new();
    swriteln!(buf);
    assert_eq!(buf, "\n");
    let mut buf = String::new();
    swriteln!(buf,);
    assert_eq!(buf, "\n");
}

mod qualified {
    use swrite::SWrite;

    #[test]
    fn test_swrite() {
        let mut buf = String::new();
        swrite::swrite!(buf, "Hello, {}!", "world");
        assert_eq!(buf, "Hello, world!");
    }

    #[test]
    fn test_swriteln() {
        let mut buf = String::new();
        swrite::swriteln!(buf, "Hello, {}!", "world");
        assert_eq!(buf, "Hello, world!\n");
    }

    #[test]
    fn test_swriteln_appends() {
        let mut buf = String::new();
        swrite::swrite!(buf, "Hello, {}", "world");
        assert_eq!(buf, "Hello, world");
        swrite::swriteln!(buf, "!");
        assert_eq!(buf, "Hello, world!\n");
    }

    #[test]
    fn test_swriteln_empty() {
        let mut buf = String::new();
        swrite::swriteln!(buf);
        assert_eq!(buf, "\n");
        let mut buf = String::new();
        swrite::swriteln!(buf,);
        assert_eq!(buf, "\n");
    }
}
