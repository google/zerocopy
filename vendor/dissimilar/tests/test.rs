// Upstream diff-match-patch's test suite is imported as unit tests in
// src/tests.rs, as they test APIs which are private in the Rust implementation.
//
// This directory is for Rust-specific integration tests and regression tests.

#![allow(clippy::non_ascii_literal)]

use dissimilar::{diff, Chunk};

#[test]
fn test_unicode() {
    // Unicode snowman and unicode comet have the same first two bytes. A
    // byte-based diff would produce a 2-byte Equal followed by 1-byte Delete
    // and Insert.
    let snowman = "\u{2603}";
    let comet = "\u{2604}";
    assert_eq!(snowman.as_bytes()[..2], comet.as_bytes()[..2]);

    let d = diff(snowman, comet);
    assert_eq!(d, vec![Chunk::Delete(snowman), Chunk::Insert(comet)]);
}

#[test]
fn test_issue9() {
    let a = "[乀丁abcd一]";
    let b = "[一abcd丁]";
    let d = diff(a, b);
    assert_eq!(
        d,
        vec![
            Chunk::Equal("["),
            Chunk::Delete("乀丁"),
            Chunk::Insert("一"),
            Chunk::Equal("abcd"),
            Chunk::Delete("一"),
            Chunk::Insert("丁"),
            Chunk::Equal("]"),
        ],
    );
}

#[test]
fn test_issue15() {
    let a = "A のダ";
    let b = "A ダ";
    let d = diff(a, b);

    assert_eq!(
        d,
        vec![Chunk::Equal("A "), Chunk::Delete("の"), Chunk::Equal("ダ")],
    );
}
