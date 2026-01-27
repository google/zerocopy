// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::cfg_expr::{
    error::{ParseError, Reason},
    expr::{Expression, Predicate as P},
};

macro_rules! test_validate {
    (ok [$($text:expr => [$($expected:expr),*$(,)?]),+$(,)?]) => {
        $(
            let val_expr = Expression::parse($text).unwrap();
            let mut predicates = val_expr.predicates().enumerate();

            $(
                let actual = predicates.next().unwrap();

                assert_eq!($expected, actual.1, "failed @ index {}", actual.0);
            )*

            if let Some((_, additional)) = predicates.next() {
                assert!(false, "found additional requirement {additional:?}");
            }
        )+
    };
}

macro_rules! err {
    ($text:expr => $reason:ident @ $range:expr) => {
        let act_err = Expression::parse($text).unwrap_err();

        let expected =
            ParseError { original: $text.to_owned(), span: $range, reason: Reason::$reason };

        assert_eq!(expected, act_err);
    };

    ($text:expr => $unexpected:expr; $range:expr) => {
        let act_err = Expression::parse($text).unwrap_err();

        let expected = ParseError {
            original: $text.to_owned(),
            span: $range,
            reason: Reason::Unexpected($unexpected),
        };

        assert_eq!(expected, act_err);
    };
}

#[test]
fn fails_empty() {
    err!("" => Empty @ 0..0);
    err!(" " => Empty @ 0..1);
    err!("\n\t\n" => Empty @ 0..3);
}

#[test]
fn fails_malformed() {
    err!("," => &["<key>", "all", "any", "not"]; 0..1);
    // Keys can't begin with a number
    err!("8" => &["<key>", "all", "any", "not"]; 0..1);
    err!("=" => &["<key>", "all", "any", "not"]; 0..1);
    err!("(" => &["<key>", "all", "any", "not"]; 0..1);
    err!("key =" => &["\"<value>\""]; 5..5);
    err!("key1, key2" => MultipleRootPredicates @ 0..10);
    err!("key1, key2,     " => MultipleRootPredicates @ 0..16);
    err!("key1 = \"v\", key2" => MultipleRootPredicates @ 0..16);
}

#[test]
fn fails_unbalanced_parens() {
    err!("not(key" => UnclosedParens @ 3..7);
    err!("key)" => UnopenedParens @ 3..4);
    err!("foo (" => &["=", ",", ")"]; 4..5);
}

#[test]
fn fails_unbalanced_quotes() {
    err!("key = \"value" => UnclosedQuotes @ 6..12);
    err!("key = \"" => UnclosedQuotes @ 6..7);
    err!("key = \"value, key = \"value\"" => &[",", ")"]; 21..26);
    err!("all(key = \"value), key = \"value\"" => &[",", ")"]; 26..31);
    err!("not(key = \"value)" => UnclosedQuotes @ 10..17);
}

#[test]
fn handles_single_predicate() {
    test_validate!(ok [
        "cfg(key)" => [P::Flag("key")],
        "unix"  => [P::Flag("unix")],
        "target_arch = \"mips\"" => [P::KeyValue{ key: "target_arch", val: "mips" }],
        "feature = \"awesome\"" => [P::KeyValue{ key: "feature", val: "awesome" }],
        "_key" => [P::Flag("_key")],
        " key" => [P::Flag("key")],
        " key  " => [P::Flag("key")],
        " key  = \"val\"" => [P::KeyValue{ key: "key", val: "val" }],
        "key=\"\"" => [P::KeyValue{ key: "key", val: "" }],
        " key=\"7\"       " => [P::KeyValue{ key: "key", val: "7" }],
        "key = \"7 q\" " => [P::KeyValue{ key: "key", val: "7 q" }],
        "target_has_atomic = \"ptr\"" => [P::KeyValue{ key: "target_has_atomic", val: "ptr" }],
        "target_has_atomic = \"4\"" => [P::KeyValue{ key: "target_has_atomic", val: "4" }],
        "target_has_atomic = \"64\"" => [P::KeyValue{ key: "target_has_atomic", val: "64" }],
        "target_has_atomic = \"128\" " => [P::KeyValue{ key: "target_has_atomic", val: "128" }],
        "panic = \"unwind\"" => [P::KeyValue{ key: "panic", val: "unwind" }],
        "panic = \"abort\"" => [P::KeyValue{ key: "panic", val: "abort" }],
    ]);
}

#[test]
fn handles_simple_fns() {
    test_validate!(ok [
        "any()" => [],
        "all()"  => [],
        "not(key = \"value\")" => [P::KeyValue { key: "key", val: "value" }],
    ]);
}

#[test]
fn fails_invalid_fns() {
    err!("nope()" => &["=", ",", ")"]; 4..5);
    err!("all(nope())" => &["=", ",", ")"]; 8..9);
    err!("any(,)" => &["<key>", ")", "all", "any", "not"]; 4..5);
    err!("blah(key)" => &["=", ",", ")"]; 4..5);
}

#[test]
fn ensures_not_has_one_predicate() {
    assert_eq!(Expression::parse("not()").unwrap_err(), ParseError {
        original: "not()".to_owned(),
        span: 0..5,
        reason: Reason::InvalidNot(0)
    });

    assert_eq!(Expression::parse("not(key_one, key_two)").unwrap_err(), ParseError {
        original: "not(key_one, key_two)".to_owned(),
        span: 0..21,
        reason: Reason::InvalidNot(2),
    });

    assert_eq!(Expression::parse("any(not(not(key_one, key_two)))").unwrap_err(), ParseError {
        original: "any(not(not(key_one, key_two)))".to_owned(),
        span: 8..29,
        reason: Reason::InvalidNot(2),
    });

    test_validate!(ok [
        "not(key)" => [P::Flag("key")],
        "not(key,)" => [P::Flag("key")],
        "not(key = \"value\")" => [P::KeyValue { key: "key", val: "value" }],
        "not(key = \"value\",)" => [P::KeyValue { key: "key", val: "value" }],
        "not(not(not(key = \"value\",)))" => [P::KeyValue { key: "key", val: "value" }],
    ]);
}
