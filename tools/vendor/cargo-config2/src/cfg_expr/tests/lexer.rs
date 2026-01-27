// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::cfg_expr::expr::lexer::{Lexer, Token};

macro_rules! test_lex {
    ($text:expr, [$($token:expr),+$(,)?]) => {
        let lexed: Vec<_> = Lexer::new($text).map(|lt| lt.unwrap().token).collect();
        let expected = vec![$($token),+];

        assert_eq!(lexed, expected);
    }
}

#[test]
fn handles_raw() {
    test_lex!("key", [Token::Key("key")]);
}

#[test]
fn strips_attribute() {
    test_lex!("cfg(key)", [Token::Key("key")]);
}

#[test]
fn handle_key_value() {
    test_lex!("key = \"value\"", [Token::Key("key"), Token::Equals, Token::Value("value"),]);
}

#[test]
fn handle_empty_value() {
    test_lex!("key = \"\"", [Token::Key("key"), Token::Equals, Token::Value(""),]);
}

#[test]
fn handle_short_key() {
    test_lex!("k", [Token::Key("k"),]);
}

#[test]
fn handle_cfg_keywords() {
    test_lex!("all(any(not(any_blah,all_nope,not_any)))", [
        Token::All,
        Token::OpenParen,
        Token::Any,
        Token::OpenParen,
        Token::Not,
        Token::OpenParen,
        Token::Key("any_blah"),
        Token::Comma,
        Token::Key("all_nope"),
        Token::Comma,
        Token::Key("not_any"),
        Token::CloseParen,
        Token::CloseParen,
        Token::CloseParen,
    ]);
}
