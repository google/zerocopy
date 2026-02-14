
// Lean keywords that are valid Rust identifiers
pub fn theorem() {}
pub fn axiom() {}
pub fn variable() {}
pub fn example() {}
pub fn lemma() {}
pub fn def() {}
pub fn class() {}
pub fn instance() {}
pub fn structure() {}
pub fn inductive() {}
pub fn from() {} // 'from' is not a keyword in Rust 2021? Actually it is context dependent.
pub fn have() {}
pub fn show() {}
pub fn calc() {}
pub fn then() {}
pub fn with() {}
pub fn section() {}
pub fn namespace() {}
pub fn end() {}
pub fn import() {}
pub fn open() {}
pub fn attribute() {}
pub fn universe() {}

// Lean keywords that are also Rust keywords (need raw identifiers)
pub fn r#where() {}
pub fn r#do() {}
pub fn r#let() {}
pub fn r#mut() {}
pub fn r#if() {}
pub fn r#else() {}
pub fn r#match() {}
