// Expect: rejected (RFC 2025 "harmless" example: IndexMut activates the borrow before the argument).
pub fn f() {
    let mut v: Vec<String> = vec![String::from("Hello, ")];
    v[0].push_str(&format!("{}", v.len()));
}
