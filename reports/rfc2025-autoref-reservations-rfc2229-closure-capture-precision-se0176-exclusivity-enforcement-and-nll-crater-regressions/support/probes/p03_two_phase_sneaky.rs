// Expect: rejected (RFC 2025 "sneaky" example: argument mutates the receiver's base).
pub fn f() {
    let mut v: Vec<String> = vec![String::from("Hello, ")];
    let s = String::from("foo");
    v[0].push_str({ v.push(s); "World!" });
}
