// Expect: accepted (RFC 2025 motivating example; autoref receiver is a two-phase borrow).
pub fn f() -> Vec<usize> {
    let mut vec: Vec<usize> = vec![1];
    vec.push(vec.len());
    vec
}
