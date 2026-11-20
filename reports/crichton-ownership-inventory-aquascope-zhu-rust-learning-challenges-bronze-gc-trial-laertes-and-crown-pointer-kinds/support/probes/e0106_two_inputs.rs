// The elision rules cannot pick an output lifetime: two input lifetimes, no &self receiver.
pub fn longest(x: &str, y: &str) -> &str {
    if x.len() >= y.len() { x } else { y }
}
