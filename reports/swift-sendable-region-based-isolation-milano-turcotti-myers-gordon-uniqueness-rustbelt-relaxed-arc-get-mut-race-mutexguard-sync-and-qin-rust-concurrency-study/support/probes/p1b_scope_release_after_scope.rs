// Expect acceptance: the same release placed after the scope compiles.
fn main() {
    let v = vec![1u8, 2, 3];
    std::thread::scope(|s| {
        s.spawn(|| println!("{}", v.len()));
    });
    drop(v); // statically placed release after the join point
}
