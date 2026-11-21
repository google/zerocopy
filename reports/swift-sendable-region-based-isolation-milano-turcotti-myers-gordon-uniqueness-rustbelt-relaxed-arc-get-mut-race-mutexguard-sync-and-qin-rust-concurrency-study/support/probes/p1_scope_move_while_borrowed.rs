// Expect rejection: a value borrowed by a scoped thread cannot be dropped
// (released) inside the scope.
fn main() {
    let v = vec![1u8, 2, 3];
    std::thread::scope(|s| {
        s.spawn(|| println!("{}", v.len()));
        drop(v); // release while a scoped thread may still borrow `v`
    });
}
