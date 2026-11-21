// Expect rejection: an unscoped spawn requires F: 'static, so it cannot borrow a local.
fn main() {
    let v = vec![1u8, 2, 3];
    let h = std::thread::spawn(|| println!("{}", v.len()));
    h.join().unwrap();
}
