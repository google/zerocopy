#[track_caller]
extern "Rust" fn f() -> u32 {
    std::panic::Location::caller().line()
}
fn main() {
    let _ = f();
}
