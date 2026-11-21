fn main() {
    let c = #[track_caller] || std::panic::Location::caller().line();
    let _ = c();
}
