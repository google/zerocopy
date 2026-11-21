// Run: a panic in a scoped child is joined and re-raised by scope() itself.
fn main() {
    let r = std::panic::catch_unwind(|| {
        std::thread::scope(|s| {
            s.spawn(|| panic!("child failed"));
        });
    });
    let msg = r.err().and_then(|e| e.downcast_ref::<&str>().map(|s| s.to_string())
        .or_else(|| e.downcast_ref::<String>().cloned()));
    println!("scope() panicked with: {:?}", msg);
}
