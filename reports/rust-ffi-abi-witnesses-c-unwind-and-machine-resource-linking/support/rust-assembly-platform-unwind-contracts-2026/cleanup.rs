struct Guard;
impl Drop for Guard {
    fn drop(&mut self) { std::hint::black_box(7u64); }
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn rust_cleanup(callback: extern "C-unwind" fn()) -> u64 {
    let _guard = Guard;
    callback();
    23
}
