fn noop(_: &mut i32) {}

fn main() {
    let mut value = 42;
    let raw = &mut value as *mut i32;
    let borrowed = unsafe { &mut *raw };
    let observed = unsafe { *raw };
    noop(borrowed);
    assert_eq!(observed, 42);
}
