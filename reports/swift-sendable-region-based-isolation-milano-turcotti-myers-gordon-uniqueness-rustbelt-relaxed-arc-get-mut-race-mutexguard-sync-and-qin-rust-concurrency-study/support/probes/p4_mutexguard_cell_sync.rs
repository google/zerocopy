// Expect rejection on toolchains carrying the fix for the MutexGuard<T>: Sync
// bound (MutexGuard<T>: Sync now requires T: Sync; Cell<i32> is !Sync).
use std::cell::Cell;
use std::sync::MutexGuard;
fn assert_sync<T: Sync>() {}
fn main() {
    assert_sync::<MutexGuard<'static, Cell<i32>>>();
}
