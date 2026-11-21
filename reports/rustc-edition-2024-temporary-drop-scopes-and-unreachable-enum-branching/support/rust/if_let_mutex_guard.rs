//! Whether a `MutexGuard` scrutinee temporary is still held inside the `else`
//! block of `if let` and inside a `match` arm. `try_lock` is used so that a
//! still-held guard is observed as `held` instead of deadlocking.

use std::sync::Mutex;

#[inline(never)]
fn if_let_else(m: &Mutex<Option<u32>>) -> &'static str {
    if let Some(_v) = *m.lock().unwrap() {
        "then"
    } else if m.try_lock().is_ok() {
        "released"
    } else {
        "held"
    }
}

#[inline(never)]
fn match_arm(m: &Mutex<Option<u32>>) -> &'static str {
    match *m.lock().unwrap() {
        Some(_v) => "then",
        None => {
            if m.try_lock().is_ok() {
                "released"
            } else {
                "held"
            }
        }
    }
}

fn main() {
    let m = Mutex::new(None);
    println!("IF_LET_ELSE_LOCK={} MATCH_ARM_LOCK={}", if_let_else(&m), match_arm(&m));
}
