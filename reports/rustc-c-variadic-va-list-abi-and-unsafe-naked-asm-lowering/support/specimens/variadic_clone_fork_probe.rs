#![allow(stable_features)]
#![feature(c_variadic)]

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn rust_variadic_clone_fork(count: usize, mut ap: ...) -> u64 {
    let mut ap_fork = ap.clone();
    let mut fork_sum: u64 = 0;
    for _ in 0..count {
        fork_sum += unsafe { ap_fork.next_arg::<u64>() };
    }
    drop(ap_fork);
    let mut orig_sum: u64 = 0;
    for _ in 0..count {
        orig_sum += unsafe { ap.next_arg::<u64>() };
    }
    if fork_sum == orig_sum { orig_sum } else { u64::MAX }
}

fn main() {
    let cf = unsafe { rust_variadic_clone_fork(4, 11u64, 22u64, 33u64, 44u64) };
    println!("CLONE_FORK={cf}");
}
