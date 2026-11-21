#![feature(core_intrinsics, const_eval_select)]
#![allow(internal_features, dead_code, unconditional_panic)]

use core::intrinsics::const_eval_select;

pub const TOP_TRIVIAL: u64 = 42;

pub const fn compute_triangular(n: u64) -> u64 {
    let mut acc = 0;
    let mut i = 1;
    while i <= n {
        acc += i;
        i += 1;
    }
    acc
}

pub const TOP_COMPUTED: u64 = compute_triangular(10);

pub trait Cap {
    const LIMIT: usize;
}

pub struct SmallCap;
impl Cap for SmallCap {
    const LIMIT: usize = 12;
}

#[inline(never)]
pub fn generic_unevaluated<T: Cap, const N: usize>(seed: u8) -> usize {
    let arr = [seed; N];
    let inline_bump = const { compute_triangular(4) as usize };
    T::LIMIT + inline_bump + (arr.len() ^ (arr[0] as usize))
}

#[inline(never)]
pub fn promoted_and_unpromoted_borrows(divisor: u32, dead_flag: bool) -> u32 {
    // Implicitly promoted to `promoted[0]` (`&'static [u32; 3]` in .rodata).
    let prom_slice: &'static [u32; 3] = &[10, 20, 30];
    // Implicitly promoted mutable borrow of 0-length array (`promote_consts.rs` special case).
    let prom_empty_mut: &'static mut [u32; 0] = &mut [];
    // Unpromotable because `divisor` is a runtime argument and division is fallible.
    let unprom_runtime = &[100_u32.wrapping_add(divisor)];
    // Unpromotable fallible division by zero in dead runtime branch: NOT promoted, so no CTFE error!
    if dead_flag {
        let _dead_ref = &(1_u32 / 0);
    }
    prom_slice[0] + prom_slice[2] + (prom_empty_mut.len() as u32) + unprom_runtime[0]
}

const fn sum_bytes_ct(ptr: *const u8, len: usize) -> u64 {
    let mut acc = 0_u64;
    let mut i = 0;
    while i < len {
        acc += unsafe { *ptr.add(i) } as u64;
        i += 1;
    }
    acc
}

fn sum_bytes_rt(ptr: *const u8, len: usize) -> u64 {
    // Runtime implementation uses pointer address alignment inspection (`ptr.addr()`),
    // which is forbidden in CTFE, while computing the exact same mathematical sum.
    let align_rem = ptr.addr() & 7;
    let head = align_rem.min(len);
    let mut acc = 0_u64;
    for i in 0..head {
        acc += unsafe { *ptr.add(i) } as u64;
    }
    for i in head..len {
        acc += unsafe { *ptr.add(i) } as u64;
    }
    acc
}

#[inline(never)]
pub const fn sum_dispatch(bytes: &[u8]) -> u64 {
    const_eval_select((bytes.as_ptr(), bytes.len()), sum_bytes_ct, sum_bytes_rt)
}

pub const CTFE_SUM_WITNESS: u64 = sum_dispatch(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

fn main() {
    let g = generic_unevaluated::<SmallCap, 4>(3);
    let p = promoted_and_unpromoted_borrows(5, false);
    let rt_sum = sum_dispatch(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    let inline_val = const { compute_triangular(6) };
    assert_eq!(TOP_TRIVIAL, 42);
    assert_eq!(TOP_COMPUTED, 55);
    assert_eq!(inline_val, 21);
    assert_eq!(g, 12 + 10 + (4 ^ 3));
    assert_eq!(p, 10 + 30 + 105);
    assert_eq!(CTFE_SUM_WITNESS, 55);
    assert_eq!(rt_sum, 55);
    println!(
        "TRIVIAL={} COMPUTED={} INLINE={} GENERIC={} PROM={} CT_SUM={} RT_SUM={}",
        TOP_TRIVIAL, TOP_COMPUTED, inline_val, g, p, CTFE_SUM_WITNESS, rt_sum
    );
}
