#![feature(explicit_tail_calls)]
#![allow(incomplete_features, unused)]

pub struct BigFreeze(pub [u64; 8]);

#[inline(never)]
pub fn tail_helper(a: BigFreeze, b: BigFreeze, n: u64) -> u64 {
    a.0[0] ^ b.0[0] ^ n
}

#[inline(never)]
pub fn tail_reads_then_becomes(a: BigFreeze, b: BigFreeze, n: u64) -> u64 {
    if n == 0 {
        return a.0[0] ^ b.0[0];
    }
    let s = a.0[1].wrapping_add(b.0[1]);
    become tail_helper(BigFreeze([s; 8]), BigFreeze([n; 8]), n - 1)
}
