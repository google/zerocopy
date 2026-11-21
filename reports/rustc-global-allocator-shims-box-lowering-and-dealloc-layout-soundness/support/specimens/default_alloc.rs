//! Symbol and IR specimen that uses the default allocator (there is no `#[global_allocator]`).
//!
//!     rustc --edition 2021 -C opt-level=3 -C codegen-units=1 -C save-temps --emit=link,llvm-ir default_alloc.rs

use std::hint::black_box;

/// A heap round trip whose value never escapes: an optimizing build may remove the allocation.
#[no_mangle]
#[inline(never)]
pub fn unpinned_roundtrip(seed: u64) -> u64 {
    let b = Box::new([seed; 8]);
    let mut s = 0u64;
    for x in b.iter() {
        s = s.wrapping_add(*x);
    }
    s
}

/// The box escapes through `black_box`, so the allocation has to happen.
#[no_mangle]
#[inline(never)]
pub fn pinned_roundtrip(seed: u64) -> u64 {
    let b = black_box(Box::new([seed; 8]));
    b[0]
}

/// A zero-sized box: no allocator call is expected at any optimization level.
#[no_mangle]
#[inline(never)]
pub fn zst_box() -> usize {
    let b = black_box(Box::new(()));
    &*b as *const () as usize
}

#[no_mangle]
#[inline(never)]
pub fn grow(v: &mut Vec<u64>, x: u64) {
    v.push(x);
}

fn main() {
    let mut v = Vec::new();
    grow(&mut v, unpinned_roundtrip(black_box(3)));
    grow(&mut v, pinned_roundtrip(black_box(4)));
    grow(&mut v, zst_box() as u64);
    println!("{}", v.iter().sum::<u64>());
}
