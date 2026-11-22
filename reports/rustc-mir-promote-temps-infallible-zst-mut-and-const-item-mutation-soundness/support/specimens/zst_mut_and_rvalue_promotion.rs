#![allow(dead_code, useless_ptr_null_checks)]

#[inline(never)]
pub fn probe_three_promoteds() -> (&'static mut [u32], &'static mut [u32; 0], &'static [u32; 2]) {
    let a: &'static mut [u32] = &mut [];
    let b: &'static mut [u32; 0] = &mut [];
    let c: &'static [u32; 2] = &[10 + 1, 20 * 2];
    (a, b, c)
}

#[inline(never)]
fn dual_protected_zst_mut(x: &mut [u32], y: &mut [u32]) -> bool {
    x.len() == 0 && y.len() == 0 && core::ptr::eq(x.as_mut_ptr(), y.as_mut_ptr())
}

fn main() {
    let (a, b, c) = probe_three_promoteds();
    let nz = !a.as_ptr().is_null();
    let (x, y) = a.split_at_mut(0);
    let same_alloc_dual_protected = dual_protected_zst_mut(x, y);
    println!("PROMOTED_OK={} NZ={} C={:?}", b.is_empty() && same_alloc_dual_protected, nz, c);
}
