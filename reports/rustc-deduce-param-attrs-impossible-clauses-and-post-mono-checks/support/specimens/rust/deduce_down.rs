//! Downstream crate: calls every upstream function so that the upstream
//! symbols appear as `declare` lines, and instantiates the generic one.
extern crate deduce_up;
use deduce_up::*;
use std::cell::Cell;

#[inline(never)]
pub fn call_read_big_freeze(v: u64) -> u64 {
    read_big_freeze(BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_shared_borrow_big_freeze(v: u64) -> u64 {
    shared_borrow_big_freeze(BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_shared_borrow_big_cell(v: u64) -> u64 {
    shared_borrow_big_cell(BigCell(std::array::from_fn(|_| Cell::new(v))))
}
#[inline(never)]
pub fn call_raw_const_borrow_big_freeze(v: u64) -> u64 {
    raw_const_borrow_big_freeze(BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_mutate_local_copy_big_freeze(v: u64) -> u64 {
    mutate_local_copy_big_freeze(BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_forward_by_move_indirect(v: u64) -> u64 {
    forward_by_move_indirect(BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_mixed_read_then_forward(v: u64) -> u64 {
    mixed_read_then_forward(BigFreeze([v; 8]), BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_mixed_forward_then_read(v: u64) -> u64 {
    mixed_forward_then_read(BigFreeze([v; 8]), BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_generic_drop_only_string(s: &str) -> u64 {
    generic_drop_only::<String>(std::array::from_fn(|_| String::from(s)), 5)
}
#[inline(never)]
pub fn call_generic_drop_only_u64(v: u64) -> u64 {
    generic_drop_only::<u64>([v; 8], 7)
}
// Forwarding witness: the argument is a by-value copy of `*src`.  rustc lowers
// it as `memcpy(tmp, src); call read_big_copy(tmp)`.  Whether LLVM may pass
// `src` itself depends on the attributes of `read_big_copy`'s declaration,
// which is all the downstream crate knows about that function.
#[inline(never)]
pub fn forwarding_witness(src: &BigCopy) -> u64 {
    read_big_copy(*src)
}
// Variant that also reads `*src` after the call.  Recorded without a
// prediction: the extra read lets an earlier LLVM pass split the copy.
#[inline(never)]
pub fn forwarding_witness_split(src: &BigCopy) -> u64 {
    read_big_copy(*src).wrapping_add(src.0[3])
}
#[inline(never)]
pub fn call_ret_never_returns() -> u8 {
    ret_never_returns()[0]
}
#[inline(never)]
pub fn call_ret_not_captured(v: u8) -> u8 {
    ret_not_captured(v)[3]
}
#[inline(never)]
pub fn call_ret_captured(v: u8) -> u8 {
    ret_captured(v)[3]
}
