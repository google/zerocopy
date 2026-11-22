//! Upstream crate: by-value parameters large enough to be passed by hidden
//! pointer (`PassMode::Indirect`) under the Rust ABI on x86-64.
#![allow(unused)]
use std::cell::Cell;
use std::hint::black_box;

/// 64 bytes, align 8, `Freeze`, no drop glue.
pub struct BigFreeze(pub [u64; 8]);
/// 64 bytes, align 8, NOT `Freeze` (`Cell` wraps `UnsafeCell`), no drop glue.
pub struct BigCell(pub [Cell<u64>; 8]);

/// 64 bytes, align 8, `Freeze`, `Copy`: used only by the forwarding witness.
#[derive(Clone, Copy)]
pub struct BigCopy(pub [u64; 8]);

// Only reads of the parameter.
#[inline(never)]
pub fn read_big_freeze(x: BigFreeze) -> u64 {
    x.0[0].wrapping_add(x.0[7])
}

// Only reads of a `Copy` parameter (callee of the forwarding witness).
#[inline(never)]
pub fn read_big_copy(x: BigCopy) -> u64 {
    x.0[0].wrapping_add(x.0[7])
}

// `&x` where the parameter type is `Freeze`.
#[inline(never)]
pub fn shared_borrow_big_freeze(x: BigFreeze) -> u64 {
    black_box(&x);
    x.0[0]
}

// `&x` where the parameter type is not `Freeze`.
#[inline(never)]
pub fn shared_borrow_big_cell(x: BigCell) -> u64 {
    black_box(&x);
    x.0[0].get()
}

// `&raw const x`.
#[inline(never)]
pub fn raw_const_borrow_big_freeze(x: BigFreeze) -> u64 {
    black_box(&raw const x);
    x.0[0]
}

// In-place store into the parameter at a data-dependent index (so no MIR pass
// can prove the store dead), with no borrow of the parameter.
#[inline(never)]
pub fn mutate_local_copy_big_freeze(mut x: BigFreeze) -> u64 {
    let i = (x.0[0] & 7) as usize;
    x.0[i] = 0xdead;
    x.0[0] ^ x.0[7]
}

// The parameter is only dropped, as a whole local.
#[inline(never)]
pub fn generic_drop_only<T>(_x: [T; 8], flag: u64) -> u64 {
    flag.wrapping_mul(3)
}

#[inline(never)]
pub fn sink_big_freeze(x: BigFreeze) -> u64 {
    x.0[1]
}

// The parameter is forwarded as a by-move call argument.
#[inline(never)]
pub fn forward_by_move_indirect(x: BigFreeze) -> u64 {
    sink_big_freeze(x)
}

// Two indirect parameters: the first is only read, the second is forwarded.
#[inline(never)]
pub fn mixed_read_then_forward(a: BigFreeze, b: BigFreeze) -> u64 {
    a.0[0].wrapping_add(sink_big_freeze(b))
}

// Two indirect parameters: the first is forwarded, the second is only read.
#[inline(never)]
pub fn mixed_forward_then_read(a: BigFreeze, b: BigFreeze) -> u64 {
    sink_big_freeze(a).wrapping_add(b.0[0])
}

// Indirect return place that is never written in MIR.
#[inline(never)]
pub fn ret_never_returns() -> [u8; 80] {
    loop {}
}

// Indirect return place written by a plain assignment.
#[inline(never)]
pub fn ret_not_captured(v: u8) -> [u8; 80] {
    [v; 80]
}

// Indirect return place used as the destination of a call.
#[inline(never)]
pub fn ret_captured(v: u8) -> [u8; 80] {
    black_box([v; 80])
}
