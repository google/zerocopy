// Reproducible probe inputs for layout queries, target constants, and const blocks.
#![allow(dead_code, unreachable_code, unused_variables, path_statements)]

use core::marker::PhantomData;
use core::mem::{align_of, align_of_val, offset_of, size_of, size_of_val};

pub struct ReprRustStruct {
    pub a: u8,
    pub b: u32,
    pub c: u16,
}

#[repr(C)]
pub struct ReprCStruct {
    pub a: u8,
    pub b: u32,
    pub c: u16,
}

pub struct NestedRust {
    pub tag: u8,
    pub inner: ReprRustStruct,
}

pub struct Wrapper<T> {
    pub prefix: u8,
    pub field: T,
}

#[repr(C)]
pub struct ReprCWrapper<T> {
    pub prefix: u8,
    pub field: T,
}

pub enum ReprRustEnum {
    A(u8),
    B(u64),
}

// ============================================================================
// Layout and target constant probes: size_of, align_of, size_of_val, align_of_val, offset_of!, consts
// ============================================================================

pub fn q2_1_size_align_mono() -> (usize, usize) {
    let s = size_of::<ReprRustStruct>();
    let a = align_of::<ReprRustStruct>();
    (s, a)
}

pub fn q2_1_size_align_generic<T>() -> (usize, usize) {
    let s = size_of::<T>();
    let a = align_of::<T>();
    (s, a)
}

pub fn q2_1_size_align_val_mono(v: &ReprRustStruct) -> (usize, usize) {
    let s = size_of_val(v);
    let a = align_of_val(v);
    (s, a)
}

pub fn q2_1_size_align_val_generic<T>(v: &T) -> (usize, usize) {
    let s = size_of_val(v);
    let a = align_of_val(v);
    (s, a)
}

pub fn q2_1_size_align_val_slice(v: &[ReprRustStruct]) -> (usize, usize) {
    let s = size_of_val(v);
    let a = align_of_val(v);
    (s, a)
}

pub fn q2_1_offset_of_mono() -> (usize, usize, usize) {
    let o_rust = offset_of!(ReprRustStruct, b);
    let o_c = offset_of!(ReprCStruct, b);
    let o_nested = offset_of!(NestedRust, inner.b);
    (o_rust, o_c, o_nested)
}

pub fn q2_1_offset_of_generic<T>() -> (usize, usize) {
    let o_rust = offset_of!(Wrapper<T>, field);
    let o_c = offset_of!(ReprCWrapper<T>, field);
    (o_rust, o_c)
}

pub fn q2_1_target_consts() -> (u32, usize, bool) {
    let bits = usize::BITS;
    let max = usize::MAX;
    let is_64 = cfg!(target_pointer_width = "64");
    (bits, max, is_64)
}

pub fn q2_1_const_block_size_of_mono() {
    const {
        assert!(size_of::<ReprRustStruct>() == 8);
    }
}

pub fn q2_1_const_block_size_of_generic<T>() {
    const {
        assert!(size_of::<T>() == 8);
    }
}

pub const NAMED_RUST_SIZE: usize = size_of::<ReprRustStruct>();

pub fn q2_1_layout_folding_pathways() -> (usize, usize, &'static usize) {
    // Pathway A: Named const item using size_of::<ReprRustStruct>()
    let from_named_const = NAMED_RUST_SIZE;
    // Pathway B: Array repeat count using size_of::<ReprRustStruct>()
    let arr = [0u8; size_of::<ReprRustStruct>()];
    // Pathway C: Promoted temporary borrowing size_of::<ReprRustStruct>()
    let promoted_ref: &'static usize = &size_of::<ReprRustStruct>();
    (from_named_const, arr.len(), promoted_ref)
}

// ============================================================================
// Const placement probes: Inline `const { ... }` and associated consts in live vs. dead CFG
// ============================================================================

pub fn q2_2a_value_const_block() -> usize {
    let x: usize = const { 1 + 2 };
    x
}

pub fn q2_2a_value_const_block_generic<T>() -> usize {
    let x: usize = const { size_of::<T>() + 1 };
    x
}

pub fn q2_2b_live_stmt_const_block<T>() {
    const {
        assert!(size_of::<T>() == 8);
    };
}

pub fn q2_2c_if_false_const_block<T>() {
    if false {
        const {
            assert!(size_of::<T>() == 8);
        };
    }
}

pub fn q2_2d_post_return_const_block<T>() {
    return;
    const {
        assert!(size_of::<T>() == 8);
    };
}

pub struct S<T>(PhantomData<T>);
impl<T> S<T> {
    pub const OK: () = assert!(size_of::<T>() == 8);
}

pub fn q2_2e_named_assoc_const_live<T>() {
    let _ = S::<T>::OK;
}

pub fn q2_2e_named_assoc_const_if_false<T>() {
    if false {
        let _ = S::<T>::OK;
    }
}

pub fn q2_2e_named_assoc_const_post_return<T>() {
    return;
    let _ = S::<T>::OK;
}

pub fn q2_2e_named_assoc_const_value_bind_dead<T>() {
    if false {
        let _x: () = S::<T>::OK;
    }
}
