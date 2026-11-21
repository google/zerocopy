#![feature(asm_unwind)]
#![allow(dead_code, unused_variables, unused_assignments, unreachable_code)]

use std::arch::asm;

pub struct DropGuard<'a>(pub &'a mut u32, pub u32);

impl<'a> Drop for DropGuard<'a> {
    #[inline(never)]
    fn drop(&mut self) {
        *self.0 += self.1;
    }
}

#[inline(never)]
pub fn maybe_panic_rust(should_panic: bool) -> u32 {
    if should_panic {
        panic!("rust callee panic");
    }
    7
}

unsafe extern "C" {
    fn opaque_c_nounwind(x: u32) -> u32;
}

unsafe extern "C-unwind" {
    fn opaque_c_unwind(x: u32) -> u32;
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn rust_defined_c_unwind(should_panic: bool) -> u32 {
    if should_panic {
        panic!("rust-defined C-unwind panic");
    }
    11
}

#[derive(Copy, Clone)]
pub enum Two {
    A(u32),
    B(bool),
}

/// 1. Match with guard and FakeBorrow/FakeRead(ForMatchGuard, ForGuardBinding) + FalseEdge
#[inline(never)]
pub fn specimen_match_guard(mut x: Two, flag: bool) -> u32 {
    match x {
        Two::A(v) if {
            let _ = v;
            flag
        } => {
            x = Two::B(false);
            let _ = x;
            v + 1
        }
        Two::A(v) => v + 2,
        Two::B(b) if b => 10,
        Two::B(_) => 20,
    }
}

/// 2. Let-ascription (`AscribeUserType`), array-to-pointer and mut-to-const pointer coercions
#[inline(never)]
pub fn specimen_ascribe_and_ptr_coercions(buf: &mut [u32; 3], x: &u32) -> *const u32 {
    let a: &u32 = x;
    let b: u32 = *a;
    let arr_ref: &[u32; 3] = buf;
    let arr_to_ptr: *const u32 = arr_ref as *const u32;
    let slice_ref: &[u32] = arr_ref;
    let elem_ptr: *const u32 = slice_ref.as_ptr();
    let raw_mut: *mut [u32; 3] = buf;
    let raw_const: *const [u32; 3] = raw_mut;
    let _ = (b, arr_to_ptr, raw_const, elem_ptr);
    arr_to_ptr
}

/// 3. Let-underscore PlaceMention vs named-let value load
#[inline(never)]
pub unsafe fn specimen_place_mention_only(p: *const bool) {
    unsafe {
        let _ = *p;
    }
}

/// 4. Refutable wildcard match generating PlaceMention + FakeRead(ForMatchedPlace)
#[inline(never)]
pub unsafe fn specimen_wildcard_match_place_mention(p: *const bool) -> u32 {
    unsafe {
        match *p {
            _ => 42,
        }
    }
}

/// 5. Infinite loop creating `FalseUnwind` in analysis MIR
#[inline(never)]
pub fn specimen_loop_false_unwind(mut n: u32) -> u32 {
    loop {
        if n == 0 {
            return 99;
        }
        n -= 1;
    }
}

/// 6. Nested slice indexing generating `FakeBorrowKind::Shallow` + `FakeRead(ForIndex)`
#[inline(never)]
pub fn specimen_nested_index_fake_borrow(s: &mut [&mut [u32]], i: usize, j: usize) -> u32 {
    s[i][j] += 1;
    s[i][j]
}

/// 7. Callers exercising AbortUnwindingCalls across caller ABI x callee ABI x DropGuard
#[inline(never)]
pub fn caller_rust_calls_rust_with_drop(log: &mut u32, p: bool) -> u32 {
    let _g = DropGuard(log, 1);
    maybe_panic_rust(p)
}

#[inline(never)]
pub fn caller_rust_calls_rust_no_drop(p: bool) -> u32 {
    maybe_panic_rust(p)
}

#[inline(never)]
pub unsafe extern "C" fn caller_extern_c_calls_rust_with_drop(log: &mut u32, p: bool) -> u32 {
    let _g = DropGuard(log, 2);
    maybe_panic_rust(p)
}

#[inline(never)]
pub unsafe extern "C" fn caller_extern_c_calls_rust_no_drop(p: bool) -> u32 {
    maybe_panic_rust(p)
}

#[inline(never)]
pub unsafe extern "C" fn caller_extern_c_calls_foreign_c_unwind_with_drop(
    log: &mut u32,
    x: u32,
) -> u32 {
    let _g = DropGuard(log, 4);
    unsafe { opaque_c_unwind(x) }
}

#[inline(never)]
pub unsafe extern "C" fn caller_extern_c_calls_foreign_c_unwind_no_drop(x: u32) -> u32 {
    unsafe { opaque_c_unwind(x) }
}

#[inline(never)]
pub unsafe extern "C-unwind" fn caller_extern_c_unwind_calls_foreign_c_unwind_with_drop(
    log: &mut u32,
    x: u32,
) -> u32 {
    let _g = DropGuard(log, 8);
    unsafe { opaque_c_unwind(x) }
}

#[inline(never)]
pub unsafe extern "C" fn caller_extern_c_calls_foreign_c_nounwind_with_drop(
    log: &mut u32,
    x: u32,
) -> u32 {
    let _g = DropGuard(log, 16);
    unsafe { opaque_c_nounwind(x) }
}

#[inline(never)]
pub unsafe fn caller_rust_calls_fnptr_c_unwind_with_drop(
    log: &mut u32,
    f: unsafe extern "C-unwind" fn(u32) -> u32,
    x: u32,
) -> u32 {
    let _g = DropGuard(log, 32);
    unsafe { f(x) }
}

#[inline(never)]
pub unsafe fn caller_rust_calls_fnptr_c_unwind_no_drop(
    f: unsafe extern "C-unwind" fn(u32) -> u32,
    x: u32,
) -> u32 {
    unsafe { f(x) }
}

#[inline(never)]
pub fn caller_rust_calls_rust_defined_c_unwind_with_drop(log: &mut u32, p: bool) -> u32 {
    let _g = DropGuard(log, 64);
    rust_defined_c_unwind(p)
}

#[inline(never)]
pub unsafe fn caller_rust_inline_asm_may_unwind_with_drop(log: &mut u32) {
    let _g = DropGuard(log, 128);
    unsafe {
        asm!("nop", options(may_unwind));
    }
}

#[inline(never)]
pub fn caller_rust_assert_overflow_with_drop(log: &mut u32, a: u32, b: u32) -> u32 {
    let _g = DropGuard(log, 256);
    a + b
}
