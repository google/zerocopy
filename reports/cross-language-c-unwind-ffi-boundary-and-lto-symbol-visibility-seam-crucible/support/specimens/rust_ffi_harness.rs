// Rust harness for cross-language C-unwind / C unwinding matrix,
// i128/u128 SysV ABI parity (against clang C++17 and gcc C17), and
// cross-language ThinLTO inlining verification.

use std::mem::{align_of, offset_of, size_of};
use std::panic::{catch_unwind, AssertUnwindSafe};

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

fn trace_event(tag: &str) {
    let mut buf = [0u8; 128];
    let prefix = b"[TRACE] ";
    let tb = tag.as_bytes();
    let total = prefix.len() + tb.len() + 1;
    if total <= buf.len() {
        buf[..prefix.len()].copy_from_slice(prefix);
        buf[prefix.len()..prefix.len() + tb.len()].copy_from_slice(tb);
        buf[prefix.len() + tb.len()] = b'\n';
        unsafe {
            let _ = write(2, buf.as_ptr(), total);
        }
    }
}

struct RustGuard {
    counter: *mut i32,
    tag: &'static str,
}

impl Drop for RustGuard {
    fn drop(&mut self) {
        unsafe {
            if !self.counter.is_null() {
                *self.counter += 1;
            }
        }
        trace_event(self.tag);
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pair48 {
    pub tag: u8,
    pub big: u128,
    pub tail: u64,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mixed64 {
    pub a: u8,
    pub u: u128,
    pub b: u32,
    pub s: i128,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LayoutReport {
    pub size: u64,
    pub align: u64,
    pub off0: u64,
    pub off1: u64,
    pub off2: u64,
    pub off3: u64,
}

unsafe extern "C-unwind" {
    fn cpp_throw_code(code: i32, trace_dtor: i32) -> !;
    fn cpp_try_call_rust(fn_ptr: unsafe extern "C-unwind" fn(*mut i32) -> i32, drops: *mut i32) -> i32;
    fn cpp_raii_then_rust_panic(rust_fn: extern "C-unwind" fn(), cpp_dtors: *mut i32);
    fn cpp_raii_then_throw(code: i32, cpp_dtors: *mut i32) -> !;
    fn cpp_try_rust_catch_unwind(
        rust_fn: unsafe extern "C-unwind" fn(*mut i32, *mut i32) -> i32,
        rust_drops: *mut i32,
        cpp_dtors: *mut i32,
    ) -> i32;
}

unsafe extern "C" {
    #[allow(clashing_extern_declarations)]
    #[link_name = "cpp_try_call_rust"]
    fn cpp_try_call_rust_nounwind(fn_ptr: unsafe extern "C" fn(*mut i32) -> i32, drops: *mut i32) -> i32;
    #[allow(clashing_extern_declarations)]
    #[link_name = "cpp_throw_code"]
    fn cpp_throw_code_nounwind(code: i32, trace_dtor: i32) -> !;

    fn cpp_inspect_pair48_layout() -> LayoutReport;
    fn cpp_inspect_mixed64_layout() -> LayoutReport;
    fn cpp_pass_pair48_byval(p: Pair48) -> u128;
    fn cpp_ret_pair48_sret(tag: u8, big: u128, tail: u64) -> Pair48;
    fn cpp_pass_mixed64_byval(m: Mixed64) -> u128;
    fn cpp_ret_mixed64_sret(a: u8, u: u128, b: u32, s: i128) -> Mixed64;
    fn cpp_add_pair_128(a: u128, b: i128) -> u128;
    fn cpp_unaligned_gpr_128(tag: u8, a: u128, b: i128) -> i128;
    fn cpp_spill_5gpr_128(
        g0: u64, g1: u64, g2: u64, g3: u64, g4: u64,
        stack_val: u128, r9_tail: u64,
    ) -> u128;

    fn gcc_inspect_pair48_layout() -> LayoutReport;
    fn gcc_inspect_mixed64_layout() -> LayoutReport;
    fn gcc_spill_5gpr_128(
        g0: u64, g1: u64, g2: u64, g3: u64, g4: u64,
        stack_val: u128, r9_tail: u64,
    ) -> u128;
    fn gcc_unaligned_gpr_128(tag: u8, a: u128, b: i128) -> i128;

    fn cpp_vis_default_fn(x: u64) -> u64;
    fn cpp_vis_hidden_fn(x: u64) -> u64;
    fn cpp_thinlto_leaf_mul_add128(a: u128, b: u128) -> u128;
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C-unwind" fn rust_c_unwind_with_guard(rust_drops: *mut i32) -> i32 {
    let _g = RustGuard { counter: rust_drops, tag: "rust_c_unwind_guard_drop" };
    unsafe { cpp_throw_code(42, 0) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C-unwind" fn rust_c_unwind_no_guard(_rust_drops: *mut i32) -> i32 {
    unsafe { cpp_throw_code(42, 0) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn rust_panic_target() {
    trace_event("rust_panicking_in_c_unwind");
    panic!("intentional rust C-unwind panic");
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C-unwind" fn rust_catch_cpp_throw_inner(
    rust_drops: *mut i32,
    cpp_dtors: *mut i32,
) -> i32 {
    let res = catch_unwind(AssertUnwindSafe(|| {
        let _rg = RustGuard { counter: rust_drops, tag: "rust_inner_catch_guard_drop" };
        unsafe { cpp_raii_then_throw(77, cpp_dtors) }
    }));
    if res.is_err() {
        trace_event("rust_caught_unexpectedly");
        1
    } else {
        0
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn rust_extern_c_nounwind_with_guard(rust_drops: *mut i32) -> i32 {
    let _g = RustGuard { counter: rust_drops, tag: "rust_nounwind_guard_drop" };
    unsafe { cpp_throw_code_nounwind(42, 0) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn rust_call_cpp_thinlto_leaf(a: u128, b: u128) -> u128 {
    unsafe { cpp_thinlto_leaf_mul_add128(a, b) + 1 }
}

fn run_i128_abi_suite() {
    let rust_p48 = LayoutReport {
        size: size_of::<Pair48>() as u64,
        align: align_of::<Pair48>() as u64,
        off0: offset_of!(Pair48, tag) as u64,
        off1: offset_of!(Pair48, big) as u64,
        off2: offset_of!(Pair48, tail) as u64,
        off3: 0,
    };
    let cpp_p48 = unsafe { cpp_inspect_pair48_layout() };
    let gcc_p48 = unsafe { gcc_inspect_pair48_layout() };

    let rust_m64 = LayoutReport {
        size: size_of::<Mixed64>() as u64,
        align: align_of::<Mixed64>() as u64,
        off0: offset_of!(Mixed64, a) as u64,
        off1: offset_of!(Mixed64, u) as u64,
        off2: offset_of!(Mixed64, b) as u64,
        off3: offset_of!(Mixed64, s) as u64,
    };
    let cpp_m64 = unsafe { cpp_inspect_mixed64_layout() };
    let gcc_m64 = unsafe { gcc_inspect_mixed64_layout() };

    let a128: u128 = 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210u128;
    let b128: i128 = -0x0011_2233_4455_6677_8899_aabb_ccdd_eeff_i128;
    let p48 = Pair48 { tag: 0x2a, big: a128, tail: 0x9988_7766_5544_3322u64 };
    let expected_pass48 = p48.big.wrapping_add(p48.tag as u128).wrapping_add(p48.tail as u128);
    let got_pass48 = unsafe { cpp_pass_pair48_byval(p48) };
    let got_ret48 = unsafe { cpp_ret_pair48_sret(0x2a, a128, 100) };
    let exp_ret48 = Pair48 { tag: 0x2a, big: a128 ^ (0x55aau128 << 64), tail: 111 };

    let m64 = Mixed64 { a: 0x7f, u: a128, b: 0xdead_beef, s: b128 };
    let got_pass64 = unsafe { cpp_pass_mixed64_byval(m64) };
    let exp_pass64 = m64.u ^ (m64.s as u128) ^ (((m64.b as u128) << 64) | (m64.a as u128));
    let got_ret64 = unsafe { cpp_ret_mixed64_sret(0x7f, a128, 0x100, b128) };
    let exp_ret64 = Mixed64 { a: 0x7f, u: a128 + 3, b: 0x105, s: b128 - 7 };

    let got_add = unsafe { cpp_add_pair_128(a128, b128) };
    let exp_add = a128.wrapping_add(b128 as u128).wrapping_add(7);

    let got_unaligned_cpp = unsafe { cpp_unaligned_gpr_128(0x5a, a128, b128) };
    let got_unaligned_gcc = unsafe { gcc_unaligned_gpr_128(0x5a, a128, b128) };
    let exp_unaligned = ((a128 ^ 0x5au128) as i128).wrapping_sub(b128);

    let got_spill_cpp = unsafe {
        cpp_spill_5gpr_128(0x11, 0x22, 0x33, 0x44, 0x55, a128, 0x8000_0000_0000_0007u64)
    };
    let got_spill_gcc = unsafe {
        gcc_spill_5gpr_128(0x11, 0x22, 0x33, 0x44, 0x55, a128, 0x8000_0000_0000_0007u64)
    };
    let xor_tail = 0x11u64 ^ 0x22 ^ 0x33 ^ 0x44 ^ 0x55 ^ 0x8000_0000_0000_0007u64;
    let exp_spill = a128.wrapping_add(xor_tail as u128);

    let match_all = rust_p48 == cpp_p48
        && rust_p48 == gcc_p48
        && rust_m64 == cpp_m64
        && rust_m64 == gcc_m64
        && got_pass48 == expected_pass48
        && got_ret48 == exp_ret48
        && got_pass64 == exp_pass64
        && got_ret64 == exp_ret64
        && got_add == exp_add
        && got_unaligned_cpp == exp_unaligned
        && got_unaligned_gcc == exp_unaligned
        && got_spill_cpp == exp_spill
        && got_spill_gcc == exp_spill;

    let vis_sum = unsafe { cpp_vis_default_fn(3) + cpp_vis_hidden_fn(4) };
    println!(
        "I128_SZ={} I128_AL={} P48_RUST=({},{},{},{},{}) P48_CPP=({},{},{},{},{}) P48_GCC=({},{},{},{},{}) M64_RUST=({},{},{},{},{},{}) M64_CPP=({},{},{},{},{},{}) M64_GCC=({},{},{},{},{},{}) SPILL_CPP_OK={} SPILL_GCC_OK={} MATCH={} VIS_SUM={}",
        size_of::<u128>(),
        align_of::<u128>(),
        rust_p48.size, rust_p48.align, rust_p48.off0, rust_p48.off1, rust_p48.off2,
        cpp_p48.size, cpp_p48.align, cpp_p48.off0, cpp_p48.off1, cpp_p48.off2,
        gcc_p48.size, gcc_p48.align, gcc_p48.off0, gcc_p48.off1, gcc_p48.off2,
        rust_m64.size, rust_m64.align, rust_m64.off0, rust_m64.off1, rust_m64.off2, rust_m64.off3,
        cpp_m64.size, cpp_m64.align, cpp_m64.off0, cpp_m64.off1, cpp_m64.off2, cpp_m64.off3,
        gcc_m64.size, gcc_m64.align, gcc_m64.off0, gcc_m64.off1, gcc_m64.off2, gcc_m64.off3,
        got_spill_cpp == exp_spill,
        got_spill_gcc == exp_spill,
        match_all,
        vis_sum,
    );
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "cell1_cpp_through_rust_c_unwind" => {
            let mut rust_drops: i32 = 0;
            let rc = unsafe { cpp_try_call_rust(rust_c_unwind_with_guard, &mut rust_drops) };
            println!("RC={rc} RUST_DROPS={rust_drops}");
        }
        "cell2_rust_panic_through_cpp_raii" => {
            let mut cpp_dtors: i32 = 0;
            let res = catch_unwind(AssertUnwindSafe(|| unsafe {
                cpp_raii_then_rust_panic(rust_panic_target, &mut cpp_dtors);
            }));
            let caught = res.is_err();
            if caught {
                trace_event("rust_caught_panic");
            }
            println!("CAUGHT={caught} CPP_DTORS={cpp_dtors}");
        }
        "cell3_rust_catch_unwind_on_cpp" => {
            let mut rust_drops: i32 = 0;
            let mut cpp_dtors: i32 = 0;
            let rc = unsafe {
                cpp_try_rust_catch_unwind(rust_catch_cpp_throw_inner, &mut rust_drops, &mut cpp_dtors)
            };
            println!("RC={rc} RUST_DROPS={rust_drops} CPP_DTORS={cpp_dtors}");
        }
        "cell4a_c_unwind_no_guard" => {
            let mut rust_drops: i32 = 0;
            let rc = unsafe { cpp_try_call_rust(rust_c_unwind_no_guard, &mut rust_drops) };
            println!("RC={rc} RUST_DROPS={rust_drops}");
        }
        "cell5_extern_c_nounwind_throw" => {
            let mut rust_drops: i32 = 0;
            let rc = unsafe { cpp_try_call_rust_nounwind(rust_extern_c_nounwind_with_guard, &mut rust_drops) };
            println!("RC={rc} RUST_DROPS={rust_drops}");
        }
        "i128_abi" => {
            run_i128_abi_suite();
        }
        "xlang_thinlto" => {
            let a = std::hint::black_box(10u128);
            let b = std::hint::black_box(20u128);
            let res = rust_call_cpp_thinlto_leaf(a, b);
            println!("THINLTO_SUM={res}");
        }
        other => {
            eprintln!("unknown mode: {other}");
            std::process::exit(2);
        }
    }
}
