#![feature(core_intrinsics, f16, f128)]
#![allow(internal_features)]
#![cfg_attr(not(miri), no_std)]
#![cfg_attr(not(miri), no_main)]

#[cfg(not(miri))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[inline(never)]
pub fn bb<T>(x: T) -> T {
    core::hint::black_box(x)
}

#[inline(never)]
pub extern "Rust" fn rust_abi_return_f32(x: f32) -> f32 {
    core::hint::black_box(x)
}

#[inline(never)]
pub extern "C" fn c_abi_return_f32(x: f32) -> f32 {
    core::hint::black_box(x)
}

pub const CTFE_ZERO_DIV_ZERO_F32: u32 = (0.0_f32 / 0.0_f32).to_bits();
pub const CTFE_QNAN1_PLUS_QNAN2: u32 = (f32::from_bits(0x7fc0_0001) + f32::from_bits(0x7fc0_0002)).to_bits();
pub const CTFE_SNAN_PLUS_ONE: u32 = (f32::from_bits(0x7f80_0001) + 1.0_f32).to_bits();
pub const CTFE_NEG_SNAN: u32 = (-f32::from_bits(0x7f80_0001)).to_bits();

#[repr(C)]
pub struct FloatObs {
    pub ctfe_zero_div_zero: u32,
    pub rt_zero_div_zero: u32,
    pub rt_qnan1_plus_qnan2: u32,
    pub rt_qnan2_plus_qnan1: u32,
    pub rt_snan_plus_one: u32,
    pub rt_neg_snan: u32,
    pub rt_min_qnan_one: u32,
    pub rt_min_snan_one: u32,
    pub rt_rust_abi_snan: u32,
    pub rt_c_abi_snan: u32,
    pub rt_cast_nan_i32: i32,
    pub rt_cast_pos_inf_i32: i32,
    pub rt_cast_neg_inf_i32: i32,
}

pub fn collect_obs() -> FloatObs {
    let z = bb(0.0_f32);
    let qnan1 = bb(f32::from_bits(0x7fc0_0001));
    let qnan2 = bb(f32::from_bits(0x7fc0_0002));
    let snan = bb(f32::from_bits(0x7f80_0001));
    let one = bb(1.0_f32);
    FloatObs {
        ctfe_zero_div_zero: CTFE_ZERO_DIV_ZERO_F32,
        rt_zero_div_zero: (z / z).to_bits(),
        rt_qnan1_plus_qnan2: (qnan1 + qnan2).to_bits(),
        rt_qnan2_plus_qnan1: (qnan2 + qnan1).to_bits(),
        rt_snan_plus_one: (snan + one).to_bits(),
        rt_neg_snan: (-snan).to_bits(),
        rt_min_qnan_one: qnan1.min(one).to_bits(),
        rt_min_snan_one: snan.min(one).to_bits(),
        rt_rust_abi_snan: rust_abi_return_f32(f32::from_bits(bb(0x7f80_0001))).to_bits(),
        rt_c_abi_snan: c_abi_return_f32(f32::from_bits(bb(0x7f80_0001))).to_bits(),
        rt_cast_nan_i32: qnan1 as i32,
        rt_cast_pos_inf_i32: bb(f32::INFINITY) as i32,
        rt_cast_neg_inf_i32: bb(f32::NEG_INFINITY) as i32,
    }
}

fn hex_u32(mut v: u32, out: &mut [u8; 8]) {
    let digits = b"0123456789abcdef";
    let mut i = 8;
    while i > 0 {
        i -= 1;
        out[i] = digits[(v & 0xf) as usize];
        v >>= 4;
    }
}

#[cfg(miri)]
fn main() {
    let o = collect_obs();
    println!(
        "ctfe_0div0={:#010x} rt_0div0={:#010x} q1+q2={:#010x} q2+q1={:#010x} snan+1={:#010x} neg_snan={:#010x} min_q={:#010x} min_s={:#010x} rust_abi={:#010x} c_abi={:#010x} cast=({},{},{})",
        o.ctfe_zero_div_zero,
        o.rt_zero_div_zero,
        o.rt_qnan1_plus_qnan2,
        o.rt_qnan2_plus_qnan1,
        o.rt_snan_plus_one,
        o.rt_neg_snan,
        o.rt_min_qnan_one,
        o.rt_min_snan_one,
        o.rt_rust_abi_snan,
        o.rt_c_abi_snan,
        o.rt_cast_nan_i32,
        o.rt_cast_pos_inf_i32,
        o.rt_cast_neg_inf_i32,
    );
}

#[cfg(not(miri))]
#[no_mangle]
#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(".globl _start", "_start:", "and rsp, -16", "call run_entry");
#[cfg(target_arch = "x86")]
core::arch::global_asm!(".globl _start", "_start:", "and esp, -16", "call run_entry");
#[cfg(target_arch = "aarch64")]
core::arch::global_asm!(".globl _start", "_start:", "bl run_entry");

#[no_mangle]
pub unsafe extern "C" fn run_entry() -> ! {
    let o = collect_obs();
    let vals = [
        o.ctfe_zero_div_zero,
        o.rt_zero_div_zero,
        o.rt_qnan1_plus_qnan2,
        o.rt_qnan2_plus_qnan1,
        o.rt_snan_plus_one,
        o.rt_neg_snan,
        o.rt_min_qnan_one,
        o.rt_min_snan_one,
        o.rt_rust_abi_snan,
        o.rt_c_abi_snan,
        o.rt_cast_nan_i32 as u32,
        o.rt_cast_pos_inf_i32 as u32,
        o.rt_cast_neg_inf_i32 as u32,
    ];
    let mut buf = [b' '; 13 * 9];
    let mut idx = 0;
    while idx < 13 {
        let mut h = [0u8; 8];
        hex_u32(vals[idx], &mut h);
        let base = idx * 9;
        let mut j = 0;
        while j < 8 {
            buf[base + j] = h[j];
            j += 1;
        }
        buf[base + 8] = if idx == 12 { b'\n' } else { b',' };
        idx += 1;
    }
    #[cfg(target_arch = "aarch64")]
    core::arch::asm!(
        "mov x8, #64",
        "mov x0, #1",
        "svc #0",
        "mov x8, #94",
        "mov x0, #0",
        "svc #0",
        in("x1") buf.as_ptr(),
        in("x2") buf.len(),
        options(noreturn)
    );
    #[cfg(target_arch = "x86")]
    core::arch::asm!(
        "mov eax, 4",
        "mov ebx, 1",
        "int 0x80",
        "mov eax, 252",
        "xor ebx, ebx",
        "int 0x80",
        in("ecx") buf.as_ptr(),
        in("edx") buf.len(),
        options(noreturn)
    );
    #[cfg(target_arch = "x86_64")]
    core::arch::asm!(
        "mov rax, 1",
        "mov rdi, 1",
        "syscall",
        "mov rax, 231",
        "xor rdi, rdi",
        "syscall",
        in("rsi") buf.as_ptr(),
        in("rdx") buf.len(),
        options(noreturn)
    );
}

#[cfg(not(miri))]
#[no_mangle]
pub unsafe extern "C" fn rust_eh_personality() {}

#[cfg(not(miri))]
#[no_mangle]
pub unsafe extern "C" fn memset(dst: *mut u8, val: i32, count: usize) -> *mut u8 {
    let mut i = 0;
    while i < count {
        core::ptr::write_volatile(dst.add(i), val as u8);
        i += 1;
    }
    dst
}

#[cfg(not(miri))]
#[no_mangle]
pub unsafe extern "C" fn memcpy(dst: *mut u8, src: *const u8, count: usize) -> *mut u8 {
    let mut i = 0;
    while i < count {
        core::ptr::write_volatile(dst.add(i), core::ptr::read_volatile(src.add(i)));
        i += 1;
    }
    dst
}
