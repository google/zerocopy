#![no_std]
#![crate_type = "rlib"]
use core::arch::{asm, naked_asm};

pub unsafe fn pure_nomem_add(a: u64, b: u64) -> u64 {
    let out: u64;
    unsafe {
        asm!(
            "lea {out}, [{a} + {b}]",
            a = in(reg) a,
            b = in(reg) b,
            out = lateout(reg) out,
            options(pure, nomem, nostack, preserves_flags),
        );
    }
    out
}

pub unsafe fn clobber_c_abi_call(fn_ptr: extern "C" fn(u64) -> u64, arg: u64) -> u64 {
    let ret: u64;
    unsafe {
        asm!(
            "call {callee}",
            callee = in(reg) fn_ptr,
            in("rdi") arg,
            lateout("rax") ret,
            clobber_abi("C"),
        );
    }
    ret
}

#[unsafe(naked)]
pub unsafe extern "C" fn naked_identity(x: u64) -> u64 {
    naked_asm!(
        "mov rax, rdi",
        "ret",
    )
}
