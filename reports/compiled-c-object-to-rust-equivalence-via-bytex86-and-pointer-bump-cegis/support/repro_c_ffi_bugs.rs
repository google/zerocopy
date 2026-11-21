// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Linked Rust-calls-C hardware reproducer suite for the 4 classic compiled-C
//! FFI bugs in `c_ffi_bugs.c` (`gcc 15.2.0 -O2` `.o` linked as `-l static=cfibugs`).

#![allow(unsafe_op_in_unsafe_fn)]

use std::arch::asm;
use std::ptr;
use std::sync::atomic::{AtomicUsize, Ordering};

unsafe extern "C" {
    // Bug 1: C signature is `uint64_t c_bug1_int_len_endpoints(const uint8_t *buf, int len)`
    // while Rust FFI caller passes 64-bit `usize` in `%rsi`!
    fn c_bug1_int_len_endpoints(buf: *const u8, len: usize) -> u64;
    fn c_bug2_signed_char_fnv1a(buf: *const u8, len: usize) -> u64;
    fn c_bug3_off_by_one_xor(dst: *mut u8, src: *const u8, len: usize, key: u8);
    fn c_bug4_asm_clobber_abi(buf: *const u8, len: usize) -> u64;
}

// Minimal POSIX / glibc declarations (`0` external crate dependencies)
const PROT_NONE: i32 = 0x0;
const PROT_READ: i32 = 0x1;
const PROT_WRITE: i32 = 0x2;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;
const MAP_NORESERVE: i32 = 0x4000;
const SIGSEGV: i32 = 11;
const SA_SIGINFO: i32 = 0x00000004;
const SA_NODEFER: i32 = 0x40000000;

#[repr(C)]
struct SigInfoHeader {
    si_signo: i32,
    si_errno: i32,
    si_code: i32,
    _pad0: i32,
    si_addr: *mut u8,
    _rest: [u8; 104],
}

#[repr(C)]
struct SigSetJmpBuf {
    buf: [u64; 32],
}

#[repr(C)]
struct KernelSigSet {
    bits: [u64; 16],
}

#[repr(C)]
struct SigAction {
    sa_sigaction: usize,
    sa_mask: KernelSigSet,
    sa_flags: i32,
    sa_restorer: usize,
}

unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: isize) -> *mut u8;
    fn munmap(addr: *mut u8, len: usize) -> i32;
    fn mprotect(addr: *mut u8, len: usize, prot: i32) -> i32;
    fn sigaction(sig: i32, act: *const SigAction, oldact: *mut SigAction) -> i32;
    fn __sigsetjmp(env: *mut SigSetJmpBuf, savemask: i32) -> i32;
    fn siglongjmp(env: *mut SigSetJmpBuf, val: i32) -> !;
}

static mut JMP_ENV: SigSetJmpBuf = SigSetJmpBuf { buf: [0; 32] };
static FAULT_SIG: AtomicUsize = AtomicUsize::new(0);
static FAULT_ADDR: AtomicUsize = AtomicUsize::new(0);

extern "C" fn segv_handler(sig: i32, info: *const SigInfoHeader, _uctx: *mut u8) {
    unsafe {
        FAULT_SIG.store(sig as usize, Ordering::SeqCst);
        if !info.is_null() {
            FAULT_ADDR.store((*info).si_addr as usize, Ordering::SeqCst);
        }
        siglongjmp(&raw mut JMP_ENV, 1);
    }
}

pub fn rust_endpoints_u64(buf: &[u8]) -> u64 {
    match buf.len() {
        0 => 0,
        n => (buf[0] as u64) + (buf[n - 1] as u64),
    }
}

pub fn rust_fnv1a64(buf: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &b in buf {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

pub fn rust_xor_stream(dst: &mut [u8], src: &[u8], key: u8) {
    for (d, &s) in dst.iter_mut().zip(src.iter()) {
        *d = s ^ key;
    }
}

pub fn rust_sum_u8_to_u64(buf: &[u8]) -> u64 {
    buf.iter().fold(0u64, |acc, &b| acc.wrapping_add(b as u64))
}

#[test]
fn repro_bug1_int_len_truncation_2gib() {
    let len_2gib: usize = 0x8000_0000;
    unsafe {
        let base = mmap(
            ptr::null_mut(),
            len_2gib,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
            -1,
            0,
        );
        assert_ne!(base as isize, -1, "2 GiB MAP_NORESERVE mmap failed");
        *base.add(0) = 1;
        *base.add(len_2gib - 1) = 2;

        let slice = std::slice::from_raw_parts(base, len_2gib);
        let rust_ret = rust_endpoints_u64(slice);
        let c_ret = c_bug1_int_len_endpoints(base, len_2gib);

        let _ = munmap(base, len_2gib);

        assert_eq!(rust_ret, 3);
        assert_eq!(
            c_ret, 0,
            "Bug 1 reproduced: C `test esi, esi; jle` truncated 2 GiB usize to negative i32"
        );
        assert_ne!(c_ret, rust_ret);
    }
}

#[test]
fn repro_bug2_signed_char_sign_extension() {
    // ASCII byte < 0x80 agrees, masking the bug on ASCII-only tests:
    let ascii = [0x7fu8];
    let c_ascii = unsafe { c_bug2_signed_char_fnv1a(ascii.as_ptr(), ascii.len()) };
    assert_eq!(c_ascii, rust_fnv1a64(&ascii));

    // CaDiCaL minimal counterexample: len = 1, buf = [0x80]
    let hi_byte = [0x80u8];
    let rust_h = rust_fnv1a64(&hi_byte);
    let c_h = unsafe { c_bug2_signed_char_fnv1a(hi_byte.as_ptr(), hi_byte.len()) };
    assert_eq!(rust_h, 0xaf643d4c8602915f);
    assert_ne!(
        c_h, rust_h,
        "Bug 2 reproduced: `48 0f be 17` (`movsx rdx, BYTE PTR [rdi]`) sign-extended 0x80"
    );
}

#[test]
fn repro_bug3_off_by_one_canary_and_guard_page_sigsegv() {
    // Part A: CaDiCaL minimal witness `len = 0, src[0] = 0, key = 1` overwrites `dst[0]`!
    let mut dst_rust = [0xAAu8];
    let mut dst_c = [0xAAu8];
    let src = [0x00u8];
    rust_xor_stream(&mut dst_rust[..0], &src[..0], 0x01);
    unsafe {
        c_bug3_off_by_one_xor(dst_c.as_mut_ptr(), src.as_ptr(), 0, 0x01);
    }
    assert_eq!(dst_rust[0], 0xAA, "Safe Rust preserved canary at dst[0]");
    assert_eq!(
        dst_c[0], 0x01,
        "Bug 3 reproduced: C `i <= len` (`jae`) wrote out-of-bounds dst[0] at len = 0"
    );

    // Part B: Hardware `PROT_NONE` guard-page `SIGSEGV` at `len = 1`
    unsafe {
        let pages = mmap(
            ptr::null_mut(),
            8192,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            -1,
            0,
        );
        assert_ne!(pages as isize, -1);
        let guard = pages.add(4096);
        assert_eq!(mprotect(guard, 4096, PROT_NONE), 0);

        let src_end = pages.add(4095);
        let dst_ok = pages.add(0);
        *src_end = 0x42;
        *dst_ok = 0x00;

        // Safe Rust touches only `src_end[0]` (`len = 1`) and never faults:
        rust_xor_stream(
            std::slice::from_raw_parts_mut(dst_ok, 1),
            std::slice::from_raw_parts(src_end, 1),
            0xFF,
        );
        assert_eq!(*dst_ok, 0x42 ^ 0xFF);

        let mut old_act = std::mem::zeroed::<SigAction>();
        let act = SigAction {
            sa_sigaction: segv_handler as *const () as usize,
            sa_mask: KernelSigSet { bits: [0; 16] },
            sa_flags: SA_SIGINFO | SA_NODEFER,
            sa_restorer: 0,
        };
        assert_eq!(sigaction(SIGSEGV, &act, &mut old_act), 0);
        FAULT_SIG.store(0, Ordering::SeqCst);
        FAULT_ADDR.store(0, Ordering::SeqCst);

        if __sigsetjmp(&raw mut JMP_ENV, 1) == 0 {
            c_bug3_off_by_one_xor(dst_ok, src_end, 1, 0xFF);
        }

        assert_eq!(sigaction(SIGSEGV, &old_act, ptr::null_mut()), 0);
        let sig = FAULT_SIG.load(Ordering::SeqCst);
        let addr = FAULT_ADDR.load(Ordering::SeqCst);
        let _ = munmap(pages, 8192);

        assert_eq!(sig, SIGSEGV as usize, "Expected SIGSEGV on off-by-one overread");
        assert_eq!(addr, guard as usize, "Fault address must equal guard page start");
    }
}

#[test]
fn repro_bug4_callee_saved_and_upper_ymm_clobber() {
    // 16-byte input exercises GCC `-O2`'s Legacy Non-VEX SSE2 loop (`pxor`/`punpck*`/`paddq`),
    // proving empirically that Legacy SSE2 preserves the inline-asm's dirty `YMM0[255:128]`!
    let buf = [1u8; 16];
    let want_rax = rust_sum_u8_to_u64(&buf);
    assert_eq!(want_rax, 16);

    let rbx_in: u64 = 0x1122_3344_5566_7788;
    let r12_in: u64 = 0x99aa_bbcc_ddee_ff00;
    let mut rax_out: u64 = 0;
    let mut rbx_out: u64 = 0;
    let mut r12_out: u64 = 0;
    let mut ymm0_out = [0u8; 32];

    unsafe {
        asm!(
            "push rbx",
            "push r12",
            "push r13",
            "mov r13, rdx",
            "vzeroupper",
            "mov rbx, rcx",
            "mov r12, r8",
            "call {callee}",
            "vmovdqu ymmword ptr [r13], ymm0",
            "vzeroupper",
            "mov rcx, rbx",
            "mov rdx, r12",
            "pop r13",
            "pop r12",
            "pop rbx",
            callee = sym c_bug4_asm_clobber_abi,
            in("rdi") buf.as_ptr(),
            in("rsi") buf.len(),
            inout("rdx") ymm0_out.as_mut_ptr() => r12_out,
            inout("rcx") rbx_in => rbx_out,
            in("r8") r12_in,
            lateout("rax") rax_out,
            clobber_abi("C"),
        );
    }

    assert_eq!(
        rax_out, want_rax,
        "Return value matches safe Rust 100%, hiding the ABI bug from value-only tests"
    );
    assert_eq!(
        rbx_out, 0xdead_beef_cafe_babe,
        "Bug 4 reproduced: callee-saved %rbx clobbered across FFI boundary"
    );
    assert_eq!(
        r12_out,
        r12_in.wrapping_add(1),
        "Bug 4 reproduced: callee-saved %r12 incremented across FFI boundary"
    );
    assert_eq!(
        &ymm0_out[16..32],
        &[0xFFu8; 16],
        "Bug 4 reproduced: YMM0[255:128] remained dirty across GCC -O2's Legacy SSE2 loop"
    );
}
