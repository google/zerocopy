// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(unsafe_op_in_unsafe_fn)]

use core::arch::asm;
use core::arch::x86_64::*;
use std::sync::Mutex;

static SIG_TEST_LOCK: Mutex<()> = Mutex::new(());

const PROT_READ: i32 = 1;
const PROT_WRITE: i32 = 2;
const PROT_NONE: i32 = 0;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;
const SIGSEGV: i32 = 11;
const SA_SIGINFO: i32 = 4;
const SA_NODEFER: i32 = 0x40000000;

#[repr(C)]
struct SigInfoPrefix {
    si_signo: i32,
    si_errno: i32,
    si_code: i32,
    _pad0: i32,
    si_addr: usize,
    _pad: [u8; 128],
}

#[repr(C)]
struct KernelSigAction {
    sa_sigaction: usize,
    sa_flags: usize,
    sa_restorer: usize,
    sa_mask: u64,
}

type JmpBuf = [u64; 32];

unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: isize) -> *mut u8;
    fn munmap(addr: *mut u8, len: usize) -> i32;
    fn mprotect(addr: *mut u8, len: usize, prot: i32) -> i32;
    fn __sigsetjmp(env: *mut JmpBuf, savemask: i32) -> i32;
    fn siglongjmp(env: *mut JmpBuf, val: i32) -> !;
}

unsafe extern "C" fn segv_restorer() -> ! {
    asm!("mov eax, 15", "syscall", options(noreturn));
}

static mut JMP_ENV: JmpBuf = [0; 32];
static mut LAST_CODE: i32 = 0;
static mut LAST_ADDR: usize = 0;

unsafe extern "C" fn segv_handler(_sig: i32, info: *const SigInfoPrefix, _uctx: *mut u8) {
    LAST_CODE = (*info).si_code;
    LAST_ADDR = (*info).si_addr;
    siglongjmp(&raw mut JMP_ENV, 1);
}

unsafe fn catch_fault<F: FnOnce()>(f: F) -> Option<(i32, usize)> {
    let act = KernelSigAction {
        sa_sigaction: segv_handler as *const () as usize,
        sa_flags: (SA_SIGINFO | SA_NODEFER | 0x04000000) as usize,
        sa_restorer: segv_restorer as *const () as usize,
        sa_mask: 0,
    };
    let mut old = KernelSigAction {
        sa_sigaction: 0,
        sa_flags: 0,
        sa_restorer: 0,
        sa_mask: 0,
    };
    let rc: isize;
    asm!(
        "mov eax, 13",
        "syscall",
        in("edi") SIGSEGV,
        in("rsi") &act as *const KernelSigAction,
        in("rdx") &mut old as *mut KernelSigAction,
        in("r10") 8usize,
        lateout("rax") rc,
        out("rcx") _,
        out("r11") _,
    );
    assert_eq!(rc, 0);
    LAST_CODE = 0;
    LAST_ADDR = 0;
    let res = if __sigsetjmp(&raw mut JMP_ENV, 1) == 0 {
        f();
        None
    } else {
        Some((LAST_CODE, LAST_ADDR))
    };
    let _: isize;
    asm!(
        "mov eax, 13",
        "syscall",
        in("edi") SIGSEGV,
        in("rsi") &old as *const KernelSigAction,
        in("rdx") core::ptr::null_mut::<KernelSigAction>(),
        in("r10") 8usize,
        lateout("rax") _,
        out("rcx") _,
        out("r11") _,
    );
    res
}

#[target_feature(enable = "avx2")]
unsafe fn buggy_inplace_xor_overlap(buf: &mut [u8], key: u8) {
    let len = buf.len();
    assert!(len >= 32);
    let ptr = buf.as_mut_ptr();
    let vkey = _mm256_set1_epi8(key as i8);
    let mut cur = 0usize;
    while cur + 32 < len {
        let v = _mm256_loadu_si256(ptr.add(cur) as *const __m256i);
        _mm256_storeu_si256(ptr.add(cur) as *mut __m256i, _mm256_xor_si256(v, vkey));
        cur += 32;
    }
    let tail = len - 32;
    let vt = _mm256_loadu_si256(ptr.add(tail) as *const __m256i);
    _mm256_storeu_si256(ptr.add(tail) as *mut __m256i, _mm256_xor_si256(vt, vkey));
}

#[test]
fn test_bug01_inplace_xor_overlap_len33() {
    // Aligned len = 32 masks the bug completely:
    let mut aligned = [0u8; 32];
    unsafe { buggy_inplace_xor_overlap(&mut aligned, 1); }
    assert_eq!(aligned, [1u8; 32]);

    // Synthesized minimal counterexample: len = 33, key = 1, q = 1!
    let mut buf = [0u8; 33];
    unsafe { buggy_inplace_xor_overlap(&mut buf, 1); }
    assert_ne!(buf[1], (0u8 ^ 1u8), "Overlap lane q=1 double-XORed back to 0!");
    assert_eq!(buf[1], 0);
}

#[test]
fn test_bug02_unguarded_len_lt_32_pre_guard_fault() {
    let _g = SIG_TEST_LOCK.lock().unwrap();
    unsafe {
        let base = mmap(core::ptr::null_mut(), 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        assert_eq!(mprotect(base, 4096, PROT_NONE), 0);
        let rw = base.add(4096);
        let len: usize = 1;
        let fault = catch_fault(|| {
            let v = _mm256_set1_epi8(0x11);
            let tail_ptr = rw.wrapping_add(len.wrapping_sub(32));
            _mm256_storeu_si256(tail_ptr as *mut __m256i, v);
        });
        assert_eq!(munmap(base, 8192), 0);
        let (code, addr) = fault.expect("Expected SIGSEGV on pre-guard page wraparound");
        assert_eq!(code, 2);
        assert_eq!(addr, (rw as usize) - 31);
    }
}

#[test]
fn test_bug03_maskmovdqu_all_zero_mask_fault() {
    let _g = SIG_TEST_LOCK.lock().unwrap();
    unsafe {
        let base = mmap(core::ptr::null_mut(), 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        assert_eq!(mprotect(base.add(4096), 4096, PROT_READ), 0);
        let ro_page = base.add(4096);
        // 1. Compile-time constant zero mask: LLVM InstCombine elides `llvm.x86.sse2.maskmov.dqu`!
        let elided = catch_fault(|| {
            let src = _mm_set1_epi8(0x42);
            let const_zero = _mm_setzero_si128();
            _mm_maskmoveu_si128(src, const_zero, ro_page as *mut i8);
        });
        assert!(elided.is_none(), "Constant zero mask is elided by LLVM InstCombine");

        // 2. Opaque runtime all-zero mask (`black_box`): emits hardware `vmaskmovdqu` and faults!
        let fault = catch_fault(|| {
            let src = core::hint::black_box(_mm_set1_epi8(0x42));
            let zero_mask = core::hint::black_box(_mm_setzero_si128());
            _mm_maskmoveu_si128(src, zero_mask, ro_page as *mut i8);
        });
        assert_eq!(munmap(base, 8192), 0);
        let (code, addr) = fault.expect("Expected MASKMOVDQU SIGSEGV despite runtime mask == 0");
        assert_eq!(code, 2);
        assert_eq!(addr, (ro_page as usize) + 8);
    }
}

#[test]
fn test_bug04_vpshufb_bit7_zeroing_trap() {
    unsafe {
        let mut lut_bytes = [0u8; 32];
        lut_bytes[0] = 1;
        lut_bytes[16] = 1;
        let lut = _mm256_loadu_si256(lut_bytes.as_ptr() as *const __m256i);
        let inp = _mm256_set1_epi8(128u8 as i8);
        let buggy_out = _mm256_shuffle_epi8(lut, inp);
        let mut res = [0u8; 32];
        _mm256_storeu_si256(res.as_mut_ptr() as *mut __m256i, buggy_out);
        assert_eq!(res[0], 0, "Bit 7 (0x80) forced vpshufb lane to 0 instead of lut[0]=1");
        assert_ne!(res[0], 1);
    }
}

#[repr(C, align(32))]
struct Aligned32Arena {
    buf: [u8; 32],
}

#[test]
fn test_bug05_aligned_rmw_slack_writeback_clobber() {
    let mut arena = Aligned32Arena { buf: [0u8; 32] };
    unsafe {
        let base = arena.buf.as_mut_ptr();
        let old = _mm256_load_si256(base as *const __m256i);
        // Interleaved sibling/atomic write at offset 1 (outside slice_len = 1):
        core::ptr::write_volatile(base.add(1), 1);
        // Blend only lane 0 (`0xFF` at byte 0, `0x00` on slack lanes `1..32`):
        let mut mask_arr = [0u8; 32];
        mask_arr[0] = 0xFF;
        let mask = _mm256_loadu_si256(mask_arr.as_ptr() as *const __m256i);
        let new_val = _mm256_xor_si256(old, _mm256_set1_epi8(0x42));
        let blended = _mm256_blendv_epi8(old, new_val, mask);
        _mm256_store_si256(base as *mut __m256i, blended);
        let observed_sibling = core::ptr::read_volatile(base.add(1));
        assert_eq!(observed_sibling, 0, "Aligned 32B RMW slack-writeback wiped out sibling update!");
        assert_ne!(observed_sibling, 1);
    }
}

#[test]
fn test_bug06_rep_movsb_df1_backward_corruption() {
    let mut buf: [u8; 8] = [0u8, 0u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8];
    let expected = {
        let mut ref_b = buf;
        for i in 0..2usize {
            ref_b[2 + i] = buf[5 + i];
        }
        ref_b
    };
    unsafe {
        let mut rdi = buf.as_mut_ptr().add(2);
        let mut rsi = buf.as_ptr().add(5);
        let mut rcx: usize = 2;
        asm!(
            "std",
            "rep movsb",
            "cld",
            inout("rdi") rdi,
            inout("rsi") rsi,
            inout("rcx") rcx,
            options(nostack),
        );
    }
    assert_ne!(buf[1], expected[1]);
}
