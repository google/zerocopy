#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""
Ahead-of-time ELF `.o` verification discriminator for SFI + DWARF `.eh_frame`
unwinding and reentrant callbacks on x86-64 Linux and AArch64 (`qemu-aarch64
11.1.2 -cpu max`):

  1. `guest_fde_frame_mismatch`: Stack-switching SFI transition whose `.eh_frame`
     recovers frame state (`rbp` / `r12`) from the writable SFI guest stack;
     normal returns restore the host stack directly (`unsound_normal`), whereas
     unwinding from a reentrant `extern "C-unwind"` callback reads the modified
     guest stack state (`rc = 42` sentinel exit or silent `r12` corruption).
  2. `missing_fde_sfi_obj_abort`: Sandboxed `.o` compiled with `-fno-unwind-tables
     -fno-asynchronous-unwind-tables` invoking a panicking `extern "C-unwind"`
     callback without a host-anchored trampoline aborts in Phase 1 (`error 5`,
     `rc = -6`) and skips outer Rust `Drop` destructors (`outer_drops = 0`).
  3. `stateless_reentrant_clobber`: Reentrant `Host_0 -> SFI_1 -> Host_cb_2 ->
     SFI_3` with a stateless entry stub resetting `guest_sp` overwrites `SFI_1`'s
     suspended guest stack slots.
  4. `fixed_jump_over_fde_suite`: Host-anchored Jump-Over FDE trampoline pair +
     `WatermarkGuard` tested on both `rustc 1.99.1` and `rustc 1.102.0-nightly`
     linked against a 32-byte-bundled `gcc -c` SFI `.o` object: preserves
     reentrant guest frames, unwinds across nested SFI activations in 1 FDE hop
     per activation with zero guest-stack reads, runs all `Drop` destructors,
     preserves `r12`, and restores `guest_sp` watermarks.
  5. `aarch64_lfi_qemu_max`: Ahead-of-time compiled AArch64 LFI (`[x27, wIdx,
     uxtw]`, `w26` watermark, `bti c` under ELF BTI property, `paciasp`/`autiasp`)
     tested under `/usr/bin/qemu-aarch64 11.1.2 -cpu max`.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


SFI_GUEST_BUNDLED_S = r"""
    .section .text.sfi_sandbox, "ax", @progbits
    .bundle_align_mode 5
    .p2align 5
    .globl sfi_sandbox_code_start
sfi_sandbox_code_start:
    # Bundle 0 (0x00): Portal exit to host `sfi_enter_trampoline`
    ret

    .p2align 5
    # Bundle 1 (0x20): Portal hostcall jump to host `sfi_hostcall_trampoline`
    jmp sfi_hostcall_trampoline

    .p2align 5
    .globl sfi_guest_outer
    # Bundle 2 (0x40): sfi_guest_outer(rdi = val, rsi = mode)
sfi_guest_outer:
    subl $16, %r13d
    movq %rdi, (%r14,%r13,1)
    movq %rsi, 8(%r14,%r13,1)
    movq %rsi, %rdi
    movq (%r14,%r13,1), %rsi
    .bundle_lock
    subl $8, %r13d
    movl $(.Louter_ret - sfi_sandbox_code_start), %r11d
    movq %r11, (%r14,%r13,1)
    jmp sfi_sandbox_code_start + 0x20
    .bundle_unlock

    .p2align 5
.Louter_ret:
    movq (%r14,%r13,1), %rcx
    addq %rcx, %rax
    addl $16, %r13d
    .bundle_lock
    movl (%r14,%r13,1), %r11d
    addl $8, %r13d
    andl $0x1e0, %r11d
    leaq (%r15,%r11,1), %r11
    jmp *%r11
    .bundle_unlock

    .p2align 5
    .globl sfi_guest_inner
    # sfi_guest_inner(rdi = val, rsi = inner_mode)
sfi_guest_inner:
    subl $16, %r13d
    movabsq $0x7777888811112222, %rcx
    movq %rcx, (%r14,%r13,1)
    movq %rcx, 8(%r14,%r13,1)
    cmpq $2, %rsi
    je .Linner_panic_branch
    leaq 100(%rdi), %rax
    addl $16, %r13d
    .bundle_lock
    movl (%r14,%r13,1), %r11d
    addl $8, %r13d
    andl $0x1e0, %r11d
    leaq (%r15,%r11,1), %r11
    jmp *%r11
    .bundle_unlock

    .p2align 5
.Linner_panic_branch:
    # Overwrite guest stack return slot before invoking panicking Rust callback
    movq %rcx, 16(%r14,%r13,1)
    movl $99, %edi
    jmp sfi_sandbox_code_start + 0x20
    .p2align 5

    # Separate non-FDE object helper to verify Phase-1 abort when `.eh_frame` is absent
    .section .text.no_fde, "ax", @progbits
    .globl no_fde_direct_callback_caller
no_fde_direct_callback_caller:
    pushq %rbx
    movl $1, %edi
    call rust_panicking_callback
    popq %rbx
    ret
"""


RUST_HOST_HARNESS_RS = r"""
#![allow(function_casts_as_integer)]
use std::arch::global_asm;
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};

static DROP_OUTER: AtomicUsize = AtomicUsize::new(0);
static DROP_INNER: AtomicUsize = AtomicUsize::new(0);

struct CountDrop(&'static AtomicUsize);
impl Drop for CountDrop {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

#[no_mangle]
pub extern "C" fn outside_sandbox_sentinel() -> ! {
    println!("OUTCOME=UNWIND_REDIRECTED_OUTSIDE_SANDBOX");
    std::process::exit(42);
}

#[no_mangle]
pub extern "C-unwind" fn rust_panicking_callback(mode: u64) -> u64 {
    if mode == 1 {
        panic!("reentrant_callback_panic");
    }
    mode + 100
}

global_asm!(
    r#"
    .text
    .globl unsound_guest_stack_sfi_stub
    .type unsound_guest_stack_sfi_stub, @function
unsound_guest_stack_sfi_stub:
    .cfi_startproc
    leaq 8(%rsp), %rcx
    movq %rdi, %rsp
    subq $32, %rsp
    .cfi_escape 0x0f, 0x03, 0x77, 0x00, 0x06
    .cfi_escape 0x10, 0x0c, 0x02, 0x77, 0x08
    movq %rcx, 0(%rsp)
    movq %r12, 8(%rsp)

    cmpq $1, %rsi
    jne 1f
    .cfi_escape 0x10, 0x06, 0x02, 0x77, 0x10
    movq %rdx, 16(%rsp)
    movl $1, %edi
    call rust_panicking_callback
    jmp 3f
1:
    movq %rbp, 16(%rsp)
    cmpq $2, %rsi
    jne 2f
    movabsq $0x5555666677778888, %rax
    movq %rax, 8(%rsp)
    movl $1, %edi
    call rust_panicking_callback
    jmp 3f
2:
    movq %rdx, 16(%rsp)
    movl $0, %edi
    call rust_panicking_callback
3:
    movq 8(%rsp), %r12
    movq 0(%rsp), %rcx
    leaq -8(%rcx), %rsp
    ret
    .cfi_endproc

    .globl frame_pointer_catch_caller
    .type frame_pointer_catch_caller, @function
frame_pointer_catch_caller:
    .cfi_startproc
    pushq %rbp
    .cfi_def_cfa_offset 16
    .cfi_offset rbp, -16
    movq %rsp, %rbp
    .cfi_def_cfa_register rbp
    call do_catch_trampoline_c
    leave
    .cfi_def_cfa rsp, 8
    ret
    .cfi_endproc
"#,
    options(att_syntax)
);

#[repr(C)]
pub struct SfiContext {
    pub code_base: u64,
    pub arena_base: u64,
    pub code_mask: u32,
    pub guest_sp: u32,
    pub stateless_bug_mode: u32,
    pub initial_guest_sp: u32,
    pub cb_fn: extern "C-unwind" fn(*mut SfiContext, u64, u64) -> u64,
}

global_asm!(
    r#"
    .text
    .globl sfi_enter_trampoline
    .type sfi_enter_trampoline, @function
sfi_enter_trampoline:
    .cfi_startproc
    pushq %rbp
    .cfi_adjust_cfa_offset 8
    .cfi_offset rbp, -16
    pushq %rbx
    .cfi_adjust_cfa_offset 8
    .cfi_offset rbx, -24
    pushq %r12
    .cfi_adjust_cfa_offset 8
    .cfi_offset r12, -32
    pushq %r13
    .cfi_adjust_cfa_offset 8
    .cfi_offset r13, -40
    pushq %r14
    .cfi_adjust_cfa_offset 8
    .cfi_offset r14, -48
    pushq %r15
    .cfi_adjust_cfa_offset 8
    .cfi_offset r15, -56
    subq $8, %rsp
    .cfi_adjust_cfa_offset 8

    movq %rdi, %r12
    movl %esi, %r11d
    movq 0(%r12), %r15
    movq 8(%r12), %r14
    movl 24(%r12), %eax
    testl %eax, %eax
    jz 1f
    movl 28(%r12), %r13d
    jmp 2f
1:
    movl 20(%r12), %r13d
2:
    subl $8, %r13d
    movq $0, (%r14,%r13,1)
    andl 16(%r12), %r11d
    leaq (%r15,%r11,1), %rax
    movq %rdx, %rdi
    movq %rcx, %rsi

    call *%rax
    addq $8, %rsp
    .cfi_adjust_cfa_offset -8
    popq %r15
    .cfi_adjust_cfa_offset -8
    popq %r14
    .cfi_adjust_cfa_offset -8
    popq %r13
    .cfi_adjust_cfa_offset -8
    popq %r12
    .cfi_adjust_cfa_offset -8
    popq %rbx
    .cfi_adjust_cfa_offset -8
    popq %rbp
    .cfi_adjust_cfa_offset -8
    ret
    .cfi_endproc

    .globl sfi_hostcall_trampoline
    .type sfi_hostcall_trampoline, @function
sfi_hostcall_trampoline:
    .cfi_startproc
    pushq %r13
    .cfi_adjust_cfa_offset 8

    leal -64(%r13), %eax
    movl %eax, 20(%r12)

    movq %rsi, %rdx
    movq %rdi, %rsi
    movq %r12, %rdi
    movq 32(%r12), %rax
    call *%rax

    popq %r13
    .cfi_adjust_cfa_offset -8

    movq 0(%r12), %r15
    movq 8(%r12), %r14
    movl (%r14,%r13,1), %r11d
    addl $8, %r13d
    andl 16(%r12), %r11d
    leaq (%r15,%r11,1), %r11
    jmp *%r11
    .cfi_endproc
"#,
    options(att_syntax)
);

extern "C-unwind" {
    fn unsound_guest_stack_sfi_stub(guest_top: *mut u8, mode: u64, alt_rbp: u64) -> u64;
    fn no_fde_direct_callback_caller() -> u64;
    fn sfi_enter_trampoline(ctx: *mut SfiContext, entry_off: u64, arg0: u64, arg1: u64) -> u64;
}
extern "C" {
    fn frame_pointer_catch_caller(data: *mut u8) -> u64;
    fn sfi_sandbox_code_start();
    fn sfi_guest_outer();
    fn sfi_guest_inner();
}

#[no_mangle]
pub extern "C" fn do_catch_trampoline_c(data: *mut u8) -> u64 {
    let closure_opt = unsafe { &mut *(data as *mut Option<Box<dyn FnOnce() -> u64>>) };
    let closure = closure_opt.take().unwrap();
    let _outer_guard = CountDrop(&DROP_OUTER);
    match panic::catch_unwind(AssertUnwindSafe(closure)) {
        Ok(v) => v,
        Err(_) => 0xCA06_4700,
    }
}

struct WatermarkGuard {
    ctx: *mut SfiContext,
    saved_guest_sp: u32,
}
impl Drop for WatermarkGuard {
    fn drop(&mut self) {
        unsafe {
            (*self.ctx).guest_sp = self.saved_guest_sp;
        }
    }
}

pub unsafe fn sfi_invoke_guarded(
    ctx: *mut SfiContext,
    entry_off: u64,
    arg0: u64,
    arg1: u64,
) -> u64 {
    let saved = (*ctx).guest_sp;
    let _wm = WatermarkGuard {
        ctx,
        saved_guest_sp: saved,
    };
    sfi_enter_trampoline(ctx, entry_off, arg0, arg1)
}

#[inline(never)]
fn run_catch_inside_r12_holder<F: FnOnce() -> u64>(f: F) -> (bool, u64, u64) {
    let mut r12_val: u64 = 0x1122_3344_5566_7788;
    let mut boxed: Option<Box<dyn FnOnce() -> u64>> = Some(Box::new(f));
    let ptr = (&mut boxed as *mut Option<Box<dyn FnOnce() -> u64>>) as *mut u8;
    let ret_val: u64;
    unsafe {
        core::arch::asm!(
            "call {tramp}",
            tramp = sym frame_pointer_catch_caller,
            in("rdi") ptr,
            inout("r12") r12_val,
            lateout("rax") ret_val,
            clobber_abi("C"),
        );
    }
    (ret_val == 0xCA06_4700, ret_val, r12_val)
}

fn alloc_aligned_zeroed(size: usize, align: usize) -> *mut u8 {
    let layout = std::alloc::Layout::from_size_align(size, align).unwrap();
    let p = unsafe { std::alloc::alloc_zeroed(layout) };
    assert!(!p.is_null());
    p
}

extern "C-unwind" fn reentrant_host_cb(ctx: *mut SfiContext, mode: u64, val: u64) -> u64 {
    let _inner_guard = CountDrop(&DROP_INNER);
    let base = sfi_sandbox_code_start as *const () as usize as u64;
    let inner_off = (sfi_guest_inner as *const () as usize as u64) - base;
    unsafe {
        match mode {
            10 => sfi_invoke_guarded(ctx, inner_off, val * 2, 0),
            20 => sfi_invoke_guarded(ctx, inner_off, val * 2, 2),
            99 => panic!("reentrant_host_cb_explicit_panic"),
            _ => val + 1,
        }
    }
}

fn main() {
    let arg = std::env::args().nth(1).unwrap_or_default();
    let base = sfi_sandbox_code_start as *const () as usize as u64;
    let outer_off = (sfi_guest_outer as *const () as usize as u64) - base;

    match arg.as_str() {
        "unsound_normal" => unsafe {
            let gstack = alloc_aligned_zeroed(65536, 4096);
            let top = gstack.add(65536);
            let alt_frame: [u64; 2] = [0, outside_sandbox_sentinel as *const () as usize as u64];
            let (_, ret, r12) = run_catch_inside_r12_holder(|| {
                unsound_guest_stack_sfi_stub(top, 0, alt_frame.as_ptr() as u64)
            });
            println!("OUTCOME=NORMAL_OK ret=0x{:x} r12=0x{:x}", ret, r12);
        },
        "guest_fde_cfa_redirect" => unsafe {
            let gstack = alloc_aligned_zeroed(65536, 4096);
            let top = gstack.add(65536);
            let alt_stack = alloc_aligned_zeroed(16384, 4096);
            let alt_rbp = alt_stack.add(8192) as *mut u64;
            *alt_rbp = 0;
            *alt_rbp.add(1) = outside_sandbox_sentinel as *const () as usize as u64;
            let _ = run_catch_inside_r12_holder(|| {
                unsound_guest_stack_sfi_stub(top, 1, alt_rbp as u64)
            });
            println!("OUTCOME=UNEXPECTED_SURVIVAL");
        },
        "guest_fde_csr_corrupt" => unsafe {
            let gstack = alloc_aligned_zeroed(65536, 4096);
            let top = gstack.add(65536);
            let (caught, _, r12) = run_catch_inside_r12_holder(|| {
                unsound_guest_stack_sfi_stub(top, 2, 0)
            });
            println!(
                "OUTCOME=CAUGHT caught={} r12=0x{:016x} corrupted={}",
                caught,
                r12,
                r12 != 0x1122_3344_5566_7788
            );
        },
        "missing_fde_sfi_obj_abort" => unsafe {
            DROP_OUTER.store(0, Ordering::SeqCst);
            let (caught, _, _) = run_catch_inside_r12_holder(|| no_fde_direct_callback_caller());
            println!(
                "OUTCOME=DONE caught={} outer_drops={}",
                caught,
                DROP_OUTER.load(Ordering::SeqCst)
            );
        },
        "stateless_reentrant_clobber" => unsafe {
            let arena = alloc_aligned_zeroed(1 << 20, 4096);
            let mut ctx = SfiContext {
                code_base: base,
                arena_base: arena as u64,
                code_mask: 0x1E0,
                guest_sp: 0x80000,
                stateless_bug_mode: 1,
                initial_guest_sp: 0x80000,
                cb_fn: reentrant_host_cb,
            };
            let got = sfi_invoke_guarded(&mut ctx, outer_off, 0x1000, 10);
            println!(
                "OUTCOME=STATELESS_DONE got=0x{:016x} expected=0x3064 clobbered={}",
                got,
                got != 0x3064
            );
        },
        "fixed_jump_over_fde_suite" => unsafe {
            let arena = alloc_aligned_zeroed(1 << 20, 4096);
            let mut ctx = SfiContext {
                code_base: base,
                arena_base: arena as u64,
                code_mask: 0x1E0,
                guest_sp: 0x80000,
                stateless_bug_mode: 0,
                initial_guest_sp: 0x80000,
                cb_fn: reentrant_host_cb,
            };
            let got_reentrant = sfi_invoke_guarded(&mut ctx, outer_off, 0x1000, 10);
            let wm_after_normal = ctx.guest_sp;

            DROP_OUTER.store(0, Ordering::SeqCst);
            DROP_INNER.store(0, Ordering::SeqCst);
            let ctx_ptr = &mut ctx as *mut SfiContext;
            let (caught, _, r12_after) = run_catch_inside_r12_holder(|| {
                sfi_invoke_guarded(ctx_ptr, outer_off, 0x1000, 20)
            });
            let wm_after_panic = ctx.guest_sp;
            let outer_drops = DROP_OUTER.load(Ordering::SeqCst);
            let inner_drops = DROP_INNER.load(Ordering::SeqCst);

            let got_post_panic = sfi_invoke_guarded(&mut ctx, outer_off, 0x2000, 10);
            println!(
                "OUTCOME=FIXED_OK reentrant=0x{:x} wm_norm=0x{:x} caught={} r12=0x{:016x} outer_drops={} inner_drops={} wm_panic=0x{:x} post_panic=0x{:x}",
                got_reentrant,
                wm_after_normal,
                caught,
                r12_after,
                outer_drops,
                inner_drops,
                wm_after_panic,
                got_post_panic
            );
        },
        _ => panic!("unknown mode"),
    }
}
"""


AARCH64_LFI_STATIC_C = r"""
typedef unsigned char uint8_t;
typedef unsigned int uint32_t;
typedef unsigned long uint64_t;

static void sys_write(const char *s) {
    uint64_t len = 0;
    while (s[len]) len++;
    register uint64_t x0 __asm__("x0") = 1;
    register const char *x1 __asm__("x1") = s;
    register uint64_t x2 __asm__("x2") = len;
    register uint64_t x8 __asm__("x8") = 64;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x8) : "memory");
}

__attribute__((noreturn))
static void sys_exit(int code) {
    register uint64_t x0 __asm__("x0") = (uint64_t)code;
    register uint64_t x8 __asm__("x8") = 94;
    __asm__ volatile("svc #0" : : "r"(x0), "r"(x8));
    __builtin_unreachable();
}

static int sys_mprotect(void *addr, uint64_t len, uint64_t prot) {
    register uint64_t x0 __asm__("x0") = (uint64_t)addr;
    register uint64_t x1 __asm__("x1") = len;
    register uint64_t x2 __asm__("x2") = prot;
    register uint64_t x8 __asm__("x8") = 226;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x8) : "memory");
    return (int)x0;
}

static void write_hex64(const char *prefix, uint64_t v, const char *suffix) {
    char buf[32];
    const char *hex = "0123456789abcdef";
    buf[0] = '0';
    buf[1] = 'x';
    for (int i = 0; i < 16; i++) {
        buf[2 + i] = hex[(v >> ((15 - i) * 4)) & 0xf];
    }
    buf[18] = '\0';
    sys_write(prefix);
    sys_write(buf);
    sys_write(suffix);
}

typedef struct A64LfiCtx {
    uint64_t code_base;
    uint64_t arena_base;
    uint32_t code_mask;
    uint32_t guest_sp;
    uint64_t cb_fn;
    uint64_t host_drops;
} A64LfiCtx;

static uint8_t g_lfi_arena[1048576] __attribute__((aligned(4096)));

extern uint64_t a64_lfi_enter(A64LfiCtx *ctx, uint64_t entry_off, uint64_t a0, uint64_t a1);
extern void a64_lfi_hostcall_trampoline(void);
extern void lfi_static_code_base(void);
extern void lfi_non_bti_target(void);

__asm__(
    ".text\n"
    ".p2align 2\n"
    ".globl a64_lfi_enter\n"
    "a64_lfi_enter:\n"
    "    paciasp\n"
    "    stp x29, x30, [sp, #-96]!\n"
    "    mov x29, sp\n"
    "    stp x19, x20, [sp, #16]\n"
    "    stp x21, x22, [sp, #32]\n"
    "    stp x23, x24, [sp, #48]\n"
    "    stp x25, x26, [sp, #64]\n"
    "    stp x27, x28, [sp, #80]\n"
    "    mov x25, x0\n"
    "    ldr x28, [x25, #0]\n"
    "    ldr x27, [x25, #8]\n"
    "    ldr w26, [x25, #20]\n"
    "    sub w26, w26, #8\n"
    "    str xzr, [x27, w26, uxtw]\n"
    "    ldr w16, [x25, #16]\n"
    "    bic w1, w1, #3\n"
    "    and w16, w1, w16\n"
    "    add x16, x28, w16, uxtw\n"
    "    mov x0, x2\n"
    "    mov x1, x3\n"
    "    blr x16\n"
    "    ldp x27, x28, [sp, #80]\n"
    "    ldp x25, x26, [sp, #64]\n"
    "    ldp x23, x24, [sp, #48]\n"
    "    ldp x21, x22, [sp, #32]\n"
    "    ldp x19, x20, [sp, #16]\n"
    "    ldp x29, x30, [sp], #96\n"
    "    autiasp\n"
    "    ret\n"

    ".globl a64_lfi_hostcall_trampoline\n"
    "a64_lfi_hostcall_trampoline:\n"
    "    bti c\n"
    "    paciasp\n"
    "    stp x29, x30, [sp, #-32]!\n"
    "    mov x29, sp\n"
    "    str x26, [sp, #16]\n"
    "    sub w9, w26, #64\n"
    "    str w9, [x25, #20]\n"
    "    mov x2, x1\n"
    "    mov x1, x0\n"
    "    mov x0, x25\n"
    "    ldr x16, [x25, #24]\n"
    "    blr x16\n"
    "    ldr x26, [sp, #16]\n"
    "    ldp x29, x30, [sp], #32\n"
    "    autiasp\n"
    "    ldr x28, [x25, #0]\n"
    "    ldr x27, [x25, #8]\n"
    "    ldr w16, [x27, w26, uxtw]\n"
    "    add w26, w26, #8\n"
    "    ldr w17, [x25, #16]\n"
    "    bic w16, w16, #3\n"
    "    and w16, w16, w17\n"
    "    add x16, x28, w16, uxtw\n"
    "    br x16\n"

    /* Page-aligned ahead-of-time compiled AArch64 LFI code section */
    ".p2align 12\n"
    ".globl lfi_static_code_base\n"
    "lfi_static_code_base:\n"
    /* 0x00: Portal 0 */
    "    bti c\n"
    "    ret\n"
    /* 0x08: Portal 1 */
    "    bti c\n"
    "    b a64_lfi_hostcall_trampoline\n"
    "    nop\n"
    "    nop\n"
    /* 0x18: LFI_outer */
    "    bti c\n"
    "    sub w26, w26, #16\n"
    "    str x0, [x27, w26, uxtw]\n"
    "    add w9, w26, #8\n"
    "    str x1, [x27, w9, uxtw]\n"
    "    mov x9, x0\n"
    "    mov x0, x1\n"
    "    mov x1, x9\n"
    "    sub w26, w26, #8\n"
    "    mov w16, #0x48\n"
    "    str x16, [x27, w26, uxtw]\n"
    "    b lfi_static_code_base + 0x08\n"
    /* 0x48: LFI_outer_cont */
    "    bti c\n"
    "    ldr x9, [x27, w26, uxtw]\n"
    "    add x0, x0, x9\n"
    "    add w26, w26, #16\n"
    "    ldr w16, [x27, w26, uxtw]\n"
    "    add w26, w26, #8\n"
    "    bic w16, w16, #3\n"
    "    and w16, w16, #0xff\n"
    "    add x16, x28, w16, uxtw\n"
    "    br x16\n"
    /* 0x70: LFI_inner */
    "    bti c\n"
    "    sub w26, w26, #16\n"
    "    movz x9, #0x5555, lsl #16\n"
    "    movk x9, #0x6666\n"
    "    str x9, [x27, w26, uxtw]\n"
    "    cmp x1, #2\n"
    "    b.eq 1f\n"
    "    add x0, x0, #100\n"
    "    add w26, w26, #16\n"
    "    ldr w16, [x27, w26, uxtw]\n"
    "    add w26, w26, #8\n"
    "    bic w16, w16, #3\n"
    "    and w16, w16, #0xff\n"
    "    add x16, x28, w16, uxtw\n"
    "    br x16\n"
    "1:\n"
    "    add w10, w26, #16\n"
    "    str x9, [x27, w10, uxtw]\n"
    "    mov x0, #99\n"
    "    b lfi_static_code_base + 0x08\n"
    ".globl lfi_non_bti_target\n"
    "lfi_non_bti_target:\n"
    "    add x0, x0, #77\n"
    "    ret\n"
    ".p2align 12\n"
);

typedef struct HostCatchEnv {
    uint64_t sp;
    uint64_t fp;
    uint64_t lr;
    uint64_t x19_28[10];
    uint32_t saved_guest_sp;
} HostCatchEnv;

static HostCatchEnv g_catch_env;

extern int host_set_catch(HostCatchEnv *env);
extern void host_throw_unwind(HostCatchEnv *env, int val) __attribute__((noreturn));

__asm__(
    ".p2align 2\n"
    ".globl host_set_catch\n"
    "host_set_catch:\n"
    "    mov x9, sp\n"
    "    str x9, [x0, #0]\n"
    "    str x29, [x0, #8]\n"
    "    pacia x30, x9\n"
    "    str x30, [x0, #16]\n"
    "    autia x30, x9\n"
    "    stp x19, x20, [x0, #24]\n"
    "    stp x21, x22, [x0, #40]\n"
    "    stp x23, x24, [x0, #56]\n"
    "    stp x25, x26, [x0, #72]\n"
    "    stp x27, x28, [x0, #88]\n"
    "    mov w0, #0\n"
    "    ret\n"

    ".globl host_throw_unwind\n"
    "host_throw_unwind:\n"
    "    ldr x9, [x0, #0]\n"
    "    ldr x29, [x0, #8]\n"
    "    ldr x30, [x0, #16]\n"
    "    ldp x19, x20, [x0, #24]\n"
    "    ldp x21, x22, [x0, #40]\n"
    "    ldp x23, x24, [x0, #56]\n"
    "    ldp x25, x26, [x0, #72]\n"
    "    ldp x27, x28, [x0, #88]\n"
    "    mov sp, x9\n"
    "    autia x30, x9\n"
    "    mov w0, w1\n"
    "    ret\n"
);

static uint64_t a64_lfi_invoke_guarded(A64LfiCtx *ctx, uint64_t off, uint64_t a0, uint64_t a1) {
    uint32_t saved_wm = ctx->guest_sp;
    uint64_t r = a64_lfi_enter(ctx, off, a0, a1);
    ctx->guest_sp = saved_wm;
    return r;
}

static uint64_t a64_host_callback(A64LfiCtx *ctx, uint64_t mode, uint64_t val) {
    ctx->host_drops += 1;
    if (mode == 10) {
        return a64_lfi_invoke_guarded(ctx, 0x70, val * 2, 0);
    }
    if (mode == 20) {
        return a64_lfi_invoke_guarded(ctx, 0x70, val * 2, 2);
    }
    if (mode == 99) {
        ctx->guest_sp = g_catch_env.saved_guest_sp;
        host_throw_unwind(&g_catch_env, 77);
    }
    return val + 1;
}

__asm__(
    ".text\n"
    ".p2align 2\n"
    ".globl _start\n"
    "_start:\n"
    "    ldr x0, [sp]\n"
    "    bl c_main\n"
);

void c_main(uint64_t argc) {

    /* Enforce PROT_READ | PROT_EXEC | PROT_BTI (0x15) on the static LFI code page */
    (void)sys_mprotect((void *)&lfi_static_code_base, 4096, 0x15);

    if (argc == 2) {
        uint64_t non_bti_addr = (uint64_t)&lfi_non_bti_target;
        __asm__ volatile("mov x16, %0\nbr x16\n" : : "r"(non_bti_addr) : "x16");
        sys_exit(1);
    }

    if (argc == 3) {
        if (host_set_catch(&g_catch_env) == 0) {
            g_catch_env.lr ^= (1ULL << 56);
            host_throw_unwind(&g_catch_env, 1);
        }
        sys_exit(1);
    }

    A64LfiCtx ctx;
    ctx.code_base = (uint64_t)&lfi_static_code_base;
    ctx.arena_base = (uint64_t)&g_lfi_arena[0];
    ctx.code_mask = 0xff;
    ctx.guest_sp = 0x80000;
    ctx.cb_fn = (uint64_t)&a64_host_callback;
    ctx.host_drops = 0;

    register uint64_t x19_canary __asm__("x19") = 0x1122334455667788ULL;
    __asm__ volatile("" : "+r"(x19_canary));
    uint64_t r1 = a64_lfi_invoke_guarded(&ctx, 0x18, 0x1000, 10);

    g_catch_env.saved_guest_sp = ctx.guest_sp;
    int caught = host_set_catch(&g_catch_env);
    if (caught == 0) {
        (void)a64_lfi_invoke_guarded(&ctx, 0x18, 0x1000, 20);
        sys_exit(3);
    }
    __asm__ volatile("" : "+r"(x19_canary));

    uint64_t r2 = a64_lfi_invoke_guarded(&ctx, 0x18, 0x2000, 10);

    write_hex64("A64_LFI_OK r1=", r1, " ");
    write_hex64("caught=", (uint64_t)caught, " ");
    write_hex64("x19=", x19_canary, " ");
    write_hex64("wm=", (uint64_t)ctx.guest_sp, " ");
    write_hex64("r2=", r2, "\n");
    sys_exit(0);
}
"""


def find_lld() -> str:
    for cand in [
        shutil.which("ld.lld"),
        shutil.which("lld-19"),
        str(
            Path.home()
            / ".rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld"
        ),
    ]:
        if cand and Path(cand).exists():
            return cand
    raise RuntimeError("ld.lld not found")


def run_x86_suite_for_rustc(td: Path, toolchain: str) -> dict[str, object]:
    slug = toolchain.lstrip("+").replace(".", "_").replace("-", "_")
    s_path = td / f"sfi_guest_{slug}.s"
    o_path = td / f"sfi_guest_{slug}.o"
    rs_path = td / f"unwind_sfi_{slug}.rs"
    bin_path = td / f"unwind_sfi_{slug}"

    s_path.write_text(SFI_GUEST_BUNDLED_S)
    subprocess.run(["gcc", "-c", str(s_path), "-o", str(o_path)], check=True)
    rs_path.write_text(RUST_HOST_HARNESS_RS)

    ver = subprocess.run(["rustc", toolchain, "-vV"], capture_output=True, text=True, check=True).stdout.strip()
    subprocess.run(
        [
            "rustc",
            toolchain,
            "-C",
            "opt-level=2",
            "-C",
            "panic=unwind",
            f"-Clink-arg={o_path}",
            str(rs_path),
            "-o",
            str(bin_path),
        ],
        check=True,
    )

    modes = [
        "unsound_normal",
        "guest_fde_cfa_redirect",
        "guest_fde_csr_corrupt",
        "missing_fde_sfi_obj_abort",
        "stateless_reentrant_clobber",
        "fixed_jump_over_fde_suite",
    ]
    out: dict[str, object] = {"rustc_vV": ver, "cases": {}}
    for m in modes:
        r = subprocess.run([str(bin_path), m], capture_output=True, text=True)
        clean_err = r.stderr.replace(str(td), "<TMP>")
        out["cases"][m] = {
            "rc": r.returncode,
            "stdout": r.stdout.strip(),
            "stderr_tail": "\n".join(clean_err.strip().splitlines()[-4:]),
        }
    return out


def run_aarch64_lfi_suite(td: Path) -> dict[str, object]:
    c_path = td / "a64_lfi.c"
    bin_path = td / "a64_lfi"
    c_path.write_text(AARCH64_LFI_STATIC_C)
    clang = shutil.which("clang-19") or shutil.which("clang")
    assert clang is not None
    lld = find_lld()

    subprocess.run(
        [
            clang,
            "--target=aarch64-linux-gnu",
            "-march=armv8.5-a",
            "-mbranch-protection=standard",
            "-O2",
            "-static",
            "-nostdlib",
            f"--ld-path={lld}",
            "-Wl,-e,_start",
            str(c_path),
            "-o",
            str(bin_path),
        ],
        check=True,
    )

    qemu = "/usr/bin/qemu-aarch64"
    qemu_ver = subprocess.run([qemu, "--version"], capture_output=True, text=True, check=True).stdout.splitlines()[0]
    clang_ver = subprocess.run([clang, "--version"], capture_output=True, text=True, check=True).stdout.splitlines()[0]

    r_ok = subprocess.run([qemu, "-cpu", "max", str(bin_path)], capture_output=True, text=True)
    r_bti = subprocess.run([qemu, "-cpu", "max", str(bin_path), "bti"], capture_output=True, text=True)
    r_pac = subprocess.run([qemu, "-cpu", "max", str(bin_path), "pac", "mismatch"], capture_output=True, text=True)

    return {
        "qemu_version": qemu_ver,
        "clang_version": clang_ver,
        "reentrant_and_poisoned_unwind": {
            "rc": r_ok.returncode,
            "stdout": r_ok.stdout.strip(),
            "stderr": r_ok.stderr.strip(),
        },
        "prot_bti_missing_landing_pad_trap": {
            "rc": r_bti.returncode,
            "stdout": r_bti.stdout.strip(),
            "stderr": r_bti.stderr.strip(),
        },
        "feat_fpac_corrupted_lr_trap": {
            "rc": r_pac.returncode,
            "stdout": r_pac.stdout.strip(),
            "stderr": r_pac.stderr.strip(),
        },
    }


def main() -> int:
    with tempfile.TemporaryDirectory() as td_str:
        td = Path(td_str)
        res = {
            "kernel": subprocess.run(["uname", "-srm"], capture_output=True, text=True, check=True).stdout.strip(),
            "mmap_min_addr": int(Path("/proc/sys/vm/mmap_min_addr").read_text().strip()),
            "x86_64_rustc_1_99_1": run_x86_suite_for_rustc(td, "+1.99.1"),
            "x86_64_rustc_nightly": run_x86_suite_for_rustc(td, "+nightly"),
            "aarch64_lfi_qemu_max": run_aarch64_lfi_suite(td),
        }

    for key in ("x86_64_rustc_1_99_1", "x86_64_rustc_nightly"):
        cases = res[key]["cases"]
        assert cases["unsound_normal"]["rc"] == 0 and "NORMAL_OK" in cases["unsound_normal"]["stdout"], cases
        assert (
            cases["guest_fde_cfa_redirect"]["rc"] == 42
            and "UNWIND_REDIRECTED_OUTSIDE_SANDBOX" in cases["guest_fde_cfa_redirect"]["stdout"]
        ), cases
        assert cases["guest_fde_csr_corrupt"]["rc"] == 0 and "corrupted=true" in cases["guest_fde_csr_corrupt"]["stdout"], cases
        assert cases["missing_fde_sfi_obj_abort"]["rc"] == -6, cases
        assert cases["stateless_reentrant_clobber"]["rc"] == 0 and "clobbered=true" in cases["stateless_reentrant_clobber"]["stdout"], cases
        f_out = cases["fixed_jump_over_fde_suite"]["stdout"]
        assert (
            cases["fixed_jump_over_fde_suite"]["rc"] == 0
            and "reentrant=0x3064" in f_out
            and "caught=true" in f_out
            and "r12=0x1122334455667788" in f_out
            and "outer_drops=1" in f_out
            and "inner_drops=2" in f_out
            and "wm_panic=0x80000" in f_out
            and "post_panic=0x6064" in f_out
        ), cases["fixed_jump_over_fde_suite"]

    a64 = res["aarch64_lfi_qemu_max"]
    assert a64["reentrant_and_poisoned_unwind"]["rc"] == 0, a64
    assert "r1=0x0000000000003064" in a64["reentrant_and_poisoned_unwind"]["stdout"], a64
    assert "x19=0x1122334455667788" in a64["reentrant_and_poisoned_unwind"]["stdout"], a64
    assert "r2=0x0000000000006064" in a64["reentrant_and_poisoned_unwind"]["stdout"], a64
    assert a64["prot_bti_missing_landing_pad_trap"]["rc"] == -4, a64
    assert a64["feat_fpac_corrupted_lr_trap"]["rc"] == -4, a64

    (HERE / "unwind_rop_and_reentrant_results.json").write_text(json.dumps(res, indent=2) + "\n")
    print("ALL_UNWIND_SFI_AND_AARCH64_LFI_CHECKS_PASSED")
    print(json.dumps(res, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
