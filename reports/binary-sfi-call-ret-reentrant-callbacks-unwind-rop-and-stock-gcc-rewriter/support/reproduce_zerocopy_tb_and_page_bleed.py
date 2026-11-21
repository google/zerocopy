#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""
Live Linux `7.1.6` virtual-memory (`memfd_create` / `mmap` / `mprotect` /
`SA_SIGINFO`) and `cargo +nightly miri` (`-Zmiri-tree-borrows`) reproducer for
Zero-Copy Rust <-> SFI Arena Sharing:

  1. Hardware 4 KiB Page-Granularity Write Bleed (`subpage_write_bleed_poc`):
     co-locating a writable 64-byte slice `[0..64)` and an immutable Rust slice
     `[64..128)` on one `4,096`-byte `PROT_READ | PROT_WRITE` SFI page allows
     an SFI-legal `mov [r14 + 64], 0xBAD0C0DE` (`0 <= 64 < 2^32`) to silently
     corrupt the adjacent Rust `&[u8]` with zero hardware traps.
  2. Dual-Mapped `memfd_create` Read-Only Window (`memfd_dual_map_prot_read`):
     mapping a `memfd_create` file `PROT_READ | PROT_WRITE` on the host side
     (`host_ptr`) and `PROT_READ` inside `[r14 + 0x10000, r14 + 0x11000)`
     flanked by `PROT_NONE` pages delivers true zero-copy reads while trapping
     any rogue SFI store with `SIGSEGV` (`SEGV_ACCERR`, `si_code = 2`) and
     leaving `*host_ptr` `100%` unmutated.
  3. Page-Aligned `SfiBox<[u8]>` Guarded Allocation (`sfibox_page_aligned_guard`):
     whole-page (`4,096`-byte) `PROT_READ | PROT_WRITE` allocation with
     zero-initialized page tail `[len .. 4096)` flanked by `PROT_NONE` guard
     pages traps cross-page OOB writes (`SEGV_ACCERR`) while isolating sibling
     `SfiBox` allocations.
  4. `Tree Borrows` (`-Zmiri-tree-borrows`) Protector & Sibling-Slice UB Matrix:
     - `ub_frozen_ref_across_writable_sfi`: holding protected `&[u8]` (`Frozen`)
       across a writable SFI call triggers immediate `StrongProtector` UB;
     - `ub_sibling_mut_slice_across_sfi_oob_write`: holding protected sibling
       `b: &mut [u8]` inside the same writable SFI arena while passing `a` by
       offset triggers `StrongProtector` UB when C writes `b` via integer offset;
     - `ub_reentrant_cb_slice_across_nested_sfi`: reentrant Rust callback
       holding `chunk: &[u8]` into the writable arena across nested `SFI_3`
       triggers `Frozen` foreign-write UB;
     - `ok_sfi_arena_span_handles_and_scoped_loan`: `SfiArena` + provenance-free
       `SfiSpan` (`u32` offset/length) + scoped `with_slice` / `with_slice_mut`
       suspended across `sfi_enter(&mut arena)` (including reentrant callbacks)
       passes `-Zmiri-tree-borrows` with zero UB.
"""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


LINUX_VM_BLEED_C = r"""
#define _GNU_SOURCE
#include <errno.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

static sigjmp_buf g_jmp;
static volatile int g_sig = 0;
static volatile int g_si_code = 0;
static volatile uintptr_t g_fault_addr = 0;

static void segv_handler(int sig, siginfo_t *info, void *uctx) {
    (void)uctx;
    g_sig = sig;
    g_si_code = info ? info->si_code : 0;
    g_fault_addr = info ? (uintptr_t)info->si_addr : 0;
    siglongjmp(g_jmp, 1);
}

/* SFI-instrumented store: `movl %esi, %r11d; movq %rdx, (%r14,%r11,1)` */
__attribute__((noinline))
static void sfi_masked_store64(uint8_t *r14_base, uint32_t guest_off, uint64_t val) {
    __asm__ volatile(
        "movq %0, %%r14\n\t"
        "movl %1, %%r11d\n\t"
        "movq %2, (%%r14,%%r11,1)\n\t"
        :
        : "r"(r14_base), "r"(guest_off), "r"(val)
        : "r11", "r14", "memory"
    );
}

__attribute__((noinline))
static uint64_t sfi_masked_load64(uint8_t *r14_base, uint32_t guest_off) {
    uint64_t out;
    __asm__ volatile(
        "movq %1, %%r14\n\t"
        "movl %2, %%r11d\n\t"
        "movq (%%r14,%%r11,1), %0\n\t"
        : "=r"(out)
        : "r"(r14_base), "r"(guest_off)
        : "r11", "r14", "memory"
    );
    return out;
}

int main(void) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = segv_handler;
    sa.sa_flags = SA_SIGINFO;
    sigaction(SIGSEGV, &sa, NULL);

    /* Reserve a real `4 GiB + 2 * 64 KiB` PROT_NONE SFI envelope via MAP_NORESERVE! */
    const size_t GUARD = 65536;
    const size_t ARENA_4G = 4294967296ULL;
    const size_t TOTAL = GUARD + ARENA_4G + GUARD;
    uint8_t *env_base = mmap(NULL, TOTAL, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (env_base == MAP_FAILED) {
        perror("mmap 4GiB");
        return 2;
    }
    uint8_t *r14 = env_base + GUARD;

    /* 1. Sub-page 4 KiB write-bleed PoC:
     * Map page 0 `[r14 + 0 .. r14 + 4096)` as PROT_READ | PROT_WRITE.
     * Slice A `[0..64)` is passed to C; Slice B `[64..128)` holds Rust `Frozen` data `0x1111222233334444`. */
    mprotect(r14, 4096, PROT_READ | PROT_WRITE);
    volatile uint64_t *rust_frozen_neighbor = (volatile uint64_t *)(r14 + 64);
    *rust_frozen_neighbor = 0x1111222233334444ULL;
    sfi_masked_store64(r14, 64, 0xBAD0C0DECAFEBABEULL);
    uint64_t bleed_after = *rust_frozen_neighbor;

    /* 2. Dual-mapped `memfd_create` read-only zero-copy window at `[r14 + 0x10000 .. r14 + 0x11000)`:
     * Host writes via `host_rw` (`PROT_READ | PROT_WRITE`); SFI maps same fd `PROT_READ` (`MAP_FIXED`). */
    int mfd = memfd_create("sfi_zc_ro", MFD_CLOEXEC);
    ftruncate(mfd, 4096);
    uint64_t *host_rw = mmap(NULL, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, mfd, 0);
    uint8_t *sfi_ro = mmap(r14 + 0x10000, 4096, PROT_READ, MAP_SHARED | MAP_FIXED, mfd, 0);
    (void)sfi_ro;
    host_rw[0] = 0x9988776655443322ULL;
    uint64_t zc_read = sfi_masked_load64(r14, 0x10000);

    g_sig = 0;
    g_si_code = 0;
    int ro_trapped = 0;
    if (sigsetjmp(g_jmp, 1) == 0) {
        sfi_masked_store64(r14, 0x10000, 0xDEADBEEFULL);
    } else {
        ro_trapped = 1;
    }
    int ro_sig = g_sig;
    int ro_code = g_si_code; /* SEGV_ACCERR == 2 */
    uint64_t host_after_attack = host_rw[0];

    /* 3. Page-aligned `SfiBox<[u8]>` at `[r14 + 0x20000 .. r14 + 0x21000)` (`len = 100` bytes,
     * tail `[100..4096)` zero-filled, adjacent pages `0x1f000` and `0x21000` remain `PROT_NONE`!). */
    mprotect(r14 + 0x20000, 4096, PROT_READ | PROT_WRITE);
    /* Valid tail store inside same 4 KiB SfiBox page touches only SfiBox padding: */
    sfi_masked_store64(r14, 0x20000 + 128, 0xABCDULL);
    /* Cross-page OOB store at `+4096` hits `PROT_NONE` (`SEGV_ACCERR`) immediately: */
    g_sig = 0;
    g_si_code = 0;
    int guard_trapped = 0;
    if (sigsetjmp(g_jmp, 1) == 0) {
        sfi_masked_store64(r14, 0x21000, 0xDEADBEEFULL);
    } else {
        guard_trapped = 1;
    }
    int guard_sig = g_sig;
    int guard_code = g_si_code;

    printf(
        "{\"bleed_corrupted\": %s, \"bleed_val_hex\": \"0x%016llx\", "
        "\"zc_read_matches\": %s, \"ro_write_trapped\": %s, \"ro_sig\": %d, \"ro_si_code\": %d, "
        "\"host_unmutated\": %s, \"guard_trapped\": %s, \"guard_sig\": %d, \"guard_si_code\": %d, "
        "\"segv_accerr_const\": %d}\n",
        (bleed_after == 0xBAD0C0DECAFEBABEULL) ? "true" : "false",
        (unsigned long long)bleed_after,
        (zc_read == 0x9988776655443322ULL) ? "true" : "false",
        ro_trapped ? "true" : "false",
        ro_sig,
        ro_code,
        (host_after_attack == 0x9988776655443322ULL) ? "true" : "false",
        guard_trapped ? "true" : "false",
        guard_sig,
        guard_code,
        SEGV_ACCERR
    );

    munmap(host_rw, 4096);
    close(mfd);
    munmap(env_base, TOTAL);
    return 0;
}
"""


MIRI_TB_CARGO_TOML = """[package]
name = "sfi_tb_probe"
version = "0.1.0"
edition = "2021"
"""

MIRI_TB_MAIN_RS = r"""
//! Live `-Zmiri-tree-borrows` discriminator for zero-copy SFI arena sharing:
//! models an exposed SFI writable arena (`r14_addr = arena_ptr.expose_provenance()`)
//! where sandboxed C accesses arbitrary 32-bit offsets via `std::ptr::with_exposed_provenance_mut`.

#[derive(Copy, Clone)]
pub struct SfiSpan {
    pub offset: u32,
    pub len: u32,
}

/// Subtle Tree Borrows trap: storing `Box<[u8]>` inside `BadBoxSfiArena` causes
/// recursive `Box` retagging (`Unique` + `WeakProtector`) when `&mut BadBoxSfiArena`
/// is passed to `sfi_enter`, invalidating the exposed root tag on `with_slice_mut`!
pub struct BadBoxSfiArena {
    buf: Box<[u8]>,
    r14_addr: usize,
}

impl BadBoxSfiArena {
    pub fn new(size: usize) -> Self {
        let mut buf = vec![0u8; size].into_boxed_slice();
        let r14_addr = buf.as_mut_ptr().expose_provenance();
        Self { buf, r14_addr }
    }
    pub fn with_slice_mut<R>(&mut self, span: SfiSpan, f: impl FnOnce(&mut [u8]) -> R) -> R {
        f(&mut self.buf[span.offset as usize..(span.offset + span.len) as usize])
    }
    pub fn sfi_enter<R>(&mut self, guest_body: impl FnOnce(usize, &mut Self) -> R) -> R {
        let addr = self.r14_addr;
        guest_body(addr, self)
    }
}

/// Sound `SfiArena`: owns a raw `*mut u8` allocation (`alloc_zeroed` / `mmap`) with
/// NO `Box<T>` field, so passing `&mut SfiArena` never recursively retags the backing
/// buffer, while `sfi_enter(&mut self)` statically suspends all scoped `&[u8]` / `&mut [u8]`!
pub struct SfiArena {
    raw_ptr: *mut u8,
    size: usize,
    r14_addr: usize,
}

impl SfiArena {
    pub fn new(size: usize) -> Self {
        assert!(size > 0);
        let layout = std::alloc::Layout::from_size_align(size, 4096).unwrap();
        let raw_ptr = unsafe { std::alloc::alloc_zeroed(layout) };
        assert!(!raw_ptr.is_null());
        let r14_addr = raw_ptr.expose_provenance();
        Self { raw_ptr, size, r14_addr }
    }

    pub fn with_slice<R>(&self, span: SfiSpan, f: impl FnOnce(&[u8]) -> R) -> R {
        let start = span.offset as usize;
        let len = span.len as usize;
        assert!(start + len <= self.size);
        let slice = unsafe { core::slice::from_raw_parts(self.raw_ptr.add(start), len) };
        f(slice)
    }

    pub fn with_slice_mut<R>(&mut self, span: SfiSpan, f: impl FnOnce(&mut [u8]) -> R) -> R {
        let start = span.offset as usize;
        let len = span.len as usize;
        assert!(start + len <= self.size);
        let slice = unsafe { core::slice::from_raw_parts_mut(self.raw_ptr.add(start), len) };
        f(slice)
    }

    pub fn sfi_enter<R>(
        &mut self,
        guest_body: impl FnOnce(usize, &mut Self) -> R,
    ) -> R {
        let addr = self.r14_addr;
        guest_body(addr, self)
    }
}

impl Drop for SfiArena {
    fn drop(&mut self) {
        let layout = std::alloc::Layout::from_size_align(self.size, 4096).unwrap();
        unsafe { std::alloc::dealloc(self.raw_ptr, layout) };
    }
}

/// Simulated sandboxed C store `mov [r14 + idx32], val` via exposed integer provenance.
unsafe fn simulated_c_sfi_write(r14_addr: usize, idx32: u32, val: u8) {
    let p: *mut u8 = core::ptr::with_exposed_provenance_mut(r14_addr.wrapping_add(idx32 as usize));
    p.write(val);
}

// Case 1 (UB): Holding a protected `&[u8]` (`Frozen` + `StrongProtector`) into a writable
// SFI arena while sandboxed C writes to that offset.
fn helper_holding_frozen_protector(r14_addr: usize, view: &[u8]) -> u8 {
    unsafe { simulated_c_sfi_write(r14_addr, 0, 0xAA) };
    view[0]
}

fn ub_frozen_ref_across_writable_sfi() {
    let mut raw = vec![1u8; 8192];
    let r14_addr = raw.as_mut_ptr().expose_provenance();
    let view: &[u8] = &raw[0..64];
    let _ = helper_holding_frozen_protector(r14_addr, view);
}

// Case 2 (UB): Two disjoint slices `(a, b)` inside the SAME writable SFI arena (`4096` bytes
// apart!). Rust passes `a` by offset to C while holding `b: &mut [u8]` under `StrongProtector`;
// malicious C ignores `a`'s offset and writes `[r14 + 4096]` (`b`)!
fn helper_holding_sibling_mut_protector(r14_addr: usize, sibling_b: &mut [u8]) -> u8 {
    // Malicious C writes to offset 4096 (inside `sibling_b`)!
    unsafe { simulated_c_sfi_write(r14_addr, 4096, 0xBB) };
    sibling_b[0] = 0xCC;
    sibling_b[0]
}

fn ub_sibling_mut_slice_across_sfi_oob_write() {
    let mut raw = vec![0u8; 8192];
    let r14_addr = raw.as_mut_ptr().expose_provenance();
    let (_slice_a, slice_b) = raw.split_at_mut(4096);
    let _ = helper_holding_sibling_mut_protector(r14_addr, slice_b);
}

// Case 3 (UB): Reentrant callback `Host_cb_2` creates `chunk: &[u8]` into the writable
// SFI arena and keeps `chunk` live across a nested `SFI_3` invocation that writes that byte!
fn ub_reentrant_cb_slice_across_nested_sfi() {
    let mut raw = vec![7u8; 4096];
    let r14_addr = raw.as_mut_ptr().expose_provenance();
    // Inside `Host_cb_2`: unsafe code creates `&[u8]` from `r14_addr` and holds it across `SFI_3`!
    let chunk: &[u8] = unsafe {
        core::slice::from_raw_parts(core::ptr::with_exposed_provenance(r14_addr), 64)
    };
    let first = chunk[0];
    // Nested `SFI_3` writes `[r14 + 0]` while `chunk` (`Frozen`) is still used below!
    unsafe { simulated_c_sfi_write(r14_addr, 0, 0xDD) };
    let second = chunk[0];
    assert_ne!(first, second);
}

// Case 4 (UB): Storing `Box<[u8]>` instead of `*mut u8` inside `BadBoxSfiArena`!
// Moving `Box<[u8]>` into `Self` and passing `&mut BadBoxSfiArena` recursively retags
// `Box<[u8]>` (`Unique`), disabling the earlier exposed `r14_addr` tag on `with_slice_mut`!
fn ub_box_backing_field_retag() {
    let mut bad = BadBoxSfiArena::new(8192);
    let span_a = SfiSpan { offset: 0, len: 64 };
    bad.with_slice_mut(span_a, |s| s[0] = 41);
    bad.sfi_enter(|r14, _| unsafe { simulated_c_sfi_write(r14, 0, 42) });
}

// Case 5 (SAFE): `SfiArena` (`*mut u8` raw backing, zero `Box` field) + `SfiSpan` (`u32` handles)
// + scoped `with_slice` / `with_slice_mut` suspended across `sfi_enter(&mut arena)`!
fn ok_sfi_arena_span_handles_and_scoped_loan() {
    let mut arena = SfiArena::new(8192);
    let span_a = SfiSpan { offset: 0, len: 64 };
    let span_b = SfiSpan { offset: 4096, len: 64 };

    arena.with_slice_mut(span_a, |s| s[0] = 41);
    arena.with_slice_mut(span_b, |s| s[0] = 100);

    let out = arena.sfi_enter(|r14, arena_cb| {
        // SFI_1 writes to span_a AND arbitrarily scribbles to span_b (4096)!
        unsafe {
            simulated_c_sfi_write(r14, 0, 42);
            simulated_c_sfi_write(r14, 4096, 200);
        }
        // Reentrant Host_cb_2 inspects `span_a` inside a scoped borrow that ENDS before SFI_3!
        let observed_mid = arena_cb.with_slice(span_a, |s| s[0]);
        // Nested SFI_3 writes again without violating any live `&[u8]` or `&mut [u8]`!
        let nested = arena_cb.sfi_enter(|r14_inner, _| {
            unsafe { simulated_c_sfi_write(r14_inner, 0, observed_mid + 1) };
            99u8
        });
        nested
    });

    let final_a = arena.with_slice(span_a, |s| s[0]);
    let final_b = arena.with_slice(span_b, |s| s[0]);
    assert_eq!((out, final_a, final_b), (99, 43, 200));
    println!("MIRI_OK final_a={} final_b={}", final_a, final_b);
}

fn main() {
    let case = std::env::args().nth(1).unwrap_or_default();
    match case.as_str() {
        "ub_frozen" => ub_frozen_ref_across_writable_sfi(),
        "ub_sibling_mut" => ub_sibling_mut_slice_across_sfi_oob_write(),
        "ub_reentrant_cb" => ub_reentrant_cb_slice_across_nested_sfi(),
        "ub_box_backing" => ub_box_backing_field_retag(),
        "ok_sfi_arena" => ok_sfi_arena_span_handles_and_scoped_loan(),
        _ => panic!("unknown case"),
    }
}
"""


def run_linux_vm_bleed(td: Path) -> dict[str, object]:
    c_path = td / "vm_bleed.c"
    bin_path = td / "vm_bleed"
    c_path.write_text(LINUX_VM_BLEED_C)
    subprocess.run(["gcc", "-O2", "-Wall", "-Wextra", str(c_path), "-o", str(bin_path)], check=True)
    r = subprocess.run([str(bin_path)], capture_output=True, text=True, check=True)
    return json.loads(r.stdout.strip())


def run_miri_suite(td: Path) -> dict[str, object]:
    proj = td / "sfi_tb_probe"
    (proj / "src").mkdir(parents=True)
    (proj / "Cargo.toml").write_text(MIRI_TB_CARGO_TOML)
    (proj / "src" / "main.rs").write_text(MIRI_TB_MAIN_RS)

    ver = subprocess.run(["cargo", "+nightly", "miri", "--version"], capture_output=True, text=True, check=True).stdout.strip()
    env = dict(os.environ)
    env["MIRIFLAGS"] = "-Zmiri-tree-borrows -Zmiri-permissive-provenance"
    env["CARGO_TARGET_DIR"] = str(td / "miri_target")

    out: dict[str, object] = {"miri_version": ver, "cases": {}}
    for c in ["ub_frozen", "ub_sibling_mut", "ub_reentrant_cb", "ub_box_backing", "ok_sfi_arena"]:
        r = subprocess.run(
            ["cargo", "+nightly", "miri", "run", "--quiet", "--", c],
            cwd=str(proj),
            env=env,
            capture_output=True,
            text=True,
        )
        # Strip temp directory paths from Miri stderr so saved receipts are path-clean!
        clean_err = r.stderr.replace(str(td), "<TMP>")
        err_lines = [ln for ln in clean_err.splitlines() if "error: Undefined Behavior:" in ln or "write access through" in ln]
        out["cases"][c] = {
            "rc": r.returncode,
            "stdout": r.stdout.strip(),
            "ub_detected": "Undefined Behavior:" in r.stderr,
            "ub_headline": err_lines[0] if err_lines else "",
        }
    return out


def main() -> int:
    with tempfile.TemporaryDirectory() as td_str:
        td = Path(td_str)
        vm_res = run_linux_vm_bleed(td)
        miri_res = run_miri_suite(td)

    assert vm_res["bleed_corrupted"] is True
    assert vm_res["zc_read_matches"] is True
    assert vm_res["ro_write_trapped"] is True and vm_res["ro_si_code"] == vm_res["segv_accerr_const"]
    assert vm_res["host_unmutated"] is True
    assert vm_res["guard_trapped"] is True and vm_res["guard_si_code"] == vm_res["segv_accerr_const"]

    mc = miri_res["cases"]
    assert mc["ub_frozen"]["ub_detected"] is True
    assert mc["ub_sibling_mut"]["ub_detected"] is True
    assert mc["ub_reentrant_cb"]["ub_detected"] is True
    assert mc["ub_box_backing"]["ub_detected"] is True
    assert mc["ok_sfi_arena"]["rc"] == 0 and mc["ok_sfi_arena"]["ub_detected"] is False

    res = {"linux_vm_4kib_and_memfd": vm_res, "miri_tree_borrows": miri_res}
    (HERE / "zerocopy_tb_and_page_bleed_results.json").write_text(json.dumps(res, indent=2) + "\n")
    print("ALL_ZEROCOPY_VM_AND_MIRI_TB_CHECKS_PASSED")
    print(json.dumps(res, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
