#!/usr/bin/env python3
"""Live Armv8.5-A MTE (16-byte tag granule) + SVE empirical probe executed
under `qemu-aarch64 -cpu max` from a static `#![no_std]` AArch64 binary
compiled by `rustc +1.99.1 --target aarch64-unknown-linux-gnu`.

Uses tempfile.TemporaryDirectory() exclusively for transient build artifacts.
"""

from __future__ import annotations

import glob
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True


AARCH64_MTE_RUST_SRC = r"""
#![no_std]
#![no_main]

use core::arch::aarch64::uint8x16_t;
use core::arch::asm;

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    exit_group(99)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_eh_personality() {}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memset(dst: *mut u8, c: i32, n: usize) -> *mut u8 {
    let mut i = 0usize;
    while i < n {
        unsafe { core::ptr::write_volatile(dst.add(i), c as u8); }
        i += 1;
    }
    dst
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memcpy(dst: *mut u8, src: *const u8, n: usize) -> *mut u8 {
    let mut i = 0usize;
    while i < n {
        unsafe { core::ptr::write_volatile(dst.add(i), *src.add(i)); }
        i += 1;
    }
    dst
}

#[repr(C)]
struct KernelSigAction {
    sa_handler: usize,
    sa_flags: usize,
    sa_mask: u64,
}

#[repr(C)]
struct SigInfoHeader {
    si_signo: i32,
    si_errno: i32,
    si_code: i32,
    _pad: i32,
    si_addr: usize,
}

static mut PAGE_BASE: usize = 0;

unsafe fn syscall6(
    n: usize,
    a0: usize,
    a1: usize,
    a2: usize,
    a3: usize,
    a4: usize,
    a5: usize,
) -> isize {
    let ret: isize;
    unsafe {
        asm!(
            "svc #0",
            in("x8") n,
            inout("x0") a0 => ret,
            in("x1") a1,
            in("x2") a2,
            in("x3") a3,
            in("x4") a4,
            in("x5") a5,
            options(nostack),
        );
    }
    ret
}

fn write_stdout(buf: &[u8]) {
    unsafe {
        let _ = syscall6(64, 1, buf.as_ptr() as usize, buf.len(), 0, 0, 0);
    }
}

fn exit_group(code: usize) -> ! {
    unsafe {
        let _ = syscall6(94, code, 0, 0, 0, 0, 0);
    }
    loop {}
}

fn write_u64_dec(mut v: u64) {
    let mut tmp = [0u8; 24];
    if v == 0 {
        write_stdout(b"0");
        return;
    }
    let mut i = 24usize;
    while v > 0 {
        i -= 1;
        tmp[i] = b'0' + ((v % 10) as u8);
        v /= 10;
    }
    write_stdout(&tmp[i..24]);
}

fn write_i32_dec(v: i32) {
    if v < 0 {
        write_stdout(b"-");
        write_u64_dec((-(v as i64)) as u64);
    } else {
        write_u64_dec(v as u64);
    }
}

unsafe extern "C" fn segv_handler(sig: i32, info: *const SigInfoHeader, _uctx: *mut u8) {
    unsafe {
        let code = (*info).si_code;
        let raw_addr = (*info).si_addr;
        let untagged = raw_addr & 0x00ff_ffff_ffff_ffffusize;
        let tag = (raw_addr >> 56) & 0xff;
        let base = PAGE_BASE;
        let off = untagged.wrapping_sub(base);
        write_stdout(b"{\"faulted\":true,\"si_signo\":");
        write_i32_dec(sig);
        write_stdout(b",\"si_code\":");
        write_i32_dec(code);
        write_stdout(b",\"fault_offset\":");
        write_u64_dec(off as u64);
        write_stdout(b",\"fault_ptr_tag\":");
        write_u64_dec(tag as u64);
        write_stdout(b"}\n");
        exit_group(0);
    }
}

unsafe fn install_segv_handler() {
    let act = KernelSigAction {
        sa_handler: segv_handler as *const () as usize,
        sa_flags: 0x0000_0004, // SA_SIGINFO
        sa_mask: 0,
    };
    let rc = unsafe {
        syscall6(134, 11, (&raw const act) as usize, 0, 8, 0, 0)
    };
    if rc != 0 {
        exit_group(210);
    }
}

#[inline(always)]
unsafe fn stg_16(tagged_addr: usize) {
    unsafe {
        asm!(
            ".arch armv8.5-a+memtag",
            "stg {p}, [{p}]",
            p = in(reg) tagged_addr,
            options(nostack),
        );
    }
}

fn memchr_scalar(needle: u8, ptr: *const u8, len: usize) -> isize {
    let mut i = 0usize;
    while i < len {
        let b = unsafe { *ptr.add(i) };
        if b == needle {
            return i as isize;
        }
        i += 1;
    }
    -1
}

/// MTE-safe AArch64 NEON 16-byte aligned over-read memchr:
/// - Preserves MTE logical tag `[59:56]` via `bic algn, ptr, #15`
/// - Every `ldr q, [algn]` accesses one 16B MTE granule `[algn, algn + 16)`
///   containing at least 1 byte of `[ptr, ptr + len)`.
unsafe fn memchr_neon_mte_safe(needle: u8, ptr: *const u8, len: usize) -> isize {
    if len == 0 {
        return -1;
    }
    let out: isize;
    unsafe {
        asm!(
            "dup {vn:v}.16b, {needle:w}",
            "bic {algn}, {ptr}, #15",
            "and {mis}, {ptr}, #15",
            "ldr {vd:q}, [{algn}]",
            "cmeq {vc:v}.16b, {vd:v}.16b, {vn:v}.16b",
            "shrn {ve:v}.8b, {vc:v}.8h, #4",
            "fmov {synd}, {ve:d}",
            "lsl {sh}, {mis}, #2",
            "lsr {synd}, {synd}, {sh}",
            "mov {rem1}, #16",
            "sub {rem1}, {rem1}, {mis}",
            "cmp {len}, {rem1}",
            "b.hi 2f",
            "cbz {synd}, 5f",
            "rbit {synd}, {synd}",
            "clz {synd}, {synd}",
            "lsr {synd}, {synd}, #2",
            "cmp {synd}, {len}",
            "b.hs 5f",
            "mov {out}, {synd}",
            "b 6f",
            "2:",
            "cbnz {synd}, 4f",
            "add {algn}, {algn}, #16",
            "sub {rem}, {len}, {rem1}",
            "3:",
            "cmp {rem}, #16",
            "b.ls 7f",
            "ldr {vd:q}, [{algn}]",
            "cmeq {vc:v}.16b, {vd:v}.16b, {vn:v}.16b",
            "shrn {ve:v}.8b, {vc:v}.8h, #4",
            "fmov {synd}, {ve:d}",
            "cbnz {synd}, 8f",
            "add {algn}, {algn}, #16",
            "sub {rem}, {rem}, #16",
            "b 3b",
            "4:",
            "rbit {synd}, {synd}",
            "clz {synd}, {synd}",
            "lsr {out}, {synd}, #2",
            "b 6f",
            "7:",
            "ldr {vd:q}, [{algn}]",
            "cmeq {vc:v}.16b, {vd:v}.16b, {vn:v}.16b",
            "shrn {ve:v}.8b, {vc:v}.8h, #4",
            "fmov {synd}, {ve:d}",
            "cbz {synd}, 5f",
            "rbit {synd}, {synd}",
            "clz {synd}, {synd}",
            "lsr {synd}, {synd}, #2",
            "cmp {synd}, {rem}",
            "b.hs 5f",
            "sub {algn}, {algn}, {ptr}",
            "add {out}, {algn}, {synd}",
            "b 6f",
            "8:",
            "rbit {synd}, {synd}",
            "clz {synd}, {synd}",
            "lsr {synd}, {synd}, #2",
            "sub {algn}, {algn}, {ptr}",
            "add {out}, {algn}, {synd}",
            "b 6f",
            "5:",
            "mov {out}, #-1",
            "6:",
            ptr = in(reg) ptr,
            len = in(reg) len,
            needle = in(reg) needle as u32,
            algn = out(reg) _,
            mis = out(reg) _,
            sh = out(reg) _,
            synd = out(reg) _,
            rem1 = out(reg) _,
            rem = out(reg) _,
            out = out(reg) out,
            vn = out(vreg) _,
            vd = out(vreg) _,
            vc = out(vreg) _,
            ve = out(vreg) _,
            options(readonly, nostack),
        );
    }
    out
}

unsafe fn run_case(case_id: u8, base: usize) {
    unsafe {
        for g in 0..256usize {
            let tag = 1usize + (g % 14);
            stg_16((base + g * 16) | (tag << 56));
        }

        match case_id {
            b'0' => {
                let alloc_tag = 5usize;
                let left_guard_tag = 9usize;
                let right_guard_tag = 11usize;
                let needle = 0xA5u8;
                let mut checks = 0u64;

                for start_mis in 0..16usize {
                    for len in 0..=80usize {
                        let start_untagged = base + 64 + start_mis;
                        let end_untagged = start_untagged + len;
                        let first_g = 64 / 16;
                        let last_g = if len == 0 {
                            first_g
                        } else {
                            ((end_untagged - 1) - base) / 16
                        };

                        stg_16((base + 3 * 16) | (left_guard_tag << 56));
                        let p_left = ((base + 3 * 16) | (left_guard_tag << 56)) as *mut u8;
                        core::ptr::write_bytes(p_left, needle, 16);

                        for g in first_g..=last_g {
                            let pg = ((base + g * 16) | (alloc_tag << 56)) as *mut u8;
                            stg_16(pg as usize);
                            core::ptr::write_bytes(pg, needle, 16);
                        }

                        let p_right = ((base + (last_g + 1) * 16) | (right_guard_tag << 56)) as *mut u8;
                        stg_16(p_right as usize);
                        core::ptr::write_bytes(p_right, needle, 16);

                        let hay_ptr = (start_untagged | (alloc_tag << 56)) as *mut u8;
                        if len > 0 {
                            core::ptr::write_bytes(hay_ptr, 0x5A, len);
                        }

                        if memchr_neon_mte_safe(needle, hay_ptr, len) != -1 {
                            exit_group(101);
                        }
                        checks += 1;

                        if len > 0 {
                            *hay_ptr.add(len - 1) = needle;
                            if memchr_neon_mte_safe(needle, hay_ptr, len) != (len - 1) as isize {
                                exit_group(102);
                            }
                            *hay_ptr.add(len - 1) = 0x5A;
                            checks += 1;

                            let mid = len / 2;
                            *hay_ptr.add(mid) = needle;
                            *hay_ptr.add(len - 1) = needle;
                            let exp = memchr_scalar(needle, hay_ptr, len);
                            if memchr_neon_mte_safe(needle, hay_ptr, len) != exp {
                                exit_group(103);
                            }
                            checks += 1;
                        }
                    }
                }
                write_stdout(b"{\"faulted\":false,\"checks_passed\":");
                write_u64_dec(checks);
                write_stdout(b"}\n");
            }
            b'1' => {
                stg_16(base | (1 << 56));
                stg_16((base + 16) | (2 << 56));
                let ptr = base | (1 << 56);
                let algn32 = ptr & !31usize;
                let mut q0: uint8x16_t;
                let mut q1: uint8x16_t;
                asm!(
                    "ldp {q0:q}, {q1:q}, [{p}]",
                    p = in(reg) algn32,
                    q0 = out(vreg) q0,
                    q1 = out(vreg) q1,
                    options(readonly, nostack),
                );
                core::hint::black_box((q0, q1));
                write_stdout(b"{\"faulted\":false}\n");
            }
            b'2' => {
                stg_16(base | (1 << 56));
                stg_16((base + 16) | (2 << 56));
                let ptr = (base + 16) | (2 << 56);
                let algn32 = ptr & !31usize;
                let mut q0: uint8x16_t;
                let mut q1: uint8x16_t;
                asm!(
                    "ldp {q0:q}, {q1:q}, [{p}]",
                    p = in(reg) algn32,
                    q0 = out(vreg) q0,
                    q1 = out(vreg) q1,
                    options(readonly, nostack),
                );
                core::hint::black_box((q0, q1));
                write_stdout(b"{\"faulted\":false}\n");
            }
            b'3' => {
                stg_16(base | (1 << 56));
                stg_16((base + 16) | (2 << 56));
                let ptr = (base + 1) | (1 << 56);
                let mut q0: uint8x16_t;
                asm!(
                    "ldr {q0:q}, [{p}]",
                    p = in(reg) ptr,
                    q0 = out(vreg) q0,
                    options(readonly, nostack),
                );
                core::hint::black_box(q0);
                write_stdout(b"{\"faulted\":false}\n");
            }
            b'4' => {
                stg_16(base | (1 << 56));
                let ptr = (base + 3) | (1 << 56);
                let bad_algn = ptr & 0x0000_ffff_ffff_fff0usize;
                let mut q0: uint8x16_t;
                asm!(
                    "ldr {q0:q}, [{p}]",
                    p = in(reg) bad_algn,
                    q0 = out(vreg) q0,
                    options(readonly, nostack),
                );
                core::hint::black_box(q0);
                write_stdout(b"{\"faulted\":false}\n");
            }
            b'5' => {
                // Discriminator: SVE `ldff1b` across a PROT_NONE MMU page boundary vs
                // QEMU 11.1.2 linux-user SVE MTE-tag-check omission on `ld1b`/`ldff1b`!
                let g2 = syscall6(222, 0, 8192, 0, 0x22, usize::MAX, 0) as usize;
                let _ = syscall6(226, g2, 4096, 1 | 2, 0, 0, 0);
                let p_page_edge = g2 + 4096 - 16;

                stg_16(base | (1 << 56));
                let p_mismatched_tag0 = base | (2 << 56); // granule 0 has tag 1 != 2!

                let vl_bytes: usize;
                let ffr_page_cnt: usize;
                let ffr_mte_cnt: usize;
                asm!(
                    ".arch armv8.5-a+sve+memtag",
                    "rdvl {vl}, #1",
                    "setffr",
                    "ptrue p0.b",
                    "ldff1b {{z0.b}}, p0/z, [{pp}]",
                    "rdffr p1.b",
                    "cntp {cp}, p0, p1.b",
                    "setffr",
                    "ldff1b {{z1.b}}, p0/z, [{pm}]",
                    "rdffr p2.b",
                    "cntp {cm}, p0, p2.b",
                    pp = in(reg) p_page_edge,
                    pm = in(reg) p_mismatched_tag0,
                    vl = out(reg) vl_bytes,
                    cp = out(reg) ffr_page_cnt,
                    cm = out(reg) ffr_mte_cnt,
                    out("v0") _,
                    out("v1") _,
                    options(readonly, nostack),
                );
                let _ = syscall6(215, g2, 8192, 0, 0, 0, 0); // munmap
                write_stdout(b"{\"faulted\":false,\"sve_vl_bytes\":");
                write_u64_dec(vl_bytes as u64);
                write_stdout(b",\"ldff1b_valid_bytes_before_prot_none\":");
                write_u64_dec(ffr_page_cnt as u64);
                write_stdout(b",\"qemu_user_ldff1b_bytes_on_mismatched_mte_tag\":");
                write_u64_dec(ffr_mte_cnt as u64);
                write_stdout(b"}\n");
            }
            _ => exit_group(205),
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let mut cmd_buf = [0u8; 128];
    let mut path = *b"/proc/self/cmdline\0";
    let fd = unsafe { syscall6(56, (-100isize) as usize, path.as_mut_ptr() as usize, 0, 0, 0, 0) };
    let mut case_id = b'0';
    if fd >= 0 {
        let n = unsafe { syscall6(63, fd as usize, cmd_buf.as_mut_ptr() as usize, cmd_buf.len(), 0, 0, 0) };
        let _ = unsafe { syscall6(57, fd as usize, 0, 0, 0, 0, 0) };
        if n > 0 {
            let slice = &cmd_buf[..(n as usize)];
            let mut i = 0usize;
            while i < slice.len() && slice[i] != 0 {
                i += 1;
            }
            if i + 1 < slice.len() && slice[i + 1] != 0 {
                case_id = slice[i + 1];
            }
        }
    }

    let flags = 1usize | (1usize << 1) | (0xfffeusize << 3);
    let rc = unsafe { syscall6(167, 55, flags, 0, 0, 0, 0) };
    if rc != 0 {
        exit_group(200);
    }

    unsafe {
        install_segv_handler();
    }

    let addr = unsafe { syscall6(222, 0, 4096, 0x1 | 0x2 | 0x20, 0x22, usize::MAX, 0) };
    if addr < 0 || (addr as usize) > usize::MAX - 4096 {
        exit_group(201);
    }
    unsafe {
        PAGE_BASE = addr as usize;
        run_case(case_id, addr as usize);
    }
    exit_group(0);
}
"""


def main() -> int:
    out_json_path = (
        Path(__file__).resolve().parent / "probe_aarch64_mte_granules_results.json"
    )
    sysroot = subprocess.check_output(
        ["rustc", "+1.99.1", "--print", "sysroot"], text=True
    ).strip()
    lld_candidates = glob.glob(sysroot + "/**/rust-lld", recursive=True)
    if not lld_candidates:
        raise RuntimeError("rust-lld not found in rustc +1.99.1 sysroot")
    rust_lld = lld_candidates[0]

    qemu_bin = shutil.which("qemu-aarch64")
    if not qemu_bin:
        raise RuntimeError("qemu-aarch64 not found on PATH")
    qemu_ver = (
        subprocess.check_output([qemu_bin, "--version"], text=True)
        .splitlines()[0]
        .strip()
    )
    qemu_sha256 = hashlib.sha256(Path(qemu_bin).read_bytes()).hexdigest()
    rustc_ver = (
        subprocess.check_output(["rustc", "+1.99.1", "-vV"], text=True)
        .splitlines()[0]
        .strip()
    )

    cases = {
        "0": "mte_16b_aligned_neon_memchr_matrix",
        "1": "fault_32b_ldp_trailing_granule_mismatch",
        "2": "fault_32b_ldp_leading_granule_mismatch",
        "3": "fault_16b_unaligned_ldr_crossing_granule",
        "4": "fault_48bit_mask_strips_mte_tag",
        "5": "sve_ldff1b_prot_none_vs_qemu_user_sve_mte_gap",
    }

    out_cases: dict[str, object] = {}
    with tempfile.TemporaryDirectory() as td:
        tdp = Path(td)
        src = tdp / "aarch64_mte_probe.rs"
        binp = tdp / "aarch64_mte_probe"
        src.write_text(AARCH64_MTE_RUST_SRC, encoding="utf-8")

        r_comp = subprocess.run(
            [
                "rustc",
                "+1.99.1",
                "--target",
                "aarch64-unknown-linux-gnu",
                "-C",
                "panic=abort",
                "-C",
                "relocation-model=static",
                "-C",
                "opt-level=2",
                "-C",
                f"linker={rust_lld}",
                "-C",
                "linker-flavor=ld.lld",
                str(src),
                "-o",
                str(binp),
            ],
            capture_output=True,
            text=True,
        )
        if r_comp.returncode != 0:
            sys.stderr.write(f"Compile failed:\n{r_comp.stderr}\n")
            return 1

        for cid, name in cases.items():
            rq = subprocess.run(
                [qemu_bin, "-cpu", "max", str(binp), cid],
                capture_output=True,
                text=True,
            )
            if rq.returncode != 0:
                sys.stderr.write(
                    f"Case {cid} ({name}) failed rc={rq.returncode}:\nstdout={rq.stdout}\nstderr={rq.stderr}\n"
                )
                return 1
            out_cases[name] = json.loads(rq.stdout.strip())

    assert out_cases["mte_16b_aligned_neon_memchr_matrix"] == {
        "faulted": False,
        "checks_passed": 3856,
    }
    assert out_cases["fault_32b_ldp_trailing_granule_mismatch"] == {
        "faulted": True,
        "si_signo": 11,
        "si_code": 9,
        "fault_offset": 16,
        "fault_ptr_tag": 1,
    }
    assert out_cases["fault_32b_ldp_leading_granule_mismatch"] == {
        "faulted": True,
        "si_signo": 11,
        "si_code": 9,
        "fault_offset": 0,
        "fault_ptr_tag": 2,
    }
    assert out_cases["fault_16b_unaligned_ldr_crossing_granule"] == {
        "faulted": True,
        "si_signo": 11,
        "si_code": 9,
        "fault_offset": 16,
        "fault_ptr_tag": 1,
    }
    assert out_cases["fault_48bit_mask_strips_mte_tag"] == {
        "faulted": True,
        "si_signo": 11,
        "si_code": 9,
        "fault_offset": 0,
        "fault_ptr_tag": 0,
    }
    assert out_cases["sve_ldff1b_prot_none_vs_qemu_user_sve_mte_gap"][
        "ldff1b_valid_bytes_before_prot_none"
    ] == 16

    result = {
        "rustc": rustc_ver,
        "target": "aarch64-unknown-linux-gnu",
        "qemu": qemu_ver,
        "qemu_binary_sha256": qemu_sha256,
        "linux_aarch64_SEGV_MTESERR_const": 9,
        "cases": out_cases,
    }
    out_json_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
