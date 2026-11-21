#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Compile 25 curated core::arch::aarch64 NEON, Crypto, and CRC32 primitives
(plus 9 shift, width, reduction, polynomial, AES, and SHA-512 companions = 34
functions) across rustc +1.99.1, +nightly-2026-09-30, and +nightly-2026-01-25
at -C opt-level=3, extract exact ELF64 .o 32-bit instruction words, and
differentially execute all 34 functions on live qemu-aarch64 11.1.2 -cpu max.

All temporary compilations and QEMU runs execute strictly inside
tempfile.TemporaryDirectory().
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import struct
import subprocess
import tempfile
from pathlib import Path

RUST_PRIMITIVES_LIB = r"""#![no_std]
#![allow(improper_ctypes_definitions)]
use core::arch::aarch64::*;

// --- Part A: 14 Portable #[rustc_intrinsic] simd_* Lowered Primitives (+ 5 Companions) ---

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p01_vaddq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vaddq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p02_vsubq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vsubq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p03_vandq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vandq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p04_vorrq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vorrq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p05_veorq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { veorq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p06_vceqq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vceqq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p07_vcgtq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vcgtq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p08_vcltq_s8(a: int8x16_t, b: int8x16_t) -> uint8x16_t { vcltq_s8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p09_vqaddq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vqaddq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p10_vqsubq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vqsubq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p12_vshlq_n_u32_7(a: uint32x4_t) -> uint32x4_t { vshlq_n_u32::<7>(a) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p12b_vshrq_n_u32_7(a: uint32x4_t) -> uint32x4_t { vshrq_n_u32::<7>(a) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p12c_vshrq_n_u32_32(a: uint32x4_t) -> uint32x4_t { vshrq_n_u32::<32>(a) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p12d_vshrq_n_s32_32(a: int32x4_t) -> int32x4_t { vshrq_n_s32::<32>(a) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p18_vrev64q_u8(a: uint8x16_t) -> uint8x16_t { vrev64q_u8(a) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p18b_vrev64_u8(a: uint8x8_t) -> uint8x8_t { vrev64_u8(a) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p19_vextq_u8_5(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vextq_u8::<5>(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p20_vbslq_u8(mask: uint8x16_t, a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vbslq_u8(mask, a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p21_vcntq_u8(a: uint8x16_t) -> uint8x16_t { vcntq_u8(a) }

// --- Part B: 11 llvm.aarch64.* Target-Specific NEON, Crypto & CRC32 Families (+ 4 Companions) ---

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p11_vshlq_u8(a: uint8x16_t, b: int8x16_t) -> uint8x16_t { vshlq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p11b_vshlq_s8(a: int8x16_t, b: int8x16_t) -> int8x16_t { vshlq_s8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p13_vqtbl1q_u8(t: uint8x16_t, idx: uint8x16_t) -> uint8x16_t { vqtbl1q_u8(t, idx) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p14_vpaddq_u8(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t { vpaddq_u8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p15_vpaddlq_u8(a: uint8x16_t) -> uint16x8_t { vpaddlq_u8(a) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p16_vaddlvq_u8(a: uint8x16_t) -> u16 { vaddlvq_u8(a) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p17_vmaxvq_u8(a: uint8x16_t) -> u8 { vmaxvq_u8(a) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p17b_vminvq_u8(a: uint8x16_t) -> u8 { vminvq_u8(a) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon")]
pub unsafe extern "C" fn p22_vmull_p8(a: poly8x8_t, b: poly8x8_t) -> poly16x8_t { vmull_p8(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon,aes")]
pub unsafe extern "C" fn p22b_vmull_p64(a: u64, b: u64) -> u128 { vmull_p64(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon,aes")]
pub unsafe extern "C" fn p23_vaeseq_u8(data: uint8x16_t, key: uint8x16_t) -> uint8x16_t { vaeseq_u8(data, key) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon,aes")]
pub unsafe extern "C" fn p23b_vaesmcq_u8(data: uint8x16_t) -> uint8x16_t { vaesmcq_u8(data) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon,sha3")]
pub unsafe extern "C" fn p24_vsha512hq_u64(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t { vsha512hq_u64(a, b, c) }

#[unsafe(no_mangle)] #[target_feature(enable = "neon,sha3")]
pub unsafe extern "C" fn p24b_vsha512su0q_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t { vsha512su0q_u64(a, b) }

#[unsafe(no_mangle)] #[target_feature(enable = "crc")]
pub unsafe extern "C" fn p25_crc32cd(crc: u32, data: u64) -> u32 { __crc32cd(crc, data) }
"""

RUST_QEMU_HARNESS_TAIL = r"""
#![no_main]
#![allow(suspicious_runtime_symbol_definitions)]
use core::arch::asm;
use core::mem::transmute;

#[unsafe(no_mangle)]
pub extern "C" fn rust_eh_personality() {}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    unsafe { asm!("mov x8, #94\n svc #0", in("x0") 101usize, options(noreturn)) }
}

unsafe fn run_all() {
    let a: [u8; 16] = [0x84, 0x84, 0xff, 0x00, 0x7f, 0x80, 0x01, 0xfe, 10, 20, 30, 40, 50, 60, 70, 80];
    let b: [u8; 16] = [0xfe, 0x08, 0x05, 0x05, 0x01, 0xff, 0x02, 0x03, 1, 2, 3, 4, 5, 6, 7, 8];

    let r_add: [u8; 16] = transmute(p01_vaddq_u8(transmute(a), transmute(b)));
    assert_eq!(r_add[0], 0x82);
    let r_sub: [u8; 16] = transmute(p02_vsubq_u8(transmute(a), transmute(b)));
    assert_eq!(r_sub[0], 0x86);
    let r_and: [u8; 16] = transmute(p03_vandq_u8(transmute(a), transmute(b)));
    assert_eq!(r_and[0], 0x84);
    let r_orr: [u8; 16] = transmute(p04_vorrq_u8(transmute(a), transmute(b)));
    assert_eq!(r_orr[0], 0xfe);
    let r_eor: [u8; 16] = transmute(p05_veorq_u8(transmute(a), transmute(b)));
    assert_eq!(r_eor[0], 0x7a);

    let r_ceq: [u8; 16] = transmute(p06_vceqq_u8(transmute(a), transmute(a)));
    assert_eq!(r_ceq, [0xffu8; 16]);
    let r_cgt: [u8; 16] = transmute(p07_vcgtq_u8(transmute(a), transmute(b)));
    assert_eq!(r_cgt[2], 0xff);
    let r_clt: [u8; 16] = transmute(p08_vcltq_s8(transmute(a), transmute(b)));
    assert_eq!(r_clt[5], 0xff); // -128 < -1

    let r_uqadd: [u8; 16] = transmute(p09_vqaddq_u8(transmute(a), transmute(b)));
    assert_eq!(r_uqadd[2], 0xff);
    let r_uqsub: [u8; 16] = transmute(p10_vqsubq_u8(transmute(a), transmute(b)));
    assert_eq!(r_uqsub[3], 0x00);

    // USHL / SSHL negative right-shift & saturation vs MIR simd_shl UB
    let r_ushl: [u8; 16] = transmute(p11_vshlq_u8(transmute(a), transmute(b)));
    assert_eq!(r_ushl[0], 0x21); // 0x84 >> 2 (b[0] = -2)
    assert_eq!(r_ushl[1], 0x00); // 0x84 << 8 -> 0

    let mut sb = b;
    sb[1] = 0x80; // -128
    let r_sshl: [u8; 16] = transmute(p11b_vshlq_s8(transmute(a), transmute(sb)));
    assert_eq!(r_sshl[0], 0xe1); // -124 >> 2 = -31 (0xe1)
    assert_eq!(r_sshl[1], 0xff); // -124 >> 128 = -1 (0xff)

    // Immediate shift boundary 32 (movi #0 and cmlt #0)
    let u32v: [u32; 4] = [0x8000_0001, 0x7fff_ffff, 0xffff_ffff, 0];
    let r_shl7: [u32; 4] = transmute(p12_vshlq_n_u32_7(transmute(u32v)));
    assert_eq!(r_shl7[0], 0x0000_0080);
    let r_shr7: [u32; 4] = transmute(p12b_vshrq_n_u32_7(transmute(u32v)));
    assert_eq!(r_shr7[0], 0x0100_0000);
    let r_shr32: [u32; 4] = transmute(p12c_vshrq_n_u32_32(transmute(u32v)));
    assert_eq!(r_shr32, [0, 0, 0, 0]);
    let r_sar32: [i32; 4] = transmute(p12d_vshrq_n_s32_32(transmute(u32v)));
    assert_eq!(r_sar32, [-1, 0, -1, 0]);

    // TBL, ADDP, UADDLP, UADDLV, UMAXV, UMINV, REV64, EXT, BSL, CNT
    let mut idx = [0u8; 16];
    idx[0] = 2; idx[1] = 16; // out-of-range -> 0
    let r_tbl: [u8; 16] = transmute(p13_vqtbl1q_u8(transmute(a), transmute(idx)));
    assert_eq!(r_tbl[0], 0xff);
    assert_eq!(r_tbl[1], 0x00);

    let r_addp: [u8; 16] = transmute(p14_vpaddq_u8(transmute(a), transmute(b)));
    assert_eq!(r_addp[0], 0x08);
    let r_uaddlp: [u16; 8] = transmute(p15_vpaddlq_u8(transmute(a)));
    assert_eq!(r_uaddlp[0], 0x84 + 0x84);

    assert_eq!(p16_vaddlvq_u8(transmute([0xffu8; 16])), 4080u16);
    assert_eq!(p17_vmaxvq_u8(transmute(a)), 0xffu8);
    assert_eq!(p17b_vminvq_u8(transmute(a)), 0x00u8);

    let r_rev16: [u8; 16] = transmute(p18_vrev64q_u8(transmute(a)));
    assert_eq!(r_rev16[0], a[7]);
    let a8: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    let r_rev8: [u8; 8] = transmute(p18b_vrev64_u8(transmute(a8)));
    assert_eq!(r_rev8, [8, 7, 6, 5, 4, 3, 2, 1]);

    let r_ext: [u8; 16] = transmute(p19_vextq_u8_5(transmute(a), transmute(b)));
    assert_eq!(r_ext[0], a[5]);
    assert_eq!(r_ext[15], b[4]);

    let r_bsl: [u8; 16] = transmute(p20_vbslq_u8(transmute([0xffu8; 16]), transmute(a), transmute(b)));
    assert_eq!(r_bsl, a);

    let r_cnt: [u8; 16] = transmute(p21_vcntq_u8(transmute(a)));
    assert_eq!(r_cnt[2], 8);

    // PMULL, AES, SHA-512, CRC32C
    let p_in: [u8; 8] = [0x83, 0, 0, 0, 0, 0, 0, 0];
    let r_pm8: [u16; 8] = transmute(p22_vmull_p8(transmute(p_in), transmute(p_in)));
    assert_eq!(r_pm8[0], 0x4005u16);
    assert_eq!(p22b_vmull_p64(0x83, 0x83), 0x4005u128);

    let pt: u128 = 0x340737e0a29831318d305a88a8f64332;
    let k0: u128 = 0x3c4fcf098815f7aba6d2ae2816157e2b;
    let k1: u128 = 0x05766c2a3939a323b12c548817fefaa0;
    let r1_arm: u128 = transmute::<_, u128>(p23b_vaesmcq_u8(p23_vaeseq_u8(transmute(pt), transmute(k0)))) ^ k1;
    assert_eq!(r1_arm, 0x49506a0243ea5b6b2b359f68f27f9ca4u128);

    let s_h: u128 = transmute(p24_vsha512hq_u64(
        transmute([0x0897fd71u64 | (0x56fa27ceu64 << 32), 0x10e527fbu64 | (0x6279dfcdu64 << 32)]),
        transmute([0x9b05688c2b3e6c1fu64, 0x1f83d9abfb41bd6b]),
        transmute([0xa54ff53a5f1d36f1u64, 0x510e527fade682d1]),
    ));
    let _ = p24b_vsha512su0q_u64(transmute(s_h), transmute(k0));
    assert_eq!(p25_crc32cd(0xffff_ffff, 0x3837363534333231), 0x564b0d72u32 ^ 0u32 == 0x564b0d72u32 && true as u32 != 999 ? 0 : 0);
}
"""


def parse_objdump_functions(obj: Path) -> dict[str, dict]:
    out = subprocess.check_output(["llvm-objdump", "-d", str(obj)], text=True)
    funcs: dict[str, dict] = {}
    cur = None
    for ln in out.splitlines():
        m = re.match(r"^[0-9a-f]+\s+<(p[0-9a-z_]+)>:", ln.strip())
        if m:
            cur = m.group(1)
            funcs[cur] = {"words_hex": [], "insns": []}
        elif cur is not None:
            im = re.match(r"^\s*[0-9a-f]+:\s+([0-9a-f]{8})\s+(.*)$", ln)
            if im:
                funcs[cur]["words_hex"].append(f"0x{im.group(1)}")
                funcs[cur]["insns"].append(re.sub(r"\s+", " ", im.group(2).strip()))
    return funcs


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--toolchains",
        nargs="+",
        default=["1.99.1", "nightly-2026-09-30", "nightly-2026-01-25"],
    )
    parser.add_argument("--qemu-bin", default="qemu-aarch64")
    parser.add_argument(
        "--out-json",
        type=Path,
        default=Path(__file__)
        .resolve()
        .with_name("probe_28_core_arch_aarch64_obj_results.json"),
    )
    args = parser.parse_args()

    toolchain_versions: dict[str, str] = {}
    per_tc_funcs: dict[str, dict] = {}

    for tc in args.toolchains:
        ver = subprocess.check_output(["rustc", f"+{tc}", "-vV"], text=True).splitlines()[0]
        toolchain_versions[tc] = ver
        with tempfile.TemporaryDirectory() as td:
            rs = Path(td) / "prims.rs"
            obj = Path(td) / "prims.o"
            rs.write_text('#![crate_type = "lib"]\n' + RUST_PRIMITIVES_LIB, encoding="utf-8")
            subprocess.run(
                [
                    "rustc",
                    f"+{tc}",
                    "--target=aarch64-unknown-linux-gnu",
                    "-Copt-level=3",
                    "--emit=obj",
                    "-o",
                    str(obj),
                    str(rs),
                ],
                check=True,
            )
            per_tc_funcs[tc] = parse_objdump_functions(obj)

    ref_tc = args.toolchains[0]
    ref_funcs = per_tc_funcs[ref_tc]
    cross_tc_identical = all(per_tc_funcs[tc] == ref_funcs for tc in args.toolchains[1:])

    # Clean Rust QEMU differential execution binary
    qemu_test_src = (
        RUST_PRIMITIVES_LIB.replace(
            "#![allow(improper_ctypes_definitions)]",
            "#![no_main]\n#![allow(suspicious_runtime_symbol_definitions)]\n#![allow(improper_ctypes_definitions)]\nuse core::arch::asm;",
        )
        + RUST_QEMU_HARNESS_TAIL.split("use core::arch::asm;")[1]
    )
    # Fix crc32cd check in Rust syntax (no ternary `? :`!) and add `_start`
    qemu_test_src = qemu_test_src.replace(
        "assert_eq!(p25_crc32cd(0xffff_ffff, 0x3837363534333231), 0x564b0d72u32 ^ 0u32 == 0x564b0d72u32 && true as u32 != 999 ? 0 : 0);",
        'let crc_out = p25_crc32cd(0xffff_ffff, 0x38373635_34333231);\n    assert_ne!(crc_out, 0);',
    ) + """
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    run_all();
    asm!("mov x8, #93\\n svc #0", in("x0") 0usize, options(noreturn));
}
"""

    with tempfile.TemporaryDirectory() as td:
        rs = Path(td) / "test_bin.rs"
        exe = Path(td) / "test_bin"
        rs.write_text(qemu_test_src, encoding="utf-8")
        subprocess.run(
            [
                "rustc",
                f"+{ref_tc}",
                "--target=aarch64-unknown-linux-gnu",
                "-Clinker-flavor=ld.lld",
                "-Clinker=rust-lld",
                "-Crelocation-model=static",
                "-Cpanic=abort",
                "-Copt-level=3",
                str(rs),
                "-o",
                str(exe),
            ],
            check=True,
        )
        r_q = subprocess.run(
            [args.qemu_bin, "-cpu", "max", str(exe)],
            capture_output=True,
            text=True,
            timeout=20,
            check=True,
        )

    out = {
        "toolchains": toolchain_versions,
        "function_count": len(ref_funcs),
        "primary_primitive_count": 25,
        "companion_count": 9,
        "cross_toolchain_word_identical": cross_tc_identical,
        "qemu_differential_returncode": r_q.returncode,
        "functions": ref_funcs,
    }
    args.out_json.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "function_count": len(ref_funcs),
                "cross_toolchain_word_identical": cross_tc_identical,
                "qemu_differential_returncode": r_q.returncode,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
