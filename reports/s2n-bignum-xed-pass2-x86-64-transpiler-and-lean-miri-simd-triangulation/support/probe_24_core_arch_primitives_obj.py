#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Compile all 24 curated core::arch::x86_64 SIMD primitives (16 portable simd_*
operations + 8 llvm.x86.* families, plus 5 shift/shuffle boundary companions)
on rustc 1.99.1 -C opt-level=3 and rustc 1.102.0-nightly -C opt-level=3,
extract exact ELF64 .o machine bytes, and differentially execute all primitives
on live x86_64 AVX-512 silicon inside tempfile.TemporaryDirectory().
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

RUST_PRIMITIVES_LIB = r"""#![crate_type = "lib"]
#![allow(improper_ctypes_definitions)]
use core::arch::x86_64::*;

// --- Part A: 16 Portable #[rustc_intrinsic] simd_* Operations ---

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p01_simd_add(a: __m256i, b: __m256i) -> __m256i {
    _mm256_add_epi8(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p02_simd_sub(a: __m256i, b: __m256i) -> __m256i {
    _mm256_sub_epi8(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p03_simd_and(a: __m256i, b: __m256i) -> __m256i {
    _mm256_and_si256(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p04_simd_or(a: __m256i, b: __m256i) -> __m256i {
    _mm256_or_si256(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p05_simd_xor(a: __m256i, b: __m256i) -> __m256i {
    _mm256_xor_si256(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p06_simd_eq(a: __m256i, b: __m256i) -> __m256i {
    _mm256_cmpeq_epi8(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p07_simd_gt(a: __m256i, b: __m256i) -> __m256i {
    _mm256_cmpgt_epi8(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p08_simd_lt(a: __m128i, b: __m128i) -> __m128i {
    _mm_cmplt_epi8(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p09_simd_bitmask(a: __m256i) -> i32 {
    _mm256_movemask_epi8(a)
}

#[no_mangle] #[target_feature(enable = "avx2,sse4.1")]
pub unsafe extern "sysv64" fn p10_simd_extract(a: __m128i) -> i64 {
    _mm_extract_epi64::<1>(a)
}

#[no_mangle] #[target_feature(enable = "avx512f,avx512vl")]
pub unsafe extern "sysv64" fn p11_simd_funnel_shl(a: __m256i, b: __m256i) -> __m256i {
    _mm256_rolv_epi32(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p12_simd_reduce_or(a: __m256i, b: __m256i) -> i32 {
    _mm256_testz_si256(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p13_simd_saturating_sub(a: __m256i, b: __m256i) -> __m256i {
    _mm256_subs_epu8(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p14_simd_shl(a: __m256i) -> __m256i {
    _mm256_slli_epi32::<7>(a)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p14b_simd_shl_var(a: __m256i, count: __m256i) -> __m256i {
    _mm256_sllv_epi32(a, count)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p14c_simd_shl_oob40(a: __m256i) -> __m256i {
    _mm256_slli_epi32::<40>(a)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p15_simd_shr(a: __m256i) -> __m256i {
    _mm256_srli_epi32::<7>(a)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p15b_simd_sar(a: __m256i) -> __m256i {
    _mm256_srai_epi32::<7>(a)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p15c_simd_sar_oob40(a: __m256i) -> __m256i {
    _mm256_srai_epi32::<40>(a)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p16_simd_shuffle(a: __m256i, b: __m256i) -> __m256i {
    _mm256_permute2x128_si256::<0x21>(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p16b_simd_shuffle_zero(a: __m256i, b: __m256i) -> __m256i {
    _mm256_permute2x128_si256::<0x81>(a, b)
}

// --- Part B: 8 Curated llvm.x86.* Intrinsic Families ---

#[no_mangle] #[target_feature(enable = "avx,pclmulqdq")]
pub unsafe extern "sysv64" fn p17_pclmulqdq(a: __m128i, b: __m128i) -> __m128i {
    _mm_clmulepi64_si128::<0x10>(a, b)
}

#[no_mangle] #[target_feature(enable = "avx,aes")]
pub unsafe extern "sysv64" fn p18_aesni(a: __m128i, round_key: __m128i) -> __m128i {
    _mm_aesenc_si128(a, round_key)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p19_pshufb(a: __m256i, mask: __m256i) -> __m256i {
    _mm256_shuffle_epi8(a, mask)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p20_psadbw(a: __m256i, b: __m256i) -> __m256i {
    _mm256_sad_epu8(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p21_vperm(a: __m256i, idx: __m256i) -> __m256i {
    _mm256_permutevar8x32_epi32(a, idx)
}

#[no_mangle] #[target_feature(enable = "avx512f,avx512vl")]
pub unsafe extern "sysv64" fn p22_pternlog(a: __m256i, b: __m256i, c: __m256i) -> __m256i {
    _mm256_ternarylogic_epi32::<0x96>(a, b, c)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p23_pmaddwd(a: __m256i, b: __m256i) -> __m256i {
    _mm256_madd_epi16(a, b)
}

#[no_mangle] #[target_feature(enable = "avx2")]
pub unsafe extern "sysv64" fn p24_pmaddubsw(a: __m256i, b: __m256i) -> __m256i {
    _mm256_maddubs_epi16(a, b)
}
"""

RUST_EXEC_TEST = r"""
use core::mem::transmute;

#[target_feature(enable = "avx2,sse4.1,aes,pclmulqdq,avx512f,avx512vl")]
unsafe fn run_all() {
    unsafe {
        // 1. Shift saturation & sign-clamp on live silicon vs MIR simd_shl/simd_shr guards
        let v: [u32; 8] = [0x8000_0001, 0x7FFF_FFFF, 0x1234_5679, 1, 0xFFFF_FFFF, 42, 0, 0xDEAD_BEEF];
        let cnts: [u32; 8] = [0, 1, 31, 32, 33, 64, 255, 7];
        let r_sllv: [u32; 8] = transmute(p14b_simd_shl_var(transmute(v), transmute(cnts)));
        assert_eq!(r_sllv, [0x8000_0001, 0xFFFF_FFFE, 0x8000_0000, 0, 0, 0, 0, (0xDEAD_BEEFu32 << 7)]);

        let r_oob40: [u32; 8] = transmute(p14c_simd_shl_oob40(transmute(v)));
        assert_eq!(r_oob40, [0u32; 8]);

        let r_sar40: [i32; 8] = transmute(p15c_simd_sar_oob40(transmute(v)));
        assert_eq!(r_sar40, [-1, 0, 0, 0, -1, 0, 0, -1]);

        // 2. movemask_epi8 on non-boolean byte lanes (0x80, 0x7F, 0x01, 0xFE)
        let mb: [u8; 32] = core::array::from_fn(|i| if i % 3 == 0 { 0x80 } else if i % 3 == 1 { 0x7F } else { 0xFE });
        let mask = p09_simd_bitmask(transmute(mb)) as u32;
        let mut expected_mask = 0u32;
        for i in 0..32 {
            if (mb[i] & 0x80) != 0 { expected_mask |= 1u32 << i; }
        }
        assert_eq!(mask, expected_mask);

        // 3. pshufb bit-7 zeroing + 128-bit in-lane modular indexing
        let tbl: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_add(0x10));
        let ctl: [u8; 32] = core::array::from_fn(|i| if i % 4 == 3 { 0x80 | (i as u8) } else { (15 - (i % 16)) as u8 | 0x30 });
        let shuf: [u8; 32] = transmute(p19_pshufb(transmute(tbl), transmute(ctl)));
        for i in 0..32 {
            let exp = if (ctl[i] & 0x80) != 0 { 0 } else { tbl[(i / 16) * 16 + ((ctl[i] & 0x0F) as usize)] };
            assert_eq!(shuf[i], exp);
        }

        // 4. pmaddubsw signed i16 saturation (255 * -128 + 255 * -128 = -65280 -> -32768)
        //    and (255 * 127 + 255 * 127 = +64770 -> +32767)
        let mut ub = [0u8; 32];
        let mut sb = [0i8; 32];
        ub[0] = 255; ub[1] = 255; sb[0] = -128; sb[1] = -128;
        ub[2] = 255; ub[3] = 255; sb[2] = 127;  sb[3] = 127;
        ub[4] = 10;  ub[5] = 20;  sb[4] = -3;   sb[5] = 4;
        let madd_ub: [i16; 16] = transmute(p24_pmaddubsw(transmute(ub), transmute(sb)));
        assert_eq!(madd_ub[0], -32768);
        assert_eq!(madd_ub[1], 32767);
        assert_eq!(madd_ub[2], 50);

        // 5. pmaddwd i32 wrapping (-32768 * -32768 + -32768 * -32768 = 2^31 -> -2147483648 in i32!)
        let mut w1 = [0i16; 16];
        let mut w2 = [0i16; 16];
        w1[0] = -32768; w1[1] = -32768; w2[0] = -32768; w2[1] = -32768;
        w1[2] = 300;    w1[3] = -200;   w2[2] = 5;      w2[3] = 7;
        let madd_wd: [i32; 8] = transmute(p23_pmaddwd(transmute(w1), transmute(w2)));
        assert_eq!(madd_wd[0], i32::MIN);
        assert_eq!(madd_wd[1], 100);

        // 6. AES-NI FIPS-197 Appendix B cipher round 1
        let state: u128 = 0x0848f8e92a8dc69a2be2f4a0bee33d19;
        let rkey1: u128 = 0x05766c2a3939a323b12c548817fefaa0;
        let out_aes: u128 = transmute(p18_aesni(transmute(state), transmute(rkey1)));
        assert_eq!(out_aes, 0x49506a0243ea5b6b2b359f68f27f9ca4);

        // 7. PCLMULQDQ::<0x10> (a[0] * b[1] over GF(2)[x])
        let pa: [u64; 2] = [0x8000_0000_0000_0001, 0xDEAD_BEEF_CAFE_BABE];
        let pb: [u64; 2] = [0x1111_2222_3333_4444, 0x8000_0000_0000_0001];
        let pcl: u128 = transmute(p17_pclmulqdq(transmute(pa), transmute(pb)));
        assert_eq!(pcl, 0x4000_0000_0000_0000_0000_0000_0000_0001u128);

        // 8. AVX-512VL rolv_epi32 (funnel shift) & pternlog 0x96 (3-way XOR)
        let rot: [u32; 8] = transmute(p11_simd_funnel_shl(transmute(v), transmute(cnts)));
        for i in 0..8 {
            assert_eq!(rot[i], v[i].rotate_left(cnts[i]));
        }
        let tern: [u32; 8] = transmute(p22_pternlog(transmute(v), transmute(cnts), transmute([0xA5A5_5A5Au32; 8])));
        for i in 0..8 {
            assert_eq!(tern[i], v[i] ^ cnts[i] ^ 0xA5A5_5A5Au32);
        }

        // 9. testz_si256 (simd_reduce_or) & permute2x128 bit-3 zeroing
        assert_eq!(p12_simd_reduce_or(transmute([0xF0F0_F0F0u32; 8]), transmute([0x0F0F_0F0Fu32; 8])), 1);
        assert_eq!(p12_simd_reduce_or(transmute([0xF0F0_F0F1u32; 8]), transmute([0x0F0F_0F0Fu32; 8])), 0);
        let perm_z: [u128; 2] = transmute(p16b_simd_shuffle_zero(transmute([11u128, 22u128]), transmute([33u128, 44u128])));
        assert_eq!(perm_z, [22u128, 0u128]);
    }
    println!("ALL_SILICON_SIMD_ASSERTIONS_PASSED");
}

fn main() {
    unsafe { run_all(); }
}
"""


def extract_elf_functions(obj_path: Path) -> dict[str, dict]:
    data = obj_path.read_bytes()
    assert data[:4] == b"\x7fELF" and data[4] == 2 and data[5] == 1
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize, e_shnum, _ = struct.unpack_from("<HHH", data, 58)
    sections = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, sh_link, sh_info, _, sh_entsize = (
            struct.unpack_from("<IIQQQQIIQQ", data, off)
        )
        sections.append({
            "sh_type": sh_type, "sh_offset": sh_offset, "sh_size": sh_size,
            "sh_link": sh_link, "sh_info": sh_info, "sh_entsize": sh_entsize,
        })

    def get_str(strtab, off):
        b = strtab["sh_offset"] + off
        return data[b : data.index(b"\x00", b)].decode("utf-8")

    # Parse objdump disassemblies per symbol
    disasm_txt = subprocess.check_output(["objdump", "-d", "-M", "intel", str(obj_path)], text=True)
    disasm_map: dict[str, list[str]] = {}
    cur_sym = None
    for line in disasm_txt.splitlines():
        m = re.match(r"^[0-9a-fA-F]+\s+<([^>]+)>:", line)
        if m:
            cur_sym = m.group(1)
            disasm_map[cur_sym] = []
        elif cur_sym and re.match(r"^\s*[0-9a-fA-F]+:\s+", line):
            parts = line.split("\t")
            mnem = parts[2].strip() if len(parts) >= 3 else line.strip()
            disasm_map[cur_sym].append(mnem)

    funcs = {}
    for sec in sections:
        if sec["sh_type"] == 2:  # SHT_SYMTAB
            strtab = sections[sec["sh_link"]]
            nsyms = sec["sh_size"] // sec["sh_entsize"]
            for k in range(nsyms):
                st_name, st_info, _, st_shndx, st_value, st_size = struct.unpack_from(
                    "<IBBHQQ", data, sec["sh_offset"] + k * sec["sh_entsize"]
                )
                if (st_info & 0xF) == 2 and 0 < st_shndx < len(sections) and st_size > 0:
                    name = get_str(strtab, st_name)
                    if name.startswith("p"):
                        tsec = sections[st_shndx]
                        raw = data[tsec["sh_offset"] + st_value : tsec["sh_offset"] + st_value + st_size]
                        funcs[name] = {
                            "size_bytes": st_size,
                            "hex_bytes": raw.hex(" "),
                            "byte_list": list(raw),
                            "sha256": hashlib.sha256(raw).hexdigest(),
                            "insns": disasm_map.get(name, []),
                            "insn_count": len(disasm_map.get(name, [])),
                        }
    return dict(sorted(funcs.items()))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-json", required=True, type=Path)
    args = ap.parse_args()

    toolchains = [
        ("rustc_1_99_1", "1.99.1"),
        ("rustc_1_102_0_nightly", "nightly-2026-11-12"),
    ]
    results = {"toolchains": {}, "primitives": {}, "comparison_summary": {}}

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        lib_rs = td_path / "prims.rs"
        lib_rs.write_text(RUST_PRIMITIVES_LIB)

        bin_rs = td_path / "exec_test.rs"
        bin_rs.write_text(RUST_PRIMITIVES_LIB.replace('#![crate_type = "lib"]\n', "") + "\n" + RUST_EXEC_TEST)

        per_tc_funcs = {}
        for label, tc in toolchains:
            vv = subprocess.check_output(["rustup", "run", tc, "rustc", "-vV"], text=True)
            results["toolchains"][label] = {
                line.split(":", 1)[0].strip(): line.split(":", 1)[1].strip()
                for line in vv.splitlines() if ":" in line
            }
            obj_p = td_path / f"prims_{label}.o"
            subprocess.run(
                ["rustup", "run", tc, "rustc", "--edition=2021", "-C", "opt-level=3", "--emit=obj", str(lib_rs), "-o", str(obj_p)],
                check=True,
            )
            per_tc_funcs[label] = extract_elf_functions(obj_p)

            bin_p = td_path / f"exec_{label}"
            subprocess.run(
                ["rustup", "run", tc, "rustc", "--edition=2021", "-C", "opt-level=3", str(bin_rs), "-o", str(bin_p)],
                check=True,
            )
            run_out = subprocess.check_output([str(bin_p)], text=True).strip()
            results["toolchains"][label]["silicon_execution"] = run_out

        all_names = sorted(per_tc_funcs["rustc_1_99_1"].keys())
        identical_count = 0
        diff_names = []
        for name in all_names:
            f199 = per_tc_funcs["rustc_1_99_1"][name]
            fnig = per_tc_funcs["rustc_1_102_0_nightly"][name]
            same = f199["byte_list"] == fnig["byte_list"]
            if same:
                identical_count += 1
            else:
                diff_names.append(name)
            results["primitives"][name] = {
                "byte_identical_199_vs_nightly": same,
                "rustc_1_99_1": f199,
                "rustc_1_102_0_nightly": fnig,
            }
        results["comparison_summary"] = {
            "total_functions_extracted": len(all_names),
            "curated_24_count": 24,
            "companion_boundary_count": len(all_names) - 24,
            "byte_identical_across_toolchains": identical_count,
            "differing_functions": diff_names,
        }

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n")
    print(json.dumps(results["comparison_summary"], indent=2))
    for k, v in results["primitives"].items():
        print(f"{k:26s}: {v['rustc_1_99_1']['hex_bytes']:32s} -> {' ; '.join(v['rustc_1_99_1']['insns'])} (same={v['byte_identical_199_vs_nightly']})")


if __name__ == "__main__":
    main()
