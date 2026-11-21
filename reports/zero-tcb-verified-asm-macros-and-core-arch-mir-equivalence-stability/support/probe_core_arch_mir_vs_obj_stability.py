#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Empirical probe of core::arch SIMD MIR stability vs. ELF64 .o machine-code churn:
1. Production SIMD crate census (core::arch vs asm!) & stdarch leaf-primitive Pareto curve.
2. Why default MIR Inline leaves core::arch calls un-inlined (SSE2 libcore vs AVX2 SIMD ABI gate).
3. 5 AVX2 hot loops x 4 rustc versions x 4 compilation/context perturbations:
   exact Runtime(PostCleanup) MIR stability vs ELF64 .o machine-code / regalloc / relocation churn.
All scratch compilations execute inside tempfile.TemporaryDirectory().
"""

from __future__ import annotations

import glob
import hashlib
import json
import os
import re
import struct
import subprocess
import tempfile
from pathlib import Path

TOOLCHAINS = [
    ("1.98.0-nightly", "nightly-2026-06-01"),
    ("1.99.1", "1.99.1"),
    ("1.100.0", "1.100.0"),
    ("1.102.0-nightly", "nightly-2026-11-12"),
]

PRODUCTION_CRATES = [
    "zlib-rs-0.6.8",
    "memchr-2.8.3",
    "simdutf8-0.1.5",
    "crc32fast-1.5.5",
    "simd-adler32-0.3.10",
    "blake3-1.8.7",
    "aho-corasick-1.1.5",
    "bytecount-0.6.9",
    "hashbrown-0.17.1",
    "sha2-0.11.1",
    "chacha20-0.10.2",
    "aes-0.9.4",
]

KERNELS = [
    "adler32_avx2",
    "memchr_avx2",
    "utf8_range_avx2",
    "dot_maddubs_avx2",
    "clmul_fold_avx2",
]

KERNEL_SOURCE = r'''#![crate_type = "lib"]
#![allow(dead_code)]
use core::arch::x86_64::*;

// ---PREFIX_MARKER---

pub fn adler32_ref(data: &[u8]) -> u32 {
    let mut a: u32 = 1;
    let mut b: u32 = 0;
    for &byte in data {
        a = (a + byte as u32) % 65521;
        b = (b + a) % 65521;
    }
    (b << 16) | a
}

#[no_mangle]
#[target_feature(enable = "avx2")]
pub unsafe fn adler32_avx2(data: &[u8]) -> u32 {
    let mut a: u32 = 1;
    let mut b: u32 = 0;
    let weights = _mm256_setr_epi8(
        32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17,
        16, 15, 14, 13, 12, 11, 10,  9,  8,  7,  6,  5,  4,  3,  2,  1,
    );
    let ones = _mm256_set1_epi16(1);
    let zero = _mm256_setzero_si256();
    let mut i = 0usize;
    let len = data.len();
    let ptr = data.as_ptr();
    while i + 32 <= len {
        let chunk = unsafe { _mm256_loadu_si256(ptr.add(i) as *const __m256i) };
        let sad = _mm256_sad_epu8(chunk, zero);
        let weighted_16 = _mm256_maddubs_epi16(chunk, weights);
        let weighted_32 = _mm256_madd_epi16(weighted_16, ones);
        let sad_lo = _mm256_castsi256_si128(sad);
        let sad_hi = _mm256_extracti128_si256::<1>(sad);
        let sum_sad = _mm_add_epi64(sad_lo, sad_hi);
        let block_a = (_mm_cvtsi128_si64(sum_sad) as u32)
            .wrapping_add(_mm_extract_epi64::<1>(sum_sad) as u32);

        let w_lo = _mm256_castsi256_si128(weighted_32);
        let w_hi = _mm256_extracti128_si256::<1>(weighted_32);
        let w_sum2 = _mm_add_epi32(w_lo, w_hi);
        let w_shuf = _mm_shuffle_epi32::<0b01_00_11_10>(w_sum2);
        let w_sum4 = _mm_add_epi32(w_sum2, w_shuf);
        let w_shuf2 = _mm_shuffle_epi32::<0b10_11_00_01>(w_sum4);
        let block_b = _mm_cvtsi128_si32(_mm_add_epi32(w_sum4, w_shuf2)) as u32;

        b = (b.wrapping_add(a.wrapping_mul(32)).wrapping_add(block_b)) % 65521;
        a = (a.wrapping_add(block_a)) % 65521;
        i += 32;
    }
    while i < len {
        a = (a + data[i] as u32) % 65521;
        b = (b + a) % 65521;
        i += 1;
    }
    (b << 16) | a
}

pub fn memchr_ref(needle: u8, hay: &[u8]) -> Option<usize> {
    let mut i = 0;
    while i < hay.len() {
        if hay[i] == needle {
            return Some(i);
        }
        i += 1;
    }
    None
}

#[no_mangle]
#[target_feature(enable = "avx2")]
pub unsafe fn memchr_avx2(needle: u8, hay: &[u8]) -> Option<usize> {
    let vn = _mm256_set1_epi8(needle as i8);
    let len = hay.len();
    let ptr = hay.as_ptr();
    let mut i = 0usize;
    while i + 128 <= len {
        let c0 = unsafe { _mm256_loadu_si256(ptr.add(i) as *const __m256i) };
        let c1 = unsafe { _mm256_loadu_si256(ptr.add(i + 32) as *const __m256i) };
        let c2 = unsafe { _mm256_loadu_si256(ptr.add(i + 64) as *const __m256i) };
        let c3 = unsafe { _mm256_loadu_si256(ptr.add(i + 96) as *const __m256i) };
        let e0 = _mm256_cmpeq_epi8(c0, vn);
        let e1 = _mm256_cmpeq_epi8(c1, vn);
        let e2 = _mm256_cmpeq_epi8(c2, vn);
        let e3 = _mm256_cmpeq_epi8(c3, vn);
        let or01 = _mm256_or_si256(e0, e1);
        let or23 = _mm256_or_si256(e2, e3);
        let any = _mm256_or_si256(or01, or23);
        if _mm256_movemask_epi8(any) != 0 {
            let m0 = _mm256_movemask_epi8(e0) as u32;
            if m0 != 0 { return Some(i + m0.trailing_zeros() as usize); }
            let m1 = _mm256_movemask_epi8(e1) as u32;
            if m1 != 0 { return Some(i + 32 + m1.trailing_zeros() as usize); }
            let m2 = _mm256_movemask_epi8(e2) as u32;
            if m2 != 0 { return Some(i + 64 + m2.trailing_zeros() as usize); }
            let m3 = _mm256_movemask_epi8(e3) as u32;
            return Some(i + 96 + m3.trailing_zeros() as usize);
        }
        i += 128;
    }
    while i + 32 <= len {
        let c = unsafe { _mm256_loadu_si256(ptr.add(i) as *const __m256i) };
        let m = _mm256_movemask_epi8(_mm256_cmpeq_epi8(c, vn)) as u32;
        if m != 0 {
            return Some(i + m.trailing_zeros() as usize);
        }
        i += 32;
    }
    while i < len {
        if hay[i] == needle {
            return Some(i);
        }
        i += 1;
    }
    None
}

pub fn utf8_range_ref(data: &[u8]) -> bool {
    // Rejects forbidden UTF-8 bytes 0xC0, 0xC1, and 0xF5..=0xFF via nibble range check
    let mut i = 0;
    while i < data.len() {
        let b = data[i];
        if b == 0xC0 || b == 0xC1 || b >= 0xF5 {
            return false;
        }
        i += 1;
    }
    true
}

#[no_mangle]
#[target_feature(enable = "avx2")]
pub unsafe fn utf8_range_avx2(data: &[u8]) -> bool {
    // High-nibble / low-nibble VPSHUFB classification:
    // Byte is invalid iff (hi == 0xC && lo <= 1) || (hi == 0xF && lo >= 5)
    // Bit 0: hi == 0xC vs lo <= 1; Bit 1: hi == 0xF vs lo >= 5.
    let hi_tbl = _mm256_setr_epi8(
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2,
    );
    let lo_tbl = _mm256_setr_epi8(
        1, 1, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
        1, 1, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    );
    let mask_0f = _mm256_set1_epi8(0x0F);
    let len = data.len();
    let ptr = data.as_ptr();
    let mut i = 0usize;
    while i + 32 <= len {
        let v = unsafe { _mm256_loadu_si256(ptr.add(i) as *const __m256i) };
        if _mm256_movemask_epi8(v) != 0 {
            let hi_nib = _mm256_and_si256(_mm256_srli_epi16::<4>(v), mask_0f);
            let lo_nib = _mm256_and_si256(v, mask_0f);
            let hi_cls = _mm256_shuffle_epi8(hi_tbl, hi_nib);
            let lo_cls = _mm256_shuffle_epi8(lo_tbl, lo_nib);
            if _mm256_testz_si256(hi_cls, lo_cls) == 0 {
                return false;
            }
        }
        i += 32;
    }
    while i < len {
        let b = data[i];
        if b == 0xC0 || b == 0xC1 || b >= 0xF5 {
            return false;
        }
        i += 1;
    }
    true
}

pub fn dot_maddubs_ref(u: &[u8], s: &[i8]) -> i32 {
    let n = if u.len() < s.len() { u.len() } else { s.len() };
    let mut acc: i32 = 0;
    let mut i = 0usize;
    while i + 2 <= n {
        let p0 = (u[i] as i32) * (s[i] as i32);
        let p1 = (u[i + 1] as i32) * (s[i + 1] as i32);
        let pair = (p0 + p1).clamp(-32768, 32767);
        acc = acc.wrapping_add(pair);
        i += 2;
    }
    if i < n {
        acc = acc.wrapping_add((u[i] as i32) * (s[i] as i32));
    }
    acc
}

#[no_mangle]
#[target_feature(enable = "avx2")]
pub unsafe fn dot_maddubs_avx2(u: &[u8], s: &[i8]) -> i32 {
    let n = if u.len() < s.len() { u.len() } else { s.len() };
    let ones = _mm256_set1_epi16(1);
    let mut vacc = _mm256_setzero_si256();
    let up = u.as_ptr();
    let sp = s.as_ptr();
    let mut i = 0usize;
    while i + 32 <= n {
        let vu = unsafe { _mm256_loadu_si256(up.add(i) as *const __m256i) };
        let vs = unsafe { _mm256_loadu_si256(sp.add(i) as *const __m256i) };
        let prod16 = _mm256_maddubs_epi16(vu, vs);
        let prod32 = _mm256_madd_epi16(prod16, ones);
        vacc = _mm256_add_epi32(vacc, prod32);
        i += 32;
    }
    let lo = _mm256_castsi256_si128(vacc);
    let hi = _mm256_extracti128_si256::<1>(vacc);
    let sum128 = _mm_add_epi32(lo, hi);
    let sh1 = _mm_shuffle_epi32::<0b01_00_11_10>(sum128);
    let sum64 = _mm_add_epi32(sum128, sh1);
    let sh2 = _mm_shuffle_epi32::<0b10_11_00_01>(sum64);
    let mut acc = _mm_cvtsi128_si32(_mm_add_epi32(sum64, sh2));
    while i + 2 <= n {
        let p0 = (u[i] as i32) * (s[i] as i32);
        let p1 = (u[i + 1] as i32) * (s[i + 1] as i32);
        acc = acc.wrapping_add((p0 + p1).clamp(-32768, 32767));
        i += 2;
    }
    if i < n {
        acc = acc.wrapping_add((u[i] as i32) * (s[i] as i32));
    }
    acc
}

fn clmul64_soft(a: u64, b: u64) -> u128 {
    let mut acc: u128 = 0;
    let mut k = 0;
    while k < 64 {
        if ((b >> k) & 1) != 0 {
            acc ^= (a as u128) << k;
        }
        k += 1;
    }
    acc
}

pub fn clmul_fold_ref(blocks: &[[u8; 16]], k_lo: u64, k_hi: u64) -> (u64, u64) {
    if blocks.is_empty() {
        return (0, 0);
    }
    let mut acc_lo = u64::from_le_bytes(blocks[0][0..8].try_into().unwrap());
    let mut acc_hi = u64::from_le_bytes(blocks[0][8..16].try_into().unwrap());
    let mut i = 1usize;
    while i < blocks.len() {
        let m_lo = u64::from_le_bytes(blocks[i][0..8].try_into().unwrap());
        let m_hi = u64::from_le_bytes(blocks[i][8..16].try_into().unwrap());
        let p0 = clmul64_soft(acc_lo, k_lo);
        let p1 = clmul64_soft(acc_hi, k_hi);
        let folded = p0 ^ p1 ^ ((m_hi as u128) << 64 | (m_lo as u128));
        acc_lo = folded as u64;
        acc_hi = (folded >> 64) as u64;
        i += 1;
    }
    (acc_lo, acc_hi)
}

#[no_mangle]
#[target_feature(enable = "avx2,pclmulqdq")]
pub unsafe fn clmul_fold_avx2(blocks: &[[u8; 16]], k_lo: u64, k_hi: u64) -> (u64, u64) {
    if blocks.is_empty() {
        return (0, 0);
    }
    let key = _mm_set_epi64x(k_hi as i64, k_lo as i64);
    let mut acc = unsafe { _mm_loadu_si128(blocks.as_ptr() as *const __m128i) };
    let mut i = 1usize;
    while i < blocks.len() {
        let msg = unsafe { _mm_loadu_si128(blocks.as_ptr().add(i) as *const __m128i) };
        let p0 = _mm_clmulepi64_si128::<0x00>(acc, key);
        let p1 = _mm_clmulepi64_si128::<0x11>(acc, key);
        acc = _mm_xor_si128(_mm_xor_si128(p0, p1), msg);
        i += 1;
    }
    (_mm_cvtsi128_si64(acc) as u64, _mm_extract_epi64::<1>(acc) as u64)
}

// ---SUFFIX_MARKER---
'''

CALLER_PERTURBATION_PREFIX = r'''
// Sibling function + line-shift + caller pressure perturbation
#[no_mangle]
pub fn unrelated_sibling_perturb(xs: &[u64], seed: u64) -> u64 {
    let mut h = seed;
    for &x in xs {
        h = h.rotate_left(13).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ x;
    }
    h
}
'''

CALLER_PERTURBATION_SUFFIX = r'''
#[no_mangle]
#[target_feature(enable = "avx2,pclmulqdq")]
pub unsafe fn hot_caller_pipeline(buf: &[u8], sbuf: &[i8], blocks: &[[u8; 16]]) -> u64 {
    let a = unsafe { adler32_avx2(buf) } as u64;
    let m = unsafe { memchr_avx2(0x7F, buf) }.unwrap_or(999) as u64;
    let u = unsafe { utf8_range_avx2(buf) } as u64;
    let d = unsafe { dot_maddubs_avx2(buf, sbuf) } as i64 as u64;
    let (c0, c1) = unsafe { clmul_fold_avx2(blocks, 0x1EDC6F41, 0x82F63B78) };
    a.wrapping_add(m).wrapping_add(u).wrapping_add(d) ^ c0 ^ c1
}
'''


def canonicalize_mir(mir_text: str) -> str:
    """Strip source-location comments and debug/scope line numbers while preserving
    exact MIR types, locals, basic blocks, statements, rvalues, and terminators.
    """
    out = []
    for raw in mir_text.splitlines():
        line = re.sub(r"//.*$", "", raw).rstrip()
        if not line.strip():
            continue
        # Normalize scope debug coordinates (`scope 1 at /tmp/...:12:3: 15:4`)
        if re.match(r"^\s*scope\s+\d+\s+", line):
            line = re.sub(r"\s+at\s+.*\{", " {", line)
        out.append(line)
    return "\n".join(out)


def parse_elf64_symbols_and_relocs(obj_path: Path) -> dict[str, dict]:
    """Parse ELF64 relocatable .o symbol bytes and relocation counts directly."""
    data = obj_path.read_bytes()
    assert data[:4] == b"\x7fELF" and data[4] == 2 and data[5] == 1
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)

    sections = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        (
            sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size,
            sh_link, sh_info, sh_addralign, sh_entsize
        ) = struct.unpack_from("<IIQQQQIIQQ", data, off)
        sections.append({
            "idx": i, "sh_name": sh_name, "sh_type": sh_type, "sh_flags": sh_flags,
            "sh_offset": sh_offset, "sh_size": sh_size, "sh_link": sh_link,
            "sh_info": sh_info, "sh_entsize": sh_entsize,
        })

    def get_str(strtab_sec, str_off):
        base = strtab_sec["sh_offset"] + str_off
        end = data.index(b"\x00", base)
        return data[base:end].decode("utf-8", errors="replace")

    # Count relocations per target section index (`sh_info` in SHT_RELA == 4)
    sec_relocs: dict[int, list[tuple[int, int]]] = {}
    for sec in sections:
        if sec["sh_type"] == 4 and sec["sh_entsize"] == 24:  # SHT_RELA
            target_shndx = sec["sh_info"]
            cnt = sec["sh_size"] // 24
            rels = []
            for k in range(cnt):
                r_offset, r_info, _r_addend = struct.unpack_from(
                    "<QQq", data, sec["sh_offset"] + k * 24
                )
                rels.append((r_offset, r_info & 0xFFFFFFFF))
            sec_relocs[target_shndx] = rels

    result = {}
    for sec in sections:
        if sec["sh_type"] == 2:  # SHT_SYMTAB
            strtab = sections[sec["sh_link"]]
            nsyms = sec["sh_size"] // sec["sh_entsize"]
            for k in range(nsyms):
                st_name, st_info, _st_other, st_shndx, st_value, st_size = struct.unpack_from(
                    "<IBBHQQ", data, sec["sh_offset"] + k * sec["sh_entsize"]
                )
                st_type = st_info & 0xF
                if st_type == 2 and 0 < st_shndx < len(sections) and st_size > 0:  # STT_FUNC
                    name = get_str(strtab, st_name)
                    tsec = sections[st_shndx]
                    start = tsec["sh_offset"] + st_value
                    raw_bytes = data[start : start + st_size]
                    rels = [
                        (ro - st_value, rt)
                        for (ro, rt) in sec_relocs.get(st_shndx, [])
                        if st_value <= ro < st_value + st_size
                    ]
                    result[name] = {
                        "size_bytes": st_size,
                        "sha256": hashlib.sha256(raw_bytes).hexdigest(),
                        "reloc_count": len(rels),
                        "shndx": st_shndx,
                    }
    return result


def parse_objdump_functions(obj_path: Path) -> dict[str, dict]:
    out = subprocess.check_output(
        ["objdump", "-d", "-M", "intel", str(obj_path)], text=True
    )
    funcs = {}
    cur_name = None
    insns = []
    for line in out.splitlines():
        m_hdr = re.match(r"^[0-9a-fA-F]+\s+<([^>]+)>:$", line.strip())
        if m_hdr:
            if cur_name is not None:
                funcs[cur_name] = summarize_disasm(insns)
            cur_name = m_hdr.group(1)
            insns = []
        elif cur_name is not None:
            m_ins = re.match(r"^\s*[0-9a-fA-F]+:\s+(?:[0-9a-fA-F]{2}\s+)+\s*(.+)$", line)
            if m_ins:
                insns.append(m_ins.group(1).strip())
    if cur_name is not None:
        funcs[cur_name] = summarize_disasm(insns)
    return funcs


def summarize_disasm(insns: list[str]) -> dict:
    mnemonics = [i.split()[0] for i in insns if i]
    ymms = sorted(set(re.findall(r"\bymm(?:1[0-5]|[0-9])\b", "\n".join(insns))))
    xmms = sorted(set(re.findall(r"\bxmm(?:1[0-5]|[0-9])\b", "\n".join(insns))))
    gprs = sorted(set(re.findall(
        r"\b(?:rax|rbx|rcx|rdx|rsi|rdi|rbp|rsp|r8|r9|r10|r11|r12|r13|r14|r15|"
        r"eax|ebx|ecx|edx|esi|edi|ebp|esp|r8d|r9d|r10d|r11d|r12d|r13d|r14d|r15d)\b",
        "\n".join(insns),
    )))
    reg_seq = re.findall(
        r"\b(?:ymm(?:1[0-5]|[0-9])|xmm(?:1[0-5]|[0-9])|"
        r"rax|rbx|rcx|rdx|rsi|rdi|rbp|r8|r9|r10|r11|r12|r13|r14|r15|"
        r"eax|ebx|ecx|edx|esi|edi|ebp|r8d|r9d|r10d|r11d|r12d|r13d|r14d|r15d)\b",
        "\n".join(insns),
    )
    rsp_mem = sum(1 for i in insns if "[rsp" in i)
    rip_mem = sum(1 for i in insns if "[rip" in i)
    return {
        "insn_count": len(insns),
        "mnemonic_seq_sha256": hashlib.sha256(" ".join(mnemonics).encode()).hexdigest()[:16],
        "reg_seq_sha256": hashlib.sha256(" ".join(reg_seq).encode()).hexdigest()[:16],
        "ymm_regs": ymms,
        "xmm_regs": xmms,
        "gpr_count": len(gprs),
        "rsp_mem_refs": rsp_mem,
        "rip_const_refs": rip_mem,
    }


def run_differential_sanity_check() -> dict:
    """Compile and execute all 5 AVX2 kernels against their scalar Rust reference twins."""
    test_harness = KERNEL_SOURCE.replace("#![crate_type = \"lib\"]", "") + r'''
fn main() {
    let mut data = vec![0u8; 307];
    let mut sdata = vec![0i8; 307];
    for i in 0..data.len() {
        data[i] = ((i * 73 + 19) & 0xFF) as u8;
        sdata[i] = (((i * 37 + 5) & 0x7F) as i8).wrapping_sub(60);
    }
    for len in [0usize, 1, 2, 15, 16, 31, 32, 33, 63, 64, 127, 128, 129, 256, 307] {
        let sub_u = &data[..len];
        let sub_s = &sdata[..len];
        assert_eq!(adler32_ref(sub_u), unsafe { adler32_avx2(sub_u) }, "adler32 len={len}");
        assert_eq!(dot_maddubs_ref(sub_u, sub_s), unsafe { dot_maddubs_avx2(sub_u, sub_s) }, "dot len={len}");
        assert_eq!(utf8_range_ref(sub_u), unsafe { utf8_range_avx2(sub_u) }, "utf8 len={len}");
        for needle in [0u8, 19, 127, 200, 255] {
            assert_eq!(memchr_ref(needle, sub_u), unsafe { memchr_avx2(needle, sub_u) }, "memchr len={len}");
        }
    }
    let mut ascii_valid = vec![b'a'; 195];
    assert!(utf8_range_ref(&ascii_valid) && unsafe { utf8_range_avx2(&ascii_valid) });
    for pos in [0usize, 15, 31, 32, 64, 194] {
        for bad in [0xC0u8, 0xC1, 0xF5, 0xFF] {
            ascii_valid[pos] = bad;
            assert_eq!(utf8_range_ref(&ascii_valid), unsafe { utf8_range_avx2(&ascii_valid) });
            assert!(!unsafe { utf8_range_avx2(&ascii_valid) });
            ascii_valid[pos] = b'a';
        }
    }
    let blocks: Vec<[u8; 16]> = (0..9)
        .map(|k| core::array::from_fn(|j| ((k * 29 + j * 11 + 3) & 0xFF) as u8))
        .collect();
    for n in 0..=9 {
        assert_eq!(
            clmul_fold_ref(&blocks[..n], 0x1EDC_6F41_1111_2222, 0x82F6_3B78_3333_4444),
            unsafe { clmul_fold_avx2(&blocks[..n], 0x1EDC_6F41_1111_2222, 0x82F6_3B78_3333_4444) },
            "clmul n={n}"
        );
    }
    println!("DIFF_OK checks=all");
}
'''
    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "diff_test.rs"
        bin_p = Path(td) / "diff_test"
        src.write_text(test_harness)
        subprocess.check_call([
            "rustup", "run", "1.99.1", "rustc", "--edition=2021",
            "-C", "opt-level=3", str(src), "-o", str(bin_p)
        ])
        out = subprocess.check_output([str(bin_p)], text=True).strip()
        return {"status": out}


def analyze_stdarch_and_crate_pareto() -> dict:
    sysroot = subprocess.check_output(
        ["rustup", "run", "1.99.1", "rustc", "--print", "sysroot"], text=True
    ).strip()
    stdarch_root = Path(sysroot) / "lib/rustlib/src/rust/library/stdarch/crates/core_arch/src"
    llvm_links = {}
    fn_bodies = {}
    for dirpath, _, files in os.walk(stdarch_root):
        if "/x86" not in dirpath:
            continue
        for f in files:
            if not f.endswith(".rs"):
                continue
            txt = (Path(dirpath) / f).read_text()
            for m in re.finditer(
                r'#\[link_name\s*=\s*"(llvm\.[^"]+)"\](?:\s*#\[[^\]]*\])*\s*(?:pub\s+)?(?:unsafe\s+)?fn\s+([a-zA-Z0-9_]+)',
                txt,
            ):
                llvm_links[m.group(2)] = m.group(1)
            lines = txt.splitlines()
            i = 0
            while i < len(lines):
                m = re.search(r"pub\s+(?:const\s+)?(?:unsafe\s+)?fn\s+(_mm[a-zA-Z0-9_]*)\b", lines[i])
                if m:
                    name = m.group(1)
                    brace, started, j, bl = 0, False, i, []
                    while j < len(lines):
                        bl.append(lines[j])
                        for ch in lines[j]:
                            if ch == "{":
                                brace += 1
                                started = True
                            elif ch == "}":
                                brace -= 1
                        j += 1
                        if started and brace <= 0:
                            break
                    fn_bodies[name] = "\n".join(bl)
                    i = j
                else:
                    i += 1

    def classify(name: str, seen: set[str] | None = None):
        if seen is None:
            seen = set()
        if name in seen or name not in fn_bodies:
            return set(), set()
        seen.add(name)
        body = re.sub(r"//.*", "", fn_bodies[name])
        body = body[body.index("{") :] if "{" in body else body
        s_ops = set(re.findall(r"\b(simd_[a-z0-9_]+)\b", body))
        l_ops = set()
        for tok in re.findall(r"\b([a-zA-Z_][a-zA-Z0-9_]*)\s*(?:::<[^>]*>)?\s*\(", body):
            if tok in llvm_links:
                l_ops.add(llvm_links[tok])
            elif tok.startswith("_mm") and tok != name:
                s2, l2 = classify(tok, seen)
                s_ops |= s2
                l_ops |= l2
        return s_ops, l_ops

    crate_rows = []
    total_calls: dict[str, int] = {}
    cargo_reg = Path.home() / ".cargo" / "registry" / "src"
    for c in PRODUCTION_CRATES:
        matches = glob.glob(str(cargo_reg / "*" / c))
        if not matches:
            continue
        p = Path(matches[0])
        vcs = p / ".cargo_vcs_info.json"
        sha = json.loads(vcs.read_text())["git"]["sha1"] if vcs.exists() else "unknown"
        local_defs = set()
        rs_files = [Path(r) / f for r, _, fs in os.walk(p) for f in fs if f.endswith(".rs")]
        for rf in rs_files:
            txt_nc = re.sub(r"//.*", "", rf.read_text(errors="ignore"))
            for d in re.findall(r"\bfn\s+(_mm(?:256|512)?_[a-z0-9_]+)\b", txt_nc):
                local_defs.add(d)
        x86_cnt = 0
        x86_uniq = set()
        asm_x86 = 0
        asm_other = 0
        for rf in rs_files:
            txt_nc = re.sub(r"//.*", "", rf.read_text(errors="ignore"))
            n_asm = len(re.findall(r"\b(?:asm|naked_asm|global_asm)!", txt_nc))
            rel = str(rf.relative_to(p))
            if n_asm:
                if "x86" in rel:
                    asm_x86 += n_asm
                else:
                    asm_other += n_asm
            for m in re.findall(r"\b(_mm(?:256|512)?_[a-z0-9_]+)\s*(?:::<[^>]*>)?\s*\(", txt_nc):
                if m in local_defs:
                    continue
                x86_cnt += 1
                x86_uniq.add(m)
                total_calls[m] = total_calls.get(m, 0) + 1
        crate_rows.append({
            "crate": c,
            "git_sha1": sha,
            "x86_stdarch_call_sites": x86_cnt,
            "x86_unique_intrinsics": len(x86_uniq),
            "x86_asm_sites": asm_x86,
            "non_x86_asm_sites": asm_other,
        })

    # Group llvm.x86.* into width-independent semantic families (e.g., pclmulqdq, pshufb, psadbw, pmaddwd, pmaddubsw)
    def canonical_llvm_family(op: str) -> str:
        if "pclmulqdq" in op:
            return "llvm_family:pclmulqdq"
        if "pshuf.b" in op:
            return "llvm_family:pshufb"
        if "psad.bw" in op:
            return "llvm_family:psadbw"
        if "pmadd.wd" in op or "pmaddw.d" in op:
            return "llvm_family:pmaddwd"
        if "pmadd.ub.sw" in op or "pmaddubs.w" in op:
            return "llvm_family:pmaddubsw"
        if "aes" in op:
            return "llvm_family:aesni"
        if "pternlog" in op:
            return "llvm_family:pternlog"
        if "vpermi2var" in op or "perm2" in op or "permd" in op or "permq" in op:
            return "llvm_family:vperm"
        if "vpdpbusd" in op:
            return "llvm_family:vpdpbusd"
        if "ptest" in op:
            return "llvm_family:ptest"
        return f"llvm_family:{op}"

    total_sites = sum(total_calls.values())
    pure_mir_sites = 0
    portable_simd_sites = 0
    llvm_leaf_sites = 0
    simd_used_all = set()
    family_counts: dict[str, int] = {}
    for fn_name, cnt in total_calls.items():
        s_ops, l_ops = classify(fn_name)
        simd_used_all |= s_ops
        if not l_ops and not s_ops:
            pure_mir_sites += cnt
            family_counts["pure_mir_transmute_mem"] = family_counts.get("pure_mir_transmute_mem", 0) + cnt
        elif not l_ops:
            portable_simd_sites += cnt
            key = "portable_simd:" + "+".join(sorted(s_ops))
            family_counts[key] = family_counts.get(key, 0) + cnt
        else:
            llvm_leaf_sites += cnt
            fams = "+".join(sorted({canonical_llvm_family(x) for x in l_ops}))
            family_counts[fams] = family_counts.get(fams, 0) + cnt

    ranked_llvm = sorted(
        [(k, v) for k, v in family_counts.items() if k.startswith("llvm_family:")],
        key=lambda x: -x[1],
    )
    return {
        "stdarch_199_x86_fn_count": len(fn_bodies),
        "stdarch_199_x86_llvm_link_count": len(llvm_links),
        "crates_scanned": crate_rows,
        "total_x86_stdarch_sites": total_sites,
        "unique_x86_stdarch_fns_used": len(total_calls),
        "pure_mir_sites": pure_mir_sites,
        "portable_simd_sites": portable_simd_sites,
        "zero_llvm_intrinsic_sites": pure_mir_sites + portable_simd_sites,
        "zero_llvm_intrinsic_pct": round(100.0 * (pure_mir_sites + portable_simd_sites) / max(1, total_sites), 2),
        "unique_portable_simd_ops_used": sorted(simd_used_all),
        "llvm_leaf_sites": llvm_leaf_sites,
        "ranked_llvm_families": ranked_llvm,
    }


def run_stability_matrix() -> dict:
    configs = [
        ("opt2", ["-C", "opt-level=2"], False),
        ("opt3", ["-C", "opt-level=3"], False),
        ("opt3_x86_64_v3", ["-C", "opt-level=3", "-C", "target-cpu=x86-64-v3"], False),
        ("opt3_caller_perturb", ["-C", "opt-level=3", "-C", "codegen-units=1"], True),
    ]
    matrix = []
    tc_versions = {}

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        for tc_label, tc_rustup in TOOLCHAINS:
            vv = subprocess.check_output(
                ["rustup", "run", tc_rustup, "rustc", "-vV"], text=True
            )
            tc_versions[tc_label] = {
                line.split(":", 1)[0].strip(): line.split(":", 1)[1].strip()
                for line in vv.splitlines()
                if ":" in line
            }
            for cfg_label, flags, with_perturb in configs:
                src_text = KERNEL_SOURCE
                if with_perturb:
                    src_text = src_text.replace("// ---PREFIX_MARKER---", CALLER_PERTURBATION_PREFIX)
                    src_text = src_text.replace("// ---SUFFIX_MARKER---", CALLER_PERTURBATION_SUFFIX)
                src_file = td_path / f"k_{tc_label}_{cfg_label}.rs"
                obj_file = td_path / f"k_{tc_label}_{cfg_label}.o"
                mir_dir = td_path / f"mir_{tc_label}_{cfg_label}"
                mir_inl_dir = td_path / f"mir_inl_{tc_label}_{cfg_label}"
                mir_dir.mkdir()
                mir_inl_dir.mkdir()
                src_file.write_text(src_text)

                env = os.environ.copy()
                env["RUSTC_BOOTSTRAP"] = "1"

                # 1. Compile .o + dump Runtime(PostCleanup) MIR
                subprocess.check_call([
                    "rustup", "run", tc_rustup, "rustc", "--edition=2021",
                    "--crate-name", "simd_kernels",
                    *flags,
                    "-Z", "function-sections=yes",
                    "-Z", "dump-mir=avx2",
                    f"-Zdump-mir-dir={mir_dir}",
                    "--emit=obj",
                    str(src_file),
                    "-o", str(obj_file),
                ], env=env)

                # 2. Also dump unfolded stdarch MIR (`-Z inline-mir-hint-threshold=2000`)
                subprocess.check_call([
                    "rustup", "run", tc_rustup, "rustc", "--edition=2021",
                    "--crate-name", "simd_kernels",
                    *flags,
                    "-Z", "inline-mir-hint-threshold=2000",
                    "-Z", "inline-mir-threshold=2000",
                    "-Z", "dump-mir=avx2",
                    f"-Zdump-mir-dir={mir_inl_dir}",
                    "--emit=llvm-ir",
                    str(src_file),
                    "-o", str(td_path / "dummy.ll"),
                ], env=env)

                elf_syms = parse_elf64_symbols_and_relocs(obj_file)
                dis_syms = parse_objdump_functions(obj_file)

                for kname in KERNELS:
                    pc_files = [
                        p for p in mir_dir.iterdir()
                        if f".{kname}." in p.name and p.name.endswith("runtime-post-cleanup.after.mir")
                    ]
                    assert len(pc_files) == 1, f"missing postcleanup MIR for {kname}: {pc_files}"
                    pc_canon = canonicalize_mir(pc_files[0].read_text())
                    pc_hash = hashlib.sha256(pc_canon.encode()).hexdigest()[:16]

                    inl_files = [
                        p for p in mir_inl_dir.iterdir()
                        if f".{kname}." in p.name and p.name.endswith("Inline.after.mir")
                    ]
                    if not inl_files:
                        inl_files = [
                            p for p in mir_inl_dir.iterdir()
                            if f".{kname}." in p.name and p.name.endswith("runtime-optimized.after.mir")
                        ]
                    inl_canon = canonicalize_mir(inl_files[0].read_text())
                    inl_hash = hashlib.sha256(inl_canon.encode()).hexdigest()[:16]

                    es = elf_syms[kname]
                    ds = dis_syms[kname]
                    matrix.append({
                        "kernel": kname,
                        "toolchain": tc_label,
                        "config": cfg_label,
                        "postcleanup_mir_hash": pc_hash,
                        "unfolded_stdarch_mir_hash": inl_hash,
                        "obj_sha256_16": es["sha256"][:16],
                        "obj_size_bytes": es["size_bytes"],
                        "obj_reloc_count": es["reloc_count"],
                        **ds,
                    })

    # Aggregate stability summary per kernel across all 16 (4 toolchains x 4 configs) runs
    summary_by_kernel = {}
    for kname in KERNELS:
        rows = [r for r in matrix if r["kernel"] == kname]
        # Within-toolchain flag/caller perturbations:
        within_tc_mir_drifts = 0
        within_tc_obj_drifts = 0
        for tc_label, _ in TOOLCHAINS:
            tc_rows = [r for r in rows if r["toolchain"] == tc_label]
            if len({r["postcleanup_mir_hash"] for r in tc_rows}) > 1:
                within_tc_mir_drifts += 1
            if len({r["obj_sha256_16"] for r in tc_rows}) > 1:
                within_tc_obj_drifts += 1
        summary_by_kernel[kname] = {
            "total_cells": len(rows),
            "distinct_postcleanup_mir_hashes": len({r["postcleanup_mir_hash"] for r in rows}),
            "distinct_unfolded_stdarch_mir_hashes": len({r["unfolded_stdarch_mir_hash"] for r in rows}),
            "distinct_obj_byte_hashes": len({r["obj_sha256_16"] for r in rows}),
            "distinct_mnemonic_schedules": len({r["mnemonic_seq_sha256"] for r in rows}),
            "distinct_regalloc_sequences": len({r["reg_seq_sha256"] for r in rows}),
            "insn_count_min_max": [min(r["insn_count"] for r in rows), max(r["insn_count"] for r in rows)],
            "obj_bytes_min_max": [min(r["obj_size_bytes"] for r in rows), max(r["obj_size_bytes"] for r in rows)],
            "rsp_refs_min_max": [min(r["rsp_mem_refs"] for r in rows), max(r["rsp_mem_refs"] for r in rows)],
            "reloc_count_min_max": [min(r["obj_reloc_count"] for r in rows), max(r["obj_reloc_count"] for r in rows)],
            "within_toolchain_mir_drift_count": within_tc_mir_drifts,
            "within_toolchain_obj_drift_count": within_tc_obj_drifts,
        }

    return {
        "toolchains": tc_versions,
        "summary_by_kernel": summary_by_kernel,
        "matrix": matrix,
    }


def main() -> None:
    diff_res = run_differential_sanity_check()
    pareto_res = analyze_stdarch_and_crate_pareto()
    stab_res = run_stability_matrix()
    combined = {
        "differential_sanity": diff_res,
        "stdarch_and_crate_pareto": pareto_res,
        "mir_vs_obj_stability": stab_res,
    }
    out_path = Path(__file__).with_name("probe_core_arch_mir_vs_obj_stability_results.json")
    out_path.write_text(json.dumps(combined, indent=2, sort_keys=True) + "\n")
    print(f"Differential check: {diff_res['status']}")
    print(
        f"Crates x86 stdarch sites={pareto_res['total_x86_stdarch_sites']}, "
        f"zero-llvm={pareto_res['zero_llvm_intrinsic_sites']} ({pareto_res['zero_llvm_intrinsic_pct']}%)"
    )
    for k, s in stab_res["summary_by_kernel"].items():
        print(
            f"  {k:18s}: MIR_hashes={s['distinct_postcleanup_mir_hashes']:2d}/16 "
            f"(unfolded={s['distinct_unfolded_stdarch_mir_hashes']:2d}/16) | "
            f".o_hashes={s['distinct_obj_byte_hashes']:2d}/16 "
            f"(regalloc={s['distinct_regalloc_sequences']:2d}/16, "
            f"insns={s['insn_count_min_max']}, bytes={s['obj_bytes_min_max']})"
        )


if __name__ == "__main__":
    main()
