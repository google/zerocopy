#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""16-seed symbol, loop-header, JCC-boundary, and .eh_frame_hdr address-modulo analyzer for rustc 1.99.1."""

import argparse
import json
import math
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = str(TC_ROOT / "bin" / "rustc")
LLVM_BIN = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
LLVM_OBJDUMP = str(LLVM_BIN / "llvm-objdump")
LLVM_NM = str(LLVM_BIN / "llvm-nm")
LLVM_READELF = "readelf"

# Representative hot loops matching the W-Core benchmark suite (Q6)
WORKLOAD_SOURCES = {
    "bench-serde-json": r"""
#[inline(never)]
pub fn scan_json_tokens(input: &[u8]) -> u64 {
    let mut acc = 0u64;
    let mut in_str = false;
    let mut esc = false;
    let mut depth = 0u64;
    let mut i = 0usize;
    while i < input.len() {
        let b = input[i];
        if in_str {
            if esc {
                esc = false;
            } else if b == b'\\' {
                esc = true;
            } else if b == b'"' {
                in_str = false;
                acc = acc.wrapping_add(depth.wrapping_mul(31));
            } else {
                acc = acc.wrapping_mul(131).wrapping_add(b as u64);
            }
        } else {
            match b {
                b'"' => in_str = true,
                b'{' | b'[' => depth = depth.wrapping_add(1),
                b'}' | b']' => depth = depth.wrapping_sub(1),
                b':' | b',' => acc = acc.rotate_left(7) ^ depth,
                b'0'..=b'9' => acc = acc.wrapping_mul(10).wrapping_add((b - b'0') as u64),
                _ => {}
            }
        }
        i += 1;
    }
    acc ^ depth
}

fn main() {
    let payload = br#"{"id":12345,"name":"alpha_beta_gamma","values":[10,20,30,40,50],"nested":{"ok":true,"msg":"escaped \"quote\" here"}}"#;
    let mut buf = Vec::with_capacity(payload.len() * 64);
    for _ in 0..64 {
        buf.extend_from_slice(payload);
    }
    let mut total = 0u64;
    for _ in 0..100 {
        total = total.wrapping_add(std::hint::black_box(scan_json_tokens(std::hint::black_box(&buf))));
    }
    if total == 0 { println!("0"); }
}
""",
    "bench-regex-automata": r"""
#[inline(never)]
pub fn dfa_step_search(trans: &[u32; 1024], hay: &[u8]) -> u32 {
    let mut state = 0u32;
    let mut matches = 0u32;
    let mut i = 0usize;
    while i < hay.len() {
        let b = hay[i] as usize;
        let idx = ((state as usize) & 3) * 256 + b;
        state = unsafe { *trans.get_unchecked(idx) };
        if (state & 4) != 0 {
            matches = matches.wrapping_add(1);
            state &= 3;
        }
        i += 1;
    }
    matches ^ state
}

fn main() {
    let mut trans = [0u32; 1024];
    for s in 0..4 {
        for b in 0..256 {
            trans[s * 256 + b] = ((s + b + 1) & 3) as u32 | if b == b'a' as usize && s == 2 { 4 } else { 0 };
        }
    }
    let hay = [b'a'; 256];
    let mut sum = 0u32;
    for _ in 0..1000 {
        sum = sum.wrapping_add(std::hint::black_box(dfa_step_search(std::hint::black_box(&trans), std::hint::black_box(&hay))));
    }
    if sum == 0 { println!("0"); }
}
""",
    "bench-unwind-drop-ladder": r"""
struct DropGuard<'a>(&'a mut u64, u64);
impl<'a> Drop for DropGuard<'a> {
    #[inline(never)]
    fn drop(&mut self) {
        *self.0 = self.0.rotate_left(5).wrapping_add(self.1);
    }
}

#[inline(never)]
pub fn recurse_and_unwind(depth: usize, sink: &mut u64) {
    let mut local = *sink ^ (depth as u64);
    if depth == 0 {
        panic!("leaf unwind");
    }
    recurse_and_unwind(depth - 1, &mut local);
    let _g = DropGuard(sink, local.wrapping_add(depth as u64 + 1));
}

fn main() {
    let mut acc = 1u64;
    for _ in 0..20 {
        let mut s = acc;
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            recurse_and_unwind(16, &mut s);
        }));
        acc = acc.wrapping_add(s);
    }
    if acc == 0 { println!("0"); }
}
""",
    "bench-concurrency-sync": r"""
use std::sync::atomic::{AtomicU64, Ordering};

#[inline(never)]
pub fn cas_ring_step(cell: &AtomicU64, rounds: usize) -> u64 {
    let mut cur = cell.load(Ordering::Relaxed);
    for i in 0..rounds {
        let next = cur.wrapping_mul(6364136223846793005).wrapping_add(i as u64 | 1);
        match cell.compare_exchange_weak(cur, next, Ordering::AcqRel, Ordering::Relaxed) {
            Ok(_) => cur = next,
            Err(actual) => cur = actual,
        }
    }
    cur
}

fn main() {
    let cell = AtomicU64::new(7);
    let v = std::hint::black_box(cas_ring_step(&cell, 2000));
    if v == 0 { println!("0"); }
}
""",
    "bench-compression-image": r"""
#[inline(never)]
pub fn lz77_window_kernel(src: &[u8]) -> u64 {
    let mut ht = [0u16; 256];
    let mut hash_acc = 0u64;
    let mut i = 0usize;
    while i + 4 <= src.len() {
        let w = u32::from_le_bytes([src[i], src[i + 1], src[i + 2], src[i + 3]]);
        let h = ((w.wrapping_mul(0x1e35a7bd)) >> 24) as usize;
        let prev = ht[h] as usize;
        ht[h] = i as u16;
        if prev < i && i - prev < 128 && src[prev] == src[i] {
            hash_acc = hash_acc.wrapping_add((i - prev) as u64);
        } else {
            hash_acc = hash_acc.rotate_left(3) ^ (w as u64);
        }
        i += 1;
    }
    hash_acc
}

fn main() {
    let data = [0x5au8; 4096];
    let v = std::hint::black_box(lz77_window_kernel(std::hint::black_box(&data)));
    if v == 0 { println!("0"); }
}
""",
}

HOT_SYMBOLS = {
    "bench-serde-json": "scan_json_tokens",
    "bench-regex-automata": "dfa_step_search",
    "bench-unwind-drop-ladder": "recurse_and_unwind",
    "bench-concurrency-sync": "cas_ring_step",
    "bench-compression-image": "lz77_window_kernel",
}

Q6_SEED_MEDIANS_SERDE_US = {
    1: 21.017, 2: 17.803, 3: 17.814, 4: 17.857,
    5: 17.757, 6: 20.974, 7: 17.923, 8: 18.940,
    9: 18.326, 10: 18.773, 11: 20.951, 12: 18.357,
    13: 17.525, 14: 21.120, 15: 17.892, 16: 18.015,
}

JCC_MNEMONICS = {
    "je", "jne", "jz", "jnz", "ja", "jae", "jb", "jbe",
    "jg", "jge", "jl", "jle", "js", "jns", "jo", "jno", "jp", "jnp", "jmp",
}
FUSIBLE_CMP_TEST = {"cmp", "cmpb", "cmpw", "cmpl", "cmpq", "test", "testb", "testw", "testl", "testq"}


def parse_function_disassembly(elf_path: Path, target_sub: str) -> dict:
    proc = subprocess.run(
        [LLVM_OBJDUMP, "-d", str(elf_path)],
        capture_output=True, text=True, check=True,
    )
    in_fn = False
    fn_name = ""
    fn_va = 0
    insns = []
    for line in proc.stdout.splitlines():
        m_hdr = re.match(r"^([0-9a-fA-F]+)\s+<([^>]+)>:$", line.strip())
        if m_hdr:
            if in_fn and insns:
                break
            va = int(m_hdr.group(1), 16)
            name = m_hdr.group(2)
            if target_sub in name:
                in_fn = True
                fn_name = name
                fn_va = va
            continue
        if in_fn:
            m_ins = re.match(r"^\s*([0-9a-fA-F]+):\s+((?:[0-9a-fA-F]{2}\s+)+)\s*([a-zA-Z0-9_.]+)(.*)$", line)
            if m_ins:
                iva = int(m_ins.group(1), 16)
                raw_bytes = m_ins.group(2).strip().split()
                mnem = m_ins.group(3).lower()
                ops = m_ins.group(4).strip()
                insns.append({
                    "va": iva,
                    "len": len(raw_bytes),
                    "end_va": iva + len(raw_bytes),
                    "mnem": mnem,
                    "ops": ops,
                })
    if not insns:
        return {}

    end_va = insns[-1]["end_va"]
    backedge_targets = set()
    jcc_boundary_crossings_32b = 0
    fused_jcc_pairs = []

    for idx, ins in enumerate(insns):
        if ins["mnem"] in JCC_MNEMONICS:
            m_tgt = re.search(r"0x([0-9a-fA-F]+)", ins["ops"])
            if m_tgt:
                tva = int(m_tgt.group(1), 16)
                if fn_va <= tva <= ins["va"]:
                    backedge_targets.add(tva)
            # Check SKX102: JCC or macro-fused CMP/TEST+JCC crossing or ending on a 32B boundary
            start_va = ins["va"]
            if idx > 0 and insns[idx - 1]["mnem"] in FUSIBLE_CMP_TEST:
                start_va = insns[idx - 1]["va"]
            end_i = ins["end_va"]
            # Crosses or ends on 32B boundary if (start_va // 32) != (end_i // 32) or (end_i % 32 == 0)
            crosses_or_ends_32 = ((start_va // 32) != ((end_i - 1) // 32)) or (end_i % 32 == 0)
            if crosses_or_ends_32:
                jcc_boundary_crossings_32b += 1
            if idx > 0 and insns[idx - 1]["mnem"] in FUSIBLE_CMP_TEST:
                fused_jcc_pairs.append({
                    "cmp_va": hex(start_va),
                    "jcc_end_va": hex(end_i),
                    "cmp_mod_32": start_va % 32,
                    "jcc_end_mod_32": end_i % 32,
                    "skx102_hazard_32b": crosses_or_ends_32,
                })

    loop_hdr_va = min(backedge_targets) if backedge_targets else fn_va
    dsb_32b_windows_spanned = ((end_va - 1) // 32) - (fn_va // 32) + 1
    l1i_64b_lines_spanned = ((end_va - 1) // 64) - (fn_va // 64) + 1
    itlb_4k_pages_spanned = ((end_va - 1) // 4096) - (fn_va // 4096) + 1

    return {
        "symbol": fn_name,
        "entry_va": hex(fn_va),
        "end_va": hex(end_va),
        "size_bytes": end_va - fn_va,
        "entry_mod_16": fn_va % 16,
        "entry_mod_32": fn_va % 32,
        "entry_mod_64": fn_va % 64,
        "entry_mod_4096": fn_va % 4096,
        "entry_mod_16384": fn_va % 16384,
        "loop_header_va": hex(loop_hdr_va),
        "loop_header_mod_16": loop_hdr_va % 16,
        "loop_header_mod_32": loop_hdr_va % 32,
        "loop_header_mod_64": loop_hdr_va % 64,
        "loop_header_in_tail_12b_of_64b_line": (loop_hdr_va % 64) >= 52,
        "dsb_32b_windows_spanned": dsb_32b_windows_spanned,
        "l1i_64b_lines_spanned": l1i_64b_lines_spanned,
        "itlb_4k_pages_spanned": itlb_4k_pages_spanned,
        "skx102_32b_boundary_jcc_count": jcc_boundary_crossings_32b,
        "fused_jcc_pairs": fused_jcc_pairs[:8],
    }


def analyze_eh_frame_locality(elf_path: Path) -> dict:
    proc = subprocess.run([LLVM_READELF, "-SW", str(elf_path)], capture_output=True, text=True, check=True)
    eh_hdr_size = 0
    eh_frame_size = 0
    for line in proc.stdout.splitlines():
        m = re.match(r"^\s*\[\s*\d+\]\s+(\S+)\s+(\S+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)", line)
        if m:
            sname, _, _, _, sz_hex = m.groups()
            if sname == ".eh_frame_hdr":
                eh_hdr_size = int(sz_hex, 16)
            elif sname == ".eh_frame":
                eh_frame_size = int(sz_hex, 16)
    fde_entries = max(0, (eh_hdr_size - 12) // 8)
    bsearch_steps = int(math.ceil(math.log2(max(1, fde_entries))))
    return {
        "eh_frame_hdr_bytes": eh_hdr_size,
        "eh_frame_bytes": eh_frame_size,
        "fde_table_entries": fde_entries,
        "binary_search_comparisons_per_frame": bsearch_steps,
        "eh_frame_4k_pages": (eh_frame_size + 4095) // 4096,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=HERE / "layout_root_cause_catalog.json")
    args = parser.parse_args()

    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    tmp_base.mkdir(parents=True, exist_ok=True)

    results = {}
    with tempfile.TemporaryDirectory(dir=tmp_base) as tmp:
        tmp_dir = Path(tmp)
        for wname, src_code in WORKLOAD_SOURCES.items():
            src_file = tmp_dir / f"{wname.replace('-', '_')}.rs"
            src_file.write_text(src_code, encoding="utf-8")
            target_sym = HOT_SYMBOLS[wname]

            # 1. Default unshuffled build without -Z function-sections (ld.bfd style single .text)
            bin_default = tmp_dir / f"{wname}_default"
            subprocess.run(
                [RUSTC, "-C", "opt-level=3", "-C", "codegen-units=16", str(src_file), "-o", str(bin_default)],
                check=True,
            )
            default_info = parse_function_disassembly(bin_default, target_sym)
            default_eh = analyze_eh_frame_locality(bin_default)

            # 2. 16 --shuffle-sections seeds with -Z function-sections=yes and rust-lld
            seed_records = []
            for seed in range(1, 17):
                bin_seed = tmp_dir / f"{wname}_seed_{seed}"
                env = os.environ.copy()
                env["RUSTC_BOOTSTRAP"] = "1"
                subprocess.run(
                    [
                        RUSTC,
                        "-C", "opt-level=3",
                        "-C", "codegen-units=16",
                        "-Z", "function-sections=yes",
                        "-Z", "unstable-options",
                        "-C", "link-self-contained=+linker",
                        "-C", "linker-flavor=gnu-lld-cc",
                        "-C", f"link-arg=-Wl,--shuffle-sections=*={seed}",
                        str(src_file),
                        "-o", str(bin_seed),
                    ],
                    env=env,
                    check=True,
                )
                info = parse_function_disassembly(bin_seed, target_sym)
                info["seed"] = seed
                if wname == "bench-serde-json":
                    med_us = Q6_SEED_MEDIANS_SERDE_US[seed]
                    info["q6_median_us"] = med_us
                    info["regime"] = "slow_bimodal" if seed in (1, 6, 11, 14) else "fast_bimodal"
                seed_records.append(info)
                if seed == 1:
                    lld_eh = analyze_eh_frame_locality(bin_seed)

            results[wname] = {
                "default_no_func_sections": {
                    "disassembly_alignment": default_info,
                    "eh_frame_locality": default_eh,
                },
                "lld_function_sections_eh_frame": lld_eh,
                "shuffled_16_seeds": seed_records,
            }

    args.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
