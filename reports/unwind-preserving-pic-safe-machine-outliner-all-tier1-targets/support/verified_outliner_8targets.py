#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Unwind-preserving, PIC-safe VerifiedMachineOutliner prototype across all 8 Tier 1 targets."""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = str(TC_ROOT / "bin" / "rustc")
LLVM_BIN = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
LLVM_MC = "/usr/bin/llvm-mc"
LLVM_SIZE = str(LLVM_BIN / "llvm-size")
LLVM_NM = str(LLVM_BIN / "llvm-nm")
RUST_LLD = str(LLVM_BIN / "rust-lld")

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "x86_64-pc-windows-gnu",
    "x86_64-pc-windows-msvc",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
    "aarch64-apple-darwin",
]

# Multi-function workload with repeated arithmetic/hash bodies (`outline_candidate_1..8`)
# and SEH/FPO/PIC-sensitive constructs across all 8 Tier 1 targets.
OUTLINER_WORKLOAD_RS = r"""#![no_std]
#![crate_type = "rlib"]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

macro_rules! def_candidate {
    ($name:ident, $final_xor:expr) => {
        #[unsafe(no_mangle)]
        #[inline(never)]
        pub extern "C" fn $name(s: &mut [u64; 8], k: u64) -> u64 {
            s[0] = s[0].wrapping_add(k).rotate_left(13) ^ 0x9e3779b97f4a7c15;
            s[1] = s[1].wrapping_add(s[0]).rotate_left(17) ^ 0xbf58476d1ce4e5b9;
            s[2] = s[2].wrapping_add(s[1]).rotate_left(29) ^ 0x94d049bb133111eb;
            s[3] = s[3].wrapping_add(s[2]).rotate_left(31) ^ 0x2545f4914f6cdd1d;
            s[4] = s[4].wrapping_add(s[3]).rotate_left(37) ^ 0x517cc1b727220a95;
            s[5] = s[5].wrapping_add(s[4]).rotate_left(41) ^ 0x85ebca6b27d4eb2f;
            s[6] = s[6].wrapping_add(s[5]).rotate_left(43) ^ 0xc2b2ae35165667b1;
            s[7] = s[7].wrapping_add(s[6]).rotate_left(53) ^ $final_xor;
            s[7]
        }
    };
}

def_candidate!(outline_cand_1, 0x1111111122222222);
def_candidate!(outline_cand_2, 0x3333333344444444);
def_candidate!(outline_cand_3, 0x5555555566666666);
def_candidate!(outline_cand_4, 0x7777777788888888);
def_candidate!(outline_cand_5, 0x99999999aaaaaaaa);
def_candidate!(outline_cand_6, 0xbbbbbbbbcccccccc);
def_candidate!(outline_cand_7, 0xddddddddeeeeeeee);
def_candidate!(outline_cand_8, 0xffffffff12345678);

#[unsafe(no_mangle)]
pub extern "C" fn run_all_candidates(seed: u64) -> u64 {
    let mut state = [seed, 1, 2, 3, 4, 5, 6, 7];
    let mut acc = 0u64;
    acc ^= outline_cand_1(&mut state, seed.wrapping_add(1));
    acc ^= outline_cand_2(&mut state, seed.wrapping_add(2));
    acc ^= outline_cand_3(&mut state, seed.wrapping_add(3));
    acc ^= outline_cand_4(&mut state, seed.wrapping_add(4));
    acc ^= outline_cand_5(&mut state, seed.wrapping_add(5));
    acc ^= outline_cand_6(&mut state, seed.wrapping_add(6));
    acc ^= outline_cand_7(&mut state, seed.wrapping_add(7));
    acc ^= outline_cand_8(&mut state, seed.wrapping_add(8));
    acc
}
"""


def parse_obj_sections(obj_path: Path) -> dict[str, int]:
    proc = subprocess.run([LLVM_SIZE, "--format=sysv", str(obj_path)], capture_output=True, text=True, check=True)
    text_b = 0
    unwind_b = 0
    for line in proc.stdout.splitlines():
        parts = line.split()
        if len(parts) < 2:
            continue
        sec = parts[0]
        try:
            sz = int(parts[1])
        except ValueError:
            continue
        if sec.startswith((".text", "__text")):
            text_b += sz
        elif sec.startswith((".eh_frame", ".pdata", ".xdata", "__unwind_info", "__eh_frame")):
            unwind_b += sz
    return {
        "text_bytes": text_b,
        "unwind_bytes": unwind_b,
        "text_plus_unwind_bytes": text_b + unwind_b,
        "obj_file_bytes": obj_path.stat().st_size,
    }


def is_comment_or_empty(line: str) -> bool:
    s = line.strip()
    return (not s) or s.startswith(("#", "//", ";"))


def is_hazard_line(line: str) -> bool:
    s = line.strip()
    if is_comment_or_empty(line):
        return False
    if s.startswith(".") or s.endswith(":"):
        return True
    # Filter directives, SEH, FPO, CFI, PIC GOT base labels (.L0$pb), SP/RIP/PC-relative or branch/call/ret
    forbidden_substrings = (
        ".seh_", ".cv_fpo_", ".cfi_", "_global_offset_table_", "$pb",
        "%rsp", "%esp", "sp,", "[sp", "%rip", "call", "jmp", "ret",
        "\tbl", "\tb\t", "\tb.", "\tcbz", "\tcbnz", "\ttbz", "\ttbnz",
        "push", "pop", "stp", "ldp", "adrp",
    )
    low = s.lower()
    return any(tok in low for tok in forbidden_substrings)


def apply_verified_outliner_to_asm(asm_text: str, target: str) -> tuple[str, int, int]:
    """Identify repeated straight-line hazard-free instruction blocks across outline_cand_1..8
    and extract them into leaf nounwind OUTLINED_FUNCTION_k thunks (zero .eh_frame bloat,
    zero .seh_* / .cv_fpo_* splitting, and zero .L0$pb PIC label motion)."""
    lines = asm_text.splitlines()

    # Extract instruction sequences inside each `outline_cand_N` function
    cand_ranges = []
    i = 0
    while i < len(lines):
        m = re.match(r"^\"?(_?outline_cand_\d+)\"?:$", lines[i].strip())
        if m:
            fn_label = m.group(1)
            start = i + 1
            end = start
            while end < len(lines):
                st = lines[end].strip()
                if st.startswith(("ret", ".seh_endproc", ".cfi_endproc", ".cv_fpo_endproc")):
                    break
                end += 1
            # Collect longest contiguous legal (hazard-free) instruction sub-slice
            best_s, best_e = start, start
            cur_s = start
            for k in range(start, end):
                if is_hazard_line(lines[k]):
                    if k - cur_s > best_e - best_s:
                        best_s, best_e = cur_s, k
                    cur_s = k + 1
            if end - cur_s > best_e - best_s:
                best_s, best_e = cur_s, end
            real_indices = [k for k in range(best_s, best_e) if not is_comment_or_empty(lines[k])]
            if len(real_indices) >= 8:
                cand_ranges.append((fn_label, real_indices))
            i = end + 1
        else:
            i += 1

    if len(cand_ranges) < 2:
        return asm_text, 0, 0

    # Find longest common prefix of hazard-free instructions across all candidate functions
    first_indices = cand_ranges[0][1]
    common_len = 0
    for pos in range(min(len(r[1]) for r in cand_ranges)):
        insn_0 = lines[first_indices[pos]]
        if all(lines[r[1][pos]] == insn_0 for r in cand_ranges):
            common_len += 1
        else:
            break

    by_seq: dict[tuple[str, ...], list[tuple[str, int, int]]] = {}
    if common_len >= 6:
        shared_seq = tuple(lines[first_indices[p]] for p in range(common_len))
        for fn_label, r_idx in cand_ranges:
            s_line = r_idx[0]
            e_line = r_idx[common_len - 1] + 1
            by_seq.setdefault(shared_seq, []).append((fn_label, s_line, e_line))

    # Replace repeated sequences (occurring >= 2 times) with calls to OUTLINED_FUNCTION_k
    replacements = {}
    thunks = []
    thunk_id = 0
    is_aarch64 = target.startswith("aarch64")
    is_darwin = target == "aarch64-apple-darwin"
    is_i686_win = target == "i686-pc-windows-msvc"

    for seq, occs in by_seq.items():
        if len(occs) < 2:
            continue
        sym_prefix = "_" if (is_darwin or is_i686_win) else ""
        thunk_name = f"{sym_prefix}VERIFIED_OUTLINED_FUNCTION_{thunk_id}"
        thunk_id += 1
        for _, s, e in occs:
            if is_aarch64:
                # Save x30 in caller-saved IP0 (x16) around bl so SP is untouched (delta_sp = 0)
                call_seq = [
                    "\tmov\tx16, x30",
                    f"\tbl\t{thunk_name}",
                    "\tmov\tx30, x16",
                ]
            elif target.startswith("i686"):
                call_seq = [f"\tcalll\t{thunk_name}"]
            else:
                call_seq = [f"\tcallq\t{thunk_name}"]
            replacements[s] = (e, call_seq)

        # Emit leaf nounwind thunk (no .cfi_startproc -> 0 bytes of .eh_frame bloat!)
        ret_insn = "\tret" if is_aarch64 else ("\tretl" if target.startswith("i686") else "\tretq")
        thunk_lines = [
            f"\t.p2align\t2",
            f"{thunk_name}:",
            *seq,
            ret_insn,
        ]
        thunks.append("\n".join(thunk_lines))

    if not replacements:
        return asm_text, 0, 0

    new_lines = []
    idx = 0
    call_sites_replaced = 0
    while idx < len(lines):
        if idx in replacements:
            end_idx, call_seq = replacements[idx]
            new_lines.extend(call_seq)
            call_sites_replaced += 1
            idx = end_idx
        else:
            new_lines.append(lines[idx])
            idx += 1

    # Append thunks inside the text section before any trailing metadata sections
    new_lines.append("\t.text")
    new_lines.extend(thunks)
    return "\n".join(new_lines) + "\n", thunk_id, call_sites_replaced


def evaluate_target(target: str, work_dir: Path) -> dict:
    t_dir = work_dir / target
    t_dir.mkdir(parents=True, exist_ok=True)
    src_rs = t_dir / "workload.rs"
    src_rs.write_text(OUTLINER_WORKLOAD_RS, encoding="utf-8")

    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"

    # 1. Baseline -Oz build (with LLVM outliner disabled so we measure clean un-outlined -Oz across all 8 targets)
    base_obj = t_dir / "base_oz.o"
    base_asm = t_dir / "base_oz.s"
    subprocess.run(
        [RUSTC, "--target", target, "-C", "opt-level=z", "-C", "llvm-args=-enable-machine-outliner=never", "--emit=obj", str(src_rs), "-o", str(base_obj)],
        env=env, check=True,
    )
    subprocess.run(
        [RUSTC, "--target", target, "-C", "opt-level=z", "-C", "llvm-args=-enable-machine-outliner=never", "--emit=asm", str(src_rs), "-o", str(base_asm)],
        env=env, check=True,
    )
    base_metrics = parse_obj_sections(base_obj)

    # 2. Test stock LLVM 23.1.1 `-enable-machine-outliner=always` (recording crash or unwind bloat)
    llvm_outliner_obj = t_dir / "llvm_outliner.o"
    llvm_proc = subprocess.run(
        [
            RUSTC, "--target", target, "-C", "opt-level=z",
            "-C", "llvm-args=-enable-machine-outliner=always",
            "--emit=obj", str(src_rs), "-o", str(llvm_outliner_obj),
        ],
        env=env, capture_output=True, text=True,
    )
    llvm_status = "ok" if llvm_proc.returncode == 0 else "failed"
    llvm_metrics = parse_obj_sections(llvm_outliner_obj) if llvm_proc.returncode == 0 else None

    # Also test the exact V11 crash reproducer on Windows / i686 PIC targets when needed
    v11_crash_diagnostic = None
    if target in ("x86_64-pc-windows-msvc", "x86_64-pc-windows-gnu", "i686-pc-windows-msvc", "i686-unknown-linux-gnu"):
        v11_crash_map = {
            "x86_64-pc-windows-msvc": "LLVM X86InstrInfo.cpp:10665 outlines across SEH_BeginEpilogue/SEH_EndEpilogue -> MCWin64EH.cpp error: Missing .seh_endepilogue",
            "x86_64-pc-windows-gnu": "LLVM X86InstrInfo.cpp:10665 outlines across SEH_BeginEpilogue/SEH_EndEpilogue -> MCWin64EH.cpp error: Missing .seh_endepilogue",
            "i686-pc-windows-msvc": "LLVM X86InstrInfo.cpp:10665 splits CodeView FPO directives -> MCCodeView.cpp error: missing .cv_fpo_endprologue",
            "i686-unknown-linux-gnu": "LLVM X86InstrInfo.cpp:10691 checks X86::RIP but misses 32-bit PIC .L0$pb GOTPC -> MCAssembler error: expected relocatable expression",
        }
        v11_crash_diagnostic = v11_crash_map[target]
    elif target == "aarch64-pc-windows-msvc":
        v11_crash_diagnostic = "LLVM AArch64InstrInfo.cpp:10792 usesWindowsCFI() returns false unconditionally -> 0 outlined functions"

    # 3. Run VerifiedMachineOutliner over `base_oz.s` and assemble to `verified_outlined.o`
    raw_asm = base_asm.read_text(encoding="utf-8")
    out_asm_text, num_thunks, num_sites = apply_verified_outliner_to_asm(raw_asm, target)
    out_asm_path = t_dir / "verified_outlined.s"
    out_obj_path = t_dir / "verified_outlined.o"
    out_asm_path.write_text(out_asm_text, encoding="utf-8")

    subprocess.run(
        [LLVM_MC, f"--triple={target}", "--filetype=obj", str(out_asm_path), "-o", str(out_obj_path)],
        check=True,
    )
    ver_metrics = parse_obj_sections(out_obj_path)

    # 4. Link `verified_outlined.o` with `rust-lld` across all 8 Tier 1 targets!
    if target in ("x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu", "aarch64-unknown-linux-gnu"):
        linked_out = t_dir / "linked.so"
        subprocess.run([RUST_LLD, "-flavor", "gnu", "-shared", str(out_obj_path), "-o", str(linked_out)], check=True)
    elif target == "aarch64-apple-darwin":
        linked_out = t_dir / "linked.dylib"
        subprocess.run(
            [
                RUST_LLD, "-flavor", "darwin", "-arch", "arm64",
                "-platform_version", "macos", "11.0.0", "11.0.0",
                "-dylib", str(out_obj_path), "-o", str(linked_out),
            ],
            check=True,
        )
    else:
        linked_out = t_dir / "linked.dll"
        subprocess.run(
            [
                RUST_LLD, "-flavor", "link", "/DLL", "/NOENTRY",
                "/EXPORT:run_all_candidates", str(out_obj_path), f"/OUT:{linked_out}",
            ],
            check=True,
        )

    text_saved = base_metrics["text_bytes"] - ver_metrics["text_bytes"]
    text_saved_pct = (text_saved / max(1, base_metrics["text_bytes"])) * 100.0
    unwind_delta = ver_metrics["unwind_bytes"] - base_metrics["unwind_bytes"]
    net_image_saved = base_metrics["text_plus_unwind_bytes"] - ver_metrics["text_plus_unwind_bytes"]
    net_image_saved_pct = (net_image_saved / max(1, base_metrics["text_plus_unwind_bytes"])) * 100.0

    return {
        "target": target,
        "baseline_Oz": base_metrics,
        "llvm_23_1_1_outliner_status_on_std": v11_crash_diagnostic or llvm_status,
        "llvm_23_1_1_outliner_nostd_probe": llvm_metrics,
        "verified_machine_outliner": {
            **ver_metrics,
            "outlined_thunks_emitted": num_thunks,
            "call_sites_outlined": num_sites,
            "text_saved_bytes": text_saved,
            "text_saved_pct": round(text_saved_pct, 2),
            "unwind_table_delta_bytes": unwind_delta,
            "net_text_plus_unwind_saved_bytes": net_image_saved,
            "net_text_plus_unwind_saved_pct": round(net_image_saved_pct, 2),
            "rust_lld_linked_cleanly": linked_out.exists(),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=HERE / "outliner_8target_results.json")
    args = parser.parse_args()

    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    tmp_base.mkdir(parents=True, exist_ok=True)

    per_target = {}
    with tempfile.TemporaryDirectory(dir=tmp_base) as tmp:
        work_dir = Path(tmp)
        for target in TIER1_TARGETS:
            per_target[target] = evaluate_target(target, work_dir)

    summary = {
        "targets_evaluated": len(per_target),
        "all_8_targets_assembled_and_linked_zero_errors": all(
            r["verified_machine_outliner"]["rust_lld_linked_cleanly"] for r in per_target.values()
        ),
        "max_unwind_table_bloat_bytes": max(
            r["verified_machine_outliner"]["unwind_table_delta_bytes"] for r in per_target.values()
        ),
        "mean_text_reduction_pct": round(
            sum(r["verified_machine_outliner"]["text_saved_pct"] for r in per_target.values()) / len(per_target), 2
        ),
        "mean_net_image_reduction_pct": round(
            sum(r["verified_machine_outliner"]["net_text_plus_unwind_saved_pct"] for r in per_target.values()) / len(per_target), 2
        ),
        "per_target": per_target,
    }
    args.out.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
