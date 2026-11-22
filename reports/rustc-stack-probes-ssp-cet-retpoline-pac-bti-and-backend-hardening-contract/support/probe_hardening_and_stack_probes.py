#!/usr/bin/env python3
"""Reproducible probe for rustc stack-probe and machine-code security hardening.

Measures on the invoking `rustc` toolchain (and `rustc_codegen_cranelift` when
installed in the active sysroot):
  - Part A: x86-64 inline stack-probe frame-size sweep across 10 sizes
    (1024..65536 B), verifying the 4,096 B page threshold, unroll-vs-loop
    transition (LLVM > 32,768 B vs Cranelift > 16,384 B), absence of
    `__rust_probestack` calls, LLVM IR `"probe-stack"="inline-asm"`, and
    suppression under `-C profile-generate` and `-Z sanitizer=address`.
  - Part B: x86-64 `-Z stack-protector={none,basic,strong,all}` (both `#![no_std]`
    and `std` partial-mitigation diagnostics), `-Z cf-protection={branch,return,full}`
    (`endbr64`, `.note.gnu.property` `IBT`/`SHSTK`, and link-time bitwise-AND
    degradation against unhardened objects), `-Z retpoline` /
    `-Z retpoline-external-thunk` (`__llvm_retpoline_r11` /
    `__x86_indirect_thunk_r11`, `-C unsafe-allow-abi-mismatch`), `-Z sanitizer=address`,
    and Cranelift fail-open matrix when Cranelift is available.
  - Part C: AArch64 (`aarch64-unknown-linux-gnu`, `#![no_core]`)
    `-Z branch-protection` matrix (`default`, `bti`, `bti,pac-ret`,
    `bti,pac-ret,leaf`, `bti,pac-ret,leaf,b-key`), verifying `hint #25` (`paciasp`),
    `hint #29` (`autiasp`), `hint #27`/`#31` (`pacibsp`/`autibsp`), `hint #34`
    (`bti c`), `hint #36` (`bti j`), `br x16` tail-call register discipline, and
    `.note.gnu.property` (`BTI`, `PAC`).

Usage:
  python3 probe_hardening_and_stack_probes.py [--out output.json]
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


FRAME_SIZES = [1024, 3968, 4096, 4097, 8192, 16384, 20480, 32752, 32768, 36864, 65536]


def run_cmd(cmd: list[str], cwd: str | None = None, timeout: int = 60) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
    )


def scrub_paths(text: str, tmpdir: str) -> str:
    """Remove temporary/host absolute paths so JSON artifacts remain portable."""
    out = text.replace(tmpdir, "<TMPDIR>")
    home = os.path.expanduser("~")
    if home and home != "/":
        out = out.replace(home, "<HOME>")
    out = re.sub(r"/tmp/tmp[a-zA-Z0-9_]+", "<TMPDIR>", out)
    return out


def find_objdump(rustc_bin: str) -> str:
    sysroot_res = run_cmd([rustc_bin, "--print", "sysroot"])
    if sysroot_res.returncode == 0:
        sysroot = Path(sysroot_res.stdout.strip())
        for candidate in sysroot.glob("lib/rustlib/*/bin/llvm-objdump"):
            if os.access(candidate, os.X_OK):
                return str(candidate)
    for name in ("objdump", "llvm-objdump"):
        found = shutil.which(name)
        if found:
            return found
    raise RuntimeError("Neither objdump nor llvm-objdump found on PATH")


def find_readelf() -> str:
    found = shutil.which("readelf")
    if found:
        return found
    raise RuntimeError("readelf not found on PATH")


def disassemble_symbol(objdump: str, obj_path: Path, symbol: str) -> str:
    if Path(objdump).name == "llvm-objdump":
        cmd = [objdump, "-d", "-r", "--x86-asm-syntax=att", f"--disassemble-symbols={symbol}", str(obj_path)]
    else:
        cmd = [objdump, "-d", "-r", f"--disassemble={symbol}", str(obj_path)]
    res = run_cmd(cmd)
    if res.returncode != 0 or symbol not in res.stdout:
        # Fallback to full objdump and slice symbol block
        cmd_full = [objdump, "-d", "-r", str(obj_path)]
        res = run_cmd(cmd_full)
        return extract_symbol_block(res.stdout, symbol)
    return extract_symbol_block(res.stdout, symbol)


def extract_symbol_block(disasm: str, symbol: str) -> str:
    lines = disasm.splitlines()
    start = None
    for idx, line in enumerate(lines):
        if re.search(rf"<{re.escape(symbol)}>:", line):
            start = idx + 1
            break
    if start is None:
        return ""
    body: list[str] = []
    for line in lines[start:]:
        if not line.strip():
            if body:
                break
            continue
        if re.match(r"^[0-9a-fA-F]+\s+<[^>]+>:", line):
            break
        body.append(line)
    return "\n".join(body)


def count_instructions(sym_asm: str) -> int:
    count = 0
    for line in sym_asm.splitlines():
        # Instruction lines begin with hex address + ':'
        if re.match(r"^\s*[0-9a-fA-F]+:\s", line):
            # Exclude continuation byte lines (no mnemonic column)
            parts = line.split("\t")
            if len(parts) >= 3 and parts[2].strip():
                count += 1
    return count


def check_cranelift_available(rustc_bin: str, tmpdir: Path) -> bool:
    probe_rs = tmpdir / "check_clif.rs"
    probe_rs.write_text("#![crate_type = \"lib\"]\npub fn f(x: u64) -> u64 { x }\n")
    res = run_cmd([
        rustc_bin,
        "-Z", "codegen-backend=cranelift",
        "--emit=obj",
        "-o", str(tmpdir / "check_clif.o"),
        str(probe_rs),
    ])
    return res.returncode == 0


def check_target_available(rustc_bin: str, target: str, tmpdir: Path) -> bool:
    probe_rs = tmpdir / "check_target.rs"
    probe_rs.write_text(
        "#![no_core]\n#![feature(no_core, lang_items)]\n#![crate_type = \"lib\"]\n"
        "#[lang = \"pointee_sized\"] pub trait PointeeSized {}\n"
        "#[lang = \"meta_sized\"] pub trait MetaSized: PointeeSized {}\n"
        "#[lang = \"sized\"] pub trait Sized: MetaSized {}\n"
        "#[lang = \"copy\"] pub trait Copy {}\n"
        "#[unsafe(no_mangle)] pub extern \"C\" fn t(x: u64) -> u64 { x }\n"
    )
    res = run_cmd([
        rustc_bin,
        f"--target={target}",
        "--emit=asm",
        "-o", str(tmpdir / "check_target.s"),
        str(probe_rs),
    ])
    return res.returncode == 0


def probe_part_a_stack_probes(
    rustc_bin: str,
    objdump: str,
    tmpdir: Path,
    has_cranelift: bool,
) -> dict[str, Any]:
    src = [
        "#![crate_type = \"lib\"]",
        "use core::hint::black_box;",
    ]
    for sz in FRAME_SIZES:
        src.append(
            f"#[unsafe(no_mangle)] #[inline(never)] "
            f"pub extern \"C\" fn frame_{sz}(v: u8) -> u8 {{ "
            f"let mut buf = [v; {sz}]; "
            f"let p = black_box(buf.as_mut_ptr()); "
            f"unsafe {{ *p.add({sz - 1}) }} }}"
        )
    rs_path = tmpdir / "stack_probes.rs"
    rs_path.write_text("\n".join(src) + "\n")

    # Compile with LLVM (obj + llvm-ir)
    llvm_obj = tmpdir / "stack_probes_llvm.o"
    llvm_ll = tmpdir / "stack_probes_llvm.ll"
    r_llvm = run_cmd([rustc_bin, "--edition=2024", "-O", "--emit=obj", "-o", str(llvm_obj), str(rs_path)])
    r_ll = run_cmd([rustc_bin, "--edition=2024", "-O", "--emit=llvm-ir", "-o", str(llvm_ll), str(rs_path)])
    ll_text = llvm_ll.read_text() if r_ll.returncode == 0 and llvm_ll.exists() else ""
    has_ir_probe_inline_asm = '"probe-stack"="inline-asm"' in ll_text

    # Test probe-stack suppression under -C profile-generate and -Z sanitizer=address
    prof_ll = tmpdir / "stack_probes_profgen.ll"
    r_prof = run_cmd([
        rustc_bin, "--edition=2024", "-O", f"-Cprofile-generate={tmpdir / 'profdata'}",
        "--emit=llvm-ir", "-o", str(prof_ll), str(rs_path),
    ])
    prof_has_probe_attr = (
        '"probe-stack"' in prof_ll.read_text()
        if r_prof.returncode == 0 and prof_ll.exists()
        else None
    )

    asan_ll = tmpdir / "stack_probes_asan.ll"
    r_asan = run_cmd([
        rustc_bin, "--edition=2024", "-O", "-Zsanitizer=address",
        "--emit=llvm-ir", "-o", str(asan_ll), str(rs_path),
    ])
    asan_has_probe_attr = (
        '"probe-stack"' in asan_ll.read_text()
        if r_asan.returncode == 0 and asan_ll.exists()
        else None
    )

    clif_obj = tmpdir / "stack_probes_clif.o"
    r_clif = None
    if has_cranelift:
        r_clif = run_cmd([
            rustc_bin, "--edition=2024", "-O", "-Z", "codegen-backend=cranelift",
            "--emit=obj", "-o", str(clif_obj), str(rs_path),
        ])

    sweep: dict[str, Any] = {}
    for sz in FRAME_SIZES:
        sym = f"frame_{sz}"
        entry: dict[str, Any] = {}
        if r_llvm.returncode == 0:
            asm = disassemble_symbol(objdump, llvm_obj, sym)
            steps = len(re.findall(r"sub[q]?\s+\$0x1000,\s*%rsp", asm))
            entry["llvm"] = {
                "rc": r_llvm.returncode,
                "has_4096_step": steps > 0,
                "probe_step_insn_count": steps,
                "has_probestack_call": "__rust_probestack" in asm,
                "has_probe_loop_branch": bool(re.search(r"\b(jne|jb|ja|jnz)\b", asm)),
                "has_movq_probe_store": bool(re.search(r"movq\s+\$0x0,\s*\(%rsp\)", asm)),
                "insn_count": count_instructions(asm),
                "asm_head": "\n".join(asm.splitlines()[:22]),
            }
        else:
            entry["llvm"] = {"rc": r_llvm.returncode, "stderr": scrub_paths(r_llvm.stderr, str(tmpdir))}

        if has_cranelift and r_clif is not None and r_clif.returncode == 0:
            casm = disassemble_symbol(objdump, clif_obj, sym)
            csteps = len(re.findall(r"sub[q]?\s+\$0x1000,\s*%rsp", casm))
            entry["cranelift"] = {
                "rc": r_clif.returncode,
                "has_4096_step": csteps > 0,
                "probe_step_insn_count": csteps,
                "has_probestack_call": "__rust_probestack" in casm or "__cranelift_probestack" in casm,
                "has_probe_loop_branch": bool(re.search(r"\b(jne|jb|ja|jnz)\b", casm)),
                "has_movl_probe_store": bool(re.search(r"movl\s+\$0x0,\s*\(%rsp\)", casm)),
                "insn_count": count_instructions(casm),
                "asm_head": "\n".join(casm.splitlines()[:22]),
            }
        else:
            entry["cranelift"] = {"available": False}
        sweep[str(sz)] = entry

    return {
        "llvm_ir_has_probe_stack_inline_asm": has_ir_probe_inline_asm,
        "llvm_ir_profile_generate_retains_probe_stack": prof_has_probe_attr,
        "llvm_ir_asan_retains_probe_stack": asan_has_probe_attr,
        "frame_size_sweep": sweep,
    }


def probe_part_b_hardening_matrix(
    rustc_bin: str,
    objdump: str,
    readelf: str,
    tmpdir: Path,
    has_cranelift: bool,
) -> dict[str, Any]:
    # Crate using std (exercises #154613 partial mitigation diagnostics & target modifiers)
    std_rs = tmpdir / "hardening_std.rs"
    std_rs.write_text(
        "#![crate_type = \"lib\"]\n"
        "use core::hint::black_box;\n"
        "#[unsafe(no_mangle)] #[inline(never)]\n"
        "pub extern \"C\" fn stack_buf(v: u8, idx: usize) -> u8 {\n"
        "    let mut buf = [v; 64];\n"
        "    let p = black_box(buf.as_mut_ptr());\n"
        "    unsafe { *p.add(idx & 63) }\n"
        "}\n"
        "#[unsafe(no_mangle)] #[inline(never)]\n"
        "pub extern \"C\" fn scalar_only(a: u64, b: u64) -> u64 {\n"
        "    a.wrapping_mul(31).wrapping_add(b)\n"
        "}\n"
        "#[unsafe(no_mangle)] #[inline(never)]\n"
        "pub extern \"C\" fn scalar_addr_taken(a: u64, b: u64) -> u64 {\n"
        "    let mut x = a.wrapping_mul(31).wrapping_add(b);\n"
        "    let p = black_box(&mut x as *mut u64);\n"
        "    unsafe { *p }\n"
        "}\n"
        "#[unsafe(no_mangle)] #[inline(never)]\n"
        "pub extern \"C\" fn indirect_call(f: extern \"C\" fn(u64) -> u64, x: u64) -> u64 {\n"
        "    f(x)\n"
        "}\n"
    )

    out: dict[str, Any] = {}

    # 1. SSP modes on LLVM (with std)
    for mode in ("none", "basic", "strong", "all"):
        obj = tmpdir / f"llvm_ssp_{mode}.o"
        res = run_cmd([rustc_bin, "--edition=2024", "-O", f"-Zstack-protector={mode}", "--emit=obj", "-o", str(obj), str(std_rs)])
        entry: dict[str, Any] = {
            "rc": res.returncode,
            "stderr_head": scrub_paths("\n".join(res.stderr.splitlines()[:12]), str(tmpdir)),
            "has_partial_mitigation_warning": "154613" in res.stderr or "allow-partial-mitigations" in res.stderr,
        }
        if res.returncode == 0:
            sb = disassemble_symbol(objdump, obj, "stack_buf")
            sc = disassemble_symbol(objdump, obj, "scalar_only")
            sa = disassemble_symbol(objdump, obj, "scalar_addr_taken")
            entry["stack_buf_has_fs28"] = "%fs:0x28" in sb
            entry["stack_buf_has_chk_fail"] = "__stack_chk_fail" in sb
            entry["scalar_only_has_fs28"] = "%fs:0x28" in sc
            entry["scalar_only_has_chk_fail"] = "__stack_chk_fail" in sc
            entry["scalar_addr_taken_has_fs28"] = "%fs:0x28" in sa
            entry["scalar_addr_taken_has_chk_fail"] = "__stack_chk_fail" in sa
            entry["stack_buf_asm"] = sb
            entry["scalar_only_asm"] = sc
        else:
            entry["stack_buf_has_fs28"] = False
            entry["stack_buf_has_chk_fail"] = False
            entry["scalar_only_has_fs28"] = False
            entry["scalar_only_has_chk_fail"] = False
            entry["scalar_addr_taken_has_fs28"] = False
            entry["scalar_addr_taken_has_chk_fail"] = False
        out[f"llvm_ssp_{mode}"] = entry

    # Test -Z allow-partial-mitigations=stack-protector and -Z deny-partial-mitigations=stack-protector
    for opt in ("allow-partial-mitigations=stack-protector", "deny-partial-mitigations=stack-protector"):
        key = "llvm_ssp_all_" + opt.split("-")[0]
        obj = tmpdir / f"{key}.o"
        res = run_cmd([
            rustc_bin, "--edition=2024", "-O", "-Zstack-protector=all", f"-Z{opt}",
            "--emit=obj", "-o", str(obj), str(std_rs),
        ])
        out[key] = {
            "rc": res.returncode,
            "stderr_head": scrub_paths("\n".join(res.stderr.splitlines()[:12]), str(tmpdir)),
        }

    # 2. Intel CET (-Z cf-protection={branch,return,full})
    for mode in ("branch", "return", "full"):
        obj = tmpdir / f"llvm_cet_{mode}.o"
        res = run_cmd([rustc_bin, "--edition=2024", "-O", f"-Zcf-protection={mode}", "--emit=obj", "-o", str(obj), str(std_rs)])
        entry = {
            "rc": res.returncode,
            "stderr_head": scrub_paths("\n".join(res.stderr.splitlines()[:8]), str(tmpdir)),
        }
        if res.returncode == 0:
            asm = disassemble_symbol(objdump, obj, "indirect_call")
            notes = run_cmd([readelf, "-n", str(obj)]).stdout
            first_insn = next((l for l in asm.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l)), "")
            entry["indirect_call_starts_endbr64"] = "endbr64" in first_insn
            entry["gnu_property_ibt"] = "IBT" in notes
            entry["gnu_property_shstk"] = "SHSTK" in notes
            entry["notes_snippet"] = notes.strip()
            entry["asm"] = asm
        out[f"llvm_cet_{mode}"] = entry

    # 2b. Test linked binary CET .note.gnu.property AND-merge degradation when linked with stock std
    cet_bin_rs = tmpdir / "cet_bin.rs"
    cet_bin_rs.write_text(
        "#[inline(never)] fn target(x: u64) -> u64 { x.wrapping_add(1) }\n"
        "fn main() {\n"
        "    let f: fn(u64) -> u64 = std::hint::black_box(target);\n"
        "    std::process::exit((f(0) - 1) as i32);\n"
        "}\n"
    )
    cet_exe = tmpdir / "cet_bin_exe"
    r_cet_bin = run_cmd([rustc_bin, "--edition=2024", "-O", "-Zcf-protection=full", "-o", str(cet_exe), str(cet_bin_rs)])
    cet_bin_notes = run_cmd([readelf, "-n", str(cet_exe)]).stdout if r_cet_bin.returncode == 0 else ""
    out["llvm_cet_full_linked_with_stock_std"] = {
        "rc": r_cet_bin.returncode,
        "stderr_head": scrub_paths("\n".join(r_cet_bin.stderr.splitlines()[:8]), str(tmpdir)),
        "linked_exe_retains_ibt": "IBT" in cet_bin_notes,
        "linked_exe_retains_shstk": "SHSTK" in cet_bin_notes,
        "notes_snippet": cet_bin_notes.strip()[:600],
    }

    # 3. Retpoline matrix
    # 3a. -Z retpoline without -C unsafe-allow-abi-mismatch=retpoline (against std)
    r_ret_no = run_cmd([rustc_bin, "--edition=2024", "-O", "-Zretpoline", "--emit=obj", "-o", str(tmpdir / "ret_no.o"), str(std_rs)])
    out["llvm_retpoline_no_abi_override"] = {
        "rc": r_ret_no.returncode,
        "stderr_head": scrub_paths("\n".join(r_ret_no.stderr.splitlines()[:12]), str(tmpdir)),
    }
    # 3b. -Z retpoline WITH -C unsafe-allow-abi-mismatch=retpoline
    ret_obj = tmpdir / "llvm_retpoline.o"
    r_ret = run_cmd([
        rustc_bin, "--edition=2024", "-O", "-Zretpoline", "-Cunsafe-allow-abi-mismatch=retpoline",
        "--emit=obj", "-o", str(ret_obj), str(std_rs),
    ])
    ret_asm = disassemble_symbol(objdump, ret_obj, "indirect_call") if r_ret.returncode == 0 else ""
    out["llvm_retpoline"] = {
        "rc": r_ret.returncode,
        "has_llvm_retpoline_r11": "__llvm_retpoline_r11" in ret_asm,
        "has_raw_indirect_call_or_jmp": bool(re.search(r"\b(call|jmp)[q]?\s+\*", ret_asm)),
        "asm": ret_asm,
    }
    # 3c. -Z retpoline-external-thunk with mismatched override (retpoline only)
    r_ext_wrong = run_cmd([
        rustc_bin, "--edition=2024", "-O", "-Zretpoline-external-thunk", "-Cunsafe-allow-abi-mismatch=retpoline",
        "--emit=obj", "-o", str(tmpdir / "ret_ext_wrong.o"), str(std_rs),
    ])
    out["llvm_retpoline_external_thunk_wrong_override"] = {
        "rc": r_ext_wrong.returncode,
        "stderr_head": scrub_paths("\n".join(r_ext_wrong.stderr.splitlines()[:12]), str(tmpdir)),
    }
    # 3d. -Z retpoline-external-thunk WITH BOTH comma-separated target-modifier overrides
    ret_ext_obj = tmpdir / "llvm_ret_ext.o"
    r_ext_ok = run_cmd([
        rustc_bin, "--edition=2024", "-O", "-Zretpoline-external-thunk",
        "-Cunsafe-allow-abi-mismatch=retpoline,retpoline-external-thunk",
        "--emit=obj", "-o", str(ret_ext_obj), str(std_rs),
    ])
    ret_ext_asm = disassemble_symbol(objdump, ret_ext_obj, "indirect_call") if r_ext_ok.returncode == 0 else ""
    out["llvm_retpoline_external_thunk_both_overrides"] = {
        "rc": r_ext_ok.returncode,
        "stderr_head": scrub_paths("\n".join(r_ext_ok.stderr.splitlines()[:12]), str(tmpdir)),
        "has_external_thunk_symbol": "__x86_indirect_thunk_r11" in ret_ext_asm,
        "has_raw_indirect_call_or_jmp": bool(re.search(r"\b(call|jmp)[q]?\s+\*", ret_ext_asm)),
        "asm": ret_ext_asm,
    }

    # 4. ASan on LLVM
    asan_obj = tmpdir / "llvm_asan.o"
    r_asan = run_cmd([rustc_bin, "--edition=2024", "-O", "-Zsanitizer=address", "--emit=obj", "-o", str(asan_obj), str(std_rs)])
    asan_sb = disassemble_symbol(objdump, asan_obj, "stack_buf") if r_asan.returncode == 0 else ""
    out["llvm_asan"] = {
        "rc": r_asan.returncode,
        "has_asan_instrumentation": "__asan_" in asan_sb or "asan" in asan_sb.lower(),
        "asm_head": "\n".join(asan_sb.splitlines()[:20]),
    }

    # 5. Cranelift four-flag matrix (if Cranelift backend is installed)
    if has_cranelift:
        clif_cases = [
            ("clif_asan", ["-Zsanitizer=address"]),
            ("clif_ssp_all", ["-Zstack-protector=all"]),
            ("clif_cet_full", ["-Zcf-protection=full"]),
            ("clif_retpoline", ["-Zretpoline", "-Cunsafe-allow-abi-mismatch=retpoline"]),
        ]
        for cname, extra in clif_cases:
            cobj = tmpdir / f"{cname}.o"
            rc = run_cmd([
                rustc_bin, "--edition=2024", "-O", "-Zcodegen-backend=cranelift",
                *extra, "--emit=obj", "-o", str(cobj), str(std_rs),
            ])
            centry: dict[str, Any] = {
                "rc": rc.returncode,
                "stderr_head": scrub_paths("\n".join(rc.stderr.splitlines()[:12]), str(tmpdir)),
            }
            if rc.returncode == 0:
                sb = disassemble_symbol(objdump, cobj, "stack_buf")
                ic = disassemble_symbol(objdump, cobj, "indirect_call")
                notes = run_cmd([readelf, "-n", str(cobj)]).stdout
                centry.update({
                    "has_asan_instrumentation": "__asan_" in sb,
                    "has_fs28": "%fs:0x28" in sb,
                    "has_chk_fail": "__stack_chk_fail" in sb,
                    "has_endbr64": "endbr64" in ic,
                    "gnu_property_ibt": "IBT" in notes,
                    "gnu_property_shstk": "SHSTK" in notes,
                    "has_retpoline_thunk": "retpoline" in ic or "indirect_thunk" in ic,
                    "has_raw_indirect_call_or_jmp": bool(re.search(r"\b(call|jmp)[q]?\s+\*", ic)),
                    "indirect_asm": ic,
                })
            out[cname] = centry
    else:
        out["cranelift_live_probe"] = {
            "available": False,
            "reason": "rustc_codegen_cranelift component not installed in invoking toolchain sysroot",
        }

    return out


def probe_part_c_aarch64_pac_bti(
    rustc_bin: str,
    readelf: str,
    tmpdir: Path,
) -> dict[str, Any]:
    target = "aarch64-unknown-linux-gnu"
    if not check_target_available(rustc_bin, target, tmpdir):
        return {"available": False, "target": target}

    arm_rs = tmpdir / "arm_pac_bti.rs"
    arm_rs.write_text(
        "#![no_core]\n"
        "#![feature(no_core, lang_items)]\n"
        "#![crate_type = \"lib\"]\n"
        "#[lang = \"pointee_sized\"] pub trait PointeeSized {}\n"
        "#[lang = \"meta_sized\"] pub trait MetaSized: PointeeSized {}\n"
        "#[lang = \"sized\"] pub trait Sized: MetaSized {}\n"
        "#[lang = \"copy\"] pub trait Copy {}\n"
        "#[repr(u8)]\n"
        "pub enum Op {\n"
        "    A = 0, B = 1, C = 2, D = 3, E = 4, F = 5, G = 6, H = 7,\n"
        "    I = 8, J = 9, K = 10, L = 11, M = 12, N = 13, O = 14, P = 15,\n"
        "}\n"
        "unsafe extern \"C\" {\n"
        "    fn ext_0(x: u64) -> u64; fn ext_1(x: u64) -> u64;\n"
        "    fn ext_2(x: u64) -> u64; fn ext_3(x: u64) -> u64;\n"
        "    fn ext_4(x: u64) -> u64; fn ext_5(x: u64) -> u64;\n"
        "    fn ext_6(x: u64) -> u64; fn ext_7(x: u64) -> u64;\n"
        "    fn ext_8(x: u64) -> u64; fn ext_9(x: u64) -> u64;\n"
        "    fn ext_10(x: u64) -> u64; fn ext_11(x: u64) -> u64;\n"
        "    fn ext_12(x: u64) -> u64; fn ext_13(x: u64) -> u64;\n"
        "    fn ext_14(x: u64) -> u64; fn ext_15(x: u64) -> u64;\n"
        "}\n"
        "#[unsafe(no_mangle)] #[inline(never)]\n"
        "pub extern \"C\" fn arm_leaf(x: u64) -> u64 { x }\n"
        "#[unsafe(no_mangle)] #[inline(never)]\n"
        "pub extern \"C\" fn arm_tailcall(f: extern \"C\" fn(u64) -> u64, x: u64) -> u64 { f(x) }\n"
        "#[unsafe(no_mangle)] #[inline(never)]\n"
        "pub extern \"C\" fn arm_nonleaf_call(f: extern \"C\" fn(u64) -> u64, x: u64) -> u64 {\n"
        "    unsafe { ext_0(f(x)); 0 }\n"
        "}\n"
        "#[unsafe(no_mangle)] #[inline(never)]\n"
        "pub extern \"C\" fn arm_jumptable(op: Op, x: u64) -> u64 {\n"
        "    unsafe {\n"
        "        match op {\n"
        "            Op::A => ext_0(x), Op::B => ext_1(x), Op::C => ext_2(x), Op::D => ext_3(x),\n"
        "            Op::E => ext_4(x), Op::F => ext_5(x), Op::G => ext_6(x), Op::H => ext_7(x),\n"
        "            Op::I => ext_8(x), Op::J => ext_9(x), Op::K => ext_10(x), Op::L => ext_11(x),\n"
        "            Op::M => ext_12(x), Op::N => ext_13(x), Op::O => ext_14(x), Op::P => ext_15(x),\n"
        "        }\n"
        "    }\n"
        "}\n"
    )

    configs = [
        ("default", []),
        ("bti_only", ["-Zbranch-protection=bti"]),
        ("bti_pac_ret", ["-Zbranch-protection=bti,pac-ret"]),
        ("bti_pac_ret_leaf", ["-Zbranch-protection=bti,pac-ret,leaf"]),
        ("bti_pac_ret_leaf_bkey", ["-Zbranch-protection=bti,pac-ret,leaf,b-key"]),
    ]

    results: dict[str, Any] = {"available": True, "target": target, "configs": {}}
    for label, extra in configs:
        asm_path = tmpdir / f"arm_{label}.s"
        obj_path = tmpdir / f"arm_{label}.o"
        r_asm = run_cmd([
            rustc_bin, "--edition=2024", f"--target={target}", "-O", *extra,
            "--emit=asm", "-o", str(asm_path), str(arm_rs),
        ])
        r_obj = run_cmd([
            rustc_bin, "--edition=2024", f"--target={target}", "-O", *extra,
            "--emit=obj", "-o", str(obj_path), str(arm_rs),
        ])
        asm_text = asm_path.read_text() if r_asm.returncode == 0 and asm_path.exists() else ""
        notes_text = (
            run_cmd([readelf, "-n", str(obj_path)]).stdout
            if r_obj.returncode == 0 and obj_path.exists()
            else ""
        )

        # Extract per-function snippets from assembly
        fn_snippets: dict[str, str] = {}
        for fn_name in ("arm_leaf", "arm_tailcall", "arm_nonleaf_call", "arm_jumptable"):
            m = re.search(
                rf"^{fn_name}:\n(.*?)^\s*\.size\s+{fn_name},",
                asm_text,
                flags=re.MULTILINE | re.DOTALL,
            )
            if m:
                fn_snippets[fn_name] = "\n".join(
                    l for l in m.group(1).splitlines()
                    if not l.strip().startswith(".cfi_")
                )

        tail_asm = fn_snippets.get("arm_tailcall", "")
        leaf_asm = fn_snippets.get("arm_leaf", "")
        nonleaf_asm = fn_snippets.get("arm_nonleaf_call", "")
        jt_asm = fn_snippets.get("arm_jumptable", "")

        results["configs"][label] = {
            "rc_asm": r_asm.returncode,
            "rc_obj": r_obj.returncode,
            "stderr_head": scrub_paths("\n".join(r_asm.stderr.splitlines()[:8]), str(tmpdir)),
            "leaf_has_hint25_paciasp": "hint\t#25" in leaf_asm or "paciasp" in leaf_asm,
            "leaf_has_hint29_autiasp": "hint\t#29" in leaf_asm or "autiasp" in leaf_asm,
            "leaf_has_hint27_pacibsp": "hint\t#27" in leaf_asm or "pacibsp" in leaf_asm,
            "leaf_has_hint31_autibsp": "hint\t#31" in leaf_asm or "autibsp" in leaf_asm,
            "leaf_has_hint34_bti_c": "hint\t#34" in leaf_asm or "bti\tc" in leaf_asm,
            "nonleaf_has_hint25_paciasp": "hint\t#25" in nonleaf_asm or "paciasp" in nonleaf_asm,
            "nonleaf_has_hint29_autiasp": "hint\t#29" in nonleaf_asm or "autiasp" in nonleaf_asm,
            "tailcall_uses_br_x16_or_x17": bool(re.search(r"\bbr\s+x(16|17)\b", tail_asm)),
            "tailcall_branch_insn": next((l.strip() for l in tail_asm.splitlines() if re.search(r"\bbr\s+", l)), ""),
            "jumptable_has_hint36_bti_j": "hint\t#36" in jt_asm or "bti\tj" in jt_asm,
            "gnu_property_bti": "BTI" in notes_text,
            "gnu_property_pac": "PAC" in notes_text,
            "notes_snippet": notes_text.strip(),
            "functions": fn_snippets,
        }

    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default=shutil.which("rustc") or "rustc")
    parser.add_argument("--out", default="-", help="Output JSON path (or '-' for stdout)")
    args = parser.parse_args()

    rustc_ver = run_cmd([args.rustc, "-vV"])
    if rustc_ver.returncode != 0:
        print(f"ERROR: failed to invoke {args.rustc} -vV: {rustc_ver.stderr}", file=sys.stderr)
        return 1

    objdump = find_objdump(args.rustc)
    readelf = find_readelf()

    with tempfile.TemporaryDirectory(prefix="rustc_hardening_probe_") as td:
        tmpdir = Path(td)
        has_clif = check_cranelift_available(args.rustc, tmpdir)
        payload = {
            "timestamp_utc": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "rustc_version": rustc_ver.stdout.strip(),
            "objdump_tool": Path(objdump).name,
            "cranelift_available": has_clif,
            "part_a_stack_probes": probe_part_a_stack_probes(args.rustc, objdump, tmpdir, has_clif),
            "part_b_ssp_cet_retpoline_asan": probe_part_b_hardening_matrix(
                args.rustc, objdump, readelf, tmpdir, has_clif
            ),
            "part_c_aarch64_pac_bti": probe_part_c_aarch64_pac_bti(args.rustc, readelf, tmpdir),
        }

    rendered = json.dumps(payload, indent=2, ensure_ascii=True) + "\n"
    if args.out == "-":
        sys.stdout.write(rendered)
    else:
        Path(args.out).write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
