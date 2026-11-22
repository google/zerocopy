#!/usr/bin/env python3
"""Empirical rustc + LLVM IR + MIR + native execution probe for:
- `find_cold_blocks`, `core::hint::cold_path`, `core::intrinsics::{cold_path,likely,unlikely}`,
  `@llvm.expect.i1`, and 2000:1 `!prof !"branch_weights"` propagation
- `#[optimize(size|speed|none)]`, `#[cold]`, and `-C opt-level={0,2,s,z}` LLVM attribute derivation
- `fn_can_unwind`, `AbortUnwindingCalls`, `-Z panic-in-drop=abort` (`drop_glue` vs `drop_in_place`),
  foreign vs Rust `extern "C-unwind"`, and `-C panic=immediate-abort` compatibility checks.

Uses Python standard library only. Runs exclusively inside TemporaryDirectory and
scrubs temporary paths so no local filesystem state leaks into recorded outputs.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_OUT = HERE / "probe_output"

SRC_PART_A = r"""#![feature(core_intrinsics)]
#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub fn cw_1_two_way_unlikely(c: bool, x: i32) -> i32 {
    if core::intrinsics::unlikely(c) {
        x.wrapping_add(99)
    } else {
        x.wrapping_sub(1)
    }
}

#[unsafe(no_mangle)]
pub fn cw_2_two_way_hint_cold_path(c: bool, x: i32) -> i32 {
    if c {
        core::hint::cold_path();
        x.wrapping_add(99)
    } else {
        x.wrapping_sub(1)
    }
}

#[unsafe(no_mangle)]
pub fn cw_2b_two_way_intrinsic_cold_path(c: bool, x: i32) -> i32 {
    if c {
        core::intrinsics::cold_path();
        x.wrapping_add(99)
    } else {
        x.wrapping_sub(1)
    }
}

#[unsafe(no_mangle)]
pub fn cw_3_multi_way_switch_cold(tag: u32, x: i32) -> i32 {
    match tag {
        0 => x.wrapping_add(1),
        1 => x.wrapping_add(2),
        2 => {
            core::hint::cold_path();
            x.wrapping_add(99)
        }
        3 => x.wrapping_add(4),
        _ => x,
    }
}

#[unsafe(no_mangle)]
pub fn cw_4_likely_hot_branch(c: bool, x: i32) -> i32 {
    if core::intrinsics::likely(c) {
        x.wrapping_add(1)
    } else {
        x.wrapping_sub(99)
    }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn cw_step_tick(v: u32) -> u32 {
    v.wrapping_add(1)
}

#[unsafe(no_mangle)]
pub fn cw_5_cyclic_cold_loop(enter_loop: bool, mut n: u32) -> u32 {
    if enter_loop {
        loop {
            n = cw_step_tick(n);
            if n == 0 {
                core::hint::cold_path();
                return 99;
            }
        }
    } else {
        n.wrapping_add(1)
    }
}
"""

SRC_PART_B = r"""#![feature(optimize_attribute)]
#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub fn oa_default(x: u32) -> u32 {
    x.wrapping_mul(3).wrapping_add(1)
}

#[optimize(size)]
#[unsafe(no_mangle)]
pub fn oa_size(x: u32) -> u32 {
    x.wrapping_mul(5).wrapping_add(2)
}

#[optimize(speed)]
#[unsafe(no_mangle)]
pub fn oa_speed(x: u32) -> u32 {
    x.wrapping_mul(7).wrapping_add(3)
}

#[optimize(none)]
#[unsafe(no_mangle)]
pub fn oa_none(x: u32) -> u32 {
    x.wrapping_mul(11).wrapping_add(4)
}

#[cold]
#[unsafe(no_mangle)]
pub fn oa_cold(x: u32) -> u32 {
    x.wrapping_mul(13).wrapping_add(5)
}

#[inline(always)]
#[optimize(none)]
#[unsafe(no_mangle)]
pub fn oa_inline_always_optnone(x: u32) -> u32 {
    x.wrapping_mul(17).wrapping_add(6)
}
"""

SRC_PART_C = r"""#![crate_type = "lib"]

unsafe extern "C" {
    fn ext_c();
}

unsafe extern "C-unwind" {
    fn ext_c_unwind();
}

#[unsafe(no_mangle)]
pub extern "C" fn rust_def_extern_c() {}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn rust_def_extern_c_unwind() {}

pub struct LoudDrop(pub u32);

impl Drop for LoudDrop {
    #[inline(never)]
    fn drop(&mut self) {
        if self.0 == 99 {
            panic!("drop panic");
        }
    }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub unsafe fn call_public_drop_in_place(p: *mut LoudDrop) {
    unsafe { core::ptr::drop_in_place(p) }
}

#[unsafe(no_mangle)]
pub unsafe fn caller_of_foreign_c_unwind(mut d: LoudDrop) {
    d.0 = d.0.wrapping_add(1);
    unsafe { ext_c_unwind() };
}

#[unsafe(no_mangle)]
pub unsafe fn caller_of_foreign_c(mut d: LoudDrop) {
    d.0 = d.0.wrapping_add(1);
    unsafe { ext_c() };
}
"""

SRC_DROP_MOD = r"""#![crate_type = "lib"]

pub struct LoudDrop(pub u32);

impl Drop for LoudDrop {
    #[inline(never)]
    fn drop(&mut self) {
        if self.0 == 99 {
            panic!("drop panic triggered");
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn trigger_drop_panic() {
    let _g = LoudDrop(99);
}
"""

SRC_DROP_HARNESS = r"""unsafe extern "C-unwind" {
    fn trigger_drop_panic();
}

fn main() {
    let res = std::panic::catch_unwind(|| unsafe {
        trigger_drop_panic();
    });
    if res.is_err() {
        println!("CAUGHT_DROP_PANIC");
    } else {
        println!("NO_PANIC");
    }
}
"""

SRC_DROP_BIN_DIRECT = r"""pub struct LoudDrop(pub u32);
impl Drop for LoudDrop {
    fn drop(&mut self) {
        if self.0 == 99 {
            panic!("drop panic");
        }
    }
}
fn main() {
    let _g = LoudDrop(99);
}
"""

SRC_IMM_LIB = r"""#![no_std]
#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub fn imm_bounds_index(arr: &[i32; 4], i: usize) -> i32 {
    arr[i]
}
"""

SRC_IMM_BIN = r"""#![no_std]
#![no_main]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    loop {}
}
"""


def resolve_rustc(requested: str) -> str:
    if requested != "rustc":
        return requested
    candidate = Path.home() / ".cargo/bin/rustc"
    if candidate.is_file():
        return str(candidate)
    return "rustc"


def sanitize_text(text: str, tmp_root: Path) -> str:
    s = text.replace(str(tmp_root), "<TMP>")
    s = s.replace(str(HERE), "<SUPPORT>")
    home = str(Path.home())
    if home:
        s = s.replace(home, "<HOME>")
    user = os.environ.get("USER") or ""
    if user:
        s = s.replace(user, "<USER>")
    return s


def run_cmd(cmd: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=str(cwd) if cwd else None, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)


def parse_llvm_ir(ll_text: str) -> dict:
    metadata: dict[str, str] = {}
    attrs: dict[str, str] = {}
    aliases: dict[str, dict] = {}
    decls: dict[str, dict] = {}
    defs: dict[str, dict] = {}

    lines = ll_text.splitlines()
    for line in lines:
        m_md = re.match(r"^(!\d+)\s*=\s*(.+)$", line)
        if m_md:
            metadata[m_md.group(1)] = m_md.group(2).strip()
            continue
        m_at = re.match(r"^attributes\s+(#\d+)\s*=\s*\{\s*(.*?)\s*\}\s*$", line)
        if m_at:
            attrs[m_at.group(1)] = m_at.group(2).strip()
            continue
        m_al = re.match(r"^@([^\s=]+)\s*=\s*.*?alias\b.*?,\s*ptr\s+@([^\s,]+)", line)
        if m_al:
            aliases[m_al.group(1)] = {"line": line.strip(), "target": m_al.group(2)}
            continue
        m_decl = re.match(r"^declare\b.*?@([^\s(]+)\(([^)]*)\).*?(?:#(\d+))?\s*$", line)
        if m_decl:
            attr_id = f"#{m_decl.group(3)}" if m_decl.group(3) else None
            decls[m_decl.group(1)] = {"header": line.strip(), "attr_id": attr_id}

    i = 0
    while i < len(lines):
        line = lines[i]
        m_def = re.match(r"^define\b.*?@([^\s(]+)\(.*?(?:#(\d+))?(?:\s+personality\b.*)?\s*\{\s*$", line)
        if m_def:
            name = m_def.group(1)
            attr_id = None
            m_aid = re.search(r"#(\d+)", line)
            if m_aid:
                attr_id = f"#{m_aid.group(1)}"
            body_lines = []
            j = i + 1
            while j < len(lines) and lines[j] != "}":
                body_lines.append(lines[j])
                j += 1
            defs[name] = {
                "header": line.strip(),
                "attr_id": attr_id,
                "body_lines": body_lines,
                "full_text": "\n".join([line] + body_lines + ["}"]),
            }
            i = j + 1
        else:
            i += 1

    return {"metadata": metadata, "attrs": attrs, "aliases": aliases, "decls": decls, "defs": defs}


def resolve_prof_branch_weights(body_lines: list[str], metadata: dict[str, str]) -> list[str]:
    found: list[str] = []
    for line in body_lines:
        for m in re.finditer(r"!prof\s+(!\d+)", line):
            md_val = metadata.get(m.group(1), "")
            if '"branch_weights"' in md_val:
                # Strip surrounding `!{` and `}` to normalize nicely
                inner = md_val
                if inner.startswith("!{") and inner.endswith("}"):
                    inner = inner[2:-1]
                found.append(inner)
    return found


def inspect_part_a_fn(parsed: dict, fn_name: str) -> dict:
    target_name = fn_name
    aliased_to = None
    if fn_name in parsed["aliases"]:
        aliased_to = parsed["aliases"][fn_name]["target"]
        target_name = aliased_to
    fdef = parsed["defs"].get(target_name)
    if fdef is None:
        return {"missing": True}
    body = fdef["body_lines"]
    has_cold_call = any("cold_path" in l and re.search(r"\b(?:call|invoke)\b", l) for l in body)
    expect_calls = [l.strip() for l in body if "@llvm.expect." in l]
    prof_bw = resolve_prof_branch_weights(body, parsed["metadata"])
    out = {
        "aliased_to": aliased_to,
        "has_cold_path_call_insn": has_cold_call,
        "expect_calls": expect_calls,
        "prof_branch_weights": prof_bw,
    }
    if fn_name == "cw_5_cyclic_cold_loop":
        start_lines = []
        in_start = False
        for l in body:
            if l.startswith("start:"):
                in_start = True
                continue
            if in_start:
                if re.match(r"^[A-Za-z0-9_.]+:", l):
                    break
                start_lines.append(l.strip())
        out["entry_block_has_expect"] = any("@llvm.expect." in l for l in start_lines)
        out["entry_block_has_prof"] = any("!prof " in l for l in start_lines)
        out["start_block_lines"] = start_lines
    return out


def probe_part_a(rustc_bin: str, tmp: Path) -> dict:
    src = tmp / "part_a.rs"
    src.write_text(SRC_PART_A, encoding="utf-8")
    fns = [
        "cw_1_two_way_unlikely",
        "cw_2_two_way_hint_cold_path",
        "cw_2b_two_way_intrinsic_cold_path",
        "cw_3_multi_way_switch_cold",
        "cw_4_likely_hot_branch",
        "cw_5_cyclic_cold_loop",
    ]
    modes = {
        "opt2_prepass": ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        "opt2_full": ["-C", "opt-level=2"],
        "opt2_full_nomerge": ["-C", "opt-level=2", "-Z", "merge-functions=disabled"],
        "opt0": ["-C", "opt-level=0"],
    }
    out: dict = {}
    for mode, flags in modes.items():
        ll_path = tmp / f"part_a_{mode}.ll"
        proc = run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                f"--remap-path-prefix={tmp}=<TMP>",
                "--emit=llvm-ir",
                "-o",
                str(ll_path),
                str(src),
            ]
            + flags
        )
        mode_res: dict = {"rc": proc.returncode}
        if proc.returncode == 0:
            parsed = parse_llvm_ir(ll_path.read_text(encoding="utf-8"))
            mode_res["functions"] = {fn: inspect_part_a_fn(parsed, fn) for fn in fns}
            mode_res["aliases"] = {k: v["target"] for k, v in parsed["aliases"].items()}
        else:
            mode_res["stderr"] = sanitize_text(proc.stderr, tmp)
        out[mode] = mode_res

    # MIR Inline pass check on cw_2 vs cw_1 to verify check_inline::is_inline_valid_on_fn `Err("cold")`
    mir_dir = tmp / "mir_a"
    mir_dir.mkdir(exist_ok=True)
    mir_proc = run_cmd(
        [
            rustc_bin,
            "--edition=2024",
            f"--remap-path-prefix={tmp}=<TMP>",
            "-C",
            "opt-level=2",
            "-Z",
            "dump-mir=Inline",
            "-Z",
            f"dump-mir-dir={mir_dir}",
            "--emit=llvm-ir",
            "-o",
            str(tmp / "part_a_mir.ll"),
            str(src),
        ]
    )
    mir_info = {"rc": mir_proc.returncode}
    if mir_proc.returncode == 0:
        for fn in ("cw_1_two_way_unlikely", "cw_2_two_way_hint_cold_path", "cw_2b_two_way_intrinsic_cold_path"):
            after_files = sorted(mir_dir.glob(f"*{fn}*.Inline.after.mir"))
            if after_files:
                txt = after_files[0].read_text(encoding="utf-8")
                mir_info[fn] = {
                    "calls_hint_cold_path_after_mir_inline": "hint::cold_path" in txt,
                    "calls_intrinsics_cold_path_after_mir_inline": "intrinsics::cold_path" in txt,
                }
    out["mir_inline_check"] = mir_info
    return out


def probe_part_b(rustc_bin: str, tmp: Path) -> dict:
    src = tmp / "part_b.rs"
    src.write_text(SRC_PART_B, encoding="utf-8")
    fns = ["oa_default", "oa_size", "oa_speed", "oa_none", "oa_cold", "oa_inline_always_optnone"]
    out: dict = {}
    for pipeline_mode, extra in [("prepass", ["-C", "no-prepopulate-passes"]), ("full", [])]:
        pipe_res: dict = {}
        for opt_lvl in ("0", "2", "s", "z"):
            ll_path = tmp / f"part_b_{pipeline_mode}_{opt_lvl}.ll"
            proc = run_cmd(
                [
                    rustc_bin,
                    "--edition=2024",
                    f"--remap-path-prefix={tmp}=<TMP>",
                    "-C",
                    f"opt-level={opt_lvl}",
                    "--emit=llvm-ir",
                    "-o",
                    str(ll_path),
                    str(src),
                ]
                + extra
            )
            if proc.returncode != 0:
                pipe_res[f"opt_{opt_lvl}"] = {"rc": proc.returncode, "stderr": sanitize_text(proc.stderr, tmp)}
                continue
            parsed = parse_llvm_ir(ll_path.read_text(encoding="utf-8"))
            fn_attrs = {}
            for fn in fns:
                fdef = parsed["defs"].get(fn)
                if fdef is None:
                    fn_attrs[fn] = None
                else:
                    attr_str = parsed["attrs"].get(fdef["attr_id"] or "", "")
                    fn_attrs[fn] = attr_str
            pipe_res[f"opt_{opt_lvl}"] = fn_attrs
        out[pipeline_mode] = pipe_res
    return out


def find_symbol_has_nounwind(parsed: dict, substr: str) -> tuple[str | None, bool | None, str | None]:
    for table in (parsed["defs"], parsed["decls"]):
        for name, entry in table.items():
            if substr in name:
                attr_str = parsed["attrs"].get(entry["attr_id"] or "", "")
                tokens = set(attr_str.split())
                return name, ("nounwind" in tokens), attr_str
    return None, None, None


def probe_part_c(rustc_bin: str, tmp: Path) -> dict:
    src = tmp / "part_c.rs"
    src.write_text(SRC_PART_C, encoding="utf-8")
    out: dict = {}
    strategies = {
        "panic_unwind": ["-C", "panic=unwind"],
        "panic_abort": ["-C", "panic=abort"],
        "panic_unwind_drop_abort": ["-C", "panic=unwind", "-Z", "panic-in-drop=abort"],
    }
    for key, flags in strategies.items():
        ll_path = tmp / f"part_c_{key}.ll"
        proc = run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                f"--remap-path-prefix={tmp}=<TMP>",
                "-C",
                "opt-level=0",
                "-C",
                "no-prepopulate-passes",
                "--emit=llvm-ir",
                "-o",
                str(ll_path),
                str(src),
            ]
            + flags
        )
        entry: dict = {"rc": proc.returncode}
        if proc.returncode == 0:
            parsed = parse_llvm_ir(ll_path.read_text(encoding="utf-8"))
            _, foreign_c_nw, _ = find_symbol_has_nounwind(parsed, "ext_c")
            # Be careful: "ext_c" is a prefix of "ext_c_unwind"! Check exact match.
            fc_attr = parsed["attrs"].get((parsed["decls"].get("ext_c") or {}).get("attr_id") or "", "")
            fcu_attr = parsed["attrs"].get((parsed["decls"].get("ext_c_unwind") or {}).get("attr_id") or "", "")
            rc_attr = parsed["attrs"].get((parsed["defs"].get("rust_def_extern_c") or {}).get("attr_id") or "", "")
            rcu_attr = parsed["attrs"].get((parsed["defs"].get("rust_def_extern_c_unwind") or {}).get("attr_id") or "", "")
            _, dg_nw, dg_attr = find_symbol_has_nounwind(parsed, "drop_glue")
            _, dip_nw, dip_attr = find_symbol_has_nounwind(parsed, "drop_in_place")
            caller_def = parsed["defs"].get("caller_of_foreign_c_unwind")
            caller_attr = parsed["attrs"].get((caller_def or {}).get("attr_id") or "", "")
            caller_has_invoke = bool(
                caller_def and any(re.search(r"\binvoke\b.*@ext_c_unwind\b", l) for l in caller_def["body_lines"])
            )
            caller_c_def = parsed["defs"].get("caller_of_foreign_c")
            caller_c_has_invoke = bool(
                caller_c_def and any(re.search(r"\binvoke\b.*@ext_c\b", l) for l in caller_c_def["body_lines"])
            )
            dg_name, _, _ = find_symbol_has_nounwind(parsed, "drop_glue")
            dg_def = parsed["defs"].get(dg_name) if dg_name else None
            dg_has_invoke_drop = bool(
                dg_def and any(re.search(r"\binvoke\b.*Drop4drop", l) for l in dg_def["body_lines"])
            )
            dg_calls_panic_cannot_unwind = bool(
                dg_def and any("panic_cannot_unwind" in l for l in dg_def["body_lines"])
            )

            entry.update(
                {
                    "foreign_c_nounwind": "nounwind" in set(fc_attr.split()),
                    "foreign_c_unwind_nounwind": "nounwind" in set(fcu_attr.split()),
                    "rust_def_extern_c_nounwind": "nounwind" in set(rc_attr.split()),
                    "rust_def_extern_c_unwind_nounwind": "nounwind" in set(rcu_attr.split()),
                    "lang_drop_glue_nounwind": dg_nw,
                    "public_drop_in_place_nounwind": dip_nw,
                    "caller_has_invoke_foreign_c_unwind": caller_has_invoke,
                    "caller_has_invoke_foreign_c": caller_c_has_invoke,
                    "caller_nounwind": "nounwind" in set(caller_attr.split()),
                    "drop_glue_has_invoke_drop": dg_has_invoke_drop,
                    "drop_glue_calls_panic_cannot_unwind": dg_calls_panic_cannot_unwind,
                    "raw_attrs": {
                        "ext_c": fc_attr,
                        "ext_c_unwind": fcu_attr,
                        "rust_def_extern_c": rc_attr,
                        "rust_def_extern_c_unwind": rcu_attr,
                        "drop_glue": dg_attr,
                        "drop_in_place": dip_attr,
                        "caller_of_foreign_c_unwind": caller_attr,
                    },
                }
            )
        else:
            entry["stderr"] = sanitize_text(proc.stderr, tmp)
        out[key] = entry

    # Runtime execution proof for -Z panic-in-drop=abort vs -C panic=unwind,
    # plus direct bin-link check showing IncompatiblePanicInDropStrategy against prebuilt std.
    mod_src = tmp / "drop_mod.rs"
    mod_src.write_text(SRC_DROP_MOD, encoding="utf-8")
    harness_src = tmp / "drop_harness.rs"
    harness_src.write_text(SRC_DROP_HARNESS, encoding="utf-8")
    bin_direct_src = tmp / "drop_bin_direct.rs"
    bin_direct_src.write_text(SRC_DROP_BIN_DIRECT, encoding="utf-8")

    rt_results: dict = {}
    for rt_name, flags in [
        ("panic_unwind", ["-C", "panic=unwind"]),
        ("panic_unwind_drop_abort", ["-C", "panic=unwind", "-Z", "panic-in-drop=abort"]),
    ]:
        obj = tmp / f"drop_mod_{rt_name}.o"
        exe = tmp / f"drop_harness_{rt_name}"
        c_obj = run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                f"--remap-path-prefix={tmp}=<TMP>",
                "--emit=obj",
                "-o",
                str(obj),
                str(mod_src),
            ]
            + flags
        )
        c_exe = run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                f"--remap-path-prefix={tmp}=<TMP>",
                "-C",
                "panic=unwind",
                "-C",
                f"link-arg={obj}",
                "-o",
                str(exe),
                str(harness_src),
            ]
        )
        if c_obj.returncode != 0 or c_exe.returncode != 0:
            rt_results[rt_name] = {
                "compile_rc": c_obj.returncode or c_exe.returncode,
                "stderr": sanitize_text(c_obj.stderr + c_exe.stderr, tmp),
            }
        else:
            rproc = run_cmd([str(exe)])
            rt_results[rt_name] = {
                "compile_rc": 0,
                "run_rc": rproc.returncode,
                "aborted_sigabrt": rproc.returncode == -signal.SIGABRT,
                "stdout": sanitize_text(rproc.stdout, tmp).strip(),
                "has_panic_cannot_unwind_msg": "panic in a function that cannot unwind" in rproc.stderr,
                "has_drop_glue_frame": "core::ptr::drop_glue" in rproc.stderr or "drop_glue" in rproc.stderr,
            }

    direct_bin_proc = run_cmd(
        [
            rustc_bin,
            "--edition=2024",
            f"--remap-path-prefix={tmp}=<TMP>",
            "-C",
            "panic=unwind",
            "-Z",
            "panic-in-drop=abort",
            "--crate-type=bin",
            "-o",
            str(tmp / "drop_bin_direct"),
            str(bin_direct_src),
        ]
    )
    rt_results["direct_bin_link_against_prebuilt_std"] = {
        "rc": direct_bin_proc.returncode,
        "incompatible_panic_in_drop": "incompatible with this crate's strategy of `abort`" in direct_bin_proc.stderr,
        "first_error_line": sanitize_text(
            next((l for l in direct_bin_proc.stderr.splitlines() if l.startswith("error:")), ""),
            tmp,
        ),
    }
    out["drop_in_panic_runtime"] = rt_results

    # Immediate-abort library IR emission + binary link rejection check
    imm_lib = tmp / "imm_lib.rs"
    imm_lib.write_text(SRC_IMM_LIB, encoding="utf-8")
    imm_ll = tmp / "imm_lib.ll"
    imm_proc = run_cmd(
        [
            rustc_bin,
            "--edition=2024",
            f"--remap-path-prefix={tmp}=<TMP>",
            "-Z",
            "unstable-options",
            "-C",
            "panic=immediate-abort",
            "-C",
            "opt-level=2",
            "--emit=llvm-ir",
            "-o",
            str(imm_ll),
            str(imm_lib),
        ]
    )
    imm_entry: dict = {"rc": imm_proc.returncode}
    if imm_proc.returncode == 0:
        parsed_imm = parse_llvm_ir(imm_ll.read_text(encoding="utf-8"))
        fdef = parsed_imm["defs"].get("imm_bounds_index")
        attr_str = parsed_imm["attrs"].get((fdef or {}).get("attr_id") or "", "")
        ir_text = sanitize_text((fdef or {}).get("full_text", ""), tmp)
        imm_entry.update(
            {
                "has_llvm_trap": "@llvm.trap" in ir_text,
                "has_panic_bounds_call": "panic_bounds_check" in ir_text,
                "nounwind": "nounwind" in set(attr_str.split()),
                "ir": ir_text,
            }
        )
    else:
        imm_entry["stderr"] = sanitize_text(imm_proc.stderr, tmp)
    out["panic_immediate_abort_no_std"] = imm_entry

    imm_bin_src = tmp / "imm_bin.rs"
    imm_bin_src.write_text(SRC_IMM_BIN, encoding="utf-8")
    imm_bin_proc = run_cmd(
        [
            rustc_bin,
            "--edition=2024",
            f"--remap-path-prefix={tmp}=<TMP>",
            "-Z",
            "unstable-options",
            "-C",
            "panic=immediate-abort",
            "--crate-type=bin",
            "-o",
            str(tmp / "imm_bin"),
            str(imm_bin_src),
        ]
    )
    out["panic_immediate_abort_bin_link"] = {
        "rc": imm_bin_proc.returncode,
        "stderr": sanitize_text(imm_bin_proc.stderr, tmp).strip(),
    }
    return out


def compute_checks(results: dict, baseline: dict | None) -> dict[str, bool]:
    pa = results["part_a_cold_blocks_and_branch_weights"]
    pb = results["part_b_optimize_and_cold_attrs"]
    pc = results["part_c_nounwind_and_panic_strategies"]

    pre = pa["opt2_prepass"]["functions"]
    full = pa["opt2_full_nomerge"]["functions"]
    full_merged = pa["opt2_full"]["functions"]
    opt0 = pa["opt0"]["functions"]
    mir_inl = pa["mir_inline_check"]

    checks: dict[str, bool] = {}

    # Part A assertions
    checks["a_prepass_intrinsics_erased_hint_kept"] = (
        pre["cw_1_two_way_unlikely"]["has_cold_path_call_insn"] is False
        and pre["cw_2_two_way_hint_cold_path"]["has_cold_path_call_insn"] is True
        and pre["cw_2b_two_way_intrinsic_cold_path"]["has_cold_path_call_insn"] is False
        and pre["cw_3_multi_way_switch_cold"]["has_cold_path_call_insn"] is True
        and pre["cw_4_likely_hot_branch"]["has_cold_path_call_insn"] is False
    )
    checks["a_mir_inline_blocks_cold_fn"] = (
        mir_inl.get("cw_2_two_way_hint_cold_path", {}).get("calls_hint_cold_path_after_mir_inline") is True
        and mir_inl.get("cw_2b_two_way_intrinsic_cold_path", {}).get("calls_intrinsics_cold_path_after_mir_inline") is True
        and mir_inl.get("cw_1_two_way_unlikely", {}).get("calls_intrinsics_cold_path_after_mir_inline") is True
    )
    checks["a_prepass_expect_and_switch_weights"] = (
        len(pre["cw_1_two_way_unlikely"]["expect_calls"]) == 1
        and "i1 false)" in pre["cw_1_two_way_unlikely"]["expect_calls"][0]
        and len(pre["cw_2_two_way_hint_cold_path"]["expect_calls"]) == 1
        and len(pre["cw_2b_two_way_intrinsic_cold_path"]["expect_calls"]) == 1
        and len(pre["cw_4_likely_hot_branch"]["expect_calls"]) == 1
        and "i1 true)" in pre["cw_4_likely_hot_branch"]["expect_calls"][0]
        and pre["cw_3_multi_way_switch_cold"]["expect_calls"] == []
        and pre["cw_3_multi_way_switch_cold"]["prof_branch_weights"]
        == ['!"branch_weights", i32 2000, i32 2000, i32 2000, i32 1, i32 2000']
    )
    checks["a_opt2_full_lowers_expect_to_branch_weights"] = (
        full["cw_1_two_way_unlikely"]["prof_branch_weights"] == ['!"branch_weights", !"expected", i32 1, i32 2000']
        and full["cw_2_two_way_hint_cold_path"]["prof_branch_weights"]
        == ['!"branch_weights", !"expected", i32 1, i32 2000']
        and full["cw_2b_two_way_intrinsic_cold_path"]["prof_branch_weights"]
        == ['!"branch_weights", !"expected", i32 1, i32 2000']
        and full["cw_3_multi_way_switch_cold"]["prof_branch_weights"]
        == ['!"branch_weights", i32 2000, i32 2000, i32 2000, i32 1, i32 2000']
        and full["cw_4_likely_hot_branch"]["prof_branch_weights"]
        == ['!"branch_weights", !"expected", i32 2000, i32 1']
        and all(full[f]["has_cold_path_call_insn"] is False for f in full)
        and full_merged["cw_2_two_way_hint_cold_path"]["aliased_to"] == "cw_1_two_way_unlikely"
        and full_merged["cw_2b_two_way_intrinsic_cold_path"]["aliased_to"] == "cw_1_two_way_unlikely"
    )
    checks["a_opt0_suppresses_all_hints"] = all(
        opt0[f]["has_cold_path_call_insn"] is False
        and opt0[f]["expect_calls"] == []
        and opt0[f]["prof_branch_weights"] == []
        for f in opt0
    )
    checks["a_cyclic_cold_loop_entry_unmarked"] = (
        pre["cw_5_cyclic_cold_loop"]["entry_block_has_expect"] is False
        and full["cw_5_cyclic_cold_loop"]["entry_block_has_prof"] is False
        and full["cw_5_cyclic_cold_loop"]["prof_branch_weights"]
        == ['!"branch_weights", !"expected", i32 1, i32 2000']
    )

    # Part B assertions (check prepass exact codegen_llvm emission + optnone/noinline invariant)
    def tok(lvl: str, fn: str) -> set[str]:
        return set(pb["prepass"][lvl][fn].split())

    checks["b_opt_s_default_only_optsize"] = "optsize" in tok("opt_s", "oa_default") and "minsize" not in tok("opt_s", "oa_default")
    checks["b_opt_z_default_both_minsize_and_optsize"] = {"minsize", "optsize"} <= tok("opt_z", "oa_default")
    checks["b_optimize_size_overrides_all_levels"] = all(
        {"minsize", "optsize"} <= tok(lvl, "oa_size") for lvl in ("opt_0", "opt_2", "opt_s", "opt_z")
    )
    checks["b_optimize_speed_strips_size_attrs"] = all(
        "minsize" not in tok(lvl, "oa_speed") and "optsize" not in tok(lvl, "oa_speed")
        for lvl in ("opt_0", "opt_2", "opt_s", "opt_z")
    )
    checks["b_optimize_none_forces_noinline_optnone"] = all(
        {"noinline", "optnone"} <= tok(lvl, fn) and "optsize" not in tok(lvl, fn) and "minsize" not in tok(lvl, fn)
        for lvl in ("opt_0", "opt_2", "opt_s", "opt_z")
        for fn in ("oa_none", "oa_inline_always_optnone")
    )
    checks["b_cold_orthogonal_to_size"] = (
        "cold" in tok("opt_2", "oa_cold")
        and "cold" in tok("opt_s", "oa_cold")
        and "cold" in tok("opt_z", "oa_cold")
        and "optsize" in tok("opt_s", "oa_cold")
        and {"minsize", "optsize"} <= tok("opt_z", "oa_cold")
    )

    # Part C assertions
    pu, pa_s, pda = pc["panic_unwind"], pc["panic_abort"], pc["panic_unwind_drop_abort"]
    checks["c_panic_unwind_matrix"] = (
        pu["rc"] == 0
        and pu["foreign_c_nounwind"] is True
        and pu["foreign_c_unwind_nounwind"] is False
        and pu["rust_def_extern_c_nounwind"] is True
        and pu["rust_def_extern_c_unwind_nounwind"] is False
        and pu["lang_drop_glue_nounwind"] is False
        and pu["public_drop_in_place_nounwind"] is False
        and pu["caller_has_invoke_foreign_c_unwind"] is True
        and pu["caller_has_invoke_foreign_c"] is False
        and pu["caller_nounwind"] is False
    )
    checks["c_panic_abort_foreign_c_unwind_split"] = (
        pa_s["rc"] == 0
        and pa_s["foreign_c_nounwind"] is True
        and pa_s["foreign_c_unwind_nounwind"] is False
        and pa_s["rust_def_extern_c_nounwind"] is True
        and pa_s["rust_def_extern_c_unwind_nounwind"] is True
        and pa_s["lang_drop_glue_nounwind"] is True
        and pa_s["public_drop_in_place_nounwind"] is True
        and pa_s["caller_has_invoke_foreign_c_unwind"] is True
        and pa_s["caller_nounwind"] is True
    )
    checks["c_panic_in_drop_abort_split"] = (
        pda["rc"] == 0
        and pda["lang_drop_glue_nounwind"] is True
        and pda["public_drop_in_place_nounwind"] is False
        and pda["drop_glue_has_invoke_drop"] is True
        and pda["drop_glue_calls_panic_cannot_unwind"] is True
        and pda["caller_nounwind"] is False
    )
    checks["c_drop_runtime_abort"] = (
        pc["drop_in_panic_runtime"]["panic_unwind"]["run_rc"] == 0
        and pc["drop_in_panic_runtime"]["panic_unwind"]["stdout"] == "CAUGHT_DROP_PANIC"
        and pc["drop_in_panic_runtime"]["panic_unwind_drop_abort"]["aborted_sigabrt"] is True
        and pc["drop_in_panic_runtime"]["panic_unwind_drop_abort"]["has_panic_cannot_unwind_msg"] is True
        and pc["drop_in_panic_runtime"]["direct_bin_link_against_prebuilt_std"]["rc"] != 0
        and pc["drop_in_panic_runtime"]["direct_bin_link_against_prebuilt_std"]["incompatible_panic_in_drop"] is True
    )
    imm = pc["panic_immediate_abort_no_std"]
    imm_bin = pc["panic_immediate_abort_bin_link"]
    checks["c_immediate_abort_prebuilt_core_behavior"] = (
        imm["rc"] == 0
        and imm["has_llvm_trap"] is False
        and imm["has_panic_bounds_call"] is True
        and imm["nounwind"] is True
        and imm_bin["rc"] != 0
        and "incompatible with `immediate-abort`" in imm_bin["stderr"]
    )

    if baseline is not None:
        bpa = baseline["part_a_cold_blocks_and_branch_weights"]
        bpb = baseline["part_b_optimize_and_cold_attrs"]
        bpc = baseline["part_c_nounwind_and_panic_strategies"]

        part_a_parity = True
        for mode in ("opt2_prepass", "opt0"):
            for fn, bvals in bpa[mode].items():
                lvals = pa[mode]["functions"][fn]
                for k in ("has_cold_path_call_insn", "expect_calls", "prof_branch_weights"):
                    if lvals[k] != bvals[k]:
                        part_a_parity = False
        for fn, bvals in bpa["opt2_full"].items():
            lvals = full[fn]
            for k in ("has_cold_path_call_insn", "expect_calls", "prof_branch_weights"):
                if lvals[k] != bvals[k]:
                    part_a_parity = False

        # Part B baseline comparison on full pipeline (strips target-specific attrs; check exact token sets)
        part_b_parity = True
        for opt_lvl in ("opt_2", "opt_s", "opt_z"):
            for fn, b_attr_str in bpb[opt_lvl].items():
                l_tokens = set(pb["full"][opt_lvl][fn].split())
                b_tokens = set(b_attr_str.split())
                # Compare codegen optimization & cold/inline attributes (which stay invariant)
                key_attrs = {"cold", "minsize", "optsize", "optnone", "noinline"}
                if (l_tokens & key_attrs) != (b_tokens & key_attrs):
                    part_b_parity = False

        part_c_parity = True
        for strat in ("panic_unwind", "panic_abort", "panic_unwind_drop_abort"):
            for k in (
                "rc",
                "foreign_c_nounwind",
                "foreign_c_unwind_nounwind",
                "rust_def_extern_c_nounwind",
                "rust_def_extern_c_unwind_nounwind",
                "lang_drop_glue_nounwind",
                "public_drop_in_place_nounwind",
                "caller_has_invoke_foreign_c_unwind",
                "caller_nounwind",
            ):
                if pc[strat][k] != bpc[strat][k]:
                    part_c_parity = False
        for k in ("rc", "has_llvm_trap", "has_panic_bounds_call", "nounwind"):
            if imm[k] != bpc["panic_immediate_abort_no_std"][k]:
                part_c_parity = False

        checks["parity_with_llvm23_baseline_part_a"] = part_a_parity
        checks["parity_with_llvm23_baseline_part_b"] = part_b_parity
        checks["parity_with_llvm23_baseline_part_c"] = part_c_parity

    return checks


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rustc", default="rustc", help="path to nightly rustc binary")
    ap.add_argument("--out", default=str(DEFAULT_OUT), help="output directory for probe_results.json")
    ap.add_argument(
        "--baseline",
        default=str(DEFAULT_OUT / "llvm23_baseline.json"),
        help="optional baseline JSON for cross-version parity checks",
    )
    args = ap.parse_args(argv)

    rustc_bin = resolve_rustc(args.rustc)
    ver_proc = run_cmd([rustc_bin, "--version", "--verbose"])
    if ver_proc.returncode != 0:
        print(f"failed to run {rustc_bin} --version --verbose: {ver_proc.stderr}", file=sys.stderr)
        return 1

    baseline = None
    bp = Path(args.baseline)
    if bp.is_file():
        baseline = json.loads(bp.read_text(encoding="utf-8"))

    with tempfile.TemporaryDirectory(prefix="rustc_cold_nu_probe_") as tmp_str:
        tmp = Path(tmp_str)
        results = {
            "schema": "rustc-cold-nu-probe/1",
            "generated_on": datetime.date.today().isoformat(),
            "rustc_version": ver_proc.stdout.strip(),
            "part_a_cold_blocks_and_branch_weights": probe_part_a(rustc_bin, tmp),
            "part_b_optimize_and_cold_attrs": probe_part_b(rustc_bin, tmp),
            "part_c_nounwind_and_panic_strategies": probe_part_c(rustc_bin, tmp),
        }

    checks = compute_checks(results, baseline)
    results["checks"] = checks
    results["all_checks_passed"] = all(checks.values())

    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    out_file = out_dir / "probe_results.json"
    out_file.write_text(json.dumps(results, indent=1) + "\n", encoding="utf-8")

    passed = sum(1 for v in checks.values() if v)
    print(f"Probe complete: {passed}/{len(checks)} checks passed.")
    for k, v in checks.items():
        if not v:
            print(f"  FAIL: {k}", file=sys.stderr)
    return 0 if results["all_checks_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
