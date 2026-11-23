#!/usr/bin/env python3
"""Differential execution probe for rustc MIR lint_body (-Zlint-mir),
Validator (-Zvalidate-mir), SanityCheck (rustc_peek), and Prettify
(ReorderBasicBlocks / ReorderLocals) invariants."""

from __future__ import annotations

import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile


PKG_DIR = pathlib.Path(__file__).resolve().parent.parent
OUT_JSON = PKG_DIR / "support" / "probe_results.json"


def find_rustc() -> str:
    found = shutil.which("rustc")
    if found:
        return found
    candidate = pathlib.Path.home() / ".cargo" / "bin" / "rustc"
    if candidate.is_file():
        return str(candidate)
    raise RuntimeError("rustc binary not found in PATH or ~/.cargo/bin")


def find_miri_and_sysroot() -> tuple[str | None, str | None]:
    rustup_dir = pathlib.Path.home() / ".rustup" / "toolchains"
    miri_bin: str | None = None
    if rustup_dir.is_dir():
        for tc in sorted(rustup_dir.iterdir()):
            cand = tc / "bin" / "miri"
            if cand.is_file():
                miri_bin = str(cand)
                break
    sysroot_cand = pathlib.Path.home() / ".cache" / "miri"
    sysroot = str(sysroot_cand) if (sysroot_cand / "lib").is_dir() else None
    return miri_bin, sysroot


def sanitize_text(text: str, tmp_dir: str) -> str:
    text = text.replace(tmp_dir, "<tmp>")
    home = str(pathlib.Path.home())
    if home:
        text = text.replace(home, "<home>")
    text = re.sub(r"/rustc-dev/[0-9a-f]{40}/", "<rustc-src>/", text)
    text = re.sub(r"/usr/local/google/home/[^/\s]+/", "<home>/", text)
    text = re.sub(r"/x20/[^\s\"']+", "<shared>", text)
    text = re.sub(r"rustc-ice-[0-9T_-]+-\d+\.txt", "rustc-ice-<ts>.txt", text)
    return text


def run_cmd(
    cmd: list[str],
    *,
    cwd: str,
    tmp_dir: str,
    timeout: int = 30,
) -> dict[str, object]:
    env = os.environ.copy()
    env["RUSTC_ICE"] = "0"
    proc = subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return {
        "rc": proc.returncode,
        "stdout": sanitize_text(proc.stdout, tmp_dir).strip(),
        "stderr": sanitize_text(proc.stderr, tmp_dir).strip(),
    }


def extract_llvm_fn(ir_text: str, needle: str) -> str:
    lines = ir_text.splitlines()
    for idx, line in enumerate(lines):
        if line.startswith("define ") and needle in line:
            block = [line]
            for j in range(idx + 1, len(lines)):
                block.append(lines[j])
                if lines[j] == "}":
                    break
            return "\n".join(block)
    return ""


def main() -> int:
    rustc = find_rustc()
    miri_bin, miri_sysroot = find_miri_and_sysroot()

    with tempfile.TemporaryDirectory(prefix="mir_lint_pretty_probe_") as td:
        tdp = pathlib.Path(td)

        ver = run_cmd([rustc, "--version", "--verbose"], cwd=td, tmp_dir=td)
        miri_ver = (
            run_cmd([miri_bin, "--version"], cwd=td, tmp_dir=td)
            if miri_bin
            else None
        )

        # 1. Pass flag validation probe (+Lint, +SanityCheck, +Prettify)
        flag_rs = tdp / "flag_probe.rs"
        flag_rs.write_text("pub fn id(x: u32) -> u32 { x }\n", encoding="utf-8")
        flag_res = run_cmd(
            [
                rustc,
                "--crate-type",
                "lib",
                "--edition",
                "2024",
                "-Zvalidate-mir",
                "-Zmir-enable-passes=+Lint,+SanityCheck,+Prettify",
                str(flag_rs),
                "-o",
                str(tdp / "libflag.rlib"),
            ],
            cwd=td,
            tmp_dir=td,
        )
        pass_names: list[str] = []
        for line in str(flag_res["stderr"]).splitlines():
            if "valid MIR pass names are:" in line:
                pass_names = re.findall(r"`([^`]+)`", line)
                break

        # 2. lint_body (-Zlint-mir) vs Validator (-Zvalidate-mir) vs Miri
        custom_mir_cases: dict[str, dict[str, object]] = {
            "overlap_assign": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn overlap_assign(mut a: u32) -> u32 {\n"
                    "    mir! {\n"
                    "        {\n"
                    "            a = Move(a);\n"
                    "            RET = a;\n"
                    "            Return()\n"
                    "        }\n"
                    "    }\n"
                    "}\n"
                    "fn main() { assert_eq!(overlap_assign(42), 42); }\n"
                ),
                "run_miri": True,
            },
            "overlap_array_assign": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn overlap_array_assign(mut a: [u32; 8]) -> [u32; 8] {\n"
                    "    mir! {\n"
                    "        {\n"
                    "            a = Move(a);\n"
                    "            RET = a;\n"
                    "            Return()\n"
                    "        }\n"
                    "    }\n"
                    "}\n"
                    "fn main() { assert_eq!(overlap_array_assign([7; 8])[0], 7); }\n"
                ),
                "run_miri": True,
            },
            "overlap_disjoint_tuple_fields": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn overlap_disjoint_fields(mut t: (u32, u32)) -> u32 {\n"
                    "    mir! {\n"
                    "        {\n"
                    "            t.0 = Move(t.1);\n"
                    "            RET = t.0;\n"
                    "            Return()\n"
                    "        }\n"
                    "    }\n"
                    "}\n"
                    "fn main() { assert_eq!(overlap_disjoint_fields((1, 2)), 2); }\n"
                ),
                "run_miri": True,
            },
            "overlap_binop_same_local": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn overlap_binop(mut a: u32) -> u32 {\n"
                    "    mir! {\n"
                    "        {\n"
                    "            a = a + 1_u32;\n"
                    "            RET = a;\n"
                    "            Return()\n"
                    "        }\n"
                    "    }\n"
                    "}\n"
                    "fn main() { assert_eq!(overlap_binop(41), 42); }\n"
                ),
                "run_miri": True,
            },
            "use_after_storage_dead": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn use_after_storage_dead() -> u32 {\n"
                    "    mir! {\n"
                    "        let tmp: u32;\n"
                    "        {\n"
                    "            StorageLive(tmp);\n"
                    "            tmp = 7_u32;\n"
                    "            StorageDead(tmp);\n"
                    "            RET = tmp;\n"
                    "            Return()\n"
                    "        }\n"
                    "    }\n"
                    "}\n"
                    "fn main() { let _ = use_after_storage_dead(); }\n"
                ),
                "run_miri": True,
            },
            "double_storage_live_then_write": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn double_storage_live() -> u32 {\n"
                    "    mir! {\n"
                    "        let tmp: u32;\n"
                    "        {\n"
                    "            StorageLive(tmp);\n"
                    "            StorageLive(tmp);\n"
                    "            tmp = 7_u32;\n"
                    "            RET = tmp;\n"
                    "            StorageDead(tmp);\n"
                    "            Return()\n"
                    "        }\n"
                    "    }\n"
                    "}\n"
                    "fn main() { assert_eq!(double_storage_live(), 7); }\n"
                ),
                "run_miri": True,
            },
            "double_storage_live_clobber": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn double_storage_live_clobber() -> u32 {\n"
                    "    mir! {\n"
                    "        let tmp: u32;\n"
                    "        {\n"
                    "            StorageLive(tmp);\n"
                    "            tmp = 99_u32;\n"
                    "            StorageLive(tmp);\n"
                    "            RET = tmp;\n"
                    "            StorageDead(tmp);\n"
                    "            Return()\n"
                    "        }\n"
                    "    }\n"
                    "}\n"
                    "fn main() { let _ = double_storage_live_clobber(); }\n"
                ),
                "run_miri": True,
            },
            "double_storage_dead": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn double_storage_dead() -> u32 {\n"
                    "    mir! {\n"
                    "        let tmp: u32;\n"
                    "        {\n"
                    "            StorageLive(tmp);\n"
                    "            tmp = 7_u32;\n"
                    "            StorageDead(tmp);\n"
                    "            StorageDead(tmp);\n"
                    "            RET = 1_u32;\n"
                    "            Return()\n"
                    "        }\n"
                    "    }\n"
                    "}\n"
                    "fn main() { assert_eq!(double_storage_dead(), 1); }\n"
                ),
                "run_miri": True,
            },
            "return_with_live_local": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn return_with_live_local() -> u32 {\n"
                    "    mir! {\n"
                    "        let tmp: u32;\n"
                    "        {\n"
                    "            StorageLive(tmp);\n"
                    "            tmp = 7_u32;\n"
                    "            RET = tmp;\n"
                    "            Return()\n"
                    "        }\n"
                    "    }\n"
                    "}\n"
                    "fn main() { assert_eq!(return_with_live_local(), 7); }\n"
                ),
                "run_miri": True,
            },
            "call_duplicate_move_arg": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n"
                    "fn sink(_x: u32, _y: u32) -> u32 { 0 }\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn call_dup_move(mut x: u32) -> u32 {\n"
                    "    mir! {\n"
                    "        {\n"
                    "            Call(RET = sink(Move(x), Move(x)), ReturnTo(bb1), UnwindContinue())\n"
                    "        }\n"
                    "        bb1 = { Return() }\n"
                    "    }\n"
                    "}\n"
                ),
                "run_miri": False,
            },
            "call_dest_field_distinct": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n"
                    "fn id(x: u32) -> u32 { x }\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn call_field_distinct(mut p: (u32, u32)) -> u32 {\n"
                    "    mir! {\n"
                    "        {\n"
                    "            Call(p.0 = id(Move(p.1)), ReturnTo(bb1), UnwindContinue())\n"
                    "        }\n"
                    "        bb1 = { RET = p.0; Return() }\n"
                    "    }\n"
                    "}\n"
                ),
                "run_miri": False,
            },
            "call_dest_same_field": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n"
                    "fn id(x: u32) -> u32 { x }\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn call_same_field(mut p: (u32, u32)) -> u32 {\n"
                    "    mir! {\n"
                    "        {\n"
                    "            Call(p.0 = id(Move(p.0)), ReturnTo(bb1), UnwindContinue())\n"
                    "        }\n"
                    "        bb1 = { RET = p.0; Return() }\n"
                    "    }\n"
                    "}\n"
                ),
                "run_miri": False,
            },
            "unreachable_storage_poison": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub fn unreachable_poison() -> u32 {\n"
                    "    mir! {\n"
                    "        let tmp: u32;\n"
                    "        {\n"
                    "            tmp = 7_u32;\n"
                    "            RET = tmp;\n"
                    "            Return()\n"
                    "        }\n"
                    "        bb_dead = {\n"
                    "            StorageLive(tmp);\n"
                    "            StorageDead(tmp);\n"
                    "            Return()\n"
                    "        }\n"
                    "    }\n"
                    "}\n"
                ),
                "run_miri": False,
            },
            "validator_bad_unwind_action": {
                "source": (
                    "#![feature(custom_mir, core_intrinsics)]\n"
                    "#![allow(internal_features)]\n"
                    "use core::intrinsics::mir::*;\n\n"
                    "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
                    "pub extern \"C\" fn bad_unwind(f: extern \"C\" fn()) {\n"
                    "    mir! {\n"
                    "        {\n"
                    "            Call(RET = f(), ReturnTo(bb1), UnwindContinue())\n"
                    "        }\n"
                    "        bb1 = { Return() }\n"
                    "    }\n"
                    "}\n"
                ),
                "run_miri": False,
            },
        }

        modes = {
            "default": [],
            "z_validate_mir": ["-Zvalidate-mir"],
            "z_lint_mir": ["-Zlint-mir"],
            "z_validate_and_lint": ["-Zvalidate-mir", "-Zlint-mir"],
        }

        matrix_results: dict[str, dict[str, object]] = {}
        for name, spec in custom_mir_cases.items():
            src_path = tdp / f"{name}.rs"
            src_path.write_text(str(spec["source"]), encoding="utf-8")
            runs: dict[str, object] = {}
            crate_type = "bin" if spec["run_miri"] else "lib"
            for mode_name, flags in modes.items():
                out_art = tdp / f"{name}_{mode_name}"
                res = run_cmd(
                    [
                        rustc,
                        "--crate-type",
                        crate_type,
                        "--edition",
                        "2024",
                        *flags,
                        str(src_path),
                        "-o",
                        str(out_art),
                    ],
                    cwd=td,
                    tmp_dir=td,
                )
                runs[mode_name] = {
                    "flags": flags,
                    "rc": res["rc"],
                    "stderr_excerpt": str(res["stderr"])[:1800],
                }
            miri_run = None
            if spec["run_miri"] and miri_bin and miri_sysroot:
                miri_run = run_cmd(
                    [
                        miri_bin,
                        "--edition",
                        "2024",
                        "--sysroot",
                        miri_sysroot,
                        str(src_path),
                    ],
                    cwd=td,
                    tmp_dir=td,
                )
            matrix_results[name] = {
                "source": spec["source"],
                "runs": runs,
                "miri": miri_run,
            }

        # 3. SanityCheck & rustc_peek probes
        peek_cases = {
            "peek_init_ok": (
                "#![feature(rustc_attrs, core_intrinsics)]\n"
                "#![allow(internal_features)]\n"
                "use core::intrinsics::rustc_peek;\n\n"
                "#[rustc_mir(rustc_peek_maybe_init, stop_after_dataflow)]\n"
                "pub fn peek_init(x: i32) {\n"
                "    rustc_peek(&x);\n"
                "}\n",
                [],
            ),
            "peek_init_without_stop": (
                "#![feature(rustc_attrs, core_intrinsics)]\n"
                "#![allow(internal_features)]\n"
                "use core::intrinsics::rustc_peek;\n\n"
                "#[rustc_mir(rustc_peek_maybe_init)]\n"
                "pub fn peek_init_no_stop(x: i32) {\n"
                "    rustc_peek(&x);\n"
                "}\n",
                [],
            ),
            "peek_uninit_with_sanity_check_enabled": (
                "#![feature(rustc_attrs, core_intrinsics)]\n"
                "#![allow(internal_features)]\n"
                "use core::intrinsics::rustc_peek;\n\n"
                "#[rustc_mir(rustc_peek_maybe_init, stop_after_dataflow)]\n"
                "pub fn peek_uninit() {\n"
                "    let x: i32;\n"
                "    rustc_peek(&x);\n"
                "}\n",
                [],
            ),
            "peek_uninit_with_sanity_check_disabled_hits_borrowck": (
                "#![feature(rustc_attrs, core_intrinsics)]\n"
                "#![allow(internal_features)]\n"
                "use core::intrinsics::rustc_peek;\n\n"
                "#[rustc_mir(rustc_peek_maybe_init, stop_after_dataflow)]\n"
                "pub fn peek_uninit() {\n"
                "    let x: i32;\n"
                "    rustc_peek(&x);\n"
                "}\n",
                ["-Zmir-enable-passes=-SanityCheck"],
            ),
            "peek_liveness_dead": (
                "#![feature(rustc_attrs, core_intrinsics)]\n"
                "#![allow(internal_features)]\n"
                "use core::intrinsics::rustc_peek;\n\n"
                "#[rustc_mir(rustc_peek_liveness, stop_after_dataflow)]\n"
                "pub fn peek_liveness(x: i32) {\n"
                "    rustc_peek(&x);\n"
                "}\n",
                [],
            ),
            "peek_maybe_uninit_definitely_init": (
                "#![feature(rustc_attrs, core_intrinsics)]\n"
                "#![allow(internal_features)]\n"
                "use core::intrinsics::rustc_peek;\n\n"
                "#[rustc_mir(rustc_peek_maybe_uninit, stop_after_dataflow)]\n"
                "pub fn peek_maybe_uninit(x: i32) {\n"
                "    rustc_peek(&x);\n"
                "}\n",
                [],
            ),
            "peek_maybe_uninit_with_sanity_check_disabled_codegen_ice": (
                "#![feature(rustc_attrs, core_intrinsics)]\n"
                "#![allow(internal_features)]\n"
                "use core::intrinsics::rustc_peek;\n\n"
                "#[rustc_mir(rustc_peek_maybe_uninit, stop_after_dataflow)]\n"
                "pub fn peek_maybe_uninit(x: i32) {\n"
                "    rustc_peek(&x);\n"
                "}\n",
                ["-Zmir-enable-passes=-SanityCheck"],
            ),
        }
        sanity_results: dict[str, object] = {}
        for pname, (psrc, pflags) in peek_cases.items():
            ppath = tdp / f"{pname}.rs"
            ppath.write_text(psrc, encoding="utf-8")
            pres = run_cmd(
                [
                    rustc,
                    "--crate-type",
                    "lib",
                    "--edition",
                    "2024",
                    *pflags,
                    str(ppath),
                    "-o",
                    str(tdp / f"{pname}.rlib"),
                ],
                cwd=td,
                tmp_dir=td,
            )
            sanity_results[pname] = {
                "flags": pflags,
                "rc": pres["rc"],
                "stderr_excerpt": str(pres["stderr"])[:2200],
            }

        # 4. Prettify (ReorderBasicBlocks + ReorderLocals) differential probe
        pretty_src = (
            "#[inline(never)]\n"
            "pub fn multi_branch_cfg(x: i32, flag: bool) -> i32 {\n"
            "    let mut sum = 0;\n"
            "    let mut i = 0;\n"
            "    while i < x {\n"
            "        if flag && (i % 2 == 0) {\n"
            "            sum += i * 3;\n"
            "        } else if i == 5 {\n"
            "            return sum + 100;\n"
            "        } else {\n"
            "            sum -= 1;\n"
            "        }\n"
            "        i += 1;\n"
            "    }\n"
            "    sum\n"
            "}\n\n"
            "fn main() {\n"
            "    println!(\"PRETTIFY={}\", multi_branch_cfg(8, true) + multi_branch_cfg(4, false));\n"
            "}\n"
        )
        pretty_rs = tdp / "prettify_probe.rs"
        pretty_rs.write_text(pretty_src, encoding="utf-8")

        base_dump_dir = tdp / "mir_base"
        pretty_dump_dir = tdp / "mir_pretty"
        base_dump_dir.mkdir()
        pretty_dump_dir.mkdir()

        base_bin = tdp / "prettify_base"
        pretty_bin = tdp / "prettify_on"
        base_ll = tdp / "prettify_base.ll"
        pretty_ll = tdp / "prettify_on.ll"

        base_compile = run_cmd(
            [
                rustc,
                "--edition",
                "2024",
                "-O",
                "-Zdump-mir=ReorderBasicBlocks|ReorderLocals|runtime-optimized",
                "-Zdump-mir-dir=" + str(base_dump_dir),
                str(pretty_rs),
                "-o",
                str(base_bin),
            ],
            cwd=td,
            tmp_dir=td,
        )
        pretty_compile = run_cmd(
            [
                rustc,
                "--edition",
                "2024",
                "-O",
                "-Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals",
                "-Zdump-mir=ReorderBasicBlocks|ReorderLocals|runtime-optimized",
                "-Zdump-mir-dir=" + str(pretty_dump_dir),
                str(pretty_rs),
                "-o",
                str(pretty_bin),
            ],
            cwd=td,
            tmp_dir=td,
        )
        run_cmd(
            [
                rustc,
                "--edition",
                "2024",
                "-O",
                "--emit=llvm-ir",
                str(pretty_rs),
                "-o",
                str(base_ll),
            ],
            cwd=td,
            tmp_dir=td,
        )
        run_cmd(
            [
                rustc,
                "--edition",
                "2024",
                "-O",
                "-Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals",
                "--emit=llvm-ir",
                str(pretty_rs),
                "-o",
                str(pretty_ll),
            ],
            cwd=td,
            tmp_dir=td,
        )

        base_exec = run_cmd([str(base_bin)], cwd=td, tmp_dir=td)
        pretty_exec = run_cmd([str(pretty_bin)], cwd=td, tmp_dir=td)

        base_ir_fn = extract_llvm_fn(base_ll.read_text(encoding="utf-8"), "multi_branch_cfg")
        pretty_ir_fn = extract_llvm_fn(pretty_ll.read_text(encoding="utf-8"), "multi_branch_cfg")

        def alpha_norm_llvm(ir: str) -> str:
            # Canonicalize MIR-derived basic-block labels (`bbN`) by first-appearance order
            # and collapse label comment padding differences (`bb9` vs `bb11`).
            mapping: dict[str, str] = {}
            def repl(m: re.Match[str]) -> str:
                tok = m.group(0)
                if tok not in mapping:
                    mapping[tok] = f"bbK{len(mapping)}"
                return mapping[tok]
            normed = re.sub(r"\bbb\d+\b", repl, ir)
            return re.sub(r"\s+; preds =", " ; preds =", normed)

        llvm_alpha_identical = (
            bool(base_ir_fn)
            and alpha_norm_llvm(base_ir_fn) == alpha_norm_llvm(pretty_ir_fn)
        )

        # Also check compiled object .text equivalence as a library without main's specialization
        lib_base_obj = tdp / "libpretty_base.o"
        lib_pretty_obj = tdp / "libpretty_on.o"
        run_cmd(
            [rustc, "--crate-type", "lib", "--edition", "2024", "-O", "--emit=obj", str(pretty_rs), "-o", str(lib_base_obj)],
            cwd=td,
            tmp_dir=td,
        )
        run_cmd(
            [rustc, "--crate-type", "lib", "--edition", "2024", "-O", "-Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals", "--emit=obj", str(pretty_rs), "-o", str(lib_pretty_obj)],
            cwd=td,
            tmp_dir=td,
        )
        lib_obj_identical = lib_base_obj.read_bytes() == lib_pretty_obj.read_bytes()

        def load_single_dump(dump_dir: pathlib.Path, pattern: str) -> str:
            matches = sorted(dump_dir.glob(pattern))
            if not matches:
                return ""
            return matches[0].read_text(encoding="utf-8")

        mir_dumps = {
            "baseline_runtime_optimized": load_single_dump(
                base_dump_dir, "*multi_branch_cfg.*.runtime-optimized.after.mir"
            ),
            "before_reorder_basic_blocks": load_single_dump(
                pretty_dump_dir, "*multi_branch_cfg.*.ReorderBasicBlocks.before.mir"
            ),
            "after_reorder_basic_blocks": load_single_dump(
                pretty_dump_dir, "*multi_branch_cfg.*.ReorderBasicBlocks.after.mir"
            ),
            "after_reorder_locals": load_single_dump(
                pretty_dump_dir, "*multi_branch_cfg.*.ReorderLocals.after.mir"
            ),
            "prettify_runtime_optimized": load_single_dump(
                pretty_dump_dir, "*multi_branch_cfg.*.runtime-optimized.after.mir"
            ),
        }

        # Dead unreachable block RPO crash at -Zmir-opt-level=0
        dead_bb_rs = tdp / "dead_bb_unsorted.rs"
        dead_bb_rs.write_text(
            "#![feature(custom_mir, core_intrinsics)]\n"
            "#![allow(internal_features)]\n"
            "use core::intrinsics::mir::*;\n"
            "#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n"
            "pub fn dead_bb_unsorted2(x: u32) -> u32 {\n"
            "    mir! {\n"
            "        { Goto(bb3) }\n"
            "        bb1 = { RET = 99_u32; Return() }\n"
            "        bb2 = { RET = x; Return() }\n"
            "        bb3 = { Goto(bb2) }\n"
            "    }\n"
            "}\n",
            encoding="utf-8",
        )
        dead_bb_opt0 = run_cmd(
            [
                rustc,
                "--crate-type",
                "lib",
                "--edition",
                "2024",
                "-Zmir-opt-level=0",
                "-Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals",
                str(dead_bb_rs),
                "-o",
                str(tdp / "libdead0.rlib"),
            ],
            cwd=td,
            tmp_dir=td,
        )
        dead_bb_default = run_cmd(
            [
                rustc,
                "--crate-type",
                "lib",
                "--edition",
                "2024",
                "-Zmir-enable-passes=+ReorderBasicBlocks,+ReorderLocals",
                str(dead_bb_rs),
                "-o",
                str(tdp / "libdead1.rlib"),
            ],
            cwd=td,
            tmp_dir=td,
        )

        payload = {
            "rustc_version": ver["stdout"],
            "miri_version": miri_ver["stdout"] if miri_ver else None,
            "pass_flag_resolution_probe": {
                "rc": flag_res["rc"],
                "stderr": flag_res["stderr"],
                "valid_pass_names_count": len(pass_names),
                "valid_pass_names": pass_names,
            },
            "lint_body_vs_validator_vs_miri": matrix_results,
            "sanity_check_rustc_peek": sanity_results,
            "prettify_reorder_probe": {
                "baseline_compile_rc": base_compile["rc"],
                "baseline_exec": base_exec,
                "prettify_compile_rc": pretty_compile["rc"],
                "prettify_exec": pretty_exec,
                "llvm_ir_multi_branch_cfg_identical": bool(base_ir_fn) and base_ir_fn == pretty_ir_fn,
                "llvm_ir_multi_branch_cfg_alpha_identical": llvm_alpha_identical,
                "lib_obj_bytes_identical": lib_obj_identical,
                "llvm_ir_multi_branch_cfg_base": base_ir_fn,
                "llvm_ir_multi_branch_cfg_prettify": pretty_ir_fn,
                "mir_dumps": mir_dumps,
                "dead_bb_unsorted_opt0_prettify": {
                    "rc": dead_bb_opt0["rc"],
                    "stderr_excerpt": str(dead_bb_opt0["stderr"])[:1200],
                },
                "dead_bb_unsorted_default_prettify": {
                    "rc": dead_bb_default["rc"],
                    "stderr_excerpt": str(dead_bb_default["stderr"])[:1200],
                },
            },
        }

        OUT_JSON.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {OUT_JSON} ({OUT_JSON.stat().st_size} bytes)")
        print("Valid pass names count:", len(pass_names))
        print("LLVM IR identical:", payload["prettify_reorder_probe"]["llvm_ir_multi_branch_cfg_identical"])
        print("Baseline exec:", base_exec, "Prettify exec:", pretty_exec)
        print("Dead BB opt0 rc:", dead_bb_opt0["rc"], "default rc:", dead_bb_default["rc"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
