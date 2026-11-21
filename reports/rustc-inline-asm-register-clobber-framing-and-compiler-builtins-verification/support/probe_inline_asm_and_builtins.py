#!/usr/bin/env python3
"""Live rustc MIR, LLVM IR, assembly, and native execution probe for inline asm & compiler-builtins."""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

PACKAGE_DIR = Path(__file__).resolve().parent.parent
SUPPORT_DIR = PACKAGE_DIR / "support"
SPECIMENS_DIR = SUPPORT_DIR / "specimens"
RESULTS_PATH = SUPPORT_DIR / "probe_results.json"
REMAP_FLAGS = [
    f"--remap-path-prefix={SPECIMENS_DIR}=support/specimens",
    f"--remap-path-prefix={PACKAGE_DIR}=package",
    f"--remap-path-prefix={Path.home()}=/home/user",
]


def _tool_env() -> dict[str, str]:
    env = os.environ.copy()
    home = Path.home()
    extra = [str(home / ".cargo/bin"), str(home / ".elan/bin"), str(home / ".local/bin")]
    env["PATH"] = ":".join(extra + [env.get("PATH", "")])
    return env


ENV = _tool_env()


def run_cmd(cmd: list[str], cwd: Path | None = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=ENV,
        text=True,
        capture_output=True,
    )
    if check and proc.returncode != 0:
        raise RuntimeError(f"command failed ({proc.returncode}): {' '.join(cmd)}\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}")
    return proc


def find_objdump() -> str | None:
    for candidate in ("llvm-objdump", "objdump"):
        p = shutil.which(candidate, path=ENV["PATH"])
        if p:
            return p
    # Check rustup llvm-tools if present
    sysroot = Path(run_cmd(["rustc", "--print", "sysroot"]).stdout.strip())
    for p in sysroot.glob("lib/rustlib/*/bin/llvm-objdump"):
        if p.is_file():
            return str(p)
    return None


def scan_sysroot_library(sysroot: Path) -> dict:
    lib_root = sysroot / "lib/rustlib/src/rust/library"
    rs_files = sorted(lib_root.rglob("*.rs"))
    asm_pat = re.compile(r"\b(?:core::arch::|std::arch::)?(asm|naked_asm|global_asm)\s*!")
    option_names = (
        "pure",
        "nomem",
        "readonly",
        "preserves_flags",
        "nostack",
        "noreturn",
        "may_unwind",
        "att_syntax",
        "raw",
    )
    by_kind: dict[str, int] = {"asm": 0, "naked_asm": 0, "global_asm": 0}
    by_crate: dict[str, int] = {}
    option_counts: dict[str, int] = {opt: 0 for opt in option_names}
    no_builtins_sites: list[dict] = []
    mem_builtins: list[str] = []

    for path in rs_files:
        rel = path.relative_to(lib_root)
        crate = rel.parts[0]
        if crate in ("vendor", "alloctests", "coretests"):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        lines = text.splitlines()
        for idx, line in enumerate(lines, 1):
            stripped = line.strip()
            if stripped.startswith("//"):
                continue
            if "no_builtins" in line:
                no_builtins_sites.append({"file": str(rel), "line": idx, "text": stripped})
            if "#[mem_builtin]" in stripped and idx < len(lines):
                mem_builtins.append(f"{rel}:{idx}: {lines[idx].strip()}")
            for m in asm_pat.finditer(line):
                kind = m.group(1)
                by_kind[kind] += 1
                by_crate[crate] = by_crate.get(crate, 0) + 1
                # Inspect up to 40 lines for options(...)
                window = "\n".join(lines[idx - 1 : min(len(lines), idx + 40)])
                opt_m = re.search(r"options\s*\(([^)]*)\)", window)
                if opt_m:
                    opts_text = opt_m.group(1)
                    for opt in option_names:
                        if re.search(rf"\b{opt}\b", opts_text):
                            option_counts[opt] += 1

    return {
        "library_root": "rustlib/src/rust/library",
        "total_rs_files_scanned": len(rs_files),
        "total_asm_macro_invocations": sum(by_kind.values()),
        "by_kind": by_kind,
        "by_crate": dict(sorted(by_crate.items())),
        "option_counts_within_40_lines": option_counts,
        "no_builtins_sites": no_builtins_sites,
        "mem_builtins": mem_builtins,
    }


def extract_llvm_functions(ll_text: str) -> dict[str, dict]:
    lines = ll_text.splitlines()
    funcs: dict[str, dict] = {}
    attrs_defs: dict[str, str] = {}
    module_asms: list[str] = []

    for line in lines:
        if line.startswith("module asm "):
            module_asms.append(line)
        m_attr = re.match(r"^(attributes #\d+ = \{.*\})$", line.strip())
        if m_attr:
            key = line.split("=")[0].strip().split()[-1]
            attrs_defs[key] = m_attr.group(1)

    cur_name: str | None = None
    cur_header: str = ""
    cur_body: list[str] = []
    for line in lines:
        m_def = re.match(r"^(?:define|declare)\b.*@\"?([A-Za-z0-9_.$]+)\"?\(", line)
        if m_def:
            cur_name = m_def.group(1)
            cur_header = line
            cur_body = [line]
            if line.startswith("declare "):
                funcs[cur_name] = {"header": cur_header, "body": line, "asm_lines": []}
                cur_name = None
            continue
        if cur_name is not None:
            cur_body.append(line)
            if line.strip() == "}":
                body_str = "\n".join(cur_body)
                asm_lines = [l.strip() for l in cur_body if " asm " in l]
                attr_refs = re.findall(r"#\d+", cur_header) + [
                    r for al in asm_lines for r in re.findall(r"#\d+", al)
                ]
                funcs[cur_name] = {
                    "header": cur_header,
                    "asm_lines": asm_lines,
                    "resolved_attrs": {r: attrs_defs[r] for r in dict.fromkeys(attr_refs) if r in attrs_defs},
                    "has_unreachable": any("unreachable" in l for l in cur_body),
                    "has_invoke": any(l.strip().startswith("invoke ") for l in cur_body),
                }
                cur_name = None
    return {"module_asm": module_asms, "functions": funcs}


def extract_asm_blocks(s_text: str) -> dict[str, list[str]]:
    blocks: dict[str, list[str]] = {}
    cur_fn: str | None = None
    for line in s_text.splitlines():
        m_label = re.match(r"^([A-Za-z_.$][A-Za-z0-9_.$]*):$", line.strip())
        if m_label and not m_label.group(1).startswith("."):
            cur_fn = m_label.group(1)
            blocks.setdefault(cur_fn, [])
        elif cur_fn is not None:
            if line.strip().startswith(".size ") or line.strip().startswith(".cfi_endproc"):
                blocks[cur_fn].append(line)
                if line.strip().startswith(".size "):
                    cur_fn = None
            else:
                blocks[cur_fn].append(line)
    return blocks


def extract_mir_inline_asm(mir_dir: Path) -> dict[str, list[str]]:
    res: dict[str, list[str]] = {}
    for mir_file in sorted(mir_dir.glob("*.mir")):
        text = mir_file.read_text(encoding="utf-8", errors="replace")
        fn_blocks = re.split(r"(?=^fn )", text, flags=re.MULTILINE)
        for blk in fn_blocks:
            m_fn = re.match(r"^fn ([A-Za-z0-9_]+)\(", blk)
            if not m_fn:
                continue
            fn_name = m_fn.group(1)
            asm_lines = [l.strip() for l in blk.splitlines() if "asm!(" in l or "unwind" in l or "return;" in l]
            if any("asm!(" in l for l in asm_lines):
                res[fn_name] = asm_lines
    return res


def probe_matrix() -> dict:
    src = SPECIMENS_DIR / "constraint_and_options_matrix.rs"
    targets = [
        ("x86_64-unknown-linux-gnu", True),
        ("aarch64-unknown-linux-gnu", True),
        ("aarch64-apple-darwin", False),
        ("x86_64-pc-windows-msvc", False),
    ]
    out: dict = {}
    objdump = find_objdump()

    for target, emit_obj in targets:
        with tempfile.TemporaryDirectory() as td_str:
            td = Path(td_str)
            mir_dir = td / "mir"
            mir_dir.mkdir()
            emits = "mir,llvm-ir,asm,obj" if emit_obj else "mir,llvm-ir,asm"
            cmd = [
                "rustc",
                "--edition", "2024", *REMAP_FLAGS,
                "--crate-type", "lib",
                "--target", target,
                "-C", "opt-level=2",
                f"--emit={emits}",
                "-Z", f"dump-mir=all",
                "-Z", f"dump-mir-dir={mir_dir}",
                "--out-dir", str(td),
                str(src),
            ]
            run_cmd(cmd)
            ll_file = next(td.glob("*.ll"))
            s_file = next(td.glob("*.s"))
            ll_info = extract_llvm_functions(ll_file.read_text(encoding="utf-8"))
            s_blocks = extract_asm_blocks(s_file.read_text(encoding="utf-8"))
            mir_info = extract_mir_inline_asm(mir_dir)

            obj_disasm = ""
            if emit_obj and objdump and target == "x86_64-unknown-linux-gnu":
                obj_file = next(td.glob("*.o"))
                obj_disasm = run_cmd([objdump, "-dr", str(obj_file)], check=False).stdout

            probe_summary: dict = {}
            for fn_name, finfo in sorted(ll_info["functions"].items()):
                if not fn_name.startswith("probe_"):
                    continue
                probe_summary[fn_name] = {
                    "llvm_header": finfo["header"],
                    "llvm_asm_lines": finfo["asm_lines"],
                    "llvm_resolved_attrs": finfo["resolved_attrs"],
                    "has_unreachable": finfo.get("has_unreachable", False),
                    "has_invoke": finfo.get("has_invoke", False),
                    "mir_asm_lines": mir_info.get(fn_name, []),
                    "asm_lines": s_blocks.get(fn_name, s_blocks.get("_" + fn_name, []))[:25],
                }
            out[target] = {
                "module_asm": ll_info["module_asm"],
                "probes": probe_summary,
                "x86_objdump_probe_sym_excerpt": [
                    l for l in obj_disasm.splitlines()
                    if any(k in l for k in ("probe_sym_and_const", "lea", "helper_target", "probe_out_early_clobber", "probe_lateout", "R_X86_64"))
                ][:24] if obj_disasm else [],
            }

    # Additional AArch64 branch-protection probe on naked vs normal fn
    with tempfile.TemporaryDirectory() as td_str:
        td = Path(td_str)
        bp_rs = td / "bp_probe.rs"
        bp_rs.write_text(
            "#![no_std]\n"
            "use core::arch::naked_asm;\n"
            "#[unsafe(no_mangle)] pub extern \"C\" fn normal_add1(x: usize) -> usize { x + 1 }\n"
            "#[unsafe(naked)] #[unsafe(no_mangle)] pub unsafe extern \"C\" fn naked_id(x: usize) -> usize { naked_asm!(\"ret\") }\n",
            encoding="utf-8",
        )
        run_cmd([
            "rustc", "--edition", "2024", *REMAP_FLAGS, "--crate-type", "lib",
            "--target", "aarch64-unknown-linux-gnu",
            "-Z", "branch-protection=bti,pac-ret",
            "-C", "unsafe-allow-abi-mismatch=branch-protection",
            "-C", "opt-level=2", "--emit=llvm-ir,asm", "--out-dir", str(td), str(bp_rs)
        ])
        ll_info = extract_llvm_functions(next(td.glob("*.ll")).read_text())
        s_blocks = extract_asm_blocks(next(td.glob("*.s")).read_text())
        out["aarch64_branch_protection_naked_vs_normal"] = {
            "normal_add1_llvm": ll_info["functions"].get("normal_add1", {}),
            "naked_id_llvm": ll_info["functions"].get("naked_id", {}),
            "module_asm": ll_info["module_asm"],
            "normal_add1_asm": s_blocks.get("normal_add1", []),
            "naked_id_asm": s_blocks.get("naked_id", []),
        }
    return out


def probe_compile_rejections() -> list[dict]:
    cases = [
        ("x86_64_reserved_rbp", "x86_64-unknown-linux-gnu", 'unsafe { core::arch::asm!("nop", in("rbp") 0u64); }'),
        ("x86_64_reserved_rsp", "x86_64-unknown-linux-gnu", 'unsafe { core::arch::asm!("nop", in("rsp") 0u64); }'),
        ("x86_64_reserved_rbx", "x86_64-unknown-linux-gnu", 'unsafe { core::arch::asm!("nop", in("rbx") 0u64); }'),
        ("x86_64_reserved_ah", "x86_64-unknown-linux-gnu", 'unsafe { core::arch::asm!("nop", in("ah") 0u8); }'),
        ("aarch64_reserved_x19", "aarch64-unknown-linux-gnu", 'unsafe { core::arch::asm!("nop", in("x19") 0u64); }'),
        ("aarch64_reserved_x29", "aarch64-unknown-linux-gnu", 'unsafe { core::arch::asm!("nop", in("x29") 0u64); }'),
        ("aarch64_reserved_sp", "aarch64-unknown-linux-gnu", 'unsafe { core::arch::asm!("nop", in("sp") 0u64); }'),
        ("aarch64_linux_x18_allowed", "aarch64-unknown-linux-gnu", 'unsafe { core::arch::asm!("nop", in("x18") 0u64); }'),
        ("aarch64_darwin_x18_reserved", "aarch64-apple-darwin", 'unsafe { core::arch::asm!("nop", in("x18") 0u64); }'),
        ("clobber_abi_with_regclass_out", "x86_64-unknown-linux-gnu", 'let _x: u64; unsafe { core::arch::asm!("nop", out(reg) _x, clobber_abi("C")); }'),
        ("pure_without_nomem_readonly", "x86_64-unknown-linux-gnu", 'let _x: u64; unsafe { core::arch::asm!("mov {}, 1", out(reg) _x, options(pure)); }'),
        ("nomem_and_readonly_conflict", "x86_64-unknown-linux-gnu", 'unsafe { core::arch::asm!("nop", options(nomem, readonly)); }'),
    ]
    results = []
    with tempfile.TemporaryDirectory() as td_str:
        td = Path(td_str)
        for idx, (name, target, body) in enumerate(cases):
            rs = td / f"diag_{idx}.rs"
            rs.write_text(f"#![no_std]\npub unsafe fn f() {{ {body} }}\n", encoding="utf-8")
            proc = run_cmd([
                "rustc", "--edition", "2024", *REMAP_FLAGS, "--crate-type", "lib",
                "--target", target, "--error-format=json",
                "--emit=metadata", "--out-dir", str(td), str(rs),
            ], check=False)
            msgs = []
            for line in proc.stderr.splitlines():
                if line.startswith("{"):
                    d = json.loads(line)
                    if d.get("level") == "error":
                        msgs.append(d.get("message", ""))
            results.append({
                "name": name,
                "target": target,
                "compile_rc": proc.returncode,
                "error_messages": msgs,
            })
    return results


def probe_ce1() -> dict:
    src = SPECIMENS_DIR / "ce1_lateout_aliasing.rs"
    objdump = find_objdump()
    out: dict = {}
    s_excerpts: list[str] = []
    for opt in ("0", "2"):
        with tempfile.TemporaryDirectory() as td_str:
            td = Path(td_str)
            bin_path = td / "ce1_bin"
            run_cmd([
                "rustc", "--edition", "2024", *REMAP_FLAGS, "-C", f"opt-level={opt}",
                "--emit=llvm-ir,asm,link", "-o", str(bin_path), str(src)
            ])
            ll_file = td / "ce1_bin.ll"
            s_file = td / "ce1_bin.s"
            run_proc = run_cmd([str(bin_path)])
            ll_text = ll_file.read_text(encoding="utf-8")
            s_text = s_file.read_text(encoding="utf-8")

            ll_asm = [l.strip() for l in ll_text.splitlines() if " asm " in l and "mov ${1:e}, 0" in l or (" asm " in l and "add" in l)]
            s_blocks = extract_asm_blocks(s_text)
            buggy_blk = next((v for k, v in s_blocks.items() if "buggy_lateout_zero_add" in k), [])
            safe_blk = next((v for k, v in s_blocks.items() if "safe_early_out_zero_add" in k), [])

            obj_lines = []
            if objdump:
                dis = run_cmd([objdump, "-d", str(bin_path)], check=False).stdout
                lines = dis.splitlines()
                for i, l in enumerate(lines):
                    if "buggy_lateout_zero_add" in l or "safe_early_out_zero_add" in l:
                        obj_lines.extend(lines[i : i + 15])

            out[f"opt_O{opt}"] = {
                "stdout": run_proc.stdout.strip(),
                "llvm_asm_calls": ll_asm,
                "buggy_lateout_asm": buggy_blk,
                "safe_early_out_asm": safe_blk,
                "objdump_excerpt": obj_lines,
            }
            if opt == "2":
                s_excerpts.append("# CE1 (-C opt-level=2): lateout(reg) vs out(reg)")
                s_excerpts.extend(buggy_blk)
                s_excerpts.append("")
                s_excerpts.extend(safe_blk)
    (SPECIMENS_DIR / "ce1_lateout_aliasing.s").write_text("\n".join(s_excerpts) + "\n", encoding="utf-8")
    return out


def probe_ce2() -> dict:
    src = SPECIMENS_DIR / "ce2_redzone_nostack.rs"
    with tempfile.TemporaryDirectory() as td_str:
        td = Path(td_str)
        bin_path = td / "ce2_bin"
        run_cmd([
            "rustc", "--edition", "2024", *REMAP_FLAGS, "-C", "opt-level=2",
            "--emit=llvm-ir,asm,link", "-o", str(bin_path), str(src)
        ])
        run_proc = run_cmd([str(bin_path)])
        ll_text = (td / "ce2_bin.ll").read_text(encoding="utf-8")
        s_text = (td / "ce2_bin.s").read_text(encoding="utf-8")
        s_blocks = extract_asm_blocks(s_text)
        with_ns = next((v for k, v in s_blocks.items() if "leaf_with_nostack" in k), [])
        without_ns = next((v for k, v in s_blocks.items() if "leaf_without_nostack" in k), [])
        ll_asm = [l.strip() for l in ll_text.splitlines() if "push " in l and " asm " in l]

        excerpt = ["# CE2 (-C opt-level=2): leaf_with_nostack vs leaf_without_nostack"] + with_ns + [""] + without_ns
        (SPECIMENS_DIR / "ce2_redzone_nostack.s").write_text("\n".join(excerpt) + "\n", encoding="utf-8")

        return {
            "stdout": run_proc.stdout.strip(),
            "llvm_asm_calls": ll_asm,
            "leaf_with_nostack_has_sub_rsp": any("subq" in l and "%rsp" in l for l in with_ns),
            "leaf_without_nostack_has_sub_rsp": any("subq" in l and "%rsp" in l for l in without_ns),
            "leaf_with_nostack_asm": with_ns,
            "leaf_without_nostack_asm": without_ns,
        }


def probe_builtins_and_loop_idiom() -> dict:
    ops_src = SPECIMENS_DIR / "builtins_128bit_ops.rs"
    objdump = find_objdump()
    targets_128: dict = {}
    for target in ("x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu", "riscv64gc-unknown-none-elf"):
        with tempfile.TemporaryDirectory() as td_str:
            td = Path(td_str)
            run_cmd([
                "rustc", "--edition", "2024", *REMAP_FLAGS, "--crate-type", "lib",
                "--target", target, "-C", "opt-level=2",
                "--emit=llvm-ir,asm,obj", "--out-dir", str(td), str(ops_src)
            ])
            ll_text = next(td.glob("*.ll")).read_text(encoding="utf-8")
            s_text = next(td.glob("*.s")).read_text(encoding="utf-8")
            s_blocks = extract_asm_blocks(s_text)
            ll_calls = {}
            for fn in ("probe_u128_div", "probe_u128_rem", "probe_i128_div", "probe_u128_mul", "probe_u128_shl", "probe_u128_lshr"):
                m = re.search(rf"define .*@{fn}\(.*?\n(.*?)\n\}}", ll_text, re.DOTALL)
                body = m.group(1) if m else ""
                calls = re.findall(r"(?:call|tail call|invoke)[^@\n]*@([A-Za-z0-9_.$]+)", body)
                ll_calls[fn] = {
                    "llvm_calls": calls,
                    "asm_lines": s_blocks.get(fn, [])[:28],
                }
            relocs = []
            if objdump and target == "x86_64-unknown-linux-gnu":
                obj_file = next(td.glob("*.o"))
                relocs = [
                    l for l in run_cmd([objdump, "-dr", str(obj_file)], check=False).stdout.splitlines()
                    if "udivti3" in l or "umodti3" in l or "divti3" in l or "R_X86_64" in l
                ]
            targets_128[target] = {"functions": ll_calls, "obj_relocs": relocs}

    # LoopIdiomRecognize self-recursion hazard
    no_attr_src = SPECIMENS_DIR / "memcpy_without_no_builtins.rs"
    with_attr_src = SPECIMENS_DIR / "memcpy_with_no_builtins.rs"
    loop_res: dict = {}
    s_cmp_lines: list[str] = []
    for label, src in (("without_no_builtins", no_attr_src), ("with_no_builtins", with_attr_src)):
        loop_res[label] = {}
        for target in ("x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu"):
            with tempfile.TemporaryDirectory() as td_str:
                td = Path(td_str)
                run_cmd([
                    "rustc", "--edition", "2024", *REMAP_FLAGS, "--crate-type", "lib",
                    "--target", target, "-C", "opt-level=2",
                    "--emit=llvm-ir,asm", "--out-dir", str(td), str(src)
                ])
                ll_text = next(td.glob("*.ll")).read_text(encoding="utf-8")
                s_text = next(td.glob("*.s")).read_text(encoding="utf-8")
                ll_info = extract_llvm_functions(ll_text)
                s_blocks = extract_asm_blocks(s_text)
                memcpy_ll = ll_info["functions"].get("memcpy", {})
                memset_ll = ll_info["functions"].get("memset", {})
                set_bytes_name = next((k for k in ll_info["functions"] if "set_bytes_helper" in k), "")
                copy_fwd_name = next((k for k in ll_info["functions"] if "copy_forward_helper" in k), "")
                set_bytes_ll = ll_info["functions"].get(set_bytes_name, {})
                copy_fwd_ll = ll_info["functions"].get(copy_fwd_name, {})
                has_no_builtins_attr = any('"no-builtins"' in v for v in memset_ll.get("resolved_attrs", {}).values())
                has_helper_no_builtins_attr = any('"no-builtins"' in v for v in set_bytes_ll.get("resolved_attrs", {}).values())
                memcpy_asm = s_blocks.get("memcpy", [])
                memset_asm = s_blocks.get("memset", [])
                set_bytes_asm = s_blocks.get(set_bytes_name, [])
                copy_fwd_asm = s_blocks.get(copy_fwd_name, [])
                self_recursive_memcpy = any(
                    re.search(r"\b(jmpq?|callq?|b|bl)\b.*\bmemcpy\b", l) for l in copy_fwd_asm + memcpy_asm
                )
                self_recursive_memset = any(
                    re.search(r"\b(jmpq?|callq?|b|bl)\b.*\bmemset\b", l) for l in set_bytes_asm + memset_asm
                )
                loop_res[label][target] = {
                    "memset_llvm_header": memset_ll.get("header", ""),
                    "memcpy_llvm_header": memcpy_ll.get("header", ""),
                    "set_bytes_helper_llvm_header": set_bytes_ll.get("header", ""),
                    "copy_forward_helper_llvm_header": copy_fwd_ll.get("header", ""),
                    "has_llvm_no_builtins_attr": has_no_builtins_attr,
                    "has_helper_llvm_no_builtins_attr": has_helper_no_builtins_attr,
                    "resolved_attrs": set_bytes_ll.get("resolved_attrs", {}),
                    "llvm_calls_llvm_memcpy": "@llvm.memcpy" in ll_text,
                    "llvm_calls_llvm_memset": "@llvm.memset" in ll_text,
                    "asm_self_recursive_memcpy": self_recursive_memcpy,
                    "asm_self_recursive_memset": self_recursive_memset,
                    "set_bytes_helper_asm_excerpt": set_bytes_asm[:25],
                    "copy_forward_helper_asm_excerpt": copy_fwd_asm[:25],
                    "memset_asm_excerpt": memset_asm[:15],
                    "memcpy_asm_excerpt": memcpy_asm[:15],
                }
                if target == "x86_64-unknown-linux-gnu":
                    s_cmp_lines.append(f"# {label} ({target}) - set_bytes_helper + memset")
                    s_cmp_lines.extend(set_bytes_asm[:25])
                    s_cmp_lines.extend(memset_asm[:15])
                    s_cmp_lines.append(f"# {label} ({target}) - copy_forward_helper + memcpy")
                    s_cmp_lines.extend(copy_fwd_asm[:25])
                    s_cmp_lines.extend(memcpy_asm[:15])
                    s_cmp_lines.append("")
    (SPECIMENS_DIR / "memcpy_loop_idiom_hazard.s").write_text("\n".join(s_cmp_lines) + "\n", encoding="utf-8")
    return {"u128_i128_ops": targets_128, "memcpy_loop_idiom": loop_res}


def main() -> None:
    rustc_vv = run_cmd(["rustc", "--version", "--verbose"]).stdout.strip()
    lean_v = run_cmd(["lean", "--version"]).stdout.strip()
    sysroot = Path(run_cmd(["rustc", "--print", "sysroot"]).stdout.strip())

    results = {
        "toolchain": {
            "rustc_version_verbose": rustc_vv,
            "lean_version": lean_v,
        },
        "sysroot_census": scan_sysroot_library(sysroot),
        "constraint_and_options_matrix": probe_matrix(),
        "compile_rejections": probe_compile_rejections(),
        "ce1_lateout_aliasing": probe_ce1(),
        "ce2_redzone_nostack": probe_ce2(),
        "builtins_and_loop_idiom": probe_builtins_and_loop_idiom(),
    }
    RESULTS_PATH.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {RESULTS_PATH} ({RESULTS_PATH.stat().st_size} bytes)")
    print("CE1 O0:", results["ce1_lateout_aliasing"]["opt_O0"]["stdout"])
    print("CE1 O2:", results["ce1_lateout_aliasing"]["opt_O2"]["stdout"])
    print("CE2 O2:", results["ce2_redzone_nostack"]["stdout"])
    print(
        "memset without #![no_builtins] x86_64 self_recursive:",
        results["builtins_and_loop_idiom"]["memcpy_loop_idiom"]["without_no_builtins"]["x86_64-unknown-linux-gnu"]["asm_self_recursive_memset"],
        "| with #![no_builtins]:",
        results["builtins_and_loop_idiom"]["memcpy_loop_idiom"]["with_no_builtins"]["x86_64-unknown-linux-gnu"]["asm_self_recursive_memset"],
        "| memcpy without/with:",
        results["builtins_and_loop_idiom"]["memcpy_loop_idiom"]["without_no_builtins"]["x86_64-unknown-linux-gnu"]["asm_self_recursive_memcpy"],
        results["builtins_and_loop_idiom"]["memcpy_loop_idiom"]["with_no_builtins"]["x86_64-unknown-linux-gnu"]["asm_self_recursive_memcpy"],
    )


if __name__ == "__main__":
    main()
