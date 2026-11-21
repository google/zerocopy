#!/usr/bin/env python3
"""Live rustc, LLVM IR, ELF64 (readelf/objdump), linker GC, and multi-thread TLS probes.

Compiles the standalone specimens under `support/specimens/` inside an ephemeral
`tempfile.TemporaryDirectory()`, parses MIR, LLVM IR, `readelf -SW/-lW/-rW/-sW`, and
`objdump -dr` outputs, executes native PIE binaries (including `SIGSEGV` read-only faults
and multi-thread LIFO TLS destructors), and writes sanitized JSON to
`support/probe_output/probe_results.json`.
"""

from __future__ import annotations

import getpass
import json
import os
from pathlib import Path
import re
import shutil
import socket
import subprocess
import tempfile
from typing import Any


def build_env() -> dict[str, str]:
    env = os.environ.copy()
    home = Path.home()
    extra = [
        str(home / ".cargo" / "bin"),
        str(home / ".local" / "bin"),
        str(home / ".elan" / "bin"),
    ]
    env["PATH"] = ":".join(extra + [env.get("PATH", "")])
    return env


def run(cmd: list[str], env: dict[str, str], cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        capture_output=True,
        text=True,
        timeout=90,
    )


def sanitize_text(text: str, tmp_dir: Path, home_dir: Path) -> str:
    text = text.replace(str(tmp_dir), "<TMP>")
    text = text.replace(str(home_dir), "<HOME>")
    return text


def parse_readelf_sections(stdout: str) -> dict[str, dict[str, str]]:
    out: dict[str, dict[str, str]] = {}
    pat = re.compile(
        r"^\s*\[\s*\d+\]\s+(\S+)\s+(\S+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+\S+\s+(\S*)"
    )
    for line in stdout.splitlines():
        m = pat.match(line)
        if not m:
            continue
        name, sh_type, addr, off, size_hex, flags = m.groups()
        out[name] = {
            "type": sh_type,
            "addr": f"0x{addr}",
            "offset": f"0x{off}",
            "size_bytes": str(int(size_hex, 16)),
            "flags": flags,
        }
    return out


def parse_readelf_symbols(stdout: str, targets: list[str]) -> dict[str, dict[str, str]]:
    out: dict[str, dict[str, str]] = {}
    for line in stdout.splitlines():
        for sym in targets:
            if sym in line.split():
                parts = line.split()
                if len(parts) >= 8:
                    out[sym] = {
                        "value": f"0x{parts[1]}",
                        "size": parts[2],
                        "type": parts[3],
                        "bind": parts[4],
                        "vis": parts[5],
                        "ndx": parts[6],
                        "name": parts[7],
                    }
    return out


def parse_readelf_segments(stdout: str) -> dict[str, dict[str, str]]:
    out: dict[str, dict[str, str]] = {}
    for line in stdout.splitlines():
        stripped = line.strip()
        if stripped.startswith(("TLS ", "GNU_RELRO ", "LOAD ")):
            parts = stripped.split()
            kind = parts[0]
            if kind == "TLS" and len(parts) >= 7:
                out["PT_TLS"] = {
                    "offset": parts[1],
                    "vaddr": parts[2],
                    "paddr": parts[3],
                    "filesz_tdata": str(int(parts[4], 16)),
                    "memsz_total": str(int(parts[5], 16)),
                    "tbss_bytes": str(int(parts[5], 16) - int(parts[4], 16)),
                    "flags": parts[6],
                }
            elif kind == "GNU_RELRO" and len(parts) >= 7:
                out["PT_GNU_RELRO"] = {
                    "offset": parts[1],
                    "vaddr": parts[2],
                    "filesz": str(int(parts[4], 16)),
                    "memsz": str(int(parts[5], 16)),
                    "flags": parts[6],
                }
    return out


def parse_readelf_relocs(stdout: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for line in stdout.splitlines():
        m = re.search(r"\b(R_X86_64_\w+)\b", line)
        if m:
            rtype = m.group(1)
            counts[rtype] = counts.get(rtype, 0) + 1
    return counts


def probe_s1_promote_consts(specimens_dir: Path, tmp: Path, env: dict[str, str]) -> dict[str, Any]:
    s1_dir = tmp / "s1"
    s1_dir.mkdir()
    mir_dir = s1_dir / "mir_dump"
    src = specimens_dir / "s1_promote_consts_mir.rs"
    proc = run(
        [
            "rustc",
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name=s1_promote",
            "-Z",
            "dump-mir=PromoteTemps",
            "-Z",
            f"dump-mir-dir={mir_dir}",
            str(src),
            "-o",
            str(s1_dir / "libs1.rlib"),
        ],
        env,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"s1 compile failed: {proc.stderr}")

    fn_names = [
        "promo_arith_and_index",
        "promo_empty_mut_slice",
        "promo_multiuse_temp",
        "reject_unsafecell",
        "reject_needs_drop",
        "reject_fallible_div_and_oob",
        "reject_nested_oob_index",
        "reject_const_fn_in_fn",
        "SAFE_PROMO_IN_CONST",
    ]
    mir_results: dict[str, Any] = {}
    after_files = sorted(mir_dir.glob("*.PromoteTemps.after.mir"))
    before_files = sorted(mir_dir.glob("*.PromoteTemps.before.mir"))

    for fn in fn_names:
        matched_after = [p for p in after_files if fn in p.name]
        matched_before = [p for p in before_files if fn in p.name]
        after_txt = matched_after[0].read_text() if matched_after else ""
        before_txt = matched_before[0].read_text() if matched_before else ""
        promoted_uses = re.findall(r"const\s+\S+::promoted\[(\d+)\]", after_txt)
        mir_results[fn] = {
            "found_after_mir": bool(matched_after),
            "before_lines": len(before_txt.splitlines()),
            "after_lines": len(after_txt.splitlines()),
            "promoted_ref_count": len(promoted_uses),
            "promoted_indices": promoted_uses,
            "has_runtime_div": bool(re.search(r"\bDiv\(", after_txt)),
            "has_runtime_checked_pos_call": ("checked_pos(" in after_txt),
            "storage_live_before": len(re.findall(r"\bStorageLive\(", before_txt)),
            "storage_live_after": len(re.findall(r"\bStorageLive\(", after_txt)),
        }

    return {
        "compile_rc": proc.returncode,
        "after_mir_file_count": len(after_files),
        "functions": mir_results,
    }


def probe_s2_statics_and_relro(specimens_dir: Path, tmp: Path, env: dict[str, str]) -> dict[str, Any]:
    s2_dir = tmp / "s2"
    s2_dir.mkdir()
    src = specimens_dir / "s2_global_alloc_and_elf_sections.rs"
    syms = [
        "IMMUT_SCALAR_STATIC",
        "ZERO_IMMUT_STATIC",
        "RELRO_PTR_STATIC",
        "MUT_NONZERO_STATIC",
        "MUT_ZERO_STATIC",
        "TLS_NONZERO_CELL",
        "TLS_ZERO_CELL",
        "TLS_ZERO_FREEZE",
    ]

    # 1) LLVM IR + PIC object
    p_pic = run(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-C",
            "relocation-model=pic",
            "--emit=llvm-ir,obj",
            str(src),
            "--out-dir",
            str(s2_dir),
        ],
        env,
    )
    if p_pic.returncode != 0:
        raise RuntimeError(f"s2 pic compile failed: {p_pic.stderr}")

    ll_txt = (s2_dir / "s2_global_alloc_and_elf_sections.ll").read_text()
    ll_globals = {}
    for line in ll_txt.splitlines():
        for sym in syms:
            if line.startswith(f"@{sym} = "):
                ll_globals[sym] = line.strip()
        if "99\\99\\99" in line or "c\"\\99" in line or "splat (i8 -103)" in line:
            ll_globals["PROMOTED_0x99_ARRAY"] = line.strip()

    obj_pic = s2_dir / "s2_global_alloc_and_elf_sections.o"
    pic_sec = parse_readelf_sections(run(["readelf", "-SW", str(obj_pic)], env).stdout)
    pic_sym = parse_readelf_symbols(run(["readelf", "-sW", str(obj_pic)], env).stdout, syms)
    pic_rel = parse_readelf_relocs(run(["readelf", "-rW", str(obj_pic)], env).stdout)

    # 2) Non-PIC (-C relocation-model=static) object comparison for RELRO_PTR_STATIC
    s2_static_dir = tmp / "s2_static"
    s2_static_dir.mkdir()
    p_static = run(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-C",
            "relocation-model=static",
            "--emit=obj",
            str(src),
            "-o",
            str(s2_static_dir / "static.o"),
        ],
        env,
    )
    if p_static.returncode != 0:
        raise RuntimeError(f"s2 static compile failed: {p_static.stderr}")
    static_sec = parse_readelf_sections(run(["readelf", "-SW", str(s2_static_dir / "static.o")], env).stdout)

    # 3) Linked PIE executable (default rust-lld) + GNU ld comparison + SIGSEGV checks
    exe_lld = s2_dir / "s2_lld_bin"
    p_lld = run(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=2",
            str(src),
            "-o",
            str(exe_lld),
        ],
        env,
    )
    if p_lld.returncode != 0:
        raise RuntimeError(f"s2 lld link failed: {p_lld.stderr}")

    lld_segs = parse_readelf_segments(run(["readelf", "-lW", str(exe_lld)], env).stdout)
    lld_secs = parse_readelf_sections(run(["readelf", "-SW", str(exe_lld)], env).stdout)
    lld_dyn_rel = parse_readelf_relocs(run(["readelf", "-rW", str(exe_lld)], env).stdout)

    exe_bfd = s2_dir / "s2_bfd_bin"
    p_bfd = run(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-C",
            "link-self-contained=no",
            "-C",
            "link-arg=-fuse-ld=bfd",
            str(src),
            "-o",
            str(exe_bfd),
        ],
        env,
    )
    bfd_segs = (
        parse_readelf_segments(run(["readelf", "-lW", str(exe_bfd)], env).stdout)
        if p_bfd.returncode == 0
        else {}
    )

    run_normal = run([str(exe_lld), "normal"], env)
    run_write_ro = run([str(exe_lld), "write_rodata"], env)
    run_write_relro = run([str(exe_lld), "write_relro"], env)

    addr_kv = {}
    for tok in run_normal.stdout.strip().split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            addr_kv[k] = v

    return {
        "llvm_ir_globals": ll_globals,
        "pic_obj_sections_selected": {
            k: v
            for k, v in pic_sec.items()
            if any(
                k.startswith(pref)
                for pref in (".rodata", ".data.rel.ro", ".data.", ".bss.", ".tdata.", ".tbss.")
            )
        },
        "pic_obj_symbols": pic_sym,
        "pic_obj_reloc_counts": pic_rel,
        "static_model_relro_section": {
            k: v for k, v in static_sec.items() if "RELRO_PTR_STATIC" in k
        },
        "linked_lld_segments": lld_segs,
        "linked_lld_sections_key": {
            k: lld_secs[k]
            for k in (".rodata", ".data.rel.ro", ".data", ".bss", ".tdata", ".tbss")
            if k in lld_secs
        },
        "linked_lld_dyn_relocs": lld_dyn_rel,
        "linked_gnu_bfd_rc": p_bfd.returncode,
        "linked_gnu_bfd_segments": bfd_segs,
        "runtime_modes": {
            "normal_rc": run_normal.returncode,
            "normal_addresses_runtime": addr_kv,
            "write_rodata_rc": run_write_ro.returncode,
            "write_relro_rc": run_write_relro.returncode,
        },
    }


def extract_fn_disasm(objdump_out: str, fn_name: str) -> list[str]:
    lines = objdump_out.splitlines()
    captured: list[str] = []
    inside = False
    for line in lines:
        if f"<{fn_name}>:" in line:
            inside = True
            captured.append(line.strip())
            continue
        if inside:
            if not line.strip():
                break
            captured.append(line.strip())
    return captured


def probe_s3_tls_models(specimens_dir: Path, tmp: Path, env: dict[str, str]) -> dict[str, Any]:
    s3_dir = tmp / "s3"
    s3_dir.mkdir()
    src = specimens_dir / "s3_tls_models_x86_64.rs"
    models = ["global-dynamic", "local-dynamic", "initial-exec", "local-exec"]
    model_results: dict[str, Any] = {}

    for model in models:
        mdir = s3_dir / model
        mdir.mkdir()
        # 1) Compile as cdylib .o (not dso_local -> preserves all 4 raw ELF TLS models)
        cdylib_obj_dir = mdir / "cdylib_obj"
        cdylib_obj_dir.mkdir()
        p_cdylib_obj = run(
            [
                "rustc",
                "--edition=2021",
                "--crate-type=cdylib",
                "--cfg",
                "feature_cdylib",
                "-C",
                "opt-level=2",
                "-C",
                "relocation-model=pic",
                "-Z",
                f"tls-model={model}",
                "--emit=llvm-ir,obj",
                str(src),
                "--out-dir",
                str(cdylib_obj_dir),
            ],
            env,
        )
        if p_cdylib_obj.returncode != 0:
            raise RuntimeError(f"s3 cdylib obj ({model}) failed: {p_cdylib_obj.stderr}")

        cdylib_obj_file = cdylib_obj_dir / "s3_tls_models_x86_64.o"
        cdylib_obj_relocs = parse_readelf_relocs(run(["readelf", "-rW", str(cdylib_obj_file)], env).stdout)
        cdylib_obj_disasm = extract_fn_disasm(
            run(["objdump", "-dr", str(cdylib_obj_file)], env).stdout, "read_tls_pair"
        )

        # 2) Compile as bin .o (dso_local -> shows rustc/LLVM clamping GD/LD to IE)
        p_obj = run(
            [
                "rustc",
                "--edition=2021",
                "-C",
                "opt-level=2",
                "-C",
                "relocation-model=pic",
                "-Z",
                f"tls-model={model}",
                "--emit=llvm-ir,obj",
                str(src),
                "--out-dir",
                str(mdir),
            ],
            env,
        )
        if p_obj.returncode != 0:
            raise RuntimeError(f"s3 obj ({model}) failed: {p_obj.stderr}")

        obj_file = mdir / "s3_tls_models_x86_64.o"
        relocs = parse_readelf_relocs(run(["readelf", "-rW", str(obj_file)], env).stdout)
        disasm = run(["objdump", "-dr", str(obj_file)], env).stdout
        fn_disasm = extract_fn_disasm(disasm, "read_tls_pair")
        ll_txt = (mdir / "s3_tls_models_x86_64.ll").read_text()
        ll_tls_decls = [
            ln.strip()
            for ln in ll_txt.splitlines()
            if ln.startswith(("@TLS_MODEL_A", "@TLS_MODEL_B"))
        ]

        # 3) Link as PIE executable and check TLS relaxation + runtime output
        exe = mdir / "tls_exe"
        p_exe = run(
            [
                "rustc",
                "--edition=2021",
                "-C",
                "opt-level=2",
                "-Z",
                f"tls-model={model}",
                str(src),
                "-o",
                str(exe),
            ],
            env,
        )
        exe_rc = run([str(exe)], env) if p_exe.returncode == 0 else None
        exe_disasm = extract_fn_disasm(run(["objdump", "-d", str(exe)], env).stdout, "read_tls_pair") if p_exe.returncode == 0 else []
        exe_segs = parse_readelf_segments(run(["readelf", "-lW", str(exe)], env).stdout) if p_exe.returncode == 0 else {}

        # 4) Link as cdylib to test local-exec rejection under -shared
        so_path = mdir / "libtls_probe.so"
        p_cdylib = run(
            [
                "rustc",
                "--edition=2021",
                "--crate-type=cdylib",
                "--cfg",
                "feature_cdylib",
                "-C",
                "opt-level=2",
                "-Z",
                f"tls-model={model}",
                str(src),
                "-o",
                str(so_path),
            ],
            env,
        )
        cdylib_dyn_rel = (
            parse_readelf_relocs(run(["readelf", "-rW", str(so_path)], env).stdout)
            if p_cdylib.returncode == 0
            else {}
        )

        model_results[model] = {
            "cdylib_obj_rc": p_cdylib_obj.returncode,
            "cdylib_obj_reloc_counts": cdylib_obj_relocs,
            "cdylib_obj_read_tls_pair_disasm": cdylib_obj_disasm,
            "bin_obj_rc": p_obj.returncode,
            "llvm_ir_tls_decls": ll_tls_decls,
            "bin_obj_reloc_counts": relocs,
            "bin_obj_read_tls_pair_disasm": fn_disasm,
            "pie_link_rc": p_exe.returncode,
            "pie_exec_rc": exe_rc.returncode if exe_rc else None,
            "pie_exec_stdout": exe_rc.stdout.strip() if exe_rc else None,
            "pie_pt_tls": exe_segs.get("PT_TLS", {}),
            "pie_read_tls_pair_disasm": exe_disasm,
            "cdylib_link_rc": p_cdylib.returncode,
            "cdylib_dyn_relocs": cdylib_dyn_rel,
            "cdylib_error_excerpt": (
                sanitize_text(p_cdylib.stderr.strip()[:600], tmp, Path.home())
                if p_cdylib.returncode != 0
                else ""
            ),
        }

    return model_results


def probe_s4_used_and_init_array(specimens_dir: Path, tmp: Path, env: dict[str, str]) -> dict[str, Any]:
    s4_dir = tmp / "s4"
    s4_dir.mkdir()
    src = specimens_dir / "s4_used_compiler_vs_linker_and_init_array.rs"

    p_ir_obj = run(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=2",
            "--emit=llvm-ir,obj",
            str(src),
            "--out-dir",
            str(s4_dir),
        ],
        env,
    )
    if p_ir_obj.returncode != 0:
        raise RuntimeError(f"s4 ir/obj failed: {p_ir_obj.stderr}")

    ll_txt = (s4_dir / "s4_used_compiler_vs_linker_and_init_array.ll").read_text()
    ll_used_lines = [
        ln.strip()
        for ln in ll_txt.splitlines()
        if any(
            tok in ln
            for tok in ("@llvm.used", "@llvm.compiler.used", "USED_COMP", "USED_LINK", "USED_BARE", "INIT_ARRAY_CTOR", "PLAIN_UNUSED")
        )
    ]

    obj_secs = parse_readelf_sections(
        run(["readelf", "-SW", str(s4_dir / "s4_used_compiler_vs_linker_and_init_array.o")], env).stdout
    )
    obj_custom = {
        k: v
        for k, v in obj_secs.items()
        if k.startswith((".custom_", ".init_array"))
    }

    linkers = {
        "rust_lld": ["-C", "link-arg=-Wl,--gc-sections"],
        "gnu_ld": ["-C", "link-self-contained=no", "-C", "link-arg=-fuse-ld=bfd", "-C", "link-arg=-Wl,--gc-sections"],
    }
    linked_results: dict[str, Any] = {}
    for l_name, extra_args in linkers.items():
        exe = s4_dir / f"s4_{l_name}"
        p_link = run(
            [
                "rustc",
                "--edition=2021",
                "-C",
                "opt-level=2",
                *extra_args,
                str(src),
                "-o",
                str(exe),
            ],
            env,
        )
        if p_link.returncode != 0:
            raise RuntimeError(f"s4 link ({l_name}) failed: {p_link.stderr}")
        l_secs = parse_readelf_sections(run(["readelf", "-SW", str(exe)], env).stdout)
        l_syms = run(["readelf", "-sW", str(exe)], env).stdout
        exec_p = run([str(exe)], env)
        linked_results[l_name] = {
            "link_rc": p_link.returncode,
            "exec_rc": exec_p.returncode,
            "exec_stdout": exec_p.stdout.strip(),
            "sections_present": {
                sec: (sec in l_secs) for sec in (".custom_plain", ".custom_comp", ".custom_link", ".custom_bare", ".init_array")
            },
            "symbols_present": {
                sym: (sym in l_syms) for sym in ("PLAIN_UNUSED", "USED_COMP", "USED_LINK", "USED_BARE", "INIT_ARRAY_CTOR")
            },
            "init_array_sec": l_secs.get(".init_array", {}),
        }

    # Test staticlib archive boundary: an unreferenced `.rlib` member is NOT pulled from archive
    # even with `#[used(linker)]`, unless a symbol in that TU is referenced or `--whole-archive` is used.
    arch_dir = s4_dir / "arch"
    arch_dir.mkdir()
    lib_src = arch_dir / "dep_ctor.rs"
    lib_src.write_text(
        "#![crate_type = \"rlib\"]\n"
        "use std::sync::atomic::{AtomicU64, Ordering};\n"
        "pub static DEP_FLAG: AtomicU64 = AtomicU64::new(0);\n"
        "#[inline(never)] pub fn touch_dep() -> u64 { DEP_FLAG.load(Ordering::SeqCst) }\n"
        "#[inline(never)] unsafe extern \"C\" fn dep_ctor() { DEP_FLAG.store(0x77, Ordering::SeqCst); }\n"
        "#[used] #[link_section = \".init_array\"]\n"
        "#[no_mangle] static DEP_INIT: unsafe extern \"C\" fn() = dep_ctor;\n",
        encoding="utf-8",
    )
    main_unref = arch_dir / "main_unreferenced.rs"
    main_unref.write_text(
        "fn main() { println!(\"UNREF_RAN\"); }\n",
        encoding="utf-8",
    )
    main_ref = arch_dir / "main_referenced.rs"
    main_ref.write_text(
        "extern crate dep_ctor;\n"
        "fn main() { println!(\"DEP_FLAG=0x{:x}\", dep_ctor::touch_dep()); assert_eq!(dep_ctor::touch_dep(), 0x77); }\n",
        encoding="utf-8",
    )
    run(["rustc", "--edition=2021", "-C", "opt-level=2", "--crate-type=rlib", str(lib_src), "-o", str(arch_dir / "libdep_ctor.rlib")], env)
    exe_unref = arch_dir / "exe_unref"
    run(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=2",
            "--extern",
            f"dep_ctor={arch_dir / 'libdep_ctor.rlib'}",
            "-L",
            str(arch_dir),
            "-C",
            "link-arg=-Wl,--gc-sections",
            str(main_unref),
            "-o",
            str(exe_unref),
        ],
        env,
    )
    exe_ref = arch_dir / "exe_ref"
    run(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=2",
            "--extern",
            f"dep_ctor={arch_dir / 'libdep_ctor.rlib'}",
            "-L",
            str(arch_dir),
            "-C",
            "link-arg=-Wl,--gc-sections",
            str(main_ref),
            "-o",
            str(exe_ref),
        ],
        env,
    )
    unref_syms = run(["readelf", "-sW", str(exe_unref)], env).stdout
    ref_exec = run([str(exe_ref)], env)

    return {
        "llvm_ir_lines": ll_used_lines,
        "obj_sections": obj_custom,
        "linked_by_linker": linked_results,
        "rlib_member_extraction_boundary": {
            "unreferenced_rlib_contains_DEP_INIT": "DEP_INIT" in unref_syms,
            "referenced_rlib_exec_rc": ref_exec.returncode,
            "referenced_rlib_exec_stdout": ref_exec.stdout.strip(),
        },
    }


def probe_s5_tls_multithread_and_dtors(specimens_dir: Path, tmp: Path, env: dict[str, str]) -> dict[str, Any]:
    s5_dir = tmp / "s5"
    s5_dir.mkdir()
    src = specimens_dir / "s5_tls_multithread_and_lifo_drop_order.rs"
    exe = s5_dir / "s5_tls_mt"
    p_comp = run(["rustc", "--edition=2021", "-C", "opt-level=2", str(src), "-o", str(exe)], env)
    if p_comp.returncode != 0:
        raise RuntimeError(f"s5 compile failed: {p_comp.stderr}")

    p_exec = run([str(exe)], env)
    if p_exec.returncode != 0:
        raise RuntimeError(f"s5 exec failed ({p_exec.returncode}): {p_exec.stdout} {p_exec.stderr}")

    segs = parse_readelf_segments(run(["readelf", "-lW", str(exe)], env).stdout)
    dyn_syms = run(["readelf", "-sW", str(exe)], env).stdout
    has_cxa_thread_atexit = "__cxa_thread_atexit_impl" in dyn_syms

    return {
        "compile_rc": p_comp.returncode,
        "exec_rc": p_exec.returncode,
        "exec_stdout": p_exec.stdout.strip(),
        "pt_tls_segment": segs.get("PT_TLS", {}),
        "uses_weak_cxa_thread_atexit_impl_sym": has_cxa_thread_atexit,
    }


def main() -> int:
    support_dir = Path(__file__).resolve().parent
    specimens_dir = support_dir / "specimens"
    out_path = support_dir / "probe_output" / "probe_results.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    env = build_env()

    rustc_ver = run(["rustc", "-vV"], env).stdout.strip()
    readelf_ver = run(["readelf", "--version"], env).stdout.splitlines()[0].strip()
    ld_ver = run(["ld", "--version"], env).stdout.splitlines()[0].strip()
    tls_models_out = run(["rustc", "--print", "tls-models"], env).stdout.strip()

    with tempfile.TemporaryDirectory(prefix="probe_statics_tls_") as tmp_raw:
        tmp = Path(tmp_raw)
        s1 = probe_s1_promote_consts(specimens_dir, tmp, env)
        s2 = probe_s2_statics_and_relro(specimens_dir, tmp, env)
        s3 = probe_s3_tls_models(specimens_dir, tmp, env)
        s4 = probe_s4_used_and_init_array(specimens_dir, tmp, env)
        s5 = probe_s5_tls_multithread_and_dtors(specimens_dir, tmp, env)

    payload = {
        "toolchain": {
            "rustc_vV": rustc_ver,
            "readelf_version": readelf_ver,
            "gnu_ld_version": ld_ver,
            "rustc_print_tls_models": tls_models_out,
        },
        "s1_promote_consts_mir": s1,
        "s2_global_alloc_and_elf_sections": s2,
        "s3_tls_models_x86_64": s3,
        "s4_used_compiler_vs_linker_and_init_array": s4,
        "s5_tls_multithread_and_lifo_drop_order": s5,
    }

    serialized = json.dumps(payload, indent=2) + "\n"
    sysroot = run(["rustc", "--print", "sysroot"], env).stdout.strip()
    runtime_secrets = [s for s in (str(Path.home()), sysroot, "/tmp/", getpass.getuser(), socket.gethostname()) if s]
    for forbidden in runtime_secrets:
        if forbidden in serialized:
            idx = serialized.find(forbidden)
            snippet = serialized[max(0, idx - 60) : idx + 80]
            raise RuntimeError(f"sanitization check failed: found host-local token near {snippet!r}")

    out_path.write_text(serialized, encoding="utf-8")
    print(f"Wrote {out_path} ({len(serialized)} bytes), all probes passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
