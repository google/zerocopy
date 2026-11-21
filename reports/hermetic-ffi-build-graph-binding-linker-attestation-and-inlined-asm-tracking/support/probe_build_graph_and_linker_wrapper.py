#!/usr/bin/env python3
"""Executable probes for Cargo build.rs provenance, verify-vs-build divergence,
rlib native-library bundling (+bundle/-bundle/+whole-archive), TOCTOU mutation,
and hermetic -C linker= wrapper attestation (--dependency-file, --trace, -Map,
@response-file expansion, and SHT_LLVM_DEPENDENT_LIBRARIES smuggling).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def run(cmd: list[str], cwd: pathlib.Path | None = None, env: dict[str, str] | None = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=merged_env,
        text=True,
        capture_output=True,
        check=check,
    )


def compile_c_archive(c_src: str, lib_name: str, out_dir: pathlib.Path, obj_name: str = "unit.o") -> pathlib.Path:
    c_path = out_dir / f"{lib_name}.c"
    o_path = out_dir / obj_name
    a_path = out_dir / f"lib{lib_name}.a"
    c_path.write_text(c_src)
    run(["gcc", "-O2", "-fPIC", "-c", str(c_path), "-o", str(o_path)])
    if a_path.exists():
        a_path.unlink()
    run(["ar", "rcs", str(a_path), str(o_path)])
    return a_path


def probe_1a_cargo_build_rs_divergence(toolchain: str) -> dict:
    """Demonstrates:
    1) `cargo check` passes --emit=dep-info,metadata and never links native libs,
       succeeding even when build.rs emits a nonexistent static library.
    2) A hostile/buggy build.rs inspecting RUSTC_WRAPPER or OPT_LEVEL/PROFILE
       emits benign C code during wrapper-based verification vs malicious C code
       during standard `cargo build` from the identical Rust source tree.
    """
    with tempfile.TemporaryDirectory(prefix="probe1a_") as td:
        root = pathlib.Path(td)
        src = root / "src"
        src.mkdir()

        (root / "Cargo.toml").write_text(
            '[package]\nname = "diverge_demo"\nversion = "0.1.0"\nedition = "2021"\n'
        )
        (src / "main.rs").write_text(
            'extern "C" { fn native_policy_val() -> i32; }\n'
            'fn main() {\n'
            '    let v = unsafe { native_policy_val() };\n'
            '    println!("VAL={v}");\n'
            '}\n'
        )
        # First test: build.rs referencing a nonexistent lib during `cargo check`
        (root / "build.rs").write_text(
            'fn main() {\n'
            '    println!("cargo::rustc-link-lib=static=nonexistent_ghost_lib");\n'
            '}\n'
        )
        chk_missing = run(["cargo", f"+{toolchain}", "check", "--quiet"], cwd=root, check=False)
        bld_missing = run(["cargo", f"+{toolchain}", "build", "--quiet"], cwd=root, check=False)

        # Second test: build.rs diverging based on RUSTC_WRAPPER (and OPT_LEVEL)
        (root / "build.rs").write_text(
            'use std::env;\n'
            'use std::fs;\n'
            'use std::path::PathBuf;\n'
            'use std::process::Command;\n'
            'fn main() {\n'
            '    println!("cargo::rerun-if-env-changed=RUSTC_WRAPPER");\n'
            '    println!("cargo::rerun-if-env-changed=VERIFY_MODE");\n'
            '    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());\n'
            '    let has_wrapper = env::var("RUSTC_WRAPPER").map(|v| !v.is_empty()).unwrap_or(false);\n'
            '    let opt = env::var("OPT_LEVEL").unwrap_or_default();\n'
            '    // Benign return value (42) when invoked under a RUSTC_WRAPPER or opt_level=="0",\n'
            '    // divergent value (666) under release without wrapper (or vice versa).\n'
            '    let ret_val = if has_wrapper { 42 } else if opt != "0" { 999 } else { 666 };\n'
            '    let c_file = out_dir.join("policy.c");\n'
            '    let o_file = out_dir.join("policy.o");\n'
            '    let a_file = out_dir.join("libpolicy.a");\n'
            '    fs::write(&c_file, format!("int native_policy_val(void) {{ return {ret_val}; }}\\n")).unwrap();\n'
            '    assert!(Command::new("gcc").args(["-O2", "-c"]).arg(&c_file).arg("-o").arg(&o_file).status().unwrap().success());\n'
            '    let _ = fs::remove_file(&a_file);\n'
            '    assert!(Command::new("ar").args(["rcs"]).arg(&a_file).arg(&o_file).status().unwrap().success());\n'
            '    println!("cargo::rustc-link-search=native={}", out_dir.display());\n'
            '    println!("cargo::rustc-link-lib=static=policy");\n'
            '}\n'
        )

        # Create a trivial pass-through RUSTC_WRAPPER script simulating a verifier hook
        wrapper = root / "verify_wrapper.sh"
        wrapper.write_text("#!/bin/sh\nexec \"$@\"\n")
        wrapper.chmod(0o755)

        # Build 1: with RUSTC_WRAPPER set (e.g., verifier / cargo-clippy / custom driver)
        b_wrap = run(
            ["cargo", f"+{toolchain}", "build", "--quiet"],
            cwd=root,
            env={"RUSTC_WRAPPER": str(wrapper)},
        )
        exe_dbg = root / "target" / "debug" / "diverge_demo"
        out_wrap = run([str(exe_dbg)]).stdout.strip()
        sha_wrap = sha256_file(exe_dbg)

        # Build 2: plain cargo build (no wrapper)
        b_plain = run(
            ["cargo", f"+{toolchain}", "build", "--quiet"],
            cwd=root,
            env={"RUSTC_WRAPPER": ""},
        )
        out_plain = run([str(exe_dbg)]).stdout.strip()
        sha_plain = sha256_file(exe_dbg)

        # Build 3: cargo build --release (OPT_LEVEL=3, PROFILE=release)
        b_rel = run(
            ["cargo", f"+{toolchain}", "build", "--release", "--quiet"],
            cwd=root,
            env={"RUSTC_WRAPPER": ""},
        )
        exe_rel = root / "target" / "release" / "diverge_demo"
        out_rel = run([str(exe_rel)]).stdout.strip()

        return {
            "toolchain": toolchain,
            "cargo_check_with_missing_native_lib_rc": chk_missing.returncode,
            "cargo_build_with_missing_native_lib_rc": bld_missing.returncode,
            "cargo_build_missing_stderr_excerpt": bld_missing.stderr.strip().splitlines()[-3:],
            "wrapper_build_output": out_wrap,
            "wrapper_build_exe_sha256": sha_wrap,
            "plain_debug_build_output": out_plain,
            "plain_debug_exe_sha256": sha_plain,
            "release_build_output": out_rel,
            "diverged_under_identical_rust_source": (out_wrap != out_plain) and (out_plain != out_rel),
        }


def probe_1b_rlib_bundling_and_toctou(toolchain: str) -> dict:
    """Compares rlib archive layouts under:
    - static=+bundle (default): native .o unpacked directly into .rlib
    - static=+bundle,+whole-archive: native .a stored as .bundled_lib wrapper object
    - static=-bundle: native .a NOT stored in .rlib -> downstream TOCTOU mutation
      changes final binary without recompiling upstream .rlib!
    """
    with tempfile.TemporaryDirectory(prefix="probe1b_") as td:
        root = pathlib.Path(td)
        nat_dir = root / "native"
        nat_dir.mkdir()
        a_path = compile_c_archive("int k_val(void) { return 11; }\n", "myffi", nat_dir, "myffi_impl.o")
        sha_v1 = sha256_file(a_path)

        lib_rs = root / "up.rs"
        lib_rs.write_text(
            'extern "C" { fn k_val() -> i32; }\n'
            'pub fn get_k() -> i32 { unsafe { k_val() } }\n'
        )
        main_rs = root / "app.rs"
        main_rs.write_text('fn main() { println!("K={}", up::get_k()); }\n')

        modes = {}
        for label, link_spec in [
            ("default_bundle", "static=myffi"),
            ("bundle_whole_archive", "static:+bundle,+whole-archive=myffi"),
            ("no_bundle", "static:-bundle=myffi"),
        ]:
            mdir = root / label
            mdir.mkdir()
            rlib = mdir / "libup.rlib"
            run([
                "rustc", f"+{toolchain}", "--crate-type=rlib", "--crate-name=up",
                "-L", f"native={nat_dir}", "-l", link_spec,
                str(lib_rs), "-o", str(rlib),
            ])
            members = run(["ar", "t", str(rlib)]).stdout.strip().splitlines()
            modes[label] = {
                "rlib_members": members,
                "contains_unpacked_native_o": "myffi_impl.o" in members,
                "contains_packed_archive_wrapper": "libmyffi.a" in members,
            }

        # Now mutate libmyffi.a on disk to return 77 WITHOUT recompiling any rlib!
        compile_c_archive("int k_val(void) { return 77; }\n", "myffi", nat_dir, "myffi_impl.o")
        sha_v2 = sha256_file(a_path)

        downstream_results = {}
        for label in ("default_bundle", "bundle_whole_archive", "no_bundle"):
            mdir = root / label
            rlib = mdir / "libup.rlib"
            exe = mdir / "app"
            run([
                "rustc", f"+{toolchain}", "--crate-type=bin",
                "--extern", f"up={rlib}",
                "-L", f"native={nat_dir}",
                str(main_rs), "-o", str(exe),
            ])
            downstream_results[label] = run([str(exe)]).stdout.strip()

        return {
            "toolchain": toolchain,
            "native_a_sha256_v1": sha_v1,
            "native_a_sha256_v2": sha_v2,
            "rlib_layouts": modes,
            "downstream_after_on_disk_mutation": downstream_results,
        }


LINKER_WRAPPER_SCRIPT = r'''#!/usr/bin/env python3
"""Hermetic attestation linker wrapper for rustc -C linker=<wrapper>.
Expands @response files, injects --dependency-file, --trace, and -Map,
optionally adds --no-dependent-libraries, executes the real linker driver,
and writes a JSON attestation manifest with SHA-256 digests of every resolved
input and the linked output artifact.
"""
import hashlib, json, os, pathlib, shlex, subprocess, sys

def sha256_file(p: pathlib.Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()

def expand_args(argv):
    out = []
    rsp_files = []
    for a in argv:
        if a.startswith("@") and len(a) > 1:
            p = pathlib.Path(a[1:])
            if p.is_file():
                rsp_files.append(str(p))
                text = p.read_text(encoding="utf-8", errors="replace")
                # POSIX response file tokens
                out.extend(expand_args(shlex.split(text))[0])
                continue
        out.append(a)
    return out, rsp_files

def parse_depfile(path: pathlib.Path):
    if not path.is_file():
        return []
    raw = path.read_text(encoding="utf-8", errors="replace")
    # Unwrap makefile line continuations
    raw = raw.replace("\\\n", " ")
    if ":" in raw:
        _, rhs = raw.split(":", 1)
    else:
        rhs = raw
    # Handle escaped spaces
    deps = []
    cur = []
    i = 0
    while i < len(rhs):
        c = rhs[i]
        if c == "\\" and i + 1 < len(rhs) and rhs[i + 1] == " ":
            cur.append(" ")
            i += 2
        elif c.isspace():
            if cur:
                deps.append("".join(cur))
                cur = []
            i += 1
        else:
            cur.append(c)
            i += 1
    if cur:
        deps.append("".join(cur))
    return deps

def main():
    real_linker = os.environ["HERMETIC_REAL_LINKER"]
    manifest_out = pathlib.Path(os.environ["HERMETIC_MANIFEST_OUT"])
    dep_out = pathlib.Path(os.environ["HERMETIC_DEPFILE_OUT"])
    map_out = pathlib.Path(os.environ["HERMETIC_MAP_OUT"])
    disable_deplibs = os.environ.get("HERMETIC_NO_DEPLIBS", "0") == "1"

    raw_args = sys.argv[1:]
    expanded_args, rsp_files = expand_args(raw_args)

    # Identify output path (-o <path>)
    out_path = None
    for i, a in enumerate(expanded_args):
        if a == "-o" and i + 1 < len(expanded_args):
            out_path = expanded_args[i + 1]
        elif a.startswith("-o") and len(a) > 2:
            out_path = a[2:]

    injected = [
        f"-Wl,--dependency-file={dep_out}",
        "-Wl,--trace",
        f"-Wl,-Map={map_out}",
    ]
    if disable_deplibs:
        injected.append("-Wl,--no-dependent-libraries")

    # Pre-link hash snapshot of direct file paths in argv
    argv_files_pre = {}
    for a in expanded_args:
        if not a.startswith("-") and os.path.isfile(a):
            p = pathlib.Path(a)
            st = p.stat()
            argv_files_pre[a] = {"sha256": sha256_file(p), "ino": st.st_ino, "size": st.st_size}

    cmd = [real_linker] + raw_args + injected
    proc = subprocess.run(cmd, text=True, capture_output=True)

    # Parse depfile and trace lines
    deps = parse_depfile(dep_out)
    dep_digests = {}
    for d in deps:
        p = pathlib.Path(d)
        if p.is_file():
            st = p.stat()
            dep_digests[d] = {"sha256": sha256_file(p), "ino": st.st_ino, "size": st.st_size}

    # Check pre/post invariance on direct argv inputs
    toctou_mismatches = []
    for a, pre in argv_files_pre.items():
        p = pathlib.Path(a)
        if not p.is_file():
            toctou_mismatches.append({"path": a, "reason": "vanished"})
        else:
            post_sha = sha256_file(p)
            if post_sha != pre["sha256"]:
                toctou_mismatches.append({"path": a, "pre": pre["sha256"], "post": post_sha})

    trace_lines = [ln for ln in proc.stdout.splitlines() if ln.strip()]
    out_sha = sha256_file(pathlib.Path(out_path)) if (out_path and os.path.isfile(out_path)) else None

    manifest = {
        "real_linker": real_linker,
        "returncode": proc.returncode,
        "response_files_expanded": rsp_files,
        "raw_argv_count": len(raw_args),
        "expanded_argv_count": len(expanded_args),
        "output_path": out_path,
        "output_sha256": out_sha,
        "depfile_entries_count": len(deps),
        "depfile_entries": deps,
        "depfile_digests_count": len(dep_digests),
        "trace_lines_count": len(trace_lines),
        "trace_lines_all": trace_lines,
        "trace_sample_archive_members": [ln for ln in trace_lines if "(" in ln and ")" in ln][:15],
        "trace_sample_first": trace_lines[:10],
        "map_file_bytes": map_out.stat().st_size if map_out.is_file() else 0,
        "toctou_mismatches": toctou_mismatches,
        "stderr": proc.stderr.strip(),
    }
    manifest_out.write_text(json.dumps(manifest, indent=2))
    # Forward stderr to rustc (don't pollute stdout unless linker failed)
    if proc.stderr:
        sys.stderr.write(proc.stderr)
    sys.exit(proc.returncode)

if __name__ == "__main__":
    main()
'''


def probe_1c_linker_wrapper_and_deplibs_smuggling(toolchain: str) -> dict:
    """Tests hermetic -C linker= wrapper across:
    1) Default rust-lld (gnu-lld-cc)
    2) System GNU ld.bfd (-C link-arg=-fuse-ld=bfd)
    3) Forced @response-file input passed via -C link-arg=@rsp
    4) SHT_LLVM_DEPENDENT_LIBRARIES (.deplibs) smuggling in rust-lld (default ON)
       vs blocked by -Wl,--no-dependent-libraries.
    """
    with tempfile.TemporaryDirectory(prefix="probe1c_") as td:
        root = pathlib.Path(td)
        wrapper = root / "hermetic_ld.py"
        wrapper.write_text(LINKER_WRAPPER_SCRIPT)
        wrapper.chmod(0o755)

        nat_dir = root / "native"
        nat_dir.mkdir()
        compile_c_archive("int add_one(int x) { return x + 1; }\n", "helper", nat_dir, "helper.o")

        # Also build a "smuggled" library that will NOT appear on rustc/linker argv
        smug_dir = root / "smuggled"
        smug_dir.mkdir()
        smug_a = compile_c_archive(
            'extern int smuggled_ran;\n'
            'int smuggled_val(void) { return 777; }\n',
            "secret_dep",
            smug_dir,
            "secret_dep.o",
        )
        # Build an object file containing SHT_LLVM_DEPENDENT_LIBRARIES referencing snug_a by absolute path!
        deplib_s = root / "deplib_carrier.s"
        deplib_o = root / "deplib_carrier.o"
        deplib_s.write_text(
            '.text\n'
            '.globl carrier_fn\n'
            '.type carrier_fn, @function\n'
            'carrier_fn:\n'
            '    jmp smuggled_val@PLT\n'
            '.section .deplibs,"",@llvm_dependent_libraries\n'
            f'.asciz "{smug_a}"\n'
            '.section .note.GNU-stack,"",@progbits\n'
        )
        # Assemble with clang-19 (LLVM MC understands @llvm_dependent_libraries; fallback to numeric 0x6fff4c04)
        asm_res = run(["clang-19", "-c", str(deplib_s), "-o", str(deplib_o)], check=False)
        if asm_res.returncode != 0:
            deplib_s.write_text(
                '.text\n'
                '.globl carrier_fn\n'
                '.type carrier_fn, @function\n'
                'carrier_fn:\n'
                '    jmp smuggled_val@PLT\n'
                '.section .deplibs,"",0x6fff4c04\n'
                f'.asciz "{smug_a}"\n'
                '.section .note.GNU-stack,"",@progbits\n'
            )
            run(["as", str(deplib_s), "-o", str(deplib_o)])

        app_rs = root / "app.rs"
        app_rs.write_text(
            'extern "C" { fn add_one(x: i32) -> i32; }\n'
            'fn main() { println!("OUT={}", unsafe { add_one(41) }); }\n'
        )

        # Response file test
        rsp_path = root / "extra.rsp"
        rsp_path.write_text("-Wl,--as-needed\n")

        sysroot = run(["rustc", f"+{toolchain}", "--print", "sysroot"]).stdout.strip()

        def norm(s: str) -> str:
            return s.replace(sysroot, "<RUSTC_SYSROOT>").replace(str(root), "<TMPDIR>")

        results = {}
        for mode_name, extra_rustc_args in [
            ("rust_lld_default", ["-C", f"link-arg=@{rsp_path}"]),
            ("gnu_ld_bfd", ["-C", "link-arg=-fuse-ld=bfd", "-C", f"link-arg=@{rsp_path}"]),
        ]:
            mdir = root / mode_name
            mdir.mkdir()
            manifest_path = mdir / "manifest.json"
            dep_path = mdir / "link.d"
            map_path = mdir / "link.map"
            exe = mdir / "app"
            run(
                [
                    "rustc", f"+{toolchain}", "-O",
                    "-C", f"linker={wrapper}",
                    "-L", f"native={nat_dir}", "-l", "static=helper",
                    *extra_rustc_args,
                    str(app_rs), "-o", str(exe),
                ],
                env={
                    "HERMETIC_REAL_LINKER": "/usr/bin/cc",
                    "HERMETIC_MANIFEST_OUT": str(manifest_path),
                    "HERMETIC_DEPFILE_OUT": str(dep_path),
                    "HERMETIC_MAP_OUT": str(map_path),
                },
            )
            manifest = json.loads(manifest_path.read_text())
            out = run([str(exe)]).stdout.strip()
            has_libhelper_in_dep = any("libhelper.a" in d for d in manifest["depfile_entries"])
            has_crt_in_dep = any("crt1.o" in d or "Scrt1.o" in d for d in manifest["depfile_entries"])
            results[mode_name] = {
                "run_output": out,
                "response_files_expanded": [norm(x) for x in manifest["response_files_expanded"]],
                "depfile_entries_count": manifest["depfile_entries_count"],
                "depfile_contains_libhelper_a": has_libhelper_in_dep,
                "depfile_contains_crt_startup": has_crt_in_dep,
                "trace_lines_count": manifest["trace_lines_count"],
                "trace_sample_archive_members": [norm(x) for x in manifest["trace_sample_archive_members"][:6]],
                "trace_sample_first": [norm(x) for x in manifest["trace_sample_first"][:6]],
                "map_file_bytes": manifest["map_file_bytes"],
                "toctou_mismatches": manifest["toctou_mismatches"],
            }

        # Now test SHT_LLVM_DEPENDENT_LIBRARIES smuggling under rust-lld (default vs --no-dependent-libraries)
        smug_rs = root / "smug_app.rs"
        smug_rs.write_text(
            'extern "C" { fn carrier_fn() -> i32; }\n'
            'fn main() { println!("SMUG={}", unsafe { carrier_fn() }); }\n'
        )
        smug_results = {}
        for mode_name, no_deplibs in [("lld_default_allows_deplibs", "0"), ("lld_no_dependent_libraries", "1")]:
            mdir = root / mode_name
            mdir.mkdir()
            manifest_path = mdir / "manifest.json"
            dep_path = mdir / "link.d"
            map_path = mdir / "link.map"
            exe = mdir / "smug_app"
            p = run(
                [
                    "rustc", f"+{toolchain}", "-O",
                    "-C", f"linker={wrapper}",
                    "-C", f"link-arg={deplib_o}",
                    str(smug_rs), "-o", str(exe),
                ],
                env={
                    "HERMETIC_REAL_LINKER": "/usr/bin/cc",
                    "HERMETIC_MANIFEST_OUT": str(manifest_path),
                    "HERMETIC_DEPFILE_OUT": str(dep_path),
                    "HERMETIC_MAP_OUT": str(map_path),
                    "HERMETIC_NO_DEPLIBS": no_deplibs,
                },
                check=False,
            )
            manifest = json.loads(manifest_path.read_text()) if manifest_path.is_file() else {}
            smug_results[mode_name] = {
                "rustc_rc": p.returncode,
                "run_output": run([str(exe)]).stdout.strip() if p.returncode == 0 else None,
                "smuggled_archive_absent_from_argv": True,
                "smuggled_archive_caught_by_depfile": any("libsecret_dep.a" in d for d in manifest.get("depfile_entries", [])),
                "smuggled_archive_caught_by_trace": any("libsecret_dep.a" in ln for ln in manifest.get("trace_lines_all", [])),
                "trace_matching_smuggled": [norm(ln) for ln in manifest.get("trace_lines_all", []) if "libsecret_dep.a" in ln],
                "stderr_excerpt": [norm(ln) for ln in p.stderr.strip().splitlines()[-3:]] if p.returncode != 0 else [],
            }

        results["sht_llvm_dependent_libraries_smuggling"] = smug_results
        return {"toolchain": toolchain, **results}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--toolchains", nargs="+", default=["1.99.1", "nightly-2026-06-01"])
    parser.add_argument("--json-out", type=pathlib.Path)
    args = parser.parse_args()

    out = {}
    for tc in args.toolchains:
        out[tc] = {
            "probe_1a_cargo_divergence": probe_1a_cargo_build_rs_divergence(tc),
            "probe_1b_rlib_bundling_and_toctou": probe_1b_rlib_bundling_and_toctou(tc),
            "probe_1c_linker_wrapper_and_deplibs": probe_1c_linker_wrapper_and_deplibs_smuggling(tc),
        }

    rendered = json.dumps(out, indent=2)
    if args.json_out:
        args.json_out.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
