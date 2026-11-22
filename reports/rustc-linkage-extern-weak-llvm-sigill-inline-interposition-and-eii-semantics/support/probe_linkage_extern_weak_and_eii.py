#!/usr/bin/env python3
"""Empirical probe for rustc `#![feature(linkage)]` & `#![feature(extern_item_impls)]` (`#[eii]`).

Reproduces four distinct compiler/interpreter/linker defects and semantics checks:
  c1: Same-CGU `#[no_mangle]` definition + `#[linkage = "extern_weak"]` declaration
      mutating the defined LLVM global/function linkage to illegal `define extern_weak`,
      bypassing `-Z verify-llvm-ir`, failing `llvm-as` round-trip parsing, and crashing
      LLVM `AsmPrinter::emitFunctionBody()` / `emitLinkage()` with `SIGILL` (`rc = -4`).
  c2: Cross-crate `extern_weak` native vs. Miri divergence (`PRESENT=Some(77) SAME_SLOT=false`
      natively vs. `PRESENT=None SAME_SLOT=true` in Miri due to `extern_static_pointer`
      short-circuiting before `lookup_exported_symbol`), plus a Linux built-in weak shim check.
  c3: Contradictory ``#[inline] is ignored on externally exported functions`` warning on
      `#[inline(always)] #[linkage = "weak"]` where `rustc_codegen_llvm` still emits
      `alwaysinline`, breaking strong-over-weak interposition even at
      `-Z mir-opt-level=0 -C opt-level=0`, plus `-Z inline-llvm=no` control.
  c4: `#![feature(extern_item_impls)]` (`#[eii]`) default weak-alias vs. explicit strong
      override resolution natively (debug & `--release`), same-crate default-alias
      suppression, duplicate-explicit compile error, and Miri foreign-lookup failure (`rc = 1`).

Uses only Python 3.10+ standard library and local `rustc` / `cargo` / `cargo miri` / sysroot LLVM tools.
All scratch workspaces live inside `tempfile.TemporaryDirectory()`.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _env_with_cargo() -> dict[str, str]:
    env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    path = env.get("PATH", "")
    if cargo_bin not in path.split(os.pathsep):
        env["PATH"] = f"{cargo_bin}{os.pathsep}{path}" if path else cargo_bin
    # Disable ANSI color codes for deterministic diagnostics.
    env["CARGO_TERM_COLOR"] = "never"
    return env


def _run(
    cmd: list[str],
    *,
    cwd: Path,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env or _env_with_cargo(),
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def _find_sysroot_tool(env: dict[str, str], name: str) -> str | None:
    p = _run(["rustc", "--print", "sysroot"], cwd=Path("."), env=env)
    if p.returncode != 0:
        return None
    sysroot = Path(p.stdout.strip())
    for candidate in sysroot.glob(f"lib/rustlib/*/bin/{name}"):
        if candidate.is_file():
            return str(candidate)
    return shutil.which(name, path=env.get("PATH"))


def _sanitize_paths(text: str, tmp: Path) -> str:
    home = str(Path.home())
    text = text.replace(str(tmp), "<TMP>")
    text = text.replace(home, "<HOME>")
    return text


def probe_c1_same_cgu_extern_weak(env: dict[str, str], llvm_as: str | None) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="probe_c1_") as td:
        tmp = Path(td)
        src_fn = tmp / "same_cgu_fn.rs"
        src_fn.write_text(
            """#![feature(linkage)]

#[unsafe(no_mangle)]
pub extern "C" fn present_fn() -> i32 {
    77
}

mod imp {
    unsafe extern "C" {
        #[linkage = "extern_weak"]
        pub static present_fn: Option<unsafe extern "C" fn() -> i32>;
    }
}

fn main() {
    let f = unsafe { imp::present_fn };
    let val = f.map(|g| unsafe { g() });
    println!("PRESENT={val:?}");
}
""",
            encoding="utf-8",
        )

        # 1a. Emit LLVM IR (single CGU)
        ir_out = tmp / "same_cgu_fn.ll"
        p_ir = _run(
            [
                "rustc",
                "--edition=2024",
                "-C",
                "codegen-units=1",
                "--emit=llvm-ir",
                "-o",
                str(ir_out),
                str(src_fn),
            ],
            cwd=tmp,
            env=env,
        )
        emitted_ir_lines: list[str] = []
        if ir_out.is_file():
            for line in ir_out.read_text(encoding="utf-8", errors="replace").splitlines():
                if (
                    "_rust_extern_with_linkage_" in line
                    or "define extern_weak" in line
                    or "@present_fn(" in line
                ):
                    emitted_ir_lines.append(line)

        # 1b. Round-trip emitted IR through llvm-as (LLParser check)
        llvm_as_result: dict[str, Any] = {"available": llvm_as is not None}
        if llvm_as and ir_out.is_file():
            p_as = _run([llvm_as, str(ir_out), "-o", str(tmp / "same_cgu_fn.bc")], cwd=tmp, env=env)
            llvm_as_result["rc"] = p_as.returncode
            llvm_as_result["stderr"] = _sanitize_paths(p_as.stderr.strip(), tmp)

        # 1c. Native codegen (single CGU) -> expected SIGILL (-4)
        bin_out = tmp / "same_cgu_fn_bin"
        p_cg = _run(
            [
                "rustc",
                "--edition=2024",
                "-C",
                "codegen-units=1",
                "-o",
                str(bin_out),
                str(src_fn),
            ],
            cwd=tmp,
            env=env,
        )

        # 1d. Native codegen with -Z verify-llvm-ir -> checks if llvm::Verifier catches define extern_weak
        p_verify = _run(
            [
                "rustc",
                "--edition=2024",
                "-C",
                "codegen-units=1",
                "-Z",
                "verify-llvm-ir",
                "-o",
                str(tmp / "same_cgu_fn_verify_bin"),
                str(src_fn),
            ],
            cwd=tmp,
            env=env,
        )

        # 1e. Same-CGU static variable collision (data symbol instead of function)
        src_data = tmp / "same_cgu_data.rs"
        src_data.write_text(
            """#![feature(linkage)]

#[unsafe(no_mangle)]
pub static PRESENT_DATA: i32 = 42;

mod imp_data {
    unsafe extern "C" {
        #[linkage = "extern_weak"]
        pub static PRESENT_DATA: *const i32;
    }
}

fn main() {
    let p = unsafe { imp_data::PRESENT_DATA };
    let v = if p.is_null() { None } else { Some(unsafe { *p }) };
    println!("DATA={v:?}");
}
""",
            encoding="utf-8",
        )
        data_ir = tmp / "same_cgu_data.ll"
        p_data_ir = _run(
            [
                "rustc",
                "--edition=2024",
                "-C",
                "codegen-units=1",
                "--emit=llvm-ir",
                "-o",
                str(data_ir),
                str(src_data),
            ],
            cwd=tmp,
            env=env,
        )
        data_ir_lines: list[str] = []
        if data_ir.is_file():
            for line in data_ir.read_text(encoding="utf-8", errors="replace").splitlines():
                if "PRESENT_DATA" in line or "_rust_extern_with_linkage_" in line:
                    data_ir_lines.append(line)
        p_data_cg = _run(
            [
                "rustc",
                "--edition=2024",
                "-C",
                "codegen-units=1",
                "-o",
                str(tmp / "same_cgu_data_bin"),
                str(src_data),
            ],
            cwd=tmp,
            env=env,
        )
        data_llvm_as: dict[str, Any] = {"available": llvm_as is not None}
        if llvm_as and data_ir.is_file():
            p_das = _run([llvm_as, str(data_ir), "-o", str(tmp / "same_cgu_data.bc")], cwd=tmp, env=env)
            data_llvm_as["rc"] = p_das.returncode
            data_llvm_as["stderr"] = _sanitize_paths(p_das.stderr.strip(), tmp)

        # 1f. Control: separate-crate definition + extern_weak declaration
        prov_rs = tmp / "prov.rs"
        prov_rs.write_text(
            """#[unsafe(no_mangle)]
pub extern "C" fn present_fn() -> i32 {
    77
}
pub fn anchor() -> i32 { 1 }
""",
            encoding="utf-8",
        )
        app_rs = tmp / "app.rs"
        app_rs.write_text(
            """#![feature(linkage)]
extern crate prov;

unsafe extern "C" {
    #[linkage = "extern_weak"]
    static present_fn: Option<unsafe extern "C" fn() -> i32>;
}

fn main() {
    let _ = prov::anchor();
    let val = unsafe { present_fn }.map(|g| unsafe { g() });
    println!("PRESENT={val:?}");
}
""",
            encoding="utf-8",
        )
        p_prov = _run(
            ["rustc", "--edition=2024", "--crate-type=rlib", "-o", str(tmp / "libprov.rlib"), str(prov_rs)],
            cwd=tmp,
            env=env,
        )
        p_app = _run(
            [
                "rustc",
                "--edition=2024",
                "--extern",
                f"prov={tmp / 'libprov.rlib'}",
                "-o",
                str(tmp / "app_bin"),
                str(app_rs),
            ],
            cwd=tmp,
            env=env,
        )
        ctrl_stdout = ""
        if p_app.returncode == 0:
            p_run = _run([str(tmp / "app_bin")], cwd=tmp, env=env)
            ctrl_stdout = p_run.stdout.strip()

        return {
            "fn_same_cgu": {
                "emit_ir_rc": p_ir.returncode,
                "emitted_ir_lines": emitted_ir_lines,
                "llvm_as_roundtrip": llvm_as_result,
                "codegen_rc": p_cg.returncode,
                "codegen_stderr_head": "\n".join(
                    _sanitize_paths(p_cg.stderr, tmp).splitlines()[:15]
                ),
                "verify_llvm_ir_rc": p_verify.returncode,
                "verify_llvm_ir_stderr_head": "\n".join(
                    _sanitize_paths(p_verify.stderr, tmp).splitlines()[:15]
                ),
            },
            "static_same_cgu": {
                "emit_ir_rc": p_data_ir.returncode,
                "emitted_ir_lines": data_ir_lines,
                "llvm_as_roundtrip": data_llvm_as,
                "codegen_rc": p_data_cg.returncode,
                "codegen_stderr_head": "\n".join(
                    _sanitize_paths(p_data_cg.stderr, tmp).splitlines()[:15]
                ),
            },
            "separate_crate_control": {
                "prov_rc": p_prov.returncode,
                "app_rc": p_app.returncode,
                "stdout": ctrl_stdout,
            },
        }


def probe_c2_cross_crate_extern_weak(env: dict[str, str]) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="probe_c2_") as td:
        tmp = Path(td)
        (tmp / "prov" / "src").mkdir(parents=True)
        (tmp / "app" / "src").mkdir(parents=True)

        (tmp / "Cargo.toml").write_text(
            '[workspace]\nmembers = ["prov", "app"]\nresolver = "2"\n',
            encoding="utf-8",
        )
        (tmp / "prov" / "Cargo.toml").write_text(
            '[package]\nname = "prov"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        (tmp / "prov" / "src" / "lib.rs").write_text(
            """#[unsafe(no_mangle)]
pub extern "C" fn present_fn() -> i32 {
    77
}

pub fn anchor() -> i32 {
    1
}
""",
            encoding="utf-8",
        )
        (tmp / "app" / "Cargo.toml").write_text(
            '[package]\nname = "app"\nversion = "0.1.0"\nedition = "2024"\n\n[dependencies]\nprov = { path = "../prov" }\n',
            encoding="utf-8",
        )
        (tmp / "app" / "src" / "main.rs").write_text(
            """#![feature(linkage)]

unsafe extern "C" {
    #[linkage = "extern_weak"]
    static present_fn: Option<unsafe extern "C" fn() -> i32>;
    #[linkage = "extern_weak"]
    static missing_fn: Option<unsafe extern "C" fn() -> i32>;
    #[linkage = "extern_weak"]
    static strlen: Option<unsafe extern "C" fn(*const core::ffi::c_char) -> usize>;
}

fn main() {
    let _ = prov::anchor();
    let p = unsafe { present_fn }.map(|f| unsafe { f() });
    let m = unsafe { missing_fn }.map(|f| unsafe { f() });
    let same_slot = (&raw const present_fn as usize) == (&raw const missing_fn as usize);
    let builtin_len = unsafe { strlen }.map(|f| unsafe { f(c"hello".as_ptr()) });
    println!("PRESENT={p:?} MISSING={m:?} SAME_SLOT={same_slot} BUILTIN_STRLEN={builtin_len:?}");
}
""",
            encoding="utf-8",
        )

        p_native = _run(["cargo", "run", "-q", "-p", "app"], cwd=tmp, env=env)
        p_miri = _run(["cargo", "miri", "run", "-q", "-p", "app"], cwd=tmp, env=env, timeout=180)
        return {
            "native_rc": p_native.returncode,
            "native_stdout": p_native.stdout.strip(),
            "native_stderr": _sanitize_paths(p_native.stderr.strip(), tmp),
            "miri_rc": p_miri.returncode,
            "miri_stdout": p_miri.stdout.strip(),
            "miri_stderr": _sanitize_paths(p_miri.stderr.strip(), tmp),
        }


def probe_c3_weak_inline_contradiction(env: dict[str, str], llvm_nm: str | None) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="probe_c3_") as td:
        tmp = Path(td)
        weak_rs = tmp / "weak_lib.rs"
        weak_rs.write_text(
            """#![feature(linkage)]

#[linkage = "weak"]
#[unsafe(no_mangle)]
pub extern "C" fn weak_plain() -> u32 {
    10
}

#[inline]
#[linkage = "weak"]
#[unsafe(no_mangle)]
pub extern "C" fn weak_hint() -> u32 {
    10
}

#[inline(always)]
#[linkage = "weak"]
#[unsafe(no_mangle)]
pub extern "C" fn weak_always() -> u32 {
    10
}

pub fn call_plain() -> u32 { weak_plain() }
pub fn call_hint() -> u32 { weak_hint() }
pub fn call_always() -> u32 { weak_always() }
""",
            encoding="utf-8",
        )
        strong_rs = tmp / "strong_bin.rs"
        strong_rs.write_text(
            """extern crate weak_lib;

#[unsafe(no_mangle)]
pub extern "C" fn weak_plain() -> u32 { 99 }

#[unsafe(no_mangle)]
pub extern "C" fn weak_hint() -> u32 { 99 }

#[unsafe(no_mangle)]
pub extern "C" fn weak_always() -> u32 { 99 }

fn main() {
    let callers = (weak_lib::call_plain(), weak_lib::call_hint(), weak_lib::call_always());
    let direct = (weak_plain(), weak_hint(), weak_always());
    println!("CALLERS={callers:?} DIRECT={direct:?}");
}
""",
            encoding="utf-8",
        )

        configs: dict[str, list[str]] = {
            "mir_opt0_o0": ["-Z", "mir-opt-level=0", "-C", "opt-level=0"],
            "default_o0": ["-C", "opt-level=0"],
            "default_o2": ["-C", "opt-level=2"],
            "no_inline_llvm_o0": ["-Z", "inline-llvm=no", "-C", "opt-level=0"],
        }

        out: dict[str, Any] = {}
        for name, flags in configs.items():
            sub = tmp / name
            sub.mkdir()
            rlib = sub / "libweak_lib.rlib"
            p_lib = _run(
                ["rustc", "--edition=2024", "--crate-type=rlib", "-C", "codegen-units=1", *flags, "-o", str(rlib), str(weak_rs)],
                cwd=sub,
                env=env,
            )
            bin_path = sub / "strong_bin"
            p_bin = _run(
                [
                    "rustc",
                    "--edition=2024",
                    "-C",
                    "codegen-units=1",
                    *flags,
                    "--extern",
                    f"weak_lib={rlib}",
                    "-o",
                    str(bin_path),
                    str(strong_rs),
                ],
                cwd=sub,
                env=env,
            )
            stdout = ""
            if p_bin.returncode == 0:
                p_exec = _run([str(bin_path)], cwd=sub, env=env)
                stdout = p_exec.stdout.strip()
            warnings = [
                ln for ln in p_lib.stderr.splitlines() if ln.startswith("warning:") or "help: externally exported" in ln
            ]
            entry: dict[str, Any] = {
                "flags": flags,
                "lib_rc": p_lib.returncode,
                "bin_rc": p_bin.returncode,
                "stdout": stdout,
                "warnings": warnings,
            }
            if name in ("mir_opt0_o0", "default_o2"):
                ir_file = sub / "weak_lib.ll"
                p_ir = _run(
                    [
                        "rustc",
                        "--edition=2024",
                        "--crate-type=rlib",
                        "-C",
                        "codegen-units=1",
                        *flags,
                        "--emit=llvm-ir",
                        "-o",
                        str(ir_file),
                        str(weak_rs),
                    ],
                    cwd=sub,
                    env=env,
                )
                if p_ir.returncode == 0 and ir_file.is_file():
                    ir_text = ir_file.read_text(encoding="utf-8", errors="replace")
                    fn_defs = []
                    attr_defs = []
                    for ln in ir_text.splitlines():
                        if any(k in ln for k in ("@weak_plain(", "@weak_hint(", "@weak_always(", "call_always", "call_hint", "call_plain")):
                            if ln.startswith("define ") or "call " in ln or "ret i32" in ln:
                                fn_defs.append(ln)
                        if ln.startswith("attributes #") and ("alwaysinline" in ln or "inlinehint" in ln):
                            attr_defs.append(ln)
                    entry["ir_fn_lines"] = fn_defs[:20]
                    entry["ir_inline_attr_groups"] = attr_defs
                if llvm_nm and bin_path.is_file():
                    p_nm = _run([llvm_nm, str(rlib)], cwd=sub, env=env)
                    entry["rlib_nm_weak_syms"] = [
                        ln for ln in p_nm.stdout.splitlines() if "weak_" in ln
                    ]
            out[name] = entry
        return out


def probe_c4_eii_native_and_miri(env: dict[str, str]) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="probe_c4_") as td:
        tmp = Path(td)
        for pkg in ("hook_api", "app_default", "app_override", "app_same_crate", "app_dup_override"):
            (tmp / pkg / "src").mkdir(parents=True)

        (tmp / "Cargo.toml").write_text(
            '[workspace]\nmembers = ["hook_api", "app_default", "app_override", "app_same_crate"]\nresolver = "2"\n',
            encoding="utf-8",
        )
        (tmp / "hook_api" / "Cargo.toml").write_text(
            '[package]\nname = "hook_api"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        (tmp / "hook_api" / "src" / "lib.rs").write_text(
            """#![feature(extern_item_impls)]

#[eii]
pub fn compute_hook(x: i32) -> i32 {
    x + 10
}

pub fn invoke(x: i32) -> i32 {
    compute_hook(x)
}
""",
            encoding="utf-8",
        )

        (tmp / "app_default" / "Cargo.toml").write_text(
            '[package]\nname = "app_default"\nversion = "0.1.0"\nedition = "2024"\n\n[dependencies]\nhook_api = { path = "../hook_api" }\n',
            encoding="utf-8",
        )
        (tmp / "app_default" / "src" / "main.rs").write_text(
            """fn main() {
    println!("DEFAULT={}", hook_api::invoke(5));
}
""",
            encoding="utf-8",
        )

        (tmp / "app_override" / "Cargo.toml").write_text(
            '[package]\nname = "app_override"\nversion = "0.1.0"\nedition = "2024"\n\n[dependencies]\nhook_api = { path = "../hook_api" }\n',
            encoding="utf-8",
        )
        (tmp / "app_override" / "src" / "main.rs").write_text(
            """#![feature(extern_item_impls)]

#[hook_api::compute_hook]
fn custom_impl(x: i32) -> i32 {
    x + 900
}

fn main() {
    println!("OVERRIDE={}", hook_api::invoke(5));
}
""",
            encoding="utf-8",
        )

        (tmp / "app_same_crate" / "Cargo.toml").write_text(
            '[package]\nname = "app_same_crate"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        (tmp / "app_same_crate" / "src" / "main.rs").write_text(
            """#![feature(extern_item_impls)]

#[eii]
pub fn local_hook(x: i32) -> i32 {
    x + 10
}

#[local_hook]
fn local_override(x: i32) -> i32 {
    x + 700
}

fn main() {
    println!("SAME_CRATE_OVERRIDE={}", local_hook(5));
}
""",
            encoding="utf-8",
        )

        p_def_rel = _run(["cargo", "run", "-q", "--release", "-p", "app_default"], cwd=tmp, env=env)
        p_ovr_rel = _run(["cargo", "run", "-q", "--release", "-p", "app_override"], cwd=tmp, env=env)
        p_def_dbg = _run(["cargo", "run", "-q", "-p", "app_default"], cwd=tmp, env=env)
        p_ovr_dbg = _run(["cargo", "run", "-q", "-p", "app_override"], cwd=tmp, env=env)
        p_same = _run(["cargo", "run", "-q", "--release", "-p", "app_same_crate"], cwd=tmp, env=env)

        p_miri_def = _run(["cargo", "miri", "run", "-q", "-p", "app_default"], cwd=tmp, env=env, timeout=180)
        p_miri_ovr = _run(["cargo", "miri", "run", "-q", "-p", "app_override"], cwd=tmp, env=env, timeout=180)

        # Standalone duplicate explicit EII impl check (expected compile error DuplicateEiiImpls)
        dup_rs = tmp / "dup_eii.rs"
        dup_rs.write_text(
            """#![feature(extern_item_impls)]

#[eii]
fn dup_hook(x: i32) -> i32;

#[dup_hook]
fn impl_a(x: i32) -> i32 { x + 1 }

#[dup_hook]
fn impl_b(x: i32) -> i32 { x + 2 }

fn main() {
    println!("{}", dup_hook(1));
}
""",
            encoding="utf-8",
        )
        p_dup = _run(["rustc", "--edition=2024", "-o", str(tmp / "dup_eii_bin"), str(dup_rs)], cwd=tmp, env=env)

        # Emit LLVM IR for hook_api and app_same_crate to inspect weak alias forwarding shim vs suppression
        hook_ir = tmp / "hook_api.ll"
        _run(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=rlib",
                "--crate-name=hook_api",
                "-C",
                "codegen-units=1",
                "--emit=llvm-ir",
                "-o",
                str(hook_ir),
                str(tmp / "hook_api" / "src" / "lib.rs"),
            ],
            cwd=tmp,
            env=env,
        )
        hook_ir_defs = []
        if hook_ir.is_file():
            for ln in hook_ir.read_text(encoding="utf-8", errors="replace").splitlines():
                if ln.startswith("define ") and "compute_hook" in ln:
                    hook_ir_defs.append(ln)

        same_ir = tmp / "same_crate.ll"
        _run(
            [
                "rustc",
                "--edition=2024",
                "-C",
                "codegen-units=1",
                "--emit=llvm-ir",
                "-o",
                str(same_ir),
                str(tmp / "app_same_crate" / "src" / "main.rs"),
            ],
            cwd=tmp,
            env=env,
        )
        same_ir_defs = []
        if same_ir.is_file():
            for ln in same_ir.read_text(encoding="utf-8", errors="replace").splitlines():
                if ln.startswith("define ") and ("local_hook" in ln or "local_override" in ln):
                    same_ir_defs.append(ln)

        return {
            "native_default_release": {"rc": p_def_rel.returncode, "stdout": p_def_rel.stdout.strip()},
            "native_override_release": {"rc": p_ovr_rel.returncode, "stdout": p_ovr_rel.stdout.strip()},
            "native_default_debug": {"rc": p_def_dbg.returncode, "stdout": p_def_dbg.stdout.strip()},
            "native_override_debug": {"rc": p_ovr_dbg.returncode, "stdout": p_ovr_dbg.stdout.strip()},
            "native_same_crate_override": {"rc": p_same.returncode, "stdout": p_same.stdout.strip()},
            "miri_default": {
                "rc": p_miri_def.returncode,
                "stdout": p_miri_def.stdout.strip(),
                "stderr": _sanitize_paths(p_miri_def.stderr.strip(), tmp),
            },
            "miri_override": {
                "rc": p_miri_ovr.returncode,
                "stdout": p_miri_ovr.stdout.strip(),
                "stderr": _sanitize_paths(p_miri_ovr.stderr.strip(), tmp),
            },
            "duplicate_explicit_compile_error": {
                "rc": p_dup.returncode,
                "stderr": _sanitize_paths(p_dup.stderr.strip(), tmp),
            },
            "hook_api_ir_defs": hook_ir_defs,
            "same_crate_ir_defs": same_ir_defs,
        }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional JSON output file path")
    args = parser.parse_args(argv)

    env = _env_with_cargo()
    rustc_v = _run(["rustc", "-vV"], cwd=Path("."), env=env).stdout.strip()
    miri_v = _run(["cargo", "miri", "--version"], cwd=Path("."), env=env).stdout.strip()
    llvm_as = _find_sysroot_tool(env, "llvm-as")
    llvm_nm = _find_sysroot_tool(env, "llvm-nm")

    results = {
        "rustc_version": rustc_v,
        "miri_version": miri_v,
        "cases": {
            "c1_same_cgu_define_extern_weak_sigill": probe_c1_same_cgu_extern_weak(env, llvm_as),
            "c2_cross_crate_extern_weak_native_vs_miri": probe_c2_cross_crate_extern_weak(env),
            "c3_weak_linkage_inline_warning_contradiction": probe_c3_weak_inline_contradiction(env, llvm_nm),
            "c4_eii_default_vs_override_native_and_miri": probe_c4_eii_native_and_miri(env),
        },
    }

    encoded = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(encoded, encoding="utf-8")
    else:
        sys.stdout.write(encoded)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
