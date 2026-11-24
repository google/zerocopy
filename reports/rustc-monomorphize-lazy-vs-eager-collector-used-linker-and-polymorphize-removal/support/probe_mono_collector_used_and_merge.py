#!/usr/bin/env python3
"""Live rustc probe for monomorphization collection (Lazy vs. Eager),
rlib cross_crate_inlinable deferral, #[used(compiler)] vs. #[used(linker)],
-Zpolymorphize removal, and LLVM -O2 MergeFunctions folding.

Runs strictly inside a temporary directory and writes sanitized JSON results.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

MONO_SPECIMEN_RS = r"""#![feature(used_with_arg)]

#[used(compiler)]
static USED_COMP: [u8; 1] = [7];

#[used(linker)]
static USED_LINK: [u8; 1] = [8];

#[inline(never)]
fn poly_const<T>(x: u32) -> u32 {
    x.wrapping_mul(3).wrapping_add(1)
}

#[inline(never)]
fn poly_size<T>(x: u32) -> usize {
    (x as usize).wrapping_add(core::mem::size_of::<T>())
}

#[inline(never)]
fn dead() -> u32 {
    42
}

pub fn pub_dead_small() -> u32 {
    99
}

#[inline(never)]
pub fn pub_dead_exported() -> u32 {
    123
}

fn gen_dead<T>(x: T) -> T {
    x
}

#[unsafe(no_mangle)]
pub extern "C" fn exported_fn(x: u32) -> u32 {
    poly_const::<u8>(x)
        .wrapping_add(poly_const::<u16>(x))
        .wrapping_add(poly_const::<u64>(x))
        .wrapping_add(poly_size::<u8>(x) as u32)
        .wrapping_add(poly_size::<u16>(x) as u32)
        .wrapping_add(poly_size::<u64>(x) as u32)
}

fn main() {
    let _ = exported_fn(5);
}
"""

BARE_USED_RS = r"""#[used]
static USED_DEFAULT: [u8; 1] = [9];

pub fn touch() -> u8 {
    42
}
"""

POLY_SPECIMEN_RS = r"""#[inline(never)]
fn poly_const<T>(x: u32) -> u32 {
    x.wrapping_mul(3).wrapping_add(1)
}

#[inline(never)]
fn poly_size<T>(x: u32) -> usize {
    (x as usize).wrapping_add(core::mem::size_of::<T>())
}

#[unsafe(no_mangle)]
pub extern "C" fn drive(x: u32) -> u32 {
    poly_const::<u8>(x)
        .wrapping_add(poly_const::<u16>(x))
        .wrapping_add(poly_const::<u64>(x))
        .wrapping_add(poly_size::<u8>(x) as u32)
        .wrapping_add(poly_size::<u16>(x) as u32)
        .wrapping_add(poly_size::<u64>(x) as u32)
}

fn main() {
    println!("{}", drive(11));
}
"""

DOWNSTREAM_APP_RS = r"""extern crate mono;

fn main() {
    let f: fn() -> u32 = mono::pub_dead_small;
    let g: fn() -> u32 = mono::pub_dead_exported;
    println!("{}", f().wrapping_add(g()));
}
"""


def run_cmd(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        text=True,
        capture_output=True,
        check=False,
    )


def find_sysroot_tool(sysroot: Path, name: str) -> str | None:
    candidate = sysroot / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin" / name
    if candidate.is_file():
        return str(candidate)
    return shutil.which(name)


def sanitize_text(text: str, tmpdir: Path) -> str:
    return text.replace(str(tmpdir), "<TMP>")


def extract_mono_items(stderr_text: str) -> list[str]:
    return sorted(
        line.strip()
        for line in stderr_text.splitlines()
        if line.strip().startswith("MONO_ITEM ")
    )


def has_mono_fn(mono_items: list[str], target_name: str) -> bool:
    for item in mono_items:
        # Match "MONO_ITEM fn <name> @@ ..." or generic prefix "<name>::<"
        if f"MONO_ITEM fn {target_name} @@" in item or f"MONO_ITEM fn {target_name}::<" in item:
            return True
    return False


def has_mono_static(mono_items: list[str], target_name: str) -> bool:
    return any(f"MONO_ITEM static {target_name} @@" in item for item in mono_items)


def collect_mono_case(
    rustc_bin: str,
    llvm_nm: str | None,
    readelf_bin: str | None,
    tmpdir: Path,
    src_path: Path,
    crate_type: str,
    link_dead_code: str,
    tag: str,
) -> dict:
    out_prefix = (
        tmpdir / f"libmono_{tag}.rlib" if crate_type == "rlib" else tmpdir / f"mono_{tag}"
    )
    cmd_mono = [
        rustc_bin,
        "--edition=2024",
        f"--crate-type={crate_type}",
        "-Copt-level=2",
        f"-Clink-dead-code={link_dead_code}",
        "-Ccodegen-units=1",
        "-Zprint-mono-items=yes",
        "-o",
        str(out_prefix),
        str(src_path),
    ]
    res_mono = run_cmd(cmd_mono, tmpdir)
    combined_out = res_mono.stdout + "\n" + res_mono.stderr
    mono_items = extract_mono_items(combined_out)

    # Also emit LLVM IR and single object file for section/IR inspection.
    ll_path = tmpdir / f"mono_{tag}.ll"
    obj_path = tmpdir / f"mono_{tag}.o"
    run_cmd(
        [
            rustc_bin,
            "--edition=2024",
            f"--crate-type={crate_type}",
            "-Copt-level=2",
            f"-Clink-dead-code={link_dead_code}",
            "-Ccodegen-units=1",
            "--emit=llvm-ir",
            "-o",
            str(ll_path),
            str(src_path),
        ],
        tmpdir,
    )
    run_cmd(
        [
            rustc_bin,
            "--edition=2024",
            f"--crate-type={crate_type}",
            "-Copt-level=2",
            f"-Clink-dead-code={link_dead_code}",
            "-Ccodegen-units=1",
            "--emit=obj",
            "-o",
            str(obj_path),
            str(src_path),
        ],
        tmpdir,
    )

    ll_text = ll_path.read_text(encoding="utf-8") if ll_path.is_file() else ""
    ir_highlights = [
        line.strip()
        for line in ll_text.splitlines()
        if any(
            tok in line
            for tok in (
                "USED_COMP",
                "USED_LINK",
                "@llvm.used",
                "@llvm.compiler.used",
                "define ",
            )
        )
        and ("USED_" in line or "@llvm." in line or "poly_" in line or "exported_fn" in line or "dead" in line)
    ]

    nm_symbols: list[str] = []
    if llvm_nm and obj_path.is_file():
        nm_res = run_cmd([llvm_nm, str(obj_path)], tmpdir)
        nm_symbols = [
            line.strip()
            for line in nm_res.stdout.splitlines()
            if any(k in line for k in ("USED_", "poly_", "exported_fn", "dead", "main"))
        ]

    readelf_sections: list[str] = []
    if readelf_bin and obj_path.is_file():
        re_res = run_cmd([readelf_bin, "-WS", str(obj_path)], tmpdir)
        readelf_sections = [
            line.strip()
            for line in re_res.stdout.splitlines()
            if any(k in line for k in ("USED_COMP", "USED_LINK", "Key to Flags", "R (retain)"))
        ]

    return {
        "crate_type": crate_type,
        "link_dead_code": link_dead_code,
        "compile_returncode": res_mono.returncode,
        "mono_item_count": len(mono_items),
        "mono_items": mono_items,
        "contains_dead": has_mono_fn(mono_items, "dead"),
        "contains_pub_dead_small": has_mono_fn(mono_items, "pub_dead_small"),
        "contains_pub_dead_exported": has_mono_fn(mono_items, "pub_dead_exported"),
        "contains_gen_dead": has_mono_fn(mono_items, "gen_dead"),
        "contains_main": has_mono_fn(mono_items, "main"),
        "contains_used_comp": has_mono_static(mono_items, "USED_COMP"),
        "contains_used_link": has_mono_static(mono_items, "USED_LINK"),
        "llvm_ir_highlights": ir_highlights,
        "llvm_nm_obj_symbols": nm_symbols,
        "readelf_used_sections": readelf_sections,
    }


def collect_merge_ir_case(
    rustc_bin: str,
    tmpdir: Path,
    src_path: Path,
    opt_level: str,
    link_dead_code: str,
    extra_args: list[str],
    tag: str,
) -> dict:
    ll_path = tmpdir / f"poly_{tag}.ll"
    cmd = [
        rustc_bin,
        "--edition=2024",
        "--crate-type=rlib",
        f"-Copt-level={opt_level}",
        f"-Clink-dead-code={link_dead_code}",
        "-Ccodegen-units=1",
        "--emit=llvm-ir",
        *extra_args,
        "-o",
        str(ll_path),
        str(src_path),
    ]
    res = run_cmd(cmd, tmpdir)
    ll_text = ll_path.read_text(encoding="utf-8") if ll_path.is_file() else ""
    defines = [
        line.strip()
        for line in ll_text.splitlines()
        if line.startswith("define ") and ("poly_const" in line or "poly_size" in line)
    ]
    aliases = [
        line.strip()
        for line in ll_text.splitlines()
        if " alias " in line and ("poly_const" in line or "poly_size" in line)
    ]
    caller_calls = [
        line.strip()
        for line in ll_text.splitlines()
        if ("call " in line) and ("poly_const" in line or "poly_size" in line)
    ]
    return {
        "opt_level": opt_level,
        "link_dead_code": link_dead_code,
        "extra_args": extra_args,
        "compile_returncode": res.returncode,
        "define_count_poly_const_or_size": len(defines),
        "alias_count_poly_const_or_size": len(aliases),
        "defines": defines,
        "aliases": aliases,
        "caller_calls": caller_calls,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent / "probe_results.json",
        help="Output JSON file path",
    )
    args = parser.parse_args()

    rustc_bin = shutil.which("rustc") or "rustc"
    ver_res = run_cmd([rustc_bin, "--version", "--verbose"], Path("/tmp"))
    if ver_res.returncode != 0:
        print(f"rustc invocation failed: {ver_res.stderr}", file=sys.stderr)
        return 1
    sysroot_res = run_cmd([rustc_bin, "--print", "sysroot"], Path("/tmp"))
    sysroot = Path(sysroot_res.stdout.strip())
    llvm_nm = find_sysroot_tool(sysroot, "llvm-nm")
    readelf_bin = shutil.which("readelf")
    ld_res = run_cmd(["ld", "--version"], Path("/tmp"))

    with tempfile.TemporaryDirectory() as td:
        tmpdir = Path(td)
        mono_rs = tmpdir / "mono.rs"
        mono_rs.write_text(MONO_SPECIMEN_RS, encoding="utf-8")

        bare_used_rs = tmpdir / "bare_used.rs"
        bare_used_rs.write_text(BARE_USED_RS, encoding="utf-8")

        poly_rs = tmpdir / "poly.rs"
        poly_rs.write_text(POLY_SPECIMEN_RS, encoding="utf-8")

        # 1. Print-mono-items=lazy rejection check
        res_lazy_cli = run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                "--crate-type=bin",
                "-Zprint-mono-items=lazy",
                "-o",
                str(tmpdir / "lazy_cli"),
                str(mono_rs),
            ],
            tmpdir,
        )

        # 2. Lazy vs Eager across bin and rlib
        mono_cases = {
            "bin_lazy_link_dead_code_no": collect_mono_case(
                rustc_bin, llvm_nm, readelf_bin, tmpdir, mono_rs, "bin", "no", "bin_lazy"
            ),
            "bin_eager_link_dead_code_yes": collect_mono_case(
                rustc_bin, llvm_nm, readelf_bin, tmpdir, mono_rs, "bin", "yes", "bin_eager"
            ),
            "rlib_lazy_link_dead_code_no": collect_mono_case(
                rustc_bin, llvm_nm, readelf_bin, tmpdir, mono_rs, "rlib", "no", "rlib_lazy"
            ),
            "rlib_eager_link_dead_code_yes": collect_mono_case(
                rustc_bin, llvm_nm, readelf_bin, tmpdir, mono_rs, "rlib", "yes", "rlib_eager"
            ),
        }

        # 2b. Downstream consumer linking against Lazy rlib
        app_rs = tmpdir / "app.rs"
        app_rs.write_text(DOWNSTREAM_APP_RS, encoding="utf-8")
        app_bin = tmpdir / "app_bin"
        rlib_lazy_artifact = tmpdir / "libmono_rlib_lazy.rlib"
        app_res = run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                "--crate-type=bin",
                "-Copt-level=2",
                "-Clink-dead-code=no",
                "-Ccodegen-units=1",
                "-Zprint-mono-items=yes",
                "--extern",
                f"mono={rlib_lazy_artifact}",
                "-o",
                str(app_bin),
                str(app_rs),
            ],
            tmpdir,
        )
        app_mono_items = extract_mono_items(app_res.stdout + "\n" + app_res.stderr)
        app_run = run_cmd([str(app_bin)], tmpdir) if app_res.returncode == 0 else None

        # 3. Bare #[used] default behavior on Linux ELF
        bare_ll = tmpdir / "bare_used.ll"
        bare_obj = tmpdir / "bare_used.o"
        run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                "--crate-type=rlib",
                "-Copt-level=2",
                "--emit=llvm-ir",
                "-o",
                str(bare_ll),
                str(bare_used_rs),
            ],
            tmpdir,
        )
        run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                "--crate-type=rlib",
                "-Copt-level=2",
                "--emit=obj",
                "-o",
                str(bare_obj),
                str(bare_used_rs),
            ],
            tmpdir,
        )
        bare_ll_lines = [
            line.strip()
            for line in bare_ll.read_text(encoding="utf-8").splitlines()
            if "USED_DEFAULT" in line or "@llvm.used" in line or "@llvm.compiler.used" in line
        ]
        bare_sections: list[str] = []
        if readelf_bin and bare_obj.is_file():
            re_bare = run_cmd([readelf_bin, "-WS", str(bare_obj)], tmpdir)
            bare_sections = [
                line.strip()
                for line in re_bare.stdout.splitlines()
                if "USED_DEFAULT" in line
            ]

        # 4. Real linker GC survival (--gc-sections vs --no-gc-sections)
        bin_gc = tmpdir / "bin_gc"
        bin_nogc = tmpdir / "bin_nogc"
        run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                "--crate-type=bin",
                "-Copt-level=2",
                "-Clink-dead-code=no",
                "-Ccodegen-units=1",
                "-Clink-arg=-Wl,--gc-sections",
                "-o",
                str(bin_gc),
                str(mono_rs),
            ],
            tmpdir,
        )
        run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                "--crate-type=bin",
                "-Copt-level=2",
                "-Clink-dead-code=no",
                "-Ccodegen-units=1",
                "-Clink-arg=-Wl,--no-gc-sections",
                "-o",
                str(bin_nogc),
                str(mono_rs),
            ],
            tmpdir,
        )
        gc_syms: list[str] = []
        nogc_syms: list[str] = []
        if llvm_nm:
            gc_syms = [
                line.strip()
                for line in run_cmd([llvm_nm, str(bin_gc)], tmpdir).stdout.splitlines()
                if "USED_" in line or "exported_fn" in line
            ]
            nogc_syms = [
                line.strip()
                for line in run_cmd([llvm_nm, str(bin_nogc)], tmpdir).stdout.splitlines()
                if "USED_" in line or "exported_fn" in line
            ]

        # 5. -Zpolymorphize removal & MergeFunctions across optimization / linkage modes
        res_poly_cli = run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                "--crate-type=rlib",
                "-Copt-level=2",
                "-Zpolymorphize=on",
                "-o",
                str(tmpdir / "poly_cli"),
                str(poly_rs),
            ],
            tmpdir,
        )

        merge_cases = {
            "o2_default_merge_functions_aliases_lazy": collect_merge_ir_case(
                rustc_bin, tmpdir, poly_rs, "2", "no", [], "o2_default"
            ),
            "o2_merge_functions_disabled_lazy": collect_merge_ir_case(
                rustc_bin,
                tmpdir,
                poly_rs,
                "2",
                "no",
                ["-Zmerge-functions=disabled"],
                "o2_disabled",
            ),
            "o2_eager_external_linkage_aliases": collect_merge_ir_case(
                rustc_bin, tmpdir, poly_rs, "2", "yes", [], "o2_eager_aliases"
            ),
            "o2_eager_external_linkage_trampolines": collect_merge_ir_case(
                rustc_bin,
                tmpdir,
                poly_rs,
                "2",
                "yes",
                ["-Zmerge-functions=trampolines"],
                "o2_eager_trampolines",
            ),
            "o1_merge_functions_inactive": collect_merge_ir_case(
                rustc_bin, tmpdir, poly_rs, "1", "no", [], "o1_default"
            ),
        }

        # 6. Runtime observational equivalence under MergeFunctions on vs disabled
        exe_mf_on = tmpdir / "poly_exe_on"
        exe_mf_off = tmpdir / "poly_exe_off"
        run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                "--crate-type=bin",
                "-Copt-level=2",
                "-Ccodegen-units=1",
                "-o",
                str(exe_mf_on),
                str(poly_rs),
            ],
            tmpdir,
        )
        run_cmd(
            [
                rustc_bin,
                "--edition=2024",
                "--crate-type=bin",
                "-Copt-level=2",
                "-Ccodegen-units=1",
                "-Zmerge-functions=disabled",
                "-o",
                str(exe_mf_off),
                str(poly_rs),
            ],
            tmpdir,
        )
        run_on = run_cmd([str(exe_mf_on)], tmpdir)
        run_off = run_cmd([str(exe_mf_off)], tmpdir)

        payload = {
            "rustc_version": ver_res.stdout.strip(),
            "ld_version": ld_res.stdout.splitlines()[0].strip() if ld_res.stdout else "",
            "experiments": {
                "print_mono_items_lazy_rejected": {
                    "returncode": res_lazy_cli.returncode,
                    "stderr": sanitize_text(res_lazy_cli.stderr.strip(), tmpdir),
                },
                "mono_collector_lazy_vs_eager_and_used_statics": mono_cases,
                "downstream_rlib_consumer": {
                    "compile_returncode": app_res.returncode,
                    "mono_item_count": len(app_mono_items),
                    "mono_items": app_mono_items,
                    "local_codegen_pub_dead_small": has_mono_fn(app_mono_items, "mono::pub_dead_small"),
                    "local_codegen_pub_dead_exported": has_mono_fn(app_mono_items, "mono::pub_dead_exported"),
                    "runtime_returncode": app_run.returncode if app_run else -1,
                    "runtime_stdout": app_run.stdout.strip() if app_run else "",
                },
                "bare_used_default_linux_elf": {
                    "llvm_ir_lines": bare_ll_lines,
                    "readelf_sections": bare_sections,
                },
                "linker_gc_survival": {
                    "gc_sections_symbols": gc_syms,
                    "no_gc_sections_symbols": nogc_syms,
                    "used_comp_survives_gc": any("USED_COMP" in s for s in gc_syms),
                    "used_link_survives_gc": any("USED_LINK" in s for s in gc_syms),
                    "used_comp_survives_no_gc": any("USED_COMP" in s for s in nogc_syms),
                    "used_link_survives_no_gc": any("USED_LINK" in s for s in nogc_syms),
                },
                "polymorphize_removal_and_merge_functions": {
                    "z_polymorphize_on_rejected": {
                        "returncode": res_poly_cli.returncode,
                        "stderr": sanitize_text(res_poly_cli.stderr.strip(), tmpdir),
                    },
                    "ir_modes": merge_cases,
                    "runtime_equivalence": {
                        "merge_functions_on_stdout": run_on.stdout.strip(),
                        "merge_functions_disabled_stdout": run_off.stdout.strip(),
                        "outputs_identical": (
                            run_on.returncode == 0
                            and run_off.returncode == 0
                            and run_on.stdout.strip() == run_off.stdout.strip()
                        ),
                    },
                },
            },
        }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.output}")
    print(
        "Counts:",
        {k: v["mono_item_count"] for k, v in mono_cases.items()},
    )
    print(
        "Merge defines/aliases:",
        {
            k: (v["define_count_poly_const_or_size"], v["alias_count_poly_const_or_size"])
            for k, v in merge_cases.items()
        },
    )
    print("Linker GC survival:", payload["experiments"]["linker_gc_survival"])
    print("Runtime eq:", payload["experiments"]["polymorphize_removal_and_merge_functions"]["runtime_equivalence"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
