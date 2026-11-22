#!/usr/bin/env python3
"""Empirical reproducibility probe for rustc path remapping, multi-CGU builds,
deterministic ar archive writing, incremental session nonces, and ELF linking.

Runs real `rustc`, `ar`, and linked ELF binaries in isolated temporary
directories, scrubbing all host-specific filesystem paths from the JSON output.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


LIB_RS = r"""#![crate_name = "repro_lib"]

pub mod caller {
    #[track_caller]
    #[inline(never)]
    pub fn where_am_i() -> &'static str {
        core::panic::Location::caller().file()
    }

    #[inline(never)]
    pub fn call_tracked() -> &'static str {
        where_am_i()
    }
}

pub mod arith_a {
    #[inline]
    pub fn helper_mul(x: u64, y: u64) -> u64 {
        x.wrapping_mul(y).wrapping_add(1)
    }

    #[inline(never)]
    pub fn compute_a1(x: u64) -> u64 {
        helper_mul(x, 3).wrapping_add(7)
    }

    #[inline(never)]
    pub fn compute_a2(x: u64) -> u64 {
        helper_mul(x ^ 0x55, 5).rotate_left(3)
    }
}

pub mod arith_b {
    use crate::arith_a::helper_mul;

    #[inline(never)]
    pub fn compute_b1(x: u64) -> u64 {
        helper_mul(x, 7).wrapping_sub(2)
    }

    #[inline(never)]
    pub fn compute_b2(x: u64) -> u64 {
        helper_mul(x.wrapping_add(11), 13) ^ 0xaa
    }
}

pub mod arith_c {
    use crate::arith_a::helper_mul;

    #[inline(never)]
    pub fn compute_c1(x: u64) -> u64 {
        helper_mul(x, 17).wrapping_add(19)
    }

    #[inline(never)]
    pub fn compute_c2(x: u64) -> u64 {
        helper_mul(x.rotate_right(5), 23)
    }
}

pub mod arith_d {
    use crate::arith_a::helper_mul;

    #[inline(never)]
    pub fn compute_d1(x: u64) -> u64 {
        helper_mul(x, 29).wrapping_add(31)
    }

    #[inline(never)]
    pub fn compute_d2(x: u64) -> u64 {
        helper_mul(x ^ 0xff, 37)
    }
}

pub mod dispatch {
    use crate::{arith_a, arith_b, arith_c, arith_d};

    pub fn fold_all(seed: u64) -> u64 {
        let mut acc = seed;
        acc = arith_a::compute_a1(acc);
        acc = arith_a::compute_a2(acc);
        acc = arith_b::compute_b1(acc);
        acc = arith_b::compute_b2(acc);
        acc = arith_c::compute_c1(acc);
        acc = arith_c::compute_c2(acc);
        acc = arith_d::compute_d1(acc);
        acc = arith_d::compute_d2(acc);
        acc
    }

    pub fn add_pair(a: u64, b: u64) -> u64 {
        arith_a::helper_mul(a, 1).wrapping_sub(1).wrapping_add(b)
    }
}

pub fn entry_sum(x: u64, y: u64) -> u64 {
    dispatch::add_pair(x, y)
}
"""

BIN_RS = r"""extern crate repro_lib;

fn main() {
    let a = repro_lib::entry_sum(4, 6);
    let b = repro_lib::entry_sum(10, 20);
    let loc = repro_lib::caller::where_am_i();
    let fold = repro_lib::dispatch::fold_all(1);
    println!("{a} {b} {loc} {fold}");
}
"""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def run_cmd(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    merged_env["LC_ALL"] = "C"
    merged_env["TZ"] = "UTC"
    if env:
        merged_env.update(env)
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=merged_env,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"command failed (rc={proc.returncode}): {' '.join(cmd)}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    return proc


def find_rustc() -> str:
    found = shutil.which("rustc")
    if found:
        return found
    candidate = Path.home() / ".cargo" / "bin" / "rustc"
    if candidate.exists():
        return str(candidate)
    raise FileNotFoundError("rustc not found in PATH or ~/.cargo/bin/rustc")


def count_needle(path: Path, needle: bytes) -> int:
    data = path.read_bytes()
    return data.count(needle)


def parse_gnu_ar(archive_bytes: bytes) -> dict[str, Any]:
    """Parse a GNU/SVR4 `ar` archive at exact byte offsets."""
    if not archive_bytes.startswith(b"!<arch>\n"):
        raise ValueError("not a standard GNU/SVR4 ar archive")
    pos = 8
    strtab: bytes = b""
    strtab_span: tuple[int, int] | None = None
    members: list[dict[str, Any]] = []
    n = len(archive_bytes)
    while pos + 60 <= n:
        hdr_start = pos
        hdr = archive_bytes[pos : pos + 60]
        if hdr[58:60] != b"`\n":
            raise ValueError(f"invalid ar header magic at offset {pos}: {hdr[58:60]!r}")
        raw_name = hdr[0:16].decode("ascii", errors="replace")
        mtime = int(hdr[16:28].decode("ascii").strip() or "0")
        uid = int(hdr[28:34].decode("ascii").strip() or "0")
        gid = int(hdr[34:40].decode("ascii").strip() or "0")
        mode_octal = hdr[40:48].decode("ascii").strip()
        size = int(hdr[48:58].decode("ascii").strip())
        data_start = pos + 60
        data_end = data_start + size
        payload = archive_bytes[data_start:data_end]
        next_pos = data_end + (size % 2)

        if raw_name.startswith("//"):
            strtab = payload
            strtab_span = (data_start, data_end)
            resolved_name = "//"
            kind = "gnu_strtab"
        elif raw_name.startswith("/ "):
            resolved_name = "/"
            kind = "symtab"
        elif raw_name.startswith("/SYM64/"):
            resolved_name = "/SYM64/"
            kind = "symtab64"
        elif raw_name.startswith("/"):
            off = int(raw_name[1:].strip())
            end_idx = strtab.find(b"/\n", off)
            if end_idx == -1:
                end_idx = strtab.find(b"\n", off)
            resolved_name = strtab[off:end_idx].decode("ascii", errors="replace") if end_idx != -1 else raw_name.strip()
            kind = "member"
        else:
            resolved_name = raw_name.strip().rstrip("/")
            kind = "member"

        members.append(
            {
                "name": resolved_name,
                "kind": kind,
                "header_span": [hdr_start, hdr_start + 60],
                "data_span": [data_start, data_end],
                "size": size,
                "mtime": mtime,
                "uid": uid,
                "gid": gid,
                "mode_octal": mode_octal,
                "payload_sha256": sha256_bytes(payload),
            }
        )
        pos = next_pos
    return {
        "total_bytes": n,
        "strtab_span": list(strtab_span) if strtab_span else None,
        "members": members,
    }


def classify_offset(parsed: dict[str, Any], offset: int) -> str:
    for m in parsed["members"]:
        hs, he = m["header_span"]
        ds, de = m["data_span"]
        if hs <= offset < he:
            return f"ar_header:{m['name']}"
        if ds <= offset < de:
            if m["kind"] == "gnu_strtab":
                return "ar_gnu_strtab(//)"
            return f"member_payload:{m['name']}"
    return "ar_padding"


def extract_cgu_temp_suffix(member_name: str) -> str | None:
    # Incremental CGU member names have the form:
    #   <crate>.<25-char-base36-cgu-hash>.<7-char-base36-invocation_temp>.rcgu.o
    m = re.match(r"^[^.]+\.[0-9a-z]{25}\.([0-9a-z]{7})\.rcgu\.o$", member_name)
    return m.group(1) if m else None


def classify_elf_leaks_by_section(obj_path: Path, needle: bytes) -> dict[str, int]:
    """Map every byte occurrence of `needle` inside an ELF object to its exact ELF section."""
    readelf = shutil.which("readelf")
    if not readelf:
        return {"readelf_unavailable": 1}
    proc = subprocess.run(
        [readelf, "-S", "-W", str(obj_path)],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        return {"readelf_failed": 1}
    sections: list[tuple[str, int, int]] = []
    # Matches rows like: [ 5] .rodata.str1.1 PROGBITS 0000000000000000 0002d0 000030 ...
    row_re = re.compile(r"^\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+[0-9a-fA-F]+\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+")
    for line in proc.stdout.splitlines():
        m = row_re.match(line)
        if m:
            sec_name = m.group(1)
            sec_off = int(m.group(2), 16)
            sec_sz = int(m.group(3), 16)
            if sec_sz > 0:
                sections.append((sec_name, sec_off, sec_off + sec_sz))

    data = obj_path.read_bytes()
    counts: dict[str, int] = {}
    idx = 0
    while True:
        idx = data.find(needle, idx)
        if idx == -1:
            break
        hit_sec = "<outside_sections>"
        for sec_name, start, end in sections:
            if start <= idx < end:
                hit_sec = sec_name
                break
        counts[hit_sec] = counts.get(hit_sec, 0) + 1
        idx += len(needle)
    return dict(sorted(counts.items()))


def inspect_dwarf_leaks(obj_path: Path, raw_dir: str) -> dict[str, Any]:
    """Classify path leak sites in an ELF object file by section and DWARF attribute."""
    by_section = classify_elf_leaks_by_section(obj_path, raw_dir.encode("ascii"))
    readelf = shutil.which("readelf")
    dwarf_attrs: dict[str, int] = {}
    if readelf:
        proc_info = subprocess.run(
            [readelf, "--debug-dump=info", str(obj_path)],
            capture_output=True,
            text=True,
            check=False,
        )
        if proc_info.returncode == 0:
            comp_dir_hits = 0
            at_name_hits = 0
            for line in proc_info.stdout.splitlines():
                if raw_dir in line:
                    if "DW_AT_comp_dir" in line:
                        comp_dir_hits += 1
                    elif "DW_AT_name" in line:
                        at_name_hits += 1
            dwarf_attrs["DW_AT_comp_dir"] = comp_dir_hits
            dwarf_attrs["DW_AT_name"] = at_name_hits
    return {"by_elf_section": by_section, "dwarf_info_attrs": dwarf_attrs}


def compile_lib(
    rustc: str,
    src_dir: Path,
    out_dir: Path,
    extra_args: list[str],
    pass_abs_src: bool = True,
) -> dict[str, Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    src_arg = str(src_dir / "lib.rs") if pass_abs_src else "lib.rs"
    cmd = [
        rustc,
        "--edition=2024",
        "--crate-type=rlib",
        "--crate-name=repro_lib",
        "--emit=metadata,obj,link",
        "-C",
        "opt-level=2",
        "--out-dir",
        str(out_dir),
        *extra_args,
        src_arg,
    ]
    run_cmd(cmd, cwd=src_dir)
    rmeta = out_dir / "librepro_lib.rmeta"
    rlib = out_dir / "librepro_lib.rlib"
    # With -C codegen-units=1, rustc emits repro_lib.o; with >1, it emits multiple .rcgu.o files.
    single_obj = out_dir / "repro_lib.o"
    objs = [single_obj] if single_obj.exists() else sorted(out_dir.glob("*.o"))
    return {"rmeta": rmeta, "rlib": rlib, "objs": objs}


def run_probe_1_cross_dir(rustc: str, root: Path) -> dict[str, Any]:
    dir_alpha = root / "dir_alpha"
    dir_beta = root / "dir_beta"
    for d in (dir_alpha, dir_beta):
        d.mkdir(parents=True, exist_ok=True)
        (d / "lib.rs").write_text(LIB_RS, encoding="utf-8")

    # Modes: (name, debuginfo, remap_path, remap_cwd, remap_scope, pass_abs_src)
    modes = [
        ("dbg0_no_remap", "0", False, False, None, True),
        ("dbg0_remap_path", "0", True, False, None, True),
        ("dbg0_remap_path_and_cwd", "0", True, True, None, True),
        ("dbg0_remap_cwd_only_relsrc", "0", False, True, None, False),
        ("dbg0_remap_cwd_only_abssrc", "0", False, True, None, True),
        ("dbg2_no_remap", "2", False, False, None, True),
        ("dbg2_remap_path_only", "2", True, False, None, True),
        ("dbg2_remap_path_and_cwd", "2", True, True, None, True),
        ("dbg2_remap_scope_object", "2", True, False, "object", True),
    ]

    results: dict[str, Any] = {}
    for name, dbg, use_remap_path, use_remap_cwd, scope, pass_abs in modes:
        out_a = root / "p1_out" / name / "alpha"
        out_b = root / "p1_out" / name / "beta"

        def make_args(d: Path) -> list[str]:
            args = ["-C", f"debuginfo={dbg}", "-C", "codegen-units=1"]
            if use_remap_path:
                args.append(f"--remap-path-prefix={d}=/repro")
            if use_remap_cwd:
                args.extend(["-Z", "remap-cwd-prefix=/repro"])
            if scope is not None:
                args.extend(["-Z", "unstable-options", f"--remap-path-scope={scope}"])
            return args

        res_a = compile_lib(rustc, dir_alpha, out_a, make_args(dir_alpha), pass_abs_src=pass_abs)
        res_b = compile_lib(rustc, dir_beta, out_b, make_args(dir_beta), pass_abs_src=pass_abs)

        obj_a = res_a["objs"][0]
        obj_b = res_b["objs"][0]

        h_a = {
            "rmeta": sha256_file(res_a["rmeta"]),
            "obj": sha256_file(obj_a),
            "rlib": sha256_file(res_a["rlib"]),
        }
        h_b = {
            "rmeta": sha256_file(res_b["rmeta"]),
            "obj": sha256_file(obj_b),
            "rlib": sha256_file(res_b["rlib"]),
        }
        # Count occurrences of the distinguishing directory basename (dir_alpha / dir_beta)
        leaks_a = {
            "rmeta": count_needle(res_a["rmeta"], b"dir_alpha"),
            "obj": count_needle(obj_a, b"dir_alpha"),
            "rlib": count_needle(res_a["rlib"], b"dir_alpha"),
        }
        leaks_b = {
            "rmeta": count_needle(res_b["rmeta"], b"dir_beta"),
            "obj": count_needle(obj_b, b"dir_beta"),
            "rlib": count_needle(res_b["rlib"], b"dir_beta"),
        }
        entry: dict[str, Any] = {
            "debuginfo": int(dbg),
            "remap_path_prefix": use_remap_path,
            "remap_cwd_prefix": use_remap_cwd,
            "remap_path_scope": scope or "all (default)",
            "source_arg_kind": "absolute" if pass_abs else "relative",
            "bit_exact": {
                "rmeta": h_a["rmeta"] == h_b["rmeta"],
                "obj": h_a["obj"] == h_b["obj"],
                "rlib": h_a["rlib"] == h_b["rlib"],
            },
            "leaks_alpha": leaks_a,
            "leaks_beta": leaks_b,
            "bytes_alpha": {
                "rmeta": res_a["rmeta"].stat().st_size,
                "obj": obj_a.stat().st_size,
                "rlib": res_a["rlib"].stat().st_size,
            },
            "bytes_beta": {
                "rmeta": res_b["rmeta"].stat().st_size,
                "obj": obj_b.stat().st_size,
                "rlib": res_b["rlib"].stat().st_size,
            },
            "hashes_alpha": h_a,
            "hashes_beta": h_b,
        }
        if name in ("dbg0_no_remap", "dbg2_no_remap"):
            entry["obj_leak_breakdown_alpha"] = inspect_dwarf_leaks(obj_a, "dir_alpha")
        results[name] = entry

    results["cross_mode_comparisons"] = {
        "dbg0_remap_path_vs_remap_path_and_cwd_obj_equal": (
            results["dbg0_remap_path"]["hashes_alpha"]["obj"]
            == results["dbg0_remap_path_and_cwd"]["hashes_alpha"]["obj"]
        ),
        "dbg0_remap_path_vs_remap_path_and_cwd_rmeta_equal": (
            results["dbg0_remap_path"]["hashes_alpha"]["rmeta"]
            == results["dbg0_remap_path_and_cwd"]["hashes_alpha"]["rmeta"]
        ),
        "dbg2_remap_path_only_vs_remap_path_and_cwd_obj_equal": (
            results["dbg2_remap_path_only"]["hashes_alpha"]["obj"]
            == results["dbg2_remap_path_and_cwd"]["hashes_alpha"]["obj"]
        ),
        "dbg2_remap_path_only_vs_remap_path_and_cwd_rmeta_equal": (
            results["dbg2_remap_path_only"]["hashes_alpha"]["rmeta"]
            == results["dbg2_remap_path_and_cwd"]["hashes_alpha"]["rmeta"]
        ),
    }
    return results


def run_probe_2_cgu_threads(rustc: str, root: Path) -> dict[str, Any]:
    src_dir = root / "p2_src"
    src_dir.mkdir(parents=True, exist_ok=True)
    (src_dir / "lib.rs").write_text(LIB_RS, encoding="utf-8")

    configs = [
        ("cgu1_t1", 1, 1),
        ("cgu16_t1", 16, 1),
        ("cgu16_t4", 16, 4),
    ]
    results: dict[str, Any] = {}
    for name, cgus, threads in configs:
        rlib_hashes: list[str] = []
        rmeta_hashes: list[str] = []
        obj_bundle_hashes: list[str] = []
        sample_ar: dict[str, Any] | None = None
        for run_idx in range(4):
            out_dir = root / "p2_out" / name / f"run_{run_idx}"
            args = [
                "-C",
                f"codegen-units={cgus}",
                "-Z",
                f"threads={threads}",
                f"--remap-path-prefix={src_dir}=/repro",
            ]
            res = compile_lib(rustc, src_dir, out_dir, args, pass_abs_src=True)
            rlib_bytes = res["rlib"].read_bytes()
            rlib_hashes.append(sha256_bytes(rlib_bytes))
            rmeta_hashes.append(sha256_file(res["rmeta"]))
            # Deterministic digest over all emitted .o files sorted by basename
            h = hashlib.sha256()
            for obj in sorted(res["objs"], key=lambda p: p.name):
                h.update(obj.name.encode("utf-8"))
                h.update(b"\0")
                h.update(obj.read_bytes())
            obj_bundle_hashes.append(h.hexdigest())
            if run_idx == 0:
                sample_ar = parse_gnu_ar(rlib_bytes)

        assert sample_ar is not None
        regular_members = [m for m in sample_ar["members"] if m["kind"] == "member"]
        rcgu_members = [m["name"] for m in regular_members if m["name"].endswith(".rcgu.o")]
        all_zero_meta = all(
            m["mtime"] == 0 and m["uid"] == 0 and m["gid"] == 0 and m["mode_octal"] == "100644"
            for m in regular_members
        ) or all(
            m["mtime"] == 0 and m["uid"] == 0 and m["gid"] == 0 and m["mode_octal"] == "644"
            for m in regular_members
        )
        results[name] = {
            "codegen_units": cgus,
            "threads": threads,
            "runs": 4,
            "unique_rlib_hashes": len(set(rlib_hashes)),
            "unique_rmeta_hashes": len(set(rmeta_hashes)),
            "unique_obj_bundle_hashes": len(set(obj_bundle_hashes)),
            "all_bit_exact": (
                len(set(rlib_hashes)) == 1
                and len(set(rmeta_hashes)) == 1
                and len(set(obj_bundle_hashes)) == 1
            ),
            "rlib_sha256": rlib_hashes[0],
            "rmeta_sha256": rmeta_hashes[0],
            "rlib_bytes": sample_ar["total_bytes"],
            "cgu_member_count": len(rcgu_members),
            "ar_members": [m["name"] for m in regular_members],
            "ar_member_headers": [
                {
                    "name": m["name"],
                    "mtime": m["mtime"],
                    "uid": m["uid"],
                    "gid": m["gid"],
                    "mode_octal": m["mode_octal"],
                    "size": m["size"],
                }
                for m in regular_members
            ],
            "all_ar_headers_deterministic_zero_epoch": all_zero_meta,
        }

    results["cgu16_t1_eq_cgu16_t4_rlib"] = (
        results["cgu16_t1"]["rlib_sha256"] == results["cgu16_t4"]["rlib_sha256"]
    )
    results["cgu16_t1_eq_cgu16_t4_rmeta"] = (
        results["cgu16_t1"]["rmeta_sha256"] == results["cgu16_t4"]["rmeta_sha256"]
    )
    return results


def run_probe_3_clean_vs_incremental(rustc: str, root: Path) -> dict[str, Any]:
    src_dir = root / "p3_src"
    src_dir.mkdir(parents=True, exist_ok=True)
    (src_dir / "lib.rs").write_text(LIB_RS, encoding="utf-8")

    incr_cache = root / "p3_incr_cache"
    incr_cache.mkdir(parents=True, exist_ok=True)

    base_args = [f"--remap-path-prefix={src_dir}=/repro", "-C", "codegen-units=1"]

    # 1. Clean (default MIR inline enabled at opt-level=2)
    clean_res = compile_lib(rustc, src_dir, root / "p3_out/clean", base_args)
    # 2. Clean with -Z inline-mir=no (isolates MIR Inline suppression from CGU naming)
    clean_noinline_res = compile_lib(
        rustc, src_dir, root / "p3_out/clean_noinline", [*base_args, "-Z", "inline-mir=no"]
    )
    # 3. Incremental cold (populates incr_cache)
    incr_cold_res = compile_lib(
        rustc, src_dir, root / "p3_out/incr_cold", [*base_args, "-C", f"incremental={incr_cache}"]
    )
    # 4. Incremental warm #1 (reuses incr_cache, identical source)
    incr_warm1_res = compile_lib(
        rustc, src_dir, root / "p3_out/incr_warm1", [*base_args, "-C", f"incremental={incr_cache}"]
    )
    # 5. Incremental warm #2 (second warm reuse to observe fresh invocation_temp draw)
    incr_warm2_res = compile_lib(
        rustc, src_dir, root / "p3_out/incr_warm2", [*base_args, "-C", f"incremental={incr_cache}"]
    )
    # 6. Incremental cold with forced -Z inline-mir=yes (in a separate cache dir)
    incr_inline_cache = root / "p3_incr_inline_cache"
    incr_inline_cache.mkdir(parents=True, exist_ok=True)
    incr_force_inline_res = compile_lib(
        rustc,
        src_dir,
        root / "p3_out/incr_force_inline",
        [*base_args, "-C", f"incremental={incr_inline_cache}", "-Z", "inline-mir=yes"],
    )

    def summarize(res: dict[str, Path]) -> tuple[dict[str, Any], bytes, dict[str, Any]]:
        rlib_bytes = res["rlib"].read_bytes()
        rmeta_bytes = res["rmeta"].read_bytes()
        parsed = parse_gnu_ar(rlib_bytes)
        reg = [m for m in parsed["members"] if m["kind"] == "member"]
        rcgu_objs = [m for m in reg if m["name"].endswith(".rcgu.o")]
        info = {
            "rlib_bytes": len(rlib_bytes),
            "rmeta_bytes": len(rmeta_bytes),
            "rlib_sha256": sha256_bytes(rlib_bytes),
            "rmeta_sha256": sha256_bytes(rmeta_bytes),
            "ar_members": [m["name"] for m in reg],
            "rcgu_member_payload_sha256s": [m["payload_sha256"] for m in rcgu_objs],
            "rcgu_member_sizes": [m["size"] for m in rcgu_objs],
            "rmeta_member_payload_sha256": next(
                (m["payload_sha256"] for m in reg if m["name"] == "lib.rmeta"), None
            ),
            "rmeta_link_member_payload_sha256": next(
                (m["payload_sha256"] for m in reg if m["name"] == "lib.rmeta-link"), None
            ),
            "invocation_temp_suffixes": [
                extract_cgu_temp_suffix(m["name"]) for m in rcgu_objs
            ],
        }
        return info, rlib_bytes, parsed

    clean_info, clean_bytes, _ = summarize(clean_res)
    clean_noinline_info, _, _ = summarize(clean_noinline_res)
    cold_info, cold_bytes, cold_parsed = summarize(incr_cold_res)
    warm1_info, warm1_bytes, warm1_parsed = summarize(incr_warm1_res)
    warm2_info, warm2_bytes, warm2_parsed = summarize(incr_warm2_res)
    incr_finline_info, _, _ = summarize(incr_force_inline_res)

    def diff_rlibs(b1: bytes, p1: dict[str, Any], b2: bytes, p2: dict[str, Any]) -> dict[str, Any]:
        same_len = len(b1) == len(b2)
        if not same_len:
            return {"same_length": False, "len_a": len(b1), "len_b": len(b2)}
        diffs = [i for i in range(len(b1)) if b1[i] != b2[i]]
        by_region: dict[str, int] = {}
        for off in diffs:
            reg = classify_offset(p1, off)
            by_region[reg] = by_region.get(reg, 0) + 1
        # Extract suffixes and Hamming distance across all CGUs
        s1 = [extract_cgu_temp_suffix(m["name"]) for m in p1["members"] if m["name"].endswith(".rcgu.o")]
        s2 = [extract_cgu_temp_suffix(m["name"]) for m in p2["members"] if m["name"].endswith(".rcgu.o")]
        hamming_sum = None
        if s1 and len(s1) == len(s2) and all(a and b and len(a) == len(b) for a, b in zip(s1, s2)):
            hamming_sum = sum(
                sum(c1 != c2 for c1, c2 in zip(a, b))
                for a, b in zip(s1, s2)
            )
        return {
            "same_length": True,
            "total_bytes": len(b1),
            "cgu_count": len(s1),
            "diff_byte_count": len(diffs),
            "diff_offsets": diffs[:40],
            "diff_offsets_truncated": len(diffs) > 40,
            "diff_bytes_by_region": by_region,
            "suffix_a": s1,
            "suffix_b": s2,
            "unique_suffixes_a": sorted(set(x for x in s1 if x)),
            "unique_suffixes_b": sorted(set(x for x in s2 if x)),
            "suffix_hamming_sum": hamming_sum,
            "expected_2x_hamming_matches_diff": (hamming_sum is not None and len(diffs) == 2 * hamming_sum),
        }

    # Also test multi-CGU incremental (-C codegen-units=16) to verify 2 * M * d_H scaling
    incr_cgu16_cache = root / "p3_incr_cgu16_cache"
    incr_cgu16_cache.mkdir(parents=True, exist_ok=True)
    cgu16_args = [f"--remap-path-prefix={src_dir}=/repro", "-C", "codegen-units=16", "-C", f"incremental={incr_cgu16_cache}"]
    incr16_cold_res = compile_lib(rustc, src_dir, root / "p3_out/incr16_cold", cgu16_args)
    incr16_warm_res = compile_lib(rustc, src_dir, root / "p3_out/incr16_warm", cgu16_args)
    incr16_cold_info, incr16_cold_bytes, incr16_cold_parsed = summarize(incr16_cold_res)
    incr16_warm_info, incr16_warm_bytes, incr16_warm_parsed = summarize(incr16_warm_res)

    return {
        "clean": clean_info,
        "clean_no_mir_inline": clean_noinline_info,
        "incr_cold": cold_info,
        "incr_warm1": warm1_info,
        "incr_warm2": warm2_info,
        "incr_force_mir_inline": incr_finline_info,
        "incr_cgu16_cold": incr16_cold_info,
        "incr_cgu16_warm": incr16_warm_info,
        "comparisons": {
            "clean_eq_incr_cold_rlib": clean_info["rlib_sha256"] == cold_info["rlib_sha256"],
            "clean_eq_incr_cold_rmeta": clean_info["rmeta_sha256"] == cold_info["rmeta_sha256"],
            "clean_eq_incr_cold_obj_payload": (
                clean_info["rcgu_member_payload_sha256s"] == cold_info["rcgu_member_payload_sha256s"]
            ),
            "clean_noinline_eq_incr_cold_rmeta": (
                clean_noinline_info["rmeta_sha256"] == cold_info["rmeta_sha256"]
            ),
            "clean_noinline_eq_incr_cold_obj_payload": (
                clean_noinline_info["rcgu_member_payload_sha256s"]
                == cold_info["rcgu_member_payload_sha256s"]
            ),
            "clean_eq_incr_force_inline_rmeta": (
                clean_info["rmeta_sha256"] == incr_finline_info["rmeta_sha256"]
            ),
            "incr_cold_eq_incr_warm1_rlib": cold_info["rlib_sha256"] == warm1_info["rlib_sha256"],
            "incr_cold_eq_incr_warm1_rmeta": cold_info["rmeta_sha256"] == warm1_info["rmeta_sha256"],
            "incr_cold_eq_incr_warm1_obj_payload": (
                cold_info["rcgu_member_payload_sha256s"] == warm1_info["rcgu_member_payload_sha256s"]
            ),
            "incr_warm1_eq_incr_warm2_obj_payload": (
                warm1_info["rcgu_member_payload_sha256s"] == warm2_info["rcgu_member_payload_sha256s"]
            ),
            "incr_cold_vs_warm1_byte_diff": diff_rlibs(cold_bytes, cold_parsed, warm1_bytes, warm1_parsed),
            "incr_cold_vs_warm2_byte_diff": diff_rlibs(cold_bytes, cold_parsed, warm2_bytes, warm2_parsed),
            "incr_warm1_vs_warm2_byte_diff": diff_rlibs(warm1_bytes, warm1_parsed, warm2_bytes, warm2_parsed),
            "incr_cgu16_cold_eq_warm_rmeta": incr16_cold_info["rmeta_sha256"] == incr16_warm_info["rmeta_sha256"],
            "incr_cgu16_cold_eq_warm_obj_payloads": (
                incr16_cold_info["rcgu_member_payload_sha256s"] == incr16_warm_info["rcgu_member_payload_sha256s"]
            ),
            "incr_cgu16_cold_eq_warm_rlib": incr16_cold_info["rlib_sha256"] == incr16_warm_info["rlib_sha256"],
            "incr_cgu16_cold_vs_warm_byte_diff": diff_rlibs(
                incr16_cold_bytes, incr16_cold_parsed, incr16_warm_bytes, incr16_warm_parsed
            ),
        },
    }


def run_probe_4_linked_elf(rustc: str, root: Path) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for label in ("alpha", "beta"):
        d = root / f"elf_dir_{label}"
        d.mkdir(parents=True, exist_ok=True)
        (d / "lib.rs").write_text(LIB_RS, encoding="utf-8")
        (d / "main.rs").write_text(BIN_RS, encoding="utf-8")
        out_dir = d / "out"
        out_dir.mkdir(parents=True, exist_ok=True)

        # Build library
        run_cmd(
            [
                rustc,
                "--edition=2024",
                "--crate-type=rlib",
                "--crate-name=repro_lib",
                "-C",
                "opt-level=2",
                "-C",
                "debuginfo=2",
                "-C",
                "codegen-units=1",
                f"--remap-path-prefix={d}=/repro",
                "-o",
                str(out_dir / "librepro_lib.rlib"),
                str(d / "lib.rs"),
            ],
            cwd=d,
        )
        # Build and link binary
        bin_path = out_dir / "repro_bin"
        run_cmd(
            [
                rustc,
                "--edition=2024",
                "--crate-type=bin",
                "--crate-name=repro_bin",
                "-C",
                "opt-level=2",
                "-C",
                "debuginfo=2",
                "-C",
                "codegen-units=1",
                f"--remap-path-prefix={d}=/repro",
                "--extern",
                f"repro_lib={out_dir / 'librepro_lib.rlib'}",
                "-o",
                str(bin_path),
                str(d / "main.rs"),
            ],
            cwd=d,
        )
        run_out = run_cmd([str(bin_path)], cwd=d)
        leaks = count_needle(bin_path, f"elf_dir_{label}".encode("ascii"))
        out[label] = {
            "elf_bytes": bin_path.stat().st_size,
            "elf_sha256": sha256_file(bin_path),
            "rlib_sha256": sha256_file(out_dir / "librepro_lib.rlib"),
            "leaks": leaks,
            "run_stdout": run_out.stdout.strip(),
        }

    out["elf_bit_exact"] = out["alpha"]["elf_sha256"] == out["beta"]["elf_sha256"]
    out["rlib_bit_exact"] = out["alpha"]["rlib_sha256"] == out["beta"]["rlib_sha256"]
    out["stdout_equal"] = out["alpha"]["run_stdout"] == out["beta"]["run_stdout"]
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=None, help="Write JSON results to this file")
    args = parser.parse_args()

    rustc = find_rustc()
    rustc_ver = run_cmd([rustc, "--version", "-v"]).stdout.strip()
    ar_ver = run_cmd(["ar", "--version"]).stdout.splitlines()[0].strip()

    with tempfile.TemporaryDirectory(prefix="rustc_repro_probe_") as tmp:
        root = Path(tmp)
        payload = {
            "rustc_version_verbose": rustc_ver,
            "ar_version": ar_ver,
            "probe_1_cross_dir_determinism": run_probe_1_cross_dir(rustc, root),
            "probe_2_cgu_and_threads_repeatability": run_probe_2_cgu_threads(rustc, root),
            "probe_3_clean_vs_incremental": run_probe_3_clean_vs_incremental(rustc, root),
            "probe_4_linked_elf_repro": run_probe_4_linked_elf(rustc, root),
        }

    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
