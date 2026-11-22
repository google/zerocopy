#!/usr/bin/env python3
"""Standalone empirical probe of rustc version stamping, RUSTC_OVERRIDE_VERSION_STRING,
CAS argv[0] symlink vs dladdr sysroot discovery (including the CWD relative_target_rustlib_path bug),
and .rmeta version/SVH coupling."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import struct
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def resolve_real_rustc(explicit_rustc: str | None = None) -> Path:
    cmd = [explicit_rustc] if explicit_rustc else ["rustc"]
    sysroot = subprocess.check_output([*cmd, "--print", "sysroot"], text=True).strip()
    real_rustc = Path(sysroot) / "bin" / "rustc"
    if not real_rustc.is_file():
        raise FileNotFoundError(f"Missing {real_rustc}")
    return real_rustc


def sanitize_paths(
    text: str,
    *,
    rustup_home: Path,
    real_sysroot: Path,
    tmp: Path | None = None,
) -> str:
    if tmp is not None:
        text = text.replace(str(tmp), "<TMPDIR>")
    text = text.replace(str(rustup_home), "<RUSTUP_HOME>")
    text = text.replace(str(real_sysroot), "<SYSROOT>")
    text = text.replace(str(Path.home()), "<HOME>")
    return text


def run_probe(explicit_rustc: str | None = None) -> tuple[dict[str, Any], Path, Path]:
    real_rustc = resolve_real_rustc(explicit_rustc)
    real_sysroot = real_rustc.parent.parent
    rustup_home = Path(os.environ.get("RUSTUP_HOME", Path.home() / ".rustup"))
    results: dict[str, Any] = {}

    # 1. Inspect default rustc -vV vs RUSTC_OVERRIDE_VERSION_STRING
    vv_default = subprocess.check_output([str(real_rustc), "-vV"], text=True)
    env_override = os.environ.copy()
    env_override["RUSTC_OVERRIDE_VERSION_STRING"] = "1.99.0-monorepo-custom (deadbeef 2026-11-22)"
    vv_override = subprocess.check_output([str(real_rustc), "-vV"], env=env_override, text=True)
    results["rustc_path"] = sanitize_paths(
        str(real_rustc), rustup_home=rustup_home, real_sysroot=real_sysroot
    )
    results["vv_default"] = vv_default.strip().splitlines()
    results["vv_override"] = vv_override.strip().splitlines()

    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        clean_cwd = tmp / "clean_cwd"
        clean_cwd.mkdir()

        # 2. Test RBE CAS symlink vs dereferenced copy sysroot resolution (filesearch.rs)
        # Case 2a: argv[0] is a symlink inside a CAS tree WITH lib/rustlib, invoked from clean_cwd.
        # Because filesearch.rs calls rustc_target::relative_target_rustlib_path(&p, "dummy")
        # which returns RELATIVE "lib/rustlib/dummy" without joining onto `p`, `rustlib_path.exists()`
        # checks `./lib/rustlib` in CWD instead of `p/lib/rustlib`. Thus from clean_cwd it fails to
        # detect the CAS sysroot and falls back to dladdr(librustc_driver.so).
        cas_with_rustlib = tmp / "cas_with_rustlib"
        (cas_with_rustlib / "bin").mkdir(parents=True)
        (cas_with_rustlib / "lib" / "rustlib").mkdir(parents=True)
        os.symlink(real_rustc, cas_with_rustlib / "bin" / "rustc")
        sysroot_2a = subprocess.check_output(
            [str(cas_with_rustlib / "bin" / "rustc"), "--print", "sysroot"],
            cwd=str(clean_cwd),
            text=True,
        ).strip()

        # Case 2b: A CAS symlink tree WITHOUT lib/rustlib, invoked from a CWD containing `./lib/rustlib`.
        # `rustlib_path.exists()` stats `CWD/lib/rustlib` -> True -> returns `cas_no_rustlib`.
        cwd_with_lib_rustlib = tmp / "cwd_with_lib_rustlib"
        (cwd_with_lib_rustlib / "lib" / "rustlib").mkdir(parents=True)
        cas_no_rustlib = tmp / "cas_no_rustlib"
        (cas_no_rustlib / "bin").mkdir(parents=True)
        os.symlink(real_rustc, cas_no_rustlib / "bin" / "rustc")
        sysroot_2b_clean_cwd = subprocess.check_output(
            [str(cas_no_rustlib / "bin" / "rustc"), "--print", "sysroot"],
            cwd=str(clean_cwd),
            text=True,
        ).strip()
        sysroot_2b_poisoned_cwd = subprocess.check_output(
            [str(cas_no_rustlib / "bin" / "rustc"), "--print", "sysroot"],
            cwd=str(cwd_with_lib_rustlib),
            text=True,
        ).strip()

        # Case 2c: argv[0] is a regular file (as materialized by RBE when symlinks are dereferenced).
        # `fs::read_link(&p)` fails -> `from_env_args_next()` returns None even if CWD has lib/rustlib,
        # falling back to `dladdr(librustc_driver.so)` + `try_canonicalize`.
        cas_regular = tmp / "cas_regular"
        (cas_regular / "bin").mkdir(parents=True)
        (cas_regular / "lib" / "rustlib").mkdir(parents=True)
        shutil.copy2(real_rustc, cas_regular / "bin" / "rustc")
        for item in (real_sysroot / "lib").iterdir():
            if item.name == "rustlib":
                continue
            os.symlink(item, cas_regular / "lib" / item.name)
        sysroot_2c = subprocess.check_output(
            [str(cas_regular / "bin" / "rustc"), "--print", "sysroot"],
            cwd=str(cwd_with_lib_rustlib),
            text=True,
        ).strip()

        results["sysroot_discovery"] = {
            "real_sysroot": sanitize_paths(
                str(real_sysroot), rustup_home=rustup_home, real_sysroot=real_sysroot, tmp=tmp
            ),
            "case_2a_cas_symlink_with_lib_rustlib_from_clean_cwd": sanitize_paths(
                sysroot_2a, rustup_home=rustup_home, real_sysroot=real_sysroot, tmp=tmp
            ),
            "case_2a_fell_back_to_dladdr_due_to_relative_path_bug": (
                Path(sysroot_2a).resolve() == real_sysroot.resolve()
            ),
            "case_2b_cas_symlink_without_rustlib_from_clean_cwd": sanitize_paths(
                sysroot_2b_clean_cwd, rustup_home=rustup_home, real_sysroot=real_sysroot, tmp=tmp
            ),
            "case_2b_cas_symlink_without_rustlib_from_cwd_with_lib_rustlib": sanitize_paths(
                sysroot_2b_poisoned_cwd, rustup_home=rustup_home, real_sysroot=real_sysroot, tmp=tmp
            ),
            "case_2b_cwd_hijacked_sysroot_to_cas_dir": (sysroot_2b_poisoned_cwd == str(cas_no_rustlib)),
            "case_2c_regular_bin_with_symlinked_libs": sanitize_paths(
                sysroot_2c, rustup_home=rustup_home, real_sysroot=real_sysroot, tmp=tmp
            ),
            "case_2c_canonicalized_dladdr_to_real_sysroot": (
                Path(sysroot_2c).resolve() == real_sysroot.resolve()
            ),
        }

        # 3. Inspect .rmeta binary header (METADATA_HEADER, Svh, rustc_version string) & simulate E0514
        dep_rs = tmp / "dep.rs"
        dep_rs.write_text('#![crate_type = "rlib"]\npub fn add(a: u32, b: u32) -> u32 { a + b }\n', encoding="utf-8")
        rmeta_path = tmp / "libdep.rmeta"
        subprocess.run(
            [str(real_rustc), "--edition=2021", "--emit=metadata", "-o", str(rmeta_path), str(dep_rs)],
            check=True,
        )
        raw = bytearray(rmeta_path.read_bytes())
        magic = bytes(raw[0:8])
        root_pos = struct.unpack_from("<Q", raw, 8)[0]
        unhashed_pos = struct.unpack_from("<Q", raw, 16)[0]
        svh_hex = bytes(raw[24:40]).hex()
        rustc_ver_idx = raw.find(b"rustc ")
        end_idx = rustc_ver_idx
        while end_idx < len(raw) and 32 <= raw[end_idx] < 127:
            end_idx += 1
        embedded_ver_str = raw[rustc_ver_idx:end_idx].decode("ascii")

        # Verify that RUSTC_OVERRIDE_VERSION_STRING does NOT alter .rmeta's embedded CFG_VERSION
        rmeta_override_path = tmp / "libdep_override.rmeta"
        subprocess.run(
            [str(real_rustc), "--edition=2021", "--emit=metadata", "-o", str(rmeta_override_path), str(dep_rs)],
            env=env_override,
            check=True,
        )
        raw_ovr = rmeta_override_path.read_bytes()
        ovr_idx = raw_ovr.find(b"rustc ")
        ovr_end = ovr_idx
        while ovr_end < len(raw_ovr) and 32 <= raw_ovr[ovr_end] < 127:
            ovr_end += 1
        ovr_ver_str = raw_ovr[ovr_idx:ovr_end].decode("ascii")

        tampered = bytearray(raw)
        flip_pos = end_idx - 2
        tampered[flip_pos] = ord("X") if tampered[flip_pos] != ord("X") else ord("Y")
        tampered_rmeta = tmp / "libdep_tampered.rmeta"
        tampered_rmeta.write_bytes(tampered)

        user_rs = tmp / "user.rs"
        user_rs.write_text('#![crate_type = "rlib"]\npub fn call() -> u32 { dep::add(1, 2) }\n', encoding="utf-8")
        proc_mismatch = subprocess.run(
            [
                str(real_rustc),
                "--edition=2021",
                "--emit=metadata",
                "--extern",
                f"dep={tampered_rmeta}",
                "-o",
                str(tmp / "libuser.rmeta"),
                str(user_rs),
            ],
            capture_output=True,
            text=True,
        )

        results["rmeta_header_probe"] = {
            "rmeta_size_bytes": len(raw),
            "magic_bytes_hex": magic.hex(),
            "metadata_version": magic[7],
            "root_pos": root_pos,
            "unhashed_pos": unhashed_pos,
            "svh_128bit_le_hex": svh_hex,
            "embedded_rustc_version": embedded_ver_str,
            "rmeta_with_RUSTC_OVERRIDE_VERSION_STRING": ovr_ver_str,
            "override_env_affects_rmeta": (ovr_ver_str != embedded_ver_str),
            "embedded_version_offset": rustc_ver_idx,
            "version_mismatch_exit_code": proc_mismatch.returncode,
            "version_mismatch_stderr_first_lines": [
                sanitize_paths(ln, rustup_home=rustup_home, real_sysroot=real_sysroot, tmp=tmp)
                for ln in proc_mismatch.stderr.strip().splitlines()[:8]
            ],
        }

    return results, rustup_home, real_sysroot


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rustc",
        type=str,
        default=None,
        help="Optional rustc executable path (defaults to active `rustc --print sysroot`).",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_suffix(".json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()
    res, _, _ = run_probe(args.rustc)
    serialized = json.dumps(res, indent=2) + "\n"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(serialized, encoding="utf-8")
    print(serialized, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
