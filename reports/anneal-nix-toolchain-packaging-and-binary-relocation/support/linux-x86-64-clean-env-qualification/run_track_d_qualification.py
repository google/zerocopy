#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Track D qualification probe for Q-D1 (--manifest-path) and Q-D2 (8 -> 7 -> 6 host SONAMEs)."""

import json
import re
import subprocess
import time
from pathlib import Path

TRACK_D = Path(__file__).resolve().parent
TASK4_DIR = TRACK_D.parent.parent / "mvp-investigations" / "task4"
FIXTURES_DIR = TASK4_DIR / "work" / "fixtures"
HOME_BASELINE = TRACK_D / "home_baseline"
HOME_HARDENED = TRACK_D / "home_hardened"
TC_HASH = "e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a"

ALL_8_HOST_LIBS = [
    ("/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2", "/lib64/ld-linux-x86-64.so.2"),
    ("/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2", "/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2"),
    ("/usr/lib/x86_64-linux-gnu/libc.so.6", "/lib/x86_64-linux-gnu/libc.so.6"),
    ("/usr/lib/x86_64-linux-gnu/libm.so.6", "/lib/x86_64-linux-gnu/libm.so.6"),
    ("/usr/lib/x86_64-linux-gnu/libpthread.so.0", "/lib/x86_64-linux-gnu/libpthread.so.0"),
    ("/usr/lib/x86_64-linux-gnu/libdl.so.2", "/lib/x86_64-linux-gnu/libdl.so.2"),
    ("/usr/lib/x86_64-linux-gnu/librt.so.1", "/lib/x86_64-linux-gnu/librt.so.1"),
    ("/usr/lib/x86_64-linux-gnu/libgcc_s.so.1", "/lib/x86_64-linux-gnu/libgcc_s.so.1"),
    ("/usr/lib/x86_64-linux-gnu/libz.so.1.3.2", "/lib/x86_64-linux-gnu/libz.so.1"),
]


def scrub_command(cmd):
    """Replace host-specific paths in command arrays with portable placeholders."""
    out = []
    for tok in cmd:
        s = str(tok)
        if str(TRACK_D) in s:
            s = s.replace(str(TRACK_D), "<track_d>")
        if str(TASK4_DIR) in s:
            s = s.replace(str(TASK4_DIR), "<task4>")
        out.append(s)
    return out


def readelf_dynamic_summary(path: Path, label: str, preserve_rustup=False):
    out_d = subprocess.run(
        ["readelf", "-dW", str(path)], capture_output=True, text=True, check=True
    ).stdout
    needed = []
    rpath = []
    runpath = []
    soname = None
    raw_lines = []
    for line in out_d.splitlines():
        if any(k in line for k in ["(NEEDED)", "(RPATH)", "(RUNPATH)", "(SONAME)"]):
            clean_line = line.strip()
            if not preserve_rustup:
                clean_line = re.sub(
                    r"/[^\s\[\]]+/\.rustup/", "<host_home>/.rustup/", clean_line
                )
            raw_lines.append(clean_line)
        if "(NEEDED)" in line:
            m = re.search(r"Shared library:\s*\[(.+?)\]", line)
            if m:
                needed.append(m.group(1))
        elif "(RPATH)" in line:
            m = re.search(r"Library rpath:\s*\[(.+?)\]", line)
            if m:
                rpath.append(m.group(1))
        elif "(RUNPATH)" in line:
            m = re.search(r"Library runpath:\s*\[(.+?)\]", line)
            if m:
                val = m.group(1)
                if not preserve_rustup:
                    val = re.sub(r"^/[^\s:]+/\.rustup/", "<host_home>/.rustup/", val)
                runpath.append(val)
        elif "(SONAME)" in line:
            m = re.search(r"Library soname:\s*\[(.+?)\]", line)
            if m:
                soname = m.group(1)

    has_nix_store_str = b"/nix/store/" in path.read_bytes()
    return {
        "label": label,
        "soname": soname,
        "dt_needed": needed,
        "dt_rpath": rpath,
        "dt_runpath": runpath,
        "contains_nix_store_bytes": has_nix_store_str,
        "readelf_d_relevant_lines": raw_lines,
    }


def bwrap_minimal(home_dir: Path, cli_bin: Path, exclude_dests=()):
    cmd = [
        "bwrap",
        "--die-with-parent",
        "--unshare-all",
        "--tmpfs", "/",
        "--dir", "/lib64",
        "--dir", "/lib/x86_64-linux-gnu",
        "--dir", "/usr/bin",
        "--dir", "/bin",
        "--proc", "/proc",
        "--dev", "/dev",
        "--tmpfs", "/tmp",
        "--bind", str(home_dir), "/tmp/clean-home",
        "--ro-bind", str(cli_bin), "/work/cargo-anneal",
        "--ro-bind", str(FIXTURES_DIR), "/work/fixtures",
        "--chdir", "/work",
        "--clearenv",
        "--setenv", "HOME", "/tmp/clean-home",
        "--setenv", "PATH", "",
    ]
    mounted_sonames = []
    for src, dst in ALL_8_HOST_LIBS:
        if dst in exclude_dests:
            continue
        cmd.extend(["--ro-bind", src, dst])
        soname = Path(dst).name
        if soname not in mounted_sonames:
            mounted_sonames.append(soname)
    return cmd, mounted_sonames


def run_check(check_id: str, desc: str, cmd: list, mounted_sonames: list):
    print(f"[{check_id}] {desc} ({len(mounted_sonames)} host SONAMEs)...", flush=True)
    t0 = time.monotonic()
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    elapsed_ms = int((time.monotonic() - t0) * 1000)
    print(f"  -> exit={proc.returncode} ({elapsed_ms} ms)", flush=True)
    parsed_json = None
    stdout_strip = proc.stdout.strip()
    if stdout_strip.startswith("{") and stdout_strip.endswith("}"):
        try:
            parsed_json = json.loads(stdout_strip)
        except Exception:
            pass
    compact_receipt = None
    if isinstance(parsed_json, dict):
        compact_receipt = {
            k: v
            for k, v in parsed_json.items()
            if k
            in (
                "schema_version",
                "status",
                "phase",
                "detail",
                "request_sha256",
                "capture_sha256",
                "capture_binary_sha256",
                "model_manifest_sha256",
                "specification_manifest_sha256",
                "scope",
                "selected",
                "timing_ms",
            )
        }
        if "audit" in parsed_json and isinstance(parsed_json["audit"], dict):
            compact_receipt["audit_summary"] = {
                k: parsed_json["audit"].get(k)
                for k in (
                    "axioms",
                    " bindings",
                    "canonicalRoot",
                    "exactType",
                    "expected",
                    "subject",
                    "theorem",
                    "toolchain",
                )
                if k in parsed_json["audit"]
            }
            compact_receipt["audit_summary"]["bindings"] = parsed_json["audit"].get("bindings")

    return {
        "check_id": check_id,
        "description": desc,
        "host_soname_count": len(mounted_sonames),
        "host_sonames": mounted_sonames,
        "command": scrub_command(cmd),
        "exit_code": proc.returncode,
        "elapsed_ms": elapsed_ms,
        "stdout": proc.stdout if parsed_json is None else "<json_receipt>",
        "stderr": proc.stderr,
        "receipt": compact_receipt,
    }


def main():
    tc_base = HOME_BASELINE / ".cache" / "anneal" / "toolchain" / TC_HASH
    tc_hard = HOME_HARDENED / ".cache" / "anneal" / "toolchain" / TC_HASH
    cli_orig = TASK4_DIR / "cargo-anneal"
    cli_patched = TRACK_D / "cargo-anneal-patched"
    cli_rpath = TRACK_D / "cargo-anneal-rpath-bundle"

    elf_headers = {
        "before_hardening": [
            readelf_dynamic_summary(cli_orig, "cargo-anneal (unpatched host build)", preserve_rustup=True),
            readelf_dynamic_summary(tc_base / "bin/anneal-rustc-capture", "bin/anneal-rustc-capture (unhardened)"),
            readelf_dynamic_summary(tc_base / "rust/bin/cargo", "rust/bin/cargo"),
            readelf_dynamic_summary(tc_base / "rust/bin/rustc", "rust/bin/rustc"),
            readelf_dynamic_summary(tc_base / "rust/lib/librustc_driver-5d5a3c5207375ffc.so", "rust/lib/librustc_driver-5d5a3c5207375ffc.so"),
            readelf_dynamic_summary(tc_base / "rust/lib/libLLVM.so.22.1-rust-1.98.0-nightly", "rust/lib/libLLVM.so.22.1-rust-1.98.0-nightly"),
            readelf_dynamic_summary(tc_base / "lean/bin/lean", "lean/bin/lean"),
            readelf_dynamic_summary(tc_base / "lean/lib/libz.so.1.2.11", "lean/lib/libz.so.1.2.11 (unhardened)"),
            readelf_dynamic_summary(tc_base / "lean/lib/libgcc_s.so.1", "lean/lib/libgcc_s.so.1 (unhardened)"),
            readelf_dynamic_summary(tc_base / "lean/lib/libatomic.so.1.2.0", "lean/lib/libatomic.so.1.2.0 (unhardened)"),
        ],
        "after_hardening": [
            readelf_dynamic_summary(cli_patched, "cargo-anneal-patched (7-SONAME / 8-SONAME CLI, zero DT_RUNPATH)"),
            readelf_dynamic_summary(cli_rpath, "cargo-anneal-rpath-bundle (6-SONAME CLI, resolves libgcc_s.so.1 from bundle)"),
            readelf_dynamic_summary(tc_hard / "bin/anneal-rustc-capture", "bin/anneal-rustc-capture (hardened DT_RUNPATH)"),
            readelf_dynamic_summary(tc_hard / "lean/lib/libz.so.1.2.11", "lean/lib/libz.so.1.2.11 (hardened, /nix/store stripped)"),
            readelf_dynamic_summary(tc_hard / "lean/lib/libgcc_s.so.1", "lean/lib/libgcc_s.so.1 (hardened, /nix/store stripped)"),
            readelf_dynamic_summary(tc_hard / "lean/lib/libatomic.so.1.2.0", "lean/lib/libatomic.so.1.2.0 (hardened, /nix/store stripped)"),
        ],
        "rust_lib_symlinks_added": {
            "rust/lib/libz.so.1": "../../lean/lib/libz.so.1.2.11",
            "rust/lib/libgcc_s.so.1": "../../lean/lib/libgcc_s.so.1",
        },
    }

    checks = []

    # --- Q-D1: 8-SONAME Ultra-Minimal Rootfs with PATH="" and 0 host binaries ---
    cmd_base, sonames_8 = bwrap_minimal(HOME_BASELINE, cli_patched, exclude_dests=())
    r_d1_1 = run_check(
        "D1.1",
        "Patched cargo-anneal verify --manifest-path scalar-cargo in 8-SONAME ultra-minimal rootfs (PATH='', 0 host binaries)",
        cmd_base + [
            "/work/cargo-anneal", "verify",
            "--manifest-path", "/work/fixtures/scalar-cargo/rust/Cargo.toml",
            "--proof-dir", "/work/fixtures/scalar-cargo/lean",
        ],
        sonames_8,
    )
    assert r_d1_1["exit_code"] == 0 and r_d1_1["receipt"]["status"] == "crate_verified", r_d1_1
    checks.append(r_d1_1)

    r_d1_2 = run_check(
        "D1.2",
        "Direct bundled cargo metadata --no-deps --offline in 8-SONAME ultra-minimal rootfs (PATH='', no RUSTC env var)",
        cmd_base + [
            f"/tmp/clean-home/.cache/anneal/toolchain/{TC_HASH}/rust/bin/cargo",
            "metadata", "--format-version=1", "--no-deps", "--offline",
            "--manifest-path", "/work/fixtures/scalar-cargo/rust/Cargo.toml",
        ],
        sonames_8,
    )
    assert r_d1_2["exit_code"] == 0, r_d1_2
    checks.append(r_d1_2)

    # --- Q-D2 (7 Host SONAMEs: libz.so.1 removed from host) ---
    no_libz = ("/lib/x86_64-linux-gnu/libz.so.1",)
    cmd_7_unhard, sonames_7 = bwrap_minimal(HOME_BASELINE, cli_patched, exclude_dests=no_libz)
    r_d2_7_0 = run_check(
        "D2-7.0",
        "Negative control: unhardened bundle in 7-SONAME rootfs (libz.so.1 absent from host)",
        cmd_7_unhard + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/scalar-pos/request.json"],
        sonames_7,
    )
    assert r_d2_7_0["exit_code"] == 2 and "libz.so.1" in r_d2_7_0["receipt"]["detail"], r_d2_7_0
    checks.append(r_d2_7_0)

    cmd_7_hard, _ = bwrap_minimal(HOME_HARDENED, cli_patched, exclude_dests=no_libz)
    r_d2_7_1 = run_check(
        "D2-7.1",
        "Hardened bundle in 7-SONAME rootfs: scalar-pos verify --request (crate_verified)",
        cmd_7_hard + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/scalar-pos/request.json"],
        sonames_7,
    )
    assert r_d2_7_1["exit_code"] == 0 and r_d2_7_1["receipt"]["status"] == "crate_verified", r_d2_7_1
    checks.append(r_d2_7_1)

    r_d2_7_2 = run_check(
        "D2-7.2",
        "Hardened bundle in 7-SONAME rootfs: scalar-mut verify --request (proof_failed)",
        cmd_7_hard + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/scalar-mut/request.json"],
        sonames_7,
    )
    assert r_d2_7_2["exit_code"] == 1 and r_d2_7_2["receipt"]["status"] == "proof_failed", r_d2_7_2
    checks.append(r_d2_7_2)

    r_d2_7_3 = run_check(
        "D2-7.3",
        "Hardened bundle in 7-SONAME rootfs: scalar-cargo verify --manifest-path (crate_verified, PATH='')",
        cmd_7_hard + [
            "/work/cargo-anneal", "verify",
            "--manifest-path", "/work/fixtures/scalar-cargo/rust/Cargo.toml",
            "--proof-dir", "/work/fixtures/scalar-cargo/lean",
        ],
        sonames_7,
    )
    assert r_d2_7_3["exit_code"] == 0 and r_d2_7_3["receipt"]["status"] == "crate_verified", r_d2_7_3
    checks.append(r_d2_7_3)

    r_d2_7_4 = run_check(
        "D2-7.4",
        "Hardened bundle in 7-SONAME rootfs: starnix-pos 10-file verify --request (selected_unit_verified)",
        cmd_7_hard + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/starnix-pos/request.json"],
        sonames_7,
    )
    assert r_d2_7_4["exit_code"] == 0 and r_d2_7_4["receipt"]["status"] == "selected_unit_verified", r_d2_7_4
    checks.append(r_d2_7_4)

    r_d2_7_5 = run_check(
        "D2-7.5",
        "Hardened bundle in 7-SONAME rootfs: starnix-zero 10-file verify --request (proof_failed)",
        cmd_7_hard + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/starnix-zero/request.json"],
        sonames_7,
    )
    assert r_d2_7_5["exit_code"] == 1 and r_d2_7_5["receipt"]["status"] == "proof_failed", r_d2_7_5
    checks.append(r_d2_7_5)

    # --- Q-D2 (6 Host SONAMEs: BOTH libz.so.1 AND libgcc_s.so.1 removed from host; glibc-only!) ---
    no_libz_no_gcc = ("/lib/x86_64-linux-gnu/libz.so.1", "/lib/x86_64-linux-gnu/libgcc_s.so.1")
    cmd_6_norpath, sonames_6 = bwrap_minimal(HOME_HARDENED, cli_patched, exclude_dests=no_libz_no_gcc)
    r_d2_6_0 = run_check(
        "D2-6.0",
        "Negative control in 6-SONAME rootfs: cargo-anneal without bundle DT_RUNPATH fails to load libgcc_s.so.1",
        cmd_6_norpath + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/scalar-pos/request.json"],
        sonames_6,
    )
    assert r_d2_6_0["exit_code"] == 127 and "libgcc_s.so.1" in r_d2_6_0["stderr"], r_d2_6_0
    checks.append(r_d2_6_0)

    cmd_6_hard, _ = bwrap_minimal(HOME_HARDENED, cli_rpath, exclude_dests=no_libz_no_gcc)
    r_d2_6_1 = run_check(
        "D2-6.1",
        "Hardened bundle + CLI in 6-SONAME (glibc-only) rootfs: scalar-pos verify --request (crate_verified)",
        cmd_6_hard + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/scalar-pos/request.json"],
        sonames_6,
    )
    assert r_d2_6_1["exit_code"] == 0 and r_d2_6_1["receipt"]["status"] == "crate_verified", r_d2_6_1
    checks.append(r_d2_6_1)

    r_d2_6_2 = run_check(
        "D2-6.2",
        "Hardened bundle + CLI in 6-SONAME (glibc-only) rootfs: scalar-mut verify --request (proof_failed)",
        cmd_6_hard + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/scalar-mut/request.json"],
        sonames_6,
    )
    assert r_d2_6_2["exit_code"] == 1 and r_d2_6_2["receipt"]["status"] == "proof_failed", r_d2_6_2
    checks.append(r_d2_6_2)

    r_d2_6_3 = run_check(
        "D2-6.3",
        "Hardened bundle + CLI in 6-SONAME (glibc-only) rootfs: scalar-cargo verify --manifest-path (crate_verified, PATH='')",
        cmd_6_hard + [
            "/work/cargo-anneal", "verify",
            "--manifest-path", "/work/fixtures/scalar-cargo/rust/Cargo.toml",
            "--proof-dir", "/work/fixtures/scalar-cargo/lean",
        ],
        sonames_6,
    )
    assert r_d2_6_3["exit_code"] == 0 and r_d2_6_3["receipt"]["status"] == "crate_verified", r_d2_6_3
    checks.append(r_d2_6_3)

    r_d2_6_4 = run_check(
        "D2-6.4",
        "Hardened bundle + CLI in 6-SONAME (glibc-only) rootfs: starnix-pos 10-file verify --request (selected_unit_verified)",
        cmd_6_hard + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/starnix-pos/request.json"],
        sonames_6,
    )
    assert r_d2_6_4["exit_code"] == 0 and r_d2_6_4["receipt"]["status"] == "selected_unit_verified", r_d2_6_4
    checks.append(r_d2_6_4)

    r_d2_6_5 = run_check(
        "D2-6.5",
        "Hardened bundle + CLI in 6-SONAME (glibc-only) rootfs: starnix-zero 10-file verify --request (proof_failed)",
        cmd_6_hard + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/starnix-zero/request.json"],
        sonames_6,
    )
    assert r_d2_6_5["exit_code"] == 1 and r_d2_6_5["receipt"]["status"] == "proof_failed", r_d2_6_5
    checks.append(r_d2_6_5)

    # Negative control: omit librt.so.1 (leaving 5 host SONAMEs) to prove 6 glibc SONAMEs is a tight lower bound
    no_libz_no_gcc_no_rt = (
        "/lib/x86_64-linux-gnu/libz.so.1",
        "/lib/x86_64-linux-gnu/libgcc_s.so.1",
        "/lib/x86_64-linux-gnu/librt.so.1",
    )
    cmd_5, sonames_5 = bwrap_minimal(HOME_HARDENED, cli_rpath, exclude_dests=no_libz_no_gcc_no_rt)
    r_d2_6_6 = run_check(
        "D2-6.6",
        "Tight lower-bound check in 5-SONAME rootfs (librt.so.1 omitted): fails loading librustc_driver -> librt.so.1",
        cmd_5 + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/scalar-pos/request.json"],
        sonames_5,
    )
    assert r_d2_6_6["exit_code"] == 2 and "librt.so.1" in r_d2_6_6["receipt"]["detail"], r_d2_6_6
    checks.append(r_d2_6_6)

    out_data = {
        "elf_headers": elf_headers,
        "qualification_checks": checks,
    }
    out_path = TRACK_D / "track_d_q1_q2_results.json"
    out_path.write_text(json.dumps(out_data, indent=2) + "\n")
    print(f"ALL Q-D1 AND Q-D2 CHECKS PASSED ({len(checks)} checks). Wrote {out_path}")


if __name__ == "__main__":
    main()
