#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Clean-environment and ultra-minimal rootfs qualification for the packaged Anneal toolchain."""

import json
import os
import shutil
import subprocess
import time
from pathlib import Path

SCRATCH = Path("<scratch>/mvp-investigations/task4")
SCALAR_SRC = Path("<workspace>/anneal/.agent-worktrees/joshlf-mvp/trusted/cargo-anneal/tests/fixtures/scalar")
STARNIX_BUNDLE = Path("/tmp/anneal-mvp-starnix-bundle-final")
WORK_DIR = SCRATCH / "work"


def prepare_work_dir():
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)
    WORK_DIR.mkdir(parents=True)

    # Copy cargo-anneal and omnibus archive
    shutil.copy2(SCRATCH / "cargo-anneal", WORK_DIR / "cargo-anneal")
    shutil.copy2(
        SCRATCH / "anneal-toolchain-omnibus-0.1.0.tar.zst",
        WORK_DIR / "anneal-toolchain-omnibus-0.1.0.tar.zst",
    )

    fixtures = WORK_DIR / "fixtures"
    fixtures.mkdir()

    # 1. scalar-pos and scalar-mut
    for variant, body_line in [("scalar-pos", "    0\n"), ("scalar-mut", "    1\n")]:
        vdir = fixtures / variant
        (vdir / "rust").mkdir(parents=True)
        (vdir / "lean").mkdir(parents=True)
        lib_rs = (SCALAR_SRC / "lib.rs").read_text().replace("    0\n", body_line)
        (vdir / "rust" / "lib.rs").write_text(lib_rs)
        shutil.copy2(SCALAR_SRC / "Spec.lean", vdir / "lean" / "Spec.lean")
        shutil.copy2(SCALAR_SRC / "Proof.lean", vdir / "lean" / "Proof.lean")
        req = {
            "schema_version": 1,
            "compilation": {
                "source_root": "rust",
                "crate_root": "lib.rs",
                "crate_name": "scalar",
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": [],
                "source_files": ["lib.rs"],
            },
            "scope": {"kind": "crate"},
            "proof": {
                "source_root": "lean",
                "sources": [
                    {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                    {"module": "Proof", "path": "Proof.lean", "role": "proof"},
                ],
            },
        }
        (vdir / "request.json").write_text(json.dumps(req, indent=2))

    # 2. scalar-cargo (for testing --manifest-path shortcut)
    scargo = fixtures / "scalar-cargo"
    shutil.copytree(fixtures / "scalar-pos", scargo)
    (scargo / "rust" / "Cargo.toml").write_text(
        '[package]\nname = "scalar"\nversion = "0.0.0"\nedition = "2024"\n[lib]\npath = "lib.rs"\n'
    )

    # 3. starnix-pos, starnix-zero, starnix-masked-identity
    shutil.copytree(STARNIX_BUNDLE / "production", fixtures / "starnix-pos")
    shutil.copytree(STARNIX_BUNDLE / "zero", fixtures / "starnix-zero")
    shutil.copytree(STARNIX_BUNDLE / "masked-identity", fixtures / "starnix-masked-identity")


def run_cmd(cmd, desc):
    print(f"Running: {desc}...", flush=True)
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
    return {
        "description": desc,
        "command": cmd,
        "exit_code": proc.returncode,
        "elapsed_ms": elapsed_ms,
        "stdout": proc.stdout if parsed_json is None else "<parsed_json>",
        "stderr": proc.stderr,
        "receipt": parsed_json,
    }


def run_suite_1_standard_clean():
    """Suite 1: Clean Linux environment without /nix/store, rustup, elan, cargo, or workspace."""
    home_host = SCRATCH / "clean_home_suite1"
    if home_host.exists():
        shutil.rmtree(home_host)
    home_host.mkdir(parents=True)

    def bwrap_base(extra_env=None):
        cmd = [
            "bwrap",
            "--die-with-parent",
            "--unshare-all",
            "--ro-bind", "/usr", "/usr",
            "--tmpfs", "/usr/local",
            "--ro-bind", "/bin", "/bin",
            "--ro-bind", "/lib", "/lib",
            "--ro-bind", "/lib64", "/lib64",
            "--proc", "/proc",
            "--dev", "/dev",
            "--tmpfs", "/tmp",
            "--bind", str(home_host), "/tmp/clean-home",
            "--ro-bind", str(WORK_DIR), "/work",
            "--chdir", "/work",
            "--clearenv",
            "--setenv", "HOME", "/tmp/clean-home",
            "--setenv", "PATH", "/usr/bin:/bin",
        ]
        if extra_env:
            for k, v in extra_env.items():
                cmd.extend(["--setenv", k, v])
        return cmd

    results = []

    # 1a. Verify environment isolation inside bwrap
    probe_script = (
        "set -e; "
        "echo \"HOME=$HOME PATH=$PATH\"; "
        "for p in /nix /nix/store /usr/local/google /tmp/clean-home/.rustup /tmp/clean-home/.elan /tmp/clean-home/.cargo; do "
        "  if [ -e \"$p\" ]; then echo \"LEAK:$p\"; exit 1; else echo \"ABSENT:$p\"; fi; "
        "done; "
        "for t in rustup rustc cargo elan lean lake patchelf nix; do "
        "  if command -v \"$t\" >/dev/null 2>&1; then echo \"FOUND_TOOL:$t\"; exit 1; else echo \"ABSENT_TOOL:$t\"; fi; "
        "done"
    )
    r_probe = run_cmd(
        bwrap_base() + ["/bin/sh", "-c", probe_script],
        "Suite 1.0: Probe clean environment absence of /nix, /usr/local/google, rustup, elan, cargo, lean",
    )
    assert r_probe["exit_code"] == 0, f"Probe failed: {r_probe}"
    results.append(r_probe)

    # 1b. Run cargo-anneal setup --local-archive
    r_setup = run_cmd(
        bwrap_base() + ["/work/cargo-anneal", "setup", "--local-archive", "/work/anneal-toolchain-omnibus-0.1.0.tar.zst"],
        "Suite 1.1: cargo-anneal setup --local-archive in clean environment",
    )
    assert r_setup["exit_code"] == 0, f"Setup failed: {r_setup}"
    installed_line = r_setup["stdout"].strip()
    assert installed_line.startswith("Installed Anneal toolchain at /tmp/clean-home/.cache/anneal/toolchain/"), installed_line
    installed_container_path = installed_line.split("Installed Anneal toolchain at ", 1)[1].strip()
    results.append(r_setup)

    # 1c. Verify scalar positive (crate_verified) with NO --capture/--sysroot/--lean flags
    r_scalar_pos = run_cmd(
        bwrap_base() + [
            "/work/cargo-anneal", "verify",
            "--request", "/work/fixtures/scalar-pos/request.json",
            "--artifacts", "/tmp/clean-home/artifacts-scalar-pos",
        ],
        "Suite 1.2: scalar positive verification (crate_verified, automatic bundle resolution)",
    )
    assert r_scalar_pos["exit_code"] == 0 and r_scalar_pos["receipt"]["status"] == "crate_verified", r_scalar_pos
    results.append(r_scalar_pos)

    # 1d. Verify scalar failing mutation (proof_failed)
    r_scalar_mut = run_cmd(
        bwrap_base() + [
            "/work/cargo-anneal", "verify",
            "--request", "/work/fixtures/scalar-mut/request.json",
            "--artifacts", "/tmp/clean-home/artifacts-scalar-mut",
        ],
        "Suite 1.3: scalar mutated source verification (proof_failed)",
    )
    assert r_scalar_mut["exit_code"] == 1 and r_scalar_mut["receipt"]["status"] == "proof_failed", r_scalar_mut
    results.append(r_scalar_mut)

    # 1e. Verify Starnix 10-file positive (selected_unit_verified)
    r_starnix_pos = run_cmd(
        bwrap_base() + [
            "/work/cargo-anneal", "verify",
            "--request", "/work/fixtures/starnix-pos/request.json",
            "--artifacts", "/tmp/clean-home/artifacts-starnix-pos",
        ],
        "Suite 1.4: starnix 10-file positive verification (selected_unit_verified, automatic bundle resolution)",
    )
    assert r_starnix_pos["exit_code"] == 0 and r_starnix_pos["receipt"]["status"] == "selected_unit_verified", r_starnix_pos
    results.append(r_starnix_pos)

    # 1f. Verify Starnix 10-file failing mutation (zero)
    r_starnix_zero = run_cmd(
        bwrap_base() + [
            "/work/cargo-anneal", "verify",
            "--request", "/work/fixtures/starnix-zero/request.json",
            "--artifacts", "/tmp/clean-home/artifacts-starnix-zero",
        ],
        "Suite 1.5: starnix 10-file mutated (return 0) verification (proof_failed)",
    )
    assert r_starnix_zero["exit_code"] == 1 and r_starnix_zero["receipt"]["status"] == "proof_failed", r_starnix_zero
    results.append(r_starnix_zero)

    # 1g. Verify Starnix 10-file failing mutation (masked-identity)
    r_starnix_masked = run_cmd(
        bwrap_base() + [
            "/work/cargo-anneal", "verify",
            "--request", "/work/fixtures/starnix-masked-identity/request.json",
            "--artifacts", "/tmp/clean-home/artifacts-starnix-masked",
        ],
        "Suite 1.6: starnix 10-file mutated (masked-identity) verification (proof_failed)",
    )
    assert r_starnix_masked["exit_code"] == 1 and r_starnix_masked["receipt"]["status"] == "proof_failed", r_starnix_masked
    results.append(r_starnix_masked)

    # 1h. Test --manifest-path Cargo shortcut without cargo on PATH vs with bundled rust/bin on PATH
    r_cargo_no_path = run_cmd(
        bwrap_base() + [
            "/work/cargo-anneal", "verify",
            "--manifest-path", "/work/fixtures/scalar-cargo/rust/Cargo.toml",
            "--proof-dir", "/work/fixtures/scalar-cargo/lean",
        ],
        "Suite 1.7a: --manifest-path shortcut with PATH=/usr/bin:/bin (shows verify.rs:262 bare `cargo` lookup)",
    )
    assert r_cargo_no_path["exit_code"] == 2 and r_cargo_no_path["receipt"]["phase"] == "cargo", r_cargo_no_path
    results.append(r_cargo_no_path)

    r_cargo_with_bundled_path = run_cmd(
        bwrap_base({"PATH": f"{installed_container_path}/rust/bin:/usr/bin:/bin"}) + [
            "/work/cargo-anneal", "verify",
            "--manifest-path", "/work/fixtures/scalar-cargo/rust/Cargo.toml",
            "--proof-dir", "/work/fixtures/scalar-cargo/lean",
        ],
        "Suite 1.7b: --manifest-path shortcut with <installed>/rust/bin on PATH (crate_verified)",
    )
    assert r_cargo_with_bundled_path["exit_code"] == 0 and r_cargo_with_bundled_path["receipt"]["status"] == "crate_verified", r_cargo_with_bundled_path
    results.append(r_cargo_with_bundled_path)

    return results


def run_suite_2_ultra_minimal_rootfs():
    """Suite 2: Ultra-minimal rootfs mounting ONLY the 8 declared host shared libraries and ZERO host binaries."""
    home_host = SCRATCH / "clean_home_suite2"
    if home_host.exists():
        shutil.rmtree(home_host)
    home_host.mkdir(parents=True)

    # Exact 8 host shared libraries identified in static ELF audit
    host_libs = [
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

    def bwrap_minimal(exclude_dest=None):
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
            "--bind", str(home_host), "/tmp/clean-home",
            "--ro-bind", str(WORK_DIR), "/work",
            "--chdir", "/work",
            "--clearenv",
            "--setenv", "HOME", "/tmp/clean-home",
            "--setenv", "PATH", "/usr/bin:/bin",
        ]
        for src, dst in host_libs:
            if dst == exclude_dest:
                continue
            cmd.extend(["--ro-bind", src, dst])
        return cmd

    results = []

    # 2a. Setup in ultra-minimal 8-library rootfs (with zero /bin or /usr/bin binaries!)
    r_setup = run_cmd(
        bwrap_minimal() + ["/work/cargo-anneal", "setup", "--local-archive", "/work/anneal-toolchain-omnibus-0.1.0.tar.zst"],
        "Suite 2.1: cargo-anneal setup in ultra-minimal rootfs (8 host .so files only, 0 host binaries)",
    )
    assert r_setup["exit_code"] == 0, f"Minimal setup failed: {r_setup}"
    results.append(r_setup)

    # 2b. Scalar positive in ultra-minimal rootfs
    r_scalar_pos = run_cmd(
        bwrap_minimal() + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/scalar-pos/request.json"],
        "Suite 2.2: scalar positive in ultra-minimal 8-library rootfs (crate_verified)",
    )
    assert r_scalar_pos["exit_code"] == 0 and r_scalar_pos["receipt"]["status"] == "crate_verified", r_scalar_pos
    results.append(r_scalar_pos)

    # 2c. Scalar mutation in ultra-minimal rootfs
    r_scalar_mut = run_cmd(
        bwrap_minimal() + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/scalar-mut/request.json"],
        "Suite 2.3: scalar mutated in ultra-minimal 8-library rootfs (proof_failed)",
    )
    assert r_scalar_mut["exit_code"] == 1 and r_scalar_mut["receipt"]["status"] == "proof_failed", r_scalar_mut
    results.append(r_scalar_mut)

    # 2d. Starnix 10-file positive in ultra-minimal rootfs
    r_starnix_pos = run_cmd(
        bwrap_minimal() + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/starnix-pos/request.json"],
        "Suite 2.4: starnix 10-file positive in ultra-minimal 8-library rootfs (selected_unit_verified)",
    )
    assert r_starnix_pos["exit_code"] == 0 and r_starnix_pos["receipt"]["status"] == "selected_unit_verified", r_starnix_pos
    results.append(r_starnix_pos)

    # 2e. Starnix 10-file failing mutation in ultra-minimal rootfs
    r_starnix_zero = run_cmd(
        bwrap_minimal() + ["/work/cargo-anneal", "verify", "--request", "/work/fixtures/starnix-zero/request.json"],
        "Suite 2.5: starnix 10-file mutated (return 0) in ultra-minimal 8-library rootfs (proof_failed)",
    )
    assert r_starnix_zero["exit_code"] == 1 and r_starnix_zero["receipt"]["status"] == "proof_failed", r_starnix_zero
    results.append(r_starnix_zero)

    # 2f. Negative control: omit libz.so.1 from ultra-minimal rootfs to prove tight lower bound
    r_no_libz = run_cmd(
        bwrap_minimal(exclude_dest="/lib/x86_64-linux-gnu/libz.so.1") + [
            "/work/cargo-anneal", "verify", "--request", "/work/fixtures/scalar-pos/request.json"
        ],
        "Suite 2.6: negative control omitting libz.so.1 (proves libz.so.1 is strictly required by bin/anneal-rustc-capture)",
    )
    assert r_no_libz["exit_code"] == 2 and r_no_libz["receipt"]["phase"] == "capture" and "libz.so.1" in r_no_libz["receipt"]["detail"], r_no_libz
    results.append(r_no_libz)

    return results


def main():
    prepare_work_dir()
    suite1 = run_suite_1_standard_clean()
    suite2 = run_suite_2_ultra_minimal_rootfs()

    out = {
        "suite_1_standard_clean_env": suite1,
        "suite_2_ultra_minimal_8_lib_rootfs": suite2,
    }
    out_path = SCRATCH / "clean_env_qualification_results.json"
    out_path.write_text(json.dumps(out, indent=2))
    print(f"ALL QUALIFICATION SUITES PASSED. Wrote {out_path}")


if __name__ == "__main__":
    main()
