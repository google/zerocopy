#!/usr/bin/env python3
"""Standalone empirical probe for language toolchain multiplexers and loader isolation.

Part A: Go 1.21+ toolchain selection and language gating (`golang/go`)
  - `go 1.21` vs `go 1.24` `-lang=` forwarding in `go build -n` under
    `GOTOOLCHAIN=local` and `GOTOOLCHAIN=path`.
  - Language feature gating (`for range 3` from Go 1.22) under `go 1.21` vs `go 1.24`
    compiled by the same `go1.27.3` binary (`GOTOOLCHAIN=local`), plus `go vet`
    `stdversion` standard-library symbol gating (`slices.Backward` from Go 1.23).
  - Fail-closed diagnostics when `go.mod` requests `toolchain go1.99.0` or `go 1.99.0`
    under `GOTOOLCHAIN=local`, `GOTOOLCHAIN=path`, and `GOTOOLCHAIN=auto`.
  - Internal switch-loop and target-mismatch sentinels
    (`GOTOOLCHAIN_INTERNAL_SWITCH_COUNT=100` and
    `GOTOOLCHAIN_INTERNAL_SWITCH_VERSION=go1.99.0`) plus `GOSUMDB=off` rejection.

Part B: `rustup` / `elan` environment mutation and GNU `glibc` `ld.so`
  `LD_LIBRARY_PATH` > `DT_RUNPATH` cross-toolchain poisoning:
  1. Exact environment mutations performed by `rustup run 1.93.1 env`.
  2. Direct `<sysroot-1.100.0>/bin/rustc -vV` with `LD_LIBRARY_PATH=<sysroot-1.93.1>/lib`
     under `LD_DEBUG=libs`: demonstrates `ld.so` searching `LD_LIBRARY_PATH` before ELF
     `DT_RUNPATH` (`$ORIGIN/../lib`), and why hashed `librustc_driver-<hash>.so`
     and release-suffixed `libLLVM.so.23.1-rust-1.100.0-stable` miss `1.93.1/lib` and
     fall through to `1.100.0/lib`.
  3. Direct `<sysroot-nightly-2026-11-20>/bin/rustc -vV` with
     `LD_LIBRARY_PATH=<sysroot-nightly-2026-11-12>/lib` under `LD_DEBUG=libs`: proves
     live cross-toolchain `libLLVM.so.23.1-rust-1.102.0-nightly` splicing across two
     nightlies in the same release cycle because nightly `libLLVM` omits a commit hash
     from `DT_SONAME`.
  4. Direct `<elan-v4.35.0>/bin/lean --version` with
     `LD_LIBRARY_PATH=<elan-v4.34.1>/lib/lean`: proves silent kernel downgrade via
     unversioned `libleanshared.so`.
  5. `cargo` invocation in a crate with `rust-toolchain.toml` (`channel = "1.100.0"`)
     under inherited `RUSTUP_TOOLCHAIN=1.93.1` + `LD_LIBRARY_PATH=<sysroot-1.93.1>/lib`,
     testing both proxy `cargo` and direct `<sysroot-1.100.0>/bin/cargo`, alongside the
     scrubbed hermetic control with explicit `RUSTC=<sysroot-1.100.0>/bin/rustc`.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def run_cmd(
    argv: list[str],
    *,
    cwd: str | Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 30,
) -> dict[str, Any]:
    proc = subprocess.run(
        argv,
        cwd=str(cwd) if cwd is not None else None,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    return {
        "argv": argv,
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def extract_lang_flag(text: str) -> list[str]:
    return sorted(set(re.findall(r"-lang=\S+", text)))


def extract_goversion_flag(text: str) -> list[str]:
    return sorted(set(re.findall(r"-goversion\s+\S+", text)))


def probe_part_a_go() -> dict[str, Any]:
    base_env = os.environ.copy()
    results: dict[str, Any] = {}
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        gocache = tmp_path / "gocache"
        gomodcache = tmp_path / "gomodcache"
        goenv_file = tmp_path / "go.env"
        gocache.mkdir()
        gomodcache.mkdir()
        goenv_file.write_text("", encoding="utf-8")

        def make_env(extra: dict[str, str]) -> dict[str, str]:
            env = base_env.copy()
            env.pop("GOTOOLCHAIN", None)
            env.pop("GOTOOLCHAIN_INTERNAL_SWITCH_VERSION", None)
            env.pop("GOTOOLCHAIN_INTERNAL_SWITCH_COUNT", None)
            env["GOCACHE"] = str(gocache)
            env["GOMODCACHE"] = str(gomodcache)
            env["GOENV"] = str(goenv_file)
            env["GOPROXY"] = "off"
            env.update(extra)
            return env

        ver = run_cmd(["go", "version"], cwd=tmp_path, env=make_env({}))
        results["go_version"] = ver["stdout"].strip()

        matrix_cases = []
        for go_dir_ver in ("1.21", "1.24"):
            for gt_mode in ("local", "path"):
                mod_dir = tmp_path / f"mod_{go_dir_ver.replace('.', '_')}_{gt_mode}"
                mod_dir.mkdir()
                (mod_dir / "go.mod").write_text(
                    f"module example.com/probe\n\ngo {go_dir_ver}\n",
                    encoding="utf-8",
                )
                (mod_dir / "main.go").write_text(
                    "package main\n\nfunc main() {}\n",
                    encoding="utf-8",
                )
                res = run_cmd(
                    ["go", "build", "-n", "."],
                    cwd=mod_dir,
                    env=make_env({"GOTOOLCHAIN": gt_mode}),
                )
                combined = res["stdout"] + "\n" + res["stderr"]
                compile_lines = [
                    line.strip()
                    for line in combined.splitlines()
                    if "/compile " in line and "-lang=" in line
                ]
                matrix_cases.append(
                    {
                        "go_directive": go_dir_ver,
                        "GOTOOLCHAIN": gt_mode,
                        "returncode": res["returncode"],
                        "lang_flags": extract_lang_flag(combined),
                        "goversion_flags": extract_goversion_flag(combined),
                        "sample_compile_line": compile_lines[-1] if compile_lines else "",
                    }
                )
        results["build_n_lang_matrix"] = matrix_cases

        lang_gate_cases = []
        for go_dir_ver in ("1.21", "1.24"):
            mod_dir = tmp_path / f"gate_{go_dir_ver.replace('.', '_')}"
            mod_dir.mkdir()
            (mod_dir / "go.mod").write_text(
                f"module example.com/gate\n\ngo {go_dir_ver}\n",
                encoding="utf-8",
            )
            (mod_dir / "main.go").write_text(
                'package main\n\nimport "slices"\n\nfunc main() {\n'
                "\t_ = slices.Backward([]int{1, 2})\n"
                "\tfor range 3 {\n\t}\n"
                "}\n",
                encoding="utf-8",
            )
            build_res = run_cmd(
                ["go", "build", "-o", str(mod_dir / "app"), "."],
                cwd=mod_dir,
                env=make_env({"GOTOOLCHAIN": "local"}),
            )
            std_dir = tmp_path / f"std_{go_dir_ver.replace('.', '_')}"
            std_dir.mkdir()
            (std_dir / "go.mod").write_text(
                f"module example.com/stdgate\n\ngo {go_dir_ver}\n",
                encoding="utf-8",
            )
            (std_dir / "main.go").write_text(
                'package main\n\nimport "slices"\n\nfunc main() {\n'
                "\t_ = slices.Backward([]int{1, 2})\n"
                "}\n",
                encoding="utf-8",
            )
            std_build = run_cmd(
                ["go", "build", "-o", str(std_dir / "app"), "."],
                cwd=std_dir,
                env=make_env({"GOTOOLCHAIN": "local"}),
            )
            std_vet = run_cmd(
                ["go", "vet", "."],
                cwd=std_dir,
                env=make_env({"GOTOOLCHAIN": "local"}),
            )
            lang_gate_cases.append(
                {
                    "go_directive": go_dir_ver,
                    "go122_syntax_build_rc": build_res["returncode"],
                    "go122_syntax_build_stderr": build_res["stderr"].strip(),
                    "go123_stdlib_only_build_rc": std_build["returncode"],
                    "go123_stdlib_only_vet_rc": std_vet["returncode"],
                    "go123_stdlib_only_vet_stderr": std_vet["stderr"].strip(),
                }
            )
        results["language_vs_stdlib_gating"] = lang_gate_cases

        high_tc_cases = []
        for label, gomod_body in [
            ("toolchain_go1.99.0_only", "module example.com/hi\n\ngo 1.24\n\ntoolchain go1.99.0\n"),
            ("go_1.99.0_directive", "module example.com/hi2\n\ngo 1.99.0\n\ntoolchain go1.99.0\n"),
        ]:
            case_dir = tmp_path / label
            case_dir.mkdir()
            (case_dir / "go.mod").write_text(gomod_body, encoding="utf-8")
            (case_dir / "main.go").write_text("package main\nfunc main() {}\n", encoding="utf-8")
            for gt_mode in ("local", "path", "auto"):
                res = run_cmd(
                    ["go", "build", "-n", "."],
                    cwd=case_dir,
                    env=make_env({"GOTOOLCHAIN": gt_mode, "GODEBUG": "toolchaintrace=1"}),
                )
                high_tc_cases.append(
                    {
                        "scenario": label,
                        "GOTOOLCHAIN": gt_mode,
                        "returncode": res["returncode"],
                        "stderr": res["stderr"].strip(),
                    }
                )
        results["higher_toolchain_diagnostics"] = high_tc_cases

        loop_dir = tmp_path / "loop_probe"
        loop_dir.mkdir()
        (loop_dir / "go.mod").write_text(
            "module example.com/loop\n\ngo 1.24\n\ntoolchain go1.99.0\n",
            encoding="utf-8",
        )
        (loop_dir / "main.go").write_text("package main\nfunc main() {}\n", encoding="utf-8")

        max_switch_res = run_cmd(
            ["go", "version"],
            cwd=loop_dir,
            env=make_env(
                {
                    "GOTOOLCHAIN": "path",
                    "GOTOOLCHAIN_INTERNAL_SWITCH_COUNT": "100",
                }
            ),
        )
        mismatch_res = run_cmd(
            ["go", "version"],
            cwd=loop_dir,
            env=make_env(
                {
                    "GOTOOLCHAIN": "path",
                    "GOTOOLCHAIN_INTERNAL_SWITCH_VERSION": "go1.99.0",
                }
            ),
        )
        gosumdb_off_res = run_cmd(
            ["go", "version"],
            cwd=loop_dir,
            env=make_env(
                {
                    "GOTOOLCHAIN": "go1.99.0",
                    "GOSUMDB": "off",
                    "GOPROXY": "https://proxy.golang.org",
                }
            ),
        )
        results["internal_sentinels"] = {
            "switch_count_100": {
                "returncode": max_switch_res["returncode"],
                "stderr": max_switch_res["stderr"].strip(),
            },
            "switch_version_mismatch": {
                "returncode": mismatch_res["returncode"],
                "stderr": mismatch_res["stderr"].strip(),
            },
            "gosumdb_off_rejection": {
                "returncode": gosumdb_off_res["returncode"],
                "stderr": gosumdb_off_res["stderr"].strip(),
            },
        }

    return results


def parse_env_output(stdout: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in stdout.splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            out[k] = v
    return out


def parse_ld_debug_events(stderr: str, needle_libs: list[str]) -> list[str]:
    matched: list[str] = []
    for line in stderr.splitlines():
        if any(lib in line for lib in needle_libs) or "search path=" in line:
            cleaned = re.sub(r"^\s*\d+:\s*", "", line).strip()
            if (
                any(lib in cleaned for lib in needle_libs)
                or "(LD_LIBRARY_PATH)" in cleaned
                or "(RUNPATH" in cleaned
            ):
                if cleaned not in matched:
                    matched.append(cleaned)
    return matched[:25]


def probe_part_b_rustup_and_ldso() -> dict[str, Any]:
    results: dict[str, Any] = {}
    clean_base = os.environ.copy()
    for k in (
        "LD_LIBRARY_PATH",
        "RUSTUP_TOOLCHAIN",
        "RUSTUP_TOOLCHAIN_SOURCE",
        "RUST_RECURSION_COUNT",
        "RUSTC",
        "ELAN_TOOLCHAIN",
    ):
        clean_base.pop(k, None)

    env_93 = run_cmd(["rustup", "run", "1.93.1", "env"], env=clean_base)
    parsed_93 = parse_env_output(env_93["stdout"])
    sysroot_93 = run_cmd(
        ["rustup", "run", "1.93.1", "rustc", "--print", "sysroot"], env=clean_base
    )["stdout"].strip()
    sysroot_100 = run_cmd(
        ["rustup", "run", "1.100.0", "rustc", "--print", "sysroot"], env=clean_base
    )["stdout"].strip()

    first_path = parsed_93.get("PATH", "").split(":")[0]
    cargo_bin_dir = str(Path(parsed_93.get("CARGO_HOME", str(Path.home() / ".cargo"))) / "bin")
    path_head_label = "<CARGO_HOME>/bin" if first_path == cargo_bin_dir else "<CALLER_PATH_HEAD>"

    results["rustup_run_1_93_1_env"] = {
        "RUSTUP_TOOLCHAIN": parsed_93.get("RUSTUP_TOOLCHAIN"),
        "RUSTUP_HOME": parsed_93.get("RUSTUP_HOME"),
        "CARGO_HOME": parsed_93.get("CARGO_HOME"),
        "RUST_RECURSION_COUNT": parsed_93.get("RUST_RECURSION_COUNT"),
        "LD_LIBRARY_PATH": parsed_93.get("LD_LIBRARY_PATH"),
        "PATH_first_entry": path_head_label,
        "sysroot_1_93_1": sysroot_93,
        "sysroot_1_100_0": sysroot_100,
    }

    rustc_100_bin = str(Path(sysroot_100) / "bin" / "rustc")
    lib_93 = str(Path(sysroot_93) / "lib")
    env_poison_stable = clean_base.copy()
    env_poison_stable["LD_LIBRARY_PATH"] = lib_93
    env_poison_stable["LD_DEBUG"] = "libs"
    res_stable_ld = run_cmd([rustc_100_bin, "-vV"], env=env_poison_stable)
    results["direct_rustc_1_100_0_with_ld_library_path_1_93_1"] = {
        "returncode": res_stable_ld["returncode"],
        "stdout": res_stable_ld["stdout"].strip(),
        "ld_debug_trace": parse_ld_debug_events(
            res_stable_ld["stderr"],
            ["librustc_driver-", "libLLVM.so."],
        ),
    }

    sys_n1 = run_cmd(
        ["rustup", "run", "nightly-2026-11-12", "rustc", "--print", "sysroot"],
        env=clean_base,
    )["stdout"].strip()
    sys_n2 = run_cmd(
        ["rustup", "run", "nightly-2026-11-20", "rustc", "--print", "sysroot"],
        env=clean_base,
    )["stdout"].strip()
    rustc_n2 = str(Path(sys_n2) / "bin" / "rustc")
    lib_n1 = str(Path(sys_n1) / "lib")
    env_poison_nightly = clean_base.copy()
    env_poison_nightly["LD_LIBRARY_PATH"] = lib_n1
    env_poison_nightly["LD_DEBUG"] = "libs"
    res_nightly_ld = run_cmd([rustc_n2, "-vV"], env=env_poison_nightly)

    init_libs_nightly = [
        re.sub(r"^\s*\d+:\s*", "", ln).strip()
        for ln in res_nightly_ld["stderr"].splitlines()
        if "calling init:" in ln and ("librustc_driver" in ln or "libLLVM" in ln)
    ]
    results["cross_nightly_same_soname_llvm_hijack"] = {
        "host_toolchain_A": "nightly-2026-11-12",
        "child_toolchain_B": "nightly-2026-11-20",
        "returncode": res_nightly_ld["returncode"],
        "stdout": res_nightly_ld["stdout"].strip(),
        "calling_init_objects": init_libs_nightly,
        "hijacked_llvm_from_toolchain_A": any(
            "nightly-2026-11-12" in x and "libLLVM" in x for x in init_libs_nightly
        ),
        "driver_from_toolchain_B": any(
            "nightly-2026-11-20" in x and "librustc_driver" in x
            for x in init_libs_nightly
        ),
        "ld_debug_trace": parse_ld_debug_events(
            res_nightly_ld["stderr"],
            ["librustc_driver-", "libLLVM.so."],
        ),
    }

    elan_home = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan"))) / "toolchains"
    lean_34_lib = elan_home / "leanprover--lean4---v4.34.1" / "lib" / "lean"
    lean_35_bin = elan_home / "leanprover--lean4---v4.35.0" / "bin" / "lean"
    if lean_34_lib.is_dir() and lean_35_bin.is_file():
        clean_lean = run_cmd([str(lean_35_bin), "--version"], env=clean_base)
        env_poison_lean = clean_base.copy()
        env_poison_lean["LD_LIBRARY_PATH"] = str(lean_34_lib)
        env_poison_lean["LD_DEBUG"] = "libs"
        poisoned_lean = run_cmd([str(lean_35_bin), "--version"], env=env_poison_lean)
        lean_inits = [
            re.sub(r"^\s*\d+:\s*", "", ln).strip()
            for ln in poisoned_lean["stderr"].splitlines()
            if (
                "calling init:" in ln
                or "symbol=" in ln
                or "error:" in ln
                or "lookup error" in ln
            )
            and ("libleanshared" in ln or "libInit_shared" in ln or "lean" in ln)
        ]
        results["cross_lean_unhashed_soname_hijack"] = {
            "clean_v4_35_0_stdout": clean_lean["stdout"].strip(),
            "poisoned_with_v4_34_1_ld_library_path_rc": poisoned_lean["returncode"],
            "poisoned_stdout": poisoned_lean["stdout"].strip(),
            "poisoned_diagnostics_and_inits": lean_inits[:15],
        }

    with tempfile.TemporaryDirectory() as tmp:
        crate_dir = Path(tmp) / "victim_crate"
        (crate_dir / "src").mkdir(parents=True)
        (crate_dir / "rust-toolchain.toml").write_text(
            '[toolchain]\nchannel = "1.100.0"\n',
            encoding="utf-8",
        )
        (crate_dir / "Cargo.toml").write_text(
            '[package]\nname = "victim_crate"\nversion = "0.1.0"\nedition = "2021"\n',
            encoding="utf-8",
        )
        (crate_dir / "build.rs").write_text(
            "fn main() {\n"
            '    println!("cargo:warning=BUILD_RS_RUSTC={}", std::env::var("RUSTC").unwrap_or_default());\n'
            '    println!("cargo:warning=BUILD_RS_LD_LP={}", std::env::var("LD_LIBRARY_PATH").unwrap_or_default());\n'
            '    println!("cargo:warning=BUILD_RS_RUSTUP_TC={}", std::env::var("RUSTUP_TOOLCHAIN").unwrap_or_default());\n'
            "}\n",
            encoding="utf-8",
        )
        (crate_dir / "src" / "lib.rs").write_text(
            "pub fn answer() -> u32 { 42 }\n", encoding="utf-8"
        )

        cargo_home = Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo")))
        proxy_cargo = str(cargo_home / "bin" / "cargo")
        direct_cargo_100 = str(Path(sysroot_100) / "bin" / "cargo")

        t_clean = Path(tmp) / "target_clean"
        r_clean = run_cmd(
            [proxy_cargo, "check", "-vv", "--offline", "--target-dir", str(t_clean)],
            cwd=crate_dir,
            env=clean_base,
        )

        poison_cargo_env = clean_base.copy()
        poison_cargo_env["RUSTUP_TOOLCHAIN"] = "1.93.1-x86_64-unknown-linux-gnu"
        poison_cargo_env["LD_LIBRARY_PATH"] = lib_93
        t_proxy_hijack = Path(tmp) / "target_proxy_hijack"
        r_proxy_hijack = run_cmd(
            [proxy_cargo, "check", "-vv", "--offline", "--target-dir", str(t_proxy_hijack)],
            cwd=crate_dir,
            env=poison_cargo_env,
        )

        t_direct_hijack = Path(tmp) / "target_direct_hijack"
        r_direct_hijack = run_cmd(
            [direct_cargo_100, "check", "-vv", "--offline", "--target-dir", str(t_direct_hijack)],
            cwd=crate_dir,
            env=poison_cargo_env,
        )

        hermetic_env = clean_base.copy()
        hermetic_env["RUSTC"] = rustc_100_bin
        t_hermetic = Path(tmp) / "target_hermetic"
        r_hermetic = run_cmd(
            [direct_cargo_100, "check", "-vv", "--offline", "--target-dir", str(t_hermetic)],
            cwd=crate_dir,
            env=hermetic_env,
        )

        def summarize_cargo_vv(res: dict[str, Any], cargo_bin: str) -> dict[str, Any]:
            cargo_ver = run_cmd([cargo_bin, "-V"], env=clean_base)["stdout"].strip()
            combined = res["stdout"] + "\n" + res["stderr"]
            rustc_v = re.findall(r"rustc 1\.\d+\.\d+[^\n]*", combined)
            warnings = [
                ln.strip() for ln in combined.splitlines() if "BUILD_RS_" in ln
            ]
            return {
                "returncode": res["returncode"],
                "invoked_cargo_binary": cargo_bin,
                "cargo_binary_intrinsic_version": cargo_ver,
                "observed_rustc_versions_in_vv": sorted(set(rustc_v)),
                "build_rs_env_warnings": warnings,
            }

        results["cargo_inheritance_matrix"] = {
            "clean_proxy_cargo": summarize_cargo_vv(r_clean, proxy_cargo),
            "poisoned_proxy_cargo_under_rustup_1_93_1_env": summarize_cargo_vv(
                r_proxy_hijack, proxy_cargo
            ),
            "poisoned_direct_cargo_1_100_0_under_rustup_1_93_1_env": summarize_cargo_vv(
                r_direct_hijack, direct_cargo_100
            ),
            "scrubbed_hermetic_direct_cargo_1_100_0_with_explicit_RUSTC": summarize_cargo_vv(
                r_hermetic, direct_cargo_100
            ),
        }

    return results


def sanitize_paths(obj: Any) -> Any:
    home = str(Path.home())
    rustup_home = os.environ.get("RUSTUP_HOME", str(Path.home() / ".rustup"))
    cargo_home = os.environ.get("CARGO_HOME", str(Path.home() / ".cargo"))
    elan_home = os.environ.get("ELAN_HOME", str(Path.home() / ".elan"))
    if isinstance(obj, str):
        s = obj
        for raw, token in (
            (rustup_home, "<RUSTUP_HOME>"),
            (cargo_home, "<CARGO_HOME>"),
            (elan_home, "<ELAN_HOME>"),
            (home, "<HOME>"),
        ):
            if raw and raw != "/":
                s = s.replace(raw, token)
        s = re.sub(r"/tmp/tmp[A-Za-z0-9_]+", "<TMPDIR>", s)
        return s
    if isinstance(obj, list):
        return [sanitize_paths(x) for x in obj]
    if isinstance(obj, dict):
        return {k: sanitize_paths(v) for k, v in obj.items()}
    return obj


def main() -> int:
    report = sanitize_paths(
        {
            "host": {
                "platform": sys.platform,
                "python": sys.version.split()[0],
            },
            "part_a_go_toolchain": probe_part_a_go(),
            "part_b_rustup_elan_ldso": probe_part_b_rustup_and_ldso(),
        }
    )
    out_path = Path(__file__).resolve().parent / "probe_toolchain_isolation_results.json"
    out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
