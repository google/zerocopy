#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Closed-namespace FileLoader macro-expansion refusal matrix probe.

Builds `fileloader_macro_probe.rs` against an installed nightly `rustc-dev`
toolchain, constructs a stripped `--sysroot` lacking `lib/rustlib/src`, and
verifies which stdlib panic/unreachable/todo/unimplemented/assert macro forms
trigger `FileLoader::read_file` on `library/core/src/{panic,macros/mod}.rs`
during `make_format_args` (`SourceMap::span_to_snippet`), even inside
`#[allow(unused)]` unselected functions and even when `rustc` exits `0`.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
DRIVER_RS = HERE / "fileloader_macro_probe.rs"


def find_rustc_dev_sysroot() -> tuple[str, Path]:
    preferred = ["+nightly-2026-05-31", "+nightly-2026-06-01", "+nightly"]
    seen = set()
    candidates = []
    for p in preferred:
        candidates.append([p])
    proc = subprocess.run(["rustup", "toolchain", "list"], capture_output=True, text=True)
    if proc.returncode == 0:
        for line in proc.stdout.splitlines():
            tc = line.split()[0]
            if "nightly" in tc:
                candidates.append([f"+{tc}"])
    for sel in candidates:
        key = sel[0]
        if key in seen:
            continue
        seen.add(key)
        sys_p = subprocess.run(["rustc", *sel, "--print", "sysroot"], capture_output=True, text=True)
        if sys_p.returncode != 0:
            continue
        sysroot = Path(sys_p.stdout.strip())
        # Check for rustc-dev interface crate (.rmeta) so we match installed rustc-dev.
        lib_dir = sysroot / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "lib"
        if list(lib_dir.glob("librustc_interface-*.rmeta")):
            ver = subprocess.check_output(["rustc", *sel, "-vV"], text=True)
            return ver.strip(), sysroot
    raise RuntimeError("No nightly toolchain with `rustc-dev` component found")


def main() -> int:
    ver_info, sysroot = find_rustc_dev_sysroot()
    cases = [
        ("unreachable_msg_2021", "2021", 'if x > 3 { unreachable!("msg") }', "library/core/src/panic.rs"),
        ("unreachable_bare_2021", "2021", "if x > 3 { unreachable!() }", None),
        ("unreachable_fmtarg_2015", "2015", 'if x > 3 { unreachable!("bad {}", x) }', "library/core/src/panic.rs"),
        ("unreachable_fmtarg_2018", "2018", 'if x > 3 { unreachable!("bad {}", x) }', "library/core/src/panic.rs"),
        ("unreachable_fmtarg_2021", "2021", 'if x > 3 { unreachable!("bad {}", x) }', "library/core/src/panic.rs"),
        ("unreachable_msg_2015", "2015", 'if x > 3 { unreachable!("msg") }', None),
        ("unreachable_msg_2024", "2024", 'if x > 3 { unreachable!("msg") }', "library/core/src/panic.rs"),
        ("panic_msg_2021", "2021", 'if x > 3 { panic!("msg") }', None),
        ("panic_fmtarg_2021", "2021", 'if x > 3 { panic!("bad {}", x) }', None),
        ("todo_msg_2021", "2021", 'if x > 3 { todo!("msg") }', "library/core/src/macros/mod.rs"),
        ("todo_bare_2021", "2021", "if x > 3 { todo!() }", None),
        ("unimplemented_msg_2021", "2021", 'if x > 3 { unimplemented!("msg") }', "library/core/src/macros/mod.rs"),
        ("unimplemented_bare_2021", "2021", "if x > 3 { unimplemented!() }", None),
        ("assert_msg_2021", "2021", 'assert!(x < 4, "msg");', None),
        ("assert_eq_msg_2021", "2021", 'assert_eq!(x, 1, "msg");', None),
        ("debug_assert_2021", "2021", "debug_assert!(x < 4); debug_assert_eq!(x, x);", None),
    ]

    with tempfile.TemporaryDirectory(prefix="fileloader_macro_probe_") as td:
        tmp = Path(td)
        probe_bin = tmp / "fileloader_macro_probe"
        rustc_bin = sysroot / "bin" / "rustc"
        env = os.environ.copy()
        env["LD_LIBRARY_PATH"] = f"{sysroot / 'lib'}:{env.get('LD_LIBRARY_PATH', '')}".rstrip(":")
        comp = subprocess.run(
            [str(rustc_bin), "--edition", "2024", "-O", "-L", str(sysroot / "lib"), str(DRIVER_RS), "-o", str(probe_bin)],
            env=env,
            capture_output=True,
            text=True,
        )
        if comp.returncode != 0:
            raise RuntimeError(f"Failed to build driver:\n{comp.stderr}")

        nosrc = tmp / "sysroot-nosrc"
        (nosrc / "lib" / "rustlib").mkdir(parents=True)
        os.symlink(
            sysroot / "lib" / "rustlib" / "x86_64-unknown-linux-gnu",
            nosrc / "lib" / "rustlib" / "x86_64-unknown-linux-gnu",
        )

        results = []
        for name, ed, body, expected_suffix in cases:
            cdir = tmp / "cases" / name
            cdir.mkdir(parents=True)
            src = cdir / "lib.rs"
            src.write_text(
                f"#![no_std]\n"
                f"pub fn selected(x: u32) -> u32 {{ x.wrapping_add(1) }}\n"
                f"#[allow(unused)]\n"
                f"pub fn unselected(x: u32) -> u32 {{ {body} x }}\n"
            )
            for mode in ("default", "nosrc"):
                out_dir = tmp / f"out_{name}_{mode}"
                out_dir.mkdir()
                cmd = [
                    str(probe_bin),
                    "rustc",
                    "--edition",
                    ed,
                    "--crate-type",
                    "lib",
                    "--crate-name",
                    "probe",
                    "--emit=metadata",
                    "-Copt-level=0",
                    "-Cdebug-assertions=no",
                    "-Coverflow-checks=no",
                    "--out-dir",
                    str(out_dir),
                ]
                if mode == "nosrc":
                    cmd.append(f"--sysroot={nosrc}")
                cmd.append(str(src))
                cenv = env.copy()
                cenv["PROBE_ALLOWED"] = str(src.resolve())
                cenv["PROBE_BACKTRACE"] = "1"
                p = subprocess.run(cmd, env=cenv, capture_output=True, text=True)
                refusals = [
                    m.group(1)
                    for line in p.stderr.splitlines()
                    if (m := re.search(r"\[probe\] REFUSAL: undeclared compiler read: ([^:]+):", line))
                ]
                bt_top = [l.strip() for l in p.stderr.splitlines() if l.startswith("[probe-bt]")]
                expected_ec = 3 if expected_suffix else 0
                assert p.returncode == expected_ec, (
                    f"{name}/{mode}: expected exit {expected_ec}, got {p.returncode}\n{p.stderr}"
                )
                if expected_suffix:
                    assert any(r.endswith(expected_suffix) for r in refusals), (
                        f"{name}/{mode}: expected {expected_suffix}, got {refusals}"
                    )
                    assert any("make_format_args" in l for l in bt_top), (
                        f"{name}/{mode}: missing make_format_args frame in backtrace: {bt_top}"
                    )
                else:
                    assert not refusals, f"{name}/{mode}: unexpected refusals {refusals}"
                results.append(
                    {
                        "case": name,
                        "edition": ed,
                        "sysroot_mode": mode,
                        "exit_code": p.returncode,
                        "refused_paths": refusals,
                        "has_span_to_snippet": any("span_to_snippet" in l for l in bt_top),
                    }
                )

    print(json.dumps({"status": "PASS", "rustc": ver_info.splitlines()[0], "cases": len(results), "results": results}, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
