#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reproducible probe for rustc MIR lowering subtleties across toolchains.

Runs `rustc +nightly-2026-03-19` and `rustc +nightly-2026-05-31` in temporary
directories (leaving zero build artifacts in the package directory) on
`mir_subtleties_specimen.rs` across:
  1. Partial moves out of multi-field non-`Copy` aggregates (`Operand::Move`).
  2. `StatementKind::PlaceMention` erasure vs. `-Z mir-preserve-ub` retention.
  3. Dead-branch associated constant (`if false { let _ = Fail::<T>::C; }`)
     across `built`, `runtime-post-cleanup`, `SimplifyConstCondition`, and
     `runtime-optimized`, plus monomorphization (`E0080`) verification.
  4. Compiler-inserted `TerminatorKind::Assert` (`checked_add`, `bad_overflow`)
     vs. `core::panicking::panic` (`explicit_assert`) and `#[cfg(debug_assertions)]`
     item shifts across `(debug-assertions=yes/no) x (overflow-checks=yes/no)`.
"""

from __future__ import annotations

import json
import pathlib
import re
import subprocess
import tempfile
from typing import Any

TOOLCHAINS = [
    "+nightly-2026-03-19",
    "+nightly-2026-05-31",
]

FN_HEADER_RE = re.compile(r"^fn\s+([A-Za-z0-9_<>:]+)\s*\(", re.MULTILINE)


def get_version_info(toolchain: str) -> dict[str, str]:
    out = subprocess.check_output(
        ["rustc", toolchain, "-vV"], text=True
    ).strip()
    info: dict[str, str] = {}
    for idx, line in enumerate(out.splitlines()):
        if idx == 0:
            info["headline"] = line
        elif ":" in line:
            k, v = line.split(":", 1)
            info[k.strip()] = v.strip()
    return info


def dump_mir_pass(
    toolchain: str,
    src_path: pathlib.Path,
    pass_filter: str,
    extra_flags: list[str],
) -> dict[str, str]:
    with tempfile.TemporaryDirectory() as tmp:
        tmp_dir = pathlib.Path(tmp)
        dump_dir = tmp_dir / "dump"
        cmd = [
            "rustc",
            toolchain,
            "--crate-type=lib",
            "--emit=mir",
            f"-Zdump-mir={pass_filter}",
            "-Zdump-mir-exclude-pass-number=no",
            f"-Zdump-mir-dir={dump_dir}",
            *extra_flags,
            "-o",
            str(tmp_dir / "out.mir"),
            str(src_path),
        ]
        subprocess.run(cmd, check=True, capture_output=True, text=True)
        results: dict[str, str] = {}
        if dump_dir.exists():
            for p in sorted(dump_dir.glob("*.mir")):
                results[p.name] = p.read_text()
        results["__emitted_mir__"] = (tmp_dir / "out.mir").read_text()
        return results


def find_dump(dumps: dict[str, str], fn_name: str, pass_suffix: str) -> str:
    for name, content in dumps.items():
        if f".{fn_name}." in name and name.endswith(pass_suffix):
            return content
    raise KeyError(f"Missing dump for {fn_name} with suffix {pass_suffix}")


def extract_body_lines(mir_text: str) -> list[str]:
    return [
        line.strip()
        for line in mir_text.splitlines()
        if line.strip() and not line.strip().startswith("//")
    ]


def probe_toolchain(toolchain: str, specimen_path: pathlib.Path) -> dict[str, Any]:
    vinfo = get_version_info(toolchain)

    # 1 & 2 & 3: Dump built, RemovePlaceMention, runtime-post-cleanup,
    # SimplifyConstCondition, SimplifyLocals-before-const-prop, and runtime-optimized
    pass_filter = (
        "built|RemovePlaceMention|runtime-post-cleanup|"
        "SimplifyConstCondition-after-inst-simplify|"
        "SimplifyLocals-before-const-prop|runtime-optimized"
    )
    default_dumps = dump_mir_pass(toolchain, specimen_path, pass_filter, [])
    preserve_ub_dumps = dump_mir_pass(
        toolchain, specimen_path, pass_filter, ["-Zmir-preserve-ub"]
    )

    # (a) Partial move out of multi-field non-Copy struct
    pm_post_cleanup = find_dump(
        default_dumps, "partial_move_sibling", "runtime-post-cleanup.after.mir"
    )
    pm_moves = [
        line.strip()
        for line in pm_post_cleanup.splitlines()
        if "move (_1." in line or "StorageDead(_1)" in line
    ]

    # (b) PlaceMention erasure vs. -Z mir-preserve-ub retention
    pl_built = find_dump(
        default_dumps, "place_mention_raw_ptr", "built.after.mir"
    )
    pl_default_post = find_dump(
        default_dumps,
        "place_mention_raw_ptr",
        "runtime-post-cleanup.after.mir",
    )
    pl_preserve_post = find_dump(
        preserve_ub_dumps,
        "place_mention_raw_ptr",
        "runtime-post-cleanup.after.mir",
    )
    pl_preserve_opt = find_dump(
        preserve_ub_dumps,
        "place_mention_raw_ptr",
        "runtime-optimized.after.mir",
    )

    # (c) Dead-branch PME (`if false { let _ = Fail::<T>::C; }`)
    db_built = find_dump(default_dumps, "dead_branch_pme", "built.after.mir")
    db_post_cleanup = find_dump(
        default_dumps, "dead_branch_pme", "runtime-post-cleanup.after.mir"
    )
    db_after_scc = find_dump(
        default_dumps,
        "dead_branch_pme",
        "SimplifyConstCondition-after-inst-simplify.after.mir",
    )
    db_after_simplify_locals = find_dump(
        default_dumps,
        "dead_branch_pme",
        "SimplifyLocals-before-const-prop.after.mir",
    )
    db_opt = find_dump(
        default_dumps, "dead_branch_pme", "runtime-optimized.after.mir"
    )

    # Also test monomorphization of `dead_branch_pme::<u8>()` vs unreachable-after-return
    with tempfile.TemporaryDirectory() as tmp:
        tmp_dir = pathlib.Path(tmp)
        mono_src = tmp_dir / "mono_test.rs"
        mono_src.write_text(
            specimen_path.read_text()
            + "\npub fn instantiate_dead_branch_pme() -> usize { dead_branch_pme::<u8>() }\n"
        )
        mono_res = subprocess.run(
            [
                "rustc",
                toolchain,
                "--crate-type=lib",
                "--emit=obj",
                "-o",
                str(tmp_dir / "mono.o"),
                str(mono_src),
            ],
            capture_output=True,
            text=True,
        )

    # (d) Matrix of (debug-assertions=yes/no) x (overflow-checks=yes/no)
    profiles: dict[str, Any] = {}
    for dbg in ("yes", "no"):
        for ovf in ("yes", "no"):
            key = f"debug_assertions_{dbg}__overflow_checks_{ovf}"
            flags = [
                f"-Cdebug-assertions={dbg}",
                f"-Coverflow-checks={ovf}",
            ]
            prof_dumps = dump_mir_pass(
                toolchain,
                specimen_path,
                "runtime-post-cleanup",
                flags,
            )
            emitted_fns = FN_HEADER_RE.findall(prof_dumps["__emitted_mir__"])
            ca_mir = find_dump(
                prof_dumps, "checked_add", "runtime-post-cleanup.after.mir"
            )
            bo_mir = find_dump(
                prof_dumps, "bad_overflow", "runtime-post-cleanup.after.mir"
            )
            ea_mir = find_dump(
                prof_dumps, "explicit_assert", "runtime-post-cleanup.after.mir"
            )
            profiles[key] = {
                "flags": flags,
                "emitted_fn_order": emitted_fns,
                "debug_only_helper_present": "debug_only_helper" in emitted_fns,
                "checked_add_has_add_with_overflow": "AddWithOverflow(" in ca_mir,
                "checked_add_has_assert_terminator": "assert(!move (" in ca_mir,
                "checked_add_has_wrapping_add": " = Add(" in ca_mir,
                "bad_overflow_has_assert_terminator": "assert(!move (" in bo_mir,
                "bad_overflow_has_unreachable_call": "unreachable_unchecked()" in bo_mir,
                "explicit_assert_has_switch_int": "switchInt(" in ea_mir,
                "explicit_assert_has_panic_call": "panic(const \"assertion failed: x > 0\")"
                in ea_mir,
                "explicit_assert_has_assert_terminator": any(
                    line.strip().startswith("assert(")
                    for line in ea_mir.splitlines()
                ),
            }

    return {
        "version": vinfo,
        "partial_move_sibling": {
            "runtime_post_cleanup_move_and_storage_lines": pm_moves,
            "has_move_field_0": any("move (_1.0: NonCopy)" in l for l in pm_moves),
            "has_move_field_1": any("move (_1.1: NonCopy)" in l for l in pm_moves),
            "has_storage_dead_on_root_param": any(
                "StorageDead(_1)" in l for l in pm_moves
            ),
        },
        "place_mention_raw_ptr": {
            "built_has_place_mention": "PlaceMention((*_1));" in pl_built,
            "default_runtime_post_cleanup_has_place_mention": "PlaceMention("
            in pl_default_post,
            "preserve_ub_runtime_post_cleanup_has_place_mention": "PlaceMention((*_1));"
            in pl_preserve_post,
            "preserve_ub_runtime_optimized_has_place_mention": "PlaceMention((*_1));"
            in pl_preserve_opt,
            "default_runtime_post_cleanup_lines": extract_body_lines(
                pl_default_post
            ),
            "preserve_ub_runtime_post_cleanup_lines": extract_body_lines(
                pl_preserve_post
            ),
        },
        "dead_branch_pme": {
            "built_has_fail_const": "const Fail::<T>::C" in db_built,
            "runtime_post_cleanup_has_fail_const_in_dead_bb": "const Fail::<T>::C"
            in db_post_cleanup,
            "after_simplify_const_condition_has_switch_int": "switchInt("
            in db_after_scc,
            "after_simplify_const_condition_has_fail_const": "const Fail::<T>::C"
            in db_after_scc,
            "after_simplify_locals_has_fail_const": "const Fail::<T>::C"
            in db_after_simplify_locals,
            "runtime_optimized_has_fail_const_in_bbs": "const Fail::<T>::C"
            in db_opt,
            "monomorphize_u8_exit_code": mono_res.returncode,
            "monomorphize_u8_triggers_e0080": "error[E0080]" in mono_res.stderr,
        },
        "profiles": profiles,
    }


def main() -> None:
    here = pathlib.Path(__file__).resolve().parent
    specimen_path = here / "mir_subtleties_specimen.rs"
    output_path = here / "mir_subtleties_output.json"

    report: dict[str, Any] = {
        "specimen": specimen_path.name,
        "toolchains": {},
    }
    for tc in TOOLCHAINS:
        report["toolchains"][tc] = probe_toolchain(tc, specimen_path)

    output_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"Wrote {output_path}")


if __name__ == "__main__":
    main()
