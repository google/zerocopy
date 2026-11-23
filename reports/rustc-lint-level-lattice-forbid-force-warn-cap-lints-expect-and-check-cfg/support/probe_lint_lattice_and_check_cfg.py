#!/usr/bin/env python3
"""Reproducible empirical probe for rustc lint-level lattice, forbid,
--cap-lints, --force-warn, #[expect], --check-cfg, and #[cfg_attr] expansion.

Runs entirely inside a temporary directory and records exact command lines,
rustc version/commit metadata, exit codes, stdout, and stderr.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
from typing import Any


SLUG = "rustc-lint-level-lattice-forbid-force-warn-cap-lints-expect-and-check-cfg"


def run_rustc_case(
    tmp: Path,
    case_id: str,
    code: str,
    *,
    edition: str = "2024",
    crate_type: str = "bin",
    extra_args: list[str] | None = None,
    run_binary: bool = False,
) -> dict[str, Any]:
    case_dir = tmp / case_id
    case_dir.mkdir(parents=True, exist_ok=True)
    src_path = case_dir / "probe.rs"
    src_path.write_text(code, encoding="utf-8")

    out_path = case_dir / ("libprobe.rlib" if crate_type == "lib" else "probe_bin")
    cmd = [
        "rustc",
        f"--edition={edition}",
        f"--crate-type={crate_type}",
        "--color=never",
        *(extra_args or []),
        "-o",
        str(out_path),
        str(src_path),
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, cwd=case_dir, timeout=30)

    def sanitize(text: str) -> str:
        # Keep paths relative/clean so probe_results.json never leaks temp dirs or host paths.
        return text.replace(str(case_dir) + "/", "").replace(str(case_dir), "<tmpdir>").strip()

    result: dict[str, Any] = {
        "case_id": case_id,
        "edition": edition,
        "crate_type": crate_type,
        "extra_args": list(extra_args or []),
        "source_sha256": hashlib.sha256(code.encode("utf-8")).hexdigest(),
        "source": code,
        "compile_cmd": [
            "rustc",
            f"--edition={edition}",
            f"--crate-type={crate_type}",
            "--color=never",
            *(extra_args or []),
            "-o",
            out_path.name,
            "probe.rs",
        ],
        "compile_returncode": proc.returncode,
        "compile_stdout": sanitize(proc.stdout),
        "compile_stderr": sanitize(proc.stderr),
    }

    if run_binary and proc.returncode == 0 and crate_type == "bin" and out_path.exists():
        run_proc = subprocess.run([str(out_path)], capture_output=True, text=True, cwd=case_dir, timeout=15)
        result["run_returncode"] = run_proc.returncode
        result["run_stdout"] = run_proc.stdout.strip()
        result["run_stderr"] = run_proc.stderr.strip()

    return result


def collect_probe_results() -> dict[str, Any]:
    ver_proc = subprocess.run(["rustc", "-Vv"], capture_output=True, text=True, check=True)
    rustc_vv = ver_proc.stdout.strip()
    commit_hash = ""
    release = ""
    host = ""
    for line in rustc_vv.splitlines():
        if line.startswith("commit-hash:"):
            commit_hash = line.split(":", 1)[1].strip()
        elif line.startswith("release:"):
            release = line.split(":", 1)[1].strip()
        elif line.startswith("host:"):
            host = line.split(":", 1)[1].strip()

    results: dict[str, Any] = {
        "schema": "rustc-lint-lattice-check-cfg-probe/1",
        "rustc_vv": rustc_vv,
        "rustc_release": release,
        "rustc_commit_hash": commit_hash,
        "host": host,
        "platform": platform.platform(),
        "cases": {},
    }

    with tempfile.TemporaryDirectory(prefix="rustc_lint_probe_") as td:
        tmp = Path(td)
        cases: dict[str, Any] = {}

        # --- Group A: Forbid, E0453, forbidden_lint_groups FCW, --cap-lints, --force-warn, #[expect] ---
        forbid_unsafe_src = (
            "#![forbid(unsafe_code)]\n"
            "\n"
            "#[allow(unsafe_code)]\n"
            "fn f() {\n"
            "    unsafe {}\n"
            "}\n"
            "fn main() {}\n"
        )
        cases["a01_forbid_overruled_by_allow_e0453"] = run_rustc_case(
            tmp, "a01", forbid_unsafe_src
        )
        cases["a02_forbid_overruled_by_expect_e0453"] = run_rustc_case(
            tmp,
            "a02",
            "#![forbid(unsafe_code)]\n#[expect(unsafe_code)]\nfn f() {\n    unsafe {}\n}\nfn main() {}\n",
        )
        cases["a03_forbid_overruled_by_warn_e0453"] = run_rustc_case(
            tmp,
            "a03",
            "#![forbid(unsafe_code)]\n#[warn(unsafe_code)]\nfn f() {\n    unsafe {}\n}\nfn main() {}\n",
        )
        cases["a04_forbid_with_inner_deny_ignored"] = run_rustc_case(
            tmp,
            "a04",
            "#![forbid(unsafe_code)]\n#[deny(unsafe_code)]\nfn f() {\n    unsafe {}\n}\nfn main() {}\n",
        )
        cases["a05_forbid_deny_then_allow_still_e0453"] = run_rustc_case(
            tmp,
            "a05",
            "#![forbid(unsafe_code)]\n#[deny(unsafe_code)]\n#[allow(unsafe_code)]\nfn f() {\n    unsafe {}\n}\nfn main() {}\n",
        )
        cases["a06_allow_then_forbid_same_item_valid"] = run_rustc_case(
            tmp,
            "a06",
            "#[allow(unsafe_code)]\n#[forbid(unsafe_code)]\nfn f() {\n    unsafe {}\n}\nfn main() {}\n",
        )

        # Group forbid vs member allow/expect (FCW #81670)
        cases["a07_forbid_group_vs_member_allow_fcw"] = run_rustc_case(
            tmp,
            "a07",
            "#![forbid(unused)]\n#[allow(dead_code)]\nfn unused_fn() {}\nfn main() {}\n",
        )
        cases["a08_forbid_group_vs_same_group_allow_fcw"] = run_rustc_case(
            tmp,
            "a08",
            "#![forbid(unused)]\n#[allow(unused)]\nfn unused_fn() {}\nfn main() {}\n",
        )
        cases["a09_forbid_group_vs_member_expect_fcw"] = run_rustc_case(
            tmp,
            "a09",
            "#![forbid(unused)]\n#[expect(dead_code)]\nfn unused_fn() {}\nfn main() {}\n",
        )
        cases["a10_cli_forbid_group_vs_member_allow_fcw"] = run_rustc_case(
            tmp,
            "a10",
            "#[allow(dead_code)]\nfn unused_fn() {}\nfn main() {}\n",
            extra_args=["-F", "unused"],
        )
        cases["a11_forbid_warnings_vs_member_allow_dead_code"] = run_rustc_case(
            tmp,
            "a11",
            "#![forbid(warnings)]\n#[allow(dead_code)]\nfn unused_fn() {}\nfn main() {}\n",
        )
        cases["a11b_forbid_warnings_vs_allow_default_lint_unsafe"] = run_rustc_case(
            tmp,
            "a11b",
            "#![forbid(warnings)]\n#[allow(unsafe_code)]\npub fn f() { unsafe {} }\nfn main() {}\n",
        )
        cases["a11c_forbid_warnings_vs_warn_then_allow_unsafe"] = run_rustc_case(
            tmp,
            "a11c",
            "#![forbid(warnings)]\n#[warn(unsafe_code)]\n#[allow(unsafe_code)]\npub fn f() { unsafe {} }\nfn main() {}\n",
        )
        cases["a11d_forbid_unused_allow_then_warn_dead_code"] = run_rustc_case(
            tmp,
            "a11d",
            "#![forbid(unused)]\n#[allow(dead_code)]\n#[warn(dead_code)]\nfn unused() {}\nfn main() {}\n",
        )
        cases["a12_forbid_warnings_vs_allow_warnings_fcw"] = run_rustc_case(
            tmp,
            "a12",
            "#![forbid(warnings)]\n#[allow(warnings)]\nfn unused_fn() {}\nfn main() {}\n",
        )
        cases["a12b_direct_forbid_then_group_forbid_then_allow_downgrades"] = run_rustc_case(
            tmp,
            "a12b",
            "#![forbid(dead_code)]\n#[forbid(unused)]\n#[allow(dead_code)]\nfn unused_fn() {}\nfn main() {}\n",
        )

        # --cap-lints matrix
        cap_src = (
            "#![forbid(unsafe_code)]\n"
            "#![deny(dead_code)]\n"
            "\n"
            "fn unused() {\n"
            "    unsafe {}\n"
            "}\n"
            "fn main() {\n"
            "    println!(\"CAP_LINTS_OK\");\n"
            "}\n"
        )
        cases["a13_cap_lints_uncapped_default_rejected"] = run_rustc_case(
            tmp, "a13", cap_src
        )
        cases["a14_cap_lints_warn_downgrades_forbid_and_deny"] = run_rustc_case(
            tmp, "a14", cap_src, extra_args=["--cap-lints=warn"], run_binary=True
        )
        cases["a15_cap_lints_allow_silences_forbid_and_deny"] = run_rustc_case(
            tmp, "a15", cap_src, extra_args=["--cap-lints=allow"], run_binary=True
        )
        cases["a16_cap_lints_deny_caps_forbid_to_deny"] = run_rustc_case(
            tmp, "a16", cap_src, extra_args=["--cap-lints=deny"]
        )

        # --cap-lints effect on E0453
        cases["a17_cap_lints_deny_removes_e0453"] = run_rustc_case(
            tmp, "a17", forbid_unsafe_src, extra_args=["--cap-lints=deny"], run_binary=True
        )
        cases["a18_cap_lints_warn_removes_e0453"] = run_rustc_case(
            tmp, "a18", forbid_unsafe_src, extra_args=["--cap-lints=warn"], run_binary=True
        )
        cases["a19_cap_lints_allow_removes_e0453"] = run_rustc_case(
            tmp, "a19", forbid_unsafe_src, extra_args=["--cap-lints=allow"], run_binary=True
        )

        # Repeated --cap-lints order (first wins via opt_str)
        cases["a20_cap_lints_repeated_allow_then_forbid"] = run_rustc_case(
            tmp,
            "a20",
            "#![forbid(unsafe_code)]\nfn main() { unsafe {} }\n",
            extra_args=["--cap-lints=allow", "--cap-lints=forbid"],
        )
        cases["a21_cap_lints_repeated_forbid_then_allow"] = run_rustc_case(
            tmp,
            "a21",
            "#![forbid(unsafe_code)]\nfn main() { unsafe {} }\n",
            extra_args=["--cap-lints=forbid", "--cap-lints=allow"],
        )

        # CLI flag ordering and stickiness
        unused_src = "fn unused() {}\nfn main() {}\n"
        cases["a22_cli_forbid_dead_code"] = run_rustc_case(
            tmp, "a22", unused_src, extra_args=["-F", "dead_code"]
        )
        cases["a23_cli_forbid_then_allow_sticky"] = run_rustc_case(
            tmp, "a23", unused_src, extra_args=["-F", "dead_code", "-A", "dead_code"]
        )
        cases["a24_cli_allow_then_forbid_raises"] = run_rustc_case(
            tmp, "a24", unused_src, extra_args=["-A", "dead_code", "-F", "dead_code"]
        )
        cases["a25_cli_deny_then_allow_overrides"] = run_rustc_case(
            tmp, "a25", unused_src, extra_args=["-D", "dead_code", "-A", "dead_code"]
        )
        cases["a26_cli_allow_then_deny_overrides"] = run_rustc_case(
            tmp, "a26", unused_src, extra_args=["-A", "dead_code", "-D", "dead_code"]
        )

        # --force-warn matrix
        allow_unused_src = "#[allow(dead_code)]\nfn unused_item() {}\nfn main() {}\n"
        cases["a27_force_warn_overrides_allow"] = run_rustc_case(
            tmp, "a27", allow_unused_src, extra_args=["--force-warn", "dead_code"]
        )
        cases["a28_force_warn_bypasses_cap_lints_allow"] = run_rustc_case(
            tmp,
            "a28",
            allow_unused_src,
            extra_args=["--cap-lints=allow", "--force-warn", "dead_code"],
        )
        cases["a29_force_warn_beats_forbid_attr"] = run_rustc_case(
            tmp,
            "a29",
            "#![forbid(dead_code)]\nfn unused_item() {}\nfn main() {}\n",
            extra_args=["--force-warn", "dead_code"],
        )
        cases["a30_cli_force_warn_then_forbid_keeps_force_warn"] = run_rustc_case(
            tmp,
            "a30",
            unused_src,
            extra_args=["--force-warn", "dead_code", "-F", "dead_code"],
        )
        cases["a31_cli_forbid_then_force_warn_keeps_forbid"] = run_rustc_case(
            tmp,
            "a31",
            unused_src,
            extra_args=["-F", "dead_code", "--force-warn", "dead_code"],
        )
        cases["a32_cli_force_warn_warnings_rejected"] = run_rustc_case(
            tmp,
            "a32",
            "fn main() {}\n",
            extra_args=["--force-warn", "warnings"],
        )

        # -A warnings session-level can_emit_warnings interaction
        cases["a33_cli_allow_warnings_vs_crate_warn_warnings"] = run_rustc_case(
            tmp,
            "a33",
            "#![warn(warnings)]\n#[warn(dead_code)]\nfn unused() {}\nfn main() {}\n",
            extra_args=["-A", "warnings"],
        )
        cases["a33b_cli_allow_warnings_vs_crate_deny_dead_code"] = run_rustc_case(
            tmp,
            "a33b",
            "#![deny(dead_code)]\nfn unused() {}\nfn main() {}\n",
            extra_args=["-A", "warnings"],
        )
        cases["a34_cli_allow_warnings_then_warn_warnings_cli"] = run_rustc_case(
            tmp,
            "a34",
            "fn unused() {}\nfn main() {}\n",
            extra_args=["-A", "warnings", "-W", "warnings"],
        )

        # RFC 2383 #[expect] matrix
        cases["a35_expect_fulfilled_silent"] = run_rustc_case(
            tmp,
            "a35",
            "#[expect(dead_code)]\nfn unused() {}\nfn main() {}\n",
        )
        cases["a36_expect_unfulfilled_warn_with_reason"] = run_rustc_case(
            tmp,
            "a36",
            "#[expect(dead_code, reason = \"kept for probe\")]\nfn used() {}\nfn main() { used(); }\n",
        )
        cases["a37_expect_fulfilled_with_cli_allow"] = run_rustc_case(
            tmp,
            "a37",
            "#[expect(dead_code)]\nfn unused() {}\nfn main() {}\n",
            extra_args=["-A", "dead_code"],
        )
        cases["a38_expect_unfulfilled_with_cli_allow_still_warns"] = run_rustc_case(
            tmp,
            "a38",
            "#[expect(dead_code)]\nfn used() {}\nfn main() { used(); }\n",
            extra_args=["-A", "dead_code"],
        )
        cases["a39_expect_unfulfilled_suppressed_by_cli_allow_warnings"] = run_rustc_case(
            tmp,
            "a39",
            "#[expect(dead_code)]\nfn used() {}\nfn main() { used(); }\n",
            extra_args=["-A", "warnings"],
        )
        cases["a40_expect_fulfilled_suppressed_by_cap_lints_allow"] = run_rustc_case(
            tmp,
            "a40",
            "#[expect(dead_code)]\nfn unused() {}\nfn main() {}\n",
            extra_args=["--cap-lints=allow"],
        )
        cases["a41_expect_unfulfilled_suppressed_by_cap_lints_allow"] = run_rustc_case(
            tmp,
            "a41",
            "#[expect(dead_code)]\nfn used() {}\nfn main() { used(); }\n",
            extra_args=["--cap-lints=allow"],
        )
        cases["a42_expect_fulfilled_with_force_warn"] = run_rustc_case(
            tmp,
            "a42",
            "#[expect(dead_code)]\nfn unused() {}\nfn main() {}\n",
            extra_args=["--force-warn", "dead_code"],
        )
        cases["a43_expect_unfulfilled_with_force_warn"] = run_rustc_case(
            tmp,
            "a43",
            "#[expect(dead_code)]\nfn used() {}\nfn main() { used(); }\n",
            extra_args=["--force-warn", "dead_code"],
        )
        cases["a44_expect_overridden_by_inner_allow_unfulfilled"] = run_rustc_case(
            tmp,
            "a44",
            "#[expect(dead_code)]\n#[allow(dead_code)]\nfn unused() {}\nfn main() {}\n",
        )
        cases["a45_expect_overridden_by_inner_allow_under_force_warn"] = run_rustc_case(
            tmp,
            "a45",
            "#[expect(dead_code)]\n#[allow(dead_code)]\nfn unused() {}\nfn main() {}\n",
            extra_args=["--force-warn", "dead_code"],
        )
        cases["a46_expect_unfulfilled_lint_expectations_ignored"] = run_rustc_case(
            tmp,
            "a46",
            "#[expect(unfulfilled_lint_expectations)]\nfn main() {}\n",
        )

        # Attribute ordering on same node & nested scope
        cases["a47_later_allow_overrides_earlier_warn"] = run_rustc_case(
            tmp,
            "a47",
            "#[warn(dead_code)]\n#[allow(dead_code)]\nfn unused() {}\nfn main() {}\n",
        )
        cases["a48_later_warn_overrides_earlier_allow"] = run_rustc_case(
            tmp,
            "a48",
            "#[allow(dead_code)]\n#[warn(dead_code)]\nfn unused() {}\nfn main() {}\n",
        )
        cases["a49_nested_scope_overrides_crate_deny"] = run_rustc_case(
            tmp,
            "a49",
            "#![deny(dead_code)]\n#[allow(dead_code)]\nfn unused() {}\nfn main() {}\n",
        )

        # --- Group B: --check-cfg, #[cfg_attr(false, ...)], and #[cfg(false)] interaction ---
        cases["b01_check_cfg_expected_fast_silent"] = run_rustc_case(
            tmp,
            "b01",
            "#[cfg(feature = \"fast\")]\nfn fast_fn() {}\nfn main() {}\n",
            extra_args=["--check-cfg=cfg(feature, values(\"fast\"))"],
            run_binary=True,
        )
        cases["b02_check_cfg_typo_and_unknown_name_warn"] = run_rustc_case(
            tmp,
            "b02",
            "#[cfg(feature = \"typo\")]\nfn a() {}\n#[cfg(unknown_flag)]\nfn b() {}\nfn main() {}\n",
            extra_args=["--check-cfg=cfg(feature, values(\"fast\"))"],
        )
        cases["b03_check_cfg_checks_false_cfg_attr_predicate"] = run_rustc_case(
            tmp,
            "b03",
            "#[cfg_attr(unknown_pred, allow(dead_code))]\nfn main() {}\n",
            extra_args=["--check-cfg=cfg(feature, values(\"fast\"))"],
        )
        cases["b04_cfg_attr_false_strips_malformed_and_unknown_inner_attrs"] = run_rustc_case(
            tmp,
            "b04",
            (
                "#![forbid(unsafe_code)]\n"
                "#[cfg_attr(false, inline(bogus_never_valid))]\n"
                "#[cfg_attr(false, cfg(unknown_nested_cfg))]\n"
                "#[cfg_attr(false, allow(nonexistent_bogus_lint))]\n"
                "#[cfg_attr(false, allow(unsafe_code))]\n"
                "fn helper() -> u32 { 7 }\n"
                "fn main() { println!(\"CFG_ATTR_STRIPPED={}\", helper()); }\n"
            ),
            extra_args=["--check-cfg=cfg(feature, values(\"fast\"))"],
            run_binary=True,
        )
        cases["b05_cfg_attr_true_rejects_malformed_inner_attr"] = run_rustc_case(
            tmp,
            "b05",
            "#[cfg_attr(true, inline(bogus_never_valid))]\nfn f() {}\nfn main() {}\n",
        )
        cases["b06a_cfg_attr_true_triggers_e0453_and_unexpected_cfgs"] = run_rustc_case(
            tmp,
            "b06a",
            (
                "#![forbid(unsafe_code)]\n"
                "#[cfg_attr(true, allow(unsafe_code))]\n"
                "fn f1() { unsafe {} }\n"
                "#[cfg_attr(true, cfg(unknown_nested_cfg))]\n"
                "fn f2() {}\n"
                "fn main() {}\n"
            ),
            extra_args=["--check-cfg=cfg(feature, values(\"fast\"))"],
        )
        cases["b06b_cfg_attr_true_allow_plus_false_cfg_strips_item_before_e0453"] = run_rustc_case(
            tmp,
            "b06b",
            (
                "#![forbid(unsafe_code)]\n"
                "#[cfg_attr(true, allow(unsafe_code))]\n"
                "#[cfg_attr(true, cfg(unknown_nested_cfg))]\n"
                "fn f() { unsafe {} }\n"
                "fn main() {}\n"
            ),
            extra_args=["--check-cfg=cfg(feature, values(\"fast\"))"],
        )
        cases["b07_cfg_attr_false_still_requires_attr_item_syntax"] = run_rustc_case(
            tmp,
            "b07",
            "#[cfg_attr(false, 123_not_an_attr)]\nfn main() {}\n",
        )
        cases["b08_cfg_false_strips_unvalidated_inner_attrs_and_e0453"] = run_rustc_case(
            tmp,
            "b08",
            (
                "#![forbid(unsafe_code)]\n"
                "#[cfg(false)]\n"
                "#[inline(bogus_never_valid)]\n"
                "#[allow(unsafe_code)]\n"
                "fn stripped() { unsafe {} }\n"
                "fn main() {}\n"
            ),
            extra_args=["--check-cfg=cfg(feature, values(\"fast\"))"],
        )
        cases["b09_cfg_false_short_circuits_second_cfg_attr_only_in_order"] = run_rustc_case(
            tmp,
            "b09",
            (
                "#[cfg(false)]\n"
                "#[cfg(unknown_second_cfg)]\n"
                "fn skipped() {}\n"
                "fn main() {}\n"
            ),
            extra_args=["--check-cfg=cfg()"],
        )
        cases["b10_cfg_unknown_first_then_cfg_false_warns"] = run_rustc_case(
            tmp,
            "b10",
            (
                "#[cfg(unknown_first_cfg)]\n"
                "#[cfg(false)]\n"
                "fn warns_first() {}\n"
                "fn main() {}\n"
            ),
            extra_args=["--check-cfg=cfg()"],
        )
        cases["b11_check_cfg_cap_lints_allow_vs_force_warn_unexpected_cfgs"] = run_rustc_case(
            tmp,
            "b11",
            "#[cfg(unknown_flag)]\nfn f() {}\nfn main() {}\n",
            extra_args=["--check-cfg=cfg()", "--cap-lints=allow", "--force-warn", "unexpected_cfgs"],
        )
        cases["b12a_crate_expect_covers_item_unexpected_cfgs"] = run_rustc_case(
            tmp,
            "b12a",
            "#![expect(unexpected_cfgs)]\n#[cfg(unknown_flag)]\nfn f() {}\nfn main() {}\n",
            extra_args=["--check-cfg=cfg()"],
        )
        cases["b12b_item_expect_misses_own_cfg_even_when_active"] = run_rustc_case(
            tmp,
            "b12b",
            "#[expect(unexpected_cfgs)]\n#[cfg(unknown_flag)]\nfn f() {}\nfn main() {}\n",
            extra_args=["--check-cfg=cfg()", "--cfg=unknown_flag"],
        )
        cases["b12c_item_expect_covers_cfg_macro_inside_body"] = run_rustc_case(
            tmp,
            "b12c",
            "#[expect(unexpected_cfgs)]\nfn f() -> bool { cfg!(unknown_flag) }\nfn main() { let _ = f(); }\n",
            extra_args=["--check-cfg=cfg()"],
        )
        cases["b12d_mod_expect_covers_inner_item_cfg"] = run_rustc_case(
            tmp,
            "b12d",
            "#[expect(unexpected_cfgs)]\nmod m {\n    #[cfg(unknown_flag)]\n    pub fn f() {}\n}\nfn main() {}\n",
            extra_args=["--check-cfg=cfg()"],
        )

        results["cases"] = cases

    return results


def main(argv: list[str] | None = None) -> int:
    default_out = Path(__file__).resolve().parent / "probe_results.json"
    parser = argparse.ArgumentParser(
        description="Run the rustc lint-level, cap-lints, force-warn, expect, and check-cfg probe matrix."
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        default=default_out,
        help=f"Output JSON path (default: {default_out})",
    )
    args = parser.parse_args(argv)
    out_path = args.output
    out_path.parent.mkdir(parents=True, exist_ok=True)
    results = collect_probe_results()
    out_path.write_text(json.dumps(results, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    n_cases = len(results["cases"])
    print(f"wrote {out_path} ({n_cases} cases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
