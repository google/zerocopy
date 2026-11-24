#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/check_mir_differential.py`."""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys
import tempfile
from typing import Any
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_mir_differential as cmd  # noqa: E402
import perf_tracking  # noqa: E402


def _sample_diff_report(*, unsound: int = 0, killed: int = 5, total: int = 5) -> dict:
    cases = [
        {
            "id": "arith_u32_wrapping_add",
            "source": "src/arith_pass.rs",
            "function": "u32_wrapping_add",
            "category": "arith",
            "expected": "pass",
            "allow_conservative_unsupported": False,
            "kernel_checked": True,
            "miri": {
                "kind": "returned",
                "value": {"kind": "int", "int_kind": "u32", "bits": "4"},
            },
            "lean": {
                "kind": "returned",
                "value": {"kind": "int", "int_kind": "u32", "bits": "4"},
            },
            "verdict": {
                "kind": "agree_value",
                "value": {"kind": "int", "int_kind": "u32", "bits": "4"},
            },
        },
        {
            "id": "ub_div_zero_u32",
            "source": "src/ub_corpus.rs",
            "function": "div_zero_u32",
            "category": "ub",
            "expected": "ub",
            "allow_conservative_unsupported": False,
            "kernel_checked": True,
            "miri": {
                "kind": "undefined_behavior",
                "detail": "error: Undefined Behavior: dividing by zero",
            },
            "lean": {"kind": "undefined_behavior", "detail": "undefined"},
            "verdict": (
                {"kind": "unsound_missed_fault"}
                if unsound > 0
                else {"kind": "agree_undefined_behavior"}
            ),
        },
        {
            "id": "unsup_diverging_abort_call",
            "source": "src/unsupported_controls.rs",
            "function": "abort_control",
            "category": "unsupported_control",
            "expected": "unsupported_control",
            "allow_conservative_unsupported": True,
            "kernel_checked": False,
            "miri": {"kind": "abnormal_abort", "detail": "aborted"},
            "lean": {"kind": "unsupported", "detail": "unsupported"},
            "verdict": {
                "kind": "sound_conservative_abstraction",
                "miri": {"kind": "abnormal_abort", "detail": "aborted"},
                "lean_detail": "unsupported",
            },
        },
    ]
    return {
        "schema": "anneal-differential-run/v1",
        "alpha_notice": cmd.ALPHA_NOTICE,
        "mir_dialect": "profile_v1",
        "manifest_path": "tests/corpora/differential/profile_v1/manifest.toml",
        "capture_bin_source": "env_anneal_capture",
        "capture_bin_sha256": "c" * 64,
        "prebuilt_overlay": "staged:26/29",
        "legs": [
            "miri",
            "lean_step_core_captured",
            "lean_wp_kernel_single_block",
        ],
        "metrics": {
            "compared_count": 3,
            "pass_agreed_count": 1,
            "ub_agreed_count": 0 if unsound > 0 else 1,
            "conservative_unsupported_count": 1,
            "kernel_checked_pass_count": 1,
            "kernel_checked_ub_count": 0 if unsound > 0 else 1,
            "unsound_missed_fault_count": unsound,
            "value_mismatch_count": 0,
            "unexpected_conservative_count": 0,
            "leg_divergence_count": 0,
        },
        "red_flags_passed": 0 if unsound > 0 else 7,
        "red_flag_error": "unsound fault present" if unsound > 0 else None,
        "cases": cases,
        "mutant_check": {
            "total_mutants": total,
            "killed_mutants": killed,
            "killed_pct": (killed * 100.0 / total) if total else 0.0,
            "results": [],
            "synthetic_lean_probes": [
                {
                    "probe_id": "probe_move_deinit_ignored",
                    "description": "synthetic move-deinit check",
                    "passed": True,
                    "expected_kill_verdict": "UnsoundMissedFault",
                    "actual_verdict": "UnsoundMissedFault",
                }
            ],
        },
    }


class CheckMirDifferentialTests(unittest.TestCase):
    def test_detail_and_perf_metrics_validate_against_perf_tracking(self) -> None:
        diff = _sample_diff_report()
        detail = cmd.build_semantic_detail_report(
            diff_report=diff,
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux", "arch": "x86_64"},
        )
        self.assertEqual(detail["schema"], "anneal-semantic-detail/v1")
        self.assertEqual(detail["alpha_notice"], cmd.ALPHA_NOTICE)
        self.assertEqual(detail["trust_tier"], "candidate:mir_semantics")
        self.assertEqual(detail["known_bugs"], [])
        diff_ev = detail["evidence_blocks"]["differential_oracle"]
        self.assertEqual(diff_ev["capture_bin_source"], "env_anneal_capture")
        self.assertEqual(diff_ev["capture_bin_sha256"], "c" * 64)
        self.assertEqual(diff_ev["prebuilt_overlay"], "staged:26/29")
        self.assertEqual(detail["differential_runs"][0]["capture_bin_source"], "env_anneal_capture")
        self.assertEqual(detail["differential_runs"][0]["prebuilt_overlay"], "staged:26/29")
        self.assertTrue(cmd.report_passes(detail))

        perf = cmd.build_perf_metrics_snippet(diff)
        self.assertEqual(perf["differential_oracle.litmus.compared_count"], 3)
        self.assertEqual(
            perf["differential_oracle.litmus.kernel_checked_pass_count"], 1
        )
        self.assertEqual(perf["differential_oracle.litmus.kernel_checked_ub_count"], 1)
        self.assertEqual(
            perf["differential_oracle.litmus.unexpected_conservative_count"], 0
        )
        self.assertEqual(perf["differential_oracle.mutants.killed_pct"], 100.0)
        self.assertEqual(perf["differential_oracle.red_flags.passed_count"], 7)

        full_perf_record = {
            "schema": perf_tracking.RECORD_SCHEMA,
            "commit": {
                "sha": "a" * 40,
                "short_sha": "a" * 12,
                "timestamp": "2026-11-23T06:00:00Z",
                "unix_ts": 1_780_000_000,
                "subject": "Differential oracle telemetry",
                "branch": "main",
            },
            "environment": {
                "profile": "linux-x86_64",
                "os": "Linux",
                "arch": "x86_64",
                "cpu_model": "Test CPU",
                "vcpu_count": 4,
                "ram_total_kib": 16_000_000,
                "lean_version": "4.34.1",
                "rustc_version": "rustc 1.98.0-nightly",
            },
            "sampling": {
                "verify_repeats": 1,
                "aggregation": "single",
            },
            "metrics": perf,
        }
        validated = perf_tracking.validate_record(full_perf_record)
        self.assertEqual(validated["metrics"], perf)
        for metric_id in perf:
            desc = perf_tracking.describe_metric(metric_id)
            self.assertEqual(desc["category"], "differential_oracle")

    def test_rejects_empty_cases_missing_mutants_and_unsound_fault(self) -> None:
        bad_unsound = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(unsound=1),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="b" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        self.assertFalse(cmd.report_passes(bad_unsound))
        self.assertEqual(len(bad_unsound["known_bugs"]), 1)

        bad_mutant = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(killed=4, total=5),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="b" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        self.assertFalse(cmd.report_passes(bad_mutant))

        missing_mutants = _sample_diff_report()
        missing_mutants["mutant_check"] = None
        detail_no_mutants = cmd.build_semantic_detail_report(
            diff_report=missing_mutants,
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="b" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        self.assertFalse(cmd.report_passes(detail_no_mutants, require_mutants=True))
        self.assertTrue(cmd.report_passes(detail_no_mutants, require_mutants=False))

        empty_cases = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": None},
            repo="google/zerocopy",
            branch="main",
            commit_sha="b" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        empty_cases["differential_runs"][0]["cases"] = []
        self.assertFalse(cmd.report_passes(empty_cases))

    def test_maybe_run_mir_eval_manifest_absent_vs_present(self) -> None:
        status, bin_path = cmd.maybe_run_mir_eval_manifest(None)
        self.assertFalse(status["executed"])
        self.assertIsNone(status["passed"])
        self.assertIsNone(bin_path)

        with tempfile.TemporaryDirectory() as tmpd:
            repo = Path(tmpd)
            mir_dir = repo / "tools" / "anneal-mir-eval"
            mir_dir.mkdir(parents=True)
            manifest = mir_dir / "Cargo.toml"
            manifest.write_text("[package]\nname='anneal-mir-eval'\n", encoding="utf-8")
            fake_target = mir_dir / "target" / "debug"
            fake_target.mkdir(parents=True)
            (fake_target / "anneal-mir-eval").write_text("", encoding="utf-8")

            def _artifact_stdout(exe_path: Path) -> str:
                return (
                    json.dumps(
                        {
                            "reason": "compiler-artifact",
                            "manifest_path": str(manifest.resolve()),
                            "target": {
                                "kind": ["bin"],
                                "name": "anneal-mir-eval",
                            },
                            "profile": {"test": False},
                            "executable": str(exe_path),
                        }
                    )
                    + "\n"
                )

            def _mock_cargo_for(exe_path: Path):
                def _side_effect(args: list[str], **_kwargs: Any) -> mock.Mock:
                    if "build" in args:
                        return mock.Mock(
                            returncode=0,
                            stdout=_artifact_stdout(exe_path),
                            stderr="",
                        )
                    return mock.Mock(returncode=0, stdout="", stderr="")

                return _side_effect

            with (
                mock.patch.dict(os.environ, {}, clear=False),
                mock.patch(
                    "subprocess.run",
                    side_effect=_mock_cargo_for(fake_target / "anneal-mir-eval"),
                ) as run_mock,
            ):
                os.environ.pop("CARGO_TARGET_DIR", None)
                status2, bin_path2 = cmd.maybe_run_mir_eval_manifest(manifest)
            self.assertTrue(status2["executed"])
            self.assertTrue(status2["passed"])
            self.assertEqual(
                bin_path2.resolve(), (fake_target / "anneal-mir-eval").resolve()
            )
            self.assertEqual(run_mock.call_count, 2)

            # Workspace-member layout: Cargo places the binary under
            # `<repo>/target/debug`, not `<manifest-parent>/target/debug`.
            ws_target = repo / "target" / "debug"
            ws_target.mkdir(parents=True)
            ws_bin = ws_target / "anneal-mir-eval"
            ws_bin.write_text("", encoding="utf-8")
            with (
                mock.patch.dict(os.environ, {}, clear=False),
                mock.patch("subprocess.run", side_effect=_mock_cargo_for(ws_bin)),
            ):
                os.environ.pop("CARGO_TARGET_DIR", None)
                status_ws, bin_ws = cmd.maybe_run_mir_eval_manifest(manifest)
            self.assertTrue(status_ws["passed"], status_ws)
            self.assertEqual(bin_ws, ws_bin)

            # Missing `compiler-artifact` record fails closed even on rc == 0.
            empty_ok = mock.Mock(returncode=0, stdout="", stderr="")
            with mock.patch("subprocess.run", return_value=empty_ok):
                status_no_json, bin_no_json = cmd.maybe_run_mir_eval_manifest(manifest)
            self.assertTrue(status_no_json["executed"])
            self.assertFalse(status_no_json["passed"])
            self.assertIsNone(bin_no_json)

            fail_proc = mock.Mock(returncode=101, stdout="", stderr="assertion failed")
            with mock.patch("subprocess.run", return_value=fail_proc):
                status3, bin_path3 = cmd.maybe_run_mir_eval_manifest(manifest)
            self.assertTrue(status3["executed"])
            self.assertFalse(status3["passed"])
            self.assertIsNone(bin_path3)

            rel_target_bin = mir_dir / "rel-target" / "nested" / "debug"
            rel_target_bin.mkdir(parents=True)
            (rel_target_bin / "anneal-mir-eval").write_text("", encoding="utf-8")
            abs_target_dir = repo / "abs-target"
            (abs_target_dir / "debug").mkdir(parents=True)
            (abs_target_dir / "debug" / "anneal-mir-eval").write_text(
                "", encoding="utf-8"
            )
            outside_cwd = repo / "outside-cwd"
            outside_cwd.mkdir()
            prev_cwd = Path.cwd()
            try:
                os.chdir(outside_cwd)
                rel_exe = (
                    mir_dir.resolve()
                    / "rel-target"
                    / "nested"
                    / "debug"
                    / "anneal-mir-eval"
                )
                with (
                    mock.patch.dict(
                        os.environ,
                        {"CARGO_TARGET_DIR": "rel-target/nested"},
                        clear=False,
                    ),
                    mock.patch(
                        "subprocess.run", side_effect=_mock_cargo_for(rel_exe)
                    ),
                ):
                    status_rel, bin_rel = cmd.maybe_run_mir_eval_manifest(manifest)
                self.assertTrue(status_rel["passed"], status_rel)
                self.assertEqual(bin_rel, rel_exe)

                abs_exe = abs_target_dir / "debug" / "anneal-mir-eval"
                with (
                    mock.patch.dict(
                        os.environ,
                        {"CARGO_TARGET_DIR": str(abs_target_dir)},
                        clear=False,
                    ),
                    mock.patch(
                        "subprocess.run", side_effect=_mock_cargo_for(abs_exe)
                    ),
                ):
                    status_abs, bin_abs = cmd.maybe_run_mir_eval_manifest(manifest)
                self.assertTrue(status_abs["passed"], status_abs)
                self.assertEqual(bin_abs, abs_exe)
            finally:
                os.chdir(prev_cwd)

    def test_main_rejects_symlink_anneal_root_and_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd)
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()
            sym_anneal = root / "anneal_sym"
            os.symlink(anneal_dir, sym_anneal)
            with self.assertRaises(ValueError):
                cmd.main(["--anneal-root", str(sym_anneal), "--allow-unknown-git"])

            out_json = root / "detail.json"
            perf_json = root / "perf.json"
            perf_rec_json = root / "perf-record.json"
            sample = _sample_diff_report()

            with (
                mock.patch.object(
                    cmd,
                    "maybe_run_mir_eval_manifest",
                    return_value=({"executed": False, "passed": None}, None),
                ),
                mock.patch.object(cmd, "run_anneal_diff", return_value=(0, sample)),
            ):
                with self.assertRaises(RuntimeError):
                    cmd.main(["--anneal-root", str(anneal_dir)])

                bad_src_rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--allow-unknown-git",
                        "--expect-capture-source",
                        "explicit",
                    ]
                )
                self.assertEqual(bad_src_rc, 1)

                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--allow-unknown-git",
                        "--branch",
                        "pr-test-branch",
                        "--expect-capture-source",
                        "env_anneal_capture",
                        "--output",
                        str(out_json),
                        "--perf-metrics-out",
                        str(perf_json),
                        "--perf-record-out",
                        str(perf_rec_json),
                    ]
                )
            self.assertEqual(rc, 0)
            written_detail = json.loads(out_json.read_text(encoding="utf-8"))
            written_perf = json.loads(perf_json.read_text(encoding="utf-8"))
            written_rec = json.loads(perf_rec_json.read_text(encoding="utf-8"))
            self.assertEqual(written_detail["schema"], cmd.DETAIL_SCHEMA)
            self.assertEqual(written_detail["branch"], "pr-test-branch")
            self.assertEqual(
                written_perf["differential_oracle.litmus.compared_count"], 3
            )
            perf_tracking.validate_record(written_rec)
            self.assertEqual(written_rec["commit"]["branch"], "pr-test-branch")

            sym_out = root / "sym.json"
            os.symlink(out_json, sym_out)
            with self.assertRaises(ValueError):
                cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--allow-unknown-git",
                        "--output",
                        str(sym_out),
                    ]
                )

    def test_outside_cwd_anchors_relative_cli_and_env_paths_and_rejects_symlinks(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            repo_root = Path(tmpd).resolve()
            anneal_dir = repo_root / "anneal"
            (anneal_dir / "target" / "debug").mkdir(parents=True)
            (anneal_dir / "corpora").mkdir(parents=True)
            (repo_root / "tools" / "eval").mkdir(parents=True)

            diff_bin = anneal_dir / "target" / "debug" / "anneal-diff"
            diff_bin.write_text("", encoding="utf-8")
            capture_bin = anneal_dir / "target" / "debug" / "anneal-rustc-capture"
            capture_bin.write_text("", encoding="utf-8")
            manifest_file = anneal_dir / "corpora" / "manifest.toml"
            manifest_file.write_text("schema_version = 1\n", encoding="utf-8")
            mir_eval_bin = repo_root / "tools" / "eval" / "anneal-mir-eval"
            mir_eval_bin.write_text("", encoding="utf-8")
            mir_eval_manifest = repo_root / "tools" / "eval" / "Cargo.toml"
            mir_eval_manifest.write_text(
                "[package]\nname = 'anneal-mir-eval'\n", encoding="utf-8"
            )
            (repo_root / "tools" / "eval" / "target" / "debug").mkdir(parents=True)
            (
                repo_root / "tools" / "eval" / "target" / "debug" / "anneal-mir-eval"
            ).write_text("", encoding="utf-8")

            sample = _sample_diff_report()
            recorded_calls: list[tuple[list[str], Path, dict[str, str]]] = []

            def fake_subprocess_run(
                args: list[str],
                *,
                cwd: Path | None = None,
                env: dict[str, str] | None = None,
                **kwargs: object,
            ) -> mock.Mock:
                if args and (
                    Path(args[0]).name in ("git", "rustc", "lean")
                    or "--version" in args
                ):
                    return mock.Mock(returncode=1, stdout="", stderr="")
                if len(args) >= 2 and args[1] == "test":
                    return mock.Mock(returncode=0, stdout="", stderr="")
                if len(args) >= 2 and args[1] == "build":
                    built_exe = (
                        repo_root
                        / "tools"
                        / "eval"
                        / "target"
                        / "debug"
                        / "anneal-mir-eval"
                    )
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": str(mir_eval_manifest.resolve()),
                                "target": {
                                    "kind": ["bin"],
                                    "name": "anneal-mir-eval",
                                },
                                "profile": {"test": False},
                                "executable": str(built_exe),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                recorded_calls.append(
                    (list(args), Path(cwd) if cwd else Path.cwd(), dict(env or {}))
                )
                return mock.Mock(
                    returncode=0, stdout=json.dumps(sample), stderr=""
                )

            prev_cwd = Path.cwd()
            try:
                os.chdir(repo_root)
                with (
                    mock.patch.dict(
                        os.environ,
                        {
                            "ANNEAL_CAPTURE": "anneal/target/debug/anneal-rustc-capture",
                            "ANNEAL_MIRI_SYSROOT": "rel-miri-sysroot",
                            "ANNEAL_DIFF_CACHE_DIR": "rel-diff-cache",
                            "CARGO_TARGET_DIR": "rel-cargo-target",
                            "CARGO": "./scripts/cargo-wrap",
                        },
                        clear=False,
                    ),
                    mock.patch(
                        "subprocess.run", side_effect=fake_subprocess_run
                    ),
                ):
                    rc = cmd.main(
                        [
                            "--anneal-root",
                            "anneal",
                            "--anneal-diff-bin",
                            "anneal/target/debug/anneal-diff",
                            "--manifest",
                            "anneal/corpora/manifest.toml",
                            "--capture-bin",
                            "anneal/target/debug/anneal-rustc-capture",
                            "--mir-eval-bin",
                            "tools/eval/anneal-mir-eval",
                            "--cache-root",
                            "rel-cache/diff",
                            "--output",
                            "rel-out/detail.json",
                            "--perf-metrics-out",
                            "rel-out/perf.json",
                            "--perf-record-out",
                            "rel-out/perf-record.json",
                            "--branch",
                            "rel-branch",
                            "--allow-unknown-git",
                        ]
                    )
                self.assertEqual(rc, 0)
                self.assertEqual(len(recorded_calls), 1)
                diff_args, diff_cwd, diff_env = recorded_calls[0]
                self.assertEqual(diff_cwd, anneal_dir)
                self.assertEqual(diff_args[0], str(diff_bin))
                self.assertEqual(
                    diff_args[diff_args.index("--manifest") + 1],
                    str(manifest_file),
                )
                self.assertEqual(
                    diff_args[diff_args.index("--capture-bin") + 1],
                    str(capture_bin),
                )
                self.assertEqual(
                    diff_args[diff_args.index("--mir-eval-bin") + 1],
                    str(mir_eval_bin),
                )
                self.assertEqual(
                    diff_args[diff_args.index("--cache-root") + 1],
                    str(repo_root / "rel-cache" / "diff"),
                )
                self.assertEqual(
                    diff_env["ANNEAL_CAPTURE"], str(capture_bin)
                )
                self.assertEqual(
                    diff_env["ANNEAL_MIRI_SYSROOT"],
                    str(repo_root / "rel-miri-sysroot"),
                )
                self.assertEqual(
                    diff_env["ANNEAL_DIFF_CACHE_DIR"],
                    str(repo_root / "rel-diff-cache"),
                )
                self.assertEqual(
                    diff_env["CARGO_TARGET_DIR"],
                    str(repo_root / "rel-cargo-target"),
                )
                self.assertEqual(
                    diff_env["CARGO"], str(repo_root / "scripts" / "cargo-wrap")
                )
                self.assertTrue((repo_root / "rel-out" / "detail.json").is_file())
                self.assertTrue((repo_root / "rel-out" / "perf.json").is_file())
                self.assertTrue(
                    (repo_root / "rel-out" / "perf-record.json").is_file()
                )

                # Direct `run_anneal_diff` call with relative `Path` objects
                # also anchors against the caller's working directory.
                recorded_calls.clear()
                with (
                    mock.patch.dict(os.environ, {"CARGO": "cargo"}, clear=False),
                    mock.patch(
                        "subprocess.run", side_effect=fake_subprocess_run
                    ),
                ):
                    rc_direct, _ = cmd.run_anneal_diff(
                        anneal_root=Path("anneal"),
                        manifest=Path("anneal/corpora/manifest.toml"),
                        capture_bin=Path("anneal/target/debug/anneal-rustc-capture"),
                        mir_eval_bin=Path("tools/eval/anneal-mir-eval"),
                        cache_root=Path("rel-cache/direct"),
                        self_check_oracle=False,
                        anneal_diff_bin=None,
                    )
                self.assertEqual(rc_direct, 0)
                direct_args, direct_cwd, direct_env = recorded_calls[0]
                self.assertEqual(direct_cwd, anneal_dir)
                self.assertEqual(direct_args[0], "cargo")
                self.assertEqual(direct_env["CARGO"], "cargo")
                self.assertEqual(
                    direct_args[direct_args.index("--manifest") + 1],
                    str(manifest_file),
                )
                self.assertEqual(
                    direct_args[direct_args.index("--cache-root") + 1],
                    str(repo_root / "rel-cache" / "direct"),
                )

                # Relative `--mir-eval-manifest` resolves against `repo_root`,
                # and missing relative manifests return `rc == 1` cleanly.
                recorded_calls.clear()
                with (
                    mock.patch.dict(os.environ, {}, clear=False),
                    mock.patch(
                        "subprocess.run", side_effect=fake_subprocess_run
                    ),
                ):
                    os.environ.pop("CARGO_TARGET_DIR", None)
                    rc_eval = cmd.main(
                        [
                            "--anneal-root",
                            "anneal",
                            "--anneal-diff-bin",
                            "anneal/target/debug/anneal-diff",
                            "--mir-eval-manifest",
                            "tools/eval/Cargo.toml",
                            "--branch",
                            "rel-branch",
                            "--allow-unknown-git",
                        ]
                    )
                    rc_missing_eval = cmd.main(
                        [
                            "--anneal-root",
                            "anneal",
                            "--anneal-diff-bin",
                            "anneal/target/debug/anneal-diff",
                            "--mir-eval-manifest",
                            "tools/eval/missing-Cargo.toml",
                            "--allow-unknown-git",
                        ]
                    )
                self.assertEqual(rc_eval, 0)
                self.assertEqual(rc_missing_eval, 1)
                eval_args, _, _ = recorded_calls[0]
                self.assertEqual(
                    eval_args[eval_args.index("--mir-eval-bin") + 1],
                    str(
                        repo_root
                        / "tools"
                        / "eval"
                        / "target"
                        / "debug"
                        / "anneal-mir-eval"
                    ),
                )

                # Reject symlinks on relative CLI paths (including lexical
                # `nonexistent/../sym` paths) before running child commands.
                sym_file = repo_root / "sym-target"
                os.symlink(diff_bin, sym_file)
                for flag in (
                    "--anneal-diff-bin",
                    "--manifest",
                    "--capture-bin",
                    "--mir-eval-bin",
                    "--mir-eval-manifest",
                    "--cache-root",
                    "--output",
                    "--perf-metrics-out",
                    "--perf-record-out",
                ):
                    for rel_sym in ("sym-target", "missing-parent/../sym-target"):
                        with self.subTest(flag=flag, rel_sym=rel_sym):
                            with self.assertRaises(ValueError):
                                cmd.main(
                                    [
                                        "--anneal-root",
                                        "anneal",
                                        flag,
                                        rel_sym,
                                        "--allow-unknown-git",
                                    ]
                                )
            finally:
                os.chdir(prev_cwd)

    def test_child_subprocesses_strip_actions_and_github_credentials(
        self,
    ) -> None:
        secret_env = {
            "ACTIONS_CACHE_URL": "https://results-receiver.actions.example/cache/",
            "ACTIONS_ID_TOKEN_REQUEST_TOKEN": "oidc-secret-token",
            "ACTIONS_ID_TOKEN_REQUEST_URL": "https://vstoken.actions.example/",
            "ACTIONS_RESULTS_URL": "https://results-receiver.actions.example/",
            "ACTIONS_RUNTIME_TOKEN": "runtime-secret-token",
            "ACTIONS_RUNTIME_URL": "https://pipelines.actions.example/",
            "GH_TOKEN": "ghs_secret_cli_token",
            "GITHUB_TOKEN": "ghs_secret_actions_token",
            "ANNEAL_BENIGN_TEST_VAR": "kept-value",
        }
        self.assertEqual(
            frozenset(cmd._STRIPPED_CHILD_ENV_VARS),
            frozenset(secret_env.keys()) - {"ANNEAL_BENIGN_TEST_VAR"},
        )

        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            (anneal_dir / "target" / "debug").mkdir(parents=True)
            diff_bin = anneal_dir / "target" / "debug" / "anneal-diff"
            diff_bin.write_text("", encoding="utf-8")

            eval_dir = root / "tools" / "eval"
            (eval_dir / "target" / "debug").mkdir(parents=True)
            eval_manifest = eval_dir / "Cargo.toml"
            eval_manifest.write_text(
                "[package]\nname = 'anneal-mir-eval'\n", encoding="utf-8"
            )
            (eval_dir / "target" / "debug" / "anneal-mir-eval").write_text(
                "", encoding="utf-8"
            )

            sample = _sample_diff_report()
            seen_envs: list[tuple[list[str], dict[str, str] | None]] = []

            def spy_subprocess_run(
                args: list[str],
                *,
                env: dict[str, str] | None = None,
                **kwargs: object,
            ) -> mock.Mock:
                seen_envs.append((list(args), None if env is None else dict(env)))
                if args and args[0] == "git":
                    if "rev-parse" in args and "--abbrev-ref" in args:
                        return mock.Mock(returncode=0, stdout="main\n", stderr="")
                    if "rev-parse" in args:
                        return mock.Mock(
                            returncode=0, stdout=("a" * 40) + "\n", stderr=""
                        )
                    return mock.Mock(
                        returncode=0, stdout="1780000000\n", stderr=""
                    )
                if args and "--version" in args:
                    return mock.Mock(
                        returncode=0, stdout="tool 1.0.0\n", stderr=""
                    )
                if len(args) >= 2 and args[1] == "test":
                    return mock.Mock(returncode=0, stdout="", stderr="")
                if len(args) >= 2 and args[1] == "build":
                    built_exe = eval_dir / "target" / "debug" / "anneal-mir-eval"
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": str(eval_manifest.resolve()),
                                "target": {
                                    "kind": ["bin"],
                                    "name": "anneal-mir-eval",
                                },
                                "profile": {"test": False},
                                "executable": str(built_exe),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                return mock.Mock(
                    returncode=0, stdout=json.dumps(sample), stderr=""
                )

            with (
                mock.patch.dict(os.environ, secret_env, clear=False),
                mock.patch("subprocess.run", side_effect=spy_subprocess_run),
            ):
                os.environ.pop("CARGO_TARGET_DIR", None)
                rc = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--anneal-diff-bin",
                        str(diff_bin),
                        "--mir-eval-manifest",
                        str(eval_manifest),
                    ]
                )
            self.assertEqual(rc, 0)
            # Covers git (3), cargo test/build (2), anneal-diff run (1),
            # and rustc/lean version probes (2).
            self.assertGreaterEqual(len(seen_envs), 8)
            for sub_args, sub_env in seen_envs:
                self.assertIsNotNone(
                    sub_env,
                    f"subprocess {sub_args!r} inherited raw os.environ",
                )
                assert sub_env is not None
                self.assertEqual(
                    sub_env.get("ANNEAL_BENIGN_TEST_VAR"), "kept-value"
                )
                for secret_key in cmd._STRIPPED_CHILD_ENV_VARS:
                    self.assertFalse(
                        secret_key in sub_env,
                        f"subprocess {sub_args!r} leaked {secret_key}",
                    )

    def test_artifact_manifest_and_missing_mir_eval_and_hex_provenance(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            manifest = Path(tmpd) / "Cargo.toml"
            manifest.write_text("[package]\nname='x'\n", encoding="utf-8")
            exe = Path(tmpd) / "anneal-mir-eval"
            exe.write_text("", encoding="utf-8")
            no_manifest_line = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                    "profile": {"test": False},
                    "executable": str(exe),
                }
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    no_manifest_line, "anneal-mir-eval", manifest.resolve()
                )
            )

        detail_missing_eval = cmd.build_semantic_detail_report(
            diff_report=_sample_diff_report(),
            mir_eval_status={"executed": False, "passed": False},
            repo="google/zerocopy",
            branch="main",
            commit_sha="a" * 40,
            commit_unix_ts=1_780_000_000,
            environment_profile={"os": "linux"},
        )
        self.assertFalse(cmd.report_passes(detail_missing_eval))

    def test_nonvirtual_workspace_default_members_selection(self) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            root_manifest = root / "Cargo.toml"
            member_dir = root / "tools" / "anneal-mir-eval"
            member_dir.mkdir(parents=True)
            member_manifest = member_dir / "Cargo.toml"
            member_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            other_dir = root / "tools" / "other-eval"
            other_dir.mkdir(parents=True)
            other_manifest = other_dir / "Cargo.toml"
            other_manifest.write_text(
                '[package]\nname = "other-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            excl_dir = root / "tools" / "excluded-eval"
            excl_dir.mkdir(parents=True)
            excl_manifest = excl_dir / "Cargo.toml"
            excl_manifest.write_text(
                '[package]\nname = "excl-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            target_bin = root / "target" / "debug" / "anneal-mir-eval"
            target_bin.parent.mkdir(parents=True)
            target_bin.write_text("", encoding="utf-8")

            def _artifact(manifest: Path) -> str:
                return json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": str(manifest),
                        "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                        "profile": {"test": False},
                        "executable": str(target_bin),
                    }
                )

            # Package + workspace with explicit `default-members` permits the
            # selected default member while excluding unselected members,
            # excluded dirs, and `"."` when omitted from `default-members`.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\n'
                'exclude = ["tools/excluded-eval"]\n'
                'default-members = ["tools/anneal-mir-eval"]\n',
                encoding="utf-8",
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(other_manifest), "anneal-mir-eval", root_manifest
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(excl_manifest), "anneal-mir-eval", root_manifest
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                )
            )

            # Including `"."` alongside a member in `default-members` permits
            # both root and selected member manifests.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\n'
                'default-members = [".", "tools/anneal-mir-eval"]\n',
                encoding="utf-8",
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )

            # Package + workspace without `default-members` targets only root.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\n',
                encoding="utf-8",
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                )
            )

            # Explicit empty `default-members` rejects all manifests.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\ndefault-members = []\n',
                encoding="utf-8",
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                )
            )

    def test_virtual_workspace_manifest_and_mutually_exclusive_mir_eval_flags(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()

            vws_manifest = root / "Cargo.toml"
            vws_manifest.write_text(
                '[workspace]\nresolver = "2"\nmembers = ["tools/*"]\n'
                'exclude = ["tools/excluded-eval"]\n',
                encoding="utf-8",
            )
            member_dir = root / "tools" / "anneal-mir-eval"
            member_dir.mkdir(parents=True)
            member_manifest = member_dir / "Cargo.toml"
            member_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            excl_dir = root / "tools" / "excluded-eval"
            excl_dir.mkdir(parents=True)
            excl_manifest = excl_dir / "Cargo.toml"
            excl_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            target_bin = root / "target" / "debug" / "anneal-mir-eval"
            target_bin.parent.mkdir(parents=True)
            target_bin.write_text("", encoding="utf-8")

            member_artifact = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "manifest_path": str(member_manifest),
                    "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                    "profile": {"test": False},
                    "executable": str(target_bin),
                }
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    member_artifact, "anneal-mir-eval", vws_manifest
                ),
                target_bin,
            )

            # Excluded workspace dirs and conflicting duplicate artifacts fail
            # closed.
            excluded_artifact = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "manifest_path": str(excl_manifest),
                    "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                    "profile": {"test": False},
                    "executable": str(target_bin),
                }
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    excluded_artifact, "anneal-mir-eval", vws_manifest
                )
            )
            other_member_dir = root / "tools" / "other-eval"
            other_member_dir.mkdir(parents=True)
            other_manifest = other_member_dir / "Cargo.toml"
            other_manifest.write_text(
                '[package]\nname = "other"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            dup_stdout = (
                member_artifact
                + "\n"
                + json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": str(other_manifest),
                        "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                        "profile": {"test": False},
                        "executable": str(root / "target" / "debug" / "other"),
                    }
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    dup_stdout, "anneal-mir-eval", vws_manifest
                )
            )

            # End-to-end `maybe_run_mir_eval_manifest` accepts a virtual
            # workspace manifest whose `compiler-artifact` identifies the
            # member `Cargo.toml`.
            def _vws_cargo_side_effect(
                args: list[str], **_kwargs: Any
            ) -> mock.Mock:
                if "build" in args:
                    return mock.Mock(
                        returncode=0,
                        stdout=member_artifact + "\n",
                        stderr="",
                    )
                return mock.Mock(returncode=0, stdout="", stderr="")

            with mock.patch(
                "subprocess.run", side_effect=_vws_cargo_side_effect
            ):
                status_vws, bin_vws = cmd.maybe_run_mir_eval_manifest(
                    vws_manifest
                )
            self.assertTrue(status_vws["passed"], status_vws)
            self.assertEqual(bin_vws, target_bin)

            # Passing both `--mir-eval-manifest` and `--mir-eval-bin` is
            # rejected before running any child process.
            with (
                mock.patch.object(
                    cmd, "maybe_run_mir_eval_manifest"
                ) as run_manifest_mock,
                mock.patch.object(cmd, "run_anneal_diff") as run_diff_mock,
            ):
                with self.assertRaises(SystemExit) as ctx:
                    cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--mir-eval-manifest",
                            str(member_manifest),
                            "--mir-eval-bin",
                            str(target_bin),
                            "--allow-unknown-git",
                        ]
                    )
                self.assertEqual(ctx.exception.code, 2)
                run_manifest_mock.assert_not_called()
                run_diff_mock.assert_not_called()

            # `maybe_run_mir_eval_manifest` anchors relative Cargo tool and
            # home/target environment overrides against `caller_cwd` before
            # invoking Cargo with `cwd=manifest_canon.parent`.
            caller_root = root / "caller-launch-dir"
            caller_root.mkdir()
            recorded_manifest_envs: list[tuple[list[str], Path, dict[str, str]]] = []

            def _anchored_cargo_side_effect(
                args: list[str],
                *,
                cwd: Path | None = None,
                env: dict[str, str] | None = None,
                **_kwargs: object,
            ) -> mock.Mock:
                recorded_manifest_envs.append(
                    (list(args), Path(cwd) if cwd else Path.cwd(), dict(env or {}))
                )
                if len(args) >= 2 and args[1] == "build":
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": str(member_manifest.resolve()),
                                "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                                "profile": {"test": False},
                                "executable": str(target_bin),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                return mock.Mock(returncode=0, stdout="", stderr="")

            prev_cwd = Path.cwd()
            try:
                os.chdir(caller_root)
                with (
                    mock.patch.dict(
                        os.environ,
                        {
                            "CARGO": "./scripts/cargo-wrap",
                            "RUSTC": "./scripts/rustc-wrap",
                            "RUSTDOC": "./scripts/rustdoc-wrap",
                            "RUSTC_WRAPPER": "./scripts/clippy-wrap",
                            "RUSTC_WORKSPACE_WRAPPER": "sccache",
                            "CARGO_HOME": "./rel-cargo-home",
                            "CARGO_TARGET_DIR": "./rel-cargo-target",
                            "PATH": f"./toolchain/bin{os.pathsep}/usr/bin",
                            "LD_LIBRARY_PATH": f"./lib{os.pathsep}/usr/lib",
                        },
                        clear=False,
                    ),
                    mock.patch(
                        "subprocess.run", side_effect=_anchored_cargo_side_effect
                    ),
                ):
                    rel_manifest = Path(os.path.relpath(member_manifest, caller_root))
                    st_anchor, bin_anchor = cmd.maybe_run_mir_eval_manifest(rel_manifest)
            finally:
                os.chdir(prev_cwd)

            self.assertTrue(st_anchor["passed"], st_anchor)
            self.assertEqual(bin_anchor, target_bin)
            self.assertEqual(len(recorded_manifest_envs), 2)
            for call_args, call_cwd, call_env in recorded_manifest_envs:
                self.assertEqual(call_cwd, member_manifest.resolve().parent)
                self.assertEqual(
                    call_args[0], str(caller_root / "scripts" / "cargo-wrap")
                )
                self.assertEqual(
                    call_env["RUSTC"], str(caller_root / "scripts" / "rustc-wrap")
                )
                self.assertEqual(
                    call_env["RUSTDOC"], str(caller_root / "scripts" / "rustdoc-wrap")
                )
                self.assertEqual(
                    call_env["RUSTC_WRAPPER"],
                    str(caller_root / "scripts" / "clippy-wrap"),
                )
                self.assertEqual(call_env["RUSTC_WORKSPACE_WRAPPER"], "sccache")
                self.assertEqual(
                    call_env["CARGO_HOME"], str(caller_root / "rel-cargo-home")
                )
                self.assertEqual(
                    call_env["CARGO_TARGET_DIR"],
                    str(caller_root / "rel-cargo-target"),
                )
                self.assertEqual(
                    call_env["PATH"],
                    f"{caller_root / 'toolchain' / 'bin'}{os.pathsep}/usr/bin",
                )
                self.assertEqual(
                    call_env["LD_LIBRARY_PATH"],
                    f"{caller_root / 'lib'}{os.pathsep}/usr/lib",
                )

            # Explicit `--commit-sha` / `--commit-unix-ts` / `--branch`
            # populate telemetry without `--allow-unknown-git` even outside git.
            out_rev = root / "rev-detail.json"
            perf_rev = root / "rev-perf-record.json"
            explicit_sha = "A" * 40
            with mock.patch.object(
                cmd, "run_anneal_diff", return_value=(0, _sample_diff_report())
            ):
                rc_rev = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--branch",
                        "ci-main",
                        "--commit-sha",
                        explicit_sha,
                        "--commit-unix-ts",
                        "1785000123",
                        "--output",
                        str(out_rev),
                        "--perf-record-out",
                        str(perf_rev),
                    ]
                )
            self.assertEqual(rc_rev, 0)
            detail_rev = json.loads(out_rev.read_text(encoding="utf-8"))
            self.assertEqual(detail_rev["branch"], "ci-main")
            self.assertEqual(detail_rev["commit_sha"], "a" * 40)
            self.assertEqual(detail_rev["commit_unix_ts"], 1785000123)
            rec_rev = json.loads(perf_rev.read_text(encoding="utf-8"))
            self.assertEqual(rec_rev["commit"]["sha"], "a" * 40)
            self.assertEqual(rec_rev["commit"]["unix_ts"], 1785000123)
            self.assertEqual(rec_rev["commit"]["branch"], "ci-main")

            # Invalid or unpaired `--commit-sha` / `--commit-unix-ts` fails
            # closed.
            for bad_flags in (
                ["--commit-sha", "not-a-sha"],
                ["--commit-unix-ts", "-1"],
                ["--commit-sha", "a" * 40],
                ["--commit-unix-ts", "1785000123"],
            ):
                with self.assertRaises(SystemExit) as bad_ctx:
                    cmd.main(
                        ["--anneal-root", str(anneal_dir), *bad_flags]
                    )
                self.assertEqual(bad_ctx.exception.code, 2)
            with self.assertRaisesRegex(ValueError, "provided together"):
                cmd._git_metadata(anneal_dir, commit_sha_override="a" * 40)
            with self.assertRaisesRegex(ValueError, "provided together"):
                cmd._git_metadata(anneal_dir, commit_unix_ts_override=1785000123)

            # `_collect_environment` probes the suite-selected `ToolchainEnv`
            # rustc and Lean executables across explicit overrides and
            # install-root/cache fallbacks.
            (anneal_dir / "trusted" / "lean").mkdir(parents=True, exist_ok=True)
            (anneal_dir / "trusted" / "lean" / "lean-toolchain").write_text(
                "leanprover/lean4:v4.34.1\n", encoding="utf-8"
            )
            sys_root = root / "sys-a"
            (sys_root / "bin").mkdir(parents=True)
            (sys_root / "lib").mkdir(parents=True)
            (sys_root / "bin" / "rustc").write_text("", encoding="utf-8")
            mvp_lean = root / "mvp-lean"
            mvp_lean.write_text("", encoding="utf-8")
            inst_root = root / "inst-root"
            (inst_root / "rust" / "bin").mkdir(parents=True)
            (inst_root / "rust" / "lib").mkdir(parents=True)
            (inst_root / "rust" / "bin" / "rustc").write_text("", encoding="utf-8")
            (inst_root / "lean" / "bin").mkdir(parents=True)
            (inst_root / "lean" / "bin" / "lean").write_text("", encoding="utf-8")
            xdg_cache = root / "xdg-cache"
            xdg_lean = (
                xdg_cache / "anneal" / "toolchain" / "v1" / "lean" / "bin" / "lean"
            )
            xdg_lean.parent.mkdir(parents=True)
            xdg_lean.write_text("", encoding="utf-8")

            probed: list[tuple[list[str], str]] = []

            def _probe_side_effect(
                args: list[str],
                *,
                env: dict[str, str] | None = None,
                **_kwargs: object,
            ) -> mock.Mock:
                probed.append((list(args), (env or {}).get("LD_LIBRARY_PATH", "")))
                return mock.Mock(returncode=0, stdout=f"{args[0]} 1.0.0\n", stderr="")

            with mock.patch("subprocess.run", side_effect=_probe_side_effect):
                with mock.patch.dict(
                    os.environ,
                    {
                        "RUSTC": "/ambient/rustc",
                        "ANNEAL_SYSROOT": str(sys_root),
                        "ANNEAL_MVP_LEAN": str(mvp_lean),
                    },
                    clear=True,
                ):
                    env1 = cmd._collect_environment(anneal_dir, caller_cwd=root)
                self.assertEqual(env1["rustc_version"], f"{sys_root / 'bin' / 'rustc'} 1.0.0")
                self.assertEqual(env1["lean_version"], f"{mvp_lean} 1.0.0")
                self.assertIn(str(sys_root / "lib"), probed[0][1])

                probed.clear()
                with mock.patch.dict(
                    os.environ,
                    {
                        "ANNEAL_TEST_INSTALL_ROOT": str(inst_root),
                    },
                    clear=True,
                ):
                    env2 = cmd._collect_environment(anneal_dir, caller_cwd=root)
                self.assertEqual(
                    env2["rustc_version"],
                    f"{inst_root / 'rust' / 'bin' / 'rustc'} 1.0.0",
                )
                self.assertEqual(
                    env2["lean_version"],
                    f"{inst_root / 'lean' / 'bin' / 'lean'} 1.0.0",
                )

                probed.clear()
                with mock.patch.dict(
                    os.environ,
                    {
                        "XDG_CACHE_HOME": str(xdg_cache),
                    },
                    clear=True,
                ):
                    env3 = cmd._collect_environment(anneal_dir, caller_cwd=root)
                self.assertEqual(env3["lean_version"], f"{xdg_lean} 1.0.0")

        docs_text = (
            Path(__file__).resolve().parent.parent / "docs" / "perf-tracking.md"
        ).read_text(encoding="utf-8")
        self.assertIn(
            'One of `"ms"`, `"KiB"`, `"B"`, `"count"`, `"%"`.', docs_text
        )


if __name__ == "__main__":
    unittest.main()
