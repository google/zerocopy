# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Report validation, `mir-eval` selection, and `main` symlink tests for
`check_mir_differential.py`."""

from __future__ import annotations

import json
import os
from pathlib import Path
import tempfile
from typing import Any
from unittest import mock

import check_mir_differential as cmd
import perf_tracking
from check_mir_differential_tests.support import _sample_diff_report


class ReportAndEvalCases:
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
