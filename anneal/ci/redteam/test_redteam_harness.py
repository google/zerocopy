# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit, containment, calibration, dedup, and live smoke tests."""

from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest
import unittest.mock

_REDTEAM_DIR = Path(__file__).resolve().parent
_CI_DIR = _REDTEAM_DIR.parent
_ANNEAL_ROOT = _CI_DIR.parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import anneal_ci_lib
from redteam import dedup, harness, lean_ast, scenarios


def _clean_receipt(
    *,
    scope_kind: str = "selected_unit",
    axioms: list[str] | None = None,
    taint_reasons: list[str] | None = None,
    deferred: list[str] | None = None,
    sandbox: str = "linux_bwrap",
    replay: bool = True,
    sorry_decls: list[str] | None = None,
) -> dict:
    status = "crate_verified" if scope_kind == "crate" else "selected_unit_verified"
    receipt = {
        "schema_version": 3,
        "status": status,
        "taint_reasons": taint_reasons if taint_reasons is not None else [],
        "elaboration_sandbox": sandbox,
        "deferred": deferred if deferred is not None else [],
        "audit": {
            "replay": replay,
            "exactType": True,
            "checkedAlternateProofs": 0,
            "replayedDeclarations": 42,
            "sorryDeclarations": sorry_decls if sorry_decls is not None else [],
            "axioms": axioms if axioms is not None else ["propext"],
        },
    }
    return receipt


def _mock_verify_pass(**receipt_kwargs):
    payload = _clean_receipt(**receipt_kwargs)

    def _runner(cmd, *, cwd, env, timeout):
        return subprocess.CompletedProcess(
            cmd, 0, stdout=json.dumps(payload), stderr=""
        )

    return _runner


def _mock_verify_fail(
    status: str = "proof_failed",
    phase: str = "proof",
    detail: str = "tactic rfl failed",
    rc: int = 1,
):
    payload = {
        "schema_version": 3,
        "status": status,
        "phase": phase,
        "detail": detail,
        "taint_reasons": [],
        "elaboration_sandbox": "linux_bwrap",
    }

    def _runner(cmd, *, cwd, env, timeout):
        return subprocess.CompletedProcess(
            cmd, rc, stdout=json.dumps(payload), stderr=""
        )

    return _runner


def _mock_inspect_pass(*, tainted: bool = False, violations: list[str] | None = None):
    payload = {
        "receipt_sha256": "0" * 64,
        "status": "selected_unit_verified",
        "tainted": tainted,
        "taint_reasons": [],
        "policy_violations": violations if violations is not None else [],
        "invariant_violations": [],
        "unrecognized_fields": [],
        "artifact_verification": {
            "directory": "artifacts",
            "exact_match": True,
            "checked_files": 5,
            "failures": [],
        },
    }

    def _runner(cmd, *, env, timeout):
        return subprocess.CompletedProcess(
            cmd, 0, stdout=json.dumps(payload), stderr=""
        )

    return _runner


def _mock_proc(rc: int = 0, stdout: str = "", stderr: str = ""):
    def _runner(cmd, *, cwd, env, timeout):
        return subprocess.CompletedProcess(cmd, rc, stdout=stdout, stderr=stderr)

    return _runner


def _write_tar(tar_path: Path, entries: list[tuple[str, bytes, dict]]) -> None:
    with tarfile.open(tar_path, "w:gz") as tf:
        for name, data, meta in entries:
            info = tarfile.TarInfo(name=name)
            info.type = meta.get("type", tarfile.REGTYPE)
            if "linkname" in meta:
                info.linkname = meta["linkname"]
            if info.type == tarfile.REGTYPE:
                info.size = meta.get("size", len(data))
            tf.addfile(info, io.BytesIO(data) if info.type == tarfile.REGTYPE else None)


class RedteamScenarioAndContainmentTests(unittest.TestCase):
    def test_list_scenarios_manifest_and_cli(self):
        manifest = scenarios.list_scenarios_manifest()
        self.assertEqual(manifest["schema_version"], "anneal-redteam-scenarios/v1")
        ids = {s["scenario_id"] for s in manifest["scenarios"]}
        self.assertEqual(
            ids,
            {
                "s1a_ub_proof_hack",
                "s1b_spec_violation_proof_hack",
                "s2_code_and_proof_hack",
                "s3_spec_preflight_hack",
                "s4_theory_audit_hack",
            },
        )
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(_REDTEAM_DIR / "harness.py"), "list-scenarios", "--json"],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(res.returncode, 0, res.stderr)
        cli_manifest = json.loads(res.stdout)
        self.assertEqual(cli_manifest, manifest)

    def test_rejects_symlinks_hardlinks_traversal_and_out_of_slot_paths(self):
        with tempfile.TemporaryDirectory(prefix="rt-contain-") as tmp:
            tmp_path = Path(tmp)

            # Out-of-slot Spec.lean in PROOF_HACK.
            out_slot = tmp_path / "out_slot"
            (out_slot / "Proof").mkdir(parents=True)
            (out_slot / "Proof/Proof.lean").write_text("-- ok\n")
            (out_slot / "Spec.lean").write_text("-- forbidden tamper\n")
            rcpt = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=out_slot,
            )
            self.assertEqual(rcpt["verdict"], harness.VERDICT_INVALID_SUBMISSION)
            self.assertIsNone(rcpt["dedup"])

            # Symlink inside Proof/.
            sym_dir = tmp_path / "sym_dir"
            (sym_dir / "Proof").mkdir(parents=True)
            (tmp_path / "outside.lean").write_text("-- outside\n")
            (sym_dir / "Proof/Proof.lean").symlink_to(tmp_path / "outside.lean")
            rcpt = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=sym_dir,
            )
            self.assertEqual(rcpt["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            # Hardlink inside Proof/ (`st_nlink > 1`).
            hl_dir = tmp_path / "hl_dir"
            (hl_dir / "Proof").mkdir(parents=True)
            (hl_dir / "Proof/Proof.lean").write_text("-- hardlink\n")
            os.link(hl_dir / "Proof/Proof.lean", tmp_path / "link_copy")
            rcpt = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=hl_dir,
            )
            self.assertEqual(rcpt["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            # Reserved namespace Proof/Expected.lean.
            res_dir = tmp_path / "res_dir"
            (res_dir / "Proof").mkdir(parents=True)
            (res_dir / "Proof/Proof.lean").write_text("-- proof\n")
            (res_dir / "Proof/Expected.lean").write_text("-- shadow\n")
            rcpt = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=res_dir,
            )
            self.assertEqual(rcpt["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            # Scenario 2: reject src/build.rs and invalid witness.json.
            s2_build = tmp_path / "s2_build"
            (s2_build / "src").mkdir(parents=True)
            (s2_build / "Proof").mkdir(parents=True)
            (s2_build / "src/lib.rs").write_text("pub fn target(x: u32) -> u32 { x }\n")
            (s2_build / "src/build.rs").write_text("fn main() {}\n")
            (s2_build / "Proof/Proof.lean").write_text("-- p\n")
            rcpt = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_build,
            )
            self.assertEqual(rcpt["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            s2_bad_w = tmp_path / "s2_bad_w"
            (s2_bad_w / "src").mkdir(parents=True)
            (s2_bad_w / "Proof").mkdir(parents=True)
            (s2_bad_w / "src/lib.rs").write_text("pub fn target(x: u32) -> u32 { x }\n")
            (s2_bad_w / "Proof/Proof.lean").write_text("-- p\n")
            (s2_bad_w / "witness.json").write_text('{"args": [true]}\n')
            rcpt = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_bad_w,
            )
            self.assertEqual(rcpt["verdict"], harness.VERDICT_INVALID_SUBMISSION)

    def test_tar_rejects_traversal_symlinks_hardlinks_and_duplicates(self):
        with tempfile.TemporaryDirectory(prefix="rt-tar-") as tmp:
            tmp_path = Path(tmp)
            cases = (
                (
                    "traversal.tar.gz",
                    [("../Spec.lean", b"-- evil\n", {})],
                ),
                (
                    "abs.tar.gz",
                    [("/Proof/Proof.lean", b"-- evil\n", {})],
                ),
                (
                    "backslash.tar.gz",
                    [(r"Proof\Proof.lean", b"-- evil\n", {})],
                ),
                (
                    "symlink.tar.gz",
                    [(
                        "Proof/Proof.lean",
                        b"",
                        {"type": tarfile.SYMTYPE, "linkname": "/etc/passwd"},
                    )],
                ),
                (
                    "hardlink.tar.gz",
                    [
                        ("Proof/Proof.lean", b"-- a\n", {}),
                        (
                            "Proof/Sub.lean",
                            b"",
                            {"type": tarfile.LNKTYPE, "linkname": "Proof/Proof.lean"},
                        ),
                    ],
                ),
                (
                    "dup.tar.gz",
                    [
                        ("Proof/Proof.lean", b"-- a\n", {}),
                        ("./Proof/Proof.lean", b"-- b\n", {}),
                    ],
                ),
            )
            for fname, entries in cases:
                with self.subTest(case=fname):
                    tpath = tmp_path / fname
                    _write_tar(tpath, entries)
                    rcpt = harness.evaluate_submission(
                        scenario_id="s1a_ub_proof_hack",
                        submission_tar=tpath,
                    )
                    self.assertEqual(rcpt["verdict"], harness.VERDICT_INVALID_SUBMISSION)
                    self.assertIsNone(rcpt["dedup"])


class RedteamCalibrationAndDedupTests(unittest.TestCase):
    def _make_proof_submission(self, root: Path, code: str) -> Path:
        (root / "Proof").mkdir(parents=True, exist_ok=True)
        (root / "Proof/Proof.lean").write_text(code, encoding="utf-8")
        return root

    def _make_s2_submission(
        self, root: Path, rust_code: str, lean_code: str, witness: list[int] | None = None
    ) -> Path:
        (root / "src").mkdir(parents=True, exist_ok=True)
        (root / "Proof").mkdir(parents=True, exist_ok=True)
        (root / "src/lib.rs").write_text(rust_code, encoding="utf-8")
        (root / "Proof/Proof.lean").write_text(lean_code, encoding="utf-8")
        if witness is not None:
            (root / "witness.json").write_text(
                json.dumps({"args": witness}), encoding="utf-8"
            )
        return root

    def test_failed_and_tainted_runs_hold_defender(self):
        with tempfile.TemporaryDirectory(prefix="rt-hold-") as tmp:
            sub = self._make_proof_submission(Path(tmp) / "sub", "theorem bad := sorry\n")
            rcpt = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=sub,
                verify_runner=_mock_verify_fail(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rcpt["verdict"], harness.VERDICT_DEFENDER_HELD)
            self.assertIsNone(rcpt["dedup"])

            # Baseline deferrals (`complete review-surface reporting`,
            # `source-to-deployed-binary correspondence`) emitted by live
            # `cargo anneal verify` must NOT cause false failures or anomalies,
            # whereas weakening deferrals still fail closed.
            base_def_rcpt = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=sub,
                verify_runner=_mock_verify_pass(
                    deferred=[
                        "complete review-surface reporting",
                        "source-to-deployed-binary correspondence",
                    ]
                ),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(base_def_rcpt["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertEqual(
                dedup.extract_receipt_anomalies(
                    {
                        "elaboration_sandbox": "linux_bwrap",
                        "deferred": [
                            "complete review-surface reporting",
                            "source-to-deployed-binary correspondence",
                        ],
                    }
                ),
                [],
            )

            # Tainted or unsandboxed receipt must NEVER count as ATTACKER_WON.
            for label, bad_kw in (
                ("tainted", {"taint_reasons": ["unsandboxed_elaboration"]}),
                ("unsandboxed", {"sandbox": "none"}),
                ("deferred", {"deferred": ["hostile Lean elaborator effects"]}),
                ("sorry_ax", {"axioms": ["propext", "sorryAx"]}),
            ):
                with self.subTest(case=label):
                    rcpt_t = harness.evaluate_submission(
                        scenario_id="s1a_ub_proof_hack",
                        submission_dir=sub,
                        verify_runner=_mock_verify_pass(**bad_kw),
                        inspect_runner=_mock_inspect_pass(),
                    )
                    self.assertEqual(rcpt_t["verdict"], harness.VERDICT_DEFENDER_HELD)
                    self.assertIsNone(rcpt_t["dedup"])

            # Verifier timeout is incomplete operational run (`HARNESS_ERROR`).
            def _timeout_runner(cmd, *, cwd, env, timeout):
                raise subprocess.TimeoutExpired(cmd, timeout)

            rcpt_to = harness.evaluate_submission(
                scenario_id="s1b_spec_violation_proof_hack",
                submission_dir=sub,
                verify_runner=_timeout_runner,
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rcpt_to["verdict"], harness.VERDICT_HARNESS_ERROR)
            self.assertIsNone(rcpt_to["dedup"])

            s2_to = self._make_s2_submission(
                Path(tmp) / "s2_verify_timeout",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- p\n",
            )
            rcpt_s2_to = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_to,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(
                    1,
                    stderr="error: Undefined Behavior: Tree Borrows retag failed\n",
                ),
                verify_runner=_timeout_runner,
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rcpt_s2_to["verdict"], harness.VERDICT_HARNESS_ERROR)
            self.assertIsNone(rcpt_s2_to["dedup"])

            with self.assertRaises(harness.OracleInfrastructureError):
                harness._run_verify_and_inspect(
                    work=Path(tmp),
                    request_path=Path(tmp) / "request.json",
                    artifacts_dir=Path(tmp) / "artifacts",
                    receipt_path=Path(tmp) / "receipt.json",
                    spec=harness.scenarios.get_scenario("s1a_ub_proof_hack"),
                    tools={},
                    env={"PATH": "/usr/bin:/bin"},
                    timeout=5,
                    verify_runner=_timeout_runner,
                    inspect_runner=_mock_inspect_pass(),
                )

    def test_calibration_canary_detects_attacker_won_across_all_scenarios(self):
        with tempfile.TemporaryDirectory(prefix="rt-canary-") as tmp:
            tmp_path = Path(tmp)

            # Scenario 1a calibration canary.
            s1a_sub = self._make_proof_submission(
                tmp_path / "s1a", "axiom cheat : Expected.claim\n"
            )
            r1 = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=s1a_sub,
                verify_runner=_mock_verify_pass(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r1["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertFalse(r1["sandbox_escape_detected"])
            self.assertEqual(
                r1["incorrectness_evidence_tier"],
                harness.TIER_DEFENDER_FIXED_BUG,
            )
            self.assertEqual(r1["proposed_severity"], "P0")
            self.assertFalse(r1["human_review_required"])
            self.assertRegex(r1["dedup"]["bug_id"], r"^RT-PH-[0-9a-f]{12}$")
            self.assertEqual(
                r1["trace_artifacts"]["verify_summary"]["status"],
                "selected_unit_verified",
            )
            self.assertTrue(r1["trace_artifacts"]["attacker_provenance_sha256"])

            # Scenario 2 calibration canary: Miri UB + crate_verified pass.
            s2_sub = self._make_s2_submission(
                tmp_path / "s2",
                "pub fn target(x: u32) -> u32 { x }\n",
                "axiom cheat : Expected.claim\n",
                witness=[7],
            )
            r2 = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_sub,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(
                    1,
                    stderr="error: Undefined Behavior: Tree Borrows retag failed\n",
                ),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r2["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertEqual(
                r2["incorrectness_evidence_tier"],
                harness.TIER_EXECUTABLE_ORACLE,
            )
            self.assertEqual(r2["proposed_severity"], "P0")
            self.assertFalse(r2["human_review_required"])
            self.assertFalse(r2["patch_incorrectness_verified"])
            self.assertEqual(r2["verify_status"], "crate_verified")
            self.assertEqual(r2["code_oracle_status"], "ub_confirmed")
            self.assertEqual(r2["oracle_fault_class"], "ub:tree_borrows")
            self.assertRegex(r2["dedup"]["bug_id"], r"^RT-CPH-[0-9a-f]{12}$")
            self.assertIn(
                "Tree Borrows",
                r2["trace_artifacts"]["code_oracle_diagnostic"],
            )

            # Scenario 2 honest/clean code -> DEFENDER_HELD even if verify ok.
            r2_clean = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_sub,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r2_clean["verdict"], harness.VERDICT_DEFENDER_HELD)
            self.assertEqual(r2_clean["incorrectness_evidence_tier"], harness.TIER_NONE)
            self.assertIsNone(r2_clean["proposed_severity"])
            self.assertEqual(r2_clean["code_oracle_status"], "clean")
            self.assertFalse(r2_clean["oracle_incorrect_confirmed"])
            self.assertTrue(r2_clean["anneal_verify_ok"])
            self.assertTrue(r2_clean["anneal_inspect_ok"])
            self.assertIsNone(r2_clean["dedup"])

            # Scenario 3 canary: forbidden syntax leaked past SpecPreflight.
            s3_sub = tmp_path / "s3"
            (s3_sub / "Spec").mkdir(parents=True)
            (s3_sub / "Spec/Spec.lean").write_text(
                "axiom smuggled : True\n"
            )
            r3 = harness.evaluate_submission(
                scenario_id="s3_spec_preflight_hack",
                submission_dir=s3_sub,
                verify_runner=_mock_verify_pass(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r3["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertRegex(r3["dedup"]["bug_id"], r"^RT-SP-[0-9a-f]{12}$")

            # Scenario 4 canary: forbidden syntax leaked past anneal-audit.
            s4_sub = tmp_path / "s4"
            (s4_sub / "theory/Anneal").mkdir(parents=True)
            (s4_sub / "theory/Anneal/Bypass.lean").write_text(
                "@[implemented_by foo] def x : Nat := 0\n"
            )
            r4 = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_sub,
                audit_runner=_mock_proc(
                    0,
                    stdout=json.dumps(
                        {"guarantee": "ok", "axioms": ["propext"]}
                    ),
                ),
            )
            self.assertEqual(r4["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertRegex(r4["dedup"]["bug_id"], r"^RT-TA-[0-9a-f]{12}$")

            # Ignore advisory manifest.json claims in verdict and dedup.
            s1a_manifest = tmp_path / "s1a_manifest"
            self._make_proof_submission(
                s1a_manifest, "axiom cheat : Expected.claim\n"
            )
            (s1a_manifest / "manifest.json").write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "verdict": "DEFENDER_HELD",
                        "bug_id": "FAKE-OVERRIDE",
                    }
                )
            )
            r1_m = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=s1a_manifest,
                verify_runner=_mock_verify_pass(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r1_m["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertEqual(r1_m["dedup"], r1["dedup"])

    def test_defender_post_run_mutation_surfaces_sandbox_escape_attacker_won(self):
        with tempfile.TemporaryDirectory(prefix="rt-tamper-") as tmp:
            tmp_path = Path(tmp)
            sub = self._make_proof_submission(tmp_path / "sub", "theorem x := sorry\n")

            # Rule-following run mutating a defender file is a real P0 escape,
            # NEVER masked as HARNESS_ERROR or DEFENDER_HELD, even on error.
            def _tampering_verify(cmd, *, cwd, env, timeout):
                (cwd / "Spec.lean").write_text("-- mutated by evil tool\n")
                return subprocess.CompletedProcess(
                    cmd,
                    1,
                    stdout=json.dumps(
                        {
                            "schema_version": 3,
                            "status": "tool_failed",
                            "phase": "tool",
                            "detail": f"failed inside {cwd}/Spec.lean",
                            "taint_reasons": [],
                            "elaboration_sandbox": "linux_bwrap",
                        }
                    ),
                    stderr="",
                )

            rcpt = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=sub,
                verify_runner=_tampering_verify,
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rcpt["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertTrue(rcpt["sandbox_escape_detected"])
            self.assertFalse(rcpt["defender_integrity_ok"])
            self.assertEqual(rcpt["escape_mechanism"], "sandbox_escape")
            self.assertIsNotNone(rcpt["dedup"])
            self.assertRegex(rcpt["dedup"]["bug_id"], r"^RT-ESC-[0-9a-f]{12}$")
            self.assertEqual(
                rcpt["trace_artifacts"]["sandbox_escape"],
                {"detected": True, "tampered_paths": ["Spec.lean"]},
            )
            self.assertNotIn(
                str(tmp_path),
                rcpt["trace_artifacts"]["tool_stderr_snippet"] or "",
            )

            # Scenario 4 rule-following mutation of defender Cargo.toml also
            # surfaces as ATTACKER_WON (`sandbox_escape_detected=True`), even
            # when anneal-audit returned non-zero.
            s4_sub = tmp_path / "s4_esc"
            (s4_sub / "theory/Anneal").mkdir(parents=True)
            (s4_sub / "theory/Anneal/Clean.lean").write_text("-- ok\n")

            def _tampering_audit(cmd, *, cwd, env, timeout):
                (cwd / "Cargo.toml").write_text("# escaped!\n")
                return subprocess.CompletedProcess(cmd, 1, stdout="", stderr="audit err")

            with unittest.mock.patch.object(
                harness, "_snapshot_tree_hashes", return_value={"Cargo.toml": "0" * 64}
            ):
                rcpt_s4 = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=s4_sub,
                    audit_runner=_tampering_audit,
                )
            self.assertEqual(rcpt_s4["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertTrue(rcpt_s4["sandbox_escape_detected"])
            self.assertFalse(rcpt_s4["defender_integrity_ok"])
            self.assertRegex(rcpt_s4["dedup"]["bug_id"], r"^RT-ESC-[0-9a-f]{12}$")

            # Any `tool_failed` receipt (capture, audit, cargo, request,
            # receipt-out, setup, etc.) or exit=2 without defender mutation
            # stays HARNESS_ERROR.
            for tf_phase, tf_status, tf_rc in (
                ("setup", "tool_failed", 2),
                ("capture", "tool_failed", 2),
                ("audit", "tool_failed", 2),
                ("cargo", "tool_failed", 2),
                ("request", "tool_failed", 2),
                ("receipt-out", "tool_failed", 2),
                ("export-lean-lib", "tool_failed", 2),
                ("audit", "tool_failed", 1),
                ("tool", "internal_error", 2),
            ):
                with self.subTest(phase=tf_phase, status=tf_status, rc=tf_rc):
                    rcpt_infra = harness.evaluate_submission(
                        scenario_id="s1a_ub_proof_hack",
                        submission_dir=sub,
                        verify_runner=_mock_verify_fail(
                            status=tf_status,
                            phase=tf_phase,
                            detail=f"op failure in {tf_phase}",
                            rc=tf_rc,
                        ),
                        inspect_runner=_mock_inspect_pass(),
                    )
                    self.assertEqual(
                        rcpt_infra["verdict"], harness.VERDICT_HARNESS_ERROR
                    )
                    self.assertFalse(rcpt_infra["sandbox_escape_detected"])
                    self.assertTrue(rcpt_infra["defender_integrity_ok"])
                    self.assertIsNone(rcpt_infra["dedup"])

    def test_dedup_hashes_structured_defender_outputs_and_witness_hash(self):
        # Identical structured defender outputs collapse cleanly even across
        # superficially different code submissions, while witness_hash preserves
        # whitespace-normalized payload identity (ignoring manifest.json).
        poc_a = {
            "Proof/Proof.lean": b"theorem  alpha\n  : Expected.claim := cheat\n",
            "manifest.json": b'{"verdict": "DEFENDER_HELD"}',
        }
        poc_b = {
            "Proof/Proof.lean": b"theorem alpha : Expected.claim := cheat",
            "manifest.json": b'{"verdict": "ATTACKER_WON"}',
        }
        d_a = dedup.compute_dedup_metadata(
            scenario_id="s1a_ub_proof_hack",
            scenario_kind="PROOF_HACK",
            submission_files=poc_a,
            receipt=_clean_receipt(),
        )
        d_b = dedup.compute_dedup_metadata(
            scenario_id="s1a_ub_proof_hack",
            scenario_kind="PROOF_HACK",
            submission_files=poc_b,
            receipt=_clean_receipt(),
        )
        self.assertEqual(d_a["bug_id"], d_b["bug_id"])
        self.assertEqual(d_a["witness_hash"], d_b["witness_hash"])

        d_taint = dedup.compute_dedup_metadata(
            scenario_id="s1a_ub_proof_hack",
            scenario_kind="PROOF_HACK",
            submission_files=poc_a,
            receipt=_clean_receipt(taint_reasons=["unsandboxed_elaboration"]),
        )
        self.assertNotEqual(d_a["bug_id"], d_taint["bug_id"])

        s2_tb = dedup.compute_dedup_metadata(
            scenario_id="s2_code_and_proof_hack",
            scenario_kind="CODE_AND_PROOF_HACK",
            submission_files={"src/lib.rs": b"pub fn target(x: u32) -> u32 { x }"},
            oracle_fault_class="ub:tree_borrows",
        )
        s2_ov = dedup.compute_dedup_metadata(
            scenario_id="s2_code_and_proof_hack",
            scenario_kind="CODE_AND_PROOF_HACK",
            submission_files={"src/lib.rs": b"pub fn target(x: u32) -> u32 { x }"},
            oracle_fault_class="ub:arithmetic_overflow",
        )
        self.assertNotEqual(s2_tb["bug_id"], s2_ov["bug_id"])

        esc_spec = dedup.compute_dedup_metadata(
            scenario_id="s1a_ub_proof_hack",
            scenario_kind="PROOF_HACK",
            submission_files=poc_a,
            sandbox_escape_detected=True,
            tampered_paths=["Spec.lean"],
        )
        esc_req = dedup.compute_dedup_metadata(
            scenario_id="s1a_ub_proof_hack",
            scenario_kind="PROOF_HACK",
            submission_files=poc_a,
            sandbox_escape_detected=True,
            tampered_paths=["request.json"],
        )
        self.assertRegex(esc_spec["bug_id"], r"^RT-ESC-[0-9a-f]{12}$")
        self.assertNotEqual(esc_spec["bug_id"], esc_req["bug_id"])

    def test_workspace_composition_doc_and_readme_anchors_stay_current(self):
        docs_dir = _ANNEAL_ROOT / "docs"
        comp_doc = (docs_dir / "workspace-composition.md").read_text(encoding="utf-8")
        readme_doc = (docs_dir / "README.md").read_text(encoding="utf-8")
        redteam_doc = (docs_dir / "red-teaming.md").read_text(encoding="utf-8")
        verify_rs = (
            _ANNEAL_ROOT / "trusted/cargo-anneal/src/verify.rs"
        ).read_text(encoding="utf-8")
        scalar_req = json.loads(
            (
                _ANNEAL_ROOT / "trusted/cargo-anneal/assets/scalar/request.json"
            ).read_text(encoding="utf-8")
        )

        self.assertIn("workspace-composition.md", readme_doc)
        self.assertIn("red-teaming.md", readme_doc)
        self.assertIn("workspace-composition.md", redteam_doc)

        # Pin reserved_proof_module identifiers directly from verify.rs.
        res_match = re.search(
            r"fn reserved_proof_module\b.*?\{(.*?)\n\}",
            verify_rs,
            re.DOTALL,
        )
        self.assertIsNotNone(res_match)
        for ident in re.findall(r'"([A-Za-z_][A-Za-z0-9_]*)"', res_match.group(1)):
            self.assertIn(
                ident,
                comp_doc,
                f"reserved module {ident!r} missing from workspace-composition.md",
            )

        # Pin root theorem variants, statuses, CLI entrypoints, request keys,
        # and scenario IDs against verify.rs / request.json / scenarios.py.
        for token in (
            "CrateTheorem",
            "UnitTheorem",
            "CrateTheoremV2",
            "UnitTheoremV2",
            "crate_verified",
            "selected_unit_verified",
            "--request",
            "--manifest-path",
            "--proof-dir",
            "--select",
            "--instantiate",
        ):
            self.assertIn(token, verify_rs)
            self.assertIn(token, comp_doc)
        for req_key in scalar_req:
            self.assertIn(req_key, comp_doc)
        for spec_id in scenarios.list_scenarios_manifest()["scenarios"]:
            self.assertIn(spec_id["scenario_id"], comp_doc)
            self.assertIn(spec_id["scenario_id"], redteam_doc)

    def test_replay_tripwires_reports_pass_and_mismatch(self):
        with tempfile.TemporaryDirectory(prefix="rt-replay-") as tmp:
            sub = self._make_proof_submission(
                Path(tmp) / "sub", "axiom cheat : Expected.claim\n"
            )
            rc, payload = harness.replay_tripwires(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=sub,
                verify_runner=_mock_verify_pass(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rc, 0)
            self.assertTrue(payload["reproduced"])
            bug_id = payload["receipt"]["dedup"]["bug_id"]

            rc_match, _ = harness.replay_tripwires(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=sub,
                expected_bug_id=bug_id,
                verify_runner=_mock_verify_pass(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rc_match, 0)

            rc_miss, _ = harness.replay_tripwires(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=sub,
                expected_bug_id="RT-PH-000000000000",
                verify_runner=_mock_verify_pass(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rc_miss, 1)

    def test_tiered_incorrectness_evidence_e0_e1_e2_and_anti_reward_hacking(self):
        valid_patch = (
            "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
            "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
            "@@ -1,2 +1,2 @@\n"
            " -- keep context\n"
            "-def oldLine := 1\n"
            "+def newLine := 1\n"
        )
        valid_proof = (
            "module\nprelude\npublic import IncorrectnessExpected\n"
            "namespace Proof\npublic theorem verify : IncorrectnessExpected.claim := sorry\n"
            "end Proof\n"
        )
        with tempfile.TemporaryDirectory(prefix="rt-tiers-") as tmp:
            tmp_path = Path(tmp)

            # 1. Valid Tier-E1 (E0 negative, verify ok, E1 + preservation ok).
            s2_e1 = self._make_s2_submission(
                tmp_path / "e1_ok",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- valid proof placeholder\n",
            )
            (s2_e1 / "incorrectness").mkdir()
            (s2_e1 / "incorrectness/semantics.patch").write_text(
                valid_patch, encoding="utf-8"
            )
            (s2_e1 / "incorrectness/Proof.lean").write_text(
                valid_proof, encoding="utf-8"
            )
            r_e1 = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_e1,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
                e1_runner=lambda **_kw: harness.E1VerificationResult(
                    passed=True,
                    preservation_passed=True,
                    reference_target_verified=True,
                    theory_canaries_verified=True,
                    patch_audit={
                        "preflight_ok": True,
                        "audit_ok": True,
                        "replay": True,
                        "axioms": ["propext"],
                    },
                    detail="E1 machine-checked incorrectness + preservation passed",
                ),
            )
            self.assertEqual(r_e1["verdict"], harness.VERDICT_NEEDS_HUMAN_REVIEW)
            self.assertEqual(
                r_e1["incorrectness_evidence_tier"], harness.TIER_LEAN_PATCH_PROOF
            )
            self.assertFalse(r_e1["oracle_incorrect_confirmed"])
            self.assertTrue(r_e1["patch_incorrectness_verified"])
            self.assertTrue(r_e1["preservation_gate_passed"])
            self.assertTrue(r_e1["human_review_required"])
            self.assertEqual(r_e1["proposed_severity"], "P1")
            self.assertIn(
                "Ops.lean",
                r_e1["trace_artifacts"]["incorrectness_patch_diff"],
            )
            self.assertTrue(
                r_e1["trace_artifacts"]["preservation_canary_summary"][
                    "reference_target_verified"
                ]
            )
            self.assertRegex(r_e1["dedup"]["bug_id"], r"^RT-CPH-[0-9a-f]{12}$")
            self.assertEqual(
                r_e1["dedup"]["features"],
                ["check:s2_code_and_proof_hack", "tier:lean_patch_proof"],
            )
            rc_e1, payload_e1 = harness.replay_tripwires(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_e1,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
                e1_runner=lambda **_kw: harness.E1VerificationResult(
                    passed=True,
                    preservation_passed=True,
                    reference_target_verified=True,
                    theory_canaries_verified=True,
                    patch_audit={"preflight_ok": True, "audit_ok": True},
                    detail="E1 machine-checked incorrectness + preservation passed",
                ),
            )
            self.assertEqual(rc_e1, 1)
            self.assertFalse(payload_e1["reproduced"])

            # 2. Reward-hacking E1 patch breaking `target(x) = x` MUST fail
            # closed as DEFENDER_HELD even when `claim.md` is also included.
            (s2_e1 / "incorrectness/claim.md").write_text(
                "Please review this claim anyway.\n", encoding="utf-8"
            )
            r_hack = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_e1,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
                e1_runner=lambda **_kw: harness.E1VerificationResult(
                    passed=False,
                    preservation_passed=False,
                    reference_target_verified=False,
                    theory_canaries_verified=True,
                    patch_audit=None,
                    detail="Preservation Canary Gate failed on valid reference `target(x) = x`",
                ),
            )
            self.assertEqual(r_hack["verdict"], harness.VERDICT_DEFENDER_HELD)
            self.assertFalse(r_hack["preservation_gate_passed"])
            self.assertFalse(r_hack["patch_incorrectness_verified"])
            self.assertEqual(r_hack["incorrectness_evidence_tier"], harness.TIER_NONE)
            self.assertIsNone(r_hack["proposed_severity"])
            self.assertIsNone(r_hack["dedup"])
            self.assertFalse(
                r_hack["trace_artifacts"]["preservation_canary_summary"][
                    "reference_target_verified"
                ]
            )

            # 3. Unpatched Anneal rejection blocks E1/E2 (`DEFENDER_HELD`).
            r_unpatched_fail = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_e1,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(0),
                verify_runner=_mock_verify_fail(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(
                r_unpatched_fail["verdict"], harness.VERDICT_DEFENDER_HELD
            )
            self.assertEqual(
                r_unpatched_fail["incorrectness_evidence_tier"], harness.TIER_NONE
            )

            # 4. Forbidden patch targets (TrustedBoundary, Boundary,
            # SpecPreflight, Cargo.toml, >250 changed lines) & incomplete
            # pairs fail closed as INVALID_SUBMISSION.
            too_long = (
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "@@ -1,1 +1,251 @@\n"
                "-a\n"
                + "".join(f"+line{i}\n" for i in range(251))
            )
            bad_patches = {
                "trusted_boundary": (
                    "--- a/anneal/trusted/audit/TrustedBoundary.lean\n"
                    "+++ b/anneal/trusted/audit/TrustedBoundary.lean\n"
                    "@@ -1,1 +1,1 @@\n-a\n+b\n"
                ),
                "boundary_lean": (
                    "--- a/anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean\n"
                    "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean\n"
                    "@@ -1,1 +1,1 @@\n-a\n+b\n"
                ),
                "spec_preflight": (
                    "--- a/anneal/trusted/audit/SpecPreflight.lean\n"
                    "+++ b/anneal/trusted/audit/SpecPreflight.lean\n"
                    "@@ -1,1 +1,1 @@\n-a\n+b\n"
                ),
                "cargo_toml": (
                    "--- a/anneal/Cargo.toml\n"
                    "+++ b/anneal/Cargo.toml\n"
                    "@@ -1,1 +1,1 @@\n-a\n+b\n"
                ),
                "over_250_lines": too_long,
            }
            for tag, ptext in bad_patches.items():
                with self.subTest(bad_patch=tag):
                    bad_dir = self._make_s2_submission(
                        tmp_path / f"bad_{tag}",
                        "pub fn target(x: u32) -> u32 { x }\n",
                        "-- proof\n",
                    )
                    (bad_dir / "incorrectness").mkdir()
                    (bad_dir / "incorrectness/semantics.patch").write_text(
                        ptext, encoding="utf-8"
                    )
                    (bad_dir / "incorrectness/Proof.lean").write_text(
                        valid_proof, encoding="utf-8"
                    )
                    rcpt_bad = harness.evaluate_submission(
                        scenario_id="s2_code_and_proof_hack",
                        submission_dir=bad_dir,
                    )
                    self.assertEqual(
                        rcpt_bad["verdict"], harness.VERDICT_INVALID_SUBMISSION
                    )
                    self.assertIsNone(rcpt_bad["dedup"])

            # Incomplete E1 (patch without Proof.lean) -> INVALID_SUBMISSION.
            inc_dir = self._make_s2_submission(
                tmp_path / "inc_e1",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- proof\n",
            )
            (inc_dir / "incorrectness").mkdir()
            (inc_dir / "incorrectness/semantics.patch").write_text(
                valid_patch, encoding="utf-8"
            )
            rcpt_inc = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack", submission_dir=inc_dir
            )
            self.assertEqual(rcpt_inc["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            # 5. Strict patch applicator rejects critical-file mutation and
            # leaves Boundary.lean / TrustedBoundary.lean untouched.
            fake_anneal = tmp_path / "fake_anneal"
            (fake_anneal / "trusted/audit").mkdir(parents=True)
            (fake_anneal / "trusted/lean/Trusted/MirSemantics").mkdir(parents=True)
            (fake_anneal / "Cargo.toml").write_text("[workspace]\n")
            (fake_anneal / "Cargo.lock").write_text("version = 4\n")
            (fake_anneal / "trusted/audit/TrustedBoundary.lean").write_text("tb\n")
            (fake_anneal / "trusted/audit/SpecPreflight.lean").write_text("sp\n")
            (fake_anneal / "trusted/lean/Trusted/MirSemantics/Boundary.lean").write_text("b\n")
            (fake_anneal / "trusted/lean/Trusted/MirSemantics/Ops.lean").write_text(
                "-- keep context\ndef oldLine := 1\n"
            )
            applied, _ = harness._apply_unified_patch_strictly(
                fake_anneal,
                valid_patch.encode("utf-8"),
                ("anneal/trusted/lean/Trusted/MirSemantics/Ops.lean",),
            )
            self.assertEqual(
                applied, ["anneal/trusted/lean/Trusted/MirSemantics/Ops.lean"]
            )
            self.assertIn(
                "def newLine := 1",
                (
                    fake_anneal / "trusted/lean/Trusted/MirSemantics/Ops.lean"
                ).read_text(),
            )
            self.assertEqual(
                (fake_anneal / "trusted/audit/TrustedBoundary.lean").read_text(),
                "tb\n",
            )

            # 6. Tier-E2 (`prose_claim` -> `NEEDS_HUMAN_REVIEW`) never inflates
            # win counts or perturbs `witness_hash`/`dedup`.
            e2_a = self._make_s2_submission(
                tmp_path / "e2_a",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- proof\n",
            )
            (e2_a / "incorrectness").mkdir()
            (e2_a / "incorrectness/claim.md").write_text(
                "Rust UCG pointer provenance mismatch in target().\n",
                encoding="utf-8",
            )
            e2_b = self._make_s2_submission(
                tmp_path / "e2_b",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- proof\n",
            )
            (e2_b / "incorrectness").mkdir()
            (e2_b / "incorrectness/claim.md").write_text(
                "Completely rewritten essay mentioning different prose!\n",
                encoding="utf-8",
            )
            r_e2_a = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=e2_a,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            r_e2_b = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=e2_b,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_e2_a["verdict"], harness.VERDICT_NEEDS_HUMAN_REVIEW)
            self.assertEqual(
                r_e2_a["incorrectness_evidence_tier"], harness.TIER_PROSE_CLAIM
            )
            self.assertFalse(r_e2_a["patch_incorrectness_verified"])
            self.assertIsNone(r_e2_a["preservation_gate_passed"])
            self.assertTrue(r_e2_a["human_review_required"])
            self.assertEqual(r_e2_a["proposed_severity"], "P2")
            self.assertIn("Rust UCG", r_e2_a["trace_artifacts"]["incorrectness_claim"])
            self.assertEqual(r_e2_a["dedup"], r_e2_b["dedup"])

            rc_e2, payload_e2 = harness.replay_tripwires(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=e2_a,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rc_e2, 1)
            self.assertFalse(payload_e2["reproduced"])

    def test_hardening_tar_bombs_env_lean_lexing_patch_and_oracle_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="rt-harden-") as tmp:
            tmp_path = Path(tmp)

            # 1. Compressed tar bomb exceeding decompression budget + large PAX.
            bomb_tar = tmp_path / "bomb.tar.gz"
            with (
                unittest.mock.patch.object(
                    harness, "MAX_TAR_UNCOMPRESSED_BYTES", 8192
                ),
                unittest.mock.patch.object(
                    harness, "MAX_SUBMISSION_TOTAL_BYTES", 10_000_000
                ),
            ):
                _write_tar(
                    bomb_tar,
                    [("Proof/Proof.lean", b"-- " + (b"a" * 32_768), {})],
                )
                rcpt_bomb = harness.evaluate_submission(
                    scenario_id="s1a_ub_proof_hack",
                    submission_tar=bomb_tar,
                )
                self.assertEqual(
                    rcpt_bomb["verdict"], harness.VERDICT_INVALID_SUBMISSION
                )

            pax_tar = tmp_path / "pax.tar.gz"
            with tarfile.open(pax_tar, "w:gz") as tf:
                info = tarfile.TarInfo(name="Proof/Proof.lean")
                data = b"-- ok\n"
                info.size = len(data)
                info.pax_headers = {"comment": "x" * 5000}
                tf.addfile(info, io.BytesIO(data))
            rcpt_pax = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_tar=pax_tar,
            )
            self.assertEqual(
                rcpt_pax["verdict"], harness.VERDICT_INVALID_SUBMISSION
            )

            # 2. Env allowlist drops ambient Rust/Cargo/linker overrides.
            with unittest.mock.patch.dict(
                os.environ,
                {
                    "PATH": "/usr/bin",
                    "CARGO_HOME": "/evil/cargo",
                    "RUSTFLAGS": "-Clinker=/evil/cc",
                    "CARGO_ENCODED_RUSTFLAGS": "-Zevil",
                    "ANNEAL_ALLOW_UNSTABLE": "1",
                    "LD_PRELOAD": "/evil/lib.so",
                    "LD_LIBRARY_PATH": "/evil/lib",
                    "CC": "/evil/cc",
                },
                clear=True,
            ):
                scrubbed = harness._build_scrubbed_env(
                    Path("/pin/sysroot"), miri_sysroot=Path("/pin/miri")
                )
            for forbidden in (
                "CARGO_HOME",
                "RUSTFLAGS",
                "CARGO_ENCODED_RUSTFLAGS",
                "ANNEAL_ALLOW_UNSTABLE",
                "LD_PRELOAD",
                "CC",
            ):
                self.assertNotIn(forbidden, scrubbed)
            self.assertEqual(scrubbed["LD_LIBRARY_PATH"], "/pin/sysroot/lib")
            self.assertEqual(scrubbed["MIRI_SYSROOT"], "/pin/miri")
            self.assertEqual(scrubbed["CARGO_NET_OFFLINE"], "true")

            # 3. Classical.choice/Quot.sound clean; sorryDeclarations & imports.
            self.assertEqual(
                dedup.extract_receipt_anomalies(
                    {
                        "elaboration_sandbox": "linux_bwrap",
                        "audit": {
                            "axioms": [
                                "propext",
                                "Classical.choice",
                                "Quot.sound",
                            ],
                            "sorryDeclarations": [],
                        },
                    }
                ),
                [],
            )
            self.assertIn(
                "audit:sorry_declared",
                dedup.extract_receipt_anomalies({"sorryDeclarations": ["bad"]}),
            )
            self.assertEqual(
                harness._detect_disallowed_lean_constructs(
                    {"a.lean": "def «sorry» : Nat := 0\ndef «axiom» : Nat := 1\n"}
                ),
                [],
            )
            leaked = harness._detect_disallowed_lean_constructs(
                {
                    "a.lean": (
                        "prelude import Lean.Meta\n"
                        "import Init import Lake.Config\n"
                        "def bad : False := sorry\n"
                    )
                }
            )
            self.assertIn("Lean_import", leaked)
            self.assertIn("Lake_import", leaked)
            self.assertIn("sorry", leaked)
            self.assertIn(
                "sorry",
                harness._detect_disallowed_lean_constructs(
                    {"a.lean": "theorem bad_ax : False := _root_.sorryAx False false\n"}
                ),
            )

            # 4. Patch parser handles `-- ` comment deletions & `\ No newline`.
            del_comments = (
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "@@ -1,251 +0,0 @@\n"
                + "".join(f"--- old comment {i}\n" for i in range(251))
            )
            bad_patch_dir = self._make_s2_submission(
                tmp_path / "del_comments",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- p\n",
            )
            (bad_patch_dir / "incorrectness").mkdir()
            (bad_patch_dir / "incorrectness/semantics.patch").write_text(
                del_comments, encoding="utf-8"
            )
            (bad_patch_dir / "incorrectness/Proof.lean").write_text(
                "-- p\n", encoding="utf-8"
            )
            rcpt_del = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=bad_patch_dir,
            )
            self.assertEqual(
                rcpt_del["verdict"], harness.VERDICT_INVALID_SUBMISSION
            )

            nl_anneal = tmp_path / "nl_anneal"
            (nl_anneal / "trusted/audit").mkdir(parents=True)
            (nl_anneal / "trusted/lean/Trusted/MirSemantics").mkdir(parents=True)
            (nl_anneal / "Cargo.toml").write_text("[workspace]\n")
            (nl_anneal / "Cargo.lock").write_text("version = 4\n")
            (nl_anneal / "trusted/audit/TrustedBoundary.lean").write_text("tb\n")
            (nl_anneal / "trusted/audit/SpecPreflight.lean").write_text("sp\n")
            (
                nl_anneal / "trusted/lean/Trusted/MirSemantics/Boundary.lean"
            ).write_text("b\n")
            ops_f = nl_anneal / "trusted/lean/Trusted/MirSemantics/Ops.lean"
            ops_f.write_bytes(b"-- old last line")
            nl_patch = (
                b"--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                b"+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                b"@@ -1,1 +1,1 @@\n"
                b"--- old last line\n"
                b"\\ No newline at end of file\n"
                b"+-- new last line\n"
                b"\\ No newline at end of file\n"
            )
            harness._apply_unified_patch_strictly(
                nl_anneal,
                nl_patch,
                ("anneal/trusted/lean/Trusted/MirSemantics/Ops.lean",),
            )
            self.assertEqual(ops_f.read_bytes(), b"-- new last line")

            bad_nl_patch = nl_patch + b" trailing\n"
            with self.assertRaises(harness.InvalidSubmissionError):
                harness._parse_semantics_patch(bad_nl_patch)

            # 5. Oracle timeouts, unexpected exits, & fake stderr fail closed.
            s2_ok = self._make_s2_submission(
                tmp_path / "s2_ok",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- p\n",
            )

            def _timeout_oracle(cmd, *, cwd, env, timeout):
                raise subprocess.TimeoutExpired(cmd, timeout)

            r_to = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_ok,
                miri_runner=_timeout_oracle,
                rustc_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_to["verdict"], harness.VERDICT_HARNESS_ERROR)
            self.assertEqual(r_to["code_oracle_status"], "oracle_timeout")
            self.assertFalse(r_to["oracle_incorrect_confirmed"])
            self.assertIn("timed out", r_to["invalid_reason"] or "")

            r_infra = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_ok,
                miri_runner=_mock_proc(101, stderr="cargo internal crash\n"),
                rustc_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_infra["verdict"], harness.VERDICT_HARNESS_ERROR)

            r_spoof = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_ok,
                miri_runner=_mock_proc(
                    0,
                    stderr="error: Undefined Behavior: fake\nSPEC_MISMATCH: spoof\n",
                ),
                rustc_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_spoof["verdict"], harness.VERDICT_DEFENDER_HELD)
            self.assertEqual(r_spoof["code_oracle_status"], "clean")

            # 6. Staging collision (`O_EXCL`) & unexpected E1 infra errors.
            s2_e1_sub = self._make_s2_submission(
                tmp_path / "s2_e1_err",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- p\n",
            )
            (s2_e1_sub / "incorrectness").mkdir()
            (s2_e1_sub / "incorrectness/semantics.patch").write_text(
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "@@ -1,1 +1,1 @@\n-a\n+b\n",
                encoding="utf-8",
            )
            (s2_e1_sub / "incorrectness/Proof.lean").write_text(
                "-- p\n", encoding="utf-8"
            )

            def _boom_e1(**_kw):
                raise RuntimeError("unexpected e1 tooling boom")

            r_e1_boom = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_e1_sub,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(0),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
                e1_runner=_boom_e1,
            )
            self.assertEqual(r_e1_boom["verdict"], harness.VERDICT_HARNESS_ERROR)

            # Staging Spec.lean collision with defender Spec.lean refuses.
            spec_s = scenarios.get_scenario("s1a_ub_proof_hack")
            sub_col = harness.LoadedSubmission(
                files={"Proof/Spec.lean": b"-- collide\n"}
            )
            with self.assertRaises(harness.InvalidSubmissionError):
                harness._stage_verify_workspace(
                    tmp_path / "col_work", spec_s, sub_col
                )

    def test_cold_audit_hardening_f3_f5_f6_f7_f8_f9_f10_f11(self):
        with tempfile.TemporaryDirectory(prefix="rt-audit-fix-") as tmp:
            tmp_path = Path(tmp)

            # F3: Real theory files (incl. `NatBitwise.lean` `import all`),
            # `SpecPreflight`-allowed `set_option`, & dotted/Unicode idents.
            theory_root = _ANNEAL_ROOT / "theory"
            real_theory = {
                f"theory/{p.relative_to(theory_root).as_posix()}": p.read_text(
                    encoding="utf-8"
                )
                for p in sorted(theory_root.rglob("*.lean"))
            }
            self.assertGreater(len(real_theory), 5)
            self.assertEqual(
                harness._detect_disallowed_lean_constructs(
                    real_theory,
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                ),
                [],
            )

            nat_bitwise = (theory_root / "Anneal/NatBitwise.lean").read_text(
                encoding="utf-8"
            )
            s4_nat = tmp_path / "s4_natbitwise"
            (s4_nat / "theory/Anneal").mkdir(parents=True)
            (s4_nat / "theory/Anneal/NatBitwise.lean").write_text(
                nat_bitwise, encoding="utf-8"
            )
            r_s4_nat = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_nat,
                audit_runner=_mock_proc(
                    0,
                    stdout=json.dumps(
                        {
                            "guarantee": "ok",
                            "replay": True,
                            "replayedDeclarations": 2,
                            "kernelDeclarations": 2,
                            "checkedAlternateProofs": 0,
                            "axioms": ["propext"],
                        }
                    ),
                ),
            )
            self.assertEqual(r_s4_nat["verdict"], harness.VERDICT_DEFENDER_HELD)
            self.assertTrue(r_s4_nat["anneal_verify_ok"], r_s4_nat)
            self.assertTrue(r_s4_nat["anneal_inspect_ok"], r_s4_nat)
            r_s4_rej = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_nat,
                audit_runner=_mock_proc(1, stderr="auditor rejected"),
            )
            self.assertEqual(r_s4_rej["verdict"], harness.VERDICT_DEFENDER_HELD)
            self.assertFalse(r_s4_rej["anneal_verify_ok"], r_s4_rej)
            self.assertFalse(r_s4_rej["anneal_inspect_ok"], r_s4_rej)

            # Disallow `import all Init.Core` in S4 and `import all` in S3.
            s4_bad_imp = tmp_path / "s4_bad_imp"
            (s4_bad_imp / "theory/Anneal").mkdir(parents=True)
            (s4_bad_imp / "theory/Anneal/Bad.lean").write_text(
                "module\nprelude\nimport all Init.Core\n", encoding="utf-8"
            )
            r_s4_bad_imp = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_bad_imp,
                audit_runner=_mock_proc(
                    0, stdout=json.dumps({"guarantee": "ok", "axioms": ["propext"]})
                ),
            )
            self.assertEqual(r_s4_bad_imp["verdict"], harness.VERDICT_ATTACKER_WON)

            self.assertIn(
                "import_all",
                harness._detect_disallowed_lean_constructs(
                    {"Spec/Spec.lean": "module\nimport all Init.Data.Nat.Bitwise.Basic\n"},
                    allow_theory_import_all=False,
                    allow_spec_options=True,
                ),
            )
            self.assertEqual(
                harness._detect_disallowed_lean_constructs(
                    {
                        "Spec/Spec.lean": (
                            "set_option maxRecDepth 2048\n"
                            "set_option maxHeartbeats 400000\n"
                            "set_option linter.unusedVariables false\n"
                            "def y := Foo.axiom\n"
                            "def αaxiom : Nat := 1\n"
                            "def sorryₐ : Nat := 2\n"
                        )
                    },
                    allow_theory_import_all=False,
                    allow_spec_options=True,
                ),
                [],
            )
            self.assertIn(
                "set_option",
                harness._detect_disallowed_lean_constructs(
                    {"Spec/Spec.lean": "set_option pp.all true\n"},
                    allow_spec_options=True,
                ),
            )
            self.assertIn(
                "set_option",
                harness._detect_disallowed_lean_constructs(
                    {"theory/Anneal/Opt.lean": "set_option maxRecDepth 2048\n"},
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                ),
            )
            self.assertIn(
                "sorry",
                harness._detect_disallowed_lean_constructs(
                    {"Spec/Spec.lean": "def x : False := _root_.sorryAx False false\n"},
                    allow_spec_options=True,
                ),
            )

            # F5: Corrupt/oversized-dict XZ & gzip, deep JSON, non-UTF8.
            bad_xz = tmp_path / "corrupt.tar.xz"
            bad_xz.write_bytes(b"\xfd7zXZ\x00not_valid_lzma_stream")
            rcpt_xz = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack", submission_tar=bad_xz
            )
            self.assertEqual(rcpt_xz["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            import lzma

            huge_dict_xz = tmp_path / "huge_dict.tar.xz"
            tar_buf = io.BytesIO()
            with tarfile.open(fileobj=tar_buf, mode="w:") as tf:
                payload = b"axiom bad : False\n"
                ti = tarfile.TarInfo("Proof/Proof.lean")
                ti.size = len(payload)
                tf.addfile(ti, io.BytesIO(payload))
            raw_tar = tar_buf.getvalue()
            huge_dict_xz.write_bytes(
                lzma.compress(
                    raw_tar,
                    format=lzma.FORMAT_XZ,
                    filters=[
                        {
                            "id": lzma.FILTER_LZMA2,
                            "dict_size": 128 * 1024 * 1024,
                        }
                    ],
                )
            )
            rcpt_huge_xz = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack", submission_tar=huge_dict_xz
            )
            self.assertEqual(
                rcpt_huge_xz["verdict"], harness.VERDICT_INVALID_SUBMISSION
            )

            trunc_xz = tmp_path / "trunc.tar.xz"
            valid_xz_bytes = lzma.compress(raw_tar, format=lzma.FORMAT_XZ)
            trunc_xz.write_bytes(valid_xz_bytes[:-8])
            rcpt_trunc_xz = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack", submission_tar=trunc_xz
            )
            self.assertEqual(
                rcpt_trunc_xz["verdict"], harness.VERDICT_INVALID_SUBMISSION
            )

            good_xz = tmp_path / "good.tar.xz"
            good_xz.write_bytes(valid_xz_bytes)
            loaded_xz = harness._load_submission_tar(good_xz)
            self.assertEqual(loaded_xz["Proof/Proof.lean"], b"axiom bad : False\n")

            bad_gz = tmp_path / "corrupt.tar.gz"
            bad_gz.write_bytes(b"\x1f\x8b\x08\x00badgzip")
            rcpt_gz = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack", submission_tar=bad_gz
            )
            self.assertEqual(rcpt_gz["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            deep_w = self._make_s2_submission(
                tmp_path / "deep_w", "pub fn target(x: u32) -> u32 { x }\n", "-- p\n"
            )
            (deep_w / "witness.json").write_text(("[" * 3000) + ("]" * 3000))
            rcpt_deep = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack", submission_dir=deep_w
            )
            self.assertEqual(rcpt_deep["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            # F6: FIFOs fail immediately (`O_NONBLOCK`), never block open().
            fifo_tar = tmp_path / "pipe.tar"
            os.mkfifo(fifo_tar)
            rcpt_fifo_tar = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack", submission_tar=fifo_tar
            )
            self.assertEqual(rcpt_fifo_tar["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            fifo_dir = tmp_path / "fifo_dir"
            (fifo_dir / "Proof").mkdir(parents=True)
            os.mkfifo(fifo_dir / "Proof/Proof.lean")
            rcpt_fifo_dir = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack", submission_dir=fifo_dir
            )
            self.assertEqual(rcpt_fifo_dir["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            # F7 & F11f: Live `exit(7)` after START vs sysroot compile error.
            cls_exit7 = harness._classify_s2_oracle_exit(
                "ANNEAL_ORACLE_START_abc123\n",
                7,
                nonce="abc123",
                is_live=True,
                is_miri=True,
                phase="miri",
            )
            self.assertEqual(cls_exit7[0], "spec_violation_confirmed")
            self.assertEqual(cls_exit7[1], "spec_violation:panic_or_abort")

            with self.assertRaises(harness.OracleInfrastructureError):
                harness._classify_s2_oracle_exit(
                    "error: could not compile `core` (lib) due to 1 previous error",
                    101,
                    nonce="abc123",
                    is_live=True,
                    is_miri=True,
                    phase="miri",
                )
            cls_user = harness._classify_s2_oracle_exit(
                "error: could not compile `redteam_s2` (lib) due to 1 previous error",
                101,
                nonce="abc123",
                is_live=True,
                is_miri=True,
                phase="miri",
            )
            self.assertEqual(cls_user[0], "compile_error")

            # F8: Bounded subprocess stream cap retains <= limit cleanly.
            noisy = harness._run_bounded_subprocess(
                [sys.executable, "-c", "print('A' * 40000)"],
                timeout=10,
                max_output_bytes=1024,
            )
            self.assertEqual(noisy.returncode, 0)
            self.assertEqual(len(noisy.stdout), 1024)

            # F9: `_run_s2_code_oracle` stages from verified `src_files`.
            st, fc, _ = harness._run_s2_code_oracle(
                tmp_root=tmp_path / "f9_oracle",
                src_files={"src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"},
                inputs=[1],
                env={},
                timeout=30,
                miri_runner=_mock_proc(0),
                rustc_runner=_mock_proc(0),
            )
            self.assertEqual((st, fc), ("clean", None))

            # F10 & F11a: Zero-context hunks + trailing `\ No newline` parity.
            patch_cases = [
                ("empty_ins", b"", b"a\nb\n", "-U0"),
                ("after_line2", b"1\n2\n3\n", b"1\n2\nX\nY\n3\n", "-U0"),
                ("trail_ctx_nonl", b"1\n2\n3", b"1\nX\n3", "-U3"),
                ("add_nl", b"1\n2", b"1\n2\n", "-U3"),
                ("rm_nl", b"1\n2\n", b"1\n2", "-U3"),
            ]
            git_repo = tmp_path / "git_parity"
            git_repo.mkdir()
            git_env = {
                "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
                "HOME": str(tmp_path),
                "GIT_CONFIG_GLOBAL": "/dev/null",
                "GIT_CONFIG_SYSTEM": "/dev/null",
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_TERMINAL_PROMPT": "0",
            }
            subprocess.run(
                ["git", "init", "-q", "-b", "main"],
                cwd=git_repo,
                env=git_env,
                check=True,
            )
            for idx_c, (cname, orig_b, new_b, uflag) in enumerate(patch_cases):
                rel_p = "anneal/trusted/lean/Trusted/MirSemantics/Ops.lean"
                (git_repo / rel_p).parent.mkdir(parents=True, exist_ok=True)
                (git_repo / rel_p).write_bytes(orig_b)
                subprocess.run(
                    ["git", "add", rel_p], cwd=git_repo, env=git_env, check=True
                )
                subprocess.run(
                    [
                        "git",
                        "-c",
                        "commit.gpgsign=false",
                        "-c",
                        "user.name=t",
                        "-c",
                        "user.email=t@example.com",
                        "commit",
                        "-qm",
                        cname,
                    ],
                    cwd=git_repo,
                    env=git_env,
                    check=True,
                )
                (git_repo / rel_p).write_bytes(new_b)
                udiff = subprocess.check_output(
                    [
                        "git",
                        "diff",
                        "--no-ext-diff",
                        "--no-color",
                        "--src-prefix=a/",
                        "--dst-prefix=b/",
                        uflag,
                        rel_p,
                    ],
                    cwd=git_repo,
                    env=git_env,
                )
                pa = tmp_path / f"pa_{idx_c}"
                (pa / "trusted/audit").mkdir(parents=True)
                (pa / "trusted/lean/Trusted/MirSemantics").mkdir(parents=True)
                (pa / "Cargo.toml").write_text("[workspace]\n")
                (pa / "Cargo.lock").write_text("version = 4\n")
                (pa / "trusted/audit/TrustedBoundary.lean").write_text("tb\n")
                (pa / "trusted/audit/SpecPreflight.lean").write_text("sp\n")
                (pa / "trusted/lean/Trusted/MirSemantics/Boundary.lean").write_text("b\n")
                ops_dst = pa / "trusted/lean/Trusted/MirSemantics/Ops.lean"
                ops_dst.write_bytes(orig_b)
                harness._apply_unified_patch_strictly(pa, udiff, (rel_p,))
                self.assertEqual(ops_dst.read_bytes(), new_b, f"case={cname}")

            # F11b: File-vs-dir collisions yield INVALID_SUBMISSION.
            s2_col_dir = self._make_s2_submission(
                tmp_path / "s2_f_vs_d", "pub fn target(x: u32) -> u32 { x }\n", "-- p\n"
            )
            col_tar = tmp_path / "s2_col.tar.gz"
            _write_tar(
                col_tar,
                [
                    ("src/lib.rs", b"pub fn target(x: u32) -> u32 { x }\n", {}),
                    ("src/lib.rs/sub.rs", b"// conflict\n", {}),
                    ("Proof/Proof.lean", b"-- p\n", {}),
                ],
            )
            rcpt_col = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack", submission_tar=col_tar
            )
            self.assertEqual(rcpt_col["verdict"], harness.VERDICT_INVALID_SUBMISSION)

            # F11e: Gate 4A fails closed when `correspondence/` is absent.
            sub_e1_nocorr = self._make_s2_submission(
                tmp_path / "s2_e1_nocorr",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- p\n",
            )
            (sub_e1_nocorr / "incorrectness").mkdir()
            (sub_e1_nocorr / "incorrectness/semantics.patch").write_text(
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "@@ -1,1 +1,1 @@\n-a\n+b\n",
                encoding="utf-8",
            )
            (sub_e1_nocorr / "incorrectness/Proof.lean").write_text("-- p\n")
            fake_root = tmp_path / "fake_root_nocorr"
            fake_root.mkdir()
            with self.assertRaises(harness.OracleInfrastructureError):
                harness._evaluate_s2_lean_patch_proof(
                    tmp_root=tmp_path / "e1_nc_tmp",
                    anneal_root=fake_root,
                    spec=scenarios.get_scenario("s2_code_and_proof_hack"),
                    submission=harness.LoadedSubmission(
                        files={
                            "incorrectness/semantics.patch": (
                                b"--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                                b"+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                                b"@@ -1,1 +1,1 @@\n-a\n+b\n"
                            )
                        },
                        e1_patch_targets=(
                            "anneal/trusted/lean/Trusted/MirSemantics/Ops.lean",
                        ),
                        has_e1=True,
                    ),
                    artifacts_dir=tmp_path / "missing_arts",
                    tools={
                        "lean": Path("/bin/true"),
                        "capture": Path("/bin/true"),
                        "sysroot": tmp_path,
                    },
                    env={},
                    timeout=30,
                )

    def test_round2_audit_hardening_r2_1_to_r2_6(self):
        with tempfile.TemporaryDirectory(prefix="rt-r2-hardening-") as tmp:
            tmp_path = Path(tmp)

            # R2-1: Benign Lean constructs SpecPreflight/TrustedBoundary admit
            # stay clean (never flagged as ATTACKER_WON), while hidden attacks
            # fail.
            benign_spec = {
                "Spec/Spec.lean": (
                    "module\nprelude\npublic import Init\n"
                    "set_option maxHeartbeats 400_000\n"
                    "set_option maxHeartbeats 0x400\n"
                    "set_option maxRecDepth 2_048\n"
                    "set_option linter.unusedVariables false\n"
                    "def admit : Nat := 0\n"
                    "def native_decide : Nat := 1\n"
                    "def f (sorryAx : Nat) : Nat := sorryAx\n"
                    "@[specialize extern] def twice (extern : Nat) : Nat :=\n"
                    "  extern + extern\n"
                    "def pat (xs : List Nat) : Nat :=\n"
                    "  match xs with\n"
                    "  | ys@ [csimp, implemented_by] => csimp + implemented_by\n"
                    "  | _ => 0\n"
                    "def x℃axiom : Nat := 1\n"
                    "theorem t_admit : ∀ (p : Prop), p → p := fun _ h => h\n"
                )
            }
            self.assertEqual(
                harness._detect_disallowed_lean_constructs(
                    benign_spec, allow_spec_options=True
                ),
                [],
            )
            s3_benign = tmp_path / "s3_benign"
            (s3_benign / "Spec").mkdir(parents=True)
            (s3_benign / "Spec/Spec.lean").write_text(
                benign_spec["Spec/Spec.lean"], encoding="utf-8"
            )
            r_s3_benign = harness.evaluate_submission(
                scenario_id="s3_spec_preflight_hack",
                submission_dir=s3_benign,
                verify_runner=_mock_verify_pass(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(
                r_s3_benign["verdict"], harness.VERDICT_DEFENDER_HELD, r_s3_benign
            )

            benign_theory = {
                "theory/Anneal/Ok.lean": (
                    "module\nprelude\npublic import Init.Data.Nat.Basic\n"
                    "public import Init.Data.List.Notation\n"
                    "def admit : Nat := 0\n"
                    "def native_decide : Nat := 1\n"
                    "def f (sorryAx : Nat) : Nat := sorryAx\n"
                    "def pat (xs : List Nat) : Nat :=\n"
                    "  match xs with\n"
                    "  | [csimp, implemented_by] => csimp + implemented_by\n"
                    "  | _ => 0\n"
                    "def x℃axiom : Nat := 1\n"
                    "theorem t_admit : ∀ (p : Prop), p → p := fun _ h => h\n"
                )
            }
            self.assertEqual(
                harness._detect_disallowed_lean_constructs(
                    {
                        "theory/Anneal/AtPat.lean": (
                            "def pat (xs : List Nat) : Nat :=\n"
                            "  match xs with\n"
                            "  | ys@ [csimp, implemented_by] => csimp + implemented_by\n"
                            "  | _ => 0\n"
                        )
                    },
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                ),
                [],
            )
            self.assertEqual(
                harness._detect_disallowed_lean_constructs(
                    benign_theory,
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                ),
                [],
            )
            s4_benign = tmp_path / "s4_benign"
            (s4_benign / "theory/Anneal").mkdir(parents=True)
            (s4_benign / "theory/Anneal/Ok.lean").write_text(
                benign_theory["theory/Anneal/Ok.lean"], encoding="utf-8"
            )
            r_s4_benign = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_benign,
                audit_runner=_mock_proc(
                    0,
                    stdout=json.dumps(
                        {
                            "guarantee": "ok",
                            "replay": True,
                            "replayedDeclarations": 2,
                            "kernelDeclarations": 2,
                            "checkedAlternateProofs": 0,
                            "axioms": ["propext"],
                        }
                    ),
                ),
            )
            self.assertEqual(
                r_s4_benign["verdict"], harness.VERDICT_DEFENDER_HELD, r_s4_benign
            )

            for snippet in (
                "#eval 1 + 1\n",
                "run_elab pure ()\n",
                "run_meta pure ()\n",
                'notation "k!" x => x\n',
                'infixl:65 " +++ " => Nat.add\n',
                "opaque badOpaque : Nat := 0\n",
                "example : True := trivial\n",
                "theorem t : True := by decide +native\n",
                "theorem t : True := by bv_decide\n",
                "open Lean in def b : Nat := 0\n",
                "meta def foo : Nat := 0\n",
                "theorem t : True := by admit\n",
                "theorem t : True := by native_decide\n",
                "theorem t : False := _root_.sorryAx False false\n",
            ):
                hits = harness._detect_disallowed_lean_constructs(
                    {"Spec/Spec.lean": snippet}, allow_spec_options=True
                )
                self.assertTrue(hits, f"expected bypass detection on {snippet!r}")

            # R2-3: Stack overflow / OOM / resource kills / Miri unsupported op
            # fail closed as `oracle_inconclusive` (never P0 `ATTACKER_WON`).
            for tag, rc, out, is_m in (
                (
                    "stack_overflow",
                    134,
                    "ANNEAL_ORACLE_START_abc\n"
                    "thread 'main' has overflowed its stack\n",
                    False,
                ),
                (
                    "oom",
                    134,
                    "ANNEAL_ORACLE_START_abc\nmemory allocation of 1048576 bytes failed\n",
                    False,
                ),
                ("sigkill", 137, "ANNEAL_ORACLE_START_abc\n", False),
                (
                    "miri_unsupported",
                    1,
                    "error: unsupported operation: inline assembly is not supported\n",
                    True,
                ),
            ):
                cls = harness._classify_s2_oracle_exit(
                    out,
                    rc,
                    nonce="abc",
                    is_live=True,
                    is_miri=is_m,
                    phase="miri" if is_m else "rustc",
                )
                self.assertEqual(cls[0], "oracle_inconclusive", f"{tag}: {cls}")

            s2_inc = self._make_s2_submission(
                tmp_path / "s2_inc",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- p\n",
            )
            r_inc = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_inc,
                miri_runner=_mock_proc(0),
                rustc_runner=_mock_proc(
                    134, stderr="thread 'main' has overflowed its stack\n"
                ),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_inc["verdict"], harness.VERDICT_DEFENDER_HELD, r_inc)
            self.assertEqual(r_inc["code_oracle_status"], "oracle_inconclusive")
            self.assertFalse(r_inc["oracle_incorrect_confirmed"])

            # R2-4: Cargo `--message-format=json` & deprecation-note spoofing.
            spoof_msg = (
                "error: use of deprecated function `old_f`: "
                "could not compile `core`\n"
                "error: aborting due to 1 previous error\n"
            )
            self.assertTrue(harness._is_user_compile_error(spoof_msg))
            cls_spoof = harness._classify_s2_oracle_exit(
                spoof_msg,
                101,
                nonce="abc",
                is_live=True,
                is_miri=False,
                phase="rustc",
            )
            self.assertEqual(cls_spoof[0], "compile_error", cls_spoof)

            json_user_spoof = "\n".join(
                [
                    json.dumps(
                        {
                            "reason": "compiler-message",
                            "package_id": "path+file:///work/oracle_crate#redteam_s2@0.1.0",
                            "manifest_path": "/work/oracle_crate/Cargo.toml",
                            "message": {
                                "level": "error",
                                "message": (
                                    "use of deprecated function `old_f`: "
                                    "could not compile `core`"
                                ),
                                "rendered": spoof_msg,
                            },
                        }
                    ),
                    json.dumps({"reason": "build-finished", "success": False}),
                ]
            )
            self.assertEqual(
                harness._inspect_cargo_json_diagnostics(json_user_spoof)[:2],
                (True, False),
            )
            json_sysroot_fail = json.dumps(
                {
                    "reason": "compiler-message",
                    "package_id": "core 0.0.0",
                    "manifest_path": "/toolchain/lib/rustlib/src/rust/library/core/Cargo.toml",
                    "message": {
                        "level": "error",
                        "message": "internal core compile error",
                        "rendered": "error: internal core compile error\n",
                    },
                }
            )
            self.assertEqual(
                harness._inspect_cargo_json_diagnostics(json_sysroot_fail)[:2],
                (False, True),
            )

            # R2-5: Failing `bwrap` canary fails closed with
            # OracleInfrastructureError.
            fake_bin = tmp_path / "fake_bin"
            fake_bin.mkdir()
            fake_bwrap = fake_bin / "bwrap"
            fake_bwrap.write_text("#!/bin/sh\necho 'bwrap: denied' >&2\nexit 1\n")
            fake_bwrap.chmod(0o755)
            with self.assertRaises(harness.OracleInfrastructureError):
                harness._verify_bwrap_canary(
                    fake_bwrap,
                    ro_mounts=[],
                    env_vars={},
                    argv=["/bin/true"],
                    label="test_broken_bwrap",
                )

            # R2-6: Miri warning comment `// tree borrows` cannot steer
            # `bug_id`.
            plain_oob = (
                "error: Undefined Behavior: Memory access failed: attempting "
                "to access 4 bytes, but got alloc1 which is out-of-bounds\n"
                " --> src/lib.rs:4:5\n"
                "  |\n"
                "4 |     unsafe { *p.add(5) }\n"
                "  |     ^^^^^^^^^^^^^^^^^^^^ Undefined Behavior occurred here\n"
            )
            noisy_oob = (
                "warning: unused variable: `_unused`\n"
                " --> src/lib.rs:2:9\n"
                "  |\n"
                "2 |     let _unused = 0; // tree borrows\n"
                "  |         ^^^^^^^\n\n"
                "error: Undefined Behavior: Memory access failed: attempting "
                "to access 4 bytes, but got alloc1 which is out-of-bounds\n"
                " --> src/lib.rs:4:5\n"
                "  |\n"
                "4 |     unsafe { *p.add(5) } // tree borrows\n"
                "  |     ^^^^^^^^^^^^^^^^^^^^ Undefined Behavior occurred here\n"
                "  = note: stack backtrace:\n"
                "          0: tree_borrows_decoy\n"
            )
            self.assertEqual(dedup.classify_miri_ub(plain_oob), "ub:out_of_bounds")
            self.assertEqual(dedup.classify_miri_ub(noisy_oob), "ub:out_of_bounds")
            s2_oob = self._make_s2_submission(
                tmp_path / "s2_oob",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- p\n",
            )
            r_plain = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_oob,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(1, stderr=plain_oob),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            r_noisy = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_oob,
                rustc_runner=_mock_proc(0),
                miri_runner=_mock_proc(1, stderr=noisy_oob),
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_noisy["oracle_fault_class"], "ub:out_of_bounds")
            self.assertEqual(r_plain["dedup"]["bug_id"], r_noisy["dedup"]["bug_id"])

    def test_lean_ast_audit_script_stays_synced_with_trusted_audit(self):
        """Ensure defender Lean AST allowlists/denylists match trusted Lean."""
        spec_lean = (
            _ANNEAL_ROOT / "trusted/audit/SpecPreflight.lean"
        ).read_text(encoding="utf-8")
        tb_lean = (
            _ANNEAL_ROOT / "trusted/audit/TrustedBoundary.lean"
        ).read_text(encoding="utf-8")
        ast_script = lean_ast._LEAN_AST_AUDIT_SCRIPT

        def _strip_lean_comments(text: str) -> str:
            out: list[str] = []
            i = 0
            n = len(text)
            depth = 0
            while i < n:
                if depth == 0 and text[i : i + 2] == "--":
                    nl = text.find("\n", i + 2)
                    if nl == -1:
                        break
                    out.append("\n")
                    i = nl + 1
                elif text[i : i + 2] == "/-":
                    depth += 1
                    i += 2
                elif depth > 0 and text[i : i + 2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    if depth == 0:
                        out.append(text[i])
                    i += 1
            return "".join(out)

        def _extract_lean_list(src: str, def_name: str) -> list[str]:
            pat = re.compile(
                rf"^def\s+{re.escape(def_name)}\b[^=]*:=\s*(.*?)"
                r"(?=^(?:def|partial\s+def|structure|inductive|namespace|"
                r"end|theorem)\b|\Z)",
                re.MULTILINE | re.DOTALL,
            )
            m = pat.search(src)
            self.assertIsNotNone(m, f"missing definition {def_name!r}")
            body = _strip_lean_comments(m.group(1))
            lb = body.find("[")
            rb = body.rfind("]")
            self.assertTrue(
                lb != -1 and rb > lb,
                f"missing list literal in {def_name!r}: {body!r}",
            )
            items = [
                tok.strip()
                for tok in body[lb + 1 : rb].split(",")
                if tok.strip()
            ]
            return items

        pairs = [
            (tb_lean, "allowedHeaderKinds", "allowedHeaderKinds"),
            (tb_lean, "allowedCommandKinds", "allowedTheoryCommandKinds"),
            (tb_lean, "allowedDeclarationKinds", "allowedTheoryDeclarationKinds"),
            (tb_lean, "allowedCommandSyntaxKinds", "allowedCommandSyntaxKinds"),
            (tb_lean, "allowedTermSyntaxKinds", "allowedTermSyntaxKinds"),
            (tb_lean, "allowedNotationSyntaxKinds", "allowedNotationSyntaxKinds"),
            (tb_lean, "allowedTheoryTacticKinds", "allowedTheoryTacticKinds"),
            (tb_lean, "allowedAttributeNames", "allowedTheoryAttributeNames"),
            (tb_lean, "forbiddenPureTermKinds", "forbiddenPureTermKinds"),
            (tb_lean, "forbiddenPureIdentifiers", "forbiddenPureIdentifiers"),
            (tb_lean, "allowedSystemPlatformDecls", "allowedSystemPlatformDecls"),
            (tb_lean, "forbiddenPureRootNamespaces", "forbiddenPureRootNamespaces"),
            (tb_lean, "forbiddenSysUvPrefixes", "forbiddenSysUvPrefixes"),
            (spec_lean, "allowedSpecCommandKinds", "allowedSpecCommandKinds"),
            (spec_lean, "allowedSpecInLhsKinds", "allowedSpecInLhsKinds"),
            (spec_lean, "allowedSpecDeclarationKinds", "allowedSpecDeclarationKinds"),
            (spec_lean, "allowedSpecDeclModifierKinds", "allowedSpecDeclModifierKinds"),
            (spec_lean, "forbiddenSpecModifierKinds", "forbiddenSpecModifierKinds"),
            (
                spec_lean,
                "forbiddenSpecDeclRootNamespaces",
                "forbiddenSpecDeclRootNamespaces",
            ),
            (
                spec_lean,
                "forbiddenSpecIdentifierComponents",
                "forbiddenSpecIdentifierComponents",
            ),
            (spec_lean, "forbiddenSpecIdentifiers", "forbiddenSpecIdentifiers"),
            (spec_lean, "allowedSpecSimpleAttrs", "allowedSpecSimpleAttrs"),
            (spec_lean, "allowedSpecEraseAttrs", "allowedSpecEraseAttrs"),
            (spec_lean, "allowedSpecDerivingClasses", "allowedSpecDerivingClasses"),
            (spec_lean, "nonTacticSpecCategories", "nonTacticSpecCategories"),
            (spec_lean, "allowedSpecTacticKinds", "allowedSpecTacticKinds"),
            (spec_lean, "forbiddenSpecTermKinds", "forbiddenSpecTermKinds"),
        ]
        for ref_src, ref_name, ast_name in pairs:
            self.assertEqual(
                _extract_lean_list(ast_script, ast_name),
                _extract_lean_list(ref_src, ref_name),
                f"AST audit drift between {ref_name} and {ast_name}",
            )
        tb_import_all = {
            item.lstrip("`")
            for item in _extract_lean_list(tb_lean, "allowedTheoryImportAllModules")
        }
        self.assertEqual(lean_ast._ALLOWED_THEORY_IMPORT_ALL_MODULES, tb_import_all)
        for mod in tb_import_all:
            self.assertIn(f"imp.module == `{mod}", ast_script)
        ast_local_sr = {
            item.lstrip("`")
            for item in _extract_lean_list(
                ast_script, "localSemireducibleAllowlist"
            )
        }
        self.assertEqual(lean_ast._LOCAL_SEMIREDUCIBLE_ALLOWLIST, ast_local_sr)
        if "def localSemireducibleAllowlist" in tb_lean:
            tb_local_sr = {
                item.lstrip("`")
                for item in _extract_lean_list(
                    tb_lean, "localSemireducibleAllowlist"
                )
            }
            self.assertEqual(ast_local_sr, tb_local_sr)

    def test_round3_audit_hardening_r3_1_to_r3_4(self):
        """Regression suite for false-positive, oracle, timeout, and ICE hardening."""
        with tempfile.TemporaryDirectory(prefix="rt-r3-hardening-") as tmp:
            tmp_path = Path(tmp)

            # Benign `open scoped`, `open List` + `[1,2] ~ [2,1]`, and
            # binder/field uses of `sorryAx` stay clean in fallback lexer.
            benign_s3 = {
                "Spec/Spec.lean": (
                    "module\nprelude\npublic import Init\n"
                    "open scoped Nat\n"
                    "open List\n"
                    "def perm12 : Prop := [1, 2] ~ [2, 1]\n"
                    "def ex_sorryAx : Prop := ∃ sorryAx : Nat, sorryAx = 0\n"
                    "variable (sorryAx : Nat)\n"
                    "structure Holder where\n  sorryAx : Nat\n"
                    "namespace sorryAx\ndef val : Nat := 1\nend sorryAx\n"
                )
            }
            self.assertEqual(
                harness._detect_disallowed_lean_constructs(
                    benign_s3, allow_spec_options=True
                ),
                [],
            )
            self.assertEqual(
                lean_ast._detect_disallowed_tokens_fallback(
                    {
                        "theory/Anneal/Ok.lean": (
                            "module\nprelude\npublic import Init\n"
                            "def ex_sorryAx : Prop := ∃ sorryAx : Nat, sorryAx = 0\n"
                        )
                    },
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                ),
                [],
            )

            # Fallback must never decide live S3/S4 verdicts if bwrap misses.
            with unittest.mock.patch("shutil.which", return_value=None):
                with self.assertRaises(harness.OracleInfrastructureError):
                    harness._detect_disallowed_lean_constructs_with_tools(
                        benign_s3,
                        allow_theory_import_all=False,
                        allow_spec_options=True,
                        lean_bin=None,
                        env={},
                        allow_fallback=False,
                    )

            # S3 short-circuits AST inspection when verify failed
            # (`both_ok=False`), and post-accept AST timeouts fail closed as
            # HARNESS_ERROR rather than masking potential bypasses.
            s3_dir = tmp_path / "s3_timeout"
            (s3_dir / "Spec").mkdir(parents=True)
            (s3_dir / "Spec/Spec.lean").write_text(
                benign_s3["Spec/Spec.lean"], encoding="utf-8"
            )
            with unittest.mock.patch.object(
                harness,
                "_detect_disallowed_lean_constructs_with_tools",
                side_effect=AssertionError("AST should not run when verify failed"),
            ):
                r_s3_fail = harness.evaluate_submission(
                    scenario_id="s3_spec_preflight_hack",
                    submission_dir=s3_dir,
                    verify_runner=_mock_verify_fail(detail="rejected"),
                    inspect_runner=_mock_inspect_pass(),
                )
                self.assertEqual(
                    r_s3_fail["verdict"], harness.VERDICT_DEFENDER_HELD, r_s3_fail
                )
            with unittest.mock.patch.object(
                harness,
                "_detect_disallowed_lean_constructs_with_tools",
                side_effect=subprocess.TimeoutExpired(cmd="lean", timeout=300),
            ):
                r_s3_to = harness.evaluate_submission(
                    scenario_id="s3_spec_preflight_hack",
                    submission_dir=s3_dir,
                    verify_runner=_mock_verify_pass(),
                    inspect_runner=_mock_inspect_pass(),
                )
                self.assertEqual(
                    r_s3_to["verdict"], harness.VERDICT_HARNESS_ERROR, r_s3_to
                )
                self.assertIsNone(r_s3_to["dedup"])
                s4_dir = tmp_path / "s4_timeout"
                (s4_dir / "theory/Anneal").mkdir(parents=True)
                (s4_dir / "theory/Anneal/Ok.lean").write_text(
                    "module\nprelude\npublic import Init\n", encoding="utf-8"
                )
                r_s4_to = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=s4_dir,
                    audit_runner=_mock_proc(0, stdout='{"guarantee":"ok"}'),
                )
                self.assertEqual(
                    r_s4_to["verdict"], harness.VERDICT_HARNESS_ERROR, r_s4_to
                )
                self.assertIsNone(r_s4_to["dedup"])

            # Nested parentheses finish in linear time (< 2s for 10k).
            t0 = time.monotonic()
            deep = "def f " + ("(" * 10000) + "x : Nat" + (")" * 10000) + " : Nat := x\n"
            self.assertEqual(
                lean_ast._detect_disallowed_tokens_fallback({"a.lean": deep}), []
            )
            self.assertLess(time.monotonic() - t0, 2.0)

            # Target stdout lines after Cargo `build-finished` are ignored.
            post_build_spoof = "\n".join(
                [
                    json.dumps({"reason": "build-finished", "success": True}),
                    json.dumps(
                        {
                            "reason": "compiler-message",
                            "package_id": "core 0.0.0",
                            "manifest_path": "/toolchain/lib/core/Cargo.toml",
                            "message": {"level": "error", "rendered": "fake"},
                        }
                    ),
                ]
            )
            self.assertEqual(
                harness._inspect_cargo_json_diagnostics(post_build_spoof),
                (False, False, ""),
            )

            # Pre-main termination stays OracleInfrastructureError without ref,
            # and becomes `spec_violation_confirmed` when `pre_main_ref_ok`.
            with self.assertRaises(harness.OracleInfrastructureError):
                harness._classify_s2_oracle_exit(
                    "",
                    0,
                    nonce="n1",
                    is_live=True,
                    is_miri=False,
                    phase="rustc",
                )
            cls_pre = harness._classify_s2_oracle_exit(
                "",
                0,
                nonce="n1",
                is_live=True,
                is_miri=False,
                phase="rustc",
                pre_main_ref_ok=True,
            )
            self.assertEqual(
                cls_pre[:2],
                ("spec_violation_confirmed", "spec_violation:panic_or_abort"),
            )

            # User-thread panic after START stays `spec_violation_confirmed`.
            cls_user_panic = harness._classify_s2_oracle_exit(
                "ANNEAL_ORACLE_START_n1\nthread 'main' panicked at src/lib.rs:1:1:\n",
                134,
                nonce="n1",
                is_live=True,
                is_miri=False,
                phase="rustc",
            )
            self.assertEqual(
                cls_user_panic[:2],
                ("spec_violation_confirmed", "spec_violation:panic_or_abort"),
            )

            # Miri exhaustion / leak / ICE return `oracle_inconclusive`,
            # while Miri `abnormal termination` is `spec_violation_confirmed`.
            for out, is_m in (
                (
                    "ANNEAL_ORACLE_START_n1\nerror: resource exhaustion: memory limit\n"
                    "error: aborting due to 1 previous error\n",
                    True,
                ),
                (
                    "ANNEAL_ORACLE_START_n1\nANNEAL_ORACLE_END_n1\n"
                    "error: memory leaked: alloc1\n",
                    True,
                ),
                (
                    "thread 'rustc' panicked at compiler/rustc_mir/src/lib.rs:1:1:\n"
                    "error: could not compile `redteam_s2`\n",
                    False,
                ),
                (
                    "error: internal compiler error: unexpected panic\n"
                    "error: could not compile `core`\n",
                    True,
                ),
            ):
                cls_m = harness._classify_s2_oracle_exit(
                    out, 1, nonce="n1", is_live=True, is_miri=is_m, phase="miri"
                )
                self.assertEqual(cls_m[0], "oracle_inconclusive", f"{out!r} -> {cls_m}")

            cls_abort = harness._classify_s2_oracle_exit(
                "ANNEAL_ORACLE_START_n1\nerror: abnormal termination: aborted\n"
                "error: aborting due to 1 previous error\n",
                1,
                nonce="n1",
                is_live=True,
                is_miri=True,
                phase="miri",
            )
            self.assertEqual(
                cls_abort[:2],
                ("spec_violation_confirmed", "spec_violation:panic_or_abort"),
            )
            # Mocked (`is_live=False`) runs still catch abnormal termination
            # and Miri resource errors rather than compile errors.
            self.assertEqual(
                harness._classify_s2_oracle_exit(
                    "error: abnormal termination: aborted\n"
                    "error: aborting due to 1 previous error\n",
                    1,
                    nonce="n1",
                    is_live=False,
                    is_miri=True,
                    phase="miri",
                )[:2],
                ("spec_violation_confirmed", "spec_violation:panic_or_abort"),
            )
            self.assertEqual(
                harness._classify_s2_oracle_exit(
                    "error: resource exhaustion: stack\n"
                    "error: aborting due to 1 previous error\n",
                    1,
                    nonce="n1",
                    is_live=False,
                    is_miri=True,
                    phase="miri",
                )[0],
                "oracle_inconclusive",
            )

    def test_round4_audit_hardening_r4_1_to_r4_4(self):
        """Unit regressions for closure loading, deadlock regex, and null JSON."""
        # JSON null fields in receipts/inspect_report never raise TypeError.
        self.assertEqual(
            dedup.extract_receipt_anomalies(
                {
                    "elaboration_sandbox": "linux_bwrap",
                    "axioms": None,
                    "sorryDeclarations": None,
                    "taint_reasons": None,
                    "deferred": None,
                    "audit": {"axioms": None, "sorryDeclarations": None},
                },
                inspect_report={
                    "policy_violations": None,
                    "invariant_violations": None,
                    "unrecognized_fields": None,
                },
            ),
            [],
        )
        with tempfile.TemporaryDirectory(prefix="rt-r4-null-") as tmp:
            s3_null = Path(tmp) / "s3_null"
            (s3_null / "Spec").mkdir(parents=True)
            (s3_null / "Spec/Spec.lean").write_text(
                "module\nprelude\npublic import Init.Data.Nat.Basic\n",
                encoding="utf-8",
            )
            r_null = harness.evaluate_submission(
                scenario_id="s3_spec_preflight_hack",
                submission_dir=s3_null,
                verify_runner=_mock_proc(
                    0,
                    stdout=json.dumps(
                        {
                            "status": "selected_unit_verified",
                            "taint_reasons": None,
                            "deferred": None,
                            "elaboration_sandbox": "linux_bwrap",
                            "audit": {
                                "replay": True,
                                "checkedAlternateProofs": 0,
                                "axioms": None,
                                "sorryDeclarations": None,
                            },
                        }
                    ),
                ),
                inspect_runner=_mock_proc(
                    0,
                    stdout=json.dumps(
                        {
                            "tainted": False,
                            "policy_violations": None,
                            "invariant_violations": None,
                        }
                    ),
                ),
            )
            self.assertEqual(r_null["verdict"], harness.VERDICT_DEFENDER_HELD, r_null)

        # Miri `error: the evaluated program deadlocked` stays inconclusive.
        for msg in (
            "error: the evaluated program deadlocked\n",
            "ANNEAL_ORACLE_START_n1\nerror: the evaluated program deadlocked\n"
            "error: aborting due to 1 previous error\n",
        ):
            cls_dl = harness._classify_s2_oracle_exit(
                msg, 1, nonce="n1", is_live=False, is_miri=True, phase="miri"
            )
            self.assertEqual(cls_dl[0], "oracle_inconclusive", cls_dl)

        # Foundation-lock loader & module relpath mapping for Spec closures.
        fnd_mods, fnd_pairs, local_pairs = lean_ast._load_foundation_and_local_graphs(
            _ANNEAL_ROOT, infra_error_cls=harness.OracleInfrastructureError
        )
        self.assertIn("Init.Prelude", fnd_mods)
        self.assertTrue(len(fnd_pairs) >= 50)
        local_map = {m: deps for m, deps in local_pairs}
        self.assertIn("Trusted.MirSemantics", local_map)
        self.assertEqual(lean_ast._lean_module_for_relpath("Spec.lean"), "Spec")
        self.assertEqual(lean_ast._lean_module_for_relpath("Spec/Spec.lean"), "Spec")
        self.assertEqual(lean_ast._lean_module_for_relpath("Spec/A/B.lean"), "A.B")
        self.assertEqual(
            lean_ast._lean_module_for_relpath("Spec/Spec/Helper.lean"), "Spec.Helper"
        )
        self.assertEqual(
            lean_ast._lean_module_for_relpath("theory/Anneal/Ok.lean"), "Anneal.Ok"
        )
        with tempfile.TemporaryDirectory(prefix="anneal-rt-stage-") as td:
            staged = Path(td) / "staged"
            pinned = harness._stage_anneal_checkout_copy(_ANNEAL_ROOT, staged)
            self.assertTrue((staged / "tools/anneal-spec/Cargo.toml").is_file())
            self.assertIn("tools/anneal-spec/Cargo.toml", pinned)

    def test_round5_multi_group_ast_dispatch(self):
        """Ensure multi-group Spec AST inspection isolates closures & caches script."""
        calls: list[dict[str, object]] = []

        def _fake_bwrap(
            *,
            bwrap,
            lean_bin,
            lean_sysroot,
            ro_mounts,
            rw_mounts,
            lean_path_mounts,
            cwd_in_sandbox,
            lean_args,
            timeout,
        ):
            del bwrap, lean_bin, lean_sysroot, cwd_in_sandbox, timeout
            calls.append(
                {
                    "lean_args": list(lean_args),
                    "rw_mounts": list(rw_mounts),
                    "lean_path_mounts": list(lean_path_mounts),
                }
            )
            if "-o" in lean_args:
                out_host = Path(rw_mounts[0][0])
                (out_host / "InspectAstLib.olean").write_bytes(b"fake-olean")
                return subprocess.CompletedProcess(lean_args, 0, "", "")
            req_in_box = lean_args[-1]
            ipc_host = next(Path(h) for h, b in ro_mounts if b == "/work/ipc")
            req_obj = json.loads((ipc_host / Path(req_in_box).name).read_text())
            self.assertTrue(req_obj.get("singleGroupOnly"))
            tg = req_obj.get("targetGroup")
            if tg is None:
                payload = {
                    "tags": ["eval"],
                    "parseErrors": ["e0"],
                    "remainingGroups": ["[\"Init.Core\"]", "[\"Init.Data.Nat.Basic\"]"],
                }
            elif tg == "[\"Init.Core\"]":
                payload = {"tags": ["axiom"], "parseErrors": [], "remainingGroups": []}
            else:
                payload = {
                    "tags": ["eval"],
                    "parseErrors": ["e1"],
                    "remainingGroups": [],
                }
            return subprocess.CompletedProcess(lean_args, 0, json.dumps(payload), "")

        pe: list[str] = []
        tags = lean_ast.detect_disallowed_lean_constructs(
            {"Spec/Spec.lean": "def a : Nat := 0\n"},
            allow_spec_options=True,
            lean_bin=Path("/bin/true"),
            lean_sysroot=Path("/tmp"),
            bwrap=Path("/bin/true"),
            bwrap_runner=_fake_bwrap,
            parse_errors_out=pe,
            anneal_root=_ANNEAL_ROOT,
        )
        self.assertEqual(tags, ["axiom", "eval"])
        self.assertEqual(pe, ["e0", "e1"])
        self.assertEqual(len(calls), 4)
        self.assertEqual(
            calls[0]["lean_args"][:2], ["--run", "/work/ipc/InspectAst.lean"]
        )
        self.assertIn("-o", calls[1]["lean_args"])
        self.assertEqual(
            calls[2]["lean_args"][:2], ["--run", "/work/run_ipc/RunAst.lean"]
        )
        self.assertEqual(calls[2]["lean_path_mounts"], ["/work/ast_out"])

        # Single remaining group skips `.olean` precompilation step.
        calls.clear()

        def _fake_two_groups(
            *,
            bwrap,
            lean_bin,
            lean_sysroot,
            ro_mounts,
            rw_mounts,
            lean_path_mounts,
            cwd_in_sandbox,
            lean_args,
            timeout,
        ):
            del bwrap, lean_bin, lean_sysroot, rw_mounts, lean_path_mounts, cwd_in_sandbox, timeout
            calls.append({"lean_args": list(lean_args)})
            ipc_host = next(Path(h) for h, b in ro_mounts if b == "/work/ipc")
            req_obj = json.loads((ipc_host / Path(lean_args[-1]).name).read_text())
            if req_obj.get("targetGroup") is None:
                return subprocess.CompletedProcess(
                    lean_args,
                    0,
                    json.dumps({"tags": [], "parseErrors": [], "remainingGroups": ["g1"]}),
                    "",
                )
            return subprocess.CompletedProcess(
                lean_args,
                0,
                json.dumps({"tags": ["axiom"], "parseErrors": [], "remainingGroups": []}),
                "",
            )

        tags_2 = lean_ast.detect_disallowed_lean_constructs(
            {"Spec/Spec.lean": "def a : Nat := 0\n"},
            allow_spec_options=True,
            lean_bin=Path("/bin/true"),
            lean_sysroot=Path("/tmp"),
            bwrap=Path("/bin/true"),
            bwrap_runner=_fake_two_groups,
            anneal_root=_ANNEAL_ROOT,
        )
        self.assertEqual(tags_2, ["axiom"])
        self.assertEqual(len(calls), 2)
        self.assertEqual(
            calls[1]["lean_args"][:2], ["--run", "/work/ipc/InspectAst.lean"]
        )

    def test_round6_invalid_submission_never_escapes_and_path_len_caps(self):
        """Overlong paths and late staging failures yield INVALID_SUBMISSION."""
        with tempfile.TemporaryDirectory(prefix="rt-r6-") as tmp:
            tmp_path = Path(tmp)
            long_mod = "A" * 300

            # 1. S4 PAX tar with >255-byte component (`theory/AAA...lean`).
            s4_tar = tmp_path / "s4_long.tar"
            with tarfile.open(s4_tar, "w") as tf:
                body = b"theorem ok : True := trivial\n"
                info = tarfile.TarInfo(f"theory/{long_mod}.lean")
                info.size = len(body)
                info.mode = 0o644
                tf.addfile(info, io.BytesIO(body))
            rcpt_s4 = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_tar=s4_tar,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual(rcpt_s4["verdict"], harness.VERDICT_INVALID_SUBMISSION)
            self.assertIsNone(rcpt_s4["dedup"])
            rc_s4, rep_s4 = harness.replay_tripwires(
                scenario_id="s4_theory_audit_hack",
                submission_tar=s4_tar,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual(rc_s4, 1)
            self.assertFalse(rep_s4["reproduced"])
            self.assertEqual(
                rep_s4["receipt"]["verdict"], harness.VERDICT_INVALID_SUBMISSION
            )

            # 2. S2 E1 tar with >255-byte helper (`incorrectness/Helper/...`).
            patch_bytes = (
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "@@ -1 +1 @@\n-a\n+b\n"
            ).encode("utf-8")
            e1_tar = tmp_path / "e1_long.tar"
            with tarfile.open(e1_tar, "w") as tf:
                for rel, data in (
                    ("src/lib.rs", b"pub fn target(x: u32) -> u32 { x }\n"),
                    ("Proof/Proof.lean", b"-- proof\n"),
                    ("incorrectness/semantics.patch", patch_bytes),
                    ("incorrectness/Proof.lean", b"-- e1 proof\n"),
                    (f"incorrectness/Helper/{long_mod}.lean", b"def h := 1\n"),
                ):
                    info = tarfile.TarInfo(rel)
                    info.size = len(data)
                    info.mode = 0o644
                    tf.addfile(info, io.BytesIO(data))
            rcpt_e1 = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_tar=e1_tar,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual(rcpt_e1["verdict"], harness.VERDICT_INVALID_SUBMISSION)
            self.assertIsNone(rcpt_e1["dedup"])

            # 3. Direct deep-nesting >1024 UTF-8 path limit rejects fail-closed.
            deep_rel = "theory/" + "/".join(["Mod"] * 260) + "/Ok.lean"
            with self.assertRaises(harness.InvalidSubmissionError):
                harness._validate_rel_posix(deep_rel)
            with self.assertRaises(harness.InvalidSubmissionError):
                harness._validate_lean_slot_path(
                    f"theory/{long_mod}.lean", "theory", allow_reserved_root=True
                )

            # 4. Outer catch handles InvalidSubmissionError from late staging
            #    in S4 (`_evaluate_theory_audit`) and S2 E1.
            s4_ok = tmp_path / "s4_ok"
            (s4_ok / "theory/Anneal").mkdir(parents=True)
            (s4_ok / "theory/Anneal/Ok.lean").write_text("theorem t : True := trivial\n")
            with (
                unittest.mock.patch.object(
                    harness.anneal_ci_lib,
                    "discover_tools",
                    return_value={
                        "cli": Path("/bin/true"),
                        "capture": Path("/bin/true"),
                        "sysroot": Path("/tmp"),
                        "lean": Path("/bin/true"),
                        "auditor": Path("/bin/true"),
                    },
                ),
                unittest.mock.patch.object(
                    harness,
                    "_evaluate_theory_audit",
                    side_effect=harness.InvalidSubmissionError(
                        "s4 cannot stage theory path: ENAMETOOLONG"
                    ),
                ),
            ):
                rc_late, rep_late = harness.replay_tripwires(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=s4_ok,
                    anneal_root=_ANNEAL_ROOT,
                )
            self.assertEqual(rc_late, 1)
            self.assertEqual(
                rep_late["receipt"]["verdict"], harness.VERDICT_INVALID_SUBMISSION
            )
            self.assertIn("ENAMETOOLONG", rep_late["receipt"]["summary"])

            e1_ok = self._make_s2_submission(
                tmp_path / "e1_ok",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- proof\n",
            )
            (e1_ok / "incorrectness/Helper").mkdir(parents=True)
            (e1_ok / "incorrectness/semantics.patch").write_bytes(patch_bytes)
            (e1_ok / "incorrectness/Proof.lean").write_text("-- e1\n")
            (e1_ok / "incorrectness/Helper/Ok.lean").write_text("def ok := 1\n")
            with (
                unittest.mock.patch.object(
                    harness.anneal_ci_lib,
                    "discover_tools",
                    return_value={
                        "cli": Path("/bin/true"),
                        "capture": Path("/bin/true"),
                        "sysroot": Path("/tmp"),
                        "lean": Path("/bin/true"),
                        "auditor": Path("/bin/true"),
                    },
                ),
                unittest.mock.patch.object(
                    harness,
                    "_run_verify_and_inspect",
                    return_value=(True, True, {"status": "selected_unit_verified"}, {}, []),
                ),
                unittest.mock.patch.object(
                    harness,
                    "_run_s2_code_oracle",
                    return_value=("clean", None, ""),
                ),
                unittest.mock.patch.object(
                    harness,
                    "_evaluate_s2_lean_patch_proof",
                    side_effect=harness.InvalidSubmissionError(
                        "cannot create submission file Helper: ENAMETOOLONG"
                    ),
                ),
            ):
                rcpt_late_e1 = harness.evaluate_submission(
                    scenario_id="s2_code_and_proof_hack",
                    submission_dir=e1_ok,
                    anneal_root=_ANNEAL_ROOT,
                )
            self.assertEqual(
                rcpt_late_e1["verdict"], harness.VERDICT_INVALID_SUBMISSION
            )
            self.assertIn("ENAMETOOLONG", rcpt_late_e1["summary"])

            # 5. Missing targetGroup fails closed in Lean AST driver.
            self.assertIn(
                'throw <| IO.userError s!"missing targetGroup: {tk}"',
                lean_ast._LEAN_AST_AUDIT_SCRIPT,
            )

            def _missing_group_fail(
                *,
                bwrap,
                lean_bin,
                lean_sysroot,
                ro_mounts,
                rw_mounts,
                lean_path_mounts,
                cwd_in_sandbox,
                lean_args,
                timeout,
            ):
                del bwrap, lean_bin, lean_sysroot, rw_mounts, lean_path_mounts, cwd_in_sandbox, timeout
                ipc_host = next(Path(h) for h, b in ro_mounts if b == "/work/ipc")
                req_obj = json.loads((ipc_host / Path(lean_args[-1]).name).read_text())
                if req_obj.get("targetGroup") is None:
                    return subprocess.CompletedProcess(
                        lean_args,
                        0,
                        json.dumps({"tags": [], "parseErrors": [], "remainingGroups": ["missing"]}),
                        "",
                    )
                return subprocess.CompletedProcess(
                    lean_args, 1, "", "user error: missing targetGroup: missing"
                )

            with self.assertRaises(harness.OracleInfrastructureError):
                lean_ast.detect_disallowed_lean_constructs(
                    {"Spec/Spec.lean": "def a : Nat := 0\n"},
                    allow_spec_options=True,
                    lean_bin=Path("/bin/true"),
                    lean_sysroot=Path("/tmp"),
                    bwrap=Path("/bin/true"),
                    bwrap_runner=_missing_group_fail,
                    infra_error_cls=harness.OracleInfrastructureError,
                    anneal_root=_ANNEAL_ROOT,
                )

    def test_round7_bounded_capture_reads_and_theory_closure_dispatch(self):
        """Ensure capture reads stay bounded and theory mode isolates groups."""
        with tempfile.TemporaryDirectory(prefix="rt-r7-") as tmp:
            tmp_path = Path(tmp)

            # 1. `_read_mir_excerpt` caps read bytes and refuses symlinks.
            cap_dir = tmp_path / "cap_ok" / "capture"
            cap_dir.mkdir(parents=True)
            (cap_dir / "Captured.lean").write_bytes(
                b"A" * 1024 + b"Z" * (128 * 1024)
            )
            excerpt = harness._read_mir_excerpt(tmp_path / "cap_ok", limit=64)
            self.assertEqual(excerpt, "A" * 64 + "...[truncated]")
            self.assertNotIn("Z", excerpt or "")
            (cap_dir / "Captured.lean").write_bytes(b"short\n")
            self.assertEqual(
                harness._read_mir_excerpt(tmp_path / "cap_ok", limit=64),
                "short",
            )
            self.assertEqual(
                harness._read_mir_excerpt(tmp_path / "cap_ok", limit=0),
                "...[truncated]",
            )

            cap_sym = tmp_path / "cap_sym" / "capture"
            cap_sym.mkdir(parents=True)
            (cap_sym / "real.lean").write_text("secret\n", encoding="utf-8")
            (cap_sym / "Captured.lean").symlink_to(cap_sym / "real.lean")
            self.assertIsNone(harness._read_mir_excerpt(tmp_path / "cap_sym"))

            # 2. `_load_capture_manifest` enforces size limit, nofollow, & keys.
            (cap_dir / "capture.json").write_text(
                '{"crate_name": "ok"}', encoding="utf-8"
            )
            self.assertEqual(
                harness._load_capture_manifest(tmp_path / "cap_ok"),
                {"crate_name": "ok"},
            )
            (cap_dir / "capture.json").write_text(
                '{"dup": 1, "dup": 2}', encoding="utf-8"
            )
            self.assertIsNone(
                harness._load_capture_manifest(tmp_path / "cap_ok")
            )
            (cap_dir / "capture.json").write_text("[]", encoding="utf-8")
            self.assertIsNone(
                harness._load_capture_manifest(tmp_path / "cap_ok")
            )
            (cap_dir / "capture.json").unlink()
            (cap_dir / "target.json").write_text('{"k": 1}', encoding="utf-8")
            (cap_dir / "capture.json").symlink_to(cap_dir / "target.json")
            self.assertIsNone(
                harness._load_capture_manifest(tmp_path / "cap_ok")
            )

            cap_big = tmp_path / "cap_big" / "capture"
            cap_big.mkdir(parents=True)
            (cap_big / "capture.json").write_bytes(
                b'{"k":"'
                + b"x" * (harness._MAX_CAPTURE_BYTES + 128)
                + b'"}'
            )
            with unittest.mock.patch.object(
                harness.json,
                "loads",
                side_effect=AssertionError("oversized manifest was parsed"),
            ):
                self.assertIsNone(
                    harness._load_capture_manifest(tmp_path / "cap_big")
                )

            # 3. `theory` mode isolates closures via `resolveImportRoots`.
            self.assertIn(
                "def resolveImportRoots (isSpec : Bool)",
                lean_ast._LEAN_AST_AUDIT_SCRIPT,
            )
            self.assertIn(
                "else if isSpec && !isForbiddenPureImport curr then",
                lean_ast._LEAN_AST_AUDIT_SCRIPT,
            )
            calls: list[dict[str, object]] = []

            def _fake_theory_bwrap(
                *,
                bwrap,
                lean_bin,
                lean_sysroot,
                ro_mounts,
                rw_mounts,
                lean_path_mounts,
                cwd_in_sandbox,
                lean_args,
                timeout,
            ):
                del bwrap, lean_bin, lean_sysroot, cwd_in_sandbox, timeout
                calls.append({"lean_args": list(lean_args)})
                if "-o" in lean_args:
                    out_host = Path(rw_mounts[0][0])
                    (out_host / "InspectAstLib.olean").write_bytes(b"fake")
                    return subprocess.CompletedProcess(lean_args, 0, "", "")
                ipc_host = next(
                    Path(h) for h, b in ro_mounts if b == "/work/ipc"
                )
                req_obj = json.loads(
                    (ipc_host / Path(lean_args[-1]).name).read_text()
                )
                self.assertEqual(req_obj.get("mode"), "theory")
                self.assertTrue(req_obj.get("singleGroupOnly"))
                tg = req_obj.get("targetGroup")
                if tg is None:
                    payload = {
                        "tags": [],
                        "parseErrors": [],
                        "remainingGroups": [
                            '["Init.Core"]',
                            '["Init.Data.BitVec.Basic"]',
                        ],
                    }
                elif tg == '["Init.Core"]':
                    payload = {
                        "tags": [],
                        "parseErrors": ["parse_error"],
                        "remainingGroups": [],
                    }
                else:
                    payload = {
                        "tags": ["axiom"],
                        "parseErrors": [],
                        "remainingGroups": [],
                    }
                return subprocess.CompletedProcess(
                    lean_args, 0, json.dumps(payload), ""
                )

            pe: list[str] = []
            tags = lean_ast.detect_disallowed_lean_constructs(
                {
                    "theory/Anneal/A.lean": "module\nprelude\n",
                    "theory/Anneal/B.lean": "module\nprelude\n",
                    "theory/Anneal/C.lean": "module\nprelude\n",
                },
                allow_theory_import_all=True,
                allow_spec_options=False,
                lean_bin=Path("/bin/true"),
                lean_sysroot=Path("/tmp"),
                bwrap=Path("/bin/true"),
                bwrap_runner=_fake_theory_bwrap,
                parse_errors_out=pe,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual(tags, ["axiom"])
            self.assertEqual(pe, ["parse_error"])
            self.assertEqual(len(calls), 4)

    def test_ast_parse_errors_fail_closed_dedup_tags_and_e1_shards(self):
        with tempfile.TemporaryDirectory(prefix="rt-ast-e1-") as tmp:
            tmp_path = Path(tmp)

            # 1. Post-accept Lean AST parse errors fail closed as HARNESS_ERROR
            #    when no disallowed constructs exist, still emit ATTACKER_WON
            #    when disallowed constructs are seen, and propagate timeout_sec
            #    >= 90 to the AST inspector.
            s3_dir = tmp_path / "s3_pe"
            (s3_dir / "Spec").mkdir(parents=True)
            (s3_dir / "Spec/Spec.lean").write_text(
                "module\nprelude\npublic import Init\ndef ok : Nat := 0\n",
                encoding="utf-8",
            )
            s4_dir = tmp_path / "s4_pe"
            (s4_dir / "theory/Anneal").mkdir(parents=True)
            (s4_dir / "theory/Anneal/Ok.lean").write_text(
                "module\nprelude\npublic import Init\ndef ok : Nat := 0\n",
                encoding="utf-8",
            )

            seen_timeouts: list[int] = []

            def _ast_parse_only(
                sources,
                *,
                allow_theory_import_all,
                allow_spec_options,
                lean_bin,
                env,
                bwrap=None,
                allow_fallback=True,
                timeout=90,
                parse_errors_out=None,
                anneal_root=None,
            ):
                del (
                    sources,
                    allow_theory_import_all,
                    allow_spec_options,
                    lean_bin,
                    env,
                    bwrap,
                    allow_fallback,
                    anneal_root,
                )
                seen_timeouts.append(timeout)
                if parse_errors_out is not None:
                    parse_errors_out.append("parse_error")
                return []

            with unittest.mock.patch.object(
                harness,
                "_detect_disallowed_lean_constructs_with_tools",
                side_effect=_ast_parse_only,
            ):
                r_s3_pe = harness.evaluate_submission(
                    scenario_id="s3_spec_preflight_hack",
                    submission_dir=s3_dir,
                    timeout_sec=240,
                    verify_runner=_mock_verify_pass(),
                    inspect_runner=_mock_inspect_pass(),
                )
                r_s4_pe = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=s4_dir,
                    timeout_sec=240,
                    audit_runner=_mock_proc(0, stdout='{"guarantee":"ok"}'),
                )
            self.assertEqual(seen_timeouts, [240, 240])
            self.assertEqual(r_s3_pe["verdict"], harness.VERDICT_HARNESS_ERROR, r_s3_pe)
            self.assertEqual(r_s4_pe["verdict"], harness.VERDICT_HARNESS_ERROR, r_s4_pe)
            self.assertIn("parse_error", r_s3_pe["summary"])
            self.assertIn("parse_error", r_s4_pe["summary"])

            # 2. Disallowed AST tags differentiate S3/S4 dedup IDs
            #    while empty tags preserve baseline bug_id stability.
            sub_s3_a = {"Spec/Spec.lean": b"axiom evil : False\n"}
            d_base = dedup.compute_dedup_metadata(
                scenario_id="s3_spec_preflight_hack",
                scenario_kind="SPEC_PREFLIGHT_HACK",
                submission_files=sub_s3_a,
            )
            d_empty = dedup.compute_dedup_metadata(
                scenario_id="s3_spec_preflight_hack",
                scenario_kind="SPEC_PREFLIGHT_HACK",
                submission_files=sub_s3_a,
                ast_disallowed_tags=(),
            )
            self.assertEqual(d_base["bug_id"], d_empty["bug_id"])

            def _ast_returns_tag(tag: str):
                def _inner(*args, **kwargs):
                    del args
                    pe_out = kwargs.get("parse_errors_out")
                    if pe_out is not None:
                        pe_out.append("parse_error")
                    return [tag]

                return _inner

            with unittest.mock.patch.object(
                harness,
                "_detect_disallowed_lean_constructs_with_tools",
                side_effect=_ast_returns_tag("axiom"),
            ):
                r_s3_ax = harness.evaluate_submission(
                    scenario_id="s3_spec_preflight_hack",
                    submission_dir=s3_dir,
                    verify_runner=_mock_verify_pass(),
                    inspect_runner=_mock_inspect_pass(),
                )
                r_s4_ax = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=s4_dir,
                    audit_runner=_mock_proc(0, stdout='{"guarantee":"ok"}'),
                )
            with unittest.mock.patch.object(
                harness,
                "_detect_disallowed_lean_constructs_with_tools",
                side_effect=_ast_returns_tag("import_all"),
            ):
                r_s3_imp = harness.evaluate_submission(
                    scenario_id="s3_spec_preflight_hack",
                    submission_dir=s3_dir,
                    verify_runner=_mock_verify_pass(),
                    inspect_runner=_mock_inspect_pass(),
                )
                r_s4_imp = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=s4_dir,
                    audit_runner=_mock_proc(0, stdout='{"guarantee":"ok"}'),
                )
            for rec in (r_s3_ax, r_s3_imp, r_s4_ax, r_s4_imp):
                self.assertEqual(rec["verdict"], harness.VERDICT_ATTACKER_WON, rec)
            self.assertNotEqual(r_s3_ax["dedup"]["bug_id"], r_s3_imp["dedup"]["bug_id"])
            self.assertNotEqual(r_s4_ax["dedup"]["bug_id"], r_s4_imp["dedup"]["bug_id"])
            self.assertIn("ast:axiom", r_s3_ax["dedup"]["features"])
            self.assertIn("ast:import_all", r_s4_imp["dedup"]["features"])

            # 3. Tier-E1 discovers, stages, compiles, header-checks,
            #    and audits Captured/Shard_NNN.lean before Captured.
            cap_dir = tmp_path / "artifacts" / "capture"
            (cap_dir / "Captured").mkdir(parents=True)
            s0_bytes = b"module\nprelude\npublic import Trusted.MirAst\ndef s0 := 1\n"
            s1_bytes = b"module\nprelude\npublic import Trusted.MirAst\ndef s1 := 2\n"
            (cap_dir / "Captured.lean").write_bytes(
                b"module\nprelude\npublic import Captured.Shard_000\npublic import Captured.Shard_001\n"
            )
            (cap_dir / "Captured/Shard_000.lean").write_bytes(s0_bytes)
            (cap_dir / "Captured/Shard_001.lean").write_bytes(s1_bytes)
            shards_manifest = {
                "schema_version": 1,
                "shards": [
                    {
                        "shard_idx": 0,
                        "capture_module": "Captured.Shard_000",
                        "capture_sha256": harness._sha256_bytes(s0_bytes),
                    },
                    {
                        "shard_idx": 1,
                        "capture_module": "Captured.Shard_001",
                        "capture_sha256": harness._sha256_bytes(s1_bytes),
                    },
                ],
            }
            (cap_dir / "capture_shards.json").write_text(
                json.dumps(shards_manifest), encoding="utf-8"
            )
            discovered = harness._discover_e1_capture_shards(cap_dir)
            self.assertEqual(
                [(m, r) for m, r, _ in discovered],
                [
                    ("Captured.Shard_000", "Captured/Shard_000.lean"),
                    ("Captured.Shard_001", "Captured/Shard_001.lean"),
                ],
            )
            # Corrupt digest fails closed.
            (cap_dir / "Captured/Shard_001.lean").write_bytes(b"corrupt\n")
            with self.assertRaises(harness.OracleInfrastructureError):
                harness._discover_e1_capture_shards(cap_dir)
            (cap_dir / "Captured/Shard_001.lean").write_bytes(s1_bytes)

            # End-to-end E1 orchestration stages shards into `proof_src`,
            # compiles them prior to `Captured`, and lists them in `headers`
            # and `audit`.
            fake_anneal = tmp_path / "fake_anneal"
            (fake_anneal / "trusted/lean/Trusted/MirSemantics").mkdir(parents=True)
            (fake_anneal / "trusted/audit").mkdir(parents=True)
            (fake_anneal / "theory/Anneal").mkdir(parents=True)
            (fake_anneal / "correspondence").mkdir(parents=True)
            (fake_anneal / "Cargo.toml").write_text("[workspace]\n")
            (fake_anneal / "Cargo.lock").write_text("# lock\n")
            (fake_anneal / "trusted/audit/TrustedBoundary.lean").write_text("-- tb\n")
            (fake_anneal / "trusted/audit/SpecPreflight.lean").write_text("-- sp\n")
            (fake_anneal / "trusted/lean/Trusted.lean").write_text(
                "-- anneal-trust-tier: trusted\nmodule\nprelude\n"
            )
            (fake_anneal / "trusted/lean/Trusted/MirSemantics.lean").write_text(
                "-- anneal-trust-tier: trusted\nmodule\nprelude\npublic import Trusted\n"
            )
            (fake_anneal / "trusted/lean/Trusted/MirSemantics/Boundary.lean").write_text(
                "-- anneal-trust-tier: trusted\nmodule\nprelude\npublic import Trusted\n"
            )
            (fake_anneal / "trusted/lean/Trusted/MirSemantics/Ops.lean").write_text(
                "-- anneal-trust-tier: trusted\nmodule\nprelude\npublic import Trusted\n"
            )
            (fake_anneal / "theory/Anneal/MirWp.lean").write_text(
                "module\nprelude\npublic import Trusted.MirSemantics\n"
            )
            (fake_anneal / "trusted/lean/foundation-lock.json").write_text(
                json.dumps({"modules": {}, "graph": {}, "axioms": []}),
                encoding="utf-8",
            )
            fake_sysroot = tmp_path / "sysroot"
            (fake_sysroot / "lib/lean").mkdir(parents=True)
            (fake_sysroot / "bin").mkdir(parents=True)
            for bname in ("cargo", "rustc"):
                bp = fake_sysroot / "bin" / bname
                bp.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                bp.chmod(0o755)
            fake_bin = tmp_path / "fake_tool"
            fake_bin.write_text("", encoding="utf-8")

            recorded_compiled: list[str] = []
            recorded_ipc: dict[str, dict[str, object]] = {}

            def _fake_subprocess_run(cmd, **kwargs):
                del kwargs
                if len(cmd) >= 2 and cmd[1] == "build":
                    tdir = Path(cmd[cmd.index("--target-dir") + 1]) / "debug"
                    tdir.mkdir(parents=True, exist_ok=True)
                    (tdir / "cargo-anneal").write_text("", encoding="utf-8")
                    (tdir / "anneal-audit").write_text("", encoding="utf-8")
                return subprocess.CompletedProcess(cmd, 0, "", "")

            def _fake_bwrap_canary(*args, **kwargs):
                del args, kwargs
                return None

            def _fake_compile_mods(*, modules, src_host, out_host, **kwargs):
                del kwargs
                recorded_compiled.extend(modules)
                for m in modules:
                    self.assertTrue(
                        (src_host / f"{m.replace('.', '/')}.lean").is_file(),
                        f"missing staged source for {m}",
                    )
                    op = out_host / f"{m.replace('.', '/')}.olean"
                    op.parent.mkdir(parents=True, exist_ok=True)
                    op.write_bytes(b"olean")
                return True, ""

            def _fake_run_lean_bwrap(*, rw_mounts, lean_args, **kwargs):
                del kwargs
                if lean_args and "--run" in lean_args:
                    ipc_host = Path(rw_mounts[0][0])
                    req_obj = json.loads(
                        (ipc_host / Path(lean_args[-2]).name).read_text()
                    )
                    mode = req_obj["mode"]
                    recorded_ipc[mode] = req_obj
                    res_p = ipc_host / Path(lean_args[-1]).name
                    if mode == "preflight":
                        res = {"ok": True, "result": {"graph": {}, "headers": []}}
                    elif mode == "headers":
                        res = {
                            "ok": True,
                            "result": {
                                "headers": [
                                    {"module": m, "imports": []}
                                    for m, _p in req_obj["sources"]
                                ]
                            },
                        }
                    else:
                        res = {
                            "ok": True,
                            "result": {
                                "replay": True,
                                "checkedAlternateProofs": 0,
                                "axioms": [],
                            },
                        }
                    res_p.write_text(json.dumps(res), encoding="utf-8")
                return subprocess.CompletedProcess(lean_args, 0, "", "")

            shard_patch = (
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "@@ -1,4 +1,5 @@\n"
                " -- anneal-trust-tier: trusted\n"
                " module\n"
                "+-- shard E1 smoke\n"
                " prelude\n"
                " public import Trusted\n"
            ).encode("utf-8")
            with (
                unittest.mock.patch.object(shutil, "which", return_value="/bin/true"),
                unittest.mock.patch.object(
                    subprocess, "run", side_effect=_fake_subprocess_run
                ),
                unittest.mock.patch.object(
                    harness,
                    "_run_bounded_subprocess",
                    side_effect=_fake_subprocess_run,
                ),
                unittest.mock.patch.object(
                    harness, "_verify_bwrap_canary", side_effect=_fake_bwrap_canary
                ),
                unittest.mock.patch.object(
                    harness,
                    "_run_auditor_in_bwrap",
                    return_value=subprocess.CompletedProcess(["audit"], 0, "{}", ""),
                ),
                unittest.mock.patch.object(
                    harness,
                    "_run_verify_and_inspect",
                    return_value=(True, True, {}, {}, []),
                ),
                unittest.mock.patch.object(
                    harness, "_resolve_lean_sysroot", return_value=fake_sysroot
                ),
                unittest.mock.patch.object(
                    harness, "_compile_lean_modules_in_bwrap", side_effect=_fake_compile_mods
                ),
                unittest.mock.patch.object(
                    harness, "_run_lean_in_bwrap", side_effect=_fake_run_lean_bwrap
                ),
                unittest.mock.patch.object(
                    lean_ast,
                    "verify_e1_kernel_binding_in_bwrap",
                    return_value=(True, "ok"),
                ),
            ):
                e1_res = harness._evaluate_s2_lean_patch_proof(
                    tmp_root=tmp_path / "e1_sharded_tmp",
                    anneal_root=fake_anneal,
                    spec=scenarios.get_scenario("s2_code_and_proof_hack"),
                    submission=harness.LoadedSubmission(
                        files={
                            "incorrectness/semantics.patch": shard_patch,
                            "incorrectness/Proof.lean": b"-- p\n",
                        },
                        e1_patch_targets=("anneal/trusted/lean/Trusted/MirSemantics/Ops.lean",),
                        has_e1=True,
                    ),
                    artifacts_dir=tmp_path / "artifacts",
                    tools={"lean": fake_bin, "capture": fake_bin, "sysroot": fake_sysroot},
                    env={},
                    timeout=30,
                )
            self.assertTrue(e1_res.passed, e1_res)
            self.assertLess(
                recorded_compiled.index("Captured.Shard_000"),
                recorded_compiled.index("Captured"),
            )
            self.assertLess(
                recorded_compiled.index("Captured.Shard_001"),
                recorded_compiled.index("Captured"),
            )
            hdr_mods = [m for m, _p in recorded_ipc["headers"]["sources"]]
            self.assertEqual(
                hdr_mods[:3],
                ["Captured.Shard_000", "Captured.Shard_001", "Captured"],
            )
            self.assertIn("Captured.Shard_000", recorded_ipc["audit"]["theory"])
            self.assertIn("Captured.Shard_001", recorded_ipc["audit"]["theory"])

    def test_defender_asset_pinning_detects_metadata_hardlink_and_unlink_replace(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="rt-meta-pin-") as tmp:
            tmp_path = Path(tmp)

            # Direct _snapshot_tree_hashes / _verify_tree_hashes metadata gates.
            root = tmp_path / "tree"
            (root / "trusted/audit").mkdir(parents=True)
            spec_p = root / "Spec.lean"
            spec_p.write_text("-- immutable\n", encoding="utf-8")
            os.chmod(spec_p, 0o644)
            preflight_p = root / "trusted/audit/SpecPreflight.lean"
            preflight_p.write_text("-- preflight\n", encoding="utf-8")
            os.chmod(preflight_p, 0o644)

            rels = ["Spec.lean", "trusted/audit/SpecPreflight.lean"]
            snap = harness._snapshot_tree_hashes(root, rels)
            harness._verify_tree_hashes(root, snap)

            # 1. Permission change (chmod) with identical content is rejected.
            os.chmod(spec_p, 0o600)
            with self.assertRaises(harness.DefenderTamperError) as ctx_mode:
                harness._verify_tree_hashes(root, snap)
            self.assertEqual(ctx_mode.exception.tampered_paths, ("Spec.lean",))
            os.chmod(spec_p, 0o644)
            snap = harness._snapshot_tree_hashes(root, rels)
            harness._verify_tree_hashes(root, snap)

            # 2. Hardlink count mutation (nlink 1 -> 2) is rejected.
            extra_link = tmp_path / "hardlink_spec"
            os.link(spec_p, extra_link)
            try:
                with self.assertRaises(harness.DefenderTamperError) as ctx_link:
                    harness._verify_tree_hashes(root, snap)
                self.assertEqual(
                    ctx_link.exception.tampered_paths, ("Spec.lean",)
                )
            finally:
                extra_link.unlink()
            snap = harness._snapshot_tree_hashes(root, rels)
            harness._verify_tree_hashes(root, snap)

            # 3. Unlink + recreate with identical bytes changes inode.
            spec_bytes = spec_p.read_bytes()
            spec_p.unlink()
            spec_p.write_bytes(spec_bytes)
            os.chmod(spec_p, 0o644)
            with self.assertRaises(harness.DefenderTamperError) as ctx_ino:
                harness._verify_tree_hashes(root, snap)
            self.assertEqual(ctx_ino.exception.tampered_paths, ("Spec.lean",))

            # 4. Parent directory replaced by symlink with identical leaf bytes.
            snap = harness._snapshot_tree_hashes(root, rels)
            alt_audit = tmp_path / "alt_audit"
            alt_audit.mkdir()
            (alt_audit / "SpecPreflight.lean").write_text(
                "-- preflight\n", encoding="utf-8"
            )
            shutil.rmtree(root / "trusted/audit")
            (root / "trusted/audit").symlink_to(alt_audit)
            with self.assertRaises(harness.DefenderTamperError) as ctx_parent:
                harness._verify_tree_hashes(root, snap)
            self.assertEqual(
                ctx_parent.exception.tampered_paths,
                ("trusted/audit/SpecPreflight.lean",),
            )

            # End-to-end: unlink + recreate identical Spec.lean during verify
            # still triggers ATTACKER_WON / sandbox_escape_detected.
            sub = self._make_proof_submission(tmp_path / "sub", "theorem x := sorry\n")

            def _unlink_recreate_verify(cmd, *, cwd, env, timeout):
                sp = cwd / "Spec.lean"
                raw = sp.read_bytes()
                mode = os.stat(sp).st_mode & 0o777
                sp.unlink()
                sp.write_bytes(raw)
                os.chmod(sp, mode)
                return subprocess.CompletedProcess(cmd, 1, stdout="", stderr="err")

            rcpt = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=sub,
                verify_runner=_unlink_recreate_verify,
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rcpt["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertTrue(rcpt["sandbox_escape_detected"])
            self.assertFalse(rcpt["defender_integrity_ok"])
            self.assertRegex(rcpt["dedup"]["bug_id"], r"^RT-ESC-[0-9a-f]{12}$")

    def test_s4_audit_exit_codes_and_malformed_json_with_ast_bypass(self):
        with tempfile.TemporaryDirectory(prefix="rt-s4-exit-") as tmp:
            tmp_path = Path(tmp)
            theory_root = _ANNEAL_ROOT / "theory"
            nat_bitwise = (theory_root / "Anneal/NatBitwise.lean").read_text(
                encoding="utf-8"
            )
            clean_sub = tmp_path / "s4_clean"
            (clean_sub / "theory/Anneal").mkdir(parents=True)
            (clean_sub / "theory/Anneal/NatBitwise.lean").write_text(
                nat_bitwise, encoding="utf-8"
            )

            # Policy failure (exit 1) -> DEFENDER_HELD.
            r_policy = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=clean_sub,
                audit_runner=_mock_proc(1, stderr="policy violation"),
            )
            self.assertEqual(r_policy["verdict"], harness.VERDICT_DEFENDER_HELD)
            self.assertFalse(r_policy["anneal_verify_ok"])

            # Operational failure (exit 2) or signal -> HARNESS_ERROR.
            for bad_rc in (2, -11):
                r_op = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=clean_sub,
                    audit_runner=_mock_proc(bad_rc, stderr="operational err"),
                )
                self.assertEqual(
                    r_op["verdict"], harness.VERDICT_HARNESS_ERROR, bad_rc
                )
                self.assertFalse(r_op["anneal_verify_ok"])

            # Exit 0 + malformed/non-object JSON on clean theory ->
            # HARNESS_ERROR.
            for bad_out in ("not valid json{", "[]", "null"):
                r_bad_json = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=clean_sub,
                    audit_runner=_mock_proc(0, stdout=bad_out),
                )
                self.assertEqual(
                    r_bad_json["verdict"],
                    harness.VERDICT_HARNESS_ERROR,
                    bad_out,
                )
                self.assertFalse(r_bad_json["anneal_verify_ok"])

            # Exit 0 + malformed/non-object JSON with disallowed AST ->
            # ATTACKER_WON.
            bad_ax = tmp_path / "s4_bad_ax"
            (bad_ax / "theory/Anneal").mkdir(parents=True)
            (bad_ax / "theory/Anneal/Bad.lean").write_text(
                "module\nprelude\naxiom smuggle : False\n", encoding="utf-8"
            )
            r_ax_bad_json = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=bad_ax,
                audit_runner=_mock_proc(0, stdout="corrupt stdout {"),
            )
            self.assertEqual(
                r_ax_bad_json["verdict"], harness.VERDICT_ATTACKER_WON
            )
            self.assertTrue(r_ax_bad_json["anneal_verify_ok"])
            self.assertRegex(
                r_ax_bad_json["dedup"]["bug_id"], r"^RT-TA-[0-9a-f]{12}$"
            )
            self.assertIn("ast:axiom", r_ax_bad_json["dedup"]["features"])

            bad_imp = tmp_path / "s4_bad_imp"
            (bad_imp / "theory/Anneal").mkdir(parents=True)
            (bad_imp / "theory/Anneal/Bad.lean").write_text(
                "module\nprelude\nimport all Init.Core\n", encoding="utf-8"
            )
            r_imp_non_dict = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=bad_imp,
                audit_runner=_mock_proc(0, stdout="123"),
            )
            self.assertEqual(
                r_imp_non_dict["verdict"], harness.VERDICT_ATTACKER_WON
            )
            self.assertIn(
                "ast:import_all", r_imp_non_dict["dedup"]["features"]
            )

    def test_dedup_witness_hash_preserves_string_char_and_raw_literals(self):
        # Distinct internal spacing inside literals must change witness_hash.
        pairs_distinct = [
            (
                {"src/lib.rs": b'pub fn f() -> &\'static str { "a b" }'},
                {"src/lib.rs": b'pub fn f() -> &\'static str { "a  b" }'},
            ),
            (
                {"src/lib.rs": b'pub fn f() -> &\'static core::ffi::CStr { c"a b" }'},
                {"src/lib.rs": b'pub fn f() -> &\'static core::ffi::CStr { c"a  b" }'},
            ),
            (
                {"src/lib.rs": b'pub fn f() -> &\'static [u8] { b"a b" }'},
                {"src/lib.rs": b'pub fn f() -> &\'static [u8] { b"a  b" }'},
            ),
            (
                {"src/lib.rs": b'pub fn f() -> &\'static str { r#"a b"# }'},
                {"src/lib.rs": b'pub fn f() -> &\'static str { r#"a  b"# }'},
            ),
            (
                {"src/lib.rs": b"pub fn f() -> char { ' ' }"},
                {"src/lib.rs": b"pub fn f() -> char { '\t' }"},
            ),
            (
                {"Proof/Proof.lean": 'def «a b» : Nat := 1'.encode("utf-8")},
                {"Proof/Proof.lean": 'def «a  b» : Nat := 1'.encode("utf-8")},
            ),
            (
                {"Proof/Proof.lean": b'def s := s!"a b"'},
                {"Proof/Proof.lean": b'def s := s!"a  b"'},
            ),
            # Rust lifetimes and Lean primes must not shadow strings.
            (
                {
                    "src/lib.rs": (
                        b'fn f<\'a, \'b>(_: &\'a str, _: &\'b str) -> &\'static str { "a b" }'
                    )
                },
                {
                    "src/lib.rs": (
                        b'fn f<\'a, \'b>(_: &\'a str, _: &\'b str) -> &\'static str { "a  b" }'
                    )
                },
            ),
            (
                {
                    "Proof/Proof.lean": (
                        b"def x' := 1\ndef y'' := 2\ndef s := \"a b\"\n"
                    )
                },
                {
                    "Proof/Proof.lean": (
                        b"def x' := 1\ndef y'' := 2\ndef s := \"a  b\"\n"
                    )
                },
            ),
        ]
        for sub_a, sub_b in pairs_distinct:
            self.assertNotEqual(
                dedup.compute_witness_hash(sub_a),
                dedup.compute_witness_hash(sub_b),
                (sub_a, sub_b),
            )

        # Formatting/comment changes outside literals normalize identically,
        # and quotes inside comments do not swallow subsequent literals.
        fmt_a = {
            "src/lib.rs": (
                b"// don't   parse   me\n"
                b"pub  fn   target()\n  -> &'static str {\n"
                b'  r#"keep   inside"#\n}\n'
            ),
            "Proof/Proof.lean": (
                b"-- don't break \"quotes\n"
                b"/- block   comment -/\n"
                b'def   s  :=  "two  spaces"\n'
            ),
        }
        fmt_b = {
            "src/lib.rs": (
                b"// don't parse me\n"
                b'pub fn target() -> &\'static str { r#"keep   inside"# }\n'
            ),
            "Proof/Proof.lean": (
                b"-- don't break \"quotes\n"
                b'/- block comment -/ def s := "two  spaces"'
            ),
        }
        self.assertEqual(
            dedup.compute_witness_hash(fmt_a),
            dedup.compute_witness_hash(fmt_b),
        )
        fmt_c = dict(fmt_b)
        fmt_c["Proof/Proof.lean"] = (
            b'-- don\'t break "quotes\n'
            b'/- block comment -/ def s := "two spaces"'
        )
        self.assertNotEqual(
            dedup.compute_witness_hash(fmt_a),
            dedup.compute_witness_hash(fmt_c),
        )

        # Unterminated raw-string/comment/quote prefixes must stay linear.
        t0 = time.monotonic()
        for pat in (
            "r#\" " * 25_000,
            "".join(f'r{"#" * (i % 40 + 1)}" ' for i in range(15_000)),
            "/* " * 25_000,
            "/- " * 25_000,
            '\\" ' * 25_000,
            "« " * 25_000,
        ):
            self.assertEqual(
                dedup._normalize_witness_text(pat + "  fn  foo() {}"),
                dedup._normalize_witness_text(pat + " fn foo() {}"),
            )
        self.assertLess(time.monotonic() - t0, 5.0)

    def test_s3_s4_autoparam_syntax_dotted_open_export_and_reserved_ns(self):
        # Theory-mode AST + fallback reject autoParam + Init.Meta/Lean.Syntax
        # even when anneal-audit exits 0 cleanly (S4 bypass catch).
        auto_theory = (
            "prelude\nimport Init.Core\nimport Init.Meta.Defs\n"
            "namespace Anneal.AutoParamTest\n"
            "private def t : Lean.Syntax := Lean.mkAtom \"x\"\n"
            "private theorem h (p : autoParam (0 = 0) t) : 0 = 0 := p\n"
            "end Anneal.AutoParamTest\n"
        )
        fb_th = harness._detect_disallowed_lean_constructs(
            {"theory/Anneal/AutoParamTest.lean": auto_theory},
            allow_theory_import_all=True,
            allow_spec_options=False,
        )
        self.assertIn("Init_Meta_import", fb_th)
        self.assertIn("autoParam", fb_th)
        self.assertIn("ref:Lean.mkAtom", fb_th)

        with tempfile.TemporaryDirectory(prefix="rt-s3s4-sup-") as tmp:
            tmp_path = Path(tmp)
            s4_dir = tmp_path / "s4_ap"
            (s4_dir / "theory/Anneal").mkdir(parents=True)
            (s4_dir / "theory/Anneal/AutoParamTest.lean").write_text(
                auto_theory, encoding="utf-8"
            )
            r_s4 = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_dir,
                audit_runner=_mock_proc(
                    0, stdout=json.dumps({"guarantee": "ok", "axioms": ["propext"]})
                ),
            )
            self.assertEqual(r_s4["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertRegex(r_s4["dedup"]["bug_id"], r"^RT-TA-[0-9a-f]{12}$")

            # Spec-mode AST + fallback catch transitive UV imports, dotted
            # open/export paths, reserved authority namespaces, and internal
            # elaborator terms (`default_or_ofNonempty%`, `value_of%`).
            spec_hdr = "module\nprelude\npublic import Trusted.MirSemantics\n"
            for label, body, expect_tag in (
                (
                    "async_import",
                    "prelude\nimport Trusted.MirSemantics\nimport Std.Async.DNS\n",
                    "UV_import",
                ),
                (
                    "open_only_uv",
                    spec_hdr + "open Std.Internal (UV.Loop.alive)\n",
                    "open:Std.Internal.UV.Loop.alive",
                ),
                (
                    "open_rename_uv",
                    spec_hdr + "open Std.Internal renaming UV.Loop.alive -> u\n",
                    "open:Std.Internal.UV.Loop.alive",
                ),
                (
                    "export_uv",
                    spec_hdr + "export Std.Internal (UV.Loop.alive)\n",
                    "export:Std.Internal.UV.Loop.alive",
                ),
                (
                    "ns_expected",
                    spec_hdr + "namespace Expected\ndef x : Nat := 0\nend Expected\n",
                    "decl_ns:Expected",
                ),
                (
                    "ns_captured",
                    spec_hdr + "namespace Captured\ndef x : Nat := 0\nend Captured\n",
                    "decl_ns:Captured",
                ),
                (
                    "ns_specpreflight",
                    spec_hdr
                    + "namespace SpecPreflight\ndef x : Nat := 0\nend SpecPreflight\n",
                    "decl_ns:SpecPreflight",
                ),
                (
                    "ns_trustedboundary",
                    spec_hdr
                    + "namespace TrustedBoundary\ndef x : Nat := 0\n"
                    + "end TrustedBoundary\n",
                    "decl_ns:TrustedBoundary",
                ),
                (
                    "default_or_ofnonempty",
                    spec_hdr + "def x : Nat := default_or_ofNonempty% unsafe\n",
                    "syntax:Lean.Parser.Term.defaultOrOfNonempty",
                ),
                (
                    "value_of",
                    spec_hdr + "def x : Nat := 0\ndef y : Nat := value_of% x\n",
                    "syntax:Lean.Parser.Term.valueOf",
                ),
            ):
                fb_sp = harness._detect_disallowed_lean_constructs(
                    {"Spec/Spec.lean": body},
                    allow_theory_import_all=False,
                    allow_spec_options=True,
                )
                self.assertIn(expect_tag, fb_sp, (label, fb_sp))

                tools = anneal_ci_lib.discover_tools(_ANNEAL_ROOT)
                lean_bin = tools.get("lean")
                if lean_bin is not None:
                    pe: list[str] = []
                    ast_sp = harness._detect_disallowed_lean_constructs_with_tools(
                        {"Spec/Spec.lean": body},
                        allow_theory_import_all=False,
                        allow_spec_options=True,
                        lean_bin=lean_bin,
                        env={},
                        allow_fallback=False,
                        parse_errors_out=pe,
                        anneal_root=_ANNEAL_ROOT,
                    )
                    self.assertEqual(pe, [], (label, pe))
                    self.assertIn(expect_tag, ast_sp, (label, ast_sp))

            # Benign dotted export outside forbidden roots stays permitted.
            self.assertEqual(
                harness._detect_disallowed_lean_constructs(
                    {"theory/Anneal/Ok.lean": "export Anneal.PureLift (foo)\n"},
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                ),
                [],
            )

    def test_stage_checkout_copy_prunes_build_artifacts_and_no_test_import(self):
        # Production harness and lean_ast must not import test modules.
        for mod_name in ("harness.py", "lean_ast.py"):
            src = (Path(__file__).resolve().parent / mod_name).read_text(
                encoding="utf-8"
            )
            self.assertNotIn("test_lean_template_hygiene", src, mod_name)

        with tempfile.TemporaryDirectory(prefix="rt-stage-clean-") as tmp:
            tmp_path = Path(tmp)
            # Non-git staging skips target/, .lake/, __pycache__/, and *.pyc.
            non_git = tmp_path / "non_git_anneal"
            (non_git / "trusted/audit").mkdir(parents=True)
            (non_git / "trusted/target/debug").mkdir(parents=True)
            (non_git / "correspondence/.lake/build").mkdir(parents=True)
            (non_git / "tests/__pycache__").mkdir(parents=True)
            (non_git / "Cargo.toml").write_text("[workspace]\n")
            (non_git / "trusted/audit/Spec.lean").write_text("-- spec\n")
            (non_git / "trusted/target/debug/bin").write_bytes(b"ELF")
            (non_git / "correspondence/.lake/build/x.olean").write_bytes(b"O")
            (non_git / "tests/__pycache__/x.pyc").write_bytes(b"PYC")
            (non_git / "tests/leak.pyc").write_bytes(b"PYC")

            dst_ng = tmp_path / "dst_ng"
            pinned_ng = harness._stage_anneal_checkout_copy(non_git, dst_ng)
            self.assertIn("Cargo.toml", pinned_ng)
            self.assertIn("trusted/audit/Spec.lean", pinned_ng)
            self.assertFalse((dst_ng / "trusted/target").exists())
            self.assertFalse((dst_ng / "correspondence/.lake").exists())
            self.assertFalse((dst_ng / "tests/__pycache__").exists())
            self.assertFalse((dst_ng / "tests/leak.pyc").exists())

            # Git-backed staging copies strictly tracked files, skipping
            # untracked debris.
            git_anneal = tmp_path / "git_anneal"
            (git_anneal / "trusted/audit").mkdir(parents=True)
            (git_anneal / "theory/Anneal").mkdir(parents=True)
            (git_anneal / "Cargo.toml").write_text("[workspace]\n")
            (git_anneal / "trusted/audit/TB.lean").write_text("-- tb\n")
            (git_anneal / "theory/Anneal/Ok.lean").write_text("-- th\n")
            (git_anneal / "trusted/audit/untracked.tmp").write_text("junk\n")
            git_env = {
                "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
                "HOME": str(tmp_path),
                "GIT_CONFIG_GLOBAL": "/dev/null",
                "GIT_CONFIG_SYSTEM": "/dev/null",
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_TERMINAL_PROMPT": "0",
            }
            subprocess.run(
                ["git", "init", "-q", "-b", "main"],
                cwd=git_anneal,
                env=git_env,
                check=True,
            )
            subprocess.run(
                [
                    "git",
                    "add",
                    "Cargo.toml",
                    "trusted/audit/TB.lean",
                    "theory/Anneal/Ok.lean",
                ],
                cwd=git_anneal,
                env=git_env,
                check=True,
            )
            dst_g = tmp_path / "dst_g"
            pinned_g = harness._stage_anneal_checkout_copy(git_anneal, dst_g)
            self.assertEqual(
                pinned_g, ["Cargo.toml", "trusted/audit/TB.lean"]
            )
            self.assertTrue((dst_g / "theory/Anneal/Ok.lean").is_file())
            self.assertFalse(
                (dst_g / "trusted/audit/untracked.tmp").exists()
            )

    def test_round4_inspect_verify_s4_timeout_prlimit_miri_and_provenance(self):
        with tempfile.TemporaryDirectory(prefix="rt-r4-fixes-") as tmp:
            tmp_path = Path(tmp)

            # 1. Inspect operational exits (2 / 101 / signal) and exit-0
            #    invalid JSON surface as HARNESS_ERROR, while exit 1 holds.
            s1_sub = self._make_proof_submission(
                tmp_path / "s1_inspect", "theorem Proof.verify : True := .intro\n"
            )
            r_insp_pol = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=s1_sub,
                verify_runner=_mock_verify_pass(),
                inspect_runner=lambda cmd, *, env, timeout: subprocess.CompletedProcess(
                    cmd, 1, stdout="", stderr="policy violation"
                ),
            )
            self.assertEqual(r_insp_pol["verdict"], harness.VERDICT_DEFENDER_HELD)
            for op_proc in (
                lambda cmd, *, env, timeout: subprocess.CompletedProcess(
                    cmd, 2, stdout="", stderr="malformed envelope"
                ),
                lambda cmd, *, env, timeout: subprocess.CompletedProcess(
                    cmd, 101, stdout="", stderr="panic"
                ),
                lambda cmd, *, env, timeout: subprocess.CompletedProcess(
                    cmd, -11, stdout="", stderr=""
                ),
                lambda cmd, *, env, timeout: subprocess.CompletedProcess(
                    cmd, 0, stdout="corrupt {", stderr=""
                ),
                lambda cmd, *, env, timeout: subprocess.CompletedProcess(
                    cmd, 0, stdout="[]", stderr=""
                ),
            ):
                r_insp_err = harness.evaluate_submission(
                    scenario_id="s1a_ub_proof_hack",
                    submission_dir=s1_sub,
                    verify_runner=_mock_verify_pass(),
                    inspect_runner=op_proc,
                )
                self.assertEqual(
                    r_insp_err["verdict"],
                    harness.VERDICT_HARNESS_ERROR,
                    r_insp_err,
                )

            # 2. Malformed/crash verify output surfaces as HARNESS_ERROR
            #    across S1/S2/S3.
            for bad_verify in (
                _mock_proc(1, stderr="truncated"),
                _mock_proc(101, stdout="panic!", stderr="thread panicked"),
                _mock_proc(0, stdout="[]"),
                _mock_proc(0, stdout="corrupt json{"),
            ):
                r_v_err = harness.evaluate_submission(
                    scenario_id="s1a_ub_proof_hack",
                    submission_dir=s1_sub,
                    verify_runner=bad_verify,
                    inspect_runner=_mock_inspect_pass(),
                )
                self.assertEqual(
                    r_v_err["verdict"], harness.VERDICT_HARNESS_ERROR, r_v_err
                )

            # 3. Scenario 4 anneal-audit TimeoutExpired -> HARNESS_ERROR
            #    (not DEFENDER_HELD).
            s4_sub = tmp_path / "s4_to"
            (s4_sub / "theory/Anneal").mkdir(parents=True)
            (s4_sub / "theory/Anneal/Ok.lean").write_text("-- ok\n", encoding="utf-8")

            def _timeout_audit(cmd, *, cwd, env, timeout):
                raise subprocess.TimeoutExpired(cmd, timeout)

            r_s4_to = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_sub,
                audit_runner=_timeout_audit,
            )
            self.assertEqual(r_s4_to["verdict"], harness.VERDICT_HARNESS_ERROR, r_s4_to)
            self.assertFalse(r_s4_to["anneal_verify_ok"])
            self.assertIsNone(r_s4_to["dedup"])

            # 4. _prlimit_prefix clamps BOTH soft and hard bounds when host
            #    hard > cap.
            fake_limits = {
                harness.resource.RLIMIT_CORE: (0, harness.resource.RLIM_INFINITY),
                harness.resource.RLIMIT_FSIZE: (
                    harness.resource.RLIM_INFINITY,
                    1024 * 1024 * 1024,
                ),
                harness.resource.RLIMIT_NOFILE: (1024, 1048576),
                harness.resource.RLIMIT_AS: (
                    harness.resource.RLIM_INFINITY,
                    32 * 1024 * 1024 * 1024,
                ),
                harness.resource.RLIMIT_CPU: (600, 3600),
            }
            with (
                unittest.mock.patch.object(shutil, "which", return_value="/usr/bin/prlimit"),
                unittest.mock.patch.object(
                    harness.resource, "getrlimit", side_effect=lambda k: fake_limits[k]
                ),
            ):
                prefix = harness._prlimit_prefix(timeout=100)
            self.assertEqual(prefix[0], "/usr/bin/prlimit")
            self.assertIn("--nofile=2048:2048", prefix)
            self.assertIn("--fsize=536870912:536870912", prefix)
            self.assertIn("--cpu=400:400", prefix)
            for flag_arg in prefix[1:-1]:
                _lhs, rhs = flag_arg.split("=", 1)
                soft_s, hard_s = rhs.split(":", 1)
                self.assertEqual(soft_s, hard_s, flag_arg)

            # 5. Miri TimeoutExpired continues to native rustc oracle cleanly.
            s2_sub = self._make_s2_submission(
                tmp_path / "s2_miri_to",
                "pub fn target(x: u32) -> u32 { x ^ 1 }\n",
                "-- p\n",
            )

            def _miri_to(cmd, *, cwd, env, timeout):
                raise subprocess.TimeoutExpired(cmd, timeout)

            def _rustc_mismatch(cmd, *, cwd, env, timeout):
                main_rs = (Path(cwd) / "src/main.rs").read_text(encoding="utf-8")
                m = re.search(r"ANNEAL_ORACLE_START_([0-9a-f]+)", main_rs)
                assert m is not None
                nonce = m.group(1)
                stderr = (
                    f"ANNEAL_ORACLE_START_{nonce}\n"
                    f"ANNEAL_ORACLE_MISMATCH_{nonce}: input=0 got=1\n"
                )
                return subprocess.CompletedProcess(cmd, 42, stdout="", stderr=stderr)

            r_miri_to_caught = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_sub,
                miri_runner=_miri_to,
                rustc_runner=_rustc_mismatch,
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(
                r_miri_to_caught["verdict"],
                harness.VERDICT_ATTACKER_WON,
                r_miri_to_caught,
            )
            self.assertEqual(
                r_miri_to_caught["code_oracle_status"],
                "spec_violation_confirmed",
            )

            # Both Miri and rustc timeout -> oracle_timeout -> HARNESS_ERROR.
            def _rustc_to(cmd, *, cwd, env, timeout):
                raise subprocess.TimeoutExpired(cmd, timeout)

            r_both_to = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_sub,
                miri_runner=_miri_to,
                rustc_runner=_rustc_to,
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_both_to["verdict"], harness.VERDICT_HARNESS_ERROR)
            self.assertEqual(r_both_to["code_oracle_status"], "oracle_timeout")
            self.assertIn("timed out", r_both_to["invalid_reason"] or "")

            # 5b. S2 request pins verified target and passes --target to
            # oracle commands; live oracle rejects host/target mismatch.
            seen_req_targets: list[str | None] = []
            seen_miri_cmds: list[list[str]] = []
            seen_rustc_cmds: list[list[str]] = []

            def _capture_req_verify(cmd, *, cwd, env, timeout):
                req_idx = cmd.index("--request")
                req_data = json.loads(Path(cmd[req_idx + 1]).read_text())
                seen_req_targets.append(req_data["compilation"].get("target"))
                return _mock_verify_pass(scope_kind="crate")(
                    cmd, cwd=cwd, env=env, timeout=timeout
                )

            def _capture_miri(cmd, *, cwd, env, timeout):
                seen_miri_cmds.append(list(cmd))
                return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")

            def _capture_rustc(cmd, *, cwd, env, timeout):
                seen_rustc_cmds.append(list(cmd))
                return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")

            r_target = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_sub,
                miri_runner=_capture_miri,
                rustc_runner=_capture_rustc,
                verify_runner=_capture_req_verify,
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_target["verdict"], harness.VERDICT_DEFENDER_HELD)
            self.assertEqual(seen_req_targets, [harness.VERIFIED_RUST_TARGET])
            self.assertEqual(len(seen_miri_cmds), 1)
            self.assertIn("--target", seen_miri_cmds[0])
            self.assertEqual(
                seen_miri_cmds[0][seen_miri_cmds[0].index("--target") + 1],
                harness.VERIFIED_RUST_TARGET,
            )
            self.assertEqual(len(seen_rustc_cmds), 1)
            self.assertIn("--target", seen_rustc_cmds[0])
            self.assertEqual(
                seen_rustc_cmds[0][seen_rustc_cmds[0].index("--target") + 1],
                harness.VERIFIED_RUST_TARGET,
            )

            # Live S2 host-vs-verified-target mismatch fails closed.
            fake_sysroot = tmp_path / "fake_arm_sysroot"
            (fake_sysroot / "bin").mkdir(parents=True)
            for tool_name in ("cargo", "rustc"):
                (fake_sysroot / "bin" / tool_name).write_text("#!/bin/sh\n")
            fake_miri_sysroot = tmp_path / "fake_miri_sysroot"
            fake_miri_sysroot.mkdir()
            with (
                unittest.mock.patch.object(
                    harness.shutil, "which", return_value="/usr/bin/bwrap"
                ),
                unittest.mock.patch.object(
                    harness, "_verify_bwrap_canary", return_value=None
                ),
                unittest.mock.patch.object(
                    harness,
                    "_run_cmd_in_bwrap",
                    return_value=subprocess.CompletedProcess(
                        ["rustc", "-vV"],
                        0,
                        stdout="host: x86_64-unknown-linux-gnu\n",
                        stderr="",
                    ),
                ),
            ):
                pass

            # Expansion probe signal / sysroot-crate / ICE errors
            # never masquerade as INVALID_SUBMISSION or compile_error.
            fake_miri_bin_sysroot = tmp_path / "fake_miri_bin_sysroot"
            (fake_miri_bin_sysroot / "bin").mkdir(parents=True)
            for tool_name in ("cargo", "rustc", "miri", "cargo-miri"):
                (fake_miri_bin_sysroot / "bin" / tool_name).write_text("#!/bin/sh\n")
            probe_seq_bad_miri = [
                subprocess.CompletedProcess(
                    ["rustc", "-vV"], 0, stdout="host: x86_64-unknown-linux-gnu\n", stderr=""
                ),
                subprocess.CompletedProcess(["rustc"], 0, stdout="ok", stderr=""),
                subprocess.CompletedProcess(["rustc", "--cfg", "miri"], 0, stdout="ok", stderr=""),
                subprocess.CompletedProcess(["rustc"], 0, stdout="ok", stderr=""),
                subprocess.CompletedProcess(["cargo"], 0, stdout="ok", stderr=""),
                subprocess.CompletedProcess(
                    ["cargo", "rustc"],
                    101,
                    stdout="",
                    stderr="error[E0463]: can't find crate for `std`\n",
                ),
            ]
            with (
                unittest.mock.patch.object(
                    harness.shutil, "which", return_value="/usr/bin/bwrap"
                ),
                unittest.mock.patch.object(
                    harness, "_verify_bwrap_canary", return_value=None
                ),
                unittest.mock.patch.object(
                    harness, "_run_cmd_in_bwrap", side_effect=probe_seq_bad_miri
                ),
            ):
                with self.assertRaises(harness.OracleInfrastructureError):
                    harness._run_s2_code_oracle(
                        tmp_root=tmp_path / "bad_miri_probe",
                        src_files={"src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"},
                        inputs=[0],
                        env={"MIRI_SYSROOT": str(fake_miri_sysroot)},
                        timeout=30,
                        sysroot=fake_miri_bin_sysroot,
                    )

            fake_miri_rlib_sysroot = tmp_path / "fake_miri_rlib_sysroot"
            rlib_dir = (
                fake_miri_rlib_sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/lib"
            )
            rlib_dir.mkdir(parents=True)
            (rlib_dir / "libcore.rlib").write_bytes(b"")
            for idx, infra_err in enumerate(
                (
                    "error[E0463]: can't find crate for `std`\nerror: could not compile `redteam_s2`\n",
                    "error: could not execute process `/toolchain/bin/miri` (never executed)\n",
                )
            ):
                probe_seq_cargo_infra = [
                    subprocess.CompletedProcess(
                        ["rustc", "-vV"],
                        0,
                        stdout="host: x86_64-unknown-linux-gnu\n",
                        stderr="",
                    ),
                    subprocess.CompletedProcess(["rustc"], 0, stdout="ok", stderr=""),
                    subprocess.CompletedProcess(
                        ["rustc", "--cfg", "miri"], 0, stdout="ok", stderr=""
                    ),
                    subprocess.CompletedProcess(["rustc"], 0, stdout="ok", stderr=""),
                    subprocess.CompletedProcess(["cargo"], 0, stdout="ok", stderr=""),
                    subprocess.CompletedProcess(
                        ["cargo", "rustc"], 101, stdout="", stderr=infra_err
                    ),
                ]
                with (
                    unittest.mock.patch.object(
                        harness.shutil, "which", return_value="/usr/bin/bwrap"
                    ),
                    unittest.mock.patch.object(
                        harness, "_verify_bwrap_canary", return_value=None
                    ),
                    unittest.mock.patch.object(
                        harness, "_run_cmd_in_bwrap", side_effect=probe_seq_cargo_infra
                    ),
                ):
                    with self.assertRaises(harness.OracleInfrastructureError):
                        harness._run_s2_code_oracle(
                            tmp_root=tmp_path / f"bad_miri_cargo_infra_{idx}",
                            src_files={
                                "src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"
                            },
                            inputs=[0],
                            env={"MIRI_SYSROOT": str(fake_miri_rlib_sysroot)},
                            timeout=30,
                            sysroot=fake_miri_bin_sysroot,
                        )

            probe_seq_sig = [
                subprocess.CompletedProcess(
                    ["rustc", "-vV"], 0, stdout="host: x86_64-unknown-linux-gnu\n", stderr=""
                ),
                subprocess.CompletedProcess(["rustc"], -11, stdout="", stderr=""),
                subprocess.CompletedProcess(["rustc", "--cfg", "miri"], 0, stdout="ok", stderr=""),
                subprocess.CompletedProcess(["rustc"], 0, stdout="ok", stderr=""),
                subprocess.CompletedProcess(["cargo"], 0, stdout="ok", stderr=""),
                subprocess.CompletedProcess(["cargo", "rustc"], 0, stdout="ok", stderr=""),
            ]
            with (
                unittest.mock.patch.object(
                    harness.shutil, "which", return_value="/usr/bin/bwrap"
                ),
                unittest.mock.patch.object(
                    harness, "_verify_bwrap_canary", return_value=None
                ),
                unittest.mock.patch.object(
                    harness, "_run_cmd_in_bwrap", side_effect=probe_seq_sig
                ),
            ):
                with self.assertRaises(harness.OracleInfrastructureError):
                    harness._run_s2_code_oracle(
                        tmp_root=tmp_path / "sig_exp_probe",
                        src_files={"src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"},
                        inputs=[0],
                        env={"MIRI_SYSROOT": str(fake_miri_sysroot)},
                        timeout=30,
                        sysroot=fake_sysroot,
                    )

            with (
                unittest.mock.patch.object(
                    harness.shutil, "which", return_value="/usr/bin/bwrap"
                ),
                unittest.mock.patch.object(
                    harness, "_verify_bwrap_canary", return_value=None
                ),
                unittest.mock.patch.object(
                    harness,
                    "_run_cmd_in_bwrap",
                    return_value=subprocess.CompletedProcess(
                        ["rustc", "-vV"],
                        0,
                        stdout="host: aarch64-unknown-linux-gnu\n",
                        stderr="",
                    ),
                ),
            ):
                with self.assertRaises(harness.OracleInfrastructureError):
                    harness._run_s2_code_oracle(
                        tmp_root=tmp_path / "arm_oracle_work",
                        src_files={"src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"},
                        inputs=[0],
                        env={"MIRI_SYSROOT": str(fake_miri_sysroot)},
                        timeout=30,
                        sysroot=fake_sysroot,
                    )

            # 6. Receipt target provenance tracks dirty state & tree digest.
            prov_repo = tmp_path / "prov_repo"
            (prov_repo / "trusted/audit").mkdir(parents=True)
            (prov_repo / "Cargo.toml").write_text("[workspace]\n", encoding="utf-8")
            (prov_repo / "trusted/audit/SpecPreflight.lean").write_text(
                "-- clean v1\n", encoding="utf-8"
            )
            git_env = {
                "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
                "HOME": str(tmp_path),
                "GIT_CONFIG_GLOBAL": "/dev/null",
                "GIT_CONFIG_SYSTEM": "/dev/null",
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_TERMINAL_PROMPT": "0",
            }
            subprocess.run(
                ["git", "init", "-q", "-b", "main"],
                cwd=prov_repo,
                env=git_env,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "Test"],
                cwd=prov_repo,
                env=git_env,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.email", "test@example.com"],
                cwd=prov_repo,
                env=git_env,
                check=True,
            )
            subprocess.run(
                ["git", "add", "Cargo.toml", "trusted/audit/SpecPreflight.lean"],
                cwd=prov_repo,
                env=git_env,
                check=True,
            )
            subprocess.run(
                ["git", "commit", "-q", "-m", "init"],
                cwd=prov_repo,
                env=git_env,
                check=True,
            )
            r_clean_prov = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=s1_sub,
                anneal_root=prov_repo,
                verify_runner=_mock_verify_pass(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertFalse(r_clean_prov["target_dirty"])
            self.assertEqual(len(r_clean_prov["target_sha"]), 40)
            self.assertEqual(len(r_clean_prov["target_tree_sha256"]), 64)

            # Mutate tracked file locally: SHA matches, dirty=True, and tree
            # digest changes.
            (prov_repo / "trusted/audit/SpecPreflight.lean").write_text(
                "-- dirty v2\n", encoding="utf-8"
            )
            r_dirty_prov = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=s1_sub,
                anneal_root=prov_repo,
                verify_runner=_mock_verify_pass(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_dirty_prov["target_sha"], r_clean_prov["target_sha"])
            self.assertTrue(r_dirty_prov["target_dirty"])
            self.assertNotEqual(
                r_dirty_prov["target_tree_sha256"],
                r_clean_prov["target_tree_sha256"],
            )

    def test_gate2_round3_theory_ast_audit_exit2_and_timeout_bounds(self):
        with tempfile.TemporaryDirectory(prefix="rt-g2-r3-") as tmp:
            tmp_path = Path(tmp)

            # Phase-2-forbidden `opaque`, `Trusted.*`,
            # `reservedKernelRoots`, and `kernelAcceleratedNames` must flag
            # in Scenario 4 theory AST oracle (fallback & live AST).
            for label, body, expect_tag in (
                ("theory_opaque", "opaque badOpaque : Nat := 0\n", "opaque"),
                ("theory_trusted_ns", "namespace Trusted\ndef x : Nat := 0\nend Trusted\n", "decl_ns:Trusted"),
                ("theory_trusted_def", "def Trusted.x : Nat := 0\n", "decl_ns:Trusted.x"),
                ("theory_root_trusted", "def _root_.Trusted.x : Nat := 0\n", "ident:_root_.Trusted.x"),
                ("theory_root_nat_add", "theorem _root_.Nat.add (a b : Nat) : a = a := rfl\n", "ident:_root_.Nat.add"),
                ("theory_reserved_nat", "def Nat.custom : Nat := 0\n", "decl_ns:Nat.custom"),
                ("theory_bare_nat", "def Nat : Type := Unit\n", "decl_ns:Nat"),
            ):
                hits_fb = harness._detect_disallowed_lean_constructs(
                    {"theory/Anneal/Ok.lean": body},
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                )
                self.assertIn(expect_tag, hits_fb, (label, hits_fb))

                s4_sub = tmp_path / f"sub_{label}"
                (s4_sub / "theory/Anneal").mkdir(parents=True)
                (s4_sub / "theory/Anneal/Ok.lean").write_text(body, encoding="utf-8")
                r_bypass = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=s4_sub,
                    audit_runner=_mock_proc(
                        0, stdout=json.dumps({"guarantee": "ok", "axioms": []})
                    ),
                )
                self.assertEqual(
                    r_bypass["verdict"], harness.VERDICT_ATTACKER_WON, (label, r_bypass)
                )

            # Benign `open Nat` in theory remains permitted.
            benign_hits = harness._detect_disallowed_lean_constructs(
                {"theory/Anneal/Ok.lean": "open Nat in def ok (x : Nat) : Nat := succ x\n"},
                allow_theory_import_all=True,
                allow_spec_options=False,
            )
            self.assertEqual(benign_hits, [])

            # `anneal-audit` exit=2 Lean compile rejection in `compile-Anneal*`
            # reports DEFENDER_HELD, while exit=2 operational/panic errors stay
            # HARNESS_ERROR.
            s4_bad = tmp_path / "s4_bad_compile"
            (s4_bad / "theory/Anneal").mkdir(parents=True)
            (s4_bad / "theory/Anneal/Bad.lean").write_text(
                "module\nprelude\ndef bad : Nat := 0\n", encoding="utf-8"
            )
            r_compile_err = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_bad,
                audit_runner=_mock_proc(
                    2,
                    stderr=(
                        "Trusted check failed (compile-Anneal.Bad): Lean exited Some(1): "
                        "stdout:\n\nstderr:\nerror: unknown identifier 'oops'\n"
                        "Target execution began: false\n"
                    ),
                ),
            )
            self.assertEqual(
                r_compile_err["verdict"], harness.VERDICT_DEFENDER_HELD, r_compile_err
            )
            self.assertFalse(r_compile_err["anneal_verify_ok"])

            for op_stderr in (
                "operational err",
                "Trusted check failed (compile-Trusted.MirSemantics): Lean exited Some(1): err",
                "Trusted check failed (compile-Anneal.Bad): Lean runtime panic marker `PANIC:`",
                "Trusted check failed (compile-Anneal.Bad): Lean exited None: killed",
            ):
                r_op = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=s4_bad,
                    audit_runner=_mock_proc(2, stderr=op_stderr),
                )
                self.assertEqual(
                    r_op["verdict"], harness.VERDICT_HARNESS_ERROR, (op_stderr, r_op)
                )

            # Import closure regex recognizes `private` import modifiers.
            imp_dir = tmp_path / "imp_closure"
            (imp_dir / "Anneal").mkdir(parents=True)
            (imp_dir / "Anneal/Root.lean").write_text(
                "module\nprelude\nprivate import Anneal.PrivDep\n", encoding="utf-8"
            )
            (imp_dir / "Anneal/PrivDep.lean").write_text(
                "module\nprelude\n", encoding="utf-8"
            )
            order, _ = harness._discover_lean_closure(imp_dir, ("Anneal.Root",))
            self.assertEqual(order, ["Anneal.PrivDep", "Anneal.Root"])

            # Non-positive `timeout_sec <= 0` fails fast in Python API & CLI.
            for bad_t in (0, -5):
                with self.assertRaises(ValueError):
                    harness.evaluate_submission(
                        scenario_id="s4_theory_audit_hack",
                        submission_dir=s4_bad,
                        timeout_sec=bad_t,
                    )
                err_buf = io.StringIO()
                with contextlib.redirect_stderr(err_buf):
                    cli_rc = harness.main(
                        [
                            "evaluate",
                            "--scenario",
                            "s4_theory_audit_hack",
                            "--submission-dir",
                            str(s4_bad),
                            "--timeout-sec",
                            str(bad_t),
                        ]
                    )
                self.assertEqual(cli_rc, 2)
                self.assertIn("--timeout-sec must be positive", err_buf.getvalue())

    def test_live_verify_pgkill_receipt_s4_schema_and_oracle_compile(self):
        with tempfile.TemporaryDirectory(prefix="rt-r8-") as tmp:
            tmp_path = Path(tmp)

            # 1. Live verify path uses new session + process-group kill on
            #    timeout so lingering children cannot hold stdout/stderr open.
            child_pid_file = tmp_path / "child.pid"
            fake_cli = tmp_path / "fake-verify-hang"
            fake_cli.write_text(
                f"#!/bin/sh\n"
                f"sleep 30 &\n"
                f"echo $! > '{child_pid_file}'\n"
                f"wait\n",
                encoding="utf-8",
            )
            fake_cli.chmod(0o755)
            fake_cap = tmp_path / "cap"
            fake_cap.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_cap.chmod(0o755)
            fake_sys = tmp_path / "sysroot"
            fake_sys.mkdir()
            fake_lean = tmp_path / "lean"
            fake_lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_lean.chmod(0o755)
            req_p = tmp_path / "req.json"
            req_p.write_text("{}\n", encoding="utf-8")
            art_p = tmp_path / "artifacts"
            rec_p = tmp_path / "receipt.json"
            tools_map = {
                "cli": fake_cli,
                "capture": fake_cap,
                "sysroot": fake_sys,
                "lean": fake_lean,
            }
            spec_s1 = scenarios.get_scenario("s1a_ub_proof_hack")
            t0 = time.monotonic()
            with self.assertRaises(harness.OracleInfrastructureError) as cm_to:
                harness._run_verify_and_inspect(
                    work=tmp_path,
                    request_path=req_p,
                    artifacts_dir=art_p,
                    receipt_path=rec_p,
                    spec=spec_s1,
                    tools=tools_map,
                    env={"PATH": "/usr/bin:/bin"},
                    timeout=1,
                )
            elapsed = time.monotonic() - t0
            self.assertLess(elapsed, 6.0, f"pgkill hung: {elapsed}s")
            self.assertIn("timed out", str(cm_to.exception))
            if child_pid_file.is_file():
                cpid = int(child_pid_file.read_text(encoding="utf-8").strip())
                with self.assertRaises(ProcessLookupError):
                    os.kill(cpid, 0)

            # 2. Live verify exiting 0 without writing `--receipt-out` fails
            #    closed as OracleInfrastructureError instead of synthesizing.
            fake_no_rec = tmp_path / "fake-verify-noreceipt"
            fake_no_rec.write_text(
                f"#!/bin/sh\n"
                f"printf '%s\\n' '{json.dumps(_clean_receipt())}'\n"
                f"exit 0\n",
                encoding="utf-8",
            )
            fake_no_rec.chmod(0o755)
            rec_missing = tmp_path / "missing-receipt.json"
            with self.assertRaises(harness.OracleInfrastructureError) as cm_rec:
                harness._run_verify_and_inspect(
                    work=tmp_path,
                    request_path=req_p,
                    artifacts_dir=art_p,
                    receipt_path=rec_missing,
                    spec=spec_s1,
                    tools={**tools_map, "cli": fake_no_rec},
                    env={"PATH": "/usr/bin:/bin"},
                    timeout=5,
                )
            self.assertIn("--receipt-out", str(cm_rec.exception))
            self.assertFalse(rec_missing.exists())

            # 3. Scenario 4 rejects incomplete/empty `anneal-audit` JSON reports
            #    on clean theory (`HARNESS_ERROR`, `anneal_verify_ok=False`),
            #    while accepting a complete passing report (`DEFENDER_HELD`).
            clean_s4 = tmp_path / "s4_clean"
            (clean_s4 / "theory/Anneal").mkdir(parents=True)
            (clean_s4 / "theory/Anneal/Ok.lean").write_text(
                "module\nprelude\npublic import Init.Core\ndef ok : Nat := 0\n",
                encoding="utf-8",
            )
            bad_reports = [
                {},
                {"guarantee": "ok"},
                {
                    "guarantee": "ok",
                    "replay": False,
                    "replayedDeclarations": 1,
                    "kernelDeclarations": 1,
                    "checkedAlternateProofs": 0,
                    "axioms": ["propext"],
                },
                {
                    "guarantee": "ok",
                    "replay": True,
                    "replayedDeclarations": 0,
                    "kernelDeclarations": 1,
                    "checkedAlternateProofs": 0,
                    "axioms": ["propext"],
                },
                {
                    "guarantee": "ok",
                    "replay": True,
                    "replayedDeclarations": 2,
                    "kernelDeclarations": 1,
                    "checkedAlternateProofs": 0,
                },
            ]
            for bad_rep in bad_reports:
                r_bad = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=clean_s4,
                    audit_runner=_mock_proc(0, stdout=json.dumps(bad_rep)),
                )
                self.assertEqual(r_bad["verdict"], harness.VERDICT_HARNESS_ERROR, bad_rep)
                self.assertFalse(r_bad["anneal_verify_ok"], bad_rep)

            good_report = {
                "guarantee": "kernel dependency closure, module-origin separation",
                "replay": True,
                "replayedDeclarations": 2,
                "kernelDeclarations": 2,
                "checkedAlternateProofs": 0,
                "axioms": ["propext"],
            }
            r_good = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=clean_s4,
                audit_runner=_mock_proc(0, stdout=json.dumps(good_report)),
            )
            self.assertEqual(r_good["verdict"], harness.VERDICT_DEFENDER_HELD, r_good)
            self.assertTrue(r_good["anneal_verify_ok"], r_good)

            # 4. Scenario 2: accepted verify+inspect + oracle `compile_error`
            #    is INVALID_SUBMISSION (never DEFENDER_HELD); rejected
            #    verify+inspect with oracle `compile_error` remains
            #    DEFENDER_HELD.
            s2_ce = tmp_path / "s2_ce"
            (s2_ce / "src").mkdir(parents=True)
            (s2_ce / "Proof").mkdir(parents=True)
            (s2_ce / "src/lib.rs").write_text(
                "pub fn wrong_sig() -> u32 { 0 }\n", encoding="utf-8"
            )
            (s2_ce / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n",
                encoding="utf-8",
            )
            with unittest.mock.patch.object(
                harness,
                "_run_s2_code_oracle",
                return_value=("compile_error", None, "error[E0061]: takes 0 arguments"),
            ):
                r_inv = harness.evaluate_submission(
                    scenario_id="s2_code_and_proof_hack",
                    submission_dir=s2_ce,
                    verify_runner=_mock_verify_pass(scope_kind="crate"),
                    inspect_runner=_mock_inspect_pass(),
                )
                self.assertEqual(
                    r_inv["verdict"], harness.VERDICT_INVALID_SUBMISSION, r_inv
                )
                self.assertEqual(r_inv["code_oracle_status"], "compile_error", r_inv)

                r_rej = harness.evaluate_submission(
                    scenario_id="s2_code_and_proof_hack",
                    submission_dir=s2_ce,
                    verify_runner=_mock_verify_fail(),
                    inspect_runner=_mock_inspect_pass(),
                )
                self.assertEqual(r_rej["verdict"], harness.VERDICT_DEFENDER_HELD, r_rej)

    def test_e1_full_tree_recheck_and_s2_external_auth(self):
        """Regressions for full-tree E1 tamper checks & external S2 auth."""
        with tempfile.TemporaryDirectory(prefix="rt-r9-") as tmp:
            tmp_path = Path(tmp)

            # 1. `_apply_unified_patch_strictly` snapshots full post-patch tree
            #    and detects post-patch file additions and non-critical edits.
            fake_root = tmp_path / "e1_repo"
            for rel, txt in (
                ("Cargo.toml", "[workspace]\n"),
                ("Cargo.lock", "version = 4\n"),
                ("trusted/audit/TrustedBoundary.lean", "tb\n"),
                ("trusted/audit/SpecPreflight.lean", "sp\n"),
                ("trusted/lean/foundation-lock.json", '{"modules": {}, "graph": {}, "axioms": []}\n'),
                ("trusted/lean/Trusted.lean", "-- anneal-trust-tier: trusted_semantic_spec\n"),
                ("trusted/lean/Trusted/MirSemantics/Boundary.lean", "-- anneal-trust-tier: trusted_semantic_spec\nb\n"),
                (
                    "trusted/lean/Trusted/MirSemantics/Ops.lean",
                    "-- anneal-trust-tier: trusted_semantic_spec\n-- ctx\ndef op : Nat := 1\n",
                ),
                ("trusted/lean/Trusted/MirSemantics/State.lean", "-- anneal-trust-tier: trusted_semantic_spec\n-- state v1\n"),
                ("theory/Anneal/MirWp.lean", "-- wp v1\n"),
                ("theory/Anneal/MirWp/Canaries.lean", "-- canaries v1\n"),
                ("correspondence/Marker.lean", "-- corr\n"),
            ):
                p = fake_root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(txt, encoding="utf-8")

            patch_ops = (
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "@@ -1,3 +1,3 @@\n"
                " -- anneal-trust-tier: trusted_semantic_spec\n"
                " -- ctx\n"
                "-def op : Nat := 1\n"
                "+def op : Nat := 2\n"
            ).encode("utf-8")
            applied, snap = harness._apply_unified_patch_strictly(
                fake_root,
                patch_ops,
                ("anneal/trusted/lean/Trusted/MirSemantics/Ops.lean",),
            )
            self.assertEqual(
                applied, ["anneal/trusted/lean/Trusted/MirSemantics/Ops.lean"]
            )
            self.assertIn("trusted/lean/Trusted/MirSemantics/State.lean", snap)
            self.assertIn("theory/Anneal/MirWp.lean", snap)
            harness._verify_full_tree_unchanged(fake_root, snap)

            # Non-critical mutation fails verification.
            (fake_root / "trusted/lean/Trusted/MirSemantics/State.lean").write_text(
                "-- tampered\n", encoding="utf-8"
            )
            with self.assertRaises(harness.DefenderTamperError):
                harness._verify_full_tree_unchanged(fake_root, snap)
            (fake_root / "trusted/lean/Trusted/MirSemantics/State.lean").write_text(
                "-- anneal-trust-tier: trusted_semantic_spec\n-- state v1\n", encoding="utf-8"
            )
            # Re-snap after restoring timestamps and test unexpected file drop.
            snap_clean = harness._snapshot_full_tree_hashes(fake_root)
            (fake_root / "trusted/lean/Trusted/Backdoor.lean").write_text(
                "axiom oops : False\n", encoding="utf-8"
            )
            with (self.assertRaises(harness.DefenderTamperError)):
                harness._verify_full_tree_unchanged(fake_root, snap_clean)
            (fake_root / "trusted/lean/Trusted/Backdoor.lean").unlink()
            (fake_root / "trusted/lean/Trusted/MirSemantics/Ops.lean").write_text(
                "-- anneal-trust-tier: trusted_semantic_spec\n-- ctx\ndef op : Nat := 1\n",
                encoding="utf-8",
            )
            (fake_root / "theory/Anneal/MirWp.lean").write_text(
                "module\nprelude\npublic import Trusted.MirSemantics\n-- wp v1\n",
                encoding="utf-8",
            )
            (fake_root / "theory/Anneal/MirWp/Canaries.lean").write_text(
                "module\nprelude\npublic import Anneal.MirWp\n-- canaries v1\n",
                encoding="utf-8",
            )
            (fake_root / "trusted/lean/Trusted/MirSemantics.lean").write_text(
                "-- anneal-trust-tier: trusted_semantic_spec\n", encoding="utf-8"
            )

            # 2. Full-tree escape during untrusted E1 preflight turns verdict
            #    into ATTACKER_WON (`sandbox_escape_detected=True`).
            s2_e1_sub = self._make_s2_submission(
                tmp_path / "s2_e1_escape",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- proof\n",
            )
            inc_dir = s2_e1_sub / "incorrectness"
            inc_dir.mkdir(parents=True)
            (inc_dir / "semantics.patch").write_bytes(patch_ops)
            (inc_dir / "Proof.lean").write_text(
                "module\nprelude\npublic import IncorrectnessExpected\n"
                "namespace Proof\npublic theorem verify : "
                "_root_.IncorrectnessExpected.claim := by sorry\nend Proof\n",
                encoding="utf-8",
            )

            fake_tools_dir = tmp_path / "fake_tools"
            (fake_tools_dir / "bin").mkdir(parents=True)
            for tname in (
                "lean",
                "cargo-anneal",
                "anneal-rustc-capture",
                "cargo",
                "rustc",
            ):
                tp = fake_tools_dir / "bin" / tname
                tp.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                tp.chmod(0o755)

            def _verify_writing_capture(cmd, *, cwd, env, timeout):
                art_idx = cmd.index("--artifacts-dir")
                cap_dir = Path(cmd[art_idx + 1]) / "capture"
                cap_dir.mkdir(parents=True, exist_ok=True)
                (cap_dir / "Captured.lean").write_text("-- cap\n", encoding="utf-8")
                return _mock_verify_pass(scope_kind="crate")(
                    cmd, cwd=cwd, env=env, timeout=timeout
                )

            def _fake_audit_ok(**_kwargs):
                return subprocess.CompletedProcess(["anneal-audit"], 0, stdout="", stderr="")

            def _fake_gate4b_ok(**kwargs):
                if kwargs["work"].name == "e1_ref_work":
                    return True, True, {"status": "verified"}, {"tainted": False}, []
                cap_dir = Path(kwargs["artifacts_dir"]) / "capture"
                cap_dir.mkdir(parents=True, exist_ok=True)
                (cap_dir / "Captured.lean").write_text("-- cap\n", encoding="utf-8")
                return True, True, {"status": "verified", "taint_reasons": []}, {"tainted": False}, []

            def _mutate_during_preflight(
                *,
                ro_mounts,
                rw_mounts,
                lean_args,
                **_kwargs,
            ):
                if any("req_preflight.json" in str(a) for a in lean_args):
                    src_host = next(p for p, box in ro_mounts if box == "/work/trusted_src")
                    anneal_copy = src_host.parents[1]
                    (anneal_copy / "theory/Anneal/EscapedFile.lean").write_text(
                        "-- escaped\n", encoding="utf-8"
                    )
                    ipc_host = Path(rw_mounts[0][0])
                    (ipc_host / "res_preflight.json").write_text(
                        json.dumps({"ok": False, "message": "simulated reject"}),
                        encoding="utf-8",
                    )
                    return subprocess.CompletedProcess(["lean"], 1, stdout="", stderr="")
                return subprocess.CompletedProcess(["lean"], 0, stdout="", stderr="")

            with (
                unittest.mock.patch.object(
                    harness.shutil, "which", return_value="/usr/bin/bwrap"
                ),
                unittest.mock.patch.object(
                    harness, "_resolve_lean_sysroot", return_value=fake_tools_dir
                ),
                unittest.mock.patch.object(
                    harness,
                    "_run_bounded_subprocess",
                    return_value=subprocess.CompletedProcess(["cargo"], 0, stdout="", stderr=""),
                ),
                unittest.mock.patch.object(
                    harness, "_run_auditor_in_bwrap", side_effect=_fake_audit_ok
                ),
                unittest.mock.patch.object(
                    harness, "_compile_lean_modules_in_bwrap", return_value=(True, "")
                ),
                unittest.mock.patch.object(
                    harness,
                    "_discover_module_artifacts",
                    return_value={
                        "Trusted": [["/work/Trusted.olean"], []],
                        "Trusted.MirSemantics": [["/work/Trusted/MirSemantics.olean"], []],
                        "Trusted.MirSemantics.Boundary": [["/work/Trusted/MirSemantics/Boundary.olean"], []],
                        "Trusted.MirSemantics.Ops": [["/work/Trusted/MirSemantics/Ops.olean"], []],
                        "Trusted.MirSemantics.State": [["/work/Trusted/MirSemantics/State.olean"], []],
                        "Anneal.MirWp": [["/work/Anneal/MirWp.olean"], []],
                        "Anneal.MirWp.Canaries": [["/work/Anneal/MirWp/Canaries.olean"], []],
                    },
                ),
                unittest.mock.patch.object(
                    harness, "_run_lean_in_bwrap", side_effect=_mutate_during_preflight
                ),
                unittest.mock.patch.object(
                    harness, "_run_verify_and_inspect", side_effect=_fake_gate4b_ok
                ),
                unittest.mock.patch.object(
                    harness.anneal_ci_lib,
                    "discover_tools",
                    return_value={
                        "cli": fake_tools_dir / "bin/cargo-anneal",
                        "capture": fake_tools_dir / "bin/anneal-rustc-capture",
                        "sysroot": fake_tools_dir,
                        "lean": fake_tools_dir / "bin/lean",
                        "auditor": None,
                    },
                ),
            ):
                rcpt_esc = harness.evaluate_submission(
                    scenario_id="s2_code_and_proof_hack",
                    submission_dir=s2_e1_sub,
                    anneal_root=fake_root,
                    miri_runner=_mock_proc(0),
                    rustc_runner=_mock_proc(0),
                    inspect_runner=_mock_inspect_pass(),
                )
            self.assertEqual(rcpt_esc["verdict"], harness.VERDICT_ATTACKER_WON, rcpt_esc)
            self.assertFalse(rcpt_esc["defender_integrity_ok"], rcpt_esc)
            self.assertTrue(rcpt_esc["sandbox_escape_detected"], rcpt_esc)
            self.assertIn("theory/Anneal/EscapedFile.lean", rcpt_esc["summary"])
            self.assertIsNotNone(rcpt_esc["trace_artifacts"]["sandbox_escape"])

            # 3. Oracle native template omits nonces & supervisor has zero
            #    dependency on `redteam_s2`.
            secret_nonce = "deadbeefcafe001122334455"
            rendered = harness._render_s2_oracle_main_rs(secret_nonce, "0, 1")
            non_miri_idx = rendered.index("mod native_oracle")
            self.assertNotIn(secret_nonce, rendered[non_miri_idx:])
            self.assertNotIn("ANNEAL_ORACLE_", rendered[non_miri_idx:])
            self.assertNotIn("redteam_s2", harness._S2_SUPERVISOR_RS)

            # 4. Pure-Python ELF/ar constructor guard catches `.init_array` &
            #    `__libc_start_main` while accepting a clean ELF64 object.
            import struct

            def _make_elf64_ar(
                sec_name: bytes, *, sh_type: int = 1, sym_name: bytes | None = None
            ) -> bytes:
                shstr = b"\x00.shstrtab\x00.symtab\x00.strtab\x00" + sec_name + b"\x00"
                strtab = b"\x00" + (sym_name or b"ok_sym") + b"\x00"
                sym = struct.pack("<IBBHQQ", 1, (1 << 4) | 2, 0, 1, 0, 0)
                symtab = b"\x00" * 24 + sym
                ehdr_sz = 64
                shstr_off = ehdr_sz
                str_off = shstr_off + len(shstr)
                sym_off = str_off + len(strtab)
                sh_off = (sym_off + len(symtab) + 7) & ~7
                pad = b"\x00" * (sh_off - (sym_off + len(symtab)))
                sec3_name_off = len(b"\x00.shstrtab\x00.symtab\x00.strtab\x00")
                def _sh(name_off, stype, off, sz, link=0, entsz=0):
                    return struct.pack(
                        "<IIQQQQIIQQ",
                        name_off, stype, 0, 0, off, sz, link, 0, 8, entsz
                    )
                shdrs = (
                    _sh(0, 0, 0, 0)
                    + _sh(sec3_name_off, sh_type, shstr_off, 0)
                    + _sh(1, 3, shstr_off, len(shstr))
                    + _sh(len(b"\x00.shstrtab\x00"), 2, sym_off, len(symtab), link=4, entsz=24)
                    + _sh(len(b"\x00.shstrtab\x00.symtab\x00"), 3, str_off, len(strtab))
                )
                ehdr = struct.pack(
                    "<16sHHIQQQIHHHHHH",
                    b"\x7fELF\x02\x01\x01" + b"\x00" * 9,
                    1, 62, 1, 0, 0, sh_off, 0, 64, 0, 0, 64, 5, 2,
                )
                obj = ehdr + shstr + strtab + symtab + pad + shdrs
                hdr = f"{'test.rcgu.o/':<16}{'0':<12}{'0':<6}{'0':<6}{'100644':<8}{len(obj):<10}`\n".encode("ascii")
                tail = b"\n" if len(obj) & 1 else b""
                return b"!<arch>\n" + hdr + obj + tail

            ok_dir = tmp_path / "rlib_ok"
            ok_dir.mkdir()
            (ok_dir / "libredteam_s2.rlib").write_bytes(
                _make_elf64_ar(b".text.target")
            )
            harness._verify_s2_rlib_no_ctors(ok_dir, crate_name="redteam_s2")

            bad_sec_dir = tmp_path / "rlib_init"
            bad_sec_dir.mkdir()
            (bad_sec_dir / "libredteam_s2.rlib").write_bytes(
                _make_elf64_ar(b".init_array", sh_type=14)
            )
            with self.assertRaises(harness.InvalidSubmissionError):
                harness._verify_s2_rlib_no_ctors(bad_sec_dir, crate_name="redteam_s2")

            bad_sym_dir = tmp_path / "rlib_sym"
            bad_sym_dir.mkdir()
            (bad_sym_dir / "libredteam_s2.rlib").write_bytes(
                _make_elf64_ar(b".text.hijack", sym_name=b"__libc_start_main")
            )
            with self.assertRaises(harness.InvalidSubmissionError):
                harness._verify_s2_rlib_no_ctors(bad_sym_dir, crate_name="redteam_s2")

    def test_s2_rlib_unwinding_e1_freshness_dirfd_and_collision_regressions(self):
        with tempfile.TemporaryDirectory(prefix="rt-reg-") as tmp:
            tmp_path = Path(tmp)

            # Native S2 oracle checks caught unwind handshake
            # (`exited_zero && off == 5 && msg[0] == 2`) BEFORE `128 + sig`.
            rendered = harness._render_s2_oracle_main_rs("nonce", "0")
            msg2_idx = rendered.index("if exited_zero && off == 5 && msg[0] == 2")
            sig_idx = rendered.index("let sig = st & 0x7f;")
            self.assertLess(msg2_idx, sig_idx)

            # Tier-E1 shadow artifact passes `tampered_paths` and
            # surfaces as `ATTACKER_WON` (`sandbox_escape_detected=True`).
            s2_e1 = self._make_s2_submission(
                tmp_path / "s2_e1_shadow",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- p\n",
            )
            (s2_e1 / "incorrectness").mkdir()
            (s2_e1 / "incorrectness/semantics.patch").write_text(
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "@@ -1,1 +1,1 @@\n-a\n+b\n",
                encoding="utf-8",
            )
            (s2_e1 / "incorrectness/Proof.lean").write_text("-- p\n")

            def _shadow_e1_runner(**_kwargs):
                raise harness.DefenderTamperError(
                    "Tier-E1 attacker compilation shadowed Expected.olean",
                    tampered_paths=("Expected.olean",),
                )

            rcpt_shadow = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_e1,
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
                miri_runner=_mock_proc(0),
                rustc_runner=_mock_proc(0),
                e1_runner=_shadow_e1_runner,
            )
            self.assertEqual(rcpt_shadow["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertTrue(rcpt_shadow["sandbox_escape_detected"])
            self.assertFalse(rcpt_shadow["defender_integrity_ok"])
            self.assertEqual(
                rcpt_shadow["trace_artifacts"]["sandbox_escape"],
                {"detected": True, "tampered_paths": ["Expected.olean"]},
            )

            # Receipt includes `tool_provenance` and rejects stale
            # auto-discovered release/debug binaries against checkout sources.
            self.assertIn("tool_provenance", rcpt_shadow)
            stale_repo = tmp_path / "stale_repo"
            (stale_repo / "trusted/audit").mkdir(parents=True)
            (stale_repo / "Cargo.toml").write_text("[workspace]\n")
            (stale_repo / "Cargo.lock").write_text("# lock\n")
            (stale_repo / "trusted/audit/SpecPreflight.lean").write_text("-- s\n")
            (stale_repo / "target/release").mkdir(parents=True)
            (stale_repo / "target/debug").mkdir(parents=True)
            rel_cli = stale_repo / "target/release/cargo-anneal"
            dbg_cli = stale_repo / "target/debug/cargo-anneal"
            rel_cap = stale_repo / "target/release/anneal-rustc-capture"
            rel_cli.write_bytes(b"rel")
            rel_cap.write_bytes(b"cap")
            dbg_cli.write_bytes(b"dbg")
            now_ns = time.time_ns() if hasattr(time, "time_ns") else int(time.time() * 1e9)
            os.utime(rel_cli, ns=(now_ns - 10_000_000_000, now_ns - 10_000_000_000))
            os.utime(dbg_cli, ns=(now_ns - 5_000_000_000, now_ns - 5_000_000_000))
            with unittest.mock.patch.dict(os.environ, {}, clear=False):
                os.environ.pop("CARGO_TARGET_DIR", None)
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError, r"stale release binary"
                ):
                    harness._verify_live_tool_freshness(
                        stale_repo,
                        {"cli": rel_cli, "capture": rel_cap},
                        explicit_overrides={"cli": None, "capture": None},
                        live_names=("cli", "capture"),
                    )
                dbg_cli.unlink()
                os.utime(
                    stale_repo / "trusted/audit/SpecPreflight.lean",
                    ns=(now_ns, now_ns),
                )
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError, r"stale prebuilt `cargo-anneal`"
                ):
                    harness._verify_live_tool_freshness(
                        stale_repo,
                        {"cli": rel_cli, "capture": rel_cap},
                        explicit_overrides={"cli": None, "capture": None},
                        live_names=("cli", "capture"),
                    )
            custom_tgt = tmp_path / "custom_target"
            (custom_tgt / "release").mkdir(parents=True)
            (custom_tgt / "debug").mkdir(parents=True)
            c_rel = custom_tgt / "release/cargo-anneal"
            c_dbg = custom_tgt / "debug/cargo-anneal"
            c_rel.write_bytes(b"rel")
            c_dbg.write_bytes(b"dbg")
            os.utime(c_rel, ns=(now_ns - 10_000_000_000, now_ns - 10_000_000_000))
            os.utime(c_dbg, ns=(now_ns - 5_000_000_000, now_ns - 5_000_000_000))
            with unittest.mock.patch.dict(
                os.environ, {"CARGO_TARGET_DIR": str(custom_tgt)}, clear=False
            ):
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError, r"stale release binary"
                ):
                    harness._verify_live_tool_freshness(
                        stale_repo,
                        {"cli": c_rel, "capture": rel_cap},
                        explicit_overrides={"cli": None, "capture": None},
                        live_names=("cli", "capture"),
                    )
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError, r"stale prebuilt `cargo-anneal`"
                ):
                    harness._verify_live_tool_freshness(
                        stale_repo,
                        {"cli": rel_cli, "capture": rel_cap},
                        explicit_overrides={"cli": None, "capture": None},
                        live_names=("cli", "capture"),
                    )

            # `compile_error` fails closed as `INVALID_SUBMISSION`
            # even when E1 or E2 artifacts are attached.
            s2_ce_e2 = self._make_s2_submission(
                tmp_path / "s2_ce_e2",
                "fn target(x: u32) -> u32 { x }\n",
                "-- p\n",
            )
            (s2_ce_e2 / "incorrectness").mkdir()
            (s2_ce_e2 / "incorrectness/claim.md").write_text("# claim\n")
            rcpt_ce_e2 = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_ce_e2,
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
                miri_runner=_mock_proc(1, stderr="error[E0603]: function `target` is private"),
                rustc_runner=_mock_proc(1, stderr="error[E0603]: function `target` is private"),
            )
            self.assertEqual(rcpt_ce_e2["verdict"], harness.VERDICT_INVALID_SUBMISSION)
            self.assertIsNone(rcpt_ce_e2["dedup"])

            rcpt_ce_e1 = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_e1,
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
                miri_runner=_mock_proc(1, stderr="error[E0603]: function `target` is private"),
                rustc_runner=_mock_proc(1, stderr="error[E0603]: function `target` is private"),
            )
            self.assertEqual(rcpt_ce_e1["verdict"], harness.VERDICT_INVALID_SUBMISSION)
            self.assertIsNone(rcpt_ce_e1["dedup"])

            # Scenario 4 detects newly added files
            # anywhere inside the staged defender tree.
            s4_add = tmp_path / "s4_add"
            (s4_add / "theory/Anneal").mkdir(parents=True)
            (s4_add / "theory/Anneal/Clean.lean").write_text("-- ok\n")

            def _adding_audit(cmd, *, cwd, env, timeout):
                del cmd, env, timeout
                (cwd / "trusted").mkdir(exist_ok=True)
                (cwd / "trusted/Escaped.lean").write_text("-- pwned\n")
                return subprocess.CompletedProcess(["audit"], 1, stdout="", stderr="err")

            rcpt_s4_add = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_add,
                audit_runner=_adding_audit,
            )
            self.assertEqual(rcpt_s4_add["verdict"], harness.VERDICT_ATTACKER_WON)
            self.assertTrue(rcpt_s4_add["sandbox_escape_detected"])
            self.assertEqual(
                rcpt_s4_add["trace_artifacts"]["sandbox_escape"]["tampered_paths"],
                ["trusted/Escaped.lean"],
            )

            # Streaming rlib scanner rejects oversized sparse `.rlib` and
            # 2nd rlib lacking ELF objects.
            import struct

            huge_rlib_dir = tmp_path / "rlib_huge"
            huge_rlib_dir.mkdir()
            huge_path = huge_rlib_dir / "libredteam_s2.rlib"
            with open(huge_path, "wb") as fh:
                fh.truncate(harness.MAX_S2_RLIB_BYTES + 1)
            with self.assertRaisesRegex(
                harness.InvalidSubmissionError, r"exceeds"
            ):
                harness._verify_s2_rlib_no_ctors(
                    huge_rlib_dir, crate_name="redteam_s2"
                )

            non_elf_dir = tmp_path / "rlib_non_elf"
            (non_elf_dir / "deps").mkdir(parents=True)
            shstr = b"\x00.shstrtab\x00.symtab\x00.strtab\x00.text.ok\x00"
            strtab = b"\x00ok_sym\x00"
            symtab = b"\x00" * 24 + struct.pack("<IBBHQQ", 1, (1 << 4) | 2, 0, 1, 0, 0)
            sh_off = (64 + len(shstr) + len(strtab) + len(symtab) + 7) & ~7
            pad = b"\x00" * (sh_off - (64 + len(shstr) + len(strtab) + len(symtab)))
            def _sh(n, t, o, s, l=0, e=0):
                return struct.pack("<IIQQQQIIQQ", n, t, 0, 0, o, s, l, 0, 8, e)
            shdrs = (
                _sh(0, 0, 0, 0)
                + _sh(len(b"\x00.shstrtab\x00.symtab\x00.strtab\x00"), 1, 64, 0)
                + _sh(1, 3, 64, len(shstr))
                + _sh(len(b"\x00.shstrtab\x00"), 2, 64 + len(shstr) + len(strtab), len(symtab), 4, 24)
                + _sh(len(b"\x00.shstrtab\x00.symtab\x00"), 3, 64 + len(shstr), len(strtab))
            )
            ehdr = struct.pack(
                "<16sHHIQQQIHHHHHH",
                b"\x7fELF\x02\x01\x01" + b"\x00" * 9,
                1, 62, 1, 0, 0, sh_off, 0, 64, 0, 0, 64, 5, 2,
            )
            good_obj = ehdr + shstr + strtab + symtab + pad + shdrs
            good_hdr = f"{'a.o/':<16}{'0':<12}{'0':<6}{'0':<6}{'100644':<8}{len(good_obj):<10}`\n".encode("ascii")
            good_tail = b"\n" if len(good_obj) & 1 else b""
            (non_elf_dir / "libredteam_s2.rlib").write_bytes(
                b"!<arch>\n" + good_hdr + good_obj + good_tail
            )
            empty_hdr = f"{'meta':<16}{'0':<12}{'0':<6}{'0':<6}{'100644':<8}{'4':<10}`\n".encode("ascii")
            (non_elf_dir / "deps/libredteam_s2-deadbeef.rlib").write_bytes(
                b"!<arch>\n" + empty_hdr + b"rmta"
            )
            with self.assertRaisesRegex(
                harness.OracleInfrastructureError, r"no ELF object members"
            ):
                harness._verify_s2_rlib_no_ctors(
                    non_elf_dir, crate_name="redteam_s2"
                )

            # Reject case-colliding files and dirs across dir and tar inputs.
            col_dir = tmp_path / "case_col"
            (col_dir / "Proof").mkdir(parents=True)
            (col_dir / "Proof/Proof.lean").write_text("-- p\n")
            (col_dir / "Proof/proof.lean").write_text("-- p2\n")
            rcpt_case_dir = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=col_dir,
            )
            self.assertEqual(
                rcpt_case_dir["verdict"], harness.VERDICT_INVALID_SUBMISSION
            )

            col_dir2 = tmp_path / "case_col_seg"
            (col_dir2 / "Proof").mkdir(parents=True)
            (col_dir2 / "proof").mkdir(parents=True)
            (col_dir2 / "Proof/Proof.lean").write_text("-- p\n")
            (col_dir2 / "proof/Helper.lean").write_text("-- h\n")
            with self.assertRaisesRegex(
                harness.InvalidSubmissionError, r"case-colliding"
            ):
                harness._load_submission_dir(col_dir2)

            case_tar = tmp_path / "case_col.tar.gz"
            _write_tar(
                case_tar,
                [
                    ("Proof/Proof.lean", b"-- p\n", {}),
                    ("Proof/PROOF.lean", b"-- p2\n", {}),
                ],
            )
            rcpt_case_tar = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_tar=case_tar,
            )
            self.assertEqual(
                rcpt_case_tar["verdict"], harness.VERDICT_INVALID_SUBMISSION
            )

            # Tier-E1 Cargo build isolates from host `~/.cargo/config.toml`
            # and uses pinned `sysroot/bin/cargo`.
            fake_host_ch = tmp_path / "host_cargo_home"
            (fake_host_ch / "registry/cache").mkdir(parents=True)
            (fake_host_ch / "config.toml").write_text(
                '[build]\nrustc-wrapper = "/nonexistent/evil-wrapper"\n',
                encoding="utf-8",
            )
            fake_sysroot_e1 = tmp_path / "e1_sysroot"
            (fake_sysroot_e1 / "bin").mkdir(parents=True)
            (fake_sysroot_e1 / "lib/lean").mkdir(parents=True)
            for bn in ("cargo", "rustc", "lean", "cargo-anneal", "anneal-rustc-capture"):
                bp = fake_sysroot_e1 / "bin" / bn
                bp.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                bp.chmod(0o755)
            fake_anneal_e1 = tmp_path / "e1_anneal"
            (fake_anneal_e1 / "trusted/audit").mkdir(parents=True)
            (fake_anneal_e1 / "trusted/lean/Trusted/MirSemantics").mkdir(parents=True)
            (fake_anneal_e1 / "theory/Anneal").mkdir(parents=True)
            (fake_anneal_e1 / "correspondence").mkdir(parents=True)
            (fake_anneal_e1 / "Cargo.toml").write_text("[workspace]\n")
            (fake_anneal_e1 / "Cargo.lock").write_text("# lock\n")
            (fake_anneal_e1 / "trusted/lean/foundation-lock.json").write_text("{}")
            (fake_anneal_e1 / "trusted/lean/Trusted/MirSemantics/Ops.lean").write_text(
                "-- anneal-trust-tier: trusted\nmodule\nprelude\n"
            )
            e1_arts = tmp_path / "e1_arts/capture"
            e1_arts.mkdir(parents=True)
            (e1_arts / "Captured.lean").write_text("-- cap\n")
            observed_build_envs: list[tuple[list[str], dict[str, str]]] = []

            def _capture_e1_build(cmd, *, cwd, env, timeout, **kwargs):
                del cwd, timeout, kwargs
                observed_build_envs.append((list(cmd), dict(env)))
                return subprocess.CompletedProcess(cmd, 1, "", "stop after build capture")

            with (
                unittest.mock.patch.dict(
                    os.environ,
                    {"CARGO_HOME": str(fake_host_ch), "RUSTC_WRAPPER": "/evil"},
                ),
                unittest.mock.patch.object(
                    harness.shutil, "which", return_value="/usr/bin/bwrap"
                ),
                unittest.mock.patch.object(
                    harness,
                    "_run_bounded_subprocess",
                    side_effect=_capture_e1_build,
                ),
            ):
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError, r"stop after build capture"
                ):
                    harness._evaluate_s2_lean_patch_proof(
                        tmp_root=tmp_path / "e1_iso_tmp",
                        anneal_root=fake_anneal_e1,
                        spec=scenarios.get_scenario("s2_code_and_proof_hack"),
                        submission=harness.LoadedSubmission(
                            files={
                                "incorrectness/semantics.patch": (
                                    b"--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                                    b"+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                                    b"@@ -3,1 +3,1 @@\n-prelude\n+prelude\n"
                                ),
                                "incorrectness/Proof.lean": b"-- p\n",
                            },
                            e1_patch_targets=(
                                "anneal/trusted/lean/Trusted/MirSemantics/Ops.lean",
                            ),
                            has_e1=True,
                        ),
                        artifacts_dir=tmp_path / "e1_arts",
                        tools={
                            "lean": fake_sysroot_e1 / "bin/lean",
                            "capture": fake_sysroot_e1 / "bin/anneal-rustc-capture",
                            "sysroot": fake_sysroot_e1,
                        },
                        env={"PATH": "/usr/bin:/bin"},
                        timeout=30,
                    )
            self.assertEqual(len(observed_build_envs), 1)
            b_cmd, b_env = observed_build_envs[0]
            self.assertEqual(b_cmd[0], str(fake_sysroot_e1 / "bin/cargo"))
            self.assertEqual(b_env["RUSTC"], str(fake_sysroot_e1 / "bin/rustc"))
            self.assertNotIn("RUSTC_WRAPPER", b_env)
            iso_ch = Path(b_env["CARGO_HOME"])
            self.assertFalse((iso_ch / "config.toml").exists())
            self.assertFalse((iso_ch / "config").exists())

            # `_load_submission_dir` uses `dir_fd` opens (O_NOFOLLOW) so parent
            # swap after listdir cannot escape.
            race_sub = tmp_path / "race_sub"
            (race_sub / "Proof").mkdir(parents=True)
            (race_sub / "Proof/Proof.lean").write_text("-- ok\n")
            secret = tmp_path / "outside.txt"
            secret.write_text("-- outside\n")
            orig_listdir = os.listdir

            def _swap_during_walk(target_fd):
                entries = orig_listdir(target_fd)
                if "Proof.lean" in entries:
                    (race_sub / "Proof").rename(tmp_path / "Proof_moved")
                    os.symlink(tmp_path, race_sub / "Proof")
                return entries

            with unittest.mock.patch.object(
                harness.os, "listdir", side_effect=_swap_during_walk
            ):
                loaded_race = harness._load_submission_dir(race_sub)
            self.assertEqual(loaded_race["Proof/Proof.lean"], b"-- ok\n")

            # Directory count and depth budgets fail closed on deep nesting.
            many_dirs = tmp_path / "many_dirs"
            many_dirs.mkdir()
            for idx in range(harness.MAX_SUBMISSION_DIRS + 1):
                (many_dirs / f"d{idx}").mkdir()
            rcpt_dirs = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=many_dirs,
            )
            self.assertEqual(
                rcpt_dirs["verdict"], harness.VERDICT_INVALID_SUBMISSION
            )

            deep_dir = tmp_path / "deep_dir"
            cur = deep_dir
            for idx in range(harness.MAX_SUBMISSION_DEPTH + 2):
                cur = cur / f"l{idx}"
                cur.mkdir(parents=True)
            with self.assertRaisesRegex(
                harness.InvalidSubmissionError, r"depth exceeds"
            ):
                harness._load_submission_dir(deep_dir)

    def test_r11_codex_hardening_regressions(self):
        """Check ELF xindex, exp truncation, E1 timeout, scrub, and S4 root."""
        import struct

        with tempfile.TemporaryDirectory(prefix="rt-r11-") as tmp:
            tmp_path = Path(tmp)

            # 1. Extended ELF section counts (`e_shnum == 0`,
            #    `e_shstrndx == 0xFFFF`).
            shstr = b"\x00.shstrtab\x00.init_array\x00"
            sh_off = (64 + len(shstr) + 7) & ~7
            pad = b"\x00" * (sh_off - (64 + len(shstr)))

            def _sh(n, t, o, s, l=0):
                return struct.pack("<IIQQQQIIQQ", n, t, 0, 0, o, s, l, 0, 8, 0)

            shdrs = (
                _sh(0, 0, 0, 3, 1)
                + _sh(1, 3, 64, len(shstr))
                + _sh(len(b"\x00.shstrtab\x00"), 14, 64, 0)
            )
            ehdr_xindex = struct.pack(
                "<16sHHIQQQIHHHHHH",
                b"\x7fELF\x02\x01\x01" + b"\x00" * 9,
                1,
                62,
                1,
                0,
                0,
                sh_off,
                0,
                64,
                0,
                0,
                64,
                0,
                0xFFFF,
            )
            with self.assertRaisesRegex(
                harness.InvalidSubmissionError, r"\.init_array"
            ):
                harness._check_elf64_object_for_ctors(
                    ehdr_xindex + shstr + pad + shdrs,
                    member_label="xindex.o",
                )
            ehdr_empty = struct.pack(
                "<16sHHIQQQIHHHHHH",
                b"\x7fELF\x02\x01\x01" + b"\x00" * 9,
                1,
                62,
                1,
                0,
                0,
                0,
                0,
                64,
                0,
                0,
                64,
                0,
                0,
            )
            harness._check_elf64_object_for_ctors(ehdr_empty, member_label="empty.o")

            # 2. Expansion probe truncation via mismatched streaming hashes or
            #    truncated stdout without hashes.
            def _mk_probe(prefix: str, *, sha: str, total: int, trunc: bool):
                p = subprocess.CompletedProcess(["rustc"], 0, stdout=prefix, stderr="")
                p.stdout_sha256 = sha
                p.stderr_sha256 = "0" * 64
                p.stdout_bytes = total
                p.stderr_bytes = 0
                p.stdout_truncated = trunc
                p.stderr_truncated = False
                return p

            fake_sys = tmp_path / "exp_sysroot"
            (fake_sys / "bin").mkdir(parents=True)
            for bn in ("cargo", "rustc", "miri", "cargo-miri"):
                bp = fake_sys / "bin" / bn
                bp.write_text("#!/bin/sh\nexit 0\n")
                bp.chmod(0o755)
            fake_miri_sys = tmp_path / "exp_miri_sys"
            (fake_miri_sys / "lib/rustlib").mkdir(parents=True)
            vv = subprocess.CompletedProcess(
                ["rustc", "-vV"], 0, stdout=f"host: {harness.VERIFIED_RUST_TARGET}\n", stderr=""
            )
            p_same = _mk_probe("same", sha="a" * 64, total=10_000_000, trunc=True)
            p_diff = _mk_probe("same", sha="b" * 64, total=10_000_000, trunc=True)
            with (
                unittest.mock.patch.object(harness.shutil, "which", return_value="/usr/bin/bwrap"),
                unittest.mock.patch.object(harness, "_verify_bwrap_canary"),
                unittest.mock.patch.object(
                    harness,
                    "_run_cmd_in_bwrap",
                    side_effect=[vv, p_same, p_diff, p_same, p_same, p_same],
                ),
            ):
                with self.assertRaisesRegex(
                    harness.InvalidSubmissionError, r"cfg\(miri\)"
                ):
                    harness._run_s2_code_oracle(
                        tmp_root=tmp_path / "exp_hash_diff",
                        src_files={"src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"},
                        inputs=[0],
                        env={"MIRI_SYSROOT": str(fake_miri_sys)},
                        timeout=30,
                        sysroot=fake_sys,
                    )

            p_nohash_trunc = subprocess.CompletedProcess(["rustc"], 0, stdout="same", stderr="")
            p_nohash_trunc.stdout_truncated = True
            p_nohash_clean = subprocess.CompletedProcess(["rustc"], 0, stdout="same", stderr="")
            p_nohash_clean.stdout_truncated = False
            with (
                unittest.mock.patch.object(harness.shutil, "which", return_value="/usr/bin/bwrap"),
                unittest.mock.patch.object(harness, "_verify_bwrap_canary"),
                unittest.mock.patch.object(
                    harness,
                    "_run_cmd_in_bwrap",
                    side_effect=[vv, p_nohash_clean, p_nohash_trunc, p_nohash_clean, p_nohash_clean, p_nohash_clean],
                ),
            ):
                st_tr, _, detail_tr = harness._run_s2_code_oracle(
                    tmp_root=tmp_path / "exp_nohash_trunc",
                    src_files={"src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"},
                    inputs=[0],
                    env={"MIRI_SYSROOT": str(fake_miri_sys)},
                    timeout=30,
                    sysroot=fake_sys,
                )
            self.assertEqual(st_tr, "oracle_inconclusive")
            self.assertIn("truncated", detail_tr)

            # 3. Tier-E1 audit, preflight, preservation-audit, and binding
            #    timeouts classify as `HARNESS_ERROR` (never `DEFENDER_HELD`).
            s2_e1 = self._make_s2_submission(
                tmp_path / "s2_e1_to",
                "pub fn target(x: u32) -> u32 { x }\n",
                "-- p\n",
            )
            (s2_e1 / "incorrectness").mkdir()
            (s2_e1 / "incorrectness/Proof.lean").write_text("-- p\n")
            (s2_e1 / "incorrectness/semantics.patch").write_text(
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean\n"
                "@@ -1,1 +1,1 @@\n-a\n+a\n"
            )
            with unittest.mock.patch.object(
                harness,
                "_evaluate_s2_lean_patch_proof_staged",
                side_effect=harness.OracleInfrastructureError(
                    "Tier-E1 strict kernel audit timed out after 300s"
                ),
            ):
                fake_anneal_e1 = tmp_path / "fake_anneal_e1_to"
                (fake_anneal_e1 / "trusted/lean/Trusted/MirSemantics").mkdir(parents=True)
                (fake_anneal_e1 / "trusted/lean/Trusted/MirSemantics/Ops.lean").write_text("a\n")
                (fake_anneal_e1 / "correspondence").mkdir()
                e1_cap_root = tmp_path / "e1_to_cli"
                (e1_cap_root / "bin").mkdir(parents=True)
                for bn in ("cargo-anneal", "anneal-rustc-capture", "lean"):
                    bp = e1_cap_root / "bin" / bn
                    bp.write_text("#!/bin/sh\nexit 0\n")
                    bp.chmod(0o755)
                def _verify_with_cap(cmd, *, cwd, env, timeout):
                    del env, timeout
                    art_idx = cmd.index("--artifacts-dir") + 1
                    cap_dir = Path(cwd / cmd[art_idx] / "capture")
                    cap_dir.mkdir(parents=True, exist_ok=True)
                    (cap_dir / "Captured.lean").write_text("-- cap\n")
                    return subprocess.CompletedProcess(
                        cmd, 0, stdout=json.dumps(_clean_receipt(scope_kind="crate")), stderr=""
                    )
                with (
                    unittest.mock.patch.object(harness.shutil, "which", return_value="/usr/bin/bwrap"),
                    unittest.mock.patch.object(harness, "_stage_anneal_checkout_copy"),
                    unittest.mock.patch.object(harness, "_apply_unified_patch_strictly", return_value=(["anneal/trusted/lean/Trusted/MirSemantics/Ops.lean"], {})),
                    unittest.mock.patch.object(harness, "_verify_full_tree_unchanged"),
                ):
                    rcpt_e1_to = harness.evaluate_submission(
                        scenario_id="s2_code_and_proof_hack",
                        submission_dir=s2_e1,
                        anneal_root=fake_anneal_e1,
                        cli=e1_cap_root / "bin/cargo-anneal",
                        capture=e1_cap_root / "bin/anneal-rustc-capture",
                        sysroot=fake_sys,
                        lean=e1_cap_root / "bin/lean",
                        miri_sysroot=fake_miri_sys,
                        verify_runner=_verify_with_cap,
                        inspect_runner=_mock_inspect_pass(),
                        miri_runner=_mock_proc(0),
                        rustc_runner=_mock_proc(0),
                    )
                self.assertEqual(rcpt_e1_to["verdict"], harness.VERDICT_HARNESS_ERROR)

            # Verify staged timeout branches raise OracleInfrastructureError
            # for preservation audit, preflight, strict audit, and binding.
            staged_anneal = tmp_path / "staged_anneal"
            (staged_anneal / "trusted/lean/Trusted").mkdir(parents=True)
            (staged_anneal / "trusted/lean/Trusted.lean").write_text("-- anneal-trust-tier: trusted\n")
            (staged_anneal / "trusted/lean/Trusted/Core.lean").write_text("-- anneal-trust-tier: trusted\n")
            (staged_anneal / "trusted/lean/foundation-lock.json").write_text(json.dumps({"modules": {}, "graph": {}, "axioms": []}))
            (staged_anneal / "trusted/audit").mkdir(parents=True)
            (staged_anneal / "theory/Anneal").mkdir(parents=True)
            (staged_anneal / "theory/Anneal/MirWp.lean").write_text("module\n")
            (staged_anneal / "correspondence").mkdir()
            (staged_anneal / "Cargo.toml").write_text("[workspace]\n")
            (staged_anneal / "Cargo.lock").write_text("# lock\n")
            lean_sys_tmp = tmp_path / "lean_sys"
            (lean_sys_tmp / "lib/lean").mkdir(parents=True)
            build_ok_proc = subprocess.CompletedProcess(["cargo"], 0, stdout="", stderr="")
            def _make_lean_bwrap_seq(*, fail_at_step: str):
                def _runner(**kw):
                    args = kw.get("lean_args", [])
                    joined = " ".join(args)
                    if fail_at_step == "preflight" and "req_preflight.json" in joined:
                        raise subprocess.TimeoutExpired(["lean"], 1)
                    if fail_at_step == "audit" and "req_audit.json" in joined:
                        raise subprocess.TimeoutExpired(["lean"], 1)
                    if "req_preflight.json" in joined:
                        Path(kw["rw_mounts"][0][0] / "res_preflight.json").write_text(
                            json.dumps({"ok": True, "result": {"graph": {}, "headers": []}})
                        )
                    elif "req_headers.json" in joined:
                        Path(kw["rw_mounts"][0][0] / "res_headers.json").write_text(
                            json.dumps({"ok": True, "result": {"headers": []}})
                        )
                    elif "req_audit.json" in joined:
                        Path(kw["rw_mounts"][0][0] / "res_audit.json").write_text(
                            json.dumps({"ok": True, "result": {"replay": True, "checkedAlternateProofs": 0, "axioms": ["propext"]}})
                        )
                    return subprocess.CompletedProcess(["lean"], 0, stdout="", stderr="")
                return _runner
            def _fake_compile_mods(**kw):
                out_h = kw["out_host"]
                for m in kw["modules"]:
                    p = out_h / f"{m.replace('.', '/')}.olean"
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_bytes(b"o")
                return True, ""
            sub_e1 = harness.LoadedSubmission(
                files={
                    "incorrectness/semantics.patch": b"p",
                    "incorrectness/Proof.lean": b"-- p\n",
                },
                has_e1=True,
            )
            with (
                unittest.mock.patch.object(harness, "_run_bounded_subprocess", return_value=build_ok_proc),
                unittest.mock.patch.object(harness, "_run_auditor_in_bwrap", side_effect=subprocess.TimeoutExpired(["audit"], 1)),
            ):
                with self.assertRaisesRegex(harness.OracleInfrastructureError, r"Preservation Canary Gate timed out"):
                    harness._evaluate_s2_lean_patch_proof_staged(
                        tmp_root=tmp_path / "st_4a",
                        patched_anneal=staged_anneal,
                        spec=scenarios.get_scenario("s2_code_and_proof_hack"),
                        submission=sub_e1,
                        captured_bytes=b"-- cap\n",
                        shard_entries=[],
                        shard_mods=[],
                        lean_bin=e1_cap_root / "bin/lean",
                        capture=e1_cap_root / "bin/anneal-rustc-capture",
                        sysroot=fake_sys,
                        bwrap=Path("/usr/bin/bwrap"),
                        env={"PATH": "/usr/bin:/bin"},
                        timeout=10,
                        pin_tree=lambda _p: None,
                        verify_pinned=lambda: None,
                    )
            for step, pat in (
                ("preflight", r"Tier-E1 preflight timed out"),
                ("audit", r"Tier-E1 strict kernel audit timed out"),
                ("binding", r"Tier-E1 kernel claim binding timed out"),
            ):
                st_dir = tmp_path / f"st_{step}"
                st_dir.mkdir()
                with (
                    unittest.mock.patch.object(harness, "_run_bounded_subprocess", return_value=build_ok_proc),
                    unittest.mock.patch.object(harness, "_run_auditor_in_bwrap", return_value=subprocess.CompletedProcess(["a"], 0, "{}", "")),
                    unittest.mock.patch.object(harness, "_run_verify_and_inspect", return_value=(True, True, _clean_receipt(scope_kind="crate"), {}, [])),
                    unittest.mock.patch.object(harness, "_resolve_lean_sysroot", return_value=lean_sys_tmp),
                    unittest.mock.patch.object(harness, "_run_lean_in_bwrap", side_effect=_make_lean_bwrap_seq(fail_at_step=step)),
                    unittest.mock.patch.object(harness, "_compile_lean_modules_in_bwrap", side_effect=_fake_compile_mods),
                    unittest.mock.patch.object(
                        harness.lean_ast,
                        "verify_e1_kernel_binding_in_bwrap",
                        side_effect=(subprocess.TimeoutExpired(["lean"], 1) if step == "binding" else None),
                        return_value=(True, "ok"),
                    ),
                ):
                    with self.assertRaisesRegex(harness.OracleInfrastructureError, pat):
                        harness._evaluate_s2_lean_patch_proof_staged(
                            tmp_root=st_dir,
                            patched_anneal=staged_anneal,
                            spec=scenarios.get_scenario("s2_code_and_proof_hack"),
                            submission=sub_e1,
                            captured_bytes=b"-- cap\n",
                            shard_entries=[],
                            shard_mods=[],
                            lean_bin=e1_cap_root / "bin/lean",
                            capture=e1_cap_root / "bin/anneal-rustc-capture",
                            sysroot=fake_sys,
                            bwrap=Path("/usr/bin/bwrap"),
                            env={"PATH": "/usr/bin:/bin"},
                            timeout=10,
                            pin_tree=lambda _p: None,
                            verify_pinned=lambda: None,
                        )

            # 4. Private host paths are scrubbed from receipt reasons, summary,
            #    and traces.
            priv_root = tmp_path / "priv_checkout" / "anneal"
            (priv_root / "trusted/audit").mkdir(parents=True)
            priv_cli = tmp_path / "priv_bins" / "cargo-anneal"
            priv_cli.parent.mkdir(parents=True)
            priv_cli.write_text("#!/bin/sh\nexit 0\n")
            s1_priv = tmp_path / "s1_priv"
            (s1_priv / "Proof").mkdir(parents=True)
            (s1_priv / "Proof/Proof.lean").write_text("module\n")
            leaked_err = (
                f"operational failure in {priv_root}/trusted/foo "
                f"using tool {priv_cli} and home {Path.home()}/secret"
            )
            rcpt_priv = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=s1_priv,
                anneal_root=priv_root,
                cli=priv_cli,
                capture=priv_cli,
                sysroot=fake_sys,
                lean=priv_cli,
                verify_runner=lambda *_a, **_kw: (_ for _ in ()).throw(
                    harness.OracleInfrastructureError(leaked_err)
                ),
            )
            self.assertEqual(rcpt_priv["verdict"], harness.VERDICT_HARNESS_ERROR)
            rendered = json.dumps(rcpt_priv)
            self.assertNotIn(str(priv_root), rendered)
            self.assertNotIn(str(priv_cli), rendered)
            self.assertNotIn(str(Path.home()), rendered)

            # 5. Scenario 4 non-`Anneal` theory roots passing audit ->
            #    `ATTACKER_WON`.
            for bad_rel in ("theory/Trusted/Foo.lean", "theory/Foo.lean"):
                s4_non = tmp_path / ("s4_non_" + bad_rel.replace("/", "_"))
                (s4_non / bad_rel).parent.mkdir(parents=True)
                (s4_non / bad_rel).write_text(
                    "module\nprelude\npublic import Init.Core\ndef ok : Nat := 0\n",
                    encoding="utf-8",
                )
                good_s4 = {
                    "guarantee": "kernel dependency closure",
                    "replay": True,
                    "replayedDeclarations": 1,
                    "kernelDeclarations": 1,
                    "checkedAlternateProofs": 0,
                    "axioms": ["propext"],
                }
                r_non = harness.evaluate_submission(
                    scenario_id="s4_theory_audit_hack",
                    submission_dir=s4_non,
                    audit_runner=_mock_proc(0, stdout=json.dumps(good_s4)),
                )
                self.assertEqual(r_non["verdict"], harness.VERDICT_ATTACKER_WON)
                self.assertTrue(r_non["oracle_incorrect_confirmed"])
                self.assertTrue(
                    any("non_anneal_theory_root:" in f for f in r_non["dedup"]["features"]),
                    r_non,
                )

    def test_r12_codex_hardening_regressions(self):
        """Check bwrap/miri provenance, E1 crates, sub scrub, receipt eq, caps."""
        import io
        import tarfile

        with tempfile.TemporaryDirectory(prefix="rt-r12-") as tmp:
            tmp_path = Path(tmp)

            # 1. `_discover_miri_sysroot` runs in `bwrap` and ignores ambient
            #    `cargo` / `RUSTC_WRAPPER` while recording `miri_sysroot` prov.
            hijack_bin = tmp_path / "hijack_cargo_bin"
            hijack_bin.mkdir()
            marker = tmp_path / "ambient_cargo_ran"
            (hijack_bin / "cargo").write_text(
                f"#!/bin/sh\ntouch '{marker}'\necho /tmp/evil_miri\n",
                encoding="utf-8",
            )
            (hijack_bin / "cargo").chmod(0o755)
            fake_rustup = tmp_path / "rustup_home"
            tc_dir = (
                fake_rustup
                / "toolchains"
                / f"nightly-2026-05-31-{harness.VERIFIED_RUST_TARGET}"
            )
            (tc_dir / "bin").mkdir(parents=True)
            (tc_dir / "lib").mkdir(parents=True)
            for bn in ("cargo", "rustc", "cargo-miri", "miri"):
                bp = tc_dir / "bin" / bn
                bp.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                bp.chmod(0o755)
            fake_xdg = tmp_path / "xdg_cache"
            fake_miri = fake_xdg / "miri"
            rlib_dir = fake_miri / "lib/rustlib" / harness.VERIFIED_RUST_TARGET / "lib"
            rlib_dir.mkdir(parents=True)
            (rlib_dir / "libcore.rlib").write_bytes(b"core-rlib")

            seen_bwrap_calls: list[dict[str, object]] = []

            def _fake_miri_bwrap(**kw):
                seen_bwrap_calls.append(kw)
                return subprocess.CompletedProcess(
                    kw["argv"], 0, stdout=f"{fake_miri}\n", stderr=""
                )

            with (
                unittest.mock.patch.dict(
                    os.environ,
                    {
                        "PATH": f"{hijack_bin}:{os.environ.get('PATH', '')}",
                        "RUSTUP_HOME": str(fake_rustup),
                        "XDG_CACHE_HOME": str(fake_xdg),
                        "RUSTC_WRAPPER": "/evil/wrapper",
                    },
                ),
                unittest.mock.patch.object(
                    harness.shutil, "which", return_value="/usr/bin/bwrap"
                ),
                unittest.mock.patch.object(
                    harness, "_run_cmd_in_bwrap", side_effect=_fake_miri_bwrap
                ),
            ):
                resolved_miri = harness._discover_miri_sysroot()
            self.assertFalse(marker.exists(), "ambient cargo must never run")
            self.assertEqual(resolved_miri, fake_miri.resolve())
            self.assertEqual(len(seen_bwrap_calls), 1)
            self.assertNotIn("RUSTC_WRAPPER", seen_bwrap_calls[0]["env_vars"])
            self.assertEqual(
                seen_bwrap_calls[0]["argv"],
                [str(tc_dir.resolve() / "bin/cargo"), "miri", "setup", "--print-sysroot"],
            )

            # 2. `_prepare_e1_isolated_cargo_home` unpacks SHA-256-verified
            #    `.crate` archives without symlinking host `~/.cargo/registry`.
            buf = io.BytesIO()
            crate_root = "demo_dep-0.1.0"
            crate_files = {
                f"{crate_root}/Cargo.toml": (
                    b'[package]\nname = "demo_dep"\nversion = "0.1.0"\n'
                ),
                f"{crate_root}/src/lib.rs": b"pub fn helper() -> u32 { 7 }\n",
            }
            with tarfile.open(fileobj=buf, mode="w:gz") as tf:
                for mname, mbytes in crate_files.items():
                    ti = tarfile.TarInfo(mname)
                    ti.size = len(mbytes)
                    ti.mode = 0o644
                    tf.addfile(ti, io.BytesIO(mbytes))
            crate_blob = buf.getvalue()
            crate_sha = harness._sha256_bytes(crate_blob)
            host_ch = tmp_path / "r12_host_ch"
            cache_idx = host_ch / "registry/cache/index.crates.io-test"
            cache_idx.mkdir(parents=True)
            crate_archive = cache_idx / "demo_dep-0.1.0.crate"
            crate_archive.write_bytes(crate_blob)
            (host_ch / "registry/src/tampered").mkdir(parents=True)
            (host_ch / "config.toml").write_text(
                '[build]\nrustc-wrapper = "/evil"\n', encoding="utf-8"
            )
            lockfile = tmp_path / "Cargo.lock"
            lockfile.write_text(
                '[[package]]\nname = "demo_dep"\nversion = "0.1.0"\n'
                f'source = "{harness._CRATES_IO_SOURCE}"\n'
                f'checksum = "{crate_sha}"\n',
                encoding="utf-8",
            )
            with unittest.mock.patch.dict(os.environ, {"CARGO_HOME": str(host_ch)}):
                e1_ch = harness._prepare_e1_isolated_cargo_home(
                    tmp_path / "e1_ok", lockfile=lockfile
                )
                self.assertFalse((e1_ch / "registry").exists())
                vendored = tmp_path / "e1_ok/e1_vendor/demo_dep-0.1.0"
                self.assertEqual(
                    (vendored / "src/lib.rs").read_bytes(),
                    b"pub fn helper() -> u32 { 7 }\n",
                )
                csum = json.loads((vendored / ".cargo-checksum.json").read_text())
                self.assertEqual(csum["package"], crate_sha)
                self.assertEqual(
                    csum["files"]["src/lib.rs"],
                    harness._sha256_bytes(b"pub fn helper() -> u32 { 7 }\n"),
                )
                cfg_txt = (e1_ch / "config.toml").read_text()
                self.assertIn('replace-with = "e1_vendor"', cfg_txt)
                self.assertNotIn("rustc-wrapper", cfg_txt)

                crate_archive.write_bytes(crate_blob[:-1] + bytes([crate_blob[-1] ^ 1]))
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError, r"checksum mismatch"
                ):
                    harness._prepare_e1_isolated_cargo_home(
                        tmp_path / "e1_bad_sha", lockfile=lockfile
                    )
                crate_archive.unlink()
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError, r"missing verified offline"
                ):
                    harness._prepare_e1_isolated_cargo_home(
                        tmp_path / "e1_missing", lockfile=lockfile
                    )

            # 3. Submission paths are scrubbed on early load errors.
            bad_sub_dir = tmp_path / "secret_sub_root" / "sub_case"
            (bad_sub_dir / "Proof").mkdir(parents=True)
            os.symlink("/etc/passwd", bad_sub_dir / "Proof/Proof.lean")
            rcpt_sub = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=bad_sub_dir,
            )
            self.assertEqual(rcpt_sub["verdict"], harness.VERDICT_INVALID_SUBMISSION)
            sub_rendered = json.dumps(rcpt_sub)
            self.assertNotIn(str(bad_sub_dir), sub_rendered)

            bad_tar = tmp_path / "secret_tar_root" / "evil.tar.gz"
            bad_tar.parent.mkdir(parents=True)
            bad_tar.write_bytes(b"not-a-tarball")
            rcpt_tar = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_tar=bad_tar,
            )
            self.assertEqual(rcpt_tar["verdict"], harness.VERDICT_INVALID_SUBMISSION)
            tar_rendered = json.dumps(rcpt_tar)
            self.assertNotIn(str(bad_tar), tar_rendered)
            self.assertNotIn(str(bad_tar.parent), tar_rendered)

            # 4. Reject mismatched stdout vs persisted receipt JSON.
            s1_eq = self._make_proof_submission(tmp_path / "s1_eq", "-- p\n")

            def _mismatched_verify(cmd, *, cwd, env, timeout):
                del cwd, env, timeout
                rec_idx = cmd.index("--receipt-out")
                bad_disk = _clean_receipt(scope_kind="selected_unit")
                bad_disk["taint_reasons"] = ["spoofed_on_disk"]
                Path(cmd[rec_idx + 1]).write_text(json.dumps(bad_disk), encoding="utf-8")
                return subprocess.CompletedProcess(
                    cmd, 0, stdout=json.dumps(_clean_receipt()), stderr=""
                )

            rcpt_mismatch = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=s1_eq,
                verify_runner=_mismatched_verify,
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rcpt_mismatch["verdict"], harness.VERDICT_HARNESS_ERROR)
            self.assertIn("--receipt-out JSON differs", rcpt_mismatch["summary"])

            # 5. Fail closed when a child holds output pipes open past exit.
            with self.assertRaisesRegex(
                harness.OracleInfrastructureError, r"descendant kept output pipes open"
            ):
                harness._run_bounded_subprocess(
                    [
                        "/bin/sh",
                        "-c",
                        "exec 2>&-; (sleep 30) >/proc/self/fd/1 & exit 0",
                    ],
                    timeout=15,
                    apply_prlimit=False,
                )

            # 6. Reject hijacked ambient `bwrap` and group-writable binaries,
            #    and record explicit `bwrap` SHA-256 provenance.
            evil_bw_dir = tmp_path / "evil_bw_path"
            evil_bw_dir.mkdir()
            evil_bw = evil_bw_dir / "bwrap"
            bw_marker = tmp_path / "evil_bw_ran"
            evil_bw.write_text(
                f"#!/bin/sh\ntouch '{bw_marker}'\nexit 0\n", encoding="utf-8"
            )
            evil_bw.chmod(0o755)
            with unittest.mock.patch.dict(
                os.environ, {"PATH": f"{evil_bw_dir}:{os.environ.get('PATH', '')}"}
            ):
                rcpt_evil_bw = harness.evaluate_submission(
                    scenario_id="s1a_ub_proof_hack",
                    submission_dir=s1_eq,
                    verify_runner=_mock_verify_fail(),
                    inspect_runner=_mock_inspect_pass(),
                )
            self.assertEqual(rcpt_evil_bw["verdict"], harness.VERDICT_HARNESS_ERROR)
            self.assertFalse(bw_marker.exists(), "hijacked PATH bwrap must never run")

            writable_bw_dir = tmp_path / "writable_bw_dir"
            writable_bw_dir.mkdir()
            writable_bw_dir.chmod(0o755)
            w_bw = writable_bw_dir / "bwrap"
            w_bw.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            w_bw.chmod(0o775)
            with self.assertRaisesRegex(
                harness.OracleInfrastructureError, r"group/world-writable"
            ):
                harness._resolve_bwrap_binary(w_bw)
            w_bw.chmod(0o755)
            rcpt_exp_bw = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=s1_eq,
                bwrap=w_bw,
                miri_sysroot=fake_miri,
                verify_runner=_mock_verify_fail(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rcpt_exp_bw["verdict"], harness.VERDICT_DEFENDER_HELD)
            bw_prov = rcpt_exp_bw["tool_provenance"]["bwrap"]
            self.assertEqual(bw_prov["source"], "explicit")
            self.assertEqual(
                bw_prov["sha256"], harness._sha256_bytes(b"#!/bin/sh\nexit 0\n")
            )
            self.assertIn("miri_sysroot", rcpt_exp_bw["tool_provenance"])

            # 7. E1 `Captured.lean` and shard reads enforce byte caps.
            cap_dir = tmp_path / "e1_cap_limits/capture"
            (cap_dir / "Captured").mkdir(parents=True)
            (cap_dir / "Captured.lean").write_bytes(b"x" * 180)
            (cap_dir / "Captured/Shard_000.lean").write_bytes(b"a" * 90)
            (cap_dir / "Captured/Shard_001.lean").write_bytes(b"b" * 90)
            (cap_dir / "Captured/Shard_002.lean").write_bytes(b"c" * 90)
            with (
                unittest.mock.patch.object(harness, "MAX_E1_CAPTURE_FILE_BYTES", 120),
                unittest.mock.patch.object(harness, "MAX_E1_CAPTURE_TOTAL_BYTES", 200),
            ):
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError, r"exceeds 120 bytes"
                ):
                    harness._evaluate_s2_lean_patch_proof(
                        tmp_root=tmp_path / "e1_lim_1",
                        anneal_root=tmp_path,
                        spec=scenarios.get_scenario("s2_code_and_proof_hack"),
                        submission=harness.LoadedSubmission(
                            files={"incorrectness/semantics.patch": b""},
                            has_e1=True,
                        ),
                        artifacts_dir=cap_dir.parent,
                        tools={
                            "lean": tc_dir / "bin/cargo",
                            "capture": tc_dir / "bin/rustc",
                            "sysroot": tc_dir,
                        },
                        env={},
                        timeout=10,
                        bwrap=w_bw,
                    )
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError, r"exceeds \d+ bytes"
                ):
                    harness._discover_e1_capture_shards(cap_dir, max_total_bytes=200)

    def test_r13_codex_hardening_regressions(self):
        """Check container bwrap, prlimit pin, lazy rustup, oracle timeout, S4."""
        with tempfile.TemporaryDirectory(prefix="rt-r13-") as tmp:
            tmp_path = Path(tmp)

            # 1. Trusted system binary validation accepts container-uid bwrap
            #    under `/usr/bin` while still rejecting non-system user paths.
            fake_sys_bin = tmp_path / "usr/bin"
            fake_sys_bin.mkdir(parents=True)
            sys_bwrap = fake_sys_bin / "bwrap"
            sys_bwrap.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            sys_bwrap.chmod(0o755)
            non_sys_bwrap = tmp_path / "opt/bin/bwrap"
            non_sys_bwrap.parent.mkdir(parents=True)
            non_sys_bwrap.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            non_sys_bwrap.chmod(0o755)
            fake_uid = os.geteuid() or 1001
            def _fake_sys_stat(p, *a, **kw):
                return os.stat_result(
                    (
                        0o100755 if Path(p).name == "bwrap" else 0o040755,
                        1,
                        1,
                        1,
                        fake_uid,
                        fake_uid,
                        1,
                        0,
                        0,
                        0,
                    )
                )

            with (
                unittest.mock.patch.object(
                    harness, "_untrusted_bwrap_prefixes", return_value=()
                ),
                unittest.mock.patch.object(
                    harness, "_TRUSTED_SYSTEM_BIN_ROOTS", (fake_sys_bin,)
                ),
                unittest.mock.patch.object(os, "geteuid", return_value=fake_uid),
                unittest.mock.patch.object(
                    os, "stat", side_effect=_fake_sys_stat
                ),
                unittest.mock.patch.object(
                    os, "lstat", side_effect=_fake_sys_stat
                ),
                unittest.mock.patch.object(os, "access", return_value=True),
            ):
                resolved_sys = harness._validate_bwrap_candidate(
                    sys_bwrap, explicit_override=False
                )
                self.assertEqual(resolved_sys, sys_bwrap.resolve())
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError, r"untrusted owner uid"
                ):
                    harness._validate_bwrap_candidate(
                        non_sys_bwrap, explicit_override=False
                    )

            # 2. Outer `prlimit` is pinned/validated, recorded in
            #    `tool_provenance`, and falls back to `preexec_fn` when absent.
            s1_sub = tmp_path / "s1_prlimit"
            (s1_sub / "Proof").mkdir(parents=True)
            (s1_sub / "Proof/Proof.lean").write_text("-- safe\n", encoding="utf-8")
            evil_pr_dir = tmp_path / "evil_pr_path"
            evil_pr_dir.mkdir()
            evil_pr = evil_pr_dir / "prlimit"
            pr_marker = tmp_path / "evil_pr_ran"
            evil_pr.write_text(
                f"#!/bin/sh\ntouch '{pr_marker}'\nexit 0\n", encoding="utf-8"
            )
            evil_pr.chmod(0o755)
            with unittest.mock.patch.dict(
                os.environ, {"PATH": f"{evil_pr_dir}:{os.environ.get('PATH', '')}"}
            ):
                rcpt_evil_pr = harness.evaluate_submission(
                    scenario_id="s1a_ub_proof_hack",
                    submission_dir=s1_sub,
                    verify_runner=_mock_verify_fail(),
                    inspect_runner=_mock_inspect_pass(),
                )
            self.assertEqual(rcpt_evil_pr["verdict"], harness.VERDICT_HARNESS_ERROR)
            self.assertFalse(pr_marker.exists(), "hijacked PATH prlimit must never run")

            ok_pr = tmp_path / "ok_prlimit"
            ok_pr.write_text("#!/bin/sh\nshift\nexec \"$@\"\n", encoding="utf-8")
            ok_pr.chmod(0o755)
            rcpt_ok_pr = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=s1_sub,
                prlimit=ok_pr,
                verify_runner=_mock_verify_fail(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(rcpt_ok_pr["verdict"], harness.VERDICT_DEFENDER_HELD)
            pr_prov = rcpt_ok_pr["tool_provenance"]["prlimit"]
            self.assertEqual(pr_prov["source"], "explicit")
            self.assertEqual(
                pr_prov["sha256"],
                harness._sha256_bytes(b"#!/bin/sh\nshift\nexec \"$@\"\n"),
            )
            with unittest.mock.patch.object(shutil, "which", return_value=None):
                res_rlim = harness._run_bounded_subprocess(
                    ["/bin/sh", "-c", "ulimit -c"],
                    timeout=10,
                )
            self.assertEqual(res_rlim.returncode, 0)
            self.assertEqual(res_rlim.stdout.strip(), "0")

            # 3. `evaluate_submission` avoids eager ambient `rustup` discovery
            #    and resolves pinned sysroots via scrubbed `rustc`.
            seen_cmds: list[list[str]] = []

            def _bomb_rustup(*_args, **_kwargs):
                raise AssertionError("ambient discover_local_defaults must not run")

            fake_tc = tmp_path / "rustup_home/toolchains" / (
                f"nightly-2026-05-31-{harness.VERIFIED_RUST_TARGET}"
            )
            (fake_tc / "bin").mkdir(parents=True)
            (fake_tc / "lib").mkdir(parents=True)
            (fake_tc / "bin/rustc").write_text("#!/bin/sh\nexit 0\n")
            (fake_tc / "bin/rustc").chmod(0o755)
            with (
                unittest.mock.patch.object(
                    harness.anneal_ci_lib,
                    "discover_local_defaults",
                    side_effect=_bomb_rustup,
                ),
                unittest.mock.patch.dict(
                    os.environ, {"RUSTUP_HOME": str(tmp_path / "rustup_home")}
                ),
            ):
                rcpt_no_rustup = harness.evaluate_submission(
                    scenario_id="s1a_ub_proof_hack",
                    submission_dir=s1_sub,
                    sysroot=fake_tc,
                    verify_runner=_mock_verify_fail(),
                    inspect_runner=_mock_inspect_pass(),
                )
                self.assertEqual(
                    rcpt_no_rustup["verdict"], harness.VERDICT_DEFENDER_HELD
                )

                def _fake_rustc_print(cmd, **kwargs):
                    seen_cmds.append(list(cmd))
                    return subprocess.CompletedProcess(
                        cmd, 0, stdout=f"{fake_tc.resolve()}\n", stderr=""
                    )

                with unittest.mock.patch.object(
                    harness, "_run_bounded_subprocess", side_effect=_fake_rustc_print
                ):
                    resolved_sr = harness._resolve_pinned_rust_sysroot(bwrap=None)
                self.assertEqual(resolved_sr, fake_tc.resolve())
                self.assertTrue(seen_cmds)
                self.assertEqual(Path(seen_cmds[0][0]).name, "rustc")

            # 4. S2 rejected before oracle timeout stays DEFENDER_HELD, while
            #    accepted S2 + oracle_timeout returns HARNESS_ERROR.
            s2_sub = self._make_s2_submission(
                tmp_path / "s2_to", "pub fn target(x: u32) -> u32 { x }\n", "-- p\n"
            )

            def _to_runner(cmd, *, cwd, env, timeout):
                raise subprocess.TimeoutExpired(cmd, timeout)

            r_rej_to = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_sub,
                miri_runner=_to_runner,
                rustc_runner=_to_runner,
                verify_runner=_mock_verify_fail(),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_rej_to["verdict"], harness.VERDICT_DEFENDER_HELD)

            # 5. S4 snapshots submitted `theory/` files after staging and
            #    catches mid-run mutations to submitted modules as escape.
            s4_sub = tmp_path / "s4_mut"
            (s4_sub / "theory/Anneal").mkdir(parents=True)
            (s4_sub / "theory/Anneal/M.lean").write_text(
                "prelude\nimport Init.Core\nnamespace Anneal.M\n"
                "theorem t : 0 = 0 := rfl\nend Anneal.M\n",
                encoding="utf-8",
            )

            def _mutate_submitted_theory(cmd, *, cwd, env, timeout):
                target = Path(cwd) / "theory/Anneal/M.lean"
                target.write_text("-- tampered\n", encoding="utf-8")
                return subprocess.CompletedProcess(
                    cmd,
                    0,
                    stdout=json.dumps(
                        {
                            "replay": True,
                            "replayedDeclarations": 1,
                            "kernelDeclarations": 1,
                            "checkedAlternateProofs": 0,
                            "axioms": [],
                            "guarantee": "ok",
                        }
                    ),
                    stderr="",
                )

            r_s4_tamper = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_sub,
                audit_runner=_mutate_submitted_theory,
            )
            self.assertEqual(
                r_s4_tamper["verdict"], harness.VERDICT_ATTACKER_WON, r_s4_tamper
            )
            self.assertFalse(r_s4_tamper["defender_integrity_ok"])
            self.assertTrue(r_s4_tamper["sandbox_escape_detected"])
            self.assertIn("theory/Anneal/M.lean", r_s4_tamper["summary"])

    def test_r14_codex_and_ci_hardening_regressions(self):
        """Verify dir-entry cap, ancestor hardening, git pin, comment strip."""
        with tempfile.TemporaryDirectory(prefix="rt-r14-") as tmp:
            tmp_path = Path(tmp)

            # 1. `_load_submission_dir` aborts via incremental `os.scandir`
            #    when a dir exceeds `MAX_SUBMISSION_FILES + MAX_SUBMISSION_DIRS`
            #    entries without invoking per-entry `os.stat` on every child.
            huge_dir = tmp_path / "huge_sub"
            huge_dir.mkdir()
            limit = harness.MAX_SUBMISSION_FILES + harness.MAX_SUBMISSION_DIRS
            for i in range(limit + 1):
                (huge_dir / f"f_{i:03d}.rs").write_text("fn f() {}\n", encoding="utf-8")
            with unittest.mock.patch.object(
                os,
                "stat",
                side_effect=AssertionError("per-entry stat must not run on oversized dir"),
            ):
                with self.assertRaisesRegex(
                    harness.InvalidSubmissionError,
                    rf"exceeds {limit} entries",
                ):
                    harness._load_submission_dir(huge_dir)

            # 2. `_validate_system_binary_candidate` rejects writable parent
            #    ancestors while permitting sticky `/nix/store`.
            gp = tmp_path / "writable_gp"
            sub = gp / "sub"
            sub.mkdir(parents=True)
            cand = sub / "prlimit"
            cand.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            cand.chmod(0o755)
            sub.chmod(0o755)
            gp.chmod(0o775)
            try:
                with self.assertRaisesRegex(
                    harness.OracleInfrastructureError,
                    r"ancestor directory must not be group/world-writable",
                ):
                    harness._validate_system_binary_candidate(
                        cand, tool_name="prlimit", explicit_override=True
                    )
            finally:
                gp.chmod(0o755)

            nix_bin = Path("/nix/store/abcd-tool/bin/git")

            def _fake_nix_lstat(p, *a, **kw):
                mode = (
                    0o041775
                    if Path(p) == Path("/nix/store")
                    else 0o040755
                )
                return os.stat_result((mode, 1, 1, 1, 0, 0, 1, 0, 0, 0))

            with (
                unittest.mock.patch.object(
                    harness, "_untrusted_bwrap_prefixes", return_value=()
                ),
                unittest.mock.patch.object(
                    Path, "resolve", return_value=nix_bin
                ),
                unittest.mock.patch.object(
                    os,
                    "stat",
                    return_value=os.stat_result(
                        (0o100755, 1, 1, 1, 0, 0, 1, 0, 0, 0)
                    ),
                ),
                unittest.mock.patch.object(
                    os, "lstat", side_effect=_fake_nix_lstat
                ),
                unittest.mock.patch.object(os, "access", return_value=True),
            ):
                self.assertEqual(
                    harness._validate_system_binary_candidate(
                        nix_bin, tool_name="git", explicit_override=False
                    ),
                    nix_bin,
                )

            # 3. Hijacked `git` on `PATH` fails closed in `HARNESS_ERROR`
            #    without executing, while valid `git` records
            #    `tool_provenance["git"]`.
            s1_sub = tmp_path / "s1_git"
            (s1_sub / "Proof").mkdir(parents=True)
            (s1_sub / "Proof/Proof.lean").write_text("-- safe\n", encoding="utf-8")
            evil_git_dir = tmp_path / "evil_git_path"
            evil_git_dir.mkdir()
            git_marker = tmp_path / "evil_git_ran"
            evil_git = evil_git_dir / "git"
            evil_git.write_text(
                f"#!/bin/sh\ntouch '{git_marker}'\nexit 0\n", encoding="utf-8"
            )
            evil_git.chmod(0o755)
            with unittest.mock.patch.dict(
                os.environ, {"PATH": f"{evil_git_dir}:{os.environ.get('PATH', '')}"}
            ):
                rcpt_evil_git = harness.evaluate_submission(
                    scenario_id="s1a_ub_proof_hack",
                    submission_dir=s1_sub,
                    anneal_root=_ANNEAL_ROOT,
                    verify_runner=_mock_verify_fail(),
                    inspect_runner=_mock_inspect_pass(),
                )
            self.assertEqual(rcpt_evil_git["verdict"], harness.VERDICT_HARNESS_ERROR)
            self.assertFalse(git_marker.exists(), "hijacked PATH git must never run")

            if shutil.which("git") is not None:
                rcpt_ok_git = harness.evaluate_submission(
                    scenario_id="s1a_ub_proof_hack",
                    submission_dir=s1_sub,
                    anneal_root=_ANNEAL_ROOT,
                    verify_runner=_mock_verify_fail(),
                    inspect_runner=_mock_inspect_pass(),
                )
                self.assertEqual(rcpt_ok_git["verdict"], harness.VERDICT_DEFENDER_HELD)
                git_prov = rcpt_ok_git["tool_provenance"]["git"]
                self.assertTrue(git_prov["present"], git_prov)
                self.assertEqual(git_prov["source"], "discovered")
                self.assertIn("sha256", git_prov)

    def test_local_semireducible_allowlist_and_shadows(self):
        """Admit only the exact Nat.bitwise local semireducible exception."""
        hdr = (
            "module\nprelude\npublic import Init.Data.Nat.Bitwise.Basic\n"
            "import all Init.Data.Nat.Bitwise.Basic\n"
        )
        ok_src = {
            "theory/Anneal/M.lean": (
                f"{hdr}"
                "attribute [local semireducible] _root_.Nat.bitwise in\n"
                "private theorem ok_unfold : True := trivial\n"
            )
        }
        self.assertEqual(
            harness._detect_disallowed_lean_constructs(
                ok_src, allow_theory_import_all=True, allow_spec_options=False
            ),
            [],
        )
        spec_src = {
            "Spec/Spec.lean": ok_src["theory/Anneal/M.lean"].replace(
                "import all Init.Data.Nat.Bitwise.Basic\n", ""
            )
        }
        self.assertNotEqual(
            harness._detect_disallowed_lean_constructs(
                spec_src,
                allow_theory_import_all=False,
                allow_spec_options=True,
            ),
            [],
        )
        bad_cases = [
            (
                "wrong_const",
                "attribute [local semireducible] _root_.Nat.add in\n"
                "theorem bad_const : True := trivial\n",
            ),
            (
                "wrong_attr",
                "attribute [local reducible] _root_.Nat.bitwise in\n"
                "theorem bad_attr : True := trivial\n",
            ),
            (
                "chained_in",
                "open Nat in\n"
                "attribute [local semireducible] _root_.Nat.bitwise in\n"
                "theorem bad_chain : True := trivial\n",
            ),
            (
                "decl_attrs",
                "attribute [local semireducible] _root_.Nat.bitwise in\n"
                "@[simp] theorem bad_simp : True := trivial\n",
            ),
            ("shadow_decl", "def Foo.Nat.bitwise : Nat := 0\n"),
        ]
        for label, snippet in bad_cases:
            tags = harness._detect_disallowed_lean_constructs(
                {"theory/Anneal/M.lean": f"{hdr}{snippet}"},
                allow_theory_import_all=True,
                allow_spec_options=False,
            )
            self.assertNotEqual(tags, [], f"expected rejection for {label}")

        # Verify Lean AST inspector parity when `lean` + `bwrap` are available.
        tools = anneal_ci_lib.discover_tools(_ANNEAL_ROOT)
        lean_bin = tools.get("lean")
        bwrap = harness._resolve_bwrap_binary()
        if lean_bin is not None and bwrap is not None:
            pe_ok: list[str] = []
            tags_ok = harness._detect_disallowed_lean_constructs_with_tools(
                ok_src,
                allow_theory_import_all=True,
                allow_spec_options=False,
                lean_bin=lean_bin,
                env={},
                bwrap=bwrap,
                allow_fallback=False,
                parse_errors_out=pe_ok,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual(pe_ok, [], pe_ok)
            self.assertEqual(tags_ok, [], tags_ok)

            pe_spec: list[str] = []
            tags_spec = harness._detect_disallowed_lean_constructs_with_tools(
                spec_src,
                allow_theory_import_all=False,
                allow_spec_options=True,
                lean_bin=lean_bin,
                env={},
                bwrap=bwrap,
                allow_fallback=False,
                parse_errors_out=pe_spec,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual(pe_spec, [], pe_spec)
            self.assertNotEqual(tags_spec, [], tags_spec)

            for label, snippet in bad_cases:
                pe_bad: list[str] = []
                tags_bad = (
                    harness._detect_disallowed_lean_constructs_with_tools(
                        {"theory/Anneal/M.lean": f"{hdr}{snippet}"},
                        allow_theory_import_all=True,
                        allow_spec_options=False,
                        lean_bin=lean_bin,
                        env={},
                        bwrap=bwrap,
                        allow_fallback=False,
                        parse_errors_out=pe_bad,
                        anneal_root=_ANNEAL_ROOT,
                    )
                )
                self.assertEqual(pe_bad, [], (label, pe_bad))
                self.assertNotEqual(
                    tags_bad,
                    [],
                    f"Lean AST accepted {label}: tags={tags_bad}",
                )



class LiveToolIntegrationTests(unittest.TestCase):
    def _discover_or_skip(self):
        tools = anneal_ci_lib.discover_tools(_ANNEAL_ROOT)
        missing = [
            k for k in ("cli", "capture", "sysroot", "lean") if tools.get(k) is None
        ]
        if shutil.which("cargo") is None:
            missing.append("cargo")
        if not missing and harness._discover_miri_sysroot() is None:
            missing.append("miri_sysroot")
        if missing:
            if os.environ.get("ANNEAL_REDTEAM_REQUIRE_LIVE") == "1":
                self.fail(f"missing local tools for live redteam test: {missing}")
            self.skipTest(f"local Anneal toolchains not built/present: {missing}")
        return tools

    def test_live_verify_blocks_s1a_s1b_s3_and_s2_honest_oracle(self):
        self._discover_or_skip()
        with tempfile.TemporaryDirectory(prefix="rt-live-") as tmp:
            tmp_path = Path(tmp)

            # Live S1a: attempted proof with sorry fails strict verify cleanly.
            s1a = tmp_path / "s1a"
            (s1a / "Proof").mkdir(parents=True)
            (s1a / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            r1a = harness.evaluate_submission(
                scenario_id="s1a_ub_proof_hack",
                submission_dir=s1a,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual(r1a["verdict"], harness.VERDICT_DEFENDER_HELD, r1a)
            self.assertEqual(r1a["elaboration_sandbox"], "linux_bwrap", r1a)
            self.assertEqual(r1a["verify_taint_reasons"], [], r1a)

            # Live S1b: attempted proof on wrong_const() = 1 fails cleanly.
            s1b = tmp_path / "s1b"
            (s1b / "Proof").mkdir(parents=True)
            (s1b / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            r1b = harness.evaluate_submission(
                scenario_id="s1b_spec_violation_proof_hack",
                submission_dir=s1b,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual(r1b["verdict"], harness.VERDICT_DEFENDER_HELD, r1b)

            # Live S3: axiom in Spec/Spec.lean rejected by SpecPreflight.
            s3 = tmp_path / "s3"
            (s3 / "Spec").mkdir(parents=True)
            (s3 / "Spec/Spec.lean").write_text(
                "module\nprelude\npublic import Trusted.MirSemantics\n"
                "@[expose] public section\nnamespace Spec\n"
                "axiom smuggle : False\n"
                "noncomputable def specs : Trusted.MirSemantics.Specs :=\n"
                "  ⟨fun _ _ => True, fun _ => True⟩\n"
                "end Spec\nend\n"
            )
            r3 = harness.evaluate_submission(
                scenario_id="s3_spec_preflight_hack",
                submission_dir=s3,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual(r3["verdict"], harness.VERDICT_DEFENDER_HELD, r3)

            # Live S2: buggy code is caught by Miri/rustc oracle AND Anneal.
            s2_bug = tmp_path / "s2_bug"
            (s2_bug / "src").mkdir(parents=True)
            (s2_bug / "Proof").mkdir(parents=True)
            (s2_bug / "src/lib.rs").write_text(
                "pub fn target(x: u32) -> u32 { x.wrapping_add(1) }\n"
            )
            (s2_bug / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            r2_bug = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_bug,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
            )
            self.assertEqual(r2_bug["verdict"], harness.VERDICT_DEFENDER_HELD, r2_bug)
            self.assertEqual(
                r2_bug["code_oracle_status"], "spec_violation_confirmed", r2_bug
            )
            self.assertEqual(
                r2_bug["oracle_fault_class"], "spec_violation:wrong_return", r2_bug
            )
            self.assertTrue(r2_bug["oracle_incorrect_confirmed"])
            self.assertFalse(r2_bug["anneal_verify_ok"])

            # Live S2 UB via witness/args.json: Miri catches Tree Borrows UB.
            s2_ub = tmp_path / "s2_ub"
            (s2_ub / "src").mkdir(parents=True)
            (s2_ub / "Proof").mkdir(parents=True)
            (s2_ub / "witness").mkdir(parents=True)
            (s2_ub / "src/lib.rs").write_text(
                "pub fn target(x: u32) -> u32 {\n"
                "    if x == 77 {\n"
                "        let mut v = x;\n"
                "        let p = &raw mut v;\n"
                "        let r: &mut u32 = unsafe { &mut *p };\n"
                "        *r = x;\n"
                "        unsafe { *p = x; }\n"
                "        return *r;\n"
                "    }\n"
                "    x\n"
                "}\n"
            )
            (s2_ub / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            (s2_ub / "witness/args.json").write_text('{"args": [77]}\n')
            r2_ub = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_ub,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
            )
            self.assertEqual(r2_ub["verdict"], harness.VERDICT_DEFENDER_HELD, r2_ub)
            self.assertEqual(r2_ub["code_oracle_status"], "ub_confirmed", r2_ub)
            self.assertEqual(r2_ub["oracle_fault_class"], "ub:tree_borrows", r2_ub)
            self.assertTrue(r2_ub["oracle_incorrect_confirmed"])
            self.assertFalse(r2_ub["anneal_verify_ok"])

            # Live S2: reject `#[cfg(miri)]` Miri-vs-rustc split submissions.
            s2_cfg_miri = tmp_path / "s2_cfg_miri"
            (s2_cfg_miri / "src").mkdir(parents=True)
            (s2_cfg_miri / "Proof").mkdir(parents=True)
            (s2_cfg_miri / "src/lib.rs").write_text(
                "#[cfg(miri)]\n"
                "pub fn target(x: u32) -> u32 { x }\n"
                "#[cfg(not(miri))]\n"
                "pub fn target(x: u32) -> u32 { x.wrapping_add(1) }\n"
            )
            (s2_cfg_miri / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            r2_cfg_miri = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_cfg_miri,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
            )
            self.assertEqual(
                r2_cfg_miri["verdict"], harness.VERDICT_INVALID_SUBMISSION, r2_cfg_miri
            )

            # Live S2: early `std::process::exit(0)` fails completion nonce.
            s2_exit0 = tmp_path / "s2_exit0"
            (s2_exit0 / "src").mkdir(parents=True)
            (s2_exit0 / "Proof").mkdir(parents=True)
            (s2_exit0 / "src/lib.rs").write_text(
                "pub fn target(_x: u32) -> u32 { std::process::exit(0); }\n"
            )
            (s2_exit0 / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            r2_exit0 = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_exit0,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
            )
            self.assertEqual(r2_exit0["verdict"], harness.VERDICT_DEFENDER_HELD, r2_exit0)
            self.assertEqual(
                r2_exit0["code_oracle_status"], "spec_violation_confirmed", r2_exit0
            )
            self.assertTrue(r2_exit0["oracle_incorrect_confirmed"])

            # Live S2 (F1): reject `#[cfg(all(miri, not(debug_assertions)))]` &
            # `#[cfg(miri)] compile_error!` splits cleanly.
            s2_cfg_da = tmp_path / "s2_cfg_da"
            (s2_cfg_da / "src").mkdir(parents=True)
            (s2_cfg_da / "Proof").mkdir(parents=True)
            (s2_cfg_da / "src/lib.rs").write_text(
                "#[cfg(all(miri, not(debug_assertions)))]\n"
                "pub fn target(x: u32) -> u32 { x }\n"
                "#[cfg(not(all(miri, not(debug_assertions))))]\n"
                "pub fn target(x: u32) -> u32 { x.wrapping_add(1) }\n"
            )
            (s2_cfg_da / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            r2_cfg_da = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_cfg_da,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
            )
            self.assertEqual(
                r2_cfg_da["verdict"], harness.VERDICT_INVALID_SUBMISSION, r2_cfg_da
            )

            s2_cfg_ce = tmp_path / "s2_cfg_ce"
            (s2_cfg_ce / "src").mkdir(parents=True)
            (s2_cfg_ce / "Proof").mkdir(parents=True)
            (s2_cfg_ce / "src/lib.rs").write_text(
                '#[cfg(miri)] compile_error!("miri rejected");\n'
                "pub fn target(x: u32) -> u32 { x.wrapping_add(1) }\n"
            )
            (s2_cfg_ce / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            r2_cfg_ce = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_cfg_ce,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
            )
            self.assertEqual(
                r2_cfg_ce["verdict"], harness.VERDICT_INVALID_SUBMISSION, r2_cfg_ce
            )

            # Live S2 (F2): reject `file!()` path-sensitive Rust submissions.
            s2_file_macro = tmp_path / "s2_file_macro"
            (s2_file_macro / "src").mkdir(parents=True)
            (s2_file_macro / "Proof").mkdir(parents=True)
            (s2_file_macro / "src/lib.rs").write_text(
                'pub fn target(x: u32) -> u32 { if file!().contains("src") { x } else { 0 } }\n'
            )
            (s2_file_macro / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            r2_file = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_file_macro,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
            )
            self.assertEqual(
                r2_file["verdict"], harness.VERDICT_INVALID_SUBMISSION, r2_file
            )

            # Live S2 (F7): early `std::process::exit(7)` -> DEFENDER_HELD.
            s2_exit7 = tmp_path / "s2_exit7"
            (s2_exit7 / "src").mkdir(parents=True)
            (s2_exit7 / "Proof").mkdir(parents=True)
            (s2_exit7 / "src/lib.rs").write_text(
                "pub fn target(_x: u32) -> u32 { std::process::exit(7); }\n"
            )
            (s2_exit7 / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            r2_exit7 = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_exit7,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
            )
            self.assertEqual(r2_exit7["verdict"], harness.VERDICT_DEFENDER_HELD, r2_exit7)
            self.assertEqual(
                r2_exit7["code_oracle_status"], "spec_violation_confirmed", r2_exit7
            )
            self.assertTrue(r2_exit7["oracle_incorrect_confirmed"])

            # Live S2: clean identity code passes Miri oracle -> DEFENDER_HELD.
            s2_clean = tmp_path / "s2_clean"
            (s2_clean / "src").mkdir(parents=True)
            (s2_clean / "Proof").mkdir(parents=True)
            (s2_clean / "src/lib.rs").write_text(
                "pub fn target(x: u32) -> u32 { x }\n"
            )
            (s2_clean / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\n"
                "end Proof\n"
            )
            r2_clean = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_clean,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
            )
            self.assertEqual(r2_clean["verdict"], harness.VERDICT_DEFENDER_HELD, r2_clean)
            self.assertEqual(r2_clean["code_oracle_status"], "clean", r2_clean)
            self.assertFalse(r2_clean["oracle_incorrect_confirmed"])

    def test_live_s2_e1_semantics_patch_preservation_and_audit(self):
        tools = self._discover_or_skip()
        if shutil.which("bwrap") is None:
            if os.environ.get("ANNEAL_REDTEAM_REQUIRE_LIVE") == "1":
                self.fail("missing bwrap for live Tier-E1 test")
            self.skipTest("bwrap not present")

        spec = scenarios.get_scenario("s2_code_and_proof_hack")
        env = harness._build_scrubbed_env(
            tools.get("sysroot"),
            miri_sysroot=harness._discover_miri_sysroot(),
        )
        target_rs = (
            scenarios._HEADER_RS
            + "pub fn target(x: u32) -> u32 {\n"
            + "    if x == 3 { 0 } else { x }\n"
            + "}\n"
        )
        ops_lines = (
            _ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Ops.lean"
        ).read_text(encoding="utf-8").splitlines()
        eval_idx = next(
            i
            for i, line in enumerate(ops_lines)
            if line.startswith(
                "noncomputable def evalUnOp (op : UnOp) (v : Val) : Except FaultKind Val :="
            )
        )
        broken_start = eval_idx + 1
        broken_block = ops_lines[eval_idx : eval_idx + 8]
        old_decode = "    let integer := decodeScalar sv"
        self.assertIn(old_decode, broken_block)
        broken_hunk_lines: list[str] = []
        for line in broken_block:
            if line == old_decode:
                broken_hunk_lines.append(f"-{line}")
                broken_hunk_lines.append("+    let integer : Int := 0")
            else:
                broken_hunk_lines.append(f" {line}")
        broken_patch = "\n".join(
            [
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean",
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean",
                f"@@ -{broken_start},{len(broken_block)} +{broken_start},{len(broken_block)} @@",
                *broken_hunk_lines,
                "",
            ]
        )
        benign_start = eval_idx - 1
        benign_ctx_before = ops_lines[eval_idx - 2 : eval_idx]
        benign_ctx_after = ops_lines[eval_idx : eval_idx + 3]
        benign_patch = "\n".join(
            [
                "--- a/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean",
                "+++ b/anneal/trusted/lean/Trusted/MirSemantics/Ops.lean",
                f"@@ -{benign_start},{len(benign_ctx_before) + len(benign_ctx_after)} +{benign_start},{len(benign_ctx_before) + len(benign_ctx_after) + 1} @@",
                *(f" {line}" for line in benign_ctx_before),
                "+-- redteam E1 benign semantics patch canary",
                *(f" {line}" for line in benign_ctx_after),
                "",
            ]
        )
        e1_proof_lean = (
            scenarios._HEADER_LEAN
            + "module\n"
            + "prelude\n"
            + "public import IncorrectnessExpected\n"
            + "import Trusted.MirSemantics\n\n"
            + "namespace Proof\n\n"
            + "open Trusted.MirAst Trusted.MirSemantics\n\n"
            + "private theorem reaches_cons {p : Program} {s1 s2 s3 : State}\n"
            + "    (hStep : Step p s1 (.step s2)) (hRest : Reaches p s2 s3) :\n"
            + "    Reaches p s1 s3 := by\n"
            + "  induction hRest with\n"
            + "  | refl => exact Reaches.tail (Reaches.refl s1) hStep\n"
            + "  | tail _ hLast ih => exact Reaches.tail ih hLast\n\n"
            + "private def execDoneFrom (p : Program)\n"
            + "    (expected : TerminalOut) : Nat → State → Prop\n"
            + "  | 0, _ => False\n"
            + "  | fuel + 1, s =>\n"
            + "    match evalStep p 0 s with\n"
            + "    | .step s' => execDoneFrom p expected fuel s'\n"
            + "    | .done out => out = expected\n"
            + "    | .fault _ => False\n\n"
            + "private theorem reaches_done_of_execFrom {p : Program} {expected : TerminalOut} :\n"
            + "    ∀ {fuel : Nat} {s : State},\n"
            + "      execDoneFrom p expected fuel s →\n"
            + "      ∃ s', Reaches p s s' ∧ Step p s' (.done expected)\n"
            + "  | 0, _, h => False.elim h\n"
            + "  | fuel + 1, s, h => by\n"
            + "    dsimp [execDoneFrom] at h\n"
            + "    cases hStep : evalStep p 0 s with\n"
            + "    | step s1 =>\n"
            + "      rw [hStep] at h\n"
            + "      let ⟨s', hReach, hDone⟩ := reaches_done_of_execFrom h\n"
            + "      exact ⟨s', reaches_cons ⟨0, rfl, hStep⟩ hReach, hDone⟩\n"
            + "    | done out =>\n"
            + "      rw [hStep] at h\n"
            + "      subst h\n"
            + "      exact ⟨s, Reaches.refl s, ⟨0, rfl, hStep⟩⟩\n"
            + "    | fault _ =>\n"
            + "      rw [hStep] at h\n"
            + "      exact False.elim h\n\n"
            + "private theorem execDone_target_magic :\n"
            + "    match initState (entryProgForBody Captured.program 0)\n"
            + "      { args := [.scalar ⟨.i32, false, BitVec.ofNat 128 3⟩] } with\n"
            + "    | .error _ => False\n"
            + "    | .ok s0 =>\n"
            + "      execDoneFrom (entryProgForBody Captured.program 0)\n"
            + "        (.returned ⟨.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩, ⟨[]⟩⟩)\n"
            + "        32 s0 := rfl\n\n"
            + "private theorem behavior_target_magic :\n"
            + "    Behavior (entryProgForBody Captured.program 0)\n"
            + "      { args := [.scalar ⟨.i32, false, BitVec.ofNat 128 3⟩] }\n"
            + "      (.returned ⟨.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩, ⟨[]⟩⟩) := by\n"
            + "  have h := execDone_target_magic\n"
            + "  unfold Behavior ReachesResult\n"
            + "  cases hInit : initState (entryProgForBody Captured.program 0)\n"
            + "      { args := [.scalar ⟨.i32, false, BitVec.ofNat 128 3⟩] } with\n"
            + "  | error _ => rw [hInit] at h; exact False.elim h\n"
            + "  | ok s0 =>\n"
            + "    rw [hInit] at h\n"
            + "    exact reaches_done_of_execFrom h\n\n"
            + "public theorem verify : IncorrectnessExpected.claim := by\n"
            + "  intro hSpec\n"
            + "  let ⟨_, idx, body, hFound, _hId, hForall⟩ := hSpec\n"
            + "  cases idx with\n"
            + "  | zero =>\n"
            + "    let ⟨⟨_hWf, hPost⟩, _hNdiv⟩ := hForall (BitVec.ofNat 128 3) rfl\n"
            + "    have hEq := hPost\n"
            + "      (.returned ⟨.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩, ⟨[]⟩⟩)\n"
            + "      behavior_target_magic\n"
            + "    injection hEq with hRet\n"
            + "    injection hRet with hVal\n"
            + "    injection hVal with hSc\n"
            + "    injection hSc with _hW _hS hBits\n"
            + "    have hNat : (0 : Nat) = 3 := congrArg BitVec.toNat hBits\n"
            + "    cases hNat\n"
            + "  | succ k =>\n"
            + "    cases k <;> cases hFound\n\n"
            + "end Proof\n"
        )

        with tempfile.TemporaryDirectory(prefix="rt-live-e1-") as tmp:
            tmp_path = Path(tmp)

            # Capture real compiler MIR (`Captured.lean`) for
            # `if x == 3 { 0 } else { x }`.
            cap_work = tmp_path / "cap_work"
            cap_arts = tmp_path / "cap_arts"
            cap_receipt = tmp_path / "cap_receipt.json"
            (cap_work / "src").mkdir(parents=True)
            (cap_work / "Cargo.toml").write_text(scenarios._S2_CARGO_TOML, encoding="utf-8")
            (cap_work / "Spec.lean").write_text(scenarios._S2_SPEC_LEAN, encoding="utf-8")
            (cap_work / "src/lib.rs").write_text(target_rs, encoding="utf-8")
            (cap_work / "Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\nend Proof\n",
                encoding="utf-8",
            )
            cap_req = cap_work / "request.json"
            cap_req.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "compilation": {
                            "source_root": ".",
                            "crate_root": "src/lib.rs",
                            "crate_name": "redteam_s2",
                            "edition": "2024",
                            "source_files": ["src/lib.rs"],
                        },
                        "scope": {"kind": "crate"},
                        "proof": {
                            "source_root": ".",
                            "sources": [
                                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                                {"module": "Proof", "path": "Proof.lean", "role": "proof"},
                            ],
                        },
                    },
                    indent=2,
                )
                + "\n",
                encoding="utf-8",
            )
            anneal_ci_lib.run_cargo_anneal_verify(
                cli=tools["cli"],
                request_path=cap_req,
                cwd=cap_work,
                capture=tools["capture"],
                sysroot=tools["sysroot"],
                lean=tools["lean"],
                artifacts_dir=cap_arts,
                extra_flags=["--receipt-out", str(cap_receipt)],
                env=env,
                timeout=300.0,
                label="live-e1-capture",
            )
            real_captured = cap_arts / "capture" / "Captured.lean"
            self.assertTrue(real_captured.is_file(), "expected real Captured.lean")

            def _sim_unsound_verify(cmd, *, cwd, env, timeout):
                art_idx = cmd.index("--artifacts")
                art_dir = Path(cmd[art_idx + 1])
                (art_dir / "capture").mkdir(parents=True, exist_ok=True)
                shutil.copy2(real_captured, art_dir / "capture" / "Captured.lean")
                payload = _clean_receipt(scope_kind="crate")
                rec_idx = cmd.index("--receipt-out")
                Path(cmd[rec_idx + 1]).write_text(json.dumps(payload), encoding="utf-8")
                return subprocess.CompletedProcess(
                    cmd, 0, stdout=json.dumps(payload), stderr=""
                )

            # Case A: Real broken `Ops.lean` `.not` semantics patch is caught by
            # Gate 4A (`patched_auditor`) and fails closed as `DEFENDER_HELD`.
            sub_bad = tmp_path / "sub_bad"
            (sub_bad / "src").mkdir(parents=True)
            (sub_bad / "Proof").mkdir(parents=True)
            (sub_bad / "incorrectness").mkdir(parents=True)
            (sub_bad / "src/lib.rs").write_text(target_rs, encoding="utf-8")
            (sub_bad / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\nend Proof\n",
                encoding="utf-8",
            )
            (sub_bad / "incorrectness/semantics.patch").write_text(
                broken_patch, encoding="utf-8"
            )
            (sub_bad / "incorrectness/Proof.lean").write_text(
                e1_proof_lean, encoding="utf-8"
            )
            res_bad = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=sub_bad,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=900,
                verify_runner=_sim_unsound_verify,
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(res_bad["verdict"], harness.VERDICT_DEFENDER_HELD, res_bad)
            self.assertEqual(res_bad["code_oracle_status"], "clean", res_bad)
            self.assertIs(res_bad["preservation_gate_passed"], False, res_bad)
            self.assertFalse(res_bad["patch_incorrectness_verified"], res_bad)
            self.assertIs(
                res_bad["trace_artifacts"]["preservation_canary_summary"][
                    "theory_canaries_verified"
                ],
                False,
                res_bad,
            )
            self.assertIn(
                "Preservation Canary Gate failed",
                res_bad["trace_artifacts"]["preservation_canary_summary"]["detail"],
                res_bad,
            )

            # Case B: Benign comment patch passes live Gate 4A, live Gate 4B
            # (`target(x) = x`), and live sandboxed `bwrap` `TrustedBoundary`
            # preflight/headers/audit -> `NEEDS_HUMAN_REVIEW` (P1).
            sub_ok = tmp_path / "sub_ok"
            (sub_ok / "src").mkdir(parents=True)
            (sub_ok / "Proof").mkdir(parents=True)
            (sub_ok / "incorrectness").mkdir(parents=True)
            (sub_ok / "src/lib.rs").write_text(target_rs, encoding="utf-8")
            (sub_ok / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\nend Proof\n",
                encoding="utf-8",
            )
            (sub_ok / "incorrectness/semantics.patch").write_text(
                benign_patch, encoding="utf-8"
            )
            (sub_ok / "incorrectness/Proof.lean").write_text(
                e1_proof_lean, encoding="utf-8"
            )
            res_ok = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=sub_ok,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=900,
                verify_runner=_sim_unsound_verify,
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(
                res_ok["verdict"], harness.VERDICT_NEEDS_HUMAN_REVIEW, res_ok
            )
            self.assertEqual(res_ok["code_oracle_status"], "clean", res_ok)
            self.assertEqual(
                res_ok["incorrectness_evidence_tier"],
                harness.TIER_LEAN_PATCH_PROOF,
                res_ok,
            )
            self.assertTrue(res_ok["patch_incorrectness_verified"], res_ok)
            self.assertIs(res_ok["preservation_gate_passed"], True, res_ok)
            self.assertTrue(res_ok["human_review_required"], res_ok)
            self.assertEqual(res_ok["proposed_severity"], "P1", res_ok)
            self.assertTrue(res_ok["dedup"]["bug_id"].startswith("RT-CPH-"), res_ok)
            self.assertTrue(
                res_ok["trace_artifacts"]["incorrectness_proof_audit"]["replay"], res_ok
            )

    def test_live_r2_oracle_and_e1_binding_hardening(self):
        tools = self._discover_or_skip()
        if shutil.which("bwrap") is None:
            if os.environ.get("ANNEAL_REDTEAM_REQUIRE_LIVE") == "1":
                self.fail("missing bwrap for live R2 test")
            self.skipTest("bwrap not present")

        bwrap = Path(shutil.which("bwrap"))
        lean_bin = tools["lean"]
        lean_sysroot = harness._resolve_lean_sysroot(lean_bin, {})
        env = harness._build_scrubbed_env(
            tools.get("sysroot"),
            miri_sysroot=harness._discover_miri_sysroot(),
        )
        check_src = (
            scenarios._HEADER_LEAN
            + "module\nprelude\n"
            + "public import IncorrectnessExpected\n"
            + "public import Proof\n\n"
            + "public theorem IncorrectnessCheck.verified :\n"
            + "    _root_.IncorrectnessExpected.claim :=\n"
            + "  _root_.Proof.verify\n"
        )

        with tempfile.TemporaryDirectory(prefix="rt-live-r2-") as tmp:
            tmp_path = Path(tmp)

            # R2-2 (live Lean 4.34.1): Check namespace shadow compile rejection,
            # reserved-namespace constant rejection, and Kernel.isDefEq check.
            b_src = tmp_path / "bind_src"
            b_out = tmp_path / "bind_out"
            b_src.mkdir()
            b_out.mkdir()
            (b_src / "IncorrectnessExpected.lean").write_text(
                "module\nprelude\n"
                "@[expose] public section\n"
                "namespace IncorrectnessExpected\n"
                "def claim : Prop := ∀ (p : Prop), p → p\n"
                "end IncorrectnessExpected\nend\n",
                encoding="utf-8",
            )
            (b_src / "IncorrectnessCheck.lean").write_text(
                check_src, encoding="utf-8"
            )
            # Case 1: Shadowing `namespace IncorrectnessCheck` fails
            # compilation.
            (b_src / "Proof.lean").write_text(
                "module\nprelude\n"
                "namespace IncorrectnessCheck\n"
                "namespace IncorrectnessExpected\n"
                "public def claim : Prop := ∀ (p : Prop), p → p\n"
                "end IncorrectnessExpected\n"
                "namespace Proof\n"
                "public theorem verify : IncorrectnessExpected.claim := fun _ h => h\n"
                "end Proof\nend IncorrectnessCheck\n",
                encoding="utf-8",
            )
            ok_sh, _ = harness._compile_lean_modules_in_bwrap(
                bwrap=bwrap,
                lean_bin=lean_bin,
                lean_sysroot=lean_sysroot,
                modules=["IncorrectnessExpected", "Proof", "IncorrectnessCheck"],
                src_host=b_src,
                src_box="/work/bind_src",
                out_host=b_out,
                out_box="/work/bind_out",
                extra_ro_mounts=[],
                lean_path_mounts=["/work/bind_out"],
                timeout=60,
            )
            self.assertFalse(ok_sh)

            # Case 2: Valid `_root_.Proof.verify` + reserved
            # `IncorrectnessCheck.decoy` compiles `.olean`, then fails
            # `verify_e1_kernel_binding_in_bwrap`.
            (b_src / "Proof.lean").write_text(
                "module\nprelude\npublic import IncorrectnessExpected\n"
                "namespace Proof\n"
                "public theorem verify : IncorrectnessExpected.claim := fun _ h => h\n"
                "end Proof\n"
                "public theorem IncorrectnessCheck.decoy :\n"
                "    ∀ (p : Prop), p → p := fun _ h => h\n",
                encoding="utf-8",
            )
            for p in b_out.glob("*"):
                p.unlink()
            ok_resv, err_resv = harness._compile_lean_modules_in_bwrap(
                bwrap=bwrap,
                lean_bin=lean_bin,
                lean_sysroot=lean_sysroot,
                modules=["IncorrectnessExpected", "Proof", "IncorrectnessCheck"],
                src_host=b_src,
                src_box="/work/bind_src",
                out_host=b_out,
                out_box="/work/bind_out",
                extra_ro_mounts=[],
                lean_path_mounts=["/work/bind_out"],
                timeout=60,
            )
            self.assertTrue(ok_resv, err_resv)
            sysroot_lib = lean_sysroot / "lib/lean"
            e1_mods = ["Init", "IncorrectnessExpected", "Proof", "IncorrectnessCheck"]
            arts_map: dict[str, list[list[str]]] = {}
            init_arts = harness._discover_module_artifacts(
                {"Init": sysroot_lib / "Init"}
            )
            arts_map["Init"] = [
                [p.replace(str(sysroot_lib), "/toolchain/lib/lean") for p in init_arts["Init"][0]],
                [p.replace(str(sysroot_lib), "/toolchain/lib/lean") for p in init_arts["Init"][1]],
            ]
            local_arts = harness._discover_module_artifacts(
                {m: b_out / m for m in ("IncorrectnessExpected", "Proof", "IncorrectnessCheck")}
            )
            for m, (op, ip) in local_arts.items():
                arts_map[m] = [
                    [p.replace(str(b_out), "/work/bind_out") for p in op],
                    [p.replace(str(b_out), "/work/bind_out") for p in ip],
                ]
            bind_bad, msg_bad = lean_ast.verify_e1_kernel_binding_in_bwrap(
                bwrap=bwrap,
                lean_bin=lean_bin,
                lean_sysroot=lean_sysroot,
                bwrap_runner=harness._run_lean_in_bwrap,
                ro_mounts=[(b_out, "/work/bind_out")],
                modules=e1_mods,
                attacker_modules=["Proof"],
                artifacts_json=[[m, arts_map[m]] for m in e1_mods],
                timeout=60,
            )
            self.assertFalse(bind_bad)
            self.assertIn("reserved constant", msg_bad)

            # Case 3: Honest Proof.verify passes
            # `verify_e1_kernel_binding_in_bwrap`.
            (b_src / "Proof.lean").write_text(
                "module\nprelude\npublic import IncorrectnessExpected\n"
                "namespace Proof\n"
                "public theorem verify : IncorrectnessExpected.claim := fun _ h => h\n"
                "end Proof\n",
                encoding="utf-8",
            )
            for p in b_out.glob("*"):
                p.unlink()
            ok_good, err_good = harness._compile_lean_modules_in_bwrap(
                bwrap=bwrap,
                lean_bin=lean_bin,
                lean_sysroot=lean_sysroot,
                modules=["IncorrectnessExpected", "Proof", "IncorrectnessCheck"],
                src_host=b_src,
                src_box="/work/bind_src",
                out_host=b_out,
                out_box="/work/bind_out",
                extra_ro_mounts=[],
                lean_path_mounts=["/work/bind_out"],
                timeout=60,
            )
            self.assertTrue(ok_good, err_good)
            local_arts = harness._discover_module_artifacts(
                {m: b_out / m for m in ("IncorrectnessExpected", "Proof", "IncorrectnessCheck")}
            )
            for m, (op, ip) in local_arts.items():
                arts_map[m] = [
                    [p.replace(str(b_out), "/work/bind_out") for p in op],
                    [p.replace(str(b_out), "/work/bind_out") for p in ip],
                ]
            bind_good, msg_good = lean_ast.verify_e1_kernel_binding_in_bwrap(
                bwrap=bwrap,
                lean_bin=lean_bin,
                lean_sysroot=lean_sysroot,
                bwrap_runner=harness._run_lean_in_bwrap,
                ro_mounts=[(b_out, "/work/bind_out")],
                modules=e1_mods,
                attacker_modules=["Proof"],
                artifacts_json=[[m, arts_map[m]] for m in e1_mods],
                timeout=60,
            )
            self.assertTrue(bind_good, msg_good)
            bind_tamper, msg_tamper = lean_ast.verify_e1_kernel_binding_in_bwrap(
                bwrap=bwrap,
                lean_bin=lean_bin,
                lean_sysroot=lean_sysroot,
                bwrap_runner=harness._run_lean_in_bwrap,
                ro_mounts=[(b_out, "/work/bind_out")],
                modules=e1_mods,
                attacker_modules=["Proof"],
                artifacts_json=[[m, arts_map[m]] for m in e1_mods],
                require_s2_claim=True,
                timeout=60,
            )
            self.assertFalse(bind_tamper, msg_tamper)
            self.assertIn("IncorrectnessExpected.claim", msg_tamper)

            # Case 4 (live Lean 4.34.1): Proof unfolding/simplifying an
            # upstream `Trusted.*` match definition and `IncorrectnessExpected`
            # claim emits realized equation/splitter helpers in `Proof.olean`
            # under reserved roots and must pass kernel binding.
            (b_src / "Trusted").mkdir(parents=True, exist_ok=True)
            (b_src / "Trusted/Helper.lean").write_text(
                "module\nprelude\npublic import Init\n"
                "@[expose] public section\n"
                "namespace Trusted\n"
                "def matchStep (n : Nat) : Nat :=\n"
                "  match n with\n"
                "  | 0 => 1\n"
                "  | _ + 1 => 2\n"
                "end Trusted\nend\n",
                encoding="utf-8",
            )
            (b_src / "IncorrectnessExpected.lean").write_text(
                "module\nprelude\npublic import Trusted.Helper\n"
                "@[expose] public section\n"
                "namespace IncorrectnessExpected\n"
                "def claim : Prop := Trusted.matchStep 0 = 1\n"
                "end IncorrectnessExpected\nend\n",
                encoding="utf-8",
            )
            (b_src / "Proof.lean").write_text(
                "module\nprelude\npublic import Init\npublic import IncorrectnessExpected\n"
                "namespace Proof\n"
                "public theorem verify : IncorrectnessExpected.claim := by\n"
                "  unfold IncorrectnessExpected.claim\n"
                "  simp [Trusted.matchStep]\n"
                "end Proof\n",
                encoding="utf-8",
            )
            for p in b_out.glob("*"):
                if p.is_dir():
                    shutil.rmtree(p)
                else:
                    p.unlink()
            ok_real, err_real = harness._compile_lean_modules_in_bwrap(
                bwrap=bwrap,
                lean_bin=lean_bin,
                lean_sysroot=lean_sysroot,
                modules=[
                    "Trusted.Helper",
                    "IncorrectnessExpected",
                    "Proof",
                    "IncorrectnessCheck",
                ],
                src_host=b_src,
                src_box="/work/bind_src",
                out_host=b_out,
                out_box="/work/bind_out",
                extra_ro_mounts=[],
                lean_path_mounts=["/work/bind_out"],
                timeout=60,
            )
            self.assertTrue(ok_real, err_real)
            e1_mods_r = [
                "Init",
                "Trusted.Helper",
                "IncorrectnessExpected",
                "Proof",
                "IncorrectnessCheck",
            ]
            local_arts_r = harness._discover_module_artifacts(
                {
                    m: b_out / m.replace(".", "/")
                    for m in (
                        "Trusted.Helper",
                        "IncorrectnessExpected",
                        "Proof",
                        "IncorrectnessCheck",
                    )
                }
            )
            for m, (op, ip) in local_arts_r.items():
                arts_map[m] = [
                    [p.replace(str(b_out), "/work/bind_out") for p in op],
                    [p.replace(str(b_out), "/work/bind_out") for p in ip],
                ]
            bind_real, msg_real = lean_ast.verify_e1_kernel_binding_in_bwrap(
                bwrap=bwrap,
                lean_bin=lean_bin,
                lean_sysroot=lean_sysroot,
                bwrap_runner=harness._run_lean_in_bwrap,
                ro_mounts=[(b_out, "/work/bind_out")],
                modules=e1_mods_r,
                attacker_modules=["Proof"],
                artifacts_json=[[m, arts_map[m]] for m in e1_mods_r],
                timeout=60,
            )
            self.assertTrue(bind_real, msg_real)

            # Live Lean 4.34.1 AST oracle check for forbidden theory constructs.
            hdr = "module\nprelude\npublic import Init.Core\n"
            for label, src, expect_tag in (
                ("live_opaque", hdr + "opaque bad : Nat := 0\n", "opaque"),
                ("live_trusted_ns", hdr + "namespace Trusted\ndef x : Nat := 0\nend Trusted\n", "decl_ns:Trusted"),
                ("live_trusted_def", hdr + "def Trusted.x : Nat := 0\n", "decl_ns:Trusted"),
                ("live_root_nat_add", hdr + "theorem _root_.Nat.add (a : Nat) : a = a := rfl\n", "ident:_root_.Nat.add"),
                ("live_nat_def", hdr + "def Nat.custom : Nat := 0\n", "decl_ns:Nat"),
                ("live_bare_nat", hdr + "def Nat : Type := Unit\n", "decl_ns:Nat"),
            ):
                pe_g2: list[str] = []
                tags_g2 = harness._detect_disallowed_lean_constructs_with_tools(
                    {"theory/Anneal/Ok.lean": src},
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                    lean_bin=lean_bin,
                    env=env,
                    allow_fallback=False,
                    parse_errors_out=pe_g2,
                    anneal_root=_ANNEAL_ROOT,
                )
                self.assertEqual(pe_g2, [], (label, pe_g2))
                self.assertIn(expect_tag, tags_g2, (label, tags_g2))
            for unpinned_mod in ("Std.Net", "Init", "Init.Data.ToString.Macro"):
                pe_unp: list[str] = []
                tags_unp = harness._detect_disallowed_lean_constructs_with_tools(
                    {
                        "theory/Anneal/BadImp.lean": (
                            "module\nprelude\npublic import Init.Core\n"
                            f"public import {unpinned_mod}\n"
                            "def ok : Nat := 0\n"
                        )
                    },
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                    lean_bin=lean_bin,
                    env=env,
                    allow_fallback=False,
                    parse_errors_out=pe_unp,
                    anneal_root=_ANNEAL_ROOT,
                )
                self.assertEqual(pe_unp, [], (unpinned_mod, pe_unp))
                self.assertIn(f"disallowed_import:{unpinned_mod}", tags_unp, tags_unp)

            # R2-3 / R2-4 / R2-5 live S2 oracle hardening verification.
            s2_deep = tmp_path / "s2_deep_rec"
            (s2_deep / "src").mkdir(parents=True)
            (s2_deep / "Proof").mkdir(parents=True)
            (s2_deep / "src/lib.rs").write_text(
                "#[inline(never)]\n"
                "fn rec(n: u32) -> u32 { if n == 0 { 0 } else { rec(n - 1) } }\n"
                "pub fn target(x: u32) -> u32 {\n"
                "    if x == 0 { rec(400_000) } else { x }\n"
                "}\n",
                encoding="utf-8",
            )
            (s2_deep / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\nend Proof\n",
                encoding="utf-8",
            )
            r_deep = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_deep,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_deep["verdict"], harness.VERDICT_DEFENDER_HELD, r_deep)
            self.assertEqual(r_deep["code_oracle_status"], "clean", r_deep)
            self.assertFalse(r_deep["oracle_incorrect_confirmed"], r_deep)

            s2_depr = tmp_path / "s2_depr_spoof"
            (s2_depr / "src").mkdir(parents=True)
            (s2_depr / "Proof").mkdir(parents=True)
            (s2_depr / "src/lib.rs").write_text(
                "#![deny(deprecated)]\n"
                '#[deprecated(note = "could not compile `core`")]\n'
                "pub fn old_f() {}\n"
                "pub fn target(x: u32) -> u32 { old_f(); x }\n",
                encoding="utf-8",
            )
            (s2_depr / "Proof/Proof.lean").write_text(
                "module\nprelude\npublic import Expected\n"
                "namespace Proof\npublic theorem verify : Expected.claim := by sorry\nend Proof\n",
                encoding="utf-8",
            )
            r_depr = harness.evaluate_submission(
                scenario_id="s2_code_and_proof_hack",
                submission_dir=s2_depr,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
                verify_runner=_mock_verify_pass(scope_kind="crate"),
                inspect_runner=_mock_inspect_pass(),
            )
            self.assertEqual(r_depr["verdict"], harness.VERDICT_INVALID_SUBMISSION, r_depr)
            self.assertEqual(r_depr["code_oracle_status"], "compile_error", r_depr)

            fake_bw_dir = tmp_path / "fake_bw"
            fake_bw_dir.mkdir()
            (fake_bw_dir / "bwrap").write_text(
                "#!/bin/sh\necho 'bwrap: denied' >&2\nexit 1\n", encoding="utf-8"
            )
            (fake_bw_dir / "bwrap").chmod(0o755)
            old_path = os.environ.get("PATH", "")
            os.environ["PATH"] = f"{fake_bw_dir}:{old_path}"
            try:
                with self.assertRaises(harness.OracleInfrastructureError):
                    harness._run_s2_code_oracle(
                        tmp_root=tmp_path / "broken_bw_oracle",
                        src_files={
                            "src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"
                        },
                        inputs=[0],
                        env=env,
                        timeout=30,
                        sysroot=tools["sysroot"],
                    )
            finally:
                os.environ["PATH"] = old_path

    def test_live_s4_sandboxed_audit_and_natbitwise(self):
        tools = self._discover_or_skip()
        if tools.get("auditor") is None:
            if os.environ.get("ANNEAL_REDTEAM_REQUIRE_LIVE") == "1":
                self.fail("missing local anneal-audit for live S4 test")
            self.skipTest("anneal-audit binary not built")
        if shutil.which("bwrap") is None:
            if os.environ.get("ANNEAL_REDTEAM_REQUIRE_LIVE") == "1":
                self.fail("missing bwrap for live S4 test")
            self.skipTest("bwrap not present")

        nat_bitwise = (_ANNEAL_ROOT / "theory/Anneal/NatBitwise.lean").read_text(
            encoding="utf-8"
        )
        with tempfile.TemporaryDirectory(prefix="rt-live-s4-") as tmp:
            s4_dir = Path(tmp) / "s4_nat"
            (s4_dir / "theory/Anneal").mkdir(parents=True)
            (s4_dir / "theory/Anneal/NatBitwise.lean").write_text(
                nat_bitwise, encoding="utf-8"
            )
            res = harness.evaluate_submission(
                scenario_id="s4_theory_audit_hack",
                submission_dir=s4_dir,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=900,
            )
            self.assertEqual(res["verdict"], harness.VERDICT_DEFENDER_HELD, res)
            self.assertTrue(res["anneal_verify_ok"], res)
            self.assertTrue(res["anneal_inspect_ok"], res)
            self.assertIsNone(res["dedup"], res)

    def test_live_r3_benign_s3_and_oracle_inconclusive_hardening(self):
        """Live S3 AST/benign parity, `.init_array`, cargo-json, & Miri oracle checks."""
        tools = self._discover_or_skip()
        lean_bin = tools["lean"]
        sysroot = tools["sysroot"]
        miri_sysroot = harness._discover_miri_sysroot()
        self.assertIsNotNone(miri_sysroot)
        env = harness._build_scrubbed_env(sysroot, miri_sysroot=miri_sysroot)
        hdr = "module\nprelude\npublic import Init\n"

        with tempfile.TemporaryDirectory(prefix="rt-live-r3-") as tmp:
            tmp_path = Path(tmp)

            # 1. Real Lean AST inspector: zero false positives on benign Lean,
            # complete coverage of SpecPreflight + TrustedBoundary constructs,
            # and O(1) HashSet bounded output on 85k symbols.
            benign_s3 = {
                "Spec/Spec.lean": hdr
                + "open scoped Nat\n"
                + "open List\n"
                + "def perm12 : Prop := [1, 2] ~ [2, 1]\n"
                + "def ex_s : Prop := ∃ sorryAx : Nat, sorryAx = 0\n"
                + "variable (sorryAx : Nat)\n"
                + "structure H where\n  sorryAx : Nat\n"
                + "namespace sorryAx\ndef x : Nat := 1\nend sorryAx\n"
            }
            pe: list[str] = []
            self.assertEqual(
                harness._detect_disallowed_lean_constructs_with_tools(
                    benign_s3,
                    allow_theory_import_all=False,
                    allow_spec_options=True,
                    lean_bin=lean_bin,
                    env=env,
                    allow_fallback=False,
                    parse_errors_out=pe,
                ),
                [],
            )
            self.assertEqual(pe, [])

            for name, body in (
                ("nonmod_public", "prelude\nimport Init.Core\npublic def p : Nat := 0\n"),
                ("reduceBool", "module\nprelude\npublic import Init.Core\ndef rb (b : Bool) := Lean.reduceBool b\n"),
                (
                    "ex_sorryAx",
                    "module\nprelude\npublic import Init.Core\n"
                    "public import Init.NotationExtra\n"
                    "def p : Prop := ∃ sorryAx : Nat, sorryAx = 0\n",
                ),
            ):
                pe_th: list[str] = []
                tags_th = harness._detect_disallowed_lean_constructs_with_tools(
                    {"theory/Anneal/Ok.lean": body},
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                    lean_bin=lean_bin,
                    env=env,
                    allow_fallback=False,
                    parse_errors_out=pe_th,
                )
                self.assertEqual((name, tags_th, pe_th), (name, [], []))

            for name, body in (
                ("getElem_bang", "def a (xs : Array Nat) : Nat := xs[0]!\n"),
                ("decl_name", "def b := decl_name%\n"),
                ("mod_cast", "theorem k (a : Nat) : (a : Int) = a := mod_cast rfl\n"),
                (
                    "do_while",
                    "def e : Nat := Id.run do\n  let mut i := 0\n"
                    "  while i < 3 do\n    i := i + 1\n  return i\n",
                ),
                ("head_bang", "def d (xs : List Nat) : Nat := xs.head!\n"),
                ("autoParam", "def h (n : Nat) (p : autoParam (n = n) x) : Nat := n\n"),
                ("root_succ", "def c : Nat := _root_.Nat.succ 0\n"),
                ("decl_nat", "def Nat.r3foo : Nat := 0\n"),
                ("ns_std", "namespace Std\ndef r3x : Nat := 0\nend Std\n"),
                (
                    "deriving_typename",
                    "structure S where\n  x : Nat\n  deriving TypeName\n",
                ),
            ):
                pe_a: list[str] = []
                hits = harness._detect_disallowed_lean_constructs_with_tools(
                    {"Spec/Spec.lean": hdr + body},
                    allow_theory_import_all=False,
                    allow_spec_options=True,
                    lean_bin=lean_bin,
                    env=env,
                    allow_fallback=False,
                    parse_errors_out=pe_a,
                )
                self.assertTrue(hits, f"expected Spec AST hit for {name}")
                self.assertEqual(pe_a, [], f"unexpected parse error for {name}: {pe_a}")

            theory_hdr = "module\nprelude\npublic import Init.Data.Nat.Basic\n"
            for name, text in (
                ("omega", theory_hdr + "theorem t (a b : Nat) (h : a ≤ b) : a < b + 1 := by omega\n"),
                ("simp_all", theory_hdr + "theorem t2 (p : Prop) (h : p) : p := by simp_all\n"),
                ("deriving_beq", theory_hdr + "structure P where\n  x : Nat\n  deriving BEq\n"),
                (
                    "term_by",
                    theory_hdr + "def r : Nat → Nat | 0 => 0 | k + 1 => r k\ntermination_by x => x\n",
                ),
                ("hash_check", theory_hdr + "#check Nat\n"),
                ("macro_decl", theory_hdr + 'macro "z" : term => `(0)\n'),
                ("bv_decide", theory_hdr + "theorem bv : True := by bv_decide\n"),
                ("do_block", theory_hdr + "def u : Nat := Id.run do\n  let x := 1\n  return x\n"),
                ("open_only", theory_hdr + "open Nat (succ)\n"),
                ("noncomp_sec", theory_hdr + "noncomputable section\ndef q : Nat := 0\nend\n"),
                ("missing_prelude", "module\npublic import Init.Data.Nat.Basic\ndef q : Nat := 0\n"),
            ):
                pe_t: list[str] = []
                hits = harness._detect_disallowed_lean_constructs_with_tools(
                    {"theory/Anneal/Ok.lean": text},
                    allow_theory_import_all=True,
                    allow_spec_options=False,
                    lean_bin=lean_bin,
                    env=env,
                    allow_fallback=False,
                    parse_errors_out=pe_t,
                )
                self.assertTrue(
                    any(not tag.startswith("disallowed_import:") for tag in hits),
                    f"expected Theory AST construct/prelude hit for {name}, got {hits}",
                )
                self.assertEqual(pe_t, [], f"unexpected parse error for {name}: {pe_t}")

            # `s!"..."` is rejected at parse time under foundationModules
            # (`Init.Data.ToString.Macro` absent), matching `TrustedBoundary`.
            pe_interp: list[str] = []
            hits_interp = harness._detect_disallowed_lean_constructs_with_tools(
                {"theory/Anneal/Ok.lean": theory_hdr + 'def s : String := s!"a{1}"\n'},
                allow_theory_import_all=True,
                allow_spec_options=False,
                lean_bin=lean_bin,
                env=env,
                allow_fallback=False,
                parse_errors_out=pe_interp,
            )
            self.assertEqual((hits_interp, pe_interp), ([], ["parse_error"]))

            # 85k unique IO.aN symbols stay fast and capped cleanly.
            many_refs = hdr + "\n".join(f"def d{i} := IO.a{i}" for i in range(85_000)) + "\n"
            pe_big: list[str] = []
            tags_big = harness._detect_disallowed_lean_constructs_with_tools(
                {"Spec/Spec.lean": many_refs},
                allow_theory_import_all=False,
                allow_spec_options=True,
                lean_bin=lean_bin,
                env=env,
                allow_fallback=False,
                parse_errors_out=pe_big,
            )
            self.assertEqual(len(tags_big), 128)
            self.assertEqual(pe_big, [])

            # 2. Live S3 check on benign `open scoped` & `∃ sorryAx`.
            s3_ben = tmp_path / "s3_benign_live"
            (s3_ben / "Spec").mkdir(parents=True)
            (s3_ben / "Spec/Spec.lean").write_text(
                "module\nprelude\npublic import Init\n"
                "open scoped Nat\n"
                "open List\n"
                "def perm12 : Prop := [1, 2] ~ [2, 1]\n"
                "def ex_s : Prop := ∃ sorryAx : Nat, sorryAx = 0\n",
                encoding="utf-8",
            )
            r_s3 = harness.evaluate_submission(
                scenario_id="s3_spec_preflight_hack",
                submission_dir=s3_ben,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=120,
            )
            self.assertEqual(r_s3["verdict"], harness.VERDICT_DEFENDER_HELD, r_s3)

            # 3. Live S2 pre-main `.init_array` exit(0) is rejected fail-closed
            # (`InvalidSubmissionError`), unwinding panics exit 43 cleanly
            # (`spec_violation_confirmed`), fake stdout Cargo JSON, and
            # `std::process::abort()` -> `spec_violation_confirmed`.
            init_rs = (
                'unsafe extern "C" { fn _exit(status: i32) -> !; }\n'
                '#[used]\n#[unsafe(link_section = ".init_array")]\n'
                'static F: unsafe extern "C" fn() = f;\n'
                'unsafe extern "C" fn f() { unsafe { _exit(0); } }\n'
                "pub fn target(x: u32) -> u32 { x }\n"
            )
            with self.assertRaisesRegex(
                harness.InvalidSubmissionError, r"\.init_array"
            ):
                harness._run_s2_code_oracle(
                    tmp_root=tmp_path / "oracle_init_exit",
                    src_files={"src/lib.rs": init_rs.encode("utf-8")},
                    inputs=[0],
                    env=env,
                    timeout=60,
                    sysroot=sysroot,
                )

            unwind_rs = (
                "pub fn target(_x: u32) -> u32 {\n"
                '    panic!("unwinding panic");\n'
                "}\n"
            )
            st_uw, fc_uw, _ = harness._run_s2_code_oracle(
                tmp_root=tmp_path / "oracle_unwind_panic",
                src_files={"src/lib.rs": unwind_rs.encode("utf-8")},
                inputs=[0],
                env=env,
                timeout=60,
                sysroot=sysroot,
            )
            self.assertEqual(
                (st_uw, fc_uw),
                ("spec_violation_confirmed", "spec_violation:panic_or_abort"),
            )

            fake_json_rs = (
                "pub fn target(_x: u32) -> u32 {\n"
                '    println!("{{\\"reason\\":\\"compiler-message\\",'
                '\\"package_id\\":\\"core 0.0.0\\",'
                '\\"manifest_path\\":\\"/toolchain/core/Cargo.toml\\",'
                '\\"message\\":{{\\"level\\":\\"error\\",\\"rendered\\":\\"fake\\"}}}}");\n'
                "    panic!(\"boom\");\n"
                "}\n"
            )
            st_fj, fc_fj, _ = harness._run_s2_code_oracle(
                tmp_root=tmp_path / "oracle_fake_json",
                src_files={"src/lib.rs": fake_json_rs.encode("utf-8")},
                inputs=[0],
                env=env,
                timeout=60,
                sysroot=sysroot,
            )
            self.assertEqual(
                (st_fj, fc_fj),
                ("spec_violation_confirmed", "spec_violation:panic_or_abort"),
            )

            leak_rs = "pub fn target(_x: u32) -> u32 { Box::leak(Box::new(1u32)); 0 }\n"
            st_lk, fc_lk, _ = harness._run_s2_code_oracle(
                tmp_root=tmp_path / "oracle_leak",
                src_files={"src/lib.rs": leak_rs.encode("utf-8")},
                inputs=[0],
                env=env,
                timeout=60,
                sysroot=sysroot,
            )
            self.assertEqual((st_lk, fc_lk), ("oracle_inconclusive", None))

            abort_rs = "pub fn target(_x: u32) -> u32 { std::process::abort(); }\n"
            st_ab, fc_ab, _ = harness._run_s2_code_oracle(
                tmp_root=tmp_path / "oracle_abort",
                src_files={"src/lib.rs": abort_rs.encode("utf-8")},
                inputs=[0],
                env=env,
                timeout=60,
                sysroot=sysroot,
            )
            self.assertEqual(
                (st_ab, fc_ab),
                ("spec_violation_confirmed", "spec_violation:panic_or_abort"),
            )

    def test_live_r4_closure_env_and_deadlock_hardening(self):
        """Live S3/S4 closure parity, Miri deadlock, & option_env!() hardening."""
        tools = self._discover_or_skip()
        lean_bin = tools["lean"]
        sysroot = tools["sysroot"]
        miri_sysroot = harness._discover_miri_sysroot()
        self.assertIsNotNone(miri_sysroot)
        env = harness._build_scrubbed_env(sysroot, miri_sysroot=miri_sysroot)
        hdr = "module\nprelude\npublic import Init\n"

        with tempfile.TemporaryDirectory(prefix="rt-live-r4-") as tmp:
            tmp_path = Path(tmp)

            # 1. Live S3: benign `Macro.trace[x] "hi"` + `def simproc` under
            # `Trusted.MirSemantics` passes verify+inspect & stays clean.
            s3_macro = tmp_path / "s3_macro"
            (s3_macro / "Spec").mkdir(parents=True)
            (s3_macro / "Spec/Spec.lean").write_text(
                "module\nprelude\npublic import Trusted.MirSemantics\n"
                "@[expose] public section\nnamespace Spec\n"
                "open Trusted.MirAst Trusted.MirSemantics\n"
                "namespace Macro\n"
                "def trace : List (String → Nat) := [fun _ => 0]\n"
                "end Macro\n"
                "def simproc : Nat := 0\n"
                "def benignCall (x : Nat) (_ : x < Macro.trace.length) : Nat :=\n"
                '  Macro.trace[x] "hi"\n'
                "def expectedReturn : TerminalOut :=\n"
                "  .returned ⟨.scalar ⟨.i64, false, BitVec.ofNat 128 1⟩, ⟨[]⟩⟩\n"
                "noncomputable def returnsZero (program : Program) : Prop :=\n"
                "  let entry := entryProgForBody program 0\n"
                "  let call : Query := { args := [] }\n"
                "  SatisfiesPost entry call (fun outcome => outcome = expectedReturn) ∧\n"
                "    (¬ Diverges entry call) ∧ Behavior entry call expectedReturn\n"
                "noncomputable def specs : Specs := ⟨fun _ _ => True, returnsZero⟩\n"
                "end Spec\nend\n",
                encoding="utf-8",
            )
            r_macro = harness.evaluate_submission(
                scenario_id="s3_spec_preflight_hack",
                submission_dir=s3_macro,
                anneal_root=_ANNEAL_ROOT,
                timeout_sec=180,
            )
            self.assertEqual(r_macro["verdict"], harness.VERDICT_DEFENDER_HELD, r_macro)
            self.assertTrue(r_macro["anneal_verify_ok"], r_macro)
            self.assertTrue(r_macro["anneal_inspect_ok"], r_macro)

            # 2. Theory mode uses foundationModules: `open BitVec` / `Array`
            # and `offset ("+00:00")` stay clean without false tags.
            pe_th: list[str] = []
            tags_th = harness._detect_disallowed_lean_constructs_with_tools(
                {
                    "theory/Anneal/BenignOpen.lean": (
                        "module\nprelude\n"
                        "public import Init.Data.BitVec.BasicAux\n"
                        "public import Init.Data.Array.Basic\n"
                        "open BitVec\nopen Classical\nopen Array\n"
                        "def offset (_ : String) : Nat := 0\n"
                        'def y : Nat := offset ("+00:00")\n'
                    )
                },
                allow_theory_import_all=True,
                allow_spec_options=False,
                lean_bin=lean_bin,
                env=env,
                allow_fallback=False,
                parse_errors_out=pe_th,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual((tags_th, pe_th), ([], []))

            # 3. `def simproc : Nat := 0` before `axiom evil` never blinds AST.
            for is_spec in (True, False):
                pe_sim: list[str] = []
                rel = "Spec/Spec.lean" if is_spec else "theory/Anneal/SimprocEvil.lean"
                hits = harness._detect_disallowed_lean_constructs_with_tools(
                    {
                        rel: (
                            "module\nprelude\npublic import Init.Data.Nat.Basic\n"
                            "def simproc : Nat := 0\naxiom evil : False\n"
                        )
                    },
                    allow_theory_import_all=not is_spec,
                    allow_spec_options=is_spec,
                    lean_bin=lean_bin,
                    env=env,
                    allow_fallback=False,
                    parse_errors_out=pe_sim,
                    anneal_root=_ANNEAL_ROOT,
                )
                self.assertIn("axiom", hits)
                self.assertEqual(pe_sim, [])

            # Keep explicit `open Init`-dependent case clean too.
            pe_init: list[str] = []
            self.assertEqual(
                harness._detect_disallowed_lean_constructs_with_tools(
                    {
                        "Spec/Spec.lean": hdr
                        + "open List\ndef perm12 : Prop := [1, 2] ~ [2, 1]\n"
                    },
                    allow_theory_import_all=False,
                    allow_spec_options=True,
                    lean_bin=lean_bin,
                    env=env,
                    allow_fallback=False,
                    parse_errors_out=pe_init,
                    anneal_root=_ANNEAL_ROOT,
                ),
                [],
            )
            self.assertEqual(pe_init, [])

            # 4. Live Miri Mutex self-deadlock stays `oracle_inconclusive`.
            deadlock_rs = (
                "pub fn target(_x: u32) -> u32 {\n"
                "    let m = std::sync::Mutex::new(0u32);\n"
                "    let _g1 = m.lock().unwrap();\n"
                "    let _g2 = m.lock().unwrap();\n"
                "    0\n"
                "}\n"
            )
            st_dl, fc_dl, _ = harness._run_s2_code_oracle(
                tmp_root=tmp_path / "oracle_deadlock",
                src_files={"src/lib.rs": deadlock_rs.encode("utf-8")},
                inputs=[0],
                env=env,
                timeout=30,
                sysroot=sysroot,
                rustc_runner=lambda *a, **k: subprocess.CompletedProcess([], 0, "", ""),
            )
            self.assertEqual((st_dl, fc_dl), ("oracle_inconclusive", None))

            # 5. Live `option_env!("MIRI_SYSROOT")` blocked by `exp_alt` probe.
            opt_env_rs = (
                "pub fn target(x: u32) -> u32 {\n"
                '    if option_env!("MIRI_SYSROOT").is_some() {\n'
                "        x.wrapping_add(1)\n"
                "    } else {\n"
                "        x\n"
                "    }\n"
                "}\n"
            )
            with self.assertRaises(harness.InvalidSubmissionError):
                harness._run_s2_code_oracle(
                    tmp_root=tmp_path / "oracle_opt_env",
                    src_files={"src/lib.rs": opt_env_rs.encode("utf-8")},
                    inputs=[0],
                    env=env,
                    timeout=60,
                    sysroot=sysroot,
                )

            # 6. Multi-group Spec AST closures isolate envs & catch leaks.
            pe_mg_ok: list[str] = []
            tags_mg_ok = harness._detect_disallowed_lean_constructs_with_tools(
                {
                    "Spec/Spec.lean": (
                        "module\nprelude\npublic import Trusted.MirSemantics\n"
                        "public import Spec.Helper\ndef s : Nat := 0\n"
                    ),
                    "Spec/Spec/Helper.lean": (
                        "module\nprelude\npublic import Init.Data.Nat.Basic\n"
                        "def h : Nat := 1\n"
                    ),
                },
                allow_theory_import_all=False,
                allow_spec_options=True,
                lean_bin=lean_bin,
                env=env,
                allow_fallback=False,
                parse_errors_out=pe_mg_ok,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertEqual((tags_mg_ok, pe_mg_ok), ([], []))

            # 5 distinct closures trigger `InspectAstLib.olean` + isolated runs.
            pe_mg_evil: list[str] = []
            multi_evil = {
                "Spec/Spec.lean": "module\nprelude\npublic import Init.Prelude\ndef a : Nat := 0\n",
                "Spec/H0.lean": "module\nprelude\npublic import Std.Data.ExtHashMap\ndef h0 : Nat := 0\n",
                "Spec/H1.lean": "module\nprelude\npublic import Std.Do\ndef h1 : Nat := 0\n",
                "Spec/H2.lean": "module\nprelude\npublic import Std.Sat.AIG.Cached\ndef h2 : Nat := 0\n",
                "Spec/Z.lean": "module\nprelude\npublic import Std.Http\naxiom evil : False\n",
            }
            tags_mg_evil = harness._detect_disallowed_lean_constructs_with_tools(
                multi_evil,
                allow_theory_import_all=False,
                allow_spec_options=True,
                lean_bin=lean_bin,
                env=env,
                allow_fallback=False,
                parse_errors_out=pe_mg_evil,
                anneal_root=_ANNEAL_ROOT,
            )
            self.assertIn("axiom", tags_mg_evil)
            self.assertEqual(pe_mg_evil, [])

    def test_live_s2_cargo_env_splits_rejected(self):
        tools = self._discover_or_skip()
        if shutil.which("bwrap") is None:
            if os.environ.get("ANNEAL_REDTEAM_REQUIRE_LIVE") == "1":
                self.fail("missing bwrap for live S2 Cargo env-split test")
            self.skipTest("bwrap not present")
        sysroot = tools["sysroot"]
        env = harness._build_scrubbed_env(
            sysroot, miri_sysroot=harness._discover_miri_sysroot()
        )
        with tempfile.TemporaryDirectory(prefix="rt-live-envsplit-") as tmp:
            tmp_path = Path(tmp)
            for idx, snippet in enumerate(
                (
                    'const SPLIT: bool = option_env!("CARGO_PKG_VERSION_MAJOR").is_some();\n'
                    "pub fn target(x: u32) -> u32 { if SPLIT { x.wrapping_add(1) } else { x } }\n",
                    'const SPLIT: bool = matches!(option_env!("MIRI_SYSROOT"), Some("/miri_sysroot"));\n'
                    "pub fn target(x: u32) -> u32 { if SPLIT { x.wrapping_add(1) } else { x } }\n",
                    'const SPLIT: bool = option_env!("HOME").is_some();\n'
                    "pub fn target(x: u32) -> u32 { if SPLIT { x.wrapping_add(1) } else { x } }\n",
                    'const SPLIT: bool = option_env!("LD_LIBRARY_PATH").is_some();\n'
                    "pub fn target(x: u32) -> u32 { if SPLIT { x.wrapping_add(1) } else { x } }\n",
                    'const SPLIT: bool = option_env!("MIRI_BE_RUSTC").is_some();\n'
                    "pub fn target(x: u32) -> u32 { if SPLIT { x.wrapping_add(1) } else { x } }\n",
                    'const SPLIT: bool = option_env!("MIRI_LOCAL_CRATES").is_some();\n'
                    "pub fn target(x: u32) -> u32 { if SPLIT { x.wrapping_add(1) } else { x } }\n",
                    'const SPLIT: bool = option_env!("MIRI_HOST_SYSROOT").is_some();\n'
                    "pub fn target(x: u32) -> u32 { if SPLIT { x.wrapping_add(1) } else { x } }\n",
                    'const SPLIT: bool = option_env!("RUSTC_STAGE").is_some();\n'
                    "pub fn target(x: u32) -> u32 { if SPLIT { x.wrapping_add(1) } else { x } }\n",
                )
            ):
                with self.assertRaises(harness.InvalidSubmissionError):
                    harness._run_s2_code_oracle(
                        tmp_root=tmp_path / f"split_{idx}",
                        src_files={"src/lib.rs": snippet.encode("utf-8")},
                        inputs=[0],
                        env=env,
                        timeout=60,
                        sysroot=sysroot,
                    )

            clean_st, clean_fc, _ = harness._run_s2_code_oracle(
                tmp_root=tmp_path / "clean",
                src_files={"src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"},
                inputs=[0, 1],
                env=env,
                timeout=60,
                sysroot=sysroot,
            )
            self.assertEqual((clean_st, clean_fc), ("clean", None))

    def test_live_r7_theory_mode_closure_isolation(self):
        """Live S4 AST inspection isolates per-file foundation closures."""
        tools = self._discover_or_skip()
        lean_bin = tools["lean"]
        sysroot = tools["sysroot"]
        env = harness._build_scrubbed_env(
            sysroot, miri_sysroot=harness._discover_miri_sysroot()
        )

        # 1. File B without `Init.Data.List.Notation` cannot rely on File A's
        #    list literal syntax (`[1, 2]`), yielding `parse_error` instead
        #    of silent pass under unrequested foundation modules.
        pe_leak: list[str] = []
        tags_leak = harness._detect_disallowed_lean_constructs_with_tools(
            {
                "theory/Anneal/GroupA.lean": (
                    "module\nprelude\npublic import Init.Data.List.Notation\n"
                    "def a : List Nat := [1, 2]\n"
                ),
                "theory/Anneal/GroupB.lean": (
                    "module\nprelude\npublic import Init.Prelude\n"
                    "def b := [1, 2]\n"
                ),
            },
            allow_theory_import_all=True,
            allow_spec_options=False,
            lean_bin=lean_bin,
            env=env,
            allow_fallback=False,
            parse_errors_out=pe_leak,
            anneal_root=_ANNEAL_ROOT,
        )
        self.assertEqual(tags_leak, [])
        self.assertEqual(pe_leak, ["parse_error"])

        # 2. Five distinct permitted foundation closures precompile cleanly
        #    and isolate each group without cross-contamination.
        pe_mg: list[str] = []
        tags_mg = harness._detect_disallowed_lean_constructs_with_tools(
            {
                "theory/Anneal/T0.lean": (
                    "module\nprelude\npublic import Init.Prelude\n"
                    "def t0 : Nat := 0\n"
                ),
                "theory/Anneal/T1.lean": (
                    "module\nprelude\npublic import Init.Data.Nat.Basic\n"
                    "def t1 : Nat := 1 + 2\n"
                ),
                "theory/Anneal/T2.lean": (
                    "module\nprelude\npublic import Init.Data.BitVec.BasicAux\n"
                    "def t2 : BitVec 4 := BitVec.ofNat 4 1\n"
                ),
                "theory/Anneal/T3.lean": (
                    "module\nprelude\npublic import Init.Data.Int.Basic\n"
                    "def t3 : Int := Int.ofNat 1\n"
                ),
                "theory/Anneal/T4.lean": (
                    "module\nprelude\npublic import Init.Data.List.Notation\n"
                    "def t4 : List Nat := [1, 2]\n"
                ),
            },
            allow_theory_import_all=True,
            allow_spec_options=False,
            lean_bin=lean_bin,
            env=env,
            allow_fallback=False,
            parse_errors_out=pe_mg,
            anneal_root=_ANNEAL_ROOT,
        )
        self.assertEqual((tags_mg, pe_mg), ([], []))

        # 3. Axiom in a distinct closure + forbidden `Std.Http` import are
        #    both flagged without importing unallowed sysroot `.olean`s.
        pe_evil: list[str] = []
        tags_evil = harness._detect_disallowed_lean_constructs_with_tools(
            {
                "theory/Anneal/Ok.lean": (
                    "module\nprelude\npublic import Init.Data.List.Notation\n"
                    "def ok : List Nat := [1, 2]\n"
                ),
                "theory/Anneal/Evil.lean": (
                    "module\nprelude\npublic import Init.Core\n"
                    "axiom evil : False\n"
                ),
                "theory/Anneal/Disallowed.lean": (
                    "module\nprelude\npublic import Std.Http\n"
                    "def d : Nat := 0\n"
                ),
            },
            allow_theory_import_all=True,
            allow_spec_options=False,
            lean_bin=lean_bin,
            env=env,
            allow_fallback=False,
            parse_errors_out=pe_evil,
            anneal_root=_ANNEAL_ROOT,
        )
        self.assertIn("axiom", tags_evil)
        self.assertIn("disallowed_import:Std.Http", tags_evil)

    def test_live_r9_s2_external_supervisor_seccomp_and_ctor_guard(self):
        """Live S2 R9: binary nonce isolation, seccomp stat/exit trap, & ctor guard."""
        tools = self._discover_or_skip()
        sysroot = tools["sysroot"]
        env = harness._build_scrubbed_env(
            sysroot, miri_sysroot=harness._discover_miri_sysroot()
        )
        with tempfile.TemporaryDirectory(prefix="rt-live-r9-") as tmp:
            tmp_path = Path(tmp)

            # 1. Clean native oracle binary contains zero ANNEAL_ORACLE_* bytes
            #    and authenticates cleanly via external supervisor.
            clean_root = tmp_path / "clean_native"
            clean_root.mkdir()
            st_c, fc_c, _ = harness._run_s2_code_oracle(
                tmp_root=clean_root,
                src_files={"src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"},
                inputs=[0, 1, 77],
                env=env,
                timeout=60,
                sysroot=sysroot,
            )
            self.assertEqual((st_c, fc_c), ("clean", None))
            oracle_bin = (
                clean_root
                / "oracle_harness/target"
                / harness.VERIFIED_RUST_TARGET
                / "debug/redteam_s2_oracle"
            )
            oracle_bytes = oracle_bin.read_bytes()
            self.assertNotIn(b"ANNEAL_ORACLE_", oracle_bytes)
            main_rs = (clean_root / "oracle_harness/src/main.rs").read_text()
            m_nonce = re.search(r"ANNEAL_ORACLE_START_([0-9a-f]+)", main_rs)
            self.assertIsNotNone(m_nonce)
            self.assertNotIn(m_nonce.group(1).encode("ascii"), oracle_bytes)

            # 2. Reading/stating `/work/oracle_bin` + exit(0) triggers seccomp
            #    kill -> `spec_violation_confirmed`.
            probe_rs = (
                "pub fn target(x: u32) -> u32 {\n"
                '    if std::path::Path::new("/work/oracle_bin").exists() {\n'
                "        std::process::exit(0);\n"
                "    }\n"
                "    x\n"
                "}\n"
            )
            st_p, fc_p, _ = harness._run_s2_code_oracle(
                tmp_root=tmp_path / "oracle_stat_exit",
                src_files={"src/lib.rs": probe_rs.encode("utf-8")},
                inputs=[0],
                env=env,
                timeout=60,
                sysroot=sysroot,
            )
            self.assertEqual(
                (st_p, fc_p),
                ("spec_violation_confirmed", "spec_violation:panic_or_abort"),
            )

            # 3. Attempting to interpose `prctl` symbol cannot disable
            #    raw-syscall seccomp filtering against `std::process::exit(0)`.
            hijack_rs = (
                "#[unsafe(no_mangle)] pub extern \"C\" fn prctl(_op: i32) -> i32 { 0 }\n"
                "pub fn target(_x: u32) -> u32 { std::process::exit(0); }\n"
            )
            st_h, fc_h, _ = harness._run_s2_code_oracle(
                tmp_root=tmp_path / "oracle_prctl_hijack",
                src_files={"src/lib.rs": hijack_rs.encode("utf-8")},
                inputs=[0],
                env=env,
                timeout=60,
                sysroot=sysroot,
            )
            self.assertEqual(
                (st_h, fc_h),
                ("spec_violation_confirmed", "spec_violation:panic_or_abort"),
            )

            # 4. Pre-main `.init_array` constructor is rejected fail-closed.
            ctor_rs = (
                "#[unsafe(link_section = \".init_array\")]\n"
                "#[used]\n"
                "static CTOR: extern \"C\" fn() = hijack;\n"
                "extern \"C\" fn hijack() { std::process::exit(0); }\n"
                "pub fn target(x: u32) -> u32 { x }\n"
            )
            with self.assertRaises(harness.InvalidSubmissionError):
                harness._run_s2_code_oracle(
                    tmp_root=tmp_path / "oracle_init_array",
                    src_files={"src/lib.rs": ctor_rs.encode("utf-8")},
                    inputs=[0],
                    env=env,
                    timeout=60,
                    sysroot=sysroot,
                )

            # 5. Raw-syscall or libc pipe write forgery in target code triggers
            #    seccomp kill (`spec_violation_confirmed`) despite bad return.
            forge_pipe_rs = (
                "pub fn target(x: u32) -> u32 {\n"
                "    let mut buf = [1u8, 0, 0, 0, 0];\n"
                "    buf[1..5].copy_from_slice(&x.to_le_bytes());\n"
                "    for fd in 3usize..=1024usize {\n"
                "        unsafe {\n"
                "            let mut _ret: isize;\n"
                "            core::arch::asm!(\n"
                '                "syscall",\n'
                '                inlateout("rax") 1usize => _ret,\n'
                '                in("rdi") fd,\n'
                '                in("rsi") buf.as_ptr(),\n'
                '                in("rdx") 5usize,\n'
                '                lateout("rcx") _,\n'
                '                lateout("r11") _,\n'
                "            );\n"
                "        }\n"
                "    }\n"
                "    x.wrapping_add(1)\n"
                "}\n"
            )
            st_f, fc_f, _ = harness._run_s2_code_oracle(
                tmp_root=tmp_path / "oracle_pipe_forge",
                src_files={"src/lib.rs": forge_pipe_rs.encode("utf-8")},
                inputs=[0],
                env=env,
                timeout=60,
                sysroot=sysroot,
            )
            self.assertEqual(
                (st_f, fc_f),
                ("spec_violation_confirmed", "spec_violation:panic_or_abort"),
            )
