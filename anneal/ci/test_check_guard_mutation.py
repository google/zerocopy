# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the TCB guard-mutation CI check (`check_guard_mutation.py`).

These tests run in `static-checks` without requiring a Lean toolchain: they
validate static catalog invariants against the live repository sources, test
mutation/classification edge cases (including anti-crash-masquerading guards),
exercise the full runner loop against a deterministic fake `lean` binary, and
verify the GitHub Actions workflow wiring in `anneal-current.yml`.
"""

import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import textwrap
import unittest

import check_guard_mutation
from workflow_yaml import load_workflow_yaml


CI_DIR = Path(__file__).resolve().parent
ANNEAL_ROOT = CI_DIR.parent
SCRIPT = CI_DIR / "check_guard_mutation.py"


def _write_fake_lean(bin_path: Path, behavior_code: str) -> None:
    """Create an executable Python script masquerading as `lean`."""
    bin_path.write_text(
        f"#!{sys.executable}\n"
        "import json, os, sys\n"
        "from pathlib import Path\n"
        f"{behavior_code}\n",
        encoding="utf-8",
    )
    bin_path.chmod(bin_path.stat().st_mode | stat.S_IXUSR)


class GuardMutationUnitTests(unittest.TestCase):
    def test_live_catalog_static_invariants_and_cli_list(self):
        errors = check_guard_mutation.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertEqual(errors, [], f"catalog invariant errors: {errors}")
        self.assertGreaterEqual(
            len(check_guard_mutation.MIR_SEMANTICS_GUARDS), 65
        )
        self.assertGreaterEqual(
            len(check_guard_mutation.AUDIT_HEADER_GUARDS), 17
        )
        self.assertIn(
            "Trusted/MirSemantics/Layout",
            check_guard_mutation.SEMANTICS_DOWNSTREAM,
        )
        self.assertEqual(
            check_guard_mutation.SEMANTICS_DOWNSTREAM[
                "Trusted/MirSemantics/Layout"
            ][-1],
            "Trusted/MirSemantics/Boundary",
        )

        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--list"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res.returncode, 0, res.stderr)
        expected_total = len(check_guard_mutation.MIR_SEMANTICS_GUARDS) + len(
            check_guard_mutation.AUDIT_HEADER_GUARDS
        )
        self.assertIn(f"Total cataloged guards: {expected_total}", res.stdout)

    def test_apply_single_guard_mutation_requires_exact_unique_match(self):
        src = "alpha\nbeta\ngamma\n"
        mutated = check_guard_mutation.apply_single_guard_mutation(
            src, "beta", "BETA", guard_id="g1"
        )
        self.assertEqual(mutated, "alpha\nBETA\ngamma\n")

        with self.assertRaisesRegex(ValueError, "found 0 occurrences"):
            check_guard_mutation.apply_single_guard_mutation(
                src, "missing", "x", guard_id="g0"
            )
        with self.assertRaisesRegex(ValueError, "found 2 occurrences"):
            check_guard_mutation.apply_single_guard_mutation(
                "dup\ndup\n", "dup", "x", guard_id="g2"
            )
        with self.assertRaisesRegex(ValueError, "must differ"):
            check_guard_mutation.apply_single_guard_mutation(
                src, "beta", "beta", guard_id="g_same"
            )

    def test_find_theorem_line_span(self):
        fixture = textwrap.dedent(
            """\
            namespace Test

            theorem first_thm : True :=
              trivial

            theorem second_thm :
                True := by
              trivial

            end Test
            """
        )
        self.assertEqual(
            check_guard_mutation.find_theorem_line_span(fixture, "first_thm"),
            (3, 5),
        )
        self.assertEqual(
            check_guard_mutation.find_theorem_line_span(fixture, "second_thm"),
            (6, 9),
        )
        with self.assertRaisesRegex(ValueError, "not found"):
            check_guard_mutation.find_theorem_line_span(fixture, "missing_thm")

    def test_classify_refutation_failure_blocks_crash_masquerading(self):
        # Surviving mutant (rc=0) must be reported as SURVIVED.
        status, _ = check_guard_mutation.classify_refutation_failure(
            0, "", "OpsRefutations.lean", (20, 30)
        )
        self.assertEqual(status, "SURVIVED")

        # Genuine proof failure inside target theorem span is KILLED.
        good_err = (
            "/tmp/OpsRefutations.lean:25:4: error: Type mismatch\n"
            "  rfl\nhas type\n  False\n"
        )
        status, _ = check_guard_mutation.classify_refutation_failure(
            1, good_err, "OpsRefutations.lean", (20, 30)
        )
        self.assertEqual(status, "KILLED")

        # Proof failure outside target theorem span must NOT count as a kill.
        wrong_line_err = (
            "/tmp/OpsRefutations.lean:55:4: error: Type mismatch\n"
            "  rfl\nhas type\n  False\n"
        )
        status, _ = check_guard_mutation.classify_refutation_failure(
            1, wrong_line_err, "OpsRefutations.lean", (20, 30)
        )
        self.assertEqual(status, "ERROR")

        # Parse errors, missing identifiers, and timeouts never count as kills.
        for bad_marker in (
            "unknown identifier 'foo'",
            "expected token",
            "maximum recursion depth has been reached",
            "deterministic timeout",
            "PANIC at Lean.Kernel",
        ):
            bad_out = (
                f"/tmp/OpsRefutations.lean:25:4: error: Type mismatch\n"
                f"{bad_marker}\n"
            )
            status, _ = check_guard_mutation.classify_refutation_failure(
                1, bad_out, "OpsRefutations.lean", (20, 30)
            )
            self.assertEqual(status, "ERROR", bad_marker)

        # Signal or non-1 exit code is an operational ERROR, never a kill.
        status, _ = check_guard_mutation.classify_refutation_failure(
            -9, good_err, "OpsRefutations.lean", (20, 30)
        )
        self.assertEqual(status, "ERROR")

    def _run_synthetic_suite(
        self, fake_lean_body: str, *, suite: str = "all"
    ) -> tuple[int, str, str, dict[str, object] | None, dict[str, str], dict[str, str]]:
        """Run `check_guard_mutation.py` with a fake `lean` binary."""
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-unit-") as tmp:
            tmp_path = Path(tmp)
            fake_lean = tmp_path / "fake_lean"
            _write_fake_lean(fake_lean, fake_lean_body)
            json_out = tmp_path / "report.json"

            tracked_files = [
                ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Ops.lean",
                ANNEAL_ROOT / "trusted/audit/TrustedBoundary.lean",
            ]
            before_hashes = {
                str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in tracked_files
            }

            res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(ANNEAL_ROOT),
                    "--lean",
                    str(fake_lean),
                    "--suite",
                    suite,
                    "--filter",
                    "ops_div_rem_by_zero"
                    if suite == "mir_semantics"
                    else "audit_header_reject_lean_import",
                    "--jobs",
                    "1",
                    "--json-out",
                    str(json_out),
                ],
                capture_output=True,
                text=True,
            )
            after_hashes = {
                str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in tracked_files
            }
            parsed = (
                json.loads(json_out.read_text(encoding="utf-8"))
                if json_out.is_file()
                else None
            )
            return (
                res.returncode,
                res.stdout,
                res.stderr,
                parsed,
                before_hashes,
                after_hashes,
            )

    def test_runner_passes_on_clean_kill_and_leaves_tree_untouched(self):
        # Fake `lean` succeeds on baseline and mutated semantics/sanity, and
        # fails with a localized Type mismatch on `OpsRefutations.lean` when
        # `LEAN_PATH` has two entries (mutant overlay + base).
        ops_span = check_guard_mutation.find_theorem_line_span(
            (
                ANNEAL_ROOT
                / "ci/fixtures/guard_mutation/OpsRefutations.lean"
            ).read_text(encoding="utf-8"),
            "refute_ops_div_rem_by_zero",
        )
        fake_lean_body = textwrap.dedent(
            f"""\
            args = sys.argv[1:]
            lean_path = os.environ.get("LEAN_PATH", "")
            is_mutant = "anneal-gmut-" in lean_path and "anneal-gmut-base-" not in lean_path
            if "-o" in args:
                out_idx = args.index("-o") + 1
                Path(args[out_idx]).write_bytes(b"fake-olean")
                src = args[-1]
                if is_mutant and src.endswith("OpsRefutations.lean"):
                    print(f"{{src}}:{ops_span[0]}:2: error: Type mismatch (rfl)")
                    sys.exit(1)
                sys.exit(0)
            sys.exit(0)
            """
        )
        rc, out, err, report, before, after = self._run_synthetic_suite(
            fake_lean_body, suite="mir_semantics"
        )
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(before, after)
        assert report is not None
        self.assertEqual(report["killed"], 1)
        self.assertEqual(report["survived"], 0)
        self.assertEqual(report["errors"], 0)

    def test_runner_fails_closed_on_surviving_mutant_and_build_error(self):
        # Case 1: Mutant survives (refutation still exits 0).
        survive_body = textwrap.dedent(
            """\
            args = sys.argv[1:]
            if "-o" in args:
                Path(args[args.index("-o") + 1]).write_bytes(b"fake-olean")
            sys.exit(0)
            """
        )
        rc, out, err, report, _, _ = self._run_synthetic_suite(
            survive_body, suite="mir_semantics"
        )
        self.assertEqual(rc, 1, out + err)
        assert report is not None
        self.assertEqual(report["survived"], 1)
        self.assertEqual(report["killed"], 0)

        # Case 2: Mutated semantics module itself fails to compile -> ERROR,
        # never counted as a kill.
        broken_mutant_body = textwrap.dedent(
            """\
            args = sys.argv[1:]
            lean_path = os.environ.get("LEAN_PATH", "")
            is_mutant = "anneal-gmut-" in lean_path and "anneal-gmut-base-" not in lean_path
            if "-o" in args:
                src = args[-1]
                if is_mutant and src.endswith("Ops.lean"):
                    print("syntax error in mutated Ops.lean", file=sys.stderr)
                    sys.exit(1)
                Path(args[args.index("-o") + 1]).write_bytes(b"fake-olean")
            sys.exit(0)
            """
        )
        rc2, out2, err2, report2, _, _ = self._run_synthetic_suite(
            broken_mutant_body, suite="mir_semantics"
        )
        self.assertEqual(rc2, 1, out2 + err2)
        assert report2 is not None
        self.assertEqual(report2["errors"], 1)
        self.assertEqual(report2["killed"], 0)

    def test_runner_audit_headers_suite_detects_policy_flip(self):
        # Fake `lean` compiles TrustedBoundary, policy-rejects on baseline
        # (`tb_olean` in LEAN_PATH), and accepts on mutant (`anneal-gmut-` in
        # LEAN_PATH).
        fake_audit_body = textwrap.dedent(
            """\
            args = sys.argv[1:]
            if args == ["--print-prefix"]:
                print("/fake/sysroot")
                sys.exit(0)
            if "-o" in args:
                Path(args[args.index("-o") + 1]).write_bytes(b"fake-olean")
                sys.exit(0)
            if args[0] == "--run":
                res_path = Path(args[3])
                lean_path = os.environ.get("LEAN_PATH", "")
                if "tb_olean" in lean_path:
                    res_path.write_text(json.dumps({
                        "ok": False,
                        "category": "policy",
                        "message": "policy: disallowed sysroot import Lean",
                    }))
                    sys.exit(1)
                res_path.write_text(json.dumps({"ok": True, "result": {}}))
                sys.exit(0)
            sys.exit(2)
            """
        )
        rc, out, err, report, before, after = self._run_synthetic_suite(
            fake_audit_body, suite="audit_headers"
        )
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(before, after)
        assert report is not None
        self.assertEqual(report["killed"], 1)
        self.assertEqual(report["survived"], 0)
        self.assertEqual(report["errors"], 0)

    def test_runner_audit_blocks_broken_positive_sanity_anti_masquerading(self):
        # Fake `lean` policy-rejects negative fixture and accepts positive check
        # on baseline (`tb_olean` in LEAN_PATH), then breaks positive sanity on
        # the mutant: must classify as ERROR, never KILLED.
        broken_pos_body = textwrap.dedent(
            """\
            args = sys.argv[1:]
            if args == ["--print-prefix"]:
                print("/fake/sysroot")
                sys.exit(0)
            if "-o" in args:
                Path(args[args.index("-o") + 1]).write_bytes(b"fake-olean")
                sys.exit(0)
            if args[0] == "--run":
                req_path = Path(args[2])
                res_path = Path(args[3])
                lean_path = os.environ.get("LEAN_PATH", "")
                is_pos = req_path.name.startswith("pos_")
                if "tb_olean" in lean_path:
                    if is_pos:
                        res_path.write_text(json.dumps({"ok": True, "result": {}}))
                        sys.exit(0)
                    res_path.write_text(json.dumps({
                        "ok": False,
                        "category": "policy",
                        "message": "policy: trust tier rejected",
                    }))
                    sys.exit(1)
                if is_pos:
                    res_path.write_text(json.dumps({
                        "ok": False,
                        "category": "operational",
                        "message": "parser regression on mutant",
                    }))
                    sys.exit(2)
                res_path.write_text(json.dumps({"ok": True, "result": {}}))
                sys.exit(0)
            sys.exit(2)
            """
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-pos-") as tmp:
            tmp_path = Path(tmp)
            fake_lean = tmp_path / "fake_lean"
            _write_fake_lean(fake_lean, broken_pos_body)
            json_out = tmp_path / "report.json"
            res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(ANNEAL_ROOT),
                    "--lean",
                    str(fake_lean),
                    "--suite",
                    "audit_headers",
                    "--filter",
                    "audit_preflight_reject_theory_trust_tier",
                    "--jobs",
                    "1",
                    "--json-out",
                    str(json_out),
                ],
                capture_output=True,
                text=True,
            )
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            report = json.loads(json_out.read_text(encoding="utf-8"))
            self.assertEqual(report["errors"], 1)
            self.assertEqual(report["killed"], 0)

    def test_workflow_wires_guard_mutation_in_test_and_verify(self):
        workflow = load_workflow_yaml(
            (
                ANNEAL_ROOT.parent / ".github/workflows/anneal-current.yml"
            ).read_text(encoding="utf-8")
        )
        steps = workflow["jobs"]["test-and-verify"]["steps"]
        by_id = {s["id"]: (i, s) for i, s in enumerate(steps) if "id" in s}
        self.assertIn("guard_mutation", by_id)
        gm_idx, gm_step = by_id["guard_mutation"]
        self.assertGreater(gm_idx, by_id["save_miri_olean_cache"][0])
        self.assertLess(gm_idx, by_id["clean_tree"][0])
        for token in (
            "ACTIONS_CACHE_URL",
            "ACTIONS_RESULTS_URL",
            "ACTIONS_RUNTIME_TOKEN",
        ):
            self.assertEqual(gm_step.get("env", {}).get(token), "")
        run_src = gm_step["run"]
        self.assertIn("/usr/bin/python3 -I -B ci/check_guard_mutation.py", run_src)
        self.assertIn('--lean "$ANNEAL_TEST_INSTALL_ROOT/lean/bin/lean"', run_src)
        self.assertIn("guard-mutation.log", run_src)

    def test_runner_preserves_module_olean_companion_parts(self):
        # Fake `lean` emits `.olean`, `.olean.server`, and `.olean.private`
        # like Lean 4 `module` compilation and requires unmodified base
        # modules (`Trusted/MirAst.olean.{server,private}`) to be linked into
        # the mutant's `LEAN_PATH` directory while omitting rebuilt modules.
        ops_span = check_guard_mutation.find_theorem_line_span(
            (
                ANNEAL_ROOT
                / "ci/fixtures/guard_mutation/OpsRefutations.lean"
            ).read_text(encoding="utf-8"),
            "refute_ops_div_rem_by_zero",
        )
        fake_lean_body = textwrap.dedent(
            f"""\
            args = sys.argv[1:]
            lean_path = Path(os.environ.get("LEAN_PATH", "").split(os.pathsep)[0])
            is_mutant = "anneal-gmut-" in str(lean_path) and "anneal-gmut-base-" not in str(lean_path)
            if "-o" in args:
                out_path = Path(args[args.index("-o") + 1])
                src = args[-1]
                if is_mutant and src.endswith("Ops.lean"):
                    for suffix in (".olean", ".olean.server", ".olean.private"):
                        if not (lean_path / f"Trusted/MirAst{{suffix}}").is_file():
                            print(f"missing Trusted/MirAst{{suffix}}", file=sys.stderr)
                            sys.exit(1)
                    if (lean_path / "Trusted/MirSemantics/Ops.olean.server").exists():
                        print("stale Ops.olean.server copied", file=sys.stderr)
                        sys.exit(1)
                for suffix in ("", ".server", ".private"):
                    Path(f"{{out_path}}{{suffix}}").write_bytes(b"fake-olean")
                if is_mutant and src.endswith("OpsRefutations.lean"):
                    print(f"{{src}}:{ops_span[0]}:2: error: Type mismatch (rfl)")
                    sys.exit(1)
                sys.exit(0)
            sys.exit(0)
            """
        )
        rc, out, err, report, before, after = self._run_synthetic_suite(
            fake_lean_body, suite="mir_semantics"
        )
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(before, after)
        assert report is not None
        self.assertEqual(report["killed"], 1)
        self.assertEqual(report["survived"], 0)
        self.assertEqual(report["errors"], 0)

    def test_changed_file_zero_guard_skip_needs_no_lean_and_checks_anchors(self):
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-skip-") as tmp:
            json_out = Path(tmp) / "skip_report.json"
            clean_env = {k: v for k, v in os.environ.items() if k != "ANNEAL_LEAN"}
            clean_env["PATH"] = ""
            res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(ANNEAL_ROOT),
                    "--changed-file",
                    "anneal/theory/Anneal.lean",
                    "--changed-file",
                    "docs/trust-model.md",
                    "--json-out",
                    str(json_out),
                ],
                capture_output=True,
                text=True,
                env=clean_env,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertIn("0 guards selected (skipping Lean baseline)", res.stdout)
            report = json.loads(json_out.read_text(encoding="utf-8"))
            self.assertEqual(report["total"], 0)
            self.assertEqual(report["killed"], 0)
            self.assertEqual(report["survived"], 0)
            self.assertEqual(report["errors"], 0)

            # Even when `--changed-file` selects 0 live guards, static catalog
            # and anchor validation must still run and fail closed on drift.
            fake_root = Path(tmp) / "fake_anneal"
            for rel in (
                "trusted/lean/Trusted/MirSemantics",
                "ci/fixtures/guard_mutation",
            ):
                shutil.copytree(ANNEAL_ROOT / rel, fake_root / rel)
            tb_dst = fake_root / "trusted/audit/TrustedBoundary.lean"
            tb_dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ANNEAL_ROOT / "trusted/audit/TrustedBoundary.lean", tb_dst)

            ops_path = fake_root / "trusted/lean/Trusted/MirSemantics/Ops.lean"
            ops_path.write_text(
                ops_path.read_text(encoding="utf-8").replace(
                    check_guard_mutation.MIR_SEMANTICS_GUARDS[0].anchor,
                    "-- broken anchor",
                    1,
                ),
                encoding="utf-8",
            )
            drift_res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(fake_root),
                    "--changed-file",
                    "anneal/theory/Anneal.lean",
                ],
                capture_output=True,
                text=True,
                env=clean_env,
            )
            self.assertEqual(drift_res.returncode, 1)
            self.assertIn("guard catalog validation failed", drift_res.stderr)

    def test_changed_file_selection_closure_and_full_sweep_triggers(self):
        # TrustedBoundary.lean and foundation-lock.json select all 17
        # audit_headers guards and 0 MIR guards.
        for audit_trigger in (
            "anneal/trusted/audit/TrustedBoundary.lean",
            "trusted/lean/foundation-lock.json",
        ):
            mir_g, audit_g = check_guard_mutation.select_guards_for_changed_files(
                [audit_trigger]
            )
            self.assertEqual(len(mir_g), 0, msg=audit_trigger)
            self.assertEqual(
                len(audit_g),
                len(check_guard_mutation.AUDIT_HEADER_GUARDS),
                msg=audit_trigger,
            )
            self.assertEqual(len(audit_g), 17, msg=audit_trigger)

        # MirModel.lean, Step.lean, and other trusted/lean/** files (excluding
        # foundation-lock.json and MirSemantics/CanaryFixtures.lean) select all
        # 92 MIR guards and 0 audit guards.
        for mir_trigger in (
            "anneal/trusted/lean/Trusted/MirModel.lean",
            "trusted/lean/Trusted/MirSemantics/Step.lean",
            "anneal/trusted/lean/Trusted/MirSemantics.lean",
            "anneal/trusted/lean/Trusted.lean",
            "trusted/lean/Trusted/MirAst.lean",
        ):
            mir_sel, audit_sel = (
                check_guard_mutation.select_guards_for_changed_files(
                    [mir_trigger]
                )
            )
            self.assertEqual(
                len(mir_sel),
                len(check_guard_mutation.MIR_SEMANTICS_GUARDS),
                msg=mir_trigger,
            )
            self.assertEqual(len(mir_sel), 92, msg=mir_trigger)
            self.assertEqual(audit_sel, [], msg=mir_trigger)

        # CanaryFixtures.lean and theory/Anneal.lean select 0 guards.
        for zero_trigger in (
            "anneal/trusted/lean/Trusted/MirSemantics/CanaryFixtures.lean",
            "trusted/lean/Trusted/MirSemantics/CanaryFixtures.lean",
            "anneal/theory/Anneal.lean",
        ):
            mir_z, audit_z = check_guard_mutation.select_guards_for_changed_files(
                [zero_trigger]
            )
            self.assertEqual(mir_z, [], msg=zero_trigger)
            self.assertEqual(audit_z, [], msg=zero_trigger)

        # Union of audit + MIR triggers selects all 109 guards.
        mir_union, audit_union = (
            check_guard_mutation.select_guards_for_changed_files(
                [
                    "anneal/trusted/audit/TrustedBoundary.lean",
                    "anneal/trusted/lean/Trusted/MirModel.lean",
                ]
            )
        )
        self.assertEqual(len(mir_union) + len(audit_union), 109)

        # Full-sweep escalation triggers select all 109 guards.
        for trigger in (
            "ci/check_guard_mutation.py",
            "anneal/ci/fixtures/guard_mutation/OpsRefutations.lean",
            "trusted/lean/lean-toolchain",
        ):
            mir_full, audit_full = check_guard_mutation.select_guards_for_changed_files(
                [trigger]
            )
            self.assertEqual(
                len(mir_full),
                len(check_guard_mutation.MIR_SEMANTICS_GUARDS),
                f"expected full MIR sweep for {trigger}",
            )
            self.assertEqual(
                len(audit_full),
                len(check_guard_mutation.AUDIT_HEADER_GUARDS),
                f"expected full audit sweep for {trigger}",
            )

    def test_changed_file_trusted_boundary_skips_mir_baseline(self):
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-aud-") as tmp:
            tmp_path = Path(tmp)
            fake_lean = tmp_path / "fake_lean"
            log_file = tmp_path / "invocations.log"
            json_out = tmp_path / "report.json"
            fake_body = textwrap.dedent(
                f"""\
                args = sys.argv[1:]
                with open({str(log_file)!r}, "a", encoding="utf-8") as fh:
                    fh.write(" ".join(args) + "\\n")
                if args == ["--print-prefix"]:
                    print("/fake/sysroot")
                    sys.exit(0)
                if "-o" in args:
                    src = args[-1]
                    if "MirSemantics" in src or "MirAst" in src:
                        print(f"unexpected MIR baseline compile: {{src}}", file=sys.stderr)
                        sys.exit(9)
                    Path(args[args.index("-o") + 1]).write_bytes(b"fake-olean")
                    sys.exit(0)
                if args[0] == "--run":
                    req_path = Path(args[2])
                    res_path = Path(args[3])
                    lean_path = os.environ.get("LEAN_PATH", "")
                    is_pos = req_path.name.startswith("pos_")
                    if "tb_olean" in lean_path:
                        if is_pos:
                            res_path.write_text(json.dumps({{"ok": True, "result": {{}}}}))
                            sys.exit(0)
                        res_path.write_text(json.dumps({{
                            "ok": False,
                            "category": "policy",
                            "message": "policy: rejected",
                        }}))
                        sys.exit(1)
                    if is_pos:
                        res_path.write_text(json.dumps({{"ok": True, "result": {{}}}}))
                        sys.exit(0)
                    res_path.write_text(json.dumps({{"ok": True, "result": {{}}}}))
                    sys.exit(0)
                sys.exit(2)
                """
            )
            _write_fake_lean(fake_lean, fake_body)
            res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(ANNEAL_ROOT),
                    "--lean",
                    str(fake_lean),
                    "--changed-file",
                    "anneal/trusted/audit/TrustedBoundary.lean",
                    "--jobs",
                    "1",
                    "--json-out",
                    str(json_out),
                ],
                capture_output=True,
                text=True,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            report = json.loads(json_out.read_text(encoding="utf-8"))
            self.assertEqual(
                report["total"], len(check_guard_mutation.AUDIT_HEADER_GUARDS)
            )
            self.assertEqual(report["killed"], report["total"])
            self.assertEqual(report["errors"], 0)
            log_text = log_file.read_text(encoding="utf-8")
            self.assertNotIn("MirSemantics", log_text)
            self.assertNotIn("MirAst", log_text)

    def test_changed_file_rejects_invalid_and_traversal_paths(self):
        for bad_path in (
            "",
            "   ",
            "a\x00b",
            "trusted\\audit\\TrustedBoundary.lean",
            "/etc/passwd",
            "../secret.lean",
            "anneal/../trusted/audit/TrustedBoundary.lean",
            ".",
            "..",
            "./trusted/audit/TrustedBoundary.lean",
            "trusted//audit/TrustedBoundary.lean",
            "anneal",
            "anneal/",
        ):
            with self.assertRaises(ValueError, msg=f"expected reject for {bad_path!r}"):
                check_guard_mutation.select_guards_for_changed_files([bad_path])

        # Trailing invalid path must still fail closed even after a full-sweep
        # trigger appears earlier in `--changed-file`.
        with self.assertRaises(ValueError):
            check_guard_mutation.select_guards_for_changed_files(
                ["ci/check_guard_mutation.py", "../bad"]
            )

        cli_res = subprocess.run(
            [
                sys.executable,
                "-I",
                "-B",
                str(SCRIPT),
                "--anneal-root",
                str(ANNEAL_ROOT),
                "--changed-file",
                "../escape.lean",
            ],
            capture_output=True,
            text=True,
        )
        self.assertEqual(cli_res.returncode, 1)
        self.assertIn("..", cli_res.stderr)


if __name__ == "__main__":
    unittest.main()
