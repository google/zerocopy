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
from pathlib import Path
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
            len(check_guard_mutation.MIR_SEMANTICS_GUARDS), 40
        )
        self.assertGreaterEqual(
            len(check_guard_mutation.AUDIT_HEADER_GUARDS), 2
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


if __name__ == "__main__":
    unittest.main()
