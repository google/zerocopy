# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the Rust TCB guard-mutation CI check.

These tests run cleanly in `unittest discover` without invoking `cargo` builds:
they validate static catalog invariants against the live `anneal/trusted/`
sources, verify strict anti-fake-kill classification rules (compile failures,
signals, wrong-test failures, and vacuous `0 tests` runs can never count as
baseline passes or mutant kills), and exercise the end-to-end runner against a
deterministic fake `cargo` binary.
"""

import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest import mock

import check_rust_guard_mutation


CI_DIR = Path(__file__).resolve().parent
ANNEAL_ROOT = CI_DIR.parent
SCRIPT = CI_DIR / "check_rust_guard_mutation.py"


def _write_fake_cargo(bin_path: Path, behavior_code: str) -> None:
    """Create an executable Python script masquerading as `cargo`."""
    bin_path.write_text(
        f"#!{sys.executable}\n"
        "import os, sys\n"
        "from pathlib import Path\n"
        f"{behavior_code}\n",
        encoding="utf-8",
    )
    bin_path.chmod(bin_path.stat().st_mode | stat.S_IXUSR)


class RustGuardMutationUnitTests(unittest.TestCase):
    def test_live_catalog_static_invariants_and_cli_list(self):
        errors = check_rust_guard_mutation.validate_catalog_invariants(
            ANNEAL_ROOT
        )
        self.assertEqual(errors, [], f"catalog invariant errors: {errors}")

        guards = check_rust_guard_mutation.RUST_GUARDS
        self.assertGreaterEqual(len(guards), 18)

        audit_guards = [g for g in guards if g.suite == "anneal_audit"]
        ca_guards = [g for g in guards if g.suite == "cargo_anneal"]
        self.assertGreaterEqual(len(audit_guards), 8)
        self.assertGreaterEqual(len(ca_guards), 8)

        # Verify distinct target files across both crates and zero overlap with
        # `stage.rs`, `olean_cache.rs`, or `rustc-capture/`.
        touched_files = {g.target_file for g in guards}
        for required_file in (
            "trusted/audit/src/cargo_boundary.rs",
            "trusted/audit/src/miri_pin.rs",
            "trusted/audit/src/repo_audit.rs",
            "trusted/cargo-anneal/src/core/elf.rs",
            "trusted/cargo-anneal/src/core/identifiers.rs",
            "trusted/cargo-anneal/src/sandbox.rs",
            "trusted/cargo-anneal/src/sys_util.rs",
            "trusted/cargo-anneal/src/toolchain.rs",
            "trusted/cargo-anneal/src/verify.rs",
            "trusted/cargo-anneal/src/bundle.rs",
        ):
            self.assertIn(required_file, touched_files)

        for g in guards:
            for forbidden in ("stage.rs", "olean_cache.rs", "rustc-capture"):
                self.assertNotIn(forbidden, g.target_file)

        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--list"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertIn(
            f"Total cataloged Rust guards: {len(guards)}", res.stdout
        )

    def test_apply_single_guard_mutation_requires_exact_unique_match(self):
        src = "alpha\nbeta\ngamma\n"
        mutated = check_rust_guard_mutation.apply_single_guard_mutation(
            src, "beta", "BETA", guard_id="g1"
        )
        self.assertEqual(mutated, "alpha\nBETA\ngamma\n")

        with self.assertRaisesRegex(ValueError, "found 0 occurrences"):
            check_rust_guard_mutation.apply_single_guard_mutation(
                src, "missing", "x", guard_id="g0"
            )
        with self.assertRaisesRegex(ValueError, "found 2 occurrences"):
            check_rust_guard_mutation.apply_single_guard_mutation(
                "dup\ndup\n", "dup", "x", guard_id="g2"
            )
        with self.assertRaisesRegex(ValueError, "must differ"):
            check_rust_guard_mutation.apply_single_guard_mutation(
                src, "beta", "beta", guard_id="g_same"
            )

    def test_validate_catalog_rejects_excluded_paths_and_duplicates(self):
        fake_guards = check_rust_guard_mutation.RUST_GUARDS + (
            check_rust_guard_mutation.RustGuard(
                guard_id=check_rust_guard_mutation.RUST_GUARDS[0].guard_id,
                suite="cargo_anneal",
                target_file="trusted/cargo-anneal/src/stage.rs",
                description="bad excluded path",
                anchor="a",
                replacement="b",
                package="cargo-anneal",
                test_args=("--lib",),
                test_name="nonexistent_unit_test",
            ),
        )
        with mock.patch.object(
            check_rust_guard_mutation, "RUST_GUARDS", fake_guards
        ):
            errors = check_rust_guard_mutation.validate_catalog_invariants(
                ANNEAL_ROOT
            )
        joined = "\n".join(errors)
        self.assertIn("duplicate guard_id", joined)
        self.assertIn("excluded path 'stage.rs'", joined)
        self.assertIn("not found", joined)

    def test_classify_rust_test_outcome_blocks_fake_kills(self):
        test_name = (
            "sandbox::tests::door1_inspector_result_handles_empty_valid_and_extra_files"
        )

        # Passing mutant reports SURVIVED.
        ok_out = (
            f"running 1 test\n"
            f"test {test_name} ... ok\n\n"
            f"test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured;\n"
        )
        status, _ = check_rust_guard_mutation.classify_rust_test_outcome(
            0, ok_out, test_name
        )
        self.assertEqual(status, "SURVIVED")

        # Vacuous `0 tests` filter match reports ERROR even when rc == 0.
        zero_out = (
            "running 0 tests\n\n"
            "test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured;\n"
        )
        status, detail = check_rust_guard_mutation.classify_rust_test_outcome(
            0, zero_out, test_name
        )
        self.assertEqual(status, "ERROR")
        self.assertIn("0 tests executed", detail)

        # Genuine targeted failure with exit code 101 reports KILLED.
        fail_out = (
            f"running 1 test\n"
            f"test {test_name} ... FAILED\n\n"
            f"test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured;\n"
        )
        status, _ = check_rust_guard_mutation.classify_rust_test_outcome(
            101, fail_out, test_name
        )
        self.assertEqual(status, "KILLED")

        # Failure on a different test name does not count as KILLED.
        wrong_fail_out = (
            "running 1 test\n"
            "test sandbox::tests::unrelated ... FAILED\n\n"
            "test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured;\n"
        )
        status, _ = check_rust_guard_mutation.classify_rust_test_outcome(
            101, wrong_fail_out, test_name
        )
        self.assertEqual(status, "ERROR")

        # Compile error without test summary reports ERROR.
        status, _ = check_rust_guard_mutation.classify_rust_test_outcome(
            101, "error[E0308]: mismatched types", test_name
        )
        self.assertEqual(status, "ERROR")

        # Signal termination reports ERROR even if output looks like failure.
        status, _ = check_rust_guard_mutation.classify_rust_test_outcome(
            -9, fail_out, test_name
        )
        self.assertEqual(status, "ERROR")

    @classmethod
    def setUpClass(cls) -> None:
        cls._mini_tmp = tempfile.TemporaryDirectory(prefix="anneal-rgmut-mini-")
        cls.mini_anneal = Path(cls._mini_tmp.name) / "anneal"
        for rel in (
            "trusted/audit/src/cargo_boundary.rs",
            "trusted/audit/src/miri_pin.rs",
            "trusted/audit/src/repo_audit.rs",
            "tests/audit/tests/boundary_audit.rs",
            "trusted/cargo-anneal/src/core/elf.rs",
            "trusted/cargo-anneal/src/core/identifiers.rs",
            "trusted/cargo-anneal/src/sandbox.rs",
            "trusted/cargo-anneal/src/sys_util.rs",
            "trusted/cargo-anneal/src/toolchain.rs",
            "trusted/cargo-anneal/src/verify.rs",
            "trusted/cargo-anneal/src/bundle.rs",
            "tests/cargo-anneal/tests/sandbox_escape.rs",
        ):
            dst = cls.mini_anneal / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ANNEAL_ROOT / rel, dst)

    @classmethod
    def tearDownClass(cls) -> None:
        cls._mini_tmp.cleanup()

    def _run_synthetic_suite(
        self,
        fake_cargo_body: str,
        *,
        suite: str = "all",
        name_filter: str = "cargo_boundary_member_outside_trusted",
        jobs: int = 1,
    ) -> tuple[
        int,
        str,
        str,
        dict[str, object] | None,
        dict[str, str],
        dict[str, str],
    ]:
        """Run `check_rust_guard_mutation.main()` with a fake `cargo` binary."""
        import contextlib
        import io

        with tempfile.TemporaryDirectory(prefix="anneal-rgmut-unit-") as tmp:
            tmp_path = Path(tmp)
            fake_cargo = tmp_path / "fake_cargo"
            _write_fake_cargo(fake_cargo, fake_cargo_body)
            json_out = tmp_path / "report.json"

            tracked_files = sorted(
                {ANNEAL_ROOT / g.target_file for g in check_rust_guard_mutation.RUST_GUARDS}
            )
            before_hashes = {
                str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in tracked_files
            }

            stdout_buf = io.StringIO()
            stderr_buf = io.StringIO()
            with (
                contextlib.redirect_stdout(stdout_buf),
                contextlib.redirect_stderr(stderr_buf),
            ):
                rc = check_rust_guard_mutation.main(
                    [
                        "--anneal-root",
                        str(self.mini_anneal),
                        "--cargo",
                        str(fake_cargo),
                        "--suite",
                        suite,
                        "--filter",
                        name_filter,
                        "--jobs",
                        str(jobs),
                        "--json-out",
                        str(json_out),
                    ]
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
                rc,
                stdout_buf.getvalue(),
                stderr_buf.getvalue(),
                parsed,
                before_hashes,
                after_hashes,
            )

    def test_runner_passes_on_clean_kill_parallel_and_leaves_tree_untouched(self):
        # Match two guards (`_outside_trusted`) across `--jobs 2`. Fake `cargo`
        # detects whether `cargo_boundary.rs` in cwd has `if false {` mutated
        # from baseline, passes baseline, compiles mutants with `--no-run`, and
        # emits `FAILED` for the targeted `--exact` test on mutant runs.
        g_member = next(
            g
            for g in check_rust_guard_mutation.RUST_GUARDS
            if g.guard_id == "cargo_boundary_member_outside_trusted"
        )
        g_dep = next(
            g
            for g in check_rust_guard_mutation.RUST_GUARDS
            if g.guard_id == "cargo_boundary_path_dep_outside_trusted"
        )
        anchor_norm = g_member.anchor
        anchor_dep = g_dep.anchor

        fake_cargo = textwrap.dedent(
            f"""\
            args = sys.argv[1:]
            if "--test" in args:
                assert args[args.index("-p") + 1] == "anneal-audit-tests", args
            src = Path("trusted/audit/src/cargo_boundary.rs").read_text(encoding="utf-8")
            is_mutant = ({anchor_norm!r} not in src) or ({anchor_dep!r} not in src)
            if "--no-run" in args:
                sys.exit(0)
            test_name = args[args.index("--exact") + 1]
            print("running 1 test")
            if is_mutant:
                print(f"test {{test_name}} ... FAILED")
                print("test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured;")
                sys.exit(101)
            print(f"test {{test_name}} ... ok")
            print("test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured;")
            sys.exit(0)
            """
        )
        rc, out, err, report, before, after = self._run_synthetic_suite(
            fake_cargo,
            suite="anneal_audit",
            name_filter="_outside_trusted",
            jobs=2,
        )
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(before, after)
        assert report is not None
        self.assertEqual(report["total"], 2)
        self.assertEqual(report["killed"], 2)
        self.assertEqual(report["survived"], 0)
        self.assertEqual(report["errors"], 0)
        self.assertEqual(report["kill_rate_pct"], 100.0)

    def test_runner_blocks_compile_error_masquerade_survived_and_empty_baseline(self):
        g = next(
            x
            for x in check_rust_guard_mutation.RUST_GUARDS
            if x.guard_id == "cargo_boundary_member_outside_trusted"
        )

        # Case 1: Compile failure (`--no-run` exits 101) on mutant MUST produce
        # ERROR and NEVER run the test step or count as a kill.
        compile_err_cargo = textwrap.dedent(
            f"""\
            args = sys.argv[1:]
            src = Path("trusted/audit/src/cargo_boundary.rs").read_text(encoding="utf-8")
            is_mutant = {g.anchor!r} not in src
            if "--no-run" in args:
                if is_mutant:
                    print("error[E0308]: mismatched types", file=sys.stderr)
                    sys.exit(101)
                sys.exit(0)
            test_name = args[args.index("--exact") + 1]
            if is_mutant:
                raise AssertionError("test step must not run after compile failure")
            print("running 1 test")
            print(f"test {{test_name}} ... ok")
            print("test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured;")
            sys.exit(0)
            """
        )
        rc1, out1, err1, rep1, before1, after1 = self._run_synthetic_suite(
            compile_err_cargo
        )
        self.assertEqual(rc1, 1, out1 + err1)
        self.assertEqual(before1, after1)
        assert rep1 is not None
        self.assertEqual(rep1["errors"], 1)
        self.assertEqual(rep1["killed"], 0)
        self.assertIn("failed to compile", rep1["results"][0]["detail"])

        # Case 2: Mutant passes targeted test -> SURVIVED -> rc == 1.
        survived_cargo = textwrap.dedent(
            """\
            args = sys.argv[1:]
            if "--no-run" in args:
                sys.exit(0)
            test_name = args[args.index("--exact") + 1]
            print("running 1 test")
            print(f"test {test_name} ... ok")
            print("test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured;")
            sys.exit(0)
            """
        )
        rc2, out2, err2, rep2, _, _ = self._run_synthetic_suite(survived_cargo)
        self.assertEqual(rc2, 1, out2 + err2)
        assert rep2 is not None
        self.assertEqual(rep2["survived"], 1)
        self.assertEqual(rep2["killed"], 0)

        # Case 3: Baseline `--exact` runs 0 tests -> fail before mutants.
        zero_base_cargo = textwrap.dedent(
            """\
            args = sys.argv[1:]
            if "--no-run" in args:
                sys.exit(0)
            print("running 0 tests")
            print("test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured;")
            sys.exit(0)
            """
        )
        rc3, out3, err3, rep3, _, _ = self._run_synthetic_suite(zero_base_cargo)
        self.assertEqual(rc3, 1, out3 + err3)
        self.assertIsNone(rep3)
        self.assertIn("0 tests executed", err3)

    def test_cli_rejects_non_positive_jobs_and_timeout(self):
        import contextlib
        import io

        for flag in ("--jobs", "--timeout-sec"):
            with (
                contextlib.redirect_stderr(io.StringIO()),
                self.assertRaises(SystemExit) as ctx,
            ):
                check_rust_guard_mutation.main(["--list", flag, "0"])
            self.assertEqual(ctx.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
