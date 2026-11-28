# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the TCB guard-mutation CI check (`check_guard_mutation.py`).

These tests run in `anneal-ci-tests` without requiring a Lean toolchain: they
validate static catalog invariants against the live repository sources, test
mutation/classification edge cases (including anti-crash-masquerading guards),
exercise the full runner loop against a deterministic fake `lean` binary, and
verify the `ci-core` check wiring in `ci/checks.toml` and
`anneal/ci/run_anneal_check.sh`.
"""

import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import textwrap
import tomllib
import unittest
from unittest import mock

import check_guard_mutation


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


def _populate_fake_rustc_dev_sysroot(
    sysroot: Path,
    triple: str = "x86_64-unknown-linux-gnu",
) -> None:
    """Populate both `<sysroot>/lib` and target `rustlib` `rustc-dev` files."""
    (sysroot / "lib").mkdir(parents=True, exist_ok=True)
    (sysroot / "lib" / "librustc_driver-fake.so").write_bytes(b"so")
    rustlib_dir = sysroot / "lib" / "rustlib" / triple / "lib"
    rustlib_dir.mkdir(parents=True, exist_ok=True)
    (rustlib_dir / "librustc_driver-fake.so").write_bytes(b"so")
    (rustlib_dir / "librustc_middle-fake.rmeta").write_bytes(b"rmeta")


def _write_fake_probe_rustc(
    bin_path: Path,
    *,
    commit_hash: str,
    triple: str,
    sysroot: Path,
    label: str = "fake",
    target_arch: str = "x86_64",
    target_os: str = "linux",
    pointer_width: str = "64",
    endian: str = "little",
    cfg_exit_code: int = 0,
) -> None:
    """Create a probe-only fake `rustc` reporting metadata and `--print cfg`."""
    if cfg_exit_code != 0:
        cfg_lines = f"    sys.exit({cfg_exit_code})"
    else:
        cfg_lines = (
            f'    print(\'target_arch="{target_arch}"\')\n'
            f'    print(\'target_os="{target_os}"\')\n'
            f'    print(\'target_pointer_width="{pointer_width}"\')\n'
            f'    print(\'target_endian="{endian}"\')\n'
            "    sys.exit(0)"
        )
    body = textwrap.dedent(
        f"""\
        args = sys.argv[1:]
        if args == ["--version", "--verbose"]:
            print("rustc 1.98.0-nightly ({label})")
            print("commit-hash: {commit_hash}")
            print("host: {triple}")
            sys.exit(0)
        if args == ["--print", "sysroot"]:
            print({str(sysroot)!r})
            sys.exit(0)
        """
    )
    _write_fake_lean(
        bin_path,
        f'{body}if args == ["--print", "cfg"]:\n{cfg_lines}\nsys.exit(1)\n',
    )


def _create_isolated_extract_anneal_root(dest: Path) -> Path:
    """Create a hermetic synthetic `anneal_root` isolated from `$HOME`."""
    for rel in (
        "ci/fixtures/guard_mutation",
        "trusted/lean",
        "trusted/audit",
        "trusted/rustc-capture/src",
    ):
        shutil.copytree(ANNEAL_ROOT / rel, dest / rel)
    (dest / "Cargo.toml").write_text("[workspace]\n", encoding="utf-8")
    return dest


def _isolated_extract_env(
    root: Path,
    base_env: dict[str, str] | None = None,
) -> dict[str, str]:
    """Return an env dict pointing `HOME`/`CARGO_HOME` to clean temp dirs."""
    clean_home = root / "clean_home"
    clean_cargo_home = root / "clean_cargo_home"
    clean_home.mkdir(parents=True, exist_ok=True)
    clean_cargo_home.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ if base_env is None else base_env)
    env["HOME"] = str(clean_home)
    env["CARGO_HOME"] = str(clean_cargo_home)
    return env


class GuardMutationUnitTests(unittest.TestCase):
    def test_live_catalog_static_invariants_and_cli_list(self):
        errors = check_guard_mutation.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertEqual(errors, [], f"catalog invariant errors: {errors}")
        self.assertGreaterEqual(
            len(check_guard_mutation.MIR_SEMANTICS_GUARDS), 342
        )
        self.assertGreaterEqual(
            len(check_guard_mutation.AUDIT_HEADER_GUARDS), 8
        )
        self.assertGreaterEqual(
            len(check_guard_mutation.AUDIT_BOUNDARY_GUARDS), 12
        )
        self.assertGreaterEqual(
            len(check_guard_mutation.EXTRACT_GUARDS), 45
        )
        # Derive the expected module set from `Trusted/MirSemantics/*.lean` on
        # disk rather than trusting `SEMANTICS_MODULES` alone: every file
        # outside `NON_GUARD_SEMANTICS_MODULES` (fixture-only `CanaryFixtures`)
        # must have active guard-mutation coverage.
        discovered_modules = {
            f"Trusted/MirSemantics/{p.stem}"
            for p in (ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics").glob(
                "*.lean"
            )
        }
        expected_modules = discovered_modules - set(
            check_guard_mutation.NON_GUARD_SEMANTICS_MODULES
        )
        self.assertEqual(
            set(check_guard_mutation.SEMANTICS_MODULES), expected_modules
        )
        covered_modules = {
            g.target_module for g in check_guard_mutation.MIR_SEMANTICS_GUARDS
        }
        self.assertEqual(covered_modules, expected_modules)

        with mock.patch.object(
            check_guard_mutation, "NON_GUARD_SEMANTICS_MODULES", ()
        ):
            unlisted_errs = check_guard_mutation.validate_catalog_invariants(
                ANNEAL_ROOT
            )
        self.assertTrue(
            any("outside SEMANTICS_MODULES" in e for e in unlisted_errs),
            unlisted_errs,
        )
        with mock.patch.object(
            check_guard_mutation,
            "NON_GUARD_SEMANTICS_MODULES",
            ("Trusted/MirSemantics/Ops",),
        ):
            overlap_errs = check_guard_mutation.validate_catalog_invariants(
                ANNEAL_ROOT
            )
        self.assertTrue(
            any("overlap" in e for e in overlap_errs),
            overlap_errs,
        )

        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--list"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(res.returncode, 0, res.stderr)
        expected_total = (
            len(check_guard_mutation.MIR_SEMANTICS_GUARDS)
            + len(check_guard_mutation.AUDIT_HEADER_GUARDS)
            + len(check_guard_mutation.AUDIT_BOUNDARY_GUARDS)
            + len(check_guard_mutation.EXTRACT_GUARDS)
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

            @[simp]
            theorem third_thm : True :=
              trivial

            example : True := trivial

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
        self.assertEqual(
            check_guard_mutation.find_theorem_line_span(fixture, "third_thm"),
            (11, 13),
        )
        with self.assertRaisesRegex(ValueError, "not found"):
            check_guard_mutation.find_theorem_line_span(fixture, "missing_thm")

    def test_fixture_import_ceiling_and_forbidden_tokens_gate(self):
        # Comments and string literals are ignored; active bypass tokens fail.
        clean_src = (
            "-- sorry native_decide unsafe axiom\n"
            "/- ofReduceBool admit -/\n"
            'def msg : String := "sorry unsafe"\n'
            "theorem ok_thm : True := trivial\n"
        )
        self.assertEqual(
            check_guard_mutation._find_forbidden_fixture_tokens(clean_src), []
        )
        for tok in (
            "sorry",
            "admit",
            "native_decide",
            "ofReduceBool",
            "axiom",
            "unsafe",
        ):
            self.assertEqual(
                check_guard_mutation._find_forbidden_fixture_tokens(
                    f"theorem t : True := {tok}\n"
                ),
                [tok],
            )

        # Routing a pruned `Layout` guard through `PositiveSanity` (which
        # imports `Trusted.MirSemantics.Boundary`) must be rejected by
        # `validate_catalog_invariants`.
        layout_guard = next(
            g
            for g in check_guard_mutation.MIR_SEMANTICS_GUARDS
            if g.target_module == "Trusted/MirSemantics/Layout"
        )
        bad_guard = check_guard_mutation.MirSemanticsGuard(
            guard_id="bad_layout_import_ceiling",
            target_file=layout_guard.target_file,
            target_module=layout_guard.target_module,
            description="stale downstream import test",
            anchor=layout_guard.anchor,
            replacement=layout_guard.replacement,
            fixture_module=layout_guard.fixture_module,
            theorem_name=layout_guard.theorem_name,
            sanity_module="PositiveSanity",
            needs_wf_helper=False,
        )
        with mock.patch.object(
            check_guard_mutation,
            "MIR_SEMANTICS_GUARDS",
            (bad_guard,),
        ):
            errs = check_guard_mutation.validate_catalog_invariants(ANNEAL_ROOT)
        self.assertTrue(
            any("outside SEMANTICS_DOWNSTREAM" in e for e in errs),
            f"expected import-ceiling error, got {errs}",
        )

        # `public`, `meta`, `import all`, multi-module `import A B`, inline
        # block comments, `;`-separated imports, and multiline imports are all
        # parsed, while Lean char literals containing `"` or `\"` do not blind
        # token/import scanning.
        import_sample = (
            "-- import Trusted.MirSemantics.Boundary\n"
            'def s : String := "import Trusted.MirSemantics.Step"\n'
            "def c1 : Char := '\"'\n"
            "def c2 : Char := '\\\"'\n"
            "meta import Trusted.MirSemantics.State\n"
            "public meta import all Trusted.MirSemantics.Step "
            "Trusted.MirSemantics.Boundary -- trailing\n"
            "/- pre -/ import all Init.Core; import Trusted.MirSemantics.Ops\n"
            "import\n"
            "  Trusted.MirSemantics.Memory\n"
            "  Trusted.MirSemantics.Layout\n"
            "public\n"
            "  meta\n"
            "  import\n"
            "  all\n"
            "  Trusted.MirSemantics.Bytes\n"
            "import «Trusted».MirSemantics.Enum\n"
            "import Trusted.«MirSemantics».Boundary\n"
            'def raw1 := r"a\\"; import Trusted.MirSemantics.Bytes\n'
            'def raw2 := r#"nested " import Trusted.MirSemantics.Step"# '
            "prelude import Trusted.MirSemantics.Layout\n"
            "import Init.Core import Trusted.MirSemantics.Ops "
            "public meta import all Trusted.MirSemantics.Memory\n"
            "theorem after_imports (x' import' : Nat) : True := sorry\n"
        )
        self.assertEqual(
            check_guard_mutation._extract_lean_imports(import_sample),
            [
                "Trusted.MirSemantics.State",
                "Trusted.MirSemantics.Step",
                "Trusted.MirSemantics.Boundary",
                "Init.Core",
                "Trusted.MirSemantics.Ops",
                "Trusted.MirSemantics.Memory",
                "Trusted.MirSemantics.Layout",
                "Trusted.MirSemantics.Bytes",
                "Trusted.MirSemantics.Enum",
                "Trusted.MirSemantics.Boundary",
                "Trusted.MirSemantics.Bytes",
                "Trusted.MirSemantics.Layout",
                "Init.Core",
                "Trusted.MirSemantics.Ops",
                "Trusted.MirSemantics.Memory",
            ],
        )
        for bad_imp in (
            "import «unclosed\n",
            "import Trusted.«unclosed\n",
            "import 123bogus\n",
            "import\ntheorem t : True := trivial\n",
        ):
            with self.assertRaises(ValueError):
                check_guard_mutation._extract_lean_imports(bad_imp)
        self.assertEqual(
            check_guard_mutation._find_forbidden_fixture_tokens(
                'def r1 := r"a\\"\ntheorem t : True := sorry\n'
            ),
            ["sorry"],
        )
        self.assertEqual(
            check_guard_mutation._find_forbidden_fixture_tokens(import_sample),
            ["sorry"],
        )

        # Target-feature negative fixture targets `x86_64-unknown-linux-gnu`
        # (and emits `compile_error!` on any other arch) without unstable
        # target-feature flags.
        tf_guard = next(
            g
            for g in check_guard_mutation.EXTRACT_GUARDS
            if g.guard_id == "extract_reject_target_feature"
        )
        self.assertIn('target_arch = "x86_64"', tf_guard.negative_source)
        self.assertIn("compile_error!", tf_guard.negative_source)
        self.assertLess(
            tf_guard.negative_source.index("compile_error!"),
            tf_guard.negative_source.index("target_feature(enable ="),
        )
        self.assertEqual(tf_guard.allow_unstable_features, ())

        # Capture option forwarding: `--allow-unstable-feature` and
        # `--stdlib-crate` / `--crate-name` propagate to subprocess argv.
        with (
            tempfile.TemporaryDirectory(prefix="anneal-gmut-capargs-") as cap_tmp,
            mock.patch.object(
                check_guard_mutation.subprocess,
                "run",
                return_value=subprocess.CompletedProcess(
                    args=[],
                    returncode=1,
                    stdout='{"status":"unsupported","diagnostics":[],"unsupported":[]}\n',
                    stderr="",
                ),
            ) as mock_run,
        ):
            cap_dir = Path(cap_tmp)
            check_guard_mutation._run_extract_capture(
                Path("/bin/true"),
                "pub fn selected() {}",
                capture_scope="select",
                select_root="selected",
                instantiate_json="",
                allow_unstable_features=("fn_align",),
                work_dir=cap_dir,
                tag="allow_test",
                sysroot="/sys",
                host_triple="x86_64-unknown-linux-gnu",
                env={},
                timeout_sec=10,
            )
            argv_allow = mock_run.call_args.args[0]
            self.assertIn("--allow-unstable-feature", argv_allow)
            self.assertIn("fn_align", argv_allow)
            self.assertEqual(
                argv_allow[argv_allow.index("--crate-name") + 1], "demo"
            )

            check_guard_mutation._run_extract_capture(
                Path("/bin/true"),
                "pub fn selected() {}",
                capture_scope="select",
                select_root="selected",
                instantiate_json="",
                stdlib_crate="core",
                work_dir=cap_dir,
                tag="stdlib_test",
                sysroot="/sys",
                host_triple="x86_64-unknown-linux-gnu",
                env={},
                timeout_sec=10,
            )
            argv_core = mock_run.call_args.args[0]
            self.assertIn("--stdlib-crate", argv_core)
            self.assertEqual(
                argv_core[argv_core.index("--stdlib-crate") + 1], "core"
            )
            self.assertEqual(
                argv_core[argv_core.index("--crate-name") + 1], "core"
            )

        with tempfile.TemporaryDirectory() as err_tmp:
            err_dir = Path(err_tmp)
            with mock.patch.object(
                check_guard_mutation.subprocess,
                "run",
                side_effect=PermissionError(13, "noexec permission denied"),
            ):
                cap_rc, cap_parsed, cap_out = (
                    check_guard_mutation._run_extract_capture(
                        err_dir / "missing_capture",
                        "pub fn selected() {}",
                        capture_scope="select",
                        select_root="selected",
                        instantiate_json="",
                        work_dir=err_dir,
                        tag="perm_test",
                        sysroot="/sys",
                        host_triple="x86_64-unknown-linux-gnu",
                        env={},
                        timeout_sec=10,
                    )
                )
                unit_rc, unit_out = check_guard_mutation._run_extract_unit_test(
                    err_dir / "missing_unit",
                    "some_test",
                    work_dir=err_dir,
                    env={},
                    timeout_sec=10,
                )
            self.assertEqual(cap_rc, -1)
            self.assertIsNone(cap_parsed)
            self.assertIn("capture launch failed:", cap_out)
            self.assertEqual(unit_rc, -1)
            self.assertIn("unit test launch failed:", unit_out)

        summary_lean_only = check_guard_mutation._format_summary({
            "total": 1,
            "killed": 1,
            "survived": 0,
            "errors": 0,
            "kill_rate_pct": 100.0,
            "baseline_sec": 0.1,
            "total_sec": 0.2,
            "skipped_suites": ["extract_guards"],
            "skipped_reason": "--lean-only requested",
            "results": [],
        })
        self.assertIn("Skipped suites (--lean-only requested):", summary_lean_only)

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
            "heartbeat_limit_exceeded",
            "recursion_depth_exceeded",
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
        self,
        fake_lean_body: str,
        *,
        suite: str = "all",
        extra_env: dict[str, str] | None = None,
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

            filter_name = (
                "ops_div_rem_by_zero"
                if suite == "mir_semantics"
                else (
                    "audit_header_reject_lean_import"
                    if suite == "audit_headers"
                    else "spec_preflight_reject_auto_implicit"
                )
            )
            env = None
            if extra_env is not None:
                env = dict(os.environ)
                env.update(extra_env)
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
                    filter_name,
                    "--jobs",
                    "1",
                    "--json-out",
                    str(json_out),
                ],
                env=env,
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

    def test_checks_toml_wires_guard_mutation(self):
        checks_cfg = tomllib.loads(
            (ANNEAL_ROOT.parent / "ci/checks.toml").read_text(encoding="utf-8")
        )
        checks_by_id = {c["id"]: c for c in checks_cfg["checks"]}
        self.assertIn("anneal-guard-mutation", checks_by_id)
        gm_chk = checks_by_id["anneal-guard-mutation"]
        self.assertEqual(gm_chk.get("image"), "anneal-tc")
        self.assertEqual(gm_chk.get("sandbox"), "nested_bwrap")
        self.assertEqual(gm_chk.get("workdir"), "anneal")
        self.assertNotIn("events", gm_chk)
        self.assertEqual(
            gm_chk.get("command"),
            ["./ci/run_anneal_check.sh", "guard-mutation"],
        )
        gm_includes = {
            pat
            for sel in gm_chk.get("inputs", [])
            for pat in sel.get("include", [])
        }
        for required_pat in (
            "anneal/ci/check_guard_mutation.py",
            "anneal/ci/fixtures/guard_mutation/**",
            "anneal/trusted/lean/**",
            "anneal/trusted/audit/TrustedBoundary.lean",
        ):
            self.assertIn(required_pat, gm_includes)

        runner_src = (CI_DIR / "run_anneal_check.sh").read_text(encoding="utf-8")
        gm_match = re.search(
            r"(?ms)^\s*guard-mutation\)\n(.*?)\n\s*;;$", runner_src
        )
        self.assertIsNotNone(gm_match)
        gm_body = gm_match.group(1)
        self.assertIn("/usr/bin/python3 -I -B ci/check_guard_mutation.py", gm_body)
        self.assertIn("--lean /opt/anneal-nix/lean-toolchain/bin/lean", gm_body)
        self.assertIn("guard-mutation.json", gm_body)

    def test_runner_preserves_module_olean_companion_parts(self):
        # Fake `lean` emits `.olean*` and `.ir*` artifacts like Lean 4 `module`
        # compilation and requires unmodified base modules (`Trusted/MirAst.*`)
        # to be linked into the mutant's `LEAN_PATH` directory while omitting
        # rebuilt modules.
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
            lp_str = str(lean_path)
            is_mutant = "anneal-gmut-" in lp_str and "anneal-gmut-base-" not in lp_str
            if "-o" in args:
                out_path = Path(args[args.index("-o") + 1])
                out_stem = out_path.with_suffix("")
                src = args[-1]
                artifacts = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig")
                if is_mutant and src.endswith("Ops.lean"):
                    for suffix in artifacts:
                        if not (lean_path / f"Trusted/MirAst{{suffix}}").is_file():
                            print(f"missing Trusted/MirAst{{suffix}}", file=sys.stderr)
                            sys.exit(1)
                    if (lean_path / "Trusted/MirSemantics/Ops.olean.server").exists():
                        print("stale Ops.olean.server copied", file=sys.stderr)
                        sys.exit(1)
                    if (lean_path / "Trusted/MirSemantics/Ops.ir").exists():
                        print("stale Ops.ir copied", file=sys.stderr)
                        sys.exit(1)
                for suffix in artifacts:
                    Path(f"{{out_stem}}{{suffix}}").write_bytes(b"fake-olean")
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

    def test_spec_preflight_parity_with_trusted_boundary(self):
        audit_dir = ANNEAL_ROOT / "trusted/audit"
        tb_text = (audit_dir / "TrustedBoundary.lean").read_text(encoding="utf-8")
        sp_text = (audit_dir / "SpecPreflight.lean").read_text(encoding="utf-8")

        decl_re = re.compile(
            r"^(?:(?:private|protected|unsafe|noncomputable) )*(?:partial )?"
            r"def ([A-Za-z_][A-Za-z0-9_'!?]*)",
            re.M,
        )
        boundary_re = re.compile(
            r"^(?:/--|/-!|--|@\[|(?:(?:private|protected|unsafe|noncomputable) )*"
            r"(?:partial )?def |structure |inductive |abbrev |theorem |instance |"
            r"namespace |end |open |section |#)",
            re.M,
        )

        def def_blocks(text: str) -> dict[str, list[str]]:
            # Map every top-level `def` name to its whitespace-normalized
            # body, which runs to the next top-level declaration or comment.
            blocks: dict[str, list[str]] = {}
            for m in decl_re.finditer(text):
                nxt = boundary_re.search(text, m.end())
                body = text[m.start() : nxt.start() if nxt else len(text)]
                blocks.setdefault(m.group(1), []).append(" ".join(body.split()))
            return blocks

        tb_defs = def_blocks(tb_text)
        sp_defs = def_blocks(sp_text)
        # Entry points that intentionally differ (TrustedBoundary serves the
        # repository and legacy target-audit modes as well) and helpers only
        # SpecPreflight defines.
        divergent = {"run", "main"}
        # Definitions that differ only by these whitespace-normalized
        # substitutions: SpecPreflight checks headers with its own
        # `inspectHeaderSyntax` instead of the general `inspectSyntax`.
        header_check = (
            "inspectSyntax (.ofList allowedHeaderKinds) header.raw "
            "(requirePrelude := false) (checkPureRefs := false)",
            "inspectHeaderSyntax header.raw (requirePrelude := false)",
        )
        substituted = {"inspectHeader": [header_check], "preflightSpecs": [header_check]}
        spec_preflight_only = {
            "importSysrootEnv",
            "inspectHeaderSyntax",
            "encodeCanonName",
            "collectSysrootConsts",
            "collectTargetConsts",
            "isPairedUnsafeRec",
            "isRealizedTheoremName",
            "sameConstantInfo",
        }
        for name, body in sp_defs.items():
            if name in divergent:
                self.assertIn(name, tb_defs, name)
                continue
            if name in spec_preflight_only:
                self.assertNotIn(name, tb_defs, f"`{name}` is now shared; check parity")
                continue
            self.assertIn(name, tb_defs, f"SpecPreflight.lean defines unshared `{name}`")
            expected = tb_defs[name]
            for old, new in substituted.get(name, []):
                self.assertEqual(
                    [b.count(old) for b in expected], [1] * len(expected), name
                )
                expected = [b.replace(old, new) for b in expected]
            self.assertEqual(
                body,
                expected,
                f"SpecPreflight.lean drifted from TrustedBoundary.lean on `{name}`",
            )
        # Guard against a vacuous comparison: every security-relevant
        # specification admission definition must be among the shared ones.
        for required in (
            "allowedHeaderKinds",
            "allowedSystemPlatformDecls",
            "forbiddenPureIdentifiers",
            "forbiddenPureRootNamespaces",
            "forbiddenSysUvPrefixes",
            "isForbiddenPureNamespace",
            "isForbiddenPureImport",
            "forbiddenSpecRootNamespaces",
            "forbiddenSpecDeclRootNamespaces",
            "forbiddenSpecIdentifierComponents",
            "forbiddenSpecIdentifiers",
            "forbiddenSpecModifierKinds",
            "allowedSpecCommandKinds",
            "allowedSpecTacticKinds",
            "rejectForbiddenSpecNamespace",
            "rejectForbiddenSpecDeclNamespace",
            "pushSpecScopes",
            "checkSpecDeclNamespace",
            "inspectSpecSyntax",
            "applySpecScope",
            "parseAndInspectSpecCommands",
            "inspectHeader",
            "preflightSpecs",
        ):
            self.assertIn(required, sp_defs, required)
            self.assertNotIn(required, divergent | spec_preflight_only, required)

        # `forbiddenSpecDeclRootNamespaces` (with the
        # `forbiddenSpecRootNamespaces` prefix it extends) must cover every
        # `reservedKernelRoots` root.
        def name_list(text: str, name: str) -> set[str]:
            block = def_blocks(text)[name][0]
            return set(re.findall(r"`([A-Za-z_][A-Za-z0-9_.]*)", block))

        reserved = name_list(tb_text, "reservedKernelRoots")
        self.assertIn("Init", reserved)
        covered = (
            name_list(sp_text, "forbiddenSpecDeclRootNamespaces")
            | name_list(sp_text, "forbiddenSpecRootNamespaces")
            | name_list(sp_text, "forbiddenPureRootNamespaces")
        )
        self.assertEqual(reserved - covered, set())

    def test_runner_audit_boundary_suite_checks_sanity_and_policy_flip(self):
        # Baseline `tb_olean` accepts `resolve-imports` and sanity checks
        # (`spec_sanity` / `target-export`) while rejecting negative fixtures.
        # Mutant (`anneal-gmut-`) preserves sanity and flips negative to ok
        # (KILLED) or keeps rejecting (SURVIVED).
        def make_fake_boundary(
            fail_mutant_sanity: bool, survive_mutant: bool = False
        ) -> str:
            return textwrap.dedent(
                f"""\
                args = sys.argv[1:]
                forbidden_env = [
                    k for k in os.environ
                    if k != "LEAN_PATH"
                    and k.startswith(("LEAN_", "LAKE_", "ELAN_", "LD_", "DYLD_"))
                ]
                if forbidden_env:
                    print(f"unstripped lean env vars: {{forbidden_env}}", file=sys.stderr)
                    sys.exit(2)
                if args == ["--print-prefix"]:
                    if "LEAN_PATH" in os.environ:
                        print("unexpected LEAN_PATH on --print-prefix", file=sys.stderr)
                        sys.exit(2)
                    print("/fake/sysroot")
                    sys.exit(0)
                if "-o" in args:
                    Path(args[args.index("-o") + 1]).write_bytes(b"fake-olean")
                    sys.exit(0)
                if "--run" in args:
                    run_idx = args.index("--run")
                    run_args = args[run_idx + 1 :]
                    if len(run_args) == 1:
                        if "-j1" not in args[:run_idx]:
                            print("missing -j1 on forge script", file=sys.stderr)
                            sys.exit(2)
                        if os.environ.get("LEAN_PATH") != "":
                            print(
                                f"expected empty LEAN_PATH on forge, got {{os.environ.get('LEAN_PATH')!r}}",
                                file=sys.stderr,
                            )
                            sys.exit(2)
                        p = Path(run_args[0])
                        if p.name == "forge_dup_library.lean":
                            (p.parent / "DupLib.olean").write_bytes(b"fake-dup-lib")
                        sys.exit(0)
                    req = json.loads(Path(run_args[1]).read_text())
                    res_path = Path(run_args[2])
                    lean_path = os.environ.get("LEAN_PATH", "")
                    mode = req["mode"]
                    if mode in ("resolve-imports", "target-export"):
                        res_path.write_text(json.dumps({{"ok": True, "result": {{"graph": {{}}}}}}))
                        sys.exit(0)
                    tag_name = Path(run_args[1]).name
                    is_baseline = "tb_olean" in lean_path
                    if "sanity" in tag_name:
                        if {fail_mutant_sanity!r} and not is_baseline:
                            res_path.write_text(json.dumps({{
                                "ok": False,
                                "category": "policy",
                                "message": "broken sanity on mutant",
                            }}))
                            sys.exit(1)
                        res_path.write_text(json.dumps({{"ok": True, "result": {{}}}}))
                        sys.exit(0)
                    if is_baseline or {survive_mutant!r}:
                        res_path.write_text(json.dumps({{
                            "ok": False,
                            "category": "policy",
                            "message": "policy: rejected boundary fixture",
                        }}))
                        sys.exit(1)
                    res_path.write_text(json.dumps({{"ok": True, "result": {{}}}}))
                    sys.exit(0)
                sys.exit(2)
                """
            )

        rc, out, err, report, before, after = self._run_synthetic_suite(
            make_fake_boundary(False),
            suite="audit_boundary",
            extra_env={
                "LEAN_SYSROOT": "/tmp/bogus-lean-sysroot",
                "LEAN_ABORT_ON_PANIC": "1",
                "LAKE_HOME": "/tmp/bogus-lake",
                "ELAN_TOOLCHAIN": "bogus-toolchain",
                "LD_PRELOAD": "/tmp/bogus.so",
                "LD_LIBRARY_PATH": "/tmp/bogus-lib",
                "DYLD_INSERT_LIBRARIES": "/tmp/bogus.dylib",
            },
        )
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(before, after)
        assert report is not None
        self.assertEqual(report["killed"], 1)
        self.assertEqual(report["survived"], 0)
        self.assertEqual(report["errors"], 0)

        # If positive sanity breaks on mutant, status must be ERROR, not KILLED.
        rc2, out2, err2, report2, _, _ = self._run_synthetic_suite(
            make_fake_boundary(True), suite="audit_boundary"
        )
        self.assertEqual(rc2, 1, out2 + err2)
        assert report2 is not None
        self.assertEqual(report2["errors"], 1)
        self.assertEqual(report2["killed"], 0)

        # If mutant still rejects negative fixture, status must be SURVIVED.
        rc3, out3, err3, report3, _, _ = self._run_synthetic_suite(
            make_fake_boundary(False, survive_mutant=True),
            suite="audit_boundary",
        )
        self.assertEqual(rc3, 1, out3 + err3)
        assert report3 is not None
        self.assertEqual(report3["survived"], 1)
        self.assertEqual(report3["killed"], 0)

    def test_validate_catalog_rejects_unknown_boundary_fixture_id(self):
        sample = check_guard_mutation.AUDIT_BOUNDARY_GUARDS[0]
        bad_spec = check_guard_mutation.AuditBoundaryGuard(
            guard_id="bad_spec_fixture",
            target_file=sample.target_file,
            mode="spec-preflight",
            description="unknown spec fixture_id",
            anchor=sample.anchor,
            replacement=sample.replacement,
            fixture_id="nonexistent_spec_fixture",
        )
        bad_target = check_guard_mutation.AuditBoundaryGuard(
            guard_id="bad_target_fixture",
            target_file=sample.target_file,
            mode="target-audit",
            description="mode-mismatched target fixture_id",
            anchor=sample.anchor,
            replacement=sample.replacement,
            fixture_id="spec_auto_implicit",
        )
        with mock.patch.object(
            check_guard_mutation,
            "AUDIT_BOUNDARY_GUARDS",
            (bad_spec, bad_target),
        ):
            errors = check_guard_mutation.validate_catalog_invariants(
                ANNEAL_ROOT
            )
        self.assertTrue(
            any("unknown spec-preflight fixture_id" in e for e in errors),
            errors,
        )
        self.assertTrue(
            any("unknown target-audit fixture_id" in e for e in errors),
            errors,
        )

    def test_semantics_downstream_covers_transitive_importers(self):
        # Verify that for every `target_module` in `SEMANTICS_DOWNSTREAM`,
        # the rebuild list matches the exact intersection of transitive
        # importers of `target_module` and transitive dependencies of all
        # fixture/sanity modules exercised by that module's guards, in
        # topological order, so no stale `.olean` survives a mutant rebuild.
        sem_dir = ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics"
        sem_index = {
            mod: idx
            for idx, mod in enumerate(check_guard_mutation.SEMANTICS_MODULES)
        }
        direct_imp_of: dict[str, set[str]] = {}
        direct_importers: dict[str, set[str]] = {}
        for lean_file in sorted(sem_dir.glob("*.lean")):
            mod = f"Trusted/MirSemantics/{lean_file.stem}"
            if mod not in sem_index:
                continue
            for raw_imp in check_guard_mutation._extract_lean_imports(
                lean_file.read_text(encoding="utf-8")
            ):
                imp = raw_imp.replace(".", "/")
                if imp in sem_index:
                    direct_imp_of.setdefault(mod, set()).add(imp)
                    direct_importers.setdefault(imp, set()).add(mod)

        def closure(adj: dict[str, set[str]], roots: set[str]) -> set[str]:
            seen = set(roots)
            stack = list(roots)
            while stack:
                cur = stack.pop()
                for nxt in adj.get(cur, ()):
                    if nxt not in seen:
                        seen.add(nxt)
                        stack.append(nxt)
            return seen

        fixture_dir = ANNEAL_ROOT / "ci/fixtures/guard_mutation"

        def fixture_semantics_imports(root_mod: str) -> set[str]:
            """Return `Trusted/MirSemantics/*` imports reachable from a fixture."""
            sem_imports: set[str] = set()
            visited: set[str] = set()
            stack = [root_mod]
            while stack:
                cur = stack.pop()
                if cur in visited:
                    continue
                visited.add(cur)
                lean_path = fixture_dir / f"{cur}.lean"
                self.assertTrue(
                    lean_path.is_file(),
                    f"missing fixture module {cur!r} at {lean_path}",
                )
                for line in lean_path.read_text(encoding="utf-8").splitlines():
                    stripped = line.strip()
                    if not stripped.startswith(("import ", "public import ")):
                        continue
                    imp = stripped.split()[-1].replace(".", "/")
                    if imp in sem_index:
                        sem_imports.add(imp)
                    elif (fixture_dir / f"{imp}.lean").is_file():
                        stack.append(imp)
            return sem_imports

        for mod, rebuild_list in check_guard_mutation.SEMANTICS_DOWNSTREAM.items():
            guards = [
                g
                for g in check_guard_mutation.MIR_SEMANTICS_GUARDS
                if g.target_module == mod
            ]
            self.assertTrue(guards, f"expected at least one guard for {mod}")
            roots: set[str] = set()
            for g in guards:
                roots |= fixture_semantics_imports(g.fixture_module)
                roots |= fixture_semantics_imports(g.sanity_module)
                if g.needs_wf_helper:
                    roots |= fixture_semantics_imports("GuardRefuteWf")
            needed_deps = closure(direct_imp_of, roots)
            trans_importers = closure(direct_importers, {mod})
            expected = needed_deps & trans_importers
            actual = set(rebuild_list)
            if mod == "Trusted/MirSemantics/Memory":
                self.assertEqual(actual, {"Trusted/MirSemantics/Memory"})
                for g in guards:
                    self.assertFalse(g.needs_wf_helper)
            elif mod == "Trusted/MirSemantics/Layout":
                self.assertTrue(
                    actual
                    <= {
                        "Trusted/MirSemantics/Layout",
                        "Trusted/MirSemantics/Memory",
                        "Trusted/MirSemantics/Bytes",
                    }
                )
                for g in guards:
                    self.assertFalse(g.needs_wf_helper)
            self.assertEqual(
                actual,
                expected,
                f"SEMANTICS_DOWNSTREAM[{mod!r}] missing or extra modules: "
                f"missing={sorted(expected - actual)}, "
                f"extra={sorted(actual - expected)}",
            )
            self.assertEqual(
                list(rebuild_list),
                sorted(rebuild_list, key=sem_index.__getitem__),
                f"SEMANTICS_DOWNSTREAM[{mod!r}] is not in topological order",
            )

    def _run_synthetic_extract_suite(
        self,
        *,
        filter_name: str,
        outcome: str,
        timeout_sec: int = 60,
    ) -> tuple[int, str, str, dict[str, object] | None, dict[str, str], dict[str, str]]:
        """Run `extract_guards` against deterministic fake `rustc`/`cargo`."""
        pinned_commit = check_guard_mutation._read_pinned_compiler_commit(
            ANNEAL_ROOT
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-ext-unit-") as tmp:
            tmp_path = Path(tmp)
            iso_anneal = _create_isolated_extract_anneal_root(
                tmp_path / "anneal_iso"
            )
            ext_env = _isolated_extract_env(tmp_path)
            sysroot = tmp_path / "sysroot"
            _populate_fake_rustc_dev_sysroot(sysroot)

            fake_rustc = tmp_path / "rustc"
            fake_cargo = tmp_path / "cargo"
            json_out = tmp_path / "report.json"

            _write_fake_lean(
                fake_rustc,
                textwrap.dedent(
                    f"""\
                    args = sys.argv[1:]
                    if args == ["--version", "--verbose"]:
                        print("rustc 1.98.0-nightly (fake)")
                        print("commit-hash: {pinned_commit}")
                        print("host: x86_64-unknown-linux-gnu")
                        sys.exit(0)
                    if args == ["--print", "sysroot"]:
                        print({str(sysroot)!r})
                        sys.exit(0)
                    if args == ["--print", "cfg"]:
                        print('target_arch="x86_64"')
                        print('target_os="linux"')
                        print('target_pointer_width="64"')
                        print('target_endian="little"')
                        sys.exit(0)
                    if "-o" in args:
                        out_path = Path(args[args.index("-o") + 1])
                        if {outcome!r} == "compile_fail":
                            print("error[E0308]: mismatched types", file=sys.stderr)
                            sys.exit(1)
                        if out_path.name.endswith(".rlib"):
                            out_path.write_bytes(b"fake-rlib")
                            sys.exit(0)
                        if "--test" in args:
                            script = (
                                "#!{sys.executable}\\n"
                                "import sys\\n"
                                "tname = sys.argv[2]\\n"
                                "is_sanity = 'use_retag' in tname\\n"
                                "outcome = {outcome!r}\\n"
                                "if is_sanity:\\n"
                                "    if outcome == 'sanity_break':\\n"
                                "        print(f'test {{tname}} ... FAILED')\\n"
                                "        print('test result: FAILED. 0 passed; 1 failed')\\n"
                                "        sys.exit(101)\\n"
                                "    print(f'test {{tname}} ... ok')\\n"
                                "    print('test result: ok. 1 passed; 0 failed')\\n"
                                "    sys.exit(0)\\n"
                                "if outcome == 'survive':\\n"
                                "    print(f'test {{tname}} ... ok')\\n"
                                "    print('test result: ok. 1 passed; 0 failed')\\n"
                                "    sys.exit(0)\\n"
                                "if outcome == 'unit_crash':\\n"
                                "    print('thread panicked with SIGABRT')\\n"
                                "    sys.exit(134)\\n"
                                "print(f'test {{tname}} ... FAILED')\\n"
                                "print('test result: FAILED. 0 passed; 1 failed')\\n"
                                "sys.exit(101)\\n"
                            )
                        else:
                            script = (
                                "#!{sys.executable}\\n"
                                "import json, sys, time\\n"
                                "src = sys.argv[sys.argv.index('--crate-root') + 1]\\n"
                                "is_sanity = 'sanity_' in src\\n"
                                "outcome = {outcome!r}\\n"
                                "if is_sanity:\\n"
                                "    if outcome == 'sanity_break':\\n"
                                "        print(json.dumps({{'status': 'unsupported', "
                                "'diagnostics': ['sanity broke'], 'unsupported': []}}))\\n"
                                "        sys.exit(1)\\n"
                                "    print(json.dumps({{'status': 'captured'}}))\\n"
                                "    sys.exit(0)\\n"
                                "if outcome == 'timeout':\\n"
                                "    time.sleep(3)\\n"
                                "    sys.exit(0)\\n"
                                "if outcome == 'tool_failed':\\n"
                                "    print(json.dumps({{'status': 'tool_failed', "
                                "'diagnostics': ['ICE'], 'unsupported': []}}))\\n"
                                "    sys.exit(1)\\n"
                                "if outcome == 'compiler_failed_err':\\n"
                                "    print(json.dumps({{'status': 'compiler_failed', "
                                "'diagnostics': ['rustc err'], 'unsupported': []}}))\\n"
                                "    sys.exit(1)\\n"
                                "if outcome == 'kill':\\n"
                                "    print(json.dumps({{'status': 'captured'}}))\\n"
                                "    sys.exit(0)\\n"
                                "if outcome == 'fallback_kill':\\n"
                                "    print(json.dumps({{'status': 'unsupported', "
                                "'diagnostics': [], 'unsupported': "
                                "[{{'reason': 'unsupported type: Guard'}}]}}))\\n"
                                "    sys.exit(1)\\n"
                                "print(json.dumps({{'status': 'unsupported', "
                                "'diagnostics': ['function alignment'], 'unsupported': "
                                "[{{'reason': 'cleanup block bb1'}}]}}))\\n"
                                "sys.exit(1)\\n"
                            )
                        out_path.write_text(script, encoding="utf-8")
                        out_path.chmod(0o755)
                        sys.exit(0)
                    sys.exit(2)
                    """
                ),
            )
            _write_fake_lean(
                fake_cargo,
                textwrap.dedent(
                    f"""\
                    args = sys.argv[1:]
                    if args == ["--version"]:
                        print("cargo 1.98.0")
                        sys.exit(0)
                    tdir = Path(args[args.index("--target-dir") + 1])
                    deps = tdir / "debug" / "deps"
                    deps.mkdir(parents=True, exist_ok=True)
                    for dep in {check_guard_mutation.EXTRACT_DIRECT_DEPS!r}:
                        rlib = deps / f"lib{{dep}}-deadbeef.rlib"
                        rlib.write_bytes(b"rlib")
                        print(json.dumps({{
                            "reason": "compiler-artifact",
                            "target": {{"name": dep, "kind": ["lib"]}},
                            "profile": {{"test": False}},
                            "filenames": [str(rlib)],
                        }}))
                    if args[0] == "test":
                        unit_exe = deps / "anneal_rustc_capture-unit"
                        unit_exe.write_text(
                            "#!{sys.executable}\\n"
                            "import sys\\n"
                            "tname = sys.argv[2]\\n"
                            "print(f'test {{tname}} ... ok')\\n"
                            "print('test result: ok. 1 passed; 0 failed')\\n",
                            encoding="utf-8",
                        )
                        unit_exe.chmod(0o755)
                        print(json.dumps({{
                            "reason": "compiler-artifact",
                            "target": {{"name": "anneal_rustc_capture", "kind": ["lib"]}},
                            "profile": {{"test": True}},
                            "executable": str(unit_exe),
                            "filenames": [str(unit_exe)],
                        }}))
                    else:
                        cap_exe = tdir / "debug" / "anneal-rustc-capture"
                        cap_exe.write_text(
                            "#!{sys.executable}\\n"
                            "import json, sys\\n"
                            "src = sys.argv[sys.argv.index('--crate-root') + 1]\\n"
                            "if 'sanity_' in src or {outcome!r} == 'baseline_mismatch':\\n"
                            "    print(json.dumps({{'status': 'captured'}}))\\n"
                            "    sys.exit(0)\\n"
                            "print(json.dumps({{'status': 'unsupported', "
                            "'diagnostics': ['function alignment'], "
                            "'unsupported': [{{'reason': 'cleanup block bb1'}}]}}))\\n"
                            "sys.exit(1)\\n",
                            encoding="utf-8",
                        )
                        cap_exe.chmod(0o755)
                        print(json.dumps({{
                            "reason": "compiler-artifact",
                            "target": {{"name": "anneal-rustc-capture", "kind": ["bin"]}},
                            "profile": {{"test": False}},
                            "executable": str(cap_exe),
                            "filenames": [str(cap_exe)],
                        }}))
                    sys.exit(0)
                    """
                ),
            )

            tracked = [
                ANNEAL_ROOT / "trusted/rustc-capture/src/extract.rs",
                ANNEAL_ROOT / "trusted/rustc-capture/src/capture.rs",
                ANNEAL_ROOT / "trusted/rustc-capture/src/ir.rs",
                ANNEAL_ROOT / "trusted/rustc-capture/src/mono.rs",
            ]
            before = {
                str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in tracked
            }
            res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(iso_anneal),
                    "--rustc",
                    str(fake_rustc),
                    "--suite",
                    "extract_guards",
                    "--filter",
                    filter_name,
                    "--jobs",
                    "1",
                    "--timeout-sec",
                    str(timeout_sec),
                    "--json-out",
                    str(json_out),
                ],
                env=ext_env,
                capture_output=True,
                text=True,
            )
            after = {
                str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in tracked
            }
            parsed = (
                json.loads(json_out.read_text(encoding="utf-8"))
                if json_out.is_file()
                else None
            )
            return res.returncode, res.stdout, res.stderr, parsed, before, after

    def test_runner_extract_guards_suite_capture_and_unit_modes(self):
        # Capture mode: KILLED, SURVIVED, sanity-broken ERROR, compile ERROR,
        # tool_failed ERROR, timeout ERROR, precedence fallback KILLED,
        # fallback compiler_failed/tool_failed ERROR, and baseline mismatch.
        rc, out, err, rep, before, after = self._run_synthetic_extract_suite(
            filter_name="extract_reject_fn_alignment",
            outcome="kill",
        )
        self.assertEqual(rc, 0, out + err)
        self.assertEqual(before, after)
        assert rep is not None
        self.assertEqual(rep["killed"], 1)
        self.assertEqual(rep["survived"], 0)
        self.assertEqual(rep["errors"], 0)

        rc_s, _, _, rep_s, _, _ = self._run_synthetic_extract_suite(
            filter_name="extract_reject_fn_alignment",
            outcome="survive",
        )
        self.assertEqual(rc_s, 1)
        assert rep_s is not None
        self.assertEqual(rep_s["survived"], 1)

        for err_outcome in ("sanity_break", "compile_fail", "tool_failed"):
            rc_e, _, _, rep_e, _, _ = self._run_synthetic_extract_suite(
                filter_name="extract_reject_fn_alignment",
                outcome=err_outcome,
            )
            self.assertEqual(rc_e, 1, err_outcome)
            assert rep_e is not None
            self.assertEqual(rep_e["errors"], 1, err_outcome)
            self.assertEqual(rep_e["killed"], 0, err_outcome)

        rc_to, _, _, rep_to, _, _ = self._run_synthetic_extract_suite(
            filter_name="extract_reject_fn_alignment",
            outcome="timeout",
            timeout_sec=1,
        )
        self.assertEqual(rc_to, 1)
        assert rep_to is not None
        self.assertEqual(rep_to["errors"], 1)
        self.assertEqual(rep_to["killed"], 0)

        rc_fb, out_fb, err_fb, rep_fb, _, _ = self._run_synthetic_extract_suite(
            filter_name="extract_reject_cleanup_block",
            outcome="fallback_kill",
        )
        self.assertEqual(rc_fb, 0, out_fb + err_fb)
        assert rep_fb is not None
        self.assertEqual(rep_fb["killed"], 1)

        for fb_err in ("tool_failed", "compiler_failed_err"):
            rc_fbe, _, _, rep_fbe, _, _ = self._run_synthetic_extract_suite(
                filter_name="extract_reject_cleanup_block",
                outcome=fb_err,
            )
            self.assertEqual(rc_fbe, 1, fb_err)
            assert rep_fbe is not None
            self.assertEqual(rep_fbe["errors"], 1, fb_err)
            self.assertEqual(rep_fbe["killed"], 0, fb_err)

        rc_bm, _, err_bm, rep_bm, _, _ = self._run_synthetic_extract_suite(
            filter_name="extract_reject_fn_alignment",
            outcome="baseline_mismatch",
        )
        self.assertEqual(rc_bm, 1)
        self.assertIsNone(rep_bm)
        self.assertIn("baseline anneal-rustc-capture did not reject", err_bm)

        # Unit mode: KILLED, SURVIVED, sanity-broken ERROR, compile ERROR,
        # and crash (rc != 101) ERROR.
        rc_u, out_u, err_u, rep_u, b_u, a_u = self._run_synthetic_extract_suite(
            filter_name="extract_rodata_reject_provenance",
            outcome="kill",
        )
        self.assertEqual(rc_u, 0, out_u + err_u)
        self.assertEqual(b_u, a_u)
        assert rep_u is not None
        self.assertEqual(rep_u["killed"], 1)

        rc_us, _, _, rep_us, _, _ = self._run_synthetic_extract_suite(
            filter_name="extract_rodata_reject_provenance",
            outcome="survive",
        )
        self.assertEqual(rc_us, 1)
        assert rep_us is not None
        self.assertEqual(rep_us["survived"], 1)

        for u_err in ("sanity_break", "compile_fail", "unit_crash"):
            rc_ue, _, _, rep_ue, _, _ = self._run_synthetic_extract_suite(
                filter_name="extract_rodata_reject_provenance",
                outcome=u_err,
            )
            self.assertEqual(rc_ue, 1, u_err)
            assert rep_ue is not None
            self.assertEqual(rep_ue["errors"], 1, u_err)
            self.assertEqual(rep_ue["killed"], 0, u_err)

    def test_extract_guards_fail_closed_when_explicit_and_skip_in_lean_only_all(
        self,
    ):
        # Explicit `--suite extract_guards` with missing `--rustc` or with
        # ambient `RUSTC`/`PATH` pointing to a wrong commit must fail closed.
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-norustc-") as tmp:
            tmp_path = Path(tmp)
            iso_anneal = _create_isolated_extract_anneal_root(
                tmp_path / "anneal_iso"
            )
            bad_rustc = tmp_path / "missing_rustc"
            res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(iso_anneal),
                    "--rustc",
                    str(bad_rustc),
                    "--suite",
                    "extract_guards",
                ],
                env=_isolated_extract_env(tmp_path),
                capture_output=True,
                text=True,
            )
            self.assertEqual(res.returncode, 1)
            self.assertIn("pinned nightly rustc", res.stderr)

            wrong_rustc = tmp_path / "rustc"
            _write_fake_lean(
                wrong_rustc,
                textwrap.dedent(
                    """\
                    if sys.argv[1:] == ["--version", "--verbose"]:
                        print("rustc 1.85.0 (stable)")
                        print("commit-hash: 0000000000000000000000000000000000000000")
                        print("host: x86_64-unknown-linux-gnu")
                        sys.exit(0)
                    sys.exit(1)
                    """
                ),
            )
            env = _isolated_extract_env(tmp_path)
            env["RUSTC"] = str(wrong_rustc)
            env["PATH"] = str(tmp_path)
            res_env = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(iso_anneal),
                    "--suite",
                    "extract_guards",
                ],
                capture_output=True,
                text=True,
                env=env,
            )
            self.assertEqual(res_env.returncode, 1)
            self.assertIn("pinned nightly rustc", res_env.stderr)

        # In `--suite all` when pinned nightly rustc is unavailable (e.g.
        # lean-only CI job), Lean suites execute and `extract_guards` is
        # recorded in `skipped_suites`.
        ops_span = check_guard_mutation.find_theorem_line_span(
            (
                ANNEAL_ROOT / "ci/fixtures/guard_mutation/OpsRefutations.lean"
            ).read_text(encoding="utf-8"),
            "refute_ops_div_rem_by_zero",
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-leanonly-") as tmp:
            fake_lean = Path(tmp) / "fake_lean"
            _write_fake_lean(
                fake_lean,
                textwrap.dedent(
                    f"""\
                    args = sys.argv[1:]
                    lean_path = os.environ.get("LEAN_PATH", "")
                    is_mutant = "anneal-gmut-" in lean_path and "anneal-gmut-base-" not in lean_path
                    if "-o" in args:
                        Path(args[args.index("-o") + 1]).write_bytes(b"fake-olean")
                        if is_mutant and args[-1].endswith("OpsRefutations.lean"):
                            print(f"{{args[-1]}}:{ops_span[0]}:2: error: Type mismatch (rfl)")
                            sys.exit(1)
                        sys.exit(0)
                    sys.exit(0)
                    """
                ),
            )
            one_mir = [
                g
                for g in check_guard_mutation.MIR_SEMANTICS_GUARDS
                if g.guard_id == "ops_div_rem_by_zero"
            ]
            one_ext = [
                g
                for g in check_guard_mutation.EXTRACT_GUARDS
                if g.guard_id == "extract_reject_fn_alignment"
            ]
            with (
                mock.patch.object(
                    check_guard_mutation,
                    "_select_guards",
                    return_value=(one_mir, [], [], one_ext),
                ),
                mock.patch.object(
                    check_guard_mutation,
                    "_resolve_extract_toolchain",
                    return_value=None,
                ),
            ):
                report = check_guard_mutation.run_guard_mutation_suite(
                    anneal_root=ANNEAL_ROOT,
                    lean_bin=fake_lean,
                    suite="all",
                    jobs=1,
                )
            self.assertEqual(report["killed"], 1)
            self.assertEqual(report["survived"], 0)
            self.assertEqual(report["errors"], 0)
            self.assertEqual(report["skipped_suites"], ["extract_guards"])

    def test_relative_tool_paths_resolve_before_temp_cwd_execution(self):
        pinned_commit = check_guard_mutation._read_pinned_compiler_commit(
            ANNEAL_ROOT
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-relpath-") as tmp:
            caller_cwd = Path(tmp)
            tc_bin = caller_cwd / "rel_tc" / "bin"
            tc_bin.mkdir(parents=True)
            sysroot = caller_cwd / "rel_tc" / "sysroot"
            _populate_fake_rustc_dev_sysroot(sysroot)

            rustc_body = textwrap.dedent(
                f"""\
                args = sys.argv[1:]
                if args == ["--version", "--verbose"]:
                    print("rustc 1.98.0-nightly (fake)")
                    print("commit-hash: {pinned_commit}")
                    print("host: x86_64-unknown-linux-gnu")
                    sys.exit(0)
                if args == ["--print", "sysroot"]:
                    print({str(sysroot)!r})
                    sys.exit(0)
                if args == ["--print", "cfg"]:
                    print('target_arch="x86_64"')
                    print('target_os="linux"')
                    print('target_pointer_width="64"')
                    print('target_endian="little"')
                    sys.exit(0)
                if "-o" in args:
                    out_path = Path(args[args.index("-o") + 1])
                    if out_path.name.endswith(".rlib"):
                        out_path.write_bytes(b"fake-rlib")
                        sys.exit(0)
                    out_path.write_text(
                        "#!{sys.executable}\\n"
                        "import json, sys\\n"
                        "print(json.dumps({{'status': 'captured'}}))\\n"
                        "sys.exit(0)\\n",
                        encoding="utf-8",
                    )
                    out_path.chmod(0o755)
                    sys.exit(0)
                sys.exit(2)
                """
            )
            cargo_body = textwrap.dedent(
                f"""\
                args = sys.argv[1:]
                if args == ["--version"]:
                    print("cargo 1.98.0")
                    sys.exit(0)
                if not Path(os.environ["RUSTC"]).is_absolute():
                    sys.exit(9)
                tdir = Path(args[args.index("--target-dir") + 1])
                deps = tdir / "debug" / "deps"
                deps.mkdir(parents=True, exist_ok=True)
                for dep in {check_guard_mutation.EXTRACT_DIRECT_DEPS!r}:
                    rlib = deps / f"lib{{dep}}-deadbeef.rlib"
                    rlib.write_bytes(b"rlib")
                    print(json.dumps({{
                        "reason": "compiler-artifact",
                        "target": {{"name": dep, "kind": ["lib"]}},
                        "profile": {{"test": False}},
                        "filenames": [str(rlib)],
                    }}))
                cap_exe = tdir / "debug" / "anneal-rustc-capture"
                cap_exe.write_text(
                    "#!{sys.executable}\\n"
                    "import json, sys\\n"
                    "src = sys.argv[sys.argv.index('--crate-root') + 1]\\n"
                    "if 'sanity_' in src:\\n"
                    "    print(json.dumps({{'status': 'captured'}}))\\n"
                    "    sys.exit(0)\\n"
                    "print(json.dumps({{'status': 'unsupported', "
                    "'diagnostics': ['function alignment'], "
                    "'unsupported': []}}))\\n"
                    "sys.exit(1)\\n",
                    encoding="utf-8",
                )
                cap_exe.chmod(0o755)
                print(json.dumps({{
                    "reason": "compiler-artifact",
                    "target": {{"name": "anneal-rustc-capture", "kind": ["bin"]}},
                    "profile": {{"test": False}},
                    "executable": str(cap_exe),
                    "filenames": [str(cap_exe)],
                }}))
                sys.exit(0)
                """
            )
            _write_fake_lean(tc_bin / "rustc", rustc_body)
            _write_fake_lean(tc_bin / "cargo", cargo_body)

            iso_anneal = _create_isolated_extract_anneal_root(
                caller_cwd / "anneal_iso"
            )
            rel_anneal = os.path.relpath(iso_anneal, caller_cwd)
            env_clean = {
                k: v
                for k, v in _isolated_extract_env(caller_cwd).items()
                if k not in ("RUSTC", "CARGO")
            }
            env_clean["PATH"] = "/usr/bin:/bin"
            res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    rel_anneal,
                    "--rustc",
                    "rel_tc/bin/rustc",
                    "--suite",
                    "extract_guards",
                    "--filter",
                    "extract_reject_fn_alignment",
                    "--jobs",
                    "1",
                    "--json-out",
                    "rel_out/report.json",
                ],
                cwd=caller_cwd,
                env=env_clean,
                capture_output=True,
                text=True,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            rep = json.loads(
                (caller_cwd / "rel_out" / "report.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(rep["killed"], 1)

            # Separate relative `RUSTC` and `CARGO` env vars without sibling
            # `cargo`, plus fail-closed check on missing explicit `CARGO`.
            only_rustc_dir = caller_cwd / "rel_rustc_only"
            only_cargo_dir = caller_cwd / "rel_cargo_only"
            only_rustc_dir.mkdir()
            only_cargo_dir.mkdir()
            _write_fake_lean(only_rustc_dir / "rustc", rustc_body)
            _write_fake_lean(only_cargo_dir / "cargo", cargo_body)

            env_sep = dict(env_clean)
            env_sep["RUSTC"] = "rel_rustc_only/rustc"
            env_sep["CARGO"] = "rel_cargo_only/cargo"
            res_sep = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    rel_anneal,
                    "--suite",
                    "extract_guards",
                    "--filter",
                    "extract_reject_fn_alignment",
                    "--jobs",
                    "1",
                ],
                cwd=caller_cwd,
                env=env_sep,
                capture_output=True,
                text=True,
            )
            self.assertEqual(
                res_sep.returncode, 0, res_sep.stdout + res_sep.stderr
            )

            env_bad_cargo = dict(env_sep)
            env_bad_cargo["CARGO"] = "rel_missing/cargo"
            res_bad = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    rel_anneal,
                    "--suite",
                    "extract_guards",
                    "--filter",
                    "extract_reject_fn_alignment",
                    "--jobs",
                    "1",
                ],
                cwd=caller_cwd,
                env=env_bad_cargo,
                capture_output=True,
                text=True,
            )
            self.assertEqual(res_bad.returncode, 1)
            self.assertIn("does not point to a runnable cargo", res_bad.stderr)

    def test_extract_guards_derives_target_triple_and_host_deps_dirs_from_cargo_json(
        self,
    ):
        # When `CARGO_BUILD_TARGET` or `.cargo/config.toml` sets `build.target`
        # to the host triple, Cargo places target `.rlib`s + executables under
        # `<target-dir>/<triple>/debug/...` while host proc-macro shared
        # libraries live under `<target-dir>/debug/deps`. Direct `rustc` mutant
        # builds (both `capture` and `unit` modes) must pass `-L dependency=...`
        # for both artifact directories.
        pinned_commit = check_guard_mutation._read_pinned_compiler_commit(
            ANNEAL_ROOT
        )
        triple = "x86_64-unknown-linux-gnu"
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-target-deps-") as tmp:
            root = Path(tmp)
            iso_anneal = _create_isolated_extract_anneal_root(
                root / "anneal_iso"
            )
            tc_bin = root / "bin"
            sysroot = root / "sysroot"
            tc_bin.mkdir(parents=True)
            _populate_fake_rustc_dev_sysroot(sysroot, triple)

            rustc_body = textwrap.dedent(
                f"""\
                args = sys.argv[1:]
                if args == ["--version", "--verbose"]:
                    print("rustc 1.98.0-nightly (fake)")
                    print("commit-hash: {pinned_commit}")
                    print("host: {triple}")
                    sys.exit(0)
                if args == ["--print", "sysroot"]:
                    print({str(sysroot)!r})
                    sys.exit(0)
                if args == ["--print", "cfg"]:
                    print('target_arch="x86_64"')
                    print('target_os="linux"')
                    print('target_pointer_width="64"')
                    print('target_endian="little"')
                    sys.exit(0)
                if "-o" in args:
                    if (
                        "--target" not in args
                        or args[args.index("--target") + 1] != {triple!r}
                    ):
                        print(f"missing --target {triple}: {{args}}", file=sys.stderr)
                        sys.exit(10)
                    if not any(
                        args[i] == "-C" and args[i + 1] == "panic=unwind"
                        for i in range(len(args) - 1)
                    ):
                        print(f"missing -C panic=unwind: {{args}}", file=sys.stderr)
                        sys.exit(13)
                    dep_dirs = [
                        args[i + 1][len("dependency="):]
                        for i, tok in enumerate(args[:-1])
                        if tok == "-L" and args[i + 1].startswith("dependency=")
                    ]
                    has_triple = any(
                        p.endswith("{triple}/debug/deps") for p in dep_dirs
                    )
                    has_host = any(
                        p.endswith("/extract_target/debug/deps")
                        for p in dep_dirs
                    )
                    if not (has_triple and has_host):
                        print(
                            f"missing expected -L dependency dirs: {{dep_dirs}}",
                            file=sys.stderr,
                        )
                        sys.exit(7)
                    if any(
                        k.startswith("CARGO_TARGET_")
                        and k.endswith(("_RUSTFLAGS", "_LINKER"))
                        for k in os.environ
                    ):
                        print("unsanitized CARGO_TARGET_* env in rustc", file=sys.stderr)
                        sys.exit(13)
                    out_path = Path(args[args.index("-o") + 1])
                    if out_path.name.endswith(".rlib"):
                        out_path.write_bytes(b"fake-rlib")
                        sys.exit(0)
                    if "--test" in args:
                        out_path.write_text(
                            "#!{sys.executable}\\n"
                            "import sys\\n"
                            "tname = sys.argv[2]\\n"
                            "if 'no_provenance' in tname:\\n"
                            "    print(f'test {{tname}} ... FAILED')\\n"
                            "    print('test result: FAILED. 0 passed; 1 failed')\\n"
                            "    sys.exit(101)\\n"
                            "print(f'test {{tname}} ... ok')\\n"
                            "print('test result: ok. 1 passed; 0 failed')\\n"
                            "sys.exit(0)\\n",
                            encoding="utf-8",
                        )
                    else:
                        out_path.write_text(
                            "#!{sys.executable}\\n"
                            "import json, sys\\n"
                            "print(json.dumps({{'status': 'captured'}}))\\n"
                            "sys.exit(0)\\n",
                            encoding="utf-8",
                        )
                    out_path.chmod(0o755)
                    sys.exit(0)
                sys.exit(2)
                """
            )
            cargo_body = textwrap.dedent(
                f"""\
                args = sys.argv[1:]
                if args == ["--version"]:
                    print("cargo 1.98.0")
                    sys.exit(0)
                if (
                    "--target" not in args
                    or args[args.index("--target") + 1] != {triple!r}
                ):
                    print(f"missing --target {triple} on cargo: {{args}}", file=sys.stderr)
                    sys.exit(9)
                if "--locked" not in args or "--offline" not in args:
                    print(f"missing --locked/--offline on cargo: {{args}}", file=sys.stderr)
                    sys.exit(16)
                cbt = os.environ.get("CARGO_BUILD_TARGET")
                if cbt not in (None, "", {triple!r}):
                    print(f"unsanitized cross CARGO_BUILD_TARGET={{cbt!r}}", file=sys.stderr)
                    sys.exit(8)
                if (
                    "--config" not in args
                    or args[args.index("--config") + 1]
                    != 'profile.dev.panic="unwind"'
                ):
                    print(f"missing profile.dev.panic=unwind --config: {{args}}", file=sys.stderr)
                    sys.exit(14)
                if Path.cwd().resolve() != Path({str(iso_anneal)!r}).resolve():
                    print(f"expected cargo cwd={iso_anneal}, got {{Path.cwd()}}", file=sys.stderr)
                    sys.exit(15)
                expected_encoded = (
                    "-Lnative="
                    + {str(sysroot / "lib")!r}
                    + "\\x1f-Clink-arg=-Wl,-rpath,"
                    + {str(sysroot / "lib")!r}
                )
                if (
                    os.environ.get("CARGO_ENCODED_RUSTFLAGS") != expected_encoded
                    or "RUSTFLAGS" in os.environ
                    or any(
                        k.startswith("CARGO_TARGET_")
                        and k.endswith(("_RUSTFLAGS", "_LINKER"))
                        for k in os.environ
                    )
                    or {str(sysroot / "lib")!r} not in os.environ.get("LD_LIBRARY_PATH", "").split(os.pathsep)
                    or {str(sysroot / "lib")!r} not in os.environ.get("DYLD_LIBRARY_PATH", "").split(os.pathsep)
                    or os.environ.get("CARGO_NET_OFFLINE") != "true"
                    or os.environ.get("CARGO_PROFILE_DEV_PANIC") != "unwind"
                    or "CARGO_PROFILE_TEST_PANIC" in os.environ
                    or os.environ.get("RUSTC_WRAPPER") != ""
                    or os.environ.get("RUSTC_WORKSPACE_WRAPPER") != ""
                    or "CARGO_BUILD_RUSTC_WRAPPER" in os.environ
                    or "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER" in os.environ
                ):
                    print("unsanitized Cargo rustflags/rpath/panic/wrapper in env", file=sys.stderr)
                    sys.exit(12)
                tdir = Path(args[args.index("--target-dir") + 1])
                host_deps = tdir / "debug" / "deps"
                triple_debug = tdir / {triple!r} / "debug"
                triple_deps = triple_debug / "deps"
                host_deps.mkdir(parents=True, exist_ok=True)
                triple_deps.mkdir(parents=True, exist_ok=True)
                pm_so = host_deps / "libserde_derive-deadbeef.so"
                pm_so.write_bytes(b"proc-macro")
                print(json.dumps({{
                    "reason": "compiler-artifact",
                    "target": {{"name": "serde_derive", "kind": ["proc-macro"]}},
                    "profile": {{"test": False}},
                    "filenames": [str(pm_so)],
                }}))
                for dep in {check_guard_mutation.EXTRACT_DIRECT_DEPS!r}:
                    rlib = triple_deps / f"lib{{dep}}-deadbeef.rlib"
                    rlib.write_bytes(b"rlib")
                    print(json.dumps({{
                        "reason": "compiler-artifact",
                        "target": {{"name": dep, "kind": ["lib"]}},
                        "profile": {{"test": False}},
                        "filenames": [str(rlib)],
                    }}))
                if args[0] == "test":
                    unit_exe = triple_deps / "anneal_rustc_capture-unit"
                    unit_exe.write_text(
                        "#!{sys.executable}\\n"
                        "import sys\\n"
                        "tname = sys.argv[2]\\n"
                        "print(f'test {{tname}} ... ok')\\n"
                        "print('test result: ok. 1 passed; 0 failed')\\n",
                        encoding="utf-8",
                    )
                    unit_exe.chmod(0o755)
                    print(json.dumps({{
                        "reason": "compiler-artifact",
                        "target": {{"name": "anneal_rustc_capture", "kind": ["lib"]}},
                        "profile": {{"test": True}},
                        "executable": str(unit_exe),
                        "filenames": [str(unit_exe)],
                    }}))
                else:
                    cap_exe = triple_debug / "anneal-rustc-capture"
                    cap_exe.write_text(
                        "#!{sys.executable}\\n"
                        "import json, sys\\n"
                        "src = sys.argv[sys.argv.index('--crate-root') + 1]\\n"
                        "if 'sanity_' in src:\\n"
                        "    print(json.dumps({{'status': 'captured'}}))\\n"
                        "    sys.exit(0)\\n"
                        "print(json.dumps({{'status': 'unsupported', "
                        "'diagnostics': ['function alignment'], "
                        "'unsupported': []}}))\\n"
                        "sys.exit(1)\\n",
                        encoding="utf-8",
                    )
                    cap_exe.chmod(0o755)
                    print(json.dumps({{
                        "reason": "compiler-artifact",
                        "target": {{"name": "anneal-rustc-capture", "kind": ["bin"]}},
                        "profile": {{"test": False}},
                        "executable": str(cap_exe),
                        "filenames": [str(cap_exe)],
                    }}))
                sys.exit(0)
                """
            )
            _write_fake_lean(tc_bin / "rustc", rustc_body)
            _write_fake_lean(tc_bin / "cargo", cargo_body)

            for cbt_val, filt in (
                ("aarch64-unknown-linux-gnu", "extract_reject_fn_alignment"),
                (triple, "extract_rodata_reject_provenance"),
            ):
                env = _isolated_extract_env(root)
                env["CARGO_BUILD_TARGET"] = cbt_val
                env["RUSTFLAGS"] = "-C panic=abort"
                env["CARGO_ENCODED_RUSTFLAGS"] = "-C\x1fpanic=abort"
                env["CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS"] = "-O"
                env["CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER"] = (
                    "/nonexistent/ld"
                )
                env["CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER"] = (
                    "/nonexistent/ld"
                )
                env["CARGO_PROFILE_DEV_PANIC"] = "abort"
                env["CARGO_PROFILE_TEST_PANIC"] = "abort"
                env["RUSTC_WRAPPER"] = "./relative-wrapper"
                env["RUSTC_WORKSPACE_WRAPPER"] = "./ws-wrapper"
                env["CARGO_BUILD_RUSTC_WRAPPER"] = "./cfg-wrapper"
                env["CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"] = "./cfg-ws-wrapper"
                json_out = root / f"{filt}.json"
                res = subprocess.run(
                    [
                        sys.executable,
                        "-I",
                        "-B",
                        str(SCRIPT),
                        "--anneal-root",
                        str(iso_anneal),
                        "--rustc",
                        str(tc_bin / "rustc"),
                        "--suite",
                        "extract_guards",
                        "--filter",
                        filt,
                        "--jobs",
                        "1",
                        "--json-out",
                        str(json_out),
                    ],
                    env=env,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                rep = json.loads(json_out.read_text(encoding="utf-8"))
                self.assertEqual(rep["killed"], 1)
                self.assertEqual(rep["errors"], 0)

    def test_precedence_fallback_rejects_unrelated_compiler_failed_or_unsupported(
        self,
    ):
        # For `extract_eval_required_consts` (baseline `"compiler_failed"` with
        # `"E0080"` and fallback `"unsupported type:"`), only the expected
        # downstream `unsupported` fallback counts as `KILLED`;
        # `compiler_failed` with `E0080` is `SURVIVED`, while `compiler_failed`
        # without `E0080` or an unrelated `unsupported` diagnostic is `ERROR`.
        guard = next(
            g
            for g in check_guard_mutation.EXTRACT_GUARDS
            if g.guard_id == "extract_eval_required_consts"
        )
        pinned_commit = check_guard_mutation._read_pinned_compiler_commit(
            ANNEAL_ROOT
        )
        triple = "x86_64-unknown-linux-gnu"
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-prec-fb-") as tmp:
            root = Path(tmp)
            sysroot = root / "sysroot"
            _populate_fake_rustc_dev_sysroot(sysroot, triple)
            deps_dir = root / "deps"
            deps_dir.mkdir()
            extern_rlibs = {}
            for dep in check_guard_mutation.EXTRACT_DIRECT_DEPS:
                p = deps_dir / f"lib{dep}-mock.rlib"
                p.write_bytes(b"rlib")
                extern_rlibs[dep] = p

            cases = (
                (
                    "survive_e0080",
                    1,
                    {
                        "status": "compiler_failed",
                        "diagnostics": ["error[E0080]: evaluation panicked"],
                        "unsupported": [],
                    },
                    "error[E0080]: evaluation panicked",
                    "SURVIVED",
                ),
                (
                    "error_other_compiler_failed",
                    1,
                    {
                        "status": "compiler_failed",
                        "diagnostics": ["error[E0425]: unresolved name"],
                        "unsupported": [],
                    },
                    "error[E0425]: unresolved name",
                    "ERROR",
                ),
                (
                    "error_unrelated_unsupported",
                    1,
                    {
                        "status": "unsupported",
                        "diagnostics": ["unrelated unsupported item"],
                        "unsupported": [],
                    },
                    "",
                    "ERROR",
                ),
                (
                    "error_survive_zero_rc",
                    0,
                    {
                        "status": "compiler_failed",
                        "diagnostics": ["error[E0080]: evaluation panicked"],
                        "unsupported": [],
                    },
                    "error[E0080]: evaluation panicked",
                    "ERROR",
                ),
                (
                    "error_fallback_zero_rc",
                    0,
                    {
                        "status": "unsupported",
                        "diagnostics": [],
                        "unsupported": [
                            {"reason": "unsupported type: &'{erased} ()"}
                        ],
                    },
                    "",
                    "ERROR",
                ),
                (
                    "kill_expected_fallback",
                    1,
                    {
                        "status": "unsupported",
                        "diagnostics": [],
                        "unsupported": [
                            {"reason": "unsupported type: &'{erased} ()"}
                        ],
                    },
                    "",
                    "KILLED",
                ),
            )
            for label, neg_rc, neg_payload, neg_stderr, expected in cases:
                fake_rustc = root / f"rustc_{label}"
                case_file = root / f"case_{label}.json"
                case_file.write_text(
                    json.dumps(
                        {
                            "rc": neg_rc,
                            "payload": neg_payload,
                            "stderr": neg_stderr,
                        }
                    ),
                    encoding="utf-8",
                )
                inner_script = textwrap.dedent(
                    f"""\
                    #!{sys.executable}
                    import json, pathlib, sys
                    src = sys.argv[sys.argv.index("--crate-root") + 1]
                    if "sanity_" in src:
                        print(json.dumps({{"status": "captured"}}))
                        sys.exit(0)
                    cfg = json.loads(pathlib.Path({str(case_file)!r}).read_text(encoding="utf-8"))
                    if cfg["stderr"]:
                        print(cfg["stderr"], file=sys.stderr)
                    print(json.dumps(cfg["payload"]))
                    sys.exit(cfg["rc"])
                    """
                )
                inner_file = root / f"inner_{label}.py"
                inner_file.write_text(inner_script, encoding="utf-8")
                _write_fake_lean(
                    fake_rustc,
                    textwrap.dedent(
                        f"""\
                        args = sys.argv[1:]
                        if args == ["--version", "--verbose"]:
                            print("rustc 1.98.0-nightly (fake)")
                            print("commit-hash: {pinned_commit}")
                            print("host: {triple}")
                            sys.exit(0)
                        if args == ["--print", "sysroot"]:
                            print({str(sysroot)!r})
                            sys.exit(0)
                        if args == ["--print", "cfg"]:
                            print('target_arch="x86_64"')
                            print('target_os="linux"')
                            print('target_pointer_width="64"')
                            print('target_endian="little"')
                            sys.exit(0)
                        if "-o" in args:
                            out_path = Path(args[args.index("-o") + 1])
                            if out_path.name.endswith(".rlib"):
                                out_path.write_bytes(b"rlib")
                                sys.exit(0)
                            out_path.write_bytes(Path({str(inner_file)!r}).read_bytes())
                            out_path.chmod(0o755)
                            sys.exit(0)
                        sys.exit(2)
                        """
                    ),
                )
                res = check_guard_mutation._check_one_extract_guard(
                    guard,
                    anneal_root=ANNEAL_ROOT,
                    rustc_bin=fake_rustc,
                    sysroot=str(sysroot),
                    host_triple=triple,
                    deps_dirs=(deps_dir,),
                    extern_rlibs=extern_rlibs,
                    timeout_sec=30,
                )
                self.assertEqual(res.status, expected, f"{label}: {res}")

    def test_rustup_directory_override_resolves_concrete_sysroot_toolchain(
        self,
    ):
        # Simulate a `rustup` proxy in `PATH`/`RUSTC`/`CARGO` that reports the
        # pinned nightly only when invoked inside `caller_cwd` (via a directory
        # override) and selects a global stable toolchain when invoked from
        # temporary directories. `_resolve_extract_toolchain` must switch both
        # `rustc` and `cargo` to `<sysroot>/bin/{rustc,cargo}`.
        pinned_commit = check_guard_mutation._read_pinned_compiler_commit(
            ANNEAL_ROOT
        )
        triple = "x86_64-unknown-linux-gnu"
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-rustup-") as tmp:
            root = Path(tmp)
            iso_anneal = _create_isolated_extract_anneal_root(
                root / "anneal_iso"
            )
            caller_cwd = root / "project_override_dir"
            proxy_bin = root / "cargo_home_bin"
            sysroot = root / "toolchains" / f"nightly-{triple}"
            sysroot_bin = sysroot / "bin"
            caller_cwd.mkdir(parents=True)
            proxy_bin.mkdir(parents=True)
            sysroot_bin.mkdir(parents=True)
            _populate_fake_rustc_dev_sysroot(sysroot, triple)

            # Concrete sysroot binaries work regardless of `cwd`.
            _write_fake_lean(
                sysroot_bin / "rustc",
                textwrap.dedent(
                    f"""\
                    args = sys.argv[1:]
                    if args == ["--version", "--verbose"]:
                        print("rustc 1.98.0-nightly (concrete)")
                        print("commit-hash: {pinned_commit}")
                        print("host: {triple}")
                        sys.exit(0)
                    if args == ["--print", "sysroot"]:
                        print({str(sysroot)!r})
                        sys.exit(0)
                    if args == ["--print", "cfg"]:
                        print('target_arch="x86_64"')
                        print('target_os="linux"')
                        print('target_pointer_width="64"')
                        print('target_endian="little"')
                        sys.exit(0)
                    if "-o" in args:
                        out_path = Path(args[args.index("-o") + 1])
                        if out_path.name.endswith(".rlib"):
                            out_path.write_bytes(b"rlib")
                            sys.exit(0)
                        out_path.write_text(
                            "#!{sys.executable}\\n"
                            "import json, sys\\n"
                            "print(json.dumps({{'status': 'captured'}}))\\n"
                            "sys.exit(0)\\n",
                            encoding="utf-8",
                        )
                        out_path.chmod(0o755)
                        sys.exit(0)
                    sys.exit(2)
                    """
                ),
            )
            _write_fake_lean(
                sysroot_bin / "cargo",
                textwrap.dedent(
                    f"""\
                    args = sys.argv[1:]
                    if args == ["--version"]:
                        print("cargo 1.98.0-nightly (concrete)")
                        sys.exit(0)
                    if Path(os.environ["RUSTC"]).resolve() != Path({str(sysroot_bin / 'rustc')!r}).resolve():
                        print(f"expected concrete sysroot RUSTC, got {{os.environ['RUSTC']}}", file=sys.stderr)
                        sys.exit(11)
                    tdir = Path(args[args.index("--target-dir") + 1])
                    deps = tdir / {triple!r} / "debug" / "deps"
                    deps.mkdir(parents=True, exist_ok=True)
                    for dep in {check_guard_mutation.EXTRACT_DIRECT_DEPS!r}:
                        rlib = deps / f"lib{{dep}}-deadbeef.rlib"
                        rlib.write_bytes(b"rlib")
                        print(json.dumps({{
                            "reason": "compiler-artifact",
                            "target": {{"name": dep, "kind": ["lib"]}},
                            "profile": {{"test": False}},
                            "filenames": [str(rlib)],
                        }}))
                    cap_exe = tdir / {triple!r} / "debug" / "anneal-rustc-capture"
                    cap_exe.write_text(
                        "#!{sys.executable}\\n"
                        "import json, sys\\n"
                        "src = sys.argv[sys.argv.index('--crate-root') + 1]\\n"
                        "if 'sanity_' in src:\\n"
                        "    print(json.dumps({{'status': 'captured'}}))\\n"
                        "    sys.exit(0)\\n"
                        "print(json.dumps({{'status': 'unsupported', "
                        "'diagnostics': ['function alignment'], "
                        "'unsupported': []}}))\\n"
                        "sys.exit(1)\\n",
                        encoding="utf-8",
                    )
                    cap_exe.chmod(0o755)
                    print(json.dumps({{
                        "reason": "compiler-artifact",
                        "target": {{"name": "anneal-rustc-capture", "kind": ["bin"]}},
                        "profile": {{"test": False}},
                        "executable": str(cap_exe),
                        "filenames": [str(cap_exe)],
                    }}))
                    sys.exit(0)
                    """
                ),
            )

            # Proxy shims simulate a `rustup` directory override on
            # `caller_cwd`.
            _write_fake_lean(
                proxy_bin / "rustc",
                textwrap.dedent(
                    f"""\
                    cwd = Path.cwd().resolve()
                    override_root = Path({str(caller_cwd)!r}).resolve()
                    in_override = cwd == override_root or override_root in cwd.parents
                    args = sys.argv[1:]
                    if not in_override:
                        if args == ["--version", "--verbose"]:
                            print("rustc 1.85.0 (stable)")
                            print("commit-hash: 1111111111111111111111111111111111111111")
                            print("host: {triple}")
                            sys.exit(0)
                        if args == ["--print", "sysroot"]:
                            print("/nonexistent/stable/sysroot")
                            sys.exit(0)
                        print("proxy rustc invoked outside override dir!", file=sys.stderr)
                        sys.exit(99)
                    os.execv({str(sysroot_bin / 'rustc')!r}, [{str(sysroot_bin / 'rustc')!r}, *args])
                    """
                ),
            )
            _write_fake_lean(
                proxy_bin / "cargo",
                textwrap.dedent(
                    f"""\
                    cwd = Path.cwd().resolve()
                    override_root = Path({str(caller_cwd)!r}).resolve()
                    in_override = cwd == override_root or override_root in cwd.parents
                    args = sys.argv[1:]
                    if not in_override:
                        if args == ["--version"]:
                            print("cargo 1.85.0 (stable)")
                            sys.exit(0)
                        print("proxy cargo invoked outside override dir!", file=sys.stderr)
                        sys.exit(98)
                    os.execv({str(sysroot_bin / 'cargo')!r}, [{str(sysroot_bin / 'cargo')!r}, *args])
                    """
                ),
            )

            env = _isolated_extract_env(root)
            env["PATH"] = f"{proxy_bin}{os.pathsep}{env.get('PATH', '')}"
            env["RUSTC"] = "rustc"
            env["CARGO"] = "cargo"
            json_out = root / "rustup_report.json"
            res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(iso_anneal),
                    "--suite",
                    "extract_guards",
                    "--filter",
                    "extract_reject_fn_alignment",
                    "--jobs",
                    "1",
                    "--json-out",
                    str(json_out),
                ],
                cwd=caller_cwd,
                env=env,
                capture_output=True,
                text=True,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            rep = json.loads(json_out.read_text(encoding="utf-8"))
            self.assertEqual(rep["killed"], 1)
            self.assertEqual(rep["errors"], 0)

    def test_lean_only_sandbox_without_rustc_capture_sources(self):
        import re
        import shutil

        # Simulate `ci-core`'s `anneal-guard-mutation` `nested_bwrap` input
        # sandbox, which mounts `ci/fixtures/guard_mutation/**`,
        # `trusted/lean/**`, and `trusted/audit/TrustedBoundary.lean` WITHOUT
        # `trusted/rustc-capture/src/**` while `run_anneal_check.sh` sets
        # `RUSTC=/opt/anneal-nix/build-rustc`.
        run_sh = (ANNEAL_ROOT / "ci/run_anneal_check.sh").read_text(
            encoding="utf-8"
        )
        m = re.search(
            r"(?ms)^\s*guard-mutation\)\n(.*?)\n\s*;;$", run_sh
        )
        self.assertIsNotNone(m)
        assert m is not None
        self.assertIn("--lean-only", m.group(1))

        ops_span = check_guard_mutation.find_theorem_line_span(
            (
                ANNEAL_ROOT / "ci/fixtures/guard_mutation/OpsRefutations.lean"
            ).read_text(encoding="utf-8"),
            "refute_ops_div_rem_by_zero",
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-sandbox-") as tmp:
            sandbox = Path(tmp) / "anneal"
            shutil.copytree(
                ANNEAL_ROOT / "ci/fixtures/guard_mutation",
                sandbox / "ci/fixtures/guard_mutation",
            )
            shutil.copytree(
                ANNEAL_ROOT / "trusted/lean",
                sandbox / "trusted/lean",
            )
            (sandbox / "trusted/audit").mkdir(parents=True)
            for audit_name in ("TrustedBoundary.lean", "SpecPreflight.lean"):
                shutil.copy2(
                    ANNEAL_ROOT / "trusted/audit" / audit_name,
                    sandbox / "trusted/audit" / audit_name,
                )

            # Default 4-suite validation still requires `trusted/rustc-capture`.
            full_errs = check_guard_mutation.validate_catalog_invariants(
                sandbox
            )
            self.assertTrue(
                any("trusted/rustc-capture" in e for e in full_errs),
                full_errs,
            )
            # `--lean-only` validates all Lean suites + metadata cleanly.
            self.assertEqual(
                check_guard_mutation.validate_catalog_invariants(
                    sandbox, lean_only=True
                ),
                [],
            )

            fake_lean = Path(tmp) / "fake_lean"
            _write_fake_lean(
                fake_lean,
                textwrap.dedent(
                    f"""\
                    args = sys.argv[1:]
                    lean_path = os.environ.get("LEAN_PATH", "")
                    is_mutant = "anneal-gmut-" in lean_path and "anneal-gmut-base-" not in lean_path
                    if "-o" in args:
                        Path(args[args.index("-o") + 1]).write_bytes(b"fake-olean")
                        if is_mutant and args[-1].endswith("OpsRefutations.lean"):
                            print(f"{{args[-1]}}:{ops_span[0]}:2: error: Type mismatch (rfl)")
                            sys.exit(1)
                        sys.exit(0)
                    sys.exit(0)
                    """
                ),
            )
            json_out = Path(tmp) / "lean_only.json"
            env = dict(os.environ)
            env["RUSTC"] = "/opt/anneal-nix/nonexistent-build-rustc"
            res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(sandbox),
                    "--lean-only",
                    "--lean",
                    str(fake_lean),
                    "--filter",
                    "ops_div_rem_by_zero",
                    "--jobs",
                    "1",
                    "--json-out",
                    str(json_out),
                ],
                env=env,
                capture_output=True,
                text=True,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            rep = json.loads(json_out.read_text(encoding="utf-8"))
            self.assertEqual(rep["killed"], 1)
            self.assertEqual(rep["errors"], 0)

            # `--lean-only --suite extract_guards` and `--lean-only` with an
            # extract-only `--filter` must fail closed in both run and `--list`
            # modes instead of exiting `0` on an empty guard set.
            for extra_args, expected_err in (
                (
                    ["--suite", "extract_guards"],
                    "--lean-only cannot be combined",
                ),
                (
                    ["--list", "--suite", "extract_guards"],
                    "--lean-only cannot be combined",
                ),
                (
                    [
                        "--lean",
                        str(fake_lean),
                        "--filter",
                        "extract_reject_fn_alignment",
                    ],
                    "no Lean guards matched",
                ),
                (
                    ["--list", "--filter", "extract_reject_fn_alignment"],
                    "no guards matched",
                ),
            ):
                res_bad = subprocess.run(
                    [
                        sys.executable,
                        "-I",
                        "-B",
                        str(SCRIPT),
                        "--anneal-root",
                        str(sandbox),
                        "--lean-only",
                        *extra_args,
                    ],
                    env=env,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(res_bad.returncode, 1, extra_args)
                self.assertIn(expected_err, res_bad.stderr, extra_args)

            # Baseline Cargo `TimeoutExpired` converts to a controlled `FAIL:`
            # error (`RuntimeError`) without emitting an uncaught traceback.
            iso_anneal = _create_isolated_extract_anneal_root(
                sandbox.parent / "anneal_timeout_iso"
            )
            with (
                mock.patch.dict(
                    os.environ,
                    _isolated_extract_env(sandbox.parent),
                    clear=True,
                ),
                mock.patch.object(
                    check_guard_mutation,
                    "_resolve_extract_toolchain",
                    return_value=(
                        Path("/fake/rustc"),
                        Path("/fake/cargo"),
                        "/fake/sysroot",
                        "x86_64-unknown-linux-gnu",
                    ),
                ),
                mock.patch.object(
                    check_guard_mutation.subprocess,
                    "run",
                    side_effect=subprocess.TimeoutExpired(
                        cmd=["/fake/cargo"], timeout=180
                    ),
                ),
                io.StringIO() as stderr_buf,
                mock.patch.object(sys, "stderr", stderr_buf),
            ):
                rc_to = check_guard_mutation.main(
                    [
                        "--anneal-root",
                        str(iso_anneal),
                        "--suite",
                        "extract_guards",
                        "--filter",
                        "extract_reject_fn_alignment",
                    ]
                )
                err_to = stderr_buf.getvalue()
            self.assertEqual(rc_to, 1, err_to)
            self.assertIn("FAIL: baseline anneal-rustc-capture", err_to)
            self.assertIn("timed out", err_to)
            self.assertNotIn("Traceback", err_to)

    def test_base_sysroot_without_rustc_dev_and_invalid_rustc_env_handling(
        self,
    ):
        # Base `rustc` ships `<sysroot>/lib/librustc_driver-*.so` without the
        # `rustc-dev` (`rustc_private`) artifacts under
        # `<sysroot>/lib/rustlib/<triple>/lib/`. Verify `--suite all` cleanly
        # auto-skips `extract_guards` while `--suite extract_guards` fails
        # closed, and that setting `RUSTC` to a nonexistent or broken binary
        # fails closed even under `--suite all`.
        pinned_commit = check_guard_mutation._read_pinned_compiler_commit(
            ANNEAL_ROOT
        )
        triple = "x86_64-unknown-linux-gnu"
        ops_span = check_guard_mutation.find_theorem_line_span(
            (
                ANNEAL_ROOT / "ci/fixtures/guard_mutation/OpsRefutations.lean"
            ).read_text(encoding="utf-8"),
            "refute_ops_div_rem_by_zero",
        )
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-nodev-") as tmp:
            root = Path(tmp)
            iso_anneal_suite = _create_isolated_extract_anneal_root(
                root / "iso_suite_anneal"
            )
            sysroot = root / "base_sysroot"
            (sysroot / "lib").mkdir(parents=True)
            (sysroot / "lib" / "librustc_driver-abc.so").write_bytes(b"so")
            target_lib = sysroot / "lib" / "rustlib" / triple / "lib"
            target_lib.mkdir(parents=True)
            (target_lib / "libstd-abc.rlib").write_bytes(b"rlib")

            tc_bin = root / "bin"
            tc_bin.mkdir()
            base_rustc = tc_bin / "rustc"
            fake_cargo = tc_bin / "cargo"
            _write_fake_probe_rustc(
                base_rustc,
                commit_hash=pinned_commit,
                triple=triple,
                sysroot=sysroot,
                label="base-without-rustc-dev",
            )
            _write_fake_lean(
                fake_cargo,
                "if sys.argv[1:] == ['--version']: print('cargo 1.98.0'); sys.exit(0)\nsys.exit(1)\n",
            )
            with mock.patch.dict(
                os.environ, _isolated_extract_env(root), clear=True
            ):
                self.assertIsNone(
                    check_guard_mutation._probe_rustc_candidate(
                        base_rustc, pinned_commit, 10
                    )
                )

            # A pinned `rustc` with complete `rustc-dev` artifacts on a
            # non-`x86_64-unknown-linux-gnu` host — including 64-bit
            # little-endian non-`x86_64` or musl Linux profiles (`aarch64`,
            # `musl`, `riscv64gc`, `powerpc64le`), macOS, Windows, Android,
            # 32-bit, or big-endian — must be treated as unavailable because
            # `anneal-rustc-capture` only supports `x86_64-unknown-linux-gnu`;
            # `--suite all` must auto-skip rather than crashing in sanity.
            unsupported_profiles = (
                ("aarch64-unknown-linux-gnu", "aarch64", "linux", "64", "little", 0),
                ("x86_64-unknown-linux-musl", "x86_64", "linux", "64", "little", 0),
                ("riscv64gc-unknown-linux-gnu", "riscv64", "linux", "64", "little", 0),
                ("powerpc64le-unknown-linux-gnu", "powerpc64", "linux", "64", "little", 0),
                ("aarch64-apple-darwin", "aarch64", "macos", "64", "little", 0),
                ("x86_64-pc-windows-msvc", "x86_64", "windows", "64", "little", 0),
                ("aarch64-linux-android", "aarch64", "android", "64", "little", 0),
                ("i686-unknown-linux-gnu", "x86", "linux", "32", "little", 0),
                ("x86_64-unknown-linux-gnux32", "x86_64", "linux", "32", "little", 0),
                ("s390x-unknown-linux-gnu", "s390x", "linux", "64", "big", 0),
                ("cfg-wrong-arch-linux", "aarch64", "linux", "64", "little", 0),
                ("cfg-fail-linux", "x86_64", "linux", "64", "little", 1),
            )
            for (
                prof_name,
                prof_arch,
                prof_os,
                prof_width,
                prof_endian,
                prof_cfg_rc,
            ) in unsupported_profiles:
                prof_triple = (
                    "x86_64-unknown-linux-gnu"
                    if prof_name in ("cfg-fail-linux", "cfg-wrong-arch-linux")
                    else prof_name
                )
                prof_sysroot = root / f"sysroot_{prof_name}"
                _populate_fake_rustc_dev_sysroot(prof_sysroot, prof_triple)
                prof_rustc = root / f"rustc_{prof_name}"
                _write_fake_probe_rustc(
                    prof_rustc,
                    commit_hash=pinned_commit,
                    triple=prof_triple,
                    sysroot=prof_sysroot,
                    label=f"unsupported-{prof_name}",
                    target_arch=prof_arch,
                    target_os=prof_os,
                    pointer_width=prof_width,
                    endian=prof_endian,
                    cfg_exit_code=prof_cfg_rc,
                )
                with mock.patch.dict(
                    os.environ, _isolated_extract_env(root), clear=True
                ):
                    self.assertIsNone(
                        check_guard_mutation._probe_rustc_candidate(
                            prof_rustc, pinned_commit, 10
                        ),
                        prof_name,
                    )

            # Even when an override shim reports `x86_64-unknown-linux-gnu` in
            # `caller_cwd`, fallback to an unsupported `<sysroot>/bin/rustc`
            # inside `probe_cwd` must be rejected by `--print cfg` even when
            # `<sysroot>/bin/cargo` is present, whereas a matching `x86_64`
            # 64-bit little-endian Linux `<sysroot>/bin/rustc` succeeds.
            for sr_endian, expect_resolved in (("big", False), ("little", True)):
                sr_override = root / f"sr_override_{sr_endian}"
                sr_override.mkdir()
                sr_target = root / f"sr_target_{sr_endian}"
                _populate_fake_rustc_dev_sysroot(sr_target, triple)
                (sr_target / "bin").mkdir(parents=True)
                _write_fake_probe_rustc(
                    sr_target / "bin" / "rustc",
                    commit_hash=pinned_commit,
                    triple=triple,
                    sysroot=sr_target,
                    label=f"sysroot-{sr_endian}-endian",
                    target_os="linux",
                    pointer_width="64",
                    endian=sr_endian,
                )
                _write_fake_lean(
                    sr_target / "bin" / "cargo",
                    "if sys.argv[1:] == ['--version']: print('cargo 1.98.0'); sys.exit(0)\nsys.exit(1)\n",
                )
                sr_shim = root / f"sr_shim_{sr_endian}"
                _write_fake_lean(
                    sr_shim,
                    textwrap.dedent(
                        f"""\
                        cwd = Path.cwd().resolve()
                        override_root = Path({str(sr_override)!r}).resolve()
                        args = sys.argv[1:]
                        if cwd == override_root:
                            if args == ["--version", "--verbose"]:
                                print("rustc 1.98.0-nightly (override)")
                                print("commit-hash: {pinned_commit}")
                                print("host: {triple}")
                                sys.exit(0)
                            if args == ["--print", "sysroot"]:
                                print({str(sr_target)!r})
                                sys.exit(0)
                            if args == ["--print", "cfg"]:
                                print('target_arch="x86_64"')
                                print('target_os="linux"')
                                print('target_pointer_width="64"')
                                print('target_endian="little"')
                                sys.exit(0)
                        elif args == ["--version", "--verbose"]:
                            print("rustc 1.85.0 (stable)")
                            print("commit-hash: 1111111111111111111111111111111111111111")
                            print("host: {triple}")
                            sys.exit(0)
                        sys.exit(1)
                        """
                    ),
                )
                env_sr = _isolated_extract_env(
                    root,
                    {
                        k: v
                        for k, v in os.environ.items()
                        if k not in ("RUSTC", "CARGO")
                    },
                )
                env_sr["PATH"] = str(sr_target / "bin")
                prev_cwd = Path.cwd()
                try:
                    os.chdir(sr_override)
                    with mock.patch.dict(os.environ, env_sr, clear=True):
                        probed = check_guard_mutation._probe_rustc_candidate(
                            sr_shim, pinned_commit, 10
                        )
                    if expect_resolved:
                        self.assertEqual(
                            probed,
                            (
                                sr_target / "bin" / "rustc",
                                sr_target / "bin" / "cargo",
                                str(sr_target),
                                triple,
                            ),
                        )
                    else:
                        self.assertIsNone(probed)
                finally:
                    os.chdir(prev_cwd)

            # A non-rustup wrapper printing a relative `--print sysroot`
            # resolves against each probe's `cwd`: without `<sysroot>/bin/rustc`
            # fallback it must fail instead of slipping past `probe_cwd`, and
            # with a clean `<sysroot>/bin/rustc` it resolves to that sysroot
            # compiler (`None` if `<sysroot>/bin/rustc` also emits relative).
            for with_sr_bin, sr_bin_rel, expect_ok in (
                (False, False, False),
                (True, True, False),
                (True, False, True),
            ):
                rel_caller = root / f"rel_caller_{with_sr_bin}_{sr_bin_rel}"
                rel_caller.mkdir()
                rel_sr = rel_caller / "rel_sysroot"
                _populate_fake_rustc_dev_sysroot(rel_sr, triple)
                (rel_sr / "bin").mkdir(parents=True)
                _write_fake_lean(
                    rel_sr / "bin" / "cargo",
                    "if sys.argv[1:] == ['--version']: print('cargo 1.98.0'); sys.exit(0)\nsys.exit(1)\n",
                )
                if with_sr_bin:
                    sr_print = "'./rel_sysroot'" if sr_bin_rel else repr(str(rel_sr))
                    _write_fake_lean(
                        rel_sr / "bin" / "rustc",
                        textwrap.dedent(
                            f"""\
                            args = sys.argv[1:]
                            if args == ["--version", "--verbose"]:
                                print("rustc 1.98.0-nightly")
                                print("commit-hash: {pinned_commit}")
                                print("host: {triple}")
                                sys.exit(0)
                            if args == ["--print", "sysroot"]:
                                print({sr_print})
                                sys.exit(0)
                            if args == ["--print", "cfg"]:
                                print('target_arch="x86_64"')
                                print('target_os="linux"')
                                print('target_pointer_width="64"')
                                print('target_endian="little"')
                                sys.exit(0)
                            sys.exit(1)
                            """
                        ),
                    )
                rel_shim = root / f"rel_shim_{with_sr_bin}_{sr_bin_rel}"
                _write_fake_lean(
                    rel_shim,
                    textwrap.dedent(
                        f"""\
                        args = sys.argv[1:]
                        if args == ["--version", "--verbose"]:
                            print("rustc 1.98.0-nightly (rel-shim)")
                            print("commit-hash: {pinned_commit}")
                            print("host: {triple}")
                            sys.exit(0)
                        if args == ["--print", "sysroot"]:
                            print("./rel_sysroot")
                            sys.exit(0)
                        if args == ["--print", "cfg"]:
                            print('target_arch="x86_64"')
                            print('target_os="linux"')
                            print('target_pointer_width="64"')
                            print('target_endian="little"')
                            sys.exit(0)
                        sys.exit(1)
                        """
                    ),
                )
                env_rel = _isolated_extract_env(
                    root,
                    {
                        k: v
                        for k, v in os.environ.items()
                        if k not in ("RUSTC", "CARGO")
                    },
                )
                env_rel["PATH"] = str(rel_sr / "bin")
                prev_cwd = Path.cwd()
                try:
                    os.chdir(rel_caller)
                    with mock.patch.dict(os.environ, env_rel, clear=True):
                        probed = check_guard_mutation._probe_rustc_candidate(
                            rel_shim, pinned_commit, 10
                        )
                    if expect_ok:
                        self.assertEqual(
                            probed,
                            (
                                rel_sr / "bin" / "rustc",
                                rel_sr / "bin" / "cargo",
                                str(rel_sr),
                                triple,
                            ),
                        )
                    else:
                        self.assertIsNone(probed)
                finally:
                    os.chdir(prev_cwd)

            # A non-rustup wrapper reporting matching `(commit, host, sysroot)`
            # across `caller_cwd` and `probe_cwd` whose `--print cfg` changes
            # with `cwd` (supported x86_64 in `caller_cwd`, wrong target in
            # `probe_cwd`) must fall back to `<sysroot>/bin/rustc` and fail
            # closed if `<sysroot>/bin/rustc` is absent or also reports bad cfg.
            for with_sr_bin, sr_cfg_arch, expect_ok in (
                (False, "x86_64", False),
                (True, "aarch64", False),
                (True, "x86_64", True),
            ):
                cfg_caller = root / f"cfg_caller_{with_sr_bin}_{sr_cfg_arch}"
                cfg_caller.mkdir()
                cfg_sr = cfg_caller / "sysroot"
                _populate_fake_rustc_dev_sysroot(cfg_sr, triple)
                (cfg_sr / "bin").mkdir(parents=True)
                _write_fake_lean(
                    cfg_sr / "bin" / "cargo",
                    "if sys.argv[1:] == ['--version']: print('cargo 1.98.0'); sys.exit(0)\nsys.exit(1)\n",
                )
                if with_sr_bin:
                    _write_fake_probe_rustc(
                        cfg_sr / "bin" / "rustc",
                        commit_hash=pinned_commit,
                        triple=triple,
                        sysroot=cfg_sr,
                        label="sr-cfg-rustc",
                        target_arch=sr_cfg_arch,
                    )
                cfg_shim = root / f"cfg_shim_{with_sr_bin}_{sr_cfg_arch}"
                _write_fake_lean(
                    cfg_shim,
                    textwrap.dedent(
                        f"""\
                        args = sys.argv[1:]
                        if args == ["--version", "--verbose"]:
                            print("rustc 1.98.0-nightly (cfg-shim)")
                            print("commit-hash: {pinned_commit}")
                            print("host: {triple}")
                            sys.exit(0)
                        if args == ["--print", "sysroot"]:
                            print({str(cfg_sr)!r})
                            sys.exit(0)
                        if args == ["--print", "cfg"]:
                            in_caller = os.path.abspath(os.getcwd()) == {str(cfg_caller.resolve())!r}
                            arch = "x86_64" if in_caller else "aarch64"
                            print(f'target_arch="{{arch}}"')
                            print('target_os="linux"')
                            print('target_pointer_width="64"')
                            print('target_endian="little"')
                            sys.exit(0)
                        sys.exit(1)
                        """
                    ),
                )
                env_cfg = _isolated_extract_env(
                    root,
                    {
                        k: v
                        for k, v in os.environ.items()
                        if k not in ("RUSTC", "CARGO")
                    },
                )
                env_cfg["PATH"] = str(cfg_sr / "bin")
                prev_cwd = Path.cwd()
                try:
                    os.chdir(cfg_caller)
                    with mock.patch.dict(os.environ, env_cfg, clear=True):
                        probed = check_guard_mutation._probe_rustc_candidate(
                            cfg_shim, pinned_commit, 10
                        )
                    if expect_ok:
                        self.assertEqual(
                            probed,
                            (
                                cfg_sr / "bin" / "rustc",
                                cfg_sr / "bin" / "cargo",
                                str(cfg_sr),
                                triple,
                            ),
                        )
                    else:
                        self.assertIsNone(probed)
                finally:
                    os.chdir(prev_cwd)

            fake_lean = root / "fake_lean"
            _write_fake_lean(
                fake_lean,
                textwrap.dedent(
                    f"""\
                    args = sys.argv[1:]
                    lean_path = os.environ.get("LEAN_PATH", "")
                    is_mutant = "anneal-gmut-" in lean_path and "anneal-gmut-base-" not in lean_path
                    if "-o" in args:
                        Path(args[args.index("-o") + 1]).write_bytes(b"fake-olean")
                        if is_mutant and args[-1].endswith("OpsRefutations.lean"):
                            print(f"{{args[-1]}}:{ops_span[0]}:2: error: Type mismatch (rfl)")
                            sys.exit(1)
                        sys.exit(0)
                    sys.exit(0)
                    """
                ),
            )

            env_base = _isolated_extract_env(root)
            env_base.pop("RUSTC", None)
            env_base["CARGO"] = str(fake_cargo)
            env_base["PATH"] = str(tc_bin)
            one_mir = [
                g
                for g in check_guard_mutation.MIR_SEMANTICS_GUARDS
                if g.guard_id == "ops_div_rem_by_zero"
            ]
            one_ext = [
                g
                for g in check_guard_mutation.EXTRACT_GUARDS
                if g.guard_id == "extract_reject_fn_alignment"
            ]
            with (
                mock.patch.dict(os.environ, env_base, clear=True),
                mock.patch.object(
                    check_guard_mutation,
                    "_select_guards",
                    return_value=(one_mir, [], [], one_ext),
                ),
            ):
                rep_all = check_guard_mutation.run_guard_mutation_suite(
                    anneal_root=iso_anneal_suite,
                    lean_bin=fake_lean,
                    suite="all",
                    jobs=1,
                )
            self.assertEqual(rep_all["killed"], 1)
            self.assertEqual(rep_all["errors"], 0)
            self.assertEqual(rep_all["skipped_suites"], ["extract_guards"])

            for unsup_host in (
                "aarch64-unknown-linux-gnu",
                "x86_64-unknown-linux-musl",
                "aarch64-apple-darwin",
                "i686-unknown-linux-gnu",
                "s390x-unknown-linux-gnu",
            ):
                unsup_tc = root / f"tc_{unsup_host}"
                unsup_tc.mkdir()
                shutil.copy2(root / f"rustc_{unsup_host}", unsup_tc / "rustc")
                shutil.copy2(fake_cargo, unsup_tc / "cargo")
                env_unsup = _isolated_extract_env(root)
                env_unsup.pop("RUSTC", None)
                env_unsup["CARGO"] = str(unsup_tc / "cargo")
                env_unsup["PATH"] = str(unsup_tc)
                with (
                    mock.patch.dict(os.environ, env_unsup, clear=True),
                    mock.patch.object(
                        check_guard_mutation,
                        "_select_guards",
                        return_value=(one_mir, [], [], one_ext),
                    ),
                ):
                    rep_unsup = check_guard_mutation.run_guard_mutation_suite(
                        anneal_root=iso_anneal_suite,
                        lean_bin=fake_lean,
                        suite="all",
                        jobs=1,
                    )
                self.assertEqual(rep_unsup["killed"], 1, unsup_host)
                self.assertEqual(rep_unsup["errors"], 0, unsup_host)
                self.assertEqual(
                    rep_unsup["skipped_suites"], ["extract_guards"], unsup_host
                )

                res_unsup_ext = subprocess.run(
                    [
                        sys.executable,
                        "-I",
                        "-B",
                        str(SCRIPT),
                        "--anneal-root",
                        str(iso_anneal_suite),
                        "--suite",
                        "extract_guards",
                        "--filter",
                        "extract_reject_fn_alignment",
                    ],
                    env=env_unsup,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(res_unsup_ext.returncode, 1, unsup_host)
                self.assertIn(
                    "on an x86_64-unknown-linux-gnu host",
                    res_unsup_ext.stderr,
                    unsup_host,
                )

            res_ext = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(iso_anneal_suite),
                    "--suite",
                    "extract_guards",
                    "--filter",
                    "extract_reject_fn_alignment",
                ],
                env=env_base,
                capture_output=True,
                text=True,
            )
            self.assertEqual(res_ext.returncode, 1)
            self.assertIn("pinned nightly rustc with rustc-dev", res_ext.stderr)

            # Explicit `RUSTC` pointing to a nonexistent, broken, mismatched-
            # commit, unsupported-host, or `rustc-dev`-less compiler fails
            # closed even under `--suite all` rather than falling back to `PATH`
            # or auto-skipping.
            broken_rustc = root / "broken_rustc"
            _write_fake_lean(broken_rustc, "sys.exit(2)\n")
            wrong_commit_rustc = root / "wrong_commit_rustc"
            _write_fake_probe_rustc(
                wrong_commit_rustc,
                commit_hash="deadbeefdeadbeef",
                triple=triple,
                sysroot=sysroot,
                label="wrong-commit",
            )
            for bad_val, err_pat in (
                ("", "RUSTC is empty"),
                (str(root / "missing_rustc"), "does not point to a runnable rustc"),
                (str(broken_rustc), "does not point to a runnable rustc"),
                (str(base_rustc), "is not the pinned nightly rustc"),
                (str(wrong_commit_rustc), "is not the pinned nightly rustc"),
                (
                    str(root / "rustc_aarch64-unknown-linux-gnu"),
                    "on an x86_64-unknown-linux-gnu host",
                ),
                (
                    str(root / "rustc_x86_64-unknown-linux-musl"),
                    "on an x86_64-unknown-linux-gnu host",
                ),
                (
                    str(root / "rustc_i686-unknown-linux-gnu"),
                    "on an x86_64-unknown-linux-gnu host",
                ),
                (
                    str(root / "rustc_s390x-unknown-linux-gnu"),
                    "on an x86_64-unknown-linux-gnu host",
                ),
            ):
                env_bad = dict(env_base)
                env_bad["RUSTC"] = bad_val
                with (
                    mock.patch.dict(os.environ, env_bad, clear=True),
                    mock.patch.object(
                        check_guard_mutation,
                        "_select_guards",
                        return_value=(one_mir, [], [], one_ext),
                    ),
                    self.assertRaisesRegex(RuntimeError, err_pat),
                ):
                    check_guard_mutation.run_guard_mutation_suite(
                        anneal_root=iso_anneal_suite,
                        lean_bin=fake_lean,
                        suite="all",
                        jobs=1,
                    )

            # Explicit invalid/empty `CARGO` override must also fail closed
            # under `--suite all` even when a valid `rustc-dev` toolchain is
            # present on `PATH` without `RUSTC` or `--rustc`.
            dev_sysroot = root / "dev_sysroot"
            _populate_fake_rustc_dev_sysroot(dev_sysroot, triple)
            dev_bin = dev_sysroot / "bin"
            dev_bin.mkdir(parents=True)
            dev_rustc = dev_bin / "rustc"
            dev_cargo = dev_bin / "cargo"
            _write_fake_probe_rustc(
                dev_rustc,
                commit_hash=pinned_commit,
                triple=triple,
                sysroot=dev_sysroot,
                label="pinned-with-dev",
            )
            _write_fake_lean(
                dev_cargo,
                "if sys.argv[1:] == ['--version']: print('cargo 1.98.0'); sys.exit(0)\nsys.exit(1)\n",
            )
            non_exec_cargo = root / "non_exec_cargo"
            non_exec_cargo.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            non_exec_cargo.chmod(0o644)
            broken_cargo = root / "broken_cargo"
            _write_fake_lean(broken_cargo, "sys.exit(2)\n")

            for bad_cargo, err_pat in (
                ("", "CARGO is empty"),
                (str(root / "missing_cargo"), "does not point to a runnable cargo"),
                (str(non_exec_cargo), "does not point to a runnable cargo"),
                (str(broken_cargo), "does not point to a runnable cargo"),
            ):
                env_bad_cargo = dict(env_base)
                env_bad_cargo["PATH"] = str(dev_bin)
                env_bad_cargo["CARGO"] = bad_cargo
                with (
                    mock.patch.dict(os.environ, env_bad_cargo, clear=True),
                    mock.patch.object(
                        check_guard_mutation,
                        "_select_guards",
                        return_value=(one_mir, [], [], one_ext),
                    ),
                    self.assertRaisesRegex(RuntimeError, err_pat),
                ):
                    check_guard_mutation.run_guard_mutation_suite(
                        anneal_root=iso_anneal_suite,
                        lean_bin=fake_lean,
                        suite="all",
                        jobs=1,
                    )

            # Unrunnable `<sysroot>/bin/cargo` (non-executable or failing
            # `--version`) must not be auto-selected or raise PermissionError.
            bad_sr = root / "bad_cargo_sysroot"
            bad_sr_bin = bad_sr / "bin"
            bad_sr_bin.mkdir(parents=True)
            _populate_fake_rustc_dev_sysroot(bad_sr, triple)
            bad_sr_rustc = bad_sr_bin / "rustc"
            _write_fake_probe_rustc(
                bad_sr_rustc,
                commit_hash=pinned_commit,
                triple=triple,
                sysroot=bad_sr,
                label="bad-cargo-sysroot",
            )
            bad_sr_cargo = bad_sr_bin / "cargo"
            bad_sr_cargo.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            bad_sr_cargo.chmod(0o644)
            with (
                tempfile.TemporaryDirectory(prefix="anneal-gmut-probe-") as p,
                mock.patch.dict(
                    os.environ,
                    _isolated_extract_env(
                        root,
                        {k: v for k, v in env_base.items() if k != "CARGO"}
                        | {"PATH": "/nonexistent-bin"},
                    ),
                    clear=True,
                ),
            ):
                self.assertIsNone(
                    check_guard_mutation._resolve_cargo_for_rustc(
                        bad_sr_rustc, bad_sr, Path(p), 5
                    )
                )
            bad_sr_cargo.chmod(0o755)
            bad_sr_cargo.write_text("#!/bin/sh\nexit 2\n", encoding="utf-8")
            with (
                tempfile.TemporaryDirectory(prefix="anneal-gmut-probe-") as p,
                mock.patch.dict(
                    os.environ,
                    _isolated_extract_env(
                        root,
                        {k: v for k, v in env_base.items() if k != "CARGO"}
                        | {"PATH": "/nonexistent-bin"},
                    ),
                    clear=True,
                ),
            ):
                self.assertIsNone(
                    check_guard_mutation._resolve_cargo_for_rustc(
                        bad_sr_rustc, bad_sr, Path(p), 5
                    )
                )
                with mock.patch.dict(
                    os.environ,
                    {"PATH": str(dev_bin)},
                    clear=False,
                ):
                    self.assertEqual(
                        check_guard_mutation._resolve_cargo_for_rustc(
                            bad_sr_rustc, bad_sr, Path(p), 5
                        ),
                        Path(os.path.abspath(dev_cargo)),
                    )

            # When `<sysroot>/bin/cargo` is missing, explicit `CARGO` pointing
            # to a non-rustup wrapper that fails or changes `--version` outside
            # the caller's cwd must fail closed rather than slipping through,
            # while a cwd-stable explicit `CARGO` succeeds; ambient
            # cwd-sensitive `cargo` on `PATH` must likewise be skipped.
            cwd_sens_cargo = root / "cwd_sensitive_wrapper"
            cwd_sens_cargo.write_text(
                f"#!{sys.executable}\n"
                "import os, sys\n"
                "from pathlib import Path\n"
                "if Path.cwd() != Path("
                f"{str(root)!r}"
                "):\n"
                "    print('cargo 1.85.0 (wrong-cwd)')\n"
                "    sys.exit(0)\n"
                "print('cargo 1.98.0-nightly (caller-only)')\n",
                encoding="utf-8",
            )
            cwd_sens_cargo.chmod(0o755)
            stable_cargo = root / "stable_wrapper"
            _write_fake_lean(
                stable_cargo,
                "if sys.argv[1:] == ['--version']: print('cargo 1.98.0-nightly'); sys.exit(0)\nsys.exit(1)\n",
            )
            ambient_bin = root / "ambient_cwd_bin"
            ambient_bin.mkdir()
            ambient_cargo = ambient_bin / "cargo"
            ambient_cargo.write_bytes(cwd_sens_cargo.read_bytes())
            ambient_cargo.chmod(0o755)
            old_cwd = Path.cwd()
            try:
                os.chdir(root)
                with (
                    tempfile.TemporaryDirectory(prefix="anneal-gmut-probe-") as p,
                    mock.patch.dict(
                        os.environ,
                        _isolated_extract_env(
                            root,
                            {k: v for k, v in env_base.items() if k != "CARGO"}
                            | {"PATH": str(ambient_bin)},
                        ),
                        clear=True,
                    ),
                ):
                    self.assertIsNone(
                        check_guard_mutation._resolve_cargo_for_rustc(
                            bad_sr_rustc, bad_sr, Path(p), 5
                        )
                    )
                    with (
                        mock.patch.dict(
                            os.environ,
                            {"CARGO": str(cwd_sens_cargo)},
                            clear=False,
                        ),
                        self.assertRaisesRegex(
                            RuntimeError,
                            "usable across working directories",
                        ),
                    ):
                        check_guard_mutation._resolve_cargo_for_rustc(
                            bad_sr_rustc, bad_sr, Path(p), 5
                        )
                    with mock.patch.dict(
                        os.environ,
                        {"CARGO": str(stable_cargo)},
                        clear=False,
                    ):
                        self.assertEqual(
                            check_guard_mutation._resolve_cargo_for_rustc(
                                bad_sr_rustc, bad_sr, Path(p), 5
                            ),
                            stable_cargo,
                        )
            finally:
                os.chdir(old_cwd)

            # A non-rustup `CARGO` or `RUSTC` wrapper that agrees in both the
            # caller's directory and `probe_cwd`, yet switches toolchains inside
            # the real `anneal_root` build directory, must be rejected (when no
            # usable sysroot binary exists) or bypassed in favor of the concrete
            # sysroot binary when `_resolve_extract_toolchain` probes with
            # `build_cwd=anneal_root`.
            build_anneal = root / "build_anneal_root"
            build_anneal.mkdir()
            (build_anneal / "Cargo.toml").write_text("[workspace]\n", encoding="utf-8")
            b_sysroot = root / "build_cwd_sysroot"
            _populate_fake_rustc_dev_sysroot(b_sysroot, triple)
            (b_sysroot / "bin").mkdir(parents=True)
            b_sr_rustc = b_sysroot / "bin" / "rustc"
            _write_fake_probe_rustc(
                b_sr_rustc,
                commit_hash=pinned_commit,
                triple=triple,
                sysroot=b_sysroot,
                label="build-cwd-sr-rustc",
            )
            b_sr_cargo = b_sysroot / "bin" / "cargo"
            _write_fake_lean(
                b_sr_cargo,
                "if sys.argv[1:] == ['--version']: print('cargo 1.98.0-nightly'); sys.exit(0)\nsys.exit(1)\n",
            )
            build_sens_cargo = root / "build_cwd_cargo_wrapper"
            build_sens_cargo.write_text(
                f"#!{sys.executable}\n"
                "import sys\n"
                "from pathlib import Path\n"
                f"if Path.cwd().resolve() == Path({str(build_anneal)!r}).resolve():\n"
                "    print('cargo 1.85.0 (build-dir-override)')\n"
                "    sys.exit(0)\n"
                "print('cargo 1.98.0-nightly')\n",
                encoding="utf-8",
            )
            build_sens_cargo.chmod(0o755)
            build_sens_rustc = root / "build_cwd_rustc_wrapper"
            _write_fake_lean(
                build_sens_rustc,
                textwrap.dedent(
                    f"""\
                    args = sys.argv[1:]
                    in_build = Path.cwd().resolve() == Path({str(build_anneal)!r}).resolve()
                    if args == ["--version", "--verbose"]:
                        print("rustc 1.85.0 (wrong-in-build)" if in_build else "rustc 1.98.0-nightly")
                        print("commit-hash: " + ("2222222222222222222222222222222222222222" if in_build else {pinned_commit!r}))
                        print("host: {triple}")
                        sys.exit(0)
                    if args == ["--print", "sysroot"]:
                        print({str(b_sysroot)!r})
                        sys.exit(0)
                    if args == ["--print", "cfg"]:
                        print('target_arch="x86_64"')
                        print('target_os="linux"')
                        print('target_pointer_width="64"')
                        print('target_endian="little"')
                        sys.exit(0)
                    sys.exit(1)
                    """
                ),
            )
            caller_out = root / "caller_outside_anneal"
            caller_out.mkdir()
            old_cwd = Path.cwd()
            try:
                os.chdir(caller_out)
                with (
                    tempfile.TemporaryDirectory(prefix="anneal-gmut-probe-") as p,
                    mock.patch.dict(
                        os.environ,
                        _isolated_extract_env(
                            root,
                            {"CARGO": str(build_sens_cargo), "PATH": "/nonexistent-bin"},
                        ),
                        clear=True,
                    ),
                    self.assertRaisesRegex(
                        RuntimeError, "usable across working directories"
                    ),
                ):
                    check_guard_mutation._resolve_cargo_for_rustc(
                        bad_sr_rustc, bad_sr, Path(p), 5, build_cwd=build_anneal
                    )
                with (
                    mock.patch.dict(
                        os.environ,
                        _isolated_extract_env(
                            root,
                            {
                                "RUSTC": str(build_sens_rustc),
                                "CARGO": str(build_sens_cargo),
                                "PATH": "/nonexistent-bin",
                            },
                        ),
                        clear=True,
                    ),
                    mock.patch.object(
                        check_guard_mutation,
                        "_read_pinned_compiler_commit",
                        return_value=pinned_commit,
                    ),
                ):
                    resolved_tc = check_guard_mutation._resolve_extract_toolchain(
                        build_anneal, None, 10
                    )
                self.assertEqual(
                    resolved_tc,
                    (
                        Path(os.path.abspath(b_sr_rustc)),
                        Path(os.path.abspath(b_sr_cargo)),
                        str(b_sysroot),
                        triple,
                    ),
                )
            finally:
                os.chdir(old_cwd)
            iso_anneal = _create_isolated_extract_anneal_root(
                root / "nonexec_anneal_iso"
            )
            with (
                mock.patch.dict(
                    os.environ, _isolated_extract_env(root), clear=True
                ),
                self.assertRaisesRegex(RuntimeError, "failed to execute cargo"),
            ):
                check_guard_mutation._build_extract_baseline(
                    anneal_root=iso_anneal,
                    rustc_bin=bad_sr_rustc,
                    cargo_bin=non_exec_cargo,
                    sysroot=str(bad_sr),
                    host_triple=triple,
                    base_target_dir=root / "nonexec_target",
                    need_capture=True,
                    need_unit=False,
                    timeout_sec=5,
                )

    def test_extract_guards_rejects_ambient_cargo_and_rustup_configs(self):
        # `_build_extract_baseline` and `_probe_rustc_candidate` must fail
        # closed before executing Cargo or rustc when an ancestor directory of
        # `anneal_root` or `TMPDIR` contains `.cargo/config*` or
        # `rust-toolchain*`.
        pinned_commit = check_guard_mutation._read_pinned_compiler_commit(
            ANNEAL_ROOT
        )
        triple = "x86_64-unknown-linux-gnu"
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-amb-") as tmp:
            root = Path(tmp)
            invoked = root / "invoked.flag"

            # Case 1: ancestor of `anneal_root` holds `.cargo/config.toml`.
            parent_cfg = root / "with_cargo_cfg"
            fake_anneal = parent_cfg / "repo" / "anneal"
            fake_anneal.mkdir(parents=True)
            (parent_cfg / ".cargo").mkdir()
            (parent_cfg / ".cargo" / "config.toml").write_text(
                f'[target.{triple}]\nlinker = "/nonexistent/evil"\n',
                encoding="utf-8",
            )
            fake_cargo = root / "cargo"
            _write_fake_lean(
                fake_cargo,
                f"Path({str(invoked)!r}).write_text('ran', encoding='utf-8')\nsys.exit(0)\n",
            )
            fake_rustc = root / "rustc"
            _write_fake_probe_rustc(
                fake_rustc,
                commit_hash=pinned_commit,
                triple=triple,
                sysroot=root / "sysroot",
            )
            with (
                mock.patch.dict(
                    os.environ, _isolated_extract_env(root), clear=True
                ),
                self.assertRaisesRegex(RuntimeError, "ambient toolchain"),
            ):
                check_guard_mutation._build_extract_baseline(
                    anneal_root=fake_anneal,
                    rustc_bin=fake_rustc,
                    cargo_bin=fake_cargo,
                    sysroot=str(root / "sysroot"),
                    host_triple=triple,
                    base_target_dir=root / "target_dir",
                    need_capture=True,
                    need_unit=False,
                    timeout_sec=10,
                )
            self.assertFalse(invoked.exists())

            # Case 2: `TMPDIR` contains `rust-toolchain.toml` when probing.
            sysroot = root / "sysroot"
            _populate_fake_rustc_dev_sysroot(sysroot, triple)
            hostile_tmp = root / "hostile_tmp"
            hostile_tmp.mkdir()
            (hostile_tmp / "rust-toolchain.toml").write_text(
                '[toolchain]\npath = "/nonexistent/evil"\n',
                encoding="utf-8",
            )
            sentinel_rustc = root / "sentinel_rustc"
            _write_fake_lean(
                sentinel_rustc,
                textwrap.dedent(
                    f"""\
                    if Path.cwd().resolve() == Path({str(hostile_tmp)!r}).resolve() or Path({str(hostile_tmp)!r}).resolve() in Path.cwd().resolve().parents:
                        Path({str(invoked)!r}).write_text("probed-in-hostile-tmp", encoding="utf-8")
                    if sys.argv[1:] == ["--version", "--verbose"]:
                        print("rustc 1.98.0-nightly")
                        print("commit-hash: {pinned_commit}")
                        print("host: {triple}")
                        sys.exit(0)
                    if sys.argv[1:] == ["--print", "sysroot"]:
                        print({str(sysroot)!r})
                        sys.exit(0)
                    if sys.argv[1:] == ["--print", "cfg"]:
                        print('target_arch="x86_64"')
                        print('target_os="linux"')
                        print('target_pointer_width="64"')
                        print('target_endian="little"')
                        sys.exit(0)
                    sys.exit(1)
                    """
                ),
            )
            clean_cwd = root / "clean_caller"
            clean_cwd.mkdir()
            old_cwd = Path.cwd()
            try:
                os.chdir(clean_cwd)
                with (
                    mock.patch.dict(
                        os.environ,
                        _isolated_extract_env(root, {"TMPDIR": str(hostile_tmp)}),
                        clear=True,
                    ),
                    mock.patch.object(tempfile, "tempdir", str(hostile_tmp)),
                    self.assertRaisesRegex(RuntimeError, "ambient toolchain"),
                ):
                    check_guard_mutation._probe_rustc_candidate(
                        sentinel_rustc, pinned_commit, 10
                    )
            finally:
                os.chdir(old_cwd)
            self.assertFalse(invoked.exists())

            # Case 3: `$CARGO_HOME/config.toml` setting `target.<triple>.linker`
            # (or `[build]`/`[env]` in `config` or invalid/symlinked configs)
            # must fail closed before running Cargo, while benign `[source]`
            # vendoring config in `$CARGO_HOME/config.toml` passes.
            clean_anneal = root / "clean_repo" / "anneal"
            clean_anneal.mkdir(parents=True)
            cargo_home_bad = root / "cargo_home_bad"
            cargo_home_bad.mkdir()
            (cargo_home_bad / "config.toml").write_text(
                f'[target.{triple}]\nlinker = "/nonexistent/evil"\n',
                encoding="utf-8",
            )
            with (
                mock.patch.dict(
                    os.environ, {"CARGO_HOME": str(cargo_home_bad)}
                ),
                self.assertRaisesRegex(RuntimeError, "Cargo home config"),
            ):
                check_guard_mutation._build_extract_baseline(
                    anneal_root=clean_anneal,
                    rustc_bin=fake_rustc,
                    cargo_bin=fake_cargo,
                    sysroot=str(sysroot),
                    host_triple=triple,
                    base_target_dir=root / "ch_target_1",
                    need_capture=True,
                    need_unit=False,
                    timeout_sec=10,
                )
            self.assertFalse(invoked.exists())

            # Case 4: `CARGO_HOME` unset, default `$HOME/.cargo/config.toml`
            # defining `target.<triple>.linker` must also fail closed.
            fake_home = root / "fake_home"
            (fake_home / ".cargo").mkdir(parents=True)
            (fake_home / ".cargo" / "config.toml").write_text(
                f'[target.{triple}]\nlinker = "/nonexistent/evil"\n',
                encoding="utf-8",
            )
            env_home = {
                k: v for k, v in os.environ.items() if k != "CARGO_HOME"
            } | {"HOME": str(fake_home)}
            with (
                mock.patch.dict(os.environ, env_home, clear=True),
                self.assertRaisesRegex(RuntimeError, "Cargo home config"),
            ):
                check_guard_mutation._build_extract_baseline(
                    anneal_root=clean_anneal,
                    rustc_bin=fake_rustc,
                    cargo_bin=fake_cargo,
                    sysroot=str(sysroot),
                    host_triple=triple,
                    base_target_dir=root / "ch_target_2",
                    need_capture=True,
                    need_unit=False,
                    timeout_sec=10,
                )
            self.assertFalse(invoked.exists())

            # Case 5: `$CARGO_HOME/config` extensionless `[build]` override and
            # symlinked config fail closed.
            cargo_home_ext = root / "cargo_home_ext"
            cargo_home_ext.mkdir()
            (cargo_home_ext / "config").write_text(
                '[build]\nrustc-wrapper = "evil"\n',
                encoding="utf-8",
            )
            with (
                mock.patch.dict(
                    os.environ, {"CARGO_HOME": str(cargo_home_ext)}
                ),
                self.assertRaisesRegex(RuntimeError, "Cargo home config"),
            ):
                check_guard_mutation._build_extract_baseline(
                    anneal_root=clean_anneal,
                    rustc_bin=fake_rustc,
                    cargo_bin=fake_cargo,
                    sysroot=str(sysroot),
                    host_triple=triple,
                    base_target_dir=root / "ch_target_3",
                    need_capture=True,
                    need_unit=False,
                    timeout_sec=10,
                )
            self.assertFalse(invoked.exists())

            cargo_home_sym = root / "cargo_home_sym"
            cargo_home_sym.mkdir()
            (cargo_home_sym / "config.toml").symlink_to(
                cargo_home_bad / "config.toml"
            )
            with (
                mock.patch.dict(
                    os.environ, {"CARGO_HOME": str(cargo_home_sym)}
                ),
                self.assertRaisesRegex(RuntimeError, "Cargo home config"),
            ):
                check_guard_mutation._build_extract_baseline(
                    anneal_root=clean_anneal,
                    rustc_bin=fake_rustc,
                    cargo_bin=fake_cargo,
                    sysroot=str(sysroot),
                    host_triple=triple,
                    base_target_dir=root / "ch_target_4",
                    need_capture=True,
                    need_unit=False,
                    timeout_sec=10,
                )
            self.assertFalse(invoked.exists())

            # Case 6: vendored `[source]`-only `$CARGO_HOME/config.toml` is
            # permitted by `_assert_no_ambient_toolchain_configs`, and relative
            # `CARGO_HOME` / `HOME` resolve against `anneal_root` (both logical
            # and symlink-resolved) rather than the caller's working directory.
            cargo_home_vendor = root / "cargo_home_vendor"
            cargo_home_vendor.mkdir()
            (cargo_home_vendor / "config.toml").write_text(
                '[source.crates-io]\nreplace-with = "anneal-vendor"\n'
                '[source.anneal-vendor]\ndirectory = "/opt/anneal-cargo-vendor"\n',
                encoding="utf-8",
            )
            with mock.patch.dict(
                os.environ, {"CARGO_HOME": str(cargo_home_vendor)}
            ):
                check_guard_mutation._assert_no_ambient_toolchain_configs(
                    clean_anneal,
                    check_root_dot_cargo=True,
                    check_cargo_home=True,
                )

            caller_clean = root / "caller_clean"
            caller_clean.mkdir()
            (caller_clean / "rel_cargo").mkdir()
            (caller_clean / "rel_cargo" / "config.toml").write_text(
                '[source.crates-io]\nreplace-with = "anneal-vendor"\n'
                '[source.anneal-vendor]\n'
                'directory = "/opt/anneal-cargo-vendor"\n',
                encoding="utf-8",
            )
            (clean_anneal / "rel_cargo").mkdir()
            (clean_anneal / "rel_cargo" / "config.toml").write_text(
                f'[target.{triple}]\nlinker = "/nonexistent/evil"\n',
                encoding="utf-8",
            )
            old_cwd = Path.cwd()
            try:
                os.chdir(caller_clean)
                with (
                    mock.patch.dict(os.environ, {"CARGO_HOME": "rel_cargo"}),
                    self.assertRaisesRegex(RuntimeError, "Cargo home config"),
                ):
                    check_guard_mutation._build_extract_baseline(
                        anneal_root=clean_anneal,
                        rustc_bin=fake_rustc,
                        cargo_bin=fake_cargo,
                        sysroot=str(sysroot),
                        host_triple=triple,
                        base_target_dir=root / "ch_target_5",
                        need_capture=True,
                        need_unit=False,
                        timeout_sec=10,
                    )
                self.assertFalse(invoked.exists())

                # Relative `HOME` with `CARGO_HOME` unset also resolves against
                # `anneal_root`.
                rel_home_cargo = clean_anneal / "rel_home" / ".cargo"
                rel_home_cargo.mkdir(parents=True)
                (rel_home_cargo / "config.toml").write_text(
                    f'[target.{triple}]\nlinker = "/nonexistent/evil"\n',
                    encoding="utf-8",
                )
                env_rel_home = {
                    k: v for k, v in os.environ.items() if k != "CARGO_HOME"
                } | {"HOME": "rel_home"}
                with (
                    mock.patch.dict(os.environ, env_rel_home, clear=True),
                    self.assertRaisesRegex(RuntimeError, "Cargo home config"),
                ):
                    check_guard_mutation._build_extract_baseline(
                        anneal_root=clean_anneal,
                        rustc_bin=fake_rustc,
                        cargo_bin=fake_cargo,
                        sysroot=str(sysroot),
                        host_triple=triple,
                        base_target_dir=root / "ch_target_6",
                        need_capture=True,
                        need_unit=False,
                        timeout_sec=10,
                    )
                self.assertFalse(invoked.exists())

                # Symlinked `anneal_root` resolves `../rel_parent_cargo` against
                # the physical Cargo `cwd` as well as the logical path.
                real_parent = root / "real_parent"
                real_anneal = real_parent / "anneal"
                real_anneal.mkdir(parents=True)
                (real_parent / "rel_parent_cargo").mkdir()
                (
                    real_parent / "rel_parent_cargo" / "config.toml"
                ).write_text(
                    f'[target.{triple}]\nlinker = "/nonexistent/evil"\n',
                    encoding="utf-8",
                )
                sym_parent = root / "sym_parent"
                sym_parent.mkdir()
                sym_anneal = sym_parent / "anneal"
                sym_anneal.symlink_to(real_anneal)
                with (
                    mock.patch.dict(
                        os.environ, {"CARGO_HOME": "../rel_parent_cargo"}
                    ),
                    self.assertRaisesRegex(RuntimeError, "Cargo home config"),
                ):
                    check_guard_mutation._build_extract_baseline(
                        anneal_root=sym_anneal,
                        rustc_bin=fake_rustc,
                        cargo_bin=fake_cargo,
                        sysroot=str(sysroot),
                        host_triple=triple,
                        base_target_dir=root / "ch_target_7",
                        need_capture=True,
                        need_unit=False,
                        timeout_sec=10,
                    )
                self.assertFalse(invoked.exists())

                # Clean relative `CARGO_HOME` (offline vendored `[source]`)
                # resolves cleanly to an absolute path in
                # `_extract_subprocess_env`.
                (real_anneal / "rel_vendor").mkdir()
                (real_anneal / "rel_vendor" / "config.toml").write_text(
                    '[source.crates-io]\nreplace-with = "anneal-vendor"\n'
                    '[source.anneal-vendor]\n'
                    'directory = "/opt/anneal-cargo-vendor"\n',
                    encoding="utf-8",
                )
                with mock.patch.dict(
                    os.environ, {"CARGO_HOME": "rel_vendor"}
                ):
                    check_guard_mutation._assert_no_ambient_toolchain_configs(
                        sym_anneal,
                        check_root_dot_cargo=True,
                        check_cargo_home=True,
                    )
                    ext_env = check_guard_mutation._extract_subprocess_env(
                        fake_rustc,
                        str(sysroot),
                        root / "ext_ice",
                        triple,
                        cargo_cwd=sym_anneal,
                    )
                    self.assertEqual(
                        Path(ext_env["CARGO_HOME"]),
                        (real_anneal / "rel_vendor").resolve(),
                    )
                    self.assertEqual(ext_env["CARGO_NET_OFFLINE"], "true")

                # Case 7: remote `[source]` replacements, dangling/cyclic
                # `replace-with`, and `[net]`/`[registries]`/`[http]`/`[term]`
                # configs must all fail closed.
                bad_cargo_configs = (
                    (
                        "remote_registry",
                        '[source.crates-io]\nreplace-with = "mirror"\n'
                        '[source.mirror]\n'
                        'registry = "https://evil.example/index"\n',
                    ),
                    (
                        "remote_git",
                        '[source.crates-io]\nreplace-with = "mirror"\n'
                        '[source.mirror]\n'
                        'git = "https://evil.example/repo.git"\n',
                    ),
                    (
                        "local_registry_key",
                        '[source.crates-io]\nreplace-with = "mirror"\n'
                        '[source.mirror]\nlocal-registry = "/tmp/reg"\n',
                    ),
                    (
                        "dangling_replace",
                        '[source.crates-io]\nreplace-with = "missing"\n',
                    ),
                    (
                        "cyclic_replace",
                        '[source.crates-io]\nreplace-with = "a"\n'
                        '[source.a]\nreplace-with = "crates-io"\n',
                    ),
                    (
                        "ambient_net",
                        "[net]\noffline = false\n",
                    ),
                    (
                        "ambient_registries",
                        '[registries.evil]\nindex = "https://evil.example"\n',
                    ),
                )
                for label, cfg_text in bad_cargo_configs:
                    bad_ch = root / f"bad_ch_{label}"
                    bad_ch.mkdir()
                    (bad_ch / "config.toml").write_text(
                        cfg_text, encoding="utf-8"
                    )
                    with (
                        mock.patch.dict(
                            os.environ, {"CARGO_HOME": str(bad_ch)}
                        ),
                        self.assertRaisesRegex(
                            RuntimeError, "Cargo home config", msg=label
                        ),
                    ):
                        check_guard_mutation._build_extract_baseline(
                            anneal_root=clean_anneal,
                            rustc_bin=fake_rustc,
                            cargo_bin=fake_cargo,
                            sysroot=str(sysroot),
                            host_triple=triple,
                            base_target_dir=root / f"ch_bad_{label}",
                            need_capture=True,
                            need_unit=False,
                            timeout_sec=10,
                        )
                    self.assertFalse(invoked.exists())

                # Case 8: when `anneal_root` is checked out beneath `$HOME`
                # (`~/zerocopy/anneal`), offline directory-vendored
                # `$HOME/.cargo/config.toml` passes when `CARGO_HOME` defaults
                # to `$HOME/.cargo`, fails closed on non-vendoring settings,
                # fails closed when `CARGO_HOME` points elsewhere, and never
                # permits `<repo_root>/.cargo`.
                home_checkout = root / "home_checkout"
                home_anneal = home_checkout / "zerocopy" / "anneal"
                home_anneal.mkdir(parents=True)
                home_cargo = home_checkout / ".cargo"
                home_cargo.mkdir()
                (home_cargo / "config.toml").write_text(
                    '[source.crates-io]\nreplace-with = "anneal-vendor"\n'
                    '[source.anneal-vendor]\n'
                    'directory = "/opt/anneal-cargo-vendor"\n',
                    encoding="utf-8",
                )
                env_home_co = {
                    k: v for k, v in os.environ.items() if k != "CARGO_HOME"
                } | {"HOME": str(home_checkout)}
                with mock.patch.dict(os.environ, env_home_co, clear=True):
                    check_guard_mutation._assert_no_ambient_toolchain_configs(
                        home_anneal,
                        check_root_dot_cargo=True,
                        check_cargo_home=True,
                    )
                with (
                    mock.patch.dict(
                        os.environ,
                        env_home_co | {"CARGO_HOME": str(cargo_home_vendor)},
                        clear=True,
                    ),
                    self.assertRaisesRegex(RuntimeError, "ambient toolchain"),
                ):
                    check_guard_mutation._assert_no_ambient_toolchain_configs(
                        home_anneal,
                        check_root_dot_cargo=True,
                        check_cargo_home=True,
                    )
                (home_cargo / "config.toml").write_text(
                    f'[target.{triple}]\nlinker = "/nonexistent/evil"\n',
                    encoding="utf-8",
                )
                with (
                    mock.patch.dict(os.environ, env_home_co, clear=True),
                    self.assertRaisesRegex(RuntimeError, "Cargo home config"),
                ):
                    check_guard_mutation._build_extract_baseline(
                        anneal_root=home_anneal,
                        rustc_bin=fake_rustc,
                        cargo_bin=fake_cargo,
                        sysroot=str(sysroot),
                        host_triple=triple,
                        base_target_dir=root / "ch_target_home_co",
                        need_capture=True,
                        need_unit=False,
                        timeout_sec=10,
                    )
                self.assertFalse(invoked.exists())
                (home_checkout / "rust-toolchain.toml").write_text(
                    '[toolchain]\nchannel = "stable"\n', encoding="utf-8"
                )
                (home_cargo / "config.toml").write_text(
                    '[source.crates-io]\nreplace-with = "anneal-vendor"\n'
                    '[source.anneal-vendor]\n'
                    'directory = "/opt/anneal-cargo-vendor"\n',
                    encoding="utf-8",
                )
                with (
                    mock.patch.dict(os.environ, env_home_co, clear=True),
                    self.assertRaisesRegex(RuntimeError, "ambient toolchain"),
                ):
                    check_guard_mutation._assert_no_ambient_toolchain_configs(
                        home_anneal,
                        check_root_dot_cargo=True,
                        check_cargo_home=True,
                    )
                repo_dot_cargo = home_checkout / "zerocopy" / ".cargo"
                repo_dot_cargo.mkdir()
                (repo_dot_cargo / "config.toml").write_text(
                    '[source.crates-io]\nreplace-with = "anneal-vendor"\n'
                    '[source.anneal-vendor]\n'
                    'directory = "/opt/anneal-cargo-vendor"\n',
                    encoding="utf-8",
                )
                with (
                    mock.patch.dict(
                        os.environ,
                        {
                            "HOME": str(root / "clean_home_sep"),
                            "CARGO_HOME": str(repo_dot_cargo),
                        },
                        clear=True,
                    ),
                    self.assertRaisesRegex(
                        RuntimeError, "forbidden root Cargo config directory"
                    ),
                ):
                    check_guard_mutation._assert_no_ambient_toolchain_configs(
                        home_anneal,
                        check_root_dot_cargo=True,
                        check_cargo_home=True,
                    )

                # Hostile workstation `HOME` (`~/.cargo/config.toml` `[build]`
                # + `~/rust-toolchain.toml`) must not break synthetic tests.
                (home_cargo / "config.toml").write_text(
                    '[build]\nrustc-wrapper = "evil"\n', encoding="utf-8"
                )
                with mock.patch.dict(
                    os.environ,
                    {
                        "HOME": str(home_checkout),
                        "CARGO_HOME": str(home_cargo),
                    },
                ):
                    rc_h, _, err_h, rep_h, _, _ = (
                        self._run_synthetic_extract_suite(
                            filter_name="extract_reject_fn_alignment",
                            outcome="kill",
                        )
                    )
                    self.assertEqual(rc_h, 0, err_h)
                    self.assertEqual(rep_h["killed"], 1, rep_h)
            finally:
                os.chdir(old_cwd)

    def test_extract_guards_requires_exit_code_1_on_baseline_rejection(self):
        pinned_commit = check_guard_mutation._read_pinned_compiler_commit(
            ANNEAL_ROOT
        )
        triple = "x86_64-unknown-linux-gnu"
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-base-rc-") as tmp:
            root = Path(tmp)
            iso_anneal = _create_isolated_extract_anneal_root(
                root / "anneal_iso"
            )
            tc_bin = root / "bin"
            sysroot = root / "sysroot"
            tc_bin.mkdir(parents=True)
            _populate_fake_rustc_dev_sysroot(sysroot, triple)
            _write_fake_probe_rustc(
                tc_bin / "rustc",
                commit_hash=pinned_commit,
                triple=triple,
                sysroot=sysroot,
            )
            cargo_body = textwrap.dedent(
                f"""\
                args = sys.argv[1:]
                if args == ["--version"]:
                    print("cargo 1.98.0")
                    sys.exit(0)
                tdir = Path(args[args.index("--target-dir") + 1])
                deps = tdir / {triple!r} / "debug" / "deps"
                deps.mkdir(parents=True, exist_ok=True)
                for dep in {check_guard_mutation.EXTRACT_DIRECT_DEPS!r}:
                    rlib = deps / f"lib{{dep}}-deadbeef.rlib"
                    rlib.write_bytes(b"rlib")
                    print(json.dumps({{
                        "reason": "compiler-artifact",
                        "target": {{"name": dep, "kind": ["lib"]}},
                        "profile": {{"test": False}},
                        "filenames": [str(rlib)],
                    }}))
                cap_exe = tdir / {triple!r} / "debug" / "anneal-rustc-capture"
                cap_exe.write_text(
                    "#!{sys.executable}\\n"
                    "import json, sys\\n"
                    "src = sys.argv[sys.argv.index('--crate-root') + 1]\\n"
                    "if 'sanity_' in src:\\n"
                    "    print(json.dumps({{'status': 'captured'}}))\\n"
                    "    sys.exit(0)\\n"
                    "print(json.dumps({{'status': 'unsupported', "
                    "'diagnostics': ['function alignment'], "
                    "'unsupported': []}}))\\n"
                    "sys.exit(0)\\n",
                    encoding="utf-8",
                )
                cap_exe.chmod(0o755)
                print(json.dumps({{
                    "reason": "compiler-artifact",
                    "target": {{"name": "anneal-rustc-capture", "kind": ["bin"]}},
                    "profile": {{"test": False}},
                    "executable": str(cap_exe),
                    "filenames": [str(cap_exe)],
                }}))
                sys.exit(0)
                """
            )
            _write_fake_lean(tc_bin / "cargo", cargo_body)
            env = _isolated_extract_env(root)
            res = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--anneal-root",
                    str(iso_anneal),
                    "--rustc",
                    str(tc_bin / "rustc"),
                    "--suite",
                    "extract_guards",
                    "--filter",
                    "extract_reject_fn_alignment",
                    "--jobs",
                    "1",
                ],
                env=env,
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("with exit code 1", res.stdout + res.stderr)

    def test_extract_probe_strips_forbidden_loader_env_vars(self):
        pinned_commit = check_guard_mutation._read_pinned_compiler_commit(
            ANNEAL_ROOT
        )
        triple = "x86_64-unknown-linux-gnu"
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-probe-env-") as tmp:
            root = Path(tmp)
            iso_anneal = _create_isolated_extract_anneal_root(
                root / "anneal_iso"
            )
            sysroot = root / "sysroot"
            _populate_fake_rustc_dev_sysroot(sysroot, triple)
            (sysroot / "bin").mkdir(parents=True)
            log_path = root / "probe_loader_env.log"
            guard_env_check = textwrap.dedent(
                f"""\
                forbidden = {check_guard_mutation.FORBIDDEN_LOADER_ENV_VARS!r}
                seen = [k for k in forbidden if k in os.environ]
                with open({str(log_path)!r}, "a", encoding="utf-8") as fh:
                    fh.write(json.dumps({{
                        "argv": sys.argv,
                        "seen": seen,
                        "ld_lib": os.environ.get("LD_LIBRARY_PATH"),
                    }}) + "\\n")
                if seen:
                    sys.stderr.write("leaked forbidden loader env: " + ",".join(seen))
                    sys.exit(99)
                """
            )
            rustc_bin = sysroot / "bin" / "rustc"
            _write_fake_lean(
                rustc_bin,
                guard_env_check
                + textwrap.dedent(
                    f"""\
                    args = sys.argv[1:]
                    if args == ["--version", "--verbose"]:
                        print("rustc 1.98.0-nightly")
                        print("commit-hash: {pinned_commit}")
                        print("host: {triple}")
                        sys.exit(0)
                    if args == ["--print", "sysroot"]:
                        print({str(sysroot)!r})
                        sys.exit(0)
                    if args == ["--print", "cfg"]:
                        print('target_arch="x86_64"')
                        print('target_os="linux"')
                        print('target_pointer_width="64"')
                        print('target_endian="little"')
                        sys.exit(0)
                    sys.exit(1)
                    """
                ),
            )
            cargo_bin = sysroot / "bin" / "cargo"
            _write_fake_lean(
                cargo_bin,
                guard_env_check
                + "if sys.argv[1:] == ['--version']:\n"
                + "    print('cargo 1.98.0')\n"
                + "    sys.exit(0)\n"
                + "sys.exit(1)\n",
            )
            dirty_env = _isolated_extract_env(root)
            for var in check_guard_mutation.FORBIDDEN_LOADER_ENV_VARS:
                dirty_env[var] = "/nonexistent/evil-preload.so"
            dirty_env["RUSTC"] = str(rustc_bin)
            dirty_env["CARGO"] = str(cargo_bin)
            dirty_env["PATH"] = str(sysroot / "bin")
            dirty_env["LD_LIBRARY_PATH"] = "/opt/safe-rustc/lib"

            old_cwd = Path.cwd()
            try:
                os.chdir(root)
                with mock.patch.dict(os.environ, dirty_env, clear=True):
                    self.assertTrue(
                        check_guard_mutation._is_runnable_rustc(rustc_bin, 10)
                    )
                    info = check_guard_mutation._query_rustc_info(rustc_bin, 10)
                    self.assertEqual(info, (pinned_commit, triple, str(sysroot)))
                    self.assertTrue(
                        check_guard_mutation._is_supported_extract_host(
                            rustc_bin, triple, 10
                        )
                    )
                    self.assertEqual(
                        check_guard_mutation._run_cargo_version(cargo_bin, 10),
                        "cargo 1.98.0",
                    )
                    resolved = check_guard_mutation._resolve_extract_toolchain(
                        iso_anneal, None, 10
                    )
                    self.assertEqual(
                        resolved,
                        (rustc_bin, cargo_bin, str(sysroot), triple),
                    )
            finally:
                os.chdir(old_cwd)

            entries = [
                json.loads(line)
                for line in log_path.read_text(encoding="utf-8").splitlines()
            ]
            self.assertGreaterEqual(len(entries), 10)
            for entry in entries:
                self.assertEqual(entry["seen"], [], entry)
                self.assertEqual(entry["ld_lib"], "/opt/safe-rustc/lib", entry)

    def test_extract_toolchain_resolution_rejects_ambient_configs_before_probe(
        self,
    ):
        pinned_commit = check_guard_mutation._read_pinned_compiler_commit(
            ANNEAL_ROOT
        )
        triple = "x86_64-unknown-linux-gnu"
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-amb-res-") as tmp:
            root = Path(tmp)
            invoked = root / "invoked.flag"
            tc_bin = root / "tc_bin"
            tc_bin.mkdir()
            sysroot = root / "sysroot"
            _populate_fake_rustc_dev_sysroot(sysroot, triple)

            sentinel_rustc = tc_bin / "rustc"
            sentinel_cargo = tc_bin / "cargo"
            _write_fake_lean(
                sentinel_rustc,
                textwrap.dedent(
                    f"""\
                    Path({str(invoked)!r}).write_text(
                        f"rustc:{{os.getcwd()}}", encoding="utf-8"
                    )
                    args = sys.argv[1:]
                    if args == ["--version", "--verbose"]:
                        print("rustc 1.98.0-nightly")
                        print("commit-hash: {pinned_commit}")
                        print("host: {triple}")
                        sys.exit(0)
                    if args == ["--print", "sysroot"]:
                        print({str(sysroot)!r})
                        sys.exit(0)
                    if args == ["--print", "cfg"]:
                        print('target_arch="x86_64"')
                        print('target_os="linux"')
                        print('target_pointer_width="64"')
                        print('target_endian="little"')
                        sys.exit(0)
                    sys.exit(1)
                    """
                ),
            )
            _write_fake_lean(
                sentinel_cargo,
                textwrap.dedent(
                    f"""\
                    Path({str(invoked)!r}).write_text(
                        f"cargo:{{os.getcwd()}}", encoding="utf-8"
                    )
                    if sys.argv[1:] == ["--version"]:
                        print("cargo 1.98.0")
                        sys.exit(0)
                    sys.exit(1)
                    """
                ),
            )
            fake_lean = root / "fake_lean"
            _write_fake_lean(fake_lean, "sys.exit(0)\n")
            one_ext = [
                g
                for g in check_guard_mutation.EXTRACT_GUARDS
                if g.guard_id == "extract_reject_fn_alignment"
            ]

            for kind in ("rust_toolchain", "ancestor_dot_cargo"):
                repo = root / f"repo_{kind}"
                amb_anneal = _create_isolated_extract_anneal_root(
                    repo / "anneal"
                )
                if kind == "rust_toolchain":
                    (amb_anneal / "rust-toolchain.toml").write_text(
                        '[toolchain]\nchannel = "nightly"\n', encoding="utf-8"
                    )
                else:
                    (repo / ".cargo").mkdir()
                    (repo / ".cargo" / "config.toml").write_text(
                        f'[target.{triple}]\nlinker = "/nonexistent/evil"\n',
                        encoding="utf-8",
                    )

                clean_caller = root / f"clean_caller_{kind}"
                clean_caller.mkdir()
                env = _isolated_extract_env(root)
                env.pop("RUSTC", None)
                env["CARGO"] = str(sentinel_cargo)
                env["PATH"] = str(tc_bin)

                old_cwd = Path.cwd()
                try:
                    for caller_dir in (clean_caller, amb_anneal):
                        os.chdir(caller_dir)
                        with (
                            mock.patch.dict(os.environ, env, clear=True),
                            self.assertRaisesRegex(
                                RuntimeError,
                                "ambient toolchain|forbidden root Cargo config",
                            ),
                        ):
                            check_guard_mutation._probe_rustc_candidate(
                                sentinel_rustc,
                                pinned_commit,
                                10,
                                build_cwd=amb_anneal,
                            )
                        self.assertFalse(invoked.exists(), f"{kind}:{caller_dir}")

                        for suite_name in ("extract_guards", "all"):
                            with (
                                mock.patch.dict(os.environ, env, clear=True),
                                mock.patch.object(
                                    check_guard_mutation,
                                    "_select_guards",
                                    return_value=([], [], [], one_ext),
                                ),
                                self.assertRaisesRegex(
                                    RuntimeError,
                                    "ambient toolchain|forbidden root Cargo config",
                                ),
                            ):
                                check_guard_mutation.run_guard_mutation_suite(
                                    anneal_root=amb_anneal,
                                    lean_bin=fake_lean,
                                    suite=suite_name,
                                    jobs=1,
                                )
                            self.assertFalse(
                                invoked.exists(),
                                f"{kind}:{caller_dir}:{suite_name}",
                            )
                finally:
                    os.chdir(old_cwd)

            clean_anneal = _create_isolated_extract_anneal_root(
                root / "clean_repo" / "anneal"
            )
            dirty_caller = root / "dirty_caller"
            dirty_caller.mkdir()
            (dirty_caller / "rust-toolchain.toml").write_text(
                '[toolchain]\nchannel = "nightly"\n', encoding="utf-8"
            )
            for use_explicit_env in (False, True):
                env_caller = _isolated_extract_env(root)
                if use_explicit_env:
                    env_caller["RUSTC"] = str(sentinel_rustc)
                else:
                    env_caller.pop("RUSTC", None)
                env_caller["CARGO"] = str(sentinel_cargo)
                env_caller["PATH"] = str(tc_bin)
                old_cwd = Path.cwd()
                try:
                    os.chdir(dirty_caller)
                    with (
                        mock.patch.dict(os.environ, env_caller, clear=True),
                        self.assertRaisesRegex(
                            RuntimeError, "ambient toolchain"
                        ),
                    ):
                        check_guard_mutation._resolve_extract_toolchain(
                            clean_anneal, None, 10
                        )
                    self.assertFalse(
                        invoked.exists(), f"dirty_caller:{use_explicit_env}"
                    )
                finally:
                    os.chdir(old_cwd)

    def test_resolve_executable_token_ignores_cwd_bare_commands_and_non_exec(self):
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-exe-") as tmp:
            root = Path(tmp)
            cwd_dir = root / "cwd_untrusted"
            cwd_dir.mkdir()
            path_dir = root / "trusted_path"
            path_dir.mkdir()

            cwd_rustc = cwd_dir / "rustc"
            cwd_rustc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            cwd_rustc.chmod(0o755)
            cwd_cargo = cwd_dir / "cargo"
            cwd_cargo.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            cwd_cargo.chmod(0o644)

            path_rustc = path_dir / "rustc"
            path_rustc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            path_rustc.chmod(0o755)
            path_nonexec_lean = path_dir / "lean"
            path_nonexec_lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            path_nonexec_lean.chmod(0o644)

            old_cwd = Path.cwd()
            try:
                os.chdir(cwd_dir)
                with mock.patch.dict(
                    os.environ,
                    _isolated_extract_env(root, {"PATH": str(path_dir)}),
                    clear=True,
                ):
                    self.assertEqual(
                        check_guard_mutation._resolve_executable_token("rustc"),
                        path_rustc.resolve(),
                    )
                    self.assertIsNone(
                        check_guard_mutation._resolve_executable_token("cargo")
                    )
                    self.assertIsNone(
                        check_guard_mutation._resolve_executable_token("lean")
                    )
                    self.assertEqual(
                        check_guard_mutation._resolve_executable_token("./rustc"),
                        cwd_rustc.resolve(),
                    )
                    self.assertIsNone(
                        check_guard_mutation._resolve_executable_token("./cargo")
                    )
            finally:
                os.chdir(old_cwd)

    def test_main_cli_dot_slash_tool_paths_resolve_cwd_and_bare_uses_path(self):
        with tempfile.TemporaryDirectory(prefix="anneal-gmut-cli-exe-") as tmp:
            root = Path(tmp)
            cwd_dir = root / "cwd_explicit"
            cwd_dir.mkdir()
            nonexec_cwd = root / "cwd_nonexec"
            nonexec_cwd.mkdir()
            path_dir = root / "trusted_path"
            path_dir.mkdir()

            cwd_lean = cwd_dir / "lean"
            cwd_rustc = cwd_dir / "rustc"
            path_lean = path_dir / "lean"
            path_rustc = path_dir / "rustc"
            nonexec_lean = nonexec_cwd / "lean"
            nonexec_rustc = nonexec_cwd / "rustc"
            for exe in (cwd_lean, cwd_rustc, path_lean, path_rustc):
                exe.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                exe.chmod(0o755)
            for non_exe in (nonexec_lean, nonexec_rustc):
                non_exe.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                non_exe.chmod(0o644)

            iso_anneal = _create_isolated_extract_anneal_root(
                root / "anneal_iso"
            )
            fake_lean_report = {
                "total": 1,
                "killed": 1,
                "survived": 0,
                "errors": 0,
                "kill_rate_pct": 100.0,
                "baseline_sec": 0.01,
                "total_sec": 0.01,
                "skipped_suites": [],
                "results": [],
            }
            old_cwd = Path.cwd()
            try:
                for path_var in (str(path_dir), str(root / "empty_path")):
                    os.chdir(cwd_dir)
                    with (
                        mock.patch.dict(
                            os.environ,
                            _isolated_extract_env(root, {"PATH": path_var}),
                            clear=True,
                        ),
                        mock.patch.object(
                            check_guard_mutation,
                            "run_guard_mutation_suite",
                            return_value=fake_lean_report,
                        ) as run_mock,
                    ):
                        rc = check_guard_mutation.main([
                            "--anneal-root",
                            str(iso_anneal),
                            "--lean",
                            "./lean",
                            "--suite",
                            "mir_semantics",
                            "--lean-only",
                        ])
                        self.assertEqual(rc, 0)
                        self.assertEqual(
                            run_mock.call_args.kwargs["lean_bin"],
                            cwd_lean.resolve(),
                        )

                    seen_rustc: list[Path] = []

                    def _fake_probe(
                        rustc_bin: Path,
                        pinned_commit: str,
                        timeout_sec: int,
                        *,
                        build_cwd: Path | None = None,
                    ) -> None:
                        seen_rustc.append(rustc_bin)
                        return None

                    with (
                        mock.patch.dict(
                            os.environ,
                            _isolated_extract_env(root, {"PATH": path_var}),
                            clear=True,
                        ),
                        mock.patch.object(
                            check_guard_mutation,
                            "_read_pinned_compiler_commit",
                            return_value="0" * 40,
                        ),
                        mock.patch.object(
                            check_guard_mutation,
                            "_probe_rustc_candidate",
                            side_effect=_fake_probe,
                        ),
                    ):
                        rc = check_guard_mutation.main([
                            "--anneal-root",
                            str(iso_anneal),
                            "--rustc",
                            "./rustc",
                            "--suite",
                            "extract_guards",
                        ])
                        self.assertEqual(rc, 1)
                        self.assertEqual(seen_rustc, [cwd_rustc.resolve()])

                # Bare names must resolve strictly via PATH even when CWD has
                # executables with the same name.
                os.chdir(cwd_dir)
                with (
                    mock.patch.dict(
                        os.environ,
                        _isolated_extract_env(root, {"PATH": str(path_dir)}),
                        clear=True,
                    ),
                    mock.patch.object(
                        check_guard_mutation,
                        "run_guard_mutation_suite",
                        return_value=fake_lean_report,
                    ) as run_mock,
                ):
                    rc = check_guard_mutation.main([
                        "--anneal-root",
                        str(iso_anneal),
                        "--lean",
                        "lean",
                        "--suite",
                        "mir_semantics",
                        "--lean-only",
                    ])
                    self.assertEqual(rc, 0)
                    self.assertEqual(
                        run_mock.call_args.kwargs["lean_bin"],
                        path_lean.resolve(),
                    )

                bare_rustc_seen: list[Path] = []
                with (
                    mock.patch.dict(
                        os.environ,
                        _isolated_extract_env(root, {"PATH": str(path_dir)}),
                        clear=True,
                    ),
                    mock.patch.object(
                        check_guard_mutation,
                        "_read_pinned_compiler_commit",
                        return_value="0" * 40,
                    ),
                    mock.patch.object(
                        check_guard_mutation,
                        "_probe_rustc_candidate",
                        side_effect=lambda r, *a, **kw: bare_rustc_seen.append(r) or None,
                    ),
                ):
                    rc = check_guard_mutation.main([
                        "--anneal-root",
                        str(iso_anneal),
                        "--rustc",
                        "rustc",
                        "--suite",
                        "extract_guards",
                    ])
                    self.assertEqual(rc, 1)
                    self.assertEqual(bare_rustc_seen, [path_rustc.resolve()])

                # Non-executable `./lean` and `./rustc` fail closed without
                # falling back to executable PATH binaries.
                os.chdir(nonexec_cwd)
                with (
                    mock.patch.dict(
                        os.environ,
                        _isolated_extract_env(root, {"PATH": str(path_dir)}),
                        clear=True,
                    ),
                    self.assertRaisesRegex(
                        SystemExit, r"Lean binary not found: \./lean"
                    ),
                ):
                    check_guard_mutation.main([
                        "--anneal-root",
                        str(iso_anneal),
                        "--lean",
                        "./lean",
                        "--suite",
                        "mir_semantics",
                        "--lean-only",
                    ])

                with (
                    mock.patch.dict(
                        os.environ,
                        _isolated_extract_env(root, {"PATH": str(path_dir)}),
                        clear=True,
                    ),
                    mock.patch.object(
                        check_guard_mutation,
                        "_probe_rustc_candidate",
                    ) as probe_mock,
                ):
                    rc = check_guard_mutation.main([
                        "--anneal-root",
                        str(iso_anneal),
                        "--rustc",
                        "./rustc",
                        "--suite",
                        "extract_guards",
                    ])
                    self.assertEqual(rc, 1)
                    probe_mock.assert_not_called()
            finally:
                os.chdir(old_cwd)


if __name__ == "__main__":
    unittest.main()
