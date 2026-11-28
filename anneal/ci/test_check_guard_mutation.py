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
import json
import os
from pathlib import Path
import re
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
        self.assertGreaterEqual(
            len(check_guard_mutation.AUDIT_BOUNDARY_GUARDS), 12
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

            public theorem third_thm :
                True :=
              trivial

            private def helper_boundary : Nat := 0

            private theorem fourth_thm : True := trivial

              theorem fifth_indented :
                True := trivial

              public def sixth_indented_boundary : Nat := 1

              private theorem seventh_indented : True := trivial

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
            (10, 13),
        )
        self.assertEqual(
            check_guard_mutation.find_theorem_line_span(fixture, "fourth_thm"),
            (16, 17),
        )
        self.assertEqual(
            check_guard_mutation.find_theorem_line_span(
                fixture, "fifth_indented"
            ),
            (18, 20),
        )
        self.assertEqual(
            check_guard_mutation.find_theorem_line_span(
                fixture, "seventh_indented"
            ),
            (23, 24),
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
            is_mutant = "anneal-gmut-" in str(lean_path) and "anneal-gmut-base-" not in str(lean_path)
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

    def test_positive_canaries_live_only_in_sanity_modules(self):
        # The refutation-only invariant and fixture-local import boundary live
        # in production `check_guard_mutation.validate_refutation_modules` and
        # execute inside `validate_catalog_invariants` on every standalone
        # runner invocation.
        fixture_dir = ANNEAL_ROOT / "ci/fixtures/guard_mutation"
        guards = check_guard_mutation.MIR_SEMANTICS_GUARDS
        sanity_mods = {g.sanity_module for g in guards}
        fixture_mods = {g.fixture_module for g in guards}
        self.assertFalse(sanity_mods & fixture_mods)
        self.assertEqual(
            check_guard_mutation.validate_refutation_modules(ANNEAL_ROOT), []
        )

        # Verify `validate_catalog_invariants` (invoked by the standalone
        # runner) surfaces refutation-only violations directly.
        with mock.patch.object(
            check_guard_mutation,
            "find_forbidden_positive_checks",
            return_value=["embedded success expectation in synthetic_canary"],
        ):
            runner_errors = check_guard_mutation.validate_catalog_invariants(
                ANNEAL_ROOT
            )
        self.assertTrue(
            any(
                "embedded success expectation in synthetic_canary" in err
                for err in runner_errors
            ),
            runner_errors,
        )

        strip_lean_comments_and_strings = (
            check_guard_mutation.strip_lean_comments_and_strings
        )
        decl_re = check_guard_mutation.LEAN_DECL_TOKEN_RE
        pinned_exact_refutations = check_guard_mutation.PINNED_EXACT_REFUTATIONS
        find_forbidden_positive_checks = (
            check_guard_mutation.find_forbidden_positive_checks
        )
        allowed_local_imports = (
            check_guard_mutation.allowed_fixture_local_imports
        )

        def collect_local_imports(
            root: str, *, overrides: dict[str, str] | None = None
        ) -> set[str]:
            return check_guard_mutation.collect_fixture_local_imports(
                fixture_dir, root, overrides=overrides
            )

        # Regression checks for the Lean scanner and refutation-only rules:
        # 1. `"/-"` inside a string literal must not comment out a canary.
        string_bypass = (
            'def label : String := "/-"\n'
            'theorem positive_hidden : True := trivial\n'
            'def tail : String := "-/"\n'
        )
        self.assertIn(
            "positive declaration positive_hidden",
            find_forbidden_positive_checks(string_bypass, allowed_theorems=set()),
        )
        # 2. Nested block comments must be stripped cleanly without eating code.
        nested_comment = (
            "/- outer /- inner -/ still comment -/\n"
            "theorem positive_after_nested : True := trivial\n"
        )
        self.assertIn(
            "positive declaration positive_after_nested",
            find_forbidden_positive_checks(nested_comment, allowed_theorems=set()),
        )
        # 2b. `/-` inside a Lean quoted identifier `«...»` must not comment
        # out a canary.
        guillemet_bypass = (
            "def «/-» : Nat := 0\n"
            "theorem positive_hidden_guillemet : True := trivial\n"
            "def «-/» : Nat := 0\n"
        )
        self.assertIn(
            "positive declaration positive_hidden_guillemet",
            find_forbidden_positive_checks(
                guillemet_bypass, allowed_theorems=set()
            ),
        )
        # 2c. Inline block comments between tokens must preserve whitespace
        # separation so `theorem/- c -/foo` or `import/- c -/Mod` cannot hide.
        inline_comment_decl = "theorem/- marker -/canary_inline : True := trivial\n"
        self.assertIn(
            "uncataloged theorem canary_inline",
            find_forbidden_positive_checks(
                inline_comment_decl, allowed_theorems={"refute_something"}
            ),
        )
        # 3. A renamed standalone positive canary (including `public theorem`)
        # or anonymous `example` must still be rejected as uncataloged.
        renamed_canary = (
            "theorem canary_valid : pred = true := rfl\n"
            "public theorem canary_pub : pred = true := rfl\n"
            "example : pred = true := rfl\n"
        )
        renamed_issues = find_forbidden_positive_checks(
            renamed_canary, allowed_theorems={"refute_something"}
        )
        self.assertIn("uncataloged theorem canary_valid", renamed_issues)
        self.assertIn("uncataloged theorem canary_pub", renamed_issues)
        self.assertIn("uncataloged example", renamed_issues)
        # 3b. Proposition-valued, unannotated, or tactic-bearing helper defs
        # and unrelated `.allocId = N` conjuncts must be rejected.
        prop_val_helpers = (
            "def validCase : WellFormed validProg q := trivial\n"
            "def untypedProof := rfl\n"
            "def sneakyData : Nat := by exact 0\n"
            "def sneakyAscribe : Nat := (0 : Nat)\n"
        )
        prop_val_issues = find_forbidden_positive_checks(
            prop_val_helpers, allowed_theorems=set()
        )
        self.assertIn("disallowed non-data helper def validCase", prop_val_issues)
        self.assertIn(
            "disallowed non-data helper def untypedProof", prop_val_issues
        )
        self.assertIn(
            "disallowed non-data helper def sneakyData", prop_val_issues
        )
        self.assertIn(
            "disallowed non-data helper def sneakyAscribe", prop_val_issues
        )
        sneaky_alloc_id = (
            "theorem refute_sneaky_alloc :\n"
            "    readBytes m p 0 1 = .error .undefined ∧\n"
            "    (allocateStack validMem layout).2.allocId = 2 := ⟨rfl, rfl⟩\n"
        )
        self.assertIn(
            "embedded success expectation in refute_sneaky_alloc",
            find_forbidden_positive_checks(
                sneaky_alloc_id, allowed_theorems={"refute_sneaky_alloc"}
            ),
        )
        # 4. A cataloged `refute_*` theorem mixing a negative fault with a
        # positive `| .step _ => True`, `= .ok ...`, `.done (.returned ...)`,
        # or unpinned `.done (.aborted ...)` branch must be rejected.
        mixed_refute = (
            "theorem refute_mixed :\n"
            "    (match x with | .fault .undefined => True | _ => False) ∧\n"
            "    (match y with | .step _ => True | _ => False) := ⟨trivial, trivial⟩\n"
            "theorem refute_ok : f = .ok 1 := rfl\n"
            "theorem refute_done_ret :\n"
            "    (match z with | .done (.returned _) => True | _ => False) := trivial\n"
            "theorem refute_eq_done_ret : g = .done (.returned out) := rfl\n"
            "theorem refute_done_abort :\n"
            "    (match evalAssertFailure .boundsCheck .abort .unreachable\n"
            "        MemoryState.empty false with\n"
            "     | .done (.aborted _) => True | _ => False) := trivial\n"
            "theorem refute_unknown_head_abort :\n"
            "    (match a with | .done (.aborted _) => True | _ => False) := trivial\n"
            "def validHelper : Prop := f = .ok 1\n"
            "private abbrev validAbbrev : Prop :=\n"
            "    match y with | .step _ => True | _ => False\n"
            "def validIsOk : Prop := (f x).isOk = true\n"
            "def validCustomProp : Prop := x ≠ y\n"
        )
        mixed_issues = find_forbidden_positive_checks(
            mixed_refute,
            allowed_theorems={
                "refute_mixed",
                "refute_ok",
                "refute_done_ret",
                "refute_eq_done_ret",
                "refute_done_abort",
                "refute_unknown_head_abort",
            },
        )
        self.assertIn("embedded success expectation in refute_mixed", mixed_issues)
        self.assertIn("embedded success expectation in refute_ok", mixed_issues)
        self.assertIn(
            "embedded success expectation in refute_done_ret", mixed_issues
        )
        self.assertIn(
            "embedded success expectation in refute_eq_done_ret", mixed_issues
        )
        self.assertIn(
            "embedded success expectation in refute_done_abort", mixed_issues
        )
        self.assertIn(
            "embedded success expectation in refute_unknown_head_abort",
            mixed_issues,
        )
        self.assertIn(
            "embedded success expectation in def validHelper", mixed_issues
        )
        self.assertIn(
            "embedded success expectation in abbrev validAbbrev", mixed_issues
        )
        self.assertIn(
            "embedded success expectation in def validIsOk", mixed_issues
        )
        self.assertIn(
            "disallowed non-data helper def validCustomProp", mixed_issues
        )
        # 5. Command-wrapped declarations (`set_option ... in theorem ...`,
        # `open ... in example ...`) and complement-of-failure success checks
        # (`| .error _ => False | _ => True`, `| _ => 0 = 0`, `| x => True`,
        # `| _ | .error _ => True`, `f ≠ .fault .undefined`, `¬ (f = .error _)`)
        # must all be caught.
        wrapped_and_comp = (
            "set_option autoImplicit false in theorem positive_wrapped : "
            "pred = true := rfl\n"
            "open Foo in example : True := trivial\n"
            "theorem refute_comp_wild :\n"
            "    (match f with | .error _ => False | _ => True) := trivial\n"
            "theorem refute_comp_eq :\n"
            "    (match f with | .error _ => False | _ => 0 = 0) := rfl\n"
            "theorem refute_comp_var :\n"
            "    (match f with | .fault _ => False | ok => True) := trivial\n"
            "theorem refute_or_wild :\n"
            "    (match f with | _ | .error _ => True) := trivial\n"
            "theorem refute_ne_fault : f ≠ .fault .undefined := by decide\n"
            "theorem refute_not_err : ¬ (f = .error .oob) := by decide\n"
            "theorem refute_lhs_ok : (.ok 1 : Except Fault Nat) = op := rfl\n"
            "theorem refute_lhs_multiline :\n"
            "    (.ok 1\n"
            "      : Except Fault Nat)\n"
            "    = op := rfl\n"
            "theorem refute_rhs_paren : op = (.ok 1) := rfl\n"
            "theorem refute_rhs_qual : op = Except.ok 1 := rfl\n"
            "theorem refute_eq_app : Eq (StepOutcome.step s) op := rfl\n"
        )
        wrapped_issues = find_forbidden_positive_checks(
            wrapped_and_comp,
            allowed_theorems={
                "refute_comp_wild",
                "refute_comp_eq",
                "refute_comp_var",
                "refute_or_wild",
                "refute_ne_fault",
                "refute_not_err",
                "refute_lhs_ok",
                "refute_lhs_multiline",
                "refute_rhs_paren",
                "refute_rhs_qual",
                "refute_eq_app",
            },
        )
        self.assertIn("positive declaration positive_wrapped", wrapped_issues)
        self.assertIn("uncataloged theorem positive_wrapped", wrapped_issues)
        self.assertIn("uncataloged example", wrapped_issues)
        for thm in (
            "refute_comp_wild",
            "refute_comp_eq",
            "refute_comp_var",
            "refute_or_wild",
            "refute_ne_fault",
            "refute_not_err",
            "refute_lhs_ok",
            "refute_lhs_multiline",
            "refute_rhs_paren",
            "refute_rhs_qual",
            "refute_eq_app",
        ):
            self.assertIn(
                f"embedded success expectation in {thm}", wrapped_issues
            )
        # 6. Top-level `#guard` / `#eval` commands before the first declaration
        # (and any success expression in the preamble) must be rejected.
        preamble_guard = (
            "import PositiveSanity\n"
            "#guard (validOp 0).isOk\n"
            "theorem refute_ok_after : True := trivial\n"
        )
        preamble_issues = find_forbidden_positive_checks(
            preamble_guard, allowed_theorems={"refute_ok_after"}
        )
        self.assertIn("disallowed command #guard", preamble_issues)
        self.assertIn("embedded success expectation in preamble", preamble_issues)
        # 7. Unqualified success constructors (including after `open Except` /
        # `open StepOutcome` / `export` or bare `some`) must be rejected.
        unqualified_source = (
            "open Except\n"
            "export StepOutcome (step)\n"
            "theorem refute_unqual_ok : op = ok 1 := rfl\n"
            "theorem refute_unqual_step : op = step st := rfl\n"
            "theorem refute_unqual_ret : op = returned v := rfl\n"
            "theorem refute_unqual_inr : op = inr v := rfl\n"
            "theorem refute_unqual_some_rhs : op = some 1 := rfl\n"
            "theorem refute_unqual_some_lhs : some 1 = op := rfl\n"
            "theorem refute_unqual_some_eq : Eq (some 1) op := rfl\n"
        )
        unqual_issues = find_forbidden_positive_checks(
            unqualified_source,
            allowed_theorems={
                "refute_unqual_ok",
                "refute_unqual_step",
                "refute_unqual_ret",
                "refute_unqual_inr",
                "refute_unqual_some_rhs",
                "refute_unqual_some_lhs",
                "refute_unqual_some_eq",
            },
        )
        self.assertIn("disallowed open directive: open Except", unqual_issues)
        self.assertIn("disallowed export directive", unqual_issues)
        for thm in (
            "refute_unqual_ok",
            "refute_unqual_step",
            "refute_unqual_ret",
            "refute_unqual_inr",
            "refute_unqual_some_rhs",
            "refute_unqual_some_lhs",
            "refute_unqual_some_eq",
        ):
            self.assertIn(
                f"embedded success expectation in {thm}", unqual_issues
            )
        # 8. Extending any pinned refutation theorem (evaluation-order or
        # allocation-ID freshness) with an extra assertion must be rejected.
        extended_pinned = (
            pinned_exact_refutations[
                "refute_step_v2_assign_resolves_destination_first"
            ].replace(":= trivial", "∧ validOp = .ok 1 := trivial")
            + "\n"
        )
        extended_issues = find_forbidden_positive_checks(
            extended_pinned,
            allowed_theorems={
                "refute_step_v2_assign_resolves_destination_first"
            },
        )
        self.assertIn(
            "allowlisted refute_step_v2_assign_resolves_destination_first "
            "drifted from pinned refutation assertion",
            extended_issues,
        )
        extended_fresh = (
            pinned_exact_refutations[
                "refute_mem_v2_entry_raw_ptr_arg_fresh"
            ].replace(":= rfl", "∧ (allocateStack validMem l).2.allocId = 2 := rfl")
            + "\n"
        )
        self.assertIn(
            "allowlisted refute_mem_v2_entry_raw_ptr_arg_fresh "
            "drifted from pinned refutation assertion",
            find_forbidden_positive_checks(
                extended_fresh,
                allowed_theorems={"refute_mem_v2_entry_raw_ptr_arg_fresh"},
            ),
        )
        # 9. Boolean-success equalities (`= true`, `true =`, `Eq true ...`,
        # `Bool.true`) and negated-`false` checks (`≠ false`, `¬ (p = false)`)
        # must be rejected.
        bool_success_source = (
            "theorem refute_bool_rhs : isSupportedV2LocalTy ty = true := rfl\n"
            "theorem refute_bool_qual : isSupportedV2LocalTy ty = Bool.true := rfl\n"
            "theorem refute_bool_lhs : true = isSupportedV2LocalTy ty := rfl\n"
            "theorem refute_bool_eq : Eq true (isSupportedV2LocalTy ty) := rfl\n"
            "theorem refute_bool_ne : isSupportedV2LocalTy ty ≠ false := by decide\n"
            "theorem refute_bool_not : ¬ (isSupportedV2LocalTy ty = false) := by decide\n"
        )
        bool_issues = find_forbidden_positive_checks(
            bool_success_source,
            allowed_theorems={
                "refute_bool_rhs",
                "refute_bool_qual",
                "refute_bool_lhs",
                "refute_bool_eq",
                "refute_bool_ne",
                "refute_bool_not",
            },
        )
        for thm in (
            "refute_bool_rhs",
            "refute_bool_qual",
            "refute_bool_lhs",
            "refute_bool_eq",
            "refute_bool_ne",
            "refute_bool_not",
        ):
            self.assertIn(
                f"embedded success expectation in {thm}", bool_issues
            )
        # 10. Zero-hash raw strings ending in `\` (`r"\"`) must not swallow
        # following declarations, and `Not (...)` / `... → False` failure
        # complements must be rejected just like `¬ (...)`.
        raw_and_not_source = (
            'def raw_bs : String := r"\\"\n'
            "theorem positive_after_raw_bs : True := trivial\n"
            'def tail_quote : String := ""\n'
            "theorem refute_not_word_err : Not (validOp = .error .undefined) := by decide\n"
            "theorem refute_not_word_false : Not (pred ty = false) := by decide\n"
            "theorem refute_imp_false : (validOp = .error .undefined) → False := by decide\n"
        )
        raw_not_issues = find_forbidden_positive_checks(
            raw_and_not_source,
            allowed_theorems={
                "refute_not_word_err",
                "refute_not_word_false",
                "refute_imp_false",
            },
        )
        self.assertIn("positive declaration positive_after_raw_bs", raw_not_issues)
        for thm in (
            "refute_not_word_err",
            "refute_not_word_false",
            "refute_imp_false",
        ):
            self.assertIn(
                f"embedded success expectation in {thm}", raw_not_issues
            )
        # 11. Outcome recursors/eliminators (`Except.rec`, `casesOn`, `elim`,
        # `toBool`, `ite`) and `fun _ => True` outside `¬ BodyVerified` must
        # be rejected.
        recursor_source = (
            "theorem refute_except_rec : "
            "Except.rec (motive := fun _ => Prop) (fun _ => False) "
            "(fun _ => True) (validOp 0) := trivial\n"
            "theorem refute_step_cases_on : "
            "StepOutcome.casesOn (validStep 0) (fun _ => True) (fun _ => False) := trivial\n"
            "theorem refute_opt_elim : Option.elim (validOpt 0) False (fun _ => True) := trivial\n"
            "theorem refute_to_bool : (validOp 0).toBool = false := rfl\n"
        )
        rec_issues = find_forbidden_positive_checks(
            recursor_source,
            allowed_theorems={
                "refute_except_rec",
                "refute_step_cases_on",
                "refute_opt_elim",
                "refute_to_bool",
            },
        )
        for thm in (
            "refute_except_rec",
            "refute_step_cases_on",
            "refute_opt_elim",
            "refute_to_bool",
        ):
            self.assertIn(f"embedded success expectation in {thm}", rec_issues)
        # 12. Monadic `pure` / `do return` constructions and any non-negative
        # theorem type (even via an unknown constructor name or bare `True`)
        # must be rejected by the structural refutation-type allowlist.
        monadic_source = (
            "theorem refute_pure_eq : validOp = (pure 1 : Except Fault Nat) := rfl\n"
            "theorem refute_do_return : validOp = (do return 1) := rfl\n"
            "theorem refute_custom_ctor : validOp = customOk 1 := rfl\n"
            "theorem refute_tautology : True := trivial\n"
        )
        monadic_issues = find_forbidden_positive_checks(
            monadic_source,
            allowed_theorems={
                "refute_pure_eq",
                "refute_do_return",
                "refute_custom_ctor",
                "refute_tautology",
            },
        )
        for thm in (
            "refute_pure_eq",
            "refute_do_return",
            "refute_custom_ctor",
            "refute_tautology",
        ):
            self.assertIn(
                f"embedded success expectation in {thm}", monadic_issues
            )
        # 13. Setup-arm masking must reject `let` bindings and conjunctions
        # inside `.ok`/`.step` arms, and proof-local assertions (`have`,
        # `show`, `let`, bare type ascriptions) must be rejected even when
        # the outer theorem type is a valid negative refutation.
        setup_and_proof_source = (
            "theorem refute_setup_let_true : "
            "(match validOp 0 with | .ok x => let _ := x; True | .error _ => False) := trivial\n"
            "theorem refute_setup_let_eq : "
            "(match validOp 0 with | .ok x => let y := x; y = 42 | .error _ => False) := rfl\n"
            "theorem refute_setup_step_let : "
            "(match evalStatementV2 b f m c s with | .step s' => let _ := s'; True | _ => False) := trivial\n"
            "theorem refute_setup_conj : "
            "(match validOp 0 with | .ok x => x = 42 ∧ badOp 0 = .error .undefined | .error _ => False) := ⟨rfl, rfl⟩\n"
            "theorem refute_proof_have_wf : badOp 0 = .error .undefined := by\n"
            "  have h : WellFormed validProg queryEmpty := sorry\n"
            "  exact rfl\n"
            "theorem refute_proof_have_untyped : badOp 0 = .error .undefined := by\n"
            "  have := positive_canary\n"
            "  exact rfl\n"
            "theorem refute_proof_show : badOp 0 = .error .undefined := by\n"
            "  have _ := (show validOp 0 = customOk 1 from rfl)\n"
            "  exact rfl\n"
            "theorem refute_proof_let : badOp 0 = .error .undefined :=\n"
            "  let _ : validOp 0 = customOk 1 := rfl\n"
            "  rfl\n"
            "theorem refute_proof_ascribe : badOp 0 = .error .undefined :=\n"
            "  ((fun _ => rfl) (rfl : validOp 0 = customOk 1))\n"
        )
        sp_issues = find_forbidden_positive_checks(
            setup_and_proof_source,
            allowed_theorems={
                "refute_setup_let_true",
                "refute_setup_let_eq",
                "refute_setup_step_let",
                "refute_setup_conj",
                "refute_proof_have_wf",
                "refute_proof_have_untyped",
                "refute_proof_show",
                "refute_proof_let",
                "refute_proof_ascribe",
            },
        )
        for thm in (
            "refute_setup_let_true",
            "refute_setup_let_eq",
            "refute_setup_step_let",
            "refute_setup_conj",
            "refute_proof_have_wf",
            "refute_proof_have_untyped",
            "refute_proof_show",
            "refute_proof_let",
            "refute_proof_ascribe",
        ):
            self.assertIn(f"embedded success expectation in {thm}", sp_issues)
        # 14. Auxiliary proposition arguments in proofs (`@And.right ...`),
        # non-hash elaborator commands (`run_cmd`, `initialize`, `elab`),
        # trailing top-level connectives on negated predicates
        # (`¬ WellFormed badProg q → Diverges validProg q`), and unvalidated
        # theorem-type `let` bindings or parameter binders before `:` must all
        # be rejected.
        closed_grammar_source = (
            "run_cmd pure ()\n"
            "initialize pure ()\n"
            "theorem refute_and_right : badOp 0 = .error .undefined := by\n"
            "  exact @And.right ((entryMemoryWithCaller cm).nextAllocId = 6) _ ⟨rfl, rfl⟩\n"
            "theorem refute_neg_imp :\n"
            "    ¬ WellFormed badProg q → Diverges validProg q := rfl\n"
            "theorem refute_neg_or :\n"
            "    ¬ WellFormed badProg q ∨ WellFormed validProg q := rfl\n"
            "theorem refute_type_let_eq :\n"
            "    let _ : (allocateStack validMem ⟨1, 0⟩).2.allocId = 2 := rfl;\n"
            "    readBytes m p 0 1 = .error .undefined := rfl\n"
            "theorem refute_type_let_wf :\n"
            "    let _ : WellFormed validProg queryEmpty := positive_proof;\n"
            "    readBytes m p 0 1 = .error .undefined := rfl\n"
            "theorem refute_type_let_untyped :\n"
            "    let _ := positive_proof;\n"
            "    readBytes m p 0 1 = .error .undefined := rfl\n"
            "theorem refute_default_binder (_ : validOp 0 = customOk 1 := rfl) :\n"
            "    badOp 0 = .error .undefined := rfl\n"
            "theorem refute_if_gate :\n"
            "    (if tyHasRawPtrV2 (.option (.rawPtr .shared (.int .i8 false)))\n"
            "     then readBytes bad m 0 1 else readBytes valid m 0 1)\n"
            "      = .error .undefined := rfl\n"
            "theorem refute_nested_let_rhs :\n"
            "    badOp 0 = .error (let _ : WellFormed validProg queryEmpty := rfl; .undefined) := rfl\n"
            "theorem refute_nested_let_lhs :\n"
            "    (let _ : WellFormed validProg queryEmpty := rfl; badOp 0) = .error .undefined := rfl\n"
            "theorem refute_by_elab :\n"
            "    (by_elab pure default) = .error .undefined := rfl\n"
            'theorem refute_interp_hidden :\n'
            '    ¬ WellFormed { identity := s!"{let _ : WellFormed validProg queryEmpty := rfl; 0}" } queryEmpty := rfl\n'
            "theorem refute_bang_false : !isSupportedV2LocalTy validTy = false := rfl\n"
            "theorem refute_bool_not_false : Bool.not (isSupportedV2LocalTy validTy) = false := rfl\n"
            "theorem refute_eq_nested_match :\n"
            "    (match tyHasRawPtrV2 optTy with | true => badOp | false => okOp) = .error .undefined := rfl\n"
            "theorem refute_pred_nested_match :\n"
            "    ¬ WellFormed (match validPred with | true => badProg | false => okProg) queryEmpty := rfl\n"
            "theorem refute_scrutinee_nested_match :\n"
            "    (match (match validPred with | true => badOp | false => okOp) with | .error _ => True | _ => False) := trivial\n"
            "def sneakyMatchHelper : Nat := match n with | 0 => 0 | 1 => 1\n"
        )
        cg_issues = find_forbidden_positive_checks(
            closed_grammar_source,
            allowed_theorems={
                "refute_and_right",
                "refute_neg_imp",
                "refute_neg_or",
                "refute_type_let_eq",
                "refute_type_let_wf",
                "refute_type_let_untyped",
                "refute_default_binder",
                "refute_if_gate",
                "refute_nested_let_rhs",
                "refute_nested_let_lhs",
                "refute_by_elab",
                "refute_interp_hidden",
                "refute_bang_false",
                "refute_bool_not_false",
                "refute_eq_nested_match",
                "refute_pred_nested_match",
                "refute_scrutinee_nested_match",
            },
        )
        self.assertIn("disallowed elaborator command run_cmd", cg_issues)
        self.assertIn("disallowed elaborator command initialize", cg_issues)
        self.assertIn("disallowed elaborator command by_elab", cg_issues)
        self.assertIn("disallowed preamble statement: run_cmd pure ()", cg_issues)
        self.assertIn("disallowed non-data helper def sneakyMatchHelper", cg_issues)
        for thm in (
            "refute_and_right",
            "refute_neg_imp",
            "refute_neg_or",
            "refute_type_let_eq",
            "refute_type_let_wf",
            "refute_type_let_untyped",
            "refute_default_binder",
            "refute_if_gate",
            "refute_nested_let_rhs",
            "refute_nested_let_lhs",
            "refute_by_elab",
            "refute_interp_hidden",
            "refute_bang_false",
            "refute_bool_not_false",
            "refute_eq_nested_match",
            "refute_pred_nested_match",
            "refute_scrutinee_nested_match",
        ):
            self.assertIn(f"embedded success expectation in {thm}", cg_issues)
        # 15. Local binders and pure-data helper declarations/parameters must
        # reject built-in constructors, keywords, and semantic predicates
        # (including normalized French quotes such as `«false»`), so
        # `let false : Bool := true` cannot shadow `Bool.false` in `= false` or
        # `| false => True` arms.
        shadow_binder_source = (
            "theorem refute_let_false : "
            "let false : Bool := true; validUtf8Bytes [0x41] = false := rfl\n"
            "def false : Bool := true\n"
            "theorem refute_def_false : validUtf8Bytes [0x41] = false := rfl\n"
            "theorem refute_guillemet_false : "
            "let «false» : Bool := true; validUtf8Bytes [0x41] = false := rfl\n"
            "theorem refute_match_let_false : "
            "let false : Bool := true; "
            "match validUtf8Bytes [0x41] with | false => True | _ => False := rfl\n"
            "theorem refute_let_none : "
            "let none : Bool := true; validUtf8Bytes [0x41] = none := rfl\n"
            "def hBad (false : Nat) : Nat := false\n"
            "theorem refute_fun_false : ¬ BodyVerified badProg queryEmpty := "
            "(fun false => by exact rfl)\n"
            "theorem refute_have_false : badOp 0 = .error .undefined := by\n"
            "  have false : ReachesResultV2 badProg s (.fault .undefined) := rfl\n"
            "  exact false\n"
        )
        shadow_issues = find_forbidden_positive_checks(
            shadow_binder_source,
            allowed_theorems={
                "refute_let_false",
                "refute_def_false",
                "refute_guillemet_false",
                "refute_match_let_false",
                "refute_let_none",
                "refute_fun_false",
                "refute_have_false",
            },
        )
        self.assertIn("disallowed non-data helper def false", shadow_issues)
        self.assertIn("disallowed non-data helper def hBad", shadow_issues)
        for thm in (
            "refute_let_false",
            "refute_guillemet_false",
            "refute_match_let_false",
            "refute_let_none",
            "refute_fun_false",
            "refute_have_false",
        ):
            self.assertIn(f"embedded success expectation in {thm}", shadow_issues)
        # 16. Imported sanity modules must not declare identifiers or
        # directives that shadow allowlisted refutation head functions or
        # built-in constructors (e.g. `GuardMutation.readBytes` or
        # `evalStepV2`).
        with tempfile.TemporaryDirectory() as tmp_imp:
            imp_dir = Path(tmp_imp)
            (imp_dir / "PositiveSanity.lean").write_text(
                "namespace GuardMutation\n"
                "def readBytes (x : Nat) : Option (List UInt8) := some []\n"
                "def GuardMutation.evalStepV2 : Nat := 0\n"
                "def «ptrAddInMem» : Nat := 0\n"
                "theorem true : True := trivial\n"
                "macro \"badMacro\" : command => `(theorem bad : True := trivial)\n"
                "namespace ShadowNs\n"
                "end ShadowNs\n",
                encoding="utf-8",
            )
            _, _, imp_shadow_issues = check_guard_mutation._collect_imported_module_info(
                imp_dir, {"PositiveSanity"}
            )
        joined_imp = "\n".join(imp_shadow_issues)
        self.assertIn("disallowed shadowing declaration def readBytes", joined_imp)
        self.assertIn("disallowed shadowing declaration def evalStepV2", joined_imp)
        self.assertIn("disallowed shadowing declaration def ptrAddInMem", joined_imp)
        self.assertIn("disallowed shadowing declaration theorem true", joined_imp)
        self.assertIn("disallowed elaborator command macro", joined_imp)
        self.assertIn("disallowed namespace directive: namespace ShadowNs", joined_imp)

        # Regression check: importing another refutation fixture (inline,
        # block-comment-separated, multiline, or guillemet-quoted) is
        # unrebuilt and must fail the allowed-local-imports check.
        step_guard = next(
            g for g in guards if g.fixture_module == "StepRefutations"
        )
        bad_imports = collect_local_imports(
            step_guard.fixture_module,
            overrides={
                step_guard.fixture_module: (
                    "import GuardRefuteWf\n"
                    "import PositiveSanity\n"
                    "import/- marker -/ProfileV2Refutations\n"
                    "public\n"
                    "import\n"
                    "  all\n"
                    "  BoundaryRefutations\n"
                    "import «MemoryRefutations»\n"
                )
            },
        )
        self.assertIn(
            "ProfileV2Refutations",
            bad_imports - allowed_local_imports(step_guard),
        )
        self.assertIn(
            "BoundaryRefutations",
            bad_imports - allowed_local_imports(step_guard),
        )
        self.assertIn(
            "MemoryRefutations",
            bad_imports - allowed_local_imports(step_guard),
        )

        # The check above must see every canary moved by this commit.
        positive_text = strip_lean_comments_and_strings(
            (fixture_dir / "PositiveSanity.lean").read_text(encoding="utf-8")
        )
        memory_text = strip_lean_comments_and_strings(
            (fixture_dir / "MemorySanity.lean").read_text(encoding="utf-8")
        )
        positive_found = [
            (m.group(2) or "").strip("«»")
            for m in decl_re.finditer(positive_text)
            if m.group(1) in ("theorem", "lemma")
            and (m.group(2) or "").strip("«»").startswith("positive")
        ]
        memory_found = [
            (m.group(2) or "").strip("«»")
            for m in decl_re.finditer(memory_text)
            if m.group(1) in ("theorem", "lemma")
            and (m.group(2) or "").strip("«»").startswith("positive")
        ]
        for name in (
            "positive_boundary_v2_admits_valid_fake_ptr_metadata",
            "positive_bytes_utf8_valid_boundaries",
            "positive_bytes_v2_array_elem_layout_one_level",
            "positive_bytes_v2_slice_empty_never_and_zst_unit",
            "positive_core_contracts_i128_in_bounds",
            "positive_core_contracts_option_unwrap_live_ref",
            "positive_core_contracts_slice_shared_input",
            "positive_enum_v2_overflow_pair_local",
            "positive_enum_v2_vec_box_slice_scalar_elems",
            "positive_pinned_setup_prefixes",
            "positive_step_assert_checked_overflow_aborts",
            "positive_step_v2_assign_aggregate_deref_ptr_before_overwrite",
            "positive_step_v2_assign_aggregate_non_clobbering",
            "positive_step_v2_assign_repeat_disjoint",
            "positive_step_v2_assign_use_non_overlapping_and_scalar_pairs",
            "positive_step_v2_get_unchecked_shared_input",
            "positive_step_v2_option_discriminant_isize_dst",
            "positive_step_v2_overflow_assert_passes",
            "positive_step_v2_partial_tuple_moves",
            "positive_step_v2_ptr_cast_keeps_or_drops_mut",
            "positive_step_v2_ptr_metadata_str_usize",
            "positive_step_v2_raw_borrow_const_through_const",
            "positive_step_v2_update_val_at_proj_ranges",
            "positive_step_v2_zst_enum_no_provenance_deref",
            "positive_step_v2_zst_raw_ptr_write_and_read",
        ):
            self.assertIn(name, positive_found)
        for name in (
            "positive_mem_v2_entry_non_raw_ptr_arg_unchanged",
            "positive_mem_v2_entry_option_none_zero",
            "positive_mem_v2_slice_get_unchecked_elem_size_in_bounds",
            "positive_zst_alignment_only_canaries",
        ):
            self.assertIn(name, memory_found)
        # Baseline-only exact value check must remain wired and assert the
        # exact scaled pointer offset for `elemSize = 4, startOff = 1`.
        self.assertIn(
            "MemoryBaselineExact",
            check_guard_mutation.BASELINE_ONLY_MEMORY_FIXTURES,
        )
        baseline_exact_text = strip_lean_comments_and_strings(
            (fixture_dir / "MemoryBaselineExact.lean").read_text(
                encoding="utf-8"
            )
        )
        self.assertIn(
            "baseline_mem_v2_slice_get_unchecked_elem_size_exact",
            baseline_exact_text,
        )
        self.assertIn(".ok (.slicePtr ⟨some 1, 4, .isize⟩ 0)", baseline_exact_text)

    def test_semantics_downstream_covers_transitive_importers(self):
        # Verify that for every `target_module` in `SEMANTICS_DOWNSTREAM` whose
        # guards compile against `Boundary`-importing fixtures (i.e. anything
        # outside the isolated `Memory` fast path), `SEMANTICS_DOWNSTREAM`
        # includes every transitive importer in `Trusted/MirSemantics/*.lean`
        # in topological order so no stale `.olean` survives a mutant rebuild.
        sem_dir = ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics"
        sem_index = {
            mod: idx
            for idx, mod in enumerate(check_guard_mutation.SEMANTICS_MODULES)
        }
        direct_importers: dict[str, set[str]] = {}
        for lean_file in sorted(sem_dir.glob("*.lean")):
            mod = f"Trusted/MirSemantics/{lean_file.stem}"
            if mod not in sem_index:
                continue
            for line in lean_file.read_text(encoding="utf-8").splitlines():
                stripped = line.strip()
                if stripped.startswith(("import ", "public import ")):
                    imp = stripped.split()[-1].replace(".", "/")
                    if imp in sem_index:
                        direct_importers.setdefault(imp, set()).add(mod)

        def transitive_importers(root: str) -> set[str]:
            seen = {root}
            stack = [root]
            while stack:
                cur = stack.pop()
                for nxt in direct_importers.get(cur, ()):
                    if nxt not in seen:
                        seen.add(nxt)
                        stack.append(nxt)
            return seen

        fixture_dir = ANNEAL_ROOT / "ci/fixtures/guard_mutation"

        def fixture_semantics_imports(root_mod: str) -> set[str]:
            """Return all `Trusted/MirSemantics/*` modules reachable from a
            fixture module, following helper imports in `fixture_dir`."""
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
            # `Memory` intentionally uses isolated `Memory`-only fixtures and
            # `MemorySanity` without rebuilding downstream modules; verify that
            # every `Memory` guard obeys that contract transitively.
            if mod == "Trusted/MirSemantics/Memory":
                allowed = set(rebuild_list)
                self.assertEqual(allowed, {"Trusted/MirSemantics/Memory"})
                mem_guards = [
                    g
                    for g in check_guard_mutation.MIR_SEMANTICS_GUARDS
                    if g.target_module == mod
                ]
                self.assertTrue(mem_guards, "expected at least one Memory guard")
                for g in mem_guards:
                    self.assertFalse(
                        g.needs_wf_helper,
                        f"{g.guard_id} sets needs_wf_helper=True on isolated "
                        f"Memory fast path",
                    )
                    for role, mod_name in (
                        ("fixture_module", g.fixture_module),
                        ("sanity_module", g.sanity_module),
                    ):
                        reached = fixture_semantics_imports(mod_name)
                        self.assertTrue(
                            reached <= allowed,
                            f"{g.guard_id} {role} {mod_name!r} imports "
                            f"non-Memory semantics modules "
                            f"{sorted(reached - allowed)} while "
                            f"SEMANTICS_DOWNSTREAM[{mod!r}] only rebuilds "
                            f"{sorted(allowed)}",
                        )
                continue
            expected = transitive_importers(mod)
            actual = set(rebuild_list)
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

    def test_validate_refutation_modules_rejects_recursors_and_lambdas_in_predicates(
        self,
    ):
        allowed = {"refute_demo"}
        cases = (
            (
                "Decidable.casesOn + @ + fun in negated WellFormed",
                """\
                prelude
                import Trusted.MirSemantics.Boundary
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    ¬ WellFormed (@Decidable.casesOn P (fun _ => Program) inst (fun _ => goodProg) (fun _ => badProg)) queryEmpty :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "Or.elim in negated WellFormed",
                """\
                prelude
                import Trusted.MirSemantics.Boundary
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    ¬ WellFormed (Or.elim h (fun _ => goodProg) (fun _ => badProg)) queryEmpty :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "Classical.choose in negated WellFormed",
                """\
                prelude
                import Trusted.MirSemantics.Boundary
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    ¬ WellFormed (Classical.choose h) queryEmpty :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "non-canonical lambda in negated BodyVerified",
                """\
                prelude
                import Trusted.MirSemantics.Boundary
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    ¬ BodyVerified badProg 0 badBody (fun x => validCheck x) :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "qualified recursor in pure-data helper",
                """\
                prelude
                import Trusted.MirSemantics.Boundary
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                noncomputable def sneakyRecHelper : Nat :=
                  Nat.casesOn n 0 (fun _ => 1)
                theorem refute_demo :
                    ¬ WellFormed badProg queryEmpty :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "postfix Bool.toNat gate in negative equality",
                """\
                prelude
                import Trusted.MirSemantics.Memory
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    readBytes mem 1 0 (isSupportedV2LocalTy validTy).toNat = .error .undefined :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "qualified Bool.toUInt8 gate in negative equality",
                """\
                prelude
                import Trusted.MirSemantics.Memory
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    readBytes mem 1 0 (Bool.toUInt8 (isSupportedV2LocalTy validTy)) = .error .undefined :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "Option.get proof-requiring projection via dot notation",
                """\
                prelude
                import Trusted.MirSemantics.Memory
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    readBytes mem (validOp.get rfl) 0 4 = .error .undefined :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "qualified Option.get proof-requiring projection",
                """\
                prelude
                import Trusted.MirSemantics.Memory
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    readBytes mem (Option.get validOp rfl) 0 4 = .error .undefined :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "bracket indexing GetElem in data argument",
                """\
                prelude
                import Trusted.MirSemantics.Memory
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    readBytes mem xs[0] 0 4 = .error .undefined :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "qualified Trusted.MirSemantics conditional evaluator + nested predicate",
                """\
                prelude
                import Trusted.MirSemantics.Step
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    Trusted.MirSemantics.evalBoolSwitchBranches
                      (Trusted.MirSemantics.isSupportedV2LocalTy u32Ty)
                      0 [(0, 1), (2, 2)] = .error .undefined :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "unqualified open MirSemantics conditional evaluator + nested predicate",
                """\
                prelude
                import Trusted.MirSemantics.Step
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    evalBoolSwitchBranches
                      (isSupportedV2LocalTy u32Ty)
                      0 [(0, 1), (2, 2)] = .error .undefined :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "nested MirSemantics predicate inside allowlisted head call args",
                """\
                prelude
                import Trusted.MirSemantics.Step
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    readBytes emptyMemory 1 0 (isSupportedV2LocalTy u32Ty) = .error .undefined :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "unallowlisted Unicode identifier in data argument",
                """\
                prelude
                import Trusted.MirSemantics.Bytes
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    validUtf8Bytes δ = false :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "French-quoted Unicode identifier in data argument",
                """\
                prelude
                import Trusted.MirSemantics.Bytes
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    validUtf8Bytes «δ» = false :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "French-quoted spaced identifier in data argument",
                """\
                prelude
                import Trusted.MirSemantics.Bytes
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    validUtf8Bytes «a b» = false :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "qualified Unicode identifier in data argument",
                """\
                prelude
                import Trusted.MirSemantics.Bytes
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    validUtf8Bytes foo.δ = false :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "unallowlisted Unicode identifier in negation proof term",
                """\
                prelude
                import Trusted.MirSemantics.Step
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    ¬ BodyVerified emptyMemory :=
                  fun h => δ
                end GuardMutation
                """,
            ),
            (
                "unpinned .ok setup success gate inside refutation theorem",
                """\
                prelude
                import Trusted.MirSemantics.Step
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    (match initState progIndirectUninitRead queryEmpty with
                     | .ok s0 => evalStep progIndirectUninitRead 0 s0 = .fault .undefined
                     | .error _ => False) :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "same-line second theorem after target theorem",
                """\
                prelude
                import Trusted.MirSemantics.Bytes
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo : validUtf8Bytes [0xFF] = false := rfl theorem refute_other : validUtf8Bytes [0x80] = false := rfl
                end GuardMutation
                """,
            ),
            (
                "unpinned .done (.aborted ...) equality in refutation theorem",
                """\
                prelude
                import Trusted.MirSemantics.Step
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    evalCorePanicAbort .abort .unreachable queryEmpty.callerMem false = .done (.aborted queryEmpty.callerMem) :=
                  rfl
                end GuardMutation
                """,
            ),
            (
                "unpinned .done (.aborted _) => True arm in refutation theorem",
                """\
                prelude
                import Trusted.MirSemantics.Step
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    (match evalCorePanicAbort .abort .unreachable queryEmpty.callerMem false with
                     | .done (.aborted _) => True
                     | _ => False) :=
                  trivial
                end GuardMutation
                """,
            ),
            (
                "spaceless default-value binder before colon on refutation theorem",
                """\
                prelude
                import Trusted.MirSemantics.Bytes
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo(_:validUtf8Bytes [0x41]=true:=rfl): validUtf8Bytes [0xFF] = false := rfl
                end GuardMutation
                """,
            ),
            (
                "spaceless implicit binder before colon on refutation theorem",
                """\
                prelude
                import Trusted.MirSemantics.Bytes
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo{x:Nat}: validUtf8Bytes [0xFF] = false := rfl
                end GuardMutation
                """,
            ),
            (
                "spaceless universe binder before colon on refutation theorem",
                """\
                prelude
                import Trusted.MirSemantics.Bytes
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo.{u}: validUtf8Bytes [0xFF] = false := rfl
                end GuardMutation
                """,
            ),
            (
                "mid-line second theorem on final line of multi-line theorem",
                """\
                prelude
                import Trusted.MirSemantics.Bytes
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    validUtf8Bytes [0xFF] = false
                  := rfl theorem refute_other : validUtf8Bytes [0x80] = false := rfl
                end GuardMutation
                """,
            ),
            (
                "unpinned .done (.aborted ...) arm with nested none/false fields",
                """\
                prelude
                import Trusted.MirSemantics.Step
                namespace GuardMutation
                open Trusted.MirAst Trusted.MirSemantics
                theorem refute_demo :
                    (match evalCorePanicAbort .abort .unreachable queryEmpty.callerMem false with
                     | .done (.aborted { allocations := [{ allocId := 2, alignLog2 := 0, mutability := .mut, bytes := [.init 0 none], live := false }] }) => True
                     | _ => False) :=
                  trivial
                end GuardMutation
                """,
            ),
        )
        for label, src in cases:
            with self.subTest(case=label):
                issues = check_guard_mutation.find_forbidden_positive_checks(
                    textwrap.dedent(src),
                    allowed_theorems=allowed | {"refute_other"},
                )
                self.assertTrue(
                    issues,
                    f"expected refutation validator to reject {label}",
                )
        # Same-line and mid-line declarations must fail closed in
        # find_theorem_line_span too.
        same_line_src = (
            "theorem refute_a : validUtf8Bytes [0xFF] = false := rfl "
            "theorem refute_b : validUtf8Bytes [0x80] = false := rfl\n"
        )
        with self.assertRaises(ValueError):
            check_guard_mutation.find_theorem_line_span(
                same_line_src, "refute_a"
            )
        with self.assertRaises(ValueError):
            check_guard_mutation.find_theorem_line_span(
                same_line_src, "refute_b"
            )
        mid_line_src = (
            "theorem refute_a :\n"
            "    validUtf8Bytes [0xFF] = false\n"
            "  := rfl theorem refute_b : validUtf8Bytes [0x80] = false := rfl\n"
        )
        with self.assertRaises(ValueError):
            check_guard_mutation.find_theorem_line_span(
                mid_line_src, "refute_a"
            )
        with self.assertRaises(ValueError):
            check_guard_mutation.find_theorem_line_span(
                mid_line_src, "refute_b"
            )


if __name__ == "__main__":
    unittest.main()
