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


if __name__ == "__main__":
    unittest.main()
