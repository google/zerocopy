# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`check_minirust_pin.py` tests for the constructive axiom checks (`--check-
axioms`) and CI coverage."""

from __future__ import annotations

from .support import (
    ANNEAL_ROOT,
    check_minirust_pin,
    os,
    Path,
    populate_valid_repo,
    re,
    SCRIPT,
    subprocess,
    sys,
    tempfile,
    tomllib,
    write_fake_lean,
)


class AxiomsAndCiCases:
    """`CheckMiniRustPinTests` methods for the constructive axiom checks
    (`--check-axioms`) and CI coverage."""

    # ------------------------------------------------------------------
    # Constructive axiom check tests (`--check-axioms`)
    # ------------------------------------------------------------------

    def test_extract_exported_theorems_scopes_and_visibility(self) -> None:
        src = (
            "namespace Anneal.MiniRustProof\n"
            "structure S where\n"
            "  private field : Nat\n"
            "theorem thm_top : True := trivial\n"
            "private theorem thm_priv : True := trivial\n"
            "private @[simp] theorem thm_priv_attr : True := trivial\n"
            "@[simp] theorem thm_attr : True := trivial\n"
            "mutual\n"
            "theorem thm_mut : True := trivial\n"
            "end\n"
            "section Inner\n"
            "theorem thm_sec : True := trivial\n"
            "end Inner\n"
            "namespace Sub\n"
            "theorem thm_sub : True := trivial\n"
            "end Sub\n"
            "export Anneal.MiniRust.OracleCert (reexported_thm)\n"
            "end Anneal.MiniRustProof\n"
        )
        got = check_minirust_pin.extract_exported_theorems(src)
        self.assertEqual(
            got,
            [
                "Anneal.MiniRustProof.thm_top",
                "Anneal.MiniRustProof.thm_attr",
                "Anneal.MiniRustProof.thm_mut",
                "Anneal.MiniRustProof.thm_sec",
                "Anneal.MiniRustProof.Sub.thm_sub",
            ],
        )
        self.assertIn(
            "Anneal.MiniRustProof.reexported_thm",
            check_minirust_pin.extract_declared_symbols(src),
        )

    def test_resolve_lean_command_uses_direct_binary_without_wrappers(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            fake = write_fake_lean(Path(tmp) / "lean", "import sys; sys.exit(0)\n")
            self.assertEqual(
                check_minirust_pin._resolve_lean_command(fake), [str(fake)]
            )
            self.assertEqual(
                check_minirust_pin._resolve_lean_command(
                    "lean", path_env=str(tmp)
                ),
                [str(fake)],
            )
            with self.assertRaises(check_minirust_pin.VerificationError):
                check_minirust_pin._resolve_lean_command("lean", path_env="")

    def test_check_axioms_accepts_constructive_and_rejects_classical_or_sorry(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            root = tmp_path / "anneal"
            stage = tmp_path / "stage"
            stage.mkdir()
            populate_valid_repo(
                root,
                lean_files={"Syntax.lean": "def x := 1\n"},
                proof_lean=(
                    "namespace Anneal.MiniRustProof\n"
                    "theorem minirust_forward_sim_holds : True := trivial\n"
                    "theorem minirust_bi_fault_equiv_holds : 1 = 1 := rfl\n"
                    "end Anneal.MiniRustProof\n"
                ),
            )

            ok_lean = write_fake_lean(
                tmp_path / "lean_ok.py",
                """
import os, pathlib, sys
assert str(pathlib.Path(sys.argv[-1])).endswith("CheckMiniRustAxioms.lean")
assert os.environ.get("LEAN_PATH", ""), "LEAN_PATH must include stage-dir"
for secret_var in (
    "ACTIONS_CACHE_URL",
    "ACTIONS_RESULTS_URL",
    "ACTIONS_RUNTIME_TOKEN",
    "GITHUB_TOKEN",
    "GH_TOKEN",
):
    assert secret_var not in os.environ, f"leaked {secret_var}"
probe = pathlib.Path(sys.argv[-1]).read_text(encoding="utf-8")
assert "import Anneal.MiniRustProof" in probe
print("'Anneal.MiniRustProof.minirust_forward_sim_holds' depends on axioms: [propext,")
print(" Quot.sound]")
print("'Anneal.MiniRustProof.minirust_bi_fault_equiv_holds' does not depend on any axioms")
""",
            )
            env_with_secrets = os.environ.copy()
            env_with_secrets.update(
                {
                    "ACTIONS_CACHE_URL": "https://cache.example.invalid",
                    "ACTIONS_RESULTS_URL": "https://results.example.invalid",
                    "ACTIONS_RUNTIME_TOKEN": "mock-runtime-token",
                    "GITHUB_TOKEN": "mock-github-token",
                    "GH_TOKEN": "mock-gh-token",
                }
            )
            res_ok = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--repo-root",
                    str(root),
                    "--check-axioms",
                    "--lean",
                    str(ok_lean),
                    "--stage-dir",
                    str(stage),
                ],
                capture_output=True,
                text=True,
                env=env_with_secrets,
            )
            self.assertEqual(res_ok.returncode, 0, res_ok.stderr)
            self.assertIn("axioms: OK (2 exported theorems", res_ok.stdout)

            for bad_axiom in (
                "Classical.choice",
                "sorryAx",
                "Lean.ofReduceBool",
            ):
                with self.subTest(bad_axiom=bad_axiom):
                    bad_lean = write_fake_lean(
                        tmp_path / f"lean_bad_{bad_axiom}.py",
                        f"""
print("'Anneal.MiniRustProof.minirust_forward_sim_holds' depends on axioms: [propext, {bad_axiom}]")
print("'Anneal.MiniRustProof.minirust_bi_fault_equiv_holds' does not depend on any axioms")
""",
                    )
                    res_bad = self.run_cli(
                        "--repo-root",
                        str(root),
                        "--check-axioms",
                        "--lean",
                        str(bad_lean),
                        "--stage-dir",
                        str(stage),
                    )
                    self.assertNotEqual(res_bad.returncode, 0)
                    self.assertIn(bad_axiom, res_bad.stderr)

            missing_lean = write_fake_lean(
                tmp_path / "lean_missing.py",
                """
print("'Anneal.MiniRustProof.minirust_forward_sim_holds' does not depend on any axioms")
""",
            )
            res_missing = self.run_cli(
                "--repo-root",
                str(root),
                "--check-axioms",
                "--lean",
                str(missing_lean),
            )
            self.assertNotEqual(res_missing.returncode, 0)
            self.assertIn(
                "missing from `#print axioms` output", res_missing.stderr
            )

            # Bare `--lean` / `ANNEAL_LEAN` command names resolve via `PATH`
            # (not CWD) and fail closed when absent from `PATH`.
            bin_dir = tmp_path / "custom_bin"
            bin_dir.mkdir()
            write_fake_lean(
                bin_dir / "custom-lean-stub",
                """
p = "Anneal.MiniRustProof"
print(f"'{p}.minirust_forward_sim_holds' depends on axioms: [propext]")
print(f"'{p}.minirust_bi_fault_equiv_holds' does not depend on any axioms")
""",
            )
            path_env = {
                **os.environ,
                "PATH": f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}",
            }
            res_bare_flag = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--repo-root",
                    str(root),
                    "--check-axioms",
                    "--lean",
                    "custom-lean-stub",
                ],
                capture_output=True,
                text=True,
                env=path_env,
            )
            self.assertEqual(
                res_bare_flag.returncode, 0, res_bare_flag.stderr
            )
            res_bare_env = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(SCRIPT),
                    "--repo-root",
                    str(root),
                    "--check-axioms",
                ],
                capture_output=True,
                text=True,
                env={**path_env, "ANNEAL_LEAN": "custom-lean-stub"},
            )
            self.assertEqual(res_bare_env.returncode, 0, res_bare_env.stderr)
            res_bare_missing = self.run_cli(
                "--repo-root",
                str(root),
                "--check-axioms",
                "--lean",
                "nonexistent-lean-binary-xyz",
            )
            self.assertNotEqual(res_bare_missing.returncode, 0)

    def test_ci_core_checks_toml_and_codeowners_cover_minirust_pin(self) -> None:
        ws_root = ANNEAL_ROOT.parent
        checks_path = ws_root / "ci" / "checks.toml"
        codeowners_path = ws_root / ".github" / "CODEOWNERS"
        with checks_path.open("rb") as fh:
            checks_cfg = tomllib.load(fh)
        checks_by_id = {
            chk["id"]: chk
            for chk in checks_cfg.get("checks", [])
            if "id" in chk
        }
        self.assertIn("anneal-ci-tests", checks_by_id)
        ci_tests_includes = {
            pat
            for inp in checks_by_id["anneal-ci-tests"].get("inputs", [])
            if inp.get("kind") == "glob" and not inp.get("exclude")
            for pat in inp.get("include", [])
        }
        self.assertIn("anneal/vendor/minirust/**", ci_tests_includes)

        for check_id in (
            "anneal-flake-eval",
            "anneal-clippy",
            "anneal-sandbox-aarch64",
            "anneal-installed-smoke",
        ):
            with self.subTest(check_id=check_id):
                self.assertIn(check_id, checks_by_id)
                pin_includes = {
                    pat
                    for inp in checks_by_id[check_id].get("inputs", [])
                    if inp.get("kind") == "glob" and not inp.get("exclude")
                    for pat in inp.get("include", [])
                }
                self.assertIn(
                    "anneal/vendor/minirust/UPSTREAM_PIN.json", pin_includes
                )

        codeowners_lines = [
            ln.strip()
            for ln in codeowners_path.read_text(encoding="utf-8").splitlines()
            if ln.strip() and not ln.lstrip().startswith("#")
        ]
        for expected_rule in (
            "/anneal/correspondence/Anneal/MiniRust/ @joshlf @jswrenn @mdittmer",
            "/anneal/correspondence/Anneal/MiniRustProof.lean @joshlf @jswrenn @mdittmer",
            "/anneal/vendor/minirust/UPSTREAM_PIN.json @joshlf @jswrenn @mdittmer",
        ):
            self.assertIn(expected_rule, codeowners_lines)

    def test_tier0_ci_script_invokes_check_minirust_pin_on_checkout(
        self,
    ) -> None:
        script_text = (ANNEAL_ROOT / "ci" / "run_anneal_check.sh").read_text(
            encoding="utf-8"
        )
        ci_tests_match = re.search(
            r"^\s*ci-tests\)\n(.*?)^\s*;;\n",
            script_text,
            re.M | re.S,
        )
        self.assertIsNotNone(ci_tests_match)
        ci_tests_body = " ".join(
            ln.rstrip("\\").strip()
            for ln in ci_tests_match.group(1).splitlines()
        )
        self.assertIn(
            "./ci/check_minirust_pin.py "
            "--repo-root . --check-lean --check-anchors",
            ci_tests_body,
        )
