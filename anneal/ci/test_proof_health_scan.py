# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `anneal/ci/proof_health_scan.py`."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import proof_health_scan


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=repo, check=True, capture_output=True, text=True
    ).stdout.strip()


def _init_repo(repo: Path) -> None:
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.name", "Test")
    _git(repo, "config", "user.email", "test@example.com")


def _write(repo: Path, rel: str, text: str) -> None:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _commit(repo: Path, msg: str) -> str:
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", msg)
    return _git(repo, "rev-parse", "HEAD")


def _request_json(spec_files: list[str]) -> str:
    sources = [
        {"module": f.removesuffix(".lean"), "path": f, "role": "specification"}
        for f in spec_files
    ]
    sources.append({"module": "Proof", "path": "Proof.lean", "role": "proof"})
    return json.dumps(
        {
            "schema_version": 1,
            "scope": {"kind": "selected_unit", "roots": ["a", "b"]},
            "proof": {
                "source_root": ".",
                "specification": "Spec.specs",
                "theorem": "Proof.verify",
                "sources": sources,
            },
        },
        indent=2,
    )


def _write_unit(repo: Path, unit: str) -> None:
    specs = ["Spec.lean", "Bounds.lean"] if unit == "01_u" else ["Spec.lean"]
    _write(repo, f"zerocopy/proofs/{unit}/request.json", _request_json(specs))
    _write(repo, f"zerocopy/proofs/{unit}/Spec.lean", "prelude\n-- s0\n")
    _write(repo, f"zerocopy/proofs/{unit}/Proof.lean", "prelude\n-- p0\n")


class ProofHealthScanTests(unittest.TestCase):
    def test_strip_nested_comments_and_strings_and_unused_private_scan(self):
        sample = (
            "-- top comment\n"
            "/- outer /- inner private theorem fake : True := rfl -/ still comment -/\n"
            "private theorem used_helper : True := True.intro\n"
            "private theorem dead_helper : True := True.intro\n"
            "theorem main_thm : True := by\n"
            "  have _s : String := \"dead_helper in string does not count\"\n"
            "  exact used_helper\n"
        )
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "Proof.lean"
            p.write_text(sample, encoding="utf-8")
            unused = proof_health_scan.find_unused_private_decls([p], Path(tmp))
            self.assertEqual(len(unused), 1)
            self.assertEqual(unused[0]["name"], "dead_helper")

    def test_scan_file_hygiene_catches_all_g4_anti_golf_violations(self):
        clean = (
            "prelude\n"
            "theorem ok_thm : True := by\n"
            "  have h : True := True.intro; exact h\n"
        )
        self.assertEqual(proof_health_scan.scan_file_hygiene(clean, "Proof.lean"), [])

        bad = (
            "prelude\n"
            + ("-- " + "x" * 105 + "\n")
            + "local macro \"golf\" : tactic => `(tactic| rfl)\n"
            + "theorem t1 : True := by simp [*]\n"
            + "theorem t2 : True := by simp_all\n"
            + "theorem t3 : True := by simp only [evalStep, Nat.add_zero]\n"
            + "theorem t3b : True := by simp (config := {}) only [writePlace]\n"
            + "theorem t4 : True := by intro; rfl; rfl; rfl\n"
        )
        violations = proof_health_scan.scan_file_hygiene(bad, "Proof.lean")
        rules = [v["rule"] for v in violations]
        self.assertGreaterEqual(rules.count("simp_only_evaluator"), 2)
        self.assertEqual(
            set(rules),
            {
                "max_columns",
                "forbidden_local_macro",
                "forbidden_simp_wildcard",
                "simp_only_evaluator",
                "excessive_semicolons",
            },
        )

    def test_profile_compiled_module_and_fail_soft_telemetry(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lean_root = root / "tc/lean"
            (lean_root / "bin").mkdir(parents=True)
            (lean_root / "lib/lean").mkdir(parents=True)
            fake_lean = lean_root / "bin/lean"
            fake_lean.write_text(
                "#!/usr/bin/env python3\n"
                "import json, pathlib, sys\n"
                "args = sys.argv[1:]\n"
                "if '--print-prefix' in args:\n"
                "    print(pathlib.Path(__file__).resolve().parent.parent)\n"
                "    sys.exit(0)\n"
                "if '--run' in args:\n"
                "    print(json.dumps({\n"
                "        'compiled_decl_count': 4,\n"
                "        'module_union_dag': 120,\n"
                "        'sum_val_dag': 80,\n"
                "        'sum_val_tree': 240,\n"
                "        'kernel_replay_runs_ms': [11.0, 10.5, 12.0],\n"
                "    }))\n"
                "    sys.exit(0)\n"
                "sys.exit(1)\n",
                encoding="utf-8",
            )
            fake_lean.chmod(0o700)
            lib_dir = root / "lean-lib"
            lib_dir.mkdir()
            (lib_dir / "Proof.olean").write_bytes(b"o" * 100)
            (lib_dir / "Proof.olean.private").write_bytes(b"p" * 50)
            prof = proof_health_scan.profile_compiled_module(
                fake_lean, [lib_dir], "Proof"
            )
            self.assertEqual(prof["proof_olean_bytes"], 150)
            self.assertEqual(prof["tree_to_dag_ratio"], 3.0)
            self.assertEqual(prof["kernel_replay_ms"], 11.0)

            bad_lean = lean_root / "bin/bad_lean"
            bad_lean.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
            bad_lean.chmod(0o700)
            repo = root / "repo"
            (repo / "anneal/theory").mkdir(parents=True)
            (repo / "anneal/correspondence").mkdir(parents=True)
            (repo / "zerocopy/proofs/01_u").mkdir(parents=True)
            (repo / "zerocopy/proofs/01_u/Proof.lean").write_text(
                "prelude\ntheorem verify : True := True.intro\n", encoding="utf-8"
            )
            tel = proof_health_scan.collect_proof_burden_telemetry(
                repo, lean_bin=bad_lean, lean_lib_dirs=[lib_dir]
            )
            self.assertEqual(
                tel["metrics"]["proof_burden.zerocopy_suite.hand_proof_loc"], 2
            )
            self.assertNotIn(
                "proof_burden.zerocopy_suite.proof_olean_bytes", tel["metrics"]
            )

    def test_d3_advisories_flag_long_theorems_and_tree_bombs(self):
        proof_stats = {
            "gt_20_theorems": [
                {"file": "zerocopy/proofs/01/Proof.lean", "line": 10, "name": "big", "nb_loc": 24}
            ]
        }
        theory_stats = {"gt_60_count": 3, "max_thm_loc": 140}
        kernel_prof = {
            "proof_olean_bytes": 34352,
            "tree_to_dag_ratio": 75.2,
            "kernel_replay_ms": 477.4,
        }
        adv = proof_health_scan.evaluate_d3_advisories(
            proof_stats,
            theory_stats=theory_stats,
            kernel_profile=kernel_prof,
        )
        kinds = {a["kind"] for a in adv}
        self.assertEqual(
            kinds,
            {
                "proof_thm_gt_20_nb",
                "theory_gt_60_heavy_tail",
                "expr_tree_to_dag_ratio_high",
            },
        )

    def test_char_literal_does_not_mask_following_violations(self):
        sample = (
            "prelude\n"
            "def q : Char := '\"'\n"
            "def esc : Char := '\\''\n"
            "def uni : Char := '\\u0022'\n"
            "def s : String := \"a'b\"\n"
            "private theorem dead_after_char : True := True.intro\n"
            "theorem bad_after_char : True := by\n"
            "  let x' := True.intro\n"
            "  exact x'\n"
            "theorem also_simp : True := by simp [*]\n"
        )
        violations = proof_health_scan.scan_file_hygiene(sample, "Proof.lean")
        rules = {v["rule"] for v in violations}
        self.assertIn("forbidden_simp_wildcard", rules)
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "Proof.lean"
            p.write_text(sample, encoding="utf-8")
            unused = proof_health_scan.find_unused_private_decls([p], Path(tmp))
            self.assertEqual([u["name"] for u in unused], ["dead_after_char"])

    def test_profile_compiled_modules_multi_module_and_minimal_env(self):
        self.assertNotIn("Environment.ofKernelEnv", proof_health_scan.PROFILER_LEAN_SRC)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lean_root = root / "tc/lean"
            (lean_root / "bin").mkdir(parents=True)
            (lean_root / "lib/lean").mkdir(parents=True)
            inv_log = root / "inv.json"
            fake_lean = lean_root / "bin/lean"
            fake_lean.write_text(
                "#!/usr/bin/env python3\n"
                "import json, os, pathlib, sys\n"
                "args = sys.argv[1:]\n"
                "if '--print-prefix' in args:\n"
                "    print(pathlib.Path(__file__).resolve().parent.parent)\n"
                "    sys.exit(0)\n"
                "if '--run' in args:\n"
                f"    pathlib.Path({str(inv_log)!r}).write_text(\n"
                "        json.dumps({'args': args, 'env': dict(os.environ)})\n"
                "    )\n"
                "    print(json.dumps({\n"
                "        'compiled_decl_count': 6,\n"
                "        'module_union_dag': 140,\n"
                "        'sum_val_dag': 90,\n"
                "        'sum_val_tree': 180,\n"
                "        'kernel_replay_runs_ms': [8.0, 9.0, 10.0],\n"
                "    }))\n"
                "    sys.exit(0)\n"
                "sys.exit(1)\n",
                encoding="utf-8",
            )
            fake_lean.chmod(0o700)
            repo = root / "repo"
            (repo / "anneal/theory").mkdir(parents=True)
            (repo / "anneal/correspondence").mkdir(parents=True)
            unit_src = repo / "zerocopy/proofs/01_u"
            unit_src.mkdir(parents=True)
            (unit_src / "AutoScaffold.lean").write_text("prelude\n", encoding="utf-8")
            (unit_src / "Proof.lean").write_text("prelude\n", encoding="utf-8")
            lib_dir = root / "out/01_u/lean-lib"
            lib_dir.mkdir(parents=True)
            (lib_dir / "AutoScaffold.olean").write_bytes(b"a" * 40)
            (lib_dir / "Proof.olean").write_bytes(b"p" * 60)

            with mock.patch.dict(os.environ, {"SECRET_AMBIENT_VAR": "must_not_leak"}):
                tel = proof_health_scan.collect_proof_burden_telemetry(
                    repo, lean_bin=fake_lean, lean_lib_dirs=[lib_dir]
                )
            self.assertEqual(
                tel["metrics"]["proof_burden.zerocopy_suite.proof_olean_bytes"], 100
            )
            logged = json.loads(inv_log.read_text(encoding="utf-8"))
            self.assertNotIn("SECRET_AMBIENT_VAR", logged["env"])
            self.assertEqual(logged["env"]["LEAN_SYSROOT"], str(lean_root.resolve()))
            self.assertIn("AutoScaffold,Proof", logged["args"])
            self.assertEqual(logged["args"][-1], str(lean_root.resolve()))

    def test_cli_fails_closed_without_base_ref_under_github_actions(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "repo"
            (repo / "zerocopy/proofs").mkdir(parents=True)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            with mock.patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}):
                with self.assertRaisesRegex(
                    proof_health_scan.HealthScanError, "no git base ref"
                ):
                    proof_health_scan.main(
                        ["--repo-root", str(repo), "--check-hygiene"]
                    )

    def test_cli_rejects_symlink_arguments_before_resolve(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            repo = root / "repo"
            (repo / "zerocopy/proofs").mkdir(parents=True)
            (repo / "anneal/theory").mkdir(parents=True)
            (repo / "anneal/correspondence").mkdir(parents=True)
            real_lean = root / "lean"
            real_lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            real_lean.chmod(0o700)
            lib_dir = root / "lib"
            lib_dir.mkdir()
            lean_file = repo / "zerocopy/proofs/Test.lean"
            lean_file.write_text("prelude\n", encoding="utf-8")

            sym_repo = root / "sym_repo"
            sym_repo.symlink_to(repo)
            sym_lib = root / "sym_lib"
            sym_lib.symlink_to(lib_dir)
            sym_path = root / "sym_test.lean"
            sym_path.symlink_to(lean_file)
            sym_out = root / "sym_out.json"
            sym_out.symlink_to(root / "target.json")

            cases = [
                ["--repo-root", str(sym_repo), "--check-hygiene"],
                ["--repo-root", str(repo), "--paths", str(sym_path), "--check-hygiene"],
                ["--repo-root", str(repo), "--telemetry", "--lean-lib-dir", str(sym_lib)],
                ["--repo-root", str(repo), "--json-out", str(sym_out)],
            ]
            for argv in cases:
                with self.subTest(argv=argv), self.assertRaisesRegex(
                    proof_health_scan.HealthScanError, "symlink"
                ):
                    proof_health_scan.main(argv)

    def test_simp_lemma_list_scan_covers_options_nesting_and_bare_simp(self):
        flagged = [
            "by simp +arith only [evalStep]",
            "by simp +decide only [evalStep]",
            "by simp only [xs[0], evalStep]",
            "by simp only [f (g [a]), Place.beq]",
            "by simp [evalStep]",
            "by simp (config := {}) only [writePlace]",
            "by simp -zeta +arith [MirTy.beq]",
            "by dsimp only [IntWidth.beq]",
            "by simpa [evalRvalue] using h",
            "by simp? [evalTerminator]",
            "by\n  simp only\n    [Nat.add_zero,\n     evalStep]",
        ]
        clean = [
            "by simp only [Nat.add_zero]",
            "by simp [Foo.evalStep_eq]",
            "by simp at h",
            "by simp only [xs[0]]\n  exact evalStep",
            "by simp -- [evalStep]",
        ]
        for tactic in flagged + clean:
            text = f"prelude\ntheorem t : True := {tactic}\n"
            rules = [
                v["rule"] for v in proof_health_scan.scan_file_hygiene(text, "P.lean")
            ]
            with self.subTest(tactic=tactic):
                self.assertEqual(
                    rules.count("simp_only_evaluator"), 1 if tactic in flagged else 0
                )

    def test_hygiene_ratchet_follows_renames_of_legacy_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            _init_repo(repo)
            legacy = "prelude\n" + "".join(
                f"theorem t{i} : True := True.intro -- {'x' * 90}\n" for i in range(4)
            )
            _write(repo, "anneal/theory/Old.lean", legacy)
            base = _commit(repo, "base")
            _git(repo, "mv", "anneal/theory/Old.lean", "anneal/theory/New.lean")
            _commit(repo, "Rename legacy file")
            self.assertEqual(
                proof_health_scan.check_repo_hygiene(repo, base_rev=base), []
            )
            _write(
                repo,
                "anneal/theory/New.lean",
                legacy + f"theorem t9 : True := True.intro -- {'y' * 90}\n",
            )
            violations = proof_health_scan.check_repo_hygiene(repo, base_rev=base)
            self.assertEqual([v["rule"] for v in violations], ["max_columns"])

    def _spec_repo(self, repo: Path) -> str:
        """Create a repo with unit `01_u` (specification sources `Spec.lean`
        and `Bounds.lean`) and an out-of-scope corpus; return the base sha."""
        _init_repo(repo)
        _write_unit(repo, "01_u")
        _write(repo, "zerocopy/proofs/01_u/Bounds.lean", "prelude\n-- b0\n")
        _write(repo, "anneal/tests/corpora/x/Spec.lean", "prelude\n-- s\n")
        return _commit(repo, "base")

    def test_spec_gate_blocks_net_changes_to_protected_paths(self):
        unit = "zerocopy/proofs/01_u"
        request = json.loads(_request_json(["Spec.lean", "Bounds.lean"]))
        narrowed = json.loads(json.dumps(request))
        narrowed["scope"]["roots"] = ["a"]
        renamed = json.loads(json.dumps(request))
        renamed["proof"]["sources"][0]["path"] = "AltSpec.lean"
        more_proofs = json.loads(json.dumps(request))
        more_proofs["proof"]["sources"].append(
            {"module": "Helper", "path": "Helper.lean", "role": "proof"}
        )
        promoted = json.loads(json.dumps(more_proofs))
        promoted["proof"]["sources"][-1]["role"] = "specification"

        def edit_spec(repo):
            _write(repo, f"{unit}/Spec.lean", "prelude\n-- s1\n")

        def edit_bounds(repo):
            _write(repo, f"{unit}/Bounds.lean", "prelude\n-- b1\n")

        def narrow_scope(repo):
            _write(repo, f"{unit}/request.json", json.dumps(narrowed))

        def replace_spec(repo):
            _git(repo, "rm", "-q", f"{unit}/Spec.lean")
            _write(repo, f"{unit}/AltSpec.lean", "prelude\n-- alt\n")
            _write(repo, f"{unit}/request.json", json.dumps(renamed))
            _write(repo, f"{unit}/Proof.lean", "prelude\n-- p1\n")

        def rename_spec(repo):
            _git(repo, "mv", f"{unit}/Spec.lean", f"{unit}/Spec2.lean")

        def rename_unit(repo):
            _git(repo, "mv", unit, "zerocopy/proofs/01_renamed")

        def delete_unit(repo):
            _git(repo, "rm", "-q", "-r", unit)

        def add_proof_module(repo):
            _write(repo, f"{unit}/Helper.lean", "prelude\n-- h\n")
            _write(repo, f"{unit}/request.json", json.dumps(more_proofs))

        def add_spec_module(repo):
            _write(repo, f"{unit}/Helper.lean", "prelude\n-- h\n")
            _write(repo, f"{unit}/request.json", json.dumps(promoted))

        def corrupt_request(repo):
            _write(repo, f"{unit}/request.json", "{")

        def symlink_request(repo):
            path = repo / unit / "request.json"
            old_text = path.read_text(encoding="utf-8")
            path.unlink()
            path.symlink_to(old_text)

        def duplicate_role_key(repo):
            text = json.dumps(more_proofs).replace(
                '"role": "proof"}]', '"role": "specification", "role": "proof"}]'
            )
            self.assertIn('"role": "specification", "role": "proof"', text)
            _write(repo, f"{unit}/Helper.lean", "prelude\n-- h\n")
            _write(repo, f"{unit}/request.json", text)

        def edit_proof(repo):
            _write(repo, f"{unit}/Proof.lean", "prelude\n-- p1\n")

        def add_unit(repo):
            _write_unit(repo, "05_new")

        def edit_corpus(repo):
            _write(repo, "anneal/tests/corpora/x/Spec.lean", "prelude\n-- s2\n")

        blocked = {
            "edit Spec.lean": (edit_spec, "Edit spec"),
            "edit differently named spec": (edit_bounds, "Edit bounds"),
            "narrow scope": (narrow_scope, "Narrow scope"),
            "add spec module": (add_spec_module, "Add spec module"),
            "corrupt request": (corrupt_request, "Corrupt request"),
            "symlink request": (symlink_request, "Symlink request"),
            "duplicate role key": (duplicate_role_key, "Duplicate role key"),
            "record separator injection": (
                edit_spec,
                "Edit spec\n\nSigned-off-by: A\x1e000000000000\x1f"
                "Spec-Change: 01_u tightening",
            ),
            "line separator injection": (
                edit_spec,
                "Edit spec\n\nSigned-off-by: A\x1eSpec-Change: 01_u tightening",
            ),
            "replace spec": (replace_spec, "[proof-opt] Replace spec"),
            "rename spec": (rename_spec, "Rename spec"),
            "rename unit": (rename_unit, "Rename unit"),
            "delete unit": (delete_unit, "Delete unit"),
            "negative prose": (edit_spec, "Edit spec\n\nNo Spec-Change: needed."),
            "trailer-like body line": (
                edit_spec,
                "Edit spec\n\nSpec-Change: 01_u tightening\n\nMore prose.",
            ),
            "other unit trailer": (edit_spec, "Edit\n\nSpec-Change: 02_v tightening"),
        }
        allowed = {
            "edit proof": (edit_proof, "Edit proof"),
            "add proof module": (add_proof_module, "Add proof module"),
            "add unit": (add_unit, "Add unit"),
            "edit corpus": (edit_corpus, "Edit corpus"),
            "trailer": (
                edit_spec,
                "Edit spec\n\nSpec-Change: 01_u tightening\nAgent-authored-by: AI",
            ),
            "rename unit with trailer": (
                rename_unit,
                "Rename unit\n\nSpec-Change: 01_u refactor",
            ),
        }
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            base = self._spec_repo(repo)
            for name, (mutate, msg) in {**blocked, **allowed}.items():
                with self.subTest(name):
                    _git(repo, "checkout", "-q", "-B", "pr", base)
                    mutate(repo)
                    _commit(repo, msg)
                    errs = proof_health_scan.check_spec_immutability_git(repo, base)
                    if name in allowed:
                        self.assertEqual(errs, [])
                    else:
                        self.assertEqual(len(errs), 1, errs)
                        self.assertIn(f"{unit}:", errs[0])

            # Splitting the spec edit and an unrelated trailer across commits is
            # judged on the net diff, and an authorizing trailer on any commit
            # in the range counts.
            _git(repo, "checkout", "-q", "-B", "pr", base)
            edit_spec(repo)
            _commit(repo, "Edit spec")
            edit_proof(repo)
            _commit(repo, "Edit proof\n\nSpec-Change: 01_u tightening")
            self.assertEqual(
                proof_health_scan.check_spec_immutability_git(repo, base), []
            )

    def test_spec_gate_rejects_malformed_trailers(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            base = self._spec_repo(repo)
            for trailer in (
                "Spec-Change: not needed",
                "spec-change: 01_u tightening",
                "Spec-Change: 01_u",
                "Spec-Change: 01_u tightening extra",
            ):
                with self.subTest(trailer):
                    _git(repo, "checkout", "-q", "-B", "pr", base)
                    _write(repo, "zerocopy/proofs/01_u/Proof.lean", "prelude\n-- p1\n")
                    _commit(repo, f"Edit proof\n\n{trailer}")
                    errs = proof_health_scan.check_spec_immutability_git(repo, base)
                    self.assertEqual(len(errs), 1, errs)
                    self.assertIn("malformed trailer", errs[0])

    def test_spec_gate_judges_merges_by_net_tree(self):
        spec = "zerocopy/proofs/01_u/Spec.lean"
        proof = "zerocopy/proofs/01_u/Proof.lean"
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            fork = self._spec_repo(repo)
            _write(repo, spec, "prelude\n-- s1 tightened\n")
            _commit(repo, "Tighten spec\n\nSpec-Change: 01_u tightening")
            _write(repo, "README.md", "main\n")
            main_tip = _commit(repo, "Main readme")
            _git(repo, "checkout", "-q", "-b", "side", fork)
            _write(repo, "SIDE.md", "side\n")
            _commit(repo, "Side")

            def pr_branch():
                _git(repo, "checkout", "-q", "-B", "pr", fork)
                _write(repo, proof, "prelude\n-- p1\n")
                _commit(repo, "Shrink proof")

            def gate():
                return proof_health_scan.check_spec_immutability_git(repo, "main")

            cases = {
                "two-parent -s ours": ["-s", "ours", "main"],
                "octopus -s ours": ["-s", "ours", "main", "side"],
            }
            for name, merge_args in cases.items():
                with self.subTest(name):
                    pr_branch()
                    _git(repo, "merge", "-q", *merge_args, "-m", "Merge")
                    self.assertEqual(
                        (repo / spec).read_text(encoding="utf-8"), "prelude\n-- s0\n"
                    )
                    errs = gate()
                    self.assertEqual(len(errs), 1, errs)
                    self.assertIn(spec, errs[0])

            with self.subTest("clean merge"):
                pr_branch()
                _git(repo, "merge", "-q", "--no-ff", "main", "side", "-m", "Merge")
                self.assertEqual(gate(), [])

            with self.subTest("synthetic PR merge"):
                pr_branch()
                pr_tip = _git(repo, "rev-parse", "HEAD")
                _git(repo, "checkout", "-q", "--detach", main_tip)
                _git(repo, "merge", "-q", "--no-ff", pr_tip, "-m", "Merge PR")
                self.assertEqual(gate(), [])

            with self.subTest("conflict resolution"):
                pr_branch()
                _write(repo, spec, "prelude\n-- pr edit\n")
                _commit(repo, "Edit spec\n\nSpec-Change: 01_u refactor")
                subprocess.run(
                    ["git", "merge", "-q", "main"], cwd=repo, capture_output=True
                )
                _write(repo, spec, "prelude\n-- resolved\n")
                _commit(repo, "Merge main")
                self.assertEqual(gate(), [])
                # Without an authorizing trailer, the resolution fails.
                _git(repo, "checkout", "-q", "-B", "pr2", fork)
                _write(repo, proof, "prelude\n-- p1\n")
                _commit(repo, "Shrink proof")
                subprocess.run(
                    ["git", "merge", "-q", "--no-commit", "main"],
                    cwd=repo,
                    capture_output=True,
                )
                _write(repo, spec, "prelude\n-- resolved\n")
                _commit(repo, "Merge main")
                self.assertEqual(len(gate()), 1)

    def test_missing_base_ref_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            self._spec_repo(repo)
            with self.assertRaisesRegex(proof_health_scan.HealthScanError, "not found"):
                proof_health_scan.git_merge_base(repo, "refs/heads/no-such-ref")
            proc = subprocess.run(
                [
                    sys.executable,
                    str(Path(proof_health_scan.__file__)),
                    "--repo-root",
                    str(repo),
                    "--check-hygiene",
                    "--base-ref",
                    "refs/heads/no-such-ref",
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(proc.returncode, 1)
            self.assertIn("not found", proc.stderr)
            self.assertNotIn("Traceback", proc.stderr)

    def test_simp_wildcard_scan_covers_all_simp_forms(self):
        flagged = [
            "by simp [*]",
            "by simp [*, Nat.add_zero]",
            "by simp [Nat.add_zero, *]",
            "by simp only [*]",
            "by simp +arith [*]",
            "by simp (config := {}) only [*]",
            "by dsimp [*]",
            "by simpa [*] using h",
            "by simp? [*]",
            "by simp_arith [*]",
            "by\n  simp\n    [h,\n     *]",
            "by simp_all",
            "by simp_all only [h]",
        ]
        clean = [
            "by simp [h]",
            "by simp [f (*)]",
            "by simp [xs[*]]",
            "by simp at *",
            "by simp -- [*]",
            "by exact (· * ·)",
        ]
        for tactic in flagged + clean:
            text = f"prelude\ntheorem t : True := {tactic}\n"
            rules = [
                v["rule"] for v in proof_health_scan.scan_file_hygiene(text, "P.lean")
            ]
            with self.subTest(tactic=tactic):
                self.assertEqual(
                    rules.count("forbidden_simp_wildcard"),
                    1 if tactic in flagged else 0,
                )

    def test_hygiene_ratchet_uses_merge_base(self):
        legacy = "prelude\n" + "".join(
            f"theorem t{i} : True := True.intro -- {'x' * 90}\n" for i in range(2)
        )
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            _init_repo(repo)
            _write(repo, "zerocopy/proofs/README.md", "units\n")
            _write(repo, "anneal/theory/Old.lean", legacy)
            _write(repo, "anneal/theory/Gone.lean", legacy)
            fork = _commit(repo, "base")
            # `main` later fixes one legacy file and deletes the other.
            _write(repo, "anneal/theory/Old.lean", "prelude\n")
            _git(repo, "rm", "-q", "anneal/theory/Gone.lean")
            _commit(repo, "Fix legacy files")
            _git(repo, "checkout", "-q", "-b", "pr", fork)
            _write(repo, "README.md", "pr\n")
            _commit(repo, "Unrelated change")
            argv = ["--repo-root", str(repo), "--check-hygiene", "--base-ref", "main"]
            with mock.patch("sys.stdout"):
                self.assertEqual(proof_health_scan.main(argv), 0)
            # Introducing a new violation on the branch still fails.
            _write(
                repo,
                "anneal/theory/Old.lean",
                legacy + f"theorem t9 : True := True.intro -- {'y' * 90}\n",
            )
            with mock.patch("sys.stdout"):
                self.assertEqual(proof_health_scan.main(argv), 1)

    def test_ensure_nonsymlink_stays_below_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            real = Path(tmp) / "real"
            (real / "repo/sub").mkdir(parents=True)
            (real / "repo/sub/F.lean").write_text("prelude\n", encoding="utf-8")
            (real / "repo/link").symlink_to(real / "repo/sub")
            alias = Path(tmp) / "alias"
            alias.symlink_to(real)
            # A symlink above the root is not inspected.
            root = alias / "repo"
            proof_health_scan.ensure_nonsymlink(root / "sub/F.lean", root)
            proof_health_scan.ensure_nonsymlink(alias / "repo/sub")
            for path in (root / "link/F.lean", root / "link"):
                with self.subTest(path=path), self.assertRaisesRegex(
                    proof_health_scan.HealthScanError, "symlink"
                ):
                    proof_health_scan.ensure_nonsymlink(path, root)
            with self.assertRaisesRegex(proof_health_scan.HealthScanError, "escapes"):
                proof_health_scan.ensure_nonsymlink(real / "x", root)

    def test_spec_gate_handles_criss_cross_merges(self):
        spec = "zerocopy/proofs/01_u/Spec.lean"
        proof = "zerocopy/proofs/01_u/Proof.lean"
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            root = self._spec_repo(repo)
            _git(repo, "checkout", "-q", "-b", "b2", root)
            _write(repo, spec, "prelude\n-- s1\n")
            b2 = _commit(repo, "Tighten\n\nSpec-Change: 01_u tightening")
            _git(repo, "checkout", "-q", "-b", "b1", root)
            _write(repo, "A.txt", "a\n")
            b1 = _commit(repo, "A")
            _git(repo, "checkout", "-q", "main")
            _git(repo, "merge", "-q", "--no-ff", b2, "-m", "Merge b2")
            _git(repo, "merge", "-q", "--no-ff", b1, "-m", "Merge b1")

            def pr(spec_text, strategy):
                _git(repo, "checkout", "-q", "-B", "pr", b1)
                _git(repo, "merge", "-q", *strategy, b2, "-m", "Merge b2")
                _write(repo, proof, "prelude\n-- p1\n")
                if spec_text is not None:
                    _write(repo, spec, spec_text)
                _commit(repo, "Edit")
                bases = _git(repo, "merge-base", "--all", "main", "HEAD").split()
                self.assertEqual(sorted(bases), sorted([b1, b2]))
                return proof_health_scan.check_spec_immutability_git(repo, "main")

            # Keeping or weakening the old spec without a trailer fails even
            # though `b2`'s trailer is reachable from `HEAD`.
            self.assertEqual(len(pr(None, ["-s", "ours"])), 1)
            self.assertEqual(len(pr("prelude\n-- evil\n", ["-s", "ours"])), 1)
            self.assertEqual(len(pr("prelude\n-- evil\n", ["--no-ff"])), 1)
            self.assertEqual(pr(None, ["--no-ff"]), [])

    def test_spec_gate_counts_conflicts_on_protected_paths(self):
        unit = "zerocopy/proofs/01_u"
        request = json.loads(_request_json(["Spec.lean", "Bounds.lean"]))
        widened = json.loads(json.dumps(request))
        widened["scope"]["roots"].append("c")
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            fork = self._spec_repo(repo)
            cases = {
                "Spec.lean": "prelude\n-- s1\n",
                "request.json": json.dumps(widened),
            }
            for name, text in cases.items():
                with self.subTest(name):
                    _git(repo, "checkout", "-q", "-B", "main", fork)
                    _write(repo, f"{unit}/{name}", text)
                    _commit(repo, "Change on main\n\nSpec-Change: 01_u tightening")
                    # Modify/delete: the merged tree keeps `main`'s file.
                    _git(repo, "checkout", "-q", "-B", "pr", fork)
                    _git(repo, "rm", "-q", f"{unit}/{name}")
                    _commit(repo, "Delete")
                    errs = proof_health_scan.check_spec_immutability_git(repo, "main")
                    self.assertEqual(len(errs), 1, errs)
                    self.assertIn(f"{unit}/{name}", errs[0])

    def test_block_comments_and_line_breaks_match_lean(self):
        flagged = {
            "theorem t : True := by simp/- -/only [*]": "forbidden_simp_wildcard",
            'local/- -/macro "g" : tactic => `(tactic| rfl)': "forbidden_local_macro",
            "-- " + "x" * 60 + "\u2028" + "y" * 60: "max_columns",
        }
        for line, rule in flagged.items():
            text = f"prelude\n{line}\n"
            with self.subTest(line=line):
                rules = [
                    v["rule"] for v in proof_health_scan.scan_file_hygiene(text, "P.lean")
                ]
                self.assertEqual(rules, [rule])
        # A leading block comment keeps the declaration at column 0.
        self.assertEqual(
            proof_health_scan.strip_lean_comments_and_strings("/- c -/theorem t\n"),
            ["theorem t"],
        )


if __name__ == "__main__":
    unittest.main()
