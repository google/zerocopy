# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/verify_zerocopy.py` hygiene and Receipt v3 gates."""

import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import anneal_scaffold
import verify_zerocopy


def make_receipt(**overrides):
    receipt = {
        "schema_version": 3,
        "status": "selected_unit_verified",
        "taint_reasons": [],
        "elaboration_sandbox": "linux_bwrap",
        "deferred": [],
        "scope": {
            "kind": "selected_unit",
            "roots": ["util::macros::__unsafe"],
        },
        "request_sha256": "req-digest",
        "capture_sha256": "cap-digest",
        "specification_manifest_sha256": "spec-digest",
        "model_manifest_sha256": "model-digest",
        "selected": ["util::macros::__unsafe"],
        "timing_ms": {"total": 100},
        "audit": {
            "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
            "exactType": True,
            "checkedAlternateProofs": 0,
            "axioms": ["propext"],
            "bindings": {
                "requestSha256": "req-digest",
                "captureSha256": "cap-digest",
                "specificationManifestSha256": "spec-digest",
                "modelManifestSha256": "model-digest",
            },
        },
    }
    for key, val in overrides.items():
        if key == "audit":
            receipt["audit"].update(val)
        else:
            receipt[key] = val
    return receipt


def make_proof_tree(root: Path):
    src_dir = root / "zerocopy/src"
    src_dir.mkdir(parents=True)
    (src_dir / "lib.rs").write_text("", encoding="utf-8")

    proofs_dir = root / "zerocopy/proofs"
    proofs_dir.mkdir(parents=True)
    (proofs_dir / "README.md").write_text("# Proofs\n", encoding="utf-8")

    unit = proofs_dir / "01_unit"
    unit.mkdir()
    (unit / "Spec.lean").write_text("prelude\n", encoding="utf-8")
    (unit / "Proof.lean").write_text("prelude\n", encoding="utf-8")
    (unit / "request.json").write_text(
        json.dumps({
            "schema_version": 1,
            "compilation": {"source_root": "../../src"},
            "scope": {"kind": "selected_unit", "roots": ["util::macros::__unsafe"]},
            "proof": {
                "source_root": ".",
                "sources": [
                    {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                    {"module": "Proof", "path": "Proof.lean", "role": "proof"},
                ],
            },
        }),
        encoding="utf-8",
    )
    return proofs_dir, src_dir, unit


class VerifyZerocopyTests(unittest.TestCase):
    def test_discover_units_valid_and_rejects_stray_files_or_symlinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            proofs_dir, src_dir, unit = make_proof_tree(Path(tmp))
            discovered = verify_zerocopy.discover_units(proofs_dir, src_dir)
            self.assertEqual([u.name for u, _ in discovered], ["01_unit"])

            stray = unit / "run.sh"
            stray.write_text("#!/bin/sh\n", encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "undeclared files"):
                verify_zerocopy.discover_units(proofs_dir, src_dir)
            stray.unlink()

            link = unit / "evil.lean"
            link.symlink_to(unit / "Spec.lean")
            with self.assertRaisesRegex(RuntimeError, "symlink disallowed"):
                verify_zerocopy.discover_units(proofs_dir, src_dir)
            link.unlink()

            stray_top = proofs_dir / "lakefile.toml"
            stray_top.write_text("", encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "unexpected top-level"):
                verify_zerocopy.discover_units(proofs_dir, src_dir)

    def test_discover_units_rejects_bad_source_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            other_src = root / "zerocopy/other_src"
            other_src.mkdir(parents=True)
            (other_src / "lib.rs").write_text("", encoding="utf-8")
            proofs_dir, src_dir, unit = make_proof_tree(root)
            req = json.loads((unit / "request.json").read_text(encoding="utf-8"))
            req["compilation"]["source_root"] = "../../other_src"
            (unit / "request.json").write_text(json.dumps(req), encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "does not resolve"):
                verify_zerocopy.discover_units(proofs_dir, src_dir)

    def test_validate_receipt_accepts_clean_and_rejects_taint_or_axioms(self):
        good = make_receipt()
        parsed = verify_zerocopy.validate_receipt(
            "01_unit", 0, json.dumps(good), "", ["util::macros::__unsafe"]
        )
        self.assertEqual(parsed["status"], "selected_unit_verified")

        empty_digest = make_receipt(request_sha256="")
        empty_digest["audit"]["bindings"]["requestSha256"] = ""
        missing_digest = make_receipt()
        del missing_digest["model_manifest_sha256"]
        del missing_digest["audit"]["bindings"]["modelManifestSha256"]

        bad_cases = [
            ("taint", make_receipt(taint_reasons=["unsandboxed_elaboration"]), "taint_reasons"),
            ("sandbox", make_receipt(elaboration_sandbox="none"), "elaboration_sandbox"),
            ("axioms", make_receipt(audit={"axioms": ["propext", "Classical.choice"]}), "axioms"),
            ("exactType", make_receipt(audit={"exactType": False}), "exactType"),
            ("altProof", make_receipt(audit={"checkedAlternateProofs": 1}), "checkedAlternateProofs"),
            ("sorry", make_receipt(sorry_declarations=["foo"]), "sorry_declarations"),
            ("status", make_receipt(status="proof_failed"), "status="),
            ("roots_str", make_receipt(scope={"kind": "selected_unit", "roots": "not-a-list"}), "scope mismatch"),
            ("deferred_null", make_receipt(deferred=None), "deferred=None"),
            ("deferred_str", make_receipt(deferred="hostile"), "deferred='hostile'"),
            ("deferred_dict", make_receipt(deferred={}), "deferred=\\{\\}"),
            (
                "deferred_hostile",
                make_receipt(deferred=["hostile Lean elaborator effects"]),
                "hostile Lean elaborator effects deferred",
            ),
            ("empty_digest", empty_digest, "binding digest"),
            ("missing_digest", missing_digest, "binding digest"),
            ("exit", good, "exit=1"),
        ]
        for label, payload, needle in bad_cases:
            rc = 1 if label == "exit" else 0
            with self.subTest(case=label):
                with self.assertRaisesRegex(RuntimeError, needle):
                    verify_zerocopy.validate_receipt(
                        "01_unit", rc, json.dumps(payload), "", ["util::macros::__unsafe"]
                    )

    def test_main_runs_with_mocked_cli_and_writes_summary(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proofs_dir, src_dir, _ = make_proof_tree(root)
            fake_cli = root / "cargo-anneal"
            fake_cap = root / "anneal-rustc-capture"
            fake_lean = root / "lean"
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            for bin_path in (fake_cap, fake_lean):
                bin_path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                bin_path.chmod(0o755)
            payload_json = json.dumps(make_receipt())
            fake_cli.write_text(
                "#!/usr/bin/env python3\n"
                f"print({payload_json!r})\n",
                encoding="utf-8",
            )
            fake_cli.chmod(0o755)
            artifacts = root / "out"
            with contextlib.redirect_stdout(io.StringIO()):
                rc = verify_zerocopy.main([
                    "--proofs-dir", str(proofs_dir),
                    "--src-dir", str(src_dir),
                    "--cli", str(fake_cli),
                    "--capture", str(fake_cap),
                    "--sysroot", str(fake_sys),
                    "--lean", str(fake_lean),
                    "--artifacts-dir", str(artifacts),
                ])
            self.assertEqual(rc, 0)
            summary = json.loads((artifacts / "summary.json").read_text(encoding="utf-8"))
            self.assertEqual(summary["unit_count"], 1)
            self.assertIn("01_unit", summary["units"])

    def test_validate_receipt_allows_absent_deferred(self):
        receipt = make_receipt()
        del receipt["deferred"]
        parsed = verify_zerocopy.validate_receipt(
            "01_unit", 0, json.dumps(receipt), "", ["util::macros::__unsafe"]
        )
        self.assertEqual(parsed["status"], "selected_unit_verified")

    def test_discover_units_deduplicates_selected_units_preserving_order(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proofs_dir, src_dir, unit_01 = make_proof_tree(root)
            unit_02 = proofs_dir / "02_unit"
            unit_02.mkdir()
            for fname in ("Spec.lean", "Proof.lean", "request.json"):
                (unit_02 / fname).write_text(
                    (unit_01 / fname).read_text(encoding="utf-8"), encoding="utf-8"
                )

            selected = verify_zerocopy.discover_units(
                proofs_dir, src_dir, selected_units=["02_unit", "01_unit", "02_unit"]
            )
            self.assertEqual([u.name for u, _ in selected], ["02_unit", "01_unit"])

    def test_main_deduplicates_unit_flags_and_skips_local_discovery(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proofs_dir, src_dir, _ = make_proof_tree(root)
            fake_cli = root / "cargo-anneal"
            fake_cap = root / "anneal-rustc-capture"
            fake_lean = root / "lean"
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            for bin_path in (fake_cap, fake_lean):
                bin_path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                bin_path.chmod(0o755)
            invocations = root / "calls.txt"
            payload_json = json.dumps(make_receipt())
            fake_cli.write_text(
                "#!/usr/bin/env python3\n"
                "from pathlib import Path\n"
                f"with Path({str(invocations)!r}).open('a', encoding='utf-8') as f:\n"
                "    f.write('1\\n')\n"
                f"print({payload_json!r})\n",
                encoding="utf-8",
            )
            fake_cli.chmod(0o755)
            artifacts = root / "out"
            with (
                mock.patch.object(
                    verify_zerocopy,
                    "discover_local_defaults",
                    side_effect=AssertionError("should not probe local defaults"),
                ),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                rc = verify_zerocopy.main([
                    "--proofs-dir", str(proofs_dir),
                    "--src-dir", str(src_dir),
                    "--unit", "01_unit",
                    "--unit", "01_unit",
                    "--cli", str(fake_cli),
                    "--capture", str(fake_cap),
                    "--sysroot", str(fake_sys),
                    "--lean", str(fake_lean),
                    "--artifacts-dir", str(artifacts),
                ])
            self.assertEqual(rc, 0)
            self.assertEqual(
                invocations.read_text(encoding="utf-8").splitlines(), ["1"]
            )
            summary = json.loads(
                (artifacts / "summary.json").read_text(encoding="utf-8")
            )
            self.assertEqual(summary["unit_count"], 1)

    def test_main_help_defers_local_discovery(self):
        with (
            mock.patch.object(
                verify_zerocopy,
                "discover_local_defaults",
                side_effect=AssertionError("should not probe local defaults on --help"),
            ),
            contextlib.redirect_stdout(io.StringIO()),
        ):
            with self.assertRaises(SystemExit) as exc:
                verify_zerocopy.main(["--help"])
            self.assertEqual(exc.exception.code, 0)

    def test_discover_local_defaults_empty_xdg_and_dangling_symlink(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            home = root / "home"
            cwd = root / "cwd"
            anneal_root = root / "anneal"
            home.mkdir()
            cwd.mkdir()
            anneal_root.mkdir()

            # Decoy under CWD that would be probed if XDG_CACHE_HOME="" were
            # treated as relative `.`.
            decoy_lean = cwd / "anneal/toolchain/decoy/lean/bin/lean"
            decoy_lean.parent.mkdir(parents=True)
            decoy_lean.write_text("", encoding="utf-8")

            cache_tc = home / ".cache/anneal/toolchain"
            cache_tc.mkdir(parents=True)
            (cache_tc / "broken").symlink_to(root / "nonexistent")
            good_lean = cache_tc / "good/lean/bin/lean"
            good_lean.parent.mkdir(parents=True)
            good_lean.write_text("", encoding="utf-8")

            old_cwd = os.getcwd()
            try:
                os.chdir(cwd)
                for empty_xdg in ("", "   "):
                    with (
                        self.subTest(xdg_cache_home=empty_xdg),
                        mock.patch.dict(
                            os.environ, {"XDG_CACHE_HOME": empty_xdg}, clear=False
                        ),
                        mock.patch.object(Path, "home", return_value=home),
                        mock.patch("subprocess.check_output", side_effect=OSError),
                    ):
                        defaults = verify_zerocopy.discover_local_defaults(anneal_root)
                        self.assertEqual(defaults["lean"], good_lean)
            finally:
                os.chdir(old_cwd)

    def test_autoscaffold_drift_and_role_gates_in_verify_zerocopy(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proofs_dir, src_dir, unit = make_proof_tree(root)
            cap_data = {
                "program": {
                    "bodies": [{
                        "identity": "rust-path-v1::util::macros::__unsafe",
                        "arg_count": 0,
                        "local_tys": [{"kind": "unit"}],
                        "blocks": [{"statements": [], "terminator": {"kind": "ret"}}],
                    }]
                }
            }
            rendered = anneal_scaffold.render_scaffold(cap_data)
            (unit / "AutoScaffold.lean").write_text(rendered, encoding="utf-8")

            bad_req = json.loads((unit / "request.json").read_text(encoding="utf-8"))
            bad_req["proof"]["sources"] = [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {
                    "module": "AutoScaffold",
                    "path": "AutoScaffold.lean",
                    "role": "specification",
                },
                {"module": "Proof", "path": "Proof.lean", "role": "proof"},
            ]
            (unit / "request.json").write_text(json.dumps(bad_req), encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "role='proof'"):
                verify_zerocopy.discover_units(proofs_dir, src_dir)

            good_req = dict(bad_req)
            good_req["proof"] = dict(bad_req["proof"])
            good_req["proof"]["sources"] = [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "AutoScaffold", "path": "AutoScaffold.lean", "role": "proof"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"},
            ]
            (unit / "request.json").write_text(json.dumps(good_req), encoding="utf-8")

            fake_cli = root / "cargo-anneal"
            fake_cap = root / "anneal-rustc-capture"
            fake_lean = root / "lean"
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            for bin_path in (fake_cap, fake_lean):
                bin_path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                bin_path.chmod(0o755)
            payload_json = json.dumps(make_receipt())
            cap_json_txt = json.dumps(cap_data)
            fake_cli.write_text(
                "#!/usr/bin/env python3\n"
                "import sys\n"
                "from pathlib import Path\n"
                "art = Path(sys.argv[sys.argv.index('--artifacts') + 1])\n"
                "(art / 'capture').mkdir(parents=True, exist_ok=True)\n"
                f"(art / 'capture/capture.json').write_text({cap_json_txt!r}, encoding='utf-8')\n"
                f"print({payload_json!r})\n",
                encoding="utf-8",
            )
            fake_cli.chmod(0o755)

            with contextlib.redirect_stdout(io.StringIO()):
                rc = verify_zerocopy.main([
                    "--proofs-dir", str(proofs_dir),
                    "--src-dir", str(src_dir),
                    "--cli", str(fake_cli),
                    "--capture", str(fake_cap),
                    "--sysroot", str(fake_sys),
                    "--lean", str(fake_lean),
                ])
            self.assertEqual(rc, 0)

            (unit / "AutoScaffold.lean").write_text(
                rendered + "-- stale\n", encoding="utf-8"
            )
            with (
                contextlib.redirect_stdout(io.StringIO()),
                self.assertRaisesRegex(RuntimeError, "AutoScaffold.lean drift"),
            ):
                verify_zerocopy.main([
                    "--proofs-dir", str(proofs_dir),
                    "--src-dir", str(src_dir),
                    "--cli", str(fake_cli),
                    "--capture", str(fake_cap),
                    "--sysroot", str(fake_sys),
                    "--lean", str(fake_lean),
                ])

            # Restore clean AutoScaffold.lean and verify anti-golf gate.
            (unit / "AutoScaffold.lean").write_text(rendered, encoding="utf-8")
            (unit / "Proof.lean").write_text(
                "prelude\ntheorem verify : True := by simp [*]\n",
                encoding="utf-8",
            )
            with (
                contextlib.redirect_stdout(io.StringIO()),
                self.assertRaisesRegex(RuntimeError, "proof hygiene violation"),
            ):
                verify_zerocopy.main([
                    "--proofs-dir", str(proofs_dir),
                    "--src-dir", str(src_dir),
                    "--cli", str(fake_cli),
                    "--capture", str(fake_cap),
                    "--sysroot", str(fake_sys),
                    "--lean", str(fake_lean),
                ])

    def test_main_symlink_policy_for_cli_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proofs_dir = root / "proofs"
            proofs_dir.mkdir()
            src_dir = root / "src"
            src_dir.mkdir()
            (src_dir / "lib.rs").write_text("", encoding="utf-8")
            fake_bin = root / "bin"
            fake_bin.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_bin.chmod(0o700)
            fake_dir = root / "sysroot"
            fake_dir.mkdir()

            sym_bin = root / "sym_bin"
            sym_bin.symlink_to(fake_bin)
            sym_sys = root / "sym_sys"
            sym_sys.symlink_to(fake_dir)
            sym_proofs = root / "sym_proofs"
            sym_proofs.symlink_to(proofs_dir)
            sym_src = root / "sym_src"
            sym_src.symlink_to(src_dir)
            sym_art = root / "sym_art"
            sym_art.symlink_to(fake_dir)
            alias = root / "alias"
            alias.symlink_to(root)

            def tools(cli=fake_bin, capture=fake_bin, sysroot=fake_dir, lean=fake_bin):
                return [
                    "--cli", str(cli),
                    "--capture", str(capture),
                    "--sysroot", str(sysroot),
                    "--lean", str(lean),
                ]

            dirs = ["--proofs-dir", str(proofs_dir), "--src-dir", str(src_dir)]
            rejected = [
                ["--proofs-dir", str(sym_proofs), "--src-dir", str(src_dir), *tools()],
                ["--proofs-dir", str(proofs_dir), "--src-dir", str(sym_src), *tools()],
                [*dirs, "--artifacts-dir", str(sym_art), *tools()],
            ]
            for argv in rejected:
                with self.subTest(argv=argv), self.assertRaisesRegex(
                    RuntimeError, "symlink"
                ):
                    verify_zerocopy.main(argv)

            # Symlinked toolchain paths (elan, Nix) and symlinks above the
            # proofs tree are accepted; these runs fail later, on the empty
            # proofs tree.
            accepted = [
                [*dirs, *tools(cli=sym_bin)],
                [*dirs, *tools(capture=sym_bin)],
                [*dirs, *tools(sysroot=sym_sys)],
                [*dirs, *tools(lean=sym_bin)],
                [
                    "--proofs-dir", str(alias / "proofs"),
                    "--src-dir", str(alias / "src"),
                    *tools(),
                ],
            ]
            for argv in accepted:
                with self.subTest(argv=argv), self.assertRaisesRegex(
                    RuntimeError, "no proof units discovered"
                ):
                    verify_zerocopy.main(argv)

            (proofs_dir / "01_u").mkdir()
            (root / "elsewhere").mkdir()
            (root / "elsewhere/Evil.lean").write_text("prelude\n", encoding="utf-8")
            (proofs_dir / "01_u/sub").symlink_to(root / "elsewhere")
            (proofs_dir / "01_u/Proof.lean").symlink_to(root / "elsewhere/Evil.lean")
            with self.assertRaisesRegex(RuntimeError, "symlink"):
                verify_zerocopy.main([*dirs, *tools()])


if __name__ == "__main__":
    unittest.main()
