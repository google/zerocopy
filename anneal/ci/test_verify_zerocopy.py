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
from pathlib import Path
import tempfile
import unittest

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


if __name__ == "__main__":
    unittest.main()
