# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/verify_anneal_spec_zerocopy.py`."""

from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

import verify_anneal_spec_zerocopy


def make_receipt(**overrides):
    receipt = {
        "schema_version": 3,
        "status": "selected_unit_verified",
        "taint_reasons": [],
        "elaboration_sandbox": "linux_bwrap",
        "deferred": [],
        "scope": {
            "kind": "selected_unit",
            "roots": ["<() as PointerMetadata>::to_elem_count"],
        },
        "request_sha256": "req-digest",
        "capture_sha256": "cap-digest",
        "specification_manifest_sha256": "spec-digest",
        "model_manifest_sha256": "model-digest",
        "selected": [
            {
                "def_id": 0,
                "path": "<() as PointerMetadata>::to_elem_count",
                "body_index": 0,
            }
        ],
        "timing_ms": {"total": 10},
        "spec_warnings": [],
        "assumptions": ["experimental pointer-free MIR semantics"],
        "correspondence_provenance": {
            "schema_version": 1,
            "upstream_repository": "https://github.com/proofs-rs/lean-miri",
            "upstream_commit": "c92d1d97",
            "upstream_lean_toolchain": "leanprover/lean4:v4.35.0",
            "build_lean_toolchain": "leanprover/lean4:v4.34.1",
            "upstream_pin_sha256": "a" * 64,
            "sysroot_foundation_manifest_sha256": "b" * 64,
            "patched_files": [],
            "minirust_upstream": {
                "upstream_repository": "https://github.com/minirust/minirust",
                "upstream_commit": "d821c6e3",
                "upstream_pin_sha256": "a" * 64,
                "tarball_sha256": "b" * 64,
                "manifest_sha256": "c" * 64,
                "file_count": 1,
                "files": {"spec/lang/syntax.md": "d" * 64},
            },
            "correspondence_adapters": {
                "trusted/correspondence/Trusted/Correspondence.lean": "c" * 64,
            },
            "correspondence_proofs": {
                "correspondence/Anneal/MirCorrespondenceProof.lean": "d" * 64,
            },
            "trusted_lean": {
                "trusted/lean/Trusted/MirSemantics.lean": "e" * 64,
            },
            "note": "pass2",
        },
        "audit": {
            "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
            "subject": "Captured.program",
            "expected": "Expected.claim",
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "replay": True,
            "replayedDeclarations": 1,
            "sorryDeclarations": [],
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
    receipt.update(overrides)
    return receipt


def make_fixture(root: Path):
    src_dir = root / "zerocopy/src"
    src_dir.mkdir(parents=True)
    (src_dir / "lib.rs").write_text("", encoding="utf-8")

    spec_root = root / "anneal/tools/anneal-spec"
    unit = spec_root / "tests/zerocopy/02_unit_pointer_metadata"
    unit.mkdir(parents=True)
    (unit / "Spec.lean").write_text(
        "signature := some { isUnsafe := false, params := [.unit], ret := .int .isize false }\n",
        encoding="utf-8",
    )
    (unit / "Proof.lean").write_text("prelude\n", encoding="utf-8")
    (unit / "spec.rs").write_text(
        "#[anneal::spec(total, ensures(|count| count == 0))]\nfn to_elem_count(self) -> usize;\n",
        encoding="utf-8",
    )
    (unit / "spec_span_map.json").write_text("{}\n", encoding="utf-8")
    (unit / "request.json").write_text(
        json.dumps({
            "schema_version": 1,
            "compilation": {"source_root": "../../../../../../zerocopy/src"},
            "scope": {
                "kind": "selected_unit",
                "roots": ["<() as PointerMetadata>::to_elem_count"],
            },
            "proof": {
                "source_root": ".",
                "specification": "Spec.specs",
                "theorem": "Proof.verify",
                "sources": [
                    {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                    {"module": "Proof", "path": "Proof.lean", "role": "proof"},
                ],
            },
        }),
        encoding="utf-8",
    )
    return spec_root, unit.parent, src_dir, unit


def make_trusted_tree(root: Path):
    trusted = root / "anneal/trusted/lean"
    (trusted / "Trusted/MirSemantics").mkdir(parents=True)
    (trusted / "Trusted.lean").write_text("prelude\n", encoding="utf-8")
    (trusted / "Trusted/MirAst.lean").write_text(
        "module\nprelude\npublic import Init.Prelude\n", encoding="utf-8"
    )
    (trusted / "Trusted/MirSemantics/Ops.lean").write_text(
        "module\nprelude\npublic import Trusted.MirAst\n", encoding="utf-8"
    )
    (trusted / "Trusted/MirSemantics.lean").write_text(
        "module\nprelude\npublic import Trusted.MirSemantics.Ops\n"
        "public import Trusted.MirAst\n",
        encoding="utf-8",
    )
    return trusted


class VerifyAnnealSpecZerocopyTests(unittest.TestCase):
    def test_discover_spec_units_rejects_strays_and_symlinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            _, proofs_dir, src_dir, unit = make_fixture(Path(tmp))
            found = verify_anneal_spec_zerocopy.discover_spec_units(proofs_dir, src_dir)
            self.assertEqual([u.name for u, _ in found], ["02_unit_pointer_metadata"])

            stray = unit / "extra.txt"
            stray.write_text("bad", encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "undeclared files"):
                verify_anneal_spec_zerocopy.discover_spec_units(proofs_dir, src_dir)
            stray.unlink()

            link = unit / "link.lean"
            link.symlink_to(unit / "Spec.lean")
            with self.assertRaisesRegex(RuntimeError, "symlink disallowed"):
                verify_anneal_spec_zerocopy.discover_spec_units(proofs_dir, src_dir)

    def test_run_suite_accepts_clean_and_rejects_passing_negative(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec_root, proofs_dir, src_dir, _ = make_fixture(root)
            trusted = make_trusted_tree(root)
            work = root / "work"
            work.mkdir()
            args = SimpleNamespace(
                proofs_dir=proofs_dir,
                src_root=spec_root,
                src_dir=src_dir,
                trusted_lean=trusted,
                cli=root / "cargo-anneal",
                capture=root / "capture",
                sysroot=root / "sysroot",
                lean=root / "lean",
                lower=root / "lower",
                jobs=1,
                timeout=30,
            )

            verify_cmds = []

            def fake_run(cmd, **_kwargs):
                if "--check" in cmd or "--out-dir" in cmd or cmd[0] == str(args.lean):
                    return subprocess.CompletedProcess(cmd, 0, "", "")
                verify_cmds.append(cmd)
                if "neg-" in cmd[cmd.index("--request") + 1]:
                    return subprocess.CompletedProcess(
                        cmd, 1, json.dumps({"status": "proof_failed"}), ""
                    )
                return subprocess.CompletedProcess(
                    cmd, 0, json.dumps(make_receipt()), ""
                )

            with mock.patch("verify_anneal_spec_zerocopy.subprocess.run", side_effect=fake_run):
                with redirect_stdout(io.StringIO()):
                    summary = verify_anneal_spec_zerocopy.run_suite(args, work)
            # `cargo-anneal verify` prints a human card unless asked for JSON.
            self.assertEqual(len(verify_cmds), 3)
            for cmd in verify_cmds:
                self.assertEqual(cmd[1:4], ["verify", "--format", "json"])
            self.assertEqual(summary["unit_count"], 1)
            self.assertEqual(summary["lean_compile"]["status"], "compiled")
            self.assertEqual(
                summary["negatives"]["mutated_spec_rs"]["status"], "proof_failed"
            )
            self.assertEqual(
                summary["negatives"]["mismatched_signature"]["status"],
                "proof_failed",
            )

            def broken_neg(cmd, **_kwargs):
                if "--check" in cmd or "--out-dir" in cmd or cmd[0] == str(args.lean):
                    return subprocess.CompletedProcess(cmd, 0, "", "")
                return subprocess.CompletedProcess(
                    cmd, 0, json.dumps(make_receipt()), ""
                )

            work_bad = root / "work-bad"
            work_bad.mkdir()
            with mock.patch("verify_anneal_spec_zerocopy.subprocess.run", side_effect=broken_neg):
                with self.assertRaisesRegex(RuntimeError, "unexpectedly succeeded"):
                    with redirect_stdout(io.StringIO()):
                        verify_anneal_spec_zerocopy.run_suite(args, work_bad)

    def test_run_suite_binds_receipt_and_rejects_duplicate_keys(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec_root, proofs_dir, src_dir, unit = make_fixture(root)
            trusted = make_trusted_tree(root)
            args = SimpleNamespace(
                proofs_dir=proofs_dir,
                src_root=spec_root,
                src_dir=src_dir,
                trusted_lean=trusted,
                cli=root / "cargo-anneal",
                capture=root / "capture",
                sysroot=root / "sysroot",
                lean=root / "lean",
                lower=root / "lower",
                jobs=1,
                timeout=30,
            )

            def runner(receipt):
                def fake_run(cmd, **_kwargs):
                    if (
                        "--check" in cmd
                        or "--out-dir" in cmd
                        or cmd[0] == str(args.lean)
                    ):
                        return subprocess.CompletedProcess(cmd, 0, "", "")
                    return subprocess.CompletedProcess(
                        cmd, 0, json.dumps(receipt), ""
                    )

                return fake_run

            # A receipt for a different theorem than the request names.
            wrong_thm = make_receipt()
            wrong_thm["audit"] = dict(
                wrong_thm["audit"], theorem="Proof.other"
            )
            for name, receipt, pattern in (
                ("thm", wrong_thm, "audit.theorem"),
                ("warn", make_receipt(spec_warnings=["w"]), "spec_warnings"),
            ):
                work = root / f"work-{name}"
                work.mkdir()
                with mock.patch(
                    "verify_anneal_spec_zerocopy.subprocess.run",
                    side_effect=runner(receipt),
                ):
                    with self.assertRaisesRegex(RuntimeError, pattern):
                        with redirect_stdout(io.StringIO()):
                            verify_anneal_spec_zerocopy.run_suite(args, work)

            req_path = unit / "request.json"
            text = req_path.read_text(encoding="utf-8")
            req_path.write_text(
                text.replace('{"schema_version": 1,', '{"schema_version": 1, '
                             '"schema_version": 1,', 1),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                verify_anneal_spec_zerocopy.discover_spec_units(
                    proofs_dir, src_dir
                )

    def test_trusted_module_order_puts_imports_first_and_rejects_cycles(self):
        with tempfile.TemporaryDirectory() as tmp:
            trusted = make_trusted_tree(Path(tmp))
            order = verify_anneal_spec_zerocopy.trusted_module_order(trusted)
            self.assertEqual(
                [m for m, _ in order],
                ["Trusted.MirAst", "Trusted.MirSemantics.Ops", "Trusted.MirSemantics"],
            )
            (trusted / "Trusted/MirAst.lean").write_text(
                "prelude\nimport Trusted.MirSemantics\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(RuntimeError, "import cycle"):
                verify_anneal_spec_zerocopy.trusted_module_order(trusted)
            (trusted / "Trusted/MirAst.lean").write_text(
                "prelude\nimport Trusted.Missing\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(RuntimeError, "missing Trusted module"):
                verify_anneal_spec_zerocopy.trusted_module_order(trusted)

    def test_lean_compile_check_builds_in_order_and_rejects_any_message(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec_root, _, _, _ = make_fixture(root)
            trusted = make_trusted_tree(root)
            args = SimpleNamespace(
                src_root=spec_root,
                trusted_lean=trusted,
                lean=root / "lean",
                lower=root / "lower",
                timeout=30,
            )
            calls = []

            def clean(cmd, **kwargs):
                calls.append((cmd, kwargs.get("env")))
                return subprocess.CompletedProcess(cmd, 0, "", "")

            work = root / "work"
            work.mkdir()
            with mock.patch("verify_anneal_spec_zerocopy.subprocess.run", side_effect=clean):
                result = verify_anneal_spec_zerocopy.run_lean_compile_check(args, work)
            self.assertEqual(result, {"status": "compiled", "trusted_modules": 3})
            lib = work / "lean-compile/lib"
            self.assertEqual(calls[0][0][-1], "tests/lean_compile/spec.rs")
            self.assertEqual(
                [cmd[-1] for cmd, _ in calls[1:]],
                [
                    str(trusted / "Trusted/MirAst.lean"),
                    str(trusted / "Trusted/MirSemantics/Ops.lean"),
                    str(trusted / "Trusted/MirSemantics.lean"),
                    str(work / "lean-compile/Spec.lean"),
                    str(spec_root / "tests/lean_compile/Check.lean"),
                ],
            )
            self.assertEqual(calls[3][0][1:4], [f"--root={trusted}", "-o", str(lib / "Trusted/MirSemantics.olean")])
            self.assertEqual(
                calls[4][0][1:6],
                [
                    "-DautoImplicit=false",
                    "-DrelaxedAutoImplicit=false",
                    f"--root={work / 'lean-compile'}",
                    "-o",
                    str(lib / "Spec.olean"),
                ],
            )
            self.assertTrue(all(env["LEAN_PATH"] == str(lib) for _, env in calls[1:]))

            def warns_on_spec(cmd, **_kwargs):
                if cmd[-1].endswith("Spec.lean"):
                    return subprocess.CompletedProcess(cmd, 0, "Spec.lean:1:0: warning: x\n", "")
                return subprocess.CompletedProcess(cmd, 0, "", "")

            work_bad = root / "work-bad"
            work_bad.mkdir()
            with mock.patch(
                "verify_anneal_spec_zerocopy.subprocess.run", side_effect=warns_on_spec
            ):
                with self.assertRaisesRegex(RuntimeError, "generated Spec.lean failed"):
                    verify_anneal_spec_zerocopy.run_lean_compile_check(args, work_bad)


if __name__ == "__main__":
    unittest.main()
