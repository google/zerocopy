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
        "selected": [
            {"def_id": 0, "path": "util::macros::__unsafe", "body_index": 0}
        ],
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

    def test_validate_receipt_profile_v2_root_requires_inapplicable_provenance(self):
        inapplicable = {"applicable": False, "reason": "Profile v1 only"}
        good = make_receipt(
            audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
            correspondence_provenance=inapplicable,
        )
        parsed = verify_zerocopy.validate_receipt(
            "05_unit", 0, json.dumps(good), "", ["util::macros::__unsafe"]
        )
        self.assertEqual(parsed["audit"]["canonicalRoot"], "Trusted.MirSemantics.UnitTheoremV2")

        bad_cases = [
            (
                "v2_missing_provenance",
                make_receipt(audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"}),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_applicable_provenance",
                make_receipt(
                    audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
                    correspondence_provenance={"applicable": True},
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_zero_applicable_provenance",
                make_receipt(
                    audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
                    correspondence_provenance={"applicable": 0},
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_none_applicable_provenance",
                make_receipt(
                    audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
                    correspondence_provenance={"applicable": None},
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_string_applicable_provenance",
                make_receipt(
                    audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
                    correspondence_provenance={"applicable": "false"},
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "unknown_root",
                make_receipt(
                    audit={"canonicalRoot": "Trusted.MirSemantics.CrateTheoremV2"},
                    correspondence_provenance=inapplicable,
                ),
                "canonicalRoot=",
            ),
        ]
        for label, payload, needle in bad_cases:
            with self.subTest(case=label):
                with self.assertRaisesRegex(RuntimeError, needle):
                    verify_zerocopy.validate_receipt(
                        "05_unit", 0, json.dumps(payload), "", ["util::macros::__unsafe"]
                    )

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

    def test_discover_units_accepts_instantiations_only_and_mixed_scopes(self):
        valid_scopes = [
            {
                "kind": "selected_unit",
                "roots": [],
                "instantiations": [
                    {"path": "foo", "args": ["u8"]},
                    {"path": "bar", "args": ["'static", "core::num::NonZero<u16>"]},
                ],
            },
            {
                "kind": "selected_unit",
                "roots": ["baz"],
                "instantiations": [{"path": "foo", "args": ["u8"]}],
            },
            {
                "kind": "selected_unit",
                "roots": [],
                "instantiations": [{"path": "lifetime_only", "args": []}],
            },
            {
                "kind": "selected_unit",
                "roots": ["baz"],
                "instantiations": [],
            },
        ]
        for idx, scope in enumerate(valid_scopes):
            with self.subTest(idx=idx), tempfile.TemporaryDirectory() as tmp:
                proofs_dir, src_dir, unit = make_proof_tree(Path(tmp))
                req = json.loads((unit / "request.json").read_text(encoding="utf-8"))
                req["scope"] = scope
                (unit / "request.json").write_text(json.dumps(req), encoding="utf-8")
                discovered = verify_zerocopy.discover_units(proofs_dir, src_dir)
                self.assertEqual(len(discovered), 1)
                self.assertEqual(discovered[0][1]["scope"], scope)

    def test_discover_units_rejects_empty_and_malformed_instantiations(self):
        invalid_scopes = [
            ("empty_omitted", {"kind": "selected_unit", "roots": []}),
            ("empty_both", {"kind": "selected_unit", "roots": [], "instantiations": []}),
            ("dup_roots", {"kind": "selected_unit", "roots": ["a", "a"]}),
            (
                "inst_null",
                {"kind": "selected_unit", "roots": ["a"], "instantiations": None},
            ),
            (
                "inst_not_dict",
                {"kind": "selected_unit", "roots": [], "instantiations": ["foo"]},
            ),
            (
                "inst_empty_path",
                {
                    "kind": "selected_unit",
                    "roots": [],
                    "instantiations": [{"path": "", "args": ["u8"]}],
                },
            ),
            (
                "inst_missing_args",
                {"kind": "selected_unit", "roots": [], "instantiations": [{"path": "foo"}]},
            ),
            (
                "inst_empty_arg",
                {
                    "kind": "selected_unit",
                    "roots": [],
                    "instantiations": [{"path": "foo", "args": [""]}],
                },
            ),
            (
                "inst_args_not_list",
                {
                    "kind": "selected_unit",
                    "roots": [],
                    "instantiations": [{"path": "foo", "args": "u8"}],
                },
            ),
            (
                "inst_arg_non_str",
                {
                    "kind": "selected_unit",
                    "roots": [],
                    "instantiations": [{"path": "foo", "args": [1]}],
                },
            ),
            (
                "inst_extra_key",
                {
                    "kind": "selected_unit",
                    "roots": [],
                    "instantiations": [{"path": "foo", "args": ["u8"], "extra": 1}],
                },
            ),
            (
                "scope_extra_key",
                {"kind": "selected_unit", "roots": ["a"], "extra": 1},
            ),
            (
                "dup_inst",
                {
                    "kind": "selected_unit",
                    "roots": [],
                    "instantiations": [
                        {"path": "foo", "args": ["u8"]},
                        {"path": "foo", "args": ["u8"]},
                    ],
                },
            ),
        ]
        for label, scope in invalid_scopes:
            with self.subTest(case=label), tempfile.TemporaryDirectory() as tmp:
                proofs_dir, src_dir, unit = make_proof_tree(Path(tmp))
                req = json.loads((unit / "request.json").read_text(encoding="utf-8"))
                req["scope"] = scope
                (unit / "request.json").write_text(json.dumps(req), encoding="utf-8")
                with self.assertRaises(RuntimeError):
                    verify_zerocopy.discover_units(proofs_dir, src_dir)

    def test_validate_receipt_binds_roots_and_instantiations_and_selected(self):
        expected_insts = [
            {"path": "b", "args": ["u8"]},
            {"path": "a", "args": ["bool"]},
        ]
        inst_only_receipt = make_receipt(
            scope={
                "kind": "selected_unit",
                "roots": [],
                "instantiations": [
                    {"path": "a", "args": ["bool"]},
                    {"path": "b", "args": ["u8"]},
                ],
            }
        )
        parsed = verify_zerocopy.validate_receipt(
            "01_unit", 0, json.dumps(inst_only_receipt), "", [], expected_insts
        )
        self.assertEqual(parsed["status"], "selected_unit_verified")

        mixed_receipt = make_receipt(
            scope={
                "kind": "selected_unit",
                "roots": ["r"],
                "instantiations": [{"path": "a", "args": ["u16"]}],
            }
        )
        verify_zerocopy.validate_receipt(
            "01_unit",
            0,
            json.dumps(mixed_receipt),
            "",
            ["r"],
            [{"path": "a", "args": ["u16"]}],
        )

        # Explicitly empty `instantiations: []` in request matches omitted key
        # from `cargo-anneal`'s `skip_serializing_if = "BTreeSet::is_empty"`.
        verify_zerocopy.validate_receipt(
            "01_unit", 0, json.dumps(make_receipt()), "", ["util::macros::__unsafe"], []
        )

        omitted_selected = make_receipt()
        del omitted_selected["selected"]

        bad_cases = [
            (
                "omitted_selected",
                ["util::macros::__unsafe"],
                None,
                omitted_selected,
                "selected=None",
            ),
            (
                "dropped_all_insts",
                ["r"],
                [{"path": "a", "args": ["u8"]}],
                make_receipt(scope={"kind": "selected_unit", "roots": ["r"]}),
                "scope mismatch",
            ),
            (
                "dropped_one_inst",
                [],
                expected_insts,
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": [],
                        "instantiations": [{"path": "a", "args": ["bool"]}],
                    }
                ),
                "scope mismatch",
            ),
            (
                "changed_arg",
                [],
                [{"path": "a", "args": ["bool"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": [],
                        "instantiations": [{"path": "a", "args": ["u8"]}],
                    }
                ),
                "scope mismatch",
            ),
            (
                "changed_path",
                [],
                [{"path": "a", "args": ["bool"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": [],
                        "instantiations": [{"path": "c", "args": ["bool"]}],
                    }
                ),
                "scope mismatch",
            ),
            (
                "extra_inst",
                [],
                [{"path": "a", "args": ["bool"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": [],
                        "instantiations": [
                            {"path": "a", "args": ["bool"]},
                            {"path": "b", "args": ["u8"]},
                        ],
                    }
                ),
                "scope mismatch",
            ),
            (
                "dup_inst_in_receipt",
                [],
                [{"path": "a", "args": ["bool"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": [],
                        "instantiations": [
                            {"path": "a", "args": ["bool"]},
                            {"path": "a", "args": ["bool"]},
                        ],
                    }
                ),
                "scope mismatch",
            ),
            (
                "unexpected_inst_for_root_only",
                ["util::macros::__unsafe"],
                [],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": ["util::macros::__unsafe"],
                        "instantiations": [{"path": "a", "args": ["u8"]}],
                    }
                ),
                "scope mismatch",
            ),
            (
                "empty_selected",
                ["util::macros::__unsafe"],
                [],
                make_receipt(selected=[]),
                "selected=\\[\\]",
            ),
            (
                "null_selected",
                ["util::macros::__unsafe"],
                [],
                make_receipt(selected=None),
                "selected=None",
            ),
            (
                "non_list_selected",
                ["util::macros::__unsafe"],
                None,
                make_receipt(selected={"path": "util::macros::__unsafe"}),
                "selected=",
            ),
            (
                "selected_null_entry",
                ["util::macros::__unsafe"],
                None,
                make_receipt(selected=[None]),
                "selected=",
            ),
            (
                "selected_string_entry",
                ["util::macros::__unsafe"],
                None,
                make_receipt(selected=["util::macros::__unsafe"]),
                "selected=",
            ),
            (
                "selected_missing_field",
                ["util::macros::__unsafe"],
                None,
                make_receipt(selected=[{"def_id": 0, "path": "x"}]),
                "selected=",
            ),
            (
                "selected_extra_field",
                ["util::macros::__unsafe"],
                None,
                make_receipt(
                    selected=[
                        {"def_id": 0, "path": "x", "body_index": 0, "x": 1}
                    ]
                ),
                "selected=",
            ),
            (
                "selected_bool_def_id",
                ["util::macros::__unsafe"],
                None,
                make_receipt(
                    selected=[{"def_id": True, "path": "x", "body_index": 0}]
                ),
                "selected=",
            ),
            (
                "selected_neg_body_index",
                ["util::macros::__unsafe"],
                None,
                make_receipt(
                    selected=[{"def_id": 0, "path": "x", "body_index": -1}]
                ),
                "selected=",
            ),
            (
                "selected_empty_path",
                ["util::macros::__unsafe"],
                None,
                make_receipt(
                    selected=[{"def_id": 0, "path": "", "body_index": 0}]
                ),
                "selected=",
            ),
            (
                "wrong_scope_kind_with_roots",
                ["util::macros::__unsafe"],
                None,
                make_receipt(
                    scope={
                        "kind": "crate",
                        "roots": ["util::macros::__unsafe"],
                    }
                ),
                "scope mismatch",
            ),
            (
                "changed_root",
                ["util::macros::__unsafe"],
                None,
                make_receipt(
                    scope={"kind": "selected_unit", "roots": ["other::item"]}
                ),
                "scope mismatch",
            ),
            (
                "dropped_root",
                ["r1", "r2"],
                None,
                make_receipt(scope={"kind": "selected_unit", "roots": ["r1"]}),
                "scope mismatch",
            ),
            (
                "extra_root",
                ["r1"],
                None,
                make_receipt(
                    scope={"kind": "selected_unit", "roots": ["r1", "r2"]}
                ),
                "scope mismatch",
            ),
            (
                "mixed_dropped_root",
                ["r1", "r2"],
                [{"path": "a", "args": ["u8"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": ["r1"],
                        "instantiations": [{"path": "a", "args": ["u8"]}],
                    }
                ),
                "scope mismatch",
            ),
            (
                "mixed_extra_root",
                ["r1"],
                [{"path": "a", "args": ["u8"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": ["r1", "r2"],
                        "instantiations": [{"path": "a", "args": ["u8"]}],
                    }
                ),
                "scope mismatch",
            ),
        ]
        for label, exp_roots, exp_insts, payload, needle in bad_cases:
            with self.subTest(case=label):
                with self.assertRaisesRegex(RuntimeError, needle):
                    verify_zerocopy.validate_receipt(
                        "01_unit", 0, json.dumps(payload), "", exp_roots, exp_insts
                    )

    def test_main_runs_instantiation_only_unit_and_records_scope(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proofs_dir, src_dir, unit = make_proof_tree(root)
            scope = {
                "kind": "selected_unit",
                "roots": [],
                "instantiations": [{"path": "id", "args": ["u8"]}],
            }
            req = json.loads((unit / "request.json").read_text(encoding="utf-8"))
            req["scope"] = scope
            (unit / "request.json").write_text(json.dumps(req), encoding="utf-8")

            fake_cli = root / "cargo-anneal"
            fake_cap = root / "anneal-rustc-capture"
            fake_lean = root / "lean"
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            for bin_path in (fake_cap, fake_lean):
                bin_path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                bin_path.chmod(0o755)
            payload_json = json.dumps(make_receipt(scope=scope))
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
            self.assertEqual(summary["units"]["01_unit"]["scope"], scope)


if __name__ == "__main__":
    unittest.main()
