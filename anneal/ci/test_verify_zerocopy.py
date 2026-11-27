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
import re
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

import render_correspondence_provenance
import verify_zerocopy


SHA_A = "a" * 64
SHA_B = "b" * 64
SHA_C = "c" * 64
SHA_D = "d" * 64
SHA_E = "e" * 64
SHA_F = "f" * 64


def make_v1_provenance(**overrides):
    prov = {
        "schema_version": 1,
        "upstream_repository": "https://github.com/proofs-rs/lean-miri",
        "upstream_commit": "c92d1d97",
        "upstream_lean_toolchain": "leanprover/lean4:v4.35.0",
        "build_lean_toolchain": "leanprover/lean4:v4.34.1",
        "upstream_pin_sha256": SHA_A,
        "sysroot_foundation_manifest_sha256": SHA_B,
        "patched_files": [],
        "minirust_upstream": make_minirust_upstream(),
        "correspondence_adapters": {
            "trusted/correspondence/Trusted/Correspondence.lean": SHA_C,
        },
        "correspondence_proofs": {
            "correspondence/Anneal/MirCorrespondenceProof.lean": SHA_D,
        },
        "trusted_lean": {
            "trusted/lean/Trusted/MirSemantics.lean": SHA_E,
        },
        "note": "pass2",
    }
    prov.update(overrides)
    return prov


def make_v3_provenance(**overrides):
    prov = make_v1_provenance(
        schema_version=3,
        claim_kind="exact_refines",
        permitted_axioms=["Classical.choice", "Quot.sound", "propext"],
        model_system_relation={
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "bidirectional",
            "licensed_claim_shapes": ["forall_safety"],
        },
        tcb_shims=[],
        taint_reasons=[],
        qualifiers={
            "choice_total": True,
            "assumed_seams": [],
            "scope_kind": "full_gate",
        },
    )
    prov.update(overrides)
    return prov


def make_minirust_upstream(**overrides):
    mr = {
        "upstream_repository": "https://github.com/minirust/minirust",
        "upstream_commit": "d821c6e3",
        "upstream_pin_sha256": SHA_A,
        "tarball_sha256": SHA_B,
        "manifest_sha256": SHA_C,
        "file_count": 1,
        "files": {"spec/lang/syntax.md": SHA_D},
    }
    mr.update(overrides)
    return mr


DEFAULT_CONFIG = {
    "source_root": "../../src",
    "crate_root": "lib.rs",
    "crate_name": "zerocopy",
    "crate_type": "lib",
    "panic": "unwind",
    "edition": "2021",
    "target": "x86_64-unknown-linux-gnu",
    "cfg": ["no_zerocopy_allocator_api_1_100_0"],
    "env": {"CARGO_PKG_VERSION": "0.8.64"},
    "source_files": ["lib.rs"],
}


def make_receipt(**overrides):
    receipt = {
        "schema_version": 3,
        "status": "selected_unit_verified",
        "taint_reasons": [],
        "elaboration_sandbox": "linux_bwrap",
        "assumptions": [
            "faithful pinned compiler capture",
            "experimental pointer-free MIR semantics",
            "Lean kernel and admitted foundation",
            "intact compiler and verification environment",
        ],
        "deferred": [
            "complete review-surface reporting",
            "source-to-deployed-binary correspondence",
        ],
        "spec_warnings": [],
        "correspondence_provenance": make_v1_provenance(),
        "scope": {
            "kind": "selected_unit",
            "roots": ["util::macros::__unsafe"],
        },
        "configuration": {
            "crate_root": "lib.rs",
            "crate_name": "zerocopy",
            "crate_type": "lib",
            "panic": "unwind",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": ["no_zerocopy_allocator_api_1_100_0"],
            "env": {"CARGO_PKG_VERSION": "0.8.64"},
            "opt_level": 0,
            "debug_assertions": False,
            "overflow_checks": False,
            "mir_preserve_ub": True,
            "pointer_bits": 64,
            "endian": "little",
            "declared_source_files": ["lib.rs"],
        },
        "request_sha256": "req-digest",
        "capture_sha256": "cap-digest",
        "specification_manifest_sha256": "spec-digest",
        "model_manifest_sha256": "model-digest",
        "selected": [
            {"def_id": 0, "path": "util::macros::__unsafe", "body_index": 0}
        ],
        "sources": [
            {
                "relative_path": "lib.rs",
                "sha256": (
                    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7"
                    "852b855"
                ),
            }
        ],
        "timing_ms": {"total": 100},
        "audit": {
            "replay": True,
            "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
            "subject": "Captured.program",
            "expected": "Expected.claim",
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "exactType": True,
            "replayedDeclarations": 10,
            "checkedAlternateProofs": 0,
            "sorryDeclarations": [],
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
        elif key == "configuration":
            receipt["configuration"].update(val)
        else:
            receipt[key] = val
    return receipt


def real_tmp_root(tmp: str) -> Path:
    return Path(tmp).resolve(strict=True)


def make_unit_request(
    *,
    roots=None,
    instantiations=None,
    cfg=None,
    env=None,
    crate_root="lib.rs",
    crate_name="zerocopy",
    overflow_checks=None,
    source_files=None,
    specification="Spec.specs",
    theorem="Proof.verify",
    sources=None,
):
    scope = {
        "kind": "selected_unit",
        "roots": ["util::macros::__unsafe"] if roots is None else roots,
    }
    if instantiations is not None:
        scope["instantiations"] = instantiations
    compilation = {
        "source_root": "../../src",
        "crate_root": crate_root,
        "crate_name": crate_name,
        "edition": "2021",
        "target": "x86_64-unknown-linux-gnu",
        "cfg": (
            ["no_zerocopy_allocator_api_1_100_0"] if cfg is None else cfg
        ),
        "env": {"CARGO_PKG_VERSION": "0.8.64"} if env is None else env,
        "source_files": ["lib.rs"] if source_files is None else source_files,
    }
    if overflow_checks is not None:
        compilation["overflow_checks"] = overflow_checks
    return {
        "schema_version": 1,
        "compilation": compilation,
        "scope": scope,
        "proof": {
            "source_root": ".",
            "specification": specification,
            "theorem": theorem,
            "sources": (
                [
                    {
                        "module": "Spec",
                        "path": "Spec.lean",
                        "role": "specification",
                    },
                    {"module": "Proof", "path": "Proof.lean", "role": "proof"},
                ]
                if sources is None
                else sources
            ),
        },
    }


def make_proof_tree(root: Path, *, unit_names=("01_unit",)):
    root = root.resolve(strict=True)
    zc_dir = root / "zerocopy"
    src_dir = zc_dir / "src"
    src_dir.mkdir(parents=True)
    (src_dir / "lib.rs").write_text("", encoding="utf-8")
    (zc_dir / "Cargo.toml").write_text(
        '[package]\nname = "zerocopy"\nversion = "0.8.64"\n',
        encoding="utf-8",
    )

    proofs_dir = zc_dir / "proofs"
    proofs_dir.mkdir(parents=True)
    (proofs_dir / "README.md").write_text("# Proofs\n", encoding="utf-8")

    first_unit = None
    for name in unit_names:
        unit = proofs_dir / name
        unit.mkdir()
        (unit / "Spec.lean").write_text(
            "prelude\ndef specs : Specs := ⟨(), ()⟩\n", encoding="utf-8"
        )
        (unit / "Proof.lean").write_text(
            "prelude\nimport Anneal.Wp\n", encoding="utf-8"
        )
        (unit / "request.json").write_text(
            json.dumps(make_unit_request()),
            encoding="utf-8",
        )
        if first_unit is None:
            first_unit = unit

    return proofs_dir, src_dir, first_unit


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

            for stray_name in ("lakefile.toml", "MANIFEST.json"):
                stray_top = proofs_dir / stray_name
                stray_top.write_text("", encoding="utf-8")
                try:
                    with self.assertRaisesRegex(
                        RuntimeError, "unexpected top-level"
                    ):
                        verify_zerocopy.discover_units(proofs_dir, src_dir)
                finally:
                    stray_top.unlink()

    def test_discover_units_rejects_bad_source_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            other_src = root / "zerocopy/other_src"
            other_src.mkdir(parents=True)
            (other_src / "lib.rs").write_text("", encoding="utf-8")
            proofs_dir, src_dir, unit = make_proof_tree(root)
            req = json.loads((unit / "request.json").read_text(encoding="utf-8"))
            req["compilation"]["source_root"] = "../../other_src"
            (unit / "request.json").write_text(json.dumps(req), encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "does not resolve"):
                verify_zerocopy.discover_units(proofs_dir, src_dir)

    def test_discover_units_enforces_request_and_consistency(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            proofs_dir, src_dir, unit = make_proof_tree(
                root, unit_names=("01_unit", "02_unit")
            )

            # 1. Selecting an unknown `--unit` or symlinked/missing
            # `request.json` fails closed.
            with self.assertRaisesRegex(
                RuntimeError, "requested proof unit\\(s\\) not found"
            ):
                verify_zerocopy.discover_units(
                    proofs_dir, src_dir, selected_units=["99_unknown"]
                )

            req_path = unit / "request.json"
            saved_req = req_path.read_text(encoding="utf-8")
            alt_req = root / "alt_request.json"
            alt_req.write_text(saved_req, encoding="utf-8")
            req_path.unlink()
            with self.assertRaisesRegex(RuntimeError, "missing request.json"):
                verify_zerocopy.discover_units(proofs_dir, src_dir)
            req_path.symlink_to(alt_req)
            with self.assertRaisesRegex(
                RuntimeError, "symlink disallowed in proof unit"
            ):
                verify_zerocopy.discover_units(proofs_dir, src_dir)
            req_path.unlink()
            req_path.write_text(saved_req, encoding="utf-8")

            # 2. Request validation catches invalid fields, roles, `Spec*.lean`
            # filename rules, and duplicate JSON keys.
            override_req = make_unit_request()
            override_req["proof"]["specification_module"] = "WeakSpec"
            dup_mod_req = make_unit_request(
                sources=[
                    {
                        "module": "Spec",
                        "path": "Spec.lean",
                        "role": "specification",
                    },
                    {"module": "Spec", "path": "Proof.lean", "role": "proof"},
                ]
            )
            dup_path_req = make_unit_request(
                sources=[
                    {
                        "module": "Spec",
                        "path": "Spec.lean",
                        "role": "specification",
                    },
                    {"module": "Proof", "path": "Spec.lean", "role": "proof"},
                ]
            )
            spec_only_req = make_unit_request(
                sources=[
                    {
                        "module": "Spec",
                        "path": "Spec.lean",
                        "role": "specification",
                    },
                    {
                        "module": "OtherProof",
                        "path": "Proof.lean",
                        "role": "proof",
                    },
                ]
            )
            spec_wrong_role_req = make_unit_request(
                sources=[
                    {
                        "module": "Spec",
                        "path": "Spec.lean",
                        "role": "proof",
                    },
                    {
                        "module": "Proof",
                        "path": "Proof.lean",
                        "role": "proof",
                    },
                ]
            )
            unknown_field_req = make_unit_request()
            unknown_field_req["compilation"]["extra_flag"] = True
            bad_cfg_type_req = make_unit_request()
            bad_cfg_type_req["compilation"]["cfg"] = None
            non_dict_proof_req = make_unit_request()
            non_dict_proof_req["proof"] = "x"
            bool_schema_req = make_unit_request()
            bool_schema_req["schema_version"] = True
            float_schema_req = make_unit_request()
            float_schema_req["schema_version"] = 1.0
            list_crate_type_req = make_unit_request()
            list_crate_type_req["compilation"]["crate_type"] = ["lib"]
            missing_pkg_ver_req = make_unit_request(env={})
            bad_overflow_req = make_unit_request(overflow_checks="yes")
            omitted_edition_req = make_unit_request()
            del omitted_edition_req["compilation"]["edition"]

            bad_single_requests = [
                (
                    "omitted_edition",
                    omitted_edition_req,
                    "compilation\\.edition must be non-empty",
                ),
                (
                    "crate_root",
                    make_unit_request(crate_root="util/mod.rs"),
                    "compilation\\.crate_root must belong",
                ),
                (
                    "spec_outside_spec_role",
                    spec_wrong_role_req,
                    "role 'specification'",
                ),
                (
                    "missing_proof_role_mod",
                    spec_only_req,
                    "proof\\.theorem module",
                ),
                (
                    "spec_mod_override",
                    override_req,
                    "specification_module/theorem_module",
                ),
                ("dup_module", dup_mod_req, "duplicate proof module"),
                ("dup_path", dup_path_req, "duplicate proof source path"),
                ("unknown_comp_field", unknown_field_req, "unexpected field"),
                ("null_cfg", bad_cfg_type_req, "cfg must be a list"),
                (
                    "non_bool_overflow_checks",
                    bad_overflow_req,
                    "overflow_checks must be a boolean",
                ),
                (
                    "list_crate_type",
                    list_crate_type_req,
                    "crate_type must be one of",
                ),
                (
                    "missing_cargo_pkg_version",
                    missing_pkg_ver_req,
                    "CARGO_PKG_VERSION must be non-empty",
                ),
                (
                    "non_dict_proof",
                    non_dict_proof_req,
                    "proof must be a JSON object",
                ),
                (
                    "bool_schema_version",
                    bool_schema_req,
                    "unsupported request schema_version",
                ),
                (
                    "float_schema_version",
                    float_schema_req,
                    "unsupported request schema_version",
                ),
            ]
            for label, bad_req, regex in bad_single_requests:
                with self.subTest(case=label):
                    req_path.write_text(json.dumps(bad_req), encoding="utf-8")
                    with self.assertRaisesRegex(RuntimeError, regex):
                        verify_zerocopy.discover_units(proofs_dir, src_dir)
            req_path.write_text(saved_req, encoding="utf-8")

            # 3. Cross-unit `compilation` consistency rejects divergent
            # compiler flags, environment, crate_root, or omitted `edition`.
            unit_02_req_path = proofs_dir / "02_unit/request.json"
            saved_req_02 = unit_02_req_path.read_text(encoding="utf-8")
            edition_drift_req = make_unit_request()
            edition_drift_req["compilation"]["edition"] = "2024"
            for label, bad_req_02 in [
                ("cfg_drift", make_unit_request(cfg=["kani"])),
                ("env_drift", make_unit_request(env={"CARGO_PKG_VERSION": "0.0.0"})),
                ("crate_name_drift", make_unit_request(crate_name="other")),
                ("overflow_checks_drift", make_unit_request(overflow_checks=True)),
                ("edition_drift", edition_drift_req),
            ]:
                with self.subTest(cross_unit_case=label):
                    unit_02_req_path.write_text(
                        json.dumps(bad_req_02), encoding="utf-8"
                    )
                    with self.assertRaisesRegex(
                        RuntimeError, "compilation config inconsistent with 01_unit"
                    ):
                        verify_zerocopy.discover_units(proofs_dir, src_dir)
            unit_02_req_path.write_text(saved_req_02, encoding="utf-8")

            with self.subTest(case="spec_rename_outside_spec_glob"):
                (unit / "Semantics.lean").write_text(
                    "prelude\ndef specs : Specs := ⟨(), ()⟩\n",
                    encoding="utf-8",
                )
                try:
                    renamed_spec_req = make_unit_request(
                        sources=[
                            {
                                "module": "Semantics",
                                "path": "Semantics.lean",
                                "role": "specification",
                            },
                            {
                                "module": "Proof",
                                "path": "Proof.lean",
                                "role": "proof",
                            },
                        ]
                    )
                    req_path.write_text(
                        json.dumps(renamed_spec_req), encoding="utf-8"
                    )
                    with self.assertRaisesRegex(RuntimeError, "Spec\\*\\.lean"):
                        verify_zerocopy.discover_units(proofs_dir, src_dir)
                finally:
                    (unit / "Semantics.lean").unlink()

            with self.subTest(case="extra_proof_helper_module_allowed"):
                (unit / "AutoScaffold.lean").write_text(
                    "prelude\nimport Anneal.Scalar\n", encoding="utf-8"
                )
                try:
                    helper_req = make_unit_request(
                        sources=[
                            {
                                "module": "Spec",
                                "path": "Spec.lean",
                                "role": "specification",
                            },
                            {
                                "module": "AutoScaffold",
                                "path": "AutoScaffold.lean",
                                "role": "proof",
                            },
                            {
                                "module": "Proof",
                                "path": "Proof.lean",
                                "role": "proof",
                            },
                        ]
                    )
                    req_path.write_text(json.dumps(helper_req), encoding="utf-8")
                    units = verify_zerocopy.discover_units(proofs_dir, src_dir)
                    self.assertEqual(
                        [u.name for u, _ in units], ["01_unit", "02_unit"]
                    )
                finally:
                    (unit / "AutoScaffold.lean").unlink()

            with self.subTest(case="extra_spec_helper_module_allowed"):
                (unit / "SpecAux.lean").write_text(
                    "prelude\n", encoding="utf-8"
                )
                try:
                    extra_spec_req = make_unit_request(
                        sources=[
                            {
                                "module": "Spec",
                                "path": "Spec.lean",
                                "role": "specification",
                            },
                            {
                                "module": "SpecAux",
                                "path": "SpecAux.lean",
                                "role": "specification",
                            },
                            {
                                "module": "Proof",
                                "path": "Proof.lean",
                                "role": "proof",
                            },
                        ]
                    )
                    req_path.write_text(
                        json.dumps(extra_spec_req), encoding="utf-8"
                    )
                    units = verify_zerocopy.discover_units(proofs_dir, src_dir)
                    self.assertEqual(
                        [u.name for u, _ in units], ["01_unit", "02_unit"]
                    )
                finally:
                    (unit / "SpecAux.lean").unlink()

            with self.subTest(case="duplicate_json_key_in_request"):
                req_path.write_text(
                    '{"schema_version": 1, "schema_version": 2}',
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(RuntimeError, "duplicate JSON key"):
                    verify_zerocopy.discover_units(proofs_dir, src_dir)
            req_path.write_text(saved_req, encoding="utf-8")

            # 4. Dynamic `zerocopy/src/**/*.rs` completeness, `doctests.rs`
            # exclusion, and `Cargo.toml` version checks.
            (src_dir / "unlisted.rs").write_text("data\n", encoding="utf-8")
            try:
                with self.assertRaisesRegex(
                    RuntimeError, "compilation\\.source_files mismatch"
                ):
                    verify_zerocopy.discover_units(proofs_dir, src_dir)
            finally:
                (src_dir / "unlisted.rs").unlink()

            (src_dir / "doctests.rs").write_text("fn d() {}\n", encoding="utf-8")
            try:
                self.assertEqual(
                    [
                        u.name
                        for u, _ in verify_zerocopy.discover_units(
                            proofs_dir, src_dir
                        )
                    ],
                    ["01_unit", "02_unit"],
                )
                req_path.write_text(
                    json.dumps(
                        make_unit_request(
                            source_files=["doctests.rs", "lib.rs"]
                        )
                    ),
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(
                    RuntimeError, "compilation\\.source_files mismatch"
                ):
                    verify_zerocopy.discover_units(proofs_dir, src_dir)
            finally:
                req_path.write_text(saved_req, encoding="utf-8")
                (src_dir / "doctests.rs").unlink()

            (root / "zerocopy/Cargo.toml").write_text(
                "[package]\nname = 'zerocopy'\nversion = '0.8.65'\n",
                encoding="utf-8",
            )
            discovered_bump = verify_zerocopy.discover_units(
                proofs_dir, src_dir
            )
            self.assertEqual(
                [u.name for u, _ in discovered_bump], ["01_unit", "02_unit"]
            )
            self.assertEqual(
                verify_zerocopy._extract_zerocopy_crate_version(
                    root / "zerocopy/Cargo.toml"
                ),
                "0.8.65",
            )

            # Workspace-inherited `version.workspace = true` resolves cleanly,
            # missing static version returns None without blocking discovery,
            # and invalid TOML / symlinked `Cargo.toml` fails closed.
            (root / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["zerocopy"]\n'
                '[workspace.package]\nversion = "0.9.1"\n',
                encoding="utf-8",
            )
            (root / "zerocopy/Cargo.toml").write_text(
                '[package]\nname = "zerocopy"\nversion.workspace = true\n',
                encoding="utf-8",
            )
            self.assertEqual(
                verify_zerocopy._extract_zerocopy_crate_version(
                    root / "zerocopy/Cargo.toml"
                ),
                "0.9.1",
            )
            (root / "Cargo.toml").unlink()
            # Explicit `package.workspace` sibling workspace root resolves
            # cleanly even outside the crate's ancestor directory chain.
            sibling_ws = root / "sibling_ws"
            sibling_ws.mkdir()
            (sibling_ws / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["../zerocopy"]\n'
                '[workspace.package]\nversion = "0.9.2"\n',
                encoding="utf-8",
            )
            (root / "zerocopy/Cargo.toml").write_text(
                '[package]\nname = "zerocopy"\n'
                'version.workspace = true\nworkspace = "../sibling_ws"\n',
                encoding="utf-8",
            )
            self.assertEqual(
                verify_zerocopy._extract_zerocopy_crate_version(
                    root / "zerocopy/Cargo.toml"
                ),
                "0.9.2",
            )
            (root / "zerocopy/Cargo.toml").write_text(
                '[package]\nname = "zerocopy"\n',
                encoding="utf-8",
            )
            self.assertIsNone(
                verify_zerocopy._extract_zerocopy_crate_version(
                    root / "zerocopy/Cargo.toml"
                )
            )
            self.assertEqual(
                len(verify_zerocopy.discover_units(proofs_dir, src_dir)), 2
            )
            (root / "zerocopy/Cargo.toml").write_text(
                "[package\nname = 'zerocopy'\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(RuntimeError, "invalid TOML"):
                verify_zerocopy._extract_zerocopy_crate_version(
                    root / "zerocopy/Cargo.toml"
                )
            sym_toml = root / "sym_Cargo.toml"
            sym_toml.symlink_to(root / "zerocopy/Cargo.toml")
            with self.assertRaisesRegex(RuntimeError, "symlink disallowed"):
                verify_zerocopy._extract_zerocopy_crate_version(sym_toml)

    def test_validate_receipt_accepts_clean_and_rejects_taint_or_axioms(self):
        good = make_receipt()
        parsed = verify_zerocopy.validate_receipt(
            "01_unit",
            0,
            json.dumps(good),
            "",
            ["util::macros::__unsafe"],
            expected_compilation=DEFAULT_CONFIG,
            expected_instantiations=[],
            expected_spec_decl="Spec.specs",
            expected_proof_thm="Proof.verify",
            expected_axioms=["propext"],
        )
        self.assertEqual(parsed["status"], "selected_unit_verified")

        staged_paths = make_receipt(
            configuration={
                "crate_root": "/tmp/anneal-work/rust/lib.rs",
                "declared_source_files": ["/tmp/anneal-work/rust/lib.rs"],
            }
        )
        parsed_staged = verify_zerocopy.validate_receipt(
            "01_unit",
            0,
            json.dumps(staged_paths),
            "",
            ["util::macros::__unsafe"],
            expected_compilation=DEFAULT_CONFIG,
            expected_instantiations=[],
            expected_spec_decl="Spec.specs",
            expected_proof_thm="Proof.verify",
        )
        self.assertEqual(parsed_staged["status"], "selected_unit_verified")

        overflow_cfg = dict(DEFAULT_CONFIG, overflow_checks=True)
        overflow_ok = make_receipt(configuration={"overflow_checks": True})
        self.assertEqual(
            verify_zerocopy.validate_receipt(
                "01_unit",
                0,
                json.dumps(overflow_ok),
                "",
                ["util::macros::__unsafe"],
                expected_compilation=overflow_cfg,
                expected_spec_decl="Spec.specs",
                expected_proof_thm="Proof.verify",
            )["status"],
            "selected_unit_verified",
        )
        with self.assertRaisesRegex(
            RuntimeError, "configuration\\.overflow_checks=False"
        ):
            verify_zerocopy.validate_receipt(
                "01_unit",
                0,
                json.dumps(good),
                "",
                ["util::macros::__unsafe"],
                expected_compilation=overflow_cfg,
                expected_spec_decl="Spec.specs",
                expected_proof_thm="Proof.verify",
            )

        with self.assertRaisesRegex(RuntimeError, "sources sha256 mismatch"):
            verify_zerocopy.validate_receipt(
                "01_unit",
                0,
                json.dumps(make_receipt(sources=[{"relative_path": "lib.rs", "sha256": "dead"}])),
                "",
                ["util::macros::__unsafe"],
                expected_compilation=DEFAULT_CONFIG,
                expected_source_hashes={
                    "lib.rs": (
                        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca49599"
                        "1b7852b855"
                    )
                },
            )

        # Per-unit `expected_axioms=[]` rejects `propext` even though `propext`
        # is globally allowed.
        with self.assertRaisesRegex(RuntimeError, "disallowed audit\\.axioms"):
            verify_zerocopy.validate_receipt(
                "01_unit",
                0,
                json.dumps(good),
                "",
                ["util::macros::__unsafe"],
                expected_axioms=[],
            )

        empty_digest = make_receipt(request_sha256="")
        empty_digest["audit"]["bindings"]["requestSha256"] = ""
        missing_digest = make_receipt()
        del missing_digest["model_manifest_sha256"]
        del missing_digest["audit"]["bindings"]["modelManifestSha256"]
        missing_warnings = make_receipt()
        del missing_warnings["spec_warnings"]

        bad_cases = [
            (
                "taint",
                make_receipt(taint_reasons=["unsandboxed_elaboration"]),
                "taint_reasons",
            ),
            (
                "sandbox",
                make_receipt(elaboration_sandbox="none"),
                "elaboration_sandbox",
            ),
            (
                "axioms",
                make_receipt(
                    audit={"axioms": ["propext", "Classical.choice"]}
                ),
                "axioms",
            ),
            ("axioms_non_str", make_receipt(audit={"axioms": [{}]}), "axioms"),
            (
                "axioms_dup",
                make_receipt(audit={"axioms": ["propext", "propext"]}),
                "axioms",
            ),
            ("exactType", make_receipt(audit={"exactType": False}), "exactType"),
            (
                "altProof",
                make_receipt(audit={"checkedAlternateProofs": 1}),
                "checkedAlternateProofs",
            ),
            (
                "replay_false",
                make_receipt(audit={"replay": False}),
                "audit\\.replay",
            ),
            (
                "replayed_zero",
                make_receipt(audit={"replayedDeclarations": 0}),
                "replayedDeclarations",
            ),
            (
                "audit_sorry",
                make_receipt(audit={"sorryDeclarations": ["Proof.hole"]}),
                "sorryDeclarations",
            ),
            (
                "audit_subject",
                make_receipt(audit={"subject": "Fake.program"}),
                "audit\\.subject",
            ),
            (
                "audit_expected",
                make_receipt(audit={"expected": "Fake.claim"}),
                "audit\\.expected",
            ),
            (
                "sorry",
                make_receipt(sorry_declarations=["foo"]),
                "sorry_declarations",
            ),
            ("status", make_receipt(status="proof_failed"), "status="),
            (
                "roots_str",
                make_receipt(
                    scope={"kind": "selected_unit", "roots": "not-a-list"}
                ),
                "scope mismatch",
            ),
            ("selected_drop", make_receipt(selected=[]), "selected mismatch"),
            (
                "selected_str",
                make_receipt(selected=["util::macros::__unsafe"]),
                "selected mismatch",
            ),
            (
                "selected_dup_idx",
                make_receipt(
                    selected=[
                        {
                            "def_id": 1,
                            "path": "util::macros::__unsafe",
                            "body_index": 0,
                        },
                        {
                            "def_id": 1,
                            "path": "util::macros::__unsafe",
                            "body_index": 0,
                        },
                    ]
                ),
                "selected mismatch",
            ),
            (
                "selected_bool_id",
                make_receipt(
                    selected=[
                        {
                            "def_id": True,
                            "path": "util::macros::__unsafe",
                            "body_index": 0,
                        }
                    ]
                ),
                "selected mismatch",
            ),
            (
                "sources_extra",
                make_receipt(
                    sources=[
                        {"relative_path": "lib.rs", "sha256": "src-digest"},
                        {"relative_path": "extra.rs", "sha256": "extra-digest"},
                    ]
                ),
                "sources mismatch",
            ),
            (
                "spec_warnings_nonempty",
                make_receipt(spec_warnings=[{"code": "trivial_property"}]),
                "spec_warnings",
            ),
            (
                "spec_warnings_missing",
                missing_warnings,
                "spec_warnings=None",
            ),
            (
                "cfg_mismatch",
                make_receipt(configuration={"cfg": ["kani"]}),
                "configuration\\.cfg",
            ),
            (
                "cfg_stdlib_crate",
                make_receipt(
                    configuration={"stdlib_crate": {"crate_type": "core"}}
                ),
                "unexpected configuration keys=\\['stdlib_crate'\\]",
            ),
            (
                "cfg_stdlib_crate_null",
                make_receipt(configuration={"stdlib_crate": None}),
                "unexpected configuration keys=\\['stdlib_crate'\\]",
            ),
            (
                "cfg_extra_key",
                make_receipt(configuration={"unreviewed_flag": True}),
                "unexpected configuration keys=\\['unreviewed_flag'\\]",
            ),
            (
                "cfg_dup",
                make_receipt(
                    configuration={
                        "cfg": [
                            "no_zerocopy_allocator_api_1_100_0",
                            "no_zerocopy_allocator_api_1_100_0",
                        ]
                    }
                ),
                "configuration\\.cfg",
            ),
            (
                "crate_root_mismatch",
                make_receipt(
                    configuration={"crate_root": "/tmp/work/rust/other.rs"}
                ),
                "configuration\\.crate_root",
            ),
            (
                "decl_files_mismatch",
                make_receipt(
                    configuration={
                        "declared_source_files": ["/tmp/work/rust/lib.rs"]
                    }
                ),
                "configuration\\.declared_source_files",
            ),
            (
                "float_schema_ver",
                make_receipt(schema_version=3.0),
                "schema_version",
            ),
            (
                "bool_alt_proofs",
                make_receipt(audit={"checkedAlternateProofs": False}),
                "checkedAlternateProofs",
            ),
            (
                "spec_decl_swap",
                make_receipt(audit={"specification": "WeakSpec.specs"}),
                "audit\\.specification",
            ),
            (
                "thm_swap",
                make_receipt(audit={"theorem": "Proof.other"}),
                "audit\\.theorem",
            ),
            ("deferred_null", make_receipt(deferred=None), "deferred=None"),
            (
                "deferred_str",
                make_receipt(deferred="hostile"),
                "deferred='hostile'",
            ),
            ("deferred_dict", make_receipt(deferred={}), "deferred=\\{\\}"),
            (
                "deferred_non_str_elem",
                make_receipt(deferred=[{}]),
                "deferred=\\[\\{\\}\\]",
            ),
            (
                "opt_level",
                make_receipt(configuration={"opt_level": 3}),
                "configuration\\.opt_level",
            ),
            (
                "mir_preserve_ub",
                make_receipt(configuration={"mir_preserve_ub": False}),
                "configuration\\.mir_preserve_ub",
            ),
            (
                "overflow_checks",
                make_receipt(configuration={"overflow_checks": True}),
                "configuration\\.overflow_checks",
            ),
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
                        "01_unit",
                        rc,
                        json.dumps(payload),
                        "",
                        ["util::macros::__unsafe"],
                        expected_compilation=DEFAULT_CONFIG,
                        expected_instantiations=[],
                        expected_spec_decl="Spec.specs",
                        expected_proof_thm="Proof.verify",
                    )

        # Duplicate keys in receipt JSON fail closed.
        with self.assertRaisesRegex(RuntimeError, "duplicate JSON key"):
            verify_zerocopy.validate_receipt(
                "01_unit",
                0,
                '{"status": "proof_failed", "status": "selected_unit_verified"}',
                "",
                ["util::macros::__unsafe"],
            )

    def test_main_runs_with_mocked_cli_and_writes_summary(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            proofs_dir, src_dir, _ = make_proof_tree(root)
            fake_cli = root / "cargo-anneal"
            fake_cap = root / "anneal-rustc-capture"
            fake_lean = root / "lean"
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            fake_lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_lean.chmod(0o755)
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import json, sys\n"
                "from pathlib import Path\n"
                "args = sys.argv[1:]\n"
                "out_dir = Path(args[args.index('--out-dir') + 1])\n"
                "out_dir.mkdir(parents=True, exist_ok=False)\n"
                "(out_dir / 'capture.json').write_text(\n"
                "    json.dumps({'selected': [{'def_id': 0, 'path': 'id::<u8>', 'body_index': 0}]})\n"
                ")\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)
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
            summary = json.loads(
                (artifacts / "summary.json").read_text(encoding="utf-8")
            )
            self.assertEqual(summary["unit_count"], 1)
            self.assertIn("01_unit", summary["units"])
            unit_rec = summary["units"]["01_unit"]
            expected_receipt = make_receipt()
            self.assertEqual(unit_rec["profile"], 1)
            self.assertEqual(
                unit_rec["canonical_root"],
                expected_receipt["audit"]["canonicalRoot"],
            )
            self.assertEqual(
                unit_rec["taint_reasons"], expected_receipt["taint_reasons"]
            )
            self.assertEqual(
                unit_rec["assumptions"], expected_receipt["assumptions"]
            )
            self.assertEqual(unit_rec["deferred"], expected_receipt["deferred"])
            self.assertEqual(
                unit_rec["spec_warnings"], expected_receipt["spec_warnings"]
            )
            self.assertEqual(
                unit_rec["correspondence_provenance"],
                expected_receipt["correspondence_provenance"],
            )
            self.assertFalse(summary["crate_version_drift"])

            # Release version bump in `Cargo.toml` + omitted optional
            # `instantiations` succeed while recording `crate_version_drift`.
            (root / "zerocopy/Cargo.toml").write_text(
                '[package]\nname = "zerocopy"\nversion = "0.8.65"\n',
                encoding="utf-8",
            )
            artifacts_bump = root / "out_bump"
            err_buf = io.StringIO()
            with (
                contextlib.redirect_stdout(io.StringIO()),
                contextlib.redirect_stderr(err_buf),
            ):
                rc_bump = verify_zerocopy.main([
                    "--proofs-dir", str(proofs_dir),
                    "--src-dir", str(src_dir),
                    "--cli", str(fake_cli),
                    "--capture", str(fake_cap),
                    "--sysroot", str(fake_sys),
                    "--lean", str(fake_lean),
                    "--artifacts-dir", str(artifacts_bump),
                ])
            self.assertEqual(rc_bump, 0)
            bump_summary = json.loads(
                (artifacts_bump / "summary.json").read_text(encoding="utf-8")
            )
            self.assertTrue(bump_summary["crate_version_drift"])
            self.assertEqual(bump_summary["cargo_toml_version"], "0.8.65")
            self.assertIn("differs from request.json", err_buf.getvalue())

    def test_validate_receipt_profile_v2_root_requires_inapplicable_provenance(self):
        inapplicable = {"applicable": False, "reason": "Profile v1 only"}
        v2_assumptions = [
            "faithful pinned compiler capture",
            (
                "experimental Profile v2 MIR semantics: caller memory, "
                "single-level references and raw pointers, little-endian byte "
                "order, and no aliasing model (Stacked or Tree Borrows); "
                "raw-pointer arguments are assumed to carry provenance; every "
                "reference argument, including those of unsafe functions, is "
                "assumed to point to initialized bytes that decode to a valid "
                "value of the pointee type"
            ),
        ]
        good = make_receipt(
            audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
            correspondence_provenance=inapplicable,
            assumptions=v2_assumptions,
        )
        parsed = verify_zerocopy.validate_receipt(
            "05_unit", 0, json.dumps(good), "", ["util::macros::__unsafe"]
        )
        self.assertEqual(parsed["audit"]["canonicalRoot"], "Trusted.MirSemantics.UnitTheoremV2")

        v2_missing_prov = make_receipt(
            audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
            assumptions=v2_assumptions,
        )
        del v2_missing_prov["correspondence_provenance"]

        bad_cases = [
            (
                "v2_missing_provenance",
                v2_missing_prov,
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_missing_reason_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={"applicable": False},
                    assumptions=v2_assumptions,
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_blank_reason_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={
                        "applicable": False,
                        "reason": "   ",
                    },
                    assumptions=v2_assumptions,
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_extra_key_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={
                        "applicable": False,
                        "reason": "Profile v1 only",
                        "schema_version": 1,
                    },
                    assumptions=v2_assumptions,
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_blank_extra_assumption",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance=inapplicable,
                    assumptions=[*v2_assumptions, "   "],
                ),
                "Profile v2 receipt missing assumptions list",
            ),
            (
                "v2_applicable_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={
                        "applicable": True,
                        "reason": "Profile v1 only",
                    },
                    assumptions=v2_assumptions,
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_zero_applicable_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={
                        "applicable": 0,
                        "reason": "Profile v1 only",
                    },
                    assumptions=v2_assumptions,
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_none_applicable_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={
                        "applicable": None,
                        "reason": "Profile v1 only",
                    },
                    assumptions=v2_assumptions,
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_string_applicable_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={
                        "applicable": "false",
                        "reason": "Profile v1 only",
                    },
                    assumptions=v2_assumptions,
                ),
                "Profile v2 receipt without inapplicable",
            ),
            (
                "unknown_root",
                make_receipt(
                    audit={"canonicalRoot": "Trusted.MirSemantics.CrateTheoremV2"},
                    correspondence_provenance=inapplicable,
                    assumptions=v2_assumptions,
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

    def test_validate_receipt_rejects_missing_or_corrupted_caveat_fields(self):
        missing_deferred = make_receipt()
        del missing_deferred["deferred"]
        missing_assumptions = make_receipt()
        del missing_assumptions["assumptions"]
        missing_provenance = make_receipt()
        del missing_provenance["correspondence_provenance"]
        missing_taint = make_receipt()
        del missing_taint["taint_reasons"]
        missing_warnings = make_receipt()
        del missing_warnings["spec_warnings"]
        missing_root = make_receipt()
        del missing_root["audit"]["canonicalRoot"]

        bad_cases = [
            ("missing_deferred", missing_deferred, "missing deferred list"),
            (
                "blank_deferred_entries",
                make_receipt(deferred=["", "   "]),
                "blank entry in deferred",
            ),
            (
                "missing_assumptions",
                missing_assumptions,
                "Profile v1 receipt missing or invalid assumptions",
            ),
            (
                "empty_assumptions",
                make_receipt(assumptions=[]),
                "Profile v1 receipt missing or invalid assumptions",
            ),
            (
                "blank_only_assumptions",
                make_receipt(assumptions=["   "]),
                "Profile v1 receipt missing or invalid assumptions",
            ),
            (
                "blank_trailing_assumption",
                make_receipt(
                    assumptions=["faithful pinned compiler capture", ""]
                ),
                "Profile v1 receipt missing or invalid assumptions",
            ),
            (
                "non_list_assumptions",
                make_receipt(assumptions="faithful pinned compiler capture"),
                "Profile v1 receipt missing or invalid assumptions",
            ),
            (
                "non_str_assumptions_elem",
                make_receipt(assumptions=["ok", 42]),
                "Profile v1 receipt missing or invalid assumptions",
            ),
            (
                "missing_provenance",
                missing_provenance,
                "Profile v1 receipt missing correspondence_provenance",
            ),
            (
                "empty_provenance",
                make_receipt(correspondence_provenance={}),
                "Profile v1 receipt missing correspondence_provenance",
            ),
            (
                "non_dict_provenance",
                make_receipt(correspondence_provenance=["pass2"]),
                "Profile v1 receipt missing correspondence_provenance",
            ),
            (
                "arbitrary_key_provenance",
                make_receipt(correspondence_provenance={"foo": "bar"}),
                "correspondence_provenance\\.schema_version=None",
            ),
            (
                "reason_only_provenance",
                make_receipt(
                    correspondence_provenance={"reason": "Pass 2 skipped"}
                ),
                "Profile v1 receipt correspondence_provenance must omit "
                "applicable and reason",
            ),
            (
                "bool_schema_version_provenance",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        schema_version=True
                    )
                ),
                "correspondence_provenance\\.schema_version=True",
            ),
            (
                "unsupported_schema_version_provenance",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        schema_version=2
                    )
                ),
                "correspondence_provenance\\.schema_version=2",
            ),
            (
                "blank_upstream_commit_provenance",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        upstream_commit="   "
                    )
                ),
                "correspondence_provenance\\.upstream_commit=",
            ),
            (
                "v1_extra_unknown_key_provenance",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(extra="x")
                ),
                "unexpected correspondence_provenance keys=\\['extra'\\]",
            ),
            (
                "v1_with_v3_claim_kind_key",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        claim_kind="exact_refines"
                    )
                ),
                "unexpected correspondence_provenance keys=\\['claim_kind'\\]",
            ),
            (
                "v1_bad_pin_hex_uppercase",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        upstream_pin_sha256="A" * 64
                    )
                ),
                "correspondence_provenance\\.upstream_pin_sha256=",
            ),
            (
                "v1_bad_pin_hex_trailing_newline",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        upstream_pin_sha256=SHA_A + "\n"
                    )
                ),
                "correspondence_provenance\\.upstream_pin_sha256=",
            ),
            (
                "v1_bad_sysroot_hex_short",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        sysroot_foundation_manifest_sha256="deadbeef"
                    )
                ),
                "correspondence_provenance\\."
                "sysroot_foundation_manifest_sha256",
            ),
            (
                "v1_empty_adapters_map",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        correspondence_adapters={}
                    )
                ),
                "missing or empty correspondence_provenance\\."
                "correspondence_adapters",
            ),
            (
                "v1_bad_proofs_digest",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        correspondence_proofs={"p.lean": "not-a-sha256"}
                    )
                ),
                "invalid entry in correspondence_provenance\\."
                "correspondence_proofs",
            ),
            (
                "v1_empty_trusted_lean_map",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        trusted_lean={}
                    )
                ),
                "missing or empty correspondence_provenance\\.trusted_lean",
            ),
            (
                "v1_patched_file_duplicate_path",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        patched_files=[
                            {
                                "path": "Miri/A.lean",
                                "upstream_sha256": SHA_A,
                                "patched_sha256": SHA_B,
                            },
                            {
                                "path": "Miri/A.lean",
                                "upstream_sha256": SHA_A,
                                "patched_sha256": SHA_C,
                            },
                        ]
                    )
                ),
                "duplicate correspondence_provenance\\.patched_files",
            ),
            (
                "v1_patched_file_extra_key",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        patched_files=[
                            {
                                "path": "Miri/A.lean",
                                "upstream_sha256": SHA_A,
                                "patched_sha256": SHA_B,
                                "extra": 1,
                            }
                        ]
                    )
                ),
                "patched_files\\[0\\] keys mismatch",
            ),
            (
                "v1_patched_file_bad_sha",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        patched_files=[
                            {
                                "path": "Miri/A.lean",
                                "upstream_sha256": "xyz",
                                "patched_sha256": SHA_B,
                            }
                        ]
                    )
                ),
                "patched_files\\[0\\]\\.upstream_sha256 invalid",
            ),
            (
                "v1_minirust_explicit_null",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=None
                    )
                ),
                "invalid correspondence_provenance\\.minirust_upstream=None",
            ),
            (
                "v1_minirust_non_dict",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=["bad"]
                    )
                ),
                "invalid correspondence_provenance\\.minirust_upstream=",
            ),
            (
                "v1_minirust_extra_key",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(extra="nope")
                    )
                ),
                "unexpected correspondence_provenance\\.minirust_upstream "
                "keys=\\['extra'\\]",
            ),
            (
                "v1_minirust_untrimmed_repo",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            upstream_repository=" https://github.com/minirust/minirust"
                        )
                    )
                ),
                "minirust_upstream\\.upstream_repository must be trimmed",
            ),
            (
                "v1_minirust_blank_repo",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            upstream_repository="   "
                        )
                    )
                ),
                "minirust_upstream\\.upstream_repository must be trimmed",
            ),
            (
                "v1_minirust_untrimmed_commit",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            upstream_commit=" d821c6e3 "
                        )
                    )
                ),
                "minirust_upstream\\.upstream_commit must be trimmed",
            ),
            (
                "v1_minirust_bad_pin_sha",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            upstream_pin_sha256="A" * 64
                        )
                    )
                ),
                "minirust_upstream\\.upstream_pin_sha256 invalid",
            ),
            (
                "v1_minirust_bad_tarball_sha",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            tarball_sha256="A" * 64
                        )
                    )
                ),
                "minirust_upstream\\.tarball_sha256 invalid",
            ),
            (
                "v1_minirust_bad_manifest_sha",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            manifest_sha256="short"
                        )
                    )
                ),
                "minirust_upstream\\.manifest_sha256 invalid",
            ),
            (
                "v1_minirust_zero_file_count",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            file_count=0, files={}
                        )
                    )
                ),
                "minirust_upstream\\.file_count must be a positive integer",
            ),
            (
                "v1_minirust_negative_file_count",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(file_count=-1)
                    )
                ),
                "minirust_upstream\\.file_count must be a positive integer",
            ),
            (
                "v1_minirust_float_file_count",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            file_count=1.0
                        )
                    )
                ),
                "minirust_upstream\\.file_count must be a positive integer",
            ),
            (
                "v1_minirust_bool_file_count",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            file_count=True
                        )
                    )
                ),
                "minirust_upstream\\.file_count must be a positive integer",
            ),
            (
                "v1_minirust_count_gt_files",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(file_count=2)
                    )
                ),
                "minirust_upstream\\.file_count \\(2\\) disagrees with "
                "files length \\(1\\)",
            ),
            (
                "v1_minirust_count_lt_files",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            file_count=1,
                            files={
                                "spec/lang/syntax.md": SHA_D,
                                "spec/lang/values.md": SHA_E,
                            },
                        )
                    )
                ),
                "minirust_upstream\\.file_count \\(1\\) disagrees with "
                "files length \\(2\\)",
            ),
            (
                "v1_minirust_non_dict_files",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            files=["spec/lang/syntax.md"]
                        )
                    )
                ),
                "missing or empty correspondence_provenance\\."
                "minirust_upstream\\.files",
            ),
            (
                "v1_minirust_empty_files",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(files={})
                    )
                ),
                "missing or empty correspondence_provenance\\."
                "minirust_upstream\\.files",
            ),
            (
                "v1_minirust_empty_file_key",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            files={"": SHA_D}
                        )
                    )
                ),
                "invalid entry in correspondence_provenance\\."
                "minirust_upstream\\.files",
            ),
            (
                "v1_minirust_untrimmed_file_key",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            files={" spec/lang/syntax.md": SHA_D}
                        )
                    )
                ),
                "invalid entry in correspondence_provenance\\."
                "minirust_upstream\\.files",
            ),
            (
                "v1_minirust_bad_file_digest",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            files={"spec/lang/syntax.md": "xyz"}
                        )
                    )
                ),
                "invalid entry in correspondence_provenance\\."
                "minirust_upstream\\.files",
            ),
            (
                "v1_minirust_uppercase_file_digest",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            files={"spec/lang/syntax.md": "D" * 64}
                        )
                    )
                ),
                "invalid entry in correspondence_provenance\\."
                "minirust_upstream\\.files",
            ),
            (
                "v1_minirust_nonstr_file_digest",
                make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=make_minirust_upstream(
                            files={"spec/lang/syntax.md": 123}
                        )
                    )
                ),
                "invalid entry in correspondence_provenance\\."
                "minirust_upstream\\.files",
            ),
            (
                "v1_inapplicable_provenance",
                make_receipt(
                    correspondence_provenance={
                        "applicable": False,
                        "reason": "unpinned",
                    }
                ),
                "Profile v1 receipt correspondence_provenance must omit "
                "applicable and reason",
            ),
            (
                "v1_applicable_true_provenance",
                make_receipt(
                    correspondence_provenance={
                        "applicable": True,
                        "schema_version": 1,
                    }
                ),
                "Profile v1 receipt correspondence_provenance must omit "
                "applicable and reason",
            ),
            ("missing_taint_reasons", missing_taint, "taint_reasons=None"),
            ("missing_spec_warnings", missing_warnings, "spec_warnings=None"),
            ("missing_canonical_root", missing_root, "canonicalRoot=None"),
        ]
        for label, payload, needle in bad_cases:
            with self.subTest(case=label):
                with self.assertRaisesRegex(RuntimeError, needle):
                    verify_zerocopy.validate_receipt(
                        "01_unit",
                        0,
                        json.dumps(payload),
                        "",
                        ["util::macros::__unsafe"],
                    )

        # Schema 1 omitting any mandatory field must fail closed.
        for omitted_field in (
            "upstream_repository",
            "upstream_commit",
            "upstream_lean_toolchain",
            "build_lean_toolchain",
            "upstream_pin_sha256",
            "sysroot_foundation_manifest_sha256",
            "patched_files",
            "minirust_upstream",
            "correspondence_adapters",
            "correspondence_proofs",
            "trusted_lean",
            "note",
        ):
            with self.subTest(v1_omitted=omitted_field):
                prov = make_v1_provenance()
                del prov[omitted_field]
                payload = make_receipt(correspondence_provenance=prov)
                with self.assertRaisesRegex(
                    RuntimeError,
                    f"correspondence_provenance\\.{omitted_field}",
                ):
                    verify_zerocopy.validate_receipt(
                        "01_unit",
                        0,
                        json.dumps(payload),
                        "",
                        ["util::macros::__unsafe"],
                    )

        # Schema 3 omitting any mandatory field must fail closed.
        for omitted_v3 in (
            "minirust_upstream",
            "claim_kind",
            "permitted_axioms",
            "model_system_relation",
            "tcb_shims",
            "taint_reasons",
            "qualifiers",
        ):
            with self.subTest(v3_omitted=omitted_v3):
                prov = make_v3_provenance()
                del prov[omitted_v3]
                payload = make_receipt(correspondence_provenance=prov)
                with self.assertRaisesRegex(
                    RuntimeError, f"correspondence_provenance\\.{omitted_v3}"
                ):
                    verify_zerocopy.validate_receipt(
                        "01_unit",
                        0,
                        json.dumps(payload),
                        "",
                        ["util::macros::__unsafe"],
                    )

        # `minirust_upstream` is mandatory on applicable provenance and must
        # include all 7 fields.
        for omitted_mr in (
            "upstream_repository",
            "upstream_commit",
            "upstream_pin_sha256",
            "tarball_sha256",
            "manifest_sha256",
            "file_count",
            "files",
        ):
            with self.subTest(mr_omitted=omitted_mr):
                mr = make_minirust_upstream()
                del mr[omitted_mr]
                payload = make_receipt(
                    correspondence_provenance=make_v1_provenance(
                        minirust_upstream=mr
                    )
                )
                with self.assertRaisesRegex(
                    RuntimeError,
                    f"correspondence_provenance\\.minirust_upstream\\.{omitted_mr}",
                ):
                    verify_zerocopy.validate_receipt(
                        "01_unit",
                        0,
                        json.dumps(payload),
                        "",
                        ["util::macros::__unsafe"],
                    )

        # Schema 3 invalid enums, cross-field mismatches, and extra keys fail.
        v3_bad_cases = [
            (
                "v3_extra_key",
                make_v3_provenance(extra="nope"),
                "unexpected correspondence_provenance keys=\\['extra'\\]",
            ),
            (
                "v3_unknown_claim_kind",
                make_v3_provenance(claim_kind="weak_refines"),
                "correspondence_provenance\\.claim_kind='weak_refines'",
            ),
            (
                "v3_unhashable_claim_kind",
                make_v3_provenance(claim_kind=["exact_refines"]),
                "correspondence_provenance\\.claim_kind=\\['exact_refines'\\]",
            ),
            (
                "v3_empty_permitted_axioms",
                make_v3_provenance(permitted_axioms=[]),
                "permitted_axioms must not be empty",
            ),
            (
                "v3_unsorted_permitted_axioms",
                make_v3_provenance(
                    permitted_axioms=["propext", "Classical.choice"]
                ),
                "strictly sorted and duplicate-free",
            ),
            (
                "v3_incompatible_claim_kind_relation",
                make_v3_provenance(
                    claim_kind="sound_refines",
                    model_system_relation={
                        "kind": "simulation",
                        "qualifier": "wf_stutter",
                        "direction": "bidirectional",
                        "licensed_claim_shapes": ["forall_safety"],
                    },
                ),
                "incompatible with model_system_relation",
            ),
            (
                "v3_missing_patched_shim",
                make_v3_provenance(
                    patched_files=[
                        {
                            "path": "Miri/A.lean",
                            "upstream_sha256": SHA_A,
                            "patched_sha256": SHA_F,
                        }
                    ],
                    tcb_shims=[],
                    taint_reasons=[],
                ),
                "is missing from tcb_shims",
            ),
            (
                "v3_patched_shim_digest_mismatch",
                make_v3_provenance(
                    patched_files=[
                        {
                            "path": "Miri/A.lean",
                            "upstream_sha256": SHA_A,
                            "patched_sha256": SHA_F,
                        }
                    ],
                    tcb_shims=[
                        {
                            "id": "lean-miri:Miri/A.lean",
                            "kind": "upstream_bugfix_patch",
                            "sha256": SHA_E,
                            "status": "assumed",
                        }
                    ],
                    taint_reasons=["vendor_upstream_patches_present"],
                ),
                "disagrees with patched_files\\.patched_sha256",
            ),
            (
                "v3_orphan_patch_shim",
                make_v3_provenance(
                    patched_files=[],
                    tcb_shims=[
                        {
                            "id": "lean-miri:Miri/Ghost.lean",
                            "kind": "upstream_bugfix_patch",
                            "sha256": SHA_F,
                            "status": "assumed",
                        }
                    ],
                    taint_reasons=["vendor_upstream_patches_present"],
                ),
                "has no matching patched_files entry",
            ),
            (
                "v3_assumed_seam_missing_from_shims",
                make_v3_provenance(
                    qualifiers={
                        "choice_total": True,
                        "assumed_seams": ["seam_a"],
                        "scope_kind": "full_gate",
                    },
                    taint_reasons=["assumed_seams_present"],
                ),
                "qualifiers\\.assumed_seams entry 'seam_a' is missing",
            ),
            (
                "v3_taint_reasons_mismatch",
                make_v3_provenance(
                    qualifiers={
                        "choice_total": False,
                        "assumed_seams": [],
                        "scope_kind": "full_gate",
                    },
                    taint_reasons=[],
                ),
                "taint_reasons \\[\\] disagrees with expected "
                "\\['choice_total_false'\\]",
            ),
            (
                "v3_bad_qualifiers_scope",
                make_v3_provenance(
                    qualifiers={
                        "choice_total": True,
                        "assumed_seams": [],
                        "scope_kind": "unknown_gate",
                    }
                ),
                "qualifiers\\.scope_kind='unknown_gate'",
            ),
            (
                "v3_shim_missing_commit_and_sha256",
                make_v3_provenance(
                    tcb_shims=[
                        {
                            "id": "seam_x",
                            "kind": "append_only_spec_lemma",
                            "status": "proved",
                        }
                    ]
                ),
                "must specify at least one of commit or sha256",
            ),
        ]
        for label, bad_prov, needle in v3_bad_cases:
            with self.subTest(case=label):
                with self.assertRaisesRegex(RuntimeError, needle):
                    verify_zerocopy.validate_receipt(
                        "01_unit",
                        0,
                        json.dumps(
                            make_receipt(correspondence_provenance=bad_prov)
                        ),
                        "",
                        ["util::macros::__unsafe"],
                    )

        # Positive checks:
        # 1. Non-experimental Profile v1 receipt (3 assumptions) + complete
        #    schema-3 provenance (both clean and patched/seam-consistent).
        non_experimental_v1 = make_receipt(
            assumptions=[
                "faithful pinned compiler capture",
                "Lean kernel and admitted foundation",
                "intact compiler and verification environment",
            ],
            correspondence_provenance=make_v3_provenance(),
        )
        parsed = verify_zerocopy.validate_receipt(
            "01_unit",
            0,
            json.dumps(non_experimental_v1),
            "",
            ["util::macros::__unsafe"],
            expected_profile=1,
        )
        self.assertEqual(len(parsed["assumptions"]), 3)

        v3_with_patch_and_seam = make_v3_provenance(
            minirust_upstream=make_minirust_upstream(),
            patched_files=[
                {
                    "path": "Miri/A.lean",
                    "upstream_sha256": SHA_A,
                    "patched_sha256": SHA_F,
                }
            ],
            tcb_shims=[
                {
                    "id": "lean-miri:Miri/A.lean",
                    "kind": "upstream_bugfix_patch",
                    "sha256": SHA_F,
                    "status": "assumed",
                },
                {
                    "id": "seam_a",
                    "kind": "assumed_seam",
                    "commit": "abc123",
                    "status": "assumed",
                },
            ],
            qualifiers={
                "choice_total": False,
                "assumed_seams": ["seam_a"],
                "scope_kind": "partial_gate",
            },
            taint_reasons=[
                "assumed_seams_present",
                "choice_total_false",
                "vendor_upstream_patches_present",
            ],
        )
        parsed_v3 = verify_zerocopy.validate_receipt(
            "01_unit",
            0,
            json.dumps(
                make_receipt(correspondence_provenance=v3_with_patch_and_seam)
            ),
            "",
            ["util::macros::__unsafe"],
            expected_profile=1,
        )
        self.assertEqual(
            parsed_v3["correspondence_provenance"], v3_with_patch_and_seam
        )

        # 2. Live rendered repository provenance from
        #    `render_correspondence_provenance.py` must be accepted verbatim.
        anneal_root = Path(__file__).resolve().parents[1]
        rendered_raw = render_correspondence_provenance.render_provenance_json(
            trusted_bundle_rs=(
                anneal_root / "trusted/cargo-anneal/src/trusted_bundle.rs"
            ),
            upstream_pin=anneal_root / "vendor/lean-miri/UPSTREAM_PIN.json",
            minirust_upstream_pin=(
                anneal_root / "vendor/minirust/UPSTREAM_PIN.json"
            ),
            correspondence_adapters_dir=anneal_root / "trusted/correspondence",
            correspondence_proofs_dir=anneal_root / "correspondence",
            trusted_lean_dir=anneal_root / "trusted/lean",
            anneal_root=anneal_root,
        )
        live_provenance = json.loads(rendered_raw)
        parsed_live = verify_zerocopy.validate_receipt(
            "01_unit",
            0,
            json.dumps(make_receipt(correspondence_provenance=live_provenance)),
            "",
            ["util::macros::__unsafe"],
            expected_profile=1,
        )
        self.assertEqual(
            parsed_live["correspondence_provenance"], live_provenance
        )

    def test_validate_receipt_profile_v1_accepts_only_exact_decoupled_sentinel(
        self,
    ):
        reason = verify_zerocopy.DECOUPLED_CORRESPONDENCE_PROVENANCE_REASON
        # The Python mirror must match the Rust constant that `cargo-anneal`
        # emits (Rust `\<newline>` continuations elide the indentation).
        schema_rs = (
            Path(__file__).resolve().parents[1]
            / "trusted/cargo-anneal/src/core/inspect/schema.rs"
        ).read_text(encoding="utf-8")
        match = re.search(
            r'pub const DECOUPLED_CORRESPONDENCE_PROVENANCE_REASON: &str = '
            r'"((?:[^"\\]|\\.)*)";',
            schema_rs,
            re.DOTALL,
        )
        self.assertIsNotNone(match)
        self.assertEqual(re.sub(r"\\\n\s*", "", match.group(1)), reason)

        decoupled = {"applicable": False, "reason": reason}
        parsed = verify_zerocopy.validate_receipt(
            "01_unit",
            0,
            json.dumps(make_receipt(correspondence_provenance=decoupled)),
            "",
            ["util::macros::__unsafe"],
            expected_profile=1,
        )
        self.assertEqual(parsed["correspondence_provenance"], decoupled)

        bad_cases = [
            ("altered_reason", {"applicable": False, "reason": reason + " "}),
            ("applicable_zero", {"applicable": 0, "reason": reason}),
            ("applicable_true", {"applicable": True, "reason": reason}),
            (
                "extra_key",
                {"applicable": False, "reason": reason, "extra": 1},
            ),
            ("missing_applicable", {"reason": reason}),
        ]
        for label, provenance in bad_cases:
            with self.subTest(case=label):
                with self.assertRaisesRegex(
                    RuntimeError, "must omit applicable and reason"
                ):
                    verify_zerocopy.validate_receipt(
                        "01_unit",
                        0,
                        json.dumps(
                            make_receipt(correspondence_provenance=provenance)
                        ),
                        "",
                        ["util::macros::__unsafe"],
                        expected_profile=1,
                    )

    def test_summary_json_propagates_v1_and_v2_receipt_caveats_verbatim(self):
        v1_assumptions = [
            "faithful pinned compiler capture",
            "experimental pointer-free MIR semantics",
            "Lean kernel and admitted foundation",
            "intact compiler and verification environment",
        ]
        v1_deferred = [
            "complete review-surface reporting",
            "source-to-deployed-binary correspondence",
        ]
        v1_provenance = make_v1_provenance()
        v2_assumptions = [
            "faithful pinned compiler capture",
            (
                "experimental Profile v2 MIR semantics: caller memory, "
                "single-level references and raw pointers, little-endian byte "
                "order, and no aliasing model (Stacked or Tree Borrows); "
                "raw-pointer arguments are assumed to carry provenance; every "
                "reference argument, including those of unsafe functions, is "
                "assumed to point to initialized bytes that decode to a valid "
                "value of the pointee type"
            ),
            "Lean kernel and admitted foundation",
            "intact compiler and verification environment",
        ]
        v2_deferred = [
            "complete review-surface reporting",
            "source-to-deployed-binary correspondence",
        ]
        v2_provenance = {
            "applicable": False,
            "reason": (
                "bundled Pass 2 correspondence covers Profile v1 semantics "
                "only; Profile v2 execution rules are not certified against "
                "lean-miri"
            ),
        }
        v2_root_fn = (
            "<&[u8] as byte_slice::SplitByteSlice>::split_at_unchecked"
        )

        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            proofs_dir, src_dir, _ = make_proof_tree(
                root,
                unit_names=(
                    "01_usize_pointer_metadata",
                    "08_byte_slice_split_at_unchecked",
                ),
            )
            v2_unit = proofs_dir / "08_byte_slice_split_at_unchecked"
            (v2_unit / "Spec.lean").write_text(
                "prelude\ndef specs : SpecsV2 := ⟨(), ()⟩\n",
                encoding="utf-8",
            )
            (v2_unit / "request.json").write_text(
                json.dumps(make_unit_request(roots=[v2_root_fn])),
                encoding="utf-8",
            )

            v1_receipt = make_receipt(
                assumptions=v1_assumptions,
                deferred=v1_deferred,
                correspondence_provenance=v1_provenance,
            )
            v2_receipt = make_receipt(
                scope={"kind": "selected_unit", "roots": [v2_root_fn]},
                selected=[{"def_id": 0, "path": v2_root_fn, "body_index": 0}],
                audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
                assumptions=v2_assumptions,
                deferred=v2_deferred,
                correspondence_provenance=v2_provenance,
            )

            receipt_map = {
                "01_usize_pointer_metadata": v1_receipt,
                "08_byte_slice_split_at_unchecked": v2_receipt,
            }
            fake_cli = root / "cargo-anneal"
            fake_cap = root / "anneal-rustc-capture"
            fake_lean = root / "lean"
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            fake_lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_lean.chmod(0o755)
            fake_cap.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_cap.chmod(0o755)
            fake_cli.write_text(
                "#!/usr/bin/env python3\n"
                "import json\n"
                "from pathlib import Path\n"
                f"receipts = {json.dumps(receipt_map)!r}\n"
                "print(json.dumps(json.loads(receipts)[Path.cwd().name]))\n",
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
            summary = json.loads(
                (artifacts / "summary.json").read_text(encoding="utf-8")
            )
            self.assertEqual(summary["unit_count"], 2)

            v1_rec = summary["units"]["01_usize_pointer_metadata"]
            self.assertEqual(v1_rec["profile"], 1)
            self.assertEqual(
                v1_rec["canonical_root"], "Trusted.MirSemantics.UnitTheorem"
            )
            self.assertEqual(v1_rec["taint_reasons"], [])
            self.assertEqual(v1_rec["assumptions"], v1_assumptions)
            self.assertEqual(v1_rec["deferred"], v1_deferred)
            self.assertEqual(v1_rec["spec_warnings"], [])
            self.assertEqual(
                v1_rec["correspondence_provenance"], v1_provenance
            )

            v2_rec = summary["units"]["08_byte_slice_split_at_unchecked"]
            self.assertEqual(v2_rec["profile"], 2)
            self.assertEqual(
                v2_rec["canonical_root"], "Trusted.MirSemantics.UnitTheoremV2"
            )
            self.assertEqual(v2_rec["taint_reasons"], [])
            self.assertEqual(v2_rec["assumptions"], v2_assumptions)
            self.assertEqual(v2_rec["deferred"], v2_deferred)
            self.assertEqual(v2_rec["spec_warnings"], [])
            self.assertEqual(
                v2_rec["correspondence_provenance"], v2_provenance
            )
            self.assertIs(
                v2_rec["correspondence_provenance"]["applicable"], False
            )

            # Dropping any required caveat field from a CLI-emitted receipt
            # must fail closed without writing `summary.json`.
            missing_field_checks = (
                ("canonicalRoot", "canonicalRoot=None"),
                (
                    "assumptions",
                    "Profile v1 receipt missing or invalid assumptions",
                ),
                ("deferred", "missing deferred list"),
                (
                    "correspondence_provenance",
                    "Profile v1 receipt missing correspondence_provenance",
                ),
                ("spec_warnings", "spec_warnings=None"),
                ("taint_reasons", "taint_reasons=None"),
            )
            for missing_key, needle in missing_field_checks:
                with self.subTest(missing_key=missing_key):
                    broken = make_receipt(
                        assumptions=v1_assumptions,
                        deferred=v1_deferred,
                        correspondence_provenance=v1_provenance,
                    )
                    if missing_key == "canonicalRoot":
                        del broken["audit"]["canonicalRoot"]
                    else:
                        del broken[missing_key]
                    broken_map = {
                        "01_usize_pointer_metadata": broken,
                        "08_byte_slice_split_at_unchecked": v2_receipt,
                    }
                    fake_cli.write_text(
                        "#!/usr/bin/env python3\n"
                        "import json\n"
                        "from pathlib import Path\n"
                        f"receipts = {json.dumps(broken_map)!r}\n"
                        "print(json.dumps("
                        "json.loads(receipts)[Path.cwd().name]))\n",
                        encoding="utf-8",
                    )
                    fake_cli.chmod(0o755)
                    fail_artifacts = root / f"fail_{missing_key}"
                    with self.assertRaisesRegex(RuntimeError, needle):
                        verify_zerocopy.main([
                            "--proofs-dir", str(proofs_dir),
                            "--src-dir", str(src_dir),
                            "--cli", str(fake_cli),
                            "--capture", str(fake_cap),
                            "--sysroot", str(fake_sys),
                            "--lean", str(fake_lean),
                            "--artifacts-dir", str(fail_artifacts),
                        ])
                    self.assertFalse((fail_artifacts / "summary.json").exists())

    def test_validate_receipt_profile_v1_v2_match_and_disclosures(self):
        v2_semantics = (
            "experimental Profile v2 MIR semantics: caller memory, single-level "
            "references and raw pointers, little-endian byte order, and no "
            "aliasing model (Stacked or Tree Borrows); raw-pointer arguments are "
            "assumed to carry provenance; every reference argument, including "
            "those of unsafe functions, is assumed to point to initialized bytes "
            "that decode to a valid value of the pointee type"
        )
        v2_assumptions = [
            "faithful pinned compiler capture",
            v2_semantics,
            "Lean kernel and admitted foundation",
            "intact compiler and verification environment",
        ]
        v1_assumptions = [
            "faithful pinned compiler capture",
            "experimental pointer-free MIR semantics",
            "Lean kernel and admitted foundation",
            "intact compiler and verification environment",
        ]
        inapplicable = {
            "applicable": False,
            "reason": "bundled Pass 2 correspondence covers Profile v1 semantics only",
        }

        v1_good = make_receipt(assumptions=v1_assumptions)
        for expected_profile in (None, 1):
            with self.subTest(case="v1_pass", expected_profile=expected_profile):
                parsed = verify_zerocopy.validate_receipt(
                    "01_unit",
                    0,
                    json.dumps(v1_good),
                    "",
                    ["util::macros::__unsafe"],
                    expected_profile=expected_profile,
                )
                self.assertEqual(
                    parsed["audit"]["canonicalRoot"],
                    "Trusted.MirSemantics.UnitTheorem",
                )

        v2_good = make_receipt(
            audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
            correspondence_provenance=inapplicable,
            assumptions=v2_assumptions,
        )
        for expected_profile in (None, 2):
            with self.subTest(case="v2_pass", expected_profile=expected_profile):
                parsed = verify_zerocopy.validate_receipt(
                    "06_unit",
                    0,
                    json.dumps(v2_good),
                    "",
                    ["util::macros::__unsafe"],
                    expected_profile=expected_profile,
                )
                self.assertEqual(
                    parsed["audit"]["canonicalRoot"],
                    "Trusted.MirSemantics.UnitTheoremV2",
                )

        v2_missing_prov = make_receipt(
            audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
            assumptions=v2_assumptions,
        )
        del v2_missing_prov["correspondence_provenance"]
        v2_missing_assumptions = make_receipt(
            audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
            correspondence_provenance=inapplicable,
        )
        del v2_missing_assumptions["assumptions"]

        mismatch_cases = [
            ("v1_expected_got_v2", v2_good, 1, "does not match Profile v1"),
            ("v2_expected_got_v1", v1_good, 2, "does not match Profile v2"),
            ("invalid_expected_bool", v1_good, True, "invalid expected_profile"),
            ("invalid_expected_v3", v1_good, 3, "invalid expected_profile"),
            (
                "unknown_root",
                make_receipt(
                    audit={"canonicalRoot": "Trusted.MirSemantics.CrateTheoremV2"},
                    correspondence_provenance=inapplicable,
                    assumptions=v2_assumptions,
                ),
                None,
                "canonicalRoot=",
            ),
            (
                "v1_with_v2_assumption",
                make_receipt(assumptions=v2_assumptions),
                1,
                "Profile v1 receipt carries Profile v2",
            ),
            (
                "v2_missing_provenance",
                v2_missing_prov,
                2,
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_applicable_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={
                        "applicable": True,
                        "reason": "Profile v1 only",
                    },
                    assumptions=v2_assumptions,
                ),
                2,
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_zero_applicable_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={
                        "applicable": 0,
                        "reason": "Profile v1 only",
                    },
                    assumptions=v2_assumptions,
                ),
                2,
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_none_applicable_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={
                        "applicable": None,
                        "reason": "Profile v1 only",
                    },
                    assumptions=v2_assumptions,
                ),
                2,
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_string_applicable_provenance",
                make_receipt(
                    audit={
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"
                    },
                    correspondence_provenance={
                        "applicable": "false",
                        "reason": "Profile v1 only",
                    },
                    assumptions=v2_assumptions,
                ),
                2,
                "Profile v2 receipt without inapplicable",
            ),
            (
                "v2_missing_assumptions",
                v2_missing_assumptions,
                2,
                "missing assumptions list",
            ),
            (
                "v2_v1_assumptions_only",
                make_receipt(
                    audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
                    correspondence_provenance=inapplicable,
                    assumptions=v1_assumptions,
                ),
                2,
                "must not carry Profile v1 pointer-free assumption",
            ),
            (
                "v2_incomplete_disclosure",
                make_receipt(
                    audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
                    correspondence_provenance=inapplicable,
                    assumptions=["experimental Profile v2 MIR semantics: partial"],
                ),
                2,
                "missing disclosures",
            ),
        ]
        for label, payload, expected_profile, needle in mismatch_cases:
            with self.subTest(case=label):
                with self.assertRaisesRegex(RuntimeError, needle):
                    verify_zerocopy.validate_receipt(
                        "06_unit",
                        0,
                        json.dumps(payload),
                        "",
                        ["util::macros::__unsafe"],
                        expected_profile=expected_profile,
                    )

    def test_expected_unit_profile_from_spec_and_end_to_end_mismatch(self):
        # All real repository `zerocopy/proofs/*` units must resolve cleanly
        # when present (`ci-core` `anneal-ci-tests` mounts `zerocopy/proofs/**`
        # without `zerocopy/src/**`).
        repo_root = Path(__file__).resolve().parents[2]
        if (repo_root / "zerocopy/proofs").is_dir():
            self.assertFalse(
                (repo_root / "zerocopy/proofs/MANIFEST.json").exists()
            )
            actual_unit_dirs = sorted(
                p.name
                for p in (repo_root / "zerocopy/proofs").iterdir()
                if p.is_dir()
            )
            self.assertGreaterEqual(len(actual_unit_dirs), 6)
        codeowners_path = repo_root / ".github/CODEOWNERS"
        if codeowners_path.is_file():
            co_lines = [
                ln.strip()
                for ln in codeowners_path.read_text(
                    encoding="utf-8"
                ).splitlines()
                if ln.strip() and not ln.lstrip().startswith("#")
            ]
            for line in co_lines:
                pat = line.split()[0]
                self.assertNotIn("\\", pat)
                self.assertFalse(pat.startswith("!"))
                self.assertNotIn("[", pat)
            co_patterns = {ln.split()[0] for ln in co_lines}
            self.assertNotIn("/zerocopy/proofs/MANIFEST.json", co_patterns)
            for required_pat in (
                "/zerocopy/proofs/*/request.json",
                "/zerocopy/proofs/*/Spec*.lean",
            ):
                self.assertIn(required_pat, co_patterns)

        if (repo_root / "zerocopy/proofs").is_dir() and (
            repo_root / "zerocopy/src"
        ).is_dir():
            real_units = verify_zerocopy.discover_units(
                repo_root / "zerocopy/proofs",
                repo_root / "zerocopy/src",
                repo_root=repo_root,
            )
            real_profiles = {
                unit_dir.name: verify_zerocopy.expected_unit_profile(
                    unit_dir, request
                )
                for unit_dir, request in real_units
            }
            for profile in real_profiles.values():
                self.assertIn(profile, (1, 2))
            self.assertTrue(
                {1, 2}.issubset(real_profiles.values()), real_profiles
            )

        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            proofs_dir, src_dir, unit = make_proof_tree(root)
            request = json.loads((unit / "request.json").read_text(encoding="utf-8"))

            # Comments and strings mentioning `SpecsV2` must not fool v1 units.
            (unit / "Spec.lean").write_text(
                "prelude\n"
                "-- def specs : SpecsV2 := fake\n"
                "/- /- def specs : SpecsV2 := nested -/ -/\n"
                'def msg : String := "def specs : SpecsV2 :="\n'
                "noncomputable def specs : Trusted.MirSemantics.Specs := ⟨(), ()⟩\n",
                encoding="utf-8",
            )
            self.assertEqual(
                verify_zerocopy.expected_unit_profile(unit, request), 1
            )

            # Switch `Spec.lean` to Profile v2 (`SpecsV2`), including Char
            # literals containing `"` and identifier primes like `x'`.
            v2_spec_src = (
                "prelude\n"
                "-- def specs : Specs := comment\n"
                "def q1 : Char := '\"'\n"
                "def q2 : Char := '\\\"'\n"
                "def x' : Nat := 0\n"
                "def a'b' : Nat := 0\n"
                "def specs : SpecsV2 := ⟨(), ()⟩\n"
            )
            stripped_v2 = verify_zerocopy._strip_lean_comments_and_strings(
                v2_spec_src
            )
            self.assertIn("def x' : Nat := 0", stripped_v2)
            self.assertIn("def a'b' : Nat := 0", stripped_v2)
            self.assertNotIn('"', stripped_v2)
            (unit / "Spec.lean").write_text(v2_spec_src, encoding="utf-8")
            self.assertEqual(
                verify_zerocopy.expected_unit_profile(unit, request), 2
            )

            fake_cli = root / "cargo-anneal"
            fake_cap = root / "anneal-rustc-capture"
            fake_lean = root / "lean"
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            fake_lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_lean.chmod(0o755)
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import json, sys\n"
                "from pathlib import Path\n"
                "args = sys.argv[1:]\n"
                "out_dir = Path(args[args.index('--out-dir') + 1])\n"
                "out_dir.mkdir(parents=True, exist_ok=False)\n"
                "(out_dir / 'capture.json').write_text(\n"
                "    json.dumps({'selected': [{'def_id': 0, 'path': 'id::<u8>', 'body_index': 0}]})\n"
                ")\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)

            # `Spec.lean` is Profile v2, but CLI emits a v1 receipt -> reject.
            v1_payload = json.dumps(make_receipt())
            fake_cli.write_text(
                f"#!/usr/bin/env python3\nprint({v1_payload!r})\n",
                encoding="utf-8",
            )
            fake_cli.chmod(0o755)
            with self.assertRaisesRegex(RuntimeError, "does not match Profile v2"):
                verify_zerocopy.main([
                    "--proofs-dir", str(proofs_dir),
                    "--src-dir", str(src_dir),
                    "--cli", str(fake_cli),
                    "--capture", str(fake_cap),
                    "--sysroot", str(fake_sys),
                    "--lean", str(fake_lean),
                ])

            # `Spec.lean` is Profile v2 and CLI emits a valid v2 receipt -> ok.
            v2_payload = json.dumps(
                make_receipt(
                    audit={"canonicalRoot": "Trusted.MirSemantics.UnitTheoremV2"},
                    correspondence_provenance={
                        "applicable": False,
                        "reason": "Profile v1 only",
                    },
                    assumptions=[
                        "faithful pinned compiler capture",
                        (
                            "experimental Profile v2 MIR semantics: no aliasing "
                            "model; raw-pointer arguments are assumed to carry "
                            "provenance; including those of unsafe functions; "
                            "decode to a valid value of the pointee type"
                        ),
                    ],
                )
            )
            fake_cli.write_text(
                f"#!/usr/bin/env python3\nprint({v2_payload!r})\n",
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

            # `Spec.lean` is Profile v1, but CLI emits a v2 receipt -> reject.
            (unit / "Spec.lean").write_text(
                "prelude\ndef specs : Specs := ⟨(), ()⟩\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(RuntimeError, "does not match Profile v1"):
                verify_zerocopy.main([
                    "--proofs-dir", str(proofs_dir),
                    "--src-dir", str(src_dir),
                    "--cli", str(fake_cli),
                    "--capture", str(fake_cap),
                    "--sysroot", str(fake_sys),
                    "--lean", str(fake_lean),
                ])

            # Missing or ambiguous `Specs`/`SpecsV2` fails closed at discovery.
            for label, bad_spec in (
                ("missing", "prelude\n"),
                ("ambiguous", "prelude\ndef specs : Specs := a\ndef specs : SpecsV2 := b\n"),
            ):
                with self.subTest(case=label):
                    (unit / "Spec.lean").write_text(bad_spec, encoding="utf-8")
                    with self.assertRaisesRegex(
                        RuntimeError, "cannot uniquely determine MIR profile"
                    ):
                        verify_zerocopy.discover_units(proofs_dir, src_dir)

            # Non-`.` `proof.source_root` resolves relative to `unit_dir`, and
            # missing spec files raise a prefixed `RuntimeError`.
            sub_dir = unit / "lean"
            sub_dir.mkdir()
            (sub_dir / "Spec.lean").write_text(
                "prelude\ndef specs : SpecsV2 := ⟨(), ()⟩\n", encoding="utf-8"
            )
            sub_req = json.loads((unit / "request.json").read_text(encoding="utf-8"))
            sub_req["proof"]["source_root"] = "lean"
            self.assertEqual(
                verify_zerocopy.expected_unit_profile(unit, sub_req), 2
            )
            sub_req["proof"]["source_root"] = "missing_dir"
            with self.assertRaisesRegex(
                RuntimeError, r"^01_unit: cannot read specification source "
            ):
                verify_zerocopy.expected_unit_profile(unit, sub_req)

    def test_discover_units_deduplicates_selected_units_preserving_order(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            proofs_dir, src_dir, _ = make_proof_tree(
                root, unit_names=("01_unit", "02_unit")
            )

            selected = verify_zerocopy.discover_units(
                proofs_dir, src_dir, selected_units=["02_unit", "01_unit", "02_unit"]
            )
            self.assertEqual([u.name for u, _ in selected], ["02_unit", "01_unit"])

    def test_main_deduplicates_unit_flags_and_skips_local_discovery(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            proofs_dir, src_dir, _ = make_proof_tree(root)
            fake_cli = root / "cargo-anneal"
            fake_cap = root / "anneal-rustc-capture"
            fake_lean = root / "lean"
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            fake_lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_lean.chmod(0o755)
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import json, sys\n"
                "from pathlib import Path\n"
                "args = sys.argv[1:]\n"
                "out_dir = Path(args[args.index('--out-dir') + 1])\n"
                "out_dir.mkdir(parents=True, exist_ok=False)\n"
                "(out_dir / 'capture.json').write_text(\n"
                "    json.dumps({'selected': [{'def_id': 0, 'path': 'id::<u8>', 'body_index': 0}]})\n"
                ")\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)
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
            root = real_tmp_root(tmp)
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
                with self.assertRaisesRegex(RuntimeError, r"^01_unit: .*scope"):
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
            },
            selected=[
                {"def_id": 0, "path": "a::<bool>", "body_index": 0},
                {"def_id": 1, "path": "b::<u8>", "body_index": 1},
            ],
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
            },
            selected=[
                {"def_id": 0, "path": "r", "body_index": 0},
                {"def_id": 1, "path": "a::<u16>", "body_index": 1},
            ],
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
            (
                "mixed_selected_missing_root",
                ["r1"],
                [{"path": "a", "args": ["u8"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": ["r1"],
                        "instantiations": [{"path": "a", "args": ["u8"]}],
                    },
                    selected=[
                        {"def_id": 0, "path": "a::<u8>", "body_index": 0}
                    ],
                ),
                "selected mismatch",
            ),
            (
                "selected_exceeds_inst_count",
                [],
                [{"path": "a", "args": ["u8"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": [],
                        "instantiations": [{"path": "a", "args": ["u8"]}],
                    },
                    selected=[
                        {"def_id": 0, "path": "a::<u8>", "body_index": 0},
                        {"def_id": 1, "path": "extra::fn", "body_index": 1},
                    ],
                ),
                "selected mismatch",
            ),
            (
                "selected_unrelated_body_for_inst",
                [],
                [{"path": "a", "args": ["u8"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": [],
                        "instantiations": [{"path": "a", "args": ["u8"]}],
                    },
                    selected=[
                        {
                            "def_id": 0,
                            "path": "unrelated::function",
                            "body_index": 0,
                        }
                    ],
                ),
                "selected mismatch",
            ),
            (
                "mixed_selected_unrelated_body_for_inst",
                ["r1"],
                [{"path": "a", "args": ["u8"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": ["r1"],
                        "instantiations": [{"path": "a", "args": ["u8"]}],
                    },
                    selected=[
                        {"def_id": 0, "path": "r1", "body_index": 0},
                        {
                            "def_id": 1,
                            "path": "unrelated::function",
                            "body_index": 1,
                        },
                    ],
                ),
                "selected mismatch",
            ),
            (
                "selected_wrong_inst_arg",
                [],
                [{"path": "a", "args": ["u8"]}],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": [],
                        "instantiations": [{"path": "a", "args": ["u8"]}],
                    },
                    selected=[
                        {"def_id": 0, "path": "a::<bool>", "body_index": 0}
                    ],
                ),
                "selected mismatch",
            ),
            (
                "selected_dropped_second_inst",
                [],
                [
                    {"path": "a", "args": ["bool"]},
                    {"path": "b", "args": ["u8"]},
                ],
                make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": [],
                        "instantiations": [
                            {"path": "a", "args": ["bool"]},
                            {"path": "b", "args": ["u8"]},
                        ],
                    },
                    selected=[
                        {"def_id": 0, "path": "a::<bool>", "body_index": 0}
                    ],
                ),
                "selected mismatch",
            ),
        ]
        for label, exp_roots, exp_insts, payload, needle in bad_cases:
            with self.subTest(case=label):
                with self.assertRaisesRegex(RuntimeError, needle):
                    verify_zerocopy.validate_receipt(
                        "01_unit", 0, json.dumps(payload), "", exp_roots, exp_insts
                    )

        # Canonical formatting rules handle region-erasure dedup, trait
        # dispatch with already-expanded type paths, and const/ref stripping.
        canonical_cases = [
            (
                "region_dedup",
                [],
                [
                    {"path": "with_lt", "args": ["'static", "usize"]},
                    {"path": "with_lt", "args": ["usize"]},
                ],
                [{"def_id": 0, "path": "with_lt::<usize>", "body_index": 0}],
            ),
            (
                "trait_dispatch",
                [],
                [{"path": "Tag::tag", "args": ["::core::mem::ManuallyDrop<u8>"]}],
                [
                    {
                        "def_id": 0,
                        "path": "<core::mem::ManuallyDrop<u8> as Tag>::tag",
                        "body_index": 0,
                    }
                ],
            ),
            (
                "trait_generic_and_method_generic",
                [],
                [{"path": "Tag::tag", "args": ["u8", "bool", "u16"]}],
                [
                    {
                        "def_id": 0,
                        "path": "<u8 as Tag<bool>>::tag::<u16>",
                        "body_index": 0,
                    }
                ],
            ),
            (
                "trait_generic_only",
                [],
                [{"path": "Tag::tag", "args": ["u8", "bool"]}],
                [
                    {
                        "def_id": 0,
                        "path": "<u8 as Tag<bool>>::tag",
                        "body_index": 0,
                    }
                ],
            ),
            (
                "inherent_generic_with_method_generic",
                [],
                [{"path": "Wrap::new", "args": ["u8", "bool"]}],
                [
                    {
                        "def_id": 0,
                        "path": "<Wrap<u8>>::new::<bool>",
                        "body_index": 0,
                    }
                ],
            ),
            (
                "const_and_ref",
                [],
                [
                    {"path": "add_const", "args": ["0x2a_usize"]},
                    {"path": "take_ref", "args": ["&'static mut (u8, bool)"]},
                ],
                [
                    {"def_id": 0, "path": "add_const::<42>", "body_index": 0},
                    {
                        "def_id": 1,
                        "path": "take_ref::<&mut (u8, bool)>",
                        "body_index": 1,
                    },
                ],
            ),
        ]
        for label, exp_roots, exp_insts, sel in canonical_cases:
            with self.subTest(case=label):
                payload = make_receipt(
                    scope={
                        "kind": "selected_unit",
                        "roots": exp_roots,
                        "instantiations": exp_insts,
                    },
                    selected=sel,
                )
                verify_zerocopy.validate_receipt(
                    "01_unit", 0, json.dumps(payload), "", exp_roots, exp_insts
                )

        # Swapped trait vs method generic arguments must still be rejected.
        with self.assertRaisesRegex(RuntimeError, "selected mismatch"):
            verify_zerocopy.validate_receipt(
                "01_unit",
                0,
                json.dumps(
                    make_receipt(
                        scope={
                            "kind": "selected_unit",
                            "roots": [],
                            "instantiations": [
                                {"path": "Tag::tag", "args": ["u8", "bool", "u16"]}
                            ],
                        },
                        selected=[
                            {
                                "def_id": 0,
                                "path": "<u8 as Tag<u16>>::tag::<bool>",
                                "body_index": 0,
                            }
                        ],
                    )
                ),
                "",
                [],
                [{"path": "Tag::tag", "args": ["u8", "bool", "u16"]}],
            )

        # Even without `expected_compilation`, `stdlib_crate` must fail closed.
        with self.assertRaisesRegex(
            RuntimeError, "unexpected configuration keys=\\['stdlib_crate'\\]"
        ):
            verify_zerocopy.validate_receipt(
                "01_unit",
                0,
                json.dumps(
                    make_receipt(configuration={"stdlib_crate": True})
                ),
                "",
                ["util::macros::__unsafe"],
            )

    def test_main_runs_instantiation_only_unit_and_records_scope(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
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
            fake_lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_lean.chmod(0o755)
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import json, sys\n"
                "from pathlib import Path\n"
                "args = sys.argv[1:]\n"
                "out_dir = Path(args[args.index('--out-dir') + 1])\n"
                "out_dir.mkdir(parents=True, exist_ok=False)\n"
                "(out_dir / 'capture.json').write_text(\n"
                "    json.dumps({'selected': [{'def_id': 0, 'path': 'id::<u8>', 'body_index': 0}]})\n"
                ")\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)
            payload_json = json.dumps(
                make_receipt(
                    scope=scope,
                    selected=[{"def_id": 0, "path": "id::<u8>", "body_index": 0}],
                )
            )
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

            # Concrete arg drift or unrelated selected bodies fail closed.
            for bad_sel_path in ("id::<bool>", "unrelated::function"):
                bad_payload = json.dumps(
                    make_receipt(
                        scope=scope,
                        selected=[
                            {"def_id": 0, "path": bad_sel_path, "body_index": 0}
                        ],
                    )
                )
                fake_cli.write_text(
                    "#!/usr/bin/env python3\n"
                    f"print({bad_payload!r})\n",
                    encoding="utf-8",
                )
                fake_cli.chmod(0o755)
                with self.assertRaisesRegex(RuntimeError, "selected mismatch"):
                    verify_zerocopy.main([
                        "--proofs-dir", str(proofs_dir),
                        "--src-dir", str(src_dir),
                        "--cli", str(fake_cli),
                        "--capture", str(fake_cap),
                        "--sysroot", str(fake_sys),
                        "--lean", str(fake_lean),
                    ])

    def test_selected_entries_account_for_lowered_instantiations(self):
        # An instantiation of an impl item prints with the impl's parameters
        # substituted, which no textual spelling of the request predicts.
        impl = "m::_::<impl Tr for m::W<O>>::f"
        keys = [(impl, ("m::Big",)), (impl, ("m::Little",)), ("id", ("u8",))]
        big = "m::_::<impl Tr for m::W<m::Big>>::f"
        little = "m::_::<impl Tr for m::W<m::Little>>::f"
        # The lowering covers every instantiation, predicted or not.
        lowered = frozenset({big, little, "id::<u8>"})

        def sel(*paths):
            return [
                {"def_id": i, "path": p, "body_index": i}
                for i, p in enumerate(paths)
            ]

        check = verify_zerocopy._validate_selected_entries
        self.assertFalse(check(sel(big, little, "id::<u8>"), [], keys))
        self.assertTrue(
            check(
                sel(big, little, "id::<u8>"), [], keys,
                lowered_inst_paths=lowered,
            )
        )
        # Every lowered body must be reported, and nothing else may be.
        for bad in (
            sel(big, "id::<u8>"),
            sel(big, little),
            sel(big, big.replace("Big", "Native"), "id::<u8>"),
            sel(big, little, "id::<u16>"),
        ):
            self.assertFalse(
                check(bad, [], keys, lowered_inst_paths=lowered), bad
            )
        # An empty lowering accounts for nothing.
        self.assertFalse(
            check(
                sel(big, little, "id::<u8>"), [], keys,
                lowered_inst_paths=frozenset(),
            )
        )
        # Two requests that lower to one instance leave room under the length
        # bound, which must not admit an unrelated body.
        alias_keys = [("id", ("u8",)), ("id", ("Alias",))]
        one = frozenset({"id::<u8>"})
        self.assertTrue(
            check(sel("id::<u8>"), [], alias_keys, lowered_inst_paths=one)
        )
        self.assertFalse(
            check(
                sel("id::<u8>", "bogus"), [], alias_keys,
                lowered_inst_paths=one,
            )
        )

    def test_unit_receipt_lowers_every_instantiation_when_one_is_unmatched(
        self,
    ):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            proofs_dir, src_dir, unit = make_proof_tree(root)
            impl = "m::_::<impl Tr for m::W<O>>::f"
            insts = [
                {"path": "id", "args": ["u8"]},
                {"path": impl, "args": ["m::Big"]},
            ]
            scope = {
                "kind": "selected_unit",
                "roots": [],
                "instantiations": insts,
            }
            req = json.loads((unit / "request.json").read_text(encoding="utf-8"))
            req["scope"] = scope
            (unit / "request.json").write_text(json.dumps(req), encoding="utf-8")
            ((_, request),) = verify_zerocopy.discover_units(proofs_dir, src_dir)
            lib_sha = verify_zerocopy.anneal_ci_lib.sha256_file(src_dir / "lib.rs")
            fake_cap = root / "anneal-rustc-capture"
            calls = root / "calls.jsonl"
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import json, sys\n"
                "from pathlib import Path\n"
                "args = sys.argv[1:]\n"
                "insts = [json.loads(args[i + 1])\n"
                "         for i, a in enumerate(args) if a == '--instantiate']\n"
                f"with open({str(calls)!r}, 'a') as f:\n"
                "    f.write(json.dumps(insts) + '\\n')\n"
                "out = Path(args[args.index('--out-dir') + 1])\n"
                "out.mkdir(parents=True)\n"
                "paths = [i['path'].replace('<O>', '<' + i['args'][0] + '>')\n"
                "         if '<O>' in i['path']\n"
                "         else i['path'] + '::<' + i['args'][0] + '>'\n"
                "         for i in insts]\n"
                "sel = [{'def_id': n, 'path': p, 'body_index': n}\n"
                "       for n, p in enumerate(paths)]\n"
                "(out / 'capture.json').write_text(json.dumps({'selected': sel}))\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)
            big = "m::_::<impl Tr for m::W<m::Big>>::f"

            def receipt(*paths):
                return make_receipt(
                    scope=scope,
                    selected=[
                        {"def_id": i, "path": p, "body_index": i}
                        for i, p in enumerate(paths)
                    ],
                    sources=[{"relative_path": "lib.rs", "sha256": lib_sha}],
                )

            verify_zerocopy.validate_unit_receipt(
                unit, 0, receipt("id::<u8>", big), request, capture=fake_cap
            )
            # The predicted `id` request is lowered along with the impl one.
            self.assertEqual(
                [json.loads(line) for line in calls.read_text().splitlines()],
                [insts],
            )
            for bad in (
                receipt(big),
                receipt("id::<u8>", big.replace("Big", "Little")),
                receipt("id::<u16>", big),
            ):
                with self.assertRaisesRegex(RuntimeError, "selected mismatch"):
                    verify_zerocopy.validate_unit_receipt(
                        unit, 0, bad, request, capture=fake_cap
                    )

    def test_instantiation_fallback_runs_one_capture_for_all(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            _, _, unit = make_proof_tree(root)
            fake_cap = root / "anneal-rustc-capture"
            calls = root / "calls.jsonl"
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import json, sys\n"
                "from pathlib import Path\n"
                "args = sys.argv[1:]\n"
                "insts = [json.loads(args[i + 1])\n"
                "         for i, a in enumerate(args) if a == '--instantiate']\n"
                f"with open({str(calls)!r}, 'a') as f:\n"
                "    f.write(json.dumps(insts) + '\\n')\n"
                "out = Path(args[args.index('--out-dir') + 1])\n"
                "out.mkdir(parents=True)\n"
                "paths = sorted({i['path'].replace('<O>', '<' + i['args'][0] + '>')\n"
                "                for i in insts})\n"
                "sel = [{'def_id': n, 'path': p, 'body_index': n}\n"
                "       for n, p in enumerate(paths)]\n"
                "(out / 'capture.json').write_text(json.dumps({'selected': sel}))\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)
            impl = "m::_::<impl Tr for m::W<O>>::f"
            keys = [(impl, (f"m::T{i}",)) for i in range(40)]
            lowered = verify_zerocopy.resolve_instantiation_candidates_via_capture(
                unit, DEFAULT_CONFIG, keys, capture=fake_cap
            )
            self.assertEqual(
                lowered,
                frozenset(
                    f"m::_::<impl Tr for m::W<m::T{i}>>::f" for i in range(40)
                ),
            )
            runs = calls.read_text(encoding="utf-8").splitlines()
            self.assertEqual(len(runs), 1)
            self.assertEqual(
                [(i["path"], tuple(i["args"])) for i in json.loads(runs[0])],
                keys,
            )

            # A capture that selects nothing cannot account for any request.
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import json, sys\n"
                "from pathlib import Path\n"
                "args = sys.argv[1:]\n"
                "out = Path(args[args.index('--out-dir') + 1])\n"
                "out.mkdir(parents=True)\n"
                "(out / 'capture.json').write_text(json.dumps({'selected': []}))\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(RuntimeError, "invalid capture.json"):
                verify_zerocopy.resolve_instantiation_candidates_via_capture(
                    unit, DEFAULT_CONFIG, keys, capture=fake_cap
                )

    def test_main_resolves_type_aliased_instantiation_via_capture(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            proofs_dir, src_dir, unit = make_proof_tree(root)
            (src_dir / "lib.rs").write_text(
                "pub type Alias = u8;\n"
                "pub fn id<T>(x: T) -> T { x }\n",
                encoding="utf-8",
            )
            scope = {
                "kind": "selected_unit",
                "roots": [],
                "instantiations": [{"path": "id", "args": ["Alias"]}],
            }
            req = json.loads((unit / "request.json").read_text(encoding="utf-8"))
            req["scope"] = scope
            (unit / "request.json").write_text(
                json.dumps(req), encoding="utf-8"
            )

            lib_sha = verify_zerocopy.anneal_ci_lib.sha256_file(
                src_dir / "lib.rs"
            )

            # Without `capture` lowering, textual validation stays strict.
            receipt_u8 = make_receipt(
                scope=scope,
                selected=[{"def_id": 0, "path": "id::<u8>", "body_index": 0}],
                sources=[{"relative_path": "lib.rs", "sha256": lib_sha}],
            )
            with self.assertRaisesRegex(RuntimeError, "selected mismatch"):
                verify_zerocopy.validate_parsed_receipt(
                    "01_unit",
                    0,
                    receipt_u8,
                    [],
                    scope["instantiations"],
                )

            fake_cli = root / "cargo-anneal"
            fake_cap = root / "anneal-rustc-capture"
            fake_lean = root / "lean"
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            cap_probe = root / "cap_probe.json"
            fake_lean.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_lean.chmod(0o755)
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import json, os, sys\n"
                "from pathlib import Path\n"
                "args = sys.argv[1:]\n"
                f"Path({str(cap_probe)!r}).write_text(\n"
                "    json.dumps({'argv': args, 'env': dict(os.environ)})\n"
                ")\n"
                "out_dir = Path(args[args.index('--out-dir') + 1])\n"
                "inst = json.loads(args[args.index('--instantiate') + 1])\n"
                "out_dir.mkdir(parents=True, exist_ok=False)\n"
                "resolved = 'id::<u8>' if inst == {'path': 'id', 'args': ['Alias']} else 'unexpected'\n"
                "(out_dir / 'capture.json').write_text(\n"
                "    json.dumps({'selected': [{'def_id': 0, 'path': resolved, 'body_index': 0}]})\n"
                ")\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)

            payload_json = json.dumps(receipt_u8)
            fake_cli.write_text(
                "#!/usr/bin/env python3\n"
                f"print({payload_json!r})\n",
                encoding="utf-8",
            )
            fake_cli.chmod(0o755)
            artifacts = root / "out"
            with mock.patch.dict(
                os.environ,
                {
                    "RUSTC_WRAPPER": "bogus-wrapper",
                    "AMBIENT_TEST_SECRET": "leaked",
                    "LD_LIBRARY_PATH": "/bogus/lib",
                    "DYLD_LIBRARY_PATH": "/bogus/dyld",
                },
            ):
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

            probe = json.loads(cap_probe.read_text(encoding="utf-8"))
            lib_key = (
                "DYLD_LIBRARY_PATH"
                if sys.platform == "darwin"
                else "LD_LIBRARY_PATH"
            )
            self.assertEqual(set(probe["env"]) - {"LC_CTYPE"}, {"PATH", lib_key})
            self.assertEqual(probe["env"]["PATH"], "/usr/bin:/bin")
            self.assertEqual(
                probe["env"][lib_key], str(fake_sys.resolve() / "lib")
            )
            self.assertIn(
                "--cfg=no_zerocopy_allocator_api_1_100_0", probe["argv"]
            )
            self.assertIn("--env=CARGO_PKG_VERSION=0.8.64", probe["argv"])
            self.assertNotIn("--cfg", probe["argv"])
            self.assertNotIn("--env", probe["argv"])

            for bad_sel_path in ("id::<bool>", "unrelated::function"):
                bad_payload = json.dumps(
                    make_receipt(
                        scope=scope,
                        selected=[
                            {"def_id": 0, "path": bad_sel_path, "body_index": 0}
                        ],
                        sources=[{"relative_path": "lib.rs", "sha256": lib_sha}],
                    )
                )
                fake_cli.write_text(
                    "#!/usr/bin/env python3\n"
                    f"print({bad_payload!r})\n",
                    encoding="utf-8",
                )
                fake_cli.chmod(0o755)
                with self.assertRaisesRegex(RuntimeError, "selected mismatch"):
                    verify_zerocopy.main([
                        "--proofs-dir", str(proofs_dir),
                        "--src-dir", str(src_dir),
                        "--cli", str(fake_cli),
                        "--capture", str(fake_cap),
                        "--sysroot", str(fake_sys),
                        "--lean", str(fake_lean),
                    ])

            # Non-zero `anneal-rustc-capture` exit (e.g. exit 127 link error)
            # or missing `capture.json` must fail explicitly, never downgrade
            # into a misleading `selected mismatch`.
            fake_cli.write_text(
                "#!/usr/bin/env python3\n"
                f"print({payload_json!r})\n",
                encoding="utf-8",
            )
            fake_cli.chmod(0o755)
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import sys\n"
                "sys.stderr.write('error while loading shared libraries: librustc_driver.so\\n')\n"
                "sys.exit(127)\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)
            with self.assertRaisesRegex(
                RuntimeError, r"rustc-capture failed.*exit 127.*librustc_driver"
            ):
                verify_zerocopy.main([
                    "--proofs-dir", str(proofs_dir),
                    "--src-dir", str(src_dir),
                    "--cli", str(fake_cli),
                    "--capture", str(fake_cap),
                    "--sysroot", str(fake_sys),
                    "--lean", str(fake_lean),
                ])

            fake_cap.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            fake_cap.chmod(0o755)
            with self.assertRaisesRegex(
                RuntimeError, r"rustc-capture failed.*exit 0"
            ):
                verify_zerocopy.main([
                    "--proofs-dir", str(proofs_dir),
                    "--src-dir", str(src_dir),
                    "--cli", str(fake_cli),
                    "--capture", str(fake_cap),
                    "--sysroot", str(fake_sys),
                    "--lean", str(fake_lean),
                ])

            not_a_dir = root / "sysroot_file"
            not_a_dir.write_text("x", encoding="utf-8")
            with self.assertRaisesRegex(
                RuntimeError, r"sysroot is not a directory"
            ):
                verify_zerocopy.resolve_instantiation_candidates_via_capture(
                    unit,
                    DEFAULT_CONFIG,
                    [("id", ("Alias",))],
                    capture=fake_cap,
                    sysroot=not_a_dir,
                )

    def test_discover_units_and_main_reject_root_and_artifacts_symlinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            proofs_dir, src_dir, _ = make_proof_tree(root)

            # Both existing-target and dangling symlinks for `proofs_dir`
            # and `src_dir` must fail closed in `discover_units` and `main()`.
            proofs_link = root / "proofs_link"
            proofs_link.symlink_to(proofs_dir)
            src_link = root / "src_link"
            src_link.symlink_to(src_dir)
            proofs_dangling = root / "proofs_dangling"
            proofs_dangling.symlink_to(root / "missing_proofs")
            src_dangling = root / "src_dangling"
            src_dangling.symlink_to(root / "missing_src")

            for p_arg, s_arg, needle in [
                (proofs_link, src_dir, "symlink disallowed in proofs"),
                (proofs_dangling, src_dir, "symlink disallowed in proofs"),
                (proofs_dir, src_link, "symlink disallowed in src"),
                (proofs_dir, src_dangling, "symlink disallowed in src"),
            ]:
                with self.assertRaisesRegex(RuntimeError, needle):
                    verify_zerocopy.discover_units(p_arg, s_arg)

            # Direct `discover_units` calls without `repo_root` reject both
            # immediate (`zc_link/{proofs,src}`) and deeper (`alias/nested/...`)
            # symlinked ancestors.
            zc_link = root / "zc_link"
            zc_link.symlink_to(root / "zerocopy")
            for p_arg, s_arg, needle in [
                (zc_link / "proofs", src_dir, "symlink disallowed in proofs path"),
                (proofs_dir, zc_link / "src", "symlink disallowed in src path"),
            ]:
                with self.assertRaisesRegex(RuntimeError, needle):
                    verify_zerocopy.discover_units(p_arg, s_arg)

            nested_target = root / "nested_real/inner"
            nested_target.mkdir(parents=True)
            (nested_target / "src").mkdir()
            (nested_target / "src/lib.rs").write_text("", encoding="utf-8")
            nested_alias = root / "nested_alias"
            nested_alias.symlink_to(root / "nested_real")
            for p_arg, s_arg, needle in [
                (
                    nested_alias / "inner/proofs",
                    src_dir,
                    "symlink disallowed in proofs path",
                ),
                (
                    proofs_dir,
                    nested_alias / "inner/src",
                    "symlink disallowed in src path",
                ),
            ]:
                with self.assertRaisesRegex(RuntimeError, needle):
                    verify_zerocopy.discover_units(p_arg, s_arg)

            # Fixture creation under a symlinked TMPDIR (such as macOS
            # `/var` -> `private/var`) still resolves canonical roots.
            sym_tmp_backing = root / "sym_tmp_real"
            sym_tmp_backing.mkdir()
            sym_tmp = root / "sym_tmp_link"
            sym_tmp.symlink_to(sym_tmp_backing)
            with (
                mock.patch.dict(os.environ, {"TMPDIR": str(sym_tmp)}),
                mock.patch.object(tempfile, "tempdir", None),
                tempfile.TemporaryDirectory() as raw_sub_tmp,
            ):
                p_sub, s_sub, _ = make_proof_tree(Path(raw_sub_tmp))
                self.assertEqual(
                    [u.name for u, _ in verify_zerocopy.discover_units(p_sub, s_sub)],
                    ["01_unit"],
                )

            link_hop = root / "zerocopy/link"
            link_hop.symlink_to(root / "zerocopy/src")
            with self.assertRaisesRegex(
                RuntimeError, "symlink disallowed in proofs path"
            ):
                verify_zerocopy.discover_units(
                    root / "zerocopy/link/../proofs",
                    src_dir,
                    repo_root=root,
                )

            # Absolute path starting outside `repo_root` and entering via `..`
            # still enforces `repo_root` symlink hygiene.
            outside_sibling = root.parent / f"{root.name}_reentry_probe"
            outside_reentry = (
                outside_sibling
                / ".."
                / root.name
                / "zc_link"
                / "proofs"
            )
            with self.assertRaisesRegex(
                RuntimeError, "symlink disallowed in proofs path"
            ):
                verify_zerocopy.discover_units(
                    outside_reentry,
                    src_dir,
                    repo_root=root,
                )

            lib_rs = src_dir / "lib.rs"
            other_lib = root / "other_lib.rs"
            other_lib.write_text("", encoding="utf-8")
            lib_rs.unlink()
            lib_rs.symlink_to(other_lib)
            with self.assertRaisesRegex(RuntimeError, "crate root missing"):
                verify_zerocopy.discover_units(proofs_dir, src_dir)
            lib_rs.unlink()
            lib_rs.write_text("", encoding="utf-8")

            fake_cli = root / "cargo-anneal"
            fake_cap = root / "anneal-rustc-capture"
            fake_lean = root / "lean"
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            for bin_path in (fake_cli, fake_cap, fake_lean):
                bin_path.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
                bin_path.chmod(0o755)
            common_args = [
                "--cli", str(fake_cli),
                "--capture", str(fake_cap),
                "--sysroot", str(fake_sys),
                "--lean", str(fake_lean),
            ]

            fake_script = root / "anneal/ci/verify_zerocopy.py"
            fake_script.parent.mkdir(parents=True)
            fake_script.write_text("# stub\n", encoding="utf-8")

            with mock.patch.object(verify_zerocopy, "__file__", str(fake_script)):
                for label, p_arg, s_arg, needle in [
                    (
                        "main_proofs_symlink",
                        str(proofs_link),
                        src_dir,
                        "symlink disallowed in proofs",
                    ),
                    (
                        "main_proofs_dangling",
                        str(proofs_dangling),
                        src_dir,
                        "symlink disallowed in proofs",
                    ),
                    (
                        "main_src_symlink",
                        str(proofs_dir),
                        src_link,
                        "symlink disallowed in src",
                    ),
                    (
                        "main_src_dangling",
                        str(proofs_dir),
                        src_dangling,
                        "symlink disallowed in src",
                    ),
                    (
                        "main_lexical_parent_hop_rel",
                        "zerocopy/link/../proofs",
                        src_dir,
                        "symlink disallowed in proofs",
                    ),
                    (
                        "main_lexical_parent_hop_abs",
                        str(root / "zerocopy/link/../proofs"),
                        src_dir,
                        "symlink disallowed in proofs",
                    ),
                ]:
                    with self.subTest(case=label):
                        orig_cwd = Path.cwd()
                        try:
                            os.chdir(root)
                            with self.assertRaisesRegex(RuntimeError, needle):
                                verify_zerocopy.main([
                                    "--proofs-dir", p_arg,
                                    "--src-dir", str(s_arg),
                                    *common_args,
                                ])
                        finally:
                            os.chdir(orig_cwd)

            # `main()` rejects a symlinked `zerocopy/` parent via relative path.
            rel_repo = root / "rel_repo"
            rel_script = rel_repo / "anneal/ci/verify_zerocopy.py"
            rel_script.parent.mkdir(parents=True)
            rel_script.write_text("# stub\n", encoding="utf-8")
            rel_zc_real = rel_repo / "real_zc"
            rel_zc_real.mkdir(parents=True)
            (root / "zerocopy/proofs").rename(rel_zc_real / "proofs")
            (root / "zerocopy/src").rename(rel_zc_real / "src")
            (rel_repo / "zerocopy").symlink_to(rel_zc_real)
            orig_cwd = Path.cwd()
            try:
                os.chdir(rel_repo)
                with mock.patch.object(verify_zerocopy, "__file__", str(rel_script)):
                    with self.assertRaisesRegex(
                        RuntimeError, "symlink disallowed in proofs path"
                    ):
                        verify_zerocopy.main([
                            "--proofs-dir", "zerocopy/proofs",
                            "--src-dir", "zerocopy/src",
                            *common_args,
                        ])
            finally:
                os.chdir(orig_cwd)
            (rel_zc_real / "proofs").rename(root / "zerocopy/proofs")
            (rel_zc_real / "src").rename(root / "zerocopy/src")

            # Existing and dangling symlink `--artifacts-dir` fail closed,
            # while genuinely external symlinked ancestors succeed identically
            # under both absolute and relative `--artifacts-dir` spellings
            # and outside symlinks entering `repo_root` still check in-repo
            # symlinks fail-closed.
            art_target = root / "real_out"
            art_target.mkdir()
            art_link = root / "art_link"
            art_link.symlink_to(art_target)
            art_dangling = root / "art_dangling"
            art_dangling.symlink_to(root / "missing_out")
            with tempfile.TemporaryDirectory(dir=root) as sub_repo_str:
                sub_repo = Path(sub_repo_str)
                (sub_repo / "link_dir").symlink_to(art_target)
                reentry_art = (
                    root.parent
                    / f"{root.name}_art_probe"
                    / ".."
                    / root.name
                    / sub_repo.name
                    / "link_dir"
                    / "ev_out"
                )
                with self.assertRaisesRegex(
                    RuntimeError, "symlink disallowed in artifacts"
                ):
                    verify_zerocopy._reject_symlink_ancestors_in_repo(
                        reentry_art, "artifacts", repo_root=sub_repo
                    )

            with (
                tempfile.TemporaryDirectory() as ext_tmp_str,
                mock.patch.object(verify_zerocopy, "__file__", str(fake_script)),
            ):
                ext_tmp = real_tmp_root(ext_tmp_str)
                for a_arg in (art_link, art_dangling):
                    with self.assertRaisesRegex(
                        RuntimeError, "symlink disallowed in artifacts"
                    ):
                        verify_zerocopy.main([
                            "--proofs-dir", str(proofs_dir),
                            "--src-dir", str(src_dir),
                            "--artifacts-dir", str(a_arg),
                            *common_args,
                        ])

                # Outside symlink pointing to `repo_root` (or directly into an
                # in-repo symlink) must still reject in-repo symlink components.
                checkout_alias = ext_tmp / "checkout_alias"
                checkout_alias.symlink_to(root)
                rel_checkout_alias = ext_tmp / "rel_checkout_alias"
                rel_checkout_alias.symlink_to(
                    os.path.relpath(root, ext_tmp)
                )
                sneaky_alias = ext_tmp / "sneaky_alias"
                sneaky_alias.symlink_to(root / "zerocopy/link")
                dbl_slash_alias = ext_tmp / "dbl_slash_alias"
                dbl_slash_alias.symlink_to(f"/{root}")
                dbl_slash_in_repo = Path(
                    f"/{root}/zerocopy/link/proofs"
                )
                self.assertEqual(dbl_slash_in_repo.anchor, "//")
                for alias_proofs in (
                    checkout_alias / "zerocopy/link/proofs",
                    rel_checkout_alias / "zerocopy/link/proofs",
                    dbl_slash_alias / "zerocopy/link/proofs",
                    dbl_slash_in_repo,
                    sneaky_alias,
                    sneaky_alias / "sub",
                ):
                    with self.assertRaisesRegex(
                        RuntimeError, "symlink disallowed in proofs"
                    ):
                        verify_zerocopy.main([
                            "--proofs-dir", str(alias_proofs),
                            "--src-dir", str(src_dir),
                            *common_args,
                        ])
                with self.assertRaisesRegex(
                    RuntimeError, "symlink disallowed in artifacts"
                ):
                    verify_zerocopy.main([
                        "--proofs-dir", str(proofs_dir),
                        "--src-dir", str(src_dir),
                        "--artifacts-dir",
                        str(checkout_alias / "art_link/ev"),
                        *common_args,
                    ])

                # Symlink loop along an outside prefix fails closed cleanly.
                loop_a = ext_tmp / "loop_a"
                loop_b = ext_tmp / "loop_b"
                loop_a.symlink_to("loop_b")
                loop_b.symlink_to("loop_a")
                with self.assertRaisesRegex(
                    RuntimeError, "too many symlink levels in artifacts"
                ):
                    verify_zerocopy.main([
                        "--proofs-dir", str(proofs_dir),
                        "--src-dir", str(src_dir),
                        "--artifacts-dir", str(loop_a / "out"),
                        *common_args,
                    ])

                # External symlinked ancestor for `--artifacts-dir` (named
                # `zerocopy`) succeeds identically for both absolute and
                # relative CLI paths, while a relative external leaf symlink
                # still fails closed.
                ext_real = ext_tmp / "ext_real"
                ext_real.mkdir()
                ext_zc = ext_tmp / "external/zerocopy"
                ext_zc.parent.mkdir()
                ext_zc.symlink_to(ext_real)
                with self.assertRaisesRegex(RuntimeError, "invalid JSON receipt"):
                    verify_zerocopy.main([
                        "--proofs-dir", str(proofs_dir),
                        "--src-dir", str(src_dir),
                        "--artifacts-dir", str(ext_zc / "ev_abs"),
                        *common_args,
                    ])
                self.assertTrue((ext_real / "ev_abs").is_dir())

                orig_cwd = Path.cwd()
                try:
                    os.chdir(root)
                    rel_ext_ev = os.path.relpath(ext_zc / "ev_rel", root)
                    self.assertTrue(rel_ext_ev.startswith(".."))
                    with self.assertRaisesRegex(
                        RuntimeError, "invalid JSON receipt"
                    ):
                        verify_zerocopy.main([
                            "--proofs-dir", "zerocopy/proofs",
                            "--src-dir", "zerocopy/src",
                            "--artifacts-dir", rel_ext_ev,
                            *common_args,
                        ])
                    self.assertTrue((ext_real / "ev_rel").is_dir())

                    rel_ext_leaf = os.path.relpath(ext_zc, root)
                    with self.assertRaisesRegex(
                        RuntimeError, "symlink disallowed in artifacts"
                    ):
                        verify_zerocopy.main([
                            "--proofs-dir", "zerocopy/proofs",
                            "--src-dir", "zerocopy/src",
                            "--artifacts-dir", rel_ext_leaf,
                            *common_args,
                        ])
                finally:
                    os.chdir(orig_cwd)

    def test_cargo_pkg_version_doc_only_enforcement(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = real_tmp_root(tmp)
            proofs_dir, src_dir, _ = make_proof_tree(root)
            (root / "zerocopy/Cargo.toml").write_text(
                '[package]\nname = "zerocopy"\nversion = "0.8.65"\n',
                encoding="utf-8",
            )

            # Doc attributes with `concat!(..., env!("CARGO_PKG_VERSION"))`,
            # nested block comments, raw strings, lifetimes, and char escapes
            # must be allowed cleanly.
            valid_rs = """
//! crate doc mentioning env!("CARGO_PKG_VERSION") only in comment
/* outer /* nested env!("CARGO_PKG_VERSION") */ still comment */
pub fn helper<'a>(_s: &'a [u8], _x: u8) -> char {
    let _q = '\\'';
    let _r = r#"not an env macro"#;
    let _b = b'\\n';
    let _ = _x;
    _q
}
pub fn accept_env_param(env: u8, option_env: u8) -> u8 {
    let local = env + option_env;
    struct S { env: u8 }
    let s = S { env: local };
    s.env
}
pub trait NeverTrait {}
impl NeverTrait for ! {
    #[cfg_attr(
        not(feature = "derive"),
        doc = concat!("[d]: https://docs.rs/zerocopy/", env!("CARGO_PKG_VERSION"), "/"),
    )]
    fn ok(&self) {}
}
"""
            (src_dir / "lib.rs").write_text(valid_rs, encoding="utf-8")
            discovered = verify_zerocopy.discover_units(proofs_dir, src_dir)
            self.assertEqual(len(discovered), 1)

            # Executable `env!`, `option_env!`, `core::env!`, macro smuggling,
            # non-doc attributes, `cfg_attr` predicate use, and bare
            # `CARGO_PKG_*` strings must fail closed.
            bad_sources = [
                (
                    "exec_env",
                    'pub fn v() -> &\'static str { env!("CARGO_PKG_VERSION") }\n',
                ),
                (
                    "comment_split_env",
                    'pub fn v() -> &\'static str { env /* x */ ! ("CARGO_PKG_VERSION") }\n',
                ),
                (
                    "option_env",
                    'pub fn v() -> Option<&\'static str> { core::option_env!("CARGO_PKG_VERSION") }\n',
                ),
                (
                    "non_doc_attr",
                    '#[cfg_attr(all(), export_name = env!("CARGO_PKG_VERSION"))]\npub fn f() {}\n',
                ),
                (
                    "cfg_attr_pred",
                    '#[cfg_attr(env!("CARGO_PKG_VERSION"), doc = "hi")]\npub fn f() {}\n',
                ),
                (
                    "doc_alias",
                    '#[doc(alias = env!("CARGO_PKG_VERSION"))]\npub fn f() {}\n',
                ),
                (
                    "doc_other_var",
                    '#[doc = env!("CARGO_PKG_NAME")]\npub fn f() {}\n',
                ),
                (
                    "macro_smuggle",
                    'macro_rules! m { (#[doc = $e:expr]) => { pub fn f() -> &\'static str { $e } }; }\n'
                    'm!(#[doc = concat!("v", env!("CARGO_PKG_VERSION"))]);\n',
                ),
                (
                    "fn_param_attr",
                    'pub fn f(#[doc = concat!(env!("CARGO_PKG_VERSION"))] _x: u8) {}\n',
                ),
                (
                    "nested_comment_trick",
                    '/* a /* b */ */ pub fn v() -> &\'static str { env!("CARGO_PKG_VERSION") }\n',
                ),
                (
                    "bare_cargo_pkg_lit",
                    'pub const K: &\'static str = "CARGO_PKG_VERSION";\n',
                ),
                (
                    "alias_concat_env",
                    'use core::env as e;\n'
                    'pub fn v() -> &\'static str { e!(concat!("CARGO_PKG", "_VERSION")) }\n',
                ),
                (
                    "alias_stringify_env",
                    'use core::env as e;\n'
                    'pub fn v() -> &\'static str { e!(stringify!(CARGO_PKG_VERSION)) }\n',
                ),
                (
                    "group_use_option_env",
                    'use core::{option_env as o};\n'
                    'pub fn v() -> Option<&\'static str> { o!(stringify!(CARGO_PKG_VERSION)) }\n',
                ),
                (
                    "pub_reexport_env",
                    'pub use core::env;\n',
                ),
                (
                    "alias_other_env_var",
                    'use core::env as e;\n'
                    'pub fn v() -> Option<&\'static str> { Some(e!("HOME")) }\n',
                ),
                (
                    "macro_rules_env_other",
                    'macro_rules! m { () => { env!("HOME") }; }\n',
                ),
                (
                    "raw_env_concat",
                    'pub fn v() -> &\'static str { r#env!(concat!("CARGO", "_PKG_VERSION")) }\n',
                ),
                (
                    "macro_forward_env",
                    'macro_rules! fwd { ($m:ident) => { $m!(concat!("CARGO", "_PKG_VERSION")) }; }\n'
                    'pub fn v() -> &\'static str { fwd!(env) }\n',
                ),
                (
                    "macro_forward_raw_env",
                    'macro_rules! fwd { ($m:ident) => { $m!(concat!("CARGO", "_PKG_VERSION")) }; }\n'
                    'pub fn v() -> &\'static str { fwd!(r#env) }\n',
                ),
                (
                    "macro_forward_option_env",
                    'macro_rules! fwd { ($m:ident) => { $m!(concat!("CARGO", "_PKG_VERSION")) }; }\n'
                    'pub fn v() -> Option<&\'static str> { fwd!(r#option_env) }\n',
                ),
            ]
            for label, code in bad_sources:
                with self.subTest(case=label):
                    (src_dir / "lib.rs").write_text(code, encoding="utf-8")
                    with self.assertRaises(RuntimeError):
                        verify_zerocopy.discover_units(proofs_dir, src_dir)

            # Matching `Cargo.toml` and `request.json` versions still allow
            # doc attributes and still enforce doc-only usage unconditionally
            # so `option_env!`/`env!` cannot diverge under `bwrap --clearenv`.
            (root / "zerocopy/Cargo.toml").write_text(
                '[package]\nname = "zerocopy"\nversion = "0.8.64"\n',
                encoding="utf-8",
            )
            (src_dir / "lib.rs").write_text(valid_rs, encoding="utf-8")
            self.assertEqual(
                len(verify_zerocopy.discover_units(proofs_dir, src_dir)), 1
            )
            for label, code in (
                (
                    "match_exec_env",
                    'pub fn v() -> &\'static str { env!("CARGO_PKG_VERSION") }\n',
                ),
                (
                    "match_option_env_name",
                    'pub fn n() -> Option<&\'static str> { option_env!("CARGO_PKG_NAME") }\n',
                ),
            ):
                with self.subTest(case=label):
                    (src_dir / "lib.rs").write_text(code, encoding="utf-8")
                    with self.assertRaises(RuntimeError):
                        verify_zerocopy.discover_units(proofs_dir, src_dir)


if __name__ == "__main__":
    unittest.main()
