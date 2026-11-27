# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared imports and fixture builders for the
`verify_anneal_spec_zerocopy.py` tests."""

from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from types import SimpleNamespace
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
    (root / "zerocopy/proofs").mkdir()

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


def write_spec_sources(unit: Path, files):
    (unit / "spec_sources.json").write_text(
        json.dumps({"files": files}), encoding="utf-8"
    )


def set_source_files(unit: Path, files):
    req_path = unit / "request.json"
    req = json.loads(req_path.read_text(encoding="utf-8"))
    if files is None:
        req["compilation"].pop("source_files", None)
    else:
        req["compilation"]["source_files"] = files
    req_path.write_text(json.dumps(req), encoding="utf-8")


def list_targets_output(cmd):
    """What a fake `--list-targets` reports: one item for the lowering
    fixture, which must not be empty, and none for anything else."""
    if cmd[-1] == f"{verify_anneal_spec_zerocopy.LEAN_COMPILE_FIXTURE}/spec.rs":
        return json.dumps([{"target": "f", "claim": "f", "file": cmd[-1], "kind": "external"}])
    return "[]"
