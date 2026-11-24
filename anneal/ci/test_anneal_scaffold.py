# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and P1/P2/P3 perturbation-survival regression tests for `anneal_scaffold`."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import anneal_scaffold
import verify_zerocopy

UNIT_TY = {"kind": "unit"}
BOOL_TY = {"kind": "bool"}
ISIZE_TY = {"kind": "int", "width": "isize", "signed": False}
U64_TY = {"kind": "int", "width": "i64", "signed": False}


def sample_u64_capture(p2_reordered: bool = False, p3_extra_local: bool = False):
    """Build deterministic `align_down_mask` + `is_aligned_mask` capture fixtures."""
    if not p3_extra_local:
        align_body = {
            "identity": "rust-path-v1::align_down_mask",
            "arg_count": 2,
            "local_tys": [U64_TY, U64_TY, U64_TY, U64_TY, U64_TY, U64_TY],
            "blocks": [{
                "statements": [
                    {"kind": "storage_live", "local": 3},
                    {
                        "kind": "assign",
                        "local": 3,
                        "value": {"kind": "use", "operand": {"kind": "copy", "local": 1}},
                    },
                    {"kind": "storage_live", "local": 4},
                    {"kind": "storage_live", "local": 5},
                    {
                        "kind": "assign",
                        "local": 5,
                        "value": {"kind": "use", "operand": {"kind": "copy", "local": 2}},
                    },
                    {
                        "kind": "assign",
                        "local": 4,
                        "value": {
                            "kind": "unary",
                            "op": "not",
                            "operand": {"kind": "move", "local": 5},
                        },
                    },
                    {"kind": "storage_dead", "local": 5},
                    {
                        "kind": "assign",
                        "local": 0,
                        "value": {
                            "kind": "binary",
                            "op": "bit_and",
                            "left": {"kind": "move", "local": 3},
                            "right": {"kind": "move", "local": 4},
                        },
                    },
                    {"kind": "storage_dead", "local": 4},
                    {"kind": "storage_dead", "local": 3},
                ],
                "terminator": {"kind": "ret"},
            }],
        }
    else:
        align_body = {
            "identity": "rust-path-v1::align_down_mask",
            "arg_count": 2,
            "local_tys": [U64_TY, U64_TY, U64_TY, U64_TY, U64_TY, U64_TY, U64_TY],
            "blocks": [{
                "statements": [
                    {"kind": "storage_live", "local": 3},
                    {"kind": "storage_live", "local": 6},
                    {
                        "kind": "assign",
                        "local": 6,
                        "value": {"kind": "use", "operand": {"kind": "copy", "local": 2}},
                    },
                    {
                        "kind": "assign",
                        "local": 3,
                        "value": {
                            "kind": "unary",
                            "op": "not",
                            "operand": {"kind": "move", "local": 6},
                        },
                    },
                    {"kind": "storage_dead", "local": 6},
                    {"kind": "storage_live", "local": 4},
                    {
                        "kind": "assign",
                        "local": 4,
                        "value": {"kind": "use", "operand": {"kind": "copy", "local": 1}},
                    },
                    {"kind": "storage_live", "local": 5},
                    {
                        "kind": "assign",
                        "local": 5,
                        "value": {"kind": "use", "operand": {"kind": "copy", "local": 3}},
                    },
                    {
                        "kind": "assign",
                        "local": 0,
                        "value": {
                            "kind": "binary",
                            "op": "bit_and",
                            "left": {"kind": "move", "local": 4},
                            "right": {"kind": "move", "local": 5},
                        },
                    },
                    {"kind": "storage_dead", "local": 5},
                    {"kind": "storage_dead", "local": 4},
                    {"kind": "storage_dead", "local": 3},
                ],
                "terminator": {"kind": "ret"},
            }],
        }

    is_aligned_body = {
        "identity": "rust-path-v1::is_aligned_mask",
        "arg_count": 2,
        "local_tys": [BOOL_TY, U64_TY, U64_TY, U64_TY, U64_TY, U64_TY],
        "blocks": [{
            "statements": [
                {"kind": "storage_live", "local": 3},
                {"kind": "storage_live", "local": 4},
                {
                    "kind": "assign",
                    "local": 4,
                    "value": {"kind": "use", "operand": {"kind": "copy", "local": 1}},
                },
                {"kind": "storage_live", "local": 5},
                {
                    "kind": "assign",
                    "local": 5,
                    "value": {"kind": "use", "operand": {"kind": "copy", "local": 2}},
                },
                {
                    "kind": "assign",
                    "local": 3,
                    "value": {
                        "kind": "binary",
                        "op": "bit_and",
                        "left": {"kind": "move", "local": 4},
                        "right": {"kind": "move", "local": 5},
                    },
                },
                {"kind": "storage_dead", "local": 5},
                {"kind": "storage_dead", "local": 4},
                {
                    "kind": "assign",
                    "local": 0,
                    "value": {
                        "kind": "binary",
                        "op": "eq",
                        "left": {"kind": "move", "local": 3},
                        "right": {
                            "kind": "constant",
                            "ty": U64_TY,
                            "lit": {"kind": "scalar", "bits": "0"},
                        },
                    },
                },
                {"kind": "storage_dead", "local": 3},
            ],
            "terminator": {"kind": "ret"},
        }],
    }
    bodies = (
        [is_aligned_body, align_body]
        if p2_reordered
        else [align_body, is_aligned_body]
    )
    return {"program": {"bodies": bodies}}


def sample_isize_capture(p1_extra_local: bool = False, p2_reordered: bool = False):
    """Build deterministic `PointerMetadata` `usize` + `()` capture fixtures."""
    if not p1_extra_local:
        usize_from = {
            "identity": "rust-path-v1::<usize as PointerMetadata>::from_elem_count",
            "arg_count": 1,
            "local_tys": [ISIZE_TY, ISIZE_TY],
            "blocks": [{
                "statements": [{
                    "kind": "assign",
                    "local": 0,
                    "value": {"kind": "use", "operand": {"kind": "copy", "local": 1}},
                }],
                "terminator": {"kind": "ret"},
            }],
        }
    else:
        usize_from = {
            "identity": "rust-path-v1::<usize as PointerMetadata>::from_elem_count",
            "arg_count": 1,
            "local_tys": [ISIZE_TY, ISIZE_TY, ISIZE_TY],
            "blocks": [{
                "statements": [
                    {"kind": "storage_live", "local": 2},
                    {
                        "kind": "assign",
                        "local": 2,
                        "value": {"kind": "use", "operand": {"kind": "copy", "local": 1}},
                    },
                    {
                        "kind": "assign",
                        "local": 0,
                        "value": {"kind": "use", "operand": {"kind": "copy", "local": 2}},
                    },
                    {"kind": "storage_dead", "local": 2},
                ],
                "terminator": {"kind": "ret"},
            }],
        }

    unit_to = {
        "identity": "rust-path-v1::<() as PointerMetadata>::to_elem_count",
        "arg_count": 1,
        "local_tys": [ISIZE_TY, UNIT_TY],
        "blocks": [{
            "statements": [{
                "kind": "assign",
                "local": 0,
                "value": {
                    "kind": "use",
                    "operand": {
                        "kind": "constant",
                        "ty": ISIZE_TY,
                        "lit": {"kind": "scalar", "bits": "0"},
                    },
                },
            }],
            "terminator": {"kind": "ret"},
        }],
    }
    bodies = [unit_to, usize_from] if p2_reordered else [usize_from, unit_to]
    return {"program": {"bodies": bodies}}


def _extract_ok_signature(rendered: str, slug: str) -> str:
    marker = f"theorem ok_{slug} :\n"
    start = rendered.index(marker)
    end = rendered.index(" :=", start)
    return rendered[start:end]


class AnnealScaffoldTests(unittest.TestCase):
    def test_p1_p2_p3_exported_theorem_signatures_stay_identical(self):
        base_isize = anneal_scaffold.render_scaffold(sample_isize_capture())
        p1_isize = anneal_scaffold.render_scaffold(
            sample_isize_capture(p1_extra_local=True)
        )
        p2_isize = anneal_scaffold.render_scaffold(
            sample_isize_capture(p2_reordered=True)
        )
        self.assertEqual(
            _extract_ok_signature(base_isize, "usize_from_elem_count"),
            _extract_ok_signature(p1_isize, "usize_from_elem_count"),
        )
        self.assertEqual(
            _extract_ok_signature(base_isize, "usize_from_elem_count"),
            _extract_ok_signature(p2_isize, "usize_from_elem_count"),
        )
        self.assertIn("def id_usize_from_elem_count : DefId := 0", base_isize)
        self.assertIn("def id_usize_from_elem_count : DefId := 1", p2_isize)
        self.assertIn("theorem all_bodies_safe :", p1_isize)
        self.assertNotIn("set_option", base_isize)
        self.assertNotRegex(base_isize, r"\bsimp\b|\bsimp_all\b")

        base_u64 = anneal_scaffold.render_scaffold(sample_u64_capture())
        p2_u64 = anneal_scaffold.render_scaffold(sample_u64_capture(p2_reordered=True))
        p3_u64 = anneal_scaffold.render_scaffold(
            sample_u64_capture(p3_extra_local=True)
        )
        self.assertEqual(
            _extract_ok_signature(base_u64, "align_down_mask"),
            _extract_ok_signature(p2_u64, "align_down_mask"),
        )
        self.assertEqual(
            _extract_ok_signature(base_u64, "align_down_mask"),
            _extract_ok_signature(p3_u64, "align_down_mask"),
        )
        self.assertIn("scafU64Val (a0 &&& (~~~a1))", p3_u64)
        self.assertTrue(
            all(len(line) <= 100 for line in p3_u64.splitlines()),
            "every generated line must respect <= 100 column gate",
        )

    def test_slug_collision_disambiguation_and_duplicate_identity_rejection(self):
        b1 = {
            "identity": "rust-path-v1::a::foo",
            "arg_count": 0,
            "local_tys": [UNIT_TY],
            "blocks": [{"statements": [], "terminator": {"kind": "ret"}}],
        }
        b2 = {
            "identity": "rust-path-v1::a_foo",
            "arg_count": 0,
            "local_tys": [UNIT_TY],
            "blocks": [{"statements": [], "terminator": {"kind": "ret"}}],
        }
        slugs = anneal_scaffold.assign_unique_slugs([b1, b2])
        self.assertEqual(slugs, ["a_foo", "a_foo_2"])

        with self.assertRaisesRegex(anneal_scaffold.ScaffoldError, "duplicate body"):
            anneal_scaffold.assign_unique_slugs([b1, dict(b1)])

    def test_check_mode_and_symlink_or_duplicate_json_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cap_path = root / "capture.json"
            out_path = root / "AutoScaffold.lean"
            cap_data = sample_isize_capture()
            cap_path.write_text(json.dumps(cap_data), encoding="utf-8")

            rc = anneal_scaffold.main([
                "--capture-json",
                str(cap_path),
                "--output",
                str(out_path),
            ])
            self.assertEqual(rc, 0)
            self.assertEqual(
                anneal_scaffold.main([
                    "--capture-json",
                    str(cap_path),
                    "--output",
                    str(out_path),
                    "--check",
                ]),
                0,
            )

            out_path.write_text(
                out_path.read_text(encoding="utf-8") + "-- drift\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(anneal_scaffold.ScaffoldError, "drift"):
                anneal_scaffold.main([
                    "--capture-json",
                    str(cap_path),
                    "--output",
                    str(out_path),
                    "--check",
                ])

            dup_json = root / "dup.json"
            dup_json.write_text('{"program": {"bodies": []}, "program": {}}', encoding="utf-8")
            with self.assertRaisesRegex(anneal_scaffold.ScaffoldError, "duplicate JSON key"):
                anneal_scaffold.load_strict_json(dup_json)

            sym = root / "sym.json"
            sym.symlink_to(cap_path)
            with self.assertRaisesRegex(anneal_scaffold.ScaffoldError, "symlink"):
                anneal_scaffold.load_strict_json(sym)

    def test_capture_from_request_mocked_cli_and_confinement_guards(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve(strict=True)
            src_dir = root / "src"
            src_dir.mkdir()
            (src_dir / "lib.rs").write_text("#![no_std]\n", encoding="utf-8")
            outside = root / "outside.rs"
            outside.write_text("// outside\n", encoding="utf-8")

            unit_dir = root / "proofs" / "u01"
            unit_dir.mkdir(parents=True)
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            fake_cap = root / "fake_capture.py"
            cap_payload = json.dumps(sample_isize_capture())
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import pathlib, sys\n"
                "args = sys.argv[1:]\n"
                "assert args[0] == 'capture', args\n"
                "assert all(a.startswith('--') and '=' in a for a in args[1:]), args\n"
                "out_dir = pathlib.Path(\n"
                "    next(a.split('=', 1)[1] for a in args if a.startswith('--out-dir='))\n"
                ")\n"
                "out_dir.mkdir(parents=True, exist_ok=True)\n"
                f"(out_dir / 'capture.json').write_text({cap_payload!r}, encoding='utf-8')\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)

            def make_req(
                source_root: str = "../../src", source_files=None, crate_root: str = "lib.rs"
            ):
                return {
                    "schema_version": 1,
                    "compilation": {
                        "source_root": source_root,
                        "crate_root": crate_root,
                        "crate_name": "demo",
                        "edition": "2024",
                        "target": "x86_64-unknown-linux-gnu",
                        "cfg": ['feature="alloc"'],
                        "env": {"RUSTC_BOOTSTRAP": "1"},
                        "source_files": source_files if source_files is not None else ["lib.rs"],
                    },
                    "scope": {
                        "kind": "selected_unit",
                        "roots": ["demo_fn"],
                        "instantiations": [{"root": "demo_fn", "args": []}],
                    },
                }

            req_path = unit_dir / "request.json"
            req_path.write_text(json.dumps(make_req()), encoding="utf-8")
            self.assertEqual(
                anneal_scaffold.main([
                    "--request",
                    str(req_path),
                    "--capture",
                    str(fake_cap),
                    "--sysroot",
                    str(fake_sys),
                ]),
                0,
            )
            self.assertTrue((unit_dir / "AutoScaffold.lean").is_file())
            self.assertEqual(
                anneal_scaffold.main([
                    "--request",
                    str(req_path),
                    "--capture",
                    str(fake_cap),
                    "--sysroot",
                    str(fake_sys),
                    "--check",
                ]),
                0,
            )

            # Reject parent traversal (`..`) in `crate_root` / `source_files`.
            req_path.write_text(
                json.dumps(make_req(source_files=["../outside.rs"])),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                anneal_scaffold.ScaffoldError, "unsafe source_file path"
            ):
                anneal_scaffold.capture_from_request(
                    req_path, capture=fake_cap, sysroot=fake_sys
                )

            # Reject intra-root symlinks (`src/sym.rs -> ../outside.rs`).
            (src_dir / "sym.rs").symlink_to(outside)
            req_path.write_text(
                json.dumps(make_req(source_files=["lib.rs", "sym.rs"])),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(anneal_scaffold.ScaffoldError, "symlink"):
                anneal_scaffold.capture_from_request(
                    req_path, capture=fake_cap, sysroot=fake_sys
                )

            # Reject `source_root` symlink (`proofs/sym_src -> ../src`).
            sym_src = root / "proofs" / "sym_src"
            sym_src.symlink_to(src_dir)
            req_path.write_text(
                json.dumps(make_req(source_root="../sym_src")),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(anneal_scaffold.ScaffoldError, "symlink"):
                anneal_scaffold.capture_from_request(
                    req_path, capture=fake_cap, sysroot=fake_sys
                )

    def test_live_p1_p2_p3_zero_proof_edit_survival_when_toolchain_present(self):
        """When Anneal toolchain env vars are configured, run real kernel-checked
        P1, P2, and P3 perturbations asserting 0 edits to `Proof.lean`."""
        anneal_root = _CI_DIR.parent
        repo_root = anneal_root.parent
        tools = {
            "cli": verify_zerocopy.env_tool(["ANNEAL_CLI", "ANNEAL_TEST_CARGO_ANNEAL"]),
            "capture": verify_zerocopy.env_tool(
                ["ANNEAL_CAPTURE"], "bin/anneal-rustc-capture"
            ),
            "sysroot": verify_zerocopy.env_tool(
                ["ANNEAL_SYSROOT", "ANNEAL_TEST_RUST_SYSROOT"], "rust"
            ),
            "lean": verify_zerocopy.env_tool(["ANNEAL_LEAN"], "lean/bin/lean"),
        }
        if any(v is None or not v.exists() for v in tools.values()):
            missing = sorted(k for k, v in tools.items() if v is None or not v.exists())
            msg = f"live P1/P2/P3 kernel test requires ANNEAL_* toolchain paths: {missing}"
            # CI sets this so a misconfigured toolchain fails instead of skipping.
            if os.environ.get("ANNEAL_REQUIRE_LIVE_SCAFFOLD_TEST") == "1":
                self.fail(msg)
            self.skipTest(msg)

        cli = tools["cli"].resolve(strict=True)
        capture = tools["capture"].resolve(strict=True)
        sysroot = tools["sysroot"].resolve(strict=True)
        lean = tools["lean"].resolve(strict=True)
        env = dict(os.environ, LD_LIBRARY_PATH=str(sysroot / "lib"))

        # 1. P1 & P2 on `zerocopy/proofs/04_substantive_and_frombytes_markers`
        orig_unit = repo_root / "zerocopy/proofs/04_substantive_and_frombytes_markers"
        orig_proof_bytes = (orig_unit / "Proof.lean").read_bytes()

        def mutate_p1(lib_rs: str) -> str:
            old = "    fn from_elem_count(elems: usize) -> usize {\n        elems\n    }"
            new = (
                "    fn from_elem_count(elems: usize) -> usize {\n"
                "        let count_copy = elems;\n"
                "        count_copy\n"
                "    }"
            )
            assert old in lib_rs
            return lib_rs.replace(old, new, 1)

        def mutate_p2(lib_rs: str) -> str:
            m1 = "impl PointerMetadata for () {"
            m2 = "impl PointerMetadata for usize {"
            i1 = lib_rs.index(m1)
            i2 = lib_rs.index(m2, i1)
            i3 = lib_rs.index("\n}\n", i2 + len(m2)) + 3
            return (
                lib_rs[:i1]
                + lib_rs[i2:i3]
                + "\n"
                + lib_rs[i1:i2].rstrip("\n")
                + "\n"
                + lib_rs[i3:]
            )

        for label, mut_fn in (("P1", mutate_p1), ("P2", mutate_p2)):
            with self.subTest(perturbation=label), tempfile.TemporaryDirectory() as td:
                work = Path(td)
                shutil.copytree(repo_root / "zerocopy/src", work / "zerocopy/src")
                lib_path = work / "zerocopy/src/lib.rs"
                lib_path.write_text(
                    mut_fn(lib_path.read_text(encoding="utf-8")), encoding="utf-8"
                )
                dst_proofs = work / "zerocopy/proofs"
                (dst_proofs).mkdir(parents=True)
                (dst_proofs / "README.md").write_text("# Proofs\n", encoding="utf-8")
                dst_unit = dst_proofs / orig_unit.name
                shutil.copytree(orig_unit, dst_unit)

                anneal_scaffold.main([
                    "--request",
                    str(dst_unit / "request.json"),
                    "--cli",
                    str(cli),
                    "--capture",
                    str(capture),
                    "--sysroot",
                    str(sysroot),
                    "--lean",
                    str(lean),
                ])
                # Assert 0 edits to hand-authored Proof.lean!
                self.assertEqual((dst_unit / "Proof.lean").read_bytes(), orig_proof_bytes)
                rc = verify_zerocopy.main([
                    "--proofs-dir",
                    str(dst_proofs),
                    "--src-dir",
                    str(work / "zerocopy/src"),
                    "--cli",
                    str(cli),
                    "--capture",
                    str(capture),
                    "--sysroot",
                    str(sysroot),
                    "--lean",
                    str(lean),
                    "--jobs",
                    "1",
                ])
                self.assertEqual(rc, 0)

        # 2. P3 (`let inv = !mask; addr & inv`) on 4-fn `u64` alignment crate
        rust_base = (
            "#![no_std]\n"
            "pub fn align_down_mask(addr: u64, mask: u64) -> u64 { addr & !mask }\n"
            "pub fn align_bits_in_mask(addr: u64, mask: u64) -> u64 { addr & mask }\n"
            "pub fn is_aligned_mask(addr: u64, mask: u64) -> bool { (addr & mask) == 0 }\n"
            "pub fn align_down_page(addr: u64) -> u64 { addr & !0xfffu64 }\n"
        )
        rust_p3 = rust_base.replace(
            "{ addr & !mask }",
            "{ let inv = !mask; addr & inv }",
            1,
        )
        spec_lean = (
            "prelude\n"
            "import Init.Data.BitVec.Basic\n"
            "import Trusted.MirSemantics\n"
            "namespace Spec\n"
            "open Trusted.MirAst Trusted.MirSemantics\n"
            "abbrev Word64 := BitVec 64\n"
            "def u64Val (n : Word64) : Val := .scalar ⟨.i64, false, BitVec.ofNat 128 n.toNat⟩\n"
            "def boolVal (b : Bool) : Val := .bool b\n"
            "noncomputable def ReturnsTotal\n"
            "    (p : Program) (d : DefId) (args : List Val) (ret : Val) : Prop :=\n"
            "  let entry := entryProgForBody p d\n"
            "  let call : Query := { args := args }\n"
            "  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩\n"
            "  SatisfiesPost entry call (fun o => o = expected) ∧\n"
            "    ¬ Diverges entry call ∧ Behavior entry call expected\n"
            "def safetyPrecondition (id : String) (args : List Val) : Prop :=\n"
            "  ((id = \"rust-path-v1::align_down_mask\" ∨\n"
            "    id = \"rust-path-v1::align_bits_in_mask\" ∨\n"
            "    id = \"rust-path-v1::is_aligned_mask\") ∧\n"
            "    ∃ a m : Word64, args = [u64Val a, u64Val m]) ∨\n"
            "  (id = \"rust-path-v1::align_down_page\" ∧ ∃ a : Word64, args = [u64Val a])\n"
            "noncomputable def propSpec (p : Program) : Prop :=\n"
            "  p.bodies.length = 4 ∧\n"
            "  (∃ d b, getElem? p.bodies d = some b ∧\n"
            "    b.identity = \"rust-path-v1::align_down_mask\" ∧\n"
            "    ∀ a m : Word64, ReturnsTotal p d [u64Val a, u64Val m] (u64Val (a &&& ~~~m))) ∧\n"
            "  (∃ d b, getElem? p.bodies d = some b ∧\n"
            "    b.identity = \"rust-path-v1::align_bits_in_mask\" ∧\n"
            "    ∀ a m : Word64, ReturnsTotal p d [u64Val a, u64Val m] (u64Val (a &&& m))) ∧\n"
            "  (∃ d b, getElem? p.bodies d = some b ∧\n"
            "    b.identity = \"rust-path-v1::is_aligned_mask\" ∧\n"
            "    ∀ a m : Word64,\n"
            "      ReturnsTotal p d [u64Val a, u64Val m]\n"
            "        (boolVal ((a &&& m) == BitVec.ofNat 64 0))) ∧\n"
            "  (∃ d b, getElem? p.bodies d = some b ∧\n"
            "    b.identity = \"rust-path-v1::align_down_page\" ∧\n"
            "    ∀ a : Word64,\n"
            "      ReturnsTotal p d [u64Val a] (u64Val (a &&& ~~~(BitVec.ofNat 64 0xfff))))\n"
            "noncomputable def specs : Specs := ⟨safetyPrecondition, propSpec⟩\n"
            "end Spec\n"
        )
        hand_proof = (
            "prelude\n"
            "import Expected\n"
            "import AutoScaffold\n"
            "namespace Proof\n"
            "open AutoScaffold\n"
            "theorem verify : Expected.claim :=\n"
            "  ⟨rfl, rfl, rfl, rfl, rfl, rfl, all_bodies_safe,\n"
            "    ⟨rfl,\n"
            "      ⟨id_align_down_mask, body_align_down_mask,\n"
            "        get_align_down_mask, rfl, ok_align_down_mask.2⟩,\n"
            "      ⟨id_align_bits_in_mask, body_align_bits_in_mask,\n"
            "        get_align_bits_in_mask, rfl, ok_align_bits_in_mask.2⟩,\n"
            "      ⟨id_is_aligned_mask, body_is_aligned_mask,\n"
            "        get_is_aligned_mask, rfl, ok_is_aligned_mask.2⟩,\n"
            "      ⟨id_align_down_page, body_align_down_page,\n"
            "        get_align_down_page, rfl, ok_align_down_page.2⟩⟩⟩\n"
            "end Proof\n"
        )
        # A 60-character slug exercises the long-identifier wrapping paths.
        long_name = "align_down_mask_with_a_deliberately_long_identifier_name_xyz"
        self.assertEqual(len(long_name), 60)

        def lengthen(text: str) -> str:
            return text.replace("align_down_mask", long_name)

        p3_cases = (
            ("P3_base", rust_base, spec_lean, hand_proof),
            ("P3_perturbed", rust_p3, spec_lean, hand_proof),
            ("P3_long_slug", lengthen(rust_base), lengthen(spec_lean), lengthen(hand_proof)),
        )
        for p3_label, src_code, spec_text, proof_text in p3_cases:
            with self.subTest(perturbation=p3_label), tempfile.TemporaryDirectory() as td:
                work = Path(td)
                (work / "src").mkdir()
                (work / "src/lib.rs").write_text(src_code, encoding="utf-8")
                pdir = work / "proofs"
                pdir.mkdir()
                (pdir / "Spec.lean").write_text(spec_text, encoding="utf-8")
                (pdir / "Proof.lean").write_text(proof_text, encoding="utf-8")
                req_path = pdir / "request.json"
                req_path.write_text(
                    json.dumps({
                        "schema_version": 1,
                        "compilation": {
                            "source_root": "../src",
                            "crate_root": "lib.rs",
                            "crate_name": "align_bench",
                            "edition": "2021",
                            "target": "x86_64-unknown-linux-gnu",
                            "cfg": [],
                            "env": {},
                            "source_files": ["lib.rs"],
                        },
                        "scope": {
                            "kind": "selected_unit",
                            "roots": [
                                lengthen("align_down_mask")
                                if p3_label == "P3_long_slug"
                                else "align_down_mask",
                                "align_bits_in_mask",
                                "is_aligned_mask",
                                "align_down_page",
                            ],
                        },
                        "proof": {
                            "source_root": ".",
                            "specification": "Spec.specs",
                            "theorem": "Proof.verify",
                            "sources": [
                                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                                {
                                    "module": "AutoScaffold",
                                    "path": "AutoScaffold.lean",
                                    "role": "proof",
                                },
                                {"module": "Proof", "path": "Proof.lean", "role": "proof"},
                            ],
                        },
                    }),
                    encoding="utf-8",
                )
                anneal_scaffold.main([
                    "--request",
                    str(req_path),
                    "--cli",
                    str(cli),
                    "--capture",
                    str(capture),
                    "--sysroot",
                    str(sysroot),
                    "--lean",
                    str(lean),
                ])
                self.assertEqual((pdir / "Proof.lean").read_text(encoding="utf-8"), proof_text)
                scaffold_text = (pdir / "AutoScaffold.lean").read_text(encoding="utf-8")
                self.assertTrue(all(len(line) <= 100 for line in scaffold_text.splitlines()))
                if p3_label == "P3_long_slug":
                    self.assertIn(f"private theorem exec_{long_name}", scaffold_text)
                proc = subprocess.run(
                    [
                        str(cli),
                        "verify",
                        "--request",
                        str(req_path),
                        "--capture",
                        str(capture),
                        "--sysroot",
                        str(sysroot),
                        "--lean",
                        str(lean),
                    ],
                    cwd=pdir,
                    env=env,
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
                receipt = json.loads(proc.stdout)
                self.assertEqual(receipt["status"], "selected_unit_verified")
                self.assertEqual(receipt["taint_reasons"], [])

    def test_long_slug_and_deep_u64_chain_respect_100_col_gate(self):
        long_slug = "AtomicUsize_TryFromBytes_marker_very_long_subsystem_helper_nm"
        self.assertEqual(len(long_slug), 61)
        long_ident = f"rust-path-v1::{long_slug}"
        stmts: list[dict] = [
            {"kind": "storage_live", "local": 3},
            {"kind": "storage_live", "local": 4},
            {
                "kind": "assign",
                "local": 4,
                "value": {"kind": "use", "operand": {"kind": "copy", "local": 1}},
            },
            {
                "kind": "assign",
                "local": 3,
                "value": {
                    "kind": "unary",
                    "op": "not",
                    "operand": {"kind": "move", "local": 4},
                },
            },
            {"kind": "storage_dead", "local": 4},
        ]
        # Chain 6 alternating bitwise ops so symbolic expressions exceed 100 chars.
        next_local = 5
        cur = 3
        for idx in range(6):
            rhs_tmp = next_local
            out_tmp = next_local + 1
            next_local += 2
            stmts.extend([
                {"kind": "storage_live", "local": out_tmp},
                {"kind": "storage_live", "local": rhs_tmp},
                {
                    "kind": "assign",
                    "local": rhs_tmp,
                    "value": {
                        "kind": "use",
                        "operand": {"kind": "copy", "local": 1 if idx % 2 == 0 else 2},
                    },
                },
                {
                    "kind": "assign",
                    "local": out_tmp,
                    "value": {
                        "kind": "binary",
                        "op": "bit_and" if idx % 2 == 0 else "bit_or",
                        "left": {"kind": "move", "local": cur},
                        "right": {"kind": "move", "local": rhs_tmp},
                    },
                },
                {"kind": "storage_dead", "local": rhs_tmp},
                {"kind": "storage_dead", "local": cur},
            ])
            cur = out_tmp
        stmts.extend([
            {
                "kind": "assign",
                "local": 0,
                "value": {"kind": "use", "operand": {"kind": "move", "local": cur}},
            },
            {"kind": "storage_dead", "local": cur},
        ])
        cap = {
            "program": {
                "bodies": [{
                    "identity": long_ident,
                    "arg_count": 2,
                    "local_tys": [U64_TY] * next_local,
                    "blocks": [{"statements": stmts, "terminator": {"kind": "ret"}}],
                }]
            }
        }
        rendered = anneal_scaffold.render_scaffold(cap)
        self.assertTrue(
            all(len(line) <= 100 for line in rendered.splitlines()),
            "every generated line must stay <= 100 cols",
        )
        # The `u64` template (not the `s1_only` fallback) must have rendered.
        self.assertIn(f"private theorem exec_{long_slug}", rendered)
        self.assertIn(f"theorem ok_{long_slug} :", rendered)
        self.assertIn(f"ok_{long_slug}.1", rendered)
        self.assertIn("theorem all_bodies_safe :", rendered)
        self.assertGreaterEqual(rendered.count("(.next (next := s"), 20)
        self.assertGreaterEqual(rendered.count("(step_u64And "), 3)
        self.assertGreaterEqual(rendered.count("(step_u64Or "), 3)

    def test_every_template_renders_max_length_slugs_within_100_cols(self):
        def ident(tag: str) -> str:
            name = f"{tag}_" + "x" * (anneal_scaffold.MAX_SLUG_LEN - len(tag) - 1)
            self.assertEqual(len(name), anneal_scaffold.MAX_SLUG_LEN)
            return f"rust-path-v1::{name}"

        unit0 = {
            "identity": ident("unit0"),
            "arg_count": 0,
            "local_tys": [UNIT_TY],
            "blocks": [{"statements": [], "terminator": {"kind": "ret"}}],
        }
        const_unit = sample_isize_capture()["program"]["bodies"][1]
        const_unit = dict(const_unit, identity=ident("const_unit"))
        const_isize = {
            "identity": ident("const_isize"),
            "arg_count": 1,
            "local_tys": [ISIZE_TY, ISIZE_TY],
            "blocks": [dict(const_unit["blocks"][0])],
        }
        isize_copy = sample_isize_capture(p1_extra_local=True)["program"]["bodies"][0]
        isize_copy = dict(isize_copy, identity=ident("isize_copy"))
        u64_two = sample_u64_capture()["program"]["bodies"][0]
        u64_two = dict(u64_two, identity=ident("u64_two"))
        u64_bool = sample_u64_capture()["program"]["bodies"][1]
        u64_bool = dict(u64_bool, identity=ident("u64_bool"))
        bodies = [unit0, const_unit, const_isize, isize_copy, u64_two, u64_bool]
        rendered = anneal_scaffold.render_scaffold({"program": {"bodies": bodies}})
        self.assertTrue(all(len(line) <= 100 for line in rendered.splitlines()))
        for body in bodies:
            slug = body["identity"].removeprefix("rust-path-v1::")
            self.assertIn(f"theorem ok_{slug} :", rendered)
        for helper in (
            "unit0_ok", "unit_const_1arg_ok", "isize_const_1arg_ok",
            "isize_id_1arg_ok", "u64_arg2_ok",
        ):
            self.assertRegex(rendered, rf"(?m)^  {helper}\b")
        self.assertIn("theorem all_bodies_safe :", rendered)

        # Over-long slugs are truncated deterministically and stay distinct.
        over_a = dict(unit0, identity=ident("unit0") + "_tail_a")
        over_b = dict(unit0, identity=ident("unit0") + "_tail_b")
        slugs = anneal_scaffold.assign_unique_slugs([over_a, over_b, unit0])
        self.assertEqual(len(set(slugs)), 3)
        self.assertTrue(all(len(s) <= anneal_scaffold.MAX_SLUG_LEN for s in slugs))
        self.assertEqual(slugs, anneal_scaffold.assign_unique_slugs([over_a, over_b, unit0]))
        collide = anneal_scaffold.assign_unique_slugs(
            [unit0, dict(unit0, identity=unit0["identity"].replace("_", "::", 1))]
        )
        self.assertEqual(collide[1], collide[0][:-2] + "_2")
        rendered = anneal_scaffold.render_scaffold(
            {"program": {"bodies": [over_a, over_b]}}
        )
        self.assertTrue(all(len(line) <= 100 for line in rendered.splitlines()))

    def test_u64_max_constants_reflow_within_100_cols(self):
        max_bits = str((1 << 64) - 1)
        page_bits = str((1 << 64) - 4096)

        def const(bits: str) -> dict:
            return {"kind": "constant", "ty": U64_TY, "lit": {"kind": "scalar", "bits": bits}}

        def assign(local: int, value: dict) -> dict:
            return {"kind": "assign", "local": local, "value": value}

        def binary(op: str, left: dict, right: dict) -> dict:
            return {"kind": "binary", "op": op, "left": left, "right": right}

        def body(name: str, ret_ty: dict, args: int, temps: int, stmts: list) -> dict:
            lives = [
                {"kind": "storage_live", "local": i}
                for i in range(1 + args, 1 + args + temps)
            ]
            return {
                "identity": f"rust-path-v1::{name}",
                "arg_count": args,
                "local_tys": [ret_ty] + [U64_TY] * (args + temps),
                "blocks": [{"statements": lives + stmts, "terminator": {"kind": "ret"}}],
            }

        copy1, copy2 = {"kind": "copy", "local": 1}, {"kind": "copy", "local": 2}
        bodies = [
            # `!((a & 1) & u64::MAX)`
            body("not_and_max", U64_TY, 1, 2, [
                assign(2, binary("bit_and", copy1, const("1"))),
                assign(3, binary("bit_and", {"kind": "move", "local": 2}, const(max_bits))),
                assign(0, {"kind": "unary", "op": "not",
                           "operand": {"kind": "move", "local": 3}}),
            ]),
            # `(((a & m) | m) & !0xfff) == u64::MAX`
            body("eq_max", BOOL_TY, 2, 3, [
                assign(3, binary("bit_and", copy1, copy2)),
                assign(4, binary("bit_or", {"kind": "move", "local": 3}, copy2)),
                assign(5, binary("bit_and", {"kind": "move", "local": 4}, const(page_bits))),
                assign(0, binary("eq", {"kind": "move", "local": 5}, const(max_bits))),
            ]),
        ]
        for b in bodies:
            self.assertIsNotNone(anneal_scaffold.analyze_u64_straight_line(b))
        rendered = anneal_scaffold.render_scaffold({"program": {"bodies": bodies}})
        self.assertTrue(all(len(line) <= 100 for line in rendered.splitlines()))
        self.assertIn("private theorem exec_not_and_max", rendered)
        self.assertIn("private theorem exec_eq_max", rendered)
        self.assertIn(f"(step_u64EqConst (((a0 &&& a1) ||| a1) &&&\n", rendered)

    def test_reflow_splits_only_inside_brackets(self):
        inside = "  (" + " &&& ".join(["(BitVec.ofNat 64 18446744073709551615)"] * 3) + ")"
        lines = anneal_scaffold._reflow_long_line(inside)
        self.assertGreater(len(lines), 1)
        self.assertTrue(all(len(line) <= 100 for line in lines))
        self.assertEqual(" ".join(x.strip() for x in lines), inside.strip())
        outside = "  " + " &&& ".join(["x" * 30] * 4)
        self.assertEqual(anneal_scaffold._reflow_long_line(outside), [outside])

    def test_capture_from_request_clean_env_joined_flags_and_symlink_main(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve(strict=True)
            src_dir = root / "src"
            src_dir.mkdir()
            (src_dir / "lib.rs").write_text("#![no_std]\n", encoding="utf-8")
            unit_dir = root / "proofs/u01"
            unit_dir.mkdir(parents=True)
            fake_sys = root / "sysroot"
            (fake_sys / "lib").mkdir(parents=True)
            cap_log = root / "cap_inv.json"
            fake_cap = root / "fake_capture.py"
            cap_payload = json.dumps(sample_isize_capture())
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import json, os, pathlib, sys\n"
                "args = sys.argv[1:]\n"
                f"pathlib.Path({str(cap_log)!r}).write_text(\n"
                "    json.dumps({'args': args, 'env': dict(os.environ)})\n"
                ")\n"
                "out_dir = pathlib.Path(\n"
                "    next(a.split('=', 1)[1] for a in args if a.startswith('--out-dir='))\n"
                ")\n"
                "out_dir.mkdir(parents=True, exist_ok=True)\n"
                f"(out_dir / 'capture.json').write_text({cap_payload!r}, encoding='utf-8')\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)
            req_path = unit_dir / "request.json"
            req_path.write_text(
                json.dumps({
                    "schema_version": 1,
                    "compilation": {
                        "source_root": "../../src",
                        "crate_root": "lib.rs",
                        "crate_name": "demo",
                        "cfg": ["-Zmiri-tag", 'feature="alloc"'],
                        "env": {"-DASH_KEY": "-val", "FOO": "bar"},
                        "source_files": ["lib.rs"],
                    },
                    "scope": {"kind": "selected_unit", "roots": ["demo_fn"]},
                }),
                encoding="utf-8",
            )
            with mock.patch.dict(os.environ, {"LEAK_SECRET": "nope"}):
                rc = anneal_scaffold.main([
                    "--request",
                    str(req_path),
                    "--capture",
                    str(fake_cap),
                    "--sysroot",
                    str(fake_sys),
                ])
            self.assertEqual(rc, 0)
            logged = json.loads(cap_log.read_text(encoding="utf-8"))
            self.assertNotIn("LEAK_SECRET", logged["env"])
            self.assertEqual(logged["env"]["PATH"], "/usr/bin:/bin")
            self.assertEqual(logged["env"]["LD_LIBRARY_PATH"], str(fake_sys / "lib"))
            self.assertIn("--cfg=-Zmiri-tag", logged["args"])
            self.assertIn("--env=-DASH_KEY=-val", logged["args"])
            self.assertIn("--env=FOO=bar", logged["args"])
            # Every value-bearing flag travels as one `--flag=value` token.
            self.assertEqual(logged["args"][0], "capture")
            for arg in logged["args"][1:]:
                self.assertRegex(arg, r"^--[a-z-]+=")
            for flag in (
                "--crate-name=demo",
                "--crate-type=lib",
                "--panic=unwind",
                "--edition=2024",
                "--target=x86_64-unknown-linux-gnu",
                f"--sysroot={fake_sys}",
                f"--crate-root={src_dir / 'lib.rs'}",
                f"--source-file={src_dir / 'lib.rs'}",
                "--select=demo_fn",
            ):
                self.assertIn(flag, logged["args"])

            # Toolchain inputs may be symlinks (elan, Nix profiles).
            sym_cap = root / "sym_cap"
            sym_cap.symlink_to(fake_cap)
            sym_sys = root / "sym_sys"
            sym_sys.symlink_to(fake_sys)
            for tool_args in (
                ["--capture", str(sym_cap), "--sysroot", str(fake_sys)],
                ["--capture", str(fake_cap), "--sysroot", str(sym_sys)],
            ):
                with self.subTest(tool_args=tool_args):
                    self.assertEqual(
                        anneal_scaffold.main(["--request", str(req_path), *tool_args]), 0
                    )
            anneal_scaffold.capture_from_request(req_path, capture=sym_cap, sysroot=sym_sys)

            sym_out = root / "sym_out.lean"
            sym_out.symlink_to(unit_dir / "AutoScaffold.lean")
            with self.assertRaisesRegex(anneal_scaffold.ScaffoldError, "symlink"):
                anneal_scaffold.main([
                    "--request",
                    str(req_path),
                    "--output",
                    str(sym_out),
                    "--capture",
                    str(fake_cap),
                    "--sysroot",
                    str(fake_sys),
                ])

    def test_u64_zst_temporary_falls_back_to_s1(self):
        # `storage_live` on a `()` temporary yields `.immediate (some .unit)`,
        # which the `u64` template's `.immediate none` slot model cannot match.
        base = sample_u64_capture()["program"]["bodies"][0]
        self.assertIsNotNone(anneal_scaffold.analyze_u64_straight_line(base))
        stmts = base["blocks"][0]["statements"]
        zst = dict(
            base,
            local_tys=base["local_tys"] + [UNIT_TY],
            blocks=[{
                "statements": [{"kind": "storage_live", "local": 6}]
                + stmts
                + [{"kind": "storage_dead", "local": 6}],
                "terminator": {"kind": "ret"},
            }],
        )
        self.assertIsNone(anneal_scaffold.analyze_u64_straight_line(zst))
        rendered = anneal_scaffold.render_scaffold({"program": {"bodies": [zst]}})
        self.assertNotIn("private theorem exec_align_down_mask", rendered)
        self.assertNotIn("theorem all_bodies_safe :", rendered)

    def test_unannotated_temporaries_fall_back_to_s1(self):
        # `initLocalsLoop` starts a temporary without any `StorageLive` or
        # `StorageDead` marker as `liveUninitSlot ty`, not `.dead`.
        base = sample_u64_capture()["program"]["bodies"][0]
        unannotated = dict(base, local_tys=base["local_tys"] + [U64_TY])
        self.assertIsNone(anneal_scaffold.analyze_u64_straight_line(unannotated))

        isize = sample_isize_capture(p1_extra_local=True)["program"]["bodies"][0]
        self.assertIsNotNone(anneal_scaffold.analyze_isize_copy_chain(isize))
        isize_unannotated = dict(
            isize,
            local_tys=isize["local_tys"] + [ISIZE_TY],
        )
        self.assertIsNone(anneal_scaffold.analyze_isize_copy_chain(isize_unannotated))

    def test_u64_eq_const_after_12_nots_against_u64_max_fits_100_cols(self):
        nots = 12
        temps = list(range(2, 2 + nots))
        stmts: list[dict] = [{"kind": "storage_live", "local": t} for t in temps]
        prev = {"kind": "copy", "local": 1}
        for t in temps:
            stmts.append({
                "kind": "assign",
                "local": t,
                "value": {"kind": "unary", "op": "not", "operand": prev},
            })
            prev = {"kind": "move", "local": t}
        stmts.append({
            "kind": "assign",
            "local": 0,
            "value": {
                "kind": "binary",
                "op": "eq",
                "left": prev,
                "right": {
                    "kind": "constant",
                    "ty": U64_TY,
                    "lit": {"kind": "scalar", "bits": str((1 << 64) - 1)},
                },
            },
        })
        stmts.extend({"kind": "storage_dead", "local": t} for t in reversed(temps))
        body = {
            "identity": "rust-path-v1::not12_eq_max",
            "arg_count": 1,
            "local_tys": [BOOL_TY, U64_TY] + [U64_TY] * nots,
            "blocks": [{"statements": stmts, "terminator": {"kind": "ret"}}],
        }
        self.assertIsNotNone(anneal_scaffold.analyze_u64_straight_line(body))
        rendered = anneal_scaffold.render_scaffold({"program": {"bodies": [body]}})
        self.assertTrue(all(len(line) <= 100 for line in rendered.splitlines()))
        self.assertIn("private theorem exec_not12_eq_max", rendered)
        self.assertIn("(step_u64EqConst (", rendered)

    def test_check_mode_compares_bytes_and_rejects_crlf_or_lone_cr(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cap_path = root / "capture.json"
            cap_path.write_text(json.dumps(sample_isize_capture()), encoding="utf-8")
            out_path = root / "AutoScaffold.lean"
            base_argv = ["--capture-json", str(cap_path), "--output", str(out_path)]
            self.assertEqual(anneal_scaffold.main(base_argv), 0)
            lf_bytes = out_path.read_bytes()
            self.assertNotIn(b"\r", lf_bytes)
            self.assertEqual(anneal_scaffold.main([*base_argv, "--check"]), 0)
            for label, newline in (("CRLF", b"\r\n"), ("CR", b"\r")):
                with self.subTest(newline=label):
                    out_path.write_bytes(lf_bytes.replace(b"\n", newline))
                    with self.assertRaisesRegex(anneal_scaffold.ScaffoldError, "drift"):
                        anneal_scaffold.main([*base_argv, "--check"])

    def test_helper_names_are_reserved_against_per_body_names(self):
        self.assertIn("ok_of_executes", anneal_scaffold.helper_declared_names())
        self.assertIn("of_executes", anneal_scaffold.reserved_body_slugs())
        unit0 = {
            "identity": "rust-path-v1::of_executes",
            "arg_count": 0,
            "local_tys": [UNIT_TY],
            "blocks": [{"statements": [], "terminator": {"kind": "ret"}}],
        }
        self.assertEqual(anneal_scaffold.assign_unique_slugs([unit0]), ["of_executes_2"])

        # Every top-level declaration across all templates must be unique and
        # be either a helper or a `<per-body prefix>_<slug>` declaration.
        bodies = [
            unit0,
            dict(sample_isize_capture()["program"]["bodies"][1], identity="rust-path-v1::c"),
            sample_isize_capture(p1_extra_local=True)["program"]["bodies"][0],
            *sample_u64_capture()["program"]["bodies"],
        ]
        rendered = anneal_scaffold.render_scaffold({"program": {"bodies": bodies}})
        names = anneal_scaffold.LEAN_DECL_NAME_RE.findall(rendered)
        self.assertEqual(len(names), len(set(names)), names)
        self.assertEqual(rendered.count("theorem ok_of_executes "), 1)
        helpers = anneal_scaffold.helper_declared_names()
        slugs = anneal_scaffold.assign_unique_slugs(bodies)
        per_body = {
            f"{prefix}_{slug}"
            for prefix in anneal_scaffold.PER_BODY_DECL_PREFIXES
            for slug in slugs
        }
        for name in names:
            self.assertTrue(
                name in helpers or name in per_body or name == "all_bodies_safe", name
            )

    def test_symlink_checks_stop_at_root_and_ignore_host_prefixes(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp).resolve(strict=True)
            real = base / "real"
            (real / "sub").mkdir(parents=True)
            (real / "sub/x.rs").write_text("", encoding="utf-8")
            alias = base / "alias"
            alias.symlink_to(real)
            ensure = anneal_scaffold.ensure_regular_nonsymlink
            err = anneal_scaffold.ScaffoldError

            # Without a root, only the leaf is checked (like macOS `/var`).
            ensure(alias / "sub/x.rs", "leaf")
            with self.assertRaisesRegex(err, "must not be a symlink"):
                ensure(alias, "leaf")
            # The root itself and anything above it are trusted.
            ensure(alias / "sub/x.rs", "confined", root=alias)
            # Symlinks strictly below the root are rejected.
            (real / "sub_link").symlink_to(real / "sub")
            with self.assertRaisesRegex(err, "must not traverse a symlink"):
                ensure(real / "sub_link/x.rs", "confined", root=real)
            with self.assertRaisesRegex(err, "escapes"):
                ensure(base / "other.rs", "confined", root=real)

            # End to end: a unit reached through a symlinked host prefix works,
            # while a source file reached through an in-root symlink does not.
            src_dir = real / "src"
            (src_dir / "inner").mkdir(parents=True)
            (src_dir / "lib.rs").write_text("#![no_std]\n", encoding="utf-8")
            (src_dir / "inner/a.rs").write_text("", encoding="utf-8")
            (src_dir / "inner_link").symlink_to(src_dir / "inner")
            unit_dir = real / "proofs/u01"
            unit_dir.mkdir(parents=True)
            fake_sys = real / "sysroot"
            fake_sys.mkdir()
            fake_cap = real / "fake_capture.py"
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                "import pathlib, sys\n"
                "out_dir = pathlib.Path(\n"
                "    next(a.split('=', 1)[1] for a in sys.argv if a.startswith('--out-dir='))\n"
                ")\n"
                "out_dir.mkdir(parents=True, exist_ok=True)\n"
                f"(out_dir / 'capture.json').write_text({json.dumps(sample_isize_capture())!r})\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)
            req = {
                "compilation": {
                    "source_root": "../../src",
                    "crate_root": "lib.rs",
                    "crate_name": "demo",
                    "source_files": ["lib.rs", "inner/a.rs"],
                },
                "scope": {"kind": "selected_unit", "roots": ["demo_fn"]},
            }
            (unit_dir / "request.json").write_text(json.dumps(req), encoding="utf-8")
            alias_req = alias / "proofs/u01/request.json"
            self.assertEqual(
                anneal_scaffold.main([
                    "--request", str(alias_req),
                    "--capture", str(alias / "fake_capture.py"),
                    "--sysroot", str(alias / "sysroot"),
                ]),
                0,
            )
            req["compilation"]["source_files"] = ["lib.rs", "inner_link/a.rs"]
            (unit_dir / "request.json").write_text(json.dumps(req), encoding="utf-8")
            with self.assertRaisesRegex(err, "must not traverse a symlink"):
                anneal_scaffold.capture_from_request(
                    alias_req, capture=fake_cap, sysroot=fake_sys
                )

    def test_capture_from_request_rejects_malformed_request_fields(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve(strict=True)
            src_dir = root / "src"
            src_dir.mkdir()
            (src_dir / "lib.rs").write_text("#![no_std]\n", encoding="utf-8")
            unit_dir = root / "proofs/u01"
            unit_dir.mkdir(parents=True)
            fake_sys = root / "sysroot"
            fake_sys.mkdir()
            ran = root / "ran"
            fake_cap = root / "fake_capture.py"
            fake_cap.write_text(
                "#!/usr/bin/env python3\n"
                f"open({str(ran)!r}, 'w').close()\n"
                "raise SystemExit(1)\n",
                encoding="utf-8",
            )
            fake_cap.chmod(0o755)

            def request(**overrides):
                comp = {
                    "source_root": "../../src",
                    "crate_root": "lib.rs",
                    "crate_name": "demo",
                    "source_files": ["lib.rs"],
                }
                scope = {"kind": "selected_unit", "roots": ["demo_fn"]}
                for key, val in overrides.items():
                    table, _, field = key.partition("__")
                    (comp if table == "comp" else scope)[field] = val
                return {"compilation": comp, "scope": scope}

            req_path = unit_dir / "request.json"
            cases = {
                "absolute source_root": (
                    request(comp__source_root=str(src_dir)), "relative path"
                ),
                "empty source_root": (request(comp__source_root=""), "relative path"),
                "cfg string": (request(comp__cfg="feature"), "cfg must be a list"),
                "cfg non-str item": (request(comp__cfg=[1]), "cfg must be a list"),
                "env list": (request(comp__env=["A=1"]), "env must map"),
                "env non-str value": (request(comp__env={"A": 1}), "env must map"),
                "roots string": (request(scope__roots="demo_fn"), "roots must be a list"),
                "instantiations of str": (
                    request(scope__instantiations=["demo_fn"]),
                    "instantiations must be a list",
                ),
                "crate_type non-str": (request(comp__crate_type=["lib"]), "crate_type"),
            }
            for label, (req, pattern) in cases.items():
                with self.subTest(case=label):
                    req_path.write_text(json.dumps(req), encoding="utf-8")
                    with self.assertRaisesRegex(anneal_scaffold.ScaffoldError, pattern):
                        anneal_scaffold.capture_from_request(
                            req_path, capture=fake_cap, sysroot=fake_sys
                        )
                    self.assertFalse(ran.exists(), "capture must not run")


if __name__ == "__main__":
    unittest.main()
