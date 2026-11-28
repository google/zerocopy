# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`verify_anneal_spec_zerocopy.py` tests for claim-bound crate units and their
negative controls."""

from .support import (
    io,
    json,
    list_targets_output,
    make_fixture,
    make_trusted_tree,
    mock,
    Path,
    redirect_stdout,
    shutil,
    SimpleNamespace,
    subprocess,
    tempfile,
    verify_anneal_spec_zerocopy,
)


class ClaimBoundUnitsCases:
    """`VerifyAnnealSpecZerocopyTests` methods for claim-bound crate units and
    their negative controls."""

    def test_claim_bound_crate_units(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec_root, proofs_dir, src_dir, unit = make_fixture(root)
            zc_proofs = root / "zerocopy/proofs"
            crate_unit = zc_proofs / "01_zc"
            (crate_unit / "Specs/zerocopy").mkdir(parents=True)
            (crate_unit / "Specs/zerocopy/zc01.lean").write_text("", encoding="utf-8")
            (crate_unit / "spec_sources.json").write_text(
                '{"files": ["lib.rs"], "claim": "zc01"}', encoding="utf-8"
            )
            request = {
                "compilation": {"crate_name": "zerocopy", "source_files": ["lib.rs"]},
                "proof": {
                    "specification": "Specs.zerocopy.zc01.specs",
                    "sources": [
                        {"module": "Specs.zerocopy.zc01",
                         "path": "Specs/zerocopy/zc01.lean", "role": "specification"},
                        {"module": "Proof", "path": "Proof.lean", "role": "proof"},
                    ],
                },
            }

            def write_request(req):
                (crate_unit / "request.json").write_text(json.dumps(req), encoding="utf-8")

            write_request(request)
            # Hand-written units without `spec_sources.json` are skipped.
            (zc_proofs / "02_hand").mkdir()
            found = verify_anneal_spec_zerocopy.discover_crate_units(zc_proofs, src_dir)
            self.assertEqual(
                [(u.name, f, c, k) for u, _, f, c, k in found],
                [("01_zc", ["lib.rs"], "zc01", "zerocopy")],
            )

            for mutate, pattern in (
                (lambda r: r["proof"].update(specification="Spec.specs"), "must have exactly"),
                (lambda r: r["proof"]["sources"][0].update(path="Spec.lean"), "must have exactly"),
                (lambda r: r["compilation"].update(crate_name="zero-copy"), "crate_name"),
            ):
                bad = json.loads(json.dumps(request))
                mutate(bad)
                write_request(bad)
                with self.subTest(pattern=pattern):
                    with self.assertRaisesRegex(RuntimeError, pattern):
                        verify_anneal_spec_zerocopy.discover_crate_units(zc_proofs, src_dir)
            write_request(request)
            (crate_unit / "spec_sources.json").write_text(
                '{"files": ["lib.rs"]}', encoding="utf-8"
            )
            with self.assertRaisesRegex(RuntimeError, "must bind a claim"):
                verify_anneal_spec_zerocopy.discover_crate_units(zc_proofs, src_dir)
            (crate_unit / "spec_sources.json").write_text(
                '{"files": ["lib.rs"], "claim": "1bad"}', encoding="utf-8"
            )
            with self.assertRaisesRegex(RuntimeError, "optional"):
                verify_anneal_spec_zerocopy.discover_crate_units(zc_proofs, src_dir)
            (crate_unit / "spec_sources.json").write_text(
                '{"files": ["lib.rs"], "claim": "zc01"}', encoding="utf-8"
            )
            found = verify_anneal_spec_zerocopy.discover_crate_units(zc_proofs, src_dir)

            # A second unit may share `lib.rs` under another claim, but not
            # bind the same claim, even on other files.
            other = zc_proofs / "03_zc"
            shutil.copytree(crate_unit, other)
            moved = json.loads(json.dumps(request).replace("zc01", "zc03"))
            (other / "request.json").write_text(json.dumps(moved), encoding="utf-8")
            (other / "spec_sources.json").write_text(
                '{"files": ["lib.rs"], "claim": "zc03"}', encoding="utf-8"
            )
            self.assertEqual(
                [c for _, _, _, c, _ in verify_anneal_spec_zerocopy.discover_crate_units(
                    zc_proofs, src_dir)],
                ["zc01", "zc03"],
            )
            (other / "request.json").write_text(json.dumps(request), encoding="utf-8")
            (other / "spec_sources.json").write_text(
                '{"files": ["lib.rs"], "claim": "zc01"}', encoding="utf-8"
            )
            with self.assertRaisesRegex(RuntimeError, "already bound by 01_zc"):
                verify_anneal_spec_zerocopy.discover_crate_units(zc_proofs, src_dir)
            shutil.rmtree(other)
            (zc_proofs / "04_link").symlink_to(crate_unit)
            with self.assertRaisesRegex(RuntimeError, "symlink disallowed"):
                verify_anneal_spec_zerocopy.discover_crate_units(zc_proofs, src_dir)
            (zc_proofs / "04_link").unlink()

            args = SimpleNamespace(
                src_root=spec_root, src_dir=src_dir, lower=root / "lower", timeout=30,
            )
            calls = []

            def fake_run(cmd, **_kwargs):
                calls.append(cmd)
                return subprocess.CompletedProcess(cmd, 0, "", "")

            with mock.patch(
                "verify_anneal_spec_zerocopy.subprocess.run", side_effect=fake_run
            ):
                verify_anneal_spec_zerocopy.check_crate_unit_freshness(
                    args, crate_unit, ["lib.rs"], "zc01", "zerocopy"
                )
            self.assertEqual(
                calls[0],
                [str(args.lower), "--src-root", str(src_dir.resolve()),
                 "--format", "v2-module", "--crate-slug", "zerocopy",
                 "--claim", "zc01", "--check", str(crate_unit), "lib.rs"],
            )

            # Uniqueness: a crate unit owns the items of its claim in its files.
            listing = []

            def listing_run(cmd, **_kwargs):
                if cmd[cmd.index("--list-targets") + 1:] == ["lib.rs"]:
                    return subprocess.CompletedProcess(cmd, 0, json.dumps(listing), "")
                return subprocess.CompletedProcess(cmd, 0, "[]", "")

            def uniqueness(crate_units):
                units = verify_anneal_spec_zerocopy.discover_spec_units(proofs_dir, src_dir)
                with mock.patch(
                    "verify_anneal_spec_zerocopy.subprocess.run", side_effect=listing_run
                ):
                    return verify_anneal_spec_zerocopy.check_contract_uniqueness(
                        args, units, crate_units
                    )

            def item(target, claim):
                return {"target": target, "claim": claim, "file": "lib.rs", "kind": "inline"}

            listing[:] = [item("a", "zc01"), item("b", "zc01")]
            self.assertEqual(
                uniqueness(found),
                {"crate_targets": 2, "companion_targets": 0, "crate_units": 1},
            )
            listing.append(item("c", "other"))
            with self.assertRaisesRegex(RuntimeError, r"`c` .*not none"):
                uniqueness(found)
            listing.pop()
            with self.assertRaisesRegex(RuntimeError, r"not \['01_zc', '01_zc'\]"):
                uniqueness(found + found)
            # An `anneal-spec` unit lowering the same file claims it too.
            (unit / "spec.rs").unlink()
            (unit / "spec_sources.json").write_text('{"files": ["lib.rs"]}', encoding="utf-8")
            req = json.loads((unit / "request.json").read_text(encoding="utf-8"))
            req["compilation"]["source_files"] = ["lib.rs"]
            (unit / "request.json").write_text(json.dumps(req), encoding="utf-8")
            with self.assertRaisesRegex(
                RuntimeError, r"not \['01_zc', '02_unit_pointer_metadata'\]"
            ):
                uniqueness(found)
            # ...and may not bind a claim itself.
            (unit / "spec_sources.json").write_text(
                '{"files": ["lib.rs"], "claim": "zc01"}', encoding="utf-8"
            )
            with self.assertRaisesRegex(RuntimeError, "belong in zerocopy/proofs"):
                verify_anneal_spec_zerocopy.discover_spec_units(proofs_dir, src_dir)

    def test_negative_controls_support_claim_bound_crate_units(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec_root, proofs_dir, src_dir, _ = make_fixture(root)
            # `anneal-spec`'s own unit directory may be absent.
            shutil.rmtree(proofs_dir)
            self.assertEqual(
                verify_anneal_spec_zerocopy.discover_spec_units(proofs_dir, src_dir), []
            )
            (src_dir / "lib.rs").write_text(
                '#[cfg_attr(anneal, anneal::spec(claim = "zc02", total, '
                "ensures(|count| count == 0)))]\nfn to_elem_count() {}\n",
                encoding="utf-8",
            )
            unit = root / "zerocopy/proofs/02_unit_pointer_metadata"
            (unit / "Specs/zerocopy").mkdir(parents=True)
            (unit / "Specs/zerocopy/zc02.lean").write_text(
                "signature := some { isUnsafe := false, params := [.unit], "
                "ret := .int .isize false }\n",
                encoding="utf-8",
            )
            (unit / "spec_sources.json").write_text(
                '{"files": ["lib.rs"], "claim": "zc02"}', encoding="utf-8"
            )
            (unit / "request.json").write_text(json.dumps({
                "compilation": {"crate_name": "zerocopy", "source_root": "../../src",
                                "source_files": ["lib.rs"]},
                "proof": {
                    "specification": "Specs.zerocopy.zc02.specs",
                    "sources": [
                        {"module": "Specs.zerocopy.zc02",
                         "path": "Specs/zerocopy/zc02.lean", "role": "specification"},
                        {"module": "Proof", "path": "Proof.lean", "role": "proof"},
                    ],
                },
            }), encoding="utf-8")
            work = root / "work"
            work.mkdir()
            args = SimpleNamespace(
                src_root=spec_root, src_dir=src_dir, lower=root / "lower",
                cli=root / "cargo-anneal", capture=root / "capture",
                sysroot=root / "sysroot", lean=root / "lean", timeout=30,
            )
            lower_cmds = []

            def fake_run(cmd, **_kwargs):
                if cmd[0] == str(args.lower):
                    lower_cmds.append(cmd)
                    return subprocess.CompletedProcess(cmd, 0, "", "")
                return subprocess.CompletedProcess(
                    cmd, 1, json.dumps({"status": "proof_failed"}), ""
                )

            with mock.patch(
                "verify_anneal_spec_zerocopy.subprocess.run", side_effect=fake_run
            ):
                results = verify_anneal_spec_zerocopy.run_negative_controls(
                    args, unit, work
                )
            self.assertEqual(
                {k: v["status"] for k, v in results.items()},
                {"mutated_spec_rs": "proof_failed", "mismatched_signature": "proof_failed"},
            )
            neg = work / "neg-mutated_spec_rs"
            self.assertEqual(
                lower_cmds,
                [[str(args.lower), "--src-root", str(work / "neg-mutated_spec_rs-src"),
                  "--format", "v2-module", "--crate-slug", "zerocopy", "--claim", "zc02",
                  "--out-dir", str(neg), "lib.rs"]],
            )
            self.assertIn(
                "count == 1",
                (work / "neg-mutated_spec_rs-src/lib.rs").read_text(encoding="utf-8"),
            )
            # The signature mutation edits the generated module.
            self.assertIn(
                ".int .i32 false",
                (work / "neg-mismatched_signature/Specs/zerocopy/zc02.lean").read_text(
                    encoding="utf-8"
                ),
            )

            # The whole suite runs without `anneal-spec` units, with the
            # negatives on the claim-bound unit.
            suite_args = SimpleNamespace(
                **vars(args), proofs_dir=proofs_dir,
                zerocopy_proofs_dir=root / "zerocopy/proofs",
                trusted_lean=make_trusted_tree(root), jobs=1,
            )

            def suite_run(cmd, **_kwargs):
                if "--list-targets" in cmd:
                    return subprocess.CompletedProcess(cmd, 0, list_targets_output(cmd), "")
                if cmd[0] == str(args.lower) or cmd[0] == str(args.lean):
                    return subprocess.CompletedProcess(cmd, 0, "", "")
                return subprocess.CompletedProcess(
                    cmd, 1, json.dumps({"status": "proof_failed"}), ""
                )

            suite_work = root / "suite-work"
            suite_work.mkdir()
            with mock.patch(
                "verify_anneal_spec_zerocopy.subprocess.run", side_effect=suite_run
            ):
                with redirect_stdout(io.StringIO()):
                    summary = verify_anneal_spec_zerocopy.run_suite(suite_args, suite_work)
            self.assertEqual(summary["unit_count"], 0)
            self.assertEqual(summary["contract_uniqueness"]["crate_units"], 1)
            self.assertEqual(
                {k: v["status"] for k, v in summary["negatives"].items()},
                {"mutated_spec_rs": "proof_failed", "mismatched_signature": "proof_failed"},
            )

            # A symlinked or dangling `anneal-spec` unit directory fails closed.
            proofs_dir.symlink_to(root / "nowhere")
            with self.assertRaisesRegex(RuntimeError, "invalid anneal-spec proofs"):
                verify_anneal_spec_zerocopy.discover_spec_units(proofs_dir, src_dir)
            (root / "nowhere").mkdir()
            with self.assertRaisesRegex(RuntimeError, "invalid anneal-spec proofs"):
                verify_anneal_spec_zerocopy.discover_spec_units(proofs_dir, src_dir)
