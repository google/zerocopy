# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`verify_anneal_spec_zerocopy.py` tests for `run_suite`, receipt binding, and
contract uniqueness."""

from .support import (
    io,
    json,
    list_targets_output,
    make_fixture,
    make_receipt,
    make_trusted_tree,
    mock,
    os,
    Path,
    redirect_stdout,
    set_source_files,
    shutil,
    SimpleNamespace,
    subprocess,
    tempfile,
    verify_anneal_spec_zerocopy,
    write_spec_sources,
)


class RunSuiteCases:
    """`VerifyAnnealSpecZerocopyTests` methods for `run_suite`, receipt binding,
    and contract uniqueness."""

    def test_run_suite_accepts_clean_and_rejects_passing_negative(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec_root, proofs_dir, src_dir, _ = make_fixture(root)
            trusted = make_trusted_tree(root)
            work = root / "work"
            work.mkdir()
            args = SimpleNamespace(
                proofs_dir=proofs_dir,
                zerocopy_proofs_dir=root / "zerocopy/proofs",
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

            # A claim-bound `zerocopy/proofs` unit is checked for freshness.
            crate_unit = root / "zerocopy/proofs/01_zc"
            crate_unit.mkdir()
            (crate_unit / "spec_sources.json").write_text(
                '{"files": ["lib.rs"], "claim": "zc01"}', encoding="utf-8"
            )
            (crate_unit / "request.json").write_text(json.dumps({
                "compilation": {"crate_name": "zerocopy", "source_files": ["lib.rs"]},
                "proof": {
                    "specification": "Specs.zerocopy.zc01.specs",
                    "sources": [{"module": "Specs.zerocopy.zc01",
                                 "path": "Specs/zerocopy/zc01.lean",
                                 "role": "specification"}],
                },
            }), encoding="utf-8")
            verify_cmds = []
            claim_checks = []

            def fake_run(cmd, **_kwargs):
                if "--list-targets" in cmd:
                    return subprocess.CompletedProcess(cmd, 0, list_targets_output(cmd), "")
                if "--check" in cmd and "--claim" in cmd:
                    claim_checks.append(cmd)
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
            self.assertEqual(
                summary["contract_uniqueness"],
                {"crate_targets": 0, "companion_targets": 0, "crate_units": 1},
            )
            self.assertEqual(
                [cmd[cmd.index("--claim") + 1] for cmd in claim_checks
                 if cmd[cmd.index("--check") + 1] == str(crate_unit)],
                ["zc01"],
            )
            self.assertEqual(summary["lean_compile"]["status"], "compiled")
            self.assertEqual(
                summary["negatives"]["mutated_spec_rs"]["status"], "proof_failed"
            )
            self.assertEqual(
                summary["negatives"]["mismatched_signature"]["status"],
                "proof_failed",
            )

            def broken_neg(cmd, **_kwargs):
                if "--list-targets" in cmd:
                    return subprocess.CompletedProcess(cmd, 0, list_targets_output(cmd), "")
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
                zerocopy_proofs_dir=root / "zerocopy/proofs",
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
                    if "--list-targets" in cmd:
                        return subprocess.CompletedProcess(cmd, 0, list_targets_output(cmd), "")
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

    def test_contract_uniqueness_rejects_duplicates_and_orphans(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec_root, proofs_dir, src_dir, unit = make_fixture(root)
            (src_dir / "layout.rs").write_text("", encoding="utf-8")
            args = SimpleNamespace(
                src_root=spec_root, src_dir=src_dir, lower=root / "lower",
                timeout=30,
            )
            # What `--list-targets` reports for each input file.
            listings = {}
            calls = []

            def fake_run(cmd, **_kwargs):
                calls.append(cmd)
                inputs = cmd[cmd.index("--list-targets") + 1:]
                listed = [e for i in inputs for e in listings.get(i, [])]
                return subprocess.CompletedProcess(cmd, 0, json.dumps(listed), "")

            def check():
                units = verify_anneal_spec_zerocopy.discover_spec_units(
                    proofs_dir, src_dir
                )
                calls.clear()
                with mock.patch(
                    "verify_anneal_spec_zerocopy.subprocess.run",
                    side_effect=fake_run,
                ):
                    return verify_anneal_spec_zerocopy.check_contract_uniqueness(
                        args, units
                    )

            def entry(target, file, kind):
                return {"target": target, "claim": "c", "file": file, "kind": kind}

            spec_rel = os.path.relpath(unit / "spec.rs", spec_root)
            listings[spec_rel] = [entry("a", spec_rel, "external")]
            # Phase 0: only companion specifications, so nothing to claim.
            self.assertEqual(check(), {"crate_targets": 0, "companion_targets": 1, "crate_units": 0})
            self.assertEqual(
                calls[0],
                [str(args.lower), "--src-root", str(src_dir.resolve()),
                 "--list-targets", "layout.rs", "lib.rs"],
            )
            self.assertEqual(calls[1][2:], [str(spec_root), "--list-targets", spec_rel])

            # An inline specification that no unit lowers.
            listings["layout.rs"] = [entry("b", "layout.rs", "inline")]
            with self.assertRaisesRegex(RuntimeError, r"`b` \(zerocopy/src/layout.rs\) "
                                        r"must be lowered by exactly one unit, not none"):
                check()
            # The same item specified inline and in a companion file.
            listings["layout.rs"] = [entry("a", "layout.rs", "inline")]
            with self.assertRaisesRegex(
                RuntimeError, "`a` is specified in both zerocopy/src/layout.rs and "
            ):
                check()
            # Two companion files may specify the same item.
            listings["layout.rs"] = []
            shutil.copytree(unit, proofs_dir / "05_again")
            again = os.path.relpath(proofs_dir / "05_again/spec.rs", spec_root)
            listings[again] = [entry("a", again, "external")]
            self.assertEqual(check(), {"crate_targets": 0, "companion_targets": 2, "crate_units": 0})
            shutil.rmtree(proofs_dir / "05_again")
            listings["layout.rs"] = [entry("a", "layout.rs", "inline")]

            # A unit that lowers the file claims its specifications.
            (unit / "spec.rs").unlink()
            write_spec_sources(unit, ["layout.rs"])
            set_source_files(unit, ["layout.rs", "lib.rs"])
            self.assertEqual(check(), {"crate_targets": 1, "companion_targets": 0, "crate_units": 0})
            # Two units that lower the same file both claim them.
            shutil.copytree(unit, proofs_dir / "03_copy")
            with self.assertRaisesRegex(
                RuntimeError,
                r"not \['02_unit_pointer_metadata', '03_copy'\]",
            ):
                check()

            # Symlinks under the crate sources fail closed rather than being
            # skipped.
            (src_dir / "linked.rs").symlink_to(src_dir / "layout.rs")
            with self.assertRaisesRegex(RuntimeError, "symlink in"):
                check()
            (src_dir / "linked.rs").unlink()

            def failing(cmd, **_kwargs):
                return subprocess.CompletedProcess(cmd, 1, "", "E_ANNEAL_X")

            units = verify_anneal_spec_zerocopy.discover_spec_units(proofs_dir, src_dir)
            with mock.patch(
                "verify_anneal_spec_zerocopy.subprocess.run", side_effect=failing
            ):
                with self.assertRaisesRegex(RuntimeError, "list-targets failed.*E_ANNEAL_X"):
                    verify_anneal_spec_zerocopy.check_contract_uniqueness(args, units)
