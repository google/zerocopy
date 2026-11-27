# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`verify_anneal_spec_zerocopy.py` tests for spec unit discovery,
`spec_sources.json` lowering, and mutated negatives."""

from .support import (
    json,
    make_fixture,
    mock,
    os,
    Path,
    set_source_files,
    SimpleNamespace,
    subprocess,
    tempfile,
    verify_anneal_spec_zerocopy,
    write_spec_sources,
)


class UnitsAndSourcesCases:
    """`VerifyAnnealSpecZerocopyTests` methods for spec unit discovery,
    `spec_sources.json` lowering, and mutated negatives."""

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

    def test_spec_sources_unit_lowers_crate_files_from_crate_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec_root, proofs_dir, src_dir, unit = make_fixture(root)
            (src_dir / "util").mkdir()
            (src_dir / "util/macros.rs").write_text("", encoding="utf-8")
            (unit / "spec.rs").unlink()
            write_spec_sources(unit, ["lib.rs", "util/macros.rs"])
            set_source_files(unit, ["lib.rs", "util/macros.rs", "other.rs"])

            found = verify_anneal_spec_zerocopy.discover_spec_units(
                proofs_dir, src_dir
            )
            self.assertEqual([u.name for u, _ in found], [unit.name])

            args = SimpleNamespace(
                src_root=spec_root, src_dir=src_dir, lower=root / "lower",
                timeout=30,
            )
            calls = []

            def fake_run(cmd, **_kwargs):
                calls.append(cmd)
                return subprocess.CompletedProcess(cmd, 0, "", "")

            with mock.patch(
                "verify_anneal_spec_zerocopy.subprocess.run",
                side_effect=fake_run,
            ):
                verify_anneal_spec_zerocopy.check_freshness(
                    args, unit, found[0][1]
                )
            self.assertEqual(
                calls,
                [[
                    str(root / "lower"), "--src-root",
                    str(src_dir.resolve()), "--check", str(unit),
                    "lib.rs", "util/macros.rs",
                ]],
            )

            # A companion `spec.rs` unit still lowers from the workspace root.
            calls.clear()
            (unit / "spec_sources.json").unlink()
            (unit / "spec.rs").write_text("", encoding="utf-8")
            with mock.patch(
                "verify_anneal_spec_zerocopy.subprocess.run",
                side_effect=fake_run,
            ):
                verify_anneal_spec_zerocopy.check_freshness(
                    args, unit, found[0][1]
                )
            self.assertEqual(calls[0][2], str(spec_root))
            self.assertEqual(
                calls[0][-1], os.path.relpath(unit / "spec.rs", spec_root)
            )

    def test_spec_sources_rejects_ambiguous_or_escaping_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _, proofs_dir, src_dir, unit = make_fixture(root)
            (src_dir / "util").mkdir()
            (src_dir / "util/macros.rs").write_text("", encoding="utf-8")
            (root / "outside.rs").write_text("", encoding="utf-8")
            (src_dir / "linked.rs").symlink_to(root / "outside.rs")
            (src_dir / "dirlink").symlink_to(src_dir / "util")
            set_source_files(
                unit,
                [
                    "lib.rs", "util/macros.rs", "linked.rs", "gone.rs",
                    "dirlink/macros.rs", "-h.rs",
                ],
            )

            def discover():
                return verify_anneal_spec_zerocopy.discover_spec_units(
                    proofs_dir, src_dir
                )

            # Both inputs, then neither.
            write_spec_sources(unit, ["lib.rs"])
            with self.assertRaisesRegex(RuntimeError, "exactly one of"):
                discover()
            (unit / "spec.rs").unlink()
            (unit / "spec_sources.json").unlink()
            with self.assertRaisesRegex(RuntimeError, "exactly one of"):
                discover()

            for files, pattern in (
                ([], "must be"),
                ("lib.rs", "must be"),
                (["../outside.rs"], "invalid spec source"),
                (["/abs/lib.rs"], "invalid spec source"),
                (["./lib.rs"], "invalid spec source"),
                (["util//macros.rs"], "invalid spec source"),
                (["util\\macros.rs"], "invalid spec source"),
                (["lib.txt"], "invalid spec source"),
                (["-h.rs"], "invalid spec source"),
                ([7], "invalid spec source"),
                (["dirlink/macros.rs"], "not a regular file"),
                (["lib.rs", "lib.rs"], "duplicate spec source"),
                (["missing.rs"], "not in compilation.source_files"),
                (["gone.rs"], "not a regular file"),
                (["linked.rs"], "not a regular file"),
            ):
                with self.subTest(files=files):
                    write_spec_sources(unit, files)
                    with self.assertRaisesRegex(RuntimeError, pattern):
                        discover()

            (unit / "spec_sources.json").write_text(
                '{"files": ["lib.rs"], "extra": 1}', encoding="utf-8"
            )
            with self.assertRaisesRegex(RuntimeError, "must be"):
                discover()
            (unit / "spec_sources.json").write_text(
                '{"files": ["lib.rs"], "files": ["util/macros.rs"]}',
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                discover()

            (unit / "spec_sources.json").unlink()
            (unit / "spec_sources.json").symlink_to(root / "outside.rs")
            with self.assertRaisesRegex(RuntimeError, "symlink disallowed"):
                discover()
            # `load_spec_sources` refuses it on its own too.
            request = json.loads(
                (unit / "request.json").read_text(encoding="utf-8")
            )
            with self.assertRaisesRegex(RuntimeError, "regular file"):
                verify_anneal_spec_zerocopy.load_spec_sources(
                    unit, request, src_dir.resolve()
                )
            (unit / "spec_sources.json").unlink()

            write_spec_sources(unit, ["lib.rs"])
            set_source_files(unit, None)
            with self.assertRaisesRegex(
                RuntimeError, "requires compilation.source_files"
            ):
                discover()

    def test_mutated_spec_negative_supports_inline_base_units(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            spec_root, _, src_dir, unit = make_fixture(root)
            (src_dir / "lib.rs").write_text(
                "#[cfg_attr(anneal, anneal::spec(total, "
                "ensures(|count| count == 0)))]\nfn to_elem_count() {}\n",
                encoding="utf-8",
            )
            (unit / "spec.rs").unlink()
            write_spec_sources(unit, ["lib.rs"])
            set_source_files(unit, ["lib.rs"])
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
                "verify_anneal_spec_zerocopy.subprocess.run",
                side_effect=fake_run,
            ):
                results = verify_anneal_spec_zerocopy.run_negative_controls(
                    args, unit, work
                )
            self.assertEqual(
                {k: v["status"] for k, v in results.items()},
                {"mutated_spec_rs": "proof_failed",
                 "mismatched_signature": "proof_failed"},
            )
            neg_dir = work / "neg-mutated_spec_rs"
            neg_src = work / "neg-mutated_spec_rs-src"
            self.assertEqual(
                lower_cmds,
                [[str(args.lower), "--src-root", str(neg_src), "--out-dir",
                  str(neg_dir), "lib.rs"]],
            )
            self.assertIn(
                "count == 1", (neg_src / "lib.rs").read_text(encoding="utf-8")
            )
            self.assertIn(
                "count == 0", (src_dir / "lib.rs").read_text(encoding="utf-8")
            )
            req = json.loads(
                (neg_dir / "request.json").read_text(encoding="utf-8")
            )
            self.assertEqual(
                (neg_dir / req["compilation"]["source_root"]).resolve(),
                neg_src.resolve(),
            )

            # The needle must appear exactly once across the named sources:
            # not zero times, not twice in one file, and not once in each of
            # two files or once in one and twice in another.
            needle = "ensures(|count| count == 0)\n"
            (src_dir / "util").mkdir()
            write_spec_sources(unit, ["lib.rs", "util/m.rs"])
            set_source_files(unit, ["lib.rs", "util/m.rs"])
            for n, (lib, m) in enumerate(((0, 0), (2, 0), (1, 1), (1, 2))):
                with self.subTest(lib=lib, m=m):
                    (src_dir / "lib.rs").write_text(needle * lib,
                                                    encoding="utf-8")
                    (src_dir / "util/m.rs").write_text(needle * m,
                                                       encoding="utf-8")
                    work_n = root / f"work-dup-{n}"
                    work_n.mkdir()
                    with mock.patch(
                        "verify_anneal_spec_zerocopy.subprocess.run",
                        side_effect=fake_run,
                    ):
                        with self.assertRaisesRegex(
                            RuntimeError, "failed to mutate the negative-control"
                        ):
                            verify_anneal_spec_zerocopy.run_negative_controls(
                                args, unit, work_n
                            )
