from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "reference.py"
SPEC = importlib.util.spec_from_file_location("reference_tool", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
reference = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = reference
SPEC.loader.exec_module(reference)


def valid_metadata(**overrides):
    data = {
        "topics": ["lean", "lean/elaboration"],
        "subjects": [
            {
                "name": "Lean 4",
                "identity": {
                    "repository": "leanprover/lean4",
                    "revision": "0123456789abcdef0123456789abcdef01234567",
                    "version": "v4.30.0-rc2",
                },
            }
        ],
        "observed_at": "2026-09-24",
    }
    data.update(overrides)
    return data


def make_root(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    root.mkdir(parents=True)
    for name in ("AGENTS.md", "FORMAT.md", "README.md"):
        (root / name).write_text(f"# {name}\n", encoding="utf-8")
    (root / "CATALOG.json").write_text(reference.generate_catalog(root, []), encoding="utf-8")
    return root


def add_report(root: Path, name="example", metadata=None, prose="# Example\n") -> Path:
    package = root / "reports" / name
    package.mkdir(parents=True)
    (package / "REPORT.json").write_text(
        json.dumps(valid_metadata() if metadata is None else metadata, indent=2),
        encoding="utf-8",
    )
    (package / "REPORT.md").write_text(prose, encoding="utf-8")
    return package


def refresh_catalog(root: Path) -> None:
    reports, problems = reference.load_reports(root)
    if problems:
        raise AssertionError([problem.message for problem in problems])
    (root / "CATALOG.json").write_text(reference.generate_catalog(root, reports), encoding="utf-8")


def messages(problems):
    return [problem.message for problem in problems]


class ReferenceToolTests(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp_path = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def test_empty_corpus_is_valid(self):
        root = make_root(self.tmp_path)
        self.assertEqual(reference.check(root), [])

    def test_valid_report_and_catalog(self):
        root = make_root(self.tmp_path)
        add_report(root)
        refresh_catalog(root)
        self.assertEqual(reference.check(root), [])

    def test_report_markdown_is_not_semantically_parsed_but_must_be_utf8(self):
        root = make_root(self.tmp_path)
        package = add_report(root, prose="--> not a structured report\n")
        refresh_catalog(root)
        self.assertEqual(reference.check(root), [])
        (package / "REPORT.md").write_bytes(b"\xff")
        self.assertTrue(any("not valid UTF-8" in p.message for p in reference.check(root)))

    def test_duplicate_json_keys_are_rejected(self):
        root = make_root(self.tmp_path)
        package = root / "reports" / "duplicate"
        package.mkdir(parents=True)
        (package / "REPORT.json").write_text(
            '{"topics":["a"],"topics":["b"],"subjects":[],"observed_at":"2026-09-24"}',
            encoding="utf-8",
        )
        (package / "REPORT.md").write_text("# Example\n", encoding="utf-8")
        _, problems = reference.load_reports(root)
        self.assertTrue(any("duplicate object key" in p.message for p in problems))

    def test_nonstandard_json_constants_are_rejected(self):
        root = make_root(self.tmp_path)
        package = root / "reports" / "constant"
        package.mkdir(parents=True)
        (package / "REPORT.json").write_text(
            '{"topics":["a"],"subjects":[],"observed_at":NaN}',
            encoding="utf-8",
        )
        (package / "REPORT.md").write_text("# Example\n", encoding="utf-8")
        _, problems = reference.load_reports(root)
        self.assertTrue(any("invalid JSON constant" in p.message for p in problems))

    def test_lone_unicode_surrogate_is_rejected_at_json_boundary(self):
        root = make_root(self.tmp_path)
        package = root / "reports" / "surrogate"
        package.mkdir(parents=True)
        (package / "REPORT.json").write_text(
            r'{"topics":["a"],"subjects":[{"name":"\ud800","identity":{"x":"y"}}],"observed_at":"2026-09-24"}',
            encoding="utf-8",
        )
        (package / "REPORT.md").write_text("# Example\n", encoding="utf-8")
        _, problems = reference.load_reports(root)
        self.assertTrue(any("Unicode scalar" in p.message for p in problems))

    def test_metadata_validation(self):
        cases = [
            ({"subjects": valid_metadata()["subjects"], "observed_at": "2026-09-24"}, "missing metadata keys"),
            (valid_metadata(extra="x"), "unknown metadata keys"),
            (valid_metadata(topics=[]), "'topics' must be a non-empty array"),
            (valid_metadata(topics=["Lean/Bad"]), "lowercase slash-separated"),
            (valid_metadata(topics=["lean", "lean"]), "duplicate topic"),
            (valid_metadata(subjects=[]), "'subjects' must be a non-empty array"),
            (
                valid_metadata(
                    subjects=[
                        {"name": "X", "identity": {"revision": "a"}},
                        {"name": "X", "identity": {"revision": "b"}},
                    ]
                ),
                "duplicate subject name",
            ),
            (
                valid_metadata(subjects=[{"name": "X", "identity": {}}]),
                "identity must be a non-empty object",
            ),
            (
                valid_metadata(subjects=[{"name": "X", "identity": {"revision": ""}}]),
                "must be a non-empty string",
            ),
            (valid_metadata(observed_at="2026-02-30"), "valid YYYY-MM-DD"),
        ]
        for idx, (metadata, needle) in enumerate(cases):
            with self.subTest(needle=needle):
                root = make_root(self.tmp_path / str(idx))
                add_report(root, metadata=metadata)
                _, problems = reference.load_reports(root)
                self.assertTrue(any(needle in message for message in messages(problems)))

    def test_subject_unknown_key_is_rejected(self):
        root = make_root(self.tmp_path)
        metadata = valid_metadata(
            subjects=[{"name": "X", "identity": {"revision": "abc"}, "role": "tool"}]
        )
        add_report(root, metadata=metadata)
        _, problems = reference.load_reports(root)
        self.assertTrue(any("unknown keys" in p.message for p in problems))

    def test_immediate_children_of_reports_are_packages(self):
        root = make_root(self.tmp_path)
        stray = root / "reports" / "stray.txt"
        stray.parent.mkdir(parents=True)
        stray.write_text("x", encoding="utf-8")
        problems = reference.check(root)
        self.assertTrue(any("must be report directories" in p.message for p in problems))

    def test_package_names_are_simple_slugs(self):
        root = make_root(self.tmp_path)
        bad = root / "reports" / "Lean.Bad"
        bad.mkdir(parents=True)
        problems = reference.check(root)
        self.assertTrue(any("lowercase ASCII words" in p.message for p in problems))

    def test_package_requires_root_report_files(self):
        root = make_root(self.tmp_path)
        package = root / "reports" / "missing"
        package.mkdir(parents=True)
        problems = reference.check(root)
        rendered = messages(problems)
        self.assertTrue(any("REPORT.json" in p.message for p in problems))
        self.assertTrue(any("REPORT.md" in p.message for p in problems))

    def test_arbitrary_nested_support_files_are_allowed_including_report_names(self):
        root = make_root(self.tmp_path)
        package = add_report(root)
        nested = package / "fixtures" / "nested"
        nested.mkdir(parents=True)
        (nested / "REPORT.json").write_text("not metadata", encoding="utf-8")
        (nested / "REPORT.md").write_text("not report prose", encoding="utf-8")
        (package / "schema.json").write_text("{}", encoding="utf-8")
        refresh_catalog(root)
        self.assertEqual(reference.check(root), [])

    def test_symlinks_are_rejected_anywhere_under_reports(self):
        root = make_root(self.tmp_path)
        package = add_report(root)
        target = package / "target.txt"
        target.write_text("x", encoding="utf-8")
        link = package / "link.txt"
        try:
            link.symlink_to(target.name)
        except OSError as exc:
            self.skipTest(f"symlinks unavailable: {exc}")
        self.assertTrue(any("symlinks are not allowed" in p.message for p in reference.check(root)))

    def test_reports_symlink_is_rejected_even_if_dangling(self):
        root = make_root(self.tmp_path)
        reports = root / "reports"
        try:
            reports.symlink_to(root / "missing", target_is_directory=True)
        except OSError as exc:
            self.skipTest(f"symlinks unavailable: {exc}")
        self.assertTrue(any("reports must not be a symlink" in p.message for p in reference.check(root)))

    def test_required_root_file_symlink_is_rejected(self):
        root = make_root(self.tmp_path)
        target = root / "real-readme.md"
        target.write_text("# real\n", encoding="utf-8")
        (root / "README.md").unlink()
        try:
            (root / "README.md").symlink_to(target.name)
        except OSError as exc:
            self.skipTest(f"symlinks unavailable: {exc}")
        self.assertTrue(any("required root files must not be symlinks" in p.message for p in reference.check(root)))

    def test_traversal_error_fails_closed(self):
        root = make_root(self.tmp_path)
        package = add_report(root)
        original = os.scandir

        def failing(path):
            if Path(path) == package:
                raise PermissionError("denied")
            return original(path)

        with mock.patch.object(reference.os, "scandir", side_effect=failing):
            problems = reference.check(root)
        self.assertTrue(any("cannot enumerate report package" in p.message for p in problems))

    def test_catalog_is_deterministic_and_maps_package_to_metadata(self):
        root = make_root(self.tmp_path)
        add_report(root, "z", metadata=valid_metadata(topics=["zeta"]))
        add_report(root, "a", metadata=valid_metadata(topics=["alpha"]))
        reports, problems = reference.load_reports(root)
        self.assertEqual(problems, [])
        first = reference.generate_catalog(root, list(reversed(reports)))
        second = reference.generate_catalog(root, reports)
        self.assertEqual(first, second)
        parsed = json.loads(first)
        self.assertEqual(list(parsed["reports"]), ["a", "z"])
        self.assertEqual(parsed["reports"]["a"], valid_metadata(topics=["alpha"]))

    def test_catalog_uses_ascii_safe_canonical_json(self):
        root = make_root(self.tmp_path)
        add_report(
            root,
            metadata=valid_metadata(
                subjects=[{"name": "Léan", "identity": {"revision": "α"}}]
            ),
        )
        reports, problems = reference.load_reports(root)
        self.assertEqual(problems, [])
        catalog = reference.generate_catalog(root, reports)
        catalog.encode("ascii")
        self.assertIn(r"\u00e9", catalog)
        self.assertIn(r"\u03b1", catalog)

    def test_stale_catalog_is_reported(self):
        root = make_root(self.tmp_path)
        add_report(root)
        self.assertTrue(any("generated catalog is stale" in p.message for p in reference.check(root)))

    def test_catalog_command_writes_atomically_and_then_checks(self):
        root = make_root(self.tmp_path)
        add_report(root)
        with mock.patch.object(reference.os, "replace", wraps=os.replace) as replace:
            result = reference.main(["--root", str(root), "catalog"])
        self.assertEqual(result, 0)
        self.assertEqual(replace.call_count, 1)
        self.assertEqual(reference.check(root), [])
        leftovers = list(root.glob(".CATALOG.json.*"))
        self.assertEqual(leftovers, [])

    def test_catalog_command_refuses_invalid_report_without_rewriting_catalog(self):
        root = make_root(self.tmp_path)
        original = (root / "CATALOG.json").read_text(encoding="utf-8")
        package = root / "reports" / "bad"
        package.mkdir(parents=True)
        (package / "REPORT.json").write_text("not json", encoding="utf-8")
        (package / "REPORT.md").write_text("# bad\n", encoding="utf-8")
        result = reference.main(["--root", str(root), "catalog"])
        self.assertEqual(result, 1)
        self.assertEqual((root / "CATALOG.json").read_text(encoding="utf-8"), original)

    def test_check_cli_exit_statuses(self):
        root = make_root(self.tmp_path)
        ok = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(root), "check"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(ok.returncode, 0)
        self.assertIn("reference check passed", ok.stdout)

        (root / "README.md").unlink()
        bad = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(root), "check"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(bad.returncode, 1)
        self.assertIn("required root file README.md is missing", bad.stderr)


if __name__ == "__main__":
    unittest.main()
