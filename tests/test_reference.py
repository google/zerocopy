from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).absolute().parents[1] / "tools" / "reference.py"
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
    root = tmp_path / "candidate"
    root.mkdir(parents=True)
    for name in ("AGENTS.md", "FORMAT.md", "README.md"):
        (root / name).write_text(f"# {name}\n", encoding="utf-8")
    (root / "tools").mkdir()
    (root / "tests").mkdir()
    (root / "tools" / "reference.py").write_bytes(SCRIPT.read_bytes())
    (root / "tests" / "test_reference.py").write_text("# tests\n", encoding="utf-8")
    (root / "CATALOG.json").write_bytes(reference._catalog_bytes([]))
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
    root_entries, problems = reference._root_structure(root)
    if problems:
        raise AssertionError([problem.message for problem in problems])
    reports, problems = reference._load_reports(root, root_entries)
    if problems:
        raise AssertionError([problem.message for problem in problems])
    (root / "CATALOG.json").write_bytes(reference._catalog_bytes(reports))


class ReferenceToolTests(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp_path = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def test_empty_candidate_is_valid(self):
        root = make_root(self.tmp_path)
        self.assertEqual(reference._check_root(root), [])

    def test_valid_report_and_catalog(self):
        root = make_root(self.tmp_path)
        add_report(root)
        refresh_catalog(root)
        self.assertEqual(reference._check_root(root), [])

    def test_structural_root_names_are_exact(self):
        root = make_root(self.tmp_path)
        (root / "AGENTS.md").rename(root / "agents.md")
        problems = reference._check_root(root)
        self.assertTrue(any("required file AGENTS.md is missing" in p.message for p in problems))

    def test_structural_nested_names_are_exact(self):
        root = make_root(self.tmp_path)
        (root / "tools" / "reference.py").rename(root / "tools" / "Reference.py")
        problems = reference._check_root(root)
        self.assertTrue(any("required file reference.py is missing" in p.message for p in problems))

    def test_report_root_names_are_exact(self):
        root = make_root(self.tmp_path)
        package = add_report(root)
        (package / "REPORT.json").rename(package / "report.json")
        problems = reference._check_root(root)
        self.assertTrue(any("required file REPORT.json is missing" in p.message for p in problems))

    def test_structural_intermediate_directory_must_be_real_directory(self):
        root = make_root(self.tmp_path)
        external = root / "external-tools"
        external.mkdir()
        (external / "reference.py").write_bytes(SCRIPT.read_bytes())
        for child in (root / "tools").iterdir():
            child.unlink()
        (root / "tools").rmdir()
        try:
            (root / "tools").symlink_to(external, target_is_directory=True)
        except OSError as exc:
            self.skipTest(f"symlinks unavailable: {exc}")
        problems = reference._check_root(root)
        self.assertTrue(any("tools" in str(p.path) and "ordinary directory" in p.message for p in problems))

    def test_candidate_root_symlink_is_rejected(self):
        root = make_root(self.tmp_path)
        alias = self.tmp_path / "alias"
        try:
            alias.symlink_to(root, target_is_directory=True)
        except OSError as exc:
            self.skipTest(f"symlinks unavailable: {exc}")
        result = subprocess.run(
            [sys.executable, str(alias / "tools" / "reference.py"), "check"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("must be an ordinary directory", result.stderr)

    def test_cli_has_no_external_root_override(self):
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(self.tmp_path), "check"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 2)

    def test_required_source_files_must_be_utf8(self):
        root = make_root(self.tmp_path)
        (root / "README.md").write_bytes(b"\xff")
        self.assertTrue(any("not valid UTF-8" in p.message for p in reference._check_root(root)))

    def test_duplicate_json_keys_are_rejected(self):
        root = make_root(self.tmp_path)
        package = root / "reports" / "duplicate"
        package.mkdir(parents=True)
        (package / "REPORT.json").write_text(
            '{"topics":["a"],"topics":["b"],"subjects":[],"observed_at":"2026-09-24"}',
            encoding="utf-8",
        )
        (package / "REPORT.md").write_text("# Example\n", encoding="utf-8")
        root_entries, _ = reference._root_structure(root)
        _, problems = reference._load_reports(root, root_entries)
        self.assertTrue(any("duplicate object key" in p.message for p in problems))

    def test_nonstandard_json_constants_are_rejected(self):
        root = make_root(self.tmp_path)
        package = root / "reports" / "constant"
        package.mkdir(parents=True)
        (package / "REPORT.json").write_text(
            '{"topics":["a"],"subjects":[],"observed_at":NaN}', encoding="utf-8"
        )
        (package / "REPORT.md").write_text("# Example\n", encoding="utf-8")
        root_entries, _ = reference._root_structure(root)
        _, problems = reference._load_reports(root, root_entries)
        self.assertTrue(any("invalid JSON constant" in p.message for p in problems))

    def test_lone_unicode_surrogate_is_rejected(self):
        root = make_root(self.tmp_path)
        package = root / "reports" / "surrogate"
        package.mkdir(parents=True)
        (package / "REPORT.json").write_text(
            r'{"topics":["a"],"subjects":[{"name":"\ud800","identity":{"x":"y"}}],"observed_at":"2026-09-24"}',
            encoding="utf-8",
        )
        (package / "REPORT.md").write_text("# Example\n", encoding="utf-8")
        root_entries, _ = reference._root_structure(root)
        _, problems = reference._load_reports(root, root_entries)
        self.assertTrue(any("Unicode scalar" in p.message for p in problems))

    def test_metadata_validation(self):
        cases = [
            ({"subjects": valid_metadata()["subjects"], "observed_at": "2026-09-24"}, "missing metadata keys"),
            (valid_metadata(extra="x"), "unknown metadata keys"),
            (valid_metadata(topics=[]), "'topics' must be a non-empty array"),
            (valid_metadata(topics=["Lean/Bad"]), "lowercase slash-separated"),
            (valid_metadata(topics=["lean", "lean"]), "duplicate topic"),
            (valid_metadata(subjects=[]), "'subjects' must be a non-empty array"),
            (valid_metadata(subjects=[{"name": "X", "identity": {}}]), "identity must be a non-empty object"),
            (valid_metadata(subjects=[{"name": "X", "identity": {"revision": ""}}]), "must be a non-empty string"),
            (valid_metadata(observed_at="2026-02-30"), "valid YYYY-MM-DD"),
        ]
        for idx, (metadata, needle) in enumerate(cases):
            with self.subTest(needle=needle):
                root = make_root(self.tmp_path / str(idx))
                add_report(root, metadata=metadata)
                root_entries, _ = reference._root_structure(root)
                _, problems = reference._load_reports(root, root_entries)
                self.assertTrue(any(needle in p.message for p in problems))

    def test_subject_names_need_not_be_unique(self):
        root = make_root(self.tmp_path)
        add_report(
            root,
            metadata=valid_metadata(
                subjects=[
                    {"name": "Lean 4", "identity": {"revision": "aaa"}},
                    {"name": "Lean 4", "identity": {"revision": "bbb"}},
                ]
            ),
        )
        refresh_catalog(root)
        self.assertEqual(reference._check_root(root), [])

    def test_subject_unknown_key_is_rejected(self):
        root = make_root(self.tmp_path)
        add_report(
            root,
            metadata=valid_metadata(
                subjects=[{"name": "X", "identity": {"revision": "abc"}, "role": "tool"}]
            ),
        )
        root_entries, _ = reference._root_structure(root)
        _, problems = reference._load_reports(root, root_entries)
        self.assertTrue(any("unknown keys" in p.message for p in problems))

    def test_immediate_children_of_reports_are_packages(self):
        root = make_root(self.tmp_path)
        stray = root / "reports" / "stray.txt"
        stray.parent.mkdir(parents=True)
        stray.write_text("x", encoding="utf-8")
        self.assertTrue(any("must be directories" in p.message for p in reference._check_root(root)))

    def test_package_names_are_simple_slugs(self):
        root = make_root(self.tmp_path)
        (root / "reports" / "Lean.Bad").mkdir(parents=True)
        self.assertTrue(any("lowercase ASCII words" in p.message for p in reference._check_root(root)))

    def test_package_requires_report_root_files(self):
        root = make_root(self.tmp_path)
        (root / "reports" / "missing").mkdir(parents=True)
        problems = reference._check_root(root)
        self.assertTrue(any("REPORT.json" in p.message for p in problems))
        self.assertTrue(any("REPORT.md" in p.message for p in problems))

    def test_support_material_is_structurally_opaque(self):
        root = make_root(self.tmp_path)
        package = add_report(root)
        nested = package / "fixtures" / "nested"
        nested.mkdir(parents=True)
        (nested / "REPORT.json").write_text("not metadata", encoding="utf-8")
        (nested / "REPORT.md").write_bytes(b"\xff")
        refresh_catalog(root)
        self.assertEqual(reference._check_root(root), [])

    def test_invalid_report_never_produces_report_object(self):
        root = make_root(self.tmp_path)
        package = add_report(root, metadata=valid_metadata(subjects=[]))
        report, problems = reference._load_report(package)
        self.assertIsNone(report)
        self.assertTrue(problems)

    def test_catalog_is_canonical_ascii_bytes(self):
        root = make_root(self.tmp_path)
        add_report(root, metadata=valid_metadata(subjects=[{"name": "Léan", "identity": {"revision": "α"}}]))
        root_entries, _ = reference._root_structure(root)
        reports, problems = reference._load_reports(root, root_entries)
        self.assertEqual(problems, [])
        catalog = reference._catalog_bytes(reports)
        catalog.decode("ascii")
        self.assertIn(b"\\u00e9", catalog)
        self.assertTrue(catalog.endswith(b"\n"))
        self.assertNotIn(b"\r", catalog)

    def test_crlf_catalog_is_stale(self):
        root = make_root(self.tmp_path)
        canonical = reference._catalog_bytes([])
        (root / "CATALOG.json").write_bytes(canonical.replace(b"\n", b"\r\n"))
        self.assertTrue(any("generated catalog is stale" in p.message for p in reference._check_root(root)))

    def test_catalog_replacement_breaks_hardlinks_without_mutating_target(self):
        if not hasattr(os, "link"):
            self.skipTest("hardlinks unavailable")
        root = make_root(self.tmp_path)
        external = self.tmp_path / "external.json"
        external.write_bytes(b"unchanged\n")
        catalog = root / "CATALOG.json"
        catalog.unlink()
        try:
            os.link(external, catalog)
        except OSError as exc:
            self.skipTest(f"hardlinks unavailable: {exc}")
        reference._replace_catalog(catalog, reference._catalog_bytes([]))
        self.assertEqual(external.read_bytes(), b"unchanged\n")
        self.assertEqual(reference._check_root(root), [])

    def test_catalog_replacement_replaces_symlink_without_following_target(self):
        root = make_root(self.tmp_path)
        external = self.tmp_path / "external.json"
        external.write_bytes(b"unchanged\n")
        catalog = root / "CATALOG.json"
        catalog.unlink()
        try:
            catalog.symlink_to(external)
        except OSError as exc:
            self.skipTest(f"symlinks unavailable: {exc}")
        reference._replace_catalog(catalog, reference._catalog_bytes([]))
        self.assertEqual(external.read_bytes(), b"unchanged\n")
        self.assertFalse(catalog.is_symlink())
        self.assertEqual(reference._check_root(root), [])

    def test_catalog_replacement_leaves_no_temporary_files(self):
        root = make_root(self.tmp_path)
        reference._replace_catalog(root / "CATALOG.json", reference._catalog_bytes([]))
        self.assertEqual(list(root.glob(".CATALOG.json.*")), [])

    def test_catalog_command_repairs_missing_or_malformed_catalog(self):
        root = make_root(self.tmp_path)
        add_report(root)
        catalog = root / "CATALOG.json"
        catalog.unlink()
        result = subprocess.run(
            [sys.executable, str(root / "tools" / "reference.py"), "catalog"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(reference._check_root(root), [])
        catalog.write_bytes(b"\xff")
        result = subprocess.run(
            [sys.executable, str(root / "tools" / "reference.py"), "catalog"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(reference._check_root(root), [])

    def test_catalog_command_refuses_invalid_report_without_rewriting_catalog(self):
        root = make_root(self.tmp_path)
        original = (root / "CATALOG.json").read_bytes()
        package = root / "reports" / "bad"
        package.mkdir(parents=True)
        (package / "REPORT.json").write_text("not json", encoding="utf-8")
        (package / "REPORT.md").write_text("# bad\n", encoding="utf-8")
        result = subprocess.run(
            [sys.executable, str(root / "tools" / "reference.py"), "catalog"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 1)
        self.assertEqual((root / "CATALOG.json").read_bytes(), original)

    def test_catalog_directory_is_not_replaced(self):
        root = make_root(self.tmp_path)
        catalog = root / "CATALOG.json"
        catalog.unlink()
        catalog.mkdir()
        result = subprocess.run(
            [sys.executable, str(root / "tools" / "reference.py"), "catalog"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 1)
        self.assertTrue(catalog.is_dir())

    def test_check_cli_exit_status(self):
        root = make_root(self.tmp_path)
        result = subprocess.run(
            [sys.executable, str(root / "tools" / "reference.py"), "check"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("reference check passed", result.stdout)


if __name__ == "__main__":
    unittest.main()
