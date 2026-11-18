from __future__ import annotations

from dataclasses import FrozenInstanceError
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


POLICY_DATA = {"schema": "reference-corpus/1", "topic_namespaces": ["optics", "sensors"]}
POLICY = reference.parse_policy(json.dumps(POLICY_DATA).encode("utf-8"))


def valid_metadata(**overrides):
    data = {
        "topics": ["optics", "optics/calibration"],
        "subjects": [
            {
                "name": "Sensor model",
                "identity": {
                    "repository": "example/sensors",
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
    (root / "CORPUS.json").write_text(json.dumps(POLICY_DATA), encoding="utf-8")
    (root / "CATALOG.json").write_bytes(reference._catalog_bytes([]))
    return root


DEFAULT_PROSE = """# Example

## Summary
## Applicability
## Findings
## Boundaries
## Evidence
## Revalidation
"""


def add_report(root: Path, name="example", metadata=None, prose=DEFAULT_PROSE) -> Path:
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
    reports, problems = reference._load_reports(root, root_entries, POLICY)
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
        _, problems = reference._load_reports(root, root_entries, POLICY)
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
        _, problems = reference._load_reports(root, root_entries, POLICY)
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
        _, problems = reference._load_reports(root, root_entries, POLICY)
        self.assertTrue(any("scalar UTF-8" in p.message for p in problems))

    def test_metadata_validation(self):
        cases = [
            ({"subjects": valid_metadata()["subjects"], "observed_at": "2026-09-24"}, "missing metadata keys"),
            (valid_metadata(extra="x"), "unknown metadata keys"),
            (valid_metadata(topics=[]), "'topics' must be a non-empty array"),
            (valid_metadata(topics=["Optics/Bad"]), "lowercase slash-separated"),
            (valid_metadata(topics=["unknown/subtopic"]), "top-level namespace 'unknown'"),
            (valid_metadata(topics=["optics", "optics"]), "duplicate topic"),
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
                _, problems = reference._load_reports(root, root_entries, POLICY)
                self.assertTrue(any(needle in p.message for p in problems))

    def test_subject_names_need_not_be_unique(self):
        root = make_root(self.tmp_path)
        add_report(
            root,
            metadata=valid_metadata(
                subjects=[
                    {"name": "Sensor model", "identity": {"revision": "aaa"}},
                    {"name": "Sensor model", "identity": {"revision": "bbb"}},
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
        _, problems = reference._load_reports(root, root_entries, POLICY)
        self.assertTrue(any("unknown keys" in p.message for p in problems))

    def test_immediate_children_of_reports_are_packages(self):
        root = make_root(self.tmp_path)
        stray = root / "reports" / "stray.txt"
        stray.parent.mkdir(parents=True)
        stray.write_text("x", encoding="utf-8")
        self.assertTrue(any("must be directories" in p.message for p in reference._check_root(root)))

    def test_package_names_are_simple_slugs(self):
        root = make_root(self.tmp_path)
        (root / "reports" / "Optics.Bad").mkdir(parents=True)
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
        report, problems = reference._load_report(package, POLICY)
        self.assertIsNone(report)
        self.assertTrue(problems)

    def test_support_bytes_modes_and_links_are_opaque(self):
        root = make_root(self.tmp_path)
        package = add_report(root)
        probe = package / "probe"
        probe.write_bytes(b"\x00\xffopaque executable bytes\n")
        probe.chmod(0o755)
        external = self.tmp_path / "external-source"
        external.write_bytes(b"must not inspect or rewrite this target\n")
        link = package / "external-link"
        try:
            link.symlink_to(external)
        except OSError as exc:
            self.skipTest(f"symlinks unavailable: {exc}")
        refresh_catalog(root)
        self.assertEqual(reference._check_root(root), [])
        self.assertEqual(probe.read_bytes(), b"\x00\xffopaque executable bytes\n")
        self.assertEqual(probe.stat().st_mode & 0o777, 0o755)
        self.assertTrue(link.is_symlink())
        self.assertEqual(os.readlink(link), str(external))
        self.assertEqual(external.read_bytes(), b"must not inspect or rewrite this target\n")

    def test_catalog_is_canonical_ascii_bytes(self):
        root = make_root(self.tmp_path)
        add_report(root, metadata=valid_metadata(subjects=[{"name": "Léan", "identity": {"revision": "α"}}]))
        root_entries, _ = reference._root_structure(root)
        reports, problems = reference._load_reports(root, root_entries, POLICY)
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

    def test_all_selected_topic_namespaces_are_accepted(self):
        root = make_root(self.tmp_path)
        topics = []
        for ns in sorted(POLICY.topic_namespaces):
            topics.append(ns)
            topics.append(f"{ns}/subtopic")
        add_report(root, metadata=valid_metadata(topics=topics))
        refresh_catalog(root)
        self.assertEqual(reference._check_root(root), [])

    def test_prose_section_validation(self):
        cases = [
            (
                "## Summary\n## Applicability\n## Findings\n## Boundaries\n## Evidence\n## Revalidation\n",
                "exactly one top-level '# <title>' heading",
            ),
            (
                "# Title 1\n# Title 2\n## Summary\n## Applicability\n## Findings\n## Boundaries\n## Evidence\n## Revalidation\n",
                "exactly one top-level '# <title>' heading",
            ),
            (
                "# Title\n## Summary\n## Applicability\n## Findings\n## Boundaries\n## Evidence\n",
                "must contain exact top-level sections in order",
            ),
            (
                "# Title\n## Applicability\n## Summary\n## Findings\n## Boundaries\n## Evidence\n## Revalidation\n",
                "must contain exact top-level sections in order",
            ),
            (
                "# Title\n## Summary\n## Applicability\n## Findings\n## Extra\n## Boundaries\n## Evidence\n## Revalidation\n",
                "must contain exact top-level sections in order",
            ),
            (
                "## Summary\n# Title\n## Applicability\n## Findings\n## Boundaries\n## Evidence\n## Revalidation\n",
                "must appear before '## Summary'",
            ),
        ]
        for idx, (prose, needle) in enumerate(cases):
            with self.subTest(needle=needle, idx=idx):
                root = make_root(self.tmp_path / f"prose-{idx}")
                add_report(root, prose=prose)
                root_entries, _ = reference._root_structure(root)
                _, problems = reference._load_reports(root, root_entries, POLICY)
                self.assertTrue(any(needle in p.message for p in problems), [p.message for p in problems])

    def test_prose_headings_inside_fenced_code_blocks_are_ignored(self):
        root = make_root(self.tmp_path)
        prose = """# Example Title

## Summary

```markdown
# Not a title
## Not a section
```

## Applicability
### Subheading is allowed
## Findings
~~~sh
# shell comment
## another comment
~~~
## Boundaries
## Evidence
## Revalidation
"""
        add_report(root, prose=prose)
        refresh_catalog(root)
        self.assertEqual(reference._check_root(root), [])


    def test_policy_is_strict_and_has_no_fallback(self):
        invalid = [
            {},
            {"schema": "reference-corpus/1"},
            {**POLICY_DATA, "extra": True},
            {**POLICY_DATA, "schema": "reference-corpus/2"},
            {**POLICY_DATA, "topic_namespaces": []},
            {**POLICY_DATA, "topic_namespaces": "optics"},
            {**POLICY_DATA, "topic_namespaces": ["optics", "optics"]},
        ]
        invalid.extend({**POLICY_DATA, "topic_namespaces": [name]}
                       for name in ["", "Optics", "two/segments", "é", "-bad", None, 3])
        for value in invalid:
            with self.subTest(value=value):
                with self.assertRaises(reference.ValidationFailure):
                    reference.parse_policy(json.dumps(value).encode("utf-8"))
        for data in [b'{} trailing', b'\xff',
                     b'{"schema":"reference-corpus/1","schema":"reference-corpus/1","topic_namespaces":["optics"]}',
                     b'{"schema":"reference-corpus/1","topic_namespaces":[NaN]}',
                     b'{"schema":"reference-corpus/1","topic_namespaces":["\\ud800"]}']:
            with self.subTest(data=data):
                with self.assertRaises(reference.ValidationFailure):
                    reference.parse_policy(data)

    def test_policy_value_is_immutable_and_validated_at_construction(self):
        with self.assertRaises(FrozenInstanceError):
            POLICY.topic_namespaces = frozenset({"other"})
        for namespaces in [frozenset(), frozenset({"bad/name"}), {"optics"}]:
            with self.subTest(namespaces=namespaces):
                with self.assertRaises(ValueError):
                    reference.CorpusPolicy(namespaces)

    def test_unrelated_policy_accepts_its_topics_with_identical_checker(self):
        root = make_root(self.tmp_path)
        alternate = {"schema": "reference-corpus/1", "topic_namespaces": ["maps+data", "terrain.v2"]}
        (root / "CORPUS.json").write_text(json.dumps(alternate), encoding="utf-8")
        add_report(root, metadata=valid_metadata(topics=["maps+data", "terrain.v2/ridges"]))
        result = subprocess.run(
            [sys.executable, str(root / "tools/reference.py"), "catalog"],
            cwd=self.tmp_path, capture_output=True, check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(reference._check_root(root), [])
        self.assertEqual((root / "tools/reference.py").read_bytes(), SCRIPT.read_bytes())
        (root / "CORPUS.json").write_text(json.dumps(POLICY_DATA), encoding="utf-8")
        self.assertTrue(any("top-level namespace" in p.message for p in reference._check_root(root)))

    def test_missing_wrong_case_and_symlink_policy_are_rejected(self):
        root = make_root(self.tmp_path)
        policy = root / "CORPUS.json"
        policy.rename(root / "corpus.json")
        self.assertTrue(any("CORPUS.json" in str(p.path) for p in reference._check_root(root)))
        (root / "corpus.json").unlink()
        external = self.tmp_path / "external-policy.json"
        external.write_text(json.dumps(POLICY_DATA), encoding="utf-8")
        policy.symlink_to(external)
        self.assertTrue(any("ordinary file" in p.message for p in reference._check_root(root)))

    def test_invalid_policy_does_not_replace_catalog(self):
        root = make_root(self.tmp_path)
        original = (root / "CATALOG.json").read_bytes()
        for data in [b'{}', b'{"schema":"reference-corpus/1","topic_namespaces":[]}']:
            with self.subTest(data=data):
                (root / "CORPUS.json").write_bytes(data)
                result = subprocess.run(
                    [sys.executable, str(root / "tools/reference.py"), "catalog"],
                    cwd=self.tmp_path, capture_output=True, check=False,
                )
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertEqual((root / "CATALOG.json").read_bytes(), original)

    def test_cli_works_from_unrelated_cwd(self):
        root = make_root(self.tmp_path)
        result = subprocess.run(
            [sys.executable, str(root / "tools/reference.py"), "check"],
            cwd=self.tmp_path, capture_output=True, check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_shared_byte_parser_rejects_invalid_json_and_unicode(self):
        for data in [b'{"key":1,"key":2}', b'NaN', b'1e999', b'"\\udfff"', b'\xff']:
            with self.subTest(data=data):
                with self.assertRaises(reference.ValidationFailure):
                    reference.parse_json(data)
        self.assertEqual(reference.parse_json(b'{"name":"caf\xc3\xa9"}'), {"name": "café"})


if __name__ == "__main__":
    unittest.main()
