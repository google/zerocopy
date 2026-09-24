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


def report_text(metadata=None, body="# Any Markdown body is semantically reviewed elsewhere.\n"):
    metadata = valid_metadata() if metadata is None else metadata
    return (
        "<!-- reference-metadata\n"
        + json.dumps(metadata, indent=2, sort_keys=True)
        + "\n-->\n"
        + body
    )


def make_root(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    root.mkdir(parents=True)
    for name in ("AGENTS.md", "FORMAT.md", "README.md"):
        (root / name).write_text(f"# {name}\n", encoding="utf-8")
    (root / "reports").mkdir()
    (root / "CATALOG.json").write_text(reference.generate_catalog(root, []), encoding="utf-8")
    return root


def add_report(root: Path, rel="reports/lean/example/REPORT.md", text=None) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text if text is not None else report_text(), encoding="utf-8")
    return path


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

    def test_report_body_is_not_mechanically_parsed(self):
        root = make_root(self.tmp_path)
        add_report(root, text=report_text(body="not even valid report prose by FORMAT.md\n"))
        refresh_catalog(root)
        self.assertEqual(reference.check(root), [])

    def test_metadata_must_be_first(self):
        root = make_root(self.tmp_path)
        path = add_report(root, text="preface\n" + report_text())
        _, problems = reference.parse_report(path)
        self.assertTrue(any("must begin with" in message for message in messages(problems)))

    def test_invalid_json_is_reported(self):
        root = make_root(self.tmp_path)
        path = add_report(root, text="<!-- reference-metadata\n{ nope }\n-->\nbody\n")
        _, problems = reference.parse_report(path)
        self.assertTrue(any("invalid reference metadata JSON" in m for m in messages(problems)))

    def test_metadata_validation(self):
        cases = [
            ({"subjects": valid_metadata()["subjects"], "observed_at": "2026-09-24"}, "missing metadata keys: topics"),
            (valid_metadata(extra="x"), "unknown metadata keys: extra"),
            (valid_metadata(observed_under={"host": "linux"}), "unknown metadata keys: observed_under"),
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
            (valid_metadata(subjects=[{"name": "X", "identity": {}}]), "identity must be a non-empty object"),
            (valid_metadata(subjects=[{"name": "X", "identity": {"revision": ""}}]), "must be a non-empty string"),
            (valid_metadata(observed_at="2026-02-30"), "valid YYYY-MM-DD"),
        ]
        for metadata, needle in cases:
            with self.subTest(needle=needle):
                root = make_root(self.tmp_path / needle.replace("/", "_"))
                path = add_report(root, text=report_text(metadata))
                _, problems = reference.parse_report(path)
                self.assertTrue(any(needle in message for message in messages(problems)))

    def test_subject_unknown_key_is_rejected(self):
        root = make_root(self.tmp_path)
        metadata = valid_metadata(
            subjects=[{"name": "X", "identity": {"revision": "abc"}, "role": "tool"}]
        )
        path = add_report(root, text=report_text(metadata))
        _, problems = reference.parse_report(path)
        self.assertTrue(any("unknown keys: role" in message for message in messages(problems)))

    def test_arbitrary_report_owned_support_files_are_allowed(self):
        root = make_root(self.tmp_path)
        add_report(root)
        for rel in (
            "reports/lean/example/fixtures/input.llbc",
            "reports/lean/example/scripts/check.py",
            "reports/lean/example/schema.json",
        ):
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("x\n", encoding="utf-8")
        refresh_catalog(root)
        self.assertEqual(reference.check(root), [])

    def test_files_under_reports_must_belong_to_report(self):
        root = make_root(self.tmp_path)
        stray = root / "reports" / "lean" / "stray.txt"
        stray.parent.mkdir(parents=True)
        stray.write_text("x", encoding="utf-8")
        problems = reference.check(root)
        self.assertTrue(any("must belong to a directory containing REPORT.md" in p.message for p in problems))

    def test_nested_reports_are_rejected(self):
        root = make_root(self.tmp_path)
        add_report(root, "reports/lean/outer/REPORT.md")
        add_report(root, "reports/lean/outer/inner/REPORT.md")
        problems = reference.check(root)
        self.assertTrue(any("report directories must not be nested" in p.message for p in problems))

    def test_symlinks_under_reports_are_rejected(self):
        root = make_root(self.tmp_path)
        add_report(root)
        target = root / "outside.txt"
        target.write_text("outside\n", encoding="utf-8")
        link = root / "reports" / "lean" / "example" / "linked.txt"
        try:
            link.symlink_to(target)
        except OSError as exc:
            self.skipTest(f"symlink creation unavailable: {exc}")
        problems = reference.check(root)
        self.assertTrue(any("symlinks are not allowed" in p.message for p in problems))

    def test_invalid_utf8_report_is_reported(self):
        root = make_root(self.tmp_path)
        path = root / "reports" / "lean" / "bad" / "REPORT.md"
        path.parent.mkdir(parents=True)
        path.write_bytes(b"\xff\xfe")
        _, problems = reference.parse_report(path)
        self.assertTrue(any("not valid UTF-8" in p.message for p in problems))

    def test_catalog_is_deterministic_and_sorted_by_path(self):
        root = make_root(self.tmp_path)
        add_report(root, "reports/zeta/z/REPORT.md", report_text(valid_metadata(topics=["zeta"])))
        add_report(root, "reports/alpha/a/REPORT.md", report_text(valid_metadata(topics=["alpha"])))
        reports, problems = reference.load_reports(root)
        self.assertEqual(problems, [])
        first = reference.generate_catalog(root, list(reversed(reports)))
        second = reference.generate_catalog(root, reports)
        self.assertEqual(first, second)
        parsed = json.loads(first)
        self.assertEqual(
            [entry["path"] for entry in parsed["reports"]],
            ["reports/alpha/a/REPORT.md", "reports/zeta/z/REPORT.md"],
        )

    def test_catalog_copies_only_path_and_metadata(self):
        root = make_root(self.tmp_path)
        add_report(root)
        reports, problems = reference.load_reports(root)
        self.assertEqual(problems, [])
        catalog = json.loads(reference.generate_catalog(root, reports))
        entry = catalog["reports"][0]
        self.assertEqual(set(entry), {"path", "topics", "subjects", "observed_at"})
        self.assertEqual(entry["path"], "reports/lean/example/REPORT.md")
        self.assertEqual(entry["topics"], ["lean", "lean/elaboration"])

    def test_stale_catalog_is_reported(self):
        root = make_root(self.tmp_path)
        add_report(root)
        problems = reference.check(root)
        self.assertTrue(any("generated catalog is stale" in problem.message for problem in problems))

    def test_catalog_command_writes_catalog(self):
        root = make_root(self.tmp_path)
        add_report(root)
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(root), "catalog"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("wrote CATALOG.json (1 reports)", result.stdout)
        self.assertEqual(reference.check(root), [])

    def test_catalog_write_uses_atomic_replace(self):
        root = make_root(self.tmp_path)
        add_report(root)
        with mock.patch.object(reference.os, "replace", wraps=os.replace) as replace:
            result = reference.main(["--root", str(root), "catalog"])
        self.assertEqual(result, 0)
        self.assertEqual(replace.call_count, 1)
        self.assertEqual(Path(replace.call_args.args[1]), root / "CATALOG.json")

    def test_catalog_command_refuses_invalid_report_without_rewriting_catalog(self):
        root = make_root(self.tmp_path)
        original = (root / "CATALOG.json").read_text(encoding="utf-8")
        add_report(root, text="not a report")
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(root), "catalog"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 1)
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
