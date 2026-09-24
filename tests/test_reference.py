from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "reference.py"
SPEC = importlib.util.spec_from_file_location("reference_tool", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
reference = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = reference
SPEC.loader.exec_module(reference)

REQUIRED_SECTIONS = """\
## Summary

A compact summary.

## Applicability

Applies to the exact subject above.

## Findings

Basis: source

The behavior is deterministic for this fixture.

## Boundaries

Other versions were not examined.

## Evidence

Inspected the pinned source.

## Revalidation

Rerun the fixture.
"""


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


def report_text(metadata=None, *, title="Example behavior", sections=REQUIRED_SECTIONS):
    metadata = valid_metadata() if metadata is None else metadata
    return (
        "<!-- reference-metadata\n"
        + json.dumps(metadata, indent=2, sort_keys=True)
        + "\n-->\n\n"
        + f"# {title}\n\n"
        + sections
    )


def make_root(tmp_path: Path) -> Path:
    root = tmp_path / "repo"
    root.mkdir(parents=True)
    for name in ("AGENTS.md", "FORMAT.md", "README.md"):
        (root / name).write_text(f"# {name}\n", encoding="utf-8")
    (root / "reports").mkdir()
    (root / "CATALOG.md").write_text(reference.generate_catalog(root, []), encoding="utf-8")
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
    (root / "CATALOG.md").write_text(reference.generate_catalog(root, reports), encoding="utf-8")


def messages(problems):
    return [problem.message for problem in problems]


def _git(cwd: Path, *args: str, check=True) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env.update(
        {
            "GIT_AUTHOR_NAME": "Reference Test",
            "GIT_AUTHOR_EMAIL": "reference@example.invalid",
            "GIT_COMMITTER_NAME": "Reference Test",
            "GIT_COMMITTER_EMAIL": "reference@example.invalid",
        }
    )
    return subprocess.run(
        ["git", *args], cwd=cwd, env=env, text=True, capture_output=True, check=check
    )


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

    def test_metadata_must_be_first(self):
        root = make_root(self.tmp_path)
        path = add_report(root, text="preface\n" + report_text())
        _, problems = reference.parse_report(path)
        self.assertTrue(any("must begin with" in message for message in messages(problems)))

    def test_invalid_json_is_reported(self):
        root = make_root(self.tmp_path)
        text = "<!-- reference-metadata\n{ nope }\n-->\n\n# X\n\n" + REQUIRED_SECTIONS
        path = add_report(root, text=text)
        _, problems = reference.parse_report(path)
        self.assertTrue(
            any("invalid reference metadata JSON" in message for message in messages(problems))
        )

    def test_metadata_validation(self):
        cases = [
            (
                {"subjects": valid_metadata()["subjects"], "observed_at": "2026-09-24"},
                "missing metadata keys: topics",
            ),
            (valid_metadata(extra="x"), "unknown metadata keys: extra"),
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
            (
                valid_metadata(observed_under={}),
                "'observed_under' must be a non-empty object",
            ),
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

    def test_required_sections_must_be_present_and_ordered(self):
        root = make_root(self.tmp_path)
        sections = REQUIRED_SECTIONS.replace("## Applicability", "## Zzz", 1)
        path = add_report(root, text=report_text(sections=sections))
        _, problems = reference.parse_report(path)
        self.assertTrue(
            any("missing required section '## Applicability'" in m for m in messages(problems))
        )

        reordered = REQUIRED_SECTIONS.replace(
            "## Summary\n\nA compact summary.\n\n## Applicability\n\nApplies to the exact subject above.",
            "## Applicability\n\nApplies to the exact subject above.\n\n## Summary\n\nA compact summary.",
        )
        path.write_text(report_text(sections=reordered), encoding="utf-8")
        _, problems = reference.parse_report(path)
        self.assertTrue(any("must appear in FORMAT.md order" in m for m in messages(problems)))

    def test_required_section_must_not_be_empty(self):
        root = make_root(self.tmp_path)
        sections = REQUIRED_SECTIONS.replace(
            "## Boundaries\n\nOther versions were not examined.", "## Boundaries\n"
        )
        path = add_report(root, text=report_text(sections=sections))
        _, problems = reference.parse_report(path)
        self.assertTrue(any("'## Boundaries' must not be empty" in m for m in messages(problems)))

    def test_only_one_h1_and_it_comes_first(self):
        root = make_root(self.tmp_path)
        path = add_report(
            root,
            text=report_text().replace(
                "# Example behavior", "intro\n\n# Example behavior\n\n# Second", 1
            ),
        )
        _, problems = reference.parse_report(path)
        rendered = messages(problems)
        self.assertTrue(any("exactly one H1" in m for m in rendered))
        self.assertTrue(any("first non-empty line" in m for m in rendered))

    def test_broken_local_link_is_reported(self):
        root = make_root(self.tmp_path)
        text = report_text().replace("A compact summary.", "A compact [summary](missing.md).")
        add_report(root, text=text)
        problems = reference.check(root)
        self.assertTrue(any("broken local link" in problem.message for problem in problems))

    def test_existing_local_link_with_fragment_is_accepted(self):
        root = make_root(self.tmp_path)
        support = root / "reports" / "lean" / "example" / "evidence" / "notes.md"
        support.parent.mkdir(parents=True)
        support.write_text("# Notes\n", encoding="utf-8")
        text = report_text().replace("A compact summary.", "See [notes](evidence/notes.md#notes).")
        add_report(root, text=text)
        refresh_catalog(root)
        self.assertEqual(reference.check(root), [])

    def test_files_under_reports_must_belong_to_report(self):
        root = make_root(self.tmp_path)
        stray = root / "reports" / "lean" / "stray.txt"
        stray.parent.mkdir(parents=True)
        stray.write_text("x", encoding="utf-8")
        problems = reference.check(root)
        self.assertTrue(
            any("must belong to a directory containing REPORT.md" in p.message for p in problems)
        )

    def test_report_support_file_location_is_restricted(self):
        root = make_root(self.tmp_path)
        add_report(root)
        bad = root / "reports" / "lean" / "example" / "notes.txt"
        bad.write_text("x", encoding="utf-8")
        problems = reference.check(root)
        self.assertTrue(any("must be under evidence/ or probes/" in p.message for p in problems))

    def test_nested_support_files_are_allowed(self):
        root = make_root(self.tmp_path)
        add_report(root)
        nested = root / "reports" / "lean" / "example" / "probes" / "nested" / "probe.lean"
        nested.parent.mkdir(parents=True)
        nested.write_text("example : True := trivial\n", encoding="utf-8")
        refresh_catalog(root)
        self.assertEqual(reference.check(root), [])

    def test_catalog_is_deterministic_and_sorted_by_path(self):
        root = make_root(self.tmp_path)
        add_report(
            root,
            "reports/zeta/z/REPORT.md",
            report_text(title="Z report", metadata=valid_metadata(topics=["zeta"])),
        )
        add_report(
            root,
            "reports/alpha/a/REPORT.md",
            report_text(title="A report", metadata=valid_metadata(topics=["alpha"])),
        )
        reports, problems = reference.load_reports(root)
        self.assertEqual(problems, [])
        first = reference.generate_catalog(root, list(reversed(reports)))
        second = reference.generate_catalog(root, reports)
        self.assertEqual(first, second)
        self.assertLess(first.index("A report"), first.index("Z report"))

    def test_catalog_contains_derived_fields(self):
        root = make_root(self.tmp_path)
        add_report(root)
        reports, problems = reference.load_reports(root)
        self.assertEqual(problems, [])
        catalog = reference.generate_catalog(root, reports)
        self.assertIn("[Example behavior](reports/lean/example/REPORT.md)", catalog)
        self.assertIn("`lean/elaboration`", catalog)
        self.assertIn("Lean 4 (repository=leanprover/lean4", catalog)
        self.assertIn("Summary: A compact summary.", catalog)

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
        self.assertIn("wrote CATALOG.md (1 reports)", result.stdout)
        self.assertEqual(reference.check(root), [])

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

    def test_orphan_branch_root_has_no_parents(self):
        repo = self.tmp_path / "repo"
        repo.mkdir()
        _git(repo, "init", "-q")
        _git(repo, "checkout", "--orphan", "reference")
        (repo / "README.md").write_text("root\n", encoding="utf-8")
        _git(repo, "add", "README.md")
        _git(repo, "commit", "-q", "-m", "root")
        parents = _git(repo, "show", "-s", "--format=%P", "HEAD").stdout.strip()
        self.assertEqual(parents, "")

    def test_concurrent_writers_require_fast_forward_reconciliation(self):
        seed = self.tmp_path / "seed"
        remote = self.tmp_path / "remote.git"
        writer_a = self.tmp_path / "writer-a"
        writer_b = self.tmp_path / "writer-b"

        seed.mkdir()
        _git(seed, "init", "-q")
        _git(seed, "checkout", "--orphan", "reference")
        (seed / "BASE").write_text("base\n", encoding="utf-8")
        _git(seed, "add", "BASE")
        _git(seed, "commit", "-q", "-m", "root")

        subprocess.run(["git", "init", "--bare", "-q", str(remote)], check=True)
        _git(seed, "remote", "add", "origin", str(remote))
        _git(seed, "push", "-q", "origin", "reference")
        subprocess.run(
            ["git", "--git-dir", str(remote), "symbolic-ref", "HEAD", "refs/heads/reference"],
            check=True,
        )

        subprocess.run(["git", "clone", "-q", str(remote), str(writer_a)], check=True)
        subprocess.run(["git", "clone", "-q", str(remote), str(writer_b)], check=True)

        (writer_a / "A").write_text("a\n", encoding="utf-8")
        _git(writer_a, "add", "A")
        _git(writer_a, "commit", "-q", "-m", "writer A")
        _git(writer_a, "push", "-q", "origin", "reference")

        (writer_b / "B").write_text("b\n", encoding="utf-8")
        _git(writer_b, "add", "B")
        _git(writer_b, "commit", "-q", "-m", "writer B")
        rejected = _git(writer_b, "push", "origin", "reference", check=False)
        self.assertNotEqual(rejected.returncode, 0)
        self.assertTrue("fetch first" in rejected.stderr or "non-fast-forward" in rejected.stderr)

        _git(writer_b, "fetch", "-q", "origin", "reference")
        _git(writer_b, "rebase", "origin/reference")
        _git(writer_b, "push", "-q", "origin", "reference")

        verification = self.tmp_path / "verification"
        subprocess.run(["git", "clone", "-q", str(remote), str(verification)], check=True)
        self.assertEqual((verification / "A").read_text(encoding="utf-8"), "a\n")
        self.assertEqual((verification / "B").read_text(encoding="utf-8"), "b\n")
        self.assertEqual(_git(verification, "rev-list", "--count", "HEAD").stdout.strip(), "3")

    def test_multi_file_candidate_becomes_visible_in_one_ref_update(self):
        repo = self.tmp_path / "repo"
        remote = self.tmp_path / "remote.git"
        repo.mkdir()
        _git(repo, "init", "-q")
        _git(repo, "checkout", "--orphan", "reference")
        (repo / "BASE").write_text("base\n", encoding="utf-8")
        _git(repo, "add", "BASE")
        _git(repo, "commit", "-q", "-m", "root")
        subprocess.run(["git", "init", "--bare", "-q", str(remote)], check=True)
        _git(repo, "remote", "add", "origin", str(remote))
        _git(repo, "push", "-q", "origin", "reference")

        old_remote = subprocess.run(
            ["git", "--git-dir", str(remote), "rev-parse", "refs/heads/reference"],
            text=True,
            capture_output=True,
            check=True,
        ).stdout.strip()

        (repo / "REPORT.md").write_text("report\n", encoding="utf-8")
        (repo / "CATALOG.md").write_text("catalog\n", encoding="utf-8")
        _git(repo, "add", "REPORT.md", "CATALOG.md")
        _git(repo, "commit", "-q", "-m", "candidate")
        new_local = _git(repo, "rev-parse", "HEAD").stdout.strip()

        self.assertNotEqual(old_remote, new_local)
        before = subprocess.run(
            ["git", "--git-dir", str(remote), "ls-tree", "--name-only", "refs/heads/reference"],
            text=True,
            capture_output=True,
            check=True,
        ).stdout.splitlines()
        self.assertNotIn("REPORT.md", before)
        self.assertNotIn("CATALOG.md", before)

        _git(repo, "push", "-q", "origin", "reference")
        after = subprocess.run(
            ["git", "--git-dir", str(remote), "ls-tree", "--name-only", "refs/heads/reference"],
            text=True,
            capture_output=True,
            check=True,
        ).stdout.splitlines()
        self.assertIn("REPORT.md", after)
        self.assertIn("CATALOG.md", after)

    def test_headings_and_links_inside_fenced_code_are_ignored(self):
        root = make_root(self.tmp_path)
        sections = REQUIRED_SECTIONS.replace(
            "The behavior is deterministic for this fixture.",
            """The behavior is deterministic for this fixture.\n\n```markdown\n## Summary\n[not a real link](missing.md)\n```""",
        )
        add_report(root, text=report_text(sections=sections))
        refresh_catalog(root)
        self.assertEqual(reference.check(root), [])

    def test_local_link_must_not_escape_corpus_root(self):
        root = make_root(self.tmp_path)
        outside = self.tmp_path / "outside.md"
        outside.write_text("outside\n", encoding="utf-8")
        text = report_text().replace(
            "A compact summary.", "See [outside](../../../../outside.md)."
        )
        add_report(root, text=text)
        problems = reference.check(root)
        self.assertTrue(any("local link escapes corpus root" in p.message for p in problems))

    def test_nested_reports_are_rejected(self):
        root = make_root(self.tmp_path)
        add_report(root, "reports/lean/outer/REPORT.md")
        add_report(root, "reports/lean/outer/inner/REPORT.md")
        problems = reference.check(root)
        self.assertTrue(any("report directories must not be nested" in p.message for p in problems))

    def test_invalid_utf8_report_is_reported(self):
        root = make_root(self.tmp_path)
        path = root / "reports" / "lean" / "bad" / "REPORT.md"
        path.parent.mkdir(parents=True)
        path.write_bytes(b"\xff\xfe")
        _, problems = reference.parse_report(path)
        self.assertTrue(any("not valid UTF-8" in p.message for p in problems))

    def test_catalog_command_refuses_invalid_report_without_rewriting_catalog(self):
        root = make_root(self.tmp_path)
        original = (root / "CATALOG.md").read_text(encoding="utf-8")
        add_report(root, text="not a report")
        result = subprocess.run(
            [sys.executable, str(SCRIPT), "--root", str(root), "catalog"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 1)
        self.assertEqual((root / "CATALOG.md").read_text(encoding="utf-8"), original)


if __name__ == "__main__":
    unittest.main()
