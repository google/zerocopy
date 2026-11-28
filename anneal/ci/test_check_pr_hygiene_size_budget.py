# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the advisory `review-size` budget in `check_pr_hygiene.py`.

These live apart from `test_check_pr_hygiene.py` and build their own scratch
repositories, so they do not depend on that file's layout.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_pr_hygiene as cph  # noqa: E402

SCRIPT = Path(__file__).resolve().parent / "check_pr_hygiene.py"
BUDGET = cph.REVIEW_SIZE_BUDGET

HEADER_MD = """\
<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->
"""
HEADER_LEAN = """\
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.
"""
CRR = (
    "<!-- code-review-rules:begin -->\n"
    "Rules text.\n"
    "<!-- code-review-rules:end -->\n"
)
MESSAGE = (
    "[ci] Add data\n\n"
    "Add data that the tests need, so they stop generating it.\n\n"
    "Agent-authored-by: AI agent acting on joshlf's behalf\n"
)


def lines(n: int, tag: str = "x") -> str:
    return "".join(f"{tag} {i}\n" for i in range(n))


def git(repo: Path, *args: str) -> str:
    env = {
        **{k: v for k, v in os.environ.items() if not k.startswith("GIT_")},
        "GIT_AUTHOR_NAME": "Test Author",
        "GIT_AUTHOR_EMAIL": "test@example.com",
        "GIT_COMMITTER_NAME": "Test Author",
        "GIT_COMMITTER_EMAIL": "test@example.com",
        "GIT_CONFIG_NOSYSTEM": "1",
        "HOME": str(repo.parent),
    }
    return subprocess.run(
        ["git", "-c", "core.hooksPath=/dev/null", "-c",
         "init.defaultBranch=main", *args],
        cwd=repo, env=env, capture_output=True, text=True, check=True,
    ).stdout


class SizeExclusionTests(unittest.TestCase):
    def test_categories(self):
        cases = {
            "anneal/trusted/cargo-anneal/src/bundled_resources.rs":
                "generated",
            "anneal/trusted/root-manifest.sha256": "generated",
            "anneal/theory/bundled_theory.json": "generated",
            "anneal/Cargo.lock": "lock",
            "anneal/flake.lock": "lock",
            "anneal/theory/lake-manifest.json": "lock",
            "anneal/trusted/lean/foundation-lock.json": "lock",
            "anneal/vendor/x/src/lib.rs": "vendor",
            "anneal/tests/cargo-anneal/tests/fixtures/a/Proof.lean":
                "fixture",
            "anneal/tests/cargo-anneal/tests/fixtures/a/b/StepLemmas.lean":
                "fixture",
            "anneal/tests/corpora/scalar_specs/c/Proof.lean": "fixture",
            "zerocopy/proofs/01_unit/Proof.lean": "fixture",
        }
        for path, want in cases.items():
            with self.subTest(path=path):
                self.assertEqual(cph.size_exclusion(path), want)

    def test_reviewable_paths(self):
        for path in (
            "anneal/ci/check_pr_hygiene.py",
            "anneal/theory/Anneal/Core/Proof.lean",
            "anneal/Cargo.toml",
            # Specs, expectations, and trusted or CI segments stay in scope.
            "anneal/tests/cargo-anneal/tests/fixtures/a/Spec.lean",
            "anneal/tests/cargo-anneal/tests/fixtures/a/SpecProof.lean",
            "anneal/tests/cargo-anneal/tests/fixtures/Expected/Proof.lean",
            "anneal/tests/cargo-anneal/tests/fixtures/trusted/Proof.lean",
            "anneal/tests/cargo-anneal/tests/fixtures/a/lib.rs",
            "anneal/tests/cargo-anneal/tests/fixtures/../x/Proof.lean",
            "anneal/tests/cargo-anneal/tests/fixtures/a\\b/Proof.lean",
            "anneal/tests/cargo-anneal/tests/fixtures/..\\trusted\\x/"
            "Proof.lean",
            # The corpora runner and `zerocopy/proofs/` walk depth 1 only.
            "anneal/tests/corpora/scalar_specs/c/d/Proof.lean",
            "anneal/tests/corpora/scalar_specs/c/Lemmas.lean",
            "zerocopy/proofs/01_unit/sub/Proof.lean",
        ):
            with self.subTest(path=path):
                self.assertIsNone(cph.size_exclusion(path))


class ReviewSizeTests(unittest.TestCase):
    def test_budget_boundary(self):
        at = cph.review_size([("anneal/ci/a.py", BUDGET)])
        self.assertFalse(at.over_budget)
        self.assertIsNone(cph.review_size_warning(at))
        over = cph.review_size([("anneal/ci/a.py", BUDGET),
                                ("anneal/ci/b.py", 1)])
        self.assertTrue(over.over_budget)
        w = cph.review_size_warning(over)
        self.assertIsNotNone(w)
        self.assertEqual(w.check, "review-size")
        self.assertIn(f"{BUDGET + 1} reviewable changed lines in 2 file(s)",
                      w.message)
        self.assertIn("gh stack link --base main", w.message)
        self.assertIn("excluded: none", w.message)

    def test_excluded_lines_do_not_count(self):
        size = cph.review_size([
            ("anneal/ci/a.py", 10),
            ("anneal/Cargo.lock", 5000),
            ("anneal/tests/cargo-anneal/tests/fixtures/a/Proof.lean", 3000),
            ("anneal/docs/logo.png", None),
        ])
        self.assertFalse(size.over_budget)
        self.assertEqual(size.to_json(), {
            "budget": BUDGET,
            "reviewable_lines": 10,
            "reviewable_files": 1,
            "excluded": {
                "generated": {"lines": 0, "files": 0},
                "lock": {"lines": 5000, "files": 1},
                "vendor": {"lines": 0, "files": 0},
                "fixture": {"lines": 3000, "files": 1},
                "binary": {"lines": 0, "files": 1},
            },
            "over_budget": False,
        })

    def test_warning_reports_breakdown(self):
        size = cph.review_size([
            ("anneal/ci/a.py", BUDGET + 50),
            ("anneal/flake.lock", 7),
            ("zerocopy/proofs/01_unit/Proof.lean", 30),
            ("zerocopy/proofs/02_unit/Proof.lean", 12),
            ("anneal/docs/logo.png", None),
        ])
        msg = cph.review_size_warning(size).message
        self.assertIn(
            "excluded: 7 lock line(s) in 1 file(s), 42 fixture line(s) in "
            "2 file(s), 1 binary file(s)", msg)
        self.assertIn("advisory and does not fail the check", msg)

    def test_malformed_numstat_fails_closed(self):
        class FakeGit:
            def __init__(self, raw: bytes):
                self.raw = raw

            def run(self, *args, **kw) -> bytes:
                return self.raw

        ok = b"3\t1\ta.py\0-\t-\tlogo.png\0" b"2\t0\t\0old\0new name\0"
        self.assertEqual(cph.diff_numstat(FakeGit(ok), "a", "b"), [
            ("a.py", 4), ("logo.png", None), ("new name", 2)])
        self.assertEqual(cph.diff_numstat(FakeGit(b""), "a", "b"), [])
        for raw in (b"x\ty\tz\0", b"1\t1\t\0old\0", b"1\t1\t\0\0new\0",
                    b"no tabs\0",
                    # Empty records, leading or embedded, must not end the
                    # scan early and hide later entries.
                    b"\0900\t0\ta.py\0", b"1\t0\ts.py\0\0900\t0\tb.py\0",
                    # Output without a final NUL is truncated.
                    b"900\t0\ta.py", b"900\t0\t\0old\0new",
                    # Non-ASCII digits pass `str.isdigit()`.
                    "\u00b2\t0\ta.py\0".encode()):
            with self.subTest(raw=raw):
                with self.assertRaises(cph.GitError):
                    cph.diff_numstat(FakeGit(raw), "a", "b")


class RepoTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="anneal-review-size-")
        self.repo = Path(self._tmp.name) / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q")
        self.write("AGENTS.md", "Root agent instructions.\n")
        self.write("anneal/AGENTS.md", HEADER_MD + "\n# Rules\n\n" + CRR)
        self.write("anneal/.gemini/styleguide.md", "# Style\n\n" + CRR)
        self.write("anneal/data/old.txt", lines(40, "old"))
        self.commit("Initial commit")
        git(self.repo, "branch", "base")

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def write(self, rel: str, text: str | bytes) -> None:
        path = self.repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(text, bytes):
            path.write_bytes(text)
        else:
            path.write_text(text, encoding="utf-8")

    def commit(self, message: str = MESSAGE) -> str:
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "--allow-empty", "-m", message)
        return git(self.repo, "rev-parse", "HEAD").strip()

    def run_script(self, *args: str, env: dict[str, str] | None = None
                   ) -> subprocess.CompletedProcess[str]:
        base_env = {k: v for k, v in os.environ.items()
                    if k not in ("GITHUB_STEP_SUMMARY", "GITHUB_ACTIONS",
                                 "PR_TITLE")}
        return subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--base", "base", *args],
            capture_output=True, text=True, check=False,
            env={**base_env, **(env or {})},
        )

    def run_json(self, **kw) -> tuple[int, dict[str, object]]:
        res = self.run_script("--json", **kw)
        return res.returncode, json.loads(res.stdout)

    def size_warnings(self, report: dict[str, object]) -> list[dict]:
        return [w for w in report["warnings"] if w["check"] == "review-size"]

    def test_numstat_counts_renames_and_binaries(self):
        git(self.repo, "mv", "anneal/data/old.txt", "anneal/data/new.txt")
        self.write("anneal/data/new.txt", lines(40, "old") + "extra\n")
        self.write("anneal/data/with space.txt", lines(3))
        self.write("anneal/data/with\ttab.txt", lines(2))
        self.write("anneal/data/blob.bin", b"\x00\x01\x02" * 10)
        self.commit()
        git_ = cph.Git(self.repo)
        stats = dict(cph.diff_numstat(git_, git_.commit("base"),
                                      git_.commit("HEAD")))
        self.assertEqual(stats, {
            "anneal/data/new.txt": 1,
            "anneal/data/with space.txt": 3,
            "anneal/data/with\ttab.txt": 2,
            "anneal/data/blob.bin": None,
        })

    def test_over_budget_warns_without_failing(self):
        self.write("anneal/data/big.txt", lines(BUDGET + 1))
        self.commit()
        code, report = self.run_json()
        self.assertEqual(code, 0, report)
        self.assertTrue(report["ok"])
        self.assertEqual(report["findings"], [])
        self.assertEqual(len(self.size_warnings(report)), 1)
        self.assertEqual(report["review_size"]["reviewable_lines"],
                         BUDGET + 1)
        self.assertTrue(report["review_size"]["over_budget"])

    def test_at_budget_is_silent(self):
        self.write("anneal/data/big.txt", lines(BUDGET))
        self.commit()
        code, report = self.run_json()
        self.assertEqual(code, 0, report)
        self.assertEqual(self.size_warnings(report), [])
        self.assertFalse(report["review_size"]["over_budget"])

    def test_deletions_count(self):
        self.write("anneal/data/old.txt", "")
        self.write("anneal/data/big.txt", lines(BUDGET - 39))
        self.commit()
        _, report = self.run_json()
        self.assertEqual(report["review_size"]["reviewable_lines"],
                         BUDGET + 1)
        self.assertEqual(len(self.size_warnings(report)), 1)

    def test_excluded_files_do_not_warn(self):
        self.write("anneal/Cargo.lock", lines(5 * BUDGET))
        self.write("anneal/tests/cargo-anneal/tests/fixtures/a/Proof.lean",
                   HEADER_LEAN + lines(5 * BUDGET, "--"))
        self.write("anneal/data/small.txt", lines(10))
        self.commit()
        code, report = self.run_json()
        self.assertEqual(code, 0, report)
        self.assertEqual(self.size_warnings(report), [])
        size = report["review_size"]
        self.assertEqual(size["reviewable_lines"], 10)
        self.assertEqual(size["excluded"]["lock"]["lines"], 5 * BUDGET)
        self.assertEqual(size["excluded"]["fixture"]["lines"],
                         5 * BUDGET + HEADER_LEAN.count("\n"))

    def test_findings_keep_their_exit_code(self):
        # A new Python file without a license header is a finding.
        self.write("anneal/ci/bad.py", "X = 1\n")
        self.write("anneal/data/big.txt", lines(BUDGET + 1))
        self.commit()
        code, report = self.run_json()
        self.assertEqual(code, 1)
        self.assertFalse(report["ok"])
        self.assertEqual({f["check"] for f in report["findings"]},
                         {"header"})
        self.assertEqual(len(self.size_warnings(report)), 1)

    def test_review_size_is_not_waivable(self):
        self.write("anneal/data/big.txt", lines(BUDGET + 1))
        self.commit(MESSAGE.replace(
            "Agent-authored-by",
            "Skip-pr-hygiene: review-size -- split later\n"
            "Agent-authored-by"))
        code, report = self.run_json()
        self.assertEqual(code, 1, report)
        self.assertEqual([f["check"] for f in report["findings"]],
                         ["skip-pr-hygiene"])
        self.assertEqual(report["waived_findings"], [])
        self.assertEqual(len(self.size_warnings(report)), 1)

    def test_waiving_another_check_keeps_the_warning(self):
        self.write("anneal/ci/bad.py", "X = 1\n")
        self.write("anneal/data/big.txt", lines(BUDGET + 1))
        self.commit(MESSAGE.replace(
            "Agent-authored-by",
            "Skip-pr-hygiene: header -- generated stub\n"
            "Agent-authored-by"))
        code, report = self.run_json()
        self.assertEqual(code, 0, report)
        self.assertEqual([w["check"] for w in report["waived_findings"]],
                         ["header"])
        self.assertEqual(len(self.size_warnings(report)), 1)

    def test_text_mode(self):
        self.write("anneal/data/big.txt", lines(BUDGET + 1))
        self.commit()
        res = self.run_script()
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertIn("warning: [review-size] ", res.stderr)
        self.assertIn("PR hygiene checks passed.", res.stdout)
        self.assertNotIn("::warning", res.stdout)

    def test_github_actions_annotation(self):
        self.write("anneal/data/big.txt", lines(BUDGET + 1))
        self.commit()
        res = self.run_script(env={"GITHUB_ACTIONS": "true"})
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertIn("::warning title=PR review-size budget::", res.stdout)
        res = self.run_script("--json", env={"GITHUB_ACTIONS": "true"})
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertIn("::warning title=PR review-size budget::", res.stderr)
        json.loads(res.stdout)

    def test_tree_only_mode_has_no_size(self):
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--json"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(res.returncode, 0, res.stdout)
        self.assertNotIn("review_size", json.loads(res.stdout))


if __name__ == "__main__":
    unittest.main()
