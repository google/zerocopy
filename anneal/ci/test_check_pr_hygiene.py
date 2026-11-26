# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `anneal/ci/check_pr_hygiene.py`."""

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
# Built at runtime so this file contains no literal review-round ID.
ROUND_ID = "G2" + "-R3"
SHA_RUST = "8144389c895da997dbdecaa635e41d6a50be6ffd"

HEADER_PY = """\
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""
HEADER_RS = HEADER_PY.replace("# ", "// ").replace("#\n", "//\n")
HEADER_LEAN = HEADER_PY.replace("# ", "-- ").replace("#\n", "--\n")
HEADER_MD = """\
<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->
"""
CRR = (
    "<!-- code-review-rules:begin -->\n"
    "Rules text.\n"
    "<!-- code-review-rules:end -->\n"
)
TRAILER = "Agent-authored-by: AI agent acting on joshlf's behalf"
GOOD_MESSAGE = (
    "[ci] Add a helper\n\n"
    "Add a helper that does one thing well, so callers stop duplicating\n"
    "the logic.\n\n"
    f"{TRAILER}\n"
)
AUTHOR = "Test Author <test@example.com>"


def ambient_env() -> dict[str, str]:
    """The test environment without inputs that change the script's output.

    Under GitHub Actions, an inherited `GITHUB_STEP_SUMMARY` would make
    waiver tests write to the real step summary.
    """
    return {k: v for k, v in os.environ.items()
            if k not in ("GITHUB_STEP_SUMMARY", "PR_TITLE")}


def git(repo: Path, *args: str, env: dict[str, str] | None = None) -> str:
    full_env = {
        **{k: v for k, v in os.environ.items() if not k.startswith("GIT_")},
        "GIT_AUTHOR_NAME": "Test Author",
        "GIT_AUTHOR_EMAIL": "test@example.com",
        "GIT_COMMITTER_NAME": "Test Author",
        "GIT_COMMITTER_EMAIL": "test@example.com",
        "GIT_CONFIG_NOSYSTEM": "1",
        "HOME": str(repo.parent),
        **(env or {}),
    }
    return subprocess.run(
        ["git", "-c", "core.hooksPath=/dev/null", "-c", "init.defaultBranch=main",
         *args],
        cwd=repo, env=full_env, capture_output=True, text=True, check=True,
    ).stdout


class RepoTestCase(unittest.TestCase):
    """Builds a scratch repository with a minimal Anneal tree on `main`."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="anneal-pr-hygiene-")
        self.repo = Path(self._tmp.name) / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q")
        self.write("AGENTS.md", "Root agent instructions.\n")
        self.write("anneal/AGENTS.md", HEADER_MD + "\n# Rules\n\n" + CRR)
        self.write("anneal/.gemini/styleguide.md", "# Style\n\n" + CRR)
        self.write("anneal/docs/existing.md", HEADER_MD + "\n" + "x" * 100
                   + " y\n")
        self.write("anneal/ci/existing.py", HEADER_PY + "\nVALUE = 1\n")
        self.write("anneal/ci/legacy.sh", "echo 1\necho 2\necho 3\necho 4\n")
        self.write("anneal/README.md", "Short readme.\n")
        self.commit("Initial commit")
        git(self.repo, "branch", "base")

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def write(self, rel: str, text: str) -> None:
        path = self.repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def commit(self, message: str = GOOD_MESSAGE, env=None) -> str:
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "--allow-empty", "-m", message, env=env)
        return git(self.repo, "rev-parse", "HEAD").strip()

    def run_check(self, *args: str, base: str | None = "base",
                  env: dict[str, str] | None = None
                  ) -> tuple[int, dict[str, object]]:
        cmd = [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
               str(self.repo), "--json"]
        if base is not None:
            cmd += ["--base", base]
        res = subprocess.run(
            cmd + list(args), capture_output=True, text=True, check=False,
            env={**ambient_env(), **(env or {})},
        )
        return res.returncode, json.loads(res.stdout)

    def findings(self, *args: str, **kw) -> list[dict[str, object]]:
        return self.run_check(*args, **kw)[1]["findings"]

    def assert_finding(self, check: str, needle: str, *args: str,
                       **kw) -> dict[str, object]:
        found = self.findings(*args, **kw)
        for f in found:
            if f["check"] == check and needle in f["message"]:
                return f
        self.fail(f"no {check!r} finding containing {needle!r}: {found}")

    def assert_clean(self, *args: str, **kw) -> dict[str, object]:
        code, report = self.run_check(*args, **kw)
        self.assertEqual(report["findings"], [], report)
        self.assertEqual(code, 0)
        self.assertTrue(report["ok"])
        return report


class CleanChangeTests(RepoTestCase):
    def test_clean_change_passes_and_reports_tuple(self):
        self.write("anneal/ci/helper.py", HEADER_PY + "\n# Short comment.\n"
                   + "X = '" + "y" * 120 + "'\n")
        head = self.commit()
        report = self.assert_clean()
        self.assertEqual(report["schema"], "anneal-pr-hygiene/v1")
        self.assertEqual(report["head"], head)
        self.assertEqual(report["commits"], [head])
        self.assertEqual(report["merge_base"], report["target_base"])

    def test_tree_only_mode_runs_without_base(self):
        report = self.assert_clean(base=None)
        self.assertNotIn("commits", report)

    def test_bad_ref_fails_closed_with_exit_2(self):
        code, report = self.run_check(base="no-such-ref")
        self.assertEqual(code, 2)
        self.assertFalse(report["ok"])
        self.assertIn("error", report)

    def test_empty_flag_values_fail_closed(self):
        for flag in ("--pr-body-file", "--receipt-file", "--expected-author"):
            with self.subTest(flag=flag):
                code, report = self.run_check(flag, "")
                self.assertEqual(code, 2, report)
                self.assertIn("must not be empty", report["error"])

    def test_pr_inputs_require_base(self):
        body = self.repo.parent / "body.md"
        body.write_text("x\n")
        code, _ = self.run_check("--pr-body-file", str(body), base=None)
        self.assertEqual(code, 2)
        code, _ = self.run_check("--expected-author", AUTHOR, base=None)
        self.assertEqual(code, 2)

    def test_text_mode_exit_codes(self):
        self.write("anneal/ci/bad.py", "X = 1\n")
        self.commit()
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--base", "base"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(res.returncode, 1)
        self.assertIn("[header] anneal/ci/bad.py:1", res.stderr)


class CommitMessageTests(RepoTestCase):
    def touch(self) -> None:
        self.write("anneal/docs/note.md", HEADER_MD + "\nA note.\n")

    def test_long_subject(self):
        self.touch()
        self.commit("[ci] " + "Word " * 15 + "\n\n" + TRAILER + "\n")
        self.assert_finding("commit-message", "subject is")

    def test_github_squash_suffix_does_not_count(self):
        self.touch()
        subject = "[ci] " + "a" * 60
        self.commit(f"{subject} (#4321)\n\nBody.\n\n{TRAILER}\n")
        self.assert_clean()

    def test_subject_period_and_missing_blank_line(self):
        self.touch()
        self.commit(f"[ci] Add a thing.\nBody right away.\n\n{TRAILER}\n")
        self.assert_finding("commit-message", "ends with a period")
        self.assert_finding("commit-message", "one blank line")

    def test_wrappable_body_line(self):
        self.touch()
        self.commit("[ci] Add\n\n" + "word " * 16 + "end\n\n" + TRAILER + "\n")
        self.assert_finding("commit-message", "wrap at 72")

    def test_unbreakable_url_code_fence_and_table_are_exempt(self):
        self.touch()
        url = "https://example.com/" + "a" * 70
        self.commit(
            "[ci] Add\n\n"
            f"{url}\n\n"
            "```\n" + "code " * 20 + "\n```\n\n"
            "    " + ("code " * 20).rstrip() + "\n\n"
            "| a | " + "b" * 80 + " |\n\n"
            "Fixes #123\n"
            "Signed-off-by: " + ("Long Name " * 6) + "<x@example.com>\n"
            f"{TRAILER}\n"
        )
        self.assert_clean()

    def test_gherrit_and_review_round_ids(self):
        self.touch()
        self.commit(f"[ci] Add\n\nAddress {ROUND_ID} feedback.\n\n"
                    f"gherrit-pr-id: Gabc\n{TRAILER}\n")
        self.assert_finding("commit-message", "gherrit-pr-id")
        self.assert_finding("commit-message", "review-round ID")

    def test_trailer_may_precede_other_trailers(self):
        self.touch()
        self.commit(f"[ci] Add\n\nBody.\n\n{TRAILER}\n"
                    "Signed-off-by: Test Author <test@example.com>\n")
        self.assert_clean()

    def test_trailer_examples_in_code_blocks_do_not_count(self):
        self.touch()
        self.commit(f"[ci] Add\n\nFor example:\n\n```\n{TRAILER}\n```\n\n"
                    f"{TRAILER}\n")
        self.assert_clean()

    def test_one_trailer_per_user(self):
        self.touch()
        other = TRAILER.replace("joshlf", "someone")
        self.commit(f"[ci] Add\n\nBody.\n\n{TRAILER}\n{other}\n")
        self.assert_clean()

    def test_trailer_outside_final_block(self):
        self.touch()
        self.commit(f"[ci] Add\n\n{TRAILER}\n\nMore prose after.\n")
        self.assert_finding("commit-message", "final trailer block")

    def test_duplicate_trailer(self):
        self.touch()
        self.commit(f"[ci] Add\n\nBody.\n\n{TRAILER}\n{TRAILER}\n")
        self.assert_finding("commit-message", "at most one")

    def test_tab_indented_body_is_measured_expanded(self):
        self.touch()
        self.commit("[ci] Add\n\n- item\n\t" + "word " * 13 + "end\n\n"
                    + TRAILER + "\n")
        self.assert_finding("commit-message", "wrap at 72")

    def test_malformed_trailer(self):
        self.touch()
        self.commit("[ci] Add\n\nBody.\n\n"
                    "Agent-Authored-By: Gemini on joshlf's behalf\n")
        self.assert_finding("commit-message", "malformed trailer")

    def test_qualified_trailer_is_accepted(self):
        self.touch()
        self.commit(f"[ci] Add\n\nBody.\n\n{TRAILER} (content only)\n")
        self.assert_clean()

    def test_record_separators_and_quoted_paths_in_commits(self):
        self.write('anneal/docs/odd"name.md', HEADER_MD)
        self.commit("[ci] Add.\n\nBody with \x1e separator.\n")
        code, report = self.run_check()
        self.assertEqual(code, 1, report)
        self.assertTrue(any("ends with a period" in f["message"]
                            for f in report["findings"]))

    def test_bot_like_authors_are_checked_unless_skipped(self):
        self.write("anneal/Cargo.lock", "# lock\n")
        long_line = "Updates `x` from 3.23.2 to 3.24.1 " + "word " * 10
        self.commit(f"Bump x.\n\n{long_line}\n", env={
            "GIT_AUTHOR_NAME": "dependabot[bot]",
            "GIT_AUTHOR_EMAIL":
                "49699333+dependabot[bot]@users.noreply.github.com"})
        # Commit metadata is author-controlled, so a `[bot]` name alone
        # never skips the checks.
        self.assert_finding("commit-message", "ends with a period")
        code, report = self.run_check("--skip-commit-messages")
        self.assertEqual(code, 0, report)
        self.assertTrue(any("--skip-commit-messages" in w["message"]
                            for w in report["warnings"]))
        self.assert_finding("commit-author", "author is",
                            "--skip-commit-messages",
                            "--expected-author", AUTHOR)

    def test_commits_outside_anneal_are_skipped(self):
        self.write("zerocopy/src/lib.rs", "fn f() {}\n")
        self.commit("not our conventions at all, a very long subject line "
                    "that keeps going.")
        code, report = self.run_check()
        self.assertEqual(code, 0, report)
        self.assertIn("skipped", report["warnings"][0]["message"])

    def test_every_commit_in_range_is_checked(self):
        self.touch()
        self.commit()
        self.write("anneal/docs/note2.md", HEADER_MD + "\nB.\n")
        self.commit("[ci] Second commit.\n\nBody.\n\n" + TRAILER + "\n")
        self.assert_finding("commit-message", "ends with a period")

    def test_expected_author(self):
        self.touch()
        self.commit()
        self.assert_clean("--expected-author", AUTHOR)
        f = self.assert_finding("commit-author", "author is",
                                "--expected-author", "J <j@example.com>")
        self.assertIn("Test Author", f["message"])


class DiffTests(RepoTestCase):
    def test_diff_check_trailing_whitespace(self):
        self.write("anneal/ci/existing.py", HEADER_PY + "\nVALUE = 2   \n")
        self.commit()
        self.assert_finding("diff-check", "trailing whitespace")

    def test_vendor_and_non_anneal_paths_are_out_of_scope(self):
        self.write("anneal/vendor/lean-miri/x.lean", "x   \n" + "-- " + "w " * 60
                   + "\n")
        self.write("zerocopy/src/lib.rs", "// " + "w " * 60 + "\n")
        self.commit()
        self.assert_clean()

    def test_anneal_integration_paths_are_in_scope(self):
        self.write(".github/workflows/anneal-extra.yml", "on: push\n")
        self.write("zerocopy/proofs/05_x/Spec.lean", HEADER_LEAN
                   + "\n-- " + "word " * 17 + "end\n")
        self.commit()
        found = {(f["check"], f["path"]) for f in self.findings()}
        self.assertIn(("header", ".github/workflows/anneal-extra.yml"), found)
        self.assertIn(("wrap", "zerocopy/proofs/05_x/Spec.lean"), found)

    def test_new_file_header(self):
        self.write("anneal/ci/new.py", "X = 1\n")
        self.commit()
        self.assert_finding("header", "does not open with the Fuchsia")

    def test_header_variants_and_exemptions(self):
        self.write("anneal/ci/a.py", "#!/usr/bin/env python3\n#\n" + HEADER_PY)
        self.write("anneal/src/b.rs", HEADER_RS)
        self.write("anneal/theory/C.lean", HEADER_LEAN)
        self.write("anneal/docs/d.md", HEADER_MD)
        self.write("anneal/skills/x/SKILL.md", "---\nname: x\n---\n")
        self.write("anneal/data.json", "{}\n")
        self.commit()
        self.assert_clean()

    def test_header_must_be_the_leading_comment(self):
        prose = "\n".join(ln[2:] for ln in HEADER_PY.splitlines())
        self.write("anneal/ci/late.py", 'X = 1\n"""\n' + prose + '\n"""\n')
        self.write("anneal/docs/late.md", "# Title\n\n" + HEADER_MD)
        self.commit()
        paths = {f["path"] for f in self.findings() if f["check"] == "header"}
        self.assertEqual(paths, {"anneal/ci/late.py", "anneal/docs/late.md"})

    def test_header_comment_must_be_closed_and_contain_the_text(self):
        body = HEADER_MD.replace("<!-- Copyright", "Copyright")
        self.write("anneal/docs/a.md", "<!-- --> " + body)
        self.write("anneal/docs/b.md", HEADER_MD.replace(" -->", ""))
        self.write("anneal/docs/c.md", "#! title\n" + HEADER_MD)
        self.write("anneal/src/d.rs", "#![no_std]\n" + HEADER_RS)
        one_line = " ".join(body.replace(" -->", "").split())
        self.write("anneal/docs/e.md", "<!-- --> " + one_line + "\n")
        self.commit()
        paths = {f["path"] for f in self.findings() if f["check"] == "header"}
        self.assertEqual(paths, {"anneal/docs/a.md", "anneal/docs/b.md",
                                 "anneal/docs/c.md", "anneal/src/d.rs",
                                 "anneal/docs/e.md"})

    def test_header_year_bound_ignores_commit_dates(self):
        self.write("anneal/ci/future.py", HEADER_PY.replace("2026", "2090"))
        self.commit(env={"GIT_COMMITTER_DATE": "2090-01-01T00:00:00Z",
                         "GIT_AUTHOR_DATE": "2090-01-01T00:00:00Z"})
        self.assert_finding("header", "plausible creation year")

    def test_header_year_must_be_plausible(self):
        self.write("anneal/ci/future.py", HEADER_PY.replace("2026", "2999"))
        self.commit()
        self.assert_finding("header", "plausible creation year")

    def test_renamed_file_is_not_new(self):
        # Neither file carries a header that would satisfy a new-file check.
        git(self.repo, "mv", "anneal/ci/legacy.sh", "anneal/ci/moved.sh")
        self.write("anneal/ci/moved.sh", "echo 1\necho 2\necho 3\necho 4\necho 5\n")
        self.commit()
        self.assert_clean()

    def test_moved_file_keeps_its_original_header(self):
        git(self.repo, "mv", "anneal/ci/existing.py", "anneal/ci/moved.py")
        self.commit()
        self.assert_clean()


class WrapTests(RepoTestCase):
    LONG = "word " * 17 + "end"

    def test_markdown_prose_over_80(self):
        self.write("anneal/docs/existing.md", HEADER_MD + "\n" + self.LONG
                   + "\n")
        self.commit()
        f = self.assert_finding("wrap", "wrap prose at 80")
        self.assertEqual(f["path"], "anneal/docs/existing.md")

    def test_markdown_exemptions(self):
        url = "https://example.com/" + "a" * 75
        self.write("anneal/docs/new.md", HEADER_MD + (
            "\n# A heading that is long " + "h" * 70 + "\n\n"
            "| a | b |\n|---|---|\n| " + "c " * 50 + "| d |\n\n"
            "a | b\n--- | ---\n" + "c " * 50 + "| d\n\n"
            "```\n" + "code " * 30 + "end\n```\n\n"
            f"See\n{url}\n\n"
            "- `" + "x" * 76 + "`\n\n"
            "$$a + b + " + "c + " * 30 + "$$\n\n"
            "[ref]: " + url + "\n\n"
            "<img src=\"" + url + "\">\n"
        ))
        self.commit()
        self.assert_clean()

    def test_front_matter_is_exempt(self):
        self.write("anneal/skills/s/SKILL.md",
                   "---\ndescription: " + "d " * 60 + "e\n---\n\nShort.\n")
        self.commit()
        self.assert_clean()

    def test_unchanged_long_line_is_not_flagged(self):
        self.write("anneal/docs/existing.md",
                   (self.repo / "anneal/docs/existing.md").read_text()
                   + "\nShort addition.\n")
        self.commit()
        self.assert_clean()

    def test_rust_comment_lean_comment_and_python_comment(self):
        self.write("anneal/src/a.rs", HEADER_RS + "\n/// " + self.LONG
                   + "\nfn f() { let s = \"" + "q" * 100 + "\"; }\n")
        self.write("anneal/theory/B.lean", HEADER_LEAN
                   + "\n/-- Doc.\n" + self.LONG + "\n-/\ndef x := 1\n")
        self.write("anneal/ci/c.py", HEADER_PY + "\n# " + self.LONG + "\n")
        self.commit()
        paths = {f["path"] for f in self.findings() if f["check"] == "wrap"}
        self.assertEqual(paths, {"anneal/src/a.rs", "anneal/theory/B.lean",
                                 "anneal/ci/c.py"})

    def test_code_strings_directives_and_doc_fences_are_not_prose(self):
        self.write("anneal/src/a.rs", HEADER_RS + (
            "\n//@ fail(capture): \"" + "m " * 60 + "\"\n"
            "/// ```\n/// " + ("let x = 1; " * 10).rstrip() + "\n/// ```\nfn f() {}\n"
        ))
        self.write("anneal/ci/c.py", HEADER_PY + (
            '\nS = """\n# ' + self.LONG + '\n"""\n'
        ))
        self.write("anneal/x.nix", HEADER_PY + (
            "\n{ s = ''\n    # " + self.LONG + "\n  ''; }\n"
        ))
        self.commit()
        self.assert_clean()

    def test_package_readme_keeps_one_line_per_paragraph(self):
        self.write("anneal/README.md", self.LONG + " " + self.LONG + "\n")
        self.commit()
        self.assert_clean()

    def test_indented_license_header_is_verbatim_text(self):
        indented = "".join("        " + ln + "\n"
                           for ln in HEADER_PY.splitlines())
        self.write("anneal/ci/gen.sh", HEADER_PY
                   + "\ncat <<'EOF'\n" + indented + "EOF\n")
        self.commit()
        self.assert_clean()

    def test_split_code_span_is_a_warning_only(self):
        self.write("anneal/docs/new.md", HEADER_MD
                   + "\nThe `foo\nbar` span is split.\n")
        self.commit()
        code, report = self.run_check()
        self.assertEqual(code, 0, report)
        self.assertTrue(any("split across" in w["message"]
                            for w in report["warnings"]))

    def test_review_round_id_in_headings_and_tables(self):
        self.write("anneal/docs/new.md", HEADER_MD + (
            f"\n## Changes from {ROUND_ID}\n\n| a | {ROUND_ID} |\n|---|---|\n\n"
            f"```\n{ROUND_ID}\n```\n"))
        self.commit()
        found = [f["line"] for f in self.findings()
                 if f["check"] == "review-round-id"]
        self.assertEqual(found, [9, 11])

    def test_inline_triple_backtick_span_is_not_a_fence(self):
        self.write("anneal/docs/new.md", HEADER_MD + (
            f"\n```x``` is inline.\n\nSee {ROUND_ID}.\n"))
        self.commit()
        found = [f["line"] for f in self.findings()
                 if f["check"] == "review-round-id"]
        self.assertEqual(found, [11])

    def test_review_round_id_in_comment_but_not_string(self):
        self.write("anneal/ci/c.py", HEADER_PY
                   + f'\n# Fixes {ROUND_ID}.\nID = "{ROUND_ID}-01"\n')
        self.commit()
        found = [f for f in self.findings() if f["check"] == "review-round-id"]
        self.assertEqual([f["line"] for f in found], [9])


class WrapUnitTests(unittest.TestCase):
    def test_wrap_violation(self):
        self.assertFalse(cph.wrap_violation("a" * 80, 0, 80))
        self.assertTrue(cph.wrap_violation("a " * 41, 0, 80))
        # Overflowing unit starts the line.
        self.assertFalse(cph.wrap_violation("// " + "x" * 90, 3, 80))
        # Overflowing unit would not fit on a continuation line.
        self.assertFalse(cph.wrap_violation("see " + "x" * 81, 0, 80))
        # Code spans are unbreakable; this one fits on its own line.
        self.assertTrue(cph.wrap_violation("see `" + "x " * 38 + "`", 0, 80))

    def test_units_keep_code_spans_whole(self):
        text = "a `b c` d"
        self.assertEqual([text[s:e] for s, e in cph.units(text)],
                         ["a", "`b c`", "d"])
        self.assertEqual(cph.unmatched_backtick("x `y"), 1)
        self.assertIsNone(cph.unmatched_backtick("`` a ` b ``"))


class TrustedCitationTests(RepoTestCase):
    def write_trusted(self, body: str, path="anneal/trusted/lean/T.lean"):
        header = HEADER_RS if path.endswith(".rs") else HEADER_LEAN
        comment = "//" if path.endswith(".rs") else "--"
        self.write(path, header + "\n" + body.replace("-- ", comment + " "))
        self.commit()

    def test_unpinned_branch_link(self):
        self.write_trusted("-- https://github.com/rust-lang/rust/blob/master/"
                           "x.rs\n")
        self.assert_finding("trusted-citation", "full 40-hex")

    def test_rendered_reference_html(self):
        self.write_trusted("-- https://doc.rust-lang.org/reference/x.html\n")
        self.assert_finding("trusted-citation", "unpinned rendered docs")

    def test_unresolved_abbreviated_sha(self):
        self.write_trusted("-- See `rust-lang/rust` `8144389c` for this.\n")
        self.assert_finding("trusted-citation", "abbreviated upstream SHA")

    def test_pinned_and_resolved_citations_pass(self):
        self.write_trusted(
            f"-- `rust-lang/rust` `{SHA_RUST}`\n-- and rust-lang/rust@8144389c.\n"
            f"-- https://github.com/rust-lang/reference/blob/{SHA_RUST}/a.md\n",
            path="anneal/trusted/rustc-capture/src/x.rs",
        )
        self.assert_clean()

    def test_untrusted_paths_are_not_linted(self):
        self.write("anneal/theory/T.lean", HEADER_LEAN
                   + "\n-- https://doc.rust-lang.org/reference/x.html\n")
        self.commit()
        self.assert_clean()

    def test_new_trusted_file_without_sha_warns(self):
        self.write_trusted("def x := 1\n")
        code, report = self.run_check()
        self.assertEqual(code, 0)
        self.assertTrue(any(w["check"] == "trusted-citation"
                            for w in report["warnings"]))


class TreeCheckTests(RepoTestCase):
    def test_agents_budget(self):
        self.write("anneal/sub/AGENTS.md", "x" * 32000)
        self.commit()
        self.assert_finding("agents-budget", "shared instruction budget",
                            base=None)

    def test_agents_budget_reserve_env(self):
        self.write("anneal/sub/AGENTS.md", "x" * 31000)
        self.commit()
        self.assert_clean(base=None, env={"GLOBAL_AGENTS_BYTES": "0"})
        self.assert_finding("agents-budget", "budget", base=None,
                            env={"GLOBAL_AGENTS_BYTES": "1500"})
        self.assert_finding("agents-budget", "invalid", base=None,
                            env={"GLOBAL_AGENTS_BYTES": "1e3"})

    def test_agents_outside_anneal_are_not_counted(self):
        self.write("zerocopy/AGENTS.md", "x" * 32000)
        self.commit()
        self.assert_clean(base=None)

    def test_crr_mirror_drift(self):
        self.write("anneal/.gemini/styleguide.md",
                   "# Style\n\n" + CRR.replace("Rules", "Rulez"))
        self.commit()
        self.assert_finding("code-review-rules-parity", "byte-identical",
                            base=None)

    def test_crr_missing_marker(self):
        self.write("anneal/.gemini/styleguide.md", "# Style\n\nNo markers.\n")
        self.commit()
        self.assert_finding("code-review-rules-parity", "expected one",
                            base=None)


class PrBodyTests(RepoTestCase):
    MESSAGE = (
        "[ci] Add a helper\n\n"
        "Add a helper that does one thing well, so callers stop duplicating\n"
        "the logic.\n\n"
        "- First item wraps across\n  two lines.\n\n"
        "```\nkeep   this\n```\n\n"
        "Fixes #12\n"
        f"{TRAILER}\n"
    )
    EXPECTED = (
        "Add a helper that does one thing well, so callers stop duplicating "
        "the logic.\n\n"
        "- First item wraps across two lines.\n\n"
        "```\nkeep   this\n```\n\n"
        "Fixes #12\n\n"
        "*Authored by an AI agent acting on joshlf's behalf.*\n"
    )

    def setUp(self) -> None:
        super().setUp()
        self.write("anneal/docs/note.md", HEADER_MD + "\nA note.\n")
        self.commit(self.MESSAGE)

    def body_file(self, text: str) -> str:
        path = self.repo.parent / "body.md"
        path.write_bytes(text.encode())
        return str(path)

    def test_emit_pr_body(self):
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--emit-pr-body"],
            capture_output=True, text=True, check=True,
        )
        self.assertEqual(res.stdout, self.EXPECTED)

    def test_matching_body_and_title_pass_with_crlf(self):
        self.assert_clean(
            "--pr-body-file", self.body_file(
                self.EXPECTED.replace("\n", "\r\n")),
            "--pr-title", "[ci] Add a helper")

    def test_mismatched_body(self):
        f = self.assert_finding(
            "pr-body", "first difference at line 1",
            "--pr-body-file", self.body_file("## Summary\n\nStuff.\n"))
        self.assertIn("## Summary", f["message"])

    def test_missing_disclosure(self):
        self.assert_finding(
            "pr-body", "end of body", "--pr-body-file",
            self.body_file(self.EXPECTED.rsplit("\n\n", 1)[0] + "\n"))

    def test_mismatched_title(self):
        self.assert_finding("pr-title", "differs", "--pr-title", "Other")

    def test_multi_commit_is_skipped_with_warning(self):
        self.write("anneal/docs/note2.md", HEADER_MD + "\nB.\n")
        self.commit()
        code, report = self.run_check("--pr-body-file", self.body_file("x"))
        self.assertEqual(code, 0, report)
        self.assertTrue(any(w["check"] == "pr-body"
                            for w in report["warnings"]))


class UnwrapUnitTests(unittest.TestCase):
    def test_qualifiers_and_blockquotes(self):
        body = ("> quoted line\n> continues\n\n"
                f"{TRAILER} (content only)\n")
        # A content-only trailer means the agent did not write the message,
        # so the description carries no notice.
        self.assertEqual(cph.commit_body_to_pr_body(body),
                         "> quoted line continues\n")
        body = f"Text.\n\n{TRAILER} (commit message only)\n"
        self.assertEqual(
            cph.commit_body_to_pr_body(body),
            "Text.\n\n*Authored by an AI agent acting on joshlf's behalf.*\n")

    def test_inline_triple_backtick_line_is_not_a_fence(self):
        body = (f"```x``` starts this line.\n\nWrapped\nprose.\n\n{TRAILER}\n")
        self.assertEqual(
            cph.commit_body_to_pr_body(body),
            "```x``` starts this line.\n\nWrapped prose.\n\n"
            "*Authored by an AI agent acting on joshlf's behalf.*\n")
        self.assertEqual(
            cph.commit_body_to_pr_body("Some prose\n```x``` continues.\n"),
            "Some prose ```x``` continues.\n")

    def test_hard_breaks_headings_and_empty(self):
        self.assertEqual(cph.commit_body_to_pr_body(""), "")
        body = "# Head\nline one  \nline two\nthree\n"
        self.assertEqual(cph.commit_body_to_pr_body(body),
                         "# Head\nline one  \nline two three\n")


class ReceiptTests(RepoTestCase):
    def setUp(self) -> None:
        super().setUp()
        self.write("anneal/trusted/lean/A.lean", HEADER_LEAN)
        self.write("anneal/trusted/lean/B.lean", HEADER_LEAN)
        self.write("anneal/ci/tool.py", HEADER_PY)
        self.write("anneal/docs/guide.md", HEADER_MD)
        self.commit()

    def receipt(self, text: str) -> str:
        path = self.repo.parent / "receipt.md"
        path.write_text(text, encoding="utf-8")
        return str(path)

    def footer(self) -> str:
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--base", "base", "--emit-receipt-footer"],
            capture_output=True, text=True, check=True,
        )
        return res.stdout

    def footer_data(self) -> dict[str, object]:
        m = cph.RECEIPT_FOOTER_RE.search(self.footer())
        return json.loads(m.group(1))

    def good(self, data: dict[str, object] | None = None) -> str:
        footer = (self.footer() if data is None else
                  f"<!-- anneal-receipt:v1 {json.dumps(data)} -->\n")
        return ("### Human review surface\n\n"
                "- `anneal/trusted/lean/{A,B}.lean`: new definitions.\n\n"
                + footer)

    def test_emitted_footer_binds_tuple_and_surface(self):
        data = self.footer_data()
        self.assertEqual(data["head"], git(self.repo, "rev-parse",
                                           "HEAD").strip())
        self.assertEqual(data["tree"], git(self.repo, "rev-parse",
                                           "HEAD^{tree}").strip())
        self.assertEqual(data["human_review_surface"], [
            "anneal/ci/tool.py", "anneal/trusted/lean/A.lean",
            "anneal/trusted/lean/B.lean"])
        self.assert_clean("--receipt-file", self.receipt(self.good()))

    def test_footer_count_json_and_keys(self):
        for text, needle in (
            ("### Human review surface\n\nnone\n", "0 `anneal-receipt:`"),
            (self.good() + self.footer(), "2 `anneal-receipt:`"),
            ("Human review surface\n<!-- anneal-receipt:v1 {nope} -->",
             "not valid JSON"),
        ):
            with self.subTest(needle=needle):
                self.assert_finding("receipt", needle,
                                    "--receipt-file", self.receipt(text))
        data = self.footer_data()
        data["extra"] = 1
        self.assert_finding("receipt", "exactly the keys",
                            "--receipt-file", self.receipt(self.good(data)))

    def test_extra_markers_duplicates_and_hidden_prose(self):
        good = self.good()
        for extra in ("<!-- anneal-receipt:v1 not-json -->\n",
                      "<!-- anneal-receipt:v1 [] -->\n",
                      "<!-- anneal-receipt:v2 {} -->\n"):
            with self.subTest(extra=extra):
                self.assert_finding("receipt", "2 `anneal-receipt:` marker",
                                    "--receipt-file",
                                    self.receipt(good + extra))
        # Mentioning the footer in prose is fine.
        self.assert_clean("--receipt-file", self.receipt(
            good + "The `anneal-receipt:v1` footer is generated.\n"))
        footer = self.footer()
        head = self.footer_data()["head"]
        dup = footer.replace('"target_base": ',
                             f'"target_base": "{head}", "target_base": ', 1)
        self.assert_finding("receipt", "duplicate key",
                            "--receipt-file", self.receipt(
                                "### Human review surface\n\n" + dup))
        hidden = "<!-- Human review surface -->\n" + footer
        self.assert_finding("receipt", "visible `Human review",
                            "--receipt-file", self.receipt(hidden))

    def test_footer_escapes_comment_close(self):
        footer = cph.receipt_footer("a" * 40, "a" * 40, "b" * 40, "c" * 40,
                                    ["anneal/ci/x-->y.py"])
        self.assertEqual(footer.count("-->"), 1)
        data = json.loads(cph.RECEIPT_FOOTER_RE.search(footer).group(1))
        self.assertEqual(data["human_review_surface"], ["anneal/ci/x-->y.py"])

    def test_shas_must_be_full_and_current(self):
        data = self.footer_data()
        data["head"] = data["head"][:12]
        self.assert_finding("receipt", "`head` must be a full 40-hex",
                            "--receipt-file", self.receipt(self.good(data)))
        data = self.footer_data()
        data["tree"] = "a" * 40
        self.assert_finding("receipt", "footer `tree` is `aaaaaaaaaaaa`",
                            "--receipt-file", self.receipt(self.good(data)))
        data = self.footer_data()
        data["target_base"], data["head"] = data["head"], data["target_base"]
        found = [f["message"] for f in self.findings(
            "--receipt-file", self.receipt(self.good(data)))]
        self.assertTrue(any("footer `head`" in m for m in found), found)
        self.assertTrue(any("footer `target_base`" in m for m in found), found)

    def test_surface_must_be_complete_and_real(self):
        data = self.footer_data()
        data["human_review_surface"].remove("anneal/ci/tool.py")
        f = self.assert_finding("receipt", "omits",
                                "--receipt-file", self.receipt(self.good(data)))
        self.assertIn("anneal/ci/tool.py", f["message"])
        data = self.footer_data()
        data["human_review_surface"] += ["anneal/ci/", "anneal/docs/other.md"]
        f = self.assert_finding("receipt", "does not change",
                                "--receipt-file", self.receipt(self.good(data)))
        self.assertIn("anneal/ci/", f["message"])
        # Listing a changed path outside the review surface is allowed.
        data = self.footer_data()
        data["human_review_surface"].append("anneal/docs/guide.md")
        self.assert_clean("--receipt-file", self.receipt(self.good(data)))
        data["human_review_surface"] = "anneal/ci/tool.py"
        self.assert_finding("receipt", "must be a list",
                            "--receipt-file", self.receipt(self.good(data)))

    def test_prose_block_is_still_required(self):
        text = self.good().replace("### Human review surface", "### Notes")
        self.assert_finding("receipt", "lacks a visible `Human review",
                            "--receipt-file", self.receipt(text))

    def test_emit_footer_requires_base(self):
        code, report = self.run_check("--emit-receipt-footer", base=None)
        self.assertEqual(code, 2, report)


class HardeningTests(RepoTestCase):
    """Inputs that once hid content from, or confused, the checks."""

    LONG = "word " * 17 + "end"

    def test_added_line_resembling_a_patch_header(self):
        self.write("anneal/docs/existing.md", HEADER_MD + "\n++ not a header\n"
                   + self.LONG + "\n")
        self.commit()
        f = self.assert_finding("wrap", "wrap prose at 80")
        self.assertEqual(f["line"], 10)

    def test_path_with_spaces_and_quotes(self):
        self.write("anneal/docs/my note.md", self.LONG + "\n")
        self.write('anneal/docs/odd"name.md', "x\n")
        self.write('anneal/docs/my "odd" note.md', "x\n")
        self.commit()
        found = self.findings()
        self.assertIn(("header", "anneal/docs/my note.md"),
                      {(f["check"], f["path"]) for f in found})
        self.assertIn(("wrap", "anneal/docs/my note.md"),
                      {(f["check"], f["path"]) for f in found})
        self.assertIn(("header", 'anneal/docs/odd"name.md'),
                      {(f["check"], f["path"]) for f in found})
        self.assertIn(("header", 'anneal/docs/my "odd" note.md'),
                      {(f["check"], f["path"]) for f in found})

    def test_gitattributes_cannot_hide_content(self):
        self.write(".gitattributes", "*.py -diff\n* whitespace=-trailing-space\n")
        self.write("anneal/ci/new.py", "# " + self.LONG + "   \n")
        self.commit()
        checks = {f["check"] for f in self.findings()}
        self.assertTrue({"header", "wrap", "diff-check"} <= checks, checks)

    def test_binary_looking_content_is_still_checked(self):
        self.write("anneal/docs/nul.md", HEADER_MD + "\x00\n" + self.LONG
                   + "\n")
        self.commit()
        self.assert_finding("wrap", "wrap prose at 80")

    def test_ambient_git_config_and_env_are_ignored(self):
        cfg = self.repo.parent / "evil.gitconfig"
        cfg.write_text("[core]\n\twhitespace = -trailing-space\n"
                       "[diff]\n\trelative = true\n")
        self.write("anneal/ci/existing.py", HEADER_PY + "\nVALUE = 2   \n")
        self.commit()
        self.assert_finding("diff-check", "trailing whitespace", env={
            "GIT_CONFIG_GLOBAL": str(cfg), "HOME": str(self.repo.parent),
            "GIT_DIR": "/nonexistent",
        })

    def test_deletions_do_not_widen_diff_check(self):
        git(self.repo, "rm", "-q", "anneal/docs/existing.md")
        self.write("anneal/vendor/lean-miri/x.lean", "x   \n")
        self.commit()
        self.assert_clean()

    def test_empty_new_file_needs_header(self):
        self.write("anneal/ci/empty.py", "")
        self.commit()
        self.assert_finding("header", "does not open with")

    def test_python_triple_quotes_in_strings_and_docstrings(self):
        self.write("anneal/ci/q.py", HEADER_PY + (
            "\nQ = ('\"\"\"', \"'''\")\n# " + self.LONG + "\n"
            'def f():\n    """Doc.\n\n    # ' + self.LONG + '\n    """\n'
        ))
        self.commit()
        found = [f["line"] for f in self.findings() if f["check"] == "wrap"]
        self.assertEqual(found, [10])

    def test_form_feed_does_not_shift_lines(self):
        self.write("anneal/ci/ff.py", HEADER_PY + '\nSEP = "\x0c"\n# '
                   + self.LONG + "\n")
        self.commit()
        found = [f["line"] for f in self.findings() if f["check"] == "wrap"]
        self.assertEqual(found, [10])

    def test_markdown_indented_code_block_spans_lines(self):
        self.write("anneal/docs/existing.md", HEADER_MD + "\nText:\n\n    "
                   + self.LONG + "\n    " + self.LONG + "\n\nAfter.\n")
        self.commit()
        self.assert_clean()

    def test_rust_string_literals_are_not_comments(self):
        self.write("anneal/src/s.rs", HEADER_RS + (
            '\nconst A: &str = r#"\n// ' + self.LONG + '\n"#;\n'
            'const B: &str = "\n// ' + self.LONG + '\n";\n'
            "fn f<'a>(x: &'a str) -> char { '\"' }\n// " + self.LONG + "\n"
            'const C: &str = r"C:\\";\n// ' + self.LONG + '\n'
            'const D: &CStr = cr#"a"b"#;\n'
            "// " + self.LONG + "\n"
        ))
        self.commit()
        found = [f["line"] for f in self.findings() if f["check"] == "wrap"]
        self.assertEqual(found, [16, 18, 20])

    def test_lean_char_literal_does_not_open_a_string(self):
        self.write("anneal/theory/C.lean", HEADER_LEAN + (
            "\ndef c := '\"' /- Start of a block comment\n" + self.LONG
            + "\n-/\n"
        ))
        self.commit()
        found = [f["line"] for f in self.findings() if f["check"] == "wrap"]
        self.assertEqual(found, [10])

    def test_pinned_link_with_fragment_or_punctuation(self):
        url = f"https://github.com/rust-lang/rust/commit/{SHA_RUST}"
        self.write("anneal/trusted/lean/T.lean", HEADER_LEAN
                   + f"\n-- See {url}.\n-- And {url}#diff-abc, too.\n")
        self.commit()
        self.assert_clean()

    def test_crr_markers_on_one_line(self):
        one = "<!-- code-review-rules:begin --><!-- code-review-rules:end -->\n"
        self.write("anneal/AGENTS.md", HEADER_MD + one)
        self.write("anneal/.gemini/styleguide.md", one)
        self.commit()
        self.assert_finding("code-review-rules-parity", "expected one",
                            base=None)


class ReviewSurfaceTests(RepoTestCase):
    def surface(self) -> list[str]:
        return self.run_check()[1]["human_review_surface"]

    def test_renames_and_deletions_count_their_sources(self):
        self.write("anneal/trusted/lean/A.lean", HEADER_LEAN)
        self.write("anneal/trusted/lean/D.lean", HEADER_LEAN + "-- d\n")
        self.commit()
        git(self.repo, "branch", "-f", "base", "HEAD")
        git(self.repo, "mv", "anneal/trusted/lean/A.lean",
            "anneal/docs/A.lean")
        git(self.repo, "rm", "-q", "anneal/trusted/lean/D.lean")
        self.commit()
        self.assertEqual(self.surface(), ["anneal/trusted/lean/A.lean",
                                          "anneal/trusted/lean/D.lean"])

    def test_trust_tier_edits_anywhere(self):
        self.write("anneal/theory/T.lean", HEADER_LEAN
                   + "-- anneal-trust-tier: vetted\n")
        self.write("zerocopy/proofs/01_x/Proof.lean", HEADER_LEAN
                   + "-- anneal-trust-tier: vetted\n")
        self.write("anneal/theory/U.lean", HEADER_LEAN)
        self.commit()
        self.assertEqual(self.surface(), ["anneal/theory/T.lean",
                                          "zerocopy/proofs/01_x/Proof.lean"])
        git(self.repo, "branch", "-f", "base", "HEAD")
        self.write("anneal/theory/T.lean", HEADER_LEAN)
        self.write("anneal/theory/U.lean", HEADER_LEAN + "-- plain\n")
        self.commit()
        self.assertEqual(self.surface(), ["anneal/theory/T.lean"])
        git(self.repo, "branch", "-f", "base", "HEAD")
        git(self.repo, "rm", "-q", "zerocopy/proofs/01_x/Proof.lean")
        self.commit()
        self.assertEqual(self.surface(), ["zerocopy/proofs/01_x/Proof.lean"])

    def test_proof_unit_specs_and_requests(self):
        self.write("zerocopy/proofs/05_x/Spec.lean", HEADER_LEAN)
        self.write("zerocopy/proofs/05_x/request.json", "{}\n")
        self.write("zerocopy/proofs/05_x/Proof.lean", HEADER_LEAN)
        self.commit()
        self.assertEqual(self.surface(), ["zerocopy/proofs/05_x/Spec.lean",
                                          "zerocopy/proofs/05_x/request.json"])

    def test_review_surface_categories(self):
        for path in (".gemini/styleguide.md", "anneal/.claude/x.json",
                     "zerocopy/.vscode/settings.json", "anneal/AGENTS.md",
                     "anneal/sub/AGENTS.override.md", "anneal/vendor/x.lean",
                     "anneal/trusted/lean/lake-manifest.json",
                     ".github/workflows/anneal.yml", "skills/x/SKILL.md",
                     "anneal/docs/trust-model.md", "rust-toolchain.toml",
                     "anneal/docs/rustc-workarounds.md",
                     "zerocopy/proofs/01_x/Spec.lean",
                     "zerocopy/proofs/01_x/request.json",
                     "zerocopy/proofs/01_x/SpecHelpers.lean",
                     "ci/checks.toml", ".cargo", "anneal/.cargo",
                     ".gitmodules", "anneal/.gitmodules",
                     "anneal/theory/bundle-manifest.json"):
            self.assertTrue(cph.is_hrs_path(path), path)
        for path in ("anneal/docs/guide.md", "anneal/theory/T.lean",
                     "zerocopy/src/lib.rs", "zerocopy/proofs/01_x/Proof.lean"):
            self.assertFalse(cph.is_hrs_path(path), path)
        self.assertTrue(cph.is_hrs_path("zerocopy/proofs/01_x/Proof.lean",
                                        trust_tier_changed=True))
        for path in (".claude", "anneal/.gemini", ".vscode"):
            self.assertTrue(cph.is_hrs_path(path), path)

    def test_single_hyphen_lines_are_not_trust_tier_directives(self):
        self.write("anneal/theory/V.lean", HEADER_LEAN
                   + "/-\n- anneal-trust-tier: prose\n-/\n")
        self.commit()
        git(self.repo, "branch", "-f", "base", "HEAD")
        self.write("anneal/theory/V.lean", HEADER_LEAN + "/-\n-/\n")
        self.commit()
        self.assertEqual(self.surface(), [])


def waiver_message(*waivers: str, body: str = "") -> str:
    """A clean commit message whose final trailer block holds `waivers`."""
    trailers = "".join(f"{w}\n" for w in waivers)
    return (
        "[ci] Add a generated note\n\n"
        "Add a note whose long line comes from a generator.\n\n"
        f"{body}{trailers}{TRAILER}\n"
    )


WAIVE_WRAP = "Skip-pr-hygiene: wrap -- Generated text keeps source lines."
# Line 9 of the note: `HEADER_MD` is seven lines, then a blank line.
LONG_LINE = ("word " * 20).rstrip() + "\n"


class WaiverTests(RepoTestCase):
    def add_long_line(self) -> None:
        self.write("anneal/docs/note.md", HEADER_MD + "\n" + LONG_LINE)

    def amend(self, message: str) -> str:
        """Rewrite the tip commit, as an author revising a waiver would."""
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "--amend", "--allow-empty", "-m",
            message)
        return git(self.repo, "rev-parse", "HEAD").strip()

    def skip_findings(self, report: dict[str, object]) -> list[str]:
        return [f["message"] for f in report["findings"]
                if f["check"] == "skip-pr-hygiene"]

    def test_valid_waiver_moves_findings_and_records_opt_out(self):
        self.add_long_line()
        head = self.commit(waiver_message(WAIVE_WRAP))
        report = self.assert_clean()
        self.assertEqual(
            [(w["check"], w["path"], w["line"], w["reason"])
             for w in report["waived_findings"]],
            [("wrap", "anneal/docs/note.md", 9,
              "Generated text keeps source lines.")])
        self.assertEqual(report["opt_outs"], [{
            "checks": ["wrap"],
            "reason": "Generated text keeps source lines.",
            "commit": head,
            "line": 5,
        }])

    def test_clean_run_reports_empty_waiver_lists(self):
        self.add_long_line()
        self.commit()
        code, report = self.run_check()
        self.assertEqual(code, 1)
        self.assertEqual(report["waived_findings"], [])
        self.assertEqual(report["opt_outs"], [])

    def test_lines_are_unioned_and_only_named_checks_are_waived(self):
        self.add_long_line()
        self.write("anneal/ci/bad.py", "X = 1\n")
        self.commit(waiver_message(WAIVE_WRAP))
        code, report = self.run_check()
        self.assertEqual(code, 1)
        self.assertEqual([f["check"] for f in report["findings"]],
                         ["header"])
        self.amend(waiver_message(
            WAIVE_WRAP, "Skip-pr-hygiene: header -- Fixture mirrors input."))
        report = self.assert_clean()
        self.assertEqual(sorted(w["check"]
                                for w in report["waived_findings"]),
                         ["header", "wrap"])
        self.assertEqual(len(report["opt_outs"]), 2)
        self.amend(waiver_message(
            "Skip-pr-hygiene: wrap,header -- Generated fixture output."))
        report = self.assert_clean()
        self.assertEqual(report["opt_outs"][0]["checks"], ["wrap", "header"])

    def test_waiver_covers_commit_messages_across_the_range(self):
        self.add_long_line()
        self.commit("[ci] Subject that ends with a period.\n\n" + TRAILER)
        self.write("anneal/docs/other.md", HEADER_MD + "\nShort.\n")
        self.commit(waiver_message(
            "Skip-pr-hygiene: commit-message,wrap -- Imported history."))
        report = self.assert_clean()
        self.assertIn("commit-message",
                      {w["check"] for w in report["waived_findings"]})

    def test_unused_waiver_fails(self):
        self.add_long_line()
        self.commit(waiver_message(
            "Skip-pr-hygiene: wrap,diff-check -- Generated text here."))
        code, report = self.run_check()
        self.assertEqual(code, 1)
        self.assertEqual(self.skip_findings(report), [
            "`diff-check` has no findings to waive; remove it from the "
            "trailer"])
        self.assertEqual([w["check"] for w in report["waived_findings"]],
                         ["wrap"])

    def test_waiver_without_any_finding_fails(self):
        self.write("anneal/docs/note.md", HEADER_MD + "\nShort.\n")
        self.commit(waiver_message(WAIVE_WRAP))
        f = self.assert_finding("skip-pr-hygiene", "no findings to waive")
        self.assertEqual(f["line"], 5)

    def test_reason_needs_five_non_whitespace_characters(self):
        self.add_long_line()
        self.commit()
        for reason in ("tiny", "a b c d"):
            with self.subTest(reason=reason):
                self.amend(waiver_message(
                    f"Skip-pr-hygiene: wrap -- {reason}"))
                code, report = self.run_check()
                self.assertEqual(code, 1)
                self.assertTrue(any("at least 5" in m for m in
                                    self.skip_findings(report)), report)
                # A rejected waiver waives nothing.
                self.assertIn("wrap", {f["check"]
                                       for f in report["findings"]})
        self.amend(waiver_message("Skip-pr-hygiene: wrap -- a b c d e"))
        self.assert_clean()

    def test_unwaivable_and_unknown_names_fail(self):
        self.add_long_line()
        self.commit()
        for name in ("all", "agents-budget", "code-review-rules-parity",
                     "commit-author",
                     "pr-body", "pr-title", "pr-title-policy", "receipt",
                     "skip-pr-hygiene", "Wrap", "bogus"):
            with self.subTest(name=name):
                self.amend(waiver_message(
                    f"Skip-pr-hygiene: wrap,{name} -- Generated text."))
                code, report = self.run_check()
                self.assertEqual(code, 1)
                messages = self.skip_findings(report)
                self.assertTrue(any(f"cannot waive `{name}`" in m
                                    for m in messages), messages)
                self.assertEqual(report["opt_outs"], [])

    def test_malformed_trailers_fail(self):
        self.add_long_line()
        cases = {
            "Skip-pr-hygiene: wrap - Generated text.": "` -- `",
            "Skip-pr-hygiene: wrap": "` -- `",
            "Skip-pr-hygiene: wrap,,header -- Generated text.":
                "<check>[,<check>...]",
            "Skip-pr-hygiene: wrap header -- Generated text.":
                "<check>[,<check>...]",
            # Without the space, the line is not a trailer at all.
            "Skip-pr-hygiene:wrap -- Generated text.": "final trailer block",
            # A continuation line of another trailer.
            "Fixes #12\n Skip-pr-hygiene: wrap -- Generated text.":
                "spell the trailer",
        }
        self.commit()
        for trailer, needle in cases.items():
            with self.subTest(trailer=trailer):
                self.amend(waiver_message(trailer))
                code, report = self.run_check()
                self.assertEqual(code, 1)
                self.assertTrue(any(needle in m for m in
                                    self.skip_findings(report)), report)

    def test_key_casing_must_be_exact(self):
        self.add_long_line()
        self.commit()
        for key in ("skip-pr-hygiene", "SKIP-PR-HYGIENE", "Skip-PR-Hygiene"):
            with self.subTest(key=key):
                self.amend(waiver_message(
                    f"{key}: wrap -- Generated text keeps lines."))
                code, report = self.run_check()
                self.assertEqual(code, 1)
                self.assertTrue(any("spell the trailer exactly" in m
                                    for m in self.skip_findings(report)))
                self.assertEqual(report["waived_findings"], [])

    def test_folded_trailer_fails(self):
        self.add_long_line()
        self.commit(waiver_message(
            "Skip-pr-hygiene: wrap -- Generated text that\n"
            "  continues on a folded line."))
        f = self.assert_finding("skip-pr-hygiene", "folded")
        self.assertEqual(f["line"], 5)

    def test_waiver_outside_final_trailer_block_fails(self):
        self.add_long_line()
        self.commit(waiver_message(body=f"{WAIVE_WRAP}\n\n"))
        code, report = self.run_check()
        self.assertEqual(code, 1)
        self.assertTrue(any("final trailer block" in m
                            for m in self.skip_findings(report)))
        self.assertEqual(report["waived_findings"], [])

    def test_trailer_on_earlier_commit_fails_in_any_case(self):
        self.add_long_line()
        self.commit(waiver_message("skip-PR-hygiene: wrap -- Old waiver."))
        # Commits outside Anneal paths are scanned too.
        self.write("README.md", "Root readme.\n")
        early = self.commit(waiver_message(WAIVE_WRAP))
        self.write("anneal/docs/other.md", HEADER_MD + "\nShort.\n")
        self.commit(waiver_message(WAIVE_WRAP))
        code, report = self.run_check()
        self.assertEqual(code, 1)
        tips = [f for f in report["findings"]
                if f["check"] == "skip-pr-hygiene"]
        self.assertEqual(len(tips), 2, tips)
        self.assertTrue(all("only the PR's tip commit" in f["message"]
                            for f in tips))
        self.assertIn(f"commit {early[:12]}", [f["path"] for f in tips])
        # The tip commit's own waiver still applies.
        self.assertEqual([w["check"] for w in report["waived_findings"]],
                         ["wrap"])

    def test_code_block_mentions_are_ignored(self):
        self.add_long_line()
        doc = (
            "Document the trailer syntax:\n\n"
            "```\n" + WAIVE_WRAP + "\n```\n\n"
            "    " + WAIVE_WRAP + "\n\n"
        )
        self.commit(waiver_message(body=doc))
        self.write("anneal/docs/other.md", HEADER_MD + "\nShort.\n")
        self.commit(waiver_message(body=doc))
        code, report = self.run_check()
        # Neither commit waives or misplaces anything, so only the long
        # line remains.
        self.assertEqual(code, 1)
        self.assertEqual([f["check"] for f in report["findings"]], ["wrap"])
        self.assertEqual(report["opt_outs"], [])

    def test_waived_findings_are_annotated_and_summarized(self):
        self.add_long_line()
        self.commit(waiver_message(
            "Skip-pr-hygiene: wrap -- Keeps 100% of | generated <rows>."))
        summary = self.repo.parent / "summary.md"
        summary.write_text("Earlier step output.\n")
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--base", "base"],
            capture_output=True, text=True, check=False,
            env={**ambient_env(), "GITHUB_STEP_SUMMARY": str(summary)},
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        annotations = [ln for ln in res.stdout.splitlines()
                       if ln.startswith("::")]
        self.assertEqual(len(annotations), 1, res.stdout)
        self.assertTrue(annotations[0].startswith(
            "::warning file=anneal/docs/note.md,line=9,"
            "title=PR hygiene waived%3A wrap::[wrap] anneal/docs/note.md:9: "),
            annotations[0])
        self.assertIn("Keeps 100%25 of | generated <rows>.", annotations[0])
        self.assertIn("PR hygiene checks passed (1 waived).", res.stdout)
        text = summary.read_text()
        self.assertTrue(text.startswith("Earlier step output.\n"))
        self.assertIn("| Check | Location | Finding | Reason |", text)
        self.assertIn(
            "| wrap | anneal/docs/note.md:9 | 99 columns; wrap prose at 80 "
            "columns | Keeps 100% of &#124; generated &lt;rows&gt;. |", text)

    def test_commit_message_annotation_has_no_file(self):
        self.add_long_line()
        self.commit("[ci] Subject with a period.\n\n" + TRAILER)
        self.write("anneal/docs/other.md", HEADER_MD + "\nShort.\n")
        self.commit(waiver_message(
            "Skip-pr-hygiene: commit-message,wrap -- Imported history."))
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--base", "base", "--json"],
            capture_output=True, text=True, check=False, env=ambient_env(),
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        # With --json, stdout is the report and annotations go to stderr.
        self.assertTrue(json.loads(res.stdout)["ok"])
        lines = [ln for ln in res.stderr.splitlines()
                 if ln.startswith("::warning")]
        self.assertEqual(len(lines), 2, res.stderr)
        commit_line = next(ln for ln in lines if "commit-message" in ln)
        self.assertTrue(commit_line.startswith(
            "::warning title=PR hygiene waived%3A commit-message::"))

    def test_no_summary_without_waivers(self):
        self.write("anneal/docs/note.md", HEADER_MD + "\nShort.\n")
        self.commit()
        summary = self.repo.parent / "summary.md"
        code, _ = self.run_check(env={"GITHUB_STEP_SUMMARY": str(summary)})
        self.assertEqual(code, 0)
        self.assertFalse(summary.exists())

    def test_trailer_survives_pr_body_unwrapping(self):
        self.add_long_line()
        self.commit(waiver_message(WAIVE_WRAP))
        expected = (
            "Add a note whose long line comes from a generator.\n\n"
            f"{WAIVE_WRAP}\n\n"
            "*Authored by an AI agent acting on joshlf's behalf.*\n"
        )
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), "--emit-pr-body"],
            capture_output=True, text=True, check=True,
        )
        self.assertEqual(res.stdout, expected)
        body = self.repo.parent / "body.md"
        body.write_text(expected)
        self.assert_clean("--pr-body-file", str(body))

    def test_commit_message_waiver_does_not_cover_identity(self):
        self.add_long_line()
        self.commit(waiver_message(
            "Skip-pr-hygiene: commit-message,wrap -- Imported history."))
        code, report = self.run_check("--expected-author",
                                      "J <j@example.com>")
        self.assertEqual(code, 1)
        self.assertEqual(
            sorted({f["check"] for f in report["findings"]}),
            ["commit-author", "skip-pr-hygiene"])
        # `commit-message` had nothing else to waive, so it is unused.
        self.assertEqual(self.skip_findings(report), [
            "`commit-message` has no findings to waive; remove it from the "
            "trailer"])
        self.amend(waiver_message(
            "Skip-pr-hygiene: commit-author,wrap -- Imported history."))
        code, report = self.run_check("--expected-author",
                                      "J <j@example.com>")
        self.assertEqual(code, 1)
        self.assertTrue(any("cannot waive `commit-author`" in m
                            for m in self.skip_findings(report)))
        self.assertIn("commit-author", {f["check"]
                                        for f in report["findings"]})


# Built at runtime so `ci/check_todo.sh` does not flag this file.
MARKER = "TO" + "DO"
TITLE_REGEX = r"\b[T]ODO\b"


class PrTitlePolicyTests(RepoTestCase):
    def setUp(self) -> None:
        super().setUp()
        self.write("anneal/docs/note.md", HEADER_MD + "\nA note.\n")
        self.commit()
        self.write("anneal/docs/note2.md", HEADER_MD + "\nB.\n")
        self.commit()

    def test_forbidden_title_fails_on_multi_commit_pr(self):
        f = self.assert_finding(
            "pr-title-policy", "matches the forbidden pattern",
            "--forbid-pr-title-regex", TITLE_REGEX,
            env={"PR_TITLE": f"[ci] Resolve {MARKER} list"})
        self.assertIn(TITLE_REGEX, f["message"])

    def test_allowed_titles_pass(self):
        for title in ("[ci] Add helpers", f"[ci] {MARKER}S stay",
                      f"[ci] {MARKER.lower()} list"):
            with self.subTest(title=title):
                self.assert_clean("--forbid-pr-title-regex", TITLE_REGEX,
                                  env={"PR_TITLE": title})

    def test_title_flag_takes_precedence_without_equality_check(self):
        env = {"PR_TITLE": "[ci] Fine title"}
        self.assert_finding(
            "pr-title-policy", MARKER, "--forbid-pr-title-regex",
            TITLE_REGEX, "--pr-title", f"{MARKER}: fix", env=env)
        # Multi-commit PRs skip the `--pr-title` equality check.
        code, report = self.run_check(
            "--forbid-pr-title-regex", TITLE_REGEX, "--pr-title",
            "[ci] Unrelated title", env={"PR_TITLE": f"{MARKER}"})
        self.assertEqual(code, 0, report)

    def test_title_policy_runs_without_base(self):
        code, report = self.run_check(
            "--forbid-pr-title-regex", TITLE_REGEX, base=None,
            env={"PR_TITLE": f"{MARKER} later"})
        self.assertEqual(code, 1)
        self.assertEqual([f["check"] for f in report["findings"]],
                         ["pr-title-policy"])

    def test_missing_title_or_bad_regex_fails_closed(self):
        for args, env in (
                (("--forbid-pr-title-regex", TITLE_REGEX), {}),
                (("--forbid-pr-title-regex", TITLE_REGEX),
                 {"PR_TITLE": "  "}),
                (("--forbid-pr-title-regex", ""), {"PR_TITLE": "x"}),
                (("--forbid-pr-title-regex", "("), {"PR_TITLE": "x"})):
            with self.subTest(args=args, env=env):
                code, report = self.run_check(*args, env=env)
                self.assertEqual(code, 2, report)
                self.assertIn("error", report)

    def test_title_policy_is_not_waivable(self):
        self.commit(waiver_message(
            "Skip-pr-hygiene: pr-title-policy -- Title fixed later."))
        code, report = self.run_check(
            "--forbid-pr-title-regex", TITLE_REGEX,
            env={"PR_TITLE": f"{MARKER} title"})
        self.assertEqual(code, 1)
        self.assertEqual(sorted(f["check"] for f in report["findings"]),
                         ["pr-title-policy", "skip-pr-hygiene"])


class RepositoryTreeTests(unittest.TestCase):
    def test_checked_in_tree_passes_tree_checks(self):
        repo = Path(__file__).resolve().parents[2]
        if not (repo / ".git").exists():
            self.skipTest("not running from a Git checkout")
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo", str(repo),
             "--json"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)


if __name__ == "__main__":
    unittest.main()
