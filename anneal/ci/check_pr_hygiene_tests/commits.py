# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Clean changes and commit message checks."""

from __future__ import annotations

from .support import (
    AUTHOR,
    HEADER_MD,
    HEADER_PY,
    ROUND_ID,
    SCRIPT,
    subprocess,
    sys,
    TRAILER,
)


class CleanChangeCases:
    """Test methods of `CleanChangeTests`."""

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


class CommitMessageCases:
    """Test methods of `CommitMessageTests`."""

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
