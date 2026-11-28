# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`Skip-pr-hygiene` waiver checks and the unwaivable PR title policy."""

from __future__ import annotations

from .support import (
    ambient_env,
    git,
    HEADER_MD,
    json,
    SCRIPT,
    subprocess,
    sys,
    TRAILER,
)


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


class WaiverCases:
    """Test methods of `WaiverTests`."""

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
                     "rustc-workaround", "skip-pr-hygiene", "Wrap", "bogus"):
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


class PrTitlePolicyCases:
    """Test methods of `PrTitlePolicyTests`."""

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
