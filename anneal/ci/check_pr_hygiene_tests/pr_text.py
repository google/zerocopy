# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""PR body and receipt checks."""

from __future__ import annotations

from .support import (
    cph,
    git,
    HEADER_LEAN,
    HEADER_MD,
    HEADER_PY,
    json,
    SCRIPT,
    subprocess,
    sys,
    TRAILER,
)


class PrBodyCases:
    """Test methods of `PrBodyTests`."""

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


class UnwrapUnitCases:
    """Test methods of `UnwrapUnitTests`."""

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


class ReceiptCases:
    """Test methods of `ReceiptTests`."""

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
