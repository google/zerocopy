# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Diff, file header, prose wrapping, citation, and tree checks."""

from __future__ import annotations

from .support import (
    cph,
    CRR,
    git,
    HEADER_LEAN,
    HEADER_MD,
    HEADER_PY,
    HEADER_RS,
    ROUND_ID,
    SHA_RUST,
)


class DiffCases:
    """Test methods of `DiffTests`."""

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


class WrapCases:
    """Test methods of `WrapTests`."""

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


class WrapUnitCases:
    """Test methods of `WrapUnitTests`."""

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


class TrustedCitationCases:
    """Test methods of `TrustedCitationTests`."""

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


class TreeCheckCases:
    """Test methods of `TreeCheckTests`."""

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

    def test_rustc_workaround_anchors(self):
        tag = cph.WORKAROUND_TAG
        self.write("anneal/trusted/x.rs",
                   HEADER_RS + f"// {tag}(#4364): summary\nfn f() {{}}\n")
        self.write("anneal/docs/x.md", f"Example `// {tag}(#PENDING): s`\n")
        self.write("anneal/vendor/x.rs", f"// {tag}(#PENDING): s\n")
        self.commit()
        self.assert_clean(base=None)
        self.write("anneal/ci/y.py", HEADER_PY + f"# {tag}(#PENDING): s\n")
        self.commit()
        found = self.assert_finding("rustc-workaround", "#PENDING", base=None)
        self.assertEqual((found["path"], found["line"]), ("anneal/ci/y.py", 8))
        self.assert_finding("rustc-workaround", "#PENDING")
        self.write("anneal/ci/y.py", HEADER_PY + f"x = 1  # {tag}(#1): s\n")
        self.commit()
        self.assert_finding("rustc-workaround", "malformed anchor", base=None)

    def test_crr_missing_marker(self):
        self.write("anneal/.gemini/styleguide.md", "# Style\n\nNo markers.\n")
        self.commit()
        self.assert_finding("code-review-rules-parity", "expected one",
                            base=None)
