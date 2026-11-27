# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Adversarial input hardening and review surface checks."""

from __future__ import annotations

from .support import (
    cph,
    git,
    HEADER_LEAN,
    HEADER_MD,
    HEADER_PY,
    HEADER_RS,
    SHA_RUST,
)


class HardeningCases:
    """Test methods of `HardeningTests`."""

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


class ReviewSurfaceCases:
    """Test methods of `ReviewSurfaceTests`."""

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
                     "zerocopy/proofs/01_x/spec_sources.json",
                     "zerocopy/proofs/01_x/Specs/zerocopy/zc01.lean",
                     "zerocopy/proofs/01_x/Specs/zerocopy/Proof.lean",
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
