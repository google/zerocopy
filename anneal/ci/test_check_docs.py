# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and negative-oracle tests for `ci/check_docs.py`."""

import hashlib
import io
import json
from pathlib import Path
import stat
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

import check_docs
from workflow_yaml import load_workflow_yaml


ANNEAL_ROOT = Path(__file__).resolve().parent.parent


def _make_minimal_anneal_root(root: Path) -> Path:
    """Create a valid minimal `anneal/` tree for isolated oracle tests."""
    root.mkdir(parents=True, exist_ok=True)
    (root / "PRINCIPLES.md").write_text(
        "# Principles\n\nSee [Threat\nModel](THREAT_MODEL.md).\n",
        encoding="utf-8",
    )
    (root / "THREAT_MODEL.md").write_text(
        "# Threat Model\n\nSee [Trust Model](docs/trust-model.md).\n",
        encoding="utf-8",
    )
    (root / "META_PRINCIPLES.md").write_text(
        "# Meta-Principles\n\nSee [Principles](PRINCIPLES.md).\n",
        encoding="utf-8",
    )
    (root / "book/src/reference").mkdir(parents=True)
    (root / "book/examples/cli/help").mkdir(parents=True)
    (root / "book/book.toml").write_text(
        '[book]\ntitle = "Anneal"\n'
        '[output.html]\nsite-url = "/zerocopy/anneal/"\n'
        'git-repository-url = "https://github.com/google/zerocopy/tree/main/anneal"\n'
        'default-theme = "light"\n'
        'preferred-dark-theme = "navy"\n',
        encoding="utf-8",
    )
    (root / "book/src/SUMMARY.md").write_text(
        "# Summary\n\n"
        "- [Introduction](index.md)\n"
        "- [CLI](reference/cli.md)\n"
        "- [Principles](foundations/principles.md)\n"
        "- [Threat Model](foundations/threat-model.md)\n"
        "- [Meta-Principles](foundations/meta-principles.md)\n",
        encoding="utf-8",
    )
    (root / "book/src/index.md").write_text(
        "# Anneal\n\nWelcome.\n", encoding="utf-8"
    )
    (root / "book/src/reference/cli.md").write_text(
        "# CLI\n\n"
        "```console\n"
        "{{#include ../../examples/cli/help/transcript.txt}}\n"
        "```\n",
        encoding="utf-8",
    )
    (root / "book/examples/cli/help/case.json").write_text(
        json.dumps(
            {
                "kind": "cli",
                "display_command": "$ cargo anneal --help",
                "argv": ["anneal", "--help"],
                "expect_exit": 0,
                "transcript": "transcript.txt",
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (root / "book/examples/cli/help/transcript.txt").write_text(
        "$ cargo anneal --help\nUsage: cargo anneal\n",
        encoding="utf-8",
    )
    return root


class CheckSourcesOracleTests(unittest.TestCase):
    def test_valid_minimal_tree_passes(self):
        with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
            root = _make_minimal_anneal_root(Path(tmp))
            self.assertEqual(check_docs.check_sources(root), [])

    def test_raw_inline_fences_and_commonmark_desyncs_fail(self):
        cases = [
            ("rust", "```rust\nfn main() {}\n```"),
            ("sh", "```sh\necho hi\n```"),
            ("reordered_tags", "```no_run,rust\nfn main() {}\n```"),
            ("html_entity_info", "```&#114;ust\nfn main() {}\n```"),
            ("backslash_escaped_comma", "```rust\\,no_run\nfn main() {}\n```"),
            ("blockquote_fence", "> ```rust\n> fn main() {}\n> ```"),
            ("list_item_fence", "- ```rust\n  fn main() {}\n  ```"),
            ("nested_blockquote_in_list", "- > ```rust\n  > fn main() {}\n  > ```"),
            (
                "four_space_indented_desync",
                "    ````\n```rust\nfn unverified() {}\n```\n<script>alert(1)</script>\n    ````",
            ),
            (
                "list_exit_breakout",
                "- ```text\n```rust\nfn unverified() {}\n```\n</main><script>alert(1)</script><main>\n  ```",
            ),
        ]
        for label, snippet in cases:
            with self.subTest(case=label):
                with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
                    root = _make_minimal_anneal_root(Path(tmp))
                    (root / "book/src/index.md").write_text(
                        f"# Intro\n\n{snippet}\n", encoding="utf-8"
                    )
                    errors = check_docs.check_sources(root)
                    self.assertTrue(
                        any(
                            "code fence" in e or "unclosed fenced" in e
                            for e in errors
                        ),
                        errors,
                    )
                    if label in ("four_space_indented_desync", "list_exit_breakout"):
                        self.assertTrue(
                            any("raw HTML tags are forbidden" in e for e in errors),
                            errors,
                        )

    def test_conceptual_fence_forbidden_in_strict_chapters(self):
        with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
            root = _make_minimal_anneal_root(Path(tmp))
            (root / "book/src/reference/cli.md").write_text(
                "# CLI\n\n"
                "```console\n"
                "{{#include ../../examples/cli/help/transcript.txt}}\n"
                "```\n\n"
                "```rust,conceptual\nfn sketch() {}\n```\n",
                encoding="utf-8",
            )
            errors = check_docs.check_sources(root)
            self.assertTrue(
                any("`conceptual` code fence is forbidden" in e for e in errors),
                errors,
            )

    def test_disallowed_mdbook_directives_and_unfenced_includes_fail(self):
        bad_directives = [
            ("playground", "{{#playground ../examples/cli/help/transcript.txt}}", "disallowed or malformed"),
            ("trailing_space", "{{#include ../examples/cli/help/transcript.txt }}", "disallowed or malformed"),
            ("extra_args", "{{#include ../examples/cli/help/transcript.txt 1:2}}", "disallowed or malformed"),
            ("quoted_path", '{{#include "../examples/cli/help/transcript.txt"}}', "disallowed or malformed"),
            ("unclosed", "{{#include ../examples/cli/help/transcript.txt", "disallowed or malformed"),
            ("unfenced_prose_include", "{{#include ../examples/cli/help/transcript.txt}}", "only permitted inside a checked code fence"),
        ]
        for label, directive, expected in bad_directives:
            with self.subTest(case=label):
                with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
                    root = _make_minimal_anneal_root(Path(tmp))
                    (root / "book/src/index.md").write_text(
                        f"# Intro\n\n{directive}\n", encoding="utf-8"
                    )
                    errors = check_docs.check_sources(root)
                    self.assertTrue(any(expected in e for e in errors), errors)

    def test_unverified_file_bad_ranges_and_anchors_via_check_sources(self):
        with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
            root = _make_minimal_anneal_root(Path(tmp))
            (root / "book/examples/cli/help/unverified.txt").write_text(
                "unverified\n", encoding="utf-8"
            )
            (root / "book/examples/cli/help/transcript.txt").write_text(
                "$ cargo anneal --help\n"
                "// ANCHOR: empty\n// ANCHOR_END: empty\n"
                "// ANCHOR: dup\nline\n// ANCHOR_END: dup\n"
                "// ANCHOR: dup\nline2\n// ANCHOR_END: dup\n"
                "// ANCHOR: unclosed\n",
                encoding="utf-8",
            )
            (root / "book/src/index.md").write_text(
                "# Intro\n\n"
                "```console\n"
                "{{#include ../examples/cli/help/unverified.txt}}\n"
                "```\n\n"
                "```console\n"
                "{{#include ../examples/cli/help/transcript.txt:foo:bar}}\n"
                "```\n\n"
                "```console\n"
                "{{#include ../examples/cli/help/transcript.txt:1_0:2}}\n"
                "```\n\n"
                "```console\n"
                "{{#include ../examples/cli/help/transcript.txt:+1:2}}\n"
                "```\n\n"
                "```console\n"
                "{{#include ../examples/cli/help/transcript.txt:empty}}\n"
                "```\n\n"
                "```console\n"
                "{{#include ../examples/cli/help/transcript.txt:missing}}\n"
                "```\n",
                encoding="utf-8",
            )
            errors = check_docs.check_sources(root)
            self.assertTrue(
                any("not a registered verified artifact" in e for e in errors),
                errors,
            )
            self.assertEqual(
                sum("non-integer line range" in e for e in errors), 3, errors
            )
            self.assertTrue(any("anchor `empty`" in e for e in errors), errors)
            self.assertTrue(
                any("missing anchor `missing`" in e for e in errors), errors
            )
            self.assertTrue(
                any("duplicate ANCHOR start `dup`" in e for e in errors), errors
            )
            self.assertTrue(
                any("unclosed ANCHOR `unclosed`" in e for e in errors), errors
            )

    def test_hidden_rustdoc_unsafe_and_inner_doc_anneal_spec_fail(self):
        with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
            root = _make_minimal_anneal_root(Path(tmp))
            rs_path = root / "book/examples/cli/help/demo.rs"
            rs_path.write_text(
                "//! ```anneal\n"
                "// ANCHOR: shown\n"
                "# unsafe fn hidden_by_rustdoc() {}\n"
                "pub fn safe_id(x: usize) -> usize { x }\n"
                "// ANCHOR_END: shown\n"
                "/// anneal:requires x != 0\n"
                "pub unsafe fn hidden_outside(x: usize) -> usize { x }\n",
                encoding="utf-8",
            )
            errors: list[str] = []
            check_docs._validate_rust_anchor_coverage(
                rs_path, [(3, 4, "rustdoc_include")], errors
            )
            self.assertTrue(any("```anneal" in e for e in errors), errors)
            self.assertTrue(any("hidden_by_rustdoc" in e for e in errors), errors)
            self.assertTrue(any("hidden_outside" in e for e in errors), errors)

    def test_unreferenced_example_case_fails_even_if_case_json_included(self):
        with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
            root = _make_minimal_anneal_root(Path(tmp))
            orphan = root / "book/examples/cli/orphan"
            orphan.mkdir(parents=True)
            (orphan / "case.json").write_text(
                json.dumps(
                    {
                        "kind": "cli",
                        "display_command": "$ cargo anneal --version",
                        "argv": ["anneal", "--version"],
                        "expect_exit": 0,
                        "transcript": "transcript.txt",
                    }
                ),
                encoding="utf-8",
            )
            (orphan / "transcript.txt").write_text(
                "$ cargo anneal --version\ncargo-anneal 0.1.0\n",
                encoding="utf-8",
            )
            (root / "book/src/index.md").write_text(
                "# Intro\n\n```console\n{{#include ../examples/cli/orphan/case.json}}\n```\n",
                encoding="utf-8",
            )
            errors = check_docs.check_sources(root)
            self.assertTrue(
                any("not a registered verified artifact" in e for e in errors),
                errors,
            )
            self.assertTrue(
                any("verified artifact is not included" in e for e in errors),
                errors,
            )

    def test_exact_case_allowlist_and_raw_html_tags_fail(self):
        for rel_path in (
            "Cargo.toml",
            "helper.py",
            "Proof.lean",
            "theme/index.hbs",
            "src/x.html",
            "src/pic.svg",
            "src/page.xhtml",
            "src/evil.MD",
            "examples/cli/help/Cargo.toml",
            "examples/cli/help/cargo.lock",
            "examples/cli/help/demo.RS",
        ):
            with self.subTest(path=rel_path):
                with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
                    root = _make_minimal_anneal_root(Path(tmp))
                    target = root / "book" / rel_path
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text("", encoding="utf-8")
                    errors = check_docs.check_sources(root)
                    self.assertTrue(
                        len(errors) > 0, f"expected rejection for {rel_path}"
                    )

        for label, bad_md in (
            ("script", "<script>alert(1)</script>"),
            ("img_multiline", '<img src="x" onerror\n="alert(1)">'),
            ("main_breakout", "</main><p>x</p>"),
            ("base_tag", '<base href="https://attacker.example/">'),
            ("entity_js_link", '<a href="&#106;avascript:alert(1)">click</a>'),
            ("md_js_link", "[click](javascript:alert(1))"),
            ("multiline_backtick_breakout", "`foo\n<script>alert(1)</script>\nbar`"),
        ):
            with self.subTest(html=label):
                with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
                    root = _make_minimal_anneal_root(Path(tmp))
                    (root / "book/src/index.md").write_text(
                        f"# Intro\n\n{bad_md}\n", encoding="utf-8"
                    )
                    errors = check_docs.check_sources(root)
                    self.assertTrue(
                        any(
                            "raw HTML tags are forbidden" in e
                            or "disallowed script/data URL scheme" in e
                            for e in errors
                        ),
                        errors,
                    )

    def test_unmapped_wrapped_governing_doc_link_fails(self):
        with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
            root = _make_minimal_anneal_root(Path(tmp))
            (root / "PRINCIPLES.md").write_text(
                "# Principles\n\nSee [Wrapped\nLink](docs/unmapped.md).\n",
                encoding="utf-8",
            )
            errors = check_docs.check_sources(root)
            self.assertTrue(
                any("unmapped relative link `docs/unmapped.md`" in e for e in errors),
                errors,
            )

    def test_duplicate_checked_in_governing_doc_fails(self):
        with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
            root = _make_minimal_anneal_root(Path(tmp))
            (root / "book/src/foundations").mkdir(parents=True)
            (root / "book/src/foundations/principles.md").write_text(
                "# Duplicate\n", encoding="utf-8"
            )
            errors = check_docs.check_sources(root)
            self.assertTrue(
                any("do not check in a duplicate copy" in e for e in errors),
                errors,
            )

    def test_book_toml_disallowed_sections_missing_site_url_and_themes_fail(self):
        bad_configs = [
            (
                "preprocessor",
                '[book]\ntitle = "Anneal"\n[output.html]\nsite-url = "/zerocopy/anneal/"\n[preprocessor.evil]\ncommand = "true"\n',
                "disallowed top-level sections",
            ),
            (
                "custom_output",
                '[book]\ntitle = "Anneal"\n[output.html]\nsite-url = "/zerocopy/anneal/"\n[output.evil]\ncommand = "true"\n',
                "disallowed `[output]` sections",
            ),
            (
                "additional_js",
                '[book]\ntitle = "Anneal"\n[output.html]\nsite-url = "/zerocopy/anneal/"\nadditional-js = ["x.js"]\n',
                "disallowed `[output.html]` keys",
            ),
            (
                "missing_output",
                '[book]\ntitle = "Anneal"\n',
                "missing `[output]` table",
            ),
            (
                "missing_site_url",
                '[book]\ntitle = "Anneal"\n[output.html]\ndefault-theme = "light"\n',
                "`[output.html].site-url` must be",
            ),
            (
                "bad_site_url",
                '[book]\ntitle = "Anneal"\n[output.html]\nsite-url = "https://attacker.example/"\n',
                "`[output.html].site-url` must be",
            ),
            (
                "bad_repo_url",
                '[book]\ntitle = "Anneal"\n[output.html]\nsite-url = "/zerocopy/anneal/"\ngit-repository-url = "javascript:alert(1)"\n',
                "`[output.html].git-repository-url` must start with",
            ),
            (
                "custom_theme_name",
                '[book]\ntitle = "Anneal"\n[output.html]\nsite-url = "/zerocopy/anneal/"\ndefault-theme = "custom-injected"\n',
                "must be a built-in mdBook theme",
            ),
        ]
        for label, toml_text, expected in bad_configs:
            with self.subTest(case=label):
                with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
                    root = _make_minimal_anneal_root(Path(tmp))
                    (root / "book/book.toml").write_text(
                        toml_text, encoding="utf-8"
                    )
                    errors = check_docs.check_sources(root)
                    self.assertTrue(any(expected in e for e in errors), errors)

    def test_cli_argv_allowlist_traversal_and_case_schema_fail_closed(self):
        bad_cases = [
            (
                "bare_setup_network",
                {
                    "kind": "cli",
                    "display_command": "$ cargo anneal setup",
                    "argv": ["anneal", "setup"],
                    "expect_exit": 0,
                    "transcript": "transcript.txt",
                },
                "closed offline CLI allowlist",
            ),
            (
                "future_verify_unsandboxed",
                {
                    "kind": "cli",
                    "display_command": "$ cargo anneal verify",
                    "argv": ["anneal", "verify"],
                    "expect_exit": 0,
                    "transcript": "transcript.txt",
                },
                "closed offline CLI allowlist",
            ),
            (
                "absolute_arg",
                {
                    "kind": "cli",
                    "display_command": "$ cargo anneal setup --local-archive /etc/passwd",
                    "argv": ["anneal", "setup", "--local-archive", "/etc/passwd"],
                    "expect_exit": 1,
                    "transcript": "transcript.txt",
                },
                "absolute or parent-traversal paths",
            ),
            (
                "equals_absolute",
                {
                    "kind": "cli",
                    "display_command": "$ cargo anneal setup --local-archive=/etc/passwd",
                    "argv": ["anneal", "setup", "--local-archive=/etc/passwd"],
                    "expect_exit": 1,
                    "transcript": "transcript.txt",
                },
                "absolute or parent-traversal paths",
            ),
            (
                "equals_parent",
                {
                    "kind": "cli",
                    "display_command": "$ cargo anneal setup --local-archive=../secret",
                    "argv": ["anneal", "setup", "--local-archive=../secret"],
                    "expect_exit": 1,
                    "transcript": "transcript.txt",
                },
                "absolute or parent-traversal paths",
            ),
            (
                "display_argv_mismatch",
                {
                    "kind": "cli",
                    "display_command": "$ cargo anneal --old-flag",
                    "argv": ["anneal", "--help"],
                    "expect_exit": 0,
                    "transcript": "transcript.txt",
                },
                "does not match `argv`",
            ),
            (
                "cargo_missing_anneal_subcommand",
                {
                    "kind": "cli",
                    "display_command": "$ cargo setup --help",
                    "argv": ["setup", "--help"],
                    "expect_exit": 0,
                    "transcript": "transcript.txt",
                },
                "does not match `argv`",
            ),
            (
                "bool_exit_code",
                {
                    "kind": "cli",
                    "display_command": "$ cargo anneal --help",
                    "argv": ["anneal", "--help"],
                    "expect_exit": True,
                    "transcript": "transcript.txt",
                },
                "`expect_exit` must be an integer",
            ),
            (
                "dot_setup_file",
                {
                    "kind": "cli",
                    "display_command": "$ cargo anneal --help",
                    "argv": ["anneal", "--help"],
                    "expect_exit": 0,
                    "transcript": "transcript.txt",
                    "setup_files": {"./.": "bad"},
                },
                "invalid `setup_files` relative path",
            ),
        ]
        for label, case_obj, expected in bad_cases:
            with self.subTest(case=label):
                with tempfile.TemporaryDirectory(prefix="anneal-docs-test-") as tmp:
                    root = _make_minimal_anneal_root(Path(tmp))
                    (root / "book/examples/cli/help/case.json").write_text(
                        json.dumps(case_obj), encoding="utf-8"
                    )
                    errors = check_docs.check_sources(root)
                    self.assertTrue(any(expected in e for e in errors), errors)


class VerifyExamplesOracleTests(unittest.TestCase):
    def _write_fake_cli(self, path: Path, body: str) -> Path:
        path.write_text(f"#!{sys.executable}\n{body}", encoding="utf-8")
        path.chmod(path.stat().st_mode | stat.S_IXUSR)
        return path

    def test_matching_and_drifted_cli_transcript_and_bless(self):
        with tempfile.TemporaryDirectory(prefix="anneal-docs-cli-") as tmp:
            tmp_path = Path(tmp)
            root = _make_minimal_anneal_root(tmp_path / "anneal")
            fake_bin = self._write_fake_cli(
                tmp_path / "fake-cargo-anneal",
                "import sys\nprint('Usage: cargo anneal')\n",
            )
            self.assertEqual(check_docs.verify_examples(root, fake_bin), [])

            self._write_fake_cli(
                fake_bin,
                "import sys\nprint('Usage: cargo anneal [NEW_FLAG]')\n",
            )
            errors = check_docs.verify_examples(root, fake_bin)
            self.assertTrue(
                any("transcript mismatch" in e for e in errors), errors
            )

            self.assertEqual(
                check_docs.verify_examples(root, fake_bin, bless=True), []
            )
            self.assertEqual(check_docs.verify_examples(root, fake_bin), [])

    def test_wrong_exit_code_fails(self):
        with tempfile.TemporaryDirectory(prefix="anneal-docs-cli-") as tmp:
            tmp_path = Path(tmp)
            root = _make_minimal_anneal_root(tmp_path / "anneal")
            fake_bin = self._write_fake_cli(
                tmp_path / "fake-cargo-anneal",
                "import sys\nsys.exit(2)\n",
            )
            errors = check_docs.verify_examples(root, fake_bin)
            self.assertTrue(
                any("expected exit code 0, got 2" in e for e in errors), errors
            )

    def test_main_runs_source_check_even_for_verify_examples_alone_and_rejects_mdbook_symlink(
        self,
    ):
        with tempfile.TemporaryDirectory(prefix="anneal-docs-cli-") as tmp:
            tmp_path = Path(tmp)
            root = _make_minimal_anneal_root(tmp_path / "anneal")
            (root / "book/book.toml").write_text(
                '[book]\ntitle = "Anneal"\n[preprocessor.evil]\ncommand = "true"\n',
                encoding="utf-8",
            )
            marker = tmp_path / "ran.txt"
            fake_bin = self._write_fake_cli(
                tmp_path / "fake-cargo-anneal",
                f"from pathlib import Path\nPath({str(marker)!r}).write_text('ran')\n",
            )
            rc = check_docs.main(
                [
                    "--anneal-root",
                    str(root),
                    "--verify-examples",
                    "--cargo-anneal",
                    str(fake_bin),
                ]
            )
            self.assertEqual(rc, 1)
            self.assertFalse(
                marker.exists(),
                "cargo-anneal must not execute when check_sources fails",
            )

            valid_root = _make_minimal_anneal_root(tmp_path / "anneal2")
            real_mdbook = self._write_fake_cli(tmp_path / "real-mdbook", "")
            link_mdbook = tmp_path / "link-mdbook"
            link_mdbook.symlink_to(real_mdbook)
            rc2 = check_docs.main(
                [
                    "--anneal-root",
                    str(valid_root),
                    "--build",
                    "--mdbook",
                    str(link_mdbook),
                    "--output",
                    str(tmp_path / "out"),
                ]
            )
            self.assertEqual(rc2, 1)


class EnsureMdbookTests(unittest.TestCase):
    def _build_tar_gz(self, entries: list[tuple[str, bytes]]) -> bytes:
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w:gz") as tf:
            for name, payload in entries:
                info = tarfile.TarInfo(name=name)
                info.size = len(payload)
                tf.addfile(info, io.BytesIO(payload))
        return buf.getvalue()

    def test_rejects_tarball_and_binary_sha_mismatch_and_bad_members(self):
        payload = b"fake-mdbook-binary"
        good_tar = self._build_tar_gz([("mdbook", payload)])
        good_tar_sha = hashlib.sha256(good_tar).hexdigest()
        good_bin_sha = hashlib.sha256(payload).hexdigest()

        with tempfile.TemporaryDirectory(prefix="anneal-mdbook-test-") as tmp:
            cache = Path(tmp) / "cache"

            with mock.patch.object(
                check_docs,
                "_download_with_retries",
                side_effect=lambda _u, dest: dest.write_bytes(good_tar),
            ):
                with self.assertRaisesRegex(check_docs.DocError, "tarball SHA-256"):
                    check_docs.ensure_mdbook(
                        cache,
                        expected_tarball_sha256="0" * 64,
                        expected_bin_sha256=good_bin_sha,
                    )

            with mock.patch.object(
                check_docs,
                "_download_with_retries",
                side_effect=lambda _u, dest: dest.write_bytes(good_tar),
            ):
                with self.assertRaisesRegex(check_docs.DocError, "binary SHA-256"):
                    check_docs.ensure_mdbook(
                        cache,
                        expected_tarball_sha256=good_tar_sha,
                        expected_bin_sha256="f" * 64,
                    )

            bad_tar = self._build_tar_gz([("mdbook", payload), ("extra", b"x")])
            bad_tar_sha = hashlib.sha256(bad_tar).hexdigest()
            with mock.patch.object(
                check_docs,
                "_download_with_retries",
                side_effect=lambda _u, dest: dest.write_bytes(bad_tar),
            ):
                with self.assertRaisesRegex(
                    check_docs.DocError, "unexpected mdBook tarball contents"
                ):
                    check_docs.ensure_mdbook(
                        cache,
                        expected_tarball_sha256=bad_tar_sha,
                        expected_bin_sha256=good_bin_sha,
                    )

            with mock.patch.object(
                check_docs,
                "_download_with_retries",
                side_effect=lambda _u, dest: dest.write_bytes(good_tar),
            ):
                bin_path = check_docs.ensure_mdbook(
                    cache,
                    expected_tarball_sha256=good_tar_sha,
                    expected_bin_sha256=good_bin_sha,
                )
                self.assertEqual(bin_path.read_bytes(), payload)


class HtmlLinkCheckerTests(unittest.TestCase):
    def test_valid_and_broken_links_xss_duplicate_attrs_main_breakout_and_code_parity(
        self,
    ):
        verified = {"$ cargo anneal --help\nUsage"}
        with tempfile.TemporaryDirectory(prefix="anneal-docs-html-") as tmp:
            html_root = Path(tmp)
            (html_root / "sub").mkdir()
            (html_root / "index.html").write_text(
                '<html><body><main><h1 id="top">Top</h1>'
                '<a href="sub/page.html#sec">ok</a>'
                '<a href="/zerocopy/anneal/sub/page.html#sec">ok-abs</a>'
                '<a href="https://example.com/external">ext</a>'
                '<pre><code class="language-console">$ cargo anneal --help\nUsage</code></pre>'
                "</main></body></html>",
                encoding="utf-8",
            )
            (html_root / "sub/page.html").write_text(
                '<html><body><main><h2 id="sec">Sec</h2>'
                '<a href="../index.html#top">back</a>'
                "</main></body></html>",
                encoding="utf-8",
            )
            self.assertEqual(
                check_docs.check_built_html_links(
                    html_root, verified_snippets=verified
                ),
                [],
            )

            (html_root / "sub/page.html").write_text(
                '<html><body><main><h2 id="sec">Sec</h2>'
                '<a href="../missing.html">broken-file</a>'
                '<a href="../index.html#no-such-id">broken-anchor</a>'
                '<a href="&#106;avascript:alert(1)" href="../index.html">dup-attr</a>'
                '<base href="https://attacker.example/">'
                '<svg></svg>'
                '<script>alert(1)</script>'
                '<img src="x" onerror="alert(1)">'
                '<pre><code class="language-rust">fn unverified() {}</code></pre>'
                "</main></main></body></html>",
                encoding="utf-8",
            )
            (html_root / "getting-started").mkdir()
            (html_root / "getting-started/install.html").write_text(
                "<html><body><main>"
                '<pre><code class="language-rust conceptual">fn sketch() {}</code></pre>'
                "</main></body></html>",
                encoding="utf-8",
            )
            errors = check_docs.check_built_html_links(
                html_root, verified_snippets=verified
            )
            self.assertTrue(any("broken internal link" in e for e in errors), errors)
            self.assertTrue(any("broken anchor `#no-such-id`" in e for e in errors), errors)
            self.assertTrue(any("duplicate attribute `href`" in e for e in errors), errors)
            self.assertTrue(any("disallowed URL scheme `javascript:`" in e for e in errors), errors)
            self.assertTrue(any("disallowed `<base>` element" in e for e in errors), errors)
            self.assertTrue(any("disallowed `<svg>` element" in e for e in errors), errors)
            self.assertTrue(any("disallowed `<script>` element" in e for e in errors), errors)
            self.assertTrue(any("disallowed event-handler attribute `onerror`" in e for e in errors), errors)
            self.assertTrue(any("unmatched `</main>`" in e for e in errors), errors)
            self.assertTrue(
                any("rendered `rust` code block does not match" in e for e in errors),
                errors,
            )
            self.assertTrue(
                any("rendered `conceptual` `rust` code block is forbidden" in e for e in errors),
                errors,
            )


class RepositoryDocsIntegrationTests(unittest.TestCase):
    def test_repository_book_sources_pass(self):
        self.assertEqual(check_docs.check_sources(ANNEAL_ROOT), [])

    def test_workflows_strip_actions_tokens_for_doc_steps(self):
        repo_root = ANNEAL_ROOT.parent
        anneal_ci = load_workflow_yaml(
            (repo_root / ".github/workflows/anneal-current.yml").read_text(
                encoding="utf-8"
            )
        )
        static_env = anneal_ci["jobs"]["static-checks"].get("env", {})
        for key in (
            "ACTIONS_CACHE_URL",
            "ACTIONS_RESULTS_URL",
            "ACTIONS_RUNTIME_TOKEN",
        ):
            self.assertEqual(static_env.get(key), "")

        test_steps = anneal_ci["jobs"]["test-and-verify"]["steps"]
        docs_steps = [
            step
            for step in test_steps
            if step.get("name") == "Verify and build public documentation"
        ]
        self.assertEqual(len(docs_steps), 1)
        env = docs_steps[0].get("env", {})
        for key in (
            "ACTIONS_CACHE_URL",
            "ACTIONS_RESULTS_URL",
            "ACTIONS_RUNTIME_TOKEN",
            "LD_LIBRARY_PATH",
        ):
            self.assertEqual(env.get(key), "")

        pages_wf = load_workflow_yaml(
            (repo_root / ".github/workflows/docs.yml").read_text(
                encoding="utf-8"
            )
        )
        build_steps = pages_wf["jobs"]["build"]["steps"]
        pages_docs_steps = [
            step
            for step in build_steps
            if step.get("name") == "Build Anneal public documentation"
        ]
        self.assertEqual(len(pages_docs_steps), 1)
        pages_env = pages_docs_steps[0].get("env", {})
        for key in (
            "ACTIONS_CACHE_URL",
            "ACTIONS_RESULTS_URL",
            "ACTIONS_RUNTIME_TOKEN",
        ):
            self.assertEqual(pages_env.get(key), "")
        self.assertIn("--output target/doc/anneal", pages_docs_steps[0]["run"])


if __name__ == "__main__":
    unittest.main()
