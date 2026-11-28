# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for doc locator checking (`check_doc_locators.py`)."""

import contextlib
import io
from pathlib import Path
import tempfile
import os
import sys
import textwrap
import unittest

_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import check_doc_locators  # noqa: E402


class CheckDocLocatorsTest(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        # Keep a sibling of the repository inside the temporary directory, so
        # tests can point symlinks outside the repository.
        self.outside = Path(tmp.name) / "outside"
        self.outside.mkdir()
        self.repo = Path(tmp.name) / "repo"
        self.anneal = self.repo / "anneal"
        self.roots = (self.anneal, self.repo)
        self.write("anneal/trusted/foo/src/lib.rs", "pub fn guard_dir() {}\n")
        self.write(
            "anneal/trusted/foo/Lean.lean",
            "def importViolation? := 0\ntheorem step' : True := trivial\n"
            "fn f() { seal_it!(x) }\n",
        )
        self.write("anneal/tests/x/tests/suite.rs", "mod a;\n")
        self.write("anneal/tests/x/tests/suite/a.rs", "fn split_case() {}\n")
        self.write("anneal/tests/x/tests/gone/b.rs", "fn moved_case() {}\n")
        self.write(".github/workflows/ci.yml", "on: [push]\n")

    def write(self, rel: str, text: str) -> Path:
        path = self.repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def check(self, body: str) -> list[str]:
        doc = self.write("anneal/docs/doc.md", textwrap.dedent(body))
        findings = check_doc_locators.check_doc(doc, self.roots)
        prefix = f"{doc}:"
        self.assertTrue(all(f.startswith(prefix) for f in findings), findings)
        return [f[len(prefix) :] for f in findings]

    def test_accepts_resolvable_symbol_locators(self) -> None:
        self.assertEqual(
            self.check(
                """\
                `guard_dir` (`trusted/foo/src/lib.rs`) rejects it, as does
                `crate::guard_dir`
                (`trusted/foo/src/lib.rs`);
                `split_case` (`tests/x/tests/suite.rs`) lives in the split
                directory, `moved_case` (`tests/x/tests/gone.rs`) exists only
                there, `on` (`.github/workflows/ci.yml`) resolves
                from the repository root, and `guard_dir` (`trusted/foo/`) names
                a directory.
                """
            ),
            [],
        )

    def test_rejects_repository_line_locators(self) -> None:
        self.assertEqual(
            self.check(
                """\
                See `lib.rs:12-30` and
                `trusted/foo/src/lib.rs:7`, plus `x.lean:3, 9`.
                """
            ),
            [
                "1: line locator `lib.rs:12-30`; cite a symbol instead, "
                "as `symbol` (`path/to/file`)",
                "2: line locator `trusted/foo/src/lib.rs:7`; cite a symbol "
                "instead, as `symbol` (`path/to/file`)",
                "2: line locator `x.lean:3, 9`; cite a symbol instead, "
                "as `symbol` (`path/to/file`)",
            ],
        )

    def test_rejects_missing_paths_and_symbols(self) -> None:
        self.assertEqual(
            self.check(
                """\
                `guard_dir` (`trusted/foo/src/missing.rs`) and
                `other_guard` (`trusted/foo/src/lib.rs`) and
                `guard` (`trusted/foo/src/lib.rs`) and
                `guard_dir` (`../outside/lib.rs`).
                """
            ),
            [
                "1: symbol locator path `trusted/foo/src/missing.rs` does "
                "not exist (symlinks are not followed)",
                "2: symbol `other_guard` does not occur in "
                "`trusted/foo/src/lib.rs`",
                "3: symbol `guard` does not occur in `trusted/foo/src/lib.rs`",
                "4: symbol locator path `../outside/lib.rs` must be relative "
                "and free of `..`",
            ],
        )

    def test_rejects_absolute_and_escaping_paths(self) -> None:
        outside = self.outside
        (outside / "lib.rs").write_text("fn escaped() {}\n")
        os.symlink(outside, self.anneal / "trusted" / "link")
        os.symlink(outside / "lib.rs", self.anneal / "trusted" / "file.rs")
        self.assertEqual(
            self.check(
                f"""\
                `escaped` (`{outside / "lib.rs"}`) and
                `escaped` (`trusted/link/lib.rs`) and
                `escaped` (`trusted/file.rs`) and
                `escaped` (`trusted/link/`) and
                `guard_dir` (`trusted/foo/../foo/src/lib.rs`).
                """
            ),
            [
                f"1: symbol locator path `{outside / 'lib.rs'}` must be "
                "relative and free of `..`",
                "2: symbol locator path `trusted/link/lib.rs` does not exist "
                "(symlinks are not followed)",
                "3: symbol locator path `trusted/file.rs` does not exist "
                "(symlinks are not followed)",
                "4: symbol locator path `trusted/link/` does not exist "
                "(symlinks are not followed)",
                "5: symbol locator path `trusted/foo/../foo/src/lib.rs` must "
                "be relative and free of `..`",
            ],
        )

    def test_matches_lean_and_rust_name_characters(self) -> None:
        self.assertEqual(
            self.check(
                """\
                `importViolation?` (`trusted/foo/Lean.lean`),
                `Trusted.step'` (`trusted/foo/Lean.lean`), and
                `seal_it!` (`trusted/foo/Lean.lean`) resolve, while
                `importViolation` (`trusted/foo/Lean.lean`) and
                `step` (`trusted/foo/Lean.lean`) do not.
                """
            ),
            [
                "4: symbol `importViolation` does not occur in "
                "`trusted/foo/Lean.lean`",
                "5: symbol `step` does not occur in `trusted/foo/Lean.lean`",
            ],
        )

    def test_fences_follow_commonmark(self) -> None:
        self.assertEqual(
            self.check(
                """\
                ```x``` is an inline span, so `a.rs:1` is checked.

                ````md
                ```
                `b.rs:2` stays inside the outer fence.
                ````
                `c.rs:3` follows the fence.

                ~~~
                ```
                `d.rs:4` is fenced; backticks do not close a tilde fence.
                ~~~~
                `e.rs:5` follows it.
                """
            ),
            [
                "1: line locator `a.rs:1`; cite a symbol instead, "
                "as `symbol` (`path/to/file`)",
                "7: line locator `c.rs:3`; cite a symbol instead, "
                "as `symbol` (`path/to/file`)",
                "13: line locator `e.rs:5`; cite a symbol instead, "
                "as `symbol` (`path/to/file`)",
            ],
        )

    def test_exempts_external_repository_citations(self) -> None:
        self.assertEqual(
            self.check(
                """\
                Upstream `Lean.Kernel.Environment.replay`
                (`src/lean/Lean/Replay.lean:77, 186`) is exempt.
                """
            ),
            [],
        )

    def test_external_prefix_does_not_exempt_other_paths(self) -> None:
        self.assertEqual(
            self.check("`Replay.lean:77` and `lean/Lean/Replay.lean:77`\n"),
            [
                "1: line locator `Replay.lean:77`; cite a symbol instead, "
                "as `symbol` (`path/to/file`)",
                "1: line locator `lean/Lean/Replay.lean:77`; cite a symbol "
                "instead, as `symbol` (`path/to/file`)",
            ],
        )

    def test_ignores_non_locators(self) -> None:
        self.assertEqual(
            self.check(
                """\
                `ci-core` (`NestedBwrap`), `5b` (`leanexport`),
                `TrustedBoundary.lean` (`verifyMirWpCoreTheorems`),
                `lib.rs` (`trusted/foo/src/lib.rs`), `cargo test` (`libtest`),
                `elf/dl-load.c:_dl_map_object`, `https://example.com:443/a.rs`,
                and `v4.34.1` (`foundation-lock.json`) are not locators.

                ```text
                fenced.rs:10 and `nope` (`trusted/foo/src/lib.rs`)
                ```
                """
            ),
            [],
        )

    def test_main_reports_findings_and_exit_code(self) -> None:
        good = self.write(
            "anneal/docs/good.md", "`guard_dir` (`trusted/foo/`)\n"
        )
        bad = self.write("anneal/docs/bad.md", "`lib.rs:1`\n")
        args = ["--anneal-root", str(self.anneal)]
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            self.assertEqual(check_doc_locators.main([*args, str(good)]), 0)
            self.assertEqual(
                check_doc_locators.main([*args, str(good), str(bad)]), 1
            )
        self.assertEqual(
            stderr.getvalue(),
            f"{bad}:1: line locator `lib.rs:1`; cite a symbol instead, "
            "as `symbol` (`path/to/file`)\n",
        )


class RealDocTest(unittest.TestCase):
    def test_default_docs_pass_at_head(self) -> None:
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            code = check_doc_locators.main([])
        self.assertEqual(code, 0, stderr.getvalue())

    def test_real_doc_symbol_locators_are_checked(self) -> None:
        root = check_doc_locators.ANNEAL_ROOT
        roots = (root, root.parent)
        text = (root / check_doc_locators.DEFAULT_DOCS[0]).read_text()
        sym = "`validate_toolchain_mount_dir`"
        self.assertIn(sym, text)
        with tempfile.TemporaryDirectory() as tmp:
            doc = Path(tmp) / "doc.md"
            doc.write_text(text.replace(sym, "`no_such_symbol_xyz`", 1))
            findings = check_doc_locators.check_doc(doc, roots)
        self.assertEqual(len(findings), 1, findings)
        self.assertIn("symbol `no_such_symbol_xyz` does not occur", findings[0])


if __name__ == "__main__":
    unittest.main()
