#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tests for `audit_rustc_workarounds.py`."""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import audit_rustc_workarounds as arw  # noqa: E402
import check_pr_hygiene as cph  # noqa: E402

SCRIPT = Path(__file__).resolve().parent / "audit_rustc_workarounds.py"
# Built from the split constant so this file holds no literal tag.
T = cph.WORKAROUND_TAG
SHA = "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"


def messages(path: str, text: str) -> list[str]:
    return [f.message for f in cph.scan_workarounds(path, text)[1]]


class ScanTextTests(unittest.TestCase):
    def test_well_formed_anchors_in_each_comment_syntax(self):
        cases = {
            "anneal/a.rs": f"    // {T}(#4364): codegen rewrites calls.\n",
            "anneal/b.rs": f"/// {T}(#1): doc form\n//! {T}(#2): inner\n",
            "anneal/c.py": f"# {T}(#12): python\n",
            "anneal/d.sh": f"\t# {T}(#3): shell\n",
            "anneal/e.nix": f"  # {T}(#4): nix\n",
            "anneal/f.toml": f"# {T}(#5): toml\n",
            "anneal/g.yml": f"# {T}(#6): yaml\n",
            "anneal/h.yaml": f"# {T}(#7): yaml\n",
            "anneal/i.lean": f"-- {T}(#8): lean\n",
        }
        for path, text in cases.items():
            with self.subTest(path=path):
                anchors, findings = cph.scan_workarounds(path, text)
                self.assertEqual(findings, [])
                self.assertTrue(anchors)
        anchors, _ = cph.scan_workarounds("anneal/a.rs", cases["anneal/a.rs"])
        self.assertEqual(anchors, [cph.WorkaroundAnchor(
            "anneal/a.rs", 1, 4364, "codegen rewrites calls.")])

    def test_line_numbers_and_unrelated_text(self):
        text = (f"fn f() {{}}\n// RUSTC_STD_INTERNAL_SYMBOL is fine\n"
                f"// {T}(#9): third line\n")
        anchors, findings = cph.scan_workarounds("anneal/x.rs", text)
        self.assertEqual(findings, [])
        self.assertEqual([(a.line, a.issue) for a in anchors], [(3, 9)])

    def test_pending_fails_closed(self):
        msgs = messages("anneal/x.rs", f"// {T}(#PENDING): not filed yet\n")
        self.assertEqual(len(msgs), 1)
        self.assertIn("#PENDING", msgs[0])

    def test_malformed_references(self):
        for ref in ("#0", "#012", "4364", "#", "#12a", "#pending", "#1 ",
                    "PENDING", "#1234567890"):
            with self.subTest(ref=ref):
                self.assertEqual(
                    len(messages("anneal/x.rs", f"// {T}({ref}): s\n")), 1)

    def test_missing_or_empty_summary(self):
        for tail in ("", ":", ": ", ":summary", " : summary", ":   \t"):
            with self.subTest(tail=tail):
                msgs = messages("anneal/x.rs", f"// {T}(#1){tail}\n")
                self.assertEqual(len(msgs), 1, msgs)

    def test_tag_must_open_its_own_comment_line(self):
        for line in (
            f"let x = 1; // {T}(#1): trailing\n",
            f"//{T}(#1): no space\n",
            f'let s = "{T}(#1): in a string";\n',
            f"// See {T}(#1): mid-comment\n",
            f"//// {T}(#1): four slashes\n",
            f"/* {T}(#1): block */\n",
        ):
            with self.subTest(line=line):
                self.assertEqual(len(messages("anneal/x.rs", line)), 1)

    def test_comment_marker_must_match_the_file_type(self):
        self.assertIn("`#` is not a comment marker",
                      messages("anneal/x.rs", f"# {T}(#1): s\n")[0])
        self.assertIn("`//` is not a comment marker",
                      messages("anneal/x.py", f"// {T}(#1): s\n")[0])
        self.assertIn("`#` is not a comment marker",
                      messages("anneal/x.lean", f"# {T}(#1): s\n")[0])
        self.assertIn("`--` is not a comment marker",
                      messages("anneal/x.nix", f"-- {T}(#1): s\n")[0])

    def test_misspelled_tags_and_duplicates_are_flagged(self):
        misspelled = T.replace("-", "_")
        joined = T.replace("-", "")
        for line in (f"// {misspelled}(#1): s\n", f"// {joined}(#1): s\n"):
            with self.subTest(line=line):
                self.assertEqual(len(messages("anneal/x.rs", line)), 1)
        self.assertIn("more than one", messages(
            "anneal/x.rs", f"// {T}(#1): also {T}(#2): s\n")[0])

    def test_lowercase_label_text_is_not_a_tag(self):
        self.assertEqual(messages(
            "anneal/x.rs", "// Filed as [anneal][rustc-workaround].\n"), [])


class ScopeTests(unittest.TestCase):
    def test_scope(self):
        self.assertTrue(cph.workaround_in_scope("anneal/trusted/rustc-capture/src/x.rs"))
        self.assertTrue(cph.workaround_in_scope("anneal/ci/x.py"))
        self.assertFalse(cph.workaround_in_scope("anneal/docs/rustc-workarounds.md"))
        self.assertFalse(cph.workaround_in_scope("anneal/vendor/lean-miri/x.lean"))
        self.assertFalse(cph.workaround_in_scope("src/lib.rs"))
        self.assertFalse(cph.workaround_in_scope("anneal/README"))

    def test_own_sources_hold_no_literal_tag(self):
        for path in (SCRIPT, SCRIPT.with_name("check_pr_hygiene.py"),
                     Path(__file__).resolve()):
            with self.subTest(path=path.name):
                rel = f"anneal/ci/{path.name}"
                anchors, findings = cph.scan_workarounds(
                    rel, path.read_text(encoding="utf-8"))
                self.assertEqual((anchors, findings), ([], []))


class BumpTableTests(unittest.TestCase):
    def test_groups_by_issue_and_escapes_cells(self):
        anchors = [
            cph.WorkaroundAnchor("anneal/b.rs", 7, 20, "second"),
            cph.WorkaroundAnchor("anneal/a.rs", 3, 4, "pipe | here"),
            cph.WorkaroundAnchor("anneal/c.rs", 9, 20, "second"),
            cph.WorkaroundAnchor("anneal/d.rs", 1, 20, "third"),
        ]
        table = arw.bump_table(anchors, "h" * 40, SHA)
        rows = [ln for ln in table.splitlines() if ln.startswith("| #")]
        self.assertEqual(rows, [
            "| #4 | `anneal/a.rs:3` | pipe \\| here |  |  |",
            "| #20 | `anneal/b.rs:7`<br>`anneal/c.rs:9`<br>`anneal/d.rs:1` "
            "| second<br>third |  |  |",
        ])
        self.assertIn(f"compiler pin `{SHA}`", table)
        self.assertIn("4 anchor(s) across 2 issue(s)", table)

    def test_empty_inventory_and_unknown_pin(self):
        table = arw.bump_table([], "h" * 40, None)
        self.assertIn("compiler pin unknown", table)
        self.assertIn("| none |", table)


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


class CliTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="anneal-rustc-wa-")
        self.repo = Path(self._tmp.name) / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q")
        self.write("anneal/trusted/rustc-capture/src/ir.rs",
                   f'pub const COMPILER_COMMIT: &str = "{SHA}";\n')
        self.write("anneal/trusted/rustc-capture/src/a.rs",
                   f"// {T}(#4364): first\nfn a() {{}}\n")
        self.write("anneal/ci/b.py", f"# {T}(#4365): second\n")
        self.write("anneal/docs/rustc-workarounds.md",
                   f"Example: `// {T}(#PENDING): s`\n")
        self.write("anneal/vendor/lean-miri/x.lean", f"-- {T}(#PENDING): s\n")
        self.write("src/lib.rs", f"// {T}(#PENDING): s\n")
        self.commit()

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def write(self, rel: str, text: str) -> None:
        path = self.repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def commit(self) -> str:
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "--allow-empty", "-m", "c")
        return git(self.repo, "rev-parse", "HEAD").strip()

    def run_cli(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
             str(self.repo), *args],
            capture_output=True, text=True, check=False)

    def test_clean_json_report(self):
        res = self.run_cli("--json")
        self.assertEqual(res.returncode, 0, res.stderr)
        report = json.loads(res.stdout)
        self.assertEqual(report["schema"], arw.SCHEMA)
        self.assertTrue(report["ok"])
        self.assertEqual(report["compiler_commit"], SHA)
        self.assertEqual(
            [(a["path"], a["issue"]) for a in report["anchors"]],
            [("anneal/ci/b.py", 4365),
             ("anneal/trusted/rustc-capture/src/a.rs", 4364)])
        self.assertEqual(report["head"], git(
            self.repo, "rev-parse", "HEAD").strip())

    def test_text_mode_and_bump_table(self):
        res = self.run_cli()
        self.assertEqual(res.returncode, 0)
        self.assertIn("2 well-formed", res.stdout)
        res = self.run_cli("--bump")
        self.assertEqual(res.returncode, 0)
        self.assertIn("| #4364 | `anneal/trusted/rustc-capture/src/a.rs:1` "
                      "| first |  |  |", res.stdout)
        self.assertIn("| #4365 | `anneal/ci/b.py:1` | second |", res.stdout)

    def test_findings_exit_1_and_bump_still_prints(self):
        self.write("anneal/ci/c.sh", f"# {T}(#PENDING): later\n")
        self.commit()
        res = self.run_cli("--json")
        self.assertEqual(res.returncode, 1)
        report = json.loads(res.stdout)
        self.assertFalse(report["ok"])
        self.assertEqual([(f["path"], f["line"]) for f in report["findings"]],
                         [("anneal/ci/c.sh", 1)])
        res = self.run_cli("--bump")
        self.assertEqual(res.returncode, 1)
        self.assertIn("| #4364 |", res.stdout)
        self.assertIn("anneal/ci/c.sh:1", res.stderr)

    def test_scans_the_committed_tree_not_the_worktree(self):
        first = git(self.repo, "rev-parse", "HEAD").strip()
        self.write("anneal/ci/d.py", f"# {T}(#PENDING): uncommitted\n")
        self.assertEqual(self.run_cli().returncode, 0)
        self.commit()
        self.assertEqual(self.run_cli().returncode, 1)
        self.assertEqual(self.run_cli("--head", first).returncode, 0)

    def test_symlinks_are_skipped(self):
        target = self.repo / "outside.rs"
        target.write_text(f"// {T}(#PENDING): s\n", encoding="utf-8")
        (self.repo / "anneal/ci/link.rs").symlink_to(target)
        self.commit()
        res = self.run_cli("--json")
        self.assertEqual(res.returncode, 0, res.stdout)

    def test_git_errors_exit_2(self):
        res = self.run_cli("--head", "no-such-ref", "--json")
        self.assertEqual(res.returncode, 2)
        self.assertFalse(json.loads(res.stdout)["ok"])
        res = self.run_cli("--head", "no-such-ref")
        self.assertEqual(res.returncode, 2)
        self.assertIn("error:", res.stderr)

    def test_bump_and_json_are_exclusive(self):
        self.assertEqual(self.run_cli("--bump", "--json").returncode, 2)


if __name__ == "__main__":
    unittest.main()
