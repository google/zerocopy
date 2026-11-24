# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `anneal/ci/check_todo.sh`."""

from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parent / "check_todo.sh"
MARKER = "T" + "ODO"
DISABLE = f"{MARKER}-check-disable"
ENABLE = f"{MARKER}-check-enable"


def run_git(repo: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            "git",
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.fsmonitor=false",
            *args,
        ],
        cwd=repo,
        capture_output=True,
        text=True,
        check=True,
    )


class CheckTodoTests(unittest.TestCase):
    def make_repo(self, tmp: str) -> tuple[Path, Path, Path]:
        """Create a minimal Git repo with `anneal/ci/check_todo.sh`."""
        root = Path(tmp) / "repo"
        anneal = root / "anneal"
        ci_dir = anneal / "ci"
        ci_dir.mkdir(parents=True)

        script_copy = ci_dir / "check_todo.sh"
        shutil.copyfile(SCRIPT, script_copy)
        script_copy.chmod(script_copy.stat().st_mode | stat.S_IXUSR)

        (root / "README.md").write_text("root readme\n", encoding="utf-8")
        (anneal / "README.md").write_text("anneal readme\n", encoding="utf-8")

        run_git(root, "init", "-q", "-b", "main")
        run_git(root, "config", "user.name", "Test")
        run_git(root, "config", "user.email", "test@example.com")
        run_git(root, "add", ".")
        run_git(root, "commit", "-qm", "Initial commit")
        return root, anneal, script_copy

    def run_check(
        self, script: Path, *args: str, cwd: Path
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [str(script), *args],
            cwd=cwd,
            input="",
            capture_output=True,
            text=True,
            check=False,
        )

    def test_clean_repo_passes(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-clean-") as tmp:
            _, anneal, script = self.make_repo(tmp)
            res = self.run_check(script, cwd=anneal)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_commit_message_cannot_use_disable_directive(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-msg-") as tmp:
            root, anneal, script = self.make_repo(tmp)
            run_git(root, "checkout", "-qb", "feature")
            (anneal / "clean.txt").write_text("clean\n", encoding="utf-8")
            run_git(root, "add", "anneal/clean.txt")
            run_git(
                root,
                "commit",
                "-qm",
                f"Allow {DISABLE}\n\n{MARKER}: sneak past CI\n",
            )

            res = self.run_check(script, cwd=anneal)
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("COMMIT_MESSAGE(", res.stderr)
            self.assertIn(f"{MARKER}: sneak past CI", res.stderr)

    def test_commit_message_with_only_disable_directive_fails(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-dir-") as tmp:
            root, anneal, script = self.make_repo(tmp)
            run_git(root, "checkout", "-qb", "feature")
            # Include a valid disabled marker in a source file too so the
            # source-file loop also runs and must preserve exit_code=1.
            (anneal / "doc.md").write_text(
                f"<!-- {DISABLE} -->\n{MARKER}(#123): tracked\n"
                f"<!-- {ENABLE} -->\n",
                encoding="utf-8",
            )
            run_git(root, "add", "anneal/doc.md")
            run_git(root, "commit", "-qm", f"Mention {DISABLE} in commit")

            res = self.run_check(script, cwd=anneal)
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("COMMIT_MESSAGE(", res.stderr)
            self.assertIn(DISABLE, res.stderr)

    def test_nonexistent_and_empty_path_args_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-missing-") as tmp:
            _, anneal, script = self.make_repo(tmp)

            missing = self.run_check(script, "nonexistent.rs", cwd=anneal)
            self.assertNotEqual(missing.returncode, 0, missing.stdout)
            self.assertIn("nonexistent.rs", missing.stderr)

            empty = self.run_check(script, "", cwd=anneal)
            self.assertNotEqual(empty.returncode, 0, empty.stdout)
            self.assertIn("must not be empty", empty.stderr)

    def test_relative_path_arg_resolves_against_caller_pwd(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-pwd-") as tmp:
            root, anneal, script = self.make_repo(tmp)
            # Put a bare marker in the parent root README while keeping
            # `anneal/README.md` clean so resolving relative to `anneal/`
            # instead of caller `$PWD` would miss the violation.
            (root / "README.md").write_text(
                f"{MARKER}: root marker\n", encoding="utf-8"
            )

            from_root_bad = self.run_check(script, "README.md", cwd=root)
            self.assertEqual(
                from_root_bad.returncode,
                1,
                from_root_bad.stdout + from_root_bad.stderr,
            )
            self.assertIn(f"{MARKER}: root marker", from_root_bad.stderr)

            from_root_good = self.run_check(
                script, "anneal/README.md", cwd=root
            )
            self.assertEqual(
                from_root_good.returncode,
                0,
                from_root_good.stdout + from_root_good.stderr,
            )

            from_ci_subdir = self.run_check(
                script, "../README.md", cwd=anneal / "ci"
            )
            self.assertEqual(
                from_ci_subdir.returncode,
                0,
                from_ci_subdir.stdout + from_ci_subdir.stderr,
            )

    def test_source_disable_enable_and_vendor_exclusion(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-src-") as tmp:
            root, anneal, script = self.make_repo(tmp)
            run_git(root, "checkout", "-qb", "feature")
            vendor_file = anneal / "vendor/dep/lib.rs"
            vendor_file.parent.mkdir(parents=True)
            vendor_file.write_text(
                f"// {MARKER}: upstream vendor note\n", encoding="utf-8"
            )

            # Wrapped marker with issue citation passes (both dirty and
            # committed under `anneal/vendor/`).
            exempt = anneal / "exempt.rs"
            exempt.write_text(
                f"// {DISABLE}\n// {MARKER}(#123): tracked follow-up\n"
                f"// {ENABLE}\n",
                encoding="utf-8",
            )
            res = self.run_check(script, cwd=anneal)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

            run_git(root, "add", "anneal/vendor/dep/lib.rs", "anneal/exempt.rs")
            run_git(root, "commit", "-qm", "Add committed vendor fixture")
            res_committed = self.run_check(script, cwd=anneal)
            self.assertEqual(
                res_committed.returncode,
                0,
                res_committed.stdout + res_committed.stderr,
            )

            # A committed bare marker outside `vendor/` on a clean working tree
            # must be caught (`rc = 1`), ensuring the committed-tree pathspec
            # exclusion never fails open.
            bad_committed = anneal / "src/bad.rs"
            bad_committed.parent.mkdir(parents=True)
            bad_committed.write_text(
                f"// {MARKER}: bare committed non-vendor marker\n",
                encoding="utf-8",
            )
            run_git(root, "add", "anneal/src/bad.rs")
            run_git(root, "commit", "-qm", "Add committed non-vendor marker")
            res_bad_clean = self.run_check(script, cwd=anneal)
            self.assertEqual(
                res_bad_clean.returncode,
                1,
                res_bad_clean.stdout + res_bad_clean.stderr,
            )
            self.assertIn(
                "bare committed non-vendor marker", res_bad_clean.stderr
            )
            run_git(root, "reset", "-q", "--hard", "HEAD~1")

            # A bare marker after re-enabling (even with `(#123):`) fails.
            exempt.write_text(
                f"// {DISABLE}\n// {MARKER}(#123): tracked follow-up\n"
                f"// {ENABLE}\n// {MARKER}(#123): unexempt after enable\n",
                encoding="utf-8",
            )
            res_after = self.run_check(script, cwd=anneal)
            self.assertEqual(
                res_after.returncode, 1, res_after.stdout + res_after.stderr
            )
            self.assertIn("unexempt after enable", res_after.stderr)

    def test_git_grep_operational_error_fails_closed(self):
        with tempfile.TemporaryDirectory(prefix="anneal-todo-outside-") as tmp:
            _, anneal, script = self.make_repo(tmp)
            outside = Path(tmp) / "outside.txt"
            outside.write_text("clean external file\n", encoding="utf-8")

            res = self.run_check(script, str(outside), cwd=anneal)
            self.assertNotEqual(res.returncode, 0, res.stdout)
            self.assertIn("outside repository", res.stderr)


if __name__ == "__main__":
    unittest.main()
