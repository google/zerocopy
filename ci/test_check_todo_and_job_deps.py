# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/check_todo.sh` and `ci/check_job_dependencies.sh`."""

import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
import unittest
from unittest import mock


CI_DIR = Path(__file__).resolve().parent
REPO_ROOT = CI_DIR.parent
TODO_SCRIPT = CI_DIR / "check_todo.sh"
JOB_DEPS_SCRIPT = CI_DIR / "check_job_dependencies.sh"

MARKER = "T" + "ODO"
DISABLE = f"{MARKER}-check-disable"
ENABLE = f"{MARKER}-check-enable"

VALID_MULTI_PR = """\
on:
  pull_request:
jobs:
  build:
    runs-on: ubuntu-latest
    steps: []
  lint:
    runs-on: ubuntu-latest
    steps: []
  all-jobs-succeed:
    runs-on: ubuntu-latest
    needs: [build, lint]
    steps: []
"""


def hermetic_git_env() -> dict[str, str]:
    """Return an env stripped of ambient `GIT_*` and user Git configs."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env["GIT_CONFIG_GLOBAL"] = os.devnull
    env["GIT_CONFIG_NOSYSTEM"] = "1"
    return env


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
        env=hermetic_git_env(),
        capture_output=True,
        text=True,
        check=True,
    )


def copy_executable(src: Path, dst: Path) -> Path:
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    dst.chmod(dst.stat().st_mode | stat.S_IXUSR)
    return dst


class CheckTodoTests(unittest.TestCase):
    def make_tree(
        self, tmp: str, *, init_git: bool = True
    ) -> tuple[Path, Path]:
        """Create a minimal root repo tree with `ci/check_todo.sh`."""
        root = Path(tmp) / "repo"
        for sub in ("ci", "githooks", "tools", "zerocopy"):
            (root / sub).mkdir(parents=True, exist_ok=True)
            (root / sub / "clean.txt").write_text("clean\n", encoding="utf-8")

        script = copy_executable(TODO_SCRIPT, root / "ci/check_todo.sh")
        if init_git:
            run_git(root, "init", "-q", "-b", "main")
            run_git(root, "config", "user.name", "Test")
            run_git(root, "config", "user.email", "test@example.com")
            run_git(root, "add", ".")
            run_git(root, "commit", "-qm", "Initial commit")
        return root, script

    def run_check(
        self,
        script: Path,
        *args: str,
        cwd: Path,
        extra_env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        env = hermetic_git_env()
        if extra_env:
            env.update(extra_env)
        return subprocess.run(
            [str(script), *args],
            cwd=cwd,
            env=env,
            input="",
            capture_output=True,
            text=True,
            check=False,
        )

    def test_missing_rg_fails_closed(self):
        with tempfile.TemporaryDirectory(prefix="zc-norg-") as tmp:
            root, script = self.make_tree(tmp, init_git=False)
            bin_dir = Path(tmp) / "bin"
            bin_dir.mkdir()
            for tool in ("bash", "dirname", "sed"):
                path = shutil.which(tool)
                assert path is not None
                (bin_dir / tool).symlink_to(path)
            res = self.run_check(
                script, cwd=root, extra_env={"PATH": str(bin_dir)}
            )
        self.assertNotEqual(res.returncode, 0, res.stdout)
        self.assertIn("rg", res.stderr)

    @unittest.skipIf(shutil.which("rg") is None, "rg is required on PATH")
    def test_clean_tree_and_disable_enable_pass(self):
        with tempfile.TemporaryDirectory(prefix="zc-todo-clean-") as tmp:
            root, script = self.make_tree(tmp)
            exempt = root / "zerocopy/exempt.rs"
            exempt.write_text(
                f"// {DISABLE}\n// {MARKER}(#123): tracked\n// {ENABLE}\n",
                encoding="utf-8",
            )
            res = self.run_check(script, cwd=root)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

            # A marker after re-enabling must still fail.
            exempt.write_text(
                f"// {DISABLE}\n// {MARKER}(#123): tracked\n"
                f"// {ENABLE}\n// {MARKER}: unexempt\n",
                encoding="utf-8",
            )
            bad = self.run_check(script, cwd=root)
            self.assertEqual(bad.returncode, 1, bad.stdout + bad.stderr)
            self.assertIn("unexempt", bad.stderr)

    @unittest.skipIf(shutil.which("rg") is None, "rg is required on PATH")
    def test_marker_and_commit_message_fail(self):
        with tempfile.TemporaryDirectory(prefix="zc-todo-fail-") as tmp:
            root, script = self.make_tree(tmp)
            run_git(root, "checkout", "-qb", "feature")
            (root / "zerocopy/lib.rs").write_text(
                f"// {MARKER}: fix me\n", encoding="utf-8"
            )
            run_git(root, "add", "zerocopy/lib.rs")
            run_git(
                root,
                "commit",
                "-qm",
                f"Allow {DISABLE}\n\n{MARKER}: in commit message\n",
            )

            res = self.run_check(script, cwd=root)
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("COMMIT_MESSAGE(", res.stderr)
            self.assertIn("in commit message", res.stderr)
            self.assertIn("fix me", res.stderr)

    @unittest.skipIf(shutil.which("rg") is None, "rg is required on PATH")
    def test_gitless_tree_passes_clean_and_fails_marker(self):
        with tempfile.TemporaryDirectory(prefix="zc-todo-nogit-") as tmp:
            root, script = self.make_tree(tmp, init_git=False)
            self.assertFalse((root / ".git").exists())

            ok = self.run_check(script, cwd=root)
            self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)

            (root / "tools/dirty.rs").write_text(
                f"// {MARKER}: unmerged\n", encoding="utf-8"
            )
            bad = self.run_check(script, cwd=root)
            self.assertEqual(bad.returncode, 1, bad.stdout + bad.stderr)
            self.assertIn("unmerged", bad.stderr)

    @unittest.skipIf(shutil.which("rg") is None, "rg is required on PATH")
    def test_rg_operational_error_fails_closed(self):
        for init_git in (True, False):
            with self.subTest(init_git=init_git):
                with tempfile.TemporaryDirectory(prefix="zc-todo-rgerr-") as t:
                    root, script = self.make_tree(t, init_git=init_git)
                    bad = self.run_check(script, "nonexistent.rs", cwd=root)
                    self.assertNotEqual(bad.returncode, 0, bad.stdout)
                    self.assertIn("nonexistent.rs", bad.stderr)

                    empty = self.run_check(script, "", cwd=root)
                    self.assertNotEqual(empty.returncode, 0, empty.stdout)
                    self.assertIn("must not be empty", empty.stderr)

    @unittest.skipIf(shutil.which("rg") is None, "rg is required on PATH")
    def test_git_operational_errors_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="zc-todo-giterr-") as tmp:
            root, script = self.make_tree(tmp, init_git=True)
            outside = Path(tmp) / "outside.txt"
            outside.write_text("clean external file\n", encoding="utf-8")

            bad_grep = self.run_check(script, str(outside), cwd=root)
            self.assertNotEqual(bad_grep.returncode, 0, bad_grep.stdout)
            self.assertIn("outside repository", bad_grep.stderr)

            # Corrupt `git log` and `git rev-parse` via shim to verify git
            # operational errors inside `.git`-present repos fail closed.
            shim_dir = Path(tmp) / "shim"
            shim_dir.mkdir()
            real_git = shutil.which("git")
            assert real_git is not None
            git_shim = shim_dir / "git"
            git_shim.write_text(
                "#!/usr/bin/env python3\n"
                "import os, subprocess, sys\n"
                "fail_cmd = os.environ.get('FAIL_GIT_CMD', '')\n"
                "if len(sys.argv) > 1 and sys.argv[1] == fail_cmd:\n"
                "    sys.stderr.write(f'simulated git {fail_cmd} failure\\n')\n"
                "    sys.exit(128)\n"
                f"sys.exit(subprocess.call([{real_git!r}, *sys.argv[1:]]))\n",
                encoding="utf-8",
            )
            git_shim.chmod(stat.S_IRWXU)
            shim_path = f"{shim_dir}:{os.environ.get('PATH', '')}"

            bad_log = self.run_check(
                script,
                cwd=root,
                extra_env={"PATH": shim_path, "FAIL_GIT_CMD": "log"},
            )
            self.assertNotEqual(bad_log.returncode, 0, bad_log.stdout)
            self.assertIn("simulated git log failure", bad_log.stderr)

            self.assertTrue((root / ".git").exists())
            bad_rev = self.run_check(
                script,
                cwd=root,
                extra_env={"PATH": shim_path, "FAIL_GIT_CMD": "rev-parse"},
            )
            self.assertNotEqual(bad_rev.returncode, 0, bad_rev.stdout)
            self.assertIn("simulated git rev-parse failure", bad_rev.stderr)

    @unittest.skipIf(shutil.which("rg") is None, "rg is required on PATH")
    def test_hermetic_git_env_isolates_sentinel_repo(self):
        with tempfile.TemporaryDirectory(prefix="zc-todo-sentinel-") as tmp:
            sentinel = Path(tmp) / "sentinel.git"
            subprocess.run(
                ["git", "init", "--bare", "-q", str(sentinel)],
                env=hermetic_git_env(),
                capture_output=True,
                text=True,
                check=True,
            )
            cfg_before = (sentinel / "config").read_text(encoding="utf-8")
            head_before = (sentinel / "HEAD").read_text(encoding="utf-8")
            refs_before = sorted(
                p.relative_to(sentinel).as_posix()
                for p in (sentinel / "refs").rglob("*")
            )

            with mock.patch.dict(
                os.environ,
                {
                    "GIT_DIR": str(sentinel),
                    "GIT_WORK_TREE": str(sentinel),
                },
            ):
                root, script = self.make_tree(tmp, init_git=True)
                ok = self.run_check(script, cwd=root)
                self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)

                (root / "tools/bad.rs").write_text(
                    f"// {MARKER}: isolated\n", encoding="utf-8"
                )
                bad = self.run_check(script, cwd=root)
                self.assertEqual(bad.returncode, 1, bad.stdout + bad.stderr)
                self.assertIn("isolated", bad.stderr)

            self.assertEqual(
                (sentinel / "config").read_text(encoding="utf-8"), cfg_before
            )
            self.assertEqual(
                (sentinel / "HEAD").read_text(encoding="utf-8"), head_before
            )
            refs_after = sorted(
                p.relative_to(sentinel).as_posix()
                for p in (sentinel / "refs").rglob("*")
            )
            self.assertEqual(refs_after, refs_before)
            cnt = run_git(root, "rev-list", "--count", "HEAD").stdout.strip()
            self.assertEqual(cnt, "1")

    @unittest.skipIf(shutil.which("rg") is None, "rg is required on PATH")
    def test_relative_args_and_vendor_exclusion(self):
        with tempfile.TemporaryDirectory(prefix="zc-todo-rel-") as tmp:
            root, script = self.make_tree(tmp, init_git=True)
            vendor = root / "zerocopy/vendor/dep.rs"
            vendor.parent.mkdir(parents=True)
            vendor.write_text(f"// {MARKER}: vendored\n", encoding="utf-8")
            run_git(root, "add", "zerocopy/vendor/dep.rs")
            run_git(root, "commit", "-qm", "Add vendored file")

            ok = self.run_check(script, cwd=root)
            self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)

            # Relative path argument from subdirectory resolves against caller.
            (root / "anneal").mkdir()
            (root / "anneal/bad.rs").write_text(
                f"// {MARKER}: anneal explicit\n", encoding="utf-8"
            )
            bad = self.run_check(script, "bad.rs", cwd=root / "anneal")
            self.assertEqual(bad.returncode, 1, bad.stdout + bad.stderr)
            self.assertIn("anneal explicit", bad.stderr)


class CheckJobDependenciesTests(unittest.TestCase):
    def run_synthetic(
        self,
        *,
        workflows: dict[str, str] | None = None,
        extra_github_files: dict[str, str] | None = None,
        extra_env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory(prefix="zc-job-deps-") as tmp:
            root = Path(tmp) / "repo"
            wf_dir = root / ".github/workflows"
            wf_dir.mkdir(parents=True)
            script = copy_executable(
                JOB_DEPS_SCRIPT, root / "ci/check_job_dependencies.sh"
            )

            wfs = (
                {"ci.yml": VALID_MULTI_PR}
                if workflows is None
                else workflows
            )
            for name, content in wfs.items():
                path = wf_dir / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8")

            for rel, content in (extra_github_files or {}).items():
                path = root / ".github" / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8")

            env = os.environ.copy()
            env.pop("GITHUB_STEP_SUMMARY", None)
            if extra_env:
                env.update(extra_env)

            return subprocess.run(
                [str(script)],
                cwd=root,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )

    @unittest.skipIf(shutil.which("yq") is None, "yq is required on PATH")
    def test_live_repo_workflows_pass(self):
        res = subprocess.run(
            [str(JOB_DEPS_SCRIPT)],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_missing_yq_fails_closed(self):
        bash_bin = shutil.which("bash")
        dirname_bin = shutil.which("dirname")
        assert bash_bin is not None and dirname_bin is not None
        with tempfile.TemporaryDirectory(prefix="zc-noyq-") as bin_dir:
            (Path(bin_dir) / "bash").symlink_to(bash_bin)
            (Path(bin_dir) / "dirname").symlink_to(dirname_bin)
            res = self.run_synthetic(extra_env={"PATH": bin_dir})
        self.assertNotEqual(res.returncode, 0, res.stdout)
        self.assertIn("yq is required", res.stderr)

    @unittest.skipIf(shutil.which("yq") is None, "yq is required on PATH")
    def test_valid_workflows_and_non_workflow_yaml_pass(self):
        workflows = {
            "multi_map.yml": VALID_MULTI_PR,
            "multi_seq_scalar_needs.yml": (
                "on: [push, pull_request]\n"
                "jobs:\n"
                "  build: {}\n"
                "  all-jobs-succeed:\n"
                "    needs: build\n"
            ),
            "single_scalar_pr.yml": "on: pull_request\njobs:\n  one: {}\n",
            "single_seq_pr.yml": "on: [pull_request]\njobs:\n  one: {}\n",
            "single_map_pr.yml": (
                "on:\n  pull_request:\njobs:\n  one: {}\n"
            ),
            "dispatch_multi.yml": (
                "on: workflow_dispatch\n"
                "jobs:\n"
                "  a: {}\n"
                "  b: {}\n"
            ),
            "mixed_sep_names.yml": (
                "on: pull_request\n"
                "jobs:\n"
                "  check-version: {}\n"
                "  check_actions: {}\n"
                "  all-jobs-succeed:\n"
                "    needs: [check-version, check_actions]\n"
            ),
            "call_with_gate.yml": (
                "on: workflow_call\n"
                "jobs:\n"
                "  a: {}\n"
                "  b: {}\n"
                "  all-jobs-succeed:\n"
                "    needs: [a, b]\n"
            ),
        }
        extra = {
            "dependabot.yml": "version: 2\nupdates: []\n",
            "actions/sample/action.yml": (
                "name: Sample\nruns:\n  using: composite\n"
            ),
        }
        res = self.run_synthetic(workflows=workflows, extra_github_files=extra)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    @unittest.skipIf(shutil.which("yq") is None, "yq is required on PATH")
    def test_comm_locale_invariant_on_mixed_separators(self):
        loc = subprocess.run(
            ["locale", "-a"], capture_output=True, text=True, check=False
        )
        locales = {line.strip().lower() for line in loc.stdout.splitlines()}
        if "en_us.utf8" not in locales and "en_us.utf-8" not in locales:
            self.skipTest("en_US.UTF-8 locale not installed")
        wf = (
            "on: pull_request\n"
            "jobs:\n"
            "  check-version: {}\n"
            "  check_actions: {}\n"
            "  check_fmt: {}\n"
            "  all-jobs-succeed:\n"
            "    needs: [check_actions, check_fmt]\n"
        )
        res = self.run_synthetic(
            workflows={"mixed.yml": wf},
            extra_env={"LC_ALL": "en_US.UTF-8"},
        )
        self.assertNotEqual(res.returncode, 0, res.stdout)
        self.assertIn(
            "missing dependencies on some jobs: check-version ", res.stderr
        )
        self.assertNotIn("check_actions", res.stderr)
        self.assertNotIn("not in sorted order", res.stderr)

    @unittest.skipIf(shutil.which("yq") is None, "yq is required on PATH")
    def test_malformed_and_empty_yaml_fail_closed(self):
        for label, wfs, extra in (
            ("bad_workflow", {"bad.yml": "on: [\njobs:\n  a: {}\n"}, None),
            ("empty_workflow", {"empty.yml": ""}, None),
            ("bad_non_workflow", None, {"dependabot.yml": "version: [\n"}),
        ):
            with self.subTest(case=label):
                res = self.run_synthetic(
                    workflows=wfs, extra_github_files=extra
                )
                self.assertNotEqual(res.returncode, 0, res.stdout)
                self.assertIn("failed to parse YAML", res.stderr)

    @unittest.skipIf(shutil.which("yq") is None, "yq is required on PATH")
    def test_missing_needs_and_missing_gate_fail_closed(self):
        cases = {
            "scalar_pr_missing_needs": (
                "on: pull_request\n"
                "jobs:\n"
                "  build: {}\n"
                "  lint: {}\n"
                "  all-jobs-succeed:\n"
                "    needs: [build]\n"
            ),
            "seq_pr_missing_needs": (
                "on: [push, pull_request]\n"
                "jobs:\n"
                "  build: {}\n"
                "  lint: {}\n"
                "  all-jobs-succeed:\n"
                "    needs: [build]\n"
            ),
            "call_gate_missing_needs": (
                "on: workflow_call\n"
                "jobs:\n"
                "  build: {}\n"
                "  lint: {}\n"
                "  all-jobs-succeed:\n"
                "    needs: [build]\n"
            ),
        }
        for name, content in cases.items():
            with self.subTest(case=name):
                res = self.run_synthetic(workflows={f"{name}.yml": content})
                self.assertNotEqual(res.returncode, 0, res.stdout)
                self.assertIn(
                    "missing dependencies on some jobs: lint", res.stderr
                )

        for label, wf in (
            ("map", "on:\n  pull_request:\njobs:\n  a: {}\n  b: {}\n"),
            ("seq", "on: [push, pull_request]\njobs:\n  a: {}\n  b: {}\n"),
            ("scalar", "on: pull_request\njobs:\n  a: {}\n  b: {}\n"),
        ):
            with self.subTest(missing_gate=label):
                res = self.run_synthetic(workflows={"nogate.yml": wf})
                self.assertNotEqual(res.returncode, 0, res.stdout)
                self.assertIn("missing all-jobs-succeed", res.stderr)

    @unittest.skipIf(shutil.which("yq") is None, "yq is required on PATH")
    def test_invalid_gate_needs_and_step_summary(self):
        bad_needs = {
            "omitted": (
                "on: pull_request\njobs:\n  a: {}\n  all-jobs-succeed: {}\n"
            ),
            "empty_list": (
                "on: pull_request\njobs:\n  a: {}\n"
                "  all-jobs-succeed:\n    needs: []\n"
            ),
            "non_string_entry": (
                "on: pull_request\njobs:\n  a: {}\n"
                "  all-jobs-succeed:\n    needs: [123]\n"
            ),
            "map_needs": (
                "on: pull_request\njobs:\n  a: {}\n"
                "  all-jobs-succeed:\n    needs:\n      a: b\n"
            ),
        }
        for label, wf in bad_needs.items():
            with self.subTest(case=label):
                with tempfile.NamedTemporaryFile(mode="r+") as summary:
                    res = self.run_synthetic(
                        workflows={"bad_needs.yml": wf},
                        extra_env={"GITHUB_STEP_SUMMARY": summary.name},
                    )
                    self.assertNotEqual(res.returncode, 0, res.stdout)
                    self.assertIn("all-jobs-succeed.needs", res.stderr)
                    summary.seek(0)
                    self.assertIn("all-jobs-succeed.needs", summary.read())

        missing_on = self.run_synthetic(
            workflows={"missing_on.yml": "jobs:\n  a: {}\n"}
        )
        self.assertNotEqual(missing_on.returncode, 0, missing_on.stdout)
        self.assertIn("unsupported 'on' trigger", missing_on.stderr)

    @unittest.skipIf(shutil.which("yq") is None, "yq is required on PATH")
    def test_mikefarah_yq_v4_simulated_tags(self):
        """Exercise `!!*` tag branching via a shim over host `yq`.

        Real `mikefarah/yq v4.44.1` coverage runs in CI `run-git-hooks` after
        `.github/actions/install-yq`.
        """
        real_yq = shutil.which("yq")
        self.assertIsNotNone(real_yq)
        with tempfile.TemporaryDirectory(prefix="zc-yq-shim-") as shim_tmp:
            shim_bin = Path(shim_tmp) / "yq"
            shim_bin.write_text(
                "#!/usr/bin/env python3\n"
                "import subprocess, sys\n"
                f"proc = subprocess.run([{real_yq!r}, *sys.argv[1:]], "
                "capture_output=True, text=True)\n"
                "out = proc.stdout\n"
                "if any('| type' in a for a in sys.argv[1:]):\n"
                "    mapping = {'string': '!!str', 'array': '!!seq', "
                "'object': '!!map', 'null': '!!null', 'boolean': '!!bool'}\n"
                "    out = '\\n'.join(mapping.get(x, x) "
                "for x in out.splitlines()) + ('\\n' if out else '')\n"
                "sys.stdout.write(out)\n"
                "sys.stderr.write(proc.stderr)\n"
                "sys.exit(proc.returncode)\n",
                encoding="utf-8",
            )
            shim_bin.chmod(stat.S_IRWXU)
            env_override = {"PATH": f"{shim_tmp}:{os.environ.get('PATH', '')}"}

            ok = self.run_synthetic(
                workflows={
                    "ok_seq.yml": (
                        "on: [pull_request]\n"
                        "jobs:\n"
                        "  build: {}\n"
                        "  all-jobs-succeed:\n"
                        "    needs: build\n"
                    ),
                    "ok_single.yml": (
                        "on: pull_request\njobs:\n  solo: {}\n"
                    ),
                },
                extra_env=env_override,
            )
            self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)

            bad = self.run_synthetic(
                workflows={
                    "bad.yml": (
                        "on: pull_request\n"
                        "jobs:\n"
                        "  a: {}\n"
                        "  b: {}\n"
                        "  all-jobs-succeed:\n"
                        "    needs: [a]\n"
                    )
                },
                extra_env=env_override,
            )
            self.assertNotEqual(bad.returncode, 0, bad.stdout)
            self.assertIn("missing dependencies on some jobs: b", bad.stderr)


if __name__ == "__main__":
    unittest.main()
