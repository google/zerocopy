# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `ci/scripts/check_shell_and_hooks.sh`."""

from __future__ import annotations

import ast
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest


SCRIPT = (
    Path(__file__).resolve().parent / "scripts" / "check_shell_and_hooks.sh"
)
PRE_PUSH_TEMPLATE = (
    "#!/usr/bin/env bash\n"
    "set -eo pipefail\n"
    "./ci/sample.sh &\n"
    "SAMPLE_PID=$!\n"
    "./zerocopy/ci/check_all_toolchains_tested.sh >/dev/null &\n"
    "TOOLCHAINS_PID=$!\n"
    "python3 -I -B ./ci/test_shell_and_hooks.py >/dev/null &\n"
    "SHELL_HOOKS_TEST_PID=$!\n"
    "wait $SAMPLE_PID\n"
    "wait $TOOLCHAINS_PID\n"
    "wait $SHELL_HOOKS_TEST_PID\n"
)
CLEAN_SCRIPT = "#!/usr/bin/env bash\nset -euo pipefail\nexit 0\n"
ALLOWLIST_PACKAGING_SCRIPT = (
    "#!/usr/bin/env bash\nset -euo pipefail\n"
    "if ! tar -xOzf a b | \\\n"
    "  grep -Fx -e '// SPDX-License-Identifier: "
    "BSD-2-Clause OR Apache-2.0 OR MIT' \\\n"
    "    -e '/* SPDX-License-Identifier: "
    "BSD-2-Clause OR Apache-2.0 OR MIT */' \\\n"
    "    > /dev/null; then\n  exit 1\nfi\n"
)


def _extract_allowlist() -> set[tuple[str, str]]:
    text = SCRIPT.read_text(encoding="utf-8")
    m = re.search(r"^ALLOWLIST[^=]*=\s*(\{.*?\n\})$", text, re.M | re.S)
    assert m is not None, (
        "ALLOWLIST block not found in check_shell_and_hooks.sh"
    )
    raw = ast.literal_eval(m.group(1))
    assert isinstance(raw, set) and raw
    return raw


class CheckShellAndHooksTests(unittest.TestCase):
    def _build_fixture_repo(
        self,
        tmp: str,
        script_body: str,
        *,
        pre_push_body: str | None = None,
    ) -> Path:
        root = Path(tmp) / "repo"
        (root / "ci" / "scripts").mkdir(parents=True)
        (root / "githooks").mkdir()
        (root / "zerocopy" / "ci").mkdir(parents=True)

        target_script = root / "ci" / "scripts" / "check_shell_and_hooks.sh"
        shutil.copyfile(SCRIPT, target_script)
        target_script.chmod(target_script.stat().st_mode | stat.S_IXUSR)

        sample = root / "ci" / "sample.sh"
        sample.write_text(script_body, encoding="utf-8")
        sample.chmod(sample.stat().st_mode | stat.S_IXUSR)

        # Dummy marker so `check_shell_and_hooks.sh`'s `ci/*.py` coverage check
        # succeeds hermetically without reading outside `ci/scripts/`.
        dummy_py = root / "ci" / "test_shell_and_hooks.py"
        dummy_py.write_text("# dummy\n", encoding="utf-8")

        cargo_sh = root / "zerocopy" / "cargo.sh"
        cargo_sh.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
        cargo_sh.chmod(cargo_sh.stat().st_mode | stat.S_IXUSR)

        for rel, body in (
            (
                "zerocopy/ci/check_all_toolchains_tested.sh",
                CLEAN_SCRIPT,
            ),
            ("zerocopy/ci/check_packaging.sh", ALLOWLIST_PACKAGING_SCRIPT),
        ):
            p = root / rel
            p.write_text(body, encoding="utf-8")
            p.chmod(p.stat().st_mode | stat.S_IXUSR)

        pre_push = root / "githooks" / "pre-push"
        hook_txt = pre_push_body or PRE_PUSH_TEMPLATE
        pre_push.write_text(hook_txt, encoding="utf-8")
        pre_push.chmod(pre_push.stat().st_mode | stat.S_IXUSR)
        return root

    def _run_check(
        self,
        repo: Path,
        *,
        args: tuple[str, ...] = (),
        shellcheck_exit: int | None = None,
    ) -> subprocess.CompletedProcess[str]:
        # Build a minimal isolated PATH so missing vs failing `shellcheck` is
        # explicitly controlled by `shellcheck_exit`.
        bin_dir = repo / "_bin"
        bin_dir.mkdir(exist_ok=True)
        for tool in ("bash", "grep", "egrep", "fgrep", "dirname", "env"):
            found = shutil.which(tool)
            if found and not (bin_dir / tool).exists():
                (bin_dir / tool).symlink_to(found)
        py_link = bin_dir / "python3"
        if not py_link.exists():
            py_link.symlink_to(Path(sys.executable).resolve())
        if shellcheck_exit is not None:
            sc = bin_dir / "shellcheck"
            sc.write_text(
                f"#!/bin/sh\nexit {shellcheck_exit}\n", encoding="utf-8"
            )
            sc.chmod(sc.stat().st_mode | stat.S_IXUSR)
        env = {"PATH": str(bin_dir), "HOME": str(repo), "TERM": "dumb"}
        return subprocess.run(
            [
                "bash",
                str(repo / "ci" / "scripts" / "check_shell_and_hooks.sh"),
                *args,
            ],
            cwd=repo,
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )

    def test_piped_grep_is_fail_closed_with_allowlist(self) -> None:
        clean_body = (
            "#!/usr/bin/env bash\n"
            "set -euo pipefail\n"
            "# git rev-list HEAD | grep -Fxq deadbeef\n"
            "false || grep -q fallback\n"
            "grep -Fxq deadbeef file.txt\n"
            'grep -Fxq -e "foo" <<< "$var"\n'
            "grep -E '^pat$' file.txt | sort\n"
            "git rev-list HEAD | sort >/dev/null\n"
            "(( 1 | 2 ))\n"
            '[[ "$x" =~ ^(foo|grep)$ ]]\n'
            "[[ a =~ x|y ]]\n"
            "grep -q file file.txt\n"
            'x="$(case "$y" in a) echo "don\'t" ;; esac)"\n'
            'x="$(echo $((1 << 2)))"\n'
            'x="$(y=${foo:-)}; echo "don\'t")"\n'
            'case "$x" in\n  case|grep) echo ok ;;\n  if) echo ok ;;\n'
            '  fi) echo ok ;;\nesac\n'
            'echo "$(cat <<\x27EOF\x27\nhello | grep -q world\nEOF\n)"\n'
        )
        with tempfile.TemporaryDirectory(prefix="zc-shell-clean-") as tmp:
            repo = self._build_fixture_repo(tmp, clean_body)
            res = self._run_check(repo)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

        for label, bad_line in (
            ("short_q", "git rev-list HEAD | grep -q deadbeef\n"),
            ("no_space_pipe", "git rev-list HEAD|grep -q deadbeef\n"),
            ("pipe_amp", "git rev-list HEAD |& grep -q deadbeef\n"),
            ("egrep_q", "git rev-list HEAD | egrep -q deadbeef\n"),
            ("fgrep_q", "git rev-list HEAD | fgrep -q deadbeef\n"),
            ("quoted_grep", 'git rev-list HEAD | "grep" -q deadbeef\n'),
            ("trailing_pipe", "git rev-list HEAD |\n  grep -q deadbeef\n"),
            (
                "trailing_pipe_comment",
                "git rev-list HEAD | # pipe\n  grep -q deadbeef\n",
            ),
            (
                "trailing_pipe_comment_line",
                "git rev-list HEAD |\n  # comment\n  grep -q deadbeef\n",
            ),
            (
                "trailing_pipe_blank_line",
                "git rev-list HEAD |\n\n  grep -q deadbeef\n",
            ),
            (
                "trailing_pipe_bs_cont",
                "git rev-list HEAD | \\\n  env FOO=1 \\\n  grep -q deadbeef\n",
            ),
            (
                "quoted_hash_before_pipe_sq",
                "git log --format='%s #%h' |\n  grep -q deadbeef\n",
            ),
            (
                "quoted_hash_before_pipe_dq",
                'printf "%s\\n" "a #b" |\n  grep -q a\n',
            ),
            (
                "quoted_hash_on_env_bs_cont",
                'git rev-list HEAD | \\\n  env MSG="a # b" \\\n'
                "  grep -q deadbeef\n",
            ),
            (
                "pipe_brace_group",
                "git rev-list HEAD | {\n  echo a\n  grep -q deadbeef\n}\n",
            ),
            (
                "pipe_subshell",
                "git rev-list HEAD | (\n  grep -q deadbeef\n)\n",
            ),
            (
                "pipe_while_body",
                "git rev-list HEAD | while read -r x; do\n"
                '  grep -q "$x"\ndone\n',
            ),
            (
                "pipe_if_body",
                "git rev-list HEAD | if true; then\n"
                "  grep -q deadbeef\nfi\n",
            ),
            (
                "pipe_heredoc_then_grep",
                "cat <<'EOF' |\nhello\nEOF\n  grep -q hello\n",
            ),
            (
                "env_u_grep_q",
                "git rev-list HEAD | env -u FOO grep -q deadbeef\n",
            ),
            (
                "command_p_grep_q",
                "git rev-list HEAD | command -p grep -q deadbeef\n",
            ),
            (
                "eval_grep_q",
                "git rev-list HEAD | eval grep -q deadbeef\n",
            ),
            (
                "sudo_grep_q",
                "git rev-list HEAD | sudo grep -q deadbeef\n",
            ),
            (
                "busybox_grep_q",
                "git rev-list HEAD | busybox grep -q deadbeef\n",
            ),
            (
                "here_string_then_piped_grep_q",
                'cat <<< "$var"\ngit log | grep -q deadbeef\n',
            ),
            (
                "here_string_fd0_then_piped_grep_q",
                "cat 0<<< x\ngit log | grep -q deadbeef\n",
            ),
            (
                "abbrev_quiet",
                "echo a | grep --quie a\n",
            ),
            (
                "dq_cmd_subst_grep_q",
                'x="$(git rev-list HEAD | grep -q deadbeef || true)"\n',
            ),
            (
                "dq_cmd_subst_case_pipe_grep_q",
                'x="$(case x in a) echo ok | grep -q ok ;; esac)"\n',
            ),
            (
                "dq_cmd_subst_pe_rparen_grep_q",
                'x="$(y=${foo:-)}; echo a | grep -q a)"\n',
            ),
            (
                "grep_piped_to_grep_q",
                "grep a file.txt | grep -q b\n",
            ),
            (
                "unallowlisted_piped_grep_v",
                "git rev-list HEAD | grep -v deadbeef\n",
            ),
            (
                "conditional_plus_o_pipefail",
                "if false; then set +o pipefail; fi\n"
                "git rev-list HEAD | grep -q deadbeef\n",
            ),
        ):
            with self.subTest(case=label):
                with tempfile.TemporaryDirectory(prefix="zc-shell-bad-") as tmp:
                    repo = self._build_fixture_repo(
                        tmp,
                        f"#!/usr/bin/env bash\nset -euo pipefail\n{bad_line}",
                    )
                    res = self._run_check(repo)
                    self.assertNotEqual(
                        res.returncode, 0, res.stdout + res.stderr
                    )
                    self.assertIn("piped grep is disallowed", res.stderr)

    def test_allowlist_entries_are_non_quiet_and_fail_on_mutation(self) -> None:
        allowlist = _extract_allowlist()
        self.assertEqual(len(allowlist), 3)
        for fname, line_text in allowlist:
            self.assertNotRegex(
                line_text, r"(^|\s)(-[A-Za-z]*q|--qui|--sil)"
            )

        with tempfile.TemporaryDirectory(prefix="zc-shell-allow-") as tmp:
            repo = self._build_fixture_repo(
                tmp, "#!/usr/bin/env bash\nset -euo pipefail\nexit 0\n"
            )
            pkg = repo / "zerocopy" / "ci" / "check_packaging.sh"
            ok = self._run_check(repo)
            self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)

            for mut_label, mut_body in (
                (
                    "grep_line_mutated",
                    "#!/usr/bin/env bash\nset -euo pipefail\n"
                    "tar -xOzf a b | \\\n  grep -Fxq -e 'x' >/dev/null\n",
                ),
                (
                    "cont_line_q",
                    "#!/usr/bin/env bash\nset -euo pipefail\n"
                    "if ! tar -xOzf a b | \\\n"
                    "  grep -Fx -e '// SPDX-License-Identifier: "
                    "BSD-2-Clause OR Apache-2.0 OR MIT' \\\n"
                    "    -e '/* SPDX-License-Identifier: "
                    "BSD-2-Clause OR Apache-2.0 OR MIT */' -q \\\n"
                    "    > /dev/null; then\n  exit 1\nfi\n",
                ),
                (
                    "cont_last_line_quiet",
                    "#!/usr/bin/env bash\nset -euo pipefail\n"
                    "if ! tar -xOzf a b | \\\n"
                    "  grep -Fx -e '// SPDX-License-Identifier: "
                    "BSD-2-Clause OR Apache-2.0 OR MIT' \\\n"
                    "    -e '/* SPDX-License-Identifier: "
                    "BSD-2-Clause OR Apache-2.0 OR MIT */' \\\n"
                    "    --quiet > /dev/null; then\n  exit 1\nfi\n",
                ),
            ):
                with self.subTest(case=mut_label):
                    pkg.write_text(mut_body, encoding="utf-8")
                    res = self._run_check(repo)
                    self.assertNotEqual(
                        res.returncode, 0, res.stdout + res.stderr
                    )
                    self.assertIn("zerocopy/ci/check_packaging.sh", res.stderr)

            pkg.write_text(CLEAN_SCRIPT, encoding="utf-8")
            stale_line = self._run_check(repo)
            self.assertNotEqual(stale_line.returncode, 0)
            self.assertIn(
                "stale ALLOWLIST entry (line not matched)", stale_line.stderr
            )

            pkg.unlink()
            stale_file = self._run_check(repo)
            self.assertNotEqual(stale_file.returncode, 0)
            self.assertIn(
                "stale ALLOWLIST entry (file not scanned)", stale_file.stderr
            )

    def test_syntax_shellcheck_and_pre_push_coverage(self) -> None:
        clean_body = "#!/usr/bin/env bash\nset -euo pipefail\nexit 0\n"
        with tempfile.TemporaryDirectory(prefix="zc-shell-opts-") as tmp:
            repo = self._build_fixture_repo(tmp, clean_body)
            missing_sc = self._run_check(repo, args=("--require-shellcheck",))
            self.assertEqual(missing_sc.returncode, 1)
            ok_sc = self._run_check(
                repo, args=("--require-shellcheck",), shellcheck_exit=0
            )
            self.assertEqual(ok_sc.returncode, 0, ok_sc.stdout + ok_sc.stderr)

        with tempfile.TemporaryDirectory(prefix="zc-shell-syn-") as tmp:
            repo = self._build_fixture_repo(
                tmp, "#!/usr/bin/env bash\nif then fi\n"
            )
            res = self._run_check(repo)
            self.assertNotEqual(res.returncode, 0)

        with tempfile.TemporaryDirectory(prefix="zc-shell-cov-") as tmp:
            repo = self._build_fixture_repo(
                tmp,
                clean_body,
                pre_push_body="#!/usr/bin/env bash\nexit 0\n",
            )
            res = self._run_check(repo)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn(
                "./ci/sample.sh not called from githooks/pre-push", res.stderr
            )

        with tempfile.TemporaryDirectory(prefix="zc-shell-wait-") as tmp:
            repo = self._build_fixture_repo(
                tmp,
                clean_body,
                pre_push_body=(
                    "#!/usr/bin/env bash\n"
                    "./ci/sample.sh\n"
                    "./zerocopy/ci/check_all_toolchains_tested.sh\n"
                    "./ci/test_shell_and_hooks.py\n"
                ),
            )
            res = self._run_check(repo)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("SHELL_HOOKS_TEST_PID", res.stderr)

        py_m = re.search(
            r"python3 -I -B - \"\$\{SHELL_FILES\[@\]\}\" <<'PY'\n(.*?)\nPY\n",
            SCRIPT.read_text(encoding="utf-8"),
            re.S,
        )
        self.assertIsNotNone(py_m)
        assert py_m is not None
        with tempfile.TemporaryDirectory(prefix="zc-shell-hd-") as tmp:
            bad = Path(tmp) / "unterm.sh"
            bad.write_text(
                "cat <<EOF\nhello\ngit log | grep -q y\n", encoding="utf-8"
            )
            res = subprocess.run(
                [sys.executable, "-I", "-B", "-c", py_m.group(1), str(bad)],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("unterminated heredoc", res.stderr)

    def test_pipeline_newline_arith_redir_wrapper_heredoc(self) -> None:
        for label, body in (
            (
                "pipe_while_inner_pipe_then_if_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD | while read -r line; do\n"
                "  echo \"$line\" | tr a b\n"
                "  if true; then\n"
                "    echo ok\n"
                "  fi\n"
                "  grep -q deadbeef file\n"
                "done\n",
            ),
            (
                "pipe_amp_redir",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD | &>/dev/null grep -q deadbeef\n",
            ),
            (
                "pipe_amp_append_redir",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD | &>>/dev/null grep -q deadbeef\n",
            ),
            (
                "pipe_abs_env_wrapper",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD | /usr/bin/env grep -q deadbeef\n",
            ),
            (
                "pipe_abs_timeout_abs_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD | /usr/bin/timeout 5 /bin/grep -q y\n",
            ),
            (
                "arith_cmd_sub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "(( a = $(git log | grep -q y) ))\n",
            ),
            (
                "unquoted_heredoc_cmd_sub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<EOF\n"
                "$(git log | grep -q y)\n"
                "EOF\n",
            ),
            (
                "unquoted_heredoc_backtick",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<-EOF\n"
                "\t`git log | grep -q y`\n"
                "\tEOF\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-pipe-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "completed_pipe_then_subshell_non_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "echo a | sort\n"
                "(\n  grep -q foo file.txt\n)\n",
            ),
            (
                "arith_bitshift_and_bitwise_or_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "(( x = 1 << 2 ))\n"
                "(( 1 | grep ))\n"
                "exit 0\n",
            ),
            (
                "unquoted_heredoc_apostrophes_and_quoted_heredoc_cmd_sub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<EOF\ndon't break \"quotes\"\nEOF\n"
                "cat <<'EOF'\n$(git log | grep -q y)\nEOF\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-pipe-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_func_def_and_array_proc_sub(self) -> None:
        for label, body in (
            (
                "func_def_in_piped_while_preserves_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD | while read -r line; do\n"
                "  helper() { echo \"$line\"; }\n"
                "  grep -q deadbeef\n"
                "done\n",
            ),
            (
                "func_def_in_piped_brace_group_preserves_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD | { helper() { echo ok; }; "
                "grep -q deadbeef; }\n",
            ),
            (
                "func_def_spaced_parens_in_piped_brace_group",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD | { helper ( ) { echo ok; }; "
                "grep -q deadbeef; }\n",
            ),
            (
                "function_kw_in_piped_while_preserves_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD | while read -r line; do\n"
                "  function helper { echo \"$line\"; }\n"
                "  grep -q deadbeef\n"
                "done\n",
            ),
            (
                "function_kw_parens_in_piped_brace_group",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD | { function helper() { echo ok; }; "
                "grep -q deadbeef; }\n",
            ),
            (
                "array_assign_input_proc_sub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=( <(git rev-list HEAD | grep -q deadbeef) )\n",
            ),
            (
                "array_assign_output_proc_sub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=( >(git rev-list HEAD | grep -q deadbeef) )\n",
            ),
            (
                "param_expansion_proc_sub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "echo ${x:-<(git rev-list HEAD | grep -q deadbeef)}\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-func-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "non_piped_func_def_with_file_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "helper() { grep -q foo file.txt; }\n"
                "function helper2 { grep -q bar file.txt; }\n",
            ),
            (
                "param_expansion_quoted_lt_paren_and_safe_array_proc_sub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x=${var%%"<("*}\n'
                "arr=( <(grep -q foo file.txt) )\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-func-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_nested_subshell_array_comments_and_out_proc_sub(self) -> None:
        for label, body in (
            (
                "nested_subshell_not_arith_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "((echo a); git rev-list HEAD | grep -q deadbeef)\n"
                "# ))\n",
            ),
            (
                "nested_subshell_followed_by_arith",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "((true); printf 'deadbeef\\n' | grep -q deadbeef)\n"
                "(( x = 1 ))\n",
            ),
            (
                "array_comment_with_quote_and_paren_before_proc_sub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=(\n"
                "  # don't ) close early\n"
                "  <(git rev-list HEAD | grep -q deadbeef)\n"
                ")\n",
            ),
            (
                "output_proc_sub_direct_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git rev-list HEAD > >(grep -q deadbeef)\n",
            ),
            (
                "output_proc_sub_via_tee",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "echo a | tee >(grep -q a) >/dev/null\n",
            ),
            (
                "output_proc_sub_in_array_literal",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=( >(grep -q deadbeef) )\n",
            ),
            (
                "piped_select_preserves_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "echo 1 | select x in a b; do\n"
                "  grep -q deadbeef\n"
                "  break\n"
                "done\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-nest-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "nested_subshell_without_piped_grep_and_arith",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "((true); grep -q foo file.txt)\n"
                "(( (1 + 2) == 3 ))\n",
            ),
            (
                "array_with_comments_and_hash_word_and_safe_input_proc_sub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=(\n"
                "  # don't ) break\n"
                "  foo#bar\n"
                "  <(grep -q foo file.txt)\n"
                ")\n"
                "echo ${#arr[@]}\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-nest-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_append_assign_fd_redir_and_dq_param_sq(self) -> None:
        for label, body in (
            (
                "append_assign_prefix_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | FOO+=1 grep -q deadbeef\n",
            ),
            (
                "array_elem_assign_prefix_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | FOO[0]+=1 grep -q deadbeef\n",
            ),
            (
                "brace_fd_redir_prefix_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | {fd}>/dev/null grep -q deadbeef\n",
            ),
            (
                "dq_param_exp_sq_cmd_sub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "x=\"${msg:-'$(git rev-list HEAD | grep -q deadbeef)'}\"\n",
            ),
            (
                "unquoted_heredoc_param_exp_sq_cmd_sub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<EOF\n"
                "${msg:-'$(git rev-list HEAD | grep -q deadbeef)'}\n"
                "EOF\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-assign-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "unquoted_param_exp_sq_inhibits_cmd_sub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "x=${msg:-'$(git rev-list HEAD | grep -q deadbeef)'}\n",
            ),
            (
                "non_piped_append_assign_and_brace_fd_redir",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "FOO+=1 grep -q foo file.txt\n"
                "{fd}>/dev/null grep -q foo file.txt\n"
                "printf 'a\\n' | { cat >/dev/null; }\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-assign-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_piped_cmdsub_and_out_procsub_inheritance(self) -> None:
        for label, body in (
            (
                "piped_stage_dq_cmdsub_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'printf "deadbeef\\n" | echo "$(grep -q deadbeef)"\n',
            ),
            (
                "out_procsub_nested_cmdsub_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'printf "deadbeef\\n" > >(echo "$(grep -o deadbeef)")\n',
            ),
            (
                "piped_stage_backtick_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'printf "deadbeef\\n" | echo "`grep -q deadbeef`"\n',
            ),
            (
                "piped_stage_in_procsub_cmdsub_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'printf "deadbeef\\n" | cat <(echo "$(grep -q deadbeef)")\n',
            ),
            (
                "piped_stage_unquoted_heredoc_cmdsub_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | cat <<EOF\n"
                "$(grep -q deadbeef)\n"
                "EOF\n",
            ),
            (
                "piped_heredoc_before_or_list",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | cat <<EOF || true\n"
                "$(grep -q deadbeef)\n"
                "EOF\n",
            ),
            (
                "piped_heredoc_before_and_list",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | cat <<EOF && true\n"
                "$(grep -q deadbeef)\n"
                "EOF\n",
            ),
            (
                "piped_heredoc_before_semi",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | cat <<EOF; true\n"
                "$(grep -q deadbeef)\n"
                "EOF\n",
            ),
            (
                "piped_brace_heredoc_before_or_list",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | { true; } <<EOF || true\n"
                "$(grep -q deadbeef)\n"
                "EOF\n",
            ),
            (
                "multi_heredoc_second_piped",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<A | cat <<B\n"
                "$(grep -q foo file.txt)\n"
                "A\n"
                "$(grep -q deadbeef)\n"
                "B\n",
            ),
            (
                "piped_stage_redir_cmdsub_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'printf "deadbeef\\n" | true <<< "$(grep -q deadbeef)"\n',
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-sub-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "lhs_pipe_cmdsub_not_stdin_piped",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'echo "$(grep -q deadbeef file.txt)" | cat >/dev/null\n',
            ),
            (
                "lhs_pipe_unquoted_heredoc_not_piped",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<EOF | cat >/dev/null\n"
                "$(grep -q foo file.txt)\n"
                "EOF\n",
            ),
            (
                "lhs_pipe_heredoc_and_clean_rhs",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<A | cat <<B >/dev/null\n"
                "$(grep -q foo file.txt)\n"
                "A\n"
                "hello\n"
                "B\n",
            ),
            (
                "standalone_cmdsub_grep_file",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="$(grep -q deadbeef file.txt)"\n',
            ),
            (
                "heredoc_in_cmdsub_closed_on_same_line_clean_tail",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "x=$(cat <<EOF)\n'\nEOF\ngrep -q foo file.txt\n# '\n",
            ),
            (
                "heredoc_multiline_cmdsub_fifo_clean",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<A; echo $(\ncat <<B\n$(grep -q foo file.txt)\nB\n)\n"
                "$(grep -q foo file.txt)\nA\n",
            ),
            (
                "heredoc_order_outer_cmdsub_outer_clean",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<A >/dev/null; x=$(cat <<B); cat <<C >/dev/null\n"
                "B\nA\nC\n"
                "cat <<A >/dev/null; x=$(cat <<B1); y=$(cat <<B2); "
                "cat <<C >/dev/null\n"
                "B1\nB2\nA\nC\n"
                "cat <<A >/dev/null; x=$(cat <<B; cat $(cat <<C))\n"
                "C\nB\nA\n"
                "grep -q foo file.txt\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-sub-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

        for label, bad_body in (
            (
                "cmdsub_heredoc_closed_same_line_quote_desync",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "x=$(cat <<EOF)\n'\nEOF\ngit log | grep -q x\n# '\n",
            ),
            (
                "dq_cmdsub_heredoc_closed_same_line_quote_desync",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="$(cat <<EOF)"\n\'\nEOF\ngit log | grep -q x\n# \'\n',
            ),
            (
                "procsub_heredoc_closed_same_line_quote_desync",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <(cat <<EOF)\n'\nEOF\ngit log | grep -q x\n# '\n",
            ),
            (
                "piped_cmdsub_heredoc_closed_same_line_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git log | cat $(cat <<EOF)\n$(grep -q x)\nEOF\n",
            ),
            (
                "nested_cmdsub_heredoc_closed_same_line_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "git log | cat $(echo $(cat <<EOF))\n$(grep -q x)\nEOF\n",
            ),
            (
                "heredoc_order_outer_then_cmdsub_true_delim",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<A >/dev/null; x=$(cat <<true)\n"
                "true\nA\ngit log | grep -q x\ntrue\n",
            ),
            (
                "heredoc_order_same_cmd_arg_then_true_delim",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<A >/dev/null $(cat <<true)\n"
                "true\nA\ngit log | grep -q x\ntrue\n",
            ),
            (
                "heredoc_order_procsub_true_delim",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<A >/dev/null <(cat <<true)\n"
                "true\nA\ngit log | grep -q x\ntrue\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-hd-rp-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, bad_body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

    @staticmethod
    def _extract_embedded_python() -> str:
        script_text = SCRIPT.read_text(encoding="utf-8")
        m = re.search(
            r'python3 -I -B - "\$\{SHELL_FILES\[@\]\}" <<\'PY\'\n(.*?)\nPY\b',
            script_text,
            re.S,
        )
        assert m is not None, "embedded scanner not found"
        return m.group(1)

    def test_dq_backtick_extglob_locale_and_compound_prefixes(self) -> None:
        for label, body in (
            (
                "dq_param_exp_backtick_escaped_quote_comment_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "msg=''\n"
                'x="${msg:-`printf \\"a #\\n\\" | grep -q a`}"\n',
            ),
            (
                "optparen_case_pattern_top_level_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'y=a\necho 1 | case "$y" in (a|b) grep -q 1 ;; esac\n',
            ),
            (
                "locale_dq_string_grep_and_wrapper",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | $\"grep\" -q deadbeef\n",
            ),
            (
                "locale_dq_string_env_wrapper",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | $\"env\" grep -q deadbeef\n",
            ),
            (
                "time_p_compound_block_preserves_enclosing_pipe_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | "
                "{ time -p { echo ok >/dev/null; }; grep -q deadbeef; }\n",
            ),
            (
                "coproc_named_compound_block_preserves_enclosing_pipe_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | "
                "{ coproc MYNAME { echo ok >/dev/null; }; "
                "grep -q deadbeef; }\n",
            ),
            (
                "time_p_case_inside_cmdsub_does_not_truncate",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'y=a\nx="$(time -p case "$y" in a) echo ok ;; esac; '
                "printf 'deadbeef\\n' | grep -q deadbeef)\"\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-ext-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "locale_and_time_p_and_coproc_without_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'y=a\ncase "$y" in (a|b) echo ok ;; esac\n'
                '$"grep" -q foo file.txt\n'
                "time -p { echo ok; }\n"
                "coproc MYNAME { echo ok; }\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-ext-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

        scanner_py = self._extract_embedded_python()
        for label, body, expect_fail in (
            (
                "extglob_case_pattern_top_level_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'y=a\necho 1 | case "$y" in @(a|b)) grep -q 1 ;; esac\n',
                True,
            ),
            (
                "extglob_case_pattern_in_cmdsub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'y=a\nx="$(case "$y" in (@(a|+(b|#))) echo a | grep -q a ;; '
                'esac)"\n',
                True,
            ),
            (
                "extglob_case_pattern_clean",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'y=a\ncase "$y" in @(a|b)) echo ok ;; esac\n',
                False,
            ),
        ):
            with self.subTest(extglob=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-extglob-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                b_res = subprocess.run(
                    [
                        "bash",
                        "-O",
                        "extglob",
                        "-n",
                        str(repo / "ci" / "sample.sh"),
                    ],
                    text=True,
                    capture_output=True,
                    check=False,
                )
                self.assertEqual(b_res.returncode, 0, b_res.stderr)
                res = subprocess.run(
                    [
                        sys.executable,
                        "-I",
                        "-B",
                        "-",
                        "ci/sample.sh",
                        "zerocopy/ci/check_packaging.sh",
                    ],
                    cwd=repo,
                    input=scanner_py,
                    text=True,
                    capture_output=True,
                    check=False,
                )
                if expect_fail:
                    self.assertNotEqual(res.returncode, 0, label)
                    self.assertIn("piped grep is disallowed", res.stderr, label)
                else:
                    self.assertEqual(
                        res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                    )

    def test_arith_backtrack_and_time_dashdash(self) -> None:
        for label, body in (
            (
                "word_arith_backtrack_subshell_cmdsub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "x=$((printf 'deadbeef\\n' | grep -q deadbeef); echo ok)\n",
            ),
            (
                "dq_arith_backtrack_subshell_cmdsub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="$((echo a); printf \'deadbeef\\n\' | grep -q deadbeef)"\n',
            ),
            (
                "param_exp_arith_backtrack_subshell_cmdsub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'msg=""\n'
                'x="${msg:-$((printf \'deadbeef\\n\' | grep -q deadbeef); '
                'echo ok)}"\n',
            ),
            (
                "nested_arith_backtrack_subshell_cmdsub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "x=$(( $((printf 'deadbeef\\n' | grep -q deadbeef); "
                "echo 1) + 0 ))\n",
            ),
            (
                "heredoc_arith_backtrack_subshell_cmdsub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<EOF >/dev/null\n"
                "$((printf 'deadbeef\\n' | grep -q deadbeef); echo ok)\n"
                "EOF\n",
            ),
            (
                "time_dashdash_compound_block",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | "
                "{ time -- { echo ok >/dev/null; }; grep -q deadbeef; }\n",
            ),
            (
                "time_p_dashdash_compound_block",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | "
                "{ time -p -- { echo ok >/dev/null; }; grep -q deadbeef; }\n",
            ),
            (
                "time_dashdash_case_inside_cmdsub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'y=a\nx="$(time -- case "$y" in a) echo ok ;; esac; '
                "printf 'deadbeef\\n' | grep -q deadbeef)\"\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-arith-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "arith_backtrack_and_time_dashdash_without_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "x=$((echo a); grep -q foo file.txt)\n"
                'y="$((echo a); echo b)"\n'
                "time -- { echo ok; }\n"
                "time -p -- { echo ok; }\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-arith-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_array_redir_and_case_esac_patterns(self) -> None:
        for label, body in (
            (
                "array_var_fd_redir_before_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=()\n"
                "printf 'deadbeef\\n' | {arr[0]}>/dev/null grep -q deadbeef\n",
            ),
            (
                "assoc_array_quoted_bracket_redir_before_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "declare -A m=()\n"
                "printf 'deadbeef\\n' | {m[']']}>/dev/null grep -q deadbeef\n",
            ),
            (
                "nested_bracket_redir_before_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=(); a=(0)\n"
                "printf 'deadbeef\\n' | "
                "{arr[a[0]]}>/dev/null grep -q deadbeef\n",
            ),
            (
                "array_redir_subscript_cmdsub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=()\n"
                "printf 'deadbeef\\n' | "
                "{arr[$(grep -q deadbeef; echo 0)]}>/dev/null cat\n",
            ),
            (
                "case_bar_esac_pattern_preserves_pipe_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "y=a\n"
                "printf 'deadbeef\\n' | "
                'case "$y" in a|esac) grep -q deadbeef ;; esac\n',
            ),
            (
                "case_spaced_bar_esac_pattern_preserves_pipe_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "y=a\n"
                "printf 'deadbeef\\n' | "
                'case "$y" in a | esac) grep -q deadbeef ;; esac\n',
            ),
            (
                "case_paren_esac_pattern_preserves_pipe_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "y=esac\n"
                "printf 'deadbeef\\n' | "
                'case "$y" in (esac) grep -q deadbeef ;; esac\n',
            ),
            (
                "case_quoted_and_subst_esac_pattern_preserves_pipe_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "y=esac; p=''\n"
                "printf 'deadbeef\\n' | "
                'case "$y" in ${p}esac) grep -q deadbeef ;; esac\n',
            ),
            (
                "case_bar_esac_inside_cmdsub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "y=a\n"
                'x="$(case "$y" in a|esac) '
                "printf 'deadbeef\\n' | grep -q deadbeef ;; esac)\"\n",
            ),
            (
                "case_paren_esac_inside_cmdsub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "y=esac\n"
                'x="$(case "$y" in (esac) '
                "printf 'deadbeef\\n' | grep -q deadbeef ;; esac)\"\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-redir-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "array_redir_and_case_esac_without_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=(); y=esac\n"
                "{arr[0]}>/dev/null grep -q foo file.txt\n"
                'case "$y" in a|esac) grep -q foo file.txt ;; esac\n'
                'case "$y" in (esac) grep -q foo file.txt ;; esac\n'
                'case "$y" in a) echo ok ;; esac\n',
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-redir-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_bracket_regex_hash_and_compound_trailing_redir(self) -> None:
        for label, body in (
            (
                "bracket_regex_eq_lparen_hash_before_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="a=#"\n'
                'if [[ "$x" =~ ^a=(#|b)$ ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n",
            ),
            (
                "brace_group_trailing_herestring_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'yes deadbeef | { true; } <<< "$(grep -q deadbeef)"\n',
            ),
            (
                "subshell_trailing_herestring_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'yes deadbeef | (true) <<< "$(grep -q deadbeef)"\n',
            ),
            (
                "if_compound_trailing_redir_cmdsub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | "
                'if true; then true; fi > "$(grep -q deadbeef && '
                'echo /dev/null)"\n',
            ),
            (
                "brace_group_trailing_array_redir_cmdsub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=()\n"
                "yes deadbeef | { true; } "
                "{arr[$(grep -q deadbeef; echo 0)]}>/dev/null\n",
            ),
            (
                "brace_group_trailing_heredoc_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "yes deadbeef | { true; } <<EOF\n"
                "$(grep -q deadbeef)\n"
                "EOF\n",
            ),
            (
                "case_trailing_herestring_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "yes deadbeef | case a in a) ;; esac "
                '<<< "$(grep -q deadbeef)"\n',
            ),
            (
                "empty_case_trailing_herestring_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'yes deadbeef | case a in esac <<< "$(grep -q deadbeef)"\n',
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-ere-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "bracket_regex_hash_and_non_piped_compound_redirs",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="a=#"\n'
                'if [[ "$x" =~ ^a=(#|b)$ ]]; then echo ok; fi\n'
                'if [[ "$x" =~ ^(#|b)$ ]]; then echo ok; fi\n'
                'yes deadbeef | { true; }\n'
                "grep -q foo file.txt\n"
                '(yes deadbeef | (true)) <<< "$(grep -q foo file.txt)"\n',
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-ere-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_case_and_for_header_reserved_words(self) -> None:
        for label, body in (
            (
                "case_in_word_followed_by_esac_then_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "case in in\n"
                "esac\n"
                "printf 'deadbeef\\n' | grep -q deadbeef\n"
                "case a in a) ;; esac\n",
            ),
            (
                "case_in_word_and_in_pattern_preserves_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | "
                "case in in in) grep -q deadbeef ;; esac\n",
            ),
            (
                "for_in_list_containing_do_and_done_preserves_piped_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | "
                "for x in do done; do grep -q deadbeef; done\n",
            ),
            (
                "for_do_var_and_do_item_preserves_piped_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | "
                "for do in a do; do grep -q deadbeef; done\n",
            ),
            (
                "for_arith_header_preserves_piped_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | "
                "for ((i=0; i<1; i++)) do grep -q deadbeef; done\n",
            ),
            (
                "select_in_list_containing_do_done_preserves_piped_scope",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | "
                "select x in do done; do grep -q deadbeef; break; done\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-hdr-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "case_and_for_header_reserved_words_without_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "case in in\n"
                "esac\n"
                "case in in in) grep -q foo file.txt ;; esac\n"
                "case esac in (esac) grep -q foo file.txt ;; esac\n"
                "for x in do done; do echo \"$x\"; done\n"
                "for x\n"
                "in do\n"
                "do echo \"$x\"; done\n"
                "for x do echo \"$x\"; done\n"
                "for ((i=0; i<1; i++)); do echo \"$i\"; done\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-hdr-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_brace_for_loops_and_ere_bracket_classes(self) -> None:
        for label, body in (
            (
                "for_arith_brace_body_then_done_loop_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "echo 1 | for ((i=0; i<1; i++)) { grep -q 1; }\n"
                'for y in a; do echo "$y"; done\n',
            ),
            (
                "for_in_brace_body_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "echo 1 | for x in a; { grep -q 1; }\n",
            ),
            (
                "for_no_in_brace_body_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "echo 1 | for x; { grep -q 1; }\n",
            ),
            (
                "select_in_brace_body_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "echo 1 | select x in a; { grep -q 1; break; }\n",
            ),
            (
                "for_brace_trailing_herestring_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'echo 1 | for ((i=0; i<1; i++)) { true; } <<< "$(grep -q 1)"\n',
            ),
            (
                "regex_ere_bracket_with_parens_before_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x=""\n'
                'if [[ "$x" =~ []()] ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n"
                'if [[ "$x" =~ [[:alpha:]()] ]]; then true; fi\n',
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-loop-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "brace_for_loops_and_ere_bracket_without_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "x=a\n"
                'for ((i=0; i<1; i++)) { grep -q foo file.txt; }\n'
                'for y in a; { echo "$y"; }\n'
                'for y in { }; do echo "$y"; done\n'
                'if [[ "$x" =~ []()] ]]; then echo ok; fi\n'
                'if [[ "$x" =~ [^]()] ]]; then echo ok; fi\n'
                'if [[ "$x" =~ [[:alpha:]()] ]]; then echo ok; fi\n'
                'if [[ "$x" =~ [a ]]; then echo ok; fi\n',
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-loop-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_dq_param_procsub_and_func_cont(self) -> None:
        for label, body in (
            (
                "dq_param_exp_literal_lt_lparen_then_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'var=""\nx="${var:-<(}"\necho "hello )"\n'
                "printf 'deadbeef\\n' | grep -q deadbeef\n"
                'echo "}"\n',
            ),
            (
                "heredoc_param_exp_literal_lt_lparen_sq_then_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'var=""\ncat <<EOF >/dev/null\n'
                "${var:-<(}'\n"
                "$(printf 'deadbeef\\n' | grep -q deadbeef)\n"
                "EOF\n",
            ),
            (
                "func_empty_parens_with_line_cont_before_case_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="$(f( \\\n ) case a in a) '
                "printf 'deadbeef\\n' | grep -q deadbeef ;; esac)\"\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-dq-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "dq_param_exp_procsub_literals_and_func_cont_clean",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'var=""\nx="${var:->(grep -q a)}"\n'
                'y="${var%%<(a)*}"\n'
                "f( \\\n ) case a in a) grep -q foo file.txt ;; esac\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-dq-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_dq_arith_quotes_and_operator_line_cont(self) -> None:
        for label, body in (
            (
                "dq_arith_backtrack_with_sq_rparen",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="$((echo \'a))b\'); '
                "printf 'deadbeef\\n' | grep -q deadbeef)\"\n",
            ),
            (
                "dq_arith_backtrack_with_ansi_sq_rparen",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="$((echo $\'a))b\'); '
                "printf 'deadbeef\\n' | grep -q deadbeef)\"\n",
            ),
            (
                "fd_redir_with_line_cont",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | 2\\\n>/dev/null grep -q deadbeef\n",
            ),
            (
                "var_fd_redir_with_line_cont",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | {fd}\\\n"
                ">/dev/null grep -q deadbeef\n",
            ),
            (
                "amp_redir_with_line_cont",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | &\\\n>/dev/null grep -q deadbeef\n",
            ),
            (
                "pipe_amp_with_line_cont",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' |\\\n& grep -q deadbeef\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-cont-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "dq_arith_param_sq_and_line_cont_clean",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'a=""\n'
                'x="$(( ${a:-\'}\'} + 1 ))"\n'
                'y="$((echo \'a))b\'); echo ok)"\n'
                "2\\\n>/dev/null grep -q foo file.txt\n"
                "cat <<\\\n-EOF >/dev/null\n"
                "\tgrep -q foo file.txt\n"
                "EOF\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-cont-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_nested_array_assign_and_paren_bracket_regex(self) -> None:
        for label, body in (
            (
                "nested_array_prefix_assign",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | FOO[a[0]]=1 grep -q deadbeef\n",
            ),
            (
                "dq_rbracket_array_prefix_assign",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'printf \'deadbeef\\n\' | FOO["]"]=1 grep -q deadbeef\n',
            ),
            (
                "sq_rbracket_array_prefix_assign",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | FOO[']']=1 grep -q deadbeef\n",
            ),
            (
                "space_in_array_prefix_assign",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | FOO[1 + 1]=1 grep -q deadbeef\n",
            ),
            (
                "nested_array_append_prefix_assign",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | FOO[a[0]]+=1 grep -q deadbeef\n",
            ),
            (
                "paren_hash_ere_in_bracket_test",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="b"\n'
                'if [[ "$x" =~ (#|b) ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n",
            ),
            (
                "paren_pipe_hash_ere_in_bracket_test",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="#b"\n'
                'if [[ "$x" =~ (a)|#b ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n",
            ),
            (
                "multi_paren_hash_ere_in_bracket_test",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="a#"\n'
                'if [[ "$x" =~ (a)(#|b) ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n",
            ),
            (
                "paren_space_hash_ere_in_bracket_test",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="foo #bar"\n'
                'if [[ "$x" =~ (foo #bar) ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n",
            ),
            (
                "nested_paren_hash_ere_in_bracket_test",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="#b"\n'
                'if [[ "$x" =~ ((a)|(#b)) ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n",
            ),
            (
                "leading_pipe_hash_ere_in_bracket_test",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="#b"\n'
                'if [[ "$x" =~ |#b ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-arr-ere-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "nested_array_and_paren_ere_clean",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="b"\n'
                'FOO[a[0]]=1 echo ok\n'
                'FOO["]"]=1 echo ok\n'
                'if [[ "$x" =~ (#|b) ]] && [[ "$x" =~ (a)|#b ]] && '
                '[[ "$x" =~ (a)(#|b) ]] && [[ "$x" =~ (foo #bar) ]] && '
                '[[ "$x" =~ ((a)|(#b)) ]] && [[ "$x" =~ |#b ]]; then\n'
                "  grep -q foo file.txt\n"
                "fi\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-arr-ere-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_param_lbrace_and_array_append_literals(self) -> None:
        for label, body in (
            (
                "dq_param_bare_lbrace_evasion",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "var='{hello}'\n"
                'x="${var#{}"\n'
                "printf 'deadbeef\\n' | grep -q deadbeef\n"
                'echo "$x}"\n',
            ),
            (
                "unquoted_param_bare_lbrace_evasion",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "var='{hello}'\n"
                "x=${var#{}\n"
                "printf 'deadbeef\\n' | grep -q deadbeef\n"
                "echo done }\n",
            ),
            (
                "array_append_rbrace_evasion",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=()\n"
                "printf 'deadbeef\\n' | { arr+=( } ); grep -q deadbeef; }\n",
            ),
            (
                "array_append_case_evasion",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=()\n"
                "arr+=( case )\n"
                "printf 'deadbeef\\n' | grep -q deadbeef\n"
                "case a in a) ;; esac\n",
            ),
            (
                "array_append_cmdsub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=()\n"
                "arr+=( $(printf 'deadbeef\\n' | grep -q deadbeef) )\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-lbrace-arr-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "param_bare_lbrace_and_array_append_clean",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "var='{hello}'\n"
                'x="${var#{}"\n'
                'y="${var//{/}"\n'
                'z="${var:-{a}}"\n'
                "tools=()\n"
                "printf 'ok\\n' | while IFS= read -r line; do\n"
                "  tools+=(grep)\n"
                '  echo "$line"\n'
                "done\n"
                "arr=()\n"
                "arr+=( case } )\n"
                'arr+=\\\n( "grep" )\n'
                'echo "$x" "$y" "$z" "${arr[0]}" "${#tools[@]}"\n',
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-lbrace-arr-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_bracket_test_extglob_hash(self) -> None:
        for label, body in (
            (
                "bracket_eq_extglob_hash_then_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="a"\n'
                'if [[ "$x" == @(a|#b) ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n"
                'if [[ "$x" == a ]]; then echo ok; fi\n',
            ),
            (
                "bracket_neq_nested_extglob_hash",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="c"\n'
                'if [[ "$x" != !(@(a|*(#b))) ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n",
            ),
            (
                "bracket_extglob_cmdsub_piped_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="a"\n'
                'if [[ "$x" == @(a|$(printf "deadbeef\\n" '
                "| grep -q deadbeef)) ]]; then\n"
                "  echo ok\n"
                "fi\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-extbracket-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "bracket_extglob_hash_clean",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="a"\n'
                'if [[ "$x" == @(a|#b) ]] && '
                '[[ "$x" != *(b|?(#c)) ]] && '
                '[[ "$x" == @(foo|]]) ]]; then\n'
                "  grep -q foo file.txt\n"
                "fi\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-extbracket-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_bracket_unary_neg_comment_and_case_subshell_esac(self) -> None:
        for label, body in (
            (
                "bracket_unary_neg_comment_apostrophe_evasion",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "if [[ !( -n \"\"\n"
                "  # ) ]]; echo '\n"
                ") ]]; then\n"
                '  printf "deadbeef\\n" | grep -q deadbeef\n'
                "fi\n# '\n",
            ),
            (
                "bracket_unary_neg_then_extglob_hash",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="a"\n'
                'if [[ !( "$x" != @(a|#b) ) ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n",
            ),
            (
                "piped_case_subshell_no_dsemi_before_esac",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | {\n"
                "  case a in a) (echo ok) esac\n"
                "  grep -q deadbeef\n"
                "}\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-negbracket-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "bracket_unary_neg_comment_apostrophe_clean",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x=""\n'
                "if [[ !(\n"
                "  # don't match when non-empty\n"
                '  -n "$x"\n'
                ") ]]; then\n"
                "  echo ok\n"
                "fi\n"
                "case a in a) (echo ok) esac\n",
            ),
            (
                "piped_case_subshell_no_dsemi_clean_tail",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'a\\n' | case a in a) (cat) esac\n"
                "grep -q foo file.txt\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-negbracket-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_line_cont_introducers_and_nested_case_closers(self) -> None:
        for label, body in (
            (
                "dq_line_cont_dollar_lparen",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'x="$\\\n(printf \'deadbeef\\n\' | grep -q deadbeef)"\n',
            ),
            (
                "heredoc_line_cont_dollar_lparen",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<EOF >/dev/null\n"
                "$\\\n(printf 'deadbeef\\n' | grep -q deadbeef)\n"
                "EOF\n",
            ),
            (
                "heredoc_line_cont_dollar_brace_cmdsub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "cat <<EOF >/dev/null\n"
                '${a:-"$\\\n(printf \'deadbeef\\n\' | grep -q deadbeef)"}\n'
                "EOF\n",
            ),
            (
                "array_line_cont_procsub",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "arr=( >\\\n(grep -q deadbeef) )\n"
                'echo "${#arr[@]}"\n',
            ),
            (
                "line_cont_ansi_sq_grep_in_pipe",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | $\\\n'grep' -q deadbeef\n",
            ),
            (
                "line_cont_locale_dq_grep_in_pipe",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'printf \'deadbeef\\n\' | $\\\n"grep" -q deadbeef\n',
            ),
            (
                "case_bracket_test_before_esac",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | {\n"
                "  case a in a) [[ -n a ]] esac\n"
                "  grep -q deadbeef\n"
                "}\n",
            ),
            (
                "case_arith_before_esac",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | {\n"
                "  case a in a) (( 1 )) esac\n"
                "  grep -q deadbeef\n"
                "}\n",
            ),
            (
                "case_empty_inner_case_before_esac",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | {\n"
                "  case a in a) case b in esac esac\n"
                "  grep -q deadbeef\n"
                "}\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-intro-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, body in (
            (
                "piped_case_closers_clean_tail",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'a\\n' | case a in a) [[ -n a ]] esac\n"
                "printf 'a\\n' | case a in a) (( 1 )) esac\n"
                "printf 'a\\n' | case a in a) case b in esac esac\n"
                'x="$\\\n(echo ok)"\n'
                "y=$\\\n'ok'\n"
                'z=$\\\n"ok"\n'
                "grep -q foo file.txt\n",
            ),
        ):
            with self.subTest(good=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-intro-ok-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertEqual(
                    res.returncode, 0, f"{label}: {res.stdout}{res.stderr}"
                )

    def test_regex_class_quoted_and_subst_elements(self) -> None:
        bad_patterns = (
            ("sq_range", "(['a-z'])"),
            ("dq_range", '(["a-z"])'),
            ("dq_rbrack", '(["]"])'),
            ("dq_negated", '([^"a"])'),
            ("dq_subst", '(["${v}"])'),
            ("param_subst", "([${v}])"),
            ("cmd_subst", "([$(printf a)])"),
            ("backtick_subst", "([`printf a`])"),
            ("ansi_sq", "([$'a'])"),
            ("locale_dq", '([$"a"])'),
            ("sq_caret_prefix", "(['^'a])"),
        )
        for label, pat in bad_patterns:
            body = (
                "#!/usr/bin/env bash\nset -euo pipefail\nv=a\nx=a\n"
                f'if [[ "$x" =~ {pat} ]]; then\n'
                "  printf 'deadbeef\\n' | grep -q deadbeef\n"
                "fi\n"
                "case a in a) ;; esac\n"
                'if [[ "$x" == a ]]; then echo ok; fi\n'
            )
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-re-bad-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        for label, bad_body in (
            (
                "rparen_in_bracket_class_no_desync",
                "#!/usr/bin/env bash\nset -euo pipefail\nx=a\n"
                "[[ $x =~ ([)] ]] || echo no # )\n"
                "git log | grep -q x\n"
                "echo ]]\n",
            ),
            (
                "sq_empty_rparen_in_bracket_class",
                "#!/usr/bin/env bash\nset -euo pipefail\nx=a\n"
                "[[ $x =~ ([''])] ]] || echo no # )\n"
                "git log | grep -q x\n"
                "echo ]]\n",
            ),
            (
                "dq_empty_rparen_in_bracket_class",
                "#!/usr/bin/env bash\nset -euo pipefail\nx=a\n"
                '[[ $x =~ ([""])] ]] || echo no # )\n'
                "git log | grep -q x\n"
                "echo ]]\n",
            ),
            (
                "sq_caret_rparen_in_bracket_class",
                "#!/usr/bin/env bash\nset -euo pipefail\nx=a\n"
                "[[ $x =~ (['^'])] ]] || echo no # )\n"
                "git log | grep -q x\n"
                "echo ]]\n",
            ),
            (
                "if_rparen_in_bracket_class",
                "#!/usr/bin/env bash\nset -euo pipefail\nx=a\n"
                "if [[ $x =~ ([)] ]]; then :; fi # )\n"
                "printf 'deadbeef\\n' | grep -q deadbeef\n"
                "echo ]]\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-re-rp-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, bad_body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        good_body = (
            "#!/usr/bin/env bash\nset -euo pipefail\nv=a\nx=a\n"
            + "".join(
                f'if [[ "$x" =~ {pat} ]]; then echo ok; fi\n'
                for _, pat in bad_patterns
            )
            + 'if [[ "]" =~ [\'\']] ]]; then echo ok; fi\n'
            + 'if [[ "]" =~ [""]] ]]; then echo ok; fi\n'
            + "if [[ \"a\" =~ (['^']]) ]]; then echo ok; fi\n"
            + "if [[ ' ' =~ ([ ]) ]]; then echo ok; fi\n"
            + '[[ "$x" =~ ([\'\']) ]] || true\n'
            + '[[ "$x" =~ ([""]) ]] || true\n'
            + "[[ \"$x\" =~ (['^']) ]] || true\n"
            + '[[ "$x" =~ (["^"]) ]] || true\n'
            + "[[ \"$x\" =~ ([$'^']) ]] || true\n"
            + "[[ \"$x\" =~ ([^'']) ]] || true\n"
            + "[[ \"$x\" =~ (['']^) ]] || true\n"
            + "grep -q foo file.txt\n"
        )
        with tempfile.TemporaryDirectory(prefix="zc-shell-re-ok-") as tmp:
            repo = self._build_fixture_repo(tmp, good_body)
            res = self._run_check(repo)
            self.assertEqual(
                res.returncode, 0, f"{res.stdout}{res.stderr}"
            )

    def test_coproc_name_compound_bracket_and_arith(self) -> None:
        for label, body in (
            (
                "coproc_name_dbl_bracket_brace_pipe_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\nx=\"\"\n"
                "printf 'deadbeef\\n' | {\n"
                '  coproc MYNAME [[ -n "$x" && } == "$x" ]]\n'
                "  grep -q deadbeef\n"
                "}\n",
            ),
            (
                "coproc_name_arith_brace_pipe_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'deadbeef\\n' | {\n"
                "  coproc MYNAME (( 1 + 1 ))\n"
                "  grep -q deadbeef\n"
                "}\n",
            ),
            (
                "coproc_grep_regex_after_pipe",
                "#!/usr/bin/env bash\nset -euo pipefail\nx=foo\n"
                "printf 'deadbeef\\n' | {\n"
                '  coproc MYNAME [[ "$x" =~ ^(foo|grep)$ ]]\n'
                "  grep -q deadbeef\n"
                "}\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-coproc-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        clean_body = (
            "#!/usr/bin/env bash\nset -euo pipefail\nx=foo\n"
            'coproc MYNAME [[ "$x" =~ ^(foo|grep)$ ]]\n'
            'coproc grep [[ "$x" =~ ^(foo|grep)$ ]]\n'
            'printf "a\\n" | coproc grep [[ -n a ]]\n'
            'printf "a\\n" | coproc grep (( 1 ))\n'
            "grep -q foo file.txt\n"
        )
        with tempfile.TemporaryDirectory(prefix="zc-shell-coproc-ok-") as tmp:
            repo = self._build_fixture_repo(tmp, clean_body)
            res = self._run_check(repo)
            self.assertEqual(
                res.returncode, 0, f"{res.stdout}{res.stderr}"
            )

    def test_bracket_double_lparen_and_closer_stage_keywords(self) -> None:
        for label, body in (
            (
                "bracket_double_lparen_comment_desync",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                'if [[ (( -n "a"\n'
                "  # )) ]]; echo '\n"
                ")) ]]; then\n"
                '  printf "deadbeef\\n" | grep -q deadbeef\n'
                "fi\n"
                "# '\n",
            ),
            (
                "if_bracket_then_no_semi",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'a\\n' | if [[ -n a ]] then grep -q a; fi\n",
            ),
            (
                "while_bracket_do_no_semi",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'a\\n' | while [[ -n '' ]] do grep -q a; done\n",
            ),
            (
                "until_arith_do_no_semi",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'a\\n' | until (( 1 )) do grep -q a; done\n",
            ),
            (
                "if_subshell_else_no_semi",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'a\\n' | if false; then (echo no) "
                "else grep -q a; fi\n",
            ),
            (
                "if_subshell_elif_no_semi",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'a\\n' | if false; then (echo no) "
                "elif grep -q a; then echo ok; fi\n",
            ),
            (
                "if_subshell_then_bracket_regex_grep",
                "#!/usr/bin/env bash\nset -euo pipefail\n"
                "printf 'a\\n' | if (true) then [[ a =~ (#|b) ]] "
                "&& grep -q a; fi\n",
            ),
        ):
            with self.subTest(bad=label), tempfile.TemporaryDirectory(
                prefix="zc-shell-stage-"
            ) as tmp:
                repo = self._build_fixture_repo(tmp, body)
                res = self._run_check(repo)
                self.assertNotEqual(res.returncode, 0, label)
                self.assertIn("piped grep is disallowed", res.stderr, label)

        clean_body = (
            "#!/usr/bin/env bash\nset -euo pipefail\n"
            'if [[ (( -n "a"\n'
            "  # )) ]]; echo '\n"
            ")) ]]; then\n"
            "  grep -q foo file.txt\n"
            "fi\n"
            "# '\n"
            "if [[ -n a ]] then grep -q foo file.txt; fi\n"
            "while [[ -n '' ]] do grep -q foo file.txt; done\n"
            "until (( 1 )) do grep -q foo file.txt; done\n"
            "if false; then (echo no) else grep -q foo file.txt; fi\n"
            "if false; then (echo no) elif grep -q foo file.txt; "
            "then echo ok; fi\n"
            "if (true) then [[ a =~ (#|b) ]] && grep -q foo file.txt; fi\n"
        )
        with tempfile.TemporaryDirectory(prefix="zc-shell-stage-ok-") as tmp:
            repo = self._build_fixture_repo(tmp, clean_body)
            res = self._run_check(repo)
            self.assertEqual(
                res.returncode, 0, f"{res.stdout}{res.stderr}"
            )


if __name__ == "__main__":
    unittest.main()
