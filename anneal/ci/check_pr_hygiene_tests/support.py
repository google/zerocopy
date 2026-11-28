# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared constants, helpers, and the `RepoTestCase` fixture for the
`check_pr_hygiene` tests."""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_pr_hygiene as cph  # noqa: E402

SCRIPT = Path(__file__).resolve().parent.parent / "check_pr_hygiene.py"
# Built at runtime so this file contains no literal review-round ID.
ROUND_ID = "G2" + "-R3"
SHA_RUST = "8144389c895da997dbdecaa635e41d6a50be6ffd"

HEADER_PY = """\
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""
HEADER_RS = HEADER_PY.replace("# ", "// ").replace("#\n", "//\n")
HEADER_LEAN = HEADER_PY.replace("# ", "-- ").replace("#\n", "--\n")
HEADER_MD = """\
<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->
"""
CRR = (
    "<!-- code-review-rules:begin -->\n"
    "Rules text.\n"
    "<!-- code-review-rules:end -->\n"
)
TRAILER = "Agent-authored-by: AI agent acting on joshlf's behalf"
GOOD_MESSAGE = (
    "[ci] Add a helper\n\n"
    "Add a helper that does one thing well, so callers stop duplicating\n"
    "the logic.\n\n"
    f"{TRAILER}\n"
)
AUTHOR = "Test Author <test@example.com>"


def ambient_env() -> dict[str, str]:
    """The test environment without inputs that change the script's output.

    Under GitHub Actions, an inherited `GITHUB_STEP_SUMMARY` would make
    waiver tests write to the real step summary.
    """
    return {k: v for k, v in os.environ.items()
            if k not in ("GITHUB_STEP_SUMMARY", "PR_TITLE")}


def git(repo: Path, *args: str, env: dict[str, str] | None = None) -> str:
    full_env = {
        **{k: v for k, v in os.environ.items() if not k.startswith("GIT_")},
        "GIT_AUTHOR_NAME": "Test Author",
        "GIT_AUTHOR_EMAIL": "test@example.com",
        "GIT_COMMITTER_NAME": "Test Author",
        "GIT_COMMITTER_EMAIL": "test@example.com",
        "GIT_CONFIG_NOSYSTEM": "1",
        "HOME": str(repo.parent),
        **(env or {}),
    }
    return subprocess.run(
        ["git", "-c", "core.hooksPath=/dev/null", "-c", "init.defaultBranch=main",
         *args],
        cwd=repo, env=full_env, capture_output=True, text=True, check=True,
    ).stdout


class RepoTestCase(unittest.TestCase):
    """Builds a scratch repository with a minimal Anneal tree on `main`."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="anneal-pr-hygiene-")
        self.repo = Path(self._tmp.name) / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q")
        self.write("AGENTS.md", "Root agent instructions.\n")
        self.write("anneal/AGENTS.md", HEADER_MD + "\n# Rules\n\n" + CRR)
        self.write("anneal/.gemini/styleguide.md", "# Style\n\n" + CRR)
        self.write("anneal/docs/existing.md", HEADER_MD + "\n" + "x" * 100
                   + " y\n")
        self.write("anneal/ci/existing.py", HEADER_PY + "\nVALUE = 1\n")
        self.write("anneal/ci/legacy.sh", "echo 1\necho 2\necho 3\necho 4\n")
        self.write("anneal/README.md", "Short readme.\n")
        self.commit("Initial commit")
        git(self.repo, "branch", "base")

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def write(self, rel: str, text: str) -> None:
        path = self.repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def commit(self, message: str = GOOD_MESSAGE, env=None) -> str:
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "--allow-empty", "-m", message, env=env)
        return git(self.repo, "rev-parse", "HEAD").strip()

    def run_check(self, *args: str, base: str | None = "base",
                  env: dict[str, str] | None = None
                  ) -> tuple[int, dict[str, object]]:
        cmd = [sys.executable, "-I", "-B", str(SCRIPT), "--repo",
               str(self.repo), "--json"]
        if base is not None:
            cmd += ["--base", base]
        res = subprocess.run(
            cmd + list(args), capture_output=True, text=True, check=False,
            env={**ambient_env(), **(env or {})},
        )
        return res.returncode, json.loads(res.stdout)

    def findings(self, *args: str, **kw) -> list[dict[str, object]]:
        return self.run_check(*args, **kw)[1]["findings"]

    def assert_finding(self, check: str, needle: str, *args: str,
                       **kw) -> dict[str, object]:
        found = self.findings(*args, **kw)
        for f in found:
            if f["check"] == check and needle in f["message"]:
                return f
        self.fail(f"no {check!r} finding containing {needle!r}: {found}")

    def assert_clean(self, *args: str, **kw) -> dict[str, object]:
        code, report = self.run_check(*args, **kw)
        self.assertEqual(report["findings"], [], report)
        self.assertEqual(code, 0)
        self.assertTrue(report["ok"])
        return report
