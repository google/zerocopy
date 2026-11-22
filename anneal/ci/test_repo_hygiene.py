# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Public repository hygiene checks for ``anneal/``."""

import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


ANNEAL_ROOT = Path(__file__).resolve().parent.parent

# Exclude pinned third-party corpora whose upstream contents are outside
# Anneal's authoring boundary.
_CONTENT_EXCLUDED_PREFIXES = ("vendor/lean-miri/",)

_EPHEMERAL_FILENAME_RE = re.compile(
    r"(^|/)(HANDOFF|PROGRESS|REPRODUCE|REVIEW_LEDGER)[^/]*\.md$",
    re.IGNORECASE,
)

# Documented agent and editor configuration files intentionally tracked under
# `anneal/`. Updating this allowlist requires a `ci/` Pass 2 update alongside
# `AGENTS.md` Gate 5 approval for any new nested editor/agent config path.
_ALLOWED_AGENT_CONFIG_PATHS = frozenset(
    {
        ".agents/skills.json",
        ".gemini/styleguide.md",
        "AGENTS.md",
        "CLAUDE.md",
    }
)

# Ambient override and editor configs forbidden anywhere in the tracked tree.
_UNCONDITIONAL_BANNED_NAMES = frozenset(
    {
        ".cargo",
        ".envrc",
        ".gitattributes",
        "agents.override.md",
        ".cursorrules",
        ".windsurfrules",
        ".clinerules",
        ".mcp.json",
    }
)

_UNLISTED_CONFIG_DIRS = frozenset(
    {
        ".agents",
        ".claude",
        ".gemini",
        ".codex",
        ".cursor",
        ".vscode",
        ".devcontainer",
        ".idea",
        ".zed",
    }
)

_AGENT_DOC_FILENAMES = frozenset({"agents.md", "claude.md", "gemini.md"})

_UNIX_HOME_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])(?:/home/|/Users/)([A-Za-z0-9._-]+)"
    r"(?=[/\\:\"'`)\s,;]|$)"
)
_UNIX_ROOT_RE = re.compile(
    r"(?<![A-Za-z0-9_.:/-])/root/([A-Za-z0-9._-]+)(?=[/\\:\"'`)\s,;]|$)"
)
_WINDOWS_HOME_RE = re.compile(
    r"(?i)(?<![A-Za-z0-9_.-])C:\\{1,2}Users\\{1,2}([A-Za-z0-9._-]+)"
    r"(?=[\\/'\"`)\s,;]|$)"
)

# Synthetic placeholder user names used in unit tests and documentation.
_PLACEHOLDER_HOME_USERS = frozenset(
    {"alice", "bob", "charlie", "user", "example", "test", "runner"}
)

# Documented synthetic `HOME=None` stems used in `toolchain.rs` unit tests.
_ALLOWED_SYNTHETIC_ROOT_STEMS = (
    "/root/.cache/anneal/",
    "/root/anneal/toolchain",
    "/root/.elan/",
)

# Inherited Git override variables that could redirect `-C <root>` commands.
_GIT_ENV_OVERRIDES = frozenset(
    {
        "GIT_DIR",
        "GIT_INDEX_FILE",
        "GIT_WORK_TREE",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_COMMON_DIR",
        "GIT_CEILING_DIRECTORIES",
        "GIT_CONFIG_PARAMETERS",
        "GIT_CONFIG_COUNT",
    }
)

_REGULAR_FILE_MODES = frozenset({"100644", "100755"})


class NotAGitWorktreeError(RuntimeError):
    """Raised when the inspected root is outside any Git worktree."""


def _git_env() -> dict[str, str]:
    """Return sanitized process environment for deterministic Git calls."""
    env = {
        key: value
        for key, value in os.environ.items()
        if key not in _GIT_ENV_OVERRIDES
    }
    env["LC_ALL"] = "C"
    return env


def _git_cmd(root: Path, *args: str) -> list[str]:
    """Build a side-effect-free ``git -C <root>`` command list."""
    return [
        "git",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "core.fsmonitor=false",
        "-C",
        str(root),
        *args,
    ]


def tracked_stage_entries(root: Path) -> list[tuple[str, str]]:
    """Return ``(mode, rel_path)`` pairs from ``git ls-files -z --stage``."""
    env = _git_env()
    probe = subprocess.run(
        _git_cmd(root, "rev-parse", "--is-inside-work-tree"),
        env=env,
        capture_output=True,
        text=True,
    )
    if (
        probe.returncode == 128
        and "not a git repository" in (probe.stderr or "").lower()
    ):
        raise NotAGitWorktreeError(f"{root} is not inside a Git worktree")
    if probe.returncode != 0 or probe.stdout.strip() != "true":
        raise subprocess.CalledProcessError(
            probe.returncode, probe.args, probe.stdout, probe.stderr
        )

    raw = subprocess.check_output(
        _git_cmd(root, "ls-files", "-z", "--stage"), env=env
    )
    entries: list[tuple[str, str]] = []
    for raw_entry in raw.split(b"\x00"):
        if not raw_entry:
            continue
        meta, sep, raw_path = raw_entry.partition(b"\t")
        if not sep or not raw_path:
            raise AssertionError(
                f"malformed git ls-files --stage record: {raw_entry!r}"
            )
        mode = meta.decode("ascii").split(" ", 1)[0]
        rel = raw_path.decode("utf-8", errors="surrogateescape")
        entries.append((mode, rel))
    if not entries:
        raise AssertionError(f"git ls-files returned no paths under {root}")
    return entries


def tracked_files(root: Path) -> list[str]:
    """Return NUL-delimited Git-tracked relative paths under ``root``."""
    return [rel for _, rel in tracked_stage_entries(root)]


def find_banned_paths(paths: list[str]) -> list[str]:
    """Return tracked paths violating ephemeral, toolchain, or config rules."""
    violations: list[str] = []
    for rel in paths:
        parts = PurePosixPath(rel).parts
        if not parts:
            continue
        lower_parts = tuple(part.lower() for part in parts)
        lower_name = lower_parts[-1]
        if _EPHEMERAL_FILENAME_RE.search(rel):
            violations.append(rel)
        elif any(
            part in _UNCONDITIONAL_BANNED_NAMES or part.startswith(".cargo")
            for part in lower_parts
        ):
            violations.append(rel)
        elif lower_name.startswith("rust-toolchain"):
            violations.append(rel)
        elif (
            lower_name == "lean-toolchain"
            and rel != "trusted/lean/lean-toolchain"
        ):
            violations.append(rel)
        elif rel not in _ALLOWED_AGENT_CONFIG_PATHS and (
            lower_name in _AGENT_DOC_FILENAMES
            or any(part in _UNLISTED_CONFIG_DIRS for part in lower_parts)
        ):
            violations.append(rel)
    return violations


def find_banned_entries(
    root: Path, entries: list[tuple[str, str]]
) -> list[str]:
    """Return path, symlink, and non-regular index entry violations."""
    violations = find_banned_paths([rel for _, rel in entries])
    for mode, rel in entries:
        if mode not in _REGULAR_FILE_MODES:
            violations.append(f"{rel} [non-regular-entry:{mode}]")
        elif (root / rel).is_symlink():
            violations.append(f"{rel} [symlink]")
    return violations


def _has_home_path_leak(line: str) -> bool:
    """Return whether ``line`` contains a non-placeholder home directory."""
    for pattern in (_UNIX_HOME_RE, _WINDOWS_HOME_RE):
        if any(
            match.group(1).lower() not in _PLACEHOLDER_HOME_USERS
            for match in pattern.finditer(line)
        ):
            return True
    return any(
        not line[match.start() :].startswith(_ALLOWED_SYNTHETIC_ROOT_STEMS)
        for match in _UNIX_ROOT_RE.finditer(line)
    )


def find_home_directory_leaks(root: Path, paths: list[str]) -> list[str]:
    """Return ``path:line`` home-directory hits in tracked UTF-8 files."""
    violations: list[str] = []
    for rel in paths:
        if rel.startswith(_CONTENT_EXCLUDED_PREFIXES):
            continue
        path = root / rel
        if path.is_symlink() or not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        for line_no, line in enumerate(text.splitlines(), 1):
            if _has_home_path_leak(line):
                violations.append(f"{rel}:{line_no} [home-directory-path]")
    return violations


class RepoHygieneTests(unittest.TestCase):
    def _anneal_tracked_entries(self) -> list[tuple[str, str]]:
        try:
            return tracked_stage_entries(ANNEAL_ROOT)
        except NotAGitWorktreeError as exc:
            self.skipTest(str(exc))

    def test_no_ephemeral_or_disallowed_config_paths(self) -> None:
        bad = find_banned_entries(
            ANNEAL_ROOT, self._anneal_tracked_entries()
        )
        self.assertEqual(
            bad,
            [],
            f"Tracked files contain disallowed paths or entries: {bad}",
        )

    def test_no_workstation_home_paths(self) -> None:
        paths = [rel for _, rel in self._anneal_tracked_entries()]
        violations = find_home_directory_leaks(ANNEAL_ROOT, paths)
        self.assertEqual(
            violations,
            [],
            "Workstation home directory paths found in tracked files:\n"
            + "\n".join(violations[:40]),
        )

    def test_rejects_banned_paths_and_allows_documented_paths(self) -> None:
        paths = [
            "README.md",
            "AGENTS.md",
            "CLAUDE.md",
            ".agents/skills.json",
            ".gemini/styleguide.md",
            "trusted/lean/lean-toolchain",
            "HANDOFF.md",
            "docs/PROGRESS.md",
            "notes/REPRODUCE-bug.md",
            "REVIEW_LEDGER.md",
            "docs/review_ledger.md",
            "notes/Review_Ledger-1.md",
            "sub/AGENTS.md",
            "Agents.md",
            "AGENTS.override.md",
            ".envrc",
            "sub/.gitattributes",
            ".cargo/config.toml",
            ".Cargo/config.toml",
            "rust-toolchain.toml",
            "rust-toolchain-nightly",
            "rust-toolchain-old",
            "Rust-Toolchain.toml",
            "theory/lean-toolchain",
            "theory/Lean-Toolchain",
            "trusted/lean/Lean-Toolchain",
            ".vscode/settings.json",
            ".VSCODE/settings.json",
            ".idea/workspace.xml",
            ".cursor/rules.md",
            ".claude/settings.json",
            ".Claude/settings.json",
            ".codex/config.toml",
            ".agents/extra.json",
        ]
        self.assertEqual(
            find_banned_paths(paths),
            [
                "HANDOFF.md",
                "docs/PROGRESS.md",
                "notes/REPRODUCE-bug.md",
                "REVIEW_LEDGER.md",
                "docs/review_ledger.md",
                "notes/Review_Ledger-1.md",
                "sub/AGENTS.md",
                "Agents.md",
                "AGENTS.override.md",
                ".envrc",
                "sub/.gitattributes",
                ".cargo/config.toml",
                ".Cargo/config.toml",
                "rust-toolchain.toml",
                "rust-toolchain-nightly",
                "rust-toolchain-old",
                "Rust-Toolchain.toml",
                "theory/lean-toolchain",
                "theory/Lean-Toolchain",
                "trusted/lean/Lean-Toolchain",
                ".vscode/settings.json",
                ".VSCODE/settings.json",
                ".idea/workspace.xml",
                ".cursor/rules.md",
                ".claude/settings.json",
                ".Claude/settings.json",
                ".codex/config.toml",
                ".agents/extra.json",
            ],
        )

    def test_rejects_symlink_and_gitlink_entries(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            env = _git_env()
            subprocess.run(
                _git_cmd(root, "init", "--quiet"), env=env, check=True
            )
            (root / "docs").mkdir()
            (root / "docs" / "link.md").symlink_to(
                "/" + "home/devuser/secret"
            )
            subprocess.run(_git_cmd(root, "add", "."), env=env, check=True)
            entries = tracked_stage_entries(root)
            self.assertEqual(entries, [("120000", "docs/link.md")])
            self.assertEqual(
                find_banned_entries(root, entries),
                ["docs/link.md [non-regular-entry:120000]"],
            )
            self.assertEqual(
                find_banned_entries(root, [("160000", "vendor/submod")]),
                ["vendor/submod [non-regular-entry:160000]"],
            )

    def test_rejects_home_paths_with_git_isolation_and_exemptions(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            env = _git_env()
            subprocess.run(
                _git_cmd(root, "init", "--quiet"),
                env=env,
                check=True,
            )
            (root / "docs").mkdir()
            (root / "vendor" / "lean-miri").mkdir(parents=True)
            (root / "ok.rs").write_text(
                'let home = "'
                + "/home/alice/.elan/bin/lean"
                + '";\n'
                + 'let mac = "'
                + "/Users/bob/cache"
                + '";\n'
                + 'let r1 = "/root/.cache/anneal/toolchain";\n'
                + 'let r2 = "/root/anneal/toolchain";\n'
                + 'let r3 = "/root/.elan/toolchains/v1/bin/lean";\n'
                + "let doc = https://example.com"
                + "/ho"
                + "me/devuser;\n",
                encoding="utf-8",
            )
            (root / "bin.dat").write_bytes(b"\xff\xfe\x00\x01")
            (root / "vendor" / "lean-miri" / "Upstream.lean").write_text(
                "/" + "home/devuser/upstream\n",
                encoding="utf-8",
            )
            (root / "docs" / "leak.md").write_text(
                "clean line\n"
                + "/"
                + "home/devuser/workspace/notes.md\n"
                + "/"
                + "Users/devuser/src/project\n"
                + r"C:\Us"
                + r"ers\devuser\code"
                + "\n"
                + r"C:\\Us"
                + r"ers\\devuser\\code"
                + "\n"
                + "/ro"
                + "ot/.codex/session\n"
                + '"/root/.cache/anneal/ok" "/ro'
                + 'ot/workspace/foo"\n',
                encoding="utf-8",
            )
            subprocess.run(_git_cmd(root, "add", "."), env=env, check=True)
            with mock.patch.dict(
                os.environ,
                {
                    "GIT_DIR": "/nonexistent/git-dir",
                    "GIT_INDEX_FILE": "/nonexistent/index",
                    "GIT_WORK_TREE": "/nonexistent/worktree",
                },
            ):
                paths = tracked_files(root)
            self.assertEqual(
                find_home_directory_leaks(root, paths),
                [
                    "docs/leak.md:2 [home-directory-path]",
                    "docs/leak.md:3 [home-directory-path]",
                    "docs/leak.md:4 [home-directory-path]",
                    "docs/leak.md:5 [home-directory-path]",
                    "docs/leak.md:6 [home-directory-path]",
                    "docs/leak.md:7 [home-directory-path]",
                ],
            )

    def test_non_git_directory_raises_not_a_git_worktree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            env = _git_env()
            env["GIT_CEILING_DIRECTORIES"] = str(root.parent)
            with mock.patch.object(
                sys.modules[__name__], "_git_env", return_value=env
            ):
                with self.assertRaises(NotAGitWorktreeError):
                    tracked_files(root)

    def test_inherited_git_ceiling_directories_does_not_hide_repo(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp).resolve()
            sub = repo / "sub"
            sub.mkdir()
            env = _git_env()
            subprocess.run(
                _git_cmd(repo, "init", "--quiet"), env=env, check=True
            )
            (sub / "ok.txt").write_text("ok\n", encoding="utf-8")
            subprocess.run(_git_cmd(repo, "add", "."), env=env, check=True)
            with mock.patch.dict(
                os.environ, {"GIT_CEILING_DIRECTORIES": str(repo)}
            ):
                self.assertEqual(
                    tracked_stage_entries(sub),
                    [("100644", "ok.txt")],
                )

    def test_dubious_ownership_exit_128_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dubious = subprocess.CompletedProcess(
                args=["git", "rev-parse", "--is-inside-work-tree"],
                returncode=128,
                stdout="",
                stderr="fatal: detected dubious ownership in repository",
            )
            with mock.patch.object(subprocess, "run", return_value=dubious):
                with self.assertRaises(subprocess.CalledProcessError):
                    tracked_files(root)


if __name__ == "__main__":
    unittest.main()
