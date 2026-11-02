#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Deterministic Git reproducer for GHerrit multi-remote base-branch resolution.

Reproduces the base-branch resolution mismatch in `joshlf/gherrit`
(`src/util/repository.rs:72-125` and `src/pre_push/mod.rs:146-162` at commit
`2dbcbb6174ac3cf75dd7fcd0ab15cb27027b405d`, and `src/util.rs:178-231` and
`src/pre_push/mod.rs:127-142` at commit
`86179afb27feabd50ddd7d2dc2493892885db8ba`):

1. `Repo::default_remote_name` reads `gherrit.remote` (defaulting to `"origin"`).
2. `Repo::find_default_branch_on_default_remote` reads
   `refs/remotes/<remote>/HEAD` and strips `refs/remotes/<remote>/` to obtain
   the short branch name (e.g., `"main"`).
3. `collect_commits` then resolves `refs/heads/<default_branch>` instead of
   `refs/remotes/<remote>/<default_branch>` before calling
   `Repo::commits_between(default_ref, head)`.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any

FIRST_GIT_TIMESTAMP = 946_684_800


class GitFixture:
    """Self-contained deterministic Git repository fixture."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.step = 0

    def env(self, *, advance_clock: bool = False) -> dict[str, str]:
        if advance_clock:
            self.step += 1
        timestamp = FIRST_GIT_TIMESTAMP + self.step * 60
        date_str = f"{timestamp} +0000"
        env = {
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "HOME": str(self.root),
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_TERMINAL_PROMPT": "0",
            "GIT_AUTHOR_NAME": "Test Author",
            "GIT_AUTHOR_EMAIL": "author@example.com",
            "GIT_COMMITTER_NAME": "Test Author",
            "GIT_COMMITTER_EMAIL": "author@example.com",
            "GIT_AUTHOR_DATE": date_str,
            "GIT_COMMITTER_DATE": date_str,
            "LC_ALL": "C",
        }
        return env

    def git(
        self,
        repo: Path,
        args: list[str],
        *,
        advance_clock: bool = False,
        check: bool = True,
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", *args],
            cwd=repo,
            env=self.env(advance_clock=advance_clock),
            text=True,
            capture_output=True,
            check=check,
        )

    def commit(
        self,
        repo: Path,
        subject: str,
        gherrit_id: str | None = None,
    ) -> str:
        message = subject
        if gherrit_id is not None:
            message = f"{subject}\n\ngherrit-pr-id: {gherrit_id}"
        self.git(
            repo,
            [
                "commit",
                "--allow-empty",
                "--no-verify",
                "--cleanup=verbatim",
                "-m",
                message,
            ],
            advance_clock=True,
        )
        return self.git(repo, ["rev-parse", "HEAD"]).stdout.strip()


def resolve_remote_and_default_branch(
    fx: GitFixture, repo: Path
) -> tuple[str, str]:
    """Mirrors `Repo::default_remote_name` and `find_default_branches`."""
    remote_proc = fx.git(
        repo, ["config", "--get", "gherrit.remote"], check=False
    )
    remote_name = (
        remote_proc.stdout.strip()
        if remote_proc.returncode == 0 and remote_proc.stdout.strip()
        else "origin"
    )

    branches: list[str] = []
    head_ref = f"refs/remotes/{remote_name}/HEAD"
    sym_proc = fx.git(repo, ["symbolic-ref", "-q", head_ref], check=False)
    if sym_proc.returncode == 0:
        target = sym_proc.stdout.strip()
        prefix = f"refs/remotes/{remote_name}/"
        if target.startswith(prefix):
            branches.append(target[len(prefix) :])

    cfg_proc = fx.git(
        repo, ["config", "--get", "init.defaultBranch"], check=False
    )
    if cfg_proc.returncode == 0 and cfg_proc.stdout.strip():
        branches.append(cfg_proc.stdout.strip())

    for candidate in ("main", "master", "trunk"):
        ref_proc = fx.git(
            repo,
            [" show-ref", "--verify", "--quiet", f"refs/heads/{candidate}"]
            if False
            else ["show-ref", "--verify", "--quiet", f"refs/heads/{candidate}"],
            check=False,
        )
        if ref_proc.returncode == 0:
            branches.append(candidate)

    branches.append("main")
    return remote_name, branches[0]


def commits_between(
    fx: GitFixture, repo: Path, ancestor_oid: str, descendant_oid: str
) -> tuple[bool, list[dict[str, str]]]:
    """Mirrors `Repo::commits_between` in `src/util/repository.rs:168-194`."""
    mb_proc = fx.git(
        repo, ["merge-base", ancestor_oid, descendant_oid], check=False
    )
    if mb_proc.returncode != 0 or mb_proc.stdout.strip() != ancestor_oid:
        return False, []

    log_proc = fx.git(
        repo,
        [
            "log",
            "--reverse",
            "--format=%H%x00%s%x00%(trailers:key=gherrit-pr-id,valueonly,unfold)",
            f"{ancestor_oid}..{descendant_oid}",
        ],
    )
    commits: list[dict[str, str]] = []
    for line in log_proc.stdout.splitlines():
        if not line:
            continue
        oid, subject, pr_id = line.split("\0")
        commits.append(
            {
                "oid": oid,
                "subject": subject,
                "gherrit_id": pr_id.strip(),
            }
        )
    return True, commits


def collect_commits_unpatched(
    fx: GitFixture, repo: Path, branch_name: str
) -> dict[str, Any]:
    """Mirrors unpatched `collect_commits` in `src/pre_push/mod.rs:146-162`."""
    remote_name, default_branch = resolve_remote_and_default_branch(fx, repo)
    head_oid = fx.git(repo, ["rev-parse", "HEAD"]).stdout.strip()
    resolved_ref = f"refs/heads/{default_branch}"
    default_oid = fx.git(repo, ["rev-parse", resolved_ref]).stdout.strip()
    ok, stack = commits_between(fx, repo, default_oid, head_oid)
    if not ok:
        return {
            "status": "error",
            "remote_name": remote_name,
            "default_branch": default_branch,
            "resolved_ref": resolved_ref,
            "resolved_oid": default_oid,
            "head_oid": head_oid,
            "error": (
                f"The branch '{branch_name}' is not based on '{default_branch}'.\n"
                "GHerrit only supports stacked branches that share history with "
                "the default branch.\n"
                f"Maybe you want to 'git rebase' on '{default_branch}' before pushing?"
            ),
        }
    return {
        "status": "ok",
        "remote_name": remote_name,
        "default_branch": default_branch,
        "resolved_ref": resolved_ref,
        "resolved_oid": default_oid,
        "head_oid": head_oid,
        "collected_count": len(stack),
        "collected_commits": stack,
    }


def collect_commits_patched(
    fx: GitFixture, repo: Path, branch_name: str
) -> dict[str, Any]:
    """Patched `collect_commits` resolving `refs/remotes/<remote>/<branch>` first."""
    remote_name, default_branch = resolve_remote_and_default_branch(fx, repo)
    head_oid = fx.git(repo, ["rev-parse", "HEAD"]).stdout.strip()

    remote_tracking_ref = f"refs/remotes/{remote_name}/{default_branch}"
    remote_check = fx.git(
        repo, ["rev-parse", "--verify", "--quiet", remote_tracking_ref], check=False
    )
    if remote_check.returncode == 0:
        resolved_ref = remote_tracking_ref
        default_oid = remote_check.stdout.strip()
        display_target = f"{remote_name}/{default_branch}"
    else:
        resolved_ref = f"refs/heads/{default_branch}"
        default_oid = fx.git(repo, ["rev-parse", resolved_ref]).stdout.strip()
        display_target = default_branch

    ok, stack = commits_between(fx, repo, default_oid, head_oid)
    if not ok:
        return {
            "status": "error",
            "remote_name": remote_name,
            "default_branch": default_branch,
            "resolved_ref": resolved_ref,
            "resolved_oid": default_oid,
            "head_oid": head_oid,
            "error": (
                f"The branch '{branch_name}' is not based on '{display_target}'.\n"
                "GHerrit only supports stacked branches that share history with "
                "the default branch.\n"
                f"Maybe you want to 'git rebase' on '{display_target}' before pushing?"
            ),
        }
    return {
        "status": "ok",
        "remote_name": remote_name,
        "default_branch": default_branch,
        "resolved_ref": resolved_ref,
        "resolved_oid": default_oid,
        "head_oid": head_oid,
        "collected_count": len(stack),
        "collected_commits": stack,
    }


def run_reproducer() -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        fx = GitFixture(root)

        origin_bare = root / "origin.git"
        secondary_bare = root / "secondary.git"
        local_repo = root / "worktree"
        origin_bare.mkdir()
        secondary_bare.mkdir()
        local_repo.mkdir()

        fx.git(origin_bare, ["init", "--bare", "--initial-branch=main"])
        fx.git(secondary_bare, ["init", "--bare", "--initial-branch=main"])
        fx.git(local_repo, ["init", "--initial-branch=main"])
        fx.git(local_repo, ["remote", "add", "origin", str(origin_bare)])
        fx.git(local_repo, ["remote", "add", "secondary", str(secondary_bare)])
        fx.git(local_repo, ["config", "gherrit.remote", "secondary"])

        # Commit A (initial root), U1, and B = U2 (stack base).
        oid_a = fx.commit(local_repo, "Initial root commit")
        oid_u1 = fx.commit(
            local_repo,
            "Upstream commit 1",
            "G0000000000000000000000000000001",
        )
        oid_b = fx.commit(
            local_repo,
            "Upstream commit 2 (stack base)",
            "G0000000000000000000000000000002",
        )

        # Seed both remotes at A initially, and origin at B.
        fx.git(local_repo, ["push", "origin", f"{oid_b}:refs/heads/main"])
        fx.git(local_repo, ["push", "secondary", f"{oid_a}:refs/heads/main"])
        fx.git(local_repo, ["fetch", "origin"])
        fx.git(local_repo, ["fetch", "secondary"])
        fx.git(
            local_repo,
            [
                "symbolic-ref",
                "refs/remotes/secondary/HEAD",
                "refs/remotes/secondary/main",
            ],
        )

        # Create managed feature stack B -> C1 -> C2 -> C3.
        fx.git(local_repo, ["checkout", "-b", "feature-stack", oid_b])
        fx.git(
            local_repo,
            ["config", "branch.feature-stack.gherritManaged", "managedPrivate"],
        )
        fx.git(local_repo, ["config", "branch.feature-stack.pushRemote", "."])
        fx.git(local_repo, ["config", "branch.feature-stack.remote", "."])
        fx.git(
            local_repo,
            ["config", "branch.feature-stack.merge", "refs/heads/feature-stack"],
        )

        oid_c1 = fx.commit(
            local_repo,
            "Feature commit 1",
            "G1000000000000000000000000000001",
        )
        oid_c2 = fx.commit(
            local_repo,
            "Feature commit 2",
            "G1000000000000000000000000000002",
        )
        oid_c3 = fx.commit(
            local_repo,
            "Feature commit 3",
            "G1000000000000000000000000000003",
        )

        # Scenario 2A: secondary/main is behind stack base B (at A), while local
        # refs/heads/main is at B.
        s2_before_ff_unpatched = collect_commits_unpatched(
            fx, local_repo, "feature-stack"
        )
        s2_before_ff_patched = collect_commits_patched(
            fx, local_repo, "feature-stack"
        )

        # Scenario 2B: Both local refs/heads/main and secondary/main are at A
        # (behind stack base B).
        fx.git(local_repo, ["update-ref", "refs/heads/main", oid_a])
        s2_local_also_behind_unpatched = collect_commits_unpatched(
            fx, local_repo, "feature-stack"
        )

        # Fast-forward secondary/main to stack base B.
        fx.git(local_repo, ["push", "secondary", f"{oid_b}:refs/heads/main"])
        fx.git(local_repo, ["fetch", "secondary"])

        # Scenario 1: Local refs/heads/main advances on origin/main to M1 (past
        # stack base B), while secondary/main equals B.
        fx.git(local_repo, ["checkout", "main"])
        fx.git(local_repo, ["reset", "--hard", oid_b])
        oid_m1 = fx.commit(
            local_repo,
            "Origin main advancement past stack base",
            "G2000000000000000000000000000001",
        )
        fx.git(local_repo, ["push", "origin", f"{oid_m1}:refs/heads/main"])
        fx.git(local_repo, ["checkout", "feature-stack"])

        s1_unpatched = collect_commits_unpatched(fx, local_repo, "feature-stack")
        s1_patched = collect_commits_patched(fx, local_repo, "feature-stack")

        # Scenario 3: Local-only repository without remote-tracking ref falls
        # back to refs/heads/main and rejects orphan branch.
        local_only = root / "local-only"
        local_only.mkdir()
        fx.git(local_only, ["init", "--initial-branch=main"])
        oid_local_root = fx.commit(local_only, "Local root")
        fx.git(local_only, ["checkout", "--orphan", "lonely-branch"])
        oid_lonely = fx.commit(
            local_only,
            "Lonely commit",
            "G3000000000000000000000000000001",
        )
        s3_unpatched = collect_commits_unpatched(
            fx, local_only, "lonely-branch"
        )
        s3_patched = collect_commits_patched(fx, local_only, "lonely-branch")

        # Assertions verifying all claims.
        assert s1_unpatched["status"] == "error"
        assert (
            "The branch 'feature-stack' is not based on 'main'."
            in s1_unpatched["error"]
        )
        assert s1_patched["status"] == "ok"
        assert [c["oid"] for c in s1_patched["collected_commits"]] == [
            oid_c1,
            oid_c2,
            oid_c3,
        ]

        assert s2_before_ff_patched["status"] == "ok"
        assert [
            c["oid"] for c in s2_before_ff_patched["collected_commits"]
        ] == [oid_u1, oid_b, oid_c1, oid_c2, oid_c3]
        assert s2_local_also_behind_unpatched["status"] == "ok"
        assert [
            c["oid"]
            for c in s2_local_also_behind_unpatched["collected_commits"]
        ] == [oid_u1, oid_b, oid_c1, oid_c2, oid_c3]

        assert s3_unpatched["status"] == "error"
        assert s3_patched["status"] == "error"
        assert s3_patched["resolved_ref"] == "refs/heads/main"

        return {
            "git_commits": {
                "A_root": oid_a,
                "U1_upstream": oid_u1,
                "B_stack_base": oid_b,
                "C1_stack": oid_c1,
                "C2_stack": oid_c2,
                "C3_stack_head": oid_c3,
                "M1_local_main_ahead": oid_m1,
                "local_only_root": oid_local_root,
                "local_only_orphan": oid_lonely,
            },
            "scenario_1_local_main_ahead_of_secondary_main": {
                "refs_heads_main": oid_m1,
                "refs_remotes_secondary_main": oid_b,
                "head": oid_c3,
                "unpatched_collect_commits": s1_unpatched,
                "patched_collect_commits": s1_patched,
            },
            "scenario_2_remote_main_behind_stack_base": {
                "refs_remotes_secondary_main_before_ff": oid_a,
                "stack_base": oid_b,
                "head": oid_c3,
                "patched_when_remote_behind": s2_before_ff_patched,
                "unpatched_when_local_main_also_behind": (
                    s2_local_also_behind_unpatched
                ),
                "unpatched_when_local_main_reset_to_stack_base": (
                    s2_before_ff_unpatched
                ),
                "patched_after_remote_fast_forward_to_base": s1_patched,
            },
            "scenario_3_local_only_fallback_orphan_rejection": {
                "unpatched": s3_unpatched,
                "patched": s3_patched,
            },
        }


def main() -> int:
    results = run_reproducer()
    json.dump(results, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
