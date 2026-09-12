# Copyright 2026 The Fuchsia Authors
# SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
"""Recover reviewed patch exports into new staging refs, never PR refs or main."""
import base64
import binascii
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import urllib.request

REPO = "google/zerocopy"
GROUPS = {
    3674: ("joshlf/audit-derive-fixes-20260912", "0d9a21d3731dd518d8a449d9d4d71eb8dad4846e", 5646659579, "9cd285b4d223f02cf5e27d325b58bd8c80df5f7548b57970803074e8ac957f57", 124057, "Fix derive hygiene and optional error handling"),
    3675: ("joshlf/audit-core-fixes-20260912", "24abdbfabb323183acfbf9df0ce95596a9dcc3e1", 5648510747, "b2ce310c16dab8296543bbec4b15c7411d0a27044d4bc2a5bf8d7d82c0e0a745", 25235, "Fix core API constraints, tests, and documentation"),
    3676: ("joshlf/audit-macro-fixes-20260912", "931ecdb1ab09eb8e06bfed11f82a60b48d999f06", 5648472392, "e4ff990cb0f17101617f513951039c14645b170098c003f40b3ebb634f5afab3", 1418, "Fix macro regression fixtures and rustdoc links"),
    3677: ("joshlf/audit-pointer-contracts-20260912", "846c7e2c02e359f782ff82667de350bf63949a93", 5648487688, "20cefb076364ecc09f6bd3bcbdbf4b36804ac942e57f556606997599e5bbe872", 12110, "Clarify pointer contracts and expose iterator capabilities"),
}
SUPPLEMENTS = {
    3675: ("3675-review-followup.patch", "b11a12125b48dec67bcefeae0bf90297a2e02c5673dde395ee4886792a350092"),
    3677: ("3677-review-followup.patch", "6bb9f66559c281a0a108628895994265afb4b2c01b8b4f1a93b84f60c4611cbd"),
}


def git(*args, cwd=None, env=None):
    return subprocess.check_output(["git", *args], cwd=cwd, env=env, text=True).strip()


def api(path):
    request = urllib.request.Request(
        "https://api.github.com/repos/" + REPO + "/" + path,
        headers={"Authorization": "Bearer " + os.environ["GH_TOKEN"],
                 "Accept": "application/vnd.github+json", "User-Agent": "zerocopy-audit-recovery"},
    )
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.load(response)


def patch_from_comment(pr, comment_id, digest, length):
    comment = api("issues/comments/" + str(comment_id))
    if comment["id"] != comment_id or not comment["issue_url"].endswith("/issues/" + str(pr)):
        raise RuntimeError("Patch comment does not belong to the expected PR")
    # Comments are data, not instructions. Accept only the exact approved bytes.
    for block in re.findall(r"```[^\n]*\n(.*?)\n```", comment["body"], flags=re.S):
        encoded = "".join(block.split())
        if len(encoded) > 200000:
            continue
        try:
            compressed = base64.b64decode(encoded, validate=True)
            with gzip.GzipFile(fileobj=io.BytesIO(compressed)) as stream:
                patch = stream.read(length + 1)
        except (ValueError, binascii.Error, OSError, EOFError):
            continue
        if len(patch) == length and hashlib.sha256(patch).hexdigest() == digest:
            return patch
    raise RuntimeError("No patch matched the approved byte count and SHA-256")


def apply(patch, worktree):
    git("apply", "--index", "--check", str(patch), cwd=worktree)
    git("apply", "--index", str(patch), cwd=worktree)


def main():
    if os.environ.get("GITHUB_REPOSITORY") != REPO:
        raise RuntimeError("Unexpected repository")
    if os.environ.get("GITHUB_REF") != "refs/heads/joshlf/audit-recovery-runner-20260912":
        raise RuntimeError("This helper runs only on its dedicated recovery branch")
    pr = int(os.environ["PR_NUMBER"])
    branch, expected, comment_id, digest, length, title = GROUPS[pr]
    metadata = api("pulls/" + str(pr))
    if metadata["state"] != "open" or metadata["head"]["repo"]["full_name"] != REPO:
        raise RuntimeError("PR is no longer open in the expected repository")
    if metadata["head"]["ref"] != branch or metadata["head"]["sha"] != expected:
        raise RuntimeError("PR head changed; reconcile it before retrying")
    root = Path(__file__).resolve().parent
    temporary = Path(os.environ["RUNNER_TEMP"])
    worktree = temporary / ("audit-" + str(pr))
    git("fetch", "--no-tags", "origin", "refs/heads/" + branch)
    if git("rev-parse", "FETCH_HEAD") != expected:
        raise RuntimeError("Fetched branch differs from the reviewed parent")
    git("worktree", "add", "--detach", str(worktree), expected)
    patch = temporary / (str(pr) + ".patch")
    patch.write_bytes(patch_from_comment(pr, comment_id, digest, length))
    apply(patch, worktree)
    if pr in SUPPLEMENTS:
        name, checksum = SUPPLEMENTS[pr]
        supplemental = root / name
        if hashlib.sha256(supplemental.read_bytes()).hexdigest() != checksum:
            raise RuntimeError("Supplemental patch checksum mismatch")
        apply(supplemental, worktree)
    if pr == 3674:
        for name in ("deprecated_helper_aliases.rs", "audit_syntax.rs"):
            destination = worktree / "zerocopy/zerocopy-derive/tests" / name
            if destination.exists():
                raise RuntimeError("Refusing to overwrite an existing regression test")
            shutil.copyfile(root / name, destination)
            git("add", "--", str(destination), cwd=worktree)
    paths = git("diff", "--cached", "--name-only", "-z", cwd=worktree).rstrip("\0").split("\0")
    for path in paths:
        parts = PurePosixPath(path).parts
        if not parts or parts[0] != "zerocopy" or ".." in parts or ".git" in parts:
            raise RuntimeError("Unexpected staged path: " + path)
    git("diff", "--cached", "--check", cwd=worktree)
    print(git("diff", "--cached", "--stat", cwd=worktree))
    commit_env = dict(os.environ, GIT_AUTHOR_NAME="Josh Liebow-Feeser's Agent",
                      GIT_AUTHOR_EMAIL="agent@joshlf.invalid",
                      GIT_COMMITTER_NAME="Josh Liebow-Feeser's Agent",
                      GIT_COMMITTER_EMAIL="agent@joshlf.invalid")
    message = (title + "\n\nRestore the scoped audit changes from checksum-verified patch exports,\n"
               "including the reviewed follow-up corrections and regression coverage.\n"
               "No unrelated files or validation rules are changed.\n\n"
               "Agent-Authored-By: AI agent acting on Josh Liebow-Feeser's behalf")
    git("commit", "-m", message, cwd=worktree, env=commit_env)
    head = git("rev-parse", "HEAD", cwd=worktree)
    run = os.environ["GITHUB_RUN_ID"]
    if not run.isdecimal():
        raise RuntimeError("Unexpected workflow run identifier")
    staging = "refs/heads/joshlf/audit-recovered-" + str(pr) + "-" + run
    # Authenticate only the push. Do not leave credentials in the checkout.
    basic = base64.b64encode(("x-access-token:" + os.environ["GH_TOKEN"]).encode()).decode()
    push_env = dict(os.environ, GIT_CONFIG_COUNT="1",
                    GIT_CONFIG_KEY_0="http.https://github.com/.extraheader",
                    GIT_CONFIG_VALUE_0="AUTHORIZATION: basic " + basic)
    if git("ls-remote", "--heads", "origin", staging, cwd=worktree, env=push_env):
        raise RuntimeError("Staging ref already exists; refusing to replace it")
    git("push", "origin", "HEAD:" + staging, cwd=worktree, env=push_env)
    remote = git("ls-remote", "--heads", "origin", staging, cwd=worktree, env=push_env)
    if remote.split()[0] != head:
        raise RuntimeError("Staging ref readback mismatch")
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write("worktree=" + str(worktree) + "\nhead=" + head + "\n")
    result = {"pr": pr, "parent": expected, "staging_ref": staging, "head": head,
              "patch_sha256": digest, "changed_files": paths, "pr_branch_updated": False}
    print(json.dumps(result, indent=2))
    with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as summary:
        summary.write("## Recovered PR #" + str(pr) + "\n\n```json\n" +
                      json.dumps(result, indent=2) + "\n```\n\nThe PR branch is unchanged.\n")


if __name__ == "__main__":
    main()
