#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Crate-agnostic, path-scoped GitHub release notes generator.

Computes release notes for any crate or directory subset in a multi-crate
repository:
  1. Decomposes `--tag` into `(prefix, semver)` and discovers the previous
     tag with the same prefix along the target commit's first-parent history
     using strict SemVer 2.0.0 precedence (stable releases skip prereleases;
     prereleases consider both).
  2. Lists first-parent commits touching `--path` since the previous tag.
  3. Resolves commit SHAs to merged PRs in batches via GitHub GraphQL,
     filtering out excluded labels and authors while falling back to direct
     commit bullets for commits without a matching merged PR.
  4. Identifies first-time repository contributors (`## New Contributors`)
     via batched GraphQL search and writes GitHub-compatible Markdown to
     stdout.
"""

from __future__ import annotations

import argparse
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

EXCLUDED_LABELS = frozenset({"hide-from-release-notes"})
EXCLUDED_AUTHORS = frozenset({"dependabot[bot]"})
EXCLUDED_AUTHORS_LOWER = frozenset(a.lower() for a in EXCLUDED_AUTHORS)
# `google-pr-creation-bot` is a GitHub `User` (not a `Bot`) that authors both
# labeled version-bump PRs and unlabeled backport PRs. Do not exclude it from
# `What's Changed`, but never celebrate it under `New Contributors`.
NEW_CONTRIBUTOR_EXCLUDED_USERS_LOWER = frozenset({"google-pr-creation-bot"})

PR_BATCH_SIZE = 50
COMMIT_BATCH_SIZE = 50
SEARCH_BATCH_SIZE = 20
MAX_GRAPHQL_INT = 2_147_483_647
RETRY_BACKOFF_SECONDS = (2.0, 5.0)

_PRE_ID = r"(?:0|[1-9][0-9]*|[0-9]*[A-Za-z-][0-9A-Za-z-]*)"
_BUILD_ID = r"[0-9A-Za-z-]+"
_SEMVER_CORE = (
    rf"(?P<major>0|[1-9][0-9]*)\."
    rf"(?P<minor>0|[1-9][0-9]*)\."
    rf"(?P<patch>0|[1-9][0-9]*)"
    rf"(?:-(?P<prerelease>{_PRE_ID}(?:\.{_PRE_ID})*))?"
    rf"(?:\+(?P<build>{_BUILD_ID}(?:\.{_BUILD_ID})*))?"
)
# Prefix never contains `.` and never ends with a digit, making `(prefix,
# version)` mathematically unique for every string while excluding leading
# `-`/`/`, `..`, `//`, and git-ref glob metacharacters.
_PREFIX_SEG = r"[A-Za-z0-9][A-Za-z0-9_]*(?:[-/][A-Za-z0-9][A-Za-z0-9_]*)*"
_PREFIX_RE = rf"(?:(?:{_PREFIX_SEG}[-/])?v|{_PREFIX_SEG}[-/])?"
TAG_RE = re.compile(rf"\A(?P<prefix>{_PREFIX_RE})(?P<version>{_SEMVER_CORE})\Z")

_SAFE_TAG_RE = re.compile(r"\A[A-Za-z0-9][A-Za-z0-9_./+-]*\Z")
_HEX_SHA_RE = re.compile(r"\A[0-9a-f]{40}\Z")
_REPO_SLUG_RE = re.compile(
    r"\A(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+)\Z"
)
_ORIGIN_REPO_RE = re.compile(
    r"(?:\A(?:https?|ssh)://(?:[^/@\s]+@)?github\.com/|"
    r"\Agit@github\.com:)"
    r"(?P<owner>[A-Za-z0-9_.-]+)/(?P<repo>[A-Za-z0-9_.-]+?)(?:\.git)?/?\Z"
)
_TRAILING_PR_RE = re.compile(r"\(#([1-9][0-9]*)\)\s*\Z")
_GITHUB_LOGIN_RE = re.compile(r"\A[A-Za-z0-9-]+\Z")
_ISO_UTC_RE = re.compile(r"\A\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z\Z")

_TRANSIENT_ERR_PATTERNS = (
    "http 500",
    "http 502",
    "http 503",
    "http 504",
    "http 429",
    "bad gateway",
    "service unavailable",
    "gateway timeout",
    "something went wrong",
    "rate limit",
    "secondary rate limit",
    "abuse detection",
    "timed out",
    "timeout",
    "connection reset",
    "connection refused",
    "temporary failure",
    "unexpected eof",
    "tls handshake",
)
_TRANSIENT_GQL_TYPES = frozenset(
    {"RATE_LIMITED", "INTERNAL", "SERVICE_UNAVAILABLE"}
)

_PR_SELECTION = (
    "number title url merged mergedAt "
    "mergeCommit { oid } "
    "repository { nameWithOwner } "
    "author { __typename login } "
    "labels(first: 50) { pageInfo { hasNextPage } nodes { name } }"
)


@dataclass(frozen=True)
class SemVer:
    """SemVer 2.0.0 version with full precedence comparison."""

    major: int
    minor: int
    patch: int
    prerelease: tuple[str, ...] = ()
    build: str | None = None

    @property
    def is_prerelease(self) -> bool:
        return bool(self.prerelease)

    def precedence_key(
        self,
    ) -> tuple[int, int, int, int, tuple[tuple[int, int | str], ...]]:
        """Return SemVer 2.0.0 Section 11 precedence key (ignores build)."""
        if not self.prerelease:
            return (self.major, self.minor, self.patch, 1, ())
        parts: list[tuple[int, int | str]] = []
        for ident in self.prerelease:
            if ident.isascii() and ident.isdigit():
                parts.append((0, int(ident)))
            else:
                parts.append((1, ident))
        return (self.major, self.minor, self.patch, 0, tuple(parts))

    def precedence_lt(self, other: SemVer) -> bool:
        return self.precedence_key() < other.precedence_key()


@dataclass(frozen=True)
class CommitInfo:
    sha: str
    subject: str


@dataclass(frozen=True)
class PullRequestInfo:
    number: int
    title: str
    url: str
    merge_commit_oid: str
    merged_at: str
    author_login: str | None
    author_type: str | None
    labels: frozenset[str]


@dataclass(frozen=True)
class ChangelogEntry:
    bullet: str
    author_login: str | None = None
    author_type: str | None = None
    merged_at: str | None = None
    pr_url: str | None = None


@dataclass(frozen=True)
class NewContributor:
    login: str
    pr_url: str


def parse_tag(tag: str) -> tuple[str, SemVer]:
    """Decompose a release tag into `(prefix, SemVer)` or raise `ValueError`."""
    match = TAG_RE.match(tag)
    if not match:
        raise ValueError(
            f"Tag {tag!r} does not match `<prefix><semver>` "
            "(e.g. `v0.8.64`, `anneal-v0.1.0-alpha.24`)"
        )
    pre_raw = match.group("prerelease")
    pre = tuple(pre_raw.split(".")) if pre_raw else ()
    semver = SemVer(
        major=int(match.group("major")),
        minor=int(match.group("minor")),
        patch=int(match.group("patch")),
        prerelease=pre,
        build=match.group("build"),
    )
    return match.group("prefix"), semver


def normalize_paths(raw_paths: Sequence[str]) -> tuple[str, ...]:
    """Validate and normalize repo-root-relative POSIX `--path` arguments."""
    if not raw_paths:
        raise ValueError("At least one `--path` argument is required")
    normalized: list[str] = []
    seen: set[str] = set()
    for raw in raw_paths:
        if not raw:
            raise ValueError("`--path` must not be empty")
        if any(ord(ch) < 32 or ord(ch) == 127 for ch in raw):
            raise ValueError(f"Invalid control character in `--path`: {raw!r}")
        if raw.startswith("/") or raw.startswith(":") or "\\" in raw:
            raise ValueError(
                f"`--path` must be a relative POSIX path without leading "
                f"`/` or `:`: {raw!r}"
            )
        stripped = raw.rstrip("/")
        if not stripped:
            raise ValueError(f"`--path` must name a repo subdirectory: {raw!r}")
        parts = stripped.split("/")
        if any(part in ("", ".", "..") for part in parts):
            raise ValueError(
                f"`--path` must not contain empty, `.`, or `..` segments: "
                f"{raw!r}"
            )
        norm = "/".join(parts)
        if norm not in seen:
            seen.add(norm)
            normalized.append(norm)
    return tuple(normalized)


def validate_repo_slug(slug: str) -> tuple[str, str]:
    """Validate an `OWNER/REPO` slug and return `(owner, repo)`."""
    match = _REPO_SLUG_RE.match(slug)
    if not match:
        raise ValueError(
            f"Invalid repository slug (expected OWNER/REPO): {slug!r}"
        )
    owner = match.group("owner")
    repo = match.group("repo")
    if owner in (".", "..") or repo in (".", ".."):
        raise ValueError(f"Invalid repository slug: {slug!r}")
    return owner, repo


def parse_github_remote_url(url: str) -> tuple[str, str]:
    """Extract `(owner, repo)` from a GitHub git remote URL."""
    match = _ORIGIN_REPO_RE.match(url.strip())
    if not match:
        raise ValueError(
            f"Could not parse GitHub OWNER/REPO from origin URL: {url!r}"
        )
    return validate_repo_slug(f"{match.group('owner')}/{match.group('repo')}")


def validate_git_ref_arg(ref: str, *, flag_name: str) -> str:
    """Reject empty, option-like, whitespace, or range-like ref arguments."""
    if not ref:
        raise ValueError(f"`{flag_name}` must not be empty")
    if ref.startswith("-"):
        raise ValueError(f"`{flag_name}` must not start with `-`: {ref!r}")
    if ".." in ref or any(ch.isspace() or ord(ch) < 32 for ch in ref):
        raise ValueError(f"Invalid `{flag_name}` ref: {ref!r}")
    return ref


def validate_tag_name(tag: str, *, flag_name: str) -> str:
    """Validate a tag name for safe git ref lookup and changelog URLs."""
    if (
        not _SAFE_TAG_RE.match(tag)
        or ".." in tag
        or "//" in tag
        or tag.endswith("/")
    ):
        raise ValueError(f"Invalid `{flag_name}` tag name: {tag!r}")
    return tag


def _run_git(
    repo_root: Path, args: Sequence[str], *, check: bool = True
) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo_root), *args],
        text=True,
        capture_output=True,
        check=False,
    )
    if check and proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip()
        raise RuntimeError(
            f"git {' '.join(args)} failed (exit {proc.returncode}): {detail}"
        )
    return proc.stdout


def _try_git_rev_parse_commit(repo_root: Path, rev: str) -> str | None:
    proc = subprocess.run(
        ["git", "-C", str(repo_root), "rev-parse", "--verify", "--quiet", rev],
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        return None
    sha = proc.stdout.strip()
    return sha if _HEX_SHA_RE.match(sha) else None


def find_repo_root(cwd: Path | None = None) -> Path:
    """Return the enclosing git repository root."""
    proc = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=str(cwd) if cwd is not None else None,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0 or not proc.stdout.strip():
        detail = proc.stderr.strip() or "not inside a git repository"
        raise RuntimeError(f"Failed to locate git repository root: {detail}")
    return Path(proc.stdout.strip())


def ensure_not_shallow(repo_root: Path, target_sha: str) -> None:
    """Fail closed if `target_sha`'s history is shallowly truncated.

    Repositories may carry unrelated shallow grafts (for example, on an orphan
    or vendored tag) while the target branch itself has complete history. Only
    fail when a shallow graft lies within `target_sha`'s ancestry, or when the
    shallow boundary cannot be read.
    """
    out = _run_git(repo_root, ["rev-parse", "--is-shallow-repository"]).strip()
    if out != "true":
        return
    raw_path = _run_git(
        repo_root, ["rev-parse", "--git-path", "shallow"]
    ).strip()
    shallow_path = Path(raw_path)
    if not shallow_path.is_absolute():
        shallow_path = repo_root / shallow_path
    if not shallow_path.is_file():
        raise RuntimeError(
            "Shallow git repository detected with unreadable shallow boundary "
            "(`fetch-depth: 0` is required)"
        )
    shallow_shas = {
        line.strip()
        for line in shallow_path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    if not shallow_shas or any(not _HEX_SHA_RE.match(s) for s in shallow_shas):
        raise RuntimeError(
            "Shallow git repository detected with malformed shallow boundary "
            "(`fetch-depth: 0` is required)"
        )
    ancestors = set(_run_git(repo_root, ["rev-list", target_sha]).splitlines())
    if shallow_shas & ancestors:
        raise RuntimeError(
            "Shallow git repository detected on target commit history "
            "(`fetch-depth: 0` is required for accurate baseline tag "
            "discovery and commit traversal)"
        )


def resolve_target_sha(
    repo_root: Path, tag: str, target: str | None
) -> str:
    """Resolve the release target commit SHA."""
    if target is not None:
        validate_git_ref_arg(target, flag_name="--target")
        sha = _try_git_rev_parse_commit(repo_root, f"{target}^{{commit}}")
        if sha is None:
            raise RuntimeError(
                f"Target ref {target!r} does not resolve to a commit"
            )
        return sha
    tag_sha = _try_git_rev_parse_commit(
        repo_root, f"refs/tags/{tag}^{{commit}}"
    )
    if tag_sha is not None:
        return tag_sha
    head_sha = _try_git_rev_parse_commit(repo_root, "HEAD^{commit}")
    if head_sha is None:
        raise RuntimeError("Failed to resolve `HEAD` to a commit")
    return head_sha


def validate_paths_exist(
    repo_root: Path, target_sha: str, paths: Sequence[str]
) -> None:
    """Fail closed if any requested `--path` is absent at `target_sha`."""
    for path in paths:
        proc = subprocess.run(
            [
                "git",
                "-C",
                str(repo_root),
                "cat-file",
                "-e",
                f"{target_sha}:{path}",
            ],
            text=True,
            capture_output=True,
            check=False,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                f"Path {path!r} does not exist at target commit "
                f"{target_sha[:12]}"
            )


def resolve_repo_slug(
    repo_root: Path, repo_arg: str | None
) -> tuple[str, str]:
    """Resolve `(owner, repo)` from `--repo`, `GITHUB_REPOSITORY`, or origin."""
    if repo_arg:
        return validate_repo_slug(repo_arg)
    env_repo = os.environ.get("GITHUB_REPOSITORY", "").strip()
    if env_repo:
        return validate_repo_slug(env_repo)
    origin_url = _run_git(repo_root, ["remote", "get-url", "origin"]).strip()
    return parse_github_remote_url(origin_url)


def find_previous_tag(
    repo_root: Path,
    target_sha: str,
    prefix: str,
    new_semver: SemVer,
    explicit_previous_tag: str | None = None,
) -> tuple[str, str] | None:
    """Return `(prev_tag, prev_sha)` or `None` for an initial release."""
    if explicit_previous_tag is not None:
        prev_tag = validate_tag_name(
            explicit_previous_tag, flag_name="--previous-tag"
        )
        prev_sha = _try_git_rev_parse_commit(
            repo_root, f"refs/tags/{prev_tag}^{{commit}}"
        )
        if prev_sha is None:
            raise RuntimeError(
                f"Previous tag {prev_tag!r} does not exist or is not a commit"
            )
        return prev_tag, prev_sha

    fmt = (
        "%(if)%(*objectname)%(then)%(*objectname)%(else)%(objectname)%(end)%09"
        "%(if)%(*objecttype)%(then)%(*objecttype)%(else)%(objecttype)%(end)%09"
        "%(refname:lstrip=2)"
    )
    out = _run_git(
        repo_root,
        [
            "for-each-ref",
            f"--merged={target_sha}",
            f"--format={fmt}",
            f"refs/tags/{prefix}*",
        ],
    )
    candidate_re = re.compile(
        rf"\A{re.escape(prefix)}(?P<version>{_SEMVER_CORE})\Z"
    )
    # Map commit SHA -> best `(precedence_key, tag_name)` for that commit.
    best_by_sha: dict[
        str,
        tuple[
            tuple[int, int, int, int, tuple[tuple[int, int | str], ...]], str
        ],
    ] = {}
    for line in out.splitlines():
        if not line:
            continue
        parts = line.split("\t", 2)
        if len(parts) != 3:
            continue
        sha, obj_type, tag_name = parts
        if obj_type != "commit" or not _HEX_SHA_RE.match(sha):
            continue
        match = candidate_re.match(tag_name)
        if not match:
            continue
        pre_raw = match.group("prerelease")
        cand = SemVer(
            major=int(match.group("major")),
            minor=int(match.group("minor")),
            patch=int(match.group("patch")),
            prerelease=tuple(pre_raw.split(".")) if pre_raw else (),
            build=match.group("build"),
        )
        if not cand.precedence_lt(new_semver):
            continue
        if not new_semver.is_prerelease and cand.is_prerelease:
            continue
        rank = (cand.precedence_key(), tag_name)
        existing = best_by_sha.get(sha)
        if existing is None or rank > existing:
            best_by_sha[sha] = rank

    if not best_by_sha:
        return None

    rev_out = _run_git(
        repo_root, ["rev-list", "--first-parent", target_sha]
    )
    for sha in rev_out.splitlines():
        if sha in best_by_sha:
            return best_by_sha[sha][1], sha
    return None


def list_scoped_commits(
    repo_root: Path,
    target_sha: str,
    prev_sha: str | None,
    paths: Sequence[str],
) -> tuple[CommitInfo, ...]:
    """List first-parent commits touching `paths` in chronological order."""
    rev_range = f"{prev_sha}..{target_sha}" if prev_sha else target_sha
    pathspecs = [f":(literal){p}" for p in paths]
    out = _run_git(
        repo_root,
        [
            "log",
            "--first-parent",
            "--reverse",
            "-z",
            "--format=%H%x09%s",
            rev_range,
            "--",
            *pathspecs,
        ],
    )
    commits: list[CommitInfo] = []
    for record in out.split("\x00"):
        if not record:
            continue
        sha, sep, subject = record.partition("\t")
        if not sep or not _HEX_SHA_RE.match(sha):
            raise RuntimeError(f"Unexpected git log record: {record!r}")
        commits.append(CommitInfo(sha=sha, subject=subject))
    return tuple(commits)


def extract_trailing_pr_number(subject: str) -> int | None:
    """Extract a valid 32-bit GraphQL PR number from trailing `(#N)`."""
    match = _TRAILING_PR_RE.search(subject)
    if not match:
        return None
    num = int(match.group(1))
    if num <= 0 or num > MAX_GRAPHQL_INT:
        return None
    return num


def _is_transient_graphql_failure(
    stderr: str, errors: Sequence[Mapping[str, object]]
) -> bool:
    lower_err = stderr.lower()
    if any(pat in lower_err for pat in _TRANSIENT_ERR_PATTERNS):
        return True
    for err in errors:
        err_type = err.get("type")
        if isinstance(err_type, str) and err_type in _TRANSIENT_GQL_TYPES:
            return True
        msg = err.get("message")
        if isinstance(msg, str) and any(
            pat in msg.lower() for pat in _TRANSIENT_ERR_PATTERNS
        ):
            return True
    return False


class GitHubGraphQL:
    """Read-only GraphQL client over `gh api graphql` with bounded retries."""

    def __init__(
        self,
        owner: str,
        repo: str,
        *,
        sleep_fn: Callable[[float], None] = time.sleep,
    ) -> None:
        self.owner = owner
        self.repo = repo
        self._slug_lower = f"{owner}/{repo}".lower()
        self._sleep = sleep_fn

    def query(
        self,
        query: str,
        variables: Mapping[str, object],
        *,
        allowed_not_found_aliases: frozenset[str] = frozenset(),
    ) -> dict[str, object]:
        payload = json.dumps({"query": query, "variables": dict(variables)})
        attempts = len(RETRY_BACKOFF_SECONDS) + 1
        last_error: RuntimeError | None = None
        for attempt in range(attempts):
            proc = subprocess.run(
                ["gh", "api", "graphql", "--input", "-"],
                input=payload,
                text=True,
                capture_output=True,
                check=False,
            )
            data, retryable, err = self._parse_response(
                proc, allowed_not_found_aliases
            )
            if data is not None:
                return data
            last_error = err
            if retryable and attempt < len(RETRY_BACKOFF_SECONDS):
                self._sleep(RETRY_BACKOFF_SECONDS[attempt])
                continue
            raise last_error
        raise last_error or RuntimeError("GraphQL request failed")

    def _parse_response(
        self,
        proc: subprocess.CompletedProcess[str],
        allowed_not_found_aliases: frozenset[str],
    ) -> tuple[dict[str, object] | None, bool, RuntimeError]:
        raw_out = proc.stdout.strip()
        stderr = proc.stderr.strip()
        if not raw_out:
            err = RuntimeError(
                f"gh api graphql returned empty output (exit {proc.returncode})"
                f": {stderr or 'no stderr'}"
            )
            return None, _is_transient_graphql_failure(stderr, ()), err
        try:
            parsed = json.loads(raw_out)
        except json.JSONDecodeError as exc:
            err = RuntimeError(
                f"gh api graphql returned invalid JSON (exit {proc.returncode})"
                f": {exc}; stderr={stderr}"
            )
            retryable = proc.returncode != 0 or _is_transient_graphql_failure(
                stderr, ()
            )
            return None, retryable, err
        if not isinstance(parsed, dict):
            err = RuntimeError("gh api graphql returned non-object JSON")
            return None, False, err

        raw_errors = parsed.get("errors")
        errors: list[Mapping[str, object]] = []
        if raw_errors is not None:
            if not isinstance(raw_errors, list) or not all(
                isinstance(e, Mapping) for e in raw_errors
            ):
                return None, False, RuntimeError(
                    f"Malformed GraphQL `errors` field: {raw_errors!r}"
                )
            errors = list(raw_errors)

        only_allowed_not_found = bool(errors) and bool(
            allowed_not_found_aliases
        ) and all(
            e.get("type") == "NOT_FOUND"
            and isinstance(e.get("path"), list)
            and len(e["path"]) == 2
            and e["path"][0] == "repository"
            and e["path"][1] in allowed_not_found_aliases
            for e in errors
        )

        top_msg = parsed.get("message")
        err_context = (
            f"{stderr}\n{top_msg}" if isinstance(top_msg, str) else stderr
        )

        if errors and not only_allowed_not_found:
            err = RuntimeError(f"GraphQL errors: {errors}")
            return (
                None,
                _is_transient_graphql_failure(err_context, errors),
                err,
            )

        data = parsed.get("data")
        if proc.returncode != 0 and not (
            only_allowed_not_found and isinstance(data, dict)
        ):
            err = RuntimeError(
                f"gh api graphql exited {proc.returncode}: {stderr or raw_out}"
            )
            return (
                None,
                _is_transient_graphql_failure(err_context, errors),
                err,
            )

        if not isinstance(data, dict):
            err = RuntimeError("GraphQL response missing `data` object")
            return (
                None,
                _is_transient_graphql_failure(err_context, errors),
                err,
            )

        return data, False, RuntimeError("unreachable")

    def _is_same_repo(self, node: Mapping[str, object]) -> bool:
        repo_obj = node.get("repository")
        if not isinstance(repo_obj, Mapping):
            return False
        nwo = repo_obj.get("nameWithOwner")
        return isinstance(nwo, str) and nwo.lower() == self._slug_lower

    def _parse_pr(self, node: Mapping[str, object]) -> PullRequestInfo:
        number = node.get("number")
        title = node.get("title")
        url = node.get("url")
        merged = node.get("merged")
        merged_at = node.get("mergedAt")
        merge_commit = node.get("mergeCommit")
        if (
            not isinstance(number, int)
            or isinstance(number, bool)
            or not isinstance(title, str)
            or not isinstance(url, str)
            or not isinstance(merged, bool)
            or not isinstance(merged_at, str)
            or not _ISO_UTC_RE.match(merged_at)
            or not isinstance(merge_commit, Mapping)
            or not isinstance(merge_commit.get("oid"), str)
        ):
            raise RuntimeError(
                f"Malformed merged PullRequest payload: {node!r}"
            )

        labels_conn = node.get("labels")
        if not isinstance(labels_conn, Mapping):
            raise RuntimeError(f"PR #{number} missing `labels` connection")
        page_info = labels_conn.get("pageInfo")
        if not isinstance(page_info, Mapping):
            raise RuntimeError(f"PR #{number} missing `labels.pageInfo`")
        if page_info.get("hasNextPage"):
            raise RuntimeError(
                f"PR #{number} has more than 50 labels; refusing to risk "
                "missing exclusion labels"
            )
        raw_labels = labels_conn.get("nodes")
        if not isinstance(raw_labels, list):
            raise RuntimeError(f"PR #{number} missing `labels.nodes` list")
        labels: set[str] = set()
        for label_node in raw_labels:
            if not isinstance(label_node, Mapping) or not isinstance(
                label_node.get("name"), str
            ):
                raise RuntimeError(
                    f"PR #{number} has malformed label node: {label_node!r}"
                )
            labels.add(label_node["name"])

        author_obj = node.get("author")
        author_login: str | None = None
        author_type: str | None = None
        if author_obj is not None:
            if not isinstance(author_obj, Mapping):
                raise RuntimeError(f"PR #{number} has malformed `author` field")
            raw_type = author_obj.get("__typename")
            raw_login = author_obj.get("login")
            if not isinstance(raw_type, str) or not isinstance(raw_login, str):
                raise RuntimeError(
                    f"PR #{number} has incomplete `author`: {author_obj!r}"
                )
            author_type = raw_type
            if raw_type == "Bot":
                author_login = (
                    raw_login
                    if raw_login.endswith("[bot]")
                    else f"{raw_login}[bot]"
                )
            else:
                author_login = raw_login

        return PullRequestInfo(
            number=number,
            title=title,
            url=url,
            merge_commit_oid=str(merge_commit["oid"]),
            merged_at=merged_at,
            author_login=author_login,
            author_type=author_type,
            labels=frozenset(labels),
        )

    def fetch_prs_by_number(
        self, expected_oids_by_num: Mapping[int, frozenset[str]]
    ) -> dict[str, PullRequestInfo]:
        """Batch-fetch merged PRs by number, keyed by verified `mergeCommit`."""
        unique_nums = list(expected_oids_by_num.keys())
        result: dict[str, PullRequestInfo] = {}
        for start in range(0, len(unique_nums), PR_BATCH_SIZE):
            batch = unique_nums[start : start + PR_BATCH_SIZE]
            var_defs = ["$owner: String!", "$repo: String!"]
            fields: list[str] = []
            variables: dict[str, object] = {
                "owner": self.owner,
                "repo": self.repo,
            }
            aliases: set[str] = set()
            for idx, num in enumerate(batch):
                alias = f"p{idx}"
                aliases.add(alias)
                var_defs.append(f"$n{idx}: Int!")
                fields.append(
                    f"{alias}: pullRequest(number: $n{idx}) "
                    f"{{ {_PR_SELECTION} }}"
                )
                variables[f"n{idx}"] = num
            query = (
                f"query({', '.join(var_defs)}) {{"
                "  repository(owner: $owner, name: $repo) {"
                f"    {' '.join(fields)}"
                "  }"
                "}"
            )
            data = self.query(
                query, variables, allowed_not_found_aliases=frozenset(aliases)
            )
            repo_obj = data.get("repository")
            if not isinstance(repo_obj, Mapping):
                raise RuntimeError(
                    f"Repository {self.owner}/{self.repo} not found"
                )
            for idx, num in enumerate(batch):
                pr_node = repo_obj.get(f"p{idx}")
                if pr_node is None:
                    continue
                if not isinstance(pr_node, Mapping):
                    raise RuntimeError(
                        f"Unexpected payload for PR #{num}: {pr_node!r}"
                    )
                if not pr_node.get("merged"):
                    continue
                mc = pr_node.get("mergeCommit")
                oid = mc.get("oid") if isinstance(mc, Mapping) else None
                if (
                    not isinstance(oid, str)
                    or oid not in expected_oids_by_num[num]
                ):
                    continue
                result[oid] = self._parse_pr(pr_node)
        return result

    def fetch_prs_by_commit_sha(
        self, commits: Sequence[CommitInfo]
    ) -> dict[str, PullRequestInfo]:
        """Batch-resolve commit SHAs via `associatedPullRequests`."""
        result: dict[str, PullRequestInfo] = {}
        for start in range(0, len(commits), COMMIT_BATCH_SIZE):
            batch = commits[start : start + COMMIT_BATCH_SIZE]
            var_defs = ["$owner: String!", "$repo: String!"]
            fields: list[str] = []
            variables: dict[str, object] = {
                "owner": self.owner,
                "repo": self.repo,
            }
            for idx, commit in enumerate(batch):
                var_defs.append(f"$oid{idx}: GitObjectID!")
                fields.append(
                    f"c{idx}: object(oid: $oid{idx}) {{"
                    "  ... on Commit {"
                    "    associatedPullRequests(first: 10) {"
                    "      pageInfo { hasNextPage }"
                    f"      nodes {{ {_PR_SELECTION} }}"
                    "    }"
                    "  }"
                    "}"
                )
                variables[f"oid{idx}"] = commit.sha
            query = (
                f"query({', '.join(var_defs)}) {{"
                "  repository(owner: $owner, name: $repo) {"
                f"    {' '.join(fields)}"
                "  }"
                "}"
            )
            data = self.query(query, variables)
            repo_obj = data.get("repository")
            if not isinstance(repo_obj, Mapping):
                raise RuntimeError(
                    f"Repository {self.owner}/{self.repo} not found"
                )
            for idx, commit in enumerate(batch):
                obj = repo_obj.get(f"c{idx}")
                if obj is None:
                    continue
                if not isinstance(obj, Mapping):
                    raise RuntimeError(
                        f"Unexpected commit payload for {commit.sha}: {obj!r}"
                    )
                assoc = obj.get("associatedPullRequests")
                if assoc is None:
                    continue
                if not isinstance(assoc, Mapping):
                    raise RuntimeError(
                        f"Malformed associatedPullRequests for {commit.sha}"
                    )
                raw_nodes = assoc.get("nodes")
                if not isinstance(raw_nodes, list):
                    raise RuntimeError(
                        "Malformed associatedPullRequests.nodes for "
                        f"{commit.sha}"
                    )
                matches: list[PullRequestInfo] = []
                for node in raw_nodes:
                    if node is None:
                        continue
                    if not isinstance(node, Mapping):
                        raise RuntimeError(
                            f"Malformed associated PR node for {commit.sha}"
                        )
                    if not self._is_same_repo(node) or not node.get("merged"):
                        continue
                    mc = node.get("mergeCommit")
                    if (
                        isinstance(mc, Mapping)
                        and mc.get("oid") == commit.sha
                    ):
                        matches.append(self._parse_pr(node))
                if matches:
                    hint = extract_trailing_pr_number(commit.subject)
                    chosen = next(
                        (
                            m
                            for m in matches
                            if hint is not None and m.number == hint
                        ),
                        min(matches, key=lambda m: m.number),
                    )
                    result[commit.sha] = chosen
                else:
                    pi = assoc.get("pageInfo")
                    if not isinstance(pi, Mapping):
                        raise RuntimeError(
                            f"Malformed associatedPullRequests.pageInfo for "
                            f"{commit.sha}"
                        )
                    if pi.get("hasNextPage"):
                        raise RuntimeError(
                            f"Commit {commit.sha} has >10 associated PRs and "
                            "none matched `mergeCommit.oid` on page 1"
                        )
        return result

    def count_prior_merged_prs(
        self, author_earliest_merged_at: Mapping[str, str]
    ) -> dict[str, int]:
        """Batch-count merged PRs by each author strictly before `merged_at`."""
        items = list(author_earliest_merged_at.items())
        counts: dict[str, int] = {}
        for start in range(0, len(items), SEARCH_BATCH_SIZE):
            batch = items[start : start + SEARCH_BATCH_SIZE]
            var_defs: list[str] = []
            fields: list[str] = []
            variables: dict[str, object] = {}
            for idx, (login, merged_at) in enumerate(batch):
                if not _GITHUB_LOGIN_RE.match(login):
                    raise RuntimeError(
                        f"Unsafe GitHub login for search: {login!r}"
                    )
                if not _ISO_UTC_RE.match(merged_at):
                    raise RuntimeError(
                        f"Unexpected mergedAt timestamp for search: "
                        f"{merged_at!r}"
                    )
                var_defs.append(f"$q{idx}: String!")
                fields.append(
                    f"s{idx}: search(query: $q{idx}, type: ISSUE, first: 1) "
                    "{ issueCount }"
                )
                variables[f"q{idx}"] = (
                    f"repo:{self.owner}/{self.repo} is:pr is:merged "
                    f"author:{login} merged:<{merged_at}"
                )
            query = f"query({', '.join(var_defs)}) {{ {' '.join(fields)} }}"
            data = self.query(query, variables)
            for idx, (login, _merged_at) in enumerate(batch):
                search_obj = data.get(f"s{idx}")
                if not isinstance(search_obj, Mapping):
                    raise RuntimeError(
                        f"Malformed search result for author {login!r}"
                    )
                count = search_obj.get("issueCount")
                if not isinstance(count, int) or isinstance(count, bool):
                    raise RuntimeError(
                        f"Malformed issueCount for author {login!r}: {count!r}"
                    )
                counts[login] = count
        return counts


def _single_line(text: str) -> str:
    return " ".join(text.splitlines()).strip()


def _is_excluded_pr(pr: PullRequestInfo) -> bool:
    if pr.labels & EXCLUDED_LABELS:
        return True
    if (
        pr.author_login is not None
        and pr.author_login.lower() in EXCLUDED_AUTHORS_LOWER
    ):
        return True
    return False


def build_changelog_entries(
    commits: Sequence[CommitInfo], client: GitHubGraphQL
) -> tuple[ChangelogEntry, ...]:
    """Resolve commits to filtered changelog bullets preserving commit order."""
    if not commits:
        return ()

    expected_by_num: dict[int, set[str]] = {}
    for commit in commits:
        num = extract_trailing_pr_number(commit.subject)
        if num is not None:
            expected_by_num.setdefault(num, set()).add(commit.sha)

    resolved: dict[str, PullRequestInfo] = (
        client.fetch_prs_by_number(
            {num: frozenset(oids) for num, oids in expected_by_num.items()}
        )
        if expected_by_num
        else {}
    )
    unresolved = [c for c in commits if c.sha not in resolved]

    if unresolved:
        fallback_prs = client.fetch_prs_by_commit_sha(unresolved)
        resolved.update(fallback_prs)

    entries: list[ChangelogEntry] = []
    for commit in commits:
        pr = resolved.get(commit.sha)
        if pr is not None:
            if _is_excluded_pr(pr):
                continue
            title = _single_line(pr.title)
            if pr.author_login:
                bullet = f"* {title} by @{pr.author_login} in {pr.url}"
            else:
                bullet = f"* {title} in {pr.url}"
            entries.append(
                ChangelogEntry(
                    bullet=bullet,
                    author_login=pr.author_login,
                    author_type=pr.author_type,
                    merged_at=pr.merged_at,
                    pr_url=pr.url,
                )
            )
        else:
            subject = _single_line(commit.subject)
            entries.append(
                ChangelogEntry(bullet=f"* {subject} ({commit.sha[:7]})")
            )
    return tuple(entries)


def find_new_contributors(
    entries: Sequence[ChangelogEntry], client: GitHubGraphQL
) -> tuple[NewContributor, ...]:
    """Identify first-time human PR authors in order of first appearance."""
    # Map lowercase login -> (canonical_login, earliest_merged_at, url).
    candidates: dict[str, tuple[str, str, str]] = {}
    order: list[str] = []
    for entry in entries:
        login = entry.author_login
        if (
            entry.author_type != "User"
            or not login
            or entry.merged_at is None
            or entry.pr_url is None
        ):
            continue
        lower = login.lower()
        if (
            lower in EXCLUDED_AUTHORS_LOWER
            or lower in NEW_CONTRIBUTOR_EXCLUDED_USERS_LOWER
            or not _GITHUB_LOGIN_RE.match(login)
        ):
            continue
        existing = candidates.get(lower)
        if existing is None:
            candidates[lower] = (login, entry.merged_at, entry.pr_url)
            order.append(lower)
        elif entry.merged_at < existing[1]:
            candidates[lower] = (existing[0], entry.merged_at, entry.pr_url)

    if not candidates:
        return ()

    query_map = {
        candidates[lower][0]: candidates[lower][1] for lower in order
    }
    prior_counts = client.count_prior_merged_prs(query_map)
    new_contributors: list[NewContributor] = []
    for lower in order:
        login, _merged_at, pr_url = candidates[lower]
        if prior_counts.get(login) == 0:
            new_contributors.append(NewContributor(login=login, pr_url=pr_url))
    return tuple(new_contributors)


def render_release_notes(
    *,
    owner: str,
    repo: str,
    tag: str,
    prev_tag: str | None,
    entries: Sequence[ChangelogEntry],
    new_contributors: Sequence[NewContributor],
) -> str:
    """Render GitHub-compatible Markdown release notes."""
    sections: list[str] = []
    if entries:
        lines = ["## What's Changed", *(e.bullet for e in entries)]
        sections.append("\n".join(lines))
    elif prev_tag is None:
        sections.append("Initial release.")

    if new_contributors:
        lines = [
            "## New Contributors",
            *(
                f"* @{c.login} made their first contribution in {c.pr_url}"
                for c in new_contributors
            ),
        ]
        sections.append("\n".join(lines))

    if prev_tag is not None:
        changelog_url = (
            f"https://github.com/{owner}/{repo}/compare/{prev_tag}...{tag}"
        )
    else:
        changelog_url = f"https://github.com/{owner}/{repo}/commits/{tag}"
    sections.append(f"**Full Changelog**: {changelog_url}")

    return "\n\n".join(sections) + "\n"


def generate_release_notes(
    *,
    tag: str,
    paths: Sequence[str],
    target: str | None = None,
    previous_tag: str | None = None,
    repo: str | None = None,
    repo_root: Path | None = None,
    client_factory: Callable[[str, str], GitHubGraphQL] = GitHubGraphQL,
) -> str:
    """End-to-end release-notes generation pipeline."""
    prefix, new_semver = parse_tag(tag)
    norm_paths = normalize_paths(paths)
    root = repo_root if repo_root is not None else find_repo_root()
    target_sha = resolve_target_sha(root, tag, target)
    ensure_not_shallow(root, target_sha)
    validate_paths_exist(root, target_sha, norm_paths)
    owner, repo_name = resolve_repo_slug(root, repo)

    prev_result = find_previous_tag(
        root, target_sha, prefix, new_semver, explicit_previous_tag=previous_tag
    )
    prev_tag = prev_result[0] if prev_result is not None else None
    prev_sha = prev_result[1] if prev_result is not None else None

    commits = list_scoped_commits(root, target_sha, prev_sha, norm_paths)
    if commits:
        client = client_factory(owner, repo_name)
        entries = build_changelog_entries(commits, client)
        new_contributors = find_new_contributors(entries, client)
    else:
        entries = ()
        new_contributors = ()

    return render_release_notes(
        owner=owner,
        repo=repo_name,
        tag=tag,
        prev_tag=prev_tag,
        entries=entries,
        new_contributors=new_contributors,
    )


def _build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Generate path-scoped GitHub release notes in Markdown and write "
            "them to stdout."
        )
    )
    parser.add_argument(
        "--tag",
        required=True,
        help="Release tag (e.g. v0.8.64 or anneal-v0.1.0-alpha.24).",
    )
    parser.add_argument(
        "--path",
        dest="paths",
        action="append",
        required=True,
        help="Repo-root-relative path to scope commits to (repeatable).",
    )
    parser.add_argument(
        "--target",
        default=None,
        help=(
            "Target git ref/commit (default: refs/tags/<tag> if present, "
            "otherwise HEAD)."
        ),
    )
    parser.add_argument(
        "--previous-tag",
        default=None,
        help="Override auto-discovered baseline tag.",
    )
    parser.add_argument(
        "--repo",
        default=None,
        help="GitHub OWNER/REPO (default: GITHUB_REPOSITORY or origin remote).",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_arg_parser()
    args = parser.parse_args(argv)
    try:
        notes = generate_release_notes(
            tag=args.tag,
            paths=args.paths,
            target=args.target,
            previous_tag=args.previous_tag,
            repo=args.repo,
        )
    except (ValueError, RuntimeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    sys.stdout.write(notes)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
