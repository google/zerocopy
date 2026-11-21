# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for the shared workflow release-notes generator."""

from __future__ import annotations

import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

WORKFLOW_DIR = Path(__file__).resolve().parents[1] / ".github"
sys.path.insert(0, str(WORKFLOW_DIR))
import release_notes as rn


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        text=True,
        capture_output=True,
        check=True,
    )
    return proc.stdout.strip()


def _init_repo(repo: Path) -> None:
    _git(repo, "init", "-b", "main")
    _git(repo, "config", "user.name", "Test Author")
    _git(repo, "config", "user.email", "test@example.com")
    _git(
        repo,
        "remote",
        "add",
        "origin",
        "https://github.com/google/zerocopy.git",
    )


def _commit_file(repo: Path, rel_path: str, content: str, message: str) -> str:
    full = repo / rel_path
    full.parent.mkdir(parents=True, exist_ok=True)
    full.write_text(content, encoding="utf-8")
    _git(repo, "add", rel_path)
    _git(repo, "commit", "-m", message)
    return _git(repo, "rev-parse", "HEAD")


def _pr_node(
    number: int,
    oid: str,
    *,
    title: str = "Fix something",
    repo_nwo: str = "google/zerocopy",
    merged: bool = True,
    merged_at: str = "2026-04-01T12:00:00Z",
    author: dict[str, object] | None = None,
    labels: list[str] | None = None,
    labels_has_next_page: bool = False,
) -> dict[str, object]:
    if author is None:
        author_obj: dict[str, object] | None = {
            "__typename": "User",
            "login": "alice",
        }
    else:
        author_obj = author
    return {
        "number": number,
        "title": title,
        "url": f"https://github.com/{repo_nwo}/pull/{number}",
        "merged": merged,
        "mergedAt": merged_at,
        "mergeCommit": {"oid": oid},
        "repository": {"nameWithOwner": repo_nwo},
        "author": author_obj,
        "labels": {
            "pageInfo": {"hasNextPage": labels_has_next_page},
            "nodes": [{"name": lbl} for lbl in (labels or [])],
        },
    }


def _completed(
    stdout: str = "", stderr: str = "", returncode: int = 0
) -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(
        args=["gh", "api", "graphql", "--input", "-"],
        returncode=returncode,
        stdout=stdout,
        stderr=stderr,
    )


class TestTagAndSemVer(unittest.TestCase):
    def test_valid_tags(self) -> None:
        cases = [
            ("v0.8.64", "v", rn.SemVer(0, 8, 64)),
            ("0.2.189", "", rn.SemVer(0, 2, 189)),
            (
                "anneal-v0.1.0-alpha.24",
                "anneal-v",
                rn.SemVer(0, 1, 0, ("alpha", "24")),
            ),
            (
                "derive-v0.7.0-alpha.1",
                "derive-v",
                rn.SemVer(0, 7, 0, ("alpha", "1")),
            ),
            ("unsafe-fields-v0.2.1", "unsafe-fields-v", rn.SemVer(0, 2, 1)),
            ("crate2-v1.0.0", "crate2-v", rn.SemVer(1, 0, 0)),
            ("crates/foo/v1.2.3", "crates/foo/v", rn.SemVer(1, 2, 3)),
            ("crates/foo-1.2.3", "crates/foo-", rn.SemVer(1, 2, 3)),
            (
                "foo_bar-v0.0.1-0.a-b",
                "foo_bar-v",
                rn.SemVer(0, 0, 1, ("0", "a-b")),
            ),
            (
                "v1.0.0-rc.1+build.42",
                "v",
                rn.SemVer(1, 0, 0, ("rc", "1"), "build.42"),
            ),
        ]
        for raw, expected_prefix, expected_ver in cases:
            with self.subTest(tag=raw):
                prefix, ver = rn.parse_tag(raw)
                self.assertEqual(prefix, expected_prefix)
                self.assertEqual(ver, expected_ver)

    def test_invalid_tags(self) -> None:
        invalid = [
            "",
            "vv0.8.64",
            "crate1.0.0",
            "v01.2.3",
            "v1.02.3",
            "v1.2.03",
            "anneal-v0.1.0-01",
            "foo.bar-v1.0.0",
            "-v1.0.0",
            "/v1.0.0",
            "foo//v1.0.0",
            "foo--v1.0.0",
            "v1.2",
            "v1.2.3-",
            "v1.2.3+",
            "v1.2.3\n",
            "gherrit/G1234/v1",
        ]
        for raw in invalid:
            with self.subTest(tag=raw):
                with self.assertRaises(ValueError):
                    rn.parse_tag(raw)

    def test_semver_precedence_section_11(self) -> None:
        ordered = [
            "v1.0.0-alpha",
            "v1.0.0-alpha.1",
            "v1.0.0-alpha.beta",
            "v1.0.0-beta",
            "v1.0.0-beta.2",
            "v1.0.0-beta.11",
            "v1.0.0-rc.1",
            "v1.0.0",
            "v1.0.1",
        ]
        versions = [rn.parse_tag(t)[1] for t in ordered]
        for i, vi in enumerate(versions):
            for j, vj in enumerate(versions):
                self.assertEqual(
                    vi.precedence_lt(vj),
                    i < j,
                    f"compare {ordered[i]} vs {ordered[j]}",
                )

    def test_semver_build_metadata_ignored_in_precedence(self) -> None:
        _, v1 = rn.parse_tag("v1.0.0+build.1")
        _, v2 = rn.parse_tag("v1.0.0+build.2")
        self.assertFalse(v1.precedence_lt(v2))
        self.assertFalse(v2.precedence_lt(v1))


class TestValidationHelpers(unittest.TestCase):
    def test_normalize_paths(self) -> None:
        self.assertEqual(
            rn.normalize_paths(["zerocopy/", "anneal/v1/", "zerocopy"]),
            ("zerocopy", "anneal/v1"),
        )
        for bad in [
            [],
            [""],
            ["/zerocopy"],
            [":zerocopy"],
            ["zerocopy\\src"],
            ["."],
            [".."],
            ["./zerocopy"],
            ["zerocopy/../anneal"],
            ["zerocopy//src"],
            ["zerocopy\n"],
        ]:
            with self.subTest(bad=bad):
                with self.assertRaises(ValueError):
                    rn.normalize_paths(bad)

    def test_repo_slug_and_remote_urls(self) -> None:
        urls = [
            "https://github.com/google/zerocopy.git",
            "https://github.com/google/zerocopy",
            "https://github.com/google/zerocopy/",
            "https://x-access-token:tok@github.com/google/zerocopy.git",
            "git@github.com:google/zerocopy.git",
            "ssh://git@github.com/google/zerocopy.git",
        ]
        for url in urls:
            with self.subTest(url=url):
                self.assertEqual(
                    rn.parse_github_remote_url(url), ("google", "zerocopy")
                )
        self.assertEqual(
            rn.parse_github_remote_url("https://github.com/a/foo.bar.git"),
            ("a", "foo.bar"),
        )
        for bad_slug in ["google/zerocopy\n", "onlyone", "../zerocopy", "a/.."]:
            with self.subTest(bad_slug=bad_slug):
                with self.assertRaises(ValueError):
                    rn.validate_repo_slug(bad_slug)
        with self.assertRaises(ValueError):
            rn.parse_github_remote_url(
                "https://example.com/google/zerocopy.git"
            )

    def test_ref_and_tag_validation(self) -> None:
        self.assertEqual(
            rn.validate_git_ref_arg("HEAD~1", flag_name="--target"), "HEAD~1"
        )
        for bad_ref in ["", "-foo", "--all", "a..b", "a b", "a\nb"]:
            with self.assertRaises(ValueError):
                rn.validate_git_ref_arg(bad_ref, flag_name="--target")
        self.assertEqual(
            rn.validate_tag_name(
                "anneal-v0.1.0-alpha.23", flag_name="--previous-tag"
            ),
            "anneal-v0.1.0-alpha.23",
        )
        for bad_tag in ["", "-v1.0.0", "v1..2", "a//b", "a/", "v1.0.0?x=1"]:
            with self.assertRaises(ValueError):
                rn.validate_tag_name(bad_tag, flag_name="--previous-tag")

    def test_extract_trailing_pr_number(self) -> None:
        self.assertEqual(rn.extract_trailing_pr_number("Fix bug (#123)"), 123)
        self.assertEqual(
            rn.extract_trailing_pr_number("Backport (#123) (#456)  "), 456
        )
        self.assertIsNone(rn.extract_trailing_pr_number('Revert "Fix (#123)"'))
        self.assertIsNone(rn.extract_trailing_pr_number("Zero (#0)"))
        self.assertEqual(
            rn.extract_trailing_pr_number("Max (#2147483647)"), 2147483647
        )
        self.assertIsNone(
            rn.extract_trailing_pr_number("Overflow (#2147483648)")
        )


class TestGitHistoryAndTagDiscovery(unittest.TestCase):
    def test_multi_crate_tags_and_prerelease_rules(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td) / "repo"
            repo.mkdir()
            _init_repo(repo)

            c1 = _commit_file(repo, "zerocopy/lib.rs", "1\n", "Initial zc (#1)")
            _git(repo, "tag", "-a", "v0.8.62", "-m", "Release v0.8.62")

            _commit_file(repo, "anneal/v1/lib.rs", "1\n", "Initial anneal (#2)")
            _git(repo, "tag", "anneal-v0.1.0-alpha.22")

            c3 = _commit_file(
                repo, "zerocopy/lib.rs", "2\n", "Prerelease zc (#3)"
            )
            _git(repo, "tag", "v0.8.63-alpha.1")

            _commit_file(repo, "anneal/v1/lib.rs", "2\n", "Anneal update (#4)")
            _git(
                repo,
                "tag",
                "-a",
                "anneal-v0.1.0-alpha.23",
                "-m",
                "Release anneal-v0.1.0-alpha.23",
            )
            _git(
                repo,
                "tag",
                "anneal-toolchains-v0.1.0-alpha.24-999-abcdef012345",
            )
            _git(repo, "tag", "gherrit/G123456/v1")

            c5 = _commit_file(repo, "zerocopy/lib.rs", "3\n", "Stable zc (#5)")
            # A colliding branch name must not cause `for-each-ref` to skip the
            # `v0.8.62` tag (`%(refname:lstrip=2)` vs `%(refname:short)`).
            _git(repo, "branch", "v0.8.62", c5)

            # Stable v0.8.63 skips v0.8.63-alpha.1 and anneal tags -> v0.8.62.
            _, sv_stable = rn.parse_tag("v0.8.63")
            self.assertEqual(
                rn.find_previous_tag(repo, c5, "v", sv_stable), ("v0.8.62", c1)
            )

            # Prerelease v0.8.63-alpha.2 sees v0.8.63-alpha.1.
            _, sv_pre2 = rn.parse_tag("v0.8.63-alpha.2")
            self.assertEqual(
                rn.find_previous_tag(repo, c5, "v", sv_pre2),
                ("v0.8.63-alpha.1", c3),
            )

            # Prerelease v0.8.63-alpha.1 skips itself -> v0.8.62.
            _, sv_pre1 = rn.parse_tag("v0.8.63-alpha.1")
            self.assertEqual(
                rn.find_previous_tag(repo, c3, "v", sv_pre1), ("v0.8.62", c1)
            )

            # Anneal alpha.24 skips toolchains and zerocopy tags -> alpha.23.
            _, sv_an = rn.parse_tag("anneal-v0.1.0-alpha.24")
            prev_an = rn.find_previous_tag(repo, c5, "anneal-v", sv_an)
            if prev_an is None:
                self.fail("Expected previous tag anneal-v0.1.0-alpha.23")
            self.assertEqual(prev_an[0], "anneal-v0.1.0-alpha.23")

            # Unreleased crate prefix -> None (initial release).
            _, sv_exo = rn.parse_tag("exocrate-v0.1.0")
            self.assertIsNone(
                rn.find_previous_tag(repo, c5, "exocrate-v", sv_exo)
            )

    def test_same_commit_multiple_tags_and_target_resolution(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td) / "repo"
            repo.mkdir()
            _init_repo(repo)

            c1 = _commit_file(repo, "zerocopy/a.rs", "1\n", "First (#1)")
            _git(repo, "tag", "v0.8.61")
            c2 = _commit_file(repo, "zerocopy/a.rs", "2\n", "Second (#2)")
            _git(repo, "tag", "v0.8.62")
            _git(repo, "tag", "v0.8.63")
            c3 = _commit_file(repo, "zerocopy/a.rs", "3\n", "Third (#3)")

            # Releasing v0.8.64 at c3 picks highest tag on c2 (v0.8.63).
            _, sv64 = rn.parse_tag("v0.8.64")
            self.assertEqual(
                rn.find_previous_tag(repo, c3, "v", sv64), ("v0.8.63", c2)
            )
            # Releasing v0.8.63 defaults target to refs/tags/v0.8.63 (c2) and
            # picks v0.8.62 on the same commit (strictly < v0.8.63).
            self.assertEqual(rn.resolve_target_sha(repo, "v0.8.63", None), c2)
            _, sv63 = rn.parse_tag("v0.8.63")
            self.assertEqual(
                rn.find_previous_tag(repo, c2, "v", sv63), ("v0.8.62", c2)
            )
            # Untagged v0.8.64 defaults target to HEAD (c3).
            self.assertEqual(rn.resolve_target_sha(repo, "v0.8.64", None), c3)
            # Explicit --previous-tag override.
            self.assertEqual(
                rn.find_previous_tag(
                    repo, c3, "v", sv64, explicit_previous_tag="v0.8.61"
                ),
                ("v0.8.61", c1),
            )
            with self.assertRaises(RuntimeError):
                rn.find_previous_tag(
                    repo, c3, "v", sv64, explicit_previous_tag="v9.9.9"
                )

    def test_path_scoping_merges_renames_empty_and_subdir_cwd(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td) / "repo"
            repo.mkdir()
            _init_repo(repo)

            _commit_file(repo, "zerocopy/a.rs", "1\n", "init zc")
            _commit_file(repo, "anneal/b.rs", "1\n", "init anneal")
            _commit_file(repo, "other/c.rs", "1\n", "init other")
            _git(repo, "tag", "v0.1.0")

            # 1. Unrelated crate commit -> excluded.
            _commit_file(repo, "anneal/b.rs", "2\n", "anneal change (#10)")
            # 2. Root chore -> excluded.
            _commit_file(repo, "README.md", "hi\n", "root chore (#11)")
            # 3. Empty commit -> excluded.
            _git(repo, "commit", "--allow-empty", "-m", "empty commit (#12)")
            # 4. Direct zerocopy commit -> included.
            zc1 = _commit_file(repo, "zerocopy/a.rs", "2\n", "zc fix (#13)")
            # 5. --no-ff merge touching zerocopy -> included.
            _git(repo, "checkout", "-b", "feat-zc")
            _commit_file(repo, "zerocopy/a.rs", "3\n", "branch zc commit")
            _git(repo, "checkout", "main")
            _commit_file(repo, "anneal/b.rs", "3\n", "main anneal (#14)")
            _git(repo, "merge", "--no-ff", "feat-zc", "-m", "Merge zc (#15)")
            zc_merge = _git(repo, "rev-parse", "HEAD")
            # 6. --no-ff merge touching only anneal -> excluded.
            _git(repo, "checkout", "-b", "feat-an")
            _commit_file(repo, "anneal/b.rs", "4\n", "branch anneal commit")
            _git(repo, "checkout", "main")
            _git(repo, "merge", "--no-ff", "feat-an", "-m", "Merge an (#16)")
            # 7. Cross-boundary rename into zerocopy -> included.
            _git(repo, "mv", "other/c.rs", "zerocopy/c.rs")
            _git(repo, "commit", "-m", "Move file into zerocopy (#17)")
            zc_mv = _git(repo, "rev-parse", "HEAD")

            prev_sha = _git(repo, "rev-parse", "v0.1.0")
            head_sha = _git(repo, "rev-parse", "HEAD")
            commits = rn.list_scoped_commits(
                repo, head_sha, prev_sha, ("zerocopy",)
            )
            self.assertEqual([c.sha for c in commits], [zc1, zc_merge, zc_mv])

            # Multi-path union includes both zerocopy and README.md commits.
            multi = rn.list_scoped_commits(
                repo, head_sha, prev_sha, ("zerocopy", "README.md")
            )
            self.assertEqual(len(multi), 4)

            # Running find_repo_root from a nested subdirectory resolves root.
            self.assertEqual(
                rn.find_repo_root(repo / "zerocopy").resolve(), repo.resolve()
            )

            # Missing path at target fails closed.
            with self.assertRaises(RuntimeError):
                rn.validate_paths_exist(repo, head_sha, ("does-not-exist",))

    def test_shallow_clone_fails_closed_and_unrelated_graft(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            origin = Path(td) / "origin"
            shallow = Path(td) / "shallow"
            origin.mkdir()
            _init_repo(origin)
            _commit_file(origin, "zerocopy/a.rs", "1\n", "c1")
            _commit_file(origin, "zerocopy/a.rs", "2\n", "c2")
            subprocess.run(
                [
                    "git",
                    "clone",
                    "--depth",
                    "1",
                    f"file://{origin}",
                    str(shallow),
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            shallow_head = _git(shallow, "rev-parse", "HEAD")
            with self.assertRaisesRegex(RuntimeError, "Shallow git repository"):
                rn.ensure_not_shallow(shallow, shallow_head)

            # Unrelated orphan shallow graft outside target ancestry succeeds.
            orphan_repo = Path(td) / "orphan"
            orphan_repo.mkdir()
            _init_repo(orphan_repo)
            _commit_file(orphan_repo, "zerocopy/a.rs", "1\n", "main c1")
            main_head = _git(orphan_repo, "rev-parse", "HEAD")
            _git(orphan_repo, "checkout", "--orphan", "unrelated")
            _git(orphan_repo, "rm", "-rf", ".")
            orphan_sha = _commit_file(orphan_repo, "x.txt", "x\n", "orphan c1")
            _git(orphan_repo, "checkout", "main")
            (orphan_repo / ".git" / "shallow").write_text(
                f"{orphan_sha}\n", encoding="utf-8"
            )
            self.assertEqual(
                _git(orphan_repo, "rev-parse", "--is-shallow-repository"),
                "true",
            )
            rn.ensure_not_shallow(orphan_repo, main_head)
            with self.assertRaisesRegex(RuntimeError, "Shallow git repository"):
                rn.ensure_not_shallow(orphan_repo, orphan_sha)

    def test_zero_commits_makes_no_graphql_calls(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td) / "repo"
            repo.mkdir()
            _init_repo(repo)
            _commit_file(repo, "zerocopy/a.rs", "1\n", "init")
            _git(repo, "tag", "v0.8.62")
            _commit_file(repo, "anneal/b.rs", "1\n", "only anneal (#99)")

            called = False

            def _fail_factory(owner: str, name: str) -> rn.GitHubGraphQL:
                nonlocal called
                called = True
                raise AssertionError("GraphQL client should not be constructed")

            with mock.patch.dict(
                os.environ, {"GITHUB_REPOSITORY": ""}, clear=False
            ):
                notes = rn.generate_release_notes(
                    tag="v0.8.63",
                    paths=("zerocopy",),
                    repo_root=repo,
                    client_factory=_fail_factory,
                )
            self.assertFalse(called)
            expected_url = (
                "https://github.com/google/zerocopy/compare/v0.8.62...v0.8.63"
            )
            self.assertEqual(notes, f"**Full Changelog**: {expected_url}\n")


class TestGraphQLAndRendering(unittest.TestCase):
    def test_pass_4a_4b_exclusions_bots_and_new_contributors(self) -> None:
        s1 = "1" * 40  # Normal PR via Pass 4a (new contributor alice)
        s2 = "2" * 40  # Labeled hide-from-release-notes -> excluded
        s3 = "3" * 40  # dependabot (Bot) -> excluded
        s4 = "4" * 40  # google-pr-creation-bot (User) -> included, not NC
        s5 = "5" * 40  # Mismatched #99 (>50 labels) -> Pass 4b finds #205
        s6 = "6" * 40  # Deleted author + NOT_FOUND on #404 -> Pass 4b
        s7 = "7" * 40  # Direct commit (no PR)
        s8 = "8" * 40  # Earlier PR by alice (same release, tests earliest)
        s9 = "9" * 40  # Existing contributor bob (prior count = 3)

        commits = (
            rn.CommitInfo(s1, "Feature A (#201)"),
            rn.CommitInfo(s2, "Release 0.8.64 (#202)"),
            rn.CommitInfo(s3, "Bump foo (#203)"),
            rn.CommitInfo(s4, "Backport fix (#204)"),
            rn.CommitInfo(s5, "Backport old fix (#99)"),
            rn.CommitInfo(s6, "Mystery fix (#404)"),
            rn.CommitInfo(s7, "Direct commit without PR"),
            rn.CommitInfo(s8, "Earlier alice fix (#208)"),
            rn.CommitInfo(s9, "Bob fix (#209)"),
        )

        responses = [
            # Pass 4a: pullRequest(number: ...) with scoped NOT_FOUND on p5.
            _completed(
                stdout=json.dumps(
                    {
                        "data": {
                            "repository": {
                                "p0": _pr_node(
                                    201,
                                    s1,
                                    title="Feature A",
                                    merged_at="2026-04-02T10:00:00Z",
                                    author={
                                        "__typename": "User",
                                        "login": "alice",
                                    },
                                ),
                                "p1": _pr_node(
                                    202,
                                    s2,
                                    title="Release 0.8.64",
                                    labels=["hide-from-release-notes"],
                                ),
                                "p2": _pr_node(
                                    203,
                                    s3,
                                    title="Bump foo",
                                    author={
                                        "__typename": "Bot",
                                        "login": "dependabot",
                                    },
                                ),
                                "p3": _pr_node(
                                    204,
                                    s4,
                                    title="Backport fix",
                                    author={
                                        "__typename": "User",
                                        "login": "google-pr-creation-bot",
                                    },
                                ),
                                # PR #99 belongs to another commit and has >50
                                # labels; oid check must skip it BEFORE
                                # label-truncation validation.
                                "p4": _pr_node(
                                    99,
                                    "f" * 40,
                                    title="Old PR",
                                    labels_has_next_page=True,
                                ),
                                "p5": None,
                                "p6": _pr_node(
                                    208,
                                    s8,
                                    title="Earlier alice fix",
                                    merged_at="2026-04-01T08:00:00Z",
                                    author={
                                        "__typename": "User",
                                        "login": "alice",
                                    },
                                ),
                                "p7": _pr_node(
                                    209,
                                    s9,
                                    title="Bob fix",
                                    merged_at="2026-04-03T09:00:00Z",
                                    author={
                                        "__typename": "User",
                                        "login": "bob",
                                    },
                                ),
                            }
                        },
                        "errors": [
                            {"type": "NOT_FOUND", "path": ["repository", "p5"]}
                        ],
                    }
                ),
                returncode=1,
            ),
            # Pass 4b: object(oid: ...) for unresolved commits [s5, s6, s7].
            _completed(
                stdout=json.dumps(
                    {
                        "data": {
                            "repository": {
                                "c0": {
                                    "associatedPullRequests": {
                                        "pageInfo": {"hasNextPage": False},
                                        "nodes": [
                                            # Fork PR with same oid is ignored.
                                            _pr_node(
                                                999,
                                                s5,
                                                repo_nwo="fork/zerocopy",
                                                title="Fork PR",
                                            ),
                                            _pr_node(
                                                205,
                                                s5,
                                                title="Backport old fix",
                                                author={
                                                    "__typename": "Bot",
                                                    "login": "helper-bot",
                                                },
                                            ),
                                        ],
                                    }
                                },
                                "c1": {
                                    "associatedPullRequests": {
                                        "pageInfo": {"hasNextPage": False},
                                        "nodes": [
                                            {
                                                **_pr_node(
                                                    206,
                                                    s6,
                                                    title="Mystery\nfix",
                                                ),
                                                "author": None,
                                            }
                                        ],
                                    }
                                },
                                "c2": {
                                    "associatedPullRequests": {
                                        "pageInfo": {"hasNextPage": False},
                                        "nodes": [],
                                    }
                                },
                            }
                        }
                    }
                )
            ),
            # Pass 5: New Contributors search for [alice, bob].
            _completed(
                stdout=json.dumps(
                    {
                        "data": {
                            "s0": {"issueCount": 0},
                            "s1": {"issueCount": 3},
                        }
                    }
                )
            ),
        ]

        captured_inputs: list[dict[str, object]] = []

        def _fake_run(_cmd, **kwargs):
            captured_inputs.append(json.loads(kwargs["input"]))
            return responses.pop(0)

        client = rn.GitHubGraphQL("google", "zerocopy", sleep_fn=lambda _: None)
        with mock.patch.object(subprocess, "run", side_effect=_fake_run):
            entries = rn.build_changelog_entries(commits, client)
            new_contribs = rn.find_new_contributors(entries, client)

        self.assertEqual(len(responses), 0)
        # Verify search used alice's earlier mergedAt (#208) and skipped bots.
        search_vars = captured_inputs[2]["variables"]
        self.assertEqual(
            search_vars,
            {
                "q0": (
                    "repo:google/zerocopy is:pr is:merged "
                    "author:alice merged:<2026-04-01T08:00:00Z"
                ),
                "q1": (
                    "repo:google/zerocopy is:pr is:merged "
                    "author:bob merged:<2026-04-03T09:00:00Z"
                ),
            },
        )
        notes = rn.render_release_notes(
            owner="google",
            repo="zerocopy",
            tag="v0.8.64",
            prev_tag="v0.8.63",
            entries=entries,
            new_contributors=new_contribs,
        )
        base = "https://github.com/google/zerocopy"
        expected = "\n".join(
            [
                "## What's Changed",
                f"* Feature A by @alice in {base}/pull/201",
                f"* Backport fix by @google-pr-creation-bot in {base}/pull/204",
                f"* Backport old fix by @helper-bot[bot] in {base}/pull/205",
                f"* Mystery fix in {base}/pull/206",
                f"* Direct commit without PR ({s7[:7]})",
                f"* Earlier alice fix by @alice in {base}/pull/208",
                f"* Bob fix by @bob in {base}/pull/209",
                "",
                "## New Contributors",
                f"* @alice made their first contribution in {base}/pull/208",
                "",
                f"**Full Changelog**: {base}/compare/v0.8.63...v0.8.64",
                "",
            ]
        )
        self.assertEqual(notes, expected)

    def test_repo_level_not_found_fails_closed(self) -> None:
        client = rn.GitHubGraphQL("google", "missing", sleep_fn=lambda _: None)
        resp = _completed(
            stdout=json.dumps(
                {
                    "data": {"repository": None},
                    "errors": [{"type": "NOT_FOUND", "path": ["repository"]}],
                }
            ),
            returncode=1,
        )
        with mock.patch.object(subprocess, "run", return_value=resp):
            with self.assertRaisesRegex(RuntimeError, "GraphQL errors"):
                client.fetch_prs_by_number({1: frozenset({"a" * 40})})

    def test_label_truncation_fails_closed(self) -> None:
        sha = "a" * 40
        client = rn.GitHubGraphQL("google", "zerocopy", sleep_fn=lambda _: None)
        resp = _completed(
            stdout=json.dumps(
                {
                    "data": {
                        "repository": {
                            "p0": _pr_node(10, sha, labels_has_next_page=True)
                        }
                    }
                }
            )
        )
        with mock.patch.object(subprocess, "run", return_value=resp):
            with self.assertRaisesRegex(RuntimeError, "more than 50 labels"):
                client.fetch_prs_by_number({10: frozenset({sha})})

    def test_associated_prs_truncation_fails_closed(self) -> None:
        sha = "b" * 40
        client = rn.GitHubGraphQL("google", "zerocopy", sleep_fn=lambda _: None)
        resp = _completed(
            stdout=json.dumps(
                {
                    "data": {
                        "repository": {
                            "c0": {
                                "associatedPullRequests": {
                                    "pageInfo": {"hasNextPage": True},
                                    "nodes": [],
                                }
                            }
                        }
                    }
                }
            )
        )
        with mock.patch.object(subprocess, "run", return_value=resp):
            with self.assertRaisesRegex(RuntimeError, ">10 associated PRs"):
                client.fetch_prs_by_commit_sha((rn.CommitInfo(sha, "Direct"),))

    def test_transient_retries_exhaustion_and_permanent_fail_fast(self) -> None:
        sleeps: list[float] = []
        client = rn.GitHubGraphQL("google", "zerocopy", sleep_fn=sleeps.append)
        transient_seq = [
            _completed(stdout="", stderr="HTTP 502 Bad Gateway", returncode=1),
            _completed(
                stdout=json.dumps(
                    {"message": "Something went wrong while executing query."}
                ),
                returncode=1,
            ),
            _completed(stdout=json.dumps({"data": {"ok": True}})),
        ]
        with mock.patch.object(subprocess, "run", side_effect=transient_seq):
            data = client.query("query { ok }", {})
        self.assertEqual(data, {"ok": True})
        self.assertEqual(sleeps, [2.0, 5.0])

        # Exhausted transient errors raise RuntimeError after 2 sleeps.
        sleeps.clear()
        always_503 = _completed(
            stdout=json.dumps(
                {"errors": [{"type": "RATE_LIMITED", "message": "slow down"}]}
            ),
            returncode=1,
        )
        with mock.patch.object(subprocess, "run", return_value=always_503):
            with self.assertRaisesRegex(RuntimeError, "RATE_LIMITED"):
                client.query("query { ok }", {})
        self.assertEqual(sleeps, [2.0, 5.0])

        # Permanent error fails immediately without sleeping.
        sleeps.clear()
        perm = _completed(
            stdout=json.dumps(
                {"errors": [{"type": "FORBIDDEN", "message": "denied"}]}
            ),
            returncode=1,
        )
        with mock.patch.object(subprocess, "run", return_value=perm):
            with self.assertRaisesRegex(RuntimeError, "GraphQL errors"):
                client.query("query { ok }", {})
        self.assertEqual(sleeps, [])

    def test_initial_release_empty_and_nonempty_rendering(self) -> None:
        base = "https://github.com/google/zerocopy"
        empty_init = rn.render_release_notes(
            owner="google",
            repo="zerocopy",
            tag="exocrate-v0.1.0",
            prev_tag=None,
            entries=(),
            new_contributors=(),
        )
        self.assertEqual(
            empty_init,
            "Initial release.\n\n"
            f"**Full Changelog**: {base}/commits/exocrate-v0.1.0\n",
        )

        nonempty_init = rn.render_release_notes(
            owner="google",
            repo="zerocopy",
            tag="exocrate-v0.1.0",
            prev_tag=None,
            entries=(rn.ChangelogEntry(bullet="* Add exocrate (abcdef1)"),),
            new_contributors=(),
        )
        self.assertEqual(
            nonempty_init,
            "## What's Changed\n"
            "* Add exocrate (abcdef1)\n\n"
            f"**Full Changelog**: {base}/commits/exocrate-v0.1.0\n",
        )

    def test_resolve_repo_slug_precedence_and_cli_errors(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td) / "repo"
            repo.mkdir()
            _init_repo(repo)
            with mock.patch.dict(
                os.environ,
                {"GITHUB_REPOSITORY": "envowner/envrepo"},
                clear=False,
            ):
                self.assertEqual(
                    rn.resolve_repo_slug(repo, "argowner/argrepo"),
                    ("argowner", "argrepo"),
                )
                self.assertEqual(
                    rn.resolve_repo_slug(repo, None), ("envowner", "envrepo")
                )
            with mock.patch.dict(
                os.environ, {"GITHUB_REPOSITORY": ""}, clear=False
            ):
                self.assertEqual(
                    rn.resolve_repo_slug(repo, None), ("google", "zerocopy")
                )

        # CLI main() returns exit code 1 with diagnostic on stderr for bad tag.
        stderr_buf = io.StringIO()
        with mock.patch.object(rn.sys, "stderr", stderr_buf):
            code = rn.main(["--tag", "bad-tag", "--path", "zerocopy"])
        self.assertEqual(code, 1)
        self.assertIn("error:", stderr_buf.getvalue())


if __name__ == "__main__":
    unittest.main()
