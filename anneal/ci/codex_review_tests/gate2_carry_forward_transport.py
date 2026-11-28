# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`codex_review` tests for Gate 2 carry-forward through the GitHub
transport.
"""

from .support import (
    copy,
    GitHub,
    hashlib,
    patch,
    unittest,
)


class Gate2CarryForwardTransportTests(unittest.TestCase):
    """GitHub.verify_rebase_carry_forward against canned API responses."""

    OLD_HEAD, OLD_BASE, OLD_TREE = "6" * 40, "7" * 40, "0" * 40
    NEW_HEAD, NEW_BASE = "8" * 40, "9" * 40
    PARENT_TREE = "5" * 40
    MANIFEST = "anneal/trusted/root-manifest.sha256"
    BLOB = "4" * 40

    def _commit(self, sha, parent, files, message="msg", tree=None):
        return {"sha": sha, "commit": {"tree": {"sha": tree or self.OLD_TREE},
                                       "message": message},
                "parents": [{"sha": parent}], "files": files}

    @staticmethod
    def _diff(files, modes=None):
        modes = modes or {}
        return "".join(
            f"diff --git a/{f['filename']} b/{f['filename']}\n"
            f"index 1111111..2222222 {modes.get(f['filename'], '100644')}\n"
            f"--- a/{f['filename']}\n" for f in files)

    def _gh(self, old_files, new_files, base_files, *, status="ahead",
            new_message="msg", old_tree=None, new_modes=None, calls=None):
        responses = {
            f"commits/{self.OLD_HEAD}": self._commit(
                self.OLD_HEAD, self.OLD_BASE, old_files, tree=old_tree),
            f"commits/{self.NEW_HEAD}": self._commit(
                self.NEW_HEAD, self.NEW_BASE, new_files, new_message, tree="1" * 40),
            f"compare/{self.OLD_BASE}...{self.NEW_BASE}": {
                "status": status, "files": base_files},
            f"commits/{self.OLD_BASE}": self._commit(
                self.OLD_BASE, "3" * 40, [], tree=self.PARENT_TREE),
        }
        diffs = {
            f"commits/{self.OLD_HEAD}": self._diff(old_files),
            f"commits/{self.NEW_HEAD}": self._diff(new_files, new_modes),
        }
        gh = GitHub("google/zerocopy", "token")

        def request(path, data=None):
            if calls is not None:
                calls.append(path)
            return copy.deepcopy(responses[path])
        gh.request = request
        gh.request_text = lambda path, accept: diffs[path]
        return gh

    def _verify(self, gh, old_tree=None):
        return gh.verify_rebase_carry_forward(
            self.OLD_HEAD, self.OLD_BASE, old_tree or self.OLD_TREE,
            self.NEW_HEAD, self.NEW_BASE)

    def _f(self, name, patch, sha=None):
        return {"filename": name, "status": "modified", "patch": patch,
                "sha": sha or self.BLOB}

    def _manifest(self, ctx_before, removed, added, ctx_after, sha):
        return self._f(self.MANIFEST,
                       f"@@ -1,3 +1,3 @@\n {ctx_before}\n-{removed}\n+{added}\n {ctx_after}",
                       sha)

    def test_clean_rebase_over_unrelated_base(self):
        f = [self._f("anneal/a.rs", "@@ -1 +1 @@\n-a\n+b")]
        calls = []
        ik = self._verify(self._gh(f, f, [{"filename": "zerocopy/src/lib.rs"}], calls=calls))
        msg_sha = hashlib.sha256(b"msg").hexdigest()
        self.assertEqual(ik, f"one:{self.PARENT_TREE}:{self.OLD_TREE}:{msg_sha}")
        # Each commit is read once for metadata and files.
        self.assertEqual(calls.count(f"commits/{self.OLD_HEAD}"), 1)
        self.assertEqual(calls.count(f"commits/{self.NEW_HEAD}"), 1)
        self.assertIsNone(self._verify(self._gh(f, f, [{"filename": "anneal/a.rs"}])))
        self.assertIsNone(self._verify(self._gh(f, f, [{"filename": "x"}], status="diverged")))
        self.assertIsNone(self._verify(self._gh(f, f, [{"filename": "x"}], new_message="msg2")))
        semantic = [self._f("anneal/a.rs", "@@ -1 +1 @@\n-a\n+c")]
        self.assertIsNone(self._verify(self._gh(f, semantic, [{"filename": "x"}])))
        # The anchor's reviewed tree must be the commit's real tree.
        self.assertIsNone(self._verify(self._gh(f, f, [{"filename": "x"}]), old_tree="2" * 40))
        # A mode change with identical content is caught from the raw diff.
        self.assertIsNone(self._verify(self._gh(
            f, f, [{"filename": "x"}], new_modes={"anneal/a.rs": "100755"})))
        self.assertIsNone(self._verify(self._gh(
            f, f, [{"filename": "x"}], new_modes={"anneal/a.rs": "120000"})))

    def test_parent_and_diff_coverage_checks(self):
        f = [self._f("a", "+x"), self._f("b", "+y")]
        gh = self._gh(f, f, [{"filename": "c"}])
        self.assertIsNotNone(self._verify(gh))
        # The anchor must sit directly on the base its review names.
        self.assertIsNone(gh.verify_rebase_carry_forward(
            self.OLD_HEAD, "3" * 40, self.OLD_TREE, self.NEW_HEAD, self.NEW_BASE))
        # Both raw diffs must cover exactly the JSON file list.
        short = self._diff(f[:1])
        gh.request_text = lambda path, accept: short
        self.assertIsNone(self._verify(gh))

    def test_other_heads_with_the_same_patch_block(self):
        f = [self._f("anneal/a.rs", "@@ -1 +1 @@\n-a\n+b")]
        gh = self._gh(f, f, [{"filename": "zerocopy/src/lib.rs"}])
        other = "3" * 40
        responses = {}
        base_request = gh.request

        def request(path, data=None):
            if path in responses:
                return copy.deepcopy(responses[path])
            return base_request(path, data)
        gh.request = request

        def verify(heads):
            return gh.verify_rebase_carry_forward(
                self.OLD_HEAD, self.OLD_BASE, self.OLD_TREE,
                self.NEW_HEAD, self.NEW_BASE, heads)

        # A head whose findings concern the same patch (moved context only).
        same = [self._f("anneal/a.rs", "@@ -7 +7 @@\n-a\n+b", sha="2" * 40)]
        responses[f"commits/{other}"] = self._commit(other, "1" * 40, same)
        self.assertIsNone(verify([other]))
        # A head with a different patch does not block.
        responses[f"commits/{other}"] = self._commit(
            other, "1" * 40, [self._f("anneal/a.rs", "@@ -1 +1 @@\n-a\n+c")])
        self.assertIsNotNone(verify([other]))
        # An unreadable or uncomparable head fails closed.
        responses[f"commits/{other}"] = self._commit(
            other, "1" * 40, [{"filename": "anneal/a.rs", "status": "modified"}])
        self.assertIsNone(verify([other]))
        del responses[f"commits/{other}"]

        def missing(path, data=None):
            if path == f"commits/{other}":
                raise RuntimeError("GitHub GET: HTTP 404")
            return request(path, data)
        gh.request = missing
        self.assertIsNone(verify([other]))

    def test_base_changes_to_review_rules_need_a_new_review(self):
        f = [self._f("anneal/a.rs", "@@ -1 +1 @@\n-a\n+b")]
        for path in ("anneal/AGENTS.md", "anneal/.gemini/styleguide.md",
                     "anneal/skills/trust-review/SKILL.md", "skills/x/SKILL.md",
                     "anneal/docs/codex-review.md", "anneal/ci/codex_review.py",
                     ".github/workflows/ci.yml", "AGENTS.md",
                     "anneal/THREAT_MODEL.md", "anneal/x/AGENTS.override.md",
                     "zerocopy/src/CLAUDE.md", "GEMINI.md"):
            with self.subTest(path):
                self.assertIsNone(self._verify(self._gh(f, f, [{"filename": path}])))
        self.assertIsNone(self._verify(self._gh(
            f, f, [{"filename": "x.md", "previous_filename": "anneal/AGENTS.md"}])))

    def test_same_base_never_carries_forward(self):
        f = [self._f("a", "+x")]
        gh = self._gh(f, f, [{"filename": "b"}])
        self.assertIsNone(gh.verify_rebase_carry_forward(
            self.OLD_HEAD, self.NEW_BASE, self.OLD_TREE, self.NEW_HEAD, self.NEW_BASE))

    def test_manifest_edge_cases(self):
        # The PR changes its own flake.nix digest line; main separately bumps
        # an adjacent Cargo.lock digest line in the same manifest. The PR's
        # own added and removed lines are unchanged, so it qualifies.
        old = [self._manifest("aaa  anneal/Cargo.lock", "f0  flake.nix",
                              "f1  flake.nix", "ccc  anneal/x", "a" * 40)]
        new = [self._manifest("bbb  anneal/Cargo.lock", "f0  flake.nix",
                              "f1  flake.nix", "ccc  anneal/x", "b" * 40)]
        base = [{"filename": self.MANIFEST}, {"filename": "anneal/Cargo.lock"}]
        self.assertIsNotNone(self._verify(self._gh(old, new, base)))
        # Without a base change to the manifest, its blob must still match.
        self.assertIsNone(self._verify(self._gh(old, new, [{"filename": "q"}])))
        # If main also changed flake.nix, the PR's removed digest line
        # differs, so it falls back to a full review.
        moved = [self._manifest("bbb  anneal/Cargo.lock", "f9  flake.nix",
                                "f1  flake.nix", "ccc  anneal/x", "b" * 40)]
        self.assertIsNone(self._verify(self._gh(old, moved, base + [{"filename": "flake.nix"}])))
        # Neither flake.nix nor Cargo.lock is an allowlisted overlap.
        for name in ("flake.nix", "anneal/Cargo.lock"):
            f = [self._f(name, "@@ -1 +1 @@\n-a\n+b")]
            self.assertIsNone(self._verify(self._gh(f, f, [{"filename": name}])))
