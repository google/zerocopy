# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`codex_review` tests for Gate 2 carry-forward decisions."""

from .support import (
    BASE,
    base_drift_allows_carry_forward,
    diff_file_modes,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    GitHub,
    HEAD,
    OTHER_BASE,
    OTHER_HEAD,
    OTHER_TREE,
    patch,
    pull,
    rebase_only_patch_equivalent,
    reconcile,
    review_result,
    summary,
    TREE,
    unittest,
)


class Gate2CarryForwardTests(unittest.TestCase):
    """Evaluator-verified rebase-only carry-forward of a clean Gate 2 review."""

    NEW_HEAD = "1" * 40
    NEW_BASE = "2" * 40
    NEW_TREE = "3" * 40
    BLOB = "9" * 40

    def _file(self, name, patch, status="modified", previous=None, sha=None):
        entry = {"filename": name, "status": status, "patch": patch,
                 "sha": self.BLOB if sha is None else sha}
        if previous is not None:
            entry["previous_filename"] = previous
        return entry

    def _ik(self):
        return f"one:{'4' * 40}:{self.NEW_TREE}:{'5' * 64}"

    @staticmethod
    def _anchor_ik(*_args):
        return f"one:{'6' * 40}:{TREE}:{'7' * 64}"

    def _result(self, verifier, reviews=None, comments=(), **kwargs):
        return review_result(
            self.NEW_HEAD, list(comments), reviews=reviews,
            base_sha=self.NEW_BASE, tree_sha=self.NEW_TREE,
            identity_key=kwargs.pop("identity_key", self._ik()),
            carry_forward_verifier=verifier, **kwargs,
        )

    def test_patch_equivalence(self):
        old = [self._file("a.rs", "@@ -1,3 +1,3 @@\n ctx\n-x = 1\n+x = 2\n ctx2")]
        moved = [self._file("a.rs", "@@ -9,3 +9,3 @@\n other\n-x = 1\n+x = 2\n ctx3")]
        self.assertTrue(rebase_only_patch_equivalent(old, moved))
        # A one-line semantic change in an added line never carries forward.
        semantic = [self._file("a.rs", "@@ -1,3 +1,3 @@\n ctx\n-x = 1\n+x = 3\n ctx2")]
        self.assertFalse(rebase_only_patch_equivalent(old, semantic))
        removed = [self._file("a.rs", "@@ -1,3 +1,3 @@\n ctx\n-x = 0\n+x = 2\n ctx2")]
        self.assertFalse(rebase_only_patch_equivalent(old, removed))
        no_eol = [self._file("a.rs", "@@ -1,3 +1,3 @@\n ctx\n-x = 1\n+x = 2\n\\ No newline at end of file")]
        self.assertFalse(rebase_only_patch_equivalent(old, no_eol))
        extra = old + [self._file("b.rs", "@@ -0,0 +1 @@\n+y", status="added")]
        self.assertFalse(rebase_only_patch_equivalent(old, extra))
        self.assertFalse(rebase_only_patch_equivalent(extra, old))
        renamed = [self._file("a.rs", old[0]["patch"], status="renamed", previous="z.rs")]
        self.assertFalse(rebase_only_patch_equivalent(old, renamed))
        added = [self._file("a.rs", old[0]["patch"], status="added")]
        self.assertFalse(rebase_only_patch_equivalent(old, added))
        other_src = [self._file("a.rs", old[0]["patch"], status="renamed", previous="y.rs")]
        self.assertFalse(rebase_only_patch_equivalent(renamed, other_src))
        binary = [{"filename": "a.rs", "status": "modified", "sha": self.BLOB}]
        self.assertFalse(rebase_only_patch_equivalent(binary, binary))
        self.assertFalse(rebase_only_patch_equivalent(old + old, old + old))
        self.assertFalse(rebase_only_patch_equivalent(old, old + old))
        self.assertFalse(rebase_only_patch_equivalent([], []))
        many = [self._file(f"f{i}", "+x") for i in range(300)]
        self.assertFalse(rebase_only_patch_equivalent(many, many))
        self.assertFalse(rebase_only_patch_equivalent([{"filename": 5}], [{"filename": 5}]))
        # The resulting blob must match and must be present.
        self.assertFalse(rebase_only_patch_equivalent(old, [dict(old[0], sha="8" * 40)]))
        no_sha = [{k: v for k, v in old[0].items() if k != "sha"}]
        self.assertFalse(rebase_only_patch_equivalent(no_sha, no_sha))
        self.assertFalse(rebase_only_patch_equivalent(
            [dict(old[0], sha="xyz")], [dict(old[0], sha="xyz")]))
        # Only an allowlisted file the base changed skips the blob check.
        manifest = "anneal/trusted/root-manifest.sha256"
        m_old = [self._file(manifest, "@@ -1 +1 @@\n-a\n+b", sha="a" * 40)]
        m_new = [self._file(manifest, "@@ -1 +1 @@\n-a\n+b", sha="b" * 40)]
        self.assertTrue(rebase_only_patch_equivalent(m_old, m_new, frozenset({manifest})))
        self.assertFalse(rebase_only_patch_equivalent(m_old, m_new))
        m_add = [dict(m, status="added") for m in m_old]
        m_add2 = [dict(m, status="added") for m in m_new]
        self.assertFalse(rebase_only_patch_equivalent(m_add, m_add2, frozenset({manifest})))

    def test_diff_file_modes(self):
        diff = ("diff --git a/x.sh b/x.sh\nold mode 100644\nnew mode 100755\n"
                "index 1111111..2222222\n--- a/x.sh\n+++ b/x.sh\n@@ -1 +1 @@\n-a\n+b\n"
                "diff --git a/y b/y\nnew file mode 120000\nindex 0000000..3333333\n"
                "--- /dev/null\n+++ b/y\n@@ -0,0 +1 @@\n+target\n"
                "diff --git a/z.rs b/z.rs\nindex 4444444..5555555 100644\n--- a/z.rs\n")
        self.assertEqual(diff_file_modes(diff), {
            "x.sh": ["old mode 100644", "new mode 100755"],
            "y": ["new file mode 120000"],
            "z.rs": ["index 100644"],
        })
        self.assertIsNone(diff_file_modes(
            diff + "diff --git a/z.rs b/z.rs\nindex 6666666..7777777 100644\n"))
        self.assertIsNone(diff_file_modes('diff --git "a/q x" "b/q x"\n'))
        self.assertIsNone(diff_file_modes(None))
        self.assertIsNone(diff_file_modes("diff --git a/q b/q\n--- a/q\n"))

    def test_base_drift(self):
        manifest = "anneal/trusted/root-manifest.sha256"
        paths = {"anneal/x.rs", manifest, "anneal/Cargo.lock"}
        other = [{"filename": "zerocopy/src/lib.rs"}]
        self.assertEqual(base_drift_allows_carry_forward("ahead", other, paths), frozenset())
        self.assertIsNone(base_drift_allows_carry_forward("identical", [], paths))
        self.assertIsNone(base_drift_allows_carry_forward("identical", other, paths))
        self.assertIsNone(base_drift_allows_carry_forward(
            "ahead", [{"filename": "anneal/x.rs"}], paths))
        self.assertIsNone(base_drift_allows_carry_forward(
            "ahead", [{"filename": "new.rs", "previous_filename": "anneal/x.rs"}], paths))
        self.assertEqual(base_drift_allows_carry_forward(
            "ahead", [{"filename": manifest}], paths), frozenset({manifest}))
        # Cargo.lock lines depend on their enclosing package, so no overlap.
        self.assertIsNone(base_drift_allows_carry_forward(
            "ahead", [{"filename": "anneal/Cargo.lock"}], paths))
        for status in ("diverged", "behind", None):
            self.assertIsNone(base_drift_allows_carry_forward(status, other, paths))
        self.assertIsNone(base_drift_allows_carry_forward("ahead", [], paths))
        self.assertIsNone(base_drift_allows_carry_forward(
            "ahead", [{"filename": f"f{i}"} for i in range(300)], paths))
        self.assertIsNone(base_drift_allows_carry_forward("ahead", [{"x": 1}], paths))
        self.assertIsNone(base_drift_allows_carry_forward(
            "ahead", [{"filename": "q", "previous_filename": []}], paths))

    def test_review_result_carries_forward_only_when_verified(self):
        anchor = gate2_review(head_sha=HEAD, base_sha=BASE, tree_sha=TREE)
        calls = []

        def ok(*args):
            calls.append(args)
            return self._anchor_ik()

        res = self._result(ok, reviews=[anchor])
        self.assertEqual(res.state, "success")
        self.assertIn(f"Gate 2 review of {HEAD[:12]} carried forward", res.reason)
        self.assertEqual(calls, [(HEAD, BASE, TREE, self.NEW_HEAD, self.NEW_BASE, [])])
        for bad in (None, False, True, "multi:x", f"one:{'6' * 40}"):
            with self.subTest(verifier_returns=bad):
                self.assertEqual(self._result(lambda *a, b=bad: b, reviews=[anchor]).state,
                                 "pending")

        def boom(*a):
            raise RuntimeError("GitHub GET: HTTP 404")
        self.assertEqual(self._result(boom, reviews=[anchor]).state, "pending")
        # Without a verifier (the default) nothing changes.
        self.assertEqual(self._result(None, reviews=[anchor]).state, "pending")

    def test_anchor_requirements(self):
        verify = self._anchor_ik
        p2 = {"severity": "P2", "summary": "bug"}
        cases = {
            "findings": gate2_review(verdict="findings", findings=[p2]),
            "incomplete": gate2_review(verdict="incomplete"),
            "same_family": gate2_review(reviewer_family="claude", author_family="claude"),
            "changes_requested": gate2_review(state="CHANGES_REQUESTED"),
            "stale_merge_base": gate2_review(merge_base=OTHER_BASE),
            "wrong_commit_id": gate2_review(commit_id=OTHER_HEAD),
            # A structured identity_key that contradicts the verified one.
            "wrong_identity_key": gate2_review(
                identity_key=f"one:{'6' * 40}:{TREE}:{'8' * 64}"),
            # Same base: identity-preserving rewrites use the normal path,
            # which enforces base-change freshness.
            "same_base": gate2_review(base_sha=self.NEW_BASE),
            "same_head": gate2_review(head_sha=self.NEW_HEAD, tree_sha=self.NEW_TREE),
        }
        for label, rev in cases.items():
            with self.subTest(label):
                self.assertNotEqual(self._result(verify, reviews=[rev]).state, "success")
        self.assertEqual(self._result(verify, reviews=[gate2_review(
            identity_key=self._anchor_ik())]).state, "success")
        # Only the latest item can anchor: a later findings review blocks.
        clean = gate2_review(review_id=20, submitted_at="2026-11-23T01:00:00Z")
        later = gate2_review(review_id=21, submitted_at="2026-11-23T02:00:00Z",
                             head_sha=OTHER_HEAD, tree_sha=OTHER_TREE,
                             verdict="findings", findings=[p2])
        self.assertNotEqual(self._result(verify, reviews=[clean, later]).state, "success")
        # A tombstoned (deleted-through) comment cannot anchor.
        comment = gate2_comment(comment_id=30)
        self.assertEqual(self._result(verify, comments=[comment]).state, "success")
        self.assertNotEqual(
            self._result(verify, comments=[comment], deleted_through=30).state, "success")
        # Multi-commit PRs never carry forward.
        self.assertNotEqual(self._result(
            verify, reviews=[gate2_review()],
            identity_key=f"multi:{self.NEW_BASE}:{self.NEW_HEAD}").state, "success")

    def test_earlier_findings_on_anchor_still_block(self):
        verify = self._anchor_ik
        p0 = {"severity": "P0", "summary": "unsound"}
        r1 = gate2_review(review_id=20, submitted_at="2026-11-23T01:00:00Z",
                          verdict="findings", findings=[p0])
        r2 = gate2_review(review_id=21, submitted_at="2026-11-23T02:00:00Z")
        self.assertNotEqual(self._result(verify, reviews=[r1, r2]).state, "success")
        # Findings on another head with the anchor's tree also block.
        r1_tree = gate2_review(review_id=20, submitted_at="2026-11-23T01:00:00Z",
                               head_sha=OTHER_HEAD, verdict="findings", findings=[p0])
        self.assertNotEqual(self._result(verify, reviews=[r1_tree, r2]).state, "success")
        # Findings in a deleted-through comment still block, on the anchor's
        # head or on another head with its tree.
        for c_head in (HEAD, OTHER_HEAD):
            c1 = gate2_comment(comment_id=30, head_sha=c_head,
                               verdict="findings", findings=[p0])
            self.assertNotEqual(
                self._result(verify, comments=[c1], reviews=[r2],
                             deleted_through=30).state,
                "success")
        # Unrelated findings on an earlier head and tree do not.
        r1_other = gate2_review(review_id=20, submitted_at="2026-11-23T01:00:00Z",
                                head_sha=OTHER_HEAD, tree_sha=OTHER_TREE,
                                verdict="findings", findings=[p0])
        self.assertEqual(self._result(verify, reviews=[r1_other, r2]).state, "success")

    def test_non_finding_failures_on_anchor_identity_block(self):
        verify = self._anchor_ik
        anchor = gate2_review(review_id=21, submitted_at="2026-11-23T02:00:00Z")
        # A failing item on another commit with the anchor's tree (the only
        # commits that can share its one-commit identity) still blocks.
        for label, failing in (
            ("changes_requested", gate2_review(
                review_id=20, submitted_at="2026-11-23T01:00:00Z",
                head_sha=OTHER_HEAD, state="CHANGES_REQUESTED")),
            ("same_family", gate2_review(
                review_id=20, submitted_at="2026-11-23T01:00:00Z",
                head_sha=OTHER_HEAD, reviewer_family="claude")),
            ("wrong_commit_id", gate2_review(
                review_id=20, submitted_at="2026-11-23T01:00:00Z",
                head_sha=OTHER_HEAD, commit_id=HEAD)),
        ):
            with self.subTest(label):
                self.assertNotEqual(
                    self._result(verify, reviews=[failing, anchor]).state, "success")
        # As under the normal rules, such a failure in a deleted-through
        # comment, on another tree, or with a stale merge_base does not.
        tomb = gate2_comment(comment_id=30, created_at="2026-11-23T01:00:00Z",
                             head_sha=OTHER_HEAD, reviewer_family="claude")
        self.assertEqual(
            self._result(verify, reviews=[anchor], comments=[tomb],
                         deleted_through=30).state, "success")
        other_tree = gate2_review(review_id=20, submitted_at="2026-11-23T01:00:00Z",
                                  head_sha=OTHER_HEAD, tree_sha=OTHER_TREE,
                                  state="CHANGES_REQUESTED")
        self.assertEqual(self._result(verify, reviews=[other_tree, anchor]).state, "success")

    def test_deletion_cannot_hide_newer_items(self):
        verify = self._anchor_ik
        p2 = {"severity": "P2", "summary": "bug"}
        anchor = gate2_review(review_id=21, submitted_at="2026-11-23T01:00:00Z")
        newer = gate2_comment(comment_id=50, created_at="2026-11-23T02:00:00Z",
                              head_sha=OTHER_HEAD, tree_sha=OTHER_TREE,
                              verdict="findings", findings=[p2])
        self.assertNotEqual(
            self._result(verify, reviews=[anchor], comments=[newer],
                         deleted_through=60).state, "success")
        clean_tomb = gate2_comment(comment_id=50, created_at="2026-11-23T02:00:00Z")
        self.assertNotEqual(
            self._result(verify, reviews=[anchor], comments=[clean_tomb],
                         deleted_through=60).state, "success")

    def test_heads_with_findings_are_sent_to_the_verifier(self):
        p2 = {"severity": "P2", "summary": "bug"}
        seen = []

        def verify(*args):
            seen.append(args[5])
            return self._anchor_ik()

        # Findings on another head (say, an earlier rebase of the same patch)
        # posted before a late clean review of the anchor: the verifier gets
        # that head so it can refuse when the patches match.
        findings = gate2_review(review_id=20, submitted_at="2026-11-23T01:00:00Z",
                                head_sha=OTHER_HEAD, tree_sha=OTHER_TREE,
                                base_sha=OTHER_BASE, verdict="findings", findings=[p2])
        failing = gate2_review(review_id=19, submitted_at="2026-11-23T00:30:00Z",
                               head_sha="d" * 40, tree_sha="c" * 40,
                               state="CHANGES_REQUESTED")
        clean_other = gate2_review(review_id=18, submitted_at="2026-11-23T00:20:00Z",
                                   head_sha="9" * 40, tree_sha="8" * 40)
        anchor = gate2_review(review_id=21, submitted_at="2026-11-23T02:00:00Z")
        self.assertEqual(self._result(verify, reviews=[clean_other, failing, findings,
                                                       anchor]).state, "success")
        self.assertEqual(seen, [sorted([OTHER_HEAD, "d" * 40])])
        self.assertEqual(self._result(lambda *a: None, reviews=[findings, anchor]).state,
                         "pending")

    def test_codex_summaries_block(self):
        verify = self._anchor_ik
        for label, summ in (
            ("findings_on_anchor", summary(head=HEAD, has_any_findings=True)),
            ("in_progress_on_new_head", summary(head=self.NEW_HEAD, status="in_progress")),
            ("findings_on_new_head", summary(head=self.NEW_HEAD, has_any_findings=True)),
        ):
            with self.subTest(label):
                self.assertNotEqual(
                    self._result(verify, reviews=[gate2_review()], comments=[summ]).state,
                    "success")
        clean = summary(head=OTHER_HEAD)
        self.assertEqual(
            self._result(verify, reviews=[gate2_review()], comments=[clean]).state, "success")

    def test_reconcile_uses_github_verifier(self):
        new_head, new_tree = "1" * 40, "3" * 40
        anchor = gate2_review(head_sha=HEAD, base_sha=OTHER_BASE, tree_sha=TREE)

        class VerifyingGitHub(FakeGitHub):
            def __init__(self, verdict, **kw):
                super().__init__(**kw)
                self.verdict = verdict
                self.calls = []

            def verify_rebase_carry_forward(self, *args):
                self.calls.append(args)
                return self.verdict

        for verdict, expected in ((self._anchor_ik(), "success"), (None, "pending")):
            with self.subTest(verdict=verdict):
                gh = VerifyingGitHub(
                    verdict,
                    initial=[pull(head=new_head)], comments={1: []},
                    reviews={1: [anchor]},
                    trees={new_head: new_tree, BASE: "4" * 40, HEAD: TREE},
                    parents={new_head: [BASE]}, messages={new_head: "m"},
                )
                results = reconcile(gh)
                self.assertEqual(results[new_head].state, expected)
                self.assertEqual(gh.calls, [(HEAD, OTHER_BASE, TREE, new_head, BASE, [])])
        # A fake without the verifier keeps the old behavior.
        gh = FakeGitHub(
            initial=[pull(head=new_head)], comments={1: []}, reviews={1: [anchor]},
            trees={new_head: new_tree, BASE: "4" * 40, HEAD: TREE},
            parents={new_head: [BASE]}, messages={new_head: "m"},
        )
        self.assertEqual(reconcile(gh)[new_head].state, "pending")
