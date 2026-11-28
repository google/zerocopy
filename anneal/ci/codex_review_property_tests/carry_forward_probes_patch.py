# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Sections 1-3 of the carry-forward probe suite: rebase-only patch
equivalence, base-drift admission, and file-mode and
`GitHub.verify_rebase_carry_forward` checks."""

from __future__ import annotations

from .support import (
    _commit_obj,
    _diff_text,
    ANCHOR_HEAD,
    ANCHOR_IK,
    AUTH_REVIEWERS,
    MSG,
    NEW_BASE,
    NEW_HEAD,
    OLD_BASE,
    OTHER_TREE,
    PARENT_TREE,
    TREE,
    types,
)


class PatchDriftAndModeProbes:
    """Sections 1-3 of `CarryForwardProbeSuite`."""

    def _probe_patch_drift_and_modes(self, mod: types.ModuleType) -> None:
        # 1. `patch` / `rebase_only_patch_equivalent` checks:
        patch_old = (
            "@@ -1,3 +1,3 @@\n ctx1\n-old\n+new\n"
            "\\ No newline at end of file\n"
        )
        patch_ctx = (
            "@@ -10,3 +10,3 @@\n ctx2\n-old\n+new\n"
            "\\ No newline at end of file\n"
        )
        f_old = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        f_ctx = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": patch_ctx,
            }
        ]
        self.assertTrue(mod.rebase_only_patch_equivalent(f_old, f_ctx))
        f_noeols = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": "@@ -10,3 +10,3 @@\n ctx2\n-old\n+new\n",
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_noeols))
        f_ren = [
            {
                "filename": "anneal/ci/x.py",
                "status": "renamed",
                "previous_filename": "a",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_ren))
        f_ren2 = [
            {
                "filename": "anneal/ci/x.py",
                "status": "renamed",
                "previous_filename": "b",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_ren, f_ren2))
        f_blob = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "8" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_blob))
        f_add = [
            {
                "filename": "anneal/ci/x.py",
                "status": "added",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_add))
        f_no_blob = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "patch": patch_old,
            }
        ]
        self.assertFalse(
            mod.rebase_only_patch_equivalent(f_no_blob, f_no_blob)
        )
        try:
            mod._file_change_key(f_no_blob[0], frozenset())
            self.fail("expected ValueError on missing blob sha")
        except ValueError:
            pass
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_old + f_old))
        many_300 = [
            {
                "filename": f"f{i}.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": patch_old,
            }
            for i in range(300)
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(many_300, many_300))
        self.assertFalse(mod.rebase_only_patch_equivalent([], []))
        rm_path = "anneal/trusted/root-manifest.sha256"
        rm_patch = "@@ -1 +1 @@\n-a\n+b\n"
        rm_old = [
            {
                "filename": rm_path,
                "status": "modified",
                "sha": "1" * 40,
                "patch": rm_patch,
            }
        ]
        rm_new = [
            {
                "filename": rm_path,
                "status": "modified",
                "sha": "2" * 40,
                "patch": rm_patch,
            }
        ]
        self.assertTrue(
            mod.rebase_only_patch_equivalent(
                rm_old, rm_new, frozenset({rm_path})
            )
        )
        rm_add = [
            {
                "filename": rm_path,
                "status": "added",
                "sha": "2" * 40,
                "patch": rm_patch,
            }
        ]
        rm_add_other = [
            {
                "filename": rm_path,
                "status": "added",
                "sha": "1" * 40,
                "patch": rm_patch,
            }
        ]
        self.assertFalse(
            mod.rebase_only_patch_equivalent(
                rm_add, rm_new, frozenset({rm_path})
            )
        )
        self.assertFalse(
            mod.rebase_only_patch_equivalent(
                rm_add_other, rm_add, frozenset({rm_path})
            )
        )

        # 2. `base_drift_allows_carry_forward`:
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "identical",
                [{"filename": "other.py", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward("ahead", [], {"anneal/ci/x.py"})
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "other.py", "status": "modified"}] * 300,
                {"anneal/ci/x.py"},
            )
        )
        self.assertEqual(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "other.py", "status": "modified"}],
                {"anneal/ci/x.py"},
            ),
            frozenset(),
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "anneal/ci/x.py", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [
                    {
                        "filename": "y.py",
                        "status": "renamed",
                        "previous_filename": "anneal/ci/x.py",
                    }
                ],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [
                    {
                        "filename": "unrelated.py",
                        "status": "modified",
                        "previous_filename": "",
                    }
                ],
                {"y.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [
                    {
                        "filename": "anneal/docs/codex-review.md",
                        "status": "modified",
                    }
                ],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "AGENTS.md", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "skills/foo.md", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )

        # 3. `diff_file_modes` & `GitHub.verify_rebase_carry_forward`:
        self.assertIsNone(mod.diff_file_modes(_diff_text() + _diff_text()))

        class StubGH(mod.GitHub):
            def __init__(
                self,
                *,
                same_base_compare=False,
                bad_msg=False,
                bad_tree=False,
                bad_parents=False,
                bad_modes=False,
                extra_mode=False,
                extra_both=False,
                diff_other=False,
            ):
                super().__init__("google/zerocopy", "tok", AUTH_REVIEWERS)
                self.same_base_compare = same_base_compare
                self.bad_msg = bad_msg
                self.bad_tree = bad_tree
                self.bad_parents = bad_parents
                self.bad_modes = bad_modes
                self.extra_mode = extra_mode
                self.extra_both = extra_both
                self.diff_other = diff_other

            def request(self, path, data=None):
                if path == f"commits/{ANCHOR_HEAD}":
                    return _commit_obj(
                        ANCHOR_HEAD,
                        "9" * 40 if self.bad_parents else OLD_BASE,
                        OTHER_TREE if self.bad_tree else TREE,
                    )
                if path == f"commits/{NEW_HEAD}":
                    return _commit_obj(
                        NEW_HEAD,
                        OLD_BASE if self.same_base_compare else NEW_BASE,
                        TREE,
                        message="changed" if self.bad_msg else MSG,
                    )
                if path == f"commits/{'9' * 40}":
                    patch_s = (
                        "@@ -1 +1 @@\n-a\n+c\n"
                        if self.diff_other
                        else "@@ -1 +1 @@\n-a\n+b\n"
                    )
                    return _commit_obj(
                        "9" * 40, OLD_BASE, TREE, patch_text=patch_s
                    )
                if path == f"commits/{OLD_BASE}":
                    return {
                        "sha": OLD_BASE,
                        "commit": {
                            "tree": {"sha": PARENT_TREE},
                            "message": "base",
                        },
                    }
                if path.startswith("compare/"):
                    return {
                        "status": "ahead",
                        "files": [
                            {"filename": "unrelated.txt", "status": "modified"}
                        ],
                    }
                raise AssertionError(path)

            def request_text(self, path, accept):
                if path == f"commits/{ANCHOR_HEAD}":
                    if self.extra_both:
                        return _diff_text() + _diff_text("anneal/ci/extra.py")
                    return _diff_text()
                if path == f"commits/{NEW_HEAD}":
                    if self.bad_modes:
                        return _diff_text(mode="100755")
                    if self.extra_mode or self.extra_both:
                        return _diff_text() + _diff_text("anneal/ci/extra.py")
                    return _diff_text()
                raise AssertionError(path)

        self.assertEqual(
            StubGH().verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            ),
            ANCHOR_IK,
        )
        self.assertEqual(
            StubGH(diff_other=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE, ["9" * 40]
            ),
            ANCHOR_IK,
        )
        self.assertIsNone(
            StubGH(diff_other=False).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE, ["9" * 40]
            )
        )
        self.assertIsNone(
            StubGH(same_base_compare=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, OLD_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_msg=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_tree=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_parents=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_modes=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(extra_mode=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(extra_both=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
