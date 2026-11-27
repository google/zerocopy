# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `anneal/ci/check_pr_hygiene.py`."""

# Most test methods live in mixins in the `check_pr_hygiene_tests` package,
# one module per domain. Each test class here combines its mixin with its
# original base class, so every test keeps its `module.Class.method` ID and
# `unittest` discovery, which loads only `test_*.py` files, runs it once.

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from check_pr_hygiene_tests.commits import (
    CleanChangeCases,
    CommitMessageCases,
)
from check_pr_hygiene_tests.diff_and_wrap import (
    DiffCases,
    TreeCheckCases,
    TrustedCitationCases,
    WrapCases,
    WrapUnitCases,
)
from check_pr_hygiene_tests.hardening import (
    HardeningCases,
    ReviewSurfaceCases,
)
from check_pr_hygiene_tests.pr_text import (
    PrBodyCases,
    ReceiptCases,
    UnwrapUnitCases,
)
from check_pr_hygiene_tests.support import RepoTestCase, SCRIPT
from check_pr_hygiene_tests.waivers import (
    PrTitlePolicyCases,
    WaiverCases,
)


class CleanChangeTests(CleanChangeCases, RepoTestCase):
    pass


class CommitMessageTests(CommitMessageCases, RepoTestCase):
    pass


class DiffTests(DiffCases, RepoTestCase):
    pass


class WrapTests(WrapCases, RepoTestCase):
    pass


class WrapUnitTests(WrapUnitCases, unittest.TestCase):
    pass


class TrustedCitationTests(TrustedCitationCases, RepoTestCase):
    pass


class TreeCheckTests(TreeCheckCases, RepoTestCase):
    pass


class PrBodyTests(PrBodyCases, RepoTestCase):
    pass


class UnwrapUnitTests(UnwrapUnitCases, unittest.TestCase):
    pass


class ReceiptTests(ReceiptCases, RepoTestCase):
    pass


class HardeningTests(HardeningCases, RepoTestCase):
    pass


class ReviewSurfaceTests(ReviewSurfaceCases, RepoTestCase):
    pass


class WaiverTests(WaiverCases, RepoTestCase):
    pass


class PrTitlePolicyTests(PrTitlePolicyCases, RepoTestCase):
    pass


class RepositoryTreeTests(unittest.TestCase):
    def test_checked_in_tree_passes_tree_checks(self):
        repo = Path(__file__).resolve().parents[2]
        if not (repo / ".git").exists():
            self.skipTest("not running from a Git checkout")
        res = subprocess.run(
            [sys.executable, "-I", "-B", str(SCRIPT), "--repo", str(repo),
             "--json"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)


if __name__ == "__main__":
    unittest.main()
