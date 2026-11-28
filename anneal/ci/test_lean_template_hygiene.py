# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Static hygiene checks banning `sorry` / `admit` in Lean proofs and templates."""

from pathlib import Path
import sys
import unittest

# Keep imports of the package below from writing `__pycache__` beside it.
sys.dont_write_bytecode = True

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from lean_template_hygiene_tests.cases import LeanTemplateHygieneCases

# Re-exported for `trusted_boundary_claim_sync_tests`.
from lean_template_hygiene_tests.lean_scanner import (  # noqa: F401
    strip_lean_comments_and_strings,
)


class LeanTemplateHygieneTests(LeanTemplateHygieneCases, unittest.TestCase):
    pass


if __name__ == "__main__":
    unittest.main()
