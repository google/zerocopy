# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Property fuzzers, concurrency interleavings, and mutation guards."""

# The test methods live in mixins in the `codex_review_property_tests`
# package, one module per domain. `CodexReviewPropertyTests` combines them,
# so `unittest` discovery, which loads only `test_*.py` files, runs each test
# exactly once under its original `Class.method` name.

from pathlib import Path
import sys
import unittest

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from codex_review_property_tests.carry_forward import (
    CarryForwardPropertyCases,
)
from codex_review_property_tests.carry_forward_probes import (
    CarryForwardProbeSuite,
)
from codex_review_property_tests.context_and_anchors import (
    ContextAndAnchorPropertyCases,
)


class CodexReviewPropertyTests(
    CarryForwardPropertyCases,
    CarryForwardProbeSuite,
    ContextAndAnchorPropertyCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
