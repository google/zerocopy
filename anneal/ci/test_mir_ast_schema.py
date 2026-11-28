# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Enforce zero-default invariants on `Trusted.MirAst` types."""

# The test methods live in the `mir_ast_schema_tests` package, grouped by
# domain into plain mixin classes. Composing them into `MirAstSchemaTests`
# here lets `unittest` discovery, which loads only `test_*.py` files, find
# each test exactly once under its original class and method names.

import unittest

from mir_ast_schema_tests.audit_rejections import AuditRejectionCases
from mir_ast_schema_tests.live_sources import LiveSourcesCases


class MirAstSchemaTests(
    LiveSourcesCases,
    AuditRejectionCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
