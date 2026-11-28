# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and live-Lean integration tests for `anneal/ci/anneal-lsp`."""

# The test methods live in the `anneal_lsp_tests` package as plain mixin
# classes. Composing them into the `TestCase` classes here lets `unittest`
# discovery, which loads only `test_*.py` files, find each test exactly once
# under its original class and method names.

from pathlib import Path
import sys
import unittest

# Keep imports of the package below from writing `__pycache__` beside it.
sys.dont_write_bytecode = True

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

from anneal_lsp_tests.discovery_cases import DiscoveryCases  # noqa: E402
from anneal_lsp_tests.live_server_cases import LiveServerCases  # noqa: E402
from anneal_lsp_tests.mock_mcp_cases import MockMcpCases  # noqa: E402
from anneal_lsp_tests.mock_pool_cases import MockPoolCases  # noqa: E402
from anneal_lsp_tests.mock_recovery_cases import MockRecoveryCases  # noqa: E402
from anneal_lsp_tests.sandbox_guard_cases import SandboxGuardCases  # noqa: E402


class DiscoveryAndProtocolTests(
    DiscoveryCases,
    SandboxGuardCases,
    unittest.TestCase,
):
    pass


class MockLspAndMcpTests(
    MockPoolCases,
    MockRecoveryCases,
    MockMcpCases,
    unittest.TestCase,
):
    pass


class LiveLeanServerIntegrationTest(
    LiveServerCases,
    unittest.TestCase,
):
    pass


if __name__ == "__main__":
    unittest.main()
