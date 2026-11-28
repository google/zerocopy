# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared imports, workflow paths, and job and variable names for the
release workflow tests."""

from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import tempfile

from anneal_ci_lib import WorkflowRepoFixture, load_workflow, sha256_bytes


WORKFLOWS = Path(__file__).resolve().parents[3] / ".github/workflows"
PUBLISH_ACTION = "./.github/actions/publish-github-release"
UPLOAD_ACTION = "./.github/actions/upload-file-artifact"
DOWNLOAD_ACTION = "./.github/actions/download-artifact-with-retry"
SHA_PINNED_ACTION_RE = re.compile(
    r"\A[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+@[0-9a-f]{40}\Z"
)

ANNEAL_JOBS = (
    "anneal-build-archive",
    "anneal-host-archive",
    "anneal-qualify-package",
    "anneal-publish-crate",
    "anneal-publish-github",
)
STRIPPED_RUNTIME_VARS = (
    "ACTIONS_CACHE_URL",
    "ACTIONS_RESULTS_URL",
    "ACTIONS_RUNTIME_TOKEN",
    "ACTIONS_RUNTIME_URL",
)
STRIPPED_OIDC_VARS = (
    "ACTIONS_ID_TOKEN_REQUEST_URL",
    "ACTIONS_ID_TOKEN_REQUEST_TOKEN",
)
