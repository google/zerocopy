# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared imports, repository paths, and helpers for the ci-core workflow
tests."""

import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib

from anneal_ci_lib import WorkflowRepoFixture, find_workflow_step, load_workflow
from workflow_yaml import load_workflow_yaml


SOURCE = Path(__file__).resolve().parent.parent
ANNEAL_ROOT = SOURCE.parent
REPO_ROOT = ANNEAL_ROOT.parent


def extract_bash_function(script_text: str, func_name: str) -> str:
    """Extract a top-level `func_name() { ... }` definition from bash text."""
    pattern = re.compile(
        rf"(?m)^{re.escape(func_name)}\(\)\s*\{{\n.*?\n\}}$",
        flags=re.DOTALL,
    )
    match = pattern.search(script_text)
    if match is None:
        raise AssertionError(f"missing bash function {func_name}()")
    return match.group(0)
