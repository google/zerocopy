# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Repository paths, the forbidden-token pattern, and the finding record
shared by the Lean template hygiene scanners."""

from dataclasses import dataclass
from pathlib import Path
import re

REPO_ROOT = Path(__file__).resolve().parents[3]
CHECKS_TOML = REPO_ROOT / "ci" / "checks.toml"
LEAN_SCAN_DIRS = (
    REPO_ROOT / "anneal" / "theory",
    REPO_ROOT / "anneal" / "correspondence",
    REPO_ROOT / "anneal" / "tools" / "anneal-spec" / "tests",
    REPO_ROOT / "zerocopy" / "proofs",
)
RUST_INIT_TEMPLATE = (
    REPO_ROOT / "anneal" / "trusted" / "cargo-anneal" / "src" / "init.rs"
)
RUST_INIT_ASSETS_DIR = (
    REPO_ROOT / "anneal" / "trusted" / "cargo-anneal" / "assets"
)
PYTHON_SCAFFOLD_TEMPLATE = REPO_ROOT / "anneal" / "ci" / "anneal_scaffold.py"

FORBIDDEN_TOKEN_RE = re.compile(
    r"(?<![A-Za-z0-9_])(?:sorry|admit|sorryAx)(?![A-Za-z0-9_'])"
)


@dataclass(frozen=True)
class HygieneFinding:
    path: str
    line: int
    token: str
    snippet: str
