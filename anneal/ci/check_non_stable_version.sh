#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail
cd "$(dirname "$0")/.."

# FIXME(#87): We must address all blockers listed in #87 before permitting
# stable releases.
python3 - <<'EOF'
import re
import sys

try:
    import tomllib
except ImportError:
    import tomli as tomllib

manifest_path = "trusted/cargo-anneal/Cargo.toml"
try:
    with open(manifest_path, "rb") as f:
        data = tomllib.load(f)
except Exception as e:
    print(f"Error reading {manifest_path}: {e}", file=sys.stderr)
    sys.exit(1)

package = data.get("package", {})
version = package.get("version")
if not version:
    print(
        f"Error: {manifest_path} does not specify package.version",
        file=sys.stderr,
    )
    sys.exit(1)

# Ensure the version number is a non-stable pre-release version (e.g.,
# 0.1.0-alpha.1). Under SemVer 2.0.0, pre-release versions append a hyphen and a
# series of dot-separated identifiers to the patch version. Normal / stable
# versions (such as 0.1.0 or 1.0.0) lack a pre-release tag and are forbidden
# until all blockers in #87 are resolved.
#
# FIXME(#87): We must address all blockers listed in #87 before permitting
# stable releases.
prerelease_pattern = r"^[0-9]+\.[0-9]+\.[0-9]+-[0-9A-Za-z.-]+$"
if not re.match(prerelease_pattern, version):
    print(
        f"Error: package.version '{version}' in {manifest_path} is not a "
        "pre-release version.\n"
        "Stable releases are blocked until all issues in #87 are resolved.\n"
        "See: https://github.com/joshlf/anneal/issues/87",
        file=sys.stderr,
    )
    sys.exit(1)

print(f"Verified {manifest_path} has non-stable pre-release version: {version}")
EOF
