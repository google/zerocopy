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

if [ "$#" -gt 1 ]; then
  echo "Usage: $0 [manifest_path]" >&2
  exit 1
fi

if [ "$#" -eq 1 ]; then
  manifest_path="$1"
  if [ -z "$manifest_path" ]; then
    echo "Error: manifest path must not be empty" >&2
    exit 1
  fi
  if [[ "$manifest_path" != /* ]]; then
    manifest_path="$PWD/$manifest_path"
  fi
fi

cd "$(dirname "$0")/.."
manifest_path="${manifest_path:-trusted/cargo-anneal/Cargo.toml}"

# FIXME(#4012): We must address all blockers listed in #4012 before permitting
# stable releases.
# Isolate Python (`-I -B`) when stdlib `tomllib` (Python 3.11+) is available so
# ambient repo files or `PYTHONPATH` cannot shadow stdlib and no `__pycache__`
# is written. Fall back to `-B` on Python 3.10 where third-party `tomli` may
# live in user site-packages.
python_flags=(-B)
if python3 -I -B -c "import tomllib" >/dev/null 2>&1; then
  python_flags=(-I -B)
fi
python3 "${python_flags[@]}" - "$manifest_path" <<'EOF'
import re
import sys

try:
    import tomllib
except ImportError:
    import tomli as tomllib

manifest_path = sys.argv[1]
try:
    with open(manifest_path, "rb") as f:
        data = tomllib.load(f)
except Exception as e:
    print(f"Error reading {manifest_path}: {e}", file=sys.stderr)
    sys.exit(1)

package = data.get("package")
if not isinstance(package, dict):
    print(
        f"Error: {manifest_path} does not define a [package] table",
        file=sys.stderr,
    )
    sys.exit(1)

version = package.get("version")
if not isinstance(version, str) or not version:
    print(
        f"Error: {manifest_path} does not specify package.version",
        file=sys.stderr,
    )
    sys.exit(1)

# Enforce the SemVer 2.0.0 pre-release grammar with an optional build-metadata
# suffix, requiring a non-empty `-<pre-release>` component so stable versions
# (such as 0.1.0, 1.0.0, or 0.2.0+build.1) stay blocked until all blockers in
# #4012 are resolved.
#
# FIXME(#4012): We must address all blockers listed in #4012 before permitting
# stable releases.
numeric_ident = r"(?:0|[1-9][0-9]*)"
prerelease_ident = rf"(?:{numeric_ident}|[0-9]*[A-Za-z-][0-9A-Za-z-]*)"
build_ident = r"[0-9A-Za-z-]+"
prerelease_pattern = re.compile(
    rf"{numeric_ident}\.{numeric_ident}\.{numeric_ident}"
    rf"-{prerelease_ident}(?:\.{prerelease_ident})*"
    rf"(?:\+{build_ident}(?:\.{build_ident})*)?",
    re.ASCII,
)
if not prerelease_pattern.fullmatch(version):
    print(
        f"Error: package.version '{version}' in {manifest_path} is not a "
        "valid SemVer 2.0.0 pre-release version.\n"
        "Stable releases are blocked until all issues in #4012 are resolved.\n"
        "See: https://github.com/google/zerocopy/issues/4012",
        file=sys.stderr,
    )
    sys.exit(1)

print(f"Verified {manifest_path} has non-stable pre-release version: {version}")
EOF
