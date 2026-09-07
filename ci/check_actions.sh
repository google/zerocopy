#!/usr/bin/env bash
#
# Copyright 2025 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -eo pipefail
cd "$(dirname "$0")/.."

script_name="ci/check_actions.sh"

# The Kani toolchain audit is manual: it records the bundled compiler, target,
# CBMC, option behavior, and the applicability of versioned Rust contracts.
# Require its visible version label to match the executable workflow pin so an
# automated pin-only roll cannot silently make that record stale.
semver_core='(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)'
kani_pin_line_regex="^[[:space:]]*kani-version:[[:space:]]+(${semver_core})$"
kani_audit_line_regex="^[[:space:]]*-[[:space:]]+\*\*Recorded toolchain audit for \`kani-version: (${semver_core})\`:\*\*.*$"

# Count every candidate before parsing. A valid line must not hide an
# additional malformed or duplicate key/label.
mapfile -t kani_pin_lines < <(
    # Deliberately conservative: catch quoted keys, whitespace before `:`, and
    # other noncanonical YAML spellings. The strict parser below accepts only
    # the one canonical line, so an equivalent duplicate cannot hide from the
    # audit-version comparison.
    awk '
        {
            line = $0
            sub(/^[[:space:]]*/, "", line)
            if (line !~ /^#/ && line ~ /kani-version/) print
        }
    ' .github/workflows/ci.yml
)
mapfile -t kani_audit_lines < <(
    grep -F 'Recorded toolchain audit for' zerocopy/agent_docs/validation.md || true
)

if [[ ${#kani_pin_lines[@]} -ne 1 ]]; then
    echo "$script_name: expected exactly one Kani workflow-pin candidate; found ${#kani_pin_lines[@]}" >&2
    exit 1
fi
if [[ ${#kani_audit_lines[@]} -ne 1 ]]; then
    echo "$script_name: expected exactly one recorded Kani audit-label candidate; found ${#kani_audit_lines[@]}" >&2
    exit 1
fi
if [[ "${kani_pin_lines[0]}" =~ $kani_pin_line_regex ]]; then
    kani_version="${BASH_REMATCH[1]}"
else
    echo "$script_name: malformed Kani workflow pin: '${kani_pin_lines[0]}'" >&2
    exit 1
fi
if [[ "${kani_audit_lines[0]}" =~ $kani_audit_line_regex ]]; then
    kani_audit_version="${BASH_REMATCH[1]}"
else
    echo "$script_name: malformed recorded Kani audit label: '${kani_audit_lines[0]}'" >&2
    exit 1
fi
if [[ "$kani_version" != "$kani_audit_version" ]]; then
    printf '%s\n' \
        "$script_name: Kani $kani_version is pinned, but the manual toolchain audit covers Kani $kani_audit_version." \
        "$script_name: replace the compiler/target/CBMC audit, recheck every versioned contract and tool-option premise, update its version label, and rerun the complete Kani suite." \
        >&2
    exit 1
fi

# Ensure action-validator is installed
if [ ! -x "$HOME/.cargo/bin/action-validator" ]; then
    echo "$script_name: action-validator not found, installing..." >&2
    # Install specific version to ensure reproducibility
    cargo install -q action-validator --version 0.8.0 --locked
fi
export PATH="$HOME/.cargo/bin:$PATH"

# Files to exclude from validation (e.g., because they are not Actions/Workflows)
# Use relative paths matching `find .github` output
EXCLUDE_FILES=(
    "./.github/dependabot.yml"
    "./.github/release.yml"
)

failed=0

# Use process substitution and while loop to handle filenames with spaces robustly
while IFS= read -r -d '' file; do
    # Check if file is in exclusion list
    for exclude in "${EXCLUDE_FILES[@]}"; do
        if [[ "$file" == "$exclude" ]]; then
            continue 2
        fi
    done

    if ! output=$(action-validator "$file" 2>&1); then
        echo "$script_name: ❌ Validation failed for $file" >&2
        echo "$output" | sed "s|^|$script_name:   |" >&2
        failed=1
    fi
done < <(find ./.github -type f \( -iname '*.yml' -o -iname '*.yaml' \) -print0)

if [[ $failed -ne 0 ]]; then
    echo "$script_name: One or more files failed validation." >&2
    exit 1
fi
