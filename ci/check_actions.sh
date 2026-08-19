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

# Ensure action-validator is installed
if [ ! -x "$HOME/.cargo/bin/action-validator" ]; then
    echo "$script_name: action-validator not found, installing..." >&2
    # Install specific version to ensure reproducibility
    cargo install -q action-validator --version 0.8.0 --locked
fi
export PATH="$HOME/.cargo/bin:$PATH"
export PYTHONDONTWRITEBYTECODE=1

sha256_file() {
    if command -v sha256sum >/dev/null; then
        sha256sum "$1" | cut -d ' ' -f 1
    elif command -v shasum >/dev/null; then
        shasum -a 256 "$1" | cut -d ' ' -f 1
    else
        echo "$script_name: sha256sum or shasum is required" >&2
        return 1
    fi
}

# action-validator checks the workflow schema, while actionlint additionally
# understands where expression functions are legal. GitHub silently declines
# to create a run for some expression-context errors, so this check must also
# run from the local pre-push hook rather than relying on hosted CI to diagnose
# its own workflow file. Use a checksummed upstream binary: requiring a recent
# Go compiler just to validate this repository would make every push depend on
# an otherwise-unrelated development toolchain.
actionlint_version=1.7.12
# Keep these platform hashes coordinated with the checksum manifest attached to
# https://github.com/rhysd/actionlint/releases/tag/v1.7.12.
case "$(uname -s)/$(uname -m)" in
    Linux/x86_64)
        actionlint_platform=linux_amd64
        actionlint_sha256=8aca8db96f1b94770f1b0d72b6dddcb1ebb8123cb3712530b08cc387b349a3d8
        ;;
    Linux/aarch64 | Linux/arm64)
        actionlint_platform=linux_arm64
        actionlint_sha256=325e971b6ba9bfa504672e29be93c24981eeb1c07576d730e9f7c8805afff0c6
        ;;
    Darwin/x86_64)
        actionlint_platform=darwin_amd64
        actionlint_sha256=5b44c3bc2255115c9b69e30efc0fecdf498fdb63c5d58e17084fd5f16324c644
        ;;
    Darwin/arm64)
        actionlint_platform=darwin_arm64
        actionlint_sha256=aba9ced2dee8d27fecca3dc7feb1a7f9a52caefa1eb46f3271ea66b6e0e6953f
        ;;
    *)
        echo "$script_name: actionlint $actionlint_version has no pinned binary for $(uname -s)/$(uname -m)" >&2
        exit 1
        ;;
esac

actionlint_dir="${XDG_CACHE_HOME:-$HOME/.cache}/zerocopy/actionlint-$actionlint_version-$actionlint_platform"
actionlint_bin="$actionlint_dir/actionlint"
if [ ! -x "$actionlint_bin" ]; then
    for tool in curl tar; do
        if ! command -v "$tool" >/dev/null; then
            echo "$script_name: $tool is required to install actionlint" >&2
            exit 1
        fi
    done

    echo "$script_name: actionlint not found, installing..." >&2
    actionlint_tmp="$(mktemp -d "${TMPDIR:-/tmp}/zerocopy-actionlint.XXXXXXXX")"
    trap 'rm -rf "$actionlint_tmp"' EXIT
    actionlint_asset="actionlint_${actionlint_version}_${actionlint_platform}.tar.gz"
    actionlint_archive="$actionlint_tmp/$actionlint_asset"
    curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
        --connect-timeout 15 --max-time 30 \
        --retry 5 --retry-all-errors --retry-max-time 60 \
        --output "$actionlint_archive" \
        "https://github.com/rhysd/actionlint/releases/download/v${actionlint_version}/${actionlint_asset}"

    actionlint_actual_sha256="$(sha256_file "$actionlint_archive")"
    if [ "$actionlint_actual_sha256" != "$actionlint_sha256" ]; then
        echo "$script_name: actionlint checksum mismatch: expected $actionlint_sha256, got $actionlint_actual_sha256" >&2
        exit 1
    fi

    tar -xzf "$actionlint_archive" -C "$actionlint_tmp" actionlint
    mkdir -p "$actionlint_dir"
    actionlint_candidate="$actionlint_dir/.actionlint.$$"
    install -m 0755 "$actionlint_tmp/actionlint" "$actionlint_candidate"
    mv -f "$actionlint_candidate" "$actionlint_bin"
    rm -rf "$actionlint_tmp"
    trap - EXIT
fi

failed=0

# Keep this pass focused on workflow structure and expression contexts. Shell
# and Python sources already have their own repository checks, and enabling
# actionlint's optional external integrations would make results depend on
# whichever shellcheck/pyflakes versions happen to be installed on the host.
# Run the GitHub-aware parser before the repository permission policy below:
# both parsers must accept a workflow before it is considered valid.
if ! output=$("$actionlint_bin" -shellcheck= -pyflakes= 2>&1); then
    echo "$script_name: ❌ actionlint validation failed" >&2
    echo "$output" | sed "s|^|$script_name:   |" >&2
    failed=1
fi

yq_bin="$(./.github/scripts/ensure-yq.sh)"
export YQ="$yq_bin"

# Pull request and merge-group jobs execute proposed repository code. Keep
# their GITHUB_TOKEN read-only even for same-repository PRs, whose tokens are
# not automatically downgraded like fork tokens. The checker is deliberately
# separate from individual workflows so a future publishing optimization
# cannot silently reintroduce write authority.
python3 .github/scripts/check-workflow-permissions.py \
  --yq "$yq_bin" .github/workflows
python3 .github/scripts/test_check_workflow_permissions.py
python3 .github/scripts/test_workflow_artifacts.py
python3 .github/scripts/test_check_crate_version_change.py
python3 .github/scripts/test_create_crates_release_plan.py
python3 .github/scripts/test_reconcile_crates_release.py
python3 .github/scripts/test_release_workflows.py
python3 .github/scripts/test_locked_cargo_invocations.py
python3 .github/scripts/test_ui_feature_coverage.py
python3 .github/actions/require-successful-jobs/test_check.py
python3 githooks/test_pre_push.py

# The hosted workflows delegate every apt operation to this bounded retry
# helper. Its fake-command tests verify timeouts, retries, failure propagation,
# and argument validation without requiring root or network access.
bash .github/scripts/test_install_apt_packages.sh

# cargo-zerocopy is itself CI infrastructure. Its unit tests enforce the
# default locked mode used by every Zerocopy build and test below. The tools
# workspace is intentionally unvendored, so permit a fresh checkout to fetch
# the exact dependencies recorded in its lockfile.
cargo +stable test --locked --manifest-path tools/Cargo.toml \
  -p cargo-zerocopy -p generate-readme

# Files to exclude from validation (e.g., because they are not Actions/Workflows)
# Use relative paths matching `find .github` output
EXCLUDE_FILES=(
    "./.github/dependabot.yml"
    "./.github/release.yml"
)

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
