#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
# SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
set -euo pipefail

experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_dir="$(dirname -- "$experiment_dir")"
toolchain="${RFL_TOOLCHAIN:-stable}"
if [[ ! -f "$repo_dir/rfl-linux/rust/pin-init/src/lib.rs" ]]; then
    echo "Run $experiment_dir/setup-linux.sh first." >&2
    exit 1
fi
if [[ $# -eq 0 ]]; then
    set -- test
fi
command="$1"
shift
if [[ "$command" == miri ]]; then
    subcommand="${1:-test}"
    if [[ $# -gt 0 ]]; then
        shift
    fi
    # Sysroot dependencies are separate from the experiment's local dependencies.
    # Build outside zerocopy/.cargo's vendored-source configuration.
    version="$("$repo_dir/zerocopy/cargo.sh" --version "$toolchain")"
    setup_dir="$(mktemp -d)"
    trap 'rmdir "$setup_dir"' EXIT
    (cd "$setup_dir" && rustup run "$version" cargo miri setup)
    rmdir "$setup_dir"
    trap - EXIT
    cd "$repo_dir"
    exec "$repo_dir/zerocopy/cargo.sh" "+$toolchain" miri "$subcommand" \
        --manifest-path "$experiment_dir/Cargo.toml" --offline --locked "$@"
fi
cd "$repo_dir"
exec "$repo_dir/zerocopy/cargo.sh" "+$toolchain" "$command" \
    --manifest-path "$experiment_dir/Cargo.toml" --offline --locked "$@"
