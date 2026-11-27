#!/usr/bin/env bash
#
# Copyright 2024 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -eo pipefail
cd "$(dirname "$0")/.."

if [[ "$1" == "--fix" ]]; then
    FMT_FLAGS=()
else
    FMT_FLAGS=("--check")
fi

NIGHTLY="$(zerocopy/cargo.sh --version nightly)"

zerocopy/ci/check_fmt.sh "$@"

# `--all` formats every workspace member. Without it, older `cargo fmt`
# releases fail with "Failed to find targets" on a virtual manifest such as
# `anneal/tools/anneal-spec/Cargo.toml`. None of these manifests has path
# dependencies outside its own workspace, which `--all` would also format.
for manifest in anneal/tools/anneal-spec/Cargo.toml tools/cargo-zerocopy/Cargo.toml tools/generate-readme/Cargo.toml tools/ui-runner/Cargo.toml tools/anneal-mir-eval/Cargo.toml; do
    cargo +"$NIGHTLY" fmt --manifest-path "$manifest" --all "${FMT_FLAGS[@]}" >&2
done
cargo +"$NIGHTLY" fmt --manifest-path exocrate/Cargo.toml "${FMT_FLAGS[@]}" >&2
