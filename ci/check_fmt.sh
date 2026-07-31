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

cargo +"$NIGHTLY" fmt --manifest-path tools/Cargo.toml --all "${FMT_FLAGS[@]}" >&2
cargo +"$NIGHTLY" fmt --manifest-path anneal/Cargo.toml --all "${FMT_FLAGS[@]}" >&2
cargo +"$NIGHTLY" fmt --manifest-path anneal/v1/Cargo.toml --all "${FMT_FLAGS[@]}" >&2
cargo +"$NIGHTLY" fmt --manifest-path exocrate/Cargo.toml "${FMT_FLAGS[@]}" >&2
