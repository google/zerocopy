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

: "${FMT_DOMAIN:?}"

case "$FMT_DOMAIN" in
  zerocopy)
    ./zerocopy/ci/check_fmt.sh
    ;;
  tools)
    NIGHTLY="${PIN_RUST_TOOLCHAINS__NIGHTLY:-$(./zerocopy/cargo.sh --version nightly)}"
    for manifest in \
      tools/cargo-zerocopy/Cargo.toml \
      tools/generate-readme/Cargo.toml \
      tools/ui-runner/Cargo.toml \
      tools/anneal-mir-eval/Cargo.toml; do
      cargo +"$NIGHTLY" fmt --manifest-path "$manifest" --check >&2
    done
    ;;
  exocrate)
    NIGHTLY="${PIN_RUST_TOOLCHAINS__NIGHTLY:-$(./zerocopy/cargo.sh --version nightly)}"
    cargo +"$NIGHTLY" fmt --manifest-path exocrate/Cargo.toml --check >&2
    ;;
  *)
    echo "error: unknown FMT_DOMAIN: $FMT_DOMAIN" >&2
    exit 1
    ;;
esac
