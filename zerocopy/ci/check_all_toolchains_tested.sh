#!/usr/bin/env bash
#
# Copyright 2024 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail
cd "$(dirname "$0")/.."

# Verify bijective toolchain alignment across `zerocopy/Cargo.toml`,
# `ci/pins/rust-toolchains.toml`, `ci/docker/zc-*.Dockerfile`, and
# `ci/checks.toml`.
exec python3 -I -B ../ci/scripts/check_toolchains_sync.py
