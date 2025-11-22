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

yes | ./cargo.sh +nightly install -q cargo-doc2readme --version 0.6.3

# We run `cargo-doc2readme` with the nightly toolchain and `--expand-macros` so
# that intra-doc links to feature-gated items (like `simd` or `alloc` types)
# are correctly resolved.
#
# We use `yes | ...` because `cargo.sh` is interactive and prompts for
# toolchain installation if it's missing (which is common in CI environments).
yes | ./cargo.sh +nightly doc2readme --expand-macros --all-features --check --template README.j2
