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

cargo install -q cargo-rdme --version 1.5.0

# We use `cargo-rdme` to check that the README is up-to-date with the crate
# documentation. We use `--intralinks-strip-links` to strip intra-doc links
# (e.g., `[Vec]`) because `cargo-rdme`'s link resolution is currently unreliable
# in this codebase (likely due to complex re-exports and glob imports), often
# resulting in broken links or missing definitions. Stripping them keeps the
# README clean and readable on GitHub, matching the previous behavior of our
# custom script.
cargo rdme --check --intralinks-strip-links
