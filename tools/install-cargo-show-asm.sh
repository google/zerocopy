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
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

# This helper is the single version contract for codegen snapshot generation
# and validation. Keep the exact requirement here rather than duplicating it in
# workflow YAML, where the two call sites could drift silently.
"$ROOT/zerocopy/cargo.sh" +nightly install --quiet --locked \
  --version '=0.2.62' cargo-show-asm
