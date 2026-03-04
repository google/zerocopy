#!/bin/bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Generate documentation useful for local development.

set -eo pipefail

./cargo.sh +nightly rustdoc -- \
    -Z unstable-options \
    --document-hidden-items \
    --document-private-items \
    --generate-macro-expansion \
    --extend-css rustdoc/style.css

