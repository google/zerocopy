#!/bin/bash
#
# Copyright 2024 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -eo pipefail
cd "$(dirname "$0")/../zerocopy"

# Codegen tests invoke `cargo asm`. Installing through the same helper as the
# validation workflow makes this script self-contained while keeping one exact
# tool version for both snapshot generation and validation.
bash ../tools/install-cargo-show-asm.sh

# Update the `.stderr` reference files used to validate our UI tests and the
# `.x86-64.mca` files used to validate our codegen tests.
BLESS=1 ./cargo.sh +nightly test --test codegen -p zerocopy --all-features
BLESS=1 ./cargo.sh +nightly test --test ui -p zerocopy --all-features
BLESS=1 ./cargo.sh +stable  test --test ui -p zerocopy --features=__internal_use_only_features_that_work_on_stable
BLESS=1 ./cargo.sh +msrv test --test ui -p zerocopy --features=__internal_use_only_features_that_work_on_stable

BLESS=1 ./cargo.sh +all test --test ui -p zerocopy-derive

# Update zerocopy-derive's `.expected.rs` files used to validate derive output.
ZEROCOPY_BLESS=1 ./cargo.sh +nightly test -p zerocopy-derive --lib
