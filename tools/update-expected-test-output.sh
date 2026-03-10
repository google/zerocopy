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

# Update the `.stderr` reference files used to validate our UI tests. This also
# updates the `.s` assembly snapshots for all ISAs, and the `.mca` files for
# supported ISAs, which are used to validate our codegen tests. The codegen
# framework assumes that `rustup` is installed and available in the
# environment's `PATH` to properly add cross-compilation targets.
rustup target add --toolchain $(./cargo.sh --version nightly) thumbv7m-none-eabi riscv32imc-unknown-none-elf
BLESS=1 ./cargo.sh +nightly test --test codegen -p zerocopy --all-features
BLESS=1 ./cargo.sh +nightly test --test ui -p zerocopy --all-features
BLESS=1 ./cargo.sh +stable  test --test ui -p zerocopy --features=__internal_use_only_features_that_work_on_stable
BLESS=1 ./cargo.sh +msrv test --test ui -p zerocopy --features=__internal_use_only_features_that_work_on_stable

BLESS=1 ./cargo.sh +all test --test ui -p zerocopy-derive

# Update zerocopy-derive's `.expected.rs` files used to validate derive output.
ZEROCOPY_BLESS=1 ./cargo.sh +nightly test -p zerocopy-derive --lib
