#!/bin/bash
#
# Copyright 2024 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Update the `.stderr` reference files used to validate our UI tests.

set -e

TRYBUILD=overwrite ./cargo.sh +nightly test ui --test trybuild -p zerocopy --all-features
TRYBUILD=overwrite ./cargo.sh +stable  test ui --test trybuild -p zerocopy --features=__internal_use_only_features_that_work_on_stable
# For developers using Rust Analyzer, it's often the case that Rust Analyzer has
# chosen versions of dependencies (especially syn) which have an MSRV higher than
# our own. Doing `rm Cargo.lock` here permits `./cargo.sh +msrv` to choose its own
# versions of these crates that have a lower MSRV.
rm Cargo.lock && TRYBUILD=overwrite ./cargo.sh +msrv    test ui --test trybuild -p zerocopy --features=__internal_use_only_features_that_work_on_stable

TRYBUILD=overwrite ./cargo.sh +all test ui --test trybuild -p zerocopy-derive
