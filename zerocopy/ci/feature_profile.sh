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

# This helper is the only translation from semantic CI profiles to Cargo
# feature arguments. Both ci.yml's shared environment setup and
# run_build_test_cell.sh consume it, while check_all_toolchains_tested.sh
# validates every mapping and requires the matrix to add `no-default` as soon
# as Cargo.toml defines a non-empty default feature set. Keep the output as
# whitespace-separated arguments: run_build_test_cell.sh deliberately parses
# it into an array without `eval`.
if [[ $# -ne 1 ]]; then
  echo "usage: $0 <default|no-default|stable|all>" >&2
  exit 1
fi

case "$1" in
  default)
    ;;
  no-default)
    echo --no-default-features
    ;;
  stable)
    echo --no-default-features --features \
      __internal_use_only_features_that_work_on_stable
    ;;
  all)
    echo --all-features
    ;;
  *)
    echo "unknown CI feature profile: $1" >&2
    exit 1
    ;;
esac
