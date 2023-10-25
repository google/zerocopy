#!/bin/bash
#
# Copyright 2023 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# This script is a thin wrapper around Cargo that provides human-friendly
# toolchain names which are automatically translated to the toolchain versions
# we have pinned in CI.
#
#   cargo.sh --version <toolchain-name> # looks up the version for the named toolchain
#   cargo.sh +<toolchain-name> [...]    # runs cargo commands with the named toolchain
#   cargo.sh +all [...]                 # runs cargo commands with each toolchain
#
# The meta-toolchain "all" instructs this script to run the provided command
# once for each toolchain (msrv, stable, nightly).
#
# A common task that is especially annoying to perform by hand is to update
# trybuild's stderr files. Using this script:
#
#   TRYBUILD=overwrite ./cargo.sh +all test --workspace

set -eo pipefail

function print-usage-and-exit {
  echo "Usage:"                          >&2
  echo "  $0 --version <toolchain-name>" >&2
  echo "  $0 +<toolchain-name> [...]"    >&2
  echo "  $0 +all [...]"    >&2
  exit 1
}

[[ $# -gt 0 ]] || print-usage-and-exit

function pkg-meta {
  cargo metadata --format-version 1 | jq -r ".packages[] | select(.name == \"zerocopy\").$1"
}

function lookup-version {
  VERSION="$1"
  case "$VERSION" in
    msrv)
      pkg-meta rust_version
      ;;
    stable)
      pkg-meta 'metadata.ci."pinned-stable"'
      ;;
    nightly)
      pkg-meta 'metadata.ci."pinned-nightly"'
      ;;
    *)
      echo "Unrecognized toolchain name: '$VERSION' (options are 'msrv', 'stable', 'nightly')" >&2
      return 1
      ;;
  esac
}

function get-rustflags {
  [ "$1" == nightly ] && echo "--cfg __INTERNAL_USE_ONLY_NIGHLTY_FEATURES_IN_TESTS"
}

case "$1" in
  # cargo.sh --version <toolchain-name>
  --version)
    [[ $# -eq 2 ]] || print-usage-and-exit
    lookup-version "$2"
    ;;
  # cargo.sh +all [...]
  +all)
    echo "[cargo.sh] warning: running the same command for each toolchain (msrv, stable, nightly)" >&2
    for toolchain in msrv stable nightly; do
      echo "[cargo.sh] running with toolchain: $toolchain" >&2
      $0 "+$toolchain" ${@:2}
    done
    exit 0
    ;;
  # cargo.sh +<toolchain-name> [...]
  +*)
    TOOLCHAIN="$(lookup-version ${1:1})"
    RUSTFLAGS="$(get-rustflags ${1:1}) $RUSTFLAGS" cargo "+$TOOLCHAIN" ${@:2}
    ;;
  *)
    print-usage-and-exit
    ;;
esac
