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
cd "$(dirname "$0")/.."

# Check that both package archives contain unmodified copies of every license.
# Excluding the lockfile permits packaging before a new derive version is
# available from the registry.
./cargo.sh +stable package --allow-dirty --no-verify \
  --exclude-lockfile --registry crates-io \
  --package zerocopy --package zerocopy-derive
metadata=$(./cargo.sh +stable metadata --no-deps --format-version 1)

target_dir=$(jq -r '.target_directory' <<< "$metadata")
for crate in zerocopy zerocopy-derive; do
  version=$(jq -r --arg crate "$crate" \
    '.packages[] | select(.name == $crate) | .version' <<< "$metadata")
  archive="$target_dir/package/$crate-$version.crate"

  for license in LICENSE-APACHE LICENSE-BSD LICENSE-MIT; do
    tar -xOzf "$archive" "$crate-$version/$license" | cmp - "../$license"
  done
done
