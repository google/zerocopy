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

# Usage: msrv <crate-name>
function msrv {
  cargo metadata -q --format-version 1 | jq -r ".packages[] | select(.name == \"$1\").rust_version"
}

ver_zerocopy=$(msrv zerocopy)
ver_zerocopy_derive=$(msrv zerocopy-derive)

if [[ "$ver_zerocopy" == "$ver_zerocopy_derive" ]]; then
  echo "Same MSRV ($ver_zerocopy) found for zerocopy and zerocopy-derive." | tee -a $GITHUB_STEP_SUMMARY
  exit 0
else
  echo "Different MSRVs found for zerocopy ($ver_zerocopy) and zerocopy-derive ($ver_zerocopy_derive)." \
    | tee -a $GITHUB_STEP_SUMMARY >&2
  exit 1
fi
