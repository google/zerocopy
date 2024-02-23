#!/usr/bin/env bash
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
