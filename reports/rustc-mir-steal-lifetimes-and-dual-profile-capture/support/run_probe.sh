#!/usr/bin/env bash
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TOOLCHAIN="${RUSTUP_TOOLCHAIN:-nightly-2026-05-31}"
SYSROOT="$(rustup run "${TOOLCHAIN}" rustc --print sysroot)"
WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT

rustup run "${TOOLCHAIN}" rustc \
  --edition=2021 \
  "${SCRIPT_DIR}/probe_mir_steal_and_profiles.rs" \
  -L "${SYSROOT}/lib" \
  -C link-arg=-Wl,-rpath,"${SYSROOT}/lib" \
  -o "${WORKDIR}/probe_mir_steal_and_profiles"

(
  cd "${WORKDIR}"
  LD_LIBRARY_PATH="${SYSROOT}/lib:${LD_LIBRARY_PATH:-}" \
  SYSROOT="${SYSROOT}" \
    "${WORKDIR}/probe_mir_steal_and_profiles"
)

diff -u "${SCRIPT_DIR}/probe_results.json" "${WORKDIR}/probe_results.json"
echo "Revalidation succeeded: probe_results.json matches byte-for-byte."
