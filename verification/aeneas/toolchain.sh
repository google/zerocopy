# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Runtime versions come from Anneal's archive, checked against its flake lock.
# Cache validation uses only Python and the installed tools; Nix is cold-setup only.
_aeneas_repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
_aeneas_tools=${AENEAS_TOOLCHAIN_DIR:-"$_aeneas_repo/target/aeneas/toolchain"}
_aeneas_values=$(python3 -B "$_aeneas_repo/verification/aeneas/toolchain.py" shell "$_aeneas_tools") || return 1
eval "$_aeneas_values"
export PATH="$_aeneas_tools/rust/bin:$_aeneas_tools/lean/bin:$PATH"
export LEAN_SYSROOT="$_aeneas_tools/lean"
export LD_LIBRARY_PATH="$_aeneas_tools/rust/lib:$_aeneas_tools/lean/lib:$_aeneas_tools/lean/lib/lean${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export DYLD_LIBRARY_PATH="$_aeneas_tools/rust/lib:$_aeneas_tools/lean/lib:$_aeneas_tools/lean/lib/lean${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
export CHARON_TOOLCHAIN_IS_IN_PATH=1
# Match V1's archive configuration and reuse its read-only, mtime-based caches.
# Keep CI removed only for Lake; callers retain their ordinary CI environment.
aeneas_lake() (
    unset CI
    command lake --old "$@"
)
unset _aeneas_repo _aeneas_tools _aeneas_values
