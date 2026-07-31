#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Run the cargo-zerocopy implementation from the trusted workflow checkout
# while resolving toolchain metadata and package source from another checkout.
# release.yml uses this for historical releases: old main is trusted source,
# but it may predate the current release tooling and must not supply an
# executable which receives the crates.io credential.

set -euo pipefail

usage() {
  echo "usage: $0 [--prebuilt] --source-root ZEROCOPY_DIR CARGO_ARGS..." >&2
  exit 2
}

prebuilt=false
source_root=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --prebuilt)
      prebuilt=true
      shift
      ;;
    --source-root)
      [ "$#" -ge 2 ] || usage
      source_root="$2"
      shift 2
      ;;
    *)
      break
      ;;
  esac
done

[ -n "$source_root" ] || usage
[ "$#" -gt 0 ] || usage
source_root="$(cd "$source_root" && pwd)"
repo_root="$(cd "$(dirname "$0")/.." && pwd)"
driver="$repo_root/tools/target/debug/cargo-zerocopy"

if [ "$prebuilt" = false ]; then
  # This build can execute dependency build scripts. Remove every exported
  # token-like variable rather than maintaining a list which can drift as
  # GitHub or a registry adds credentials. The trusted driver is built before
  # release.yml authenticates, and this scrub keeps other callers safe too.
  clean_environment=(
    env -u RUSTFLAGS -u CARGO_TARGET_DIR -u CARGO_BUILD_TARGET
  )
  while IFS= read -r variable; do
    case "${variable^^}" in
      *TOKEN*) clean_environment+=(-u "$variable") ;;
    esac
  done < <(compgen -e)
  (
    cd "$repo_root"
    "${clean_environment[@]}" cargo +stable build --locked \
      --manifest-path tools/Cargo.toml \
      --package cargo-zerocopy \
      --quiet
  )
elif [ ! -x "$driver" ]; then
  echo "$0: trusted Cargo driver was not built before authentication" >&2
  exit 1
fi

# cargo-zerocopy reads Cargo.toml from its working directory. Running the
# trusted binary here preserves the historical source's pinned toolchain and
# workspace resolution without executing scripts from that source checkout.
cd "$source_root"
exec "$driver" "$@"
