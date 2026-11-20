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

ROOT="$(git rev-parse --show-toplevel)"
FLAKE="$ROOT/anneal/v2"

systems=(
  aarch64-darwin
  aarch64-linux
  x86_64-darwin
  x86_64-linux
)

packages=(
  aeneas-compiled
  aeneas-download
  aeneas-metadata-files
  aeneas-unpacked
  default
  leantar
  lean-toolchain
  mathlib-cache-download
  mathlib-cache-unpacked
  omnibus-archive
  omnibus-archive-ci
  omnibus-archive-layout-check
  omnibus-tar
  rust-toolchain
)

for system in "${systems[@]}"; do
  for package in "${packages[@]}"; do
    printf 'Evaluating packages.%s.%s...\n' "$system" "$package"
    nix eval --raw "$FLAKE#packages.$system.$package.drvPath" >/dev/null
  done
done

# `test-ifd` intentionally reads metadata from the output of a derivation to
# verify that Aeneas metadata can drive downstream derivations. A fresh CI
# runner cannot evaluate that attribute under `--no-build` unless the
# intermediate derivation is already valid in the local Nix store, so this
# lightweight PR check explicitly covers the release-relevant package graph
# above and leaves `test-ifd` to explicit local/Nix testing.
