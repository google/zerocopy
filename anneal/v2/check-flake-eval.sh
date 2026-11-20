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

# Evaluate all target platforms and release-relevant package derivations in a
# single Nix invocation so Nix does not reopen the repository tree and
# re-evaluate nixpkgs 56 separate times.
eval_json="$(
  nix eval --json "$FLAKE#packages" \
    --apply 'builtins.mapAttrs (_: pkgs: builtins.mapAttrs (_: pkg: pkg.drvPath) (builtins.removeAttrs pkgs ["test-ifd"]))'
)"

EVAL_JSON="$eval_json" \
EXPECTED_SYSTEMS="${systems[*]}" \
EXPECTED_PACKAGES="${packages[*]}" \
python3 -I -B - <<'PY'
import json
import os
import sys

data = json.loads(os.environ["EVAL_JSON"])
if not isinstance(data, dict):
    sys.exit(f"expected JSON object for flake packages, got {type(data).__name__}")
systems = os.environ["EXPECTED_SYSTEMS"].split()
packages = os.environ["EXPECTED_PACKAGES"].split()

for system in systems:
    sys_pkgs = data.get(system)
    if not isinstance(sys_pkgs, dict):
        sys.exit(f"missing packages.{system} in flake evaluation")
    for package in packages:
        drv = sys_pkgs.get(package)
        if (
            not isinstance(drv, str)
            or not drv.startswith("/nix/store/")
            or not drv.endswith(".drv")
        ):
            sys.exit(
                f"invalid drvPath for packages.{system}.{package}: {drv!r}"
            )
        print(f"Verified packages.{system}.{package}: {drv}")
PY

# `test-ifd` intentionally reads metadata from the output of a derivation to
# verify that Aeneas metadata can drive downstream derivations. A fresh CI
# runner cannot evaluate that attribute under `--no-build` unless the
# intermediate derivation is already valid in the local Nix store, so this
# lightweight PR check explicitly covers the release-relevant package graph
# above and leaves `test-ifd` to explicit local/Nix testing.
