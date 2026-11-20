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

if [ "$#" -ne 1 ] || [[ "$1" != /* ]] || [ ! -d "$1" ]; then
  echo "usage: bash ci/probe_toolchain.sh /absolute/installation/root" >&2
  exit 2
fi
install_root="$(cd "$1" && pwd -P)"
probe="$(mktemp -d "${TMPDIR:-/tmp}/anneal-toolchain-probe.XXXXXX")"

finish() {
  status=$?
  if [ "$status" -eq 0 ]; then
    rm -rf "$probe"
  else
    # A closed log stream must not replace the probe's failure status.
    (printf 'Toolchain probe evidence retained at %s\n' "$probe" >&2) || :
  fi
  exit "$status"
}
trap finish EXIT

# Each tool runs without ambient compiler settings. Keep its raw streams and
# status before relaying output to the workflow log. Preserve a failing tool
# status even if reporting fails; reporting failure must also fail the probe
# when the tool succeeded.
run_tool() {
  local name="$1" status=0 reporting_status=0
  shift
  "$@" > "$probe/$name.stdout" 2> "$probe/$name.stderr" || status=$?
  printf '%s\n' "$status" > "$probe/$name.status" || reporting_status=$?
  cat "$probe/$name.stdout" || reporting_status=$?
  cat "$probe/$name.stderr" >&2 || reporting_status=$?
  if [ "$status" -ne 0 ]; then
    return "$status"
  fi
  return "$reporting_status"
}

cd "$probe"
expected_rust='1.98.0-nightly (f8a08b688 2026-05-30)'
run_tool rustc-version env -i "$install_root/rust/bin/rustc" --version
grep -Fxq "rustc $expected_rust" rustc-version.stdout
run_tool rustdoc-version env -i "$install_root/rust/bin/rustdoc" --version
grep -Fxq "rustdoc $expected_rust" rustdoc-version.stdout
run_tool lean-version env -i "$install_root/lean/bin/lean" --version
grep -Fq 'Lean (version 4.34.1,' lean-version.stdout
run_tool cargo-version env -i "$install_root/rust/bin/cargo" --version
grep -Eq '^cargo [0-9]' cargo-version.stdout
run_tool driver-version env -i "$install_root/bin/anneal-rustc-capture" --version
grep -Eq '^anneal-rustc-capture [0-9]' driver-version.stdout

# Version banners establish identity but do not load every backend needed by
# users. Compile, generate documentation, and run the capture callback from
# this extracted installation before accepting the archive.
printf '%s\n' 'example (n : Nat) : n = n := rfl' > Small.lean
run_tool lean-file env -i "$install_root/lean/bin/lean" Small.lean
printf '%s\n' '//! Installed documentation probe.' \
  'pub fn identity(n: u32) -> u32 { n }' > small.rs
run_tool rustc-metadata env -i "$install_root/rust/bin/rustc" \
  --sysroot "$install_root/rust" --edition=2024 --crate-type=lib \
  --emit=metadata small.rs -o rustc.rmeta
test -s rustc.rmeta
run_tool driver-callback env -i "$install_root/bin/anneal-rustc-capture" \
  --sysroot "$install_root/rust" --edition=2024 --crate-type=lib \
  --emit=metadata small.rs -o driver.rmeta
test -s driver.rmeta
test ! -s driver-callback.stdout
grep -Fxq 'note: anneal-rustc-capture: compiler analysis callback reached; verification not performed' \
  driver-callback.stderr

run_tool rustdoc-html env -i "$install_root/rust/bin/rustdoc" \
  --sysroot "$install_root/rust" --edition=2024 --crate-type=lib \
  --crate-name=toolchain_probe --out-dir "$probe/documentation" small.rs
grep -Fq 'Installed documentation probe.' documentation/toolchain_probe/index.html
test -s documentation/toolchain_probe/fn.identity.html

# An explicit workspace boundary prevents Cargo from inheriting an ancestor
# workspace. The empty Cargo home and offline mode make the bundled tools
# satisfy this dependency-free check without host caches or downloads.
mkdir -p fixture/src cargo-home
printf '%s\n' '[package]' 'name = "toolchain_probe"' 'version = "0.0.0"' \
  'edition = "2024"' '' '[workspace]' > fixture/Cargo.toml
cp small.rs fixture/src/lib.rs
run_tool cargo-check env -i \
  RUSTC="$install_root/rust/bin/rustc" \
  RUSTDOC="$install_root/rust/bin/rustdoc" CARGO_HOME="$probe/cargo-home" \
  "$install_root/rust/bin/cargo" check --offline \
  --manifest-path "$probe/fixture/Cargo.toml" --target-dir "$probe/target"
for metadata in "$probe"/target/debug/deps/libtoolchain_probe-*.rmeta; do
  test -s "$metadata"
done
