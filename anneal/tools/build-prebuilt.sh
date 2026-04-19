#!/bin/bash
# Copyright 2026 The Zerocopy Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

set -eo pipefail

# This script builds the precompiled artifacts for the Anneal toolchain.
# It downloads dependencies, pre-compiles the Lean library, and packages the
# artifact for the specified host platform.
#
# It is used in the release workflow and can also be run by developers to
# verify changes locally.

# Ensure we are in the anneal directory.
cd "$(dirname "$0")/.."

STAGING_DIR="dist_staging"
if [ -d "$STAGING_DIR" ]; then
    chmod -R +w "$STAGING_DIR"
fi
rm -rf "$STAGING_DIR"
mkdir -p "$STAGING_DIR"

# Extract metadata from Cargo.toml.
# We use sed to parse the TOML file. This is brittle but avoids external
# dependencies like toml-cli.
AENEAS_TAG=$(sed -n 's/^tag = "\(.*\)"/\1/p' Cargo.toml | head -n 1)
RUST_DATE="2026-02-07"
RUST_VERSION="nightly-2026-02-07"

echo "Detected Aeneas Tag: $AENEAS_TAG"
echo "Detected Rust Date: $RUST_DATE"
echo "Detected Rust Version: $RUST_VERSION"

HOST_TRIPLE="${1:-x86_64-unknown-linux-gnu}"
echo "Using Host Triple: $HOST_TRIPLE"

case "$HOST_TRIPLE" in
    "x86_64-unknown-linux-gnu") AENEAS_TARGET="linux-x86_64" ;;
    "aarch64-unknown-linux-gnu") AENEAS_TARGET="linux-aarch64" ;;
    "x86_64-apple-darwin") AENEAS_TARGET="macos-x86_64" ;;
    "aarch64-apple-darwin") AENEAS_TARGET="macos-aarch64" ;;
    *) echo "Unsupported host triple: $HOST_TRIPLE"; exit 1 ;;
esac

# Download Aeneas prebuilts.
# We download from the upstream repository to repackage them.
AENEAS_URL="https://github.com/AeneasVerif/aeneas/releases/download/${AENEAS_TAG}/aeneas-${AENEAS_TARGET}.tar.gz"
echo "Downloading Aeneas from $AENEAS_URL..."
curl -L "$AENEAS_URL" -o "$STAGING_DIR/aeneas.tar.gz"

# Download Rust toolchain components.
# We download specific nightly components required by Charon.
download_rust_component() {
    local component=$1
    local url="https://static.rust-lang.org/dist/${RUST_DATE}/${component}-nightly-${HOST_TRIPLE}.tar.gz"
    echo "Downloading $component from $url..."
    curl -L "$url" -o "$STAGING_DIR/${component}.tar.gz"
}

download_rust_component "rustc"
download_rust_component "rust-std"
download_rust_component "rustc-dev"
download_rust_component "llvm-tools"
download_rust_component "miri"

# We also need rust-src which is platform independent.
RUST_SRC_URL="https://static.rust-lang.org/dist/${RUST_DATE}/rust-src-nightly.tar.gz"
echo "Downloading rust-src from $RUST_SRC_URL..."
curl -L "$RUST_SRC_URL" -o "$STAGING_DIR/rust-src.tar.gz"

# Unpack everything.
echo "Unpacking artifacts..."
cd "$STAGING_DIR"
tar -xzf aeneas.tar.gz

mkdir -p rust
tar -xzf rustc.tar.gz -C rust --strip-components=2
tar -xzf rust-std.tar.gz -C rust --strip-components=2
tar -xzf rustc-dev.tar.gz -C rust --strip-components=2
tar -xzf llvm-tools.tar.gz -C rust --strip-components=2
tar -xzf miri.tar.gz -C rust --strip-components=2
tar -xzf rust-src.tar.gz -C rust --strip-components=2

# Move charon and charon-driver to rust/bin to sit alongside rustc
# This allows them to find shared libraries in ../lib relative to themselves.
mv charon charon-driver rust/bin/

# Nix preserves read-only permissions from the store, so we must make files
# writable.
chmod -R +w .
cd ..

# Pre-compile Lean Library.
# We need to make sure we use the correct Lean version and fetch Mathlib cache.
# We assume elan is installed on the system.
echo "Pre-compiling Lean library..."
cd "$STAGING_DIR/backends/lean"

# Ensure we use the correct Lean version specified by Aeneas.
LEAN_VERSION=$(cat lean-toolchain)
elan default "$LEAN_VERSION"

# Fetch pre-compiled Mathlib binaries to avoid hours of compilation.
lake exe cache get

# Force precompilation by unsetting CI environment variable.
# This ensures that shared libraries required for plugin loading are generated.
# Remove tests from AeneasMeta to avoid users compiling them
rm -f AeneasMeta/Async/Test.lean
rm -f AeneasMeta/Async/TestTactics.lean
# Remove imports of these tests from Async.lean
sed '/import AeneasMeta.Async.Test/d' AeneasMeta/Async.lean > AeneasMeta/Async.lean.tmp && mv AeneasMeta/Async.lean.tmp AeneasMeta/Async.lean

# Remove Mathlib tests to keep the artifact small
rm -rf .lake/packages/mathlib/MathlibTest

env -u CI lake build

# Generate the dependency graph
lake exe graph imports.dot --to Aeneas,Aeneas.Std.Core,Aeneas.Std.WP,Aeneas.Tactic.Solver.ScalarTac,Aeneas.Std.Scalar.Core --include-deps

# Prune Mathlib based on the graph
python3 ../../../tools/prune_mathlib.py imports.dot .lake/packages/mathlib

# Clean up the graph file
rm imports.dot

cd ../.. # Back to dist_staging

# Repackage the artifact.
echo "Repackaging artifact..."
# We remove the original archives before repackaging.
rm -f aeneas.tar.gz rustc.tar.gz rust-std.tar.gz rustc-dev.tar.gz llvm-tools.tar.gz miri.tar.gz rust-src.tar.gz
ZSTD_LEVEL="${ANNEAL_ZSTD_LEVEL:-19}"
tar -cf - * | zstd -"$ZSTD_LEVEL" > ../anneal-toolchain-${AENEAS_TARGET}.tar.zst

cd .. # Back to anneal directory
echo "Precompiled artifacts built successfully."
