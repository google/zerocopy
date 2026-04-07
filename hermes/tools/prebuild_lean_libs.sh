#!/bin/bash
set -ex

# Pre-builds the Mathlib cache and Aeneas standard library for Hermes integration 
# tests without relying on Cargo or the Rust crate logic. This allows us to cache 
# Mathlib and Aeneas in Docker strictly before the `src/` and `tests/` directories 
# are ever copied in, preventing source code changes from busting the heavy Mathlib compilation layer.

CACHE_ROOT="/cache/hermes_target/shared_cache"
AENEAS_DIR="$CACHE_ROOT/aeneas"

mkdir -p "$AENEAS_DIR"
tar -xzf testdata/setup/aeneas-linux-x86_64.tar.gz -C "$AENEAS_DIR"

# Determine permissions so Lake has writes locally to output objects
chmod -R a+rwX "$AENEAS_DIR"

cd "$AENEAS_DIR/backends/lean"

# Fetch pre-compiled Mathlib artifacts from cloud
lake exe cache get

# Compile the Aeneas Standard Library natively against the Mathlib cache.
# (elan will automatically download the correct Lean 4 toolchain version)
lake build

# Integration tests enforce that the cache is strictly read-only to prevent
# accidental modifications by test targets.
chmod -R a-w "$AENEAS_DIR"

# Write cache completion marker for `tests/integration.rs`
touch "$CACHE_ROOT/.complete"

# Ensure global writability for host-mounted uids
chmod -R a+rwX /cache
