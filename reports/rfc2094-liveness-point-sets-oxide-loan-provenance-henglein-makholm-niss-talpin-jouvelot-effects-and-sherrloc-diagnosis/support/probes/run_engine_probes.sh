#!/bin/bash
# Dump rustc's legacy Polonius input facts for each probe and run the three
# polonius-engine variants on them with the polonius-driver in ../polonius-driver.
# Usage: run_engine_probes.sh <probe-dir> <facts-dir> <polonius-driver-binary>
set -eu
D=$1; FACTS=$2; DRIVER=$3
for f in pc2_cond_flow pc3_cross_fn pc3_loop subset_after_join join_two_owners kill_on_reassign alpha_limit_loop; do
  out="$FACTS/$f"; rm -rf "$out"; mkdir -p "$out"
  rustc +nightly-2026-11-12 --edition 2021 --crate-type lib --emit=metadata -o "$out/o.rmeta" \
    -Zpolonius=legacy -Znll-facts -Znll-facts-dir="$out" "$D/$f.rs" >/dev/null 2>&1 || true
  for fn in $(ls "$out" | grep -v rmeta); do
    for a in Naive DatafrogOpt LocationInsensitive; do
      "$DRIVER" "$a" "$out/$fn" 1 | sed -E 's/ median_s=[0-9.]+//'
    done
  done
done
