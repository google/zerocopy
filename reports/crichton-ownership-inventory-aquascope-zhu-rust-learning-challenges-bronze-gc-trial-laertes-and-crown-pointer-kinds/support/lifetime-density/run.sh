#!/bin/bash
# Reproduce the lifetime-annotation density table.
# Usage: run.sh <root>   where <root>/<owner>__<repo> is a checkout of each pinned
# revision listed in pins.tsv (for example extracted from
# `gh api repos/<owner>/<repo>/tarball/<revision>`).
# Build first: (cd "$(dirname "$0")" && cargo build --release)
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$1
BIN=${BIN:-$HERE/target/release/lifetime-density}
# Canary: every expected field must match.
mkdir -p "$HERE/.canary" && cp "$HERE/canary.rs" "$HERE/.canary/" && "$BIN" canary "$HERE/.canary" | tr ',' '\n' | sed 's/^ *//; s/.*Stats { //; s/ }$//' > "$HERE/.canary/actual.txt"
while read -r k v; do a=$(grep "^$k " "$HERE/.canary/actual.txt" | awk '{print $2}'); [ "$a" = "$v" ] || { echo "canary mismatch: $k expected $v got $a"; exit 1; }; done < "$HERE/expected.txt"
tail -n +2 "$HERE/pins.tsv" | while IFS=$'\t' read -r repo rev dirs; do
  dir="$ROOT/${repo//\//__}"
  label=$(basename "$repo"); case $repo in clap-rs/clap) label=clap_builder;; servo/rust-smallvec) label=smallvec;; esac
  args=(); for d in $dirs; do args+=("$dir/$d"); done
  "$BIN" "$label" "${args[@]}"
done > "$HERE/raw_stats.rerun.txt"
python3 "$HERE/summarize.py" "$HERE/raw_stats.rerun.txt" "$HERE/density_table.rerun.tsv"
diff <(cut -f2- "$HERE/raw_stats.txt") <(cut -f2- "$HERE/raw_stats.rerun.txt") && echo "density table reproduced"
