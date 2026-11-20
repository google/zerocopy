#!/bin/bash
# Runs every probe under five borrow-checker configurations and records accept/reject plus diagnostics.
# Usage: run_rustc_probes.sh <probe-dir> <out-dir>
set -u
# Requires rustup toolchains 1.100.0 and nightly-2026-11-12 (rustc 1.102.0-nightly 3ef0c22cd 2026-11-11).
D=$1; OUT=$2; mkdir -p "$OUT"
modes=("stable-1.100.0:+1.100.0:" "nightly-polonius-off:+nightly-2026-11-12:-Zpolonius=off" "nightly-default:+nightly-2026-11-12:" "nightly-polonius-legacy:+nightly-2026-11-12:-Zpolonius=legacy" "nightly-polonius-next:+nightly-2026-11-12:-Zpolonius=next")
printf "probe"; for m in "${modes[@]}"; do printf "\t%s" "${m%%:*}"; done; printf "\n"
for f in "$D"/*.rs; do
  b=$(basename "$f" .rs); printf "%s" "$b"
  for m in "${modes[@]}"; do
    name=${m%%:*}; rest=${m#*:}; tc=${rest%%:*}; flag=${rest#*:}
    tmp=$(mktemp -d)
    rustc $tc --edition 2021 --crate-type lib --emit=metadata -o "$tmp/out.rmeta" $flag "$f" > "$OUT/$b.$name.stderr" 2>&1
    rc=$?; rm -rf "$tmp"
    codes=$(grep -o -E '^error\[E[0-9]+\]' "$OUT/$b.$name.stderr" | sort -u | tr -d '[]' | sed 's/error//' | paste -sd, -)
    if [ $rc -eq 0 ]; then printf "\taccept"; else printf "\treject(%s)" "${codes:-other}"; fi
  done; printf "\n"
done
