#!/bin/bash
# Usage: measure.sh N mode-flag...  ; prints wall seconds of MIR_checking (includes borrowck) from -Ztime-passes and peak RSS of rustc
N=$1; shift
HERE=$(cd "$(dirname "$0")" && pwd); mkdir -p "${WORK:-/tmp/joins}"
python3 "$HERE/gen_joins.py" $N > ${WORK:-/tmp/joins}/joins_$N.rs
for mode in "$@"; do
  flag=""; [ "$mode" != "default" ] && flag="-Zpolonius=$mode"
  tmp=$(mktemp -d)
  /usr/bin/time -f "%M %e" -o $tmp/time rustc +nightly-2026-11-12 --edition 2021 --crate-type lib --emit=metadata -o $tmp/o.rmeta -Ztime-passes $flag ${WORK:-/tmp/joins}/joins_$N.rs > $tmp/tp 2>&1
  rc=$?
  bc=$(grep -E 'MIR_checking$' $tmp/tp | head -1 | sed -E 's/time: *([0-9.]+).*/\1/')
  read rss wall < $tmp/time
  echo -e "$N\t$mode\trc=$rc\tmir_checking_s=$bc\twall_s=$wall\tpeak_rss_kb=$rss"
  rm -rf $tmp
done
