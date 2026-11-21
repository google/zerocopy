#!/usr/bin/env bash
# DoubleLink queue probe for the kaist-cp/smr-benchmark harness (pinned revision).
# Usage: run_doublelink_probe.sh <path-to-target/release> <out-dir>
# The harness prints "ops/s, peak mem, avg_mem" where memory is jemalloc
# stats.allocated (bytes) sampled by an auxiliary thread.
set -u
BIN="$1"; OUT="$2"; mkdir -p "$OUT"
T=32
run() { # manager interval
  echo "### double-link -m $1 -t $T -i $2" | tee -a "$OUT/log.txt"
  "$BIN/double-link" -m "$1" -t $T -i "$2" -o "$OUT/double-link.csv" 2>&1 | grep -E "ops/s" | tee -a "$OUT/log.txt"
}
for i in 5 10 20; do
  for m in nr ebr cdrc-ebr cdrc-ebr-flush circ-ebr hp cdrc-hp circ-hp; do
    run $m $i
  done
done
for rep in 2 3; do
  for m in ebr cdrc-ebr circ-ebr; do run $m 10; done
done
