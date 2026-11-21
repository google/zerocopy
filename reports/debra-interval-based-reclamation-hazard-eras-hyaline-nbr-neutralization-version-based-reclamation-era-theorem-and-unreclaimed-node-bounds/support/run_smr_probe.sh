#!/usr/bin/env bash
# Stalled-thread probe for the kaist-cp/smr-benchmark harness (pinned revision).
# Usage: run_smr_probe.sh <path-to-target/release> <out-dir>
# Each line of output is the harness's own summary line:
#   ops/s, peak mem (jemalloc stats.allocated), avg_mem, peak garb, avg garb.
# "-n 3" makes the harness's auxiliary thread pin once and never repin
# (a stalled reader); "-n 0" pins and unpins immediately. The flag is
# implemented only for the EBR and PEBR drivers.
set -u
BIN="$1"; OUT="$2"; mkdir -p "$OUT"
DS=hash-map; T=32; G=0; R=100000
run() { # name args...
  local name="$1"; shift
  echo "### $name $*" | tee -a "$OUT/log.txt"
  "$BIN/$name" -d $DS -t $T -g $G -r $R "$@" -o "$OUT/$name.csv" 2>&1 | grep -E "ops/s|threads" | tee -a "$OUT/log.txt"
}
for rep in 1 2 3; do
  for n in 0 3; do
    run ebr  -n $n -i 10
    run pebr -n $n -i 10
  done
done
for n in 1 2; do run ebr -n $n -i 10; run pebr -n $n -i 10; done
for i in 5 20; do run ebr -n 3 -i $i; run pebr -n 3 -i $i; done
run nr -i 10
for s in hp hp-pp nbr hp-brcu vbr; do run $s -i 10; done
