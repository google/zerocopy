#!/bin/sh
# Usage: run_spin.sh <path-to-spin-binary> <outdir>
# Builds and runs each model with and without partial-order reduction.
set -u
SPIN="$1"; OUT="$2"; HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"; cp "$HERE"/*.pml "$OUT"/; cd "$OUT"
run() { # name model extra-spin-defs extra-cc-defs pan-args
  name=$1; model=$2; sdefs=$3; cdefs=$4; pargs=$5
  rm -f pan pan.* ; "$SPIN" $sdefs -a "$model" > "$name.spin.txt" 2>&1
  gcc -O2 -w $cdefs -o pan pan.c > "$name.cc.txt" 2>&1
  /usr/bin/time -f "wall_s=%e maxrss_kb=%M" ./pan $pargs > "$name.pan.txt" 2> "$name.time.txt"
  echo "== $name"; grep -E "errors:|states, stored|transitions \(=|total actual memory|Partial Order Reduction|warning|elapsed time" "$name.pan.txt"; cat "$name.time.txt"
}
for n in 2 3 4 5 6; do
  run indep_N${n}_K3_por    indep.pml "-DN=$n -DK=3" "-DSAFETY" "-m100000"
  run indep_N${n}_K3_nored  indep.pml "-DN=$n -DK=3" "-DSAFETY -DNOREDUCE" "-m100000"
done
run ignoring_por   ignoring.pml "" "-DSAFETY" ""
run ignoring_nored ignoring.pml "" "-DSAFETY -DNOREDUCE" ""
run nexttime_por   nexttime.pml "" "" "-a"
run nexttime_nored nexttime.pml "" "-DNOREDUCE" "-a"
