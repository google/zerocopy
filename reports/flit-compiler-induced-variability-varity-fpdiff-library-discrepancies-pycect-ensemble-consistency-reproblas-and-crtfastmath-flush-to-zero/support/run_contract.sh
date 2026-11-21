#!/bin/sh
# Builds contract.c under several GCC settings; prints FMA instruction counts in f() and g() and the results.
set -u
D=$(cd "$(dirname "$0")" && pwd)
W=${WORK:-/tmp/fp_probe_work}; mkdir -p "$W"
run(){ label="$1"; shift; gcc "$@" "$D/contract.c" -lm -o "$W/contract.bin" 2>"$W/cc.err"
  w=$(grep -c -i warning "$W/cc.err")
  nf=$(objdump -d --no-show-raw-insn "$W/contract.bin" | awk '/<f>:/,/ret/' | grep -c vfmadd)
  ng=$(objdump -d --no-show-raw-insn "$W/contract.bin" | awk '/<g>:/,/ret/' | grep -c vfmadd)
  echo "$label | flags: $* | vfmadd in f=$nf g=$ng | warnings=$w | $("$W/contract.bin")"
  [ "$w" -gt 0 ] && grep -i warning "$W/cc.err" | sed "s|$D/||; s/^/    /" | head -2; return 0; }
gcc --version | head -1
run A -O2
run B -O2 -march=haswell
run C -O2 -march=haswell -std=c17
run D -O2 -march=haswell -std=gnu17
run E -O2 -march=haswell -ffp-contract=on
run F -O2 -march=haswell -ffp-contract=off
run G -O2 -march=haswell -DUSE_PRAGMA_OFF -Wall
run H -O2 -march=haswell -std=c17 -ffp-contract=fast
run I -O0 -march=haswell
run J -O2 -march=haswell -ffast-math
run K -O2 -march=haswell -std=c17 -ffast-math
