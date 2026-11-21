#!/bin/bash
# CakeML runtime probes: same compiled program, different configured heap/stack
# limits (CML_HEAP_SIZE / CML_STACK_SIZE in MiB). Sequential, timeout 60 each.
W=/tmp/oomprobe
cd "$W" || exit 1
LOG=$W/probes/out/cakeml_run.log
: > "$LOG"
run() {
  local hs=$1 ss=$2 prog=$3 n=$4
  echo "### CML_HEAP_SIZE=$hs CML_STACK_SIZE=$ss $prog $n" >> "$LOG"
  ( cd "$W" && CML_HEAP_SIZE=$hs CML_STACK_SIZE=$ss timeout 60 taskset -c 0-7 \
      /usr/bin/time -f 'EXIT=%x MAXRSS_KB=%M WALL_S=%e' "$W/probes/cakeml/$prog.cake" "$n" ) >> "$LOG" 2>&1
  echo "### shell_status=$?" >> "$LOG"; echo >> "$LOG"
}
run 16 16 heap 1000
run 16 16 heap 10000000
run 1024 16 heap 10000000
run 16 1 stack 1000
run 16 1 stack 10000000
run 16 1024 stack 10000000
echo DONE >> "$LOG"
