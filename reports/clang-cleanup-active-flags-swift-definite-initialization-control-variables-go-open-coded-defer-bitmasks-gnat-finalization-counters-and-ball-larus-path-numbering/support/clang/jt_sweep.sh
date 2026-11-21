#!/bin/bash
# Sweep LLVM's jump-threading duplication threshold and record whether the
# re-test of the conditional-cleanup flag survives in t_cond / t_two.
# Usage: bash jt_sweep.sh <clang++> <workdir>
set -eu
CXX=$1; WD=$2
mkdir -p "$WD/out"
jcc() { objdump -d --no-show-raw-insn "$1" | awk "/<$2>:/,/^\$/" | grep -cE '\sj(e|ne|a|b|g|l|s|ns|ae|be|ge|le)\s' || true; }
sz() { nm -S "$1" | awk -v s="$2" '$4==s {print strtonum("0x"$2)}'; }
printf 'eh\tjt_threshold\tt_cond_jcc\tt_cond_bytes\tt_two_jcc\tt_two_bytes\n'
for eh in -fno-exceptions -fexceptions; do
  for t in 0 3 4 5 6 50 1000; do
    o="$WD/out/jt_${eh}_${t}.o"
    "$CXX" -std=c++17 -O2 "$eh" -mllvm -jump-threading-threshold=$t -c -o "$o" "$WD/cond_cleanup.cpp"
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$eh" "$t" "$(jcc "$o" _Z6t_condbi)" "$(sz "$o" _Z6t_condbi)" "$(jcc "$o" _Z5t_twobbi)" "$(sz "$o" _Z5t_twobbi)"
  done
done
