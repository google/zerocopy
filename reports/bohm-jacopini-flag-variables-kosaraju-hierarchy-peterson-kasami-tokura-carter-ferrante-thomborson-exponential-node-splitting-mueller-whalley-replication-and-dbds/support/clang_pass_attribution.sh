#!/bin/bash
# Which LLVM pass duplicates the innermost owed-release tail? Usage: bash clang_pass_attribution.sh <clang> <g_indep_3_1.c>
set -eu
CC=$1; SRC=$2
for opts in "" "-mllvm -jump-threading-threshold=0" "-mllvm -simplifycfg-max-small-block-size=0" "-mllvm -jump-threading-threshold=0 -mllvm -simplifycfg-max-small-block-size=0" "-mllvm -disable-tail-duplicate -mllvm -disable-early-taildup -mllvm -tail-dup-placement=false"; do
  o=$(mktemp --suffix=.o); $CC -O2 $opts -c -o "$o" "$SRC"
  echo "[${opts:-default}] body_sites=$(objdump -d -r "$o" | grep -c 'R_X86_64_PLT32.*body') bytes=$(nm -S "$o" | awk '$3=="T"{print strtonum("0x"$2)}')"
  rm -f "$o"
done
