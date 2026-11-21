#!/bin/bash
# GCC trace formation (-ftracer) on generated graphs. Usage: bash tracer_probe.sh <gcc> <dir-with-generated-.c>
# Prints static body() call sites (tail copies x t) and .text bytes.
set -eu
GCC=$1; D=$2
for f in g_indep_3_1 g_indep_3_4 g_indep_6_1 g_nested_4_4; do
  for opts in "-O2" "-O2 -ftracer" "-O2 -ftracer --param tracer-max-code-growth=1000 --param tracer-min-branch-probability=0 --param tracer-dynamic-coverage=100"; do
    o=$(mktemp --suffix=.o); $GCC $opts -c -o "$o" "$D/$f.c"
    echo "$f [$opts] body_sites=$(objdump -d -r "$o" | grep -c 'R_X86_64_PLT32.*body') bytes=$(nm -S "$o" | awk '$3=="T"{print strtonum("0x"$2)}')"
    rm -f "$o"
  done
done
