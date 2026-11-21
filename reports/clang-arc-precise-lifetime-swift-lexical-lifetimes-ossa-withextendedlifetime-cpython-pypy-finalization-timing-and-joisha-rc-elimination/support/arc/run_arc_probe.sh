#!/bin/sh
# Reproduce the ARC release-timing observations. Requires clang (tested with
# Debian clang 19.1.7, x86_64 Linux). Run in an empty scratch directory that
# contains arc_probe.m, arc_callee.m, arc_interior.m, arc_stub_runtime.c, d_main.c.
set -e
CC=${CC:-clang-19}
ARC="-fobjc-arc -fobjc-runtime=gnustep-2.0"
$CC -O0 -c arc_stub_runtime.c -o stub.o
$CC -O0 -DARC_STUB_NO_MAIN -c arc_stub_runtime.c -o stub_nomain.o
$CC -O0 -c d_main.c -o d_main.o
for O in O0 O1 O2 O3 Os; do
  $CC $ARC -$O -c arc_probe.m -o arc_probe.$O.o
  $CC arc_probe.$O.o stub.o -o probe.$O
  echo "=== arc_probe -$O"; ./probe.$O
done
for O in O0 O2; do
  $CC $ARC -fno-inline -$O -c arc_callee.m -o arc_callee.$O.o
  $CC arc_callee.$O.o stub_nomain.o d_main.o -o probeD.$O
  echo "=== arc_callee -$O"; ./probeD.$O
  $CC $ARC -$O -S -emit-llvm arc_probe.m -o arc_probe.$O.ll
  $CC $ARC -$O -S -emit-llvm arc_interior.m -o arc_interior.$O.ll
  $CC $ARC -fno-inline -$O -S -emit-llvm arc_callee.m -o arc_callee.$O.ll
done
echo "=== ARC runtime calls in -O2 IR (function: call)"
for f in arc_probe.O2.ll arc_interior.O2.ll arc_callee.O2.ll; do
  awk '/^define/{fn=$0; sub(/\(.*/,"",fn); sub(/.*@/,"",fn)} /llvm\.objc\.(retain|release|retainAutorelease)\(/{ if ($0 !~ /^declare/) { line=$0; gsub(/  +/," ",line); print fn": "line } }' $f
done
