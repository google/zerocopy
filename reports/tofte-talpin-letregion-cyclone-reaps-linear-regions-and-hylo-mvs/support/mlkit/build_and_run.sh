#!/bin/bash
# Reproduces the MLKit peak-RSS probes. Requires MLKit v4.7.26 (mlkit-bin-dist-linux.tgz)
# with an mlb-path-map pointing at its lib/mlkit; set MLKIT to the mlkit binary.
# IMPORTANT: build every configuration in its own fresh directory. MLKit's
# separate-compilation cache (MLB/RI) is shared by "-no_gc" builds with and without
# --disable_atbot_analysis, and a rebuild in the same directory was observed to
# reuse objects compiled under the other setting.
set -e
MLKIT=${MLKIT:-mlkit}
declare -A CFG=( [ri]="-no_gc -no_par" [rinoatbot]="-no_gc -no_par --disable_atbot_analysis" [rigc]="-gc" [gconly]="-gc -no_ri" )
here=$(cd "$(dirname "$0")" && pwd)
work=${WORK:-/tmp/mlkit_region_probes}
for p in tailreal tailpair tailstr itermap itermap2 itercopy itercopy2 queue queue2 queue2k closure; do
  for c in ri rinoatbot rigc gconly; do
    d=$work/$c/$p; mkdir -p $d; cp $here/$p.sml $d/
    (cd $d && $MLKIT ${CFG[$c]} -o $p $p.sml > build.log 2>&1)
  done
done
run() { /usr/bin/time -f "$1 $2 n=$3 maxrss_kb=%M wall_s=%e" $work/$2/$1/$1 $3 > /dev/null; }
for c in ri rinoatbot rigc gconly; do
  for p in tailreal tailpair tailstr queue2 queue2k closure; do for n in 1000000 4000000 16000000; do run $p $c $n; done; done
  for n in 1000000 4000000; do run queue $c $n; done   # queue under gconly is quadratic in time
  for p in itermap itermap2 itercopy itercopy2; do for n in 250 1000 4000; do run $p $c $n; done; done
done
# Storage-mode evidence: count __reset_region call sites in the user object.
for p in itermap itermap2 tailpair; do echo "$p ri: $(objdump -dr $work/ri/$p/MLB/RI/$p.sml.o | grep -c __reset_region) reset sites"; done
