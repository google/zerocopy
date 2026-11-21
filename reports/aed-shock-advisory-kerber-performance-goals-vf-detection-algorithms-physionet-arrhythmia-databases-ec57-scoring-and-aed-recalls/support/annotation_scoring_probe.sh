#!/bin/sh
# Execution probe of the WFDB Software Package's EC38/EC57 comparators
# (bxb, epicmp, sumstats) on synthetic annotation timelines.
#
# Requires: WFDB_BIN pointing at a directory containing wrann, bxb, epicmp,
# sumstats built from bemoody/wfdb at de6b1d3981d69060e6a4d1b4e86375fb0d3ed2d1
# (see build_wfdb.sh), and python3.
#
# Usage: WFDB_BIN=/tmp/aed-probe/wfdb-10.7.0/app WORK=/tmp/aed-probe/run sh annotation_scoring_probe.sh
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
: "${WORK:=/tmp/aed-probe/run}"
: "${WFDB_BIN:?set WFDB_BIN to the directory holding wrann/bxb/epicmp/sumstats}"
rm -rf "$WORK"; mkdir -p "$WORK"; cd "$WORK"
export WFDB=.
python3 "$HERE/make_annotations.py" .
for rec in win vfx lrn agA agB epi; do
  for ann in atr tst; do
    "$WFDB_BIN/wrann" -r $rec -a $ann < $rec.$ann.txt
  done
done

echo "=== P1 matching window (record win, 360 Hz, offsets 0,20,35,36,53,54,55,-53,-54,-55 samples)"
"$WFDB_BIN/bxb" -r win -a atr tst -v 2>&1
echo "=== P1b same, nonstandard window -w 0.1 (36 samples)"
"$WFDB_BIN/bxb" -r win -a atr tst -w 0.1 2>&1 | sed -n '1,30p'

echo "=== P2 beats inside reference VF (record vfx)"
"$WFDB_BIN/bxb" -r vfx -a atr tst 2>&1

echo "=== P3 learning period (record lrn; test misses every beat before 300 s)"
"$WFDB_BIN/bxb" -r lrn -a atr tst 2>&1 | grep -E "QRS sensitivity|QRS positive|^ N \|"
echo "--- P3b same record with -f 0 (nonstandard: include learning period)"
"$WFDB_BIN/bxb" -r lrn -a atr tst -f 0 2>&1 | grep -E "warning|QRS sensitivity|QRS positive|^ N \|"

echo "=== P4 gross vs average (records agA, agB) via bxb -l and sumstats"
rm -f bxb.out sd.out
"$WFDB_BIN/bxb" -r agA -a atr tst -l bxb.out sd.out 2>&1
"$WFDB_BIN/bxb" -r agB -a atr tst -l bxb.out sd.out 2>&1
"$WFDB_BIN/sumstats" bxb.out

echo "=== P5 VF episode scoring (record epi)"
"$WFDB_BIN/epicmp" -r epi -a atr tst -V - 2>&1
echo "--- P5b with -I 3 (exclude episodes shorter than 3 s from all statistics; nonstandard)"
"$WFDB_BIN/epicmp" -r epi -a atr tst -V - -I 3 2>&1
