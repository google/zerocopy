#!/bin/sh
# Usage: run_infer_c.sh <path-to-infer> <workdir>
# Runs Pulse on every C file in ./c with several --pulse-max-disjuncts values
# and prints one line per (file, bound): issue types reported and wall time.
set -u
INFER="$1"; WORK="$2"; HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$WORK"; cp "$HERE"/c/*.c "$WORK"/; cd "$WORK"
for f in *.c; do
  for d in 1 2 4 8 16 20 64 256; do
    out="out_${f%.c}_d$d"
    rm -rf "$out"
    /usr/bin/time -f "%e %M" -o time.txt "$INFER" run --pulse-only --pulse-max-disjuncts "$d" \
      -o "$out" -- clang -c "$f" > /dev/null 2>&1
    issues=$(python3 -c "import json,sys; r=json.load(open('$out/report.json')); print(','.join(sorted(i['bug_type'] for i in r)) or 'none')" 2>/dev/null || echo ERROR)
    dropped=$(grep -h -o -E "pulse_disjuncts_dropped= [0-9]+" "$out/logs" 2>/dev/null | tail -1 | awk '{print $2}')
    echo "file=$f max_disjuncts=$d issues=$issues disjuncts_dropped=${dropped:-?} wall_s_maxrss_kb=$(cat time.txt)"
  done
done
