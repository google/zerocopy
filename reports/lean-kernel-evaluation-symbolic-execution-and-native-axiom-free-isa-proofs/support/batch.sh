#!/usr/bin/env bash
# Run every probe file in a directory with run.sh and summarize: file, status, wall, maxrss, axioms line.
DIR="$1"
SUM="$DIR/SUMMARY.tsv"
echo -e "file\tstatus\twall\tmaxrss_kb\taxioms_or_error" > "$SUM"
for f in "$DIR"/*.lean; do
  "$(dirname "$0")/run.sh" "$f" > /dev/null 2>&1
  o="${f%.lean}.out"
  st=$(grep -o 'Exit status: [0-9]*' "$o" | awk '{print $3}')
  wall=$(grep 'Elapsed' "$o" | awk '{print $NF}')
  rss=$(grep 'Maximum resident' "$o" | awk '{print $NF}')
  ax=$(grep -m1 "depends on axioms\|does not depend" "$o" | tr '\t' ' ')
  err=$(grep -m1 -o "error: .*" "$o" | cut -c1-120)
  echo -e "$(basename "$f")\t$st\t$wall\t$rss\t${ax} ${err}" >> "$SUM"
done
column -t -s $'\t' "$SUM"
