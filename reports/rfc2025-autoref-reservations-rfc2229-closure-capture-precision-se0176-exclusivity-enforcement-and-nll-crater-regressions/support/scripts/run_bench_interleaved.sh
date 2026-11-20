#!/usr/bin/env bash
# Interleaved variant of run_bench.sh: 9 rounds, each round runs every configuration once,
# so slow drifts in host load affect all configurations alike.
set -u
SRC=/tmp/work/bench/synth.rs
OUT=/tmp/work/bench/results_interleaved.tsv
T=$(mktemp -d /tmp/out); trap 'rm -rf "$T"' EXIT
: > "$OUT"
CFGS=("nightly-default-e2021:rustc --edition 2021"
      "nightly-polonius-off-e2021:rustc -Zpolonius=off --edition 2021"
      "nightly-default-e2018:rustc --edition 2018"
      "nightly-polonius-off-e2018:rustc -Zpolonius=off --edition 2018")
for i in $(seq 1 9); do
  for cfg in "${CFGS[@]}"; do
    name=${cfg%%:*}; cmd=${cfg#*:}
    /usr/bin/time -f "%e %M" -o "$T/time" $cmd -Ztime-passes --crate-type lib --emit=metadata -o "$T/x.rmeta" "$SRC" > "$T/tp" 2>&1
    read wall rss < "$T/time"
    bc=$(grep -E 'time: *[0-9.]+;.*MIR_checking' "$T/tp" | head -1 | sed -E 's/.*time: *([0-9.]+);.*/\1/')
    tc=$(grep -E 'time: *[0-9.]+;.*type_check_crate' "$T/tp" | head -1 | sed -E 's/.*time: *([0-9.]+);.*/\1/')
    load=$(cut -d' ' -f1 /proc/loadavg)
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$i" "$wall" "$rss" "${bc:-NA}" "${tc:-NA}" "$load" >> "$OUT"
  done
done
cat "$OUT"
