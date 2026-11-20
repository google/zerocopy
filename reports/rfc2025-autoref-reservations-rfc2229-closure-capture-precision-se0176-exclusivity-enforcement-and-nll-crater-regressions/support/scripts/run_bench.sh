#!/usr/bin/env bash
# Times `rustc --emit=metadata` (type check + borrow check, no codegen) on the synthetic crate.
# For each configuration: 5 runs; records wall seconds and max RSS (KiB) from /usr/bin/time,
# and for nightly the `MIR_checking` and `type_check_crate` rows of -Ztime-passes.
set -u
SRC=/tmp/work/bench/synth.rs
OUT=/tmp/work/bench/results.tsv
T=$(mktemp -d /tmp/out); trap 'rm -rf "$T"' EXIT
: > "$OUT"
for cfg in "nightly-default-e2021:rustc --edition 2021" \
           "nightly-polonius-off-e2021:rustc -Zpolonius=off --edition 2021" \
           "nightly-default-e2018:rustc --edition 2018" \
           "nightly-polonius-off-e2018:rustc -Zpolonius=off --edition 2018"; do
  name=${cfg%%:*}; cmd=${cfg#*:}
  for i in 1 2 3 4 5; do
    /usr/bin/time -f "%e %M" -o "$T/time" $cmd -Ztime-passes --crate-type lib --emit=metadata -o "$T/x.rmeta" "$SRC" > "$T/tp" 2>&1
    read wall rss < "$T/time"
    bc=$(grep -E 'time: *[0-9.]+;.*MIR_checking' "$T/tp" | head -1 | sed -E 's/.*time: *([0-9.]+);.*/\1/')
    tc=$(grep -E 'time: *[0-9.]+;.*type_check_crate' "$T/tp" | head -1 | sed -E 's/.*time: *([0-9.]+);.*/\1/')
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$i" "$wall" "$rss" "${bc:-NA}" "${tc:-NA}" >> "$OUT"
  done
done
for i in 1 2 3 4 5; do
  /usr/bin/time -f "%e %M" -o "$T/time" rustup run 1.100.0 rustc --edition 2021 --crate-type lib --emit=metadata -o "$T/x.rmeta" "$SRC" > /dev/null 2>&1
  read wall rss < "$T/time"
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "stable-1.100.0-e2021" "$i" "$wall" "$rss" "NA" "NA" >> "$OUT"
done
cat "$OUT"
