#!/bin/bash
# Runs the Hobbit equivalence checker on benchmark and probe programs and
# prints one summary line per run plus the checker's verdict lines.
#
# Usage: HOBBIT=/path/to/hobbit.native HOBBIT_SRC=/path/to/Hobbit-<rev> \
#        bash run_probes.sh > probe_output.txt
#
# HOBBIT_SRC is an extracted LaifsV1/Hobbit source tree (for programs/).
# Exit codes of hobbit.native (src/lts.ml:16-18): 43 = equivalent,
# 42 = inequivalent, 0 = inconclusive (bound exceeded).  124 = killed by timeout.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${HOBBIT:?set HOBBIT to the hobbit.native binary}"
: "${HOBBIT_SRC:?set HOBBIT_SRC to the Hobbit source tree}"
TIMEOUT="${TIMEOUT:-150}"

run() {   # run <label> <file> [extra hobbit args...]
  local label="$1" file="$2"; shift 2
  local out tf
  out="$(mktemp)"; tf="$(mktemp)"
  /usr/bin/time -f "%e %M" -o "$tf" timeout "$TIMEOUT" "$HOBBIT" -i "$file" "$@" >"$out" 2>&1
  local code=$?
  local verdict
  case "$code" in
    43) verdict=equivalent ;;
    42) verdict=inequivalent ;;
    0)  verdict=inconclusive ;;
    124) verdict=timeout ;;
    *)  verdict="error($code)" ;;
  esac
  # /usr/bin/time appends "Command exited with non-zero status N" before the numbers.
  local secs_rss; secs_rss="$(tail -n 1 "$tf")"
  printf '%-44s args=[%s] verdict=%s wall_s=%s maxrss_kB=%s\n' \
    "$label" "$*" "$verdict" "${secs_rss% *}" "${secs_rss#* }"
  # Everything after Hobbit's 9-line settings banner: verdict, trace, model.
  tail -n +10 "$out" | grep -v '^[[:space:]]*$' | sed 's/^/    | /' | cut -c1-300 | head -n 40
  rm -f "$out" "$tf"
}

P="$HOBBIT_SRC/programs"
echo "== Hobbit benchmark programs (default bound 6, default up-to techniques)"
for f in equiv/hector-pitts-stark.bils equiv/hector-thamsborg.bils \
         equiv/syteci-well-bracket-state.bils equiv/meyer-sieber-e1.bils \
         equiv/syteci-call-lock.bils equiv/counter.bils equiv/cell-ho.bils \
         equiv/hector-scope-extrusion-2-3.bils \
         inequiv/hector-snapback.bils inequiv/hector-stark-tricky.bils \
         inequiv/hector-scope-extrusion-1-2.bils inequiv/meyer-sieber-ineq.bils; do
  run "$f" "$P/$f"
done

echo "== Same equivalences with all up-to techniques off (-u '')"
for f in equiv/hector-pitts-stark.bils equiv/hector-thamsborg.bils \
         equiv/meyer-sieber-e1.bils equiv/syteci-call-lock.bils; do
  run "$f" "$P/$f" -u ""
  run "$f" "$P/$f" -u "" -b 12
done

echo "== Probes written for this report (support/probes/)"
for f in "$HERE"/probes/*.bils; do
  run "probes/$(basename "$f")" "$f"
done

echo "== Probe p2 with larger bounds and with up-to techniques off"
run "probes/p2-callback-revoked.bils" "$HERE/probes/p2-callback-revoked.bils" -b 12
run "probes/p2-callback-revoked.bils" "$HERE/probes/p2-callback-revoked.bils" -u "" -b 6
run "probes/p5-local-counter-vs-const.bils" "$HERE/probes/p5-local-counter-vs-const.bils" -u ""
run "probes/p5-local-counter-vs-const.bils" "$HERE/probes/p5-local-counter-vs-const.bils" -b 12
run "probes/p5-local-counter-vs-const.bils" "$HERE/probes/p5-local-counter-vs-const.bils" -b 24
run "probes/p5b-local-counter-with-invariant.bils" "$HERE/probes/p5b-local-counter-with-invariant.bils" -u "ngsrialfue"

echo "== Benchmarks at the larger bounds listed in the repository's run-tests.sh SPECIAL_BOUNDS"
run "equiv/syteci-call-lock.bils" "$P/equiv/syteci-call-lock.bils" -b 10
run "inequiv/meyer-sieber-ineq.bils" "$P/inequiv/meyer-sieber-ineq.bils" -b 8

echo "== Well-bracketing-dependent equivalences at larger bounds (default up-to techniques)"
for f in equiv/hector-pitts-stark.bils equiv/hector-thamsborg.bils; do
  run "$f" "$P/$f" -b 12
  run "$f" "$P/$f" -b 24
done
run "probes/p7-deferred-divergence-hos.bils" "$HERE/probes/p7-deferred-divergence-hos.bils" -b 12
run "probes/p7-deferred-divergence-hos.bils" "$HERE/probes/p7-deferred-divergence-hos.bils" -b 24
