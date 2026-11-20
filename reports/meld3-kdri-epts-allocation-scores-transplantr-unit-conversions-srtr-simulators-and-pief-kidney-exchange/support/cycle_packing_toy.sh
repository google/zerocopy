#!/usr/bin/env bash
# Fetch kidney_solver test fixtures at the pinned revision and run the exact toy cycle-packing
# enumerator (cycle_packing_toy.py, an independent re-implementation, not kidney_solver).
# Requires: bash, curl, python3 (standard library only).
set -euo pipefail
REV=1ce13402b61f8131fad4c06eabc4f34c30e34e6e
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORK="${WORK:-/tmp/kep_toy}"; mkdir -p "$WORK"; cd "$WORK"
for f in MD-00001-00000100.input two_2cycles.input; do
  curl -sSL "https://raw.githubusercontent.com/jamestrimble/kidney_solver/$REV/test-fixtures/$f" -o "$f"
done
sha256sum MD-00001-00000100.input two_2cycles.input
for N in 32 40 48; do /usr/bin/time -f "  [%e s, %M KB max RSS]" timeout 60 python3 "$HERE/cycle_packing_toy.py" MD-00001-00000100.input 3 $N; done
for N in 24 32 40; do /usr/bin/time -f "  [%e s, %M KB max RSS]" timeout 60 python3 "$HERE/cycle_packing_toy.py" MD-00001-00000100.input 4 $N || echo "  (timeout at 60 s)"; done
/usr/bin/time -f "  [%e s, %M KB max RSS]" python3 "$HERE/cycle_packing_toy.py" two_2cycles.input 3
