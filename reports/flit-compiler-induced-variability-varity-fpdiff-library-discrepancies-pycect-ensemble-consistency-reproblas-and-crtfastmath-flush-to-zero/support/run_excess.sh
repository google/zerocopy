#!/bin/sh
# Excess precision on 32-bit x86 (x87) versus SSE2, under GNU and ISO language modes.
set -u
D=$(cd "$(dirname "$0")" && pwd)
W=${WORK:-/tmp/fp_probe_work}; mkdir -p "$W"
for f in "-m32 -O2" "-m32 -O2 -std=c17" "-m32 -O2 -fexcess-precision=standard" "-m32 -O2 -msse2 -mfpmath=sse" "-O2"; do
  gcc $f "$D/excess.c" -o "$W/ex" && echo "[$f] $("$W/ex")"; done
