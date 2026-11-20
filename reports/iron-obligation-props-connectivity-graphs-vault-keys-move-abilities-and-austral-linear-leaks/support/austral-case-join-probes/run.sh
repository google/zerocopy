#!/bin/sh
# Usage: AUSTRAL=/path/to/austral.exe sh run.sh
# Run from a checkout of austral/austral at 0962d2a8a5d77f7daacd7f696819520733f4897d
# after: python3 concat_builtins.py && dune build bin/austral.exe
# (AUSTRAL defaults to ./_build/default/bin/austral.exe).
# Prints the compiler exit status for each probe; p8 is also compiled with gcc
# and executed when the compiler accepts it.
HERE=$(cd "$(dirname "$0")" && pwd)
AUSTRAL=${AUSTRAL:-./_build/default/bin/austral.exe}
OUT=${TMPDIR:-/tmp}/austral-case-join-probes
mkdir -p "$OUT"
for p in p1 p2 p3 p4 p5 p6 p7 p8; do
  "$AUSTRAL" compile "$HERE/$p/Test.aum" --entrypoint=Test:main --target-type=c \
     --output="$OUT/$p.c" --error-format=json > "$OUT/$p.stderr.txt" 2>&1
  echo "$p austral_exit=$?"
done
if [ -f "$OUT/p8.c" ]; then
  gcc -fwrapv -w "$OUT/p8.c" -lm -o "$OUT/p8" && "$OUT/p8"; echo "p8 run_exit=$?"
fi
