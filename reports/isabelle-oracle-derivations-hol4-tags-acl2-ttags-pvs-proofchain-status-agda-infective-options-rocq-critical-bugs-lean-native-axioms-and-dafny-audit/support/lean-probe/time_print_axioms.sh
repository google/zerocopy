#!/usr/bin/env bash
# Wall-clock comparison of the downstream file with and without its 8 `#print axioms` commands.
# Run from the probe project root after `lake build`. Single-host measurement.
set -eu
LEAN=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
export LEAN_PATH=$PWD/.lake/build/lib/lean:$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean
for f in Downstream.lean DownstreamNoPrint.lean; do
  for i in 1 2 3 4 5 6 7; do
    s=$(date +%s%N); "$LEAN" "$f" > /dev/null; e=$(date +%s%N)
    echo "$f run$i $(( (e - s) / 1000000 )) ms"
  done
done
