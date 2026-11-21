#!/bin/sh
# Usage: run.sh   (from this directory; requires cargo with network access to fetch loom)
set -u
cargo build --release -q 2>&1 | tail -3
for mode in assert noassert; do
  for k in 0 1 2 3 unset; do
    if [ "$mode" = noassert ]; then NA=1; export PROBE_NOASSERT=1; else unset PROBE_NOASSERT; fi
    if [ "$k" = unset ]; then unset LOOM_MAX_PREEMPTIONS; else export LOOM_MAX_PREEMPTIONS=$k; fi
    ./target/release/loom-preemption-probe 2>/dev/null | tail -1
  done
done
