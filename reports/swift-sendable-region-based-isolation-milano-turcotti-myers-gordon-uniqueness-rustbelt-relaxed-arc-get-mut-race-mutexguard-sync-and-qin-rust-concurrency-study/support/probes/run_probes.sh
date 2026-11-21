#!/bin/bash
# Sequential, bounded runner for the Rust probes in this directory.
# Each step: at most 8 CPUs (taskset), 60 s (timeout); peak RSS recorded by GNU time.
# Usage: run_probes.sh <probe-dir> <out-dir> [miri-sysroot]
# Set MIRI to the miri driver binary (default: miri on PATH); it may need
# LD_LIBRARY_PATH=<toolchain>/lib when invoked directly.
set -u
P="$1"; O="$2"; MS="${3:-}"
mkdir -p "$O"
run() { # name, cmd...
  local n="$1"; shift
  local t0=$(date +%s.%N)
  taskset -c 0-7 timeout 60 /usr/bin/time -f "PEAK_RSS_KB=%M WALL_S=%e EXIT=%x" "$@" > "$O/$n.out" 2> "$O/$n.err"
  local rc=$?
  echo "== $n rc=$rc $(grep -o 'PEAK_RSS_KB=.*' "$O/$n.err" | tail -1)"
  grep -E '^error\[E[0-9]+\]|^error:' "$O/$n.err" | head -3
  head -3 "$O/$n.out"
}
for f in p1_scope_move_while_borrowed p1b_scope_release_after_scope p2_spawn_borrow_local \
         p3_scope_rc_not_send p4_mutexguard_cell_sync p5_scope_forget_handle p6_scope_child_panic; do
  run "rustc_$f" rustc --edition 2021 -C codegen-units=1 -o "$O/$f" "$P/$f.rs"
  if [ -x "$O/$f" ]; then run "exec_$f" "$O/$f"; fi
done
if [ -n "$MS" ]; then
  run miri_p7_acquire "${MIRI:-miri}" --edition 2021 --sysroot "$MS" -Zmiri-many-seeds=0..32 "$P/p7_toy_arc_unique.rs"
  run miri_p7_relaxed "${MIRI:-miri}" --edition 2021 --sysroot "$MS" -Zmiri-many-seeds=0..32 -Zmiri-many-seeds-keep-going --cfg relaxed "$P/p7_toy_arc_unique.rs"
fi
