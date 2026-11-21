#!/usr/bin/env bash
# Reproduces the allocation-elision and exhaustion-surfacing probes.
# Usage: bash run_probes.sh            (writes binaries to a fresh temp dir)
# Requires: gcc/g++, rustc, systemd-run --user (for the cgroup probe), python3.
# The probes never touch more than 256 MiB of memory; large mallocs are
# reserved but not touched ("notouch").
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
B="$(mktemp -d)"
trap 'rm -rf "$B"' EXIT
echo "## environment"
uname -srm
gcc --version | head -1
rustc -vV | grep -E '^(rustc|commit-hash|LLVM)'
echo "overcommit_memory=$(cat /proc/sys/vm/overcommit_memory) overcommit_ratio=$(cat /proc/sys/vm/overcommit_ratio)"
grep -E '^(MemTotal|SwapTotal|CommitLimit):' /proc/meminfo
echo "RLIMIT_AS (ulimit -v) = $(ulimit -v)"

echo "## E1: C malloc/free elision (gcc)"
for O in O0 O2; do
  gcc -$O -o "$B/elide_c_$O" "$HERE/elide.c"
  "$B/elide_c_$O"; echo "  gcc -$O exit=$?"
  echo "  malloc calls in gcc -$O assembly: $(gcc -$O -S -o - "$HERE/elide.c" | grep -c -E 'call.*malloc')"
done
gcc -O2 -fno-builtin-malloc -o "$B/elide_c_nb" "$HERE/elide.c"
"$B/elide_c_nb"; echo "  gcc -O2 -fno-builtin-malloc exit=$?"

echo "## E2: C++ new-expression elision (g++)"
for O in O0 O2; do
  g++ -$O -o "$B/elide_cc_$O" "$HERE/elide.cc"
  "$B/elide_cc_$O"; echo "  g++ -$O exit=$?"
  echo "  operator new[] calls in g++ -$O assembly: $(g++ -$O -S -o - "$HERE/elide.cc" | grep -c -E 'call.*_Zna')"
done
g++ -O2 -fno-allocation-dce -o "$B/elide_cc_nd" "$HERE/elide.cc"
"$B/elide_cc_nd"; echo "  g++ -O2 -fno-allocation-dce exit=$?"

echo "## E3: Rust global-allocator elision (rustc)"
for O in 0 3; do
  rustc -C opt-level=$O -o "$B/elide_rs_$O" "$HERE/elide.rs" 2>/dev/null
  for m in unused observed try_reserve box; do
    out=$("$B/elide_rs_$O" $m 2>&1); ec=$?
    echo "  opt-level=$O mode=$m exit=$ec :: $(echo "$out" | head -1)"
  done
done

echo "## E4: where exhaustion surfaces (Linux)"
gcc -O0 -o "$B/touch" "$HERE/touch.c"
gcc -O0 -o "$B/multi" "$HERE/multi.c"
echo "-- baseline, no limit: touch 256 MiB"
"$B/touch" 256 | tail -1; echo "  exit=${PIPESTATUS[0]}"
echo "-- RLIMIT_AS = 128 MiB (ulimit -v 131072): touch 256 MiB"
( ulimit -v 131072; "$B/touch" 256; echo "  exit=$?" )
echo "-- cgroup v2 memory.max = 64 MiB, memory.swap.max = 0: touch 256 MiB"
systemd-run --user --scope -q -p MemoryMax=64M -p MemorySwapMax=0 "$B/touch" 256 > "$B/cg.txt" 2>&1; ec=$?
head -1 "$B/cg.txt"; tail -1 "$B/cg.txt"; echo "  exit=$ec (137 = SIGKILL)"
echo "-- overcommit_memory=0 heuristic boundary (no pages touched)"
python3 - <<'EOF'
import re
m = dict(re.findall(r'^(\w+):\s+(\d+)', open('/proc/meminfo').read(), re.M))
kb = int(m['MemTotal']) + int(m['SwapTotal'])
print(f"  MemTotal+SwapTotal = {kb} kB = {kb/1024:.4f} MiB = {kb//4} pages of 4 KiB")
EOF
LIM=$(python3 -c "import re;m=dict(re.findall(r'^(\w+):\s+(\d+)',open('/proc/meminfo').read(),re.M));print((int(m['MemTotal'])+int(m['SwapTotal']))//1024)")
for mib in $((LIM-1)) $LIM $((LIM+1)) $((LIM+200)); do "$B/touch" $mib notouch; echo "  exit=$?"; done
echo "-- per-request vs cumulative: three untouched 200000 MiB mallocs, then three over the boundary"
"$B/multi" 200000 3
"$B/multi" $((LIM+1)) 3
