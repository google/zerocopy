#!/usr/bin/env bash
# Reproduce the LowFat size-class tables from the upstream generator and measure
# allocation rounding for chosen request-size sets.
# Requires: bash, curl, gcc (x86-64 Linux, 4 KiB pages), python3.
set -euo pipefail
REV=20f8075dd1fd6588700262353c7ba619d82cea8f
BASE="https://raw.githubusercontent.com/GJDuck/LowFat/$REV/config"
WORK="${WORK:-/tmp/lowfat_probe}"
mkdir -p "$WORK" && cd "$WORK"
for f in lowfat-config.c sizes.cfg sizes2.cfg; do curl -sSL "$BASE/$f" -o "$f"; done
sha256sum lowfat-config.c sizes.cfg sizes2.cfg
gcc -O2 -o lowfat-config lowfat-config.c -lm -lpthread

cat > harness.c <<'EOF'
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include "lowfat_config.c"
/* Print "request allocated region" for every request size given on stdin. */
int main(void) {
    unsigned long long req;
    while (scanf("%llu", &req) == 1) {
        size_t idx = lowfat_heap_select((size_t)req);
        size_t alloc = (idx == 0) ? 0 : lowfat_sizes[idx - 1];
        printf("%llu %zu %zu\n", req, alloc, idx);
    }
    return 0;
}
EOF

for cfg in sizes.cfg sizes2.cfg; do
  d="run_${cfg%.cfg}"; mkdir -p "$d"
  (cd "$d" && ../lowfat-config "../$cfg" 32 > generator.log 2>&1)
  grep -E "^Region #(1|52|61): error" "$d/generator.log" || true
  grep -E "LOWFAT_NUM_REGIONS|LOWFAT_REGION_SIZE_SHIFT|LOWFAT_MAX_HEAP_ALLOC_SIZE" "$d/lowfat_config.c"
  cp "$d/lowfat_config.h" "$d/lowfat_config.c" .
  gcc -O1 -w -o "harness_${cfg%.cfg}" harness.c
done

python3 - "$WORK" <<'PY'
import subprocess, sys, os
work = sys.argv[1]
sets = {
    "uniform 1..4096": list(range(1, 4097)),
    "uniform 1..65536": list(range(1, 65537)),
    "powers of two 16..4096": [1 << k for k in range(4, 13)],
    "powers of two 16..1048576": [1 << k for k in range(4, 21)],
    "pow2 minus 8 (24..4088)": [(1 << k) - 8 for k in range(5, 13)],
}
for cfg in ("sizes", "sizes2"):
    exe = os.path.join(work, f"harness_{cfg}")
    for name, reqs in sets.items():
        out = subprocess.run([exe], input="\n".join(map(str, reqs)), capture_output=True, text=True, check=True).stdout
        rows = [tuple(map(int, l.split())) for l in out.splitlines()]
        req_total = sum(r for r, a, i in rows)
        alloc_total = sum(a for r, a, i in rows)
        worst = max(a / r for r, a, i in rows)
        print(f"{cfg:7s} | {name:26s} | n={len(rows):6d} | sum(alloc)/sum(req)={alloc_total/req_total:.4f} | worst alloc/req={worst:.4f}")
    out = subprocess.run([exe], input="16\n4096\n4095\n", capture_output=True, text=True, check=True).stdout
    print(f"{cfg:7s} | spot checks (request alloc region): " + "; ".join(out.splitlines()))
PY
