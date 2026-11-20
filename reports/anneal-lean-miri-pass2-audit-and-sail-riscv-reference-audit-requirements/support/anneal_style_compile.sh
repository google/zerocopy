#!/usr/bin/env bash
# Anneal-style per-module compile of a Lean source tree (mimics the flags in
# joshlf/anneal@c131b320 trusted/audit/src/lib.rs build_bwrap_miri_compile_args,
# minus the bwrap sandbox): lean -j1 -M<mem> -t0 -DElab.async=false
# -Ddebug.skipKernelTC=false -R <src> -o <out>/<M>.olean <src>/<M>.lean
# Usage: anneal_style_compile.sh <lean-bin> <src-root> <out-dir> <extra-LEAN_PATH|-> <mem-MiB> <Module>...
# Modules must be given in topological order. Prints per-module wall time + olean sha256/size.
set -u
LEAN="$1"; SRC="$2"; OUT="$3"; EXTRA="$4"; MEM="$5"; shift 5
mkdir -p "$OUT"
LP="$OUT"; if [ "$EXTRA" != "-" ]; then LP="$OUT:$EXTRA"; fi
for M in "$@"; do
  rel="${M//.//}"
  mkdir -p "$OUT/$(dirname "$rel")"
  t0=$(date +%s.%N)
  env -i PATH=/usr/bin:/bin HOME=/tmp LEAN_PATH="$LP" "$LEAN" -j1 -M"$MEM" -t0 -DElab.async=false -Ddebug.skipKernelTC=false ${EXTRA_FLAGS:-} \
    -R "$SRC" -o "$OUT/$rel.olean" "$SRC/$rel.lean" > "$OUT/$rel.log" 2>&1
  rc=$?
  t1=$(date +%s.%N)
  if [ $rc -ne 0 ]; then echo "FAIL $M rc=$rc ($(awk "BEGIN{print $t1-$t0}")s)"; head -c 3000 "$OUT/$rel.log"; exit $rc; fi
  sha=$(sha256sum "$OUT/$rel.olean" | cut -c1-16); sz=$(stat -c %s "$OUT/$rel.olean")
  printf "OK %-40s %7.2fs olean=%s.. %d bytes\n" "$M" "$(awk "BEGIN{print $t1-$t0}")" "$sha" "$sz"
done
