#!/bin/bash
# GNAT finalization-state probe. Usage: bash run_gnat.sh <gnat-root> <workdir>
# Emits: expanded (-gnatG) source excerpts, run output, and per-subprogram
# code sizes at -O0/-O1/-O2/-Os.
set -eu
GR=$1; WD=$2
export PATH="$GR/bin:$PATH" HOME="$WD/home" TMPDIR="$WD/tmp"
mkdir -p "$HOME" "$TMPDIR" "$WD/out"
cd "$WD/out"
cp -f "$WD"/*.ads "$WD"/*.adb .
gcc -c -gnatG -gnatws fin_probe.adb > expanded_fin_probe.txt 2>&1 || true
echo "## expanded-source lines mentioning counters / master nodes / finalizers"
grep -n -E '\bC[0-9]+ : integer|C[0-9]+ := C[0-9]+ \+ 1|case C[0-9]+ is|counter|MN : aliased|attach_object_to_(node|master)|finalize_object|_finalizer|goto L[0-9]+' -i expanded_fin_probe.txt | head -80 || true
echo "## run (-O0)"
gnatmake -q -O0 -f fin_main.adb -o fin_main_O0 >/dev/null 2>&1
./fin_main_O0
echo "## trace (-O0): V of each finalized element, in call order"
gnatmake -q -O0 -f trace_main.adb -o trace_main_O0 >/dev/null 2>&1
./trace_main_O0
printf '## code bytes per subprogram\nlevel\tsymbol\tbytes\n'
for L in O0 O1 O2 Os; do
  mkdir -p lvl_$L && (cd lvl_$L && gcc -c -$L -gnatws ../fin_probe.adb)
  nm -S --defined-only lvl_$L/fin_probe.o | awk -v L=$L '$3 ~ /^[Tt]$/ {printf "%s\t%s\t%d\n", L, $4, strtonum("0x"$2)}' \
    | grep -E 'fin_probe__(use_rec|use_arr|use_block|pick|rec3IP|rec3DF|arrIP|arrDF|rec3DI|arrDI|use_rec___finalizer|use_arr___finalizer|use_block___finalizer)' || true
done
