#!/bin/bash
# Go open-coded defer probe. Usage: bash run_go.sh <workdir> <phase>
#   phase=static : defer-kind diagnostics, frame sizes, code sizes (optimized and -N -l)
#   phase=bench  : benchmarks (single CPU)
# All Go state (cache, module cache, home) is kept under the workdir.
set -eu
WD=$1; PHASE=$2
export HOME="$WD/home" GOCACHE="$WD/gocache" GOPATH="$WD/gopath" GOTMPDIR="$WD/gotmp" \
       GOTOOLCHAIN=local GOFLAGS=-mod=mod GOENV=off GOTELEMETRY=off XDG_CONFIG_HOME="$WD/home/.config" \
       GOMAXPROCS=8
mkdir -p "$HOME" "$GOCACHE" "$GOPATH" "$GOTMPDIR" "$WD/out"
cd "$WD/deferprobe"
[ -f go.mod ] || printf 'module deferprobe\n\ngo 1.22\n' > go.mod
FUNCS="NoDefer DeferUncond DeferCond ManualCond Defer8 Defer9 DeferLoop Defer4Ret3 Defer4Ret4 PanicOpen PanicLoop"
if [ "$PHASE" = static ]; then
  for mode in opt N; do
    if [ $mode = opt ]; then GCF="-d=defer"; else GCF="-N -l -d=defer"; fi
    go build -p 1 -gcflags="$GCF" -o "$WD/out/$mode.a" . 2> "$WD/out/defer_kinds_$mode.txt" || true
    go build -p 1 -a -gcflags="$GCF -S" -o "$WD/out/$mode.a" . 2> "$WD/out/asm_$mode.txt" || true
    echo "## mode=$mode: defer kinds (file:line: kind)"
    grep -E 'defer$' "$WD/out/defer_kinds_$mode.txt" | sed -E 's#^.*/deferprobe/##' | sort -t: -k2,2n
    echo "## mode=$mode: per-function frame size, code bytes, deferreturn calls"
    printf 'func\tframe_bytes\ttext_bytes\tdeferreturn_calls\tdeferproc_calls\n'
    for f in $FUNCS; do
      hdr=$(grep -E "^deferprobe\.$f STEXT" "$WD/out/asm_$mode.txt" | head -1)
      size=$(echo "$hdr" | sed -nE 's/.* size=([0-9]+) .*/\1/p')
      frame=$(echo "$hdr" | sed -nE 's/.* args=0x[0-9a-f]+ locals=(0x[0-9a-f]+).*/\1/p')
      body=$(awk -v f="deferprobe.$f STEXT" 'index($0,f)==1{p=1;next} /STEXT/{p=0} p' "$WD/out/asm_$mode.txt")
      dr=$(echo "$body" | grep -cE 'rel .*t=R_CALL runtime\.deferreturn\+' || true)
      dp=$(echo "$body" | grep -cE 'rel .*t=R_CALL runtime\.deferproc' || true)
      printf '%s\t%d\t%s\t%s\t%s\n' "$f" "$frame" "$size" "$dr" "$dp"
    done
  done
elif [ "$PHASE" = bench ]; then
  go test -p 1 -c -o "$WD/out/deferprobe.test" .
  "$WD/out/deferprobe.test" -test.run='^$' -test.bench=. -test.benchtime=5000000x -test.count=3 -test.cpu=1
fi
