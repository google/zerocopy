#!/bin/sh
# Rebuild and run every probe in this directory on an x86-64 Linux host.
# Requirements: gcc, gfortran, clang-19 (or set CLANG), and LLVM tools
# (llvm-link and opt) for one or more LLVM major versions (set LLVM_BINS).
# Output goes to stdout; the recorded run is in ../outputs/run_all.txt.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${WORK:-/tmp/fpenv-boundary-probes}
CLANG=${CLANG:-clang-19}
LLVM_BINS=${LLVM_BINS:-"/usr/lib/llvm-19/bin /usr/lib/llvm-21/bin"}
PIN=${PIN:-"taskset -c 1"}
mkdir -p "$WORK/llvm"
cd "$WORK"

echo "== host"
uname -sr
grep -m1 "model name" /proc/cpuinfo || true
gcc --version | head -1; gfortran --version | head -1; $CLANG --version | head -1
ldd --version | head -1

echo "== 1. thread creation, signal delivery, dlopen (MXCSR / x87 control word)"
gcc -O1 -pthread "$HERE/fpenv_boundaries.c" -o probe -ldl
gcc -O2 -shared -fPIC "$HERE/lib_fast.c" -o "$WORK/lib_gcc_plain.so"
gcc -O2 -ffast-math -shared -fPIC "$HERE/lib_fast.c" -o "$WORK/lib_gcc_ffastmath_shared.so"
gcc -O2 -ffast-math -mdaz-ftz -shared -fPIC "$HERE/lib_fast.c" -o "$WORK/lib_gcc_mdazftz_shared.so"
$CLANG -O2 -ffast-math -shared -fPIC "$HERE/lib_fast.c" -o "$WORK/lib_clang_ffastmath_shared.so"
./probe "$WORK/lib_gcc_plain.so" "$WORK/lib_gcc_ffastmath_shared.so" "$WORK/lib_gcc_mdazftz_shared.so" "$WORK/lib_clang_ffastmath_shared.so"

echo "== 2. MXCSR at main() for executables"
for cc in "gcc -O2" "gcc -O2 -ffast-math" "gcc -O2 -ffast-math -mno-daz-ftz" "$CLANG -O2" "$CLANG -O2 -ffast-math"; do
  $cc "$HERE/startup_mxcsr.c" -o st; printf '%-36s ' "$cc:"; ./st
done
gfortran -O2 -ffast-math "$HERE/startup_mxcsr.f90" -o stf -J "$WORK"; printf 'gfortran -O2 -ffast-math: '; ./stf
gfortran -O2 "$HERE/startup_mxcsr.f90" -o stf -J "$WORK"; printf 'gfortran -O2:             '; ./stf

echo "== 3. Fortran procedure-boundary rules (gfortran)"
gcc -O1 -c "$HERE/fortran_c_helper.c" -o fortran_c_helper.o
gfortran -O1 "$HERE/fortran_modes.f90" fortran_c_helper.o -o fortran_modes -J "$WORK"
./fortran_modes
echo "(FE_DOWNWARD = 1024, FE_TONEAREST = 0 on x86-64 glibc)"

echo "== 4. LLVM IR denormal attributes, inlining, linking"
for f in "" "-fdenormal-fp-math=preserve-sign" "-fdenormal-fp-math=dynamic" "-ffast-math"; do
  printf '%-40s ' "$CLANG $f:"
  $CLANG -O2 $f -S -emit-llvm "$HERE/llvm/callee.c" -o - | grep -o '"denormal-fp-math[^"]*"="[^"]*"' | sort -u | tr '\n' ' '; echo
done
$CLANG -O2 -S -emit-llvm "$HERE/llvm/caller.c" -o llvm/caller_ieee.ll
$CLANG -O2 -fdenormal-fp-math=preserve-sign -S -emit-llvm "$HERE/llvm/callee.c" -o llvm/callee_ps.ll
$CLANG -O2 -fdenormal-fp-math=dynamic -S -emit-llvm "$HERE/llvm/callee.c" -o llvm/callee_dyn.ll
$CLANG -O2 -S -emit-llvm "$HERE/llvm/callee.c" -o llvm/callee_ieee.ll
for B in $LLVM_BINS; do
  for c in ps dyn ieee; do
    "$B/llvm-link" llvm/caller_ieee.ll "llvm/callee_$c.ll" -S -o "llvm/linked_$c.ll"
    n=$("$B/opt" -passes='cgscc(inline)' -inline-threshold=1000 -S "llvm/linked_$c.ll" -o - | awk '/define.*@caller/,/^}/' | grep -c 'call.*@callee_scale' || true)
    echo "$("$B/opt" --version | grep -m1 -o 'LLVM version [0-9.]*'): caller(default ieee) -> callee($c): calls left after inlining = $n (llvm-link printed no diagnostic unless shown above)"
  done
done

echo "== 5. subnormal operand cost (scalar SSE2 multiply)"
gcc -O2 "$HERE/denormal_cost.c" -o denormal_cost
$PIN ./denormal_cost; $PIN ./denormal_cost

echo "== 6. save+restore cost of control state"
gcc -O2 "$HERE/save_restore_cost.c" -o save_restore_cost -lm
$PIN ./save_restore_cost

echo "== 7. gfortran per-call cost of IEEE entry/exit"
gfortran -O2 "$HERE/fortran_call_cost.f90" -o fortran_call_cost -J "$WORK"
$PIN ./fortran_call_cost
