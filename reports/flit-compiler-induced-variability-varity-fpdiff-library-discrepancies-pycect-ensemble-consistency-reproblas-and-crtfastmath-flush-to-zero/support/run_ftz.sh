#!/bin/sh
# FTZ/DAZ probe. half.c is always compiled without fast-math; only link-time options vary.
set -u
D=$(cd "$(dirname "$0")" && pwd)
W=${WORK:-/tmp/fp_probe_work}; mkdir -p "$W"
gcc --version | head -1
gcc -O2 -c "$D/half.c" -o "$W/half.o"
gcc -O2 -c "$D/ftzmain.c" -o "$W/ftzmain.o"
echo "== crtfastmath.o in the driver's link line (gcc -###):"
for f in "" "-ffast-math" "-Ofast" "-funsafe-math-optimizations" "-ffast-math -shared" "-ffast-math -mno-daz-ftz" "-mdaz-ftz -shared"; do
  n=$(gcc $f -### "$W/half.o" -o "$W/x" 2>&1 | grep -c crtfastmath.o); echo "  link flags [$f]: crtfastmath.o mentioned $n time(s)"; done
echo "== 1. executable linked without fast-math"
gcc "$W/ftzmain.o" "$W/half.o" -o "$W/e1" -lpthread -ldl && "$W/e1"
echo "== 2. same objects, executable LINKED with -ffast-math (no object compiled with it)"
gcc -ffast-math "$W/ftzmain.o" "$W/half.o" -o "$W/e2" -lpthread -ldl && "$W/e2"
echo "== 3. linked with -ffast-math -mno-daz-ftz"
gcc -ffast-math -mno-daz-ftz "$W/ftzmain.o" "$W/half.o" -o "$W/e3" -lpthread -ldl && "$W/e3"
echo "== 4. plain executable dlopens a shared library built with -ffast-math -shared"
gcc -O2 -fPIC -ffast-math -shared "$D/ftzlib.c" -o "$W/libfm.so"
"$W/e1" "$W/libfm.so"
echo "== 5. plain executable dlopens a shared library built with -mdaz-ftz -shared"
gcc -O2 -fPIC -mdaz-ftz -shared "$D/ftzlib.c" -o "$W/libdaz.so"
"$W/e1" "$W/libdaz.so"
echo "== 6. plain executable linked against the -mdaz-ftz library with default link options"
gcc "$W/ftzmain.o" "$W/half.o" -o "$W/e6" -L"$W" -ldaz -Wl,-rpath,"$W" -lpthread -ldl
echo "  DT_NEEDED entries: $(readelf -d "$W/e6" | grep NEEDED | sed 's/.*\[\(.*\)\]/\1/' | tr '\n' ' ')"
"$W/e6" | head -1
echo "== 7. same, forcing the library to stay in DT_NEEDED (-Wl,--no-as-needed)"
gcc "$W/ftzmain.o" "$W/half.o" -o "$W/e7" -Wl,--no-as-needed -L"$W" -ldaz -Wl,--as-needed -Wl,-rpath,"$W" -lpthread -ldl
echo "  DT_NEEDED entries: $(readelf -d "$W/e7" | grep NEEDED | sed 's/.*\[\(.*\)\]/\1/' | tr '\n' ' ')"
"$W/e7" | head -1
