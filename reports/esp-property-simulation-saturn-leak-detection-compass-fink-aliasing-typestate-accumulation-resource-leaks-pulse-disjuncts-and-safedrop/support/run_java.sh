#!/bin/sh
# Usage: run_java.sh <checker-framework-dir> <path-to-infer> <workdir>
# Runs the Checker Framework Resource Leak Checker and Infer Pulse on java/Corr.java.
# Observed with OpenJDK 25.
set -u
CF="$1"; INFER="$2"; WORK="$3"; HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$WORK"; cp "$HERE"/java/Corr.java "$WORK"/; cd "$WORK"
/usr/bin/time -f "rlc wall_s=%e maxrss_kb=%M" java -jar "$CF/checker/dist/checker.jar" -processor resourceleak -d out_rlc Corr.java
/usr/bin/time -f "pulse wall_s=%e maxrss_kb=%M" "$INFER" run --pulse-only -o out_pulse -- javac --release 11 -d out_classes Corr.java
