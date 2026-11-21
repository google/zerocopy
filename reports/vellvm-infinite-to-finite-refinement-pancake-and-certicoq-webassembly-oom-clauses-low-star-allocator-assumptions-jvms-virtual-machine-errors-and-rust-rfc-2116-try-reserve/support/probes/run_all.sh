#!/bin/bash
# Runs every probe sequentially (never concurrently), each under timeout 60,
# pinned to 8 CPUs, with /usr/bin/time -v for peak RSS. Output: probes/out/run.log
set -u
W=/tmp/oomprobe
cd "$W" || exit 1
export TMPDIR=$W/tmp
LOG=$W/probes/out/run.log
: > "$LOG"
run() {
  echo "### $*" >> "$LOG"
  ( cd "$W" && timeout 60 taskset -c 0-7 /usr/bin/time -f 'EXIT=%x MAXRSS_KB=%M WALL_S=%e' "$@" ) >> "$LOG" 2>&1
  echo "### shell_status=$?" >> "$LOG"
  echo >> "$LOG"
}
JAVA="java -XX:-UsePerfData -XX:+UseSerialGC -XX:ActiveProcessorCount=2 -XX:CICompilerCount=2 -cp $W/probes/java/classes"
run $JAVA -Xmx32m OomProbe heap
run $JAVA -Xmx64m OomProbe heap
run $JAVA -Xmx64m OomProbe arraysize
run $JAVA -Xmx32m -Xss256k OomProbe stack
run $JAVA -Xmx32m -Xss1m OomProbe stack
run $JAVA -Xmx32m -Xss4m OomProbe stack
run $JAVA -Xmx32m -XX:MaxDirectMemorySize=8m OomProbe direct
R=$W/probes/rust/oom_probe
run $R push
run $R try
run $R overflow
run $R hook
run $R vecmacro
C=$W/probes/c/oom_probe
run $C malloc
run $C new
run $C nothrow
echo DONE >> "$LOG"
