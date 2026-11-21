Support material: bounded resource-exhaustion probes
=====================================================

All probes were run on 2026-11-21 on an x86_64 Linux 7.1 host (Intel Xeon @ 2.60GHz),
sequentially, each under `timeout 60`, pinned with `taskset -c 0-7`, and wrapped in
`/usr/bin/time -f 'EXIT=%x MAXRSS_KB=%M WALL_S=%e'`. Paths below assume the files
are copied to /tmp/oomprobe/probes/... (the original run used a different scratch
directory; only the prefix differs). The environment set _JAVA_OPTIONS=-XX:UseAVX=2,
which the Java launcher echoes on stderr.

Toolchains
----------
- Java: OpenJDK 27.0.1 HotSpot 64-Bit Server VM (a downstream vendor build; the
  matching upstream tag is jdk-27.0.1-ga in openjdk/jdk27u).
- Rust: rustc 1.102.0-nightly, commit-hash 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1.
- C/C++: gcc/g++ 15.2.0 (Debian 15.2.0-14), glibc 2.43.
- CakeML: release v3671, asset cake-x64-64.tar.gz,
  sha256 e3edd113497bf7fce443e69c70f09c3df1942849251c86ce8e44e6327ade0d3d.

Build
-----
  javac -d /tmp/oomprobe/probes/java/classes OomProbe.java
  rustc -O --edition 2021 -o /tmp/oomprobe/probes/rust/oom_probe oom_probe.rs
  g++ -O1 -o /tmp/oomprobe/probes/c/oom_probe oom_probe.cpp
  # CakeML compiler binary from the release assembly (outputs/cake_build.log):
  gcc -O2 -DEVAL cake.S basis_ffi.c -o cake -lm
  # each CakeML probe program:
  ./cake < cakeml_heap.cml > heap.S && gcc -O2 heap.S basis_ffi.c -o heap.cake -lm

Run
---
  bash run_all.sh       -> outputs/run.log        (Java, Rust, C/C++)
  bash run_cakeml.sh    -> outputs/cakeml_run.log (heap.cake, stack.cake)
  stack2.cake / stack3.cake were run with the same wrapper and the settings
  listed in outputs/cakeml_run2.log and outputs/cakeml_run3.log.
  The Java stack probe was repeated three times per -Xss value
  (outputs/stack_repeats.log). `rustc -Zoom=panic` was tried on an empty
  program (outputs/zoom_flag.log).

Exit-status conventions observed
--------------------------------
- shell_status=134: process killed by SIGABRT (Rust default allocation-error path).
- CakeML: exit status 1 = heap exhausted, 2 = stack exhausted (value of the
  pointer register when the generated code jumps to the halt routine; see
  basis_ffi.c cml_exit).
