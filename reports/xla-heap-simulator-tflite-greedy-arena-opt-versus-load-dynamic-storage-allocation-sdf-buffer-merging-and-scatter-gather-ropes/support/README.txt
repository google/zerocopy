Support material for the static buffer offset planning report.

dsa_probe/
  fetch_upstream.sh    downloads the tflite-micro planner sources at the pinned revision into ./upstream
  shim/                three minimal headers (status enum, empty macro, printf logger) replacing upstream
                       headers that the planner includes; the planner source itself is unmodified
  dsa_probe.cc         harness: exact optimum by enumeration, LOAD / max-weight clique, upstream TFLM
                       planner, toy best-fit re-implementations, fork-join toy model, timing
  tflm_one.cc          reproduces the 4-buffer instance where TFLM returns 12 while OPT = LOAD = 9
  out_*.txt            outputs recorded on 2026-11-20 (x86-64 Linux, GCC 15.2.0)

  Build: g++ -std=c++17 -O2 -Ishim -Iupstream dsa_probe.cc \
           upstream/tensorflow/lite/micro/memory_planner/greedy_memory_planner.cc -o dsa_probe
  Run:   ./dsa_probe stats | forkjoin | examples | timing

segmented/
  seg_probe.rs         sizes of bytes::Bytes, Chain, IoSlice; copy_to_bytes sharing vs copying
  cord_sizes.cc        sizes of absl::Cord nodes and struct iovec; IOV_MAX
  out_*.txt            outputs recorded on 2026-11-20 (x86-64 Linux, rustc 1.102.0-nightly 2026-11-11)
