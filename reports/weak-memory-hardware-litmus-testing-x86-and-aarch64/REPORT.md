# Weak-Memory Behavior of Real Hardware: x86-TSO and Armv8 Litmus Testing vs. `herd7`

## Summary

Executing a 9-family multi-threaded barrier-synchronized Rust atomic litmus suite (`2.70 \times 10^6` total barrier-synchronized thread executions, `300,000` iterations per family) pinned to distinct physical cores via `sched_setaffinity` on the host `x86_64` CPU, alongside cross-compiled AArch64 (`+v8a` and `+lse,+rcpc`) assembly verification and `herd7` (`7.58`, `9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`) axiomatic predictions, establishes:

1. **Empirical Hardware Observation Rates on Native `x86_64` vs. `herd7 -model x86tso.cat` (`support/litmus_observations_vs_herd7.csv`):**
   - **Store Buffering (`SB_Relaxed`: `x.store(1, Relaxed); r0 = y.load(Relaxed) || y.store(1, Relaxed); r1 = x.load(Relaxed)`):** Exhibits **`495` weak outcomes (`r0 = 0 /\ r1 = 0`) per `300,000` iterations (`1,650.0 ppm` / `0.165%`)** on native `x86_64`, directly demonstrating hardware FIFO store-buffer forwarding where each core's load bypasses its own uncommitted store in the store buffer before the store becomes globally visible in L1D/coherent memory.
   - **Complete Suppression of Store Buffering by `rustc 1.99.1`'s Three `SeqCst` Lowerings (`0 / 300,000` weak outcomes each):**
     - `SB_SeqCst_Fence` (`fence(Ordering::SeqCst)` $\mapsto$ `lock orl $0, -64(%rsp)`): **`0 / 300,000` (`0.0 ppm`)**.
     - `SB_SeqCst_Ops` (`store(1, SeqCst)` $\mapsto$ `xchgl %eax, (%rdi)`; `load(SeqCst)` $\mapsto$ `movl (%rsi), %eax`): **`0 / 300,000` (`0.0 ppm`)**.
     - `SB_RMW_SeqCst` (`fetch_add(1, SeqCst)` $\mapsto$ `lock xaddl %eax, (%rdi)`): **`0 / 300,000` (`0.0 ppm`)**.
   - **Zero Non-TSO Relaxations on `x86_64` Hardware (`0 / 300,000` each):** `MP_Relaxed` (`0`), `MP_RelAcq` (`0`), `LB_Relaxed` (`0`), `2+2W_Relaxed` (`0`), and `CoRR` (`0`) produce **zero** weak outcomes across `1,500,000` combined iterations, matching `x86tso.cat` (`Never`) where hardware preserves `W ->po W`, `R ->po R`, `R ->po W`, multi-copy atomicity, and per-location coherence even for `Ordering::Relaxed`.
2. **AArch64 Instruction Lowering (`+v8a` vs. `+lse,+rcpc`) and Emulation Masking Under `qemu-aarch64` (`support/rust_litmus_tests.rs`):**
   - Compiling the identical Rust litmus kernels with `rustc 1.99.1 --target aarch64-unknown-linux-gnu` confirms that baseline `+v8a` lowers `Ordering::Acquire` loads and `Ordering::SeqCst` loads identically to `ldar w0, [x1]`, whereas `-C target-feature=+lse,+rcpc` lowers `Ordering::Acquire` loads to **`ldapr w0, [x1]`** (`RCpc` weak acquire) while keeping **`ldar w0, [x1]`** (`RCsc` strong acquire) for `Ordering::SeqCst` loads, and replaces the out-of-line `__aarch64_ldadd4_acq_rel` LL/SC helper call with a single inlined **`ldaddal w8, w0, [x0]`** instruction.
   - Running AArch64 multi-threaded binaries under `qemu-aarch64` user-mode emulation on an `x86_64` host translates guest AArch64 plain `str`/`ldr` into host `x86_64` `mov` instructions executed by host pthreads: the emulator therefore inherits the **host `x86-TSO` memory model** (capable of exhibiting `SB_Relaxed` store buffering, but architecturally incapable of exhibiting non-TSO Armv8 relaxations such as `MP_Relaxed`, `LB_Relaxed`, or `2+2W_Relaxed`). Testing non-TSO Armv8 relaxations requires physical Armv8 silicon (or a cycle-accurate/model-checking simulator).

## Applicability

- **Extends:** `weak-memory-concurrency-models-hardware-mappings-and-optimizations`, `tier1-atomics-and-fences-instruction-lowering`
- **Subjects and Scope:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), specifically `library/core/src/sync/atomic.rs` and LLVM `23.1.1` `X86` / `AArch64` atomic codegen.
  - `herd/herdtools7` `7.58` (`9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`), specifically `x86tso.cat`, `aarch64.cat`, and `rc11.cat`.
  - Host `x86_64-unknown-linux-gnu` multi-core processor and `qemu-aarch64` `9.2.0`.

## Findings

### 1. Native `x86_64` Hardware Litmus Observations vs. `herd7` Axiomatic Models

**Basis: execution (`support/run_litmus_suite.py`, `support/rust_litmus_tests.rs`, `support/litmus_observations_vs_herd7.csv`).**

| Litmus Family | Weak Condition Tested | Native `x86_64` Weak Count (`300,000` iters) | Observed Rate (ppm) | `herd7 -cat x86tso.cat` Prediction | `herd7 -cat aarch64.cat` Prediction | `herd7 -cat rc11.cat` Prediction |
| :--- | :--- | :---: | :---: | :--- | :--- | :--- |
| **`SB_Relaxed`** | `r0 = 0 /\ r1 = 0` | **`495`** | **`1,650.0 ppm`** | **`Allowed` (`Sometimes`)** | **`Allowed` (`Sometimes`)** | **`Allowed` (`Sometimes`)** |
| **`SB_SeqCst_Fence`** | `r0 = 0 /\ r1 = 0` | `0` | `0.0 ppm` | `Forbidden` (`Never`) | `Forbidden` (`Never`) | `Forbidden` (`Never`) |
| **`SB_SeqCst_Ops`** | `r0 = 0 /\ r1 = 0` | `0` | `0.0 ppm` | `Forbidden` (`Never`) | `Forbidden` (`Never`) | `Forbidden` (`Never`) |
| **`SB_RMW_SeqCst`** | `r0 = 0 /\ r1 = 0` | `0` | `0.0 ppm` | `Forbidden` (`Never`) | `Forbidden` (`Never`) | `Forbidden` (`Never`) |
| **`MP_Relaxed`** | `r0 = 1 /\ r1 = 0` | `0` | `0.0 ppm` | `Forbidden` (`Never`) | **`Allowed` (`Sometimes`)** | **`Allowed` (`Sometimes`)** |
| **`MP_RelAcq`** | `r0 = 1 /\ r1 = 0` | `0` | `0.0 ppm` | `Forbidden` (`Never`) | `Forbidden` (`Never`) | `Forbidden` (`Never`) |
| **`LB_Relaxed`** | `r0 = 1 /\ r1 = 1` | `0` | `0.0 ppm` | `Forbidden` (`Never`) | **`Allowed` (`Sometimes`)** | `Forbidden` (`acyclic(po\|rf)`) |
| **`2+2W_Relaxed`** | `fx = 1 /\ fy = 1` | `0` | `0.0 ppm` | `Forbidden` (`Never`) | **`Allowed` (`Sometimes`)** | **`Allowed` (`Sometimes`)** |
| **`CoRR`** | `r0 = 1 /\ r1 = 0` | `0` | `0.0 ppm` | `Forbidden` (`Never`) | `Forbidden` (`Never`) | `Forbidden` (`Never`) |

#### Why `lock orl $0, -64(%rsp)` Eliminates All `495` Store-Buffer Relaxations

Inspecting the emitted `x86_64` assembly for `asm_sb_relaxed`, `asm_sb_seqcst_fence`, and `asm_sb_seqcst_ops`:
```nasm
asm_sb_relaxed:
    movl    $1, (%rdi)
    movl    (%rsi), %eax
    retq

asm_sb_seqcst_fence:
    movl    $1, (%rdi)
    lock orl $0, -64(%rsp)
    movl    (%rsi), %eax
    retq

asm_sb_seqcst_ops:
    movl    $1, %eax
    xchgl   %eax, (%rdi)
    movl    (%rsi), %eax
    retq
```
In `asm_sb_relaxed`, the store `movl $1, (%rdi)` enters the core's FIFO store buffer while `movl (%rsi), %eax` reads L1D immediately (`495` weak observations per `300,000` trials). Inserting either `lock orl $0, -64(%rsp)` (`fence(Ordering::SeqCst)`) or `xchgl %eax, (%rdi)` (`store(1, Ordering::SeqCst)`) forces the core to drain its store buffer to coherent L1D before executing the subsequent `movl (%rsi), %eax` load, reducing the weak outcome count from `495` to `0`.

---

### 2. AArch64 Lowering Comparison (`+v8a` vs. `+lse,+rcpc`) and QEMU User-Mode Masking

**Basis: execution (`rustc 1.99.1 --target aarch64-unknown-linux-gnu --emit=asm`).**

| Litmus Kernel | `aarch64` Baseline (`+v8a`) | `aarch64` (`-C target-feature=+lse,+rcpc`) | Weak-Memory Verification Consequence |
| :--- | :--- | :--- | :--- |
| **`asm_sb_relaxed`** | `str w8, [x0]` ; `ldr w0, [x1]` | `str w8, [x0]` ; `ldr w0, [x1]` | `Sometimes` in `aarch64.cat` (reordered by store buffer / out-of-order issue) |
| **`asm_sb_seqcst_fence`** | `str w8, [x0]` ; `dmb ish` ; `ldr w0, [x1]` | `str w8, [x0]` ; `dmb ish` ; `ldr w0, [x1]` | `Never` in `aarch64.cat` (`dmb.full` in `bob` orders `W -> R`) |
| **`asm_sb_seqcst_ops`** | `stlr w8, [x0]` ; `ldar w0, [x1]` | `stlr w8, [x0]` ; **`ldar w0, [x1]`** | `Never` in `aarch64.cat` (`[L]; po; [A]` in `bob` forbids reordering `stlr` past `ldar`) |
| **`asm_mp_rel_acq`** | `str w8, [x0]` ; `stlr w8, [x1]` ; `ldar w0, [x1]` | `str w8, [x0]` ; `stlr w8, [x1]` ; **`ldapr w0, [x1]`** | `Never` for `MP` (`(A\|Q) ->po M`), **but** `stlr` followed by `ldapr` (`[L]; po; [Q]`) is **not** ordered in `bob`, so `load(SeqCst)` must never use `ldapr`! |
| **`asm_rmw_acqrel`** | `bl __aarch64_ldadd4_acq_rel` (`ldaxr`/`stlxr` loop) | **`ldaddal w8, w0, [x0]`** | Single-instruction LSE atomic RMW; eliminates LL/SC retry livelock under high contention |

#### Why `qemu-aarch64` on an `x86_64` Host Cannot Test Non-TSO Armv8 Relaxations

In QEMU user-mode emulation (`qemu-aarch64`), guest AArch64 threads are mapped 1:1 to host Linux `pthread`s, and the Tiny Code Generator (TCG) lowers guest AArch64 plain loads (`ldr`) and stores (`str`) into host `x86_64` `mov` instructions without simulating out-of-order Armv8 load/store queues or non-coherent write buffers. Because the underlying `x86_64` hardware enforces `W ->po W`, `R ->po R`, and `R ->po W`, `qemu-aarch64` masks 100% of `MP_Relaxed`, `LB_Relaxed`, `2+2W_Relaxed`, and `IRIW` bugs (such as accidentally omitting `stlr`/`ldar` in a lock-free queue).

## Boundaries

1. **Unavailable Physical Armv8 Silicon (**not examined** — bounded stop):** Physical Apple M-series, Arm Neoverse (AWS Graviton / Google Axion), Ampere Altra, and Qualcomm Windows-on-Arm bare-metal machines are not attached to this workstation environment. All Armv8 non-TSO weak outcomes (`MP_Relaxed`, `LB_Relaxed`, `2+2W_Relaxed`) are established via `herd7 -cat aarch64.cat` exhaustive state-space enumeration and preserved in `support/rust_litmus_tests.rs` for direct execution on Armv8 hardware.

## Evidence

- **Axiomatic Hardware Models (`herd/herdtools7` `7.58` at `9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`):**
  - `herd/libdir/x86tso.cat`, `herd/libdir/aarch64.cat`, `herd/libdir/aarch64hwreqs.cat:122-138`, `herd/libdir/rc11.cat`.
- **Preserved Package Support Artifacts (`support/`):**
  - [`support/rust_litmus_tests.rs`](support/rust_litmus_tests.rs): Standalone core-pinned Rust litmus test suite (`SB`, `SB+fence`, `SB+SeqCst`, `SB+RMW`, `MP`, `MP+RelAcq`, `LB`, `2+2W`, `CoRR`) plus exported assembly inspection functions (`asm_sb_*`, `asm_mp_rel_acq`, `asm_rmw_acqrel`).
  - [`support/run_litmus_suite.py`](support/run_litmus_suite.py): Reproducible harness compiling and executing the litmus suite and comparing against `herd7`.
  - [`support/litmus_observations_vs_herd7.csv`](support/litmus_observations_vs_herd7.csv): Complete 9-family hardware observation table (`300,000` iterations per family) paired with `x86tso.cat`, `aarch64.cat`, and `rc11.cat` normative classifications.

## Revalidation

```bash
rustc +1.99.1-x86_64-unknown-linux-gnu --edition=2021 -C opt-level=3 support/rust_litmus_tests.rs -o litmus_x86_64
./litmus_x86_64 300000
```
Verify that `SB_Relaxed` is strictly positive (`> 0`) while all 8 other entries (`SB_SeqCst_Fence`, `SB_SeqCst_Ops`, `SB_RMW_SeqCst`, `MP_Relaxed`, `MP_RelAcq`, `LB_Relaxed`, `2+2W_Relaxed`, `CoRR`) equal `0`.
