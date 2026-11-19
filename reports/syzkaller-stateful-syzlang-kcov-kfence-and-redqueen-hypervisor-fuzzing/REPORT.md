# Stateful Kernel and Hypervisor Greybox Fuzzing: syzlang, KCOV/KFENCE, RedQueen I2S, and kAFL/Nyx

## Summary

Operating-system kernels and hypervisors reject structureless byte mutations because system-call chains depend on typed object lifecycles, background interrupt handlers decouple execution from calling threads, full shadow memory sanitizers multiply runtime cost, and guest-VM reboots bottleneck reset throughput. Four complementary mechanisms address these bottlenecks:

1. **Typed Syscall Resource Grammars (`syzlang`)**: `google/syzkaller` models producer–consumer resource edges (`ResourceDesc`, `ResourceType`, `Ref`) and subtype hierarchies so generated programs preserve handle validity without symbolic execution.
2. **Interrupt-Isolated Coverage (`KCOV_REMOTE_ENABLE`) & Sampled Guard Pages (`KFENCE`)**: Linux (`torvalds/linux` v6.12) binds background kernel threads and softirqs to explicit subsystem handles (`common_handle` / `handles[]`) for noiseless per-input feedback, while `KFENCE` trades deterministic full-shadow instrumentation (`KASAN`) for timer-sampled `4 KiB` virtual guard pages that detect spatial and temporal memory safety defects at negligible runtime cost.
3. **Input-to-State Comparison Solving (`RedQueen` / `CmpLog`)**: `AFLplusplus/AFLplusplus` pairs trace-preserving byte-entropy maximization (`colorization`) with fixed-size comparison logs (`struct cmp_map`, `144.50 MiB` packed layout) to invert magic values, length checks, and multi-byte constraints without an SMT solver.
4. **Hardware-Assisted Trace & Dirty-Ring Micro-Snapshots (`kAFL` / `Nyx`)**: `IntelLabs/kAFL` combines Intel Processor Trace decoding (`libxdc`) with KVM dirty-ring / fast-dirty-log (`RELOAD_MEMORY_MODE_FDL` and `RELOAD_MEMORY_MODE_DIRTY_RING`) state restoration in `kafl.qemu` to fuzz ring-0 kernels and firmware without source instrumentation or full reboots.

## Applicability

These findings apply to Linux kernel (`v6.12`), userspace/kernel coverage-guided fuzzers, and x86-64 virtualization targets pinned in `REPORT.json`:
- `google/syzkaller` (`f836d1190fca3bb4b2827b9f2081318a0edcc13a`): applies to Linux syscall/ioctl/netlink/vusb grammar synthesis and `syz-executor` running inside QEMU/VM workers.
- `torvalds/linux` (`adc218676eef25575469234709c2d87185ca223a`, `v6.12`): applies when kernels are built with `CONFIG_KCOV=y` (`CONFIG_KCOV_ENABLE_COMPARISONS=y` for comparison operands) and `CONFIG_KFENCE=y` (`CONFIG_HAVE_ARCH_KFENCE`).
- `AFLplusplus/AFLplusplus` (`d798677805de81b50aa8f45beb0342ae1617b9d8`): applies to LLVM/LTO `CmpLog`-instrumented binaries or QEMU/FRIDA binary-only translation modes implementing `struct cmp_map`.
- `IntelLabs/kAFL` (`b939b03ddd5734216c23de406f13fe6a35bf0a35`) with `kafl.qemu` (`v0.8`, `61ac92576db3573ddda9c0d0e3b55ac2a28ae403`) and `kafl.libxdc` (`v0.2`, `a4f6dcfe3c03c8e1fa1ddd56f8d8c58b91952543`): applies strictly to x86-64 hosts exposing Intel VT-x, Intel PT, and KVM dirty-page logging (`linux-image-6.8.0-nyx+`).

These components compose orthogonally across the target stack: `syzlang` or Nyx affine bytecode supplies structured inputs, `KCOV` or `Intel PT` supplies edge/comparison telemetry, `KFENCE`/`KASAN` acts as the memory-safety oracle, and `kafl.qemu` provides sub-millisecond snapshot resets.

## Findings

### 1. Resource-Typed `syzlang` Syscall Dependency Graphs (`google/syzkaller`)

Basis: source + documentation

Unstructured byte fuzzers stall on OS system-call boundaries because handles (file descriptors, sockets, BPF maps, `io_uring` rings) are opaque runtime tokens whose validity is determined across sequential calls. `google/syzkaller` solves this via a declarative static type system compiled into AST tables (`prog/types.go`):
- **Resource Lineage (`ResourceDesc` & `ResourceType`)**: `prog/types.go:332-347` defines `ResourceDesc` with `Name`, a subtype chain `Kind []string` (e.g., `fd -> sock -> sock_in`), invalid sentinel `Values []uint64` (returned by `Default()`), and constructor syscalls `Ctors []ResourceCtor`. Every output or input reference is typed via `ResourceType` (`ArgFormat BinaryFormat`, `Desc *ResourceDesc`) and tracked by `Ref uint32` (`prog/types.go:205`).
- **Directional Memory & Length Invariants**: `docs/syscall_descriptions_syntax.md` specifies explicit pointer directionality (`ptr[in, ...]`, `ptr[out, ...]`, `ptr[inout, ...]`), dependent byte/element counts (`len`, `bytesize`, `bitsize`), and union/flag discriminators. Mutators preserve well-typed producer–consumer edges while splicing calls, preventing arbitrary bit flips from immediately invalidating file descriptors or struct sizes.
- **Comparison with Nyx Affine Bytecode DAGs**: Whereas `syzlang` allows aliasing a generated `ResourceType` handle across multiple calls (risking deliberate or accidental double-close during mutation), Nyx (`Schumilo et al., USENIX Security 2021`) encodes stateful hypervisor interactions as directed acyclic graphs governed by **affine types**, guaranteeing statically that consumed resource nodes cannot be duplicated after destruction unless modeled via an explicit clone operation.

### 2. Interrupt-Isolated Coverage (`KCOV_REMOTE_ENABLE`) and Guarded Sampling (`KFENCE`)

Basis: source + execution

Kernel coverage collection fails when execution migrates off the invoking user process onto workqueues, RCU callbacks, or softirqs (such as USB/network packet reception), while exhaustive sanitizer instrumentation is often too slow for continuous fleet or high-throughput target execution. Linux `v6.12` addresses both problems with orthogonal kernel mechanisms:

1. **Task- and Handle-Scoped Coverage (`kernel/kcov.c`, `executor/executor_linux.h`)**:
   - Compiler instrumentation inserts calls to `notrace void __sanitizer_cov_trace_pc(void)` (`kernel/kcov.c:209`), writing instruction pointers into a per-instance ring buffer (`KCOV_INIT_TRACE32`/`64`).
   - When a worker thread (`kthread`) or softirq executes asynchronously, raw per-task tracking misses the coverage or attributes background noise to unrelated syscalls. `KCOV_REMOTE_ENABLE` (`kernel/kcov.c:630, 730`) accepts `struct kcov_remote_arg` (`executor/executor_linux.h:76-84`) containing `common_handle` (task-scoped background threads spawned by the process) and `handles[]` (global subsystem IDs such as `KCOV_SUBSYSTEM_USB = 0x01ull << 56` combined with `procid + 1` at lines `94-95` and `249-250`).
   - Kernel subsystems bracket asynchronous work with `kcov_remote_start(u64 handle)` (`kernel/kcov.c:849`) and `kcov_remote_stop(void)` (`kernel/kcov.c:994`), acquiring `local_lock_irqsave(&kcov_percpu_data.lock)` and guarding against nested task/softirq re-entry (`t->kcov_softirq`, lines `870-883`). This ensures each fuzzing worker observes deterministic causal coverage without cross-VM background interference.
2. **Sampled Guard-Page Oracle (`mm/kfence/core.c`, `lib/Kconfig.kfence`)**:
   - `KASAN` maintains a `1/8` virtual shadow map and checks every load/store, catching deterministic spatial and temporal bugs at high CPU/RAM cost.
   - `KFENCE` instead intercepts `__kfence_alloc` (`mm/kfence/core.c:1065`) only when a timer-armed allocation gate fires (`CONFIG_KFENCE_SAMPLE_INTERVAL`, default `100 ms`), and only for non-DMA allocations with `size <= PAGE_SIZE` (`lines 1077-1089`).
   - `kfence_guarded_alloc` (`mm/kfence/core.c:413`) allocates an object slot from a bounded freelist (`CONFIG_KFENCE_NUM_OBJECTS`, default `255`), randomizes left- vs. right-alignment (`random_right_allocate = get_random_u32_below(2)` at line `420`) to catch either underflows or overflows via hardware page faults on the surrounding unmapped guard pages (`2*N + 1` total `4 KiB` pages = `2,044.0 KiB` for `N=255`). Freed objects are page-protected to trap temporal use-after-free faults with exact allocation/free stack traces.

| Oracle Mechanism | Fault Detection Model | Spatial Alignment Trade-off | Memory Footprint (Default) | Runtime Cost |
| :--- | :--- | :--- | :--- | :--- |
| `KASAN` (inline shadow) | Deterministic per-access shadow byte check | Byte-granular redzones (`8 B` shadow granularity) | ~12.5% of kernel RAM + quarantine | High (~2x–3x CPU overhead) |
| `KFENCE` (`v6.12`) | Hardware MMU page fault on sampled slots | Page-edge random left/right align (`OOB` only on right/left side per sample) | Fixed `2,044.0 KiB` (`511` x `4 KiB` pages for `255` objects) | Near-zero (`<1%` CPU via static keys / timer gate) |

### 3. Input-to-State (`I2S`) Comparison Solving (`RedQueen` / `CmpLog`)

Basis: normative + source + execution

Symbolic execution solves multi-byte magic checks and checksums precisely, but path explosion and environment modeling stall on kernels and complex parsers. `REDQUEEN` (`Aschermann et al., NDSS 2019`, `DOI: 10.14722/ndss.2019.23371`) and its `AFL++` `CmpLog` implementation (`AFLplusplus/AFLplusplus`) replace symbolic path constraints with lightweight taint-free correspondence matching:
- **Trace-Preserving Entropy Maximization (`colorization`)**: `input_to_state_stage` (`src/afl-fuzz-redqueen.c:3270`) invokes `colorization` (`line 498`) to mutate input spans toward random high-entropy bytes while verifying via `common_fuzz_stuff` that the coverage bitmap (`afl->fsrv.trace_bits`, ignoring `unstable` bytes) matches `baseline`. This transforms zero-padded or repetitive input spans into distinct byte signatures so logged runtime operands uniquely identify input byte offsets.
- **Comparison Map Telemetry (`include/cmplog.h`)**: Compiler instrumentation writes runtime comparison instruction and `memcmp`/`strcmp` operands into `struct cmp_map` (`lines 137-143`), indexed by `CMP_MAP_W = 65536` hash buckets with ring depth `CMP_MAP_H = 32` (`lines 39-40`). Each `struct cmp_header` (`2 B`) tracks `hits:6`, `shape:5`, `type:1`, `attribute:4`; each `struct cmp_operands` (`72 B` packed: eight `u64` operand words up to 256-bit plus `occurrence` and `unused` `u32`s) records observed values.
- **Direct & Transformational Patching**: When an input byte sequence (verbatim, endian-swapped, or arithmetically offset) matches operand `v0` (`v1`), `RedQueen` patches `v1` (`v0`) directly into the corresponding input bytes. Two-stage colorization isolates checksum guards: if the execution breaks checksum validation first, mutating only the checksum region restores the path before solving inner checks.

Analytical geometry probing confirms two scaling bounds of `struct cmp_map`: its packed fields occupy **`151,519,232` bytes (`144.500 MiB`)** per shared map (`144.000 MiB` in `log[65536][32]`), and hash-indexed site selection (`W = 65536`) reaches **`P(>=1 collision) = 0.999529`** (`7.62` expected colliding pairs) by just `K = 1,000` distinct instrumented comparison sites, explaining why `AFL++` reserves `site_ids[CMP_MAP_W]` to detect and disambiguate colliding comparison sites.

### 4. Hardware-Trace & Dirty-Ring Micro-Snapshot Hypervisor Fuzzing (`kAFL` / `Nyx`)

Basis: source + documentation

Fuzzing ring-0 OS kernels, SMM firmware, or hypervisor devices from the outside eliminates target OS dependency on `KCOV`, at the cost of hardware control-flow decoding and VM state reset latency:
- **Intel PT Bitmap Reconstruction (`kafl.libxdc`)**: Intel Processor Trace records compressed conditional-branch bitstreams (`TNT` packets) and indirect branch targets (`TIP` packets) in hardware without code instrumentation. Standard disassemblers are far too slow for fuzzing throughput; `libxdc` (`libxdc.h:55-58`) initializes with guest page-fetch callbacks (`libxdc_init(filter, page_cache_fetch_fptr, ..., bitmap_ptr, bitmap_size)`) and executes `libxdc_decode` over cached disassembled basic-block transitions to populate edge bitmaps at native decoding speeds.
- **Incremental Page Restoration (`kafl.qemu`)**: Booting a full OS per input limits throughput to single-digit executions per second. `nyx/fast_vm_reload.c` (`lines 70-155`) initializes shadow physical RAM and hardware-assisted dirty-page tracking via `RELOAD_MEMORY_MODE_FDL` (`nyx_fdl_init`) or `RELOAD_MEMORY_MODE_DIRTY_RING` (`nyx_dirty_ring_init`) plus `memory_global_dirty_log_start()`. On each execution reset, `fast_snapshot_restore_operation` (`line 123`) copies back only the `num_dirty_pages` `4 KiB` guest pages modified during that run (`nyx_snapshot_nyx_fdl_restore`, `line 137`), keeping snapshot resets proportional to working-set mutation rather than total guest RAM.

### 5. Six-Level Performance & Resource Footprint Analysis (L1–L6)

Basis: source + documentation + execution + derived

| Level | `syzkaller` (`syzlang` + `KCOV`) | `AFL++` (`RedQueen` / `CmpLog`) | `kAFL` / `Nyx` (`Intel PT` + Dirty Ring) | `KFENCE` (Production Oracle) |
| :--- | :--- | :--- | :--- | :--- |
| **L1: Authoring Velocity** | High initial spec effort (~100s–1,000s LoC declarative `syzlang` per subsystem); strong reuse across kernel versions; suitable for automated grammar extraction. | Minimal (`0` grammar LoC for binary targets; flag `-c` / `AFL_LLVM_CMPLOG=1` at compile time). | Medium: requires hypercall harness/bootstrap agent (`nyx_api.h`) or affine-typed Nyx spec for multi-step devices. | Zero per-subsystem authoring (`Kconfig` toggle); debug requires triage of rare stack traces. |
| **L2: Toolchain Build** | Fast Go toolchain build (`syz-manager`, `syz-sysgen` seconds); target Linux kernel build + `CONFIG_KCOV` minutes. | Moderate C/LLVM pass compilation (`SanitizerCoverageLTO` + `CmpLog` runtime). | Heavy initial stack: custom QEMU (`kafl.qemu`), `libxdc`, Capstone, and modified KVM kernel (`6.8.0-nyx+`). | Standard kernel compile; negligible build delta. |
| **L3: Compilation & Prep** | `syz-sysgen` compiles text grammars into Go AST tables in seconds; VM image spin-up seconds. | `CmpLog` instrumentation doubles comparison sites & build link time under LTO; `colorization` adds `O(2 * len)` baseline runs per queue entry. | One-time VM boot to hypercall snapshot boundary (`fast_reload_create_in_memory`), then zero per-run boot latency. | Boot-time pool init (`kfence_init`), zero per-run prep. |
| **L4: Execution Throughput** | `~10^1–10^3` exec/s per VM instance (syscall IPC + kernel execution + QEMU/KVM overhead). | `~10^3–10^4` exec/s (forkserver/persistent mode); `CmpLog` instrumented shadow binary runs ~1.5x–3x slower than raw coverage binary. | `~10^3–1.7 x 10^4` exec/s (`Schumilo et al.`) via `4 KiB` dirty-ring page resets and `libxdc` PT packet caching. | `<1%` CPU overhead; `100 ms` default sampling misses low-frequency bugs on short runs (`P=0.632` at `10^4` triggers when `p=10^-4`). |
| **L5: Certificate / Repro Verification** | `syz-repro` / C reproducer replay takes seconds–minutes due to kernel concurrency & non-determinism. | Deterministic single-input replay in milliseconds (`afl-showmap` / crash replay). | Fast deterministic snapshot replay in sub-milliseconds (unless guest timer/IRQ state drifts). | Exact hardware fault report (`BUG: KFENCE`) emitted immediately on guard access; non-deterministic reproduction unless sampled again. |
| **L6: RAM, Disk & Binary Footprint** | Multi-GB VM images + `KCOV` per-worker `mmap` buffers (`cover_t`); `KASAN` consumes ~12.5% guest RAM. | `struct cmp_map` uses **`144.500 MiB`** packed SHM (`151,519,232 B`) plus `struct cmp_pass_stat` (`8 B x 65536 = 512 KiB`) and edge bitmap (`64 KiB+`). | Host shadow snapshot RAM + dirty-ring page buffers + raw Intel PT ring (`MiB`s per vCPU). | Fixed **`2,044.0 KiB`** (`511` x `4 KiB` pages for `255` objects) + metadata array. |

### 6. Human Comprehensibility (C1) and Conceptual Simplicity / Model Refinement (C2)

Basis: derived

- **C1 (Human Comprehensibility & Diagnostic Ergonomics)**:
  - *Working-memory burden*: `syzlang` isolates pointer shapes, struct layouts, and handle typing into readable declarative syntax, making syscall contracts reviewable independently of `syz-executor` C code. Conversely, `Intel PT` decoding failures (packet `OVF` buffer overflows, `CR3` filtering mismatches) and asynchronous `KCOV` worker race attribution create steep nonlocal debugging costs because hardware traces omit data values and concurrent execution interleavings are non-reproducible.
  - *Diagnostic clarity*: `KFENCE` and `KASAN` produce immediately human-auditable allocation/free stack traces pinpointing spatial vs. temporal violations, whereas `AFL++` `CmpLog` stalls silently when comparison-site hash collisions (`W=65536`) or un-colorized length/checksum dependencies overwrite bucket entries (`CMP_MAP_H=32`).
- **C2 (Conceptual Simplicity & Universal Model Refinement)**:
  - *Separating invariants from hardware/OS accidents*: `ioctl` struct layouts (`kcov_remote_arg`), `CMP_MAP_W` modulo buckets, Intel PT `TNT`/`TIP` packet compression, and KVM `FDL`/dirty-ring page tables are realization quirks rather than fuzzing semantics.
  - *Universal algebraic decomposition (Felleisen / Ousterhout)*: All four systems factor cleanly into three orthogonal deep modules:
    1. **Typed Linear/Affine Interaction Algebra**: Unifies `syzlang` resource handles and `Nyx` DAGs as a single typed resource-state graph where `syzlang`'s `ResourceDesc` aliasing is refined by Nyx's affine consumption discipline (preventing unintended use-after-close unless explicit borrow/dup edges are declared).
    2. **Incremental Reversible State Substrate**: Captures `Nyx`/`kafl.qemu` dirty-page deltas (or forkserver CoW pages) behind a pure `(snapshot, diff-apply, reset)` interface independent of hardware virtualization vs. userspace `fork()`.
    3. **Relational Telemetry Stream**: Unifies `KCOV` control-flow PCs, `Intel PT` branches, and `CmpLog` operand pairs as an abstract `(site_id, branch_taken, observed_operands)` observation stream, exposing why `RedQueen` fails on one-way cryptographic hashes (no invertible algebraic correspondence between operand and input) without embedding solver hacks inside the tracer.

## Boundaries

- **Known not to apply**:
  - `RedQueen` / `CmpLog` cannot invert cryptographic hash functions, PRNGs, or non-injective compression transforms where `colorization`-mutated input bytes have no syntactic equality or simple arithmetic offset correspondence with runtime comparison operands.
  - `KFENCE` does not provide deterministic bug detection for single-run unit/fuzz tests; with `p_alloc = 10^-4`, a single execution detects a heap violation with probability `0.0001`, requiring sustained uptime or `KASAN` for deterministic coverage.
  - `kAFL`/`kafl.qemu` Intel PT and KVM dirty-ring modes do not apply to non-x86 architectures (e.g., `aarch64` or `riscv64`) or unprivileged container environments lacking `/dev/kvm` and VMX PT support.
- **Not examined**:
  - Empirical execution benchmarks across live target kernels (throughput ranges in L4 are drawn from upstream paper claims and architectural analysis rather than fresh VM runs on local hardware).
  - Binary-only QEMU/FRIDA `CmpLog` emulation overhead relative to LLVM LTO compile-time `CmpLog`.
- **Unsupported**:
  - `syzlang` natively models resource construction and typing without linear/affine uniqueness enforcement in its type checker; preventing premature `close()` on shared handles relies on runtime mutator heuristics and `isDefaultArg` checks rather than compile-time affine rejection.
  - `libxdc` decodes Intel PT instruction traces strictly for x86/x86-64 binaries and requires host memory callbacks for target code pages (`page_cache_fetch_fptr`), failing with `PAGE_FAULT` (`libxdc_get_page_fault_addr`) if guest pages are swapped or unmapped.

## Evidence

- `google/syzkaller` @ `f836d1190fca3bb4b2827b9f2081318a0edcc13a`:
  - `prog/types.go` (`Ref` at line 205; `ResourceDesc`, `ResourceCtor`, `ResourceType` at lines 332–373).
  - `docs/syscall_descriptions_syntax.md` (`syscallname` grammar, `ptr`/`len`/`flags`/`const` rules).
  - `executor/executor_linux.h` (`struct kcov_remote_arg` lines 76–84, `KCOV_REMOTE_ENABLE` line 89, `kcov_remote_handle` line 99, `cover_open` lines 154–255).
- `torvalds/linux` @ `adc218676eef25575469234709c2d87185ca223a` (`v6.12`):
  - `kernel/kcov.c` (`__sanitizer_cov_trace_pc` line 209, `KCOV_REMOTE_ENABLE` lines 630/730, `kcov_remote_start` lines 849–885, `kcov_remote_stop` line 994).
  - `mm/kfence/core.c` (`CONFIG_KFENCE_NUM_OBJECTS` line 122, `kfence_guarded_alloc` lines 413–445, `__kfence_alloc` lines 1065–1095) and `lib/Kconfig.kfence` (default `KFENCE_SAMPLE_INTERVAL=100`, `KFENCE_NUM_OBJECTS=255`).
- `AFLplusplus/AFLplusplus` @ `d798677805de81b50aa8f45beb0342ae1617b9d8`:
  - `include/cmplog.h` (`CMP_MAP_W=65536`, `CMP_MAP_H=32`, `struct cmp_header`, `struct cmp_operands`, `struct cmp_map` lines 39–144).
  - `src/afl-fuzz-redqueen.c` (`colorization` lines 498–555, `input_to_state_stage` lines 3270–3320).
  - Paper: C. Aschermann, S. Schumilo, T. Blazytko, R. Gawlik, T. Holz, *REDQUEEN: Fuzzing with Input-to-State Correspondence*, NDSS 2019 (`DOI: 10.14722/ndss.2019.23371`).
- `IntelLabs/kAFL` @ `b939b03ddd5734216c23de406f13fe6a35bf0a35`, `IntelLabs/kafl.qemu` @ `61ac92576db3573ddda9c0d0e3b55ac2a28ae403` (`v0.8`), `IntelLabs/kafl.libxdc` @ `a4f6dcfe3c03c8e1fa1ddd56f8d8c58b91952543` (`v0.2`):
  - `deploy/intellabs/kafl/roles/{fuzzer,qemu,libxdc,kernel}/defaults/main.yml` (`v0.6.2`, `v0.8`, `v0.2`, `6.8.0-nyx+`).
  - `nyx/fast_vm_reload.c` (`fast_snapshot_init_operation` lines 70–120, `fast_snapshot_restore_operation` lines 123–155).
  - `libxdc.h` (`libxdc_init`, `libxdc_decode`, `libxdc_get_page_fault_addr` lines 55–59).
  - Papers: S. Schumilo et al., *kAFL: Hardware-Assisted Feedback Fuzzing for OS Kernels*, USENIX Security 2017; *Nyx: Greybox Hypervisor Fuzzing using Fast Snapshots and Affine Types*, USENIX Security 2021.
- Analytical probe executed (`python3` on 2026-11-19):
  ```text
  $ python3 - <<'EOF'
  import math
  W, H, HDR, OPS = 65536, 32, 2, 72
  total = W * HDR + W * H * OPS + W * 4 + W * 2
  print(f"cmp_map total = {total} B ({total / 1048576:.3f} MiB)")
  for k in (256, 1000, 5000):
      p_none = math.prod((W - i) / W for i in range(k))
      print(f"K={k}: P(collision)={1 - p_none:.6f}, E[pairs]={k*(k-1)/(2*W):.2f}")
  for n in (255, 1024):
      b = (2 * n + 1) * 4096
      print(f"KFENCE N={n}: {2*n+1} pages = {b} B ({b/1024:.1f} KiB)")
  for m in (1000, 10000, 50000):
      print(f"KFENCE p=1e-4, M={m}: P(catch)={1 - (1 - 1e-4)**m:.5f}")
  EOF
  cmp_map total = 151519232 B (144.500 MiB)
  K=256: P(collision)=0.392678, E[pairs]=0.50
  K=1000: P(collision)=0.999529, E[pairs]=7.62
  K=5000: P(collision)=1.000000, E[pairs]=190.70
  KFENCE N=255: 511 pages = 2093056 B (2044.0 KiB)
  KFENCE N=1024: 2049 pages = 8392704 B (8196.0 KiB)
  KFENCE p=1e-4, M=1000: P(catch)=0.09517
  KFENCE p=1e-4, M=10000: P(catch)=0.63214
  KFENCE p=1e-4, M=50000: P(catch)=0.99326
  ```

## Revalidation

1. **Source Invariants**: Fetch `prog/types.go`, `kernel/kcov.c`, `mm/kfence/core.c`, `include/cmplog.h`, `nyx/fast_vm_reload.c`, and `libxdc.h` at a target commit and verify whether `CMP_MAP_W`, `struct cmp_operands`, `KCOV_REMOTE_ENABLE`, `CONFIG_KFENCE_NUM_OBJECTS`, or `RELOAD_MEMORY_MODE_DIRTY_RING` changed layout or synchronization locks.
2. **Telemetry Geometry Probe**: Re-run the embedded Python snippet in `## Evidence` substituting updated `CMP_MAP_W`, `CMP_MAP_H`, `sizeof(cmp_operands)`, or `CONFIG_KFENCE_NUM_OBJECTS` constants to recompute memory budgets and collision rates in `<1 s`.
3. **Kernel/VM Verification**: On a host with KVM and Intel PT enabled, check `/sys/kernel/debug/kfence/stats` and `kcov_remote_arg` `ioctl` coverage isolation under concurrent `syz-executor` workers to validate runtime behavior.
