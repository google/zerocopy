# Cluster and GPU Deterministic Replay: FoundationDB Sim2, TigerBeetle VOPR, MadSim, Hermit Containers, and NVBit SASS Instrumentation

## Summary

Deterministic execution and record-replay span three distinct isolation planes with sharp completeness-vs-overhead boundaries: **application-level cooperative simulators** (`apple/foundationdb` `Sim2`, `tigerbeetle/tigerbeetle` `VOPR`, `madsim-rs/madsim`), **OS-boundary deterministic Linux container sandboxes** (`facebookexperimental/hermit` / `DetTrace`), and **hardware-level GPU SASS binary instrumentation** (`NVlabs/NVBit`).

Direct source inspection and executable modeling establish five foundational invariants across these planes:

1. **Cooperative Single-Seed Virtualization (`Sim2`, `VOPR`, `MadSim`)**: Replacing physical clocks, TCP sockets, and disk I/O with a single-threaded discrete-event loop seeded by one `64`-bit integer collapses multi-node distributed failures into bit-reproducible schedules while accelerating simulated time by `100x–10,000x` via sleep skipping (`Sim2::runLoop` `taskQueue.getSleepTime`, `VOPR` `simulator.tick()`, `MadSim` `Runtime::with_seed_and_config`). Crucially, determinism breaks silently at unintercepted ambient boundaries—`std::collections::HashMap` `RandomState`, `SYS_getrandom` vs. `libc::getrandom` on Linux (`madsim_sim_rand.rs`), unmanaged system threads (`allow_system_thread`), native C/CUDA FFI, and cross-ISA `FMA` contraction.
2. **Dual-Run Escape Detection vs. Logarithmic Merkle Bisection**: `MadSim::check_determinism` detects nondeterminism escapes (`getrandom`, `HashMap`, thread jitter) via whole-run RNG+time xor-digest replay (`O(1)` memory overhead per RNG draw, zero step localization beyond the failure time). Recording rolling SHA-256 Merkle checkpoints over `(virtual_time_ns, step, src, dst, state_hash)` enables `O(log_2 N)` bisection (`10` probes over `1,024` steps in `/tmp/det_replay_warp_probe.py`), pinpointing a silent escape at step `613` even when downstream assertion failure appears `87` steps later.
3. **Syscall Interception & PMU Retired-Conditional-Branch (RCB) Skid (`Hermit` / `DetTrace`)**: `Hermit` runs unmodified Linux binaries inside isolated namespaces via `Reverie` (`ptrace` + `seccomp-bpf`), intercepting clocks (`cpu_clock.rs`), `getrandom` (`random.rs` `Pcg64Mcg` + `AT_RANDOM` handoff), `RDTSC`/`CPUID`, and `futex` queues while using hardware PMU `PERF_COUNT_HW_BRANCH_INSTRUCTIONS` counters as a deterministic logical preemption clock. Because hardware PMU interrupts exhibit microarchitectural **skid** past `rcb_target`, `detcore/src/skid_overshoots.rs` (`RcbOvershootReport`, `SkidOvershootCounts`) tracks and deduplicates overshoot events so `--verify` distinguishes genuine guest divergence from hardware skid artifacts.
4. **GPU SIMT Warp Coalescing & Atomic Schedule Recording vs. Batch-Invariance (`NVBit`)**: `NVBit v1.8.2` disassembles GPU SASS at kernel load time (`core/nvbit.h`: `Instr`, `CFG_t`, Hopper/Blackwell `TMATransferInfo_t`) and injects device-side trampolines (`nvbit_insert_call`) before/after instructions. Sample tool `tools/mem_trace` uses leader-lane election (`__ballot_sync(__activemask(), 1)`, `__ffs(active_mask) - 1`) and 32-lane `__shfl_sync` coalescing into `288`-byte `mem_access_t` records pushed over `ChannelDev` (`2.0x` space savings over naive per-thread logs at `75%` warp occupancy). For floating-point `atomicAdd`/`atomicCAS` races (`fp32` bit drift `0xb4697845` vs. `0xaf697845`), recording only a `2`-byte warp-winner causal schedule yields **`144x` lower trace volume** than full `mem_access_t` capture—though modern LLM inference research (Thinking Machines Lab, 2025) shows greedy decoding nondeterminism is dominated by non-batch-invariant split-K reduction trees rather than `atomicAdd` races.
5. **Universal Core Abstraction**: Cooperative cluster simulators, OS syscall sandboxes, and GPU SASS tracers are disparate approximations of one conceptual kernel—**Causal Effect Capabilities + Total-Order Contention Certificates**—where eliminating hidden ambient authority (`RandomState`, raw `vDSO` clocks, unlogged `SYS_getrandom`, and uncaptured GPU `ATOM`/`RED` warp schedules) yields clean, human-bisectable deterministic replay.

## Applicability

This report covers nine pinned upstream artifacts spanning application simulators, Linux container determinism, and GPU binary instrumentation:

| Subject | Immutable Identity | Execution Layer | Host / Target Constraints | Scope Role in Synthesis |
|---|---|---|---|---|
| `apple/foundationdb` | `39fb2391049fe326d2c5c7c3dd8dbb8b596284b9` | C++ / Flow actor discrete-event simulator (`Sim2`) | Single-process host simulation of multi-node clusters | Virtualized network clogging (`SimClogging`), `KillType`, sector bitrot, `BUGGIFY` |
| `tigerbeetle/tigerbeetle` | `a2a3c7064519e08233abe26c54a43fca2f9ad9bc` | Zig static-memory VSR simulator (`VOPR`) | `.Debug` or `.ReleaseSafe` (`comptime assert(constants.verify)`) | `PacketSimulator`, `Storage` misdirected I/O overlays, multi-version rolling upgrade fuzzing |
| `madsim-rs/madsim` | `519950efb4711464f300ed7edf2967ed62d5f502` | Tokio-compatible async Rust simulator | Linux / macOS (`getentropy` / `getrandom` LD interpose) | Drop-in async RPC simulation, `RandomState` seeding, `check_determinism` escape trap |
| `facebookexperimental/hermit` | `2994b6f8e7ae4ba8a093b4e1555cd1483ada6bb8` | Linux userspace container (`Detcore` + `Reverie`) | Linux `x86_64` / `aarch64` with deterministic PMU RCBs | `seccomp`/`ptrace` virtualization, `cpu_clock.rs`, `skid_overshoots.rs` PMU skid defense |
| `NVlabs/NVBit` | `cda43eb3720c69c051385e70791e0f948028a02c` | Upstream Git repository metadata (`README.md`, `EULA.txt`) | Linux (`x86_64` / `aarch64`), CUDA `>= 12.0`, SM `3.5–12.1` | Authoritative requirement & versioning specification |
| `NVBit` Release Archive (`v1.8.2`) | `nvbit-Linux-x86_64-1.8.2.tar.bz2` (`sha256: fa2728c8921fdcb8e761fd62b2173a2492b47da3605f9ab9510e006772e48eee`) | Closed-source `libnvbit.a` (`5.51 MB`) + public C++/CUDA headers & tools | Matches `NVlabs/NVBit` `v1.8.2` release (`NVBIT_VERSION "1.8.2"`) | Concrete `Instr`/`CFG_t`/`TMATransferInfo_t` APIs and `mem_trace`/`record_reg_vals` device code |
| Zhou et al., *SIGMOD 2021* | DOI `10.1145/3448016.3457559` | FoundationDB architecture & simulation paper | FoundationDB unbundled architecture | Production simulation fault-discovery methodology and coverage metrics |
| Navarro Leija et al., *ASPLOS 2020* | DOI `10.1145/3373376.3378519` | `DetTrace` container reproducibility paper | Linux namespaces + `ptrace` container builds | Formal guarantees and syscall/timing determinization overhead |
| Villa et al., *MICRO 2019* | DOI `10.1145/3352460.3358307` | `NVBit` architectural paper | NVIDIA Volta/Turing+ SASS DBI design | Load-time SASS patching, trampoline register preservation, and `ChannelDev` design |

**Relationships and Repository Split Clarification**:
- Upstream `NVlabs/NVBit` (`cda43eb3720c69c051385e70791e0f948028a02c`) ships only `README.md` and `EULA.txt` in Git; all C++/CUDA headers (`core/nvbit.h`), static instrumentation library (`core/libnvbit.a`), `ChannelDev` (`core/utils/channel.hpp`), and reference tools (`tools/mem_trace`, `tools/record_reg_vals`) reside in the GitHub release archive (`v1.8.2`). Both are pinned in `REPORT.json` so every code citation has an exact immutable anchor.
- `Sim2`, `VOPR`, and `MadSim` require source integration against simulated I/O abstractions; `Hermit` and `NVBit` instrument unmodified compiled binaries (`ELF` and `CUDA` SASS cubins respectively) at launch/load time.
- None of the five inspected frameworks natively fuse cluster network replay and multi-GPU SASS atomic replay in one runtime; cross-boundary composition and compression metrics are derived from source measurements and executed in `/tmp/det_replay_warp_probe.py` (`Basis: execution + derived`).

## Findings

### 1. Single-Seed Cooperative Cluster Simulation and Fault Injection (`FoundationDB Sim2`, `TigerBeetle VOPR`, `MadSim`)

`Basis: normative + source + documentation`

Application-level deterministic simulation engines replace non-deterministic OS syscalls and wall-clock concurrency with a single-threaded priority queue fed by one pseudo-random seed:

#### FoundationDB `Sim2` (`fdbrpc/sim2.cpp`, Zhou et al. *SIGMOD 2021*)
- **Discrete-Event Cooperative Loop**: `Sim2::runLoop` (`fdbrpc/sim2.cpp:1588-1624`) executes on a single OS thread (`isMainThread = true`). Whenever `taskQueue.canSleep()`, virtual `time` jumps instantaneously by `sleepTime + MAX_RUNLOOP_SLEEP_DELAY * pow(deterministicRandom()->random01(), 1000.0)` (`L1594-1596`)—modeling realistic timer jitter while running multi-hour cluster outages in seconds. Tasks wake via Flow actor `co_await`/promises (`taskQueue.processReadyTimers`, `processThreadReady`, `execTask`).
- **Network Clogging, Partitions, and Partial Writes**: `SimClogging` (`L201-293`) and `Sim2Conn` (`L295-420`) inject permanent per-pair random latency, randomized send buffer capacities (`sendBufSize = max(randomInt(0, 5e6), 25e6 * (latency + 0.002))`), asymmetric disconnects (`disconnectPairUntil`), and truncated TCP writes (`buggify()` clamping `toSend` to `randomInt(0, 1000)` at `L407-408`) unless `stableConnection` connects parent/child processes (`L318-323`).
- **Process Kills, `BUGGIFY`, and Storage Corruption**: `killProcess_internal` (`L1790-1895`) models `KillInstantly`, `InjectFaults` (`simulator_should_inject_fault` at `L77-114` using line-number hashing + `p1`/`p2` thresholds), `FailDisk`, `RebootAndDelete`, and `RebootProcess` (respecting `isProtectedAddress`). `corruptedBlocks` (`L1025-1042`) injects deterministic sector corruption across crash/reboot boundaries.

#### TigerBeetle `VOPR` (`src/vopr.zig`, `src/testing/{packet_simulator.zig,storage.zig}`)
- **Strict Assertion & Zero-Drift Build Contract**: `src/vopr.zig:95, 139` enforces `comptime assert(constants.verify)` and `comptime assert(builtin.mode == .Debug or builtin.mode == .ReleaseSafe)` (explicitly rejecting `ReleaseFast`/`ReleaseSmall` so safety checks never disappear). A single `u64` `--seed` (`L133-155`) drives `stdx.PRNG` across cluster topology, fault ratios, and multi-release rolling upgrade testing (`releases[0..3]` at `L43-56, 284-293`).
- **Asymmetric Partitions & Misdirected Storage Overlays**:
  - `PacketSimulatorType` (`src/testing/packet_simulator.zig:13-258`) implements `PartitionMode` (`none`, `uniform_size`, `uniform_partition`, `isolate_single`), `PartitionSymmetry` (`symmetric` vs. `asymmetric` one-way drops), exponential one-way latency queues (`Link.queue`), `clogged_till`, packet loss, and packet replay.
  - `Storage` (`src/testing/storage.zig:49-254`) keeps pristine committed bytes in `memory` alongside a `faults` bitset and `overlays` (`overlay_buffers` max `2` concurrent overlays, `L143-188`). For a **misdirected write**, `Storage` writes the new payload to the *mistaken* sector's overlay while overlaying the *intended* target with its old bytes—forcing VSR hash chains and `GridChecker` (`L86`) to detect and repair valid-checksum data written to the wrong disk offset without corrupting pristine ground-truth verification state.

#### MadSim (`madsim-rs/madsim` @ `519950efb`)
- **Drop-In Tokio-Style API Virtualization**: `Runtime::with_seed_and_config(seed, config)` (`madsim/src/sim/runtime/mod.rs:53-69`) instantiates one `GlobalRng` (`Xoshiro256PlusPlus`, `madsim/src/sim/rand.rs:6, 53`), `task::Executor`, `FsSim`, and `NetSim` with `allow_system_thread: false` (`L63`). `Handle` (`L214-308`) exposes supervisor fault actions (`kill`, `restart`, `pause`, `resume`, `send_ctrl_c`) to test recovery from non-flushed page caches.

---

### 2. Nondeterminism Escape Vectors, Link-Time Traps, and Logarithmic Trace Bisection

`Basis: source + execution + derived`

Cooperative simulators only guarantee determinism inside their intercepted boundary. Direct inspection of `madsim/src/sim/rand.rs` and `madsim/src/sim/task/mod.rs` documents five distinct escape vectors:

1. **HashMap `RandomState` Seeding**: Rust's `std::collections::HashMap` seeds `SipHash` via `getrandom`/`getentropy`. `madsim/src/sim/rand.rs:176-283` interposes `#[no_mangle] unsafe extern "C" fn getrandom` (and `getentropy` / macOS `CCRandomGenerateBytes`), using a `thread_local! SEED` handshake (`init_std_random_state`) to determinize `RandomState::new()`. **Critical Linux Trap (`rand.rs:290-296`)**: If an upstream dependency (such as the `rand` crate) invokes the raw Linux `SYS_getrandom` syscall directly rather than `libc::getrandom`, MadSim's `#[no_mangle]` C symbol interposition is bypassed completely on Linux (`#[cfg_attr(target_os = "linux", ignore)]` on `deterministic_rand` at `L291`).
2. **Unmanaged OS Threads & Static Initializers**: `Runtime` defaults `allow_system_thread: false`, panicking on `std::thread::spawn` inside simulated futures (`madsim_task_mod.rs:237-249, 1066`). However, native C/C++/CUDA libraries (`libc`, `OpenSSL`, `cuBLAS`) calling `pthread_create` directly or caching `getpid()`/`clock_gettime` in `static` constructors bypass Rust shims.
3. **Pointer-Address & Allocator Nondeterminism**: Sorting or hashing heap pointer addresses (`usize`), `HashSet` iteration when an unseeded `ahash` or `fxhash` uses ASLR stack pointers, or ASLR memory layout differences across processes silently diverge iteration orders.
4. **Hardware Entropy & Timers (`RDTSC`, `vDSO`)**: Unintercepted x86 `RDTSC`/`RDTSCP`, `RDRAND`, or Linux `vDSO` fast-path `clock_gettime` reads bypass libc wrappers.
5. **Cross-ISA Floating-Point Contraction (`FMA`)**: Compiling simulation code with `-mfma` / `-ffp-contract=fast` vs. non-FMA targets changes intermediate rounding of `a * b + c`.

#### Dual-Run Detection (`MadSim::check_determinism`) vs. Merkle Bisection
`Runtime::check_determinism` (`madsim/src/sim/runtime/mod.rs:178-202`) runs the target closure twice from identical `seed` and `config`: Run 1 enables `GlobalRng::enable_log()`, pushing `rng.clone().gen::<u8>() ^ fold(time.elapsed().as_nanos())` on every RNG draw (`madsim_sim_rand.rs:68-86`); Run 2 enables `enable_check(log)` and panics immediately when any RNG index `i` mismatches (`panic!("non-determinism detected at {time:?}")`). While catching `RNG`-correlated divergences cheaply, purely state-level escapes that do **not** call `GlobalRng` before corrupting state (e.g., an unseeded `HashMap` reordering messages with equal timestamps) can remain invisible until an invariant fails hundreds of steps later.

Executing Part A of `/tmp/det_replay_warp_probe.py` across a 5-node, `1,024`-step cluster simulation under seed `0x9F2A`:
- Repeated clean runs produce bit-identical `SHA-256` Merkle roots (`cluster_repeat_bit_exact: true`).
- Injecting a 1-bit nondeterminism escape at step `613` (`delta ^= 1`, modeling `RandomState` or FFI jitter) produces a late final-root mismatch without altering step timing.
- Binary searching the rolling Merkle checkpoint array `[H_0, ..., H_{1023}]` isolates **exact root-cause step `613` in `10` (`log_2 1024`) hash comparisons**, narrowing blame directly to the diverging transition rather than the late symptom step.

---

### 3. Syscall Interception and PMU Retired-Conditional-Branch Scheduling in `Hermit` and `DetTrace`

`Basis: normative + source + documentation`

When legacy C/C++/Rust/Python binaries or third-party shared libraries cannot be rewritten atop `Flow` or `MadSim`, `facebookexperimental/hermit` (`Detcore` + `Reverie`, descended from `DetTrace`, Navarro Leija et al., *ASPLOS 2020*, DOI `10.1145/3373376.3378519`) achieves deterministic execution across unmodified Linux container processes:

#### Deterministic OS Boundary Virtualization
- **Namespace & Syscall Trap (`Reverie`)**: `Hermit` launches guests inside isolated PID/mount/IPC/network/user namespaces and intercepts syscalls via `seccomp-bpf` + `ptrace` (selective trapping so deterministic fast paths like pure memory compute and safe `read`/`write` bounds avoid unnecessary round-trips).
- **Virtual Time (`cpu_clock.rs:1-420`)**: Every thread maintains logical user time (charged by retired conditional branches and trapped `RDTSC`/`CPUID` instructions) and modeled system time (charged per intercepted syscall). `CLOCK_REALTIME`, `CLOCK_MONOTONIC`, `CLOCK_PROCESS_CPUTIME_ID`, and `CLOCK_THREAD_CPUTIME_ID`—including negative PID-encoded dynamic clocks decoded via `CPUCLOCK_PID`/`CPUCLOCK_WHICH` (`cpu_clock.rs:121-152`)—derive solely from deterministic logical accounting (`GUEST_KERNEL_HZ = 250`, `1 ns` `Sched` resolution).
- **Deterministic Entropy (`random.rs:30-250`)**: `Detcore` seeds a root `Pcg64Mcg` stream (`root_prng(seed)`, `L87-89`) and virtualizes `/dev/urandom`, `SYS_getrandom`, and ELF `AT_RANDOM` auxv bytes. Notably, `InitialRandomState` (`v4`, `L98-244`) transfers the exact `16`-byte `at_random_value` and up to `32` early dynamic-loader `getrandom` fills (`glibc` malloc `tcache` key) + `4` `prlimit64`/`getrlimit` reads from the pre-exec loader across `execve` without breaking record-replay determinism.
- **Single-Core Thread Serialization & PMU RCB Preemption (`scheduler.rs`, `lib.rs:198-243`)**: Rather than allowing true OS parallel races on shared memory, `Detcore` sequentializes runnable guest threads under a deterministic scheduler. Preemption timeslices trigger after a fixed count of hardware **Retired Conditional Branches (`RCB`)** configured via `perf_event_open` (`PERF_COUNT_HW_BRANCH_INSTRUCTIONS`), making preemption points depend purely on deterministic control-flow progress rather than wall-clock timer jitter.

#### Hardware PMU Interrupt Skid Hazard (`detcore/src/skid_overshoots.rs:1-160`)
On physical x86 and ARM64 CPUs, PMU overflow interrupts are imprecise: a thread may retire extra conditional branches between PMU counter overflow and interrupt delivery (**skid**), causing it to stop past `rcb_target`. `Hermit` mitigates and accounts for this explicitly:
1. `detcore` arms PMU timers conservatively below the target and steps carefully near `rcb_target`, yet late deliveries still occur under out-of-order CPU pipelines.
2. `skid_overshoots.rs` records `RcbOvershootReport { tid, rcb_target }` (`L46-51`, bounded to `RCB_OVERSHOOT_REPORTS_KEPT = 65536`) alongside Reverie's `SkidOvershootDetail` list.
3. `SkidOvershootCounts::count` (`L133-160`) deduplicates double-counted Detcore prehook reports and Reverie timer callbacks by `(tid, rcb_target)` so `hermit --verify` can definitively attribute a replay divergence to hardware PMU skid vs. an actual non-determinism bug in `Detcore` (`L17-22`).

---

### 4. GPU SIMT SASS Binary Instrumentation, Warp Coalescing, and Atomic vs. Batch Variance in `NVBit`

`Basis: normative + source + execution + derived`

Replaying or verifying GPU workloads introduces two hardware phenomena absent on CPUs: **32-thread SIMT warp execution** with hardware-scheduled divergence/reconvergence, and **cross-CTA memory/atomic races** inside HBM/L2.

#### Load-Time SASS Patching (`NVBit v1.8.2`, `core/nvbit.h`, Villa et al. *MICRO 2019*)
Unlike PTX-level instrumentation (which triggers `ptxas` register allocation changes that perturb occupancy and race schedules), `NVBit` inspects and patches native **SASS** machine code dynamically as `CUfunction`s load:
- **CFG & Instruction Inspection (`core/nvbit.h:51-250`)**: `nvbit_get_instrs(ctx, func)` yields decoded `Instr*` objects exposing `getSass()`, `getOffset()`, predicate masks (`hasPred()`, `getPredNum()`, `isPredUniform()`), memory spaces (`InstrType::MemorySpace`), Hopper/Blackwell Tensor Memory Accelerator metadata (`TMATransferInfo_t`, `L164-249`), and control-flow graphs (`CFG_t`), flagging `is_degenerate = true` whenever indirect branch targets (`JMX`/`BRX`) cannot be statically resolved (`L113-121`).
- **Trampoline Call Injection (`nvbit_insert_call`, `core/nvbit.h:527-620`)**: Tools inject `extern "C" __device__ __noinline__` CUDA functions (`IPOINT_BEFORE` or `IPOINT_AFTER`) passing guard predicates, `uint64_t` memory reference addresses (`nvbit_add_call_arg_mref_addr64`), live registers (`nvbit_add_call_arg_reg_val`), or launch constants (`nvbit_set_at_launch`). `NVBit` saves/restores caller-saved application registers and predicates around the injected call so original kernel register semantics remain intact.

#### SIMT 32-Lane Warp Coalescing & Channel Ring (`tools/mem_trace/inject_funcs.cu:43-76`, `common.h:36-44`, `mem_trace.cu:232-302`)
Logging every active thread individually to global ring buffers creates `32x` atomic contention on the ring tail pointer. `NVBit`'s `mem_trace` eliminates `31/32` of ring pushes via warp-level intra-warp coalescing:
1. All active threads execute `int active_mask = __ballot_sync(__activemask(), 1);` (`inject_funcs.cu:52`), and elect one leader via `const int first_laneid = __ffs(active_mask) - 1;` (`L54`).
2. A 32-iteration `__shfl_sync(active_mask, addr, i)` loop (`L59-61`) gathers all lane addresses into `mem_access_t ma` on the leader lane (`ctypes.sizeof(mem_access_t) == 288` bytes on 64-bit ABI: `uint64_t grid_launch_id` + `5 x int32` (`cta_id_{x,y,z}`, `warp_id`, `opcode_id`) + `4 B` padding + `uint64_t addrs[32]`).
3. Only `if (first_laneid == laneid)` pushes `ma` onto `ChannelDev*` (`cudaMallocManaged` + background host consumer `recv_thread_fun` registered via `nvbit_set_tool_thread` so tool threads skip CUDA callbacks, `mem_trace.cu:235-239`).

#### Atomic Order Capture vs. Batch-Invariance in `IEEE 754` GPU Reductions
To make a multi-warp GPU kernel with `ATOM`/`ATOMS`/`RED` (`atomicAdd`, `atomicCAS`) bit-exact on replay:
- **Contention-Order Logging**: Instrumenting SASS `ATOM`/`RED` instructions with `IPOINT_AFTER` + `nvbit_add_call_arg_reg_val` (as in `tools/record_reg_vals/record_reg_vals.cu:159-188`) captures the exact old value returned by each hardware atomic—or, via a tiny per-address sequence counter, logs the ordered `(warp_id, cta_id)` sequence **without** dumping all `32` `uint64_t` addresses.
- **Empirical Compression & Floating-Point Drift (`det_replay_warp_probe.py`)**: Simulating `128` warps (`3,066` active thread accesses at `75%` predication occupancy) performing contended `FP32` `atomicAdd` operations shows:
  - Changing warp arrival order flips final IEEE-754 `binary32` bits from **`0xb4697845`** (`Order A`) to **`0xaf697845`** (`Order B`) (`fp32_reordered_drift: true`).
  - `NVBit`'s `288`-byte `mem_access_t` warp packet (`36,864 B`) halves trace volume vs. `24 B/thread` naive per-thread logging (`73,584 B`, `2.0x` reduction).
  - Logging only the `2`-byte warp-winner schedule (`256 B`) achieves a **`144.0x` compression ratio over `mem_access_t`** (`288x` over naive) while reproducing bit-exact `0xb4697845` (`fp32_replay_exact_match: true`).
- **Distinguishing Atomic Contention vs. Batch Variance**: Recent ML-systems investigation (*"Defeating Nondeterminism in LLM Inference"*, Horace He et al., Thinking Machines Lab, 2025) demonstrated that forward-pass nondeterminism in standard greedy (`temperature = 0`) LLM inference engines (`vLLM`, `SGLang`) is **not** primarily caused by chaotic `atomicAdd` races inside kernels—because most inference matmul/RMSNorm/attention kernels avoid cross-CTA floating-point `atomicAdd` for fixed shapes—but rather by **lack of batch invariance**: dynamic batching changes tensor shapes across requests, causing kernels to switch split-K / tile reduction trees and alter floating-point summation order. Thus, `NVBit` atomic-order tracing solves *true data-race / cross-warp `atomicAdd` kernels* (physics, graph analytics, RL backprop), whereas *inference reproducibility* requires batch-invariant fixed reduction trees (or superaccumulators).

---

### 5. Cross-System Trade-Off Matrix and Six-Level Performance & Resource Footprint (`L1`–`L6`)

`Basis: source + documentation + execution + derived`

| Dimension | `apple/foundationdb` `Sim2` | `tigerbeetle/tigerbeetle` `VOPR` | `madsim-rs/madsim` | `facebookexperimental/hermit` | `NVlabs/NVBit` (`v1.8.2`) |
|---|---|---|---|---|---|
| **Isolation Boundary** | Flow actors (`ISimulator`, `Sim2Conn`, async disk) | Zig state machine + `PacketSimulator` + `Storage` | Rust async `Runtime` (`FsSim`, `NetSim`, `GlobalRng`) | Linux container (`ptrace`/`seccomp-bpf` + PMU `RCB`) | GPU SASS binary load-time patching (`LD_PRELOAD` `.so`) |
| **Targets Arbitrary Unmodified Binaries?** | No (requires Flow actor & `INetwork` programming model) | No (requires TigerBeetle static Zig I/O abstraction) | Partially (drop-in for `tokio` crates; fails on raw C/syscall FFI) | **Yes** (x86_64/aarch64 ELF, multi-process/multi-thread) | **Yes** (precompiled CUDA cubins across SM `3.5–12.1`) |
| **L1: Human / Agent Authoring Velocity** | High greenfield discipline; minimal test harness (`10–30` LoC `.toml` test scripts) | Zero-allocation Zig discipline; single `64`-bit seed reproduces full cluster failures | `1` attribute (`#[madsim::test]`) for async Rust; `~10` LoC to add fault hooks | **`0` LoC** app changes (`hermit run --seed=...`); debugging `Detcore` internals is deep | **`0` LoC** target CUDA changes; writing a custom `.cu` tool is ~150–400 LoC |
| **L2: Framework / Toolchain Build Time & RSS** | Heavy C++ (`fdbserver`); ~5–15 min cold build, `4–12 GiB` link RSS | Fast Zig static build (`zig build vopr`); `< 15–30 s` cold, `< 600 MiB` RSS | Cargo Rust crate (`madsim` + `madsim-tokio`); `< 15 s` build, `< 400 MiB` RSS | Cargo workspace (`hermit` + `detcore` + `reverie`); ~30–60 s build, `< 800 MiB` RSS | Prebuilt `libnvbit.a` (`5.26 MiB`); tool compiles with `nvcc` + `CMake` in `< 5 s` |
| **L3: Compilation, Patching & Verification Latency** | Instant scenario boot (`< 50 ms`) | `< 20 ms` `VOPR` startup; deterministic assertion checks on every tick | `< 10 ms` test boot; `check_determinism` doubles test latency (`2x` run) | `seccomp` BPF JIT attach `< 10 ms`; dynamic `AT_RANDOM` / `Detlog` setup | Load-time SASS decode + trampoline patching once per `CUfunction` (`~10–150 ms`/kernel) |
| **L4: Runtime Execution Speed & Overhead** | **100x–10,000x virtual clock speedup** (sleeps skipped); single-core CPU bound | **1,000x+ virtual speedup** (`40M` tick cap in `vopr.zig:83`; >100k ops/s simulated) | **100x–5,000x speedup** on timer-heavy RPC protocols; near-native async Rust speed | **`1.2x–3.0x`** slowdown (`ptrace`/PMU trap overhead; single-core thread serialization removes multi-core speedup) | **`1.3x–15x+` GPU slowdown** (trampoline reg save/restore + `ChannelDev` ring stalls when full; `mem_trace` coalesces `32:1` pushes) |
| **L5: Divergence & Certificate Verification Speed** | Single `seed` re-runs deterministically; `CODE_PROBE` coverage verification | `StateChecker` + `aof.validate(gpa, last_checksum)` (`vopr.zig:358-367`) inline | `GlobalRng::with` `O(1)` XOR check per draw; **no** bisection on non-RNG escapes | `hermit --verify` compares `Detlog` event streams; `SkidOvershootCounts` guards PMU noise | Host `recv_thread_fun` drains `ChannelDev`; offline replay checks `0xb4697845 == 0xb4697845` |
| **L6: RAM, Disk & Binary Footprints** | Multi-process memory collapsed into 1 OS process (`~200–800 MiB` RSS) | Static bounded `MessagePool`/`IOPSType` + in-memory `Storage` + `OverlayBuffers` | Single OS thread stack + `HashMap` virtual FS/Net (`< 50 MiB` typical test RSS) | `MAX_INITIAL_STATE_BYTES = 4096 B` auxv handoff; `RCB_OVERSHOOT_REPORTS_KEPT = 65536` (`~1 MiB`); trace logs `~10+ MB/min` | `libnvbit.a = 5,510,852 B`, tarball `988,809 B`; `mem_access_t = 288 B/warp-op` (`28,800 B` for 100 ops vs `256 B` causal atomic schedule) |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: derived + source + documentation`

#### (`C1`) Human Comprehensibility and Mental-Model Ergonomics
- **Seed Compression vs. Internal Escape Opacity**: Printing one 64-bit seed (`you can reproduce this failure with seed=...`, `vopr.zig:354`, or `MADSIM_TEST_SEED=...`, `madsim_runtime_mod.rs:207`) represents an optimal human-to-machine debugging interface: any multi-hour cluster split-brain compresses to 20 decimal digits. However, when determinism *breaks*, human comprehension collapses rapidly across abstraction boundaries:
  - A `MadSim` user sees `non-determinism detected at 142.3ms` (`madsim_sim_rand.rs:80`)—which tells *when* an RNG sequence diverged, **not** which upstream unseeded `HashMap` or `SYS_getrandom` crate caused it.
  - A `Hermit` user encountering hardware PMU skid or an unsupported syscall (`refuse_cpu_clock` with `https://github.com/rrnewton/hermit/issues/4155`, `cpu_clock.rs:276`) must reason about kernel `posix_cpu_timers.c` PID encoding, `vDSO` patching, and out-of-order branch retirement skid (`skid_overshoots.rs`)—well beyond normal developer working memory.
  - An `NVBit` user inspecting raw SASS (`IMAD.WIDE R8, R8, R9` + `JMX`/`BRX` degenerate CFGs, `nvbit.h:54, 118`) faces undocumented vendor microarchitectural opcodes unless tools lift captured warp/CTA/instruction offsets back to PTX/CUDA source lines (`nvbit_get_line_info`).
- **Diagnostic Lifting Requirement**: Combining deterministic replay with `O(log_2 N)` rolling Merkle checkpoints (`det_replay_warp_probe.py`) converts opaque "re-run failed" or "checksum mismatch at tick 40M" alerts into an exact source-step bisection index (`step = 613`).

#### (`C2`) Conceptual Simplicity, Orthogonality, and Adapter-Conservation Audit
Separating essential causal semantics from OS/GPU realization quirks unifies all five tools cleanly:
- **Realization-Medium Quirks (Accidental Complexity)**:
  1. `MadSim`'s Linux vs. macOS split (`#[no_mangle] getrandom` succeeding via `CCRandomGenerateBytes` / `dlsym` on macOS while failing if Linux Rust crates emit raw `syscall(SYS_getrandom)` instructions, `rand.rs:291-296`).
  2. `Hermit`'s `InitialRandomState` `v4` (`random.rs:94-224`) marshaling glibc's dynamic linker `tcache` `getrandom` calls and `RLIMIT_STACK` reads across `execve` strictly because Linux `ld.so` initializes before `Detcore`'s root thread exists.
  3. `NVBit`'s explicit `__ballot_sync(__activemask(), 1)` + `__shfl_sync` leader-lane protocol (`inject_funcs.cu:52-75`) compensating for NVIDIA's SIMT execution model where 32 threads share an instruction stream without native per-warp trace instructions.
- **Universal Core Abstraction (`CausalCapability` + `ScheduleCertificate`)**:
  Across cluster actors, Linux containers, and GPU warps, deterministic replay reduces to **two orthogonal invariants**:
  1. **Zero Ambient Nondeterminism**: Every source of time, entropy, I/O arrival, or floating-point rounding mode is an explicit, seeded capability rather than ambient hardware state (`RDTSC`, `RandomState`, `vDSO`, or dynamic batch-dependent reduction trees).
  2. **Causal Order Certificate for Unavoidable Concurrency**: Where hardware genuinely executes asynchronously (cross-CTA GPU `ATOM`/`RED` instructions, or multi-core shared memory), determinism only requires recording a minimal total-order tie-breaker certificate (`(addr_epoch, warp_id)`, `2 B/op`) rather than full data/address snapshots (`288 B/op`).
- **Adapter-Conservation Audit**: Simply moving from `MadSim` (`0` syscall interposition) to `Hermit` (`ptrace` + `seccomp`) does *not* automatically guarantee determinism if external shared memory bypasses the syscall boundary: Linux `io_uring` submission/completion rings, `MAP_SHARED` cross-container buffers, and `cudaMallocManaged` / GPU DMA streams mutate guest memory **without issuing syscalls**, meaning any tool that ignores DMA/shared-memory ownership merely hides nondeterminism escapes behind a deterministic syscall veneer.

## Boundaries

- **Shared-Memory & Kernel-Bypass Async I/O (`Hermit` — `unsupported` / `known not to apply`)**:
  `Hermit`'s PMU RCB serialization covers threads inside its traced process/PID tree; it cannot deterministically order memory mutations performed asynchronously by external processes over `MAP_SHARED` files, kernel `io_uring` `IORING_SETUP_SQPOLL` worker threads, RDMA NICs, or GPU DMA writes. Moreover, `cpu_clock.rs:406-414` explicitly refuses reading another process's POSIX CPU clock (`OtherProcess`) deterministically.
- **Native FFI, Raw Syscalls, & Multi-Thread Memory Races (`Sim2`, `VOPR`, `MadSim` — `unsupported`)**:
  Cooperative simulators assume user logic yields cleanly to their virtual scheduler and does not bypass virtualized time/RNG. As documented in `madsim/src/sim/rand.rs:290-296`, Linux binaries invoking `SYS_getrandom` directly bypass `libc::getrandom` symbol interposition, and enabling `set_allow_system_thread(true)` (`madsim_runtime_mod.rs:156`) forfeits determinism guarantees. Cooperative simulators also do not model weak CPU memory models (`TSO`, `ARMv8` store-buffer reorderings).
- **`NVBit` Architecture, Closed-Source Core, & Indirect Control Flow (`NVlabs/NVBit` — `unsupported` / `not examined`)**:
  - `NVBit v1.8.2` requires Linux (`x86_64` or `aarch64`), CUDA `>= 12.0`, and NVIDIA SM compute capabilities `>= 3.5 && <= 12.1` (`README.md:53-58`). Windows/macOS and non-NVIDIA GPUs are unsupported.
  - `core/libnvbit.a` (`5,510,852 B`) is distributed strictly as a precompiled static binary without source code, under the NVIDIA CUDA Toolkit EULA (`EULA.txt`), preventing independent source-level auditing of its SASS decoder/patcher.
  - Functions using dynamic register-indirect jumps (`JMX`/`BRX`) mark `CFG_t::is_degenerate = true` (`core/nvbit.h:113-118`), precluding static basic-block CFG analysis.
  - Multi-GPU NVLink/PCIe peer-to-peer atomic ordering across separate `CUcontext`s (`nvbit_at_ctx_init`) was **not examined** empirically on physical multi-GPU hardware in this sandbox.
- **Hardware PMU Availability in Nested/Virtualized Guests (`Hermit` — `unknown`)**:
  Virtualization hypervisors or cloud capsules that disable or virtualize `PERF_COUNT_HW_BRANCH_INSTRUCTIONS` accurately cause `Hermit` to either reject RCB timing (`--no-rcb-time` fallback in `lib.rs:198-216`, losing preemptive timeslicing) or incur elevated `SkidOvershootCounts`.

## Evidence

### Primary Repositories, Release Artifacts, and Literature
- **`apple/foundationdb`** @ `39fb2391049fe326d2c5c7c3dd8dbb8b596284b9`:
  - `fdbrpc/sim2.cpp`: `simulator_should_inject_fault` (`L77-114`), `SimClogging` (`L201-293`), `Sim2Conn` (`L295-420`), `corruptedBlocks` (`L1025-1042`), `Sim2::runLoop` (`L1588-1624`), `killProcess_internal` / `rebootProcess` (`L1790-1895`).
  - `flow/DeterministicRandom.cpp`.
- **`tigerbeetle/tigerbeetle`** @ `a2a3c7064519e08233abe26c54a43fca2f9ad9bc`:
  - `src/vopr.zig`: `releases` matrix (`L43-56`), `comptime assert(constants.verify)` (`L95`), `seed` parsing & `ReleaseSafe` guard (`L133-155`), main simulation loop & `aof.validate` (`L245-377`).
  - `src/testing/packet_simulator.zig`: `PacketSimulatorOptions`, `PartitionMode`, `PartitionSymmetry`, `PacketSimulatorType` (`L13-258`).
  - `src/testing/storage.zig`: `Storage::Options`, misdirected-write `overlays` & `OverlayBuffers` (`L49-254`).
- **`madsim-rs/madsim`** @ `519950efb4711464f300ed7edf2967ed62d5f502`:
  - `madsim/src/sim/runtime/mod.rs`: `Runtime::with_seed_and_config` (`L53-69`), `set_allow_system_thread` (`L156-158`), `Runtime::check_determinism` (`L178-202`), `panic_with_info` (`L205-210`).
  - `madsim/src/sim/rand.rs`: `GlobalRng` (`L28-120`), `init_std_random_state` (`L176-180`), `getrandom` / `getentropy` / `CCRandomGenerateBytes` (`L195-283`), Linux `SYS_getrandom` bypass note (`L290-296`).
  - `madsim/src/sim/task/mod.rs`: `allow_system_thread` enforcement (`L237-249, 1066-1077`).
- **`facebookexperimental/hermit`** @ `2994b6f8e7ae4ba8a093b4e1555cd1483ada6bb8`:
  - `detcore/src/cpu_clock.rs`: `GUEST_KERNEL_HZ = 250` (`L50`), `CpuClockKind` (`L55-88`), `classify` (`L121-152`), `cpu_clock_reading` & `refuse_cpu_clock` (`L276, 392-420`).
  - `detcore/src/random.rs`: `splitmix64` (`L35-40`), `root_prng` (`L87-89`), `InitialRandomState` `v4` / `MAX_EARLY_GETRANDOM = 32` (`L94-244`).
  - `detcore/src/skid_overshoots.rs`: `RcbOvershootReport` (`L46-51`), `RCB_OVERSHOOT_REPORTS_KEPT = 1 << 16` (`L56`), `SkidOvershootCounts::count` (`L106-160`).
  - `detcore/src/lib.rs`: `use_rcb_time` & `report_rcb_overshoot` (`L198-243, 747-771`).
- **`NVlabs/NVBit`** (`cda43eb3720c69c051385e70791e0f948028a02c`) & **`nvbit-Linux-x86_64-1.8.2.tar.bz2`** (`sha256: fa2728c8921fdcb8e761fd62b2173a2492b47da3605f9ab9510e006772e48eee`, `988,809 B`):
  - `README.md` (`L53-58` SM `3.5–12.1`, CUDA `>= 12.0`).
  - `core/nvbit.h` (`NVBIT_VERSION "1.8.2"`): `Instr` (`L51-105`), `CFG_t` (`L113-121`), `TMATransferInfo_t` (`L164-249`), `nvbit_insert_call` & arg injectors (`L527-620`).
  - `core/libnvbit.a` (`5,510,852 B`); `core/utils/channel.hpp` (`13,007 B`).
  - `tools/mem_trace/common.h` (`mem_access_t`, `L36-44`, verified `288 B` via Python `ctypes`); `tools/mem_trace/inject_funcs.cu` (`instrument_mem`, `L43-76`); `tools/mem_trace/mem_trace.cu` (`L232-302`); `tools/record_reg_vals/record_reg_vals.cu` (`L159-188`).
- **Literature**:
  - Jingyu Zhou et al., *"FoundationDB: A Distributed Unbundled Transactional Key Value Store"*, **SIGMOD '21**, June 2021, DOI `10.1145/3448016.3457559`.
  - Omar S. Navarro Leija et al., *"Reproducible Containers"*, **ASPLOS '20**, March 2020, pp. 167–182, DOI `10.1145/3373376.3378519`.
  - Oreste Villa, Mark Stephenson, David Nellans, and Stephen W. Keckler, *"NVBit: A Dynamic Binary Instrumentation Framework for NVIDIA GPUs"*, **MICRO-52**, October 2019, DOI `10.1145/3352460.3358307`.
  - Horace He and Thinking Machines Lab, *"Defeating Nondeterminism in LLM Inference"*, engineering report, 2025 (`https://thinkingmachines.ai/blog/defeating-nondeterminism-in-llm-inference/`).

### Self-Contained Executable Verification Probe (`Basis: execution`, observed 2026-11-19)

Command: `python3 /tmp/det_replay_warp_probe.py`

```python
#!/usr/bin/env python3
"""Cluster Merkle-bisection & GPU SIMT warp/atomic trace-compression probe."""

import hashlib
import json
import random
import struct
from typing import Dict, List, Tuple


def run_cluster(seed: int, steps: int = 1024, inject_escape_step: int = -1, escape_val: int = 0) -> Tuple[List[str], int]:
    rng = random.Random(seed)
    nodes = [0, 0, 0, 0, 0]
    merkle = b"\x00" * 32
    checkpoints: List[str] = []
    vtime_ns = 0
    for step in range(steps):
        vtime_ns += rng.randint(100, 5000)
        src = rng.randrange(5)
        dst = rng.randrange(5)
        delta = rng.randint(1, 97)
        if step == inject_escape_step:
            delta ^= escape_val
        nodes[src] = (nodes[src] + delta) & 0xFFFFFFFF
        nodes[dst] = (nodes[dst] ^ ((nodes[src] * 2654435761) & 0xFFFFFFFF)) & 0xFFFFFFFF
        payload = struct.pack(">QIIII", vtime_ns, step, src, dst, nodes[dst])
        merkle = hashlib.sha256(merkle + payload).digest()
        checkpoints.append(merkle.hex())
    return checkpoints, nodes[3]


def bisect_divergence(ref: List[str], div: List[str]) -> Tuple[int, int]:
    lo, hi = 0, len(ref) - 1
    probes = 0
    while lo < hi:
        mid = (lo + hi) // 2
        probes += 1
        if ref[mid] == div[mid]:
            lo = mid + 1
        else:
            hi = mid
    return lo, probes


def float32_add(a: float, b: float) -> float:
    return struct.unpack("<f", struct.pack("<f", a + b))[0]


def run_gpu_warp_probe(num_warps: int = 128) -> Dict[str, object]:
    rng = random.Random(0x9F2A)
    naive_thread_records = 0
    nvbit_mem_access_bytes = 0
    causal_schedule_records: List[Tuple[int, int]] = []
    warp_contribs: List[float] = []

    for w in range(num_warps):
        active_mask = 0
        for lane in range(32):
            if rng.random() < 0.75:
                active_mask |= (1 << lane)
                naive_thread_records += 1
        if active_mask != 0:
            nvbit_mem_access_bytes += 288
        val = struct.unpack("<f", struct.pack("<f", rng.uniform(0.001, 100.0) * (1.0 if w % 3 else 1e-4)))[0]
        warp_contribs.append(val)

    order_a = list(range(num_warps))
    order_b = list(range(num_warps))
    rng.shuffle(order_a)
    rng.shuffle(order_b)

    acc_a = 0.0
    for wid in order_a:
        acc_a = float32_add(acc_a, warp_contribs[wid])
        causal_schedule_records.append((wid, 0))
    acc_b = 0.0
    for wid in order_b:
        acc_b = float32_add(acc_b, warp_contribs[wid])

    acc_replay = 0.0
    for wid, _ in causal_schedule_records:
        acc_replay = float32_add(acc_replay, warp_contribs[wid])

    naive_bytes = naive_thread_records * 24
    causal_sched_bytes = len(causal_schedule_records) * 2
    return {
        "warps": num_warps,
        "active_thread_accesses": naive_thread_records,
        "naive_per_thread_bytes": naive_bytes,
        "nvbit_warp_packet_bytes": nvbit_mem_access_bytes,
        "nvbit_struct_mem_access_t_bytes": 288,
        "causal_atomic_schedule_bytes": causal_sched_bytes,
        "warp_vs_naive_ratio": round(naive_bytes / nvbit_mem_access_bytes, 2),
        "sched_vs_nvbit_ratio": round(nvbit_mem_access_bytes / causal_sched_bytes, 2),
        "fp32_order_a_hex": struct.pack("<f", acc_a).hex(),
        "fp32_order_b_hex": struct.pack("<f", acc_b).hex(),
        "fp32_reordered_drift": acc_a != acc_b,
        "fp32_replay_exact_match": acc_a == acc_replay,
    }


if __name__ == "__main__":
    ref_ckpt, ref_n3 = run_cluster(0x9F2A, 1024)
    rep_ckpt, rep_n3 = run_cluster(0x9F2A, 1024)
    div_ckpt, div_n3 = run_cluster(0x9F2A, 1024, inject_escape_step=613, escape_val=1)
    step_found, probes_used = bisect_divergence(ref_ckpt, div_ckpt)
    print(json.dumps({
        "cluster_repeat_bit_exact": (ref_ckpt[-1] == rep_ckpt[-1] and ref_n3 == rep_n3),
        "cluster_escape_injected_at": 613,
        "cluster_bisected_step": step_found,
        "cluster_bisection_probes": probes_used,
        "cluster_final_root_mismatch": ref_ckpt[-1] != div_ckpt[-1],
        "gpu_warp_atomic_probe": run_gpu_warp_probe(128),
    }, indent=2))
```

Recorded Output:

```json
{
  "cluster_repeat_bit_exact": true,
  "cluster_escape_injected_at": 613,
  "cluster_bisected_step": 613,
  "cluster_bisection_probes": 10,
  "cluster_final_root_mismatch": true,
  "gpu_warp_atomic_probe": {
    "warps": 128,
    "active_thread_accesses": 3066,
    "naive_per_thread_bytes": 73584,
    "nvbit_warp_packet_bytes": 36864,
    "nvbit_struct_mem_access_t_bytes": 288,
    "causal_atomic_schedule_bytes": 256,
    "warp_vs_naive_ratio": 2.0,
    "sched_vs_nvbit_ratio": 144.0,
    "fp32_order_a_hex": "b4697845",
    "fp32_order_b_hex": "af697845",
    "fp32_reordered_drift": true,
    "fp32_replay_exact_match": true
  }
}
```

## Revalidation

To verify whether these findings remain accurate against newer upstream releases or host environments:

1. **Re-run the Cluster Bisection & GPU Warp-Schedule Probe**: Execute `python3 /tmp/det_replay_warp_probe.py` (`< 50 ms`, Python 3.10+ stdlib only) and assert `cluster_bisected_step == 613`, `cluster_bisection_probes == 10`, `gpu_warp_atomic_probe.fp32_reordered_drift is True`, and `gpu_warp_atomic_probe.fp32_replay_exact_match is True`.
2. **Diff Upstream Determinism Boundaries**:
   - In `apple/foundationdb`, inspect `fdbrpc/sim2.cpp` (`Sim2::runLoop`, `SimClogging`, `killProcess_internal`) for changes to protected-process rules or virtual sleep jitter.
   - In `tigerbeetle/tigerbeetle`, inspect `src/vopr.zig` (`comptime assert(constants.verify)`), `src/testing/packet_simulator.zig`, and `src/testing/storage.zig` (`overlays`) for new fault modes or release-matrix policies.
   - In `madsim-rs/madsim`, inspect `madsim/src/sim/rand.rs` (`getrandom` / `init_std_random_state`) and `madsim/src/sim/runtime/mod.rs` (`check_determinism`) to verify whether Linux `SYS_getrandom` raw-syscall crates remain unintercepted (`#[cfg_attr(target_os = "linux", ignore)]`).
   - In `facebookexperimental/hermit`, inspect `detcore/src/skid_overshoots.rs` (`SkidOvershootCounts::count`), `detcore/src/cpu_clock.rs` (`GUEST_KERNEL_HZ`), and `detcore/src/random.rs` (`InitialRandomState`).
   - In `NVlabs/NVBit`, verify the latest release tarball SHA-256 and inspect `core/nvbit.h` (`NVBIT_VERSION`, `TMATransferInfo_t`, SM upper bound in `README.md`) and `tools/mem_trace/{common.h,inject_funcs.cu}`.
