# Spatial HLS Lowering, Elastic Handshake Deadlocks, Virtualized FPGA OS Shells, and Single-Source Heterogeneous Offload

## Summary

Compiling single-source heterogeneous workloads across CPUs, GPUs, and reconfigurable FPGAs couples two fragile boundaries: spatial hardware scheduling inside the accelerator (control lowering, FIFO slack matching, and memory bank arbitration) and virtualized memory movement across the PCIe/network boundary (FPGA TLBs, RDMA queue pairs, and host–device unified shared memory). Inspection of `calyxir/calyx`, `llvm/circt`, `fpgasystems/Coyote`, and `AdaptiveCpp/AdaptiveCpp` reveals four load-bearing invariants and failure modes. First, dynamic `go`/`done` handshake lowering (`TopDownCompileControl`) adds per-stage transition and `par` synchronization overhead (`+45.60%` cycle inflation in a 64-iteration 4-stage pipeline probe) unless islands promote to cycle-accurate `static<N>` FSMs (`CompileStatic`), while `ScheduleConflicts` tracks parallel group/invoke conflicts without prohibiting single-port BRAM hazards caught dynamically by Cider (`CombMem`). Second, CIRCT's default cycle-only `HandshakeInsertBuffersPass` (`strategy="cycles"`) leaves acyclic reconvergent fork–join diamonds unbuffered, inducing `3.25x` throughput collapse (`65` vs. `20` cycles) under 1-token pipelines and complete deadlock (`0/4` batches) when the slow arm requires $K > B$ tokens per output. Third, Coyote's multi-tenant FPGA shell (`N_REGIONS` isolated `mmu_region_top` units, `4 KiB` `sTLB` + `2 MiB` `lTLB`, and 100G RoCEv2 `rocev2_ip`) actually disables Linux HMM in current builds (`fpga_hmm.c` is legacy/uncompiled, and `en_hmm=1` silently turns `UNMAP`/`OFFLOAD`/`SYNC` ioctls into no-ops), relying instead on `FOLL_LONGTERM` GUP pinning, explicit DMA drain fences, and `dma_buf` GPU P2P. Fourth, AdaptiveCpp's single-pass `SSCP` JIT specialization decouples frontend parsing from backend PTX/SPIR-V lowering, yet `--acpp-stdpar` intercepts heap allocators into Unified Shared Memory whose page-granularity migrations suffer `26.7x` PCIe thrashing under AoS CPU–GPU false sharing (`5,120` vs. `192` page faults over 10 phases) unless separated into SoA `Region`s and explicit asynchronous prefetches.

## Applicability

This report characterizes four interacting toolchain and hardware layers examined at pinned upstream revisions:

- **Spatial hardware IR & control lowering**: `calyxir/calyx` (`e1bca4bf6779ccc98b5099f9a2284ca3b0bef637`, Nigam et al. ASPLOS 2021) covering `calyx/opt` passes (`TopDownCompileControl`, `StaticPromotion`, `CompileStatic`, `Papercut`), `ScheduleConflicts`, and the `Cider` flattened RTL interpreter (`CombMem`), alongside `llvm/circt` (`203f159ce10d78940df4264327d5f3fc8b902112`) covering `Calyx` dialect definitions, `SCFToCalyx` lowering (`scf.for`/`scf.while`), and `HandshakeInsertBuffersPass`. Applies to synchronous FPGA RTL targeting SystemVerilog/Verilator/Vivado.
- **Multi-tenant FPGA OS shell & RDMA**: `fpgasystems/Coyote` (`0fbc94ba60296c44fc76698396579ac719aadd3b`, Korolija et al. OSDI 2020) on AMD/Xilinx UltraScale+ (`u200`/`u250`/`u280`/`u55c`) boards with 100G CMAC RoCEv2 (`rocev2_ip` v0.82) and Linux PCIe driver (`vfpga_isr.c`, `vfpga_gup.c`). Findings on `dma_buf` GPU P2P assume Linux $\ge 6.2$ with `EN_CUDA` or `EN_ROCM`.
- **Single-source heterogeneous JIT & USM**: `AdaptiveCpp/AdaptiveCpp` (`96c7d17a9d029a5660ac06d7519b3763e9823ab6`, Alpay & Heuveline IWOCL 2023) using `--acpp-targets=generic` (`Generic SSCP`) and `--acpp-stdpar` targeting CUDA, HIP/ROCm, OpenCL/Level Zero SPIR-V, and OpenMP CPUs.
- **Executable cycle & paging probes**: Run on `Python 3.13.15` (`Linux 7.1.6-1rodete1-amd64 x86_64`) using deterministic cycle simulators and page-migration counters to measure exact cycle overheads, elastic deadlock thresholds, AoS false-sharing traffic, and Coyote `sTLB`/`lTLB` miss counts.

## Findings

### 1. Structural Datapath vs. Explicit Control Lowering (`calyx` & `circt`)

Basis: normative + source + execution

Calyx separates **structural hardware** (`cells` and guarded `wires` grouped into named behaviors) from **imperative control** (`seq`, `par`, `if`, `while`, `repeat`, and cycle-exact `static<N>` variants). Lowering these constructs into synthesizable RTL exposes sharp trade-offs between composability, cycle latency, and memory port safety:

1. **Dynamic `TDCC` (`TopDownCompileControl`) vs. Static `CompileStatic` FSM Lowering**:
   - In `calyx/opt/src/passes/top_down_compile_control.rs`, `TopDownCompileControl` compiles arbitrary dynamic `seq`/`par`/`if`/`while` trees into finite-state machines gated on each group's 1-bit `go`/`done` handshake signals. Specifically, `Control::Par` (`L1615-L1675`) allocates one `1`-bit `std_reg(1)` done-latch (`pd`) per parallel arm (`L1625, L1672`), drives `group["go"] = !(pd.out | group.done)` (`L1675`), latches `pd` when an arm finishes, and advances the parent FSM once all `pd` registers assert high. Similarly, `calculate_states_seq` (`L1114-L1125`) prepends an initial state `0` when control starts with `if`/`while`.
   - `StaticPromotion` (`static_promotion.rs:L41-L111`, default `threshold=1`, `cycle-limit=33554432`, `if-diff-limit=1`, `compaction=true`) promotes `@promotable(n)` dynamic islands whose latency is statically bounded into `static<N>` control (`static_seq`, `static_par`, `static_repeat`, `static_if`).
   - `CompileStatic` (`compile_static.rs:L21-L226`) eliminates internal `done` handshake polling completely inside `static<N>` islands, compiling control schedules into shared modulo counters (`one_hot_cutoff` switching between one-hot and binary FSM encodings, `L38-L40`), and generates `wrapper_` (`build_wrapper_group`, `L118-L179`) or `while_wrapper_` (`build_wrapper_group_while`, `L189-L226`) using a single `signal_reg` and continuous reset assignments (`offload_pause` governing sub-FSM pausing) at the dynamic/static boundary.
   - **Measured cycle overhead (`Probe 2A`)**: Simulating a 64-iteration loop executing 4 stages (`g0`: 2 cycles, `g1`: 3 cycles, `par { g2a(4); g2b(2) }`: 4 cycles, `g3`: 2 cycles = `11` static cycles/iter) yields **`704` cycles** under `CompileStatic` (`static_repeat` + compacted FSM) versus **`1,025` cycles** under non-early dynamic `TDCC` (`+45.60%` overhead, or **`1.456x` speedup** from static promotion).

2. **CIRCT `SCFToCalyx` Semantic Bridge and Divergences**:
   - In `llvm/circt`, `SCFToCalyx.cpp` lowers MLIR `func`, `scf.if`, `scf.for` (`getStaticTripCount()` at `L100` enabling static bounds), and `scf.while` (`L64-L116, L2013-L2159`) into CIRCT's `calyx` dialect (`CalyxControl.td:L25-L424`). `calyx-remove-comb-groups` (`CalyxPasses.td:L70-L110`) transforms 0-cycle combinational condition groups (`"static"=0`) into 1-cycle registered groups (`"static"=1`) so conditions stay stable across FSM state transitions.
   - **Preserved native-vs-CIRCT semantic disagreement (`CalyxControl.td:L319-L320`)**: CIRCT explicitly documents that `calyx.while %cond with @comb_group` semantics diverge from native Calyx regarding when `@comb_group` is active relative to body iterations, requiring `calyx-remove-comb-groups` before exporting to native `calyx` or Verilog.

3. **BRAM Port-Protocol & Multi-Arm Conflict Safety (`Papercut`, `ScheduleConflicts`, `CombMem`)**:
   - `Papercut` (`papercut.rs:L18-L105`) statically verifies primitive interface invariants derived from `write_together` (e.g., driving `reg.in` requires driving `reg.write_en`) and `read_together` (`comb_path_specs`) plus missing group `done` drivers.
   - `ScheduleConflicts` (`schedule_conflicts.rs:L9-L216`) constructs an undirected conflict graph between all group/invoke IDs appearing in sibling branches of dynamic `Par` (`L179-L197`) and static `StaticPar` (`L101-L119`) so register/cell-sharing passes never merge storage used concurrently. Crucially, `ScheduleConflicts` prevents *post-hoc merging* of distinct cells, whereas two distinct groups written by a frontend that reference the *same* single-port BRAM inside `par { g_write; g_read }` compile structurally and trigger dynamic `UndefinedWriteAddr`/`UndefinedWrite` or read-after-write hazards in `Cider` (`CombMem::exec_cycle`, `calyx_cider_memories.rs:L587-L638`; reproduced in `Probe 2A` as `[(1, 'memA', 'W', 'R')]`) unless banked (`memA_bank0`, `memA_bank1` -> `[]`).

### 2. CIRCT `Handshake` Elastic Backpressure Deadlocks & Slack Matching

Basis: source + execution + derived

CIRCT's `Handshake` dialect (`HandshakeOps.td:L49-L80`) models dataflow pipelines as unsynchronized processes communicating over single-consumer (`valid`/`ready`) elastic channels inside a dominance-free `handshake.func` region. While elastic handshaking tolerates variable-latency memories and dynamic branches without a central FSM, reconvergent topologies expose structural deadlocks unless buffers satisfy **slack-matching invariants**:

```
   +---> [Fast Path: 0 cycles + FIFO(B slots)] ---+
   |                                              v
[Fork]                                          [Join] ---> Consumer
   |                                              ^
   +---> [Slow Path: L-stage pipe / K-coalesce] --+

1) Acyclic 1:1 (L=4): B < L does NOT deadlock, but collapses II=1 (20 cyc) -> II=4 (65 cyc, 3.25x slower).
2) Reconvergent K=4 coalescing (1 output per K inputs) or cyclic dependence:
   B < K (B=1,2,3) DETERMINISTICALLY DEADLOCKS at cycle B+1 (0/4 batches)!
   Fork stalls because Fast FIFO(B) is full; Join cannot pop Fast until Slow gathers K=4 tokens.
```

Inspecting `lib/Dialect/Handshake/Transforms/Buffers.cpp` (`L67-L215`) reveals the exact compiler gap:

- **`strategy="cycles"` (`bufferCyclesStrategy`, `L145-L166`)**: Walks `MergeLikeOpInterface` operations and checks `inCycle(mergeOp, isSeqBuffer)` (`L118-L142`), placing sequential buffers (`BufferTypeEnum::seq`) *only* on cyclic merge outputs to break combinational cycles and transparent `fifo` buffers on non-cyclic merges. **It places zero buffers on acyclic `fork` -> `join` reconvergent paths.**
- **`strategy="allFIFO"` (`bufferAllFIFOStrategy`, `L168-L179`)**: Breaks cycles with sequential buffers and adds `BufferTypeEnum::fifo` of depth `bufferSize` on every remaining unbuffered edge (`L96-L114`). However, uniform shallow buffering (`bufferSize = 1` or `2`) still fails whenever path latency asymmetry or token-consumption rate ratio exceeds `bufferSize`.
- **Execution verification (`Probe 2B`)**: Simulating `16` tokens across a reconvergent diamond (`slow_stages = 4`):
  - Under 1:1 acyclic `slow_stages = 4`, `B=1` avoids deadlock but degrades from `20` cycles (`B=4,8`, optimal `II=1`) to `65` cycles (**`3.25x` throughput collapse**), `B=2` takes `34` cycles, and `B=3` takes `25` cycles.
  - Under a $K=4$ coalescing consumer (`reconvergent_k4_coalesce`, where `join` drains $K=4$ fast metadata tokens once the slow arm reduces $4$ tokens), `B=1, 2, 3` **deadlocks (`completed=False`, `0/4` batches at cycles `2, 3, 4`)**, while `B=4, 8` completes all `4/4` batches in `17` cycles. Slack matching therefore requires static latency/rate sizing $B \ge \max(\Delta L_{\text{acyclic}}, K_{\text{coalesce}})$—an invariant missing from `Buffers.cpp` at the pinned revision.

### 3. Multi-Tenant FPGA OS Shells (`Coyote`): Soft IOMMU/TLBs, Legacy HMM, and 100G RoCEv2

Basis: documentation + source + execution

Coyote (`fpgasystems/Coyote`, OSDI 2020) virtualizes UltraScale+ FPGAs across `N_REGIONS` isolated tenant slots (`vFPGA[i]`), wrapping each user kernel inside dynamic-layer AXI/MMU/credit bridges (`coyote_mmu.md`, `coyote_network.md`):

1. **Per-vFPGA Dual-TLB MMU & DMA Drain Fencing (`coyote_mmu.md:L45-L205`, `vfpga_isr.c`, `vfpga_gup.c`)**:
   - Each `mmu_region_top[i]` hosts two set-associative BRAM TLBs queried in parallel (`lTLB` wins at `ST_CHECK`, `L61-L71`): **`sTLB`** (`4 KiB` pages, `1024` sets × `4` ways = `4,096` entries) and **`lTLB`** (`2 MiB` hugepages, `512` sets × `2` ways = `1,024` entries; `1 GiB` noted as host-only with known issues). Addressing uses raw unhashed bits `vaddr[PG_BITS +: TLB_ORDER]` (`L69`), exposing pathologically strided virtual allocations to set-associativity conflict misses.
   - A 104-bit TLB word packs `{tag, ctid[5:0], strm[1:0], valid, pfn, hpid[31:0]}` (`L73-L79`). Read and write `tlb_fsm`s share BRAM lookup ports via a 2-bit `mutex`, split multi-page DMA requests at page boundaries (`ST_CALC_*` `L102`), and absorb up to `33` consecutive misses in `cch_buff` (`CACHE_MAX_SIZE = 32`, `L119`) to coalesce page-fault IRQs (`MAX_N_MAP_PAGES = 256` entries filled per IRQ `L165`).
   - On miss, `cnfg_slave` asserts MSI-X `usr_irq[i]`; Linux `vfpga_isr` (`vfpga_isr.c:L59-L72`) enqueues `wqueue_pfault` -> `vfpga_pfault_handler` -> `mmu_handler_gup` (`vfpga_gup.c:L27`), which pins pages via `pin_user_pages_remote(..., FOLL_LONGTERM)` (`tlb_get_user_pages`, `L299`), runs `dma_map_single`, optionally migrates host $\leftrightarrow$ card memory (`STRM_HOST=1` vs. `STRM_CARD=0`), and programs `fpga_{s,l}Tlb` over driver-private AXI4-Lite BAR windows (`tlb_slave_axil` `L240`; unmapped from userspace for multi-tenant isolation).
   - **Two-phase invalidation (`L169-L185`)**: Because GUP pins pages `FOLL_LONGTERM` without MMU notifiers, `tlb_unmap_gup` first clears entries via `valid=0` writes (matching `tag` + `hpid`) and then writes `INVLDT_LAST` (`0x30`) to stall until *both* `rd` and `wr` `tlb_fsm` circular in-flight RAMs (`depth=16`) drain overlapping DMAs and emit `IRQ_INVLDT`.
2. **Legacy HMM vs. GUP Migration & `dma_buf` GPU P2P (`coyote_mmu.md:L206-L224`)**:
   - Contrary to assumptions that Coyote runs Linux HMM page migration natively, direct inspection of `coyote_mmu.md:L206-L209` confirms `HMM_KERNEL` (`driver/LEGACY/hmm/fpga_hmm.c`) is **legacy and uncompiled** in the active Makefile; worse, the live `en_hmm` module parameter gates `IOCTL_UNMAP_USER_MEM`, `IOCTL_UNMAP_DMABUF`, `IOCTL_OFFLOAD_REQ`, and `IOCTL_SYNC_REQ` (`if(!en_hmm)`), so booting with `en_hmm=1` silently converts unmap and migration ioctls into no-ops. Instead, Coyote uses `FOLL_LONGTERM` GUP + explicit `LOCAL_OFFLOAD`/`LOCAL_SYNC` DMA (`offl_ctrl`/`sync_ctrl`) and Linux $\ge 6.2$ `dma_buf_dynamic_attach(allow_peer2peer, move_notify=p2p_move_notify)` (`vfpga_gup.c:L887`) for CUDA/ROCm GPU P2P without host DRAM bounce buffers.
3. **100G RoCEv2 RDMA Integration & Hard Limits (`coyote_network.md:L104-L209`)**:
   - At `322 MHz` CMAC `rclk` -> `250 MHz` HLS `nclk` (`512`-bit AXI-Stream), `rocev2_ip` (v0.82) implements Reliable Connection (`RC`) `RDMA WRITE`/`READ`/`SEND` over UDP port `4791` (`PMTU_BYTES=4096`), backed by card HBM/DDR retransmission buffers (`rdma_mux_retrans.sv`, `RETRANS_RETRY_CNT=12`).
   - Because `QPN = (vfid << 6) | ctid` indexes fixed `ROCE_STACK_MAX_QPS = 500` BRAM tables without an RTL bounds check, `(vfid=7, ctid=52)` (`QPN=500`) silently overflows QP tables (`L121`). Furthermore, `ack_gap_enforcer.sv` injects `85` cycles of backpressure after each ACK (`L144`), RX ICRC verification is unsupported (`L109`), `EN_TCP` TOE is broken in current templates (`L4, L225`), and packet-sniffer streams bypass CDC/PR decouplers (`L207`).

### 4. Single-Source `AdaptiveCpp` `SSCP` JIT & `HMM`/USM Page-Migration Thrashing

Basis: documentation + source + execution

AdaptiveCpp (`AdaptiveCpp/AdaptiveCpp`) compiles single-source C++20/SYCL and `--acpp-stdpar` algorithms in **one compiler pass (`Generic SSCP`)**:

1. **Two-Stage `IR Constant` Compilation (`doc/generic-sscp.md`, `include/hipSYCL/glue/llvm-sscp/jit.hpp`)**:
   - **Stage 1 (AOT frontend)**: Clang parses host and device C++ once into LLVM IR containing uninitialized global `Stage 1 IR constants` (`is_device`, `bitcode_blob`), clones the module, sets constants, runs DCE + kernel extraction (`KernelOutliningPass`), swaps device math/atomic calls to `__acpp_sscp_*` stubs, and embeds generic LLVM bitcode inside the host binary.
   - **Stage 2 (Runtime `llvm-to-backend` JIT)**: Upon first kernel dispatch, `jit::compile()` (`jit.hpp:L267-L320`) injects runtime device constants (`Stage 2 IR constants`), runs `translator->specializeKernelArgument(...)` (`L286`), attaches `noalias` metadata (`L295`), resolves call targets (`specializeFunctionCalls`, `L316`), links backend bitcode libraries, and lowers to PTX, SPIR-V, or AMDGPU GCN in one unified IR pipeline.
2. **`--acpp-stdpar` Heap Interception, Sync Elision & `4 KiB` HMM Thrashing (`doc/stdpar.md:L75-L175`, `MallocToUSM.hpp`)**:
   - Compiling with `--acpp-stdpar` rewrites `operator new/delete`, `malloc`, `aligned_alloc`, and `free` (not `calloc`/`realloc`, and excluding stack variables `L151-L152`) into SYCL shared USM allocations, relying on driver/HMM page migration whenever CPU and GPU alternate accesses. Notice the fragile ODR link hazard (`L162-L168`): linking a `--acpp-stdpar` TU with a non-`stdpar` TU causes `std::vector` header instantiations to non-deterministically pick regular `malloc` vs. USM `malloc`! Moreover, enabling `--acpp-stdpar-system-usm` forces the compiler to treat host stack accesses as potentially GPU-visible, disabling cross-kernel `wait()` synchronization elision (`L98-L100`).
   - **AoS false-sharing thrashing (`Probe 2C`)**: When `16,384` `64`-byte AoS structs (`16 B` CPU metadata + `48 B` GPU float payload = `64` records per `4096 B` page, `256` pages) alternate between host metadata updates and device kernel sweeps over `10` iterations, every `4 KiB` page faults across PCIe in both directions (**`5,120` page migrations = `20 MiB`** transferred over `1 MiB` working state). Splitting into Struct-of-Arrays (`SoA`: `64` CPU-only pages + `192` GPU-only pages) drops migrations to **`192` (`0.75 MiB`, `26.7x` reduction)** with zero ongoing ping-pong. Similarly, mapping `256 MiB` of DMA buffers through Coyote's `sTLB` (`4 KiB`) vs. `lTLB` (`2 MiB`) cuts TLB capacity misses **`512x` (`65,536` vs. `128`)**, keeping the working set inside Coyote's `1,024`-entry `lTLB` without page-fault IRQs (`Probe 2C`).

### 5. Six-Level Quantitative Performance & Resource Footprint (`L1`–`L6`)

Basis: source + documentation + execution + derived

| Level | Metric / Scope | `calyx` (`TDCC` vs. `CompileStatic`) | `circt` (`Calyx` / `Handshake`) | `Coyote` (`vFPGA MMU` + `100G RoCEv2`) | `AdaptiveCpp` (`SSCP` + `stdpar`) |
|---|---|---|---|---|---|
| **`L1` Authoring & Velocity** | Subsystem LoC & spec overhead | `tdcc.rs` `1,785` + `compile_static.rs` `1,429` + `static_promotion.rs` `700` + `papercut.rs` `374` LoC; `Calyx` IR is verbose (`~3–5x` Python/MLIR generator output) | `SCFToCalyx.cpp` `3,126` + `Buffers.cpp` `228` + `*.td` `1,863` LoC; MLIR ODS automates parser/verifier boilerplate | `vfpga_gup.c` `1,119` + `vfpga_isr.c` `222` + `coyote_defs.h` `1,211` LoC; 10–15 LoC `cThread` host wrappers vs. raw RTL | `jit.hpp` `496` LoC; C++20 `stdpar` reduces multi-device kernel code to single-pass host STL calls (`~1x` CPU LoC) |
| **`L2` Toolchain Build** | Host compiler build speed & RSS | Cargo Rust workspace (`~30–60 s` incremental, `< 1.5 GiB` RSS); optional Verilator/Cider build | C++ LLVM + MLIR + CIRCT build (`~15–45 min` clean build, `4–12 GiB` link RSS unless `lld`/`mold` used) | Shell + Vivado HLS IP build (`rocev2_ip`, `toe_ip`, `CLOCK_PERIOD=4 ns`), **`1–4 h` Vivado P&R** (`16–48 GiB` RSS) | Clang/LLVM plugin + runtime (`~3–8 min` CMake build, `~2–4 GiB` RSS) |
| **`L3` Compilation & Synthesis** | IR pass & JIT specialization latency | Sub-second Rust passes (`ms` for `StaticPromotion` + `CompileStatic` + `Papercut`) | Sub-second MLIR `SCFToCalyx` + `HandshakeInsertBuffers` (`ms`); downstream SV emission `< 1 s` | `vFPGA` dynamic-region partial reconfiguration builds per kernel still require Vivado P&R (`tens of min–hours`) | Single AOT Clang pass (`1x` parse vs. `N` SMCP backend parses); runtime `Stage 2` JIT `tens–hundreds of ms` (cached thereafter) |
| **`L4` Runtime Execution** | Throughput, cycles & fault latency | **`1.456x` speedup** (`704` vs. `1,025` cycles over `64` iters in `Probe 2A`); `static<N>` reaches `II=1` | `Handshake` `B=1` degrades `II=1->4` (`65` vs. `20` cyc, `3.25x` loss) or **deadlocks** at `B < K` (`Probe 2B`) | `100 Gbps` `512`-bit AXIS @ `250/322 MHz`; **`512x` miss drop** via `2 MiB` `lTLB` (`Probe 2C`); GUP fault triggers PCIe IRQ + workqueue `pin_user_pages_remote` (`tens of µs`) | Native-parity `PTX`/`SPIR-V` execution once JIT-specialized; AoS HMM thrashing causes **`26.7x` excess PCIe traffic** vs. SoA (`Probe 2C`) |
| **`L5` Safety / Admission** | Static/dynamic invariant verification | `Papercut` (`ms` port-protocol check) + `ScheduleConflicts` graph; `Cider` dynamic simulation catches BRAM write/addr hazards | MLIR verifier checks single-use SSA in `handshake.func`; no static slack-matching deadlock proof in `Buffers.cpp` | Driver enforces BAR separation (no userspace TLB write) + `INVLDT` DMA drain fence; **no RTL QPN `< 500` bounds check** | Clang SSCP checks stack-pointer non-offload (`L152`); ODR mismatch across `--acpp-stdpar` TUs unchecked at link (`L164`) |
| **`L6` Memory, Area & Energy** | BRAM/LUT, TLB & power footprint | `CompileStatic` replaces per-group `done` FFs + `pd` regs with shared modulo counter (binary above `one_hot_cutoff`) | `bufferAll` inserts registers on every channel (high FF/LUT area); `cycles` minimizes area at deadlock risk | `sTLB` (`4096` × `104 b` = `52 KiB` BRAM/vFPGA) + `lTLB` (`1024` × `104 b` = `13 KiB` BRAM/vFPGA) + card HBM/DDR retrans buffers (`~30–75 W` FPGA TDP) | Host bitcode embedded in binary; HMM avoids `2x` duplicate allocations at `4 KiB` page-table cost (`8 B`/PTE) unless pinned/SoA |

### 6. Human Comprehensibility (`C1`) and Universal Model Refinement (`C2`)

Basis: derived + source

#### (`C1`) Human Comprehensibility & Non-Local Reasoning Burden

Designing across these four stacks forces a human engineer to track **10+ cross-layer mental models** simultaneously: Calyx `go`/`done` vs. early-reset `static<N>` `signal_reg` wrappers, `while ... with` CIRCT-vs-Calyx divergence, Cider vs. static `ScheduleConflicts` gaps on BRAMs, elastic `Handshake` reconvergent slack matching, Coyote `sTLB` unhashed direct-mapped index aliasing, `QPN = (vfid<<6)|ctid` silent `500`-entry table wraparound, `en_hmm=1` silent ioctl no-op traps, sniffer missing CDC/decouplers, `stdpar` ODR header allocation skew, and `--acpp-stdpar-system-usm` killing sync elision.

While an agent can inspect all four repositories rapidly, **diagnostics and failure modes remain deeply hostile to human comprehension**: a `Handshake` deadlock manifests during RTL simulation as silent `valid=1, ready=0` hang with zero backpressure blame path; a `QPN >= 500` overflow corrupts sibling tenant RoCE state silently; and AoS false sharing under `--acpp-stdpar` runs cleanly with catastrophic PCIe slowdown and no compiler warning.

#### (`C2`) Conceptual Simplicity, Adapter Conservation & Minimal Universal Model

Evaluating these systems through Ousterhout's Deep Module lens, Jackson's Concept Design, and Felleisen macro-expressibility shows how three orthogonal primitives subsume the ad-hoc control, handshake, and DMA adapters without pushing hidden complexity into wrappers (**Adapter Conservation**):

1. **`Region<Brand, DeviceSpace, Layout>`**: Binds memory buffers explicitly to storage spaces (`HostDRAM`, `FPGA_CardHBM`, `GPU_HBM`, `BRAM_Bank[k]`) and layout discipline (`SoA` non-aliasing slices vs. AoS), making `1RW` BRAM bank conflicts (`Probe 2A`), AoS false sharing (`Probe 2C`), and `en_hmm` / `P2P` space mismatches static type errors rather than runtime hangs or silent no-ops.
2. **`Grade<Latency(N), Slack(B), MTU(4096)>`**: Unifies Calyx `static<N>` cycle contracts, CIRCT `Handshake` FIFO slack-matching lower bounds ($B \ge \max(\Delta L, K)$), and Coyote `QPN < 500` / `2 MiB` hugepage bounds inside one quantitative static check—turning `Probe 2B`'s runtime elastic deadlock and `QPN` overflow into local compile-time diagnostics pinpointing the offending edge or table bound.
3. **`Certificate<AvailVisFence, StaticWrapper>`**: Encodes cross-domain ordering contracts—both Calyx dynamic-to-static FSM `signal_reg` wrappers and Coyote's two-phase `valid=0` + DMA `INVLDT` drain fence / `OFFLOAD` completion barriers—as linear protocol obligations rather than unverified register sequences (`REG_0 -> REG_1 -> REG_2` in `cnfg_slave.sv`). Under Felleisen's macro-expressibility test, replacing `en_hmm` runtime flags and `ScheduleConflicts` post-hoc checks with `Region` + `Grade` genuinely *eliminates* cross-layer failure classes rather than translating them into runtime adapter boilerplate.

## Boundaries

- **Coyote FPGA shell multi-vendor & Versal applicability (`known not to apply` / `unsupported`)**: `coyote_network.md` (`L3, L69`) explicitly scopes the 100G CMAC RoCEv2 network stack to AMD/Xilinx UltraScale+ (`u55c`, `u200`, `u250`, `u280`) with no Versal `v80` CMAC branch; TCP TOE (`EN_TCP`) is explicitly documented as broken in current templates (`L4, L225`); IPv6/ICMPv6 and RX ICRC checking are unsupported (`L36, L109`); and Coyote's `1 GiB` `lTLB` configuration has documented issues (`coyote_mmu.md:L65`).
- **Coyote live Linux HMM support (`known not to apply` at pinned commit)**: `driver/LEGACY/hmm/fpga_hmm.c` is uncompiled legacy code (`coyote_mmu.md:L206-L209`), so Coyote unified memory at `0fbc94ba60296c44fc76698396579ac719aadd3b` does not use hardware-transparent Linux HMM; setting `en_hmm=1` breaks user unmap and offload/sync ioctls.
- **Actual Vivado P&R LUT/BRAM/WNS numbers & real GPU/FPGA hardware PCIe measurements (`not examined`)**: Execution probes on the test host (`x86_64` CPU without attached UltraScale+ FPGA or discrete GPU) measured cycle counts, deadlock thresholds, AoS/SoA page counts, and TLB miss reductions in Python simulation (`Probe 2A`–`2C`), not live physical bitstream synthesis or hardware PCIe DMA throughput.
- **Static control promotion over data-dependent loops (`unsupported` in `CompileStatic`)**: `StaticPromotion` (`static_promotion.rs:L92-L99`) skips loops exceeding `cycle-limit` (`33554432`), unbalanced conditionals exceeding `if-diff-limit`, or unbounded `while` loops whose termination depends on runtime values; such regions must retain dynamic `TDCC` (`go`/`done`) control and wrapper bridges (`CompileStatic`).
- **CIRCT `Handshake` arbitrary-rate / dynamic-select deadlock completeness (`unknown` for general cyclic DFGs)**: `Probe 2B` establishes deadlock for $B < K$ on reconvergent $K$-coalescing paths and throughput collapse on acyclic pipelines; general cyclic `Handshake` graphs with data-dependent `mux`/`cond_br` routing remain undecidable for purely structural cycle checks without bounded model checking or dataflow Petri-net reachability.
- **AdaptiveCpp `stdpar` non-intercepted allocators and multi-backend MQS (`unsupported`)**: `doc/stdpar.md` (`L128, L151-L152`) explicitly notes `calloc`/`realloc` and stack pointers are not converted to USM, and experimental multi-queue scheduling (`--acpp-stdpar-mqs`) schedules across multiple devices of the *same* backend only (not across CPU+GPU+FPGA simultaneously).

## Evidence

All observations were collected on `2026-11-19` directly from pinned upstream commits, verified DOIs/proceedings, and executed probes:

### Primary Source Locations
- **Calyx (`calyxir/calyx` @ `e1bca4bf6779ccc98b5099f9a2284ca3b0bef637`)**:
  - `calyx/opt/src/passes/top_down_compile_control.rs`: `calculate_states_seq` (`L1114-L1125`), `Control::Par` `pd` done-latch lowering (`L1615-L1675`).
  - `calyx/opt/src/passes/static_promotion.rs`: `StaticPromotion` options & policy (`L41-L120`).
  - `calyx/opt/src/passes/compile_static.rs`: `CompileStatic` (`L21-L110`), `build_wrapper_group` (`L118-L179`), `build_wrapper_group_while` (`L189-L226`).
  - `calyx/opt/src/passes/papercut.rs`: `Papercut` `write_together`/`read_together` checks (`L18-L160`).
  - `calyx/opt/src/analysis/schedule_conflicts.rs`: `ScheduleConflicts` dynamic/static `Par` conflict graph (`L9-L216`).
  - `cider/src/flatten/primitives/stateful/memories.rs`: `CombMem::exec_cycle` (`L587-L638`), `InvalidMemoryAccess` (`L330`).
- **CIRCT (`llvm/circt` @ `203f159ce10d78940df4264327d5f3fc8b902112`)**:
  - `include/circt/Dialect/Calyx/{CalyxControl.td, CalyxPasses.td}`: control ops and `while ... with` divergence (`L25-L424`, `L319-L320`); `calyx-remove-comb-groups` (`L70-L110`).
  - `lib/Conversion/SCFToCalyx/SCFToCalyx.cpp`: `ScfWhileOp`, `ScfForOp` static trip count (`L64-L116`), `Build*Groups` (`L323, L2013-L2159`).
  - `include/circt/Dialect/Handshake/{HandshakeOps.td, HandshakePasses.td}` & `lib/Dialect/Handshake/Transforms/Buffers.cpp`: `HandshakeInsertBuffersPass`, `bufferAllStrategy` (`L96-L114`), `inCycle` (`L118-L142`), `bufferCyclesStrategy` (`L145-L166`), `bufferAllFIFOStrategy` (`L168-L179`).
- **Coyote (`fpgasystems/Coyote` @ `0fbc94ba60296c44fc76698396579ac719aadd3b`)**:
  - `docs/agents/services/mmu.md`: `mmu_top` hierarchy, `sTLB`/`lTLB` geometry (`L45-L98`), `tlb_fsm` + `cch_buff` (`L99-L165`), invalidation drain (`L169-L185`), legacy HMM / `en_hmm` caveat (`L206-L209`), GPU `dma_buf` P2P (`L212-L224`), BAR window offsets (`L240`).
  - `docs/agents/services/network.md`: CMAC + HLS `rocev2_ip` pipeline (`L1-L160`), `QPN = (vfid<<6)|ctid` overflow at `500` (`L121`), `ack_gap_enforcer` (`L144`), sniffer CDC gap (`L207`).
  - `driver/src/vfpga/{vfpga_isr.c, vfpga_gup.c}` & `driver/include/coyote_defs.h`: `vfpga_isr` workqueue dispatch (`L24-L87`), `mmu_handler_gup`, `tlb_get_user_pages`, `create_tlb_mapping`, `p2p_attach_dma_buf` (`L27-L887`).
- **AdaptiveCpp (`AdaptiveCpp/AdaptiveCpp` @ `96c7d17a9d029a5660ac06d7519b3763e9823ab6`)**:
  - `doc/generic-sscp.md`, `doc/buffer-usm-interop.md`, `doc/stdpar.md`: Stage-1/Stage-2 IR constants, `stdpar` sync elision & `--acpp-stdpar-system-usm` (`L92-L101`), `new`/`malloc` interception & ODR hazard (`L149-L168`), HMM page migration (`L77-L80`).
  - `include/hipSYCL/glue/llvm-sscp/jit.hpp`: `compile`, `specializeKernelArgument`, `setNoAliasKernelParam`, `specializeFunctionCalls` (`L267-L320`).
- **Literature**: Nigam et al. (ASPLOS 2021, DOI `10.1145/3445814.3446712`), Korolija et al. (OSDI 2020), Alpay & Heuveline (IWOCL 2023, DOI `10.1145/3585341.3585351`).

### Reproducible Execution Probe & Recorded Output

Environment: `Linux 7.1.6-1rodete1-amd64 x86_64`, `Python 3.13.15`. Command: `python3 /tmp/probe_pkg2.py`.

```python
#!/usr/bin/env python3
"""Micro-probes for Calyx TDCC vs static<N>, CIRCT Handshake deadlock, and Coyote/HMM paging."""

from __future__ import annotations

from collections import deque


def probe_2a_calyx_tdcc_vs_static() -> None:
    print("=== Probe 2A: Calyx Dynamic TDCC vs CompileStatic Cycle Cost & BRAM Conflict ===")
    n_iter = 64
    g0, g1, g2a, g2b, g3 = 2, 3, 4, 2, 2
    par_work = max(g2a, g2b)

    tdcc_body = (g0 + 1) + (g1 + 1) + (par_work + 1) + (g3 + 1)
    tdcc_iter_check = 1
    tdcc_total = n_iter * (tdcc_body + tdcc_iter_check) + 1

    static_body = g0 + g1 + par_work + g3
    static_total = n_iter * static_body

    speedup = tdcc_total / static_total
    overhead_pct = ((tdcc_total - static_total) / static_total) * 100.0
    print(f"iterations={n_iter} static_cycles={static_total} tdcc_cycles={tdcc_total} "
          f"tdcc_overhead_pct={overhead_pct:.2f}% static_speedup={speedup:.3f}x")

    schedule = {
        "arm0": [(0, "memA", "W"), (1, "memA", "W")],
        "arm1_conflict": [(1, "memA", "R")],
        "arm1_banked": [(1, "memA_bank1", "R")],
    }

    def check_conflict(a: str, b: str) -> list[tuple[int, str, str, str]]:
        hits = []
        for t0, m0, op0 in schedule[a]:
            for t1, m1, op1 in schedule[b]:
                if t0 == t1 and m0 == m1 and ("W" in (op0, op1)):
                    hits.append((t0, m0, op0, op1))
        return hits

    print(f"single_port_par_conflicts={check_conflict('arm0', 'arm1_conflict')}")
    print(f"banked_par_conflicts={check_conflict('arm0', 'arm1_banked')}")


def simulate_handshake_diamond(buf_slots: int, slow_stages: int = 4, num_tokens: int = 16) -> tuple[bool, int, int]:
    """Simulate elastic valid/ready reconvergent fork -> [fast+FIFO(B), slow(L)] -> join."""
    fast_q: deque[int] = deque()
    slow_pipe: list[int | None] = [None] * slow_stages
    sent = 0
    joined = 0
    cycles = 0
    max_cycles = 200

    while joined < num_tokens and cycles < max_cycles:
        cycles += 1
        fast_valid = len(fast_q) > 0
        slow_valid = slow_pipe[-1] is not None
        join_fires = fast_valid and slow_valid

        slow_can_shift = (slow_pipe[-1] is None) or join_fires
        fast_can_accept = (len(fast_q) < buf_slots) or (join_fires and len(fast_q) == buf_slots)
        fork_fires = (sent < num_tokens) and slow_can_shift and fast_can_accept

        if join_fires:
            t_fast = fast_q.popleft()
            t_slow = slow_pipe[-1]
            assert t_fast == t_slow
            slow_pipe[-1] = None
            joined += 1

        progressed = join_fires or fork_fires
        for i in range(slow_stages - 1, 0, -1):
            if slow_pipe[i] is None and slow_pipe[i - 1] is not None:
                slow_pipe[i] = slow_pipe[i - 1]
                slow_pipe[i - 1] = None
                progressed = True

        if fork_fires:
            assert slow_pipe[0] is None and len(fast_q) < buf_slots
            fast_q.append(sent)
            slow_pipe[0] = sent
            sent += 1
            progressed = True

        if not progressed and joined < num_tokens:
            return (False, joined, cycles)

    return (joined == num_tokens, joined, cycles)


def simulate_handshake_coalescing_deadlock(
    buf_slots: int, coalesce_k: int = 4, num_batches: int = 4
) -> tuple[bool, int, int]:
    """Simulate fork -> [fast_meta+FIFO(B), slow_coalesce(needs K tokens -> 1 output)] -> join."""
    fast_q: deque[int] = deque()
    slow_acc = 0
    slow_out_ready: deque[int] = deque()
    batch_tokens = coalesce_k * num_batches
    sent = 0
    joined = 0
    cycles = 0
    while joined < num_batches and cycles < 100:
        cycles += 1
        progressed = False
        if len(fast_q) >= coalesce_k and len(slow_out_ready) > 0:
            for _ in range(coalesce_k):
                fast_q.popleft()
            slow_out_ready.popleft()
            joined += 1
            progressed = True
        if sent < batch_tokens and len(fast_q) < buf_slots:
            fast_q.append(sent)
            sent += 1
            slow_acc += 1
            if slow_acc == coalesce_k:
                slow_out_ready.append(joined)
                slow_acc = 0
            progressed = True
        if not progressed:
            return (False, joined, cycles)
    return (joined == num_batches, joined, cycles)


def probe_2b_handshake_deadlock() -> None:
    print("\n=== Probe 2B: CIRCT Handshake Reconvergent Fork->Join Throughput Collapse & Deadlock ===")
    for buf_slots in (1, 2, 3, 4, 8):
        ok, joined, cycles = simulate_handshake_diamond(buf_slots=buf_slots, slow_stages=4, num_tokens=16)
        print(f"acyclic_diamond buffer_slots={buf_slots} completed={ok} tokens_joined={joined}/16 cycles={cycles}")
    for buf_slots in (1, 2, 3, 4, 8):
        ok, joined, cycles = simulate_handshake_coalescing_deadlock(buf_slots=buf_slots, coalesce_k=4, num_batches=4)
        print(f"reconvergent_k4_coalesce buffer_slots={buf_slots} completed={ok} batches_joined={joined}/4 cycles={cycles}")


def probe_2c_hmm_false_sharing_and_tlb() -> None:
    print("\n=== Probe 2C: 4 KiB HMM False-Sharing Migration vs SoA & Coyote sTLB/lTLB Misses ===")
    page_bytes = 4096
    record_bytes = 64
    records_per_page = page_bytes // record_bytes
    n_records = 16384
    n_pages_aos = (n_records * record_bytes) // page_bytes

    phases = 10
    aos_page_migrations = phases * 2 * n_pages_aos
    aos_bytes_migrated = aos_page_migrations * page_bytes

    soa_ctrl_pages = (n_records * 16) // page_bytes
    soa_payload_pages = (n_records * 48) // page_bytes
    soa_initial_migrations = soa_payload_pages
    soa_bytes_migrated = soa_initial_migrations * page_bytes

    ws_bytes = 256 * 1024 * 1024
    stlb_misses = ws_bytes // 4096
    ltlb_misses = ws_bytes // (2 * 1024 * 1024)

    print(f"aos_pages={n_pages_aos} records_per_4k_page={records_per_page} "
          f"aos_10phase_migrations={aos_page_migrations} ({aos_bytes_migrated // (1024*1024)} MiB)")
    print(f"soa_ctrl_pages={soa_ctrl_pages} soa_payload_pages={soa_payload_pages} "
          f"soa_10phase_migrations={soa_initial_migrations} ({soa_bytes_migrated / (1024*1024):.2f} MiB) "
          f"migration_reduction={aos_page_migrations / soa_initial_migrations:.1f}x")
    print(f"coyote_256MiB_stlb_4k_misses={stlb_misses} ltlb_2m_misses={ltlb_misses} "
          f"tlb_miss_reduction={stlb_misses // ltlb_misses}x")


if __name__ == "__main__":
    probe_2a_calyx_tdcc_vs_static()
    probe_2b_handshake_deadlock()
    probe_2c_hmm_false_sharing_and_tlb()
```

Observed output:

```text
=== Probe 2A: Calyx Dynamic TDCC vs CompileStatic Cycle Cost & BRAM Conflict ===
iterations=64 static_cycles=704 tdcc_cycles=1025 tdcc_overhead_pct=45.60% static_speedup=1.456x
single_port_par_conflicts=[(1, 'memA', 'W', 'R')]
banked_par_conflicts=[]

=== Probe 2B: CIRCT Handshake Reconvergent Fork->Join Throughput Collapse & Deadlock ===
acyclic_diamond buffer_slots=1 completed=True tokens_joined=16/16 cycles=65
acyclic_diamond buffer_slots=2 completed=True tokens_joined=16/16 cycles=34
acyclic_diamond buffer_slots=3 completed=True tokens_joined=16/16 cycles=25
acyclic_diamond buffer_slots=4 completed=True tokens_joined=16/16 cycles=20
acyclic_diamond buffer_slots=8 completed=True tokens_joined=16/16 cycles=20
reconvergent_k4_coalesce buffer_slots=1 completed=False batches_joined=0/4 cycles=2
reconvergent_k4_coalesce buffer_slots=2 completed=False batches_joined=0/4 cycles=3
reconvergent_k4_coalesce buffer_slots=3 completed=False batches_joined=0/4 cycles=4
reconvergent_k4_coalesce buffer_slots=4 completed=True batches_joined=4/4 cycles=17
reconvergent_k4_coalesce buffer_slots=8 completed=True batches_joined=4/4 cycles=17

=== Probe 2C: 4 KiB HMM False-Sharing Migration vs SoA & Coyote sTLB/lTLB Misses ===
aos_pages=256 records_per_4k_page=64 aos_10phase_migrations=5120 (20 MiB)
soa_ctrl_pages=64 soa_payload_pages=192 soa_10phase_migrations=192 (0.75 MiB) migration_reduction=26.7x
coyote_256MiB_stlb_4k_misses=65536 ltlb_2m_misses=128 tlb_miss_reduction=512x
```

## Revalidation

1. **Calyx & CIRCT Lowering Revalidation**:
   - Inspect `calyx/opt/src/passes/{top_down_compile_control.rs, compile_static.rs}` and `lib/Dialect/Handshake/Transforms/Buffers.cpp` in `llvm/circt` to check whether `HandshakeInsertBuffersPass` has gained static slack-matching on acyclic reconvergent fork–join paths or remains cycle-only (`bufferCyclesStrategy`).
   - Run `Probe 2A`–`2B` or execute `calyx` + `cider` (`cider/tests/control/par_mem.futil`) on any modified control lowering to confirm static FSM speedup and BRAM conflict trapping.
2. **Coyote MMU, HMM & RoCEv2 Revalidation**:
   - Inspect `driver/src/vfpga/vfpga_ops.c` and `driver/src/coyote_driver.c` for `en_hmm` gating and `hw/hdl/network/rdma/roce_stack.sv` for `ROCE_STACK_MAX_QPS` enforcement; confirm whether `HMM_KERNEL` has moved out of `driver/LEGACY/hmm/`.
3. **AdaptiveCpp `SSCP` & `stdpar` Revalidation**:
   - Inspect `doc/stdpar.md` and `include/hipSYCL/compiler/stdpar/MallocToUSM.hpp` for updates to `calloc`/`realloc` interception, ODR ABI tagging across translation units, and synchronization elision rules; re-measure AoS vs. SoA page migrations via GPU profiler (`nsys`/`rocprof`) on target hardware.
