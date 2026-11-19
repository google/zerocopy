# Multicore Real-Time Interference, Hardware Cache/Bandwidth Partitioning, PREM, MrsP Locking, and Prosa Mechanized Schedulability

## Summary

On commercial off-the-shelf (COTS) multicore processors, single-core worst-case execution time (WCET) bounds and uniprocessor locking invariants fail silently even when real-time tasks share zero software locks and zero virtual memory. Cross-core interference propagates through a stack of implicit shared hardware queues—Last-Level Cache (LLC) ways and sets, Miss Status Holding Registers (MSHRs), LLC write-back buffers, coherence directories/snoop filters, on-chip interconnects, and DRAM bank row-buffers under FR-FCFS memory controllers—inducing multi-fold latency amplification that breaks hard deadlines and fails airborne certification objectives (`CAST-32A`, `EASA AMC 20-193`, `FAA AC 20-193`).

Four complementary layers are required to restore analyzable multicore real-time timing, each with strict architectural limits:

1. **Spatial and temporal memory-hierarchy partitioning** (`Intel RDT CAT/CDP/MBA`, `Arm MPAM`, hypervisor `page coloring`, `PALLOC`, `MemGuard`): Way-level LLC partitioning (`CAT` / `MPAM CPOR`) eliminates LLC capacity evictions across partitions, **but does not isolate shared MSHRs, LLC write-back buffers, DRAM bank row-buffers, or interconnect arbiters**. Closing those residual channels requires combining LLC partitioning with DRAM bank partitioning (`PALLOC` XOR bank coloring) and periodic or hardware memory-bandwidth regulation (`MemGuard` monitoring both LLC read misses and LLC write-backs, `Intel MBA` / `mba_sc`, or `Arm MPAM MBW_MAX` / `FEAT_MPAM_PE_BW_CTRL`). Even with periodic regulation `(Q, P)`, boundary-straddling bursts deliver up to $2Q$ transactions inside intervals shorter than $P$ (verified via executable probe at $33.3\times$ average rate over $60\,\mu\text{s}$), and shared DRAM bank conflicts multiply that stall by $3.0\times$.
2. **Compiler/runtime execution restructuring (`PREM` and Cache Pseudo-Locking)**: The Predictable Execution Model splits real-time tasks into serialized *Memory Phases* (prefetching code/data into private cache or scratchpad under arbitrated bus access) and interference-free *Execution Phases* (strictly cache-resident, zero main-memory traffic). Linux `resctrl` Cache Pseudo-Locking provides a hardware-assisted approximation via exclusive `CAT` masks, but carries no architectural residency guarantee against `CLFLUSH`/`WBINVD`, cache-shrinking C-states, or un-enforced post-`mmap` core affinity.
3. **Multiprocessor real-time locking (`MPCP`, `MSRP`, `OMLP`, `MrsP`)**: Uniprocessor Stack Resource Policy (`SRP`) and Priority Ceiling Protocol (`PCP`) break across cores because remote lock holders can be preempted locally while remote cores wait. `MPCP` uses suspension + remote ceiling boosting (and virtual spinning in `MPCP-VS`, disallowing nesting in `LITMUS^RT`); `MSRP` uses non-preemptive FIFO spinning (blocking unrelated urgent local tasks); `OMLP` achieves asymptotic $O(m)$ priority-inversion blocking optimality via dual FIFO+priority queues; and Burns–Wellings `MrsP` combines per-processor priority ceilings, FIFO queues, preemptable spinning, and **migratory helping** (implemented via sticky thread queues in `RTEMS`). Our discrete-event probe confirms that `MrsP` eliminates unrelated urgent-task blocking (`0` vs `7` ticks under `MSRP`), **but** unconstrained migration ping-pong under non-zero migration cost (`mig_cost = 1`) completely erodes helping gains on contended threads unless migration bounds or deferred-return policies are enforced.
4. **Mechanized schedulability foundations (`Prosa` / `RefinedProsa`)**: `Prosa` (Rocq/Coq `v0.6`) replaces fragile pen-and-paper response-time arguments with an abstract busy-window theorem (`aRTA`) parameterized by interference bounds and supply functions, while `RefinedProsa` (PLDI 2025) bridges abstract scheduling models down to verified C scheduler code for interrupt-free uniprocessor kernels. Bridging `Prosa` end-to-end across multicore hardware interference channels, DRAM-bank contention, and `MrsP` migratory helping remains an open verification frontier.

## Applicability

This report synthesizes primary architecture documentation, upstream kernel/hypervisor/RTOS source code, peer-reviewed real-time systems literature, and standalone executable discrete-event probes across the following relationships:

- **Hardware partitioning mechanisms vs. kernel/firmware implementations**: `Intel RDT` (`CAT`, `CDP`, `MBA`, `MBM`) and `AMD` extensions (`SMBA` for CXL.memory) are characterized via `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `Documentation/filesystems/resctrl.rst`, `fs/resctrl/rdtgroup.c`) and `intel/intel-cmt-cat` (`ac1a9f606eeadb447b7706d17d9fa76fa89a279b`). `Arm MPAM` (`ARM DDI 0598`, Armv8.4-A+) is characterized via mainline Linux's MPAM driver (`drivers/resctrl/mpam_devices.c` at the same Linux revision) and EL3/EL2 trap/bandwidth-control initialization in `ARM-software/arm-trusted-firmware` (`0d2c4394f010bc91327ee1ee923bf6d70d446bb7`).
- **Software memory-hierarchy isolation vs. residual microarchitectural channels**: `heechul/memguard` (`613be205f6b2351743866852f631e664d8e4ace4`), `heechul/palloc` (`d470088a1eb21b0dca99f475404225222c956732`), and `bao-project/bao-hypervisor` (`c3907240d0eca92a338b20f0c43ecbf3f9cd60bd`) are evaluated against MSHR blocking (`Valsan et al., RTAS 2016`), shared-cache write-back DoS (`Bechtel & Yun, RTAS 2019`), and DRAM controller interference bounds (`Kim et al., RTAS 2014`).
- **Execution restructuring (`PREM`) vs. locking protocols (`MPCP`, `MSRP`, `OMLP`, `MrsP`) vs. mechanized analysis (`Prosa`)**: `PREM` (`Pellizzoni et al., RTAS 2011`) addresses memory-bus contention without software locks; `RTEMS/rtems` (`17bb6e147c83309ce3bbf43e4f77600a4c64ea0b`) and `LITMUS-RT/litmus-rt` (`7811e5b1eaef361f45659a1f6d49acb050b1f316`) supply concrete production implementations of `MrsP`, `MPCP`/`MPCP-VS`, `DPCP`, `FMLP`, and `PCP`, compared against `Burns & Wellings (ECRTS 2013)`, `Garrido et al. (Ada-Europe 2017)`, `Gai et al. (RTSS 2001)`, `Rajkumar (ICDCS 1990)`, `Brandenburg & Anderson (RTSS 2010)`, and `Prosa` (`v0.6`, `ECRTS 2016/2020/2022`, `PLDI 2025`).

**Scope constraints:** Findings on hardware partitioning apply to shared-memory SMP multicore SoCs (x86-64 Xeon/Core with Intel RDT or AMD QoS, Armv8.4-A+ with MPAM, and Arm/RISC-V embedded SoCs supporting stage-2 MMU page coloring). Locking protocol proofs assume partitioned fixed-priority (`P-FP`) or global/clustered EDF/FP scheduling with cache-coherent shared memory and bounded atomic instruction latency. Linux `MemGuard` and `PALLOC` observations reflect out-of-tree kernel module/patch designs targeting Linux 3.x–6.14 rather than mainline upstream APIs.

## Findings

### 1. Shared Microarchitectural Interference Channels Beyond LLC Capacity

**Basis:** normative (hardware/certification specifications) + source (`palloc`, `memguard`) + derived (published microarchitectural models).

Isolating shared Last-Level Cache (LLC) capacity alone does **not** achieve timing composability across cores. On modern COTS multicore SoCs, at least six coupled microarchitectural channels propagate worst-case execution time (WCET) interference from co-running cores even when virtual address spaces and LLC ways are completely disjoint:

| Interference Channel | Shared Hardware Structure | Mechanism of Cross-Core Delay | Defeated by LLC Way Partitioning Alone? | Primary Mitigation Required |
| :--- | :--- | :--- | :--- | :--- |
| **1. LLC Capacity / Conflict Eviction** | Shared set-associative LLC data/tag arrays | Co-runner fills evict victim's working set into DRAM | **Yes** (disjoint ways via `CAT`/`MPAM CPOR` or disjoint sets via page coloring) | Way partitioning (`CAT`/`MPAM`) or set coloring (`Bao`) |
| **2. Non-Blocking Cache MSHRs** | Miss Status Holding Registers (typically 8–20 entries per cache bank/slice) | Co-runner generates parallel cache misses exhausting shared MSHRs; **all** subsequent cache accesses (even hits to private ways!) stall until an MSHR drains | **No** (`Valsan et al., RTAS 2016`) | Per-core/per-partition MSHR limits (hardware) or bandwidth throttling (`MemGuard`/`MPAM`) |
| **3. LLC Write-Back Buffer & Fill Queue** | Dirty eviction write-back queue between LLC and memory controller | Co-runner performs dirty-line streaming (`store`-heavy) saturating shared write-back buffers; stalls victim LLC misses even when read-miss counters stay low | **No** (`Bechtel & Yun, RTAS 2019`) | Separate LLC write-back regulation (`MemGuard` `write_event` + `read_event`) |
| **4. Coherence Directory / Snoop Filter** | Inclusive snoop filter or directory entries tracking private L1/L2 lines | Co-runner allocates distinct lines in the same directory set, causing **inclusion-victim back-invalidations** of the victim's private L1/L2 cache lines | **No** (directory associativity is decoupled from LLC ways) | Non-inclusive/victim LLCs, directory partitioning, or set coloring covering directory index bits |
| **5. DRAM Bank Row-Buffers & Bus Turnaround** | Shared DRAM channels, ranks, banks, and FR-FCFS memory controller queues | Co-runner closes victim's open row-buffer (`row hit` $\approx 15\text{ ns}$ $\to$ `row conflict` $t_{\text{RP}}+t_{\text{RCD}}+t_{\text{CAS}} \approx 45\text{ ns}$), plus `read-to-write` ($t_{\text{RTW}}$) / `write-to-read` ($t_{\text{WTR}}$) bus turnaround and `tFAW` activation windows (`Kim et al., RTAS 2014`) | **No** | DRAM bank coloring (`PALLOC` with XOR-mapping) + bus/bandwidth reservation |
| **6. On-Chip Interconnect (NoC / Ring / Mesh)** | Shared ring stops, mesh routers, credit queues | Heavy traffic from other cores consumes link credits and increases hop arbitration delay | **No** | TDMA/PREM phase scheduling or `MPAM` priority partitioning (`INTPRI`/`DSPRI`) |

#### 1.1 MSHR Exhaustion and Write-Back Denial-of-Service
- **MSHR Blocking (`Valsan et al., RTAS 2016`, DOI `10.1109/RTAS.2016.7461361`)**: Non-blocking shared caches use a finite pool of MSHRs to track outstanding misses. When co-running best-effort cores issue memory-level-parallel (MLP) misses into their *own* dedicated cache ways, they can saturate the shared LLC's MSHR pool. Once MSHRs are full, the cache pipeline stalls **all** incoming lookups—including cache *hits* from a real-time core operating entirely inside its private LLC partition. In `Valsan et al.`, blocking MSHR contention caused slowdowns exceeding $5\times$ even under strict cache-way partitioning.
- **Write-Back Buffer Saturation (`Bechtel & Yun, RTAS 2019`, DOI `10.1109/RTAS.2019.00037`)**: Even when a bandwidth regulator monitors LLC read-miss PMU counters, an adversary performing `store` misses that allocate and dirty lines inside a small private cache partition triggers sustained dirty evictions into the shared write-back buffer. Because write-backs bypass read-miss counters and incur expensive DRAM write-to-read bus turnarounds ($t_{\text{WTR}}$), write-heavy co-runners can degrade an isolated real-time victim by $>10\times$ unless write-backs are explicitly regulated.

#### 1.2 DRAM Row-Buffer Interference and XOR Bank Mapping
- **FR-FCFS Reordering & Per-Bank Bounds (`Kim et al., RTAS 2014`, DOI `10.1109/RTAS.2014.6925998`)**: COTS DDR memory controllers employ First-Ready, First-Come-First-Served (FR-FCFS) scheduling, which prioritizes *row-buffer hits* over older *row-buffer misses*. In a shared DRAM bank, a co-runner issuing sequential hits can starve a real-time core's pending request up to the controller's starvation-cap threshold, while interleaving requests to different rows turns every victim access into a row conflict ($t_{\text{RP}} + t_{\text{RCD}} + t_{\text{CAS}}$).
- **XOR Physical-to-Bank Hashing (`heechul/palloc`, `palloc_xormap-6.14.patch`)**: Older DRAM controllers mapped bank indices directly from contiguous physical address bits, allowing simple bitmask coloring. Modern Intel and Arm memory controllers XOR multiple high-order row bits with lower bank bits to reduce bank conflicts on average workloads. Inspecting `heechul/palloc` (`d470088a1eb21b0dca99f475404225222c956732`, `palloc_xormap-6.14.patch`, `mm/page_alloc.c` additions) shows that `PALLOC` had to replace its single bitmask with an array of XOR-parity masks (`static unsigned long sysctl_palloc_masks[MAX_PALLOC_BITS]`), where each entry `sysctl_palloc_masks[i]` specifies the set of physical address bit positions XOR-folded together to compute bank-color bit `i`. Pages in the Linux buddy allocator (`zone->color_list[c]`, `zone->color_bitmap`) are then binned by XOR-color and assigned per-cgroup via `CONFIG_CGROUP_PALLOC`. Without matching the hardware's exact XOR hash (discovered empirically via timing probes such as `palloc/mc-mapping.c` / `detect-mc-mapping-xor.sh`), naive page coloring fails to isolate DRAM banks.

#### 1.3 Regulatory Certification Objectives (`CAST-32A` and `A(M)C 20-193`)
**Basis:** normative / documentation (`CAST-32A`, `EASA AMC 20-193`, `FAA AC 20-193`).

Civil aviation authorities formalized multicore interference requirements in `CAST-32A` (2016) and superseded it with harmonized binding guidance `EASA AMC 20-193` (2022) and `FAA AC 20-193` (2024). Four resource-usage objectives govern interference analysis:
- **`MCP_Resource_Usage_1`**: Identify all shared hardware resources and processor configuration settings capable of affecting execution timing or integrity across cores.
- **`MCP_Resource_Usage_2`**: Define and control the allocation and configuration of shared resources across hosted software applications (including robust resource and time partitioning, RRTP).
- **`MCP_Resource_Usage_3`**: Identify all **interference channels** (`ICs`) across active cores and verify the effectiveness of chosen mitigations (either eliminating the channel via partitioning/scheduling or bounding worst-case interference conservatively).
- **`MCP_Resource_Usage_4`**: Verify WCET bounds and mitigation robustness under maximum worst-case stress (e.g., adversarial interference generators saturating memory controllers, caches, and interconnects concurrently with the target software).

---

### 2. Hardware Cache and Memory-Bandwidth Partitioning (`Intel RDT`, `Arm MPAM`, `Page Coloring`, `MemGuard`)

**Basis:** source (`torvalds/linux`, `intel/intel-cmt-cat`, `ARM-software/arm-trusted-firmware`, `bao-project/bao-hypervisor`, `heechul/memguard`) + documentation (`resctrl.rst`) + execution (`probe_multicore_rt.py`).

#### 2.1 Intel Resource Director Technology (`CAT`, `CDP`, `MBA`, `SMBA`) and Linux `resctrl`
Direct inspection of `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `Documentation/filesystems/resctrl.rst` lines 22–26, 851–1160) and `intel/intel-cmt-cat` (`ac1a9f606eeadb447b7706d17d9fa76fa89a279b`, `lib/allocation.c` lines 91–1610) establishes the concrete hardware/OS interface and critical engineering pitfalls:

1. **Class of Service (`CLOSID`) & Cache Bit Masks (`CBM`)**:
   - Each logical CPU selects its active `CLOSID` via `IA32_PQR_ASSOC` (`PQOS_MSR_ASSOC`, shifted by `PQOS_MSR_ASSOC_QECLOS_SHIFT`, `allocation.c:91,1305`).
   - Each `CLOSID` maps to an L3 or L2 Capacity Bit Mask MSR (`PQOS_MSR_L3CA_MASK_START + class_id`, or `class_id * 2` when Code and Data Prioritization `CDP` splits code and data into `L3CODE`/`L3DATA` via `PQOS_MSR_L3_QOS_CFG_CDP_EN`, `allocation.c:390,1513`).
   - **Contiguous-Mask Hardware Constraint**: On many Intel CPUs, `CBM` bitmasks MUST form a single contiguous run of `1` bits (`0x3`, `0x6`, `0xC` valid; `0x5`, `0xA` invalid unless `/sys/fs/resctrl/info/{resource}/sparse_masks` reports `1`; `resctrl.rst:857-861`). Furthermore, under **Sub-NUMA Clustering (SNC)**, an L3 `CBM` applies across all SNC nodes, dividing the effective cache capacity per bit by the number of SNC nodes (`resctrl.rst:882-886`).
   - **Allocation-Only Semantics**: `CAT` restricts *line fills (allocations)*, not hits. A core can still read/write lines already residing in cache ways outside its `CBM`. This property enables **Cache Pseudo-Locking** (`resctrl.rst:1067-1160`), where the kernel disables prefetchers and preemption, flushes cache, loads a physically contiguous buffer using an exclusive temporary `CLOSNEW`, and then withdraws those ways from every active `CLOS` so no workload can evict them. **Critical caveats documented in `resctrl.rst:1103-1118`**: pseudo-locking provides *no strict architectural guarantee*—`INVD`, `WBINVD`, and `CLFLUSH` still evict locked lines; deeper CPU C-states shrink or power-gate cache (requiring automatic C-state restriction); and core-affinity compliance is checked only at `mmap()` time, not enforced dynamically thereafter.
2. **Intel `MBA` (Memory Bandwidth Allocation) Nonlinearities vs. `mba_sc` and AMD `SMBA`**:
   - On Intel SKUs, hardware `MBA` inserts programmable delay values between the L2 cache and the shared interconnect/L3 (`PQOS_MSR_MBA_MASK_START + class_id`, `allocation.c:976`), exposed as approximate percentage steps (`min_bandwidth` + $N \cdot \text{bandwidth\_gran}$, `resctrl.rst:894-901`).
   - **Two Real-Time Pitfalls Documented in `resctrl.rst:903-948`**:
     1. *Per-Core vs. Package Bandwidth Decoupling*: Because `MBA` throttles per-core L2-external bandwidth while DRAM saturation occurs at the package L3-external bus, configuring 20 threads at `50%` bandwidth on a 24-core SKU (where aggregate L2 external is $240\text{ GB/s}$ but L3 external is $100\text{ GB/s}$) saturates DRAM at $100\text{ GB/s}$ regardless—and a `10%` mask allows $10\text{ GB/s}$ for 1 thread vs. $40\text{ GB/s}$ for 4 threads!
     2. *SMT Co-Thread Coupling*: On SKUs with per-core throttling (`thread_throttle_mode`), placing a high-bandwidth thread and a low-bandwidth thread on sibling SMT hyperthreads throttles *both* to the lower limit (`resctrl.rst:903-906`).
     3. *Software Feedback Workaround (`mba_sc`)*: Mounting `resctrl` with `mba_MBps` enables a kernel software feedback loop (`mba_sc`) that polls `MBM` counters periodically and adjusts hardware delay values to hold actual bandwidth below a MiB/s cap (`resctrl.rst:937-948`). Because `mba_sc` is a closed-loop reactive controller, it still exhibits transient overshoots at sub-polling timescales.
   - **AMD `MBA` and `SMBA`**: On AMD platforms, `MB` schemata directly specify bandwidth limits in multiples of $1/8\text{ GB/s}$ (`resctrl.rst:1027-1045`), and `SMBA` (Slow Memory Bandwidth Allocation, `PQOS_MSR_SMBA_MASK_START_AMD`, `allocation.c:1204`) provides a separate bandwidth throttle specifically for CXL.memory tiers (`resctrl.rst:993-1011`).

#### 2.2 Arm MPAM (`ARM DDI 0598`) and Mainline Linux / TF-A Implementation
Direct inspection of `torvalds/linux` (`drivers/resctrl/mpam_devices.c`, lines 301–454, 846–1060, 1510–1970) and `ARM-software/arm-trusted-firmware` (`lib/extensions/mpam/mpam.c`, lines 14–91) reveals a far richer—and more heterogeneous—architectural surface than Intel RDT:

- **End-to-End Transaction Tagging (`PARTID` + `PMG`)**: Every memory transaction emitted by a Processing Element (PE), SMMU/DMA master, or GPU carries a Partition ID (`PARTID`, up to 16-bit) and a Performance Monitoring Group (`PMG`, up to 8-bit) derived from exception-level system registers (`MPAM0_EL1`, `MPAM1_EL1`, `MPAM2_EL2`, `MPAM3_EL3`). Firmware (`mpam_enable_per_world`, `tf_mpam.c:14-27`) sets `MPAM3_EL3_MPAMEN_BIT` and clears `MPAM3_EL3_TRAPLOWER_BIT` so OS/hypervisors can switch `PARTID`s on context switch without trapping to EL3.
- **Memory System Components (`MSC`) and Resource Instance Selectors (`RIS`)**: Unlike Intel's fixed core-MSR model, Arm MPAM places MMIO-mapped or system-register-mapped `MSC`s at arbitrary points along the memory fabric (L2, L3, SLC, interconnect, DRAM controller). Each `MSC` can expose up to 16 `RIS` instances (`MPAMCFG_PART_SEL_RIS`, `mpam_devices.c:444-454`) and supports optional internal `PARTID` narrowing (`MPAMCFG_PART_SEL_INTERNAL`, mapping many OS `PARTID`s onto fewer hardware `intpartid`s).
- **Five Orthogonal Control Classes Probed in `mpam_ris_hw_probe()` (`mpam_devices.c:956-1059`)**:
  1. **Cache Portion Partitioning (`CPOR`)**: Way/portion bitmap (`MPAMCFG_CPBM`, width `cpbm_wd`), directly analogous to Intel `CAT`.
  2. **Cache Capacity Partitioning (`CCAP`)**: Fractional maximum capacity limit (`MPAMCFG_CMAX`, width `cmax_wd`), optional soft-limit mode (`HAS_CMAX_SOFTLIM`), minimum guaranteed capacity (`HAS_CMIN`), and associativity cap (`MPAMCFG_CASSOC`, `cassoc_wd`)—enabling soft work-conserving isolation unavailable in Intel `CAT`.
  3. **Memory Bandwidth Partitioning (`MBW`)**: Supports *four* distinct regulators—portion bitmaps (`MPAMCFG_MBW_PBM`, `mbw_pbm_bits`), fractional maximum caps (`MPAMCFG_MBW_MAX`, fixed-point fraction clamped to `min(bwa_wd, 16)` bits at `mpam_devices.c:1026`), minimum guarantees (`MPAMCFG_MBW_MIN`), and proportional sharing weights (`MPAMCFG_MBW_PROP`).
  4. **Priority Partitioning (`PRI`)**: Assigns internal interconnect priority (`MPAMCFG_PRI_INTPRI`) and downstream memory-controller priority (`MPAMCFG_PRI_DSPRI`) per `PARTID` (`mpam_devices.c:1039-1058, 1961-1969`), directly addressing interconnect arbitration channels.
  5. **PE-Side Bandwidth Control (`FEAT_MPAM_PE_BW_CTRL`, `tf_mpam.c:29-91`)**: Newer Armv8.x/v9 extensions add core-local bandwidth limiters (`MPAMBW0_EL1`, `MPAMBW1_EL1`, `MPAMBW2_EL2`, `MPAMBW3_EL3`) with hardware scaling and hard-limit bits (`HARDLIM`), throttling traffic right at the PE before it even enters the interconnect.
- **Production Silicon Errata & Spec Traps Observed in `mpam_devices.c:846-954, 1531-1586`**:
  - **NVIDIA T241 (Grace) errata**: `T241-MPAM-1` (`T241_SCRUB_SHADOW_REGS`), `T241-MPAM-4` (`T241_FORCE_MBW_MIN_TO_ONE`), and `T241-MPAM-6` (`T241_MBW_COUNTER_SCALE_64`, requiring software to multiply raw `MBWU` readings by `64` at line 1565!).
  - **Arm CMN-650 erratum 3642720 (`IGNORE_CSU_NRDY`)**: Combined with Arm spec `IHI009A.a` permitting hardware without automatic `MSMON___NRDY` (not-ready) tracking to leave the bit software-writable rather than `RES0`, the Linux driver must actively probe `MSMON_CSU` with write/read toggles (`mpam_ris_hw_probe_csu_nrdy`, lines 903–954) to avoid permanently returning `-EBUSY` on cache occupancy reads.
  - **Consequence for Formal Verification**: Certifying an Arm MPAM-based WCET bound cannot stop at the architectural manual (`DDI 0598`); it must bind to the exact `MSC` `IIDR` revision and verified workaround set.

#### 2.3 Hypervisor Page Coloring (`Bao`) vs. Hardware Way Partitioning
Inspecting `bao-project/bao-hypervisor` (`c3907240d0eca92a338b20f0c43ecbf3f9cd60bd`, `src/core/mem.c:59-177`) illustrates software set-level cache coloring: the hypervisor partitions physical page frames by the address bits overlapping the LLC set-index field (`cpu()->as.colors` passed to `mem_alloc_ppages()`), mapping only disjoint color subsets into each guest VM's stage-2 page tables.

| Property | Hardware Way Partitioning (`CAT` / `MPAM CPOR`) | Hypervisor Page Coloring (`Bao` / `Jailhouse`) | DRAM Bank Coloring (`PALLOC`) |
| :--- | :--- | :--- | :--- |
| **Hardware ISA Support Required** | Yes (`Intel RDT` / `Arm MPAM`) | No (standard 4 KiB MMU / stage-2 paging) | No (MMU + reverse-engineered bank XOR bits) |
| **Partitioning Dimension** | Cache ways (reduces effective associativity per partition!) | Cache sets (preserves full cache associativity!) | DRAM banks (eliminates inter-core row conflicts) |
| **Memory Capacity Coupling** | **Decoupled** (any DRAM frame can map to any `CLOS`/`PARTID`) | **Tightly coupled** (1/k cache colors locks 1/k of physical DRAM!) | **Tightly coupled** (each bank owns a fixed fraction of DRAM) |
| **Hugepages (`2 MiB` / `1 GiB`)** | Fully compatible | **Broken** (hugepage offset bits span cache set-index bits; increases TLB pressure) | **Broken** (bank bits lie in PA bits 12–20) |
| **DMA / Non-CPU Masters** | `Arm MPAM` supports SMMU `PARTID`; `Intel CAT` uses I/O QoS (`PQOS_MSR_L3_IO_QOS_CFG`) | Automatically covers DMA if IOMMU maps colored buffers | Automatically covers DMA if buffers are bank-colored |
| **Dynamic Reconfiguration Cost** | $O(1)$ MSR/MMIO write (stale lines drain lazily) | Expensive (requires page migration / copy + TLB shootdown) | Expensive (page migration) |

#### 2.4 `MemGuard` Software Bandwidth Regulation & Periodic-Server Burstiness
Direct inspection of `heechul/memguard` (`613be205f6b2351743866852f631e664d8e4ace4`, `memguard.c:163-580`) shows how software memory-bandwidth reservation operates on COTS cores lacking hardware `MBA`/`MPAM`:
- **Dual Read/Write PMU Regulation**: `memguard.c:172-173` tracks **both** `g_read_counter_id` (`PMU_LLC_MISS_COUNTER_ID`) and `g_write_counter_id` (`PMU_LLC_WB_COUNTER_ID`) over a synchronized per-core `hrtimer` period (`g_period_us = 1000`, line 163). When either hardware PMU counter overflows its per-period budget, the NMI/hardirq handler (`event_overflow_callback` / `event_write_overflow_callback`, lines 376–398) queues an `irq_work` callback (`memguard_read_process_overflow`, lines 436–543) to safely wake a highest-priority per-core `throttle_thread` (`wake_up_interruptible(&cinfo->throttle_evt)`, line 542) that idles the core until the next period boundary.
- **Reclaiming & Exclusive Modes**: When `g_use_reclaim` is enabled (lines 457–489), an overflowing core first reclaims its own donated slack, then harvests slack from other online cores up to `g_qmin`. If *all* active cores become throttled (`cpumask_equal(global->throttle_mask, global->active_mask)`, line 508), `g_use_exclusive == 2` (`SP`: spare bandwidth sharing from RTAS 2013) unthrottles all cores for the remainder of the period, whereas `g_use_exclusive == 5` (`PS`: period shortening) immediately triggers `__newperiod()` across all cores. **Hard-real-time caveat**: Enabling `g_use_exclusive == 2` sacrifices strict worst-case latency isolation if a real-time job arrives mid-period while best-effort cores are running unthrottled in exclusive mode!
- **Worst-Case Boundary-Straddling Burstiness (Verified by Execution)**:
  **Basis:** execution (`/tmp/probe_multicore_rt.py`, Part 2) + derived.
  For a periodic regulator enforcing budget $Q$ transactions per period $P$ with peak drain time $t_{\text{burst}} = Q \cdot t_{\text{tx}}$, the exact supremum of interfering transactions arriving from one core inside an arbitrary victim window of length $L$ occurs when Period 0 places its burst at $[P - t_{\text{burst}}, P]$ and Periods $k \ge 1$ place their bursts at $[kP, kP + t_{\text{burst}}]$:
  $$W_{\max}(L) = \min\!\big(L, t_{\text{burst}}\big)\frac{Q}{t_{\text{burst}}} + \sum_{k=1}^{\infty} \max\!\big(0, \min(P - t_{\text{burst}} + L, kP + t_{\text{burst}}) - kP\big)\frac{Q}{t_{\text{burst}}}$$
  For a representative configuration ($P = 1000\,\mu\text{s}$, $Q = 2000\text{ tx/period}$, $t_{\text{hit}} = 15\text{ ns} \implies t_{\text{burst}} = 30\,\mu\text{s}$, $3$ interfering cores, $t_{\text{row-conflict}} = 45\text{ ns}$), our standalone Python probe produced:

| Victim Window $L$ | Naive Avg Rate (`tx/core`) | Worst-Case `MemGuard` Burst (`tx/core`) | Burst / Avg Amplification | 3-Core DRAM Stall (Private Banks, `15 ns/tx`) | 3-Core DRAM Stall (Shared Bank Conflicts, `45 ns/tx`) |
| :---: | :---: | :---: | :---: | :---: | :---: |
| `30.0 us` | `60` | `2000` | **`33.33x`** | `90.0 us` | `270.0 us` |
| `60.0 us` | `120` | `4000` | **`33.33x`** | `180.0 us` | **`540.0 us`** (`9.0x` window!) |
| `200.0 us` | `400` | `4000` | `10.00x` | `180.0 us` | `540.0 us` |
| `1000.0 us` | `2000` | `4000` | **`2.00x`** | `180.0 us` | `540.0 us` |
| `1060.0 us` | `2120` | `6000` | `2.83x` | `270.0 us` | `810.0 us` |
| `2000.0 us` | `4000` | `6000` | `1.50x` | `270.0 us` | `810.0 us` |

  **Engineering takeaway**: Average-bandwidth budgeting under-approximates short-interval (`< P`) real-time interference by more than an order of magnitude (`33.33x` at $L = 60\,\mu\text{s}$), and failing to pair `MemGuard` with DRAM bank partitioning (`PALLOC`) amplifies that burst penalty by another $3.0\times$ via row-buffer thrashing.

---

### 3. Predictable Execution Model (`PREM`) and Compiler-Directed Phase Splitting

**Basis:** normative / documentation (`Pellizzoni et al., RTAS 2011`, DOI `10.1109/RTAS.2011.33`) + derived.

Instead of reacting to arbitrary memory traffic with hardware/software throttles, the **Predictable Execution Model (`PREM`)** restructures compiled code into a sequence of non-preemptive **Predictable Intervals**, each partitioned into two (or three, in the **Acquisition–Execution–Restitution (`AER`)** extension) strictly separated phases:

1. **Memory / Acquisition Phase (`M` / `A`)**: Software-prefetches (or DMA-transfers into local scratchpad / partitioned LLC) the *entire* code and data footprint required by the upcoming interval. Only one core (or an explicitly scheduled TDMA/priority-arbitrated set of cores) accesses main memory during its Memory Phase, completely eliminating cross-core DRAM/MSHR/bus contention.
2. **Execution Phase (`E`)**: Executes computation strictly out of local cache/scratchpad with **zero main-memory misses**. Because no request leaves the core's private cache/partition, the Execution Phase's WCET is mathematically independent of concurrent cores and equals its single-core cache-hit WCET.
3. **Write-Back / Restitution Phase (`R`, in 3-phase `AER`)**: Explicitly flushes/writes back modified cache lines to shared DRAM under arbitrated bus control, avoiding unscheduled dirty evictions during subsequent execution phases.

**Compiler and Language Invariants Required by `PREM`:**
- **Tile Size Bounded by Effective Cache Capacity**: Each predictable interval's combined code + stack + heap/data working set must fit strictly within the core's guaranteed private cache capacity $C_{\text{priv}}$ (accounting for reduced associativity if way-partitioned via `CAT`/`MPAM`).
- **Self-Eviction Freedom (No Internal Conflict Misses)**: Fitting in total bytes is insufficient on set-associative caches; if two simultaneously live arrays map to the same cache sets with degree exceeding the partition's way count $W_{\text{priv}}$, the `Execution Phase` triggers self-evictions to DRAM, breaking `PREM`'s zero-miss invariant. Compiler-directed `PREM` passes therefore require static data-layout/padding alignment or scratchpad allocation (paralleling GPU/TPU explicit DMA-to-SRAM tiling).
- **Alias & Control-Flow Precision**: Dynamic pointer chasing, unbounded recursion, heap allocation (`malloc`), and data-dependent indirect loads over structures larger than $C_{\text{priv}}$ cannot be prefetched statically; such code must execute in legacy **Compatible Intervals** (lower-assurance or non-interfering slots).
- **Non-Preemptability Across `M -> E`**: Preempting a core between its Memory Phase and Execution Phase risks evicting prefetched lines from L1/L2, requiring either non-preemptive interval scheduling or explicit re-prefetching overhead accounted for in schedulability analysis.

---

### 4. Multiprocessor Real-Time Locking Protocols (`MPCP`, `MSRP`, `OMLP`, `MrsP`)

**Basis:** normative (protocol papers: `Baker 1991`, `Rajkumar 1990`, `Gai et al. 2001`, `Brandenburg & Anderson 2010`, `Burns & Wellings 2013`, `Garrido et al. 2017`) + source (`RTEMS/rtems`, `LITMUS-RT/litmus-rt`) + execution (`probe_multicore_rt.py`).

#### 4.1 Why Uniprocessor `SRP` and `PCP` Break on Multicore
Under uniprocessor `SRP` (`Baker, Real-Time Systems 1991`, DOI `10.1007/bf00365393`), raising the system ceiling upon lock acquisition prevents any task capable of needing the lock (or lower priority) from preempting the lock holder, guaranteeing deadlock freedom and at most one critical section of priority-inversion blocking per job. On $m \ge 2$ cores, **raising a local ceiling on Core $p$ cannot prevent tasks on Core $q \neq p$ from requesting the same global resource**, nor does a local ceiling on Core $p$ prevent a *higher-priority unrelated task* $\tau_h$ on Core $p$ (whose priority strictly exceeds the resource's local ceiling on Core $p$) from preempting the lock holder—stalling all remote cores waiting on that lock (**lock-holder preemption**).

#### 4.2 Architectural & Asymptotic Comparison of Multiprocessor Locking Protocols

| Protocol | Scheduling Class | Wait Mechanism | Lock-Holder Preemption Defense | Priority-Inversion Blocking Asymptotic Bound | Nesting Support | Concrete Source Inspected |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **MPCP** (`Rajkumar 1990`, DOI `10.1109/icdcs.1990.89257`) | Partitioned FP (`P-FP`) | **Suspension** (priority-ordered queue) | Boosts global lock holder above *all* normal local priorities (`global ceiling > max normal prio`) | Multiple remote blockings per request; subject to back-to-back remote ceiling preemptions | Forbidden in `LITMUS^RT` (`-EBUSY`) | `LITMUS-RT/litmus-rt` `litmus/sched_pfp.c:685-885` |
| **MPCP-VS** (`Lakshmanan et al.` / `LITMUS^RT`) | `P-FP` | **Virtual Spinning** (per-CPU local admission token `mpcpvs_vspin` + suspension) | Same global ceiling boost + caps concurrent global waiters to 1/core | Tighter than MPCP by preventing cascading local-core remote-wait queues | Forbidden in `LITMUS^RT` | `LITMUS-RT/litmus-rt` `litmus/sched_pfp.c:706-798` |
| **DPCP** (`Rajkumar et al. 1988`, DOI `10.1109/real.1988.51121`) | `P-FP` | **Suspension + RPC/Migration** to dedicated synchronization processor | Executes all critical sections for resource $R$ on one assigned core | Eliminates cross-core cache-line bouncing; concentrates blocking on sync core | Restricted | `LITMUS-RT/litmus-rt` `litmus/sched_pfp.c:1388-1600` |
| **MSRP** (`Gai et al. 2001`, DOI `10.1109/REAL.2001.990598`) | `P-FP` / `P-EDF` | **Non-preemptive FIFO spinning** (local locks use `SRP`) | Both lock holder **and** all spinning waiters execute **non-preemptively** | $O(m)$ FIFO spin bound (`<= (m-1)` remote CSs), **but** blocks unrelated urgent local tasks by entire spin+CS duration | Local/group restrictions | Analytical + `probe_multicore_rt.py` |
| **OMLP** (`Brandenburg & Anderson 2010`, DOI `10.1109/rtss.2010.17`) | Global (`G-EDF`/`G-FP`) & Partitioned (`P-FP`/`P-EDF`) | **Suspension** (dual queue: $m$-slot FIFO queue `FQ` + priority queue `PQ` for overflow) | Priority donation / boosting on head of `FQ` | **Asymptotically optimal $\Theta(m)$** s-oblivious pi-blocking (matches $\Omega(m)$ lower bound for suspension locks!) | Group locks (`DGL` / `RNLP`) | `Brandenburg & Anderson 2010` + `Handbook 2022` (`10.1007/978-981-287-251-7_10`) |
| **MrsP** (`Burns & Wellings 2013`, DOI `10.1109/ECRTS.2013.37`) | `P-FP` (and SMP partitioned schedulers) | **Preemptable FIFO spinning + Migratory Helping** | Per-core `SRP` ceiling on owner & waiters; if owner is preempted by higher-priority local task, **waiting core migrates & executes owner's CS** | **Zero** blocking on unrelated local tasks above local ceiling; FIFO spin bounded by `(n_r - 1)` CSs (+ migration cost) | Supported via lock-order / transitive helping (`Garrido et al. 2017`) | `RTEMS/rtems` `mrsp.h`, `mrspimpl.h`, `threadqenqueue.c` |

#### 4.3 Deep Dive into `MPCP` / `MPCP-VS` (`LITMUS^RT`) and `OMLP` Dual-Queue Optimality
- **`LITMUS^RT` `MPCP` & `MPCP-VS` Source Invariants (`litmus/sched_pfp.c:685-860`)**:
  - `struct mpcp_semaphore` stores `owner`, a priority-ordered wait queue `wait`, per-CPU ceilings `prio_ceiling[NR_CPUS]`, and boolean `vspin`.
  - Lines 790–792 enforce strict non-nesting: `if (tsk_rt(t)->num_locks_held || tsk_rt(t)->num_local_locks_held) return -EBUSY;`.
  - When `sem->vspin` is enabled, `mpcp_vspin_enter()` (`lines 710-750`) acquires a per-CPU pointer `mpcpvs_vspin` (suspending competing local jobs in priority order on `mpcpvs_vspin_wait`), ensuring at most one task per core competes for global locks simultaneously.
  - Critically, line 802 calls `boost_priority(t, sem->prio_ceiling[get_partition(t)])` **before** calling `schedule()` to suspend—so that when the previous owner hands off ownership and wakes `t`, `t` resumes already at its remote ceiling priority without a preemption window.
- **`OMLP` Asymptotic Optimality (`Brandenburg & Anderson, RTSS 2010`, DOI `10.1109/rtss.2010.17`)**:
  - Naive priority-ordered suspension queues suffer $\Omega(n)$ starvation/pi-blocking (where $n \gg m$ is total task count) because higher-priority arrivals repeatedly cut ahead, whereas naive single FIFO queues also suffer $\Omega(n)$ blocking when $n$ tasks pile into the FIFO queue.
  - `OMLP` achieves optimal $O(m)$ maximum suspension-oblivious pi-blocking by splitting each resource's wait structure into a bounded **FIFO queue `FQ` of maximum length $m$** (at most one slot per processor) backed by an unbounded **priority queue `PQ`**. Jobs arriving when `|FQ| < m` enter `FQ` directly; jobs arriving when `|FQ| == m` wait in `PQ` and promote into `FQ` in priority order whenever a slot opens. A job at the head of `FQ` holds the lock (with priority inheritance/donation), bounding worst-case pi-blocking to $(2m - 1) L_{\max}$ regardless of total task count $n$.

#### 4.4 `MrsP` Formal Mechanics, `RTEMS` Source Implementation, and Migration-Cost Trap
In Burns & Wellings (`ECRTS 2013`, DOI `10.1109/ECRTS.2013.37`), each global resource $r$ shared by tasks across a set of cores $P(r)$ (with $|P(r)| = n_r$) defines a **per-processor ceiling** $\lceil r \rceil_p = \max \{\text{prio}(\tau_i) \mid \tau_i \text{ runs on core } p \text{ and uses } r\}$.
1. **Acquire & Preemptable Spin**: Upon requesting $r$ on core $p$, $\tau_i$ immediately raises its active priority to $\lceil r \rceil_p$ and appends to $r$'s global FIFO queue. While waiting, $\tau_i$ spins *preemptably* at priority $\lceil r \rceil_p$—meaning any task on core $p$ with priority $> \lceil r \rceil_p$ can preempt $\tau_i$ immediately with **zero** spin blocking.
2. **Migratory Helping**: If the current owner $\tau_o$ on core $p_o$ is preempted by a local task with priority $> \lceil r \rceil_{p_o}$, any core $p_w$ whose top-running task is a FIFO waiter for $r$ **lends its processor** to execute $\tau_o$'s critical section (temporarily migrating $\tau_o$ to $p_w$ at ceiling $\lceil r \rceil_{p_w}$). Thus, as long as *any* competing core has no higher-priority local work than its ceiling for $r$, the critical section makes forward progress.
3. **Burns–Wellings Response-Time Analysis Recurrence**: Treating spinning and helping time as execution inflation rather than suspension, the worst-case access cost $\hat{e}_i(r)$ of a single access to $r$ (with maximum critical section length $e(r)$ across cores, ignoring migration overhead) is bounded by $\hat{e}_i(r) = |P(r)| \cdot e(r)$, yielding the partitioned fixed-priority response-time fixed point:
   $$R_i = C_i^{\text{ext}} + B_i + \sum_{j \in hp(i)} \left\lceil \frac{R_i}{T_j} \right\rceil C_j^{\text{ext}}$$
   where $C_k^{\text{ext}}$ inflates every global resource access of $\tau_k$ from $e(r)$ to $\hat{e}_k(r)$ (including FIFO waiting delay from up to $n_r - 1$ remote cores), and $B_i$ is the standard local `SRP` blocking from at most one lower-priority local task whose access to a resource $r'$ satisfies $\lceil r' \rceil_p \ge \text{prio}(\tau_i)$ (also inflated to $\hat{e}(r')$).
4. **Nested Resources in `MrsP` (`Garrido, Zhao, Burns, Wellings, Ada-Europe 2017`, DOI `10.1007/978-3-319-60588-3_5`)**: When a task holding outer lock $r_1$ requests inner lock $r_2$, simple single-resource helping can stall or create transitive migration chains across disjoint core sets $P(r_1) \neq P(r_2)$. Nested `MrsP` requires strict partial-order resource acquisition (for deadlock freedom), ceiling elevation to $\max(\lceil r_1 \rceil_p, \lceil r_2 \rceil_p)$, and **transitive helping** (waiters on $r_1$ may help the holder of $r_2$ that is blocking $r_1$'s owner) or group locking.
5. **Production Implementation in `RTEMS` (`RTEMS/rtems @ 17bb6e147c83309ce3bbf43e4f77600a4c64ea0b`)**:
   Direct source inspection of `cpukit/include/rtems/score/mrsp.h`, `cpukit/include/rtems/score/mrspimpl.h`, and `cpukit/score/src/threadqenqueue.c` reveals exact OS-level invariants:
   - `MRSP_Control` (`mrsp.h:77-92`) stores `Thread_queue_Control Wait_queue`, `Priority_Node Ceiling_priority`, and a flexible array `Priority_Control ceiling_priorities[]` indexed by scheduler instance (initialized in `_MRSP_Initialize`, `mrspimpl.h:300-329`).
   - `_MRSP_Claim_ownership()` (`mrspimpl.h:257-284`) raises the thread's priority to the local ceiling (`_MRSP_Raise_priority`, returning `STATUS_MUTEX_CEILING_VIOLATED` if the caller's base priority exceeds the ceiling), sets ownership, and calls `_Thread_Priority_update_and_make_sticky(executing)` so the SMP scheduler keeps the owner eligible for remote helping if preempted.
   - `_MRSP_Wait_for_ownership()` (`mrspimpl.h:363-417`) first raises the waiter to its local ceiling, then invokes `_Thread_queue_Enqueue_sticky()` (`threadqenqueue.c:496-570`). Crucially, `_Thread_queue_Enqueue_sticky()` runs deadlock detection along the wait-for graph (`_Thread_queue_Path_acquire`, lines 511–527), asserts `cpu_self->thread_dispatch_disable_level == 1` (`lines 544-548`, aborting with `INTERNAL_ERROR_THREAD_QUEUE_ENQUEUE_STICKY_FROM_BAD_STATE` if called with preemption disabled!), calls `_Thread_Priority_update_and_make_sticky(the_thread)` + `_Thread_Dispatch_enable(cpu_self)` (`lines 558-559`), and **then** busy-spins (`while (_Thread_Wait_flags_get_acquire(the_thread) != wait_flags) {}`, lines 563–565) with preemption enabled!
   - On handoff, `_Thread_queue_Surrender_sticky()` (`threadqenqueue.c:877-885`) updates `queue->owner = new_owner` and flips `new_owner`'s wait flags directly without scheduler unblocking because the waiter remained runnable/sticky.
6. **Discrete-Event Protocol Verification & Migration Ping-Pong Trade-Off (`Basis: execution`)**:
   Running `/tmp/probe_multicore_rt.py` (Part 1) on a 3-core scenario—Core 0: `T_high0` (prio 10, no lock, $r=2, C=4$), `T_low0` (prio 1, lock $R$, $r=0, C_{\text{pre}}=1, e=5, C_{\text{post}}=1$); Core 1: `T_urg1` (prio 10, no lock, $r=3, C=2$), `T_med1` (prio 4, lock $R$, $r=2, e=4, C_{\text{post}}=1$); Core 2: `T_med2` (prio 3, lock $R$, $r=2, e=4, C_{\text{post}}=1$)—produced:

| Protocol | `T_high0` (Core 0, urgent, no lock) `R / delay` | `T_urg1` (Core 1, urgent, no lock) `R / delay` | `T_low0` (Core 0, lock holder) `R / helped / migs` | `T_med1` (Core 1, waiter 1) `R / spin` | `T_med2` (Core 2, waiter 2) `R / spin` |
| :--- | :---: | :---: | :---: | :---: | :---: |
| **Naive Spinlock** | `4 / 0` | `2 / 0` | `11 / 0 / 0` | `13 / 6` | `17 / 12` |
| **MSRP** (non-preemptive spin) | **`8 / +4`** (blocked!) | **`9 / +7`** (blocked!) | `11 / 0 / 0` | `11 / 4` | `13 / 8` |
| **MrsP (`mig_cost = 0`)** | **`4 / 0`** | **`2 / 0`** | **`7 / 4 / 3`** | **`9 / 2`** | **`13 / 8`** |
| **MrsP (`mig_cost = 1`)** | **`4 / 0`** | **`2 / 0`** | `11 / 4 / 4` | `13 / 6` | `17 / 12` |

   **Key empirical insight**: `MrsP` simultaneously protects urgent unrelated tasks (`T_high0`, `T_urg1`: `0` blocking vs `+4`/`+7` under `MSRP`) and bounds FIFO spinning (`T_med2` spin `8 <= (m-1)*e_max = 10`). However, with `mig_cost = 1` tick per core transfer, `T_low0` bounces **4 times** (`Core 0 -> Core 1 -> Core 2 -> Core 1 -> Core 0`) as preemptions start and finish, accumulating `4` ticks of migration overhead that completely cancels helping's latency advantage for `T_med1`/`T_med2`! Production `MrsP` runtimes must therefore account explicitly for per-migration cache-affinity and IPI cost in $e(r)$ and prefer *non-eager return* (allowing a helped owner to finish its critical section on the helper core rather than immediately bouncing back when its home core becomes free).

---

### 5. `Prosa` Mechanized Real-Time Schedulability Analysis

**Basis:** normative (peer-reviewed proofs: `ECRTS 2016`, `ECRTS 2020`, `ECRTS 2022`, `RTSS 2022`, `PLDI 2025`) + source (`rocq-prover/opam` `rocq-prosa.0.6`).

Paper-and-pencil real-time schedulability proofs have a documented history of subtle edge-case errors (off-by-one busy-window boundaries, hidden self-suspension interactions, invalid critical-instant assumptions on multiprocessors). **Prosa** (`gitlab.mpi-sws.org/RT-PROOFS/rt-proofs`, released in OPAM as `rocq-prosa.0.6` for `rocq-core >= 9.0` with `coq-mathcomp-algebra` and `coq-mathcomp-zify`; previously `coq-prosa.0.5` for Coq `8.13–8.16`) establishes a readable, modular mechanized library for real-time timing proofs:

1. **Layered Trace Architecture (`Cerqueira, Stutz, Brandenburg, ECRTS 2016`, DOI `10.1109/ECRTS.2016.28`)**:
   - Decouples *abstract discrete-time schedules* (`schedule : instant -> processor_state`), *arrival sequences*, *task/job parameters* (WCET, arrival curves, deadlines), *scheduler semantics* (work-conserving, FP, EDF, FIFO, non-preemptive regions), and *analysis theorems*.
   - Prioritizes human readability of definitions (`prosa.model.*`) so domain experts can audit specifications without reading proof scripts (`prosa.analysis.*`), mitigating specification-validation risk in certification (`DO-178C` / `AMC 20-193`).
2. **Abstract Response-Time Analysis (`aRTA`, `Bozhko & Brandenburg, ECRTS 2020`, DOI `10.4230/LIPIcs.ECRTS.2020.22`)**:
   - Unifies uniprocessor and restricted-supply response-time proofs under one parameterized busy-window theorem. Instead of re-proving the busy-window principle for every scheduling policy, priority-inversion protocol, or supply interruption (such as `MemGuard` throttling or `PREM` memory phases!), an analyst instantiates two abstract predicates:
     - **Interference Bound Function (`IBF`)**: Upper-bounds cumulative interfering work (higher-priority preemptions, non-preemptive blocking, lock spin/helping delay, hardware bus interference) over any busy interval of length $\Delta$.
     - **Supply Bound Function (`SBF`)**: Lower-bounds guaranteed processor service over any interval of length $\Delta$ (capturing periodic servers, TDMA slots, or virtualization budgets).
   - Once `IBF` and `SBF` satisfy the abstract soundness conditions, `Prosa` automatically yields a kernel-checked theorem certifying that the fixed-point solution $R$ of the search-space inequality is a sound worst-case response time bound.
3. **Explainable Certification Evidence & Multiprocessor / Locking Coverage (`Maida et al., ECRTS 2022`, DOI `10.4230/LIPIcs.ECRTS.2022.19`; `Bedarkar et al., RTSS 2022`, DOI `10.1109/RTSS55097.2022.00026`)**:
   - `Maida et al.` generate independently checkable response-time certificates (`POET` / foundational RTA) backed by `Prosa`'s Coq/Rocq proofs, turning schedulability tests into machine-checked evidence rather than trusting unverified C++/Python analysis tools.
   - `Prosa` includes formal models for ideal uniprocessor and multiprocessor states (`ideal_multiprocessor`), global scheduling (`G-EDF`, `G-FP` response-time bounds / RTA for global scheduling), restricted-supply processors, non-preemptive sections, FIFO scheduling (`RTSS 2022`), and lock-induced priority-inversion blocking abstractions.
4. **Bridging to Verified C Scheduler Implementations (`RefinedProsa`, `Bedarkar et al., PLDI 2025`, DOI `10.1145/3729249`)**:
   - Connects `Prosa`'s abstract timing schedules to `RefinedC` / `Iris` separation-logic verification of actual C scheduler code (for interrupt-free uniprocessor schedulers), proving that the compiled C dispatch loop refines the `Prosa` abstract schedule trace so timing theorems transfer down to code rather than stopping at an unlinked mathematical model.

## Boundaries

- **Not examined — Direct source tree of `rt-proofs-v0.6.tar.gz` internals**: Because outbound direct HTTP access to `gitlab.mpi-sws.org` was unavailable in the observation environment, `Prosa`'s exact Coq/Rocq module-level proof files inside `v0.6` were not directly inspected line-by-line; release metadata, dependencies, archive URL, and `SHA-512` checksum were directly verified from `rocq-prover/opam` (`06733fd8dcbd7ca2e61bc38c72d6062a52f20d57`), and architectural theorems (`aRTA`, foundational RTA, `RefinedProsa`) are grounded in the cited peer-reviewed papers.
- **Not examined — Full `MrsP` migratory helping mechanization inside `Prosa` / `RefinedProsa`**: Whether `rocq-prosa v0.6` contains a complete mechanized proof of Burns–Wellings `MrsP` with nested transitive helping and concrete migration costs (as opposed to abstract spin/blocking `IBF` instantiations) was not verified directly from the `.v` source tree (`unknown` without inspecting `rt-proofs-v0.6.tar.gz`). `RefinedProsa` (`PLDI 2025`) is explicitly scoped to *interrupt-free uniprocessor* C schedulers (`known not to apply` to SMP migratory-helping kernels like `RTEMS` without further extension).
- **Known not to apply — Single-layer hardware partitioning as a complete `CAST-32A`/`A(M)C 20-193` mitigation**: `Intel CAT` and `Arm MPAM CPOR` alone **do not** bound MSHR exhaustion, LLC write-back buffer saturation, snoop-filter/directory evictions, or DRAM bank row-buffer conflicts; citing way partitioning alone as sufficient interference mitigation is unsound on COTS multicore hardware.
- **Known not to apply — `Intel MBA` hardware percentages as linear bandwidth reservations**: Per `torvalds/linux` `resctrl.rst:908-936`, hardware `MBA` percentages apply at the per-core L2-to-interconnect boundary and do not translate linearly to package DRAM bandwidth across varying thread counts; real-time bounds require empirical stress calibration (`MCP_Resource_Usage_4`) or bounded periodic/hardware caps verified at the DRAM controller.
- **Unsupported — Nested global locks in `LITMUS^RT` `MPCP` (`litmus/sched_pfp.c:790-792`)**: Attempting nested `MPCP` acquisition explicitly fails with `-EBUSY`. Similarly, `RTEMS` `_Thread_queue_Enqueue_sticky()` (`threadqenqueue.c:544-548`) does not support acquiring an `MrsP` mutex while thread dispatching is already disabled (`thread_dispatch_disable_level != 1`).
- **Unknown — Tightness of `PREM` compiler auto-partitioning on arbitrary pointer-rich Rust/C++ workloads**: While `PREM` is proven effective on statically analyzable array/control-loop kernels, automatic transformation of general dynamic-allocation or trait-object/pointer-chasing code into conflict-free predictable intervals without manual programmer restructuring remains an open research problem.

## Evidence

### Upstream Repository Source Citations (Pinned Revisions)
- **`heechul/memguard` @ `613be205f6b2351743866852f631e664d8e4ace4`**:
  - `memguard.c:163-173` — `g_period_us = 1000`, `g_read_counter_id` (`PMU_LLC_MISS_COUNTER_ID`), `g_write_counter_id` (`PMU_LLC_WB_COUNTER_ID`), `g_use_reclaim`, `g_use_exclusive`.
  - `memguard.c:376-398` — `event_overflow_callback`, `event_write_overflow_callback` queuing `irq_work` from hardirq/NMI context.
  - `memguard.c:436-580` — `memguard_read_process_overflow` / `memguard_write_process_overflow`: local & global slack reclaim (`g_qmin`), exclusive modes (`2` = SP, `5` = PS), and `wake_up_interruptible(&cinfo->throttle_evt)`.
- **`heechul/palloc` @ `d470088a1eb21b0dca99f475404225222c956732`**:
  - `palloc_xormap-6.14.patch` (patching `include/linux/palloc.h`, `mm/mm_init.c`, `mm/page_alloc.c`) — `sysctl_palloc_masks[MAX_PALLOC_BITS]` XOR bank-bit mapping, per-zone `color_list[c]` and `color_bitmap`, `CONFIG_CGROUP_PALLOC`.
  - `mc-mapping.c`, `detect-mc-mapping-xor.sh` — empirical DRAM bank XOR-mapping discovery tools.
- **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`**:
  - `Documentation/filesystems/resctrl.rst:22-26, 851-948` — `CAT`/`CDP`/`MBM`/`MBA`, contiguous `CBM` constraint (`sparse_masks`), SNC per-bit capacity division, `MBA` per-core vs package L3 saturation anomalies, `thread_throttle_mode`, and `mba_sc` (`mba_MBps`).
  - `Documentation/filesystems/resctrl.rst:993-1160` — AMD `SMBA` (CXL.memory) and `Cache Pseudo-Locking` procedure, `INVD`/`WBINVD`/`CLFLUSH` & C-state eviction caveats, and one-time `mmap()` core-affinity check.
  - `drivers/resctrl/mpam_devices.c:444-454, 846-1060, 1510-1970` — `MPAMCFG_PART_SEL_RIS`/`INTERNAL`, `mpam_quirks[]` (`T241-MPAM-1/4/6`, `CMN-650` erratum `3642720`), `IHI009A.a` `NRDY` probe (`mpam_ris_hw_probe_csu_nrdy`), `mpam_ris_hw_probe()` (`CCAP`, `CPOR`, `MBW`, `PRI`), `T241_MBW_COUNTER_SCALE_64` (`now *= 64` at L1565), `mpam_reprogram_ris_partid()`.
- **`intel/intel-cmt-cat` @ `ac1a9f606eeadb447b7706d17d9fa76fa89a279b`**:
  - `lib/allocation.c:91-100, 390-484, 976-1268, 1297-1610` — `PQOS_MSR_ASSOC`, `PQOS_MSR_L3CA_MASK_START`, `PQOS_MSR_L2CA_MASK_START`, `PQOS_MSR_MBA_MASK_START`, `PQOS_MSR_SMBA_MASK_START_AMD`, `PQOS_MSR_L3_QOS_CFG_CDP_EN`, `PQOS_MSR_L3_IO_QOS_CFG`.
- **`ARM-software/arm-trusted-firmware` @ `0d2c4394f010bc91327ee1ee923bf6d70d446bb7`**:
  - `lib/extensions/mpam/mpam.c:14-91` — `mpam_enable_per_world()` (`MPAM3_EL3_MPAMEN_BIT`), `mpam_init_el3()` & `mpam_init_el2_unused()` (`FEAT_MPAM_PE_BW_CTRL` registers `MPAMBW{0,1,2,3}_EL*`, `HARDLIM`, `HW_SCALE_ENABLE`).
- **`bao-project/bao-hypervisor` @ `c3907240d0eca92a338b20f0c43ecbf3f9cd60bd`**:
  - `src/core/mem.c:59-177` — `pp_alloc()`, `mem_alloc_page()` calling `mem_alloc_ppages(cpu()->as.colors, num_pages, phys_aligned)`.
- **`RTEMS/rtems` @ `17bb6e147c83309ce3bbf43e4f77600a4c64ea0b`**:
  - `cpukit/include/rtems/score/mrsp.h:77-92` — `MRSP_Control` (`Wait_queue`, `Ceiling_priority`, `ceiling_priorities[]`).
  - `cpukit/include/rtems/score/mrspimpl.h:257-468` — `_MRSP_Claim_ownership`, `_MRSP_Initialize`, `_MRSP_Wait_for_ownership`, `_MRSP_Seize`.
  - `cpukit/score/src/threadqenqueue.c:496-570, 876-886` — `_Thread_queue_Enqueue_sticky` (deadlock detection, `thread_dispatch_disable_level == 1` invariant, sticky priority update, preemptable spin loop) and `_Thread_queue_Surrender_sticky`.
- **`LITMUS-RT/litmus-rt` @ `7811e5b1eaef361f45659a1f6d49acb050b1f316`**:
  - `litmus/sched_pfp.c:511-680` (`FMLP`), `685-860` (`MPCP` & `MPCP-VS`: `mpcp_vspin_enter/exit`, `-EBUSY` anti-nesting guard L790–792, pre-suspend `boost_priority` L802), `977-1380` (`PCP`), `1388-1600` (`DPCP`), `1609-1680` (`DFLP`).
- **`rocq-prover/opam` @ `06733fd8dcbd7ca2e61bc38c72d6062a52f20d57`**:
  - `released/packages/rocq-prosa/rocq-prosa.0.6/opam` — `rt-proofs-v0.6.tar.gz`, `sha512=128dd213e687653a6ad5a55f33e76d39f4301f4fb22ff2c58379bb9d727ada00da776beee213e89b6be117f4db7c7bd73e467e28f57dfbee017891a4121e6228`, depends on `rocq-core >= 9.0 & < 9.1~`, `coq-mathcomp-algebra >= 2.4 & < 2.5~`, `coq-mathcomp-zify >= 1.5.0`.
  - `released/packages/coq-prosa/coq-prosa.0.5/opam` — `rt-proofs-v0.5.tar.gz`, `sha256=49b246784fb32137079c3aebbade1dc648d7a7cc705bdc91789ee3e144ea8279`.

### Verified Peer-Reviewed Literature & Standards
- Baker, T. P. (1991). *Stack-based scheduling of realtime processes*. Real-Time Systems, DOI `10.1007/bf00365393`.
- Rajkumar, R., Sha, L., & Lehoczky, J. P. (1988). *Real-time synchronization protocols for multiprocessors*. IEEE RTSS, DOI `10.1109/real.1988.51121`.
- Rajkumar, R. (1990). *Real-time synchronization protocols for shared memory multiprocessors*. IEEE ICDCS, DOI `10.1109/icdcs.1990.89257`.
- Gai, P., Lipari, G., & Di Natale, M. (2001). *Minimizing memory utilization of real-time task sets in single and multi-processor systems-on-a-chip*. IEEE RTSS, pp. 73–83, DOI `10.1109/REAL.2001.990598`.
- Brandenburg, B. B., & Anderson, J. H. (2010). *Optimality Results for Multiprocessor Real-Time Locking*. IEEE RTSS, DOI `10.1109/rtss.2010.17`; Brandenburg, B. B. (2022). *Multiprocessor Real-Time Locking Protocols*, Handbook of Real-Time Computing, DOI `10.1007/978-981-287-251-7_10`.
- Pellizzoni, R., Betti, E., Bak, S., Yao, G., Criswell, J., Caccamo, M., & Kegley, R. (2011). *A Predictable Execution Model for COTS-Based Embedded Systems*. IEEE RTAS, pp. 269–279, DOI `10.1109/RTAS.2011.33`.
- Yun, H., Yao, G., Pellizzoni, R., Caccamo, M., & Sha, L. (2013). *MemGuard: Memory bandwidth reservation system for efficient performance isolation in multi-core platforms*. IEEE RTAS, pp. 55–64, DOI `10.1109/RTAS.2013.6531079`.
- Burns, A., & Wellings, A. J. (2013). *A Schedulability Compatible Multiprocessor Resource Sharing Protocol — MrsP*. ECRTS, pp. 282–291, DOI `10.1109/ECRTS.2013.37`.
- Kim, H., de Niz, D., Andersson, B., Klein, M., Mutlu, O., & Rajkumar, R. (2014). *Bounding memory interference delay in COTS-based multi-core systems*. IEEE RTAS, pp. 145–154, DOI `10.1109/RTAS.2014.6925998`.
- Yun, H., Mancuso, R., Wu, Z.-P., & Pellizzoni, R. (2014). *PALLOC: DRAM bank-aware memory allocator for performance isolation on multicore platforms*. IEEE RTAS, pp. 155–166, DOI `10.1109/RTAS.2014.6925999`.
- Valsan, P. K., Yun, H., & Farshchi, F. (2016). *Taming Non-Blocking Caches to Improve Isolation in Multicore Real-Time Systems*. IEEE RTAS, pp. 1–12, DOI `10.1109/RTAS.2016.7461361`.
- Cerqueira, F., Stutz, F., & Brandenburg, B. B. (2016). *PROSA: A Case for Readable Mechanized Schedulability Analysis*. ECRTS, pp. 273–284, DOI `10.1109/ECRTS.2016.28`.
- Garrido, J., Zhao, S., Burns, A., & Wellings, A. (2017). *Supporting Nested Resources in MrsP*. Ada-Europe (LNCS), pp. 73–86, DOI `10.1007/978-3-319-60588-3_5`.
- Bechtel, M., & Yun, H. (2019). *Denial-of-Service Attacks on Shared Cache in Multicore: Analysis and Prevention*. IEEE RTAS, pp. 357–367, DOI `10.1109/RTAS.2019.00037`.
- Bozhko, S., & Brandenburg, B. B. (2020). *Abstract Response-Time Analysis: A Formal Foundation for the Busy-Window Principle*. ECRTS (LIPIcs), DOI `10.4230/LIPIcs.ECRTS.2020.22`.
- Maida, M., Bozhko, S., & Brandenburg, B. B. (2022). *Foundational Response-Time Analysis as Explainable Evidence of Timeliness*. ECRTS (LIPIcs), DOI `10.4230/LIPIcs.ECRTS.2022.19`.
- Bedarkar, K., Vardishvili, M., Bozhko, S., Maida, M., & Brandenburg, B. B. (2022). *From Intuition to Coq: A Case Study in Verified Response-Time Analysis of FIFO Scheduling*. IEEE RTSS, pp. 197–210, DOI `10.1109/RTSS55097.2022.00026`.
- Bedarkar, K., Elbeheiry, L., Sammler, M., Gäher, L., Brandenburg, B., Dreyer, D., & Garg, D. (2025). *RefinedProsa: Connecting Response-Time Analysis with C Verification for Interrupt-Free Schedulers*. PLDI (PACMPL), pp. 73–97, DOI `10.1145/3729249`.

### Self-Contained Executable Micro-Probe (`Python 3.13.15`, Linux x86-64, observed 2026-11-19)
Save as `/tmp/probe_multicore_rt.py` and run `python3 /tmp/probe_multicore_rt.py`:

```python
from dataclasses import dataclass

@dataclass
class TaskSpec:
    name: str; core: int; prio: int; release: int
    c_pre: int; c_cs: int; c_post: int; uses_r: bool

TASKS = [
    TaskSpec("T_high0", 0, 10, 2, 4, 0, 0, False),
    TaskSpec("T_low0",  0,  1, 0, 1, 5, 1, True),
    TaskSpec("T_urg1",  1, 10, 3, 2, 0, 0, False),
    TaskSpec("T_med1",  1,  4, 2, 0, 4, 1, True),
    TaskSpec("T_med2",  2,  3, 2, 0, 4, 1, True),
]

def simulate(protocol: str, mig_cost: int = 0):
    state = {t.name: {"spec": t, "rem_pre": t.c_pre, "rem_cs": t.c_cs, "rem_post": t.c_post,
                      "phase": "not_released", "finish": None, "spin": 0, "helped": 0,
                      "migs": 0, "exec_core": t.core} for t in TASKS}
    ceilings = {c: max((t.prio for t in TASKS if t.core == c and t.uses_r), default=0) for c in range(3)}
    owner, fifo, mig_pen = None, [], 0
    for tick in range(60):
        for st in state.values():
            if st["phase"] == "not_released" and tick == st["spec"].release:
                st["phase"] = "pre" if st["rem_pre"] > 0 else ("req" if st["spec"].uses_r else "done")
        for st in sorted(state.values(), key=lambda s: (s["spec"].core, -s["spec"].prio)):
            if st["phase"] == "req":
                if owner is None:
                    owner, st["phase"], st["exec_core"] = st["spec"].name, "cs", st["spec"].core
                else:
                    st["phase"] = "waiting"
                    if st["spec"].name not in fifo: fifo.append(st["spec"].name)
        def eff_prio(st):
            if protocol == "msrp" and st["phase"] in ("cs", "waiting"): return 1000
            if protocol == "mrsp" and st["phase"] in ("cs", "waiting"): return max(st["spec"].prio, ceilings[st["spec"].core])
            return st["spec"].prio
        chosen = {}
        for c in range(3):
            cands = [s for s in state.values() if s["spec"].core == c and s["phase"] in ("pre","waiting","cs","post")]
            chosen[c] = sorted(cands, key=lambda s: (-eff_prio(s), s["spec"].release))[0] if cands else None
        ost = state[owner] if owner else None
        run_c = None
        if ost:
            if chosen[ost["spec"].core] is ost: run_c = ost["spec"].core
            elif protocol == "mrsp":
                for w in fifo:
                    if chosen[state[w]["spec"].core] is state[w]: run_c = state[w]["spec"].core; break
            if run_c is not None and run_c != ost["exec_core"]:
                ost["migs"] += 1; ost["exec_core"] = run_c; mig_pen = mig_cost
        for c, st in chosen.items():
            if not st: continue
            if st["phase"] == "pre":
                st["rem_pre"] -= 1
                if st["rem_pre"] == 0:
                    st["phase"] = "req" if st["spec"].uses_r else "done"
                    if st["phase"] == "done": st["finish"] = tick + 1
            elif st["phase"] == "post":
                st["rem_post"] -= 1
                if st["rem_post"] == 0: st["phase"], st["finish"] = "done", tick + 1
            elif st["phase"] == "cs" and run_c == c:
                if mig_pen > 0: mig_pen -= 1
                else: st["rem_cs"] -= 1
            elif st["phase"] == "waiting":
                st["spin"] += 1
                if protocol == "mrsp" and run_c == c and ost:
                    ost["helped"] += 1
                    if mig_pen > 0: mig_pen -= 1
                    else: ost["rem_cs"] -= 1
        if ost and ost["rem_cs"] == 0:
            ost["phase"] = "post" if ost["rem_post"] > 0 else "done"
            if ost["phase"] == "done": ost["finish"] = tick + 1
            if fifo:
                owner = fifo.pop(0); state[owner]["phase"] = "cs"
                state[owner]["exec_core"] = state[owner]["spec"].core; mig_pen = 0
            else: owner = None
        if all(s["phase"] == "done" for s in state.values()): break
    return {k: (v["finish"] - v["spec"].release, v["spin"], v["helped"], v["migs"]) for k, v in state.items()}

def max_periodic_supply(L, Q, P, t_burst):
    t0, t1, rate = P - t_burst, P - t_burst + L, Q / t_burst
    tot = max(0.0, min(t1, P) - max(t0, P - t_burst)) * rate
    k = 1
    while k * P < t1:
        tot += max(0.0, min(t1, k * P + t_burst) - max(t0, k * P)) * rate
        k += 1
    return tot

for proto, mc in [("naive_spin",0), ("msrp",0), ("mrsp",0), ("mrsp",1)]:
    print(proto, mc, simulate(proto, mc))
for L in [30.0, 60.0, 200.0, 1000.0, 1060.0, 2000.0]:
    tx = max_periodic_supply(L, 2000.0, 1000.0, 30.0)
    print(f"L={L} worst_tx={tx:.0f} stall_priv={3*tx*0.015:.1f}us stall_shared={3*tx*0.045:.1f}us")
```

## Revalidation

1. **Re-run the Locking and Burstiness Probe**: Execute the embedded Python script above; verify that `msrp` delays `T_urg1` to `R=9`, `mrsp (mig_cost=0)` achieves `T_urg1 R=2, T_med1 R=9`, `mrsp (mig_cost=1)` matches `naive_spin` on `T_med2 (R=17)` due to `4` migrations while keeping `T_urg1 R=2`, and `max_periodic_supply(60, 2000, 1000, 30)` yields `4000` transactions (`540.0 us` 3-core shared-bank stall).
2. **Diff Mainline Linux `resctrl` / `Arm MPAM` Evolution**: Compare `torvalds/linux` `drivers/resctrl/mpam_devices.c` (especially `mpam_quirks[]` and `mpam_ris_hw_probe()`) and `Documentation/filesystems/resctrl.rst` against revision `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` to check for newly discovered `MSC` silicon errata, mainline `MPAM` `resctrl` exposure, or changes to `mba_sc`/`SMBA`/pseudo-locking invariants.
3. **Check `RTEMS` `MrsP` and `Prosa` Releases**:
   - Inspect `RTEMS/rtems` `cpukit/include/rtems/score/mrspimpl.h` and `cpukit/score/src/threadqenqueue.c` (`_Thread_queue_Enqueue_sticky`) against `17bb6e147c83309ce3bbf43e4f77600a4c64ea0b` for changes to sticky helping or nested lock rules.
   - Check `rocq-prover/opam` `released/packages/rocq-prosa/` against `06733fd8dcbd7ca2e61bc38c72d6062a52f20d57` for newer `Prosa` releases (`> v0.6`), and inspect `rt-proofs` directly when GitLab access is available to audit concrete multicore locking `.v` modules.
4. **Hardware Validation on a New Target SoC**: Before relying on `CAT`/`MPAM`/`MemGuard`/`PALLOC` for `CAST-32A`/`A(M)C 20-193` compliance, execute an empirical interference matrix running: (a) read-heavy MLP MSHR stress (`Valsan 2016`), (b) dirty-store write-back stress (`Bechtel & Yun 2019`), and (c) `palloc/mc-mapping.c` DRAM bank-XOR conflict probing concurrently with a cache-resident victim loop to verify whether residual hardware queues leak past the configured partitions.
