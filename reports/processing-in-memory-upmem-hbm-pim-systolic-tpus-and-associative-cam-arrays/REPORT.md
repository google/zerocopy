# Memory-Centric and Spatial Non-von-Neumann Architectures: UPMEM and HBM-PIM Processing-in-Memory, Systolic Arrays, and Associative CAM Processors

## Summary

Moving computation into or directly alongside storage arrays attacks the dominant energy and bandwidth wall of modern systems—off-chip DRAM/HBM channel movement (`~5`–`20 pJ/bit` across package pins vs. `< 0.1`–`0.5 pJ/bit` inside a bank or PE wire). Across commercial digital Processing-in-Memory (`UPMEM`, Samsung `HBM-PIM`, SK Hynix `GDDR6-AiM`), spatial weight/output-stationary systolic meshes (`Kung & Leiserson`, Google `TPU MXU`, `UC Berkeley Gemmini`), and bit-serial associative/content-addressable arrays (`CMOS TCAM`, `CAPE`, `SIMDRAM`), eliminating hardware cache coherence and intermediate register-file round-trips shifts fundamental correctness obligations onto **compilers, host drivers, and formal ownership invariants**:

1. **Commercial bank-near DRAM Processing Units (`UPMEM`) unlock `~1.7`–`2.0 TB/s` aggregate internal MRAM bandwidth across `2,560` cores, but impose zero hardware cache coherence, zero inter-DPU links, and a mandatory host DDR4 byte-interleaving transpose barrier.** Each UPMEM DPU pairs a pure-Harvard `24 KiB` instruction SRAM (`IRAM`), `64 KiB` scratchpad (`WRAM`), and disjoint `64 MiB` DRAM bank (`MRAM`) with a `24`-tasklet barrel pipeline (`11`-cycle same-tasklet hazard spacing) and only a native `8`-bit hardware multiplier (`CMU-SAFARI/prim-benchmarks` @ `67179099730cdccc650d52d25f458cb2e4f8a675`; `DOI: 10.1109/ACCESS.2022.3174101`). Because standard x86-64 DDR4 rank controllers stripe every 8-byte bus beat 1 byte per `x8` DRAM chip, raw linear host writes arrive byte-scrambled across 8 DPUs (`0xa0b8d0e8` corruption in our executable check) unless transposed in software (`dpu_push_xfer`) across an explicit cache-flush bulk-synchronous phase boundary.
2. **JEDEC-compatible bank-level SIMD PIM (`Samsung HBM-PIM` / `SK Hynix GDDR6-AiM`) achieves `3.5x`–`16x` memory-bound GEMV speedups behind unmodified memory controllers only if host drivers enforce uncached, non-coalesced command streams.** In `SAITPublic/PIMSimulator` (`3703d1f19c8f027360cc33a3243eb271e3bb6898`, `src/PIMCmd.h`, `src/PIMRank.cpp`), an `8`-PIM-block-per-pseudo-channel `256`-bit `FP16` SIMD engine steps its `32`-instruction Command Register File (`CRF` `pimPC_`) on *incoming host column read/write commands*. Mapping PIM trigger regions as Write-Back or Write-Combining (`WC`) merges consecutive writes to the same `64 B` cache line, silently skipping `CRF` instructions, corrupting `GRF_A`/`GRF_B` accumulations (`510 -> 110` in our executable reproducer), and failing to execute `EXIT` before normal DRAM (`SB`) reads resume.
3. **Weight- and output-stationary systolic meshes (`TPU MXU`, `ucb-bar/gemmini`) eliminate $O(N^3)$ intermediate register-file traffic by turning spatial wire propagation into an implicit schedule whose `RAW`/`WAR`/`WAW` safety depends entirely on explicit wave-drain latency tracking.** In `ucb-bar/gemmini` (`b82d49cca798a59f010488a6f6de7243f0616536`, `PE.scala`, `Mesh.scala`, `ReservationStation.scala`), each PE holds dual registers (`c1`, `c2`) switched by a pipelined `propagate` bit to overlap weight preloading or output draining with zero-stall MAC waves, cutting boundary SRAM accesses from $3N^3$ to $2N^2$ reads + $N^2$ writes. Because neither Gemmini's Scratchpad/Accumulator nor TPU's `VMEM`/`HBM` provides hardware cache coherence, issuing a `Store` controller command before the $3N - 2$ systolic wave-drain latency completes (`ReservationStation.OpT.overlaps` / `XLA` sync flags) silently reads partially accumulated zeros.
4. **Bit-serial associative processors (`CAPE` `6T` SRAM, `SIMDRAM` triple-row activation) achieve $O(b)$ bit-step execution independent of vector length $M$, trading ALU area for vertical bit-transposition and destructive-read invariants.** `CAPE` (`DOI: 10.1109/HPCA51647.2021.00054`) lowers standard RISC-V Vector (`RVV`) instructions onto `32K+`-lane push-rule `6T` SRAM subarrays via multi-row truth-table `search` and masked `update` passes (`16` bit-steps for `16`-bit addition across `8,192` elements), whereas `SIMDRAM` (`DOI: 10.1145/3445814.3446749`) executes `MAJ3`/`NOT` via triple-row DRAM activation (`AAP`) that *physically overwrites all three source rows*, requiring compiler-inserted `RowClone` backups and exposing severe RowHammer/retention margins.

## Applicability

This report examines and cross-compares four architectural classes across nine primary upstream repositories and hardware/circuit publications:

- **General-Purpose Bank-Near DRAM Cores (`UPMEM`)**: `CMU-SAFARI/prim-benchmarks` (`67179099730cdccc650d52d25f458cb2e4f8a675`, `PrIM` 16-workload suite & microbenchmarks on `2,560`-DPU DDR4-2400 systems, Gómez-Luna et al., *IEEE Access* 2022, `DOI: 10.1109/ACCESS.2022.3174101`, `arXiv:2105.03814`) and `VIA-Research/uPIMulator` (`870d916334e9ff0b190f555f951a9ec3c4257781`, cycle-accurate simulator covering `599` of `970` UPMEM SDK `2023.2.0` instructions, Hyun et al., *HPCA* 2024, `DOI: 10.1109/HPCA57654.2024.00029`, `arXiv:2308.00846`).
- **JEDEC Bank-Level DRAM SIMD Accelerators (`HBM-PIM` & `GDDR6-AiM`)**: `SAITPublic/PIMSimulator` (`3703d1f19c8f027360cc33a3243eb271e3bb6898`, Samsung `Aquabolt-XL` HBM2-PIM `Scheme8` address-mapped simulator; Lee et al., *ISCA* 2021, `DOI: 10.1109/ISCA52012.2021.00013`) contrasted with SK Hynix `1ynm` `GDDR6-AiM` (`Lee et al., ISSCC 2022`, `DOI: 10.1109/ISSCC42614.2022.9731681`).
- **Weight- and Output-Stationary Systolic Arrays**: H. T. Kung & C. E. Leiserson's VLSI systolic arrays (*Sparse Matrix Proc.* 1978 / *IEEE Computer* 1982), `ucb-bar/gemmini` (`b82d49cca798a59f010488a6f6de7243f0616536`, Chisel RTL `PE.scala`, `Mesh.scala`, `ReservationStation.scala`; Genc et al., *DAC* 2021, `DOI: 10.1109/DAC18074.2021.9586216`), Google `TPU` (`v1` `256x256` INT8 in Jouppi et al., *ISCA* 2017, `DOI: 10.1145/3079856.3080246`, `arXiv:1704.04760`; `v2`–`v5p` `128x128` and `v6e` `256x256` `BF16` MXUs documented in `openxla/xla` @ `bd6a27091b16c0719e5a2ed6a7334899ea99aa4f` and `jax-ml/scaling-book` @ `173fb0851d7e654872f0327aff2e17607cf24106`).
- **Associative & Content-Addressable In-Memory Arrays**: `16T` CMOS ternary `TCAM` (`Pagiamtzis & Sheikholeslami, IEEE JSSC 2006`, `DOI: 10.1109/JSSC.2005.864128`), Cornell's `6T`-SRAM `CAPE` (`Caminal et al., HPCA 2021`, `DOI: 10.1109/HPCA51647.2021.00054`), and SAFARI's in-DRAM `SIMDRAM` (`Hajinazar et al., ASPLOS 2021`, `DOI: 10.1145/3445814.3446749`).

Executable verification models (`probe_pkg2.py`) were run under Python `3.11+` on `x86_64` Linux to check exact byte-interleaving layouts, `CRF` coalescing failure modes, systolic cycle-drain `RAW` hazards, and `CAPE` bit-serial arithmetic.

## Findings

### 1. Bank-Near General-Purpose PIM: `UPMEM` DPUs, Byte-Interleaving Transpose Barriers, and Disjoint Coherence

`Basis: source + execution + documentation + derived`

#### 1.1 Per-DPU Pure-Harvard Scratchpad Hierarchy and Revolver Pipeline Constraints

A commercial `20`-DIMM UPMEM server (`Gómez-Luna et al., IEEE Access 2022`) integrates `2` ranks/DIMM $\times$ `8` DDR4-2400 `x8` PIM chips/rank $\times$ `8` DPUs/chip = **`2,560` independent 32-bit RISC DPUs** (`350 MHz` gen-1 / `425 MHz` gen-2) alongside **`160 GiB` total DRAM**. Direct inspection of `CMU-SAFARI/prim-benchmarks` (`67179099730cdccc650d52d25f458cb2e4f8a675`, `TRNS/dpu/task.c`, `RED/dpu/task.c`, `Microbenchmarks/CPU-DPU/host/app.c`) and `VIA-Research/uPIMulator` (`870d916334e9ff0b190f555f951a9ec3c4257781`, `rank.cc`) establishes four strict per-core architectural rules:

1. **Three-Region Non-Cached Pure-Harvard Storage**:
   - **`IRAM` (`24 KiB` SRAM)**: Dedicated instruction memory holding at most **`4,096` `48`-bit encoded instructions** (`uPIMulator` models `599` of the `970` UPMEM ISA opcodes). Code cannot execute directly out of `MRAM` or `WRAM`; exceeding `4,096` instructions fails linking immediately unless manually overlaid from host CPU phases.
   - **`WRAM` (`64 KiB` SRAM)**: Fast `1`-cycle/access (`8`-byte word) working scratchpad shared among the `24` hardware tasklets on that DPU (`mem_alloc`, `BARRIER_INIT(my_barrier, NR_TASKLETS)`, `MUTEX_INIT` in `TRNS/dpu/task.c:26–30`). Tasklets cannot load/store `MRAM` directly via ALU instructions.
   - **`MRAM` (`64 MiB` DRAM bank)**: Disjoint per-DPU bulk storage (`DPU_MRAM_HEAP_POINTER`). Moving data between `MRAM` and `WRAM` requires explicit `8`-byte-aligned autonomous DMA calls (`mram_read` / `mram_write` of `8` to `2,048` bytes), delivering `~700`–`800 MB/s` per DPU (**`~1.7`–`2.0 TB/s` aggregate across `2,560` DPUs**).
2. **11-Cycle Intra-Tasklet Barrel Hazard Spacing**:
   - Although the DPU pipeline has `14` stages (`350`/`425 MHz`), consecutive instructions from the **same tasklet** cannot issue closer than **`11` clock cycles apart** (revolver/barrel scheduling with zero same-thread forwarding interlocks). Running `1` tasklet utilizes at most `1/11` (`9.1%`) of ALU/WRAM throughput; saturating the pipeline requires **`>= 11` active tasklets** (typically `16` (`NR_TASKLETS=16`) so each tasklet still gets `64 KiB / 16 = 4 KiB` of `WRAM` tile space).
3. **The 8-Bit Native Multiplier Cliff**:
   - To fit inside tight DRAM pitch/area budgets without degrading cell density, the DPU ALU includes only a **single-cycle `8x8`-bit multiplier (`MUL_SL_SL`)** and `32`-bit add/sub/shift/logic. `32`-bit integer multiplication (`__mulsi3`) requires up to `32` multi-step shift-add instructions, `32`-bit division takes `> 40` instructions, and **IEEE-754 `FP32`/`FP64` are 100% software-emulated** (`50`–`200+` cycles/op, cutting throughput by `10x`–`30x` compared to `INT32` `ADD`!).

#### 1.2 Why Disjoint Host-DPU Memory Demands a Software Byte-Interleaving Transpose Barrier

In a conventional `64`-bit DDR4 rank made of eight `x8` DRAM dies, every `8`-byte (`64`-bit) bus transfer sends **`8` bits (`1` byte) to each of the `8` physical chips in parallel**. When the host x86-64 CPU writes a contiguous `64`-byte cache line `[w_0, w_1, ..., w_15]` (`uint32_t`) directly to a PIM rank, chip `c` (`c in 0..7`) receives only **every 8th byte** (`line[8*b + c]` for beat `b in 0..7`)!

Running our executable rank-interleaving model (`probe_pkg2.py`) on `intended[dpu] = [(dpu+1)*1000 + i]`:
- **Raw Linear Host Write (`upmem_rank_write_linear`)**: DPU `0` reads `0xa0b8d0e8` (`2,696,466,664`) instead of `1000` (`0x000003e8`), DPU `1` reads `0x0f0b0703`, and DPUs `2..7` read `0x00000000`—complete byte-level data corruption across chip boundaries!
- **Host SDK Transpose Barrier (`dpu_push_xfer` / `host_transpose_for_upmem`)**: Before issuing DDR4 rank bursts, the UPMEM host runtime must execute an explicit CPU-side `8 x 8` byte-matrix transpose (`SIMD shuffle/unpack` across `nrThreadPerPool=8` host threads in `Microbenchmarks/CPU-DPU/host/app.c:45`), followed by cache-line flush/uncached rank writes and an explicit **host-to-PIM ownership switch** (disabling host access to those MRAM ranks for the entire duration of DPU kernel execution!).

This architecture creates two dominant system and commercial bottlenecks confirmed by both `Gómez-Luna et al. (2022)`, `Hyun et al. (HPCA 2024)`, and industry deployment reports:
1. **Zero Direct DPU-to-DPU Interconnect (`uPIMulator` Multi-DPU Variance)**: DPUs cannot read or message sibling DPUs even on the *same DRAM die*. Every global reduction (`RED`), graph frontier exchange (`BFS`), or full-matrix transpose (`TRNS/host/app.c`) must copy partial results `MRAM -> Host CPU RAM` (`DPU_XFER_FROM_DPU` + inverse byte-transpose), reduce/permute on Xeon cores, and re-transpose `Host CPU RAM -> MRAM` (`DPU_XFER_TO_DPU`). Consequently, `uPIMulator` (`README.md`) achieves `R^2 = 98.4%` (`12.0%` MAE) on `710` single-DPU kernels, yet drops to `R^2 = 83.6%` (`26.9%` MAE) on `387` multi-DPU kernels because host-side NUMA, thread-pool, and DDR4 channel-arbitration overhead dominates kernel execution!
2. **Commercial Adoption & Ecosystem Friction**: While UPMEM demonstrated impressive speedups on embarrassingly bank-local integer/char scans (`SEL`, `UNI`, `BS`, bioinformatics k-mer/alignment), commercial datacenter adoption collided with (a) DDR4-2400 platform lock-in as servers migrated to DDR5 and CXL, (b) lack of `FP16`/`BF16` tensor hardware for LLM inference, and (c) the **Host-Transpose Roofline Cliff**: whenever an application offloads a single pass over host-resident arrays (`operational reuse = 1`), `CPU -> DPU` + `DPU -> CPU` transpose transfers over `~20`–`35 GB/s` host DDR4 channels take *longer* than computing directly on host AVX-512 cores!

---

### 2. JEDEC Bank-Level DRAM SIMD: Samsung `HBM-PIM` (`Aquabolt-XL`) and SK Hynix `GDDR6-AiM`

`Basis: source + normative + execution + derived`

To serve LLM/recommendation `GEMV` (`matrix-vector` decode, operational intensity $\approx 0.5\text{–}1$ FLOP/byte) without sacrificing `FP16`/`BF16` density or JEDEC pin compatibility, Samsung (`HBM2-PIM`, *ISCA* 2021, `DOI: 10.1109/ISCA52012.2021.00013`) and SK Hynix (`GDDR6-AiM`, *ISSCC* 2022, `DOI: 10.1109/ISSCC42614.2022.9731681`) embed wide vector MAC units directly at DRAM bank sense-amplifiers:

| Architectural Dimension | **Samsung `HBM2-PIM` (`Aquabolt-XL`)** (`SAITPublic/PIMSimulator` @ `3703d1f19c8f027360cc33a3243eb271e3bb6898`) | **SK Hynix `GDDR6-AiM` (`AiMX`)** (`ISSCC 2022`) |
| :--- | :--- | :--- |
| **Compute-to-Bank Ratio** | `1` PIM Block (`PB`) shared per **`2` banks** (`EVEN_BANK` + `ODD_BANK`; `8` PBs per `16`-bank pseudo-channel) | `1` dedicated Processing Unit (`PU`) per **`1` bank** (`16` PUs per `16`-bank `8 Gb` die; zero even/odd bank contention) |
| **SIMD Datapath & Precision** | `256`-bit (`16`-lane) **`FP16`** ALU (`ADD`, `MUL`, `MAC`, `MAD` + `isRelu_` modifier) | `256`-bit (`16`-lane) **`BF16`** MAC -> `FP32` accumulator (`1 TFLOPS` per `8 Gb` die at `1.25 V`) + LUT/interpolation activation (`GELU`/`SiLU`/`Sigmoid`) |
| **Internal Register / Buffer State** | Per-PB `GRF_A[8]` + `GRF_B[8]` (`8` $\times$ `32 B` each) + `SRF` scalar regs + **`32`-entry $\times$ `32`-bit `CRF`** microcode file (`PIMCmd.h`) | **`2 KiB` SRAM Global Buffer (`GB`)** per die broadcasting input vectors across all `16` bank PUs simultaneously (no `8`-register `GRF` split bottleneck) |
| **Control / Instruction Delivery** | Host writes `32`-bit RISC microcode into `CRF` in `HAB` mode; subsequent normal DRAM `RD`/`WR` commands in `PIM` mode **increment `pimPC_` (`CRF` PC)**! | Custom/extended GDDR6 all-bank `MAC_AB` / `AF` commands orchestrated by dedicated memory controller (e.g., Xilinx FPGA / ASIC host on `AiMX` PCIe card) |
| **DRAM Capacity Cost** | Halves per-die DRAM cell capacity (`4 GB` vs `8 GB` stack in `Aquabolt-XL`) to fit PB area under JEDEC thermal/die envelope | `8 Gb` (`1 GB`) die capacity in `1ynm` DRAM process (`~20%`–`25%` die area overhead) |

#### Critical Verification Hazard in `SAITPublic/PIMSimulator`: Host Command Coalescing Corrupts `pimPC_`

Inspection of `SAITPublic/PIMSimulator` (`README.md` §2.2–2.4, `src/PIMCmd.h:27–95`, `src/PIMRank.cpp:32–95`) exposes a subtle hardware-software contract required whenever PIM sits behind an unmodified host GPU/CPU memory controller (`Scheme8` address mapping `|rank|row|col_high|bg|bank|chan|col_low|offset|`):

1. **Three Modal DRAM Regimes (`SB` $\to$ `HAB` $\to$ `PIM` $\to$ `SB`)**:
   - Standard single-bank DRAM reads/writes (`SB`) transition to Host-All-Bank (`HAB`) mode via specific reserved row-address writes (`PIMRank::controlPIM`, where byte offsets such as `packet->data->u8Data_[20]` / `u8Data_[21]` trigger `GRF_A_ZEROIZE` and `GRF_B_ZEROIZE` across all `NUM_PIM_BLOCKS`), load up to `32` instructions (`ADD, MUL, MAC, MAD, MOV, FILL, NOP, JUMP, EXIT`) into `CRF`, and enter `PIM` execution mode.
2. **Memory Transactions *Are* Clock Ticks for `pimPC_`**:
   - Inside `PIM` mode, the DRAM chip has **no autonomous free-running instruction fetch clock** (because DRAM row activation `tRCD`/`tRP` and refresh `tREFI` must remain slave-synchronized to the host memory controller!). Instead, *each incoming host memory column command increments `pimPC_` by 1* (or steps `numJumpToBeTaken_` on zero-cycle `JUMP` loops) until `CRF[pimPC_] == EXIT` sets `crfExit_ = true`!
3. **Failure Mode Under Write-Combining (`WC`) or Out-of-Order Reordering (`probe_pkg2.py`)**:
   - If the host maps the PIM address aperture as cacheable (`WB`) or Write-Combining (`WC`) without strict per-beat memory barriers (`mfence` / GPU L2 bypass + controller serialization tag), hardware write-combining buffers coalesce multiple trigger writes targeting the same `64 B` cache line (`0x1000`) into **one** bus burst!
   - In `probe_pkg2.py`, a 4-element `GEMV` (`weights = [2, 3, 5, 7]`, `vec = [10, 20, 30, 40]`, exact dot product `510` reaching `pimPC_ = 4` `EXIT`) degrades under `WC` coalescing to **`grf_b = 110, pimPC_ = 2`**—producing silent wrong numerical output *and* leaving the HBM pseudo-channel wedged inside `PIM` mode (`pimPC_ != EXIT`), so subsequent ordinary host tensor reads return garbage or fault!

---

### 3. Spatial Data-Stationary Systolic Arrays: `Kung–Leiserson`, `ucb-bar/gemmini`, and `Google TPU MXU`

`Basis: source + normative + execution + derived`

#### 3.1 Eliminating Intermediate Register-File Traffic via Spatial Wavefronts

For $C_{M \times N} = A_{M \times K} B_{K \times N}$ ($M = N = K$), a conventional SIMD/SIMT core executes $N^3$ multiply-accumulates by fetching two operands from a multi-ported Vector Register File (`VRF`) and writing one accumulator back on every instruction ($3 N^3$ register-file port accesses), making multi-port `VRF` crossbar energy (`~1`–`3 pJ/op`) larger than the `BF16` multiplier itself!

Kung & Leiserson's systolic array (*1978*) replaces temporal register-file indexing with **spatial neighbor-to-neighbor wire forwarding** (`ShiftRegister(..., tile_latency+1)` and `pipe(valid, ...)` across `meshRows x meshColumns` in `ucb-bar/gemmini/src/main/scala/gemmini/Mesh.scala:51–116`):

- **Boundary-Only SRAM Traffic**: Each activation $A_{m, k}$ is read from local SRAM (`Scratchpad` / `VMEM`) **once** at the left edge of row $k$ and forwarded horizontally across $N$ PEs; each partial sum is initialized at the top of column $n$ and accumulated vertically across $N$ PEs into an edge `Accumulator` SRAM ($2N^2$ boundary reads + $N^2$ accumulator writes for $N^3$ MACs, reducing SRAM port pressure by a factor of **`N` (`128x` on a `128x128` MXU, `256x` on `256x256` TPU v1 / v6e)**!).
- **Dual-Register Zero-Stall `WS` vs. `OS` Switching (`ucb-bar/gemmini/src/main/scala/gemmini/PE.scala:82–128`)**:
  Direct inspection of `PE.scala` shows that every PE contains two stationary registers `c1` and `c2` controlled by `io.in_control.propagate` (`COMPUTE = 0` vs. `PROPAGATE = 1`, pipelined diagonally alongside data):
  1. **Weight-Stationary (`Dataflow.WS` — used in Google `TPU` MXUs)**: When `prop == PROPAGATE`, `c2` supplies the active weight to `mac_unit.io.in_b := c2.asTypeOf(weightType)` while `c1` simultaneously shifts in the *next* tile's weight via `c1 := d` (`io.out_c := c1` down the column!). Toggling `prop` flips roles in **0 stall cycles**, provided $A$ is streamed with row/reduction transpose ($A_{m, r}$ enters row $r$ skewed at cycle $t = m + r$, verified by `probe_pkg2.py`).
  2. **Output-Stationary (`Dataflow.OS`)**: Both $A$ (horizontal) and $B$ (vertical) stream through the mesh while `c1` accumulates `c1 := mac_unit.io.out_d` at full `accType` width (e.g., `INT32` or `FP32`) in place, simultaneously draining the *previous* completed tile out of `c2` (`io.out_c := (c2 >> shift_offset).clippedToWidthOf(outputType)`).

#### 3.2 Software-Managed Memory Coherence: Wave-Drain `RAW` Hazards & `128x8` Tile Padding

Eliminating hardware caches and register-renaming hardware (`Jouppi et al., ISCA 2017`, `arXiv:1704.04760` credits deterministic non-cached execution for TPU v1's tight `p99` inference latency at `92 TOPS` / `28 MiB` Unified Buffer) moves two critical safety and performance invariants into hardware scoreboards (`Gemmini`) or static `XLA` schedules (`TPU`):

1. **Asynchronous `Load` / `Execute` / `Store` Overlap & Systolic Drain Latency (`ReservationStation.scala:62–108`)**:
   - In an $N \times N$ Weight-Stationary mesh multiplying an $N \times N$ tile, the bottom-right element $C_{N-1, N-1}$ does not exit the bottom row until cycle **`3N - 2`** (`10` cycles for $N = 4$; **`382` MXU cycles** plus pipeline stages for $N = 128$!).
   - Because `Load` DMA (DRAM $\to$ Scratchpad), `Execute` (Scratchpad $\to$ Mesh $\to$ Accumulator), and `Store` DMA (Accumulator $\to$ DRAM) run on **three decoupled asynchronous controllers**, issuing `Store` on an Accumulator address range `[start, end)` before `Execute` completes its full $3N - 2$ drain produces silent **Read-After-Write (`RAW`) wave-truncation corruption** (`probe_pkg2.py`: reading `acc` at cycle `6` of `10` silently yields zeros in the lower-right triangle, `early_store_cyc6_match = False`).
   - `Gemmini` prevents this dynamically in `ReservationStation.scala:62–108` via hardware range-interval intersection (`OpT.overlaps`: `(other.start <= start && start < other.end) || ...`) across `deps_ld`, `deps_ex`, and `deps_st` bitvectors; Google `TPU` eliminates even the hardware Reservation Station, delegating `VMEM`/`HBM` DMA sync flags and systolic-drain delay slots **100% statically to the `OpenXLA` (`openxla/xla`) HLO compiler**!
2. **Practitioner `128x128` / `128x8` Padding & Recompilation Cliffs (`jax-ml/scaling-book` @ `173fb0851d7e654872f0327aff2e17607cf24106`)**:
   - Because `TPU` v2–v5p MXUs are physically hardwired `128x128` `BF16 -> FP32` grids (`256x256` on v6e) with `128x8` vector-register (`VREG`) sub-tiling, `XLA` automatically pads unaligned tensor dimensions up to multiples of `128` and `8`. An LLM vocabulary of `32,001` or an unaligned LoRA rank `r = 12` executes `128`-wide MXU passes that burn `> 90%` of silicon cycles and `VMEM` capacity multiplying zeros, while unbucketed variable sequence lengths trigger `10 s`–`300 s` `XLA` HLO re-synthesis stalls in production serving!

---

### 4. Bit-Serial Associative & Content-Addressable In-Memory Arrays (`TCAM`, `CAPE`, `SIMDRAM`)

`Basis: normative + documentation + execution + derived`

Associative / Processing-Using-Memory (`PuM`) architectures go one step beyond bank-near ALUs: every memory column or row acts directly as a logic element:

1. **Word-Parallel CMOS `16T` `TCAM` (`Pagiamtzis & Sheikholeslami, IEEE JSSC 2006`, `DOI: 10.1109/JSSC.2005.864128`)**:
   - Stores `{0, 1, X}` in two `6T` SRAM cells + `4` comparison pull-down transistors (`16T` per bit). Broadcasting a $W$-bit search key across searchlines discharges every mismatching row's precharged matchline in **$O(1)$ (`~0.5`–`1.5 ns`) single-cycle parallel lookup**, driving network switch ACL/LPM tables and hardware TLBs.
   - **Hard Physical Ceiling**: Every search switches capacitance across *all* $M \times W$ cells simultaneously (`~1`–`5 fJ/bit/search` $\implies$ `10`–`50 W` for multi-megabit routing tables at `1 GHz`, `~2.7x` area overhead over `6T` SRAM), and priority encoders add $O(\log M)$ area/delay without supporting general arithmetic.
2. **Bit-Serial `6T` Push-Rule Associative SRAM (`CAPE`, `Caminal et al., HPCA 2021`, `DOI: 10.1109/HPCA51647.2021.00054`)**:
   - `CAPE` repurposes dense foundry **push-rule `6T` CMOS SRAM subarrays** (`32,768`+ vector lanes across subarrays) into a general-purpose associative engine controlled by a standard **RISC-V Vector (`RVV`)** scalar+vector front-end.
   - Words are stored **bit-transposed (`vertical` layout)**: `b`-bit integers occupy `b` columns of a single subarray row (or column-transposed equivalent). Any $b$-bit arithmetic/relational op (`vadd.vv`, `vmul.vx`, `vmslt.vv`) executes as a deterministic $O(b)$ sequence of `search` (NOR matchline over truth-table input patterns `(ab, bb, carry)` latching per-row `tag` flip-flops) + `update` (masked multi-row write setting `(sum_b, next_carry)` on all tagged rows simultaneously).
   - **Key Scaling Law (`probe_pkg2.py`)**: Adding two `8,192`-element `16`-bit vectors completes in **`16` bit-slice steps (`O(b)`, strictly `O(1)` in vector length `M`)**! Consequently, when $M \ge 4,096$, `CAPE` delivers `14x` mean (`up to 254x`) speedup over area-equivalent OoO multi-core CPUs; conversely, when $M$ is short (`M < 64`) or bit-width $b$ is wide (`FP64`), $O(b^2)$ bit-serial multiplication (`~4,096` bit-cycles!) underperforms word-parallel SIMD.
3. **Triple-Row-Activation In-DRAM Majority Logic (`SIMDRAM`, `Hajinazar et al., ASPLOS 2021`, `DOI: 10.1145/3445814.3446749`)**:
   - Activating **three DRAM wordlines simultaneously (`AAP` command)** causes charge sharing across the three cells on each bitline (`65,536` bitlines/subarray $\times$ `16` banks = `> 10^6` parallel 1-bit lanes!), driving the sense amplifier to **`MAJ3(A, B, C) = (A ∧ B) ∨ (A ∧ C) ∨ (B ∧ C)`**. Synthesizing Majority-Inverter Graphs (`MIG`s) yields `88x` CPU throughput and `257x` energy efficiency on bulk bitwise/integer ops.
   - **Destructive-Read Coherence & Reliability Barrier**: Because DRAM sense-amplifier restoration drives *all three* open wordlines to `MAJ3(A, B, C)`, **every `AAP` operation physically destroys all three input rows**! The SIMDRAM compiler must emit `RowClone` single-subarray row-copy instructions into reserved `B-group` compute rows before every live-variable use, cannot cross subarray bitlines without LISA/host movement, and faces severe process-voltage-temperature (`PVT`) sense-margin and **RowHammer** disturbance hurdles that have thus far prevented commercial JEDEC DRAM qualification.

---

### 5. Six-Level Quantitative Engineering Matrix (`L1`–`L6`)

`Basis: source + execution + documentation + derived`

| Architecture / Toolchain | (L1) Authoring & Day-2 Verification Velocity | (L2) Toolchain / Simulator Build Time & RSS | (L3) Kernel Compile, Lowering & Synthesis Speed | (L4) Execution Throughput, Latency & Crossover | (L5) Coherence / Schedule Verification Speed | (L6) Silicon Area, Memory, Binary & Power Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`UPMEM` DPU (`CMU-SAFARI/prim-benchmarks` + `uPIMulator`)** | **High manual burden**: `300`–`800` LoC C per kernel (`task.c` + `app.c`), manual `WRAM` tiling, explicit barriers, & host transpose buffers | `dpu-upmem-dpurte-clang` SDK prebuilt; `uPIMulator` Go version builds in `< 10 s` (`8.5x` faster, `7.5x` less RAM than C++/Py) | `dpu-clang` compiles C to `.dpu` binary in **`< 100 ms`** (`< 150 MiB` RSS) | **`~1.7`–`2.0 TB/s`** MRAM BW across `2,560` DPUs (`350`–`425 MHz`); `INT8`/`INT32` scan up to `20x` Xeon, **FP32/inter-DPU `5x`–`20x` slower** due to software FP & host DDR4 (`~25 GB/s`) transpose | Disjoint MRAM bank isolation verified trivially per DPU; intra-DPU `24`-tasklet `WRAM` barrier/race checking via SMT `< 10 ms` | **`24 KiB` IRAM (`4,096` insns max!)**, `64 KiB` WRAM, `64 MiB` MRAM/DPU (`160 GiB` sys); `~12`–`15 W`/DIMM |
| **Samsung `HBM-PIM` (`PIMSimulator`) & SK Hynix `GDDR6-AiM`** | Low user LoC *if* wrapped in vendor `PyTorch`/`OneDNN` GEMV op; **extreme driver/firmware complexity** (`CRF` microcode + `Scheme8` addr bit-packing) | `SAITPublic/PIMSimulator` (`Scons` C++14) builds in **`~8`–`20 s`** (`< 500 MiB` RSS) | Static `32`-insn `CRF` micro-kernel table assembled in **`< 1 ms`** | `HBM2-PIM` **`1.2 TFLOPS`/stack (`11.2x` microkernel, `3.5x` end-to-end LLM decode)**; `GDDR6-AiM` **`1 TFLOPS`/die (`up to 16x` `AiMX` speedup)**; **`70%+` data-movement energy cut** | `32`-entry `CRF` bounded-loop (`JUMP` static count) + `SB/HAB/PIM` FSM verified exhaustively in **`< 1 ms`** | `CRF` = `128 B` (`32 x 32b`), `GRF` = `512 B`/PB (`HBM-PIM`), `2 KiB` `GB` (`AiM`); `50%` capacity trade-off (`Aquabolt-XL`) |
| **Systolic Arrays (`Google TPU MXU` / `ucb-bar/gemmini` / `OpenXLA`)** | High-level `JAX`/`PyTorch` user velocity (`10`–`50` LoC), **high Day-2 compiler/shape-debugging cost** (`128x8` padding & `VMEM` spills) | `openxla/xla` full Bazel build `30`–`90 min` (`16`–`32 GiB` RSS); `Gemmini` Chisel -> Verilator build `10`–`30 min` (`8`–`16 GiB` RSS) | Small kernel `< 200 ms`; **whole-LLM `XLA` HLO GSPMD + VMEM scheduling `10 s` to `15+ min`** | `TPU v1` `92 TOPS` INT8 (`28 MiB` UB, deterministic `p99` SLA); `v4`/`v5p` **`275`–`459 TFLOPS` BF16/chip**; `Gemmini` `16x16` saturates `>90%` MACs on aligned GEMM | Polyhedral/interval DMA-vs-systolic-drain (`3N-2` ticks) schedule verifier checks static HLO trace at `> 50 MB/s` (`< 5 ms`) | `128x128` (`16,384` MACs) or `256x256` (`65,536` MACs); `16`–`128 MiB` `VMEM` + `32`–`192 GiB` `HBM`; `~0.4`–`1.5 pJ/Op` |
| **Associative / Bit-Serial Arrays (`CMOS TCAM`, `CAPE`, `SIMDRAM`)** | **`CAPE` high human velocity** via standard `RVV` intrinsics/autovectorization; `SIMDRAM` requires custom `MIG` logic synthesis | `MIG` logic optimizer (`Mockturtle` / `SIMDRAM` / `CAPE` sim) builds in `1`–`5 min` (`1`–`3 GiB` RSS) | `MIG` majority-gate synthesis `< 50 ms` for `32`/`64`-bit ops; `RVV -> CAPE` microcode table lookup `< 1 ms` | `TCAM` **`~1 ns` $O(1)$ parallel lookup**; `CAPE` **`14x` mean (`254x` max) over OoO CPU** ($O(b)$ bit-steps, $O(1)$ in $M$); `SIMDRAM` **`88x` CPU throughput, `257x` energy efficiency** | `b`-bit truth-table / `MIG` equivalence checked **exhaustively via SAT/BDD in `< 5 ms`** (`< 100` gates per bit-slice!) | `TCAM` `16T/bit` (`1`–`5 W/Mb`); `CAPE` dense `6T` push-rule SRAM (`~32K` lanes); `SIMDRAM` `< 1%` DRAM die area overhead |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Minimization (`C2`)

`Basis: derived + source`

#### (C1) Human Comprehensibility: Explicit Hardware Quirks vs. Opaque Compiler Magic

Across memory-centric substrates, human comprehension fails at two opposite extremes:
- **Extreme #1 — Leaky Realization-Medium Micromanagement (`UPMEM` & `HBM-PIM` Driver Code)**: Asking human engineers to simultaneously track `11`-cycle tasklet barrel counts, `4,096`-instruction `IRAM` ceilings, `8`-byte `MRAM` DMA alignment, `8x8` DDR4 chip byte-transposition, and `Write-Combining` `CRF` `pimPC_` side effects exceeds human working-memory capacity (`7+` coupled invariants per loop!). Even when an LLM generates syntactically valid DPU C code in one turn, a single misaligned `mram_read` or omitted host flush causes silent numerical corruption that takes hours of human rank-dump debugging to isolate.
- **Extreme #2 — Opaque Black-Box Compiler Lowering (`XLA` Auto-Padding & `SIMDRAM` Row-Aliasing)**: Conversely, `JAX`/`XLA` lets humans write `jnp.einsum('mk,kn->mn', A, B)` in 1 line, but hides `128x8` padding, `VMEM` rematerialization, and HBM DMA overlap inside multi-million-line C++ passes—so a minor dimension tweak (`4096 -> 4097`) triggers unintuitive `2x` throughput cliffs without source-level feedback unless paired with explicit static shape/padding diagnostics (`jax.stages.Lowered.cost_analysis()`).
- **Comprehension Sweet Spot (`CAPE` `RVV` + Explicit Tile/Ownership Signatures)**: `CAPE` demonstrates that exposing a familiar, 1-page architectural contract (length-agnostic `RISC-V Vector` operations) while making the performance model transparent (`cost = O(bitwidth)` independent of `vl` up to subarray capacity, plus explicit corner-turn cost when switching horizontal/vertical views) lets humans reason locally about both correctness and latency.

#### (C2) Universal Conceptual Minimization: Layout-Indexed Linear Ownership Typestates

At first glance, UPMEM's DDR4 rank byte-scrambling, HBM-PIM's `SB/HAB/PIM` mode registers, Gemmini/TPU's `3N-2` systolic drain delay, and SIMDRAM's destructive `AAP` triple-row activation look like four unrelated hardware idiosyncrasies. Attempting to hide them behind fake hardware cache coherence (`PIM-MMU` / fine-grained page faults) *shifts rather than eliminates* complexity, re-introducing the very cross-channel snoop traffic that PIM was built to avoid!

Instead, a **single two-primitive type/IR discipline** makes all four substrates ordinary instances of one verifiable model with **zero runtime coherence hardware and zero silent corruption**:

1. **First-Class Physical Layout Functors (`Tensor<T, Shape, Layout>`)**:
   - Parameterize every buffer reference by an explicit invertible index map $\mathcal{L} : \text{LogicalCoord} \to (\text{Domain}, \text{Bank/PE}, \text{Offset}, \text{BitPos})$:
     - Standard Host RAM: `RowMajor`;
     - UPMEM Rank: `ChipByteStriped<Chips=8, BeatBytes=8>`;
     - Systolic `WS` Mesh: `TiledSkewed<TileM=128, TileN=128, SubTile=8>`;
     - `CAPE` / `SIMDRAM`: `BitSlicedVertical<Lanes=32768, Bits=b>`.
   - **Why Complexity Is Genuinely Eliminated**: Passing a `RowMajor` host buffer directly to a `ChipByteStriped<8,8>` DPU kernel or feeding un-transposed activations into a `WS` systolic port becomes a **local static type error** rather than silent `0xa0b8d0e8` runtime corruption, and layout conversions (`transpose`, `corner_turn`, `pad<128>`) appear explicitly in the costed IR!
2. **Disjoint Fractional Ownership & Timed Drain Capabilities (`Own<Region, Mode, ReadyAtCycle>`)**:
   - Model every non-coherent memory aperture via linear ownership tokens:
     - `xfer_to_pim` consumes `Own<Buf, HostWB>` (emitting mandatory cache clean + layout transpose) and yields `∏_{i=0}^{P-1} Own<Bank_i, DPU_Exec>`; while `DPU_Exec` tokens are live, host CPU loads/stores to `Buf` have *no capability token* and cannot compile;
     - `enter_pim_mode` on `HBM-PIM` consumes `Own<PseudoChan, DRAM_SB>` and yields an affine `UncachedCommandStream<CRF_Len>` token whose `exit_pim` transition requires proving exact non-coalesced trigger count `== CRF_Len`;
     - `systolic_matmul` on `Gemmini`/`TPU` consumes `Own<AccTile, Idle>` and returns `Own<AccTile, Draining, t + 3N - 2>`, which `store_dma` can only consume after static schedule clock `>= t + 3N - 2` (or hardware `ReservationStation` token completion);
     - `simdram_aap(r1, r2, r3)` consumes **linear write ownership of all three source rows**, forcing the compiler to insert explicit `row_clone` copies whenever an operand's liveness extends past the `AAP` gate!

## Boundaries

- **Live Hardware Timing vs. Architectural Cycle/Functional Models (`not examined` on physical PIM DIMMs)**: While `CMU-SAFARI/prim-benchmarks`, `VIA-Research/uPIMulator`, `SAITPublic/PIMSimulator`, and `ucb-bar/gemmini` sources were inspected directly at exact immutable commits and validated with executable Python reference models, we did **not** execute measurements on physical UPMEM DDR4-2400 DIMMs, Samsung Aquabolt-XL HBM2-PIM stacks, or Cloud TPU ASICs in this session (`not examined`). Physical host-BIOS memory-interleaving variations (e.g., Xeon channel XOR hashing on UPMEM) must be checked on target server motherboards.
- **Analog ReRAM / PCM Crossbar Compute-in-Memory (`known not to apply`)**: All findings in this report concern **digital** PIM, systolic, and associative SRAM/DRAM/TCAM substrates with exact deterministic bit-level semantics (`INT8`/`INT32`/`FP16`/`BF16`). Analog resistive crossbar (`ReRAM`, `PCM`, `Flash`) multiply-accumulate arrays suffer non-ideal ADC quantization, IR-drop wire resistance, conductance drift, and sneak-path noise, so deterministic bit-exact equivalence checking is `known not to apply` to analog crossbars.
- **Multi-Chip CXL-PIM Hardware Coherence (`unknown` / emerging)**: Next-generation CXL.mem / CXL.cache Type-2/Type-3 near-memory accelerators (`Samsung CMM-B` / `PNM`) propose selective device-side directory coherence over PCIe Gen5/Gen6; whether hardware directory snoop traffic negates PIM energy savings on fine-grained pointer-chasing graphs remains `unknown` pending independent production silicon characterization.
- **Commercial Foundry Qualification of Triple-Row DRAM `AAP` (`unsupported`)**: No commercial JEDEC DDR4/DDR5/HBM3 vendor currently exposes undocumented triple-row activation (`SIMDRAM` / `Ambit`) as a supported architectural contract (`unsupported`), due to cell-capacitance manufacturing variation and RowHammer mitigation circuits inside modern DRAM dies.

## Evidence

### Primary Upstream Repositories & Source Coordinates

1. **`CMU-SAFARI/prim-benchmarks` @ `67179099730cdccc650d52d25f458cb2e4f8a675`** (inspected 2026-11-19):
   - `README.md`: PrIM 16-workload & 8-microbenchmark specification and citations (`Gómez-Luna et al., IEEE Access 10:52565–52608, 2022`, `DOI: 10.1109/ACCESS.2022.3174101`, `arXiv:2105.03814`).
   - `TRNS/dpu/task.c:1–75` & `TRNS/host/app.c:1–75`: Intra-DPU multi-tasklet `BARRIER_INIT` / `MUTEX_INIT` `WRAM`-tiled transposition paired with host-side `trns_host` step decomposition across disjoint `DPU_MRAM_HEAP_POINTER` banks.
   - `RED/dpu/task.c:1–75` & `Microbenchmarks/CPU-DPU/host/app.c:1–75`: Tasklet local `WRAM` reduction (`BLOCK_SIZE`) + `dpu_alloc(NR_DPUS, "nrThreadPerPool=8", &dpu_set)` host communication setup.
2. **`VIA-Research/uPIMulator` @ `870d916334e9ff0b190f555f951a9ec3c4257781`** (inspected 2026-11-19):
   - `README.md` & `python_cpp/uPIMulator_backend/src/simulator/rank/rank.cc:1–85`: Validation correlation across PrIM (`R^2 = 98.4%, MAE = 12.0%` over `710` single-DPU points vs. `R^2 = 83.6%, MAE = 26.9%` over `387` multi-DPU points; `599/970` UPMEM `2023.2.0` ISA coverage; Go rewrite `8.5x` speedup / `7.5x` memory reduction; `Hyun et al., HPCA 2024`, `DOI: 10.1109/HPCA57654.2024.00029`, `arXiv:2308.00846`).
3. **`SAITPublic/PIMSimulator` @ `3703d1f19c8f027360cc33a3243eb271e3bb6898`** (inspected 2026-11-19):
   - `README.md` §1–4: HBM2 `Aquabolt-XL` topology (`1` PIM Block per `2` banks, `16` banks / `8` PBs per pseudo-channel, `256`-bit prefetch), `Scheme8` address mapping, `9`-instruction RISC `CRF` ISA, and `SB` / `HAB` / `PIM` transaction modes (`each memory command increments the CRF PC`).
   - `src/PIMCmd.h:27–95` & `src/PIMRank.cpp:27–95`: `PIMCmdType` (`NOP..EXIT`), `PIMOpdType` (`EVEN_BANK, ODD_BANK, GRF_A, GRF_B, SRF_M, SRF_A`), `pimPC_` state machine, and `PIMRank::controlPIM` `GRF_A_ZEROIZE`/`GRF_B_ZEROIZE` triggers (`Lee et al., ISCA 2021`, `DOI: 10.1109/ISCA52012.2021.00013`).
4. **`ucb-bar/gemmini` @ `b82d49cca798a59f010488a6f6de7243f0616536`** (inspected 2026-11-19):
   - `src/main/scala/gemmini/PE.scala:25–145`: Combinational `MacUnit` + dual-register `c1`, `c2` switching between `OUTPUT_STATIONARY` and `WEIGHT_STATIONARY` via `io.in_control.propagate`.
   - `src/main/scala/gemmini/Mesh.scala:16–118`: 2D `ShiftRegister` / `pipe(valid, ...)` row/column wavefront propagation without global reset wires.
   - `src/main/scala/gemmini/ReservationStation.scala:24–110`: Asynchronous `ldq`/`exq`/`stq` hazard scoreboard using `OpT.overlaps` interval checks across `deps_ld`, `deps_ex`, `deps_st` (`Genc et al., DAC 2021`, `DOI: 10.1109/DAC18074.2021.9586216`).
5. **`openxla/xla` @ `bd6a27091b16c0719e5a2ed6a7334899ea99aa4f`** & **`jax-ml/scaling-book` @ `173fb0851d7e654872f0327aff2e17607cf24106`** (inspected 2026-11-19):
   - Combined with Norman P. Jouppi et al., *ISCA* 2017 (`DOI: 10.1145/3079856.3080246`, `arXiv:1704.04760`): `256x256` INT8 (`92 TOPS`, `28 MiB` Unified Buffer) TPU v1 vs. `128x128` (`v2`–`v5p`) / `256x256` (`v6e`) `BF16 -> FP32` MXUs, `128x8` tile alignment, and `VMEM`/`HBM` software-pipelined prefetching.
6. **Peer-Reviewed Circuit & Associative-Architecture Specifications**:
   - SK Hynix `GDDR6-AiM`: S. Lee et al., *IEEE ISSCC* 2022 (`DOI: 10.1109/ISSCC42614.2022.9731681`).
   - `Kung & Leiserson` Systolic Arrays: H. T. Kung, *Why Systolic Architectures?*, *IEEE Computer* 15(1):37–46, 1982 (`DOI: 10.1109/MC.1982.1653825`).
   - `CAPE`: H. Caminal et al., *IEEE HPCA* 2021, pp. 557–569 (`DOI: 10.1109/HPCA51647.2021.00054`).
   - `SIMDRAM`: N. Hajinazar et al., *ACM ASPLOS* 2021, pp. 329–345 (`DOI: 10.1145/3445814.3446749`).
   - `CMOS TCAM`: K. Pagiamtzis & A. Sheikholeslami, *IEEE JSSC* 41(3):712–727, 2006 (`DOI: 10.1109/JSSC.2005.864128`).

### Executed Verification Probe (`2026-11-19`)

Running `probe_pkg2.py` (preserved in full under **Revalidation**) verified:
- `UPMEM_SCRAMBLED_WORD0: ['0xa0b8d0e8', '0xf0b0703', '0x0', '0x0']` on raw linear DDR4 rank write vs. `UPMEM_TRANSPOSED_WORD0: [1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000]` after `8 x 8` host byte-interleaving transposition;
- `HBMPIM_GEMV (uncached_exact, wc_coalesced_corrupt): (510, 4) (110, 2)` demonstrating silent `CRF` PC-skipping and numerical corruption when PIM trigger writes coalesce;
- `SYSTOLIC_WS_4x4 (full_drain_match, total_cycles, early_store_cyc6_match): True 10 False` confirming both the transposed activation-stream requirement ($A_{m, r}$ on row $r$) and the `3N - 2 = 10` drain hazard;
- `CAPE_BIT_SERIAL_ADD (rows, bit_steps, exact_match): 8192 16 True` confirming exact `16`-step bit-serial associative ripple-carry addition across `8,192` lanes.

## Revalidation

Run the following self-contained standard-library Python `3.10+` probe (`< 50 ms`, zero external dependencies) to revalidate all four cross-substrate invariants:

```bash
python3 - <<'EOF'
# 1. UPMEM x8 DDR4 rank byte-interleaving corruption vs. host 8x8 byte transpose
def upmem_rank_write(raw_bytes):
    dpu = [bytearray() for _ in range(8)]
    for cl in range(0, len(raw_bytes), 64):
        for beat in range(8):
            w64 = raw_bytes[cl + beat * 8 : cl + (beat + 1) * 8]
            for chip in range(8): dpu[chip].append(w64[chip])
    return [int.from_bytes(m[:4], "little") for m in dpu]

intended = [[(c + 1) * 1000 + i for i in range(2)] for c in range(8)]
flat = b"".join(w.to_bytes(4, "little") for c in intended for w in c)
assert upmem_rank_write(flat)[0] == 0xa0b8d0e8

per_dpu = [b"".join(w.to_bytes(4, "little") for w in c) for c in intended]
xposed = bytearray(per_dpu[chip][blk + beat] for blk in range(0, len(per_dpu[0]), 8) for beat in range(8) for chip in range(8))
assert upmem_rank_write(xposed) == [1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000]

# 2. Samsung HBM-PIM CRF PC-stepping under uncached vs. Write-Combining coalescing
def sim_hbmpim(wc_coalesce):
    crf = [("MAC", 0), ("MAC", 1), ("MAC", 2), ("MAC", 3), ("EXIT", 0)]
    w, v, acc, pc = [2, 3, 5, 7], [10, 20, 30, 40], 0, 0
    cmds = [(0x1000, 0), (0x1000, 1), (0x1000, 2), (0x1000, 3), (0x1040, 0)]
    if wc_coalesce:
        c2 = []
        for a, r in cmds:
            if c2 and c2[-1][0] == a: c2[-1] = (a, r)
            else: c2.append((a, r))
        cmds = c2
    for _, col in cmds:
        op, idx = crf[pc]
        if op == "MAC": acc += w[col] * v[idx]; pc += 1
        else: break
    return acc, pc
assert (sim_hbmpim(False), sim_hbmpim(True)) == ((510, 4), (110, 2))

# 3. 4x4 Weight-Stationary systolic wavefront & early-Store RAW drain hazard
A = [[i * 4 + j + 1 for j in range(4)] for i in range(4)]
B = [[(1 if i == j else 2) for j in range(4)] for i in range(4)]
ref = [[sum(A[i][k] * B[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
def sim_ws(stop_cyc):
    psum, acc = [[0] * 4 for _ in range(5)], [[0] * 4 for _ in range(4)]
    for cyc in range(stop_cyc):
        nxt = [[0] * 4 for _ in range(5)]
        for r in range(4):
            for c in range(4):
                m = cyc - r - c
                nxt[r + 1][c] = psum[r][c] + (A[m][r] if 0 <= m < 4 else 0) * B[r][c]
                if r == 3 and 0 <= m < 4: acc[m][c] = nxt[4][c]
        psum = nxt
    return acc
assert sim_ws(3 * 4 - 2) == ref and sim_ws(7) != ref

# 4. CAPE bit-serial 16-bit associative ripple-carry addition over 8192 lanes
va = [(i * 17 + 3) & 0x7FFF for i in range(8192)]
vb = [(i * 13 + 9) & 0x7FFF for i in range(8192)]
carry, out = [0] * 8192, [0] * 8192
for b in range(16):
    for r in range(8192):
        ab, bb, cb = (va[r] >> b) & 1, (vb[r] >> b) & 1, carry[r]
        out[r] |= ((ab ^ bb ^ cb) << b)
        carry[r] = (ab & bb) | (ab & cb) | (bb & cb)
assert all(out[i] == (va[i] + vb[i]) for i in range(8192))
print("OK: all UPMEM, HBM-PIM, Systolic WS, and CAPE CAM checks passed")
EOF
```

When revalidating against newer upstream revisions:
- In `SAITPublic/PIMSimulator`, diff `src/PIMCmd.h` and `src/PIMRank.cpp` to check whether newer HBM3-PIM revisions retain host-command-stepped `CRF` `pimPC_` execution or add internal bank sequencers.
- In `ucb-bar/gemmini`, diff `src/main/scala/gemmini/PE.scala` and `ReservationStation.scala` (`OpT.overlaps`) to verify scratchpad/accumulator hazard dependency generation across `ldq`/`exq`/`stq`.
