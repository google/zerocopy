# Discharging `NoDma` and `OpaqueMmio`: Coherent vs. Non-Coherent DMA Ownership, IOTLB/SMMU Revocation Races, and Posted MMIO Ordering

## Summary

Systems-code verifiers and formal microkernel models typically begin with two coarse whole-system Trusted Computing Base (TCB) assumptions:

- **`NoDma`**: no external bus-master peripheral asynchronously mutates physical RAM inside the verified address range; and
- **`OpaqueMmio`**: every memory-mapped I/O (MMIO) load or store is modeled as an unconstrained external event without register-bank side effects or interconnect buffering semantics.

Both assumptions can be discharged **incrementally per device class and per physical address range**—without rewriting a verifier's core memory model—by pairing a three-tier DMA ownership discipline (`DmaEpoch`) with a typed posted-MMIO bus refinement (`MmioBus`). Five primary-source findings govern this discharge:

1. **Three-Tier Device-DMA Ownership Taxonomy (`Tier 1` / `Tier 2` / `Tier 3`):**
   - *Tier 1 (IOMMU-Isolated Coherent DMA)* removes software cache maintenance but still requires store-buffer release (`dma_wmb()` / `__io_bw()`), exclusive physical-frame ownership transfer, and **strict synchronous IOTLB invalidation plus in-flight DMA quiescence** before reclaiming or retyping a frame to CPU RAM.
   - *Tier 2 (Cache-Managed Non-Coherent DMA)* adds cache-line-aligned ownership, pre-DMA clean (`DC CVAC`/`DC CIVAC`, `cbo.clean`/`cbo.flush`, or `CLFLUSHOPT`/`CLWB` bracketed by `MFENCE`/`SFENCE`), post-DMA invalidation (`DC IVAC`, `cbo.inval`) against speculative clean line fills, and—when buffers are unaligned, sub-page, or outside device addressing limits—software bounce buffers (`swiotlb`). Direct inspection of Linux `kernel/dma/direct.h:59–104` and `kernel/dma/swiotlb.c:1014–1092, 1735–1753` proves an asymmetric **copy/cache ordering invariant**: `sync_for_device` MUST copy CPU$\to$bounce *before* cleaning caches, whereas `sync_for_cpu` MUST invalidate caches *before* copying bounce$\to$CPU; misusing `DMA_ATTR_SKIP_CPU_SYNC` drops *both* cache invalidation and bounce copyback, causing stale CPU reads even on cache-coherent x86-64 hosts.
   - *Tier 3 (Untrusted / Byzantine Peripheral DMA)* treats the peripheral as adversarial inside any active translation aperture: safety requires page-granular (4 KiB) isolation (or bounce-pool isolation preventing sibling-object exposure), disabled or split-stage PCIe ATS (`EATS = 0` / `T2GPA = 1`), synchronous IOTLB + Device-ATC invalidation, and single-fetch copy-in validation on shared rings.
2. **IOTLB/SMMU Revocation Races Are Structurally Isomorphic to CPU TLB Shootdowns—Plus an In-Flight DMA Drain Gap:** Clearing an IOMMU page-table entry (`pteValid := false`) does not stop DMA through cached IOTLB/ATC translations until synchronous invalidation completes (`CMD_SYNC` on Arm SMMUv3, `QI_IWD_TYPE` with `SW`/`IF` on Intel VT-d, `IOFENCE.C` on RISC-V IOMMU). Crucially, Arm `ARM IHI 0070` `CMD_SYNC` guarantees completion of prior invalidation commands for *future* translations, **not** draining of already-translated in-flight DMA packets unless paired with device quiescence or root-complex drain flags (`QI_IWD_PRQ_DRAIN` / `IOFENCE.C` `PR`/`PW` + endpoint status sync). Real verified microkernels expose this exact seam: in `seL4/l4v@b0fe7693ca59` (`spec/abstract/X64/ArchVSpace_A.thy:387–389, 431`), x64 VT-d `IOSpaceCap` and `IOPageTableCap` finalization remains commented out (`FIXME x64-vtd`), leaving DMA isolation outside the verified abstract x64 proof boundary.
3. **PCIe Posted MMIO Buffering Requires Non-Posted Read-Back Flushes Against Side-Effect-Free Ports:** Under the PCI Express Base Specification (Chapter 2 Transaction Ordering), CPU MMIO writes (`writel`) are **Posted Memory Writes** (`PMW`) that complete locally at the root complex before reaching the endpoint. On Linux (`include/asm-generic/io.h:23–64, 288–298`, `arch/arm64/include/asm/io.h:110–131`, `arch/riscv/include/asm/mmio.h:134–146`), `writel()` inserts `__io_bw()` (`wmb()` / `dmb oshst` / `fence w, o`) *before* the store to order prior RAM writes ahead of a DMA doorbell, but **cannot** wait for the posted write to arrive at the endpoint. Before unmasking IRQs, issuing EOI, or starting a hardware delay after a `W1C` IRQ-ack or interrupt-mask write, drivers must issue a **non-posted MMIO read** (`readl`) to the same endpoint/bus segment (PCIe forbids a Non-Posted Read from passing a prior Posted Write in the same Traffic Class with `RO = 0`), targeting strictly an **idempotent `RO`/`RW` register** (or PCI configuration space during reset)—**never** a destructive Read-to-Clear (`R2C`) or FIFO-pop register.
4. **Progressive Stage 0 $\to$ Stage 4 Discharge Roadmap:** Kernels and verified Rust drivers can retire `OpaqueMmio` first on non-DMA peripherals (UART, PLIC/GIC, timer) using typed register-port automata (`RW`/`RO`/`WO`/`W1C`/`R2C`/`FIFO`) + posted-write flushing, then retire `NoDma` per physical region using `DmaEpoch` ownership transfer (starting with Tier 1 coherent rings, then Tier 2 non-coherent/bounce buffers, then Tier 3 untrusted peripherals), mirroring `Bedrock2`'s `ExtSpec` `mGive`/`mReceive` memory-chunk transfer pattern (`mit-plv/bedrock2@0005c47b5eaa:Semantics.v:27–57`).
5. **Kernel-Checked Lean 4 (`v4.34.1`) Mechanization (`support/dma_iotlb_mmio_probe.lean`):** A standalone constructive `Type 0` module (`prelude` + `Init.*`, zero `sorry`, zero custom axioms, zero `Classical.choice`, zero `Lean.ofReduceBool`) proves five concrete counterexample theorems (stale-IOTLB DMA corruption after premature frame retyping; posted `W1C` IRQ-ack race without read-back flush; relaxed doorbell reordering without `dma_wmb`; `R2C` read-back status clobbering; missing post-DMA cache invalidation) alongside `safeStep_preserves_inv`, `discharge_noDma_cpuOwned_view_invariant`, `discharge_opaqueMmio_w1c_readback_refinement`, and coherent/non-coherent `DmaEpoch` roundtrip theorems.

## Applicability

This report applies to operating-system kernels, hypervisors, firmware, and bare-metal or kernel-mode Rust device drivers targeting PCIe and SoC interconnects on **AArch64**, **RISC-V (RV64 + `Zicbom` + RISC-V IOMMU v1.0)**, and **x86-64 (Intel VT-d / `CLFLUSHOPT`/`CLWB`)** when replacing coarse `NoDma` and `OpaqueMmio` verification assumptions with fine-grained formal contracts.

### Subject Relationships

- **PCIe Base Specification (Rev 5.0/6.0)** defines the normative interconnect ordering rules for Posted Memory Writes (`PMW`), Non-Posted Reads (`NPR`), Completions (`Cpl`), and Relaxed Ordering (`RO`), which **Linux `torvalds/linux@4405c18c95d2`** implements in `include/asm-generic/io.h`, `arch/arm64/include/asm/io.h`, `arch/riscv/include/asm/mmio.h`, and `Documentation/driver-api/device-io.rst`.
- **Arm SMMUv3 (`ARM IHI 0070`)**, **Intel VT-d (Rev 4.1+ §6.5)**, and **RISC-V IOMMU v1.0 (`riscv-non-isa/riscv-iommu`)** define the normative IOTLB/ATC invalidation and synchronization queues instantiated in Linux's `drivers/iommu/{arm/arm-smmu-v3/arm-smmu-v3.c, intel/dmar.c}` and contrasted against `seL4/l4v@b0fe7693ca59` and `mit-plv/bedrock2@0005c47b5eaa`.
- **Linux `kernel/dma/{direct.h, swiotlb.c}` and `arch/x86/mm/pat/set_memory.c`** supply concrete implementation evidence for Tier 2 non-coherent cache maintenance and software bounce-buffer ordering.
- **Lean 4 (`v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`)** executes the self-contained mechanization in `support/dma_iotlb_mmio_probe.lean` characterizing the protocol invariants and counterexamples derived from the specifications above.

### Scope Boundaries and Cross-References to Adjacent Corpus Packages

To avoid duplicating established corpus material, this package targets the **integration delta** connecting posted MMIO ordering, 3-tier DMA/bounce ownership, IOTLB revocation vs. CPU TLB shootdowns, and progressive `NoDma`/`OpaqueMmio` TCB discharge. Adjacent corpus packages cover specialized sub-topics in full depth:

- `verified-software-hardware-ffi-mmio-dma-interconnects-and-reconfigurable-fabrics`: `Bedrock2`+`Kami` RTL refinement, `Pancake` on `seL4`, `AXI4`/`TileLink-C`/`RoCC` handshake causality, `CXL 2.0/3.0`, and FPGA DPR.
- `non-coherent-dma-cache-maintenance-zicbom-granules-and-adjacent-field-tearing-hazards`: byte-level adjacent-field tearing impossibility under `Zicbom` vs. AArch64 `DC CIVAC`/`DC IVAC` and sequential Sail ISA blind spots.
- `tock-mmio-w1c-register-bitfields-and-sbi-ffi-noreturn-fallthrough-hazards`: `tock-registers` bus provenance, `W1C` bitfield clobbering via `Write::modify`, and Rust `ucg#615` non-synchronizing volatile semantics.
- `multicore-interrupt-controllers-plic-claim-complete-and-shared-mmio-ordering`: RISC-V PLIC vs. ARM GICv3 state machines, RVWMO `mmiowb()`, and multi-hart `W1C` commutativity.
- `rdma-weak-memory-iommu-ats-and-byzantine-peripheral-verification`: one-sided RDMA (`rdmatso`), PCIe ATS/Thunderclap bypasses, cross-architecture IOMMU register tables, and Linux `IOMMU_DOMAIN_DMA_FQ` lazy flush-queue / `DevATC`-before-`IOATC` races.
- `double-fetch-toctou-shared-dma-rings-and-single-fetch-logics`: shared userspace/DMA ring single-fetch semantics (`OpaqueDma -> PrivateSnapshot` vs. `LoanFrame`).
- `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement`: CPU-side partial-walk caches (PWCs), cross-ISA TLB shootdowns, and `Ghost Dirty-Set` automata.

## Findings

### 1. Three-Tier Device-DMA Ownership Taxonomy and `swiotlb` Bounce-Buffer Hazards

`Basis: normative + documentation + source + derived`

Discharging a monolithic `NoDma` assumption requires separating peripherals by **coherence domain** and **trust boundary**, because the proof obligations for transferring a physical frame between CPU and peripheral differ sharply across three tiers:

| Tier & Device Class | Hardware Guarantees | Mandatory Software/Verifier Obligations | Primary Failure Modes if Discharged Naively |
| :--- | :--- | :--- | :--- |
| **Tier 1: IOMMU-Isolated Coherent DMA** (e.g., x86-64 PCIe with strict VT-d, ARM64 `dma-coherent` + strict SMMUv3, `CXL.cache` endpoints) | Hardware snooping keeps CPU caches coherent with DMA traffic; IOMMU enforces page-granular `(IOVA -> PA, R/W)` bounds. | 1. Exclusive linear ownership surrender (`CpuOwned -> DeviceMapped`).<br>2. Pre-doorbell store barrier (`dma_wmb()` / `__io_bw()`).<br>3. Strict synchronous IOTLB invalidation + in-flight DMA drain before reclaiming/retyping physical frame. | Premature frame retyping before IOTLB sync (stale-IOTLB DMA UAF); omitted `dma_wmb()` reordering RAM descriptor writes past MMIO doorbell; lazy flush queue (`IOMMU_DOMAIN_DMA_FQ`) returning backing page to slab allocator while IOTLB entry stays live. |
| **Tier 2: Cache-Managed Non-Coherent DMA** (e.g., embedded/SoC ARM64 `!dma-coherent`, RISC-V SoCs with `Zicbom`, x86-64 non-snooped/WC/PAT DMA) | No hardware cache snooping between CPU D-cache and DMA master; DMA reads/writes directly against PoC/DRAM. | All Tier 1 obligations **plus**:<br>4. Cache-line base alignment & size padding (`ARCH_DMA_MINALIGN`) OR bounce-buffer isolation (`swiotlb`).<br>5. Pre-DMA clean (`DC CVAC`/`DC CIVAC`, `cbo.clean`/`cbo.flush`, or `MB + CLFLUSHOPT + MB`).<br>6. Post-DMA invalidate (`DC IVAC`, `cbo.inval`) *after* DMA completion + IOTLB sync to purge speculatively prefetched clean lines. | Dirty cache-line writeback clobbering `DMA_FROM_DEVICE` data; sibling-field tearing on shared cache lines; speculative clean prefetch hiding DMA writes when post-DMA `DC IVAC` is skipped; `swiotlb` copy/cache inversion or skipped copyback (`DMA_ATTR_SKIP_CPU_SYNC`). |
| **Tier 3: Untrusted / Byzantine Peripheral DMA** (e.g., Thunderbolt/hotplug PCIe, multi-tenant SR-IOV, confidential VMs, firmware-untrusted NICs) | Peripheral may issue arbitrary reads/writes to any mapped IOVA, forge ATS translated requests (if `EATS` misconfigured), mutate shared descriptors mid-parse, or fail to quiesce on command. | All Tier 1 (and Tier 2 if non-coherent) obligations **plus**:<br>7. Strict 4 KiB page-granular isolation (no unrelated kernel/user data sharing a mapped 4 KiB page; bounce small objects into isolated pool).<br>8. Disable ATS (`STE.EATS = 0` / `EN_ATS = 0`) or enforce split-stage translation (`EATS = 0b10` / `T2GPA = 1`).<br>9. Single-fetch / copy-in validation on every descriptor read from device-accessible memory.<br>10. Synchronous IOTLB + Device-ATC invalidation with timeout-fault containment (never reuse a frame if ATC invalidation times out). | Sub-page neighbor corruption (Thunderclap); double-fetch TOCTOU over shared descriptor rings; stale `DevATC` writes after `IOATC` flush; uninitialized bounce-slot bytes leaking kernel secrets on `DMA_TO_DEVICE`. |

#### 1.1 Cross-ISA Cache Maintenance Primitives for Tier 2

Direct inspection of `torvalds/linux@4405c18c95d2` confirms three distinct architectural patterns for Tier 2 cache maintenance:

- **AArch64 (`arch/arm64/mm/cache.S`, `arch/arm64/include/asm/barrier.h:67–69`):** `DC CVAC` (clean to PoC) for `DMA_TO_DEVICE`, `DC CIVAC` (clean & invalidate) for unaligned boundary/pre-DMA cleanup, and `DC IVAC` (invalidate to PoC) post-DMA, paired with `DSB SY` (and `dmb(oshst)` / `dmb(oshld)` for coherent outer-shareable DMA barriers).
- **RISC-V `Zicbom` (RISC-V CMO spec):** `cbo.clean` (clean), `cbo.flush` (clean & invalidate), and `cbo.inval` (invalidate), bracketed with RVWMO I/O fences (`fence rw, o` before device trigger, `fence i, r` after completion). Notice that `cbo.inval` discards dirty lines without writeback and is controlled by `[m|s|h]envcfg.CBIE` (`0b11` = invalidate, `0b01` = silently promoted to flush).
- **x86-64 Non-Snooped / PMEM / PAT (`arch/x86/mm/pat/set_memory.c:328–354`):** Unlike legacy `CLFLUSH` (which was ordered with respect to stores), `CLFLUSHOPT` and `CLWB` are **weakly ordered** with respect to normal stores and each other. Linux `clflush_cache_range()` explicitly brackets the `clflushopt(p)` loop with `mb()` **both before and after** (`set_memory.c:346–354`: *"CLFLUSHOPT is an unordered instruction which needs fencing with MFENCE or SFENCE to avoid ordering issues"*).

#### 1.2 Software Bounce-Buffer (`swiotlb`) Ordering, Copyback, and Infoleak Hazards

`Basis: source + documentation + derived`

When a buffer cannot satisfy hardware DMA constraints—because it lacks cache-line alignment (`Documentation/core-api/dma-api-howto.rst:135–140`), crosses a 32-bit DMA address mask, or shares a 4 KiB physical page with unrelated kernel data for an untrusted peripheral—kernels insert a software bounce buffer (`torvalds/linux@4405c18c95d2:kernel/dma/swiotlb.c`, fixed 2048-byte `IO_TLB_SHIFT = 11` slots). Direct inspection of `kernel/dma/direct.h:59–104` and `kernel/dma/swiotlb.c:1014–1092, 1735–1753` exposes four verification-critical bounce-buffer invariants:

1. **Strict Asymmetric Order Between Bounce Copy and Cache Maintenance (`kernel/dma/direct.h:59–86`):**
   - **CPU $\to$ Device (`dma_direct_sync_single_for_device`, L59–70):** MUST execute `swiotlb_sync_single_for_device()` (copying `orig_addr -> bounce_slot`) **first**, and `arch_sync_dma_for_device()` + `arch_sync_dma_flush()` (cleaning cache lines of `bounce_slot` to DRAM) **second**. Reversing this order cleans stale pre-copy bounce lines and leaves the newly copied payload stranded dirty in CPU D-cache.
   - **Device $\to$ CPU (`dma_direct_sync_single_for_cpu`, L72–86):** MUST execute `arch_sync_dma_for_cpu()` + `arch_sync_dma_flush()` (invalidating stale CPU cache lines of `bounce_slot`) **first**, and `swiotlb_sync_single_for_cpu()` (copying `bounce_slot -> orig_addr`) **second**. Reversing this order copies stale cached bytes into `orig_addr`.
2. **Silent Copyback Loss Under `DMA_ATTR_SKIP_CPU_SYNC` (`kernel/dma/direct.h:99–103`):**
   ```c
   if (!(attrs & DMA_ATTR_SKIP_CPU_SYNC))
       dma_direct_sync_single_for_cpu(dev, addr, size, dir, flush);
   swiotlb_tbl_unmap_single(dev, phys, size, dir, attrs | DMA_ATTR_SKIP_CPU_SYNC);
   ```
   A driver that passes `DMA_ATTR_SKIP_CPU_SYNC` assuming it only elides redundant cache invalidation on a cache-coherent x86-64 host **also suppresses `swiotlb_sync_single_for_cpu()`**, leaving DMA-written data orphaned in the bounce slot while `orig_addr` retains stale bytes.
3. **Directional Asymmetry (`kernel/dma/swiotlb.c:1735–1753`):** `__swiotlb_sync_single_for_device` bounces only for `DMA_TO_DEVICE || DMA_BIDIRECTIONAL`, whereas `__swiotlb_sync_single_for_cpu` bounces only for `DMA_FROM_DEVICE || DMA_BIDIRECTIONAL`. Passing the wrong `enum dma_data_direction` silently drops the copy (or triggers `BUG_ON`) and breaks ownership transfer.
4. **Uninitialized Memory Infoleak (`kernel/dma/swiotlb.c:1064–1092`):** As explicitly documented in `swiotlb_bounce()` (L1066–1070, L1086–1090), mapping an uninitialized or partially initialized buffer with `DMA_TO_DEVICE` or `DMA_BIDIRECTIONAL` copies raw stack/heap bytes into the device-readable bounce slot, creating a confidentiality leak toward Tier 3 untrusted peripherals unless the verifier proves full buffer initialization (or zero-padding) before ownership transfer.

---

### 2. IOTLB / SMMU Revocation Races vs. CPU TLB Shootdowns (and Formal Microkernel Seams)

`Basis: normative + source + derived`

#### 2.1 Structural Parallel: CPU TLB Shootdown vs. IOMMU Frame Revocation

Revoking a physical frame from a DMA domain and retyping it as ordinary CPU/kernel RAM (`DeviceMapped -> CpuOwned`) obeys the **exact same three-phase concurrency structure** as revoking a virtual page from another CPU core before freeing/retyping the backing frame—with one crucial hardware strengthening requirement for **already-translated in-flight DMA packets**:

| Phase | CPU Virtual-Memory Frame Revocation (SMP) | Peripheral DMA Frame Revocation (IOMMU) | Violation if Skipped |
| :--- | :--- | :--- | :--- |
| **1. Disconnect Translation** | Clear leaf/branch PTE in page table + release-store (`store_release`) so future hardware page-table walks fault. | Clear IOMMU PTE / STE / Device Context entry (`pteValid := false`) + `wmb()` / `dmb ishst` so future IOTLB walks fault. | New speculative walks or DMA transactions continue resolving the physical frame. |
| **2. Flush Translation Caches & Rendezvous** | Issue cross-core TLB shootdown (`SFENCE.VMA` / `TLBI VAE1IS` + `DSB ISH` / IPI + `INVLPG`) and wait for every remote core ACK. | Enqueue IOTLB invalidation (`CMD_TLBI_*` / `QI_IOTLB_TYPE` / `IOTINVAL.VMA`), then (if ATS enabled) Device-ATC invalidation (`CMD_ATC_INV` / `QI_DIOTLB_TYPE` / `ATS.INVAL`), followed by synchronous fence (`CMD_SYNC` / `QI_IWD_TYPE` / `IOFENCE.C`) and wait for hardware completion. | **Stale-IOTLB DMA UAF:** device DMA hits cached IOTLB/ATC entry and overwrites newly retyped `CpuOwned` kernel/user memory (`dma_iotlb_mmio_probe.lean`: `stale_iotlb_corrupts_retyped_cpu_frame`). |
| **3. Drain Already-Translated In-Flight Traffic** | Remote CPU core's instruction retirement / IPI handler guarantees no prior store from that core using the old translation remains unretired past the IPI barrier. | **NOT universally guaranteed by IOTLB invalidation alone!** A DMA write that passed translation *before* `CMD_TLBI_*` may still be traversing the interconnect fabric. Must ensure device quiescence (stop/reset DMA ring + MMIO read-back) or hardware drain (`QI_IWD_PRQ_DRAIN`, `IOFENCE.C` `PR`/`PW` prior-read/write drain). | **Late In-Flight DMA Corruption:** an already-translated posted DMA write lands in DRAM *after* `CMD_SYNC` returns and *after* the CPU retypes the frame! |

#### 2.2 Hardware Completion Semantics Across SMMUv3, Intel VT-d, and RISC-V IOMMU

- **Arm SMMUv3 (`ARM IHI 0070`; `torvalds/linux@4405c18c95d2:drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c:324, 379`):** Commands in the SMMUv3 Command Queue may execute out-of-order. `CMD_SYNC` (configured with `CMDQ_SYNC_0_CS_SEV` or MSI completion) guarantees that all prior `CMD_CFGI_*`, `CMD_TLBI_*`, and `CMD_ATC_INV` commands have completed globally before `CMDQ_CONS` advances past `CMD_SYNC`. However, `CMD_SYNC` orders translation-cache invalidation visibility for *subsequent* transactions; software must still quiesce active endpoint DMA streams (or rely on PCIe ordering via endpoint read-back) so previously translated in-flight DMA writes cannot land in a retyped page.
- **Intel VT-d (Rev 4.1+ §6.5, §6.5.2.8; `torvalds/linux@4405c18c95d2:drivers/iommu/intel/dmar.c:1494–1580`):** `qi_submit_sync()` appends an Invalidation Wait Descriptor (`QI_IWD_TYPE | QI_IWD_STATUS_WRITE | QI_IWD_STATUS_DATA(QI_DONE)` plus optional `QI_IWD_PRQ_DRAIN`), kicks the hardware tail register via `writel(qi->free_head << shift, iommu->reg + DMAR_IQT_REG)`, and spins on `while (READ_ONCE(qi->desc_status[wait_index]) != QI_DONE)`. Note how this composes both seams: `writel` supplies `__io_bw()` before the posted doorbell, and the VT-d unit's completion write to `desc_status[wait_index]` provides an end-to-end synchronous rendezvous proving both doorbell arrival and invalidation drain.
- **RISC-V IOMMU v1.0 (`riscv-non-isa/riscv-iommu`):** `IOFENCE.C` explicitly exposes `PR` (order prior memory reads) and `PW` (order prior memory writes) alongside `AV` (4-byte completion store) and `WSI` (wired interrupt), giving software an explicit architectural hook to request prior-traffic ordering in addition to `IOTINVAL.VMA` / `ATS.INVAL` completion.

#### 2.3 Precedent in Verified Systems: `seL4/l4v` and `Bedrock2`

Direct inspection of two landmark verified systems shows *why* discharging `NoDma` and `OpaqueMmio` requires explicit ownership transfer rather than global absence axioms:

1. **`seL4/l4v` (`seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`):**
   - `spec/machine/MachineMonad.thy:17–20` splits machine state into `underlying_memory` (RAM) and `device_state` (device/MMIO memory), preventing kernel proofs from confusing RAM with MMIO registers.
   - However, in `spec/abstract/X64/ArchVSpace_A.thy:387–389, 431`, Intel VT-d `IOSpaceCap` and `IOPageTableCap` handling in `arch_finalise_cap` is explicitly commented out with `FIXME x64-vtd`. Consequently, verified seL4 proofs assume hardware DMA isolation (or `NoDma`) as an external platform assumption unless an IOMMU driver and synchronous IOTLB teardown are separately verified.
2. **`Bedrock2` (`mit-plv/bedrock2@0005c47b5eaa720bdcb9b94aceaca9f42726b861:bedrock2/src/bedrock2/Semantics.v:27–57`):**
   - `Bedrock2`'s `Class ExtSpec` parameterizes every external hardware/MMIO/DMA action by `ext_spec t mGive action args (fun mReceive resvals => ...)`: the caller literally surrenders a disjoint separation-logic memory fragment `mGive` to the external world and receives `mReceive` back on return, governed by `mGive_unique`, `weaken`, and `intersect` (`ext_spec.ok`).
   - This exact `mGive` / `mReceive` pattern generalizes cleanly to asynchronous DMA when extended with an explicit **revocation-pending epoch** (`RevokingPendingIotlbSync`) separating "OS cleared PTE" from "hardware returned `mReceive` with `NoDma` restored."

---

### 3. Posted MMIO Write Buffering, Synchronous Read-Back Flushes, and `W1C`/`R2C` Register Framing

`Basis: normative + documentation + source + execution + derived`

#### 3.1 PCIe Ordering Matrix and the Posted-Write Buffering Hazard

Under the **PCI Express Base Specification** (Chapter 2 Transaction Ordering, within the same Traffic Class `TC`):

1. **Rule A2a (Strict Posted-to-Posted Ordering, `RO = 0`):** A younger Posted Request (`PMW` / Memory Write or Message, including MSI/MSI-X) **must not pass** an older Posted Request.
2. **Rule A2b (Relaxed Ordering Exception, `RO = 1`):** A younger Posted Request with the **Relaxed Ordering (`RO`)** attribute set **may pass** an older Posted Request (or, under ID-Based Ordering `IDO`, when originating from a different Requester).
3. **Producer-Consumer DMA $\to$ MSI Guarantee:** Because upstream device DMA writes and MSI/MSI-X interrupts are *both* Posted Memory Writes, an MSI write issued with `RO = 0` **cannot overtake** preceding DMA payload writes (even if the payload writes had `RO = 1`, the subsequent `RO = 0` MSI write cannot pass them under Rule A2a). **Caveat:** If a device uses an out-of-band wired interrupt (`INTx`/SoC IRQ line) rather than an in-band MSI posted write, the wired IRQ bypasses the posted write path; the CPU ISR must execute a non-posted MMIO read from the device (whose PCIe Completion cannot pass prior upstream Posted DMA writes, `Documentation/driver-api/device-io.rst:106–111`) before reading DMA payload RAM!
4. **Non-Posted Read Flush Rule (NPR vs. PMW):** A **Non-Posted Read (`NPR`)** issued downstream by the CPU **must not pass** an earlier **Posted Memory Write (`PMW`)** targeting the same Traffic Class (`RO = 0`), and its returning Completion cannot return to the CPU until the endpoint has received and processed the read. Therefore, issuing `writel(val, reg)` followed by `readl(safe_reg)` to the **same endpoint** forces the posted write out of root-complex and switch buffers to the endpoint interface.

#### 3.2 Linux `io.h` Barrier Anatomy Across Architectures (`torvalds/linux@4405c18c95d2`)

Direct inspection of Linux's MMIO accessors reveals **two distinct ordering boundaries** that verifiers frequently conflate:

| Architecture & Source Path | `__io_bw()` (Before `writel`) | `__io_aw()` (After `writel`) | `__io_ar(v)` (After `readl`) | What `writel()` Guarantees vs. Does **Not** Guarantee |
| :--- | :--- | :--- | :--- | :--- |
| **Generic** (`include/asm-generic/io.h:23–64, 288–298`) | `wmb()` | `mmiowb_set_pending()` | `rmb()` | Orders prior normal RAM stores before the MMIO doorbell leaves the CPU; does **not** flush the PCIe posted write to the endpoint. |
| **AArch64** (`arch/arm64/include/asm/io.h:110–131`, `barrier.h:67–69`) | `dma_wmb()` (`dmb oshst`) | *(empty)* | `dma_rmb()` (`dmb oshld`) **+** synthetic control dependency (`eor %0, %1, %1; cbnz %0, .`) | Orders outer-shareable RAM writes before MMIO write; after `readl`, the dummy `eor`+`cbnz` control dependency ensures a subsequent `udelay()` (`ISB` in `get_cycles()`) cannot begin timing before the non-posted read completion returns! |
| **RISC-V** (`arch/riscv/include/asm/mmio.h:134–146`) | `RISCV_FENCE(w, o)` | `mmiowb_set_pending()` | `RISCV_FENCE(i, ir)` | Explicitly bridges RVWMO's disjoint memory (`r`/`w`) and I/O (`i`/`o`) domains; `mmiowb` orders `o` before spinlock release `w` (`fence o, w`). |
| **Relaxed (`writel_relaxed` / `readl_relaxed`)** | Compiler barrier / none | Compiler barrier / none | Compiler barrier / none | **Omits RAM-to-MMIO barriers!** Using `writel_relaxed` for a DMA doorbell without an explicit preceding `dma_wmb()` allows the device to fetch stale descriptor bytes (`relaxed_doorbell_without_wmb_reads_stale_desc`). |

#### 3.3 Why Read-Back Flushes Must Respect `W1C` / `R2C` / `FIFO` Port Framing

As documented in `Documentation/driver-api/device-io.rst:76–104` (canonical `qla1280_disable_intrs` pattern: `WRT_REG_WORD(&reg->ictrl, 0); RD_REG_WORD(&reg->ictrl);`), flushing a posted `W1C` IRQ-ack or interrupt-mask write before unmasking interrupts or signaling EOI prevents spurious/raced interrupt re-entry (`posted_mmio_irq_ack_without_readback_races`).

However, combining read-back flushing with hardware register side effects introduces a subtle verification trap:

- **Unsafe flush target (`R2C` / `RC` / pop-on-read `FIFO`):** Reading a Read-to-Clear status register (`r2cStatus`) or receive FIFO to flush an earlier posted write *does* drain the PCIe write queue, but simultaneously clears unrelated pending event flags or pops unread FIFO data (`r2c_readback_clobbers_pending_status`).
- **Safe flush target:** Verifiers must require every read-back flush to target a **side-effect-free `RO` or `RW` register** on the same PCIe function (e.g., an interrupt-enable control register, device ID register, or—during device reset when BARs may become unresponsive—PCI Configuration Space, which soft-fails cleanly via master abort rather than hanging the host bridge, `device-io.rst:80–83`).
- **Endpoint-internal caveat (`Basis: normative + derived`):** PCIe read-back guarantees **fabric transport delivery** to the endpoint interface; whether the endpoint has finished acting on an internal state transition (e.g., PLL lock, DMA engine halt) requires polling an explicit hardware status bit rather than a single dummy read.

---

### 4. Incremental Discharge Roadmap for `NoDma` and `OpaqueMmio`

`Basis: derived`

Instead of an all-or-nothing hardware model, a systems verifier can shrink its TCB across five explicit, composable stages—where each stage discharges one coarse axiom on a declared physical address partition while preserving the remaining assumption only on unverified devices:

| Stage | Target Device Class | `OpaqueMmio` Status | `NoDma` Status | Required Verifier Machinery (Zero Core-Memory-Model Rewrite) |
| :--- | :--- | :--- | :--- | :--- |
| **Stage 0 (Baseline)** | Pure CPU libraries / closed-world slices | Global TCB assumption | Global TCB assumption | Ordinary Rust/MIR memory model; explicitly record `NoDma` and `OpaqueMmio` in the audit ledger. |
| **Stage 1 (Non-DMA MMIO)** | UART, PLIC/GIC, timer, GPIO, RTC | **Discharged** on disjoint MMIO ranges `[base, base+len)` | Preserved (hardware has no bus-master DMA capability) | Typed register-bank automaton (`RW`/`RO`/`WO`/`W1C`/`W1S`/`R2C`/`FIFO` ports) + `MmioBus` posted-write queue + `RO` read-back flush rule before IRQ unmask / EOI + `mmiowb` on SMP spinlock release. |
| **Stage 2 (Tier 1 Coherent DMA)** | VirtIO, NVMe, PCIe NICs on coherent x86-64/ARM64/RISC-V with strict IOMMU | **Discharged** on device BAR + IOMMU queue MMIO | **Discharged** on `CpuOwned` frames; scoped to `DmaPool` | `DmaEpoch` frame-phase state machine (`CpuOwned -> DeviceMapped -> RevokingPendingIotlbSync -> CpuOwned(e+1)`), `__io_bw()`/`dma_wmb()` before doorbell, synchronous IOTLB sync (`CMD_SYNC` / `QI_IWD` / `IOFENCE.C`) + device quiescence before retyping. |
| **Stage 3 (Tier 2 Non-Coherent DMA)** | Embedded/SoC ARM64/RISC-V DMA engines without hardware snooping | **Discharged** (as Stage 2) | **Discharged** on `CpuOwned` frames with cache-line ownership | Extend `DmaEpoch` with `DmaCleanPending` and `PostDmaInvalPending`, `ARCH_DMA_MINALIGN` cache-line disjointness (or verified `swiotlb` bounce pool obeying `copy->clean` for device and `inval->copy` for CPU), and post-DMA `DC IVAC`/`cbo.inval` against speculative prefetches. |
| **Stage 4 (Tier 3 Untrusted / Byzantine DMA)** | Hotplug PCIe, Thunderbolt, SR-IOV VFs, confidential-computing untrusted peripherals | **Discharged** (as Stage 2, plus timeout/fault handling) | **Discharged** even against adversarial DMA inside mapped apertures | Enforce 4 KiB page-isolated DMA/bounce allocations, ATS disabled or split-stage (`T2GPA=1` / `EATS=0b10`), `IOATC`-before-`DevATC` invalidation order with timeout quarantine, and single-fetch copy-in promotion (`OpaqueDma -> PrivateSnapshot`) on all shared rings. |

---

### 5. Kernel-Checked Lean 4 (`v4.34.1`) Mechanization (`support/dma_iotlb_mmio_probe.lean`)

`Basis: execution + derived`

The self-contained Lean 4 (`v4.34.1`) artifact `support/dma_iotlb_mmio_probe.lean` uses strictly `prelude`, `Init.Core`, `Init.Data.Nat.Basic`, and `Init.Data.List.Basic` (constructive `Type 0`, zero `sorry`, zero custom axioms, zero `unsafe`/`partial`/`opaque`, zero `Classical.choice`, zero `Lean.ofReduceBool`). It mechanizes both the concrete hardware-bug counterexamples and the guarded `DmaEpoch` + `MmioBus` discharging refinement:

| Theorem (`DmaIotlbMmioDischarge.*`) | Category | Statement Summary | Axioms (`#print axioms`) |
| :--- | :--- | :--- | :--- |
| `stale_iotlb_corrupts_retyped_cpu_frame` | Counterexample | Clearing `pteValid := false` and retyping a frame to `cpuOwned 1` with CPU payload `0xAA` while `iotlbValid = true` permits a live DMA write to corrupt DRAM to `0xDE ≠ 0xAA`. | *(none)* |
| `posted_mmio_irq_ack_without_readback_races` | Counterexample | Enqueuing a posted `W1C` IRQ-ack and immediately unmasking CPU IRQs without a read-back flush leaves `cpuIrqUnmasked = true ∧ w1cIrqPending = true`. | *(none)* |
| `relaxed_doorbell_without_wmb_reads_stale_desc` | Counterexample | Issuing a relaxed doorbell while `storeBufDirty = true` (`storeBufVal = 0x42`, `dram = 0x00`) lets the device observe stale `0x00 ≠ 0x42`. | *(none)* |
| `r2c_readback_clobbers_pending_status` | Counterexample | Flushing a posted `W1C` write by reading an `r2cStatus` port clears `r2cEventPending` (`true → false`), whereas reading an `roIdempotent` port drains the write while preserving `r2cEventPending = true`. | *(none)* |
| `noncoherent_missing_post_inval_reads_stale_cache` | Counterexample | Reclaiming a Tier 2 non-coherent frame without post-DMA `DC IVAC`/`cbo.inval` after a speculative clean prefetch (`some 0x11`) causes `cpuReadFrame = 0x11 ≠ 0xBB = dram`. | *(none)* |
| `safeStep_preserves_inv` / `safeSteps_preserves_inv` | Preservation | Every guarded software and autonomous hardware transition in `SafeStep` (and its reflexive-transitive closure `SafeSteps`) preserves `HwSafeInv` (frame/IOTLB isolation, posted-MMIO IRQ safety, and doorbell store-buffer ordering). | *(none)* |
| `discharge_noDma_blocks_hwDmaWrite` / `discharge_noDma_cpuOwned_view_invariant` | **`NoDma` Discharge** | Under `HwSafeInv`, whenever `phase = cpuOwned e`, no hardware DMA write or IOTLB fill is enabled, and every autonomous hardware transition (`iotlbFill`, `dmaWrite`, `specPrefetch`, `mmioDrain`) leaves `phase`, `dram`, and `cpuReadFrame` identically unchanged. | *(none)* |
| `discharge_opaqueMmio_w1c_readback_refinement` | **`OpaqueMmio` Discharge** | From any `HwSafeInv` state with masked CPU IRQ, the concrete PCIe sequence `mmioPostW1cAck → mmioReadBackFlushRo → cpuUnmaskIrq` refines synchronous typed MMIO (`postedQueue = []`, `w1cIrqPending = false`, `cpuIrqUnmasked = true`), preserves `HwSafeInv`, and leaves `r2cEventPending` untouched. | *(none)* |
| `coherent_dma_epoch_roundtrip` | Tier 1 Refinement | End-to-end Tier 1 roundtrip (`cpuOwned e →* cpuOwned (e + 1)`) via `cpuDmaWmb → dmaMapCoherent → hwIotlbFill → hwDmaWrite → dmaClearPte → dmaIotlbSync` re-discharges `NoDma` and yields `cpuReadFrame = dmaPayload`. | *(none)* |
| `noncoherent_dma_epoch_roundtrip` | Tier 2 Refinement | End-to-end Tier 2 roundtrip (`cpuOwned e →* cpuOwned (e + 1)`) including mid-transfer `hwSpecPrefetch` proves `dmaPrepareNonCoherent → dmaPreCleanAndMap → ... → dmaClearPte → hwSpecPrefetch → dmaIotlbSync → dmaPostInval` re-discharges `NoDma` and yields `cpuReadFrame = dmaPayload`. | *(none)* |

## Boundaries

- **Single-frame abstraction in the Lean 4 probe (`known not to apply` to sub-page / multi-frame aliasing without side conditions):** `support/dma_iotlb_mmio_probe.lean` models one logical physical frame and one peripheral register bank. Discharging `NoDma` on real multi-frame systems additionally requires (i) disjoint physical frame ranges (4 KiB page isolation for Tier 3, `ARCH_DMA_MINALIGN` cache-line isolation or `swiotlb` bouncing for Tier 2) and (ii) proving that no second IOMMU stream/PASID retains an alias mapping to the same physical frame.
- **PCIe Relaxed Ordering (`RO = 1`) and ID-Based Ordering (`IDO`) on DMA/MMIO (`not examined` in Lean probe):** The Lean `MmioBusState` models strict-ordering (`RO = 0`) FIFO posted-write queues (PCIe Rule A2a) and single-TC non-posted reads. Multi-TC traffic, `RO = 1` posted write overtaking (Rule A2b), and peer-to-peer (P2P) DMA across PCIe switches are not mechanized in `dma_iotlb_mmio_probe.lean`.
- **Hardware-specific endpoint internal latency (`unknown` from PCIe transport rules alone):** As noted under Findings §3.3, PCIe read-back flushing guarantees delivery of prior posted writes to the endpoint's bus interface, not completion of arbitrary internal device microcode or analog state changes; device-specific completion polling remains a per-device datasheet obligation.
- **ARM SMMUv3 `CMD_SYNC` vs. platform interconnect drain (`unknown` across non-PCIe custom SoC fabrics):** While PCIe Root Complexes and Intel VT-d `QI_IWD_PRQ_DRAIN` / RISC-V `IOFENCE.C` `PR`/`PW` define architectural drain hooks, custom non-PCIe AXI/ACE SoC interconnects differ in whether an SMMU `CMD_SYNC` waits for already-translated downstream bursts; conservative verifiers must require explicit device DMA-engine quiescence prior to `dmaIotlbSync` on such SoCs.
- **Full multi-stage hardware ATS timeout recovery (`not examined` here):** ATS invalidation timeout quarantine (`CERROR_ATC_INV_SYNC`, `DMAR_FSTS_REG.ITE`, `cqcsr.cmd_to`) is covered in adjacent package `rdma-weak-memory-iommu-ats-and-byzantine-peripheral-verification`; the Lean probe models `dmaIotlbSync` only on the successful completion path.
- **Hardware errata and silicon bugs (`unsupported` by ISA/spec-level proofs):** Discharging `NoDma` and `OpaqueMmio` at the specification boundary reduces the software/verifier TCB to the hardware specifications themselves; silicon IOMMU bypass bugs or broken PCIe root-complex ordering implementations remain outside formal software verification.

## Evidence

### Primary Specifications and Literature (Observed 2026-11-22)

1. **PCI Express Base Specification Rev 5.0 / 6.0 (PCI-SIG):** Chapter 2 Transaction Ordering rules — Rule A2a (strict Posted-to-Posted ordering with `RO = 0`), Rule A2b (Relaxed Ordering `RO = 1` / `IDO` exception), Non-Posted Read vs. prior Posted Write ordering (read-back flush basis), and Producer-Consumer DMA-write-before-MSI ordering.
2. **Arm System Memory Management Unit Architecture Specification (`ARM IHI 0070`, Arm Limited):** Command Queue out-of-order execution, `CMD_TLBI_*`, `CMD_ATC_INV`, and `CMD_SYNC` completion-index guarantee vs. prior in-flight DMA transactions.
3. **Intel Virtualization Technology for Directed I/O (VT-d) Architecture Specification (Rev 4.1+, Intel Corporation):** Section 6.5 (Queued Invalidation Interface) and §6.5.2.8 (Invalidation Wait Descriptor `SW`/`IF`/`DR`/`DW`/`PD` completion and drain flags).
4. **RISC-V IOMMU Architecture Specification v1.0 (`riscv-non-isa/riscv-iommu`) & RISC-V CMO `Zicbom`:** `IOTINVAL.VMA`, `ATS.INVAL`, `IOFENCE.C` (`PR`/`PW`/`AV`/`WSI`), and `cbo.clean`/`cbo.flush`/`cbo.inval`.
5. **Klein et al., "Comprehensive Formal Verification of an OS Microkernel: seL4", ACM TOCS 32(2), 2014 (`doi:10.1145/2560537`):** Machine state separation (`underlying_memory` vs. `device_state`) and external DMA platform boundary.
6. **Erbsen et al., "Integration Verification Across Software and Hardware for a Simple Embedded System", PLDI 2021 (`doi:10.1145/3453483.3454069`):** `Bedrock2` `ExtSpec` memory-ownership transfer across external hardware steps.

### Directly Inspected Pinned Git Sources (Observed 2026-11-22)

- **`torvalds/linux@4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:**
  - `include/asm-generic/io.h:23–64, 224–298` (`__io_br`, `__io_ar`, `__io_bw`, `__io_aw`, `readl`, `writel`).
  - `arch/arm64/include/asm/io.h:110–131` and `arch/arm64/include/asm/barrier.h:67–69` (`dma_wmb()` = `dmb(oshst)`, `dma_rmb()` = `dmb(oshld)` + `eor`/`cbnz` control dependency).
  - `arch/riscv/include/asm/mmio.h:120–150` (`__io_bw() = RISCV_FENCE(w, o)`, `__io_ar(v) = RISCV_FENCE(i, ir)`, `__io_aw() = mmiowb_set_pending()`).
  - `arch/x86/mm/pat/set_memory.c:328–354` (`clflush_cache_range_opt`, `clflush_cache_range` bracketing `clflushopt` with `mb()` before and after).
  - `kernel/dma/direct.h:59–104` (`dma_direct_sync_single_for_device`, `dma_direct_sync_single_for_cpu`, `dma_direct_unmap_phys` bounce vs. cache-sync ordering and `DMA_ATTR_SKIP_CPU_SYNC`).
  - `kernel/dma/swiotlb.c:56, 1014–1092, 1735–1753` (`IO_TLB_SHIFT`, `swiotlb_bounce` uninitialized-buffer comments, `__swiotlb_sync_single_for_{device,cpu}` directional checks).
  - `drivers/iommu/intel/dmar.c:1494–1580` (`qi_submit_sync`, `QI_IWD_STATUS_WRITE | QI_IWD_TYPE`, `QI_IWD_PRQ_DRAIN`, `writel` to `DMAR_IQT_REG`, `READ_ONCE` poll loop).
  - `drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c:324, 379` (`CMDQ_SYNC_0_CS_SEV` vs. `CMDQ_SYNC_0_CS_NONE`).
  - `Documentation/driver-api/device-io.rst:76–117` (PCI posted-write flush `qla1280_disable_intrs` example, PCI Config Space soft-fail read-back, PIO read ordering after upstream DMA writes).
  - `Documentation/core-api/dma-api-howto.rst:111–165` (non-DMA'able memory classes and `__dma_from_device_group_begin/end`).
- **`seL4/l4v@b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`:**
  - `spec/machine/MachineMonad.thy:17–20` (`underlying_memory` vs. `device_state`).
  - `spec/abstract/X64/ArchVSpace_A.thy:387–389, 431` (`FIXME x64-vtd: IOSpaceCap and IOPageTableCap for arch_finalise_cap`).
- **`mit-plv/bedrock2@0005c47b5eaa720bdcb9b94aceaca9f42726b861`:**
  - `bedrock2/src/bedrock2/Semantics.v:27–57` (`Class ExtSpec`, `ext_spec.ok`, `mGive`/`mReceive` memory-chunk transfer).

### Mechanized Verification Execution (`support/dma_iotlb_mmio_probe.lean`, Observed 2026-11-22)

- **Toolchain:** Lean 4 `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), Linux x86-64.
- **Command:**
  ```bash
  ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1 elan run leanprover/lean4:v4.34.1 lean support/dma_iotlb_mmio_probe.lean
  ```
- **Observed Result:** Exit code `0`; all 12 `#print axioms` checks report `does not depend on any axioms` (zero `sorryAx`, zero `propext`, zero `Quot.sound`, zero `Classical.choice`, zero `Lean.ofReduceBool`, zero `Lean.trustCompiler`).

## Revalidation

1. **Re-run the Lean 4 (`v4.34.1`) Mechanization Probe:** From this package directory, execute:
   ```bash
   elan run leanprover/lean4:v4.34.1 lean support/dma_iotlb_mmio_probe.lean
   ```
   Verify exit code `0` and confirm every `#print axioms` line reports `does not depend on any axioms` (or strictly constructive kernel axioms with zero `sorryAx`, `Classical.choice`, `Lean.ofReduceBool`, or custom axioms). A passing run revalidates all five counterexamples, `HwSafeInv` preservation, per-frame `NoDma` discharge, `OpaqueMmio` posted-write `RO` read-back refinement, and coherent/non-coherent `DmaEpoch` roundtrips for the modeled single-frame/single-bus abstraction.
2. **Diff Upstream Linux Ordering & Bounce-Buffer Seams:** When targeting a newer Linux kernel revision, inspect diffs against `torvalds/linux@4405c18c95d2` in:
   - `include/asm-generic/io.h`, `arch/arm64/include/asm/io.h`, and `arch/riscv/include/asm/mmio.h` (verify whether `__io_bw`/`__io_ar`/`__io_aw` barrier semantics changed);
   - `kernel/dma/direct.h` and `kernel/dma/swiotlb.c` (verify `copy -> clean` / `inval -> copy` order and `DMA_ATTR_SKIP_CPU_SYNC` interaction);
   - `drivers/iommu/intel/dmar.c` (`qi_submit_sync`) and `drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c` (`CMD_SYNC` handling).
3. **Check `seL4/l4v` x64 VT-d Status:** Inspect `seL4/l4v:spec/abstract/X64/ArchVSpace_A.thy` around `arch_finalise_cap` to determine whether `IOSpaceCap`/`IOPageTableCap` verification has been completed in a newer revision.
4. **Hardware / Interconnect Revalidation:** For any specific target SoC or PCIe root complex, re-check the platform datasheet and IOMMU spec revision to verify whether `CMD_SYNC` / `IOFENCE.C` drains already-translated in-flight DMA bursts or requires explicit endpoint DMA quiescence before frame retyping.
