# One-Sided RDMA Weak Memory, Hardware IOMMU/ATS Shootdown Races, and Byzantine-Peripheral Verification

## Summary

Modern datacenter interconnects and DMA-capable PCIe peripherals break two foundational abstractions of verified systems software: **CPU-mediated cache-coherent memory ordering** and **atomic page-table revocation**.

1. **One-Sided RDMA Weak Memory (`rdmatso`, `rdmawait_rmw`, `coreRMA`, and Remote Persistency):** One-sided RDMA (`Put`, `Get`, `RCAS`, `RFAA`) bypasses remote CPUs and executes asynchronously through Network Interface Cards (NICs) over PCIe. Formalization of RDMA over x86-TSO (`rdmatso`, Ambal et al., OOPSLA 2024; extended to remote RMWs in `rdmatso_rmw`/`rdmawait_rmw`, Ambal et al., `arXiv:2601.14642`) establishes four anomalies that break standard CPU weak-memory intuitions: (i) NIC operations execute independently of subsequent local CPU stores (`Put(z2, x); x := 1` can transmit `1`); (ii) RDMA `Poll(n)` is non-compositional, acknowledging only the *earliest* unpolled operation to node `n`; (iii) `Put` acknowledgements arrive when the remote NIC *receives* the packet—*before* the remote write commits to DRAM (`pfp ∉ so`)—permitting Store Buffering even after `Wait(d)` and requiring a global fence (`GFence` via `Get`+`Wait`) to restore SC; (iv) `Get` remote reads (`aNRR`) can be reordered after later `Put` remote writes (`aNRW`), permitting Load Buffering, whereas remote RMW reads (`aNAR`) cannot; and (v) **remote RMWs are NOT atomic with respect to concurrent local CPU stores or `Put`s** because PCIe NICs cannot acquire exclusive cache-line ownership, guaranteeing mutual exclusion only among remote RMWs (`rao`). Furthermore, standard `Put` completion provides **zero remote crash durability** on persistent memory (NVRAM), requiring InfiniBand Annex A19 `RDMA FLUSH` or explicit remote-persistence drains (Kalia et al., SoCC 2020).
2. **PCIe Address Translation Services (`ATS`) & Thunderclap IOMMU Bypasses:** Thunderclap (Markettos et al., NDSS 2019) demonstrated that hardware IOMMUs fail in practice across macOS, Linux, FreeBSD, and Windows through four independent vectors: sub-page 4 KiB spatial spillover, cross-device isolation gaps, deferred IOTLB flushes, and **PCIe `ATS` spoofing**—where a malicious endpoint stamps arbitrary DMA writes with TLP Address Type `AT = 10b` (*Translated Request*), instructing a permissive IOMMU (`DC.tc.EN_ATS = 1, T2GPA = 0` or `STE.EATS = 0b01`) to bypass all page-table checks.
3. **IOTLB and Device-ATC Shootdown Races During Domain Teardown:** Direct inspection of the RISC-V IOMMU v1.0 specification and C reference model (`riscv-non-isa/riscv-iommu`) alongside Linux (`torvalds/linux`) Arm SMMUv3, Intel VT-d, and `dma-iommu` drivers reveals four subtle teardown races verified via exhaustive finite-state model checking (**Probe 2B**): (i) Linux's lazy flush queue (`IOMMU_DOMAIN_DMA_FQ`, 256-entry ring / 10 ms timeout, or 32,768 / 1,000 ms single-queue) returns from `dma_unmap` before IOTLB flush, exposing reallocated pages to DMA use-after-free; (ii) invalidating `DevATC` *before* `IOATC` allows the endpoint to refill its `DevATC` from the stale `IOATC`; (iii) IOMMU command-queue fences (`IOFENCE.C(PR=1,PW=1)`, `CMD_SYNC`, VT-d `QI_IWD`) commit only transactions *already processed by the IOMMU*, leaving upstream in-flight PCIe posted writes exposed without a PCIe read-completion drain; and (iv) a Byzantine endpoint ignoring `ATS.INVAL` triggers `CERROR_ATC_INV_SYNC` (SMMUv3), `DMA_FSTS_ITE` livelock retries (`qi_submit_sync` `goto restart` in Intel VT-d when `pci_device_is_present`), or `cqcsr.cmd_to` CQ halts (RISC-V).
4. **Formal Verification Against Byzantine DMA Peripherals:** Proving memory safety and confidentiality against adversarial PCIe peripherals requires **either** hardware-enforced split-stage ATS (`T2GPA = 1` / `STE.EATS = 0b10`) + strict teardown-with-quarantine (clear `EN_ATS`/`EATS`, PCIe FLR/SBR, never reclaim pages on unacknowledged timeout), **or** cryptographic link/device binding (`PCIe IDE` + `TDISP` + hardware Granule Protection Checks as implemented in `TF-RMM/tf-rmm`, Intel `TDX Connect`, and AMD `SEV-TIO`).

## Applicability

This report covers the combined hardware/software memory-ordering and DMA-isolation boundary across four linked technical domains:

- **Formal RDMA concurrency & persistency semantics:** `coreRMA` (`10.1145/2983990.2984033`, SC host CPUs over InfiniBand/DMAPP/Portals 4), `rdmatso` (`10.1145/3689781`, x86-TSO CPUs over InfiniBand/RoCE Reliable Connection QPs), RDMA SC-robustness (`10.1007/978-3-031-91118-7_3`), `rdmatso_rmw`/`rdmawait_rmw` (`arXiv:2601.14642`, adding remote `RCAS`/`RFAA`), and remote persistent memory (`10.1145/3419111.3421294`, InfiniBand Annex A19 `RDMA FLUSH`). Findings apply specifically to one-sided RDMA Reliable Connection (RC) semantics on x86-TSO hosts; ARMv8/RISC-V host CPUs introduce additional intra-node relaxations beyond TSO.
- **PCIe ATS & OS IOMMU vulnerabilities:** Thunderclap (`10.14722/ndss.2019.23194`, `thunderclap-io/arria10-ubuntu-sdcard` @ `fb644b9313085ddded28e29b40021b46a02fa885`) and Linux kernel mitigations (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`: `drivers/pci/ats.c`, `drivers/iommu/dma-iommu.c`).
- **Hardware IOMMU invalidation & teardown protocols:** RISC-V IOMMU Base Architecture v1.0 specification and reference C model (`riscv-non-isa/riscv-iommu` @ `ac1589c79d72ff109b8df6cb24803390c5021c4b`), Arm SMMUv3 (`IHI 0070`, inspected via `torvalds/linux/drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c` and `TF-RMM/tf-rmm/lib/smmuv3/src/smmuv3_tlbi.c`), and Intel VT-d (Rev 4.1+, inspected via `torvalds/linux/drivers/iommu/intel/dmar.c`).
- **Formal verification & confidential I/O architectures:** seL4 (`10.1145/2560537`), Hyperkernel (`10.1145/3132747.3132748`), SeKVM (`10.1109/SP40001.2021.00049`), Arm CCA formalizations (`Li et al., OSDI 2022`; `Fox et al., OOPSLA 2023`, `10.1145/3586040`), and `TF-RMM/tf-rmm` (`8d7961df074f08fd83a2460ab3a2ca0b658fde92`, RME-DA SMMUv3 + PCIe TDISP/IDE implementation).

**Relationship among subjects:** One-sided RDMA (`rdmatso`) characterizes the *data-plane* weak-memory anomalies of a cooperative NIC bypassing remote CPUs; Thunderclap and the IOMMU/ATS teardown audits characterize the *control-plane and isolation* failures when that same DMA-capable peripheral becomes untrusted, wedged, or Byzantine during mapping, translation caching, or domain abandonment; formal verification frameworks (SeKVM, Hyperkernel, Arm CCA/TF-RMM) show what hardware invariants and software protocols are necessary and sufficient to prove end-to-end containment. Two standalone Python 3 micro-probes (**Probe 2A** and **Probe 2B**) mechanize the `rdmawait_rmw` declarative axioms and exhaustively model-check all five IOMMU/ATS teardown protocols.

## Findings

### 1. One-Sided RDMA Weak Memory Semantics (`coreRMA`, `rdmatso`, `rdmawait_rmw`)

`Basis: normative + documentation + execution`

#### 1.1 Lineage: From `coreRMA` (OOPSLA 2016) to `rdmatso` (OOPSLA 2024) and `rdmatso_rmw` (2026)

- **`coreRMA` (Dan, Lam, Hoefler & Vechev, OOPSLA 2016):** Formalized an idealized RMA language (`put`, `get`, `flush`) with axiomatic semantics and constraint-solver litmus generation validated across InfiniBand Verbs, Cray DMAPP, and Portals 4, exposing specification gaps in hardware manuals. However, `coreRMA` assumed **Sequentially Consistent (SC)** intra-node CPU memory rather than real x86-TSO store buffers.
- **`rdmatso` (Ambal, Dongol, Eran, Klimis, Lahav & Raad, OOPSLA 2024):** Provided the first formal operational (two abstraction levels) and equivalent declarative semantics of RDMA running on **x86-TSO** multicore machines, reviewed with NVIDIA RDMA architects and empirically validated against **37 litmus tests** (extending SB, MP, LB, IRIW, 2+2W to `Put`, `Get`, `Poll`, and local CPU accesses) on real InfiniBand and RoCE hardware.
- **RDMA Robustness (Ambal, Lahav & Raad, ESOP 2025):** Derived syntactic/topological sufficient conditions ensuring that an RDMA program running under `rdmatso` exhibits **only Sequentially Consistent (SC) behaviors** (robustness against weak memory). Crucially, restricting the inter-node communication graph to a **tree topology** eliminates cyclic multi-path reorderings across disjoint network routes, substantially relaxing the fencing/polling obligations compared to arbitrary cyclic cluster graphs.
- **`rdmatso_rmw` and `rdmawait_rmw` (Ambal, Stupple, Dongol & Raad, `arXiv:2601.14642`):** Replaced non-compositional `Poll(n)` with work-identifier `Wait(d)` (`rdmawait`, embedded in the modular `mowgli`/`loco` library framework) and added formal operational and declarative semantics for **remote Read-Modify-Write operations (`RCAS`, `RFAA`)**, proving operational/declarative equivalence and verifying three classes of remote locks plus a sequentially consistent library `rdmasc_rmw`.

#### 1.2 Subevent Decomposition and the 12-Stamp Preserved-Program-Order (`sto`) Matrix

In `rdmawait_rmw` (`arXiv:2601.14642`, §3.1–3.2), every high-level CPU or RDMA method decomposes into fine-grained architectural **subevents** tagged with one of **12 stamps** (where subscript `n` denotes target remote node `n`):

- **CPU local events:** `Read(x)` $\mapsto \{aCR\}$, `Write(x, v)` $\mapsto \{aCW\}$, `Mfence()` $\mapsto \{aMF\}$, `CAS(x, v1, v2)` $\mapsto \{aCAS\}$ (if succeeding) or $\{aMF, aCR\}$ (if failing), `Wait(d)` $\mapsto \{aWT\}$.
- **RDMA `Put(x_n, y, d)` (`x_n :=_d y`):** $\{aNLR_n(y),\, aNRW_n(x)\}$ with internal synchronization order $aNLR_n(y) \xrightarrow{\text{iso}} aNRW_n(x)$ (NIC reads local buffer `y`, then writes remote location `x` on node `n`).
- **RDMA `Get(x, y_n, d)` (`x :=_d y_n`):** $\{aNRR_n(y),\, aNLW_n(x)\}$ with $aNRR_n(y) \xrightarrow{\text{iso}} aNLW_n(x)$ (NIC reads remote `y`, then writes local `x`).
- **RDMA `RFAA(x, y_n, v, d)` / succeeding `RCAS(x, y_n, v1, v2, d)`:** $\{aNAR_n(y),\, aNRW_n(y),\, aNLW_n(x)\}$ with $aNAR_n(y) \xrightarrow{\text{iso}} aNRW_n(y)$ and $aNAR_n(y) \xrightarrow{\text{iso}} aNLW_n(x)$ (failed `RCAS` omits $aNRW_n$).
- **Fences:** `Rfence(n)` $\mapsto \{aRF_n\}$ (orders subsequent remote ops to node `n` without blocking local CPU); `GFence({n})` $\mapsto \{aGF_n\}$ (global fence ensuring remote writes to `n` have completed in remote memory).

**Exact `sto` Stamp-Order Matrix (`arXiv:2601.14642`, Fig. 9):** For program-order-related subevents $\langle e_1, s_1 \rangle \xrightarrow{\text{po}} \langle e_2, s_2 \rangle$, the relation `ppo` preserves order iff $(s_1, s_2) \in \text{sto}$ (`✓` = always ordered; `✗` = may reorder; `sn` = ordered iff targeting the same remote node `n`):

| Earlier \ Later | `aCR` | `aCW` | `aCAS` | `aMF` | `aWT` | `aNLRn` | `aNRWn` | `aNARn` | `aNRRn` | `aNLWn` | `aRFn` | `aGFn` |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`aCR`** (CPU read) | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **`aCW`** (CPU write) | **✗** | ✓ | ✓ | ✓ | **✗** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **`aCAS` / `aMF` / `aWT` / `aGFn`** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **`aNLRn`** (Put local read) | ✗ | ✗ | ✗ | ✗ | ✗ | `sn` | `sn` | `sn` | `sn` | `sn` | `sn` | `sn` |
| **`aNRWn`** (Put/RMW rem. write) | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | `sn` | `sn` | `sn` | `sn` | **✗** | `sn` |
| **`aNARn`** (RMW remote read) | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | **`sn`** | `sn` | `sn` | `sn` | `sn` | `sn` |
| **`aNRRn`** (Get remote read) | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | **✗** | **✗** | `sn` | `sn` | `sn` | `sn` |
| **`aNLWn`** (Get/RMW loc. write) | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | `sn` | **✗** | `sn` |
| **`aRFn`** (Remote fence) | ✗ | ✗ | ✗ | ✗ | ✗ | `sn` | `sn` | `sn` | `sn` | `sn` | `sn` | `sn` |

#### 1.3 Declarative Consistency Axioms (`arXiv:2601.14642`, Definition 3)

Distinguishing when a subevent is **issued** (`ib`) from when it **completes** (`so`), let $\text{Inst} \triangleq \text{SEvent} \setminus (aCW \cup aNLW \cup aNRW)$ denote instantaneous subevents (those whose start and completion coincide; note buffered writes $aCW, aNLW, aNRW \notin \text{Inst}$!). With reads-from `rf = rfi ∪ rfe`, modification order `mo`, reads-before `rb = (rf^{-1}; mo)` (and internal `rbi`), NIC flush order `nfo` (total per thread between NIC reads and writes on the same side), remote atomic order `rao` (total over all `aNAR_n` targeting node `n`), and work-ID completion edges `pfg` (`aNLW_n -> aWT`) and `pfp` (`aNRW_n -> aWT`):

$$\text{ippo} \triangleq \text{ppo} \cup ([aCW]; \text{po}; [aCR \cup aWT]) \cup \bigcup_n ([aNRW_n \cup aNLW_n]; \text{po}; [aRF_n])$$
$$\text{ib} \triangleq (\text{ippo} \cup \text{iso} \cup \text{rf} \cup \text{pfg} \cup \text{pfp} \cup \text{nfo} \cup \text{rbi})^+$$
$$\text{so} \triangleq \text{iso} \cup \text{rfe} \cup \text{pfg} \cup \text{nfo} \cup \text{rb} \cup \text{mo} \cup \text{rao} \cup ([aNRW]; \text{iso}^{-1}; \text{rao}) \cup ([\text{Inst}]; \text{ib})$$

An execution is **`rdmawait_rmw`-consistent** iff (1) **`ib` is irreflexive** and (2) **`so` is acyclic** (equivalently `hb ⊇ so` is irreflexive).

#### 1.4 Six Architectural Anomalies Verified by Declarative Model Checking (Probe 2A)

1. **Asynchronous Local Buffer Mutation (`Put(z2, x); x := 1`):** Because row `aNLRn` has `✗` against `aCW`, the local CPU write `x := 1` can overtake the NIC's DMA read `aNLR_2(x)`, causing `z = 1` on Node 2 (**Probe 2A #1: ALLOWED**). Inserting `Wait(d)` (`Put_d(z2, x); Wait(d); x := 1`) adds `pfp: aNRW -> aWT` and `ippo: aWT -> aCW`, forming an `ib`-cycle and forbidding `z = 1` (**Probe 2A #2: FORBIDDEN**).
2. **Non-Compositional `Poll(n)` Pitfall (`arXiv:2601.14642`, Fig. 2):** Under raw RDMA `rdmatso`, `Poll(2)` synchronizes only with the *earliest* unpolled operation on the Queue Pair toward Node 2. Executing `z2 := x; z2 := x; Poll(2); x := 1` leaves the *second* `Put` unacknowledged, re-enabling `z = 1`! Compositional reasoning requires counting every preceding WR or using `Wait(d)` work identifiers (`rdmawait`).
3. **Store Buffering Survives `Put + Wait` (`arXiv:2601.14642`, Fig. 4):** In `x2 :=_d 1; Wait(d); a := y || y1 :=_e 1; Wait(e); b := x`, the remote NIC sends the `Put` acknowledgement as soon as the packet arrives at the remote NIC—*before* the PCIe write lands in DRAM. Formally, `pfp` enters `ib` **only**, NOT `so`, and since $aNRW \notin \text{Inst}$, $(aNRW, aWT) \in \text{ib}$ is filtered out by $[\text{Inst}]; \text{ib}$! Thus `(a, b) = (0, 0)` is **ALLOWED** (**Probe 2A #3**). Replacing `Wait` with `GFence` (implemented via a trailing `Get` + `Wait` from the target node, introducing `nfo: aNRW -> aNRR` and `pfg: aNLW -> aWT ∈ so`) creates a cycle in `so` and **FORBIDS `(0, 0)`** (**Probe 2A #4**).
4. **Load Buffering Allowed by `Get` (`aNRR`) but Forbidden by `RCAS`/`RFAA` (`aNAR`) (`arXiv:2601.14642`, Fig. 7a–b):** In `a := x2; y2 := 1 || b := y; x := 1`, cell `(aNRRn, aNRWn) = ✗` lets the `Get`'s remote read reorder after the later `Put`'s remote write, **ALLOWING `(a, b) = (1, 1)`** (**Probe 2A #5**). Replacing `Get` with `RCAS(a, x2, 8, 9)` changes the read stamp to `aNARn`, where cell `(aNARn, aNRWn) = sn`, introducing `ippo` and `so` ordering and **FORBIDDING `(1, 1)`** (**Probe 2A #6**).
5. **Non-Atomicity of Remote RMWs Against Local CPU Stores and `Put`s (`arXiv:2601.14642`, §2.3 & Fig. 6):** Because PCIe NICs cannot acquire exclusive MESI/MOESI cache-line ownership across a read-modify-write cycle (they issue separate PCIe read and write transactions to the root complex), a local CPU store `x := 1` or remote `Put` `x := 1` can interleave *between* `aNAR_n(x)` and `aNRW_n(x)` of an `RCAS(a, x, 0, 2)`, reading `0` and clobbering `1` with `2`! Mutual exclusion (`([aNRW]; iso^{-1}; rao) ⊆ so`) holds **solely among remote RMWs on the same node**; local accesses to lock words must therefore loop back through remote RMWs on the local NIC or use software node locks (`rdmasc_rmw`).
6. **PCIe Relaxed Ordering (RO) & Remote Persistency (`Kalia et al., SoCC 2020`; IBTA Annex A19):**
   - *PCIe RO polling hazard:* RDMA applications commonly poll the last byte of a destination buffer to detect `RDMA Write` arrival without a Completion Queue entry. Enabling PCIe Relaxed Ordering allows a younger posted PCIe write carrying the tail byte to overtake older payload writes across the root complex, exposing torn/stale payloads to the poller.
   - *Remote persistency gap:* Standard `RDMA Write` completion (even after `GFence`/`RDMA Read`) guarantees only **visibility** in the remote CPU cache/DDIO/volatile DRAM hierarchy, **not durability** across power loss on remote NVRAM/PMEM. Achieving one-sided remote crash consistency without two-sided remote-CPU `clwb`/`sfence` RPCs requires either **InfiniBand Annex A19 `RDMA FLUSH`** (global visibility + persistence placement) or disabling Intel DDIO on the target memory region coupled with a flushing `RDMA Read` into the ADR/eADR persistence domain (Kalia, Andersen & Kaminsky, SoCC 2020).

### 2. PCIe Address Translation Services (`ATS`) and Thunderclap IOMMU Bypasses

`Basis: normative + documentation + source`

Under the PCI Express Base Specification (Ch. 10, Address Translation Services), every PCIe Memory Read/Write Transaction Layer Packet (TLP) carries a 2-bit **Address Type (`AT`)** header field:
- `AT = 00b` (**Untranslated Request**): address is an IOVA; the IOMMU must translate it via its page tables / `IOATC` before forwarding to memory.
- `AT = 01b` (**Translation Request**): endpoint asks the IOMMU to translate an IOVA and return a host physical address (HPA) + permissions to store in the endpoint's local **Address Translation Cache (`DevATC` / `Dev-TLB`)**.
- `AT = 10b` (**Translated Request**): endpoint asserts *"I already translated this address via my `DevATC`"*; unless restricted by split-stage translation or disabled in the IOMMU device context, **the IOMMU bypasses page-table translation and forwards the raw physical address directly to DRAM!**

**Thunderclap (Markettos et al., NDSS 2019, `10.14722/ndss.2019.23194`):** Using an FPGA-based PCIe/Thunderbolt malicious-peripheral testbed emulating an Intel 82574L NIC (`thunderclap-io/arria10-ubuntu-sdcard` @ `fb644b9313085ddded28e29b40021b46a02fa885`), Markettos et al. demonstrated arbitrary kernel read/write, VPN cleartext sniffing, and root shell escalation across all four major OSes despite IOMMU hardware presence:

| OS (Evaluated in NDSS 2019) | Default External/Thunderbolt IOMMU | Primary Vulnerability Vectors Demonstrated | Demonstrated Exploit Impact |
| :--- | :--- | :--- | :--- |
| **macOS** | Enabled | 4 KiB sub-page spatial over-mapping; lack of inter-peripheral isolation (shared I/O visibility across devices) | Arbitrary root program execution; keystroke & framebuffer exfiltration |
| **Linux** | Disabled by default for external ports; trusted all PCIe endpoints | **PCIe `ATS` `AT=10b` IOMMU bypass** (malicious endpoint emits forged Translated Requests directly to raw HPA); 4 KiB sub-page exposure of network packet buffers sharing pages with kernel function pointers | Full physical memory read/write; cleartext VPN sniffing; kernel code execution |
| **FreeBSD** | Disabled by default | Sub-page exposure of `mbuf` callback function pointers sharing 4 KiB DMA-mapped pages | Root shell via overwritten callback pointer |
| **Windows** | Limited / disabled prior to Win10 1803+ Kernel DMA Protection | Unprotected external PCIe/Thunderbolt DMA paths lacking firmware-enforced IOMMU handoff | General physical memory DMA access |

**Direct Source Verification of Post-Thunderclap Linux Mitigations (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`):**
1. **Blocking `ATS` on Untrusted External Devices (`drivers/pci/ats.c:41-50`):**
   ```c
   bool pci_ats_supported(struct pci_dev *dev)
   {
       if (!dev->ats_cap || dev->untrusted)
           return false;
       if (dev->is_virtfn)
           return pci_ats_supported(pci_physfn(dev));
       return true;
   }
   ```
   External Thunderbolt/USB4 PCIe endpoints flagged `dev->untrusted` by ACPI/firmware are unconditionally denied PCIe ATS enablement (and the IOMMU's device-context `EN_ATS`/`EATS` bit stays cleared so spoofed `AT = 10b` packets fault immediately).
2. **Eliminating Sub-Page 4 KiB Spillover via SWIOTLB Bounce Buffering (`drivers/iommu/dma-iommu.c:592-629`):**
   ```c
   static bool dev_is_untrusted(struct device *dev) {
       return dev_is_pci(dev) && to_pci_dev(dev)->untrusted;
   }
   static bool dev_use_swiotlb(struct device *dev, size_t size, enum dma_data_direction dir) {
       return IS_ENABLED(CONFIG_SWIOTLB) &&
              (dev_is_untrusted(dev) || dma_kmalloc_needs_bounce(dev, size, dir));
   }
   ```
   Every DMA mapping for an untrusted PCIe device is bounced through dedicated page-aligned SWIOTLB slots (`dev_use_swiotlb` and `dev_use_sg_swiotlb` return `true`), preventing unrelated slab objects or kernel pointers on the same 4 KiB page from ever being mapped into the IOMMU.
3. **PCIe Access Control Services (`ACS`) Peer-to-Peer Requirement:** Even with IOMMU translation enabled and ATS disabled, if PCIe switches lack `ACS` Upstream Forwarding (`UF`) and P2P Request Redirect (`RR`), a malicious peripheral can issue peer-to-peer DMA directly to another device's BARs/VRAM (e.g., an NVMe controller or GPU) without packets ever reaching the Root Complex IOMMU.

### 3. Hardware IOMMU Comparison and IOTLB/ATC Shootdown Races During Domain Teardown

`Basis: normative + source + execution`

#### 3.1 Cross-Architecture Hardware Matrix: Arm SMMUv3 vs. Intel VT-d vs. RISC-V IOMMU

| Architectural Feature | Arm SMMUv3 (`IHI 0070`) | Intel VT-d (Rev 4.1+ Scalable Mode) | RISC-V IOMMU v1.0 (`riscv-non-isa/riscv-iommu`) |
| :--- | :--- | :--- | :--- |
| **Device Context Structure** | Stream Table Entry (`STE`, 64 B) indexed by `StreamID` | Context Entry / PASID Directory indexed by `RID` (`BDF`) + `PASID` | Device Context (`DC`, 32 B base / 64 B extended) in 1/2/3-level DDT indexed by `device_id` |
| **ATS Enable Control** | `STE.EATS`: `0b00` disabled, `0b01` full translated (`EATS_TRANS`), `0b10` split-stage (`EATS_S1CHK`), `0b11` reserved/bad STE | Context/PASID `DTE` (Device-TLB Enable); `PTS`/nested mode | `DC.tc.EN_ATS` (`0` faults `AT=01b/10b` with cause `260`); `DC.tc.T2GPA` (`1` forces G-stage translation of `AT=10b`) |
| **IOMMU TLB Invalidation** | `CMD_TLBI_NH_VA`, `CMD_TLBI_NH_ASID`, `CMD_TLBI_S2_IPA`, `CMD_TLBI_S12_VMALL` | `QI_IOTLB_TYPE`, `QI_EIOTLB_TYPE` (PASID-based), `QI_CC_TYPE`, `QI_PC_TYPE` | `IOTINVAL.VMA`, `IOTINVAL.GVMA`, `IODIR.INVAL_DDT`, `IODIR.INVAL_PDT` |
| **Device ATC Invalidation** | `CMD_ATC_INV` (StreamID, SSID/PASID, VA range) | `QI_DIOTLB_TYPE`, `QI_DEIOTLB_TYPE` (Device-TLB Invalidate Descriptor) | `ATS.INVAL` (RID, DSV/DSEG, PV/PID, PCIe ATS payload) |
| **Completion / Memory Fence** | `CMD_SYNC` (`CS=NONE/IRQ/SEV`, MSI write completion) | `QI_IWD_TYPE` (Invalidation Wait Descriptor with `IF`/`SW`/`FN` + `QI_IWD_PRQ_DRAIN`) | `IOFENCE.C` (`PR` prior-reads, `PW` prior-writes, `AV` 4-byte completion store, `WSI` wired IRQ) |
| **ATS Invalidation Timeout Behavior** | `CMDQ_CONS.ERR = CERROR_ATC_INV_SYNC` (halting on `CMD_SYNC`) | `DMAR_FSTS_REG.ITE` (aborts all pending wait descriptors; faulting SID in `DMAR_IQER_REG.ITESID`) | `cqcsr.cmd_to = 1` (stalls CQ at `IOFENCE.C`; `ATS.INVAL` is the *sole* command with a timeout) |

#### 3.2 Four Concrete Teardown and Invalidation Races Verified in Upstream Source & Probe 2B

**Hazard A — Lazy Flush-Queue Temporal Use-After-Free Window (`torvalds/linux/drivers/iommu/dma-iommu.c:96-102, 824-845, 1254-1276`):**
When an IOMMU domain operates in non-strict / lazy mode (`IOMMU_DOMAIN_DMA_FQ`), `dma-iommu.c` configures per-CPU deferred flush queues with `IOVA_DEFAULT_FQ_SIZE = 256` entries and `IOVA_DEFAULT_FQ_TIMEOUT = 10` ms (or `IOVA_SINGLE_FQ_SIZE = 32768` and `IOVA_SINGLE_FQ_TIMEOUT = 1000` ms when `dev->iommu->shadow_on_flush` is set, lines 97–102 and 642–648). Inside `__iommu_dma_unmap` (lines 837–845):
```c
iotlb_gather.queued = READ_ONCE(cookie->fq_domain);
unmapped = iommu_unmap_fast(domain, dma_addr, size, &iotlb_gather);
if (!iotlb_gather.queued)
    iommu_iotlb_sync(domain, &iotlb_gather);
iommu_dma_free_iova(domain, dma_addr, size, &iotlb_gather);
```
Because `iommu_iotlb_sync()` is skipped when `iotlb_gather.queued != NULL`, `iommu_dma_unmap_phys()` returns **immediately**—deferring only the *IOVA* and freed *page-table* pages in `queue_iova()`, while the driver immediately returns the **backing physical data page** to the OS page/slab allocator (`kfree`/`__free_pages`). For up to **10 ms** (or **1,000 ms** in single-queue mode), a malicious peripheral retains live IOTLB access to a physical page already reallocated to another kernel subsystem or tenant (**Probe 2B #1: 4-step counterexample**). Strict synchronous invalidation (`IOMMU_DOMAIN_DMA`, `iommu.strict=1`) is mandatory whenever endpoints are untrusted.

**Hazard B — Two-Level Cache Ordering Inversion (`DevATC` Invalidated Before `IOATC`):**
The RISC-V IOMMU specification (`riscv-non-isa/riscv-iommu/src/iommu_sw_guidelines.adoc`, §Device Address Translation Cache invalidations) states the strict causal invariant:
> *"Since a translation request from the DevATC may be satisfied by the IOMMU from the IOATC, to ensure correct operation software must first invalidate the IOATC before sending invalidations to the DevATC."*

If software clears the PTE and issues `ATS.INVAL` *before* `IOTINVAL.VMA` + `IOFENCE.C`, an adversarial endpoint can acknowledge `ATS.INVAL`, immediately send an `AT = 01b` Translation Request that hits the still-stale `IOATC`, refill its `DevATC`, wait for `IOTINVAL` to finish, and then issue `AT = 10b` Translated DMA writes to the reallocated page! **Probe 2B #2** automatically discovers this exact **8-step counterexample** (`OS_CLEAR_PTE -> OS_SEND_ATS_INVAL_BEFORE_IOTINVAL -> DEV_ACK_ATS_INVAL -> DEV_ATS_REFILL_FROM_IOATC_OR_PTE -> OS_IOTINVAL_AND_IOFENCE_DRAIN -> OS_REALLOC_PAGE -> VIOLATION`).

**Hazard C — Out-of-Order Command Queues and In-Flight Upstream PCIe Posted Writes:**
Per `riscv-non-isa/riscv-iommu/src/iommu_in_memory_queues.adoc:344-412`, *"The IOMMU fetches commands from the CQ in order but the IOMMU may execute the fetched commands out of order. The IOMMU advancing `cqh` is not a guarantee that the commands fetched by the IOMMU have been executed or committed."* Software must issue `IOFENCE.C` with `PR = 1` (for previously read-accessible pages, to prevent late DMA reads from observing newly written confidential data!) and `PW = 1` (for previously write-accessible pages, to prevent late DMA writes from corrupting reallocated pages). Crucially, lines 399–406 warn that **even `IOFENCE.C(PR=1, PW=1)` orders ONLY requests already processed by the IOMMU**—in-flight posted PCIe Memory Writes still traversing PCIe switches upstream of the IOMMU require an **interconnect-level fence** (e.g., an MMIO read from the PCIe device, since PCIe transaction ordering forbids completions from passing prior posted writes) before reclaiming pages (**Probe 2B #3: 7-step counterexample**).

**Hazard D — Byzantine Endpoint `ATS.INVAL` Timeouts, Command-Queue Stalls, and Livelock:**
A Byzantine (or wedged) ATS-enabled PCIe endpoint can simply refuse to return an *Invalidate Completion* message to `CMD_ATC_INV` / `QI_DIOTLB_TYPE` / `ATS.INVAL`, leaving the OS trapped between **liveness failure (DoS/livelock)** and **safety failure (post-teardown DMA UAF)**:
- *Arm SMMUv3 (`torvalds/linux/drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c:356-365`):* `__arm_smmu_cmdq_skip_err` handles `CMDQ_ERR_CERROR_ATC_INV_IDX` by returning without skipping, leaving `CONS` on `CMD_SYNC` to repeat indefinitely if the endpoint never responds—or, if higher layers time out and reclaim memory anyway without disabling `STE.EATS` and resetting the endpoint, permitting persistent `AT = 10b` UAF (**Probe 2B #4: 5-step counterexample**). Additionally, `arm_smmu_get_ste_update_safe` (`arm-smmu-v3.c:1323-1350`) documents a subtle hardware constraint: hitless updates to 512-bit STEs must never transiently combine `S2S = 1` (stage-2 stall) with `EATS != 0`, nor transiently form `EATS = 0b11` (reserved/errant).
- *Intel VT-d (`torvalds/linux/drivers/iommu/intel/dmar.c:1430-1479, 1575-1610`):* Upon `DMA_FSTS_ITE` (Invalidation Time-out Error), `qi_check_fault()` marks all `QI_IN_USE` entries as `QI_ABORT`, reads the faulting Requester ID from `DMAR_IQER_REG_ITESID` (VT-d Spec Rev 4.1 §11.4.9.9), and checks `pci_device_is_present(to_pci_dev(dev))`. If a **hot-unplugged** device disappeared, it returns `-ETIMEDOUT`; however, if a **Byzantine** endpoint remains electrically present on the PCIe bus (so `pci_device_is_present` stays `true`) while refusing Invalidate Completions, `qi_check_fault()` returns `-EAGAIN` and `qi_submit_sync()` loops via **`goto restart;`** (`dmar.c:1602`), enabling a single malicious ATS endpoint to livelock host invalidation threads!
- *Hardware Split-Stage ATS Containment (`T2GPA` / `EATS_S1CHK`):* Both RISC-V IOMMU (`iommu_ref_model/libiommu/src/iommu_translate.c:149-194`) and Arm SMMUv3 (`STRTAB_STE_1_EATS_S1CHK`) provide a hardware architectural defense: setting `DC.tc.T2GPA = 1` (or `STE.EATS = 0b10`) treats every `AT = 10b` Translated Request as a **Guest Physical Address (GPA)** and forces it through **Stage-2 / G-stage translation** (`DC.iohgatp`). Even a Byzantine endpoint with a compromised or un-invalidated `DevATC` can never escape its hypervisor/compartment's Stage-2 physical address space!

### 4. Formal Verification Against Byzantine DMA Peripherals

`Basis: documentation + source + execution + derived`

#### 4.1 Landscape of Formally Verified OS/Hypervisor DMA Models

| System / Architecture | Proof Assistant / Method | Threat Model for DMA Peripherals | How IOMMU / DMA Is Modeled & Verified | Residual Trust / Limitation |
| :--- | :--- | :--- | :--- | :--- |
| **seL4** (Klein et al., TOCS 2014) | Isabelle/HOL (refinement + noninterference) | Baseline proof assumes DMA out-of-scope or hardware-isolated | Separate unverified/engineering VT-d & SMMU drivers; kernel proof assumes no rogue DMA overwrites kernel memory | IOMMU shootdown & ATS not inside baseline functional correctness theorem |
| **Hyperkernel** (Nelson et al., SOSP 2017) | Rosette / Z3 SMT (push-button) | Untrusted asynchronous DMA writes to shared buffers | Models shared DMA/MMIO memory reads as `volatile` returning unconstrained symbolic values; DMA writes become symbolic environment transitions | Abstracts away hardware page-table/IOTLB/ATC caching state machine |
| **SeKVM** (Li et al., IEEE S&P 2021) | Coq (layered microverification) | Untrusted host KVM + untrusted assigned devices | Microverified EL2 `KCore` proves Arm SMMU stage-2 translation registers stay enabled and assigned device mappings never overlap `KCore` or other VMs' memory | Assumes synchronous SMMU TLB invalidation completes; does not model PCIe ATS `AT=10b` bypass or Byzantine timeouts |
| **Arm CCA / RMM** (Li et al., OSDI 2022; Fox et al., OOPSLA 2023) | Coq / Isabelle + CBMC / model checking | Untrusted host hypervisor + physical/DMA adversaries | Formalizes EL3/RMM concurrent firmware, Granule Protection Table (`GPT`) 4-PAS transitions (`Root/Secure/Realm/Non-secure`), and SMMU Granule Protection Checks (`GPC`) blocking non-Realm DMA to Realm granules | Device assignment (`RME-DA`) requires hardware `SMMU GPC` + PCIe `IDE`/`TDISP` trust anchor |
| **`TF-RMM/tf-rmm`** (`8d7961df...`, RME-DA) | C firmware + CBMC harnesses (`cbmc_vdev.c`) | Untrusted host hypervisor + external PCIe fabric eavesdroppers/spoofers | Implements `lib/smmuv3/src/smmuv3_tlbi.c` (`poll_cmd_sync_all` with acquire-load completion words) and `app/device_assignment/el0_app/src/dev_tdisp_cmds.c` enforcing PCIe `TDISP` lifecycle (`CONFIG_UNLOCKED -> LOCK_INTERFACE -> START_INTERFACE -> STOP_INTERFACE`) + Root Port DVSEC + `PCIe IDE` link encryption | Relies on hardware Root of Trust (SPDM/CMA device attestation) and `TDISP` responder conformance inside the PCIe endpoint |

#### 4.2 Necessary and Sufficient Teardown Invariants for Byzantine-Peripheral Containment

`Basis: derived + execution`

To prove **DMA Non-Interference & Zero Use-After-Free** during live domain teardown or compartment abandonment against a **Byzantine PCIe peripheral** (one that may asynchronously emit arbitrary `AT = 00b/01b/10b` requests, ignore `ATS.INVAL` messages, and continue DMA until electrically fenced or reset), a verified OS/hypervisor state machine must enforce six invariants (verified exhaustively in **Probe 2B #5**, reaching 13 states with **0 violations** across both honest and Byzantine endpoints):

1. **Spatial Granularity Invariant (No Sub-Page Sharing):** Every physical page mapped into an IOMMU domain is exclusively owned by that domain (no slab/heap sharing with unrelated kernel objects); untrusted endpoints use either dedicated 4 KiB-aligned exclusive buffers or SWIOTLB bounce pages (`dev_use_swiotlb`).
2. **ATS Policy Invariant:** For untrusted endpoints without hardware split-stage ATS, `EN_ATS = 0` (`STE.EATS = 0b00`) is invariant across the entire lifecycle so spoofed `AT = 10b` TLPs fault immediately (RISC-V cause `260`). Where ATS is required for performance, hardware split-stage enforcement (`T2GPA = 1` or `STE.EATS = 0b10`) bounds `AT = 10b` addresses by Stage-2/G-stage tables—or confidential I/O (`TDISP` + `IDE` + `GPC`) cryptographically binds the device interface (`TDI`).
3. **PTE-Before-Shootdown Invariant:** Clear and globally publish (`DMB`/`FENCE`/`SFENCE`) the IOMMU page-table entries *before* issuing any cache invalidation command.
4. **Strict Two-Level Shootdown Ordering (`IOATC` → `Sync` → `DevATC`):** Always complete and synchronize `IOTINVAL` (`CMD_TLBI` + `CMD_SYNC` / `QI_IOTLB` + `QI_IWD` / `IOTINVAL.VMA` + `IOFENCE.C`) *strictly before* issuing `ATS.INVAL` (`CMD_ATC_INV` / `QI_DIOTLB`), eliminating the `IOATC -> DevATC` refill race (**Probe 2B #2**).
5. **Dual-Layer In-Flight Drain Invariant:** After cache invalidations complete, execute **both** an IOMMU memory-ordering fence (`IOFENCE.C(PR=1, PW=1)` / `CMD_SYNC` / `QI_IWD`) **and** a PCIe-fabric drain (MMIO read completion or PCIe Bus Master disable + quiescence) before transitioning page ownership to the free pool or another tenant (**Probe 2B #3**).
6. **Fail-Closed Byzantine Quarantine Invariant (No Skip-on-Timeout):** If `ATS.INVAL` times out (`CERROR_ATC_INV_SYNC`, `DMA_FSTS_ITE`, or `cqcsr.cmd_to`), software must **never** skip the command and reclaim the page (**Probe 2B #4**), nor loop indefinitely on the command queue. Instead, software must atomically: (a) clear `EN_ATS`/`STE.EATS` (and `IODIR.INVAL_DDT` / `CFGI_STE`) to sever all `AT = 10b` paths at the IOMMU ingress; (b) trigger PCIe Function-Level Reset (`FLR`) or Secondary Bus Reset (`SBR`) / Root Port link disable; and (c) **permanently quarantine (leak)** the affected physical pages if hardware reset fails to confirm electrical isolation.

## Boundaries

- **Known not to apply:**
  - *`rdmatso` (`Ambal et al., OOPSLA 2024`) and `rdmawait_rmw` (`arXiv:2601.14642`):* Known not to apply unmodified to non-TSO host CPUs (e.g., ARMv8-A or RVWMO hosts, where intra-node `Read->Read` and `Write->Write` reorderings weaken the `aCR`/`aCW` rows of the `sto` matrix), nor to Unreliable Datagram (UD) or Dynamically Connected (DC) transports, nor to multi-QP reordering across distinct Queue Pairs.
  - *Linux `IOMMU_DOMAIN_DMA_FQ` (lazy flush queue):* Known not to provide temporal DMA isolation against untrusted or Byzantine peripherals (`drivers/iommu/dma-iommu.c:824-845`; **Probe 2B #1**).
  - *Remote RDMA `RCAS`/`RFAA` atomicity:* Known not to guarantee mutual exclusion against concurrent local CPU stores/CAS or remote `Put`s (`arXiv:2601.14642`, §2.3).
- **Unsupported:**
  - *RISC-V IOMMU v1.0 (`ac1589c7...`):* Explicitly does not allow caching of invalid (`V = 0`) PTEs/DDT/PDT entries (`src/iommu_sw_guidelines.adoc`), and supports command timeout **only** for `ATS.INVAL` (`src/iommu_in_memory_queues.adoc:360`).
  - *`TF-RMM/tf-rmm` (`8d7961df...`, `app/device_assignment/el0_app/src/dev_tdisp_cmds.c:70-75`):* Currently leaves platform-specific `lock_param` derivation as a `TODO` and masks out `PCI_TDISP_LOCK_INTERFACE_FLAGS_LOCK_MSIX`.
- **Not examined:**
  - *CXL.cache / CXL.mem (Compute Express Link 3.x) device coherence and `CXL.io` IDE security:* Distinct from PCIe-only DMA/RDMA models and not inspected at specification source level here.
  - *AMD-Vi (IOMMUv2) Linux driver (`drivers/iommu/amd/iommu.c`) and `SEV-TIO` firmware internals:* Architectural parallels to Intel VT-d / Arm CCA were verified at the overview level via public documentation, but AMD-Vi's `INVALIDATE_IOTLB_PAGES` / `COMPLETION_WAIT` timeout driver code was not line-audited.
  - *RDMA hardware litmus execution on live InfiniBand/RoCE NICs:* Probe 2A mechanizes the published declarative axioms (`Definition 3`) rather than executing hardware verbs over physical NICs; empirical hardware validation rests on Ambal et al. (OOPSLA 2024, 37 litmus tests) and Dan et al. (OOPSLA 2016).
- **Unknown:**
  - *Interaction of `rdmatso` with PCIe Relaxed Ordering (`IBV_ACCESS_RELAXED_ORDERING`) and GPUDirect RDMA peer-to-peer memory models:* Formalizing `rdmatso` when PCIe RO is selectively enabled per Memory Key (`MKey`) or when the target memory resides in a GPU (with PTX weak memory semantics) remains an open research problem not resolved by `arXiv:2601.14642`.
  - *Formal machine-checked proof of `TF-RMM` RME-DA + SMMUv3 + PCIe TDISP under Byzantine endpoint timeouts:* While `TF-RMM` includes CBMC harnesses (`runtime/rsi/fake_host/cbmc_vdev.c`) and Fox et al. (OOPSLA 2023) / Li et al. (OSDI 2022) verified base Arm CCA/RMM, a complete end-to-end mechanized proof covering live SMMUv3 `CMD_ATC_INV` timeout quarantine + PCIe `TDISP` teardown races has not been established in the examined artifacts.

## Evidence

### Primary Literature and Specifications
- **Ambal et al. (OOPSLA 2024):** Guillaume Ambal, Brijesh Dongol, Haggai Eran, Vasileios Klimis, Ori Lahav, Azalea Raad, *"Semantics of Remote Direct Memory Access: Operational and Declarative Models of RDMA on TSO Architectures"*, PACMPL 8(OOPSLA2), Article 341, 2024, DOI `10.1145/3689781` (`rdmatso` operational + declarative models, 37 hardware-validated litmus tests).
- **Ambal, Lahav & Raad (ESOP 2025):** *"Sufficient Conditions for Robustness of RDMA Programs"*, ESOP 2025, LNCS 15694, pp. 56–87, DOI `10.1007/978-3-031-91118-7_3` (SC robustness criteria and relaxed tree-topology conditions).
- **Ambal, Stupple, Dongol & Raad (2026):** *"Specifying and Verifying RDMA Synchronisation (Extended Version)"*, `arXiv:2601.14642` (full 4,283-line PDF inspected: §2.1 `rdmatso`/`rdmawait`/`Poll` vs `Wait`, Fig. 4 SB anomaly, §2.3 remote RMW non-atomicity against CPU/Put and `aNAR` vs `aNRR` Fig. 7, §3.1 Fig. 9 12×12 `sto` matrix, §3.2 Definition 3 `ib`/`so` consistency axioms).
- **Dan et al. (OOPSLA 2016):** Andrei Marian Dan, Patrick Lam, Torsten Hoefler, Martin T. Vechev, *"Modeling and Analysis of Remote Memory Access Programming"*, OOPSLA 2016, DOI `10.1145/2983990.2984033` (`coreRMA` axiomatic model and solver-generated litmus testing on Verbs/DMAPP/Portals 4).
- **Kalia, Andersen & Kaminsky (SoCC 2020):** *"Challenges and Solutions for Fast Remote Persistent Memory Access"*, ACM SoCC 2020, DOI `10.1145/3419111.3421294` (remote NVRAM persistency gap, InfiniBand Annex A19 `RDMA FLUSH`, DDIO effects).
- **Thunderclap (NDSS 2019):** A. Theodore Markettos, Colin Rothwell, Brett F. Gutstein, Allison Pearce, Peter G. Neumann, Simon W. Moore, Robert N. M. Watson, *"Thunderclap: Exploring Vulnerabilities in Operating System IOMMU Protection via DMA from Untrustworthy Peripherals"*, NDSS 2019, DOI `10.14722/ndss.2019.23194`; hardware platform `thunderclap-io/arria10-ubuntu-sdcard` @ `fb644b9313085ddded28e29b40021b46a02fa885`.
- **Verified Hypervisors & Confidential Computing:** Gerwin Klein et al., *"Comprehensive Formal Verification of an OS Microkernel"* (`seL4`), ACM TOCS 32(2), 2014, DOI `10.1145/2560537`; Luke Nelson et al., *"Hyperkernel: Push-Button Verification of an OS Kernel"*, SOSP 2017, DOI `10.1145/3132747.3132748`; Shih-Wei Li et al., *"A Secure and Formally Verified Linux KVM Hypervisor"* (`SeKVM`), IEEE S&P 2021, DOI `10.1109/SP40001.2021.00049`; Xupeng Li et al., *"Design and Verification of the Arm Confidential Compute Architecture"*, USENIX OSDI 2022; Anthony C. J. Fox et al., *"A Verification Methodology for the Arm Confidential Computing Architecture"*, PACMPL 7(OOPSLA1), 2023, DOI `10.1145/3586040`.

### Pinned Source Code Inspected (Observed 2026-11-19)
- **`riscv-non-isa/riscv-iommu`** @ `ac1589c79d72ff109b8df6cb24803390c5021c4b`:
  - `src/iommu_in_memory_queues.adoc:344-412` (out-of-order CQ execution, `IOFENCE.C` `PR`/`PW`/`AV`/`WSI`, `ATS.INVAL` sole-timeout note, PCIe read-completion drain requirement for upstream posted writes).
  - `src/iommu_sw_guidelines.adoc:123-260` (invalidations on DDT/PDT/MSI changes; mandatory `IOATC`-before-`DevATC` invalidation order).
  - `iommu_ref_model/libiommu/src/iommu_translate.c:140-195` (Step 7: `DC.tc.EN_ATS == 0` faults `ADDR_TYPE_TRANSLATED` with cause `260`; Step 8: `T2GPA == 0` bypasses page-table walk; Step 9: `T2GPA == 1` enforces G-stage translation).
  - `iommu_ref_model/libiommu/src/iommu_command_queue.c:85-178` & `iommu_ats.c:15-260` (`IOTINVAL`, `IODIR`, `IOFENCE_C`, `itag_tracker`, PRI queue overflow/fault handling).
- **`torvalds/linux`** @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:
  - `drivers/pci/ats.c:41-50` (`pci_ats_supported` rejecting `dev->untrusted`).
  - `drivers/iommu/dma-iommu.c:96-102` (`IOVA_DEFAULT_FQ_SIZE=256`, `IOVA_DEFAULT_FQ_TIMEOUT=10`, `IOVA_SINGLE_FQ_SIZE=32768`, `IOVA_SINGLE_FQ_TIMEOUT=1000`), `:592-629` (`dev_is_untrusted` forcing `swiotlb`), `:824-845` (`__iommu_dma_unmap` skipping `iommu_iotlb_sync` under `IOMMU_DOMAIN_DMA_FQ`), `:1254-1276` (`iommu_dma_unmap_phys`).
  - `drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c:330-385` (`__arm_smmu_cmdq_skip_err` returning on `CMDQ_ERR_CERROR_ATC_INV_IDX` to repeat `CMD_SYNC`), `:1323-1351` (`arm_smmu_get_ste_update_safe` forbidding transient `S2S=1 & EATS!=0` and `EATS=0b11`).
  - `drivers/iommu/intel/dmar.c:1390-1485` (`qi_check_fault` handling `DMA_FSTS_IQE`/`ITE`/`ICE`, `DMAR_IQER_REG_ITESID`, `pci_device_is_present` returning `-EAGAIN` vs `-ETIMEDOUT`), `:1575-1610` (`qi_submit_sync` `if (rc == -EAGAIN) goto restart;`).
- **`TF-RMM/tf-rmm`** @ `8d7961df074f08fd83a2460ab3a2ca0b658fde92`:
  - `lib/smmuv3/src/smmuv3_tlbi.c:16-95` (`smmuv3_cmd_sync_init`, `poll_cmd_sync_all` polling per-SMMU `SCA_READ32_ACQUIRE` completion words with timeout error reporting).
  - `app/device_assignment/el0_app/src/dev_tdisp_cmds.c:28-86, 164-248` (SPDM/TDISP state machine: `TDISP_GET_VERSION`, `TDISP_GET_CAPABILITIES`, `CONFIG_UNLOCKED` check, `TDISP_LOCK_INTERFACE_REQ`, Root Port `dvsec_tdisp_enable`, `TDISP_START_INTERFACE_REQ`, `TDISP_STOP_INTERFACE_REQ`).

### Executable Micro-Probes (Python 3 stdlib, Linux x86-64, 2026-11-19)

Running the self-contained model-checking script (`/tmp/probe_rdma_iommu.py`) produced the following exact output:

```text
=== Probe 2A: rdmatso / rdmawait_rmw Declarative Consistency Checker ===
  1. Put(z2,x); x:=1 -> z=1 (no Wait)        -> ib_cyclic=False, so_cyclic=False => ALLOWED
  2. Put_d(z2,x); Wait(d); x:=1 -> z=1       -> ib_cyclic=True , so_cyclic=True  => FORBIDDEN
  3. SB: Put+Wait vs Put+Wait -> (0,0)       -> ib_cyclic=False, so_cyclic=False => ALLOWED
  4. SB: Put+GFence(Get+Wait) -> (0,0)       -> ib_cyclic=False, so_cyclic=True  => FORBIDDEN
  5. LB: Get(x2); Put(y2,1) || r(y);w(x) -> (1,1) -> ib_cyclic=False, so_cyclic=False => ALLOWED
  6. LB: RCAS(x2); Put(y2,1) || r(y);w(x) -> (1,1) -> ib_cyclic=True , so_cyclic=True  => FORBIDDEN

=== Probe 2B: Exhaustive IOMMU + ATS Domain-Teardown Verification ===
  1. Lazy Flush Queue (IOMMU_DOMAIN_DMA_FQ)    | states=  3 | UNSAFE (4-step counterexample)
    Trace: INIT(byz=False) -> OS_CLEAR_PTE_AND_QUEUE_FQ -> OS_REALLOC_PAGE_BEFORE_FQ_FLUSH -> VIOLATION: in-flight posted DMA write lands on REALLOC_TENANT2 page
  2. Wrong Order (ATS.INVAL before IOTINVAL)   | states= 11 | UNSAFE (8-step counterexample)
    Trace: INIT(byz=False) -> OS_CLEAR_PTE -> OS_SEND_ATS_INVAL_BEFORE_IOTINVAL -> DEV_ACK_ATS_INVAL -> DEV_ATS_REFILL_FROM_IOATC_OR_PTE -> OS_IOTINVAL_AND_IOFENCE_DRAIN -> OS_REALLOC_PAGE -> VIOLATION: endpoint issues AT=10b Translated DMA via stale DevATC to REALLOC_TENANT2 page
  3. Missing IOFENCE(PR,PW) / PCIe Drain       | states=  6 | UNSAFE (7-step counterexample)
    Trace: INIT(byz=False) -> OS_CLEAR_PTE -> OS_IOTINVAL_SYNC -> OS_SEND_ATS_INVAL -> DEV_ACK_ATS_INVAL -> OS_REALLOC_WITHOUT_DRAIN -> VIOLATION: in-flight posted DMA write lands on REALLOC_TENANT2 page
  4. Byzantine ATS Timeout + Skip-on-Error     | states=  4 | UNSAFE (5-step counterexample)
    Trace: INIT(byz=True) -> OS_CLEAR_PTE_AND_IOTINVAL -> OS_SEND_ATS_INVAL -> OS_TIMEOUT_SKIP_AND_REALLOC -> VIOLATION: in-flight posted DMA write lands on REALLOC_TENANT2 page
  5. Verified Strict + Byzantine Quarantine    | states= 13 | SAFE (0 violations)
```

Self-contained reproduction script (`/tmp/probe_rdma_iommu.py`):

```python
#!/usr/bin/env python3
from collections import deque

def has_cycle(nodes, edges):
    adj = {u: [] for u in nodes}
    for u, v in edges: adj[u].append(v)
    c = {u: 0 for u in nodes}
    def dfs(u):
        c[u] = 1
        for v in adj[u]:
            if c[v] == 1 or (c[v] == 0 and dfs(v)): return True
        c[u] = 2; return False
    return any(c[u] == 0 and dfs(u) for u in nodes)

def check_litmus(name, V, inst, ippo, iso, rf, rfe, rb, pfg, pfp, nfo):
    ib_e = set(ippo)|set(iso)|set(rf)|set(pfg)|set(pfp)|set(nfo)
    ib_c = has_cycle(V, ib_e)
    adj = {u: set() for u in V}
    for u, v in ib_e: adj[u].add(v)
    tc = set()
    for s in V:
        vis, st = set(), list(adj[s])
        while st:
            x = st.pop()
            if x not in vis: vis.add(x); tc.add((s, x)); st.extend(adj[x])
    so_e = set(iso)|set(rfe)|set(pfg)|set(nfo)|set(rb)|{(u, v) for (u, v) in tc if u in inst}
    so_c = has_cycle(V, so_e)
    print(f"{name}: ib_cyc={ib_c} so_cyc={so_c} => {'ALLOWED' if not (ib_c or so_c) else 'FORBIDDEN'}")

def explore_teardown(mode):
    byz_vals = [True] if mode == "byz_skip" else ([False, True] if mode == "verified" else [False])
    inits = [("DEV", True, True, True, True, True, False, b, False, 0) for b in byz_vals]
    q, vis = deque([(s, [f"INIT(byz={s[7]})"]) for s in inits]), set(inits)
    while q:
        st, tr = q.popleft()
        own, pte, ioatc, datc, ats, inf, pend, byz, rst, k = st
        if own == "T2" and (inf or (ats and datc) or ioatc or pte):
            print(f"{mode}: UNSAFE ({len(vis)} states): {' -> '.join(tr)}"); return
        nx = []
        if not rst:
            if ats and (ioatc or pte) and not datc:
                nx.append(("REFILL", (own, pte, ioatc, True, ats, inf, pend, byz, rst, k)))
            if not inf and (pte or ioatc or (ats and datc)):
                nx.append(("DMA", (own, pte, ioatc, datc, ats, True, pend, byz, rst, k)))
            if pend and not byz:
                nx.append(("ACK", (own, pte, ioatc, False, ats, inf, False, byz, rst, k)))
        if mode == "lazy_fq":
            if k == 0: nx.append(("CLR_FQ", (own, False, ioatc, datc, ats, inf, pend, byz, rst, 1)))
            elif k == 1: nx.append(("REALLOC", ("T2", pte, ioatc, datc, ats, inf, pend, byz, rst, 2)))
        elif mode == "wrong_order":
            if k == 0: nx.append(("CLR", (own, False, ioatc, datc, ats, inf, pend, byz, rst, 1)))
            elif k == 1: nx.append(("ATS_INV", (own, pte, ioatc, datc, ats, inf, True, byz, rst, 2)))
            elif k == 2 and not pend: nx.append(("IOT_DRAIN", (own, pte, False, datc, ats, False, False, byz, rst, 3)))
            elif k == 3: nx.append(("REALLOC", ("T2", pte, ioatc, datc, ats, inf, pend, byz, rst, 4)))
        elif mode == "no_drain":
            if k == 0: nx.append(("CLR", (own, False, ioatc, datc, ats, inf, pend, byz, rst, 1)))
            elif k == 1: nx.append(("IOT", (own, pte, False, datc, ats, inf, pend, byz, rst, 2)))
            elif k == 2: nx.append(("ATS_INV", (own, pte, ioatc, datc, ats, inf, True, byz, rst, 3)))
            elif k == 3 and not pend: nx.append(("REALLOC", ("T2", pte, ioatc, datc, ats, inf, pend, byz, rst, 4)))
        elif mode == "byz_skip":
            if k == 0: nx.append(("CLR_IOT", (own, False, False, datc, ats, inf, pend, byz, rst, 1)))
            elif k == 1: nx.append(("ATS_INV", (own, pte, ioatc, datc, ats, inf, True, byz, rst, 2)))
            elif k == 2 and pend and byz: nx.append(("SKIP_REALLOC", ("T2", pte, ioatc, datc, ats, inf, False, byz, rst, 3)))
        elif mode == "verified":
            if k == 0: nx.append(("CLR", (own, False, ioatc, datc, ats, inf, pend, byz, rst, 1)))
            elif k == 1: nx.append(("IOT", (own, pte, False, datc, ats, inf, pend, byz, rst, 2)))
            elif k == 2: nx.append(("ATS_INV", (own, pte, ioatc, datc, ats, inf, True, byz, rst, 3)))
            elif k == 3 and not pend: nx.append(("DRAIN", (own, pte, ioatc, datc, ats, False, False, byz, rst, 4)))
            elif k == 3 and pend and byz: nx.append(("QUARANTINE", (own, False, False, False, False, False, False, byz, True, 4)))
            elif k == 4: nx.append(("REALLOC", ("T2", pte, ioatc, datc, ats, inf, pend, byz, rst, 5)))
        for lbl, nst in nx:
            if nst not in vis: vis.add(nst); q.append((nst, tr + [lbl]))
    print(f"{mode}: SAFE ({len(vis)} states, 0 violations)")

if __name__ == "__main__":
    check_litmus("1. Put(z2,x);x:=1 (no Wait)", ["e1l","e1w","e2w"], {"e1l"}, [],
                 [("e1l","e1w")], [("e2w","e1l")], [("e2w","e1l")], [], [], [], [])
    check_litmus("2. Put_d;Wait(d);x:=1", ["e1l","e1w","wt","e2w"], {"e1l","wt"}, [("wt","e2w")],
                 [("e1l","e1w")], [("e2w","e1l")], [("e2w","e1l")], [], [], [("e1w","wt")], [])
    check_litmus("3. SB(Put+Wait)", ["p1l","p1w","w1","r1","p2l","p2w","w2","r2"],
                 {"p1l","w1","r1","p2l","w2","r2"}, [("w1","r1"),("w2","r2")],
                 [("p1l","p1w"),("p2l","p2w")], [], [], [("r1","p2w"),("r2","p1w")], [], [("p1w","w1"),("p2w","w2")], [])
    check_litmus("4. SB(Put+GFence)", ["p1l","p1w","g1r","g1l","w1","r1","p2l","p2w","g2r","g2l","w2","r2"],
                 {"p1l","g1r","w1","r1","p2l","g2r","w2","r2"}, [("w1","r1"),("w2","r2")],
                 [("p1l","p1w"),("g1r","g1l"),("p2l","p2w"),("g2r","g2l")], [], [],
                 [("r1","p2w"),("r2","p1w")], [("g1l","w1"),("g2l","w2")],
                 [("p1w","w1"),("p2w","w2")], [("p1w","g1r"),("p2w","g2r")])
    check_litmus("5. LB(Get;Put)", ["gnr","gnl","pnl","pnw","ry","wx"],
                 {"gnr","pnl","ry"}, [("ry","wx")], [("gnr","gnl"),("pnl","pnw")],
                 [("pnw","ry"),("wx","gnr")], [("pnw","ry"),("wx","gnr")], [], [], [], [])
    check_litmus("6. LB(RCAS;Put)", ["gna","gnl","pnl","pnw","ry","wx"],
                 {"gna","pnl","ry"}, [("gna","pnw"),("ry","wx")], [("gna","gnl"),("pnl","pnw")],
                 [("pnw","ry"),("wx","gna")], [("pnw","ry"),("wx","gna")], [], [], [], [])
    for m in ("lazy_fq", "wrong_order", "no_drain", "byz_skip", "verified"):
        explore_teardown(m)
```

## Revalidation

To cheaply revalidate these findings against newer Linux kernels, RISC-V IOMMU / Arm SMMUv3 / Intel VT-d revisions, or RDMA libraries:

1. **Linux IOMMU & PCIe ATS Regression Checks (`torvalds/linux`):**
   - Diff `drivers/pci/ats.c` (`pci_ats_supported`) and `drivers/iommu/dma-iommu.c` (`dev_is_untrusted`, `dev_use_swiotlb`, `__iommu_dma_unmap`) to verify whether external untrusted devices remain excluded from ATS and `IOMMU_DOMAIN_DMA_FQ` and bounced through SWIOTLB.
   - Diff `drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c` (`__arm_smmu_cmdq_skip_err`, `CERROR_ATC_INV_IDX`) and `drivers/iommu/intel/dmar.c` (`qi_check_fault`, `DMA_FSTS_ITE`, `qi_submit_sync`) to check whether upstream Linux has replaced retry/livelock loops on ATS invalidation timeouts with explicit device quarantine (`pci_reset_function` + clearing `STE.EATS`/`DTE`).
2. **RISC-V IOMMU & TF-RMM Specification Checks:**
   - Diff `riscv-non-isa/riscv-iommu` (`iommu_ref_model/libiommu/src/iommu_translate.c` Steps 7–9 and `src/iommu_sw_guidelines.adoc`) to verify `DC.tc.EN_ATS` / `DC.tc.T2GPA` enforcement and `IOATC`-before-`DevATC` invalidation rules.
   - Diff `TF-RMM/tf-rmm` (`app/device_assignment/el0_app/src/dev_tdisp_cmds.c` and `lib/smmuv3/src/smmuv3_tlbi.c`) to track whether `PCI_TDISP_LOCK_INTERFACE` MSI-X locking and SMMUv3 ATC invalidation timeout quarantine have been completed and formally checked under `cbmc_vdev.c`.
3. **RDMA Weak-Memory & Teardown Model Re-Execution:**
   - Run `/tmp/probe_rdma_iommu.py` (`python3`, `<0.1s`) after modifying the `sto` matrix (e.g., to add ARMv8 host CPU relaxations or new RDMA verb stamps such as `RDMA FLUSH`) or extending the IOMMU teardown state machine (e.g., adding concurrent PASID teardown or PCIe `PRI` page-request drain) to check whether any new cycle or UAF counterexample becomes reachable.
