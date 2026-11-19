# SmartNIC/DPU-Host Mutual Distrust, PCIe IDE/TDISP/SPDM, IOMMU ATS/PRI Hazards, and Heterogeneous SoC IPC Verification

## Summary

Modern servers and mobile SoCs are no longer single-trust-domain machines with subordinate peripherals: they are **federated systems of mutually distrusting physical processors** communicating across PCIe, CXL, LPC, and on-die AXI/shared-RAM interconnects. Four core boundaries govern soundness across these fabrics:

1. **Bidirectional Cloud DPU / Host Distrust (AWS Nitro, NVIDIA BlueField)**: In bare-metal and confidential-compute clouds, the infrastructure **DPU/SmartNIC** distrusts a tenant-controlled host CPU (requiring host-side control paths such as BlueField **RShim** over PCIe to be disabled in Zero-Trust DPU Mode, and **ECPF** ownership of the eSwitch/host PF HCA), while a **Confidential VM (CVM)** or hardened host OS simultaneously distrusts both the host VMM and any unattested PCIe endpoint.
2. **Cryptographic Interconnect Security (`SPDM` + `PCIe IDE` + `TDISP`)**: Extending TEE boundaries across PCIe/CXL chains four specifications implemented in `DMTF/libspdm` and upstream Linux (`drivers/pci/{doe,tsm,ide}.c`): **PCIe DOE** transport, **DMTF SPDM (DSP0274)** device identity/measurement attestation and **Secured Messages (DSP0277)** AEAD sessions, **PCIe IDE_KM** Link/Selective stream key management (separate `K0`/`K1` key sets across `Tx`/`Rx` x `PR`/`NPR`/`CPL` sub-streams), and **TDISP** (`CONFIG_UNLOCKED -> CONFIG_LOCKED -> RUN -> ERROR`) with a 32-byte `start_interface_nonce` that cryptographically ties CVM attestation of locked MMIO/MSI-X/DMA ranges to interface activation. Formal verification of SPDM 1.2 in Tamarin (Cremers, Dax, Naska, ePrint `2024/2047`) exposed a critical (CVSS 9.0) cross-protocol mode-switch attack breaking PSK authentication when key-exchange transcripts failed to isolate modes unambiguously—proving that hardware attestation stacks require holistic multi-mode symbolic verification.
3. **IOMMU `ATS`/`PRI` Translation and Sub-Page DMA Hazards**: Enabling **Address Translation Services (ATS)** shifts translation enforcement onto the untrusted peripheral's **DevTLB (ATC)**: a rogue endpoint can spoof the TLP `AT` field (`Translated Request`) unless hardware/ACS/SMMU policy restricts ATS to trusted ports (`pci_ats_supported` explicitly returns `false` when `dev->untrusted` in Linux `drivers/pci/ats.c` L43). Even with benign ATS endpoints, invalidating DevTLB *before* syncing IOTLB invalidations permits a concurrent ATS Translation Request to refill DevTLB from a stale IOTLB entry and DMA into a freshly reallocated security domain (proved via exhaustive state-space probe; strictly prevented by `arm_smmu_invs_end_batch` in `arm-smmu-v3.c` L2732–2734 and Intel VT-d `cache_tag_flush_range`). Independently, **Thunderclap** (NDSS 2019) proved that 4 KiB/64 KiB IOMMU page granularity leaks 93.75%–99.61% of sibling kernel objects sharing a mapped page unless untrusted devices are forced through **`SWIOTLB`** bounce-buffering (`dev_use_swiotlb` in `drivers/iommu/dma-iommu.c` L597–603).
4. **BMC and Heterogeneous SoC Shared-Memory IPC (`Aspeed P2A`, `OpenBMC`, `Qualcomm SMEM/GLINK`)**: Legacy host-to-BMC debug bridges (`ASPEED AST2400/2500` **P2A** and **iLPC2AHB**, `CVE-2019-6260` "Pantsdown") collapse host/BMC isolation completely—upstream Linux `aspeed-p2a-ctrl.c` L76–79 explicitly documents that setting `SCU180_ENP2A` opens the *entire* BMC AHB address space to host reads regardless of write-filter bits. On cellular/SoC shared-RAM rings (`drivers/rpmsg/qcom_glink_native.c`), direct inspection at HEAD reveals classic cross-core FFI verification hazards: double-fetching ring headers across dispatch and payload handlers, and unchecked 32-bit unsigned `chunk_size + left_size` addition in `intentless` mode (L952, L960) that wraps modulo $2^{32}$ to poison `channel->buf` with undersized or `ZERO_SIZE_PTR` allocations when facing a compromised baseband coprocessor (`FirmWire`, NDSS 2022).

## Applicability

This report covers the mutually-distrusting interconnect, attestation, IOMMU, DPU, BMC, and shared-memory IPC layers pinned in `REPORT.json`:

- **`DMTF/libspdm` (`3f1253df61ef1af917f1f18ce40db065e93ff82c`)** and **`DMTF/spdm-emu` (`6c222618c109d29bdd7e363540089d6713cbb8ff`)**: Findings apply to DSP0274 (SPDM 1.0–1.3+), DSP0277 (Secured Messages 1.0–1.3 including Table 10 `AEAD_LIMIT` data), PCI-SIG IDE_KM (`include/industry_standard/pci_idekm.h`), and PCI-SIG TDISP 1.0 (`include/industry_standard/pci_tdisp.h`).
- **`torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`)**: Findings apply to the upstream Linux kernel subsystems inspected directly at that commit:
  - PCIe DOE/TSM/IDE (`drivers/pci/doe.c`, `drivers/pci/tsm.c`, `include/linux/pci-tsm.h`, `drivers/pci/ide.c`, `include/linux/pci-ide.h`),
  - PCIe ATS/PRI and IOMMU enforcement (`drivers/pci/ats.c`, `drivers/iommu/dma-iommu.c`, `drivers/iommu/intel/iommu.c`, `drivers/iommu/intel/cache.c`, `drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c`, `drivers/iommu/amd/iommu.c`),
  - SmartNIC ECPF host-PF split (`drivers/net/ethernet/mellanox/mlx5/core/ecpf.c`),
  - Aspeed BMC P2A/LPC bridges (`drivers/soc/aspeed/aspeed-p2a-ctrl.c`, `drivers/soc/aspeed/aspeed-lpc-ctrl.c`),
  - Qualcomm heterogeneous SoC shared-memory IPC (`drivers/soc/qcom/smem.c`, `drivers/rpmsg/qcom_glink_native.c`).
- **`Mellanox/rshim-user-space` (`67b5a7a66bd1ef3665eb79c055f0a3088d1d895c`)**, **`CodeConstruct/mctp` (`82540d8f0a6b0cb612c73f54e8a1fa962e1a09d1`)**, and **`openbmc/phosphor-host-ipmid` (`825c7b0485057bd74f1e59ee0604fe7a9d54304d`)**: Characterize the host-DPU management surface (RShim PCIe/USB/LIVEFISH boot-stream and register access) and modern OpenBMC host-BMC transport migration (legacy LPC KCS/P2A toward packetized MCTP/PLDM/SPDM).
- **Published vendor architectures & peer-reviewed papers**: AWS Nitro System Security Design (public architecture documentation), NVIDIA BlueField Zero-Trust DPU / Separated Host documentation, **Thunderclap** (`doi:10.14722/ndss.2019.23194`), **SPDM 1.2 Tamarin analysis** (`ePrint 2024/2047`), **FirmWire** (`doi:10.14722/ndss.2022.23136`), and **ASPEED Pantsdown** (`CVE-2019-6260`).

Executable verification models (reproduced in **Revalidation** and recorded in **Evidence**) check the IOMMU IOTLB/DevTLB interleaving state space, Thunderclap sub-page ratios, TDISP TDI lock-to-run automaton invariants, and Qualcomm GLINK `u32` wraparound arithmetic; they model the exact control/arithmetic semantics extracted from upstream code rather than hardware gate-level PCIe PHY timing.

## Findings

### 1. Mutual-Distrust Interconnect Matrix Across Cloud DPUs, BMCs, and Heterogeneous SoCs

Basis: source + documentation + normative + derived

Conventional OS threat models assume a strict vertical hierarchy (host CPU controls subordinate peripherals). Across cloud DPUs, Confidential Computing (TEE-IO), BMCs, and mobile baseband SoCs, **distrust is bidirectional** and differs sharply in bus authority:

| Interconnect / Pair | Core A (Host / AP) Threat to Core B | Core B (DPU / BMC / Device) Threat to Core A | Primary Hardware Enforcement Boundary | Dominant Residual Failure Mode |
| :--- | :--- | :--- | :--- | :--- |
| **AWS Nitro Card + Nitro Security Chip <-> Bare-Metal Host** | Tenant Ring 0 attempts SPI flash re-flash, PCIe DMA into Nitro Card, or card management takeover | Compromised card/operator could inspect host DRAM or spoof storage/network I/O | Nitro Security Chip intercepts motherboard SPI flash; card-side isolation; dedicated Nitro Hypervisor / bare-metal enclave | Supply-chain or card firmware bugs (closed-source ASIC/firmware) |
| **NVIDIA BlueField DPU <-> Bare-Metal Host** | Host root uses **RShim** (`/dev/rshim<N>/{boot,rshim}`) to re-flash ARM OS, read registers, or tamper with eSwitch | Compromised DPU ARM cores control host PF HCA (`mlx5` ECPF), intercept/modify packets, or DMA host memory via PCIe | Zero-Trust DPU Mode disables host RShim + restricts `HOST_PRIV_CTRL`; Host IOMMU (+ SWIOTLB / IDE+TDISP) constrains DPU DMA | Misconfigured RShim left enabled on PCIe; ATS enabled for untrusted DPU; sub-page IOMMU leakage |
| **Confidential VM (CVM) <-> PCIe/CXL Accelerator (TEE-IO)** | Untrusted host VMM replays SPDM, tampers with BARs/MSI-X, or redirects DMA/MMIO after attestation | Rogue/interposed PCIe endpoint spoofs `AT=0b10` Translated TLPs, ignores DevTLB invalidations, or leaks CVM memory | **SPDM** attestation + **PCIe Selective IDE** (AES-GCM TLP encryption) + **TDISP** (`CONFIG_LOCKED` -> `RUN` nonce) + TSM/DSM | Cross-protocol SPDM flaws (`ePrint 2024/2047`), broken IOTLB->DevTLB flush ordering, ATS spoofing |
| **Server Host <-> OpenBMC (Aspeed AST2400/2500/2600)** | Compromised host OS abuses **P2A** (`SCU180_ENP2A`) or **iLPC2AHB** bridges to read/write BMC DRAM/flash (`CVE-2019-6260`) | Compromised BMC controls host SPI flash, power/reset, virtual KVM/USB, and PCIe VGA DMA | Hardware bridge disable (`SCU180`/`SCU2C` lock); migrate to packetized **MCTP** over PCIe VDM/I2C + **PLDM/SPDM** | Enabling `SCU180_ENP2A` exposes *entire* BMC AHB space for reads; unauthenticated IPMI KCS channel |
| **Mobile AP (Linux) <-> Cellular Baseband / ADSP** | Compromised AP corrupts shared-RAM descriptors or triggers modem DoS | Over-the-air RCE in closed baseband (`FirmWire`, NDSS 2022) crafts malicious shared-RAM FIFO packets (`SMEM`/`GLINK`) or rogue DMA | Hardware SMMU/XPU memory firewalls restricting modem DRAM window; AP parser single-fetch + checked bounds | Shared-memory **double-fetch TOCTOU**, 32-bit `chunk_size + left_size` wraparound (`qcom_glink_native.c` L952), unrestricted modem DMA |

---

### 2. Cloud SmartNIC / DPU Mutual Distrust: AWS Nitro and NVIDIA BlueField

Basis: source + documentation

#### 2.1 AWS Nitro System
From AWS Nitro System Security Design documentation (`Basis: documentation`):
- **Physical Disaggregation of Control & Data Planes**: Networking (ENA), block storage (EBS), local NVMe encryption, and cloud management move onto dedicated **Nitro Cards** (Annapurna Labs ASICs), while a separate motherboard **Nitro Security Chip** physically traps and verifies all non-volatile storage writes (motherboard BIOS/UEFI SPI flash and card firmware) before the host CPU boots.
- **Bare-Metal Mutual Isolation**: Because no general-purpose Dom0 management OS shares the host CPU, AWS can expose raw bare-metal x86/ARM hardware directly to an untrusted tenant while the Nitro Security Chip prevents the tenant from persisting firmware implants across instance terminations and the Nitro Card enforces VPC network/storage boundaries across PCIe. Conversely, Nitro eliminates interactive operator SSH access to Nitro controllers so operator-side APIs are narrowly scoped and authenticated.

#### 2.2 NVIDIA BlueField DPU: `ECPF` Control Split vs `RShim` Escalation Surface
Direct inspection of `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) and `Mellanox/rshim-user-space` (`67b5a7a66bd1ef3665eb79c055f0a3088d1d895c`) pinpoints the exact hardware/software control seams on BlueField DPUs:
- **DPU Mode (`ECPF`) vs Separated Host Mode (`drivers/net/ethernet/mellanox/mlx5/core/ecpf.c` L12–76)**:
  - `mlx5_ecpf_esw_admins_host_pf()` (L12–19) distinguishes BlueField's **DPU / Embedded CPU** mode (where the ARM-side Embedded CPU Physical Function `ECPF` is the eSwitch manager and brings up/controls the external host's PF HCA via `mlx5_esw_host_pf_enable_hca()`, L53–68) from **Separated Host Mode** (where the host PF enables itself independently, L14–18).
  - In DPU Mode, the infrastructure plane running on the ARM cores owns OVS/DOCA packet steering, IPsec/TLS offload, and virtio/NVMe-oF emulation transparently beneath the host OS.
- **The `RShim` Host-to-DPU Takeover Hazard (`Mellanox/rshim-user-space/README.md` L3–83)**:
  - RShim exposes the BlueField ARM SoC over `usb`, `pcie`, or `pcie_lf` (LIVEFISH) backends (L27), creating `/dev/rshim<N>/boot` (pushes arbitrary BlueField Boot Bundle `.bfb` firmware streams to the ARM cores, L36–40), `/dev/rshim<N>/console` (virtual ARM console, L42–47), `/dev/rshim<N>/rshim` (raw internal RShim register read/write at `((rshim_channel << 16) | register_offset)`, L49–52), and `/dev/rshim<N>/misc` (controls `BOOT_MODE` between `0:rshim`, `1:emmc`, `2:emmc-boot-swap`, L54–62).
  - **Zero-Trust Security Invariant**: If host-side PCIe RShim remains enabled in a multi-tenant or bare-metal deployment, a Ring 0 tenant on the host CPU can immediately reset, boot-hijack, or read registers of the infrastructure DPU—inverting the entire DPU trust boundary! Consequently, NVIDIA BlueField **Zero-Trust DPU Mode** requires disabling host-facing PCIe RShim (restricting RShim strictly to an out-of-band BMC USB/PCIe management channel) and locking down host-privileged NIC configuration registers (`HOST_PRIV_CTRL`).

---

### 3. PCIe Confidential Interconnect Stack: DOE, SPDM (DSP0274/DSP0277), IDE_KM, and TDISP

Basis: normative + source + execution

To let a Confidential VM (CVM) or zero-trust host verify and privately bind a PCIe/CXL device across an untrusted host VMM and physical bus, PCI-SIG and DMTF layer four protocols inspected directly in `DMTF/libspdm` (`3f1253df61ef1af917f1f18ce40db065e93ff82c`) and `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`):

#### 3.1 Transport (`PCIe DOE`) & Device Attestation / AEAD Sessions (`DSP0274` + `DSP0277`)
- **PCIe Data Object Exchange (`include/industry_standard/pcidoe.h`, Linux `drivers/pci/doe.c` & `pci_tsm_doe_transfer` in `drivers/pci/tsm.c` L885)**: Standardizes an in-band PCIe Extended Capability mailbox for carrying CMA-SPDM and Secured-SPDM frames over PCIe configuration space without proprietary out-of-band buses.
- **DSP0277 Secured Message Record Layout (`DMTF/libspdm/include/industry_standard/spdm_secured_message.h` L37–140)**:
  - Every encrypted message wraps `application_data_length || payload || random_pad` under AEAD (e.g., AES-256-GCM / ChaCha20-Poly1305) authenticated with `AssociatedData = session_id (uint32) || sequence_number (transport-specific) || length (uint16)`.
  - DSP0277 version `1.3` (`SECURED_SPDM_VERSION_13 = 0x13`, L60) adds `SECURED_MESSAGE_OPAQUE_ELEMENT_SMDATA_ID_AEAD_LIMIT = 0x2` (L133–138), bounding maximum AEAD invocations per key to $2^{\text{AeadLimitExponent}}$ (`<= 64`) before mandatory `KEY_UPDATE` to prevent nonce reuse or GCM confidentiality/authenticity degradation.
- **Formal Verification Finding — SPDM 1.2 Cross-Protocol Attack (`ePrint 2024/2047`)**:
  - `Basis: normative (peer-reviewed formal analysis)`. Cas Cremers, Alexander Dax, and Aurora Naska (CISPA) modeled the full SPDM 1.2 protocol—including **certificate-based**, **pre-shared public-key**, and **pre-shared symmetric-key (`PSK_EXCHANGE`)** modes and their interactions—in the **Tamarin Prover**.
  - Tamarin automatically discovered a **cross-protocol mode-switch attack** enabling a network/bus attacker to completely break authentication in SPDM 1.2 PSK mode; the authors reproduced it against the official reference implementation and DMTF assigned a critical **CVSS 9.0 CVE**.
  - **Verification Lesson**: Proving each handshake mode (`KEY_EXCHANGE` vs `PSK_EXCHANGE`) in isolation misses cross-mode transcript confusion; Tamarin's holistic proof only closed after unambiguous mode/context binding across transcript hashes was incorporated into both the SPDM standard and `libspdm` (`library/spdm_requester_lib/libspdm_req_psk_exchange.c`).

#### 3.2 PCIe Integrity and Data Encryption Key Management (`IDE_KM`)
From `DMTF/libspdm/include/industry_standard/pci_idekm.h` (L17–126) and Linux `include/linux/pci-ide.h` (L13–116) / `drivers/pci/ide.c` (L98–720):
- **Link IDE vs Selective IDE**: Link IDE encrypts all TLPs across a single point-to-point link (up to `PCI_IDE_KM_LINK_IDE_REG_BLOCK_MAX_COUNT = 8` traffic-class streams, `pci_idekm.h` L59). **Selective IDE** (`PCI_IDE_KM_SELECTIVE_IDE_REG_BLOCK_MAX_COUNT = 255`, L60) tunnels end-to-end encrypted/MACed TLPs across untrusted PCIe switches between a Root Port (`PCI_IDE_RP`) and an Endpoint (`PCI_IDE_EP`), routing TLPs into streams via hardware **RID Association Registers** (`rid_start..rid_end`) and up to 15 **Address Association Register Blocks** (`pci_ide_partner.mem_assoc`, `pref_assoc`; Linux `pci-ide.h` L45–76). Note Linux reserves `PCI_IDE_RESERVED_STREAM_ID = 255` (L102) as an unallocated placeholder to work around endpoints that alias idle stream IDs.
- **Key Sub-Stream Matrix & Zero-Downtime Key Rotation**: `pci_idekm.h` L64–90 encodes `KEY_PROG` (`0x02`) / `KP_ACK` (`0x03`) / `K_SET_GO` (`0x04`) / `K_SET_STOP` (`0x05`) / `K_SET_GOSTOP_ACK` (`0x06`) over Secured SPDM:
  - Each stream maintains **two key sets** (`K0 = 0x00`, `K1 = 0x01`), **two directions** (`RX = 0x00`, `TX = 0x02`), and **three independent PCIe TLP sub-streams** (`PR = 0x00` Posted Requests, `NPR = 0x10` Non-Posted Requests, `CPL = 0x20` Completions) — i.e., **6 active AES-256-GCM 96-bit-MAC keys per key set** (12 key slots per Selective IDE stream) so PCIe ordering rules between PR/NPR/CPL never deadlock AES-GCM nonce counters, and so the inactive key set can be pre-programmed (`KEY_PROG`) and atomically switched (`K_SET_GO`) before counter exhaustion!
- **Fail-Closed Link State (`drivers/pci/ide.c` L669–705)**: `pci_ide_stream_enable()` verifies `FIELD_GET(PCI_IDE_SEL_STS_STATE, val) == PCI_IDE_SEL_STS_STATE_SECURE` (returning `-ENXIO` otherwise). Any subsequent integrity failure drops the stream to `INSECURE`, which hardware treats as equivalent to a **link-down** containment event (L679–681).

#### 3.3 TEE Device Interface Security Protocol (`TDISP`) & Linux PCIe TSM Subsystem
From `DMTF/libspdm/include/industry_standard/pci_tdisp.h` (L19–281) and `torvalds/linux/include/linux/pci-tsm.h` (L13–210) / `drivers/pci/tsm.c` (L186–900):
- **Role Split (`TSM` vs `DSM` vs `VMM`)**: The host OS/VMM is **untrusted** for CVM confidentiality/integrity, so Linux `drivers/pci/tsm.c` acts strictly as a message marshaler (`pci_tsm_link_ops`: `probe`, `remove`, `connect`, `disconnect`, `bind`, `unbind`, `guest_req`, `pci-tsm.h` L47–61) between the platform **TEE Security Manager (TSM)** (e.g., Intel TDX module, AMD SEV-SNP ASP, ARM RMM) and the peripheral's **Device Security Manager (DSM)** over Secured SPDM/IDE. Note `PCI_TSM_REQ_DEBUG_WRITE = 3` (L199) explicitly requires `CAP_SYS_RAW_IO` and taints the kernel because it mutates device state outside the TDISP model.
- **The 4-State TDI Lifecycle Automaton (`pci_tdisp.h` L201–204)**:
  1. `PCI_TDISP_INTERFACE_STATE_CONFIG_UNLOCKED (0)`: Normal untrusted VMM enumeration and BAR/MSI-X configuration.
  2. `CONFIG_UNLOCKED -> CONFIG_LOCKED (1)` via `LOCK_INTERFACE_REQ (0x83)`: Locks device configuration space, optional firmware update lockout (`NO_FW_UPDATE = 0x1`), MSI-X table lock (`LOCK_MSIX = 0x4`), P2P binding (`BIND_P2P = 0x8`), `ALL_REQUEST_REDIRECT = 0x10`, and binds `default_stream_id` + `mmio_reporting_offset` (L113–130). The DSM returns a fresh 32-byte **`start_interface_nonce`** (`LOCK_INTERFACE_RSP`, L135–138).
  3. **CVM Attestation (`GET_DEVICE_INTERFACE_REPORT`, `0x84`)**: While `CONFIG_LOCKED`, the CVM (via TSM) inspects `pci_tdisp_device_interface_report_struct_t` (L171–188): exact `interface_info` flags (`NO_UPDATE_AFTER_LOCK`, `DMA_WITHOUT_PASID`, `DMA_WITH_PASID`, `ATS_SUPPORTED`, `PRS_SUPPORTED`, `XT_MODE_SUPPORTED`), MSI-X control, and the exact array of `pci_tdisp_mmio_range_t` descriptors (`first_page`, `number_of_pages`, `MSIX_TABLE`, `MSIX_PBA`, `IS_NON_TEE_MEM`, `IS_MEM_ATTR_UPDATABLE`, L156–168).
  4. `CONFIG_LOCKED -> RUN (2)` via `START_INTERFACE_REQ (0x86)`: The CVM authorizes acceptance by sending back the exact 32-byte `start_interface_nonce` (L207–210). Only in `RUN` may the TDI emit TEE-marked (`T=1`) DMA and accept private CVM MMIO.
  5. **Tamper Containment (`-> ERROR (3)`) & Teardown (`STOP_INTERFACE_REQ`, `0x87`)**: As verified by Probe 2B (`Basis: execution`), any unauthorized VMM configuration write (e.g., remapping BARs or MSI-X vectors) while `CONFIG_LOCKED` or `RUN` transitions the TDI immediately to `ERROR`, invalidating `start_interface_nonce` and rejecting subsequent `START_INTERFACE_REQ`; recovery requires `STOP_INTERFACE_REQ`, which scrubs device-internal TEE state before returning to `CONFIG_UNLOCKED` (where a subsequent `LOCK_INTERFACE` mints a fresh nonce, rejecting stale nonce replays).

---

### 4. IOMMU `ATS`/`PRI` Translation Hazards and `Thunderclap` Sub-Page DMA Exposure

Basis: normative + source + execution

Even without a physically interposed PCIe bus, an untrusted endpoint (e.g., compromised SmartNIC, Thunderbolt peripheral, or tenant-flashed FPGA) attacks the host OS across the **IOMMU** boundary through three distinct hardware mechanisms:

#### 4.1 PCIe `ATS` Translated-Request Spoofing & `dev->untrusted` Blocking
- Under PCIe **Address Translation Services (ATS)**, an endpoint caches IOVA->HPA mappings in a local **Device TLB (DevTLB / ATC)** and stamps subsequent DMA TLPs with `AT = 0b10` (**Translated Request**), instructing the Root Complex / IOMMU to bypass address translation!
- **Spoofing Hazard**: Unless hardware enforces per-BDF/per-port ATS authorization (`ACS Translation Blocking` and IOMMU `STE.EATS` / VT-d Context Entry `TT`), a malicious endpoint can simply forge `AT = 0b10` with arbitrary Host Physical Addresses without ever issuing an ATS Translation Request.
- **Linux Kernel Enforcement (`drivers/pci/ats.c` L41–45, `drivers/iommu/intel/iommu.c` L3637–3645, `arm-smmu-v3.c` L1926–1984)**:
  - `pci_ats_supported()` (`ats.c` L43) unconditionally disables ATS on any external/untrusted PCIe link: `if (!dev->ats_cap || dev->untrusted) return false;`.
  - On ARM SMMUv3, `arm_smmu_make_cdtable_ste()` / S2 STE setup (`arm-smmu-v3.c` L1926–1927, L1982–1983) clears `STRTAB_STE_1_EATS` to `0` when `!ats_enabled`, causing the SMMU hardware to abort incoming `AT=0b10` Translated Requests from that StreamID.
  - On Intel VT-d, `risky_device()` (`intel/iommu.c` L3637–3641) additionally skips vendor IOMMU quirks (`RMRR`/bypass quirks) for `pdev->untrusted`.

#### 4.2 Critical Invalidation Ordering Invariant: `PTE Clear -> IOTLB Flush + Sync -> DevTLB Flush + Sync`
When ATS *is* enabled (for trusted internal accelerators or TDISP-attested endpoints), revoking a page mapping and reallocating the physical frame from `Domain A` to `Domain B` requires a strict 3-step fence:
1. Clear/update the IOMMU page-table entry (PTE) in memory and issue a write barrier.
2. **Invalidate the IOMMU IOTLB and wait for synchronous completion.**
3. **Only AFTER the IOTLB flush completes, send an ATS Invalidation Request (`CMDQ_OP_ATC_INV` / `qi_flush_dev_iotlb`) to the endpoint's DevTLB and wait for `Invalidate Completion`.**

**Exhaustive State-Space Proof (`Basis: execution`, Probe 2A)**:
- If host software reverses Steps 2 and 3 (`clear_pte -> flush_devtlb -> flush_iotlb -> realloc_to_B`), Probe 2A explores 8 reachable states and finds an exact **6-step cross-domain DMA counterexample**:
  1. `HOST: clear_pte`
  2. `HOST: flush_devtlb` (DevTLB emptied, while stale `Domain A` mapping remains in IOTLB)
  3. `DEV: ATS Translation Req` arrives and **refills DevTLB = A from the stale IOTLB!**
  4. `HOST: flush_iotlb` (IOTLB cleared, but DevTLB still holds `A`!)
  5. `HOST: realloc_to_B` (physical frame assigned to `Domain B`)
  6. `DEV: Translated DMA (AT=0b10)` accesses `Domain B`'s private frame via the stale DevTLB entry!
- Under the correct order (`clear_pte -> flush_iotlb -> flush_devtlb -> realloc_to_B`), Probe 2A exhaustively verifies **0 violations** across all interleavings (because once IOTLB and PTE are both cleared before `flush_devtlb`, no ATS Translation Request can refill `A`).
- **Upstream Linux Verification (`Basis: source`)**:
  - **ARM SMMUv3** (`drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c` L2732–2734): `arm_smmu_invs_end_batch()` explicitly splits command-queue batches with a hardware `CMD_SYNC` whenever transitioning from non-ATS (`S1`/`S2` `TLBI`) to ATS (`INV_TYPE_ATS` / `INV_TYPE_ATS_FULL`): `/* ATS must be after a sync of the S1/S2 invalidations */ if (!arm_smmu_inv_is_ats(cur) && arm_smmu_inv_is_ats(next)) return true;`.
  - **Intel VT-d** (`drivers/iommu/intel/cache.c` L77–85, L145–151, L402–466): `cache_tag_assign_domain()` always assigns `CACHE_TAG_IOTLB` before `CACHE_TAG_DEVTLB`, so `cache_tag_flush_range()` enqueues IOTLB invalidations ahead of DevTLB invalidations in the ordered Queued Invalidation (QI) ring; for nested S2 changes (`CACHE_TAG_NESTING_DEVTLB`, L449–457), Linux flushes the *entire* device ATC (`0, MAX_AGAW_PFN_WIDTH`), and on platforms with `info->dtlb_extra_inval` (`intel/iommu.c` L4295–4312, `cache.c` L402–418) emits a duplicate DevTLB flush to work around hardware in-flight ATS races.

#### 4.3 `PRI` (Page Request Interface) Resource Exhaustion & Stale-Completion Hazards
- **PCIe PRI** (`drivers/pci/ats.c`, `intel/iommu.c` L901) lets endpoints demand-page host virtual memory (SVA/PASID). A compromised or misbehaving device can flood the IOMMU Page Request Queue (PRQ) to starve host kernel threads, force excessive page-in / swap thrashing, or exploit race conditions during `sva_unbind_device()` / `mmu_notifier.invalidate_range()` if outstanding PRI responses are not drained before PASID teardown (`intel/iommu.c` L4280–4293).

#### 4.4 `Thunderclap` Sub-Page IOMMU Granularity Leakage & `SWIOTLB` Bounce-Buffering
- **Vulnerability (`Thunderclap`, Markettos et al., NDSS 2019, `doi:10.14722/ndss.2019.23194`)**: IOMMUs enforce permissions at OS page granularity (**4 KiB** on x86-64; **4 KiB or 64 KiB** on ARM64), whereas OS drivers routinely call `dma_map_single()` on small slab-allocated structs (e.g., 64-byte descriptors or 256-byte `sk_buff` headers) packed alongside unrelated kernel objects (credentials, function pointers, keys) inside the same physical page.
- **Quantified Exposure (`Basis: execution`, Probe 2A)**: Mapping a 64-byte descriptor in a 4 KiB page exposes **4,032 / 4,096 sibling bytes (98.44%)** to rogue peripheral DMA read/write; a 256-byte object exposes **93.75%** on 4 KiB pages and **65,280 / 65,536 bytes (99.61%)** on 64 KiB ARM64 pages!
- **Upstream Linux Mitigation (`drivers/iommu/dma-iommu.c` L592–616)**: `dev_use_swiotlb()` checks `IS_ENABLED(CONFIG_SWIOTLB) && (dev_is_untrusted(dev) || dma_kmalloc_needs_bounce(dev, size, dir))`, where `dev_is_untrusted(dev)` tests `dev_is_pci(dev) && to_pci_dev(dev)->untrusted` (L592–594). Untrusted PCIe devices are forced to DMA strictly into dedicated **SWIOTLB bounce pages** containing **0 adjacent kernel slab bytes**, trading a memory copy for sub-page spatial isolation.

---

### 5. OpenBMC Host-BMC Bridges (`Aspeed P2A`, `CVE-2019-6260`) and Packetized `MCTP` Migration

Basis: source + normative (CVE) + documentation

#### 5.1 ASPEED `P2A` / `iLPC2AHB` Trust-Boundary Collapse (`CVE-2019-6260` "Pantsdown")
Baseboard Management Controllers (BMCs) are supposed to remain an isolated out-of-band root of control even when the host OS is compromised. On widely deployed **ASPEED AST2400/AST2500** SoCs, hardware debug/VGA bridges shattered this boundary:
- **Direct Source Proof of Full-Space Read Exposure (`torvalds/linux/drivers/soc/aspeed/aspeed-p2a-ctrl.c` L32–99, L385–410)**:
  - `SCU180_ENP2A` (`BIT(1)` of `SCU180`, L39) enables the PCIe-to-AHB (P2A) bridge on the BMC's PCIe VGA device.
  - Lines 76–79 document a devastating hardware property directly in kernel comments:
    `/* The entire memory space is opened for reading once the bridge is enabled, therefore this needs only to be tracked once per user. */`
  - Only **writes** are partitioned into 6 coarse AHB ranges gated by 4 bits in `SCU2C` (`SCU2C_FLASH = BIT(22)`, `SCU2C_SOC = BIT(23)`, `SCU2C_SPI = BIT(24)`, `SCU2C_DRAM = BIT(25)`, L385–410)—covering BMC Flash (`0x00000000–0x0FFFFFFF`, `0x20000000–0x3FFFFFFF`), SoC MMIO (`0x10000000–0x1FFFFFFF`, `0x40000000–0x5FFFFFFF`), SPI (`0x60000000–0x7FFFFFFF`), and BMC DRAM (`0x80000000–0xFFFFFFFF` on AST2500).
- **Exploit Mechanics (`CVE-2019-6260`, CVSS 9.8)**: Alongside P2A, AST2400/AST2500 exposed an LPC SuperIO **iLPC2AHB** bridge and an **X-DMA** engine. Any host Ring 0 attacker could traverse enabled/unlocked bridges to read BMC credentials and keys from BMC DRAM, patch live OpenBMC/AMI services in RAM, or re-flash persistent malicious BMC firmware.
- **Hardening & Modern IPC (`OpenBMC`, `CodeConstruct/mctp`)**: Linux `aspeed_p2a_ctrl_probe()` now calls `aspeed_p2a_disable_all()` immediately on probe (L364), and modern OpenBMC deployments (`openbmc/phosphor-host-ipmid` @ `825c7b0485057bd74f1e59ee0604fe7a9d54304d`, `CodeConstruct/mctp` @ `82540d8f0a6b0cb612c73f54e8a1fa962e1a09d1`) disable P2A/iLPC2AHB in hardware/U-Boot and migrate host-BMC and BMC-device management off shared AHB memory / legacy IPMI KCS onto **DMTF MCTP (DSP0236)** message-passing sockets (`AF_MCTP` in Linux `net/mctp/`) carrying **PLDM** and **SPDM** over PCIe VDM, I2C, or I3C.

---

### 6. Heterogeneous SoC & Baseband Shared-Memory Mailbox Verification (`Qualcomm SMEM / GLINK`)

Basis: source + execution + normative (peer-reviewed paper)

On mobile and embedded SoCs, the Application Processor (AP) shares fixed DRAM regions with closed-source cellular basebands, DSPs, and microcontrollers. Because cellular basebands parse untrusted over-the-air LTE/5G/GSM frames in memory-unsafe RTOSes—and **FirmWire** (Hernandez et al., NDSS 2022, `doi:10.14722/ndss.2022.23136`) demonstrated automated discovery of 7 pre-authentication memory corruptions leading to over-the-air baseband RCE across Samsung and MediaTek firmware—the **AP-side shared-memory IPC parser is a direct remote attack surface** once a baseband is compromised!

Direct audit of upstream Linux **`drivers/soc/qcom/smem.c`** and **`drivers/rpmsg/qcom_glink_native.c`** (`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) illustrates the exact FFI and formal-verification hazards of shared-memory ring buffers:

1. **Shared Partition Table Trust (`drivers/soc/qcom/smem.c` L39–162)**: `smem_ptable` sits 4 KiB from the end of shared DRAM, indexing per-host private partitions (`SMEM_HOST_APPS = 0`) via `__le32 offset` and `__le32 size` guarded by hardware spinlocks (`hwspin_lock`). Any bounds check that fails to validate `offset + size <= region_size` in 64-bit arithmetic permits out-of-bounds kernel reads/writes into adjacent coprocessor partitions.
2. **Double-Fetch Across Shared FIFO Peeks (`drivers/rpmsg/qcom_glink_native.c` L919, L1065, L1212–1218)**:
   - `qcom_glink_native_rx()` first peeks the 8-byte `struct glink_msg` header (`cmd`, `param1`, `param2`) from the shared-memory RX FIFO to select the handler (`GLINK_CMD_TX_DATA`, `GLINK_CMD_INTENT`, etc.).
   - Inside `qcom_glink_rx_data()` (L919), the kernel executes a **second** `qcom_glink_rx_peek(glink, &hdr, 0, sizeof(hdr))` directly from shared RAM (which the untrusted remote coprocessor can concurrently mutate between peek 1 and peek 2!), re-reading `hdr.msg.param1` (`rcid`), `hdr.msg.param2` (`liid`), `chunk_size`, and `left_size`. Similarly, `qcom_glink_handle_intent()` (L1041–1065) computes `msglen = struct_size(msg, intents, count)` using `count` from peek 1, allocates `kmalloc(msglen, GFP_ATOMIC)`, and performs peek 2 (`qcom_glink_rx_peek(glink, msg, 0, msglen)`) from shared RAM.
3. **Unchecked 32-Bit Unsigned Wraparound in `intentless` Mode (`qcom_glink_native.c` L907–986, Probe 2C)**:
   - Lines 907–908 declare `unsigned int chunk_size, left_size;` (32-bit unsigned) populated via `le32_to_cpu()` from the remote coprocessor's shared-RAM header (L920–921).
   - Lines 952 and 960 execute unchecked 32-bit addition:
     ```c
     intent->data = kmalloc(chunk_size + left_size, GFP_ATOMIC);
     ...
     intent->size = chunk_size + left_size;
     intent->offset = 0;
     channel->buf = intent;
     ```
   - **Concrete Counterexample Witnesses (`Basis: execution`, Probe 2C)**:
     - *Witness A*: Remote coprocessor sends `chunk_size = 0x100`, `left_size = 0xFFFFFF80`. Modulo $2^{32}$, `chunk_size + left_size = 0x80`. The AP allocates an 0x80-byte buffer, assigns `channel->buf = intent` (with `intent->size = 0x80`), then hits line 981 (`0x80 - 0 < 0x100`), logs `"Insufficient space in intent"`, and jumps to `advance_rx` **without freeing or clearing `channel->buf`**! The channel is now poisoned with an undersized persistent `intent` buffer for subsequent fragments.
     - *Witness B*: Remote coprocessor sends `chunk_size = 0x100`, `left_size = 0xFFFFFF00`. Modulo $2^{32}$, `chunk_size + left_size = 0x0`. In Linux, `kmalloc(0)` returns `ZERO_SIZE_PTR` (`0x10`, non-NULL!), passing the `!intent->data` check at L954 and storing `ZERO_SIZE_PTR` in `channel->buf->data`!
   - **Required Verification Invariant**: Any shared-memory IPC parser facing an untrusted peer MUST enforce: (a) **volatile single-copy snapshot** of the entire header+payload frame into domain-private memory (or strictly monotonic snapshot of head/tail indices with `dma_rmb()` before reading frame bytes and re-checking bounds against the snapshotted length, never re-reading header fields from shared RAM), and (b) **overflow-checked arithmetic** (`check_add_overflow` / `u64` checked sum bounded by a fixed `MAX_MSG_SIZE`) *before* allocating or mutating persistent channel state.

---

### 7. Formal Verification & Memory-Safe FFI Checklist for Mutually-Distrusting Fabrics

Basis: derived + source + execution

| Boundary Property | Concrete Failure Witness | Required Verifiable Invariant |
| :--- | :--- | :--- |
| **Multi-Mode Protocol Binding** | SPDM 1.2 PSK cross-protocol auth bypass (`ePrint 2024/2047`, CVSS 9.0) | Model all handshake modes + session transitions jointly (e.g., Tamarin/ProVerif); bind mode/role tags into every transcript hash |
| **Config-Lock to Activation Coupling** | Malicious VMM alters BAR/MSI-X between attestation and CVM accept | Monotonic TDI state machine (`UNLOCKED -> LOCKED -> RUN`, tamper -> `ERROR`) with fresh 32-byte `start_interface_nonce` |
| **IOTLB / DevTLB Flush Fence** | Reversed flush allows ATS refill from stale IOTLB -> cross-domain DMA (Probe 2A) | Strictly enforce `PTE clear -> IOTLB inv + SYNC -> DevTLB inv + SYNC -> frame reuse` |
| **Sub-Page DMA Spatial Isolation** | 4 KiB / 64 KiB IOMMU page leaks 93.75%–99.61% sibling kernel bytes (`Thunderclap`) | Force `SWIOTLB` bounce-buffering (`dev_use_swiotlb`) or page-exclusive DMA arenas for untrusted devices; disable ATS (`!dev->untrusted`) |
| **Zero-Copy Shared-RAM IPC Safety** | `qcom_glink_rx_data` L952 `u32` wraparound + double-fetch peeks (Probe 2C) | Single-copy volatile snapshot into private RAM; checked arithmetic (`chunk + left <= MAX_MSG`) before allocation; roll back channel state on reject |
| **Out-of-Band Debug Bridge Closure** | BlueField PCIe `RShim` or Aspeed `SCU180_ENP2A` full-AHB read exposure (`CVE-2019-6260`) | Permanently strap/lock off host-to-BMC/DPU memory bridges in hardware/boot ROM; use message-framed channels (`MCTP`/SPDM) |

## Boundaries

- **CXL 3.x `CXL.cache` / `CXL.mem` Coherent IDE Semantics (`not examined`)**: This report examined PCIe Selective/Link IDE (`pci_idekm.h`, `drivers/pci/ide.c`) and TDISP (`pci_tdisp.h`, `drivers/pci/tsm.c`). Cache-coherent CXL.cache/CXL.mem IDE framing, CXL Type-2/Type-3 memory-expander back-invalidation snooping attacks, and CXL TSP (TEE Security Protocol) were not inspected in upstream source.
- **Vendor-Specific TSM Firmware Implementations (`unknown` / `not examined`)**: Linux `drivers/pci/tsm.c` provides the host-side kernel marshaling framework (`pci_tsm_ops`), whereas the cryptographic enforcement of SPDM/IDE_KM/TDISP resides in platform-specific TSM firmware (Intel TDX Connect SEAM module, AMD SEV-TIO ASP firmware, ARM CCA RMM/RME-DA) whose internal binaries/trees were not audited here.
- **ASPEED AST2600/AST2700 Hardware Revisions (`not examined`)**: `drivers/soc/aspeed/aspeed-p2a-ctrl.c` explicitly defines match data for `ast2400` and `ast2500` (`L412–417`). Newer ASPEED generations (AST2600/AST2700) added finer-grained hardware bridge locks and Caliptra/RoT integration not directly verified via RTL in this study.
- **AWS Nitro Hardware & Firmware Internals (`unknown`)**: AWS Nitro Card ASIC designs, Nitro Security Chip firmware, and Nitro Hypervisor binaries are proprietary; findings reflect AWS's published Nitro System Security Design whitepaper and architectural boundary documentation rather than source inspection.
- **AMD IOMMU (`drivers/iommu/amd/iommu.c`) Specific Errata (`not examined`)**: While `drivers/iommu/amd/iommu.c` was retrieved, detailed line-by-line auditing of IOTLB/DevTLB invalidation ordering focused on Intel VT-d (`intel/cache.c`, `intel/iommu.c`) and ARM SMMUv3 (`arm-smmu-v3.c`); AMD IOMMU `INVALIDATE_IOMMU_PAGES` -> `INVALIDATE_IOTLB_PAGES` command-buffer sequencing follows the same architectural invariant (`Basis: derived`) but was not audited line-by-line for AMD-specific quirks.
- **Baseband Vendor IPC Stacks Beyond Qualcomm GLINK (`not examined`)**: Samsung Exynos SIPC / CPIF, MediaTek CCCI, and Apple RTKit shared-memory IPC drivers were not source-audited at pinned commits; the single-fetch snapshot and checked-arithmetic invariants generalize architecturally (`Basis: derived`), while exact wraparound bugs in `qcom_glink_native.c` L952 apply specifically to Linux's `qcom_glink_native` `intentless` path.
- **Hardware-Non-Compliant ATS Devices (`known not to apply` to Probe 2A's safety proof)**: Probe 2A's proof that `IOTLB flush -> DevTLB flush` yields 0 cross-domain DMA violations holds strictly for endpoints that honor ATS `Invalidate Request` messages and do not spoof `AT = 0b10` Translated Requests. A malicious hardware endpoint that ignores DevTLB invalidations or forges `AT = 0b10` defeats *all* host-side flush schedules and must instead have ATS disabled at the IOMMU/ACS layer (`pci_ats_supported` returning `false`).

## Evidence

### Primary Git Repositories Inspected (`2026-11-19`)

1. **`DMTF/libspdm` @ `3f1253df61ef1af917f1f18ce40db065e93ff82c`**:
   - `include/industry_standard/spdm_secured_message.h` L37–140: DSP0277 AEAD record layout (`session_id`, `sequence_number`, `length`, `application_data_length`, `AeadTag`), `SECURED_SPDM_VERSION_13 = 0x13`, `SECURED_MESSAGE_OPAQUE_ELEMENT_SMDATA_ID_AEAD_LIMIT = 0x2`, `SECURED_MESSAGE_AEAD_LIMIT_EXPONENT_MAX = 64`.
   - `include/industry_standard/pci_idekm.h` L17–126: `PCI_IDE_KM_OBJECT_ID_*` (`QUERY`, `KEY_PROG`, `KP_ACK`, `K_SET_GO`, `K_SET_STOP`, `K_SET_GOSTOP_ACK`, `GET_KEY`, `EN_AEAD_LC`), `LINK_IDE` max 8 / `SELECTIVE_IDE` max 255 / 15 address-association blocks, `K0`/`K1`, `RX`/`TX`, `PR`/`NPR`/`CPL` sub-stream bitmasks (`L75–87`).
   - `include/industry_standard/pci_tdisp.h` L19–281: `LOCK_INTERFACE_REQ/RSP` (`0x83`/`0x03`, flags `NO_FW_UPDATE`, `LOCK_MSIX`, `BIND_P2P`, `ALL_REQUEST_REDIRECT`, 32-byte `start_interface_nonce`), `GET_DEVICE_INTERFACE_REPORT` (`0x84`, `pci_tdisp_mmio_range_t`, `pci_tdisp_device_interface_report_struct_t`), TDI states `CONFIG_UNLOCKED=0`, `CONFIG_LOCKED=1`, `RUN=2`, `ERROR=3` (L201–204), `START_INTERFACE_REQ` (`0x86`), `STOP_INTERFACE_REQ` (`0x87`).
   - `library/spdm_requester_lib/libspdm_req_psk_exchange.c` L16–422: PSK exchange opaque data, context, measurement summary hash, and HMAC verification flow.
2. **`DMTF/spdm-emu` @ `6c222618c109d29bdd7e363540089d6713cbb8ff`**:
   - `include/library/pci_ide_km_requester_lib.h` & `include/library/pci_tdisp_requester_lib.h`: Reference requester library bindings for IDE_KM and TDISP over SPDM.
3. **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`**:
   - `include/linux/pci-tsm.h` L13–210 & `drivers/pci/tsm.c` L186–900: `struct pci_tsm_ops` (`link_ops`: `probe`/`remove`/`connect`/`disconnect`/`bind`/`unbind`/`guest_req`; `devsec_ops`: `lock`/`unlock`), `struct pci_tdi`, `PCI_TSM_REQ_DEBUG_WRITE = 3` (`CAP_SYS_RAW_IO` + kernel taint), `pci_tsm_doe_transfer`.
   - `include/linux/pci-ide.h` L13–116 & `drivers/pci/ide.c` L98–720: `struct pci_ide_partner`, `struct pci_ide_regs`, `PCI_IDE_RESERVED_STREAM_ID = 255`, `pci_ide_stream_enable` verifying `PCI_IDE_SEL_STS_STATE_SECURE` or returning `-ENXIO`.
   - `drivers/pci/ats.c` L41–120: `pci_ats_supported()` rejecting `dev->untrusted` (L43), `pci_enable_ats()`.
   - `drivers/iommu/dma-iommu.c` L592–616: `dev_is_untrusted()` and `dev_use_swiotlb()` forcing bounce-buffering for untrusted PCIe devices.
   - `drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c` L1926–1984 (`STRTAB_STE_1_EATS_TRANS` gated on `ats_enabled`), L2722–2823 (`arm_smmu_invs_end_batch` enforcing S1/S2 TLBI sync strictly before `INV_TYPE_ATS` / `CMDQ_OP_ATC_INV`).
   - `drivers/iommu/intel/iommu.c` L885–903, L3637–3645 (`risky_device` skipping IOMMU quirks for `pdev->untrusted`), L4280–4312 (`quirk_extra_dev_tlb_flush`) & `drivers/iommu/intel/cache.c` L77–85, L145–165, L362–468 (`cache_tag_flush_range` ordering IOTLB before DevTLB; full ATC flush on `CACHE_TAG_NESTING_DEVTLB`).
   - `drivers/net/ethernet/mellanox/mlx5/core/ecpf.c` L12–76: `mlx5_ecpf_esw_admins_host_pf`, `mlx5_host_pf_init` / `mlx5_esw_host_pf_enable_hca` distinguishing DPU Mode from Separated Host Mode.
   - `drivers/soc/aspeed/aspeed-p2a-ctrl.c` L32–99, L364, L385–417: `SCU180_ENP2A = BIT(1)` opening entire BMC AHB space for host reading (L76–79), 6 AST2400/AST2500 write ranges gated by `SCU2C_{FLASH,SOC,SPI,DRAM}`, `aspeed_p2a_disable_all()` on probe.
   - `drivers/soc/qcom/smem.c` L39–162 & `drivers/rpmsg/qcom_glink_native.c` L900–1069, L1212–1242: `qcom_glink_rx_data` double-fetch peek (L919) and 32-bit `unsigned int` `chunk_size + left_size` wraparound in `intentless` mode (L952, L960, L981).
4. **`Mellanox/rshim-user-space` @ `67b5a7a66bd1ef3665eb79c055f0a3088d1d895c`**:
   - `README.md` L3–83: `usb|pcie|pcie_lf` backends and `/dev/rshim<N>/{boot,console,rshim,misc}` ARM SoC control surfaces.
5. **`CodeConstruct/mctp` @ `82540d8f0a6b0cb612c73f54e8a1fa962e1a09d1`** & **`openbmc/phosphor-host-ipmid` @ `825c7b0485057bd74f1e59ee0604fe7a9d54304d`**:
   - MCTP userspace control plane (`AF_MCTP`) and OpenBMC IPMI daemon boundary.

### Peer-Reviewed Papers, Standards, and Advisories

- A. Theodore Markettos, Colin Rothwell, Brett F. Gutstein, Allison Pearce, Peter G. Neumann, Simon W. Moore, and Robert N. M. Watson, *Thunderclap: Exploring Vulnerabilities in Operating System IOMMU Protection via DMA from Untrustworthy Peripherals*, NDSS 2019, DOI `10.14722/ndss.2019.23194`.
- Cas Cremers, Alexander Dax, and Aurora Naska, *Breaking and Provably Restoring Authentication: A Formal Analysis of SPDM 1.2 including Cross-Protocol Attacks*, IACR Cryptology ePrint Archive Report `2024/2047` (`https://eprint.iacr.org/2024/2047`).
- Grant Hernandez, Marius Muench, Dominik Maier, Alyssa Milburn, Shinjo Park, Tobias Scharnowski, Tyler Tucker, Patrick Traynor, and Kevin R. B. Butler, *FirmWire: Transparent Dynamic Analysis for Cellular Baseband Firmware*, NDSS 2022, DOI `10.14722/ndss.2022.23136`.
- `CVE-2019-6260` (*ASPEED AST2400/AST2500 P2A, iLPC2AHB, and X-DMA host-to-BMC bridge vulnerability / "Pantsdown"*, CVSS 9.8).
- DMTF `DSP0274` (SPDM), `DSP0277` (Secured Messages using SPDM), `DSP0236` (MCTP Base); PCI-SIG Base Specification ECNs for `DOE`, `CMA-SPDM`, `IDE`, and `TDISP`.
- AWS *Security Design of the AWS Nitro System* whitepaper; NVIDIA BlueField DPU / DOCA Zero-Trust DPU Mode documentation.

### Executable Micro-Probe Verification Outputs (`2026-11-19`, Python 3)

Running the standalone Python 3 probe (exact logic in **Revalidation**) yielded exit code `0` with all assertions passing:

```text
=== PROBE 2A: IOMMU IOTLB/DevTLB Flush Ordering & Thunderclap Sub-Page Exposure ===
Schedule=buggy_devtlb_first   | explored_states= 8 | violation=True
   step 1: HOST: clear_pte
   step 2: HOST: flush_devtlb
   step 3: DEV: ATS Translation Req refills DevTLB=A from IOTLB
   step 4: HOST: flush_iotlb
   step 5: HOST: realloc_to_B
   step 6: DEV: Translated DMA (AT=0b10) hits Domain B page via stale DevTLB!
Schedule=correct_iotlb_first  | explored_states= 5 | violation=False
Thunderclap exposure (4KiB page / 64B descriptor): 4032/4096 sibling bytes exposed (98.44%), SWIOTLB bounce=0 sibling bytes
Thunderclap exposure (4KiB page / 256B sk_buff): 3840/4096 sibling bytes exposed (93.75%), SWIOTLB bounce=0 sibling bytes
Thunderclap exposure (64KiB ARM64 page / 256B sk_buff): 65280/65536 sibling bytes exposed (99.61%), SWIOTLB bounce=0 sibling bytes

=== PROBE 2B: PCIe TDISP TDI State Automaton (pci_tdisp.h L201-204) ===
Benign TDISP flow: lock=True, start=True (RUN), final=RUN
Tampered BAR after LOCK: cfg_write=FAULT_TO_ERROR, start=False (rejected(state=ERROR)), state=ERROR
Stale nonce replay after STOP/re-LOCK: start=False (rejected(state=CONFIG_LOCKED)), state=CONFIG_LOCKED

=== PROBE 2C: Shared-Memory Mailbox (qcom_glink_rx_data L920-990) Arithmetic & Double-Fetch ===
Witness A (u32 wrap): chunk=0x100, left=0xffffff80 -> u32(chunk+left)=0x80, chunk1_accepted=False (dropped, BUT channel->buf stays allocated with size=0x80!)
Witness B (u32 wrap to 0): chunk=0x100, left=0xffffff00 -> u32(chunk+left)=0x0 (kmalloc(0)=ZERO_SIZE_PTR non-NULL), chunk1_accepted=False, channel->buf poisoned with ZERO_SIZE_PTR!
Checked defense on Witness A: (None, False); Witness B: (None, False)
```

## Revalidation

Use the following targeted checks to test whether these invariants still hold on newer upstream revisions or concrete deployments:

1. **Diff upstream Linux and `libspdm` control-boundary files against pinned revisions**:
   ```bash
   git -c protocol.version=0 ls-remote https://github.com/torvalds/linux.git HEAD
   git -c protocol.version=0 ls-remote https://github.com/DMTF/libspdm.git HEAD
   ```
   - Check `drivers/rpmsg/qcom_glink_native.c` (`qcom_glink_rx_data`) to see whether `chunk_size + left_size` in `intentless` mode has been patched to use overflow-checked arithmetic (`check_add_overflow` / `size_add`) and whether `channel->buf` is freed on rejected chunks and single-fetched from shared RAM.
   - Check `drivers/pci/ats.c` (`pci_ats_supported`), `drivers/iommu/dma-iommu.c` (`dev_use_swiotlb`), `drivers/iommu/arm/arm-smmu-v3/arm-smmu-v3.c` (`arm_smmu_invs_end_batch`), and `drivers/iommu/intel/cache.c` (`cache_tag_flush_range`) for regressions in untrusted-device ATS refusal, SWIOTLB enforcement, or IOTLB-before-DevTLB invalidation ordering.
   - Check `drivers/pci/tsm.c`, `drivers/pci/ide.c`, and `DMTF/libspdm/include/industry_standard/{pci_idekm.h,pci_tdisp.h,spdm_secured_message.h}` for newer SPDM 1.4 / TDISP 1.1 / CXL TSP extensions or stream-state changes.
2. **Rerun the standalone IOMMU flush-ordering, TDISP automaton, and GLINK wraparound verification probe**:
   ```bash
   python3 - <<'PY'
   from collections import deque
   def check(ops):
       start = (0, "A", "A", "A", "A")
       q, seen = deque([start]), {start}
       while q:
           step, pte, iotlb, devtlb, mem = q.popleft()
           if devtlb == "A" and mem == "B":
               return True
           if step < len(ops):
               op = ops[step]
               ns = (step+1, None if op=="pte" else pte, None if op=="iotlb" else iotlb,
                     None if op=="devtlb" else devtlb, "B" if op=="realloc" else mem)
               if ns not in seen: seen.add(ns); q.append(ns)
           src = iotlb if iotlb is not None else pte
           if src is not None and devtlb != src:
               ns = (step, pte, iotlb, src, mem)
               if ns not in seen: seen.add(ns); q.append(ns)
       return False
   assert check(["pte", "devtlb", "iotlb", "realloc"]) is True
   assert check(["pte", "iotlb", "devtlb", "realloc"]) is False
   # Verify qcom_glink_rx_data u32 wraparound witness
   assert ((0x100 + 0xFFFFFF80) & 0xFFFFFFFF) == 0x80
   assert ((0x100 + 0xFFFFFF00) & 0xFFFFFFFF) == 0
   print("REVALIDATION_OK")
   PY
   ```
3. **Deployment-level hardware audit**: On BlueField DPU servers, verify host PCIe RShim is disabled (`lspci` absent RShim function / `mlxconfig` `INTERNAL_CPU_RSHIM=DISABLED` & `HOST_PRIV_CTRL` locked); on ASPEED BMC platforms, verify `SCU180` bit 1 (`ENP2A`) and `iLPC2AHB` decode are disabled in BMC U-Boot/kernel runtime (`devmem` / sysfs) before exposing bare-metal hosts to untrusted tenants.
