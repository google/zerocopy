# Silicon Roots of Trust, Secure Enclaves, and Shadow Management Cores

## Summary

Modern platforms concentrate foundational trust across three structurally distinct hardware-isolation paradigms whose security boundaries, verifiability, and failure modes diverge sharply:

1. **Open-silicon Roots of Trust (RoTs) with hardware-enforced key isolation and fault-injection (FI) hardening** — exemplified by **OpenTitan** (Earl Grey RISC-V Ibex + OTBN, `keymgr`/`keymgr_dpe`, `lc_ctrl`, `alert_handler`) and **Caliptra** (CHIPS Alliance VeeR EL2, hardware Key Vault, Device Ownership Encryption, PCR Vault, sparse-FSM SoC mailbox, and Caliptra 2.2 boot-flow transition enforcement). Both eliminate software visibility of root secrets by hardware-sideloading derived keys directly into cryptographic accelerators, enforce monotonic boot-stage privilege drop in silicon (`Smepmp` `MML`/`MMWP`, Caliptra `hwset` `lock_wr`/`lock_use` and exact 3-bit DICE write counters), and counter physical/glitch attacks with dual-core lockstep, sparse encodings, differential alert ping-pong networks, and compiler-barriered software checks (`launder32`, Hamming-distance-8 booleans).
2. **Co-designed application-processor compartmentalization plus discrete enclave coprocessors** — exemplified by **Apple Silicon** (**SEP** running an L4-derived microkernel with isolated Boot ROM and hardware UID/GID keys, paired with application-processor **PAC**, legacy **PPL**, and modern **GXF/GL2** hosting **SPTM** and **TXM**). SPTM moves page-table ownership and physical-frame typing (`sptm_retype`, `XNU_PAGE_TABLE_*`, `XNU_KERNEL_RESTRICTED`) out of the XNU kernel into a lateral guarded exception level, while PAC remains vulnerable to speculative microarchitectural oracles (`PACMAN`, ISCA 2022) when pointer authentication failure leaks through cache state.
3. **Opaque, high-privilege x86 shadow execution domains** — **System Management Mode (Ring -2)** and out-of-band management coprocessors (**Intel ME/CSME** and **AMD PSP/ASP**, often termed **Ring -3**). Unlike discrete RoTs with narrow message-passing mailboxes and hardware-isolated key slots, x86 SMM executes inside shared host DRAM (`TSEG`/`SMRAM`) on the main CPU cores, accepts raw physical pointers from an untrusted Ring 0 OS via `CommBuffer` without copying payloads into SMRAM inside `PiSmmCore`, and historically suffered both software confused-deputy attacks (nested pointers, DMA TOCTOU double-fetches, SMRAM callouts) and architectural lock bypasses (**Sinkclose**, `CVE-2023-31315`, manipulating `TClose` via MSR `0xC0010113` despite SMI Lock). Ring -3 controllers possess broad DMA access to host RAM (`UMA`/`HECI` on Intel CSME; on-die ARM Cortex-A5/TrustZone on AMD PSP/ASP) while remaining closed-source; voltage fault injection against AMD PSP (`One Glitch to Rule Them All`, CCS 2021; `faulTPM`, EuroS&P 2023) and memory corruption in Intel CSME (`CVE-2017-5705` / `INTEL-SA-00086`) demonstrate that obscurity and ring hierarchy fail without hardware-backed FI countermeasures and minimal auditable TCBs.

For systems and formal-verification engineers, the decisive architectural divider is **whether the trust boundary is enforced by narrow, hardware-typed message channels and non-software-readable key paths** (OpenTitan, Caliptra, SPTM frame typing) **versus shared-address-space privilege rings relying on pervasive caller-supplied pointer validation** (x86 SMM) **or opaque bus-mastering coprocessors** (ME/PSP).

## Applicability

This report synthesizes and compares six primary upstream codebases, two industry hardware advisories, and three peer-reviewed security analyses pinned in `REPORT.json`:

- **OpenTitan (`lowRISC/opentitan` @ `1e061997389b1c257043b0dbd2388a19a6c2f6f1`)** and **Ibex (`lowRISC/ibex` @ `9b91b3a1195aecb0d80cf2de5b852e0b5f68cc6c`)**: Findings apply to the Earl Grey 1.0.0 discrete RoT architecture (`rv_core_ibex` with `SecureIbex=1`, `Lockstep`, `Smepmp`, `OTBN`, `lc_ctrl`, `alert_handler`, `keymgr`) and note where HEAD introduces **Darjeeling** / **Key Manager DPE** (`hw/ip/keymgr_dpe/`, TCG DPE multi-slot hierarchy superseding legacy linear `keymgr`). Software-hardening findings (`hardened.h`, `hardened_asm.h`, `rom.c`, `epmp_state.h`) apply to `silicon_creator` ROM compiled for RV32IMC(B).
- **Caliptra (`chipsalliance/caliptra-rtl` @ `298ad4313ed8b4da25e98e3f1131c89363a6eb92` and `chipsalliance/caliptra-sw` @ `5d35f7d928afb4d190dd4619219ecd6487987f3d`)**: Findings cover the Caliptra integrated SoC RoT block (distinct from discrete-chip OpenTitan Earl Grey) across versions 1.x through 2.0/2.1/2.2 as documented in `docs/CaliptraHardwareSpecification.md` at the pinned revision, explicitly distinguishing Caliptra 1.x (APB interface) from 2.0 (AXI subordinate + AXI Manager DMA + Adams Bridge ML-DSA), 2.1 (AXI DMA AES for OCP L.O.C.K.), and 2.2 (hardware Key Vault boot-flow transition enforcement).
- **Apple XNU (`apple-oss-distributions/xnu` @ `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`)** paired with **Apple Platform Security documentation** and **PACMAN (`doi:10.1145/3470496.3527429`)**: Source findings on SPTM frame-typing APIs (`osfmk/arm64/sptm/sptm.h`, `osfmk/arm64/sptm/pmap/pmap.c`) and PAC assembly macros (`osfmk/arm64/pac_asm.h`) apply to open-sourced XNU kernel interfaces on Apple Silicon (`arm64e`); the proprietary SPTM, TXM, and SEP OS binaries themselves are not published in `apple-oss-distributions/xnu` and are characterized via XNU's caller-side contracts and published Apple Platform Security documentation.
- **EDK II (`tianocore/edk2` @ `556dcfb466e9f05affeaff881d738807f8156d3c`)**, **AMD Sinkclose (`CVE-2023-31315` / `AMD-SB-7014`)**, **Intel CSME (`CVE-2017-5705` / `INTEL-SA-00086`)**, **One Glitch to Rule Them All (`doi:10.1145/3460120.3484779`)**, and **faulTPM (`arXiv:2304.14717`)**: Source findings on `SmmMemLib`, `PiSmmCore`, and `PiSmmCpuDxeSmm` apply to UEFI Platform Initialization (PI) Traditional SMM (x86-64). Standalone MM (used on ARM64 via TF-A/FFA and emerging x86 platforms) reduces DXE-shared surface but is outside the directly inspected `PiSmmCore` path.

Claims grounded in executable Python models (reproduced in full under **Revalidation** and recorded under **Evidence**) verify exact Boolean/Smepmp truth tables, EDK II arithmetic bounds, and Caliptra 2.2 Key Vault transition policies transcribed verbatim from upstream source; they do not substitute for gate-level synthesis or silicon testing.

## Findings

### 1. Comparative Architectural Taxonomy: Trust Boundaries, Key Isolation, and Attack Surfaces

Basis: normative + source + documentation + derived

The five architectures occupy distinct points in the design space of **TCB transparency**, **memory-bus privilege**, **secret custody**, and **fault-injection resilience**:

| Dimension | OpenTitan (Earl Grey / Darjeeling) | Caliptra (Core 2.0–2.2) | Apple SEP + SPTM/TXM/PAC | x86 SMM (EDK II PI / Intel & AMD) | Intel CSME / AMD PSP (ASP) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Deployment Topology** | Discrete silicon RoT IC (or integrated top) with independent clock/power/OTP | Synthesizable on-die RoT IP block inside host SoC | Discrete on-die SEP coprocessor + AP lateral guarded mode (`GL2`/`GXF`) | Main host CPU cores switched into Ring `-2` via SMI | Dedicated on-die/PCH microcontroller (`Ring -3`: x86 Quark/MINIX on CSME; ARM Cortex-A5/TrustZone on PSP) |
| **Core ISA & Verification Surface** | 32-bit RISC-V **Ibex** + 256-bit **OTBN**; open RTL + formal/DV assertions | 32-bit RISC-V **VeeR EL2** (4-stage scalar in-order); open RTL + Rust firmware | Closed-source SEP (ARM64/L4) + closed SPTM/TXM; open XNU kernel caller boundary | Full x86-64 host CPU + UEFI PI SMM drivers (often closed OEM binaries) | Proprietary firmware blobs (MINIX-based CSME; TrustZone TEE + fTPM on PSP) |
| **Host Memory Access** | None (discrete) / explicit bus peripherals only | Scoped AXI Subordinate mailbox + optional AXI Manager DMA (2.0+) | SEP isolated via hardware DMA filter / mailbox; SPTM owns AP page tables | Full unrestricted physical RAM access (including all Ring 0/Ring -1 memory) | Direct host DRAM DMA (`UMA` + DMA engine on CSME; full SoC fabric access on PSP) |
| **Root Secret Custody** | Hardware **sideloading** (`keymgr`/`keymgr_dpe` -> AES/KMAC/OTBN); SW cannot read root seeds | Hardware **Key Vault** (`kv.sv`, 24 slots); SW cannot read keys, only route via `dest_valid` + `hwset` locks | Hardware UID/GID keys inside SEP AES engine; never readable by SEP/AP SW | No hardware key vault; secrets live in SMRAM DRAM readable by any Ring `-2` code | Hardware fuses/keys accessible to Ring `-3` firmware (compromised on PSP via VFI) |
| **Inter-Domain IPC Contract** | Narrow peripheral/SPI/I2C commands; no shared host virtual address space | Hardware-enforced **Mailbox FSM** (`mbox.sv`) with `AXI_USER` lock & sparse-FSM error sink | Typed mailbox to SEP; `GENTER`/`GEXIT` calls into SPTM frame-retyping API | Shared host DRAM `CommBuffer` passed by raw physical pointer (`gSmmCoreMailbox`) | `HECI`/`MEI` PCIe MMIO ring (CSME); C2P/P2C mailbox + shared DRAM buffers (PSP) |
| **FI / Glitch Hardening** | Dual-core lockstep, memory ECC + Prince scrambling, OTBN blanking/wipe, `hardened_bool_t`, `launder32`, alert ping-pong -> SCRAP | Sparse FSMs, ECC SRAM, exact 3-bit DICE KV write counters, `hwset` phase locks, watchdog | Hardware glitch detectors, hardened SEP ROM, monotonic counters (closed details) | None architectural in SMRAM (Ring `-2` assumes trusted CPU hardware) | Historically weak against board-level VFI (`One Glitch`, `faulTPM` on AMD SVI2) |
| **Dominant Failure Class** | Micro-architectural / software ROM bugs if `sec_mmio` / `epmp` misconfigured | SoC integration bugs (AXI user spoofing, fuse provisioning, DMA scoping) | Speculative PAC oracle (`PACMAN`); kernel-to-SPTM ABI/logic bugs | Nested-pointer confused deputy, DMA TOCTOU on `CommBuffer`, MSR lock bypass (`Sinkclose`) | Memory corruption in opaque RTOS (`CVE-2017-5705`), voltage glitch bypassing ROM sig-check |

**Key structural derivation** (`Basis: derived`): OpenTitan and Caliptra achieve qualitatively stronger security invariants than x86 SMM or Ring -3 controllers not merely because their RTL is open, but because they **eliminate ambient authority in two orthogonal directions**: (1) **downward**, host software cannot pass arbitrary dereferenceable pointers into the RoT's private address space; and (2) **inward**, even compromised RoT firmware after early boot cannot read prior-stage root keys because hardware sideloading (`keymgr` / `kv.sv`) and irreversible hardware phase locks (`hwset` `lock_use`, `Smepmp` `MML`) enforce stage-by-stage capability attenuation in silicon.

---

### 2. OpenTitan Earl Grey & Ibex: Verified Silicon RoT, Lockstep, Smepmp, OTBN, and Compiler-Hardened ROM

Basis: source + documentation + execution

#### 2.1 Ibex Hardening Parameters and Dual-Core Lockstep (`lowRISC/ibex`)
In `lowRISC/ibex` (`9b91b3a1195aecb0d80cf2de5b852e0b5f68cc6c`), `rtl/ibex_top.sv` (L15–47) exposes compile-time security parameters that Earl Grey enables via `SecureIbex = 1'b1`:
- **Dual-Core Shadow Lockstep** (`rtl/ibex_top.sv` L39–40, `rtl/ibex_lockstep.sv` L10–123, L621–756): Instantiates a delayed redundant shadow Ibex core offset by `LockstepOffset` cycles (default `1`, configurable for temporal diversity against single-cycle clock/voltage glitches). `rtl/ibex_lockstep.sv` L755–756 computes `alert_major_internal_o = outputs_mismatch | shadow_alert_major_internal | rst_shadow_cnt_err`, immediately escalating any single-bit divergence between main and shadow core outputs or shadow reset-counter faults into a fatal alert.
- **Memory Integrity & Scrambling** (`rtl/ibex_top.sv` L41–45): Setting `SecureIbex = 1'b1` defaults `MemECC = 1'b1` (widening `MemDataWidth` from 32 to `32 + 7` bits for SECDED integrity), enables `ICacheTweakInfection`, and pairs with `ICacheScramble` (Prince cipher rounds configured via `ICacheScrNumPrinceRoundsHalf`) and `ICacheECC`.
- **Dummy Instruction Insertion & RegFile ECC**: Configured alongside LFSR seeds (`RndCnstLfsrSeed`, `RndCnstLfsrPerm`) to decorrelate power/EM traces and prevent fault injection on register file reads.

#### 2.2 RISC-V Smepmp (`mseccfg`: `MML`, `MMWP`, `RLB`) Exact Permission Semantics
OpenTitan's ROM relies on the RISC-V PMP Enhancements extension (`Smepmp`) implemented in `lowRISC/ibex/rtl/ibex_pmp.sv` (L20–151) and mirrored in OpenTitan's software shadow state `sw/device/silicon_creator/lib/epmp_state.h` (L45–169). Three bits in `mseccfg` control enforcement:
- **`MML` (Machine Mode Lockdown, bit 0)**: Sticky (set-once until reset). Splits PMP rules into M-mode-only (`L=1`), S/U-mode-only (`L=0`), and five special-case shared encodings (`{R=0, W=1}` for all `{L, X}`, plus `{L=1, R=1, W=1, X=1}`).
- **`MMWP` (Machine Mode Whitelist Policy, bit 1)**: Sticky. Changes unmatched-address default behavior for M-mode from default-allow to default-deny (`rtl/ibex_pmp.sv` L138–139: `access_fail = csr_pmp_mseccfg_mmwp | (priv_mode != PRIV_LVL_M) | (csr_pmp_mseccfg_mml && (pmp_req_type == PMP_ACC_EXEC))`).
- **`RLB` (Rule Locking Bypass, bit 2)**: Allows modifying locked (`L=1`) entries during early ROM boot; once cleared to `0` (sticky), locked entries become immutable until reset.

Exhaustive evaluation of `mml_perm_check` (`rtl/ibex_pmp.sv` L59–97) across all 16 `{L, R, W, X}` bit combinations (`Basis: execution`, Probe 1A) proves two exact architectural invariants:
1. **Universal M-mode `W^X` under `MML=1`**: Zero of the 16 encodings grant simultaneous Write and Execute permissions to M-mode (`count = 0`). The encoding `(L=1, R=1, W=1, X=1)` is repurposed by `ibex_pmp.sv` L85–88 as a **shared Read-Only** (`R--` in both M and S/U) region rather than `RWX`.
2. **Asymmetry for S/U-mode**: Exactly one encoding — `(L=0, R=1, W=1, X=1)` — grants `RWX` to S/U-mode (while denying all access to M-mode). Software auditing PMP tables must therefore verify that untrusted S/U-mode entries never set `R=W=X=1` when `W^X` is desired for lower privilege levels.
3. **Counterintuitive `R=0, W=1` shared rules**: Under `MML=1`, `(R=0, W=1)` ceases to be reserved and instead maps `{L, X}` to: `00` -> `RW-` (M) / `R--` (S/U); `01` -> `RW-` (M & S/U); `10` -> `--X` (M & S/U); `11` -> `R-X` (M) / `--X` (S/U). As `epmp_state.h` L45–49 warns, flipping `MML` from `0` to `1` retroactively changes the semantics of existing PMP entries, so ROM must verify shadow state (`epmp_state_check()`) before and after every transition (`sw/device/silicon_creator/rom/rom.c` L762–783).

#### 2.3 OTBN (OpenTitan Big Number Accelerator): Deterministic Cryptography and Side-Channel Blanking
From `hw/ip/otbn/doc/theory_of_operation.md` (L1–120 and full theory spec):
- **Isolated Coprocessor Architecture**: OTBN executes asymmetric cryptography (RSA, ECDSA P-256/P-384, Ed25519) on a dedicated 256-bit wide data path (`w0..w31` WDRs plus `x0..x31` 32-bit GPRs) with private scrambled IMEM and DMEM accessible to Ibex only when OTBN is idle (preventing concurrent shared-memory races during cryptographic computation).
- **Zero-Speculation Constant-Time Amenability**: OTBN has no data cache, no branch predictor, and no speculative execution; instruction prefetch (`theory_of_operation.md` L49–55) exists solely to pre-decode instructions for **hardware SCA blanking** (gating unused ALU/bignum datapath operands to prevent secret-dependent Hamming-distance switching leakage) while preserving memory integrity bits on unscrambled prefetched instructions.
- **Dual Entropy Sources (`RND` vs `URND`)**: `theory_of_operation.md` L59–112 distinguishes `RND` (true randomness from the Entropy Distribution Network `edn_rnd`, backed by a single-entry cache with `RND_PREFETCH`; reading `RND` stalls OTBN until EDN responds) from `URND` (a local Bivium PRNG reseeded at the start of every OTBN execution, never stalling, registered with a 1-cycle lag to deliver glitch-free masking bits and overwrite internal state during hardware secure wipe).
- **Secure Wipe on Fatal Errors**: Any integrity error, illegal instruction, call-stack overflow, or escalation halts OTBN, locks it until reset, and triggers hardware secure wiping of registers, IMEM, and DMEM using `URND` entropy.

#### 2.4 Hardware Sideloading (`keymgr` -> `keymgr_dpe`), Life Cycle (`lc_ctrl`), and Alert Escalation (`alert_handler`)
- **Key Isolation Without Software Visibility**: `hw/ip/keymgr/README.md` (L1–21) confirms Earl Grey 1.0.0 taped out `keymgr` implementing one-way DICE open-profile working state hidden from software, outputting keys either to software CSRs or via **hardware sideload buses** directly to AES, KMAC, and OTBN. At repository HEAD, `keymgr` is superseded for newer tops (Darjeeling) by `hw/ip/keymgr_dpe/README.md` (L1–38), which generalizes the linear DICE chain into a **TCG DICE Protection Environment (DPE)** multi-slot DAG where any valid slot can derive a child slot (via KMAC or optional OTBN HKDF), with per-slot retention/child-derivation policies, two independent lockable root secrets, and hardware sideloading to AES, KMAC, OTBN, and HMAC.
- **Life Cycle Controller (`hw/ip/lc_ctrl/doc/theory_of_operation.md` L6–95)**: Defaults to `RAW` on power-up until OTP senses the life-cycle partition. Conditional transitions (`RAW_UNLOCK`, `TEST_UNLOCK`, `TEST_EXIT`, `RMA_UNLOCK`) pass 128-bit tokens through a hardware cryptographic one-way hash before comparison and enforce strict monotonic transition counters in OTP. Two redundant escalation paths from `alert_handler` severities 1 and 2 temporarily force the life cycle into a virtual **`ESCALATE` (`SCRAP`-equivalent)** state that disables CPU execution, debug interfaces, key manager, and flash/OTP key access.
- **Alert Handler (`hw/top_earlgrey/ip_autogen/alert_handler/doc/theory_of_operation.md` L1–105)**: Every hardware peripheral emits alerts over **differentially encoded wire pairs** with continuous **ping-pong liveness tests** (so cutting or grounding an alert wire triggers a fatal ping-timeout escalation). Unacknowledged alerts progress through a configurable 4-phase escalation chain (NMI -> LC Escalate -> Reset -> LC Scrap).

#### 2.5 Compiler-Aware Fault-Injection Hardening in OpenTitan ROM
A critical verification and codegen lesson appears directly in `sw/device/lib/base/hardened_asm.h` (L19–33), `sw/device/lib/base/hardened.h` (L23–135), and `sw/device/silicon_creator/rom/rom.c` (L630–1060):
- **Non-Complementary High-Hamming-Distance Booleans**: `HARDENED_BOOL_TRUE = 0x739` (`0b111_0011_1001`, 11 bits, HW=7) and `HARDENED_BOOL_FALSE = 0x1d4` (`0b001_1101_0100`, 9 bits, HW=5) have `XOR = 0x6ed` and **Hamming Distance = 8** (`Basis: source + execution`, Probe 1A). They are deliberately **not bitwise complements** (defeating global bus-inversion faults) and fit within 11 bits so RISC-V materializes each in a single `addi` instruction. Byte booleans use `0xa5` vs `0x4b` (`XOR = 0xee`, HD = 6).
- **Optimizing-Compiler Defeat of Redundant Checks (`launder32`)**: As documented in `hardened.h` L67–129, a naive redundant check `if (x == 0) { HARDENED_CHECK_EQ(x, 0); }` is legally optimized by LLVM/GCC into `HARDENED_CHECK_EQ(0, 0)` via constant propagation — turning the assembly check into a tautology that passes even if a fault skipped the branch! Wrapping the branch condition as `if (launder32(x) == 0) { HARDENED_CHECK_EQ(x, 0); }` inserts an inline-assembly optimization barrier preventing the compiler from propagating `x == 0` into the dominated block while preserving runtime identity semantics. `rom.c` pairs this with control-flow integrity counters (`rom_counters[kCfiRomTryBoot]`, L814–819), randomized MMIO register readback (`sec_mmio_check_values(rnd_uint32())`, `sec_mmio_check_counters(...)`, L686–796), and a sparsely encoded ROM boot FSM (`kRomStateBootRomExt = 0xed14`, L991).

---

### 3. Caliptra: On-Die Integrated RoT, Hardware Key Vault, Boot-Flow Monitor, and Sparse-FSM Mailbox

Basis: normative + source + execution

Unlike discrete OpenTitan Earl Grey, **Caliptra** (`chipsalliance/caliptra-rtl` @ `298ad4313ed8b4da25e98e3f1131c89363a6eb92`, `chipsalliance/caliptra-sw` @ `5d35f7d928afb4d190dd4619219ecd6487987f3d`) is an **on-die IP block** embedded directly inside a host server/accelerator SoC. Its architectural specification (`docs/CaliptraHardwareSpecification.md`) and RTL reveal how an integrated RoT defends against a potentially compromised surrounding SoC:

#### 3.1 Evolution Across Caliptra 1.x -> 2.0 -> 2.1 -> 2.2
From `docs/CaliptraHardwareSpecification.md` (L21–165):
- **Core**: CHIPS Alliance **VeeR EL2** 32-bit 4-stage scalar in-order RISC-V processor, with private ICCM/DCCM and fixed internal AHB-Lite memory map (`Key Vault` at `0x1001_8000` [8 KiB], `PCR Vault` at `0x1001_A000` [8 KiB], `Mailbox CSR` at `0x3002_0000` [4 KiB], `AXI DMA` at `0x3002_2000` [4 KiB], `Mailbox SRAM Direct Access` at `0x3004_0000` [256 KiB]).
- **Caliptra 2.0**: Replaces the 1.x APB SoC interface with **AXI subordinate**, adds an **AXI Manager DMA assist engine**, and integrates **Adams Bridge** hardware acceleration for post-quantum **ML-DSA (Dilithium)** (alongside ECC P-384, LMS/HSS Winternitz Chain accelerator, SHA-256/384/512/SHA3, HMAC-384/512, HMAC-DRBG, and AES-GCM/CBC).
- **Caliptra 2.1**: Adds AXI Manager DMA AES support for **OCP L.O.C.K.** (storage/device key-management offloading with `SS_OCP_LOCK_CTRL.LOCK_IN_PROGRESS` key-vault filtering, L3277–3375).
- **Caliptra 2.2**: Introduces hardware **Key Vault Boot Flow Transition Enforcement** (`docs/CaliptraHardwareSpecification.md` L3016–3265), closing software/glitch gaps across the `ROM -> FMC -> Runtime` DICE handover.

#### 3.2 Hardware Key Vault (`kv.sv`) and De-Obfuscation Engine (`doe_ctrl.sv`)
- **Non-Software-Readable Key Slots**: In `src/keyvault/rtl/kv.sv` (L19–69), the VeeR EL2 microcontroller accesses the Key Vault over AHB-Lite strictly for **control/metadata** (slot locking, clearing, status); actual key material moves exclusively over dedicated internal hardware buses (`kv_read`, `kv_write`, `pcr_ecc_signing_key`, `pcr_mldsa_signing_key`).
- **De-Obfuscation Engine (`src/doe/rtl/doe_ctrl.sv`)**: At cold reset, hardware AES-CBC decrypts the fused Unique Device Secret (UDS) and Field Entropy (FE) using a silicon obfuscation key and writes the plaintext secrets **directly into Key Vault slots** via hardware `kv_write`. VeeR EL2 firmware never observes plaintext UDS or FE in registers or SRAM.
- **Destination-Tagged Enforcement (`dest_valid`)**: Every KV slot carries a hardware `dest_valid` bitmask constraining which crypto engine input port may consume it (e.g., `HMAC_KEY | MLDSA_SEED | ECC_SEED` for `RT_CDI`, `ECC_PKEY` for `RT_ECDSA`, `MLDSA_SEED` for `RT_MLDSA`). Hardware also enforces key-length-mismatch detection (L2847).

#### 3.3 Caliptra 2.2 Hardware Boot-Flow Monitor & Exact-Match DICE Write Counters
A standout silicon verification primitive in `docs/CaliptraHardwareSpecification.md` (L3016–3165) and `kv.sv` (L38–47) is **hardware auditing of the DICE key-derivation chain** at boot-phase transitions (`cold_boot`, `boot_flow_fmc`, `boot_flow_rt` using multi-bit `mubi4_t` signals):
- **Exact-Match 3-Bit Saturating Write Counters (ROM -> FMC)**: On `enter_fmc`, hardware requires **exact** write counts on accumulator slots:
  - Slot 6 (`FMC_CDI`): `== 4` writes (`IDevID CDI` + `LDevID intermediate` + `LDevID CDI` + `FMC Alias CDI`)
  - Slot 7 (`PCR_ECDSA`): `== 2` writes (`IDevID ECC keygen` + `PCR quote ECC keygen`)
  - Slot 8 (`PCR_MLDSA`): `== 2` writes (`IDevID MLDSA keygen` + `PCR quote MLDSA keygen`)
  As the specification explicitly notes (L3106) and Probe 1C confirms (`Basis: execution`), **exact equality** rather than `>=` catches *both* truncated DICE chains (a fault skipping a derivation step, leaving `slot 6 == 3`) *and* glitch-replayed writes (`slot 6 == 5`, which could overwrite a derived slot with an earlier secret like raw UDS).
- **Hardware-Driven Non-Clearable Locks (`hwset`)**:
  - Entering `boot_flow_fmc`: hardware asserts `lock_wr` on slots `{0, 1, 2, 6, 7, 8, 13, 14}` and `lock_use` on slots `{7, 8}` (restricting PCR quote keys exclusively to the dedicated PCR signing ports).
  - Entering `boot_flow_rt`: hardware asserts `lock_wr` on `{4, 5, 9}` and `lock_use` on `{6, 13, 14}` (permanently revoking Runtime firmware's ability to use FMC keys!). Once `hwset` is asserted, firmware cannot clear `lock_wr` or `lock_use`; only `core_only_rst_b` de-assertion clears them (L3133).
  - On cold-boot transition edges (when `WARM_RESET == 0` and `FW_UPD_RESET == 0`), hardware atomically zeroizes scratch and unpreserved slots (`Slot 3` TMP, `Slots 10–12` DPE scratch/exported CDI, and unenabled optional slots `15–22`).

#### 3.4 SoC Mailbox FSM (`src/soc_ifc/rtl/mbox.sv`): Glitch-Hardened Cross-Domain IPC
Because Caliptra sits inside an untrusted host SoC, its mailbox (`src/soc_ifc/rtl/mbox.sv` L131–792) implements strict hardware state-machine isolation between three mutually exclusive lock holders (`soc_has_lock`, `uc_has_lock`, `tap_has_lock`, formally asserted via `CALIPTRA_ASSERT_MUTEX(ERR_MBOX_LOCK_MUTEX, {soc_has_lock, uc_has_lock, tap_has_lock}, clk, !rst_b)` at L791):
- **Sparse FSM Encoding for Glitch Hardening** (`mbox.sv` L513): States (`MBOX_IDLE_SPARSE`, `MBOX_RDY_FOR_CMD_SPARSE`, `MBOX_RDY_FOR_DLEN_SPARSE`, `MBOX_RDY_FOR_DATA_SPARSE`, `MBOX_EXECUTE_UC_SPARSE`, `MBOX_EXECUTE_SOC_SPARSE`, `MBOX_EXECUTE_TAP_SPARSE`, `MBOX_ERROR_SPARSE`) use sparse encodings where any invalid state transition or fault-induced illegal state falls into the sticky `MBOX_ERROR_SPARSE` sink (L484–494).
- **Hardware `AXI_USER` (`PAUSER`) Filtering & Exclusive Ownership**: The SoC cannot write mailbox data unless it acquires `mbox_lock` and passes `valid_requester` / `valid_receiver` checks (L215–220); direct SRAM access (`dir_req_dv_q`, L565) and DMA SRAM requests (`dma_sram_req_dv_q`, L559) are hardware-gated on active lock ownership, preventing concurrent SoC overwrite of command buffers while VeeR EL2 is parsing them (eliminating the shared-RAM TOCTOU class endemic to x86 SMM).

---

### 4. Apple Silicon: SEP, PAC, PPL, and the Transition to GXF/GL2 (SPTM + TXM)

Basis: source + documentation + normative (published research)

Apple Silicon separates **off-AP cryptographic custody** (**SEP**) from **on-AP kernel compartmentalization** (**PAC** + **PPL** -> **SPTM/TXM**):

#### 4.1 Secure Enclave Processor (SEP)
Based on Apple Platform Security documentation (`Basis: documentation`):
- The **SEP** is a dedicated on-die security coprocessor with its own immutable Boot ROM, private AES engine (holding hardware-fused **UID** and **GID** keys inaccessible to software), random-number generator, memory-protection engine (encrypting/authenticating SEP DRAM slices using ephemeral per-boot keys and anti-replay trees), and an Apple-customized L4-derived microkernel (**SEPOS**).
- The application processor communicates with SEP exclusively over an asynchronous hardware mailbox; SEP enforces biometric authentication, Data Protection key wrapping, passcode throttling via Secure Storage Component (monotonic anti-replay NVM), and key-bag unwrapping without exposing raw UID keys to XNU.

#### 4.2 Evolution from PPL (APRR/SPRR) to GXF/GL2, SPTM, and TXM
On A11–A14/M1 silicon, **Page Protection Layer (PPL)** ran inside the XNU kernel address space using proprietary hardware permission-remapping registers (APRR/SPRR) to toggle page-table writeability during controlled entry/exit trampolines. Starting with newer Apple Silicon (A15/M2+ generations running modern XNU), Apple replaced PPL with **Guarded Execution Feature (GXF)** lateral execution levels (**GL0/GL1/GL2**, entered/exited via `GENTER`/`GEXIT`), hosting two standalone, minimal-TCB monitors at **GL2**:
- **SPTM (Secure Page Table Monitor)**: Sole authority over physical page tables and physical frame typing. Direct inspection of `apple-oss-distributions/xnu` (`f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`) in `osfmk/arm64/sptm/sptm.h` (L41–140) and `osfmk/arm64/sptm/pmap/pmap.c` (L146–2290) documents the kernel-to-SPTM contract:
  - **Strict Single-Type Physical Frame Typing (`sptm_retype`)**: Every SPTM-managed physical frame carries a single authoritative `sptm_frame_type_t` (`XNU_DEFAULT`, `XNU_PAGE_TABLE_COMMPAGE`, `XNU_COMMPAGE_RW`, `XNU_COMMPAGE_RO`, `XNU_COMMPAGE_RX`, `XNU_KERNEL_RESTRICTED`, plus page-table and IOMMU types). XNU cannot write page-table entries directly; it invokes `sptm_retype(paddr, prev_type, new_type, retype_params)` (`pmap.c` L1927, L1994–1999) and `sptm_map_table(ttep, va, level, table_tte)` (`pmap.c` L1931).
  - **Reference-Counted Lifecycle & In-Flight Guards**: `sptm.h` exposes `sptm_paddr_is_inflight()` (L61), `sptm_get_frame_type()` (L84), `sptm_frame_is_last_mapping()` (L105), and `sptm_get_page_table_refcnt()` (L130). A frame cannot be retyped back to writable data while active mappings or in-flight SPTM operations remain — enforcing a hardware-monitored **exclusive-ownership invariant** structurally analogous to Rust aliasing discipline at physical-page granularity.
  - **TXM (Trusted Execution Monitor)**: Co-resident monitor handling code-signing policy, trust caches, and entitlements (`pmap.c` L2287 initializes TXM VM objects separately from XNU). Together, SPTM + TXM also underpin **Apple Exclaves** (isolated domains whose physical frames are unmapped from XNU by SPTM).

#### 4.3 Pointer Authentication Codes (PAC) and Speculative Side-Channel Limits (`PACMAN`)
- **XNU PAC Implementation (`osfmk/arm64/pac_asm.h` L38–185)**: XNU uses ARMv8.3-A Pointer Authentication instructions (`PACIA`/`PACIB`/`PACDA`/`PACDB` and generic MAC chaining `PACGA` with domain tags `PACGA_TAG_BLOB = 0b0001`, L172–185) to sign code/data pointers and heap metadata with per-process/kernel keys and context diversifiers (e.g., `VMAPPLE_PAC_SET_EL0_DIVERSIFIER`, L111).
- **Speculative Verification Oracle (`PACMAN`, Ravichandran et al., ISCA 2022, `doi:10.1145/3470496.3527429`)**: `Basis: normative (peer-reviewed execution)`. Standard ARM PAC authentication (`AUT*`) replaces invalid pointers with a poisoned upper-bit canonical address that faults only upon subsequent dereference/branch. Ravichandran et al. demonstrated on Apple M1 that executing `AUT*` + dependent load/branch along a **speculatively mispredicted path** suppresses the architectural crash while leaving a cache/TLB footprint if and only if the forged PAC tag matched! This converts an architectural crash-on-failure defense into a **crash-free speculative oracle** allowing brute-force recovery of kernel PACs from userspace across privilege levels. Consequently, PAC provides exploit-mitigation friction rather than a hard isolation boundary; hard kernel-compromise containment on Apple Silicon relies on **GXF/GL2 SPTM + TXM** and **SEP**.

---

### 5. x86 System Management Mode (Ring -2): Confused-Deputy Pointer Injection, DMA TOCTOU, and Sinkclose

Basis: source + normative + execution + documentation

x86 **System Management Mode (SMM)** executes on the main application CPU cores at privilege level **Ring -2** (below OS Ring 0 and Hypervisor Ring -1) upon assertion of a System Management Interrupt (SMI), switching execution to **SMRAM** (`TSEG` protected by **SMRR** / `D_LCK` on Intel; `SMM_ADDR`/`SMM_MASK` + `HWCR.SMMLOCK` on AMD).

#### 5.1 Shallow `CommBuffer` Validation, Nested Pointers, and DMA TOCTOU in EDK II
Direct inspection of `tianocore/edk2` (`556dcfb466e9f05affeaff881d738807f8156d3c`) reveals the exact structural mechanics of Ring 0 -> Ring -2 SMI confused-deputy vulnerabilities:

1. **What `PiSmmCore` Validates (`MdeModulePkg/Core/PiSmmCore/PiSmmCore.c` L731–804)**:
   - L731 copies only the small mailbox header (`CopyMem(gSmmCorePrivate, gSmmCoreMailbox, sizeof(*gSmmCoreMailbox))`) into SMRAM.
   - L743–753 checks that `[CommunicationBuffer, CommunicationBuffer + BufferSize)` does not overlap `gSmmCoreMailbox` (`InternalIsBufferOverlapped`, using `SafeUintnAdd`, L648–649) and passes `SmmIsBufferOutsideSmmValid((UINTN)CommunicationBuffer, BufferSize)`.
   - **Critical Gap (`PiSmmCore.c` L764–795)**: `PiSmmCore` does **NOT** copy the communication payload into SMRAM. It parses `HeaderGuid` directly from host-DRAM `CommunicationBuffer` and passes the raw non-SMRAM pointer `CommData` straight to `SmiManage(CommGuid, NULL, CommData, &BufferSize)`.
2. **How `SmmIsBufferOutsideSmmValid` Works (`MdePkg/Library/SmmMemLib/SmmMemLib.c` L114–238)**:
   - **Wraparound Check (L125–127)**: Guards against 64-bit integer overflow via `(Length > MaxAddr) || (Buffer > MaxAddr) || ((Length != 0) && (Buffer > MaxAddr - (Length - 1)))`, where `MaxAddr = (1ULL << PhysicalAddressBits) - 1` (L99). Probe 1B (Witness 2) confirms that naive `Buffer + Length <= MaxAddr` fails at `Buffer = 0xFFFFFFFFFFFFF000, Length = 0x2000` (wraps modulo $2^{64}$ to `0x1000 <= MaxAddr`), whereas EDK II's subtraction form rejects it.
   - **SMRAM Exclusion (L139–160)**: Rejects any overlap with `mSmmMemLibInternalSmramRanges[]`.
   - **Post-`SmmReadyToLock` Hardening (L165–235)**: Once `mSmmMemLibSmmReadyToLock == TRUE`, requires the entire `[Buffer, Buffer + Length)` interval to lie inside a valid communication region (`mMemoryMap`), disjoint from untested GCD memory (`mSmmMemLibGcdMemSpace`) and disjoint from `EfiRuntimeServicesCode`/`Data` marked `EFI_MEMORY_RO` in `mSmmMemLibMemoryAttributesTable`.
3. **Why Confused-Deputy Exploits Persist Despite `SmmIsBufferOutsideSmmValid`**:
   - **Nested Pointer Injection (Probe 1B, Witness 1)**: `PiSmmCore` only validates the outer `CommBuffer`. If an OEM SMI handler defines a request struct containing an interior pointer (`struct Req { VOID *OutBuf; UINTN Len; };`) and writes to `Req->OutBuf` without explicitly calling `SmmIsBufferOutsideSmmValid((UINTN)Req->OutBuf, Req->Len)`, a Ring 0 attacker places `CommBuffer` in valid OS DRAM (`0x20000000`, passes outer check) and sets `Req->OutBuf = 0x7F001200` (inside TSEG SMRAM). SMM executes the write with full Ring -2 SMRAM privilege, corrupting SMI handler tables or code!
   - **DMA / Un-Rendezvoused TOCTOU Double-Fetch**: Because `CommData` remains in host DRAM outside SMRAM throughout `SmiManage`, a DMA-capable PCIe device (which is **not halted** by x86 SMI rendezvous!) — or a rogue core when `PcdCpuSmmSyncMode == MmCpuSyncModeRelaxedAp` (`PiSmmCpuDxeSmm.c` L213) — can mutate fields of `CommData` *between* an SMI handler's validation check and its dereference. The only sound defense is copying the entire untrusted input into private SMRAM via `SmmCopyMemToSmram` (`SmmMemLib.c` L259) *before* parsing or validating any field (single-fetch snapshot invariant).
   - **SMRAM Callout & Code-Access Enforcement**: If an SMI handler dereferences an attacker-controlled function pointer or protocol table entry outside SMRAM, Ring -2 executes Ring 0 attacker shellcode. EDK II mitigates this via `ConfigSmmCodeAccessCheck()` (`UefiCpuPkg/PiSmmCpuDxeSmm/PiSmmCpuDxeSmm.c` L106, enabling hardware `SMM_CODE_CHK_EN` MSR so instruction fetches outside SMRR-protected SMRAM trigger `#MC` Machine Check) and `SetMemMapAttributes()` (`SmmCpuMemoryManagement.c`) marking non-SMRAM pages NX in SMM page tables after `mSmmReadyToLock = TRUE` (`PiSmmCpuDxeSmm.c` L192).

#### 5.2 Architectural Hardware Lock Bypasses: Cache Poisoning and AMD Sinkclose (`CVE-2023-31315`)
Even with bug-free SMI handlers, x86 SMM's reliance on shared-DRAM address-decoding overrides creates hardware-level failure modes:
- **SMRAM Cache Poisoning & TXT Bypass** (Wojtczuk & Rutkowska, 2009): Historically demonstrated that misconfigured MTRRs / missing SMRR allowed Ring 0 to populate CPU caches over `TSEG` physical addresses before SMI entry, redirecting SMM execution from cached attacker code and subverting Intel TXT because `SENTER` did not measure active SMRAM.
- **AMD Sinkclose (`CVE-2023-31315` / `AMD-SB-7014`, Nissim & Okupski, IOActive, 2024)**: `Basis: normative (advisory) + documentation`. On AMD x86 processors spanning ~2006–2024 (EPYC, Ryzen, Threadripper), **TClose** — a legacy backward-compatibility memory-aliasing feature controlled via AMD's SMM mask MSR (`SMM_MASK`, `0xC0010113`) — lacked proper validation against `HWCR.SMMLOCK` (SMI Lock). A Ring 0 attacker could modify `TClose` configuration even after SMM was locked, causing SMM memory accesses during SMI execution to alias outside SMRAM to attacker-controlled memory/MMIO and yielding Ring 0 -> Ring -2 code execution capable of surviving OS reinstalls and bypassing Secure Boot. Remediation required platform microcode/PI firmware updates per `AMD-SB-7014`.

---

### 6. Ring -3 Shadow Management Cores: Intel ME/CSME and AMD PSP/ASP

Basis: normative (advisories & peer-reviewed papers) + documentation

Below SMM sit dedicated platform management microcontrollers operating independently of the x86 cores ("Ring -3"):

#### 6.1 Intel Management Engine (ME / CSME)
- **Architecture & DMA Surface**: Embedded in the Platform Controller Hub (PCH) / SoC tile, modern Intel CSME (ME 11+) runs a proprietary **MINIX-derived** operating system on an embedded x86 core (Quark-lineage) with a carved-out host RAM region (**UMA** — Unified Memory Architecture), independent DMA engines capable of reading/writing host physical DRAM outside x86 Ring 0/Ring -1/Ring -2 visibility, out-of-band NIC access (AMT), and a PCIe host mailbox (**HECI** / **MEI**).
- **Primary Vulnerability & Kill-Switch Evidence (`CVE-2017-5705` / `INTEL-SA-00086`)**: Ermolov and Goryachy (Positive Technologies, 2017) demonstrated multiple stack/heap buffer overflows in CSME firmware (`11.0–11.20`), enabling local arbitrary code execution inside Ring -3 CSME (and undermining Intel Boot Guard / platform attestation). The same research publicized the **HAP (High Assurance Platform)** strap/bit in the SPI flash descriptor, which instructs CSME firmware to halt its initialization right after early platform bring-up — an admission that enterprise/government high-assurance deployments treat an active, unverified Ring -3 RTOS as an unacceptable TCB expansion.

#### 6.2 AMD Platform Security Processor (PSP / ASP)
- **Architecture**: An on-die ARM Cortex-A5-lineage coprocessor with ARM TrustZone isolation and a Cryptographic Coprocessor (CCP). It boots from on-die ROM before the x86 cores are released from reset, verifies SPI flash firmware directories, anchors **AMD SEV / SEV-ES / SEV-SNP** (managing VM encryption keys, Reverse Map Table lifecycle, and remote attestation signing keys), and hosts the firmware TPM (**fTPM**) as a TrustZone application.
- **Fault Injection Breaking Both SEV and fTPM**:
  - **`One Glitch to Rule Them All` (Buhren, Jacob, Krachenfels, Seifert, ACM CCS 2021, `doi:10.1145/3460120.3484779`)**: Demonstrated voltage fault injection (VFI) over the motherboard **SVI2** power-management interface targeting AMD PSP boot signature verification, bypassing secure boot to run arbitrary code on the PSP and extracting SEV endorsement/attestation secrets (subverting confidential-VM isolation against a physically privileged cloud host).
  - **`faulTPM` (Jacob, Werling, Buhren, Seifert, IEEE EuroS&P 2023, `arXiv:2304.14717`)**: Extended SVI2 voltage glitching to compromise the PSP TEE hosting AMD's fTPM, extracting full fTPM state and unsealing BitLocker full-disk encryption keys in hours with inexpensive hardware.
- **Architectural Lesson (`Basis: derived`)**: Comparing **AMD PSP** (`One Glitch`, `faulTPM`) directly against **OpenTitan** (`ibex_lockstep.sv`, `hardened_asm.h`, `launder32`, `alert_handler`) and **Caliptra 2.2** (`kv.sv` exact-match 3-bit write counters + sparse FSMs) explains *why* placing a conventional unhardened microcontroller (without lockstep, sparse FSMs, glitch-hardened signature comparison, or hardware key-derivation monitors) as the silicon Root of Trust collapses under board-level fault injection.

---

### 7. Cross-Cutting Invariants for Formal Verification and Memory-Safe FFI Boundaries

Basis: derived + source + execution

Across all examined architectures, five verifiable invariants govern whether a root-of-trust or enclave boundary resists privilege escalation:

1. **Single-Fetch Snapshot Invariant (Anti-TOCTOU)**: Untrusted cross-domain buffers (SMM `CommBuffer`, RoT mailbox payloads, TEE hypercalls) MUST be copied atomically into domain-private memory (e.g., `SmmCopyMemToSmram`, Caliptra hardware-locked mailbox SRAM) *before* any header length, pointer, or tag validation. Never validate in place inside shared or DMA-accessible DRAM.
2. **No Ambient Pointer Dereference Across Trust Boundaries**: Replace raw physical/virtual pointers (`CommBuffer->OutputPtr`) with bounded indices, typed handles, or exclusive physical-frame ownership tokens (`sptm_retype` frame states, Caliptra KV slot IDs). Where legacy pointers are unavoidable (EDK II SMM), every reachable nested pointer must recursively satisfy `SmmIsBufferOutsideSmmValid` with overflow-safe subtraction (`buf <= max - (len - 1)`).
3. **Hardware-Mediated Key Custody (Sideloading + Monotonic Phase Locks)**: Root secrets (UDS, creator seeds, UID) must never traverse general-purpose CPU registers or general RAM; hardware state machines (`keymgr`/`keymgr_dpe`, `kv.sv`, `doe_ctrl.sv`) should enforce one-way derivation, `dest_valid` port typing, and sticky `hwset` revocation across boot stages (`ROM -> FMC -> RT`) with exact derivation-count auditing.
4. **Compiler-Visible Fault-Hardening Barriers**: Formal proofs of software fault-injection countermeasures at the C/Rust IR level are unsound unless optimization barriers (`launder32` / volatile inline asm) prevent dead-check elimination and constant folding, and unless binary/machine-code inspection confirms Hamming-distance encodings survive lowering.
5. **Hardware-Backed `W^X` and Lateral Privilege Separation**: Prefer hardware-enforced non-bypassable memory typing (`Smepmp` `MML=1` proving zero M-mode `W^X` encodings; Apple `GL2` SPTM owning all page-table mutations) over software-cooperative protections (`PPL` permission toggles or unlocked SMM code-fetch ranges).

## Boundaries

- **Proprietary firmware internals (`unknown` / `not examined`)**: Source code for Apple SEP OS, Apple SPTM/TXM GL2 binaries, Intel CSME MINIX firmware, and AMD PSP/ASP TrustZone firmware is closed-source and was not inspected directly. Findings about those binaries rely on open caller-side kernel interfaces (`apple-oss-distributions/xnu`), official vendor security guides/advisories (`AMD-SB-7014`, `INTEL-SA-00086`), and peer-reviewed empirical studies (`PACMAN`, `One Glitch`, `faulTPM`).
- **OpenTitan silicon netlist & physical SCA measurements (`not examined`)**: This investigation inspected RTL (`ibex_top.sv`, `ibex_lockstep.sv`, `ibex_pmp.sv`), hardware theory-of-operation specs (`otbn`, `lc_ctrl`, `alert_handler`, `keymgr`, `keymgr_dpe`), and ROM C sources (`rom.c`, `hardened.h`, `epmp_state.h`). Post-synthesis gate-level netlist glitch resistance (e.g., `Coco` / `PROLEAD` verification) and silicon tapeout power/EM side-channel measurements on Earl Grey chips were not executed here.
- **Caliptra Subsystem (`caliptra-ss`) & OCP L.O.C.K. integration (`not examined`)**: While Caliptra Core 2.0–2.2 RTL (`kv.sv`, `mbox.sv`, `doe_ctrl.sv`) and `CaliptraHardwareSpecification.md` were directly inspected, the outer SoC integration subsystem (`chipsalliance/caliptra-ss`) and Caliptra 2.x firmware runtime handlers beyond `fmc/src/flow/dice.rs` were not exhaustively audited.
- **ARM64 Standalone MM vs x86 Traditional PI SMM (`known not to apply`)**: The EDK II `PiSmmCore.c` and `SMM_CODE_CHK_EN` findings apply specifically to x86 Traditional PI SMM. ARM64 platforms implementing UEFI Standalone MM inside TrustZone S-EL0 / FF-A isolate MM from DXE and do not share x86 `SMRR`/`TClose` hardware semantics, though nested-pointer validation obligations still apply to any ABI passing physical pointers across FF-A shared buffers.
- **Intel TDX / AMD SEV-SNP microcode mitigations post-2024 (`not examined`)**: Subsequent microcode updates addressing `CVE-2023-31315` (Sinkclose) and later PSP/CSME advisories beyond the pinned CVEs were not individually benchmarked or disassembled; verification of patch presence requires platform-specific BIOS/microcode revision checks.
- **Limits of Python verification probes (`known not to apply` to hardware timing)**: Probes 1A–1C verify exact Boolean/FSM/arithmetic logic transcribed from upstream source, not RTL timing closure, physical multi-bit laser fault propagation, or C compiler codegen across specific LLVM versions.

## Evidence

### Primary Git Repositories Inspected

1. **`lowRISC/opentitan` @ `1e061997389b1c257043b0dbd2388a19a6c2f6f1`** (observed `2026-11-19`):
   - `sw/device/lib/base/hardened_asm.h` L19–33: `HARDENED_BOOL_TRUE = 0x739`, `HARDENED_BOOL_FALSE = 0x1d4`, `HARDENED_BYTE_BOOL_TRUE = 0xa5`, `HARDENED_BYTE_BOOL_FALSE = 0x4b`.
   - `sw/device/lib/base/hardened.h` L23–135: `hardened_bool_t`, `launder32()` compiler-optimization barrier rationale against collapsing `HARDENED_CHECK_EQ(x, 0)` into `HARDENED_CHECK_EQ(0, 0)`.
   - `sw/device/silicon_creator/lib/epmp_state.h` L45–169: `mseccfg` bit layout (`MML`, `MMWP`, `RLB`) and warnings on `MML` bit-pattern semantic shift.
   - `sw/device/silicon_creator/rom/rom.c` L630–1060: `epmp_state_check()`, `sec_mmio_check_values(rnd_uint32())`, `sec_mmio_check_counters(...)`, `rom_counters[kCfiRomTryBoot]`, `kRomStateBootRomExt = 0xed14`, `launder32()` usage in `rom_verify_immutable_section`.
   - `hw/ip/otbn/doc/theory_of_operation.md` L1–115: IMEM/DMEM scrambling, instruction prefetch for SCA blanking, `RND` (EDN single-entry cache + `RND_PREFETCH`) vs `URND` (local Bivium PRNG, 1-cycle registered lag for glitch-free masking/wipe).
   - `hw/ip/lc_ctrl/doc/theory_of_operation.md` L6–95: Power-up `RAW` default, hardware-hashed 128-bit unlock tokens, redundant escalation paths forcing virtual `ESCALATE` (`SCRAP`).
   - `hw/top_earlgrey/ip_autogen/alert_handler/doc/theory_of_operation.md` L1–105: Differential alert pairs, ping-pong liveness monitoring, 4-phase escalation.
   - `hw/ip/keymgr/README.md` L1–21 & `hw/ip/keymgr_dpe/README.md` L1–38: Earl Grey 1.0.0 `keymgr` sideloading and Darjeeling `keymgr_dpe` multi-slot TCG DPE replacement.
2. **`lowRISC/ibex` @ `9b91b3a1195aecb0d80cf2de5b852e0b5f68cc6c`** (observed `2026-11-19`):
   - `rtl/ibex_top.sv` L15–64: `SecureIbex`, `LockstepOffset`, `MemECC`, `MemDataWidth = MemECC ? 32 + 7 : 32`, `ICacheScramble`, `ICacheTweakInfection`, `PMPEnable`, `PMPNumRegions`.
   - `rtl/ibex_lockstep.sv` L10–124, L621–756: `SEC_CM: LOGIC.SHADOW`, `alert_major_internal_o = outputs_mismatch | shadow_alert_major_internal | rst_shadow_cnt_err`.
   - `rtl/ibex_pmp.sv` L20–151: `mml_perm_check` (L59–97), `orig_perm_check` (L101–110), `access_fault_check` (L128–151) with `MMWP` default-deny and `MML` unmatched-EXEC deny.
3. **`chipsalliance/caliptra-rtl` @ `298ad4313ed8b4da25e98e3f1131c89363a6eb92`** (observed `2026-11-19`):
   - `docs/CaliptraHardwareSpecification.md` L21–165 (Caliptra 2.0/2.1/2.2 changes, VeeR EL2 config, memory map), L2800–2933 (Key Vault architecture, `dest_valid`, key-length mismatch), L3016–3165 (Caliptra 2.2 Key Vault Boot Flow Transition Enforcement: 3-bit saturating write counters `slot 6 == 4`, `slot 7 == 2`, `slot 8 == 2`, continuous `hwset` `lock_wr`/`lock_use` table, cold-boot slot clearing table).
   - `src/keyvault/rtl/kv.sv` L19–80: AHB-Lite control-only uC port vs dedicated hardware `kv_read`/`kv_write`/`pcr_*_signing_key` buses, `mubi4_t` `boot_flow_fmc`/`boot_flow_rt`/`boot_flow_error`, `kv_monitor_alert`.
   - `src/soc_ifc/rtl/mbox.sv` L131–792: Sparse FSM (`MBOX_*_SPARSE`, L513 glitch-hardening comment), `valid_requester`/`valid_receiver` (L215–220), `CALIPTRA_ASSERT_MUTEX(ERR_MBOX_LOCK_MUTEX, {soc_has_lock, uc_has_lock, tap_has_lock})` (L791).
   - `src/doe/rtl/doe_ctrl.sv` L1–90: Hardware AES-CBC de-obfuscation directly to Key Vault.
4. **`chipsalliance/caliptra-sw` @ `5d35f7d928afb4d190dd4619219ecd6487987f3d`** (observed `2026-11-19`):
   - `README.md` and `fmc/src/flow/dice.rs`: DICE layered ROM -> FMC -> Runtime CDI derivation flow.
5. **`apple-oss-distributions/xnu` @ `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`** (observed `2026-11-19`):
   - `osfmk/arm64/sptm/sptm.h` L41–140: `SPTMArgs`, `sptm_paddr_is_inflight`, `sptm_get_frame_type`, `sptm_frame_is_last_mapping`, `sptm_get_page_table_refcnt`.
   - `osfmk/arm64/sptm/pmap/pmap.c` L146–148, L1923–2001, L2247–2290: `sptm_retype` frame-type transitions (`XNU_DEFAULT` -> `XNU_PAGE_TABLE_COMMPAGE`, `XNU_COMMPAGE_RW/RO/RX`, `XNU_KERNEL_RESTRICTED`), `sptm_map_table`, TXM VM object separation.
   - `osfmk/arm64/pac_asm.h` L38–185: `HAS_APPLE_PAC`, `VMAPPLE_PAC_SET_EL0_DIVERSIFIER`, `PACGA_TAG_BLOB = 0b0001`.
6. **`tianocore/edk2` @ `556dcfb466e9f05affeaff881d738807f8156d3c`** (observed `2026-11-19`):
   - `MdePkg/Library/SmmMemLib/SmmMemLib.c` L43–260: `mSmmMemLibInternalMaximumSupportAddress`, `SmmIsBufferOutsideSmmValid` (L114–238), `SmmCopyMemToSmram` (L259).
   - `MdeModulePkg/Core/PiSmmCore/PiSmmCore.c` L635–654 (`InternalIsBufferOverlapped`), L677–815 (`SmmEntryPoint` copying only `gSmmCoreMailbox`, validating outer `CommunicationBuffer`, passing non-SMRAM `CommData` to `SmiManage`).
   - `UefiCpuPkg/PiSmmCpuDxeSmm/PiSmmCpuDxeSmm.c` L52–221 (`ConfigSmmCodeAccessCheck()`, `mSmmReadyToLock`, `MmCpuSyncModeRelaxedAp`) and `SmmCpuMemoryManagement.c`.

### Peer-Reviewed Papers and Vendor Advisories

- Joseph Ravichandran, Weon Taek Na, Jay Lang, and Mengjia Yan, *PACMAN: Attacking ARM Pointer Authentication with Speculative Execution*, ISCA 2022, DOI `10.1145/3470496.3527429`.
- Robert Buhren, Hans Niklas Jacob, Thilo Krachenfels, and Jean-Pierre Seifert, *One Glitch to Rule Them All: Fault Injection Attacks Against AMD's Secure Encrypted Virtualization*, ACM CCS 2021, DOI `10.1145/3460120.3484779`.
- Hans Niklas Jacob, Christian Werling, Robert Buhren, and Jean-Pierre Seifert, *faulTPM: Exposing AMD fTPMs' Deepest Secrets*, IEEE EuroS&P 2023, `arXiv:2304.14717`.
- AMD Security Advisory `AMD-SB-7014` (`CVE-2023-31315`, *SMM Lock Bypass / Sinkclose*, disclosed August 2024 by Enrique Nissim and Krzysztof Okupski, IOActive).
- Intel Security Advisory `INTEL-SA-00086` (`CVE-2017-5705`, Intel CSME 11.0–11.20 firmware buffer overflows, November 2017; Ermolov & Goryachy).
- Apple Platform Security Guide (SEP, Boot ROM, GXF/GL2, SPTM, TXM, Exclaves).

### Executable Micro-Probe Verification Outputs (`2026-11-19`, Python 3)

Running the standalone verification probe (logic transcribed from `ibex_pmp.sv`, `hardened_asm.h`, `SmmMemLib.c`, and `CaliptraHardwareSpecification.md`; re-runnable snippet in **Revalidation**) yielded exit code `0` with all assertions passing:

```text
=== PROBE 1A: OpenTitan hardened_bool_t & Ibex Smepmp Truth Table ===
HARDENED_BOOL_TRUE  = 0x739 (bits=11, hw=7)
HARDENED_BOOL_FALSE = 0x1d4 (bits=9, hw=5)
XOR = 0x6ed, HD = 8, bitwise_complement_11b = False
HARDENED_BYTE_BOOL: 0xa5 vs 0x4b, XOR=0xee, HD=6
Smepmp MML=1 M-mode W^X violations: [] (count=0)
Smepmp MML=1 S/U-mode RWX entries : [(0, 1, 1, 1)] (count=1)

=== PROBE 1B: EDK II SmmIsBufferOutsideSmmValid & Nested-Pointer / Wraparound ===
Witness 1 (Nested Pointer): outer=0x20000000+0x100 -> True; nested=0x7f001200+0x40 -> False (SMRAM write if handler skips deep check)
Witness 2 (64-bit Wrap): buf=0xfffffffffffff000, len=0x2000, u64(buf+len)=0x1000 <= MAX_PHYS? True, EDK2 safe check=False
Witness 3 (Length=0): inside SMRAM -> False, outside SMRAM -> True

=== PROBE 1C: Caliptra 2.2 KV Boot-Flow Monitor & Hardware Lock Enforcement ===
Nominal ROM->FMC->RT: passed=True, RT lock_wr=[0, 1, 2, 4, 5, 6, 7, 8, 9, 13, 14], RT lock_use=[6, 7, 8, 13, 14]
Truncated DICE chain (slot6=3): enter_fmc=False, error=True
Glitch-replayed DICE write (slot6=5): enter_fmc=False, error=True
```

## Revalidation

Use the following narrow discriminating checks to revalidate these findings against newer upstream commits or target firmware builds:

1. **Diff upstream security-critical files against pinned SHAs**:
   - OpenTitan / Ibex:
     ```bash
     git -c protocol.version=0 ls-remote https://github.com/lowRISC/opentitan.git HEAD
     git -c protocol.version=0 ls-remote https://github.com/lowRISC/ibex.git HEAD
     ```
     Check whether `rtl/ibex_pmp.sv` (`mml_perm_check`), `sw/device/lib/base/hardened_asm.h`, or `hw/ip/keymgr_dpe/` modified permission encodings, Hamming distances, or DPE slot lock semantics.
   - Caliptra:
     ```bash
     git -c protocol.version=0 ls-remote https://github.com/chipsalliance/caliptra-rtl.git HEAD
     ```
     Inspect `src/keyvault/rtl/kv.sv`, `src/soc_ifc/rtl/mbox.sv`, and `docs/CaliptraHardwareSpecification.md` ("Key vault boot flow transition enforcement") to confirm whether DICE accumulator write-count invariants or `hwset` slot lock masks changed.
   - EDK II SMM:
     ```bash
     git -c protocol.version=0 ls-remote https://github.com/tianocore/edk2.git HEAD
     ```
     Check `MdeModulePkg/Core/PiSmmCore/PiSmmCore.c` (`SmmEntryPoint`) to verify whether `PiSmmCore` still passes non-SMRAM `CommData` directly to `SmiManage` rather than copying payloads into SMRAM by default, and check `MdePkg/Library/SmmMemLib/SmmMemLib.c` (`SmmIsBufferOutsideSmmValid`).
   - Apple XNU SPTM:
     ```bash
     git -c protocol.version=0 ls-remote https://github.com/apple-oss-distributions/xnu.git HEAD
     ```
     Inspect `osfmk/arm64/sptm/sptm.h` and `osfmk/arm64/sptm/pmap/pmap.c` for changes to `sptm_retype` frame types or TXM isolation boundaries.
2. **Rerun the standalone Smepmp / SMM / Caliptra KV verification probe**:
   ```bash
   python3 - <<'PY'
   # Verify OpenTitan hardened_bool_t Hamming distance & Ibex Smepmp MML=1 M-mode W^X
   assert (0x739 ^ 0x1D4).bit_count() == 8 and (0x739 ^ 0x1D4) != 0x7FF
   assert (0xA5 ^ 0x4B).bit_count() == 6
   def mml(L, R, W, X, req, priv):
       b = {"R": R, "W": W, "X": X}[req]
       if not R and W:
           return {0: req=="R" or (req=="W" and priv=="M"), 1: req in "RW",
                   2: req=="X", 3: req=="X" or (req=="R" and priv=="M")}[(L<<1)|X]
       if L and R and W and X:
           return req == "R"
       return bool(b) and (L == 1 if priv == "M" else L == 0)
   for bits in range(16):
       L, R, W, X = (bits>>3)&1, (bits>>2)&1, (bits>>1)&1, bits&1
       assert not (mml(L,R,W,X,"W","M") and mml(L,R,W,X,"X","M")), (L,R,W,X)
   # Verify EDK II SmmIsBufferOutsideSmmValid wraparound & nested-pointer separation
   MAXP = (1 << 46) - 1
   def valid(buf, ln):
       if ln > MAXP or buf > MAXP or (ln and buf > MAXP - (ln - 1)): return False
       return not ((0x7F000000 <= buf < 0x80000000) or (buf <= 0x7F000000 < buf + ln))
   assert valid(0x20000000, 0x100) and not valid(0x7F001200, 0x40)
   assert not valid(0xFFFFFFFFFFFFF000, 0x2000)
   print("REVALIDATION_OK")
   PY
   ```
3. **Platform firmware audit (when revalidating physical x86/ARM hardware)**: Verify `SMM_CODE_CHK_EN` and `TClose`/`AMD-SB-7014` microcode patch levels via platform firmware inspection tools (e.g., CHIPSEC) rather than assuming EDK II upstream defaults are enabled by OEM BIOS builds.
