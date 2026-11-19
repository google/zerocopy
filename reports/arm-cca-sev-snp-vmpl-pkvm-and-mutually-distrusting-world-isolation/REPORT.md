# Asymmetric and Mutually-Distrusting CPU World Isolation: Arm CCA, TrustZone, AMD SEV-SNP VMPL, Intel TDX, RISC-V PMP/sPMP, and Deprivileged-Host Hypervisors (pKVM/SeKVM)

## Summary

Modern hardware isolation architectures have shifted from **asymmetric two-world privilege hierarchies** (exemplified by classic Arm TrustZone, where Secure world can map and inspect Normal world memory) toward **mutually-distrusting execution domains** in which a resource-managing host or hypervisor controls scheduling and physical page allocation while being cryptographically or structurally excluded from guest memory and register state. Across six production and research architectures examined from primary ISA specifications, firmware/kernel source, and mechanized verification artifacts, five structural invariants govern soundness at the cross-world boundary:

1. **Dynamic physical-ownership transition requires a two-phase revoke-and-scrub barrier.** In Arm CCA (`ARM-software/arm-trusted-firmware`), transitioning a granule from `REALM` or `SECURE` back to `NS` MUST write `GPT_GPI_NO_ACCESS` (`0x0`), synchronize all PEs via `TLBI RPALOS` + `DSB OSH`, clean/invalidate caches to the Point of Physical Aliasing (`DC CIPAPA` / `DC CIGDPAPA`) for both the outgoing PAS and `PAS_NonSecure`, and only then publish `GPT_GPI_NS` (`0x9`). Direct `REALM -> NS` transitions admit a dirty-cacheline eviction race leaking confidential bytes into Normal world.
2. **Hardware page-ownership tables split mechanism from policy, shifting TCB correctness to lock ordering and state machines.** Arm CCA (2-level Root-PAS GPT + TF-RMM 15-state granule lock hierarchy), AMD SEV-SNP (Reverse Map Table `RMP` + guest-only `PVALIDATE` + strictly monotone `RMPADJUST` across `VMPL 0..3`), Intel TDX (SEAM-managed Secure EPT vs host Shared EPT discriminated by the GPA shared bit), and Linux pKVM (EL2-enforced host Stage-2 page tables + 4-state ownership lattice in `struct hyp_page`) all rely on exact synchronization between hardware metadata and software tracking structures.
3. **Host-facing exception and paravirtualization channels (`#VC`, `#VE`/`TDVMCALL`, SMC shared memory) form the dominant residual TCB attack surface.** Even when page-level confidentiality and integrity are enforced by hardware, untrusted host software can manipulate instruction-emulation return values (Iago/MMIO hazards in TDX `#VE`), inject asynchronous interrupts or `#VC` exceptions (WeSee, Heckler), or race shared-memory descriptors (TrustZone/OP-TEE double-fetch and SVSM `core_create_vcpu` VMSA TOCTOU).
4. **Coarse register-based physical partitioning saturates under fine-grained allocation.** RISC-V standard PMP CSRs (`pmpcfg*`/`pmpaddr*`, typically 8 or 16 hardware slots) encode power-of-two naturally aligned (`NAPOT`) or two-entry `TOR` ranges, forcing `O(log(size))` entries per non-power-of-two region and motivating Penglai's hardware-assisted page-table extensions (`sPMP` / guarded page tables).
5. **Formal verification of deprivileged-host monitors splits cleanly across three abstraction layers:** layered Coq simulation and weak-DRF relaxed-memory lifting over CompCert Clight (`VeriGu/SeKVM`, `columbia/VIA` for Arm CCA), ISA-grounded separation logic for assembly stubs (`rems-project/islaris` on Sail Armv8/v9), and separation-logic refinement types / bounded model checking for production C firmware (`rems-project/cn` on pKVM allocators; Fox et al. Isabelle/HOL + CBMC on Arm RMM).

## Applicability

This report synthesizes architectural rules, firmware/kernel implementations, cross-world boundary failure modes, and formal verification guarantees across six hardware-enforced isolation families and their pinned primary revisions:

| Architecture / System | Primary Pinned Subjects | Scope & Relationship |
|---|---|---|
| **Arm CCA (RME + TF-A + TF-RMM)** | `ARM-software/arm-trusted-firmware` (`0d2c4394...`), `TF-RMM/tf-rmm` (`8d7961df...`), `rems-project/sail-arm` (`5416ef6b...`, 2023-03 ASL snapshot), `columbia/VIA` (`06dcd851...`), Fox et al. OOPSLA 2023 (`doi:10.1145/3586040`) | Compares normative Sail Armv9.4-A base RME semantics against 2026 TF-A GPT/FIRME and TF-RMM Beta 3 implementations, plus two independent formal verification methodologies (Columbia VIA Coq vs Arm Isabelle/CBMC). |
| **Arm TrustZone (OP-TEE)** | `OP-TEE/optee_os` (`653d9849...`) | Establishes the asymmetric two-world baseline (`Normal` vs `Secure`) and cross-world shared-memory (`tmem`/`rmem`/`fmem`) marshaling and `READ_ONCE` double-fetch mitigations. |
| **AMD SEV-SNP & VMPL 0..3** | `coconut-svsm/svsm` (`2a40e72a...`), Schlueter et al. WeSee (`arXiv:2404.03526`) & Heckler | Examines intra-guest privilege ring attenuation (`RMPADJUST`, `PVALIDATE`, `RMPFlags`), VMPL0 SVSM VMSA creation TOCTOU defenses, and `#VC` validation against malicious hypervisor injection. |
| **Intel TDX** | `intel/confidential-computing.tdx.tdx-module` (`tdx_2.0` at `abd4d8ab...`), `torvalds/linux` (`4405c18c...`, `arch/x86/coco/tdx/tdx.c`) | Covers SEAM `TDG.VP.VMCALL` GPR/XMM scrubbing boundaries in TDX Module 2.0 paired with Linux guest `#VE` MMIO/PIO/MSR/CPUID decoding and hardening invariants. |
| **RISC-V Enclaves (Keystone / Penglai)** | `keystone-enclave/keystone` (`b8c23853...`), `Penglai-Enclave/Penglai-Enclave-sPMP` (`14da25ae...`) | Contrasts standard M-mode PMP CSR partitioning (`NAPOT`/`TOR` encoding and cross-hart IPI synchronization) against Penglai's scalable `sPMP` design for large/fragmented enclaves. |
| **Deprivileged-Host EL2 Hypervisors (pKVM / SeKVM)** | `torvalds/linux` (`4405c18c...`, `arch/arm64/kvm/hyp/nvhe/`), `VeriGu/sosp-paper211-ae` (`683c36a1...`), `VeriGu/SeKVM-4.18` (`75e3591e...`), `rems-project/islaris` (`c978e10f...`), `rems-project/cn` (`d1c60d17...`) | Examines how software-only EL2 micro-hypervisors achieve mutually-distrusting host/guest isolation without Arm RME hardware, and compares Coq layered simulation, Islaris machine-code proofs, and CN C refinement typing. |

**Version and feature distinctions:**
- Base Armv9.4-A RME in `rems-project/sail-arm` (2023-03 ASL snapshot) defines six `GPI` encodings (`NO_ACCESS`, `SECURE`, `NS`, `ROOT`, `REALM`, `ANY`). Current TF-A (`0d2c4394...`) additionally defines RME GPC extension encodings (`GPT_GPI_SA = 0x4`, `GPT_GPI_NSP = 0x5`, `GPT_GPI_NSO = 0xD`) and optional `FIRME_SUPPORT` locking hooks.
- Intel TDX Module `tdx_2.0` (`abd4d8ab...`) and `tdx_1.5` (`72232c15...`) maintain distinct `MRSEAM` SHA-384 measurements (enumerated on the `main` branch `859989ac...`); findings on `tdg_vp_vmcall` GPR filtering were inspected directly on `tdx_2.0`.
- Linux pKVM findings reflect mainline Linux (`4405c18c...`) non-VHE (`nvhe`) protected mode; SeKVM verification artifacts target Linux 4.18 (`VeriGu/SeKVM-4.18`).

## Findings

### 1. Architectural Taxonomy: Asymmetric Worlds vs. Mutually-Distrusting Domains

Basis: normative + source + derived

Hardware isolation designs differ along four orthogonal axes: (a) **trust symmetry** between domains, (b) **memory ownership enforcement layer** (physical address space table, reverse-map table, nested EPT/Stage-2, or physical range registers), (c) **cryptographic DRAM protection** against physical/DMA observers, and (d) **host-to-guest communication mediation**.

| System | Execution Worlds / Rings | Physical Isolation Mechanism | Memory Encryption | Host Can Read Guest RAM? | Guest Can Read Host Shared RAM? | Trusted Enforcing TCB |
|---|---|---|---|---|---|---|
| **Arm TrustZone (OP-TEE)** | 2 worlds (`NS`, `S`), EL0–EL3 | AXI `NS` bit + TZASC/TZPC static/coarse regions | Platform-optional | No | **Yes (asymmetric)** — Secure world maps NS RAM directly | EL3 Monitor + S-EL1/S-EL2 Trusted OS |
| **Arm CCA (RME)** | 4 worlds (`NS`, `S`, `Realm`, `Root`), 4 PAS | 2-level **GPT** in Root PAS + hardware **GPC** on every access & TTW | Platform memory encryption (Realm MEC/PoPA) | No (`GPCFault`) | Only explicitly NS-mapped IPAs (`PAS_NonSecure`) | Root EL3 (TF-A GPT) + R-EL2 (TF-RMM) |
| **AMD SEV-SNP + SVSM** | Host VMM + Guest **VMPL 0..3** | **RMP** (Reverse Map Table) + `PVALIDATE` + `RMPADJUST` | Per-ASID AES-128-XEX (SME/SEV) | No (ciphertext + `#NPF`/RMP integrity) | Yes via `C=0` shared PTEs (GHCB/MMIO) | AMD PSP firmware + CPU RMP hardware + VMPL0 SVSM |
| **Intel TDX** | Host VMM + **SEAM** + TD Guest (`L0` + optional L2 partitions) | **Secure EPT (SEPT)** vs Shared EPT (GPA `S`-bit) | Per-KeyID AES-XTS (MKTME) + MAC/integrity (TDX 1.5/2.0) | No (KeyID separation + SEPT access control) | Yes via GPA `S=1` shared pages | CPU SEAM hardware + signed TDX Module (`MRSEAM`) |
| **RISC-V Keystone / Penglai** | M-mode SM + Untrusted OS (S) + Enclave (S/U) | **PMP** CSRs (8/16/64 slots) / Penglai **sPMP** + Guarded PT | Optional (external memory controller) | No (M-mode PMP denies OS access to EPM) | Only designated Untrusted Shared Memory (UTM) | M-mode Security Monitor (OpenSBI/Keystone SM) |
| **Linux pKVM / SeKVM** | Untrusted Host (NS-EL1) + Micro-Hypervisor (NS-EL2) + Guests | **EL2 Stage-2 page tables applied to Host** + Guest Stage-2 | Software-only (relies on EL2 isolation, no DRAM crypto) | No (Host Stage-2 unmaps guest-owned PFNs) | Only explicitly shared PFNs (`SHARED_BORROWED`) | Minimal NS-EL2 `nvhe` hyp / SeKVM core |

**Key structural contrast (Derived):** Classic TrustZone relies on *one-way* distrust: Normal world cannot access Secure memory, but Secure world (OP-TEE) holds unrestricted physical visibility over Normal world memory (`MEM_AREA_NSEC_SHM` and dynamic NS DDR mappings). By contrast, Arm CCA introduces **mutual distrust between Secure and Realm worlds** in addition to Normal vs. Realm: neither Secure world nor Normal world may inspect Realm granules, and Realms cannot inspect Secure granules—both are mediated exclusively by Root EL3 GPT transitions.

---

### 2. Arm CCA: 4-World Physical Address Spaces, Dynamic GPT, and TF-RMM Concurrency

Basis: normative + source + execution

#### 2.1 Sail Armv9.4-A Granule Protection Check Semantics

In the normative Armv9.4-A Sail specification (`rems-project/sail-arm`, `arm-v9.4-a/src/v8_base.sail`), every physical memory access—**including every stage-1 and stage-2 translation table walk descriptor fetch** (`FetchDescriptor`, lines 19931–19944)—undergoes `GranuleProtectionCheck(addrdesc, accdesc)` (lines 19879–19926) against the 2-level Granule Protection Table (GPT) anchored at `GPTBR_EL3.BADDR`:

1. **Root-PAS Self-Protection:** `GPTWalk` (lines 19794–19871) explicitly sets `gptaddrdesc.paddress.paspace = PAS_Root` (line 19815) before reading Level 0 and Level 1 descriptors via `PhysMemRead`. GPT tables themselves reside strictly in `PAS_Root`, preventing Normal, Secure, and Realm worlds from mutating or inspecting GPT entries and avoiding recursive GPC walks.
2. **Above-PPS Asymmetric Default:** If the target physical address exceeds the configured Protected Physical Address Size (`AbovePPS(address.address)`, lines 19899–19908), `GranuleProtectionCheck` returns `GPCNoFault()` **only** when `address.paspace == PAS_NonSecure`, and unconditionally raises `GPCFault(GPCF_Fail, 0)` for `PAS_Realm`, `PAS_Secure`, and `PAS_Root`. Consequently, physical space above `PPS` cannot be aliased into confidential worlds.
3. **Table Walk Granule Protection Faults:** When a translation table walk hits a mismatched PAS granule, `FetchDescriptor` records `fault.statuscode = Fault_GPCFOnWalk` and propagates `fault.gpcfs2walk = fault.secondstage` (lines 19938–19940), preventing a malicious host from tricking a Realm or EL2 walker into reading descriptors outside its permitted PAS.
4. **Base vs. Extended GPI Permission Matrix:** In base Armv9.4-A (`v8_base.sail:19492–19518`, `GPICheck`), the 4-bit Granule Protection Information (`GPI`) field restricts accesses per table below; TF-A (`include/lib/extensions/rme.h:20–30`) adds extended RME GPC encodings for Non-Secure-Only (`NSO`) and device/security-state refinements (`SA`, `NSP`):

| GPI Macro (`rme.h`) | 4-bit Encoding | Permitted `PAS` (Base Armv9.4-A `GPICheck` / Extended RME) | Operational Role |
|---|---|---|---|
| `GPT_GPI_NO_ACCESS` | `0x0` (`0b0000`) | None (`false`) | Barrier state during cross-world undelegation; unmapped holes |
| `GPT_GPI_SA` | `0x4` (`0b0100`) | Extended RME (`GPCCR_SA_BIT`) | Secure-accessible / device assignment extension |
| `GPT_GPI_NSP` | `0x5` (`0b0101`) | Extended RME (`GPCCR_NSP_BIT`) | Non-Secure protected extension |
| `GPT_GPI_SECURE` | `0x8` (`0b1000`) | `PAS_Secure` only | Classic TrustZone Secure memory |
| `GPT_GPI_NS` | `0x9` (`0b1001`) | `PAS_NonSecure` only | Normal-world Host Linux / shared buffers |
| `GPT_GPI_ROOT` | `0xA` (`0b1010`) | `PAS_Root` only | EL3 Monitor code/data and L0/L1 GPT tables |
| `GPT_GPI_REALM` | `0xB` (`0b1011`) | `PAS_Realm` only | RMM and confidential Realm memory |
| `GPT_GPI_NSO` | `0xD` (`0b1101`) | Extended RME (`GPCCR_NSO_BIT`) | Non-Secure Only (blocks Secure/Realm/Root aliasing) |
| `GPT_GPI_ANY` | `0xF` (`0b1111`) | All four PAS (`true`) | Shared ROM/peripherals initialized prior to DDR carve-out |

Note a subtle hardware encoding pitfall preserved in TF-A (`include/lib/extensions/rme.h:180–195`): `GPCCR_EL3.PGS` encodes `0b00 = 4 KiB`, `0b01 = 64 KiB`, and `0b10 = 16 KiB` (non-monotonic ordering; `pgs_to_bits[] = { 12, 16, 14 }` in `lib/gpt_rme/gpt_rme.c:843`).

#### 2.2 Mutual-Distrust Transition Ordering & Cache Aliasing (`gpt_delegate_pas` / `gpt_undelegate_pas`)

In Arm CCA, a single DRAM physical address can have up to four distinct physical-address-space cache aliases (`(PA, PAS_NonSecure)`, `(PA, PAS_Secure)`, `(PA, PAS_Realm)`, `(PA, PAS_Root)`), distinguished by bits `[62:61]` (`GPT_NSE_*`, `rme.h:32–42`). Because hardware caches above the Point of Physical Aliasing (PoPA) do not maintain coherence *across* distinct PAS tags, changing a granule's GPI without strict serialization and PoPA cache maintenance violates confidentiality or integrity.

In `ARM-software/arm-trusted-firmware` (`lib/gpt_rme/gpt_rme.c:564–822`), the EL3 Granule Transition Service enforces asymmetric delegate vs. undelegate protocols under a GPT lock (either global `gpt_lock` or 512 MiB-strided `gpt_bitlock` when `RME_GPT_BITLOCK_BLOCK != 0`):

- **Delegation (`NS -> REALM` or `NS -> SECURE`, `gpt_delegate_pas`, lines 632–674):**
  1. Reject unless `src_sec_state ∈ {SMC_FROM_REALM, SMC_FROM_SECURE}` and current `GPI == GPT_GPI_NS`.
  2. If the covering L1 entry is a contiguous descriptor (`2 MiB`, `32 MiB`, or `512 MiB`), shatter it into 4-bit-per-granule L1 descriptors (`shatter_block`, lines 146–209).
  3. Flush target PAS speculative lines past PoPA: `flush_page_to_popa(base | nse_target)` (`DC CIPAPA` / `DC CIGDPAPA` with `FEAT_MTE2`).
  4. Write `target_pas` (`GPT_GPI_REALM` or `GPT_GPI_SECURE`) to L1 GPT entry followed by `dsboshst()`.
  5. Broadcast outer-shareable GPT TLB invalidation: `tlbi_page_dsbosh(base)` (`TLBI RPALOS` + `DSB OSH`).
  6. Flush `PAS_NonSecure` to PoPA (`flush_page_to_popa(base | (GPT_NSE_NS << 62))`) to ensure no stale NS dirty lines overwrite Realm memory later.
- **Undelegation (`REALM/SECURE -> NS`, `gpt_undelegate_pas`, lines 751–812):**
  1. Verify caller security state matches current GPI (`SMC_FROM_REALM && GPT_GPI_REALM` or `SMC_FROM_SECURE && GPT_GPI_SECURE`); shatter contiguous L1 block if needed.
  2. **Step 1 (Access Revocation Barrier):** Write `GPT_GPI_NO_ACCESS` (`0x0`) to the L1 GPT entry + `dsboshst()`, then execute `tlbi_page_dsbosh(base)`. No PE in any world can now read, write, or speculatively allocate cache lines for this PA.
  3. **Step 2 (Dual-PAS PoPA Scrub/Invalidate):** Flush outgoing PAS (`flush_page_to_popa(base | nse_outgoing)`) so previously zeroed bytes reach DRAM past PoPA, then flush `PAS_NonSecure` (`flush_page_to_popa(base | nse_ns)`) to discard any pre-scrub speculative NS cache fills.
  4. **Step 3 (Publish NS):** Write `GPT_GPI_NS` (`0x9`), run `tlbi_page_dsbosh(base)`, and optionally fuse uniform L1 descriptors back into contiguous blocks (`fuse_block`).

**Execution verification (`Basis: execution`):** Our BFS interleaving model (`probe_world_isolation.py`, Section 1 in Evidence) explores concurrent Realm PE writes, dirty cacheline evictions, and NS PE reads. The two-phase `GPT_GPI_NO_ACCESS` protocol is safe across all `10` reachable interleavings (`0` violations). Removing the `NO_ACCESS` barrier (scrubbing DRAM and writing `GPT_GPI_NS` directly) yields a 5-step counterexample in which a dirty Realm cacheline evicts `SECRET` to DRAM after scrubbing and becomes readable by a cold NS load once `GPT_GPI_NS` is published.

#### 2.3 TF-RMM Granule State Machine & Lock-Order Discipline

While EL3 tracks physical PAS ownership in the GPT, R-EL2 (`TF-RMM/tf-rmm`, `lib/granule/include/granule_types.h`) tracks fine-grained semantic ownership of every 4 KiB granule inside a compact 16-bit `struct granule { uint16_t descriptor; }` bitfield (`[15]` `bit_lock`, `[14:10]` 5-bit `state`, `[9:0]` 10-bit `refcount`, lines 275–311):

- **External vs. Internal Granule States (`granule_types.h:23–45`, `114–272`):** Six *external* states (`NS = 0`, `DELEGATED = 1`, `RD = 2`, `REC = 3`, `PDEV = 7`, `VDEV = 9`) may be passed directly by PA from untrusted Host RMI calls; nine *internal* states (`REC_AUX = 4`, `DATA = 5`, `RTT = 6`, `PDEV_AUX = 8`, `VDEV_AUX = 10`, `PARTIAL = 11`, `INTERNAL = 12`, `PSMMU_ST_L2 = 13`, `RD_AUX = 14`) are reachable only via RMM-owned metadata.
- **Deadlock-Free Total Lock Order (`granule_types.h:48–90`):** RMM enforces strict hierarchical locking:
  1. Type precedence: `RD -> REC -> PDEV -> VDEV -> RTT (root-to-leaf hand-over-hand) -> DELEGATED -> NS -> DATA -> REC_AUX -> ... -> PARTIAL`, with memory granules strictly preceding device granules (`struct dev_granule`).
  2. Ascending PA tie-breaking for independently addressed granules of identical type.
  3. **Non-blocking state-mismatch abort:** Independently addressed granules check expected state before, during contention, and after acquiring `bit_lock`; any mismatch immediately releases all locks without spinning (preventing untrusted-Host-induced livelocks).
- **Gateway Sanitization Invariant (`granule_types.h:98–106`):** `GRANULE_STATE_DELEGATED` has `refcount == 0` when unlocked; consumers must sanitize/initialize when leaving `DELEGATED` into Realm use, and RMM must zero the granule before transitioning `DELEGATED -> NS` via EL3 undelegation (`runtime/rmi/granule.c:45–59`).

#### 2.4 Formal Verification of Arm CCA: Columbia VIA vs. Arm Fox et al.

Basis: source + documentation

Two complementary verification efforts target Arm CCA's RMM/EL3M stack:
- **Columbia VIA (`columbia/VIA`, Li et al., OSDI 2022):** Mechanizes 39 CompCert Clight refinement layers (`BaremoreService` through `RMMHandler`, `README.md:54–95`) plus inline assembly proofs (`proof/Assembly/`) and a top-level Ideal-vs-Real simulation (`proof/Security/SecureMachine.v`, `RefRel.v`). Uses Mover Oracles (`proof/MoverTypes.v`) to refine hand-over-hand RTT page-table walks (`TableDataOpsRef1..3`) into atomic specifications and lifts Arm relaxed memory to sequential consistency via permutation conditions (`proof/RmiSMC/RefProof/PermCondition.v`).
- **Arm Verification Methodology (Fox et al., PACMPL/OOPSLA 2023, `doi:10.1145/3586040`):** Developed contemporaneously with Arm's production RMM specification and reference implementation. Combines interactive theorem proving (proving security/confidentiality properties over the formal RMM specification), bounded model checking (CBMC harnesses over C implementation functions), and concurrency-aware testing against the evolving RMI/RSI ABI.

---

### 3. Arm TrustZone (OP-TEE): Asymmetric Shared Memory & Double-Fetch Defenses

Basis: source

In classic Arm TrustZone (`OP-TEE/optee_os`), Secure EL1 (`OP-TEE`) does not distrust Normal world symmetrically; instead, Normal world Linux allocates shared memory (`MEM_AREA_NSEC_SHM` static buffers or dynamic non-contiguous 4 KiB page lists with `OPTEE_MSG_ATTR_NONCONTIG`, `core/include/optee_msg.h:49–75`) and passes physical addresses (`struct optee_msg_param_tmem`) or registered cookies (`struct optee_msg_param_rmem` / FF-A `fmem`) across `SMC`.

Because concurrent Normal-world CPUs retain write access to NS shared memory throughout an SMC invocation, **TOCTOU double-fetch vulnerabilities** are a primary cross-world hazard. Inspection of `OP-TEE/optee_os` (`core/arch/arm/kernel/thread_optee_smc.c:99–231` and `core/tee/entry_std.c:67–230`) reveals four defensive patterns required at every asymmetric world boundary:
1. **Single-Read Snapshot (`READ_ONCE`) of Header & Parameter Metadata:** Both `get_msg_arg()` (`thread_optee_smc.c:114`) and `std_entry_with_parg()` (`thread_optee_smc.c:200`) snapshot `arg->num_params` via `READ_ONCE`, bound-check against `OPTEE_MSG_MAX_NUM_PARAMS`, and pass the local `size_t num_params` down to `call_entry_std()` so a concurrent NS write cannot expand `num_params` after bounds validation. Similarly, `copy_in_params()` (`entry_std.c:184–230`) snapshots `params[n].attr`, `tmem->buf_ptr`, `tmem->size`, `rmem->offs`, and `fmem->global_id` once into secure-world stack/struct copies (`saved_attr[]`, `ta_param`).
2. **Checked Arithmetic Overflow:** `set_fmem_param()` (`entry_std.c:93–95`) and `set_rmem_param()` (`entry_std.c:175–177`) check `ADD_OVERFLOW(mem->offs, mem->size, &req_size) || mem->mobj->size < req_size`, returning `TEE_ERROR_SECURITY` rather than trusting NS-supplied offset/length pairs.
3. **Physical Range Containment (`core_pbuf_is` / `mobj_mapped_shm_alloc`):** Before mapping an untrusted physical address `parg` from `SMC` registers, OP-TEE verifies that `parg` lies strictly in Non-Secure DDR (`thread_optee_smc.c:191, 217–220`), preventing a classic **confused-deputy pointer attack** in which Normal world supplies a Secure-world PA and tricks OP-TEE into overwriting its own memory.
4. **Payload Data Remains Volatile:** While header metadata is copied in, `MEMREF` payload buffers referenced by `struct param_mem` remain NS-writable unless the Trusted Application explicitly copies them into secure RAM before parsing—a persistent FFI invariant for any zero-copy parser crossing a world boundary.

---

### 4. AMD SEV-SNP: Reverse Map Table, VMPL 0..3 Privilege Rings, and COCONUT-SVSM

Basis: normative + source + execution

AMD SEV-SNP adds hardware integrity and intra-guest privilege stratification to AES-encrypted VMs through the **Reverse Map Table (RMP)**—a host-physical-indexed table checked on every guest and host memory access after nested page translation.

#### 4.1 Three-Instruction Ownership Split (`RMPUPDATE`, `PVALIDATE`, `RMPADJUST`)

| Instruction | Permitted Caller | Security Effect | Failure / Invariant |
|---|---|---|---|
| `RMPUPDATE` | Host Hypervisor only | Assigns a host physical page `(HPA -> ASID, GPA, PageSize)` and **always clears `Validated = 0`** | Host can never forge `Validated = 1`; reassigning an active guest page invalidates it, triggering `#VC(0x404)` on guest access (preventing replay/remapping/aliasing). |
| `PVALIDATE` | Guest **VMPL0 only** (`coconut-svsm/svsm`, `kernel/src/sev/utils.rs:141–180`) | Toggles `Validated` bit (`0 <-> 1`) for a guest virtual address mapped to an assigned GPA (`RCX=0` for 4 KiB, `RCX=1` for 2 MiB) | Returns `CF=1` (`FAIL_UNCHANGED`) if page already in target state, `RAX=1` (`FAIL_INPUT`), or `RAX=6` (`FAIL_SIZEMISMATCH`, requiring 2 MiB -> 4 KiB fallback, `utils.rs:105–108`). |
| `RMPADJUST` | Guest **VMPL `k`** targeting strictly lower **`j > k`** (`utils.rs:240–300`) | Sets per-VMPL permission mask `(R, W, X_USER, X_SUPER)` and `BIT_VMSA` (`1 << 16`) for VMPL `j` | Strict downward monotonicity: cannot modify `j <= k`, cannot grant any permission bit VMPL `k` itself lacks (`RAX=2`, `FAIL_PERMISSION`), and cannot mark a writable page as `VMSA`. |

In `coconut-svsm/svsm` (`kernel/src/sev/utils.rs:240–256`), the exact `RMPFlags` bit layout passed in `RDX` to `rmpadjust` is:
- `[7:0]` target VMPL (`0..3`, with `GUEST_VMPL` typically `1` or `2` when SVSM runs at `VMPL0`),
- `[8]` `READ` (`1 << 8`), `[9]` `WRITE` (`1 << 9`), `[10]` `X_USER` (`1 << 10`), `[11]` `X_SUPER` (`1 << 11`),
- `[16]` `BIT_VMSA` (`1 << 16`); `RMPFlags::VMSA = READ | BIT_VMSA`.

#### 4.2 Intra-Guest Mutual Distrust: SVSM VMPL0 vs. Guest OS VMPL1/2

Running a Secure VM Service Module (`COCONUT-SVSM`) in **VMPL0** and the guest Linux kernel in **VMPL1/2** creates a *nested* mutually-distrusting boundary inside the confidential VM: VMPL0 hosts sensitive services (vTPM, UEFI variables, attestation, `PVALIDATE` proxy) that must be isolated from both the untrusted host hypervisor **and** a compromised guest kernel.

Direct inspection of `coconut-svsm/svsm` (`kernel/src/protocols/core.rs:54–179`) exposes two critical concurrency hazards at the VMPL0/VMPL1 seam:
1. **`PVALIDATE_LOCK` vs. `core_create_vcpu` Error-Path Leak (`core.rs:54–61`):** Without a reader-writer lock serializing `SVSM_REQ_CORE_PVALIDATE` (read lock) against `SVSM_REQ_CORE_CREATE_VCPU` / `DELETE_VCPU` (write lock), a guest OS race during the error-restore path (`core_create_vcpu_error_restore`, lines 74–91) could cause SVSM to restore guest permissions on a page simultaneously repurposed as an SVSM-owned page.
2. **VMSA Validation TOCTOU (`core.rs:141–172`):** To bring up a secondary guest vCPU, the guest OS supplies a candidate VMSA physical page (`paddr`) and Calling Area Address (`pcaa`). If SVSM checked `check_vmsa()` (`new.vmpl == GUEST_VMPL && (new.efer & SVME) != 0 && new.sev_features == sev_features`, lines 94–98) *before* revoking guest write access, another guest vCPU could overwrite `new.vmpl = 0` between check and `rmp_set_guest_vmsa()`, escalating into VMPL0! Therefore `core_create_vcpu` executes the strict sequence:
   1. Validate page alignment, non-overlap of `vmsa_region` and `caa_region`, and `valid_phys_region(...)` (excluding SVSM RAM).
   2. Acquire `PVALIDATE_LOCK.lock_write()` and register `paddr` in `PERCPU_VMSAS`.
   3. Call `rmp_revoke_guest_access(vaddr, PageSize::Regular)` **followed by `flush_tlb_global_sync_page(vaddr, PageSize::Regular)`** (lines 142–151).
   4. Only *after* guest write access is globally revoked across all vCPUs, evaluate `check_vmsa(&new_vmsa, ...)`.
   5. Mark the page with `rmp_set_guest_vmsa(vaddr)` (`RMPFlags::VMSA = READ | BIT_VMSA`).

#### 4.3 Malicious `#VC` and Interrupt Injection (`WeSee` / `Heckler`)

Because SEV-SNP hardware delivers `#VC` (vector `29`) for Non-Automatic Exit (NAE) events such as `CPUID`, `IOIO`, `MSR`, and `RDTSC`, an untrusted hypervisor can inject arbitrary interrupt vectors—including vector `29` (`#VC`, **WeSee**, Schlueter et al., IEEE S&P 2024, `arXiv:2404.03526`, CVE-2024-25742) or general non-timer interrupts (**Heckler**, Schlueter et al., USENIX Security 2024)—at attacker-chosen instruction boundaries when Restricted/Alternate Injection is disabled.

In `coconut-svsm/svsm` (`kernel/src/cpu/vc.rs:94–172`), SVSM narrows this surface defensively:
- **Fatal fail-closed on unvalidated pages (`vc.rs:103`):** `assert!(error_code != SVM_EXIT_PAGE_NOT_VALIDATED)` immediately terminates rather than attempting instruction emulation on `0x404`.
- **Instruction-Opcode Cross-Check (`vc.rs:110–130`):** `handle_vc_exception()` decodes the instruction at `ctx.frame.rip` via exception-table-guarded `TryPtr::read()` and requires an exact match between `ctx.error_code` and `DecodedInsn` (e.g., `(SVM_EXIT_CPUID, Some(DecodedInsn::Cpuid))`), rejecting forged `#VC` vectors delivered at non-trapping instructions.
- **No Untrusted Hypervisor CPUID (`vc.rs:148–157`):** `handle_cpuid()` exclusively serves results from the PSP-verified static firmware `cpuid_table()` rather than issuing a GHCB VMGEXIT to the untrusted VMM.
- **Hardware Mitigation:** Full mitigation of asynchronous malicious interrupt injection requires SEV-SNP **Restricted Injection** (routing all host interrupts solely through `#HV` vector `28`, with SVSM/guest draining a validated doorbell page) or **Alternate Injection** (VMPL0 mediating virtual APIC delivery to VMPL1/2).

---

### 5. Intel TDX: SEAM `TDG.VP.VMCALL` Scrubbing & Guest `#VE` MMIO Hazards

Basis: normative + source

Intel TDX isolates Trust Domains (TDs) using a CPU-enforced **Secure Arbitration Mode (SEAM)** hosting the Intel-signed TDX Module (`MRSEAM` SHA-384 measured at load time). Private TD memory is mapped via the TDX-Module-managed **Secure EPT (SEPT)** with the GPA shared bit (`BIT_ULL(gpa_width - 1)`, `linux/arch/x86/coco/tdx/tdx.c:334–335`) cleared (`0`) and encrypted under a TD-private MKTME KeyID; shared memory sets the GPA shared bit (`1`) and walks the untrusted VMM's Shared EPT.

#### 5.1 SEAM `TDG.VP.VMCALL` Register-Exposure Firewall (`tdx_2.0`)

When a TD guest explicitly requests VMM services via `TDCALL[TDG.VP.VMCALL]`, the TDX Module (`intel/confidential-computing.tdx.tdx-module`, branch `tdx_2.0`, `src/td_dispatcher/vm_exits/tdg_vp_vmcall.c:44–124`) enforces a strict opt-in register exposure mask (`control.gpr_select` and `control.xmm_select` in `RCX`):
- **Forbidden GPR bits (`tdg_vp_vmcall.c:82–96`):** Bits `0` (`RAX`), `1` (`RCX`), and `4` (`RSP`)—plus bit `5` (`RBP`) when `config_flags.no_rbp_mod` is set—MUST be zero in `control.gpr_select`, and `control.reserved` (`RCX[63:32]`) MUST be zero; otherwise the module fails closed with `TDX_OPERAND_INVALID`.
- **Mandatory Scrubbing of Non-Selected Registers (`tdg_vp_vmcall.c:57–72, 113–119`):** Only GPRs explicitly enabled in `control.gpr_select` are copied from `tdvps->guest_state.gpr_state` to `vmm_regs`; all non-selected GPRs (except `RBP` under `no_rbp_mod`) are explicitly zeroed (`0ULL`), and `td_vmexit_to_vmm()` scrubs extended vector state according to `xfam | SSE` excluding `control.xmm_select`.

#### 5.2 Guest `#VE` Handler & `TDVMCALL` MMIO/PIO Attack Surface (`torvalds/linux`)

Whereas the TDX Module enforces clean register hygiene on exit, the **guest OS `#VE` handler** (`torvalds/linux`, `arch/x86/coco/tdx/tdx.c:348–858`) sits directly on the untrusted-VMM Iago attack surface:

1. **Nested `#VE` Double-Fault Hazard (`tdx.c:762–790`):** `tdx_get_ve_info()` MUST invoke `TDCALL[TDG.VP.VEINFO_GET]` as early as possible on `#VE` entry to read `{exit_reason, exit_qual, gla, gpa, instr_len, instr_info}` and clear the `#VE valid` flag; any nested `#VE` while `#VE valid` is set escalates immediately to an unrecoverable `#DF`.
2. **Undefined `instr_len` on EPT Violations (`tdx.c:368–390`):** For instruction-execution `#VE`s (`HLT`, `RDMSR`, `WRMSR`, `CPUID`, `IO`), `ve->instr_len` is architecturally defined; for `EXIT_REASON_EPT_VIOLATION` (MMIO), `ve->instr_len` is **undefined**, forcing the guest kernel (`handle_mmio`, lines 560–668) to fetch `MAX_INSN_SIZE` bytes at `regs->ip` via `copy_from_kernel_nofault` and run an in-kernel x86 instruction decoder (`insn_decode` + `insn_decode_mmio`).
3. **Private-GPA EPT-Violation Fail-Closed (`tdx.c:831–834`):** In `virt_exception_kernel()`, if `EXIT_REASON_EPT_VIOLATION` arrives with `is_private_gpa(ve->gpa)` (`gpa == cc_mkenc(gpa)`, shared bit clear), Linux **panics immediately** (`"Unexpected EPT-violation on private memory."`), defeating VMM attempts to induce MMIO emulation on private guest RAM. Moreover, `tdx_setup()` disables SEPT `#VE` (`disable_sept_ve`) and `NOTIFY_ENABLES` (`tdg_vm_wr(TDCS_NOTIFY_ENABLES, 0, -1ULL)`, lines 340–344) to prevent host-induced spurious `#VE` floods.
4. **Residual MMIO / PIO / MSR / CPUID Trust Boundaries (`tdx.c:454–738`):**
   - `handle_mmio()` rejects userspace mode (`user_mode(regs)`), non-kernel `ve->gla`, cross-page split MMIO accesses (`vaddr / PAGE_SIZE != (vaddr + size - 1) / PAGE_SIZE`, lines 603–605, catching `load_unaligned_zeropad` faults), and `INSN_MMIO_MOVS` string ops.
   - `handle_cpuid()` restricts VMM-emulated leaves strictly to the hypervisor range `0x40000000..0x4FFFFFFF`, returning zeros outside that range (`tdx.c:511–514`).
   - **Critical remaining Iago/leakage hazards:** Every MMIO read (`mmio_read`, lines 537–552), Port I/O read (`handle_in`, lines 670–693), and MSR read (`read_msr`, lines 454–473) injects **arbitrary untrusted VMM-chosen bits** directly into guest kernel GPRs (`*val = args.r11`). Bugs in operand width / zero-or-sign extension (`extend_size`, lines 641–666) or uninitialized stack variables in MMIO read paths (historically exemplified by CVE-2024-46794) can either leak kernel stack bytes to the VMM or corrupt kernel pointer/index arithmetic downstream in unhardened device drivers.

---

### 6. RISC-V Enclave Isolation: Keystone PMP vs. Penglai sPMP

Basis: normative + source + execution

Standard RISC-V privilege architecture lacks a 4-world GPT or hardware RMP, instead relying on **M-mode Physical Memory Protection (PMP)** CSRs (`pmpcfg0..15`, `pmpaddr0..63`, typically 8 or 16 implemented entries on commodity cores) programmed by an M-mode Security Monitor (SM).

#### 6.1 Keystone SM PMP Mechanics & Hardware Slot Bottleneck

In `keystone-enclave/keystone` (`sm/src/pmp.c:52–250`), the M-mode Security Monitor isolates Enclave Private Memory (EPM) from the untrusted S-mode Linux OS by maintaining a global table of non-overlapping regions (`detect_region_overlap` with overflow-checked `CHECKED_ADD`, lines 156–186) and synchronizing PMP CSR updates across all harts via M-mode IPIs (`send_and_sync_pmp_ipi`, lines 203–222):

- **Address-Matching Modes (`sm/src/pmp.c:72–82`):**
  - **NAPOT (Naturally Aligned Power-Of-Two):** Encodes `[addr, addr + size)` into a single `pmpaddr` CSR as `(addr | (size/2 - 1)) >> 2` (line 77), requiring both `size = 2^k >= 8` and `addr % size == 0`.
  - **TOR (Top-Of-Range):** Uses two adjacent entries (`region_needs_two_entries`, lines 62–65: `pmpaddr[i-1] = addr >> 2`, `pmpaddr[i] = (addr + size) >> 2`), allowing arbitrary 4-byte-aligned bounds at double the hardware slot cost.
- **Entry Exhaustion & Contiguity Tax (`Basis: execution`):** Because hardware PMP evaluates entries in strict lowest-index priority order and provides only 8–16 slots on most cores, covering non-power-of-two or fragmented memory rapidly exhausts registers. Our micro-probe (`probe_world_isolation.py`, Section 4) confirms exact `NAPOT` encoding (`NAPOT(0x80400000, 4 MiB) -> 0x2017ffff`) and shows that covering an arbitrary 508 KiB (`127 x 4 KiB`) region at `0x80001000` consumes **7 NAPOT entries** (vs. 2 TOR entries), forcing Keystone to allocate physically contiguous enclave memory and severely limiting concurrent enclaves per core.
- **Missing Hardware Lock / M-Mode Isolation:** On baseline RV64 without `Smepmp` (Enhanced PMP), unlocked PMP entries (`L=0`) do **not** restrict M-mode itself, and locked entries (`L=1`) cannot be modified until hardware reset—forcing the SM to keep dynamic enclave PMP entries unlocked (`L=0`) and trust all M-mode code completely.

#### 6.2 Penglai Scalable Memory Protection (`sPMP` / Guarded Page Tables)

Penglai (`Penglai-Enclave/Penglai-Enclave-sPMP`, Feng et al., USENIX OSDI 2021) directly addresses the PMP entry-count ceiling by separating coarse region isolation from scalable fine-grained page ownership:
- Replaces per-enclave PMP slot consumption with hardware-checked **Guarded Page Tables (GPT/mount-table)** and **sPMP** (Supervisor-level / scalable PMP extensions integrated with OpenSBI `opensbi-0.9`/`1.0`/`1.2`), allowing thousands of concurrent non-contiguous enclaves without physically contiguous CMA reservations or cross-hart PMP slot exhaustion.
- Shifts memory-isolation enforcement from $O(N_{\text{enclaves}})$ register comparators to $O(1)$ per-enclave context-switch root pointers verified by M-mode SM on enclave enter/exit.

---

### 7. Deprivileged-Host EL2 Micro-Hypervisors: Linux pKVM & SeKVM + Formal Verification

Basis: source + documentation + execution

On Armv8-A/v9-A platforms lacking RME hardware (such as mobile Android SoCs and existing cloud Arm64 servers), **Linux pKVM** and **SeKVM** achieve mutually-distrusting host/guest isolation purely in software at **Non-Secure EL2**, deprivileging the massive Linux host kernel (NS-EL1) into an untrusted memory allocator and vCPU scheduler.

#### 7.1 Linux pKVM Host-Stage-2 Ownership State Machine (`torvalds/linux`)

Once `__pkvm_prot_finalize()` locks down EL2 (`arch/arm64/kvm/hyp/include/nvhe/mem_protect.h:33, 70–76`), pKVM installs an identity-mapped **Stage-2 page table (`host_mmu.pgt`, `VMID = 0`) underneath host Linux itself** (`kvm_host_prepare_stage2`, `mem_protect.c:159–183`). Every physical page is tracked across three components—`PKVM_ID_HOST`, `PKVM_ID_HYP`, and `PKVM_ID_GUEST` (which also defines the strict deadlock-free component lock order: `host_lock_component()` -> `guest_lock_component(vm)`, `mem_protect.h:26–31`)—using a 2-bit ownership lattice (`arch/arm64/kvm/hyp/include/nvhe/memory.h:21–71`):

- `PKVM_PAGE_OWNED` (`0b00`): Exclusive owner; holds RWX access; no other component may map the page.
- `PKVM_PAGE_SHARED_OWNED` (`0b01`): Owner that has explicitly shared the page with one borrower (or multiple non-protected guests via `page->host_share_guest_count`).
- `PKVM_PAGE_SHARED_BORROWED` (`0b10`): Non-owner mapped borrower; cannot donate or reclaim the page.
- `PKVM_NOPAGE` (`0b11`): Unmapped/inaccessible; for `hyp`, stored bitwise-complemented (`__hyp_state_comp ^ 0b11`, `memory.h:64–68, 115–123`) so zero-initialized `hyp_vmemmap` pages default directly to `PKVM_NOPAGE` without an $O(\text{RAM})$ boot loop!

Key verified transitions in `arch/arm64/kvm/hyp/nvhe/mem_protect.c`:
- **Donation (`__pkvm_host_donate_guest`, lines 1451–1486):** Locks `Host` then `Guest`; verifies `Host == PKVM_PAGE_OWNED`, `Guest == PKVM_NOPAGE`, and sufficient stage-2 memcache; unmaps from Host Stage-2 while recording owner metadata (`PKVM_ID_GUEST` + encoded GFN); maps into Guest Stage-2 with `pkvm_mkstate(KVM_PGTABLE_PROT_RWX, PKVM_PAGE_OWNED)`.
- **Forced/Normal Reclaim (`__pkvm_host_reclaim_page_guest`, lines 1394–1433):** When reclaiming a `PKVM_PAGE_OWNED` guest page back to Host, pKVM verifies `Host == PKVM_NOPAGE` and **unconditionally invokes `hyp_poison_page(phys)`** (zeroing/scrubbing confidential contents, line 1411) *before* unmapping from Guest Stage-2 and restoring `PKVM_ID_HOST` ownership—preventing a malicious host from forcing teardown to harvest guest secrets.
- **Sharing (`__pkvm_host_share_guest`, lines 1488–1557):** Validates `prot` subset of `RWX`, `Guest == PKVM_NOPAGE`, and `Host ∈ {OWNED, SHARED_OWNED}` (with `U32_MAX` overflow check on `host_share_guest_count`); transitions Host to `SHARED_OWNED` and Guest to `SHARED_BORROWED`.

**Execution verification (`Basis: execution`):** Exhaustive BFS over the 3-component single-page transition system (`probe_world_isolation.py`, Section 3) visits all `7` reachable states with `0` invariant violations: at every reachable state, exactly one component holds `OWNED` or `SHARED_OWNED`, and whenever `Guest == PKVM_PAGE_OWNED`, both `Host` and `Hyp` are strictly `PKVM_NOPAGE`.

#### 7.2 Formal Verification Trade-Offs: SeKVM vs. Islaris vs. CN

| Verification Effort | Target Codebase & Artifact | Proof Engine & Semantic Grounding | Key Security Theorem / Scope | Key Trust Assumptions / Gaps |
|---|---|---|---|---|
| **SeKVM** (Li et al., IEEE S&P 2021 `10.1109/SP40001.2021.00049`; USENIX Sec 2021; Tao et al., SOSP 2021 `10.1145/3477132.3483560`) | `VeriGu/SeKVM-4.18` (`75e3591e...`) & `VeriGu/sosp-paper211-ae` (`683c36a1...`) | Coq 8.4 over CompCert Clight (34 security-preserving layers) + Promising-Arm relaxed-memory `wDRF` lifting | End-to-end VM confidentiality & integrity (noninterference) on multiprocessor Arm relaxed memory hardware, including SMMU stage-2 page tables | Manual C retrofitting (`_hyp_text` removal) before `clightgen` (`sosp-paper211-ae/README.md:139`); unverified GCC compilation from C to AArch64 binary; 56-VMID static bound |
| **Islaris** (Sammler et al., PLDI 2022 `10.1145/3519939.3523434`) | `rems-project/islaris` (`c978e10f...`) targeting Armv8-A pKVM binary snippets | Isla symbolic execution over authoritative **Sail** Armv8/RISC-V ISA specs + Iris separation logic in Coq | Verifies *compiled machine code* (`objdump` traces of pKVM exception vector installation & relocation stubs) directly against Sail ISA semantics | Scales to critical low-level assembly/binary snippets rather than full multi-thousand-line C hypervisors; manual trace extraction from `objdump` |
| **CN** (Pulte et al., POPL 2023 `10.1145/3571194`) | `rems-project/cn` (`d1c60d17...`) targeting pKVM buddy allocator C code | Separation-logic refinement types over **Cerberus** ISO C semantics + SMT (Z3) discharge | Decidable, developer-maintained proof of C UB-freedom, pointer-arithmetic safety, and functional invariants for real pKVM allocator code | Verifies C source semantics (Cerberus) rather than compiled binary; sequential/per-module specs rather than whole-hypervisor noninterference |

---

### 8. Cross-World FFI & Zero-Copy Verification Invariants

Basis: derived (synthesized from Sections 2–7)

When authoring or verifying low-level Rust/C memory-boundary code (such as `zerocopy` transmutations, paravirtual drivers, SVSM protocols, or OP-TEE TAs) operating across mutually-distrusting CPU worlds, five invariants are non-negotiable:

1. **Volatile / Untrusted-Memory Copy-In Before Validation:** Any descriptor residing in shared memory (`NS_SHM`, SEV-SNP `C=0` GHCB/bounce buffers, TDX `S=1` pages, pKVM `SHARED_BORROWED` pages) can be mutated concurrently by a malicious host or sibling PE. Soundness requires a single volatile copy into private memory *before* structural validation or transmutation (matching OP-TEE `READ_ONCE` + `copy_in_params` and SVSM's `rmp_revoke_guest_access` + global TLB flush before `check_vmsa`).
2. **No Rust `&T` / `&mut T` Directly Over Host-Mutable Shared Pages:** Rust's aliasing and immutability guarantees for `&T` are violated if an untrusted host or sibling world can concurrently write to the backing physical page while `&T` is live; cross-world shared pages must be accessed exclusively through volatile raw-pointer reads/writes into owned private byte arrays prior to `FromBytes` interpretation.
3. **Mandatory Two-Phase Revoke-Flush-Publish on Page Handoff:** Reclaiming or returning private memory to an untrusted domain requires revoking private mappings and broadcasting TLB invalidations *before* scrubbing/poisoning to PoPA and *before* granting target-world access (Arm CCA `NO_ACCESS` barrier + `DC CIPAPA`; pKVM `hyp_poison_page`; SVSM `PVALIDATE_LOCK` + global TLB flush).
4. **Trap-Reason / Instruction Cross-Verification:** Guest handlers for host-injectable exceptions (`#VC`, `#VE`) must verify architectural consistency between the exception code, faulting GPA privacy bit (`is_private_gpa`), and decoded opcode at `RIP`, failing closed on private-memory faults.
5. **Hardware Metadata vs. Software State Lock Ordering:** Any firmware maintaining shadow metadata alongside hardware isolation tables (TF-RMM `struct granule` vs. EL3 GPT; pKVM `struct hyp_page` vs. Host/Guest Stage-2 PTEs; SVSM `PERCPU_VMSAS` vs. RMP) must enforce a strict acyclic lock order and check state-invariants *after* lock acquisition.

## Boundaries

- **Arm CCA Confidential Device Assignment (RME-DA / `PDEV` / `VDEV` / `PSMMU_ST_L2`):** `not examined` in depth beyond observing the granule state enums (`GRANULE_STATE_PDEV = 7`, `VDEV = 9`, `PSMMU_ST_L2 = 13`) and lock-ordering rules in `TF-RMM/tf-rmm` `granule_types.h`. PCIe IDE/TDISP/SPDM device attestation protocols are outside this report's scope.
- **Intel TDX 2.0 Partitioning (L1/L2 nested TDs) and TDX Connect:** `not examined`. Inspection of `intel/confidential-computing.tdx.tdx-module` (`tdx_2.0`) covered `tdg_vp_vmcall.c` GPR/XMM isolation and Linux `#VE` handling (`tdx.c`), not multi-L2 TD partitioning (`TDG.VP.ENTER`).
- **Hardware Microarchitectural Side Channels & Physical DRAM Faults:** `known not to apply` to the architectural isolation guarantees summarized here. GPT, RMP, SEPT, PMP, and EL2 Stage-2 enforce architectural memory access control only; they do not by themselves defeat cache timing, transient execution, Rowhammer/RowPress, or physical power/EM side channels (which require separate hardware/software mitigations).
- **Automated End-to-End Compilation Preservation (C -> Binary) in SeKVM and CN:** `unsupported` in the examined SeKVM (`VeriGu/sosp-paper211-ae`) and CN (`rems-project/cn`) pipelines; SeKVM verifies retrofitted CompCert Clight while compiling the deployed kernel with GCC, and CN verifies Cerberus C semantics rather than emitted AArch64 object code (whereas Islaris verifies compiled binary traces directly against Sail ISA semantics).
- **Non-x86 / Non-Arm / Non-RISC-V Confidential Computing (e.g., IBM Protected Execution Facility / s390x Secure Execution):** `not examined`.
- **Actual Silicon Execution Benchmarks of Arm CCA RME Hardware:** `unknown` from this environment (no RME-enabled silicon was executed); `columbia/VIA` benchmarks in its README were collected on an Arm Neoverse N1SDP emulation setup without native Armv9 RME hardware.

## Evidence

### Primary Repositories, Commits, and Inspected Locations (Observed 2026-11-19)

1. **`ARM-software/arm-trusted-firmware` @ `0d2c4394f010bc91327ee1ee923bf6d70d446bb7`**
   - `include/lib/extensions/rme.h:20–43, 152–196` — `GPT_GPI_*` encodings (`0x0..0xF`), `GPT_NSE_*` PAS tags, `GPCCR_EL3.PGS` non-monotonic mapping (`0b00=4K, 0b01=64K, 0b10=16K`).
   - `include/lib/gpt_rme/gpt_rme.h:43–76` — public `gpt_delegate_pas` / `gpt_undelegate_pas` and `firme_gpt_lock` APIs.
   - `lib/gpt_rme/gpt_rme.c:110–250, 564–897` — `tlbi_page_dsbosh`, `shatter_{2,32,512}mb`, `write_gpt`, two-phase `GPT_GPI_NO_ACCESS` + dual-PAS `flush_page_to_popa` in `gpt_undelegate_pas` (lines 781–803).
2. **`TF-RMM/tf-rmm` @ `8d7961df074f08fd83a2460ab3a2ca0b658fde92`**
   - `lib/granule/include/granule_types.h:11–391` — 15 granule states (`external` vs. `internal`), strict total lock order, 16-bit `struct granule` bitfields (`bit_lock`, `state`, `refcount`), and `GRANULE_STATE_DELEGATED` sanitization invariant.
   - `runtime/rmi/granule.c:19–110` — `smc_granule_range_delegate`, `smc_granule_range_undelegate`, and tracking-region queries.
3. **`rems-project/sail-arm` @ `5416ef6b43e9527c38dc71fb752259c1d01a47e1` (2023-03 ASL snapshot)**
   - `arm-v9.4-a/src/v8_base.sail:19492–19518` (`GPICheck`), `19794–19871` (`GPTWalk` using `PAS_Root` at line 19815), `19879–19926` (`GranuleProtectionCheck` including `AbovePPS` asymmetry at lines 19899–19908), `19931–19960` (`FetchDescriptor` invoking `GranuleProtectionCheck` on every TTW descriptor fetch).
4. **`columbia/VIA` @ `06dcd851332e7ae33936eb00b202d51b9bf965ee`** & **Fox et al., OOPSLA 2023 (`doi:10.1145/3586040`)**
   - `columbia/VIA` `README.md:49–114` — 39 Clight refinement layers, `MoverTypes.v`, `PermCondition.v`, `SecureMachine.v`.
   - Fox, Stockwell, Xiong, Becker, Mulligan, Petri, Chong, *"A Verification Methodology for the Arm Confidential Computing Architecture: From a Secure Specification to Safe Implementations"*, PACMPL Vol. 7, Issue OOPSLA1 (April 2023), `doi:10.1145/3586040`.
5. **`OP-TEE/optee_os` @ `653d9849f767b4d5a72ea9a0f6db55d4f883483a`**
   - `core/include/optee_msg.h:25–244` — `optee_msg_arg`, `OPTEE_MSG_ATTR_NONCONTIG`, `tmem`/`rmem`/`fmem` parameter unions.
   - `core/arch/arm/kernel/thread_optee_smc.c:99–236` — `READ_ONCE(arg->num_params)` snapshot, `core_pbuf_is(CORE_MEM_NSEC_SHM, ...)`, and `mobj_mapped_shm_alloc` NS DDR containment check.
   - `core/tee/entry_std.c:67–230` — `copy_in_params`, `set_fmem_param`, `set_tmem_param`, `set_rmem_param`, `READ_ONCE`, and `ADD_OVERFLOW` checks.
6. **`coconut-svsm/svsm` @ `2a40e72a0f44d4369bb997488f2b7a77e346a634`**
   - `kernel/src/sev/utils.rs:86–300` — `pvalidate`, `pvalidate_range` (2 MiB -> 4 KiB fallback on `FAIL_SIZEMISMATCH`), `RMPFlags` bitflags (`READ=1<<8`, `WRITE=1<<9`, `X_USER=1<<10`, `X_SUPER=1<<11`, `BIT_VMSA=1<<16`), `rmp_adjust` with `__exception_table` fixup.
   - `kernel/src/protocols/core.rs:54–217` — `PVALIDATE_LOCK`, `core_create_vcpu` revoke-and-TLB-flush-before-`check_vmsa` ordering, `core_delete_vcpu`.
   - `kernel/src/cpu/vc.rs:94–211` — `#VC` opcode cross-validation, `assert!(error_code != SVM_EXIT_PAGE_NOT_VALIDATED)`, firmware `cpuid_table()` lookup.
7. **`intel/confidential-computing.tdx.tdx-module` @ `abd4d8ab7e18a345ba33e32335577f550f7b0e83` (`tdx_2.0`)** & **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`**
   - `src/td_dispatcher/vm_exits/tdg_vp_vmcall.c:44–124` — `copy_gprs_data_from_td_to_vmm`, `gpr_check_mask` rejecting `RAX`/`RCX`/`RSP` (and `RBP` under `no_rbp_mod`), zeroing non-selected GPRs, and vector scrubbing.
   - `arch/x86/coco/tdx/tdx.c:312–858` — `tdx_setup` (`cc_mask = BIT_ULL(gpa_width - 1)`, `disable_sept_ve`), `ve_instr_len`, `handle_mmio` (`insn_decode_mmio`, split-page rejection), `tdx_get_ve_info` (`TDG_VP_VEINFO_GET`), and `is_private_gpa` panic.
   - `arch/arm64/kvm/hyp/include/nvhe/memory.h:21–123`, `mem_protect.h:18–76`, `arch/arm64/kvm/hyp/nvhe/mem_protect.c:159–183, 1394–1557` — pKVM `enum pkvm_page_state`, `struct hyp_page` `__hyp_state_comp`, `__pkvm_host_donate_guest`, `__pkvm_host_reclaim_page_guest` (`hyp_poison_page`), `__pkvm_host_share_guest`.
8. **`keystone-enclave/keystone` @ `b8c2385355b2afb5b94a4e5dc503936f1502b972`** & **`Penglai-Enclave/Penglai-Enclave-sPMP` @ `14da25ae108724f639c82091b5003f8015185e13`**
   - `sm/src/pmp.c:52–250` — `region_pmpaddr_val` NAPOT `(addr | (size/2 - 1)) >> 2` and TOR two-entry encoding, `detect_region_overlap` (`CHECKED_ADD`), `send_and_sync_pmp_ipi`.
   - `Penglai-Enclave-sPMP/README.md:10–30, 298–330` — OpenSBI 0.9/1.0/1.2 sPMP integration and OSDI 2021 citation (Feng et al., pp. 275–294).
9. **Formal Verification & Interrupt-Injection Papers**
   - `VeriGu/sosp-paper211-ae` @ `683c36a169fae261207dba1cbeb91bc73d16af3b` (`README.md:45–164`), `VeriGu/SeKVM-4.18` @ `75e3591e663958c370c919aa36fbd484be341043`; Tao et al., SOSP 2021 (`doi:10.1145/3477132.3483560`); Li et al., IEEE S&P 2021 (`doi:10.1109/SP40001.2021.00049`).
   - `rems-project/islaris` @ `c978e10f50db5c40f0fdf113f5f76a779782c6f9` (`README.md:1–60`), Sammler et al., PLDI 2022 (`doi:10.1145/3519939.3523434`).
   - `rems-project/cn` @ `d1c60d1720bed3bed0d45dab247a1959145c8cb9` (`README.md:1–60`), Pulte et al., POPL 2023 (`doi:10.1145/3571194`).
   - Schlueter, Sridhara, Bertschi, Shinde, *"WeSee: Using Malicious #VC Interrupts to Break AMD SEV-SNP"*, IEEE S&P 2024 (`arXiv:2404.03526`, `doi:10.48550/arXiv.2404.03526`, CVE-2024-25742); Schlueter et al., *"HECKLER: Breaking Confidential VMs with Malicious Interrupts"*, USENIX Security 2024, pp. 3459–3476.

### Executable Verification Micro-Probe (`Python 3.13.15`, Standard Library Only)

Save the script below to `/tmp/probe_world_isolation.py` and run `python3 /tmp/probe_world_isolation.py`:

```python
#!/usr/bin/env python3
"""Executable micro-probe for mutually-distrusting CPU world isolation invariants."""
from __future__ import annotations
from collections import deque

GPT_GPI_NO_ACCESS, GPT_GPI_SECURE, GPT_GPI_NS = 0x0, 0x8, 0x9
GPT_GPI_ROOT, GPT_GPI_REALM, GPT_GPI_ANY = 0xA, 0xB, 0xF

def gpi_check(pas: str, gpi: int) -> bool:
    return {
        GPT_GPI_NO_ACCESS: False,
        GPT_GPI_SECURE: pas == "PAS_Secure",
        GPT_GPI_NS: pas == "PAS_NonSecure",
        GPT_GPI_ROOT: pas == "PAS_Root",
        GPT_GPI_REALM: pas == "PAS_Realm",
        GPT_GPI_ANY: True,
    }[gpi]

def check_cca_undelegate_protocol(two_phase_no_access: bool) -> tuple[bool, list[str]]:
    init = (GPT_GPI_REALM, GPT_GPI_REALM, "SECRET", "STALE_NS", "SECRET", 0)
    q: deque[tuple[tuple, list[str]]] = deque([(init, [])])
    seen = {init}
    while q:
        state, trace = q.popleft()
        gpi, r_tlb, r_cache, ns_cache, dram, pc = state
        if gpi_check("PAS_NonSecure", gpi):
            observed = ns_cache if ns_cache is not None else dram
            if observed == "SECRET":
                return False, trace + [f"VIOLATION: NS observed SECRET (gpi={gpi:#x}, dram={dram}, ns_cache={ns_cache})"]
            if ns_cache is not None:
                nxt_evict = (gpi, r_tlb, r_cache, None, dram, pc)
                if nxt_evict not in seen:
                    seen.add(nxt_evict)
                    q.append((nxt_evict, trace + ["NS_Cache: evict STALE_NS (cold read next)"]))
        if gpi_check("PAS_Realm", r_tlb):
            for nxt, label in [
                ((gpi, r_tlb, "SECRET", ns_cache, dram, pc), "Realm_PE: write SECRET into Realm cache"),
                *([((gpi, r_tlb, None, ns_cache, "SECRET", pc), "Realm_Cache: evict dirty SECRET to DRAM")] if r_cache == "SECRET" else []),
            ]:
                if nxt not in seen:
                    seen.add(nxt); q.append((nxt, trace + [label]))
        if two_phase_no_access:
            steps = {
                0: ((GPT_GPI_NO_ACCESS, r_tlb, r_cache, ns_cache, dram, 1), "EL3: write_gpt(GPT_GPI_NO_ACCESS)"),
                1: ((gpi, gpi, r_cache, ns_cache, dram, 2), "EL3: tlbi_page_dsbosh() [Realm TLB now NO_ACCESS]"),
                2: ((gpi, r_tlb, None, ns_cache, "ZERO", 3), "EL3: scrub + flush_page_to_popa(PAS_Realm)"),
                3: ((gpi, r_tlb, r_cache, None, dram, 4), "EL3: flush_page_to_popa(PAS_NonSecure)"),
                4: ((GPT_GPI_NS, r_tlb, r_cache, ns_cache, dram, 5), "EL3: write_gpt(GPT_GPI_NS)"),
                5: ((gpi, gpi, r_cache, ns_cache, dram, 6), "EL3: tlbi_page_dsbosh() [NS visible]"),
            }
        else:
            steps = {
                0: ((gpi, r_tlb, r_cache, ns_cache, "ZERO", 1), "EL3(naive): scrub DRAM to ZERO while Realm still mapped"),
                1: ((GPT_GPI_NS, r_tlb, r_cache, ns_cache, dram, 2), "EL3(naive): write_gpt(GPT_GPI_NS)"),
                2: ((gpi, gpi, r_cache, ns_cache, dram, 3), "EL3(naive): tlbi_page_dsbosh()"),
            }
        if pc in steps:
            nxt, step = steps[pc]
            if nxt not in seen:
                seen.add(nxt); q.append((nxt, trace + [step]))
    return True, [f"SAFE across all {len(seen)} reachable interleavings"]

RMP_READ, RMP_WRITE, RMP_X_USER, RMP_X_SUPER, RMP_BIT_VMSA = 1<<8, 1<<9, 1<<10, 1<<11, 1<<16
RMP_RWX = RMP_READ | RMP_WRITE | RMP_X_USER | RMP_X_SUPER

def rmpadjust_check(c_v: int, c_p: int, t_v: int, n_p: int) -> str:
    if not (0 <= c_v <= 3 and 0 <= t_v <= 3): return "FAIL_INPUT"
    if t_v <= c_v or ((n_p & RMP_RWX) & ~(c_p & RMP_RWX)): return "FAIL_PERMISSION"
    if (n_p & RMP_BIT_VMSA) and (n_p & RMP_WRITE): return "FAIL_INPUT"
    return "OK"

OWNED, SHARED_OWNED, SHARED_BORROWED, NOPAGE = "OWNED", "SHARED_OWNED", "SHARED_BORROWED", "NOPAGE"

def check_pkvm_ownership() -> tuple[int, int]:
    init = (OWNED, NOPAGE, NOPAGE, 0, False)
    q, seen, viol = deque([init]), {init}, 0
    while q:
        h, hy, g, cnt, _ = q.popleft()
        owners = sum(x in (OWNED, SHARED_OWNED) for x in (h, hy, g))
        if owners != 1 or (g == OWNED and (h != NOPAGE or hy != NOPAGE)) or (hy == OWNED and (h != NOPAGE or g != NOPAGE)):
            viol += 1
        nexts = []
        if h == OWNED and g == NOPAGE and hy == NOPAGE:
            nexts += [(NOPAGE, NOPAGE, OWNED, 0, False), (SHARED_OWNED, NOPAGE, SHARED_BORROWED, 1, False),
                      (NOPAGE, OWNED, NOPAGE, 0, False), (SHARED_OWNED, SHARED_BORROWED, NOPAGE, 0, False)]
        if g == OWNED and h == NOPAGE: nexts.append((OWNED, hy, NOPAGE, 0, True))
        if h == SHARED_OWNED and g == SHARED_BORROWED and cnt == 1: nexts.append((OWNED, NOPAGE, NOPAGE, 0, False))
        if g == OWNED and h == NOPAGE and hy == NOPAGE: nexts.append((SHARED_BORROWED, NOPAGE, SHARED_OWNED, 0, False))
        if g == SHARED_OWNED and h == SHARED_BORROWED: nexts.append((NOPAGE, NOPAGE, OWNED, 0, False))
        if hy == OWNED and h == NOPAGE and g == NOPAGE: nexts.append((OWNED, NOPAGE, NOPAGE, 0, False))
        if h == SHARED_OWNED and hy == SHARED_BORROWED and cnt == 0: nexts.append((OWNED, NOPAGE, NOPAGE, 0, False))
        for ns in nexts:
            if ns not in seen: seen.add(ns); q.append(ns)
    return len(seen), viol

def napot_encode(addr: int, size: int) -> int:
    return (addr | ((size // 2) - 1)) >> 2

def napot_cover_count(base: int, length: int) -> int:
    cnt, cur, end = 0, base, base + length
    while cur < end:
        align = cur & -cur if cur else 1 << 64
        sz = min(1 << ((end - cur).bit_length() - 1), align)
        cur += sz; cnt += 1
    return cnt

if __name__ == "__main__":
    print("Two-phase NO_ACCESS:", check_cca_undelegate_protocol(True))
    print("Naive REALM->NS:", check_cca_undelegate_protocol(False))
    print("RMPADJUST:", [rmpadjust_check(*c) for c in [
        (0, RMP_RWX, 1, RMP_READ|RMP_WRITE), (1, RMP_RWX, 0, RMP_READ),
        (1, RMP_READ, 2, RMP_READ|RMP_WRITE), (0, RMP_RWX, 1, RMP_READ|RMP_BIT_VMSA),
        (0, RMP_RWX, 1, RMP_READ|RMP_WRITE|RMP_BIT_VMSA)]])
    print("pKVM reachability:", check_pkvm_ownership())
    print("NAPOT(0x80400000, 4MiB):", hex(napot_encode(0x8040_0000, 4<<20)))
    print("NAPOT cover 508KiB@0x80001000:", napot_cover_count(0x8000_1000, 508<<10))
```

**Recorded output (`Python 3.13.15`, Linux x86_64, 2026-11-19):**

```text
Two-phase NO_ACCESS: (True, ['SAFE across all 10 reachable interleavings'])
Naive REALM->NS: (False, ['EL3(naive): scrub DRAM to ZERO while Realm still mapped', 'Realm_Cache: evict dirty SECRET to DRAM', 'EL3(naive): write_gpt(GPT_GPI_NS)', 'NS_Cache: evict STALE_NS (cold read next)', 'VIOLATION: NS observed SECRET (gpi=0x9, dram=SECRET, ns_cache=None)'])
RMPADJUST: ['OK', 'FAIL_PERMISSION', 'FAIL_PERMISSION', 'OK', 'FAIL_INPUT']
pKVM reachability: (7, 0)
NAPOT(0x80400000, 4MiB): 0x2017ffff
NAPOT cover 508KiB@0x80001000: 7
```

## Revalidation

To cheaply revalidate whether these invariants still hold against newer upstream revisions:

1. **Arm CCA GPT & RMM:** Diff `lib/gpt_rme/gpt_rme.c` in `ARM-software/arm-trusted-firmware` around `gpt_undelegate_pas` to confirm `GPT_GPI_NO_ACCESS -> tlbi_page_dsbosh -> flush_page_to_popa(outgoing) -> flush_page_to_popa(NS) -> GPT_GPI_NS` ordering remains intact (or inspect the FIRME replacement path when `FIRME_SUPPORT=1`). Diff `lib/granule/include/granule_types.h` in `TF-RMM/tf-rmm` for new granule states and lock-order updates.
2. **OP-TEE Shared Memory Boundary:** Diff `core/arch/arm/kernel/thread_optee_smc.c` (`get_msg_arg`, `std_entry_with_parg`) and `core/tee/entry_std.c` (`copy_in_params`) to confirm `READ_ONCE` single-read snapshotting and `ADD_OVERFLOW` checks on every new parameter type.
3. **COCONUT-SVSM VMPL0:** Diff `kernel/src/protocols/core.rs` (`core_create_vcpu`) to verify `PVALIDATE_LOCK` + `rmp_revoke_guest_access` + `flush_tlb_global_sync_page` still strictly precede `check_vmsa`, and diff `kernel/src/cpu/vc.rs` for any newly allowed `#VC` exit codes.
4. **Intel TDX & Linux `#VE`:** Diff `src/td_dispatcher/vm_exits/tdg_vp_vmcall.c` on `intel/confidential-computing.tdx.tdx-module` (`tdx_2.0` or newer) for `gpr_check_mask` and register scrubbing, and diff `arch/x86/coco/tdx/tdx.c` in `torvalds/linux` around `virt_exception_kernel()` and `handle_mmio()` to confirm private-GPA EPT violations still panic and split-page MMIO accesses remain rejected.
5. **Linux pKVM Ownership Lattice:** Diff `arch/arm64/kvm/hyp/include/nvhe/memory.h` (`enum pkvm_page_state`) and `arch/arm64/kvm/hyp/nvhe/mem_protect.c` (`__pkvm_host_donate_guest`, `__pkvm_host_reclaim_page_guest`, `__pkvm_host_share_guest`), then rerun the inline Python reachability probe after updating any newly introduced states or transitions.
