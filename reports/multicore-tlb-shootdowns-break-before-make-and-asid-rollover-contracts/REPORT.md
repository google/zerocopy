# Multicore TLB Shootdowns, AArch64 Break-Before-Make, and ASID Rollover Verification Contracts

## Summary

On multicore systems, virtual-memory translation is **relaxed and asynchronous across hardware threads**: each core caches both leaf translations (TLBs) and intermediate directory pointers (paging-structure / page-walk caches, PWCs), and may start speculative page-table walks at any time while a root table is active. Closing multicore soundness gaps across x86-64, AArch64, and RV64 requires four invariants that single-core barrier models omit:

1. **Two-Phase Shootdown Barrier Before Page-Table Frame Recycling (`ShootdownBarrier`):** Clearing a non-leaf directory entry and flushing only the local core leaves remote cores holding stale PWC entries pointing to the unmapped page-table frame $F_{\text{pt}}$. If $F_{\text{pt}}$ is recycled into writable user memory before remote invalidation completes, a remote speculative or architectural walk dereferences attacker-controlled bytes in $F_{\text{pt}}$ as live PTEs, yielding arbitrary physical-memory access. Sound reclamation requires a strict two-phase barrier—(Phase 1) global store visibility of the invalid PTE (`DSB ISHST` / `fence w,rw` / x86 store visibility) *before* remote invalidation (`TLBI *IS` / `SBI_RFENCE` / IPI `INVLPG`/`INVPCID`), followed by (Phase 2) synchronous remote completion (`DSB ISH` / OpenSBI `tlb_sync` / blocking IPI ACK) *before* returning $F_{\text{pt}}$ to the frame allocator (plus an RCU grace period or IRQ-disabling sync if lockless software walkers exist). **Basis: normative, source, execution.**
2. **AArch64 Break-Before-Make (`BBM`) vs. `FEAT_BBM` (`BBML0`–`BBML3`) and Cross-ISA Asymmetry:** Under Arm DDI 0487, overwriting an active valid descriptor with a different output address, block size, memory type, or shareability attribute without Break-Before-Make (`Valid=0 -> DSB ISHST -> TLBI *IS -> DSB ISH -> new Valid=1`) is `CONSTRAINED UNPREDICTABLE` and may trigger a **TLB conflict abort** or silent attribute/address amalgamation. Under `ID_AA64MMFR2_EL1.BBM[55:52]`, Level 1 (`0b0001`) relaxes block-size transitions only with `nT=1`, Level 2 (`0b0010`, `BBML2`) drops `nT` **but still permits TLB conflict aborts**, and only Level 3 (`0b0011`, `BBML3`, formerly Linux `BBML2_NOABORT`, plus explicit MIDR allowlists) guarantees abort-free live block splitting/merging—yet still requires `TLBI` + `DSB ISH` before freeing discarded sub-tables. By contrast, RISC-V (`supervisor.adoc:1324–1329, 1784–1794`) defines multi-hit leaf/non-leaf overlap as unpredictably choosing either entry without a conflict abort, while x86-64 (Intel SDM Vol. 3A §4.10.2.3/§4.10.4.2) forbids uninvalidated page-size or memory-type changes. **Basis: normative, source, execution.**
3. **Multicore ASID / PCID Generation Rollover Safety (`AsidGen`):** Reusing hardware ASIDs across cores without synchronizing in-flight executions causes cross-domain TLB aliasing (ABA rollover). Lock-free fast-path allocators (`torvalds/linux` `arch/arm64/mm/context.c`) avoid rollover IPI storms by combining a monotonic `asid_generation`, atomic `active_asids` (`cmpxchg_relaxed` racing rollover `xchg_relaxed(..., 0)`), per-CPU `reserved_asids` (pinning active ASIDs across arbitrary consecutive rollovers), and a `tlb_flush_pending` mask forcing `local_flush_tlb_all()` before any rolled-over core enters a new domain. On x86-64, per-CPU dynamic PCIDs (`TLB_NR_DYN_ASIDS = 6`) paired with per-`mm` `tlb_gen` and `CR3_NOFLUSH` (bit 63) still mandate unconditional IPI shootdowns to lazy-TLB CPUs whenever `freed_tables` is set. **Basis: normative, source, execution.**
4. **Minimal TCB Contract Hooks for Kernels and Userland `munmap` / JIT Teardown:** Verifying multicore kernels and userland JIT/FFI runtimes does not require embedding microarchitectural TLB walkers or branch predictors inside a verifier TCB. Three constructive `Type 0` ghost contracts—`NoStaleTlb`/`NoStalePwc`, `AsidGen`, and `ShootdownBarrier`—capture the exact architectural proof obligations, including userland JIT code-teardown coupling between synchronous OS `munmap`/`mprotect` TLB shootdowns and remote core-serializing / I-cache barriers (`membarrier(MEMBARRIER_CMD_PRIVATE_EXPEDITED_SYNC_CORE)`, `IC IVAU + DSB ISH + ISB`, `sbi_remote_fence_i`). All three failure modes and their closing invariants are mechanically proved with zero `sorry` and zero `Classical.choice` in `support/multicore_tlb_shootdown_probe.lean` (`Lean 4.34.1`). **Basis: derived, execution.**

## Applicability

This report specifies multicore virtual-memory shootdown, Break-Before-Make, ASID/PCID rollover, and userland code-teardown verification contracts for 64-bit SMP kernels, hypervisors, and userland JIT/runtime verifiers targeting **AArch64 (`VMSAv8-64`)**, **x86-64 (`IA-32e` + `PCID`/`INVPCID`)**, and **RISC-V (`Sv39`/`Sv48`/`Sv57` + `SBI_RFENCE` + `Svinval`)**. **Basis: normative, source.**

Within `zerocopy/reference`, this report strictly targets the **multicore and transition-safety delta** left open by four complementary single-hart and bootstrap reports:
- `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` covers single-hart PWC vs. leaf TLB invalidation asymmetry (`SFENCE.VMA va, asid` vs. `INVLPG` vs. `TLBI VALE1IS`/`VAE1IS`), temporal `W -> X` `fence.i` coherence, and `sail-riscv`/`x86isa` simulator limitations.
- `riscv-sv39-asid-zero-aliasing-hardware-ad-bits-and-speculative-tlb-fill-semantics` covers RISC-V `ASIDLEN = 0` register-specifier sensitivity, single-hart `satp` switch ordering, `Svade`/`Svadu` speculative A/D writes, and `PMP` access-fault interleavings.
- `hardware-asid-width-discovery-conditional-satp-switch-fencing-and-boot-pt-barriers` covers `ASIDLEN` WARL probing, unprobed conditional `satp` switch fencing, and boot page-table construction barriers.
- `isa-page-table-tlb-coherence-sail-trap-contracts-and-toctou-dma-fetch-oracles` covers single-walk `Sv39`/x86-64 decoding, register-frame trap contracts, and shared-memory TOCTOU double-fetch oracles.

Here, the primary architectural specifications (Arm DDI 0487, Intel SDM Vol. 3A §4.10, `riscv/riscv-isa-manual@c05f1725`, `riscv-non-isa/riscv-sbi-doc@8a545eff`) are cross-checked against production SMP implementations (`torvalds/linux@5f22fb20`, `seL4/seL4@08c7e5fd`, `riscv-software-src/opensbi@61f1973b`), relaxed-VM formal models (Simner et al. ESOP 2022; Syeda & Klein JAR 2020), and a standalone Lean 4 (`v4.34.1`) mechanization (`support/multicore_tlb_shootdown_probe.lean`). Findings for `BBML3` (`ID_AA64MMFR2_EL1.BBM = 0b0011`) reflect the Linux `5f22fb20` kernel encoding and CPU allowlist; earlier kernels or hypervisors without `BBML3` support must fall back to strict BBM (`BBML0`) or TLB-conflict-abort handling. **Basis: source, documentation.**

## Findings

### 1. Multicore Relaxed-TLB & Speculative PWC Hazards on Page-Table Recycling

**Basis: normative, source, execution.**

Data-frame unmapping (`munmap` of a leaf page) and page-table-frame unmapping (`free_pgtables` / `unmapPageTable`) have different failure severities under multicore relaxed virtual memory:

- **Stale Leaf TLB (Data-Frame UAF):** If Core 0 clears a leaf PTE and frees data frame $F_{\text{data}}$ before Core 1 invalidates its leaf TLB, Core 1 retains direct read/write access to $F_{\text{data}}$ after reallocation to another domain.
- **Stale Non-Leaf PWC (Page-Table-Frame UAF -> Arbitrary Physical Access):** Because hardware walkers cache intermediate directory pointers (`PML4E`/`PDPTE`/`PDE` on x86-64; table descriptors on AArch64; non-leaf PTEs on RISC-V) and may initiate **speculative** walks at any time while a root table is loaded (`riscv/riscv-isa-manual@c05f1725` `src/priv/supervisor.adoc:1797–1817`; Simner et al., ESOP 2022), recycling a freed page-table page $F_{\text{pt}}$ before remote PWC invalidation completes lets a remote core walk *through* its stale PWC entry directly into $F_{\text{pt}}$. If $F_{\text{pt}}$ is reallocated to untrusted user memory, arbitrary user-written 64-bit words in $F_{\text{pt}}$ are interpreted by Core 1's hardware walker as valid PTEs pointing to arbitrary physical frames (including privileged kernel memory).

Production SMP kernels expose three load-bearing mechanisms that verifiers must model:

1. **Lazy-TLB CPUs Cannot Be Skipped When Freeing Page Tables (`torvalds/linux@5f22fb20`, `arch/x86/mm/tlb.c:1349–1362`):**
   On x86-64, CPUs in lazy TLB mode (running kernel threads while keeping a previous user `mm` loaded in `CR3`) may normally defer data-page flushes until their next context switch (`on_each_cpu_cond_mask(should_flush_tlb, ...)`). However, when `info->freed_tables || mm_in_asid_transition(info->mm)` is true, Linux forces synchronous IPIs to **every** CPU in `cpumask` (`on_each_cpu_mask(cpumask, flush_tlb_func, (void *)info, true)`), explicitly *"to prevent CPUs in lazy TLB mode from tripping up on the new contents of what used to be page tables, while doing a speculative memory access."*
2. **Dual Hardware + Software Walker Reclamation Barrier (`torvalds/linux@5f22fb20`, `mm/mmu_gather.c:270–329, 360–407`):**
   `tlb_flush_mmu()` enforces strict sequencing:
   $$\text{Clear PTEs} \xrightarrow{\text{store visible}} \texttt{tlb\_flush\_mmu\_tlbonly()} \xrightarrow{\text{hw PWC/TLB clear}} \texttt{tlb\_table\_flush()} \xrightarrow{\text{RCU / IRQ-sync}} \text{Free PT frames}$$
   Specifically, `tlb_table_flush()` (`L360–369`) invokes `tlb_table_invalidate(tlb)` (stopping hardware walkers via synchronous TLB/PWC shootdown) *before* `tlb_remove_table_free(*batch)` (`call_rcu(&batch->rcu, tlb_remove_table_rcu)`, `L292–295`, or `tlb_remove_table_sync_one()` via `smp_call_function` IPI, `L275–285`), which stops lockless *software* walkers (`get_user_pages_fast` under `local_irq_disable()`).
3. **RISC-V Two-Phase Shootdown (`SBI_RFENCE` + `Svinval`) & Deadlock-Safe Synchronous Wait:**
   - **Normative 4-step protocol (`riscv/riscv-isa-manual@c05f1725`, `supervisor.adoc:1209–1221`):** `#norm:sfence_vma_local_only` mandates that `SFENCE.VMA` orders *only* the local hart. Remote shootdowns require: (1) local data fence (`fence w,rw`) making PTE writes globally visible, (2) IPI delivery, (3) remote `SFENCE.VMA` (with `rs1 = x0` whenever non-leaf PTEs changed), and (4) completion signal back to the initiator.
   - **`SBI_RFENCE` (`EID 0x52464E43`, `riscv-non-isa/riscv-sbi-doc@8a545eff`, `src/ext-rfence.adoc:1–106, 258–272`):** Defines `sbi_remote_fence_i` (`FID #0`), `sbi_remote_sfence_vma` (`FID #1`), and `sbi_remote_sfence_vma_asid` (`FID #2`). Passing `start_addr = 0, size = 0` or `size = 2^XLEN - 1` invalidates the entire address space (including PWCs).
   - **OpenSBI synchronous completion (`riscv-software-src/opensbi@61f1973b`, `lib/sbi/sbi_tlb.c:253–294, 388–404`):** `sbi_tlb_request()` increments each target's completion counter (`tlb_sync`) and blocks in `tlb_sync()` (`while (atomic_read(tlb_sync) > 0) tlb_process_once(scratch)`), actively draining its own incoming TLB FIFO while waiting to prevent two-hart mutual-shootdown deadlock.
   - **`Svinval` batching (`riscv/riscv-isa-manual@c05f1725`, `src/priv/svinval.adoc:11–39`; `torvalds/linux@5f22fb20`, `arch/riscv/mm/tlbflush.c:33–41`):** Splits `SFENCE.VMA` into `SFENCE.W.INVAL` (orders prior visible stores before `SINVAL.VMA`), batched `SINVAL.VMA` instructions (matching `SFENCE.VMA` `rs1`/`rs2` invalidation scope, including the leaf-only `rs1 ≠ x0` rule!), and `SFENCE.INVAL.IR` (orders prior `SINVAL.VMA` before subsequent implicit PT walks). Omitting `SFENCE.W.INVAL` or `SFENCE.INVAL.IR` leaves `SINVAL.VMA` unordered relative to PTE stores or walks.
   - **`seL4` SMP RISC-V (`seL4/seL4@08c7e5fd`, `include/arch/riscv/arch/machine.h:105–130`):** `sfence()` runs `fence_w_rw(); sfence_local(); sbi_remote_sfence_vma(mask, 0, 0);` and `ifence()` pairs `fence.i` with `sbi_remote_fence_i(mask)`. Notice `hwASIDFlush(asid)` (`L125–130`) omits an explicit `fence_w_rw()` before `hwASIDFlushLocal(asid); sbi_remote_sfence_vma_asid(...)`, relying on SBI's internal IPI/fence ordering and `seL4`'s big kernel lock.

### 2. AArch64 Break-Before-Make (`BBM`) Constraints vs. `FEAT_BBM` (`BBML0`–`BBML3`)

**Basis: normative, source, documentation, execution.**

Under Arm DDI 0487 (VMSA translation-table update rules) and Simner et al. (ESOP 2022, DOI `10.1007/978-3-030-99336-8_6`):

- **When BBM Is Mandatory (Baseline `BBML0`):** Any transition between two **valid** descriptors that changes: (1) the output physical address (OA), (2) the translation granule / block size (e.g., splitting a 2 MiB block into a table of 4 KiB pages, or collapsing 4 KiB pages into a 2 MiB block), (3) memory type (Normal vs. Device), cacheability, or shareability attributes, (4) the `nG` (non-global) bit, or (5) the `Contiguous` hint bit.
- **When BBM Is NOT Required:** Invalid $\to$ Valid, Valid $\to$ Invalid, permission changes (`AP`/`UXN`/`PXN`) keeping OA/size/memory-type unchanged, hardware AF/DBM updates, and software-defined bits.
- **Failure Mode on BBM Violation:** Hardware may hold multiple overlapping TLB entries matching the same `(ASID, VA)` with incompatible granules or OAs. Arm DDI 0487 classifies this as **`CONSTRAINED UNPREDICTABLE`**: an implementation may either raise a synchronous **TLB conflict abort** (Data/Instruction Abort with FSC `0b110000` in `ESR_ELx`) *or* silently amalgamate attributes/output addresses, causing memory corruption or isolation loss.
- **Canonical Multicore AArch64 BBM Sequence (`torvalds/linux@5f22fb20`, `arch/arm64/include/asm/tlbflush.h:249–293, 368–390`):**
  1. Write invalid descriptor (`Valid = 0`) to the translation table entry.
  2. `DSB ISHST` — ensure the invalid descriptor store is globally visible to all PEs' hardware walkers in the Inner Shareable domain (`tlbflush.h:288`).
  3. `TLBI <op>IS` — broadcast Inner-Shareable invalidation (`TLBI VAE1IS` / `VAAE1IS` / `ASIDE1IS`; note `VALE1IS` is leaf-only and spares walk caches! Under KPTI, issue for both kernel and user ASIDs via `__tlbi_user`, `tlbflush.h:44–47, 384–386`).
  4. `DSB ISH` — block until broadcast `TLBI` completes on all Inner-Shareable PEs (`__tlbi_sync_s1ish`, `tlbflush.h:249–267`, plus errata repeat-TLBI / SME DVM sync where applicable).
  5. Write new valid descriptor (`Valid = 1`).
  6. `DSB ISHST` (make new descriptor visible to walkers) + `ISB` on the executing PE (and a context synchronization event on remote PEs before executing newly mapped instructions or relying on new kernel mappings, `tlbflush.h:291–292`).
- **`FEAT_BBM` Relaxation Hierarchy (`ID_AA64MMFR2_EL1.BBM[55:52]`, `torvalds/linux@5f22fb20`, `arch/arm64/tools/sysreg:2295–2310`, `arch/arm64/kernel/cpufeature.c:2011–2042`, `arch/arm64/mm/mmu.c:779–835`):**

| `ID_AA64MMFR2_EL1.BBM` | Level Name | Block-Size Change Without BBM (Same OA & Compatible Attrs) | TLB Conflict Abort Possible? | Still Requires `TLBI` + `DSB ISH` Before Freeing Old Sub-Tables? |
| :--- | :--- | :--- | :--- | :--- |
| `0b0000` | Level 0 (`BBML0`) | **Forbidden** (`CONSTRAINED UNPREDICTABLE`: silent corruption or abort) | Yes | **Yes** |
| `0b0001` | Level 1 (`BBML1`) | Permitted **only** if new block descriptor sets `nT = 1` (preventing block TLB caching until `TLBI` completes) | Yes (if `nT = 0` or conflict occurs) | **Yes** |
| `0b0010` | Level 2 (`BBML2`) | Permitted without `nT = 1` (no silent OA/attribute amalgamation) | **Yes** — hardware may still raise a TLB conflict abort | **Yes** |
| `0b0011` (or MIDR allowlist) | Level 3 (`BBML3`, formerly Linux `BBML2_NOABORT`) | Permitted without `nT = 1` and guaranteed **abort-free** (`split_kernel_leaf_mapping()` in `mmu.c:779–835`) | **No** (assuming no unmitigated CPU erratum, e.g., Erratum 3683289 in `cpufeature.c:2026–2028`) | **Yes** (stale PWC/TLB can still reference collapsed sub-table pages!) |

- **Cross-ISA Contrast for Block-Size / Attribute Transitions:**
  - **RISC-V (`riscv/riscv-isa-manual@c05f1725`, `supervisor.adoc:1324–1329, 1784–1794`):** Upgrading a 4 KiB page subtree to a superpage without clearing the non-leaf PTE and executing `SFENCE.VMA` (`rs1 = x0`) permits simultaneous matching TLB entries; the ISA specifies *"it is unpredictable whether the old non-leaf PTE or the new leaf PTE is used, but the behavior is otherwise well defined"* (no conflict abort). However, recycling the old L0 table page before `SFENCE.VMA x0, asid` across all harts still triggers the PWC use-after-free of §1.
  - **x86-64 (Intel SDM Vol. 3A §4.10.2.3, §4.10.4.1–§4.10.4.2; `torvalds/linux@5f22fb20`, `arch/x86/include/asm/invpcid.h:20–48`):** Intel prohibits creating multiple matching translations of differing page size or memory type without invalidation; recommended invalidation clears/updates the PTE and shoots down all cores (`INVLPG` or `INVPCID`). Crucially, `INVPCID` has four types with an easy-to-miss global-entry subtlety:
    - `Type 0` (`INVPCID_TYPE_INDIV_ADDR`): invalidates `(pcid, addr)` **excluding global entries** (unlike `INVLPG`, which *does* invalidate a global leaf at `addr`!) and wipes all paging-structure caches for `pcid`.
    - `Type 1` (`INVPCID_TYPE_SINGLE_CTXT`): invalidates all non-global TLB + paging-structure caches for `pcid`.
    - `Type 2` (`INVPCID_TYPE_ALL_INCL_GLOBAL`): invalidates all TLB + paging-structure caches across all PCIDs **including globals**.
    - `Type 3` (`INVPCID_TYPE_ALL_NON_GLOBAL`): invalidates all non-global entries across all PCIDs.

### 3. Multicore ASID & PCID Generation Rollover Races

**Basis: normative, source, execution.**

Hardware ASID spaces are finite (`8` or `16` bits on AArch64 `ID_AA64MMFR0_EL1.ASIDBits`; `0..16` bits on RV64 `satp.ASID`; `12` bits / `4096` PCIDs on x86-64 `CR3[11:0]`). Naive multicore recycling creates an **ABA aliasing race**: Core 0 exhausts ASIDs, increments the generation, and assigns hardware ASID `a` to Process B while Core 1 is still executing (or retains cached TLB/PWC entries for) Process A under `(a, gen - 1)`.

Three distinct production designs solve this with different verification obligations:

1. **Generation + Per-CPU `active_asids` / `reserved_asids` + Deferred `tlb_flush_pending` (`torvalds/linux@5f22fb20`, `arch/arm64/mm/context.c:104–271`):**
   - Each `mm->context.id` packs `(generation | hw_asid)`. Fast-path context switch (`check_and_switch_context`, `L240–244`) checks `old_active_asid != 0 && asid_gen_match(asid)` and executes `atomic64_cmpxchg_relaxed(&active_asids, old_active_asid, asid)`.
   - On ASID exhaustion under `cpu_asid_lock`, `new_context()` (`L202–207`) increments `asid_generation` by `ASID_FIRST_VERSION` (`1 << 16`) and calls `flush_context()` (`L104–132`), which:
     1. Resets `asid_map` (preserving `pinned_asid_map` and KPTI even/odd reserved bits, `L79–99`).
     2. Atomically swaps every CPU's `active_asids` to `0` (`atomic64_xchg_relaxed(..., 0)`, `L113`). Because atomic RMWs to one location are totally ordered, any concurrent fast-path `cmpxchg_relaxed` either returns `0` (forcing the slow path under `cpu_asid_lock`) or commits before the `xchg` so its new ASID is captured in `reserved_asids` (`L227–239`).
     3. **Multi-rollover preservation (`L121–124`):** If `asid == 0` (the CPU never switched out since an earlier rollover), `flush_context()` reloads `per_cpu(reserved_asids, i)` and re-sets its bit in `asid_map`, preventing an idle/long-running CPU's live ASID from ever being stolen across consecutive rollovers.
     4. Sets `cpumask_setall(&tlb_flush_pending)` (`L131`). No rollover IPI is sent; instead, each CPU entering the slow path checks `cpumask_test_and_clear_cpu(cpu, &tlb_flush_pending)` and calls `local_flush_tlb_all()` (`TLBI VMALLE1` + `DSB NSH` + `ISB`, `tlbflush.h:360–366`) *before* installing its new `active_asids` (`context.c:254–258`).
   - **Invariant requirement:** Requires `NUM_USER_ASIDS > num_possible_cpus()` (plus pinned/KPTI overhead) so `find_next_zero_bit` (`L207`) always succeeds after reserving active CPUs. Also, under Armv8.2 Common Not Private (`system_supports_cnp()`, `L221–222`), `TTBR0_EL1` must temporarily switch to a reserved zero page before changing ASID/BADDR so shared-TLB PEs do not observe mismatched `(old_BADDR, new_ASID)` pairs.
2. **Per-CPU Dynamic PCIDs + Per-`mm` `tlb_gen` (`torvalds/linux@5f22fb20`, `arch/x86/mm/tlb.c:78–290, 1109–1120`):**
   - Because Intel x86-64 lacks broadcast TLB invalidation, Linux maps each process to a per-CPU slot in `[0, TLB_NR_DYN_ASIDS - 1]` (`6` dynamic PCIDs per CPU, offset by `+1` and split with `X86_CR3_PTI_PCID_USER_BIT` under PTI, `L125–140`) plus an optional global ASID pool (`L285–289`).
   - When switching to `next` (`choose_new_asid`, `L225–272`), if `cpu_tlbstate.ctxs[asid]` matches `next->context.ctx_id` AND its `tlb_gen` equals `next_tlb_gen`, `CR3` is written with `CR3_NOFLUSH` (bit 63, `L183`); otherwise `need_flush = true` writes `CR3` with bit 63 clear (flushing that PCID). Rollover across the 6 per-CPU slots is purely CPU-local (zero cross-CPU ASID lock), trading global ASID coordination for per-`mm` `tlb_gen` tracking and synchronous IPI shootdowns (`flush_tlb_mm_range`, `L1407–1427`).
3. **Synchronous Global Shootdown on ASID Revocation (`seL4/seL4@08c7e5fd`):**
   - In `seL4`, `deleteASID` invokes `hwASIDFlush(asid)` (broadcast `TLBI ASIDE1IS` on AArch64; `sbi_remote_sfence_vma_asid` on SMP RISC-V) before clearing the ASID pool slot, avoiding lazy `tlb_flush_pending` state at the cost of synchronous remote invalidation and requiring all remote cores to switch away from the dying VSpace root *before* final flush so speculative walks cannot re-populate the revoked ASID.

### 4. Cross-Architecture Multicore Comparison Matrix (x86-64 vs. AArch64 vs. RV64)

**Basis: normative, source, derived.**

*(Complements the single-hart opcode table in `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` by focusing strictly on multicore shootdown, BBM, ASID rollover, and JIT teardown semantics.)*

| Multicore Dimension | x86-64 (`IA-32e` + `PCID`/`INVPCID`) | AArch64 (`VMSAv8-64`) | RV64 (`Sv39`/`Sv48`/`Sv57` + `SBI_RFENCE`/`Svinval`) |
| :--- | :--- | :--- | :--- |
| **SMP Shootdown Transport** | Software IPI (`on_each_cpu_mask` + remote `INVLPG`/`INVPCID`/`MOV CR3`); AMD offers hardware `INVLPGB`+`TLBSYNC` | Hardware Inner-Shareable broadcast (`TLBI *IS`) | Software IPI via M-mode `SBI_RFENCE` (`EID 0x52464E43`) or S-mode IPI (`on_each_cpu_mask`) |
| **PTE Store $\to$ Shootdown Ordering** | TSO store visibility + atomic/locked op (`inc_mm_tlb_gen`) before IPI send | Mandatory `DSB ISHST` before `TLBI *IS` | Mandatory `fence w,rw` before IPI / `SBI_RFENCE`; `SFENCE.W.INVAL` before `SINVAL.VMA` |
| **Remote Completion Barrier Before PT Frame Free** | Synchronous IPI ACK (`wait=1`), **including lazy-TLB CPUs** when `freed_tables` is set (`tlb.c:1357`) | `DSB ISH` after `TLBI *IS` (waits for all Inner-Shareable PEs) | Synchronous `SBI_RFENCE` return (`tlb_sync` draining local FIFO) or `wait=1` S-mode IPI + `SFENCE.INVAL.IR` |
| **Remote Pipeline / Fetch Sync After Code or Kernel Remap** | IPI/trap `IRET` or `CPUID`/`SERIALIZE` (I-cache snoops D-cache; fetch pipeline still needs serializing op) | `DC CVAU -> DSB ISH -> IC IVAU -> DSB ISH` + remote `ISB`/exception return (`ERET`) | `fence w,rw` + remote `FENCE.I` (`sbi_remote_fence_i`, `FID #0`) |
| **Block-Size / Attribute Transition Without BBM** | Prohibited for differing page size or memory type without invalidation (Intel SDM Vol. 3A §4.10.2.3/§4.10.4.2) | `CONSTRAINED UNPREDICTABLE` (TLB conflict abort or amalgamation) at `BBML0`; abort-free only at `BBML3` (`ID_AA64MMFR2_EL1.BBM = 0b0011` or allowlist) | Unpredictably chooses old non-leaf or new leaf, otherwise well-defined (`supervisor.adoc:1784–1794`); still unsafe to recycle old PT page before `SFENCE.VMA x0, asid` |
| **Hardware Context Tag Width & Rollover** | 12-bit PCID (`4096`); Linux uses 6 per-CPU dynamic slots + `CR3_NOFLUSH` + `tlb_gen` | 8- or 16-bit ASID (`ID_AA64MMFR0_EL1.ASIDBits`); global `asid_generation` + `active_asids`/`reserved_asids` + `tlb_flush_pending` | `0..16`-bit `WARL` `ASIDLEN`; `ASIDLEN=0` forces flush on switch; `ASIDLEN>0` uses generation + reserved ASIDs + `tlb_flush_pending` |
| **Userland `munmap` / JIT Code Teardown** | `munmap`/`mprotect` IPI shootdown + `membarrier(PRIVATE_EXPEDITED_SYNC_CORE)` (remote serializing IPI) | `munmap`/`mprotect` `TLBI *IS + DSB ISH` + `DC CVAU`/`IC IVAU` + `membarrier(SYNC_CORE)` (remote `ISB`/exception exit) | `munmap`/`mprotect` `SBI_RFENCE` `SFENCE.VMA` + `riscv_flush_icache` (`sbi_remote_fence_i`) |

### 5. Minimal Ghost-State / TCB Contract Hooks (`NoStaleTlb`, `AsidGen`, `ShootdownBarrier`)

**Basis: derived, source.**

Embedding microarchitectural TLB associativity, replacement policies, speculative prefetchers, or hardware page-table walkers into a verifier's trusted computing base (TCB) causes proof blowup and hardware over-specialization. Instead, a sound multicore verifier (for OS kernels *and* userland `munmap`/JIT runtimes) needs only **three abstract ghost-state contract hooks** at the ISA/syscall boundary:

1. **`NoStaleTlb` / `NoStalePwc` (Translation-Cache Coherence Predicate):**
   - **State:** Abstract per-hart sets/lists of cached leaf translations `tlb[h]` and cached non-leaf directory pointers `pwc[h]`, where hardware may nondeterministically insert any currently valid root/leaf translation at any step (capturing arbitrary speculative fills without modeling microarchitectural predictors).
   - **Obligation:**
     - *Page-table safety:* `∀ h e ∈ pwc[h], frameRole(e.ptFrame) ∈ {ptLeaf, quarantined}` (no hart's PWC may ever point to a `userData` or freed frame).
     - *BBM non-conflict:* `∀ h e ∈ tlb[h], liveDesc(e.asid, e.va) = some (e.granule, e.oa)` (excluding simultaneous conflicting entries unless the platform's BBM level explicitly allows same-OA granule transitions).
2. **`ShootdownBarrier` (Two-Phase Frame-Reclamation & `munmap` Contract):**
   - **State:** Per-frame quarantine token `quarantined` with a per-hart acknowledgment predicate `shootAck : FrameId -> HartId -> Bool` (plus an optional `swWalkSync : Bool` flag when lockless software walkers exist).
   - **Transitions:**
     - *Phase 1 (Break & Quarantine):* Clear all root/parent PTEs pointing to `f`, issue the global store-visibility fence (`DSB ISHST` / `fence w,rw`), transition `f : ptLeaf -> quarantined`, reset `shootAck f := fun _ => false`. Frame contents remain immutable while `quarantined`.
     - *Phase 2 (Remote Invalidation & ACK):* Each hart `h` executes a PWC-covering invalidation (`SFENCE.VMA x0, asid` / `TLBI ASIDE1IS + DSB ISH` / `INVLPG`/`INVPCID`), discharging `NoStalePwcForFrame st h f`, and sets `shootAck f h := true`.
     - *Phase 3 (Reclaim):* `recycle(f)` requires `ShootdownComplete st f := (frameRole f = quarantined) ∧ (∀ h, shootAck f h = true)`.
3. **`AsidGen` (Monotonic Generation & Pending-Flush Contract):**
   - **State:** `(curGen, mmAsid : MmId -> HwAsid × Gen, activeMm : HartId -> MmId, reservedAsid : HartId -> HwAsid, flushPending : HartId -> Bool)`.
   - **Obligation:** On generation rollover (`curGen -> curGen + 1`), snapshot every hart's active `hwAsid` into `reservedAsid`, forbid allocating any reserved `hwAsid`, and set `flushPending h := true` for all harts. Any hart `h` with `flushPending h = true` must execute `local_flush_tlb_all()` before entering a domain under `curGen + 1`, preserving `∀ h tag, flushPending h = false -> tag.hwAsid = activeHwAsid(h) -> tag.mmId = activeMm(h)`.

**Userland `munmap` and JIT Code-Teardown Composition:**
For userland Rust/JIT runtimes (e.g., Wasm/eBPF/query JITs tearing down or repurposing `W^X` code pages across threads), the OS kernel discharges `ShootdownBarrier` synchronously inside `munmap()` / `mprotect()` (`tlb_finish_mmu()` guarantees no remote thread holds a stale TLB/PWC entry to the unmapped physical page upon syscall return). However, **TLB shootdown alone does not flush remote instruction fetch pipelines or non-snooping I-caches** when a code buffer is recycled in-place (`RX -> RW -> RX`) or patched:
- On Linux (`torvalds/linux@5f22fb20`, `kernel/sched/membarrier.c:142–208, 330–345`), userland JIT teardown/republish must pair `mprotect`/`munmap` with `membarrier(MEMBARRIER_CMD_PRIVATE_EXPEDITED_SYNC_CORE, 0)`, which dispatches `ipi_sync_core()` (`smp_mb(); sync_core_before_usermode();`) to every sibling thread's CPU so each core executes a serializing instruction (`CPUID`/`SERIALIZE`/`IRET` on x86-64; `ISB`/`ERET` on AArch64) before re-entering userland, combined with explicit `DC CVAU -> DSB ISH -> IC IVAU -> DSB ISH` (AArch64) or `riscv_flush_icache` -> `sbi_remote_fence_i` (RV64). In the verifier contract, userland `CodeCap` revocation therefore requires **both** `ShootdownBarrier` (from `munmap`/`mprotect`) **and** `CoreSyncBarrier` (from `membarrier(SYNC_CORE)` / remote I-cache flush) before returning code memory to a writable pool.

### 6. Kernel-Checked Lean 4 (`v4.34.1`) Mechanization & Epistemic Calibration

**Basis: execution, derived.**

The self-contained Lean 4 (`v4.34.1`) module preserved at `support/multicore_tlb_shootdown_probe.lean` (`prelude` + `Init.Core`, `Init.Tactics`, `Init.Data.List.Basic`, `Init.Data.Nat.Basic`; constructive `Type 0`; zero `sorry`, zero custom `axiom`, zero `unsafe`/`partial`/`opaque`/`Classical.choice`/`Lean.ofReduceBool`/`._unsafe_rec`) mechanizes both the concrete multicore counterexamples and the closing ghost-contract invariants:

| Theorem in `MulticoreTlbShootdown` | Category | Property Proved | Axiom Closure |
| :--- | :--- | :--- | :--- |
| `stale_pwc_uaf_on_premature_pt_recycle` | Counterexample (2-hart) | Local-only flush + premature PT frame recycle lets `h1` walk stale PWC entry into retyped `userData` and resolve `kernelSecret` (`some 99`) | `[none]` |
| `bbm_violation_creates_tlb_conflict` | Counterexample (BBM) | Overwriting 2 MiB block with 4 KiB page without BBM produces dual matching TLB entries (`HasTlbConflict`) on `h1` | `[none]` |
| `asid_rollover_without_flush_aliases_domains` | Counterexample (ASID) | Reassigning `hwAsid = 1` across generation rollover without remote flush causes `h1` to alias domain `10` into domain `20` | `[none]` |
| `fillPwc_preserves_PtSafeInv` | Safety Preservation | Speculative/architectural PWC fills on any hart preserve `PtSafeInv` | `[none]` |
| `safeUnmapAndQuarantine_preserves_PtSafeInv` | Safety Preservation | Phase-1 root PTE clear + quarantine transition preserves `PtSafeInv` | `[none]` |
| `safeHartAckShootdown_preserves_PtSafeInv` | Safety Preservation | Phase-2 per-hart PWC flush + ACK update preserves `PtSafeInv` | `[propext]` |
| `safeRecycleAfterShootdown_preserves_PtSafeInv` | Safety Preservation | Phase-3 arbitrary attacker overwrite of recycled `ptFrame` preserves `PtSafeInv` once `ShootdownComplete` holds | `[none]` |
| `ptSafeInv_excludes_uaf_and_secret_access` | Safety Corollary | Under `PtSafeInv`, no hart's PWC walk can touch a `userData` frame or resolve a `kernelSecret` frame | `[none]` |
| `bbm_update_preserves_no_conflict` | BBM Safety | Canonical `Break -> TLBI ISH + DSB ISH -> Make` preserves `TlbMatchesLive` and `¬HasTlbConflict` across arbitrary granule/OA changes | `[none]` |
| `asid_rollover_flush_preserves_isolation` | ASID Safety | Generation rollover setting `flushPending = true` + local TLB flush on switch preserves `AsidGenInv` | `[none]` |

**Epistemic Calibration (Evidence Tiers):**
- **`[normative + source]`:** Cross-ISA invalidation scopes, `SBI_RFENCE` EID/FIDs, `Svinval` ordering, Arm `ID_AA64MMFR2_EL1.BBM` encodings (`0b0000`–`0b0011`), Linux `mmu_gather.c` / `arch/arm64/mm/context.c` / `arch/x86/mm/tlb.c` / `kernel/sched/membarrier.c`, OpenSBI `tlb_sync`, and `seL4` SMP `sfence` are directly verified against pinned upstream revisions and architectural manuals.
- **`[kernel-checked proof — abstract 2-hart model]`:** The Lean 4 probe provides a kernel-checked proof of the **contract logic** (that omitting remote shootdown/BBM/rollover-flush violates safety and enforcing `ShootdownBarrier` + `BBM` + `AsidGen` closes the races in the abstract 2-hart operational model). It does **not** verify silicon microarchitecture, hardware errata (such as Cortex/Ampere `BBM` errata), or full machine-code lowering of Linux/seL4 C/assembly.

## Boundaries

- **`known not to apply` — Single-core TLB/PWC flush proofs as multicore PT-recycling safety:** Proving local `SFENCE.VMA x0, asid` or local `INVLPG` sufficiency (as in single-hart models) is **known not to apply** to multicore page-table frame recycling, because a remote core's stale PWC entry can walk into a retyped frame (`stale_pwc_uaf_on_premature_pt_recycle`).
- **`known not to apply` — `FEAT_BBM` Level 2 (`BBML2`, `0b0010`) as abort-free block splitting:** `ID_AA64MMFR2_EL1.BBM = 0b0010` prevents silent OA/attribute amalgamation on same-OA block-size changes, but is **known not to apply** as a guarantee against synchronous TLB conflict aborts; abort-free splitting without a conflict-abort handler requires `BBML3` (`0b0011` or vendor-verified MIDR allowlist) and still requires `TLBI` + `DSB ISH` before freeing replaced sub-table pages.
- **`known not to apply` — `INVPCID` Type 0 (`INDIV_ADDR`) for global kernel pages:** Unlike `INVLPG` (which invalidates global leaf entries at `addr`), `INVPCID` Type 0 skips global (`G = 1`) entries; using Type 0 to shoot down modified global kernel mappings is **known not to apply** (requires `INVLPG` or `INVPCID` Type 2).
- **`known not to apply` — `munmap` / `mprotect` TLB shootdown alone for in-place multicore JIT code reuse:** Synchronous kernel TLB shootdowns ensure no stale VA $\to$ PA translation survives `munmap`, but are **known not to apply** as a substitute for remote instruction-pipeline serialization (`membarrier(SYNC_CORE)`) and I-cache invalidation (`IC IVAU + ISB` / `sbi_remote_fence_i`) when rewriting executable code regions.
- **`not examined` — Two-stage hypervisor nested shootdowns and IOMMU/SMMU `IOTLB`/`ATS` invalidation:** Stage-2 nested virtualization (`TLBI IPAS2E1IS` + `TLBI VMALLE1IS`, `HFENCE.GVMA`/`HFENCE.VVMA`, `INVEPT`, `VMID` rollover) and device-side DMA `IOTLB`/`PRI` invalidations were **not examined** in this package.
- **`not examined` — Hardware broadcast TLB shootdowns on AMD x86-64 (`INVLPGB` + `TLBSYNC`) and Arm `FEAT_TLBIRANGE` / `FEAT_TLBIW`:** Range-hinted broadcast encodings (`TLBI RVAE1IS`, `TTL` level hints) and AMD's `INVLPGB`/`TLBSYNC` broadcast protocol were **not examined** beyond noting Linux's `arch/arm64/include/asm/tlbflush.h` helper structure.
- **`unknown` — Microarchitectural compliance with `BBML3` across unlisted silicon revisions:** As evidenced by Linux's explicit MIDR allowlist and erratum gating (`arch/arm64/kernel/cpufeature.c:2011–2037`, e.g., Erratum 3683289), whether a given CPU revision honors abort-free `BBML3` without silicon errata is **unknown** from ISA specifications alone and must be audited per-CPU errata sheet.

## Evidence

| Subject / Artifact | Exact Coordinates | Role & Key Fact Verified |
| :--- | :--- | :--- |
| `riscv/riscv-isa-manual` | `c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `src/priv/supervisor.adoc:1209–1221, 1324–1329, 1784–1817`; `src/priv/svinval.adoc:11–39` | `normative`: `#norm:sfence_vma_local_only` 4-step SMP shootdown; multi-hit leaf/non-leaf superpage upgrade rule (unpredictable choice, well-defined, no conflict abort); speculative walk lifetime; `Svinval` (`SFENCE.W.INVAL` -> `SINVAL.VMA` -> `SFENCE.INVAL.IR`). |
| `riscv-non-isa/riscv-sbi-doc` | `8a545effe9b50484ff897d9815d7d9015cdef203`, `src/ext-rfence.adoc:1–106, 258–272` | `normative`: `SBI_RFENCE` (`EID 0x52464E43`) `FID #0` (`sbi_remote_fence_i`), `FID #1` (`sbi_remote_sfence_vma`), `FID #2` (`sbi_remote_sfence_vma_asid`), and full-space `(0, 0)` / `2^XLEN - 1` range convention. |
| `riscv-software-src/opensbi` | `61f1973bd50338b36c52dc34006f76d464ca4f34`, `lib/sbi/sbi_tlb.c:253–294, 388–404` | `source`: Synchronous completion counter `tlb_sync` waiting on all remote harts while calling `tlb_process_once()` to avoid mutual-shootdown deadlock. |
| `torvalds/linux` (AArch64 BBM & TLBI) | `5f22fb20497f4983094131f00a734362300d22d2`, `arch/arm64/tools/sysreg:2295–2310`; `arch/arm64/kernel/cpufeature.c:497–502, 2011–2042`; `arch/arm64/mm/mmu.c:779–835`; `arch/arm64/include/asm/tlbflush.h:44–47, 249–293, 360–390` | `source`: `ID_AA64MMFR2_EL1.BBM[55:52]` (`0`–`3`), `cpu_supports_bbml3()` MIDR allowlist & Erratum 3683289, `split_kernel_leaf_mapping()`, canonical `DSB ISHST -> TLBI *IS -> DSB ISH [-> ISB]` template, KPTI `__tlbi_user`. |
| `torvalds/linux` (AArch64 ASID Rollover) | `5f22fb20497f4983094131f00a734362300d22d2`, `arch/arm64/mm/context.c:20–39, 79–271` | `source`: `asid_generation`, `active_asids` (`cmpxchg_relaxed` vs. `xchg_relaxed(..., 0)`), `reserved_asids` multi-rollover preservation, `tlb_flush_pending`, `system_supports_cnp()` reserved-`TTBR0` switch. |
| `torvalds/linux` (x86-64 PCID, Lazy TLB, `mmu_gather`, `membarrier`, RV64) | `5f22fb20497f4983094131f00a734362300d22d2`, `arch/x86/mm/tlb.c:78–290, 1109–1120, 1349–1427`; `arch/x86/include/asm/invpcid.h:20–48`; `mm/mmu_gather.c:270–329, 360–407`; `arch/riscv/mm/tlbflush.c:33–127`; `kernel/sched/membarrier.c:142–208, 330–345` | `source`: Mandatory IPI to lazy-TLB CPUs when `info->freed_tables` is set; `TLB_NR_DYN_ASIDS` + `CR3_NOFLUSH`; `INVPCID` types `0`–`3`; `tlb_flush_mmu_tlbonly()` -> `tlb_table_flush()` (`call_rcu`); RV64 `Svinval`/`SBI_RFENCE`; `ipi_sync_core()` for JIT core serialization. |
| `seL4/seL4` | `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, `include/arch/riscv/arch/machine.h:67–130`; `src/arch/riscv/kernel/vspace.c:442–546` | `source`: SMP `sfence()` (`fence_w_rw` + `sfence_local` + `sbi_remote_sfence_vma`), `ifence()`, `hwASIDFlush()`, and `deleteASID()`. |
| Arm DDI 0487 & Intel SDM Vol. 3A | Arm DDI 0487 (VMSA BBM / `FEAT_BBM` / TLB conflict aborts); Intel SDM Vol. 3A §4.10.2.3, §4.10.4.1–§4.10.4.2 | `normative`: BBM constraints, `CONSTRAINED UNPREDICTABLE` multi-hit semantics, `INVPCID` types `0`–`3` vs. `INVLPG` global/PWC behavior. |
| Simner et al. (ESOP 2022) & Syeda & Klein (JAR 2020) | DOI `10.1007/978-3-030-99336-8_6` (`arXiv:2203.00642`); DOI `10.1007/s10817-019-09539-7` | `documentation`: Relaxed Armv8-A virtual-memory concurrency semantics (`BBM`/`TLBI`/`DSB ISH`/`ISB`) and saturated cached-translation invariants. |
| `leanprover/lean4` (`v4.34.1`) Probe | `5045d0056413266e57c625dcd7c365b10e377c52`, `support/multicore_tlb_shootdown_probe.lean` (`2026-11-22`) | `execution`: `elan run leanprover/lean4:v4.34.1 lean -DElab.async=false -Ddebug.skipKernelTC=false support/multicore_tlb_shootdown_probe.lean` exited `0`; 9/10 theorems depend on **zero axioms** and 1 (`safeHartAckShootdown_preserves_PtSafeInv`) depends only on `[propext]` (zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`). |

## Revalidation

1. **Re-run the Standalone Lean 4 Kernel Probe (`< 2 s`):**
   ```bash
   elan run leanprover/lean4:v4.34.1 lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/multicore_tlb_shootdown_probe.lean
   ```
   Verify exit code `0`, zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`, and axiom closure inside `{propext}` across all 10 `#print axioms` lines.
2. **Diff Upstream Kernel & ISA Contract Seams:**
   - Diff `torvalds/linux` `arch/arm64/kernel/cpufeature.c` (`cpu_supports_bbml3`) and `arch/arm64/mm/mmu.c` (`split_kernel_leaf_mapping`) for new `FEAT_BBM` levels or CPU errata.
   - Diff `torvalds/linux` `arch/x86/mm/tlb.c` (`flush_tlb_multi` `freed_tables` guard) and `mm/mmu_gather.c` (`tlb_flush_mmu`) for changes to lazy-TLB or RCU table-free ordering.
   - Diff `riscv/riscv-isa-manual` `src/priv/supervisor.adoc` (`#norm:sfence_vma_local_only`, multi-entry superpage rules) and `src/priv/svinval.adoc`, plus `riscv-non-isa/riscv-sbi-doc` `src/ext-rfence.adoc` for any asynchronous RFENCE extensions.
