# RISC-V Sv39 ASID-Zero Aliasing, Hardware A/D Bits, and Speculative TLB-Fill Semantics

## Summary

Operating-system kernels and hypervisors verifying address-space isolation, capability-frame retyping, and trap handling on RISC-V `Sv39` must account for five normative Privileged Architecture behaviors that deterministic emulators routinely mask:

1. **`ASIDLEN = 0` Global/Non-Global Aliasing and Register-Number Sensitivity in `SFENCE.VMA`**: Under `[#norm:asidlen]`, `ASIDLEN ∈ [0, 16]` may legally be `0`, hardwiring `satp.ASID` to `0` and ignoring `rs2[15:0]` in `SFENCE.VMA`. Writing `satp` neither orders page-table stores nor flushes cached translations (`[#norm:satp_op_sfence_vma]`), so switching `satp.PPN` without `SFENCE.VMA` on `ASIDLEN = 0` aliases every non-global (`G=0`) TLB entry across address spaces. Crucially, `SFENCE.VMA` branches on **register specifier identity (`rs2 = x0` vs `rs2 ≠ x0`)**, not register value: `sfence.vma x0, a0` with `a0 = 0` flushes all `ASID = 0` non-global entries while **preserving `G=1` global kernel entries** (Linux `set_mm_noasid`), whereas `sfence.vma x0, x0` flushes both `G=0` and `G=1` entries (`seL4` `setVSpaceRoot`), and `sfence.vma x0, a0` (`a0 = 0`) leaves modified `G=1` subtrees stale because `G=1` propagates downward from non-leaf PTEs (`[#norm:pte_g_op]`).
2. **Walk-Start-Time `satp` Lifetime and Root-Frame Recycling Order**: `satp` is active in **both S-mode and U-mode** (`[[norm:satp_op_active]]`). Speculative page-table walks may begin at any instant while `satp` is active and **need not abort** when `satp` changes or deactivates unless a matching `SFENCE.VMA` executes (`supervisor.adoc:1114–1120, 1797–1808`). Executing `sfence.vma x0, asid` *before* switching `satp` away from a retired root page-table frame $F_{\text{root}}$ leaves an S-mode window in which a new speculative walk can start from $F_{\text{root}}$, survive `csrw satp`, and install stale translations or touch recycled memory. Software must switch `satp` away from $F_{\text{root}}$ *before* executing `sfence.vma x0, asid` (`supervisor.adoc:1363–1369`).
3. **`Svade` vs. `Svadu` Speculative `A=1` Updates and Retyped-Frame Corruption**: Under `Svade` (or `menvcfg.ADUE = 0`), `A=0` or store `D=0` never mutates memory; architectural walks page-fault while speculative walks terminate silently. Under `Svadu` (`menvcfg.ADUE = 1`) or legacy hardware updating, Step 9 updates PTEs via an 8-byte atomic compare-and-swap directly in memory (`supervisor.adoc:1745–1749, 1780–1781`). Speculative walks **must never set `D=1`**, **may set `A=1` (`| 0x40`)** even if the access never retires (`supervisor.adoc:1625–1630, 1804–1805`), cannot corrupt an already-zeroed frame (`0x0` has `V=0`, failing Step 9's compare-and-retry), **but can corrupt bit 6 (`0x40`) of a non-zero retyped kernel object** (e.g., a CNode/TCB word matching `V=1, R=1∨X=1, rsv=0, A=0`) if a stale non-leaf page-walk cache (PWC) entry still points to that frame after an under-scoped leaf-only `sfence.vma va, asid` (`rs1 ≠ x0`).
4. **Silent Speculative Walk Termination on Invalid, Reserved, `A=0`, and PMP-Denied PTEs**: Speculative walks hitting `V=0`, reserved `R=0 ∧ W=1` (`menvcfg.SSE = 0`), non-zero reserved bits (`pte[63:54]` without `Svnapot`/`Svpbmt`/`Svrsw60t59b`, or non-leaf `A/D/U ≠ 0`), `A=0` under `Svade`, store `D=0`, or PMA/PMP rejection **must terminate silently** without modifying `scause`/`stval`/`sepc` (`supervisor.adoc:1344–1349, 1803–1808`), though valid non-leaf steps read *earlier* in that walk may remain cached until `sfence.vma x0, ...`.
5. **U-Mode `Sv39` + `PMP`/Bus Access-Fault Interleaving and Pre-Trap `A/D` Commitment**: Implicit `Sv39` PTE reads and Step 9 `A/D` writes check Physical Memory Protection (`PMP`) at **effective privilege `S`** (`machine.adoc:3330–3332, 3619–3620`), whereas the translated explicit access checks `PMP` at **effective privilege `U`**. PMP/PMA failures during Step 2 or Step 9 raise **Access Faults (`scause ∈ {1, 5, 7}`)** rather than Page Faults (`{12, 13, 15}`). Because Step 9 PTE updates are **not atomic with the explicit access** (`supervisor.adoc:1642–1648`), a U-mode store whose final physical address fails U-mode PMP or bus-faults raises Store/AMO Access Fault (`scause = 7`) while leaving `A=1, D=1` architecturally committed in the page table, and misaligned multi-page stores may partially commit on page 0 before faulting on page 1 (`supervisor.adoc:1707–1713`, `machine.adoc:3567–3574`).

## Applicability

This report compares normative RISC-V specification rules against formal ISA models and production OS/microkernel implementations across the eight subjects pinned in `REPORT.json`:

- **Normative Baseline (`riscv/riscv-isa-manual`)**: Examined at development snapshot `c05f1725f25526dd8463bac6ca75cfcfbee17d05` (`src/priv/supervisor.adoc`, `src/priv/machine.adoc`, `src/priv/smepmp.adoc`), ratified release `20250508` (`584390d9d872835b1bc45ab9ea946b56db3ad485`), and tag `Priv-v1.12` (`98964261c931d51884f733664b22efe43de93033`). Line numbers cite `c05f1725...` unless noted.
- **Models & Implementations (`riscv/sail-riscv@ec5200bd...`, `seL4/seL4@08c7e5fd...`, `seL4/l4v@b0fe7693...`, `torvalds/linux@8dac6df9...`, `riscv-software-src/opensbi@61f1973b...`)**: Inspected in source for `ASIDLEN = 0` handling, `G=1` vs `G=0` invalidation, root-table teardown, `A/D` pre-setting, and fault delivery.

Scope covers single-regime `RV64` S/U-mode virtual memory under `Sv39` (`satp.MODE = 8`, 4 KiB/2 MiB/1 GiB pages) beneath M-mode firmware with PMP. Hypervisor two-level translation (`vsatp`/`hgatp`), `Svnapot`, `Svpbmt`, `Zicfiss`, and IOMMU DMA translation are out of scope except where their reserved bits or `menvcfg` gates affect `Sv39` walks. For general S-mode nondeterminism (`LR`/`SC`, `Sstc`, `fence.i`, per-level stale leaf synthesis), see `riscv-smode-kernel-sound-nondeterminism-and-spec-permitted-behaviors`; for cross-ISA shootdowns, see `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement`.

## Findings

### 1. `ASIDLEN = 0` WARL Semantics, Non-Global Aliasing, and `SFENCE.VMA` `G`-Bit Asymmetry

Basis: normative + source + execution + derived

#### 1.1 Normative `ASIDLEN` Discovery and Truncation

In RV64 `Sv39`, `satp` (`CSR 0x180`) packs `MODE` (`63:60`, `8` for `Sv39`), `ASID` (`59:44`, `ASIDMAX = 16`), and `PPN` (`43:0`) (`supervisor.adoc:995–1061`). Under `[#norm:asidlen]`, `[#norm:asid_lsb_first]`, `[[norm:sfence_vma_rs2_bits]]`, and `[#norm:satp_op_sfence_vma]` (`L1054–1061, 1122–1124, 1277–1283`):
- `ASIDLEN ∈ [0, 16]` is **UNSPECIFIED and may be zero**, discovered by writing all ones to `satp.ASID` and reading back; only `ASID[ASIDLEN-1:0]` is writable, and `SFENCE.VMA` with `rs2 ≠ x0` ignores `rs2[63:ASIDLEN]`.
- Writing `satp` implies neither ordering nor TLB invalidation. When `ASIDLEN < 16`, software ASIDs congruent modulo $2^{\text{ASIDLEN}}$ (all software ASIDs when `ASIDLEN = 0`, collapsing to `hw_asid = 0`) share one hardware tag, aliasing `G=0` translations across address spaces if `satp.PPN` changes without `SFENCE.VMA`. *(QEMU and Spike hide this by flushing on `satp` writes; `sail-riscv@ec5200bd...` `vmem.sail:297–298` does not flush on `satp` writes and catches leaf aliasing when `asidlen = 0`.)*

#### 1.2 Register-Specifier Identity (`rs2 = x0` vs. `rs2 ≠ x0` Holding `0`) and Non-Leaf `G=1` Propagation

`SFENCE.VMA rs1, rs2` decodes **register number `rs2 == 0` (`x0`) vs `rs2 != 0`**, not whether `rs2`'s value equals `0` (`supervisor.adoc:1232–1259`; `sail-riscv` `vmem_tlb.sail:142–145`):

| Form | `rs1` | `rs2` | `rs2` Value | Levels Flushed/Ordered | `G=0` Entries | `G=1` Global Entries |
| --- | --- | --- | --- | --- | --- | --- |
| `sfence.vma x0, x0` | `x0` | `x0` | `0` | **All levels** | All ASIDs flushed | **Flushed & ordered** (`L1232–1235`) |
| `sfence.vma x0, a0` | `x0` | `a0` (`≠x0`) | `0` | **All levels** (`hw_asid=0`) | `hw_asid=0` (**all `G=0`** if `ASIDLEN=0`) | **NOT ordered, NOT flushed** (`L1237–1243`) |
| `sfence.vma a1, x0` | `a1` (`≠x0`) | `x0` | `0` | **Leaf only** (`VA=a1`) | All ASIDs (`VA=a1`) | **Flushed & ordered** (`L1245–1250`) |
| `sfence.vma a1, a0` | `a1` (`≠x0`) | `a0` (`≠x0`) | `0` | **Leaf only** (`VA=a1, hw_asid=0`) | `hw_asid=0` (`VA=a1`) | **NOT ordered, NOT flushed** (`L1252–1259`) |

Two subtle hazards govern `G=1` under `ASIDLEN = 0`:
1. **Non-Leaf `G=1` Inheritance (`[#norm:pte_g_op]`, `supervisor.adoc:1576–1583`)**: Setting `G=1` on a non-leaf PTE makes **all mappings in subsequent levels global** (`sail_vmem.sail:208`). Any user mapping placed beneath a `G=1` non-leaf PTE survives `sfence.vma x0, a0` (`a0 = 0`) across context switches!
2. **Kernel `G=1` Modifications Require `rs2 = x0` (`supervisor.adoc:1376–1383`)**: Unmapping or remapping any kernel PTE with `G=1` on its traversal path requires `rs2 = x0`; `sfence.vma x0, a0` (`a0 = 0`) leaves `G=1` entries stale.

#### 1.3 Linux (`torvalds/linux`) vs. `seL4` (`seL4/seL4`) on `ASIDLEN = 0`

- **Linux (`torvalds/linux@8dac6df9...`, `arch/riscv/mm/context.c:200–275`, `include/asm/tlbflush.h:41–52`)**: `asids_init()` (`L227–245`) probes `CSR_SATP` with `SATP_ASID_MASK`, restores `old` `satp`, immediately executes `local_flush_tlb_all()` (`sfence.vma` `x0, x0`, `L244`) to purge speculative TLB pollution incurred during the probe, and disables `use_asid_allocator` whenever `num_asids <= 2 * num_possible_cpus()`. On `ASIDLEN = 0`, `set_mm_noasid` (`L200–205`) runs `csr_write(CSR_SATP, ...)` followed by `local_flush_tlb_all_asid(0)` (`rs2 ≠ x0` holding `0`), flushing all `G=0` user entries while retaining `G=1` kernel entries (`G=1_kept = True` in **Probe Part 1**).
- **`seL4` (`seL4/seL4@08c7e5fd...`, `vspace.c:75, 578–602, 1063–1074`, `machine.h:89–148, 259–273`, `boot.c:126–143`)**: `seL4` never probes `ASIDLEN`; it writes 16-bit software `asid_t` values into `satp` inside `setVSpaceRoot` (`machine.h:259–273`) and unconditionally executes bare `sfence.vma` (`x0, x0`) after every `write_satp`. Single-core `seL4` thus remains safe on `ASIDLEN = 0` or `ASIDLEN = 9` hardware, at the cost of evicting `pte_next`'s `G=1` kernel window mappings on every context switch (`G=1_kept = False`). Removing `sfence.vma` from `setVSpaceRoot` without adding `ASIDLEN` probing and rollover would immediately break address-space isolation on `ASIDLEN < 16` cores.

---

### 2. Recycled Root Page-Table Frames and Walk-Start-Time Fencing

Basis: normative + source + execution + derived

Under `[[norm:satp_op_active]]` and speculative walk rules (`supervisor.adoc:1106–1120, 1797–1808`), `satp` is active in **both S-mode and U-mode**, and walks initiated while `satp` was active **need not terminate when `satp` changes** unless invalidated by a subsequent matching `SFENCE.VMA`.

Consequently, when retiring or recycling an ASID `a` (including `a = 0` on `ASIDLEN = 0`) or root frame $F_{\text{root}}$ currently loaded in `satp`:
- **Wrong Order (`sfence.vma x0, a` $\to$ `csrw satp, new_satp`, no post-`satp` fence)**: Because `satp` remains active in S-mode between `sfence.vma` and `csrw satp`, hardware can legally start a speculative walk from $F_{\text{root}}$ *after* the fence; `csrw satp` does not abort it, allowing stale entries to populate the TLB (`fence_before_satp_pa = 0x10000` stale in **Probe Part 2**).
- **Normative Order (`supervisor.adoc:1363–1369`)**: Software must **first** switch `satp` away from $F_{\text{root}}$ (or already hold a distinct `ASID ≠ a` in `satp` that will never reload $F_{\text{root}}$), and **then** execute `sfence.vma x0, a` (plus remote IPI/SBI shootdowns on SMP) prior to zeroing or retyping $F_{\text{root}}$ (`satp_before_fence_pa = 0x20000` fresh in **Probe Part 2**). *(In `seL4` `deleteASID`, `vspace.c:500–502`, line 500's pre-switch `hwASIDFlush(asid)` is saved locally only because line 502's `setVMRoot` issues a second `sfence()` after `write_satp`.)*

---

### 3. `Svade` vs. `Svadu` Hardware `A/D` Updates, Pre-Retype Memory, and Silent Walk Termination

Basis: normative + source + execution + derived

#### 3.1 Extension Control and Speculative vs. Architectural Walk Matrix

While `Priv-v1.12` (`98964261...`) left hardware `A/D` updating vs faulting as an unnamed implementation choice, `20250508` (`584390d9...`) and `c05f1725...` (`supervisor.adoc:1601–1654`, `machine.adoc:2194–2216`) standardize `Svade` (fault on `A=0` or store `D=0`) and `Svadu` (`menvcfg.ADUE = 1` enables atomic hardware updates; `ADUE = 0` behaves as `Svade`; toggling `ADUE` requires `sfence.vma x0, x0`). `OpenSBI` (`sbi_hart.c:131–169`) defaults `ADUE = 0` unless only `Svadu` is in the ISA string; `sail-riscv` (`vmem_pte.sail:304–310`) updates PTEs when `Svadu & ADUE == 1` or when neither `Svade` nor `Svadu` is enabled.

Across `supervisor.adoc:1338–1349, 1622–1651, 1697–1699, 1724–1808, 1915–1927`, PTE walk outcomes partition as follows:

| PTE Condition | Architectural Walk | Speculative Walk (`satp` Active) | Memory PTE Write? | Translation Cache Behavior |
| --- | --- | --- | --- | --- |
| `V = 0` (`0x0` zeroed word) | Page Fault (`12`/`13`/`15`) | **Silent termination** | Never | `V=0` caching permitted (`L1338–1341`) |
| `V=1`, `R=0 ∧ W=1` (`SSE=0`), or `pte[63:54] ≠ 0`, or non-leaf `A/D/U ≠ 0` | Page Fault (`12`/`13`/`15`) | **Silent termination** | Never | No valid translation created |
| Valid leaf, `A = 0`, `Svade` (`ADUE = 0`) | Page Fault (`12`/`13`/`15`) | **Silent termination** | Never | `A=0` step-2 read may be cached |
| Valid leaf, `A = 0`, `Svadu` (`ADUE = 1`) | Atomic CAS sets **`A := 1`** | Atomic CAS **may set `A := 1`** (`L1625–1627`) | **Yes (`\|= 0x40`)**, 8 B | Cached with `A = 1` |
| Writable leaf, `D = 0`, store walk (`ADUE = 1`) | Atomic CAS sets **`A := 1, D := 1`** | **Must NOT set `D := 1`** (`L1804–1805`); aborts | **Never sets `D=1` speculatively** | Read-only (`D=0`) entry may be cached |
| Step 2 read or Step 9 write fails PMA / S-mode PMP | **Access Fault (`1`/`5`/`7`)** | **Silent termination** (`machine.adoc:3288`) | Never | Earlier valid non-leaf steps may stay cached |

#### 3.2 Zeroed Pre-Retype Frames vs. Retyped Kernel Object Corruption (`P2.3` in Evidence)

When a microkernel (`seL4` `untyped.c:253–305`) zeros a frame via `clearMemory` and retypes it into a `CNode` or `TCB` under `Svadu` (`ADUE = 1`):
1. **Zeroed Words (`0x0`) Are Safe on Spec-Compliant Hardware**: Step 9 (`supervisor.adoc:1745–1749, 1780–1781`) forbids using the TLB in Step 9 and performs an direct-memory 8-byte compare-and-swap. If `clearMemory` already wrote `0x0` (`V=0`), any in-flight walk that read `V=1, A=0` earlier fails the compare, retries Step 2, sees `V=0`, and aborts silently (`zero_preserved = True`). *(Contrast `sail-riscv@ec5200bd...` `translate_TLB_hit`, `vmem.sail:386–405`, which writes back the cached PTE without comparing memory, non-compliantly clobbering `0x0`.)*
2. **Non-Zero Retyped Objects Corrupt Under Stale Non-Leaf PWCs**: If software unmaps a level-0 page table $F_{\text{pt}}$ at level 1 but executes leaf-only `sfence.vma va, asid` (`rs1 ≠ x0`) instead of `rs1 = x0`, the non-leaf PWC retains `L1 -> F_pt`. Once `invokeUntyped_Retype` writes a capability/TCB word `w` into $F_{\text{pt}}$ whose bit pattern satisfies `bits[63:54] = 0, V = 1, (R = 1 ∨ X = 1), A = 0` (e.g., `0x0000_0000_0000_2813`), a purely speculative walk under `ADUE = 1` follows the stale PWC entry, matches `w` in Step 9's CAS, and **sets bit 6 (`w |= 0x40`) inside the live kernel object** (`retyped_corrupted = True` in **Probe Part 3**)! Unmapping page tables with `rs1 = x0` (`vspace.c:545` `sfence()`) and pre-setting `A = 1` on all valid leaves (`makeUserPTE`, `vspace.c:666–667`) eliminates this hazard completely.

---

### 4. U-Mode `Sv39` + `PMP`/Bus Access-Fault Interleaving

Basis: normative + source + execution + derived

Under `machine.adoc:1899–1936, 3327–3337, 3567–3638` (`[[norm:exc_priority]]`, `[[pmp-vmem]]`) and `sail_vmem.sail:61, 71`:
1. **S-Mode PTW Privilege vs. U-Mode Final PA Privilege**: Implicit Step 2 PTE reads and Step 9 `A/D` writes check PMP at **privilege `S`**, whereas the translated U-mode access checks PMP at **privilege `U`**. Neither standard PMP (`machine.adoc:3562`) nor `Smepmp` (`smepmp.adoc:46–67`) separates `S` from `U` (`S/U Mode` share one column), so supervisor memory is isolated from U-mode by `pte.U = 0` while PMP isolates M-mode firmware from both. Because PMP checks may be cached in TLBs (`machine.adoc:3622–3633`), M-mode PMP CSR updates require `sfence.vma x0, x0`.
2. **PTW PMP Failures Raise Access Faults (`1/5/7`), Not Page Faults (`12/13/15`)**: Step 2 checks PMA/PMP before Step 3 checks `pte.V` (`supervisor.adoc:1724–1726`); a U-mode load walking into PMP-protected M-mode memory raises `scause = 5` (Load Access Fault), while speculative walks abort silently (`P2.4` Case U1).
3. **Committed `A=1, D=1` Before U-Mode Target Access Fault (`P2.4` Case U2)**: Because Step 9 PTE updates are **not atomic with the explicit access** (`supervisor.adoc:1642–1648`), a U-mode store through a valid `A=0, D=0` leaf (`ADUE = 1`) whose translated physical address fails U-mode PMP or bus-faults raises **Store/AMO Access Fault (`scause = 7`)** while leaving **`A=1, D=1` committed in the PTE** (`pte_AD_committed_before_trap = True`; cf. `sail_vmem_pte.sail:331–340`). Likewise, split misaligned cross-page stores may write bytes on page 0 before faulting on page 1 (`supervisor.adoc:1707–1713`), and `seL4` `handleVMFault` (`vspace.c:423–436`) collapses `12/13/15` and `1/5/7` into identical `seL4_Fault_VMFault` IPC codes.

## Boundaries

- **Two-Level Hypervisor Translation (`vsatp`/`hgatp`, `HFENCE.VVMA`/`GVMA`) (`not examined`)**: Guest two-level `Sv39x4` walks, speculative G-level `D=1` updates from implicit VS-level reads (`supervisor.adoc:1631–1633`), and VMID-zero aliasing were not examined.
- **Commercial Silicon Negative (`V=0`) PWC/TLB Caching Prevalence (`unknown`)**: While `supervisor.adoc:1338–1341` permits caching `V = 0` PTEs, which commercial RV64 microarchitectures cache `V = 0` entries could not be resolved from public specifications alone.
- **Assuming `satp` Writes Flush TLBs or Abort Speculative Walks (`known not to apply`)**: Expecting `csrw satp` to flush `G = 0` entries on `ASIDLEN = 0` or expecting `sfence.vma x0, asid` *before* `csrw satp` to prevent speculative walks in the intervening S-mode window is known not to apply (`supervisor.adoc:1114–1124, 1363–1369, 1797–1808`).
- **Separating S-Mode from U-Mode Physical Memory via Standard PMP or `Smepmp` Alone (`unsupported`)**: Both standard PMP and `Smepmp` (`smepmp.adoc:46–67`) enforce a shared `S/U Mode` permission column; S-vs-U isolation requires `Sv39` `pte.U = 0` (or M-mode PMP reprogramming on traps).

## Evidence

### Primary Git Repository Sources (Observed `2026-11-20`)

- `riscv/riscv-isa-manual` @ `c05f1725f25526dd8463bac6ca75cfcfbee17d05` (cross-checked against `20250508` @ `584390d9d872835b1bc45ab9ea946b56db3ad485` and `Priv-v1.12` @ `98964261c931d51884f733664b22efe43de93033`): `src/priv/supervisor.adoc:1049–1061, 1106–1129, 1232–1284, 1338–1390, 1576–1952`; `src/priv/machine.adoc:1899–1936, 2194–2216, 3288–3340, 3567–3638`; `src/priv/smepmp.adoc:46–67`.
- `riscv/sail-riscv` @ `ec5200bdfe0c10afa6dbb1f7b0980db2d236236e`: `model/sys/vmem.sail:56–72, 95–120, 137–261, 295–299, 370–456`; `model/sys/vmem_pte.sail:91–119, 304–372`; `model/sys/vmem_tlb.sail:117–164`; `model/sys/mem.sail:75–110, 192–252`.
- `seL4/seL4` @ `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`: `src/arch/riscv/kernel/vspace.c:63–82, 182–222, 417–451, 494–602, 656–676, 1063–1107`; `include/arch/riscv/arch/machine.h:89–148, 259–273`; `src/arch/riscv/kernel/boot.c:126–143`; `src/object/untyped.c:234–306`.
- `seL4/l4v` @ `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`: `spec/machine/RISCV64/MachineOps.thy:141–164, 197–223`.
- `torvalds/linux` @ `8dac6df92a2e66e2098bbc69061964cfe7e8375b`: `arch/riscv/mm/context.c:200–275`; `arch/riscv/include/asm/tlbflush.h:41–67`; `arch/riscv/mm/tlbflush.c:20–64`.
- `riscv-software-src/opensbi` @ `61f1973bd50338b36c52dc34006f76d464ca4f34`: `lib/sbi/sbi_hart.c:131–169`.

### Peer-Reviewed Literature

- Lustig, Sethi, Martonosi, Bhattacharjee, *"COATCheck: Verifying Memory Ordering at the Hardware-OS Interface"*, ASPLOS 2016, DOI `10.1145/2872362.2872399`.
- Simner, Armstrong, Pichon-Pharabod, Pulte, Grisenthwaite, Sewell, *"Relaxed Virtual Memory in Armv8-A"*, ESOP 2022 (LNCS 13240), arXiv DOI `10.48550/arXiv.2203.00642`.
- Syeda & Klein, *"Reasoning about Translation Lookaside Buffers"*, LPAR-21 (2017), DOI `10.29007/c2f1`.
- Klein et al., *"Comprehensive Formal Verification of an OS Microkernel"*, ACM TOCS 32(1), 2014, DOI `10.1145/2560537`.
- Armstrong et al., *"ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS"*, PACMPL (POPL 2019), DOI `10.1145/3290384`.

### Executable Micro-Probe (`Basis: execution`, Observed `2026-11-20`)

Save as `/tmp/probe_sv39_asid0_ad_pmp.py` and run `python3 /tmp/probe_sv39_asid0_ad_pmp.py`:

```python
#!/usr/bin/env python3
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

V_BIT, R_BIT, W_BIT, X_BIT, U_BIT, G_BIT, A_BIT, D_BIT = (1 << i for i in range(8))
RSV_MASK = ((1 << 10) - 1) << 54

def make_pte(ppn: int, flags: int, rsv_hi: int = 0) -> int:
    return ((rsv_hi & 0x3FF) << 54) | ((ppn & ((1 << 44) - 1)) << 10) | (flags & 0xFF)

@dataclass(frozen=True)
class TlbEntry:
    hw_asid: int; global_map: bool; level: int; vpn_prefix: int; pte: int; pte_pa: int

class Sv39Hart:
    def __init__(self, asidlen: int, adue: bool, pmp_s_rw: set, pmp_u_rw: set):
        self.asidlen, self.adue, self.pmp_s_rw, self.pmp_u_rw = asidlen, adue, pmp_s_rw, pmp_u_rw
        self.satp_mode, self.satp_asid, self.satp_ppn = 8, 0, 0
        self.mem: Dict[int, int] = {}
        self.tlb: List[TlbEntry] = []
        self.inflight_walks: List[Tuple[int, int]] = []

    def write_satp(self, mode: int, sw_asid: int, ppn: int) -> None:
        if mode in (0, 8):
            mask = (1 << self.asidlen) - 1 if self.asidlen > 0 else 0
            self.satp_mode, self.satp_asid, self.satp_ppn = mode, (sw_asid & mask), ppn

    def begin_speculative_walk(self) -> None:
        if self.satp_mode == 8:
            self.inflight_walks.append((self.satp_asid, self.satp_ppn))

    def sfence_vma(self, rs1_is_x0: bool, rs1_va: int, rs2_is_x0: bool, rs2_val: int) -> None:
        mask = (1 << self.asidlen) - 1 if self.asidlen > 0 else 0
        tgt = rs2_val & mask
        vpn0 = (rs1_va >> 12) & ((1 << 27) - 1)
        self.tlb = [
            e for e in self.tlb
            if not ((True if rs2_is_x0 else (not e.global_map and e.hw_asid == tgt))
                    and (True if rs1_is_x0 else (e.level == 0 and e.vpn_prefix == vpn0)))
        ]
        if rs1_is_x0:
            self.inflight_walks = [(a, r) for (a, r) in self.inflight_walks if not (rs2_is_x0 or a == tgt)]

    def walk_and_access(self, va: int, access: str, priv: str, speculative: bool,
                        use_inflight: Optional[Tuple[int, int]] = None) -> Tuple[str, Optional[int]]:
        pf = {"fetch": 12, "load": 13, "store": 15}[access]
        af = {"fetch": 1,  "load": 5,  "store": 7}[access]
        if not (((va >> 38) == 0) or ((va >> 38) == ((1 << 26) - 1))):
            return ("silent_abort", None) if speculative else ("page_fault", pf)
        walk_asid, a_ppn = use_inflight if use_inflight is not None else (self.satp_asid, self.satp_ppn)
        vpns = [(va >> 12) & 0x1FF, (va >> 21) & 0x1FF, (va >> 30) & 0x1FF]
        g_acc = False
        for level in (2, 1, 0):
            prefix = (va >> (12 + 9 * level)) & ((1 << (27 - 9 * level)) - 1)
            cached = next((e for e in self.tlb if e.level == level and e.vpn_prefix == prefix
                           and (e.global_map or e.hw_asid == walk_asid)), None)
            if cached is not None:
                pte, pte_pa, g_acc = cached.pte, cached.pte_pa, (g_acc or cached.global_map)
            else:
                pte_pa = (a_ppn << 12) + vpns[level] * 8
                if (pte_pa >> 12) not in self.pmp_s_rw:
                    return ("silent_abort", None) if speculative else ("access_fault", af)
                pte = self.mem.get(pte_pa, 0)
            flags = pte & 0xFF
            v, r, w, x, u, g, a_b, d_b = (bool(flags & (1 << b)) for b in range(8))
            g_acc = g_acc or g
            non_leaf = (not r and not w and not x)
            if (not v) or (not r and w) or bool(pte & RSV_MASK) or (non_leaf and (a_b or d_b or u)):
                return ("silent_abort", None) if speculative else ("page_fault", pf)
            if non_leaf:
                if level == 0:
                    return ("silent_abort", None) if speculative else ("page_fault", pf)
                if cached is None:
                    self.tlb.append(TlbEntry(walk_asid, g_acc, level, prefix, pte, pte_pa))
                a_ppn = (pte >> 10) & ((1 << 44) - 1)
                continue
            leaf_ppn = (pte >> 10) & ((1 << 44) - 1)
            if (level > 0 and (leaf_ppn & ((1 << (9 * level)) - 1)) != 0) or (priv == "U" and not u) or (priv == "S" and u) or not {"fetch": x, "load": r, "store": w}[access]:
                return ("silent_abort", None) if speculative else ("page_fault", pf)
            need_a, need_d = (not a_b), (access == "store" and not d_b)
            if need_a or need_d:
                if not self.adue:
                    return ("silent_abort", None) if speculative else ("page_fault", pf)
                if speculative and need_d:
                    return ("silent_abort", None)
                if (pte_pa >> 12) not in self.pmp_s_rw:
                    return ("silent_abort", None) if speculative else ("access_fault", af)
                if self.mem.get(pte_pa, 0) != pte:
                    return self.walk_and_access(va, access, priv, speculative, use_inflight)
                pte = (pte & ~0xFF) | flags | A_BIT | (D_BIT if (need_d and not speculative) else 0)
                self.mem[pte_pa] = pte
            if cached is None:
                self.tlb.append(TlbEntry(walk_asid, g_acc, level, prefix, pte, pte_pa))
            pa = (leaf_ppn << 12) | (va & 0xFFF)
            if not speculative and (pa >> 12) not in (self.pmp_u_rw if priv == "U" else self.pmp_s_rw):
                return ("access_fault", af)
            return ("ok", pa)
        raise AssertionError("unreachable")

h = Sv39Hart(asidlen=0, adue=False, pmp_s_rw={1, 2, 0x10, 0x20, 0x99}, pmp_u_rw={0x10, 0x20})
VA_USER, VA_KRN = 0x0000_0000_0000_1000, 0xFFFF_FFC0_0000_2000
for r_ppn, u_ppn in ((1, 0x10), (2, 0x20)):
    h.mem[(r_ppn << 12) + ((VA_USER >> 30) & 0x1FF) * 8] = make_pte(r_ppn, V_BIT)
    h.mem[(r_ppn << 12) + ((VA_USER >> 21) & 0x1FF) * 8] = make_pte(r_ppn, V_BIT)
    h.mem[(r_ppn << 12) + ((VA_USER >> 12) & 0x1FF) * 8] = make_pte(u_ppn, V_BIT | R_BIT | U_BIT | A_BIT)
    h.mem[(r_ppn << 12) + ((VA_KRN >> 30) & 0x1FF) * 8] = make_pte(r_ppn, V_BIT | G_BIT)
    h.mem[(r_ppn << 12) + ((VA_KRN >> 21) & 0x1FF) * 8] = make_pte(r_ppn, V_BIT)
    h.mem[(r_ppn << 12) + ((VA_KRN >> 12) & 0x1FF) * 8] = make_pte(0x99, V_BIT | R_BIT | A_BIT)

h.write_satp(8, 1, 1); h.walk_and_access(VA_USER, "load", "U", False); h.walk_and_access(VA_KRN, "load", "S", False)
h.write_satp(8, 2, 2); _, pa_unf = h.walk_and_access(VA_USER, "load", "U", False)
h.sfence_vma(True, 0, False, 0); g1_reg0 = any(e.global_map for e in h.tlb); _, pa_f0 = h.walk_and_access(VA_USER, "load", "U", False)
h.sfence_vma(True, 0, True, 0); g1_x0 = any(e.global_map for e in h.tlb)
print(f"[P2.1] ASIDLEN=0: satp.asid={h.satp_asid}, unfenced_pa=0x{pa_unf:x} (stale 0x10000 != 0x20000) | "
      f"sfence(x0,a0=0): pa=0x{pa_f0:x}, G=1_kept={g1_reg0} | sfence(x0,x0): G=1_kept={g1_x0}")

h2 = Sv39Hart(16, False, {1, 2, 0x10, 0x20}, {0x10, 0x20}); h2.mem.update(h.mem)
h2.write_satp(8, 5, 1); h2.sfence_vma(True, 0, False, 5); h2.begin_speculative_walk(); h2.write_satp(8, 5, 2)
for iw in list(h2.inflight_walks): h2.walk_and_access(VA_USER, "load", "U", True, iw)
_, pa_wrong = h2.walk_and_access(VA_USER, "load", "U", False)
h2.tlb.clear(); h2.inflight_walks.clear(); h2.write_satp(8, 5, 1); h2.begin_speculative_walk(); h2.write_satp(8, 5, 2); h2.sfence_vma(True, 0, False, 5)
_, pa_right = h2.walk_and_access(VA_USER, "load", "U", False)
print(f"[P2.2] Recycled ASID=5 root switch: fence_before_satp_pa=0x{pa_wrong:x} (stale!) | satp_before_fence_pa=0x{pa_right:x} (fresh)")

def probe_spec_ad(adue: bool):
    ht = Sv39Hart(16, adue, {1, 3, 0x10}, {0x10}); ht.write_satp(8, 1, 1)
    ht.mem[(1 << 12) + 0] = make_pte(1, V_BIT); ht.mem[(1 << 12) + 8] = make_pte(3, V_BIT)
    VA_T = 1 << 21
    ht.mem[(3 << 12) + 0] = make_pte(0x10, V_BIT | R_BIT | U_BIT)
    r_a0 = ht.walk_and_access(VA_T, "load", "U", True)[0]; a_set = bool(ht.mem[(3 << 12) + 0] & A_BIT)
    ht.mem[(3 << 12) + 8] = make_pte(0x10, V_BIT | W_BIT | U_BIT | A_BIT)
    r_rsv_s = ht.walk_and_access(VA_T + 0x1000, "load", "U", True)[0]; r_rsv_a = ht.walk_and_access(VA_T + 0x1000, "load", "U", False)
    ht.mem[(3 << 12) + 16] = make_pte(0x10, V_BIT | R_BIT | W_BIT | U_BIT | A_BIT)
    r_d0_s = ht.walk_and_access(VA_T + 0x2000, "store", "U", True)[0]; d_set = bool(ht.mem[(3 << 12) + 16] & D_BIT)
    ht.mem[(1 << 12) + 8] = 0; ht.sfence_vma(False, VA_T, False, 1)
    ht.mem[(3 << 12) + 0] = 0; ht.walk_and_access(VA_T, "load", "U", True); z_ok = (ht.mem[(3 << 12) + 0] == 0)
    cap_w = 0x0000_0000_0000_2813; ht.mem[(3 << 12) + 0] = cap_w; ht.walk_and_access(VA_T, "load", "U", True)
    return (r_a0, a_set, r_d0_s, d_set, r_rsv_s, r_rsv_a, z_ok, ht.mem[(3 << 12) + 0] != cap_w)

print("[P2.3] Svade (ADUE=0):", probe_spec_ad(False))
print("[P2.3] Svadu (ADUE=1):", probe_spec_ad(True))

h4 = Sv39Hart(16, True, {1, 0x30}, set()); h4.write_satp(8, 1, 1); VA_P = 0x4000
h4.mem[(1 << 12) + 0] = make_pte(0x99, V_BIT)
u1_s, u1_a = h4.walk_and_access(0, "load", "U", True), h4.walk_and_access(0, "load", "U", False)
h4.mem[(1 << 12) + 0] = make_pte(1, V_BIT); h4.sfence_vma(True, 0, True, 0)
pte_u2 = (1 << 12) + ((VA_P >> 12) & 0x1FF) * 8; h4.mem[pte_u2] = make_pte(0x30, V_BIT | R_BIT | W_BIT | U_BIT)
u2_a = h4.walk_and_access(VA_P, "store", "U", False); ad_ok = bool(h4.mem[pte_u2] & A_BIT) and bool(h4.mem[pte_u2] & D_BIT)
print(f"[P2.4] PTW-PMP fail: spec={u1_s}, arch={u1_a} (scause=5, not 13!) | Final-PA U-PMP store fail: arch={u2_a} (scause=7), pte_AD_committed_before_trap={ad_ok}")
```

Observed output (`python3 /tmp/probe_sv39_asid0_ad_pmp.py`, exit code `0`):

```text
[P2.1] ASIDLEN=0: satp.asid=0, unfenced_pa=0x10000 (stale 0x10000 != 0x20000) | sfence(x0,a0=0): pa=0x20000, G=1_kept=True | sfence(x0,x0): G=1_kept=False
[P2.2] Recycled ASID=5 root switch: fence_before_satp_pa=0x10000 (stale!) | satp_before_fence_pa=0x20000 (fresh)
[P2.3] Svade (ADUE=0): ('silent_abort', False, 'silent_abort', False, 'silent_abort', ('page_fault', 13), True, False)
[P2.3] Svadu (ADUE=1): ('ok', True, 'silent_abort', False, 'silent_abort', ('page_fault', 13), True, True)
[P2.4] PTW-PMP fail: spec=('silent_abort', None), arch=('access_fault', 5) (scause=5, not 13!) | Final-PA U-PMP store fail: arch=('access_fault', 7) (scause=7), pte_AD_committed_before_trap=True
```

## Revalidation

1. **Rerun the `Sv39` Finite-State Probe (< 1 s)**: Run `python3 /tmp/probe_sv39_asid0_ad_pmp.py`; confirm exit code `0` and identical `[P2.1]`–`[P2.4]` outputs.
2. **Diff RISC-V Privileged Spec & `sail-riscv`**: Diff `riscv/riscv-isa-manual` `src/priv/supervisor.adoc` and `src/priv/machine.adoc` (`c05f1725...`) for changes to `[#norm:asidlen]`, Step 9, or `[[pmp-vmem]]`; diff `riscv/sail-riscv` `model/sys/vmem.sail` (`ec5200bd...`, `translate_TLB_hit`) for Step 9 memory compare-and-retry support.
3. **Audit Kernel VSpace & Retype Paths**: Verify (a) boot-time `ASIDLEN` discovery or unconditional post-`satp` `sfence.vma x0, ...`, (b) zero user mappings beneath `G=1` non-leaf PTEs and `rs2 = x0` on `G=1` kernel unmaps, (c) `csrw satp` *before* `sfence.vma x0, asid` on teardown, (d) `rs1 = x0` before page-table frame retyping, and (e) `A=1` and (`D=1` iff `W=1`) pre-set on valid leaves unless `Svade` (`ADUE = 0`) is locked.
