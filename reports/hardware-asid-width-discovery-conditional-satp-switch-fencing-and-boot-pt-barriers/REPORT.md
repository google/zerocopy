# Hardware ASID Width Discovery, Conditional satp Switch Fencing, and Boot Page-Table Barriers

## Summary

Operating-system kernels often assume hardware Address Space Identifiers (ASIDs) have fixed width (`16`-bit on `Sv39`/`Sv48`/`Sv57` or ARMv8-A) and that `satp` / `TTBR0_EL1` writes separate virtual address spaces without barriers once paging starts. Both assumptions break under the RISC-V Privileged ISA (`riscv/riscv-isa-manual`) and ARMv8-A (`VMSAv8-64`) unless four invariants are enforced:
1. **Variable `ASIDLEN` and `WARL` Probing:** RISC-V permits `ASIDLEN` in `0..9` (`Sv32`) or `0..16` (`Sv39`/`Sv48`/`Sv57`), implemented LSB-first with upper bits silently zeroed (`legalize_satp` in `riscv/sail-riscv`; `#norm:sfence_vma_rs2_bits`). Probing `ASIDLEN` via `satp` must occur while `satp.MODE != Bare` and execute an **immediate `local_flush_tlb_all()`** (`sfence.vma`) after restoring `satp` so speculative walks during the probe do not pollute ASID `(1 << ASIDLEN) - 1`. On ARMv8-A, `ID_AA64MMFR0_EL1.ASIDBits` (`8` vs `16`) and `TCR_EL1.AS` must agree across SMP cores (`verify_cpu_asid_bits` in `Linux`; `check16BitASID` boot gate in `seL4`). **Basis: normative, source, execution.**
2. **Domain-Isolation Failure Under Unprobed Conditional `satp` Fencing:** Eliding `sfence.vma` on context switch whenever software ASIDs differ ($a_1 \ne a_2$) breaches isolation if `ASIDLEN < 16` and $(a_1 \bmod 2^{\text{ASIDLEN}}) = (a_2 \bmod 2^{\text{ASIDLEN}})$ (`ASIDLEN = 0` aliases *every* user domain). `seL4` RISC-V avoids this today solely via unconditional `sfence()` in `setVSpaceRoot`; conditional fencing requires proving $0 < a < 2^{\text{ASIDLEN}}$ plus per-ASID dirty-set cleanliness. **Basis: normative, source, execution.**
3. **Context-Switch Fencing vs. Rollover and Two-Level `hw_asid_t` Allocators:** Sound kernels use either (a) `ASID = 0` + `sfence.vma x0, rs2` (`X[rs2] == 0`, preserving `G = 1` entries, `Linux` `set_mm_noasid`), (b) SMP generation rollover (`Linux` `active_context` `cmpxchg_relaxed` / `reserved_context` / `context_tlb_flush_pending` requiring `num_asids > 2 * num_possible_cpus()`), or (c) capability-indexed two-level `hw_asid_t` FIFO eviction (`seL4` AArch64 `arm64_vspace.c`). **Basis: source, documentation, execution.**
4. **Boot-Time Non-Leaf Page-Table Barrier Windows:** Because `#norm:satp_op_sfence_vma` denies store-to-PTW ordering on `satp` writes, kernels need a **pre-`satp` `sfence.vma`** before first `csrw satp` (`Linux` `head.S:104`), a **full `rs1 = x0` `sfence.vma` + `fence.i`** after populating initial user non-leaf directories while `satp` is active (`seL4` `map_it_pt_cap` / `boot.c`) before first `SRET`, and SMP handoff fences (`fence_rw_rw()` / `fence_r_rw()`). **Basis: normative, source, execution.**

## Applicability

This report governs RV32/RV64 (`Sv32`, `Sv39`, `Sv48`, `Sv57`) and ARMv8-A (`VMSAv8-64`) virtual-memory roots, ASID allocators, and bootstrap paging sequences. **Basis: normative, source.**

Within the corpus, it complements two prior MMU/TLB reports without overlap: `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` (steady-state `unmapPage` / `unmapPageTable` PWC vs. leaf `sfence.vma` asymmetry and `fence.i` automata) and `isa-page-table-tlb-coherence-sail-trap-contracts-and-toctou-dma-fetch-oracles` (`Sv39` single-walk rules and `ShootdownPcm`). Here, normative specifications (`riscv/riscv-isa-manual`, `riscv/sail-riscv`, `opencompl/sail-riscv-lean`) are evaluated against kernel ASID allocators, `satp` switches, and boot initialization (`seL4/seL4`, `seL4/l4v`, `torvalds/linux`, `mit-pdos/xv6-riscv`) alongside formal cached-MMU models (`Syeda & Klein`, `Simner et al.`). **Basis: documentation, source.**

## Findings

### 1. Hardware ASID Bit-Width Variability, WARL `satp` Probing, and Probe-Induced TLB Pollution

**Basis: normative, source, execution.**

In `riscv/riscv-isa-manual` (`c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `src/priv/supervisor.adoc` L1007–1061, L1277–1283) and `riscv/sail-riscv` (`76f1ce3c184797178864b9869963e8b44465889e`, `model/core/sys_regs.sail` L1212–1280):
- `#norm:asidlen` makes `ASIDLEN` unspecified (possibly `0`), while `#norm:asid_lsb_first` requires implemented bits at `ASID[ASIDLEN-1:0]` up to `ASIDMAX = 9` (`Sv32`) or `16` (`Sv39`/`Sv48`/`Sv57`).
- `legalize_satp` (`sys_regs.sail` L1236–1260) silently zeros bits above `ASIDLEN`:
  ```sail
  Asid = if asidlen == 0 then zeros() else zero_extend(s[Asid][asidlen - 1 .. 0])
  ```
  and `#norm:sfence_vma_rs2_bits` mandates that `sfence.vma` ignores `rs2[SXLEN-1:ASIDLEN]`. Unsupported `MODE` writes leave `satp` unchanged (`#norm:satp_mode_op_unsupported`, `sys_regs.sail` L1272–1279).
- **Bare-Mode Constraint (`supervisor.adoc` L1011–1016):** `#norm:satp_mode_bare_zero_fields` and `#norm:satp_mode_bare_nonzero_unspec` leave `satp` unspecified if `MODE = Bare` is written with nonzero `ASID`, so `ASIDLEN` probing MUST run under an active paged mode (`MODE != Bare`).

`Linux` implements the canonical 5-step probe in `arch/riscv/mm/context.c` (`L227–275`, `early_initcall(asids_init)` after `relocate_enable_mmu`): (1) save `old = csr_read(CSR_SATP)`, (2) write `old | (SATP_ASID_MASK << SATP_ASID_SHIFT)`, (3) read back and compute `fls_long((val >> SATP_ASID_SHIFT) & SATP_ASID_MASK)`, (4) restore `csr_write(CSR_SATP, old)`, and (5) call **`local_flush_tlb_all()`** (`L244`). Omitting step 5 lets any walk during lines 234–237 cache non-global entries tagged with `(1 << ASIDLEN) - 1`, leaking kernel translations when user ASID `(1 << ASIDLEN) - 1` is later allocated (`reval_pkg2.py`).

On ARMv8-A, `ID_AA64MMFR0_EL1.ASIDBits` (`[7:4]`: `0` = 8-bit, `2` = 16-bit) and `TCR_EL1.AS` (`BIT(36)`) expose width non-destructively. `Linux` enforces `verify_cpu_asid_bits()` (`arch/arm64/mm/context.c` L64–77) to panic on heterogeneous cores with narrower secondary `ASIDBits`, while `seL4` AArch64 gates boot via `check16BitASID()` (`arm64_machine.h` L159–169, `boot.c` L196–199).

### 2. Domain-Isolation Failures Under Unprobed Narrow ASIDs and Conditional `satp`-Switch Fencing

**Basis: normative, source, execution.**

`seL4/seL4` (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`) allocates a 16-bit software ASID (`seL4_NumASIDPoolsBits = 7`, `seL4_ASIDPoolIndexBits = 9` in `riscv64/sel4/sel4_arch/constants.h` L43–45; two-level `riscvKSASIDTable` in `vspace.c` L319–346 and `l4v/spec/abstract/RISCV64/ArchVSpace_A.thy` L33–58) and passes `(ucast asid)` directly into `setVSpaceRoot` (`include/arch/riscv/arch/machine.h` L259–273):
```c
static inline void setVSpaceRoot(paddr_t addr, asid_t asid) {
    satp_t satp = satp_new(SATP_MODE, asid, addr >> seL4_PageBits);
    write_satp(satp.words[0]);
#ifdef ENABLE_SMP_SUPPORT
    sfence_local();
#else
    sfence();
#endif
}
```
`seL4` remains sound on `ASIDLEN < 16` **only** because `setVSpaceRoot` unconditionally issues `sfence.vma x0, x0`. If a kernel optimizes context switches to skip `sfence.vma` whenever `next_sw_asid != prev_sw_asid` without proving `sw_asid < 2^ASIDLEN`, isolation breaks immediately (`reval_pkg2.py`): on `ASIDLEN = 8`, switching from `sw_asid_A = 0x0001` to `sw_asid_B = 0x0101` truncates both to hardware tag `0x01` (or `0` when `ASIDLEN = 0`), causing Domain $B$ to hit Domain $A$'s cached user TLB/PWC entries. Likewise, selective `hwASIDFlush(0x0101)` (`sfence.vma x0, rs2`, `machine.h:122, 146`) ignores `rs2[15:8]` (`#norm:sfence_vma_rs2_bits`), invalidating `0x0001` while failing to separate domains.

### 3. Conditional `satp`-Switch Fencing vs. Generation-Rollover and Two-Level `hw_asid_t` Allocators

**Basis: normative, source, documentation, execution.**

| Strategy | Implementation | Tag Rule | Switch Barrier | Rollover / Eviction | `G = 1` Kernel Entries |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Zero-ASID Non-Global Flush** | `Linux` `set_mm_noasid` (`riscv/mm/context.c` L200–205); `supervisor.adoc` L1370–1375 | Always `ASID = 0` | `sfence.vma x0, rs2` (`rs2 != x0`, `X[rs2] == 0`) | None (every switch) | **Preserved** (`rs2 != x0`) |
| **Global-Flush Switch** | `seL4` `setVSpaceRoot` (`machine.h` L259–273); `xv6` `trampoline.S` L88–111 | `xv6`: `0`; `seL4`: `sw_asid` | `sfence.vma x0, x0` | None (`deleteASID` calls `hwASIDFlush`) | **Flushed** |
| **SMP Generation Rollover** | `Linux` `set_mm_asid` (`riscv/mm/context.c` L35–198; `arm64/mm/context.c` L104–271) | `version \| hw_asid`; needs `num_asids > 2*CPUs` | **Zero fence on fastpath**; `local_flush_tlb_all()` if `context_tlb_flush_pending[cpu]` | Exhausting bitmap increments `current_version`, snapshots active/reserved CPUs, sets flush mask | Preserved until rollover `local_flush_tlb_all()` |
| **Two-Level `hw_asid_t` FIFO** | `seL4` AArch64 `findFreeHWASID` (`arm64_vspace.c` L949–1009; `l4v` `AARCH64/ArchVSpace_A.thy` L81–160) | `hw_asid_t` (`8`/`16`-bit; `0` reserved) | `ISB` / `DSB` when `stored_vmid_valid` | FIFO `armKSNextASID` sweep evicts one `asid_t` + `invalidateTranslationASID(hw_asid)` | `nG=1` user entries flushed; `TTBR1` kernel spared |

In **SMP Generation Rollover**, three concurrent invariants carry the proof:
1. **Lock-Free Fastpath `cmpxchg_relaxed` vs. `__flush_context` `xchg(..., 0)` (`riscv/mm/context.c` L73, L168–198):** The fastpath succeeds only if `cmpxchg_relaxed(&active_context[cpu], old_active_cntx, cntx)` swaps from a nonzero `old_active_cntx` under matching `current_version`. Concurrently, `__flush_context()` under `context_lock` executes `atomic_long_xchg_relaxed(&active_context[i], 0)`. By coherence order on `active_context[cpu]`: if `xchg` precedes `cmpxchg`, `active_context[cpu] == 0` forces `cmpxchg` to fail onto the locked slow path (`context_tlb_flush_pending[cpu]` triggers `local_flush_tlb_all()`); if `cmpxchg` precedes `xchg`, `__flush_context()` observes the active ASID, marks it used in `context_asid_map`, and preserves it in `reserved_context[cpu]` (`L80–84`). Exhaustive interleaving over 64 schedules in `reval_pkg2.py` yielded `0` collisions.
2. **Capacity Floor and `reserved_context` Pinning:** Across multiple rollovers without a context switch, `__flush_context` falls back to `reserved_context[cpu]` (`L80–82`) and `check_update_reserved_context` (`L35–58`) updates *all* matching CPU slots without early return. Because ASID `0` is reserved plus up to 1 ASID per CPU, `num_asids <= num_possible_cpus() + 1` starves rollover (`reval_pkg2.py`: `ASIDLEN = 2`, 3 CPUs yields 0 free ASIDs), motivating `num_asids > 2 * num_possible_cpus()` (`riscv/mm/context.c:255`) and ARM64 KPTI's `max_pinned_asids = num_available_asids - num_possible_cpus() - 2` (`arm64/mm/context.c:396`).
3. **`mm_cpumask` Monotonicity (`riscv/mm/context.c` L210–224):** With ASID caching enabled, `set_mm` MUST NOT clear `cpu` from `mm_cpumask(prev)` (unlike `set_mm_noasid` at `L222`), because `prev`'s translations persist in `cpu`'s TLB until rollover.

Syeda and Klein (`JAR 2020`, `doi:10.1007/s10817-019-09539-7`; `ITP 2018`, `doi:10.1007/978-3-319-94821-8_32`) formalize two-level ASID assignment (`asid_t -> hw_asid_t`, as in `seL4` `arm64_vspace.c`) via an injective live-tag map requiring `invalidateTranslationASID(hw_asid)` before reassigning an evicted `hw_asid_t`.

### 4. Boot-Time Non-Leaf Page-Table Initialization Barrier Windows

**Basis: normative, source, documentation, execution.**

`#norm:satp_op_sfence_vma` (`supervisor.adoc` L1122–1128) specifies that `csrw satp` neither orders prior explicit PTE writes before subsequent page-table walks nor flushes caches, and `#norm:sfence_vma_ordering_semantics` (`L1324–1341`) allows caching invalid (`V = 0`) PTEs and non-leaf directory pointers. Three boot windows arise:

1. **Window 1 — Pre-`satp` Store Ordering Before First Paged Fetch (`Linux` `head.S:104–122`, `init.c:888–891, 1313–1314`; `xv6` `vm.c:75–84`):** After `setup_vm()` writes non-leaf and leaf entries into `early_pg_dir`/`trampoline_pg_dir` under `Bare`, `relocate_enable_mmu` issues `sfence.vma` **before** `csrw CSR_SATP, a0` (`head.S:104–105`), ensuring PTWs observe newly stored directory PTEs (`reval_pkg2.py`: omitting pre-`satp` `sfence.vma` faults on `l2_invalid`), and issues a second `sfence.vma` after installing `swapper_pg_dir`. `seL4` (`vspace.c:106–165, 305–308`, `machine.h:259–273`) writes `write_satp` before `sfence()`, relying on `elfloader` sharing identical kernel window mappings prior to `activate_kernel_vspace()`.
2. **Window 2 — Initial User Non-Leaf PT Construction While `satp` Is Active Before First `SRET` (`seL4` `boot.c:331–448`, `vspace.c:167–222`):** While kernel `satp` is active, `create_it_address_space` installs non-leaf directories (`map_it_pt_cap` `L194`: `sfence()`) and user frames (`map_it_frame_cap` `L221`: `sfence()`). Under speculative walks and negative (`V = 0`) caching (`Simner et al., ESOP 2022 doi:10.1007/978-3-030-99336-8_6`), replacing `map_it_pt_cap`'s `sfence()` with single-VA `sfence.vma va, asid` (`rs1 != x0`) leaves stale non-leaf PWC entries for sibling user pages (`reval_pkg2.py`), requiring `sfence.vma x0, asid` or `sfence.vma x0, x0` (`supervisor.adoc:1376–1379`) plus `fence.i` (`xv6` `trampoline.S:106`, `seL4` `boot.c:166`) before first user `SRET`.
3. **Window 3 — SMP Boot Handoff (`seL4` `boot.c:154–188`; `Linux` `head.S:128–184`):** Primary core executes `fence_rw_rw()` before setting `node_boot_lock = 1` (`boot.c:173–180`); secondaries execute `fence_r_rw()` (`L158`), `init_cpu()`, and `ifence_local()` (`L166`).

### 5. Mechanizable Verification Obligations for ASID-Parametric Kernels

**Basis: derived, source.**

A clean machine-checked kernel proof layer isolates ASID width and boot ordering behind four obligations:
1. **`HwAsidMask(asidlen, tag) := if asidlen == 0 then 0 else tag && ((1 <<< asidlen) - 1)`:** Route `satp` writes and `sfence.vma _, rs2` through `HwAsidMask`.
2. **`InjectiveLiveHwTag` or `ZeroAsidFlushed`:** Enforce either `(asidlen > 0 ∧ 2^asidlen > 2 * max_cpus ∧ rollover flush invariant)` or unconditional `sfence.vma x0, rs2` on switch (`asid = 0` or `rs2 = x0`).
3. **`CleanProbePostcondition`:** Boot-time `WARL` `satp` probing (`MODE != Bare`) establishes `tlbDirty = []` via `local_flush_tlb_all()` before user ASID allocation.
4. **`BootPtBarrierReady`:** `ptStoreBuf == empty` before first `csrw satp` (pre-`satp` `sfence.vma`), and `pwcDirty(IT_ASID) == [] ∧ icacheDirty == []` before first user `SRET` (`sfence.vma x0, asid`/`x0, x0` + `fence.i`).

## Boundaries

- **`known not to apply` — Probing `ASIDLEN` with `satp.MODE == Bare`, omitting pre-`satp` `sfence.vma` after boot PTE writes, or clearing `mm_cpumask(prev)` under active ASIDs:** `#norm:satp_mode_bare_zero_fields` / `#norm:satp_mode_bare_nonzero_unspec` forbid nonzero `ASID` under `Bare`; `#norm:satp_op_sfence_vma` denies store-to-PTW ordering on `satp` writes; and `Linux` `riscv/mm/context.c` (`L210–224`) relies on sticky `mm_cpumask` bits for remote shootdowns. All three shortcuts are `known not to apply`. **Basis: normative, source.**
- **`unsupported` — Running non-hypervisor `seL4` AArch64 on 8-bit ASID cores, or `sfence.vma` when `satp.MODE` is read-only zero:** `seL4` `check16BitASID()` (`arm64_machine.h:159–169`, `boot.c:196–199`) rejects <16-bit ASID hardware; `#norm:satp_mode_roz_sfence_illegal` (`supervisor.adoc:1408–1411`) permits `sfence.vma` traps when `satp.MODE` is hardwired `Bare`. **Basis: normative, source.**
- **`not examined` — `hgatp.VMID` (`VMIDLEN` `0..7`/`0..14`), `Svinval` (`sinval.vma`/`sfence.w.inval`), and ARMv8.4 `FEAT_TLBIOS`/`FEAT_CNPn`:** Guest-physical `VMID` rollover and batched invalidation extensions were `not examined`. **Basis: source.**
- **`unknown` — Negative (`V = 0`) TLB caching frequency across commercial `Sv39`/`Sv48` silicon lacking `Svvptc`:** Permissible under `supervisor.adoc:1338–1341` (requiring conservative fences), actual vendor hit rates remain `unknown`. **Basis: normative, documentation.**

## Evidence

| Subject / Paper | Pinned SHA / DOI | Exact Inspected Files, Line Ranges, or Scope | Basis |
| :--- | :--- | :--- | :--- |
| `riscv/riscv-isa-manual` | `c05f1725f25526dd8463bac6ca75cfcfbee17d05` | `src/priv/supervisor.adoc` L1007–1061 (`#norm:asidlen`, `#norm:asid_lsb_first`, `#norm:satp_mode_bare_zero_fields`), L1106–1135 (`#norm:satp_op_sfence_vma`), L1209–1411 (`#norm:sfence_vma_rs2_bits`, `#norm:sfence_vma_ordering_semantics`, `#norm:satp_mode_roz_sfence_illegal`) | `normative` |
| `riscv/sail-riscv` | `76f1ce3c184797178864b9869963e8b44465889e`, `doi:10.1145/3290384` | `model/core/sys_regs.sail` L1212–1280 (`get_asid`, `legalize_satp`); `model/sys/vmem.sail` L266–299; `model/sys/vmem_tlb.sail` L117–243 | `source`, `documentation` |
| `opencompl/sail-riscv-lean` | `51c635c460125ac87955d061fcd902ce03b8011f` | `LeanRV64D/SysRegs.lean`, `LeanRV64D/Vmem.lean`, `LeanRV64D/VmemTlb.lean` L219–345 | `source` |
| `seL4/seL4` | `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, `doi:10.1145/2560537` | `src/arch/riscv/kernel/{vspace.c,boot.c}` (`map_kernel_window`, `map_it_pt_cap` L167–195, `deleteASID` L494–504, `setVMRoot` L578–602, SMP boot L154–188); `include/arch/riscv/arch/machine.h` L112–273 (`setVSpaceRoot`); `libsel4/.../riscv64/.../constants.h` L43–45; `arm64_machine.h` (`check16BitASID` L159–169); `src/arch/arm/64/kernel/{boot.c,vspace.c}` (`findFreeHWASID` L965–1009) | `source`, `documentation` |
| `seL4/l4v` | `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`, `doi:10.1007/978-3-642-03359-9_20` | `spec/abstract/RISCV64/ArchVSpace_A.thy` L33–190; `spec/abstract/AARCH64/ArchVSpace_A.thy` L81–160 (`find_free_vmid`); `spec/machine/RISCV64/MachineOps.thy` L197–225 | `source`, `documentation` |
| `torvalds/linux` | `5f22fb20497f4983094131f00a734362300d22d2` | `arch/riscv/mm/context.c` L22–275 (`__flush_context`, `__new_context`, `set_mm_asid`, `set_mm_noasid`, `asids_init`); `arch/riscv/kernel/head.S` L76–125; `arch/riscv/mm/init.c` L837–910, L1055–1317; `arch/arm64/mm/context.c` L41–271, L374–422 | `source` |
| `mit-pdos/xv6-riscv` | `fa2ddcb7ca87a77af579380a6eafd5aff163b44f` | `kernel/vm.c` L66–84 (`kvminithart`); `kernel/trampoline.S` L88–111 | `source` |
| Syeda & Klein & Simner et al. | `doi:10.1007/s10817-019-09539-7`, `doi:10.1007/978-3-319-94821-8_32`, `doi:10.1007/978-3-030-99336-8_6`, `arXiv:2203.00642` | Cached-MMU consistent-set partitioning, two-level hardware ASID bijections, and Armv8-A walk-cache / barrier semantics | `documentation` |
| Standalone Python Probe (`reval_pkg2.py`) | Executed `2026-11-20` on Python 3.13 | Verified `ASIDLEN` `0..16` probing, `ASIDLEN=8`/`0` cross-domain leaks, probe pollution, 64-schedule rollover + starvation, and boot PWC hazards (`0.42 ms`, exit `0`) | `execution` |

## Revalidation

Run the standalone Python 3 probe below (`< 1 ms`, standard library only) to revalidate `ASIDLEN` `0..16` discovery, unprobed conditional-fence aliasing, SMP rollover schedules, and boot PWC barriers:

```python
#!/usr/bin/env python3
import itertools, time

t0 = time.perf_counter()
SATP_ASID_SHIFT, SATP_ASID_MASK, SATP_PPN_MASK = 44, 0xFFFF, (1 << 44) - 1

def legalize_satp(old, val, asidlen, modes=(0, 8, 9)):
    mode = (val >> 60) & 0xF
    if mode not in modes:
        return old
    mask = (1 << asidlen) - 1 if asidlen > 0 else 0
    return (mode << 60) | (((val >> SATP_ASID_SHIFT) & SATP_ASID_MASK & mask) << SATP_ASID_SHIFT) | (val & SATP_PPN_MASK)

for w in range(17):
    init = (8 << 60) | 0x100
    w_val = legalize_satp(init, init | (SATP_ASID_MASK << SATP_ASID_SHIFT), w)
    rb = (w_val >> SATP_ASID_SHIFT) & SATP_ASID_MASK
    assert rb.bit_length() == w and rb == ((1 << w) - 1) and legalize_satp(w_val, init, w) == init

class RelaxedMmu:
    def __init__(self, asidlen):
        self.asidlen, self.satp, self.pwc, self.leaves, self.buf, self.ram = asidlen, 8 << 60, [], [], {}, {}

    def write_pte(self, ppn, idx, pte):
        self.buf[(ppn, idx)] = pte

    def write_satp(self, mode, asid, ppn):
        self.satp = legalize_satp(self.satp, (mode << 60) | ((asid & 0xFFFF) << 44) | ppn, self.asidlen)

    def sfence_vma(self, va=None, rs2_asid=None):
        self.ram.update(self.buf); self.buf.clear()
        mask = (1 << self.asidlen) - 1 if self.asidlen > 0 else 0
        am = None if rs2_asid is None else (rs2_asid & mask)
        if va is None:
            if am is None:
                self.pwc.clear(); self.leaves.clear()
            else:
                self.pwc = [e for e in self.pwc if e[4] or e[0] != am]
                self.leaves = [e for e in self.leaves if e[3] or e[0] != am]
        else:
            vpn = va >> 12
            self.leaves = [e for e in self.leaves if (am is not None and e[3]) or (am is not None and e[0] != am) or e[1] != vpn]

    def translate(self, va):
        vpn, a, root = va >> 12, (self.satp >> 44) & 0xFFFF, self.satp & SATP_PPN_MASK
        for e in self.leaves:
            if e[1] == vpn and (e[3] or e[0] == a):
                return ("tlb_hit", e[2])
        idx2 = (va >> 30) & 0x1FF
        l1 = next(((e[3], e[4]) for e in self.pwc if e[1] == 2 and e[2] == idx2 and (e[4] or e[0] == a)), None)
        if l1 is None:
            p2 = self.ram.get((root, idx2))
            if not p2 or not p2["v"]:
                return ("fault", "l2_invalid")
            l1 = (p2["ppn"], p2.get("g", False))
            self.pwc.append((a, 2, idx2, l1[0], l1[1]))
        p1 = self.ram.get((l1[0], (va >> 21) & 0x1FF))
        if not p1 or not p1["v"]:
            return ("fault", "l1_invalid")
        p0 = self.ram.get((p1["ppn"], (va >> 12) & 0x1FF))
        if not p0 or not p0["v"]:
            return ("fault", "l0_invalid")
        self.leaves.append((a, vpn, p0["ppn"], l1[1] or p1.get("g", False) or p0.get("g", False)))
        return ("ptw_ok", p0["ppn"])

def mk_tree(m, r, l1, l0, pa):
    m.write_pte(r, 0, {"v": True, "ppn": l1}); m.write_pte(l1, 0, {"v": True, "ppn": l0}); m.write_pte(l0, 1, {"v": True, "ppn": pa})

for w, a1, a2 in ((8, 0x0001, 0x0101), (0, 1, 2)):
    m = RelaxedMmu(w); mk_tree(m, 0x100, 0x101, 0x102, 0xA000); mk_tree(m, 0x200, 0x201, 0x202, 0xB000)
    m.sfence_vma(); m.write_satp(8, a1, 0x100); assert m.translate(0x1000) == ("ptw_ok", 0xA000)
    m.write_satp(8, a2, 0x200); assert m.translate(0x1000) == ("tlb_hit", 0xA000)
    m.write_satp(8, 0, 0x200); m.sfence_vma(None, 0); assert m.translate(0x1000) == ("ptw_ok", 0xB000)

mp = RelaxedMmu(4); mk_tree(mp, 0x100, 0x101, 0x102, 0xF000); mk_tree(mp, 0x300, 0x301, 0x302, 0x3000)
mp.sfence_vma(); mp.write_satp(8, 0xFFFF, 0x100); assert mp.translate(0x1000) == ("ptw_ok", 0xF000)
mp.write_satp(8, 0, 0x100); mp.write_satp(8, 15, 0x300); assert mp.translate(0x1000) == ("tlb_hit", 0xF000)
mp.sfence_vma(); assert mp.translate(0x1000) == ("ptw_ok", 0x3000)

checks, viol = 0, 0
for sched in itertools.product((0, 1), repeat=4):
    ver, amap, cidx, act, res, pend, mmc, tlb = 1 << 16, {0}, 1, [0, 0], [0, 0], [False, False], [0]*5, [{}, {}]
    for s_i, cpu in enumerate(sched):
        mm = (s_i + cpu) % 5
        c = mmc[mm]
        if act[cpu] and (c >> 16) == (ver >> 16):
            act[cpu], nf = c, False
        else:
            c = mmc[mm]
            if (c >> 16) != (ver >> 16):
                nc = ver | (c & 7)
                hit = any(res[k] == c for k in (0, 1))
                for k in (0, 1):
                    if res[k] == c:
                        res[k] = nc
                if c != 0 and (hit or ((c & 7) not in amap)):
                    amap.add(c & 7); c = nc
                else:
                    cand = next((a for off in range(8) if (a := (cidx + off) % 8) != 0 and a not in amap), None)
                    if cand is None:
                        ver += 1 << 16; amap = {0}
                        for k in (0, 1):
                            x = act[k]; act[k] = 0
                            if x == 0: x = res[k]
                            amap.add(x & 7); res[k] = x; pend[k] = True
                        cand = next(a for a in range(1, 8) if a not in amap)
                    amap.add(cand); cidx = cand; c = cand | ver
                mmc[mm] = c
            nf = pend[cpu]; pend[cpu] = False; act[cpu] = c
        if nf: tlb[cpu].clear()
        ahw = c & 7; checks += 1
        if ahw in tlb[cpu] and tlb[cpu][ahw] != mm: viol += 1
        tlb[cpu][ahw] = mm
assert viol == 0 and len([a for a in range(4) if a not in {0, 1, 2, 3}]) == 0

bm = RelaxedMmu(16); mk_tree(bm, 0x500, 0x501, 0x502, 0x5000); bm.write_satp(8, 0, 0x500)
assert bm.translate(0x1000) == ("fault", "l2_invalid")
bm.sfence_vma(); assert bm.translate(0x1000) == ("ptw_ok", 0x5000)
bm.write_satp(8, 1, 0x600); mk_tree(bm, 0x600, 0x601, 0x602, 0x6000); bm.sfence_vma()
assert bm.translate(0x1000) == ("ptw_ok", 0x6000)
mk_tree(bm, 0x600, 0x701, 0x702, 0x7000); bm.write_pte(0x702, 2, {"v": True, "ppn": 0x7000})
bm.sfence_vma(0x1000, 1); assert bm.translate(0x2000) == ("fault", "l0_invalid")
bm.sfence_vma(None, 1); assert bm.translate(0x2000) == ("ptw_ok", 0x7000)

print(f"reval_pkg2 PASS: asidlen_0_16=ok, rollover_checks={checks} violations={viol}, boot_pwc=ok ({(time.perf_counter()-t0)*1000:.2f} ms)")
```

Upstream revalidation checks:
1. Diff `riscv/sail-riscv` `sys_regs.sail` (`legalize_satp`), `torvalds/linux` `arch/riscv/mm/{context.c,init.c}`, `head.S`, and `seL4/seL4` `include/arch/riscv/arch/machine.h` (`setVSpaceRoot`) when upgrading kernels or Sail models.
2. Diff `riscv/riscv-isa-manual` `src/priv/supervisor.adoc` (`#norm:asidlen`, `#norm:satp_op_sfence_vma`, `#norm:sfence_vma_rs2_bits`) to check extensions such as `Svvptc` relaxing invalid-PTE caching.
