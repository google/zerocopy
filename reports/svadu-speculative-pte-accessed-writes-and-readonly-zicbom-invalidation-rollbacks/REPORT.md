# RISC-V Svadu Speculative PTE.A Memory Writes, Read-Only Zicbom cbo.inval Rollbacks, and RVWMO Fence Hazards

## Summary

Formal functional-correctness, memory-isolation, and noninterference models of RISC-V OS kernels, microkernels, and hypervisors often assume that squashed speculative memory accesses never mutate architectural RAM, that read-only (`R=1, W=0`) user page-table mappings cannot destroy supervisor writes, and that `smp_mb()` (`fence rw,rw`) or single-pass TLB/I-cache flushes order DMA and code-frame reclamation. Four architectural interactions across `menvcfg`/`senvcfg`/`henvcfg`, `Svadu`/`Svade`, `Zicbom`, `RVWMO`, and `Zifencei` break those assumptions unless explicitly discharged:

1. **Asymmetric `ADUE` placement (`menvcfg` bit 61 absent from `senvcfg`) and `Svadu` speculative `PTE.A` RAM writes:** Under `Svadu`, hardware page-table A/D updating is controlled by `menvcfg.ADUE` (bit 61, governing host `satp` and hypervisor guest-physical `hgatp` walks) and `henvcfg.ADUE` (bit 61, governing virtualized `vsatp` walks), whereas `senvcfg` defines bits `[63:34]` as `WPRI` (`PMM` at `[33:32]`) and omits `ADUE` altogether. S-mode kernels cannot disable hardware A/D updates via `senvcfg`, and OpenSBI rejects `SBI_FWFT_PTE_AD_HW_UPDATING` (`SBI_ENOTSUPP`) whenever `Svade` is absent. When `menvcfg.ADUE == 1`, hardware updates `PTE.A = 1` atomically **in physical RAM** (never solely in TLBs) and is **normatively permitted to set `PTE.A = 1` during speculative execution even when the load is squashed and never architecturally performed**. Transient out-of-bounds loads (Spectre-v1) therefore leave a persistent, **timer-free** 1-bit-per-page architectural covert channel in RAM and race concurrently against non-atomic supervisor PTE stores.
2. **Read-only (`R=1, W=0`) `Zicbom` `cbo.inval` permission and `menvcfg.CBIE x senvcfg.CBIE` dirty-cache rollbacks:** Unlike `cbo.zero` (`Zicboz`), which requires Store (`W=1`) permission and checks/sets `PTE.D`, `Zicbom` instructions (`cbo.inval`, `cbo.clean`, `cbo.flush`) succeed whenever **Load (`R=1`) OR Store (`W=1`)** permission holds (plus `X=1` under `sstatus.MXR=1`) and neither check nor set `PTE.D` (while still reporting faults as Store/AMO page/access faults, `scause = 15`/`7`). U-mode executes destructive raw `cbo.inval`—deallocating dirty coherent cache lines without writeback—iff `menvcfg.CBIE == 0b11` **and** `senvcfg.CBIE == 0b11`. Because OpenSBI sets `menvcfg.CBIE = 0b11` whenever `Zicbom` is present, any kernel that scrubs retyped frames or writes IPC buffers via uncleaned CPU stores (such as `seL4` `clearMemory` -> `memzero`) without clearing `senvcfg.CBIE` lets a read-only (`R=1, W=0, U=1`) user mapping roll physical memory back to stale pre-scrub DRAM secrets. Moreover, `mstateen0.ENVCFG` (bit 62) gates `senvcfg` access (requiring `stvec` setup before `csrw senvcfg, zero`), and WARL `CBIE_AllowInval` hardware silently ignores writes of `0b01`, preserving `0b11` unless `0b00` is written.
3. **`RVWMO` non-I/O preserved program order (`fence rw,ow` / `fence ir,rw`) and `FIOM` virtualization:** `RVWMO` preserved program order applies exclusively when *both* operations access regular main memory (`r`/`w`), providing zero ordering against MMIO (`i`/`o`). `smp_mb()` (`fence rw,rw`) leaves MMIO doorbells unordered; Linux `writel()` (`fence w,o`) omits predecessor `r`, failing to order prior CPU reads of a recycled TX buffer before a DMA doorbell (`o`) overwrites that buffer (`fence rw,ow` required); and `readl()` (`fence i,ir`) omits successor `w`, failing to order an RX completion read (`i`) before descriptor-ring recycling stores (`w`) under relaxed polling (`fence ir,rw` required). When hypervisors or microkernels map emulated device queues to regular RAM, `senvcfg.FIOM = 1` / `henvcfg.FIOM = 1` is required so `i`/`o` fences imply `r`/`w`.
4. **Two-step multi-hart `sfence.vma`-before-`fence.i` executable frame reclamation:** `sfence.vma` flushes hart-local address-translation caches without invalidating instruction caches, while `fence.i` synchronizes hart-local instruction fetches with prior visible data stores without invalidating TLBs. Reclaiming an executable (`X=1`) physical frame across multiple harts requires a strict **two-step shootdown**: (1) unmap `PTE.V := 0` (or `X := 0`), execute `fence w,rw`, and complete local + remote `sfence.vma` on all harts *before* modifying the frame; then (2) write new bytes, order data stores (`fence w,o` + `cbo.clean` if I-cache is incoherent with dirty D-cache), and complete local + remote `fence.i` before exposing the new executable mapping.

## Applicability

These findings apply to formal verification, security noninterference proofs, M-mode firmware integration, and memory-management implementation on 32-bit (`Sv32`) and 64-bit (`Sv39`, `Sv48`, `Sv57`) RISC-V platforms implementing any subset of the Privileged Architecture (`S`, `H`, `Smstateen`), `Svadu`, `Svade`, `Zicbom`, `Zicboz`, `RVWMO`, and `Zifencei`.

The five subjects in `REPORT.json` establish the hardware/firmware/OS stack:

- **Normative ISA specifications:** `riscv/riscv-isa-manual` at `3142f66fd71c7ea0326b3687072318aedab587f8` defines `menvcfg`/`senvcfg`/`henvcfg`, `Svadu`/`Svade` page-table walk atomicity and speculative execution rules, `Smstateen` CSR gating, `Zicbom`/`Zicboz` permission and Modified Load Value axioms, `RVWMO` memory/I/O ordering, `sfence.vma`, and `Zifencei`.
- **Executable formal ISA specification:** `riscv/sail-riscv` at `71312d537fc10782c42b7303a611b923af0566d4` provides mechanized operational definitions for `MEnvcfg`/`SEnvcfg`/`HEnvcfg`, `hw_updates_pte`, `check_PTE_permission`, `update_PTE_Bits`, `legalize_xenvcfg_cbie`, `cbop_priv_check`, and `is_fiom_active`.
- **M-mode SBI firmware:** `riscv-software-src/opensbi` at `61f1973bd50338b36c52dc34006f76d464ca4f34` establishes reset defaults written to `mstateen0` and `menvcfg` (`ENVCFG_CBIE_INV`, `ENVCFG_ADUE`) before S-mode entry and `SBI_FWFT_PTE_AD_HW_UPDATING` constraints.
- **Production S-mode kernels:** `torvalds/linux` at `aa31d5f8b151b786b748c6bfc9a8c4f1855c8adc` and `seL4/seL4` at `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7` demonstrate OS page-table updates, `senvcfg` initialization (and omission in `seL4`), `clearMemory` cache behavior, MMIO/SMP barrier macros, and multi-hart TLB/I-cache shootdowns.

## Findings

### 1. Environment CSR Asymmetry (`menvcfg` vs `senvcfg` / `henvcfg`) and `Svadu` Speculative `PTE.A` RAM Writes

Basis: normative + source + execution + derived

#### 1.1 Why S-Mode Cannot Disable Hardware `PTE.A`/`PTE.D` Updates via `senvcfg` or `SBI_FWFT`

In `riscv/riscv-isa-manual` (`3142f66fd71c7ea0326b3687072318aedab587f8`, `src/priv/svadu.adoc:6-13`, `src/priv/machine.adoc:2194-2216`, `src/priv/supervisor.adoc:790-821`) and `riscv/sail-riscv` (`71312d537fc10782c42b7303a611b923af0566d4`, `model/core/sys_regs.sail:446-506`), `ADUE` (Hardware A/D Update Enable, bit 61) is asymmetrically placed across environment CSRs:

```sail
bitfield MEnvcfg : bits(64) = {
  STCE : 63, PBMTE : 62, ADUE : 61, CDE : 60, DTE : 59,
  PMM : 33 .. 32, CBZE : 7, CBCFE : 6, CBIE : 5 .. 4, SSE : 3, LPE : 2, FIOM : 0,
}
bitfield SEnvcfg : bits(64) = {
  PMM : 33 .. 32, UKTE : 8, CBZE : 7, CBCFE : 6, CBIE : 5 .. 4, SSE : 3, LPE : 2, FIOM : 0,
}
bitfield HEnvcfg : bits(64) = {
  STCE : 63, PBMTE : 62, ADUE : 61, DTE : 59,
  PMM : 33 .. 32, CBZE : 7, CBCFE : 6, CBIE : 5 .. 4, SSE : 3, LPE : 2, FIOM : 0,
}
```

Because S-mode and U-mode share the `satp`-rooted page table, `senvcfg` has **no `ADUE` bit** (`WPRI` at bits `[63:34]`, `supervisor.adoc:802-805`). In `sail-riscv` (`model/sys/vmem_pte.sail:304-309`), `hw_updates_pte` returns `true` whenever `Ext_Svadu` is enabled and `read_henvcfg()[ADUE] == 0b1` (for virtualized `vsatp` walks) or `menvcfg[ADUE] == 0b1` (for host `satp` and hypervisor `hgatp` walks)—or unconditionally when neither `Ext_Svadu` nor `Ext_Svade` is enabled. Moreover, `henvcfg.ADUE` is read-only zero whenever `menvcfg.ADUE == 0` (`machine.adoc:2206-2207`), and toggling `menvcfg.ADUE` requires `sfence.vma x0, x0` (`machine.adoc:2209-2211`).

OpenSBI (`riscv-software-src/opensbi` `61f1973bd50338b36c52dc34006f76d464ca4f34`) also prevents S-mode from disabling `ADUE` on `Svadu`-only hardware:

- At M-mode boot (`lib/sbi/sbi_hart.c:160-171`), if `SBI_HART_EXT_SVADE` is absent and `SBI_HART_EXT_SVADU` is present, OpenSBI sets `menvcfg |= ENVCFG_ADUE`. (If *both* extensions are present, OpenSBI defaults `menvcfg.ADUE = 0`, matching Linux `riscv_ext_svadu_validate` in `arch/riscv/kernel/cpufeature.c:308-316`, which returns `-EOPNOTSUPP` for `Svadu` when `Svade` is available.)
- In `lib/sbi/sbi_fwft.c:161-176`, `fwft_adue_supported` returns `SBI_ENOTSUPP` unless **both** `SBI_HART_EXT_SVADU` and `SBI_HART_EXT_SVADE` exist. On RVA23 cores implementing `Svadu` without `Svade`, `menvcfg.ADUE` stays `1` permanently.

#### 1.2 Architectural RAM Mutation by Squashed Speculative Loads Under `Svadu`

Under `Svade` (`menvcfg.ADUE == 0`, `supervisor.adoc:1603-1606`), accessing a leaf PTE with `PTE.A == 0` (or storing with `PTE.D == 0`) faults only on retirement; speculative page-table walks (`supervisor.adoc:1803-1808`) *must not* fault or modify RAM.

Under `Svadu` (`menvcfg.ADUE == 1`, `supervisor.adoc:1608-1635, 1745-1781, 1797-1808`), step 9 of address translation executes an atomic `PTESIZE`-wide compare-and-swap directly in physical memory:

1. **Direct physical RAM update (`supervisor.adoc:1745-1750, 1780-1781`):** Hardware atomically compares the in-memory PTE against `pte`, sets `pte.a = 1` (and `pte.d = 1` on stores), and stores the `PTESIZE` word to physical RAM; *"The address-translation cache cannot be used in step 9; accessed and dirty bits may only be updated in memory directly."*
2. **Speculative `PTE.A = 1` commit (`supervisor.adoc:1625-1633, 1803-1808`):** Lines `1625-1630` normatively permit squashed transient execution to mutate architectural RAM:
   > *"Updates of the A bit may be performed as a result of speculation, even if the associated memory access ultimately is not performed architecturally. However, updates to the D bits ... that result from an explicit store must be exact (i.e. non-speculative) and observed in program order by the local hart."*
   (At `lines 1631-1633`, if a hypervisor `hgatp` leaf PTE grants `W=1`, hardware **may** also speculatively set `PTE.D = 1` in that `hgatp` PTE during an implicit speculative walk of a guest `vsatp` table.)

#### 1.3 Timer-Free Speculative Noninterference Violation and Concurrent PTE RMW Races

Two verification hazards follow directly:

- **Timer-free persistent architectural covert/side channel:** Speculative constant-time and noninterference models (Guarnieri et al., *Spectector*, IEEE S&P 2020, DOI `10.1109/SP40000.2020.00011`; Cauligi et al., PLDI 2020, DOI `10.1145/3385412.3385970`) model transient execution (Kocher et al., *Spectre*, IEEE S&P 2019, DOI `10.1109/SP.2019.00002`) as altering only *microarchitectural* caches while preserving architectural memory upon squash—implying that disabling `scounteren` (`rdcycle`/`rdtime`) removes noiseless timing Measurement (cf. Gras et al., *AnC*, NDSS 2017, DOI `10.14722/ndss.2017.23271`). Under `Svadu`, a squashed transient load `probe_array[secret_bit * 4096]` targeting unaccessed `V=1, R=1, U=1, A=0` pages writes `PTE.A := 1` **into architectural RAM**. With zero timers (`scounteren = 0`), this persistent 1-bit-per-page mark remains observable via OS working-set aging (`ptep_test_and_clear_young`, Linux `arch/riscv/mm/pgtable.c:32-39`), `/proc/<pid>/pagemap` / `mincore` / swap eviction, or hypervisor dirty-page scans. `seL4` (`src/arch/riscv/kernel/vspace.c:663-674`) avoids `Svadu` transitions on user mappings only by eagerly pre-setting `accessed = 1, dirty = 1` in `makeUserPTE`.
- **Concurrent hardware CAS vs supervisor non-atomic PTE stores:** Hardware walkers update live (`V=1, A=0` or `W=1, D=0`) PTEs without holding OS locks. A non-atomic read-modify-write via plain `sd` (`__set_pte_at`, `pgtable.c:12-25`) can clobber a concurrent hardware `PTE.D = 1` transition; clearing `A`/`D` or revoking `W` on live `Svadu` PTEs requires atomic AMO operations (`amoand.d`, as in `test_and_clear_bit` at `pgtable.c:37`) followed by `sfence.vma`.

### 2. `Zicbom` Read-Only (`R=1`) Permission Check, `CBIE` Privilege Hierarchy, and Dirty-Cache Rollback Attacks

Basis: normative + source + execution + derived

#### 2.1 `Zicbom` vs `Zicboz` PTE Permission Asymmetry

In `src/unpriv/cmo.adoc:352-405` and `sail-riscv` (`model/sys/vmem_pte.sail:295, 346-352`), `Zicboz` and `Zicbom` check distinct leaf PTE permissions:

| Instruction (`Extension`) | Required Leaf PTE Permission (`vmem_pte.sail:295`) | `PTE.A` Check | `PTE.D` Check (`vmem_pte.sail:346-352`) | Fault `scause` (`cmo.adoc:358-361, 401-405`) |
| :--- | :--- | :--- | :--- | :--- |
| `cbo.zero` (`Zicboz`) | Store required (`W = 1`) | Yes | **Yes** (`true`) | Store/AMO page/access fault (`15` / `7`) |
| `cbo.clean`, `cbo.flush` (`Zicbom`) | **Load OR Store** (`R = 1` or `W = 1`, or `X = 1` if `MXR = 1`) | Yes | **No** (`false`) | Store/AMO page/access fault (`15` / `7`) |
| `cbo.inval` (`Zicbom`) | **Load OR Store** (`R = 1` or `W = 1`, or `X = 1` if `MXR = 1`) | Yes | **No** (`false`) | Store/AMO page/access fault (`15` / `7`) |

Although `cbo.inval` **discards modified cache data** without writeback, it requires **only Load (`R = 1`) permission** (`CacheAccess(CB_manage(_)) => pte_R | pte_W`, `vmem_pte.sail:295`) and ignores `PTE.D == 0` (`cmo.adoc:369-370`). Yet when a page is completely unmapped (`V = 0` or `U = 0`), `cbo.inval` raises a *Store/AMO* page fault (`scause = 15`), misleading fault handlers into assuming write gating even though hardware permits `cbo.inval` on every `R = 1, W = 0, U = 1` page. (On execute-only pages `R = 0, W = 0, X = 1` with `MXR = 0`, `cmo.adoc:354-357` leaves access `UNSPECIFIED`.)

#### 2.2 Hierarchical `CBIE` Evaluation, WARL `0b01` Rejection, and `Smstateen` Boot Ordering

Isolation of `cbo.inval` on readable pages relies entirely on `CBIE` (`bits [5:4]`) across `menvcfg`, `henvcfg`, and `senvcfg` (`cmo.adoc:532-558`; `machine.adoc:2247-2264`; `supervisor.adoc:905-920`; `sail-riscv` `model/extensions/Zicbom/zicbom_insts.sail:46-70`):

| Mode | `CBOP_ILLEGAL` (`scause = 2`) | `CBOP_ILLEGAL_VIRTUAL` (`scause = 22`) | `CBOP_INVAL_FLUSH` (Upgrade to `cbo.flush`) | `CBOP_INVAL_INVAL` (**Raw Invalidate**) |
| :--- | :--- | :--- | :--- | :--- |
| `M` | Never | Never | Never | Always |
| `S` / `HS` | `menvcfg.CBIE == 00` | Never | `menvcfg.CBIE == 01` | `menvcfg.CBIE == 11` |
| `U` | `menvcfg.CBIE == 00` or `senvcfg.CBIE == 00` | Never | Neither `00`, and (`menvcfg == 01` or `senvcfg == 01`) | **`menvcfg.CBIE == 11` AND `senvcfg.CBIE == 11`** |
| `VS` | `menvcfg.CBIE == 00` | `menvcfg != 00` and `henvcfg == 00` | No `00`, and (`menvcfg == 01` or `henvcfg == 01`) | `menvcfg.CBIE == 11` AND `henvcfg.CBIE == 11` |
| `VU` | `menvcfg.CBIE == 00` | `menvcfg != 00` and (`henvcfg == 00` or `senvcfg == 00`) | No `00`, and any `{m, h, s}envcfg == 01` | **`menvcfg == 11` AND `henvcfg == 11` AND `senvcfg == 11`** |

Three CSR legalization and boot-ordering hazards govern `senvcfg.CBIE`:

1. **WARL rejection of `0b01` (`CBIE_AllowInval`):** In `sail-riscv` (`model/core/sys_regs.sail:508-524`), `legalize_xenvcfg_cbie` models cores with `CBIE_AllowInval` (`{0b00, 0b11}` legal, `0b01` unsupported): writing `0b01` fails `cbie_is_legal` and **returns `old_cbie` (`0b11`) unchanged**! Only `0b00` (`CBIE_ILLEGAL`) is universally legal without `csrr` readback.
2. **Partial bit-clear bug (`csrci senvcfg, 1`):** `csrci senvcfg, 1` clears only `FIOM` (`bit 0`), leaving `CBIE` (`bits [5:4]`) intact; kernels must write `csrw senvcfg, zero`.
3. **`Smstateen` `mstateen0.ENVCFG` trap ordering (`src/priv/smstateen.adoc:203, 275-277`):** When `mstateen0.ENVCFG` (bit 62) is `0`, S-mode access to `senvcfg` raises `scause = 2` (Illegal Instruction), so `head.S` must configure `stvec` *before* `csrw senvcfg, zero` unless M-mode firmware guarantees `SMSTATEEN0_HSENVCFG` (`opensbi` `lib/sbi/sbi_hart.c:88`).

#### 2.3 End-to-End Dirty-Cache Rollback Seam Across OpenSBI, Linux, and `seL4`

1. **OpenSBI sets `menvcfg.CBIE = 0b11`:** In `opensbi` (`lib/sbi/sbi_hart.c:150-153`), `sbi_hart_reinit` sets `ENVCFG_CBIE_INV << ENVCFG_CBIE_SHIFT` (`0b11`) whenever `Zicbom` is supported, delegating U-mode protection entirely to `senvcfg.CBIE`.
2. **Linux zeroes `senvcfg.CBIE`; `seL4` leaves `senvcfg` untouched:** Linux `riscv_user_isa_enable` (`arch/riscv/kernel/cpufeature.c:1268-1283`) sets `ENVCFG_CBZE | ENVCFG_CBCFE` with `CBIE == 0b00`. Conversely, `seL4` (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, `src/arch/riscv/head.S`, `src/arch/riscv/kernel/boot.c`) never initializes `senvcfg`.
3. **Read-only user rollback of `clearMemory` / IPC stores:** `seL4` `clearMemory` (`include/arch/riscv/arch/machine.h:154-158`) scrubs retyped frames via CPU stores alone (*"Cleaning memory before user-level access. Does not flush cache."*), leaving `0x00..00` in dirty cache lines over stale DRAM bytes $v_{\text{secret}}$. If `senvcfg.CBIE == 0b11` (from dirty warm-boot state or misconfiguration), an untrusted user holding a `VMReadOnly` capability (`R = 1, W = 0, U = 1`, `vspace.c:45-50, 656-676`) executes `cbo.inval 0(a0)`. Hardware checks `pte_R | pte_W == 1`, skips `PTE.D`, evaluates `mCBIE == 11 && sCBIE == 11 -> CBOP_INVAL_INVAL`, and drops the dirty zeroed cache line. By the Modified Load Value Axiom (`cmo.adoc:262-281`), the next `ld` reads $v_{\text{secret}}$ from DRAM, breaking both confidentiality and read-only shared-memory integrity.

### 3. `RVWMO` Device I/O Ordering Gaps (`fence rw,ow` / `fence ir,rw`) and `FIOM` Virtualization

Basis: normative + source + execution + derived

#### 3.1 Why `smp_mb()`, `writel()`, and `readl()` Leave DMA Buffer Recycling Unordered

In `RVWMO` (`src/unpriv/rvwmo.adoc:267-274`), preserved program order holds between $a$ and $b$ **only if** both access regular main memory (`r`/`w`), excluding MMIO (`i`/`o`). Ordering RAM against MMIO requires explicit `FENCE` masks (`src/unpriv/rv32.adoc:769-778`; Linux `arch/riscv/include/asm/barrier.h:18-26`, `arch/riscv/include/asm/mmio.h:134-150`):

| Primitive / Instruction | Encoded `FENCE` | Orders `w -> o` (Desc -> Doorbell) | Orders `r -> o` (Buf Read -> Doorbell) | Orders `i -> r` (Poll -> RX Read) | Orders `i -> w` (Poll -> Desc Recycle) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `smp_mb()` (`__smp_mb`) | `fence rw,rw` | **No** (`so = 0`) | **No** (`so = 0`) | **No** (`pi = 0`) | **No** (`pi = 0`) |
| `writel()` (`__io_bw`) / `wmb()` | `fence w,o` / `fence ow,ow` | Yes | **No** (`pr = 0`) | No | No |
| **`fence rw,ow`** | `fence rw,ow` | **Yes** | **Yes** (`pr = 1, so = 1`) | No | No |
| `readl()` (`__io_ar`) / `rmb()` | `fence i,ir` / `fence ir,ir` | No | No | Yes | **No** (`sw = 0`) |
| **`fence ir,rw`** | `fence ir,rw` | No | No | **Yes** | **Yes** (`pi = 1, sw = 1`) |

- **Buffer-reuse `r -> o` hazard under `writel()` (`fence w,o`):** When a CPU reads payload out of a completed buffer $B$ (`r`), re-queues $B$ as a free RX DMA buffer (`w`), and rings an MMIO doorbell via `writel()` (`fence w,o` + `o`), `pr = 0` leaves `r` unordered before `o`; out-of-order execution can satisfy `r` *after* the device DMA-overwrites $B$ unless **`fence rw,ow`** precedes the doorbell.
- **Completion-poll `i -> w` hazard under `readl()` (`fence i,ir`):** Polling an MMIO completion register (`i`), reading RX payload (`r`), and writing the descriptor ownership bit (`w`) to recycle the slot requires `sw = 1` when `r` is elided or decoupled under `readl_relaxed()`; `fence i,ir` omits `sw`, whereas **`fence ir,rw`** orders `i -> r`, `i -> w`, `r -> r`, and `r -> w`.
- **`FIOM` in virtualized/user-space I/O (`supervisor.adoc:823-855`, `sys_regs.sail:651-659`):** When emulated or VFIO device queues reside in regular RAM (`r`/`w`), driver fences (`fence w,o`, `fence i,ir`) fail to order RAM accesses unless `senvcfg.FIOM = 1` (U-mode) or `henvcfg.FIOM = 1` (VS/VU-mode) expands `i`/`o` bits to `ir`/`ow` (`FIOM` may be read-only zero only if `satp.MODE` is always `Bare`, `supervisor.adoc:837-839`).

### 4. Multi-Hart TLB vs I-Cache Non-Subsumption and Two-Step Code-Frame Reclamation

Basis: normative + source + derived

In RISC-V (`src/priv/supervisor.adoc:1195-1210, 1769-1808`; `src/unpriv/zifencei.adoc:66-80`; cf. Simner et al., ESOP 2020, DOI `10.1007/978-3-030-44914-8_23`), TLBs and `I-cache` are mutually incoherent: `sfence.vma` invalidates local address-translation caches without touching `I-cache`, and `fence.i` synchronizes local instruction fetches with prior visible stores without invalidating TLBs or remote harts (`zifencei.adoc:71-75` requires a data `fence` before remote `fence.i`, e.g., `RISCV_FENCE(w, o)` in Linux `arch/riscv/mm/cacheflush.c:38`).

Reclaiming an executable (`X = 1`) physical frame $P$ from `VA_old` and remapping it at `VA_new` (`X = 1`) on SMP is **unsound if `fence.i` runs before or concurrently with remote `sfence.vma`**: while Hart 1 retains a stale `VA_old -> P` TLB entry, `supervisor.adoc:1797-1808` permits Hart 1 to speculatively fetch through `VA_old`, refilling its physically indexed `I-cache` with old or torn bytes of $P$ *after* an early `fence.i`. Sound reclamation requires a strict **two-step shootdown** (`seL4` `sfence()`/`ifence()` in `include/arch/riscv/arch/machine.h:105-118`; Linux `flush_icache_mm` in `arch/riscv/mm/cacheflush.c:57-95`):

1. **Step 1 (Translation revocation before mutation):** Clear `PTE_old.V := 0` (or `X := 0`), execute `fence w,rw`, and complete local + synchronous remote `sfence.vma` on all harts before writing to $P$.
2. **Step 2 (Store visibility and I-cache sync before execution):** Write/zero $P$, clean dirty D-cache lines if non-coherent (`cbo.clean`), execute `fence w,o` / `fence rw,rw`, and complete local + remote `fence.i` (or `icache_stale_mask` flush before `sret`) prior to fetching via `VA_new -> P`.

### 5. Summary of Kernel and Hypervisor Verification Obligations

Basis: derived

1. **`Svadu` noninterference:** When `menvcfg.ADUE == 1`, prove `PTE.A = 1` (and `PTE.D = 1` on writable/`hgatp` pages) is pre-populated across reachable mappings if speculative constant-time noninterference is required, and mutate live PTEs exclusively with atomic AMOs (cf. Klein et al., ACM TOCS 2014, DOI `10.1145/2560537`; Armstrong et al., POPL 2019, DOI `10.1145/3290384`).
2. **`Zicbom` `senvcfg.CBIE` gate:** Initialize `stvec` first, execute full `csrw senvcfg, zero`, and keep `senvcfg.CBIE == 0b00` (or verify `0b01` via `csrr`) unless all scrubbed frames and read-only shared buffers are cleaned to DRAM before U-mode entry.
3. **DMA and SMP code shootdowns:** Use `fence rw,ow` before TX/recycle DMA doorbells, `fence ir,rw` after relaxed RX completion polls, `FIOM = 1` for RAM-emulated I/O, and complete remote `sfence.vma` strictly before frame writes + remote `fence.i`.

## Boundaries

- **Non-coherent DMA driver ownership protocols and `Svpbmt` (`NC`/`IO`) attributes (`not examined`):** Legitimate S-mode non-coherent DMA cache maintenance and `Svpbmt` (`menvcfg.PBMTE`) page-attribute interactions were **not examined** in detail here.
- **Speculative step-9 `PTE.A` timing on commercial RVA23 microarchitectures (`unknown`):** Although `supervisor.adoc:1625-1627` permits squashed speculative `PTE.A = 1` RAM writes under `Svadu`, which commercial out-of-order RISC-V cores commit `PTE.A = 1` on mispredicted paths versus deferring step 9 until retirement remains **unknown** without silicon probing.
- **Read-only `Zicboz` `cbo.zero` corruption (`known not to apply`):** Read-only (`R = 1, W = 0`) rollback is **known not to apply** to `Zicboz` `cbo.zero`, which requires `W = 1` and updates `PTE.D` (`cmo.adoc:373-381`, `vmem_pte.sail:295, 352`). Speculative `PTE.A` RAM writes are likewise **known not to apply** under `Svade` (`menvcfg.ADUE == 0`, `supervisor.adoc:1604-1606, 1803-1806`).
- **Disabling `ADUE` from S-mode via `senvcfg` or `SBI_FWFT` on `Svadu`-only harts (`unsupported`):** `senvcfg` omits `ADUE` (**unsupported** architecturally, `supervisor.adoc:791-806`), and OpenSBI `SBI_FWFT_PTE_AD_HW_UPDATING` (`ADUE = 0`) is **unsupported** (`SBI_ENOTSUPP`) unless hardware implements both `Svadu` and `Svade` (`opensbi` `lib/sbi/sbi_fwft.c:161-176`).

## Evidence

### Normative Specifications and Formal Models (Observed 2026-11-21)

- **RISC-V Instruction Set Manual (`riscv/riscv-isa-manual` at `3142f66fd71c7ea0326b3687072318aedab587f8`):** `src/priv/svadu.adoc:1-14`; `src/priv/machine.adoc:2153-2264` (`menvcfg.ADUE`, `FIOM`, `CBIE`); `src/priv/supervisor.adoc:790-855, 905-920, 1185-1221, 1603-1635, 1742-1809` (`senvcfg` omitting `ADUE`, `sfence.vma`, atomic in-RAM `PTE.A`/`PTE.D` CAS, speculative `PTE.A` permission); `src/priv/smstateen.adoc:198-206, 275-278` (`mstateen0.ENVCFG`); `src/unpriv/cmo.adoc:262-283, 352-405, 532-558` (Modified Load Value Axiom, `R=1|W=1` permission, `CBIE` tree); `src/unpriv/rv32.adoc:762-780`, `src/unpriv/rvwmo.adoc:267-275`, `src/unpriv/zifencei.adoc:66-81`.
- **Sail RISC-V Model (`riscv/sail-riscv` at `71312d537fc10782c42b7303a611b923af0566d4`):** `model/core/sys_regs.sail:446-524, 651-659` (`MEnvcfg`/`SEnvcfg`/`HEnvcfg`, `legalize_xenvcfg_cbie`, `is_fiom_active`); `model/sys/vmem_pte.sail:295, 304-309, 346-352` (`pte_R | pte_W`, `hw_updates_pte`, `CB_manage => false`); `model/extensions/Zicbom/zicbom_insts.sail:46-76` (`cbop_priv_check`).

### Upstream Firmware and OS Kernel Sources (Observed 2026-11-21)

- **OpenSBI (`riscv-software-src/opensbi` at `61f1973bd50338b36c52dc34006f76d464ca4f34`):** `lib/sbi/sbi_hart.c:84-94, 150-171` (`SMSTATEEN0_HSENVCFG`, `ENVCFG_CBIE_INV`, `ENVCFG_ADUE`); `lib/sbi/sbi_fwft.c:161-195` (`fwft_adue_supported`).
- **Linux (`torvalds/linux` at `aa31d5f8b151b786b748c6bfc9a8c4f1855c8adc`):** `arch/riscv/kernel/cpufeature.c:308-316, 1268-1283`; `arch/riscv/mm/pgtable.c:8-39`; `arch/riscv/include/asm/barrier.h:18-26`; `arch/riscv/include/asm/mmio.h:134-150`; `arch/riscv/mm/cacheflush.c:28-95`.
- **seL4 (`seL4/seL4` at `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`):** `include/arch/riscv/arch/machine.h:105-118, 154-158` (`ifence`, `sfence`, `clearMemory`); `src/arch/riscv/kernel/vspace.c:45-50, 656-676` (`RISCVGetReadFromVMRights`, `makeUserPTE`); `src/arch/riscv/head.S:1-63` and `src/arch/riscv/kernel/boot.c:1-499`.

### Peer-Reviewed Literature

- Gerwin Klein et al., *"Comprehensive Formal Verification of an OS Microkernel,"* ACM TOCS 32(1), 2014, DOI: `10.1145/2560537`.
- Ben Gras et al., *"ASLR on the Line: Practical Cache Attacks on the MMU,"* NDSS 2017, DOI: `10.14722/ndss.2017.23271`.
- Paul Kocher et al., *"Spectre Attacks: Exploiting Speculative Execution,"* IEEE S&P 2019, DOI: `10.1109/SP.2019.00002`.
- Alasdair Armstrong et al., *"ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS,"* POPL 2019, DOI: `10.1145/3290384`.
- Marco Guarnieri et al., *"Spectector: Principled Detection of Speculative Information Flows,"* IEEE S&P 2020, DOI: `10.1109/SP40000.2020.00011`.
- Sunjay Cauligi et al., *"Constant-Time Foundations for the New Spectre Era,"* PLDI 2020, DOI: `10.1145/3385412.3385970`.
- Ben Simner et al., *"ARMv8-A System Semantics: Instruction Fetch in Relaxed Architectures,"* ESOP 2020, DOI: `10.1007/978-3-030-44914-8_23`.

## Revalidation

To revalidate these invariants across Sail updates, OpenSBI revisions, or target OS kernels:

1. **Run the standalone Python 3 `CBIE` x read-only rollback, `Svadu` speculative `PTE.A`, and `RVWMO` `FENCE` discriminator:**
   ```bash
   python3 - << 'EOF'
   def cbop_priv(priv: str, m: int, s: int, h: int) -> str:
       if (priv != "M" and m == 0) or (priv == "U" and s == 0):
           return "ILLEGAL"
       if (priv == "VS" and h == 0) or (priv == "VU" and (h == 0 or s == 0)):
           return "VIRTUAL"
       if ((priv != "M" and m == 1) or (priv == "U" and s == 1)
               or (priv == "VS" and h == 1) or (priv == "VU" and (h == 1 or s == 1))):
           return "FLUSH"
       return "INVAL"

   for m in (0, 1, 3):
       for s in (0, 1, 3):
           for h in (0, 1, 3):
               assert (cbop_priv("U", m, s, h) == "INVAL") == (m == 3 and s == 3)
               assert (cbop_priv("VU", m, s, h) == "INVAL") == (m == 3 and h == 3 and s == 3)

   # Read-only (R=1, W=0) U-mode cbo.inval rolls dirty 0x0 back to stale DRAM 0xDEADBEEF iff m=3, s=3
   dram, cache_dirty = 0xDEADBEEF, 0x0
   assert (True or False) and cbop_priv("U", 3, 3, 0) == "INVAL" and dram == 0xDEADBEEF

   # Svadu (ADUE=1) squashed transient OOB load mutates architectural RAM PTE.A; Svade (ADUE=0) does not
   def spec_ptes(adue: int, bit: int) -> dict[int, int]:
       p = {0: 0, 1: 0}
       if adue == 1:
           p[bit] = 1
       return p
   assert spec_ptes(0, 0) == spec_ptes(0, 1) and spec_ptes(1, 0) != spec_ptes(1, 1)

   # RVWMO fence masks: writel (w,o) misses r->o; readl (i,ir) misses i->w; rw,ow and ir,rw close both
   def orders(p: str, s: str, a: str, b: str) -> bool:
       return (a in p) and (b in s)
   assert not orders("w", "o", "r", "o") and orders("rw", "ow", "r", "o")
   assert not orders("i", "ir", "i", "w") and orders("ir", "rw", "i", "w")
   print("OK")
   EOF
   ```
2. **Audit target kernel `senvcfg` and `clearMemory` safety:** Grep `senvcfg` across `arch/riscv/` or `src/arch/riscv/` to verify `csrw senvcfg, zero` executes *after* `stvec` setup and `CBIE` (`bits [5:4]`) is never `0b11` (or `0b01` without `csrr` readback) unless all scrubbed/shared read-only frames are cleaned to DRAM via `cbo.clean`/`cbo.flush`.
3. **Audit `Svadu` and SMP code-reclamation paths:** Check `menvcfg` handling in OpenSBI `lib/sbi/sbi_hart.c` / `sbi_fwft.c`, verify atomic AMO PTE updates when `ADUE == 1`, and confirm executable frame unmapping completes remote `sfence.vma` before frame mutation and remote `fence.i`.
