# Supervisor Environment CSR Reset Contracts Across Firmware Handoffs and Svade-vs-Svadu Page-Table-Walk Correspondence

## Summary

Bootstrapping a verified RISC-V supervisor-mode (S-mode) OS kernel or microkernel from machine-mode (M-mode) runtime firmware exposes two coupled specification seams invisible when proofs assume `0`-initialized CSRs and static page tables:

1. **Privilege-Tier Split Across `menvcfg`, `henvcfg`, and `senvcfg`, Plus Unspecified Hardware Reset:** Under the RISC-V Privileged Architecture (`#norm:rst_other_state_unspec`), hardware reset leaves `menvcfg`, `senvcfg`, `scounteren`, `stvec`, and `satp` **UNSPECIFIED** (bounded only to legal `WARL` encodings, `#norm:warl_rst`). Neither `ADUE` (bit 61, toggling `Svadu` vs. `Svade`) nor `PBMTE` (bit 62, enabling `Svpbmt`) nor `STCE` (bit 63) exists in `senvcfg` (`0x10A`): bits `[63:34]` of `senvcfg` are `WPRI` read-only zero, confining `ADUE` and `PBMTE` to M-mode `menvcfg` (`0x30A`) and hypervisor `henvcfg` (`0x60A`), controllable from S-mode solely via the SBI Firmware Features extension (`FWFT`, `EID #0x46574654`). **Basis: normative, source.**
2. **Firmware Handoff Gaps Before First `SRET` to U-Mode:** SBI `HSM` `sbi_hart_start` guarantees only `satp = 0`, `sstatus.SIE = 0`, `a0 = hartid`, and `a1 = opaque`. OpenSBI `mstatus_init` sets `scounteren = 0x02` (`TM` bit only), sets `mstateen0.ENVCFG = 1`, and enables `menvcfg` `CBZE`/`CBCFE`/`CBIE = 0b11` (`CBO.INVAL`), yet **never writes `senvcfg`**. Kernels that clear `scounteren` while omitting `senvcfg` (or gating `csrw senvcfg` behind firmware extension probes) expose U-mode on first `SRET` to unspecified hardware reset bits: destructive `CBO.INVAL` drops on shared read-only frames (`CBIE = 0b11`), pointer masking (`PMM != 0`), or widened I/O fences (`FIOM = 1`). Conversely, executing unconditional `csrw senvcfg, x0` on pre-`Sm1p12` silicon or when `mstateen0.ENVCFG == 0` raises an illegal-instruction trap at boot. **Basis: normative, source, execution.**
3. **Deterministic `Svade` Faults vs. Nondeterministic `Svadu` Walks:** Under `Svade` (`menvcfg.ADUE = 0`, OpenSBI's mandatory default when both `Svade` and `Svadu` exist), implicit page-table walks (PTWs) are strictly read-only and raise deterministic page faults whenever leaf `A = 0` or store `D = 0`. Under `Svadu` (`menvcfg.ADUE = 1`), hardware atomically compares-and-sets `A`/`D` bits in memory: **speculative loads may set `A = 1` without architectural retirement**, whereas explicit-store `D = 1` updates must be exact and globally ordered before the store. Non-atomic PTE mutations (`READ_ONCE` + `atomic_long_set` in Linux's `ptep_set_wrprotect`) lose concurrent hardware `D = 1` updates, whereas `xchg` (`amoswap.d` in `ptep_get_and_clear`) and `test_and_clear_bit` (`amoand` in `ptep_test_and_clear_young`) preserve dirty bits. Pre-populating `A = 1 ∧ D = 1` on all valid leaf PTEs (`seL4` `makeUserPTE`) collapses `Svadu` and `Svade` into identical read-only translation semantics across TLB misses and Sail's `translate_TLB_hit`. **Basis: normative, source, execution, derived.**
4. **Boot and PTW Equivalence Contracts:** Sound verification requires a gated `FirstSretEnvContract` (`stvec`, `scounteren`, capability-checked `senvcfg = 0`, plus `SFENCE.VMA x0, x0` after `FWFT` `ADUE` transitions) paired with either eager `A = 1 ∧ D = 1` leaves or AMO-linearized PTE reclamation. **Basis: derived, source.**

## Applicability

This synthesis governs 32-bit and 64-bit RISC-V supervisor-mode kernels and hypervisors over M-mode SBI firmware across Privileged Architecture versions `1.10`–`1.13` (`Sv32`–`Sv57`, `Zicbom`, `Zicboz`, `Zicfilp`, `Zicfiss`, `Ssnpm`, `Smstateen`, `Svpbmt`, `Svade`, and `Svadu`). **Basis: normative, source.**

Within the corpus, this study extends adjacent virtual-memory and cache reports without duplication:
- [`hardware-asid-width-discovery-conditional-satp-switch-fencing-and-boot-pt-barriers`](../hardware-asid-width-discovery-conditional-satp-switch-fencing-and-boot-pt-barriers/REPORT.md) analyzes `satp` `ASIDLEN` discovery, ASID rollover, and pre-`satp` store barriers; here `satp` appears solely via its `HSM` reset state (`satp = 0`) and `ADUE`/`PBMTE` `SFENCE.VMA` invalidation coupling.
- [`mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement`](../mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement/REPORT.md) and [`isa-page-table-tlb-coherence-sail-trap-contracts-and-toctou-dma-fetch-oracles`](../isa-page-table-tlb-coherence-sail-trap-contracts-and-toctou-dma-fetch-oracles/REPORT.md) cover non-leaf PWCs, SMP shootdowns, and `fence.i`; here we isolate Step-9 `Svade`/`Svadu` A/D updates and concurrent PTE races.
- [`non-coherent-dma-cache-maintenance-zicbom-granules-and-adjacent-field-tearing-hazards`](../non-coherent-dma-cache-maintenance-zicbom-granules-and-adjacent-field-tearing-hazards/REPORT.md) analyzes DMA `Zicbom` granules; here `CBIE`/`CBCFE`/`CBZE` are evaluated as U-mode boot-reset exposure vectors. **Basis: documentation.**

## Findings

### 1. Normative CSR Reset Semantics and the `menvcfg` vs. `senvcfg` Bitfield Split

**Basis: normative, source, execution.**

`riscv/riscv-isa-manual` (`src/priv/machine.adoc:2770–2790`) specifies a minimal hardware reset state: M-mode privilege (`#norm:m_mode_priv_at_reset`), `mstatus.{MIE,MPRV,MBE} = 0`, `mstatus.MDT = 1` (`L460`), `hgatp.MODE = vsatp.MODE = 0` (`L2784–2785`), `mseccfg.{MLPE,MML,MMWP,RLB} = 0`, and legal `WARL` fields (`#norm:warl_rst`), while **"All other hart state is UNSPECIFIED"** (`#norm:rst_other_state_unspec`, `L2789`). Thus hardware reset leaves `menvcfg`, `henvcfg`, `senvcfg`, `mcounteren`, `scounteren`, `stvec`, and `satp` holding arbitrary legal `WARL` values. Cross-checking `machine.adoc` (`L1556–1618`, `L2128–2321`), `supervisor.adoc` (`L317–364`, `L500–530`, `L782–963`), `smstateen.adoc` (`L275–278`), and `riscv/sail-riscv` (`model/core/sys_regs.sail:446–647`) gives the exact delegation map:

| CSR & Index | Width | Key Bitfields | Controls Modes | Reset & Access Constraints |
| :--- | :--- | :--- | :--- | :--- |
| `menvcfg` / `menvcfgh` (`0x30A`/`0x31A`) | 64-bit (`32+32` RV32) | `STCE[63]`, `PBMTE[62]`, `ADUE[61]`, `CDE[60]`, `DTE[59]`, `PMM[33:32]`, `CBZE[7]`, `CBCFE[6]`, `CBIE[5:4]`, `SSE[3]`, `LPE[2]`, `FIOM[0]` | Modes `< M` | Mandatory with U-mode (`L2316`); **UNSPECIFIED** at reset; `ADUE`/`PBMTE`/`STCE` live only in `menvcfg`/`henvcfg` |
| `henvcfg` / `henvcfgh` (`0x60A`/`0x61A`) | 64-bit (`32+32` RV32) | Same bits minus `CDE` (`sys_regs.sail:494–506`) | `VS`/`VU` modes | **UNSPECIFIED** at reset; bits `{63,62,61,59,3}` RO-`0` if `menvcfg` clears them (`sys_regs.sail:592–599`); gated by `mstateen0.ENVCFG` |
| `senvcfg` (`0x10A`) | `SXLEN` (`32` or `64`) | `PMM[33:32]` (RV64), `UKTE[8]`, `CBZE[7]`, `CBCFE[6]`, `CBIE[5:4]`, `SSE[3]`, `LPE[2]`, `FIOM[0]`; **`[63:34]` `WPRI`** | **`U`/`VU`-mode only** | **UNSPECIFIED** at reset; illegal instruction in S-mode if Priv `< 1.12` (no envcfg extensions) or `mstateen0.ENVCFG == 0` |
| `mcounteren` (`0x306`) / `scounteren` (`0x106`) | 32-bit | `HPM31..3[31:3]`, `IR[2]`, `TM[1]`, `CY[0]` | S/U/`stimecmp` vs. U-mode | **UNSPECIFIED** at reset; U-mode access needs **both** `mcounteren[i] = 1` and `scounteren[i] = 1` (`supervisor.adoc:525–528`) |
| `stvec` (`0x105`) | `SXLEN` | `BASE[SXLEN-1:2]`, `MODE[1:0]` (`0` Direct, `1` Vectored) | S-mode trap vector | **UNSPECIFIED** at reset; `MODE >= 2` reserved (`supervisor.adoc:339–352`) |
| `satp` (`0x180`) | `SXLEN` | `MODE`, `ASID`, `PPN` | S/U translation | Hardware reset **UNSPECIFIED** (`machine.adoc:2789`; SBI `HSM` sets `0`) |

Three normative rules govern this boundary:
1. **Writing `senvcfg = 0` Cannot Clear `ADUE` or `PBMTE`:** In `supervisor.adoc:791–821` and `sys_regs.sail:475–492, 545–564`, `senvcfg[63:34]` is `WPRI` (`legalize_senvcfg` masks out bits outside `{33:32, 8:2, 0}`). S-mode cannot alter `ADUE` (bit 61) or `PBMTE` (bit 62) via `senvcfg`; it depends on M-mode `menvcfg` initialization or SBI v3.0 `FWFT` (`ext-firmware-features.adoc:21–22, 91–96`).
2. **`CBO.INVAL` Destruction Without Write Permission:** U-mode `Zicbom`/`Zicboz` requires **both** `menvcfg` and `senvcfg` enablement (`supervisor.adoc:891–920`). Crucially, Sail's `vmem_pte.sail:295` specifies `CacheAccess(CB_manage(_)) => pte_R | pte_W`: `CBO.INVAL` requires **only read permission** (`pte_R`), not write permission! Whenever `menvcfg.CBIE == 0b11` and reset leaves `senvcfg.CBIE == 0b11` (`#norm:cbo-inval_s_mode_inval_enc`), an unprivileged reader sharing physical pages with the kernel or DMA can silently drop dirty cache lines unless the kernel clears `senvcfg.CBIE` to `0b00` (or `menvcfg.CBIE == 0b01` forces flush).
3. **`Smstateen` Trapping vs. Immediate `PMM`/`FIOM` Side Effects:** Under `Smstateen` (`smstateen.adoc:275–277`, `#norm:mstateen0_envcfg_op`), `mstateen0.ENVCFG = 0` traps S-mode reads/writes of `senvcfg` as illegal instructions. Meanwhile, `senvcfg.PMM` (`Ssnpm` pointer masking, `supervisor.adoc:928–930`, `#norm:senvcfg_pmm_immediate`) activates **immediately without `SFENCE.VMA`**, truncating upper bits (`PMLEN = 7` or `16`) of U-mode pointers on first `SRET` if nonzero at reset, while `FIOM = 1` widens every U-mode I/O fence/AMO (`supervisor.adoc:823–855`).

### 2. M-Mode Firmware Handoff Contracts vs. S-Mode Kernel Boot Gaps Before First `SRET`

**Basis: normative, source, execution.**

Comparing `riscv-sbi-doc` (`8a545eff`), `opensbi` (`61f1973b`), `linux` (`5f22fb20`), `seL4` (`08c7e5fd`), `l4v` (`b0fe7693`), and `xv6-riscv` (`fa2ddcb7`) exposes a wide contract gap between firmware handoff guarantees and kernel startup assumptions:

1. **Normative SBI `HSM` Contract (`ext-hsm.adoc:92–102, 232–242`):** Both `sbi_hart_start` and non-retentive resume guarantee **only** `satp = 0`, `sstatus.SIE = 0`, `a0 = hartid`, `a1 = opaque`, leaving *"All other registers remain in an undefined state."* Only SBI v3.0 `FWFT` local features (`ext-firmware-features.adoc:66–103`) define zero reset values (`LANDING_PAD`, `SHADOW_STACK`, `DOUBLE_TRAP`, `PTE_AD_HW_UPDATING`, `POINTER_MASKING_PMLEN`).
2. **OpenSBI `mstatus_init` (`lib/sbi/sbi_hart.c:27–186`):** OpenSBI writes `CSR_SCOUNTEREN = 0x02` (`L46–48`, exposing `time` to U-mode), `CSR_MCOUNTEREN = -1` (`L56`), `CSR_MSTATEEN0 |= SMSTATEEN0_HSENVCFG` (`L84–115`), `CSR_SATP = 0` (`L184–185`), and `CSR_MENVCFG` (`L132–172`: clearing `ADUE` and `DTE`, setting `CBZE`, `CBCFE`, **`CBIE = 0b11` (`ENVCFG_CBIE_INV`, `L152–153`)**, `PBMTE`, `STCE`, `CDE`, and setting `ADUE = 1` **only when `!SVADE && SVADU`**, `L166–167`). **OpenSBI never writes `CSR_SENVCFG`**, passing hardware's unspecified reset `senvcfg` straight to S-mode.
3. **Kernel Boot CSR Hygiene Matrix:**

| Component | `stvec` | `satp` | `scounteren` | `senvcfg` | Boot Contract Failure / Reliance |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **OpenSBI `mstatus_init`** (`sbi_hart.c:27–186`) | Unset | `0` | `0x02` (`TM`) | **Untouched** | Sets `menvcfg.CBIE = 0b11`, `CBZE`, `CBCFE`, `mstateen0.ENVCFG`; exposes reset `senvcfg` to S/U-mode |
| **Linux RISC-V** (`head.S:84–247`, `cpufeature.c:480–663, 1268–1283`, `switch_to.h:74–90`, `process.c:203–206`) | VA vector (`L84`) | Early + `swapper_pg_dir` + `sfence.vma` (`L105–122`) | Explicit `0x2` (`L136, 247`) | `riscv_user_isa_enable()` sets `CBZE`/`CBCFE` only; `__switch_to_envcfg` (`ALTERNATIVE`) gated on `XLINUXENVCFG` | Sound **only** when DTB/ACPI populates `xlinuxenvcfg`; if `zicbom`/`zicboz`/`smnpm`/`ssnpm`/`zicfilp`/`zicfiss` are absent, `__switch_to_envcfg` becomes `nop` and reset `senvcfg` persists! |
| **seL4 RISC-V** (`head.S:23–63`, `boot.c:126–143`, `l4v` `MachineOps.thy:198–225`) | `write_stvec(trap_entry)` (`L131`) | `activate_kernel_vspace()` (`L129`) | **Omitted** | **Omitted** (`MachineOps.thy` lacks `senvcfg`/`scounteren`) | Leaves `scounteren = 0x02` from OpenSBI (`rdtime` open) and hardware reset `senvcfg` intact across first `SRET` (`reval_senvcfg_svade.py`: 3/9 legal states allow destructive `CBO.INVAL`; 6/9 enable `PMM`) |
| **xv6-riscv** (`start.c:15–66`, `riscv.h:213–230`) | M-mode `mret` to `main` | `w_satp(0)` (`L28`) | **Omitted** | **Omitted** (M-mode boot) | `w_menvcfg(r_menvcfg() \| MENVCFG_ADUE)` (`L41`) & `\| MENVCFG_STCE` (`L59`) RMW-preserve unspecified reset bits in `menvcfg` |

Two complementary hazards follow (`Basis: normative, source, execution`):
- **Silent U-Mode `CBO.INVAL` / `PMM` Exposure:** Kernels writing `scounteren` (or relying on OpenSBI's `0x02`) while omitting `senvcfg` leak destructive `CBO.INVAL` (`CBIE = 0b11`) and `PMM` pointer truncation on first `SRET` whenever reset leaves `senvcfg` nonzero.
- **Unconditional `csrw senvcfg, x0` Boot Traps:** Conversely, executing `csrw senvcfg, x0` unconditionally traps (`scause = 2`) on Priv `< 1.12` harts without envcfg extensions or when `mstateen0.ENVCFG == 0`. Kernel boot code must gate `csrw senvcfg` via extension detection (`XLINUXENVCFG` in Linux `cpufeature.c:481–488`) or a guarded trap-handling probe (matching OpenSBI's `csr_read_allowed(CSR_MENVCFG, &trap)` at `sbi_hart.c:627, 639`).

### 3. Deterministic `Svade` Faults vs. Nondeterministic `Svadu` Walks and PTE Races

**Basis: normative, source, execution, derived.**

`supervisor.adoc` (`L1596–1690`, `L1717–1770`) and Sail (`vmem.sail:95–120, 394–455`; `vmem_pte.sail:295–372`) formalize two contrasting Step-9 PTE update regimes selected by `menvcfg.ADUE` (and `henvcfg.ADUE` in virtualized execution), constrained to be uniform across harts (`#norm:pte_ad_scheme_uniform`):

| Dimension | `Svade` (`menvcfg.ADUE = 0`) | `Svadu` (`menvcfg.ADUE = 1`) |
| :--- | :--- | :--- |
| **Normative Authority** | `#norm:Svade_access_ad_bit_clear` (`supervisor.adoc:1604–1606, 1741`) | `svadu.adoc:6–13`; `supervisor.adoc:1608–1652, 1742–1749` |
| **PTW Memory Side Effects** | **Strictly read-only** | Atomic compare-and-set of `A`/`D` into RAM (`_RsrvEventual_` PMA, `L1651`) |
| **Leaf `A = 0` Behavior** | Deterministic page fault (`PTW_PTE_Needs_Update`, `vmem.sail:117`) | Hardware sets `A = 1`; **speculative loads may set `A = 1` without retirement (`L1625–1627`)** |
| **Leaf `D = 0` Store / `CBO.ZERO`** | Deterministic page fault (`vmem_pte.sail:327, 352`) | Hardware sets `D = 1` (`A = 1`); **explicit-store `D` must be exact (non-speculative, `L1628–1630`)** and ordered before the store (`L1646–1648`) |
| **`CBO.CLEAN`/`FLUSH`/`INVAL`** | Checks `A = 1` (`pte_R \| pte_W`), **ignores `D`** (`vmem_pte.sail:295, 346`) | Sets `A = 1` if `0`, **never checks or sets `D`** |
| **Prefetch (`prefetch.{r,w,i}`)** | Neither checks nor sets `A`/`D` (`L357, 362`) | Neither checks nor sets `A`/`D` |
| **Sail `translate_TLB_hit` (`vmem.sail:394–413`)** | Faults if cached TLB PTE has `A = 0` or store sees `D = 0` | Writes updated PTE to RAM (`ent.pteAddr`) **and** updates TLB entry (`L404`) |
| **Runtime `ADUE` Mutation** | Requires `SFENCE.VMA x0, x0` (`#norm:menvcfg_adue_fence`, `machine.adoc:2209–2211`; `sbi_fwft.c:182–187`) | Same (`SFENCE.VMA x0, x0` + `HFENCE.GVMA` if `H` present) |

Four subtle verification gaps arise across specification, Sail, and kernel PTE code:
1. **Sail Sequential `write_pte` vs. Hardware Atomic Compare-and-Set:** `supervisor.adoc:1745–1749` requires Step 9 to compare the walked `pte` against RAM and restart at Step 2 (`L1749`) if concurrent software mutated the PTE (`V: 1 -> 0` or `W: 1 -> 0`). Sail's single-hart `update_and_write_pte` (`vmem.sail:95–120`) writes `write_pte` directly (`L112`) without re-comparing RAM (and `vmem_pte.sail:309` defaults to hardware updating when neither `Svadu` nor `Svade` is set!). Multi-hart proofs must model Step 9 using the ISA's atomic compare-and-set semantics rather than Sail's unconditional store.
2. **Linux `ptep_set_wrprotect` Lost-`D` Race Under `Svadu`:** In `torvalds/linux`, `ptep_get_and_clear` (`pgtable.h:664–678`) uses `xchg(&ptep->pte, 0)` (`amoswap.d`) and `ptep_test_and_clear_young` (`pgtable.c:32–38`) uses `test_and_clear_bit` (`amoand`), both preserving concurrent `Svadu` updates. In contrast, **`ptep_set_wrprotect` (`pgtable.h:681–693`) executes a non-atomic `READ_ONCE(*ptep)` (`L684`) followed by `atomic_long_set(..., (pte_val(read_pte) & ~_PAGE_WRITE) | _PAGE_READ)` (`L691–692`)**. Under `ADUE = 1`, a remote hart's concurrent store atomically sets `D = 1` and modifies physical memory between `L684` and `L691`, after which `atomic_long_set` overwrites `D` back to `0` (`W = 0, D = 0`)! Linux masks this in practice because `riscv_ext_svadu_validate` (`cpufeature.c:308–316`) disables `SVADU` whenever `SVADE` is present (and OpenSBI defaults `ADUE = 0`), whereas kernels enabling `ADUE = 1` without `amoand` lose dirty pages.
3. **Speculative `A = 1` Invalidation:** Because `supervisor.adoc:1625–1627` permits speculative walkers and prefetchers to set `A = 1` under `Svadu`, `pte.A == 1` does not witness an architectural read/fetch; moreover, permission upgrades (`ptep_set_access_flags`, `pgtable.c:12–21`) require `flush_tlb_page` unless `Svvptc` guarantees invalid/faulting PTEs are never cached.
4. **Eager `A = 1 ∧ D = 1` Collapse (`seL4` Strategy):** `seL4`'s `makeUserPTE` (`vspace.c:656–675`) and `map_it_frame_cap` (`L209–220`) set `A = 1` and `D = 1` on every valid leaf PTE. In `vmem_pte.sail:312–371`, `A = 1 ∧ D = 1` forces `update_a = false` and `update_d = false`, making `update_PTE_Bits` return `None()` across all access types and collapsing `Svadu` into `Svade` (`reval_senvcfg_svade.py`: identical outputs on all non-speculative/speculative read/write combinations).

### 4. Mechanizable Boot Handoff and `Svade`/`Svadu` Refinement Obligations

**Basis: derived, source.**

The self-contained Lean 4 module below formalizes the gated boot contract `FirstSretEnvContract` and proves `safe_sret_blocks_umode_cbie_and_pmm` plus `eager_ad_collapses_svade_svadu` with zero custom axioms:

```lean
namespace RiscvBootAndAdue

structure HardwareResetCaps where
  priv112OrEnvcfg : Bool
  smstateen       : Bool
  mstateen0Envcfg : Bool

structure CsrState where
  satp       : Nat
  sstatusSie : Bool
  stvec      : Nat
  scounteren : Nat
  menvcfg    : Nat
  senvcfg    : Nat

def SbiHsmEntryPrecondition (s : CsrState) : Prop :=
  s.satp = 0 ∧ s.sstatusSie = false

def maskBit (v bit : Nat) : Bool := ((v >>> bit) &&& 1) = 1
def cbieField (v : Nat) : Nat := (v >>> 4) &&& 3
def pmmField (v : Nat) : Nat := (v >>> 32) &&& 3

def FirstSretEnvContract (caps : HardwareResetCaps) (s : CsrState) : Prop :=
  s.stvec ≠ 0 ∧
  (s.scounteren &&& 0xFFFFFFFD) = 0 ∧
  ((caps.priv112OrEnvcfg && (!caps.smstateen || caps.mstateen0Envcfg)) = true → s.senvcfg = 0)

theorem safe_sret_blocks_umode_cbie_and_pmm
    (caps : HardwareResetCaps) (s : CsrState)
    (hAcc : (caps.priv112OrEnvcfg && (!caps.smstateen || caps.mstateen0Envcfg)) = true)
    (hContract : FirstSretEnvContract caps s) :
    cbieField s.senvcfg = 0 ∧ pmmField s.senvcfg = 0 ∧ maskBit s.senvcfg 0 = false := by
  have hZero : s.senvcfg = 0 := hContract.2.2 hAcc
  simp [cbieField, pmmField, maskBit, hZero]

structure LeafPte where
  valid : Bool; read : Bool; write : Bool; exec : Bool; accessed : Bool; dirty : Bool
  deriving DecidableEq

inductive AccessKind where | load | store | cbManage | cbZero | prefetch deriving DecidableEq
inductive PtwStepResult where | ok (nextPte : LeafPte) | fault deriving DecidableEq

def evalStep9 (adue : Bool) (acc : AccessKind) (pte : LeafPte) : PtwStepResult :=
  if !pte.valid then .fault
  else
    let permOk := match acc with
      | .load => pte.read | .store => pte.write
      | .cbManage => pte.read || pte.write | .cbZero => pte.write
      | .prefetch => pte.read || pte.write || pte.exec
    if !permOk then .fault
    else if acc = .prefetch then .ok pte
    else
      let needA := !pte.accessed
      let needD := (acc = .store || acc = .cbZero) && !pte.dirty
      if !needA && !needD then .ok pte
      else if !adue then .fault
      else .ok { pte with accessed := true, dirty := if acc = .store || acc = .cbZero then true else pte.dirty }

theorem eager_ad_collapses_svade_svadu (acc : AccessKind) (pte : LeafPte)
    (hA : pte.accessed = true) (hD : pte.dirty = true) :
    evalStep9 false acc pte = evalStep9 true acc pte := by
  cases pte; simp_all [evalStep9]

end RiscvBootAndAdue
```

## Boundaries

- **`known not to apply` — Clearing `ADUE` or `PBMTE` by writing `senvcfg = 0`, omitting `SFENCE.VMA x0, x0` after `menvcfg.ADUE` changes, or using non-atomic `READ_ONCE` + `atomic_long_set` (`ptep_set_wrprotect`) under `ADUE = 1`:** `senvcfg[63:34]` is `WPRI` read-only zero (`supervisor.adoc:791–821`, `sys_regs.sail:475–492`), `#norm:menvcfg_adue_fence` (`machine.adoc:2209–2211`) mandates `SFENCE.VMA x0, x0` after modifying `ADUE`, and non-atomic `ptep_set_wrprotect` clobbers concurrent hardware `D = 1` transitions. **Basis: normative, source, execution.**
- **`unsupported` — Unconditional `csrw senvcfg, x0` on Priv `< 1.12` silicon or when `mstateen0.ENVCFG == 0`, and SBI `FWFT` `PTE_AD_HW_UPDATING` on single-scheme silicon:** S-mode `senvcfg` access traps if `mstateen0.ENVCFG == 0` (`smstateen.adoc:275`), and OpenSBI `fwft_adue_supported` (`sbi_fwft.c:161–176`) returns `SBI_ENOTSUPP` unless **both** `Svade` and `Svadu` are supported. **Basis: normative, source.**
- **`not examined` — Hypervisor `hcounteren`/`henvcfg` two-level G-translation `Svadu` rules (`sys_implicit_vs_pte_access_sets_gstage_d` in `vmem_pte.sail:325`), `Ssdbltrp` (`DTE`/`SDT`), and `Zicfilp`/`Zicfiss` shadow-stack faults (`LPE`/`SSE`):** While bit layouts and `henvcfg` masking (`sys_regs.sail:592–606`) were verified, guest hypervisor `HFENCE.VVMA`/`HFENCE.GVMA` races with G-table `A`/`D` updates were `not examined`. **Basis: source.**
- **`unknown` — Vendor silicon reset defaults for `senvcfg`, `menvcfg`, and `scounteren` under custom non-OpenSBI M-mode firmware:** Under `#norm:rst_other_state_unspec` (`machine.adoc:2789`), proprietary SoC reset values remain `unknown` without per-chip errata or runtime boot probing. **Basis: normative, documentation.**

## Evidence

| Subject | Pinned Identifier | Inspected Artifacts & Exact Line Ranges | Basis |
| :--- | :--- | :--- | :--- |
| `riscv/riscv-isa-manual` | `c05f1725f25526dd8463bac6ca75cfcfbee17d05` | `src/priv/machine.adoc` `L460, 1556–1618, 2128–2321, 2770–2796`; `src/priv/supervisor.adoc` `L317–364, 500–530, 782–963, 1596–1690, 1717–1825`; `src/priv/smstateen.adoc` `L275–278`; `src/priv/svadu.adoc` `L4–14` | `normative` |
| `riscv-non-isa/riscv-sbi-doc` | `8a545effe9b50484ff897d9815d7d9015cdef203` | `src/intro.adoc` `L1–40`; `src/ext-hsm.adoc` `L92–102, 232–242`; `src/ext-firmware-features.adoc` `L9–191` | `normative` |
| `riscv-software-src/opensbi` | `61f1973bd50338b36c52dc34006f76d464ca4f34` | `lib/sbi/sbi_hart.c` `L27–186, 638–640`; `lib/sbi/sbi_fwft.c` `L79–111, 161–195`; `include/sbi/riscv_encoding.h` `L229–251, 890–891` | `source` |
| `riscv/sail-riscv` | `76f1ce3c184797178864b9869963e8b44465889e`, `doi:10.1145/3290384` | `model/core/sys_regs.sail` `L446–647`; `model/sys/vmem.sail` `L95–120, 247–250, 394–455`; `model/sys/vmem_pte.sail` `L295, 304–372` | `source`, `documentation` |
| `torvalds/linux` | `5f22fb20497f4983094131f00a734362300d22d2` | `arch/riscv/kernel/head.S` `L84–125, 135–136, 246–247`; `cpufeature.c` `L93–122, 308–316, 480–488, 564–663, 1268–1283`; `switch_to.h` `L74–90`; `process.c` `L203–206, 413–455`; `suspend.c` `L18, 50`; `pgtable.h` `L663–756`; `mm/pgtable.c` `L8–39`; `pgtable-bits.h` `L9–20` | `source` |
| `seL4/seL4` & `seL4/l4v` | `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`, `doi:10.1145/2560537`, `doi:10.1007/978-3-642-03359-9_20` | `seL4`: `src/arch/riscv/head.S` `L23–63`, `boot.c` `L126–143`, `vspace.c` `L182–222, 533–576, 656–676`; `l4v`: `spec/machine/RISCV64/MachineOps.thy` `L198–225` | `source`, `documentation` |
| `mit-pdos/xv6-riscv` | `fa2ddcb7ca87a77af579380a6eafd5aff163b44f` | `kernel/start.c` `L15–66`; `kernel/riscv.h` `L213–230`; `kernel/vm.c` `L166–169` | `source` |
| Syeda & Klein / Simner et al. | `doi:10.1007/s10817-019-09539-7`, `doi:10.1007/978-3-030-99336-8_6`, `arXiv:2203.00642` | Cached-MMU consistent sets and relaxed speculative descriptor-walk models | `documentation` |
| Python 3 Probe (`reval_senvcfg_svade.py`) | Executed `2026-11-20`, Python 3.13 | Verified `legalize_senvcfg`, 9 reset hazards, speculative `A` dirtying, lost-`D` `ptep_set_wrprotect` witness, `xchg` safety, and eager `A=1, D=1` collapse (`0.06 ms`, exit `0`) | `execution` |

## Revalidation

Run the standalone Python 3 probe below (`< 1 ms`, standard library only) to revalidate `senvcfg`/`menvcfg` bit separation, OpenSBI + kernel reset hazards, `Svade`/`Svadu` speculative `A` updates, `ptep_set_wrprotect` dirty-bit clobbering, and `A = 1 ∧ D = 1` equivalence:

```python
#!/usr/bin/env python3
import itertools, time
t0 = time.perf_counter()

SENVCFG_MASK = (0x3 << 32) | (1 << 8) | (1 << 7) | (1 << 6) | (0x3 << 4) | (1 << 3) | (1 << 2) | 1
MENVCFG_ADUE, MENVCFG_PBMTE, MENVCFG_STCE = 1 << 61, 1 << 62, 1 << 63

def legalize_senvcfg(old: int, val: int, cbie_allow=(0, 1, 3)) -> int:
    nxt = val & SENVCFG_MASK
    if ((nxt >> 4) & 0x3) not in cbie_allow:
        nxt = (nxt & ~(0x3 << 4)) | (((old >> 4) & 0x3) << 4)
    if ((nxt >> 32) & 0x3) == 1:
        nxt = (nxt & ~(0x3 << 32)) | (((old >> 32) & 0x3) << 32)
    return nxt

s_all1 = legalize_senvcfg(0, (1 << 64) - 1)
assert (s_all1 & (MENVCFG_ADUE | MENVCFG_PBMTE | MENVCFG_STCE)) == 0 and s_all1 == SENVCFG_MASK
s_resv = legalize_senvcfg(s_all1, (0x2 << 4) | (0x1 << 32))
assert ((s_resv >> 4) & 0x3) == 3 and ((s_resv >> 32) & 0x3) == 3 and legalize_senvcfg(s_all1, 0) == 0

def opensbi_mstatus_init(has_svade: bool, has_svadu: bool, has_zicbom: bool, has_zicboz: bool) -> dict:
    menvcfg = (1 << 7 if has_zicboz else 0) | (((1 << 6) | (0x3 << 4)) if has_zicbom else 0)
    if (not has_svade) and has_svadu:
        menvcfg |= MENVCFG_ADUE
    return {"scounteren": 0x02, "mstateen0_envcfg": 1, "menvcfg": menvcfg}

fw = opensbi_mstatus_init(True, True, True, True)
assert (fw["menvcfg"] & MENVCFG_ADUE) == 0
cbie_haz = sum(1 for c in (0, 1, 3) for p in (0, 2, 3) if ((fw["menvcfg"] >> 4) & 3) == 3 and c == 3)
pmm_haz = sum(1 for c in (0, 1, 3) for p in (0, 2, 3) if p in (2, 3))
assert cbie_haz == 3 and pmm_haz == 6
for c, p in itertools.product((0, 1, 3), (0, 2, 3)):
    k_s = legalize_senvcfg((c << 4) | (p << 32), 0)
    assert ((k_s >> 4) & 3) == 0 and ((k_s >> 32) & 3) == 0

PTE_V, PTE_R, PTE_W, PTE_X, PTE_U, PTE_A, PTE_D = (1 << i for i in range(7))

def ptw_step(pte: int, is_write: bool, adue: int, speculative: bool = False) -> tuple[str, int]:
    if not (pte & PTE_V) or (is_write and not (pte & PTE_W)) or (not is_write and not (pte & PTE_R)):
        return ("fault", pte)
    need_a, need_d = (pte & PTE_A) == 0, is_write and ((pte & PTE_D) == 0)
    if speculative:
        return ("spec_ok", pte | PTE_A) if (adue == 1 and need_a) else ("spec_squash", pte)
    if need_a or need_d:
        return ("fault_ad", pte) if adue == 0 else ("ok", pte | PTE_A | (PTE_D if is_write else 0))
    return ("ok", pte)

base = PTE_V | PTE_R | PTE_W | PTE_U
assert ptw_step(base, False, 0, True) == ("spec_squash", base)
st_u, pte_u = ptw_step(base, False, 1, True)
assert st_u == "spec_ok" and (pte_u & PTE_A) != 0 and (pte_u & PTE_D) == 0

def wrprotect_race(atomic_rmw: bool) -> tuple[int, bool]:
    pte = PTE_V | PTE_R | PTE_W | PTE_U | PTE_A
    reg = pte
    _, pte = ptw_step(pte, True, 1, False)  # remote hart store sets D=1 atomically
    return (pte & ~PTE_W if atomic_rmw else (reg & ~PTE_W) | PTE_R), True

lost_pte, mod1 = wrprotect_race(False)
safe_pte, mod2 = wrprotect_race(True)
assert mod1 and (lost_pte & PTE_D) == 0 and mod2 and (safe_pte & PTE_D) != 0

for hw_first in (False, True):
    pte = PTE_V | PTE_R | PTE_W | PTE_U | PTE_A
    mod = False
    if hw_first:
        _, pte = ptw_step(pte, True, 1, False); mod = True
    obs, pte = pte, 0
    assert (not mod) or ((obs & PTE_D) != 0)

eager = PTE_V | PTE_R | PTE_W | PTE_U | PTE_A | PTE_D
for is_w, spec in itertools.product((False, True), (False, True)):
    if not (spec and is_w):
        assert ptw_step(eager, is_w, 0, spec) == ptw_step(eager, is_w, 1, spec)

print(f"reval_senvcfg_svade PASSED in {(time.perf_counter() - t0) * 1000.0:.2f} ms")
```

To check newer upstream commits for drift, diff OpenSBI `lib/sbi/sbi_hart.c` (`mstatus_init` around `CSR_SCOUNTEREN` and `CSR_SENVCFG`), Linux `arch/riscv/include/asm/pgtable.h` (`ptep_set_wrprotect`), and `seL4/seL4` `src/arch/riscv/kernel/boot.c` (`init_cpu`) for newly added `senvcfg` initialization or atomic `wrprotect` writes.
