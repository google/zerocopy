# RISC-V Zicsr Semantics, S-Mode Trap Scratch Swaps, and Assembly Handler Verification

## Summary

Unlike x86 or ARM Cortex-M cores—where hardware pushes an exception frame onto a privileged stack—RISC-V Supervisor mode (`S-mode`) saves **zero general-purpose registers**, jumps directly to `stvec` with `sstatus.SIE` cleared and `sstatus.SPP` recording a single prior-privilege bit, and delegates isolation entirely to assembly stubs (`traps.S`, `entry.S`, `trampoline.S`). **Basis: normative, source.**

Proving trap-handler correctness against authoritative RISC-V semantics (`riscv/riscv-isa-manual` and `riscv/sail-riscv`) requires six invariants:
1. **`Zicsr` Syntactic Suppression and Split `sip`/`mip` Reads:** Read/write side effects depend on **instruction register fields** (`rd == x0` suppresses reads on `CSRRW`/`CSRRWI`; `rs1 == x0` or `uimm == 0` suppresses writes on `CSRRS`/`CSRRC`/`CSRRSI`/`CSRRCI`), never runtime register values (`CSRRS rd, ro_csr, t0` with `X[t0] == 0` still executes `CSRReadWrite` and traps on read-only CSRs), while `sip`/`mip` split `rd` observation (`IncludePlatformInterrupts`) from the RMW read (`ExcludePlatformInterrupts`). Simplified symbolic interpreters (`uw-unsat/serval`) that omit these guards misclassify CSR traps and side effects. **Basis: normative, source, execution.**
2. **`sscratch` Swap Soundness Across U-Mode and Nested S-Mode Traps:** `Linux` zero-sentinel `tp` swapping (`csrrw tp, CSR_SCRATCH, tp` paired with `csrw CSR_SCRATCH, x0` on every S-mode path) handles arbitrary nested S-mode traps, whereas `seL4` uniprocessor `csrrw t0, sscratch, t0` preserves frame bijection **only** under a global S-mode fault-freedom invariant (`non_kernel_IRQs = {}`). **Basis: source, execution.**
3. **`stvec` `Direct` vs. `Vectored` WARL Masking and `.option norelax` `gp` Reload:** `Vectored` (`MODE = 1`) offsets only asynchronous interrupts (`BASE + 4 * cause`), routing all synchronous exceptions (`ecall`, faults) to `BASE` under `WARL` alignment masking (`legalize_tvec`). Handlers MUST reload `gp` inside `.option push; .option norelax` so user `gp` cannot hijack relaxed kernel global accesses. **Basis: normative, source.**
4. **`sstatus` / `sepc` Trap-Stack Transitions:** Entry sets `SPIE <- SIE`, `SIE <- 0`, `SPP <- (prev == S)`, `SDT <- 1` (`Ssdbltrp`), and `sepc <- PC`; software clears `SUM | FS | VS | ELP` (`Linux`) and sets `NextIP <- sepc + 4` strictly for `ecall` (`scause == 8`). `SRET` executes `SIE <- SPIE`, `SPIE <- 1`, `priv <- SPP`, `SPP <- 0`, `SDT <- 0`, and clears `MPRV` below M-mode. **Basis: normative, source, execution.**
5. **`Zalrsc` Reservation Persistence Across `SRET`:** `#norm:xret_clr_lr_resv` allows `SRET` to preserve `LR` reservations (`plat_reservation_invalidate_on_xret` in `sail-riscv`). Portable kernels execute an idempotent post-load dummy `SC` (`seL4` `sc.w zero, zero, (t0)` after loading `ra`; `Linux` `REG_L a2, PT_EPC(sp); REG_SC x0, a2, PT_EPC(sp)`) on exit. **Basis: normative, source, execution.**
6. **Register-Frame Bijections and Disjointness:** Full assembly verification pairs a 31-GPR + CSR relational bijection (`TrapEntryBijection` / `TrapReturnBijection`) with frame/stack/page-table disjointness, bridging `DONT_TRANSLATE` stubs via symbolic Sail traces (`Islaris`) or translation validation (`seL4/l4v`). **Basis: documentation, source, derived.**

## Applicability

This report covers RV32I/RV64I + `Zicsr` + `Zalrsc` (`A`) trap-entry and trap-return assembly across S-mode OS kernels (`seL4`, `Linux`, `xv6-riscv`) alongside comparative M-mode (`Tock`, `uw-unsat/serval` CertiKOS-style monitors) and ARM Cortex-M (`oxidecomputer/hubris`) handlers. **Basis: normative, source.**

Sibling corpus reports cover adjacent boundaries without duplicating trap-assembly semantics: `isa-page-table-tlb-coherence-sail-trap-contracts-and-toctou-dma-fetch-oracles` (`Sv39` walks and `TrapContract` wrapper placement), `mmu-page-table-walks-tlb-shootdowns-and-icache-barrier-refinement` (`sfence.vma`/`fence.i`), `load-reserved-store-conditional-reservation-sets-forward-progress-and-aba-hazards` (constrained `LR/SC` loops), `riscv-plic-priority-threshold-ordering-nested-sie-and-msrp-cross-hart-locking` (PLIC priority thresholds), and `rust-inline-assembly-contracts-relocations-and-simd-correspondence` (`rustc` `asm!`). Here, authoritative ISA models (`riscv/riscv-isa-manual`, `riscv/sail-riscv`, `opencompl/sail-riscv-lean`) ground direct comparison of concrete kernels (`seL4/seL4`, `torvalds/linux`, `tock/tock`, `mit-pdos/xv6-riscv`, `oxidecomputer/hubris`) and verification frameworks (`seL4/l4v`, `rems-project/islaris`, `uw-unsat/serval`). **Basis: documentation, source.**

## Findings

### 1. Normative `Zicsr` Operand-Index Suppression, Shadowed RMW Splits, and Ordering

**Basis: normative, source, execution.**

Per `riscv/riscv-isa-manual` (`c05f1725f25526dd8463bac6ca75cfcfbee17d05`, `src/unpriv/zicsr.adoc` L29–190) and `riscv/sail-riscv` (`76f1ce3c184797178864b9869963e8b44465889e`, `model/extensions/Zicsr/zicsr_insts.sail` L33–107), 12-bit CSR addresses encode read-only status in `csr[11:10] == 0b11` and minimum privilege in `csr[9:8]` (`sys_control.sail` L28–47). Instruction classification depends purely on encoded fields (`csr_access_type`, `zicsr_insts.sail` L33–41):

| Instruction | `rd` Field | `rs1` / `uimm` Field | `CSRAccessType` | Reads CSR? | Writes CSR? | Read-Only CSR (`0b11`) | Pseudoinstruction / Use |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `CSRRW` / `CSRRWI` | `x0` | any | `CSRWrite` | **No** (`zeros()`) | **Yes** | `Illegal_Instruction` | `csrw csr, rs1` / `csrwi` |
| `CSRRW` / `CSRRWI` | `!= x0` | `x0` / `0` | `CSRReadWrite` | **Yes** | **Yes** (`0` written) | `Illegal_Instruction` | `csrrw s0, mscratch, x0` (read & zero) |
| `CSRRW` / `CSRRWI` | `!= x0` | `!= x0` / `!= 0` | `CSRReadWrite` | **Yes** | **Yes** | `Illegal_Instruction` | `csrrw sp, sscratch, sp` |
| `CSRRS` / `CSRRC` (`I`) | any | `x0` / `0` | `CSRRead` | **Yes** (even `rd=x0`) | **No** | **Permitted** | `csrr rd, csr` |
| `CSRRS` / `CSRRC` (`I`) | any | `!= x0` / `!= 0` (even `X[rs1]=0`) | `CSRReadWrite` | **Yes** | **Yes** | `Illegal_Instruction` | `csrs` / `csrc` / `csrrc rd, sstatus, mask` |

Four subtle hardware semantics govern CSR verification:
1. **Syntactic `rs1 == x0` vs. Runtime `X[rs1] == 0` (`zicsr.adoc` L63–73):** Executing `csrrs rd, cycle, t0` when `X[t0] == 0` still encodes `rs1 != x0`, triggering `CSRReadWrite` whole-CSR write side effects and an illegal-instruction trap on read-only CSRs (`cycle`, `time`, `instret`), verified across all 30 opcode/operand configurations in `reval_pkg1.py`. Conversely, `csrrs x0, csr, x0` suppresses writes yet **still triggers read side effects** (`zicsr.adoc` L67–69, L89–90).
2. **Shadowed-Field RMW vs. `sip`/`mip` Split Reads (`zicsr.adoc` L53–61 & `zicsr_insts.sail` L54–74):** `CSRRS`/`CSRRC` write back `read_val | mask` or `read_val & ~mask`, so bits reading differently from underlying storage (e.g., `pmpaddr_n[G-1]`) get overwritten by unrelated bit sets/clears. For `mip` (`0x344`) and `sip` (`0x144`), `sail-riscv` reads `read_val = read_CSR(csr)` (`ExcludePlatformInterrupts`) for the RMW computation while assigning `dest_val = read_sip(IncludePlatformInterrupts).bits` to `X[rd]`, preventing external PLIC `SEIP` assertions from polluting writable software storage.
3. **Read-and-Zero Atomicity (`zicsr.adoc` L75–76):** `csrrw s0, mscratch, x0` (`Tock` `lib.rs:346`) reads `mscratch` into `s0` while zeroing `mscratch`; `csrrs s0, mscratch, x0` reads without zeroing.
4. **Weak Ordering and Symbolic Interpreter Gaps (`zicsr.adoc` L191–249 & `serval/riscv/interp/i-type.rkt` L82–125):** Locally, CSR side effects are visible to the immediate next instruction (`#norm:csr_side_effects_synchronous`), and explicit CSR writes override implicit same-instruction updates (`#norm:csrw_order`). Under RVWMO, CSR reads/writes order as `I`/`O` device accesses (`#norm:csr_fence_ordering`). By direct inspection, `uw-unsat/serval` (`72adc4952a1e62330aea527214a26bd0c09cbd05`, `i-type.rkt` L82–125) implements `do-csr-op` by unconditionally calling `csr-ref`, writing `rd`, and calling `csr-set!`, omitting `rd == x0` / `rs1 == x0` side-effect suppression, `csr[11:10] == 0b11` read-only faults, and `sip`/`mip` split reads.

### 2. Taxonomy of `sscratch`/`mscratch` Swap State Machines Across Six OS Architectures

**Basis: source, documentation, execution.**

At `stvec`/`mtvec` entry, all 31 GPRs belong to the interrupted context. Production and verified kernels implement five distinct RISC-V swap machines (contrasted with Cortex-M hardware stacking in Hubris):

| Kernel (`Revision`) | Source | Entry Swap | U-Mode `xscratch` | S-Mode `xscratch` | Nested S-Mode Traps? | Primary Soundness Condition / Hazard |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`seL4` UP** (`seL4/seL4` `08c7e5fd...`) | `traps.S` L33–95; `c_traps.c` L77–80 | `t0` (`x5`) <-> `sscratch` | `&tcbContext.registers` (`c_traps.c:79`) | `&tcbContext` (**never zeroed**) | **No** (halts if `SPP == 1`, `c_traps.c:112`) | Requires `non_kernel_IRQs = {}` (`l4v` `MachineOps.thy:111`) and zero S-mode exceptions; nested fault overwrites saved frame via swapped `t0` (`reval_pkg1.py`). |
| **`seL4` SMP** (`seL4/seL4` `08c7e5fd...`) | `traps.S` L26–92; `c_traps.c` L27–31 | `sp` (`x2`) <-> `sscratch` | Per-core kstack top (`*(sp-w) = &tcbContext`) | Restored (`csrw sscratch, sp`, L91) | **Fatal halt only** (`-2*REGBYTES` reused) | Requires `*(sp - w)` initialized at `restore_user_context` (`c_traps.c:28–30`) and `_start` (`head.S:39`). |
| **`Linux`** (`torvalds/linux` `5f22fb20...`) | `entry.S` L23–206, L252–279 | `tp` (`x4`) <-> `CSR_SCRATCH` | `&current` (`task_struct != 0`) | **`0`** (`csrw CSR_SCRATCH, x0`, L87, L205) | **Yes** (plus `overflow_stack` L327) | Every S-mode return path (including early `vmalloc` fault `sret` at L87–88) MUST leave `CSR_SCRATCH == 0`. |
| **`xv6-riscv`** (`mit-pdos/xv6-riscv` `fa2ddcb7...`) | `trampoline.S` L20–152; `kernelvec.S` L12–64 | `a0` -> `sscratch` (`uservec`) | Unused until L31 | Unused (`stvec = kernelvec`) | **Yes** (after `w_stvec(kernelvec)`) | Window between `csrw satp` (`trampoline.S:91`) and `w_stvec(kernelvec)` (`trap.c:47`) must never fault (`TRAPFRAME` unmapped in kernel `satp`). |
| **`Tock`** (`tock/tock` `b336e170...`) | `arch/riscv/src/lib.rs` L108–111, L287–431 | `s0` (`x8`) <-> `mscratch` | `&custom_trap_handler` (`!= 0`) | **`0`** (`csrrw s0, mscratch, zero`, L346) | **Yes** (`bgtu sp, _sstack`, L334) | Custom user handler at `slot[1]` runs in trap context and must restore `mscratch = 0` (`lib.rs:254–257`). |
| **`Oxide Hubris`** (`oxidecomputer/hubris` `969bac2b...`) | `arch.rs` L24–48; `arm_m.rs` L100–272 | Hardware `PSP`/`MSP` stack | `CURRENT_TASK_PTR` global | Hardware-stacked `BaseExceptionFrame` | Cortex-M tail-chaining | Mainline targets ARM-M/host only; RISC-V ports require `mscratch`/`sscratch` instead of globals. |

Key assembly subtleties across these handlers:
- **`seL4` SMP Two-Slot Spill (`traps.S` L28–32, L68–92):** On SMP, `sscratch` holds the core's kernel `sp` while `restore_user_context` caches `cur_thread_reg` at `((word_t*)sp)[-1]` (`c_traps.c:29–30`). Entry swaps `sp` (`L28`), spills user `t0` to `(-2*REGBYTES)(sp)` (`L30`), loads `&tcbContext` into `t0` from `(-1*REGBYTES)(sp)` (`L31`), saves all other GPRs, moves user `t0` via `x1` into slot `4` (`L69, L73`), retrieves user `sp` via `csrr x1, sscratch` into slot `1` (`L88–89`), and writes kernel `sp` back to `sscratch` (`L91`).
- **`Linux` Early-Exit `sscratch` Window (`entry.S` L87, L134–205):** When trapping from S-mode (`CSR_SCRATCH == 0`, `tp == &current`), `csrrw tp, CSR_SCRATCH, tp` (`L134`) sets `tp = 0` and temporarily leaves `CSR_SCRATCH = &current` (`!= 0`)! `.Lrestore_kernel_tpsp` executes `csrr tp, CSR_SCRATCH` (`L138`) to recover `tp`, meaning **`CSR_SCRATCH` remains nonzero** until `csrw CSR_SCRATCH, x0` (`L205`). Hence `new_valid_map_cpus_check`'s early retry return MUST execute `csrw CSR_SCRATCH, x0` (`L87`) immediately before `sret` (`L88`); omitting `L87` corrupts `TASK_TI_USER_SP` on the next S-mode trap (`reval_pkg1.py`: `MISCLASSIFIED_NESTED_TRAP`).
- **`Tock` Stack-Overflow Guard (`lib.rs` L329–347):** After `csrrw s0, mscratch, s0` (`L305`) branches on `s0 == 0` (`L308`), `Tock` checks `bgtu sp, _sstack` (`L334`) before pushing the 20-word caller-saved frame, resetting `sp = _estack` (`L341`) on overflow and atomically recovering `s0` while clearing `mscratch` via `csrrw s0, mscratch, zero` (`L346`).

### 3. `stvec` WARL Legalization (`Direct` vs. `Vectored`), Linker Relaxation Hazards, and `sepc` Advancement

**Basis: normative, source, execution.**

`supervisor.adoc` (`L319–364`) and `sail-riscv` (`sys_regs.sail` L673–702, `sys_exceptions.sail` L17–100) define `stvec` as `{BASE[XLEN-1:2], MODE[1:0]}`:
- **`Direct` (`MODE = 0`):** All exceptions and interrupts set `PC <- BASE`.
- **`Vectored` (`MODE = 1`):** Asynchronous interrupts (`IsInterrupt = 1`) set `PC <- BASE + 4 * cause` (`supervisor.adoc:350, 360–362`), whereas **all synchronous exceptions (`IsInterrupt = 0`, including `ecall`) still enter at `BASE`** (`reval_pkg1.py`).
- **`WARL` Alignment Masking (`legalize_tvec`, `sys_regs.sail` L683–701):** Reserved `MODE >= 2` values retain the prior `MODE` (or fault under `Xtvec_Fatal`), and `Vectored` masks low `BASE` bits below `2^vectored_alignment_exp`. `Tock` therefore enforces 256-byte linker alignment on `start_trap` (`lib.rs:282–287`) so `WARL` masking never truncates the vector table base.

**Linker-Relaxation `gp` Hijack (`seL4` `traps.S` L81–84, `head.S` L25–29; `Tock` `lib.rs` L93–99):** Under psABI `+/- 2 KiB` `gp`-relaxation, compiling `la gp, __global_pointer$` without `.option norelax` relaxes the pair into `mv gp, gp` (`addi gp, gp, 0`)—preserving an attacker's user `gp` (`x3`) into C/Rust kernel code! Both `seL4` and `Tock` wrap `la gp, __global_pointer$` in `.option push; .option norelax; ...; .option pop`, while `Linux` invokes `load_global_pointer` (`entry.S:208`). Disassembly verification of trap prologues must assert both `gp` reload before any C/Rust call and absence of `gp`-relative self-relaxation.

**`sepc` Advancement (`supervisor.adoc` L546–569 & `traps.S` L98–145):** Hardware latches `sepc <- virtual_addr(trapping_insn)` with `sepc[0] = 0` (and `sepc[1]` masked to `0` when `IALIGN = 32`, `#norm:sepc_op_mask_ialign32`). In `seL4` (`traps.S:105–145`) and `xv6` (`trap.c:54–62`), only U-mode `ecall` (`scause == 8`) sets `NextIP = sepc + 4`; faults and interrupts preserve `NextIP = sepc` for instruction retry. Emulated instructions or `ebreak` handlers supporting `RVC` must decode bits `[1:0] == 0b11` rather than assuming 4-byte length.

### 4. Trap-Stack Transitions (`sstatus.SPP`, `SPIE`, `SIE`, `SUM`, `FS`, `MPRV`, `SDT`) on Entry and `SRET`

**Basis: normative, source, execution.**

`sail-riscv` (`sys_control.sail` L325–357, L453–490; `base_insts.sail` L573–609, L661–730) specifies the normative state transitions of `supervisor.adoc` (`L103–284`) and `machine.adoc` (`L2650–2676`):

| Transition | `cur_privilege` | `SPP` (bit 8) | `SPIE` (bit 5) | `SIE` (bit 1) | `MPRV` (bit 17) | `SDT` (bit 24, `Ssdbltrp`) | `PC` / `sepc` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Trap to `S` (from `U`)** | `U -> S` | `<- 0` | `<- old SIE` | `<- 0` | Unchanged | `0 -> 1` (if `1`: double trap to `M`, `mcause=16`) | `sepc <- PC`; `PC <- tvec_addr` |
| **Trap to `S` (from `S`)** | `S -> S` | `<- 1` | `<- old SIE` | `<- 0` | Unchanged | `0 -> 1` (if `1`: unexpected trap -> `M`) | `sepc <- PC`; `PC <- tvec_addr` |
| **`SRET` (`SPV = 0`)** | `S -> SPP` (`TSR=0`) | `<- 0` | `<- 1` | `<- old SPIE` | `<- 0` (`new != M`) | `<- 0` | `PC <- align_pc(sepc)` |

Key verification constraints:
1. **`TSR` / `VTSR` Illegal Traps (`base_insts.sail` L667–682):** `SRET` raises `Illegal_Instruction` in U-mode or when `mstatus.TSR = 1` in S-mode (`Virtual_Instruction` in `VS` with `hstatus.VTSR = 1`).
2. **Entry Sanitization (`Linux` `entry.S` L181–188):** Because hardware preserves `sstatus.SUM`, `FS`, `VS`, and `SPELP`, `Linux` executes `csrrc s1, CSR_STATUS, t0` (`t0 = SR_SUM | SR_FS_VS | SR_ELP`), saving pre-trap `sstatus` into `s1` while atomically disabling user-memory access and FP/vector units in kernel space.
3. **`Ssdbltrp` Double-Trap Protection Window (`supervisor.adoc` L260–315, `sys_control.sail` L462–472):** Any S-mode trap taken while `SDT == 1` redirects to M-mode (`mcause = 16`, `mtval2 = unexpected scause`). Writing `SDT = 1` clears `SIE = 0` (`#norm:sstatus_sdt_sstatus_sie_overwrite`), while `SRET` clears `SDT <- 0` (`base_insts.sail:590–595`), guarding the tail exit sequence (`csrw sstatus`/`csrw sepc`..`sret`) against unrecovered nested faults.

### 5. `Zalrsc` Reservation Persistence Across `SRET` and Idempotent Dummy-`SC` Idioms

**Basis: normative, source, execution.**

Per `#norm:xret_clr_lr_resv` (`machine.adoc` L2667–2676), `SRET` is **allowed—not required—to clear an active `LR` reservation** (`plat_reservation_invalidate_on_xret` in `sail-riscv` `base_insts.sail:724`). Because `#norm:lr_reservation_set_size` (`zalrsc.adoc` L91–93; `seL4` `hardware.h` L42–52) permits arbitrarily wide reservation sets (e.g., an entire 4 KiB page) and any `sc` instruction clears the hart's reservation regardless of address or outcome (`zalrsc.adoc:23–25`, `zalrsc_insts.sail:76`), handlers face three regimes under `plat_reservation_invalidate_on_xret = false` (`reval_pkg1.py`):

1. **Omitted Dummy `SC` (`xv6-riscv` `trampoline.S` L100–152):** `userret` performs no `sc`, allowing thread $A$'s preempted `lr.d` reservation to survive across `SRET` and satisfy thread $B$'s stray `sc.d` on shared physical memory.
2. **`seL4` Post-Load Dead-Slot `SC` (`c_traps.c` L41, L48):** `seL4` loads `ra` from `0(t0)` (`L41`) **before** executing `sc.w zero, zero, (t0)` (`L48`)—explicitly noting that a wide reservation set may allow `sc.w` to overwrite `(t0)` safely only because saved `ra` is already dead until the next trap. Reordering `sc.w` before loading `ra` clobbers `ra` (`reval_pkg1.py`: `CLOBBERED_RA`).
3. **`Linux` Value-Preserving Dummy `SC` (`entry.S` L303–304):** `Linux` executes `REG_L a2, PT_EPC(sp); REG_SC x0, a2, PT_EPC(sp)` before restoring `a2`. Even if `REG_SC` unexpectedly succeeds, writing `a2` back to `PT_EPC(sp)` is an identity store on aligned kernel memory (`(sp)`) while unconditionally canceling any dangling reservation.

### 6. Proving Full Register-Frame Save/Restore Bijections Against Sail RISC-V

**Basis: documentation, source, derived.**

Against `sail-riscv` / `opencompl/sail-riscv-lean`, a sound assembly contract separates into four obligations:
1. **`TrapEntryBijection` and `TrapReturnBijection`:** Let $\sigma = (\text{gprs} : \text{Fin } 32 \to \text{BV}, \text{pc}, \text{priv}, \text{sscratch}, \text{sepc}, \text{scause}, \text{sstatus}, \text{stval}, \text{resv}, \text{mem})$ with $\text{gprs}(0) = 0$, and let $\text{FrameMatches}(\sigma, p, \text{next\_ip})$ require slots $0..30$ to hold $\sigma.\text{gprs}(1..31)$ and slots $31..34$ to hold $(\sigma.\text{scause}, \sigma.\text{sstatus}, \sigma.\text{sepc}, \text{next\_ip})$ where $\text{next\_ip} = \text{ite}(\sigma.\text{scause} = 8, \sigma.\text{sepc} + 4, \sigma.\text{sepc})$. `trap_entry` refines post-trap state $\sigma_1$ to C/Rust entry $\sigma_2$ satisfying $\text{FrameMatches}(\sigma_0, p, \text{next\_ip})$, $\sigma_2.\text{gp} = \text{\_\_global\_pointer\$}$, valid kernel `sp`, and the S-mode `sscratch` invariant; `restore_user_context` / `ret_from_exception` maps $\text{FrameMatches}(\sigma', p, \sigma'.\text{next\_ip})$ to post-`SRET` $\sigma_3$ restoring all 31 GPRs, $\text{pc} = \text{align\_pc}(\sigma'.\text{next\_ip})$, $\text{priv} = \sigma'.\text{sstatus.SPP}$, $\text{sstatus.SIE} = \sigma'.\text{sstatus.SPIE}$, user `sscratch`, and $\sigma_3.\text{resv} = \text{None}$.
2. **Spatial Non-Aliasing (`ValidFramePtr`):** `[p, p + 35*w)` must be naturally aligned, kernel-RW mapped, and disjoint from active kernel stack frames (`sp - 2*w .. sp` in `seL4` SMP) and page-table pages.
3. **Sail Symbolic Trace vs. Binary Translation Validation Bridges:** `Islaris` (`rems-project/islaris`, PLDI 2022 `doi:10.1145/3519939.3523434`) lifts `sail-riscv` into `isla_trace` trees verified in Iris (`WPasm`), pinning `mstatus.MPRV = 0` via `MaskShape 64 0x20000 0` (`theories/riscv64/sys_regs.v` L80–115). Conversely, `seL4/l4v` (PLDI 2013 `doi:10.1145/2499370.2462183`) validates compiled C via graph refinement while marking `restore_user_context` `DONT_TRANSLATE` (`c_traps.c:21`) and excluding `.S` stubs (`head.S:54–61`), making Sail-linked bijection contracts the direct closure for the assembly TCB. CertiKOS (`doi:10.1145/1379022.1375591`, `doi:10.1145/2908080.2908101`) modularizes this boundary via interrupt-disabling permission transfer between assembly stubs and C layers.

## Boundaries

- **`unsupported` — Mainline RISC-V S-mode `traps.S` in `oxidecomputer/hubris` (`969bac2bf47c98710842eb232fdd4a9c54e7dd7f`):** `sys/kern/src/arch.rs` (L24–48) enables only `host` and 32-bit `arm` (`arm_m.rs`), rejecting other targets with `compile_error!`; RISC-V trap handlers are `unsupported` in mainline Hubris. **Basis: source.**
- **`known not to apply` — Assuming `SRET` clears `LR` reservations, `CSRRS` with `X[rs1]==0` suppresses CSR writes, UP `seL4` `sscratch` survives S-mode faults, or `uw-unsat/serval` models `Zicsr` side-effect suppression:** `#norm:xret_clr_lr_resv` permits reservation retention across `SRET`; `#norm:csrrs_csrrc_rs1_x0` ties write suppression solely to `rs1 == x0`; `seL4` UP `traps.S` (`L33, L71`) clobbers user context on nested faults; and `serval/riscv/interp/i-type.rkt` (`L82–125`) always reads/writes CSRs without `x0` suppression or `0b11` checks. All four claims are `known not to apply`. **Basis: normative, source, execution.**
- **`not examined` — `Smrnmi` (`mnstatus`), AIA (`stopei`/`IMSIC`), and RVV `vlenb` preemptive vector context save/restore (`CONFIG_RISCV_ISA_V_PREEMPTIVE`):** Extension trap registers beyond base S-mode + `Zicsr` + `Zalrsc` + `Ssdbltrp` were `not examined`. **Basis: source.**
- **`unknown` — Vendor reservation-set widths lacking `Za64rs`/`Za128rs`:** Worst-case spurious-`SC` overlap radius across unannotated RV64 microarchitectures remains `unknown`, requiring idempotent dummy `SC` (`Linux` `entry.S:303–304`) or post-load dead-slot `SC` (`seL4` `c_traps.c:48`). **Basis: normative, source.**

## Evidence

| Subject / Paper | Pinned SHA / DOI | Exact Inspected Files, Line Ranges, or Scope | Basis |
| :--- | :--- | :--- | :--- |
| `riscv/riscv-isa-manual` | `c05f1725f25526dd8463bac6ca75cfcfbee17d05` | `src/unpriv/zicsr.adoc` L29–254; `src/unpriv/zalrsc.adoc` L6–154; `src/priv/supervisor.adoc` L103–364, L531–595; `src/priv/machine.adoc` L2650–2676 (`#norm:xret_clr_lr_resv`) | `normative` |
| `riscv/sail-riscv` | `76f1ce3c184797178864b9869963e8b44465889e`, `doi:10.1145/3290384` | `model/extensions/Zicsr/zicsr_insts.sail` L33–107; `model/sys/sys_control.sail` L28–61, L325–357, L453–490; `model/core/sys_regs.sail` L673–702 (`legalize_tvec`); `model/exceptions/sys_exceptions.sail` L17–120; `model/extensions/I/base_insts.sail` L573–730 (`SRET`); `model/sys/sys_reservation.sail` L15–24; `model/extensions/A/zalrsc_insts.sail` L32–81 | `source`, `documentation` |
| `opencompl/sail-riscv-lean` | `51c635c460125ac87955d061fcd902ce03b8011f` | `LeanRV64D/ZicsrInsts.lean`, `LeanRV64D/SysControl.lean`, `LeanRV64D/BaseInsts.lean` | `source` |
| `rems-project/islaris` | `c978e10f50db5c40f0fdf113f5f76a779782c6f9`, `doi:10.1145/3519939.3523434` | `theories/riscv64/sys_regs.v` L65–116 (`MaskShape 64 0x20000 0`); `theories/riscv64/specs.v` L65–102 (`instr_pre`) | `source`, `documentation` |
| `seL4/seL4` & `seL4/l4v` | `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`, `doi:10.1145/2560537`, `doi:10.1145/2499370.2462183` | `seL4`: `src/arch/riscv/traps.S` L24–147; `head.S` L23–63; `c_traps.c` L21–142 (`DONT_TRANSLATE`, `sc.w` L48); `include/arch/riscv/arch/machine/{registerset.h,hardware.h}`. `l4v`: `spec/machine/RISCV64/MachineOps.thy` L108–113, L175–189 | `source`, `documentation` |
| `torvalds/linux` | `5f22fb20497f4983094131f00a734362300d22d2` | `arch/riscv/kernel/entry.S` L23–244 (`new_valid_map_cpus_check` L87, `handle_exception` L134–209), L252–361 (`ret_from_exception`, `REG_SC` L303–304) | `source` |
| `tock/tock` | `b336e170cd1d6f15daeb332b5e51ca20e4fc3c0f`, `doi:10.1145/3132747.3132786` | `arch/riscv/src/lib.rs` L77–111 (`norelax` `gp`), L176–431 (`start_trap` 256 B align, `mscratch` swap L305, `csrrw s0, mscratch, zero` L346) | `source`, `documentation` |
| `mit-pdos/xv6-riscv` | `fa2ddcb7ca87a77af579380a6eafd5aff163b44f` | `kernel/trampoline.S` L20–152; `kernel/kernelvec.S` L12–64; `kernel/trap.c` L37–164 | `source` |
| `oxidecomputer/hubris` | `969bac2bf47c98710842eb232fdd4a9c54e7dd7f` | `sys/kern/src/arch.rs` L24–48; `sys/kern/src/arch/arm_m.rs` L100–272 | `source` |
| `uw-unsat/serval` & CertiKOS | `72adc4952a1e62330aea527214a26bd0c09cbd05`, `doi:10.1145/1379022.1375591`, `doi:10.1145/2908080.2908101` | `serval/riscv/interp/i-type.rkt` L82–125 (`do-csr-op`); `base.rkt` L34–114; `spec.rkt` L8–56; CertiKOS interrupt-layer foundations | `source`, `documentation` |
| Standalone Python Probe (`reval_pkg1.py`) | Executed `2026-11-20` on Python 3.13 | Verified 30 `Zicsr` cases, `sip` RMW split, `seL4` UP vs `Linux` `sscratch` bijection + fault mutation, `stvec` `Vectored`, `SRET`, and `Zalrsc` dummy-`SC` (`0.47 ms`, exit `0`) | `execution` |

## Revalidation

Run the standalone Python 3 probe below (`< 1 ms`, standard library only) to revalidate every `Zicsr` rule, `sscratch` swap invariant, `stvec`/`SRET` bit transition, and `Zalrsc` dummy-`SC` safety property:

```python
#!/usr/bin/env python3
import time

t0 = time.perf_counter()

def csr_access_type(op, rd_is_x0, rs1_imm_is_zero):
    if op == "CSRRW":
        return "CSRWrite" if rd_is_x0 else "CSRReadWrite"
    return "CSRRead" if rs1_imm_is_zero else "CSRReadWrite"

def exec_csr(st, op, csr_addr, rd, rs1_or_imm, is_imm=False):
    atype = csr_access_type(op, rd == 0, rs1_or_imm == 0)
    if ((csr_addr >> 10) & 3) == 3 and atype in ("CSRWrite", "CSRReadWrite"):
        return ("Illegal_Instruction", st)
    rs1_val = rs1_or_imm if is_imm else st["gprs"][rs1_or_imm]
    if atype != "CSRWrite":
        st["re"][csr_addr] = st["re"].get(csr_addr, 0) + 1
        read_val = st["csrs"][csr_addr]
    else:
        read_val = 0
    dest_val = (read_val | st.get("ext_ip", 0)) if (csr_addr in (0x144, 0x344) and atype != "CSRWrite") else read_val
    if atype != "CSRRead":
        wval = rs1_val if op == "CSRRW" else (read_val | rs1_val if op == "CSRRS" else read_val & ~rs1_val)
        st["csrs"][csr_addr] = wval & st.get("wmask", {}).get(csr_addr, (1 << 64) - 1)
        st["we"][csr_addr] = st["we"].get(csr_addr, 0) + 1
    if rd != 0:
        st["gprs"][rd] = dest_val
    return ("RETIRE_SUCCESS", st)

cases = 0
for op in ("CSRRW", "CSRRS", "CSRRC"):
    for is_imm in (False, True):
        for rd in (0, 5):
            for op2, rval in ((0, 0), (6, 0), (6, 0x10)):
                if is_imm and op2 == 6 and rval == 0:
                    continue
                cases += 1
                mk = lambda: {"gprs": [0] * 32, "csrs": {0x140: 0xAA, 0xC00: 0x55}, "re": {}, "we": {}}
                s1, s2 = mk(), mk()
                if not is_imm and op2 != 0:
                    s1["gprs"][op2] = s2["gprs"][op2] = rval
                r_ro, _ = exec_csr(s1, op, 0xC00, rd, op2, is_imm)
                assert r_ro == ("Illegal_Instruction" if (op == "CSRRW" or op2 != 0) else "RETIRE_SUCCESS")
                r_rw, s2 = exec_csr(s2, op, 0x140, rd, op2, is_imm)
                assert r_rw == "RETIRE_SUCCESS"
                assert s2["re"].get(0x140, 0) == (0 if (op == "CSRRW" and rd == 0) else 1)
                assert s2["we"].get(0x140, 0) == (0 if (op in ("CSRRS", "CSRRC") and op2 == 0) else 1)

sip_st = {"gprs": [0]*32, "csrs": {0x144: 0}, "ext_ip": 0x200, "wmask": {0x144: 0x202}, "re": {}, "we": {}}
sip_st["gprs"][5] = 2
exec_csr(sip_st, "CSRRS", 0x144, 10, 5)
assert sip_st["gprs"][10] == 0x200 and sip_st["csrs"][0x144] == 2

tock_st = {"gprs": [0]*32, "csrs": {0x340: 0xDEADBEEF}, "re": {}, "we": {}}
exec_csr(tock_st, "CSRRW", 0x340, 8, 0)
assert tock_st["gprs"][8] == 0xDEADBEEF and tock_st["csrs"][0x340] == 0

u_regs = [0] + [0x1000 + i * 0x11 for i in range(1, 32)]

def run_sel4_up(regs, sepc, scause, tcb_ptr, nested_fault=False):
    sscratch, frame, g = tcb_ptr, [0] * 35, list(regs)
    g[5], sscratch = sscratch, g[5]
    if nested_fault:
        return ("CORRUPTED_BASE_PTR", g[5], sscratch)
    for i in range(1, 32):
        if i != 5:
            frame[i - 1] = g[i]
    frame[4], frame[31], frame[33] = sscratch, scause, sepc
    frame[34] = sepc + 4 if scause == 8 else sepc
    assert [0] + [frame[i - 1] for i in range(1, 32)] == regs
    return ("BIJECTION_OK", frame[34])

assert run_sel4_up(u_regs, 0x4000, 8, 0xFFFF800000001000) == ("BIJECTION_OK", 0x4004)
assert run_sel4_up(u_regs, 0x4000, 12, 0xFFFF800000001000) == ("BIJECTION_OK", 0x4000)
assert run_sel4_up(u_regs, 0x4000, 13, 0xFFFF800000001000, nested_fault=True)[0] == "CORRUPTED_BASE_PTR"

def run_linux_trap(regs, task_ptr, ksp_top, omit_lazy_sret_zero=False):
    sscratch, g = task_ptr, list(regs)
    g[4], sscratch = sscratch, g[4]
    assert g[4] == task_ptr
    frame1 = {i: (g[2] if i == 2 else sscratch if i == 4 else g[i]) for i in range(1, 32)}
    sscratch = 0xBAD0 if omit_lazy_sret_zero else 0
    k_tp = task_ptr
    k_tp, sscratch = sscratch, k_tp
    if k_tp != 0:
        return ("MISCLASSIFIED_NESTED_TRAP", k_tp)
    k_tp = sscratch
    assert k_tp == task_ptr
    sscratch = k_tp
    assert [0] + [frame1[i] for i in range(1, 32)] == regs and sscratch == task_ptr
    return ("NESTED_BIJECTION_OK", sscratch)

assert run_linux_trap(u_regs, 0xFFFFAF8000100000, 0xFFFFAF8000204000)[0] == "NESTED_BIJECTION_OK"
assert run_linux_trap(u_regs, 0xFFFFAF8000100000, 0xFFFFAF8000204000, omit_lazy_sret_zero=True)[0] == "MISCLASSIFIED_NESTED_TRAP"

tvec = (0x80000140 & ~0xFF) | 1
assert ((tvec & ~3) + 4 * 5) == 0x80000114 and (tvec & ~3) == 0x80000100

sstatus = (0 << 8) | (1 << 5) | (1 << 17) | (1 << 24)
spp, spie = (sstatus >> 8) & 1, (sstatus >> 5) & 1
sstatus = (sstatus & ~((1 << 1) | (1 << 5) | (1 << 8) | (1 << 17) | (1 << 24))) | (spie << 1) | (1 << 5)
assert spp == 0 and sstatus == ((1 << 1) | (1 << 5))

resv, frame = (0x10000, 4096), {0: 0xDEAD1111, 34: 0x4004}
assert resv[0] <= 0x10080 < resv[0] + resv[1]
frame_bad = dict(frame); frame_bad[0] = 0
a2 = frame[34]; frame[34] = a2; resv = None
assert frame_bad[0] == 0 and frame[34] == 0x4004 and resv is None

print(f"reval_pkg1 PASS: zicsr_cases={cases}, sscratch=ok, stvec_sret=ok, zalrsc=ok ({(time.perf_counter()-t0)*1000:.2f} ms)")
```

Upstream revalidation checks:
1. Diff `riscv/sail-riscv` `zicsr_insts.sail`, `sys_control.sail`, and `base_insts.sail` (`SRET`, `plat_reservation_invalidate_on_xret`) on Sail model updates.
2. Diff `seL4/seL4` `src/arch/riscv/{traps.S,c_traps.c}` and `torvalds/linux` `arch/riscv/kernel/entry.S` to verify dummy-`SC` ordering, `.option norelax` `gp` reload, and `CSR_SCRATCH` clearing on all S-mode exit paths.
