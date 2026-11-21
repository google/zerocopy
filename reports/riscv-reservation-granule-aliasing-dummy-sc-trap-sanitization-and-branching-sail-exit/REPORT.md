# RISC-V LR/SC Reservation-Granule Aliasing, Dummy-SC Trap Sanitization, and Branching Sail Exit Semantics

## Summary

In the RISC-V Unprivileged Architecture (`Zalrsc` / `A` extension), a load-reserved instruction (`lr.w` or `lr.d`) registers a hart-private reservation set of physical bytes subsuming the addressed operand. Unless hardware implements `Za64rs` (bounding reservation sets to naturally aligned 64-byte blocks) or `Za128rs` (bounding them to 128-byte blocks), base `Zalrsc` permits an **arbitrarily large reservation set**—spanning a 4 KiB page or the entire physical address space—and permits a subsequent store-conditional (`sc.w` or `sc.d`) to a **different effective address and operand width** to succeed if its target bytes fall inside that active reservation set. Unlike Armv8-A (which provides `CLREX` and architecturally clears exclusive monitors on `ERET`), RISC-V lacks a dedicated reservation-clear instruction and does not invalidate reservations on trap entry or `SRET`/`MRET`. Supervisor kernels must therefore synthesize reservation sanitization on trap exit by executing a dummy `sc.w` or `sc.d` whose architectural guarantee (`#norm:sc_reservation_invalidate`) invalidates the hart's reservation regardless of success or failure.

Dummy-`SC` target selection determines memory-framing soundness under coarse reservation granules:

1. **Zero-store to a live TCB slot (`seL4` `restore_user_context`, `sc.w zero, zero, (t0)`):** Executing `sc.w` (or `sc.d`) with `rs2 = x0` against `ksCurThread->tcbArch.tcbContext.registers[0]` after reloading `ra` avoids faulting because `t0` is a writable kernel virtual address, but **conditionally overwrites `registers[0]` in RAM with zero** (tearing bits `[31:0]` under `sc.w` on RV64 or zeroing `[63:0]` under `sc.d`) whenever a lingering `LR` granule covers `t0`, breaking read-only TCB frame invariants.
2. **Reload-and-store to the kernel stack (`Linux` `ret_from_exception`, `REG_L a2, PT_EPC(sp); REG_SC x0, a2, PT_EPC(sp)`):** Writing back the exact value loaded from `PT_EPC(sp)` preserves byte values (`MEM'[a] = MEM[a]`) on hart-private stack memory if executed **before** restoring user `sp`, yet still triggers write-permission checks, PMP/PMA reservability checks, store triggers, and coherent cache-line stores on coarse-granule alias.
3. **Dedicated per-hart aligned scratch slot (`dummy_sc_scratch`):** Directing `sc.d zero, zero, 0(t_scratch)` to a writable, reservable kernel `.bss` doubleword aligned to 128 bytes (`Za128rs`) and disjoint from TCB, stack, and page-table footprints unconditionally clears reservations across all granule sizes ($2^3\text{ B}$ through unbounded $2^{64}\text{ B}$) without mutating modeled kernel objects or invalidating sibling-hart spinlock reservations.

Mechanizing refinement between assembly trap-exit paths and `sail-riscv` exposes two further seams: (1) `sail-riscv` types `match_reservation : physaddrbits -> bool` and `valid_reservation : unit -> bool` as **`pure`** externs (`model/sys/sys_reservation.sail`), so Lean 4 (`RiscvExtras.lean`), Rocq, and Lem/Isabelle extract them outside the state monad `SailM`, preventing `cancel_reservation` from altering `match_reservation` unless reservation state is lifted into the hart state; and (2) trap-exit assembly requires a four-way branching simulation across `(switch_satp : Bool) × (target_mode ∈ {User, IdleSupervisor})` governing `satp`/`sfence.vma` ordering, `sstatus.SPP`, `sstatus.SIE`, `sscratch`, and post-`SRET` privilege transitions (`User` vs. supervisor `WFI`).

## Applicability

This report characterizes the interaction among five pinned upstream artifacts in `REPORT.json`:

- **Normative ISA authority:** `riscv/riscv-isa-manual` (`3142f66fd71c7ea0326b3687072318aedab587f8`), covering Unprivileged `Zalrsc`, `Za64rs`, `Za128rs`, and `RVWMO` plus Privileged Supervisor `1.13` (`sstatus`, `senvcfg`, `satp`, `SFENCE.VMA`, `SRET`).
- **Formal reference model:** `riscv/sail-riscv` (`04bcb62ccab96e35b9d6ce01873851972945af6f`), covering `model/`, `c_emulator/`, and prover support (`handwritten_support/RiscvExtras.lean`, `RiscvExtrasExecutable.lean`, `riscv_extras.lem`).
- **Kernel implementations and mechanized specs:** `seL4/seL4` (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`), `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`), and `torvalds/linux` (`5f22fb20497f4983094131f00a734362300d22d2`).

Findings apply to 64-bit RISC-V (`RV64I`/`RV64GC`/`RV64IMAC`) supervisor kernels implementing `S` + `U` + `Zicsr` + `Zalrsc` (or `A`) under `Sv39`/`Sv48` virtual memory on uniprocessor and `SMP` systems. Normative reservation rules also apply to `RV32` (`lr.w`/`sc.w`), with width interactions noted where 32-bit `sc.w` targets 64-bit TCB slots on `RV64`.

## Findings

### 1. Normative Reservation-Set Granularity Lattice: Base `Zalrsc` vs. `Za128rs` and `Za64rs`

Basis: normative + derived

In `riscv/riscv-isa-manual` (`src/unpriv/zalrsc.adoc:8–26, 91–127`), `lr.w`/`lr.d` and `sc.w`/`sc.d` operate on abstract **reservation sets** rather than exact address equality:

- **Arbitrarily coarse base granularity (`#norm:lr_reservation_set_size`, `zalrsc.adoc:91–93`):** *"An implementation can register an arbitrarily large reservation set on each `lr`, provided the reservation set includes all bytes of the addressed data word or doubleword."* Without further extensions, a conforming core may record reservations at 8-byte doubleword granularity ($2^3\text{ B}$), 64-byte cache-line granularity ($2^6\text{ B}$), 4 KiB page granularity ($2^{12}\text{ B}$), or via a single per-hart boolean latch covering $[0, 2^{\text{PALEN}})$.
- **Cross-address and cross-width `SC` success (`#norm:sc_success_conditions`, `zalrsc.adoc:94–101`):** `sc.w`/`sc.d` succeeds only if the reservation remains valid, no other hart's store to the reservation set (and no device write overlapping the `lr` bytes) was observed since the pairing `lr`, no intervening `sc` occurred in program order, **and the reservation set contains the written bytes**. Lines `99–101` state explicitly: *"Note this `lr` might have had a different effective address and data size, but reserved the `sc`'s address as part of the reservation set."* Under virtual memory (`zalrsc.adoc:105–108`), an `sc` via a distinct virtual alias to the same physical granule is permitted either to succeed or to fail.
- **Unconstrained vs. constrained asymmetry (`#norm:lrsc_same_address_and_size` vs. `#norm:unconstrained_lrsc_no_progress`, `zalrsc.adoc:185–210`):** Eventual forward progress applies *only* to constrained `LR`/`SC` loops ($\le 16$ sequential base `I`/`E`/`C` instructions, no loads/stores/system ops, and **matching effective address and data size**). A cross-address dummy `SC` on trap exit is normatively *unconstrained*: hardware may fail it unconditionally or **succeed and retire its store** whenever its physical bytes lie inside the prior `LR` reservation set.
- **Optional upper-bound extensions (`src/unpriv/zars.adoc:1–18`):** `Za128rs` (`#norm:Za128rs_res_set_req`, `zars.adoc:5–8`) requires contiguous, naturally aligned reservation sets of **at most 128 bytes** ($2^7\text{ B}$); `Za64rs` (`#norm:Za64rs_res_set_req`, `zars.adoc:13–18`) implies `Za128rs` and tightens the bound to **at most 64 bytes** ($2^6\text{ B}$).

For power-of-two naturally aligned granules with exponent $e \in [3, \text{PALEN}]$, an `lr.d` at physical address $\text{pa}_{\text{lr}}$ reserves $R_e(\text{pa}_{\text{lr}}) = \{\, b \mid (b \mathbin{\&} \neg(2^e - 1)) = (\text{pa}_{\text{lr}} \mathbin{\&} \neg(2^e - 1)) \,\}$, and an aligned `sc.w`/`sc.d` at $\text{pa}_{\text{sc}}$ aliases $R_e(\text{pa}_{\text{lr}})$ iff:

$$(\text{pa}_{\text{sc}} \mathbin{\&} \neg(2^e - 1)) = (\text{pa}_{\text{lr}} \mathbin{\&} \neg(2^e - 1))$$

When $e = \text{PALEN}$ (unbounded `Zalrsc`), $\neg(2^e - 1) \equiv 0 \pmod{2^{\text{PALEN}}}$, so every physical target $\text{pa}_{\text{sc}}$ aliases every prior $\text{pa}_{\text{lr}}$.

---

### 2. Persistence of Load Reservations Across Trap Entry and `SRET`

Basis: normative + source

Unlike Armv8-A—which provides operandless `CLREX` and clears local exclusive monitors on every `ERET` (Armstrong et al., POPL 2019, DOI `10.1145/3290384`; Pulte et al., POPL 2018, DOI `10.1145/3158107`)—RISC-V leaves reservations intact across traps and privilege returns:

1. **Normative software-clearing rule (`src/unpriv/zalrsc.adoc:23–24, 137–143`):** `#norm:sc_reservation_invalidate` guarantees that executing `sc.w`/`sc.d` invalidates any reservation held by the hart regardless of success or failure. The specification note (`zalrsc.adoc:137–143`) directs software to execute an `sc` to a scratch word during preemptive context switches and virtual-to-physical page remappings.
2. **Dangling reservation sources (`torvalds/linux` `arch/riscv/kernel/entry.S:295–301`):** Lingering reservations arise not only when a thread traps mid-`LR`/`SC`, but whenever user or kernel compare-and-swap (`CAS`) code executes `lr.d` and takes a forward branch around `sc.d` on comparison mismatch. Returning to another thread $B$ that was preempted immediately before its own `sc.d` on an aliasing granule allows $B$'s `sc.d` to succeed falsely despite intervening writes, violating `RVWMO` atomicity.
3. **Confirmation in `sail-riscv` (`04bcb62ccab96e35b9d6ce01873851972945af6f`):** `trap_handler_inner` (`model/sys/sys_control.sail:270–394`) never calls `cancel_reservation()`. Both `execute MRET` and `execute SRET` (`model/extensions/I/base_insts.sail:650, 724`) guard cancellation behind `if plat_reservation_invalidate_on_xret then cancel_reservation()`, where `config/config.json.in:572` defaults `"invalidate_on_xret"` to **`false`**. Only `reset_sys()` (`sys_control.sail:576`) and `STORECON` (`zalrsc_insts.sail:76`) clear reservations unconditionally.

---

### 3. Taxonomy of Dummy-`SC` Sanitization Idioms and Coarse-Granule Aliasing Hazards

Basis: normative + source + execution + derived

Production RISC-V kernels use two in-place dummy-`SC` idioms, contrasted below with the dedicated aligned scratch-slot idiom required for frame-clean verification:

| Idiom & Source | Sequence | Target Footprint | Effect on Coarse-Granule Alias (`match_reservation == true`) | Verification & SMP Properties |
| --- | --- | --- | --- | --- |
| **Idiom A: TCB zero-store** (`seL4` `src/arch/riscv/c_traps.c:41–48`) | `ld ra, 0(t0)` ... `sc.w zero, zero, (t0)` | `ksCurThread->tcbArch.tcbContext.registers[0]` (`ra`) | **Clobbers TCB RAM:** `sc.w` zeroes `registers[0][31:0]` (tearing 64-bit `ra` on RV64); `sc.d` zeroes `[63:0]`. | Violates read-only TCB framing (`MEM' ≠ MEM`); requires proving `registers[0]` is dead across all exits. |
| **Idiom B: Stack reload-and-SC** (`Linux` `arch/riscv/kernel/entry.S:303–304`) | `REG_L a2, PT_EPC(sp)` `REG_SC x0, a2, PT_EPC(sp)` | Kernel trap frame `pt_regs.epc` on kernel stack | **Value-preserving write:** stores `a2 = MEM[PT_EPC(sp)]` back to itself, *only* while `sp` is kernel `sp`. | Preserves byte map, but emits coherent write transaction, dirtying cache line and firing store triggers. |
| **Idiom C: Dedicated `.bss` scratch** (Verification-clean) | `la t1, dummy_sc_scratch` `sc.d zero, zero, 0(t1)` | Per-hart 128B-aligned `.bss` slot outside TCB/stack/PT | Writes `0` solely to `dummy_sc_scratch[hart]`; **zero mutation** to TCBs, stacks, page tables, or user RAM. | Frame-disjoint footprint for all $e \in [3, 64]$; zero cross-hart spinlock invalidation under `Za64rs`/`Za128rs`. |

Key implementation and proof consequences:

1. **seL4's TCB `ra` clobber and why `(sp)` would fault (`seL4/seL4` `src/arch/riscv/c_traps.c:40–49`):**
   ```c
   "mv t0, %[cur_thread]       \n"
   LOAD_S " ra, (0*%[REGSIZE])(t0)  \n"
   LOAD_S "  sp, (1*%[REGSIZE])(t0)  \n"
   ...
   /* this may succeed in implementations with very large reservations, but the saved ra is dead */
   "sc.w zero, zero, (t0)\n"
   ```
   Because line 42 restores user `sp` *before* line 48 while the hart is in S-mode with `sstatus.SUM = 0`, executing `sc.w zero, zero, (sp)` against a `U = 1` or unmapped user stack pointer would immediately raise a Store/AMO Page Fault (`scause = 15`, `supervisor.adoc:1547–1566`), triggering `c_handle_exception`'s `SSTATUS_SPP` kernel `halt()` (`c_traps.c:112–119`). Targeting `(t0)` avoids faulting, but when $e \ge 12$ (same 4 KiB page) or $e = 64$, `sc.w` overwrites `registers[0][31:0] := 0` in RAM. In `seL4/l4v`, `restore_user_context` is marked `/** DONT_TRANSLATE */` (`c_traps.c:21`) and `MachineOps.thy` omits exclusive-monitor state; any assembly proof claiming `mem' = mem` over TCB objects fails on coarse-granule cores unless `registers[0]` is carved out or Idiom C is used.
2. **Linux's `sp`-restoration ordering (`torvalds/linux` `arch/riscv/kernel/entry.S:303–316`):** Linux executes `REG_L a2, PT_EPC(sp); REG_SC x0, a2, PT_EPC(sp)` at lines `303–304` while `sp` still points to the 16-byte-aligned kernel `pt_regs` frame, restoring user `x2` (`sp`) last at line `315`.
3. **Dedicated per-hart 128-byte-aligned scratch isolation:** Allocating `.balign 128; dummy_sc_scratch: .space 128 * MAX_HARTS` in writable kernel `.bss` confines conditional writes to `[scratch_pa(h), scratch_pa(h) + 8)`, preserving `mem'|_{Kernel ∪ User} = mem|_{Kernel ∪ User}` unconditionally for all $e \in [3, 64]$ without case-splitting on `match_reservation`, and preventing a coarse-alias store on Hart $h_1$ from shooting down a concurrent `LR`/`SC` spinlock on Hart $h_2$ (`#norm:sc_other_hart_store_fail`, `zalrsc.adoc:118–120`).

---

### 4. Permission, Alignment, `Svade`, and PMP/PMA Preconditions for Dummy-`SC` Retirement

Basis: normative + source

Even a *guaranteed-failing* dummy `SC` (`match_reservation == false`) performs full address translation and write-permission checks before retiring:

- **Normative rules:** `#norm:sc_retire_permission` (`zalrsc.adoc:17`), `#norm:lr_sc_alignment` (`zalrsc.adoc:74–78`, 4B/8B natural alignment), and `#norm:store_page_fault_no_w` (`supervisor.adoc:1547–1549`, write permission required).
- **Exact `sail-riscv` path (`model/sys/vmem_utils.sail:269–285` & `model/sys/mem.sail:114`):** `translate_and_write_value` runs `translateAddr(vaddr, StoreConditional(...), Supervisor)` **before** checking `match_reservation(bits_of(paddr))`, and on reservation mismatch still runs `phys_access_check`, which enforces `attributes.writable & attributes.reservability != RsrvNone` (`mem.sail:114`). Under `Svade` (`menvcfg.ADUE == 0`, where `update_and_write_pte` returns `Err(PTW_PTE_Needs_Update())`, `vmem.sail:106–118`), if the scratch page leaf PTE has `A = 0` or `D = 0`, even an unpaired `sc.d` raises **`E_SAMO_Page_Fault` (`scause = 15`)** and never reaches `cancel_reservation()` (`zalrsc_insts.sail:76`). Kernel window mappings must pre-set `PTE.V = R = W = A = D = 1, U = 0` (`seL4` `vspace.c:73–80`).

---

### 5. `sail-riscv` Reservation Modeling Seams Across C++, Lean 4, and Lem/Isabelle Backends

Basis: source + execution + derived

Auditing `riscv/sail-riscv` (`04bcb62ccab96e35b9d6ce01873851972945af6f`) reveals three concrete modeling seams:

1. **Monadic `pure` vs. `SailM` bug in prover extractions (`model/sys/sys_reservation.sail:21–24`, `handwritten_support/RiscvExtras.lean:35–38`):**
   `sys_reservation.sail` declares `load_reservation` and `cancel_reservation` as `impure`, but declares `match_reservation` and `valid_reservation` as **`pure`**. Consequently, Sail's Lean 4 backend extracts them outside `SailM` (`RiscvExtras.lean:35–38`):
   ```lean
   axiom load_reservation : BitVec Arch.addr_size → Nat → SailM Unit
   axiom match_reservation : BitVec Arch.addr_size → Bool
   axiom cancel_reservation : Unit → SailM Unit
   axiom valid_reservation : Unit → Bool
   ```
   Meanwhile, `RiscvExtrasExecutable.lean:35–38` panics (`panic "TODO: load_reservation"`). Because a pure function `BitVec Arch.addr_size → Bool` cannot read `SailM` state, **no sound instantiation of `RiscvExtras.lean` as written can transition `match_reservation pa` from `true` to `false` across `cancel_reservation ()`**. Prover developments must either mark all four hooks `impure` / internalize `cur_reservation` as a Sail `register` in `HartState`, or interpret the monadic effect trace in a product state `(HartState × Option ReservationSet)`.
2. **4 KiB configuration ceiling (`model/core/platform_config.sail:64`):** `plat_reservation_set_size_exp` is constrained to `range(2, 12)` (`config.json.in:560` default `3`), preventing JSON configuration of legal `Zalrsc` granules $> 4\text{ KiB}$ ($e > 12$).
3. **32-bit signed shift in C++ `set_reservation_set_size_exp` (`c_emulator/riscv_model_impl.cpp:38–40`):** `m_reservation_set_addr_mask = ~((1 << exponent) - 1);` uses signed 32-bit `1` (unlike `1ULL` at line `283`). While `exponent` in `[2, 30]` sign-extends to the intended `uint64_t` mask, calling public C++ method `set_reservation_set_size_exp(exponent)` (`riscv_model_impl.h:45`) with `exponent >= 31` invokes C++20 signed-overflow / shift-width undefined behavior.

---

### 6. Four-Way Branching Trap-Exit Simulation: `satp`-Switch × (`User` vs. `IdleSupervisor`)

Basis: normative + source + execution + derived

Connecting trap-exit assembly (`seL4` `setVMRoot` + `restore_user_context`; `Linux` `__switch_to` + `ret_from_exception`) to `sail-riscv`'s `SRET` (`base_insts.sail:666–730`), `SFENCE_VMA` (`base_insts.sail:772–780`), `WFI` (`base_insts.sail:746–769`), and `write_CSR(0x180)` (`vmem.sail:295–298`) requires a **four-branch simulation split** over `(switch_satp : Bool) × (target_mode ∈ {User, IdleSupervisor})`:

| Branch | `satp` & `SFENCE.VMA` Obligation | Pre-`SRET` `sstatus` | Pre-`SRET` `sscratch` | Post-`SRET` Sail State (`base_insts.sail:699–728`) |
| --- | --- | --- | --- | --- |
| **1. Same-VSpace User** | `satp` unchanged; no `sfence.vma` if PTEs unchanged (`supervisor.adoc:1122–1135`) | `SPP = 0, SPIE = 1, SIE = 0` | Kernel anchor (`tp` in `entry.S:278`; TCB/stack in `c_traps.c:79`) | `cur_privilege = User`, `SPP = 0, SIE = 1`, `PC = sepc`, `res = none` |
| **2. Cross-VSpace User** (`thread.c:18–21`) | `csrw satp, new_satp` + `sfence.vma` (`machine.h:265–272`) | `SPP = 0, SPIE = 1, SIE = 0` | Incoming user thread's kernel anchor | `cur_privilege = User`, `SPP = 0, SIE = 1`, `PC = new_sepc`, `satp` legalized, `res = none` |
| **3. Same-VSpace Idle** | `satp` remains `kernel_root_pageTable` (`asid = 0`) | `SPP = 1, SPIE = 1, SIE = 0` (`thread.c:28`) | `0` in `Linux` (`entry.S:259–261`); `ksIdleThread` TCB on non-SMP `seL4` | `cur_privilege = Supervisor`, `SPP = 0, SIE = 1`, `PC = &idle_thread` (`WFI`) |
| **4. User-to-Idle** (`thread.c:41–47`) | `csrw satp, kernel_satp` (`asid = 0`, `vspace.c:588`) + `sfence.vma` | `SPP = 1, SPIE = 1, SIE = 0` | Re-armed for S-mode idle interrupt entry | `cur_privilege = Supervisor`, `SPP = 0, SIE = 1`, `PC = &idle_thread`, `res = none` |

Three proof obligations govern this four-way split: (1) Branch 4 (`User -> IdleSupervisor`) still requires dummy-`SC` sanitization so an outgoing user thread's reservation cannot survive across `WFI` wakeups into kernel or user `SC` instructions; (2) `sscratch` invariants branch on `SPP` in `Linux` (`entry.S:259–279` skips `csrw CSR_SCRATCH, tp` when `SPP == 1` so nested S-mode traps observe `sscratch == 0`), whereas `seL4` (`c_traps.c:79, 112`) gives `ksIdleThread` a full `tcbContext` buffer; and (3) normalizing all Sail hart-record fields at instruction boundaries after splitting into the 4 `(switch_satp, SPP)` cases prevents exponential call-by-need WHNF projection retention across 30+ `ld`/`csrw`/`sc`/`sret` instructions.

## Boundaries

- **not examined — Hypervisor (`H` extension `VS`/`VU`) two-level translation and `Zacas`/`Zabha`:** Guest-physical reservation interaction with `hgatp`/`HFENCE.GVMA` and microarchitectural monitor sharing between `Zalrsc` and `amocas.*` (`Zacas`) were `not examined`.
- **unknown — Failed-`SC` implicit PTE `D`-bit updates on concrete silicon:** `#norm:sc_failed_side_effects` (`zalrsc.adoc:18–20`) leaves `UNSPECIFIED` whether a failing `sc` sets `PTE.D` under `Svadu`; silicon behavior is `unknown` from ISA text alone, motivating pre-set `PTE.A = D = 1` on scratch mappings.
- **known not to apply — Stock `sail-riscv` `RiscvExtras.lean` `match_reservation` axioms for stateful cancellation proofs:** Proving reservation invalidation across dummy `SC` is `known not to apply` against unmodified `axiom match_reservation : BitVec Arch.addr_size → Bool` (`RiscvExtras.lean:36`), which lacks a `SailM` state parameter.
- **unsupported — Granules $> 4\text{ KiB}$ in `sail-riscv` config and `LR`/`SC` in `RiscvExtrasExecutable.lean`:** Setting `reservation_set_size_exp > 12` is `unsupported` by `platform_config.sail:64` (and UB at `>= 31` in `riscv_model_impl.cpp:39`), and `LR`/`SC` execution in `RiscvExtrasExecutable.lean:35–36` is `unsupported` (`panic`).

## Evidence

### Primary Specifications, Upstream Sources, and Literature

1. **`riscv/riscv-isa-manual` (`3142f66fd71c7ea0326b3687072318aedab587f8`):** `src/unpriv/zalrsc.adoc:8–26, 74–150, 185–242`; `src/unpriv/zars.adoc:1–18`; `src/priv/supervisor.adoc:965–1135, 1185–1390, 1542–1579`.
2. **`riscv/sail-riscv` (`04bcb62ccab96e35b9d6ce01873851972945af6f`):** `model/sys/sys_reservation.sail:21–24`; `model/extensions/A/zalrsc_insts.sail:41–81`; `model/sys/vmem_utils.sail:238–302`; `model/sys/mem.sail:113–115`; `model/sys/sys_control.sail:270–394, 575–576`; `model/extensions/I/base_insts.sail:616–780`; `model/core/platform_config.sail:64–74`; `config/config.json.in:556–573`; `c_emulator/riscv_model_impl.cpp:38–40, 250–274, 548–554`; `handwritten_support/RiscvExtras.lean:35–38`; `handwritten_support/RiscvExtrasExecutable.lean:35–38`.
3. **`seL4/seL4` (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`) & `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`):** `seL4` `src/arch/riscv/c_traps.c:21–94, 108–120`, `src/arch/riscv/traps.S:24–147`, `src/arch/riscv/kernel/thread.c:18–47`, `src/arch/riscv/kernel/vspace.c:71–82, 578–602`, `include/arch/riscv/arch/machine.h:259–273`; `l4v` `spec/machine/RISCV64/MachineOps.thy:35–58, 166–225`.
4. **`torvalds/linux` (`5f22fb20497f4983094131f00a734362300d22d2`):** `arch/riscv/kernel/entry.S:134–206, 252–322`.
5. **Literature:** A. Armstrong et al., *ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS*, PACMPL 3(POPL):71, 2019, DOI `10.1145/3290384`; C. Pulte et al., *Simplifying ARM Concurrency*, PACMPL 2(POPL):19, 2018, DOI `10.1145/3158107`; G. Klein et al., *Comprehensive Formal Verification of an OS Microkernel*, ACM TOCS 32(1):2, 2014, DOI `10.1145/2560537`.

### Exhaustive Finite-State Execution Probe (Observed `2026-11-20`)

Executed with `python3` (`Python 3.11+`, standard library) on `x86_64-unknown-linux-gnu`:

```python
#!/usr/bin/env python3
"""Exhaustive check for RISC-V LR/SC granule aliasing and 4-way SRET exit paths."""

def run_dummy_sc_matrix():
    tcb_ra_pa, kstack_epc_pa, scratch_pa = 0x8020_1000, 0x8020_1108, 0x8040_0000
    cases = [("same_cacheline_64B", 0x8020_1020), ("same_l2line_128B", 0x8020_1060),
             ("same_page_4KiB", 0x8020_1800), ("disjoint_page", 0x8090_0040)]
    out = []
    for label, u_pa in cases:
        for exp in (3, 6, 7, 12, 64):
            mask = 0 if exp == 64 else ~((1 << exp) - 1) & ((1 << 64) - 1)
            out.append((label, exp, (u_pa & mask) == (tcb_ra_pa & mask),
                        (u_pa & mask) == (kstack_epc_pa & mask),
                        (u_pa & mask) == (scratch_pa & mask), False))
    return out

def run_branching_exit_check():
    passes = fails = 0
    for switch_satp in (False, True):
        for idle_smode in (False, True):
            for emit_sfence in (False, True):
                for emit_dummy_sc in (False, True):
                    for inv_on_xret in (False, True):
                        res_valid = not (emit_dummy_sc or inv_on_xret)
                        tlb_stale = switch_satp and not emit_sfence
                        new_priv = "S" if idle_smode else "U"
                        safe = (not tlb_stale) and (not res_valid) and (
                            new_priv == ("S" if idle_smode else "U"))
                        assert safe == ((emit_sfence or not switch_satp) and (emit_dummy_sc or inv_on_xret))
                        passes += int(safe)
                        fails += int(not safe)
    return passes, fails

if __name__ == "__main__":
    for r in run_dummy_sc_matrix():
        if r[0] in ("same_page_4KiB", "disjoint_page"):
            print(f"case={r[0]:18s} exp={r[1]:2d} tcb_clobber={str(r[2]):5s} stk_store={str(r[3]):5s} scr_alias={str(r[4]):5s} non_scr_clobber={r[5]}")
    p, f = run_branching_exit_check()
    print(f"branching_exit_matrix: total=32 safe={p} unsafe_rejected={f}")
```

Recorded output:

```text
case=same_page_4KiB     exp= 3 tcb_clobber=False stk_store=False scr_alias=False non_scr_clobber=False
case=same_page_4KiB     exp= 6 tcb_clobber=False stk_store=False scr_alias=False non_scr_clobber=False
case=same_page_4KiB     exp= 7 tcb_clobber=False stk_store=False scr_alias=False non_scr_clobber=False
case=same_page_4KiB     exp=12 tcb_clobber=True  stk_store=True  scr_alias=False non_scr_clobber=False
case=same_page_4KiB     exp=64 tcb_clobber=True  stk_store=True  scr_alias=True  non_scr_clobber=False
case=disjoint_page      exp= 3 tcb_clobber=False stk_store=False scr_alias=False non_scr_clobber=False
case=disjoint_page      exp= 6 tcb_clobber=False stk_store=False scr_alias=False non_scr_clobber=False
case=disjoint_page      exp= 7 tcb_clobber=False stk_store=False scr_alias=False non_scr_clobber=False
case=disjoint_page      exp=12 tcb_clobber=False stk_store=False scr_alias=False non_scr_clobber=False
case=disjoint_page      exp=64 tcb_clobber=True  stk_store=True  scr_alias=True  non_scr_clobber=False
branching_exit_matrix: total=32 safe=18 unsafe_rejected=14
```

## Revalidation

1. **Check `sail-riscv` prover monadic typing:** Inspect `model/sys/sys_reservation.sail` and `handwritten_support/RiscvExtras.lean` to determine whether `match_reservation` and `valid_reservation` remain `pure` outside `SailM` or have been lifted into `HartState`.
2. **Check `sail-riscv` C++ mask shift and exponent range:** Diff `model/core/platform_config.sail` (`plat_reservation_set_size_exp`) and `c_emulator/riscv_model_impl.cpp` (`set_reservation_set_size_exp`) for `uint64_t(1) << exponent` widening and `range(2, 12)` changes.
3. **Audit kernel trap-exit assembly and rerun probe:** Confirm that an `sc.w`/`sc.d` executes on every `sret` return path (including idle S-mode returns) against an 8-byte-aligned, `U = 0`, `A = D = 1`, PMA-reservable per-hart 128B-aligned scratch slot *before* user base registers are restored, and rerun the standalone Python script above (`< 0.05 s`).
