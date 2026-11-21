# Verified Rust-to-Assembly Boot ABI Handovers, Callee-Saved Frames, and First-SRET Seams on RISC-V

## Summary

End-to-end formal verification of a RISC-V operating system kernel written in Rust with assembly entry/exit stubs must bridge three cross-language boundaries: (1) firmware hand-off (`MRET` from OpenSBI into assembly `_start`), (2) the assembly-to-Rust initialization call (`_start` into `extern "C" fn init_kernel`) and its return to the first user-mode `sret`, and (3) recurring trap-entry/trap-return marshalling between assembly (`trap_entry` / `restore_user_context`) and `extern "C"` Rust handlers. Across these boundaries, neither Rust type-checking nor an isolated MIR/LLVM function proof guarantees architectural soundness unless machine-level calling-convention, stack-frame, and Supervisor CSR invariants match identically on both sides of every jump.

Primary-source inspection of the RISC-V SBI, ELF psABI, Privileged ISA, OpenSBI, `rustc_target`, `seL4`, `Asterinas`, `CompCert`, and `CakeML`/`Pancake` establishes four load-bearing verification contracts:

1. **Minimal SBI boot postconditions and CSR sanitization before first `sret`:** The RISC-V SBI Hart State Management specification (`ext-hsm.adoc:93–102`) defines **only four** architectural values on S-mode entry: `satp = 0`, `sstatus.SIE = 0`, `a0 = hartid`, and `a1 = opaque` (device-tree physical address), leaving **all other GPRs and supervisor CSRs undefined**. OpenSBI (`sbi_hart.c:36–48, 84–171`) enables `mstatus.FS` when FPU hardware is present, sets `scounteren = 0x02`, enables `menvcfg.{CBZE, CBCFE, CBIE, PBMTE}`, and never initializes `senvcfg`, `stvec`, `sscratch`, `sp`, or `gp`. Assembly `_start` must therefore initialize `gp` under `.option norelax`, set a 16-byte-aligned per-hart `sp`, zero `.bss` *before* entering Rust, install `stvec` *before* writing potentially gated CSRs (`senvcfg` under `Smstateen`), and sanitize `senvcfg = 0`, `scounteren`, and `sstatus.FS` prior to the first `sret` so user mode cannot execute unmediated cache-block invalidation (`CBO.INVAL`) or zeroing (`CBO.ZERO`).
2. **The $2 \times \text{XLEN}$ `extern "C"` aggregate-return cliff and `LP64` vs. `LP64D` ABI hazard:** Under the RISC-V psABI (`riscv-cc.adoc:231–318`) and `rustc`'s `classify_ret` (`compiler/rustc_target/src/callconv/riscv.rs:216–281`), a `#[repr(C)]` integer struct of size $\le 16\text{ B}$ (`KernelRet2`) returns directly in `(a0, a1)` while preserving entry arguments `(a0, a1)`. Adding a third 8-byte word (`24 B > 2 * XLEN`, `KernelRet3`) triggers `arg.make_indirect()`, silently **repurposing `a0` on entry as a caller-allocated output pointer**, shifting explicit arguments to `(a1, a2)`, and **not** guaranteeing that `a0` retains the buffer pointer upon `ret` (`riscv-cc.adoc:315–317`). Calling a `24 B`-returning `extern "C"` Rust entrypoint from assembly with SBI's `a0 = hartid = 0` causes Rust to execute `sd` stores to physical address `0x0`. Moreover, compiling kernel Rust for `riscv64gc-unknown-none-elf` (`LP64D`, `flen = 64`) rather than `riscv64imac-unknown-none-elf` (`LP64`, `flen = 0`) permits LLVM to emit `F`/`D` instructions that fault (`scause = 2`) whenever S-mode runs with `sstatus.FS = Off`.
3. **Callee-saved register framing and CSR opacity across pure Rust:** Standard RISC-V `extern "C"` calls preserve `sp` (`x2`, 128-bit aligned), `s0`–`s1` (`x8`–`x9`), and `s2`–`s11` (`x18`–`x27`), treat `gp` (`x3`) and `tp` (`x4`) as unallocatable fixed registers (`riscv-cc.adoc:16–39`), and clobber `ra`, `t0`–`t6`, and `a0`–`a7` (`Conventions1.v:35–73`). Because compiler-generated Rust without inline `asm!` emits zero `Zicsr` or privileged `SYSTEM` instructions, `senvcfg`, `sstatus`, `stvec`, `sscratch`, and `satp` are provably frame-invariant across pure Rust functions whenever `sstatus.SIE == 0`.
4. **Non-vacuity of composed multi-language refinement:** Relational composition of assembly entry ($\mathcal{R}_{\text{boot}}$), Rust initialization ($\mathcal{R}_{\text{rust}}$), and assembly exit ($\mathcal{R}_{\text{sret}}$) becomes vacuously true if intermediate boundary invariants (`16 B` `sp` alignment, zeroed `.bss`, disjoint stack/heap/TCB memory footprints, `sstatus.SIE = 0`, `senvcfg = 0`) are mutually inconsistent. Following `CompCert` (`Smallstep.v`), `CertiKOS`, and `Pancake`, end-to-end theorems require an explicit concrete initial-state witness theorem proving reachability of a valid post-`sret` user state from arbitrary SBI-compliant reset states.

## Applicability

This report governs the composition of the ten pinned upstream specifications, compilers, firmwares, and OS trees recorded in `REPORT.json`:

- **Normative ABI, SBI, and ISA specifications:** `riscv-non-isa/riscv-elf-psabi-doc` (`56561cb3e7330fe99a98fd27457229707b2786ae`), `riscv-non-isa/riscv-sbi-doc` (`8a545effe9b50484ff897d9815d7d9015cdef203`), and `riscv/riscv-isa-manual` (`3142f66fd71c7ea0326b3687072318aedab587f8`).
- **Rust language and compiler ABI lowering:** `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`) and `rust-lang/rust` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`), empirically verified via execution on `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)` (LLVM `22.1.6`).
- **Firmware and OS boot/trap implementations:** `riscv-software-src/opensbi` (`61f1973bd50338b36c52dc34006f76d464ca4f34`), `seL4/seL4` (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`), and `asterinas/asterinas` (`12374d1337d21f2d0dbe39c5cab340b41c58e553`).
- **Mechanized calling-convention and simulation frameworks:** `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`) and `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`, including `pancake/`).

Findings apply to 64-bit bare-metal RISC-V supervisor kernels (`RV64IMAC` / `LP64` and `RV64GC` / `LP64D`) booting via SBI v0.2+ HSM or ELF loaders under `Sv39`/`Sv48` virtual memory. `RV32` (`ILP32`/`ILP32D`) follows analogous $2 \times \text{XLEN} = 8\text{ B}$ thresholds where noted; vector calling conventions (`riscv_vector_cc`) and stack unwinding (`extern "C-unwind"`) are bounded under **Boundaries**.

## Findings

### 1. Firmware-to-`_start` Entry Contract and Pre-Rust Bootstrap Obligations

Basis: normative + source + derived

A verified boot chain begins at supervisor `_start` immediately after M-mode firmware executes `mret`. Comparing the normative SBI specification against OpenSBI, `seL4`, and `Asterinas` exposes a wide gap between firmware postconditions and Rust's entry preconditions:

1. **Normative SBI HSM entry state (`riscv-non-isa/riscv-sbi-doc` `src/ext-hsm.adoc:93–102, 233–242`):** Both `sbi_hart_start` and non-retentive `sbi_hart_suspend` resume guarantee **only** `satp = 0` (`Bare` physical addressing), `sstatus.SIE = 0`, `a0 = hartid`, and `a1 = opaque`, leaving *"All other registers ... in an undefined state."*
2. **Residual CSR state left by OpenSBI (`riscv-software-src/opensbi` `lib/sbi/sbi_hart.c:27–186`):** In `mstatus_init`, OpenSBI sets `mstatus.FS` (`lines 36–37`) and `mstatus.VS` (`lines 40–41`) when hardware supports `F`/`D`/`V`, writes `CSR_SCOUNTEREN = 0x02` (`line 48`), sets `SMSTATEEN0_HSENVCFG` in `mstateen0` when `Smstateen` is present (`line 88`; if omitted by another firmware, S-mode `senvcfg` access raises illegal-instruction), and sets `menvcfg` bits `CBZE`, `CBCFE`, `CBIE_INV` (`0b11`, full U-mode cache invalidation without writeback), and `PBMTE` while defaulting to `Svade` (`ADUE = 0`, `lines 136, 150–171`). OpenSBI **never initializes `senvcfg` (`0x10A`), `stvec` (`0x105`), or `sscratch` (`0x140`)**.
3. **Six ordered assembly preconditions before calling Rust (`seL4` `head.S:23–52`, `Asterinas` `bsp_boot.S:36–213`, `rust-lang/reference` `external-blocks.md:74–76`):**
   - **Instruction fence (`fence.i`, `seL4` `head.S:24`):** Synchronizes instruction fetch with prior loader code stores.
   - **Relaxation-safe `gp` initialization (`seL4` `head.S:25–29`, `Asterinas` `bsp_boot.S:30–32, 206`):** Under `.option push; .option norelax`, `_start` must set `gp` (`__global_pointer$` or per-CPU `__cpu_local_start`) before relaxed global accesses or Rust calls (`riscv-cc.adoc:34–39`).
   - **Bootstrap page tables and `sfence.vma` (`Asterinas` `bsp_boot.S:100–138`):** High-half kernels populate identity and high-half PTEs with `PTE_VRWXAD` (`bsp_boot.S:15`), execute `sfence.vma` (`line 101`) to order explicit PTE stores before walker reads (`supervisor.adoc:1190–1196`), write `satp` with WARL readback verification (`lines 108–125`, `supervisor.adoc:1050–1052`), and execute `sfence.vma` (`line 131`) before jumping to virtual addresses.
   - **`.bss` zeroing prior to Rust entry (`Asterinas` `bsp_boot.S:191–202`, `OpenSBI` `fw_base.S:197–202`):** `external-blocks.md:75` mandates that every immutable `static` be initialized *before any Rust code executes*; deferring `.bss` zeroing into Rust violates initial abstract-machine validity.
   - **16-byte-aligned disjoint per-hart `sp` (`seL4` `head.S:30–40`, `riscv-cc.adoc:319–326`):** `sp % 16 == 0` is mandatory at procedure entry, with disjoint per-core slices `stack_base + (c + 1) * 2^STACK_BITS` on SMP.
   - **Ordered `stvec` installation before `csrw senvcfg, zero`:** Because OpenSBI enables `menvcfg.CBIE = 0b11` and `CBZE = 1`, failing to write `csrw senvcfg, zero` (not merely `csrci senvcfg, 1`, which clears bit 0 `FIOM` while leaving `CBIE` `[5:4]`, `CBCFE` `[6]`, `CBZE` `[7]`, and `PMM` `[33:32]` armed, `supervisor.adoc:794–805`) lets U-mode wipe dirty supervisor cache lines after the first `sret`. Setting `stvec` *before* `csrw senvcfg, zero` ensures clean trapping if `mstateen0.ENVCFG == 0`.

---

### 2. Why Verified Kernels Split `init_kernel` Return from `restore_user_context` (`First SRET`)

Basis: source + derived

OS kernels follow two control-flow structures from Rust/C initialization to the first `sret`:

- **Divergent Rust boot (`Asterinas` `boot/mod.rs:147` & `trap/trap.S:119–185`):** `unsafe extern "C" fn riscv_boot(...) -> !` never returns to `bsp_boot.S`, instead calling assembly `run_user(regs: &mut RawUserContext)` (`trap.S:120`), which saves 14 kernel words (`s0`–`s11`, `ra`, `gp`), switches `sp` to `a0`, writes `sscratch = sp`, loads user CSRs/GPRs, and executes `sret`.
- **Returning `init_kernel` + assembly tail-dispatch (`seL4` `head.S:52–63` & `boot.c:451–499`):** `_start` executes `jal init_kernel; la ra, restore_user_context; jr ra`, keeping `init_kernel` as a normal returning function and isolating `restore_user_context` (`/** DONT_TRANSLATE */`, `c_traps.c:21`) in assembly glue.

For mechanized Rust verification, the **returning `init_kernel` seam** yields two major compositional simplifications: (1) `init_kernel` satisfies a terminating Hoare triple `{Pre_boot} init_kernel {Post_init}` inside standard S-mode Rust/MIR semantics without embedding privilege-mode switches (`Supervisor -> User`) into MIR execution; and (2) when `init_kernel` executes `ret`, all local Rust stack frames are popped (`sp == sp_entry`) and all Tree Borrows / Stacked Borrows reference protectors have expired cleanly, allowing `restore_user_context` to reset the kernel stack for subsequent traps without invalidating live Rust borrows.

---

### 3. The `extern "C"` `KernelRet` $2 \times \text{XLEN}$ Cliff and `LP64` vs. `LP64D` Lowering Rules

Basis: normative + source + execution

ABI agreement between assembly stubs and returning `extern "C"` Rust handlers is governed by `riscv-elf-psabi-doc` (`riscv-cc.adoc:178–318`) and `rust-lang/rust` (`compiler/rustc_target/src/callconv/riscv.rs:216–281, 417–450`):

| Return Type (`#[repr(C)]`, RV64) | Size | `rustc` `classify_ret` (`riscv.rs:254–274`) | Entry Argument Registers (`hart_id`, `dtb_pa`) | Return Location on `ret` | Assembly Seam Hazard |
| --- | ---: | --- | --- | --- | --- |
| `usize` / `*mut Tcb` | `8 B` | `PassMode::Direct` (`Reg::i64()`) | `a0`, `a1` | `a0` | Safe; `i32` and `u32` both sign-extend (`ArgExtension::Sext`, `riscv.rs:404–411`). |
| `KernelRet2 { pc, satp }` | `16 B` | `Uniform::new(Reg::i64(), 16B)`, returns `false` | `a0`, `a1` | `a0 = pc`, `a1 = satp` | Safe direct register-pair return (`riscv-cc.adoc:234–237, 310`). |
| `KernelRet3 { pc, satp, sstatus }` | `24 B` | `arg.make_indirect()`, returns `true` (`avail_gprs -= 1`) | **`a0 = &mut ret_buf`**, **`a1 = hart_id`**, **`a2 = dtb_pa`** | Stored to `0(a0_in)..24(a0_in)`; **exit `a0` UNSPECIFIED** | **Writes 24B to `hart_id` (`0x0`) if assembly omits `sret` pointer in `a0`; exit `a0 != &ret_buf`!** |

Three compiler-verified traps arise at this boundary:

1. **Indirect-return (`sret`) hijacking of `a0` and non-echoed `a0` on exit:** When `total.bits() > 2 * xlen` (`riscv.rs:254`), `classify_ret` calls `arg.make_indirect()` and `compute_abi_info` decrements `avail_gprs` (`riscv.rs:432–434`). As shown in **Evidence** (`rustc 1.98.0-nightly`), `handover_ret3` saves entry `a0` into `s1`, reads `hart_id` from `a1` and `dtb_pa` from `a2`, writes `sd` fields to `0(s1)..16(s1)`, and returns with `entry_pc` (not `s1`) in `a0`—confirming `riscv-cc.adoc:315–317` (*"software should not assume that a0 will hold the address of the return value on return"*, unlike x86-64 System V `%rax`). Assembly-facing `KernelRet` structs must stay $\le 16\text{ B}$ or use an explicit `*mut TrapFrame` argument in `a0`.
2. **Unsigned 32-bit sign-extension on RV64 (`riscv-cc.adoc:183–185`, `riscv.rs:403–415`):** On RV64, **both `i32` and `u32` parameters require sign-extension from bit 31** (`ArgExtension::Sext`). Passing a 32-bit unsigned value (`uint32_t dtb_size` in `seL4` `boot.c:457`) loaded with zero-extending `lwu` when bit 31 is set violates LLVM's `signext` assumption; assembly boundaries should pass `usize` (`u64`).
3. **`LP64D` (`riscv64gc-unknown-none-elf`) vs. `LP64` (`riscv64imac-unknown-none-elf`) with `sstatus.FS = Off`:** `LlvmAbi::Lp64d` sets `flen = 64` (`riscv.rs:424`), enabling FP register allocation (`fa0`–`fa7`, `fs0`–`fs11`) and `zcd` instructions. Because kernels disable S-mode FPU access (`seL4` `boot.c:138` `set_fs_off()`; `Asterinas` `trap.S:80` `csrrc ... SSTATUS_FS_MASK`), any emitted FP instruction traps with `Illegal Instruction` (`scause = 2`). Bare-metal Rust kernels must target `riscv64imac-unknown-none-elf` (`LP64`, `flen = 0`) or `-C target-feature=-f,-d`.

---

### 4. Callee-Saved Register Frames and Supervisor CSR Preservation Across Rust

Basis: normative + source + derived

The cross-language frame contract partitions machine state across `jal init_kernel` / `jal rust_trap_handler` into three classes:

1. **Callee-saved (`sp`, `s0`–`s11`) and unallocatable (`gp`, `tp`) GPRs:** `riscv-cc.adoc:16–26, 166–168` and `CompCert` `riscV/Conventions1.v:35–65` (`int_callee_save_regs := R8 :: R9 :: R18 .. R27`, plus `sp = x2`) guarantee `reg'[r] = reg[r]` on return when `[sp_entry - MaxStack, sp_entry)` is writable, 16-byte aligned, and disjoint from heap/globals (matching `CakeML`/`Pancake` `riscv_configScript.sml:18–28`). In `Asterinas` `trap.S:122–138`, `run_user` saves `s0`–`s11`, `ra`, and `gp` (`14 * 8 = 112 B`, preserving `112 % 16 == 0` stack alignment) because U-mode mutates `gp` (`x3`), requiring `_end_trap_from_user` (`trap.S:114`) to restore kernel `gp` before returning to Rust.
2. **Clobbered caller-saved GPRs (`ra`, `t0`–`t6`, `a0`–`a7`):** Assembly callers cannot rely on `{x1, x5..x7, x10..x17, x28..x31}` surviving a Rust call (`seL4` `head.S:62` reloads `ra` after `jal init_kernel`).
3. **Supervisor CSR frame preservation (`senvcfg`, `sstatus`, `stvec`, `scounteren`, `sscratch`, `satp`):** Pure Rust MIR and LLVM's RISC-V backend emit zero `Zicsr` or privileged `SYSTEM` instructions outside `asm!` / foreign calls. Under `supervisor.adoc`, unprivileged S-mode instructions leave `senvcfg`, `sstatus` (with `FS = VS = Off`), `stvec`, `scounteren`, `sscratch`, and `satp` strictly unchanged **if and only if** (a) no synchronous exception occurs (guaranteed by verified MIR safety + pre-dirtied `PTE.A = D = 1` kernel mappings under `Svade`), and (b) **`sstatus.SIE == 0`** throughout S-mode Rust execution so asynchronous interrupts cannot overwrite `sepc`, `scause`, `stval`, `SPIE`, and `SPP`. Any intentional inline-asm CSR write (`setVSpaceRoot`, `machine.h:259–273`) must carry an explicit stateful CSR contract.

---

### 5. Compositional Multi-Language Refinement and Non-Vacuity Across Boot and Trap Seams

Basis: source + derived

Following `CompCert` (`common/Smallstep.v:52–245`, `CompCertELF` DOI `10.1145/3360572`, `CompCertO` DOI `10.1145/3453483.3454097`), `CertiKOS` (POPL 2015 DOI `10.1145/2676726.2676975`; OSDI 2016 DOI `10.5555/3026877.3026928`), `seL4` translation validation (PLDI 2013 DOI `10.1145/2491956.2462183`), `Pancake` (PLOS 2023 DOI `10.1145/3623759.3624544`), and `DimSum` (POPL 2023 DOI `10.1145/3571207`), composing boot assembly ($\mathcal{T}_{\text{boot}}: P_{\text{SBI}} \to I_{\text{call}}$), Rust ($\mathcal{T}_{\text{rust}}: I_{\text{call}}' \to J_{\text{ret}}$), and `sret` exit ($\mathcal{T}_{\text{exit}}: J_{\text{ret}}' \to Q_{\text{umode}}$) suffers from **seam vacuity** whenever $I_{\text{call}} \not\Rightarrow I_{\text{call}}'$, $J_{\text{ret}} \not\Rightarrow J_{\text{ret}}'$, or top-level hypotheses are unsatisfiable. Five concrete vacuity traps recur in RISC-V Rust kernels:

1. **Stack-alignment mismatch (`8 B` vs. `16 B`):** Assembly pushes an odd word count (`sp % 16 == 8`) while $\mathcal{T}_{\text{rust}}$ assumes `sp % 16 == 0` (`riscv-cc.adoc:320`).
2. **Unzeroed `.bss` / relocation mismatch:** `_start` enters Rust before zeroing `.bss` (`external-blocks.md:75`) or applying `R_RISCV_RELATIVE` relocations (`fw_base.S:178`).
3. **`KernelRet` width drift:** Rust widens `KernelRet` to `24 B` (`arg.make_indirect()`), expecting a buffer pointer in `a0` while `_start` passes `a0 = hartid`.
4. **Omitted `senvcfg` sanitization:** $\mathcal{T}_{\text{rust}}$ frames `senvcfg_2 = senvcfg_1` and $\mathcal{T}_{\text{exit}}$ requires `senvcfg_2 == 0` for U-mode `CBO` safety, while `_start` omitted `csrw senvcfg, zero`.
5. **Unchecked stack-depth overlap:** $\mathcal{T}_{\text{rust}}$ assumes stack/global disjointness without checking compiled stack-frame depth against `BIT(CONFIG_KERNEL_STACK_BITS)`.

Eliminating seam vacuity requires: (a) **exact definitional equality** of intermediate boundary predicates ($I_{\text{call}} \equiv I_{\text{call}}'$, $J_{\text{ret}} \equiv J_{\text{ret}}'$) composed via direct modus ponens with zero extra top-level assumptions; and (b) **an existential witness theorem** (`∃ σ_0 σ_3, P_SBI(σ_0) ∧ Step_ISA^+(σ_0, σ_3) ∧ Q_umode(σ_3)`) universally quantified over firmware reset CSR values (`raw_senvcfg`, `raw_scounteren`, `raw_gpr`) reaching `cur_privilege = User` with `senvcfg = 0`, `SIE = 1`, `SPP = 0`, and `load_reservation = none`.

## Boundaries

- **not examined — Cross-language stack unwinding (`extern "C-unwind"`), `.eh_frame`, and `riscv_vector_cc`:** Bare-metal kernels use `-C panic=abort` and integer `LP64` ABIs; unwinding across trap frames and vector-register calling conventions (`riscv-cc.adoc:129–155`) were `not examined`.
- **unknown — Cross-release register stability of `extern "Rust"`:** Because `extern "Rust"` provides zero ABI stability guarantees (`external-blocks.md:101`), register assignment preservation across `rustc` upgrades is `unknown` and unsuitable for assembly boundaries.
- **known not to apply — Echoing the indirect-return pointer in `a0` on RV64 structs $> 16\text{ B}$:** x86-64 System V's `%rax` `sret`-echo rule is `known not to apply` on RISC-V (`riscv-cc.adoc:315–317`), as verified by `handover_ret3` leaving `entry_pc` in `a0` on `ret`.
- **unsupported — Pure-Rust CSR mutation or `sret` execution without assembly:** Executing `csrw`, `sfence.vma`, or `sret` in pure Rust without `asm!`, `global_asm!`, or external `.S` stubs is `unsupported` by Rust and `rustc`.

## Evidence

### Primary Specifications, Upstream Repositories, and Literature

1. **`riscv-non-isa/riscv-elf-psabi-doc` (`56561cb3e7330fe99a98fd27457229707b2786ae`):** `riscv-cc.adoc:11–40, 77–95, 178–250, 310–341`.
2. **`riscv-non-isa/riscv-sbi-doc` (`8a545effe9b50484ff897d9815d7d9015cdef203`) & `riscv-software-src/opensbi` (`61f1973bd50338b36c52dc34006f76d464ca4f34`):** `src/ext-hsm.adoc:79–107, 232–247`; `lib/sbi/sbi_hart.c:27–186`; `firmware/fw_base.S:170–215`.
3. **`riscv/riscv-isa-manual` (`3142f66fd71c7ea0326b3687072318aedab587f8`):** `src/priv/supervisor.adoc:783–1390`.
4. **`rust-lang/rust` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) & `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** `compiler/rustc_target/src/callconv/riscv.rs:216–281, 403–450`; `src/items/external-blocks.md:69–117`.
5. **`seL4/seL4` (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`) & `asterinas/asterinas` (`12374d1337d21f2d0dbe39c5cab340b41c58e553`):** `seL4` `src/arch/riscv/head.S:23–63`, `src/arch/riscv/kernel/boot.c:126–143, 451–499`, `src/arch/riscv/c_traps.c:21–94`; `Asterinas` `ostd/src/arch/riscv/boot/bsp_boot.S:30–215`, `boot/mod.rs:146–174`, `trap/trap.S:31–185`.
6. **`AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`), `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`), and Papers:** `CompCert` `riscV/Conventions1.v:35–192`, `common/Smallstep.v:52–245`; `CakeML` `compiler/backend/riscv/riscv_configScript.sml:10–43`, `pancake/README.md:1–102`; H. Cheung et al., PLOS 2023 (`10.1145/3623759.3624544`); R. Gu et al., POPL 2015 (`10.1145/2676726.2676975`) & OSDI 2016 (`10.5555/3026877.3026928`); T. Sewell et al., PLDI 2013 (`10.1145/2491956.2462183`); G. Klein et al., ACM TOCS 2014 (`10.1145/2560537`); Y. Song et al., OOPSLA 2019 (`10.1145/3360572`); J. Koenig & Z. Shao, PLDI 2021 (`10.1145/3453483.3454097`); M. Sammler et al., POPL 2023 (`10.1145/3571207`).

### Compiler Execution Probe: `KernelRet2` vs. `KernelRet3` and `LP64D` vs. `LP64` (Observed `2026-11-20`)

Compiled with `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)` (LLVM `22.1.6`) on `x86_64-unknown-linux-gnu`:

```rust
// /tmp/abi_probe.rs
#![feature(no_core, lang_items)]
#![no_core]

#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
impl Copy for usize {}

#[repr(C)]
pub struct KernelRet2 { pub entry_pc: usize, pub satp_val: usize }

#[repr(C)]
pub struct KernelRet3 { pub entry_pc: usize, pub satp_val: usize, pub sstatus_val: usize }

unsafe extern "C" { fn touch_callee_saved(x: usize) -> usize; }

#[unsafe(no_mangle)]
pub unsafe extern "C" fn handover_ret2(hart_id: usize, dtb_pa: usize) -> KernelRet2 {
    let v = unsafe { touch_callee_saved(hart_id) };
    KernelRet2 { entry_pc: v, satp_val: dtb_pa }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn handover_ret3(hart_id: usize, dtb_pa: usize) -> KernelRet3 {
    let v = unsafe { touch_callee_saved(hart_id) };
    KernelRet3 { entry_pc: v, satp_val: dtb_pa, sstatus_val: 0x20 }
}
```

Commands and recorded assembly output:

```bash
rustc --edition=2024 --crate-type=lib -C opt-level=2 --target=riscv64gc-unknown-none-elf --emit=asm /tmp/abi_probe.rs -o /tmp/abi_lp64d.s
rustc --edition=2024 --crate-type=lib -C opt-level=2 --target=riscv64imac-unknown-none-elf --emit=asm /tmp/abi_probe.rs -o /tmp/abi_lp64.s
```

```asm
	.attribute	4, 16
	.attribute	5, "rv64i2p1_m2p0_a2p1_c2p0_zmmul1p0_zaamo1p0_zalrsc1p0_zca1p0"
handover_ret2:
	addi	sp, sp, -16
	sd	ra, 8(sp)
	sd	s0, 0(sp)
	mv	s0, a1
	call	touch_callee_saved
	mv	a1, s0
	ld	ra, 8(sp)
	ld	s0, 0(sp)
	addi	sp, sp, 16
	ret
handover_ret3:
	addi	sp, sp, -32
	sd	ra, 24(sp)
	sd	s0, 16(sp)
	sd	s1, 8(sp)
	mv	s0, a2
	mv	s1, a0
	mv	a0, a1
	call	touch_callee_saved
	li	a1, 32
	sd	a0, 0(s1)
	sd	s0, 8(s1)
	sd	a1, 16(s1)
	ld	ra, 24(sp)
	ld	s0, 16(sp)
	ld	s1, 8(sp)
	addi	sp, sp, 32
	ret
```

The `diff -u /tmp/abi_lp64d.s /tmp/abi_lp64.s` output differs in `.attribute 5`: `riscv64gc-unknown-none-elf` emits `f2p2_d2p2` and `zcd1p0`, whereas `riscv64imac-unknown-none-elf` omits all `F`/`D` extensions.

## Revalidation

1. **Rerun the `no_core` `rustc --emit=asm` ABI probe (`< 0.2 s`):** Compile `/tmp/abi_probe.rs` on the target `rustc` for `riscv64imac-unknown-none-elf` and `riscv64gc-unknown-none-elf`; verify `.attribute 4, 16`, absence of `f`/`d` attributes on the kernel target, `(a0, a1)` direct return on `16 B` structs, and indirect `a0`-pointer consumption on `24 B` structs.
2. **Diff `rustc_target` and OpenSBI reset initialization:** Diff `compiler/rustc_target/src/callconv/riscv.rs` (`classify_ret`, `extend_integer_width`, `compute_abi_info`) and `lib/sbi/sbi_hart.c` (`mstatus_init`) to check for `CSR_SENVCFG` initialization or new `menvcfg` delegations.
3. **Verify boundary predicate equality and witness realizability:** Confirm `_start` postconditions match `init_kernel` preconditions identically (`sp % 16 == 0`, `.bss` zeroed, `gp` set, `SIE = FS = 0`, `stvec` valid, `senvcfg = 0`) and check an existential witness theorem constructing a valid post-`sret` U-mode state from arbitrary SBI entry states.
