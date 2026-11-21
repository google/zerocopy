# RISC-V Smstateen Extension Gating, Early-Boot Trap-Vector Ordering, and Partial CSR Modeling Limits

## Summary

The RISC-V `Smstateen` and `Ssstateen` state-enable extensions (`mstateen0..3`, `hstateen0..3`, `sstateen0..3`) change supervisor-mode CSR accessibility from unconditional presence to opt-in machine-mode delegation. Under Privileged Architecture v1.12 without `Smstateen`, `senvcfg` (`0x10A`) is unconditionally accessible in S-mode. Adding `Smstateen` breaks that monotonicity on cold reset: hardware initializes all writable `mstateen0` bits—including `mstateen0.ENVCFG` (bit 62) and `mstateen0.SE0` (bit 63)—to zero (`[#norm:mstateen_zero_initialization]`). Until M-mode firmware sets `mstateen0.ENVCFG = 1` (and, when `V = 1`, HS-mode software sets `hstateen0.ENVCFG = 1`), any S-mode or VS-mode `Zicsr` read or write targeting `senvcfg`—including `csrw senvcfg, zero` or `csrr t0, senvcfg`—raises **Illegal Instruction (`scause = 2`)** whenever `mstateen0.ENVCFG = 0` (even in VS-mode), or **Virtual Instruction (`scause = 22`)** when `V = 1`, `mstateen0.ENVCFG = 1`, and `hstateen0.ENVCFG = 0`.

This gating creates a severe early-boot ordering hazard whenever S-mode startup assembly (`boot.S`) touches `senvcfg` (or another gated CSR such as `sstateen0`, `scontext`, `siselect`, or `srmcfg`) before loading a valid handler into `stvec` (`0x105`). Immediately before executing `mret` into S-mode, OpenSBI's `sbi_hart_switch_mode` sets `stvec` to `next_addr & ~0x3` (the S-mode payload's own `_start` entry address), while `sbi_illegal_insn_handler` redirects unhandled S-mode illegal instructions to `stvec & ~0x3` via `sbi_trap_redirect`. Consequently, if `mstateen0.ENVCFG = 0` and `_start` executes `csrw senvcfg, zero` before `csrw stvec, <handler>`, control vectors back to `_start` with `sstatus.SIE = 0`, trapping the hart in a silent infinite re-entry loop. When an intermediate S-mode bootloader (such as U-Boot or an EFI stub) precedes the kernel, `stvec` instead points into reclaimed loader text, hijacking early boot on the first gated CSR trap.

Sound S-mode boot assembly therefore enforces the ordering **`sie/sstatus.SIE` mask -> `stvec` (4-byte-aligned physical handler or skip-on-trap recovery label) -> gated CSR setup (`senvcfg`, `sstateen0`) -> `sfence.vma` -> `satp` -> `sfence.vma` -> virtual `stvec`**. Across emulators and formal ISA specifications, three modeling limits recur: (1) QEMU's default `-cpu rv64` disables `ext_smstateen`, short-circuiting `smstateen_acc_ok` to `RISCV_EXCP_NONE` and masking missing-enable bugs that fault on `-cpu max`, Spike `--isa=rv64gc_smstateen`, or RVA23 silicon; (2) simplified ISA models that narrow `senvcfg` to a `FIOM`-only mask (`0x1`) drop `Zicbom`/`Zicboz` (`CBIE`, `CBCFE`, `CBZE`), `Ssnpm` (`PMM`), `Zicfilp`/`Zicfiss` (`LPE`, `SSE`), and `Svukte` (`UKTE`) bits, missing non-zeroing WARL preservation (`CBIE = 0b10`, `PMM = 0b01`) and `menvcfg.SSE` cross-CSR read modulation; and (3) upstream `riscv/sail-riscv` at `04bcb62c` omits `AIA`, `IMSIC`, `CTR`, and `JVT` from `legalize_mstateen0`, forcing bits 59, 58, 54, and 2 to read-only zero despite OpenSBI programming them.

## Applicability

These findings apply to RV32 and RV64 implementations of RISC-V Privileged Architecture v1.12 or v1.13 (`Sm1p12`, `Sm1p13`) combined with `Smstateen` / `Ssstateen` v1.0, the `H` hypervisor extension v1.0, and S-mode OS or hypervisor payloads booted from M-mode SBI firmware or chained S-mode loaders.

The six subjects in `REPORT.json` form a single vertical stack examined together:

1. **`riscv/riscv-isa-manual` (`3142f66fd71c7ea0326b3687072318aedab587f8`)**: Normative specification of `mstateen0..3`, `hstateen0..3`, `sstateen0..3` (`src/priv/smstateen.adoc`), and `stvec`, `senvcfg`, `satp`, and `Sv39` (`src/priv/supervisor.adoc`).
2. **`riscv/sail-riscv` (`04bcb62ccab96e35b9d6ce01873851972945af6f`)**: Official Sail formalization of `Zicsr` access checks, `Smstateen` legalization, `senvcfg` WARL semantics, and Lean 4 / C emulator generation.
3. **`riscv-software-src/opensbi` (`61f1973bd50338b36c52dc34006f76d464ca4f34`)**: Reference M-mode firmware establishing concrete S-mode handoff values (`mstateen0`, `hstateen0`, `sstateen0`, `menvcfg`, `medeleg`, `stvec`, `vstvec`, `satp`) and `sbi_trap_redirect`.
4. **`torvalds/linux` (`5f22fb20497f4983094131f00a734362300d22d2`)**: Production S-mode early-boot sequencing (`arch/riscv/kernel/head.S`) and KVM guest `smstateen_csr` / `senvcfg` switching (`arch/riscv/kvm/vcpu.c`).
5. **`qemu/qemu` (`225d5bd4691fc75e32536428fc9a23ddb8e30784`) and `riscv-software-src/riscv-isa-sim` (`982f078e65ab52d5d9a91248c2178f5399df7783`)**: Reference emulators used for differential validation.

Version-sensitive applicability boundaries:
- **OpenSBI `Smstateen` support**: Current OpenSBI (`lib/sbi/sbi_hart.c:84-115`) probes `CSR_MSTATEEN0` on Priv v1.12+ harts and sets `SMSTATEEN_STATEN | SMSTATEEN0_CONTEXT | SMSTATEEN0_HSENVCFG`. OpenSBI releases prior to v1.2, minimal M-mode boot ROM stubs (such as Sail's 8-instruction `DEFAULT_RSTVEC` in `lean_emulator/LeanRiscv.lean:43-53`), and restricted SBI domains leave `mstateen0 = 0`.
- **QEMU CPU flags**: Generic `-cpu rv64` leaves `ext_smstateen = false` unless `,smstateen=true` is appended, whereas `-cpu max` and RVA23 profiles enable `ext_smstateen = true` (`target/riscv/cpu.c:276`).

## Findings

### 1. Normative Smstateen/Ssstateen Gating Hierarchy and Reset Non-Monotonicity

`Basis: normative + source`

`Smstateen` defines four 64-bit CSRs at machine level (`mstateen0..3` at `0x30C..0x30F`, RV32 high halves `mstateen0h..3h` at `0x31C..0x31F`), four 64-bit CSRs at hypervisor level when `H` is present (`hstateen0..3` at `0x60C..0x60F`, RV32 high halves `0x61C..0x61F`), and four 32-bit-effective SXLEN CSRs at supervisor level (`sstateen0..3` at `0x10C..0x10F`) (`smstateen.adoc:52-74`; `stateen_csrs.sail:9-107`). Each register restricts strictly less-privileged modes without restricting its own level (`[#norm:stateen_op]`, `smstateen.adoc:86-88`).

The bit allocation of `mstateen0`, `hstateen0`, and `sstateen0` (`smstateen.adoc:186-314`; `opensbi`, `include/sbi/riscv_encoding.h:873-893`) is:

| Bit(s) | Field | Present in | Controlled Lower-Privilege State / CSRs |
| --- | --- | --- | --- |
| `63` | `SE0` | `mstateen0`, `hstateen0` | `hstateen0[h]` (from M) and `sstateen0` (from M and HS) (`0x60C`, `0x61C`, `0x10C`) |
| `62` | `ENVCFG` | `mstateen0`, `hstateen0` | `henvcfg[h]` (from M) and `senvcfg` (from M and HS) (`0x60A`, `0x61A`, `0x10A`) |
| `61` | `WPRI` | Reserved | Read-only zero (`[#norm:stateen_reserved_roz]`) |
| `60` | `CSRIND` | `mstateen0`, `hstateen0` | `Sscsrind` indirect CSRs `siselect`, `sireg1..6`, `vsiselect`, `vsireg1..6` (`0x150..0x157`, `0x250..0x257`) |
| `59` | `AIA` | `mstateen0`, `hstateen0` | `Ssaia` interrupt state outside `CSRIND` and `IMSIC` |
| `58` | `IMSIC` | `mstateen0`, `hstateen0` | `Ssaia` IMSIC state including `stopei` / `vstopei` |
| `57` | `CONTEXT` | `mstateen0`, `hstateen0` | `Sdtrig` trigger context CSRs `scontext` (`0x5A8`) and `hcontext` (`0x6A8`) |
| `56` | `P1P13` | `mstateen0` only | `hedelegh` (`0x612`, RV32 Priv v1.13); `WPRI` read-only zero in `hstateen0` |
| `55` | `SRMCFG` | `mstateen0` only | `Ssqosid` `srmcfg` (`0x181`); `WPRI` in `hstateen0` |
| `54` | `CTR` | `mstateen0`, `hstateen0` | `Smctr` / `Ssctr` Control Transfer Records state |
| `53:3` | `WPRI` | Reserved | Read-only zero |
| `2` | `JVT` | `mstateen0`, `hstateen0`, `sstateen0` | `Zcmt` jump vector table CSR `jvt` (`0x017`) |
| `1` | `FCSR` | `mstateen0`, `hstateen0`, `sstateen0` | `fflags`, `frm`, `fcsr` (`0x001..0x003`) and FP ops under `Zfinx` (`misa.F = 0`); ROZ when `misa.F = 1` |
| `0` | `C` | `mstateen0`, `hstateen0`, `sstateen0` | All custom extension state |

Four normative rules govern state transitions across this hierarchy:

1. **Hardware zero reset (`[#norm:mstateen_zero_initialization]`, `smstateen.adoc:152`)**: Hardware initializes all writable `mstateen0..3` bits to `0` on reset (`reset_stateen()` in `stateen_regs.sail:222-230`). Conversely, `hstateen*` and `sstateen*` writable bits are unspecified at reset; M-mode software setting any `mstateen*` bit to `1` must initialize matching writable bits in `hstateen*` and `sstateen*` to `0` (`smstateen.adoc:153-155, 327-332`).
2. **Downward read-only-zero masking (`[#norm:mstateen_lower_priv_roz]`, `[#norm:sstateen_vsmode_access_roz]`, `smstateen.adoc:140-145`)**: Any bit `0` in `mstateen_k` reads as `0` and ignores writes in `hstateen_k` and `sstateen_k`; any bit `0` in `hstateen_k` appears read-only `0` in `sstateen_k` when `V = 1` (`get_sstateen_mask` in `stateen_regs.sail:183`).
3. **Cascade self-gating via bit 63 (`SE0..SE3`, `[#norm:mstateen_bit_63_op]`, `smstateen.adoc:161-165`)**: `mstateen0.SE0` gates S/HS access to `sstateen0` and `hstateen0`, and `hstateen0.SE0` gates VS access to `sstateen0`. Early-boot `csrw sstateen0, zero` therefore faults whenever `SE0 = 0`.
4. **Non-monotonic extension composition (`smstateen.adoc:97`; `stateen_regs.sail:79-87`)**: In `sail-riscv`, `get_mstateen` evaluates `if not(is_mstateen_accessible()) then ones() else read_mstateen0().bits`. Adding `Smstateen` to a Priv v1.12 core without M-mode firmware updates flips the reset mask from all-ones to all-zeros, turning legal S-mode `senvcfg` accesses into traps.

### 2. Exact Exception Classification Matrix: Illegal Instruction (Cause 2) vs. Virtual Instruction (Cause 22)

`Basis: normative + source + execution`

Whether a `Zicsr` access to `senvcfg` (`0x10A`) retires, raises **Illegal Instruction (`cause = 2`)**, or raises **Virtual Instruction (`cause = 22`)** follows the H-extension HS-qualification rule (`riscv/sail-riscv`, `model/sys/sys_control.sail:48-61` and `model/postlude/csr_end.sail:33`):

```sail
function check_CSR(csr : csreg, p : Privilege, access_type : CSRAccessType) -> bool =
    check_CSR_priv(csr, p)
  & check_CSR_access(csr, access_type)
  & is_CSR_accessible(csr, p, access_type)
  & stateen_allows_CSR_access(csr, p, access_type)

function check_CSR_result(csr : csreg, p : Privilege, access_type : CSRAccessType) -> CSRCheckResult = {
  if check_CSR(csr, p, access_type) then
    CSR_Check_OK()
  else if (p == VirtualSupervisor | p == VirtualUser) & is_CSR_exception_virtual(csr, p, access_type) then
    CSR_Virtual()
  else
    CSR_Illegal()
}
```

Here `is_CSR_exception_virtual(csr, _, access_type)` evaluates `check_CSR(csr, Supervisor, access_type)`. Both QEMU (`smstateen_acc_ok` in `target/riscv/tcg/csr.c:52-81`) and Spike (`senvcfg_csr_t::verify_permissions` in `riscv/csrs.cc:1877-1889`) enforce the identical check order (`mstateen[0]` tested before `virt_enabled` / `hstateen[0]`):

| Execution Mode (`p`, `V`) | `Smstateen` | `mstateen0.ENVCFG` | `hstateen0.ENVCFG` | Architectural Result |
| --- | --- | --- | --- | --- |
| `M` (`V = 0`) | `0` or `1` | `0` or `1` | `0` or `1` | Allowed (`mstateen0` never restricts M-mode) |
| `HS` / `S` (`V = 0`) | `0` | N/A | N/A | Allowed |
| `HS` / `S` (`V = 0`) | `1` | `0` | `0` or `1` | **Illegal Instruction (`cause = 2`)** |
| `HS` / `S` (`V = 0`) | `1` | `1` | `0` or `1` | Allowed |
| `VS` (`V = 1`) | `0` | N/A | N/A | Allowed |
| `VS` (`V = 1`) | `1` | `0` | `0` (forced ROZ) | **Illegal Instruction (`cause = 2`)** — HS check also fails |
| `VS` (`V = 1`) | `1` | `1` | `0` | **Virtual Instruction (`cause = 22`)** — HS check succeeds |
| `VS` (`V = 1`) | `1` | `1` | `1` | Allowed |
| `U` (`V = 0`) or `VU` (`V = 1`) | `0` or `1` | `0` or `1` | `0` or `1` | **Illegal Instruction (`cause = 2`)** — `check_CSR_priv` fails |

Per `csr_access_type` and `doCSR` (`model/extensions/Zicsr/zicsr_insts.sail:33-53`), `check_CSR_result` executes unconditionally *before* distinguishing `CSRWrite` (`csrw senvcfg, x0`, `rd == x0`) from `CSRRead` (`csrr t0, senvcfg`, `rs1 == x0`). Neither zeroing `senvcfg` nor probing it via read avoids the trap when `ENVCFG = 0`.

### 3. Firmware Handoff State and the Early-Boot Stale-`stvec` Hazard

`Basis: source + derived + execution`

Inspecting OpenSBI (`riscv-software-src/opensbi` at `61f1973bd50338b36c52dc34006f76d464ca4f34`) reveals how machine-to-supervisor handoff interacts with early S-mode CSR faults:

1. **OpenSBI `mstateen` / `hstateen` setup (`lib/sbi/sbi_hart.c:84-130, 663-667`)**: When `CSR_MSTATEEN0` is detected, `mstatus_init()` sets `SMSTATEEN_STATEN | SMSTATEEN0_CONTEXT | SMSTATEEN0_HSENVCFG` (plus conditional `AIA`, `IMSIC`, `SVSLCT`, `CTR`, `SRMCFG`) in `CSR_MSTATEEN0`, sets `SMSTATEEN_STATEN` in `CSR_MSTATEEN1..3`, and explicitly writes `0` to `CSR_SSTATEEN0..3` and `CSR_HSTATEEN0..3`. Thus `hstateen0.ENVCFG` is always `0` at HS-mode entry; any hypervisor entering a VS-mode guest without setting bit 62 of `hstateen0` exposes guest early boot to `cause = 22` faults.
2. **OpenSBI trap delegation and `sbi_trap_redirect` (`lib/sbi/sbi_trap.c:104-233, 328-367, 424-464`; `lib/sbi/sbi_illegal_insn.c:23-175`)**: `delegate_traps()` leaves `CAUSE_ILLEGAL_INSTRUCTION` (`0x2`) *cleared* in `CSR_MEDELEG` so M-mode can emulate `rdtime`/`rdcycle`/`rdinstret`, while delegating `CAUSE_VIRTUAL_INST_FAULT` (`0x16`) when `misa.H` is present. On an unemulated CSR such as `senvcfg`, `sbi_emulate_csr_read` fails (`sbi_illegal_insn.c:71-72`), calling `truly_illegal_insn` -> `sbi_trap_redirect(regs, &trap)` (`sbi_trap.c:203-209`):
   ```c
   csr_write(CSR_STVAL, trap->tval);
   csr_write(CSR_SEPC, regs->mepc);
   csr_write(CSR_SCAUSE, trap->cause);
   regs->mepc = csr_read(CSR_STVEC) & ~MTVEC_MODE;
   ```
   Whether `medeleg[2]` is `1` (hardware delegation) or `0` (OpenSBI `sbi_trap_redirect`), an unhandled S-mode illegal instruction jumps to **`CSR_STVEC & ~0x3`**.
3. **OpenSBI `stvec` entry value (`lib/sbi/sbi_hart.c:819-832`)**: Right before `mret`, `sbi_hart_switch_mode()` sets `tvec = next_addr & ~MTVEC_MODE` and executes `csr_write(CSR_STVEC, tvec)` (or `CSR_VSTVEC` when `next_virt` is true), initializing `stvec` to the S-mode payload's own `_start` entry address.

Touching `senvcfg` at $\text{PC}_{\text{csr}} > \text{\_start}$ *before* updating `stvec` produces three failure modes:

- **Mode A — Silent Infinite `_start` Re-Entry Loop (Direct OpenSBI Handoff)**: With `stvec == _start & ~0x3` and `mstateen0.ENVCFG = 0` (pre-v1.2 OpenSBI, custom firmware, or Priv v1.11 hardware lacking `senvcfg`), `csrw senvcfg, zero` traps to M-mode and redirects to `_start` with `sstatus.SIE = 0`. Execution restarts `_start`, hits $\text{PC}_{\text{csr}}$ again, overwrites `sepc`, and loops silently forever without console output. (An identical loop occurs in VS-mode when `vstvec == _start & ~0x3`, `hstateen0.ENVCFG = 0`, and `hedeleg[22] = 1`.)
- **Mode B — Reclaimed Bootloader Handler Execution (Chained S-Mode Boot)**: When an intermediate S-mode loader (U-Boot or EFI stub) overwrites `stvec` and jumps to `_start` without resetting `stvec`, the trap vectors into stale loader code with kernel early registers.
- **Mode C — Zero-Vector Access Fault Cascade (Bare-Metal Harness)**: Minimal M-mode harnesses setting `medeleg = 0xFFFF` with reset `stvec = 0x0` vector `cause = 2` to physical `0x0000_0000` (unmapped or PMP-blocked ROM), immediately cascading into Instruction Access Fault (`scause = 1`).

Exhaustive enumeration of all $2^8 = 256$ boolean states of `(V, Smstateen, mstateen0.ENVCFG, hstateen0.ENVCFG, medeleg[2], medeleg[22], hedeleg, firmware_redirects_illegal)` identifies `80` faulting `senvcfg` configurations: `60` of `80` (`75%`) jump to stale `stvec`/`vstvec` when `senvcfg` precedes `stvec`, whereas `80` of `80` (`100%`) route deterministically to controlled kernel or M-mode handlers when `stvec` is written first.

### 4. Exact Ordering Invariants for `stvec -> senvcfg -> satp` Boot Sequences

`Basis: normative + source + derived`

Linux's RV64 entry assembly (`torvalds/linux`, `arch/riscv/kernel/head.S:76-125, 198-209, 212-306`) demonstrates safe ordering: `_start_kernel` masks `CSR_IE` and `CSR_IP`, avoids early `CSR_SENVCFG` writes, loads `.Lsecondary_park` into `CSR_TVEC` prior to `setup_vm` (`head.S:297-299`), points `CSR_TVEC` at a virtual continuation across `csrw CSR_SATP` in `relocate_enable_mmu` (`head.S:84-111`), and installs `handle_exception` before C entry. When probing optional PMP CSRs in M-mode (`head.S:229-237`), Linux loads `.Lpmp_done` into `CSR_TVEC` *before* touching `CSR_PMPADDR0` so illegal-instruction traps skip forward cleanly.

An S-mode `boot.S` that sanitizes `senvcfg` and enables `Sv39` paging must satisfy five ordered invariants:

1. **Interrupt Masking (`sstatus.SIE = 0`, `sie = 0`)**: Clear `sie` and `sstatus.SIE` so `stvec` handles only synchronous traps.
2. **4-Byte-Aligned Physical `stvec` (`stvec.MODE = 0`, `stvec.BASE % 4 = 0`)**: Before any `Smstateen`-gated or optional CSR instruction, install a 4-byte-aligned physical handler in `stvec` (`supervisor.adoc:333-336`; as noted at `sbi_hart.c:811-818`, 2-byte-aligned compressed addresses set bit 1, requesting reserved `MODE = 2`). Either point `stvec` to a dedicated panic/parking loop disjoint from `_start`, or bracket optional CSR writes with a skip label:
   ```assembly
       .balign 4
       la   t0, .Lsenvcfg_done       /* 4-byte aligned recovery target */
       csrw stvec, t0                /* Direct mode (bits [1:0] == 00) */
       csrw senvcfg, zero            /* Skips to .Lsenvcfg_done on Cause 2/22 */
       .balign 4
   .Lsenvcfg_done:
       la   t0, early_boot_trap_park
       csrw stvec, t0
   ```
3. **Gated Environment CSR Setup (`senvcfg`, `sstateen0`) Before `satp` / U-Mode**: Sanitize `senvcfg` (`0x10A`) and `sstateen0` (`0x10C`, gated by `SE0`) in Bare mode (`satp = 0`) before enabling `Svukte` (`senvcfg.UKTE`) or entering U-mode contexts governed by `FIOM`, `PMM`, `CBIE`/`CBCFE`/`CBZE`, or `LPE`/`SSE`.
4. **PTE Store Barrier and `satp` Activation**: Complete physical PTE stores, execute `sfence.vma zero, zero` (`head.S:104`), point `stvec` to a virtual continuation (if `VA != PA`) or identity-mapped handler, and write `csrw satp, t0`.
5. **Post-`satp` `sfence.vma` and Runtime `stvec`**: Execute `sfence.vma zero, zero` (`head.S:122`), install virtual `trap_entry` into `stvec`, and zero `sscratch`.

*Contrast with `seL4` (`seL4/seL4` at `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, `src/arch/riscv/kernel/boot.c:126-132`)*: `init_cpu()` calls `activate_kernel_vspace()` before `write_stvec((word_t)trap_entry)`. That order succeeds in `seL4` *only* because `seL4`'s external `elfloader` already activated `Sv39` paging with `KERNEL_ELF_BASE` mapped prior to `_start` (`src/arch/riscv/head.S:23`). Booting directly from OpenSBI (`satp = 0`) with `VA != PA` without setting `stvec` before `csrw satp` faults into stale `stvec`.

### 5. Emulator and Formal-Model Fidelity Limits Under Partial CSR Bitmasks

`Basis: source + derived + execution`

Comparing QEMU (`target/riscv/tcg/csr.c`), Spike (`riscv/csrs.cc`), and Sail (`riscv/sail-riscv`) against simplified formal ISA models highlights three fidelity limits:

#### A. Default-Disabled `Smstateen` in QEMU `-cpu rv64`

In QEMU (`target/riscv/tcg/csr.c:56-58`), `smstateen_acc_ok` returns `RISCV_EXCP_NONE` immediately when `!riscv_cpu_cfg(env)->ext_smstateen`. Because `-cpu rv64` disables `ext_smstateen` by default (unlike `-cpu max`, `rva23s64`, or `,smstateen=true`, `target/riscv/cpu.c:276, 2911-2977`), testing under default `-cpu rv64` masks missing `mstateen0.ENVCFG` / `hstateen0.ENVCFG` enables. Compliance testing requires `-cpu rv64,smstateen=true` in QEMU and `--isa=rv64gc_smstateen` in Spike.

#### B. Partial `FIOM`-Only `senvcfg` Modeling (`0x1` vs. Full RV64 WARL Mask)

RV64 `senvcfg` (`supervisor.adoc:791-806`; QEMU `tcg/csr.c:3504-3559`; Sail `sys_regs.sail:545-564`) defines eight fields:

| Bits | Field | Extension | WARL / Cross-CSR Read-Write Semantics |
| --- | --- | --- | --- |
| `0` | `FIOM` | Base `S` | Read-only `0` allowed only if `satp.MODE` is hardwired Bare (`supervisor.adoc:831-833`) |
| `2` | `LPE` | `Zicfilp` | U-mode landing-pad enable; `0` if `Zicfilp` absent |
| `3` | `SSE` | `Zicfiss` | U-mode shadow-stack enable; **masked to `0` on read** when `menvcfg.SSE == 0` (or `henvcfg.SSE == 0` if `V = 1`) (`spike/csrs.cc:1892-1895`, `sail/sys_regs.sail:550-556`) |
| `5:4` | `CBIE` | `Zicbom` | `00` off, `01` flush, `11` invalidate; **`10` reserved**—preserves `old.CBIE` or clears/traps (`sail/sys_regs.sail:515-524`) |
| `6` | `CBCFE` | `Zicbom` | Cache-block clean/flush enable |
| `7` | `CBZE` | `Zicboz` | Cache-block zero (`cbo.zero`) enable |
| `33:32` | `PMM` | `Ssnpm` | Pointer masking (`00` off, `10` PMLEN=7, `11` PMLEN=16); **`01` reserved and preserves `old.PMM`** (`qemu/tcg/csr.c:3520-3524`, `sail/sys_regs.sail:560`) |
| `63` | `UKTE` | `Svukte` | User-mode kernel-address fault latency invariance (`qemu/tcg/csr.c:3555-3557`) |

Modeling `senvcfg` as `val & 0x1` (`FIOM`-only) introduces three verification gaps:
1. **Silent bit truncation (`0x80000003_000000FC`)**: Context-switch proofs (e.g., KVM `csr_swap(CSR_SENVCFG, ...)` in `arch/riscv/kvm/vcpu.c:778, 792`) proved over a 1-bit model miss state loss or leakage across `CBIE`, `CBCFE`, `CBZE`, `LPE`, `SSE`, `PMM`, and `UKTE`.
2. **Non-idempotent WARL reservation**: Reserved encodings `CBIE = 0b10` and `PMM = 0b01` retain `old` field bits rather than masking to zero; `write_senvcfg` depends on prior register state, whereas `csrw senvcfg, 0` is deterministically valid across all extensions.
3. **Cross-CSR `SSE` coupling**: Because `read_senvcfg` depends on `menvcfg.SSE` and `henvcfg.SSE`, framing lemmas assuming `senvcfg` reads are invariant under M-mode `menvcfg` writes fail when `Zicfiss` is enabled.

#### C. Partial `mstateen0` Legalization in Upstream `sail-riscv`

In `riscv/sail-riscv` (`04bcb62ccab96e35b9d6ce01873851972945af6f`, `model/extensions/Stateen/stateen_regs.sail:19-69`), `Mstateen0` declares all 12 fields, but `enum stateen_bit` and `legalize_mstateen0` only wire 8 (`SE0`, `ENVCFG`, `CSRIND`, `CONTEXT`, `P1P13`, `SRMCFG`, `FCSR`, `C`), leaving `AIA` (59), `IMSIC` (58), `CTR` (54), and `JVT` (2) hardwired `0` on readback even when OpenSBI (`sbi_hart.c:90-105`) sets them.

### 6. Precondition Design for Mechanized Early-Boot Proofs

`Basis: derived + source`

- **Explicit firmware handoff contract**: Do not hardcode `ext_smstateen = false` or `mstateen0 = ones()` in kernel proofs targeting RVA22/RVA23 hardware. Either verify M-mode `mstateen0` setup or assume an explicit `BootFirmwareContract s0` asserting `s0.cur_privilege = Supervisor`, `hartSupports(Ext_Smstateen) -> s0.mstateen0.ENVCFG = 1` (plus `V = 1 -> s0.hstateen0.ENVCFG = 1`), and `s0.satp = 0` (`supervisor.adoc:1013-1015`).
- **CFG dominance of `stvec`**: Verify over `boot.S` that every `SYSTEM` (`0b1110011`) instruction accessing a CSR outside `{sie, sip, sstatus, stvec, sscratch, scounteren}` is dominated by `csrw stvec, r_vec` with `r_vec[1:0] == 0b00` targeting valid physical boot text disjoint from `_start`.

## Boundaries

- **Known not to apply — Unmapped virtual `stvec` before `satp`**: Loading a non-identity virtual kernel address (`VA != PA`) into `stvec` before enabling `satp` causes any early `senvcfg` trap to fetch from an unmapped physical address and fault; this is **known not to apply** as a pre-MMU guard.
- **Known not to apply — `hstateen0.ENVCFG = 1` overriding `mstateen0.ENVCFG = 0`**: By `[#norm:mstateen_lower_priv_roz]` (`smstateen.adoc:140-142`), `mstateen0.ENVCFG = 0` forces `hstateen0.ENVCFG` to read-only zero and raises Illegal Instruction (`cause = 2`) in VS-mode; hypervisor override is **known not to apply**.
- **Unsupported — `AIA`, `IMSIC`, `CTR`, and `JVT` gating in `sail-riscv` at `04bcb62c`**: Legalization and CSR gating for bits 59, 58, 54, and 2 of `mstateen0`/`hstateen0` are **unsupported** in `riscv/sail-riscv` at `04bcb62ccab96e35b9d6ce01873851972945af6f`.
- **Not examined — SBI `FWFT` runtime negotiation and `Smdbltrp`/`Ssdbltrp` recovery**: Dynamic `SBI_EXT_FWFT` ecalls (`head.S:170-175, 311-316`) and `scause = 16` double-trap recovery handlers were **not examined**.
- **Unknown — Commercial RVA23 silicon read-only-one `mstateen0` choices**: Which commercial RVA23 cores hardwire `mstateen0.ENVCFG` to read-only `1` vs. writable `0`-on-reset (`smstateen.adoc:134-150`) is **unknown** from public ISA manuals alone; portable S-mode code must assume `0` is possible.

## Evidence

### Normative Specifications and Peer-Reviewed Literature

- **`riscv/riscv-isa-manual` (`3142f66fd71c7ea0326b3687072318aedab587f8`)**:
  - `src/priv/smstateen.adoc:44-314` — `Smstateen`/`Ssstateen` CSRs, `#norm:stateen_op`, `#norm:stateen_illegal_state_access`, `#norm:mstateen_lower_priv_roz`, `#norm:mstateen_zero_initialization`, `#norm:mstateen_bit_63_op`, and `mstateen0`/`hstateen0`/`sstateen0` bit tables.
  - `src/priv/supervisor.adoc:317-364, 783-865, 965-1075` — `stvec` alignment/modes, `senvcfg` RV64/RV32 layout, and `satp` Bare-mode rules.
- **Alasdair Armstrong et al.**, *"ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS"*, PACMPL 3(POPL), Article 71, 2019, DOI: `10.1145/3290384`.

### Upstream Source Repositories (Observed `2026-11-20`)

- **`riscv/sail-riscv` (`04bcb62ccab96e35b9d6ce01873851972945af6f`)**: `model/extensions/Stateen/stateen_access_checks.sail:21-94`, `model/extensions/Stateen/stateen_regs.sail:19-230`, `model/sys/sys_control.sail:48-81, 270-360`, `model/postlude/csr_end.sail:33`, `model/extensions/Zicsr/zicsr_insts.sail:33-97`, `model/core/sys_regs.sail:515-588`.
- **`riscv-software-src/opensbi` (`61f1973bd50338b36c52dc34006f76d464ca4f34`)**: `lib/sbi/sbi_hart.c:84-130, 663-667, 810-845`, `lib/sbi/sbi_trap.c:104-233, 328-367, 424-468`, `lib/sbi/sbi_illegal_insn.c:23-175`, `include/sbi/riscv_encoding.h:229-251, 869-893`.
- **`torvalds/linux` (`5f22fb20497f4983094131f00a734362300d22d2`)**: `arch/riscv/kernel/head.S:76-125, 198-209, 229-237, 296-306`, `arch/riscv/kvm/vcpu.c:67-91, 771-797`.
- **`qemu/qemu` (`225d5bd4691fc75e32536428fc9a23ddb8e30784`)**: `target/riscv/tcg/csr.c:52-81, 3490-3559`, `target/riscv/cpu.c:276, 2911-2977`.
- **`riscv-software-src/riscv-isa-sim` (`982f078e65ab52d5d9a91248c2178f5399df7783`)**: `riscv/csrs.cc:1844-1915`.

### Execution Verification

Python 3.13 exhaustive enumeration (`observed_at`: `2026-11-20`) over all $2^8 = 256$ delegation/state-enable configurations confirmed `80` faulting states, `60/80` pre-`stvec` re-entry loop hazards, `80/80` controlled post-`stvec` deliveries, and `dropped_mask=0x00000002000000b0` on `0x00000002000000b1` under a `FIOM`-only (`0x1`) mask.

## Revalidation

1. **Run the self-contained transition-and-WARL probe** (Python 3.10+ stdlib; `<50 ms`):

   ```bash
   python3 - <<'PY'
   from itertools import product

   def check_senvcfg(virt, ext_sm, m_env, h_env):
       if not ext_sm:
           return None
       if not m_env:
           return 2   # Illegal Instruction (even when virt=True)
       if virt and not h_env:
           return 22  # Virtual Instruction
       return None

   def trap_pc(cause, virt, mdel, hdel, fw_redir, stvec, vstvec, mtvec):
       if (mdel >> cause) & 1 or fw_redir:
           return (vstvec if (virt and ((hdel >> cause) & 1)) else stvec) & ~3
       return mtvec & ~3

   START, KTRAP, MTRAP = 0x80200000, 0x80200400, 0x80000400
   faults = loops_bad = ok_good = 0
   for virt, sm, me, he, md2, md22, hd, redir in product([False, True], repeat=8):
       c = check_senvcfg(virt, sm, me, he)
       if c is None:
           continue
       faults += 1
       md = (int(md2) << 2) | (int(md22) << 22)
       hd_mask = (int(hd) << 2) | (int(hd) << 22)
       if trap_pc(c, virt, md, hd_mask, redir, START, START, MTRAP) == START:
           loops_bad += 1
       if trap_pc(c, virt, md, hd_mask, redir, KTRAP, KTRAP, MTRAP) in (KTRAP, MTRAP):
           ok_good += 1

   assert (faults, loops_bad, ok_good) == (80, 60, 80), (faults, loops_bad, ok_good)
   probe = (0x2 << 32) | (1 << 7) | (0x3 << 4) | 1
   arch_mask = (0x3 << 32) | (1 << 7) | (1 << 6) | (0x3 << 4) | (1 << 3) | (1 << 2) | 1
   assert (probe & 0x1) == 0x1 and (probe & arch_mask) == 0x2000000B1
   print("OK: 80 faulting states, 60/80 pre-stvec loop hazards, 80/80 post-stvec safe")
   PY
   ```

2. **Check upstream drift on newer revisions**:
   - `riscv-software-src/opensbi`: check `mstatus_init()` and `sbi_hart_switch_mode()` in `lib/sbi/sbi_hart.c` for `SMSTATEEN0_HSENVCFG`, zeroed `CSR_HSTATEEN0`, and `CSR_STVEC = next_addr & ~MTVEC_MODE`.
   - `riscv/sail-riscv`: check `legalize_mstateen0` in `model/extensions/Stateen/stateen_regs.sail` and `legalize_senvcfg` in `model/core/sys_regs.sail` for `AIA`, `IMSIC`, `CTR`, and `JVT` coverage.
   - `qemu/qemu`: check `smstateen_acc_ok` and `write_senvcfg` in `target/riscv/tcg/csr.c` and default `ext_smstateen` on `-cpu rv64` in `target/riscv/cpu.c`.
