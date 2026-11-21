# RISC-V Linker Relaxation gp Hijacks, AUIPC Page-Alignment Slack, and stvec WARL Alignment Hazards

## Summary

Source-level, IR-level, and pre-link `.o` verification of RISC-V supervisor kernels is unsound unless post-link ELF validation discharges three binary-level hazards introduced between assembly emission, linker relaxation, and privileged trap-vector configuration:

1. **Pre-prologue `gp` (`x3`) hijacking under `R_RISCV_RELAX`:** RISC-V trap entry into S-mode updates CSRs (`scause`, `sstatus`, `stval`, `sepc`) and `pc`, leaving all integer registers `x1`–`x31`—including `gp` (`x3`)—holding untrusted U-mode values. Under the RISC-V ELF psABI, `R_RISCV_RELAX` (code `51`) permits linkers to rewrite two-instruction `lui`/`auipc` + `addi`/`ld`/`sd` accesses within `[__global_pointer$ - 0x800, __global_pointer$ + 0x7ff]` into single-instruction `gp`-relative accesses, and omitting `Tag_RISCV_x3_reg_usage` defaults to `0`, which still allows `gp` relaxation. Without `.option norelax` (or `-Wl,--no-relax` / `-Wl,--no-relax-gp`), linkers fold an unguarded `__global_pointer$` reload into `mv gp, gp` (`0x00018193`) and rewrite any pre-`gp`-restore global access into an attacker-controlled `imm12(gp)` dereference. Moreover, LLVM `ld.lld` disables `gp` relaxation by default (`--relax-gp` required) and relaxes only `R_RISCV_HI20`/`LO12` pairs—never `R_RISCV_PCREL_HI20` `auipc` pairs—whereas GNU `ld` (`--relax` default) relaxes both, creating a cross-linker verification blind spot.
2. **Differential page-alignment slack and RV64 `medany` 32-bit `AUIPC` sign-extension bounds:** In RISC-V PC-relative addressing, `R_RISCV_PCREL_LO12_I`/`S` targets the `AUIPC` label (`P_hi`) rather than its own PC, and linkers compute `hi20 = ((S + A - P_hi) + 0x800) >> 12` to compensate for signed 12-bit `imm12` sign extension. When linker scripts place `. = ALIGN(0x1000)` between `.text` and `.rodata`/`.data`, intra-section `R_RISCV_RELAX` byte deletion shifts `P_hi` downward while page padding absorbs the shrinkage and holds data symbols fixed, incrementing `hi20` by `+1` whenever `(S + A - P_hi) & 0xfff` crosses `0x800`. On RV64I, `AUIPC` sign-extends bit 31 of `imm20 << 12` across bits `[63:32]`, making the representable `medany` displacement asymmetric: `[-0x8000_0800, +0x7fff_f7ff]`. Displacements in `[+0x7fff_f800, +0x7fff_ffff]` (strictly below `+2 GiB`) overflow `delta + 0x800` into `hi20 = 0x80000`, wrapping by `-4 GiB` (`-0x1_0000_0000`) on RV64 if unchecked.
3. **`stvec` WARL low-bit `MODE` aliasing and `BASE` alignment truncation:** `stvec` packs `MODE` in bits `[1:0]` (`00` Direct, `01` Vectored, `>=2` Reserved) and `BASE[XLEN-1:2]` in upper bits, both defined as WARL. If compressed instructions (`C` / `Zca`) leave a trap handler 2-byte aligned (`addr % 4 == 2`) without `.balign 4`, `csrw stvec, reg` presents `MODE = 10` (Reserved). Under WARL ignore legalization (`legalize_tvec`), `stvec.MODE` preserves its prior value while `BASE` drops bit 1: if prior `MODE` was `00`, traps jump 2 bytes *before* the handler; if prior `MODE` was `01`, synchronous exceptions (`ecall`, page faults) still jump to `BASE << 2` and pass functional tests while asynchronous interrupts (`scause[63] = 1`) jump to `(BASE << 2) + 4 * cause` mid-prologue. Without `Sstvecd` or a `csrr` readback check, hardware with coarser WARL `BASE` alignment (such as 64 or 256 bytes) silently zeroes low `BASE` bits even on 4-byte-aligned handlers.

## Applicability

These findings apply to static linking, binary-level formal verification, translation validation, and boot/trap-entry assembly authoring for 32-bit (`RV32I`/`RV32GC`) and 64-bit (`RV64I`/`RV64GC`) RISC-V supervisor and machine-mode kernels, hypervisors, security monitors, and bare-metal runtimes using ELF object files.

The seven subjects in `REPORT.json` jointly define the normative contract, formal reference model, toolchain implementation, execution behavior, and production kernel mitigations:

- **Normative ABI and ISA specifications:** `riscv-non-isa/riscv-elf-psabi-doc` at `56561cb3e7330fe99a98fd27457229707b2786ae` defines ELF code models (`medlow`, `medany`), relocations (`R_RISCV_PCREL_HI20`, `R_RISCV_PCREL_LO12_I`/`S`, `R_RISCV_HI20`, `R_RISCV_LO12_I`/`S`, `R_RISCV_ALIGN`, `R_RISCV_RELAX`), `__global_pointer$`, and `Tag_RISCV_x3_reg_usage`. `riscv/riscv-isa-manual` at `3142f66fd71c7ea0326b3687072318aedab587f8` defines RV64I `AUIPC`/`LUI` sign extension, S-mode trap entry, `stvec` WARL behavior, and `Sstvecd`.
- **Executable formal ISA specification:** `riscv/sail-riscv` at `71312d537fc10782c42b7303a611b923af0566d4` provides operational semantics for `UTYPE` (`AUIPC`/`LUI`), `trap_handler_inner`, and `legalize_tvec`.
- **Toolchain source and execution:** `llvm/llvm-project` at `ece0017061ac8da713b4a91ac00c26e8928022db` (`lld/ELF/Arch/RISCV.cpp`) establishes upstream LLVM `ld.lld` relocation and relaxation algorithms, while LLVM / `ld.lld` `22.1.6` (`08c84e69a84d95936296dfcab0e38b34100725d5`) provides concrete RV64 ELF compilation and linking execution traces (`relocate`, `relaxCall`, and `relaxHi20Lo12` are identical on the inspected paths across both commits).
- **Production OS kernels:** `torvalds/linux` at `aa31d5f8b151b786b748c6bfc9a8c4f1855c8adc` and `seL4/seL4` at `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7` demonstrate contrasting defensive idioms in `entry.S`/`traps.S`, `head.S`, `Makefile`, and linker scripts (`vmlinux.lds.S` vs `common_riscv.lds`).

Asymmetric `AUIPC` sign-extension overflow (`[-0x8000_0800, +0x7fff_f7ff]`) applies specifically to `RV64` (`XLEN = 64`); on `RV32`, 32-bit modular wraparound covers the full 4 GiB space. RVC 2-byte `stvec` misalignment hazards apply whenever 16-bit compressed instructions (`C` or `Zca`) are enabled in any linked translation unit (`EF_RISCV_RVC`).

## Findings

### 1. Pre-Prologue `x3` (`gp`) Hijacking and Cross-Linker Divergence Under `R_RISCV_RELAX`

Basis: normative + source + execution + derived

#### 1.1 Architectural Register State at S-Mode Trap Entry

When a RISC-V hart takes an exception or interrupt into S-mode from U-mode, hardware updates only privileged CSRs and `pc`. In `riscv/sail-riscv` (`71312d537fc10782c42b7303a611b923af0566d4`, `model/sys/sys_control.sail:325-357`), `trap_handler_inner` for `Supervisor` updates `scause`, `mstatus[SPIE, SIE, SPP]`, `hstatus[SPV, SPVP, GVA]`, `stval`, `htval`, `htinst`, `sepc`, and `cur_privilege`, returning `prepare_trap_vector(Supervisor, scause)` as the next `pc`. No general-purpose register `X(1)`..`X(31)` is banked or sanitized by hardware.

At the first instruction of the S-mode trap handler (`pc = stvec_target`) when `sstatus.SPP == 0`, `sp` (`x2`), `gp` (`x3`), and `tp` (`x4`) retain arbitrary 64-bit values chosen by U-mode. Any load, store, or pointer calculation in the trap prologue that reads `x3` (`gp`) before `x3` is explicitly overwritten with the kernel's `__global_pointer$` (or shadow-call-stack pointer) dereferences an attacker-controlled address with supervisor privilege (`cur_privilege = Supervisor`).

#### 1.2 psABI Global-Pointer Relaxation Rules and the `Tag_RISCV_x3_reg_usage = 0` Default Trap

The RISC-V ELF psABI (`riscv-non-isa/riscv-elf-psabi-doc` at `56561cb3e7330fe99a98fd27457229707b2786ae`, `riscv-elf.adoc:1326, 1331-1332, 2492-2582`) reserves `gp` (`x3`) for `__global_pointer$` (conventionally `.sdata + 0x800`, spanning `[.sdata, .sdata + 0xfff]`). Unless `-mno-relax` or `.option norelax` is active, assemblers emit a companion `R_RISCV_RELAX` relocation (type `51`, `riscv-elf.adoc:1231, 2346-2347`) at the exact `r_offset` of candidate symbol relocations.

Under *Global-Pointer Relaxation* (`riscv-elf.adoc:2493-2516`), a linker may delete the upper instruction (`lui` or `auipc`) and rewrite the paired lower instruction (`addi`, load, or store) to use base register `gp` (`x3`) whenever all three conditions hold:

1. Both the high relocation (`R_RISCV_HI20` `26` or `R_RISCV_PCREL_HI20` `23`) and every paired low relocation in the group (`R_RISCV_LO12_I` `27`, `R_RISCV_LO12_S` `28`, `R_RISCV_PCREL_LO12_I` `24`, `R_RISCV_PCREL_LO12_S` `25`) carry `R_RISCV_RELAX` (`riscv-elf.adoc:2371-2380, 2495-2496`).
2. The signed displacement satisfies `-2048 <= (S + A) - GP <= 2047` (`[-0x800, +0x7ff]`, `riscv-elf.adoc:2503`).
3. The merged ELF build attribute `Tag_RISCV_x3_reg_usage` (tag `16`, `riscv-elf.adoc:2030, 2174-2193, 2502-2503`) equals `0` or `1`.

Rule (3) creates a quiet metadata trap: `riscv-elf.adoc:2180-2183` defines `0` as fixed register with unknown purpose, `1` as global pointer for relaxation, `2` as shadow stack pointer, and `3` as temporary register, while `riscv-elf.adoc:2581` states: *"Tag_RISCV_x3_reg_usage is treated as 0 if it is not present."* Moreover, Linux `arch/riscv/Makefile:104-107` (`aa31d5f8b151b786b748c6bfc9a8c4f1855c8adc`) passes `-mno-riscv-attribute` / `-Wa,-mno-arch-attr`, omitting `.riscv.attributes` completely. Because `0` merges compatibly with `1` (`riscv-elf.adoc:2191-2192`) and `gp` relaxation is permitted for `{0, 1}`, hand-written `.S` files and freestanding Rust/C objects without `.riscv.attributes` remain silently eligible for `gp` relaxation.

#### 1.3 Two Distinct `gp` Hijack Mechanisms in Trap Prologues

When `gp` relaxation fires inside a kernel trap prologue, two distinct miscompilations arise:

- **Self-referential `gp` reload elision (`mv gp, gp`):** If the prologue reloads `gp` without `.option norelax` (e.g., `la gp, __global_pointer$` or `lui gp, %hi(__global_pointer$); addi gp, gp, %lo(__global_pointer$)`), `(S + A) - GP == 0` lies inside `[-2048, +2047]`. The linker deletes `lui`/`auipc` and rewrites `addi` to `addi gp, gp, 0` (`mv gp, gp`, `0x00018193`), leaving U-mode `x3` live across C/Rust kernel execution (`riscv-elf.adoc:2559-2564`).
- **Pre-restoration symbol access hijacking (`ld/sd/addi reg, imm12(gp)`):** Even when `load_global_pointer` is guarded by `.option push; .option norelax; ... .option pop` (Linux `arch/riscv/include/asm/asm.h:120-125`; `seL4` `src/arch/riscv/traps.S:81-84`), any *earlier* symbol reference in the prologue remains under default `.option relax`. If an early scratch save, page-fault fastpath, or naked wrapper references a kernel symbol within `[-0x800, +0x7ff]` of `__global_pointer$`, the linker rewrites it to `ld`/`sd`/`addi reg, offset(gp)`. U-mode then sets `x3 = target_kva - offset` and executes `ecall`, forcing S-mode to read or overwrite `target_kva` before reaching `load_global_pointer`.

Upstream `seL4` and Linux prevent pre-restoration hijacking solely through strict instruction ordering:

- In `seL4` (`08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`, `src/arch/riscv/traps.S:26-95`), `trap_entry` swaps `sscratch`, saves `x1`–`x31` via register-indirect stores, reloads `gp` under `.option norelax` (`traps.S:81-84`), and **only at line 94** executes `la sp, (kernel_stack_alloc + BIT(CONFIG_KERNEL_STACK_BITS))`. Moving line 94 above line 81 exposes `sp` whenever `kernel_stack_alloc + stack_size` lands near `.small` (`src/arch/riscv/common_riscv.lds:59-66`).
- In Linux (`aa31d5f8b151b786b748c6bfc9a8c4f1855c8adc`, `arch/riscv/kernel/entry.S:23-96, 128-212`), `handle_exception` swaps `tp` with `CSR_SCRATCH`. On U-mode traps, `CSR_SCRATCH` holds `task_struct` (`tp != 0`), so `bnez tp, .Lsave_context` (`entry.S:135`) branches *over* `new_valid_map_cpus_check` (`entry.S:57`, containing `la a0, new_valid_map_cpus`) and reaches `load_global_pointer` at `entry.S:208` using only `tp`- and `sp`-relative accesses (`--no-relax-gp` is added at `arch/riscv/Makefile:56-58` when `CONFIG_SHADOW_CALL_STACK` repurposes `gp`).

#### 1.4 Cross-Linker Soundness Divergence Between LLVM `ld.lld` and GNU `ld`

Inspection of `llvm/llvm-project` (`ece0017061ac8da713b4a91ac00c26e8928022db`, `lld/ELF/Arch/RISCV.cpp:992-1033, 1084-1089`) and execution of `ld.lld` `22.1.6` (`08c84e69a84d95936296dfcab0e38b34100725d5`) expose a major divergence from GNU `ld`:

| Relaxation Property | RISC-V ELF psABI (`56561cb3...`) | LLVM `ld.lld` (`ece00170...` / `22.1.6`) | GNU `ld` (BFD `elfnn-riscv.c`) |
| :--- | :--- | :--- | :--- |
| Default `--relax` | Permitted with `R_RISCV_RELAX` | Enabled (`ctx.arg.relax = true`) | Enabled |
| Default `gp` relaxation | Permitted for `Tag_RISCV_x3_reg_usage` in `{0, 1}` | **Disabled** unless `--relax-gp` passed | **Enabled** unless `--no-relax` or `--no-relax-gp` |
| `R_RISCV_HI20` + `LO12_I/S` (`lui`) -> `gp` | Specified (`riscv-elf.adoc:2495`) | Implemented (`relaxHi20Lo12`, `RISCV.cpp:992-1033`) | Implemented (`_bfd_riscv_relax_lui`) |
| `R_RISCV_PCREL_HI20` + `PCREL_LO12_I/S` (`auipc`) -> `gp` | Specified (`riscv-elf.adoc:2496, 2504-2515`) | **Not implemented** (`relax()` at `RISCV.cpp:1049-1105` omits `R_RISCV_PCREL_HI20`) | **Implemented** (`_bfd_riscv_relax_pc`) |

In `lld/ELF/Arch/RISCV.cpp:1084-1089`, `relax()` dispatches only `R_RISCV_HI20`, `R_RISCV_LO12_I`, and `R_RISCV_LO12_S` to `relaxHi20Lo12` (`INTERNAL_R_RISCV_GPREL_I`/`S`, `RISCV.cpp:654-666`). Yet `llc -mtriple=riscv64-unknown-none-elf -mattr=+c,+relax` emits `R_RISCV_RELAX` on *both* `R_RISCV_HI20` and `R_RISCV_PCREL_HI20`. Linked at `0x80200000` with `trap_scratch` at `0x80201000` and `__global_pointer$` at `0x80201800`, `ld.lld --relax-gp` emits:

```text
0000000080200000 <trap_entry>:
80200000: 00018193      mv      gp, gp
80200004: 8001b503      ld      a0, -0x800(gp)

0000000080200008 <.Ltmp0>:
80200008: 00001317      auipc   t1, 0x1
8020000c: ff833583      ld      a1, -0x8(t1)
80200010: 10200073      sret
```

`ld.lld --relax-gp` folded the unguarded `__global_pointer$` load into `mv gp, gp` (`0x00018193`) and relaxed the `R_RISCV_HI20` load into `ld a0, -0x800(gp)` (`0x8001b503`, bypassing the `--no-relax` `R_RISCV_HI20` error `524801 is not in [-524288, 524287]`), while leaving `.Ltmp0` (`R_RISCV_PCREL_HI20`) PC-relative. GNU `ld` with default flags relaxes `.Ltmp0` into `ld a1, -0x800(gp)` as well, so `ld.lld`-only CI misses latent `auipc` -> `gp` hijacks.

### 2. Differential Page-Alignment Slack and `0x800` Carry Mutation in `R_RISCV_PCREL_HI20` / `LO12`

Basis: normative + source + execution + derived

#### 2.1 Indirect `AUIPC`-Anchored Relocation Equations

RISC-V splits 32-bit PC-relative addressing across U-type `AUIPC` (`R_RISCV_PCREL_HI20`, code `23`) at $P_{\text{hi}}$ and I/S-type instructions (`R_RISCV_PCREL_LO12_I` `24`, `R_RISCV_PCREL_LO12_S` `25`) at $P_{\text{lo}} \ne P_{\text{hi}}$ (`riscv-elf.adoc:1183-1188, 1578-1620`). The `LO12` relocation symbol names a local label at $P_{\text{hi}}$ (`RE_RISCV_PC_INDIRECT`, `lld/ELF/Arch/RISCV.cpp:396-399`), so both share $\Delta = (S + A) - P_{\text{hi}}$. Because `ADDI`/loads/stores sign-extend $\text{imm}_{12} \in [\text{0x800}, \text{0xfff}]$ as $\text{imm}_{12} - \text{0x1000}$, `RISCV.cpp:616-640` adds `0x800` before shifting:

$$\text{hi}_{20}(\Delta) = \left\lfloor \frac{\Delta + \text{0x800}}{2^{12}} \right\rfloor \bmod 2^{20}, \qquad \text{lo}_{12}(\Delta) = \Delta \bmod 2^{12}.$$

#### 2.2 Non-Uniform Displacement Drift Across `ALIGN(0x1000)` Boundaries

Kernel linker scripts place `4 KiB` (`0x1000`) or `2 MiB` alignments between `.text` and `.rodata`/`.data` for W^X page permissions (Linux `arch/riscv/kernel/vmlinux.lds.S:32, 47, 76, 128`; `seL4` `src/arch/riscv/common_riscv.lds:41, 47, 100`). When `RISCV::relaxOnce` (`RISCV.cpp:1136-1158`) deletes $d > 0$ bytes inside `.text` (e.g., `relaxCall` shrinking 8-byte `auipc + jalr` to 4-byte `jal`, `RISCV.cpp:933-961`), $P_{\text{hi}}$ shifts to $P_{\text{hi}} - d$ while `. = ALIGN(0x1000)` expands padding by $+d$ bytes and holds data symbols fixed ($S' = S$). Thus $\Delta' = \Delta + d$ *grows* as bytes are deleted.

Whenever $\Delta \bmod \text{0x1000} < \text{0x800} \le (\Delta + d) \bmod \text{0x1000}$, $\text{hi}_{20}$ increments by $+1$ and $\operatorname{sext}_{12}(\text{lo}_{12})$ flips sign. Linking `medany_bounds.o` under `slack_page.lds` (`.text` at `0x802017fc`, `. = ALIGN(0x1000)` pinning `target_sym` at `0x80202000`) with `ld.lld` `22.1.6` demonstrates the flip:

- **`--no-relax`** ($P_{\text{hi}} = \text{0x80201804}$, $\Delta = \text{0x7fc} = +2044$): `auipc a0, 0x0` (`00000517`) + `addi a0, a0, 0x7fc` (`7fc50513`).
- **`--relax`** (`call` shrinks by 4 bytes, $P'_{\text{hi}} = \text{0x80201800}$, $\Delta' = \text{0x800} = +2048$): `auipc a0, 0x1` (`00001517`) + `addi a0, a0, -0x800` (`80050513`).

For binary translation validation (Sewell et al., PLDI 2013, DOI `10.1145/2491956.2462183`; Song et al., OOPSLA 2020, DOI `10.1145/3428265`), pre-link `.o` lifters cannot treat `AUIPC` `imm20` as invariant under intra-section shifts. Moreover, hand-scheduled multi-fragment sharing of one `auipc t0, %pcrel_hi(sym)` across offsets `sym + 0` and `sym + 8` (`riscv-elf.adoc:1402-1414, 2532-2553`) silently corrupts the second load by 4 KiB if page-slack drift pushes $\Delta \bmod \text{0x1000}$ into $[\text{0x7f8}, \text{0x7ff}]$.

### 3. RV64 32-Bit `AUIPC` Sign-Extension Asymmetry and `medany` Overflow Hazards

Basis: normative + source + execution + derived

In RV64I (`riscv/riscv-isa-manual` `3142f66fd71c7ea0326b3687072318aedab587f8`, `src/unpriv/rv64.adoc:92-103`; `riscv/sail-riscv` `71312d537fc10782c42b7303a611b923af0566d4`, `model/extensions/I/base_insts.sail:27-34`), `AUIPC` sign-extends bit 31 of `imm20 << 12` to 64 bits:

$$\operatorname{AUIPC}_{64}(P_{\text{hi}}, \text{imm}_{20}) = \left(P_{\text{hi}} + \operatorname{sext}_{64}(\text{imm}_{20} \ll 12)\right) \bmod 2^{64}.$$

Summing $[-\text{0x8000\_0000}, +\text{0x7fff\_f000}]$ and $[-\text{0x800}, +\text{0x7ff}]$ yields the exact asymmetric `medany` range (`riscv-elf.adoc:64-73`, `lld/ELF/Arch/RISCV.cpp:616-619`):

$$\Delta \in [-2^{31} - 2^{11},\; 2^{31} - 2^{11} - 1] = [-\text{0x8000\_0800},\; +\text{0x7fff\_f7ff}] = [-2{,}147{,}485{,}696,\; +2{,}147{,}481{,}599].$$

| Signed Displacement $\Delta = S - P_{\text{hi}}$ | `SignExtend64(val + 0x800, 64) >> 12` | `ld.lld` `22.1.6` Result | Encoded RV64 Pair / Diagnostic |
| :--- | :--- | :--- | :--- |
| `+0x7fff_f7ff` ($2^{31} - 2049$) | `+524287` (`0x7ffff`) | **Links (`0`)** | `auipc a0, 0x7ffff` (`7ffff517`) + `addi a0, a0, 0x7ff` (`7ff50513`) |
| `+0x7fff_f800` ($2^{31} - 2048 < +2\text{ GiB}$) | `+524288` (`0x80000`, 20-bit overflow) | **Fails (`1`)** | `R_RISCV_PCREL_HI20 out of range: 524288 is not in [-524288, 524287]` |
| `-0x8000_0800` ($-2^{31} - 2048 < -2\text{ GiB}$) | `-524288` (`-0x80000`, 20-bit min) | **Links (`0`)** | `auipc a0, 0x80000` (`80000517`) + `addi a0, a0, -0x800` (`80050513`) |
| `-0x8000_0801` ($-2^{31} - 2049$) | `-524289` (20-bit underflow) | **Fails (`1`)** | `R_RISCV_PCREL_HI20 out of range: -524289 is not in [-524288, 524287]` |

Consequently: (1) runtime patchers or module loaders (Linux `arch/riscv/Makefile:24-26, 109-110`; `cpufeature.c:1395-1401` `riscv_alternative_fix_offsets`) that check `isInt<32>(delta)` instead of `isInt<32>(delta + 0x800)` accept `[+0x7fff_f800, +0x7fff_ffff]` and encode `imm20 = 0x80000`, wrapping by `-4 GiB` on RV64; and (2) undefined weak symbols (`S = 0`, `riscv-elf.adoc:75-84`) referenced from `-2 GiB` (`0xffffffff_80000000`) have $\Delta = +\text{0x8000\_0000} > +\text{0x7fff\_f7ff}$, overflowing unless accessed via GOT (`R_RISCV_GOT_HI20`).

### 4. `stvec` WARL Low-Bit Mode Encoding, RVC 2-Byte Misalignment, and `BASE` Granularity Traps

Basis: normative + source + execution + derived

#### 4.1 Normative `stvec` Structure and Sail `legalize_tvec` Semantics

In `riscv/riscv-isa-manual` (`src/priv/supervisor.adoc:317-364`), `stvec` (CSR `0x105`) encodes `BASE[SXLEN-1:2]` and `MODE[1:0]` (`0` Direct `pc <- BASE << 2`; `1` Vectored where exceptions jump to `BASE << 2` and interrupts jump to `(BASE << 2) + 4 * cause`; `>=2` Reserved). In `riscv/sail-riscv` (`model/core/sys_regs.sail:673-702`), `legalize_tvec` defines WARL updates of `v` over prior `o : Mtvec`:

```sail
let v : Mtvec = match trapVectorMode(v[Mode]) {
  TV_Direct => if direct_supported then v else [v with Mode = o[Mode]],
  TV_Vector => if vectored_supported then v else [v with Mode = o[Mode]],
  _         => match xtvec_mode_reserved_behavior {
    Xtvec_Fatal  => reserved_behavior(...),
    Xtvec_Ignore => [v with Mode = o[Mode]],
  },
};
let base_alignment : tvec_alignment = match trapVectorMode(v[Mode]) {
  TV_Direct => direct_alignment_exp,
  TV_Vector => vectored_alignment_exp,
  ...
};
if base_alignment > 2
then [v with Base = [v[Base] with (base_alignment - 3) .. 0 = zeros()]]
else v;
```

#### 4.2 Three Trap-Vector Misdirection Failure Modes

1. **RVC 2-byte function alignment (`addr % 4 == 2`, `v[Mode] = 0b10` Reserved):** With `C`/`Zca` enabled, labels without `.balign 4` (`.align 2` in RISC-V gas/LLVM means $2^2 = 4$ bytes) can land at `4k + 2`. In `seL4`, neither `BEGIN_FUNC(trap_entry)` (`include/machine/assembler.h:17-20`) nor `src/arch/riscv/traps.S:23-24` emits an alignment directive; alignment relies entirely on `. = ALIGN(4K);` before `*(.text.traps)` in `src/arch/riscv/common_riscv.lds:47-50`. Writing `4k + 2` via `csrw stvec, a0` presents `v[Mode] = 0b10` (`Reserved`) and `v[Base] = k`. Under `Xtvec_Ignore`, prior `o[Mode] = 00` causes every trap to jump to `4k` (2 bytes *before* `trap_entry`), whereas prior `o[Mode] = 01` preserves `Vectored` mode!
2. **Synchronous-test survival under `MODE = 01` (`Vectored`) mid-handler jumps:** When `stvec.MODE == 01` points to a monolithic handler (`handle_exception` or `trap_entry`), **all synchronous exceptions (`scause[63] == 0`) still enter at `BASE << 2`**, passing syscall and page-fault tests. Asynchronous interrupts (`STI` `cause = 5` -> `+0x14`, `SEI` `cause = 9` -> `+0x24`) jump 20 or 36 bytes into the prologue, skipping `csrrw tp, CSR_SCRATCH, tp` (`entry.S:134`) or `csrrw sp, sscratch, sp` (`traps.S:28`)—or bisecting a 32-bit instruction when 16-bit RVC instructions precede `+0x14`.
3. **Coarser hardware WARL `BASE` alignment (`base_alignment > 2` without `Sstvecd`):** Only the `Sstvecd` extension (`src/priv/sstvecd.adoc:8-10`) guarantees that `Direct` mode accepts *any* 4-byte-aligned `BASE` (`direct_alignment_exp == 2`). On cores without `Sstvecd` where `direct_alignment_exp` is 6 (64 B) or 8 (256 B), `legalize_tvec` silently zeroes `stvec[5:2]` or `stvec[7:2]`, redirecting `.align 2` handlers (such as Linux `handle_exception` and `.Lsecondary_park`, `head.S:186`) before their entry point unless verified via `csrr` readback.

### 5. Summary of Post-Link Binary Verification Obligations

Basis: derived

Machine-code verifiers and translation validators (Sammler et al., PLDI 2022, DOI `10.1145/3519939.3523434`; Nelson et al., SOSP 2019, DOI `10.1145/3341301.3359641`) must check the **final linked ELF image**:

1. **`x3`-independence before `gp` restoration:** From `stvec_base` (and all reachable interrupt vector offsets if `MODE == 1`) to the dominating `gp` write, verify no instruction reads `x3` and the `gp` write materializes `st_value(__global_pointer$)` rather than `0x00018193` (`mv gp, gp`).
2. **Explicit linker flag gate:** Enforce `-Wl,--no-relax-gp` (or `-Wl,--no-relax`) whenever `x3` holds shadow-stack or per-hart state so neither GNU `ld` nor `ld.lld --relax-gp` emits `x3`-relative accesses.
3. **64-bit `AUIPC` + `LO12` target check:** Reconstruct $(P_{\text{hi}} + \operatorname{sext}_{64}(\text{imm}_{20} \ll 12) + \operatorname{sext}_{64}(\text{imm}_{12})) \bmod 2^{64}$ on finalized ELF bytes and confirm exact match with `st_value + addend`.
4. **`stvec` alignment and readback:** Enforce `.balign 64` (minimum `.balign 4` with `Sstvecd`), check `(st_value & 0x3) == expected_mode`, and assert `csrr` readback equals the written `stvec` value at boot.

## Boundaries

- **Dynamic/shared-library lazy PLT binding and `R_RISCV_TLSDESC` relaxation (`not examined`):** `lld/ELF/Arch/RISCV.cpp` implements `R_RISCV_TLSDESC` (`lines 739-845`) and PLT generation (`lines 282-310`), but dynamic loader (`ld.so`) interactions in user-space DSOs were **not examined**; this report covers statically linked or PIE supervisor/machine kernels and freestanding binaries.
- **Prevalence of `direct_alignment_exp > 2` in pre-`Sstvecd` silicon (`unknown`):** While `sail-riscv` parameterizes `direct_alignment_exp` (`sys_regs.sail:677-701`) and `Sstvecd` (`sstvecd.adoc:8-10`) mandates 4-byte Direct alignment, which pre-`Sstvecd` cores mask low `BASE` bits in `Direct` mode remains **unknown** from public ISA manuals alone and requires `csrw`/`csrr` probing.
- **RV32 `AUIPC` `+0x7fff_f800` `-4 GiB` sign-extension failure (`known not to apply`):** Asymmetric `medany` overflow in `[+0x7fff_f800, +0x7fff_ffff]` is **known not to apply** on `RV32I` (`XLEN = 32`), where 32-bit modular addition wraps cleanly (`riscv-elf.adoc:71-73`). Likewise, `R_RISCV_PCREL_HI20` -> `gp` relaxation is **known not to apply** in LLVM `ld.lld` at `ece0017061ac8da713b4a91ac00c26e8928022db` (`RISCV.cpp:1049-1105`), though GNU `ld` performs it on the same `.o` files.
- **Single-pair `medany` PC-relative addressing outside `[-0x8000_0800, +0x7fff_f7ff]` on RV64 (`unsupported`):** Displacements outside `[-0x8000_0800, +0x7fff_f7ff]` are **unsupported** by `R_RISCV_PCREL_HI20`/`LO12` on RV64 (`RISCV.cpp:616-619`) and require GOT indirection (`R_RISCV_GOT_HI20`) or `-mcmodel=large`.

## Evidence

### Normative Specifications and Formal Models (Observed 2026-11-21)

- **RISC-V ELF psABI (`riscv-non-isa/riscv-elf-psabi-doc` at `56561cb3e7330fe99a98fd27457229707b2786ae`, `riscv-elf.adoc`):** `medany` range and undefined weak symbols (`lines 62-84`); relocation codes `23..28, 43, 51` and indirect `PCREL_LO12` formula (`lines 1183-1231, 1570-1620`); `Tag_RISCV_x3_reg_usage` values, merge rules, and missing default `0` (`lines 2030, 2174-2193, 2581`); global-pointer relaxation rules (`lines 2492-2582`).
- **RISC-V Instruction Set Manual (`riscv/riscv-isa-manual` at `3142f66fd71c7ea0326b3687072318aedab587f8`):** `src/unpriv/rv64.adoc:87-103` (`LUI`/`AUIPC` 32-bit sign extension); `src/priv/supervisor.adoc:317-364` (`stvec` WARL `BASE`/`MODE`); `src/priv/sstvecd.adoc:1-10` (4-byte Direct `stvec.BASE`).
- **Sail RISC-V Model (`riscv/sail-riscv` at `71312d537fc10782c42b7303a611b923af0566d4`):** `model/extensions/I/base_insts.sail:27-34` (`UTYPE`); `model/sys/sys_control.sail:325-357` (`trap_handler_inner`); `model/core/sys_regs.sail:666-702` (`legalize_tvec`).

### Upstream Sources and Executed Traces (Observed 2026-11-21)

- **LLVM `lld` (`llvm/llvm-project` at `ece0017061ac8da713b4a91ac00c26e8928022db`, `lld/ELF/Arch/RISCV.cpp`):** `SignExtend64(val + 0x800, bits) >> 12` check (`lines 609-640`); `relaxHi20Lo12` and `relax()` omitting `R_RISCV_PCREL_HI20` (`lines 654-666, 992-1033, 1084-1089`); `relaxCall` and `relaxOnce` (`lines 933-961, 1136-1158`).
- **Linux (`torvalds/linux` at `aa31d5f8b151b786b748c6bfc9a8c4f1855c8adc`):** `arch/riscv/Makefile:14-26, 56-58, 104-110`; `arch/riscv/include/asm/asm.h:114-126`; `arch/riscv/kernel/entry.S:23-96, 128-212`; `arch/riscv/kernel/head.S:186-208`; `arch/riscv/kernel/vmlinux.lds.S:32, 47, 128-135`.
- **seL4 (`seL4/seL4` at `08c7e5fddb3111ff377745c8eefb07feb5c4cfb7`):** `include/machine/assembler.h:17-20`; `src/arch/riscv/traps.S:23-95`; `src/arch/riscv/common_riscv.lds:45-66`; `src/arch/riscv/kernel/boot.c:131`; `include/arch/riscv/arch/machine.h:165-168`.
- **Executed RV64 probes (`llc` / `ld.lld` `22.1.6`, commit `08c84e69a84d95936296dfcab0e38b34100725d5`):** Verified `trap_gp.ll` (`mv gp, gp` `00018193`, `ld a0, -0x800(gp)` `8001b503`, unrelaxed `auipc` `00001317`) and `medany_bounds.ll` (`0x7fc` -> `0x800` slack carry flip and exact `[-0x80000800, +0x7ffff7ff]` link boundaries).

### Peer-Reviewed Literature

- Thomas Sewell, Magnus O. Myreen, and Gerwin Klein, *"Translation Validation for a Verified OS Kernel,"* PLDI 2013, DOI: `10.1145/2491956.2462183`.
- Alasdair Armstrong et al., *"ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS,"* POPL 2019, DOI: `10.1145/3290384`.
- Luke Nelson et al., *"Scaling Symbolic Evaluation for Automated Verification of Systems Code with Serval,"* SOSP 2019, DOI: `10.1145/3341301.3359641`.
- Youngju Song et al., *"CompCertELF: Verified Separate Compilation of C Programs into ELF Object Files,"* PACMPL (OOPSLA) 2020, DOI: `10.1145/3428265`.
- Michael Sammler et al., *"Islaris: Verification of Machine Code Against Authoritative ISA Semantics,"* PLDI 2022, DOI: `10.1145/3519939.3523434`.

## Revalidation

To revalidate these invariants on a newer toolchain, linker commit, or candidate RISC-V kernel ELF image:

1. **Run the standalone Python 3 relocation, page-slack carry, and `stvec` WARL discriminator:**
   ```bash
   python3 - << 'EOF'
   def sext(v: int, b: int) -> int:
       v &= (1 << b) - 1
       return v - (1 << b) if (v & (1 << (b - 1))) else v

   def reloc_pcrel_rv64(pc_hi: int, sym: int) -> tuple[int, int]:
       d = (sym - pc_hi) & ((1 << 64) - 1)
       hi_chk = sext((d + 0x800) & ((1 << 64) - 1), 64) >> 12
       if not (-(1 << 19) <= hi_chk < (1 << 19)):
           raise OverflowError(hi_chk)
       return ((d + 0x800) >> 12) & 0xFFFFF, d & 0xFFF

   def eval_rv64(pc_hi: int, hi20: int, lo12: int) -> int:
       return (pc_hi + sext(hi20 << 12, 32) + sext(lo12, 12)) & ((1 << 64) - 1)

   pc = 0xFFFFFFFF80200000
   for ok in (-0x80000800, -0x800, 0x7FF, 0x800, 0x7FFFF7FF):
       tgt = (pc + ok) & ((1 << 64) - 1)
       assert eval_rv64(pc, *reloc_pcrel_rv64(pc, tgt)) == tgt
   for bad in (-0x80000801, 0x7FFFF800):
       try:
           reloc_pcrel_rv64(pc, (pc + bad) & ((1 << 64) - 1))
           raise AssertionError(bad)
       except OverflowError:
           pass
   assert reloc_pcrel_rv64(0x80201804, 0x80202000) == (0x0, 0x7FC)
   assert reloc_pcrel_rv64(0x80201800, 0x80202000) == (0x1, 0x800)
   print("OK")
   EOF
   ```
2. **Check `ld.lld` `R_RISCV_PCREL_HI20` -> `gp` support:** Search `relax()` in `lld/ELF/Arch/RISCV.cpp` for `R_RISCV_PCREL_HI20` or link an `auipc + ld` access to `.sdata` with `ld.lld --relax-gp` and inspect `llvm-objdump -d`.
3. **Audit a linked kernel ELF:** Confirm `(st_value(trap_entry) & 0x3) == 0` via `llvm-readobj -s` and disassemble `trap_entry` up to `load_global_pointer` via `llvm-objdump -d` to verify zero `(gp)` operands and absence of `00018193` (`mv gp, gp`).
