# Errata-Aware Linkers, Post-Link Binary Validators, and Code-Layout Relaxation

## Summary

Static compilation no longer terminates at assembly emission: assemblers (`llvm-mc`, GNU `as`), linkers (LLVM `ld.lld`, GNU `ld.bfd`), and post-link optimizers (LLVM BOLT, Google Propeller) iteratively rewrite machine code, branch encodings, alignment padding, and unwind/debug metadata after compiler codegen to satisfy silicon errata constraints, shrink PC-/GP-relative addressing, and optimize instruction-cache locality. These late rewrites violate three assumptions commonly relied upon by pre-link program verifiers and build systems:

1. **Relaxation and errata loops are not automatically monotone or single-pass.** In `lld/ELF/Writer.cpp`, thunk creation, RISC-V relaxation, and AArch64 Cortex-A53 erratum 843419 patching iterate inside a 30-pass fixed-point loop (`finalizeAddressDependentContent()`). Without explicit oscillation damping (`remove = pass < 4 ? 6 : cur - delta` for `R_RISCV_CALL`/`R_RISCV_CALL_PLT` in `lld/ELF/Arch/RISCV.cpp`), coupling a shrinkable call with `__global_pointer$`-relative `HI20`/`LO12` relaxation produces perpetual period-4 oscillation. Conversely, GNU `ld.bfd` eliminates Cortex-A53 843419 cascades via 4 KiB-padded stub sections and in-place `ADRP -> ADR` rewrites, yet recently required a no-op layout pass (`riscv_relax_pass_layout`, PR ld/34979) to prevent top-down stale-VMA estimates under `SIZEOF_HEADERS` growth from irreversibly truncating `auipc+jalr` into an overflowing `R_RISCV_JAL`.
2. **Post-codegen errata workarounds and post-link layout optimizers can invalidate pre-link functional, constant-time, speculative-execution, and power-masking proofs.** Both `ld.lld` and `ld.bfd` emit bare `B` veneers for Cortex-A53 843419 without straight-line speculation (SLS) barriers (`DSB SY; ISB`/`SB`) and omit Sequence 2. On x86-64, Intel SKX102 mitigation (`-mbranches-within-32B-boundaries`) injects `0x2e` (`CS`) prefixes onto preceding non-fusible instructions or falls back to `%rax`-referencing ModRM/SIB multi-byte NOPs (`nopl 0x0(%rax)` / `nopl 0x0(%rax,%rax,1)`), while LLVM's `X86AsmBackend::finishLayout` delimits prefix folding at `MCSymbol` boundaries (`LabeledFragments`), causing `-g` debug info to alter emitted machine bytes. Downstream, LLVM BOLT strips NOPs by default (`RemoveNops` with `KeepNops=false`), strips `repz` from `repz retq` by default (`StripRepRet=true`), re-emits preserved x86 NOPs via `MCAsmBackend::writeNopData`, and explicitly aborts (`exit(1)`) on binaries containing Cortex-A53 843419 veneers unless `--drop-cortex-a53-843419-veneers` deletes the erratum mitigation.
3. **Propeller and BOLT sit at opposite ends of the metadata-preservation vs. binary-lifting soundness spectrum, and neither removes the need for post-link ELF validation.** Propeller feeds LBR/SPE profiles back into the compiler (`-fbasic-block-sections=list=...` with `.llvm_bb_addr_map`) so compiler-native DWARF and CFI emission stays authoritative at the cost of explicit inter-cluster jumps, wider static branch encodings, and per-cluster FDEs. BOLT lifts linked ELFs to MC, rewrites `.eh_frame` (requiring `-fasynchronous-unwind-tables` for AArch64 `pac-ret` `.cfi_negate_ra_state` tracking) and DWARF v4/v5 (`DWARFRewriter`), and must undo or repair prior linker relaxations (`FixRelaxations`, `FixRISCVCallsPass`, `VeneerElimination`). Any high-assurance guarantee over functional refinement, errata absence, constant-time/speculative non-interference, or power masking must therefore be validated on the **final linked and post-link-optimized ELF bytes** (or constrained by a verified alignment-locked layout contract).

## Applicability

This report characterizes ELF linkers, x86-64/AArch64/RISC-V assemblers, post-link profile-guided optimizers, and binary-level translation validation architectures across the pinned subjects in `REPORT.json`:

- **LLVM Project (`llvm/llvm-project` at `7d9cd0de00e584d35b3bc077842790fe1bd7771d`):** Directly inspected across four coupled subsystems—`lld/ELF` (`Writer.cpp`, `AArch64ErrataFix.cpp`, `Arch/RISCV.cpp`, `Arch/X86_64.cpp`), LLVM MC (`lib/MC/MCAssembler.cpp`, `lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp`), LLVM CodeGen (`lib/CodeGen/BasicBlockSections.cpp`), and LLVM BOLT (`bolt/lib/Rewrite/{RewriteInstance,BinaryPassManager,DWARFRewriter}.cpp`, `bolt/lib/Core/{BinaryFunction,BinaryEmitter}.cpp`, `bolt/lib/Passes/{Aligner,VeneerElimination,FixRelaxationPass,FixRISCVCallsPass,PointerAuthCFIAnalyzer,ValidateMemRefs,ValidateInternalCalls}.cpp`).
- **GNU Binutils (`binutils-gdb.git` at `20a3bfdbee7e4615e96d779744e25e272beb1f4c` and `riscv-collab/riscv-binutils-gdb` at `20756b0fbe065a84710aa38f2457563b57546440`, plus local execution on Debian GNU `as` 2.47):** Directly inspected for GNU `ld.bfd` RISC-V multi-pass relaxation (`bfd/elfnn-riscv.c`), GNU `ld.bfd` AArch64 Cortex-A53 843419 mitigation (`bfd/elfnn-aarch64.c`), and GNU `as` Intel SKX102 branch alignment (`gas/config/tc-i386.c` and live x86-64 assembly execution).
- **Google Propeller (`google/llvm-propeller` at `e98f399102650de7e03e07c7299029da94d7be44`) and peer-reviewed literature:** Examined alongside LLVM's `BasicBlockSections.cpp` to compare relinking optimization (`Propeller`, ASPLOS 2023) against post-link binary rewriting (`BOLT`, CGO 2019; `Ext-TSP`, IEEE TC 2020), and evaluated against binary/ELF verification foundations (`CompCertELF`, OOPSLA 2020; seL4 binary translation validation, PLDI 2013; `Binsec/Rel`, IEEE S&P 2020; `Blade`, POPL 2021; `Coco`, USENIX Security 2021).

**Scope and target constraints:** All linker relaxation and metadata findings apply to **ELF** executables and shared objects on **x86-64**, **AArch64**, and **RISC-V (RV32/RV64 with optional RVC)**. Non-relocatable (`-r`) links skip `Writer::finalizeAddressDependentContent()`'s loop (`lld/ELF/Writer.cpp:1531`) and `_bfd_riscv_relax_section` (`bfd/elfnn-riscv.c:5942`). BOLT's relocation-mode optimizations (`BC.HasRelocations`) require binaries linked with `--emit-relocs` (`-q`); non-relocation mode cannot freely relocate functions across sections and disables passes such as `AlignerPass` (`bolt/lib/Passes/Aligner.cpp:115`) and `FixRelaxations` (`bolt/lib/Passes/FixRelaxationPass.cpp:59`). Mach-O and PE/COFF linkers, dynamic loaders (`ld.so`), and runtime JITs are outside scope unless noted in `## Boundaries`.

## Findings

### 1. Linker Relaxation Fixed Points: Architecture, Convergence, and Failure Modes

Basis: source + execution + derived

Both LLVM `ld.lld` and GNU `ld.bfd` solve a mutually recursive layout system: final instruction encodings and synthetic stubs depend on symbol virtual addresses (VAs), while symbol VAs depend on section sizes determined by those encodings and stubs. However, the two linkers partition the fixed-point iteration in fundamentally different ways.

#### 1.1 LLVM `ld.lld` Unified Address-Dependent Fixed-Point Loop

In `lld/ELF/Writer.cpp:1504-1625`, `Writer<ELFT>::finalizeAddressDependentContent()` drives all address-dependent mutations inside one `while (!ctx.arg.relocatable)` loop after an initial `ctx.script->assignAddresses()` (L1515):

1. **Target relaxation or range-extension thunks (L1532–1534):** Calls `tc.createThunks(pass, ctx.outputSections)` if `ctx.target->needsThunks` (e.g., AArch64, ARM, PPC, MIPS), or `ctx.target->relaxOnce(pass)` otherwise (e.g., RISC-V, x86-64 `GOTPCRELX` overflow un-relaxation in `lld/ELF/Arch/X86_64.cpp:507-549`). Note that LLD uses a ternary branch: a target cannot simultaneously run both `createThunks` and `relaxOnce` in the same step.
2. **Linker-script section spilling (L1535–1536):** `ctx.script->spillSections()` moves overflowing sections across memory regions.
3. **Hard pass cap (L1541–1544):** If `changed && pass >= 30`, LLD emits `"address assignment did not converge"` and breaks out of the loop.
4. **Silicon errata patchers (L1546–1555):** If `--fix-cortex-a53-843419` (AArch64) or `--fix-cortex-a8` (ARM32) is enabled, LLD refreshes `assignAddresses()` when `changed` is true and runs `a64p.createFixes()` or `a32p.createFixes()`, OR-ing the result back into `changed`.
5. **Dynamic/synthetic table sizing & pointer-auth overflow (L1557–1603):** Updates GOT, `.relr.auth.dyn` (evicting `R_AARCH64_AUTH_RELATIVE` targets wider than signed 32-bit back into `.rela.dyn`, L1567–1581), `.rela.dyn`, `.relr.dyn`, `.dynamic`, `.rela_iplt_{start,end}`, memtag descriptors, and `.eh_frame_hdr`.
6. **Address re-assignment & symbol-stability cap (L1605–1622):** Runs `changes = ctx.script->assignAddresses()`. Even when `changed == false`, if any output section address or linker-script symbol value still moved (`changes.first || changes.second`), LLD continues iterating up to `assignPasses == 5` before reporting `"address (...) of section '...' does not converge"` or `"assignment to symbol ... does not converge"`.

#### 1.2 ARM Cortex-A53 Erratum 843419: `ld.lld` vs. GNU `ld.bfd`

Basis: source + execution + derived

ARM Cortex-A53 MPCore revision 0 (`r0p0`, `r0p1`, `r0p2`, `r0p4`; ARM-EPM-048406) exhibits a pipeline hazard (Sequence 1) when four conditions hold (`lld/ELF/AArch64ErrataFix.cpp:286-369`):

1. `I1` is an `ADRP` instruction (`(instr & 0x9f000000) == 0x90000000`, L53–55) writing destination register `Rn = getRt(I1)`, placed at a 4 KiB page offset **`(VA(I1) & 0xfff) ∈ {0xff8, 0xffc}`** (L340–342, L364–367).
2. `I2` is a load/store-class instruction (`(instr & 0x0a000000) == 0x08000000`, L63–65) among single-register load/store, exclusive load/store, literal load, `STP`, `STNP`, or SIMD `ST1`, and **does not write to `Rn`** (neither as destination `Rt` of a load nor via pre-/post-indexed writeback on `Rn`, L272–284, L321–325).
3. An optional `I3` that is **not a branch** (`!isBranch(instr3)`, L229–234, L359) and does not overwrite `Rn` (note: LLD's `is843419ErratumSequence` checks `I1`, `I2`, `I4` and `!isBranch(I3)`, conservatively patching even if `I3` writes `Rn`).
4. Final instruction (`I3` in the 3-instruction form, or `I4` in the 4-instruction form) is an unsigned-immediate load/store (`(instr & 0x3b000000) == 0x39000000`, L212–214) using `Rn` as base register (`getRn(instr) == rn`, L326).

Both linkers skip scanning inline data pools via AArch64 ABI `$x` / `$d` mapping symbols (`AArch64ErrataFix.cpp:422-476`), both skip TLS IE-to-LE relaxed sequences (`AArch64ErrataFix.cpp:555-560`; `bfd/elfnn-aarch64.c:6281-6336`), and **both omit Sequence 2** (`AArch64ErrataFix.cpp:308-310`). Their patching strategies, however, diverge sharply:

| Property | LLVM `ld.lld` (`AArch64ErrataFix.cpp`) | GNU `ld.bfd` (`bfd/elfnn-aarch64.c`) |
|---|---|---|
| **In-place `ADRP -> ADR` rewrite (`±1 MiB`)** | **Never performed.** Always synthesizes a `.text.patch` veneer. | **Preferred when `ERRAT_ADR` is enabled (`full` / `adr`)** and `imm = ((decode_adrp_imm << 12) - (place & 0xfff))` fits `±1 MiB` (L5305–5318): rewrites `ADRP` to `ADR` in place, 0 extra bytes, 0 branches, sets `stub_type = aarch64_stub_none`. |
| **Out-of-line veneer contents** | 8-byte `Patch843419Section` (`.text.patch`, align 4): `[copied load/store; B (VA(ldst)+4)]` via `R_AARCH64_JUMP26` (L378, L394–420). | 8-byte `aarch64_erratum_843419_stub`: `[copied load/store; B (VA(ldst)+4)]` (L2415, L5291–5345). |
| **Stub section 4 KiB padding** | **None.** Patches are 8 bytes each, inserted after executable sections or at `getThunkSectionSpacing()` intervals (L483–527). | **Always aligned to a multiple of `0x1000` (4096 bytes)** when `ERRAT_ADRP` is enabled (`section->size = BFD_ALIGN(section->size, 0x1000)`, L4088–4096) so inserting stubs never alters `(VA & 0xfff)` of subsequent code! |
| **Cross-pass cascade behavior** | Non-4 KiB patch insertion can shift downstream `ADRP` instructions from `0xff0` to `0xff8`, triggering multi-pass cascades inside `Writer.cpp:1546-1550` (confirmed in Probe 1B.1: 3 passes vs. 2). | 4 KiB-aligned stubs preserve `(VA & 0xfff)` identically across subsequent sections, preventing stub-induced cascades (Probe 1B.1). |
| **SLS hardening (`DSB SY; ISB` / `SB`)** | **Absent.** Bare `B __CortexA53843419_<addr>` and bare `B ret` expose unmitigated Straight-Line Speculation windows. | **Absent.** Bare `0x14000000 \| (branch_offset >> 2)` (L5340–5344) lacks SLS barriers. |

#### 1.3 RISC-V Linker Relaxation: Oscillation Damping vs. Stale-VMA Truncation

Basis: source + execution + derived

RISC-V codegen emits worst-case multi-instruction sequences tagged with `R_RISCV_RELAX` and over-padded alignment blocks tagged with `R_RISCV_ALIGN` (`addend = align - 2` bytes of NOPs) so the linker can contract code as distances shrink. Comparing `lld/ELF/Arch/RISCV.cpp` against `bfd/elfnn-riscv.c` exposes three structural contrasts:

1. **Relaxation coverage (`auipc` vs. `lui` GP-relaxation):**
   - GNU `ld.bfd` implements GP-relative (`__global_pointer$`) relaxation for **both** `R_RISCV_HI20` (`lui`, `_bfd_riscv_relax_lui`, `elfnn-riscv.c:5252-5325`) **and** `R_RISCV_PCREL_HI20` (`auipc`, `_bfd_riscv_relax_pc`, `elfnn-riscv.c:5585-5710`), testing `VALID_ITYPE_IMM(symval - gp ± (max_alignment + reserve_size))` (L5317–5319, L5699–5701).
   - LLVM `ld.lld` (`RISCV.cpp:992-1033`, `relaxHi20Lo12`) relaxes `R_RISCV_HI20`/`R_RISCV_LO12_{I,S}` to `x0`-relative (`INTERNAL_R_RISCV_X0REL_{I,S}`) or `gp`-relative (`INTERNAL_R_RISCV_GPREL_{I,S}`), plus `relaxCall` (`auipc+jalr -> c.j / c.jal / jal`, L933–961), `relaxTlsLe` (L964–990), and `R_RISCV_TLSDESC_*` (L1090–1104), and **does not relax `R_RISCV_PCREL_HI20` (`auipc`) to `gp`-relative** (confirmed across `RISCV.cpp:390, 509, 603, 610`).
2. **Non-monotonicity and oscillation damping in LLD (`RISCV.cpp:1067-1076`):**
   Code shrinkage is **not globally monotone** with respect to relocation eligibility: shrinking an earlier section lowers the VA of subsequent calls/data, which *increases* forward displacement to fixed-VMA targets and shifts `__global_pointer$` downward. As demonstrated in Probe 1B.2, coupling a single forward `R_RISCV_CALL` `A` (in `sec_A`, preceding `.sdata`/`__global_pointer$`) targeting a symbol `T_A` in `sec_B` with two `R_RISCV_HI20` references (`G1`, `G2` in `sec_B`) to a fixed-VMA symbol at `gp_0 + 2046` produces a **perpetual period-4 oscillation** `(0,4,4) -> (4,4,4) -> (4,0,0) -> (0,0,0) -> (0,4,4)` when undamped:
   - Relaxing `G1, G2` (`-8 B`) pulls `T_A` inside `+1 MiB` (`1048574`), causing `A` to shrink (`-4 B`).
   - Shrinking `A` shifts `.sdata`/`gp` down by `-4 B`, pushing `M_FIXED - gp` from `2046` to `2050 > 2047` (`isInt<12>` fails), so `G1, G2` both un-relax (`+8 B`).
   - Net section growth (`+4 B`) pushes `T_A` back out of `jal` range (`1048578 > 1048574`), un-relaxing `A` (`+4 B`), restoring `gp`, and restarting the cycle until LLD aborts at `pass >= 30`.
   - LLD breaks call-driven oscillations at `RISCV.cpp:1073` by clamping call shrinkage after pass 3:
     ```cpp
     remove = pass < 4 ? 6 : cur - delta;
     relaxCall(ctx, sec, i, loc, r, remove);
     ```
     Because `remove` can only stay equal or decrease for `pass >= 4`, Probe 1B.2 confirms convergence at pass 5 to `(0, 4, 4)`. **Subtle gap:** `RISCV.cpp:1081-1089` does *not* apply this `pass < 4` clamp to `relaxHi20Lo12` or `relaxTlsLe`; oscillation remains bounded only if the feedback cycle includes at least one `R_RISCV_CALL`/`R_RISCV_CALL_PLT` site.
3. **Pass phasing and stale-VMA truncation in GNU `ld.bfd` (PR ld/34979):**
   Unlike LLD's unified loop, GNU `ld.bfd` executes discrete ordered relaxation passes registered in `bfd_elfNN_riscv_init_relax_passes` (`bfd/elfnn-riscv.c:5862-5909`) and **mutates section bytes irreversibly** (`_bfd_riscv_relax_call` shortens `auipc+jalr` into `jal` in-place rather than keeping `relaxAux` deltas until `finalizeRelax`). Because `ld.bfd` walks the linker script top-down in `lang_size_sections_1`, updating each output section's VMA right before calling `_bfd_riscv_relax_section`, an expansion of `SIZEOF_HEADERS` (e.g., `+2 * sizeof(Elf64_Phdr) = +112 B`) shifts `.text` forward *before* updating later output sections. When `max_alignment` slack (e.g., `8 B`) is smaller than header growth (`112 B`), `_bfd_riscv_relax_call` underestimates forward PC-relative distance (`1048544 + 8 <= 1048574`, Probe 1B.3) and irreversibly emits `R_RISCV_JAL`, which then fails at final relocation with `relocation truncated to fit: R_RISCV_JAL` (`true_disp = 1048656`). Commit `20a3bfdbee7e4615e96d779744e25e272beb1f4c` fixes this by prepending a no-op pass 0 (`riscv_relax_pass_layout`, `select = NULL`) before `riscv_relax_pass_shorten` (pass 1) and `riscv_relax_pass_align` (pass 2), ensuring all output section VMAs are consistent before any irreversible shortening runs.

#### 1.4 Intel SKX102 JCC Erratum: 32-Byte Alignment, Prefix Folding, `%rax`-ModRM NOPs, and Debug-Symbol Drift

Basis: normative + source + execution + derived

Intel Skylake-family processors (erratum `SKX102`, Intel Whitepaper *Mitigations for Jump Conditional Code Erratum*, 2019–2020) suffer unpredictable behavior when conditional jumps (`Jcc`) or macro-fused pairs cross 64-byte boundaries; Intel's microcode update prevents any jump (or macro-fused instruction + jump) crossing or **ending on** a 32-byte boundary from caching in the Decoded Stream Buffer (DSB / uOp cache), incurring a 0–4%+ penalty on branch-heavy loops. Both LLVM MC (`-mbranches-within-32B-boundaries`) and GNU `as` (`-mbranches-within-32B-boundaries`, equivalent to `-malign-branch-boundary=32 -malign-branch=fused+jcc+jmp -malign-branch-prefix-size=5`) mitigate this inside the assembler's layout fixed point:

1. **Exact trigger predicate (`llvm/lib/MC/MCAssembler.cpp:980-1025`):**
   `MCAssembler::layout()` iterates `relaxOnce()` until every fragment stabilizes (L703–709) and then calls `getBackend().finishLayout()` followed by a final `layoutSection` pass (L713–715). For each `MCBoundaryAlignFragment` wrapping a branch or macro-fused pair (`X86AsmBackend.cpp:448-595`), `computeBoundaryAlignSize` computes `needPadding(AlignedOffset, AlignedSize, 32)` as `mayCrossBoundary || isAgainstBoundary` (L980–984), meaning a branch **ending at offset `0x20`** (even without crossing it!) receives full padding to start at `0x20` (confirmed in Probe 1A: `cmp+je` occupying `[0x1b, 0x20)` is padded by 5 bytes to `[0x20, 0x25)`).
2. **Backward `0x2e` (`CS`) prefix folding vs. macro-fusible exclusion (`X86AsmBackend.cpp:814-928`; `gas/config/tc-i386.c:9315-9460`):**
   To avoid adding extra NOP instructions to the decoder front end, both assemblers try to absorb padding bytes by prepending redundant `0x2e` (`CS` segment override) prefixes onto preceding non-branch instructions up to `TargetPrefixMax` / `align_branch_prefix_size = 5`. Live execution with GNU `as 2.47` (Probe 1A) confirms three critical behaviors:
   - On register-only non-fusible instructions (`movq %rsi, %rcx`), `as -mbranches-within-32B-boundaries` folds two `CS` prefixes directly into the instruction: `1b: 2e 2e 48 89 f1  cs cs mov %rsi,%rcx`.
   - When the preceding instruction is either a memory operand (`movl $1, (%rdi)`) or itself macro-fusible with `Jcc` (`addq $1, %rdx`, matched by `maybe_fused_with_jcc_p`, `tc-i386.c:9327`), GAS refuses prefix folding and falls back to multi-byte NOPs.
3. **`%rax`-ModRM/SIB multi-byte NOP hazard (`X86AsmBackend.cpp:1127-1150` and live GNU `as 2.47`):**
   Both LLVM `X86AsmBackend::writeNopData` and GNU `as` emit Intel-recommended multi-byte NOPs of lengths 3–10 bytes using the `0f 1f` opcode with ModRM/SIB bytes encoding register `0` (`%rax`):
   - 3 B: `0f 1f 00` (`nopl (%rax)`)
   - 4 B: `0f 1f 40 00` (`nopl 0x0(%rax)`) — observed live at `0x1c` in Probe 1A
   - 5 B: `0f 1f 44 00 00` (`nopl 0x0(%rax,%rax,1)`) — observed live at `0x1b` in Probe 1A
   - 10 B: `66 2e 0f 1f 84 00 00 00 00 00` (`nopw %cs:0x0(%rax,%rax,1)`)
   Although architecturally a no-op, encoding `%rax` in ModRM/SIB introduces a microarchitectural register-specifier hazard analogous to implicit register-port reads identified in `Coco` (USENIX Security 2021 §3.2): on masked cryptographic code where `%rax` holds secret share `s_0` adjacent to `s_1`, an assembler-inserted `nopl 0x0(%rax,%rax,1)` can drive `%rax` onto decode/mux paths unmodeled by pre-assembly ISA verifiers. Moreover, prepending `0x2e` prefixes alters instruction-length decode groups and DSB vs. MITE decode power profiles (`Hertzbleed`, USENIX Security 2022).
4. **Debug-symbol codegen divergence (`X86AsmBackend.cpp:1038-1056`):**
   In `X86AsmBackend::finishLayout()`, LLVM collects every fragment targeted by any `MCSymbol` into `LabeledFragments` and clears the `Relaxable` candidate list whenever a labeled fragment is crossed (L1041–1055). The upstream source explicitly documents the non-determinism hazard (L1038–1040): *"The processed regions are delimitered by LabeledFragments. -g may have more MCSymbols and therefore different relaxation results."* Consequently, verifying or attesting a `-g` debug build does not guarantee byte-identical prefix/NOP encodings in a stripped release build.

---

### 2. Post-Link Profile-Guided Layout Optimizers: Meta BOLT vs. Google Propeller

Basis: normative + documentation + source + derived

Warehouse-scale binaries with tens to hundreds of megabytes of `.text` suffer severe I-cache and iTLB misses. Meta BOLT (Panchenko et al., CGO 2019; Newell & Pupyrev `Ext-TSP`, IEEE TC 2020) and Google Propeller (Shen et al., ASPLOS 2023) both optimize basic-block and function layout using hardware branch sampling (Intel LBR / ARM SPE), yet occupy diametrically opposed points in the compilation pipeline.

#### 2.1 Architectural Comparison: Post-Link Rewriting (BOLT) vs. Profile-Guided Relinking (Propeller)

| Dimension | LLVM BOLT (`bolt/` in `llvm-project`) | Google Propeller (`google/llvm-propeller` + LLVM `BasicBlockSections.cpp`) |
|---|---|---|
| **Pipeline stage** | Post-link binary rewriter: disassembles linked ELF (`--emit-relocs`) → lifts to MC + CFG → 40+ passes (`BinaryPassManager.cpp:372-593`) → re-emits ELF + rewrites metadata. | Profile-guided **relinking** optimizer: reads `.llvm_bb_addr_map` + LBR/SPE → emits compiler cluster profile (`cc_profile.txt`, v1 format: `m/u/f/c/p/g/h/t/i`) and linker symbol order (`ld_profile.txt`) → **re-compiles** with `-fbasic-block-sections=list=...` and **re-links** with `--symbol-ordering-file`. |
| **Layout algorithm** | `Ext-TSP` (Newell & Pupyrev, IEEE TC 2020) for BB layout; `HFSort`/`CDSplit` (`ReorderFunctions`, two-pass `SplitFunctions`, `BinaryPassManager.cpp:471, 489, 499`). | `Ext-TSP` chain builder (`propeller/code_layout.cc:59-142`, intra- and optional inter-function `NodeChainBuilder` + `ChainClusterBuilder`) driving compiler-emitted BB clusters (`BasicBlockSections.cpp:25-44`). |
| **CFG & Jump-Table soundness** | Must reconstruct CFG and jump tables from machine code (`BinaryFunction::buildCFG`, `ValidateMemRefs.cpp:22-53` patches cross-function `.rodata` pointers mistargeting a jump table to `BD->getAddress() - 1` + offset 1; `ValidateInternalCalls.cpp` marks non-analyzable functions ignored). | **Compiler-native CFG.** No binary lifting or jump-table guessing; `BasicBlockSections.cpp:45-64` explicitly converts inter-cluster fallthroughs into unconditional jumps and forces long relocatable inter-cluster branches. |
| **DWARF debug info preservation** | Must fully parse and rewrite `.debug_info`, `.debug_line`, `.debug_ranges`/`.debug_rnglists`, `.debug_loc`/`.debug_loclists`, `.debug_addr`, `.gdb_index`, and split DWARF `.dwo` files (`DWARFRewriter.cpp`, 2,555 LOC; converts `DW_AT_low_pc`/`high_pc` to range lists when functions split). | **Compiler-emitted DWARF** directly reflects cluster sections via standard relocations (larger `.o` relocation count and range lists, `BasicBlockSections.cpp:59-63`, but zero binary-lifting semantic drift). |
| **CFI / `.eh_frame` & AArch64 `pac-ret`** | Parses FDEs/CIEs into per-instruction MC CFI annotations, reconstructs CFI per hot/cold fragment (`BinaryEmitter.cpp:363-416`), and runs `PointerAuthCFIAnalyzer` + `PointerAuthCFIFixup` (`BinaryPassManager.cpp:375, 553`). **Fails on synchronous unwind tables** for `pac-ret` (`PointerAuthCFIAnalyzer.cpp:153-168`: warns at `>=10%` ignored functions). | **Compiler-emitted per-cluster FDEs** (`BasicBlockSections.cpp:62-63`); exception landing pads are consolidated into a dedicated `MBBSectionID::ExceptionSectionID` section (`BasicBlockSections.cpp:306-365`) with `avoidZeroOffsetLandingPad` (L396). |
| **Interaction with prior linker relaxations** | Must *undo* or repair linker relaxations before reordering: `FixRelaxations` repairs AArch64 `ADRP+ADD` relaxed from `ADRP+LDR` (`FixRelaxationPass.cpp:17-56`), `FixRISCVCallsPass` restores RISC-V relaxed calls (`FixRISCVCallsPass.cpp:19-81`), `VeneerElimination` strips range veneers (`VeneerElimination.cpp:38-224`), and `LongJmpPass`/`RISCVLongJmpPass` re-synthesize out-of-range trampolines after layout. | Runs **before** the final link, so LLD/ld.bfd performs normal single-phase linker relaxation, thunk insertion, and errata patching on the already-reordered clusters! |
| **Memory/build cost** | Requires full-binary memory during rewrite (GBs for large binaries) but needs no re-compilation of C/C++ frontends. | Scales to warehouse-scale binaries with low linker memory, requires thin-LTO/backend codegen replay (ThinLTO/Propeller relink). |

#### 2.2 How BOLT and Propeller Interact with Errata Mitigations, Constant-Time, Speculation, and Masking

Basis: source + derived

Direct inspection of `bolt/lib/Rewrite/BinaryPassManager.cpp`, `bolt/lib/Passes/VeneerElimination.cpp`, `bolt/lib/Core/BinaryEmitter.cpp`, and `bolt/lib/Passes/Aligner.cpp` reveals five concrete soundness hazards when post-link optimizers touch errata-mitigated or security-verified binaries:

1. **Hard incompatibility with AArch64 Cortex-A53 erratum 843419 veneers (`VeneerElimination.cpp:28-160`):**
   BOLT's `VeneerElimination` pass detects Cortex-A53 843419 veneers via `matchE843419Veneer(BF)`. By default (`DropCortexA53843419Veneers = false`), BOLT prints `"BOLT-ERROR: binary contains Cortex-A53 erratum 843419 workaround veneers; pass --drop-cortex-a53-843419-veneers only if the BOLTed binary will not run on Cortex-A53"` and calls **`exit(1)`** (L56–64). The root cause is structural: LLD's branch to `.text.patch` appears to BOLT's CFG builder as a tail call with zero successors, and the veneer's return branch creates a spurious secondary entry point in the caller (L83–88, L121–127, L146–151); meanwhile `LongJmpPass` would clobber scratch register `x16` if it redirected the veneer (L53–55). Even with `--drop-cortex-a53-843419-veneers`, BOLT **inlines and deletes the erratum workaround** and has no post-BOLT 843419 re-patching pass—rendering the output binary unsafe on affected Cortex-A53 silicon.
2. **Silent stripping of alignment, blanking, and AMD branch-erratum NOPs/prefixes (`BinaryPassManager.cpp:80-83, 269-272, 422-429`):**
   - `RemoveNops` runs unconditionally unless hidden flag `--keep-nops` is set (`KeepNops` defaults to `false`, L81–83, L422–423). Any SKX102 alignment padding, Spectre alignment sled, or `Coco`-style microarchitectural latch-blanking NOP emitted prior to linking is **silently deleted**.
   - `StripRepRet` runs by default on x86 (`cl::init(true)`, L269–272, L427–429), stripping `repz` from `repz retq` (the AMD K8/Family 10h branch-predictor erratum mitigation).
   - Even when `--keep-nops` is passed, `BinaryEmitter::emitFunctionBody` (`BinaryEmitter.cpp:505-515`) re-emits every sized x86 NOP through `BC.MAB->writeNopData()`, re-introducing `%rax`-ModRM multi-byte NOPs (`0f 1f ...`) and likewise emitting alignment NOPs via `Streamer.emitCodeAlignment` (`Aligner.cpp:150`, `BinaryEmitter.cpp:452-454`).
3. **Destruction of SKX102 32-byte branch alignment:**
   Because BOLT strips NOPs, reorders basic blocks (`ReorderBasicBlocks`), splits functions (`SplitFunctions`), and re-emits functions at new addresses (`AlignerPass` aligns hot function entries/blocks to 64 B, not branches to 32 B boundaries), all compiler/assembler-computed SKX102 alignments are invalidated unless BOLT's internal MC assembler is reconfigured with SKX102 boundary alignment—which itself would re-inject `0x2e` prefixes and `%rax`-ModRM NOPs.
4. **Breaking constant-time, speculative constant-time (`Blade`), and masked-execution (`Coco`) proofs:**
   - **Constant-time (`Binsec/Rel`) & cache-line invariants:** Reordering basic blocks, hot/cold splitting (`SplitFunctions`), and `AlignerPass` change instruction-cache line and BTB-set mappings across secret-independent paths; `CMOVConversion` (`BinaryPassManager.cpp:283, 477`) and `SimplifyConditionalTailCalls` (L520) alter branch/select structure. Note that `CMOVConversion` is off by default (`--cmov-conversion`), while `SimplifyConditionalTailCalls` is **on by default** (`cl::init(true)`, L240–243).
   - **Speculative constant-time (`Blade`, POPL 2021):** Moving cold blocks into `.text.cold` inserts new unconditional jumps and splits straight-line fallthroughs; `RetpolineInsertion` (`BinaryPassManager.cpp:571-572`) mitigates indirect-branch Spectre v2 if enabled, but BOLT does not preserve `Blade` `protect` cut invariants or SLS barriers across newly synthesized jumps/trampolines (`LongJmpPass`).
   - **Power masking (`Coco`, USENIX Security 2021):** `RegReAssign` (`--reg-reassign`, L234–238, L453) rewrites physical register numbers to drop REX prefixes, which can collide distinct secret shares (`s_0`, `s_1`) onto the same physical register or mux-tree glitch bank; `RemoveNops` and block reordering break cycle-exact latch blanking schedules.
5. **Propeller's advantage and residual hazard:**
   Because Propeller runs *before* assembly and final linking (`BasicBlockSections.cpp` + LLD `--symbol-ordering-file`), the final assembler (`-mbranches-within-32B-boundaries`) and linker (`--fix-cortex-a53-843419`) run *after* block clustering—preserving errata safety and compiler-native DWARF/CFI. However, Propeller's `p` cloning paths (`propeller_profile_format.md:92-105`), `t`/`i` code prefetch hints (L132–162), and hot/cold splitting still mutate CFG topology, branch encodings, and I-cache/BTB placement relative to unprofiled builds; security-critical cryptographic functions must be excluded from profile-guided splitting/cloning (e.g., placed in an unsplit section excluded from `BasicBlockSections` profiles) if pre-link layout invariants are assumed.

---

### 3. Post-Link ELF Translation Validation and Minimal-TCB Binary Verification

Basis: normative + source + derived

When assemblers, linkers, and post-link optimizers remain outside the Trusted Computing Base (TCB), security and functional claims established on source code, LLVM IR (`Alive2`), or relocatable `.o` files do not automatically transfer to the final ELF image.

#### 3.1 Taxonomy of Verification Approaches Across the Post-Link Boundary

| System / Paper | Verified Input → Output Boundary | TCB & Proof Method | Handles Linker Relaxation / Errata / BOLT? |
|---|---|---|---|
| **CompCertELF** (Wang et al., OOPSLA 2020, DOI `10.1145/3428265`) | Clight / CompCert Asm → relocatable ELF `.o` + verified linker model | Coq proof of separate compilation and linking commutativity down to ELF object encodings. | Models standard relocations and static linking; does **not** cover LLD/ld.bfd RISC-V shrinking relaxation, Cortex-A53 843419 veneer injection, SKX102 prefix folding, or BOLT post-link rewriting. |
| **seL4 Binary Translation Validation** (Sewell, Myreen & Klein, PLDI 2013, DOI `10.1145/2491956.2462183`) | Verified C (`seL4`) → linked ARM ELF binary | Post-link binary lifter + SMT-assisted refinement proof checked in Isabelle/HOL against ARM ISA semantics. | **Post-link by construction:** validates the actual linked ELF image (removing GCC and the linker from the TCB), though loop-alignment heuristics assume largely compiler-preserving CFG structure and do not verify microarchitectural CT/masking/errata properties. |
| **Binsec/Rel** (Daniel, Bardin & Rezk, IEEE S&P 2020, DOI `10.1109/SP40000.2020.00074`, `binsec/binsec` `9749bd8aed`) | Linked ELF binary (x86/ARM/RISC-V) → relational CT verdict | Binary-level relational symbolic execution (`DBA` IR) checking architectural PC and memory-address equivalence across secret inputs. | Validates **final ELF bytes** (catching compiler/linker-introduced CT regressions), bounded to explored paths/loop unrollings; does not validate functional equivalence or hardware power/errata predicates. |
| **BOLT Built-in Self-Checks** (`VerifyCFG`, `ValidateMemRefs`, `ValidateInternalCalls`, `PointerAuthCFIAnalyzer`) | Internal MC CFG between BOLT passes | Structural invariants (CFG edge consistency, jump-table ownership, frame/stack analysis, AArch64 `RAState` sign/auth pairing). | **Heuristic safety guards, not semantic translation validation:** catches specific lifting/CFG bugs and marks ambiguous functions ignored, but proves neither functional equivalence nor constant-time/errata preservation. |

#### 3.2 Requirements for a Minimal-TCB Post-Link ELF Validator

To close the gap between pre-link proofs and post-link execution without placing LLD, GNU `ld`, GAS, BOLT, or Propeller in the TCB, a post-link ELF validator operating directly on final executable load segments `B_final : VA -> u8` must discharge five orthogonal obligations:

1. **ISA-Exact Decoding & CFG/Relocation Closure:** Decode all executable `PT_LOAD` segments using a verified ISA decoder (e.g., `Sail`-derived semantics) honoring ABI mapping symbols (`$x`/`$d` on AArch64), verifying that every resolved PC-relative displacement (`R_RISCV_JAL`, `R_AARCH64_JUMP26`, `R_X86_64_PC32`), indirect jump table, and linker/BOLT veneer targets a valid instruction boundary within its authorized function or veneer set.
2. **Functional Semantic Refinement (`Pre-Link ⊑ Post-Link`):** Verify block-to-block simulation (as in seL4's PLDI 2013 validator) modulo known semantics-preserving rewrites: linker `auipc+jalr -> jal` contraction, `ADRP -> ADR` substitution, `GOTPCRELX` load-to-LEA relaxation, 8-byte errata veneer detours (proving `[copied ldst; B (VA+4)]` preserves architectural state and touches no caller-live registers), and BOLT/Propeller basic-block permutation/splitting.
3. **Linear-Time Silicon Errata Audit (`O(|B_final|)`):** Scan the finalized byte image at its actual runtime page/cache offsets:
   - *AArch64 Cortex-A53 843419:* assert zero unpatched Sequence 1 (and optionally Sequence 2) matches at `(VA & 0xfff) ∈ {0xff8, 0xffc}`, and if any veneers exist, assert every veneer and call site satisfies SLS barrier policy (`DSB SY; ISB` or `SB` if required).
   - *x86-64 Intel SKX102:* assert zero `Jcc`/`JMP`/macro-fused instructions satisfy `mayCrossBoundary(VA, size, 32) || isAgainstBoundary(VA, size, 32)`, and for masked/constant-time regions, assert zero forbidden `%rax`-ModRM NOPs (`0f 1f ...`) and zero unexpected `0x2e` prefix injections inside atomic masked bundles.
4. **Unwind & Debug Metadata Consistency:** Independently replay `.eh_frame` FDE/CIE programs across every post-link address range (including BOLT hot/cold fragments and Propeller cluster sections) to verify contiguous non-overlapping coverage, valid CFA/callee-saved register recovery at every call/trap PC, and exact `pac-ret` `.cfi_negate_ra_state` parity at every `paciasp`/`autiasp` site (matching `PointerAuthCFIAnalyzer`'s invariant without relying on BOLT to enforce it).
5. **Post-Link Security & Microarchitectural Re-Check:** Re-verify constant-time (`Binsec/Rel`), speculative cut placement (`Blade` transient/stable typing over the *post-link* CFG including any inserted veneers or cold-split jumps), and hardware-contract latch-blanking/share-disjointness invariants directly on `B_final`, binding any deployment attestation to `(H(B_final), CPUID, microcode_rev)`.

#### 3.3 Alignment-Locked Verified Layout (Preventing Post-Link Pass Collisions)

For verified cryptographic and kernel kernels where post-link errata mutation would invalidate proofs, the cleanest architectural resolution is **monotone alignment-locked layout before final verification**:
- Anchor verified code shards on 4 KiB page boundaries so `(VA & 0xfff)` is link- and 4 KiB-ASLR-invariant; clear any AArch64 `0xff8`/`0xffc` `ADRP` window with 1–2 `NOP` (`0xD503201F`) hints placed at explicitly designated safe padding slots *outside* masked/atomic regions (synthesizing zero `.text.patch` veneers).
- On x86-64, forbid backward `0x2e` prefix folding across masked regions and restrict SKX102 boundary padding to zero-register-read NOPs (`0x90` or `nopl 0(%r_blk)` using a dedicated zeroed scratch register) outside atomic blocks, eliminating `-g` `LabeledFragments` divergence.
- Exclude verified constant-time/masked sections from BOLT (`--skip-funcs`) and Propeller basic-block splitting, and run the linear-time post-link validator as a mandatory release gate.

## Boundaries

- **ARM Cortex-A53 Erratum 843419 Sequence 2 (`not examined` in live silicon / `unsupported` in `ld.lld` and `ld.bfd`):** Both `lld/ELF/AArch64ErrataFix.cpp:308-310` and `bfd/elfnn-aarch64.c` explicitly omit Sequence 2 detection; this report did not audit whether modern LLVM/GCC instruction schedulers can still emit Sequence 2 under aggressive inline assembly or hand-written kernels.
- **LLD RISC-V non-call relaxation oscillation (`unknown`):** Inspection of `lld/ELF/Arch/RISCV.cpp:1067-1089` shows the `pass < 4` monotonicity clamp is applied only to `R_RISCV_CALL`/`R_RISCV_CALL_PLT` and not to `relaxHi20Lo12` or `relaxTlsLe`. Whether a pure `HI20`/`TLS_LE`-only linker script without any `R_RISCV_CALL` can construct a self-sustaining oscillation cycle in LLD was not exhaustively resolved by a full LLD binary execution probe.
- **Alternative linkers (`mold`, `ld.gold`, Apple `ld64`, `lld-link`) (`not examined`):** `rui314/mold` (`331ac663668dc0b1f4949403854613b9b1913025`) was checked for source layout (`arch/elf-{arm64,riscv64}/lib.rs`), but its relaxation and errata-handling internals were not deeply audited; conclusions about `ld.lld` and `ld.bfd` do not automatically generalize to `mold`, Mach-O `ld64`, or COFF `lld-link`.
- **Intel microarchitectural decode of `0f 1f` ModRM `%rax` on closed x86 silicon (`unknown`):** While `X86AsmBackend.cpp:1134-1150` and live GNU `as 2.47` execution definitively establish that multi-byte x86 NOPs encode `%rax` in ModRM/SIB bytes, closed-source x86-64 cores (Skylake through Arrow Lake) do not publish gate-level RTL; whether a specific stepping suppresses register-file mux switching on `0f 1f` at pre-decode vs. decode is empirically hardware-dependent (`known not to apply` uniformly across all microarchitectures without silicon-specific TVLA/gate verification).
- **LLVM `llvm-mc` live `-g` vs. non-`-g` SKX102 binary execution (`not examined` locally):** The local execution host lacked a `clang`/`llvm-mc` binary, so the live SKX102 execution probe ran on Debian GNU `as 2.47` (`gas`), while LLVM MC's `LabeledFragments` `-g` drift is established directly from upstream source (`X86AsmBackend.cpp:1038-1056`). Note also that in Probe 1A, GNU `as 2.47` *did* fold `0x2e` prefixes across a trailing `.Lbarrier:` and even a global `mid_sym:` placed *after* `movq %rsi, %rcx` and *before* `cmpq`—showing GAS's prefix-insertion frag sits *before* the padded instruction rather than relying on LLVM's post-layout backward `LabeledFragments` scan (`known not to apply` identically between GAS and LLVM MC).
- **Stronger claim not established:** Passing BOLT's `--verify-cfg`, `ValidateMemRefs`, `ValidateInternalCalls`, and `PointerAuthCFIAnalyzer` checks does **not** establish semantic equivalence or side-channel preservation; conversely, disabling post-link optimization does not guarantee errata freedom if the assembler or linker itself injects unverified patches.

## Evidence

### 1. Upstream Source Anchors (Observed 2026-11-19)

| Subject | Commit / Version | Path & Lines / Symbols | Verified Fact |
|---|---|---|---|
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `lld/ELF/Writer.cpp:1504-1625` (`finalizeAddressDependentContent`) | Fixed-point loop combining `createThunks`/`relaxOnce`, `spillSections`, `fixCortexA53Errata843419` (`a64p.createFixes()`), `.relr.auth.dyn` eviction; 30-pass cap (L1541) + 5-pass `assignPasses` cap (L1613). |
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `lld/ELF/AArch64ErrataFix.cpp:53-656` (`is843419ErratumSequence`, `scanCortexA53Errata843419`, `Patch843419Section`, `insertPatches`, `implementPatch`) | Matches Sequence 1 at `(VA & 0xfff) ∈ {0xff8, 0xffc}`, omits Sequence 2 (L308–310), emits 8-byte `.text.patch` `[ldst; B ret]` without `ADR` rewrite, without 4 KiB stub alignment, and without SLS barriers. |
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `lld/ELF/Arch/RISCV.cpp:933-1158` (`relaxCall`, `relaxTlsLe`, `relaxHi20Lo12`, `relax`, `relaxOnce`) | Relaxes `CALL`, `TPREL`, `HI20/LO12` (`x0`/`gp`), `TLSDESC`, `R_RISCV_ALIGN`; omits `PCREL_HI20 -> gp`; applies `remove = pass < 4 ? 6 : cur - delta` oscillation damping to `CALL` only (L1073). |
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `lld/ELF/Arch/X86_64.cpp:507-549` (`X86_64::relaxOnce`) | Un-relaxes overflowing `R_RELAX_GOT_PC` / `R_RELAX_GOT_PC_NOPIC` back to `R_GOT_PC` when `maxVA >= 2^31`. |
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `llvm/lib/MC/MCAssembler.cpp:668-735, 980-1025` (`layout`, `needPadding`, `computeBoundaryAlignSize`, `relaxBoundaryAlign`) | `needPadding` triggers on `mayCrossBoundary || isAgainstBoundary`; `finishLayout()` runs post-relaxation followed by a final `layoutSection`. |
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp:814-928, 1024-1150` (`padInstructionViaPrefix`, `finishLayout`, `writeNopData`) | Backward prefix folding delimited by `LabeledFragments` (`-g` drift documented at L1038–1040); `Nops32Bit` (L1129–1150) encodes `%rax` in ModRM/SIB for 3–10 byte NOPs. |
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `bolt/lib/Rewrite/BinaryPassManager.cpp:80-83, 240-298, 372-593` | Default pass pipeline: `RemoveNops` on (`KeepNops=false`), `StripRepRet` on (`true`), `SimplifyConditionalTailCalls` on (`true`), `CMOVConversion` off, `RegReAssign` off; `PointerAuthCFIAnalyzer`/`Fixup`, `FixRelaxations`, `VeneerElimination`, `FixRISCVCallsPass`, `LongJmpPass`. |
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `bolt/lib/Passes/VeneerElimination.cpp:28-160` | Calls `exit(1)` on Cortex-A53 843419 veneers unless `--drop-cortex-a53-843419-veneers` inlines and removes the erratum workaround; documents tail-call CFG/secondary-entry interaction. |
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `bolt/lib/Core/BinaryEmitter.cpp:363-518`, `bolt/lib/Passes/PointerAuthCFIAnalyzer.cpp:38-169`, `bolt/lib/Passes/ValidateMemRefs.cpp:22-102`, `bolt/lib/Passes/Aligner.cpp:67-152` | Re-emits per-fragment FDEs/LSDAs; re-emits x86 NOPs via `writeNopData` (L507–515); `PointerAuthCFIAnalyzer` requires `-fasynchronous-unwind-tables` (L164–167); `ValidateMemRefs` shifts cross-function JT references to `addr - 1` (L45–47). |
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `llvm/lib/CodeGen/BasicBlockSections.cpp:22-86, 306-396` | Documents Propeller `-fbasic-block-sections=list`, explicit inter-cluster jumps, long inter-cluster branches, per-cluster FDEs, `ExceptionSectionID`, and `.llvm_bb_addr_map`. |
| `google/llvm-propeller` | `e98f399102650de7e03e07c7299029da94d7be44` | `propeller/code_layout.cc:42-225`, `propeller/propeller_profile_format.md:11-240` | `Ext-TSP` chain/cluster builder and v1 profile spec (`m`, `u`, `f`, `c`, `p`, `g`, `h`, `t`, `i` directives). |
| `binutils-gdb.git` (Sourceware) | `20a3bfdbee7e4615e96d779744e25e272beb1f4c` | `bfd/elfnn-riscv.c:5252-5325, 5585-5710, 5860-6030` (PR ld/34979) | Three-pass RISC-V relaxation (`layout` -> `shorten` -> `align`); both `lui` (`_bfd_riscv_relax_lui`) and `auipc` (`_bfd_riscv_relax_pc`) relax to `gp`; pass-0 `riscv_relax_pass_layout` added to prevent stale-VMA `R_RISCV_JAL` truncation under `SIZEOF_HEADERS` growth. |
| `riscv-collab/riscv-binutils-gdb` | `20756b0fbe065a84710aa38f2457563b57546440` | `bfd/elfnn-aarch64.c:4088-4170, 5260-5365, 6281-6336`; `gas/config/tc-i386.c:686-742, 9315-9460` | GNU `ld.bfd` Cortex-A53 843419 `ADRP -> ADR` rewrite (`ERRAT_ADR`, L5310–5318), 4 KiB-aligned stub sections (`BFD_ALIGN(..., 0x1000)`, L4096), TLS relaxation clearing (`clear_erratum_843419_entry`); GAS `align_branch` / `align_branch_prefix_size = 5` / `maybe_fused_with_jcc_p`. |

### 2. Execution Probe 1A: Live GNU `as 2.47` x86-64 Intel SKX102 Mitigation

**Environment:** Linux x86-64, `GNU assembler (GNU Binutils for Debian) 2.47`, `GNU objdump 2.47`, executed 2026-11-19.

**Reproducer commands and observed disassembly:**
```sh
cat <<'EOF' > /tmp/skx_nop.s
.text
.p2align 5
.globl skx_nop
skx_nop:
    .fill 21, 1, 0x90
    movl $1, (%rdi)
    cmpq %rsi, %rdi
    je .Ltarget
    ret
.Ltarget:
    xorl %eax, %eax
    ret
EOF
as -o /tmp/skx_unmit.o /tmp/skx_nop.s
as -mbranches-within-32B-boundaries -o /tmp/skx_mit.o /tmp/skx_nop.s
objdump -d /tmp/skx_unmit.o /tmp/skx_mit.o
```
- **Unmitigated (`/tmp/skx_unmit.o`):** `1b: 48 39 f7 cmp %rsi,%rdi; 1e: 74 01 je 21` (ends exactly at `0x20` — `isAgainstBoundary`).
- **Mitigated (`/tmp/skx_mit.o`):** Inserts 5-byte `%rax`-ModRM/SIB NOP `1b: 0f 1f 44 00 00  nopl 0x0(%rax,%rax,1)` before pushing `cmp+je` to `0x20`. (With `.fill 24` + `addq $1, %rdi`, GAS emits 4-byte `1c: 0f 1f 40 00  nopl 0x0(%rax)`.)
- **Prefix folding (`/tmp/skx_mov.s`, replacing `movl $1, (%rdi)` with `.fill 24` + `movq %rdi, %rdx; movq %rsi, %rcx`):** `as -mbranches-within-32B-boundaries` emits `1b: 2e 2e 48 89 f1  cs cs mov %rsi,%rcx`, folding two redundant `CS` prefixes into the preceding non-fusible register move to push `cmp+je` to `0x20`.

### 3. Execution Probe 1B: Linker Relaxation Cascade, Oscillation, and PR ld/34979 Stale-VMA Models

**Environment:** Python 3.13.15, executed 2026-11-19.

```python
MAX_JAL = (1 << 20) - 2  # +1048574

def run_riscv_osc(damped: bool):
    # sec_A (VA=0): Call A (8B->4B) targeting T_A in sec_B
    # .sdata (follows sec_A): gp = size(sec_A) + 0x800
    # sec_B (base=0x1000+size(sec_A)): HI20 G1, G2 targeting fixed M_FIXED=(8+0x800)+2046; T_A at MAX_JAL-0x1000
    rem_A = rem_G1 = rem_G2 = 0
    M_FIXED = (8 + 0x800) + 2046
    TA_OFF = MAX_JAL - 0x1000
    trace = []
    for p in range(12):
        size_A = 8 - rem_A
        va_gp = size_A + 0x800
        va_TA = (0x1000 + size_A) + TA_OFF - (rem_G1 + rem_G2)
        max_A = 6 if (not damped or p < 4) else rem_A
        nA = 4 if (max_A >= 4 and va_TA <= MAX_JAL) else 0
        gp_diff = M_FIXED - va_gp
        nG = 4 if (-2048 <= gp_diff <= 2047) else 0
        changed = (nA, nG, nG) != (rem_A, rem_G1, rem_G2)
        rem_A, rem_G1, rem_G2 = nA, nG, nG
        trace.append((p, (rem_A, rem_G1, rem_G2)))
        if not changed:
            break
    return trace
```

**Observed outputs:**
- **Cortex-A53 843419 cascade (`sec0` ADRP at `0xff8`, `sec1` ADRP at `0xff0`):**
  - `lld_8B_between`: 3 passes — pass 1 patches `sec0` at `0x400ff8` (`+8 B`), shifting `sec1` to `0x401008` so its ADRP lands at `0x401ff8`; pass 2 patches `sec1`; pass 3 converges.
  - `bfd_4KiB_padded`: 2 passes — pass 1 patches `sec0` (`+0x1000`), shifting `sec1` to `0x402000` (`ADRP` stays `0xff0`); pass 2 finds 0 hits.
  - `bfd_adr_rewrite`: 2 passes — pass 1 rewrites `ADRP -> ADR` (`+0 B`), `sec1` remains at `0x401000`.
- **RISC-V `Call <-> __global_pointer$ <-> 2x HI20` oscillation:**
  - `run_riscv_osc(damped=False)`: `[(0,(0,4,4)), (1,(4,4,4)), (2,(4,0,0)), (3,(0,0,0)), (4,(0,4,4)), ...]` (non-convergent period-4 cycle).
  - `run_riscv_osc(damped=True)` (LLD `pass < 4` cap): `[(0,(0,4,4)), (1,(4,4,4)), (2,(4,0,0)), (3,(0,0,0)), (4,(0,4,4)), (5,(0,4,4))]` (converged at pass 5).
- **GNU `ld.bfd` PR ld/34979 stale-VMA truncation (`old_text=0x10000`, `old_far=0x110050`, `hdr_growth=112 B`, `max_alignment=8 B`):**
  - Without pass-0 layout: `stale_disp + max_align = 1048544 + 8 = 1048552 <= 1048574` -> falsely shortens to `jal`, then fails at final `true_disp = 1048656 > 1048574`.
  - With pass-0 `riscv_relax_pass_layout`: `refreshed_disp + max_align = 1048664 > 1048574` -> preserves `auipc+jalr`.

## Revalidation

Use the following targeted checks when evaluating newer LLVM/LLD/BOLT, GNU Binutils, or Propeller revisions:

1. **LLD relaxation loop & errata diff check:** Diff `lld/ELF/Writer.cpp` (`finalizeAddressDependentContent`), `lld/ELF/AArch64ErrataFix.cpp` (`is843419ErratumSequence`, `Patch843419Section`, `insertPatches`), and `lld/ELF/Arch/RISCV.cpp` (`relax`, `relaxHi20Lo12`) against `7d9cd0de00e584d35b3bc077842790fe1bd7771d`. Specifically check whether LLD adds `ADRP -> ADR` rewriting, 4 KiB stub alignment, SLS barriers (`DSB SY; ISB`/`SB`) in `.text.patch`, `R_RISCV_PCREL_HI20` GP-relaxation, or `pass < 4` damping on `relaxHi20Lo12`.
2. **BOLT errata & NOP-preservation check:** Diff `bolt/lib/Passes/VeneerElimination.cpp` (`DropCortexA53843419Veneers`), `bolt/lib/Rewrite/BinaryPassManager.cpp` (`KeepNops`, `StripRepRet`, `SimplifyConditionalTailCalls`), and `bolt/lib/Core/BinaryEmitter.cpp` (`writeNopData` call at NOP re-emission). Verify whether BOLT gains a post-layout AArch64 843419 re-patching pass or preserves raw NOP byte encodings under `--keep-nops`.
3. **Assembler SKX102 & `-g` drift probe:** Re-run Probe 1A on the target `as` and `llvm-mc`/`clang` (`-mbranches-within-32B-boundaries`, with and without `-g`) and inspect `objdump -d` bytes at the 32-byte boundary for `0f 1f` ModRM `%rax` NOPs, `0x2e` CS prefixes, and debug-vs.-stripped byte divergence.
4. **GNU `ld.bfd` RISC-V pass-table check:** Check `bfd_elfNN_riscv_init_relax_passes` in `bfd/elfnn-riscv.c` to verify `riscv_relax_pass_layout` (or equivalent pre-shorten VMA synchronization) remains ahead of irreversible shortening passes, and re-run `pr34979-rv32.d` / `pr34979-rv64.d` from the GNU `ld` testsuite.
5. **Post-link release gate audit:** On any target ELF binary after linking and any BOLT/Propeller pass, run an `O(|.text|)` scanner verifying zero unpatched AArch64 843419 hits, zero SKX102 32-byte violations, zero `%rax`-ModRM NOPs inside annotated masked functions, and full `.eh_frame` FDE/`pac-ret` coverage across all split fragments.
