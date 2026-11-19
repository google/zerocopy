# CPU Silicon Errata, Microcode Hot-Patching, and Post-Compile Assembler/Linker Binary Mutation

## Summary

Formal compiler verification (such as CompCert, CakeML, or Jasmin) and binary-level proof-carrying or constant-time verification typically treat the ISA specification as an immutable hardware semantics and the compiler's emitted assembly or object stream as the final executable bytes. Both assumptions fail on real silicon. Across three decades of x86-64 and AArch64 processors, architectural silicon defects have broken ISA semantics outright (Pentium P5 FDIV SRT table omissions, Intel Skylake/Kaby Lake `SKL150`/`SKW144`/`SKX150`/`SKZ7`/`KBL095` short-loop high-byte register corruption, Intel TSX `HSW136`/`SKL105` transactional memory defects, and Raptor Lake clock-tree $V_{\min}$ shift hardware aging), while field workarounds have moved semantic and binary mutation **downstream of the compiler** into three unverified layers:

1. **Assembler-level instruction mutation** (Intel JCC Erratum `SKX102`/`SKL167`/`KBL129`): GNU `as` (`-mbranches-within-32B-boundaries`) and LLVM MC (`-x86-branches-within-32B-boundaries`) inject redundant `CS` (`0x2e`) segment-override prefixes (up to 5 bytes per instruction), widen instruction encodings via relaxation, insert multi-byte `NOP`s, force 32-byte section alignment, and shift every downstream branch offset *after* compiler code generation and register allocation.
2. **Link-time binary rewriting and veneer synthesis** (ARM Cortex-A53 Errata `843419` and `835769`): GNU `ld.bfd` and LLVM `lld` (`--fix-cortex-a53-843419`, `--fix-cortex-a53-835769`) scan already-assembled `.text` bytes after virtual address assignment, overwrite instructions in place with unconditional `B <veneer>` branches (or rewrite `ADRP` to `ADR`), synthesize out-of-line 8-byte `.text.patch`/`.stub` veneer sections, relocate memory operands into the veneer, and iterate to a fixpoint because each inserted veneer can push downstream `ADRP` instructions onto page offsets `0xFF8`/`0xFFC`.
3. **Runtime microcode hot-patching** (Intel `MSR_IA32_UCODE_WRITE` `0x79`, AMD `MSR_AMD64_PATCH_LOADER`): late OS microcode updates mutate architectural features (`CPUID` flags such as `RTM_ALWAYS_ABORT`, `TSX_CTRL`), microarchitectural pipelines (disabling the Loop Stream Detector or banning 32-byte-straddling branches from the Decoded ICache/DSB), and instruction side effects underneath live processes without changing a single byte of the binary. Conversely, microcode signature verification flaws such as AMD EntrySign (`CVE-2024-56161`) show that microcode loaders themselves sit inside the hardware Root of Trust for confidential computing (SEV-SNP).

For any verified compiler or binary-level assurance argument targeting real hardware, the trusted computing base (TCB) must therefore either (a) anchor verification *post-link* on the final linked ELF/Mach-O/PE bytes with explicit microcode/stepping attestation, or (b) formalize and constrain assembler relaxation, linker errata passes, and hardware stepping/microcode preconditions explicitly.

## Applicability

This report characterizes the interaction between **architectural CPU silicon defects**, **runtime microcode updates**, and **post-compile toolchain binary mutation** across x86-64 and AArch64 platforms. The examined subjects in `REPORT.json` relate to one another as follows:

- **Assembler-level binary mutation (`llvm/llvm-project` `1780833aa0f119a425d7f993aaac29d03cb04da6`, `riscv-collab/riscv-binutils-gdb` `20756b0fbe065a84710aa38f2457563b57546440`, local `GNU Binutils 2.47`, and `rustc 1.98.0-nightly` / `LLVM 22.1.6`)**: source inspection of `X86AsmBackend.cpp` and `gas/config/tc-i386.c` is paired with direct execution of GNU `as 2.47` and `rustc`/`LLVM 22.1.6` on x86-64 Linux (`x86_64-unknown-linux-gnu`) to observe exact byte-level instruction prefixing, NOP insertion, branch displacement mutation, and section alignment escalation under Intel JCC Erratum mitigations (`Intel Document 341810-001`).
- **Compiler- and linker-level AArch64 errata patching (`llvm/llvm-project` `1780833aa0f119a425d7f993aaac29d03cb04da6`, `riscv-collab/riscv-binutils-gdb` `20756b0fbe065a84710aa38f2457563b57546440`, `ARM-EPM-048406`)**: source inspection compares LLVM's compiler pass (`AArch64A53Fix835769.cpp`), LLD's linker patcher (`lld/ELF/AArch64ErrataFix.cpp`), and GNU BFD's linker patchers (`bfd/elfnn-aarch64.c` for both `843419` and `835769`), supplemented by a standalone Python bitmask and address-cascade verification script matching the exact LLD encoding predicates.
- **OS-level microcode hot-patching and TSX control (`torvalds/linux` `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `intel/Intel-Linux-Processor-Microcode-Data-Files` `d71fe4e2f0f70a49ebbac7f2c7e915f181361974`, `google/security-research` `dd9c753bdb2ae51e8214e50be313283daa400713`)**: source inspection of Linux's Intel/AMD microcode loaders and TSX control logic, Intel's published Raptor Lake microcode release tables, and Google Security Research's AMD EntrySign (`CVE-2024-56161`) PoC documentation.
- **Historical arithmetic and microarchitectural errata (`Edelman 1997`, Intel Specification Updates)**: primary mathematical analysis of the P5 Pentium FDIV SRT division defect, Intel Skylake/Kaby Lake short-loop LSD register corruption (`SKL150`/`SKW144`/`SKX150`/`SKZ7`/`KBL095`), Intel TSX functional and side-channel errata (`HSW136`/`SKL105`/`CVE-2019-11135`), and Raptor Lake $V_{\min}$ shift aging.

Findings about assembler/linker mutation apply whenever the relevant mitigation flags are enabled (explicitly via `-mbranches-within-32B-boundaries`, `-x86-branches-within-32B-boundaries`, `--fix-cortex-a53-843419`, `--fix-cortex-a53-835769`, or implicitly by target-default toolchain drivers on Linux/Android/embedded AArch64 targets). Byte offsets observed in local execution probes are exact for `GNU Binutils 2.47` and `rustc 1.98.0-nightly` (`LLVM 22.1.6`) on `x86_64-unknown-linux-gnu`; exact padding choices may vary across other compiler/assembler versions, while the structural invalidation of pre-assembly/pre-link byte-exactness proofs holds generally whenever post-codegen relaxation or link-time veneer synthesis is active.

## Findings

### 1. Taxonomy of Silicon Errata and Their Impact on Formal Verification Assumptions

**Basis:** normative + documentation + source + derived

Verified compilers and ISA-level proof frameworks implicitly rely on a four-layer trust chain:

```text
Source Semantics  --[Verified Compiler]-->  Assembly / Relocatable Object (.o)
                  --[Assembler / Linker]--> Final Executable Binary (ELF)
                  --[Microcode / Decode]--> Hardware Execution Semantics (ISA)
```

Silicon defects and their field workarounds rupture every boundary in this chain in distinct ways:

| Defect / Erratum | Affected Silicon | Defect Class | Primary Mitigation Layer | Verification Invariant Broken |
| :--- | :--- | :--- | :--- | :--- |
| **Pentium FDIV** (P5, 1994) | Intel Pentium P5 (60–100 MHz) | Deterministic arithmetic logic error (5 missing PLA entries in radix-4 SRT lookup table) | Silicon recall ($475M); software trap/emulation wrappers | IEEE 754 `fdiv` functional soundness; hardware ISA refines spec |
| **Skylake/Kaby Lake LSD Short-Loop Bug** (`SKL150`, `SKW144`, `SKX150`, `SKZ7`, `KBL095`, `KBW095`) | Intel 6th/7th Gen Core & Xeon (with Hyper-Threading active) | Microarchitectural pipeline corruption (short loops `< 64` insns mixing `AH`/`BH`/`CH`/`DH` with wider parent registers under SMT) | Microcode update (disabling Loop Stream Detector) or BIOS HT disable | Deterministic ISA register-file semantics for valid compiler-emitted code |
| **Intel TSX Errata & TAA** (`HSW136`, `BDE42`, `SKL105`, `CVE-2019-11135`) | Intel Haswell, Broadwell, Skylake, Cascade Lake | Functional memory-ordering/transactional corruption + speculative buffer leakage on async abort | Microcode + OS MSR control (`MSR_TSX_FORCE_ABORT` `0x10F`, `MSR_IA32_TSX_CTRL` `0x122`, `MSR_IA32_MCU_OPT_CTRL` `0x123`) | Static ISA feature availability (`CPUID.RTM`/`HLE`) and transactional atomicity/isolation |
| **Intel JCC Erratum** (`SKX102`, `SKL167`, `KBL129`) | Intel Skylake through Comet Lake / Cascade Lake | DSB (Decoded ICache) corruption on branches crossing or ending at 32-byte boundaries | Microcode (bans affected 32B lines from DSB) + **Assembler binary mutation** (prefix/NOP padding) | Post-compiler byte-exactness, relative jump offsets, instruction encodings, section alignment, and I-cache CT layout |
| **ARM Cortex-A53 Erratum 843419** | ARM Cortex-A53 `r0p0`, `r0p1`, `r0p2`, `r0p4` | Memory address miscalculation on `ADRP` at page offset `0xFF8`/`0xFFC` followed by load/store | **Linker binary rewriting** (`ADRP`→`ADR` or in-place `B <veneer>` + synthetic `.text.patch` stub) | Post-assembly CFG integrity, instruction addresses, pre-link object proofs, and single-pass layout stability |
| **ARM Cortex-A53 Erratum 835769** | ARM Cortex-A53 `r0p0`–`r0p4` | 64-bit integer MAC (`MADD`/`MSUB`/`*MADDL`/`*MSUBL`, `Ra != XZR`) immediately after memory op produces wrong result | Compiler `NOP` insertion (`AArch64A53Fix835769`) or **Linker veneer patching** (`--fix-cortex-a53-835769`) | Compiler/linker byte-exactness, cycle counts, and instruction stream identity |
| **Raptor Lake $V_{\min}$ Shift Instability** (2024–2025) | Intel 13th/14th Gen Core desktop (`RPL-S`/`HX`/`E`, e.g., CPUID `06-b7-01` B0) | Physical reliability aging of IA core clock-tree circuit under elevated voltage/temperature (irreversible duty-cycle skew) | Preventative microcode updates (`0x125`, `0x129`, `0x12B`, `0x12F`+) + BIOS power profiles; silicon replacement if already degraded | Physical hardware reliability; silent data corruption (SDC) and transient faults violate deterministic ISA execution |
| **AMD Zen EntrySign** (`CVE-2024-56161`, `AMD-SB-3019`) | AMD Zen 1 through Zen 5 (Families `0x17`, `0x19`, selected `0x1a`) | Insecure hash / signature verification in ROM microcode loader | BIOS/AGESA update + SEV-SNP firmware update + Linux SHA-256 allowlist (`verify_sha256_digest`) | Hardware Root of Trust for microcode integrity; Ring-0 host can rewrite `RDRAND` or break SEV-SNP guest isolation |

---

### 2. Deterministic Arithmetic & Microarchitectural Pipeline Errata

#### 2.1 Pentium FDIV: SRT Quotient-Selection PLA Omissions
**Basis:** normative + documentation + execution

Intel's 1994 P5 Pentium implemented IEEE 754 floating-point division (`FDIV`) using a **radix-4 SRT (Sweeney–Robertson–Tocher) division algorithm**, retiring 2 quotient bits per cycle by selecting a redundant quotient digit $q_k \in \{-2, -1, 0, +1, +2\}$ from a hardware Programmable Logic Array (PLA) indexed by the truncated scaled partial remainder $\hat{P}_k$ and the top 4 fractional bits of the normalized divisor $D \in [1, 2)$. As analyzed by Edelman (*SIAM Review* 1997, DOI `10.1137/S0036144595293959`) following Thomas Nicely's October 1994 discovery via twin-prime reciprocals ($1/824633702441$ and $1/824633702443$), a script error omitted **five cells** along the upper $q = +2$ boundary of the PLA table—causing those cells to read out `0` instead of `+2` for divisors whose normalized binary mantissa begins with `1.0001`, `1.0100`, `1.0111`, `1.1010`, or `1.1101` (top 4 fractional bits $d_{\text{idx}} \in \{1, 4, 7, 10, 13\}$) immediately followed by six consecutive `1` bits (`111111`).

**Verification probe (`Basis: execution`, Python 3.13.15):** Inspecting the normalized binary mantissas of both Tim Coe's canonical worst-case divisor (`3145727`) and Nicely's twin-prime divisors (`824633702441`, `824633702443`) confirms all three share the exact high-risk bit prefix `1.0111_111111...` ($d_{\text{idx}} = 7 = \text{0b0111}$ followed by six `1` bits):

```text
Coe worst-case:       4195835/3145727   = 1.333820449136241093 | norm_den = 1.011111111111 (top4=0111=7, next6=111111)
Nicely twin-prime #1: 1/824633702441    = 0.000000000001212660 | norm_den = 1.011111111111 (top4=0111=7, next6=111111)
Nicely twin-prime #2: 1/824633702443    = 0.000000000001212660 | norm_den = 1.011111111111 (top4=0111=7, next6=111111)
```

On affected P5 silicon, `4195835.0 / 3145727.0` returned `1.333739068902037589` instead of the exact rational `1.333820449136241002...` (IEEE 754 `binary64` `1.333820449136241093`), producing a residual `4195835 - (4195835 / 3145727) * 3145727 = 256.0` instead of `0` (a relative error of $\approx 6.1 \times 10^{-5}$). Because P5 had no field-patchable microcode loader for the FPU PLA, Intel executed a full hardware recall ($475M write-off), catalyzing formal RTL arithmetic verification (e.g., symbolic trajectory evaluation and theorem proving in HOL/ACL2) across subsequent microarchitectures.

#### 2.2 Intel Skylake/Kaby Lake Short-Loop High-Byte Register Corruption (`SKL150`/`SKW144`/`SKX150`/`SKZ7`/`KBL095`)
**Basis:** documentation

In June 2017 (highlighted by Debian maintainer Henrique de Moraes Holschuh's advisory and reproduced by OCaml compiler/runtime workloads), Intel confirmed a severe microarchitectural data-corruption erratum across 6th-generation Skylake (`SKL150`, `SKW144`, `SKX150`, `SKZ7`) and 7th-generation Kaby Lake (`KBL095`, `KBW095`) processors, titled *"Short Loops Which Use AH/BH/CH/DH Registers May Cause Unpredictable System Behavior"*:

- **Trigger conditions:** (1) Hyper-Threading (SMT) enabled with both sibling logical processors active on the physical core; (2) a short loop of fewer than 64 instructions managed by the hardware **Loop Stream Detector (LSD)**; and (3) instructions mixing partial high-byte registers (`AH`, `BH`, `CH`, `DH`) with their wider parent registers (`RAX`/`EAX`/`AX`, etc.).
- **Failure mode:** Silent register corruption, crashes, or system hangs on 100% architecturally legal x86-64 machine code emitted by standard optimizing compilers (such as GCC `-O2` compiling OCaml's GC/runtime).
- **Mitigation:** Intel's field microcode update **completely disabled the Loop Stream Detector (LSD)** on affected Skylake/Kaby Lake steppings, forcing tight loops to fall back to the Decoded ICache (DSB) and legacy decoders.

**Erratum-identifier disambiguation (`Basis: documentation`):** Note that `AH36` is *not* an Intel erratum identifier for the Skylake short-loop LSD defect. In older Intel Core 2 / Xeon specification updates, `AH36` denotes an unrelated `MONITOR`/`MWAIT` erratum (*"Split Locked Stores May Not Trigger the Monitoring Hardware"*, parallel to `AZ29`/`AO36`, disposition *"No Fix"*), and in LGA socket datasheets `AH36` denotes a physical package land coordinate. The Skylake/Kaby Lake short-loop high-byte register erratum involves the `AH`/`BH`/`CH`/`DH` architectural registers and is officially cataloged under `SKL150`, `SKW144`, `SKX150`, `SKZ7`, `KBL095`, and `KBW095` (and note further that in Intel's Core X-Series specification update, `SKZ7` is reused for an IIO PCIe ECRC credit-return erratum).

#### 2.3 Intel TSX Functional Errata and Asynchronous Abort (`HSW136`, `BDE42`, `SKL105`, `CVE-2019-11135`)
**Basis:** documentation + source

Intel Transactional Synchronization Extensions (TSX: Hardware Lock Elision `HLE` and Restricted Transactional Memory `RTM`) suffered both functional memory-ordering/correctness errata and speculative side-channel defects:

- **Functional errata (`HSW136`, `BDE42`, `SKL105`):** Titled *"Software Using Intel TSX May Result in Unpredictable System Behavior"* across Haswell, Broadwell, and Skylake steppings; early Haswell/Broadwell microcode updates forcibly disabled TSX so every `XBEGIN` immediately aborted.
- **TSX Asynchronous Abort (`TAA`, `CVE-2019-11135`):** Disclosed in November 2019, asynchronously aborted TSX transactions could transiently forward stale microarchitectural fill/load/store buffer contents (an MDS-class leakage channel even on `MDS_NO=1` Cascade Lake steppings).
- **Runtime MSR and CPUID mutation in Linux (`torvalds/linux` `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, `arch/x86/kernel/cpu/tsx.c`):**
  - On CPUs enumerating both `X86_FEATURE_RTM_ALWAYS_ABORT` and `X86_FEATURE_TSX_FORCE_ABORT`, Linux writes `MSR_TFA_TSX_CPUID_CLEAR` to `MSR_TSX_FORCE_ABORT` (`0x10F`) (`tsx.c` L127–131).
  - On CPUs enumerating `ARCH_CAP_TSX_CTRL_MSR` (added via microcode only on `MDS_NO=1` steppings, `tsx.c` L207–218), Linux writes `TSX_CTRL_RTM_DISABLE | TSX_CTRL_CPUID_CLEAR` to `MSR_IA32_TSX_CTRL` (`0x122`) (`tsx.c` L34–52).
  - Following Intel's February 2022 microcode update disabling TSX by default, Linux clears `RTM_ALLOW` in `MSR_IA32_MCU_OPT_CTRL` (`0x123`) (`tsx_dev_mode_disable`, `tsx.c` L140–167), noting that `MD_CLEAR` (`VERW`) mitigations for TAA may not be effective when TSX is re-enabled via development mode.
  - **Late-loading hazard (`tsx.c` L106–118):** Linux's own source comments explicitly document that **late microcode loading can set `X86_FEATURE_RTM_ALWAYS_ABORT` mid-uptime**; if a subsequent CPU hotplug re-detects CPUID and clears `RTM`/`HLE` after userspace already cached those feature bits at startup, live processes can fail unpredictably—so the kernel deliberately avoids retroactively clearing global CPUID feature flags after boot.

#### 2.4 Intel Raptor Lake $V_{\min}$ Shift Instability (2024–2025)
**Basis:** documentation + source

Unlike deterministic logic bugs, Intel's 13th/14th Generation Core desktop ("Raptor Lake" / "Raptor Lake Refresh") **$V_{\min}$ shift instability** illustrates **physical circuit aging** breaking ISA determinism over time:

- **Physical root cause:** Intel isolated the defect to a clock-tree circuit inside the IA core susceptible to accelerated reliability aging under elevated operating voltage and temperature, causing a permanent clock duty-cycle shift that raises the core's minimum stable operating voltage ($V_{\min}$). Once $V_{\min}$ exceeds the voltage/frequency curve, the core suffers silent data corruption (SDC), spurious decompression/shader-compilation faults, and `STATUS_ACCESS_VIOLATION` crashes.
- **Cascading firmware/microcode causes and exact Intel microcode progression:** Verified directly in `intel/Intel-Linux-Processor-Microcode-Data-Files` (`d71fe4e2f0f70a49ebbac7f2c7e915f181361974`, `releasenote.md`) for `RPL-E/HX/S` stepping `B0` (CPUID `06-b7-01/32` and `06-b7-01/36`):
  - **BIOS `0x125`** (June 2024, BIOS-distributed): fixed the Enhanced Thermal Velocity Boost (eTVB) microcode bug allowing peak boost states at elevated temperatures.
  - **`0x00000123` → `0x00000129`** (`releasenote.md` L598, Aug 2024): capped aggressive SVID voltage requests (1.55 V limit).
  - **`0x00000129` → `0x0000012b`** (`releasenote.md` L567, Sept 2024): mitigated elevated core voltage requests during idle and light-activity states.
  - **`0x0000012b` → `0x0000012c` → `0x0000012f`** (`releasenote.md` L481, L420, May 2025): addressed lingering extended low-load uptime $V_{\min}$ drift edge cases (followed in later releases by `0x132`, `0x133`, `0x137`, L280/L229/L119).
- **Implication for formal assurance:** Microcode updates only *prevent* future clock-tree aging; they cannot reverse existing silicon degradation. No software or formal proof can recover deterministic execution on physically aged silicon without hardware replacement or fault-tolerant redundant execution.

---

### 3. Assembler-Level Binary Mutation: Intel JCC Erratum (`SKX102` / `SKL167` / `KBL129`)

**Basis:** documentation + source + execution

#### 3.1 Microarchitectural Mechanism and Microcode Performance Penalty
Under Intel's Jump Conditional Code (JCC) Erratum (`SKX102` on Skylake-SP Xeon, `SKL167` on Skylake Client, `KBL129` on Kaby Lake; Intel White Paper `341810-001`, November 2019), a branch instruction—conditional jump (`Jcc`), macro-fused `(cmp/test/add/sub/and/inc/dec + Jcc)` pair, unconditional `JMP`, `CALL`, or `RET`—whose encoding **crosses or ends on a 32-byte boundary** (`(addr + len) % 32 == 0` or `addr / 32 != (addr + len - 1) / 32`) could cause unpredictable behavior when served from the Decoded ICache (Decoded Stream Buffer, DSB). Intel's microcode update prevented the defect by forbidding any 32-byte block containing such a boundary-straddling/ending jump from being cached in the DSB, forcing fallback to the legacy MITE decode pipeline (0–4% average performance regression, worse in branch-dense tight loops).

To recover DSB hits, Intel and toolchain authors added **assembler-level automatic branch alignment** to both GNU `as` and LLVM MC (`-mbranches-within-32B-boundaries` / `-x86-branches-within-32B-boundaries`). Critically, this pass runs **after all compiler optimization, register allocation, instruction selection, and scheduling**—inside the object-file assembler/MC streamer.

#### 3.2 Exact Source Mechanics in LLVM MC and GNU `as`
Direct inspection of `llvm/llvm-project` (`1780833aa0f119a425d7f993aaac29d03cb04da6`, `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp`) reveals four concrete binary-mutating mechanisms:

1. **Default branch classes and section alignment escalation (`X86AsmBackend.cpp` L104–126, L416–425, L558–599):** Enabling `-x86-branches-within-32B-boundaries` sets `AlignBoundary = assumeAligned(32)` and enables `AlignBranchFused | AlignBranchJcc | AlignBranchJmp`. Whenever `alignBranchesBegin` sees a matching branch or `isFirstMacroFusibleInst` (excluding RIP-relative operands, L247–255), it inserts an `MCBoundaryAlignFragment`, ties the branch into it in `alignBranchesEnd`, and **forces the enclosing ELF text section's minimum alignment up to 32 bytes** (`CF->getParent()->ensureMinAlignment(AlignBoundary)`, L598).
2. **Redundant segment-override prefix synthesis (`determinePaddingPrefix`, `X86AsmBackend.cpp` L266–316):** To avoid executing extra `NOP` micro-ops, LLVM MC pads *preceding* instructions in the same basic block with redundant legacy prefixes (up to `TargetPrefixMax` bytes, default 5). In 64-bit mode (`X86::Is64Bit`), if the instruction carries no explicit segment override, LLVM prepends **`CS` (`0x2e`, `X86::CS_Encoding`)** (L306–307); in 32-bit mode it emits `SS` (`0x36`) for `ESP`/`EBP`-based memory operands and `DS` (`0x3e`) otherwise (L309–315).
3. **Instruction-encoding widening (`padInstructionViaRelaxation` & `padInstsBackward`, `X86AsmBackend.cpp` L867–920, L1040–1105):** During `finishLayout()`, LLVM walks backward over `FT_Relaxable` fragments up to the nearest symbol label (`LabeledFragments`, L1041–1055) and first widens short encodings (e.g., `imm8` → `imm32`, `disp8` → `disp32`) via `padInstructionViaRelaxation` before appending redundant prefixes (`padInstructionViaPrefix`) and only finally emitting multi-byte `NOP`s inside `MCBoundaryAlignFragment` for any remaining gap (`RemainingSize`).
4. **Parallel GNU `as` implementation (`riscv-collab/riscv-binutils-gdb` `20756b0fbe065a84710aa38f2457563b57546440`, `gas/config/tc-i386.c` L742, L13131, L13172–13175, L13687–13689):** GNU `as` exposes `-mbranches-within-32B-boundaries`, `-malign-branch-boundary=NUM`, `-malign-branch=TYPE[+TYPE...]`, and `-malign-branch-prefix-size=NUM` (default `5`, capping redundant prefix insertion per instruction).

#### 3.3 Live Execution Probes: Observing Post-Codegen Binary Mutation
**Basis:** execution

**Probe 1A (GNU `as 2.47` on `x86_64-linux-gnu`):** Assembling an identical x86-64 function containing a macro-fused `cmpq $0, %rdx; jne .Ltarget` crossing byte offset `0x20` (`0x1d..0x22`) under three flag sets produces three distinct machine-code byte sequences from the exact same `.s` input:

| Mode | Bytes at `0x00` (`mov %rdi,%rax`) | Padding Before `cmp` | `cmp; jne` Offsets | `ret` Offset | Function Size |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Baseline (`as`) | `48 89 f8` (3 B) | None | `0x1d..0x22` (crosses `0x20`) | `0x27` | 40 B |
| `as -mbranches-within-32B-boundaries` | **`2e 2e 2e 48 89 f8`** (6 B: `cs cs cs mov`) | None (prefix-padded 8 insns earlier!) | `0x20..0x25` | **`0x2a`** | 43 B |
| `as -mbranches-within-32B-boundaries -malign-branch-prefix-size=0` | `48 89 f8` (3 B) | `1d: 0f 1f 00` (`nopl (%rax)`) | `0x20..0x25` | **`0x2a`** | 43 B |

Notably, GNU `as` mutated an unrelated register-to-register `mov %rdi,%rax` **eight instructions before the branch** by prepending three redundant `0x2e` (`CS`) prefixes, shifting every subsequent PC offset in the function by `+3` bytes.

**Probe 1B (`rustc 1.98.0-nightly` / `LLVM 22.1.6`, `-O` vs `-O -C llvm-args=-x86-branches-within-32B-boundaries`):** Compiling a small 14-line Rust loop (`rust_jcc_cross`) with two macro-fused branches crossing `0x20` (`1f: test %rsi,%rsi; 22: je 44`) and `0x40` (`3f: cmp %rdi,%rsi; 42: jne 30`):
- **Section alignment mutation (`readelf -SW`):** `.text.rust_jcc_cross` alignment increased from **`16`** to **`32`** and section size grew from `0x4c` to `0x4d`.
- **Instruction and displacement mutation (`objdump -d`):** LLVM MC inserted `1f: 90 nop` and `3f: 90 nop`, shrank the intervening loop-header alignment pad from 10 bytes (`26: 66 2e 0f 1f 84 00 00 00 00 00`) to 9 bytes (`27: 66 0f 1f 84 00 00 00 00 00`), and rewrote **every branch target and relative displacement** inside the function:
  - `je 44` (`22: 74 20`) shifted to `je 45` (`23: 74 20`)
  - `je 45` (`3a: 74 09`) had its `rel8` immediate mutated from `0x09` to `0x0a` (`3a: 74 0a` → `je 46`)
  - `jne 30` (`42: 75 ec`) had its backward `rel8` displacement mutated from `-20` (`0xec`) to `-21` (`0xeb` at `43: 75 eb`)

#### 3.4 Why Assembler Padding Breaks Verified Compilers and Constant-Time Proofs
**Basis:** derived (from source + execution)

1. **Pre-assembly byte-exactness invalidation:** Compilers whose correctness theorem terminates at textual assembly or MCInst streams (e.g., CompCert's `Asm` semantics, Jasmin's `asm_prog`) do not model `MCBoundaryAlignFragment` prefix injection or relaxation widening. A 1-byte shift can cascade across an entire basic block and push a 2-byte `rel8` jump past the `[-128, +127]` boundary into a 5/6-byte `rel32` encoding.
2. **Non-canonical instruction encodings:** Binary lifters, verified decoders (e.g., Sail/K/Coq x86 decoders), or SFI/NaCl-style sandboxes that reject redundant segment prefixes (`0x2e 0x2e 0x2e`) or bound instruction lengths can fail to decode or validate JCC-padded binaries.
3. **Microarchitectural & I-cache constant-time perturbation:** Even when architectural semantics are preserved, inserting prefixes and NOPs shifts cache-line boundaries (`64B`), DSB way allocation, and branch target buffer (BTB) indices—altering timing/I-cache observability for binaries whose constant-time properties depended on hand-tuned basic-block alignment.

---

### 4. Link-Time Binary Mutation and Veneer Synthesis: ARM Cortex-A53 Errata `843419` and `835769`

**Basis:** normative + source + derived + execution

On ARMv8-A Cortex-A53 (`r0p0`, `r0p1`, `r0p2`, `r0p4`; `ARM-EPM-048406`), silicon errata cannot be fixed by microcode (ARMv8-A cores generally lack x86-style patchable microcode ROMs for decode/LSU pipelines) and in the case of `843419` **cannot even be detected at compile time** because the triggering condition depends on the final virtual address modulo 4 KiB (`VA & 0xfff`), which is only determined during static linking.

#### 4.1 Cortex-A53 Erratum 843419: Exact 4-Instruction Hazard Pattern
Direct inspection of `llvm/llvm-project` (`1780833aa0f119a425d7f993aaac29d03cb04da6`, `lld/ELF/AArch64ErrataFix.cpp` L48–369) establishes the exact bitmask-checked triggering sequence ("Sequence 1" of `ARM-EPM-048406`):

1. **Instruction 1 (`VA & 0xfff ∈ {0xff8, 0xffc}`):** `ADRP Rd, <page>` (`(instr1 & 0x9f000000) == 0x90000000`, writing `Rn = getRt(instr1)`).
2. **Instruction 2 (`VA + 4`):** A load/store instruction (`(instr2 & 0x0a000000) == 0x08000000`) belonging to single-register scalar/vector load/store, `STP`/`STNP`, load/store exclusive, literal load, or SIMD `ST1`—**which does NOT write to `Rn`** (neither as destination register `Rt` on a load nor via pre/post-indexed base writeback on `Rn`, `doesLoadStoreWriteToReg`, L281–284).
3. **Instruction 3 (`VA + 8`, optional):** Either omitted (3-instruction trigger) or any non-branch instruction (`!isBranch(instr3)`, L229–234, L359) that does not write to `Rn`.
4. **Instruction 3 or 4 (`VA + 8` or `VA + 12`):** An unsigned-immediate load/store instruction (`(instr4 & 0x3b000000) == 0x39000000`) using `Rn` as its base address register (`getRn(instr4) == rn`, L326).

*Critical scope limitation documented in source (`AArch64ErrataFix.cpp` L308–310):* LLD, GNU `ld.bfd`, and `gold` deliberately **do not scan for Sequence 2** of `ARM-EPM-048406`, judging it extremely unlikely in compiler-generated code—leaving hand-written or unconventional verified assembly potentially uncovered if it triggers Sequence 2.

#### 4.2 Linker Binary Rewriting Strategies: LLD vs. GNU `ld.bfd`
Comparing `lld/ELF/AArch64ErrataFix.cpp` (LLVM `1780833aa0f119a425d7f993aaac29d03cb04da6`) against `bfd/elfnn-aarch64.c` (GNU Binutils `20756b0fbe065a84710aa38f2457563b57546440`):

| Mechanism | LLVM `lld` (`AArch64ErrataFix.cpp`) | GNU `ld.bfd` (`bfd/elfnn-aarch64.c`) |
| :--- | :--- | :--- |
| **In-place `ADRP` → `ADR` rewrite** | Not used; always synthesizes veneer (`Patch843419Section`, L371–420) | Supported (`ERRAT_ADR`, default mode, L3393, L4812, L5310): if target lies within `±1 MiB`, rewrites `ADRP` in place to `ADR` without altering CFG or adding a stub |
| **Veneer / stub patching** | Overwrites faulting `LDR`/`STR` at `patcheeOffset` with `R_AARCH64_JUMP26` (`B __CortexA53843419_<va>`); migrates any `R_AARCH64_LD64_{ABS,GOT}_LO12_NC` relocation into 8-byte `.text.patch` section `[orig_ldst; B (va+4)]` (L394–420, L533–577) | Fallback (`ERRAT_ADRP`, L2415–2419, L5319): builds 8-byte `aarch64_erratum_843419_stub` (`[orig_ldst; 0x14000000 B <ret>]`) in `.stub` section and overwrites faulting `LDR`/`STR` with branch to stub |
| **TLS relaxation interaction** | Explicitly skips `R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21` / `R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC` when `expr == R_TPREL` because IE→LE turns `ADRP` into `MOVZ` (L542–560) | Coordinated with TLS relaxation during stub sizing and relocation |
| **Data-vs-code disambiguation** | Relies strictly on ELF AArch64 mapping symbols `$x` (code) and `$d` (data) (`AArch64Err843419Patcher::init`, L422–476) | Relies on ELF mapping symbols `$x`/`$d` during `_bfd_aarch64_erratum_843419_scan` (L4185) |
| **Multi-pass address cascade** | `createFixes()` returns `addressesChanged = true` whenever patches are inserted (`insertPatches`, L483–527, L637–656), forcing re-layout and re-scanning until fixpoint | Iterates stub layout/sizing until section addresses stabilize |

**Bitmask & cascade verification (`Basis: execution`, Python 3.13.15):** Encoding the 3-instruction sequence `ADRP x0, #0x1000` (`0x90000020`) at `0x400ff8`, `STR x1, [x2]` (`0xf9000041`) at `0x400ffc`, and `LDR x0, [x0, #8]` (`0xf9400400`) at `0x401000` matches all LLD bitmasks (`isADRP=True`, `isLSClass=True`, `isLSUnsigned=True`, `Rn==ADRP.Rd`). LLD replaces `0x401000` in place with `0x14000400` (`B 0x402000`) and emits the 8-byte `.text.patch` veneer at `0x402000`: `[0xf9400400, 0x17fffc00]` (`LDR x0, [x0, #8]; B 0x401004`). If a downstream `InputSection` originally placed a safe `ADRP` at `0x402ff0` (`offset = 0xff0`), inserting this single 8-byte veneer upstream shifts that `ADRP` to `0x402ff8` (`offset = 0xff8`), **creating a brand-new 843419 hazard on pass 2**.

**Silent data-corruption hazard with stripped/missing mapping symbols (`Basis: source + derived`):** Because `AArch64Err843419Patcher::init` (`AArch64ErrataFix.cpp` L423–474) distinguishes inline literal pools from instructions solely via `$x`/`$d` mapping symbols, a custom assembler or verified code generator that places constant data inside an `SHF_EXECINSTR` section without emitting `$d` mapping symbols risks having the linker overwrite 4 bytes of read-only data with an `R_AARCH64_JUMP26` opcode if those data words happen to satisfy the bitmask at `0xFF8`/`0xFFC`.

#### 4.3 Cortex-A53 Erratum 835769: Dual Compiler and Linker Mutation
Direct inspection of `llvm/lib/Target/AArch64/AArch64A53Fix835769.cpp` (L8–73, L191–257) and `bfd/elfnn-aarch64.c` (L2409–2413, L3881–3973) documents the exact 2-instruction hazard and dual mitigation:

- **Trigger pattern:** Any memory access instruction (`mayLoadOrStore()` or `PRFM*` prefetch, L39–51) immediately followed (including across basic-block fallthrough edges, `getLastNonPseudo`, L150–189) by a **64-bit** non-SIMD integer multiply-accumulate instruction (`MADDXrrr`, `MSUBXrrr`, `SMADDLrrr`, `SMSUBLrrr`, `UMADDLrrr`, `UMSUBLrrr`) whose accumulator register `Ra != XZR` (`MI->getOperand(3).getReg() != AArch64::XZR`, L55–73; plain `MUL` encodes `Ra = XZR = 31` and does not trigger).
- **Compiler mitigation (`-mfix-cortex-a53-835769`):** Late post-RA `MachineFunctionPass` inserts an `AArch64::NOP` immediately before the MAC instruction (or at the end of the fallthrough predecessor block, L191–206).
- **Linker mitigation (`--fix-cortex-a53-835769` in GNU `ld.bfd`, `bfd/elfnn-aarch64.c` L2409–2413, L3895–3970):** For pre-compiled objects/libraries built without the compiler flag, `ld.bfd` scans executable sections, replaces the MAC instruction in place with `B __erratum_835769_veneer_<N>`, and emits an 8-byte stub `[orig_mac_insn; B <return>]` (the branch itself separates the memory op from the MAC in the pipeline!).

#### 4.4 Impact on Verified Compilation and Binary Assurance
**Basis:** derived (from source)

Link-time Cortex-A53 errata patching violates virtually every assumption of pre-link compiler verification:
- **CFG mutation:** Replacing a straight-line `LDR`/`STR` or `MADD` with `B <veneer>` + out-of-line stub + `B <ret>` alters basic-block boundaries, adds two unconditional branches per hazard site, breaks PC-relative jump-table / return-address assumptions if not relocation-tracked, and invalidates static worst-case execution time (WCET) bounds.
- **Timing and I-cache side channels:** Because `843419` triggers purely as a function of `VA & 0xfff`, two identical constant-time branches in a cryptographic routine can diverge asymmetrically if one lands on `0xFF8` and gets redirected through a remote `.text.patch` veneer (incurring an extra taken branch and I-cache miss), turning a nominally balanced branch into a link-layout-dependent timing leak.
- **Self-verifying / checksummed code:** Code-integrity hashes or proof-carrying machine-code certificates computed over `.o` files fail verification on the linked binary unless the patcher is either disabled (unsafe on `r0p0`–`r0p4` silicon), formally verified, or verified *post-link*.

---

### 5. Field Microcode Hot-Patching and Hardware Root-of-Trust Risks

**Basis:** source + documentation

#### 5.1 Live Microcode Loading Architecture in Linux
Inspecting `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) reveals how x86-64 operating systems mutate CPU execution semantics dynamically at runtime:

- **Intel loader (`arch/x86/kernel/cpu/microcode/intel.c` L689–698):** Writes the physical/virtual address of the microcode update payload to `MSR_IA32_UCODE_WRITE` (`0x79`) via `native_wrmsrq`, then executes `CPUID` and reads `MSR_IA32_UCODE_REV` (`0x8B`) via `intel_get_microcode_revision()` to confirm `rev == mc->hdr.rev`.
- **AMD loader (`arch/x86/kernel/cpu/microcode/amd.c` L335, L701–715):** Writes the patch image address to `MSR_AMD64_PATCH_LOADER` (`0xC0010020`), reads revision from `MSR_AMD64_PATCH_LEVEL` (`0x8B`), and on Family `0x17` executes `invlpg` across the patch page(s) post-load.
- **Stop-machine late reloading (`arch/x86/kernel/cpu/microcode/core.c` L623–636, L762–775):** Writing `1` to `/sys/devices/system/cpu/microcode/reload` triggers `reload_store()` → `load_late_locked()` → `stop_machine_cpuslocked(load_cpus_stopped, NULL, cpu_online_mask)`, halting all online CPUs in an NMI-guarded rendezvous, updating every primary thread (SMT siblings observe `UCODE_OK`), and resuming user/kernel execution on modified microarchitectural semantics.

#### 5.2 Dynamic Behavioral Shifts Invisible to Binary Verification
Because microcode resides in volatile SRAM inside the CPU core (reloaded on every cold reset by BIOS/UEFI or OS early initrd), **the exact same verified binary on the exact same silicon stepping can exhibit radically different security and timing semantics depending on loaded microcode revision**:
- **Instruction semantics changes:** `VERW` was repurposed via microcode to flush microarchitectural buffers (`MD_CLEAR` for MDS/TAA/MMIO stale data); `XBEGIN` transitions from executing transactions to unconditionally aborting (`RTM_ALWAYS_ABORT`); `MSR_IA32_SPEC_CTRL` bits (`IBRS`, `STIBP`, `SSBD`) appear or change behavior.
- **Microarchitectural pipeline changes:** Disabling the Loop Stream Detector (`SKL150`/`KBL095`) or banning 32-byte-boundary branches from the DSB (`SKX102`) changes instruction throughput, front-end stalls, and port contention side channels.
- **Attestation requirement:** Any hardware-grounded formal assurance claim must bind not only `target_triple` and binary SHA-256, but also the `(CPUID signature, stepping, microcode revision)` tuple—which confidential-computing attestation quotes (Intel TDX `TDREPORT`, AMD SEV-SNP `ATTESTATION_REPORT`) explicitly include.

#### 5.3 Microcode Loader Vulnerabilities: AMD EntrySign (`CVE-2024-56161`)
**Basis:** source + documentation

Microcode patch loaders are themselves complex ROM/firmware routines inside the hardware TCB. In February 2025 (reported September 2024), Google Security Research disclosed **EntrySign** (`CVE-2024-56161`, `CVE-2024-36347`, advisory `AMD-SB-3019`), affecting AMD Zen 1 through Zen 5 processors (`torvalds/linux` `arch/x86/kernel/cpu/microcode/amd.c` L245–258 explicitly enumerates `fam == 0x17`, `fam == 0x19`, and `fam == 0x1a` models `<= 0x2f`, `0x40..0x4f`, `0x60..0x7f`):

- **Flaw:** Improper signature verification and use of an insecure hash function (CMAC/non-cryptographic hash weakness in ROM validation) permitted a privileged host (Ring 0) to forge signatures and load **arbitrary custom microcode patches**.
- **Demonstrated capability (`google/security-research` `dd9c753bdb2ae51e8214e50be313283daa400713`, `pocs/cpus/entrysign/README.md` L1–20):** Tested on `AMD EPYC 7B13` (Milan) and `AMD Ryzen 9 7940HS` (Phoenix), the published PoC (`milan_rdrand_carryclear_encrypted.bin`) hot-patches the `RDRAND` instruction so that it deterministically returns the constant `4` (with `CF=0` in the benign PoC; an adversary could set `CF=1` to inject chosen randomness into guest cryptographic key generation, breaking AMD SEV-SNP confidential VM isolation despite encrypted guest memory).
- **Layered remediation:** Requires BIOS/AGESA updates to patch the ROM loader, SEV-SNP firmware updates for attestation enforcement, and OS kernel defense-in-depth (`verify_sha256_digest` in `amd.c` L263–276, L701–702 checking incoming patches against a kernel SHA-256 digest table when `cpu_has_entrysign()` and `need_sha_check(cur_rev)` hold).

---

### 6. Architectural Guidance for Verified Compilation and Binary Assurance

**Basis:** derived

| Verification Goal | Naive Assumption (Unsound on Real Hardware) | Hardened Engineering Requirement |
| :--- | :--- | :--- |
| **Byte-exact functional / SFI / CFG proof** | Proof terminates at compiler `Asm` AST or relocatable `.o` | Verify **post-link ELF bytes** (or disable post-codegen padding/veneers and fail closed on errata-affected steppings); verify ELF `$x`/`$d` mapping symbols on AArch64 |
| **Constant-time / I-cache alignment proof** | Assembler and linker preserve instruction lengths and basic-block offsets | Pin exact assembler/linker flags (`-mbranches-within-32B-boundaries`, `-malign-branch-prefix-size`, `--fix-cortex-a53-843419`), inspect linked disassembly (`objdump -d`), and re-run binary CT analysis post-link |
| **Hardware ISA soundness** | Silicon implements published ISA manual unconditionally | Record minimum safe `(CPUID/MIDR, stepping, microcode/AGESA rev)` preconditions; verify via runtime attestation or kernel boot checks; treat physical aging ($V_{\min}$ shift) as a fault-model boundary requiring hardware replacement or redundant execution |
| **Confidential computing (SEV-SNP / TDX)** | Host Ring 0 cannot alter guest instruction semantics | Require platform attestation enforcing post-EntrySign AGESA/SEV firmware and verified microcode revision levels in the attestation policy |

## Boundaries

- **Known not to apply:**
  - Intel JCC Erratum (`SKX102`/`SKL167`/`KBL129`) does not apply to AMD x86-64 processors or post-Comet-Lake Intel microarchitectures (Ice Lake / Sunny Cove and newer) whose DSB fixes the 32-byte boundary issue in silicon; however, compiling with `-mbranches-within-32B-boundaries` still mutates the binary unconditionally regardless of the host CPU that executes it.
  - ARM Cortex-A53 Errata `843419` and `835769` are specific to Cortex-A53 `r0p0`–`r0p4` silicon (not Cortex-A55/A72/A76/Neoverse or later A53 revisions), though toolchains frequently enable `--fix-cortex-a53-843419` by default across generic `aarch64-linux-gnu` / Android builds, mutating binaries targeted at newer cores as well.
  - Intel erratum code `AH36` does **not** apply to the Skylake short-loop LSD high-byte register corruption defect; `AH36` refers to a distinct `MONITOR`/`MWAIT` split-locked-store erratum in earlier Intel Core 2 / Xeon specification updates.
  - Microcode updates (`0x125`/`0x129`/`0x12B`/`0x12F`+) do **not** repair Intel Raptor Lake processors whose IA core clock-tree circuits have already suffered irreversible physical $V_{\min}$ degradation.
- **Not examined:**
  - Direct execution of an AArch64 cross-linker (`aarch64-linux-gnu-ld` / `lld` on AArch64 ELF objects) was not performed because only an `x86_64-linux-gnu` toolchain was installed on the observation host; AArch64 `843419`/`835769` behavior was verified by direct upstream source inspection of `lld` and GNU `bfd` plus exact bitmask/address-cascade simulation in Python.
  - MSVC's `/QIntel-jcc-erratum`, Apple `ld64` errata passes, and ARMv7 / Thumb-2 errata veneers (e.g., Cortex-A8 erratum `657417`) were not examined.
  - Proprietary microcode instruction set internals (Intel CRBUS/uROM formats, AMD ucode patch RAM encoding) beyond public Linux loader interfaces and the EntrySign README were not examined.
- **Unknown:**
  - Whether any real-world compiler or verified code generator currently emits **Sequence 2** of ARM Cortex-A53 Erratum 843419 (`ARM-EPM-048406`), which LLD, `ld.bfd`, and `gold` intentionally skip scanning for (`AArch64ErrataFix.cpp` L308–310).
  - Exact long-term field failure rates of Intel Raptor Lake steppings post-`0x12F` microcode across multi-year server uptimes.
- **Unsupported:**
  - In-field microcode patching for deterministic combinational/PLA logic errors lacking microcode traps (such as P5 Pentium FDIV or ARM Cortex-A53 LSU `843419`) is architecturally unsupported by the affected silicon, forcing hardware recalls or binary-mutating toolchain workarounds.

## Evidence

### Primary Upstream Source Code (Pinned Commits, Observed 2026-11-19)
- **`llvm/llvm-project` @ `1780833aa0f119a425d7f993aaac29d03cb04da6`:**
  - `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp`: L104–127 (`branches_within_32B_boundaries` defaults), L247–255 (`isFirstMacroFusibleInst`), L266–316 (`determinePaddingPrefix` emitting `X86::CS_Encoding` in 64-bit mode), L416–425 (`needAlign`), L558–599 (`alignBranchesBegin`/`alignBranchesEnd` inserting `MCBoundaryAlignFragment` and calling `ensureMinAlignment(AlignBoundary)`), L867–920 (`padInstructionViaRelaxation`, `padInstsBackward`), L1040–1105 (`finishLayout` backward relaxation across `FT_Relaxable` fragments bounded by `LabeledFragments`).
  - `lld/ELF/AArch64ErrataFix.cpp`: L53–284 (ARMv8-A instruction bitmask decoders and `doesLoadStoreWriteToReg`), L286–369 (`is843419ErratumSequence` and `scanCortexA53Errata843419` scanning page offsets `0xff8`/`0xffc`; L308–310 documenting deliberate omission of Sequence 2), L371–420 (`Patch843419Section` 8-byte `.text.patch` synthetic veneer), L422–476 (`AArch64Err843419Patcher::init` `$x`/`$d` mapping symbol extraction), L483–577 (`insertPatches` and `implementPatch` overwriting faulting load/store with `R_AARCH64_JUMP26`), L637–656 (`createFixes` returning `addressesChanged` for multi-pass fixpoint).
  - `llvm/lib/Target/AArch64/AArch64A53Fix835769.cpp`: L39–73 (`isFirstInstructionInSequence` memory/prefetch ops, `isSecondInstructionInSequence` 64-bit `MADD`/`MSUB`/`SMADDL`/`SMSUBL`/`UMADDL`/`UMSUBL` with `Ra != XZR`), L150–257 (fallthrough predecessor scan and `AArch64::NOP` insertion).
- **`riscv-collab/riscv-binutils-gdb` @ `20756b0fbe065a84710aa38f2457563b57546440` (`bfd/version.m4`: BFD `2.38`):**
  - `gas/config/tc-i386.c`: L742 (`align_branch_prefix_size = 5`), L13131, L13172–13175, L13687–13689 (`OPTION_MBRANCHES_WITH_32B_BOUNDARIES`, `-malign-branch-boundary`, `-malign-branch-prefix-size`, `-malign-branch`).
  - `bfd/elfnn-aarch64.c`: L2409–2419 (`aarch64_erratum_835769_stub`, `aarch64_erratum_843419_stub`), L3388–3397 (`ERRAT_ADR` vs veneer sizing), L3881–3973 (`_bfd_aarch64_erratum_835769_scan` and veneer creation), L4185, L4812, L5260–5325 (`_bfd_aarch64_erratum_843419_scan`, `ERRAT_ADR` in-place rewrite vs `ERRAT_ADRP` stub branching).
- **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:**
  - `arch/x86/kernel/cpu/tsx.c`: L34–52 (`tsx_disable` via `MSR_IA32_TSX_CTRL`), L81–137 (`MSR_TSX_FORCE_ABORT` vs `MSR_IA32_TSX_CTRL` and late-loading CPUID mutation hazard), L140–167 (`tsx_dev_mode_disable` clearing `RTM_ALLOW` in `MSR_IA32_MCU_OPT_CTRL`), L189–254 (`tsx_init`).
  - `arch/x86/kernel/cpu/microcode/intel.c`: L689–698 (`native_wrmsrq(MSR_IA32_UCODE_WRITE, ...)` + `intel_get_microcode_revision()`).
  - `arch/x86/kernel/cpu/microcode/core.c`: L623–636 (`stop_machine_cpuslocked(load_cpus_stopped, ...)`), L762–775 (`reload_store` sysfs trigger).
  - `arch/x86/kernel/cpu/microcode/amd.c`: L245–276 (`cpu_has_entrysign` enumerating Families `0x17`, `0x19`, `0x1a` and `verify_sha256_digest`), L335 (`MSR_AMD64_PATCH_LEVEL`), L701–715 (`MSR_AMD64_PATCH_LOADER` + Family `0x17` `invlpg`).
- **`intel/Intel-Linux-Processor-Microcode-Data-Files` @ `d71fe4e2f0f70a49ebbac7f2c7e915f181361974`:**
  - `releasenote.md`: L119, L229, L280, L420, L481, L567, L598 (`RPL-E/HX/S` stepping `B0` CPUID `06-b7-01` progression `0x123 -> 0x129 -> 0x12b -> 0x12c -> 0x12f -> 0x132 -> 0x133 -> 0x137`).
- **`google/security-research` @ `dd9c753bdb2ae51e8214e50be313283daa400713`:**
  - `pocs/cpus/entrysign/README.md`: L1–20 (`CVE-2024-56161` Milan/Phoenix PoC patching `RDRAND` to return constant `4` with `CF=0`).

### Specifications and Peer-Reviewed Literature
- Alan Edelman, *"The Mathematics of the Pentium Division Bug"*, SIAM Review, Vol. 39, No. 1, pp. 54–67 (1997), DOI `10.1137/S0036144595293959`.
- Intel Corporation, *"Mitigations for Jump Conditional Code Erratum — White Paper"*, Document `341810-001` (November 2019).
- ARM Limited, *"Cortex-A53 MPCore Software Developers Errata Notice"*, Document `ARM-EPM-048406` (Errata `843419` and `835769`).
- AMD Security Bulletin `AMD-SB-3019` / `CVE-2024-56161` / `CVE-2024-36347` (February 2025).

### Local Execution Probes (Observed 2026-11-19 on `x86_64-unknown-linux-gnu`)
- **Environment:** Linux `7.1.6-1rodete1-amd64`, `GNU Binutils 2.47` (`as`, `objdump`, `readelf`), `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`LLVM 22.1.6`), `Python 3.13.15`.
- **Probe 1A (GNU `as` prefix vs NOP mutation):** Assembling `/tmp/jcc_probe.s` (containing 29 bytes of prelude followed by `cmpq $0, %rdx; jne .Ltarget` spanning `0x1d..0x22`) via `as`, `as -mbranches-within-32B-boundaries`, and `as -mbranches-within-32B-boundaries -malign-branch-prefix-size=0`, inspected with `objdump -d`, directly reproduced `0: 2e 2e 2e 48 89 f8 cs cs cs mov %rdi,%rax` (prefix mode) and `1d: 0f 1f 00 nopl (%rax)` (NOP mode), shifting `ret` from `0x27` to `0x2a`.
- **Probe 1B (`rustc`/`LLVM 22.1.6` MC mutation):** Compiling `rust_jcc_cross` with `rustc --edition=2021 --crate-type=lib -O --emit=obj` vs adding `-C llvm-args=-x86-branches-within-32B-boundaries` directly reproduced `.text.rust_jcc_cross` alignment escalation (`16` → `32`), size growth (`0x4c` → `0x4d`), insertion of `nop` at `0x1f` and `0x3f`, and branch displacement mutation (`74 09` → `74 0a`; `75 ec` → `75 eb`).
- **Probe 1C & 1D (Python 3.13.15):** Verified exact normalized binary divisor prefixes (`1.011111111111...`) for Coe/Nicely FDIV inputs and verified LLD's exact bitmasks (`isADRP`, `isLoadStoreClass`, `isLoadStoreRegisterUnsigned`), 8-byte veneer encoding (`0x14000400` / `[0xf9400400, 0x17fffc00]`), and `+8` byte downstream `ADRP` cascade (`0x402ff0` → `0x402ff8`).

## Revalidation

1. **Re-run GNU `as` JCC prefix-padding probe (~1 second):**
   ```bash
   cat > /tmp/jcc_probe.s <<'EOF'
   .text
   .p2align 5
   .globl jcc_boundary_test
   jcc_boundary_test:
       movq %rdi, %rax
       addq $1, %rax
       xorq %rcx, %rcx
       addq $2, %rax
       addq $3, %rax
       addq $4, %rax
       addq $5, %rax
       movq %rsi, %rdx
       cmpq $0, %rdx
       jne .Ltarget
       addq $9, %rax
   .Ltarget:
       ret
   EOF
   as -o /tmp/jcc_base.o /tmp/jcc_probe.s
   as -mbranches-within-32B-boundaries -o /tmp/jcc_pfx.o /tmp/jcc_probe.s
   diff -u <(objdump -d /tmp/jcc_base.o) <(objdump -d /tmp/jcc_pfx.o)
   ```
   Confirm `2e 2e 2e 48 89 f8` (`cs cs cs mov`) appears at offset `0x00` and branch targets shift by `+3` bytes.
2. **Re-run LLVM MC JCC probe via `rustc` (or `clang -mbranches-within-32B-boundaries`):** Compile `rust_jcc_cross` with and without `-C llvm-args=-x86-branches-within-32B-boundaries`, then compare `readelf -SW` section alignments (`16` vs `32`) and `objdump -d` relative branch displacements.
3. **Check upstream LLVM / Linux drift:** Diff `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp`, `lld/ELF/AArch64ErrataFix.cpp`, `llvm/lib/Target/AArch64/AArch64A53Fix835769.cpp`, and `arch/x86/kernel/cpu/{tsx.c,microcode/*.c}` against the pinned revisions in `REPORT.json` for new errata scanners (e.g., Sequence 2 support in LLD, new `ERRAT_*` modes in GNU BFD, or updated `cpu_has_entrysign` / `verify_sha256_digest` tables in Linux).
4. **Verify live host microcode and TSX state:** On any target Linux deployment host, inspect `/proc/cpuinfo` (`cpu family`, `model`, `stepping`, `microcode`, `flags`) and `/sys/devices/system/cpu/vulnerabilities/tsx_async_abort` to confirm whether runtime microcode has altered `RTM`/`HLE`, `MD_CLEAR`, or `Vmin` mitigation state relative to build-time assumptions.
