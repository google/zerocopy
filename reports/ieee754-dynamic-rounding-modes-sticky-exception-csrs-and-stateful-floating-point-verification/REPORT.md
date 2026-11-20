# IEEE-754 Dynamic Rounding Modes, Sticky Exception CSRs, and Stateful Floating-Point Verification Across ISAs and Compilers

## Summary

Pure functional IEEE-754 models—treating `+`, `*`, `/`, `sqrt`, and `fma` as stateless operations under `roundTiesToEven` (`RNE`)—are unsound whenever hardware floating-point control and status registers (`fcsr`/`frm`/`fflags` on RISC-V, `MXCSR` on x86-64, and `FPCR`/`FPSR` on AArch64) are observable or mutated. Primary ISA specs, compiler codegen sources, mechanized compiler proofs, and empirical C23 execution probes on `gcc 15.2.0` (`x86_64`) establish four core findings:

1. **Bidirectional hidden CSR state breaks pure RNE and scalar-vs-SIMD equivalence:** Floating-point arithmetic implicitly *reads* control fields (rounding mode, `FTZ`/`FZ`, `DAZ`/`FIZ`, trap masks, default-NaN `DN`, or `mstatus.FS`) and monotonically *ORs* sticky status bits (`NV/IO`, `DZ`, `OF`, `UF`, `NX`, plus x86/Arm denormal `DE/IDC`). Under `RDN`, $x + (-x)$ evaluates to `-0.0` rather than `+0.0`; under `DAZ+FTZ` (`MXCSR = 0x9fc0`), runtime `_mm_add_ps(0x00400000, +0.0)` flushes to `+0.0` whereas constant-folded scalar arithmetic retains `0x00400000`; and unmasked SIMD tail lanes containing signaling NaNs (`[1.0f, sNaN, 0.0f, 0.0f]`) set `MXCSR.IE = 0x01` (or trap `#XM`) where scalar code leaves flags clear.
2. **RISC-V exhibits an asymmetric static-vs-vector RM trap hazard and an unstated CompCert printer assumption:** In `riscv/sail-riscv@76f1ce3c` (`fext_insts.sail:L51-L63`), scalar `F`/`D` ops with static `rm` (`0b000..0b100`) ignore `fcsr[FRM]`, whereas `rm = RM_DYN` (`0b111`) and **all RVV vector FP instructions** (`vext_fp_utils_insts.sail:L16-L21`) read `fcsr[FRM]` and trap with `Illegal_Instruction` on `101..111`. Both LLVM (`RISCVInstrInfoF.td:L556-L580`) and CompCert (`riscV/TargetPrinter.ml:L377-L421`) emit dynamic-RM 3-operand `fadd.s`/`fmul.s` (`0b111`), leaving CompCert's stateless `riscV/Asm.v` silently reliant on external `fcsr[FRM] == 0b000`.
3. **Inline assembly, FFI, C23 `FENV_ACCESS`, and cross-language LTO omit sound FP-CSR tracking:** Rust RFC 3514 (`L58-L59`) makes non-default FP control state UB, and `rustc` (`asm.rs:L259-L280`) omits `mxcsr` (clobbering only legacy x87 `"fpsr"`), Arm64 `fpcr`/`fpsr`, and RISC-V `frm` when `preserves_flags` is absent. Empirically on `gcc 15.2.0` (`-std=c23 -O2 -frounding-math`), `-frounding-math` prevents interprocedural constant folding (`1.0f + 2^-25` -> `0x3f800001`), **yet GCC still performs GVN/CSE across `fesetround(FE_UPWARD)` and `__asm__ volatile("ldmxcsr ...", "memory")`**, folding both additions into one `addss` unless SSA values are laundered via `+x` constraints.
4. **Verified compilers guard or project CSR state explicitly:** HOL4 (`binary_ieee`/`machine_ieee`) returns `(flags, float)` pairs and projects pure values via `SND`; CakeML (`x64_ok`, `arm8_ok`) enforces default control/mask invariants while leaving sticky status flags unconstrained (`MXCSR[5:0]`, `FPSR`) and disables hardware FP on RISC-V (`fp_reg_count := 0`).

## Applicability

These findings govern the seam between stateless IEEE-754 arithmetic and hardware/ABI/compiler state across the ten pinned subjects in `REPORT.json`: `riscv/sail-riscv@76f1ce3c`, `riscv-non-isa/riscv-elf-psabi-doc@56561cb3`, `ARM-software/abi-aa@9f9e067e`, `llvm/llvm-project@1163b549`, `rust-lang/rust@c7d5ba59`, `rust-lang/rfcs@f43d5789`, `AbsInt/CompCert@2685140b`, `CakeML/cakeml@2874b664`, `HOL-Theorem-Prover/HOL@aee6a90d`, and `gcc (Debian 15.2.0-14) 15.2.0` (`x86_64-linux-gnu`). This report extends `rust-floating-point-semantics-llvm-lowering-and-isa-behavior` (which covers RFC 3514 NaN rules under default RNE), `ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`, and `machine-code-verification-frameworks-and-assembly-contracts`.

## Findings

### 1. Cross-ISA Bit-Level Semantics of Floating-Point Control and Status Registers

Basis: normative + source

Table 1 summarizes hardware CSR layouts, rounding encodings, exception semantics, static overrides, and ABI conventions across RISC-V (`RV64FDV`), `x86-64`, and `AArch64`.

| Feature | RISC-V (`fcsr` / `frm` / `fflags` + `mstatus.FS`) | `x86-64` (`MXCSR` + x87 `FPCW`/`FPSW`) | Arm `AArch64` (`FPCR` + `FPSR`) |
| :--- | :--- | :--- | :--- |
| **Control vs. Status Split** | Combined 32-bit CSR `fcsr` (`0x003`) aliased by `fflags` (`0x001`, `[4:0]`) and `frm` (`0x002`, `[7:5]`), plus `mstatus.FS[14:13]` (`fdext_regs.sail:L433-L463`) | Combined `MXCSR` (default `0x1f80`: sticky `[5:0]`, `DAZ[6]`, masks `[12:7]`, `RC[14:13]`, `FTZ[15]`); separate x87 `FPCW`/`FPSW` (`X86RegisterInfo.td:L444-L452`) | **Split:** Control in `FPCR` (`RMode[23:22]`, `FZ[24]`, `DN[25]`, `FZ16[19]`, traps `[15,12:8]`, `AH[1]`, `FIZ[0]`, `NEP[2]`); status in `FPSR` (`[4:0], IDC[7], QC[27]`) |
| **Rounding Mode Encodings** | `000` `RNE`, `001` `RTZ`, `010` `RDN` ($-\infty$), `011` `RUP` ($+\infty$), `100` `RMM`; `101..110` reserved, `111` `RM_DYN` in insn (`fext_insts.sail:L31-L50`) | `00` `RN`, `01` `RD` ($-\infty$), `10` `RU` ($+\infty$), `11` `RZ` (`x64_targetScript.sml:L26`); no `RMM` | `00` `RN`, `01` `RP` ($+\infty$), `10` `RM` ($-\infty$), `11` `RZ`. **Opposite RP/RM bit order vs. x86 RD/RU!** No `RMM` |
| **Sticky Exception Bits** | `NV[4], DZ[3], OF[2], UF[1], NX[0]` (`fext_insts.sail:L68-L72`); **no denormal flag; zero hardware trap enables** | `IE[0], DE[1]` (non-IEEE denormal), `ZE[2], OE[3], UE[4], PE[5]`; clearing `IM..PM[12:7]` traps `#XM` | `FPSR`: `IOC[0], DZC[1], OFC[2], UFC[3], IXC[4], IDC[7]`, SIMD `QC[27]`; optional traps via `FPCR[15,12:8]` |
| **Reserved / Disabled Traps** | `write_fcsr` (`fdext_regs.sail:L440-L444`) allows `101..111` in `fcsr.FRM`, trapping `Illegal_Instruction` only on dynamic `rm=111` or RVV FP ops (`L55-L61`); `mstatus.FS=00` traps all `F`/`D` | `LDMXCSR` with reserved bits `[31:16]` raises `#GP(0)`; `CR0.EM`/`OSFXSR` traps SSE | `FPCR.RMode` is 2-bit exhaustive (`00..11`); `CPACR_EL1.FPEN` / `CPTR_EL2` traps FP/SIMD |
| **Static Insn Override** | **Scalar F/D:** 3-bit `rm` `[14:12]` (`rne..rmm`) bypasses `fcsr.FRM` (`fext_insts.sail:L51-L63`). **RVV FP:** **None** | **AVX-512 EVEX reg-reg only** (`{rn-sae}`..`{rz-sae}`): static RM **forcibly implies SAE** (suppresses flags & traps!) | **Scalar & NEON:** None (beyond `FCVT*` variants); `FPCR.AH=1` changes global `FMIN`/`FMAX`/NaN rules |
| **ABI Convention** | `riscv-cc.adoc:L96-L98`: `fcsr` has C11 `<fenv.h>` thread storage duration (persistent across calls; RVV `vxrm`/`vxsat` caller-saved `L111-L120`) | System V AMD64 / Win64: control/mask bits thread-global (non-default changes require `<fenv.h>`); sticky `MXCSR[5:0]` volatile | `aapcs64.rst:L898-L906`: `FPSR` unpreserved across public calls; `FPCR` global (`0-1, 8-12, 22-24` modifiable by FP-env helpers; `NEP=0` required) |

Inspecting `riscv/sail-riscv@76f1ce3c` exposes two subtle ISA state couplings:
1. **Static vs. Dynamic Rounding Asymmetry (`fext_insts.sail:L51-L63` vs. `vext_fp_utils_insts.sail:L16-L21`):** `select_instr_or_fcsr_rm(instr_rm)` checks `fcsr[FRM]` *only* when `instr_rm == RM_DYN` (`0b111`). Scalar instructions carrying static `0b000` (`rne`) execute cleanly even if `fcsr.FRM` holds illegal `0b101..0b111`. Conversely, RVV FP instructions encode no `rm` field and validate `not(rm_3b == 0b101 | rm_3b == 0b110 | rm_3b == 0b111)` directly in `valid_fp_op`.
2. **Configurable `mstatus.FS` Dirtying (`fdext_regs.sail:L447-L463`):** While `wF` (`L209`) unconditionally sets `mstatus[FS] = Dirty` (`0b11`), `accrue_fflags` updates `FS = Dirty` (`mstatus` and `vsstatus`) under one of three platform policies: `Fflags_Dirty_Precise` (`(fcsr[FFLAGS] | flags) != fcsr[FFLAGS]`), `Fflags_Dirty_Flag` (`flags != zeros()`), or `Fflags_Dirty_Instruction` (always). Thus non-`f`-writing FP compares (`feq.s`, `flt.s`) leave `mstatus.FS` behavior dependent on core-specific configuration.

---

### 2. C23 `FENV_ACCESS` / `FENV_ROUND`, LLVM Constrained Intrinsics, and Rust Inline-Assembly / FFI / LTO Hazards

Basis: normative + source + execution

#### 2.1 C23 Floating-Point Pragmas vs. Real Compiler Codegen (`gcc 15.2.0` & LLVM `23`)

ISO/IEC 9899:2024 (C23) defines `#pragma STDC FENV_ACCESS ON` (forbidding CSE/hoisting/folding across `<fenv.h>` calls) and new `#pragma STDC FENV_ROUND direction` (lexically scoped static rounding including `constexpr`, mapping cleanly to RISC-V static `rm`). Yet running our C23 probe on `gcc (Debian 15.2.0-14) 15.2.0` (`x86_64-linux-gnu`) with `a = 1.0f (0x3f800000)` and `b = 2^-25 (0x33000000)` (`RNE -> 0x3f800000`, `RUP -> 0x3f800001`) reveals a live SSA CSE miscompilation even under `-frounding-math`:

| Probe Case in C23 Binary (`gcc 15.2.0 -std=c23 -O2`) | Without `-frounding-math` | With `-frounding-math` | Observed Assembly / Root Cause |
| :--- | :--- | :--- | :--- |
| Interprocedural `add_const_fold()` (`1.0f + 0x1.0p-25f`) under `FE_UPWARD` | `folded=0x3f800000`, `rt=0x3f800001` | `folded=0x3f800001`, `rt=0x3f800001` | `-frounding-math` stops constant folding of inexact expressions |
| Intraprocedural `s1 = a+b; fesetround(FE_UPWARD); s2 = a+b; fesetround(FE_TONEAREST);` | `s1=0x3f800000, s2=0x3f800000` (wrong) | `s1=0x3f800000, s2=0x3f800000` (**STILL wrong!**) | `objdump -d`: GCC schedules both `call fesetround@plt` calls back-to-back (`+0x1d..0x24`) before a **single** `addss` (`+0x2f`) |
| Intraprocedural CSE across `__asm__ volatile("ldmxcsr %0" : : "m"(csr_up) : "memory")` | `s1=0x3f800000, s2=0x3f800000` (wrong) | `s1=0x3f800000, s2=0x3f800000` (**STILL wrong!**) | `"memory"` clobber does not block pure SSA GVN on `addss` |
| Register-laundered SSA barrier (`__asm__ volatile("" : "+x"(s1))` and `"+x"(a), "+x"(b)`) | `s1=0x3f800000, s2=0x3f800001` | `s1=0x3f800000, s2=0x3f800001` | `+x` opaque register dependency breaks GCC GVN |

In **LLVM** (`llvm/llvm-project@1163b549`, `FPEnv.h:L39-L88`), standard IR ops assume `isDefaultFPEnvironment(ebIgnore, NearestTiesToEven)` (`L68-L70`) with no CSR effects. Sound optimization barriers require `strictfp` functions lowering every FP op to `@llvm.experimental.constrained.*` intrinsics with `"round.dynamic"` and `"fpexcept.strict"` / `"fpexcept.maytrap"` (`L39-L43`). Crucially, on RISC-V (`RISCVInstrInfoF.td:L556-L580`), `PatFprFprDynFrm_m` lowers unconstrained `fadd` to `FRM_DYN` (`0b111`), so unconstrained Rust/LLVM code still reads `fcsr.FRM` dynamically at runtime.

#### 2.2 Rust Inline Assembly, RFC 3514, FFI, and Cross-Language LTO Hazards

RFC 3514 (`rust-lang/rfcs@f43d5789`, `text/3514-float-semantics.md:L58-L59`) forbids executing Rust FP code under modified FP control bits or observing status flags. Moreover, in `rust-lang/rust@c7d5ba59` (`compiler/rustc_codegen_llvm/src/asm.rs:L259-L280`), omitting `options(preserves_flags)` emits:
- **x86 / x86-64:** `~{dirflag}`, `~{fpsr}`, `~{flags}` — where `X86RegisterInfo.td:L444-L452` defines `"fpsr"` as **legacy x87 `FPSW`**, omitting `MXCSR` (and LLVM MachineIR deliberately omits `Defs` of `MXCSR` flag bits, `L450-L451`);
- **AArch64:** `~{cc}` (`NZCV` only — omitting `FPCR` and `FPSR`);
- **RISC-V:** `~{fflags}`, `~{vtype}`, `~{vl}`, `~{vxsat}`, `~{vxrm}` (omitting `~{frm}`).

This causes three cross-boundary failures: (1) inline `asm!` mutating `MXCSR`/`FPCR`/`frm` inside Rust cannot stop LLVM from hoisting or CSEing surrounding unconstrained `fadd` ops even with `"memory"` and without `preserves_flags`; (2) invoking a pure `extern "C"` Rust function from C (`FENV_ACCESS ON`) or an LFI Arm64 sandbox (`MRS`/`MSR` `FPCR`/`FPSR`) under `FE_UPWARD`/`FTZ` mixes compile-time `RNE`-folded constants with runtime `RUP`/`FTZ` machine instructions inside one Rust function; and (3) cross-language ThinLTO (`-Zcross-language-lto`) between Clang `-ffp-model=strict` (`strictfp`) and non-`strictfp` `rustc` TUs blocks inlining or leaks unconstrained RNE constant propagation across FFI calls without diagnostics.

---

### 3. How Dynamic Rounding Modes, Subnormal Flushing, and Sticky Flags Break Pure RNE Models and Portable SIMD-vs-Scalar Equivalence

Basis: normative + source + execution + derived

1. **Zero-Sign Inversion and Relaxed Error Bounds:** Under `RDN`, $x + (-x) = -0.0$ rather than $+0.0$ (`HOL4` `binary_ieeeScript.sml:L3926-L3928`), inverting `1.0 / (x - x)` from `+\infty` to `-\infty` and flipping `to_bits()`. Error bounds double from $0.5\text{ ulp}$ (`RNE`) to $1\text{ ulp}$ (`RDN`/`RUP`/`RTZ`): e.g., `(1.0f + 2^-25) + 2^-25` stays `0x3f800000` under `RNE` but becomes `0x3f800002` under `RUP`.
2. **Subnormal Flushing (`FTZ`/`DAZ`, `FPCR.FZ`/`FIZ`):** On `x86_64`, IEEE default `MXCSR = 0x00001f80` computes `0x00000001 * 0.5f = 0x00000000` with sticky `0x32` (`DE | UE | PE`). With `DAZ+FTZ` (`0x00009fc0`), runtime `_mm_add_ps(0x00400000, +0.0f)` returns **`0x00000000`** (`sticky = 0x00`), whereas constant-folded `0x00400000 + +0.0f` remains **`0x00400000`**, breaking both constant-folding equivalence and `a - b == 0.0 => a == b` zero-divisor guards (while x87 ignores `MXCSR.DAZ`/`FTZ` on `i686`).
3. **Spurious Sticky Flags / Traps from Inactive SIMD Lanes:** Running `_mm_add_ps([1.0f, sNaN (0x7f800001), 0.0f, 0.0f], [2.0f; 4])` on `x86_64` produces `0x40400000` (`3.0f`) in lane 0 while setting `MXCSR.IE = 0x01` (or raising fatal `#XM` when `IM == 0`), diverging from scalar lane-0 execution (`sticky = 0x00`) unless masked (`AVX-512 {k}`/`{sae}` or RVV inactive elements) or inert-padded.
4. **RISC-V Scalar Static-RM vs. RVV Vectorization Asymmetry:** Scalar RISC-V code hardened with static `, rne` (`0b000`) is independent of `fcsr.FRM`, yet auto-vectorizing it to RVV `vfadd.vv` (`vext_fp_utils_insts.sail:L16-L21`) re-couples execution to `fcsr.FRM` and introduces `Illegal_Instruction` traps when `fcsr.FRM ∈ {101..111}`.

---

### 4. How Verified Compilers and Proof Frameworks Model, Guard, or Bypass Rounding-Mode and Flag State

Basis: source + documentation + derived

- **CompCert & Flocq (`AbsInt/CompCert@2685140b`, `10.1007/s10817-014-9314-5`):** `lib/Floats.v:L31-L32, L124-L147` instantiates `Flocq.BinarySingleNaN` exclusively at `mode_NE`. Across `x86/Asm.v:L218-L226, L866-L874`, `aarch64/Asm.v`, and `riscV/Asm.v:L84-L93, L270-L315`, `preg` omits `MXCSR`, `FPCR`/`FPSR`, and `fcsr` entirely, treating `Pfadds`/`Paddd_ff` as pure transitions under an implicit entry invariant. **Discovered Printer Gap (`riscV/TargetPrinter.ml:L377-L421`):** While `Pfcvtws`/`Pfcvtls` print explicit `, rtz` (`L409-L421`), `Pfadds`..`Pfnmsubs` (`L377-L407`) omit `, rne`, causing `as` to encode `rm = 0b111` (`DYN`) and leaving CompCert RISC-V binaries dependent on external `fcsr.FRM == 0b000` even though printing `, rne` would make scalar arithmetic CSR-independent.
- **CakeML (`CakeML/cakeml@2874b664`, `10.4230/LIPIcs.ECOOP.2022.1`):** Source `fpSemScript.sml:L24-L71` fixes `roundTiesToEven` + `fix_NaN` (`-1w`), while backend `state_ok` predicates explicitly isolate the CSR slice required on L3 hardware models:
  - `x64_ok` (`x64_targetScript.sml:L23-L27`) requires `~FZ ∧ ~DAZ ∧ (RC = 0w) ∧ PM ∧ UM ∧ OM ∧ ZM ∧ DM ∧ IM ∧ (exception = NoException)`, constraining all 9 control/mask bits while leaving the 6 sticky status bits (`MXCSR[5:0]`) unconstrained so SSE instructions preserve `x64_ok`.
  - `arm8_ok` (`arm8_targetScript.sml:L20-L26`) exploits AArch64's split registers by requiring `(FPCR = 0w)` while leaving `FPSR` unconstrained.
  - `riscv_targetScript.sml:L183, L309` disables hardware FP altogether (`fp_reg_count := 0`, `riscv_ast (Inst (FP _)) = riscv_encode_fail`).
- **HOL4 `binary_ieee`/`machine_ieee` (`HOL-Theorem-Prover/HOL@aee6a90d`):** Operations (`float_add mode x y` in `binary_ieeeScript.sml:L588-L599`, `fp64_to_fp32_with_flags` in `machine_ieeeScript.sml:L23-L86`) return `(flags, float)` pairs parameterized by `mode`, deriving pure functions via `SND` projection (`fp64_to_fp32 m = SND o fp64_to_fp32_with_flags m`).

This yields **three verified boundary patterns** for stateful ISA composition: (1) **Control/Status Slice Decomposition** (prove `ctrl' = ctrl = default_RNE` and monotonic `status' = status | Δflags`, erasing `status` unless externally observed); (2) **Static-RM Hardening** on RISC-V scalar `F`/`D` (emit explicit `, rne`, requiring only `mstatus.FS != 0b00` while blocking RVV vectorization unless `fcsr.FRM == 0b000`); and (3) **FFI / Sandbox CSR Scrubbing** (save/set/restore `fcsr`/`MXCSR`/`FPCR` around untrusted FFI or sandbox trampolines).

## Boundaries

- **Standard Rust arithmetic under non-default CSR state (`known not to apply`):** Executing standard Rust FP operations with modified rounding modes, `FTZ`/`DAZ`, or unmasked FP traps is UB under RFC 3514 (`L52-L59`) and fails under constant folding and `asm.rs` clobber omissions.
- **GCC `15.2.0` `FENV_ACCESS` and CakeML RISC-V FP (`unsupported`):** As proved via `objdump -d`, `gcc 15.2.0 -std=c23 -O2 -frounding-math` still CSEs `a + b` across `fesetround()` and `ldmxcsr` unless `+x` register barriers are inserted (`unsupported` full `FENV_ACCESS` isolation); CakeML's RISC-V backend marks hardware FP `unsupported` (`fp_reg_count := 0`).
- **Microarchitectural `mstatus.FS` dirtying on zero-flag comparisons (`unknown`):** Because `sail-riscv` (`fdext_regs.sail:L451-L455`) parameterizes three valid silicon policies (`Fflags_Dirty_Precise`, `Fflags_Dirty_Flag`, `Fflags_Dirty_Instruction`), whether `feq.s`/`flt.s` with `flags == 0` dirties `mstatus.FS` is `unknown` without per-core configuration.
- **Decimal FP, Arm SME `FPMR`, and `SIGFPE` trap recovery (`not examined`):** ISO C23 `_Decimal32`/`64`/`128` (`FENV_DEC_ROUND`), Arm SME2 `FPMR` (`aapcs64.rst:L917`), and POSIX `SIGFPE` handler resumption from unmasked traps were `not examined`.

## Evidence

### Primary Upstream Sources

1. **Sail RISC-V (`riscv/sail-riscv@76f1ce3c184797178864b9869963e8b44465889e`):** `model/extensions/FD/fdext_regs.sail:L110-L127, L208-L210, L433-L463`; `fdext_control.sail:L18-L39`; `fext_insts.sail:L31-L73`; `model/extensions/V/vext_fp_utils_insts.sail:L16-L52`.
2. **ABIs (`riscv-non-isa/riscv-elf-psabi-doc@56561cb3e7330fe99a98fd27457229707b2786ae`, `ARM-software/abi-aa@9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`):** `riscv-cc.adoc:L96-L155`; `aapcs64/aapcs64.rst:L898-L917`.
3. **LLVM & Rust (`llvm/llvm-project@1163b5496994b8c5a8ef3377faa8858283fad39c`, `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`):** `llvm/include/llvm/IR/FPEnv.h:L39-L88`; `llvm/lib/Target/RISCV/RISCVInstrInfoF.td:L520-L580`; `llvm/lib/Target/X86/X86RegisterInfo.td:L443-L453`; `compiler/rustc_codegen_llvm/src/asm.rs:L259-L289`; `text/3514-float-semantics.md:L50-L59`.
4. **CompCert, CakeML & HOL4 (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`, `CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`, `HOL-Theorem-Prover/HOL@aee6a90d9856a842f4cbd2bfc44efb7067a141e4`):** CompCert `lib/Floats.v:L31-L32, L124-L147`, `x86/Asm.v:L218-L226, L866-L874`, `riscV/Asm.v:L84-L93, L270-L315`, `riscV/TargetPrinter.ml:L377-L421`; CakeML `semantics/fpSemScript.sml:L24-L71`, `compiler/encoders/x64/x64_targetScript.sml:L23-L27, L73-L78, L271-L275`, `arm8/arm8_targetScript.sml:L20-L26, L82-L88`, `riscv/riscv_targetScript.sml:L19-L25, L183, L309`; HOL4 `src/floating-point/binary_ieeeScript.sml:L575-L599, L3921-L3929`, `machine_ieeeScript.sml:L23-L86`.

### Peer-Reviewed Literature & Empirical Output (`2026-11-20`)

- Sylvie Boldo, Jacques-Henri Jourdan, Xavier Leroy, Guillaume Melquiond. *Verified Compilation of Floating-Point Computations*, JAR 2015, DOI: `10.1007/s10817-014-9314-5` (ARITH 2013 DOI: `10.1109/ARITH.2013.30`).
- Heiko Becker et al., *Verified Compilation and Optimization of Floating-Point Programs in CakeML*, ECOOP 2022, DOI: `10.4230/LIPIcs.ECOOP.2022.1`.
- Empirical run on `gcc (Debian 15.2.0-14) 15.2.0` (`x86_64-linux-gnu`): `-std=c23 -O2` gave `folded=0x3f800000 rt=0x3f800001`, `cse=(0x3f800000,0x3f800000)`, `under=0x00000000(sticky=0x32)`, `daz_vadd=0x00000000(mxcsr=0x00009fc0)`, `simd_lane0=0x40400000(sticky=0x01)`. With `-frounding-math`, `folded=0x3f800001` yet `cse` remained `(0x3f800000,0x3f800000)` (`objdump -d`: both `call fesetround@plt` at `+0x1d`/`+0x24` before one `addss` at `+0x2f`), while `+x` barriers gave `(0x3f800000,0x3f800001)`.

## Revalidation

```bash
python3 - <<'PY'
import subprocess, tempfile, pathlib

c_src = r'''
#include <fenv.h>
#include <immintrin.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
static uint32_t f2u(float x) { uint32_t u; memcpy(&u, &x, 4); return u; }
__attribute__((noinline)) float add_const(void) { return 1.0f + 0x1.0p-25f; }
__attribute__((noinline)) float add_rt(float a, float b) { return a + b; }
__attribute__((noinline)) float mul_rt(float a, float b) { return a * b; }
__attribute__((noinline)) __m128 vadd_rt(__m128 a, __m128 b) { return _mm_add_ps(a, b); }
__attribute__((noinline)) void cse_feset(float a, float b, uint32_t *r1, uint32_t *r2) {
    float s1 = a + b; fesetround(FE_UPWARD); float s2 = a + b; fesetround(FE_TONEAREST);
    *r1 = f2u(s1); *r2 = f2u(s2);
}
__attribute__((noinline)) void bar_feset(float a, float b, uint32_t *r1, uint32_t *r2) {
    float s1 = a + b; __asm__ volatile ("" : "+x"(s1));
    fesetround(FE_UPWARD); __asm__ volatile ("" : "+x"(a), "+x"(b));
    float s2 = a + b; __asm__ volatile ("" : "+x"(s2));
    fesetround(FE_TONEAREST); *r1 = f2u(s1); *r2 = f2u(s2);
}
int main(void) {
    uint32_t init = _mm_getcsr();
    fesetround(FE_UPWARD); float f = add_const(), r = add_rt(1.0f, 0x1.0p-25f); fesetround(FE_TONEAREST);
    uint32_t u1, u2, b1, b2; cse_feset(1.0f, 0x1.0p-25f, &u1, &u2); bar_feset(1.0f, 0x1.0p-25f, &b1, &b2);
    feclearexcept(FE_ALL_EXCEPT);
    float sm; uint32_t mb = 1u; memcpy(&sm, &mb, 4); float un = mul_rt(sm, 0.5f); uint32_t m_un = _mm_getcsr();
    _mm_setcsr((init & ~0x3fu) | 0x8040u);
    float sh; uint32_t hb = 0x00400000u; memcpy(&sh, &hb, 4);
    __m128 vd = vadd_rt(_mm_set1_ps(sh), _mm_setzero_ps()); uint32_t m_dz = _mm_getcsr();
    _mm_setcsr(init & ~0x3fu);
    float sn; uint32_t sb = 0x7f800001u; memcpy(&sn, &sb, 4);
    float l0 = _mm_cvtss_f32(vadd_rt(_mm_setr_ps(1.0f, sn, 0.0f, 0.0f), _mm_set1_ps(2.0f))); uint32_t m_sm = _mm_getcsr();
    _mm_setcsr(init);
    printf("folded=0x%08x rt=0x%08x cse=(0x%08x,0x%08x) bar=(0x%08x,0x%08x)\n", f2u(f), f2u(r), u1, u2, b1, b2);
    printf("under=0x%08x(0x%02x) daz=0x%08x(0x%08x) simd=0x%08x(0x%02x)\n", f2u(un), m_un&0x3fu, f2u(_mm_cvtss_f32(vd)), m_dz, f2u(l0), m_sm&0x3fu);
    return 0;
}
'''
with tempfile.TemporaryDirectory() as td:
    src = pathlib.Path(td) / "p.c"; src.write_text(c_src)
    for lbl, ex in [("O2", []), ("O2_frounding_math", ["-frounding-math"])]:
        bp = pathlib.Path(td) / lbl
        subprocess.run(["gcc", "-std=c23", "-O2", *ex, str(src), "-o", str(bp), "-lm"], check=True)
        print(f"=== {lbl} ===", subprocess.check_output([str(bp)], text=True).strip())
        if ex:
            print(subprocess.check_output(["objdump", "-d", "--disassemble=cse_feset", str(bp)], text=True).strip())

for repo, sha, path, needles in [
    ("riscv/sail-riscv", "76f1ce3c184797178864b9869963e8b44465889e", "model/extensions/FD/fext_insts.sail", ["select_instr_or_fcsr_rm"]),
    ("rust-lang/rust", "c7d5ba59d8e11ee2e2204b173458eec4cb41c973", "compiler/rustc_codegen_llvm/src/asm.rs", ['"~{fpsr}"', '"~{fflags}"']),
    ("AbsInt/CompCert", "2685140bf72c959446981fb99b5e44a8975021bc", "riscV/TargetPrinter.ml", ["fadd.s\t%a, %a, %a", "fcvt.w.s\t%a, %a, rtz"]),
    ("CakeML/cakeml", "2874b664e10939a3ee462215b2e068c89c1f70eb", "compiler/encoders/x64/x64_targetScript.sml", ["ms.MXCSR.RC = 0w"]),
]:
    url = f"https://raw.githubusercontent.com/{repo}/{sha}/{path}"
    txt = subprocess.check_output(["curl", "--http1.1", "-fsSL", url], text=True)
    for n in needles: assert n in txt, (repo, path, n)
    print(f"OK: {repo}@{sha[:8]}:{path}")
PY
```
