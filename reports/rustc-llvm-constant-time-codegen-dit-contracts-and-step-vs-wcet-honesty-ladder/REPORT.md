# rustc/LLVM Constant-Time Preservation, Hardware DIT/DOITM/Zkt Contracts, and the Step-Count vs. WCET / Timing-NI Honesty Ladder

## Summary

Verifying timing-channel freedom and execution-time bounds for compiled systems Rust requires separating four distinct technical claims that are frequently conflated: MIR-level constant-time discipline, post-link architectural constant-time machine code under hardware data-independent timing contracts, architectural retired-instruction step bounds, and microarchitectural WCET / cross-domain timing-channel noninterference.

1. **Empirical `rustc`/LLVM Constant-Time Breakage Across Optimization Levels and ISAs (`rustc 1.102.0-nightly`, LLVM `23.1.5`; `llc 21.1.8`):** Compiling 27 canonical constant-time Rust functions (`support/ct_idioms.rs`) across 16 target/optimization configurations (`x86_64`, `aarch64`, `riscv64gc`, `riscv64+zicond`, `thumbv7m`; `-O2`, `-O3`, `-Os`, `-Oz`) demonstrates that LLVM silently breaks textbook branchless idioms in ways that depend on optimization level, target ISA, and surrounding context:
   - **Linear-scan table masking (`ct_lut_linear_scan_16`):** On `x86_64`, LLVM `23.1.5` turns a 16-entry constant-time linear scan into **16 unrolled secret-dependent conditional branches (`jne`) gating 16 conditional memory loads** at `-C opt-level=2`, and into a secret-dependent branch inside the loop at `-Os` and `-Oz`, while emitting a branchless SSE2 SIMD scan at `-C opt-level=3` purely as a side effect of vectorization.
   - **Wrapping masks and bitmath comparisons (`ct_wrap_mask_load_arms`, `ct_u64_lt_bitmath_load_select`, `ct_u64_eq_bitmath_load_select`):** On `x86_64` (`-O2`/`-O3`/`-Os`/`-Oz`) and `riscv64gc`, LLVM folds wrapping masks `((c as u64).wrapping_neg() & va) | (!m & vb)` and hand-rolled Hacker's Delight/BearSSL bitmath comparisons back into conditional branches (`jne`, `js`, `je`, `bnez`, `bltz`, `beq`) with sunk memory loads, whereas `aarch64` lowers the same IR to branchless `csel`.
   - **Aggregate and RISC-V `select_unpredictable` hazards (`ct_select_unpred_struct`, `ct_select_unpred_u64`, `ct_select_unpred_in_loop`):** On a 32-byte `#[repr(C)]` struct `[u64; 4]`, `core::hint::select_unpredictable` lowers across **all three 64-bit ISAs** to a **secret-selected pointer** (`cmovneq`/`csel`/`bnez`) followed by a **secret-addressed memory load** (`movups (%rdx)` / `ldp q0, q1, [x9]`), leaking the secret bit through cache-line access addresses. On base `riscv64gc` (without `+zicond`), even scalar `select_unpredictable` lowers to conditional branches (`bnez`/`beqz`).
   - **`core::hint::black_box` and variable-latency instructions:** `black_box` forces un-erased stack/red-zone spills (`-1(%rsp)` / `[sp, #15]`), induces secret-dependent branches in `black_box(c1) && black_box(c2)` across all targets (`je`/`tbz`/`beqz`) because `asm sideeffect` forbids speculative evaluation of the RHS, and provides zero protection against `BypassSlowDivision` or variable-latency `div`/`udiv`/`divu` emission (including KyberSlash-class constant division emitting `divl`/`udiv`/`divuw` at `-Oz` on every tested ISA).
2. **Division of Labor (MIR CT vs. Post-Link Binary `CtProduct` + Hardware `DIT`/`DOITM`/`Zkt`):** Because single-trace-refining LLVM lowering invalidates source- and MIR-level constant-time invariants, MIR-level CT contracts serve only as early algorithmic checks. Sound architectural constant-time assurance requires **post-link relational 2-safety verification (`CtProduct`) over decoded `.o`/ELF instructions** paired with an explicit ISA-level `DIT`/`DOITM`/`Zkt` opcode allowlist (universally forbidding `DIV`/`IDIV`/`UDIV`/`SDIV`/`REM` and unguarded IEEE-754 floating-point) and an explicit execution-mode/context-switch contract (`PSTATE.DIT` in EL0/`SPSR_EL1`, Ring-0 MSR `IA32_UARCH_MISC_CTL[0]`, or static `Zkt`).
3. **Stage 0 → Stage 1 → Stage 2 Verification Honesty Ladder:** A four-rung taxonomy (`(a)` architectural step-count bounds, `(b)` storage-channel-only intransitive noninterference, `(c)` post-link architectural constant-time under `DIT`/`DOITM`/`Zkt`, and `(d)` microarchitectural WCET / cache-and-temporally-partitioned timing-channel freedom) prevents assurance receipts from conflating retired-instruction bounds with real-time WCET or storage NI with timing NI. Five separation and positive-upgrade theorems are kernel-checked in `support/StepVsTimingWitness.lean` (`Lean 4 v4.34.1`, `Type 0`, zero `sorry`).

## Applicability

### Examined Subjects and Their Relationships

This report combines four evidentiary strands across the subjects pinned in `REPORT.json`:

1. **Native `rustc` codegen (`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc 1.102.0-nightly`, `LLVM 23.1.5`):** Directly invoked with `--crate-type=lib --edition=2024 -C panic=abort --emit=asm` on `support/ct_idioms.rs` for `x86_64-unknown-linux-gnu` (`opt-level=2, 3, s, z`) and `thumbv7m-none-eabi` (`opt-level=2, 3, z`).
2. **Cross-target AArch64 and RISC-V 64 codegen (`Debian LLVM llc 21.1.8`):** Because `aarch64-unknown-none` and `riscv64gc-unknown-none-elf` `libcore` sysroots were not preinstalled on the host, `support/probe_ct_codegen.py` emits target-optimized LLVM IR from `rustc 1.102.0-nightly` (`--emit=llvm-ir -C opt-level=2, 3, z`), performs minimal syntactic adaptation from LLVM 23 IR to LLVM 21 IR (stripping `target datalayout`/`triple`, x86 `target-cpu`/`target-features`, `!guid`, `target_mem:`, `dead_on_return`/`dead_on_unwind`, `nocreateundeforpoison`; mapping `captures(none)` → `nocapture`; restoring the 2-argument `i64 -1` form of `llvm.lifetime.{start,end}.p0`) while **preserving `!unpredictable` metadata and `asm sideeffect` barriers verbatim**, and lowers via `llc` for `aarch64-unknown-none`, `riscv64-unknown-none-elf` (`+m,+a,+f,+d,+c`), and `riscv64-unknown-none-elf` (`+m,+a,+f,+d,+c,+zicond`). Because middle-end IR passes ran under `x86_64` target transform info before `llc` backend selection, AArch64 and RISC-V results characterize LLVM backend lowering of `rustc`-produced IR rather than end-to-end target-native middle-end heuristics; exact native `rustc` behavior is pinned directly on `x86_64` and `thumbv7m`.
3. **Normative hardware timing contracts and primary systems/WCET literature:** Synthesizes Arm `FEAT_DIT` (`DDI 0487`, Armv8.4-A), Intel `DOITM` (`ID 768873` / `ID 759656`), RISC-V `Zkt` (`v1.0.1`), seL4 information-flow and Time Protection literature (Murray et al. S&P 2013; Ge et al. APSys 2018 & EuroSys 2019; Wistoff et al. IEEE TC 2023), and WCET / cost-semantics literature (Wilhelm et al. ACM TECS 2008; Blackham et al. RTSS 2011; Sewell et al. RTAS 2016; Schommer et al. WCET 2018; Gómez-Londoño et al. OOPSLA 2020).
4. **Mechanized `Type 0` Lean 4 witness (`leanprover/lean4:v4.34.1`):** `support/StepVsTimingWitness.lean` formalizes the honesty-ladder separations and positive upgrade condition in core Lean 4 without external libraries.

### Scope Delta Relative to Existing Corpus Packages

Existing corpus packages already cover: (i) foundational 2-safety CT theory and the 5-level `Val-NI ≺ Arch-CT ≺ VarTime-CT ≺ Spec-CT ≺ DMP-CT` lattice (`side-channel-freedom-foundations-and-leakage-contracts-1996-2026`), (ii) `rustc 1.98.0 / LLVM 22.1.6` x86-64-only probes for DSE, `LFENCE` hoisting, CompCert-CT, Jasmin, FaCT, and Binsec/Rel (`compiler-preservation-of-constant-time-secret-erasure-and-speculative-fences`), (iii) `black_box` IR lowering and Intel DOIT Table-1 opcode inventory (`nostack-redzone-mxcsr-fastmath-hazards-usercopy-fault-tables-and-seqlock-traces`), (iv) `zeroize` and cryptographic typestate machines (`zeroize-volatile-erasure-dse-survival-and-typestate-crypto-handshake-machines`), (v) speculative execution and DMP contracts (`transient-execution-spectre-v1-bounds-masking-and-page-table-walk-cache-leakage`, `transient-execution-attacks-dmp-prefetchers-and-hardware-leakage-contracts`), (vi) timing anomalies and multicore interference (`reineke-anomaly-taxonomy-llvmta-sic-pipeline-compositionality-and-hard-realtime-multithreaded-cores`, `multicore-realtime-interference-cache-partitioning-and-mrsp-locking`), and (vii) `seL4/l4v` storage-channel unwinding and MIR fuel credits (`murray-intransitive-unwinding-speculative-constant-time-and-fuel-time-credits`).

This report covers strictly the **unclosed delta**: (1) cross-opt-level and cross-architecture (`x86_64` / `aarch64` / `riscv64gc` / `riscv64+zicond` / `thumbv7m`) empirical CT codegen breakage on `rustc 1.102.0-nightly (LLVM 23.1.5)` across all seven canonical Rust CT idiom families, (2) privilege/context-switch/FP-subnormal semantics of `PSTATE.DIT` vs. `DOITM` vs. `Zkt`, (3) the MIR-vs-post-link `CtProduct` verification split, and (4) the seL4 Time Protection / AbsInt `aiT` / CompCert-WCET / CakeML synthesis anchored in a mechanized **Stage 0 → Stage 1 → Stage 2 Honesty Ladder**.

## Findings

### 1. Empirical `rustc`/LLVM Constant-Time Codegen Matrix Across Idioms, Opt Levels, and ISAs

`Basis: execution + source` (`support/ct_idioms.rs`, `support/probe_ct_codegen.py`, `support/probe_ct_codegen_results.json`)

Compiling the 27 constant-time Rust probe functions in `support/ct_idioms.rs` across `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11, LLVM 23.1.5)` and `llc 21.1.8` yields six distinct classes of compiler-induced constant-time failure.

#### 1.1 Cross-Target Summary Matrix (`27` Functions, Key Configurations)

In the table below, **SEC-BR** denotes at least one conditional branch driven by a secret input (excluding public loop-counter branches on `n`), **SEC-ADDR** denotes a secret-dependent memory load address (e.g., pointer select or `.rodata` LUT), **JMPTBL** denotes a `.rodata` jump table with indirect branch, **DIV** denotes a variable-latency hardware divide (`divl`/`divq`/`udiv`/`divuw`), **SPILL** denotes an un-erased secret byte spilled to stack/red-zone memory, **FP** denotes an IEEE-754 floating-point instruction with no FTZ/DAZ guard, and **OK** denotes branchless, fixed-address, `DIT`-admissible ALU/SIMD emission.

| Idiom Family & Function | `x86_64` `-O2` (`rustc` 1.102) | `x86_64` `-O3` (`rustc` 1.102) | `x86_64` `-Oz` (`rustc` 1.102) | `aarch64` `-O2` (`llc` 21.1.8) | `riscv64gc` `-O2` (`llc` 21.1.8) | `riscv64+zicond` `-O2` (`llc`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`select_unpredictable`:** | | | | | | |
| `ct_select_unpred_u64` | OK (`cmoveq`) | OK (`cmoveq`) | OK (`cmoveq`) | OK (`csel`) | **SEC-BR (`bnez`)** | OK (`czero.*`) |
| `ct_select_unpred_load_arms` | OK (`cmoveq`, both loads uncond.) | OK (`cmoveq`) | OK (`cmoveq`) | OK (`csel`) | **SEC-BR (`bnez`)** | OK (`czero.*`) |
| `ct_select_unpred_struct` (`[u64; 4]`) | **SEC-ADDR** (`cmovneq` ptr + `movups`) | **SEC-ADDR** | **SEC-ADDR** | **SEC-ADDR** (`csel` ptr + `ldp`) | **SEC-BR + SEC-ADDR** (`bnez`) | **SEC-ADDR** (`czero` ptr + `ld`) |
| `ct_select_unpred_in_loop` | OK (`3× cmoveq`, pub-`n` brs only) | OK (`3× cmoveq`) | OK (`cmoveq`) | OK (`3× csel`) | **SEC-BR** (`3` secret `bnez`/`beqz` + sunk loads) | OK (`6× czero.*`) |
| **Wrapping-Mask `(m & a) \| (!m & b)`:** | | | | | | |
| `ct_wrap_mask_bool` | OK (aliased to `cmoveq`) | OK | OK | OK (`csel`) | **SEC-BR (`bnez`)** | OK (`czero.*`) |
| `ct_wrap_mask_u8_masked` | OK (`cmovneq`) | OK (`cmovneq`) | OK (`cmovneq`) | OK (`csel`) | OK (pure ALU) | OK (`czero`) |
| `ct_wrap_mask_load_arms` | **SEC-BR (`jne`) + sunk loads** | **SEC-BR (`jne`)** | **SEC-BR (`jne`)** | OK (`csel`) | **SEC-BR (`bnez`) + sunk loads** | OK (`czero.*`) |
| `ct_wrap_mask_in_loop` | OK (`cmovneq`, pub-`n` brs) | OK (`cmovneq`) | OK (`cmovneq`) | OK (`csel`) | OK (pure ALU) | OK (`czero`) |
| **`subtle`-Style XOR/AND Select:** | | | | | | |
| `ct_subtle_xor_no_barrier` | OK (pure ALU) | OK (pure ALU) | OK (pure ALU) | OK (pure ALU) | OK (pure ALU) | OK (pure ALU) |
| `ct_subtle_xor_black_box` | **SPILL** (`-1(%rsp)` red zone) | **SPILL** | **SPILL** (stack) | **SPILL** (`[sp,#15]`) | **SPILL** (`(sp)`) | **SPILL** |
| `ct_subtle_xor_volatile` | **SPILL** (`-1(%rsp)`) | **SPILL** | **SPILL** | **SPILL** | **SPILL** | **SPILL** |
| `ct_subtle_xor_in_loop_no_barrier` | OK (pure ALU, pub-`n` brs) | OK | OK | OK | OK | OK |
| `ct_subtle_xor_in_loop_black_box` | **SPILL** (`-1(%rsp)`) | **SPILL** | **SPILL** | **SPILL** (`[sp,#15]`) | **SPILL** | **SPILL** |
| **Constant-Time `u64` Comparisons:** | | | | | | |
| `ct_u64_eq_bitmath` / `ct_u64_lt_bitmath` | OK (pure ALU) | OK (pure ALU) | OK (pure ALU) | OK (pure ALU) | OK (pure ALU) | OK (pure ALU) |
| `ct_u64_lt_bitmath_load_select` | **SEC-BR (`js`) + sunk loads** | **SEC-BR (`js`)** | **SEC-BR (`js`)** | OK (`csel`) | **SEC-BR (`bltz`) + sunk loads** | OK (`czero.*`) |
| `ct_u64_eq_bitmath_load_select` | **SEC-BR (`je`) + sunk loads** | **SEC-BR (`je`)** | **SEC-BR (`jns`)** | OK (`csel`) | **SEC-BR (`beq`) + sunk loads** | OK (`czero.*`) |
| **Lookup-Table Masking & Switches:** | | | | | | |
| `ct_lut_linear_scan_16` (`&[u64; 16]`) | **SEC-BR (16× `jne` + 16 gated loads!)** | OK (SSE2 `pcmpeqb`) | **SEC-BR (`jne` + gated load)** | OK (`16× csel`; `-O3` NEON) | OK (pure ALU) | OK (`16× czero`) |
| `ct_lut_linear_scan_const_sbox` | OK (`14× cmovnel`) | OK (SSE2 `pcmpeqb`) | OK (full 16B scan + `cmovnel`) | OK (`16× csel`; `-O3` NEON) | OK (pure ALU) | OK (`15× czero`) |
| `ct_lut_linear_scan_const_sbox_black_box` | **SPILL** (`-8(%rsp)`, `14× cmovsl`) | **SPILL** (SSE2) | **SPILL** | **SPILL** | **SPILL** | **SPILL** |
| `ct_match_to_rodata_lut` | **SEC-ADDR** (`.Lswitch.table`) | **SEC-ADDR** | **SEC-ADDR** | **SEC-ADDR** (`.Lswitch.table`) | **SEC-ADDR** | **SEC-ADDR** |
| `ct_match_jump_table` | **JMPTBL** (`.LJTI6_0`, `jmpq *%rcx`) | **JMPTBL** | **JMPTBL** | **SEC-BR** (7-br tree) | **JMPTBL** | **JMPTBL** |
| **`black_box`, `DIV`, and Subnormal FP:** | | | | | | |
| `ct_black_box_short_circuit_and` | **SEC-BR (`je`) + SPILL** | **SEC-BR (`je`) + SPILL** | **SEC-BR (`jne`) + SPILL** | **SEC-BR (`tbz`) + SPILL** | **SEC-BR (`beqz`) + SPILL** | **SEC-BR (`beqz`) + SPILL** |
| `ct_black_box_div_still_var_time` | **SEC-BR (`je`) + DIV (`divq`/`divl`) + SPILL** | **SEC-BR + DIV + SPILL** | **DIV (`divq`) + SPILL** | **DIV (`udiv`) + SPILL** | **DIV (`divu`) + SPILL** | **DIV (`divu`) + SPILL** |
| `ct_const_div_kyberslash` (`/ 6658`) | OK (`mulq` magic) | OK (`mulq`) | **DIV (`divl`)** (`-Os`: OK) | OK (`umull`; **`-Oz`: `udiv`**) | OK (magic; **`-Oz`: `divuw`**) | OK (**`-Oz`: `divuw`**) |
| `ct_secret_div_u64` | **SEC-BR (`je`) + DIV (`divq`/`divl`)** | **SEC-BR + DIV** | **DIV (`divq`)** | **DIV (`udiv`)** | **DIV (`divu`)** | **DIV (`divu`)** |
| `ct_subnormal_fp_mul` (`f64`) | **FP (`mulsd`/`addsd`)** | **FP** | **FP** | **FP (`fmul`/`fadd`)** | **FP (`fmul.d`/`fadd.d`)** | **FP** |

*(Native `rustc --target=thumbv7m-none-eabi` under LLVM `23.1.5` additionally confirms that `ct_const_div_kyberslash` lowers to `umull` at `-O2`—which itself has early-termination variable latency on Cortex-M3—and switches to `udiv` at `-Oz`, while `ct_select_unpred_u64` and `ct_wrap_mask_load_arms` lower via Thumb `it`/`itt ne` predication blocks.)*

#### 1.2 Six High-Impact Compiler Breakage Mechanisms (Verbatim Disassembly)

1. **Optimization-Level Inversion in Linear-Scan LUT Masking (`ct_lut_linear_scan_16`):**
   A developer testing a 16-entry constant-time table scan (`acc |= eq.wrapping_neg() & table[i]`) at `-C opt-level=3` observes a clean 50-instruction branchless SSE2 SIMD scan (`pcmpeqb .LCPI3_0(%rip), %xmm1; pand ...; por ...`). Recompiling the **identical** Rust source at `-C opt-level=2` (or `-Os` / `-Oz`) destroys constant-time completely. At `-O2`, LLVM unrolls the loop, recognizes `mask & table[i]` as `select (i == idx), table[i], 0`, and `SelectOptimize` / `CodeGenPrepare` sinks all 16 memory loads behind **16 secret-dependent conditional branches**:
   ```asm
   ; rustc 1.102.0-nightly (LLVM 23.1.5) -C opt-level=2, x86_64:
   andb   $15, %sil
   jne    .LBB3_2
   movq   (%rdi), %r8       ; loaded ONLY if secret_idx == 0 (cache line 0)
   .LBB3_2:
   cmpb   $1, %sil
   jne    .LBB3_4
   movq   8(%rdi), %rcx     ; loaded ONLY if secret_idx == 1
   ...                      ; repeated across all 16 entries (two 64B cache lines)
   ```
   At `-C opt-level=s` and `-C opt-level=z`, the loop is retained, but LLVM still inserts a secret-dependent branch inside the loop body (`cmpq %rcx, %rsi; jne .LBB4_2; movq (%rdi,%rcx,8), %rdx`), leaking `secret_idx` on both branch predictors and data-cache lines.

2. **Aggregate `select_unpredictable` Lowers to a Secret-Addressed Load (`ct_select_unpred_struct`):**
   Although `core::hint::select_unpredictable` attaches `!unpredictable` to the LLVM IR `select`, for a 32-byte `#[repr(C)] struct Block4 { limbs: [u64; 4] }` passed by value on the stack, `rustc` emits `%0 = select i1 %c, ptr %a, ptr %b, !unpredictable !7` followed by a `memcpy` from `%0`:
   ```asm
   ; rustc 1.102.0-nightly -C opt-level=2, x86_64:      ; llc 21.1.8 -O2, aarch64:
   testl   %esi, %esi                                  add   x9, sp, #32
   leaq    8(%rsp), %rcx                               mov   x10, sp
   leaq    40(%rsp), %rdx                              cmp   w0, #0
   cmovneq %rcx, %rdx                                  csel  x9, x10, x9, ne
   movups  (%rdx), %xmm0     ; secret-selected addr!   ldp   q0, q1, [x9]     ; secret-selected addr!
   movups  16(%rdx), %xmm1                             stp   q0, q1, [x8]
   ```
   Even though no conditional branch is emitted on `x86_64` or `aarch64`, the 32-byte operands at `8(%rsp)` and `40(%rsp)` (or `sp` and `sp + 32`) routinely straddle a 64-byte cache-line boundary, leaking `c` through the L1D cache-address trace. Furthermore, on base `riscv64gc` (without `+zicond`), even scalar `ct_select_unpred_u64` and `ct_select_unpred_in_loop` lower `!unpredictable` selects directly to secret conditional branches (`bnez a0, .LBB12_2`).

3. **Wrapping Masks and Hand-Rolled Bitmath Comparisons Re-Recognized as Branches (`ct_wrap_mask_load_arms`, `ct_u64_{lt,eq}_bitmath_load_select`):**
   Writing branchless masking `let m = (c as u64).wrapping_neg(); (m & va) | (!m & vb)`—or even computing `m` via Hacker's Delight/BearSSL bitmath `((a ^ ((a ^ b) | (a.wrapping_sub(b) ^ b))) >> 63)` or `(((a ^ b) | (a ^ b).wrapping_neg()) >> 63) ^ 1`—does **not** survive LLVM `InstCombine` + `SelectOptimize` when either arm involves a dereferenced load and multiply:
   ```asm
   ; ct_u64_eq_bitmath_load_select (x86_64 -O2):       ; ct_u64_lt_bitmath_load_select (x86_64 -O2):
   cmpq   %rsi, %rdi                                  subq  %rsi, %rax ; ... ; xorq %rdi, %rax
   je     .LBB20_1                                    js    .LBB22_1
   movq   (%rcx), %rax                                movq  (%rcx), %rax
   retq                                               retq
   ```
   Notably, `ct_wrap_mask_bool` (pure register operands) was algebraically collapsed by LLVM `InstCombine` + `MergeFunctions` into an exact symbol alias of `ct_select_unpred_u64` (`@ct_wrap_mask_bool = unnamed_addr alias ..., ptr @ct_select_unpred_u64`)—meaning LLVM erased the bitmask representation before backend codegen even ran.

4. **`.rodata` Lookup Tables and Jump Tables (`ct_match_to_rodata_lut`, `ct_match_jump_table`):**
   `SimplifyCFG::switchToLookupTable` compiles dense constant matches into `.Lswitch.table` secret-indexed loads on all targets (`x86_64`, `aarch64`, `riscv64`). When arms contain distinct arithmetic (`ct_match_jump_table`), `x86_64` and `riscv64` emit a `.rodata` jump table (`.LJTI6_0`) with an indirect jump (`jmpq *%rcx` / `jr`), whereas `aarch64` emits a 7-branch binary decision tree (`b.gt`/`cbnz`/`b.ne`)—both leaking `secret_nibble`.

5. **Double-Edged `core::hint::black_box` Barriers:**
   Wrapping a secret choice bit in `black_box(c & 1)` (as in `subtle`'s `Choice` with `core_hint_black_box`) preserves branchless XOR/AND masking in `ct_subtle_xor_black_box` and `ct_subtle_xor_in_loop_black_box`, **but** incurs three structural hazards: (a) it materializes the secret onto un-erased stack/red-zone memory (`movb %dil, -1(%rsp)` on `x86_64`, `strb w8, [sp, #15]` on `aarch64`), (b) combining two barriers with short-circuit `&&` (`ct_black_box_short_circuit_and`) forces a secret conditional branch (`je`/`tbz`/`beqz`) on **every** ISA because LLVM's `asm sideeffect` prevents speculative evaluation of the second `black_box`, and (c) `black_box` on division operands (`ct_black_box_div_still_var_time`) still lowers to `BypassSlowDivision` (`je` + `divq`/`divl`) on `x86_64` `-O2`/`-O3` and variable-latency `udiv`/`divu` on `aarch64`/`riscv64`.

6. **Universal Size-Optimization `DIV` Regression and Unguarded Floating-Point:**
   At `-C opt-level=z`, `(a * 2 + 3329) / 6658` (`ct_const_div_kyberslash`) reverts from constant-time magic multiplication to hardware division on **every** tested architecture (`divl` on `x86_64`, `udiv` on `aarch64` and `thumbv7m`, `divuw` on `riscv64`). Meanwhile, `ct_subnormal_fp_mul` emits bare `mulsd`/`addsd`, `fmul`/`fadd`, and `fmul.d`/`fadd.d` without touching `MXCSR` or `FPCR`, leaving subnormal operands exposed to 10×–100× microcode-assist timing spikes.

---

### 2. Hardware Data-Independent Timing Contracts (`FEAT_DIT`, `DOITM`, `Zkt`) and Subnormal / `DIV` Hazards

`Basis: normative + documentation`

Even a perfectly branchless, fixed-address binary executes in constant time **only** when every executed opcode obeys a hardware data-independent timing contract. Modern ISAs expose three fundamentally different mechanisms—with asymmetric privilege models, context-switch semantics, and **identical universal exclusions** for integer division and unguarded floating-point:

| Property | Armv8.4-A `FEAT_DIT` (`PSTATE.DIT`) | Intel `DOITM` (`IA32_UARCH_MISC_CTL`) | RISC-V `Zkt` (`v1.0.1`) |
| :--- | :--- | :--- | :--- |
| **Normative Reference** | Arm ARM (`DDI 0487`), mandatory in Armv8.4-A (optional v8.3) | Intel DOIT ISA Guidance (`ID 768873`) & Table 1 (`ID 759656`, 594 mnemonics) | RISC-V Crypto Extensions Vol. I (`v1.0.1`), `Zkt` |
| **Feature Enumeration** | `ID_AA64PFR0_EL1.DIT` (`[51:48]`); Linux ELF `HWCAP_DIT` (`AT_HWCAP`) | `IA32_ARCH_CAPABILITIES` (MSR `0x10A`) bit `12` (`DOITM`); `CPUID.07H.02H:EDX[5]` (`MCDT_NO`) | Static ISA profile / device-tree / Linux `riscv_hwprobe` extension discovery |
| **Privilege to Toggle** | **Unprivileged (EL0–EL3)** via `MSR DIT, #1` / `MRS Xd, DIT` | **Privileged Ring 0 only** (`WRMSR` to MSR `0x1B01` bit `0`; forced on inside SGX enclaves) | **None (always-on static ISA guarantee)** for listed instructions |
| **Exception & Context-Switch Preservation** | Saved automatically into `SPSR_ELx` on trap/syscall and restored by `ERET`; Linux preserves per-thread `PSTATE.DIT` across `schedule()` and can set `DIT` in `EL1` | OS/hypervisor-managed per logical core; unprivileged userland **cannot** self-enable or audit `DOITM` without an OS contract or enclave | Stateless (cannot be lost across traps, interrupts, or context switches) |
| **Guaranteed Instruction Subset** | Enumerated integer ALU, logical, shift, bitfield, `CSEL`, crypto (`AES`/`SHA`/`PMULL`), and specified SIMD ops | 594 Table-1 mnemonics: integer ALU, `CMOVcc`, `MUL`/`IMUL`/`MULX`, `PSHUFB`/`VPERMD`, `AESENC`, `PCLMULQDQ`, integer SIMD `PMULL*` | All scalar crypto (`Zkn`/`Zks`) + enumerated base integer (`I`) and bitmanip (`Zbb`/`Zbkb`) instructions |
| **Integer `DIV` / `REM` Status** | **Explicitly EXCLUDED** (`UDIV`, `SDIV` remain data-dependent!) | **Explicitly EXCLUDED** (`DIV`, `IDIV` absent from Table 1) | **Explicitly EXCLUDED** (`div`, `divu`, `rem`, `remu` excluded from `Zkt`) |
| **Other Notable Exclusions** | Loads/stores (cache/TLB/page-fault timing), branches, floating-point subnormals | `POPCNT`, `LZCNT`, `TZCNT`, `VPERMB`, all SIMD gather/scatter (`VGATHER*`/`VSCATTER*`), **all** IEEE-754 FP | **All** IEEE-754 floating-point (`F`/`D`/`Q`), memory-hierarchy latency, branches |
| **Subnormal FP Control** | `FPCR.FZ` / `FPCR.FZ16` (flush-to-zero; alters IEEE-754 semantics, saved with FPSIMD context) | `MXCSR.FTZ` / `MXCSR.DAZ` (alters IEEE-754 semantics; `MCDT_NO = 0` cores still suffer 1-cycle MXCSR-dependent vector delays unless serialized) | **No architectural hardware FTZ/DAZ bit** in standard RISC-V `F`/`D` `fcsr`—subnormal timing cannot be hardware-flushed portably |
| **Data Memory-Dependent Prefetcher (DMP) Interaction** | On Apple M1/M2, `PSTATE.DIT = 1` does **not** disable DMP (GoFetch); on Apple M3+, `PSTATE.DIT = 1` suppresses DMP dereferences | `DOITM = 1` does **not** disable Spectre speculation and does **not** universally disable DMP without additional microcode/prefetcher MSRs | Implementation-defined; `Zkt` specifies instruction latency only, not speculative or prefetcher behavior |

**Operational Consequence for Verifiers:** Enabling `PSTATE.DIT = 1` or `DOITM = 1` is **necessary** on modern OoO cores (to suppress silent zero-skipping or narrow-operand fast paths in multipliers/ALU), yet **insufficient** unless the verifier *also* rejects every excluded opcode (`DIV`/`IDIV`/`UDIV`/`SDIV`/`REM`, floating-point without an explicit non-IEEE FTZ contract, x86 `VGATHER*`/`POPCNT`/`LZCNT`/`TZCNT`/`VPERMB`). Moreover, on x86-64 userland, because `DOITM` is Ring-0-only, any user-space constant-time receipt must record `IA32_UARCH_MISC_CTL[0] == 1` as an explicit **OS/platform precondition** rather than an inline-verifiable self-enforced instruction.

---

### 3. Division of Labor: MIR-Level CT Contracts vs. Post-Link Binary `CtProduct` Verification

`Basis: derived + execution + normative`

The empirical failures in Section 1 establish an exact architectural boundary between what a Rust MIR verifier can soundly claim and what **must** be deferred to post-link binary verification:

| Verification Layer | What It Can Soundly Verify | What It CANNOT Be Trusted To Guarantee | Recommended Role in Verification Pipeline |
| :--- | :--- | :--- | :--- |
| **Rust MIR-Level CT Contracts** (e.g., secret phantom types, MIR taint/relational checks, `LeakStepObs`) | 1. **Algorithmic secret hygiene:** No source-level `SwitchInt` on secret discriminants, no secret-indexed slice/array indexing, no secret division/remainder operators in MIR, no early-exit secret loops.<br>2. **Public/secret ABI boundary typing:** Explicit secret classification of function parameters, struct fields, and declassification points.<br>3. **Fast developer feedback** at `cargo` check time before codegen. | 1. **Branchless preservation across LLVM:** `InstCombine` + `SelectOptimize` / `CodeGenPrepare` re-introduce `jne`/`js`/`je`/`bnez` on wrapping masks, bitmath comparisons, and linear-scan LUTs (Section 1.2).<br>2. **Aggregate select address independence:** `select_unpredictable` on multi-word structs emits secret-selected pointer loads.<br>3. **Constant-divisor `DIV` avoidance:** `-Oz` emits `divl`/`udiv`/`divuw` from MIR integer division by a constant.<br>4. **Barrier side-effect safety & spill erasure:** `black_box` spills to red zone/stack and breaks short-circuit `&&`; DSE/SROA/register allocation create un-erased register/stack copies.<br>5. **Target ISA `DIT`/`DOITM`/`Zkt` opcode admissibility.** | **Front-end specification & bug-finding layer only.** Emits the `(pub, sec)` ABI signature and declassification annotations consumed downstream; **must NOT** emit a standalone binary constant-time assurance claim. |
| **Post-Link Binary Relational 2-Safety (`CtProduct` over decoded `.o`/ELF instructions)** (e.g., Binsec/Rel `checkct` or a kernel-checked relational ISA certificate over lifted machine code) | 1. **Exact PC / branch-target trace parity** on the linked machine code (`∀ s₁ ≈_pub s₂, pcTrace(s₁) = pcTrace(s₂)`), catching `SelectOptimize`, `X86CmovConversion`, `BypassSlowDivision`, `.LJTI` jump tables, and `black_box &&` branches.<br>2. **Exact effective memory-address trace parity**, catching `.Lswitch.table` `.rodata` LUTs, `ct_lut_linear_scan_16` gated loads, and `ct_select_unpred_struct` pointer-select loads.<br>3. **Strict `DIT`/`DOITM`/`Zkt` opcode allowlist checking**, rejecting every `div`/`idiv`/`udiv`/`sdiv`/`divuw`, `vgather*`, `popcnt`/`lzcnt`/`tzcnt`, and unguarded FP instruction.<br>4. **Wrapper + prologue/epilogue spill & erasure auditing** across the entire linked symbol (including red-zone `[-128, 0)(%rsp)` and caller/callee-saved registers). | 1. **Microarchitectural pipeline/cache WCET** (requires hardware timing model + IPET).<br>2. **Cross-domain microarchitectural isolation** (requires OS Time Protection / `reset_uarch` + cache coloring).<br>3. **Speculative execution (`Spectre v1/v4`)** unless upgraded from sequential `CtProduct` to speculative `SCT` semantics.<br>4. **DMP / power / DVFS frequency-throttling channels** unless hardware generation + `PSTATE.DIT`/enclave policy explicitly rules them out. | **Authoritative constant-time assurance gate** for `Rung (c)` (`PostLinkArchCT`). Consumes MIR ABI secrecy annotations, verifies the linked ELF object directly, and attaches the target's hardware `DIT`/`DOITM`/`Zkt` precondition to the receipt. |

---

### 4. Architectural Step-Count Bounds vs. Microarchitectural WCET and OS Time Protection

`Basis: normative + documentation + derived`

Two widespread category errors recur when formal verification tools report resource or security bounds: **(1)** treating a proven MIR/ISA step-count bound as a Worst-Case Execution Time (WCET) guarantee, and **(2)** treating a proven OS storage-channel noninterference theorem as timing-channel isolation. Primary literature establishes why both conflations are unsound.

#### 4.1 Retired-Instruction Step Counts vs. Microarchitectural WCET

- **Architectural Cost Semantics (`CompCert` / `CakeML` / MIR `fuel : Nat`):** Mechanized cost semantics—such as Gómez-Londoño et al. (*PACMPL OOPSLA 2020*, DOI `10.1145/3428272`) for CakeML space/step accounting, or fuel-indexed MIR/ISA operational semantics—bound **abstract semantic transitions** or **retired ISA instructions** (`steps ≤ f(n)`). These bounds are *exact and machine-independent* for proving **termination, loop-bound finiteness, algorithmic complexity, and DoS/gas budgets**. They do **not** bound wall-clock execution time on any processor with caches, pipelines, branch predictors, DRAM controllers, or variable-latency functional units: two straight-line sequences of 3 retired instructions can differ by >40× in cycle count (L1 hit vs. LLC/DRAM miss, `MUL` vs. `DIV`, normal vs. subnormal FP).
- **Microarchitectural WCET (`AbsInt aiT`, `seL4 WCET`, `CompCert` → `aiT`):** As surveyed by Wilhelm et al. (*ACM TECS 2008*, DOI `10.1145/1347375.1347389`), sound static WCET analysis requires three coupled stages on the **linked binary**:
  1. **Control-flow & infeasible-path / loop-bound extraction:** Must be proven sound on the compiled binary—as demonstrated on seL4 by Blackham et al. (*IEEE RTSS 2011*, DOI `10.1109/RTSS.2011.38`) and Sewell, Kam, and Heiser (*IEEE RTAS 2016*, DOI `10.1109/RTAS.2016.7461326`), which bridged Isabelle/HOL kernel invariants to binary loop bounds and infeasible paths; and for CompCert by Schommer et al. (*OASIcs WCET 2018*, DOI `10.4230/OASIcs.WCET.2018.8`), which preserved source-level flow annotations through CompCert down to AbsInt `aiT` without trusting unverified compiler optimizations.
  2. **Microarchitectural abstract interpretation (cache + pipeline + bus analysis):** Computes conservative per-basic-block cycle upper bounds over an explicit hardware model of the target core. On out-of-order superscalar processors exhibiting **timing anomalies** or **amplification**, local worst-case assumptions do not even compose additively, forcing either timing-compositional in-order cores (e.g., ARM Cortex-R, Tricore, Patmos, FlexPRET) or conservative state-splitting over microarchitectural states.
  3. **Implicit Path Enumeration Technique (IPET):** Solves an ILP over CFG edge counts + loop/infeasible-path constraints weighted by the microarchitectural block bounds.

#### 4.2 Storage-Channel Intransitive Noninterference vs. seL4 Time Protection

- **Storage-Channel Intransitive Noninterference (`seL4/l4v`, Murray et al., *IEEE S&P 2013*, DOI `10.1109/SP.2013.35`):** Proved machine-checked confidentiality and integrity directly on the seL4 C implementation (`~8.8k` LOC) using a static round-robin domain scheduler and polling device drivers. Crucially, the proof models **architectural state transitions only**—it explicitly assumes away microarchitectural covert and timing channels (L1/LLC caches, TLBs, branch predictors, execution ports, and domain-switch latency).
- **OS Time Protection (Ge, Yarom, Heiser, *APSys 2018* DOI `10.1145/3265723.3265724`; Ge, Yarom, Chothia, Heiser, *EuroSys 2019* DOI `10.1145/3302424.3303976`):** Demonstrates that preventing cross-domain timing channels requires the temporal dual of memory protection, enforcing two orthogonal hardware-software invariants:
  1. **Spatial partitioning of off-core / slow-to-flush shared state:** Partition the shared Last-Level Cache (LLC) via **page coloring** (or hardware way partitioning such as Intel CAT / Arm MPAM) across security domains—**including per-color kernel text/data clones** so even kernel execution during syscalls/ticks cannot induce cross-domain LLC conflicts.
  2. **Temporal partitioning of on-core private state (`reset_uarch`):** On every security-domain switch, deterministically reset all on-core microarchitectural history (L1I, L1D, BTB, BHT, RSB, TLB, prefetchers) and pad domain-switch latency to a history-independent constant. Ge et al. (*EuroSys 2019*) measured real x86 and Arm platforms and showed that **software-only flushes on COTS CPUs leave measurable residual covert channels** because commodity ISAs lack instructions to reset undocumented microarchitectural state (cache replacement metadata, MSHRs, prefetcher tables, pipeline buffers).
- **Hardware Contract Closure (`fence.t`, Wistoff et al., *IEEE Transactions on Computers 2023*, DOI `10.1109/TC.2022.3212636`):** Introduces an architectural temporal fence instruction (`fence.t`) on the open-source RISC-V CVA6 core that deterministically clears on-core microarchitectural state in hardware with `<1%` workload overhead, eliminating measurable on-core covert channels across seL4 domain switches—confirming that Rung `(d)` timing-channel freedom is fundamentally a **hardware-software co-design property**, not a pure software proof obligation.

---

### 5. Reusable Stage 0 → Stage 1 → Stage 2 Verification Honesty Ladder

`Basis: derived + execution`

To prevent verification toolchains and assurance receipts from over-claiming, every timing or confidentiality proof must be tagged with its exact rung `(a)`–`(d)` and corresponding assurance stage:

| Rung | Formal Property Name | What Is Actually Proved | Valid Engineering Claims | Forbidden Conflations (Strictly Unsound) | Required TCB & Hardware Assumptions | Assurance Stage Mapping |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **(a)** | **`ArchStepBound`** (MIR / ISA Step-Count / Fuel / Time Credits) | $\forall x.\; \text{retiredSteps}(P, x) \le B(\lvert x \rvert)$ | Termination, bounded loop iteration counts, algorithmic complexity, DoS / gas metering budgets, input flow facts for downstream WCET. | **NEVER** claim wall-clock / cycle WCET, hard real-time schedulability, or timing side-channel freedom. | MIR/ISA operational semantics; if proved at MIR only, requires compiler step-preservation or binary loop-bound re-validation. | **Stage 0** (with MIR caveat) → **Stage 1** (with explicit TCB accounting & binary step bound). |
| **(b)** | **`StorageNI`** (Storage-Channel Intransitive Noninterference) | $\forall s_1 \approx_{\text{pub}} s_2.\; \text{archState}_{\text{pub}}(\text{run}(P, s_1)) = \text{archState}_{\text{pub}}(\text{run}(P, s_2))$ | Architectural data confidentiality and isolation across security domains (e.g., `seL4/l4v` Murray et al. 2013). | **NEVER** claim timing-channel, cache-channel, or speculative side-channel freedom. | Architectural semantics + static/non-leaking scheduler; explicitly **assumes away** all timing & microarchitectural channels. | **Stage 1** (explicitly labeled *storage-channel only* in receipt). |
| **(c)** | **`PostLinkArchCT`** (Post-Link Architectural Constant-Time under `DIT`/`DOITM`/`Zkt`) | On **decoded linked ELF**: $\forall s_1 \approx_{\text{pub}} s_2.\; \text{ArchCtObs}(P_{\text{bin}}, s_1) = \text{ArchCtObs}(P_{\text{bin}}, s_2)$ (PC + mem-addr parity) $\;\land\;$ `AllOpcodesDitSafe` $\;\land\;$ `DITModeActive` | Single-core sequential constant-time resistance to branch, cache-address, `DIV`, and operand-latency timing attacks on the shipped binary. | **NEVER** claim MIR-only CT implies binary CT; **NEVER** claim real-time WCET, Spectre (`SCT`) immunity (unless upgraded to dual-label `SCT`), cross-domain timing isolation, or DMP/power/DVFS immunity. | Binary decoder + `CtProduct` verifier + hardware `PSTATE.DIT`/`DOITM`/`Zkt` silicon compliance + OS context-switch preservation of `DIT`/`DOITM` + non-DMP (or M3+ `DIT`). | **Stage 2** (shrinks compiler out of CT TCB via post-link verification; explicitly states hardware `DIT`/non-speculative boundary). |
| **(d)** | **`MicroarchWCET` / `TimeProtectedNI`** (Hardware-Modeled WCET & Partitioned Timing-Channel Freedom) | **WCET:** $\forall x, u_0 \in U_{\text{valid}}.\; \text{cycles}(P_{\text{bin}}, x, u_0) \le W_{\text{cycles}}$<br>**Timing-NI:** $\forall s_1 \approx_{\text{pub}} s_2.\; \text{cycles}(P_{\text{bin}}, s_1, u_{\text{reset}}) = \text{cycles}(P_{\text{bin}}, s_2, u_{\text{reset}})$ | Hard real-time deadline guarantees (`DO-178C` / `CAST-32A`); cross-domain covert timing-channel elimination across context switches. | **NEVER** transfer a single-core WCET bound to unpartitioned multicore COTS silicon; **NEVER** claim COTS software flushes equal hardware `fence.t` / `reset_uarch`. | Sound hardware pipeline/cache/bus model (`aiT`/`LLVMTA`) on timing-compositional core (for WCET); LLC spatial partitioning + kernel clones + hardware `reset_uarch` / `fence.t` (for cross-domain Timing-NI). | **Stage 2+** (requires dedicated microarchitectural hardware model / hardware-software Time Protection contract). |

**Stage 0 → Stage 1 → Stage 2 Receipt Discipline:**
- **Stage 0 (Prototype / MIR-only):** May report `ArchStepBound` or MIR algorithmic CT hints, **only** with a blunt caveat that LLVM lowering is unverified for timing, branches, loads, `DIV`, and spills.
- **Stage 1 (Audited TCB Accounting):** Distinguishes `ArchStepBound` `(a)` and `StorageNI` `(b)` explicitly in the machine-readable assurance receipt, forbidding any conflation with WCET or timing-channel NI, and enumerates LLVM and hardware timing assumptions as unverified TCB entries.
- **Stage 2 (Shrunk TCB / Post-Link & Hardware Contracts):** Eliminates `rustc`/LLVM from the constant-time TCB via post-link binary `CtProduct` verification `(c)` + `DIT`/`DOITM`/`Zkt` opcode allowlist + OS mode contract, and isolates microarchitectural WCET / cross-domain Time Protection `(d)` behind explicit hardware-model / `reset_uarch` obligations.

---

### 6. Mechanized Lean 4 (`v4.34.1`, `Type 0`) Separation and Upgrade Witness

`Basis: execution + derived` (`support/StepVsTimingWitness.lean`)

To make the honesty-ladder boundaries mechanically checkable, `support/StepVsTimingWitness.lean` encodes `Input`, `Opcode` (with `Opcode.isDitSafe` excluding `divVarTime` and `fpSubnormal`), `StepEvent`, `ArchCtObs`, `UarchState`, `stepCycles`, `traceCycles`, and the four rung predicates (`HasRetiredStepParity`, `SatisfiesStorageNI`, `SatisfiesPostLinkArchCT`, `SatisfiesCycleTimingNI`) in self-contained core Lean 4 (`Type 0`, zero imports, zero `sorry`). Five kernel-checked theorems establish both strict separations and the exact positive upgrade condition:

1. **`retired_step_parity_does_not_imply_wcet_or_timing_ni`:** Exhibits `progCacheLeak`, which retires exactly `3` instructions on every input (`HasRetiredStepParity`), yet takes `3` cycles (L1 hit at address `0`) vs. `42` cycles (L1 miss at address `64`) under `uarchLine0Hot`, refuting `SatisfiesCycleTimingNI` and any claim that retired-step parity bounds microarchitectural cycles.
2. **`storage_ni_and_step_parity_do_not_imply_cache_timing_ni`:** Proves `progCacheLeak` simultaneously satisfies `SatisfiesStorageNI` (`finalStorage x = x.pub + 1`) and `HasRetiredStepParity`, while violating both `SatisfiesPostLinkArchCT` and `SatisfiesCycleTimingNI`.
3. **`mir_ct_broken_by_single_trace_refining_lowering`:** Models `ct_wrap_mask_load_arms` via `progMirBranchless` (which satisfies `SatisfiesPostLinkArchCT`) and `progLlvmBroken` (which is functionally identical on all inputs, `∀ x, progLlvmBroken.finalStorage x = progMirBranchless.finalStorage x`, yet introduces a secret branch and conditional load), proving `¬ SatisfiesPostLinkArchCT progLlvmBroken`.
4. **`dit_enabled_without_allowlist_still_leaks_div`:** Proves `progDivUnderDit` satisfies `SatisfiesPostLinkArchCT` with `uarchLine0Hot.ditEnabled = true`, yet violates `AllOpcodesDitSafe` and `SatisfiesCycleTimingNI` (`4` cycles vs. `44` cycles), mechanizing the universal `DIV` exemption of `PSTATE.DIT` / `DOITM` / `Zkt`.
5. **`postlink_ct_under_dit_and_uarch_reset_implies_timing_ni`:** Proves constructively that `u.ditEnabled = true`, `SatisfiesPostLinkArchCT p`, and `AllOpcodesDitSafe p` jointly imply `SatisfiesCycleTimingNI u p` for any fixed/reset microarchitectural state `u`.

**Kernel verification record (`leanprover/lean4:v4.34.1`, exit code `0`, zero `sorry`):**
```text
'StepVsTimingHonestyLadder.retired_step_parity_does_not_imply_wcet_or_timing_ni' depends on axioms: [propext]
'StepVsTimingHonestyLadder.storage_ni_and_step_parity_do_not_imply_cache_timing_ni' depends on axioms: [propext]
'StepVsTimingHonestyLadder.mir_ct_broken_by_single_trace_refining_lowering' depends on axioms: [propext]
'StepVsTimingHonestyLadder.dit_enabled_without_allowlist_still_leaks_div' depends on axioms: [propext]
'StepVsTimingHonestyLadder.postlink_ct_under_dit_and_uarch_reset_implies_timing_ni' depends on axioms: [propext]
```

## Boundaries

- **Known not to apply:**
  - Passing MIR-level constant-time checks or compiling cleanly at `-C opt-level=3` does **not** establish constant-time machine code at `-C opt-level=2`, `-Os`, or `-Oz`, nor across target architectures (proven empirically by `ct_lut_linear_scan_16`, `ct_wrap_mask_load_arms`, `ct_select_unpred_struct`, `ct_select_unpred_u64` on `riscv64gc`, and `ct_const_div_kyberslash` at `-Oz`).
  - `core::hint::select_unpredictable` is **not** a cryptographic constant-time guarantee for multi-word aggregates (emits secret-addressed pointer loads on `x86_64`, `aarch64`, and `riscv64`) or on targets without conditional-move/conditional-zero instructions (emits `bnez` on base `riscv64gc`).
  - Hardware `PSTATE.DIT = 1`, Intel `DOITM = 1`, and RISC-V `Zkt` do **not** make `DIV`/`IDIV`/`UDIV`/`SDIV`/`REM` or IEEE-754 floating-point subnormal operations constant-time, and do **not** substitute for speculative execution defenses (`SCT`) or cross-domain Time Protection (`reset_uarch` + LLC coloring).
  - Architectural retired-instruction bounds (`Rung (a)`) do **not** imply microarchitectural WCET (`Rung (d)`), and storage-channel noninterference (`Rung (b)`) does **not** imply timing- or cache-channel noninterference (`Rungs (c)–(d)`).
- **Not examined:**
  - Native end-to-end `rustc --target=aarch64-unknown-none` and `--target=riscv64gc-unknown-none-elf` runs (target `libcore` sysroots were not installed; AArch64 and RISC-V 64 results were obtained via `rustc 1.102.0-nightly --emit=llvm-ir` lowered through `llc 21.1.8`, while native `rustc` LLVM `23.1.5` backend runs were executed on `x86_64-unknown-linux-gnu` and `thumbv7m-none-eabi`).
  - Dynamic microarchitectural hardware cycle measurements on physical silicon (`rdtsc`/`cntvct_el0`, `dudect`, TVLA power/EM traces, or physical `PSTATE.DIT`/`DOITM` MSR toggling).
  - Cranelift (`rustc_codegen_cranelift`) and GCC (`rustc_codegen_gcc`) Rust backends.
  - Multicore memory-bus / DRAM / coherence-directory WCET interference models (covered separately in `multicore-realtime-interference-cache-partitioning-and-mrsp-locking`) and full speculative-execution leakage contracts (covered in `transient-execution-spectre-v1-bounds-masking-and-page-table-walk-cache-leakage`).
- **Unknown:**
  - Whether future LLVM releases will introduce a first-class `secret` SSA type or guaranteed constant-time select intrinsic preserved through `InstCombine`, `SelectOptimize`, `X86CmovConversion`, `SimplifyCFG`, and all RISC-V/AArch64/x86-64 backends.
  - Whether `rustc`'s target-native middle-end heuristics on `aarch64-unknown-linux-gnu` (using AArch64 `TargetTransformInfo` rather than `x86_64` TTI before `llc`) trigger additional `SelectOptimize` branch conversions on `ct_lut_linear_scan_16` or `ct_wrap_mask_load_arms`.
- **Unsupported:**
  - Standard Rust, C23, and LLVM IR provide no normative constant-time preservation guarantee across optimizing compilation.
  - Unprivileged x86-64 user-space code cannot directly write `IA32_UARCH_MISC_CTL[0]` (`DOITM`), and standard RISC-V `F`/`D` provides no architectural hardware flush-to-zero (`FTZ`/`FZ`) bit in `fcsr`.
  - Commodity x86-64 and Arm CPUs lack an architectural `fence.t` / `reset_uarch` instruction capable of deterministically clearing all undocumented on-core microarchitectural state on domain switch.

## Evidence

### 1. Local Empirical Codegen Probes (Observed `2026-11-22`)

- **Host environment:** Linux `x86_64-unknown-linux-gnu`; `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` (`commit-hash: 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `LLVM version: 23.1.5`); `Debian LLVM llc 21.1.8`.
- **Preserved support artifacts:**
  - `support/ct_idioms.rs`: Self-contained `#![no_std]` Rust crate defining 27 `extern "C"` constant-time probe functions across all 7 idiom families.
  - `support/probe_ct_codegen.py`: Reproducible Python 3 driver compiling `support/ct_idioms.rs` across 16 configurations (`rustc_x86_64_O{2,3,s,z}`, `rustc_thumbv7m_O{2,3,z}`, `llc_aarch64_O{2,3,z}`, `llc_riscv64gc_O{2,3,z}`, `llc_riscv64_zicond_O{2,3,z}`) and classifying emitted branches, jump tables, `.rodata` LUTs, `cmov`/`csel`/`czero`, `div`/`udiv`/`divu`, stack/red-zone spills, and FP ops.
  - `support/probe_ct_codegen_results.json`: Full recorded output (`16 × 27` function disassemblies and classifications) from `2026-11-22`.

### 2. Mechanized Lean 4 Honesty-Ladder Witness (Observed `2026-11-22`)

- **Toolchain:** `leanprover/lean4:v4.34.1` (standalone `Type 0` file, zero external dependencies, exit code `0`, zero `sorry`, `#print axioms` strictly `[propext]` on all five theorems).
- **Preserved artifact:** `support/StepVsTimingWitness.lean` (5 theorems: `retired_step_parity_does_not_imply_wcet_or_timing_ni`, `storage_ni_and_step_parity_do_not_imply_cache_timing_ni`, `mir_ct_broken_by_single_trace_refining_lowering`, `dit_enabled_without_allowlist_still_leaks_div`, `postlink_ct_under_dit_and_uarch_reset_implies_timing_ni`).

### 3. Normative Specifications and Peer-Reviewed Primary Literature

- **Arm Architecture Reference Manual for A-profile architecture (`DDI 0487`):** `FEAT_DIT` (`PSTATE.DIT`, Armv8.4-A mandatory, EL0-writable, `SPSR_ELx` preservation, `UDIV`/`SDIV` exclusion) and `FPCR.FZ` / `FPCR.FZ16`.
- **Intel Corporation:** *Data Operand Independent Timing ISA Guidance* (`ID 768873`) and *Documented DOIT Instructions* (`ID 759656`, 594 Table-1 mnemonics; `IA32_ARCH_CAPABILITIES` MSR `0x10A` bit 12; `IA32_UARCH_MISC_CTL` MSR `0x1B01` bit 0; `CPUID.07H.02H:EDX[5]` `MCDT_NO`).
- **RISC-V International:** *RISC-V Cryptography Extensions Volume I: Scalar & Entropy Source Instructions* (`v1.0.1`), `Zkt` Data-Independent Execution Latency specification (explicitly excluding `div`/`rem` and floating-point `F`/`D`/`Q`).
- **Toby Murray et al.**, *"seL4: From General Purpose to a Proof of Information Flow Enforcement"*, IEEE S&P 2013, pp. 415–429, DOI `10.1109/SP.2013.35`.
- **Qian Ge, Yuval Yarom, Gernot Heiser**, *"No Security Without Time Protection: We Need a New Hardware-Software Contract"*, APSys 2018, DOI `10.1145/3265723.3265724`.
- **Qian Ge, Yuval Yarom, Tom Chothia, Gernot Heiser**, *"Time Protection: the Missing OS Abstraction"*, EuroSys 2019, Art. 1, pp. 1–17, DOI `10.1145/3302424.3303976`.
- **Nils Wistoff, Moritz Schneider, Frank K. Gürkaynak, Gernot Heiser, Luca Benini**, *"Systematic Prevention of On-Core Timing Channels by Full Temporal Partitioning"*, IEEE Transactions on Computers, Vol. 72, No. 5, pp. 1420–1430 (2023), DOI `10.1109/TC.2022.3212636` (arXiv `2202.12029`).
- **Reinhard Wilhelm et al.**, *"The Worst-Case Execution-Time Problem—Overview of Methods and Survey of Tools"*, ACM TECS, Vol. 7, No. 3, Art. 36 (2008), DOI `10.1145/1347375.1347389`.
- **Bernard Blackham, Yao Shi, Sudipta Chattopadhyay, Abhik Roychoudhury, Gernot Heiser**, *"Timing Analysis of a Protected Operating System Kernel"*, IEEE RTSS 2011, pp. 339–348, DOI `10.1109/RTSS.2011.38`.
- **Thomas Sewell, Felix Kam, Gernot Heiser**, *"Complete, High-Assurance Determination of Loop Bounds and Infeasible Paths for WCET Analysis"*, IEEE RTAS 2016, DOI `10.1109/RTAS.2016.7461326`.
- **Bernhard Schommer, Christoph Cullmann, Gernot Gebhard, Xavier Leroy, Michael Schmidt, Simon Wegener**, *"Embedded Program Annotations for WCET Analysis"*, OASIcs WCET 2018, DOI `10.4230/OASIcs.WCET.2018.8`.
- **Alejandro Gómez-Londoño, Johannes Åman Pohjola, Hira Taqdees Syeda, Magnus O. Myreen, Yong Kiam Tan**, *"Do You Have Space for Dessert? A Verified Space Cost Semantics for CakeML Programs"*, PACMPL OOPSLA 2020, DOI `10.1145/3428272`.

## Revalidation

1. **Re-run the empirical `rustc`/LLVM constant-time codegen probe on any newer `rustc` or `llc` release:**
   ```bash
   python3 support/probe_ct_codegen.py
   ```
   Inspect `support/probe_ct_codegen_results.json` specifically for:
   - `ct_lut_linear_scan_16` under `rustc_x86_64_O2` and `rustc_x86_64_Oz` (whether `SelectOptimize` still emits secret `jne` branches);
   - `ct_select_unpred_struct` (whether aggregate `select_unpredictable` still emits a pointer `cmov`/`csel` followed by a secret-addressed load);
   - `ct_wrap_mask_load_arms` and `ct_u64_{lt,eq}_bitmath_load_select` (whether `InstCombine` + `SelectOptimize` still introduce `jne`/`js`/`je`);
   - `ct_select_unpred_u64` on `llc_riscv64gc_O2` vs. `llc_riscv64_zicond_O2`;
   - `ct_const_div_kyberslash` at `-Oz` (whether hardware `divl`/`udiv`/`divuw` is still emitted).
   If target-native `aarch64-unknown-none` or `riscv64gc-unknown-none-elf` `rustup` targets are installed, invoke `rustc --crate-type=lib --edition=2024 --target=<triple> -C opt-level={2,3,z} -C panic=abort --emit=asm support/ct_idioms.rs` directly to close the target-native TTI boundary noted under **Boundaries**.
2. **Re-verify the Lean 4 honesty-ladder separation and upgrade theorems:**
   ```bash
   elan run leanprover/lean4:v4.34.1 lean support/StepVsTimingWitness.lean
   ```
   Confirm exit code `0`, zero `sorry`, and clean `#print axioms` output across all five theorems.
3. **Re-check hardware `DIT`/`DOITM`/`Zkt` opcode allowlists** whenever a new ISA revision (Armv9.x, newer Intel DOIT Table 1 revision, or RISC-V floating-point/vector `Zkt` extensions such as `Zvkt`) is targeted; do not infer inclusion of `DIV`/`REM` or FP instructions without checking the updated normative table.
