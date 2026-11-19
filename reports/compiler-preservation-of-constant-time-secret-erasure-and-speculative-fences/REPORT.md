# Compiler Preservation of Constant-Time, Secret Erasure, and Speculative Fences

## Summary

Standard optimizing compilers (GCC, Clang/LLVM, `rustc`) enforce only **single-trace functional refinement** over an abstract machine that treats execution timing, cache-line footprint, speculative execution, and post-lifetime memory or register contents as unobservable. Cryptographic **constant-time (CT)**, **speculative constant-time (SCT)**, and **secret erasure** are **2-safety relational hyperproperties** and **physical-state cleanup invariants** that single-trace functional equivalence does *not* preserve. Direct source inspection of LLVM (`llvm/llvm-project` `1780833aa0f119a425d7f993aaac29d03cb04da6`) and live compilation probes on `GCC 15.2.0` and `rustc 1.98.0-nightly` (`LLVM 22.1.6`) confirm six concrete compiler-induced security regressions:

1. **Branch reintroduction (`SelectOptimize` / `CodeGenPrepare` / `BypassSlowDivision`):** LLVM converts branchless `select` operations into secret-dependent conditional jumps when target heuristics judge predictable selects expensive (`isPredictableSelectExpensive()`) or an operand cold/expensive, and LLVM's `BypassSlowDivision` injects an implicit operand-dependent branch (`shr $0x20; je`) in front of 64-bit `DIV` to fast-path 32-bit values.
2. **Secret-indexed lookup-table synthesis (`SimplifyCFG::switchToLookupTable`):** Branchless or branching `match`/`switch` chains over a secret nibble are compiled directly into a `.rodata` memory lookup (`mov (%rax,%rdi,4),%eax`), creating a cache-line timing channel absent from source.
3. **Dead Store Elimination (DSE) and register/SIMD residue:** `memset`/`slice::fill(0)` on dead stack buffers is completely elided by DSE. Even when preserved via `explicit_bzero` or `ptr::write_volatile`, SROA/vectorization can keep secret key bytes resident in `%xmm0`/`%xmm1` while zeroing an untouched stack slot, and GCC `-fzero-call-used-regs=used` skips zeroing on sibling tail-call jumps (`jmp`). Even `core::hint::black_box` used in `subtle` spills the secret choice bit into the un-erased x86-64 red zone (`-0x1(%rsp)`).
4. **Optimization-flag-dependent variable-latency division (KyberSlash pattern):** Identical constant-divisor modular reductions (`(2a + 3329) / 6658`) compile to constant-time magic multiplication under `GCC -O2` and `rustc -O`, yet lower to variable-latency hardware `div %ecx` under `GCC -Os` and `rustc -C opt-level=z`.
5. **Speculative-fence (`LFENCE`) hoisting and load elimination:** Extended GCC inline assembly `__asm__ volatile("lfence" : : )` lacking a `"memory"` clobber lets `GCC 15.2.0 -O2` hoist `movzbl (%rdi),%edx` completely *above* both the bounds-check branch and `lfence`; conversely, under `rustc -O`, LLVM's unroller/GVN reuses loads from `readonly` references (`&[u8; 256]`) across subsequent `core::arch::x86_64::_mm_lfence()` calls.
6. **Verified preservation vs. post-compile verification:** Closing these gaps requires either (a) a formally verified CT/SCT-preserving compiler (**CompCert-CT** POPL 2020, **Jasmin** with Coq-verified SLH lowering and stack zeroization, or **CompCert-ct** ITP 2025 PCFL linearization), (b) secret-aware DSL lowering shielded by opaque inline assembly (**FaCT**), or (c) **binary-level relational symbolic execution** (**Binsec/Rel** `checkct`), which verifies CT (branches, memory, variable-latency `MUL`/`DIV`) *and* whole-memory secret erasure (`!secret_seeker`) directly on the linked machine code.

## Applicability

This report analyzes why mainstream optimizing compilers destroy constant-time, secret-erasure, and speculative-fence invariants, and compares the formal semantics, pass pipelines, and verification boundaries of five mitigation architectures. The subjects listed in `REPORT.json` relate as follows:

- **Mainstream optimizing compiler passes (`llvm/llvm-project` `1780833aa0f119a425d7f993aaac29d03cb04da6`, `GCC 15.2.0`, `rustc 1.98.0-nightly` / `LLVM 22.1.6`):** Source inspection of LLVM middle-end and backend passes (`SelectOptimize.cpp`, `CodeGenPrepare.cpp`, `DeadStoreElimination.cpp`, `SimplifyCFG.cpp`, `PrologEpilogInserter.cpp`, `X86FrameLowering.cpp`, `X86SpeculativeLoadHardening.cpp`) is combined with reproducible x86-64 execution probes comparing `GCC 15.2.0` (`-O2`, `-Os`, `-fzero-call-used-regs=used`) and `rustc 1.98.0` (`-O`, `-C opt-level=s`, `-C opt-level=z`).
- **Source-level library & standard mitigations (`ISO/IEC 9899:2024` §7.26.6.2, `rust-lang/rust` `b0b600668bb9b4a897e2299b0a44289d42276545`, `RustCrypto/utils` `77d1a3e6c2e8c28f49189258abb5d4405c0f1330`, `dalek-cryptography/subtle` `369e7463e85921377a5f2df80aabcbbc6d57a930`):** Direct inspection of `core::hint::{select_unpredictable, black_box}`, `zeroize`'s volatile/assembly optimization barriers, and `subtle`'s `Choice`/`ConditionallySelectable` barrier design.
- **Verified constant-time and speculative constant-time compilers (`AbsInt/CompCert` `2685140bf72c959446981fb99b5e44a8975021bc`, Barthe et al. POPL 2020 `10.1145/3371075`, `knothed/CompCert-ct` `2d1369a4888cff6fd5fd29f28a059e9cf72b1a08` ITP 2025 `10.4230/LIPIcs.ITP.2025.31`, `jasmin-lang/jasmin` `5741d17e3134f5b3b110e5e53494704d6d54f7c7`, Arranz-Olmos et al. POPL 2025 `10.1145/3704880`):** Distinguishes CT *preservation* (CompCert-CT POPL 2020, Jasmin), verified secret control-flow *elimination* (Knothe & Bringmann ITP 2025), and *speculative* CT preservation + verified stack zeroization (Jasmin + POPL 2025).
- **Secret-typed DSL & post-compile binary relational verification (`PLSysSec/fact` `b3daa03f48447285117f426129dbf539a7f32f4a`, `binsec/binsec` `9749bd8aed7ee0a27959158b1e53e8789cb0e5ab`):** Contrasts FaCT's front-end predication + inline-asm `cmov` shielding against BINSEC's post-compile `checkct` relational symbolic execution (RelSE) and secret-erasure (`Se_check`) verification directly over binaries.

Concrete assembly sequences in execution probes apply strictly to `GCC 15.2.0` and `rustc 1.98.0-nightly` (`LLVM 22.1.6`) targeting `x86_64-unknown-linux-gnu`. Because compiler optimization heuristics shift across versions, architectures (e.g., AArch64 `csel`, RISC-V `Zicond`), and build flags (`-O2` vs `-Os`/`-Oz`, PGO, LTO), any unverified compiler-barrier idiom must be treated as brittle unless verified post-compile.

## Findings

### 1. Why Single-Trace Compiler Correctness Fails for Security Hyperproperties

**Basis:** normative + derived

Standard optimizing compilers prove (or empirically test) **single-trace behavioral refinement**: for every defined execution of source program $P$, the compiled binary $P'$ produces the same sequence of architecturally observable I/O and volatile side effects. Security properties for cryptographic implementations instead require **relational 2-safety hyperproperties** and **microarchitectural/physical cleanup guarantees**:

1. **Sequential Cryptographic Constant-Time (CT):** Given a leakage function $\mathcal{L}(P, \sigma_{\text{pub}}, \sigma_{\text{sec}})$ recording every program counter (branch target), memory access address, and variable-latency instruction operand (`DIV`/`REM`, early-exit `MUL`, subnormal FP):
   $$\forall \sigma_{\text{pub}}, \sigma_{\text{sec}}^1, \sigma_{\text{sec}}^2.\quad \mathcal{L}(P, \sigma_{\text{pub}}, \sigma_{\text{sec}}^1) = \mathcal{L}(P, \sigma_{\text{pub}}, \sigma_{\text{sec}}^2)$$
2. **Speculative Constant-Time (SCT):** Extends $\mathcal{L}$ to a speculative operational semantics $\mathcal{L}_{\text{spec}}(P, \sigma_{\text{pub}}, \sigma_{\text{sec}}, D)$ parameterized by attacker-controlled microarchitectural directives $D$ (branch misprediction PHT, store-to-load bypass STL/SSB, RSB) up to a speculation window.
3. **Secret Erasure (Post-Execution Non-Interference):** At function return (or explicit declassification/drop boundary), *no* residual physical storage—stack frame, red zone, heap allocation, general-purpose registers, vector/SIMD registers (`XMM`/`YMM`/`ZMM`), or flags—may depend on $\sigma_{\text{sec}}$:
   $$\forall \sigma_{\text{pub}}, \sigma_{\text{sec}}^1, \sigma_{\text{sec}}^2, \ell \in \text{State}_{\text{exit}} \setminus \text{Out}.\quad \text{eval}(P, \sigma_{\text{pub}}, \sigma_{\text{sec}}^1)[\ell] = \text{eval}(P, \sigma_{\text{pub}}, \sigma_{\text{sec}}^2)[\ell]$$

Because $\mathcal{L}$, $\mathcal{L}_{\text{spec}}$, and dead storage slots are *invisible* in C (`ISO/IEC 9899`), C++, Rust, and LLVM IR abstract machines, **every optimizing transformation below is 100% legal under language semantics while silently destroying security**.

---

### 2. Concrete Optimizing Compiler Passes That Destroy CT, Secret Erasure, and Speculative Fences

#### 2.1 Branch Reintroduction: `SelectOptimize`, `CodeGenPrepare`, and `BypassSlowDivision`
**Basis:** source + execution

Even when programmers avoid `if` statements over secrets and write branchless ternary/masking code that lowers to LLVM IR `select`, LLVM contains multiple passes specifically designed to convert `select` instructions **back into conditional branches**:

- **`SelectOptimize` (`llvm/lib/CodeGen/SelectOptimize.cpp`, `1780833aa0f119a425d7f993aaac29d03cb04da6`):** Runs late in the CodeGen IR pipeline (L70–83, L277–290, L1023–1038). It converts select groups into branches whenever either:
  - `isSelectHighlyPredictable(SI) && TLI->isPredictableSelectExpensive()` (L1024–1028, driven by PGO profiles or static branch-weight heuristics); or
  - `hasExpensiveColdOperand(ASI)` (L1033–1037, e.g., when one arm involves a load, multiply, or longer dependency chain); or
  - loop-carried critical-path analysis favors branching (`NumSelectConvertedLoop`, L60).
- **`CodeGenPrepare::optimizeSelectInst` (`llvm/lib/CodeGen/CodeGenPrepare.cpp` L7381–7395, L7508–7515):** Legacy fallback when `SelectOptimize` is disabled, using `TLI->isPredictableSelectExpensive()` and `extractBranchWeights(*SI, TrueWeight, FalseWeight)` to lower `select` to branches.

**Live Execution Probe 2B (`rustc 1.98.0` / `LLVM 22.1.6 -O` & `GCC 15.2.0 -O2`):**
1. **Load sinking + branch introduction (`rust_select_exp_branch`):** In Rust source `let va = *a; let vb = *b; if cond { va.wrapping_mul(3).wrapping_add(1) } else { vb }`, both loads precede the conditional. Under `rustc -O`, LLVM sunk *both* loads behind a conditional branch:
   ```asm
   0: test   %edi,%edi
   2: je     f <rust_select_exp_branch+0xf>
   4: mov    (%rsi),%rax
   7: lea    (%rax,%rax,2),%rax
   b: inc    %rax
   e: ret
   f: mov    (%rdx),%rax
   12: ret
   ```
   `GCC 15.2.0 -O2` exhibited the identical transformation on `gcc_select_to_branch` (`test %edi,%edi; je 40; ... imul (%rsi),%rax ...` vs `mov (%rdx),%rax`), and LLVM likewise emitted a branch (`test $0x1,%dil; jne 1b`) for pure-arithmetic `rust_branchless_idiom` (`if (secret_bit & 1) != 0 { a*C1 + b } else { b*C2 + a }`).
2. **Compiler-synthesized operand-dependent branch (`BypassSlowDivision` in `rust_div_select`):** For 64-bit unsigned division `a / (d | 1)` with *no branch on `a` or `d` in source*, `rustc -O` (`LLVM 22.1.6`) emitted:
   ```asm
   6:  mov    %rsi,%rdx
   9:  or     %rcx,%rdx
   c:  or     $0x1,%rcx
   10: shr    $0x20,%rdx
   14: je     24 <rust_div_select+0x24>   ; <-- secret-dependent branch on high 32 bits of (a | d)!
   16: xor    %edx,%edx
   18: div    %rcx                        ; 64-bit DIV
   ...
   24: xor    %edx,%edx
   26: div    %ecx                        ; 32-bit DIV fast path
   ```
   This leaks whether `(a | d) < 2^32` via both control flow (branch predictor / PC trace) and instruction timing (32-bit vs 64-bit `DIV` latency), even if a programmer assumed hardware `DIV` was their only concern.

#### 2.2 Secret-Indexed Lookup-Table Synthesis (`SimplifyCFG::switchToLookupTable`)
**Basis:** source + execution

In `llvm/lib/Transforms/Utils/SimplifyCFG.cpp` (`shouldBuildLookupTable` L7520–7535, `switchToLookupTable` L7775–7790), LLVM eliminates multi-way switches/matches that map dense integer keys to constants by generating an anonymous `.rodata` static array and replacing control flow with a single memory load indexed by the switch discriminant.

**Live Execution Probe 2B (`rust_switch_to_lut`, `rustc 1.98.0` / `LLVM 22.1.6 -O`):** Matching `secret_nibble & 7` across 8 constant `u32` arms compiled to:
```asm
0: and    $0x7,%edi
3: lea    0x0(%rip),%rax       # .rodata lookup table
a: mov    (%rax,%rdi,4),%eax   # secret-indexed memory load!
d: ret
```
Even if the source switch was written to avoid memory accesses (or to normalize control flow via a 3-bit table), LLVM replaces it with a **secret-indexed memory load** vulnerable to cache-timing attacks (`Flush+Reload`, `Prime+Probe`).

#### 2.3 Dead Store Elimination (DSE), SROA Stack Elision, and Register/Red-Zone Residue
**Basis:** normative + source + execution

In `llvm/lib/Transforms/Scalar/DeadStoreElimination.cpp` (L2099–2111), LLVM uses `MemorySSA` to delete any removable non-volatile write (`isRemovable(DefI)`) to a single underlying stack/heap object whose lifetime ends before any subsequent read (`EliminateDeadStores` at function exit or before `free`). As documented in Simon, Chisnall, and Anderson (*IEEE EuroS&P 2018*, DOI `10.1109/EuroSP.2018.00009`), standard memory-zeroing primitives still fail to eliminate **compiler-created copies in registers, SIMD lanes, and stack spill slots**.

**Live Execution Probe 2A (`GCC 15.2.0 -O2` and `rustc 1.98.0 / LLVM 22.1.6 -O`):**

| Function / Mitigation | Observed Emitted Machine Code (`objdump -d`) | Memory Buffer Wiped? | Secret Residue Remaining at Exit |
| :--- | :--- | :--- | :--- |
| C `memset(key, 0, 32)` (`GCC -O2`) | Stack array `key` and `memset` **completely deleted**; `jmp consume` tail call | N/A (elided to SIMD) | **32B key derivatives live in `%xmm0`, `%xmm1`** |
| C `explicit_bzero(key, 32)` (`GCC -O2`) | `movaps %xmm0,0x10(%rsp); movaps %xmm1,(%rsp); ... call explicit_bzero; ret` | Yes (stack wiped) | **Secret bytes still live in `%xmm0`, `%xmm1`** |
| C `explicit_bzero` + **`-fzero-call-used-regs=used`** (`GCC -O2`) | Adds `xor %esi,%esi; xor %edi,%edi; pxor %xmm0,%xmm0; pxor %xmm1,%xmm1; ret` | Yes (stack + used regs wiped) | Cleared before `ret` *(Note: sibling tail-call `jmp` in `wipe_naive_memset` emitted **zero** `pxor` wipes!)* |
| Rust `key.fill(0)` (`rustc -O`) | `key` and `fill(0)` **completely deleted**; `jmp *sink_u8` | N/A (elided to SIMD) | **Secret bytes live in `%xmm0`, `%xmm1`** |
| Rust `write_volatile` + `compiler_fence(SeqCst)` (`rustc -O`) | Loads `*src` straight into `%xmm0`/`%xmm1` (**never writes `key` to stack!**), calls `sink_u8`, then emits 32× `movb $0x0, 0x8..0x27(%rsp)` to an **unused stack slot**! | Writes zeroes to unpopulated stack slot | **Actual secret bytes untouched in `%xmm0`, `%xmm1`!** |
| Rust `subtle`-style `black_box(choice & 1)` (`rustc -O`) | `and $0x1,%dil; mov %dil,-0x1(%rsp); movzbl -0x1(%rsp),%eax; neg %rax; ...` | Branchless mask preserved | **Secret choice bit spilled into red zone `-0x1(%rsp)` and never zeroed!** |

That `rust_wipe_volatile` disassembly is particularly instructive: LLVM's SROA/GVN observed that the loop only read `*src` (via `key`), eliminated the initial copy into stack `key`, retained the 32 secret bytes in `%xmm0`/`%xmm1`, and dutifully obeyed `write_volatile` by emitting 32 byte-wide zero stores into stack memory that never held the key.

**Standards and compiler register-wiping mitigations (`Basis: normative + source`):**
- **C23 `memset_explicit` (`ISO/IEC 9899:2024` §7.26.6.2):** Standardizes non-elidable memory erasure (`void *memset_explicit(void *s, int c, size_t n)`), replacing non-portable `explicit_bzero` / `SecureZeroMemory` / Annex K `memset_s`. Like `explicit_bzero`, it governs *only* the pointed-to memory object, not registers or compiler-synthesized spills.
- **Rust `zeroize` (`RustCrypto/utils` `77d1a3e6c2e8c28f49189258abb5d4405c0f1330`):** In `zeroize/src/bulk.rs` (L7–60), on architectures with inline assembly (`x86_64`, `aarch64`, `riscv64`, etc.), `fill_slice` and `zeroize_byte_ptr` perform fast `dst.fill(src)` / `ptr::write_bytes` followed by an assembly `optimization_barrier` (falling back to chunked `ptr::write_volatile` on other targets), and `zeroize/src/x86.rs` (L10–25) implements `Zeroize` for `__m128`/`__m256`/`__m512` via `volatile_write`—yet as `zeroize/src/lib.rs` (L501–505) explicitly warns for `Vec`, prior heap reallocations, stack moves, and compiler register spills remain outside library-level visibility.
- **Compiler register wiping (`ZeroCallUsedRegs`):** Implemented in LLVM inside `PrologEpilogInserter.cpp` (`PEIImpl::insertZeroCallUsedRegs`, L1209–1351 supporting `skip`, `used-gpr-arg`, `used-gpr`, `used-arg`, `used`, `all-gpr-arg`, `all-gpr`, `all-arg`, `all`) and lowered per target in `X86FrameLowering.cpp` (`emitZeroCallUsedRegs`, L643), matching GCC's `-fzero-call-used-regs=<choice>` / `__attribute__((zero_call_used_regs(...)))`. However, it only zeroes caller-saved registers at function return—not callee-saved registers spilled to the stack frame, not stack spill slots, and (as observed above in `GCC 15.2.0`) **not** sibling tail-call exits!

#### 2.4 Variable-Latency Hardware Instructions: KyberSlash (`DIV`) and Subnormal Floats
**Basis:** normative + documentation + execution

- **KyberSlash (Bernstein et al., *IACR TCHES 2025*, Vol. 2025, Issue 2, pp. 209–234, DOI `10.46586/tches.v2025.i2.209-234`, ePrint `2024/1049`):** Several reference and production ML-KEM/Kyber implementations computed secret-dependent coefficient compression via C integer division by a compile-time constant (`(2 * t + 3329) / 6658` or `/ 3329`), assuming compilers always strength-reduce constant division to constant-time multiplication. In practice, compilers emit variable-latency hardware `DIV`/`IDIV`/`UDIV`/`SDIV` under size optimization (`-Os`/`-Oz`), older/embedded targets, or non-inlined parameters—enabling full secret-key recovery from timing differences.
- **Live Execution Probe 2C (`GCC 15.2.0` & `rustc 1.98.0 / LLVM 22.1.6`):** Compiling the exact constant-divisor expression `(a * 2 + 3329) / 6658`:
  - **`GCC 15.2.0 -O2` and `rustc -O` / `-C opt-level=s`:** Lowered to constant-time magic multiplication (`mov $0x9d7dbb41,%edx; shr $1,%eax; imul %rdx,%rax; shr $0x2b,%rax`).
  - **`GCC 15.2.0 -Os` AND `rustc -C opt-level=z`:** Both lowered the exact same source code to variable-latency hardware division:
    ```asm
    0: lea    0xd01(,%rdi,2),%eax
    7: mov    $0x1a02,%ecx
    c: xor    %edx,%edx
    e: div    %ecx            ; <-- operand-dependent latency (KyberSlash)!
    10: ret
    ```
- **Floating-point subnormals (Andrysco et al., *IEEE S&P 2015*, DOI `10.1109/SP.2015.44`):** IEEE 754 floating-point arithmetic (`addsd`/`mulsd`/`divsd`) suffers 10×–100× microcode-assist slowdowns on x86/ARM whenever an operand or intermediate result becomes subnormal (denormal), unless flush-to-zero (`FTZ`) and denormals-are-zero (`DAZ`) modes are forced or integer arithmetic is used. Similarly, embedded cores such as ARM Cortex-M3 implement early-termination variable-latency integer `UMULL`/`SMULL` (which is why BINSEC `checkct` exposes an explicit `check_mult` option alongside `check_dividend` and `check_divisor`).

#### 2.5 Speculative-Fence Destruction and Speculative Load Hardening (SLH)
**Basis:** source + execution + documentation

Speculative execution defenses (Spectre-v1 PHT bounds-check bypass) rely either on serializing fences (`LFENCE` on x86-64, `CSDB` on AArch64) or data-dependency masking (**Speculative Load Hardening**, SLH; `llvm/lib/Target/X86/X86SpeculativeLoadHardening.cpp`). Mainstream compilers undermine manual defenses in three distinct ways:

1. **Load hoisting across `LFENCE` when memory clobbers are omitted (`Basis: execution`, `GCC 15.2.0 -O2`):**
   Comparing extended inline assembly `__asm__ volatile("lfence" : : )` (missing `"memory"` clobber) vs `__asm__ volatile("lfence" : : : "memory")` inside `if (cond) { lfence; return arr[0] + 1; } else { return arr[0] + 2; }`:
   ```asm
   ; WITHOUT "memory" clobber (gcc_extended_asm_nomem):
   0:  movzbl (%rdi),%edx          ; <-- HOISTED ABOVE BRANCH AND ABOVE LFENCE!
   3:  lea    0x2(%rdx),%eax
   6:  test   %esi,%esi
   8:  je     10
   a:  lfence                      ; <-- protects only register arithmetic!
   d:  lea    0x1(%rdx),%eax
   10: ret

   ; WITH "memory" clobber (gcc_extended_asm_mem):
   20: test   %esi,%esi
   22: je     30
   24: lfence
   27: movzbl (%rdi),%eax          ; <-- pinned strictly after LFENCE
   2a: add    $0x1,%eax
   2d: ret
   ```
   *(Subtlety observed empirically: GCC **basic** asm `__asm__ volatile("lfence")` with no colons implicitly clobbers memory and did not hoist, whereas **extended** asm with colons `: :` and no `"memory"` clobber did hoist.)*
2. **Load elimination/reuse across `_mm_lfence()` on `readonly` references (`Basis: execution`, `rustc 1.98.0 / LLVM 22.1.6 -O`):** In `hoist_uncond_proper` looping `n` times over `_mm_lfence(); acc += arr[idx & 255]` where `arr: &[u8; 256]` is a shared immutable reference (`noalias readonly`), LLVM 22.1.6 unrolled the loop 4×, emitted 4 `lfence` instructions, and **eliminated 3 of the 4 loads** (reusing `%r8d` across three intervening `lfence` barriers) because `llvm.x86.sse2.lfence` cannot mutate `readonly` memory in LLVM's alias model.
3. **Why SLH must run as a late backend pass (`X86SpeculativeLoadHardening.cpp` L132–168, L346–485):** LLVM's `-mspeculative-load-hardening` operates on `MachineFunction` MIR (`tracePredStateThroughCFG`, `hardenLoadAddr`, `hardenPostLoad`, encoding misspeculation predicate state via `CMOV` and hardening interprocedurally across calls/returns via stack-pointer tainting or `LFENCE` at function entry, L429–433). Even then, automated minimal fence/SLH placement requires formal flow-sensitive taint analysis (**Blade**, Vassena et al., *POPL 2021*, DOI `10.1145/3434330`, cutting speculative def-use flows with minimal `protect` barriers via max-flow/min-cut) and protection of *all* non-secret-address transmissions (**Ultimate SLH**, Zhang et al., *USENIX Security 2023*, closing leakages via variable-time instructions, indirect branches, and register-value side channels missed by standard address-only SLH).

---

### 3. Secret Value Types and Compiler-Barrier Idioms

**Basis:** source + documentation

Because C/C++/Rust lack first-class secrecy types, developers resort to compiler hints and optimization barriers whose semantics are systematically weaker than constant-time preservation:

- **Rust `core::hint::select_unpredictable` (`rust-lang/rust` `b0b600668bb9b4a897e2299b0a44289d42276545`, `library/core/src/hint.rs` L788–810):** Lowers to an LLVM `select` annotated with `!unpredictable` metadata, empirically emitting `cmove %rdx,%rax` on x86-64 in Probe 2B (`rust_select_unpred`). Crucially, however, `hint.rs` L805–807 explicitly states: *"Note however that this lowering is not guaranteed (on any platform) and should not be relied upon when trying to write cryptographic constant-time code."*
- **Rust `subtle` (`dalek-cryptography/subtle` `369e7463e85921377a5f2df80aabcbbc6d57a930`, `src/lib.rs` L99–112, L215–244, L511–525):** Wraps `u8` booleans in `Choice(black_box(input))` and implements `conditional_select` as `let mask = -(choice.unwrap_u8() as signed) as unsigned; a ^ (mask & (a ^ b))`. On stable Rust without `core_hint_black_box`, `subtle` falls back to `#[inline(never)] fn black_box` performing a `read_volatile` on `&input` (L222–243); with `core_hint_black_box`, it invokes `core::hint::black_box` (`rust_hint.rs` L490–492). As Probe 2B (`rust_subtle_style_mask`) demonstrated, `black_box` is a *best-effort* opaque barrier (not a semantic CT guarantee) and actively spills the secret choice bit to the un-erased stack red zone (`mov %dil,-0x1(%rsp)`).
- **Compiler-level Secret Value Types (SVT) / Constant-Time IR proposals:** Research and LLVM RFCs (starting from Simon–Chisnall–Anderson EuroS&P 2018 and subsequent LLVM secret-type proposals) propose tainting IR SSA values (`secret i64` or `ct.*` intrinsics) so that *every* IR and MIR pass (`SimplifyCFG`, `InstCombine`, `SelectOptimize`, `BypassSlowDivision`, `DSE`, register allocator) is barred from branching on, indexing memory by, strength-degrading to `DIV`, or leaving un-erased spills of secret values. To date, **upstream LLVM (`1780833aa0f119a425d7f993aaac29d03cb04da6`) has not adopted first-class secret IR types**, leaving mainstream C/C++/Rust compilers without sound end-to-end CT preservation.

---

### 4. Formally Verified Constant-Time and Speculative Constant-Time Compilers

#### 4.1 CompCert-CT (Barthe et al., POPL 2020) vs. CompCert-ct PCFL (Knothe & Bringmann, ITP 2025)
**Basis:** normative + source + documentation

Two distinct Coq-verified extensions of `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`) address complementary halves of the C constant-time problem and must not be conflated:

1. **CompCert-CT — Constant-Time *Preservation* (Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, Trieu, *POPL 2020*, DOI `10.1145/3371075`, IACR ePrint `2019/926`):**
   - **Goal:** Prove that if a source C program is *already* sequentially constant-time, the compiled assembly produced by a mildly modified CompCert compiler is provably constant-time.
   - **Proof technique:** Instruments the operational semantics of every CompCert intermediate language (`Clight` through `Asm`) with explicit leakage traces (control-flow decisions and memory addresses) and proves **constant-time simulation (CT-simulation)**—reusing CompCert's existing single-trace forward simulation proofs where passes preserve leakage structure, and introducing specialized relational simulation diagrams where passes reorder or eliminate computations.
   - **Modified passes:** Adapts/restricts CompCert passes capable of introducing secret-dependent leakage—including `Switch` compilation, instruction `Selection` (`CminorSel` avoiding leaking lowering idioms), `Constprop`, `CSE`, `Deadcode`, and `Linearize`—establishing end-to-end CT preservation for sequential (non-speculative) executions.
   - **Boundary:** Assumes source C code is already written in CT discipline (no secret branches/indices) and does not protect against speculative execution (Spectre-v1) or microarchitectural variable-latency hardware arithmetic outside the modeled leakage trace.

2. **CompCert-ct — Verified Secret Control-Flow *Elimination* (`knothed/CompCert-ct` `2d1369a4888cff6fd5fd29f28a059e9cf72b1a08`; Knothe & Bringmann, *ITP 2025*, DOI `10.4230/LIPIcs.ITP.2025.31`):**
   - **Goal:** Automatically *transform* C functions containing secret-dependent branches (annotated via `__attribute((tainted(param)))`) into branch-free predicated RTL using Moll & Hack's **Partial Control-Flow Linearization (PCFL)**.
   - **Verified theorems (inspected in `constant-time/README.md` L76–86):** Bundles semantic preservation (`transl_program_correct` in `CTTransform.v`) with `Theorem control_flow_security` (`ControlFlowSecurity.v`) proving the transformed `PredRTL` has zero secret-dependent control flow, supported by `uni_chain_path`, `chain_containment` (`InfluenceRegion.v`), `uni_cdep_equivalent` (`TaintAnalysis.v`), and `new_target_spec` (`PCFLEdgeEmbedding.v`).
   - **Current prototype restrictions (`constant-time/README.md` L6–8):** Restricted to `x86_64`, and the sound end-to-end proof currently disallows loops, memory accesses, and function calls/exits inside transformed functions (applying only to `main` unless using the unverified `CTTransformCheat` driver).

#### 4.2 Jasmin: Predictable Low-Level Compilation, Verified SCT, and Verified Stack Zeroization
**Basis:** source + normative

**Jasmin** (`jasmin-lang/jasmin` `5741d17e3134f5b3b110e5e53494704d6d54f7c7`; Almeida et al. *CCS 2017* DOI `10.1145/3133956.3134078`, *IEEE S&P 2020* DOI `10.1109/SP40001.2020.00067`; Shivakumar et al. *IEEE S&P 2023* DOI `10.1109/SP46215.2023.10179418`) adopts the *"assembly in the head"* philosophy: programmers explicitly specify register vs. stack placement (`reg` vs. `stack`), explicit spill points, and architecture instructions, while a Coq-verified compiler performs only predictable, semantics- and security-preserving transformations across x86-64, ARMv7, ARMv8-A, and RISC-V.

Direct inspection of `jasmin-lang/jasmin` (`5741d17e3134f5b3b110e5e53494704d6d54f7c7`) reveals three architectural features absent from mainstream C/Rust compilers:

1. **Full Coq-verified pipeline (`proofs/compiler/compiler.v` L281–513):** Executes deterministic passes (`RemoveAssertion` → `WintWord` → `ArrayCopy` → `LowerSpill` → `Inlining` → `Unrolling` → `LiveRangeSplitting` → `RegArrayExpansion` → `RemoveGlobal` → `LoadConstantsInCond` → `LowerInstruction` → `PropagateInline` → **`SLHLowering`** → `StackAllocation` → `LowerAddressing` → `RemoveReturn` → `RegAllocation` → `Linearization` → **`StackZeroization`** → `Tunneling` → `assemble_prog`), verifying untrusted OCaml allocation/splitting oracles via Coq-proved validators (`check_uprog`, `check_sprog`, `merge_varmaps.check`).
2. **First-class Speculative Load Hardening & SCT checking (`proofs/lang/slh_ops.v` L17–25; `compiler/src/sct_checker_forward.ml`):** Models hardware misspeculation tracking directly in the language via six SLH primitives (`SLHinit`, `SLHupdate`, `SLHmove`, `SLHprotect`, `SLHprotect_ptr`, `SLHprotect_ptr_fail`), lowered by the Coq-verified `lower_slh_prog` pass (`slh_lowering.v` / `slh_lowering_proof.v`). Crucially, **Arranz-Olmos, Barthe, Blatter, Grégoire, and Laporte (*POPL 2025*, DOI `10.1145/3704880`, ePrint `2024/1203`)** proved that *even verified constant-time compilers (including earlier Jasmin and GCC `-O0`/`-O1`) can break **speculative** constant-time* during register allocation / spilling (e.g., spilling a protected value or reordering stack accesses under misspeculation)—leading to mechanized Coq SCT-preservation proofs and corresponding patches to Jasmin's SCT type checker.
3. **Coq-verified post-linearization stack zeroization (`proofs/lang/stack_zero_strategy.v` L18–31; `proofs/compiler/stack_zeroization.v` L50–141; `proofs/compiler/compiler.v` L480–499):** Unlike C/Rust library zeroizers that run before register allocation and stack frame layout, Jasmin inserts stack zeroization **after linearization** (when the exact stack frame size `stk_max` and alignment `lfd_align` are fixed!) with three Coq-verified strategies:
   - `SZSloop`: compact loop overwriting the entire allocated stack frame;
   - **`SZSloopSCT`**: loop overwrite **followed by an `LFENCE` before `RET`** to prevent speculative return-past-zeroization leaks;
   - `SZSunrolled`: straight-line unrolled stores with no loop branch.
   Dedicated verified implementations exist for x86 (`x86_stack_zeroization.v`), ARMv7 (`arm_stack_zeroization.v`), ARMv8-A (`armv8a_stack_zeroization.v`), and RISC-V (`riscv_stack_zeroization.v`).

#### 4.3 FaCT: Information-Flow DSL Lowering to Shielded LLVM IR
**Basis:** source + normative

**FaCT** (`PLSysSec/fact` `b3daa03f48447285117f426129dbf539a7f32f4a`; Cauligi et al., *PLDI 2019*, DOI `10.1145/3314221.3314605`) bridges high-level readability and LLVM code generation using a static secrecy type system (`secret` vs. `public`) and AST-level predication (`src/command_util.ml` L200–239):

1. **Predication of secret control flow (`src/transbranch.ml` L16–83):** Maintains a stack of enclosing secret branch conditions (`_branchflow`). Every `If(cond, thens, elses)` with `Secret` condition evaluates *both* branches sequentially under positive (`__mK = cond`) and negated (`__mK' = !__mK`) path masks, converting every assignment inside a secret branch into `Cmov(lhs, _form_ctx(), rhs)` (L54–58) and converting secret `&&`/`||`/ternary expressions into `Select` nodes (L69–80). Companion passes (`transfn.ml`, `transret.ml`) thread execution masks through secret function calls and early returns.
2. **Defeating LLVM's `SelectToBranch` via inline assembly (`src/codegen.ml` L55–57, L411–466; `src/intrinsics.ml` L183–203):** Rather than trusting LLVM's `select` instruction (which `SelectOptimize`/`CodeGenPrepare` can turn back into branches), FaCT by default lowers every secret `SelectAsm` and `CmovAsm` to opaque **inline x86-64 assembly**:
   - `fact.select.asm.iN`: `"testb $1, $1; mov $3, $0; cmovnz $2, $0"` with constraints `"=&r,r,r,r,~{flags}"` (L187–191)
   - `fact.cmov.asm.iN`: `"testb $1, $1; cmovnz $2, $0"` with constraints `"=r,r,r,0,~{flags}"` (L198–202)
   Only when explicitly invoked with `-no-inline-asm` does FaCT emit `SelectXor`/`CmovXor` bitmasking.
3. **Verification boundary (`src/command_util.ml` L101–115, L169–175):** FaCT optionally emits wrappers for LLVM-IR-level verification (`-verify-llvm` / `ct-verif`), then delegates final machine-code emission to `clang` (pinned to `clang-6.0` in the repository)—meaning LLVM backend register spills, red-zone copies, and non-`cmov` instruction lowering remain outside the verified LLVM-IR boundary.

---

### 5. Post-Compile Binary-Level Relational Verification (`Binsec/Rel` / `checkct`)

**Basis:** source + normative

When software must compile through untrusted mainstream optimizing toolchains (`GCC`, `Clang`, `rustc`) and assemblers/linkers, **binary-level verification** is the only way to verify the actual linked machine code that executes on silicon. **Binsec/Rel** (Daniel, Bardin, Rezk, *IEEE S&P 2020*, DOI `10.1109/SP40000.2020.00074`) and **Haunted RelSE** (*NDSS 2021*, DOI `10.14722/ndss.2021.24286`, extending RelSE with bounded speculative execution for Spectre-PHT and Spectre-STL) implement **Relational Symbolic Execution (RelSE)** directly over lifted DBA (Dynamic Bitvector Automaton) binary IR.

Direct inspection of `binsec/binsec` (`9749bd8aed7ee0a27959158b1e53e8789cb0e5ab`, `src/sse/plugin/binsec_sse_checkct.ml`) establishes the exact verification architecture:

1. **Three-tier layered analysis (`binsec_sse_checkct.ml` L871–908):** For each security-sensitive expression `e`, `checkct` applies up to three progressively heavier checkers:
   - **Taint (`taint_analysis`, L211–230):** Fast structural check testing whether `e` differs from its mirrored copy `mirror_e(e)` (sharing identical public subterms across the two self-composed executions in `Ct_state.mirror_e` and `Ct_state.mirror_m`, L171–176, L232–294).
   - **Chosen-value concrete falsification (`cv_analysis`, L767–811):** Evaluates `e` vs `e'` against cached concrete models before invoking the SMT solver, rapidly refuting leaky instructions with concrete counterexamples `(public, secret1, secret2)`.
   - **Full Relational SMT (`relse_analysis`, L871–886):** Queries the SMT solver once per check for satisfiability of:
     $$\text{path\_predicate} \;\land\; \text{mirror}(\text{path\_predicate}) \;\land\; (e \neq e')$$
     (`Path.check_sat_assuming_v path (And (Diff e e') ct_state.conjunction)`, L877–880). Unsatisfiability proves non-interference along the explored path; satisfiability extracts a witness (`Report.t`, L58–64) with concrete `memory`, `public`, `secret1`, and `secret2` inputs demonstrating the leak.
2. **Five constant-time leakage classes (`binsec_sse_checkct.ml` L150–161, L654–696):** Automatically instruments every DBA instruction with `Ct_check(expr, kind)` hooks for:
   - `Control_flow` (`check_branch`: conditional branches and indirect jump targets, L690–694);
   - `Memory_access` (`check_memory`: all load and store effective addresses, L679–687);
   - `Multiplication` (`check_mult`: multiplier operands for early-exit hardware multipliers, L655);
   - `Dividend` and `Divisor` (`check_dividend`, `check_divisor`: `DivU`/`DivS`/`RemU`/`RemS` operands—directly catching KyberSlash-class `DIV` emissions, L658–666).
3. **Binary-level Secret-Erasure Verification (`Se_check`, `binsec_sse_checkct.ml` L382–395, L929–943):** Via the directive `check secret erasure over <symbol>`, BINSEC attaches a `Return_hook` that creates a fresh unconstrained symbolic address `!secret_seeker`, reads 1 byte at that arbitrary address (`Path.read_v path None ~addr 1 LittleEndian`), and runs the full RelSE check `analyze read path`. If *any* byte anywhere in memory (stack frame, red zone, spilled buffer, heap) differs between `secret1` and `secret2` upon return, BINSEC reports a concrete counterexample address and secret pair!

---

### 6. Cross-System Comparison Matrix

**Basis:** derived (from source + normative + execution)

| System / Approach | Operates At | Preserves Sequential CT? | Handles Speculative CT (Spectre-v1)? | Verifies / Enforces Secret Erasure? | Surviving Trust Boundary (TCB) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Mainstream GCC / LLVM (`rustc`)** | C / C++ / Rust → Machine code | **No** (`SelectOptimize`, `SwitchToLookupTable`, `BypassSlowDivision`, `-Os`/`-Oz` `DIV`) | **No** (manual `lfence` hoistable; `-mspeculative-load-hardening` unverified) | **No** (DSE deletes `memset`; `volatile` misses `%xmm`/spills; `-fzero-call-used-regs` misses stack/tail-calls) | Entire optimizing compiler + assembler + linker + hardware |
| **Library barriers (`subtle`, `zeroize`, `memset_explicit`)** | Source library on GCC/LLVM | **Best-effort only** (`black_box` unverified; spills to red zone) | **No** | **Memory object only** (not register/SIMD copies or prior spills) | Entire compiler + assembler + linker + hardware |
| **FaCT (`PLSysSec/fact`)** | Secrecy-typed DSL → inline-asm LLVM IR → `clang` | **Yes at IR + inline-asm `cmov`** (vulnerable if `-no-inline-asm` or backend spills/regs) | **No** (sequential CT model) | **No** | FaCT compiler + `clang` backend + assembler + linker + hardware |
| **CompCert-CT (Barthe et al. POPL 2020)** | C (already CT) → `Asm` | **Yes** (Coq-verified CT-simulation) | **No** (sequential CT model) | **No** (focuses on timing trace preservation) | Coq kernel + CompCert semantics + assembler/linker + hardware |
| **CompCert-ct PCFL (`knothed/CompCert-ct` ITP 2025)** | Tainted C subset → Predicated RTL | **Control-flow elimination proved** (restricted subset: no loops/mem/calls) | **No** | **No** | Coq kernel + RTL-to-Asm backend + assembler/linker + hardware |
| **Jasmin (`jasmin-lang/jasmin` + POPL 2025)** | Low-level Jasmin → x86/ARM/RISC-V `Asm` | **Yes** (Coq-verified + CT checker) | **Yes** (Coq-verified `slh_lowering` + patched SCT checker) | **Yes for stack frames** (`SZSloop`, `SZSloopSCT` + `LFENCE`, `SZSunrolled` proved in Coq) | Coq kernel + Jasmin `asm_prog` printer + assembler/linker + hardware |
| **Binsec/Rel (`binsec/binsec` `checkct`)** | **Linked binary (ELF/PE)** | **Yes** (RelSE over branches, memory, `MUL`, `DIV`) | **Yes** (Haunted RelSE for bounded PHT/STL) | **Yes for memory** (`Se_check` via unconstrained `!secret_seeker`) | BINSEC DBA lifter + SMT solver + bounded path exploration + hardware |

## Boundaries

- **Known not to apply:**
  - `core::hint::select_unpredictable` in Rust (`rust-lang/rust` `b0b600668bb9b4a897e2299b0a44289d42276545`, `library/core/src/hint.rs` L805–807) is explicitly documented *not* to guarantee branchless lowering on any platform and must not be relied on for cryptographic constant-time security.
  - `ISO/IEC 9899:2024` §7.26.6.2 `memset_explicit`, BSD/POSIX `explicit_bzero`, and Rust `zeroize` apply *only* to the explicitly addressed memory object; they do not erase secret copies held in CPU registers (`%xmm0`/`%xmm1`, GPRs), red-zone spills, or prior reallocated heap buffers.
  - Sequential constant-time preservation (CompCert-CT POPL 2020, classic FaCT, classic Jasmin CT without SLH) does *not* imply speculative constant-time (Spectre-v1/v4) safety; Arranz-Olmos et al. (*POPL 2025*, DOI `10.1145/3704880`) demonstrated concrete cases where CT-preserving compilation breaks SCT.
  - Classic PC+address constant-time models (all compilers and binary verifiers in this report) do *not* protect against hardware Data-Memory-Dependent Prefetchers (DMPs, e.g., GoFetch/Augury) that dereference pointer-shaped secret values sitting at rest in cache lines, nor against frequency-throttling power-to-timing channels (Hertzbleed).
- **Not examined:**
  - Direct execution of `binsec` (OCaml/SMT binary tool), `factc`, `jasminc`, or Coq proof builds for CompCert-CT/Jasmin was not performed on this host; their mechanisms were verified by direct source inspection at pinned commits and primary peer-reviewed publications.
  - Non-x86-64 code generation probes (AArch64 `csel`/`csdb`, RISC-V `Zicond`, WebAssembly) and Clang C front-end `-O2`/`-Oz` probes (since `clang` was absent; LLVM 22.1.6 IR/backend behavior was observed via `rustc 1.98.0-nightly`).
  - Hardware masking preservation (Boolean/arithmetic share recombination under register allocation and CSE, as studied by Tornado/maskVerif/Coco) is a distinct higher-order probing property outside this report's scope.
- **Unknown:**
  - Whether future upstream LLVM releases will accept a first-class secret-value type or guaranteed `ct.select` intrinsic across all target backends (`llvm/llvm-project` `1780833aa0f119a425d7f993aaac29d03cb04da6` still lacks one).
  - Exact completeness bounds of BINSEC `checkct` symbolic execution on large, deeply looping post-quantum cryptographic binaries (such as full ML-DSA/Dilithium rejection-sampling loops) without manual loop unrolling or path-merging annotations.
- **Unsupported:**
  - Standard C (`ISO/IEC 9899:2024`), C++, and Rust language specifications provide no normative semantics for constant-time execution, register erasure across function boundaries (including sibling tail calls), or speculative barrier non-hoisting across `readonly` references.
  - `knothed/CompCert-ct` (`2d1369a4888cff6fd5fd29f28a059e9cf72b1a08`) does not currently support loops, memory accesses, or interprocedural calls inside its formally verified `CTTransform` pipeline (`constant-time/README.md` L6–8).

## Evidence

### Primary Upstream Source Code (Pinned Commits, Observed 2026-11-19)
- **`llvm/llvm-project` @ `1780833aa0f119a425d7f993aaac29d03cb04da6`:**
  - `llvm/lib/CodeGen/SelectOptimize.cpp`: L48–83 (`SelectOptimizeImpl` statistics/analyses), L1023–1038 (converting `select` to branch on `isSelectHighlyPredictable && isPredictableSelectExpensive()` or `hasExpensiveColdOperand`).
  - `llvm/lib/CodeGen/CodeGenPrepare.cpp`: L7381–7395, L7508–7515 (`optimizeSelectInst` fallback select-to-branch lowering).
  - `llvm/lib/Transforms/Utils/SimplifyCFG.cpp`: L7520–7535 (`shouldBuildLookupTable`), L7775–7790 (`switchToLookupTable`).
  - `llvm/lib/Transforms/Scalar/DeadStoreElimination.cpp`: L2099–2111 (end-of-function dead-store removal on single underlying object).
  - `llvm/lib/CodeGen/PrologEpilogInserter.cpp`: L1209–1351 (`PEIImpl::insertZeroCallUsedRegs`); `llvm/lib/Target/X86/X86FrameLowering.cpp`: L643 (`emitZeroCallUsedRegs`).
  - `llvm/lib/Target/X86/X86SpeculativeLoadHardening.cpp`: L132–168, L346–358, L429–487 (late MIR CFG predicate tracking, `LFENCE` entry guard, `hardenLoadAddr`).
- **`jasmin-lang/jasmin` @ `5741d17e3134f5b3b110e5e53494704d6d54f7c7`:**
  - `proofs/compiler/compiler.v`: L281–513 (full Coq-verified compilation pipeline including `lower_slh_prog` at L352 and `stack_zeroization_lprog` at L498).
  - `proofs/lang/slh_ops.v`: L18–25 (`SLHinit`, `SLHupdate`, `SLHmove`, `SLHprotect`, `SLHprotect_ptr`, `SLHprotect_ptr_fail`).
  - `proofs/lang/stack_zero_strategy.v`: L18–31 (`SZSloop`, `SZSloopSCT`, `SZSunrolled`); `proofs/compiler/stack_zeroization.v`: L50–141; `proofs/_CoqProject`: L69–70, L83–84, L141–142, L147–148, L154–155, L171–172 (verified per-architecture stack zeroization & SLH proofs).
- **`PLSysSec/fact` @ `b3daa03f48447285117f426129dbf539a7f32f4a`:**
  - `src/command_util.ml`: L101–115 (`clang-6.0` backend invocation), L169–175 (`ct-verif` wrapper), L195–239 (full transformation pipeline).
  - `src/transbranch.ml`: L16–83 (`_branchflow` path-mask stack, `If` predication into `Cmov` and `Select`).
  - `src/codegen.ml`: L55–57, L411–466; `src/intrinsics.ml`: L10–41, L183–203 (x86-64 inline assembly `testb $1, $1; mov $3, $0; cmovnz $2, $0` and `testb $1, $1; cmovnz $2, $0`).
- **`binsec/binsec` @ `9749bd8aed7ee0a27959158b1e53e8789cb0e5ab`:**
  - `src/sse/plugin/binsec_sse_checkct.ml`: L58–64 (`Report.t`), L150–161 (`OPTIONS`: `check_branch`, `check_memory`, `check_mult`, `check_dividend`, `check_divisor`), L166–319 (`Ct_state` mirror expression & mirror memory tables), L382–395 (`check secret erasure over <symbol>` `Return_hook`), L654–696 (`Ct_check` DBA instrumentation), L767–908 (`cv_analysis`, `relse_analysis` querying `Diff e e' ∧ ct_state.conjunction`), L929–943 (`se_check` via unconstrained symbolic address `!secret_seeker`).
- **`knothed/CompCert-ct` @ `2d1369a4888cff6fd5fd29f28a059e9cf72b1a08`:**
  - `constant-time/README.md`: L1–87 (ITP 2025 PCFL scope restrictions and Coq theorem inventory `transl_program_correct`, `control_flow_security`, `uni_chain_path`).
- **`rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545`:**
  - `library/core/src/hint.rs`: L489–492 (`black_box`), L788–810 (`select_unpredictable` explicit non-CT disclaimer).
- **`RustCrypto/utils` @ `77d1a3e6c2e8c28f49189258abb5d4405c0f1330`:**
  - `zeroize/src/lib.rs`: L281–285, L432–459, L501–518 (`Vec` best-effort caveat), L797–801 (`volatile_write`); `zeroize/src/bulk.rs`: L7–60 (`HAS_ASM` + `optimization_barrier` vs `volatile_fill_slice`); `zeroize/src/x86.rs`: L10–25 (SIMD register `Zeroize`).
- **`dalek-cryptography/subtle` @ `369e7463e85921377a5f2df80aabcbbc6d57a930`:**
  - `src/lib.rs`: L99–112, L215–244 (`black_box` fallback and `Choice`), L511–525 (`conditional_select` / `conditional_assign` mask arithmetic).

### Standards and Peer-Reviewed Literature
- ISO/IEC 9899:2024 (C23), §7.26.6.2 (`memset_explicit`).
- Gilles Barthe, Sandrine Blazy, Benjamin Grégoire, Rémi Hutin, Vincent Laporte, David Pichardie, Alix Trieu, *"Formal Verification of a Constant-Time Preserving C Compiler"*, PACMPL Vol. 4, POPL (2020), DOI `10.1145/3371075`, IACR ePrint `2019/926`.
- Santiago Arranz-Olmos, Gilles Barthe, Lionel Blatter, Benjamin Grégoire, Vincent Laporte, *"Preservation of Speculative Constant-Time by Compilation"*, PACMPL Vol. 9, POPL, Art. 44, pp. 1293–1325 (2025), DOI `10.1145/3704880`, IACR ePrint `2024/1203`.
- David Knothe, Oliver Bringmann, *"On Verifying Secret Control Flow Elimination"*, ITP 2025, DOI `10.4230/LIPIcs.ITP.2025.31`.
- José Bacelar Almeida et al., *"Jasmin: High-Assurance and High-Speed Cryptography"*, CCS 2017, DOI `10.1145/3133956.3134078`; *"The Last Mile"*, IEEE S&P 2020, DOI `10.1109/SP40001.2020.00067`; Basavesh Ammanaghatta Shivakumar et al., *"Typing High-Speed Cryptography against Spectre v1"*, IEEE S&P 2023, DOI `10.1109/SP46215.2023.10179418`.
- Sunjay Cauligi et al., *"FaCT: A DSL for Timing-Sensitive Computation"*, PLDI 2019, DOI `10.1145/3314221.3314605`.
- Lesly-Ann Daniel, Sébastien Bardin, Tamara Rezk, *"Binsec/Rel: Efficient Relational Symbolic Execution for Constant-Time at Binary-Level"*, IEEE S&P 2020, DOI `10.1109/SP40000.2020.00074`; *"Hunting the Haunter — Efficient Relational Symbolic Execution for Spectre with Haunted RelSE"*, NDSS 2021, DOI `10.14722/ndss.2021.24286`.
- Laurent Simon, David Chisnall, Ross Anderson, *"What You Get is What You C: Controlling Side Effects in Mainstream C Compilers"*, IEEE EuroS&P 2018, DOI `10.1109/EuroSP.2018.00009`.
- Daniel J. Bernstein et al., *"KyberSlash: Exploiting secret-dependent division timings in Kyber implementations"*, IACR TCHES Vol. 2025, Issue 2, pp. 209–234, DOI `10.46586/tches.v2025.i2.209-234`, ePrint `2024/1049`.
- Marc Andrysco et al., *"On Subnormal Floating Point and Abnormal Timing"*, IEEE S&P 2015, DOI `10.1109/SP.2015.44`.
- Marco Vassena et al., *"Automatically Eliminating Speculative Leaks from Cryptographic Code with Blade"*, POPL 2021, DOI `10.1145/3434330`; Zhiyuan Zhang et al., *"Ultimate SLH: Taking Speculative Load Hardening to the Next Level"*, USENIX Security 2023.

### Local Execution Probes (Observed 2026-11-19 on `x86_64-unknown-linux-gnu`)
- **Environment:** Linux `7.1.6-1rodete1-amd64`, `gcc (Debian 15.2.0-14) 15.2.0`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`LLVM 22.1.6`), `GNU objdump 2.47`.
- **Probe 2A (DSE & register residue):** Compiled `wipe_naive_memset` and `wipe_explicit_bzero` via `gcc -O2` and `gcc -O2 -fzero-call-used-regs=used`, and `rust_wipe_naive`/`rust_wipe_volatile` via `rustc -O`; confirmed complete DSE deletion of `memset`/`fill(0)`, `%xmm0`/`%xmm1` residue surviving `explicit_bzero`, zeroing skipped on sibling tail-call `jmp`, and LLVM emitting 32 volatile zero stores to an unpopulated stack slot in `rust_wipe_volatile`.
- **Probe 2B (Branch/LUT synthesis & `black_box` red-zone spill):** Compiled `rust_switch_to_lut`, `rust_select_exp_branch`, `rust_branchless_idiom`, `rust_div_select`, `rust_select_unpred`, and `rust_subtle_style_mask` via `rustc -O`; confirmed `.rodata` LUT indexing (`mov (%rax,%rdi,4),%eax`), select-to-branch lowering, `BypassSlowDivision` (`shr $0x20,%rdx; je 24`), and red-zone spill (`mov %dil,-0x1(%rsp)`).
- **Probe 2C (KyberSlash `DIV` emission):** Compiled `(a * 2 + 3329) / 6658` under `gcc -O2` vs `gcc -Os` and `rustc -O` vs `rustc -C opt-level=z`; confirmed constant-time `imul`/`shr` under `-O2`/`-O` switching to variable-latency `div %ecx` (`f7 f1`) under `-Os` and `-C opt-level=z`.
- **Probe 2D (`LFENCE` load hoisting & `readonly` reuse):** Compiled `gcc_extended_asm_nomem` vs `gcc_extended_asm_mem` under `gcc -O2` and `hoist_uncond_proper` under `rustc -O`; confirmed `movzbl (%rdi),%edx` hoisted strictly above `test`/`je`/`lfence` when `"memory"` clobber was omitted from extended asm, and confirmed LLVM reusing a single `readonly` load across three subsequent `_mm_lfence()` calls in an unrolled loop.

## Revalidation

1. **Re-run KyberSlash `-O2` vs `-Os`/`-Oz` division check (~1 second):**
   ```bash
   cat > /tmp/kyber_div.c <<'EOF'
   #include <stdint.h>
   uint32_t compress(uint32_t a) { return (a * 2u + 3329u) / 6658u; }
   EOF
   gcc -O2 -c /tmp/kyber_div.c -o /tmp/k_O2.o && objdump -d /tmp/k_O2.o
   gcc -Os -c /tmp/kyber_div.c -o /tmp/k_Os.o && objdump -d /tmp/k_Os.o
   ```
   Verify `imul`/`shr` at `-O2` vs `div %ecx` (`f7 f1`) at `-Os` (or equivalently `rustc -C opt-level=z`).
2. **Re-run DSE, SIMD residue, and `LFENCE` hoisting probes (~2 seconds):**
   ```bash
   cat > /tmp/lfence_check.c <<'EOF'
   #include <stdint.h>
   uint8_t bad(const uint8_t *a, int c) {
     if (c) { __asm__ volatile("lfence" : : ); return a[0] + 1; }
     return a[0] + 2;
   }
   uint8_t good(const uint8_t *a, int c) {
     if (c) { __asm__ volatile("lfence" : : : "memory"); return a[0] + 1; }
     return a[0] + 2;
   }
   EOF
   gcc -O2 -c /tmp/lfence_check.c -o /tmp/lf.o && objdump -d /tmp/lf.o
   ```
   Confirm `movzbl (%rdi),%edx` precedes `test`/`je`/`lfence` in `bad` while following `lfence` in `good`.
3. **Re-run Rust `SwitchToLookupTable` / `BypassSlowDivision` / `write_volatile` probe:** Compile a minimal crate with `rustc -O --emit=obj` containing a 8-arm `match (x & 7)`, a 64-bit unsigned division, and a 32-byte `write_volatile` stack wipe; inspect `objdump -d` for `.rodata` indexed loads, `shr $0x20; je` before `div`, and `%xmm0`/`%xmm1` secret retention.
4. **Track upstream compiler and verifier evolution:**
   - Diff `llvm/lib/CodeGen/SelectOptimize.cpp` and `llvm/lib/Transforms/Utils/SimplifyCFG.cpp` against `1780833aa0f119a425d7f993aaac29d03cb04da6` for any introduction of secret IR attributes or guaranteed `ct.select` intrinsics.
   - Diff `jasmin-lang/jasmin` (`proofs/compiler/{compiler.v,slh_lowering.v,stack_zeroization.v}`) against `5741d17e3134f5b3b110e5e53494704d6d54f7c7` and `binsec/binsec` (`src/sse/plugin/binsec_sse_checkct.ml`) against `9749bd8aed7ee0a27959158b1e53e8789cb0e5ab` for new leakage models or speculative/erasure checkers.
   - For production cryptographic binaries built with untrusted optimizing compilers, integrate post-link binary RelSE (`binsec -tool checkct` with `check secret erasure over <entry>`) directly into CI whenever compiler versions, target CPUs, or optimization flags change.
