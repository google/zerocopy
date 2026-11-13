# Validating Formal ISA Models Against Hardware: Methods, Divergences, Errata, and Execution Resources

## Summary

A formal ISA specification inside a verified compiler's trusted computing base (TCB) is not proved correct inside the theorem prover; it must be empirically validated against physical silicon and reference emulators, and its treatment of underspecified or errata-affected instructions must be sound across every target microarchitecture. This report establishes the complete validation plan, divergence catalog, compiler/linker errata inventory, hardware/emulator resource matrix, and empirical validation measurements across `x86_64`, `i686`, and `aarch64`:

1. **Empirical Hardware vs. Emulator Divergences Captured (`support/hardware_validation_results.json`):** Executing our multi-extension validation suite compiled with `rustc 1.99.1` on native Intel Xeon Ice Lake-SP (`GenuineIntel` Family 6, Model 106, Stepping 6, supporting AVX-512F/BW/DQ/VL/VBMI/VBMI2/VNNI/VPOPCNTDQ/BITALG/IFMA, VAES, VPCLMULQDQ, GFNI, SHA-NI, ADX, BMI1/2) alongside `qemu-i386` 11.1.2 and `qemu-aarch64` 11.1.2 (`-cpu max`) demonstrates concrete bit-level divergences that a sound ISA model must account for:
   - **Floating-point reciprocal and reciprocal-square-root approximations (`RCPSS`, `RSQRTSS`, `VRCP14SS`, `VRSQRT14SS`, `FRECPE`, `FRSQRTE`):** On input `3.0f32` (`0x40400000`), native Intel Ice Lake-SP returns `RCPSS = 0x3eaaa000` (`0.33325195`) and `RSQRTSS = 0x3f13c800` (`0.5772705`), whereas `qemu-i386 -cpu max` returns `RCPSS = 0x3eaaaaab` (exact IEEE-754 `1.0 / 3.0`) and `RSQRTSS = 0x3f13cd3a`, and `qemu-aarch64 -cpu max` returns `FRECPE = 0x3eaa8000` and `FRSQRTE = 0x3f138000`. Even on the same Intel core, AVX-512 `VRCP14SS` returns `0x3eaaaa80` (`14`-bit mantissa table) vs SSE `RCPSS` `0x3eaaa000` (`12`-bit mantissa table), and for `1.0f32` (`0x3f800000`), SSE `RCPSS` returns `0x3f7ff000` (`0.99975586`) whereas `VRCP14SS` returns exact `0x3f800000` (`1.0`). Consequently, any ISA model that treats `RCPSS`/`RSQRTSS` as deterministic across Intel, AMD, and QEMU—rather than relational within the architectural relative-error bound ($|\text{rel\_err}| \le 1.5 \times 2^{-12}$)—is unsound across vendors and emulators.
   - **Zero-input bit scans (`BSF`/`BSR` vs `TZCNT`/`LZCNT`):** On `0`, Intel SDM specifies that `BSF`/`BSR` set `ZF=1` and leave the destination register *architecturally undefined*, whereas `TZCNT`/`LZCNT` deterministically produce the operand bit-width (`64` or `32`) with `CF=1, ZF=0`. On both native Ice Lake-SP (`x86_64` and `i686`) and `qemu-i386`, `BSF`/`BSR` on `0` preserve the prior destination register value (`0xdeadbeefcafebabe` / `0x1337c0de42429999`) while setting `ZF=1`. A sound ISA model must nevertheless leave the destination register nondeterministic (`Option` / relational `∃ v`) when `src = 0`, while modeling `TZCNT`/`LZCNT` deterministically.
   - **AArch64 division edge cases, SVE vector length, and PAC signing:** Under `qemu-aarch64 -cpu max`, `UDIV` and `SDIV` by `0` deterministically return `0` without trapping; `SDIV(i64::MIN, -1)` wraps to `0x8000000000000000` (`i64::MIN`); `RDVL x5, #1` reports a 512-bit (`64`-byte) default SVE vector length (`UADDV` over `INDEX 1..8` = `36`); and `PACDA` + `AUTDA` insert and strip a non-zero top-byte pointer authentication code (`0x005b123456789ab0` $\to$ `0x0000123456789ab0`).
2. **Compiler & Linker Errata Workarounds (`llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):** LLVM 23.1.1 and LLD implement mandatory instruction-stream and linker-relaxation workarounds for silicon errata that alter emitted machine code—most notably Intel Skylake JCC 32-byte boundary NOP padding (`X86AsmBackend.cpp`), Arm Cortex-A53 erratum `835769` (`AArch64A53Fix835769.cpp`, inserting `NOP` between memory writes and 64-bit multiply-accumulate) and erratum `843419` (`lld/ELF/Arch/AArch64.cpp:688`, redirecting `ADRP` in the last two words of a 4 KiB page to a linker veneer), and BTI/PAC landing-pad enforcement (`AArch64BranchTargets.cpp`, `lld/ELF/Arch/AArch64.cpp:32-63`).

## Applicability

The findings in this report apply to:
- **ISA validation and differential testing frameworks:** `AeneasVerif/kraken@c9aa45ee1b273892d7efa7bbf8a8a9391e17b2c0` (`Tests/TestGeneration.lean`), `leanprover/LNSym@5c05220ff970e3bdd7813ad0c9ef3741522c8b92`, ACL2 `x86isa` `Cosim`, and K-X86-64 hardware co-simulation.
- **Compiler and linker errata passes:** LLVM 23.1.1 (`llvm/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) in `llvm/lib/Target/X86/`, `llvm/lib/Target/AArch64/`, and `lld/ELF/Arch/`.
- **Execution environments examined on 2026-11-13:**
  - Native `x86_64` and `i686` IA-32 compatibility mode on Intel Xeon Ice Lake-SP (`GenuineIntel`, Family 6, Model 106, Stepping 6);
  - User-mode emulators `qemu-i386` and `qemu-aarch64` version `11.1.2 (Debian 1:11.1.2+ds-2)`.

## Findings

### 1. Validation Methods and Coverage Criteria for Trusted ISA Models

Basis: documentation + source (`AeneasVerif/kraken@c9aa45ee`, `leanprover/LNSym@5c05220f`, `10.1145/2737924.2737981`)

Validating an ISA model against silicon and reference simulators requires four complementary techniques, each catching a distinct failure class:

| Validation Method | Mechanism & Precedent | Target Defect Class Caught | Coverage Criterion |
| :--- | :--- | :--- | :--- |
| **1. Randomized & Boundary-Biased Hardware Co-Simulation** (`Kraken` `Tests/TestGeneration.lean`, `LNSym`, `K-X86-64`, `ACL2 Cosim`) | Generate concrete initial register/flag/memory states (biased toward `0`, `1`, `-1`, `INT_MIN`, `INT_MAX`, subnormals, `NaN` payloads, and page/cache-line boundaries), execute single instructions or short basic blocks natively in a sandboxed child process (`ptrace` / `sigaction` harness or inline-assembly runner), and compare final register/flag/memory state against the theorem prover's evaluator (`#eval` / extracted OCaml/C). | Wrong shift masks, carry/overflow flag polarity inversions (`SUB`/`CMP` borrow on Arm vs x86), upper-lane zeroing bugs (32-bit GPR writes zeroing bits `63:32`; VEX/EVEX zeroing upper YMM/ZMM bits vs legacy SSE preserving bits `127:64`). | **100% opcode/encoding variant coverage** $\times$ $\ge 100$ boundary-biased input vectors per variant across every supported target feature. |
| **2. Path-Exploration Symbolic Lifting (PokeEMU)** (Martignoni et al., *ASPLOS 2012* / *PLDI 2015*, `10.1145/2737924.2737981`) | Run symbolic execution (concolic path exploration) over a reference emulator (QEMU TCG, Bochs, or Sail C emulator) for a single instruction to enumerate **every feasible internal control-flow path** inside the instruction's helper function, solving path constraints with SMT to synthesize one concrete test case per internal branch. | Deep corner cases missed by uniform random inputs: e.g., `SHLD`/`SHRD` when `count % 64 == 0` vs `count == 1` vs `count > operand_size`, `CMPXCHG16B` failure branch, or IEEE-754 tininess-before-rounding vs after-rounding flags. | **100% branch coverage** of the reference specification's per-instruction semantic helper functions. |
| **3. Differential Cross-Model Equivalence Checking (`Sail` $\leftrightarrow$ `Lean` / `ASL` $\leftrightarrow$ `Lean`)** (`Verified-zkEVM/riscv-zkvm@6810fc14`, `ASLp`) | Prove or SMT-check (`bv_decide` / Bitwuzla) that for all symbolic 32-bit/variable-length opcodes in a supported class, the fast flat Lean 4 WP step function produces the exact same post-state as the vendor-derived `Sail` / `ASL` specification when defined (or refines its nondeterministic set). | Translation bugs introduced when optimizing verbose vendor ASL/Sail code into fast Lean 4 bitvector operations. | **Exhaustive symbolic bitvector equivalence** (`∀ reg_in imm, fast_step opc s = sail_step opc s`) per instruction schema. |
| **4. Undocumented & Reserved Encoding Tunneling (`sandsifter`)** (Domas, Black Hat 2017, `xoreaxeaxeax/sandsifter`) | Depth-first prefix/opcode search on x86 hardware comparing instruction length (`#UD` vs `#GP` vs page-fault boundary at `PAGE_END - k`) against decoder tables (`Intel XED` / `LLVM MC`). | Decoder/hardware desynchronization where a verifier's decoder rejects or mis-sizes a prefix combination (e.g., redundant `REX`/`LOCK`/`66h` prefixes) that hardware executes as an alias. | **Prefix-canonicalization soundness:** the compiler's verified encoder emits only canonical encodings without redundant prefixes, and the binary validator rejects non-canonical prefix sequences. |

### 2. Specification Divergences, Undefined Flags, and Architectural Underspecification

Basis: normative (Intel SDM `325462-084US`, Arm ARM `DDI 0487`) + execution (`support/hardware_validation_results.json`)

A formal ISA model used for compiler verification must never equate "hardware happened to produce value $v$ on one test CPU" with "all architectural implementations produce $v$." Instead, wherever the architecture manual designates an outcome as **Undefined**, **Implementation-Specific Approximation**, **`IMPLEMENTATION DEFINED`**, or **`CONSTRAINED UNPREDICTABLE`**, the formal model must either **forbid** the condition in its precondition or **over-approximate** (nondeterministically havoc) the affected state components.

#### 2.1 Empirically Measured Hardware and Emulator Divergences

On 2026-11-13, we compiled and executed `support/run_hardware_validation_probes.py` with `rustc 1.99.1` across three environments:
1. **Native `x86_64`:** Intel Xeon Ice Lake-SP (`GenuineIntel`, Family 6, Model 106, Stepping 6).
2. **Native `i686` IA-32 compatibility mode vs. `qemu-i386 -cpu max` (`11.1.2`):** Running the identical 32-bit `i686-unknown-linux-gnu` binary natively on the Ice Lake-SP kernel and under `qemu-i386`.
3. **AArch64 under `qemu-aarch64 -cpu max` (`11.1.2`):** Static `#![no_std]` AArch64 ELF binary compiled with `-Ctarget-feature=+lse,+aes,+sha2,+sve,+paca,+pacg,+bti` and linked with `rust-lld`.

| Probe Category & Instruction | Input Values | Native Intel Ice Lake-SP (`x86_64` / `i686`) | `qemu-i386 -cpu max` (`11.1.2`) | `qemu-aarch64 -cpu max` (`11.1.2`) | Formal ISA Modeling Requirement |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **SSE Reciprocal Estimate (`RCPSS` / `FRECPE`)** | `1.0f32` (`0x3f800000`), `3.0f32` (`0x40400000`) | `RCPSS(1.0) = 0x3f7ff000` (`0.99975586`); `RCPSS(3.0) = 0x3eaaa000` (`0.33325195`) | `RCPSS(3.0) = 0x3eaaaaab` (`0.33333334`, exact float divide!) | `FRECPE(3.0) = 0x3eaa8000` (`0.33300781`) | **Divergence observed across Intel, QEMU-i386, and Arm:** Intel uses a 12-bit ROM lookup table (`|rel_err| <= 1.5 * 2^-12`), AMD Zen uses a different ROM table, and QEMU-i386 computes `1.0f / x`. Model **x86 `RCPSS`/`RSQRTSS` relationally** via error bounds; by contrast, **Arm ASL specifies `FRECPE`/`FRSQRTE` as an exact bit-level algorithm** (`RecipEstimate`), which QEMU-aarch64 matches bit-for-bit! |
| **SSE vs. AVX-512 Reciprocal (`RCPSS` vs. `VRCP14SS`, `RSQRTSS` vs. `VRSQRT14SS`)** | `1.0f32`, `2.0f32`, `3.0f32`, `0.25f32` | `VRCP14SS(1.0) = 0x3f800000` (`1.0` exact vs `RCPSS` `0x3f7ff000`); `VRCP14SS(3.0) = 0x3eaaaa80`; `VRSQRT14SS(3.0) = 0x3f13cc80` (vs `RSQRTSS` `0x3f13c800`) | N/A | N/A | `VRCP14*` / `VRSQRT14*` guarantee $|\text{rel\_err}| \le 2^{-14}$ and exact results on powers of two, differing from legacy `RCPSS`/`RSQRTSS` even on the same core. |
| **Zero-Input Bit Scan (`BSF` / `BSR`)** | `src = 0`, pre-seeded `dst = 0xdeadbeefcafebabe` | `ZF = 1`, `dst` preserved (`0xdeadbeefcafebabe` on `x86_64`, `0xdeadbeef` on `i686`) | `ZF = 1`, `dst` preserved (`0xdeadbeef`) | N/A | Intel SDM marks `dst` **Undefined** when `src = 0` (even though Intel/AMD silicon and QEMU leave `dst` unmodified). Formal models **must havoc `dst`** when `src = 0`. |
| **Zero-Input Count Zeros (`TZCNT` / `LZCNT` / `CLZ`)** | `src = 0` (`TZCNT`/`LZCNT`), `src = 0x00f0123456789abc` (`CLZ`) | `TZCNT(0) = 64` (`32` on `i686`), `CF = 1, ZF = 0`; `LZCNT(0) = 64, CF = 1` | `TZCNT(0) = 32, CF = 1` | `CLZ = 8` | Fully deterministic across all architectures; `TZCNT`/`LZCNT` define `CF=1, ZF=0` on `0`. |
| **FMA3 Single-Rounding vs. Unfused `MULSD` + `ADDSD`** | $a = 1 + 2^{-52}$, $b = 1 - 2^{-52}$, $c = -1.0$ | `VFMADD213SD` = `0xb970000000000000` ($-2^{-104}$ exact); `VMULSD + VADDSD` = `0x0000000000000000` ($0.0$) | N/A | N/A | Confirms infinite-precision intermediate product before single IEEE-754 rounding in FMA3. |
| **Dual Carry Chains (`ADCX` + `ADOX`)** | `CF = 1, OF = 0`, adding `u64::MAX` to `1` (`ADCX`) and `2` (`ADOX`) | `c_chain = 1, o_chain = 1, CF = 1, OF = 1` | N/A | N/A | `ADCX` reads/writes only `CF`; `ADOX` reads/writes only `OF`, leaving the other flag untouched. |
| **AVX-512 Zero-Masking (`{k1}{z}`) & `VPOPCNTQ`** | `k1 = 0x05` (lanes 0, 2 active), `zmm0 = all 1s`, `vpaddq zmm1 {k1}{z}, zmm0, zmm0` | Lane 0 = `0xfffffffffffffffe` (`-2`), Lane 1 = `0x0000000000000000` (zero-masked), `VPOPCNTQ` = `64` | N/A | N/A | EVEX zero-masking `{z}` forces inactive destination lanes to `0`, whereas merge-masking preserves prior `zmm1` lanes. |
| **AArch64 Integer Division Corner Cases (`UDIV` / `SDIV`)** | `0x123456789abcdef0 / 0` and `i64::MIN / -1` | N/A (x86 `DIV`/`IDIV` raises `#DE` SIGFPE!) | N/A | `UDIV(x, 0) = 0`, `SDIV(x, 0) = 0`, `SDIV(i64::MIN, -1) = 0x8000000000000000` | Crucial x86 vs. AArch64 semantic contrast: AArch64 `UDIV`/`SDIV` are total instructions that never trap, whereas x86 `DIV`/`IDIV` trap on divide-by-zero or quotient overflow. |
| **AArch64 SVE Vector Length (`RDVL`, `INDEX`, `UADDV`) & PAC (`PACDA`/`AUTDA`)** | `RDVL #1`, `INDEX 1..`, `PACDA` + `AUTDA` on `0x0000123456789ab0` | N/A | N/A | `sve_vl_bytes = 64` (512-bit), `UADDV = 36` ($\sum_{i=1}^8 i$), `pacda_signed = 0x005b123456789ab0`, `autda_restored = 0x0000123456789ab0` | SVE semantics in Lean 4 must be parameterized by `VL ∈ {16, 32, 64, ..., 256}` bytes (`128..2048` bits); PAC tag bits depend on `TCR_EL1` and secret key registers. |

#### 2.2 Catalog of Architecturally Underspecified Behaviors

1. **x86 Undefined Status Flags:**
   - **`MUL` / `IMUL`:** `CF` and `OF` are defined; `SF`, `ZF`, `AF`, `PF` are architecturally **Undefined** (note: Intel Aldo Lake / Golden Cove and later CPUs define `ZF` on `MUL`, but earlier Intel/AMD cores do not).
   - **`SHL` / `SHR` / `SAR` / `SHLD` / `SHRD`:** When shift count is `0`, no flags are affected. When shift count $> 1$, `OF` is **Undefined**. When shift count $> 0$, `AF` is **Undefined**.
   - **`AND` / `OR` / `XOR` / `TEST`:** `CF = 0, OF = 0`, `SF, ZF, PF` defined; `AF` is **Undefined**.
   - **`DIV` / `IDIV`:** All six status flags (`CF, OF, SF, ZF, AF, PF`) are **Undefined**.
2. **x86 Vendor-Specific Differences (Intel vs. AMD):**
   - **`SYSCALL` / `SYSRET` in 32-bit mode:** Supported on AMD CPUs in legacy/compatibility mode; raises `#UD` on Intel CPUs outside 64-bit mode (`SYSENTER`/`SYSEXIT` is the Intel 32-bit counterpart).
   - **`BSF`/`BSR` and string instructions with `REX.W`:** Subtle differences in `RIP`-relative displacement wrapping and segment base treatment in 64-bit mode.
   - **Vendor-only extensions:** AMD `XOP`, `FMA4`, `TBM`, `3DNow!`, `SVM`, `SNP`; Intel `AMX` (`amx-tile`, `amx-int8`, `amx-bf16`, `amx-fp16`, `amx-complex`), `TSX`/`HLE`/`RTM`, `CET` (`IBT`/`SHSTK`), `TDX`, `APX`.
3. **Arm `IMPLEMENTATION DEFINED` and `CONSTRAINED UNPREDICTABLE` Behaviors:**
   - **SVE / SME Vector Length (`VL` / `SVL`):** Power-of-two multiple of 128 bits (`128..2048` bits); Neoverse V1 uses 256-bit SVE, Neoverse V2/N2 and Graviton4 use 128-bit SVE2, Fujitsu A64FX uses 512-bit SVE, and `qemu-aarch64 -cpu max` defaults to 512-bit (`64` bytes).
   - **Load-Exclusive / Store-Exclusive (`LDXR`/`STXR`) Reservations:** The reservation granule size (`4` words to `512` words, `CTR_EL0.ERG`) and which intervening instructions clear the monitor are `IMPLEMENTATION DEFINED` / `CONSTRAINED UNPREDICTABLE`.
   - **Overlapping registers in `LDP` (`ldp x0, x0, [x1]`) or writeback (`ldr x0, [x0], #8`):** Designated `CONSTRAINED UNPREDICTABLE` in Arm ARM; ASL models this via `Constraint_UNDEF` / `Constraint_NOP` / `Constraint_UNKNOWN` choice sets, and a verified compiler's encoder/verifier must reject such register combinations outright.

### 3. Silicon Errata and Compiler/Linker Workarounds in LLVM 23.1.1

Basis: source (`llvm/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)

A verified compiler or binary validator must know which silicon errata require codegen/linker transformations so that (a) errata-mitigation passes preserve semantic equivalence and (b) binary validators accept linker-patched veneers and NOP padding:

| Erratum / Vulnerability | Affected Hardware | LLVM 23.1.1 / LLD Source Implementation | Code Transformation & Verification Impact |
| :--- | :--- | :--- | :--- |
| **Intel Skylake JCC Erratum** (`SKX102`, Doc `338848-001US`) | Intel Skylake, Cascade Lake, Cooper Lake, Coffee Lake (Family 6, Model `0x4E`, `0x55`, `0x5E`, `0x8E`, `0x9E`) | `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp` (`-x86-branches-within-32B-boundaries`, `alignBranchesBegin`/`End`) | Inserts `NOP`s or `CS`/`DS` segment prefixes before macro-fused `CMP`/`TEST`+`Jcc` or `JMP`/`CALL`/`RET` instructions so they never cross or end on a 32-byte cache-line boundary. **Impact:** Increases instruction offsets during MC relaxation; NOPs are semantically identity transitions. |
| **Arm Cortex-A53 Erratum 835769** | Arm Cortex-A53 (r0p0–r0p4) | `llvm/lib/Target/AArch64/AArch64A53Fix835769.cpp` (`263` lines, `-aarch64-fix-cortex-a53-835769`) | A 64-bit multiply-accumulate (`MADD`, `MSUB`, `SMADDL`, `UMADDL`) immediately following a memory load/store/prefetch can produce an incorrect result. Pass inserts a `NOP` (`HINT #0`) between the memory instruction and the MAC instruction. |
| **Arm Cortex-A53 Erratum 843419** | Arm Cortex-A53 (r0p0–r0p4) | `lld/ELF/Arch/AArch64.cpp:688` (`--fix-cortex-a53-843419`, `AArch64Err843419Patcher`) | If an `ADRP` instruction sits at offset `0xFF8` or `0xFFC` of a 4 KiB page after aspecific sequence of loads/stores, `ADRP` can compute a corrupted address. **Linker-only fix:** Since page offsets `0xFF8`/`0xFFC` are unknown until final section layout, `lld` overwrites the `ADRP` in place with an unconditional `B <veneer>` to a synthetic thunk containing the relocated `ADRP` + `B <next_insn>`. **Crucial impact:** A post-link binary verifier (`Islaris` / `seL4 TV`) sees control flow jump out of the function body into a linker thunk and back! |
| **Arm Cortex-A57 FP Load Balancing** | Arm Cortex-A57 | `llvm/lib/Target/AArch64/AArch64A57FPLoadBalancing.cpp` (`742` lines) | Reassigns parity (even/odd register numbers) of temporary `D`/`S` floating-point registers in FP multiply-accumulate chains. |
| **Qualcomm Falkor Hardware Prefetcher Fix** | Qualcomm Falkor | `llvm/lib/Target/AArch64/AArch64FalkorHWPFFix.cpp` (`831` lines) | Avoids strided load tag collisions in Falkor's hardware prefetcher by rewriting base/index registers of strided `LDR` instructions. |
| **AArch64 Straight-Line Speculation (SLS)** (`CVE-2020-13844`) | Armv8-A cores speculating past unconditional branches / `RET` | `llvm/lib/Target/AArch64/AArch64SLSHardening.cpp` (`549` lines) | Appends `DSB SY; ISB` or `SB` speculation barriers after `RET`/`BR` and replaces `BLR` with `BL` to a `__llvm_slsblr_thunk_xN` stub. |
| **AArch64 BTI & PAC Landing Pads** | Armv8.5-A+ (`FEAT_BTI`, `FEAT_PAuth`) | `llvm/lib/Target/AArch64/AArch64BranchTargets.cpp` (`196` lines) & `lld/ELF/Arch/AArch64.cpp:32-63` | Inserts `BTI c` (`0xd503245f`), `BTI j` (`0xd503249f`), `BTI jc` (`0xd50324df`), or `PACIASP`/`PACIBSP` (`0xd503233f`/`0xd503237f`) at indirect branch targets; `lld` synthesizes BTI-enabled PLT stubs when `GNU_PROPERTY_AARCH64_FEATURE_1_BTI` is set. |
| **x86 Load Value Injection (LVI) & Speculative Load Hardening (SLH)** | Intel SGX / affected Core & Xeon CPUs | `X86LoadValueInjectionLoadHardening.cpp` (`845` lines), `X86LoadValueInjectionRetHardening.cpp` (`133` lines), `X86SpeculativeLoadHardening.cpp` (`2,290` lines) | Inserts `LFENCE` after loads or replaces `RET` with `POP rcx; LFENCE; JMP *rcx` (LVI) or tracks predicate state in a GPR mask ORed into pointers (SLH). |

### 4. Hardware and Emulator Resource Matrix for Extension Validation

Basis: execution + documentation

To plan continuous and release validation of the trusted ISA models across all Tier 1 extensions, the table below maps each ISA extension to concrete cloud instances, devices, and emulators:

| ISA Extension Family | Cloud Instance Types (AWS / GCP / Azure) | Local / Edge Devices | Emulator Coverage & Fidelity |
| :--- | :--- | :--- | :--- |
| **x86-64 Base, BMI1/2, ADX, AVX2, FMA, AES, SHA-NI, VAES, VPCLMULQDQ, GFNI** | **Available on current Cloudtop host** (`GenuineIntel` Ice Lake-SP Model 106); AWS `c6i`/`m6i`, GCP `n2`/`c3`, AMD `c6a`/`c7a` (`n2d`/`c3d`) | Intel 11th Gen+ (Rocket Lake / Alder Lake+), AMD Zen 3 / Zen 4+ | `qemu-x86_64 -cpu max` (`11.1.2`): high functional fidelity for integer/crypto, **diverges on `RCPSS`/`RSQRTSS` approximations** |
| **AVX-512 (`F, BW, DQ, VL, CD, IFMA, VBMI, VBMI2, VNNI, BITALG, VPOPCNTDQ`)** | **Available natively on current Cloudtop host** (verified in `support/hardware_validation_results.json`!); AWS `c6i`, GCP `n2` (Ice Lake) / `c3` (Sapphire Rapids) | Intel Xeon W / Server; AMD Ryzen 7000/9000 (Zen 4 / Zen 5) | `qemu-x86_64 -cpu max` (`11.1.2` supports AVX-512 in TCG) |
| **AVX-512 `FP16` & Intel `AMX` (`amx-tile`, `amx-int8`, `amx-bf16`, `amx-fp16`, `amx-complex`)** | AWS `c7i` / `m7i` / `r7i` (Sapphire Rapids / Emerald Rapids), GCP `c3` / `c4` | Intel Xeon Scalable 4th/5th/6th Gen (Sapphire/Emerald/Granite Rapids) | `qemu-x86_64 -cpu max` (`11.1.2` models AMX tile registers `tmm0..tmm7` and AVX-512 FP16) |
| **Intel `AVX10.1`/`AVX10.2` and `APX` (32 GPRs `r16..r31`, `REX2`, `NDD`)** | Upcoming Granite Rapids (`AVX10.1`) / Diamond Rapids (`AVX10.2` + `APX`) instances | Pre-silicon / initial server silicon | QEMU 11.1.2 TCG (partial APX/AVX10 support); Intel SDE (requires proprietary license — **do not use under automated click-through EULA restriction**) |
| **AArch64 Base, NEON, LSE, Crypto (`AES`, `PMULL`, `SHA2`, `SHA3`), DotProd, FP16/BF16, RCPC, PAC, BTI** | AWS `c6g` (Graviton2: v8.2-A + LSE/CRC), `c7g` (Graviton3: v8.4-A + SVE-256 + BF16 + I8MM + RNG + PAuth + BTI), `c8g` (Graviton4: v9.0-A + SVE2-128 + LSE2); GCP `t2a` (Ampere Altra), `c4a` (Google Axion / Neoverse V2: v9.0-A + SVE2 + BTI + PAC) | Apple M1/M2/M3/M4 (Armv8.5-A..v9.2-A + PAC + BTI + AMX/SME on M4) | `qemu-aarch64 -cpu max` (`11.1.2`): **verified in `support/hardware_validation_results.json`** (`LSE`, `AES`/`PMULL`, `SVE` 512-bit, `PACDA`/`AUTDA`, `BTI c`); Arm Fixed Virtual Platforms (FVP Base RevC) |
| **AArch64 `SVE` / `SVE2` / `SME` / `SME2` / `MTE`** | AWS `c7g` (SVE 256-bit), AWS `c8g` and GCP `c4a` (SVE2 128-bit) | Apple M4 (`SME` / `SME2`), Google Pixel 8 / Pixel 9 (Tensor G3/G4: `Armv9-A` with hardware **`MTE`** Memory Tagging Extension) | `qemu-aarch64 -cpu max` (`11.1.2` supports SVE, SVE2, SME, and MTE tag checking in user/system mode); Arm FVP (gold reference running Arm's official ASL model) |

## Boundaries

- **Intel SDE EULA boundary (`not examined`):** Intel Software Development Emulator (SDE) requires accepting the proprietary Intel Simplified Software License click-through gate and was intentionally not downloaded or executed per project compliance policy. All x86-64 (including AVX-512) and i686 validation probes were executed natively on the host Intel Xeon Ice Lake-SP CPU and cross-checked against open-source `qemu-i386` / `qemu-aarch64` 11.1.2.
- **Multi-core weak-memory hardware litmus stress (`not examined` in this run):** The hardware probes in `support/run_hardware_validation_probes.py` test single-thread sequential instruction semantics, flags, and atomic RMW functional results (`CASAL`, `LDADDAL`); multi-thread relaxed-memory litmus testing (`litmus7` / `herd7`) is covered in the memory-model track (`Run 03`).

## Evidence

1. **Executable Multi-Architecture Validation Harness and Recorded Hardware/Emulator Outputs:**
   - Script: `support/run_hardware_validation_probes.py`.
   - Recorded JSON results: `support/hardware_validation_results.json`.
   - Executed on 2026-11-13 using `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rust-lld`, `qemu-i386 11.1.2`, `qemu-aarch64 11.1.2`, and native Intel Xeon Ice Lake-SP (`GenuineIntel`, Family 6, Model 106, Stepping 6).
2. **LLVM 23.1.1 and LLD Errata Workaround Sources:**
   - Repository: `llvm/llvm-project`, revision `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`.
   - `llvm/lib/Target/AArch64/AArch64A53Fix835769.cpp:1-125` (Cortex-A53 erratum 835769 NOP insertion pass).
   - `lld/ELF/Arch/AArch64.cpp:32-63` (`isAArch64BTILandingPad` checking `PACIASP` `0xd503233f`, `PACIBSP` `0xd503237f`, `BTI c` `0xd503245f`, `BTI j` `0xd503249f`, `BTI jc` `0xd50324df`) and `688` (Cortex-A53 erratum 843419 linker patcher).
   - `llvm/lib/Target/AArch64/AArch64A57FPLoadBalancing.cpp`, `AArch64FalkorHWPFFix.cpp`, `AArch64SLSHardening.cpp`, `AArch64BranchTargets.cpp:1-120`.
   - `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp`, `X86LoadValueInjectionLoadHardening.cpp`, `X86LoadValueInjectionRetHardening.cpp`, `X86SpeculativeLoadHardening.cpp`.

## Revalidation

To rerun the hardware and QEMU differential validation probes on any Linux x86-64 host with `rustc` and `qemu-user` installed:

```console
OUT_DIR=/tmp/isa_val python3 \
  reports/isa-model-hardware-validation-divergences-errata-and-resources/support/run_hardware_validation_probes.py
```

Compare the generated `/tmp/isa_val/m9_hardware_validation_results.json` against `support/hardware_validation_results.json` to detect any microarchitectural differences (for example, AMD Zen vs. Intel Ice Lake `RCPSS`/`RSQRTSS` lookup tables or newer QEMU SVE/PAC defaults).
