# Armv9 SME2 Streaming and Lazy-ZA Protocols, WebAssembly Relaxed-SIMD Relational Nondeterminism, and Cross-Platform Callee-Saved Vector ABIs

## Summary

Relational ISA refinement and calling-convention verification for multi-target SIMD and matrix DSP kernels must discharge three hardware-to-ABI contracts omitted from pure register-transfer models:

1. **Armv9 `SME` / `SME2` Edge-Triggered Resets, `TPIDR2_EL0` Lazy `ZA` Ownership, and `ZT0` Volatility (`Basis: normative + source + documentation + execution`):**
   In `rems-project/sail-arm@5416ef6b43e9527c38dc71fb752259c1d01a47e1` (`arm-v9.4-a/src/v8_base.sail:9504-9513, 29606-29639`), `SetPSTATE_SM(v)` calls `ResetSVEState()` **iff `PSTATE.SM != v`** (zeroing `_Z[0..31]`, `_P[0..15]`, `_FFR`, and setting `FPSR` to **`0x0800009f`**, which forces `FPSR.QC = 1` and all six FP cumulative exception flags to `1`), while `SetPSTATE_ZA(v)` calls `ResetSMEState()` **iff `PSTATE.ZA != v`** (zeroing `_ZA[0..255]` and 512-bit `_ZT0`). Under `AAPCS64` (`ARM-software/abi-aa@9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`, `aapcs64/aapcs64.rst:1063-1802, 2636-2727`), a caller with live `ZA` may enter a `private-ZA` callee in **dormant** state (`PSTATE.ZA == 1, TPIDR2_EL0 == &BLK != 0`). Executing bare `smstart` without committing `TPIDR2_EL0` (`__arm_tpidr2_save(); TPIDR2_EL0 = 0`) and explicit **`zero {za}`** (`instrs64_sme.sail:4109-4123`) fails twice: `SetPSTATE_ZA(1)` is a no-op when `PSTATE.ZA == 1` (accumulating onto caller `ZA` bytes), and `smstop` clears `PSTATE.ZA := 0` while leaving `TPIDR2_EL0 == &BLK` (causing the caller to skip `__arm_tpidr2_restore` and fault with `SMEExceptionType_InactiveZA`). Furthermore, `AAPCS64` (`aapcs64.rst:989-990, 1795-1801`) defines SME2's 512-bit **`ZT0` register as caller-saved and excluded from `__arm_tpidr2_save`**, whereas `__arm_sme_save`/`__arm_sme_restore` (`compiler-rt/lib/builtins/aarch64/sme-abi.S:219-250`) preserves both `ZA` and `ZT0`.
2. **WebAssembly 3.0 `relaxed-simd` Relational Nondeterminism and Three Cross-Engine Divergences (`Basis: normative + source + execution`):**
   Wasm 3.0 (`WebAssembly/spec@d0b2e8d5544d2049fba0521922c436e3f0fcaebe`, `document/core/exec/numerics.rst:2340-2594`) defines 20 `relaxed-simd` opcodes (`0xfd 0x100..0x113`) over host profile parameters $\mathbf{R}$. Auditing `numerics.rst`, `eval_vec.ml`, `bytecodealliance/wasmtime@40e0d780e4bfa34325d342db5bcf492bea227e07`, and live V8 execution (`Node.js v24.21.0` on `x86_64`) exposes three hazards: (a) **V8 `x86_64` `i16x8.relaxed_laneselect` (`0xfd 0x10a`) lowers directly to 8-bit `pblendvb`**, returning **`0xFF00`** on `(0xFFFF, 0x0000, 0x8001)`—outside Wasm 3.0's allowed `{0x8001, 0xFFFF}`—while Cranelift (`x64/mod.rs:196-202`) selects $R = 0$ on `i16x8` vs. $R = 1$ on `i8x16`/`i32x4`/`i64x2`; (b) **deterministic-profile `relaxed_madd` (`0xfd 0x105`) contradicts itself**, with `numerics.rst:2360, 2366` specifying unfused double rounding (`0x00000000`) while `eval_vec.ml:130` and `wasmtime` `func_environ.rs:6380` evaluate fused `fma` (`0x28800000`); and (c) **`relaxed_min/max` (`0xfd 0x10d..0x110`) is non-commutative on `x86_64` (`MINPS`, $R=2$)** and leaks raw uncanonicalized NaN payloads (`0x7fc05678`).
3. **Sub-Register Partial-Width Callee-Save Lenses Across `Win64`, `SysV AMD64`, and `AAPCS64` (`Basis: normative + source + execution`):**
   Callee-save ABI contracts project asymmetric sub-register slices: `SysV AMD64` saves **0 vector bits**; `Microsoft Win64` (`CSR_Win64` in `X86CallingConv.td:1110-1111`, verified via `gcc 15.2.0 -O2 -mavx2`) saves **`xmm6`–`xmm15` bits `[127:0]` only** (`160` B + `UWOP_SAVE_XMM128`), leaving `ymm6..15[255:128]`, `zmm6..15[511:128]`, `zmm16..31`, and `k0..7` volatile while requiring `vzeroupper`; and `AAPCS64` (`aapcs64.rst:896-955`) saves **`d8`–`d15` (`[63:0]`)** in Base PCS, **`q8`–`q15` (`[127:0]`)** in `aarch64_vector_pcs`, and **full `z8`–`z23` `[VL-1:0]` + `p4`–`p15` `[PL-1:0]`** in SVE PCS, with `FPSR.QC` volatile across C calls yet preserved under Rust `asm!(..., options(preserves_flags))`.

---

## Applicability

This report governs relational ISA refinement, determinism preconditions, and binary ABI verification across Rust (`core::arch`, `asm!`, external GAS/NASM), C/C++, and WebAssembly (`wasm32`/`wasm64`), anchored to ten pinned primary subjects:

- **`ARM-software/abi-aa`** (`9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`, `aapcs64/aapcs64.rst`), **`rems-project/sail-arm`** (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`, Armstrong et al., POPL 2019 `doi:10.1145/3290384`), and **`torvalds/linux`** (`f1715c0c04606ebbe832cc760abf49dfd6f2ae1f`, `Documentation/arch/arm64/sme.rst`);
- **`WebAssembly/spec`** (`d0b2e8d5544d2049fba0521922c436e3f0fcaebe`, Youn et al., *SpecTec*, PLDI 2024 `doi:10.1145/3656440`), **`WebAssembly/relaxed-simd`** (`c3f9359af2cd607cc46b0a3274f90ea52543a2f2`), **`bytecodealliance/wasmtime`** (`40e0d780e4bfa34325d342db5bcf492bea227e07`), and **Node.js `v24.21.0`** (`V8` on Linux `x86_64`);
- **`llvm/llvm-project`** (`f61dfd8c0d8cfa6ed8a1ea3a16174d9673184825`), **`awslabs/s2n-bignum`** (`280a220986a0bc6249248187717a771153d073db`), **`FFmpeg/FFmpeg`** (`e8574d0b22b126acc76007babce536c68bc07d0a`), and System V AMD64 / Microsoft x64 ABI specifications.

**Companion corpus cross-references:** Object-level EVEX/SME2 lifting (`avx512-evex-opmask-and-arm-sve2-sme2-scalable-vector-pass2-formalization`), RVV `LMUL`/fault-only-first hazards (`rvv-lmul-vtype-hazards-arm-sme-streaming-za-tiles-and-ffload-speculation`), `WasmCert` kernel opacity (`riscv-rvv-ppc-vsx-loongarch-and-wasm-simd-isa-formalizations`), and Rust `asm!` `X86InsertVZeroUpper`/Tree Borrows contracts (`rust-inline-asm-and-external-asm-abi-seams-in-formal-verifiers`) are covered in their respective packages. This report unifies SME2 `TPIDR2_EL0`/`ZT0`/`FPSR` typestate, Wasm 3.0 `relaxed-simd` relational refinement and engine divergences, and cross-ABI sub-register projection lenses.

---

## Findings

### 1. Armv9 `SME` / `SME2` Streaming Mode, `TPIDR2_EL0` Lazy `ZA` Automaton, `ZT0` Volatility, and `zero {za}`

`Basis: normative + source + documentation + execution`

#### 1.1 Exact `sail-arm` State Transitions (`SetPSTATE_SM`, `SetPSTATE_ZA`, `FPSR`, and `ZERO {za}`)

At `EL0`, Armv9 `FEAT_SME` and `FEAT_SME2` add `SVCR` (`PSTATE.SM` bit `0`, `PSTATE.ZA` bit `1`), power-of-two Streaming Vector Length $\text{SVL} \in \{128, 256, 512, 1024, 2048\}$ bits ($\text{SVL}_B = \text{SVL}/8$ bytes), matrix array `_ZA : vector(256, bits(2048))` ($\text{SVL}_B \times \text{SVL}_B$ active bytes, `256 B` to `64 KiB`), and `SME2`'s 512-bit lookup-table register `_ZT0 : bits(512)` (`rems-project/sail-arm@5416ef6b43e9527c38dc71fb752259c1d01a47e1`, `arm-v9.4-a/src/v8_base.sail:2710-2726, 6936, 9504-9513, 29525-29639`):

```sail
function ResetSVEState () = {
    foreach (n from 0 to 31 by 1 in inc) { _Z[n] = Zeros(MAX_VL) };
    foreach (n from 0 to 15 by 1 in inc) { _P[n] = Zeros(MAX_PL) };
    _FFR = Zeros(MAX_PL);
    FPSR = Mk_FPSR_Type(ZeroExtend(0x0800009f, 64))
}
function ResetSMEState () = {
    let 'vectors_name = DIV(MAX_VL, 8);
    foreach (n from 0 to (vectors_name - 1) by 1 in inc) { _ZA[n] = Zeros(MAX_VL) };
    _ZT0 = Zeros(ZT0_LEN)
}
function SetPSTATE_SM v = { if PSTATE.SM != v then { ResetSVEState(); PSTATE.SM = v }; () }
function SetPSTATE_ZA v = { if PSTATE.ZA != v then { ResetSMEState(); PSTATE.ZA = v }; () }
```

Three operational consequences control soundness:
1. **Edge-Triggered `SetPSTATE_ZA` (`PSTATE.ZA != v`):** `SMSTART ZA` (and `SMSTART`) zeroes `_ZA` and `_ZT0` **only on a `0 -> 1` edge**. Entering `SMSTART` when `PSTATE.ZA` is already `1` **preserves existing `_ZA` and `_ZT0` bits verbatim**.
2. **`FPSR := 0x0800009f` Poison on Every `PSTATE.SM` Flip (`v8_base.sail:9512`):** Toggling `PSTATE.SM` (`0 <-> 1`) zeroes all `_Z[0..31]` (aliasing `v0..31` / `d0..31`), `_P[0..15]`, and `_FFR`, **and writes `0x0800009f` into `FPSR`**—setting bit 27 (`QC = 1`) plus `IDC, IXC, UFC, OFC, DZC, IOC = 1` to decouple out-of-order streaming pipelines from scalar FPU exception flags.
3. **Interleaved Tile Zeroing (`execute_ZERO_ZA_I__`, `instrs64_sme.sail:4109-4123`):** `zero {za}` (`imm8 = 0xFF`) clears all eight 64-bit tile views `ZAvector[i + 8s]` ($\forall i \in [0,7], s < \text{SVL}_B/8$), covering all $\text{SVL}_B$ horizontal slices without touching `_ZT0` (cleared separately via `zero {zt0}`).

#### 1.2 Relational Typestate of `AAPCS64` `TPIDR2_EL0`, `compiler-rt` `sme-abi.S`, and `ZT0`

`AAPCS64` (`aapcs64.rst:1375-1805, 2480-2755`) crosses streaming mode (`Normal` `SM == 0`, `__arm_streaming` `SM == 1`, `__arm_streaming_compatible` `SM == sm_0`) with SME state ownership:
- **`private-ZA` (default on unannotated C/Rust functions):** Entered in either `Off` (`PSTATE.ZA == 0, TPIDR2_EL0 == 0`) or `Dormant` (`PSTATE.ZA == 1, TPIDR2_EL0 == &BLK != 0`, where `BLK` is `{ void *za_save_buffer; uint16_t num_za_save_slices; uint8_t reserved[6] == 0; }`, `aapcs64.rst:1380-1398`). `ZA`-unaware callees return in `O(1)` with `0` copies. Any `private-ZA` callee touching `ZA` (`__arm_new("za")` or handwritten `.S` like `FFmpeg` `inter_sme2.S`) **must**:
  1. **Commit dormant caller `ZA` before `smstart`:** `if (TPIDR2_EL0 != 0) { __arm_tpidr2_save(); TPIDR2_EL0 = 0; }` (`aapcs64.rst:2648-2652`; `compiler-rt/lib/builtins/aarch64/sme-abi.S:116-155` checks `BLK[10..15] == 0`—aborting on nonzero reserved bytes—and loops `str za[w15, 0], [x16]; addsvl x16, x16, #1`).
  2. **Execute explicit `zero {za}` after `smstart` before accumulating (`SDOT`/`FMOPA`):** Because `Dormant` entry has `PSTATE.ZA == 1`, `smstart` leaves caller `ZA` intact in `_ZA` (`inter_sme2.S:124` omitting both `TPIDR2_EL0` commit and prologue `zero {za}` corrupts strip-0 accumulation *and* wipes `PSTATE.ZA := 0` at `smstop` while `TPIDR2_EL0 == &BLK`, tricking the caller into skipping `__arm_tpidr2_restore` and trapping on `SMEExceptionType_InactiveZA`!).
  3. **Preserve signal/unwind-safe disable ordering (`aapcs64.rst:1472-1473`, `sme-abi.S:185-188`):** Always execute **`msr TPIDR2_EL0, xzr` BEFORE `smstop za`**. Reversing that pair creates a 1-instruction asynchronous signal window (`linux/Documentation/arch/arm64/sme.rst:108-162`) where signal delivery records `PSTATE.ZA == 0` with `TPIDR2_EL0 == &BLK`, causing C++/Rust unwinders or `longjmp` to restore uninitialized stack memory!
- **SME2 `ZT0` Exclusion From Lazy Save (`aapcs64.rst:265, 989-990, 1795-1801` vs. `2480-2596`):**
  Even though `PSTATE.ZA == 0` hardware-zeroes `_ZT0`, **`AAPCS64` defines `ZT0` as caller-saved and excluded from `TPIDR2_EL0` lazy saving (`"ZT0 is therefore not handled by the lazy save scheme"`, `L1801`)**. If a caller sets up `TPIDR2_EL0 = &BLK` and calls a `private-ZA` function that commits `ZA` and runs `smstop za`, `__arm_tpidr2_restore(&BLK)` restores `ZA` **while `ZT0` returns zeroed**! Callers with live `ZT0` must spill `str zt0, [sp_slot]` eagerly unless calling `__arm_preserves("zt0")` or `__arm_agnostic("sme_za_state")` (`__arm_sme_save`/`__arm_sme_restore` in `sme-abi.S:219-250`, saving `ZT0` at `@32` when `__arm_sme_routines_support_zt0` is linked). Furthermore, Linux `svc #0` clears `PSTATE.SM := 0` on every syscall (`sme.rst:87-91`).

---

### 2. WebAssembly 3.0 `relaxed-simd` Relational Nondeterminism and Cross-Engine Divergences

`Basis: normative + source + execution`

#### 2.1 Complete Relational Semantics and Bit-Exact Determinism Domains (`numerics.rst:2340-2594`)

Wasm 3.0 `relaxed-simd` (`0xfd 0x100..0x113`; Youn et al., *SpecTec*, `doi:10.1145/3656440`) parameterizes instructions over host profile choices $\mathbf{R}$. A kernel preserves bit-exact portable equivalence (`SIMD_wasm ⊑ Spec_scalar`) iff inputs stay within $\text{Det}_{\text{op}} = \{\vec{x} \mid |\llbracket \text{op} \rrbracket(\vec{x})| = 1\}$; otherwise proofs must quantify over $\forall \mathbf{R}$:

| Opcode (`0xfd`+) | Instruction(s) | Wasm 3.0 Relational Image (`numerics.rst:2349-2594`) | `x86_64` vs. `AArch64` Lowering | Bit-Exact Precondition $\text{Det}_{\text{op}}$ |
| :--- | :--- | :--- | :--- | :--- |
| `0x100` | `i8x16.relaxed_swizzle(a, j)` | `a[j_k]` ($j_k < 16$); `0` ($j_k \ge 128$); else $\{0, a[j_k \bmod 16]\}$ ($R_{\mathsf{swizzle}}$) | `x86` `PSHUFB` ($R=1$); `Arm` `TBL` ($R=0$) | $\forall k,\; j_k \in [0, 15] \cup [128, 255]$ |
| `0x101`, `0x103` | `i32x4.relaxed_trunc_{f32x4_s, f64x2_s_zero}` | $\operatorname{trunc}(z)$ if finite $\in [-2^{31}, 2^{31})$; else $\{\operatorname{trunc\_sat\_s}(z), -2^{31}\}$ | `x86` `CVTTP*2DQ` (`-2^{31}` sentinel); `Arm` `FCVTZS` (`0` on NaN, `+2^{31}-1` on $+\text{ovf}$) | $\forall k,\; \neg\operatorname{isNaN}(z_k) \land -2^{31} \le \operatorname{trunc}(z_k) \le 2^{31}-1$ |
| `0x102`, `0x104` | `i32x4.relaxed_trunc_{f32x4_u, f64x2_u_zero}` | $\operatorname{trunc}(z)$ if finite $\in [0, 2^{32})$; else $\{\operatorname{trunc\_sat\_u}(z), 2^{32}-1\}$ | `Arm` `FCVTZU` (`0` on $<0$/NaN); `AVX-512` `VCVTTP*2UDQ` (`2^{32}-1`) | $\forall k,\; \neg\operatorname{isNaN}(z_k) \land 0 \le \operatorname{trunc}(z_k) \le 2^{32}-1$ |
| `0x105`–`0x108` | `f{32x4,64x2}.relaxed_{madd,nmadd}(a, b, c)` | $\{\operatorname{rn}(\operatorname{rn}(\pm ab)+c),\, \operatorname{fma}(\pm a, b, c)\}$ ($R_{\mathsf{fmadd}} \in \{0,1\}$) | `Arm` `FMLA` & `x86+FMA` `VFMADD*` ($R=1$); SSE2 `MULP*+ADDP*` ($R=0$) | Exact product $\pm a_k b_k$ in float $\land$ no `NaN` |
| `0x109`–`0x10c` | `i{8x16..64x2}.relaxed_laneselect(a, b, m)` | Spec: $\operatorname{bitselect}(a, b, m)$ ($R=0$) or MSB-replicated $\operatorname{sext}(\operatorname{msb}_N(m))$ ($R=1$) | `Arm` `BSL` ($R=0$); `x86` `PBLENDVB`/`BLENDVP*` ($R=1$; **V8 `i16x8` bug below!**) | $\forall k,\; m_k \in \{0,\, 2^N - 1\}$ (or $a_k = b_k$) |
| `0x10d`–`0x110` | `f{32x4,64x2}.relaxed_{min,max}(a, b)` | $R_{\mathsf{fmin/fmax}} \in \{0..3\}$: $\{\text{qNaN}, a, b\}$ on NaN; $\{\mp 0, a, b\}$ on $\{\pm 0, \mp 0\}$ | `x86` `MINPS`/`MAXPS` (`b < a ? b : a` $\to$ returns `b`, $R=2$); `Arm` `FMIN`/`FMAX` ($R \in \{0,1\}$) | $\forall k,\; \text{no NaN} \land \neg(a_k = 0 \land b_k = 0 \land \operatorname{sign}(a_k) \ne \operatorname{sign}(b_k))$ |
| `0x111` | `i16x8.relaxed_q15mulr_s(a, b)` | $\lfloor (a_k b_k + 2^{14})/2^{15} \rfloor$, except $(-32768)^2 \mapsto \{+32767, -32768\}$ | `Arm` `SQRDMULH` (`+32767`, $R=0$); `x86` `PMULHRSW` (`-32768`, $R=1$) | $\forall k,\; \neg(a_k = -32768 \land b_k = -32768)$ |
| `0x112`, `0x113` | `i16x8.relaxed_dot_i8x16_i7x16_s`, `i32x4..._add_s` | Exact signed dot when $b_j < 128$ ($\sum \in [-32512, 32258]$); signed/unsigned + `i16` sat diverge if $b_j \ge 128$ | `x86` `PMADDUBSW` (treats $b$ unsigned, saturates `i16`); `Arm` `SDOT`/widening (signed) | $\forall j \in [0, 15],\; 0 \le b_j \le 127$ (`b_j & 0x80 == 0`) |

#### 2.2 Three Verified Cross-Spec / Cross-Engine Divergences

1. **V8 `x86_64` `i16x8.relaxed_laneselect` (`0xfd 0x10a`) Emits 8-Bit `PBLENDVB` Outside Wasm 3.0's Spec:**
   In `numerics.rst:2574-2588`, $\mathsf{irelaxed\_laneselect}_{16}(\texttt{0xFFFF}, \texttt{0x0000}, \texttt{0x8001})$ permits **only** `0x8001` ($R = 0$) or `0xFFFF` ($R = 1$). Because SSE4.1/AVX2 has 8-bit `PBLENDVB`, 32-bit `BLENDVPS`, and 64-bit `BLENDVPD` **but no 16-bit MSB blend**, V8 (`Node.js v24.21.0`) emits `PBLENDVB` directly without `PSRAW m, 15`, returning **`0xFF00`** on `0x8001` and **`0x00FF`** on `0x7FFE`—violating `numerics.rst:2587` whenever `m[7] != m[15]`! Meanwhile, Cranelift (`wasmtime` `cranelift/codegen/src/isa/x64/mod.rs:196-202`) checks `self.x64_flags.has_sse41() && ty != types::I16X8`, using $R = 0$ on `i16x8` and $R = 1$ on `i8x16`/`i32x4`/`i64x2`, proving `numerics.rst:2577` requires width-indexed $R_{\mathsf{laneselect}, N}$ rather than a single scalar $R_{\mathsf{laneselect}}$.
2. **Deterministic Profile Contradiction on `relaxed_madd` (`numerics.rst:2366` vs. `eval_vec.ml:130` & `wasmtime`):**
   `numerics.rst:2360, 2366-2367` places **unfused** `fadd(fmul(z1, z2), z3)` at deterministic index `0`, yet `WebAssembly/spec`'s own `interpreter/exec/eval_vec.ml:130` (`F32x4 RelaxedMadd -> V128.F32x4.fma`) and `wasmtime`'s `relaxed_simd_deterministic()` (`func_environ.rs:6380-6385`) evaluate **fused** `fma` (`0x28800000` = $+2^{-46}$ vs. unfused `0x00000000` = $+0.0$ on $a = b = 1 + 2^{-23}, c = -(1 + 2^{-22})$).
3. **Non-Commutativity & NaN-Payload Passthrough on `relaxed_min/max` (`0xfd 0x10d`):**
   On `x86_64` (`MINPS`, $R_{\mathsf{fmin}} = 2$), V8 maps `(qNaN(0x7fc01234), 1.0) -> 1.0` (`0x3f800000`), `(1.0, qNaN(0x7fc05678)) -> 0x7fc05678` (uncanonicalized payload), `(-0.0, +0.0) -> +0.0`, and `(+0.0, -0.0) -> -0.0`, refuting `relaxed_min(a, b) == relaxed_min(b, a)`.

---

### 3. Cross-Platform Callee-Saved Vector ABIs and Sub-Register Lens Contracts

`Basis: normative + source + derived + execution`

At FFI and assembly boundaries, callee-save preservation is a sub-register projection $\pi_{\text{ABI}}(\sigma_{\text{vec}})$ over 512-bit `ZMM` or 2048-bit `_Z` banks (`X86CallingConv.td:1098-1170`; `aapcs64.rst:896-991`; `s2n-bignum` `x86/proofs/mlkem_ntt.ml:1345-1427`, `arm/proofs/mlkem_ntt.ml:552-554`):

| Calling Convention | Callee-Saved Vector Projection $\pi_{\text{ABI}}(\text{Vec})$ | Volatile Vector / Matrix / Mask State | Control & Status Register Exit Contract |
| :--- | :--- | :--- | :--- |
| **`SysV AMD64`** (`sysv64`) | **$\emptyset$ (`0` vector bits; GPRs `rbx, rbp, r12..r15` only)** | All `xmm0..15`, `ymm0..15`, `zmm0..31` `[511:0]`, `k0..k7` | `MXCSR[15:6]` preserved (`[5:0]` volatile); `DF == 0`; **`vzeroupper`** if `ymm0..15`/`zmm0..15` dirtied |
| **`Microsoft Win64`** (`win64`, `__vectorcall`) | **`xmm6..xmm15` bits `[127:0]` ONLY** (`160` B, `CSR_Win64`) | `xmm0..5[127:0]`, **`ymm0..15[255:128]`**, **`zmm0..15[511:256]`**, **`zmm16..31`**, `k0..k7` | `MXCSR[15:6]`, `DF == 0`, `vzeroupper`, plus 16B-aligned SEH `UNWIND_INFO` (`UWOP_SAVE_XMM128`) |
| **`AAPCS64 Base PCS`** (`extern "C"`) | **`v8..v15` bits `[63:0]` (`d8..d15`) ONLY** (`64` B) | `v0..7`, `v16..31`, **`v8..15[127:64]`**, **`z0..31[VL-1:128]`**, `p0..15`, `FFR`, `ZT0`; `private-ZA` | `sp % 16 == 0`; `x18` untouched; `FPCR` (`NEP == 0`) preserved; **`FPSR.QC` volatile**; `SM == 0` |
| **`AAPCS64 Vector PCS`** (`aarch64_vector_pcs`) | **`v8..v15` bits `[127:0]` (`q8..q15`)** (`128` B; GPRs `x19..x28`) | `v0..7`, `v16..31[127:0]`, **`z0..31[VL-1:128]`**, `p0..15`, `FFR`, `ZT0` | Same `FPCR` / volatile `FPSR.QC` / `SM == 0` / `private-ZA` rules |
| **`AAPCS64 SVE PCS`** (SVE `sv*` sigs) | **Full `z8..z23` `[VL-1:0]` AND `p4..p15` `[PL-1:0]`** | `z0..7`, `z24..31`, `p0..3`, `FFR`, `ZT0` | Entering `SMSTART SM` (`__arm_locally_streaming`) wipes `z8..23` + `p4..15`, requiring full scalable spills! |
| **`AAPCS64 SME `__arm_streaming`** | `z8..23[SVL-1:0]` + `p4..15[SVL/8-1:0]` (SVE sig) or `d8..15` | `z0..7`, `z24..31`, `p0..3`, `FFR`; `ZT0` unless `__arm_preserves("zt0")` | Entered/exited with `SM == 1`; if `shared-ZA`, `ZA == 1 ∧ TPIDR2_EL0 == 0` |

Three concrete epilogue invariants follow:
1. **Win64 Partial-Width Save + `vzeroupper` (`gcc 15.2.0 -O2 -mavx2` & `FFmpeg` `x86inc.asm:560-622`):** Clobbering `ymm7` on `ms_abi` spills only 16-byte `xmm7` (`vmovaps [rbp-0x10], xmm7`) and executes `vzeroupper` before `vmovaps xmm7, [rbp-0x10]`. Restoring `xmm6..15` with legacy non-VEX `movaps` *without* `vzeroupper` leaves `ymm6..15[255:128]` dirty; in HOL Light / Lean 4 (`s2n-bignum` `mlkem_ntt.ml:1347-1356`), the exact Win64 postcondition pairs $\forall r \in [6, 15],\, \sigma'.\text{zmm}(r)[127:0] = \sigma.\text{zmm}(r)[127:0]$ with $\forall r \in [0, 15],\, \sigma'.\text{zmm}(r)[511:128] = 0$.
2. **`AAPCS64` `d8`–`d15` Clobber on Bare `smstart`/`smstop`:** `FFmpeg`'s `ff_aarch64_sme_length` (`libavutil/aarch64/cpu_sme.S:26-31`: `smstart; cntb x0; smstop; ret`) zeroes `d8..d15` via `ResetSVEState()` without saving them (`rdsvl x0, #1; ret` avoids touching `SVCR` entirely).
3. **`FPSR.QC` C-ABI Volatility vs. Rust `asm!(options(preserves_flags))`:** While `extern "C"` callees may freely set `FPSR.QC := 1` (via NEON `SQADD`/`SQRDMULH`/`SQXTN`, SVE2 `SQRSHR`, or `SMSTART SM`'s `0x0800009f`), Rust's `options(preserves_flags)` on AArch64 asserts invariance of **both `NZCV` and `FPSR`** and must never be attached to saturating or streaming-mode `asm!` blocks.

---

## Boundaries

1. **Physical Armv9 `SME2` Silicon & `AArch64` Wasm JIT Execution (`not examined` on native Arm hardware):**
   `SME2` transitions were verified directly against `sail-arm@5416ef6b43e9527c38dc71fb752259c1d01a47e1`, `compiler-rt` `sme-abi.S`, `aapcs64.rst`, and an exhaustive Python state-machine checker, while `gcc 15.2.0` and `Node.js v24.21.0` ran on Linux `x86_64`; physical Apple M4 / Cortex-X925 execution was **not examined**.
2. **Intel `AMX` (`tmm0`–`tmm7`) and `AVX10.2` (`not examined`):**
   x86-64 `AMX` tile configuration (`LDTILECFG`, `TILERELEASE`, `XCR0[18:17]`) is orthogonal to `XMM`/`YMM`/`ZMM` ABI preservation and was **not examined**.
3. **Prover-Kernel Mechanization of Wasm `relaxed-simd` in `WasmCert` (`unsupported`):**
   `WasmCert-Isabelle` and `WasmCert-Coq` leave `v128` operators uninterpreted and omit Wasm 3.0 `relaxed-simd` (`unsupported`).
4. **Assuming Width-Uniform $R_{\mathsf{laneselect}}$ or Commutative `relaxed_min/max` (`known not to apply`):**
   Cranelift source (`x64/mod.rs:196-202`) and V8 `x86_64` execution (`i16x8.relaxed_laneselect` returning `0xFF00`; `f32x4.relaxed_min` returning `1.0` vs. `qNaN`) prove that width-uniform $R_{\mathsf{laneselect}}$ and unconditional `relaxed_min` commutativity **are known not to apply**.
5. **Upstream Resolution of `numerics.rst` vs. `eval_vec.ml` on Deterministic `relaxed_madd` (`unknown`):**
   Whether the Wasm Community Group will align `numerics.rst:2360` (unfused) to `eval_vec.ml:130` / `wasmtime` (fused `fma`) or vice versa is **unknown**.

---

## Evidence

### 1. Primary Specifications and Upstream Source Coordinates (Observed 2026-11-21)

- **`ARM-software/abi-aa` (`9f9e067e6c6a5d3c5c8326756500cdbd940b8ff7`):** `aapcs64/aapcs64.rst:265, 896-991, 1063-1585, 1795-1801, 2480-2755` (`d8-d15` Base PCS, `z8-z23`/`p4-p15` SVE PCS, volatile `FPSR.QC`, caller-saved `ZT0` excluded from `TPIDR2_EL0` lazy save, mandatory `TPIDR2_EL0 = 0` before `PSTATE.ZA = 0` at `L1472-1473`, `__arm_sme_save`/`__arm_sme_restore`).
- **`rems-project/sail-arm` (`5416ef6b43e9527c38dc71fb752259c1d01a47e1`):** `arm-v9.4-a/src/v8_base.sail:9504-9513` (`ResetSVEState` setting `FPSR = 0x0800009f`), `L29525-29639` (`CheckSMEZT0Enabled`, `ResetSMEState`, `SetPSTATE_SM`, `SetPSTATE_ZA`); `instrs64_sme.sail:4109-4145` (`execute_ZERO_ZA_I__`).
- **`llvm/llvm-project` (`f61dfd8c0d8cfa6ed8a1ea3a16174d9673184825`) & `torvalds/linux` (`f1715c0c04606ebbe832cc760abf49dfd6f2ae1f`):** `compiler-rt/lib/builtins/aarch64/sme-abi.S:61-250` (`__arm_tpidr2_save`, `__arm_tpidr2_restore`, `__arm_za_disable` `L185-188`, `ZT0` slot `@32` `L229`); `llvm/lib/Target/X86/X86CallingConv.td:1098-1170` (`CSR_64`, `CSR_Win64`); `linux/Documentation/arch/arm64/sme.rst:87-162`.
- **`WebAssembly/spec` (`d0b2e8d5544d2049fba0521922c436e3f0fcaebe`), `WebAssembly/relaxed-simd` (`c3f9359af2cd607cc46b0a3274f90ea52543a2f2`), & `bytecodealliance/wasmtime` (`40e0d780e4bfa34325d342db5bcf492bea227e07`):** `numerics.rst:2340-2594`; `eval_vec.ml:64-214` (`RelaxedMadd -> fma` at `L130`); `wasmtime` `crates/cranelift/src/{translate/code_translator.rs:2495-2660, func_environ.rs:6030-6395}`, `cranelift/codegen/src/isa/x64/{mod.rs:196-202, lower.isle:1670-1752}`.
- **`awslabs/s2n-bignum` (`280a220986a0bc6249248187717a771153d073db`) & `FFmpeg/FFmpeg` (`e8574d0b22b126acc76007babce536c68bc07d0a`):** `s2n-bignum` `x86/proofs/mlkem_ntt.ml:1345-1427`, `arm/proofs/mlkem_ntt.ml:552-554` (`d8..d15`); `FFmpeg` `libavutil/aarch64/{asm.S:352-371, cpu_sme.S:26-31}`, `libavcodec/aarch64/vvc/inter_sme2.S:124, 232-341`, `libavutil/x86/x86inc.asm:560-622`.

### 2. Executed Wasm 3.0 `relaxed-simd` (`Node.js v24.21.0`) and `gcc 15.2.0` Win64/SysV ABI Probes (`Basis: execution`)

Executed on Linux `x86_64` (`2026-11-21`):

```python
import subprocess, struct

def uleb(n):
    out = []
    while True:
        b, n = n & 0x7f, n >> 7
        out.append(b | (0x80 if n else 0))
        if not n: return bytes(out)
def sec(i, p): return bytes([i]) + uleb(len(p)) + p
def vc(b): return b"\xfd\x0c" + b
def op(c): return b"\xfd" + uleb(c)
def st(off, e): return b"\x41\x00" + e + b"\xfd\x0b\x00" + uleb(off)

a_ff, b_00 = b"\xff" * 16, b"\x00" * 16
m16 = struct.pack("<8H", 0x8001, 0x7FFE, 0xFFFF, 0x0000, 0x8000, 0x0001, 0xAAAA, 0x5555)
fa = struct.pack("<4I", 0x3f800001, 0x3f800001, 0x3f800000, 0x3f800000)
fc = struct.pack("<4I", 0xbf800002, 0xbf800000, 0xbf800000, 0x80000000)
ma = struct.pack("<4I", 0x7fc01234, 0x3f800000, 0x80000000, 0x00000000)
mb = struct.pack("<4I", 0x3f800000, 0x7fc05678, 0x00000000, 0x80000000)

body = (b"\x00"
  + st(0,  vc(a_ff) + vc(b_00) + vc(m16) + op(0x10a)) # i16x8.relaxed_laneselect
  + st(16, vc(fa)   + vc(fa)   + vc(fc)  + op(0x105)) # f32x4.relaxed_madd
  + st(32, vc(ma)   + vc(mb)             + op(0x10d)) # f32x4.relaxed_min
  + st(48, vc(ma)   + vc(mb)             + op(0xe8))  # f32x4.min (deterministic)
  + b"\x0b")
wasm = (b"\x00asm\x01\x00\x00\x00" + sec(1, b"\x01\x60\x00\x00") + sec(3, b"\x01\x00")
  + sec(5, b"\x01\x00\x01") + sec(7, b"\x02\x03mem\x02\x00\x03run\x00\x00")
  + sec(10, b"\x01" + uleb(len(body)) + body))
js = f"""
const inst = new WebAssembly.Instance(new WebAssembly.Module(Buffer.from("{wasm.hex()}","hex")));
inst.exports.run();
const u16 = new Uint16Array(inst.exports.mem.buffer, 0, 8);
const u32 = new Uint32Array(inst.exports.mem.buffer, 16, 12);
console.log("i16x8.relaxed_laneselect:", Array.from(u16, x => "0x"+x.toString(16).padStart(4,"0")));
console.log("f32x4.relaxed_madd:      ", Array.from(u32.slice(0,4), x => "0x"+x.toString(16).padStart(8,"0")));
console.log("f32x4.relaxed_min:       ", Array.from(u32.slice(4,8), x => "0x"+x.toString(16).padStart(8,"0")));
console.log("f32x4.min (det):         ", Array.from(u32.slice(8,12), x => "0x"+x.toString(16).padStart(8,"0")));
"""
print(subprocess.check_output(["node", "-e", js], text=True).strip())
```

Recorded `Node.js v24.21.0` output:
- `i16x8.relaxed_laneselect`: `['0xff00', '0x00ff', '0xffff', '0x0000', '0xff00', '0x0000', '0xffff', '0x0000']` (`0xff00` and `0x00ff` outside `{0x8001, 0xffff}` and `{0x7ffe, 0x0000}`).
- `f32x4.relaxed_madd`: `['0x28800000', '0x34800000', '0x00000000', '0x3f800000']` (`+2^-46` fused FMA in lane 0 vs. `+0.0` unfused).
- `f32x4.relaxed_min` vs. `f32x4.min`: `['0x3f800000', '0x7fc05678', '0x00000000', '0x80000000']` vs. `['0xffc00000', '0xffc00000', '0x80000000', '0x80000000']`.

Compiling `__attribute__((ms_abi))` vs. `__attribute__((sysv_abi))` functions clobbering `ymm7` under `gcc 15.2.0 -O2 -mavx2` (`objdump -d -M intel`) verified `sub rsp, 0x10; vmovaps [rbp-0x10], xmm7; ...; vzeroupper; vmovaps xmm7, [rbp-0x10]` (`16`-byte `[127:0]` spill + upper zeroing) on `ms_abi` vs. frameless `vpaddd; vpxor; vmovdqa [rdi], ymm0; vzeroupper; ret` on `sysv_abi`.

---

## Revalidation

1. **`AAPCS64` `SME2` `TPIDR2_EL0` & `ZT0` Contract Check (`< 5 s`):**
   Inspect `aapcs64/aapcs64.rst` (`SME state`, `TPIDR2_EL0`, `SME support routines`) in `ARM-software/abi-aa` and `compiler-rt/lib/builtins/aarch64/sme-abi.S` in `llvm/llvm-project` to confirm `ZT0` exclusion from `__arm_tpidr2_save` and `msr TPIDR2_EL0, xzr` $\to$ `smstop za` ordering in `__arm_za_disable`.
2. **Wasm 3.0 `relaxed-simd` Engine & Spec Probe (`< 3 s`):**
   Execute the inline Python + `node` script in §Evidence on any target Wasm runtime/CPU to check `i16x8.relaxed_laneselect` (`0xff00` byte-blend vs. `{0x8001, 0xffff}`), `f32x4.relaxed_madd` (`0x28800000` vs. `0x00000000`), and `f32x4.relaxed_min`, and diff `WebAssembly/spec` `numerics.rst` against `eval_vec.ml` on `RelaxedMadd`.
3. **Win64 / SysV / AAPCS64 Callee-Save Width Check (`< 3 s`):**
   Compile a 6-line `__attribute__((ms_abi))` vs. `__attribute__((sysv_abi))` C probe clobbering `ymm7`/`zmm7`/`zmm17` under `gcc`/`clang -O2 -mavx512f` and inspect `objdump -d` to verify `xmm6..15[127:0]`-only spills and `vzeroupper` placement.
