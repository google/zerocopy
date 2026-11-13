# Instruction-Selection Fallbacks and Runtime Libcall Contracts Across Tier 1 Targets in Rust 1.99.1 and LLVM 23.1.1

## Summary

A verified compiler backend targeting Rust `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) must either emit inline instruction
sequences for every primitive MIR / intrinsic operation under the active
subtarget feature set, or lower unsupported operations to external runtime
libcalls whose ABI, register-preservation rules, and semantic contracts match
`compiler_builtins`, `libc`, `libm`, or the Windows MSVC CRT. Inspecting LLVM
`23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, `RuntimeLibcalls.td`,
`LegalizeIntegerTypes.cpp`, `X86ISelLowering.cpp`, `AArch64ISelLowering.cpp`),
auditing the exported symbol tables (`llvm-nm`) of `libcompiler_builtins-*.rlib`
across all eight Tier 1 targets, and compiling multi-feature assembly probes
establishes four governing findings:

1. **Feature-dependent instruction selection vs. SWAR/libcall fallbacks:**
   Across `x86-64-v1` (baseline `SSE2`), `x86-64-v2` (`+popcnt,+sse4.2,+cx16`),
   `x86-64-v3` (`+avx2,+bmi1,+bmi2,+lzcnt,+fma,+f16c`), `x86-64-v4` (`+avx512*`),
   `i686` (`pentium4` baseline), and `aarch64` (`armv8-a` vs. `+outline-atomics`
   vs. `+lse,+fp16`), identical Rust/LLVM IR primitives lower to qualitatively
   different instruction sequences or libcalls:
   - **`ctlz(u64)` / `cttz(u64)` (`@llvm.ctlz.i64(..., i1 false)`):** On
     `x86-64-v1`/`v2`, LLVM emits `movl $127, %eax; bsrq %rdi, %rax; xorl $63, %eax`
     (relying on Intel/AMD hardware leaving the destination register `%rax = 127`
     unmodified when `bsrq` is given `0`, so `127 ^ 63 = 64`). On `x86-64-v3`
     (`+lzcnt`), it emits `lzcntq %rdi, %rax`. On `aarch64`, it emits `clz x0, x0`.
   - **`ctpop(u64)` (`@llvm.ctpop.i64`):** On `x86-64-v1`, LLVM emits a
     12-instruction SWAR parallel bit-count using magic constants
     `0x5555555555555555`, `0x3333333333333333`, `0x0f0f0f0f0f0f0f0f`, and
     multiply by `0x0101010101010101 >> 56`; on `i686` baseline, it transfers the
     64-bit integer to `%xmm0` and uses SSE2 `psadbw`; on `x86-64-v2`+, it emits
     `popcntq %rdi, %rax`; on `aarch64` (without Armv8.8-A `+cssc`), it transfers
     GPR `x0` to SIMD `d0` (`fmov d0, x0; cnt v0.8b, v0.8b; addv b0, v0.8b; fmov w0, s0`).
   - **`fmaf64` and `round_ties_even_f64`:** On `x86-64-v1`, `fmaf64` lowers to a
     tail call to `libm`'s `fma@GOTPCREL(%rip)` and `round_ties_even_f64` calls
     `rint@GOTPCREL(%rip)`. On `x86-64-v2` (`+sse4.1`), `round_ties_even_f64`
     becomes inline `roundsd $4, %xmm0, %xmm0`; on `x86-64-v3` (`+fma`), `fmaf64`
     becomes inline `vfmadd213sd %xmm2, %xmm1, %xmm0`. On `aarch64`, both are
     always single baseline instructions (`fmadd d0, d0, d1, d2` and `frintn d0, d0`).
   - **`f16` arithmetic:** On `x86-64-v1`/`v2` and `i686`, `f16 + f16` emits two
     calls to `__extendhfsf2` (`compiler_builtins`), a 32-bit `addss`, and a call
     to `__truncsfhf2`. On `x86-64-v3` (`+f16c`), it uses hardware `vcvtph2ps`,
     `vaddss`, and `vcvtps2ph $4` without libcalls. On `aarch64` baseline, it
     uses `fcvt s0, h0; fadd s0, s0, s1; fcvt h0, s0`; with `+fp16` (Armv8.2-A),
     it emits a single `fadd h0, h0, h1`.
2. **Complete `RuntimeLibcalls.td` (`495` abstract libcalls) and Tier 1 `compiler_builtins` symbol census:**
   LLVM `23.1.1`'s `llvm/include/llvm/IR/RuntimeLibcalls.td` (`4,372` lines)
   defines **495 abstract `RuntimeLibcall` entries**. Auditing the prebuilt
   `libcompiler_builtins-*.rlib` archives in Rust `1.99.1` across all eight
   Tier 1 targets reveals between **383** (`aarch64-apple-darwin`) and **775**
   (`aarch64-unknown-linux-gnu`) non-mangled C-ABI runtime symbols per target.
3. **Target-divergent lowering of `i128` division, `u64` division, and `powi`:**
   - **128-bit integer division (`__udivti3` / `__divti3`):** On all 64-bit Tier 1
     targets (`x86_64-*`, `aarch64-*`), `u128 / u128` calls `__udivti3`
     (`___udivti3` on Darwin) in `compiler_builtins` and computes `a % b` inline
     as `a - q * b`. On 32-bit x86 (`i686-unknown-linux-gnu` and
     `i686-pc-windows-msvc`), `__udivti3` is **not emitted**; LLVM's
     `SelectionDAGLegalize` expands 128-bit division inline into a ~150-instruction
     multi-block shift-subtract loop because `i128` requires four 32-bit registers!
   - **64-bit integer division on 32-bit x86:** On `i686-unknown-linux-gnu`,
     64-bit division calls `__udivdi3` / `__divdi3` (`cdecl`). On
     `i686-pc-windows-msvc`, LLVM emits calls to MSVC's `_aulldiv`, `_alldiv`,
     `_aullrem`, `_allrem`, `_allmul`, `_allshl`, `_allshr`, and `_aullshr`
     (which use a custom callee-pop / `EDX:EAX` + `EBX:ECX` calling convention
     implemented in `compiler_builtins/src/x86.rs`).
   - **`powif32` / `powif64` (`@llvm.powi`):** On Linux, Darwin, and MinGW
     targets, `@llvm.powi.f64.i32` calls `__powidf2` (`compiler_builtins`). On
     all three Windows MSVC targets (`x86_64-pc-windows-msvc`,
     `aarch64-pc-windows-msvc`, `i686-pc-windows-msvc`), `RuntimeLibcalls.td`
     suppresses `__powidf2` under `isWindowsMSVCEnvironment`, and LLVM converts
     the integer exponent to `double` (`cvtsi2sd`) and calls `pow(double, double)`
     in the Universal CRT (`ucrt`)!
4. **Non-standard ABI contracts on outline atomics, stack probes, and `memcpy`:**
   - **AArch64 outline atomics (`100` symbols):** Enabled by default on
     `aarch64-unknown-linux-gnu` (`+outline-atomics`), emitting calls to
     `__aarch64_{cas,swp,ldadd,ldclr,ldeor,ldset}{1,2,4,8,16}_{relax,acq,rel,acq_rel}`
     in `compiler_builtins`. These helpers dynamically dispatch between Armv8.0
     `ldaxr`/`stlxr` loops and Armv8.1 LSE instructions based on
     `__aarch64_have_lse_atomics`.
   - **Stack probes (`__rust_probestack` vs. `__chkstk` / `___chkstk_ms`):**
     These routines do **not** follow the platform C calling convention: on
     `x86_64` ELF (`__rust_probestack`) and Windows (`__chkstk` / `___chkstk_ms`),
     the allocation size is passed in `%rax` (`%eax` on `i686`) and on AArch64
     Windows (`__chkstk`) in `x15` (scaled by 16 bytes), while all argument
     registers (`%rcx`, `%rdx`, `%rsi`, `%rdi`, `%r8`–`%r11`, `x0`–`x7`) must be
     preserved across the probe!
   - **`memcpy` identical-pointer contract:** In C99 (`7.21.2.1`), `memcpy(dst, src, n)`
     requires non-overlapping objects even when `dst == src` and `n > 0`. In
     contrast, LLVM LangRef explicitly defines `@llvm.memcpy` to allow identical
     source and destination pointers (`dst == src`, a no-op) while prohibiting
     partial overlap. Any `memcpy` implementation linked by a Rust backend must
     therefore be safe for `dst == src`.

## Applicability

These findings apply to **Rust 1.99.1** (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
and **LLVM 23.1.1** (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) across all
eight Tier 1 targets: `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`,
`i686-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`,
`x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`, and `i686-pc-windows-msvc`.

## Findings

### 1. Feature-level instruction-selection matrix across Tier 1 targets

Basis: source (`X86ISelLowering.cpp`, `AArch64ISelLowering.cpp`) + execution (`support/lowering_and_libcalls.json`)

Table 1 records the exact instruction sequence or libcall selected by `rustc 1.99.1`
(`-C opt-level=2`) across target triples and CPU feature levels.

| Operation / Intrinsic | `x86_64-v1` (Baseline `SSE2`) | `x86_64-v2` (`+popcnt,+sse4.2,+cx16`) | `x86_64-v3` (`+avx2,+bmi1/2,+lzcnt,+fma,+f16c`) | `i686` Baseline (`pentium4`) | `aarch64` Baseline (`-outline-atomics`) | `aarch64` Default (`+outline-atomics`) | `aarch64` (`+lse,+fp16`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `u64::leading_zeros` (`ctlz`) | `movl $127,%eax; bsrq %rdi,%rax; xorl $63,%eax` | `movl $127,%eax; bsrq %rdi,%rax; xorl $63,%eax` | `lzcntq %rdi, %rax` | Two `bsrl` + `cmovnel` + `xorl $31` | `clz x0, x0` | `clz x0, x0` | `clz x0, x0` |
| `u64::trailing_zeros` (`cttz`) | `movl $64,%eax; bsfq %rdi,%rax` | `movl $64,%eax; bsfq %rdi,%rax` | `tzcntq %rdi, %rax` | Two `bsfl` + `cmovel` | `rbit x8, x0; clz x0, x8` | `rbit x8, x0; clz x0, x8` | `rbit x8, x0; clz x0, x8` |
| `u64::count_ones` (`ctpop`) | 12-insn GPR SWAR mask + `imulq` (`0x0101...01 >> 56`) | `popcntq %rdi, %rax` | `popcntq %rdi, %rax` | SSE2 `movq %xmm0; psrlw; pand; psubb; psadbw` | `fmov d0, x0; cnt v0.8b, v0.8b; addv b0, v0.8b; fmov w0, s0` | `fmov d0, x0; cnt v0.8b, v0.8b; addv b0, v0.8b; fmov w0, s0` | `fmov d0, x0; cnt v0.8b, v0.8b; addv b0, v0.8b; fmov w0, s0` |
| `u64::reverse_bits` (`bitreverse`) | `bswapq` + 3-stage nibble/pair/bit mask-shift (`19` insns) | `bswapq` + 3-stage mask-shift (`19` insns) | `bswapq` + 3-stage mask-shift (`19` insns) | Dual `bswapl` + 3-stage mask-shift (`31` insns) | `rbit x0, x0` (`1` insn) | `rbit x0, x0` (`1` insn) | `rbit x0, x0` (`1` insn) |
| `u32::saturating_add` | `addl %esi, %eax; orl $-1, %eax` (on `CF=1` via `cmovael`) | `addl` + `cmovael` | `addl` + `cmovael` | `addl` + `cmovael` | `adds w8, w0, w1; csinv w0, w8, wzr, lo` | `adds w8, w0, w1; csinv w0, w8, wzr, lo` | `adds w8, w0, w1; csinv w0, w8, wzr, lo` |
| `u64` div/rem | `divq %rsi` ( inline `64/32`-bit fastpath check) | `divq %rsi` | `divq %rsi` | Libcall `__udivdi3` (GNU) / `__aulldiv` (MSVC) + `subl/sbbl` | `udiv x8, x0, x1; msub x1, x8, x1, x0` | `udiv` + `msub` | `udiv` + `msub` |
| `u128` mul (`wrapping_mul`) | `mulq` + $2\times$ `imulq` + `addq` (`6` insns inline) | `mulq` + $2\times$ `imulq` + `addq` | `mulx` + $2\times$ `imulq` + `addq` | Inline 32-bit limb `mull`/`imull` (`26` insns) | `mul x8, x0, x2; umulh x9, x0, x2; madd...` (`6` insns) | `mul` + `umulh` + $2\times$ `madd` | `mul` + `umulh` + $2\times$ `madd` |
| `i128::overflowing_mul` | Inline `mulq` / `imulq` + high-word sign check (`38` insns) | Inline `38` insns | Inline `mulx` (`36` insns) | Inline 32-bit limb expansion (`108` insns, no `__muloti4` call) | Inline `smulh`/`umulh` check (`29` insns) | Inline `29` insns | Inline `29` insns |
| `u128` div/rem | Libcall `callq *__udivti3@GOTPCREL(%rip)` + inline `rem = a - q*b` | Libcall `__udivti3` + inline `rem` | Libcall `__udivti3` + inline `rem` | **Inline ~150-insn multi-block shift-subtract loop** (no libcall!) | Libcall `bl __udivti3` + inline `rem` | Libcall `bl __udivti3` + inline `rem` | Libcall `bl __udivti3` + inline `rem` |
| `fmaf64(a, b, c)` | Libcall `jmpq *fma@GOTPCREL(%rip)` (`libm`) | Libcall `fma` (`libm`) | `vfmadd213sd %xmm2, %xmm1, %xmm0` (inline) | Libcall `fma@PLT` / `_fma` | `fmadd d0, d0, d1, d2` (inline) | `fmadd d0, d0, d1, d2` | `fmadd d0, d0, d1, d2` |
| `round_ties_even_f64` | Libcall `jmpq *rint@GOTPCREL(%rip)` (`libm`) | `roundsd $4, %xmm0, %xmm0` (inline SSE4.1) | `vroundsd $4, %xmm0, %xmm0, %xmm0` | Libcall `rint@PLT` / `_rint` | `frintn d0, d0` (inline) | `frintn d0, d0` | `frintn d0, d0` |
| `f64 % f64` (`frem`) | Libcall `jmpq *fmod@GOTPCREL(%rip)` (`libm`) | Libcall `fmod` | Libcall `fmod` | Libcall `fmod` | Libcall `b fmod` (`_fmod` on Darwin) | Libcall `b fmod` | Libcall `b fmod` |
| `powif64(a, i32)` | Libcall `__powidf2` (`compiler_builtins`) | Libcall `__powidf2` | Libcall `__powidf2` (`pow` on Windows MSVC!) | Libcall `__powidf2` (`_pow` on Windows MSVC!) | Libcall `b __powidf2` (`b pow` on Windows MSVC!) | Libcall `b __powidf2` | Libcall `b __powidf2` |
| `f64 as i64` (saturating) | Inline SSE2 `cvttsd2siq` + `ucomisd` clamp (`11` insns) | Inline `11` insns | Inline AVX `vcvttsd2si` + clamp (`10` insns) | Inline SSE2 + clamp (`36` insns) | `fcvtzs x0, d0` (`1` insn; hardware saturates & maps NaN $\to 0$!) | `fcvtzs x0, d0` (`1` insn) | `fcvtzs x0, d0` (`1` insn) |
| `f16 + f16` | $2\times$ `__extendhfsf2` + `addss` + `__truncsfhf2` | $2\times$ `__extendhfsf2` + `addss` + `__truncsfhf2` | `vcvtph2ps` + `vaddss` + `vcvtps2ph $4` (inline F16C) | $2\times$ `__extendhfsf2` + `addss` + `__truncsfhf2` | `fcvt s1,h1; fcvt s0,h0; fadd s0,s0,s1; fcvt h0,s0` | `fcvt` + `fadd` + `fcvt` | `fadd h0, h0, h1` (`1` insn) |
| `f128 + f128` / `f128 * f128` | Libcall `__addtf3` / `__multf3` (`compiler_builtins`) | Libcall `__addtf3` / `__multf3` | Libcall `__addtf3` / `__multf3` | Libcall `__addtf3` / `__multf3` | Libcall `b __addtf3` / `b __multf3` | Libcall `b __addtf3` / `b __multf3` | Libcall `b __addtf3` / `b __multf3` |
| `AtomicU64::fetch_add(AcqRel)` | `lock xaddq %rax, (%rdi)` | `lock xaddq %rax, (%rdi)` | `lock xaddq %rax, (%rdi)` | `lock cmpxchg8b (%ebp)` loop | `ldaxr x0,[x8]; add x9,x0,x1; stlxr w10,x9,[x8]; cbnz` | Libcall `bl __aarch64_ldadd8_acq_rel` | `ldaddal x1, x0, [x0]` (`1` insn) |

---

### 2. Tier 1 `compiler_builtins` symbol inventory and provider mapping

Basis: execution (`llvm-nm --defined-only` across all 8 Tier 1 `libcompiler_builtins-*.rlib` archives in `support/lowering_and_libcalls.json`) + source (`library/compiler-builtins/compiler-builtins/src/`)

Table 2 summarizes the defined runtime symbols in `libcompiler_builtins-*.rlib`
across the eight Tier 1 targets and identifies which library provides each
libcall family.

| Target Triple | `libcompiler_builtins` Defined Symbols | `i128` Arithmetic (`*ti3`/`*ti4`) | `i64`/`i32` Arithmetic (`*di3`/`_all*`) | Soft-Float & FP Conversions (`*tf*`/`*hf*`) | AArch64 Outline Atomics (`__aarch64_*`) | Stack Probe Symbol | External Libcalls Provided by `libm` / `libc` / `ucrt` |
| :--- | ---: | ---: | ---: | ---: | ---: | :--- | :--- |
| `x86_64-unknown-linux-gnu` | 603 | 38 | 60 | 63 | 0 | `__rust_probestack` | `fmod`, `fmodf`, `fma`, `fmaf`, `rint`, `sin`, `cos`, `exp`, `log`, `pow`, `memcpy`, `memmove`, `memset`, `memcmp`, `bcmp` (`glibc`) |
| `aarch64-unknown-linux-gnu` | 775 | 38 | 60 | 63 | **100** | (inline loop) | `fmod`, `fmodf`, `sin`, `cos`, `exp`, `log`, `pow`, `memcpy`, `memmove`, `memset`, `memcmp`, `bcmp` (`glibc`) |
| `i686-unknown-linux-gnu` | 588 | 27 | 60 | 63 | 0 | `__rust_probestack` | `fmod`, `fmodf`, `fma`, `rint`, `sin`, `cos`, `exp`, `log`, `pow`, `memcpy`, `memmove`, `memset`, `memcmp`, `bcmp` (`glibc`) |
| `aarch64-apple-darwin` | 383 | 25 | 37 | 61 | **100** | (inline / `libSystem`) | `_fmod`, `_fmodf`, `_sin`, `_cos`, `_exp`, `_log`, `_pow`, `_memcpy`, `_memmove`, `_memset`, `_memcmp`, `_bcmp` (`libSystem.B.dylib`) |
| `x86_64-pc-windows-msvc` | 724 | 55 | 84 | 61 | 0 | `__chkstk` (`vcruntime`) | `fmod`, `fma`, `rint`, `pow` (including `powi`!), `memcpy`, `memmove`, `memset`, `memcmp` (`vcruntime` / `ucrt`) |
| `x86_64-pc-windows-gnu` | 459 | 38 | 60 | 54 | 0 | `___chkstk_ms` | `fmod`, `fma`, `rint`, `memcpy`, `memmove`, `memset`, `memcmp` (`libmingwex` / `ucrt`) |
| `aarch64-pc-windows-msvc` | 771 | 53 | 84 | 61 | 0 | `__chkstk` (`vcruntime`) | `fmod`, `pow` (including `powi`!), `memcpy`, `memmove`, `memset`, `memcmp` (`vcruntime` / `ucrt`) |
| `i686-pc-windows-msvc` | 511 | 52 | **67** (incl. `_alldiv`, `_aulldiv`, `_allrem`, `_aullrem`, `_allmul`, `_allshl`, `_allshr`, `_aullshr`) | 61 | 0 | `_chkstk` (`vcruntime`) | `_fmod`, `_fma`, `_rint`, `_pow`, `_memcpy`, `_memmove`, `_memset`, `_memcmp` (`vcruntime` / `ucrt`) |

*(Note: When compiling `#![no_std]` freestanding binaries without `libc`,
`compiler_builtins` can be built with the `mem` feature enabled to provide weak
definitions of `memcpy`, `memmove`, `memset`, `memcmp`, `bcmp`, and `strlen` from
`library/compiler-builtins/compiler-builtins/src/mem/`; in standard Tier 1
hosted builds, those symbols are resolved from the platform C runtime so the OS
can use AVX-512/NEON-optimized memory routines.)*

---

### 3. Semantic contracts and ABI invariants assumed by LLVM for libcalls

Basis: normative (`LLVM LangRef`, `RuntimeLibcalls.td`) + source (`compiler_builtins`, `X86FrameLowering.cpp`, `AArch64FrameLowering.cpp`)

A verified backend or verified runtime replacement must preserve six non-obvious
libcall contracts:

1. **`memcpy` with identical source and destination (`dst == src`):**
   LLVM LangRef (`@llvm.memcpy`) states: *"The `<dest>` and `<src>` pointers may
   be equal, or completely non-overlapping, but partial overlap leads to
   undefined behavior."* Unlike C99 `memcpy(dst, src, n)` (where `restrict`
   forbids `dst == src` when `n > 0`), LLVM's backend can emit `memcpy(p, p, n)`
   from self-assignments not eliminated at `-C opt-level=0`. `compiler_builtins`'s
   `memcpy` (`src/mem/mod.rs`) and `glibc`/`libSystem`/`vcruntime` satisfy this
   by copying forward byte-by-byte or word-by-word without clobbering `src` when
   `dst == src`.
2. **`memcmp` vs. `bcmp` return-value contract:**
   `memcmp(a, b, n)` must return a signed three-way lexicographical comparison
   ($<0, 0, >0$) of unsigned bytes (`u8`), whereas `bcmp(a, b, n)` (emitted by
   LLVM on Linux/Darwin for equality-only `raw_eq` comparisons) is only required
   to return `0` if equal and non-zero if unequal.
3. **Division-by-zero and `INT_MIN / -1` inside `__divti3`, `__udivti3`, `__divdi3`, `__udivdi3`:**
   LLVM treats integer division by zero and signed `T::MIN / -1` as immediate UB
   in IR, and Rust guards safe `/` and `%` with explicit MIR `Assert` checks
   before calling the libcall. Inside `compiler_builtins` (`src/int/udiv.rs`),
   passing a zero divisor returns `0` (or traps on hardware divide instructions
   in specialized paths).
4. **Custom register-preservation ABIs for stack probes:**
   - **`__rust_probestack` on `x86_64` (`src/probestack.rs:47-125`):** Input
     frame size is passed in `%rax`. The routine walks down stack pages in
     4096-byte increments touching each page, **does not modify `%rsp`** on
     return (caller subtracts `%rax` from `%rsp` after `call __rust_probestack`),
     and preserves **all** GPRs including `%rax`, `%rcx`, `%rdx`, `%rsi`, `%rdi`,
     and `%r8`–`%r11` (only clobbering `%r11` or restoring `%rax`).
   - **`___chkstk_ms` on `x86_64-pc-windows-gnu` and `__chkstk` on `x86_64-pc-windows-msvc`:**
     Size passed in `%rax`; probes pages without modifying `%rsp`; preserves
     `%rax`, `%rcx`, `%rdx`, `%r8`–`%r11` (internally saves/restores `%rcx` and
     `%rax` on a temporary stack slot).
   - **`__chkstk` on `aarch64-pc-windows-msvc` (`src/aarch64.rs`):** Input
     allocation size divided by 16 (`size >> 4`) is passed in **`x15`**; the
     routine probes stack pages and returns without modifying `sp`, clobbering
     only `x16`, `x17`, and `nzcv` while preserving `x0`–`x15`.
5. **Custom register conventions on 32-bit `i686-pc-windows-msvc` 64-bit helpers (`src/x86.rs`):**
   - `_allmul`, `_alldiv`, `_allrem`, `_aulldiv`, `_aullrem`: Receive two 64-bit
     stack arguments (`16` bytes total), return the 64-bit result in `EDX:EAX`,
     and **callee-pop all 16 bytes (`ret 16`)**.
   - `_allshl`, `_allshr`, `_aullshr`: Receive the 64-bit value in `EDX:EAX` and
     the shift amount in `CL` (not on the stack!), returning the shifted 64-bit
     result in `EDX:EAX` while preserving `EBX`, `ESI`, `EDI`, `EBP`.
6. **AArch64 outline atomics register contract (`src/aarch64_outline_atomics.rs`):**
   - `__aarch64_cas{1,2,4,8}_{relax,acq,rel,acq_rel}` takes expected value in
     `x0`/`w0`, desired value in `x1`/`w1`, and pointer in `x2`, returning the
     previous memory value in `x0`/`w0` and clobbering only `x16`, `x17`, and
     `nzcv`!
   - `__aarch64_cas16_*` takes expected 128-bit pair in `x0:x1`, desired pair in
     `x2:x3`, and pointer in `x4`, returning the old 128-bit pair in `x0:x1`!
   - `__aarch64_{swp,ldadd,ldclr,ldeor,ldset}{1,2,4,8}_*` takes operand value in
     `x0`/`w0` and pointer in `x1` (note: **value first, pointer second**,
     opposite to C `__atomic_fetch_add(ptr, val)`!), returning the old value in
     `x0`/`w0` and clobbering only `x16`, `x17`, and `nzcv`.

---

### 4. Existing formal specifications and verification of runtime builtins

Basis: documentation + source

- **CompCert (`AbsInt/CompCert`, `runtime/` and `cfrontend/Cshmgen.v`):**
  Specifies 64-bit integer helper contracts (`__i64_dtos`, `__i64_stod`,
  `__i64_udiv`, `__i64_sdiv`, `__i64_shl`, `__i64_shr`, `__i64_sar`) as external
  builtin axioms in `common/Events.v` and proves that `SelectLong.v` rewrites
  64-bit operations on 32-bit targets to helper calls preserving trace refinement.
  However, CompCert's assembly implementations in `runtime/` are trusted rather
  than machine-code-verified.
- **VST (Verified Software Toolchain) & VeriFast (`memcpy` / `memcmp`):**
  Verify C implementations of `memcpy`, `memset`, and `memcmp` against
  separation-logic contracts, though standard C proofs assume disjoint buffers
  and must be augmented with a `dst == src` branch check to satisfy LLVM's
  `@llvm.memcpy` contract.
- **Rust `compiler_builtins` test suites (`builtins-test`, `builtins-test-intrinsics`, `libm-test`):**
  `library/compiler-builtins` validates its pure-Rust implementations via
  exhaustive/PRNG fuzzing against `libgcc` / `compiler-rt` / MPFR (`libm-test`),
  and almost all integer/soft-float routines in `compiler-builtins/src/{int,float,mem}`
  are written in pure `#![no_std]` Rust without inline assembly (making them
  directly verifiable at the Rust MIR level by Anneal!).

## Boundaries

- **Target `libm` transcendental precision (`sin`, `cos`, `exp`, `log`, `pow`):**
  Because LLVM lowers transcendental intrinsics (`@llvm.sin.f64`, etc.) to the
  target platform's C math library (`glibc` `libm`, Darwin `libSystem`, Windows
  `ucrt`), bit-for-bit results for non-algebraic functions can vary by up to
  $0.5$–$4$ ULP across OSes (`rustc-backend-dependent-observable-behaviors`).
- **32-bit Arm (`arm`) and RISC-V soft-float libcalls:** Only the eight Tier 1
  targets (`x86_64`, `i686`, `aarch64`) were empirically probed with `llvm-nm`
  and `rustc --emit=asm`.

## Evidence

- **LLVM 23.1.1 (`rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
  - `llvm/include/llvm/IR/RuntimeLibcalls.td:1-4372` (`495` abstract
    `RuntimeLibcall` definitions and target predicates).
  - `llvm/lib/IR/RuntimeLibcalls.cpp:1-610`.
  - `llvm/lib/CodeGen/SelectionDAG/LegalizeIntegerTypes.cpp:1-6950`,
    `TargetLowering.cpp:1-14800`.
  - `llvm/lib/Target/X86/X86ISelLowering.cpp` and
    `llvm/lib/Target/AArch64/AArch64ISelLowering.cpp`.
- **Rust 1.99.1 (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `library/compiler-builtins/compiler-builtins/src/{int,float,mem,math,probestack.rs,aarch64_outline_atomics.rs,x86.rs,x86_64.rs,aarch64.rs}`.
  - Prebuilt `libcompiler_builtins-*.rlib` archives for all 8 Tier 1 targets in
    `1.99.1-x86_64-unknown-linux-gnu`.
- **Preserved support artifacts:**
  - `support/lowering_and_libcalls.json`: Complete `RuntimeLibcalls.td` summary,
    per-target `libcompiler_builtins` symbol tables across all 8 Tier 1 targets,
    and extracted assembly instruction sequences for 18 probe functions across
    12 target/CPU-feature configurations.
  - `support/probe_lowering_and_libcalls.py`: Standalone script reproducing all
    symbol scans and assembly probes.

## Revalidation

Run `python3 support/probe_lowering_and_libcalls.py` with a target `rustc`
toolchain and `llvm-nm` to regenerate `lowering_and_libcalls.json` and check for
any changes in `libcompiler_builtins` symbol exports or instruction-selection
fallbacks.
