# Tier 1 Atomic and Fence Instruction Lowering Across `rustc` 1.99.1 and LLVM 23.1.1

## Summary

A drop-in verified replacement for `rustc` must emit instruction sequences for
`core::sync::atomic` and `core::intrinsics::atomic_*` that preserve both intra-language
memory-model soundness and cross-language binary compatibility with C11/C++11 code compiled
by Clang, GCC, and MSVC. Across the 8 Tier 1 targets in `rust-lang/rust` `1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) and its pinned LLVM `23.1.1` backend
(`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), atomic lowering is governed by four
interacting layers:

1. **Per-target `max-atomic-width` and baseline features (`rustc_target::spec`):**
   - `x86_64-unknown-linux-gnu` sets `max-atomic-width = 64` because its baseline CPU
     (`x86-64`) omits `+cx16` (`CMPXCHG16B`), whereas `x86_64-pc-windows-msvc` and
     `x86_64-pc-windows-gnu` set `max-atomic-width = 128` and baseline
     `features = "+cx16,+sse3,+sahf"`.
   - `i686-unknown-linux-gnu` and `i686-pc-windows-msvc` set `max-atomic-width = 64` with
     `cpu = "pentium4"` (which implies `cx8` and `sse2`).
   - All three Tier 1 AArch64 targets (`aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`,
     `aarch64-pc-windows-msvc`) set `max-atomic-width = 128`, but with distinct baseline
     feature sets: `+v8a,+outline-atomics` on Linux, `cpu = "apple-m1"` (implying `+v8.4a`,
     `+lse`, `+rcpc`, `+rcpc2`, `+lse2`) on macOS, and `+v8a,+neon` on Windows MSVC in
     `1.99.1` (updated in `nightly-2026-11-12` to `+v8a,+neon,+outline-atomics`).
2. **x86-64 and i686 TSO lowering (`X86ISelLowering.cpp`):**
   - For widths $\le 64$ bits on `x86_64` ($\le 32$ bits on `i686`), `Relaxed`, `Acquire`,
     and `SeqCst` loads lower to plain `mov`; `Relaxed` and `Release` stores lower to plain
     `mov`; `SeqCst` stores lower to `xchg` (implicit `LOCK`).
   - `fence(SeqCst)` lowers to `lock orl $0, -64(%rsp)` on `x86_64` (avoiding `mfence`
     pipeline serialization latency and dodging the red zone) and `mfence` on `i686` when
     `+sse2` is enabled (falling back to `lock orl $0, (%esp)` when `-sse2`).
   - On `i686`, 64-bit atomic loads and stores use SSE2 64-bit vector moves (`movq` /
     `movsd` + `movlps`, with trailing `lock orl $0, (%esp)` on `SeqCst` store), or x87
     `fildll` + `fistpll` via stack bounce when `-sse2` is passed; all 64-bit RMWs and CAS
     use `lock cmpxchg8b`.
   - On `x86_64` with `+cmpxchg16b` (`+cx16`) only, 128-bit atomic loads, stores, RMWs, and
     CAS all lower to `lock cmpxchg16b` loops (`AtomicExpandPass` expands 128-bit load to
     `cmpxchg16b` with `0 -> 0`). When **both** `+cmpxchg16b` and `+avx` are enabled,
     LLVM 23.1.1's `hasAVX()` check in `X86TargetLowering::shouldExpandAtomicLoadInIR` /
     `shouldExpandAtomicStoreInIR` switches 128-bit atomic loads and stores to single-instruction
     `vmovdqa (%rdi), %xmm0` and `vmovdqa %xmm0, (%rdi)` (with trailing `lock orl $0, -64(%rsp)`
     for `SeqCst` store), exploiting the Intel/AMD guarantee that 16-byte-aligned AVX
     loads/stores are single-copy atomic.
3. **AArch64 progression across LL/SC, Outline Atomics, LSE, RCpc, LSE2, and LSE128:**
   - **Base Armv8.0-A (`-outline-atomics`):** Loads use `ldr` (`Relaxed`) or `ldar`
     (`Acquire`/`SeqCst`); stores use `str` (`Relaxed`) or `stlr` (`Release`/`SeqCst`);
     all RMWs and CAS use `ldxr`/`ldaxr` + `stxr`/`stlxr` loops, with strong `cxchg` emitting
     `clrex` on comparison failure.
   - **Outline atomics (`+outline-atomics` without `+lse`, default on `aarch64-unknown-linux-gnu`):**
     Loads and stores remain inline (`ldr`/`ldar`/`str`/`stlr`), and `nand`/`min`/`max`/128-bit
     RMWs remain inline `ldaxp`/`stlxp` loops, but 8/16/32/64-bit `xchg`, `xadd`, `or` (`ldset`),
     `and` (`mvn` + `ldclr`), `xor` (`ldeor`), and 8/16/32/64/128-bit `cxchg`/`cxchgweak` lower
     to calls to `__aarch64_{swp,ldadd,ldset,ldclr,ldeor}{1,2,4,8}_{relax,acq,rel,acq_rel}` and
     `__aarch64_cas{1,2,4,8,16}_{relax,acq,rel,acq_rel}` provided by `compiler_builtins` or
     `libgcc`, which check `__aarch64_have_lse_atomics` (populated via `getauxval(AT_HWCAP) & HWCAP_ATOMICS`).
   - **Armv8.1-A LSE (`+lse`):** 8..64-bit RMWs lower directly to `swp*`, `ldadd*`, `ldclr*`,
     `ldset*`, `ldeor*`, `ldsmax*`, `ldsmin*`, `ldumax*`, `ldumin*`, and `cas*` (both `cxchg`
     and `cxchgweak` emit `cas*`; only `nand` uses a `cas*` loop). 128-bit loads, stores, RMWs,
     and CAS switch from `ldxp`/`stxp` to `casp`/`caspa`/`caspl`/`caspal`.
   - **Armv8.3-A RCpc (`+rcpc`):** `Acquire` loads ≤ 64 bits lower to `ldaprb`/`ldaprh`/`ldapr`
     (processor-consistent acquire, allowing reordering after an earlier `stlr` to a different
     address unless the store was read by the same thread), whereas `SeqCst` loads keep `ldar*`.
   - **Armv8.4-A LSE2 (`+lse2`, baseline on `aarch64-apple-darwin` `apple-m1`):** 16-byte-aligned
     `ldp`/`stp` become single-copy atomic, so 128-bit loads lower to `ldp` (`Relaxed`),
     `ldp; dmb ishld` (`Acquire`), and `ldar xzr, [x0]; ldp x0, x1, [x0]; dmb ish` (`SeqCst`,
     where the dummy `ldar xzr` orders the 128-bit load after prior `stlr` stores without a full
     leading `dmb ish`), and 128-bit stores lower to `stp` (`Relaxed`), `dmb ish; stp` (`Release`),
     and `dmb ish; stp; dmb ish` (`SeqCst`).
   - **Armv9.4-A LSE128 (`+lse128`):** 128-bit `Release`/`SeqCst` stores and 128-bit `xchg`,
     `or`, and `and` lower to single-instruction `swpp{,a,l,al}`, `ldsetp{,a,l,al}`, and
     `ldclrp{,a,l,al}` (while 128-bit `xadd`/`xsub`/`xor`/`nand`/`min`/`max` remain `casp` loops
     because FEAT_LSE128 defines only `SWPP`, `LDCLRP`, and `LDSETP`).
   - **Windows AArch64 (`aarch64-pc-windows-msvc`) `dmb ish` after `SeqCst` stores/RMWs/CAS:**
     Because MSVC's ARM64 C++ `<atomic>` lowers `memory_order_seq_cst` loads to plain `ldar`
     and relies on trailing `dmb ish` barriers on `SeqCst` stores and RMWs (`shouldInsertTrailingSeqCstFenceForMSVC`
     in `AArch64ISelLowering.cpp:32234-32255`), LLVM emits a trailing `dmb ish` after `stlr`,
     `stlxr`, and `stlxp` for `SeqCst` operations on Windows AArch64 (unless folded into an LSE
     `-al` instruction).

All 373 atomic/fence probe functions compiled across 17 target/feature configurations (`5,831`
total compiled functions) and their extracted assembly sequences are preserved in
`support/atomic_lowering_matrix.json`, `support/atomic_probe.rs`, and `support/asm/*.s`.

## Applicability

- **Primary subjects:** `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
  and `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), with
  forward comparison against `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
- **Targets and feature levels covered:** All 8 Tier 1 targets across 17 configurations:
  - `x86_64-unknown-linux-gnu`: default (`x86-64`), `+cmpxchg16b`, and `+cmpxchg16b,+avx`
  - `x86_64-pc-windows-msvc`: default (`+cx16,+sse3,+sahf`)
  - `x86_64-pc-windows-gnu`: default (`+cx16,+sse3,+sahf`)
  - `i686-unknown-linux-gnu`: default (`pentium4`, `+sse2`) and `-Ctarget-cpu=i586 -Ctarget-feature=-sse2`
  - `i686-pc-windows-msvc`: default (`pentium4`, `+sse2`)
  - `aarch64-unknown-linux-gnu`: default (`+v8a,+outline-atomics`), `-outline-atomics`, `+lse`,
    `+lse,+rcpc`, `+lse,+rcpc,+lse2`, and `+lse,+rcpc,+lse2,+lse128`
  - `aarch64-apple-darwin`: default (`apple-m1`: `+v8.4a,+lse,+rcpc,+rcpc2,+lse2`)
  - `aarch64-pc-windows-msvc`: default (`+v8a,+neon`) and `+lse`
- **Relationship to prior reports:** Extends
  `assembly-atomic-fence-mappings-and-aarch64-x86-weak-memory-models` (which analyzed weak
  memory models and litmus tests for base x86-TSO and AArch64) with the complete 8-target,
  5-width (`8`, `16`, `32`, `64`, `128` bits), 15-intrinsic × 5-ordering lowering matrix,
  outline-atomics runtime helper ABI, Windows AArch64 MSVC fence rules, and Cranelift/GCC
  backend compatibility.

## Findings

### 1. Rust Intrinsics to Backend Lowering Pipeline

Basis: source + execution

In `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:117-147,377-522`, `rustc` lowers
`core::intrinsics::atomic_*` (exposed on stable through `core::sync::atomic::Atomic*`,
`fence`, and `compiler_fence`) to five `BuilderMethods` calls implemented for LLVM in
`compiler/rustc_codegen_llvm/src/builder.rs`:

| Rust intrinsic family | Orderings accepted by `rustc` | `rustc_codegen_llvm` lowering (`builder.rs`) | LLVM IR instruction emitted |
| :--- | :--- | :--- | :--- |
| `atomic_load<T, ORD>` | `Relaxed`, `Acquire`, `SeqCst` | `atomic_load` (`L701-722`) | `load atomic iN, ptr %p <ord>, align (N/8)` |
| `atomic_store<T, ORD>` | `Relaxed`, `Release`, `SeqCst` | `atomic_store` (`L928-945`) | `store atomic iN %v, ptr %p <ord>, align (N/8)` |
| `atomic_xchg`, `atomic_xadd`, `atomic_xsub`, `atomic_and`, `atomic_nand`, `atomic_or`, `atomic_xor`, `atomic_max`, `atomic_min`, `atomic_umax`, `atomic_umin` | `Relaxed`, `Acquire`, `Release`, `AcqRel`, `SeqCst` | `atomic_rmw` (`L1394-1419`) | `atomicrmw <op> ptr %p, iN %v <ord>, align (N/8)` |
| `atomic_cxchg<T, ORD, FAIL>`, `atomic_cxchgweak<T, ORD, FAIL>` | `(Relaxed\|Acquire\|Release\|AcqRel\|SeqCst, Relaxed\|Acquire\|SeqCst)` | `atomic_cmpxchg` (`L1368-1392`) | `cmpxchg [weak] ptr %p, iN %cmp, iN %new <succ> <fail>, align (N/8)` |
| `atomic_fence<ORD>` | `Acquire`, `Release`, `AcqRel`, `SeqCst` | `atomic_fence` (`L1421-1431`, `SynchronizationScope::CrossThread`) | `fence <ord>` |
| `atomic_singlethreadfence<ORD>` (`compiler_fence`) | `Acquire`, `Release`, `AcqRel`, `SeqCst` | `atomic_fence` (`L1421-1431`, `SynchronizationScope::SingleThread`) | `fence singlethread <ord>` |

Crucially, `atomic_load` (`builder.rs:709`) and `atomic_store` (`builder.rs:936`) explicitly
pass `self.tcx.data_layout().i128_align` (or the integer size alignment `size.bytes()`, which
is `16` bytes for `i128` on all Tier 1 targets in `1.99.1`) to `LLVMRustSetAlignment`. Thus
`AtomicU128` / `AtomicI128` is always 16-byte aligned in memory (`align 16`), which is a
precondition for single-copy atomicity of `cmpxchg16b` on x86-64 and `ldp`/`stp`/`casp`/`swpp`
on AArch64.

### 2. Tier 1 Target Atomic Widths and Baseline Feature Matrix

Basis: source + execution

| Target Triple | `max-atomic-width` | Default `cpu` | Default `features` (`1.99.1`) | `cfg(target_has_atomic)` values on default flags |
| :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `64` (`+cx16` overrides to `128`) | `x86-64` | `""` (LLVM implies `+sse,+sse2,+x87,+fxsr`) | `"8"`, `"16"`, `"32"`, `"64"`, `"ptr"` |
| `x86_64-pc-windows-msvc` | `128` | `x86-64` | `"+cx16,+sse3,+sahf"` | `"8"`, `"16"`, `"32"`, `"64"`, `"128"`, `"ptr"` |
| `x86_64-pc-windows-gnu` | `128` | `x86-64` | `"+cx16,+sse3,+sahf"` | `"8"`, `"16"`, `"32"`, `"64"`, `"128"`, `"ptr"` |
| `i686-unknown-linux-gnu` | `64` | `pentium4` | `""` (LLVM implies `+cx8,+sse,+sse2,+x87,+fxsr`) | `"8"`, `"16"`, `"32"`, `"64"`, `"ptr"` |
| `i686-pc-windows-msvc` | `64` | `pentium4` | `""` (LLVM implies `+cx8,+sse,+sse2,+x87,+fxsr`) | `"8"`, `"16"`, `"32"`, `"64"`, `"ptr"` |
| `aarch64-unknown-linux-gnu` | `128` | `generic` | `"+v8a,+outline-atomics"` (`+neon` required by ABI) | `"8"`, `"16"`, `"32"`, `"64"`, `"128"`, `"ptr"` |
| `aarch64-apple-darwin` | `128` | `apple-m1` | `""` (`apple-m1` implies `+v8.4a,+lse,+rcpc,+rcpc2,+lse2`) | `"8"`, `"16"`, `"32"`, `"64"`, `"128"`, `"ptr"` |
| `aarch64-pc-windows-msvc` | `128` | `generic` | `"+v8a,+neon"` (`+outline-atomics` added in `nightly-2026-11-12`) | `"8"`, `"16"`, `"32"`, `"64"`, `"128"`, `"ptr"` |

In `compiler/rustc_codegen_ssa/src/target_features.rs:509-525`, when `sess.target.arch` is
`Arch::X86_64` and `cmpxchg16b` (`cx16`) is enabled via `-Ctarget-cpu` (e.g., `x86-64-v2` or
newer) or `-Ctarget-feature=+cmpxchg16b`, `rustc` dynamically raises `max_atomic_width` from
`64` to `128` and adds `target_has_atomic="128"`.

### 3. x86-64 and 32-bit x86 (`i686`) Exact Instruction Lowering Matrix

Basis: source (`llvm/lib/Target/X86/X86ISelLowering.cpp:32480-33060,38814-38910`) + execution (`support/atomic_lowering_matrix.json`)

#### 3.1 Widths `8`, `16`, `32`, and `64` bits on `x86_64` (and `8`, `16`, `32` bits on `i686`)

In the Table below, `<s/r>` denotes `(b/%al, w/%ax, l/%eax, q/%rax)` for `8/16/32/64`-bit widths:

| Operation | Orderings | Emitted Instruction Sequence (`x86_64` / `i686` ≤32b) | Lowering Note |
| :--- | :--- | :--- | :--- |
| `atomic_load` | `Relaxed`, `Acquire`, `SeqCst` | `mov<s/r> (%ptr), %dst` | x86-TSO hardware preserves Load→Load and Load→Store order. |
| `atomic_store` | `Relaxed`, `Release` | `mov<s/r> %val, (%ptr)` | x86-TSO hardware preserves Store→Store and Load→Store order. |
| `atomic_store` | `SeqCst` | `xchg<s/r> %val, (%ptr)` | Implicit `LOCK` drains store buffer to prevent Store→Load reordering. |
| `atomic_xchg` | All 5 (`Relaxed`..`SeqCst`) | `mov<s/r> %val, %rax; xchg<s/r> %rax, (%ptr)` | Implicit `LOCK` on memory operand; no `lock` prefix byte emitted. |
| `atomic_xadd` | All 5 (`Relaxed`..`SeqCst`) | `mov<s/r> %val, %rax; lock xadd<s/r> %rax, (%ptr)` | If return value is unused in caller, peephole-optimized to `lock add<s/r>`. |
| `atomic_xsub` | All 5 (`Relaxed`..`SeqCst`) | `neg<s/r> %val; lock xadd<s/r> %val, (%ptr)` | Lowered by negating operand and executing `lock xadd`. |
| `atomic_{and,or,xor}` | All 5 (`Relaxed`..`SeqCst`) | `mov (%ptr), %rax; .L1: mov %rax, %rcx; <and\|or\|xor> %val, %rcx; lock cmpxchg %rcx, (%ptr); jne .L1` | When old value is returned; if return value is unused, lowered to `lock {and,or,xor}`. |
| `atomic_nand` | All 5 (`Relaxed`..`SeqCst`) | `mov (%ptr), %rax; .L1: mov %rax, %rcx; and %val, %rcx; not %rcx; lock cmpxchg %rcx, (%ptr); jne .L1` | Bitwise `~(old & val)` loop via `lock cmpxchg`. |
| `atomic_{max,min}` (signed) | All 5 (`Relaxed`..`SeqCst`) | `mov (%ptr), %rax; .L1: cmp %val, %rax; mov %val, %rcx; cmov{g,l} %rax, %rcx; lock cmpxchg %rcx, (%ptr); jne .L1` | Uses `cmovg`/`cmovl` for 16/32/64-bit; for 8-bit (`i8`), sign-extends `%al` (`movsbl`) and uses `cmovgl`/`cmovll`. |
| `atomic_{umax,umin}` (unsigned) | All 5 (`Relaxed`..`SeqCst`) | `mov (%ptr), %rax; .L1: cmp %val, %rax; mov %val, %rcx; cmov{a,b} %rax, %rcx; lock cmpxchg %rcx, (%ptr); jne .L1` | Uses `cmova`/`cmovb` for 16/32/64-bit; for 8-bit (`u8`), zero-extends (`movzbl`) and uses `cmoval`/`cmovbl`. |
| `atomic_cxchg` / `atomic_cxchgweak` | All 15 `(succ, fail)` pairs | `mov %cmp, %rax; lock cmpxchg<s/r> %new, (%ptr); sete %dl` | `cxchgweak` lowers identically to `cxchg` on x86; returns `(old: %rax, ok: %dl)`. |
| `atomic_fence` | `Acquire`, `Release`, `AcqRel` | *(no instruction)* | TSO satisfies Acquire/Release/AcqRel in hardware; acts as compiler barrier. |
| `atomic_fence` | `SeqCst` (`x86_64`) | `lock orl $0, -64(%rsp)` (`Linux`/`SysV`) or `lock orl $0, (%rsp)` (`Win64`) | `-64(%rsp)` on SysV x86-64 avoids clobbering the 128-byte red zone (`-128(%rsp)..0(%rsp)` when leaf); Win64 has no red zone. |
| `atomic_fence` | `SeqCst` (`i686`) | `mfence` (with `+sse2`) or `lock orl $0, (%esp)` (with `-sse2`) | Controlled by `Subtarget.hasSSE2()` in `X86InstrInfo.td`. |
| `compiler_fence` | All 4 (`Acquire`..`SeqCst`) | *(no instruction)* | `fence singlethread <ord>` prevents LLVM IR/MachineInstr reordering across the fence. |

#### 3.2 64-bit Atomics on 32-bit x86 (`i686-unknown-linux-gnu` and `i686-pc-windows-msvc`)

Because 32-bit x86 GPRs are 32 bits wide, 64-bit atomic operations (`i64`/`u64`) are expanded
by `X86TargetLowering::shouldExpandAtomicLoadInIR` (`X86ISelLowering.cpp:32514-32528`) and
`AtomicExpandPass`:

1. **64-bit `atomic_load` (`Relaxed`, `Acquire`, `SeqCst`):**
   - **Default (`pentium4`, `+sse2`):** `movq (%eax), %xmm0; movd %xmm0, %eax; pshufd $85, %xmm0, %xmm0; movd %xmm0, %edx; retl`
     (aligned 64-bit SSE2 load into `%xmm0`, unpacked to `%edx:%eax`).
   - **With `-Ctarget-cpu=i586 -Ctarget-feature=-sse2` (`+x87`):**
     `subl $12, %esp; movl 16(%esp), %eax; fildll (%eax); fistpll (%esp); movl (%esp), %eax; movl 4(%esp), %edx; addl $12, %esp; retl`
     (64-bit integer x87 load `fildll` is guaranteed atomic on 8-byte-aligned addresses since
     Pentium; bounced through the stack to `%edx:%eax` because `fildll`/`fistpll` never trap
     on integer bit patterns, unlike `fldl`/`fstpl` which corrupt signaling NaNs).
2. **64-bit `atomic_store`:**
   - **Default (`+sse2`, `Relaxed` / `Release`):**
     `movl 4(%esp), %eax; movsd 8(%esp), %xmm0; movlps %xmm0, (%eax); retl`
   - **Default (`+sse2`, `SeqCst`):**
     `movl 4(%esp), %eax; movsd 8(%esp), %xmm0; movlps %xmm0, (%eax); lock orl $0, (%esp); retl`
   - **With `-sse2` (`+x87`):**
     `fildll (%esp); fistpll (%eax)` (plus trailing `lock orl $0, (%esp)` for `SeqCst`).
3. **64-bit `atomic_xchg`, `atomic_xadd`, `atomic_xsub`, `atomic_and`, `atomic_nand`, `atomic_or`, `atomic_xor`, `atomic_max`, `atomic_min`, `atomic_umax`, `atomic_umin`, `cxchg`, and `cxchgweak`:**
   - All lower to `lock cmpxchg8b (%reg)` loops comparing `%edx:%eax` against `(%reg)` and
     storing `%ecx:%ebx` on match.

#### 3.3 128-bit Atomics on `x86_64` (`+cmpxchg16b` vs. `+cmpxchg16b,+avx`)

In `X86TargetLowering::shouldExpandAtomicLoadInIR` (`X86ISelLowering.cpp:32514-32528`) and
`shouldExpandAtomicStoreInIR` (`L32494-32512`), a 128-bit (`Size == 128`) atomic load or store
is kept as a native SelectionDAG `ATOMIC_LOAD` / `ATOMIC_STORE` **only if** `Subtarget.hasAVX()`
is true; otherwise it returns `AtomicExpansionKind::CmpXChg`:

| 128-bit Operation | `+cmpxchg16b` only (default on `x86_64-pc-windows-{msvc,gnu}`) | `+cmpxchg16b,+avx` (e.g. `-Ctarget-cpu=x86-64-v3`) |
| :--- | :--- | :--- |
| `atomic_load` (`Relaxed`, `Acquire`, `SeqCst`) | `xorl %eax,%eax; xorl %edx,%edx; xorl %ecx,%ecx; xorl %ebx,%ebx; lock cmpxchg16b (%ptr)` | `vmovdqa (%rdi), %xmm0; vmovq %xmm0, %rax; vpextrq $1, %xmm0, %rdx` |
| `atomic_store` (`Relaxed`, `Release`) | `movq (%ptr),%rax; movq 8(%ptr),%rdx; .L1: lock cmpxchg16b (%ptr); jne .L1` | `vmovq %rdx, %xmm0; vmovq %rsi, %xmm1; vpunpcklqdq %xmm0, %xmm1, %xmm0; vmovdqa %xmm0, (%rdi)` |
| `atomic_store` (`SeqCst`) | `movq (%ptr),%rax; movq 8(%ptr),%rdx; .L1: lock cmpxchg16b (%ptr); jne .L1` | `...; vmovdqa %xmm0, (%rdi); lock orl $0, -64(%rsp)` |
| `atomic_xchg`, `xadd`, `xsub`, `and`, `nand`, `or`, `xor`, `max`, `min`, `umax`, `umin` | `lock cmpxchg16b (%ptr)` retry loop (`%rdx:%rax` expected, `%rcx:%rbx` desired) | `lock cmpxchg16b (%ptr)` retry loop (identical to `+cmpxchg16b` only) |
| `cxchg_128`, `cxchgweak_128` | Single `lock cmpxchg16b (%ptr); sete 16(%sret)` | Single `lock cmpxchg16b (%ptr); sete 16(%sret)` |

**Why `+avx` is sound and interoperable with `lock cmpxchg16b`:** Both Intel (since AVX / and
retroactively documented for guaranteed 16-byte-aligned AVX accesses on processors with AVX)
and AMD guarantee that 16-byte-aligned 128-bit `vmovdqa` loads and stores are single-copy
atomic with respect to cache coherency, including concurrent `lock cmpxchg16b` operations on
normal write-back (WB) cacheable memory. Notably, while pure `vmovdqa` loads are read-only
(avoiding page faults on read-only pages), `lock cmpxchg16b` with `0 -> 0` performs a bus-locked
read-modify-write cycle and faults with `SIGSEGV`/`STATUS_ACCESS_VIOLATION` if the 16-byte
atomic resides in read-only memory (`rodata`).

### 4. AArch64 Instruction Lowering Across Feature Levels and Operating Systems

Basis: source (`llvm/lib/Target/AArch64/AArch64ISelLowering.cpp:32150-32460`, `AArch64InstrAtomics.td:1-780`) + execution (`support/atomic_lowering_matrix.json`)

#### 4.1 Widths `8`, `16`, `32`, and `64` bits on AArch64

In the table below, `<b/h/w/x>` denotes the size suffix (`b` for 8-bit, `h` for 16-bit, empty
with `w` register for 32-bit, empty with `x` register for 64-bit) and `<N>` denotes byte size
`1`, `2`, `4`, or `8`:

| Operation | Ordering | Base Armv8.0-A (`-outline-atomics`) | Outline Atomics (`+outline-atomics`, Linux default) | Armv8.1-A LSE (`+lse`) | Armv8.3-A RCpc (`+lse,+rcpc`, macOS default) | Windows AArch64 (`aarch64-pc-windows-msvc` default) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `atomic_load` | `Relaxed` | `ldr<b/h>` `[x0]` | `ldr<b/h>` `[x0]` | `ldr<b/h>` `[x0]` | `ldr<b/h>` `[x0]` | `ldr<b/h>` `[x0]` |
| `atomic_load` | `Acquire` | `ldar<b/h>` `[x0]` | `ldar<b/h>` `[x0]` | `ldar<b/h>` `[x0]` | `ldapr<b/h>` `[x0]` | `ldar<b/h>` `[x0]` |
| `atomic_load` | `SeqCst` | `ldar<b/h>` `[x0]` | `ldar<b/h>` `[x0]` | `ldar<b/h>` `[x0]` | `ldar<b/h>` `[x0]` | `ldar<b/h>` `[x0]` |
| `atomic_store` | `Relaxed` | `str<b/h>` `[x0]` | `str<b/h>` `[x0]` | `str<b/h>` `[x0]` | `str<b/h>` `[x0]` | `str<b/h>` `[x0]` |
| `atomic_store` | `Release` | `stlr<b/h>` `[x0]` | `stlr<b/h>` `[x0]` | `stlr<b/h>` `[x0]` | `stlr<b/h>` `[x0]` | `stlr<b/h>` `[x0]` |
| `atomic_store` | `SeqCst` | `stlr<b/h>` `[x0]` | `stlr<b/h>` `[x0]` | `stlr<b/h>` `[x0]` | `stlr<b/h>` `[x0]` | `stlr<b/h> [x0]; dmb ish` |
| `atomic_xchg` | `Relaxed` / `Acquire` / `Release` / `AcqRel` / `SeqCst` | `ld{,a}xr<b/h>` + `st{,l}xr<b/h>` loop | `bl __aarch64_swp<N>_{relax,acq,rel,acq_rel}` | `swp{,a,l,al}<b/h>` | `swp{,a,l,al}<b/h>` | `ld{,a}xr` + `st{,l}xr` loop (+ `dmb ish` on `SeqCst`) |
| `atomic_xadd` | `Relaxed`..`SeqCst` | `ld{,a}xr` + `add` + `st{,l}xr` loop | `bl __aarch64_ldadd<N>_{relax,acq,rel,acq_rel}` | `ldadd{,a,l,al}<b/h>` | `ldadd{,a,l,al}<b/h>` | `ld{,a}xr` + `add` + `st{,l}xr` loop (+ `dmb ish` on `SeqCst`) |
| `atomic_xsub` | `Relaxed`..`SeqCst` | `ld{,a}xr` + `sub` + `st{,l}xr` loop | `neg x0, x1; bl __aarch64_ldadd<N>_*` | `neg x8, x1; ldadd{,a,l,al}<b/h>` | `neg x8, x1; ldadd{,a,l,al}<b/h>` | `ld{,a}xr` + `sub` + `st{,l}xr` loop (+ `dmb ish` on `SeqCst`) |
| `atomic_and` | `Relaxed`..`SeqCst` | `ld{,a}xr` + `and` + `st{,l}xr` loop | `mvn x0, x1; bl __aarch64_ldclr<N>_*` | `mvn x8, x1; ldclr{,a,l,al}<b/h>` | `mvn x8, x1; ldclr{,a,l,al}<b/h>` | `ld{,a}xr` + `and` + `st{,l}xr` loop (+ `dmb ish` on `SeqCst`) |
| `atomic_or` | `Relaxed`..`SeqCst` | `ld{,a}xr` + `orr` + `st{,l}xr` loop | `bl __aarch64_ldset<N>_*` | `ldset{,a,l,al}<b/h>` | `ldset{,a,l,al}<b/h>` | `ld{,a}xr` + `orr` + `st{,l}xr` loop (+ `dmb ish` on `SeqCst`) |
| `atomic_xor` | `Relaxed`..`SeqCst` | `ld{,a}xr` + `eor` + `st{,l}xr` loop | `bl __aarch64_ldeor<N>_*` | `ldeor{,a,l,al}<b/h>` | `ldeor{,a,l,al}<b/h>` | `ld{,a}xr` + `eor` + `st{,l}xr` loop (+ `dmb ish` on `SeqCst`) |
| `atomic_nand` | `Relaxed`..`SeqCst` | `ld{,a}xr` + `and` + `mvn` + `st{,l}xr` loop | Inline `ld{,a}xr` + `and` + `mvn` + `st{,l}xr` loop (no helper!) | `ldr` + `and` + `mvn` + `cas{,a,l,al}<b/h>` loop | `ldr` + `and` + `mvn` + `cas{,a,l,al}<b/h>` loop | `ld{,a}xr` + `and` + `mvn` + `st{,l}xr` loop (+ `dmb ish` on `SeqCst`) |
| `atomic_{max,min,umax,umin}` | `Relaxed`..`SeqCst` | `ld{,a}xr` + `cmp` + `csel` + `st{,l}xr` loop | Inline `ld{,a}xr` + `cmp` + `csel` + `st{,l}xr` loop (no helper!) | `ld{smax,smin,umax,umin}{,a,l,al}<b/h>` | `ld{smax,smin,umax,umin}{,a,l,al}<b/h>` | `ld{,a}xr` + `cmp` + `csel` + `st{,l}xr` loop (+ `dmb ish` on `SeqCst`) |
| `cxchg` (strong) | `(succ, fail)` | `ld{,a}xr` + `cmp` + `b.ne .Lfail` + `st{,l}xr` + `cbnz .Lloop`; `.Lfail: clrex` | `bl __aarch64_cas<N>_{relax,acq,rel,acq_rel}` + `cmp` + `cset eq` | `cas{,a,l,al}<b/h>` + `cmp` + `cset eq` | `cas{,a,l,al}<b/h>` + `cmp` + `cset eq` | `ld{,a}xr` + `cmp` + `st{,l}xr` loop + `clrex` (+ `dmb ish` on `SeqCst`) |
| `cxchgweak` | `(succ, fail)` | Single-shot `ld{,a}xr` + `cmp` + `b.ne .Lfail` + `st{,l}xr` + `cmp w9, #0; cset eq`; `.Lfail: clrex` | `bl __aarch64_cas<N>_{relax,acq,rel,acq_rel}` + `cmp` + `cset eq` | `cas{,a,l,al}<b/h>` + `cmp` + `cset eq` | `cas{,a,l,al}<b/h>` + `cmp` + `cset eq` | Single-shot `ld{,a}xr` + `st{,l}xr` + `clrex` (+ `dmb ish` on `SeqCst`) |
| `atomic_fence` | `Acquire` | `dmb ishld` | `dmb ishld` | `dmb ishld` | `dmb ishld` | `dmb ishld` |
| `atomic_fence` | `Release`, `AcqRel`, `SeqCst` | `dmb ish` | `dmb ish` | `dmb ish` | `dmb ish` | `dmb ish` |

**Combined CAS ordering selection on AArch64:** Both LL/SC and LSE/`__aarch64_cas*` select
their acquire/release bits from the pair `(succ_ord, fail_ord)`:
- Acquire bit (`a` / `ldaxr`) is set iff `succ_ord ∈ {Acquire, AcqRel, SeqCst}` **or**
  `fail_ord ∈ {Acquire, SeqCst}`.
- Release bit (`l` / `stlxr`) is set iff `succ_ord ∈ {Release, AcqRel, SeqCst}`.

#### 4.2 128-bit Atomics on AArch64 (`v8.0a`, `+outline-atomics`, `+lse`, `+lse2`, `+lse128`)

| 128-bit Operation | Armv8.0-A (`-outline-atomics`) | Outline Atomics (`+outline-atomics`) | Armv8.1-A LSE (`+lse`) | Armv8.4-A LSE2 (`+lse,+rcpc,+lse2`, `apple-m1`) | Armv9.4-A LSE128 (`+lse2,+lse128`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `load(Relaxed)` | `.L1: ldxp x0,x1,[x8]; stxp w9,x0,x1,[x8]; cbnz w9,.L1` | Same `ldxp`+`stxp` loop (no 16B load helper!) | `mov x2,xzr; mov x3,xzr; casp x2,x3,x2,x3,[x0]` | `ldp x0, x1, [x0]` | `ldp x0, x1, [x0]` |
| `load(Acquire)` | `.L1: ldaxp x0,x1,[x8]; stxp w9,x0,x1,[x8]; cbnz w9,.L1` | Same `ldaxp`+`stxp` loop | `mov x2,xzr; mov x3,xzr; caspa x2,x3,x2,x3,[x0]` | `ldp x0, x1, [x0]; dmb ishld` | `ldp x0, x1, [x0]; dmb ishld` |
| `load(SeqCst)` | `.L1: ldaxp x0,x1,[x8]; stlxp w9,x0,x1,[x8]; cbnz w9,.L1` | Same `ldaxp`+`stlxp` loop | `mov x2,xzr; mov x3,xzr; caspal x2,x3,x2,x3,[x0]` | `ldar xzr, [x0]; ldp x0, x1, [x0]; dmb ish` | `ldar xzr, [x0]; ldp x0, x1, [x0]; dmb ish` |
| `store(Relaxed)` | `.L1: ldxp xzr,x8,[x0]; stxp w8,x2,x3,[x0]; cbnz w8,.L1` | Same `ldxp`+`stxp` loop | `ldp x4,x5,[x0]; .L1: casp x6,x7,x2,x3,[x0]; ...; b.ne .L1` | `stp x2, x3, [x0]` | `stp x2, x3, [x0]` |
| `store(Release)` | `.L1: ldxp xzr,x8,[x0]; stlxp w8,x2,x3,[x0]; cbnz w8,.L1` | Same `ldxp`+`stlxp` loop | `ldp x4,x5,[x0]; .L1: caspl x6,x7,x2,x3,[x0]; ...; b.ne .L1` | `dmb ish; stp x2, x3, [x0]` | `swppl x2, x3, [x0]` |
| `store(SeqCst)` | `.L1: ldaxp xzr,x8,[x0]; stlxp w8,x2,x3,[x0]; cbnz w8,.L1` | Same `ldaxp`+`stlxp` loop | `ldp x4,x5,[x0]; .L1: caspal x6,x7,x2,x3,[x0]; ...; b.ne .L1` | `dmb ish; stp x2, x3, [x0]; dmb ish` | `swppal x2, x3, [x0]` |
| `xchg_128` | `ld{,a}xp` + `st{,l}xp` loop | `ld{,a}xp` + `st{,l}xp` loop | `ldp` + `casp{,a,l,al}` loop | `ldp` + `casp{,a,l,al}` loop | `swpp{,a,l,al} x2, x1, [x0]` |
| `or_128` | `ld{,a}xp` + `orr` + `st{,l}xp` loop | `ld{,a}xp` + `orr` + `st{,l}xp` loop | `ldp` + `orr` + `casp{,a,l,al}` loop | `ldp` + `orr` + `casp{,a,l,al}` loop | `ldsetp{,a,l,al} x2, x1, [x0]` |
| `and_128` | `ld{,a}xp` + `and` + `st{,l}xp` loop | `ld{,a}xp` + `and` + `st{,l}xp` loop | `ldp` + `and` + `casp{,a,l,al}` loop | `ldp` + `and` + `casp{,a,l,al}` loop | `mvn` + `ldclrp{,a,l,al} x8, x1, [x0]` |
| `xadd`, `xsub`, `xor`, `nand`, `max`, `min`, `umax`, `umin` (128b) | `ld{,a}xp` + op + `st{,l}xp` loop | `ld{,a}xp` + op + `st{,l}xp` loop | `ldp` + op + `casp{,a,l,al}` loop | `ldp` + op + `casp{,a,l,al}` loop | `ldp` + op + `casp{,a,l,al}` loop |
| `cxchg_128` / `cxchgweak_128` | `ld{,a}xp` + `cmp` + `st{,l}xp` (even on mismatch, write back loaded pair!) | `bl __aarch64_cas16_{relax,acq,rel,acq_rel}` | `casp{,a,l,al} x6, x7, x4, x5, [x0]` | `casp{,a,l,al} x6, x7, x4, x5, [x0]` | `casp{,a,l,al} x6, x7, x4, x5, [x0]` |

**Critical subtlety on 128-bit LL/SC `cxchg` (`AArch64ISelLowering.cpp:32423-32455`):**
Without `+lse`, 128-bit `cxchg` and `cxchgweak` do **not** branch around `stlxp` on comparison
mismatch! Instead, when the loaded pair `(x9, x10)` does not equal `(x2, x3)`, LLVM executes
`stlxp w11, x9, x10, [x0]` (writing back the old value) and retries if `w11 != 0`. This is
required because `ldaxp` alone (unlike `ldaxr`) is only 64-bit single-copy atomic unless paired
with a succeeding `stxp`/`stlxp` to the same exclusive monitor!

#### 4.3 Outline Atomics Runtime Helper Contract (`__aarch64_*`)

On `aarch64-unknown-linux-gnu` (and `aarch64-pc-windows-msvc` starting in `nightly-2026-11-12`),
`+outline-atomics` emits calls to 100 possible helper symbols:
- `__aarch64_{cas,swp,ldadd,ldclr,ldeor,ldset}{1,2,4,8}_{relax,acq,rel,acq_rel}` (96 symbols:
  `x0` = operand / expected, `x1` = desired (for `cas`) or pointer (for RMWs), `x2` = pointer
  (for `cas`), returning old value in `x0`).
- `__aarch64_cas16_{relax,acq,rel,acq_rel}` (4 symbols: `(x0, x1)` = expected, `(x2, x3)` =
  desired, `x4` = pointer, returning old pair in `(x0, x1)`).

**Where the helpers live and how they detect LSE:**
1. **`compiler_builtins` (`library/compiler-builtins/compiler-builtins/src/aarch64_linux.rs` and `aarch64.rs`):**
   Rust's `compiler_builtins` crate (bundled into every `rustc` sysroot and linked into every
   Rust binary/cdylib/staticlib) provides weak/hidden definitions of all 100 `__aarch64_*`
   symbols alongside `libgcc` (`libgcc.a`).
2. **Runtime LSE detection (`__aarch64_have_lse_atomics`):**
   Each helper loads a 1-byte global flag `__aarch64_have_lse_atomics`:
   - If non-zero, it executes the single LSE instruction (`cas*`, `casp*`, `swp*`, `ldadd*`,
     `ldclr*`, `ldeor*`, `ldset*`) and returns (`ret`).
   - If zero, it falls back to an `ldxr`/`ldaxr` + `stxr`/`stlxr` (or `ldxp`/`stxp`) loop.
   - On Linux/Android/FreeBSD, a `.init_array` constructor (`init_have_lse_atomics`) queries
     `getauxval(AT_HWCAP)` (`AT_HWCAP = 16`) and tests `HWCAP_ATOMICS` (`1 << 8 = 0x100`),
     storing `1` or `0` into `__aarch64_have_lse_atomics`.

### 5. Cross-Compiler (`Clang`, `GCC`, `MSVC`) and Cross-Backend (`Cranelift`, `GCC`) Compatibility

Basis: source + derived

1. **Clang 23.1.1 and GCC 14/15 C11/C++20 `<atomic>` compatibility:**
   - **8, 16, 32, and 64-bit atomics:** `rustc` + LLVM 23.1.1 is 100% compatible with Clang and
     GCC across all 8 Tier 1 targets. On AArch64 with `+rcpc` (`apple-m1`), `Acquire` loads use
     `ldapr` while `SeqCst` loads use `ldar` and `Release`/`SeqCst` stores use `stlr`; mixing
     old (`ldar`) and new (`ldapr`) code preserves both Release-Acquire synchronization and SC
     for data-race-free programs (and preserves IRIW sequential consistency because `SeqCst`
     loads remain `ldar`).
   - **Windows AArch64 MSVC `<atomic>` compatibility:** Because LLVM emits trailing `dmb ish` on
     `SeqCst` stores/RMWs when targeting `aarch64-pc-windows-msvc`
     (`AArch64ISelLowering.cpp:32234-32255`), Rust `SeqCst` stores are properly ordered before
     MSVC-compiled `SeqCst` loads (`ldar` without trailing barrier).
   - **128-bit atomics (`AtomicU128` / `_Atomic __int128`) on x86-64 and AArch64:**
     - **With Clang 17+ and GCC 14+ on AArch64 (`+lse2`) and x86-64 (`+cx16,+avx`):** Compatible.
       Both GCC (`libatomic` / inline since GCC 14) and Clang/LLVM use `vmovdqa` (`x86_64 +avx`)
       and `ldp`/`stp` (`aarch64 +lse2`) alongside `cmpxchg16b` and `casp`.
     - **Hazard with legacy GCC `< 13` or `-mno-cx16` `__atomic_*_16` libatomic locks:** If C
       code is compiled without `-mcx16` on `x86_64-unknown-linux-gnu` so that `_Atomic __int128`
       calls lock-based `libatomic` routines, while Rust uses `AtomicU128` with
       `-Ctarget-feature=+cmpxchg16b` (lock-free `cmpxchg16b` / `vmovdqa`), concurrent accesses
       to the same 16-byte address will race! Both languages must agree on lock-free 16-byte
       instructions.
     - **Read-only memory hazard (`cmpxchg16b` vs. `vmovdqa`):** On `x86_64` with `+cmpxchg16b`
       and `-avx`, `AtomicU128::load` executes `lock cmpxchg16b`, which faults on read-only
       memory pages (`rodata` / `mmap(PROT_READ)`), whereas `+avx` (`vmovdqa`) and AArch64
       `+lse2` (`ldp`) succeed on read-only memory.
2. **`rustc_codegen_cranelift` (`compiler/rustc_codegen_cranelift/src/intrinsics/mod.rs:862-1040`):**
   - Lowers `atomic_load`, `atomic_store`, `atomic_xchg`, `atomic_xadd`, `atomic_xsub`,
     `atomic_and`, `atomic_nand`, `atomic_or`, `atomic_xor`, `atomic_max`, `atomic_min`,
     `atomic_umax`, `atomic_umin`, `atomic_cxchg`, `atomic_cxchgweak`, and `atomic_fence` to
     CLIF `atomic_load`, `atomic_store`, `atomic_rmw`, `atomic_cas`, and `fence` instructions.
   - **Critical difference:** Cranelift unconditionally emits **SeqCst** barriers/instructions
     for all atomic operations regardless of the Rust ordering parameter (`Relaxed`, `Acquire`,
     `Release`, `AcqRel`, `SeqCst` all lower to the strongest CLIF atomic primitives, and all
     `atomic_fence` orderings lower to `bcx.ins().fence()`). Because stronger hardware mappings
     monotonically refine weaker ones on both x86-TSO and AArch64, mixing Cranelift-compiled
     crates and LLVM-compiled crates in the same binary is memory-model sound!
   - **128-bit limitation in Cranelift:** For 128-bit `atomic_load` and `atomic_store` on
     non-x86_64 or when native 128-bit CLIF atomic load/store is unavailable, Cranelift lowers
     them via `atomic_cas` (`0 -> 0` for load, CAS retry loop for store) or rejects unsupported
     128-bit RMWs depending on ISA backend support.
3. **`rustc_codegen_gcc` (`compiler/rustc_codegen_gcc/src/builder.rs`):**
   - Lowers Rust atomic operations to `libgccjit` `__atomic_load_n`, `__atomic_store_n`,
     `__atomic_exchange_n`, `__atomic_compare_exchange_n`, `__atomic_fetch_{add,sub,and,nand,or,xor}`,
     and `__atomic_thread_fence` builtins with matching `MEMMODEL_*` constants, plus CAS loops
     for `max`/`min`/`umax`/`umin`, producing GCC's native atomic instruction sequences.

## Boundaries

- **Non-Tier-1 weak-memory architectures (`powerpc64`, `riscv64gc`, `arm`v6/v7, `mips`, `s390x`):**
  Not examined in this package's empirical assembly matrix (which covers all 8 Tier 1 targets
  across `x86_64`, `i686`, and `aarch64`).
- **Volatile + atomic combinations and `AtomicPtr` provenance:** `AtomicPtr` uses identical
  64-bit (`x86_64`/`aarch64`) or 32-bit (`i686`) integer instructions as `AtomicUsize`; strict
  provenance rules for `AtomicPtr::fetch_ptr_add` are covered in
  `rust-allocation-provenance-and-stack-lifetime-semantics`.
- **Proprietary MSVC `cl.exe` execution:** Direct execution of Microsoft's proprietary `cl.exe`
  was not performed due to EULA restrictions; MSVC compatibility on `aarch64-pc-windows-msvc`
  and `x86_64-pc-windows-msvc` is established from LLVM's `AArch64ISelLowering.cpp` /
  `X86ISelLowering.cpp` source and cross-compiled `rustc` assembly output.

## Evidence

- **Primary upstream sources (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:117-147,377-522` — MIR intrinsic dispatch
    for `atomic_*` and ordering parsing.
  - `compiler/rustc_codegen_llvm/src/builder.rs:701-722,928-945,1368-1431` — LLVM IR emission
    for `atomic_load`, `atomic_store`, `atomic_cmpxchg`, `atomic_rmw`, and `atomic_fence`.
  - `compiler/rustc_codegen_ssa/src/target_features.rs:509-525` — dynamic `max_atomic_width = 128`
    promotion when `cmpxchg16b` is enabled on `x86_64`.
  - `compiler/rustc_codegen_cranelift/src/intrinsics/mod.rs:862-1040` — Cranelift atomic lowering.
- **Primary upstream sources (`rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
  - `llvm/lib/CodeGen/AtomicExpandPass.cpp:1-2250` — generic IR-level LL/SC and CAS-loop
    expansion pass.
  - `llvm/lib/Target/X86/X86ISelLowering.cpp:32480-33060,38814-38910` — `shouldExpandAtomicLoadInIR`
    (`Subtarget.hasAVX()` 128-bit `vmovdqa` rule), `shouldExpandAtomicStoreInIR`, `LCMPXCHG8B`,
    and `LCMPXCHG16B`.
  - `llvm/lib/Target/AArch64/AArch64ISelLowering.cpp:1011-1105,32150-32460` — outline atomics,
    `hasLSE()`, `hasLSE2()`, `hasLSE128()`, `hasRCPC()`, `shouldInsertTrailingSeqCstFenceForMSVC`,
    and 128-bit `ldxp`/`stxp` vs. `ldp`/`stp` vs. `casp`/`swpp` lowering.
  - `llvm/lib/Target/AArch64/AArch64InstrAtomics.td:1-780` — TableGen patterns for `LDAPR`,
    `STLR`, `CAS`, `CASP`, `SWPP`, `LDCLRP`, `LDSETP`, and `dmb ish` / `dmb ishld`.
- **Preserved support artifacts:**
  - `support/atomic_probe.rs` — 373-function `#![no_std]` Rust probe covering all 15 atomic
    operations (`load`, `store`, `xchg`, `xadd`, `xsub`, `and`, `nand`, `or`, `xor`, `max`,
    `min`, `umax`, `umin`, `cxchg`, `cxchgweak`) across all 5 widths (`8`, `16`, `32`, `64`,
    `128` bits) and all valid orderings, plus `fence` and `compiler_fence`.
  - `support/atomic_lowering_matrix.json` — complete machine-readable matrix of extracted
    assembly instruction sequences across all 17 target/feature configurations (`5,831` total
    function entries).
  - `support/asm/*.s` — representative full assembly outputs for `x86_64`, `i686`, and `aarch64`
    configurations.

## Revalidation

To revalidate the atomic lowering matrix against a newer `rustc` or LLVM revision:

```bash
rustc +1.99.1 --edition=2021 --crate-type=rlib -Copt-level=3 --emit=asm \
  --target aarch64-unknown-linux-gnu \
  reports/tier1-atomics-and-fences-instruction-lowering/support/atomic_probe.rs \
  -o /tmp/aarch64_outline.s
```

Run the same command across the 17 target/flag combinations listed in
`support/atomic_lowering_matrix.json` (passing `--cfg has_u128` for configurations with
128-bit atomic support) and diff the per-function instruction sequences against
`support/atomic_lowering_matrix.json`.
