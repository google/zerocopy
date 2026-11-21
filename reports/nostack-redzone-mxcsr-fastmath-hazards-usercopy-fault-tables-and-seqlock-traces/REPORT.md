# `options(nostack)` Red-Zone Clobbers, `MXCSR` and `crtfastmath.o` Poisoning, Non-Naked Constant-Time Wrapper Leaks, Sideband ELF Fault Overlays, and Tear-Free Seqlock Trace Semantics

## Summary

Soundly verifying Rust programs that cross inline-assembly (`core::arch::asm!`, `naked_asm!`), C/assembly FFI object (`.o`/`.so`), and MIR-to-ISA boundaries requires closing five coupled machine-state, spatial, control-flow, side-channel, and weak-memory seams where naive endpoint or source-level contracts fail silently:

1. **`options(nostack)` requires a step-wise red-zone and `rsp` invariant, not `rsp_exit == rsp_entry` (`Basis: normative + source + execution + derived`):** In `rustc 1.99.1` and `1.102.0-nightly`, `options(nostack)` sets `alignstack = false` (`rustc_codegen_llvm/src/asm.rs:334`), suppressing `InlineAsm::Extra_IsAlignStack` so `MFI.adjustsStack()` remains `false` (`FinalizeISel.cpp:61-62`). In leaf functions on `x86_64-unknown-linux-gnu`, `X86FrameLowering.cpp:1780-1793` therefore allocates live safe Rust stack locals inside the 128-byte System V red zone `[rsp - 128, rsp)` (`-16(%rsp)` and `-8(%rsp)` at `-C opt-level=3`). Live execution confirms that balanced `push`/`pop`, `pushfq`/`pop`, and internal `call`/`ret` inside `options(nostack)` satisfy `rsp_exit == rsp_entry` (`0` delta) while **silently overwriting safe Rust locals** with arbitrary registers (`0xdeadbeefcafebabe`), live `RFLAGS` (`0x246`), or ASLR `.text` return addresses. Omitting `nostack` (`subq $24, %rsp`) or compiling with `-C no-redzone=yes` (`subq $16, %rsp`) shifts Rust locals above `rsp`.
2. **`MXCSR` splits into preserved control bits (`[15:6]`) vs. sticky status flags (`[5:0]`)—unless `options(preserves_flags)` or `crtfastmath.o` intervenes (`Basis: normative + source + execution + derived`):**
   - *`options(preserves_flags)` trap:* Normatively (`r[asm.rules.preserved-registers]`, `inline-assembly.md:1368-1373`), setting `options(preserves_flags)` on x86 **forbids mutating `MXCSR[5:0]` (`PE, UE, OE, ZE, DE, IE`)**—making almost every SSE/AVX floating-point `asm!` block with `preserves_flags` immediate UB whenever `vaddss`/`vmulss` sets `PE = 0x20` (`1.0 + 0.1 -> 0x1fa0`) or `vminss`/`vmaxss` sets `IE = 0x01` (`0x1f81`, raised even on **quiet** NaNs!). Meanwhile, `rustc` rejects `out("mxcsr") _` (`unknown register`) and emits only `~{dirflag},~{fpsr},~{flags}` (`X86::FPSW`, x87 status word) when `preserves_flags` is omitted.
   - *Pre-`main` `crtfastmath.o` poisoning:* Linking an executable with `gcc 15.2.0 -ffast-math`/`-Ofast`—or dynamically linking a shared `.so` compiled with `gcc -shared -mdaz-ftz` (which sits outside `%{!shared:...}` in GCC 15.2.0's `ENDFILE_SPEC`)—injects `set_fast_math` into `.init_array`, flipping `MXCSR` from `0x1f80` to `0x9fc0` (`DAZ | FTZ`) **before `main()`** and silently flushing 100% safe Rust subnormal arithmetic to `0.0` (`0x00400000 + 0.0 -> 0x00000000` at runtime vs. `0x00400000` in CTFE `const`, with zero FFI calls).
   - *`vminss`/`vmaxss`/`vfmadd213ss` corner asymmetries:* Hardware `vminss`/`vmaxss` returns `SRC2` on both `(-0.0, +0.0)` and `NaN`, raises `IE = 0x01` on `qNaN`, and passes `sNaN` (`0x7f800001`) un-quieted when in `SRC2`; Rust `f32::min`/`max` (`minNum`/`maxNum`) inherits `minss`'s signed-zero order dependence (`min(-0.0, +0.0) = +0.0`, `min(+0.0, -0.0) = -0.0`) while masking `qNaN`, whereas nightly `f32::minimum`/`maximum` enforces `-0.0 < +0.0` and propagates NaNs; `f32::mul_add` / `vfmadd213ss` differs from `a * b + c` both under catastrophic cancellation (`-2^-46` vs. `+0.0`) and 1-ULP double-rounding midpoint flips (`0x3f800004` vs. `0x3f800003`).
3. **Non-naked constant-time wrappers around verified `asm!` leak secrets via `black_box` stack spills, short-circuit branch induction, `X86CmovConversion`, and non-DOIT opcodes (`Basis: documentation + source + execution`):** In `Runtime(PostCleanup)` MIR, `core::hint::black_box` is a `TerminatorKind::Call` (lowered to `core::intrinsics::black_box` in optimized MIR, **not** `TerminatorKind::InlineAsm`), which `Builder::black_box` (`rustc_codegen_llvm/src/intrinsic.rs:88-120`) lowers to an `alloca` + `call void asm sideeffect "", "r,~{memory}"(ptr nonnull %_0)` (`alignstack = false`). Passing the stack slot address defeats SROA even for `u8`/`bool`, spilling secret bytes into the un-erased red zone (`-1(%rsp)`, verified live at `[caller_rsp - 9]`), and writing `black_box(c1) && black_box(c2)` **forces** LLVM to emit a secret-dependent `jne` branch whereas `(c1 && c2)` compiles to branchless `andl`. In innermost loops, `X86CmovConversion.cpp` converts high-depth-cost Rust selects into `je` branches and conditional loads while `asm!` `cmove` remains branchless, and `#[unsafe(naked)]` `naked_asm!` eliminates all wrapper spills and branches. At the ISA level (`Intel DOIT Guidance`, `594` Table-1 mnemonics), `CMOVcc`, `VPSHUFB`, `VPERMD`, `VAES*`, `VPCLMULQDQ`, and `VPMULLD`/`Q`/`UDQ` satisfy DOIT under `IA32_UARCH_MISC_CTL[DOITM] = 1`, whereas `VGATHER*`/`VPGATHER*`, `VSCATTER*`, `VPERMB`, `DIV`/`IDIV`, and all IEEE-754 floating-point instructions (`VADDPS`, `VMULPS`, `VFMADD*`) are excluded.
4. **Sideband ELF control-flow overlays (`usercopy` / `__ex_table`, `rseq`, and `target_clones` `IFUNC`s) require partial-write fault transitions and `XCR0` `xgetbv` invariants (`Basis: source + execution + derived`):** Live Linux `x86_64` execution of both Fuchsia Starnix half-open sentinel ranges (`[starnix_usercopy_start, starnix_usercopy_end) -> starnix_usercopy_fault`) and Linux `.pushsection __ex_table` PC-relative descriptors (`rep movsb`) across mapped + `PROT_NONE` pages (`19` valid bytes + `13` unmapped bytes) confirms `SA_SIGINFO` `REG_RIP` redirection returns `rem = 13` with **`dst[0..19]` already mutated in memory**—refuting atomic rollback fault models—unlike Linux `struct rseq_cs`, whose `[start_ip, start_ip + post_commit_offset)` abort window restricts shared-memory mutation to the final single commit store. Disassembly of `gcc 15.2.0` `__attribute__((target_clones("default","avx2","avx512f")))` confirms `STT_GNU_IFUNC` + `R_X86_64_IRELATIVE` calls `__cpu_indicator_init`, which gates `CPUID` on `xgetbv` (`0f 01 d0`, `XCR0[2:1] == 0b11`).
5. **Upward-compatible `MemTraceEvent` algebra mechanizes tear-free optimistic seqlocks and zero-overhead sequential collapse in Lean `v4.34.1` (`Basis: normative + execution + derived`):** Twelve kernel-checked theorems in [`support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean`](support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean) (`Init`-only, zero `sorryAx`, axioms $\subseteq \{\texttt{propext}, \texttt{Quot.sound}\}$) prove `NostackRedZoneInvariant`, `SplitMxcsrFrameSlack`, `fault_overlay_usercopy_partial_write_exact`, `rseq_pre_commit_abort_preserves_mem`, data-race UB of `.plain` seqlock readers (`plain_seqlock_reader_triggers_data_race_ub`), race-freedom plus multi-word snapshot coherence of `.singleCopyAtomic` (`asm!` `mov` / `READ_ONCE`) seqlock readers (`seqlock_single_copy_atomic_reader_sound`), and extensional collapse to sequential memory when concurrency is absent (`sequential_schedule_collapses_mem_trace_to_state`).

## Applicability

This report governs compiler codegen analysis, formal MIR-to-ISA verification, cryptographic side-channel auditing, binary fault/relocation modeling, and concurrent memory-trace design on `x86_64` Linux/ELF targets.

### Examined Subjects and Their Relationships

| Subject | Pinned Identity | Role in Investigation |
| :--- | :--- | :--- |
| **`rustc` `1.99.1` & LLVM `23.1.1`** | `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `llvm/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` | Executed on `x86_64-unknown-linux-gnu` (`-C opt-level=3`, `--emit=mir,llvm-ir,asm`) for red-zone clobbers, `MXCSR` clobbers, `f32` corners, and CT wrapper leaks |
| **`rustc` `1.102.0-nightly` & LLVM `23.1.5`** | `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `llvm/llvm-project@0a5579eb649d3634a9c30ac873300cc2944fa070` | Executed for `-Zdump-mir=runtime-post-cleanup`, `#![feature(float_minimum_maximum)]` (`f32::minimum`/`maximum`), and cross-version parity checks; primary source inspection of `asm.rs`, `intrinsic.rs`, `FinalizeISel.cpp`, `X86FrameLowering.cpp`, `X86InstrSSE.td`, and `X86CmovConversion.cpp` |
| **The Rust Reference** | `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative specification of `options(nostack)` (`r[asm.options.supported-options-nostack]`) and `options(preserves_flags)` (`r[asm.rules.preserved-registers]`) |
| **GCC `15.2.0`** | `gcc-mirror/gcc@5115c7e447fc07457443df874bf57840e8316d5f` (`Debian 15.2.0-14`, `GNU ld 2.47`) | Source inspection (`libgcc/config/i386/crtfastmath.c`) and live execution of `ENDFILE_SPEC` `crtfastmath.o` poisoning, `SA_SIGINFO` `usercopy` fault overlays, and `target_clones` `IFUNC` resolvers |
| **Linux Kernel & Fuchsia Starnix** | `torvalds/linux@5f22fb20497f4983094131f00a734362300d22d2`, `fuchsia.googlesource.com/fuchsia@fd31be1516bd2906c5b46be6c3ca3aa1adb162c0` | Reference implementations of `_ASM_EXTABLE_TYPE` (`arch/x86/include/asm/asm.h`), `struct rseq_cs` (`include/uapi/linux/rseq.h`), and `hermetic_copy.S` / `hermetic_copy_error.S` |
| **MiniRust & Lean `v4.34.1`** | `minirust/minirust@063d784186d3252bee242217f218223205c0b568`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` | Normative `Atomicity::None` data-race baseline and kernel-checked mechanization (`-DElab.async=false -Ddebug.skipKernelTC=false`) |
| **Intel DOIT ISA Guidance** | Docs `768873` (`2026-11-13`) & `759656` (`2026-02-23`) | Architectural specification of `IA32_ARCH_CAPABILITIES[12]`, `IA32_UARCH_MISC_CTL[0]`, `MCDT_NO`, and the `594` documented DOIT mnemonics |

### Relationship to Existing Corpus Reports and Scope Qualifications

This report extends—without repeating—five sibling corpus packages:
- `production-rust-ffi-inline-asm-workloads-and-adversarial-bypass-taxonomy` (which cataloged Starnix/Linux/crypto workloads and demonstrated red-zone sentinel corruption on a synthetic `[rsp - 8]` asm store, whereas Section 1 here proves LLVM allocates **pure safe Rust locals** inside `[rsp - 128, rsp)` across `options(nostack)` and derives the exact step-wise invariant);
- `rust-vs-inline-asm-behavioral-equivalence-for-verified-hot-loop-optimization` and `compiler-preservation-of-constant-time-secret-erasure-and-speculative-fences` (extended in Section 3 with the exact 4-stage `Runtime(PostCleanup)` MIR $\to$ machine-code lowering of `core::hint::black_box`, `black_box` + `&&` branch induction, and Intel's `594`-mnemonic DOIT boundary);
- `ieee754-dynamic-rounding-modes-sticky-exception-csrs-and-stateful-floating-point-verification` and `rust-floating-point-semantics-llvm-lowering-and-isa-behavior` (extended in Section 2 with the `r[asm.rules.preserved-registers]` vs. `vaddss`/`vminss` sticky-flag UB conflict, GCC 15.2.0 `ENDFILE_SPEC` `-ffast-math` vs. `-mdaz-ftz` `.init_array` poisoning of safe Rust, and the `min`/`minimum`/`vminss`/`vfmadd213ss` corner tables);
- `reentrant-ffi-mixed-mir-isa-call-stacks-tree-borrows-and-oracle-composition`, `rust-weak-memory-atomics-mir-llvm-to-x86-aarch64-lowering-and-fence-soundness`, and `rcu-qsbr-hazard-pointers-seqlocks-and-safe-memory-reclamation-verification` (whose single-threaded `OpenComponent` boundary specifically left weak-memory/seqlock traces unexamined, closed here in Section 5).

Execution measurements were collected on `Linux 7.1.6 x86_64` (`AVX`/`AVX2`/`AVX-512F`/`FMA`). Across all shared capabilities, `rustc 1.99.1` and `rustc 1.102.0-nightly` exhibited identical code generation and runtime results; `f32::minimum` and `f32::maximum` (`#![feature(float_minimum_maximum)]`) apply specifically to `1.102.0-nightly`.

## Findings

### 1. `options(nostack)` vs. the System V 128-Byte Red Zone (`[rsp - 128, rsp)`)

`Basis: normative + source + execution + derived` ([`support/probe_redzone_mxcsr_and_fastmath.py`](support/probe_redzone_mxcsr_and_fastmath.py), [`support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean`](support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean))

#### 1.1 Compiler Lowering Chain from `options(nostack)` to Red-Zone Stack-Slot Allocation

Under `rust-lang/reference@c9cc32825b03` (`src/inline-assembly.md:1229-1238`, `r[asm.options.supported-options-nostack]`), `options(nostack)` promises that the assembly block *"does not push data to the stack, or write to the stack red-zone (if supported by the target)"*, explicitly marking `asm!("push rax", "pop rax", options(nostack))` as Undefined Behavior. Tracing `rustc` into LLVM `23.1.1`/`23.1.5` exposes the exact four-step mechanism that makes violating this rule corrupt safe Rust locals:

1. **`rustc_codegen_llvm/src/asm.rs:334`:** Computes `let alignstack = !options.contains(InlineAsmOptions::NOSTACK);` and passes `alignstack` into `llvm::LLVMRustInlineAsm` (`L578`).
2. **`llvm/lib/CodeGen/SelectionDAG/SelectionDAGBuilder.cpp:10308-10309` & `MachineInstr.cpp:914-921`:** Sets `InlineAsm::Extra_IsAlignStack` in `MIOp_ExtraInfo` if and only if `IA->isAlignStack()` is true (`isStackAligningInlineAsm()`).
3. **`llvm/lib/CodeGen/FinalizeISel.cpp:61-62`:** Executes `if (TII->isFrameInstr(MI) || MI.isStackAligningInlineAsm()) MF.getFrameInfo().setAdjustsStack(true);`. When `options(nostack)` is **present**, `isStackAligningInlineAsm()` is `false`, so in a leaf function (zero `CALL` instructions), `MFI.adjustsStack()` stays **`false`**.
4. **`llvm/lib/Target/X86/X86FrameLowering.cpp:1486-1494, 1780-1793`:** Because `has128ByteRedZone(MF)` is `true` (64-bit non-Win64 without `Attribute::NoRedZone`) and `!MFI.adjustsStack()` holds, `emitPrologue` executes `StackSize = std::max(MinSize, StackSize > 128 ? StackSize - 128 : 0);`, **omitting `subq %rsp` entirely** and allocating up to `128` bytes of live safe Rust stack locals at negative offsets `[rsp - 128, rsp)` across the `asm!` block.

#### 1.2 Live Silent Corruption of Safe Rust Locals Under `rsp_exit == rsp_entry`

In `support/probe_redzone_mxcsr_and_fastmath.py`, leaf functions declare a safe Rust array `let mut safe_locals: [u64; 2] = [0x1122_3344_5566_7788, 0x99aa_bbcc_ddee_ff00];` indexed dynamically after an `asm!` block. Both `rustc 1.99.1` and `1.102.0-nightly` at `-C opt-level=3` emit identical machine code placing `safe_locals` at `-16(%rsp)` and `-8(%rsp)`:

```asm
victim_nostack_push_pop:
  movq %rdi, %rax
  movq %rsi, -16(%rsp)        # safe_locals[0] = 0x1122334455667788
  movq %rdx, -8(%rsp)         # safe_locals[1] = 0x99aabbccddeeff00 (at rsp - 8!)
  #APP
  movq %rsp, %rdi
  pushq %r8                   # decrements %rsp by 8, overwrites -8(%rsp_entry)!
  popq %rsi                   # restores %rsp == %rsp_entry!
  movq %rsp, %rdx
  #NO_APP
  andl $1, %ecx
  movq -16(%rsp,%rcx,8), %rsi # reads corrupted safe_locals!
```

| Variant (`-C opt-level=3`, `1.99.1` & `1.102.0-nightly`) | Frame Allocation | `rsp_before ^ rsp_after` | `safe_locals[0]` (`-16(%rsp)`) | `safe_locals[1]` (`-8(%rsp)`) | Outcome |
| :--- | :--- | :---: | :--- | :--- | :--- |
| `push {p}; pop {sc}` + `options(nostack)` (default SysV) | `0 B` (red zone `-16..0(%rsp)`) | `0` (`rsp_exit == rsp_entry`) | `0x1122334455667788` | **`0xdeadbeefcafebabe`** | **Silent safe-local corruption** |
| `pushfq; pop {fc}` + `options(nostack)` (default SysV) | `0 B` (red zone `-16..0(%rsp)`) | `0` (`rsp_exit == rsp_entry`) | `0x1122334455667788` | **`0x0000000000000246`** | **Leaks live `RFLAGS` into local** |
| `call 2f; jmp 3f; 2: ret; 3:` + `options(nostack)` | `0 B` (red zone `-16..0(%rsp)`) | `0` (`rsp_exit == rsp_entry`) | `0x1122334455667788` | **`0x00005579f6760da5`** | **Leaks ASLR `.text` RIP into local** |
| `push {p}; pop {sc}` **without** `nostack` (default SysV) | `subq $24, %rsp` (`8..24(%rsp)`) | `0` | `0x1122334455667788` | `0x99aabbccddeeff00` | Safe (`alignstack` shifts frame above `%rsp`) |
| `push {p}; pop {sc}` + `options(nostack)` + `-C no-redzone=yes` | `subq $16, %rsp` (`0..16(%rsp)`) | `0` | `0x1122334455667788` | `0x99aabbccddeeff00` | Locals uncorrupted (`NoRedZone` disables red zone) |

#### 1.3 Exact Step-Wise Invariant Required for `options(nostack)`

An endpoint check `rsp_exit == rsp_entry` is **unsound** (`naive_endpoint_nostack_corrupts_redzone_local` in `support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean`). Let $R \in \{0, 128\}$ denote the active ABI red-zone width ($R = 128$ on System V `x86_64` and `aarch64-apple-darwin` without `-C no-redzone=yes`; $R = 0$ under `-C no-redzone=yes`, Win64, Linux `aarch64`, or `riscv64`). Sound verification of `options(nostack)` over micro-step trace $\sigma_0 \to \sigma_1 \to \dots \to \sigma_n$ (`stepwise_nostack_preserves_redzone_and_frame`) requires at **every intermediate step $k$**:
1. **Monotone stack-pointer floor:** $\sigma_k.\text{rsp} \ge \sigma_0.\text{rsp}$ (and $\sigma_n.\text{rsp} = \sigma_0.\text{rsp}$). Even when $R = 0$ (`-C no-redzone=yes`), temporarily decrementing `rsp` without OS red-zone protection exposes $[\sigma_k.\text{rsp}, \sigma_0.\text{rsp})$ to asynchronous signal or kernel interrupt frames sharing the stack; and when $R = 128$, decrementing `rsp` shifts a POSIX signal delivery frame downward into $[\sigma_k.\text{rsp} - 128, \sigma_0.\text{rsp} - 128)$ or overwrites $[\sigma_0.\text{rsp} - 128, \sigma_0.\text{rsp})$ directly on `push`/`call`.
2. **Caller-frame and red-zone write disjointness:** Every store effective address $a$ at step $k$ outside explicitly passed mutable pointer allocations (`explicitMut`) must satisfy $a < \sigma_0.\text{rsp} - R$ (disjoint from both the red zone $[\sigma_0.\text{rsp} - R, \sigma_0.\text{rsp})$ and the caller stack frame $[\sigma_0.\text{rsp}, \text{stack\_top})$).

---

### 2. `MXCSR` Partitioning, `crtfastmath.o` Pre-`main` Poisoning, and `vminss`/`vfmadd` Corner Semantics

`Basis: normative + source + execution + derived` ([`support/probe_redzone_mxcsr_and_fastmath.py`](support/probe_redzone_mxcsr_and_fastmath.py), [`support/probe_redzone_mxcsr_and_fastmath_results.json`](support/probe_redzone_mxcsr_and_fastmath_results.json))

#### 2.1 Three-Way Tension Across `options(preserves_flags)`, `rustc`, and LLVM `MXCSR` Modeling

Inspecting `rust-lang/reference@c9cc32825b03`, `rust-lang/rust@3ef0c22cd`, and `llvm/llvm-project@0a5579eb6` uncovers a sharp normative-vs-implementation hazard on `x86`/`x86_64`:

- **Normative rule (`src/inline-assembly.md:1368-1373`, `r[asm.rules.preserved-registers]`):** Explicitly requires that **if `options(preserves_flags)` is set**, *"Floating-point exception flags in `MXCSR` (PE, UE, OE, ZE, DE, IE)"* **must be restored upon exiting the assembly code**.
- **Hardware reality (`hardware_mxcsr_sticky_transitions`):** Starting from default `MXCSR = 0x1f80`, `addss(1.0, 0.1)` sets `PE` (`0x1fa0`), `minss(qNaN, 1.0)` sets `IE` (`0x1f81`), `addss(subnormal, 1.0)` sets `PE | DE` (`0x1fa2`), `divss(1.0, 0.0)` sets `ZE` (`0x1f84`), `mulss(MAX, 2.0)` sets `PE | OE` (`0x1fa8`), and `mulss(MIN_POSITIVE, 0.3)` sets `PE | UE` (`0x1fb0`). Consequently, **attaching `options(preserves_flags)` to almost any SSE/AVX floating-point `asm!` block commits immediate normative UB** (`vaddps_inexact_violates_normative_preserves_flags_but_satisfies_split`).
- **`rustc` & LLVM lowering (`asm.rs:264-270`, `X86ISelLowering.cpp:64423-64424`, `X86InstrSSE.td:2660, 2690, 3282-3298`):** Both `rustc 1.99.1` and `1.102.0-nightly` **reject** `out("mxcsr") _` (`error: invalid register 'mxcsr': unknown register`). Omitting `preserves_flags` is the **only** valid Rust way to permit `MXCSR[5:0]` mutation, which lowers in LLVM IR to `"=&x,0,x,~{dirflag},~{fpsr},~{flags}"`—where `{fpsr}` maps to legacy x87 `X86::FPSW` (`X86ISelLowering.cpp:64424`), **not** `X86::MXCSR`. Inside LLVM's default FP environment, `X86InstrSSE.td` marks SSE/AVX arithmetic with `Uses = [MXCSR], mayRaiseFPException = 1` (omitting `Defs = [MXCSR]`, which appears only on `LDMXCSR`/`VLDMXCSR` at `L3282-3294`).
- **Required ISA Verification Contract (`SplitMxcsrFrameSlack`):** For SysV FFI calls and `asm!` blocks *without* `options(preserves_flags)`, `MXCSR` partitions into **preserved `Frame` (`MXCSR[15:6]` = `0x1f80`: `FTZ=0, RC=RNE, masks=0x3f, DAZ=0`)** and **monotonic `Slack` (`MXCSR[5:0]` sticky exception flags)**. When `options(preserves_flags)` *is* set, a sound verifier must strictly enforce `mExit.stickyFlags == mEntry.stickyFlags`.

#### 2.2 Global Pre-`main` `MXCSR` Poisoning via `gcc 15.2.0` `crtfastmath.o`

In `gcc-mirror/gcc@5115c7e447fc` (`libgcc/config/i386/crtfastmath.c:82-98`), `static void __attribute__((constructor)) set_fast_math(void)` executes `stmxcsr -0x4(%rsp); or $0x8040, %eax; ldmxcsr -0x8(%rsp)` via `.init_array` (`R_X86_64_64 .text.startup + 0` in `/usr/lib/gcc/x86_64-linux-gnu/15/crtfastmath.o`). Inspecting `gcc 15.2.0 -dumpspecs` reveals an exact asymmetric link rule:

```text
%{mdaz-ftz:crtfastmath.o%s;Ofast|ffast-math|funsafe-math-optimizations:%{!shared:%{!mno-daz-ftz:crtfastmath.o%s}}}
```

Testing all four linkage topologies against a **100% safe Rust** subnormal probe (`X = f32::from_bits(0x0040_0000)`, evaluating `X + 0.0` and `X * 0.5` both at runtime and in `const` CTFE, with **zero FFI calls** executed):

| Linkage Topology (`x86_64-unknown-linux-gnu`) | `set_fast_math` Linked? | `MXCSR` at `main()` | Safe Rust Runtime `(X + 0.0, X * 0.5)` | Safe Rust `const` CTFE | RFC 3514 Status |
| :--- | :---: | :---: | :---: | :---: | :--- |
| 1. Pure `rustc -C opt-level=3` | No | `0x1f80` | `("0x00400000", "0x00200000")` | `("0x00400000", "0x00200000")` | Preserved |
| 2. Executable linked with `gcc -ffast-math` / `-Ofast` | **Yes** (`.init_array`) | **`0x9fc0`** (`DAZ\|FTZ`) | **`("0x00000000", "0x00000000")`** | `("0x00400000", "0x00200000")` | **BROKEN before `main()`** |
| 3. Shared `.so` built with `gcc -shared -fPIC -ffast-math` | No (`%{!shared:...}`) | `0x1f80` | `("0x00400000", "0x00200000")` | `("0x00400000", "0x00200000")` | Preserved (GCC $\ge 13$ PR55522 guard) |
| 4. Shared `.so` built with `gcc -shared -fPIC -mdaz-ftz` | **Yes** (bypasses `!shared`) | **`0x9fc0`** (`DAZ\|FTZ`) | **`("0x00000000", "0x00000000")`** | `("0x00400000", "0x00200000")` | **BROKEN by `.so` load!** |

Because `-mdaz-ftz` precedes `;` outside `%{!shared:...}` in GCC 15.2.0's spec string, merely loading an uncalled `-mdaz-ftz` C shared library (or linking a hybrid binary with `-ffast-math`) violates Rust RFC 3514's default-FP-environment assumption process-wide before `main()` starts (`crtfastmath_init_array_breaks_rfc3514_subnormal`). Post-link `.init_array` section auditing (Section 2.1 of `production-rust-ffi-inline-asm-workloads-and-adversarial-bypass-taxonomy`) plus startup/FFI `stmxcsr & 0xffc0 == 0x1f80` checks are therefore mandatory when linking untrusted C toolchains.

#### 2.3 Bit-Exact Corner Matrix: `f32::{min, max, minimum, maximum, mul_add}` vs. `vminss`/`vmaxss`/`vfmadd213ss`

Measured identically across `rustc 1.99.1` and `1.102.0-nightly` (`-C opt-level=3`; `minimum`/`maximum` on `1.102.0-nightly`):

| Input Pair `(a, b)` | `f32::min` (`minNum`) | `f32::max` (`maxNum`) | `f32::minimum` (IEEE-2019) | `f32::maximum` (IEEE-2019) | x86 `vminss a, b` (`flags`) | x86 `vmaxss a, b` (`flags`) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `(-0.0, +0.0)` (`0x80000000, 0x00000000`) | **`0x00000000`** (`+0.0`) | `0x00000000` (`+0.0`) | `0x80000000` (`-0.0`) | `0x00000000` (`+0.0`) | `0x00000000` (`0x00`) | `0x00000000` (`0x00`) |
| `(+0.0, -0.0)` (`0x00000000, 0x80000000`) | `0x80000000` (`-0.0`) | **`0x80000000`** (`-0.0`) | `0x80000000` (`-0.0`) | `0x00000000` (`+0.0`) | `0x80000000` (`0x00`) | `0x80000000` (`0x00`) |
| `(qNaN1, 1.0)` (`0x7fc00001, 0x3f800000`) | `0x3f800000` | `0x3f800000` | `0x7fc00001` | `0x7fc00001` | `0x3f800000` (**`0x01` `IE`!**) | `0x3f800000` (**`0x01` `IE`!**) |
| `(1.0, qNaN1)` (`0x3f800000, 0x7fc00001`) | `0x3f800000` | `0x3f800000` | `0x7fc00001` | `0x7fc00001` | **`0x7fc00001`** (**`0x01` `IE`!**) | **`0x7fc00001`** (**`0x01` `IE`!**) |
| `(qNaN1, qNaN2)` (`0x7fc00001, 0x7fc00002`) | `0x7fc00001` | `0x7fc00001` | `0x7fc00001` | `0x7fc00001` | **`0x7fc00002`** (`0x01`) | **`0x7fc00002`** (`0x01`) |
| `(sNaN1, 1.0)` (`0x7f800001, 0x3f800000`) | `0x3f800000` | `0x3f800000` | **`0x7f800001`** (unquieted) | **`0x7f800001`** (unquieted) | `0x3f800000` (`0x01`) | `0x3f800000` (`0x01`) |
| `(1.0, sNaN1)` (`0x3f800000, 0x7f800001`) | `0x3f800000` | `0x3f800000` | **`0x7f800001`** (unquieted) | **`0x7f800001`** (unquieted) | **`0x7f800001`** (`0x01`) | **`0x7f800001`** (`0x01`) |

Four translation-validation traps stand out:
1. **Raw `vminss`/`vmaxss` is equivalent to *neither* `f32::min`/`max` nor `f32::minimum`/`maximum`:** `vminss dst, a, b` evaluates `a < b ? a : b`, returning `b` whenever unordered or equal (`(-0.0, +0.0) -> +0.0`, `(1.0, qNaN) -> qNaN` vs. `(qNaN, 1.0) -> 1.0`) and never quieting `sNaN` in `b`.
2. **Rust `f32::min`/`max` is non-commutative on signed zero at `-C opt-level=3`:** Because IEEE 754-2008 `minNum`/`maxNum` leaves signed-zero tie-breaking unspecified, LLVM lowers `f32::min` to `cmpunordss %xmm1, %xmm2` + `minss %xmm1, %xmm0` + blend (`rust_min` in `probe_redzone_mxcsr_and_fastmath_results.json`), inheriting `minss`'s second-operand bias (`min(-0.0, +0.0) == +0.0`, `max(+0.0, -0.0) == -0.0`), whereas `f32::minimum`/`maximum` inserts `vandps`/`vorps` to enforce `-0.0 < +0.0` (while propagating `sNaN` `0x7f800001` unchanged via bitwise `vblendvps`, permitted by RFC 3514's unchanged-sNaN clause when an input is `sNaN`).
3. **`vminss`/`vmaxss` sets `MXCSR.IE` (`0x01`) on *quiet* NaNs**, unlike `vaddss`/`vmulss`/`vfmadd213ss` (`hw_flags = 0x00` on `(qNaN1, 1.0, qNaN2)`).
4. **Single-rounding FMA (`f32::mul_add` / `vfmadd213ss` / baseline `fmaf@GOTPCREL`) vs. `a * b + c`:** On `(1 + 2^-23, 1 - 2^-23, -1.0)` (`0x3f800001, 0x3f7ffffe, 0xbf800000`), `mul_add` and `vfmadd213ss` both return exact `-2^-46` (`0xa8800000`, `hw_flags = 0x00`) while `a * b + c` returns `+0.0` (`0x00000000`). On `(0x3f800001, 0x3f800002, 0x337ffffe)`, single-rounding FMA rounds up to `0x3f800004` (`PE = 0x20`) while `a * b + c` double-rounds down to `0x3f800003`.

---

### 3. Non-Naked Constant-Time Wrapper Leaks and the Intel DOIT Boundary

`Basis: documentation + source + execution` ([`support/probe_ct_wrappers_fault_tables_and_ifunc.py`](support/probe_ct_wrappers_fault_tables_and_ifunc.py), [`support/probe_ct_wrappers_fault_tables_and_ifunc_results.json`](support/probe_ct_wrappers_fault_tables_and_ifunc_results.json))

#### 3.1 Four-Stage Lowering of `core::hint::black_box` and Induced Wrapper Leaks

Dumping every compiler IR stage across `rustc 1.99.1` and `1.102.0-nightly` (`-C opt-level=3`) resolves how `core::hint::black_box` actually lowers:
1. **`Runtime(PostCleanup)` MIR (`-Zdump-mir=runtime-post-cleanup`):** `_0 = std::hint::black_box::<u8>(move _2) -> [return: bb1, unwind continue];` — an ordinary `TerminatorKind::Call`, **not** `TerminatorKind::InlineAsm`.
2. **Optimized MIR (`--emit=mir`):** `_0 = std::intrinsics::black_box::<u8>(move _1) -> [return: bb1, unwind unreachable];` — still an intrinsic `Call` (`sym::black_box`).
3. **LLVM IR (`rustc_codegen_llvm/src/intrinsic.rs:88-120`, `Builder::black_box`):** `Builder::black_box(result: PlaceRef)` binds `result_val_span = [result.val.llval]`—the **pointer to the stack `alloca` backing `PlaceRef`**—and emits `call void asm sideeffect "", "r,~{memory}"(ptr nonnull %_0)` (`volatile = true`, `alignstack = false`; `"~{memory}"` for ZSTs).
4. **x86-64 Machine Code:** Passing `ptr nonnull %_0` to a `"~{memory}"` inline-asm call **defeats SROA/register promotion even for a 1-byte `u8` or `bool`**: `inspect_black_box_u8` compiles to `movb %dil, -1(%rsp); leaq -1(%rsp), %rax; movzbl -1(%rsp), %eax; retq`. Live execution (`detect_stack_residue_blackbox`) confirms the secret byte (`0x5a`) remains sitting in un-erased caller stack memory at `[caller_rsp - 9]` after return!

Comparing five constant-time wrapper idioms (`1.99.1` and `1.102.0-nightly` identical):

| Wrapper Idiom (`-C opt-level=3`) | Conditional Jumps Outside `asm!` | Stack / Red-Zone Secret Spill? | Leakage Mechanism |
| :--- | :---: | :---: | :--- |
| `ct_wrapper_plain_and`: `(c1 && c2) as u64` $\to$ `asm!("cmovne")` | **`0`** (`andl %esi, %edi`) | No | Pure register ALU + `cmovneq` |
| `ct_wrapper_blackbox_and_leak`: `(black_box(c1) && black_box(c2))` $\to$ `asm!("cmovne")` | **`1` (`jne .LBB8_1`!)** | **Yes** (`-1(%rsp)`, `-2(%rsp)`) | `black_box(c2)` has `sideeffect` in LLVM IR, forbidding speculative execution when `c1 == false` and **forcing a secret-dependent branch**! |
| `ct_wrapper_volatile_choice`: `subtle`-style `read_volatile(&c.0)` $\to$ `asm!("cmovne")` | `0` | **Yes** (`-1(%rsp)` in helper) | `read_volatile` forces stack materialization of `Choice(u8)` |
| `loop_rust_select_cmov_converted`: innermost loop with Rust `if c != 0 { heavy } else { light }` | **Secret `je .LBB13_4`** (+ loop exit) | No (but **skips memory load**!) | `X86CmovConversion.cpp:15-32` rewrites profitable loop `CMOV` into `cmpb $0, (%rdi,%r11); je` + conditional `(%rdx)` vs. `(%r8)` loads |
| `loop_asm_cmov_preserved` / `#[unsafe(naked)] ct_select_naked` (`naked_asm!`) | **`0` secret jumps** | **No** (`naked_redzone_secret_leaked = false`) | `asm!` `cmoveq` is opaque to `X86CmovConversion`; `naked_asm!` eliminates all compiler prologue/epilogue spills |

**Verification Rule:** Proving 2-safety constant-time (`LeakTrace` equivalence) solely on an inner `asm!` template inside a non-naked Rust wrapper is **unsound**; the 2-safety audit must cover the **entire compiled wrapper function** (or require `#[unsafe(naked)]` entry points with explicit register/stack zeroization).

#### 3.2 Intel DOIT (`IA32_UARCH_MISC_CTL[DOITM]`) and `MCDT_NO` Hardware Opcode Partition

Per Intel's *Data Operand Independent Timing ISA Guidance* (`ID 768873`, `2026-11-13`) and *Documented DOIT Instructions* (`ID 759656`, `2026-02-23`, `594` Table-1 mnemonics):
- **Hardware Enabling:** On Ice Lake / Gracemont and newer (`IA32_ARCH_CAPABILITIES[12] == 1`, MSR `0x10A`), constant-time execution is **not** guaranteed architecturally unless the OS sets `IA32_UARCH_MISC_CTL[0]` (`DOITM = 1`, MSR `0x1B01`; always forced on inside SGX enclaves). Additionally, on CPUs where `MCDT_NO` (`CPUID.(EAX=07H,ECX=02H):EDX[5]`) is `0`, `MXCSR` configuration-dependent timing (`MCDT`) can delay certain vector instructions by 1 cycle based on operand values unless `MXCSR` is properly configured/serialized.
- **Included in Intel DOIT Table 1 (`594` mnemonics):** Integer ALU/shifts (`ADD`, `ADC`, `ADCX`, `ADOX`, `SUB`, `XOR`, `CMOVcc`, `MUL`, `IMUL`, `MULX`, `SHLX`, `SHRX`, `SARX`, `RORX`), byte/dword shuffles (`PSHUFB`, `VPSHUFB`, `VPERMD`, `VPBLENDVB`), carryless/AES/GFNI crypto (`AESENC`/`VAESENC`, `PCLMULQDQ`/`VPCLMULQDQ`, `VGF2P8AFFINEQB`), and integer SIMD multiplies (`PMULLD`/`VPMULLD`, `VPMULLQ`, `PMULUDQ`/`VPMULUDQ`, `PMULHRSW`/`VPMULHRSW`).
- **Excluded from Intel DOIT Table 1 (Forbidden in Verified CT Kernels):**
  1. **SIMD Gather/Scatter & Masked Memory Ops:** `VGATHERDPS`/`QPS`/`DPD`/`QPD`, `VPGATHERDD`/`QD`/`DQ`/`QQ`, `VSCATTER*`, `VPSCATTER*` (completely absent from Table 1, and memory-accessing mask registers leak masked addresses even for instructions on Table 1).
  2. **Omitted Bit-Count & Byte-Permute Instructions:** `VPERMB` (AVX-512 VBMI), `POPCNT`, `LZCNT`, `TZCNT`, and integer `DIV`/`IDIV` are absent from Table 1.
  3. **All IEEE-754 Floating-Point Instructions:** `VADDPS`/`SS`, `VMULPS`/`SS`, `VDIVPS`/`SS`, `VSQRTPS`, and `VFMADD*` are completely absent from Table 1 (exhibiting subnormal/exception timing variations unless flushed, which in turn breaks RFC 3514).

---

### 4. Sideband ELF Control-Flow Overlays (`usercopy` / `__ex_table`, `rseq`, and `target_clones` `IFUNC`s)

`Basis: source + execution + derived` ([`support/probe_ct_wrappers_fault_tables_and_ifunc.py`](support/probe_ct_wrappers_fault_tables_and_ifunc.py), [`support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean`](support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean))

#### 4.1 Three Classes of Sideband ELF Control-Flow Overlays and Live `usercopy` Partial Writes

Machine-code verifiers that extract control-flow graphs solely from branch/call instructions miss three production ELF metadata overlays that dynamically rewrite `RIP` or `.text`:

| Overlay Mechanism | Upstream Source & Section Encoding | Trigger Event | Memory Prefix Effect Prior to Redirect |
| :--- | :--- | :--- | :--- |
| **1. Static Keys (`asm_goto` + `__jump_table`)** | Linux `arch/x86/include/asm/jump_label.h:15-38`, `.pushsection __jump_table,"aw"` `(code - ., target - ., key - .)` | Stop-machine / text-poke patches 5-byte `NOP5` $\leftrightarrow$ `jmp target` | Zero mid-instruction partial writes (instruction boundary branch) |
| **2. Synchronous Fault Fixups (`__ex_table` & Starnix `*_end`)** | Linux `arch/x86/include/asm/asm.h:138-144` (`.pushsection "__ex_table"` 12-byte `(from - ., to - ., type)`); Starnix `hermetic_copy.S:7-18, 172` + `hermetic_copy_error.S:11-13` | Synchronous `#PF` / `#GP` / `SIGSEGV` when `RIP` $\in [\text{start}, \text{end})$ | **Mutates `dst[0..valid]` before faulting on `src[valid]`!** (`atomic_noop_fault_model_unsound_for_usercopy`) |
| **3. Restartable Sequences (`struct rseq_cs`)** | Linux `include/uapi/linux/rseq.h:57-66` (`start_ip`, `post_commit_offset`, `abort_ip`) | Asynchronous preemption, signal delivery, or CPU migration in `[start_ip, commit_ip)` | **Zero shared-memory writes before `commit_ip`** (`rseq_pre_commit_abort_preserves_mem`) |

**Live Linux `x86_64` verification (`probe_4_usercopy_fault_tables_and_ifunc`):** Allocating two contiguous 4096-byte pages (`page0` `PROT_READ | PROT_WRITE`, `page1` `PROT_NONE`) and copying `req = 32` bytes starting at `page0 + 4096 - 19` (`19` mapped bytes `[1..=19]` followed by `13` unmapped bytes):
- **Starnix half-open range (`[starnix_usercopy_start, starnix_usercopy_end) -> starnix_usercopy_fault`):** Byte loop faults at exact guard-page offset `0` (`si_addr == page1`), `SA_SIGINFO` redirects `uc_mcontext.gregs[REG_RIP]` to `starnix_usercopy_fault`, returning `rem = 13` with `dst1[0..19] == [1..=19]` (`prefix_written_exact = true`) and `dst1[19..32] == 0xaa` (`tail_untouched = true`).
- **Linux `__ex_table` relative descriptor on `rep movsb` (`extable_rep_usercopy`):** Hardware `rep movsb` faults mid-instruction after architecturally committing `19` byte stores and decrementing `%rcx` from `32` to `13`; scanning `[__start___ex_table, __stop___ex_table)` matches `&e->insn + e->insn == rip`, redirects `REG_RIP` to `&e->fixup + e->fixup` (`movq %rcx, %rax; retq`), and returns `rem = 13` with `dst2[0..19]` written and `dst2[19..32]` untouched (`fault_overlay_usercopy_partial_write_exact`).

#### 4.2 `gcc 15.2.0` `target_clones` `STT_GNU_IFUNC` + `R_X86_64_IRELATIVE` + `xgetbv` OS-XSAVE Gating

Compiling `__attribute__((target_clones("default", "avx2", "avx512f"))) uint32_t sum_u32_clones(...)` with `gcc 15.2.0 -O2` emits three `LOCAL FUNC` clones (`.default`, `.avx2`, `.avx512f`), a `WEAK FUNC` `sum_u32_clones.resolver` aliased by `GLOBAL IFUNC` `sum_u32_clones` at `0x2be0`, and a `.rela.plt` `R_X86_64_IRELATIVE` relocation (`0x5010 -> 0x2be0`). Disassembly confirms two critical soundness properties:
1. `sum_u32_clones.resolver` calls statically linked `libgcc` `__cpu_indicator_init` via direct relative `call 1520` and reads `__cpu_model.__cpu_features[0]` via RIP-relative `lea 0x24a0(%rip), %rax; mov 0xc(%rax), %eax` (testing `0x80` in `%ah` for `AVX512F` and `0x04` in `%ah` for `AVX2`)—avoiding external PLT calls that `SIGSEGV` during `ld.so` relocation (`gotpcrelx-tlsdesc-linker-relaxations-ifunc-ordering-and-linksem-slack`).
2. Inside `__cpu_indicator_init` (`0x1c10..0x1c35`), `libgcc` does **not** trust `CPUID` alone: after checking `CPUID.01H:ECX.OSXSAVE`, it executes `xor %ecx, %ecx; xgetbv` (`0f 01 d0`) and checks `not %edx; and $0x6, %dl; je ...` (`XCR0[2:1] == 0b11`, confirming OS kernel support for XMM+YMM state saving) before advertising AVX/AVX2/AVX-512 (and `0x60000` for AMX `XTILE`). Any verified `IFUNC` or `#[target_feature]` dispatcher on x86-64 must enforce the conjunction `CPUID_feature ∧ OSXSAVE ∧ (xgetbv(0) & required_xcr0_mask) == required_xcr0_mask`.

---

### 5. Upward-Compatible Weak-Memory & Tear-Free Seqlock Trace Algebra (`MemTraceEvent`)

`Basis: normative + execution + derived` ([`support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean`](support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean), kernel-checked in Lean `v4.34.1`)

#### 5.1 Why `asm!` `READ_ONCE` (`SingleCopyAtomic`) Resolves the Rust/MiniRust Seqlock Dilemma

In MiniRust (`minirust@063d7841`, `spec/mem/concurrent.md:161-176`) and `lean-miri`, every ordinary Rust reference/pointer read lowers to `Atomicity::None` (`.plain`). As proved in `plain_seqlock_reader_triggers_data_race_ub`, an optimistic seqlock reader using `.plain` loads races with a concurrent writer's payload store and triggers immediate **Undefined Behavior even when the reader subsequently observes `seq1 != seq2` and discards the torn values**. Conversely, production kernels (Linux `READ_ONCE` via volatile/inline-asm single-instruction loads, Starnix `atomic_load_*`, high-frequency telemetry rings) rely on tear-free single-instruction `mov` (`asm!("mov {out}, [{p}]", options(readonly, nostack, preserves_flags))`) or `AtomicU64::load(Ordering::Relaxed)` to read multi-word payloads without locking.

Enriching `OpenComponent` (`reentrant-ffi-mixed-mir-isa-call-stacks-tree-borrows-and-oracle-composition`) to `OpenMemComponent` emitting `MemTraceEvent`:

```lean
inductive AccessOrder where
  | plain | singleCopyAtomic | acquire | release | acqRel | seqCst

inductive MemTraceEvent where
  | load (ord : AccessOrder) (addr : Nat) (val : Nat)
  | store (ord : AccessOrder) (addr : Nat) (val : Nat)
  | rmw (ord : AccessOrder) (addr : Nat) (oldVal newVal : Nat)
  | fence (ord : AccessOrder)
```

cleanly bridges all three verification regimes with zero architectural rework:
1. **Race-Freedom Across Overlapping Torn Retries (`non_plain_trace_never_data_races`):** Because `HasPlainDataRace` triggers if and only if at least one racing unordered access has `ord = .plain`, replacing `.plain` payload reads with `.singleCopyAtomic` (proven at the ISA level by verifying aligned single-instruction `mov` width $\le 8\text{ B}$ on x86-64/AArch64) eliminates `DataRaceUB` across *all* concurrent writer interleavings, even when `srcEpoch j₁ ≠ srcEpoch j₂` yields a cross-word torn tuple during an aborted attempt. (At the Rust type boundary, the reader must hold those loaded words in `u64`/`MaybeUninit<T>` bytes and construct typed `T` **only after** `seq1 == seq2` succeeds so torn intermediate bit patterns never violate validity invariants such as `bool` or `NonNull`.)
2. **Multi-Word Snapshot Coherence (`seqlock_single_copy_atomic_reader_sound`):** When writer epoch $e$ brackets `.singleCopyAtomic` payload stores between `store .release seq (2e - 1)` and `store .release seq (2e)`, and the reader executes `s1 := load .acquire seq` $\to$ `w_j := load .singleCopyAtomic (payload + j)` $\to$ `fence .acquire` (free on x86-TSO; `dmb ishld` on AArch64) $\to$ `s2 := load .acquire seq`:
   - Release-Acquire synchronization from `s1 = 2e` bounds every subsequent read below: $e \le \text{srcEpoch}(j)$;
   - Acquire ordering before `s2 = 2e` bounds every preceding read above: $\text{srcEpoch}(j) \le e$;
   - Hence $s_1 = s_2 = 2e \implies \forall j,\; \text{srcEpoch}(j) = e \land w_j = \text{epochSnap}(e, j)$.
3. **Zero-Overhead Sequential Collapse & Simulation Preservation (`sequential_schedule_collapses_mem_trace_to_state` & `open_mem_sim_preserves_mem_trace`):** Under any single-threaded schedule, `runSeqMemTrace evs m = runSeqMemTrace (evs.map eraseOrderToPlain) m` (proved in Lean `v4.34.1` with **zero axioms**), while `OpenMemSim` preserves the exact `List MemTraceEvent` stream across reentrant MIR-ISA refinement.

## Boundaries

- **Other architectures' red zones and FP CSRs (`not examined` empirically in live probes):** Live execution probes ran on `x86_64-unknown-linux-gnu`. While `StepwiseNostackTrace` parameterizes `redZoneBytes` generally (`128` vs. `0`), `aarch64-apple-darwin` (`128 B` ABI red zone, currently unused by `rustc` due to `frame-pointer: non-leaf` per `rust-stack-discipline-probes-red-zones-and-overflow`) and `aarch64`/`riscv64` `FPCR`/`FPSR`/`fcsr` runtime behavior (covered in `ieee754-dynamic-rounding-modes-sticky-exception-csrs-and-stateful-floating-point-verification`) were not re-executed here.
- **Unaligned cross-cache-line `asm!` loads (`known not to apply` to `SingleCopyAtomic`):** Theorem `seqlock_single_copy_atomic_reader_sound` requires each `.singleCopyAtomic` access to satisfy hardware single-copy atomicity (naturally aligned $1/2/4/8$-byte `mov` on x86-64 and ARMv8.0, or `16`-byte `vmovdqa` with AVX on Intel/AMD per SDM Vol. 3A §9.1.1 / ARMv8.4 LSE2). Unaligned `mov` crossing a 64-byte cache line can tear intra-word on hardware and does **not** instantiate `.singleCopyAtomic`.
- **Microarchitectural power/frequency/speculative channels under `DOITM = 1` (`known not to apply`):** As explicitly documented in Intel `ID 768873`, `IA32_UARCH_MISC_CTL[DOITM] = 1` guarantees cycle-count invariance of data values for the `594` Table-1 mnemonics, but does **not** prevent cache/TLB address leakage, Spectre/PHT/STL speculative leakage, or RAPL/frequency-throttling power side channels.
- **`rustc` explicit `MXCSR` clobber syntax (`unsupported`):** Neither `rustc 1.99.1` nor `1.102.0-nightly` supports `out("mxcsr") _` in `asm!`; omitting `options(preserves_flags)` is currently the sole mechanism in Rust `asm!` to legally mutate `MXCSR[5:0]`.
- **`f32::minimum` and `f32::maximum` on stable `rustc 1.99.1` (`unsupported`):** `#![feature(float_minimum_maximum)]` remains unstable in `1.99.1` and was measured on `1.102.0-nightly`.

## Evidence

### 1. Pinned Upstream Source Citations (`2026-11-21`)

- **`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:** `src/inline-assembly.md:1229-1238` (`r[asm.options.supported-options-nostack]`), `L1368-1373` (`r[asm.rules.preserved-registers]` requiring `MXCSR` exception-flag restoration under `preserves_flags`), `L1397-1404` (`DF` and x87 rules).
- **`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`) & `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`):** `compiler/rustc_codegen_llvm/src/asm.rs:258-270` (`~{dirflag},~{fpsr},~{flags}`), `L334` (`alignstack = !options.contains(NOSTACK)`), `compiler/rustc_codegen_llvm/src/intrinsic.rs:88-120` (`Builder::black_box` passing `PlaceRef` pointer to `"r,~{memory}"` inline asm), `library/core/src/hint.rs:487-492`.
- **`llvm/llvm-project@0a5579eb649d3634a9c30ac873300cc2944fa070` (`23.1.5`) & `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`23.1.1`):** `llvm/lib/CodeGen/SelectionDAG/SelectionDAGBuilder.cpp:10308-10309`, `llvm/lib/CodeGen/MachineInstr.cpp:914-921`, `llvm/lib/CodeGen/FinalizeISel.cpp:61-62`, `llvm/lib/Target/X86/X86FrameLowering.cpp:1486-1494, 1780-1793`, `llvm/lib/Target/X86/X86ISelLowering.cpp:64423-64424`, `llvm/lib/Target/X86/X86InstrSSE.td:2658-2758, 3282-3298`, `llvm/lib/Target/X86/X86CmovConversion.cpp:15-95`.
- **`gcc-mirror/gcc@5115c7e447fc07457443df874bf57840e8316d5f` (`15.2.0`):** `libgcc/config/i386/crtfastmath.c:82-98` (`set_fast_math` `.init_array` constructor) and `gcc -dumpspecs` `ENDFILE_SPEC`.
- **`torvalds/linux@5f22fb20497f4983094131f00a734362300d22d2` & `fuchsia.googlesource.com/fuchsia@fd31be1516bd2906c5b46be6c3ca3aa1adb162c0`:** `arch/x86/include/asm/asm.h:138-144` (`_ASM_EXTABLE_TYPE`), `include/uapi/linux/rseq.h:57-130` (`struct rseq_cs`, `struct rseq`), `src/starnix/lib/usercopy/arch/x64/{hermetic_copy.S:7-173, hermetic_copy_error.S:10-21}`.
- **`minirust/minirust@063d784186d3252bee242217f218223205c0b568` & Intel DOIT Guidance:** `spec/mem/concurrent.md:161-176`; Intel Docs `768873` (`2026-11-13`) and `759656` (`2026-02-23`, `594` documented DOIT mnemonics).

### 2. Preserved Package Support Artifacts (`support/`)

1. [`support/probe_redzone_mxcsr_and_fastmath.py`](support/probe_redzone_mxcsr_and_fastmath.py) and [`support/probe_redzone_mxcsr_and_fastmath_results.json`](support/probe_redzone_mxcsr_and_fastmath_results.json): Reproduces all Seam 1 & Seam 2 compiler disassemblies, red-zone safe-local overwrites, `MXCSR` sticky transitions, `crtfastmath.o` `.init_array` poisoning topologies, and `f32` corner tables across `rustc 1.99.1`, `rustc 1.102.0-nightly`, and `gcc 15.2.0`.
2. [`support/probe_ct_wrappers_fault_tables_and_ifunc.py`](support/probe_ct_wrappers_fault_tables_and_ifunc.py) and [`support/probe_ct_wrappers_fault_tables_and_ifunc_results.json`](support/probe_ct_wrappers_fault_tables_and_ifunc_results.json): Reproduces the 4-stage `black_box` MIR/IR/ASM trace, live red-zone secret residue check, `black_box` + `&&` branch induction, `X86CmovConversion` loop rewrite, dual Starnix/`__ex_table` `PROT_NONE` `usercopy` fault recovery, and `target_clones` `IFUNC` + `xgetbv` disassembly.
3. [`support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean`](support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean): Standalone `Init`-only Lean `v4.34.1` mechanization verifying all 12 theorems (`naive_endpoint_nostack_corrupts_redzone_local`, `stepwise_nostack_preserves_redzone_and_frame`, `no_redzone_relaxes_local_footprint`, `vaddps_inexact_violates_normative_preserves_flags_but_satisfies_split`, `crtfastmath_init_array_breaks_rfc3514_subnormal`, `atomic_noop_fault_model_unsound_for_usercopy`, `fault_overlay_usercopy_partial_write_exact`, `rseq_pre_commit_abort_preserves_mem`, `plain_seqlock_reader_triggers_data_race_ub`, `seqlock_single_copy_atomic_reader_sound`, `sequential_schedule_collapses_mem_trace_to_state`, and `open_mem_sim_preserves_mem_trace`) with zero `sorryAx` and zero warnings.

## Revalidation

Run the two self-contained empirical probe suites (which build inside `tempfile.TemporaryDirectory()` and leave `/tmp` clean) and re-check the Lean `v4.34.1` proofs from the package directory:

```bash
python3 -B support/probe_redzone_mxcsr_and_fastmath.py /tmp/reval_seam12.json
python3 -B support/probe_ct_wrappers_fault_tables_and_ifunc.py /tmp/reval_seam34.json
lean -DElab.async=false -Ddebug.skipKernelTC=false support/NostackMxcsrFaultOverlayAndSeqlockTraces.lean
rm -f /tmp/reval_seam12.json /tmp/reval_seam34.json
```

Key discriminating assertions to check after a `rustc`, LLVM, GCC, or Lean upgrade:
1. In `reval_seam12.json`, check `seam1_nostack_redzone.<tc>.default_redzone.runtime.push_pop[1] == "0xdeadbeefcafebabe"` (confirming leaf red-zone allocation across `options(nostack)`), `rustc_mxcsr_clobber_register.<tc>.returncode != 0` (unless `rustc` adds an explicit `mxcsr` clobber register), and `crtfastmath_ffi_poisoning.3_shared_so_has_set_fast_math_sym == false` vs. `4_shared_so_has_set_fast_math_sym == true`.
2. In `reval_seam34.json`, check `blackbox_redzone_secret_leaked_at_rsp_minus_9 == true` (unless `Builder::black_box` stops passing `PlaceRef` addresses for register-sized scalars), `ct_wrapper_blackbox_and_leak.cond_jumps` non-empty, and `starnix_range.rem == 13` / `linux_ex_table.rem == 13` with `prefix_written_exact == true`.
3. In Lean `v4.34.1`, verify exit code `0` and confirm `#print axioms` lists no `sorryAx` or `Lean.ofReduceBool`.
