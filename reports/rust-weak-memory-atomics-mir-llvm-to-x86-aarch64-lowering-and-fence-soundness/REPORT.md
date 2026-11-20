# Rust Atomic and Fence Lowering from MIR through LLVM IR to x86-64, i686, AArch64 and s390x: Measured Tables, Source Mechanisms, and Kernel-Checked Litmus Soundness with Four Sharpness Counterexamples

## Summary

> **Scope of the formal part.** The Lean development in `support/RustAtomicLoweringSoundness.lean`
> proves (a) facts about finite lowering *tables*, quantified over every operation, ordering and
> configuration, and (b) facts about finite candidate executions of four straight-line *litmus
> programs* compiled through those tables, checked against transcribed fragments of published
> axiomatic models. It is not a compilation-correctness proof for arbitrary programs. Every
> statement about real hardware is a modelling claim (`derived`), argued from the cited models.

A replacement code generator for `core::sync::atomic` has to reproduce one small, sharp table. This
report measures that table on real `rustc`, locates the LLVM source lines that produce each
configuration-dependent cell, and checks in Lean which cells are load-bearing.

1. **MIR to LLVM IR is one-to-one and loses nothing.** `core::sync::atomic` dispatches a run-time
   `Ordering` to intrinsics whose ordering is a const generic; `rustc_codegen_ssa` turns each
   intrinsic into exactly one of `load atomic`, `store atomic`, `atomicrmw`, `cmpxchg [weak]`,
   `fence`, or `fence syncscope("singlethread")` with the same ordering. At `-C opt-level=0` the
   ordering is still a run-time `i8` argument (`movl $4, %edx` for `SeqCst`) and the callee
   contains all three `load atomic` variants.
2. **Instruction selection differs between configurations in very few cells.** Across 13 measured
   configurations (468 function bodies): `-C no-redzone=yes` changes 1 of 36 functions
   (`lock orl $0, -64(%rsp)` becomes `lock orl $0, (%rsp)`); `+rcpc` changes 2 (`load(Acquire)`
   becomes `ldapr`; `load(SeqCst)` stays `ldar`); `+rcpc3` changes 0; AArch64 outlining changes
   16 (every read-modify-write and compare-exchange, no load, store or fence); `i686` without SSE
   changes 3 (`mfence` becomes `lock orl $0, (%esp)`, `movq`/`movlps` become `fildll`/`fistpll`).
   `rustc` 1.99.1, 1.100.0 and 1.102.0-nightly emit identical IR and assembly for all 36 functions
   on `x86_64`, and a reconstruction of the probe compiled with 1.98.0-nightly (LLVM 22.1.6)
   reproduces 324 of 324 assembly bodies of the nine configurations it shares with 1.99.1.
3. **The `Atomic<T>` change shows up in MIR as a rename.** `AtomicU32` is a struct through 1.95.0
   and an alias of the generic struct `Atomic<u32>` from 1.96.0 (commit
   `fa66fef1d1c78d2ecf2ba09a68e25e1e7ab154f7`). MIR call lines change from `AtomicU32::load` to
   `Atomic::<u32>::load` and the recorded MIR diffs contain nothing else. Every instruction-level
   measurement here is from a toolchain after the change, so its effect on LLVM IR and assembly
   was not measured.
4. **`compiler_fence` emits no instruction but changes what the optimizer may do.** On LLVM 22.1.6,
   `IMPORTANT = v; compiler_fence(Release); READY.store(1, Relaxed); IMPORTANT = w` keeps all three
   stores, and the same code without the fence loses the first store to dead-store elimination.
   With a `&mut` (noalias) datum the two fences change nothing: the reload is forwarded across
   them. A dead `Relaxed` load and two adjacent `Relaxed` stores were not removed or merged in
   any measured configuration.
5. **Kernel-checked results (Lean v4.34.1, at most `propext`).** For every valid pair of accesses
   and every configuration, each same-thread order that RC11 requires is kept by the selected
   instructions. For store buffering (two variants) and message passing, the weak outcome is
   forbidden by the RC11 fragment and by the compiled program on all nine store-buffer
   configurations and all four AArch64 profiles; for IRIW, by the RC11 fragment and on the four
   AArch64 profiles. Four mutants show the table is sharp:
   **CE1** `load(SeqCst)` as `ldapr` allows store buffering (and only that: message passing and
   IRIW stay forbidden); **CE2** `lock orl $0, -64(%rsp)` without a red zone touches memory the
   frame does not own; **CE3** dropping the ordering edges of a compiler fence lets a scheduler
   or a dead-store eliminator expose a stale datum to a signal handler; **CE4** dropping the
   lock, `mfence` or `bcr 15,%r0` from `SeqCst` stores and fences allows store buffering.
6. **The Lean tables are tested against the compiler.** A script reduces measured assembly to the
   token vocabulary the Lean file prints and compares: 754 of 754 cells match (384 preserved,
   370 live), 132 of 132 canary and mutant-exclusion checks pass, and a planted table fault is
   detected.

## Applicability

**What the measurements cover.** `rustc` 1.99.1 (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`,
LLVM 23.1.1) on `x86_64-unknown-linux-gnu` (`-C opt-level=3`, the same with `-C no-redzone=yes`,
and `-C opt-level=0`), `aarch64-unknown-linux-gnu` (default `+v8a,+outline-atomics`;
`-outline-atomics`; `+lse`; `+lse,+rcpc`; `+lse,+rcpc,+rcpc3`) and `i686-unknown-linux-gnu`
(default `pentium4`; `-sse2,-sse`); `rustc` 1.100.0 (`0ef1bc386059596dada8fb65b50425aab2ea637a`,
LLVM 23.1.5) and 1.102.0-nightly (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM 23.1.5) on
`x86_64` at `-C opt-level=3`; and 1.102.0-nightly on `s390x-unknown-linux-gnu`. Each configuration
compiles the same 36 functions (32 single-operation wrappers over `AtomicU8`/`AtomicU32`/`AtomicU64`,
`fence` and `compiler_fence`, and 4 optimization canaries).

**What the live probe adds.** `rustc` 1.98.0-nightly (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`,
LLVM 22.1.6) recompiles a reconstruction of those 36 functions plus 8 more on eleven
configurations (the `x86_64`, AArch64 and `i686` ones above, plus `i686` with `-sse2` only). It
could not compile for `s390x` (no `core` for that target was installed), so `s390x` rests on the
1.102.0-nightly measurement alone. The dead-store canary of finding 5.2 exists only in the live
probe and is therefore established for LLVM 22.1.6 only.

**How the subjects relate.** The three `rustc` releases and the live toolchain are compared with one
another. `llvm/llvm-project@6dfe1677ab8dffbc6ec13d53a1e0215d75147689` (`llvmorg-23.1.1`) supplies
the cited lowering source; the twelve cited LLVM files are byte-identical to the copies in
`rust-lang/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, which is the `src/llvm-project`
submodule of 1.99.1. `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5` is the
submodule of the live toolchain and is cited only where LLVM 22 and 23 differ.
`rust-lang/rust@59807616e1fa2540724bfbac14d7976d7e4a3860` (1.95.0) and
`@ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96` (1.96.0) bracket the `Atomic<T>` change.
`herd/herdtools7@1ae595498c7af7d9d2f00e29aea328b36663104c` supplies the axiomatic models the Lean
file transcribes; `torvalds/linux@adc218676eef25575469234709c2d87185ca223a` supplies independent
evidence for treating s390x as a store-buffer architecture; `leanprover/lean4` v4.34.1
(`5045d0056413266e57c625dcd7c365b10e377c52`) checks the proofs.

**What the formal results apply to.** The table theorems apply to the tables as written in the
Lean file; their link to real compilers is the differential check of finding 8, which covers only
the measured functions (8/32/64-bit integers; `swap`, `fetch_add`, `fetch_and`; the listed
orderings). The litmus theorems apply to candidate executions of the four programs of finding 6.3
under the transcribed model fragments. Extending either to 128-bit atomics, other read-modify-write
kinds, other targets or other LLVM versions needs the revalidation steps below; adjacency of
versions is not an argument.

**Configurations that are not Tier 1.** `i686` without SSE2 is described by the target
specification itself as "*not* considered a Tier 1 target"
(`i686_unknown_linux_gnu.rs:12`), and the live toolchain accepts `-sse2` only with the warning
"target feature `sse2` must be enabled to ensure that the ABI of the current target can be
implemented correctly".

**Relation to other reports in this corpus.** `tier1-atomics-and-fences-instruction-lowering`
tabulates the instruction matrix for all Tier 1 targets and five widths on 1.99.1; this report
re-measures a 36-function subset independently, adds `s390x`, `-C no-redzone=yes`,
`-C opt-level=0`, three further toolchains, the canaries and the Lean model, and corrects one
rationale (finding 7.1: the litmus shape that needs `ldar` is store buffering, not IRIW).
`weak-memory-execution-graphs-and-compilation-mappings` develops the general SC and store-buffer
graph theory in Lean without locked instructions or AArch64; `rc11-gps-fsl-timestamp-view-pcms-and-miri-store-buffer-completeness-gaps`
and `c20-seqcst-fences-release-sequences-thin-air-and-rc11-to-rvwmo-arm-compilation-soundness`
cover RC11 itself. The Lean file here is self-contained and imports none of them; it keeps to
what is specific to the Rust compiler's tables.

## Findings

### 1. The pipeline: `Ordering` value, const-generic intrinsic, LLVM IR instruction

`Basis: source [published source] + execution [real measurement]`

**Library level** (`rust-lang/rust@58cf8f9c…`, `library/core/src/sync/atomic.rs`). The public
methods take `order: Ordering` as an ordinary argument and `match` on it:

```rust
const unsafe fn atomic_store<T: Copy>(dst: *mut T, val: T, order: Ordering) {
    …   Relaxed => intrinsics::atomic_store::<T, { AO::Relaxed }>(dst, val),
        Release => intrinsics::atomic_store::<T, { AO::Release }>(dst, val),
        SeqCst => intrinsics::atomic_store::<T, { AO::SeqCst }>(dst, val),
        Acquire => panic!("there is no such thing as an acquire store"),
        AcqRel => panic!("there is no such thing as an acquire-release store"),
```

(`L3974-3985`). `atomic_load` (`L3990-4001`) rejects `Release` and `AcqRel`; compare-exchange
(`L4063-4189`) accepts 15 `(success, failure)` pairs and rejects failure orderings `Release` and
`AcqRel`; `fence` (`L4489-4500`) and `compiler_fence` (`L4574-4585`) reject `Relaxed`. These are
the validity rules `MirAtomicOp.valid` encodes.

**Compiler level.** `core::intrinsics::AtomicOrdering` fixes the discriminants
`Relaxed = 0, Release = 1, Acquire = 2, AcqRel = 3, SeqCst = 4` (`library/core/src/intrinsics/mod.rs:77-85`,
mirrored by `ScalarInt::to_atomic_ordering`, `compiler/rustc_middle/src/ty/consts/int.rs:340-356`).
`compiler/rustc_codegen_ssa/src/mir/intrinsic.rs` reads the const-generic argument
(`parse_atomic_ordering`, `L117-120`) and calls one builder method per intrinsic: `atomic_load`
(`L377-392`), `atomic_store` (`L393-405`), `atomic_fence` with `SynchronizationScope::CrossThread`
for `atomic_fence` (`L543-547`) and `SingleThread` for `atomic_singlethreadfence` (`L549-556`).
`compiler/rustc_codegen_llvm/src/builder.rs` emits the instruction (`atomic_load` `L701-716`,
`atomic_store` `L928-944`, `atomic_cmpxchg` `L1368-1392`, `atomic_rmw` `L1394-1419`,
`atomic_fence` `L1421-1438`). LLVM numbers the same orderings `Monotonic = 2, Acquire = 4,
Release = 5, AcquireRelease = 6, SequentiallyConsistent = 7`
(`llvm/include/llvm/Support/AtomicOrdering.h:56-65`), which is why the AArch64 pattern for
`dmb ishld` tests `(i64 4)`.

**Measured IR at `-C opt-level=3`** (the atomic instructions are identical on all twelve optimized
configurations, up to one `!noalias` metadata number):

| Rust | LLVM IR |
| :--- | :--- |
| `a.load(Relaxed / Acquire / SeqCst)` | `load atomic i32, ptr %a monotonic / acquire / seq_cst, align 4` |
| `a.store(v, Relaxed / Release / SeqCst)` | `store atomic i32 %v, ptr %a monotonic / release / seq_cst, align 4` |
| `a.swap(v, o)`, `a.fetch_add(v, o)`, `a.fetch_and(m, o)` | `atomicrmw xchg / add / and ptr %a, … <o>` |
| `a.compare_exchange(c, n, AcqRel, Acquire)` | `cmpxchg ptr %a, i32 %c, i32 %n acq_rel acquire, align 4` |
| `a.compare_exchange_weak(c, n, Release, Relaxed)` | `cmpxchg weak ptr %a, i32 %c, i32 %n release monotonic, align 4` |
| `fence(o)` | `fence <o>` |
| `compiler_fence(o)` | `fence syncscope("singlethread") <o>` |

**Measured at `-C opt-level=0`** (`x86_64`, 1.99.1). The wrappers are not inlined; the ordering is
passed as its discriminant: `xorl %esi, %esi` (`Relaxed`), `movl $1, %edx` (`Release`),
`movl $2, %esi` (`Acquire`), `movl $3, %edx` (`AcqRel`), `movl $4, %edx` (`SeqCst`), and in IR
`invoke void @<mangled core::sync::atomic::Atomic<u32>::store>(ptr align 4 %a, i32 %v, i8 4)`. In the live probe the
un-inlined `core::sync::atomic::atomic_load::<u32>` contains
`load atomic i32, ptr %dst monotonic`, `… acquire` and `… seq_cst` side by side.

**Consequence for a MIR-level compiler** (`derived`). The MIR of a caller shows
`_5 = core::sync::atomic::Ordering::SeqCst; _0 = Atomic::<u32>::store(move _3, move _4, move _5)`;
the const-generic ordering appears only inside `core` after the `match`. A code generator that
starts from MIR either inlines and folds that `match` or must be correct for every arm, which is
what the all-orderings table theorems of finding 6.2 provide.

In Lean, `mirToLlvm` is the map of the table above and `mirToLlvm_injective` shows that operation
kind, weak flag, synchronization scope and every ordering are recoverable from the IR
instruction (`Basis: derived [kernel-checked proof]`, no dependencies).

### 2. Measured instruction selection

`Basis: execution [real measurement]` — `support/atomic_lowering_13_config_measurements.json`
(13 configurations) and `support/live_probe_results.json` (live probe).

Loads, stores and fences, 32-bit unless noted:

| Operation | `x86_64` | `i686` | AArch64 (all profiles) | `s390x` (`z10`) |
| :--- | :--- | :--- | :--- | :--- |
| `load(Relaxed)` | `movl (%rdi), %eax` | `movl (%eax), %eax` | `ldr w0, [x0]` | `llgf %r2, 0(%r2)` |
| `load(Acquire)` | same | same | `ldar w0, [x0]`; with `+rcpc`: `ldapr w0, [x0]` | same |
| `load(SeqCst)` | same | same | `ldar w0, [x0]` (also with `+rcpc`) | same |
| `store(Relaxed)` | `movl %esi, (%rdi)` | `movl %eax, (%ecx)` | `str w1, [x0]` | `st %r3, 0(%r2)` |
| `store(Release)` | same | same | `stlr w1, [x0]` | same |
| `store(SeqCst)` | `xchgl %esi, (%rdi)` | `xchgl %ecx, (%eax)` | `stlr w1, [x0]` | `st %r3, 0(%r2); bcr 15, %r0` |
| `fence(Acquire)` | none | none | `dmb ishld` | none |
| `fence(Release)`, `fence(AcqRel)` | none | none | `dmb ish` | none |
| `fence(SeqCst)` | `lock orl $0, -64(%rsp)`; with `-C no-redzone=yes`: `lock orl $0, (%rsp)` | `mfence`; without SSE2: `lock orl $0, (%esp)` | `dmb ish` | `bcr 15, %r0` |
| `compiler_fence(any)` | none | none | none | none |

Read-modify-write and compare-exchange:

| Operation | `x86_64` / `i686` (32-bit) | AArch64 `-outline-atomics` | AArch64 default (outlined) | AArch64 `+lse` | `s390x` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `swap` | `xchgl %eax, (%rdi)` (all five orderings) | `ld[a]xr; st[l]xr; cbnz` | `bl __aarch64_swp4_{relax,acq,rel,acq_rel}` | `swp[a][l]` | `l; cs; jl` |
| `fetch_add` | `lock xaddl %eax, (%rdi)` | `ld[a]xr; add; st[l]xr; cbnz` | `bl __aarch64_ldadd4_…` | `ldadd[a][l]` | `l; lr; ar; cs; jl` |
| `fetch_and` (`u8`) | `movzbl (%rdi), %eax; …; lock cmpxchgb; jne` | `ldaxrb; and; stlxrb; cbnz` | `mvn; bl __aarch64_ldclr1_acq_rel` | `mvn; ldclralb` | `l; …; cs; jl` |
| `compare_exchange[_weak]` | `lock cmpxchgl %edx, (%rdi)` | `ld[a]xr; cmp; b.ne; st[l]xr; …; clrex` | `bl __aarch64_cas4_…` | `cas[a][l]` | `cs` |

On AArch64 the acquire variant (`a`) is selected when the success **or** the failure ordering
acquires, the release variant (`l`) when the success ordering releases, and `SeqCst` selects the
same `…al` / `_acq_rel` variant as `AcqRel` (measured: `fetch_add(SeqCst)` and `fetch_add(AcqRel)`
both give `ldaddal` / `bl __aarch64_ldadd4_acq_rel`; `compare_exchange_weak(Release, Relaxed)`
gives `casl` / `bl __aarch64_cas4_rel` / `ldxr … stlxr`).

64-bit operands on `i686`:

| Operation | SSE2 (default) | SSE1 only (`-sse2`, live probe) | x87 only (`-sse2,-sse`) |
| :--- | :--- | :--- | :--- |
| `load` (any ordering) | `movq (%eax), %xmm0` | `xorps %xmm0, %xmm0; movlps (%eax), %xmm0` | `fildll (%eax); fistpll (%esp)` |
| `store(Relaxed / Release)` | `movlps %xmm0, (%eax)` | `movlps %xmm0, (%eax)` | `fildll (%esp); fistpll (%eax)` |
| `store(SeqCst)` | `movlps %xmm0, (%eax); lock orl $0, (%esp)` | same | `fildll (%esp); fistpll (%eax); lock orl $0, (%esp)` |
| `swap`, `fetch_add`, `compare_exchange` | `lock cmpxchg8b` (loop for the first two) | same | same |
| `fence(SeqCst)` | `mfence` | `lock orl $0, (%esp)` | `lock orl $0, (%esp)` |

Number of the 36 functions whose assembly differs between two configurations of 1.99.1: red zone
on/off 1; `+lse` versus `+lse,+rcpc` 2 (`at_u32_load_acquire`, `at_u64_load_acquire`);
`+lse,+rcpc` versus `+lse,+rcpc,+rcpc3` 0; outlined versus inline AArch64 16; `i686` SSE2 versus
x87 3. The recorded assembly was cut at the first `#`, which removes AArch64 immediates
(`mov w9, ` stands for `mov w9, #1`); mnemonics and memory operands are unaffected, and the live
probe records the full text.

### 3. The LLVM source that produces each configuration-dependent cell

`Basis: source [published source]` — `llvm/llvm-project@6dfe1677ab8dffbc6ec13d53a1e0215d75147689`.

**`x86` `fence(SeqCst)`** (`llvm/lib/Target/X86/X86ISelLowering.cpp:33153-33174`). Only a
cross-thread `seq_cst` fence gets an instruction; anything else becomes `MEMBARRIER`, "a compiler
barrier; it codegens to a no-op":

```cpp
if (!Subtarget.avoidMFence() && Subtarget.hasMFence())
  return DAG.getNode(X86ISD::MFENCE, dl, MVT::Other, Op.getOperand(0));
SDValue Chain = Op.getOperand(0);
return emitLockedStackOp(DAG, Subtarget, Chain, dl);
```

with `hasMFence() { return hasSSE2() || is64Bit(); }` and `avoidMFence() { return is64Bit(); }`
(`X86Subtarget.h:286,289`). So `x86_64` always takes the locked stack operation, `i686` with SSE2
takes `mfence`, and `i686` without SSE2 takes the locked stack operation: exactly the measured
split.

**The red zone** (`X86ISelLowering.cpp:33088-33151`). `emitLockedStackOp` documents its location
as "a) very likely accessed only by a single thread to minimize cache traffic, and b) definitely
dereferenceable", and chooses

```cpp
const unsigned SPOffset = TFL.has128ByteRedZone(MF) ? -64 : 0;
```

(`L33121`) for `OR32mi8Locked`. `has128ByteRedZone` is
`Is64Bit && !IsWin64CC && !Fn.hasFnAttribute(Attribute::NoRedZone)` with the comment "x86-64 (non
Win64) has a 128 byte red zone which is guaranteed not to be clobbered by any interrupt handler"
(`X86FrameLowering.cpp:1486-1494`). `-C no-redzone` is a `rustc` codegen option
(`compiler/rustc_session/src/options.rs:2281`).

**`x86` `store(SeqCst)`** (`X86ISelLowering.cpp:33899-33986`). A legal-width `seq_cst` store is
converted to an atomic swap ("Convert seq_cst store -> xchg"). An illegal 64-bit store on a 32-bit
target is done with `MOVQ`/`MOVLPS` when SSE1 is present, otherwise through the x87 stack
(`FILD` then `FIST`), and then "If this is a sequentially consistent store, also emit an
appropriate barrier": `emitLockedStackOp`. This is why the `i686` 64-bit `SeqCst` store ends in
`lock orl $0, (%esp)` even when the same configuration uses `mfence` for `fence(SeqCst)`. The
64-bit load is selected in `ReplaceNodeResults` (`L36005-36088`: SSE1 `VZEXT_LOAD`, else `FILD`
plus a non-atomic `FIST` to a stack temporary).

**AArch64 loads and fences** (`llvm/lib/Target/AArch64/AArch64InstrAtomics.td`). The RCpc patterns
(`L51-61`, under `Predicates = [HasRCPC]`) match only `acquiring_load`, whose definition sets
`IsAtomicOrderingAcquire = 1` (`L37-42`); `seq_cst_load` (`L44-49`) matches only the `LDAR`
patterns (`L64`, `L80`, `L96`, `L114`). Fences (`L16-19`): scope 0 becomes `MEMBARRIER`, ordering
`4` (acquire) becomes `DMB 0x9` (`dmb ishld`), everything else `DMB 0xb` (`dmb ish`).

**AArch64 read-modify-write and compare-exchange**
(`llvm/lib/Target/AArch64/AArch64ISelLowering.cpp`). Library calls are selected "only if LSE was
not specified for subtarget": `if (Subtarget->outlineAtomics() && !Subtarget->hasLSE())`
(`L1021-1049`); `shouldExpandAtomicRMWInIR` (`L32347-32420`) and `shouldExpandAtomicCmpXchgInIR`
(`L32423-32443`) choose between leaving the instruction for LSE or a helper and expanding to
LL/SC. `isOpSuitableForRCPC3` (`L32200-32215`) applies only to 128-bit accesses with LSE2, which
is why `+rcpc3` changes nothing measured here. The same file states the pairing that CE1 depends
on (`L32230-32233`): "Store-Release instructions only provide seq_cst guarantees when paired with
Load-Acquire instructions." The helper names are generated in
`rust-lang/rust@58cf8f9c…:library/compiler-builtins/compiler-builtins/src/aarch64_outline_atomics.rs`
(`L11-18`: `__aarch64_{cas,swp,ldadd,ldclr,ldeor,ldset}N_ORDER` for
`ORDER = { relax, acq, rel, acq_rel }`; `L74-88`: `acquire!` and `release!` map the order to the
`a` and `l` instruction letters).

**s390x** (`llvm/lib/Target/SystemZ`). `lowerATOMIC_FENCE` (`SystemZISelLowering.cpp:5138-5157`)
emits `SystemZ::Serialize` only for a cross-thread `seq_cst` fence. Store selection
(`SystemZISelDAGToDAG.cpp:1806-1824`) replaces the atomic store with a regular store and adds:
"We have to enforce sequential consistency by performing a serialization operation after the
store." `Serialize` prints as `bcr 14,%r0` with the fast-serialization facility and `bcr 15,%r0`
otherwise (`SystemZAsmPrinter.cpp:677-684`); that facility is defined at
`SystemZFeatures.td:56-59` and first appears in the `Arch9NewFeatures` list (`L103-105`), and
`rustc` selects the older level with `base.cpu = "z10"`
(`compiler/rustc_target/src/spec/targets/s390x_unknown_linux_gnu.rs:9`), hence `bcr 15, %r0`.

### 4. Cross-release drift

`Basis: execution [real measurement] + source [published source]`

**MIR.** A separate 37-function MIR probe compiled with 1.93.1, 1.94.0, 1.96.0, 1.99.0, 1.99.1,
1.100.0 and 1.102.0-nightly shows non-span MIR differences in 0, 5, 2, 0, 0 and 0 functions across
consecutive pairs. The 5 between 1.94.0 and 1.96.0 are exactly its five atomic functions, and
every recorded diff line differs only in a type name:

```text
-fn f25_atomic_load_acquire(_1: &AtomicU64) -> u64 {
+fn f25_atomic_load_acquire(_1: &Atomic<u64>) -> u64 {
-        _0 = AtomicU64::load(move _2, move _3) -> [return: bb1, unwind continue];
+        _0 = Atomic::<u64>::load(move _2, move _3) -> [return: bb1, unwind continue];
```

(The 2 between 1.96.0 and 1.99.0 are not atomic functions.) The source confirms and narrows the
interval: at 1.95.0 `library/core/src/sync/atomic.rs` has
`pub type Atomic<T> = <T as AtomicPrimitive>::AtomicInner;` (`L345`) and `pub struct AtomicBool`
(`L372`); at 1.96.0 it has `pub struct Atomic<T: AtomicPrimitive>` (`L366`),
`pub type AtomicBool = Atomic<bool>;` (`L398`) and `pub type $atomic_type = Atomic<$int_type>;`
(`L2589`). The change is commit `fa66fef1d1c78d2ecf2ba09a68e25e1e7ab154f7` ("core: make atomic
primitives type aliases of `Atomic<T>`", committed 2026-03-01), first released in 1.96.0. The
struct stays `#[unstable(feature = "generic_atomic", issue = "130539")]` at 1.99.1 (`L382-387`)
while its aliases are stable. No instruction-level measurement straddles this change (the
earliest toolchain with IR and assembly here is 1.98.0-nightly).

**LLVM IR and assembly.** On `x86_64` at `-C opt-level=3`, 1.99.1, 1.100.0 and 1.102.0-nightly
produce identical assembly and identical IR for all 36 functions (LLVM 23.1.1 and 23.1.5). The
live 1.98.0-nightly probe (LLVM 22.1.6) matches 1.99.1 on 324 of 324 assembly bodies (after
applying the same `#` cut and ignoring branch-label numbers) and on the atomic IR lines of 322 of
324 functions over the nine shared configurations; the two differences are a `!noalias` metadata
number on one `cmpxchg`. `support/check_lowering_model.py` recomputes both figures.

### 5. Optimization canaries

#### 5.1 The four preserved canaries (twelve optimized configurations, four toolchains)

`Basis: execution [real measurement] + source [published source]`

| Canary | Result on every optimized configuration |
| :--- | :--- |
| `let _ = a.load(Relaxed); 42` | The load survives: IR `%0 = load atomic i32, ptr %a monotonic, align 4` with `%0` unused; `movl (%rdi), %eax; movl $42, %eax` / `ldr wzr, [x8]` / `l %r0, 0(%r2)`. |
| `a.store(x, Relaxed); a.store(y, Relaxed)` | Both stores survive (`movl %esi, (%rdi); movl %edx, (%rdi)`). |
| `*data = v; compiler_fence(Release); flag.store(1, Relaxed); compiler_fence(Acquire); *data` with `data: &mut u32` | Both `fence syncscope("singlethread")` instructions survive in IR and emit nothing; the reload is forwarded (`ret i32 %v`); two stores, no load. |
| the same without the two fences | Identical assembly to the previous row. |

The first row is consistent with `Instruction::mayWriteToMemory`
(`llvm/lib/IR/Instruction.cpp:1145-1163`): for a load it returns
`!cast<LoadInst>(this)->isUnordered()`, so any `monotonic` or stronger load counts as a possible
write, and `mayHaveSideEffects` (`L1346-1348`) is true whenever `mayWriteToMemory` is (`derived`;
the passes that consult these predicates were not read). The third row is what the library
documentation states:
"`compiler_fence` does not emit any machine code. However, note that `compiler_fence` is also
*not* a "compiler barrier"" (`library/core/src/sync/atomic.rs:4521-4522`). For LLVM 23.1.1 the
forwarding is consistent with `getSyncEffects` returning `NoModRef` for an object that is never
captured (`llvm/lib/Analysis/AliasAnalysis.cpp:461-485`, `derived`); the live probe shows the same
forwarding on LLVM 22.1.6, where its mechanism was not examined.

#### 5.2 The publication canary (live probe, LLVM 22.1.6 only)

`Basis: execution [real measurement] + source [published source]`

The documentation example for `compiler_fence` (`atomic.rs:4536-4567`) publishes a `static mut`
to a signal handler: `IMPORTANT_VARIABLE = 42; compiler_fence(Ordering::Release);
IS_READY.store(true, Ordering::Relaxed)`. The canary adds a later overwrite so that the first
store is dead for straight-line execution:

```rust
unsafe { IMPORTANT_VARIABLE = v };
compiler_fence(Release);          // absent in the second function
IS_READY.store(1, Relaxed);
unsafe { IMPORTANT_VARIABLE = w };
```

| | LLVM IR (`x86_64`, 1.98.0-nightly) | stores emitted |
| :--- | :--- | :--- |
| with the fence | `store i32 %v, ptr @IMPORTANT_VARIABLE`; `fence syncscope("singlethread") release`; `store atomic i32 1, ptr @IS_READY monotonic`; `store i32 %w, ptr @IMPORTANT_VARIABLE` | 3 |
| without | `store atomic i32 1, ptr @IS_READY monotonic`; `store i32 %w, ptr @IMPORTANT_VARIABLE` | 2 |

The same 3-versus-2 result holds on all ten optimized live configurations. Without the fence, a
handler that runs after `IS_READY` is set and before the last store sees the value from before
`v`. In LLVM 22.1.6 a fence is treated as reading and writing arbitrary memory:
`mayReadFromMemory` and `mayWriteToMemory` return `true` for `Instruction::Fence` regardless of
scope (`rust-lang/llvm-project@08c84e69…:llvm/lib/IR/Instruction.cpp:1038,1056`) and
`AAResults::getModRefInfo(const FenceInst *…)` returns `getModRefInfoMask(Loc)`
(`llvm/lib/Analysis/AliasAnalysis.cpp:476-485`). **LLVM 23.1.1 replaced that blanket rule**: the
function now intersects per-analysis results with `getSyncEffects(this, Loc, AAQI)`, which
returns `NoModRef` for an object that is never captured and `Ref` or `ModRef` otherwise
(`llvm/llvm-project@6dfe1677…:llvm/lib/Analysis/AliasAnalysis.cpp:461-485, 540-557`). The
canary's datum is a global, but the canary was not run on LLVM 23 (1.99.1 and later), so its
result there is `not examined`.

### 6. The Lean development

`Basis: derived [kernel-checked proof]` — `support/RustAtomicLoweringSoundness.lean`, 2,037
lines, no imports, 116 theorems. `lean -DElab.async=false -Ddebug.skipKernelTC=false` exits 0;
of the 54 audited theorems 11 depend on no axioms and 43 on `propext` only
(`support/lean_check_output.txt`). An environment-wide audit
(`support/audit_lean_environment.sh`) of all 1,306 declarations the file adds, generated
auxiliaries included, prints
`AUDIT|declarations=1306|theorems=424|unsafe=0|partial=0|unsafe_rec=0|axioms=#[propext]|declarations_using_Quot.sound=#[]`.
Recursive specification functions are declared `noncomputable`, so Lean generates no executable
`_unsafe_rec` companion for them; they are evaluated only by the kernel. The source text contains
none of `sorry`, `admit`, `native_decide`,
`bv_decide`, `omega`, `partial def`, `unsafe`, an `axiom` declaration, or a `Classical` reference.

#### 6.1 Definitions

- `RustOrdering` with `acq`, `rel`, `sc` and `le` as component-wise implication; `MirAtomicOp`
  = `load | store | rmw | casStrong | casWeak | fence | compilerFence` with `valid`;
  `LlvmAtomic`; `mirToLlvm`.
- Instruction selection: `x86_64Isel (redZone : Bool)`,
  `i686Isel (simd : I686Simd) (wide : Bool)` with `I686Simd = sse2 | sse1Only | x87Only`
  (`I686Simd.ofSse2 : Bool → I686Simd` gives the two preserved configurations),
  `a64Isel (p : FeatureProfile)` with `FeatureProfile = v80Inline | v80Outlined | lse | lseRcpc`,
  `s390xIsel`. `TsoCfg` enumerates the nine store-buffer configurations
  (`x86_64` × 2, `i686` × 3 × 2 widths, `s390x`).
- Candidate executions: events with thread, kind, location and an architecture attribute;
  `po`; a reads-from witness `rf : Nat → Option Nat` (`none` = initial value); `Acyclic` over an
  inductive transitive closure, with certificates (a strictly increasing rank for "acyclic", a
  bounded path for "cyclic").
- Store-buffer model, from `herd/libdir/x86tso.cat`: `po_ghb = WW(po) | RM(po)`,
  `implied = MA(poWR) | AM(poWR)`, `mfence = fencerel(MFENCE)`, `acyclic ghb` and
  `acyclic po-loc | amo | com`. `xchg` and `lock orl` generate a locked read and a locked write;
  `mfence` and `bcr 15,%r0` generate a fence event.
- AArch64 model, from `herd/libdir/aarch64hwreqs.cat:127-138`, restricted to explicit data
  accesses and `dmb`: `[M]; po; [dmb.full]; po; [M]`, `[R]; po; [dmb.ld]; po; [M]`,
  `[W & L]; po; [R & A]`, `[(R & A) | (R & Q)]; po; [M]`, `[M]; po; [W & L]`, plus `lmws`
  (`aarch64deps.cat:53-55`), external observation (`rf & ext`, `ca & ext`), `irreflexive ob`
  and the internal requirements `coRW1-Exp` / `coWR-Exp` (`aarch64.cat:161-167`).
  `ldar` is tagged `A`, `ldapr` `Q`, `stlr` `L`.
- RC11 fragment, from `herd/libdir/rc11.cat`: sub-relations `[W ⊒ rel]; rf; [R ⊒ acq] ⊆ sw`,
  `po | sw` (closure `⊆ hb`), `[E^sc]; (po | rb | sw); [E^sc] ⊆ psc_base`,
  `[F^sc]; po; rb; po; [F^sc] ⊆ psc_F`, with the two conditions `irreflexive (hb ; rb)` and
  `acyclic psc`. Because these are sub-relations, a violation found here is a violation of RC11
  (`derived`); nothing is claimed in the other direction.

#### 6.2 Table theorems (every operation, ordering and configuration)

| Theorem | Statement |
| :--- | :--- |
| `RustOrdering.le_refl`, `le_trans`, `le_antisymm`, `join_le`, `acquire_release_diamond` | The five orderings form a lattice; `Acquire` and `Release` are incomparable with join `AcqRel`, strictly below `SeqCst`. |
| `mirToLlvm_injective` | MIR to LLVM IR loses nothing. |
| `tso_compilerFence_emits_nothing`, `a64_fence_selection`, `compilerFence_emits_nothing_everywhere` | A compiler fence emits `[]` on all 13 model configurations. |
| `tso_weak_fence_emits_nothing`, `tso_seqcst_fence_has_barrier`, `tso_seqcst_store_has_barrier`, `tso_weaker_access_has_no_barrier` | On store-buffer targets exactly `SeqCst` stores and `SeqCst` fences contain a buffer-draining instruction; no load and no weaker store does. |
| `tso_rmw_and_cas_are_locked` | Every read-modify-write and compare-exchange contains a locked update, whatever its ordering. |
| `a64_load_selection`, `a64_store_selection` | `load(SeqCst)` is `ldar` on every profile; `ldapr` appears only for `load(Acquire)` under `lseRcpc`. |
| `a64_load_monotone`, `a64_store_monotone` | A stronger valid ordering never selects a weaker instruction (`ldr < ldapr < ldar`, `str < stlr`). |
| `a64_rmw_bits`, `a64_cas_bits` | Update primitives carry exactly `(o.acq, o.rel)`; for compare-exchange `(succ.acq ∨ fail.acq, succ.rel)`, independent of the weak flag. |
| `a64_required_order_is_barrier_ordered` | For all profiles and all valid pairs of accesses, if RC11 requires the same-thread order (acquiring read first, releasing write second, or `SeqCst` write before `SeqCst` read), the selected instructions are related by a direct `bob` clause. |
| `tso_required_order_is_kept` | The same for the nine store-buffer configurations. |

#### 6.3 Litmus theorems (all reads-from witnesses, all configurations)

Programs: **SB-SC** (`x.store(1, SeqCst); r0 = y.load(SeqCst)` ∥ the mirror image); **SB-fence**
(`Relaxed` accesses separated by `fence(SeqCst)`); **MP** (`data.store(1, Relaxed);
flag.store(1, Release)` ∥ `r0 = flag.load(Acquire); r1 = data.load(Relaxed)`); **IRIW** (two
`SeqCst` writers, two readers).

| Weak outcome | RC11 fragment | 9 store-buffer configurations | 4 AArch64 profiles |
| :--- | :--- | :--- | :--- |
| SB-SC `r0 = r1 = 0` | forbidden (`rc11_sbSC_forbidden`) | forbidden (`tso_sbSC_sound`) | forbidden (`a64_sbSC_sound`) |
| SB-fence `r0 = r1 = 0` | forbidden (`rc11_sbFence_forbidden`) | forbidden (`tso_sbFence_sound`) | forbidden (`a64_sbFence_sound`) |
| MP `r0 = 1, r1 = 0` | forbidden (`rc11_mp_forbidden`) | forbidden (`tso_mp_sound`) | forbidden (`a64_mp_sound`, including `ldapr`) |
| IRIW, all `SeqCst` | forbidden (`rc11_iriwSC_forbidden`) | not modelled | forbidden (`a64_iriwSC_sound`) |

Each target theorem has the form "for every `rf`, if the execution of the compiled program is
consistent then the weak outcome does not occur". `sbSC_sequential_outcome_is_allowed` shows the
models are not vacuously inconsistent: the sequential outcome of SB-SC is consistent on
`x86_64` and on every AArch64 profile.

### 7. Sharpness: the four counterexamples

`Basis: derived [kernel-checked proof]`; links to real compilers are `execution` where stated.

#### 7.1 CE1 — `load(SeqCst)` lowered to `ldapr`

`a64LdaprForSeqCst` is the RCpc table with one cell changed. `ce1_ldapr_allows_store_buffering`:
the SB-SC execution in which both loads return the initial value satisfies every requirement of
the AArch64 fragment (rank certificate), while `CE1` packages that with the RC11 and
real-table results. The lost edge is exactly `[W & L]; po; [R & A]` (`ce1_edge_lost`).
`ce1_mutant_keeps_mp_and_iriw` shows what is *not* lost: with `ldapr` everywhere, MP and IRIW
are still forbidden, because `[(R & A) | (R & Q)]; po; [M]` covers `Q`. Conversely
`a64_plain_loads_allow_mp_and_iriw` shows that plain `ldr` reads allow both. So on AArch64
`ldar` (rather than `ldapr`) is needed for the store-to-load shape only; IRIW needs an acquiring
read of either kind. The measured compilers do not emit the mutant: `load(SeqCst)` under
`+lse,+rcpc` and `+lse,+rcpc,+rcpc3` is `ldar` on both toolchains (4 mutant-exclusion checks).

#### 7.2 CE2 — `lock orl $0, -64(%rsp)` without a red zone

Model: a stack state `(sp, low)` where `low` is the lowest address the function may touch; the
ABI contract is `low + 128 ≤ sp` with a red zone and `low ≤ sp` without; the instruction is safe
when the lowest byte it touches is owned. `Stack.real_lowering_is_frame_safe`: the displacement
chosen by the table (`-64` with a red zone, `0` without) is safe under the matching contract.
`Stack.CE2`: without a red zone, on any stack whose owned region ends at `sp`, the contract holds
and displacement `-64` is unsafe. `Stack.top_of_stack_is_always_safe`: displacement `0` is safe
in both cases, so `-64` is an optimization (LLVM's stated reasons are false dependences and a
separate cache line) that the red-zone test guards. `Stack.lock_or_zero_preserves_value`: OR-ing
every bit of the cell with `0` writes back what was read. The model is about *ownership* of the touched bytes (LLVM's
"definitely dereferenceable"); it does not model page mappings or interrupt delivery. Measured:
`-C no-redzone=yes` gives displacement `0` on both toolchains (2 mutant-exclusion checks).

#### 7.3 CE3 — dropping the ordering edges of a compiler fence

Model: straight-line statements `store loc val | cfence`; `machine` erases `cfence`; a signal
handler observes memory after any prefix of the machine code.

- *General scheduling theorem* (`Sched.fence_edges_keep_prefix_closed`): if a schedule respects
  the edges "everything before the fence precedes everything after it", then at every
  interruption point at which some post-fence statement has executed, every scheduled pre-fence
  statement has executed.
- *The documentation example* (`Sched.fence_edges_protect_the_handler`, `Sched.CE3_reordering`):
  with the edges, source order is the only legal schedule of `IMPORTANT = 42; cfence; READY = 1`
  and the handler's assertion (`READY = 1 → IMPORTANT = 42`) holds at every point; without them
  the swapped schedule is legal and fails after its first store.
- *Elimination* (`Sched.dse_shapes`, `Sched.CE3_elimination`,
  `Sched.dse_preserves_final_memory`): a dead-store eliminator that treats the fence as a
  possible observer keeps all three stores of the publication canary; one that ignores it
  produces `READY = 1; IMPORTANT = 43`, which leaves final memory unchanged but lets the handler
  see `READY = 1` with neither published value.

`dse_shapes` reproduces both measured IR shapes of finding 5.2 (LLVM 22.1.6). The reordering
variant was not observed in any measured compiler output; it is a model result.

#### 7.4 CE4 — no lock, `mfence` or serialization on `SeqCst`

`TsoCfg.lowerNoScBarrier` turns `store(SeqCst)` into a plain store and `fence(SeqCst)` into
nothing. `ce4_plain_store_allows_store_buffering` and `ce4_dropped_fence_allows_store_buffering`:
on all nine configurations the weak SB execution satisfies both store-buffer requirements;
`ce4_edge_lost` identifies the missing write-to-read order. Measured code never matches the
mutant (18 mutant-exclusion checks on `x86_64`, `i686` and `s390x`).

### 8. Differential check of the Lean tables against measured assembly

`Basis: execution [real measurement]` — `support/check_lowering_model.py`,
`support/lean_lowering_table.txt`, `support/differential_check_summary.json`.

The Lean file prints, for 10 configurations × 37 probe functions, the shared-memory instruction
skeleton its table predicts (370 lines such as `TABLE|aarch64.lse_rcpc|at_u32_load_acquire|ldapr`).
The script reduces each measured assembly body to the same vocabulary (frame, GOT and register
traffic dropped; width suffixes and helper size digits normalized) and compares token lists for
equality.

| Data set | Configurations compared | Cells matched |
| :--- | :--- | :--- |
| preserved measurement (1.99.1, 1.100.0, 1.102.0-nightly) | 12 of 13 | 384 / 384 |
| live probe (1.98.0-nightly) | 10 of 12 | 370 / 370 |

The `-C opt-level=0` configurations are excluded (the wrappers only call into `core`), and the
live `s390x` configuration did not compile. In addition 108 canary checks and 24
mutant-exclusion checks pass, and corrupting one table cell in memory makes the comparison report
exactly the two expected mismatches. `probeTable_valid` proves every probe operation is valid.

### 9. Performance (`L1`–`L6`), Comprehensibility (`C1`–`C2`), and Validation (`V1`–`V4`)

`Basis: execution [real measurement] + derived`

- **Performance & Footprint (`L1`–`L6`):** **`L1` (Proof velocity):** authoring time
  `not measured`; structurally, 116 theorems over 143 definitions, the largest case split 900
  cases (`tso_required_order_is_kept`). **`L2` (Toolchain build time):** `not measured`.
  **`L3` (Compile / scan latency):** the live probe compiles 44 functions under 12 configurations
  in `2.3 s` wall time in total. **`L4` (Generated code runtime):** `not measured`; no generated
  code was executed. **`L5` (Checker throughput):** the full Lean file checks in `38.1 s` wall
  (`34.2 s` user) with one thread; the differential script runs in `0.15 s`. **`L6` (Footprint):**
  peak resident memory of the Lean check `904 MiB`; Lean source `85.0 KiB`; preserved measurement
  `159.8 KiB`; live results `163.9 KiB`.
- **Comprehensibility (`C1`–`C2`):** **`C1` (Auditability):** the four instruction selection
  tables occupy about 190 lines of Lean against `X86ISelLowering.cpp` (64,729 lines) and
  `AArch64ISelLowering.cpp` (35,375 lines); the three model fragments total about 350 lines
  against cat sources of 28 (`x86tso.cat`), 181 (`aarch64hwreqs.cat`, of which the `bob`
  definition is 12) and 40 (`rc11.cat`) lines. **`C2` (Orthogonality):** the measured
  configuration switches are independent in effect: red zone touches 1 cell, RCpc 2, outlining only update primitives, SSE
  level only 64-bit accesses and the fence; ordering edges of a compiler fence are independent
  of instruction emission (it emits none).
- **Validation (`V1`–`V4`):** **`V1` (Adequacy):** 754 / 754 table cells agree with compiler
  output; the comparison detects a planted fault; the models allow the sequential SB outcome.
  **`V2` (Live differential probe):** a second toolchain (1.98.0-nightly, LLVM 22.1.6)
  reproduces 324 / 324 preserved assembly bodies. **`V3` (Weak-memory / silicon leakage):**
  `not measured`; no litmus test was executed on hardware here (see
  `weak-memory-hardware-litmus-testing-x86-and-aarch64`). **`V4` (Held-out cases):** as a blind
  prediction `not measured`; the `i686` SSE1-only column and the five `ext_*` functions lie
  outside the preserved measurement and agree with the table, but the table was written with
  the live output available.

## Boundaries

- **Known not to apply:** the litmus theorems do not cover read-modify-write or compare-exchange
  *events* (LL/SC pairs, LSE instructions, outlined helpers and `lock`-prefixed updates appear
  only in the table theorems and, for x86 `xchg` and `lock orl`, as locked read/write pairs);
  programs with more than one non-initial write per location (the model sets `co` between
  non-initial writes to empty and checks `singleWriter`); dependencies; mixed-size accesses.
- **Attractive stronger conclusions that are not established:** that the tables are a sound
  compilation scheme for all programs; that RC11 consistency is characterized (only two necessary
  conditions over sub-relations are used); that `ldapr` is safe for `SeqCst` loads in programs
  without the store-to-load shape (only MP and IRIW were checked); that the reordering variant of
  CE3 happens in LLVM (it was not observed); that the red-zone model says anything about page
  faults or interrupt frames.
- **Modelling assumption:** `s390x` is checked against the x86 store-buffer model with
  `bcr 15,%r0` as the full fence. The support for this is indirect: LLVM serializes only after
  `seq_cst` stores and for `seq_cst` fences, and Linux defines `__mb()` as `bcr 15,0` / `bcr 14,0`
  while `__rmb()` and `__wmb()` are compiler barriers
  (`arch/s390/include/asm/barrier.h:13-38`). No formal s390x model was examined.
- **Not examined:** 128-bit atomics; `AtomicPtr` and `AtomicBool`; `fetch_sub`/`or`/`xor`/`nand`/
  `min`/`max`; `aarch64-apple-darwin`, `aarch64-pc-windows-msvc` (which adds trailing `dmb ish`
  after `SeqCst` stores) and other targets; `+lse2`, `+lse128`; `dmb ishst` (never emitted here);
  the outlined helpers' own code; the publication canary of finding 5.2 on LLVM 23; the code path
  by which `rustc` turns `-C no-redzone` into the `noredzone` function attribute; why store-to-load
  forwarding crosses single-thread fences for a noalias datum on LLVM 22; the LLVM dead-code and
  dead-store passes themselves; LLVM IR and assembly from before the 1.96.0 `Atomic<T>` change;
  `-C opt-level=0` instruction selection (only the call sites and the callee IR were inspected).
- **Unknown:** whether `getSyncEffects` in LLVM 23 keeps a single-thread fence as a barrier for
  dead-store elimination of an escaped global.
- **Unsupported:** nothing measured here is rejected by the compilers, but the `i686`
  configurations without SSE2 are accepted only with the warning quoted under Applicability and
  are outside what the target specification calls Tier 1.
- **Recording limitation:** the preserved assembly is cut at the first `#` and the preserved IR
  keeps only selected lines; neither affects the token comparison.

## Evidence

All observations were made on 2026-11-20. Every revision below was resolved through the GitHub
API (the commits endpoint, or the contents endpoint for submodule pointers) to the full hash
shown.

1. **`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67` (1.99.1)** — `Basis: source +
   documentation`. `library/core/src/sync/atomic.rs:27` ("Rust atomics currently follow the same
   rules as [C++20 atomics]"), `249`, `292-295`, `382-387`, `417`, `437`, `466`, `2625`,
   `3974-3985`, `3990-4001`, `4063-4189`, `4489-4500`, `4502-4567`, `4574-4585`;
   `library/core/src/intrinsics/mod.rs:77-85`; `compiler/rustc_middle/src/ty/consts/int.rs:340-356`;
   `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:117-120, 135-136, 377-405, 543-556`;
   `compiler/rustc_codegen_ssa/src/common.rs:65-68`;
   `compiler/rustc_codegen_llvm/src/builder.rs:701-716, 928-944, 1368-1392, 1394-1419, 1421-1438`;
   `compiler/rustc_session/src/options.rs:2281`;
   `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:7-9`,
   `i686_unknown_linux_gnu.rs:8-21`, `aarch64_unknown_linux_gnu.rs:24-30`,
   `s390x_unknown_linux_gnu.rs:9-10`;
   `library/compiler-builtins/compiler-builtins/src/aarch64_outline_atomics.rs:1-18, 27, 74-88`.
   Its `src/llvm-project` submodule is `rust-lang/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`.
2. **Other `rust-lang/rust` revisions** — `Basis: source + execution`. 1.93.1
   `01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf`; 1.94.0 `4a4ef493e3a1488c6e321570238084b38948f6db`;
   1.95.0 `59807616e1fa2540724bfbac14d7976d7e4a3860` (`atomic.rs:345, 372, 403`); 1.96.0
   `ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96` (`atomic.rs:366, 398, 418, 2589`); 1.99.0
   `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`; 1.100.0 `0ef1bc386059596dada8fb65b50425aab2ea637a`
   and 1.102.0-nightly `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (both with submodule
   `rust-lang/llvm-project@0a5579eb649d3634a9c30ac873300cc2944fa070`); 1.98.0-nightly
   `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (submodule
   `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5`); commit
   `fa66fef1d1c78d2ecf2ba09a68e25e1e7ab154f7`.
3. **`llvm/llvm-project` @ `6dfe1677ab8dffbc6ec13d53a1e0215d75147689` (`llvmorg-23.1.1`)** —
   `Basis: source`. `llvm/lib/Target/X86/X86ISelLowering.cpp:32482-32534, 33088-33151,
   33153-33174, 33899-33986, 36005-36088`; `X86Subtarget.h:286, 289`;
   `X86FrameLowering.cpp:1486-1494`; `llvm/lib/Target/AArch64/AArch64InstrAtomics.td:16-19,
   37-49, 51-65`; `AArch64ISelLowering.cpp:1021-1049, 32200-32255, 32347-32443`;
   `llvm/lib/Target/SystemZ/SystemZISelLowering.cpp:5138-5157`;
   `SystemZISelDAGToDAG.cpp:1806-1824`; `SystemZAsmPrinter.cpp:677-684`;
   `SystemZFeatures.td:56-59, 103-105`; `llvm/include/llvm/Support/AtomicOrdering.h:56-65`;
   `llvm/lib/IR/Instruction.cpp:1125-1163, 1346-1348`; `llvm/lib/Analysis/AliasAnalysis.cpp:461-485, 540-557`.
   All twelve files were compared byte for byte with `rust-lang/llvm-project@1b9c0d5f…` and
   are identical.
   `rust-lang/llvm-project@08c84e69…`: `llvm/lib/IR/Instruction.cpp:1038, 1056, 1069`;
   `llvm/lib/Analysis/AliasAnalysis.cpp:476-485`.
4. **`herd/herdtools7` @ `1ae595498c7af7d9d2f00e29aea328b36663104c`** — `Basis: normative` for
   the models as the Lean file uses them. `herd/libdir/x86tso.cat:6-28`; `filters.cat:4-21`;
   `stdlib.cat:31`; `aarch64hwreqs.cat:127-138`; `aarch64deps.cat:53-58`;
   `aarch64.cat:99-171`; `aarch64fences.cat`; `rc11.cat:16-38`.
5. **`torvalds/linux` @ `adc218676eef25575469234709c2d87185ca223a` (v6.12)** — `Basis: source`.
   `arch/s390/include/asm/barrier.h:13-38`.
6. **`leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (v4.34.1)** — the checker;
   `lean --version` reports this commit.
7. **Literature** — `Basis: published source` (bibliographic identity checked; the cat files
   above, not the papers, are what the Lean file transcribes). Lahav, Vafeiadis, Kang, Hur,
   Dreyer, "Repairing Sequential Consistency in C/C++11", PLDI 2017, DOI
   `10.1145/3062341.3062352`; Pulte, Flur, Deacon, French, Sarkar, Sewell, "Simplifying ARM
   Concurrency: Multicopy-Atomic Axiomatic and Operational Models for ARMv8", POPL 2018, DOI
   `10.1145/3158107`; Sewell, Sarkar, Owens, Zappa Nardelli, Myreen, "x86-TSO: A Rigorous and
   Usable Programmer's Model for x86 Multiprocessors", CACM 53(7), 2010, DOI
   `10.1145/1785414.1785443`; Podkopaev, Lahav, Vafeiadis, "Bridging the Gap between Programming
   Languages and Hardware Weak Memory Models", POPL 2019, DOI `10.1145/3290382`.
8. **Preserved support material** (`support/`):
   - `atomic_lowering_13_config_measurements.json` — `Basis: execution`. The 13 configurations
     (toolchain, target, flags, LLVM IR and assembly per function), `rustc -vV` identity of the
     seven toolchains, MIR call lines, and the MIR differences of the atomic functions.
   - `atomic_lowering_probe.rs` — the 36 preserved functions (reconstructed from the recorded
     names, signatures and IR) plus 8 live-only functions.
   - `run_live_probe.py`, `live_probe_results.json` — the live probe and its output
     (1.98.0-nightly).
   - `RustAtomicLoweringSoundness.lean`, `lean_check_output.txt`, `lean_lowering_table.txt` —
     the Lean development, its `#print axioms` output, and the table it prints.
   - `check_lowering_model.py`, `differential_check_summary.json` — the differential check and
     its result.
   - `audit_lean_environment.sh` — the environment-wide axiom and recursion audit.
   - `pinned_revisions.json` — every revision above with the API path that resolves it.

## Revalidation

1. **Re-check the proofs (about 40 s, about 1 GiB):**
   ```bash
   cd reports/rust-weak-memory-atomics-mir-llvm-to-x86-aarch64-lowering-and-fence-soundness/support
   lean -DElab.async=false -Ddebug.skipKernelTC=false RustAtomicLoweringSoundness.lean > /tmp/lean_out.txt
   grep -v '^TABLE|' /tmp/lean_out.txt | diff - lean_check_output.txt
   grep '^TABLE|' /tmp/lean_out.txt | diff - lean_lowering_table.txt
   ```
   Any axiom other than `propext` in the first diff, or any change in the second, needs review.
2. **Re-run the differential check (under 1 s):** `python3 check_lowering_model.py` must print
   `cells: 754/754 matched` and `live vs preserved raw text: 324/324 assembly bodies`, and exit 0.
   `LEAN=lean ./audit_lean_environment.sh` (about 1 min) must print the `AUDIT|` line quoted in
   finding 6.
3. **Re-measure with another toolchain (about 3 s):**
   ```bash
   python3 run_live_probe.py --rustc "$(rustup which --toolchain <toolchain> rustc)" --out /tmp/live.json
   python3 check_lowering_model.py --live /tmp/live.json
   ```
   A mismatch names the cell that changed. Running this with 1.99.1 or later also settles the
   open question of finding 5.2: compare the store counts of
   `canary_publish_then_overwrite_with_cfence` (expected 3) and `…_without_cfence` (expected 2).
   Installing the `s390x-unknown-linux-gnu` standard library closes the live `s390x` gap.
4. **Check the configuration-dependent source lines at a new LLVM revision:**
   ```bash
   BASE="https://raw.githubusercontent.com/llvm/llvm-project/${NEW_LLVM_SHA}/llvm/lib"
   curl -fsSL "$BASE/Target/X86/X86ISelLowering.cpp" | grep -n "has128ByteRedZone(MF) ? -64 : 0"
   curl -fsSL "$BASE/Target/X86/X86Subtarget.h" | grep -nE "bool (hasMFence|avoidMFence)"
   curl -fsSL "$BASE/Target/AArch64/AArch64InstrAtomics.td" | grep -nE "LDAPR|seq_cst_load"
   curl -fsSL "$BASE/Target/SystemZ/SystemZISelDAGToDAG.cpp" | grep -n "SystemZ::Serialize"
   curl -fsSL "$BASE/Analysis/AliasAnalysis.cpp" | grep -n -A12 "getModRefInfo(const FenceInst"
   ```
   If an `LDAPR` pattern starts to match `seq_cst_load`, CE1 applies to that LLVM.
5. **Check the library dispatch at a new `rustc` revision:**
   ```bash
   curl -fsSL "https://raw.githubusercontent.com/rust-lang/rust/${NEW_RUST_SHA}/library/core/src/sync/atomic.rs" \
     | grep -nE "there is no such thing|pub struct Atomic<|pub type \\\$atomic_type"
   ```
6. **Re-resolve the pins:** for each entry of `support/pinned_revisions.json`,
   `gh api <api_path> --jq .sha` must print the recorded hash.
