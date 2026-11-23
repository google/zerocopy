# Rust `core::sync::atomic` Ordering Lowering, `x86_64` TSO Codegen, Fences, and Miri Data-Race Verification

## Summary

Rust's `core::sync::atomic` module adopts the C++20 sequential-consistency-for-data-race-free-programs (SC-DRF) memory model (`Relaxed`, `Release`, `Acquire`, `AcqRel`, and `SeqCst`) and lowers it cleanly through `rustc_codegen_ssa`, LLVM atomic IR (`monotonic`, `acquire`, `release`, `acq_rel`, `seq_cst`), and target-specific SelectionDAG / TableGen lowering into machine instructions. Across `rust-lang/rust`, `llvm/llvm-project`, live compilation under `rustc 1.98.0-nightly` / LLVM `22.1.6` / `miri 0.1.0`, and a `1,960`-line kernel-checked Lean `v4.34.1` formalization (`support/AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean`), the end-to-end semantics satisfy five central invariants:

1. **Ordinary `mov` Suffices for Non-`SeqCst` Loads and Stores and `SeqCst` Loads on `x86_64` TSO; Only `store(SeqCst)` and `fence(SeqCst)` Emit Explicit Inter-Core Store-Buffer-Draining Barriers**:
   Under `x86_64` Total Store Order (`-C opt-level=2`), `AtomicU64::load` with `Relaxed`, `Acquire`, or `SeqCst` emits LLVM `load atomic i64 ... {monotonic, acquire, seq_cst}` and lowers identically to plain `movq (%rdi), %rax` (`X86InstrCompiler.td`). `AtomicU64::store` with `Relaxed` or `Release` lowers to plain `movq %rsi, (%rdi)`. By contrast, `AtomicU64::store(_, Ordering::SeqCst)` triggers `LowerATOMIC_STORE` conversion to `ISD::ATOMIC_SWAP` (`X86ISelLowering.cpp:34426`), emitting `xchgq %rsi, (%rdi)` with implicit `LOCK` semantics that drain the per-core store buffer before subsequent loads execute. Both strong (`compare_exchange`) and weak (`compare_exchange_weak`) CAS preserve `cmpxchg` vs. `cmpxchg weak` in LLVM IR (`rustc_codegen_llvm/src/builder.rs:1369`) yet lower identically on `x86_64` to `movq %rsi, %rax; lock cmpxchgq %rdx, (%rdi); sete %al`. `fetch_or` / `fetch_and` exhibit return-value sensitivity: an unused return value lowers to a single `lock orq` / `lock andb` (`X86ISelLowering.cpp:32964`), whereas a used return value expands to a `lock cmpxchgq` CAS loop.

2. **`fence(SeqCst)` Uses Locked Stack Operations Instead of `MFENCE` on 64-Bit x86**:
   On `x86-64`, `X86Subtarget::avoidMFence()` returns `is64Bit()` (`true`, `X86Subtarget.h:299`), causing `LowerATOMIC_FENCE` (`X86ISelLowering.cpp:33547-33551`) to call `emitLockedStackOp` rather than emitting `mfence`. With the default SysV ABI 128-byte red zone (`has128ByteRedZone(MF) == true`), `fence(Ordering::SeqCst)` emits `lock orl $0, -64(%rsp)`; disabling the red zone with `-C no-redzone=yes` shifts the target to top-of-stack (`lock orl $0, (%rsp)`). By contrast, on `i686-unknown-linux-gnu` (`avoidMFence() == false`), default SSE2 emits `mfence`, whereas `-C target-feature=-sse2` (`hasMFence() == false`) falls back to `lock orl $0, (%esp)`. Cross-thread `fence(Acquire | Release | AcqRel)` lowers to `ISD::MEMBARRIER` (assembler comment `#MEMBARRIER`, zero CPU barrier instructions).

3. **`compiler_fence` Emits Zero Hardware Barriers (`syncscope("singlethread")`) and Never Synchronizes Distinct Threads**:
   `core::sync::atomic::compiler_fence` lowers via `intrinsics::atomic_singlethreadfence` to LLVM `fence syncscope("singlethread") <ord>`, which `LowerATOMIC_FENCE` converts to `ISD::MEMBARRIER` (`#MEMBARRIER` with zero hardware fence instructions). Empirically (`support/probe_results.json`), inserting `compiler_fence(Ordering::SeqCst)` blocks LLVM GVN/DSE elimination of repeated non-atomic loads (`raw_ptr_two_loads_no_fence` folds to `shl` / `addq %rax, %rax`, while `raw_ptr_two_loads_with_cfence` retains both memory accesses) and repeated dead stores (`raw_ptr_two_stores_no_fence` drops `*p = 1`, while `raw_ptr_two_stores_with_cfence` keeps both `movq $1` and `movq $2`). However, in Miri (`src/tools/miri/src/machine.rs:1414`), `atomic_fence(..., singlethread: true)` is an immediate no-op (`return interp_ok(())`), so replacing `Release`/`Acquire` or `fence` with `compiler_fence(Ordering::SeqCst)` on `Relaxed` atomics triggers undefined behavior (`Data race detected`) just like plain `Relaxed`.

4. **Miri Enforces Axiomatic SC-DRF Vector Clocks and Models Weak CAS Spurious Failure Regardless of x86 TSO**:
   Because x86 hardware preserves store-to-store FIFO visibility and load-load order, unsafe Rust code with `Ordering::Relaxed` message passing may accidentally pass execution tests on x86_64 silicon while still constituting language-level UB. Miri's vector-clock detector (`src/tools/miri/src/concurrency/data_race.rs`) tracks per-thread `clock`, `fence_acquire`, `fence_release`, and `write_seqcst` alongside per-cell `sync_vector`, `read_vector`, `write_vector`, and non-atomic clocks. Under live Miri execution (`cargo +nightly miri run --offline`), both direct `Release`/`Acquire` synchronization (`MIRI_ACQ_REL_OK=42`) and `fence(Release)` / `fence(Acquire)` bracketing `Relaxed` flag ops (`MIRI_FENCE_ACQ_REL_OK=42`) pass cleanly, whereas `Relaxed`-only and `compiler_fence(SeqCst)` message passing abort immediately (`exit 1`, `error: Undefined Behavior: Data race detected`). Miri also exercises `cmpxchg_weak_failure_rate` randomness (`222` spurious failures across `64` increments) so retry loops cannot silently rely on strong-CAS x86_64 codegen.

5. **Anneal Verification Architecture Separation and Lean 4 Mechanization**:
   In `joshlf/anneal`, the trusted sequential MIR engine (`trusted/lean/Trusted/{MirAst,MirSemantics}.lean`) is single-threaded and contains no atomic or store-buffer transitions; concurrent/weak-memory semantics live in `vendor/lean-miri/Miri/Concurrency/{AtomicAccess,AtomicDispatch,DataRace,WeakMemory}.lean` (`UPSTREAM_PIN.json`, documenting `rust-lang/miri` weak memory and vector-clock checks). Complementing that separation, `support/AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean` (`1,960` lines, `240` kernel-checked theorems, zero `Classical.choice`, zero `._unsafe_rec`, axioms `[Quot.sound, propext]`) mechanizes the entire Rust-to-x86-TSO lowering mapping, C++20/Miri happens-before vs. data-race semantics, TSO store-buffer safety for `Release`/`Acquire` MP (`mov`) and `SeqCst` SB (`xchg` / `lock orl`), and the intra-thread vs. cross-thread `compiler_fence` separation theorem.

## Applicability

This reference covers the interaction among seven pinned subjects recorded in `REPORT.json`:

1. **`rust-lang/rust` HEAD (`277240238554297f93fa9ee3c7643dfa03ccbbb4`) and executed toolchain (`rustc 1.98.0-nightly` commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, build date `2026-05-31`)**:
   - All live `rustc` LLVM IR, assembly, and `cargo +nightly miri run` empirical outputs in `support/probe_results.json` were captured on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, host `x86_64-unknown-linux-gnu`, `miri 0.1.0`) targeting `x86_64-unknown-linux-gnu` (`-C opt-level=2`, default red zone and `-C no-redzone=yes`) and `i686-unknown-linux-gnu` (`-C opt-level=2`, default SSE2 and `-C target-feature=-sse2`).
   - Source-line inspections of `library/core/src/sync/atomic.rs`, `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs`, `compiler/rustc_codegen_llvm/src/{builder.rs, llvm/conversions.rs}`, and `src/tools/miri/src/{machine.rs, concurrency/data_race.rs}` were anchored against `rust-lang/rust` HEAD (`277240238554297f93fa9ee3c7643dfa03ccbbb4`).
   - **Shared vs. revision-specific behavior across `14210df0e27ccd7d` and `27724023855429`**: The intrinsic mapping (`atomic_load`, `atomic_store`, `atomic_xchg`, `atomic_xadd..xor`, `atomic_cxchg`, `atomic_cxchgweak`, `atomic_fence`, `atomic_singlethreadfence`), `rustc_codegen_llvm::llvm::conversions::FromGeneric<AtomicOrdering>`, `builder.rs` LLVM builder calls, and Miri data-race vector-clock rules are identical across both commits. Between `14210df0e2` and `2772402385542`, `library/core/src/sync/atomic.rs` introduced the generic `pub struct Atomic<T: AtomicPrimitive>` representation (`generic_atomic`, lines `381-416`), added `const` / `#[rustc_const_unstable(feature = "const_atomic", issue = "160078")]` to internal atomic wrappers, and parameterized `atomic_store` / `atomic_load` by `const VOLATILE: bool` (`lines 4299-4326`), shifting line numbers inside `atomic.rs` relative to `14210df0e2`. Runtime lowering for `AtomicBool`, `AtomicPtr<T>`, and `Atomic{U,I}{8,16,32,64}` is unchanged (`VOLATILE = false` for non-volatile atomics).

2. **`llvm/llvm-project` HEAD (`ad79ef44876165477272af224c28d1e83637574d`) and release backend `llvmorg-22.1.6` (`fc4aad7b5db3fff421df9a9637605b9ca5667881`)**:
   - The `rustc 1.98.0-nightly` toolchain embeds LLVM `22.1.6`, corresponding to tag `llvmorg-22.1.6` (`fc4aad7b5db3fff421df9a9637605b9ca5667881`).
   - Primary source analysis of `llvm/lib/Target/X86/{X86Subtarget.h, X86ISelLowering.cpp, X86InstrCompiler.td, X86InstrMisc.td}` was inspected at `ad79ef44876165477272af224c28d1e83637574d`, and the probe codegen results directly confirm that the examined SelectionDAG rules (`avoidMFence()`, `emitLockedStackOp()`, `LowerATOMIC_FENCE`, `LowerATOMIC_STORE`, `lowerAtomicArith`, `LowerCMP_SWAP`, `shouldExpandLogicAtomicRMWInIR`) match LLVM `22.1.6` identically on the probed scalar and fence patterns.

3. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) and upstream `rust-lang/miri` (`7fa591d7d4dd9af8154becbc8332f8096f8323b1`)**:
   - Clarifies the boundary between Anneal's trusted sequential MIR verifier (`trusted/lean/Trusted/`) and its vendored Miri concurrency formalization (`vendor/lean-miri/Miri/Concurrency/`), which traces its weak-memory buffer model to `rust-lang/miri` (`WeakMemory.lean` docstring references `7fa591d7d4dd9af8154becbc8332f8096f8323b1`; Miri's in-tree source at `rust-lang/rust@277240238554297f93fa9ee3c7643dfa03ccbbb4` preserves the examined vector-clock and `singlethread` rules).

4. **`leanprover/lean4` (`v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`)**:
   - Applies to `support/AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean` checked standalone without Mathlib under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

Findings apply specifically to native-width integer/pointer atomics (`u8`/`u32`/`u64` on `x86_64`, `SeqCst`/`AcqRel` fences on `x86_64` and `i686` Linux targets), Miri's default vector-clock mode, and the discrete small-step/axiomatic models verified in Lean `v4.34.1`. Extension to oversized 128-bit operations, non-x86 architectures (ARMv8 LL/SC vs. LSE, RISC-V RVWMO), or Miri GenMC mode requires separate verification as noted under **Boundaries**.

## Findings

### 1. Front-End Surface: `core::sync::atomic::Ordering` and Ordering Constraints

Basis: normative (`C++20 [atomics.order]`) + source (`rust-lang/rust@277240238554297f93fa9ee3c7643dfa03ccbbb4:library/core/src/sync/atomic.rs`).

Rust exposes a 5-variant `#[non_exhaustive]` ordering enum (`library/core/src/sync/atomic.rs:462-526`):

```rust
#[non_exhaustive]
#[rustc_diagnostic_item = "Ordering"]
pub enum Ordering {
    Relaxed,
    Release,
    Acquire,
    AcqRel,
    SeqCst,
}
```

Notably, Rust omits C++'s `memory_order_consume` and restricts which orderings are valid per operation category via explicit runtime `panic!` guards inside the `const unsafe fn` helpers (`library/core/src/sync/atomic.rs:4286-4910`):

| API Operation Category | Allowed `Ordering` Values | Disallowed (Runtime `panic!`) Orderings | Primary Anchor (`atomic.rs` @ `27724023855429`) |
| --- | --- | --- | --- |
| `load` (`atomic_load`) | `Relaxed`, `Acquire`, `SeqCst` | `Release`, `AcqRel` ("no such thing as a release/acquire-release load") | Lines `4315-4326` |
| `store` (`atomic_store`) | `Relaxed`, `Release`, `SeqCst` | `Acquire`, `AcqRel` ("no such thing as an acquire/acquire-release store") | Lines `4299-4310` |
| `swap`, `fetch_add`, `fetch_sub`, bitwise RMW | `Relaxed`, `Acquire`, `Release`, `AcqRel`, `SeqCst` | None | Lines `4332-4379` |
| `compare_exchange` / `compare_exchange_weak` `success` | `Relaxed`, `Acquire`, `Release`, `AcqRel`, `SeqCst` | None (`AtomicRwOrd`) | Lines `4388-4514` |
| `compare_exchange` / `compare_exchange_weak` `failure` | `Relaxed`, `Acquire`, `SeqCst` | `Release`, `AcqRel` ("no such thing as an acquire-release/release failure ordering") | Lines `4443-4444`, `4509-4510` |
| `fence` / `compiler_fence` | `Acquire`, `Release`, `AcqRel`, `SeqCst` | `Relaxed` ("there is no such thing as a relaxed fence") | Lines `4814-4825`, `4899-4910` |

Two subtle normative rules documented in `library/core/src/sync/atomic.rs` govern compound and CAS operations:
- **Failure ordering mapping (`strongest_failure_ordering`, lines `4286-4294`)**: When a CAS wrapper derives default failure ordering from a `success` ordering, `Release => Relaxed`, `AcqRel => Acquire`, and `{Relaxed, Acquire, SeqCst}` map to themselves. Because failed CAS loads cannot store, a `Release` success ordering relaxes its failure load to `Relaxed`, and `AcqRel` strips its release component on failure to become `Acquire`. Note also lines `4435-4442`: C++17 eliminated the historical requirement that `failure <= success`, so Rust's `atomic_compare_exchange` permits `(Relaxed, SeqCst)` (`line 4407`/`4470`) and `(Acquire, SeqCst)` explicitly.
- **Notice on RMW half-orderings (`lines 478-480`, `493-495`, `3518-3520`)**: Using `Ordering::Acquire` on `fetch_add` or `compare_exchange` leaves the store portion `Relaxed`, and using `Ordering::Release` leaves the load portion `Relaxed`.

In addition, at `277240238554297f93fa9ee3c7643dfa03ccbbb4`, `library/core/src/sync/atomic.rs:384-416` expresses `AtomicBool`, `AtomicU*`, and `AtomicI*` through the unstable generic `pub struct Atomic<T: AtomicPrimitive>`, and `atomic_load` / `atomic_store` accept `const VOLATILE: bool` alongside `#[rustc_const_unstable(feature = "const_atomic", issue = "160078")]`.

### 2. Middle-End & Codegen Pipeline: MIR Intrinsics to LLVM Atomic IR

Basis: source (`rustc_codegen_ssa`, `rustc_codegen_llvm`) + execution (`support/probe_results.json`).

In `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs`, MIR atomic intrinsics lower through `BuilderMethods` as follows:

1. **Loads (`sym::atomic_load`, `intrinsic.rs:398-415`)**: Extracts const generic `ordering = fn_args.const_at(1).to_value()` and `volatile = fn_args.const_at(2).to_value()`, parses `parse_atomic_ordering(ordering)`, and invokes `bx.atomic_load(bx.backend_type(layout), source, order, volatile, layout.size)`. In `compiler/rustc_codegen_llvm/src/builder.rs:716-735`, `Llvm::atomic_load` builds `LLVMBuildLoad2`, sets ordering with `LLVMSetOrdering(load, AtomicOrdering::from_generic(order))`, conditionally sets `LLVMSetVolatile`, and enforces `LLVMSetAlignment(load, size.bytes() as c_uint)` because LLVM LangRef mandates alignment at least equal to access byte width for atomic loads.
2. **Stores (`sym::atomic_store`, `intrinsic.rs:416-435` -> `builder.rs:940-960`)**: Calls `LLVMBuildStore`, sets `LLVMSetOrdering`, optionally marks volatile, and enforces `LLVMSetAlignment(store, size.bytes() as c_uint)`.
3. **Compare-exchange (`sym::atomic_cxchg | sym::atomic_cxchgweak`, `intrinsic.rs:437-462` -> `builder.rs:1350-1374`)**: `weak = (name == sym::atomic_cxchgweak)`. `Llvm::atomic_cmpxchg` emits `LLVMBuildAtomicCmpXchg(..., llvm::FALSE /* SingleThreaded */)` and calls `llvm::LLVMSetWeak(value, weak.to_llvm_bool())`, extracting `(val, success)` via indices `0` and `1`. Thus `compare_exchange` emits `cmpxchg ptr ...` while `compare_exchange_weak` emits `cmpxchg weak ptr ...`.
4. **RMW (`sym::atomic_xadd | xsub | and | nand | or | xor | max | min | umax | umin | xchg`, `intrinsic.rs:463-570` -> `builder.rs:1376-1401`)**: Emits `LLVMBuildAtomicRMW(..., llvm::FALSE /* SingleThreaded */)`. Note that `builder.rs:1397-1399` converts pointer RMW results (`ret_ptr`) back with `inttoptr` if needed.
5. **Hardware Fence vs. Compiler Fence (`intrinsic.rs:571-584` -> `builder.rs:1403-1420`)**:
   - `sym::atomic_fence` (`core::sync::atomic::fence`) passes `SynchronizationScope::CrossThread` -> `single_threaded = false` -> LLVM emits `fence <ord>` (global synchronization scope).
   - `sym::atomic_singlethreadfence` (`core::sync::atomic::compiler_fence`) passes `SynchronizationScope::SingleThread` -> `single_threaded = true` -> LLVM emits `fence syncscope("singlethread") <ord>`.

`compiler/rustc_codegen_llvm/src/llvm/conversions.rs:87-97` maps Rust's `AtomicOrdering` 1-to-1 to LLVM IR orderings:

```rust
impl FromGeneric<AtomicOrdering> for llvm::AtomicOrdering {
    fn from_generic(ordering: AtomicOrdering) -> Self {
        match ordering {
            AtomicOrdering::Relaxed => Self::Monotonic,
            AtomicOrdering::Acquire => Self::Acquire,
            AtomicOrdering::Release => Self::Release,
            AtomicOrdering::AcqRel => Self::AcquireRelease,
            AtomicOrdering::SeqCst => Self::SequentiallyConsistent,
        }
    }
}
```

### 3. LLVM X86 Backend Lowering & Complete Rust -> LLVM -> `x86_64` / `i686` Lowering Table

Basis: source (`llvm/llvm-project@ad79ef44876165477272af224c28d1e83637574d`) + execution (`support/probe_results.json`).

#### 3.1 Why `x86_64` Loads/Stores Lower to `mov`, `SeqCst` Stores to `xchg`, and `SeqCst` Fences to `lock orl`

On x86 hardware obeying Intel/AMD Total Store Order (TSO):
- Loads are never reordered with earlier loads, and stores are never reordered with earlier stores or earlier loads; only older buffered stores may be delayed past later loads to different addresses (store-load bypassing).
- **Atomic Loads (`X86ISelLowering.cpp:32866-32885`, `X86InstrCompiler.td:1205-1215`)**: `shouldExpandAtomicLoadInIR` returns `AtomicExpansionKind::None` for native widths (`needsCmpXchgNb(Size)` is false for 8, 16, 32, 64 bits on `x86_64`). TableGen patterns match `atomic_load_nonext_{8,16,32,64}` directly to `MOV{8,16,32,64}rm`, and can even fold them into flag-setting compares (`CMP*mi`) because any single aligned full-width load already satisfies `monotonic`, `acquire`, and `seq_cst` on x86 TSO (comment at `X86InstrCompiler.td:1210-1213`).
- **Atomic Stores (`X86ISelLowering.cpp:34343-34430`, `X86InstrCompiler.td:1187-1203`, `X86InstrMisc.td:819-850`)**: In `LowerATOMIC_STORE`, lines `34349-34356` check:
  ```cpp
  bool IsSeqCst = Node->getSuccessOrdering() == AtomicOrdering::SequentiallyConsistent;
  bool IsTypeLegal = DAG.getTargetLoweringInfo().isTypeLegal(VT);
  if (!IsSeqCst && IsTypeLegal)
    return Op;
  ```
  Consequently, legal-width `monotonic` (`Relaxed`) and `release` stores survive intact and match TableGen `MOV{8,16,32,64}mr` / `MOV*mi`. By contrast, `seq_cst` stores fall through to line `34426`:
  ```cpp
  SDValue Swap = DAG.getAtomic(ISD::ATOMIC_SWAP, dl, Node->getMemoryVT(), ...);
  ```
  `ATOMIC_SWAP` selects `XCHG{8,16,32,64}rm` (`X86InstrMisc.td:850`), whose `LOCK` microarchitectural behavior is implicit on memory operands and drains the store buffer before any later load executes.
- **RMW Return-Value Sensitivity (`X86ISelLowering.cpp:32959-33025`, `33353-33410`, `34275-34341`)**:
  - `AtomicRMWInst::Xchg` returns `AtomicExpansionKind::None` -> `XCHG*rm`.
  - `Add` / `Sub` return `None` -> `lowerAtomicArith` keeps `atomic_load_add` (lowering `Sub` to `Add(-RHS)` and XOR of sign mask to `Add(SignMask)`) -> `LXADD` (`lock xadd*`, `X86InstrCompiler.td:1081`).
  - `Or` / `And` / `Xor` dispatch to `shouldExpandLogicAtomicRMWInIR` (`32959`): if `AI->use_empty()` (discarded return value), it returns `AtomicExpansionKind::None` and `lowerAtomicArithWithLOCK` emits a single `LOCK_OR` / `LOCK_AND` / `LOCK_XOR` (`lock orq`, `lock andb`). Note lines `34310-34333`: an idempotent unused non-volatile `atomicrmw or ptr, 0` skips the target memory address completely and emits `emitLockedStackOp` (if `seq_cst`) or `ISD::MEMBARRIER` otherwise! If the return value IS used (and not a single-bit test collapsing to `bts`/`btr`/`btc`), `shouldExpandLogicAtomicRMWInIR` returns `AtomicExpansionKind::CmpXChg`, which `AtomicExpandPass` converts to an explicit `lock cmpxchg` retry loop!
- **Strong vs. Weak CAS (`LowerCMP_SWAP`, `X86ISelLowering.cpp:33558-33600`, `X86InstrCompiler.td:1046`)**: SelectionDAG `ISD::ATOMIC_CMP_SWAP_WITH_SUCCESS` lowers identically for strong and weak `cmpxchg` via `X86ISD::LCMPXCHG_DAG` (`LCMPXCHG`, emitting `lock cmpxchgq` + `SETcc COND_E`, i.e., `sete %al`) because x86 hardware implements atomic CAS rather than LL/SC and cannot fail spuriously.
- **Hardware Fences vs. Single-Thread Fences (`X86Subtarget.h:296-299`, `LowerATOMIC_FENCE`, `X86ISelLowering.cpp:33474-33556`)**:
  `LowerATOMIC_FENCE` checks:
  ```cpp
  if (FenceOrdering == AtomicOrdering::SequentiallyConsistent &&
      FenceSSID == SyncScope::System) {
    if (!Subtarget.avoidMFence() && Subtarget.hasMFence())
      return DAG.getNode(X86ISD::MFENCE, ...);
    return emitLockedStackOp(DAG, Subtarget, Chain, dl);
  }
  return DAG.getNode(ISD::MEMBARRIER, dl, MVT::Other, Op.getOperand(0));
  ```
  In `X86Subtarget.h:296-299`, `hasMFence()` is `hasSSE2() || is64Bit()`, and `avoidMFence()` is `is64Bit()`. Therefore:
  1. On `x86_64`, `avoidMFence()` is unconditionally `true`, so `fence(SeqCst)` always invokes `emitLockedStackOp` (`X86::OR32mi8Locked`), choosing `SPOffset = TFL.has128ByteRedZone(MF) ? -64 : 0` (`33503`) to avoid false stack-top cache-line dependencies when the 128-byte SysV red zone is present (`lock orl $0, -64(%rsp)` vs. `lock orl $0, (%rsp)` with `-C no-redzone=yes`).
  2. On 32-bit `i686`, `avoidMFence()` is `false`: with SSE2 enabled (`hasMFence() == true`), it emits `mfence`; with `-C target-feature=-sse2`, `hasMFence()` is `false`, so it falls back to `emitLockedStackOp` on 32-bit `%esp` with no red zone (`lock orl $0, (%esp)`).
  3. All weaker fences (`Acquire`, `Release`, `AcqRel`) and all `compiler_fence` calls (`SyncScope::SingleThread`) take line `33555` and emit `ISD::MEMBARRIER` (`#MEMBARRIER`), producing zero CPU instructions while blocking IR/MIR optimizations and scheduling across the DAG chain.

#### 3.2 Complete Verified Rust -> LLVM IR -> Machine Assembly Matrix (`rustc 1.98.0-nightly` / LLVM `22.1.6`)

The table below compiles all 30 probed functions and 4 target profiles captured verbatim in `support/probe_results.json` (`compile_returncode == 0` for all profiles):

| Probe Function | Rust Operation | LLVM IR Instruction (`x86_64 -O2`) | Emitted Assembly (`x86_64 -O2` unless noted) | CPU Barrier Emitted? |
| --- | --- | --- | --- | --- |
| `load_relaxed` | `AtomicU64::load(Relaxed)` | `load atomic i64, ptr %a monotonic, align 8` | `movq (%rdi), %rax; retq` | No |
| `load_acquire` | `AtomicU64::load(Acquire)` | `load atomic i64, ptr %a acquire, align 8` | `movq (%rdi), %rax; retq` | No |
| `load_seqcst` | `AtomicU64::load(SeqCst)` | `load atomic i64, ptr %a seq_cst, align 8` | `movq (%rdi), %rax; retq` | No |
| `store_relaxed` | `AtomicU64::store(v, Relaxed)` | `store atomic i64 %v, ptr %a monotonic, align 8` | `movq %rsi, (%rdi); retq` | No |
| `store_release` | `AtomicU64::store(v, Release)` | `store atomic i64 %v, ptr %a release, align 8` | `movq %rsi, (%rdi); retq` | No |
| `store_seqcst` | `AtomicU64::store(v, SeqCst)` | `store atomic i64 %v, ptr %a seq_cst, align 8` | `xchgq %rsi, (%rdi); retq` | Yes (implicit `LOCK`) |
| `swap_{relaxed,acqrel,seqcst}` | `AtomicU64::swap(v, ord)` | `atomicrmw xchg ptr %a, i64 %v {monotonic,acq_rel,seq_cst}, align 8` | `movq %rsi, %rax; xchgq %rax, (%rdi); retq` | Yes (implicit `LOCK`) |
| `fetch_add_{relaxed,acquire,release,acqrel,seqcst}` | `AtomicU64::fetch_add(v, ord)` | `atomicrmw add ptr %a, i64 %v {ord}, align 8` | `movq %rsi, %rax; lock xaddq %rax, (%rdi); retq` | Yes (`lock`) |
| `fetch_or_used_acqrel` | `a.fetch_or(v, AcqRel)` (used) | `atomicrmw or ptr %a, i64 %v acq_rel, align 8` | `movq (%rdi), %rax; movq %rax, %rcx; orq %rsi, %rcx; lock cmpxchgq %rcx, (%rdi); jne .LBB15_1; retq` | Yes (`lock`) |
| `fetch_or_discarded_acqrel` | `let _ = a.fetch_or(v, AcqRel)` | `atomicrmw or ptr %a, i64 %v acq_rel, align 8` + `ret void` | `lock orq %rsi, (%rdi); retq` | Yes (`lock`) |
| `fetch_and_u8_discarded_acqrel` | `let _ = a.fetch_and(v, AcqRel)` | `atomicrmw and ptr %a, i8 %v acq_rel, align 1` + `ret void` | `lock andb %sil, (%rdi); retq` | Yes (`lock`) |
| `cas_strong_{acqrel_acquire,seqcst_seqcst}` | `compare_exchange` | `cmpxchg ptr %a, i64 %cur, i64 %new ...` | `movq %rsi, %rax; lock cmpxchgq %rdx, (%rdi); sete %al; retq` | Yes (`lock`) |
| `cas_weak_{relaxed_relaxed,acqrel_acquire}` | `compare_exchange_weak` | `cmpxchg weak ptr %a, i64 %cur, i64 %new ...` | `movq %rsi, %rax; lock cmpxchgq %rdx, (%rdi); sete %al; retq` | Yes (`lock`) |
| `cas_u32_strong_acqrel_acquire` | `AtomicU32::compare_exchange` | `cmpxchg ptr %a, i32 %cur, i32 %new acq_rel acquire, align 4` | `movl %esi, %eax; lock cmpxchgl %edx, (%rdi); sete %al; retq` | Yes (`lock`) |
| `hw_fence_{acquire,release,acqrel}` | `fence(Acquire\|Release\|AcqRel)` | `fence {acquire,release,acq_rel}` | `#MEMBARRIER; retq` | No |
| `hw_fence_seqcst` (`x86_64` default) | `fence(SeqCst)` | `fence seq_cst` | `lock orl $0, -64(%rsp); retq` | Yes (`lock`) |
| `hw_fence_seqcst` (`x86_64 -C no-redzone=yes`) | `fence(SeqCst)` | `fence seq_cst` | `lock orl $0, (%rsp); retq` | Yes (`lock`) |
| `hw_fence_seqcst` (`i686` default SSE2) | `fence(SeqCst)` | `fence seq_cst` | `mfence; retl` | Yes (`mfence`) |
| `hw_fence_seqcst` (`i686 -C target-feature=-sse2`) | `fence(SeqCst)` | `fence seq_cst` | `lock orl $0, (%esp); retl` | Yes (`lock`) |
| `comp_fence_{acquire,seqcst}_only` | `compiler_fence(Acquire\|SeqCst)` | `fence syncscope("singlethread") {acquire,seq_cst}` | `#MEMBARRIER; retq` | No |
| `raw_ptr_two_loads_no_fence` | Two raw reads `*p + *p` | Single `load i64` + `%_0 = shl i64 %x, 1` (CSE'd) | `movq (%rdi), %rax; addq %rax, %rax; retq` | No |
| `raw_ptr_two_loads_with_cfence` | Two raw reads + `compiler_fence(SeqCst)` | Two `load i64` separated by `fence syncscope("singlethread") seq_cst` | `movq (%rdi), %rax; #MEMBARRIER; addq (%rdi), %rax; retq` | No (compiler barrier preserved) |
| `raw_ptr_two_stores_no_fence` | `*p = 1; *p = 2` | Single `store i64 2, ptr %p` (DSE'd `*p = 1`) | `movq $2, (%rdi); retq` | No |
| `raw_ptr_two_stores_with_cfence` | `*p = 1; compiler_fence(SeqCst); *p = 2` | `store 1` + `fence syncscope("singlethread") seq_cst` + `store 2` | `movq $1, (%rdi); #MEMBARRIER; movq $2, (%rdi); retq` | No (compiler barrier preserved) |
| `comp_fence_seqcst_two_loads` / `hw_fence_acqrel_with_loads` | Two `AtomicU64::load(Relaxed)` + fence | Two `load atomic ... monotonic` separated by `fence ...` | `movq (%rdi), %rcx; #MEMBARRIER; movq (%rdi), %rax; addq %rcx, %rax; retq` | No (vs. `no_fence_two_loads` without `#MEMBARRIER`) |

Derived check on optimization interaction: LLVM cannot eliminate a redundant *atomic* load even in `no_fence_two_loads`, whereas LLVM aggressively folds adjacent non-atomic pointer reads (`raw_ptr_two_loads_no_fence`) via GVN/CSE (`shl i64 %x, 1`) and eliminates overwritten non-atomic stores (`raw_ptr_two_stores_no_fence`) via DSE. Inserting `compiler_fence` blocks both CSE and DSE at LLVM IR (`fence syncscope("singlethread") seq_cst`) and remains as `#MEMBARRIER` in the emitted `.s` without issuing any hardware fence instruction. Notice also that in `raw_ptr_two_loads_with_cfence`, x86 instruction selection still folded the second non-atomic load directly into `addq (%rdi), %rax` after the `#MEMBARRIER` boundary.

### 4. Miri Vector-Clock Data-Race Semantics and Empirical Enforcement

Basis: source (`src/tools/miri/src/machine.rs`, `src/tools/miri/src/concurrency/data_race.rs`) + execution (`support/probe_results.json`).

Whereas `x86_64` silicon hides `Relaxed` message-passing bugs because TSO never reorders stores past later stores or loads past earlier loads, Miri evaluates Rust's **abstract SC-DRF operational semantics**, catching data races deterministically whenever happens-before (`hb`) is absent.

1. **Vector-Clock Synchronization Mechanics (`data_race.rs:556-651`, `1487-1545`, `1842-1945`)**:
   Each thread maintains a `ThreadClockSet` containing `clock` (current thread timestamp vector), `fence_acquire` (buffer of release clocks observed by `Relaxed` atomic loads since the last acquire fence), `fence_release` (snapshot of `clock` taken at the last release fence), and `write_seqcst`. Each atomic memory cell stores `AtomicMemoryCellClocks` (`sync_vector`, `read_vector`, `write_vector`, `size`):
   - **Store Release (`store_release`, lines `589-599`)**: Checks `atomic_write_detect` (no conflicting unordered non-atomic writes or reads), then `atomic.sync_vector.clone_from(&thread_clocks.clock)`.
   - **Load Acquire (`load_acquire`, lines `556-568`)**: Checks `atomic_read_detect` (last non-atomic write happened before `clock`), then joins `thread_clocks.clock.join(sync_clock)` directly.
   - **Store Relaxed vs. RMW Relaxed (`lines 603-651`)**: `store_relaxed` overwrites (`clone_from`) `atomic.sync_vector` with `&thread_clocks.fence_release`, reflecting the C++20 rule that a relaxed store breaks prior release sequences (`lines 611-617`), whereas `rmw_relaxed` and `rmw_release` **join** into `atomic.sync_vector`, preserving release sequences across RMW chains (`lines 633, 649`).
   - **Load Relaxed (`lines 573-585`)**: Joins `sync_clock` into `thread_clocks.fence_acquire` rather than `thread_clocks.clock`; non-atomic memory checks test `self.write_was_before(&thread_clocks.clock)` and `atomic.write_vector <= thread_clocks.clock`, so no synchronization occurs until a cross-thread acquire fence promotes `fence_acquire` into `clock`.
   - **Fences (`atomic_fence`, `data_race.rs:1843-1884`)**: Cross-thread `AtomicFenceOrd::{Acquire, AcqRel, SeqCst}` calls `clocks.apply_acquire_fence()` (joining `fence_acquire` into `clock`), `SeqCst` joins the global `last_sc_fence` lockstep clock and `last_sc_write_per_thread`, and `{Release, AcqRel, SeqCst}` calls `clocks.apply_release_fence()` (copying `clock` into `fence_release`).
   - **Single-thread Fences (`machine.rs:1409-1419`)**:
     ```rust
     fn atomic_fence(ecx: &MiriInterpCx<'tcx>, ordering: AtomicOrdering, singlethread: bool) -> InterpResult<'tcx> {
         if singlethread {
             // We don't support signal handlers or interrupts so this is a NOP.
             return interp_ok(());
         }
         ecx.atomic_fence(AtomicFenceOrd::from(ordering))
     }
     ```
     Because `compiler_fence` passes `singlethread = true`, Miri skips all vector-clock updates cleanly.
   - **Mutable-Allocation and Alignment Checks (`atomic_access_check`, `data_race.rs:1431-1483`)**: Before performing an atomic load, store, RMW, or CAS, Miri enforces alignment equal to `place.layout.size` (`1440-1441`) and rejects atomic stores, RMWs, oversized loads (`size > pointer_size`), and non-`Relaxed` loads targeting immutable allocations (`Mutability::Not`, `1452-1481`), noting only `Relaxed` pointer-or-smaller loads are permitted on read-only memory (`1478`).
   - **CAS and Weak Spurious Failure (`atomic_compare_exchange`, `data_race.rs:887-961`)**: On non-GenMC execution, `can_fail_spuriously` gates `rng.random_bool(1.0 - ecx.machine.cmpxchg_weak_failure_rate)` (`lines 927-933`). On failure (`950-957`), Miri still runs `validate_atomic_load(place, fail, None)` and `perform_read_on_buffered_latest(place, fail)`, so the `failure` ordering establishes `Acquire` synchronization if and only if the loaded value came from a `Release` store.

2. **Live `cargo +nightly miri run --offline` Outcomes (`support/probe_results.json`)**:
   Executing all 5 minimal Rust Edition 2024 test crates (`UnsafeCell<u64>` data payload + `AtomicU64` flag) produced exact discrimination:
   - `miri_release_acquire_message_passing_ok`: `returncode = 0`, stdout `MIRI_ACQ_REL_OK=42`.
   - `miri_release_fence_acquire_fence_ok`: `returncode = 0`, stdout `MIRI_FENCE_ACQ_REL_OK=42`.
   - `miri_relaxed_unsynchronized_data_race_ub`: `returncode = 1`, stderr `error: Undefined Behavior: Data race detected between (1) non-atomic write on thread unnamed-1 and (2) non-atomic read on thread main at alloc248+0x10`.
   - `miri_compiler_fence_non_sync_data_race_ub` (using `compiler_fence(Ordering::SeqCst)` with `Relaxed` flag): `returncode = 1`, identical data-race UB error `error: Undefined Behavior: Data race detected between (1) non-atomic write on thread unnamed-1 and (2) non-atomic read on thread main at alloc248+0x10`.
   - `miri_cas_weak_spurious_failure_check` (64 increments in a retry loop with `compare_exchange_weak(i, i + 1, AcqRel, Acquire)`): `returncode = 0`, stdout `MIRI_CAS_WEAK_OK final=64 spurious_failures=222`.

### 5. `joshlf/anneal` Architecture Boundary and Mechanized Lean `v4.34.1` Formalization

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `support/AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean`) + execution (Lean kernel `v4.34.1`).

#### 5.1 Trusted Sequential MIR vs. `vendor/lean-miri` Concurrency

Inside `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
- `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` define the single-threaded sequential MIR abstract interpreter semantics. There are no thread identifiers, atomic orderings, vector clocks, or store buffers in the trusted sequential semantics boundary.
- Multi-threaded atomic access checking and weak-memory buffering live inside `vendor/lean-miri/Miri/Concurrency/`:
  - `AtomicAccess.lean:147-149` faithfully mirrors Miri's `machine.rs:1414` rule: `prepareAtomicFence (ordering : AtomicOrdering) (singlethread : Bool)` returns `.ok none` immediately when `singlethread` is `true`, skipping `AtomicFenceOrd.ofOrdering`.
  - `WeakMemory.lean:35, 108-380` defines Miri's bounded per-location `StoreBuffer` (`STORE_BUFFER_LIMIT : Nat := 128`, `bounded : newer.length < STORE_BUFFER_LIMIT`, non-deterministic `fetchChoices` over legal modification-order reads), citing `rust-lang/miri` commit `7fa591d7d4dd9af8154becbc8332f8096f8323b1`.

#### 5.2 Kernel-Checked Mechanization (`support/AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean`)

`support/AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean` (`1,960` lines, `80,168` bytes, `938` local constants, `240` theorems) is a zero-dependency Lean `v4.34.1` formalization verified with strict kernel flags (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and audited via Lean MetaM to depend strictly on `[Quot.sound, propext]` with zero `Classical.choice`, zero `sorryAx`, zero `Lean.ofReduceBool`/`ofReduceNat`, zero `partial def`, and zero compiler `._unsafe_rec` constants (`every def` marked `noncomputable def` without `deriving`).

| Section | Modeled Components | Key Proved Theorems (`AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean`) | What It Establishes |
| --- | --- | --- | --- |
| **Sec. 1** (L42–258) | `RustOrdering`, `SyncScope`, `RustAtomicOp`, `LlvmOrdering`, `LlvmAtomicInst`, `lowerRustToLlvm` | `lowerOrderingToLlvm_injective`, `lower_load_invalid_traps_*`, `lower_store_invalid_traps_*`, `lower_fence_invalid_traps_relaxed`, `lower_cmpxchg_strong_vs_weak_llvm_flag` | Exact Rust-to-LLVM IR ordering bijection (`Relaxed -> Monotonic`), panic traps for invalid orderings, and preservation of strong vs. weak `cmpxchg` in LLVM IR. |
| **Sec. 2** (L260–445) | `CpuArch`, `X86AbiConfig`, `X86TsoInsn`, `x86HasMFence`, `x86AvoidMFence`, `x86LockedStackDisp`, `lowerAtomicToTso` | `lower_load_all_valid_orderings_mov`, `lower_store_relaxed_release_mov`, `lower_store_seqcst_xchg`, `lower_fetchOr_used_vs_discarded`, `lower_cmpxchg_strong_weak_identical_x86`, `lower_fence_weak_orderings_noop`, `lower_fence_seqcst_x86_64_redzone`, `lower_fence_seqcst_x86_64_no_redzone`, `lower_fence_seqcst_i686_sse2_mfence`, `lower_fence_seqcst_i686_nosse2_lock_orl`, `lower_compiler_fence_always_noop`, `drainsStoreBuffer_iff_emitsCpuBarrier` | Total lowering correctness across `x86_64` redzone / no-redzone and `i686` SSE2 / no-SSE2, capturing `fetch_or` use sensitivity, identical strong/weak x86 CAS (`lockCmpxchg`), and `#MEMBARRIER` zero-barrier classification. |
| **Sec. 3** (L447–914) | `ExecGraph`, `ValidExecGraph`, `DirectSw`, `HappensBefore`, `Conflicting`, `DataRace`, `DataRaceFree`, `relaxedMpGraph` | `release_acquire_mp_drf`, `fence_release_acquire_mp_drf`, `relaxedMpGraph_valid`, `no_sw_of_no_rel_acq`, `relaxedMpGraph_no_sw`, `relaxedMp_hb_implies_sb`, `relaxed_mp_data_race_witness` | Parametric DRF proof for both `Release -> Acquire` and `fence(Release)` / `fence(Acquire)` MP, contrasted with an explicit 4-event `ValidExecGraph` witness (`relaxedMpGraph`) where `rf 1 2` holds yet `DataRace relaxedMpGraph 0 3` holds. |
| **Sec. 4** (L916–1052) | `VClock2`, `MiriThreadClocks`, `MiriCellClocks`, `miriAtomicStoreSync`, `miriAtomicLoadSync`, `miriApplyFence` | `miri_rel_acq_sync_passes_clocks`, `miri_fence_rel_acq_sync_passes_clocks`, `miri_relaxed_and_cfence_fail_race_check` | Soundness correspondence with Miri's vector clocks: `Release`/`Acquire` and `fence` pass `miriCanNaRead`, whereas `Relaxed` and `miriApplyFence true ...` (`compiler_fence`) violate `miriCanNaRead`. |
| **Sec. 5** (L1054–1630) | FIFO `BufEntry` store-buffer machine (`TsoMpReach`, `TsoSbReach` across `SbLowerMode`) | `tso_mov_preserves_rel_acq_mp`, `tso_sb_mov_weak_outcome`, `tso_sb_seqcst_xchg_no_weak`, `tso_sb_fence_seqcst_no_weak` | Operational x86-TSO proofs: FIFO buffer drain makes `movStore`/`movLoad` sound for MP (`rData = 42`), `movStore` SB reaches weak `(r0 = 0, r1 = 0)`, whereas lowering `store(SeqCst)` to `xchgMem` or inserting `fence(SeqCst)` (`lockOrlStack`) eliminates `(r0 = 0, r1 = 0)` by inductive state invariants. |
| **Sec. 6** (L1632–1932) | `IrStmt`, `CompilerRewrite`, `SignalReach`, `cfenceMpGraph` | `no_fence_allows_dse`, `no_fence_allows_cse`, `compiler_fence_blocks_dse`, `compiler_fence_blocks_cse`, `compiler_fence_signal_handler_sound`, `cfenceMp_hb_implies_sb`, `compiler_fence_non_sync_separation` | Proves `compiler_fence` blocks adjacent DSE/CSE/reordering and guarantees coherent single-CPU signal-handler MP safety (`memData = 42`), yet induces `DataRace cfenceMpGraph 0 5` cross-thread and still allows the x86-TSO SB weak `(r0 = 0, r1 = 0)` outcome. |
| **Sec. 7** (L1934–1960) | Master theorem `end_to_end_atomics_and_tso_soundness` | `end_to_end_atomics_and_tso_soundness` | Single composed conjunction tying lowering equivalences, MP/SB TSO safety invariants, and Relaxed / `compiler_fence` data-race witnesses together. |

## Boundaries

The scope of negative space (what is unexamined, unresolved, or provably excluded) is explicitly bounded as follows:

1. **Known not to apply — oversized / wide atomics (e.g., 128-bit `cmpxchg16b` / AVX vector atomics on `x86_64`, 64-bit `cmpxchg8b` / x87 `fild`+`fist` on non-SSE2 `i686`)**:
   As documented directly in `llvm/llvm-project@ad79ef44876165477272af224c28d1e83637574d` (`X86ISelLowering.cpp:32846-32885`, `33369-33374`, `34358-34421`), operations wider than native GPR width (`needsCmpXchgNb(Size)`) do **not** lower to `mov`, `xchg`, or single `lock xadd`; depending on subtarget features (`cx16`, AVX, SSE2), LLVM emits `cmpxchg8b`/`cmpxchg16b`, vector loads/stores, or libatomic library calls (`compiler-rt` / `__atomic_*`). The scalar `mov`/`xchg` rules proved in this report apply exclusively to native GPR widths (8/16/32/64 bits on `x86_64`, 8/16/32 bits on `i686`).

2. **Known not to apply — cross-thread safety of `compiler_fence` or `Relaxed` message passing outside same-CPU handlers**:
   Proven unconditionally false (`miri_compiler_fence_non_sync_data_race_ub` exits `1` in Miri; Lean theorems `compiler_fence_non_sync_separation`, `relaxed_mp_data_race_witness`, and `tso_sb_mov_weak_outcome`). Passing tests on real `x86_64` CPUs under `Relaxed` MP reflect TSO hardware conservatism (`tso_mov_preserves_rel_acq_mp`) and do **not** make `Relaxed` data races defined behavior in Rust/LLVM. Note also LLVM IR's `nocapture`/aliasing/TBAA semantics on non-atomic accesses are distinct from atomic barrier semantics: `compiler_fence` only orders memory accesses within a single thread or single hardware CPU core (`signalMainStep`).

3. **Unsupported in Miri default engine — signal handlers and hardware interrupts**:
   `src/tools/miri/src/machine.rs:1414-1416` explicitly comments `// We don't support signal handlers or interrupts so this is a NOP` and ignores `compiler_fence` (`singlethread: true`). Even when `compiler_fence` is paired with `Relaxed` flag operations solely for a single-CPU signal handler (which *is* sound under `compiler_fence_signal_handler_sound`), Miri's interpreter cannot verify signal-handler code and treats singlethread fences as no-ops. Additionally, per `src/tools/miri/src/concurrency/data_race.rs:986-989`, `release_clock` / thread-clock closure hooks raise `"this operation performs synchronization that is not supported in GenMC mode"` if GenMC backend dispatch hits non-GenMC helpers, and GenMC mode was **not examined** in our live probe.

4. **Not examined empirically — ARM64 (`aarch64`) / RISC-V weak-memory codegen and Miri `-Zmiri-weak-memory-emulation` (`WeakMemory.lean`) flag execution**:
   Although `vendor/lean-miri/Miri/Concurrency/WeakMemory.lean` (`STORE_BUFFER_LIMIT = 128`) was inspected at source level, our live `rustc` and `cargo +nightly miri` probe exercised `x86_64-unknown-linux-gnu` / `i686-unknown-linux-gnu` targets and Miri's default data-race vector-clock engine (plus `cmpxchg_weak` RNG failures), without executing `-Zmiri-preemption-rate=0` sweeps or cross-compiling `aarch64` `ldar`/`stlr`/`casal` lowering.

5. **Unknown / model idealization boundaries in `AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean`**:
   - The Lean formalization models bounded 2-location 2-thread operational machines (`TsoMpState`, `TsoSbState`, `VClock2`, `SignalMachineState`) and concrete finite graphs (`relaxedMpGraph`, `cfenceMpGraph`) alongside universal quantification over arbitrary finite/infinite `ExecGraph`s in `release_acquire_mp_drf` and `fence_release_acquire_mp_drf`. It does **not** mechanize arbitrary N-thread coherence cycles, `consume` orderings (which Rust lacks), hardware instruction pipelines, speculative execution, or mixed-size accesses.
   - `shouldExpandLogicAtomicRMWInIR` single-bit-test optimizations (`BitTestIntrinsic` lowering to `lock bts`/`btr`/`btc`, `X86ISelLowering.cpp:32974-33008`) were observed at source level and noted cleanly, not included as a separate constructor in `X86TsoInsn`, which models `fetch_or` used (`cmpxchgCasLoop`) vs. discarded (`lockOrDiscard`) directly observed in the probe.

6. **Not examined — LLVM IR `atomicrmw` volatile/idempotent `or ptr, 0` lowering probe and `core::sync::atomic::Atomic<T>` unstable `generic_atomic` API stability**:
   `X86ISelLowering.cpp:34310-34333` transforms an unused non-volatile `atomicrmw or ptr, 0` into `emitLockedStackOp` (when `seq_cst`) or `MEMBARRIER`, which was verified by source inspection rather than compiled in `probe_results.json`. Similarly, `Atomic<T>` (`library/core/src/sync/atomic.rs:381-386`) and `const_atomic` (`issue = "160078"`) carry `#[unstable]` / `#[rustc_const_unstable]` attributes whose surface stability is outside this lowering study.

## Evidence

### Preserved Support Material

All empirical probes, compiler outputs, and mechanized Lean proofs are self-contained inside this package's `support/` directory:
- [support/probe_atomics_x86_64_and_miri_race.py](support/probe_atomics_x86_64_and_miri_race.py) (`579` lines): Hermetic Python probe executing inside `tempfile.TemporaryDirectory()` that invokes `rustc --edition 2024` across 4 codegen configurations (`x86_64_O2_default`, `x86_64_O2_no_redzone`, `i686_O2_default_sse2`, `i686_O2_nosse2`) with `--emit=llvm-ir,asm` and executes 5 standalone Rust crates under `cargo +nightly miri run --offline`.
- [support/probe_results.json](support/probe_results.json) (`618` lines, `26,216` bytes, observed `2026-11-23T22:38:51Z`): Verbatim toolchain version strings, LLVM IR definitions, AT&T assembly bodies for all 30 probed functions + flag variations, and sanitized Miri stdout/stderr/exit codes.
- [support/AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean](support/AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean) (`1,960` lines, `80,168` bytes): Self-contained kernel-checked Lean `v4.34.1` formalization. Verified with:
  - `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean` -> exit `0`, zero warnings/errors.
  - Lean MetaM axiom & purity audit over all `938` local constants and `240` theorems -> `unsafe_rec_count=0`, `forbidden_axiom_count=0`, `unique_axioms=[Quot.sound, propext]`.

### Primary Source Citations

1. **`rust-lang/rust` (`277240238554297f93fa9ee3c7643dfa03ccbbb4`)**:
   - `library/core/src/sync/atomic.rs`: `Atomic<T>` (`381-416`), `Ordering` enum (`462-526`), `compare_exchange` / `compare_exchange_weak` (`2164-2240`, `3450-3511`), `strongest_failure_ordering` (`4286-4294`), `atomic_store` (`4299-4310`), `atomic_load` (`4315-4326`), `atomic_swap` / `atomic_add` / `atomic_sub` (`4332-4379`), `atomic_compare_exchange` / `atomic_compare_exchange_weak` (`4388-4514`), `fence` (`4814-4825`), `compiler_fence` (`4899-4910`).
   - `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs`: `sym::atomic_load` (`398-415`), `sym::atomic_store` (`416-435`), `sym::atomic_cxchg | sym::atomic_cxchgweak` (`437-462`), `sym::atomic_xadd..xor` (`530-570`), `sym::atomic_fence` (`571-575`, `CrossThread`), `sym::atomic_singlethreadfence` (`577-584`, `SingleThread`).
   - `compiler/rustc_codegen_llvm/src/builder.rs`: `atomic_load` (`716-735`), `atomic_store` (`940-960`), `atomic_cmpxchg` (`1350-1374`), `atomic_rmw` (`1376-1401`), `atomic_fence` (`1403-1420`).
   - `compiler/rustc_codegen_llvm/src/llvm/conversions.rs`: `FromGeneric<AtomicOrdering> for llvm::AtomicOrdering` (`87-97`).
   - `src/tools/miri/src/machine.rs`: `atomic_load`..`atomic_compare_exchange` (`1363-1407`), `atomic_fence` (`1409-1419`, immediate NOP on `singlethread == true`).
   - `src/tools/miri/src/concurrency/data_race.rs`: `AtomicReadOrd` / `AtomicWriteOrd` / `AtomicFenceOrd` (`90-145`), `atomic_access` (`520-551`), `load_acquire` / `load_relaxed` (`556-585`), `store_release` / `store_relaxed` / `rmw_release` / `rmw_relaxed` (`589-651`), `atomic_read_detect` / `atomic_write_detect` / `non_atomic_read_detect` / `non_atomic_write_detect` (`655-744`), `atomic_compare_exchange` (`887-961`, `cmpxchg_weak_failure_rate` RNG at `927-933`), `atomic_fence` (`964-972`, `1843-1884`), `atomic_access_check` (`1431-1483`), `validate_atomic_load` / `validate_atomic_store` / `validate_atomic_rmw` (`1487-1545`), `acquire_clock` / `release_clock` (`1921-1944`).

2. **`llvm/llvm-project` (`ad79ef44876165477272af224c28d1e83637574d` & release tag `llvmorg-22.1.6` at `fc4aad7b5db3fff421df9a9637605b9ca5667881`)**:
   - `llvm/lib/Target/X86/X86Subtarget.h`: `hasMFence()` (`296`: `hasSSE2() || is64Bit()`), `avoidMFence()` (`299`: `is64Bit()`).
   - `llvm/lib/Target/X86/X86ISelLowering.cpp`: `shouldExpandAtomicStoreInIR` (`32846-32862`), `shouldExpandAtomicLoadInIR` (`32866-32885`), `shouldExpandLogicAtomicRMWInIR` (`32959-33025`), `shouldExpandAtomicRMWInIR` (`33353-33410`), `emitLockedStackOp` (`33474-33533`, `SPOffset = TFL.has128ByteRedZone(MF) ? -64 : 0`), `LowerATOMIC_FENCE` (`33535-33556`), `LowerCMP_SWAP` (`33558-33600`), `lowerAtomicArith` (`34275-34341`), `LowerATOMIC_STORE` (`34343-34430`), `LowerOperation` dispatch (`35029-35043`).
   - `llvm/lib/Target/X86/X86InstrCompiler.td`: `LOCK_OR` (`813`), `LCMPXCHG` (`943-1046`), `LXADD` (`1081`), `atomic_store_{8,16,32,64}` -> `MOV*` (`1187-1203`), `atomic_load_nonext_{8,16,32,64}` -> `MOV*` (`1205-1215`).
   - `llvm/lib/Target/X86/X86InstrMisc.td`: `ATOMIC_SWAP` / `XCHG*rm` (`819-850`).

3. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) & `rust-lang/miri` (`7fa591d7d4dd9af8154becbc8332f8096f8323b1`)**:
   - `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean` (Pass 1 sequential single-threaded MIR semantics).
   - `vendor/lean-miri/Miri/Concurrency/AtomicAccess.lean` (`prepareAtomicFence` NOP on `singlethread` at lines `147-149`), `vendor/lean-miri/Miri/Concurrency/WeakMemory.lean` (`STORE_BUFFER_LIMIT = 128` at line `35`, citing `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`).

### Key Toolchain Output Specimen (Live Capture Excerpts)

From [support/probe_results.json](support/probe_results.json) (`rustc 1.98.0-nightly 14210df0e 2026-05-31`, LLVM `22.1.6`, `miri 0.1.0`):

```llvm
; x86_64 -O2 LLVM IR highlights
define void @store_seqcst(ptr noundef nonnull writeonly align 8 captures(none) %a, i64 noundef %v) unnamed_addr #0 personality ptr @rust_eh_personality {
bb1:
  store atomic i64 %v, ptr %a seq_cst, align 8
  ret void
}
define noundef i64 @raw_ptr_two_loads_no_fence(ptr noundef readonly captures(none) %p) unnamed_addr #3 {
start:
  %x = load i64, ptr %p, align 8, !noundef !4
  %_0 = shl i64 %x, 1
  ret i64 %_0
}
define noundef i64 @raw_ptr_two_loads_with_cfence(ptr noundef readonly captures(none) %p) unnamed_addr #1 personality ptr @rust_eh_personality {
bb1:
  %x = load i64, ptr %p, align 8, !noundef !4
  fence syncscope("singlethread") seq_cst
  %y = load i64, ptr %p, align 8, !noundef !4
  %_0 = add i64 %y, %x
  ret i64 %_0
}
```

```text
store_seqcst (x86_64):           xchgq %rsi, (%rdi); retq
hw_fence_seqcst (x86_64):        lock orl $0, -64(%rsp); retq
hw_fence_seqcst (-C no-redzone): lock orl $0, (%rsp); retq
hw_fence_seqcst (i686 sse2):     mfence; retl
hw_fence_seqcst (i686 -sse2):    lock orl $0, (%esp); retl
hw_fence_acqrel (x86_64):        #MEMBARRIER; retq
comp_fence_seqcst_only (x86_64): #MEMBARRIER; retq
```

```text
miri_release_acquire_message_passing_ok:  exit 0  stdout="MIRI_ACQ_REL_OK=42"
miri_release_fence_acquire_fence_ok:      exit 0  stdout="MIRI_FENCE_ACQ_REL_OK=42"
miri_relaxed_unsynchronized_data_race_ub: exit 1  "error: Undefined Behavior: Data race detected between (1) non-atomic write on thread `unnamed-1` and (2) non-atomic read on thread `main` at alloc248+0x10"
miri_compiler_fence_non_sync_data_race_ub: exit 1 "error: Undefined Behavior: Data race detected between (1) non-atomic write on thread `unnamed-1` and (2) non-atomic read on thread `main` at alloc248+0x10"
miri_cas_weak_spurious_failure_check:     exit 0  stdout="MIRI_CAS_WEAK_OK final=64 spurious_failures=222"
```

## Revalidation

Each claim class can be cheaply revalidated on any newer toolchain or backend revision without repeating the full multi-repository audit:

1. **Re-run the live `rustc` + `Miri` empirical probe**:
   Execute from the package directory (requires `rustc` with `x86_64` and `i686` targets installed, plus `+nightly miri`):
   ```bash
   python3 support/probe_atomics_x86_64_and_miri_race.py
   ```
   Compare the newly generated `support/probe_results.json` against the baseline specimens above: verify `load_seqcst -> movq`, `store_seqcst -> xchgq`, `hw_fence_seqcst -> lock orl $0, -64(%rsp)` vs. `lock orl $0, (%rsp)` vs. `mfence` (`i686`), `fetch_or` used (`lock cmpxchgq`) vs. discarded (`lock orq`), `#MEMBARRIER` retention, and `compiler_fence` failure (`exit 1`) under Miri.

2. **Re-verify the Lean `v4.34.1` kernel formalization**:
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/AtomicsOrderingX86TsoLoweringAndRaceSoundness.lean
   ```
   A zero exit code confirms all `240` theorems (`end_to_end_atomics_and_tso_soundness`, `tso_sb_seqcst_xchg_no_weak`, `tso_sb_fence_seqcst_no_weak`, `compiler_fence_non_sync_separation`, etc.) type-check in the Lean 4 kernel without warnings. To verify zero forbidden axioms or unsafe recursors, run a temporary `import Lean` MetaM check iterating `env.constants` and calling `collectAxioms` across all local declarations (`unsafe_rec_count=0`, `unique_axioms ⊆ {propext, Quot.sound}`).

3. **Diff the narrow upstream source regions if upgrading toolchains**:
   - `llvm/lib/Target/X86/X86Subtarget.h` around `avoidMFence()` / `hasMFence()` and `llvm/lib/Target/X86/X86ISelLowering.cpp` around `emitLockedStackOp`, `LowerATOMIC_FENCE`, `LowerATOMIC_STORE`, and `shouldExpandLogicAtomicRMWInIR`: checks if newer Intel/AMD microarchitectures cause LLVM to switch `avoidMFence()` to `false` or change the `-64(%rsp)` red-zone offset.
   - `compiler/rustc_codegen_llvm/src/llvm/conversions.rs` (`FromGeneric<AtomicOrdering>`) and `src/tools/miri/src/machine.rs` (`atomic_fence`): checks if singlethread fences or ordering conversions change semantics.

4. **Validate corpus schema compliance** from the corpus root:
   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```
