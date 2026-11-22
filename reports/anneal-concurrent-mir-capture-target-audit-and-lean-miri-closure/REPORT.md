# Anneal Concurrent MIR Capture Seams, `TargetRole::Specification` Origin Isolation, `SepPCM`/`ResPCM` Resource Algebras, and `vendor/lean-miri` Closure Cost

## Summary

Integrating weak-memory and concurrent primitive verification end-to-end into `Anneal` (`google/zerocopy` @ `64b0b6ae57882b290b19e8ee0f7d89c05daa0caf`, `SCHEMA_VERSION = 4`) is governed by four concrete implementation boundaries across `trusted/rustc-capture`, `trusted/cargo-anneal`, `trusted/audit/TrustedBoundary.lean`, `theory/Anneal/Core/SepPCM.lean`, and `vendor/lean-miri/UPSTREAM_PIN.json`:

1. **`mir_drops_elaborated_and_const_checked` Cross-Crate Atomic Dispatch vs. Monomorphized/Intrinsic Lowering (`trusted/rustc-capture`):**
   - `anneal-rustc-capture` hooks `providers.queries.mir_drops_elaborated_and_const_checked` (`capture.rs:76`) with `-Copt-level=0 -Cdebug-assertions=no -Coverflow-checks=no` (`capture.rs:915-917`). In schema version `4`, capture admits 8..=128-bit integers (`IntWidth::I128`), `Ty::Char`, `Ty::Ordering`, `Ty::OverflowPair(IntTy)` (`(int, bool)`), `UnOp::{Not, Neg}`, `BinOp::{Div, Rem, AddWithOverflow, SubWithOverflow, MulWithOverflow, Cmp}`, and `Rvalue::Cast(CastKind::IntToInt, ..)`, while rejecting generic items (`tcx.generics_of(def).count() != 0`), `#[rustc_intrinsic]` bodies, place projections, `Rvalue::{Ref, RawPtr, ThreadLocalRef, Aggregate}`, non-`IntToInt` casts (`PtrToPtr`, `Transmute`), `TerminatorKind::{Call, Drop, Assert, UnwindResume, UnwindTerminate, InlineAsm}`, provenance-bearing `ConstValue` statics (`try_to_scalar_int`), and `--extern` / `proc_macro` crates.
   - At `mir_drops_elaborated_and_const_checked` (`runtime-post-cleanup.after`), user calls to `core::sync::atomic::AtomicUsize` methods do **not** contain inline `core::intrinsics::atomic_*` calls: across a 4-function concurrent Rust probe (`exercise_all_atomics`, `SpinMutex<T>`, `MaybeUninit`/`ManuallyDrop`, and `std::sync` primitives), `runtime-post-cleanup.after` emits `21` cross-crate `Atomic::<T>::*` method calls with runtime `Ordering` enum arguments, `0` inlined `core::intrinsics::atomic_*` calls, `1` `&/*tls*/` (`Rvalue::ThreadLocalRef`), `1` static allocation pointer constant, `13` cleanup blocks, `15` `drop` terminators, `5` `resume` terminators, `7` `terminate` terminators, and `0` `Transmute` casts (both because `runtime-post-cleanup` precedes `CheckAlignment` and because `-Cdebug-assertions=no` disables UB-check alignment `Transmute`s; enabling `-Cdebug-assertions=yes` injects `3` pointer-to-`usize` `Transmute` casts in `CheckAlignment.after` and `6` by `runtime-optimized.after`). Conversely, `-O` (`optimized_mir`) inlines RMWs to `core::intrinsics::atomic_*` while leaving `atomic_{load,store,compare_exchange,compare_exchange_weak}` as `core::sync::atomic` helper calls and introducing `25` `PtrToPtr` and `3` `Transmute` casts from library internals.
   - Across compiler pins, `core::intrinsics::atomic_{load,store}` evolved from 2 generic parameters (`<T: Copy, const ORD: AtomicOrdering>`) in Anneal's pinned `rustc 1.98.0-nightly` (`f8a08b688c`) to 3 generic parameters (`<T: Copy, const ORD: AtomicOrdering, const VOLATILE: bool>`) in `rustc 1.102.0-nightly` (`3ef0c22cd`), matching `volatileConst` already present in `vendor/lean-miri/Miri/Interpreter/IntrinsicAtomic.lean:49`.
2. **`TargetRole::Specification` Forbids Importing `theory/Anneal/*` (`target.rs:59-68` & `TrustedBoundary.lean:3039-3060`):**
   - `cargo-anneal` (`verify.rs:1360-1380`) stages `trusted/lean/*.lean` as `TargetRole::Model` and `theory/*.lean` (`Anneal.*`) as `TargetRole::Proof`. Because `TargetRole::Specification::allows` (`target.rs:63`) permits only `Model | Specification`, authored `Spec` modules are mechanically forbidden from importing or referencing any declaration in `theory/Anneal/*`.
   - Furthermore, `TrustedBoundary.lean:3039-3060` (`targetAudit`) constructs the canonical proposition `mkApp (mkConst canonicalRoot) (mkApp2 (mkConst crateCtor) (mkConst subjectName) (mkConst specName))` with `let crateCtor : Name := `Trusted.MirSemantics.Crate.mk` checked for `TargetRole.model` origin. Consequently, user-visible concurrent specification types (such as wait-ordering levels, linear `MustRelease` tokens, or concurrent `Specs` records) referenced in `Spec.lean` must reside in `Trusted.*` (`Model`), `Init.*`/`Std.*` (`foundation`), or `Specification` helpers, while separation-logic resource algebras, view PCMs, linearizability simulations, and deadlock proof rules reside in `theory/Anneal/*` (`TargetRole::Proof`).
3. **`Anneal.Core.SepPCM.ExplPCM` Cancellativity Collapses Idempotent Ghost Knowledge; Non-Cancellative `ResPCM` Conservatively Extends It (`support/Anneal/ConcurrentSeamsProof.lean`):**
   - `Anneal.Core.SepPCM` (`SepPCM.lean:62-71`) requires `cancellative : ∀ a b₁ b₂ c : M, op a b₁ = some c → op a b₂ = some c → b₁ = b₂`. Kernel-checked theorem `explPCM_idempotent_eq_unit` (`0` axioms) proves directly over `Anneal.Core.ExplPCM` that `pcm.op a a = some a` forces `a = pcm.unit` (`explPCM_no_nonunit_self_duplication`), preventing `ExplPCM` from directly representing non-unit persistent/duplicable concurrency knowledge (`Once` initialization agreement, duplicable `Arc` read witnesses, or monotonic timestamp/view bounds).
   - Universe-polymorphic `ResPCM (M : Type u)` (`core : M -> Option M` without `cancellative`) passes unmodified `TrustedBoundary.lean` `"preflight"` and full `"requireMirWp": true` `"audit"` (`2,281` replayed declarations, `0` `Classical.choice`), embeds every `ExplPCM` with definitionally identical `sepConj` and `sepWand` (`explToResPCM`, `toResPCM_conj_iff`, `toResPCM_wand_iff`), proves persistent duplicability `□ P ⊢ □ P ∗ □ P` (`persistently_duplicable`), and pairs `byteHeapletPCM` with non-cancellative `agreeNatResPCM` in a single product algebra (`agreeNat_refutes_cancellativity`, `heaplet_and_persistent_agreement_coexist`).
4. **Exact `vendor/lean-miri` `execution_machine_closure` Footprint (`UPSTREAM_PIN.json`):**
   - `UPSTREAM_PIN.json` (`c92d1d9754`) already compiles and SHA-256-pins `160` `Miri.*` modules in `execution_machine_closure`, including **`33` concurrency, Tree-Borrows, and thread/TLS modules** (`13` `Miri.Concurrency.*` + `12` `Miri.TreeBorrows.*` + `8` `Miri.Interpreter.{IntrinsicAtomic, AtomicMachine, ThreadStacks, ThreadLocal, ThreadExit, ThreadTls, TlsDestructors, MainThread}` — `0` additional modules needed for atomic/race/Tree-Borrows/scheduler correspondence). Extending `execution_machine_closure` with the `9` OS synchronization and thread-shim roots (`FutexRuntime`, `Sync`, `InitOnce`, `Join`, `LinuxFutex`, `LinuxFutexMachine`, `PthreadSync`, `ThreadMachine`, `ThreadShimMachine`) adds exactly **`25` modules** (`39` if `Miri.Interpreter.ExecutionIntrinsic` and its `14` `IntrinsicX86.*` dependencies are included).

## Applicability

- **Repository Target:** `google/zerocopy` @ `64b0b6ae57882b290b19e8ee0f7d89c05daa0caf` (`anneal/trusted/{rustc-capture, cargo-anneal, audit}`, `anneal/theory/Anneal/Core/SepPCM.lean`, and `anneal/vendor/lean-miri/UPSTREAM_PIN.json` pinning `proofs-rs/lean-miri` @ `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`).
- **Compiler & Proof Toolchains:** Anneal's pinned `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).

## Findings

### 1. Concurrent MIR Capture Surface (`runtime-post-cleanup` vs. `-O` & Intrinsic Evolution)

`Basis: source + execution`

| Metric (`SAMPLE_CONCURRENT_RS`) | `runtime-post-cleanup` (`-Copt-level=0 -Cdebug-assertions=no -Coverflow-checks=no`) | `-O` (`optimized_mir`) |
| :--- | :---: | :---: |
| `Atomic::<T>::*` uninlined method calls | `21` | `2` |
| Inlined `core::intrinsics::atomic_*` calls | `0` | `9` (`11` in `1.102` incl. `atomic_load`/`atomic_store::<..., false>`) |
| `core::sync::atomic::atomic_*` helper calls | `0` | `22` (`20` in `1.102`) |
| `&/*tls*/` (`Rvalue::ThreadLocalRef`) | `1` | `1` |
| Static allocation pointer constants | `1` | `1` |
| Cleanup basic blocks / `drop` / `resume` / `terminate` | `13` / `15` / `5` / `7` | `11` / `15` / `3` / `7` |
| `&raw const` / `&raw mut` (`Rvalue::RawPtr`) | `0` (inside `core` wrappers) | `25` (inlined from `Atomic::as_ptr`) |
| `PtrToPtr` / `Transmute` casts | `0` / `0` | `25` / `3` |

- **Debug-assertion alignment `Transmute` control:** Enabling `-Cdebug-assertions=yes` leaves `runtime-post-cleanup.after` at `0` `Transmute` casts (because `3-2-000.runtime-post-cleanup.after` precedes `3-2-001.CheckAlignment.after`), while `CheckAlignment.after` injects `3` pointer-to-`usize` `Transmute` casts.
- **Intrinsic const-generic arity shift:** `library/core/src/intrinsics/mod.rs` declares `pub unsafe fn atomic_load<T: Copy, const ORD: AtomicOrdering>` and `atomic_store<T: Copy, const ORD: AtomicOrdering>` in `rustc 1.98.0-nightly` (`f8a08b688c`), versus `pub const unsafe fn atomic_load<T: Copy, const ORD: AtomicOrdering, const VOLATILE: bool>` and `atomic_store<T: Copy, const ORD: AtomicOrdering, const VOLATILE: bool>` in `rustc 1.102.0-nightly` (`3ef0c22cd`), matching `volatileConst` in `Miri/Interpreter/IntrinsicAtomic.lean:49`.

### 2. `TargetRole` Origin Matrix & `SepPCM` Cancellativity vs. `ResPCM`

`Basis: source + execution (Lean kernel)`

1. **Specification-Theory Boundary (`target.rs:59-68`):**
   - `Model -> {Model}`
   - `Capture -> {Model, Capture}`
   - `Specification -> {Model, Specification}` (rejects `Proof`, which stages all `theory/Anneal/*` modules)
   - `Expected -> {Model, Capture, Specification, Expected}`
   - `Proof -> {Model, Capture, Specification, Expected, Proof}`
2. **Kernel-Checked Resource Algebra Bridge (`Anneal.ConcurrentSeamsProof`, `414` lines):**
   - `explPCM_idempotent_eq_unit` & `explPCM_no_nonunit_self_duplication` (`0` axioms): proves `pcm.op a a = some a -> a = pcm.unit` for every `ExplPCM M`.
   - `ResPCM (M : Type u)` & `persistently_duplicable` (`0` axioms): replaces `cancellative` with `core : M -> Option M` (`core_unit`, `core_id`, `core_idem`), proving `ResEntails (persistently rpcm P) (resConj rpcm (persistently rpcm P) (persistently rpcm P))`.
   - `explToResPCM`, `toResPCM_conj_iff`, `toResPCM_wand_iff` (`0` axioms): embeds every `ExplPCM M` with `core := fun _ => some pcm.unit` and `Iff.rfl` agreement on separating conjunction and magic wand.
   - `agreeNat_refutes_cancellativity` & `heaplet_and_persistent_agreement_coexist` (`[propext]`): non-vacuous witnesses combining `Anneal.Core.byteHeapletPCM` with persistent `agreeNatResPCM` via `prodResPCM`.

### 3. `vendor/lean-miri` Closure Inventory (`UPSTREAM_PIN.json`)

`Basis: source + execution`

- **Already in `execution_machine_closure` (`33` concurrency/aliasing modules out of `160` total, `0` extra modules):**
  - `Miri.Concurrency.{AtomicAccess, AtomicDispatch, AtomicScalarMemory, DataRace, GlobalState, Lifecycle, LocalRace, Scheduler, SyncObject, Termination, Thread, VectorClock, WeakMemory}` (`13`)
  - `Miri.TreeBorrows.{FreezeMap, FreezeVisitor, GlobalState, LocationState, NormalTree, Permissions, RetagPipeline, RetagPipelineEffectful, RetagPolicy, Traversal, TreeState, UniMap}` (`12`)
  - `Miri.Interpreter.{AtomicMachine, IntrinsicAtomic, MainThread, ThreadExit, ThreadLocal, ThreadStacks, ThreadTls, TlsDestructors}` (`8`)
- **Additional `vendor_tree` modules required for OS futex/pthread/thread shims (`25` modules without `ExecutionIntrinsic`; `39` with `ExecutionIntrinsic`):**
  - `Miri.Concurrency.{Deadline, FutexRuntime, InitOnce, Join, Sync, SyncClock, SyncRuntime}` (`7`) and `Miri.Interpreter.{AllocationDriver, DeadlineMachine, EnvVars, ExecutionAddressChoices, ExecutionChoices, ExecutionStateTransport, IoError, LayoutCompat, LinuxFutex, LinuxFutexMachine, MiriShims, PthreadObjects, PthreadSync, Scheduling, ShimSignatures, ThreadMachine, ThreadShimMachine, TimeShims}` (`18`).

## Boundaries

1. **Textual MIR Dump vs. `TyCtxt` HIR/MIR Extraction:** `support/probe_anneal_concurrent_mir_and_tcb_seams.py` measures textual `-Zdump-mir=all` (`*.runtime-post-cleanup.after.mir`) and `--emit=mir` (`-O`) outputs on `SAMPLE_CONCURRENT_RS`; in `-O`, `core::sync::atomic::atomic_{load,store,compare_exchange,compare_exchange_weak}` remain uninlined helper calls in `1.98.0-nightly` (`atomic_{load,store}::<..., false>` partially inline in `1.102.0-nightly`), whereas direct `TyCtxt::instance_mir` traversal resolves monomorphized `core::sync::atomic` bodies directly to `ty::InstanceKind::Intrinsic`.
2. **Standalone `Anneal.ConcurrentSeamsProof` Scope:** `support/Anneal/ConcurrentSeamsProof.lean` imports unmodified `Anneal.Core.SepPCM` without modifying tracked repository files; `prodResPCM` is defined at `Type` (`M₁ M₂ : Type`) matching `Anneal.Core.ExplPCM`, while `ResPCM` itself is universe-polymorphic (`M : Type u`).
3. **OS Shim Closure Target Coverage:** The `25`-module OS sync/thread closure covers Linux `futex`, POSIX `pthread` sync, `InitOnce`, and thread spawn/join shims; macOS (`MacOsSync`), FreeBSD (`FreeBsdSync`), and Windows (`WindowsSync`, `WindowsThread`) shims remain separate modules in `vendor/lean-miri/Miri/Interpreter/`.

## Evidence

- `support/probe_anneal_concurrent_mir_and_tcb_seams.py` — reproducible empirical probe of `rustc` `runtime-post-cleanup` vs. `CheckAlignment` vs. `-O` MIR, `capture.rs`/`extract.rs`/`target.rs`/`TrustedBoundary.lean` invariants, and `UPSTREAM_PIN.json` import-closure deltas.
- `support/Anneal/ConcurrentSeamsProof.lean` — `414` lines, SHA-256 `399bfd1a13560c973edcc15de4ce0377eecdd9c81bf2fef755f57b8eb6421381`, zero-`sorry` Lean 4 proof of `ExplPCM` idempotent collapse and `ResPCM` conservative extension + product composition with `byteHeapletPCM`.
- `support/verify_concurrent_seams.py` — standalone 5-gate verification driver (`TrustedBoundary.lean` `"preflight"`, `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` topological compilation, `"audit"` with `"requireMirWp": true` replaying `2,281` declarations, and `#print axioms` across all `8` theorems).

## Revalidation

```bash
ZEROCOPY_ROOT=/path/to/zerocopy \
  ZEROCOPY_REV=64b0b6ae57882b290b19e8ee0f7d89c05daa0caf \
  python3 -B reports/anneal-concurrent-mir-capture-target-audit-and-lean-miri-closure/support/probe_anneal_concurrent_mir_and_tcb_seams.py

ANNEAL_ROOT=/path/to/zerocopy/anneal \
  python3 -B reports/anneal-concurrent-mir-capture-target-audit-and-lean-miri-closure/support/verify_concurrent_seams.py
```
