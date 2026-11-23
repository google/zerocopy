/-!
# Rust `core::sync::atomic` Ordering Lowering, x86-TSO Store-Buffer Soundness,
# `compiler_fence` Separation, and Miri Release-Acquire Data-Race Freedom

Kernel-checked Lean 4 (`v4.34.1`) formalization establishing four interlocking
theorems grounded in upstream `rust-lang/rust`, `llvm/llvm-project`, and Miri
vector-clock concurrency semantics:

1. **Rust -> LLVM -> x86-TSO Lowering Classification**: Exact functional model of
   `library/core/src/sync/atomic.rs`, `rustc_codegen_ssa`, `rustc_codegen_llvm`,
   and `llvm/lib/Target/X86` (`X86ISelLowering.cpp`, `X86Subtarget.h`,
   `X86InstrCompiler.td`), including `Relaxed`/`Acquire`/`SeqCst` load -> `mov`,
   `Relaxed`/`Release` store -> `mov` vs. `SeqCst` store -> `xchg`,
   `fetch_add` -> `lock xadd`, strong/weak `compare_exchange` -> `lock cmpxchg`,
   `fence(Acquire|Release|AcqRel)` -> `#MEMBARRIER` no-op vs. `fence(SeqCst)` ->
   `lock orl $0, -64(%rsp)` (red zone) / `lock orl $0, (%rsp)` (no red zone) /
   `mfence` (`i686` SSE2), and `compiler_fence` -> `syncscope("singlethread")`
   `#MEMBARRIER` (0 CPU barrier instructions).
2. **Release-Acquire Message-Passing Data-Race-Freedom (`release_acquire_mp_drf`)**
   and **Fence-Mediated MP DRF (`fence_release_acquire_mp_drf`)**, plus **Miri
   Vector-Clock Soundness Correspondence** matching `data_race.rs`.
3. **Relaxed Message-Passing Data-Race Witness (`relaxed_mp_data_race_witness`)**
   showing an explicit unsynchronized execution graph with `DataRace`.
4. **x86-TSO Operational Store-Buffer Machine & Lowering Soundness**:
   - Store-buffering (SB) weak outcome `(r0 = 0, r1 = 0)` reachable under
     `Relaxed`/`Release` `movStore` + `movLoad`.
   - Inductive LTS proof that `SeqCst` lowering (`xchgMem` or `lockOrlStack`)
     drains the per-thread store buffer and makes `(r0 = 0, r1 = 0)` impossible.
   - Inductive LTS proof that FIFO store-buffer draining makes plain `movStore`
     (`Release`) + `movLoad` (`Acquire`) sound for message passing on x86-TSO.
5. **`compiler_fence` Intra-Thread Reordering Barrier vs. Cross-Thread
   Non-Synchronization Separation Theorem**.

Purity invariants verified for this module:
- Every `def` is marked `noncomputable def` inside the namespace (no `noncomputable section`,
  no computable recursive equations, no compiler unsafe-recursor synthesis).
- Constructive kernel checking without classical choice, SMT bitvector/integer decision
  procedures, boolean reflection compiler axioms, incomplete proof placeholders, or
  automatically synthesized typeclass derivations.
-/

namespace AtomicsOrderingX86TsoLoweringAndRaceSoundness

/-! ## Section 1: Rust Atomic Orderings, Validity, and LLVM IR Lowering -/

/-- Rust `core::sync::atomic::Ordering` (C++20 memory orders without `consume`). -/
inductive RustOrdering where
  | relaxed
  | acquire
  | release
  | acqRel
  | seqCst

/-- Synchronization scope corresponding to `rustc_codegen_ssa::common::SynchronizationScope`. -/
inductive SyncScope where
  | crossThread
  | singleThread

/-- Target CPU architecture variants relevant to x86 atomic and fence lowering. -/
inductive CpuArch where
  | x86_64
  | i686Sse2
  | i686NoSse2

/-- ABI configuration controlling red-zone usage (`-C no-redzone=yes`). -/
structure X86AbiConfig where
  arch : CpuArch
  hasRedZone : Bool

/-- Valid atomic load orderings (`Relaxed`, `Acquire`, `SeqCst`). -/
noncomputable def isValidLoadOrdering : RustOrdering → Bool
  | .relaxed => true
  | .acquire => true
  | .seqCst  => true
  | .release => false
  | .acqRel  => false

/-- Valid atomic store orderings (`Relaxed`, `Release`, `SeqCst`). -/
noncomputable def isValidStoreOrdering : RustOrdering → Bool
  | .relaxed => true
  | .release => true
  | .seqCst  => true
  | .acquire => false
  | .acqRel  => false

/-- Valid atomic fence orderings (`Acquire`, `Release`, `AcqRel`, `SeqCst`). -/
noncomputable def isValidFenceOrdering : RustOrdering → Bool
  | .relaxed => false
  | .acquire => true
  | .release => true
  | .acqRel  => true
  | .seqCst  => true

/-- Compare-exchange failure orderings exclude `Release` and `AcqRel`. -/
noncomputable def isValidCmpxchgFailureOrdering : RustOrdering → Bool
  | .relaxed => true
  | .acquire => true
  | .seqCst  => true
  | .release => false
  | .acqRel  => false

/-- Ordering strength predicate for release semantics (store/RMW/fence). -/
noncomputable def hasReleaseSem : RustOrdering → Bool
  | .release => true
  | .acqRel  => true
  | .seqCst  => true
  | .relaxed => false
  | .acquire => false

/-- Ordering strength predicate for acquire semantics (load/RMW/fence). -/
noncomputable def hasAcquireSem : RustOrdering → Bool
  | .acquire => true
  | .acqRel  => true
  | .seqCst  => true
  | .relaxed => false
  | .release => false

/-- Ordering strength predicate for sequential consistency (`SeqCst`). -/
noncomputable def isSeqCstOrd : RustOrdering → Bool
  | .seqCst => true
  | .relaxed => false
  | .acquire => false
  | .release => false
  | .acqRel => false

/-- Equality check on `RustOrdering`. -/
noncomputable def rustOrdEq : RustOrdering → RustOrdering → Bool
  | .relaxed, .relaxed => true
  | .acquire, .acquire => true
  | .release, .release => true
  | .acqRel,  .acqRel  => true
  | .seqCst,  .seqCst  => true
  | _,        _        => false

theorem rustOrdEq_refl (o : RustOrdering) : rustOrdEq o o = true := by
  cases o <;> rfl

theorem rustOrdEq_sound {a b : RustOrdering} (h : rustOrdEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- `strongest_failure_ordering` from `library/core/src/sync/atomic.rs`. -/
noncomputable def strongestFailureOrdering : RustOrdering → RustOrdering
  | .release => .relaxed
  | .relaxed => .relaxed
  | .seqCst  => .seqCst
  | .acquire => .acquire
  | .acqRel  => .acquire

theorem strongestFailureOrdering_always_valid (o : RustOrdering) :
    isValidCmpxchgFailureOrdering (strongestFailureOrdering o) = true := by
  cases o <;> rfl

/-- Rust atomic operations audited across `core::sync::atomic`. -/
inductive RustAtomicOp where
  | load (o : RustOrdering)
  | store (o : RustOrdering)
  | swap (o : RustOrdering)
  | fetchAdd (o : RustOrdering)
  | fetchSub (o : RustOrdering)
  | fetchOr (o : RustOrdering) (retUsed : Bool)
  | fetchAnd (o : RustOrdering) (retUsed : Bool)
  | cmpxchg (strong : Bool) (succ fail : RustOrdering)
  | fence (o : RustOrdering)
  | compilerFence (o : RustOrdering)

/-- LLVM `AtomicOrdering` (`compiler/rustc_codegen_llvm/src/llvm/conversions.rs`). -/
inductive LlvmOrdering where
  | monotonic
  | acquire
  | release
  | acqRel
  | seqCst

/-- LLVM IR atomic instructions emitted by `rustc_codegen_llvm::builder::Builder`. -/
inductive LlvmAtomicInst where
  | loadAtomic (ord : LlvmOrdering)
  | storeAtomic (ord : LlvmOrdering)
  | rmwXchg (ord : LlvmOrdering)
  | rmwAdd (ord : LlvmOrdering)
  | rmwSub (ord : LlvmOrdering)
  | rmwOr (ord : LlvmOrdering) (retUsed : Bool)
  | rmwAnd (ord : LlvmOrdering) (retUsed : Bool)
  | cmpxchg (weak : Bool) (succ fail : LlvmOrdering)
  | fence (scope : SyncScope) (ord : LlvmOrdering)
  | invalidPanicTrap

/-- Exact mapping `FromGeneric<AtomicOrdering> for llvm::AtomicOrdering`. -/
noncomputable def lowerOrderingToLlvm : RustOrdering → LlvmOrdering
  | .relaxed => .monotonic
  | .acquire => .acquire
  | .release => .release
  | .acqRel  => .acqRel
  | .seqCst  => .seqCst

theorem lowerOrderingToLlvm_injective {a b : RustOrdering}
    (h : lowerOrderingToLlvm a = lowerOrderingToLlvm b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- Lowering from `RustAtomicOp` through `core::sync::atomic` + `rustc_codegen_llvm`. -/
noncomputable def lowerRustToLlvm : RustAtomicOp → LlvmAtomicInst
  | .load o =>
      match isValidLoadOrdering o with
      | true  => .loadAtomic (lowerOrderingToLlvm o)
      | false => .invalidPanicTrap
  | .store o =>
      match isValidStoreOrdering o with
      | true  => .storeAtomic (lowerOrderingToLlvm o)
      | false => .invalidPanicTrap
  | .swap o => .rmwXchg (lowerOrderingToLlvm o)
  | .fetchAdd o => .rmwAdd (lowerOrderingToLlvm o)
  | .fetchSub o => .rmwSub (lowerOrderingToLlvm o)
  | .fetchOr o retUsed => .rmwOr (lowerOrderingToLlvm o) retUsed
  | .fetchAnd o retUsed => .rmwAnd (lowerOrderingToLlvm o) retUsed
  | .cmpxchg strong succ fail =>
      match isValidCmpxchgFailureOrdering fail with
      | true  => .cmpxchg (Bool.not strong) (lowerOrderingToLlvm succ) (lowerOrderingToLlvm fail)
      | false => .invalidPanicTrap
  | .fence o =>
      match isValidFenceOrdering o with
      | true  => .fence .crossThread (lowerOrderingToLlvm o)
      | false => .invalidPanicTrap
  | .compilerFence o =>
      match isValidFenceOrdering o with
      | true  => .fence .singleThread (lowerOrderingToLlvm o)
      | false => .invalidPanicTrap

theorem lower_load_invalid_traps_release :
    lowerRustToLlvm (.load .release) = .invalidPanicTrap := rfl

theorem lower_load_invalid_traps_acqRel :
    lowerRustToLlvm (.load .acqRel) = .invalidPanicTrap := rfl

theorem lower_store_invalid_traps_acquire :
    lowerRustToLlvm (.store .acquire) = .invalidPanicTrap := rfl

theorem lower_store_invalid_traps_acqRel :
    lowerRustToLlvm (.store .acqRel) = .invalidPanicTrap := rfl

theorem lower_fence_invalid_traps_relaxed :
    lowerRustToLlvm (.fence .relaxed) = .invalidPanicTrap := rfl

theorem lower_compiler_fence_invalid_traps_relaxed :
    lowerRustToLlvm (.compilerFence .relaxed) = .invalidPanicTrap := rfl

theorem lower_cmpxchg_invalid_failure_traps (strong : Bool) (succ : RustOrdering) :
    lowerRustToLlvm (.cmpxchg strong succ .release) = .invalidPanicTrap := rfl

theorem lower_cmpxchg_strong_vs_weak_llvm_flag (succ fail : RustOrdering)
    (hvalid : isValidCmpxchgFailureOrdering fail = true) :
    lowerRustToLlvm (.cmpxchg true succ fail) =
      .cmpxchg false (lowerOrderingToLlvm succ) (lowerOrderingToLlvm fail) ∧
    lowerRustToLlvm (.cmpxchg false succ fail) =
      .cmpxchg true (lowerOrderingToLlvm succ) (lowerOrderingToLlvm fail) := by
  cases fail with
  | relaxed => constructor <;> rfl
  | acquire => constructor <;> rfl
  | seqCst  => constructor <;> rfl
  | release => cases hvalid
  | acqRel  => cases hvalid

/-! ## Section 2: LLVM-to-x86_64 / i686 TSO Lowering & Classification -/

/-- x86 / x86_64 machine-level lowering representation (`X86ISelLowering.cpp`). -/
inductive X86TsoInsn where
  | movLoad
  | movStore
  | xchgMem
  | lockXadd
  | lockOrDiscard
  | lockAndDiscard
  | cmpxchgCasLoop
  | lockCmpxchg
  | lockOrlStack (spDisp : Int)
  | mfence
  | membarrierNoop
  | trapInvalid

/-- True iff the lowered x86 instruction asserts a `LOCK`-prefixed or `MFENCE` hardware barrier. -/
noncomputable def emitsCpuBarrier : X86TsoInsn → Bool
  | .xchgMem        => true
  | .lockXadd       => true
  | .lockOrDiscard  => true
  | .lockAndDiscard => true
  | .cmpxchgCasLoop => true
  | .lockCmpxchg    => true
  | .lockOrlStack _ => true
  | .mfence         => true
  | .movLoad        => false
  | .movStore       => false
  | .membarrierNoop => false
  | .trapInvalid    => false

/-- True iff the instruction drains the local TSO store buffer on commit. -/
noncomputable def drainsStoreBuffer : X86TsoInsn → Bool
  | .xchgMem        => true
  | .lockXadd       => true
  | .lockOrDiscard  => true
  | .lockAndDiscard => true
  | .cmpxchgCasLoop => true
  | .lockCmpxchg    => true
  | .lockOrlStack _ => true
  | .mfence         => true
  | _               => false

/-- Models `X86Subtarget::hasMFence()` (`X86Subtarget.h:296`). -/
noncomputable def x86HasMFence : CpuArch → Bool
  | .x86_64     => true
  | .i686Sse2   => true
  | .i686NoSse2 => false

/-- Models `X86Subtarget::avoidMFence()` (`X86Subtarget.h:299`). -/
noncomputable def x86AvoidMFence : CpuArch → Bool
  | .x86_64     => true
  | .i686Sse2   => false
  | .i686NoSse2 => false

/-- Models `emitLockedStackOp` offset (`X86ISelLowering.cpp:33503`). -/
noncomputable def x86LockedStackDisp (cfg : X86AbiConfig) : Int :=
  match cfg.arch with
  | .x86_64 =>
      match cfg.hasRedZone with
      | true  => (-64 : Int)
      | false => (0 : Int)
  | .i686Sse2   => (0 : Int)
  | .i686NoSse2 => (0 : Int)

/-- Models `LowerATOMIC_FENCE` (`X86ISelLowering.cpp:33535-33556`). -/
noncomputable def lowerLlvmFenceToX86 (cfg : X86AbiConfig) (scope : SyncScope)
    (ord : LlvmOrdering) : X86TsoInsn :=
  match ord, scope with
  | .seqCst, .crossThread =>
      match Bool.and (Bool.not (x86AvoidMFence cfg.arch)) (x86HasMFence cfg.arch) with
      | true  => .mfence
      | false => .lockOrlStack (x86LockedStackDisp cfg)
  | _, _ => .membarrierNoop

/-- Models `LowerATOMIC_STORE` + `lowerAtomicArith` + `LowerCMP_SWAP` + `X86InstrCompiler.td`. -/
noncomputable def lowerLlvmToX86 (cfg : X86AbiConfig) : LlvmAtomicInst → X86TsoInsn
  | .loadAtomic _        => .movLoad
  | .storeAtomic .seqCst => .xchgMem
  | .storeAtomic _       => .movStore
  | .rmwXchg _           => .xchgMem
  | .rmwAdd _            => .lockXadd
  | .rmwSub _            => .lockXadd
  | .rmwOr _ false       => .lockOrDiscard
  | .rmwOr _ true        => .cmpxchgCasLoop
  | .rmwAnd _ false      => .lockAndDiscard
  | .rmwAnd _ true       => .cmpxchgCasLoop
  | .cmpxchg _ _ _       => .lockCmpxchg
  | .fence scope ord     => lowerLlvmFenceToX86 cfg scope ord
  | .invalidPanicTrap    => .trapInvalid

/-- End-to-end Rust -> LLVM -> x86-TSO lowering function. -/
noncomputable def lowerAtomicToTso (cfg : X86AbiConfig) (op : RustAtomicOp) : X86TsoInsn :=
  lowerLlvmToX86 cfg (lowerRustToLlvm op)

/-- Default Linux SysV x86-64 ABI configuration (128-byte red zone enabled). -/
noncomputable def defaultX86_64Cfg : X86AbiConfig :=
  { arch := .x86_64, hasRedZone := true }

/-- Kernel/UEFI/no-redzone x86-64 configuration (`-C no-redzone=yes`). -/
noncomputable def noRedZoneX86_64Cfg : X86AbiConfig :=
  { arch := .x86_64, hasRedZone := false }

theorem lower_load_all_valid_orderings_mov (cfg : X86AbiConfig) (o : RustOrdering)
    (hvalid : isValidLoadOrdering o = true) :
    lowerAtomicToTso cfg (.load o) = .movLoad := by
  cases o with
  | relaxed => rfl
  | acquire => rfl
  | seqCst  => rfl
  | release => cases hvalid
  | acqRel  => cases hvalid

theorem lower_store_relaxed_release_mov (cfg : X86AbiConfig) :
    lowerAtomicToTso cfg (.store .relaxed) = .movStore ∧
    lowerAtomicToTso cfg (.store .release) = .movStore := by
  constructor <;> rfl

theorem lower_store_seqcst_xchg (cfg : X86AbiConfig) :
    lowerAtomicToTso cfg (.store .seqCst) = .xchgMem := rfl

theorem lower_swap_all_orderings_xchg (cfg : X86AbiConfig) (o : RustOrdering) :
    lowerAtomicToTso cfg (.swap o) = .xchgMem := by
  cases o <;> rfl

theorem lower_fetchAdd_all_orderings_lockXadd (cfg : X86AbiConfig) (o : RustOrdering) :
    lowerAtomicToTso cfg (.fetchAdd o) = .lockXadd := by
  cases o <;> rfl

theorem lower_fetchOr_used_vs_discarded (cfg : X86AbiConfig) (o : RustOrdering) :
    lowerAtomicToTso cfg (.fetchOr o true) = .cmpxchgCasLoop ∧
    lowerAtomicToTso cfg (.fetchOr o false) = .lockOrDiscard := by
  cases o <;> constructor <;> rfl

theorem lower_cmpxchg_strong_weak_identical_x86 (cfg : X86AbiConfig)
    (succ fail : RustOrdering)
    (hvalid : isValidCmpxchgFailureOrdering fail = true) :
    lowerAtomicToTso cfg (.cmpxchg true succ fail) = .lockCmpxchg ∧
    lowerAtomicToTso cfg (.cmpxchg false succ fail) = .lockCmpxchg := by
  cases fail with
  | relaxed => cases succ <;> constructor <;> rfl
  | acquire => cases succ <;> constructor <;> rfl
  | seqCst  => cases succ <;> constructor <;> rfl
  | release => cases hvalid
  | acqRel  => cases hvalid

theorem lower_fence_weak_orderings_noop (cfg : X86AbiConfig) :
    lowerAtomicToTso cfg (.fence .acquire) = .membarrierNoop ∧
    lowerAtomicToTso cfg (.fence .release) = .membarrierNoop ∧
    lowerAtomicToTso cfg (.fence .acqRel)  = .membarrierNoop := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

theorem lower_fence_seqcst_x86_64_redzone :
    lowerAtomicToTso defaultX86_64Cfg (.fence .seqCst) = .lockOrlStack (-64) := rfl

theorem lower_fence_seqcst_x86_64_no_redzone :
    lowerAtomicToTso noRedZoneX86_64Cfg (.fence .seqCst) = .lockOrlStack 0 := rfl

theorem lower_fence_seqcst_i686_sse2_mfence (rz : Bool) :
    lowerAtomicToTso { arch := .i686Sse2, hasRedZone := rz } (.fence .seqCst) = .mfence := rfl

theorem lower_fence_seqcst_i686_nosse2_lock_orl (rz : Bool) :
    lowerAtomicToTso { arch := .i686NoSse2, hasRedZone := rz } (.fence .seqCst) =
      .lockOrlStack 0 := rfl

theorem lower_compiler_fence_always_noop (cfg : X86AbiConfig) (o : RustOrdering)
    (hvalid : isValidFenceOrdering o = true) :
    lowerAtomicToTso cfg (.compilerFence o) = .membarrierNoop ∧
    emitsCpuBarrier (lowerAtomicToTso cfg (.compilerFence o)) = false := by
  cases o with
  | relaxed => cases hvalid
  | acquire => constructor <;> rfl
  | release => constructor <;> rfl
  | acqRel  => constructor <;> rfl
  | seqCst  => constructor <;> rfl

theorem drainsStoreBuffer_iff_emitsCpuBarrier (insn : X86TsoInsn) :
    drainsStoreBuffer insn = emitsCpuBarrier insn := by
  cases insn <;> rfl

/-! ## Section 3: C++20 / Rust Axiomatic Execution Graph & Data-Race Freedom -/

abbrev ThreadId := Nat
abbrev LocId := Nat
abbrev EventId := Nat
abbrev Val := Nat

/-- Memory-model event classification in the C++20 / Rust execution graph. -/
inductive MemAccessKind where
  | naWrite
  | naRead
  | atLoad (o : RustOrdering)
  | atStore (o : RustOrdering)
  | atRmw (o : RustOrdering)
  | hwFence (o : RustOrdering)
  | compFence (o : RustOrdering)

/-- Whether an access is a write (or RMW). -/
noncomputable def isWriteKind : MemAccessKind → Bool
  | .naWrite    => true
  | .atStore _  => true
  | .atRmw _    => true
  | _           => false

/-- Whether an access is a read (or RMW). -/
noncomputable def isReadKind : MemAccessKind → Bool
  | .naRead     => true
  | .atLoad _   => true
  | .atRmw _    => true
  | _           => false

/-- Whether an access is non-atomic. -/
noncomputable def isNonAtomicKind : MemAccessKind → Bool
  | .naWrite => true
  | .naRead  => true
  | _        => false

/-- Whether an access is an atomic load/store/RMW (excluding fences). -/
noncomputable def isAtomicMemOp : MemAccessKind → Bool
  | .atLoad _  => true
  | .atStore _ => true
  | .atRmw _   => true
  | _          => false

/-- Whether an event is a release-capable atomic store or RMW. -/
noncomputable def isReleaseWriteKind : MemAccessKind → Bool
  | .atStore o => hasReleaseSem o
  | .atRmw o   => hasReleaseSem o
  | _          => false

/-- Whether an event is an acquire-capable atomic load or RMW. -/
noncomputable def isAcquireReadKind : MemAccessKind → Bool
  | .atLoad o => hasAcquireSem o
  | .atRmw o  => hasAcquireSem o
  | _         => false

/-- Whether an event is a cross-thread release fence (`fence(Release|AcqRel|SeqCst)`). -/
noncomputable def isReleaseHwFenceKind : MemAccessKind → Bool
  | .hwFence o => hasReleaseSem o
  | _          => false

/-- Whether an event is a cross-thread acquire fence (`fence(Acquire|AcqRel|SeqCst)`). -/
noncomputable def isAcquireHwFenceKind : MemAccessKind → Bool
  | .hwFence o => hasAcquireSem o
  | _          => false

/-- Whether an event is a `SeqCst` atomic operation or cross-thread fence. -/
noncomputable def isSeqCstKind : MemAccessKind → Bool
  | .atLoad o  => isSeqCstOrd o
  | .atStore o => isSeqCstOrd o
  | .atRmw o   => isSeqCstOrd o
  | .hwFence o => isSeqCstOrd o
  | _          => false

/-- One dynamic execution event in the C++20 / Rust axiomatic graph. -/
structure ExecEvent where
  thread : ThreadId
  loc    : LocId
  val    : Val
  kind   : MemAccessKind

/-- Axiomatic execution graph carrying `sb`, `rf`, `mo`, and `sc` relations. -/
structure ExecGraph where
  events : EventId → Option ExecEvent
  sb     : EventId → EventId → Prop
  rf     : EventId → EventId → Prop
  mo     : EventId → EventId → Prop
  sc     : EventId → EventId → Prop

/-- Well-formedness constraints on a C++20 / Rust execution graph. -/
structure ValidExecGraph (g : ExecGraph) : Prop where
  sb_same_thread : ∀ a b ea eb,
    g.sb a b → g.events a = some ea → g.events b = some eb → ea.thread = eb.thread
  rf_same_loc_val_atomic : ∀ w r ew er,
    g.rf w r → g.events w = some ew → g.events r = some er →
    ew.loc = er.loc ∧ ew.val = er.val ∧
    isWriteKind ew.kind = true ∧ isReadKind er.kind = true ∧
    isAtomicMemOp ew.kind = true ∧ isAtomicMemOp er.kind = true
  mo_atomic_write_same_loc : ∀ w1 w2 e1 e2,
    g.mo w1 w2 → g.events w1 = some e1 → g.events w2 = some e2 →
    e1.loc = e2.loc ∧ isWriteKind e1.kind = true ∧ isWriteKind e2.kind = true ∧
    isAtomicMemOp e1.kind = true ∧ isAtomicMemOp e2.kind = true
  sc_seqcst_only : ∀ a b ea eb,
    g.sc a b → g.events a = some ea → g.events b = some eb →
    isSeqCstKind ea.kind = true ∧ isSeqCstKind eb.kind = true

/-- C++20 / Rust synchronizes-with (`sw`) edge covering direct Release->Acquire `rf`
    as well as cross-thread `fence` synchronization (`[atomics.fences]`).
    Note: `compFence` NEVER induces `DirectSw`. -/
inductive DirectSw (g : ExecGraph) : EventId → EventId → Prop where
  | relAcq (w r : EventId) (ew er : ExecEvent) :
      g.events w = some ew →
      g.events r = some er →
      isReleaseWriteKind ew.kind = true →
      isAcquireReadKind er.kind = true →
      g.rf w r →
      DirectSw g w r
  | releaseFenceToAcqRead (f w r : EventId) (ef ew er : ExecEvent) :
      g.events f = some ef →
      g.events w = some ew →
      g.events r = some er →
      isReleaseHwFenceKind ef.kind = true →
      isWriteKind ew.kind = true →
      isAtomicMemOp ew.kind = true →
      isAcquireReadKind er.kind = true →
      g.sb f w →
      g.rf w r →
      DirectSw g f r
  | relWriteToAcquireFence (w r f : EventId) (ew er ef : ExecEvent) :
      g.events w = some ew →
      g.events r = some er →
      g.events f = some ef →
      isReleaseWriteKind ew.kind = true →
      isReadKind er.kind = true →
      isAtomicMemOp er.kind = true →
      isAcquireHwFenceKind ef.kind = true →
      g.rf w r →
      g.sb r f →
      DirectSw g w f
  | fenceToFence (f1 w r f2 : EventId) (ef1 ew er ef2 : ExecEvent) :
      g.events f1 = some ef1 →
      g.events w = some ew →
      g.events r = some er →
      g.events f2 = some ef2 →
      isReleaseHwFenceKind ef1.kind = true →
      isWriteKind ew.kind = true →
      isAtomicMemOp ew.kind = true →
      isReadKind er.kind = true →
      isAtomicMemOp er.kind = true →
      isAcquireHwFenceKind ef2.kind = true →
      g.sb f1 w →
      g.rf w r →
      g.sb r f2 →
      DirectSw g f1 f2

/-- Happens-before (`hb`): transitive closure of `sb ∪ DirectSw`. -/
inductive HappensBefore (g : ExecGraph) : EventId → EventId → Prop where
  | ofSb {a b : EventId} : g.sb a b → HappensBefore g a b
  | ofSw {a b : EventId} : DirectSw g a b → HappensBefore g a b
  | trans {a b c : EventId} :
      HappensBefore g a b → HappensBefore g b c → HappensBefore g a c

theorem hb_chain_sb_sw_sb {g : ExecGraph} {a b c d : EventId}
    (h1 : g.sb a b) (h2 : DirectSw g b c) (h3 : g.sb c d) :
    HappensBefore g a d :=
  HappensBefore.trans (HappensBefore.ofSb h1)
    (HappensBefore.trans (HappensBefore.ofSw h2) (HappensBefore.ofSb h3))

/-- Conflicting memory accesses (`intro.races`): same location, distinct events,
    at least one write, and at least one non-atomic access. -/
noncomputable def Conflicting (g : ExecGraph) (e1 e2 : EventId) : Prop :=
  ∃ ev1 ev2,
    g.events e1 = some ev1 ∧
    g.events e2 = some ev2 ∧
    e1 ≠ e2 ∧
    ev1.loc = ev2.loc ∧
    (isWriteKind ev1.kind = true ∨ isWriteKind ev2.kind = true) ∧
    (isNonAtomicKind ev1.kind = true ∨ isNonAtomicKind ev2.kind = true)

/-- Data race: conflicting accesses unordered by `HappensBefore`. -/
noncomputable def DataRace (g : ExecGraph) (e1 e2 : EventId) : Prop :=
  Conflicting g e1 e2 ∧ ¬ HappensBefore g e1 e2 ∧ ¬ HappensBefore g e2 e1

/-- Data-race-free execution graph. -/
noncomputable def DataRaceFree (g : ExecGraph) : Prop :=
  ∀ e1 e2, ¬ DataRace g e1 e2

theorem conflicting_symm {g : ExecGraph} {e1 e2 : EventId}
    (h : Conflicting g e1 e2) : Conflicting g e2 e1 := by
  rcases h with ⟨ev1, ev2, h1, h2, hne, hloc, hwr, hna⟩
  refine ⟨ev2, ev1, h2, h1, ?_, Eq.symm hloc, ?_, ?_⟩
  · intro heq; exact hne (Eq.symm heq)
  · cases hwr with
    | inl hw1 => exact Or.inr hw1
    | inr hw2 => exact Or.inl hw2
  · cases hna with
    | inl hn1 => exact Or.inr hn1
    | inr hn2 => exact Or.inl hn2

/-- **Theorem 1: Release-Acquire Message-Passing Data-Race-Freedom (`release_acquire_mp_drf`)**.
    For any graph where `e0` (non-atomic write) is `sb`-before `e1` (Release/SeqCst atomic store),
    `e1` is `rf`-read by `e2` (Acquire/SeqCst atomic load), and `e2` is `sb`-before `e3`
    (non-atomic read), `HappensBefore g e0 e3` holds; and if all conflicting pairs on any
    location are either ordered by `hb` or equal to `(e0, e3)` / `(e3, e0)`, then `DataRaceFree g`. -/
theorem release_acquire_mp_drf
    (g : ExecGraph) (e0 e1 e2 e3 : EventId)
    (ev0 ev1 ev2 ev3 : ExecEvent)
    (he0 : g.events e0 = some ev0)
    (he1 : g.events e1 = some ev1)
    (he2 : g.events e2 = some ev2)
    (he3 : g.events e3 = some ev3)
    (hrel : isReleaseWriteKind ev1.kind = true)
    (hacq : isAcquireReadKind ev2.kind = true)
    (hsb01 : g.sb e0 e1)
    (hrf12 : g.rf e1 e2)
    (hsb23 : g.sb e2 e3)
    (h_other_ordered : ∀ a b, Conflicting g a b →
      (a = e0 ∧ b = e3) ∨ (a = e3 ∧ b = e0) ∨
      HappensBefore g a b ∨ HappensBefore g b a) :
    HappensBefore g e0 e3 ∧ DataRaceFree g := by
  have hsw : DirectSw g e1 e2 := DirectSw.relAcq e1 e2 ev1 ev2 he1 he2 hrel hacq hrf12
  have hhb : HappensBefore g e0 e3 := hb_chain_sb_sw_sb hsb01 hsw hsb23
  refine ⟨hhb, ?_⟩
  intro a b hrace
  rcases hrace with ⟨hconf, hna, hnb⟩
  rcases h_other_ordered a b hconf with ⟨ha, hb⟩ | ⟨ha, hb⟩ | h1 | h2
  · subst ha; subst hb; exact hna hhb
  · subst ha; subst hb; exact hnb hhb
  · exact hna h1
  · exact hnb h2

/-- **Theorem 1b: Fence-Mediated Release-Acquire MP DRF (`fence_release_acquire_mp_drf`)**.
    `e0 -[sb]-> f1 (hwFence Release) -[sb]-> s (atStore Relaxed) -[rf]-> l (atLoad Relaxed)
    -[sb]-> f2 (hwFence Acquire) -[sb]-> e3` establishes `DirectSw g f1 f2`,
    `HappensBefore g e0 e3`, and `DataRaceFree g`. -/
theorem fence_release_acquire_mp_drf
    (g : ExecGraph) (e0 f1 s l f2 e3 : EventId)
    (ev0 ef1 es el ef2 ev3 : ExecEvent)
    (he0 : g.events e0 = some ev0)
    (hf1 : g.events f1 = some ef1)
    (hs  : g.events s  = some es)
    (hl  : g.events l  = some el)
    (hf2 : g.events f2 = some ef2)
    (he3 : g.events e3 = some ev3)
    (hf1_rel : isReleaseHwFenceKind ef1.kind = true)
    (hs_wr   : isWriteKind es.kind = true)
    (hs_at   : isAtomicMemOp es.kind = true)
    (hl_rd   : isReadKind el.kind = true)
    (hl_at   : isAtomicMemOp el.kind = true)
    (hf2_acq : isAcquireHwFenceKind ef2.kind = true)
    (hsb0f1 : g.sb e0 f1)
    (hsbf1s : g.sb f1 s)
    (hrfsl  : g.rf s l)
    (hsblf2 : g.sb l f2)
    (hsbf23 : g.sb f2 e3)
    (h_other_ordered : ∀ a b, Conflicting g a b →
      (a = e0 ∧ b = e3) ∨ (a = e3 ∧ b = e0) ∨
      HappensBefore g a b ∨ HappensBefore g b a) :
    DirectSw g f1 f2 ∧ HappensBefore g e0 e3 ∧ DataRaceFree g := by
  have hsw : DirectSw g f1 f2 :=
    DirectSw.fenceToFence f1 s l f2 ef1 es el ef2 hf1 hs hl hf2
      hf1_rel hs_wr hs_at hl_rd hl_at hf2_acq hsbf1s hrfsl hsblf2
  have hhb : HappensBefore g e0 e3 := hb_chain_sb_sw_sb hsb0f1 hsw hsbf23
  refine ⟨hsw, hhb, ?_⟩
  intro a b hrace
  rcases hrace with ⟨hconf, hna, hnb⟩
  rcases h_other_ordered a b hconf with ⟨ha, hb⟩ | ⟨ha, hb⟩ | h1 | h2
  · subst ha; subst hb; exact hna hhb
  · subst ha; subst hb; exact hnb hhb
  · exact hna h1
  · exact hnb h2

/-- Concrete 4-event Relaxed Message-Passing graph (Thread 0: NA write x=42, Relaxed flag=1;
    Thread 1: Relaxed flag load == 1, NA read x). -/
noncomputable def relaxedMpEvents : EventId → Option ExecEvent
  | 0 => some { thread := 0, loc := 0, val := 42, kind := .naWrite }
  | 1 => some { thread := 0, loc := 1, val := 1,  kind := .atStore .relaxed }
  | 2 => some { thread := 1, loc := 1, val := 1,  kind := .atLoad .relaxed }
  | 3 => some { thread := 1, loc := 0, val := 42, kind := .naRead }
  | _ => none

noncomputable def relaxedMpSb : EventId → EventId → Prop
  | 0, 1 => True
  | 2, 3 => True
  | _, _ => False

noncomputable def relaxedMpRf : EventId → EventId → Prop
  | 1, 2 => True
  | _, _ => False

noncomputable def relaxedMpGraph : ExecGraph :=
  { events := relaxedMpEvents
    sb := relaxedMpSb
    rf := relaxedMpRf
    mo := fun _ _ => False
    sc := fun _ _ => False }

theorem relaxedMpGraph_valid : ValidExecGraph relaxedMpGraph := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b ea eb hsb hea heb
    cases a with
    | zero =>
      cases b with
      | zero => cases hsb
      | succ b1 =>
        cases b1 with
        | zero => cases hea; cases heb; rfl
        | succ _ => cases hsb
    | succ a1 =>
      cases a1 with
      | zero => cases hsb
      | succ a2 =>
        cases a2 with
        | zero =>
          cases b with
          | zero => cases hsb
          | succ b1 =>
            cases b1 with
            | zero => cases hsb
            | succ b2 =>
              cases b2 with
              | zero => cases hsb
              | succ b3 =>
                cases b3 with
                | zero => cases hea; cases heb; rfl
                | succ _ => cases hsb
        | succ _ => cases hsb
  · intro w r ew er hrf hew her
    cases w with
    | zero => cases hrf
    | succ w1 =>
      cases w1 with
      | zero =>
        cases r with
        | zero => cases hrf
        | succ r1 =>
          cases r1 with
          | zero => cases hrf
          | succ r2 =>
            cases r2 with
            | zero => cases hew; cases her; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
            | succ _ => cases hrf
      | succ _ => cases hrf
  · intro w1 w2 e1 e2 hmo _ _
    cases hmo
  · intro a b ea eb hsc _ _
    cases hsc

theorem no_sw_of_no_rel_acq (g : ExecGraph)
    (h_no_hw : ∀ i ev, g.events i = some ev →
      isReleaseHwFenceKind ev.kind = false ∧ isAcquireHwFenceKind ev.kind = false)
    (h_no_rf : ∀ w r ew er, g.rf w r → g.events w = some ew → g.events r = some er →
      isReleaseWriteKind ew.kind = false ∨ isAcquireReadKind er.kind = false) :
    ∀ (a b : EventId), ¬ DirectSw g a b
  | _, _, .relAcq w r ew er hw hr hrel hacq hrf => by
    rcases h_no_rf w r ew er hrf hw hr with h | h
    · rw [h] at hrel; cases hrel
    · rw [h] at hacq; cases hacq
  | _, _, .releaseFenceToAcqRead f _ _ ef _ _ hf _ _ hrel _ _ _ _ _ => by
    have hbad := (h_no_hw f ef hf).1
    rw [hbad] at hrel; cases hrel
  | _, _, .relWriteToAcquireFence _ _ f _ _ ef _ _ hf _ _ _ hacq _ _ => by
    have hbad := (h_no_hw f ef hf).2
    rw [hbad] at hacq; cases hacq
  | _, _, .fenceToFence f1 _ _ _ ef1 _ _ _ hf1 _ _ _ hrel _ _ _ _ _ _ _ _ => by
    have hbad := (h_no_hw f1 ef1 hf1).1
    rw [hbad] at hrel; cases hrel

theorem hb_in_rel_if_no_sw (g : ExecGraph) (R : EventId → EventId → Prop)
    (h_sb : ∀ a b, g.sb a b → R a b)
    (h_no_sw : ∀ a b, ¬ DirectSw g a b)
    (h_trans : ∀ a b c, R a b → R b c → R a c)
    {a b : EventId} (h : HappensBefore g a b) : R a b := by
  induction h with
  | ofSb hsb => exact h_sb _ _ hsb
  | ofSw hsw => exact False.elim (h_no_sw _ _ hsw)
  | trans _ _ ih1 ih2 => exact h_trans _ _ _ ih1 ih2

theorem relaxedMpGraph_no_sw (a b : EventId) : ¬ DirectSw relaxedMpGraph a b := by
  refine no_sw_of_no_rel_acq relaxedMpGraph ?_ ?_ a b
  · intro i ev hi
    cases i with
    | zero => cases hi; exact ⟨rfl, rfl⟩
    | succ i1 =>
      cases i1 with
      | zero => cases hi; exact ⟨rfl, rfl⟩
      | succ i2 =>
        cases i2 with
        | zero => cases hi; exact ⟨rfl, rfl⟩
        | succ i3 =>
          cases i3 with
          | zero => cases hi; exact ⟨rfl, rfl⟩
          | succ _ => cases hi
  · intro w r ew er hrf hw hr
    cases w with
    | zero => cases hrf
    | succ w1 =>
      cases w1 with
      | zero =>
        cases r with
        | zero => cases hrf
        | succ r1 =>
          cases r1 with
          | zero => cases hrf
          | succ r2 =>
            cases r2 with
            | zero => cases hw; cases hr; exact Or.inl rfl
            | succ _ => cases hrf
      | succ _ => cases hrf

theorem relaxedMpSb_elim {a b : EventId} (h : relaxedMpSb a b) :
    (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3) := by
  cases a with
  | zero =>
    cases b with
    | zero => cases h
    | succ b1 =>
      cases b1 with
      | zero => exact Or.inl ⟨rfl, rfl⟩
      | succ _ => cases h
  | succ a1 =>
    cases a1 with
    | zero => cases h
    | succ a2 =>
      cases a2 with
      | zero =>
        cases b with
        | zero => cases h
        | succ b1 =>
          cases b1 with
          | zero => cases h
          | succ b2 =>
            cases b2 with
            | zero => cases h
            | succ b3 =>
              cases b3 with
              | zero => exact Or.inr ⟨rfl, rfl⟩
              | succ _ => cases h
      | succ _ => cases h

theorem relaxedMp_hb_implies_sb {a b : EventId}
    (h : HappensBefore relaxedMpGraph a b) : relaxedMpSb a b := by
  refine hb_in_rel_if_no_sw relaxedMpGraph relaxedMpSb (fun _ _ hs => hs) relaxedMpGraph_no_sw ?_ h
  intro x y z h1 h2
  rcases relaxedMpSb_elim h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases relaxedMpSb_elim h2 with ⟨hbad, _⟩ | ⟨hbad, _⟩ <;>
    cases hbad

/-- **Theorem 2: Relaxed Message-Passing Data-Race Witness (`relaxed_mp_data_race_witness`)**.
    Events `0` (`naWrite` to loc `0`) and `3` (`naRead` from loc `0`) form an
    unsynchronized `DataRace` in `relaxedMpGraph` even though `rf 1 2` holds. -/
theorem relaxed_mp_data_race_witness :
    relaxedMpGraph.rf 1 2 ∧
    ¬ HappensBefore relaxedMpGraph 0 3 ∧
    ¬ HappensBefore relaxedMpGraph 3 0 ∧
    DataRace relaxedMpGraph 0 3 := by
  have hrf : relaxedMpGraph.rf 1 2 := trivial
  have h03 : ¬ HappensBefore relaxedMpGraph 0 3 := by
    intro h
    have hsb := relaxedMp_hb_implies_sb h
    cases hsb
  have h30 : ¬ HappensBefore relaxedMpGraph 3 0 := by
    intro h
    have hsb := relaxedMp_hb_implies_sb h
    cases hsb
  have hconf : Conflicting relaxedMpGraph 0 3 := by
    refine ⟨{ thread := 0, loc := 0, val := 42, kind := .naWrite },
            { thread := 1, loc := 0, val := 42, kind := .naRead },
            rfl, rfl, ?_, rfl, Or.inl rfl, Or.inl rfl⟩
    intro heq
    cases heq
  exact ⟨hrf, h03, h30, hconf, h03, h30⟩

/-! ## Section 4: Miri Vector-Clock Detector Soundness Correspondence -/

/-- Two-thread Lamport vector clock matching `src/tools/miri/src/concurrency/vector_clock.rs`. -/
structure VClock2 where
  c0 : Nat
  c1 : Nat

noncomputable def vclockLe (a b : VClock2) : Prop :=
  a.c0 ≤ b.c0 ∧ a.c1 ≤ b.c1

noncomputable def vclockJoin (a b : VClock2) : VClock2 :=
  { c0 := Nat.max a.c0 b.c0, c1 := Nat.max a.c1 b.c1 }

theorem vclockLe_refl (a : VClock2) : vclockLe a a :=
  ⟨Nat.le_refl a.c0, Nat.le_refl a.c1⟩

theorem vclockLe_trans {a b c : VClock2} (h1 : vclockLe a b) (h2 : vclockLe b c) :
    vclockLe a c :=
  ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2 h2.2⟩

theorem vclockJoin_le_left (a b : VClock2) : vclockLe a (vclockJoin a b) :=
  ⟨Nat.le_max_left a.c0 b.c0, Nat.le_max_left a.c1 b.c1⟩

theorem vclockJoin_le_right (a b : VClock2) : vclockLe b (vclockJoin a b) :=
  ⟨Nat.le_max_right a.c0 b.c0, Nat.le_max_right a.c1 b.c1⟩

/-- Per-thread vector-clock set matching `ThreadClockSet` in `data_race.rs`. -/
structure MiriThreadClocks where
  clock : VClock2
  fenceAcquire : VClock2
  fenceRelease : VClock2

/-- Per-location clock state matching `MemoryCellClocks` in `data_race.rs`. -/
structure MiriCellClocks where
  naWrite : VClock2
  naRead  : VClock2
  atomicSync  : VClock2
  atomicWrite : VClock2
  atomicRead  : VClock2

/-- Increment thread 0 or thread 1 coordinate (`increment_clock`). -/
noncomputable def miriIncThread (t : Bool) (c : VClock2) : VClock2 :=
  match t with
  | false => { c with c0 := Nat.succ c.c0 }
  | true  => { c with c1 := Nat.succ c.c1 }

/-- `non_atomic_write_detect` precondition check (`data_race.rs:728-733`). -/
noncomputable def miriCanNaWrite (tc : MiriThreadClocks) (cell : MiriCellClocks) : Prop :=
  vclockLe cell.naWrite tc.clock ∧
  vclockLe cell.naRead tc.clock ∧
  vclockLe cell.atomicWrite tc.clock ∧
  vclockLe cell.atomicRead tc.clock

/-- `non_atomic_read_detect` precondition check (`data_race.rs:702-708`). -/
noncomputable def miriCanNaRead (tc : MiriThreadClocks) (cell : MiriCellClocks) : Prop :=
  vclockLe cell.naWrite tc.clock ∧
  vclockLe cell.atomicWrite tc.clock

/-- `store_release` vs. `store_relaxed` cell sync update (`data_race.rs:589-619`). -/
noncomputable def miriAtomicStoreSync (ord : RustOrdering) (tc : MiriThreadClocks)
    (cell : MiriCellClocks) : MiriCellClocks :=
  match hasReleaseSem ord with
  | true  => { cell with atomicSync := tc.clock }
  | false => { cell with atomicSync := tc.fenceRelease }

/-- `load_acquire` vs. `load_relaxed` thread clock update (`data_race.rs:556-585`). -/
noncomputable def miriAtomicLoadSync (ord : RustOrdering) (tc : MiriThreadClocks)
    (cell : MiriCellClocks) : MiriThreadClocks :=
  match hasAcquireSem ord with
  | true  => { tc with clock := vclockJoin tc.clock cell.atomicSync }
  | false => { tc with fenceAcquire := vclockJoin tc.fenceAcquire cell.atomicSync }

/-- `atomic_fence` (`data_race.rs:1843-1884`); `compiler_fence` is a NOP (`machine.rs:1414`). -/
noncomputable def miriApplyFence (isCompilerFence : Bool) (ord : RustOrdering)
    (tc : MiriThreadClocks) : MiriThreadClocks :=
  match isCompilerFence with
  | true => tc
  | false =>
    let tc1 := match hasAcquireSem ord with
      | true  => { tc with clock := vclockJoin tc.clock tc.fenceAcquire }
      | false => tc
    match hasReleaseSem ord with
    | true  => { tc1 with fenceRelease := tc1.clock }
    | false => tc1

theorem miri_rel_acq_sync_passes_clocks
    (tc0_init tc1_init : MiriThreadClocks)
    (data_cell0 flag_cell0 : MiriCellClocks)
    (_h_na_ok : miriCanNaWrite tc0_init data_cell0)
    (h_no_at_data : vclockLe data_cell0.atomicWrite tc1_init.clock) :
    let data_cell1 := { data_cell0 with naWrite := tc0_init.clock }
    let flag_cell1 := miriAtomicStoreSync .release tc0_init flag_cell0
    let tc1_after  := miriAtomicLoadSync .acquire tc1_init flag_cell1
    miriCanNaRead tc1_after data_cell1 := by
  dsimp only [miriAtomicStoreSync, miriAtomicLoadSync, hasReleaseSem, hasAcquireSem, miriCanNaRead]
  refine ⟨vclockJoin_le_right tc1_init.clock tc0_init.clock, ?_⟩
  exact vclockLe_trans h_no_at_data (vclockJoin_le_left tc1_init.clock tc0_init.clock)

theorem miri_fence_rel_acq_sync_passes_clocks
    (tc0_init tc1_init : MiriThreadClocks)
    (data_cell0 flag_cell0 : MiriCellClocks)
    (h_no_at_data : vclockLe data_cell0.atomicWrite tc1_init.clock) :
    let data_cell1 := { data_cell0 with naWrite := tc0_init.clock }
    let tc0_fenced := miriApplyFence false .release tc0_init
    let flag_cell1 := miriAtomicStoreSync .relaxed tc0_fenced flag_cell0
    let tc1_loaded := miriAtomicLoadSync .relaxed tc1_init flag_cell1
    let tc1_fenced := miriApplyFence false .acquire tc1_loaded
    miriCanNaRead tc1_fenced data_cell1 := by
  dsimp only [miriApplyFence, miriAtomicStoreSync, miriAtomicLoadSync,
              hasReleaseSem, hasAcquireSem, miriCanNaRead]
  refine ⟨?_, ?_⟩
  · have h1 : vclockLe tc0_init.clock (vclockJoin tc1_init.fenceAcquire tc0_init.clock) :=
      vclockJoin_le_right tc1_init.fenceAcquire tc0_init.clock
    have h2 : vclockLe (vclockJoin tc1_init.fenceAcquire tc0_init.clock)
        (vclockJoin tc1_init.clock (vclockJoin tc1_init.fenceAcquire tc0_init.clock)) :=
      vclockJoin_le_right tc1_init.clock (vclockJoin tc1_init.fenceAcquire tc0_init.clock)
    exact vclockLe_trans h1 h2
  · exact vclockLe_trans h_no_at_data
      (vclockJoin_le_left tc1_init.clock (vclockJoin tc1_init.fenceAcquire tc0_init.clock))

theorem miri_relaxed_and_cfence_fail_race_check :
    let tc0 : MiriThreadClocks :=
      { clock := { c0 := 1, c1 := 0 }, fenceAcquire := { c0 := 0, c1 := 0 }, fenceRelease := { c0 := 0, c1 := 0 } }
    let tc1 : MiriThreadClocks :=
      { clock := { c0 := 0, c1 := 1 }, fenceAcquire := { c0 := 0, c1 := 0 }, fenceRelease := { c0 := 0, c1 := 0 } }
    let zeroCell : MiriCellClocks :=
      { naWrite := { c0 := 0, c1 := 0 }, naRead := { c0 := 0, c1 := 0 },
        atomicSync := { c0 := 0, c1 := 0 }, atomicWrite := { c0 := 0, c1 := 0 }, atomicRead := { c0 := 0, c1 := 0 } }
    let dataCell := { zeroCell with naWrite := tc0.clock }
    let tc0_cf := miriApplyFence true .seqCst tc0
    let flagCell := miriAtomicStoreSync .relaxed tc0_cf zeroCell
    let tc1_ld := miriAtomicLoadSync .relaxed tc1 flagCell
    let tc1_cf := miriApplyFence true .seqCst tc1_ld
    ¬ miriCanNaRead tc1_cf dataCell := by
  dsimp only [miriApplyFence, miriAtomicStoreSync, miriAtomicLoadSync,
              hasReleaseSem, hasAcquireSem, miriCanNaRead, vclockLe]
  intro h
  cases h.1.1

/-! ## Section 5: x86-TSO Store-Buffer Machine & Lowering Soundness -/

/-- Memory locations used in canonical MP and SB litmus machines. -/
inductive TsoLoc where
  | loc0
  | loc1

noncomputable def tsoLocEq : TsoLoc → TsoLoc → Bool
  | .loc0, .loc0 => true
  | .loc1, .loc1 => true
  | _,     _     => false

/-- Mem state over two locations (`loc0` = `x`/`data`, `loc1` = `y`/`flag`). -/
structure TsoMem where
  v0 : Nat
  v1 : Nat

noncomputable def readMem (m : TsoMem) : TsoLoc → Nat
  | .loc0 => m.v0
  | .loc1 => m.v1

noncomputable def writeMem (m : TsoMem) (l : TsoLoc) (v : Nat) : TsoMem :=
  match l with
  | .loc0 => { m with v0 := v }
  | .loc1 => { m with v1 := v }

/-- Per-thread FIFO store buffer entry. -/
structure BufEntry where
  loc : TsoLoc
  val : Nat

/-- Store-buffer forwarding lookup: newest matching write in the FIFO buffer wins,
    otherwise reads coherent shared memory `m`. Note `buf` stores oldest at head,
    newest at tail, so forwarding scans from the tail (`foldl`). -/
noncomputable def readWithBuffer (buf : List BufEntry) (m : TsoMem) (l : TsoLoc) : Nat :=
  buf.foldl (fun acc e => match tsoLocEq e.loc l with | true => e.val | false => acc) (readMem m l)

theorem readWithBuffer_nil (m : TsoMem) (l : TsoLoc) :
    readWithBuffer [] m l = readMem m l := rfl

theorem readWithBuffer_snoc_match (buf : List BufEntry) (m : TsoMem) (l : TsoLoc) (v : Nat) :
    readWithBuffer (buf ++ [{ loc := l, val := v }]) m l = v := by
  dsimp only [readWithBuffer]
  rw [List.foldl_append]
  dsimp only [List.foldl]
  cases l <;> rfl

theorem readWithBuffer_snoc_other (buf : List BufEntry) (m : TsoMem) (l1 l2 : TsoLoc) (v : Nat)
    (hne : tsoLocEq l1 l2 = false) :
    readWithBuffer (buf ++ [{ loc := l1, val := v }]) m l2 = readWithBuffer buf m l2 := by
  dsimp only [readWithBuffer]
  rw [List.foldl_append]
  dsimp only [List.foldl]
  rw [hne]

/-- Helper: check if an entry with `(loc, val)` appears in a buffer. -/
noncomputable def inBuf (l : TsoLoc) (v : Nat) : List BufEntry → Prop
  | [] => False
  | e :: es => (e.loc = l ∧ e.val = v) ∨ inBuf l v es

/-- Helper: if `(loc0, 42)` precedes `(loc1, 1)` in `buf` (or `mem.v0 = 42`). -/
noncomputable def precedesInBuf : List BufEntry → Prop
  | [] => False
  | e :: es =>
      (e.loc = .loc0 ∧ e.val = 42) ∨
      (e.loc ≠ .loc1 ∧ precedesInBuf es)

/-! ### 5A. Release-Acquire Message Passing on x86-TSO (`movStore` + `movLoad`) -/

/-- State of the 2-thread MP program on x86-TSO:
    Thread 0: `pc0=0 -> movStore loc0 42 -> pc0=1 -> movStore loc1 1 -> pc0=2`
    Thread 1: `pc1=0 -> movLoad loc1 -> rFlag (if 1 -> pc1=1) -> movLoad loc0 -> rData (pc1=2)` -/
structure TsoMpState where
  mem   : TsoMem
  buf0  : List BufEntry
  buf1  : List BufEntry
  pc0   : Nat
  pc1   : Nat
  rFlag : Nat
  rData : Nat

noncomputable def tsoMpInit : TsoMpState :=
  { mem := { v0 := 0, v1 := 0 }, buf0 := [], buf1 := [], pc0 := 0, pc1 := 0, rFlag := 0, rData := 0 }

/-- Small-step TSO operational semantics for Release-Acquire MP using plain `movStore`/`movLoad`. -/
inductive TsoMpStep : TsoMpState → TsoMpState → Prop where
  | t0WriteData (s : TsoMpState) :
      s.pc0 = 0 →
      TsoMpStep s { s with buf0 := s.buf0 ++ [{ loc := .loc0, val := 42 }], pc0 := 1 }
  | t0WriteFlag (s : TsoMpState) :
      s.pc0 = 1 →
      TsoMpStep s { s with buf0 := s.buf0 ++ [{ loc := .loc1, val := 1 }], pc0 := 2 }
  | t0Drain (s : TsoMpState) (e : BufEntry) (rest : List BufEntry) :
      s.buf0 = e :: rest →
      TsoMpStep s { s with mem := writeMem s.mem e.loc e.val, buf0 := rest }
  | t1PollFlag (s : TsoMpState) :
      s.pc1 = 0 →
      TsoMpStep s
        { s with
          rFlag := readWithBuffer s.buf1 s.mem .loc1,
          pc1 := match readWithBuffer s.buf1 s.mem .loc1 with | 1 => 1 | _ => 0 }
  | t1ReadData (s : TsoMpState) :
      s.pc1 = 1 →
      TsoMpStep s { s with rData := readWithBuffer s.buf1 s.mem .loc0, pc1 := 2 }
  | t1Drain (s : TsoMpState) (e : BufEntry) (rest : List BufEntry) :
      s.buf1 = e :: rest →
      TsoMpStep s { s with mem := writeMem s.mem e.loc e.val, buf1 := rest }

inductive TsoMpReach : TsoMpState → Prop where
  | init : TsoMpReach tsoMpInit
  | step {s s' : TsoMpState} : TsoMpReach s → TsoMpStep s s' → TsoMpReach s'

/-- Inductive invariant proving FIFO store-buffer drainage makes `movStore`/`movLoad` sound for MP. -/
noncomputable def TsoMpInv (s : TsoMpState) : Prop :=
  s.buf1 = [] ∧
  (s.pc0 = 0 → s.buf0 = [] ∧ s.mem.v0 = 0 ∧ s.mem.v1 = 0) ∧
  (s.pc0 = 1 → s.mem.v1 = 0 ∧
    ((s.buf0 = [{ loc := .loc0, val := 42 }] ∧ s.mem.v0 = 0) ∨
     (s.buf0 = [] ∧ s.mem.v0 = 42))) ∧
  (s.pc0 = 2 →
    ((s.buf0 = [{ loc := .loc0, val := 42 }, { loc := .loc1, val := 1 }] ∧ s.mem.v0 = 0 ∧ s.mem.v1 = 0) ∨
     (s.buf0 = [{ loc := .loc1, val := 1 }] ∧ s.mem.v0 = 42 ∧ s.mem.v1 = 0) ∨
     (s.buf0 = [] ∧ s.mem.v0 = 42 ∧ s.mem.v1 = 1))) ∧
  (s.pc0 = 0 ∨ s.pc0 = 1 ∨ s.pc0 = 2) ∧
  (s.pc1 = 1 → s.mem.v1 = 1 ∧ s.mem.v0 = 42) ∧
  (s.pc1 = 2 → s.rData = 42)

theorem tsoMpInv_init : TsoMpInv tsoMpInit := by
  refine ⟨rfl, ?_, ?_, ?_, Or.inl rfl, ?_, ?_⟩
  · intro _; exact ⟨rfl, rfl, rfl⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

theorem tsoMpInv_step {s s' : TsoMpState} (hi : TsoMpInv s) (hst : TsoMpStep s s') :
    TsoMpInv s' := by
  rcases hi with ⟨hb1, h0, h1, h2, hpc0, hpc1_1, hpc1_2⟩
  cases hst with
  | t0WriteData hpc =>
    obtain ⟨hb0, hm0, hm1⟩ := h0 hpc
    refine ⟨hb1, ?_, ?_, ?_, Or.inr (Or.inl rfl), hpc1_1, hpc1_2⟩
    · intro hx; cases hx
    · intro _; refine ⟨hm1, Or.inl ⟨?_, hm0⟩⟩; rw [hb0]; rfl
    · intro hx; cases hx
  | t0WriteFlag hpc =>
    obtain ⟨hm1, hcases⟩ := h1 hpc
    refine ⟨hb1, ?_, ?_, ?_, Or.inr (Or.inr rfl), hpc1_1, hpc1_2⟩
    · intro hx; cases hx
    · intro hx; cases hx
    · intro _
      rcases hcases with ⟨hb0, hm0⟩ | ⟨hb0, hm0⟩
      · left; refine ⟨?_, hm0, hm1⟩; rw [hb0]; rfl
      · right; left; refine ⟨?_, hm0, hm1⟩; rw [hb0]; rfl
  | t0Drain e rest hbuf =>
    rcases hpc0 with hp | hp | hp
    · obtain ⟨hb0, _, _⟩ := h0 hp; rw [hb0] at hbuf; cases hbuf
    · obtain ⟨hm1, hcases⟩ := h1 hp
      rcases hcases with ⟨hb0, _⟩ | ⟨hb0, _⟩
      · rw [hb0] at hbuf; cases hbuf
        refine ⟨hb1, ?_, ?_, ?_, Or.inr (Or.inl hp), ?_, hpc1_2⟩
        · intro hx; rw [hp] at hx; cases hx
        · intro _; exact ⟨hm1, Or.inr ⟨rfl, rfl⟩⟩
        · intro hx; rw [hp] at hx; cases hx
        · intro hpc1
          exfalso
          have hv := hpc1_1 hpc1
          rw [hm1] at hv
          cases hv.1
      · rw [hb0] at hbuf; cases hbuf
    · rcases h2 hp with ⟨hb0, hm0, hm1⟩ | ⟨hb0, hm0, hm1⟩ | ⟨hb0, hm0, hm1⟩
      · rw [hb0] at hbuf; cases hbuf
        refine ⟨hb1, ?_, ?_, ?_, Or.inr (Or.inr hp), ?_, hpc1_2⟩
        · intro hx; rw [hp] at hx; cases hx
        · intro hx; rw [hp] at hx; cases hx
        · intro _; right; left; exact ⟨rfl, rfl, hm1⟩
        · intro hpc1
          exfalso
          have hv := hpc1_1 hpc1
          rw [hm1] at hv
          cases hv.1
      · rw [hb0] at hbuf; cases hbuf
        refine ⟨hb1, ?_, ?_, ?_, Or.inr (Or.inr hp), ?_, hpc1_2⟩
        · intro hx; rw [hp] at hx; cases hx
        · intro hx; rw [hp] at hx; cases hx
        · intro _; right; right; exact ⟨rfl, hm0, rfl⟩
        · intro hpc1
          exfalso
          have hv := hpc1_1 hpc1
          rw [hm1] at hv
          cases hv.1
      · rw [hb0] at hbuf; cases hbuf
  | t1PollFlag hpc =>
    rw [hb1, readWithBuffer_nil]
    dsimp only [readMem]
    have hm1_implies_m0 : s.mem.v1 = 1 → s.mem.v0 = 42 := by
      intro hv1
      rcases hpc0 with hp | hp | hp
      · obtain ⟨_, _, hm1⟩ := h0 hp; rw [hm1] at hv1; cases hv1
      · obtain ⟨hm1, _⟩ := h1 hp; rw [hm1] at hv1; cases hv1
      · rcases h2 hp with ⟨_, _, hm1⟩ | ⟨_, _, hm1⟩ | ⟨_, hm0, _⟩
        · rw [hm1] at hv1; cases hv1
        · rw [hm1] at hv1; cases hv1
        · exact hm0
    refine ⟨rfl, h0, h1, h2, hpc0, ?_, ?_⟩
    · intro hpc1'
      cases hv : s.mem.v1 with
      | zero => rw [hv] at hpc1'; cases hpc1'
      | succ n =>
        cases n with
        | zero => exact ⟨rfl, hm1_implies_m0 hv⟩
        | succ _ => rw [hv] at hpc1'; cases hpc1'
    · intro hx
      cases hv : s.mem.v1 with
      | zero => rw [hv] at hx; cases hx
      | succ n =>
        cases n with
        | zero => rw [hv] at hx; cases hx
        | succ _ => rw [hv] at hx; cases hx
  | t1ReadData hpc =>
    rw [hb1, readWithBuffer_nil]
    dsimp only [readMem]
    obtain ⟨_, hm0⟩ := hpc1_1 hpc
    refine ⟨rfl, h0, h1, h2, hpc0, ?_, ?_⟩
    · intro hx; cases hx
    · intro _; exact hm0
  | t1Drain e rest hbuf =>
    rw [hb1] at hbuf; cases hbuf

theorem tsoMpInv_of_reach {s : TsoMpState} (hr : TsoMpReach s) : TsoMpInv s := by
  induction hr with
  | init => exact tsoMpInv_init
  | step _ hst ih => exact tsoMpInv_step ih hst

/-- **Theorem 3a: x86-TSO `movStore`/`movLoad` Soundness for Release-Acquire MP (`tso_mov_preserves_rel_acq_mp`)**.
    Whenever Thread 1 exits the spin loop and reads the data payload (`pc1 = 2`),
    the observed data equals `42` across ALL reachable TSO schedules. -/
theorem tso_mov_preserves_rel_acq_mp {s : TsoMpState} (hr : TsoMpReach s) (hdone : s.pc1 = 2) :
    s.rData = 42 :=
  (tsoMpInv_of_reach hr).2.2.2.2.2.2 hdone

/-! ### 5B. Store-Buffering (SB): Weak Outcome Under `movStore` vs. Soundness Under `xchg`/`lock orl` -/

/-- State of the 2-thread Store-Buffering (SB) litmus program on x86-TSO:
    Thread 0: store `loc0 := 1`, (optional fence), load `loc1 -> r0`
    Thread 1: store `loc1 := 1`, (optional fence), load `loc0 -> r1` -/
structure TsoSbState where
  mem  : TsoMem
  buf0 : List BufEntry
  buf1 : List BufEntry
  pc0  : Nat
  pc1  : Nat
  r0   : Nat
  r1   : Nat

noncomputable def tsoSbInit : TsoSbState :=
  { mem := { v0 := 0, v1 := 0 }, buf0 := [], buf1 := [], pc0 := 0, pc1 := 0, r0 := 0, r1 := 0 }

/-- Lowering mode for SB litmus execution:
    - `relaxedOrReleaseMov`: stores lower to `movStore`, no CPU fence (`pc=0` store, `pc=1` load)
    - `seqCstXchg`: stores lower to `xchgMem` (atomic commit + drained buffer)
    - `movWithSeqCstFence`: `movStore` followed by `lockOrlStack` fence before `movLoad` -/
inductive SbLowerMode where
  | relaxedOrReleaseMov
  | seqCstXchg
  | movWithSeqCstFence

/-- Parameterized x86-TSO small-step relation for the SB litmus program. -/
inductive TsoSbStep (mode : SbLowerMode) : TsoSbState → TsoSbState → Prop where
  | t0MovStore (s : TsoSbState) :
      (mode = .relaxedOrReleaseMov ∨ mode = .movWithSeqCstFence) →
      s.pc0 = 0 →
      TsoSbStep mode s { s with buf0 := s.buf0 ++ [{ loc := .loc0, val := 1 }], pc0 := 1 }
  | t0XchgStore (s : TsoSbState) :
      mode = .seqCstXchg →
      s.pc0 = 0 →
      s.buf0 = [] →
      TsoSbStep mode s { s with mem := writeMem s.mem .loc0 1, pc0 := 1 }
  | t0SeqCstFence (s : TsoSbState) :
      mode = .movWithSeqCstFence →
      s.pc0 = 1 →
      s.buf0 = [] →
      TsoSbStep mode s { s with pc0 := 2 }
  | t0MovLoad (s : TsoSbState) :
      ((mode = .relaxedOrReleaseMov ∧ s.pc0 = 1) ∨
       (mode = .seqCstXchg ∧ s.pc0 = 1) ∨
       (mode = .movWithSeqCstFence ∧ s.pc0 = 2)) →
      TsoSbStep mode s
        { s with r0 := readWithBuffer s.buf0 s.mem .loc1,
                 pc0 := match mode with | .movWithSeqCstFence => 3 | _ => 2 }
  | t1MovStore (s : TsoSbState) :
      (mode = .relaxedOrReleaseMov ∨ mode = .movWithSeqCstFence) →
      s.pc1 = 0 →
      TsoSbStep mode s { s with buf1 := s.buf1 ++ [{ loc := .loc1, val := 1 }], pc1 := 1 }
  | t1XchgStore (s : TsoSbState) :
      mode = .seqCstXchg →
      s.pc1 = 0 →
      s.buf1 = [] →
      TsoSbStep mode s { s with mem := writeMem s.mem .loc1 1, pc1 := 1 }
  | t1SeqCstFence (s : TsoSbState) :
      mode = .movWithSeqCstFence →
      s.pc1 = 1 →
      s.buf1 = [] →
      TsoSbStep mode s { s with pc1 := 2 }
  | t1MovLoad (s : TsoSbState) :
      ((mode = .relaxedOrReleaseMov ∧ s.pc1 = 1) ∨
       (mode = .seqCstXchg ∧ s.pc1 = 1) ∨
       (mode = .movWithSeqCstFence ∧ s.pc1 = 2)) →
      TsoSbStep mode s
        { s with r1 := readWithBuffer s.buf1 s.mem .loc0,
                 pc1 := match mode with | .movWithSeqCstFence => 3 | _ => 2 }
  | t0Drain (s : TsoSbState) (e : BufEntry) (rest : List BufEntry) :
      s.buf0 = e :: rest →
      TsoSbStep mode s { s with mem := writeMem s.mem e.loc e.val, buf0 := rest }
  | t1Drain (s : TsoSbState) (e : BufEntry) (rest : List BufEntry) :
      s.buf1 = e :: rest →
      TsoSbStep mode s { s with mem := writeMem s.mem e.loc e.val, buf1 := rest }

inductive TsoSbReach (mode : SbLowerMode) : TsoSbState → Prop where
  | init : TsoSbReach mode tsoSbInit
  | step {s s' : TsoSbState} : TsoSbReach mode s → TsoSbStep mode s s' → TsoSbReach mode s'

/-- **Theorem 3b (Store-Buffering Weak Outcome Witness)**:
    Under `Relaxed`/`Release` `movStore` + `movLoad` (or with `compiler_fence`!),
    x86-TSO reaches `(pc0 = 2, pc1 = 2, r0 = 0, r1 = 0)` while writes remain buffered. -/
theorem tso_sb_mov_weak_outcome :
    ∃ s, TsoSbReach .relaxedOrReleaseMov s ∧
      s.pc0 = 2 ∧ s.pc1 = 2 ∧ s.r0 = 0 ∧ s.r1 = 0 := by
  let s1 : TsoSbState := { tsoSbInit with buf0 := [{ loc := .loc0, val := 1 }], pc0 := 1 }
  let s2 : TsoSbState := { s1 with buf1 := [{ loc := .loc1, val := 1 }], pc1 := 1 }
  let s3 : TsoSbState := { s2 with r0 := 0, pc0 := 2 }
  let s4 : TsoSbState := { s3 with r1 := 0, pc1 := 2 }
  have h01 : TsoSbStep .relaxedOrReleaseMov tsoSbInit s1 :=
    TsoSbStep.t0MovStore tsoSbInit (Or.inl rfl) rfl
  have h12 : TsoSbStep .relaxedOrReleaseMov s1 s2 :=
    TsoSbStep.t1MovStore s1 (Or.inl rfl) rfl
  have h23 : TsoSbStep .relaxedOrReleaseMov s2 s3 :=
    TsoSbStep.t0MovLoad s2 (Or.inl ⟨rfl, rfl⟩)
  have h34 : TsoSbStep .relaxedOrReleaseMov s3 s4 :=
    TsoSbStep.t1MovLoad s3 (Or.inl ⟨rfl, rfl⟩)
  exact ⟨s4,
    TsoSbReach.step (TsoSbReach.step (TsoSbReach.step (TsoSbReach.step TsoSbReach.init h01) h12) h23) h34,
    rfl, rfl, rfl, rfl⟩

/-- Inductive safety invariant for `seqCstXchg` (`xchgMem` lowers `store(SeqCst)`):
    no store buffering occurs, and whichever thread executes `movLoad` second sees
    the other thread's already-committed write in `mem`! -/
noncomputable def SbXchgInv (s : TsoSbState) : Prop :=
  s.buf0 = [] ∧
  s.buf1 = [] ∧
  (s.pc0 = 0 → s.mem.v0 = 0) ∧
  (s.pc0 ≥ 1 → s.mem.v0 = 1) ∧
  (s.pc1 = 0 → s.mem.v1 = 0) ∧
  (s.pc1 ≥ 1 → s.mem.v1 = 1) ∧
  (s.pc0 = 0 ∨ s.pc0 = 1 ∨ s.pc0 = 2) ∧
  (s.pc1 = 0 ∨ s.pc1 = 1 ∨ s.pc1 = 2) ∧
  ((s.pc0 = 2 ∧ s.pc1 = 2) → (s.r0 = 1 ∨ s.r1 = 1))

theorem sbXchgInv_init : SbXchgInv tsoSbInit := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, Or.inl rfl, Or.inl rfl, ?_⟩
  · intro _; rfl
  · intro h; cases h
  · intro _; rfl
  · intro h; cases h
  · intro ⟨h, _⟩; cases h

theorem sbXchgInv_step {s s' : TsoSbState} (hi : SbXchgInv s) (hst : TsoSbStep .seqCstXchg s s') :
    SbXchgInv s' := by
  rcases hi with ⟨hb0, hb1, hp00, hp01, hp10, hp11, hpc0, hpc1, hfinal⟩
  cases hst with
  | t0MovStore hm _ => rcases hm with h | h <;> cases h
  | t1MovStore hm _ => rcases hm with h | h <;> cases h
  | t0SeqCstFence hm _ _ => cases hm
  | t1SeqCstFence hm _ _ => cases hm
  | t0Drain _ _ hbuf => rw [hb0] at hbuf; cases hbuf
  | t1Drain _ _ hbuf => rw [hb1] at hbuf; cases hbuf
  | t0XchgStore _ _ _ =>
    refine ⟨hb0, hb1, ?_, ?_, hp10, hp11, Or.inr (Or.inl rfl), hpc1, ?_⟩
    · intro hx; cases hx
    · intro _; rfl
    · intro ⟨hx, _⟩; cases hx
  | t1XchgStore _ _ _ =>
    refine ⟨hb0, hb1, hp00, hp01, ?_, ?_, hpc0, Or.inr (Or.inl rfl), ?_⟩
    · intro hx; cases hx
    · intro _; rfl
    · intro ⟨_, hx1⟩; cases hx1
  | t0MovLoad hc =>
    rcases hc with ⟨hm, _⟩ | ⟨_, hpc⟩ | ⟨hm, _⟩
    · cases hm
    · rw [hb0, readWithBuffer_nil]
      dsimp only [readMem]
      refine ⟨rfl, hb1, ?_, ?_, hp10, hp11, Or.inr (Or.inr rfl), hpc1, ?_⟩
      · intro hx; cases hx
      · intro _; exact hp01 (by rw [hpc]; exact Nat.le_refl 1)
      · intro ⟨_, h1_2⟩
        have hm1 : s.mem.v1 = 1 := hp11 (by rw [h1_2]; exact Nat.succ_le_succ (Nat.zero_le 1))
        exact Or.inl hm1
    · cases hm
  | t1MovLoad hc =>
    rcases hc with ⟨hm, _⟩ | ⟨_, hpc⟩ | ⟨hm, _⟩
    · cases hm
    · rw [hb1, readWithBuffer_nil]
      dsimp only [readMem]
      refine ⟨hb0, rfl, hp00, hp01, ?_, ?_, hpc0, Or.inr (Or.inr rfl), ?_⟩
      · intro hx; cases hx
      · intro _; exact hp11 (by rw [hpc]; exact Nat.le_refl 1)
      · intro ⟨h0_2, _⟩
        have hm0 : s.mem.v0 = 1 := hp01 (by rw [h0_2]; exact Nat.succ_le_succ (Nat.zero_le 1))
        exact Or.inr hm0
    · cases hm

theorem sbXchgInv_of_reach {s : TsoSbState} (hr : TsoSbReach .seqCstXchg s) : SbXchgInv s := by
  induction hr with
  | init => exact sbXchgInv_init
  | step _ hst ih => exact sbXchgInv_step ih hst

/-- **Theorem 3c: `xchgMem` (`store(SeqCst)`) Lowering Soundness on x86-TSO (`tso_sb_seqcst_xchg_no_weak`)**.
    Across ALL reachable executions of lowered `store(SeqCst)` SB, `(r0 = 0 ∧ r1 = 0)` is impossible. -/
theorem tso_sb_seqcst_xchg_no_weak {s : TsoSbState} (hr : TsoSbReach .seqCstXchg s)
    (h0 : s.pc0 = 2) (h1 : s.pc1 = 2) :
    s.r0 = 1 ∨ s.r1 = 1 :=
  (sbXchgInv_of_reach hr).2.2.2.2.2.2.2.2 ⟨h0, h1⟩

/-- Inductive safety invariant for `movWithSeqCstFence` (`movStore` + `lockOrlStack` before `movLoad`):
    at `pc0 >= 2` thread 0's buffer is empty and `mem.v0 = 1`, and symmetrically for thread 1,
    making `(r0 = 0, r1 = 0)` provably impossible! -/
noncomputable def SbFenceInv (s : TsoSbState) : Prop :=
  (s.pc0 = 0 → s.buf0 = [] ∧ s.mem.v0 = 0) ∧
  (s.pc0 = 1 → (s.buf0 = [{ loc := .loc0, val := 1 }] ∧ s.mem.v0 = 0) ∨ (s.buf0 = [] ∧ s.mem.v0 = 1)) ∧
  (s.pc0 = 2 → s.buf0 = [] ∧ s.mem.v0 = 1) ∧
  (s.pc0 = 3 → s.buf0 = [] ∧ s.mem.v0 = 1) ∧
  (s.pc0 = 0 ∨ s.pc0 = 1 ∨ s.pc0 = 2 ∨ s.pc0 = 3) ∧
  (s.pc1 = 0 → s.buf1 = [] ∧ s.mem.v1 = 0) ∧
  (s.pc1 = 1 → (s.buf1 = [{ loc := .loc1, val := 1 }] ∧ s.mem.v1 = 0) ∨ (s.buf1 = [] ∧ s.mem.v1 = 1)) ∧
  (s.pc1 = 2 → s.buf1 = [] ∧ s.mem.v1 = 1) ∧
  (s.pc1 = 3 → s.buf1 = [] ∧ s.mem.v1 = 1) ∧
  (s.pc1 = 0 ∨ s.pc1 = 1 ∨ s.pc1 = 2 ∨ s.pc1 = 3) ∧
  ((s.pc0 = 3 ∧ s.pc1 = 3) → (s.r0 = 1 ∨ s.r1 = 1))

theorem sbFenceInv_init : SbFenceInv tsoSbInit := by
  refine ⟨?_, ?_, ?_, ?_, Or.inl rfl, ?_, ?_, ?_, ?_, Or.inl rfl, ?_⟩
  · intro _; exact ⟨rfl, rfl⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro _; exact ⟨rfl, rfl⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro ⟨h, _⟩; cases h

theorem sbFenceInv_step {s s' : TsoSbState} (hi : SbFenceInv s)
    (hst : TsoSbStep .movWithSeqCstFence s s') : SbFenceInv s' := by
  rcases hi with ⟨h00, h01, h02, h03, hpc0, h10, h11, h12, h13, hpc1, hfinal⟩
  cases hst with
  | t0XchgStore hm _ _ => cases hm
  | t1XchgStore hm _ _ => cases hm
  | t0MovStore _ hpc =>
    obtain ⟨hb0, hm0⟩ := h00 hpc
    refine ⟨?_, ?_, ?_, ?_, Or.inr (Or.inl rfl), h10, h11, h12, h13, hpc1, ?_⟩
    · intro hx; cases hx
    · intro _; left; refine ⟨?_, hm0⟩; rw [hb0]; rfl
    · intro hx; cases hx
    · intro hx; cases hx
    · intro ⟨hx, _⟩; cases hx
  | t1MovStore _ hpc =>
    obtain ⟨hb1, hm1⟩ := h10 hpc
    refine ⟨h00, h01, h02, h03, hpc0, ?_, ?_, ?_, ?_, Or.inr (Or.inl rfl), ?_⟩
    · intro hx; cases hx
    · intro _; left; refine ⟨?_, hm1⟩; rw [hb1]; rfl
    · intro hx; cases hx
    · intro hx; cases hx
    · intro ⟨_, hx⟩; cases hx
  | t0SeqCstFence _ hpc hb =>
    obtain hcases := h01 hpc
    have hm0 : s.mem.v0 = 1 := by
      rcases hcases with ⟨hb0, _⟩ | ⟨_, hm0⟩
      · rw [hb0] at hb; cases hb
      · exact hm0
    refine ⟨?_, ?_, ?_, ?_, Or.inr (Or.inr (Or.inl rfl)), h10, h11, h12, h13, hpc1, ?_⟩
    · intro hx; cases hx
    · intro hx; cases hx
    · intro _; exact ⟨hb, hm0⟩
    · intro hx; cases hx
    · intro ⟨hx, _⟩; cases hx
  | t1SeqCstFence _ hpc hb =>
    obtain hcases := h11 hpc
    have hm1 : s.mem.v1 = 1 := by
      rcases hcases with ⟨hb1, _⟩ | ⟨_, hm1⟩
      · rw [hb1] at hb; cases hb
      · exact hm1
    refine ⟨h00, h01, h02, h03, hpc0, ?_, ?_, ?_, ?_, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    · intro hx; cases hx
    · intro hx; cases hx
    · intro _; exact ⟨hb, hm1⟩
    · intro hx; cases hx
    · intro ⟨_, hx⟩; cases hx
  | t0Drain e rest hbuf =>
    rcases hpc0 with hp | hp | hp | hp
    · obtain ⟨hb0, _⟩ := h00 hp; rw [hb0] at hbuf; cases hbuf
    · rcases h01 hp with ⟨hb0, _⟩ | ⟨hb0, _⟩
      · rw [hb0] at hbuf; cases hbuf
        refine ⟨?_, ?_, ?_, ?_, Or.inr (Or.inl hp), ?_, ?_, ?_, ?_, hpc1, ?_⟩
        · intro hx; rw [hp] at hx; cases hx
        · intro _; right; exact ⟨rfl, rfl⟩
        · intro hx; rw [hp] at hx; cases hx
        · intro hx; rw [hp] at hx; cases hx
        · intro hp1; exact h10 hp1
        · intro hp1; exact h11 hp1
        · intro hp1; exact h12 hp1
        · intro hp1; exact h13 hp1
        · intro ⟨hx, _⟩; rw [hp] at hx; cases hx
      · rw [hb0] at hbuf; cases hbuf
    · obtain ⟨hb0, _⟩ := h02 hp; rw [hb0] at hbuf; cases hbuf
    · obtain ⟨hb0, _⟩ := h03 hp; rw [hb0] at hbuf; cases hbuf
  | t1Drain e rest hbuf =>
    rcases hpc1 with hp | hp | hp | hp
    · obtain ⟨hb1, _⟩ := h10 hp; rw [hb1] at hbuf; cases hbuf
    · rcases h11 hp with ⟨hb1, _⟩ | ⟨hb1, _⟩
      · rw [hb1] at hbuf; cases hbuf
        refine ⟨?_, ?_, ?_, ?_, hpc0, ?_, ?_, ?_, ?_, Or.inr (Or.inl hp), ?_⟩
        · intro hp0; exact h00 hp0
        · intro hp0; exact h01 hp0
        · intro hp0; exact h02 hp0
        · intro hp0; exact h03 hp0
        · intro hx; rw [hp] at hx; cases hx
        · intro _; right; exact ⟨rfl, rfl⟩
        · intro hx; rw [hp] at hx; cases hx
        · intro hx; rw [hp] at hx; cases hx
        · intro ⟨_, hx⟩; rw [hp] at hx; cases hx
      · rw [hb1] at hbuf; cases hbuf
    · obtain ⟨hb1, _⟩ := h12 hp; rw [hb1] at hbuf; cases hbuf
    · obtain ⟨hb1, _⟩ := h13 hp; rw [hb1] at hbuf; cases hbuf
  | t0MovLoad hc =>
    rcases hc with ⟨hm, _⟩ | ⟨hm, _⟩ | ⟨_, hpc⟩
    · cases hm
    · cases hm
    · obtain ⟨hb0, hm0⟩ := h02 hpc
      rw [hb0, readWithBuffer_nil]
      dsimp only [readMem]
      refine ⟨?_, ?_, ?_, ?_, Or.inr (Or.inr (Or.inr rfl)), h10, h11, h12, h13, hpc1, ?_⟩
      · intro hx; cases hx
      · intro hx; cases hx
      · intro hx; cases hx
      · intro _; exact ⟨rfl, hm0⟩
      · intro ⟨_, h1_3⟩
        obtain ⟨_, hm1⟩ := h13 h1_3
        exact Or.inl hm1
  | t1MovLoad hc =>
    rcases hc with ⟨hm, _⟩ | ⟨hm, _⟩ | ⟨_, hpc⟩
    · cases hm
    · cases hm
    · obtain ⟨hb1, hm1⟩ := h12 hpc
      rw [hb1, readWithBuffer_nil]
      dsimp only [readMem]
      refine ⟨h00, h01, h02, h03, hpc0, ?_, ?_, ?_, ?_, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
      · intro hx; cases hx
      · intro hx; cases hx
      · intro hx; cases hx
      · intro _; exact ⟨rfl, hm1⟩
      · intro ⟨h0_3, _⟩
        obtain ⟨_, hm0⟩ := h03 h0_3
        exact Or.inr hm0

theorem sbFenceInv_of_reach {s : TsoSbState} (hr : TsoSbReach .movWithSeqCstFence s) :
    SbFenceInv s := by
  induction hr with
  | init => exact sbFenceInv_init
  | step _ hst ih => exact sbFenceInv_step ih hst

/-- **Theorem 3d: `fence(SeqCst)` (`lock orl $0, -64(%rsp)` / `mfence`) Soundness on x86-TSO (`tso_sb_fence_seqcst_no_weak`)**.
    Across ALL reachable executions of `movStore + lockOrlStack + movLoad`, `(r0 = 0 ∧ r1 = 0)` is impossible. -/
theorem tso_sb_fence_seqcst_no_weak {s : TsoSbState} (hr : TsoSbReach .movWithSeqCstFence s)
    (h0 : s.pc0 = 3) (h1 : s.pc1 = 3) :
    s.r0 = 1 ∨ s.r1 = 1 :=
  (sbFenceInv_of_reach hr).2.2.2.2.2.2.2.2.2.2 ⟨h0, h1⟩

/-! ## Section 6: `compiler_fence` Intra-Thread Reordering Barrier vs. Cross-Thread Separation -/

/-- Abstract single-thread IR statement modeled for compiler optimization barriers. -/
inductive IrStmt where
  | naStore (loc : LocId) (val : Val)
  | naLoad (loc : LocId) (dstReg : Nat)
  | atStoreRelaxed (loc : LocId) (val : Val)
  | atLoadRelaxed (loc : LocId) (dstReg : Nat)
  | compFence (o : RustOrdering)
  | hwFence (o : RustOrdering)

/-- Whether an IR statement acts as a compiler optimization/reordering barrier. -/
noncomputable def isCompilerBarrier : IrStmt → Bool
  | .compFence _ => true
  | .hwFence _   => true
  | _            => false

/-- Legal compiler optimization rewrite over adjacent IR statements (GVN/DSE/scheduling).
    Every rule requires the two memory instructions to be adjacent with NO `isCompilerBarrier`
    between them. -/
inductive CompilerRewrite : List IrStmt → List IrStmt → Prop where
  | swapIndependent (a b : IrStmt) (rest : List IrStmt) :
      isCompilerBarrier a = false →
      isCompilerBarrier b = false →
      CompilerRewrite (a :: b :: rest) (b :: a :: rest)
  | elimDeadNaStore (loc : LocId) (v1 v2 : Val) (rest : List IrStmt) :
      CompilerRewrite (.naStore loc v1 :: .naStore loc v2 :: rest) (.naStore loc v2 :: rest)
  | elimRedundantNaLoad (loc : LocId) (r1 r2 : Nat) (rest : List IrStmt) :
      CompilerRewrite (.naLoad loc r1 :: .naLoad loc r2 :: rest) (.naLoad loc r1 :: rest)
  | congTail (hd : IrStmt) (t1 t2 : List IrStmt) :
      CompilerRewrite t1 t2 →
      CompilerRewrite (hd :: t1) (hd :: t2)

theorem no_fence_allows_dse (loc : LocId) :
    CompilerRewrite [.naStore loc 1, .naStore loc 2] [.naStore loc 2] :=
  CompilerRewrite.elimDeadNaStore loc 1 2 []

theorem no_fence_allows_cse (loc : LocId) :
    CompilerRewrite [.naLoad loc 0, .naLoad loc 1] [.naLoad loc 0] :=
  CompilerRewrite.elimRedundantNaLoad loc 0 1 []

/-- **Theorem 4a (`compiler_fence` Intra-Thread Reordering & DSE/CSE Barrier)**:
    Inserting `compiler_fence(o)` between two non-atomic stores or two non-atomic loads
    prevents ANY `CompilerRewrite` step (neither reordering, nor DSE, nor CSE can cross it). -/
theorem compiler_fence_blocks_dse (loc : LocId) (o : RustOrdering) (target : List IrStmt) :
    ¬ CompilerRewrite [.naStore loc 1, .compFence o, .naStore loc 2] target := by
  intro h
  cases h with
  | swapIndependent _ _ _ _ hb => cases hb
  | congTail _ _ _ htail =>
    cases htail with
    | swapIndependent _ _ _ ha _ => cases ha
    | congTail _ _ _ htail2 =>
      cases htail2 with
      | congTail _ _ _ htail3 => cases htail3

theorem compiler_fence_blocks_cse (loc : LocId) (o : RustOrdering) (target : List IrStmt) :
    ¬ CompilerRewrite [.naLoad loc 0, .compFence o, .naLoad loc 1] target := by
  intro h
  cases h with
  | swapIndependent _ _ _ _ hb => cases hb
  | congTail _ _ _ htail =>
    cases htail with
    | swapIndependent _ _ _ ha _ => cases ha
    | congTail _ _ _ htail2 =>
      cases htail2 with
      | congTail _ _ _ htail3 => cases htail3

/-- Same-thread signal-handler semantics (`SignalStep`): an interrupted single-CPU
    thread shares coherent CPU memory (NO store buffer between thread and its own handler!),
    so `compiler_fence` preserving `sb` write-before-flag guarantees `data = 42` whenever
    the handler observes `flag = 1`. -/
structure SignalMachineState where
  memData : Nat
  memFlag : Nat
  pcMain  : Nat

noncomputable def signalMainStep : SignalMachineState → SignalMachineState → Prop
  | s, s' =>
      (s.pcMain = 0 ∧ s' = { s with memData := 42, pcMain := 1 }) ∨
      (s.pcMain = 1 ∧ s' = { s with pcMain := 2 }) ∨  -- compiler_fence (NOP on CPU, preserves sb)
      (s.pcMain = 2 ∧ s' = { s with memFlag := 1, pcMain := 3 })

inductive SignalReach : SignalMachineState → Prop where
  | init : SignalReach { memData := 0, memFlag := 0, pcMain := 0 }
  | step {s s' : SignalMachineState} : SignalReach s → signalMainStep s s' → SignalReach s'

noncomputable def SignalInv (s : SignalMachineState) : Prop :=
  (s.pcMain = 0 → s.memData = 0 ∧ s.memFlag = 0) ∧
  (s.pcMain = 1 → s.memData = 42 ∧ s.memFlag = 0) ∧
  (s.pcMain = 2 → s.memData = 42 ∧ s.memFlag = 0) ∧
  (s.pcMain = 3 → s.memData = 42 ∧ s.memFlag = 1) ∧
  (s.pcMain = 0 ∨ s.pcMain = 1 ∨ s.pcMain = 2 ∨ s.pcMain = 3)

theorem signalInv_of_reach {s : SignalMachineState} (hr : SignalReach s) : SignalInv s := by
  induction hr with
  | init =>
    refine ⟨fun _ => ⟨rfl, rfl⟩, fun h => ?_, fun h => ?_, fun h => ?_, Or.inl rfl⟩ <;> cases h
  | step _ hst ih =>
    rcases ih with ⟨h0, h1, h2, h3, _⟩
    rcases hst with ⟨hp, hs⟩ | ⟨hp, hs⟩ | ⟨hp, hs⟩
    · obtain ⟨_, hm⟩ := h0 hp
      subst hs
      refine ⟨fun h => ?_, fun _ => ⟨rfl, hm⟩, fun h => ?_, fun h => ?_, Or.inr (Or.inl rfl)⟩ <;> cases h
    · obtain ⟨hd, hm⟩ := h1 hp
      subst hs
      refine ⟨fun h => ?_, fun h => ?_, fun _ => ⟨hd, hm⟩, fun h => ?_, Or.inr (Or.inr (Or.inl rfl))⟩ <;> cases h
    · obtain ⟨hd, _⟩ := h2 hp
      subst hs
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun _ => ⟨hd, rfl⟩, Or.inr (Or.inr (Or.inr rfl))⟩ <;> cases h

theorem compiler_fence_signal_handler_sound {s : SignalMachineState} (hr : SignalReach s)
    (hflag : s.memFlag = 1) : s.memData = 42 := by
  rcases signalInv_of_reach hr with ⟨h0, h1, h2, h3, hpc⟩
  rcases hpc with hp | hp | hp | hp
  · rw [(h0 hp).2] at hflag; cases hflag
  · rw [(h1 hp).2] at hflag; cases hflag
  · rw [(h2 hp).2] at hflag; cases hflag
  · exact (h3 hp).1

/-- 6-event cross-thread MP graph WITH `compiler_fence(SeqCst)` on both threads:
    `0 (naWrite x) -> 1 (compFence seqCst) -> 2 (atStore flag relaxed)
     -[rf]-> 3 (atLoad flag relaxed) -> 4 (compFence seqCst) -> 5 (naRead x)`. -/
noncomputable def cfenceMpEvents : EventId → Option ExecEvent
  | 0 => some { thread := 0, loc := 0, val := 42, kind := .naWrite }
  | 1 => some { thread := 0, loc := 9, val := 0,  kind := .compFence .seqCst }
  | 2 => some { thread := 0, loc := 1, val := 1,  kind := .atStore .relaxed }
  | 3 => some { thread := 1, loc := 1, val := 1,  kind := .atLoad .relaxed }
  | 4 => some { thread := 1, loc := 9, val := 0,  kind := .compFence .seqCst }
  | 5 => some { thread := 1, loc := 0, val := 42, kind := .naRead }
  | _ => none

noncomputable def cfenceMpSb : EventId → EventId → Prop
  | 0, 1 => True
  | 1, 2 => True
  | 0, 2 => True
  | 3, 4 => True
  | 4, 5 => True
  | 3, 5 => True
  | _, _ => False

noncomputable def cfenceMpRf : EventId → EventId → Prop
  | 2, 3 => True
  | _, _ => False

noncomputable def cfenceMpGraph : ExecGraph :=
  { events := cfenceMpEvents
    sb := cfenceMpSb
    rf := cfenceMpRf
    mo := fun _ _ => False
    sc := fun _ _ => False }

theorem cfenceMpGraph_no_sw (a b : EventId) : ¬ DirectSw cfenceMpGraph a b := by
  refine no_sw_of_no_rel_acq cfenceMpGraph ?_ ?_ a b
  · intro i ev hi
    cases i with
    | zero => cases hi; exact ⟨rfl, rfl⟩
    | succ i1 =>
      cases i1 with
      | zero => cases hi; exact ⟨rfl, rfl⟩
      | succ i2 =>
        cases i2 with
        | zero => cases hi; exact ⟨rfl, rfl⟩
        | succ i3 =>
          cases i3 with
          | zero => cases hi; exact ⟨rfl, rfl⟩
          | succ i4 =>
            cases i4 with
            | zero => cases hi; exact ⟨rfl, rfl⟩
            | succ i5 =>
              cases i5 with
              | zero => cases hi; exact ⟨rfl, rfl⟩
              | succ _ => cases hi
  · intro w r ew er hrf hw hr
    cases w with
    | zero => cases hrf
    | succ w1 =>
      cases w1 with
      | zero => cases hrf
      | succ w2 =>
        cases w2 with
        | zero =>
          cases r with
          | zero => cases hrf
          | succ r1 =>
            cases r1 with
            | zero => cases hrf
            | succ r2 =>
              cases r2 with
              | zero => cases hrf
              | succ r3 =>
                cases r3 with
                | zero => cases hw; cases hr; exact Or.inl rfl
                | succ _ => cases hrf
        | succ _ => cases hrf

theorem cfenceMpSb_elim {a b : EventId} (h : cfenceMpSb a b) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 0 ∧ b = 2) ∨
    (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 5) ∨ (a = 3 ∧ b = 5) := by
  cases a with
  | zero =>
    cases b with
    | zero => cases h
    | succ b1 =>
      cases b1 with
      | zero => exact Or.inl ⟨rfl, rfl⟩
      | succ b2 =>
        cases b2 with
        | zero => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        | succ _ => cases h
  | succ a1 =>
    cases a1 with
    | zero =>
      cases b with
      | zero => cases h
      | succ b1 =>
        cases b1 with
        | zero => cases h
        | succ b2 =>
          cases b2 with
          | zero => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          | succ _ => cases h
    | succ a2 =>
      cases a2 with
      | zero => cases h
      | succ a3 =>
        cases a3 with
        | zero =>
          cases b with
          | zero => cases h
          | succ b1 =>
            cases b1 with
            | zero => cases h
            | succ b2 =>
              cases b2 with
              | zero => cases h
              | succ b3 =>
                cases b3 with
                | zero => cases h
                | succ b4 =>
                  cases b4 with
                  | zero => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                  | succ b5 =>
                    cases b5 with
                    | zero => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
                    | succ _ => cases h
        | succ a4 =>
          cases a4 with
          | zero =>
            cases b with
            | zero => cases h
            | succ b1 =>
              cases b1 with
              | zero => cases h
              | succ b2 =>
                cases b2 with
                | zero => cases h
                | succ b3 =>
                  cases b3 with
                  | zero => cases h
                  | succ b4 =>
                    cases b4 with
                    | zero => cases h
                    | succ b5 =>
                      cases b5 with
                      | zero => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
                      | succ _ => cases h
          | succ _ => cases h

theorem cfenceMp_hb_implies_sb {a b : EventId}
    (h : HappensBefore cfenceMpGraph a b) : cfenceMpSb a b := by
  refine hb_in_rel_if_no_sw cfenceMpGraph cfenceMpSb (fun _ _ hs => hs) cfenceMpGraph_no_sw ?_ h
  intro x y z h1 h2
  rcases cfenceMpSb_elim h1 with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases cfenceMpSb_elim h2 with
      ⟨hb, rfl⟩ | ⟨hb, rfl⟩ | ⟨hb, rfl⟩ | ⟨hb, rfl⟩ | ⟨hb, rfl⟩ | ⟨hb, rfl⟩ <;>
    first | trivial | cases hb

/-- **Theorem 4b (`compiler_fence` Cross-Thread Non-Synchronization Separation)**:
    Even with `compiler_fence(SeqCst)` in both threads, `(1)` `lowerAtomicToTso` emits
    `membarrierNoop` (0 CPU barriers), `(2)` the 2-thread axiomatic graph exhibits
    `DataRace cfenceMpGraph 0 5`, and `(3)` the operational x86-TSO SB trace under
    `compiler_fence(SeqCst)` still reaches the weak `(r0 = 0, r1 = 0)` outcome! -/
theorem compiler_fence_non_sync_separation (cfg : X86AbiConfig) :
    lowerAtomicToTso cfg (.compilerFence .seqCst) = .membarrierNoop ∧
    emitsCpuBarrier (lowerAtomicToTso cfg (.compilerFence .seqCst)) = false ∧
    DataRace cfenceMpGraph 0 5 ∧
    (∃ s, TsoSbReach .relaxedOrReleaseMov s ∧ s.pc0 = 2 ∧ s.pc1 = 2 ∧ s.r0 = 0 ∧ s.r1 = 0) := by
  have hlower : lowerAtomicToTso cfg (.compilerFence .seqCst) = .membarrierNoop := rfl
  have hbar   : emitsCpuBarrier (lowerAtomicToTso cfg (.compilerFence .seqCst)) = false := rfl
  have h05 : ¬ HappensBefore cfenceMpGraph 0 5 := by
    intro h; have hsb := cfenceMp_hb_implies_sb h; cases hsb
  have h50 : ¬ HappensBefore cfenceMpGraph 5 0 := by
    intro h; have hsb := cfenceMp_hb_implies_sb h; cases hsb
  have hconf : Conflicting cfenceMpGraph 0 5 := by
    refine ⟨{ thread := 0, loc := 0, val := 42, kind := .naWrite },
            { thread := 1, loc := 0, val := 42, kind := .naRead },
            rfl, rfl, ?_, rfl, Or.inl rfl, Or.inl rfl⟩
    intro heq; cases heq
  exact ⟨hlower, hbar, ⟨hconf, h05, h50⟩, tso_sb_mov_weak_outcome⟩

/-! ## Section 7: End-to-End Composition & Lowering Invariant Summaries -/

/-- Combined lowering & soundness theorem tying Rust `core::sync::atomic` operations
    to LLVM IR, x86-TSO instructions, Miri vector-clock checks, and operational traces. -/
theorem end_to_end_atomics_and_tso_soundness (cfg : X86AbiConfig) :
    (lowerAtomicToTso cfg (.load .relaxed) = .movLoad ∧
     lowerAtomicToTso cfg (.load .acquire) = .movLoad ∧
     lowerAtomicToTso cfg (.load .seqCst)  = .movLoad) ∧
    (lowerAtomicToTso cfg (.store .relaxed) = .movStore ∧
     lowerAtomicToTso cfg (.store .release) = .movStore ∧
     lowerAtomicToTso cfg (.store .seqCst)  = .xchgMem) ∧
    (lowerAtomicToTso cfg (.fence .acqRel)  = .membarrierNoop ∧
     lowerAtomicToTso defaultX86_64Cfg (.fence .seqCst) = .lockOrlStack (-64) ∧
     lowerAtomicToTso noRedZoneX86_64Cfg (.fence .seqCst) = .lockOrlStack 0 ∧
     lowerAtomicToTso cfg (.compilerFence .seqCst) = .membarrierNoop) ∧
    (∀ {s : TsoMpState}, TsoMpReach s → s.pc1 = 2 → s.rData = 42) ∧
    (∀ {s : TsoSbState}, TsoSbReach .seqCstXchg s → s.pc0 = 2 → s.pc1 = 2 → s.r0 = 1 ∨ s.r1 = 1) ∧
    (∀ {s : TsoSbState}, TsoSbReach .movWithSeqCstFence s → s.pc0 = 3 → s.pc1 = 3 → s.r0 = 1 ∨ s.r1 = 1) ∧
    DataRace relaxedMpGraph 0 3 ∧
    DataRace cfenceMpGraph 0 5 := by
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
    ?_, ?_, ?_, relaxed_mp_data_race_witness.2.2.2, ?_⟩
  · intro s hr hdone; exact tso_mov_preserves_rel_acq_mp hr hdone
  · intro s hr h0 h1; exact tso_sb_seqcst_xchg_no_weak hr h0 h1
  · intro s hr h0 h1; exact tso_sb_fence_seqcst_no_weak hr h0 h1
  · exact (compiler_fence_non_sync_separation cfg).2.2.1

end AtomicsOrderingX86TsoLoweringAndRaceSoundness
