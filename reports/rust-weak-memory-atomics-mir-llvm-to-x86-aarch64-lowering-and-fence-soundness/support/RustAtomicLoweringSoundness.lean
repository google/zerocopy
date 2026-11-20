/-!
# Rust atomic lowering: MIR → LLVM IR → x86-64 / i686 / AArch64 / s390x

Self-contained Lean 4 development (core library only, no imports).

What is modelled

* §1–§3  The Rust ordering lattice, the MIR-level atomic operations with the
  validity rules enforced by `core::sync::atomic`, and the one-to-one map onto
  LLVM IR atomic instructions.
* §4     Instruction selection tables for `x86_64` (red zone on/off), `i686`
  (SSE2 / SSE1-only / x87-only, 32- and 64-bit operands), AArch64 (four feature
  profiles) and `s390x`, transcribed from measured `rustc` output.
* §5     Table-level theorems quantified over every operation, ordering and
  configuration.
* §6–§9  Finite candidate executions of litmus programs *compiled through the
  tables of §4*, checked against fragments of the published axiomatic models
  (herd `x86tso.cat`, the Arm `aarch64hwreqs.cat` barrier-ordered-before
  clauses, and the RC11 `psc` / coherence conditions).
* §10    The red-zone stack-ownership model for `lock orl $0, d(%rsp)`.
* §11    The compiler-fence scheduling and dead-store-elimination model.
* §12    Token export used by the differential check against measured assembly.

Scope limits (also stated next to the definitions they affect)

* §6–§9 are litmus-scale: straight-line programs of loads, stores and fences,
  at most one non-initial write per location, no dependencies. They are not a
  compilation-correctness proof for arbitrary programs.
* The source-side relations in §8 are sub-relations of the RC11 ones, so a
  violation found here is an RC11 violation; the converse is not claimed.
* `s390x` is checked against the same store-buffer model as x86, with
  `bcr 15,%r0` as the full fence; that is a modelling assumption.
-/

set_option autoImplicit false

namespace RustAtomicLowering

/-!
Every recursive definition below is specification-level: it is evaluated only by the kernel
(through `decide` and `rfl`), never run. Such definitions are declared `noncomputable` so that
Lean generates no executable implementation for them and the environment holds only their
kernel-checked structural definitions. The token export of §12 uses none of them.
-/
noncomputable section

/-! ## 0. Boolean and bounded-quantifier helpers -/

theorem and_left : ∀ {a b : Bool}, (a && b) = true → a = true
  | true, _, _ => rfl
  | false, _, h => Bool.noConfusion h

theorem and_right : ∀ {a b : Bool}, (a && b) = true → b = true
  | true, _, h => h
  | false, _, h => Bool.noConfusion h

theorem and_intro : ∀ {a b : Bool}, a = true → b = true → (a && b) = true
  | _, _, rfl, rfl => rfl

theorem or_cases : ∀ {a b : Bool}, (a || b) = true → a = true ∨ b = true
  | true, _, _ => Or.inl rfl
  | false, _, h => Or.inr h

theorem or_inl : ∀ {a b : Bool}, a = true → (a || b) = true
  | _, _, rfl => rfl

theorem or_inr : ∀ {a b : Bool}, b = true → (a || b) = true
  | true, _, _ => rfl
  | false, _, h => h

theorem not_true_eq_false : ∀ {a : Bool}, (!a) = true → a = false
  | false, _ => rfl
  | true, h => Bool.noConfusion h

/-- `p` holds for every natural number below `n`. -/
noncomputable def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n && allBelow p n

theorem allBelow_spec {p : Nat → Bool} :
    ∀ {n : Nat}, allBelow p n = true → ∀ a, a < n → p a = true
  | 0, _, a, h => absurd h (Nat.not_lt_zero a)
  | n + 1, h, a, ha => by
      have h' : (p n && allBelow p n) = true := h
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ ha) with heq | hlt
      · subst heq; exact and_left h'
      · exact allBelow_spec (and_right h') a hlt

/-- `p` holds for some natural number below `n`. -/
noncomputable def anyBelow (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => p n || anyBelow p n

theorem anyBelow_spec {p : Nat → Bool} :
    ∀ {n : Nat}, anyBelow p n = true → ∃ a, a < n ∧ p a = true
  | 0, h => Bool.noConfusion h
  | n + 1, h => by
      have h' : (p n || anyBelow p n) = true := h
      rcases or_cases h' with hp | hrest
      · exact ⟨n, Nat.lt_succ_self n, hp⟩
      · have ⟨a, ha, hpa⟩ := anyBelow_spec hrest
        exact ⟨a, Nat.lt_succ_of_lt ha, hpa⟩

theorem anyBelow_intro {p : Nat → Bool} :
    ∀ {n a : Nat}, a < n → p a = true → anyBelow p n = true
  | 0, a, h, _ => absurd h (Nat.not_lt_zero a)
  | n + 1, a, h, hp => by
      show (p n || anyBelow p n) = true
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with heq | hlt
      · subst heq; exact or_inl hp
      · exact or_inr (anyBelow_intro hlt hp)

/-! ## 1. The Rust ordering lattice -/

/-- `core::sync::atomic::Ordering`. -/
inductive RustOrdering where
  | relaxed | release | acquire | acqRel | seqCst
  deriving DecidableEq, Repr

namespace RustOrdering

/-- Discriminants of `core::intrinsics::AtomicOrdering` (`Relaxed = 0`, `Release = 1`,
`Acquire = 2`, `AcqRel = 3`, `SeqCst = 4`); these are the immediates visible in
unoptimized `x86_64` call sites such as `movl $4, %edx`. -/
def discr : RustOrdering → Nat
  | relaxed => 0 | release => 1 | acquire => 2 | acqRel => 3 | seqCst => 4

/-- The ordering has acquire semantics. -/
def acq : RustOrdering → Bool
  | acquire | acqRel | seqCst => true
  | _ => false

/-- The ordering has release semantics. -/
def rel : RustOrdering → Bool
  | release | acqRel | seqCst => true
  | _ => false

/-- The ordering takes part in the sequentially consistent order. -/
def sc : RustOrdering → Bool
  | seqCst => true
  | _ => false

/-- Strength order: component-wise implication on `(acq, rel, sc)`. -/
def le (a b : RustOrdering) : Bool :=
  (!a.acq || b.acq) && (!a.rel || b.rel) && (!a.sc || b.sc)

/-- Least upper bound. -/
def join : RustOrdering → RustOrdering → RustOrdering
  | seqCst, _ => seqCst
  | _, seqCst => seqCst
  | relaxed, b => b
  | a, relaxed => a
  | release, release => release
  | acquire, acquire => acquire
  | _, _ => acqRel

theorem le_refl (a : RustOrdering) : le a a = true := by cases a <;> rfl

theorem le_trans {a b c : RustOrdering} : le a b = true → le b c = true → le a c = true := by
  cases a <;> cases b <;> cases c <;> decide

theorem le_antisymm {a b : RustOrdering} : le a b = true → le b a = true → a = b := by
  cases a <;> cases b <;> decide

theorem relaxed_le (a : RustOrdering) : le relaxed a = true := by cases a <;> rfl

theorem le_seqCst (a : RustOrdering) : le a seqCst = true := by cases a <;> rfl

theorem le_join_left (a b : RustOrdering) : le a (join a b) = true := by
  cases a <;> cases b <;> rfl

theorem le_join_right (a b : RustOrdering) : le b (join a b) = true := by
  cases a <;> cases b <;> rfl

theorem join_le {a b c : RustOrdering} : le a c = true → le b c = true → le (join a b) c = true := by
  cases a <;> cases b <;> cases c <;> decide

/-- `Acquire` and `Release` are incomparable; `AcqRel` is their join and sits strictly below `SeqCst`. -/
theorem acquire_release_diamond :
    le acquire release = false ∧ le release acquire = false ∧
    join acquire release = acqRel ∧ le acqRel seqCst = true ∧ le seqCst acqRel = false := by
  decide

theorem discr_injective {a b : RustOrdering} : discr a = discr b → a = b := by
  cases a <;> cases b <;> decide

end RustOrdering

/-! ## 2. MIR-level atomic operations -/

/-- The read-modify-write families exercised by the probe (`swap`, `fetch_add`, `fetch_and`). -/
inductive RmwKind where
  | xchg | add | and
  deriving DecidableEq, Repr

/-- A resolved `core::intrinsics::atomic_*` call as it appears in MIR, with its
const-generic ordering argument(s). -/
inductive MirAtomicOp where
  | load (o : RustOrdering)
  | store (o : RustOrdering)
  | rmw (k : RmwKind) (o : RustOrdering)
  | casStrong (succ fail : RustOrdering)
  | casWeak (succ fail : RustOrdering)
  | fence (o : RustOrdering)
  | compilerFence (o : RustOrdering)
  deriving DecidableEq, Repr

namespace MirAtomicOp

/-- Orderings accepted for loads and for compare-exchange failure. -/
def loadOrd : RustOrdering → Bool
  | .relaxed | .acquire | .seqCst => true
  | _ => false

/-- Orderings accepted for stores. -/
def storeOrd : RustOrdering → Bool
  | .relaxed | .release | .seqCst => true
  | _ => false

/-- Orderings accepted for `fence` and `compiler_fence`. -/
def fenceOrd : RustOrdering → Bool
  | .relaxed => false
  | _ => true

/-- The combinations that `core::sync::atomic` forwards to an intrinsic instead of panicking
("there is no such thing as a release load", "... an acquire store",
"... a release failure ordering", "... a relaxed fence"). -/
def valid : MirAtomicOp → Bool
  | load o => loadOrd o
  | store o => storeOrd o
  | rmw _ _ => true
  | casStrong _ f => loadOrd f
  | casWeak _ f => loadOrd f
  | fence o => fenceOrd o
  | compilerFence o => fenceOrd o

end MirAtomicOp

/-! ## 3. LLVM IR atomic instructions -/

/-- LLVM `AtomicOrdering` values reachable from Rust (`monotonic` is LLVM's name for `Relaxed`). -/
inductive LlvmOrd where
  | monotonic | acquire | release | acqRel | seqCst
  deriving DecidableEq, Repr

namespace LlvmOrd

/-- Numeric value of `llvm::AtomicOrdering`; AArch64's `atomic_fence (i64 4)` pattern tests it. -/
def code : LlvmOrd → Nat
  | monotonic => 2 | acquire => 4 | release => 5 | acqRel => 6 | seqCst => 7

def acq : LlvmOrd → Bool
  | acquire | acqRel | seqCst => true
  | _ => false

def rel : LlvmOrd → Bool
  | release | acqRel | seqCst => true
  | _ => false

theorem code_eq_four_iff (o : LlvmOrd) : code o = 4 ↔ o = acquire := by
  cases o <;> decide

end LlvmOrd

/-- `load atomic`, `store atomic`, `atomicrmw`, `cmpxchg [weak]`, `fence [syncscope("singlethread")]`. -/
inductive LlvmAtomic where
  | loadAtomic (o : LlvmOrd)
  | storeAtomic (o : LlvmOrd)
  | atomicrmw (k : RmwKind) (o : LlvmOrd)
  | cmpxchg (weak : Bool) (succ fail : LlvmOrd)
  | fence (singleThread : Bool) (o : LlvmOrd)
  deriving DecidableEq, Repr

def toLlvmOrd : RustOrdering → LlvmOrd
  | .relaxed => .monotonic | .release => .release | .acquire => .acquire
  | .acqRel => .acqRel | .seqCst => .seqCst

def ofLlvmOrd : LlvmOrd → RustOrdering
  | .monotonic => .relaxed | .release => .release | .acquire => .acquire
  | .acqRel => .acqRel | .seqCst => .seqCst

/-- `rustc_codegen_ssa` intrinsic dispatch followed by the `rustc_codegen_llvm` builder. -/
def mirToLlvm : MirAtomicOp → LlvmAtomic
  | .load o => .loadAtomic (toLlvmOrd o)
  | .store o => .storeAtomic (toLlvmOrd o)
  | .rmw k o => .atomicrmw k (toLlvmOrd o)
  | .casStrong s f => .cmpxchg false (toLlvmOrd s) (toLlvmOrd f)
  | .casWeak s f => .cmpxchg true (toLlvmOrd s) (toLlvmOrd f)
  | .fence o => .fence false (toLlvmOrd o)
  | .compilerFence o => .fence true (toLlvmOrd o)

def llvmToMir : LlvmAtomic → MirAtomicOp
  | .loadAtomic o => .load (ofLlvmOrd o)
  | .storeAtomic o => .store (ofLlvmOrd o)
  | .atomicrmw k o => .rmw k (ofLlvmOrd o)
  | .cmpxchg false s f => .casStrong (ofLlvmOrd s) (ofLlvmOrd f)
  | .cmpxchg true s f => .casWeak (ofLlvmOrd s) (ofLlvmOrd f)
  | .fence false o => .fence (ofLlvmOrd o)
  | .fence true o => .compilerFence (ofLlvmOrd o)

theorem ofLlvm_toLlvm (o : RustOrdering) : ofLlvmOrd (toLlvmOrd o) = o := by
  cases o <;> rfl

theorem toLlvm_acq (o : RustOrdering) : (toLlvmOrd o).acq = o.acq := by cases o <;> rfl

theorem toLlvm_rel (o : RustOrdering) : (toLlvmOrd o).rel = o.rel := by cases o <;> rfl

theorem llvmToMir_mirToLlvm (a : MirAtomicOp) : llvmToMir (mirToLlvm a) = a := by
  cases a with
  | load o => show MirAtomicOp.load (ofLlvmOrd (toLlvmOrd o)) = _; rw [ofLlvm_toLlvm]
  | store o => show MirAtomicOp.store (ofLlvmOrd (toLlvmOrd o)) = _; rw [ofLlvm_toLlvm]
  | rmw k o => show MirAtomicOp.rmw k (ofLlvmOrd (toLlvmOrd o)) = _; rw [ofLlvm_toLlvm]
  | casStrong s f =>
      show MirAtomicOp.casStrong (ofLlvmOrd (toLlvmOrd s)) (ofLlvmOrd (toLlvmOrd f)) = _
      rw [ofLlvm_toLlvm, ofLlvm_toLlvm]
  | casWeak s f =>
      show MirAtomicOp.casWeak (ofLlvmOrd (toLlvmOrd s)) (ofLlvmOrd (toLlvmOrd f)) = _
      rw [ofLlvm_toLlvm, ofLlvm_toLlvm]
  | fence o => show MirAtomicOp.fence (ofLlvmOrd (toLlvmOrd o)) = _; rw [ofLlvm_toLlvm]
  | compilerFence o =>
      show MirAtomicOp.compilerFence (ofLlvmOrd (toLlvmOrd o)) = _; rw [ofLlvm_toLlvm]

/-- The MIR → LLVM IR step loses nothing: operation kind, weak flag, synchronization scope and
every ordering are recoverable from the emitted instruction. -/
theorem mirToLlvm_injective {a b : MirAtomicOp} (h : mirToLlvm a = mirToLlvm b) : a = b := by
  have h' := congrArg llvmToMir h
  rw [llvmToMir_mirToLlvm, llvmToMir_mirToLlvm] at h'
  exact h'

/-! ## 4. Instruction selection tables -/

/-- x86 instruction classes (shared by `x86_64` and `i686`). -/
inductive X86Inst where
  | movLoad            -- `mov (%p), %r`
  | movStore           -- `mov %r, (%p)`
  | xchg               -- `xchg %r, (%p)` (implicitly locked)
  | lockXadd           -- `lock xadd %r, (%p)`
  | lockCmpxchg        -- `lock cmpxchg %r, (%p)`
  | lockCmpxchg8b      -- `lock cmpxchg8b (%p)`
  | lockOrSp (disp : Int)  -- `lock orl $0, disp(%rsp)` / `disp(%esp)`
  | mfence
  | sseLoad64          -- `movq (%p), %xmm0` or `movlps (%p), %xmm0`
  | sseStore64         -- `movlps %xmm0, (%p)`
  | x87Load64          -- `fildll (%p)`
  | x87Store64         -- `fistpll (%p)`
  deriving DecidableEq, Repr

/-- `X86TargetLowering` on `x86_64`. `redZone` is `has128ByteRedZone`. -/
def x86_64Isel (redZone : Bool) : LlvmAtomic → List X86Inst
  | .loadAtomic _ => [.movLoad]
  | .storeAtomic .seqCst => [.xchg]
  | .storeAtomic _ => [.movStore]
  | .atomicrmw .xchg _ => [.xchg]
  | .atomicrmw .add _ => [.lockXadd]
  | .atomicrmw .and _ => [.movLoad, .lockCmpxchg]
  | .cmpxchg _ _ _ => [.lockCmpxchg]
  | .fence false .seqCst => [.lockOrSp (if redZone then -64 else 0)]
  | .fence _ _ => []

/-- Vector/FPU feature level of an `i686` compilation. -/
inductive I686Simd where
  | sse2       -- default `pentium4`
  | sse1Only   -- `-C target-feature=-sse2`
  | x87Only    -- `-C target-feature=-sse2,-sse`
  deriving DecidableEq, Repr

/-- The two measured `i686` configurations, indexed by "is SSE2 enabled". -/
def I686Simd.ofSse2 : Bool → I686Simd
  | true => .sse2
  | false => .x87Only

/-- `X86TargetLowering` on `i686`; `wide` selects a 64-bit operand. -/
def i686Isel (simd : I686Simd) (wide : Bool) : LlvmAtomic → List X86Inst
  | .loadAtomic _ =>
      match wide, simd with
      | false, _ => [.movLoad]
      | true, .x87Only => [.x87Load64]
      | true, _ => [.sseLoad64]
  | .storeAtomic o =>
      match wide, simd, o with
      | false, _, .seqCst => [.xchg]
      | false, _, _ => [.movStore]
      | true, .x87Only, .seqCst => [.x87Store64, .lockOrSp 0]
      | true, .x87Only, _ => [.x87Store64]
      | true, _, .seqCst => [.sseStore64, .lockOrSp 0]
      | true, _, _ => [.sseStore64]
  | .atomicrmw k _ =>
      match wide, k with
      | true, _ => [.movLoad, .movLoad, .lockCmpxchg8b]
      | false, .xchg => [.xchg]
      | false, .add => [.lockXadd]
      | false, .and => [.movLoad, .lockCmpxchg]
  | .cmpxchg _ _ _ =>
      match wide with
      | true => [.lockCmpxchg8b]
      | false => [.lockCmpxchg]
  | .fence false .seqCst =>
      match simd with
      | .sse2 => [.mfence]
      | _ => [.lockOrSp 0]
  | .fence _ _ => []

/-- AArch64 feature profiles. -/
inductive FeatureProfile where
  | v80Inline     -- `+v8a,-outline-atomics`: inline LL/SC loops
  | v80Outlined   -- `+v8a,+outline-atomics` (the `aarch64-unknown-linux-gnu` default)
  | lse           -- `+lse`
  | lseRcpc       -- `+lse,+rcpc`
  deriving DecidableEq, Repr

/-- AArch64 instruction classes. `acq`/`rel` are the acquire and release variants of an instruction. -/
inductive A64Inst where
  | ldr | ldar | ldapr | str | stlr
  | loadExcl (acq : Bool)                       -- `ldxr` / `ldaxr`
  | storeExcl (rel : Bool)                      -- `stxr` / `stlxr`
  | clrex
  | lseCas (acq rel : Bool)                     -- `cas` / `casa` / `casl` / `casal`
  | lseRmw (k : RmwKind) (acq rel : Bool)       -- `swp*` / `ldadd*` / `ldclr*`
  | outlineCas (acq rel : Bool)                 -- `bl __aarch64_cas<N>_<suffix>`
  | outlineRmw (k : RmwKind) (acq rel : Bool)   -- `bl __aarch64_{swp,ldadd,ldclr}<N>_<suffix>`
  | dmbIsh | dmbIshld
  deriving DecidableEq, Repr

/-- `AArch64TargetLowering` plus the `AArch64InstrAtomics.td` patterns. -/
def a64Isel (p : FeatureProfile) : LlvmAtomic → List A64Inst
  | .loadAtomic .monotonic => [.ldr]
  | .loadAtomic .acquire =>
      match p with
      | .lseRcpc => [.ldapr]
      | _ => [.ldar]
  | .loadAtomic _ => [.ldar]
  | .storeAtomic .monotonic => [.str]
  | .storeAtomic _ => [.stlr]
  | .atomicrmw k o =>
      match p with
      | .v80Inline => [.loadExcl o.acq, .storeExcl o.rel]
      | .v80Outlined => [.outlineRmw k o.acq o.rel]
      | _ => [.lseRmw k o.acq o.rel]
  | .cmpxchg _ s f =>
      match p with
      | .v80Inline => [.loadExcl (s.acq || f.acq), .storeExcl s.rel, .clrex]
      | .v80Outlined => [.outlineCas (s.acq || f.acq) s.rel]
      | _ => [.lseCas (s.acq || f.acq) s.rel]
  | .fence true _ => []
  | .fence false .acquire => [.dmbIshld]
  | .fence false _ => [.dmbIsh]

/-- s390x instruction classes (`l`/`lg`/`llgf`, `st`/`stg`, `cs`/`csg`, `bcr 15,%r0`). -/
inductive S390Inst where
  | load | store | cs | bcr15
  deriving DecidableEq, Repr

/-- `SystemZTargetLowering` for the `z10` baseline. -/
def s390xIsel : LlvmAtomic → List S390Inst
  | .loadAtomic _ => [.load]
  | .storeAtomic .seqCst => [.store, .bcr15]
  | .storeAtomic _ => [.store]
  | .atomicrmw _ _ => [.load, .cs]
  | .cmpxchg _ _ _ => [.cs]
  | .fence false .seqCst => [.bcr15]
  | .fence _ _ => []

def lowerX86_64 (redZone : Bool) (op : MirAtomicOp) : List X86Inst :=
  x86_64Isel redZone (mirToLlvm op)

def lowerI686 (simd : I686Simd) (wide : Bool) (op : MirAtomicOp) : List X86Inst :=
  i686Isel simd wide (mirToLlvm op)

def lowerA64 (p : FeatureProfile) (op : MirAtomicOp) : List A64Inst :=
  a64Isel p (mirToLlvm op)

def lowerS390x (op : MirAtomicOp) : List S390Inst :=
  s390xIsel (mirToLlvm op)

/-- Store-buffer-level view shared by the x86 family and s390x. -/
inductive TsoOp where
  | rd            -- plain read of the operand location
  | wr            -- plain (buffered) write of the operand location
  | lockedRmw     -- locked read-modify-write of the operand location
  | lockedStack   -- locked read-modify-write of a thread-private stack slot
  | fullFence     -- `mfence` / `bcr 15,%r0`
  deriving DecidableEq, Repr

def X86Inst.toTso : X86Inst → TsoOp
  | .movLoad | .sseLoad64 | .x87Load64 => .rd
  | .movStore | .sseStore64 | .x87Store64 => .wr
  | .xchg | .lockXadd | .lockCmpxchg | .lockCmpxchg8b => .lockedRmw
  | .lockOrSp _ => .lockedStack
  | .mfence => .fullFence

def S390Inst.toTso : S390Inst → TsoOp
  | .load => .rd
  | .store => .wr
  | .cs => .lockedRmw
  | .bcr15 => .fullFence

/-- Every store-buffer configuration covered by the tables. -/
inductive TsoCfg where
  | x86_64 (redZone : Bool)
  | i686 (simd : I686Simd) (wide : Bool)
  | s390x
  deriving DecidableEq, Repr

def TsoCfg.lower : TsoCfg → MirAtomicOp → List TsoOp
  | .x86_64 rz, op => List.map X86Inst.toTso (lowerX86_64 rz op)
  | .i686 s w, op => List.map X86Inst.toTso (lowerI686 s w op)
  | .s390x, op => List.map S390Inst.toTso (lowerS390x op)

/-- Split a `TsoCfg` into its nine concrete configurations and run a tactic on each. -/
syntax "tso_cases " ident " => " tacticSeq : tactic
macro_rules
  | `(tactic| tso_cases $c:ident => $t:tacticSeq) =>
    `(tactic| (cases $c:ident with
        | x86_64 rz => cases rz <;> ($t)
        | i686 s w => cases s <;> cases w <;> ($t)
        | s390x => ($t)))

/-! ## 5. Table-level theorems (all operations, orderings and configurations) -/

def TsoOp.isBarrier : TsoOp → Bool
  | .lockedRmw | .lockedStack | .fullFence => true
  | _ => false

noncomputable def anyL {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => p x || anyL p xs

/-- The sequence contains an instruction that drains the store buffer. -/
def hasBarrier (l : List TsoOp) : Bool := anyL TsoOp.isBarrier l

/-- The sequence contains a locked update of the operand location. -/
def hasLockedRmw (l : List TsoOp) : Bool :=
  anyL (fun o => match o with | .lockedRmw => true | _ => false) l

/-- A compiler fence emits no machine instruction on any store-buffer configuration. -/
theorem tso_compilerFence_emits_nothing (c : TsoCfg) (o : RustOrdering) :
    c.lower (.compilerFence o) = [] := by
  tso_cases c => (cases o <;> rfl)

/-- On store-buffer targets only the `SeqCst` fence emits an instruction. -/
theorem tso_weak_fence_emits_nothing (c : TsoCfg) (o : RustOrdering) (h : o.sc = false) :
    c.lower (.fence o) = [] := by
  tso_cases c => (cases o <;> first | rfl | exact Bool.noConfusion h)

theorem tso_seqcst_fence_has_barrier (c : TsoCfg) :
    hasBarrier (c.lower (.fence .seqCst)) = true := by
  tso_cases c => rfl

theorem tso_seqcst_store_has_barrier (c : TsoCfg) :
    hasBarrier (c.lower (.store .seqCst)) = true := by
  tso_cases c => rfl

/-- The barrier is exactly the price of `SeqCst`: weaker stores and every load emit none. -/
theorem tso_weaker_access_has_no_barrier (c : TsoCfg) :
    hasBarrier (c.lower (.store .relaxed)) = false ∧
    hasBarrier (c.lower (.store .release)) = false ∧
    (∀ o, hasBarrier (c.lower (.load o)) = false) := by
  tso_cases c => (refine ⟨rfl, rfl, ?_⟩; intro o; cases o <;> rfl)

/-- Every read-modify-write and compare-exchange contains a locked update, whatever its ordering. -/
theorem tso_rmw_and_cas_are_locked (c : TsoCfg) (k : RmwKind) (o s f : RustOrdering) :
    hasLockedRmw (c.lower (.rmw k o)) = true ∧
    hasLockedRmw (c.lower (.casStrong s f)) = true ∧
    hasLockedRmw (c.lower (.casWeak s f)) = true := by
  tso_cases c => (cases k <;> cases o <;> cases s <;> cases f <;> exact ⟨rfl, rfl, rfl⟩)

/-- Strength of an AArch64 load instruction: `ldr < ldapr < ldar`. -/
def a64ReadStrength : List A64Inst → Nat
  | [.ldr] => 0
  | [.ldapr] => 1
  | [.ldar] => 2
  | _ => 0

/-- Strength of an AArch64 store instruction: `str < stlr`. -/
def a64WriteStrength : List A64Inst → Nat
  | [.str] => 0
  | [.stlr] => 1
  | _ => 0

/-- Ordering preservation for loads: a stronger valid ordering never selects a weaker instruction. -/
theorem a64_load_monotone (p : FeatureProfile) (o₁ o₂ : RustOrdering) :
    o₁.le o₂ = true → (MirAtomicOp.load o₁).valid = true → (MirAtomicOp.load o₂).valid = true →
    a64ReadStrength (lowerA64 p (.load o₁)) ≤ a64ReadStrength (lowerA64 p (.load o₂)) := by
  cases p <;> cases o₁ <;> cases o₂ <;> decide

/-- Ordering preservation for stores. -/
theorem a64_store_monotone (p : FeatureProfile) (o₁ o₂ : RustOrdering) :
    o₁.le o₂ = true → (MirAtomicOp.store o₁).valid = true → (MirAtomicOp.store o₂).valid = true →
    a64WriteStrength (lowerA64 p (.store o₁)) ≤ a64WriteStrength (lowerA64 p (.store o₂)) := by
  cases p <;> cases o₁ <;> cases o₂ <;> decide

/-- `load(SeqCst)` selects `ldar` on every profile; `ldapr` is selected only for
`load(Acquire)` and only when RCpc is enabled. -/
theorem a64_load_selection (p : FeatureProfile) :
    lowerA64 p (.load .seqCst) = [.ldar] ∧
    lowerA64 p (.load .relaxed) = [.ldr] ∧
    lowerA64 p (.load .acquire) = (if p = .lseRcpc then [.ldapr] else [.ldar]) := by
  cases p <;> exact ⟨rfl, rfl, rfl⟩

theorem a64_store_selection (p : FeatureProfile) :
    lowerA64 p (.store .relaxed) = [.str] ∧
    lowerA64 p (.store .release) = [.stlr] ∧
    lowerA64 p (.store .seqCst) = [.stlr] := by
  cases p <;> exact ⟨rfl, rfl, rfl⟩

theorem a64_fence_selection (p : FeatureProfile) :
    lowerA64 p (.fence .acquire) = [.dmbIshld] ∧
    lowerA64 p (.fence .release) = [.dmbIsh] ∧
    lowerA64 p (.fence .acqRel) = [.dmbIsh] ∧
    lowerA64 p (.fence .seqCst) = [.dmbIsh] ∧
    (∀ o, lowerA64 p (.compilerFence o) = []) := by
  cases p <;> (refine ⟨rfl, rfl, rfl, rfl, ?_⟩; intro o; cases o <;> rfl)

/-- Acquire and release variant bits of the atomic-update primitive in a lowered sequence. -/
def a64UpdateBits : List A64Inst → Option (Bool × Bool)
  | [.loadExcl a, .storeExcl r] => some (a, r)
  | [.loadExcl a, .storeExcl r, .clrex] => some (a, r)
  | [.lseRmw _ a r] => some (a, r)
  | [.lseCas a r] => some (a, r)
  | [.outlineRmw _ a r] => some (a, r)
  | [.outlineCas a r] => some (a, r)
  | _ => none

/-- Every read-modify-write is an atomic-update primitive whose acquire/release variant matches
the ordering exactly (`SeqCst` selects the same `…al` variant as `AcqRel`). -/
theorem a64_rmw_bits (p : FeatureProfile) (k : RmwKind) (o : RustOrdering) :
    a64UpdateBits (lowerA64 p (.rmw k o)) = some (o.acq, o.rel) := by
  cases p <;> cases k <;> cases o <;> rfl

/-- Compare-exchange: acquire iff the success or failure ordering acquires, release iff the
success ordering releases; the weak flag does not change the selected variant. -/
theorem a64_cas_bits (p : FeatureProfile) (s f : RustOrdering) :
    a64UpdateBits (lowerA64 p (.casStrong s f)) = some (s.acq || f.acq, s.rel) ∧
    a64UpdateBits (lowerA64 p (.casWeak s f)) = some (s.acq || f.acq, s.rel) := by
  cases p <;> cases s <;> cases f <;> exact ⟨rfl, rfl⟩

/-- A single-event memory access: `load o` when `isLoad`, otherwise `store o`. -/
def accessOp (isLoad : Bool) (o : RustOrdering) : MirAtomicOp :=
  match isLoad with
  | true => .load o
  | false => .store o

/-- Same-thread ordering that RC11 needs the hardware to keep between an earlier access
`(l₁, o₁)` and a later access `(l₂, o₂)`: an acquiring read stays before what follows it, a
releasing write stays after what precedes it, and a `SeqCst` write stays before a later
`SeqCst` read. -/
def rc11Requires (l₁ : Bool) (o₁ : RustOrdering) (l₂ : Bool) (o₂ : RustOrdering) : Bool :=
  (l₁ && o₁.acq) || (!l₂ && o₂.rel) || (!l₁ && o₁.sc && l₂ && o₂.sc)

/-- Direct barrier-ordered-before edge between two AArch64 access instructions (the three
attribute-only clauses of `bob`: `[W & L]; po; [R & A]`, `[(R & A) | (R & Q)]; po; [M]`,
`[M]; po; [W & L]`). -/
def a64Direct : List A64Inst → List A64Inst → Bool
  | [.stlr], [.ldar] => true
  | [.ldar], [_] => true
  | [.ldapr], [_] => true
  | [_], [.stlr] => true
  | _, _ => false

/-- Edge-level soundness on AArch64: every ordering RC11 requires between two valid accesses is
a direct barrier-ordered-before edge between the selected instructions, on every profile. -/
theorem a64_required_order_is_barrier_ordered (p : FeatureProfile)
    (l₁ : Bool) (o₁ : RustOrdering) (l₂ : Bool) (o₂ : RustOrdering) :
    (accessOp l₁ o₁).valid = true → (accessOp l₂ o₂).valid = true →
    rc11Requires l₁ o₁ l₂ o₂ = true →
    a64Direct (lowerA64 p (accessOp l₁ o₁)) (lowerA64 p (accessOp l₂ o₂)) = true := by
  cases p <;> cases l₁ <;> cases o₁ <;> cases l₂ <;> cases o₂ <;> decide

/-- Direct order between two store-buffer sequences: everything except a plain write followed
by a plain read is kept (`po_ghb`, `implied` or `mfence`). -/
def tsoDirect : List TsoOp → List TsoOp → Bool
  | [.wr], .rd :: _ => false
  | _, _ => true

/-- Edge-level soundness on the store-buffer configurations. -/
theorem tso_required_order_is_kept (c : TsoCfg)
    (l₁ : Bool) (o₁ : RustOrdering) (l₂ : Bool) (o₂ : RustOrdering) :
    (accessOp l₁ o₁).valid = true → (accessOp l₂ o₂).valid = true →
    rc11Requires l₁ o₁ l₂ o₂ = true →
    tsoDirect (c.lower (accessOp l₁ o₁)) (c.lower (accessOp l₂ o₂)) = true := by
  tso_cases c => (cases l₁ <;> cases o₁ <;> cases l₂ <;> cases o₂ <;> decide)

/-! ## 6. Candidate executions -/

/-- Finite relations on event identifiers. -/
abbrev Rel := Nat → Nat → Bool

/-- Transitive closure. -/
inductive TC (r : Rel) : Nat → Nat → Prop where
  | base {a b : Nat} : r a b = true → TC r a b
  | step {a b c : Nat} : r a b = true → TC r b c → TC r a c

def Acyclic (r : Rel) : Prop := ∀ a, ¬ TC r a a

theorem TC.trans {r : Rel} {a b c : Nat} (h₁ : TC r a b) (h₂ : TC r b c) : TC r a c := by
  induction h₁ with
  | base e => exact TC.step e h₂
  | step e _ ih => exact TC.step e (ih h₂)

theorem TC.mono {r s : Rel} (h : ∀ a b, r a b = true → s a b = true) {a b : Nat}
    (t : TC r a b) : TC s a b := by
  induction t with
  | base e => exact TC.base (h _ _ e)
  | step e _ ih => exact TC.step (h _ _ e) ih

/-- A closed walk `a → b → c → d → a` (with `a →⁺ b` and `c →⁺ d`) refutes acyclicity. -/
theorem cycle4 {r : Rel} {a b c d : Nat}
    (h₁ : TC r a b) (h₂ : r b c = true) (h₃ : TC r c d) (h₄ : r d a = true) : ¬ Acyclic r :=
  fun hac => hac a (TC.trans h₁ (TC.step h₂ (TC.trans h₃ (TC.base h₄))))

/-- A closed walk with three fixed and three dynamic edges. -/
theorem cycle6 {r : Rel} {a b c d e f : Nat}
    (h₁ : TC r a b) (h₂ : r b c = true) (h₃ : r c d = true)
    (h₄ : TC r d e) (h₅ : r e f = true) (h₆ : r f a = true) : ¬ Acyclic r :=
  fun hac => hac a
    (TC.trans h₁ (TC.step h₂ (TC.step h₃ (TC.trans h₄ (TC.step h₅ (TC.base h₆))))))

/-- Bounded reachability: a path of at most `k + 1` edges through nodes below `n`. -/
noncomputable def reach (r : Rel) (n : Nat) : Nat → Nat → Nat → Bool
  | 0, a, b => r a b
  | k + 1, a, b => r a b || anyBelow (fun m => r a m && reach r n k m b) n

theorem tc_of_reach {r : Rel} {n : Nat} :
    ∀ {k a b : Nat}, reach r n k a b = true → TC r a b
  | 0, _, _, h => TC.base h
  | k + 1, a, b, h => by
      have h' : (r a b || anyBelow (fun m => r a m && reach r n k m b) n) = true := h
      rcases or_cases h' with hab | hmid
      · exact TC.base hab
      · have ⟨m, _, hm⟩ := anyBelow_spec hmid
        exact TC.step (and_left hm) (tc_of_reach (and_right hm))

/-- `rank` strictly increases along every edge below `n`. -/
def rankOk (n : Nat) (r : Rel) (rank : Nat → Nat) : Bool :=
  allBelow (fun a => allBelow (fun b => !(r a b) || Nat.blt (rank a) (rank b)) n) n

/-- A strictly increasing rank certifies acyclicity. -/
theorem acyclic_of_rank {n : Nat} {r : Rel} (rank : Nat → Nat)
    (hdom : ∀ a b, r a b = true → a < n ∧ b < n)
    (hok : rankOk n r rank = true) : Acyclic r := by
  have hstep : ∀ a b, r a b = true → rank a < rank b := by
    intro a b hab
    have ⟨ha, hb⟩ := hdom a b hab
    have h1 := allBelow_spec (allBelow_spec hok a ha) b hb
    have h2 : (!(r a b) || Nat.blt (rank a) (rank b)) = true := h1
    rw [hab] at h2
    exact Nat.le_of_ble_eq_true h2
  have hlt : ∀ a b, TC r a b → rank a < rank b := by
    intro a b t
    induction t with
    | base e => exact hstep _ _ e
    | step e _ ih => exact Nat.lt_trans (hstep _ _ e) ih
  intro a t
  exact Nat.lt_irrefl _ (hlt a a t)

/-- Event kinds: read, write, fence. -/
inductive Kind where
  | R | W | F
  deriving DecidableEq, Repr

def Kind.isR : Kind → Bool
  | .R => true
  | _ => false

def Kind.isW : Kind → Bool
  | .W => true
  | _ => false

def Kind.isF : Kind → Bool
  | .F => true
  | _ => false

def Kind.isM : Kind → Bool
  | .F => false
  | _ => true

/-- An event of a candidate execution. Identifiers are positions in the event list; the list
is thread-major and in program order within each thread. -/
structure Ev (A : Type) where
  tid : Nat
  kind : Kind
  loc : Nat
  attr : A
  /-- Index of the litmus instruction the event was generated from. -/
  src : Nat
  /-- The event is that instruction's own access (not an auxiliary event). -/
  main : Bool

noncomputable def nth {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth xs n

theorem nth_some_lt {α : Type} :
    ∀ {l : List α} {n : Nat} {x : α}, nth l n = some x → n < l.length := by
  intro l
  induction l with
  | nil =>
      intro n x h
      have h' : (none : Option α) = some x := h
      cases h'
  | cons y ys ih =>
      intro n x h
      cases n with
      | zero => exact Nat.zero_lt_succ _
      | succ m => exact Nat.succ_lt_succ (ih h)

section Graph

variable {A : Type}

/-- Lift a predicate on two events to a relation on identifiers (false outside the graph). -/
def pairP (G : List (Ev A)) (p : Ev A → Ev A → Bool) (a b : Nat) : Bool :=
  match nth G a with
  | none => false
  | some x =>
    match nth G b with
    | none => false
    | some y => p x y

theorem pairP_dom {G : List (Ev A)} {p : Ev A → Ev A → Bool} {a b : Nat}
    (h : pairP G p a b = true) : a < G.length ∧ b < G.length := by
  unfold pairP at h
  cases hx : nth G a with
  | none => rw [hx] at h; exact Bool.noConfusion h
  | some x =>
    cases hy : nth G b with
    | none => rw [hx, hy] at h; exact Bool.noConfusion h
    | some y => exact ⟨nth_some_lt hx, nth_some_lt hy⟩

/-- Program order: same thread, earlier in the list. -/
def po (G : List (Ev A)) (a b : Nat) : Bool :=
  Nat.blt a b && pairP G (fun x y => Nat.beq x.tid y.tid) a b

theorem po_dom {G : List (Ev A)} {a b : Nat} (h : po G a b = true) :
    a < G.length ∧ b < G.length :=
  pairP_dom (and_right h)

/-- Different threads. -/
def ext (G : List (Ev A)) (a b : Nat) : Bool :=
  pairP G (fun x y => !Nat.beq x.tid y.tid) a b

/-- `a` and `b` are separated in program order by an event satisfying `p`
(`fencerel` in the cat library: `(po & (_ * B)); po`). -/
def between (G : List (Ev A)) (p : Ev A → Bool) (a b : Nat) : Bool :=
  anyBelow (fun f => po G a f && po G f b && pairP G (fun x _ => p x) f f) G.length

theorem between_dom {G : List (Ev A)} {p : Ev A → Bool} {a b : Nat}
    (h : between G p a b = true) : a < G.length ∧ b < G.length := by
  have ⟨f, _, hf⟩ := anyBelow_spec h
  exact ⟨(po_dom (and_left (and_left hf))).1, (po_dom (and_right (and_left hf))).2⟩

/-- A read and a write on the same location. -/
def rwPair (G : List (Ev A)) (r w : Nat) : Bool :=
  pairP G (fun x y => x.kind.isR && y.kind.isW && Nat.beq x.loc y.loc) r w

/-- A write and a read on the same location. -/
def wrPair (G : List (Ev A)) (w r : Nat) : Bool :=
  pairP G (fun x y => x.kind.isW && y.kind.isR && Nat.beq x.loc y.loc) w r

def optIs : Option Nat → Nat → Bool
  | some v, w => Nat.beq v w
  | none, _ => false

/-- Reads-from. `rf r = some w` means read `r` takes its value from write `w`; `rf r = none`
means it reads the initial value. -/
def rfEdge (G : List (Ev A)) (rf : Nat → Option Nat) (w r : Nat) : Bool :=
  wrPair G w r && optIs (rf r) w

/-- From-read out of an initial-value read. With at most one non-initial write per location
(`singleWriter`), this is the whole of `fr`, and `co` between non-initial writes is empty. -/
def frInit (G : List (Ev A)) (rf : Nat → Option Nat) (r w : Nat) : Bool :=
  rwPair G r w && (rf r).isNone

theorem rfEdge_intro {G : List (Ev A)} {rf : Nat → Option Nat} {w r : Nat}
    (h : wrPair G w r = true) (hr : rf r = some w) : rfEdge G rf w r = true := by
  unfold rfEdge
  rw [hr]
  exact and_intro h (Nat.beq_refl w)

theorem frInit_intro {G : List (Ev A)} {rf : Nat → Option Nat} {r w : Nat}
    (h : rwPair G r w = true) (hr : rf r = none) : frInit G rf r w = true := by
  unfold frInit
  rw [hr]
  exact and_intro h rfl

theorem rfEdge_dom {G : List (Ev A)} {rf : Nat → Option Nat} {w r : Nat}
    (h : rfEdge G rf w r = true) : w < G.length ∧ r < G.length :=
  pairP_dom (and_left h)

theorem frInit_dom {G : List (Ev A)} {rf : Nat → Option Nat} {r w : Nat}
    (h : frInit G rf r w = true) : r < G.length ∧ w < G.length :=
  pairP_dom (and_left h)

/-- Side condition of the litmus layer: no two distinct write events share a location. -/
def singleWriter (G : List (Ev A)) : Bool :=
  allBelow (fun a => allBelow (fun b =>
    Nat.beq a b || !pairP G (fun x y => x.kind.isW && y.kind.isW && Nat.beq x.loc y.loc) a b)
    G.length) G.length

noncomputable def findMain : List (Ev A) → Nat → Nat → Nat
  | [], _, pos => pos
  | e :: es, i, pos =>
    match e.main && Nat.beq e.src i with
    | true => pos
    | false => findMain es i (pos + 1)

/-- Identifier of the event carrying the access of litmus instruction `i`. -/
def mainIdx (G : List (Ev A)) (i : Nat) : Nat := findMain G i 0

/-- Rank used for the "allowed" witnesses: writes after reads and fences. -/
def writesLast (G : List (Ev A)) (a : Nat) : Nat :=
  match nth G a with
  | some e => (match e.kind with | .W => 1 | _ => 0)
  | none => 0

end Graph

/-- One straight-line litmus instruction. -/
structure LInstr where
  tid : Nat
  op : MirAtomicOp
  loc : Nat

abbrev Litmus := List LInstr

noncomputable def appendL {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: appendL xs ys

noncomputable def flatMapL {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => appendL (f x) (flatMapL f xs)

/-- Generate events instruction by instruction, numbering instructions from `i`. -/
noncomputable def eventsFrom {A : Type} (gen : Nat → LInstr → List (Ev A)) : Nat → Litmus → List (Ev A)
  | _, [] => []
  | i, x :: xs => appendL (gen i x) (eventsFrom gen (i + 1) xs)

/-- Thread-private stack slot touched by `lock orl $0, d(%sp)`. -/
def stackLoc (tid : Nat) : Nat := 1000 + tid

/-! ## 7. Store-buffer model (herd `x86tso.cat`) -/

inductive TsoAttr where
  | plain | locked | fence
  deriving DecidableEq, Repr

def tsoOpEvents (i : Nat) (x : LInstr) : TsoOp → List (Ev TsoAttr)
  | .rd => [⟨x.tid, .R, x.loc, .plain, i, true⟩]
  | .wr => [⟨x.tid, .W, x.loc, .plain, i, true⟩]
  | .lockedRmw =>
      [⟨x.tid, .R, x.loc, .locked, i, false⟩, ⟨x.tid, .W, x.loc, .locked, i, true⟩]
  | .lockedStack =>
      [⟨x.tid, .R, stackLoc x.tid, .locked, i, false⟩,
       ⟨x.tid, .W, stackLoc x.tid, .locked, i, false⟩]
  | .fullFence => [⟨x.tid, .F, 0, .fence, i, false⟩]

namespace Tso

/-- Events of a litmus program compiled with `lower`. -/
def events (lower : MirAtomicOp → List TsoOp) : Litmus → List (Ev TsoAttr) :=
  eventsFrom (fun i x => flatMapL (tsoOpEvents i x) (lower x.op)) 0

def isLocked (x : Ev TsoAttr) : Bool :=
  match x.attr with
  | .locked => true
  | _ => false

/-- `let po_ghb = WW(po) | RM(po)`. -/
def ppo (G : List (Ev TsoAttr)) (a b : Nat) : Bool :=
  po G a b &&
    pairP G (fun x y => (x.kind.isW && y.kind.isW) || (x.kind.isR && y.kind.isM)) a b

/-- `let implied = MA(poWR) | AM(poWR)`: a write-to-read pair with a locked endpoint. -/
def implied (G : List (Ev TsoAttr)) (a b : Nat) : Bool :=
  po G a b && pairP G (fun x y => x.kind.isW && y.kind.isR && (isLocked x || isLocked y)) a b

/-- `let mfence = fencerel(MFENCE)`. -/
def mfence (G : List (Ev TsoAttr)) (a b : Nat) : Bool :=
  between G (fun x => x.kind.isF) a b

/-- The part of `ghb` that does not depend on the reads-from witness. -/
def fixed (G : List (Ev TsoAttr)) (a b : Nat) : Bool :=
  mfence G a b || implied G a b || ppo G a b

/-- `let ghb = mfence | implied | po_ghb | rfe | fr | co` (with `co` empty, see `frInit`). -/
def ghb (G : List (Ev TsoAttr)) (rf : Nat → Option Nat) (a b : Nat) : Bool :=
  fixed G a b || (rfEdge G rf a b && ext G a b) || frInit G rf a b

def poLoc (G : List (Ev TsoAttr)) (a b : Nat) : Bool :=
  po G a b && pairP G (fun x y => x.kind.isM && y.kind.isM && Nat.beq x.loc y.loc) a b

/-- `po-loc | amo | com` of the uniproc check (`amo ⊆ po-loc` here). -/
def uni (G : List (Ev TsoAttr)) (rf : Nat → Option Nat) (a b : Nat) : Bool :=
  poLoc G a b || rfEdge G rf a b || frInit G rf a b

/-- `acyclic po-loc | amo | com` and `acyclic ghb as tso`. The third requirement,
`empty rmw & (fre;coe)`, holds vacuously because `coe` is empty under `singleWriter`. -/
structure Consistent (G : List (Ev TsoAttr)) (rf : Nat → Option Nat) : Prop where
  uniproc : Acyclic (uni G rf)
  tso : Acyclic (ghb G rf)

theorem fixed_dom {G : List (Ev TsoAttr)} {a b : Nat} (h : fixed G a b = true) :
    a < G.length ∧ b < G.length := by
  rcases or_cases h with h1 | h3
  · rcases or_cases h1 with hm | hi
    · exact between_dom hm
    · exact po_dom (and_left hi)
  · exact po_dom (and_left h3)

theorem ghb_dom {G : List (Ev TsoAttr)} {rf : Nat → Option Nat} {a b : Nat}
    (h : ghb G rf a b = true) : a < G.length ∧ b < G.length := by
  rcases or_cases h with h1 | h3
  · rcases or_cases h1 with hf | hr
    · exact fixed_dom hf
    · exact rfEdge_dom (and_left hr)
  · exact frInit_dom h3

theorem uni_dom {G : List (Ev TsoAttr)} {rf : Nat → Option Nat} {a b : Nat}
    (h : uni G rf a b = true) : a < G.length ∧ b < G.length := by
  rcases or_cases h with h1 | h3
  · rcases or_cases h1 with hp | hr
    · exact po_dom (and_left hp)
    · exact rfEdge_dom hr
  · exact frInit_dom h3

theorem ghb_of_fixed {G : List (Ev TsoAttr)} {rf : Nat → Option Nat} (a b : Nat)
    (h : fixed G a b = true) : ghb G rf a b = true :=
  or_inl (or_inl h)

theorem ghb_of_fr {G : List (Ev TsoAttr)} {rf : Nat → Option Nat} {r w : Nat}
    (h : rwPair G r w = true) (hr : rf r = none) : ghb G rf r w = true :=
  or_inr (frInit_intro h hr)

theorem ghb_of_rfe {G : List (Ev TsoAttr)} {rf : Nat → Option Nat} {w r : Nat}
    (h : wrPair G w r = true) (hx : ext G w r = true) (hr : rf r = some w) :
    ghb G rf w r = true :=
  or_inl (or_inr (and_intro (rfEdge_intro h hr) hx))

/-- Store buffering: if each thread's write is `ghb`-before its own read, the two reads cannot
both return the initial value. -/
theorem sb_forbidden (G : List (Ev TsoAttr)) (rf : Nat → Option Nat) {w0 r0 w1 r1 : Nat}
    (p0 : reach (fixed G) G.length 3 w0 r0 = true) (f0 : rwPair G r0 w1 = true)
    (p1 : reach (fixed G) G.length 3 w1 r1 = true) (f1 : rwPair G r1 w0 = true)
    (hc : Consistent G rf) : ¬ (rf r0 = none ∧ rf r1 = none) := fun ⟨h0, h1⟩ =>
  cycle4 (TC.mono ghb_of_fixed (tc_of_reach p0)) (ghb_of_fr f0 h0)
    (TC.mono ghb_of_fixed (tc_of_reach p1)) (ghb_of_fr f1 h1) hc.tso

/-- Message passing: data write before flag write, flag read before data read. -/
theorem mp_forbidden (G : List (Ev TsoAttr)) (rf : Nat → Option Nat) {wx wy ry rx : Nat}
    (p0 : reach (fixed G) G.length 3 wx wy = true)
    (e : wrPair G wy ry = true) (x : ext G wy ry = true)
    (p1 : reach (fixed G) G.length 3 ry rx = true) (f : rwPair G rx wx = true)
    (hc : Consistent G rf) : ¬ (rf ry = some wy ∧ rf rx = none) := fun ⟨h0, h1⟩ =>
  cycle4 (TC.mono ghb_of_fixed (tc_of_reach p0)) (ghb_of_rfe e x h0)
    (TC.mono ghb_of_fixed (tc_of_reach p1)) (ghb_of_fr f h1) hc.tso

end Tso

/-! ## 8. AArch64 model (Arm `aarch64hwreqs.cat`) and the RC11 source fragment -/

inductive A64Attr where
  | plain     -- `ldr` / `str`
  | acq       -- `ldar`   (set `A`)
  | acqPC     -- `ldapr`  (set `Q`)
  | rel       -- `stlr`   (set `L`)
  | dmbFull   -- `dmb ish`
  | dmbLd     -- `dmb ishld`
  deriving DecidableEq, Repr

/-- Events of the load, store and barrier instructions. Exclusive pairs, LSE instructions and
outlined helper calls are outside the litmus layer and generate no events. -/
def a64InstEvents (i : Nat) (x : LInstr) : A64Inst → List (Ev A64Attr)
  | .ldr => [⟨x.tid, .R, x.loc, .plain, i, true⟩]
  | .ldar => [⟨x.tid, .R, x.loc, .acq, i, true⟩]
  | .ldapr => [⟨x.tid, .R, x.loc, .acqPC, i, true⟩]
  | .str => [⟨x.tid, .W, x.loc, .plain, i, true⟩]
  | .stlr => [⟨x.tid, .W, x.loc, .rel, i, true⟩]
  | .dmbIsh => [⟨x.tid, .F, 0, .dmbFull, i, false⟩]
  | .dmbIshld => [⟨x.tid, .F, 0, .dmbLd, i, false⟩]
  | _ => []

namespace A64

def events (lower : MirAtomicOp → List A64Inst) : Litmus → List (Ev A64Attr) :=
  eventsFrom (fun i x => flatMapL (a64InstEvents i x) (lower x.op)) 0

def isA (x : Ev A64Attr) : Bool :=
  x.kind.isR && (match x.attr with | .acq => true | _ => false)

def isQ (x : Ev A64Attr) : Bool :=
  x.kind.isR && (match x.attr with | .acqPC => true | _ => false)

def isL (x : Ev A64Attr) : Bool :=
  x.kind.isW && (match x.attr with | .rel => true | _ => false)

def isDmbFull (x : Ev A64Attr) : Bool :=
  match x.attr with
  | .dmbFull => true
  | _ => false

def isDmbLd (x : Ev A64Attr) : Bool :=
  match x.attr with
  | .dmbLd => true
  | _ => false

/-- Barrier-ordered-before, restricted to explicit data accesses and `dmb`:

```
[Exp & M]; po; [dmb.full]; po; [Exp & M]
[Exp & R]; po; [dmb.ld]; po; [Exp & M]
[Exp & W & L]; po; [Exp & R & A]
[(Exp & R & A) | (Exp & R & Q)]; po; [Exp & M]
[Exp & M]; po; [Exp & W & L]
```

The `dmb.st` clause and the `amo` clause have no events here (`rustc` emitted no `dmb ishst`,
and atomic-update instructions are outside the litmus layer). -/
def bob (G : List (Ev A64Attr)) (a b : Nat) : Bool :=
  po G a b &&
    (pairP G (fun x y => isL x && isA y) a b
      || pairP G (fun x y => (isA x || isQ x) && y.kind.isM) a b
      || pairP G (fun x y => x.kind.isM && isL y) a b
      || (pairP G (fun x y => x.kind.isM && y.kind.isM) a b && between G isDmbFull a b)
      || (pairP G (fun x y => x.kind.isR && y.kind.isM) a b && between G isDmbLd a b))

/-- Local memory write successor: `[Exp & M]; (po & same-loc); [Exp & W]`. -/
def lmws (G : List (Ev A64Attr)) (a b : Nat) : Bool :=
  po G a b && pairP G (fun x y => x.kind.isM && y.kind.isW && Nat.beq x.loc y.loc) a b

/-- Locally-ordered-before for dependency-free programs without atomic updates. -/
def lob (G : List (Ev A64Attr)) (a b : Nat) : Bool :=
  bob G a b || lmws G a b

/-- Ordered-before: `lob` plus the external observations `rf & ext` and `ca & ext`. -/
def ob (G : List (Ev A64Attr)) (rf : Nat → Option Nat) (a b : Nat) : Bool :=
  lob G a b || (rfEdge G rf a b && ext G a b) || (frInit G rf a b && ext G a b)

/-- Internal visibility (`coRW1-Exp`, `coWR-Exp`): a read does not take its value from a
program-order-later write, and a read after a same-location write of its own thread does not
return the initial value. `coWW-Exp` needs `co` and is vacuous under `singleWriter`. -/
def internalOk (G : List (Ev A64Attr)) (rf : Nat → Option Nat) : Bool :=
  allBelow (fun a => allBelow (fun b =>
    !(po G a b && rfEdge G rf b a) && !(po G a b && frInit G rf b a)) G.length) G.length

/-- `irreflexive ob as external` together with the internal visibility requirements. The atomicity requirement has no instances because the litmus layer has no `rmw` pairs. -/
structure Consistent (G : List (Ev A64Attr)) (rf : Nat → Option Nat) : Prop where
  internal : internalOk G rf = true
  external : Acyclic (ob G rf)

theorem lob_dom {G : List (Ev A64Attr)} {a b : Nat} (h : lob G a b = true) :
    a < G.length ∧ b < G.length := by
  rcases or_cases h with h1 | h2
  · exact po_dom (and_left h1)
  · exact po_dom (and_left h2)

theorem ob_dom {G : List (Ev A64Attr)} {rf : Nat → Option Nat} {a b : Nat}
    (h : ob G rf a b = true) : a < G.length ∧ b < G.length := by
  rcases or_cases h with h1 | h3
  · rcases or_cases h1 with hl | hr
    · exact lob_dom hl
    · exact rfEdge_dom (and_left hr)
  · exact frInit_dom (and_left h3)

theorem ob_of_lob {G : List (Ev A64Attr)} {rf : Nat → Option Nat} (a b : Nat)
    (h : lob G a b = true) : ob G rf a b = true :=
  or_inl (or_inl h)

theorem ob_of_fre {G : List (Ev A64Attr)} {rf : Nat → Option Nat} {r w : Nat}
    (h : rwPair G r w = true) (hx : ext G r w = true) (hr : rf r = none) :
    ob G rf r w = true :=
  or_inr (and_intro (frInit_intro h hr) hx)

theorem ob_of_rfe {G : List (Ev A64Attr)} {rf : Nat → Option Nat} {w r : Nat}
    (h : wrPair G w r = true) (hx : ext G w r = true) (hr : rf r = some w) :
    ob G rf w r = true :=
  or_inl (or_inr (and_intro (rfEdge_intro h hr) hx))

theorem sb_forbidden (G : List (Ev A64Attr)) (rf : Nat → Option Nat) {w0 r0 w1 r1 : Nat}
    (p0 : reach (lob G) G.length 2 w0 r0 = true)
    (f0 : rwPair G r0 w1 = true) (x0 : ext G r0 w1 = true)
    (p1 : reach (lob G) G.length 2 w1 r1 = true)
    (f1 : rwPair G r1 w0 = true) (x1 : ext G r1 w0 = true)
    (hc : Consistent G rf) : ¬ (rf r0 = none ∧ rf r1 = none) := fun ⟨h0, h1⟩ =>
  cycle4 (TC.mono ob_of_lob (tc_of_reach p0)) (ob_of_fre f0 x0 h0)
    (TC.mono ob_of_lob (tc_of_reach p1)) (ob_of_fre f1 x1 h1) hc.external

theorem mp_forbidden (G : List (Ev A64Attr)) (rf : Nat → Option Nat) {wx wy ry rx : Nat}
    (p0 : reach (lob G) G.length 2 wx wy = true)
    (e : wrPair G wy ry = true) (x : ext G wy ry = true)
    (p1 : reach (lob G) G.length 2 ry rx = true)
    (f : rwPair G rx wx = true) (xf : ext G rx wx = true)
    (hc : Consistent G rf) : ¬ (rf ry = some wy ∧ rf rx = none) := fun ⟨h0, h1⟩ =>
  cycle4 (TC.mono ob_of_lob (tc_of_reach p0)) (ob_of_rfe e x h0)
    (TC.mono ob_of_lob (tc_of_reach p1)) (ob_of_fre f xf h1) hc.external

/-- Independent reads of independent writes: reader `a → b` sees `x` then misses `y`; reader
`d → e` sees `y` then misses `x`. -/
theorem iriw_forbidden (G : List (Ev A64Attr)) (rf : Nat → Option Nat)
    {wx wy a b d e : Nat}
    (p0 : reach (lob G) G.length 2 a b = true)
    (f0 : rwPair G b wy = true) (x0 : ext G b wy = true)
    (r0 : wrPair G wy d = true) (y0 : ext G wy d = true)
    (p1 : reach (lob G) G.length 2 d e = true)
    (f1 : rwPair G e wx = true) (x1 : ext G e wx = true)
    (r1 : wrPair G wx a = true) (y1 : ext G wx a = true)
    (hc : Consistent G rf) :
    ¬ (rf a = some wx ∧ rf b = none ∧ rf d = some wy ∧ rf e = none) :=
  fun ⟨ha, hb, hd, he⟩ =>
    cycle6 (TC.mono ob_of_lob (tc_of_reach p0)) (ob_of_fre f0 x0 hb) (ob_of_rfe r0 y0 hd)
      (TC.mono ob_of_lob (tc_of_reach p1)) (ob_of_fre f1 x1 he) (ob_of_rfe r1 y1 ha) hc.external

end A64

/-- Source events: one per load, store or fence, tagged with its Rust ordering. -/
def srcInstrEvents (i : Nat) (x : LInstr) : List (Ev RustOrdering) :=
  match x.op with
  | .load o => [⟨x.tid, .R, x.loc, o, i, true⟩]
  | .store o => [⟨x.tid, .W, x.loc, o, i, true⟩]
  | .fence o => [⟨x.tid, .F, 0, o, i, false⟩]
  | _ => []

namespace RC11

def events : Litmus → List (Ev RustOrdering) := eventsFrom srcInstrEvents 0

/-- Both events are `SeqCst` memory accesses. -/
def scAccesses (G : List (Ev RustOrdering)) (a b : Nat) : Bool :=
  pairP G (fun x y => x.kind.isM && x.attr.sc && y.kind.isM && y.attr.sc) a b

/-- Both events are `SeqCst` fences. -/
def scFences (G : List (Ev RustOrdering)) (a b : Nat) : Bool :=
  pairP G (fun x y => x.kind.isF && x.attr.sc && y.kind.isF && y.attr.sc) a b

/-- `[W ⊒ rel]; rf; [R ⊒ acq]`, a sub-relation of `sw`. -/
def sw (G : List (Ev RustOrdering)) (rf : Nat → Option Nat) (a b : Nat) : Bool :=
  pairP G (fun x y => x.attr.rel && y.attr.acq) a b && rfEdge G rf a b

/-- `po | sw`; its transitive closure is a sub-relation of `hb`. -/
def hb1 (G : List (Ev RustOrdering)) (rf : Nat → Option Nat) (a b : Nat) : Bool :=
  po G a b || sw G rf a b

/-- `[E^sc]; (po | rb | sw); [E^sc]`, a sub-relation of `psc_base` (`po ⊆ scb`, `rb ⊆ scb`,
and `sw` between two accesses of one location is in `hb|loc ⊆ scb`). -/
def pscBase (G : List (Ev RustOrdering)) (rf : Nat → Option Nat) (a b : Nat) : Bool :=
  scAccesses G a b && (po G a b || frInit G rf a b || sw G rf a b)

/-- `[F^sc]; po; rb; po; [F^sc]`, a sub-relation of `psc_F = [F^sc]; (hb | hb;eco;hb); [F^sc]`. -/
def pscF (G : List (Ev RustOrdering)) (rf : Nat → Option Nat) (a b : Nat) : Bool :=
  scFences G a b &&
    anyBelow (fun r => anyBelow (fun w =>
      po G a r && frInit G rf r w && po G w b) G.length) G.length

def psc (G : List (Ev RustOrdering)) (rf : Nat → Option Nat) (a b : Nat) : Bool :=
  pscBase G rf a b || pscF G rf a b

/-- Two necessary conditions of RC11 consistency, stated over sub-relations of the RC11
relations: `irreflexive (hb ; rb)` (an instance of COHERENCE, since `rb ⊆ eco`) and
`acyclic psc` (SC). Every RC11-consistent execution satisfies both, so refuting either one
refutes RC11 consistency. -/
structure FragmentConsistent (G : List (Ev RustOrdering)) (rf : Nat → Option Nat) : Prop where
  coherence : ∀ a b, TC (hb1 G rf) a b → frInit G rf b a = true → False
  sc : Acyclic (psc G rf)

theorem psc_of_po {G : List (Ev RustOrdering)} {rf : Nat → Option Nat} {a b : Nat}
    (hs : scAccesses G a b = true) (hp : po G a b = true) : psc G rf a b = true :=
  or_inl (and_intro hs (or_inl (or_inl hp)))

theorem psc_of_rb {G : List (Ev RustOrdering)} {rf : Nat → Option Nat} {r w : Nat}
    (hs : scAccesses G r w = true) (h : rwPair G r w = true) (hr : rf r = none) :
    psc G rf r w = true :=
  or_inl (and_intro hs (or_inl (or_inr (frInit_intro h hr))))

theorem psc_of_rf {G : List (Ev RustOrdering)} {rf : Nat → Option Nat} {w r : Nat}
    (hs : scAccesses G w r = true)
    (ho : pairP G (fun x y => x.attr.rel && y.attr.acq) w r = true)
    (h : wrPair G w r = true) (hr : rf r = some w) : psc G rf w r = true :=
  or_inl (and_intro hs (or_inr (and_intro ho (rfEdge_intro h hr))))

theorem psc_of_fences {G : List (Ev RustOrdering)} {rf : Nat → Option Nat} {a b r w : Nat}
    (hs : scFences G a b = true) (h1 : po G a r = true) (h : rwPair G r w = true)
    (h2 : po G w b = true) (hr : rf r = none) : psc G rf a b = true := by
  have hrb : frInit G rf r w = true := frInit_intro h hr
  have hw : w < G.length := (frInit_dom hrb).2
  have hrlt : r < G.length := (frInit_dom hrb).1
  have inner : anyBelow (fun w => po G a r && frInit G rf r w && po G w b) G.length = true :=
    anyBelow_intro hw (and_intro (and_intro h1 hrb) h2)
  exact or_inr (and_intro hs (anyBelow_intro (p := fun r => anyBelow (fun w =>
    po G a r && frInit G rf r w && po G w b) G.length) hrlt inner))

end RC11

/-! ## 9. Litmus programs and their theorems -/

/-- Store buffering (Dekker) with every access `SeqCst`:
`T1: x.store(1, SeqCst); r0 = y.load(SeqCst)` ∥ `T2: y.store(1, SeqCst); r1 = x.load(SeqCst)`. -/
def sbSC : Litmus :=
  [⟨1, .store .seqCst, 0⟩, ⟨1, .load .seqCst, 1⟩,
   ⟨2, .store .seqCst, 1⟩, ⟨2, .load .seqCst, 0⟩]

/-- Store buffering with relaxed accesses separated by `fence(SeqCst)`. -/
def sbFence : Litmus :=
  [⟨1, .store .relaxed, 0⟩, ⟨1, .fence .seqCst, 0⟩, ⟨1, .load .relaxed, 1⟩,
   ⟨2, .store .relaxed, 1⟩, ⟨2, .fence .seqCst, 0⟩, ⟨2, .load .relaxed, 0⟩]

/-- Message passing:
`T1: data.store(1, Relaxed); flag.store(1, Release)` ∥
`T2: r0 = flag.load(Acquire); r1 = data.load(Relaxed)`. -/
def mp : Litmus :=
  [⟨1, .store .relaxed, 0⟩, ⟨1, .store .release, 1⟩,
   ⟨2, .load .acquire, 1⟩, ⟨2, .load .relaxed, 0⟩]

/-- Independent reads of independent writes; the two writers use `SeqCst` stores and the four
reads use ordering `o`. -/
def iriw (o : RustOrdering) : Litmus :=
  [⟨1, .store .seqCst, 0⟩, ⟨2, .store .seqCst, 1⟩,
   ⟨3, .load o, 0⟩, ⟨3, .load o, 1⟩,
   ⟨4, .load o, 1⟩, ⟨4, .load o, 0⟩]

/-! ### 9.1 What the Rust memory model forbids -/

/-- RC11 forbids `r0 = r1 = 0` for `sbSC` (a `psc` cycle through `po` and `rb`). -/
theorem rc11_sbSC_forbidden (rf : Nat → Option Nat)
    (hc : RC11.FragmentConsistent (RC11.events sbSC) rf) : ¬ (rf 1 = none ∧ rf 3 = none) :=
  fun ⟨h0, h1⟩ =>
    cycle4 (a := 0) (b := 1) (c := 2) (d := 3)
      (TC.base (RC11.psc_of_po (by decide) (by decide)))
      (RC11.psc_of_rb (by decide) (by decide) h0)
      (TC.base (RC11.psc_of_po (by decide) (by decide)))
      (RC11.psc_of_rb (by decide) (by decide) h1) hc.sc

/-- RC11 forbids `r0 = r1 = 0` for `sbFence` (a `psc_F` cycle between the two fences). -/
theorem rc11_sbFence_forbidden (rf : Nat → Option Nat)
    (hc : RC11.FragmentConsistent (RC11.events sbFence) rf) : ¬ (rf 2 = none ∧ rf 5 = none) :=
  fun ⟨h0, h1⟩ =>
    hc.sc 1 (TC.step
      (RC11.psc_of_fences (a := 1) (b := 4) (r := 2) (w := 3)
        (by decide) (by decide) (by decide) (by decide) h0)
      (TC.base
        (RC11.psc_of_fences (a := 4) (b := 1) (r := 5) (w := 0)
          (by decide) (by decide) (by decide) (by decide) h1)))

/-- RC11 forbids `r0 = 1, r1 = 0` for `mp` (COHERENCE: the data write happens-before the data
read, which nevertheless reads the initial value). -/
theorem rc11_mp_forbidden (rf : Nat → Option Nat)
    (hc : RC11.FragmentConsistent (RC11.events mp) rf) : ¬ (rf 2 = some 1 ∧ rf 3 = none) :=
  fun ⟨h0, h1⟩ =>
    hc.coherence 0 3
      (TC.step (b := 1) (or_inl (by decide))
        (TC.step (b := 2) (or_inr (and_intro (by decide) (rfEdge_intro (by decide) h0)))
          (TC.base (or_inl (by decide)))))
      (frInit_intro (by decide) h1)

/-- RC11 forbids the IRIW outcome when all six accesses are `SeqCst`. -/
theorem rc11_iriwSC_forbidden (rf : Nat → Option Nat)
    (hc : RC11.FragmentConsistent (RC11.events (iriw .seqCst)) rf) :
    ¬ (rf 2 = some 0 ∧ rf 3 = none ∧ rf 4 = some 1 ∧ rf 5 = none) :=
  fun ⟨ha, hb, hd, he⟩ =>
    cycle6 (a := 2) (b := 3) (c := 1) (d := 4) (e := 5) (f := 0)
      (TC.base (RC11.psc_of_po (by decide) (by decide)))
      (RC11.psc_of_rb (by decide) (by decide) hb)
      (RC11.psc_of_rf (by decide) (by decide) (by decide) hd)
      (TC.base (RC11.psc_of_po (by decide) (by decide)))
      (RC11.psc_of_rb (by decide) (by decide) he)
      (RC11.psc_of_rf (by decide) (by decide) (by decide) ha) hc.sc

/-! ### 9.2 Soundness of the real tables on every configuration -/

theorem tso_single_writer (c : TsoCfg) :
    singleWriter (Tso.events c.lower sbSC) = true ∧
    singleWriter (Tso.events c.lower sbFence) = true ∧
    singleWriter (Tso.events c.lower mp) = true := by
  tso_cases c => decide

/-- Store-buffer targets: the compiled `sbSC` cannot produce `r0 = r1 = 0`, for every reads-from
witness and all nine configurations. -/
theorem tso_sbSC_sound (c : TsoCfg) (rf : Nat → Option Nat)
    (hc : Tso.Consistent (Tso.events c.lower sbSC) rf) :
    ¬ (rf (mainIdx (Tso.events c.lower sbSC) 1) = none ∧
       rf (mainIdx (Tso.events c.lower sbSC) 3) = none) :=
  Tso.sb_forbidden _ rf
    (w0 := mainIdx (Tso.events c.lower sbSC) 0) (w1 := mainIdx (Tso.events c.lower sbSC) 2)
    (by tso_cases c => decide) (by tso_cases c => decide)
    (by tso_cases c => decide) (by tso_cases c => decide) hc

/-- Store-buffer targets: `fence(SeqCst)` restores the store-to-load order. -/
theorem tso_sbFence_sound (c : TsoCfg) (rf : Nat → Option Nat)
    (hc : Tso.Consistent (Tso.events c.lower sbFence) rf) :
    ¬ (rf (mainIdx (Tso.events c.lower sbFence) 2) = none ∧
       rf (mainIdx (Tso.events c.lower sbFence) 5) = none) :=
  Tso.sb_forbidden _ rf
    (w0 := mainIdx (Tso.events c.lower sbFence) 0) (w1 := mainIdx (Tso.events c.lower sbFence) 3)
    (by tso_cases c => decide) (by tso_cases c => decide)
    (by tso_cases c => decide) (by tso_cases c => decide) hc

/-- Store-buffer targets: release/acquire message passing needs no instruction at all. -/
theorem tso_mp_sound (c : TsoCfg) (rf : Nat → Option Nat)
    (hc : Tso.Consistent (Tso.events c.lower mp) rf) :
    ¬ (rf (mainIdx (Tso.events c.lower mp) 2) = some (mainIdx (Tso.events c.lower mp) 1) ∧
       rf (mainIdx (Tso.events c.lower mp) 3) = none) :=
  Tso.mp_forbidden _ rf
    (wx := mainIdx (Tso.events c.lower mp) 0)
    (by tso_cases c => decide) (by tso_cases c => decide) (by tso_cases c => decide)
    (by tso_cases c => decide) (by tso_cases c => decide) hc

theorem a64_single_writer (p : FeatureProfile) :
    singleWriter (A64.events (lowerA64 p) sbSC) = true ∧
    singleWriter (A64.events (lowerA64 p) sbFence) = true ∧
    singleWriter (A64.events (lowerA64 p) mp) = true := by
  cases p <;> decide

/-- AArch64, every profile: `stlr` followed by `ldar` forbids `r0 = r1 = 0` for `sbSC`. -/
theorem a64_sbSC_sound (p : FeatureProfile) (rf : Nat → Option Nat)
    (hc : A64.Consistent (A64.events (lowerA64 p) sbSC) rf) : ¬ (rf 1 = none ∧ rf 3 = none) :=
  A64.sb_forbidden _ rf (w0 := 0) (w1 := 2)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide) hc

/-- AArch64, every profile: `dmb ish` forbids `r0 = r1 = 0` for `sbFence`. -/
theorem a64_sbFence_sound (p : FeatureProfile) (rf : Nat → Option Nat)
    (hc : A64.Consistent (A64.events (lowerA64 p) sbFence) rf) : ¬ (rf 2 = none ∧ rf 5 = none) :=
  A64.sb_forbidden _ rf (w0 := 0) (w1 := 3)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide) hc

/-- AArch64, every profile (including `ldapr` under RCpc): message passing is preserved. -/
theorem a64_mp_sound (p : FeatureProfile) (rf : Nat → Option Nat)
    (hc : A64.Consistent (A64.events (lowerA64 p) mp) rf) : ¬ (rf 2 = some 1 ∧ rf 3 = none) :=
  A64.mp_forbidden _ rf (wx := 0)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide) hc

/-- AArch64, every profile: IRIW with `SeqCst` loads is forbidden. -/
theorem a64_iriwSC_sound (p : FeatureProfile) (rf : Nat → Option Nat)
    (hc : A64.Consistent (A64.events (lowerA64 p) (iriw .seqCst)) rf) :
    ¬ (rf 2 = some 0 ∧ rf 3 = none ∧ rf 4 = some 1 ∧ rf 5 = none) :=
  A64.iriw_forbidden _ rf
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
    (by cases p <;> decide) (by cases p <;> decide) (by cases p <;> decide)
    (by cases p <;> decide) hc

/-- Non-vacuity: the models do allow the sequential outcomes of `sbSC`. Here thread 1 runs
first (`r0 = 0`) and thread 2 then reads thread 1's store (`r1 = 1`). -/
theorem sbSC_sequential_outcome_is_allowed :
    Tso.Consistent (Tso.events (TsoCfg.x86_64 true).lower sbSC)
      (fun r => match r with | 5 => some 1 | _ => none) ∧
    (∀ p : FeatureProfile, A64.Consistent (A64.events (lowerA64 p) sbSC)
      (fun r => match r with | 3 => some 0 | _ => none)) :=
  ⟨⟨acyclic_of_rank id (fun _ _ h => Tso.uni_dom h) (by decide),
    acyclic_of_rank id (fun _ _ h => Tso.ghb_dom h) (by decide)⟩,
   fun p => by
     cases p <;>
       exact ⟨by decide, acyclic_of_rank id (fun _ _ h => A64.ob_dom h) (by decide)⟩⟩

/-! ### 9.3 Sharpness: CE1 (`ldapr` for `load(SeqCst)`) -/

/-- The RCpc profile, except that `load(SeqCst)` also selects `ldapr`. -/
def a64LdaprForSeqCst : MirAtomicOp → List A64Inst
  | .load .seqCst => [.ldapr]
  | op => lowerA64 .lseRcpc op

/-- The mutant no longer provides the required store-to-load edge. -/
theorem ce1_edge_lost :
    rc11Requires false .seqCst true .seqCst = true ∧
    a64Direct (a64LdaprForSeqCst (.store .seqCst)) (a64LdaprForSeqCst (.load .seqCst)) = false := by
  decide

/-- CE1. With `load(SeqCst) ↦ ldapr` the execution of `sbSC` in which both loads return the
initial value satisfies every requirement of the AArch64 model. -/
theorem ce1_ldapr_allows_store_buffering :
    A64.Consistent (A64.events a64LdaprForSeqCst sbSC) (fun _ => none) :=
  ⟨by decide,
   acyclic_of_rank (writesLast (A64.events a64LdaprForSeqCst sbSC))
     (fun _ _ h => A64.ob_dom h) (by decide)⟩

/-- CE1, assembled: Rust forbids the outcome, every real profile forbids it, the mutant allows
it. -/
theorem CE1 :
    (∀ rf, RC11.FragmentConsistent (RC11.events sbSC) rf → ¬ (rf 1 = none ∧ rf 3 = none)) ∧
    (∀ p rf, A64.Consistent (A64.events (lowerA64 p) sbSC) rf → ¬ (rf 1 = none ∧ rf 3 = none)) ∧
    A64.Consistent (A64.events a64LdaprForSeqCst sbSC) (fun _ => none) :=
  ⟨rc11_sbSC_forbidden, a64_sbSC_sound, ce1_ldapr_allows_store_buffering⟩

/-- The same mutant still forbids message passing and IRIW: `ldapr` keeps the
`[(R & A) | (R & Q)]; po` edge and loses only `[W & L]; po; [R & A]`. -/
theorem ce1_mutant_keeps_mp_and_iriw (rf : Nat → Option Nat) :
    (A64.Consistent (A64.events a64LdaprForSeqCst mp) rf → ¬ (rf 2 = some 1 ∧ rf 3 = none)) ∧
    (A64.Consistent (A64.events a64LdaprForSeqCst (iriw .seqCst)) rf →
      ¬ (rf 2 = some 0 ∧ rf 3 = none ∧ rf 4 = some 1 ∧ rf 5 = none)) :=
  ⟨fun hc => A64.mp_forbidden _ rf (wx := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc,
   fun hc => A64.iriw_forbidden _ rf
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hc⟩

/-- Reads lowered to plain `ldr` regardless of ordering. -/
def a64PlainLoads : MirAtomicOp → List A64Inst
  | .load _ => [.ldr]
  | op => lowerA64 .lseRcpc op

/-- With plain `ldr` reads both message passing and IRIW become observable, so the acquire
instruction is necessary for each. -/
theorem a64_plain_loads_allow_mp_and_iriw :
    A64.Consistent (A64.events a64PlainLoads mp)
      (fun r => match r with | 2 => some 1 | _ => none) ∧
    A64.Consistent (A64.events a64PlainLoads (iriw .seqCst))
      (fun r => match r with | 2 => some 0 | 4 => some 1 | _ => none) :=
  ⟨⟨by decide,
    acyclic_of_rank (fun a => match a with | 0 => 1 | 1 => 2 | 2 => 3 | _ => 0)
      (fun _ _ h => A64.ob_dom h) (by decide)⟩,
   ⟨by decide,
    acyclic_of_rank (fun a => match a with | 0 => 1 | 1 => 1 | 2 => 2 | 4 => 2 | _ => 0)
      (fun _ _ h => A64.ob_dom h) (by decide)⟩⟩

/-! ### 9.4 Sharpness: CE4 (no lock / fence / serialization on `SeqCst`) -/

/-- The real table, except that `store(SeqCst)` is a plain store and `fence(SeqCst)` emits
nothing. -/
def TsoCfg.lowerNoScBarrier (c : TsoCfg) : MirAtomicOp → List TsoOp
  | .store .seqCst => [.wr]
  | .fence .seqCst => []
  | op => c.lower op

/-- Rank for the four-event mutant executions `W, R, W, R`: the two writes come last. -/
def writesAt0And2 : Nat → Nat
  | 0 => 1
  | 2 => 1
  | _ => 0

/-- The mutant no longer provides the required store-to-load order. -/
theorem ce4_edge_lost (c : TsoCfg) :
    rc11Requires false .seqCst true .seqCst = true ∧
    tsoDirect (c.lowerNoScBarrier (.store .seqCst)) (c.lowerNoScBarrier (.load .seqCst)) = false := by
  tso_cases c => decide

/-- CE4. Without the lock prefix, `mfence` or `bcr 15,%r0`, the execution of `sbSC` in which
both loads return the initial value satisfies both store-buffer requirements, on all nine
configurations. -/
theorem ce4_plain_store_allows_store_buffering (c : TsoCfg) :
    Tso.Consistent (Tso.events c.lowerNoScBarrier sbSC) (fun _ => none) := by
  tso_cases c =>
    exact ⟨acyclic_of_rank writesAt0And2 (fun _ _ h => Tso.uni_dom h) (by decide),
           acyclic_of_rank writesAt0And2 (fun _ _ h => Tso.ghb_dom h) (by decide)⟩

/-- The same holds for the fence-based program when `fence(SeqCst)` emits nothing. -/
theorem ce4_dropped_fence_allows_store_buffering (c : TsoCfg) :
    Tso.Consistent (Tso.events c.lowerNoScBarrier sbFence) (fun _ => none) := by
  tso_cases c =>
    exact ⟨acyclic_of_rank writesAt0And2 (fun _ _ h => Tso.uni_dom h) (by decide),
           acyclic_of_rank writesAt0And2 (fun _ _ h => Tso.ghb_dom h) (by decide)⟩

/-- CE4, assembled. -/
theorem CE4 :
    (∀ rf, RC11.FragmentConsistent (RC11.events sbSC) rf → ¬ (rf 1 = none ∧ rf 3 = none)) ∧
    (∀ (c : TsoCfg) rf, Tso.Consistent (Tso.events c.lower sbSC) rf →
      ¬ (rf (mainIdx (Tso.events c.lower sbSC) 1) = none ∧
         rf (mainIdx (Tso.events c.lower sbSC) 3) = none)) ∧
    (∀ c : TsoCfg, Tso.Consistent (Tso.events c.lowerNoScBarrier sbSC) (fun _ => none)) :=
  ⟨rc11_sbSC_forbidden, tso_sbSC_sound, ce4_plain_store_allows_store_buffering⟩

/-! ## 10. CE2: the red zone and `lock orl $0, d(%rsp)` -/

namespace Stack

/-- Stack ownership at an instruction boundary. -/
structure State where
  /-- Stack pointer. -/
  sp : Nat
  /-- Lowest address the function is entitled to touch. -/
  low : Nat

def redZoneBytes : Bool → Nat
  | true => 128
  | false => 0

/-- ABI contract: a function owns the stack at and above `sp`, plus the 128-byte red zone
below it when the ABI provides one. -/
def abiOk (redZone : Bool) (s : State) : Prop := s.low + redZoneBytes redZone ≤ s.sp

/-- Number of bytes below `sp` at which a displacement lands. -/
def bytesBelow (disp : Int) : Nat := (-disp).toNat

/-- `lock orl $0, disp(%sp)` stays inside owned memory when its lowest byte is owned. -/
def lockOrSafe (s : State) (disp : Int) : Prop := s.low + bytesBelow disp ≤ s.sp

/-- Displacement chosen by `emitLockedStackOp`: `has128ByteRedZone ? -64 : 0`. -/
def fenceDisp : Bool → Int
  | true => -64
  | false => 0

theorem fence_disp_matches_table (redZone : Bool) :
    lowerX86_64 redZone (.fence .seqCst) = [.lockOrSp (fenceDisp redZone)] := by
  cases redZone <;> rfl

/-- The real lowering only touches owned memory, with or without a red zone. -/
theorem real_lowering_is_frame_safe (redZone : Bool) (s : State) (h : abiOk redZone s) :
    lockOrSafe s (fenceDisp redZone) := by
  cases redZone with
  | true =>
      have h' : s.low + 128 ≤ s.sp := h
      show s.low + 64 ≤ s.sp
      exact Nat.le_trans (Nat.add_le_add_left (by decide : 64 ≤ 128) s.low) h'
  | false => exact h

/-- Displacement `0` is safe in both configurations, so `-64` is an optimization that the
red-zone test guards, not a requirement. -/
theorem top_of_stack_is_always_safe (redZone : Bool) (s : State) (h : abiOk redZone s) :
    lockOrSafe s 0 := by
  cases redZone with
  | true =>
      have h' : s.low + 128 ≤ s.sp := h
      show s.low + 0 ≤ s.sp
      exact Nat.le_trans (Nat.add_le_add_left (Nat.zero_le 128) s.low) h'
  | false => exact h

/-- CE2. Without a red zone, on any stack whose owned region ends exactly at `sp`, the ABI
contract holds and `lock orl $0, -64(%rsp)` touches memory the function does not own. -/
theorem CE2 (s : State) (tight : s.low = s.sp) :
    abiOk false s ∧ ¬ lockOrSafe s (-64) := by
  refine ⟨?_, ?_⟩
  · show s.low + 0 ≤ s.sp
    rw [tight]
    exact Nat.le_refl _
  · intro h
    have h' : s.low + 64 ≤ s.sp := h
    rw [tight] at h'
    exact Nat.not_succ_le_self s.sp
      (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 64) s.sp) h')

/-- Bitwise OR of a memory cell, given as its list of bits, with the immediate `0`. -/
noncomputable def orZero : List Bool → List Bool
  | [] => []
  | b :: bs => (b || false) :: orZero bs

/-- The instruction is value-preserving: OR with zero writes back every bit it read. -/
theorem lock_or_zero_preserves_value (bits : List Bool) : orZero bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      show (b || false) :: orZero bs = b :: bs
      rw [ih]
      cases b <;> rfl

end Stack

/-! ## 11. CE3: compiler fences, scheduling and dead-store elimination -/

namespace Sched

/-- A straight-line statement of the main flow. -/
inductive Stmt where
  | store (loc val : Nat)   -- one machine store
  | cfence                  -- `compiler_fence`: no machine instruction
  deriving DecidableEq, Repr

/-- `IMPORTANT_VARIABLE` and `IS_READY` of the `compiler_fence` documentation example. -/
def important : Nat := 0
def ready : Nat := 1

abbrev Mem := Nat → Nat

def write (m : Mem) (l v : Nat) : Mem := fun x =>
  match Nat.beq x l with
  | true => v
  | false => m x

def step (m : Mem) : Stmt → Mem
  | .store l v => write m l v
  | .cfence => m

noncomputable def run : List Stmt → Mem → Mem
  | [], m => m
  | s :: ss, m => run ss (step m s)

noncomputable def takeL {α : Type} : Nat → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, x :: xs => x :: takeL n xs

/-- Memory seen by a signal handler delivered after the first `k` statements have executed
(all locations start at `0`). -/
def observe (prog : List Stmt) (k : Nat) : Mem := run (takeL k prog) (fun _ => 0)

/-- Machine code of a statement list: compiler fences vanish. -/
noncomputable def machine : List Stmt → List Stmt
  | [] => []
  | .cfence :: rest => machine rest
  | s :: rest => s :: machine rest

/-- Statements of `prog` in the order given by `sched` (a list of statement indices). -/
noncomputable def pick (prog : List Stmt) : List Nat → List Stmt
  | [] => []
  | i :: rest =>
    match nth prog i with
    | some s => s :: pick prog rest
    | none => pick prog rest

noncomputable def allL {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && allL p xs

theorem allL_spec {α : Type} {p : α → Bool} :
    ∀ {l : List α}, allL p l = true → ∀ x, x ∈ l → p x = true
  | [], _, _, hx => nomatch hx
  | _ :: _, h, _, List.Mem.head _ => and_left h
  | _ :: xs, h, x, List.Mem.tail _ hx => allL_spec (l := xs) (and_right h) x hx

/-- `dep i j = true` means statement `i` must stay before statement `j`. A schedule respects
`dep` when no statement is placed before one of its prerequisites. -/
noncomputable def respects (dep : Nat → Nat → Bool) : List Nat → Bool
  | [] => true
  | a :: rest => allL (fun b => !dep b a) rest && respects dep rest

theorem respects_append {dep : Nat → Nat → Bool} :
    ∀ {s₁ s₂ : List Nat}, respects dep (appendL s₁ s₂) = true →
      ∀ {a b : Nat}, a ∈ s₁ → b ∈ s₂ → dep b a = false
  | [], _, _, _, _, ha, _ => nomatch ha
  | x :: xs, s₂, h, a, b, ha, hb => by
      have h' : (allL (fun b => !dep b x) (appendL xs s₂) && respects dep (appendL xs s₂)) = true := h
      cases ha with
      | head =>
          have hmem : b ∈ appendL xs s₂ := by
            clear h h'
            induction xs with
            | nil => exact hb
            | cons y ys ih => exact List.Mem.tail _ ih
          exact not_true_eq_false (allL_spec (and_left h') b hmem)
      | tail _ ha' => exact respects_append (and_right h') ha' hb

/-- The ordering edges of a compiler fence at index `f`: everything before it stays before
everything after it. -/
def fenceDep (f : Nat) (i j : Nat) : Bool := Nat.blt i f && Nat.blt f j

/-- No ordering edges at all (the two stores of the example write different locations, so
there is no data dependency either). -/
def noDep (_ _ : Nat) : Bool := false

theorem mem_appendL {α : Type} {x : α} :
    ∀ {s₁ s₂ : List α}, x ∈ appendL s₁ s₂ → x ∈ s₁ ∨ x ∈ s₂
  | [], _, h => Or.inr h
  | _ :: _, _, List.Mem.head _ => Or.inl (List.Mem.head _)
  | _ :: xs, _, List.Mem.tail _ h =>
      match mem_appendL (s₁ := xs) h with
      | Or.inl h1 => Or.inl (List.Mem.tail _ h1)
      | Or.inr h2 => Or.inr h2

/-- General scheduling theorem. If a schedule respects the edges of a fence at index `f`, then
at every interruption point (`s₁` executed, `s₂` pending) at which some post-fence statement
`j` has executed, every scheduled pre-fence statement `i` has executed too. -/
theorem fence_edges_keep_prefix_closed (f : Nat) {s₁ s₂ : List Nat}
    (h : respects (fenceDep f) (appendL s₁ s₂) = true) {i j : Nat} (hi : i < f) (hj : f < j)
    (hj₁ : j ∈ s₁) (hsched : i ∈ appendL s₁ s₂) : i ∈ s₁ := by
  rcases mem_appendL hsched with h1 | h2
  · exact h1
  · have hfalse : fenceDep f i j = false := respects_append h hj₁ h2
    have htrue : fenceDep f i j = true :=
      and_intro (Nat.ble_eq_true_of_le hi) (Nat.ble_eq_true_of_le hj)
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse

/-- The publishing side of the documentation example:
`IMPORTANT_VARIABLE = 42; compiler_fence(Release); IS_READY.store(true, Relaxed)`. -/
def publish : List Stmt := [.store important 42, .cfence, .store ready 1]

/-- The handler's assertion: once `IS_READY` is seen set, `IMPORTANT_VARIABLE` is `v`. -/
def handlerOk (v : Nat) (m : Mem) : Bool := !Nat.beq (m ready) 1 || Nat.beq (m important) v

/-- The compiler fence emits no machine instruction. -/
theorem cfence_emits_nothing : machine [Stmt.cfence] = [] := rfl

/-- With the fence edges, source order is a legal schedule and the swapped order is not; at
every interruption point of the legal schedule the handler's assertion holds. -/
theorem fence_edges_protect_the_handler :
    respects (fenceDep 1) [0, 2] = true ∧
    respects (fenceDep 1) [2, 0] = false ∧
    (∀ k, k ≤ 2 → handlerOk 42 (observe (pick publish [0, 2]) k) = true) := by
  decide

/-- CE3 (reordering). Without the fence edges the swapped order is a legal schedule, and a
signal delivered after its first store sees `IS_READY` set while `IMPORTANT_VARIABLE` still
holds the stale initial value. -/
theorem CE3_reordering :
    respects noDep [2, 0] = true ∧
    handlerOk 42 (observe (pick publish [2, 0]) 1) = false := by
  decide

/-- Is `loc` overwritten later with nothing in between that may observe it? With
`fenceObserves = true` a compiler fence counts as a possible observer. -/
noncomputable def overwrittenLater (fenceObserves : Bool) (loc : Nat) : List Stmt → Bool
  | [] => false
  | .store l _ :: rest => Nat.beq l loc || overwrittenLater fenceObserves loc rest
  | .cfence :: rest => !fenceObserves && overwrittenLater fenceObserves loc rest

/-- Dead-store elimination over store-only code. -/
noncomputable def dse (fenceObserves : Bool) : List Stmt → List Stmt
  | [] => []
  | .store l v :: rest =>
    match overwrittenLater fenceObserves l rest with
    | true => dse fenceObserves rest
    | false => .store l v :: dse fenceObserves rest
  | .cfence :: rest => .cfence :: dse fenceObserves rest

/-- `IMPORTANT_VARIABLE = v; compiler_fence(Release); IS_READY = 1; IMPORTANT_VARIABLE = w`. -/
def canary (v w : Nat) : List Stmt :=
  [.store important v, .cfence, .store ready 1, .store important w]

/-- The same statements without the compiler fence. -/
def canaryNoFence (v w : Nat) : List Stmt :=
  [.store important v, .store ready 1, .store important w]

/-- The handler's assertion for the canary: once `IS_READY` is seen set, the datum is one of
the two published values. -/
def handlerOk2 (v w : Nat) (m : Mem) : Bool :=
  !Nat.beq (m ready) 1 || Nat.beq (m important) v || Nat.beq (m important) w

/-- A fence-respecting eliminator keeps all three stores; the fence-free source loses the
first one. Both match the measured LLVM IR of the two canary functions. -/
theorem dse_shapes :
    machine (dse true (canary 42 43)) =
      [.store important 42, .store ready 1, .store important 43] ∧
    dse true (canaryNoFence 42 43) = [.store ready 1, .store important 43] ∧
    machine (dse false (canary 42 43)) = [.store ready 1, .store important 43] := by
  decide

/-- Elimination is invisible to straight-line execution: final memory is unchanged. -/
theorem dse_preserves_final_memory :
    run (dse false (canary 42 43)) (fun _ => 0) important = run (canary 42 43) (fun _ => 0) important ∧
    run (dse false (canary 42 43)) (fun _ => 0) ready = run (canary 42 43) (fun _ => 0) ready := by
  decide

/-- With the fence respected, the handler's assertion holds at every interruption point. -/
theorem dse_respecting_fence_protects_the_handler :
    ∀ k, k ≤ 3 → handlerOk2 42 43 (observe (machine (dse true (canary 42 43))) k) = true := by
  decide

/-- CE3 (elimination). An eliminator that ignores the fence deletes the pre-publication store;
a signal delivered after the first remaining store sees `IS_READY` set and neither published
value. -/
theorem CE3_elimination :
    handlerOk2 42 43 (observe (machine (dse false (canary 42 43))) 1) = false := by
  decide

end Sched

/-- On every target the compiler fence itself emits zero instructions (so CE3 is entirely
about ordering edges). -/
theorem compilerFence_emits_nothing_everywhere (o : RustOrdering) :
    (∀ c : TsoCfg, c.lower (.compilerFence o) = []) ∧
    (∀ p : FeatureProfile, lowerA64 p (.compilerFence o) = []) :=
  ⟨fun c => tso_compilerFence_emits_nothing c o, fun p => (a64_fence_selection p).2.2.2.2 o⟩

/-! ## 12. Token export for the differential check against measured assembly -/

def X86Inst.tok : X86Inst → String
  | .movLoad => "mov-load"
  | .movStore => "mov-store"
  | .xchg => "xchg"
  | .lockXadd => "lock-xadd"
  | .lockCmpxchg => "lock-cmpxchg"
  | .lockCmpxchg8b => "lock-cmpxchg8b"
  | .lockOrSp d => "lock-or-sp(" ++ toString d ++ ")"
  | .mfence => "mfence"
  | .sseLoad64 => "sse-load64"
  | .sseStore64 => "sse-store64"
  | .x87Load64 => "x87-load64"
  | .x87Store64 => "x87-store64"

def variantSuffix : Bool → Bool → String
  | false, false => ""
  | true, false => "a"
  | false, true => "l"
  | true, true => "al"

def helperSuffix : Bool → Bool → String
  | false, false => "relax"
  | true, false => "acq"
  | false, true => "rel"
  | true, true => "acq_rel"

def RmwKind.lseName : RmwKind → String
  | .xchg => "swp"
  | .add => "ldadd"
  | .and => "ldclr"

def A64Inst.tok : A64Inst → String
  | .ldr => "ldr"
  | .ldar => "ldar"
  | .ldapr => "ldapr"
  | .str => "str"
  | .stlr => "stlr"
  | .loadExcl false => "ldxr"
  | .loadExcl true => "ldaxr"
  | .storeExcl false => "stxr"
  | .storeExcl true => "stlxr"
  | .clrex => "clrex"
  | .lseCas a r => "cas" ++ variantSuffix a r
  | .lseRmw k a r => k.lseName ++ variantSuffix a r
  | .outlineCas a r => "bl:__aarch64_cas_" ++ helperSuffix a r
  | .outlineRmw k a r => "bl:__aarch64_" ++ k.lseName ++ "_" ++ helperSuffix a r
  | .dmbIsh => "dmb-ish"
  | .dmbIshld => "dmb-ishld"

def S390Inst.tok : S390Inst → String
  | .load => "load"
  | .store => "store"
  | .cs => "cs"
  | .bcr15 => "bcr15"

/-- A probe function: its symbol name, whether its operand is 64 bits wide, and the MIR
operation it performs. -/
structure ProbeFn where
  name : String
  wide : Bool
  op : MirAtomicOp

def probeTable : List ProbeFn :=
  [ ⟨"at_u32_load_relaxed", false, .load .relaxed⟩,
    ⟨"at_u32_load_acquire", false, .load .acquire⟩,
    ⟨"at_u32_load_seqcst", false, .load .seqCst⟩,
    ⟨"at_u32_store_relaxed", false, .store .relaxed⟩,
    ⟨"at_u32_store_release", false, .store .release⟩,
    ⟨"at_u32_store_seqcst", false, .store .seqCst⟩,
    ⟨"at_u32_swap_relaxed", false, .rmw .xchg .relaxed⟩,
    ⟨"at_u32_swap_acquire", false, .rmw .xchg .acquire⟩,
    ⟨"at_u32_swap_release", false, .rmw .xchg .release⟩,
    ⟨"at_u32_swap_acqrel", false, .rmw .xchg .acqRel⟩,
    ⟨"at_u32_swap_seqcst", false, .rmw .xchg .seqCst⟩,
    ⟨"at_u32_fadd_relaxed", false, .rmw .add .relaxed⟩,
    ⟨"at_u32_fadd_acquire", false, .rmw .add .acquire⟩,
    ⟨"at_u32_fadd_release", false, .rmw .add .release⟩,
    ⟨"at_u32_fadd_acqrel", false, .rmw .add .acqRel⟩,
    ⟨"at_u32_fadd_seqcst", false, .rmw .add .seqCst⟩,
    ⟨"at_u32_cas_strong_acqrel_acq", false, .casStrong .acqRel .acquire⟩,
    ⟨"at_u32_cas_strong_seqcst_seqcst", false, .casStrong .seqCst .seqCst⟩,
    ⟨"at_u32_cas_weak_rel_rlx", false, .casWeak .release .relaxed⟩,
    ⟨"at_u64_load_acquire", true, .load .acquire⟩,
    ⟨"at_u64_store_seqcst", true, .store .seqCst⟩,
    ⟨"at_u64_fadd_acqrel", true, .rmw .add .acqRel⟩,
    ⟨"at_u64_cas_seqcst", true, .casStrong .seqCst .acquire⟩,
    ⟨"at_u8_fand_acqrel", false, .rmw .and .acqRel⟩,
    ⟨"at_fence_acquire", false, .fence .acquire⟩,
    ⟨"at_fence_release", false, .fence .release⟩,
    ⟨"at_fence_acqrel", false, .fence .acqRel⟩,
    ⟨"at_fence_seqcst", false, .fence .seqCst⟩,
    ⟨"at_cfence_acquire", false, .compilerFence .acquire⟩,
    ⟨"at_cfence_release", false, .compilerFence .release⟩,
    ⟨"at_cfence_acqrel", false, .compilerFence .acqRel⟩,
    ⟨"at_cfence_seqcst", false, .compilerFence .seqCst⟩,
    ⟨"ext_u64_load_relaxed", true, .load .relaxed⟩,
    ⟨"ext_u64_load_seqcst", true, .load .seqCst⟩,
    ⟨"ext_u64_store_relaxed", true, .store .relaxed⟩,
    ⟨"ext_u64_store_release", true, .store .release⟩,
    ⟨"ext_u64_swap_seqcst", true, .rmw .xchg .seqCst⟩ ]

/-- Every probe operation is one that `core::sync::atomic` accepts. -/
theorem probeTable_valid : Sched.allL (fun f => f.op.valid) probeTable = true := by decide

/-- Exported configurations: name and token table. -/
def exportConfigs : List (String × (Bool → MirAtomicOp → List String)) :=
  [ ("x86_64.redzone", fun _ op => List.map X86Inst.tok (lowerX86_64 true op)),
    ("x86_64.no_redzone", fun _ op => List.map X86Inst.tok (lowerX86_64 false op)),
    ("i686.sse2", fun w op => List.map X86Inst.tok (lowerI686 .sse2 w op)),
    ("i686.sse1_only", fun w op => List.map X86Inst.tok (lowerI686 .sse1Only w op)),
    ("i686.x87_only", fun w op => List.map X86Inst.tok (lowerI686 .x87Only w op)),
    ("aarch64.v80_inline", fun _ op => List.map A64Inst.tok (lowerA64 .v80Inline op)),
    ("aarch64.v80_outlined", fun _ op => List.map A64Inst.tok (lowerA64 .v80Outlined op)),
    ("aarch64.lse", fun _ op => List.map A64Inst.tok (lowerA64 .lse op)),
    ("aarch64.lse_rcpc", fun _ op => List.map A64Inst.tok (lowerA64 .lseRcpc op)),
    ("s390x.z10", fun _ op => List.map S390Inst.tok (lowerS390x op)) ]

#eval do
  for cfg in exportConfigs do
    for f in probeTable do
      IO.println ("TABLE|" ++ cfg.1 ++ "|" ++ f.name ++ "|" ++ ";".intercalate (cfg.2 f.wide f.op))

/-! ## 13. Dependency audit -/

#print axioms RustOrdering.le_trans
#print axioms RustOrdering.le_antisymm
#print axioms RustOrdering.join_le
#print axioms mirToLlvm_injective
#print axioms tso_compilerFence_emits_nothing
#print axioms tso_weak_fence_emits_nothing
#print axioms tso_seqcst_store_has_barrier
#print axioms tso_weaker_access_has_no_barrier
#print axioms tso_rmw_and_cas_are_locked
#print axioms a64_load_monotone
#print axioms a64_store_monotone
#print axioms a64_load_selection
#print axioms a64_fence_selection
#print axioms a64_rmw_bits
#print axioms a64_cas_bits
#print axioms a64_required_order_is_barrier_ordered
#print axioms tso_required_order_is_kept
#print axioms acyclic_of_rank
#print axioms tc_of_reach
#print axioms rc11_sbSC_forbidden
#print axioms rc11_sbFence_forbidden
#print axioms rc11_mp_forbidden
#print axioms rc11_iriwSC_forbidden
#print axioms tso_single_writer
#print axioms tso_sbSC_sound
#print axioms tso_sbFence_sound
#print axioms tso_mp_sound
#print axioms a64_single_writer
#print axioms a64_sbSC_sound
#print axioms a64_sbFence_sound
#print axioms a64_mp_sound
#print axioms a64_iriwSC_sound
#print axioms sbSC_sequential_outcome_is_allowed
#print axioms ce1_edge_lost
#print axioms CE1
#print axioms ce1_mutant_keeps_mp_and_iriw
#print axioms a64_plain_loads_allow_mp_and_iriw
#print axioms ce4_edge_lost
#print axioms ce4_dropped_fence_allows_store_buffering
#print axioms CE4
#print axioms Stack.fence_disp_matches_table
#print axioms Stack.real_lowering_is_frame_safe
#print axioms Stack.top_of_stack_is_always_safe
#print axioms Stack.CE2
#print axioms Stack.lock_or_zero_preserves_value
#print axioms Sched.fence_edges_keep_prefix_closed
#print axioms Sched.fence_edges_protect_the_handler
#print axioms Sched.CE3_reordering
#print axioms Sched.dse_shapes
#print axioms Sched.dse_preserves_final_memory
#print axioms Sched.dse_respecting_fence_protects_the_handler
#print axioms Sched.CE3_elimination
#print axioms compilerFence_emits_nothing_everywhere
#print axioms probeTable_valid

end

end RustAtomicLowering
