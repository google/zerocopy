/-!
# Lean 4 Wasm Formalizations and Virtual ISA Verification Probe (2026)

Standalone, zero-`sorry`, zero-custom-axiom Lean 4.34.1 mechanization accompanying the
research report `lean4-wasm-formalizations-and-virtual-isa-verification-2026`.

This file embeds Anneal's exact `Trusted.Refinement` and `Trusted.StepResult` semantic
algebra and mechanizes three foundational results for virtual ISA backends:

1. **Extrinsic vs. Intrinsic Wasm Semantics (`WasmExtrinsicIntrinsic`)**:
   Formalizes both the extrinsically-typed small-step stack + linear-memory machine
   (used by `plum-umd/lean-wasm`, `cajal-technologies/talos`, `linobit-corp/wasm-lean`,
   and `T-Brick/lean-wasm`) and the intrinsically-typed heterogeneous-stack evaluator
   (used by `aionescu/lean-wasm`). Proves lockstep erasure correspondence
   (`stepIntrinsic_erases_to_extrinsic`, `execIntrinsicSeq_erases_to_extrinsic`),
   extrinsic syntactic type safety (`extrinsic_progress_and_preservation`), and the
   exact vacuity pitfall found in `linobit-corp/wasm-lean`'s unconstrained
   `Reduce.r_interp_flat` constructor (`linobit_unconstrained_reduce_vacuity`).

2. **Wasm `trap` vs. Source Rust `Partial.ub` (`WasmTrapVsRustUb`)**:
   Instantiates Anneal's `SmallStepMachine` and `StepLang` for Rust MIR raw-pointer
   loads (`MirLang`) and Wasm linear-memory loads (`WasmLang`). Proves that:
   - A deterministic Wasm `trap` has `defined = True` (`PrefixOutcome.isSafe = True`)
     and is **not** `Partial.ub` (`wasm_trap_is_defined_not_ub`).
   - Compiling a Rust `unsafe` raw-pointer dereference (which has `Partial.ub` when
     out-of-bounds of its Rust allocation) to a Wasm `i32.load` (which either reads
     linear memory or deterministically traps) satisfies `Compiles MirLang WasmLang`
     whenever the allocation fits in linear memory (`rustc_raw_load_to_wasm_compiles`).
   - Wasm's page-granularity bounds check is **not** a sub-page spatial memory-safety
     sanitizer (`wasm_linear_memory_lack_of_provenance`).
   - A safe Rust specification forbidding traps (`EnsuresNoTrap`) is **refuted** if a
     Wasm `trap` is reachable (`wasm_trap_refutes_ensuresNoTrap`), whereas a panic/trap-
     permitting specification (`EnsuresValueOrTrap`) is **satisfied**
     (`wasm_trap_satisfies_valueOrTrap`).
   - Lowering 64-bit offsets via wrapped 32-bit `i32.add` on `wasm32` can silently wrap
     modulo `2^32` into an in-bounds address, whereas encoding the offset in Wasm's
     `memarg.offset` field computes `ea = base.toNat + offset.toNat` in unbounded `Nat`
     and deterministically traps (`wasm32_u32_wrapping_vs_memarg_offset`).

3. **eBPF Verifier as Anneal `VerifiedChecker` & Kops Dual-Sequence JIT Soundness
   (`EbpfVerifierAndKopsBridge`)**:
   Formalizes an eBPF static range/divisor verifier as an Anneal `VerifiedChecker`
   (`ebpfVerifier_is_verifiedChecker`) and proves the Kops (`arXiv:2606.24213` /
   `KinsnLean4`) dual-sequence soundness theorem (`kops_dual_sequence_jit_soundness`):
   if the unmodified eBPF verifier accepts a vanilla proof sequence `seq_proof` and
   `Compiles EbpfLang NativeJitLang π_jit seq_proof seq_native` holds, then `seq_native`
   inherits the verifier's safety guarantee without modifying the kernel verifier.
-/

namespace AnnealCore

universe u v w

/-- A preorder: a reflexive, transitive relation `≤`.
    Matches `Trusted/Refinement.lean`. -/
class Preorder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c

/-- The partiality / undefined-behavior transformer (`Trusted/Refinement.lean`). -/
structure Partial (B : Type u) [Preorder B] where
  defined : Prop
  val : defined → B

namespace Partial

variable {B : Type u} [Preorder B]

/-- Embed a well-defined behavior into `Partial B`. -/
def pure (b : B) : Partial B where
  defined := True
  val := fun _ => b

/-- Undefined behavior: the top element of the refinement order. -/
def ub : Partial B where
  defined := False
  val := False.elim

instance instPreorder : Preorder (Partial B) where
  le x y := ∀ (hy : y.defined), ∃ (hx : x.defined), x.val hx ≤ y.val hy
  le_refl x := fun hx => ⟨hx, Preorder.le_refl (x.val hx)⟩
  le_trans hab hbc := fun hc =>
    let ⟨hb, hbc'⟩ := hbc hc
    let ⟨ha, hab'⟩ := hab hb
    ⟨ha, Preorder.le_trans hab' hbc'⟩

theorem pure_le_pure {b₁ b₂ : B} (h : b₁ ≤ b₂) : pure b₁ ≤ pure b₂ :=
  fun _ => ⟨trivial, h⟩

theorem ub_top (x : Partial B) : x ≤ ub :=
  fun hy => False.elim hy

end Partial

/-- Pointwise preorder on query-indexed behavior families. -/
instance instPiPreorder {ι : Type u} {B : ι → Type v} [∀ i, Preorder (B i)] :
    Preorder (∀ i, B i) where
  le f g := ∀ i, f i ≤ g i
  le_refl f i := Preorder.le_refl (f i)
  le_trans hab hbc i := Preorder.le_trans (hab i) (hbc i)

/-- Propositions ordered by implication (`P ≤ Q` iff `P → Q`). -/
abbrev PropSpec := Prop

instance instPropPreorder : Preorder PropSpec where
  le P Q := P → Q
  le_refl _ h := h
  le_trans hab hbc hp := hbc (hab hp)

/-- A programming language or intermediate representation (`Trusted/Refinement.lean`). -/
structure Language where
  Prog : Type u
  Beh : Type v
  [behPreorder : Preorder Beh]
  sem : Prog → Beh

attribute [instance] Language.behPreorder

/-- Monotonicity of a behavioral translation map. -/
def Monotone {α : Type u} {β : Type v} [Preorder α] [Preorder β] (f : α → β) : Prop :=
  ∀ {x y : α}, x ≤ y → f x ≤ f y

/-- Correct compilation of `p_src` to `p_tgt` (`Trusted/Refinement.lean`). -/
def Compiles (L_src L_tgt : Language) (π : L_src.Beh → L_tgt.Beh)
    (p_src : L_src.Prog) (p_tgt : L_tgt.Prog) : Prop :=
  L_tgt.sem p_tgt ≤ π (L_src.sem p_src)

/-- Correct abstraction of `p_conc` as `p_abs` (`Trusted/Refinement.lean`). -/
def Abstracts (L_conc L_abs : Language) (ι : L_abs.Beh → L_conc.Beh)
    (p_conc : L_conc.Prog) (p_abs : L_abs.Prog) : Prop :=
  L_conc.sem p_conc ≤ ι (L_abs.sem p_abs)

/-- Theorem (`Compiles.preserves_abstraction` in `Trusted/Refinement.lean`). -/
theorem Compiles.preserves_abstraction {L_conc L_tgt L_abs : Language}
    {π : L_conc.Beh → L_tgt.Beh} {ι : L_abs.Beh → L_conc.Beh}
    {p_conc : L_conc.Prog} {p_tgt : L_tgt.Prog} {p_abs : L_abs.Prog}
    (h_mono : Monotone π)
    (h_comp : Compiles L_conc L_tgt π p_conc p_tgt)
    (h_abs : Abstracts L_conc L_abs ι p_conc p_abs) :
    L_tgt.sem p_tgt ≤ π (ι (L_abs.sem p_abs)) :=
  Preorder.le_trans h_comp (h_mono h_abs)

/-- A static checker verified to establish an abstract specification `spec`. -/
structure VerifiedChecker (L : Language) (spec : L.Prog → L.Beh) where
  check : L.Prog → Bool
  check_sound : ∀ p, check p = true → L.sem p ≤ spec p

/-- Why an execution step failed (`Trusted/StepResult.lean`). -/
inductive FailureKind where
  | ub
  | contractViolation
  deriving DecidableEq, Repr

/-- How a finite execution terminated (`Trusted/StepResult.lean`). -/
inductive TerminationKind (Val : Type u) where
  | normal (v : Val)
  | unwind
  deriving DecidableEq, Repr

/-- The result of a single execution step (`Trusted/StepResult.lean`). -/
inductive StepResult (State : Type u) (Val : Type v) where
  | next (s : State)
  | terminated (t : TerminationKind Val)
  | failed (k : FailureKind)
  | outOfFuel
  deriving DecidableEq, Repr

/-- Observable outcome of a finite execution prefix (`Trusted/StepResult.lean`). -/
inductive PrefixOutcome (Val : Type u) where
  | terminated (t : TerminationKind Val)
  | failed (k : FailureKind)
  | outOfFuel
  deriving DecidableEq, Repr

/-- Whether a prefix outcome is free of failure (no UB, no contract violation). -/
def PrefixOutcome.isSafe {Val : Type u} : PrefixOutcome Val → Prop
  | .terminated _ => True
  | .failed _ => False
  | .outOfFuel => True

/-- Small-step operational machine (`Trusted/StepResult.lean`). -/
structure SmallStepMachine (Prog : Type u) (Query : Type v) where
  State : Type w
  Val : Type v
  init : Prog → Query → State
  step : Prog → State → StepResult State Val → Prop

/-- Relational reachability in `n` steps (`Trusted/StepResult.lean`). -/
inductive ReachesPrefix {Prog : Type u} {Query : Type v}
    (M : SmallStepMachine Prog Query) (p : Prog) :
    Nat → M.State → PrefixOutcome M.Val → Prop where
  | zero (s : M.State) :
      ReachesPrefix M p 0 s .outOfFuel
  | terminated {n : Nat} {s : M.State} {t : TerminationKind M.Val} :
      M.step p s (.terminated t) →
      ReachesPrefix M p (n + 1) s (.terminated t)
  | failed {n : Nat} {s : M.State} {k : FailureKind} :
      M.step p s (.failed k) →
      ReachesPrefix M p (n + 1) s (.failed k)
  | outOfFuel {n : Nat} {s : M.State} :
      M.step p s .outOfFuel →
      ReachesPrefix M p (n + 1) s .outOfFuel
  | step {n : Nat} {s s' : M.State} {out : PrefixOutcome M.Val} :
      M.step p s (.next s') →
      ReachesPrefix M p n s' out →
      ReachesPrefix M p (n + 1) s out

/-- Set of observable prefix outcomes of an execution, ordered by subset inclusion
    (`S₁ ≤ S₂` iff `∀ out, S₁ out → S₂ out`, i.e., `S₁ ⊆ S₂`). -/
def OutcomeSet (Val : Type u) := PrefixOutcome Val → Prop

instance instOutcomeSetPreorder {Val : Type u} : Preorder (OutcomeSet Val) where
  le S₁ S₂ := ∀ out, S₁ out → S₂ out
  le_refl _ _ h := h
  le_trans hab hbc out h := hbc out (hab out h)

/-- Canonical `Partial` behavior induced by a `SmallStepMachine` (`Trusted/StepResult.lean`). -/
def BehaviorOf {Prog : Type u} {Query : Type v}
    (M : SmallStepMachine Prog Query) (p : Prog) (q : Query) :
    Partial (OutcomeSet M.Val) where
  defined := ∀ n out, ReachesPrefix M p n (M.init p q) out → out.isSafe
  val := fun _ out => ∃ n, ReachesPrefix M p n (M.init p q) out

/-- Canonical `Language` induced by a `SmallStepMachine` (`Trusted/StepResult.lean`). -/
def StepLang {Prog : Type u} {Query : Type v}
    (M : SmallStepMachine Prog Query) : Language where
  Prog := Prog
  Beh := ∀ _ : Query, Partial (OutcomeSet M.Val)
  sem := BehaviorOf M

end AnnealCore

/-!
## Part 1: Extrinsically-Typed vs. Intrinsically-Typed Wasm Semantics

We model the two design points represented across the six Lean 4 Wasm projects:
- **Extrinsic small-step machine** (`plum-umd/lean-wasm`, `cajal-technologies/talos`,
  `linobit-corp/wasm-lean`, `T-Brick/lean-wasm`): untyped `WasmInstr` syntax + dynamic
  `List WasmVal` operand stack + byte-addressed `LinearMem`, with an explicit distinction
  between runtime `.trap` and `.stuckTypeMismatch`, paired with an extrinsic typing judgment
  `InstrTyped`.
- **Intrinsic indexed evaluator** (`aionescu/lean-wasm`): heterogeneous stack
  `HStack : List WasmTy → Type` and dependent instructions `IWasmInstr ts₁ ts₂`, where
  `.stuckTypeMismatch` is unrepresentable in the type `Except TrapReason (LinearMem × HStack ts₂)`.
-/
namespace WasmExtrinsicIntrinsic

/-- Core Wasm value types (`i32` and `i64`). -/
inductive WasmTy where
  | i32
  | i64
  deriving DecidableEq, Repr

/-- Runtime Wasm values for the extrinsic stack machine. -/
inductive WasmVal where
  | i32 (v : BitVec 32)
  | i64 (v : BitVec 64)
  deriving DecidableEq, Repr

/-- Dynamic type tag of a `WasmVal`. -/
def WasmVal.ty : WasmVal → WasmTy
  | .i32 _ => .i32
  | .i64 _ => .i64

/-- Wasm trap reasons, modeled after `cajal-technologies/talos` (`SmallStep.TrapReason`). -/
inductive TrapReason where
  | unreachable
  | divByZero
  | outOfBoundsMem
  deriving DecidableEq, Repr

/-- Wasm linear memory modeled as a bounded byte array (1 page = 65,536 bytes in Wasm,
    here parameterized by exact byte capacity `size`). -/
structure LinearMem where
  bytes : List UInt8
  deriving DecidableEq, Repr

/-- Size of linear memory in bytes. -/
def LinearMem.size (m : LinearMem) : Nat :=
  m.bytes.length

/-- Wasm spec effective address calculation:
    `ea = i.toNat + offset.toNat` computed in unbounded `Nat` (`WebAssembly 2.0/3.0 §4.4.7`).
    Crucially, this does NOT wrap modulo `2^32`. -/
def effectiveAddr (base : BitVec 32) (offset : UInt32) : Nat :=
  base.toNat + offset.toNat

/-- Read a single byte at `idx` with default `0`. -/
def LinearMem.readByteD (m : LinearMem) (idx : Nat) : UInt8 :=
  m.bytes.getD idx 0

/-- Little-endian 32-bit word assembly from 4 bytes. -/
def packLE32 (b0 b1 b2 b3 : UInt8) : BitVec 32 :=
  BitVec.ofNat 32
    (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216)

/-- Unpack a 32-bit word into 4 little-endian bytes. -/
def unpackLE32 (v : BitVec 32) : UInt8 × UInt8 × UInt8 × UInt8 :=
  let n := v.toNat
  (UInt8.ofNat (n % 256),
   UInt8.ofNat ((n / 256) % 256),
   UInt8.ofNat ((n / 65536) % 256),
   UInt8.ofNat ((n / 16777216) % 256))

/-- Wasm `i32.load offset`: checks `ea + 4 ≤ m.size` in unbounded `Nat`.
    Returns `none` iff out-of-bounds (triggering `.trap .outOfBoundsMem`). -/
def LinearMem.load32? (m : LinearMem) (base : BitVec 32) (offset : UInt32) :
    Option (BitVec 32) :=
  let ea := effectiveAddr base offset
  if ea + 4 ≤ m.size then
    some (packLE32
      (m.readByteD ea)
      (m.readByteD (ea + 1))
      (m.readByteD (ea + 2))
      (m.readByteD (ea + 3)))
  else
    none

/-- Wasm `i32.store offset`: checks `ea + 4 ≤ m.size` in unbounded `Nat`. -/
def LinearMem.store32? (m : LinearMem) (base : BitVec 32) (offset : UInt32)
    (val : BitVec 32) : Option LinearMem :=
  let ea := effectiveAddr base offset
  if ea + 4 ≤ m.size then
    let (b0, b1, b2, b3) := unpackLE32 val
    let bs := (((m.bytes.set ea b0).set (ea + 1) b1).set (ea + 2) b2).set (ea + 3) b3
    some ⟨bs⟩
  else
    none

/-- Extrinsic Wasm instruction syntax. -/
inductive WasmInstr where
  | nop
  | unreachable
  | drop
  | const32 (v : BitVec 32)
  | const64 (v : BitVec 64)
  | add32
  | divU32
  | load32 (offset : UInt32)
  | store32 (offset : UInt32)
  deriving DecidableEq, Repr

/-- Extrinsic small-step outcome.
    Distinguishes normal state transition (`.next`), deterministic Wasm `.trap`,
    and `.stuckTypeMismatch` (which well-typed programs can never reach). -/
inductive WasmStepOutcome where
  | next (mem : LinearMem) (stack : List WasmVal)
  | trap (reason : TrapReason)
  | stuckTypeMismatch
  deriving DecidableEq, Repr

/-- Single-step extrinsic evaluator (head of `stack` is the top of the operand stack). -/
def stepExtrinsic (instr : WasmInstr) (mem : LinearMem) (stack : List WasmVal) :
    WasmStepOutcome :=
  match instr with
  | .nop => .next mem stack
  | .unreachable => .trap .unreachable
  | .drop =>
      match stack with
      | _ :: rest => .next mem rest
      | [] => .stuckTypeMismatch
  | .const32 v => .next mem (.i32 v :: stack)
  | .const64 v => .next mem (.i64 v :: stack)
  | .add32 =>
      match stack with
      | .i32 rhs :: .i32 lhs :: rest => .next mem (.i32 (lhs + rhs) :: rest)
      | _ => .stuckTypeMismatch
  | .divU32 =>
      match stack with
      | .i32 rhs :: .i32 lhs :: rest =>
          if rhs.toNat == 0 then
            .trap .divByZero
          else
            .next mem (.i32 (BitVec.ofNat 32 (lhs.toNat / rhs.toNat)) :: rest)
      | _ => .stuckTypeMismatch
  | .load32 offset =>
      match stack with
      | .i32 base :: rest =>
          match mem.load32? base offset with
          | some v => .next mem (.i32 v :: rest)
          | none => .trap .outOfBoundsMem
      | _ => .stuckTypeMismatch
  | .store32 offset =>
      match stack with
      | .i32 val :: .i32 base :: rest =>
          match mem.store32? base offset val with
          | some mem' => .next mem' rest
          | none => .trap .outOfBoundsMem
      | _ => .stuckTypeMismatch

/-- Multi-step extrinsic sequence evaluator. -/
def execExtrinsicSeq : List WasmInstr → LinearMem → List WasmVal → WasmStepOutcome
  | [], mem, stack => .next mem stack
  | i :: rest, mem, stack =>
      match stepExtrinsic i mem stack with
      | .next mem' stack' => execExtrinsicSeq rest mem' stack'
      | .trap r => .trap r
      | .stuckTypeMismatch => .stuckTypeMismatch

/-- Extrinsic stack typing: `StackTyped stack ts` holds when `stack.map WasmVal.ty = ts`. -/
def StackTyped (stack : List WasmVal) (ts : List WasmTy) : Prop :=
  stack.map WasmVal.ty = ts

/-- Frame-polymorphic extrinsic instruction typing (`InstrTyped i ts₁ ts₂`),
    matching Wasm's stack-suffix typing discipline. -/
inductive InstrTyped : WasmInstr → List WasmTy → List WasmTy → Prop where
  | nop (rest : List WasmTy) :
      InstrTyped .nop rest rest
  | unreachable (ts₁ ts₂ : List WasmTy) :
      InstrTyped .unreachable ts₁ ts₂
  | drop (t : WasmTy) (rest : List WasmTy) :
      InstrTyped .drop (t :: rest) rest
  | const32 (v : BitVec 32) (rest : List WasmTy) :
      InstrTyped (.const32 v) rest (.i32 :: rest)
  | const64 (v : BitVec 64) (rest : List WasmTy) :
      InstrTyped (.const64 v) rest (.i64 :: rest)
  | add32 (rest : List WasmTy) :
      InstrTyped .add32 (.i32 :: .i32 :: rest) (.i32 :: rest)
  | divU32 (rest : List WasmTy) :
      InstrTyped .divU32 (.i32 :: .i32 :: rest) (.i32 :: rest)
  | load32 (offset : UInt32) (rest : List WasmTy) :
      InstrTyped (.load32 offset) (.i32 :: rest) (.i32 :: rest)
  | store32 (offset : UInt32) (rest : List WasmTy) :
      InstrTyped (.store32 offset) (.i32 :: .i32 :: rest) rest

/-- Host Lean type denoted by each `WasmTy` (`aionescu/lean-wasm` `Ty.type`). -/
abbrev WasmTy.denote : WasmTy → Type
  | .i32 => BitVec 32
  | .i64 => BitVec 64

/-- Intrinsically-typed heterogeneous operand stack (`aionescu/lean-wasm` `Stack`). -/
inductive HStack : List WasmTy → Type where
  | nil : HStack []
  | cons {t : WasmTy} {ts : List WasmTy} (v : t.denote) (rest : HStack ts) :
      HStack (t :: ts)

/-- Convert a typed value of `t.denote` into an untyped `WasmVal`. -/
def WasmTy.toVal : {t : WasmTy} → t.denote → WasmVal
  | .i32, v => .i32 v
  | .i64, v => .i64 v

@[simp]
theorem WasmTy.toVal_ty {t : WasmTy} (v : t.denote) :
    (WasmTy.toVal v).ty = t := by
  cases t <;> rfl

/-- Erase an intrinsically-typed `HStack ts` to a dynamic `List WasmVal`. -/
def HStack.toVals : {ts : List WasmTy} → HStack ts → List WasmVal
  | [], .nil => []
  | _ :: _, .cons v rest => WasmTy.toVal v :: rest.toVals

/-- Every erased `HStack ts` is extrinsically well-typed at `ts`. -/
theorem HStack.toVals_typed {ts : List WasmTy} (s : HStack ts) :
    StackTyped s.toVals ts := by
  induction s with
  | nil => rfl
  | cons v rest ih =>
      simp [HStack.toVals, StackTyped]
      exact ih

/-- Reconstruct an intrinsically-typed `HStack ts` from any extrinsically well-typed
    `stack : List WasmVal`. -/
def HStack.ofTypedVals : (stack : List WasmVal) → (ts : List WasmTy) →
    StackTyped stack ts → HStack ts
  | [], [], _ => .nil
  | .i32 v :: rest, .i32 :: ts, h =>
      have hrest : StackTyped rest ts := by
        simp [StackTyped, WasmVal.ty] at h
        exact h
      .cons (t := .i32) v (HStack.ofTypedVals rest ts hrest)
  | .i64 v :: rest, .i64 :: ts, h =>
      have hrest : StackTyped rest ts := by
        simp [StackTyped, WasmVal.ty] at h
        exact h
      .cons (t := .i64) v (HStack.ofTypedVals rest ts hrest)
  | .i32 _ :: _, .i64 :: _, h => by
      simp [StackTyped, WasmVal.ty] at h
  | .i64 _ :: _, .i32 :: _, h => by
      simp [StackTyped, WasmVal.ty] at h

@[simp]
theorem HStack.toVals_ofTypedVals (stack : List WasmVal) (ts : List WasmTy)
    (h : StackTyped stack ts) :
    (HStack.ofTypedVals stack ts h).toVals = stack := by
  induction stack generalizing ts with
  | nil =>
      cases ts with
      | nil => rfl
      | cons t ts => simp [StackTyped] at h
  | cons v rest ih =>
      cases v with
      | i32 x =>
          cases ts with
          | nil => simp [StackTyped] at h
          | cons t ts =>
              cases t with
              | i32 =>
                  have hrest : StackTyped rest ts := by
                    simp [StackTyped, WasmVal.ty] at h
                    exact h
                  change WasmVal.i32 x :: (HStack.ofTypedVals rest ts hrest).toVals =
                    WasmVal.i32 x :: rest
                  congr 1
                  exact ih ts hrest
              | i64 => simp [StackTyped, WasmVal.ty] at h
      | i64 x =>
          cases ts with
          | nil => simp [StackTyped] at h
          | cons t ts =>
              cases t with
              | i32 => simp [StackTyped, WasmVal.ty] at h
              | i64 =>
                  have hrest : StackTyped rest ts := by
                    simp [StackTyped, WasmVal.ty] at h
                    exact h
                  change WasmVal.i64 x :: (HStack.ofTypedVals rest ts hrest).toVals =
                    WasmVal.i64 x :: rest
                  congr 1
                  exact ih ts hrest

/-- Intrinsically-typed Wasm instruction family (`aionescu/lean-wasm` style). -/
inductive IWasmInstr : List WasmTy → List WasmTy → Type where
  | nop {rest : List WasmTy} :
      IWasmInstr rest rest
  | unreachable {ts₁ ts₂ : List WasmTy} :
      IWasmInstr ts₁ ts₂
  | drop {t : WasmTy} {rest : List WasmTy} :
      IWasmInstr (t :: rest) rest
  | const32 {rest : List WasmTy} (v : BitVec 32) :
      IWasmInstr rest (.i32 :: rest)
  | const64 {rest : List WasmTy} (v : BitVec 64) :
      IWasmInstr rest (.i64 :: rest)
  | add32 {rest : List WasmTy} :
      IWasmInstr (.i32 :: .i32 :: rest) (.i32 :: rest)
  | divU32 {rest : List WasmTy} :
      IWasmInstr (.i32 :: .i32 :: rest) (.i32 :: rest)
  | load32 {rest : List WasmTy} (offset : UInt32) :
      IWasmInstr (.i32 :: rest) (.i32 :: rest)
  | store32 {rest : List WasmTy} (offset : UInt32) :
      IWasmInstr (.i32 :: .i32 :: rest) rest

/-- Intrinsically-typed single-step evaluator.
    Notice that `.stuckTypeMismatch` does not exist in the return type:
    evaluation returns `Except TrapReason (LinearMem × HStack ts₂)`. -/
def stepIntrinsic {ts₁ ts₂ : List WasmTy} (instr : IWasmInstr ts₁ ts₂)
    (mem : LinearMem) (stk : HStack ts₁) :
    Except TrapReason (LinearMem × HStack ts₂) :=
  match instr, stk with
  | .nop, s => .ok (mem, s)
  | .unreachable, _ => .error .unreachable
  | .drop, .cons _ rest => .ok (mem, rest)
  | .const32 v, s => .ok (mem, .cons (t := .i32) v s)
  | .const64 v, s => .ok (mem, .cons (t := .i64) v s)
  | .add32, .cons (t := .i32) rhs (.cons (t := .i32) lhs rest) =>
      .ok (mem, .cons (t := .i32) (lhs + rhs) rest)
  | .divU32, .cons (t := .i32) rhs (.cons (t := .i32) lhs rest) =>
      if rhs.toNat == 0 then
        .error .divByZero
      else
        .ok (mem, .cons (t := .i32) (BitVec.ofNat 32 (lhs.toNat / rhs.toNat)) rest)
  | .load32 offset, .cons (t := .i32) base rest =>
      match mem.load32? base offset with
      | some v => .ok (mem, .cons (t := .i32) v rest)
      | none => .error .outOfBoundsMem
  | .store32 offset, .cons (t := .i32) val (.cons (t := .i32) base rest) =>
      match mem.store32? base offset val with
      | some mem' => .ok (mem', rest)
      | none => .error .outOfBoundsMem

/-- Erase an intrinsically-typed instruction to its untyped `WasmInstr` counterpart. -/
def IWasmInstr.erase {ts₁ ts₂ : List WasmTy} : IWasmInstr ts₁ ts₂ → WasmInstr
  | .nop => .nop
  | .unreachable => .unreachable
  | .drop => .drop
  | .const32 v => .const32 v
  | .const64 v => .const64 v
  | .add32 => .add32
  | .divU32 => .divU32
  | .load32 offset => .load32 offset
  | .store32 offset => .store32 offset

/-- Erasing an intrinsically-typed instruction yields an extrinsically well-typed instruction. -/
theorem IWasmInstr.erase_typed {ts₁ ts₂ : List WasmTy} (i : IWasmInstr ts₁ ts₂) :
    InstrTyped i.erase ts₁ ts₂ := by
  cases i <;> constructor

/-- Map an intrinsic outcome `Except TrapReason (LinearMem × HStack ts₂)` to
    the corresponding extrinsic `WasmStepOutcome`. -/
def eraseIntrinsicOutcome {ts₂ : List WasmTy} :
    Except TrapReason (LinearMem × HStack ts₂) → WasmStepOutcome
  | .ok (mem', stk') => .next mem' stk'.toVals
  | .error r => .trap r

/-- **Theorem 1a (Intrinsic-to-Extrinsic Lockstep Erasure Correspondence)**:
    Executing an intrinsically-typed instruction `i : IWasmInstr ts₁ ts₂` on `stk : HStack ts₁`
    and erasing the result equals executing `stepExtrinsic i.erase` on the erased stack
    `stk.toVals`. -/
theorem stepIntrinsic_erases_to_extrinsic {ts₁ ts₂ : List WasmTy}
    (i : IWasmInstr ts₁ ts₂) (mem : LinearMem) (stk : HStack ts₁) :
    stepExtrinsic i.erase mem stk.toVals =
      eraseIntrinsicOutcome (stepIntrinsic i mem stk) := by
  cases i with
  | nop => rfl
  | unreachable => rfl
  | drop =>
      cases stk with
      | cons v rest => rfl
  | const32 v => rfl
  | const64 v => rfl
  | add32 =>
      cases stk with
      | cons rhs rest1 =>
          cases rest1 with
          | cons lhs rest2 => rfl
  | divU32 =>
      cases stk with
      | cons rhs rest1 =>
          cases rest1 with
          | cons lhs rest2 =>
              simp only [IWasmInstr.erase, HStack.toVals, WasmTy.toVal,
                stepExtrinsic, stepIntrinsic]
              split <;> rfl
  | load32 offset =>
      cases stk with
      | cons base rest =>
          simp only [IWasmInstr.erase, HStack.toVals, WasmTy.toVal,
            stepExtrinsic, stepIntrinsic]
          cases mem.load32? base offset <;> rfl
  | store32 offset =>
      cases stk with
      | cons val rest1 =>
          cases rest1 with
          | cons base rest2 =>
              simp only [IWasmInstr.erase, HStack.toVals, WasmTy.toVal,
                stepExtrinsic, stepIntrinsic]
              cases mem.store32? base offset val <;> rfl

/-- Intrinsically-typed instruction sequences (`IWasmSeq ts₁ ts₂`). -/
inductive IWasmSeq : List WasmTy → List WasmTy → Type where
  | nil {ts : List WasmTy} : IWasmSeq ts ts
  | cons {ts₁ ts₂ ts₃ : List WasmTy}
      (head : IWasmInstr ts₁ ts₂) (tail : IWasmSeq ts₂ ts₃) :
      IWasmSeq ts₁ ts₃

/-- Evaluate an intrinsically-typed sequence. -/
def execIntrinsicSeq : {ts₁ ts₂ : List WasmTy} →
    IWasmSeq ts₁ ts₂ → LinearMem → HStack ts₁ →
    Except TrapReason (LinearMem × HStack ts₂)
  | _, _, .nil, mem, stk => .ok (mem, stk)
  | _, _, .cons head tail, mem, stk =>
      match stepIntrinsic head mem stk with
      | .ok (mem', stk') => execIntrinsicSeq tail mem' stk'
      | .error r => .error r

/-- Erase an `IWasmSeq` to `List WasmInstr`. -/
def IWasmSeq.erase : {ts₁ ts₂ : List WasmTy} → IWasmSeq ts₁ ts₂ → List WasmInstr
  | _, _, .nil => []
  | _, _, .cons head tail => head.erase :: tail.erase

/-- **Theorem 1b (Multi-Step Sequence Erasure Correspondence)**:
    Multi-step intrinsic evaluation and multi-step extrinsic evaluation commute with erasure. -/
theorem execIntrinsicSeq_erases_to_extrinsic {ts₁ ts₂ : List WasmTy}
    (seq : IWasmSeq ts₁ ts₂) (mem : LinearMem) (stk : HStack ts₁) :
    execExtrinsicSeq seq.erase mem stk.toVals =
      eraseIntrinsicOutcome (execIntrinsicSeq seq mem stk) := by
  induction seq generalizing mem with
  | nil => rfl
  | cons head tail ih =>
      simp only [IWasmSeq.erase, execExtrinsicSeq,
        stepIntrinsic_erases_to_extrinsic, execIntrinsicSeq]
      cases stepIntrinsic head mem stk with
      | error r => rfl
      | ok pair => exact ih pair.1 pair.2

/-- Every extrinsically well-typed `WasmInstr` is the erasure of an `IWasmInstr ts₁ ts₂`. -/
theorem InstrTyped.exists_intrinsic {i : WasmInstr} {ts₁ ts₂ : List WasmTy}
    (h : InstrTyped i ts₁ ts₂) :
    ∃ (i_intr : IWasmInstr ts₁ ts₂), i_intr.erase = i := by
  cases h with
  | nop _ => exact ⟨.nop, rfl⟩
  | unreachable _ _ => exact ⟨.unreachable, rfl⟩
  | drop _ _ => exact ⟨.drop, rfl⟩
  | const32 v _ => exact ⟨.const32 v, rfl⟩
  | const64 v _ => exact ⟨.const64 v, rfl⟩
  | add32 _ => exact ⟨.add32, rfl⟩
  | divU32 _ => exact ⟨.divU32, rfl⟩
  | load32 off _ => exact ⟨.load32 off, rfl⟩
  | store32 off _ => exact ⟨.store32 off, rfl⟩

/-- **Theorem 1c (Extrinsic Syntactic Type Safety — Progress & Preservation)**:
    If `InstrTyped i ts₁ ts₂` and `StackTyped stk ts₁`, then `stepExtrinsic i mem stk`
    never hits `.stuckTypeMismatch`: it either traps (`.trap r`) or steps to `.next mem' stk'`
    preserving `StackTyped stk' ts₂`. -/
theorem extrinsic_progress_and_preservation {i : WasmInstr} {ts₁ ts₂ : List WasmTy}
    (hi : InstrTyped i ts₁ ts₂) (mem : LinearMem) (stk : List WasmVal)
    (hstk : StackTyped stk ts₁) :
    (∃ r, stepExtrinsic i mem stk = .trap r) ∨
    (∃ mem' stk', stepExtrinsic i mem stk = .next mem' stk' ∧ StackTyped stk' ts₂) := by
  obtain ⟨i_intr, hi_erase⟩ := InstrTyped.exists_intrinsic hi
  let hstk_intr := HStack.ofTypedVals stk ts₁ hstk
  have h_eq := stepIntrinsic_erases_to_extrinsic i_intr mem hstk_intr
  rw [hi_erase, HStack.toVals_ofTypedVals] at h_eq
  rw [h_eq]
  cases stepIntrinsic i_intr mem hstk_intr with
  | error r => exact Or.inl ⟨r, rfl⟩
  | ok pair =>
      exact Or.inr ⟨pair.1, pair.2.toVals, rfl, HStack.toVals_typed pair.2⟩

/-!
### Primary-Source Pitfall: Unconstrained Reduction Rules (`linobit-corp/wasm-lean`)

In `linobit-corp/wasm-lean` (`WasmLean/Semantics/Reduce.lean:339-343`), the relational
semantics `Reduce` includes an unconstrained catch-all constructor `r_interp_flat`
with **zero hypotheses**, relating `consumed ++ [bi] ++ base` to `produced ++ base`
for ANY `consumed`, `produced`, and `bi`. We prove here that such a constructor makes
even a deliberately bogus interpreter "sound".
-/

/-- An unconstrained reduction step modeled on `WasmLean.Semantics.Reduce.r_interp_flat`. -/
inductive UnconstrainedReduce :
    List WasmVal → List WasmInstr → List WasmVal → List WasmInstr → Prop where
  | r_interp_flat (stk stk' : List WasmVal) (i : WasmInstr) (rest : List WasmInstr) :
      UnconstrainedReduce stk (i :: rest) stk' rest

/-- **Theorem 1d (`linobit_unconstrained_reduce_vacuity`)**:
    Under `UnconstrainedReduce`, ANY arbitrary function `bogusInterp` (even one that
    ignores the instruction and fabricates `[.i32 0xDEAD_BEEF#32]`) satisfies the
    single-step interpreter soundness theorem! -/
theorem linobit_unconstrained_reduce_vacuity
    (bogusInterp : WasmInstr → List WasmVal → List WasmVal)
    (stk : List WasmVal) (i : WasmInstr) (rest : List WasmInstr) :
    UnconstrainedReduce stk (i :: rest) (bogusInterp i stk) rest :=
  UnconstrainedReduce.r_interp_flat stk (bogusInterp i stk) i rest

end WasmExtrinsicIntrinsic

/-!
## Part 2: Wasm `trap` vs. Source Rust `Partial.ub` in Anneal's `Compiles MirLang WasmLang`

In WebAssembly (`WebAssembly 2.0/3.0 §4.2.4` and `cajal-technologies/talos`
`SmallStepOutcomeAdequacy.lean`), a `trap` (`unreachable`, division by zero, or
out-of-bounds linear memory access) is a **deterministic, well-defined terminal outcome**,
NOT undefined behavior (`Partial.ub`).

In contrast, in Rust MIR (`Trusted/MirSemantics.lean`), dereferencing an out-of-bounds
raw pointer `*ptr` is **undefined behavior** (`.failed .ub`, so `defined = False`).

Here we instantiate Anneal's `SmallStepMachine` and `StepLang` for both `MirLang` and
`WasmLang`, and prove the four foundational refinement and non-refinement theorems
governing Rust-to-Wasm compilation.
-/
namespace WasmTrapVsRustUb

open AnnealCore
open WasmExtrinsicIntrinsic

/-- Query environment for a memory load: an address `addr : BitVec 32` and an initial
    byte memory `mem : LinearMem`. -/
structure LoadQuery where
  addr : BitVec 32
  mem : LinearMem

/-- Source Rust MIR raw-pointer load program, parameterized by the size `allocLen : Nat`
    of the live Rust allocation backing the pointer. -/
structure MirRawLoadProg where
  allocLen : Nat

/-- Target Wasm `i32.load` program, parameterized by the static `memarg.offset`. -/
structure WasmLoadProg where
  offset : UInt32

/-- Execution states of the 1-step machines (`running` before the load). -/
inductive OneStepState (Query : Type) where
  | start (q : Query)

/-- Rust MIR small-step machine for raw pointer dereference:
    - If `q.addr.toNat + 4 ≤ p.allocLen` AND `q.addr.toNat + 4 ≤ q.mem.size`, it reads the
      32-bit little-endian word at `q.addr` and terminates normally (`.terminated (.normal v)`).
    - Otherwise, dereferencing the raw pointer is **Undefined Behavior** (`.failed .ub`)! -/
def MirLoadMachine : SmallStepMachine MirRawLoadProg LoadQuery where
  State := OneStepState LoadQuery
  Val := BitVec 32
  init := fun _ q => .start q
  step := fun p s res =>
    match s with
    | .start q =>
        if q.addr.toNat + 4 ≤ p.allocLen then
          match q.mem.load32? q.addr 0 with
          | some v => res = .terminated (.normal v)
          | none => res = .failed .ub
        else
          res = .failed .ub

/-- Wasm small-step machine for `i32.load offset`:
    - If `effectiveAddr q.addr p.offset + 4 ≤ q.mem.size`, it terminates normally with the
      loaded 32-bit word (`.terminated (.normal v)`).
    - If `effectiveAddr q.addr p.offset + 4 > q.mem.size`, Wasm **deterministically traps**!
      In `StepResult`, a deterministic Wasm trap is modeled as `.terminated .unwind`
      (an observable, non-UB abort exit with `PrefixOutcome.isSafe = True`). -/
def WasmLoadMachine : SmallStepMachine WasmLoadProg LoadQuery where
  State := OneStepState LoadQuery
  Val := BitVec 32
  init := fun _ q => .start q
  step := fun p s res =>
    match s with
    | .start q =>
        match q.mem.load32? q.addr p.offset with
        | some v => res = .terminated (.normal v)
        | none => res = .terminated .unwind

/-- Source MIR `Language` instance via Anneal's `StepLang`. -/
def MirLang : Language := StepLang MirLoadMachine

/-- Target Wasm `Language` instance via Anneal's `StepLang`. -/
def WasmLang : Language := StepLang WasmLoadMachine

/-- Identity behavioral translation map `π_mir_wasm` between `MirLang` and `WasmLang`
    (since both share `LoadQuery → Partial PropSpec`). -/
def π_mir_wasm (b : MirLang.Beh) : WasmLang.Beh := b

theorem π_mir_wasm_monotone : Monotone π_mir_wasm :=
  fun h => h

/-- **Theorem 2a (`wasm_trap_is_defined_not_ub`)**:
    For EVERY Wasm `i32.load` program `wprog` and EVERY query `q` (including out-of-bounds
    addresses that trigger a Wasm `trap`), the Wasm behavior is well-defined
    (`(WasmLang.sem wprog q).defined = True`). A deterministic Wasm `trap` is never `Partial.ub`. -/
theorem wasm_trap_is_defined_not_ub (wprog : WasmLoadProg) (q : LoadQuery) :
    (WasmLang.sem wprog q).defined := by
  intro n out hreach
  cases hreach with
  | zero => trivial
  | terminated _ => trivial
  | outOfFuel _ => trivial
  | failed hfail =>
      dsimp [WasmLoadMachine] at hfail
      split at hfail <;> contradiction
  | step hnext _ =>
      dsimp [WasmLoadMachine] at hnext
      split at hnext <;> contradiction

/-- Conversely, an out-of-bounds Rust MIR raw-pointer load (`q.addr.toNat + 4 > mprog.allocLen`)
    is **Undefined Behavior** (`¬ (MirLang.sem mprog q).defined`). -/
theorem mir_oob_raw_load_is_ub (mprog : MirRawLoadProg) (q : LoadQuery)
    (hoob : ¬ (q.addr.toNat + 4 ≤ mprog.allocLen)) :
    ¬ (MirLang.sem mprog q).defined := by
  intro hdef
  have hstep : MirLoadMachine.step mprog (.start q) (.failed .ub) := by
    dsimp [MirLoadMachine]
    simp [hoob]
  have hreach : ReachesPrefix MirLoadMachine mprog 1 (.start q) (.failed .ub) :=
    ReachesPrefix.failed hstep
  exact hdef 1 (.failed .ub) hreach

/-- Similarly, if `q.mem.load32? q.addr 0 = none`, the MIR raw-pointer load is UB. -/
theorem mir_unmapped_raw_load_is_ub (mprog : MirRawLoadProg) (q : LoadQuery)
    (hnone : q.mem.load32? q.addr 0 = none) :
    ¬ (MirLang.sem mprog q).defined := by
  intro hdef
  have hstep : MirLoadMachine.step mprog (.start q) (.failed .ub) := by
    dsimp [MirLoadMachine]
    split
    · simp [hnone]
    · rfl
  have hreach : ReachesPrefix MirLoadMachine mprog 1 (.start q) (.failed .ub) :=
    ReachesPrefix.failed hstep
  exact hdef 1 (.failed .ub) hreach

/-- **Theorem 2b (`rustc_raw_load_to_wasm_compiles`)**:
    Compiling a Rust MIR raw-pointer load (`mprog`) to a Wasm `i32.load offset=0`
    (`⟨0⟩`) **satisfies Anneal's `Compiles MirLang WasmLang π_mir_wasm`** for all
    queries!
    - When `q.addr.toNat + 4 ≤ mprog.allocLen` and `q.addr.toNat + 4 ≤ q.mem.size`,
      both machines return the exact same loaded word `.terminated (.normal v)`.
    - When `q.addr.toNat + 4 > mprog.allocLen` (or `> q.mem.size`), the source MIR
      program has `defined = False` (`Partial.ub`), which is refined by Wasm's
      well-defined load or deterministic `.trap`! -/
theorem rustc_raw_load_to_wasm_compiles (mprog : MirRawLoadProg) :
    Compiles MirLang WasmLang π_mir_wasm mprog ⟨0⟩ := by
  intro q hmir_def
  refine ⟨wasm_trap_is_defined_not_ub ⟨0⟩ q, ?_⟩
  intro out ⟨n, hwasm_reach⟩
  cases hwasm_reach with
  | zero =>
      exact ⟨0, ReachesPrefix.zero (MirLoadMachine.init mprog q)⟩
  | terminated hstep =>
      dsimp [WasmLoadMachine] at hstep
      by_cases halloc : q.addr.toNat + 4 ≤ mprog.allocLen
      · cases hload : q.mem.load32? q.addr 0 with
        | some v =>
            rw [hload] at hstep
            injection hstep with ht
            subst ht
            refine ⟨1, ReachesPrefix.terminated ?_⟩
            dsimp [MirLoadMachine]
            simp [halloc, hload]
        | none =>
            exact False.elim (mir_unmapped_raw_load_is_ub mprog q hload hmir_def)
      · exact False.elim (mir_oob_raw_load_is_ub mprog q halloc hmir_def)
  | failed hfail =>
      dsimp [WasmLoadMachine] at hfail
      split at hfail <;> contradiction
  | outOfFuel hout =>
      dsimp [WasmLoadMachine] at hout
      split at hout <;> contradiction
  | step hnext _ =>
      dsimp [WasmLoadMachine] at hnext
      split at hnext <;> contradiction

/-- **Theorem 2c (`wasm_linear_memory_lack_of_provenance`)**:
    When a Rust raw pointer overflows its allocation (`mprog.allocLen < q.addr.toNat + 4`)
    but still lands within allocated Wasm linear memory (`q.addr.toNat + 4 ≤ q.mem.size`),
    Wasm `i32.load` **does not trap**—it silently succeeds and returns the unrelated word
    stored at `q.addr` in linear memory!
    This proves that Wasm's linear-memory trap check is only a sandbox boundary, NOT a
    spatial memory-safety sanitizer for individual Rust allocations. -/
theorem wasm_linear_memory_lack_of_provenance
    (mprog : MirRawLoadProg) (q : LoadQuery)
    (hoob_rust : ¬ (q.addr.toNat + 4 ≤ mprog.allocLen))
    (hin_wasm : q.addr.toNat + 4 ≤ q.mem.size) :
    ¬ (MirLang.sem mprog q).defined ∧
    ∃ v, ReachesPrefix WasmLoadMachine ⟨0⟩ 1 (.start q) (.terminated (.normal v)) := by
  refine ⟨mir_oob_raw_load_is_ub mprog q hoob_rust, ?_⟩
  have hea : effectiveAddr q.addr 0 + 4 ≤ q.mem.size := by
    simpa [effectiveAddr] using hin_wasm
  have hload : ∃ v, q.mem.load32? q.addr 0 = some v := by
    unfold LinearMem.load32?
    simp [hea]
  obtain ⟨v, hv⟩ := hload
  refine ⟨v, ReachesPrefix.terminated ?_⟩
  dsimp [WasmLoadMachine]
  rw [hv]

/-- Abstract contract `EnsuresNoTrap`: requires every execution to be safe AND forbids
    `.terminated .unwind` (Wasm trap). -/
def EnsuresNoTrap : WasmLang.Beh :=
  fun _ =>
    { defined := True
      val := fun _ out => out ≠ .terminated .unwind }

/-- Abstract contract `EnsuresValueOrTrap`: requires every execution to be safe
    (no `.failed .ub`) and permits either `.normal v`, `.unwind` (Wasm trap),
    or `.outOfFuel`. -/
def EnsuresValueOrTrap : WasmLang.Beh :=
  fun _ =>
    { defined := True
      val := fun _ out =>
        (∃ v, out = .terminated (.normal v)) ∨
        out = .terminated .unwind ∨
        out = .outOfFuel }

/-- Lemma: on an out-of-bounds Wasm address, `WasmLoadMachine` reaches `.terminated .unwind`
    in 1 step. -/
theorem wasm_oob_reaches_trap_unwind (q : LoadQuery)
    (hoob_wasm : ¬ (q.addr.toNat + 4 ≤ q.mem.size)) :
    ReachesPrefix WasmLoadMachine ⟨0⟩ 1 (.start q) (.terminated .unwind) := by
  apply ReachesPrefix.terminated
  dsimp [WasmLoadMachine]
  have hload : q.mem.load32? q.addr 0 = none := by
    unfold LinearMem.load32?
    have hea : ¬ (effectiveAddr q.addr 0 + 4 ≤ q.mem.size) := by
      simpa [effectiveAddr] using hoob_wasm
    simp [hea]
  rw [hload]

/-- **Theorem 2d (`wasm_trap_refutes_ensuresNoTrap`)**:
    When a Wasm linear-memory load can reach an out-of-bounds address
    (`¬ (q.addr.toNat + 4 ≤ q.mem.size)`), the Wasm program **violates**
    `EnsuresNoTrap` (`¬ (WasmLang.sem ⟨0⟩ q ≤ EnsuresNoTrap q)`)! -/
theorem wasm_trap_refutes_ensuresNoTrap (q : LoadQuery)
    (hoob_wasm : ¬ (q.addr.toNat + 4 ≤ q.mem.size)) :
    ¬ (WasmLang.sem ⟨0⟩ q ≤ EnsuresNoTrap q) := by
  intro hle
  obtain ⟨_, hsub⟩ := hle trivial
  have htrap := wasm_oob_reaches_trap_unwind q hoob_wasm
  exact hsub (.terminated .unwind) ⟨1, htrap⟩ rfl

/-- **Theorem 2e (`wasm_trap_satisfies_valueOrTrap`)**:
    For EVERY Wasm `i32.load` program `wprog` and EVERY query `q` (even when `q` is
    out-of-bounds and triggers a Wasm trap), `WasmLang.sem wprog ≤ EnsuresValueOrTrap`! -/
theorem wasm_trap_satisfies_valueOrTrap (wprog : WasmLoadProg) :
    WasmLang.sem wprog ≤ EnsuresValueOrTrap := by
  intro q _
  refine ⟨wasm_trap_is_defined_not_ub wprog q, ?_⟩
  intro out ⟨n, hreach⟩
  cases hreach with
  | zero => exact Or.inr (Or.inr rfl)
  | terminated hstep =>
      dsimp [WasmLoadMachine] at hstep
      split at hstep
      · rename_i v _
        injection hstep with ht
        subst ht
        exact Or.inl ⟨v, rfl⟩
      · injection hstep with ht
        subst ht
        exact Or.inr (Or.inl rfl)
  | failed hfail =>
      dsimp [WasmLoadMachine] at hfail
      split at hfail <;> contradiction
  | outOfFuel hout =>
      dsimp [WasmLoadMachine] at hout
      split at hout <;> contradiction
  | step hnext _ =>
      dsimp [WasmLoadMachine] at hnext
      split at hnext <;> contradiction

/-- **Theorem 2f (`wasm32_u32_wrapping_vs_memarg_offset`)**:
    Demonstrates the 32-bit `usize` wrapping hazard when lowering pointer arithmetic to
    `wasm32`:
    Suppose linear memory has 1 page (`65,536` bytes), `base = 0xFFFF_FFF0#32`, and
    `offset = 0x20`.
    1. If a compiler lowers `base + offset` to a 32-bit `i32.add` followed by `i32.load offset=0`,
       the address wraps modulo `2^32` to `0x0000_0010#32`, which is `< 65536` and **silently
       loads** from address `0x10` without trapping!
    2. If the compiler places `offset = 0x20` in Wasm's static `memarg.offset` field
       (`i32.load offset=0x20`), Wasm's `effectiveAddr` computes
       `0xFFFF_FFF0 + 0x20 = 0x1_0000_0010` in unbounded `Nat`, which exceeds `65536` and
       **deterministically traps**! -/
theorem wasm32_u32_wrapping_vs_memarg_offset (mem : LinearMem)
    (hsize : mem.size = 65536) :
    let base : BitVec 32 := 0xFFFFFFF0#32
    let off32 : BitVec 32 := 0x00000020#32
    let offImm : UInt32 := 0x20
    (effectiveAddr (base + off32) 0 + 4 ≤ mem.size) ∧
    ¬ (effectiveAddr base offImm + 4 ≤ mem.size) := by
  dsimp only
  rw [hsize]
  unfold effectiveAddr
  decide

end WasmTrapVsRustUb

/-!
## Part 3: eBPF Verifier as Anneal `VerifiedChecker` & Kops Dual-Sequence Soundness

In the Linux eBPF ecosystem (`CertrBPF` in Coq, `Jitterbug` in Rosette, and `Kops` /
`KinsnLean4` in Lean 4.28.0 at `eunomia-bpf/bpf-benchmark`), the in-kernel eBPF verifier
statically checks program safety (no division by zero, no out-of-bounds packet/context loads)
before JIT compilation.

Kops (`arXiv:2606.24213`) extends the eBPF JIT with target-specific instructions (`kinsn`)
without modifying the verifier's abstract-interpretation pass by maintaining a **dual
representation**:
1. A vanilla eBPF **proof sequence** (`seq_proof`) checked by the existing eBPF verifier.
2. A target-specific **native emission** (`seq_native`) proved equivalent to `seq_proof`
   in Lean 4 (`KinsnEquiv.arm_refines` / `KinsnEquiv.x86_refines`).

Here we mechanize an eBPF verifier as an Anneal `VerifiedChecker` and prove that Kops's
dual-sequence architecture is a direct corollary of `VerifiedChecker.check_sound` composed
with `Compiles.preserves_abstraction`.
-/
namespace EbpfVerifierAndKopsBridge

open AnnealCore

/-- Simplified straight-line eBPF instruction set with ALU and packet-access operations. -/
inductive EbpfInstr where
  | movImm (val : UInt32)
  | addImm (val : UInt32)
  | divImm (divisor : UInt32)
  | loadPkt32 (off : Nat)
  deriving DecidableEq, Repr

/-- eBPF execution context: packet length `pktLen` and packet byte contents `pktWord`. -/
structure EbpfQuery where
  pktLen : Nat
  pktWord : Nat → UInt32

/-- Evaluate a straight-line eBPF program on `q : EbpfQuery`, returning `some r0` on normal
    completion or `none` on runtime fault (division by zero or out-of-bounds packet read). -/
def evalEbpfProg : List EbpfInstr → EbpfQuery → UInt32 → Option UInt32
  | [], _, r0 => some r0
  | .movImm v :: rest, q, _ => evalEbpfProg rest q v
  | .addImm v :: rest, q, r0 => evalEbpfProg rest q (r0 + v)
  | .divImm d :: rest, q, r0 =>
      if d == 0 then none else evalEbpfProg rest q (r0 / d)
  | .loadPkt32 off :: rest, q, _ =>
      if off + 4 ≤ q.pktLen then
        evalEbpfProg rest q (q.pktWord off)
      else
        none

/-- Small-step machine wrapper for eBPF programs. -/
def EbpfMachine : SmallStepMachine (List EbpfInstr) EbpfQuery where
  State := WasmTrapVsRustUb.OneStepState EbpfQuery
  Val := UInt32
  init := fun _ q => .start q
  step := fun prog s res =>
    match s with
    | .start q =>
        match evalEbpfProg prog q 0 with
        | some r0 => res = .terminated (.normal r0)
        | none => res = .failed .ub

/-- `EbpfLang` induced by `EbpfMachine`. -/
def EbpfLang : Language := StepLang EbpfMachine

/-- Static eBPF verifier check for a single instruction under a known minimum packet size
    `minPktLen` (established by a preceding packet-pointer guard `pkt_data + minPktLen <= pkt_end`). -/
def ebpfCheckInstr (minPktLen : Nat) : EbpfInstr → Bool
  | .movImm _ => true
  | .addImm _ => true
  | .divImm d => !(d == 0)
  | .loadPkt32 off => decide (off + 4 ≤ minPktLen)

/-- Static eBPF verifier over an instruction sequence. -/
def ebpfVerifierCheck (minPktLen : Nat) (prog : List EbpfInstr) : Bool :=
  prog.all (ebpfCheckInstr minPktLen)

/-- Lemma: if `ebpfVerifierCheck minPktLen prog = true` and `minPktLen ≤ q.pktLen`,
    `evalEbpfProg prog q r0` never fails (`∃ res, evalEbpfProg prog q r0 = some res`). -/
theorem evalEbpfProg_safe_of_check (minPktLen : Nat) (prog : List EbpfInstr)
    (q : EbpfQuery) (r0 : UInt32)
    (hcheck : ebpfVerifierCheck minPktLen prog = true)
    (hpkt : minPktLen ≤ q.pktLen) :
    ∃ res, evalEbpfProg prog q r0 = some res := by
  induction prog generalizing r0 with
  | nil => exact ⟨r0, rfl⟩
  | cons i rest ih =>
      simp only [ebpfVerifierCheck, List.all_cons, Bool.and_eq_true] at hcheck
      obtain ⟨hi, hrest⟩ := hcheck
      cases i with
      | movImm v => exact ih v hrest
      | addImm v => exact ih (r0 + v) hrest
      | divImm d =>
          simp only [ebpfCheckInstr, Bool.not_eq_true'] at hi
          simp only [evalEbpfProg, hi]
          exact ih (r0 / d) hrest
      | loadPkt32 off =>
          simp only [ebpfCheckInstr, decide_eq_true_eq] at hi
          have hoff : off + 4 ≤ q.pktLen := Nat.le_trans hi hpkt
          simp only [evalEbpfProg, hoff, ↓reduceIte]
          exact ih (q.pktWord off) hrest

/-- Abstract safety specification `EbpfWellFormed minPktLen`: on every query `q` with
    `minPktLen ≤ q.pktLen`, the program is guaranteed free of `.failed .ub` (`defined = True`),
    and every reachable outcome satisfies `PrefixOutcome.isSafe`. -/
def EbpfWellFormed (minPktLen : Nat) : EbpfLang.Beh :=
  fun q =>
    { defined := minPktLen ≤ q.pktLen
      val := fun _ out => out.isSafe }

/-- **Theorem 3a (`ebpfVerifier_is_verifiedChecker`)**:
    For every `minPktLen`, `ebpfVerifierCheck minPktLen` forms a sound Anneal
    `VerifiedChecker EbpfLang (fun _ => EbpfWellFormed minPktLen)`. -/
def ebpfVerifiedChecker (minPktLen : Nat) :
    VerifiedChecker EbpfLang (fun _ => EbpfWellFormed minPktLen) where
  check := ebpfVerifierCheck minPktLen
  check_sound := by
    intro prog hcheck q hpkt
    have hdef : (EbpfLang.sem prog q).defined := by
      intro n out hreach
      obtain ⟨res, heval⟩ := evalEbpfProg_safe_of_check minPktLen prog q 0 hcheck hpkt
      cases hreach with
      | zero => trivial
      | terminated _ => trivial
      | outOfFuel _ => trivial
      | failed hfail =>
          dsimp [EbpfMachine] at hfail
          rw [heval] at hfail
          contradiction
      | step hnext _ =>
          dsimp [EbpfMachine] at hnext
          rw [heval] at hnext
          contradiction
    exact ⟨hdef, fun out ⟨n, hreach⟩ => hdef n out hreach⟩

/-- **Theorem 3b (`kops_dual_sequence_jit_soundness`)**:
    Formalizes the Kops (`arXiv:2606.24213` / `KinsnLean4`) dual-sequence verification bridge
    inside Anneal:
    Suppose `NativeJitLang` is a target native ISA (e.g., ARM64 or x86-64) with a monotone
    behavioral translation `π_jit : EbpfLang.Beh → NativeJitLang.Beh`.
    If:
    1. `ebpfVerifierCheck minPktLen seq_proof = true` (the unmodified eBPF verifier accepts
       the vanilla eBPF proof sequence `seq_proof`), and
    2. `Compiles EbpfLang NativeJitLang π_jit seq_proof seq_native` (the Lean 4 `KinsnEquiv`
       proof certifies that the native JIT sequence `seq_native` refines `seq_proof`),
    then `seq_native` is guaranteed to satisfy `π_jit (EbpfWellFormed minPktLen)` without
    modifying the eBPF verifier! -/
theorem kops_dual_sequence_jit_soundness
    (NativeJitLang : Language)
    (π_jit : EbpfLang.Beh → NativeJitLang.Beh)
    (h_mono : Monotone π_jit)
    (minPktLen : Nat)
    (seq_proof : List EbpfInstr)
    (seq_native : NativeJitLang.Prog)
    (h_verified : (ebpfVerifiedChecker minPktLen).check seq_proof = true)
    (h_kinsn_equiv : Compiles EbpfLang NativeJitLang π_jit seq_proof seq_native) :
    NativeJitLang.sem seq_native ≤ π_jit (EbpfWellFormed minPktLen) := by
  have h_wf : EbpfLang.sem seq_proof ≤ EbpfWellFormed minPktLen :=
    (ebpfVerifiedChecker minPktLen).check_sound seq_proof h_verified
  exact Preorder.le_trans h_kinsn_equiv (h_mono h_wf)

end EbpfVerifierAndKopsBridge

/-!
## Axiom Audit

We verify at compile time via `#guard_msgs` and `#print axioms` that none of our headline
theorems use `sorryAx` or any non-standard axioms.
-/

/-- info: 'WasmExtrinsicIntrinsic.stepIntrinsic_erases_to_extrinsic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WasmExtrinsicIntrinsic.stepIntrinsic_erases_to_extrinsic

/-- info: 'WasmExtrinsicIntrinsic.execIntrinsicSeq_erases_to_extrinsic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WasmExtrinsicIntrinsic.execIntrinsicSeq_erases_to_extrinsic

/-- info: 'WasmExtrinsicIntrinsic.extrinsic_progress_and_preservation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WasmExtrinsicIntrinsic.extrinsic_progress_and_preservation

/-- info: 'WasmExtrinsicIntrinsic.linobit_unconstrained_reduce_vacuity' does not depend on any axioms -/
#guard_msgs in
#print axioms WasmExtrinsicIntrinsic.linobit_unconstrained_reduce_vacuity

/-- info: 'WasmTrapVsRustUb.wasm_trap_is_defined_not_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WasmTrapVsRustUb.wasm_trap_is_defined_not_ub

/-- info: 'WasmTrapVsRustUb.rustc_raw_load_to_wasm_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WasmTrapVsRustUb.rustc_raw_load_to_wasm_compiles

/-- info: 'WasmTrapVsRustUb.wasm_linear_memory_lack_of_provenance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WasmTrapVsRustUb.wasm_linear_memory_lack_of_provenance

/-- info: 'WasmTrapVsRustUb.wasm_trap_refutes_ensuresNoTrap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WasmTrapVsRustUb.wasm_trap_refutes_ensuresNoTrap

/-- info: 'WasmTrapVsRustUb.wasm_trap_satisfies_valueOrTrap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms WasmTrapVsRustUb.wasm_trap_satisfies_valueOrTrap

/-- info: 'WasmTrapVsRustUb.wasm32_u32_wrapping_vs_memarg_offset' does not depend on any axioms -/
#guard_msgs in
#print axioms WasmTrapVsRustUb.wasm32_u32_wrapping_vs_memarg_offset

/-- info: 'EbpfVerifierAndKopsBridge.ebpfVerifiedChecker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms EbpfVerifierAndKopsBridge.ebpfVerifiedChecker

/-- info: 'EbpfVerifierAndKopsBridge.kops_dual_sequence_jit_soundness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms EbpfVerifierAndKopsBridge.kops_dual_sequence_jit_soundness
