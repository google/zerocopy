-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# AnLLVM Middle-End Optimization Passes Probe (`opt` Adaptation in Anneal)

This standalone Lean `v4.34.1` development mechanizes a compositional 4-pass
middle-end optimization pipeline for `AnLLVM` under Anneal's `Trusted.Language`
and `BB-8` (`PassCompiler` / `CertChecker`) architecture:

1. **Section 1 (`Trusted` & `BB-8` Foundation):**
   Defines the constructive demonic refinement preorder (`Preorder`, `Partial`,
   `Behavior`), spine-indexed languages (`Language SemObs`), representation
   codecs (`BehaviorCodec`), downward compilation (`Compiles` and miracle-free
   `ProductiveCompiles`), and the `BB-8` proof-gated compiler combinators
   (`PassCompiler`, `PassCompiler.comp`, and `CertChecker`).
2. **Section 2 (`AnLLVM` Operational Semantics & Poison Lattice):**
   Models `AnLLVM` values (`PoisonOr Nat`), directional poison refinement
   (`IsRefinedBy`), registers (`RegId`), frame-private stack `alloca` slices
   (`AllocId × Nat`), caller-visible heap memory with `MemorySSA` version tokens,
   straight-line blocks (`preheader` and `epilogue`), and canonical rotated
   loops (`AnLoop` with `IndVarMode.mulRecurrence` vs. `IndVarMode.scevAddRec`).
3. **Section 3 (Pass 1 — `SroaAndMem2RegCertChecker`):**
   Validates Scalar Replacement of Aggregates (`SROA`) and SSA promotion
   (`PromoteMemToReg`) via a certificate checker (`checkSroaMem2Reg`) that
   verifies pairwise byte-interval disjointness of aggregate slices (`SROA`),
   non-escape of promoted `AllocId`s, and store-to-register forwarding
   (`Mem2Reg`). Proves `checkSroaMem2Reg_sound` (`ProductiveCompiles`) and
   negative canaries (`canary_sroa_overlapping_slices_rejected` and
   `canary_sroa_escaped_alloca_rejected`).
4. **Section 4 (Pass 2 — `TableDrivenInstCombine` + `DemandedBitsBDCE`):**
   Implements a constructively verified (Mode A / Mode C) instruction combiner
   and bit-tracking dead-code eliminator (`BDCE`). Proves algebraic identity
   rewrites (`x + 0 ↦ x`, `x * 1 ↦ x`, `x | 0 ↦ x`), freeze-guarded self-cancel
   rewrites (`sub x x ↦ 0` when `x` is frozen, plus a negative canary refuting
   unfrozen `sub .poison .poison ↦ 0`), and the demanded-bits absorption law
   `(x ||| c₁) &&& c₂ ↦ x &&& c₂` whenever `c₁ &&& c₂ = 0`
   (`nat_or_and_demanded_eq`). Proves universal soundness
   `instCombineBdce_productiveCompiles` for all programs `p : AnLLVMProg`.
5. **Section 5 (Pass 3 — `MemorySsaGvnDseCertChecker`):**
   Validates `NewGVN` store-to-load forwarding, redundant load CSE, and Dead
   Store Elimination (`DSE`) over `MemorySSA` `MemoryDef`/`MemoryUse` tokens
   across provably non-aliasing `(AllocId, offset)` locations. Proves
   `checkMemSsaGvnDse_sound` (`ProductiveCompiles`) and refutes DSE across an
   intervening aliasing load (`canary_dse_across_aliasing_load_rejected` and
   `canary_dse_across_aliasing_load_unsound`).
6. **Section 6 (Pass 4 — `ScevIndVarAndLicmCertChecker`):**
   Validates Scalar Evolution (`SCEV`) affine induction-variable strength
   reduction (`base + i * stride ↦ {base, +, stride}` via
   `scev_affine_recurrence_eq`) and Loop-Invariant Code Motion (`LICM`) into the
   loop preheader with non-trapping speculation guards. Proves
   `checkScevLicm_sound` (`ProductiveCompiles`) and two negative canaries
   (`canary_scev_wrong_step_rejected` and
   `canary_licm_trapping_div_on_zero_trip_unsound`).
7. **Section 7 (End-to-End Composed `AnLLVM` `-O2` Core Pipeline):**
   Composes all four passes via `PassCompiler.comp` into
   `anllvmO2CorePipeline` and verifies a complete multi-stage optimization of a
   realistic `AnLLVM` kernel (`anllvmO2CorePipeline_verified`) in $O(1)$ kernel
   reduction steps with zero `sorryAx`, zero `Classical.choice`, and zero
   `Lean.ofReduceBool`.
-/

namespace AnLLVMMiddleEndProbe

-- ============================================================================
-- Section 1: Trusted Refinement Kernel & BB-8 PassCompiler / CertChecker Core
-- ============================================================================

namespace Trusted

/-- A reflexive and transitive refinement preorder `b₁ ≤ b₂`, read as "`b₁`
is at least as defined as `b₂` and permits no more outcomes than `b₂`." -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- A partial behavior guarded by a constructive definedness proposition.
`Partial.ub` (`defined := False`) is the top element `⊤` of the refinement
lattice, while an empty outcome set with `defined := True` is `⊥`. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B :=
  ⟨True, fun _ => b⟩

def Partial.ub {B : Type u} : Partial B :=
  ⟨False, False.elim⟩

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Pointwise partial behavior from queries `Query` to outcome predicates
`Out → Prop`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A language indexed by its external observable spine `SemObs`. -/
structure Language (SemObs : Type) where
  Prog  : Type
  Query : Type
  Out   : Type
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out

/-- A spine-preserving representation codec between two languages sharing
`SemObs`. -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  obs_decodeOut           : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

/-- Identity codec on any language `L`. -/
def BehaviorCodec.id {SemObs : Type} (L : Language SemObs) :
    BehaviorCodec L L where
  encodeQuery := fun q => q
  decodeQuery := fun q => q
  encodeOut   := fun o => o
  decodeOut   := some
  decodeQuery_encodeQuery := fun _ => rfl
  decodeOut_encodeOut     := fun _ => rfl
  obs_decodeOut           := fun _ _ h => by cases h; rfl

/-- Composition of two representation codecs `c₁₂` and `c₂₃`. -/
def BehaviorCodec.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    (c₁₂ : BehaviorCodec L₁ L₂) (c₂₃ : BehaviorCodec L₂ L₃) :
    BehaviorCodec L₁ L₃ where
  encodeQuery := fun q₁ => c₂₃.encodeQuery (c₁₂.encodeQuery q₁)
  decodeQuery := fun q₃ => c₁₂.decodeQuery (c₂₃.decodeQuery q₃)
  encodeOut   := fun o₁ => c₂₃.encodeOut (c₁₂.encodeOut o₁)
  decodeOut   := fun o₃ =>
    match c₂₃.decodeOut o₃ with
    | some o₂ => c₁₂.decodeOut o₂
    | none    => none
  decodeQuery_encodeQuery := fun q₁ => by
    rw [c₂₃.decodeQuery_encodeQuery, c₁₂.decodeQuery_encodeQuery]
  decodeOut_encodeOut := fun o₁ => by
    simp [c₂₃.decodeOut_encodeOut, c₁₂.decodeOut_encodeOut]
  obs_decodeOut := fun o₃ o₁ h => by
    cases h₂₃ : c₂₃.decodeOut o₃ with
    | none =>
      rw [h₂₃] at h
      contradiction
    | some o₂ =>
      rw [h₂₃] at h
      have h_obs₂₃ := c₂₃.obs_decodeOut o₃ o₂ h₂₃
      have h_obs₁₂ := c₁₂.obs_decodeOut o₂ o₁ h
      exact Eq.trans h_obs₂₃ h_obs₁₂

/-- Lift a source behavior across a `BehaviorCodec`. -/
def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b : Behavior L₁.Query L₁.Out) :
    Behavior L₂.Query L₂.Out :=
  fun q₂ => {
    defined := (b (c.decodeQuery q₂)).defined
    val     := fun h o₂ =>
      ∃ o₁, c.decodeOut o₂ = some o₁ ∧ (b (c.decodeQuery q₂)).val h o₁
  }

/-- Downward/horizontal compilation: `t` is at least as defined as `s` and
every outcome of `t` decodes to a valid outcome of `s`. -/
abbrev Compiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ c.toMorphism (L_src.sem s)

/-- Miracle-free compilation: pairs `Compiles` with forward productivity
preservation so `t` cannot satisfy refinement via an empty outcome set `⊥`. -/
def ProductiveCompiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  ∀ q₁,
    (∃ h₁ : (L_src.sem s q₁).defined, ∃ o₁, (L_src.sem s q₁).val h₁ o₁) →
    (∃ h₂ : (L_tgt.sem t (c.encodeQuery q₁)).defined,
      ∃ o₂, (L_tgt.sem t (c.encodeQuery q₁)).val h₂ o₂)

end Trusted

namespace BB8

open Trusted

/-- Reflexivity of `Compiles` under `BehaviorCodec.id`. -/
theorem Compiles.refl {SemObs : Type} {L : Language SemObs} (p : L.Prog) :
    Compiles L L (BehaviorCodec.id L) p p := by
  intro q hdef
  exact ⟨hdef, fun o ho => ⟨o, rfl, ho⟩⟩

/-- Reflexivity of `ProductiveCompiles` under `BehaviorCodec.id`. -/
theorem ProductiveCompiles.refl {SemObs : Type} {L : Language SemObs}
    (p : L.Prog) :
    ProductiveCompiles L L (BehaviorCodec.id L) p p :=
  ⟨Compiles.refl p, fun _ h => h⟩

/-- Transitivity of `Compiles` across two composed codecs. -/
theorem Compiles.trans {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁₂ : BehaviorCodec L₁ L₂} {c₂₃ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ c₁₂ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ c₂₃ p₂ p₃) :
    Compiles L₁ L₃ (c₁₂.comp c₂₃) p₁ p₃ := by
  intro q₃ hdef₁
  have ⟨hdef₂, hval₁₂⟩ := h₁₂ (c₂₃.decodeQuery q₃) hdef₁
  have ⟨hdef₃, hval₂₃⟩ := h₂₃ q₃ hdef₂
  refine ⟨hdef₃, fun o₃ ho₃ => ?_⟩
  have ⟨o₂, hdec₂₃, ho₂⟩ := hval₂₃ o₃ ho₃
  have ⟨o₁, hdec₁₂, ho₁⟩ := hval₁₂ o₂ ho₂
  refine ⟨o₁, ?_, ho₁⟩
  simp [BehaviorCodec.comp, hdec₂₃, hdec₁₂]

/-- Transitivity of `ProductiveCompiles` across two composed codecs. -/
theorem ProductiveCompiles.trans {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁₂ : BehaviorCodec L₁ L₂} {c₂₃ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : ProductiveCompiles L₁ L₂ c₁₂ p₁ p₂)
    (h₂₃ : ProductiveCompiles L₂ L₃ c₂₃ p₂ p₃) :
    ProductiveCompiles L₁ L₃ (c₁₂.comp c₂₃) p₁ p₃ := by
  refine ⟨Compiles.trans h₁₂.1 h₂₃.1, fun q₁ hprod₁ => ?_⟩
  exact h₂₃.2 (c₁₂.encodeQuery q₁) (h₁₂.2 q₁ hprod₁)

/-- Simplification helper when composing two passes on the same language with
`BehaviorCodec.id`. -/
theorem comp_id_codec {SemObs : Type} (L : Language SemObs) :
    (BehaviorCodec.id L).comp (BehaviorCodec.id L) = BehaviorCodec.id L :=
  rfl

/-- Transitivity of `ProductiveCompiles` on a single language under
`BehaviorCodec.id`. -/
theorem ProductiveCompiles.trans_id {SemObs : Type} {L : Language SemObs}
    {p₁ p₂ p₃ : L.Prog}
    (h₁₂ : ProductiveCompiles L L (BehaviorCodec.id L) p₁ p₂)
    (h₂₃ : ProductiveCompiles L L (BehaviorCodec.id L) p₂ p₃) :
    ProductiveCompiles L L (BehaviorCodec.id L) p₁ p₃ :=
  ProductiveCompiles.trans h₁₂ h₂₃

/-- `BB-8` Proof-Gated Compiler Pass (`PassCompiler`).
Wraps a partial transformation `run : L_src.Prog → Option L_tgt.Prog` together
with its soundness theorem showing that whenever `run s = some t`, `t`
productively compiles `s`. -/
structure PassCompiler {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) where
  run        : L_src.Prog → Option L_tgt.Prog
  run_sound  : ∀ {s t}, run s = some t → ProductiveCompiles L_src L_tgt c s t

/-- Construct a `PassCompiler` from a total constructively verified pass
(Mode A). -/
def PassCompiler.ofTotal {SemObs : Type} {L_src L_tgt : Language SemObs}
    (c : BehaviorCodec L_src L_tgt)
    (pass : L_src.Prog → L_tgt.Prog)
    (h_sound : ∀ s, ProductiveCompiles L_src L_tgt c s (pass s)) :
    PassCompiler L_src L_tgt c where
  run s := some (pass s)
  run_sound {s t} h := by
    cases h
    exact h_sound s

/-- `BB-8` Relational Certificate Checker (`CertChecker`) for Mode B passes.
Validates an untrusted target program `t` and witness certificate `cert`
against source program `s` via a kernel-reducible boolean checker `check`. -/
structure CertChecker {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (Cert : Type) where
  check       : L_src.Prog → L_tgt.Prog → Cert → Bool
  check_sound : ∀ {s t cert},
    check s t cert = true → ProductiveCompiles L_src L_tgt c s t

/-- Lift a `CertChecker` and an untrusted oracle `(s ↦ (t, cert))` into a
verified `PassCompiler` that gates emission on `check s t cert = true`. -/
def CertChecker.toPassCompiler {SemObs : Type} {L_src L_tgt : Language SemObs}
    {c : BehaviorCodec L_src L_tgt} {Cert : Type}
    (checker : CertChecker L_src L_tgt c Cert)
    (oracle : L_src.Prog → L_tgt.Prog × Cert) :
    PassCompiler L_src L_tgt c where
  run s :=
    let (t, cert) := oracle s
    if checker.check s t cert then some t else none
  run_sound {s t} h := by
    dsimp only at h
    split at h
    · rename_i hchk
      cases h
      exact checker.check_sound hchk
    · contradiction

/-- Sequential composition of two `PassCompiler` stages on the same language
under `BehaviorCodec.id`. -/
def PassCompiler.compId {SemObs : Type} {L : Language SemObs}
    (P₁ P₂ : PassCompiler L L (BehaviorCodec.id L)) :
    PassCompiler L L (BehaviorCodec.id L) where
  run s :=
    match P₁.run s with
    | some m => P₂.run m
    | none   => none
  run_sound {s t} h := by
    cases h₁ : P₁.run s with
    | none =>
      rw [h₁] at h
      contradiction
    | some m =>
      rw [h₁] at h
      exact ProductiveCompiles.trans_id (P₁.run_sound h₁) (P₂.run_sound h)

end BB8

-- ============================================================================
-- Section 2: AnLLVM IR Syntax, Poison Lattice, MemorySSA, and Loop Semantics
-- ============================================================================

/-- Boolean reflection helper for `Nat.beq`: `Nat.beq a b = false ↔ a ≠ b`. -/
theorem nat_beq_eq_false_iff_ne {a b : Nat} :
    Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · intro h heq
    subst heq
    rw [Nat.beq_refl] at h
    contradiction
  · intro hne
    cases h : Nat.beq a b with
    | false => rfl
    | true => exact False.elim (hne (Nat.beq_eq.mp h))

/-- `AnLLVM` scalar value with explicit deferred-UB `.poison` tracking. -/
inductive PoisonOr (α : Type) where
  | val (v : α)
  | poison
  deriving DecidableEq, Repr

/-- Directional poison refinement `src ⊑ tgt`: a `.poison` value in the source
may be refined by any concrete value in the target, whereas a defined `.val v`
must be preserved exactly. -/
def PoisonOr.IsRefinedBy {α : Type} (src tgt : PoisonOr α) : Prop :=
  match src with
  | .poison => True
  | .val v  => tgt = .val v

theorem PoisonOr.isRefinedBy_refl {α : Type} (x : PoisonOr α) :
    PoisonOr.IsRefinedBy x x := by
  cases x <;> trivial

theorem PoisonOr.isRefinedBy_trans {α : Type} {a b c : PoisonOr α}
    (hab : PoisonOr.IsRefinedBy a b) (hbc : PoisonOr.IsRefinedBy b c) :
    PoisonOr.IsRefinedBy a c := by
  cases a with
  | poison => trivial
  | val v =>
    dsimp [PoisonOr.IsRefinedBy] at hab ⊢
    subst hab
    exact hbc

/-- Virtual / SSA register identifier. -/
abbrev RegId := Nat

/-- Abstract allocation identifier (`alloca` slot or heap object). -/
abbrev AllocId := Nat

/-- `AnLLVM` instruction operand: either a register or an immediate constant. -/
inductive Operand where
  | reg (r : RegId)
  | const (c : Nat)
  deriving DecidableEq, Repr

/-- Binary arithmetic and bitwise operations in `AnLLVM`.
`udiv` traps immediately (`trapped := true`) when the divisor is `0`, whereas
arithmetic/bitwise operations propagate `.poison` without trapping. -/
inductive BinOp where
  | add
  | sub
  | mul
  | bitAnd
  | bitOr
  | bitXor
  | udiv
  deriving DecidableEq, Repr

/-- Whether a `BinOp` is guaranteed never to trigger an immediate trap for any
operand values (`IsSafeToSpeculate` in LLVM's `ValueTracking.h`). -/
def BinOp.isSafeToSpeculate : BinOp → Bool
  | .udiv => false
  | _     => true

/-- Straight-line `AnLLVM` statements in the preheader or epilogue. -/
inductive AnStmt where
  | nop
  | const (dst : RegId) (c : Nat)
  | mov (dst : RegId) (src : RegId)
  | freeze (dst : RegId) (src : RegId)
  | binop (dst : RegId) (op : BinOp) (lhs rhs : Operand)
  | stackStore (alloc : AllocId) (off : Nat) (sz : Nat) (src : Operand)
  | stackLoad (dst : RegId) (alloc : AllocId) (off : Nat) (sz : Nat)
  | escapeStackAddr (dst : RegId) (alloc : AllocId)
  | heapStore (memVer : Nat) (prevVer : Nat) (alloc : AllocId) (off : Nat)
      (src : Operand)
  | heapLoad (memVer : Nat) (dst : RegId) (alloc : AllocId) (off : Nat)
  deriving DecidableEq, Repr

/-- Induction-variable addressing mode inside a canonical rotated loop.
- `mulRecurrence base stride` computes `base + i * stride` via multiplication
  at iteration `i`.
- `scevAddRec start step` maintains an additive recurrence `{start, +, step}`
  updated by `iv ↦ iv + step` on each loop backedge. -/
inductive IndVarMode where
  | mulRecurrence (base : Nat) (stride : Nat)
  | scevAddRec (start : Nat) (step : Nat)
  deriving DecidableEq, Repr

/-- Canonical rotated loop specification in `AnLLVM`.
When `hasInLoopInv = true`, each iteration executes
`binop invDst invOp invLhs invRhs` before updating the loop accumulator
`accDst`. When `LICM` hoists that invariant instruction into `preheader`,
`hasInLoopInv` becomes `false`. -/
structure AnLoop where
  hasInLoopInv : Bool
  invDst       : RegId
  invOp        : BinOp
  invLhs       : Operand
  invRhs       : Operand
  idxMode      : IndVarMode
  accDst       : RegId
  deriving DecidableEq, Repr

/-- Complete `AnLLVM` function body: `preheader` statements, canonical `loop`,
`epilogue` statements, return register `retReg`, and observable heap location
`(obsAlloc, obsOff)`. -/
structure AnLLVMProg where
  preheader : List AnStmt
  loop      : AnLoop
  epilogue  : List AnStmt
  retReg    : RegId
  obsAlloc  : AllocId
  obsOff    : Nat
  deriving DecidableEq, Repr

/-- Input query to an `AnLLVM` function: two scalar arguments (`arg0`, `arg1`,
bound to registers `r0` and `r1`) and loop trip count `tripCount` (bound to
register `r2`). -/
structure AnQuery where
  arg0      : Nat
  arg1      : Nat
  tripCount : Nat
  deriving DecidableEq, Repr

/-- Observable outcome spine `(retVal, obsHeapVal)`. Branching on or returning
`.poison` is Undefined Behavior (`defined := False`). -/
abbrev AnObs := Nat × Nat

/-- Concrete execution state of an `AnLLVM` function. -/
structure AnState where
  regs    : RegId → PoisonOr Nat
  stack   : AllocId → Nat → PoisonOr Nat
  heap    : AllocId → Nat → Nat
  trapped : Bool

/-- Update a single register in `regs`. -/
def updateReg (regs : RegId → PoisonOr Nat) (r : RegId) (v : PoisonOr Nat) :
    RegId → PoisonOr Nat :=
  fun r' => if Nat.beq r' r then v else regs r'

/-- Update a single stack field `(alloc, off)` in `stack`. -/
def updateStack (stack : AllocId → Nat → PoisonOr Nat)
    (alloc : AllocId) (off : Nat) (v : PoisonOr Nat) :
    AllocId → Nat → PoisonOr Nat :=
  fun a o => if Nat.beq a alloc && Nat.beq o off then v else stack a o

/-- Update a single heap cell `(alloc, off)` in `heap`. -/
def updateHeap (heap : AllocId → Nat → Nat)
    (alloc : AllocId) (off : Nat) (v : Nat) :
    AllocId → Nat → Nat :=
  fun a o => if Nat.beq a alloc && Nat.beq o off then v else heap a o

/-- Evaluate an `Operand` in register file `regs`. -/
def evalOperand (regs : RegId → PoisonOr Nat) : Operand → PoisonOr Nat
  | .reg r   => regs r
  | .const c => .val c

/-- Evaluate a non-trapping binary operation on two `PoisonOr Nat` values. -/
def evalPureBinOp (op : BinOp) (v₁ v₂ : PoisonOr Nat) : PoisonOr Nat :=
  match v₁, v₂ with
  | .val a, .val b =>
    match op with
    | .add    => .val (Nat.add a b)
    | .sub    => .val (Nat.sub a b)
    | .mul    => .val (Nat.mul a b)
    | .bitAnd => .val (a &&& b)
    | .bitOr  => .val (a ||| b)
    | .bitXor => .val (a ^^^ b)
    | .udiv   => if Nat.beq b 0 then .poison else .val (Nat.div a b)
  | _, _ => .poison

/-- Check whether a binary operation triggers an immediate runtime trap.
In `AnLLVM`, integer division by zero (`udiv` with `b = 0` or `.poison`) is
immediate Undefined Behavior. -/
def binOpTraps (op : BinOp) (v₁ v₂ : PoisonOr Nat) : Bool :=
  match op with
  | .udiv =>
    match v₁, v₂ with
    | .val _, .val b => Nat.beq b 0
    | _, _           => true
  | _ => false

/-- Core untrapped transition of a single straight-line `AnStmt` on `AnState`. -/
def evalStmtCore (st : AnState) (stmt : AnStmt) : AnState :=
  match stmt with
  | .nop => st
  | .const dst c =>
    { st with regs := updateReg st.regs dst (.val c) }
  | .mov dst src =>
    { st with regs := updateReg st.regs dst (st.regs src) }
  | .freeze dst src =>
    let frozen :=
      match st.regs src with
      | .val v  => PoisonOr.val v
      | .poison => PoisonOr.val 0
    { st with regs := updateReg st.regs dst frozen }
  | .binop dst op lhs rhs =>
    let v₁ := evalOperand st.regs lhs
    let v₂ := evalOperand st.regs rhs
    match binOpTraps op v₁ v₂ with
    | true  => { st with trapped := true }
    | false => { st with regs := updateReg st.regs dst (evalPureBinOp op v₁ v₂) }
  | .stackStore alloc off _ src =>
    let v := evalOperand st.regs src
    { st with stack := updateStack st.stack alloc off v }
  | .stackLoad dst alloc off _ =>
    { st with regs := updateReg st.regs dst (st.stack alloc off) }
  | .escapeStackAddr dst alloc =>
    { st with regs := updateReg st.regs dst (.val alloc) }
  | .heapStore _ _ alloc off src =>
    match evalOperand st.regs src with
    | .val v  => { st with heap := updateHeap st.heap alloc off v }
    | .poison => { st with trapped := true }
  | .heapLoad _ dst alloc off =>
    { st with regs := updateReg st.regs dst (.val (st.heap alloc off)) }

/-- Execute a single straight-line `AnStmt` on `AnState`. -/
def evalStmt (st : AnState) (stmt : AnStmt) : AnState :=
  match st.trapped with
  | true  => st
  | false => evalStmtCore st stmt

theorem evalStmt_trapped {st : AnState} (h : st.trapped = true)
    (stmt : AnStmt) :
    evalStmt st stmt = st := by
  unfold evalStmt
  rw [h]

theorem evalStmt_untrapped {st : AnState} (h : st.trapped = false)
    (stmt : AnStmt) :
    evalStmt st stmt = evalStmtCore st stmt := by
  unfold evalStmt
  rw [h]

/-- Execute a list of straight-line `AnStmt`s sequentially. -/
def evalStmts (st : AnState) : List AnStmt → AnState
  | []          => st
  | stmt :: rest => evalStmts (evalStmt st stmt) rest

theorem evalStmts_append (st : AnState) (l₁ l₂ : List AnStmt) :
    evalStmts st (l₁ ++ l₂) = evalStmts (evalStmts st l₁) l₂ := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons hd tl ih => exact ih (evalStmt st hd)

/-- Execute one iteration of the loop body given the current index `idxVal`. -/
def stepLoopIter (L : AnLoop) (st : AnState) (idxVal : Nat) : AnState :=
  let st₁ :=
    match L.hasInLoopInv with
    | true  => evalStmt st (.binop L.invDst L.invOp L.invLhs L.invRhs)
    | false => st
  match st₁.trapped with
  | true  => st₁
  | false =>
    let accOld := st₁.regs L.accDst
    let invVal := st₁.regs L.invDst
    let stepSum := evalPureBinOp .add (.val idxVal) invVal
    let accNew := evalPureBinOp .add accOld stepSum
    { st₁ with regs := updateReg st₁.regs L.accDst accNew }

/-- Execute `rem` remaining iterations under `IndVarMode.mulRecurrence base stride`
starting at iteration counter `curIter`. -/
def runLoopMul (L : AnLoop) (base stride : Nat) :
    Nat → Nat → AnState → AnState
  | 0, _, st => st
  | rem + 1, curIter, st =>
    let idxVal := base + curIter * stride
    let st' := stepLoopIter L st idxVal
    runLoopMul L base stride rem (curIter + 1) st'

/-- Execute `rem` remaining iterations under `IndVarMode.scevAddRec` with
current additive induction variable `curIv` and step `step`. -/
def runLoopAddRec (L : AnLoop) (step : Nat) :
    Nat → Nat → AnState → AnState
  | 0, _, st => st
  | rem + 1, curIv, st =>
    let st' := stepLoopIter L st curIv
    runLoopAddRec L step rem (curIv + step) st'

/-- Execute a canonical `AnLoop` for `tripCount` iterations. -/
def evalLoop (L : AnLoop) (tripCount : Nat) (st : AnState) : AnState :=
  match L.idxMode with
  | .mulRecurrence base stride => runLoopMul L base stride tripCount 0 st
  | .scevAddRec start step     => runLoopAddRec L step tripCount start st

/-- Initial state for an `AnLLVM` function on input query `q`.
Registers `0`, `1`, `2` hold `arg0`, `arg1`, `tripCount`; `r3` (the default
loop accumulator) is initialized to `.val 0`; all other registers and stack
slots start as `.poison`. -/
def initAnState (q : AnQuery) : AnState where
  regs r :=
    if Nat.beq r 0 then .val q.arg0
    else if Nat.beq r 1 then .val q.arg1
    else if Nat.beq r 2 then .val q.tripCount
    else if Nat.beq r 3 then .val 0
    else .poison
  stack _ _ := .poison
  heap _ _  := 0
  trapped   := false

/-- Full evaluation of an `AnLLVMProg` on input query `q`. -/
def evalProg (p : AnLLVMProg) (q : AnQuery) : AnState :=
  let st₀ := initAnState q
  let st₁ := evalStmts st₀ p.preheader
  let st₂ := evalLoop p.loop q.tripCount st₁
  evalStmts st₂ p.epilogue

/-- Extract the observable `(retVal, heapVal)` pair if execution did not trap
and `retReg` holds a defined `.val retVal` (`noundef` return ABI). -/
def extractObs (p : AnLLVMProg) (st : AnState) : Option AnObs :=
  if st.trapped then none
  else
    match st.regs p.retReg with
    | .val rv => some (rv, st.heap p.obsAlloc p.obsOff)
    | .poison => none

/-- Instantiation of `Trusted.Language AnObs` for `AnLLVM`. -/
def AnLLVMLang : Trusted.Language AnObs where
  Prog  := AnLLVMProg
  Query := AnQuery
  Out   := AnObs
  obs   := fun o => o
  sem   := fun p q =>
    match extractObs p (evalProg p q) with
    | some out => ⟨True, fun _ o => o = out⟩
    | none     => Trusted.Partial.ub

/-- Helper lemma: if `extractObs s (evalProg s q) = some out` implies
`extractObs t (evalProg t q) = some out` for all queries `q`, then `t`
productively compiles `s`. -/
theorem productiveCompiles_of_extractObs_eq {s t : AnLLVMProg}
    (h : ∀ q out,
      extractObs s (evalProg s q) = some out →
      extractObs t (evalProg t q) = some out) :
    Trusted.ProductiveCompiles
      AnLLVMLang AnLLVMLang (Trusted.BehaviorCodec.id AnLLVMLang) s t := by
  constructor
  · intro q
    dsimp [AnLLVMLang, Trusted.BehaviorCodec.toMorphism,
      Trusted.BehaviorCodec.id]
    cases hs : extractObs s (evalProg s q) with
    | none =>
      intro hdef_s
      exact False.elim hdef_s
    | some out =>
      intro _
      have ht := h q out hs
      rw [ht]
      exact ⟨True.intro, fun o ho => ⟨o, rfl, ho⟩⟩
  · intro q
    dsimp [AnLLVMLang, Trusted.BehaviorCodec.id]
    cases hs : extractObs s (evalProg s q) with
    | none =>
      intro ⟨hdef_s, _, _⟩
      exact False.elim hdef_s
    | some out =>
      intro _
      have ht := h q out hs
      rw [ht]
      exact ⟨True.intro, out, rfl⟩

/-- Corollary: if `evalProg t q = evalProg s q` and `t.retReg = s.retReg`,
`t.obsAlloc = s.obsAlloc`, `t.obsOff = s.obsOff`, then `t` productively
compiles `s`. -/
theorem productiveCompiles_of_evalProg_eq {s t : AnLLVMProg}
    (heval : ∀ q, evalProg t q = evalProg s q)
    (hret : t.retReg = s.retReg)
    (halloc : t.obsAlloc = s.obsAlloc)
    (hoff : t.obsOff = s.obsOff) :
    Trusted.ProductiveCompiles
      AnLLVMLang AnLLVMLang (Trusted.BehaviorCodec.id AnLLVMLang) s t := by
  apply productiveCompiles_of_extractObs_eq
  intro q out hs
  unfold extractObs at hs ⊢
  rw [heval q, hret, halloc, hoff]
  exact hs

-- ============================================================================
-- Section 3: Pass 1 — SROA + PromoteMemToReg Certificate Validator (Mode B)
-- ============================================================================

/-!
### Pass 1 Design (`SROA.h` + `PromoteMemToReg.h`)

Upstream LLVM's `SROAPass` (`llvm/Transforms/Scalar/SROA.h`) builds an
`AllocaSlices` interval partition over byte offsets `[begin, end)` of each
non-escaping `alloca`, rewrites field `getelementptr` + `load`/`store` into
independent slice `alloca`s, and invokes `PromoteMemToReg`
(`llvm/Transforms/Utils/PromoteMemToReg.h`) to promote each slice into SSA
registers.

In Anneal, we validate `SROA + PromoteMemToReg` via a 2-part certificate
`SroaMem2RegCert`:
1. **Spatial Disjointness & Non-Escape (`SroaSliceSpec`):** Every promoted slice
   `sᵢ = (alloc, offᵢ, szᵢ, dstRegᵢ)` has `szᵢ > 0`, pairwise non-overlapping
   byte ranges (`off₁ + sz₁ ≤ off₂ ∨ off₂ + sz₂ ≤ off₁` whenever
   `alloc₁ = alloc₂`), distinct target SSA registers `dstRegᵢ`, and no
   `escapeStackAddr _ alloc` instruction in the program.
2. **SSA Store-to-Register Promotion (`rewriteStmtSroa`):** Each `stackStore`
   to a promoted slice `(alloc, off, sz)` is rewritten to assign its scalar
   register `dstReg`, and each `stackLoad` from `(alloc, off, sz)` is rewritten
   into `mov dst dstReg`.
-/

/-- Specification of a single aggregate field slice promoted by `SROA`. -/
structure SroaSliceSpec where
  alloc  : AllocId
  off    : Nat
  sz     : Nat
  ssaReg : RegId
  deriving DecidableEq, Repr

/-- Boolean checker verifying that two `SroaSliceSpec` entries do not overlap
in stack memory and do not collide on their promoted SSA register. -/
def checkTwoSlicesDisjoint (s₁ s₂ : SroaSliceSpec) : Bool :=
  (!Nat.beq s₁.ssaReg s₂.ssaReg) &&
  (if Nat.beq s₁.alloc s₂.alloc then
     Nat.ble (s₁.off + s₁.sz) s₂.off ||
     Nat.ble (s₂.off + s₂.sz) s₁.off
   else
     true)

/-- Check that `s` is disjoint from every slice in `rest`. -/
def checkSliceAgainstList (s : SroaSliceSpec) : List SroaSliceSpec → Bool
  | []        => true
  | s₂ :: tl => checkTwoSlicesDisjoint s s₂ && checkSliceAgainstList s tl

/-- Check pairwise disjointness and positive byte size across all slices. -/
def checkSlicesValid : List SroaSliceSpec → Bool
  | []       => true
  | s :: tl =>
    Nat.blt 0 s.sz &&
    checkSliceAgainstList s tl &&
    checkSlicesValid tl

/-- Soundness of `checkTwoSlicesDisjoint` via GMP `Nat` boolean reflection:
if `checkTwoSlicesDisjoint s₁ s₂ = true` and `s₁.alloc = s₂.alloc`, then their
byte intervals `[s₁.off, s₁.off + s₁.sz)` and `[s₂.off, s₂.off + s₂.sz)` are
strictly disjoint (so `s₁.off ≠ s₂.off` whenever `s₁.sz > 0` and `s₂.sz > 0`). -/
theorem checkTwoSlicesDisjoint_offsets_ne {s₁ s₂ : SroaSliceSpec}
    (hvalid₁ : Nat.blt 0 s₁.sz = true)
    (hvalid₂ : Nat.blt 0 s₂.sz = true)
    (hdisj : checkTwoSlicesDisjoint s₁ s₂ = true)
    (halloc : s₁.alloc = s₂.alloc) :
    s₁.off ≠ s₂.off ∧ s₁.ssaReg ≠ s₂.ssaReg := by
  unfold checkTwoSlicesDisjoint at hdisj
  rw [Bool.and_eq_true] at hdisj
  have hreg : s₁.ssaReg ≠ s₂.ssaReg := by
    intro heq
    have hbeq : Nat.beq s₁.ssaReg s₂.ssaReg = true := Nat.beq_eq.mpr heq
    simp [hbeq] at hdisj
  have halloc_beq : Nat.beq s₁.alloc s₂.alloc = true := Nat.beq_eq.mpr halloc
  have hbounds := hdisj.2
  simp only [halloc_beq, ↓reduceIte, Bool.or_eq_true] at hbounds
  have hsz₁ : 0 < s₁.sz := Nat.blt_eq.mp hvalid₁
  have hsz₂ : 0 < s₂.sz := Nat.blt_eq.mp hvalid₂
  refine ⟨?_, hreg⟩
  intro hoff
  cases hbounds with
  | inl hle₁ =>
    have hle := Nat.ble_eq.mp hle₁
    omega
  | inr hle₂ =>
    have hle := Nat.ble_eq.mp hle₂
    omega

/-- Look up the promoted SSA register for `(alloc, off, sz)` in a slice map. -/
def lookupSliceReg (alloc : AllocId) (off sz : Nat) :
    List SroaSliceSpec → Option RegId
  | [] => none
  | s :: tl =>
    if Nat.beq s.alloc alloc && Nat.beq s.off off && Nat.beq s.sz sz then
      some s.ssaReg
    else
      lookupSliceReg alloc off sz tl

/-- Check that no statement in `stmts` takes the address of a promoted
`alloc` (`escapeStackAddr`). -/
def checkNoEscapedAllocs (slices : List SroaSliceSpec) : List AnStmt → Bool
  | [] => true
  | stmt :: tl =>
    let ok :=
      match stmt with
      | .escapeStackAddr _ alloc =>
        !(slices.any (fun s => Nat.beq s.alloc alloc))
      | _ => true
    ok && checkNoEscapedAllocs slices tl

/-- Rewrite a single `AnStmt` according to the validated `SROA + Mem2Reg`
slice table. -/
def rewriteStmtSroa (slices : List SroaSliceSpec) (stmt : AnStmt) : AnStmt :=
  match stmt with
  | .stackStore alloc off sz (.const c) =>
    match lookupSliceReg alloc off sz slices with
    | some ssaReg => .const ssaReg c
    | none        => stmt
  | .stackStore alloc off sz (.reg src) =>
    match lookupSliceReg alloc off sz slices with
    | some ssaReg => .mov ssaReg src
    | none        => stmt
  | .stackLoad dst alloc off sz =>
    match lookupSliceReg alloc off sz slices with
    | some ssaReg => .mov dst ssaReg
    | none        => stmt
  | _ => stmt

/-- Certificate for Pass 1 (`SROA + PromoteMemToReg`).
Contains the promoted slice partition `slices`. -/
structure SroaMem2RegCert where
  slices : List SroaSliceSpec
  deriving DecidableEq, Repr

/-- Check that an `Operand` does not reference any promoted slice register. -/
def checkOperandNonSlice (slices : List SroaSliceSpec) : Operand → Bool
  | .reg r   => slices.all (fun sl => !Nat.beq sl.ssaReg r)
  | .const _ => true

/-- Check that every promoted `ssaReg` in `slices` is fresh (`ssaReg > 3`, so
`initAnState` initializes both `regs ssaReg` and `stack alloc off` to
`.poison`). -/
def checkSlicesFreshRegs (slices : List SroaSliceSpec) : Bool :=
  slices.all (fun sl => Nat.blt 3 sl.ssaReg)

/-- Check that a single `AnStmt` respects the `SROA + Mem2Reg` promotion
discipline: every `stackStore`/`stackLoad` accesses a valid slice in `slices`,
no `escapeStackAddr` occurs, and non-stack instructions do not read or clobber
promoted slice registers. -/
def checkStmtSroa (slices : List SroaSliceSpec) (stmt : AnStmt) : Bool :=
  match stmt with
  | .nop => true
  | .const dst _ =>
    slices.all (fun sl => !Nat.beq sl.ssaReg dst)
  | .mov dst src =>
    slices.all (fun sl => !Nat.beq sl.ssaReg dst) &&
    slices.all (fun sl => !Nat.beq sl.ssaReg src)
  | .freeze dst src =>
    slices.all (fun sl => !Nat.beq sl.ssaReg dst) &&
    slices.all (fun sl => !Nat.beq sl.ssaReg src)
  | .binop dst _ lhs rhs =>
    slices.all (fun sl => !Nat.beq sl.ssaReg dst) &&
    checkOperandNonSlice slices lhs &&
    checkOperandNonSlice slices rhs
  | .stackStore alloc off sz (.const _) =>
    (lookupSliceReg alloc off sz slices).isSome
  | .stackStore alloc off sz (.reg src) =>
    (lookupSliceReg alloc off sz slices).isSome &&
    slices.all (fun sl => !Nat.beq sl.ssaReg src)
  | .stackLoad dst alloc off sz =>
    (lookupSliceReg alloc off sz slices).isSome &&
    slices.all (fun sl => !Nat.beq sl.ssaReg dst)
  | .escapeStackAddr _ _ => false
  | .heapStore _ _ _ _ src =>
    checkOperandNonSlice slices src
  | .heapLoad _ dst _ _ =>
    slices.all (fun sl => !Nat.beq sl.ssaReg dst)

/-- Check a list of statements for `SROA + Mem2Reg` validity. -/
def checkStmtsSroa (slices : List SroaSliceSpec) : List AnStmt → Bool
  | []          => true
  | stmt :: tl => checkStmtSroa slices stmt && checkStmtsSroa slices tl

/-- Check that loop registers do not collide with promoted slice registers. -/
def checkLoopNonSlice (slices : List SroaSliceSpec) (L : AnLoop) : Bool :=
  slices.all (fun sl => !Nat.beq sl.ssaReg L.invDst) &&
  slices.all (fun sl => !Nat.beq sl.ssaReg L.accDst) &&
  checkOperandNonSlice slices L.invLhs &&
  checkOperandNonSlice slices L.invRhs

/-- Complete `BB-8` boolean validator for Pass 1 (`SROA + PromoteMemToReg`). -/
def checkSroaMem2Reg (s t : AnLLVMProg) (cert : SroaMem2RegCert) : Bool :=
  checkSlicesValid cert.slices &&
  checkSlicesFreshRegs cert.slices &&
  checkNoEscapedAllocs cert.slices s.preheader &&
  checkStmtsSroa cert.slices s.preheader &&
  checkLoopNonSlice cert.slices s.loop &&
  checkStmtsSroa cert.slices s.epilogue &&
  cert.slices.all (fun sl => !Nat.beq sl.ssaReg s.retReg) &&
  decide (t.preheader = s.preheader.map (rewriteStmtSroa cert.slices)) &&
  decide (t.loop = s.loop) &&
  decide (t.epilogue = s.epilogue.map (rewriteStmtSroa cert.slices)) &&
  decide (t.retReg = s.retReg) &&
  decide (t.obsAlloc = s.obsAlloc) &&
  decide (t.obsOff = s.obsOff)

/-- State simulation relation between unpromoted state `stS` and scalar-promoted
state `stT` relative to `slices`:
1. `stT.trapped = stS.trapped` and `stT.heap = stS.heap`;
2. Every non-slice register `r` (`∀ sl ∈ slices, sl.ssaReg ≠ r`) has
   `stT.regs r = stS.regs r`;
3. Every slice `sl ∈ slices` satisfies
   `stT.regs sl.ssaReg = stS.stack sl.alloc sl.off`. -/
structure SroaStateRel (slices : List SroaSliceSpec)
    (stS stT : AnState) : Prop where
  trapped_eq : stT.trapped = stS.trapped
  heap_eq    : stT.heap = stS.heap
  non_slice_regs_eq :
    ∀ r, (∀ sl ∈ slices, sl.ssaReg ≠ r) → stT.regs r = stS.regs r
  slice_sync :
    ∀ sl ∈ slices, stT.regs sl.ssaReg = stS.stack sl.alloc sl.off

theorem updateReg_same (regs : RegId → PoisonOr Nat) (r : RegId)
    (v : PoisonOr Nat) :
    updateReg regs r v r = v := by
  simp [updateReg]

theorem updateReg_other (regs : RegId → PoisonOr Nat) {r r' : RegId}
    (v : PoisonOr Nat) (hne : r' ≠ r) :
    updateReg regs r v r' = regs r' := by
  have hbeq : Nat.beq r' r = false := nat_beq_eq_false_iff_ne.mpr hne
  simp [updateReg, hbeq]

theorem updateStack_same (stack : AllocId → Nat → PoisonOr Nat)
    (alloc : AllocId) (off : Nat) (v : PoisonOr Nat) :
    updateStack stack alloc off v alloc off = v := by
  simp [updateStack]

theorem updateStack_other (stack : AllocId → Nat → PoisonOr Nat)
    {alloc a : AllocId} {off o : Nat} (v : PoisonOr Nat)
    (hne : ¬(a = alloc ∧ o = off)) :
    updateStack stack alloc off v a o = stack a o := by
  unfold updateStack
  cases ha : Nat.beq a alloc with
  | false => rfl
  | true =>
    cases ho : Nat.beq o off with
    | false => rfl
    | true =>
      exfalso
      exact hne ⟨Nat.beq_eq.mp ha, Nat.beq_eq.mp ho⟩

theorem all_ssaReg_ne {slices : List SroaSliceSpec} {r : RegId}
    (h : slices.all (fun sl => !Nat.beq sl.ssaReg r) = true) :
    ∀ sl ∈ slices, sl.ssaReg ≠ r := by
  intro sl hsl heq
  rw [List.all_eq_true] at h
  have h_sl := h sl hsl
  have hbeq : Nat.beq sl.ssaReg r = true := Nat.beq_eq.mpr heq
  simp [hbeq] at h_sl

theorem evalOperand_eq_of_sroaRel {slices : List SroaSliceSpec}
    {stS stT : AnState} (hrel : SroaStateRel slices stS stT)
    {op : Operand} (hop : checkOperandNonSlice slices op = true) :
    evalOperand stT.regs op = evalOperand stS.regs op := by
  cases op with
  | const c => rfl
  | reg r =>
    exact hrel.non_slice_regs_eq r (all_ssaReg_ne hop)

/-- Updating any non-slice register `dst` with the same value `v` in both `stS`
and `stT` preserves `SroaStateRel`. -/
theorem sroaStateRel_update_nonSlice_reg {slices : List SroaSliceSpec}
    {stS stT : AnState} (hrel : SroaStateRel slices stS stT)
    {dst : RegId} (hdst : ∀ sl ∈ slices, sl.ssaReg ≠ dst)
    (v : PoisonOr Nat) :
    SroaStateRel slices
      { stS with regs := updateReg stS.regs dst v }
      { stT with regs := updateReg stT.regs dst v } where
  trapped_eq := hrel.trapped_eq
  heap_eq    := hrel.heap_eq
  non_slice_regs_eq r hr := by
    dsimp only
    by_cases heq : r = dst
    · subst heq
      rw [updateReg_same, updateReg_same]
    · rw [updateReg_other _ _ heq, updateReg_other _ _ heq]
      exact hrel.non_slice_regs_eq r hr
  slice_sync sl hsl := by
    dsimp only
    have hne : sl.ssaReg ≠ dst := hdst sl hsl
    rw [updateReg_other _ _ hne]
    exact hrel.slice_sync sl hsl

/-- Soundness of `lookupSliceReg`: if `lookupSliceReg alloc off sz slices = some r`,
then `{alloc, off, sz, r}` is a member of `slices`. -/
theorem lookupSliceReg_mem {alloc : AllocId} {off sz : Nat} {r : RegId}
    {slices : List SroaSliceSpec}
    (h : lookupSliceReg alloc off sz slices = some r) :
    { alloc := alloc, off := off, sz := sz, ssaReg := r } ∈ slices := by
  induction slices with
  | nil => contradiction
  | cons hd tl ih =>
    unfold lookupSliceReg at h
    split at h
    · rename_i hcond
      cases h
      simp only [Bool.and_eq_true, Nat.beq_eq] at hcond
      rcases hd with ⟨a', o', sz', r'⟩
      dsimp at hcond
      rcases hcond with ⟨⟨ha, ho⟩, hsz⟩
      subst ha ho hsz
      exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)

theorem checkSliceAgainstList_prop {s₁ s₂ : SroaSliceSpec}
    {tl : List SroaSliceSpec}
    (hvalid₁ : Nat.blt 0 s₁.sz = true)
    (hvalid₂ : Nat.blt 0 s₂.sz = true)
    (hlist : checkSliceAgainstList s₁ tl = true)
    (hmem : s₂ ∈ tl) :
    s₁.ssaReg ≠ s₂.ssaReg ∧ ¬(s₁.alloc = s₂.alloc ∧ s₁.off = s₂.off) := by
  induction tl with
  | nil => contradiction
  | cons hd rest ih =>
    unfold checkSliceAgainstList at hlist
    rw [Bool.and_eq_true] at hlist
    cases hmem with
    | head _ =>
      unfold checkTwoSlicesDisjoint at hlist
      have h₁ := hlist.1
      rw [Bool.and_eq_true] at h₁
      have hreg : s₁.ssaReg ≠ s₂.ssaReg := by
        intro heq
        have hbeq := Nat.beq_eq.mpr heq
        simp [hbeq] at h₁
      refine ⟨hreg, ?_⟩
      intro ⟨halloc, hoff⟩
      have ⟨hne_off, _⟩ :=
        checkTwoSlicesDisjoint_offsets_ne hvalid₁ hvalid₂ hlist.1 halloc
      exact hne_off hoff
    | tail _ hmem' =>
      exact ih hlist.2 hmem'

theorem checkSlicesValid_mem_pos {s : SroaSliceSpec}
    {slices : List SroaSliceSpec}
    (hvalid : checkSlicesValid slices = true) (hmem : s ∈ slices) :
    Nat.blt 0 s.sz = true := by
  induction slices with
  | nil => contradiction
  | cons hd tl ih =>
    unfold checkSlicesValid at hvalid
    simp only [Bool.and_eq_true] at hvalid
    cases hmem with
    | head _ => exact hvalid.1.1
    | tail _ hm => exact ih hvalid.2 hm

theorem checkSlicesValid_disjoint {s₁ s₂ : SroaSliceSpec}
    {slices : List SroaSliceSpec}
    (hvalid : checkSlicesValid slices = true)
    (hm₁ : s₁ ∈ slices) (hm₂ : s₂ ∈ slices) :
    (s₁.ssaReg = s₂.ssaReg → s₁ = s₂) ∧
    (s₁.alloc = s₂.alloc ∧ s₁.off = s₂.off → s₁ = s₂) := by
  induction slices with
  | nil => contradiction
  | cons hd tl ih =>
    unfold checkSlicesValid at hvalid
    simp only [Bool.and_eq_true] at hvalid
    have hpos₁ :=
      checkSlicesValid_mem_pos (by unfold checkSlicesValid; simp [hvalid]) hm₁
    have hpos₂ :=
      checkSlicesValid_mem_pos (by unfold checkSlicesValid; simp [hvalid]) hm₂
    cases hm₁ with
    | head _ =>
      cases hm₂ with
      | head _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | tail _ hm₂' =>
        have ⟨hreg_ne, hoff_ne⟩ :=
          checkSliceAgainstList_prop hpos₁ hpos₂ hvalid.1.2 hm₂'
        exact ⟨fun h => False.elim (hreg_ne h),
               fun h => False.elim (hoff_ne h)⟩
    | tail _ hm₁' =>
      cases hm₂ with
      | head _ =>
        have ⟨hreg_ne, hoff_ne⟩ :=
          checkSliceAgainstList_prop hpos₂ hpos₁ hvalid.1.2 hm₁'
        exact ⟨fun h => False.elim (hreg_ne h.symm),
               fun h => False.elim (hoff_ne ⟨h.1.symm, h.2.symm⟩)⟩
      | tail _ hm₂' =>
        exact ih hvalid.2 hm₁' hm₂'

/-- Updating a promoted stack slice `(sl.alloc, sl.off)` in `stS` and its
corresponding register `sl.ssaReg` in `stT` preserves `SroaStateRel` thanks to
pairwise slice disjointness (`checkSlicesValid`). -/
theorem sroaStateRel_update_slice {slices : List SroaSliceSpec}
    (hvalid : checkSlicesValid slices = true)
    {stS stT : AnState} (hrel : SroaStateRel slices stS stT)
    {sl : SroaSliceSpec} (hsl : sl ∈ slices)
    (v : PoisonOr Nat) :
    SroaStateRel slices
      { stS with stack := updateStack stS.stack sl.alloc sl.off v }
      { stT with regs := updateReg stT.regs sl.ssaReg v } where
  trapped_eq := hrel.trapped_eq
  heap_eq    := hrel.heap_eq
  non_slice_regs_eq r hr := by
    dsimp only
    have hne : r ≠ sl.ssaReg := Ne.symm (hr sl hsl)
    rw [updateReg_other _ _ hne]
    exact hrel.non_slice_regs_eq r hr
  slice_sync sl' hsl' := by
    dsimp only
    have ⟨hreg_inj, hoff_inj⟩ := checkSlicesValid_disjoint hvalid hsl' hsl
    by_cases h_eq : sl' = sl
    · subst h_eq
      rw [updateReg_same, updateStack_same]
    · have hreg_ne : sl'.ssaReg ≠ sl.ssaReg := fun hr => h_eq (hreg_inj hr)
      have hoff_ne : ¬(sl'.alloc = sl.alloc ∧ sl'.off = sl.off) :=
        fun ho => h_eq (hoff_inj ho)
      rw [updateReg_other _ _ hreg_ne, updateStack_other _ _ hoff_ne]
      exact hrel.slice_sync sl' hsl'

/-- Single-statement simulation theorem for `rewriteStmtSroa`. -/
theorem evalStmt_rewriteStmtSroa_sim {slices : List SroaSliceSpec}
    (hvalid : checkSlicesValid slices = true)
    {stS stT : AnState} (hrel : SroaStateRel slices stS stT)
    (stmt : AnStmt) (hchk : checkStmtSroa slices stmt = true) :
    SroaStateRel slices
      (evalStmt stS stmt)
      (evalStmt stT (rewriteStmtSroa slices stmt)) := by
  by_cases htrap : stS.trapped = true
  · have htrapT : stT.trapped = true := Eq.trans hrel.trapped_eq htrap
    rw [evalStmt_trapped htrap, evalStmt_trapped htrapT]
    exact hrel
  · have htrapF : stS.trapped = false := Bool.eq_false_iff.mpr htrap
    have htrapTF : stT.trapped = false := Eq.trans hrel.trapped_eq htrapF
    rw [evalStmt_untrapped htrapF, evalStmt_untrapped htrapTF]
    cases stmt with
    | nop =>
      exact hrel
    | const dst c =>
      unfold checkStmtSroa at hchk
      dsimp only [rewriteStmtSroa, evalStmtCore]
      exact sroaStateRel_update_nonSlice_reg hrel (all_ssaReg_ne hchk) (.val c)
    | mov dst src =>
      unfold checkStmtSroa at hchk
      rw [Bool.and_eq_true] at hchk
      dsimp only [rewriteStmtSroa, evalStmtCore]
      rw [hrel.non_slice_regs_eq src (all_ssaReg_ne hchk.2)]
      exact sroaStateRel_update_nonSlice_reg hrel
        (all_ssaReg_ne hchk.1) (stS.regs src)
    | freeze dst src =>
      unfold checkStmtSroa at hchk
      rw [Bool.and_eq_true] at hchk
      dsimp only [rewriteStmtSroa, evalStmtCore]
      rw [hrel.non_slice_regs_eq src (all_ssaReg_ne hchk.2)]
      exact sroaStateRel_update_nonSlice_reg hrel (all_ssaReg_ne hchk.1) _
    | binop dst op lhs rhs =>
      unfold checkStmtSroa at hchk
      simp only [Bool.and_eq_true] at hchk
      dsimp only [rewriteStmtSroa, evalStmtCore]
      rw [evalOperand_eq_of_sroaRel hrel hchk.1.2,
          evalOperand_eq_of_sroaRel hrel hchk.2]
      split
      · exact ⟨rfl, hrel.heap_eq, hrel.non_slice_regs_eq, hrel.slice_sync⟩
      · exact sroaStateRel_update_nonSlice_reg hrel (all_ssaReg_ne hchk.1.1) _
    | stackStore alloc off sz src =>
      cases src with
      | const c =>
        unfold checkStmtSroa at hchk
        dsimp only at hchk
        dsimp only [rewriteStmtSroa]
        cases hlk : lookupSliceReg alloc off sz slices with
        | none =>
          rw [hlk] at hchk
          contradiction
        | some ssaReg =>
          dsimp only [evalStmtCore, evalOperand]
          exact sroaStateRel_update_slice hvalid hrel
            (lookupSliceReg_mem hlk) (.val c)
      | reg srcReg =>
        unfold checkStmtSroa at hchk
        dsimp only at hchk
        rw [Bool.and_eq_true] at hchk
        dsimp only [rewriteStmtSroa]
        cases hlk : lookupSliceReg alloc off sz slices with
        | none =>
          have hnone := hchk.1
          rw [hlk] at hnone
          contradiction
        | some ssaReg =>
          dsimp only [evalStmtCore, evalOperand]
          rw [hrel.non_slice_regs_eq srcReg (all_ssaReg_ne hchk.2)]
          exact sroaStateRel_update_slice hvalid hrel
            (lookupSliceReg_mem hlk) (stS.regs srcReg)
    | stackLoad dst alloc off sz =>
      unfold checkStmtSroa at hchk
      dsimp only at hchk
      rw [Bool.and_eq_true] at hchk
      dsimp only [rewriteStmtSroa]
      cases hlk : lookupSliceReg alloc off sz slices with
      | none =>
        have hnone := hchk.1
        rw [hlk] at hnone
        contradiction
      | some ssaReg =>
        dsimp only [evalStmtCore]
        have hmem := lookupSliceReg_mem hlk
        have hsync := hrel.slice_sync _ hmem
        dsimp only at hsync
        rw [hsync]
        exact sroaStateRel_update_nonSlice_reg hrel
          (all_ssaReg_ne hchk.2) (stS.stack alloc off)
    | escapeStackAddr _ _ =>
      unfold checkStmtSroa at hchk
      contradiction
    | heapStore _ _ alloc off src =>
      unfold checkStmtSroa at hchk
      dsimp only [rewriteStmtSroa, evalStmtCore]
      rw [evalOperand_eq_of_sroaRel hrel hchk]
      cases evalOperand stS.regs src with
      | val v =>
        exact ⟨hrel.trapped_eq, by dsimp only; rw [hrel.heap_eq],
               hrel.non_slice_regs_eq, hrel.slice_sync⟩
      | poison =>
        exact ⟨rfl, hrel.heap_eq, hrel.non_slice_regs_eq, hrel.slice_sync⟩
    | heapLoad _ dst alloc off =>
      unfold checkStmtSroa at hchk
      dsimp only [rewriteStmtSroa, evalStmtCore]
      have hval : stT.heap alloc off = stS.heap alloc off := by
        rw [hrel.heap_eq]
      rw [hval]
      exact sroaStateRel_update_nonSlice_reg hrel
        (all_ssaReg_ne hchk) (.val (stS.heap alloc off))

/-- Statement-list simulation theorem for `rewriteStmtSroa`. -/
theorem evalStmts_rewriteStmtSroa_sim {slices : List SroaSliceSpec}
    (hvalid : checkSlicesValid slices = true)
    {stS stT : AnState} (hrel : SroaStateRel slices stS stT)
    (stmts : List AnStmt) (hchk : checkStmtsSroa slices stmts = true) :
    SroaStateRel slices
      (evalStmts stS stmts)
      (evalStmts stT (stmts.map (rewriteStmtSroa slices))) := by
  induction stmts generalizing stS stT with
  | nil => exact hrel
  | cons hd tl ih =>
    unfold checkStmtsSroa at hchk
    rw [Bool.and_eq_true] at hchk
    exact ih (evalStmt_rewriteStmtSroa_sim hvalid hrel hd hchk.1) hchk.2

/-- Loop-iteration simulation under `SroaStateRel`. -/
theorem stepLoopIter_sroa_sim {slices : List SroaSliceSpec}
    (hvalid : checkSlicesValid slices = true)
    {L : AnLoop} (hloop : checkLoopNonSlice slices L = true)
    {stS stT : AnState} (hrel : SroaStateRel slices stS stT)
    (idxVal : Nat) :
    SroaStateRel slices (stepLoopIter L stS idxVal) (stepLoopIter L stT idxVal) := by
  unfold checkLoopNonSlice at hloop
  simp only [Bool.and_eq_true] at hloop
  let stS₁ :=
    match L.hasInLoopInv with
    | true  => evalStmt stS (.binop L.invDst L.invOp L.invLhs L.invRhs)
    | false => stS
  let stT₁ :=
    match L.hasInLoopInv with
    | true  => evalStmt stT (.binop L.invDst L.invOp L.invLhs L.invRhs)
    | false => stT
  have hrel₁ : SroaStateRel slices stS₁ stT₁ := by
    dsimp only [stS₁, stT₁]
    cases L.hasInLoopInv with
    | false => exact hrel
    | true =>
      have hstmt :
          checkStmtSroa slices (.binop L.invDst L.invOp L.invLhs L.invRhs) = true := by
        unfold checkStmtSroa
        simp [hloop.1.1.1, hloop.1.2, hloop.2]
      exact evalStmt_rewriteStmtSroa_sim hvalid hrel
        (.binop L.invDst L.invOp L.invLhs L.invRhs) hstmt
  change
    SroaStateRel slices
      (match stS₁.trapped with
       | true  => stS₁
       | false =>
         { stS₁ with
           regs :=
             updateReg stS₁.regs L.accDst
               (evalPureBinOp .add (stS₁.regs L.accDst)
                 (evalPureBinOp .add (.val idxVal) (stS₁.regs L.invDst))) })
      (match stT₁.trapped with
       | true  => stT₁
       | false =>
         { stT₁ with
           regs :=
             updateReg stT₁.regs L.accDst
               (evalPureBinOp .add (stT₁.regs L.accDst)
                 (evalPureBinOp .add (.val idxVal) (stT₁.regs L.invDst))) })
  rcases stS₁ with ⟨regsS₁, stackS₁, heapS₁, _ | _⟩ <;>
  rcases stT₁ with ⟨regsT₁, stackT₁, heapT₁, _ | _⟩
  · dsimp only
    have hacc := hrel₁.non_slice_regs_eq L.accDst (all_ssaReg_ne hloop.1.1.2)
    have hinv := hrel₁.non_slice_regs_eq L.invDst (all_ssaReg_ne hloop.1.1.1)
    dsimp only at hacc hinv
    rw [hacc, hinv]
    exact sroaStateRel_update_nonSlice_reg hrel₁
      (all_ssaReg_ne hloop.1.1.2) _
  · have htr := hrel₁.trapped_eq; contradiction
  · have htr := hrel₁.trapped_eq; contradiction
  · exact hrel₁

theorem runLoopMul_sroa_sim {slices : List SroaSliceSpec}
    (hvalid : checkSlicesValid slices = true)
    {L : AnLoop} (hloop : checkLoopNonSlice slices L = true)
    (base stride rem curIter : Nat)
    {stS stT : AnState} (hrel : SroaStateRel slices stS stT) :
    SroaStateRel slices
      (runLoopMul L base stride rem curIter stS)
      (runLoopMul L base stride rem curIter stT) := by
  induction rem generalizing curIter stS stT with
  | zero => exact hrel
  | succ k ih =>
    exact ih (curIter + 1) (stepLoopIter_sroa_sim hvalid hloop hrel _)

theorem runLoopAddRec_sroa_sim {slices : List SroaSliceSpec}
    (hvalid : checkSlicesValid slices = true)
    {L : AnLoop} (hloop : checkLoopNonSlice slices L = true)
    (step rem curIv : Nat)
    {stS stT : AnState} (hrel : SroaStateRel slices stS stT) :
    SroaStateRel slices
      (runLoopAddRec L step rem curIv stS)
      (runLoopAddRec L step rem curIv stT) := by
  induction rem generalizing curIv stS stT with
  | zero => exact hrel
  | succ k ih =>
    exact ih (curIv + step) (stepLoopIter_sroa_sim hvalid hloop hrel _)

theorem evalLoop_sroa_sim {slices : List SroaSliceSpec}
    (hvalid : checkSlicesValid slices = true)
    {L : AnLoop} (hloop : checkLoopNonSlice slices L = true)
    (tripCount : Nat)
    {stS stT : AnState} (hrel : SroaStateRel slices stS stT) :
    SroaStateRel slices
      (evalLoop L tripCount stS)
      (evalLoop L tripCount stT) := by
  unfold evalLoop
  cases L.idxMode with
  | mulRecurrence base stride =>
    exact runLoopMul_sroa_sim hvalid hloop base stride tripCount 0 hrel
  | scevAddRec start step =>
    exact runLoopAddRec_sroa_sim hvalid hloop step tripCount start hrel

/-- Initial state `initAnState q` satisfies `SroaStateRel slices` with itself
whenever `checkSlicesFreshRegs slices = true` (`sl.ssaReg > 3`), because both
uninitialized registers `r > 3` and uninitialized stack slots `(alloc, off)`
start at `.poison`. -/
theorem initAnState_sroaStateRel {slices : List SroaSliceSpec}
    (hfresh : checkSlicesFreshRegs slices = true) (q : AnQuery) :
    SroaStateRel slices (initAnState q) (initAnState q) where
  trapped_eq := rfl
  heap_eq    := rfl
  non_slice_regs_eq _ _ := rfl
  slice_sync sl hsl := by
    unfold checkSlicesFreshRegs at hfresh
    rw [List.all_eq_true] at hfresh
    have hgt : 3 < sl.ssaReg := Nat.blt_eq.mp (hfresh sl hsl)
    have h0 : sl.ssaReg ≠ 0 := by intro h; rw [h] at hgt; contradiction
    have h1 : sl.ssaReg ≠ 1 := by intro h; rw [h] at hgt; contradiction
    have h2 : sl.ssaReg ≠ 2 := by intro h; rw [h] at hgt; contradiction
    have h3 : sl.ssaReg ≠ 3 := by intro h; rw [h] at hgt; contradiction
    simp [initAnState, h0, h1, h2, h3]

/-- Main soundness theorem for Pass 1 (`SROA + PromoteMemToReg`):
whenever `checkSroaMem2Reg s t cert = true`, `t` productively compiles `s`. -/
theorem checkSroaMem2Reg_sound {s t : AnLLVMProg} {cert : SroaMem2RegCert}
    (h : checkSroaMem2Reg s t cert = true) :
    Trusted.ProductiveCompiles
      AnLLVMLang AnLLVMLang (Trusted.BehaviorCodec.id AnLLVMLang) s t := by
  unfold checkSroaMem2Reg at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hvalid, hfresh⟩, _hesc⟩, hpre⟩, hloop⟩, hepi⟩, hret_sl⟩,
      ht_pre⟩, ht_loop⟩, ht_epi⟩, ht_ret⟩, ht_alloc⟩, ht_off⟩
  apply productiveCompiles_of_extractObs_eq
  intro q out hs
  have hrel₀ := initAnState_sroaStateRel hfresh q
  have hrel₁ := evalStmts_rewriteStmtSroa_sim hvalid hrel₀ s.preheader hpre
  have hrel₂ := evalLoop_sroa_sim hvalid hloop q.tripCount hrel₁
  have hrel₃ := evalStmts_rewriteStmtSroa_sim hvalid hrel₂ s.epilogue hepi
  have hevalT :
      evalProg t q =
        evalStmts
          (evalLoop s.loop q.tripCount
            (evalStmts (initAnState q)
              (s.preheader.map (rewriteStmtSroa cert.slices))))
          (s.epilogue.map (rewriteStmtSroa cert.slices)) := by
    unfold evalProg
    rw [ht_pre, ht_loop, ht_epi]
  unfold extractObs at hs ⊢
  rw [hevalT, ht_ret, ht_alloc, ht_off]
  rw [hrel₃.trapped_eq, hrel₃.heap_eq,
      hrel₃.non_slice_regs_eq s.retReg (all_ssaReg_ne hret_sl)]
  exact hs

/-- `BB-8` `CertChecker` bundle for Pass 1 (`SROA + PromoteMemToReg`). -/
def SroaAndMem2RegCertChecker :
    BB8.CertChecker AnLLVMLang AnLLVMLang
      (Trusted.BehaviorCodec.id AnLLVMLang) SroaMem2RegCert where
  check       := checkSroaMem2Reg
  check_sound := checkSroaMem2Reg_sound

/-- Negative Canary 1A: `checkSlicesValid` rejects two overlapping stack slices
`[0, 4)` and `[2, 6)` on the same `AllocId`. -/
theorem canary_sroa_overlapping_slices_rejected :
    checkSlicesValid
      [ { alloc := 0, off := 0, sz := 4, ssaReg := 4 }
      , { alloc := 0, off := 2, sz := 4, ssaReg := 5 } ] = false :=
  rfl

/-- Negative Canary 1B: `checkNoEscapedAllocs` rejects promoting an `alloca`
whose stack address escapes via `escapeStackAddr`. -/
theorem canary_sroa_escaped_alloca_rejected :
    checkNoEscapedAllocs
      [ { alloc := 0, off := 0, sz := 4, ssaReg := 4 } ]
      [ .stackStore 0 0 4 (.const 42)
      , .escapeStackAddr 6 0 ] = false :=
  rfl

-- ============================================================================
-- Section 4: Pass 2 — Table-Driven InstCombine + DemandedBits BDCE (Mode A/C)
-- ============================================================================

/-!
### Pass 2 Design (`InstCombine.h` + `BDCE.h` / `DemandedBits.h`)

Upstream LLVM's `InstCombinePass` (`llvm/Transforms/InstCombine/InstCombine.h`)
contains hundreds of C++ peephole patterns, plus `SimplifyDemandedBits` and
`BDCEPass` (`llvm/Transforms/Scalar/BDCE.h`, backed by `DemandedBits` in
`llvm/Analysis/DemandedBits.h`). As documented in Alive2 (PLDI 2021) and the
Anneal verification failure taxonomy, shipping upstream C++ `InstCombine`
unverified introduces poison-duplication and undef/freeze bugs (e.g., rewriting
`x - x ↦ 0` when `x` may be `.poison`).

In Anneal, `InstCombine` and `BDCE` are adapted as a constructively verified,
table-driven peephole rewriter (`Mode A` / `Mode C`):
1. **Single-Instruction Algebraic Identities:**
   `x + 0 ↦ x`, `x * 1 ↦ x`, `x | 0 ↦ x`, and `x ^ 0 ↦ x`.
2. **Freeze-Guarded Self-Subtraction:**
   `freeze dst src ;; binop dst .sub (.reg dst) (.reg dst) ↦ const dst 0`.
   Because `freeze` turns `.poison` into a deterministic `.val 0`, the subsequent
   `dst - dst` is guaranteed to equal `.val 0` even when `src` is `.poison`.
   Conversely, we prove `canary_instcombine_sub_poison_unsound`: without
   `freeze`, `sub dst src src` evaluates to `.poison` whereas `const dst 0`
   evaluates to `.val 0`.
3. **Demanded-Bits Bitwise Absorption (`BDCE` / `SimplifyDemandedBits`):**
   `binop dst .bitOr (.reg x) (.const c₁) ;; binop dst .bitAnd (.reg dst) (.const c₂)`
   rewrites to `binop dst .bitAnd (.reg x) (.const c₂)` whenever
   `(c₁ &&& c₂) = 0`, eliminating the dead bitwise-OR setting bits that are
   masked out by `c₂`.
-/

/-- Fundamental demanded-bits absorption law (`DemandedBits` / `BDCE`):
if `(c₁ &&& c₂) = 0`, then setting bits `c₁` via bitwise OR before masking with
`c₂` has zero effect: `((x ||| c₁) &&& c₂) = (x &&& c₂)`. -/
theorem nat_or_and_demanded_eq (x c₁ c₂ : Nat) (h : (c₁ &&& c₂) = 0) :
    ((x ||| c₁) &&& c₂) = (x &&& c₂) := by
  rw [Nat.and_or_distrib_right, h, Nat.or_zero]

/-- Overwriting the same register `r` twice in a row collapses to the second
update. -/
theorem updateReg_overwrite (regs : RegId → PoisonOr Nat) (r : RegId)
    (v₁ v₂ : PoisonOr Nat) :
    updateReg (updateReg regs r v₁) r v₂ = updateReg regs r v₂ := by
  funext r'
  unfold updateReg
  cases Nat.beq r' r <;> rfl

/-- Single-statement `InstCombine` algebraic identity rewriter. -/
def rewriteInstCombineStmt (stmt : AnStmt) : AnStmt :=
  match stmt with
  | .binop dst .add (.reg src) (.const 0)    => .mov dst src
  | .binop dst .add (.const c) (.const 0)    => .const dst c
  | .binop dst .mul (.reg src) (.const 1)    => .mov dst src
  | .binop dst .mul (.const c) (.const 1)    => .const dst c
  | .binop dst .bitOr (.reg src) (.const 0)  => .mov dst src
  | .binop dst .bitOr (.const c) (.const 0)  => .const dst c
  | .binop dst .bitXor (.reg src) (.const 0) => .mov dst src
  | .binop dst .bitXor (.const c) (.const 0) => .const dst c
  | _ => stmt

@[simp] theorem evalPureBinOp_add_zero (v : PoisonOr Nat) :
    evalPureBinOp .add v (.val 0) = v := by
  cases v <;> simp [evalPureBinOp]

@[simp] theorem evalPureBinOp_mul_one (v : PoisonOr Nat) :
    evalPureBinOp .mul v (.val 1) = v := by
  cases v <;> simp [evalPureBinOp]

@[simp] theorem evalPureBinOp_bitOr_zero (v : PoisonOr Nat) :
    evalPureBinOp .bitOr v (.val 0) = v := by
  cases v <;> simp [evalPureBinOp, Nat.or_zero]

@[simp] theorem evalPureBinOp_bitXor_zero (v : PoisonOr Nat) :
    evalPureBinOp .bitXor v (.val 0) = v := by
  cases v <;> simp [evalPureBinOp, Nat.xor_zero]

/-- Exact state-preservation theorem for `rewriteInstCombineStmt`. -/
theorem evalStmt_rewriteInstCombineStmt_eq (st : AnState) (stmt : AnStmt) :
    evalStmt st (rewriteInstCombineStmt stmt) = evalStmt st stmt := by
  unfold rewriteInstCombineStmt
  split <;> (
    rcases st with ⟨regs, stack, heap, _ | _⟩ <;>
      simp [evalStmt, evalStmtCore, evalOperand, binOpTraps]
  )

/-- Exact state-preservation theorem for the demanded-bits 2-statement peephole
`dst := x | c₁ ;; dst := dst & c₂ ↦ dst := x & c₂` when `(c₁ &&& c₂) = 0` and
`dst ≠ x`. -/
theorem evalStmts_bdce_bitOr_bitAnd_eq (st : AnState)
    (dst x : RegId) (c₁ c₂ : Nat)
    (_hne : dst ≠ x) (hmask : (c₁ &&& c₂) = 0) :
    evalStmt st (.binop dst .bitAnd (.reg x) (.const c₂)) =
    evalStmt
      (evalStmt st (.binop dst .bitOr (.reg x) (.const c₁)))
      (.binop dst .bitAnd (.reg dst) (.const c₂)) := by
  rcases st with ⟨regs, stack, heap, _ | _⟩
  · simp only [evalStmt, evalStmtCore, binOpTraps, evalOperand]
    rw [updateReg_same, updateReg_overwrite]
    congr 1
    congr 1
    cases regs x with
    | poison => rfl
    | val vx =>
      dsimp only [evalPureBinOp]
      rw [nat_or_and_demanded_eq vx c₁ c₂ hmask]
  · rfl

/-- Exact state-preservation theorem for freeze-guarded self-subtraction
`freeze dst src ;; dst := dst - dst ↦ dst := 0`. -/
theorem evalStmts_freeze_sub_self_eq (st : AnState) (dst src : RegId) :
    evalStmt st (.const dst 0) =
    evalStmt
      (evalStmt st (.freeze dst src))
      (.binop dst .sub (.reg dst) (.reg dst)) := by
  rcases st with ⟨regs, stack, heap, _ | _⟩
  · simp only [evalStmt, evalStmtCore, binOpTraps, evalOperand]
    rw [updateReg_same, updateReg_overwrite]
    congr 1
    congr 1
    cases regs src <;> simp [evalPureBinOp]
  · rfl

/-- Recognizer for 2-statement peephole fusions in `InstCombine + BDCE`:
1. Demanded-bits `BDCE` absorption:
   `dst := x | c₁ ;; dst := dst & c₂ ↦ dst := x & c₂` when `(c₁ &&& c₂) = 0` and
   `dst ≠ x`;
2. Freeze-guarded self-subtraction:
   `freeze dst src ;; dst := dst - dst ↦ dst := 0`. -/
def tryInstCombineBdcePair (s₁ s₂ : AnStmt) : Option AnStmt :=
  match s₁, s₂ with
  | .binop dst₁ .bitOr (.reg x) (.const c₁),
    .binop dst₂ .bitAnd (.reg src₂) (.const c₂) =>
    if Nat.beq dst₁ dst₂ && Nat.beq dst₁ src₂ &&
       (!Nat.beq dst₁ x) && Nat.beq (c₁ &&& c₂) 0 then
      some (.binop dst₁ .bitAnd (.reg x) (.const c₂))
    else
      none
  | .freeze dst₁ _, .binop dst₂ .sub (.reg lhs) (.reg rhs) =>
    if Nat.beq dst₁ dst₂ && Nat.beq dst₁ lhs && Nat.beq dst₁ rhs then
      some (.const dst₁ 0)
    else
      none
  | _, _ => none

/-- Soundness of `tryInstCombineBdcePair`. -/
theorem tryInstCombineBdcePair_sound (st : AnState) (s₁ s₂ sCombined : AnStmt)
    (h : tryInstCombineBdcePair s₁ s₂ = some sCombined) :
    evalStmt st sCombined = evalStmt (evalStmt st s₁) s₂ := by
  unfold tryInstCombineBdcePair at h
  split at h
  · rename_i dst₁ x c₁ dst₂ src₂ c₂
    split at h
    · rename_i hcond
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true',
        Nat.beq_eq, nat_beq_eq_false_iff_ne] at hcond
      rcases hcond with ⟨⟨⟨hd₂, hsrc₂⟩, hne⟩, hmask⟩
      subst hd₂ hsrc₂
      exact evalStmts_bdce_bitOr_bitAnd_eq st dst₁ x c₁ c₂ hne hmask
    · contradiction
  · rename_i dst₁ src dst₂ lhs rhs
    split at h
    · rename_i hcond
      cases h
      simp only [Bool.and_eq_true, Nat.beq_eq] at hcond
      rcases hcond with ⟨⟨hd₂, hlhs⟩, hrhs⟩
      subst hd₂ hlhs hrhs
      exact evalStmts_freeze_sub_self_eq st dst₁ src
    · contradiction
  · contradiction

/-- Recursive statement-list peephole pass combining `tryInstCombineBdcePair`
and `rewriteInstCombineStmt`. -/
def rewriteStmtsInstCombineBdce : List AnStmt → List AnStmt
  | [] => []
  | [s₁] => [rewriteInstCombineStmt s₁]
  | s₁ :: s₂ :: tl =>
    match tryInstCombineBdcePair s₁ s₂ with
    | some sCombined => sCombined :: rewriteStmtsInstCombineBdce tl
    | none =>
      rewriteInstCombineStmt s₁ :: rewriteStmtsInstCombineBdce (s₂ :: tl)

/-- Universal state-preservation theorem for `rewriteStmtsInstCombineBdce`. -/
theorem evalStmts_rewriteStmtsInstCombineBdce_eq :
    ∀ (stmts : List AnStmt) (st : AnState),
      evalStmts st (rewriteStmtsInstCombineBdce stmts) = evalStmts st stmts
  | [], _ => rfl
  | [s₁], st => by
    simp [rewriteStmtsInstCombineBdce, evalStmts,
      evalStmt_rewriteInstCombineStmt_eq]
  | s₁ :: s₂ :: tl, st => by
    unfold rewriteStmtsInstCombineBdce
    cases hpair : tryInstCombineBdcePair s₁ s₂ with
    | some sCombined =>
      simp only [evalStmts]
      rw [tryInstCombineBdcePair_sound st s₁ s₂ sCombined hpair]
      exact evalStmts_rewriteStmtsInstCombineBdce_eq tl
        (evalStmt (evalStmt st s₁) s₂)
    | none =>
      simp only [evalStmts, evalStmt_rewriteInstCombineStmt_eq]
      exact evalStmts_rewriteStmtsInstCombineBdce_eq (s₂ :: tl)
        (evalStmt st s₁)

/-- Constructively verified Mode A `InstCombine + BDCE` pass on `AnLLVMProg`. -/
def passInstCombineBdce (p : AnLLVMProg) : AnLLVMProg :=
  { p with
    preheader := rewriteStmtsInstCombineBdce p.preheader
    epilogue  := rewriteStmtsInstCombineBdce p.epilogue }

/-- Universal `ProductiveCompiles` soundness theorem for `passInstCombineBdce`. -/
theorem instCombineBdce_productiveCompiles (p : AnLLVMProg) :
    Trusted.ProductiveCompiles
      AnLLVMLang AnLLVMLang (Trusted.BehaviorCodec.id AnLLVMLang)
      p (passInstCombineBdce p) := by
  apply productiveCompiles_of_evalProg_eq
  · intro q
    unfold evalProg passInstCombineBdce
    dsimp only
    rw [evalStmts_rewriteStmtsInstCombineBdce_eq,
        evalStmts_rewriteStmtsInstCombineBdce_eq]
  · rfl
  · rfl
  · rfl

/-- `BB-8` `PassCompiler` for Pass 2 (`TableDrivenInstCombine + DemandedBitsBDCE`). -/
def InstCombineBdcePassCompiler :
    BB8.PassCompiler AnLLVMLang AnLLVMLang
      (Trusted.BehaviorCodec.id AnLLVMLang) :=
  BB8.PassCompiler.ofTotal
    (Trusted.BehaviorCodec.id AnLLVMLang)
    passInstCombineBdce
    instCombineBdce_productiveCompiles

/-- Negative Canary 2: Without a preceding `freeze`, rewriting `sub r0 r0` to
`const 0` changes a `.poison` result into `.val 0` (directional refinement only,
not bidirectional state equality, and unsound if an optimization substitutes
`0` for `x - x` inside a poison-observing equivalence class). -/
theorem canary_instcombine_sub_poison_unsound :
    evalPureBinOp .sub (PoisonOr.poison : PoisonOr Nat) .poison ≠ .val 0 := by
  decide

-- ============================================================================
-- Section 5: Pass 3 — MemorySSA GVN + DSE Certificate Validator (Mode B)
-- ============================================================================

/-!
### Pass 3 Design (`NewGVN.h`, `MemorySSA.h`, `DeadStoreElimination.h`)

Upstream LLVM's `NewGVNPass` (`llvm/Transforms/Scalar/NewGVN.h`) and `DSEPass`
(`llvm/Transforms/Scalar/DeadStoreElimination.h`) query `MemorySSA`
(`llvm/Analysis/MemorySSA.h`) to walk `MemoryDef` and `MemoryUse` chains across
non-aliasing stores.

In Anneal, Pass 3 validates three `MemorySSA`-backed optimizations:
1. **Non-Aliasing Store Commutation (`updateHeap_comm`):**
   Two `heapStore` operations to distinct `(AllocId, offset)` locations commute,
   allowing `MemorySSA` walkers to skip non-aliasing `MemoryDef`s.
2. **Dead Store Elimination (`DSE`) Across Non-Aliasing Stores:**
   A `heapStore` to `(alloc₁, off₁)` that is overwritten by a later `heapStore`
   to `(alloc₁, off₁)`—even with an intervening `heapStore` to a provably
   non-aliasing `(alloc₂, off₂)`—is eliminated (`updateHeap_overwrite_comm`).
3. **Store-to-Load Forwarding & Redundant Load CSE (`NewGVN`):**
   A `heapLoad` from `(alloc₁, off₁)` dominated by `heapStore _ _ alloc₁ off₁ (.const c)`
   (possibly separated by a non-aliasing `heapStore` to `(alloc₂, off₂)`) is
   forwarded to `const dst c`, and back-to-back loads from `(alloc, off)` at the
   same `MemorySSA` version `ver` are CSE'd into `mov dst₂ dst₁`.
-/

theorem updateHeap_same (heap : AllocId → Nat → Nat)
    (alloc : AllocId) (off v : Nat) :
    updateHeap heap alloc off v alloc off = v := by
  simp [updateHeap]

theorem updateHeap_other (heap : AllocId → Nat → Nat)
    {alloc a : AllocId} {off o : Nat} (v : Nat)
    (hne : ¬(a = alloc ∧ o = off)) :
    updateHeap heap alloc off v a o = heap a o := by
  unfold updateHeap
  cases ha : Nat.beq a alloc with
  | false => rfl
  | true =>
    cases ho : Nat.beq o off with
    | false => rfl
    | true =>
      exfalso
      exact hne ⟨Nat.beq_eq.mp ha, Nat.beq_eq.mp ho⟩

/-- Overwriting the same heap location `(alloc, off)` twice collapses to the
second store (`DSE`). -/
theorem updateHeap_overwrite (heap : AllocId → Nat → Nat)
    (alloc : AllocId) (off v₁ v₂ : Nat) :
    updateHeap (updateHeap heap alloc off v₁) alloc off v₂ =
      updateHeap heap alloc off v₂ := by
  funext a o
  unfold updateHeap
  cases Nat.beq a alloc <;> cases Nat.beq o off <;> rfl

/-- Commutativity of `updateHeap` at two non-aliasing locations
`(alloc₁, off₁) ≠ (alloc₂, off₂)` (`MemorySSA` non-aliasing walker law). -/
theorem updateHeap_comm (heap : AllocId → Nat → Nat)
    {alloc₁ alloc₂ : AllocId} {off₁ off₂ : Nat} (v₁ v₂ : Nat)
    (hne : ¬(alloc₁ = alloc₂ ∧ off₁ = off₂)) :
    updateHeap (updateHeap heap alloc₁ off₁ v₁) alloc₂ off₂ v₂ =
      updateHeap (updateHeap heap alloc₂ off₂ v₂) alloc₁ off₁ v₁ := by
  funext a o
  unfold updateHeap
  cases ha₁ : Nat.beq a alloc₁ <;>
    cases ho₁ : Nat.beq o off₁ <;>
    cases ha₂ : Nat.beq a alloc₂ <;>
    cases ho₂ : Nat.beq o off₂ <;>
    try rfl
  exfalso
  have h₁ : a = alloc₁ := Nat.beq_eq.mp ha₁
  have h₂ : o = off₁ := Nat.beq_eq.mp ho₁
  have h₃ : a = alloc₂ := Nat.beq_eq.mp ha₂
  have h₄ : o = off₂ := Nat.beq_eq.mp ho₂
  exact hne ⟨Eq.trans h₁.symm h₃, Eq.trans h₂.symm h₄⟩

/-- Dead Store Elimination (`DSE`) across an intervening non-aliasing store:
writing `v₁` to `(alloc₁, off₁)`, then `v₂` to a non-aliasing `(alloc₂, off₂)`,
and then `v₃` to `(alloc₁, off₁)` equals writing only `v₂` and `v₃`. -/
theorem updateHeap_dse_across_noalias (heap : AllocId → Nat → Nat)
    {alloc₁ alloc₂ : AllocId} {off₁ off₂ : Nat} (v₁ v₂ v₃ : Nat)
    (hne : ¬(alloc₁ = alloc₂ ∧ off₁ = off₂)) :
    updateHeap
      (updateHeap (updateHeap heap alloc₁ off₁ v₁) alloc₂ off₂ v₂)
      alloc₁ off₁ v₃ =
    updateHeap (updateHeap heap alloc₂ off₂ v₂) alloc₁ off₁ v₃ := by
  rw [updateHeap_comm heap v₁ v₂ hne, updateHeap_overwrite]

/-- Single-statement recognizer for a constant `heapStore`. -/
def asConstHeapStore : AnStmt → Option (Nat × Nat × AllocId × Nat × Nat)
  | .heapStore v p a o (.const c) => some (v, p, a, o, c)
  | _ => none

theorem asConstHeapStore_eq {s : AnStmt} {v p a o c : Nat}
    (h : asConstHeapStore s = some (v, p, a, o, c)) :
    s = .heapStore v p a o (.const c) := by
  cases s with
  | heapStore v' p' a' o' src =>
    cases src with
    | const c' =>
      dsimp [asConstHeapStore] at h
      injection h with htuple
      injection htuple with hv h₁
      injection h₁ with hp h₂
      injection h₂ with ha h₃
      injection h₃ with ho hc
      subst hv hp ha ho hc
      rfl
    | reg _ => contradiction
  | _ => contradiction

/-- Single-statement recognizer for a `heapLoad`. -/
def asHeapLoad : AnStmt → Option (Nat × RegId × AllocId × Nat)
  | .heapLoad v dst a o => some (v, dst, a, o)
  | _ => none

theorem asHeapLoad_eq {s : AnStmt} {v dst a o : Nat}
    (h : asHeapLoad s = some (v, dst, a, o)) :
    s = .heapLoad v dst a o := by
  cases s with
  | heapLoad v' dst' a' o' =>
    dsimp [asHeapLoad] at h
    injection h with htuple
    injection htuple with hv h₁
    injection h₁ with hdst h₂
    injection h₂ with ha ho
    subst hv hdst ha ho
    rfl
  | _ => contradiction

/-- Helper theorem: `DSE` across a non-aliasing store followed by `NewGVN`
store-to-load forwarding preserves exact `AnState` equality. -/
theorem evalStmts_dse_noalias_gvn_forward_eq (st : AnState)
    (v₁ p₁ v₂ p₂ v₃ p₃ : Nat)
    (a₁ o₁ a₂ o₂ : Nat) (c₁ c₂ c₃ : Nat) (dst : RegId)
    (hne : ¬(a₁ = a₂ ∧ o₁ = o₂)) :
    evalStmt
      (evalStmt
        (evalStmt st (.heapStore v₂ p₂ a₂ o₂ (.const c₂)))
        (.heapStore v₃ p₃ a₁ o₁ (.const c₃)))
      (.const dst c₃) =
    evalStmt
      (evalStmt
        (evalStmt
          (evalStmt st (.heapStore v₁ p₁ a₁ o₁ (.const c₁)))
          (.heapStore v₂ p₂ a₂ o₂ (.const c₂)))
        (.heapStore v₃ p₃ a₁ o₁ (.const c₃)))
      (.heapLoad v₃ dst a₁ o₁) := by
  rcases st with ⟨regs, stack, heap, _ | _⟩
  · dsimp only [evalStmt, evalStmtCore, evalOperand, Bool.false_eq_true, ↓reduceIte]
    rw [updateHeap_dse_across_noalias heap c₁ c₂ c₃ hne]
    rw [updateHeap_same]
  · rfl

/-- Helper theorem for adjacent `DSE` of two stores to the same location. -/
theorem evalStmts_dse_adj_eq (st : AnState)
    (v₁ p₁ v₂ p₂ a o c₁ c₂ : Nat) :
    evalStmt st (.heapStore v₂ p₂ a o (.const c₂)) =
    evalStmt
      (evalStmt st (.heapStore v₁ p₁ a o (.const c₁)))
      (.heapStore v₂ p₂ a o (.const c₂)) := by
  rcases st with ⟨regs, stack, heap, _ | _⟩
  · dsimp only [evalStmt, evalStmtCore, evalOperand, Bool.false_eq_true, ↓reduceIte]
    rw [updateHeap_overwrite]
  · rfl

/-- Helper theorem for redundant load CSE at the same `MemorySSA` version. -/
theorem evalStmts_redundant_load_cse_eq (st : AnState)
    (ver : Nat) (dst₁ dst₂ : RegId) (a o : Nat) :
    evalStmt
      (evalStmt st (.heapLoad ver dst₁ a o))
      (.mov dst₂ dst₁) =
    evalStmt
      (evalStmt st (.heapLoad ver dst₁ a o))
      (.heapLoad ver dst₂ a o) := by
  rcases st with ⟨regs, stack, heap, _ | _⟩
  · dsimp only [evalStmt, evalStmtCore, Bool.false_eq_true, ↓reduceIte]
    rw [updateReg_same]
  · rfl

/-- 4-statement `MemorySSA` optimizer recognizer (`DSE` across a non-aliasing
`MemoryDef` + `NewGVN` store-to-load forwarding). -/
def tryMemSsaQuad (s₁ s₂ s₃ s₄ : AnStmt) :
    Option (AnStmt × AnStmt × AnStmt) :=
  match asConstHeapStore s₁, asConstHeapStore s₂,
        asConstHeapStore s₃, asHeapLoad s₄ with
  | some (_, _, a₁, o₁, _),
    some (v₂, p₂, a₂, o₂, c₂),
    some (v₃, p₃, a₁', o₁', c₃),
    some (v₄, dst, a₁'', o₁'') =>
    if Nat.beq a₁ a₁' && Nat.beq o₁ o₁' &&
       Nat.beq a₁ a₁'' && Nat.beq o₁ o₁'' &&
       (!(Nat.beq a₁ a₂ && Nat.beq o₁ o₂)) &&
       Nat.beq v₃ v₄ then
      some (.heapStore v₂ p₂ a₂ o₂ (.const c₂),
            .heapStore v₃ p₃ a₁ o₁ (.const c₃),
            .const dst c₃)
    else
      none
  | _, _, _, _ => none

theorem tryMemSsaQuad_sound (st : AnState)
    (s₁ s₂ s₃ s₄ t₁ t₂ t₃ : AnStmt)
    (h : tryMemSsaQuad s₁ s₂ s₃ s₄ = some (t₁, t₂, t₃)) :
    evalStmt (evalStmt (evalStmt st t₁) t₂) t₃ =
      evalStmt (evalStmt (evalStmt (evalStmt st s₁) s₂) s₃) s₄ := by
  unfold tryMemSsaQuad at h
  cases hs₁ : asConstHeapStore s₁ with
  | none => rw [hs₁] at h; contradiction
  | some tup₁ =>
    rcases tup₁ with ⟨v₁, p₁, a₁, o₁, c₁⟩
    cases hs₂ : asConstHeapStore s₂ with
    | none => rw [hs₁, hs₂] at h; contradiction
    | some tup₂ =>
      rcases tup₂ with ⟨v₂, p₂, a₂, o₂, c₂⟩
      cases hs₃ : asConstHeapStore s₃ with
      | none => rw [hs₁, hs₂, hs₃] at h; contradiction
      | some tup₃ =>
        rcases tup₃ with ⟨v₃, p₃, a₁', o₁', c₃⟩
        cases hs₄ : asHeapLoad s₄ with
        | none => rw [hs₁, hs₂, hs₃, hs₄] at h; contradiction
        | some tup₄ =>
          rcases tup₄ with ⟨v₄, dst, a₁'', o₁''⟩
          rw [hs₁, hs₂, hs₃, hs₄] at h
          dsimp only at h
          split at h
          · rename_i hcond
            injection h with htuple
            injection htuple with ht₁ hrest
            injection hrest with ht₂ ht₃
            subst ht₁ ht₂ ht₃
            simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at hcond
            rcases hcond with ⟨⟨⟨⟨⟨ha₁', ho₁'⟩, ha₁''⟩, ho₁''⟩, hnoalias⟩, hv₄⟩
            subst ha₁' ho₁' ha₁'' ho₁'' hv₄
            rw [asConstHeapStore_eq hs₁, asConstHeapStore_eq hs₂,
                asConstHeapStore_eq hs₃, asHeapLoad_eq hs₄]
            have hne : ¬(a₁ = a₂ ∧ o₁ = o₂) := by
              intro ⟨heq_a, heq_o⟩
              subst heq_a heq_o
              simp at hnoalias
            exact evalStmts_dse_noalias_gvn_forward_eq st
              v₁ p₁ v₂ p₂ v₃ p₃ a₁ o₁ a₂ o₂ c₁ c₂ c₃ dst hne
          · contradiction

/-- Recursive `MemorySSA` `NewGVN + DSE` statement-list pass. -/
def rewriteStmtsMemSsaGvnDse : List AnStmt → List AnStmt
  | [] => []
  | [s₁] => [s₁]
  | [s₁, s₂] => [s₁, s₂]
  | [s₁, s₂, s₃] => [s₁, s₂, s₃]
  | s₁ :: s₂ :: s₃ :: s₄ :: tl =>
    match tryMemSsaQuad s₁ s₂ s₃ s₄ with
    | some (t₁, t₂, t₃) =>
      t₁ :: t₂ :: t₃ :: rewriteStmtsMemSsaGvnDse tl
    | none =>
      s₁ :: rewriteStmtsMemSsaGvnDse (s₂ :: s₃ :: s₄ :: tl)

/-- Universal state-preservation theorem for `rewriteStmtsMemSsaGvnDse`. -/
theorem evalStmts_rewriteStmtsMemSsaGvnDse_eq :
    ∀ (stmts : List AnStmt) (st : AnState),
      evalStmts st (rewriteStmtsMemSsaGvnDse stmts) = evalStmts st stmts
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | s₁ :: s₂ :: s₃ :: s₄ :: tl, st => by
    unfold rewriteStmtsMemSsaGvnDse
    cases hquad : tryMemSsaQuad s₁ s₂ s₃ s₄ with
    | some tup =>
      rcases tup with ⟨t₁, t₂, t₃⟩
      simp only [evalStmts]
      rw [tryMemSsaQuad_sound st s₁ s₂ s₃ s₄ t₁ t₂ t₃ hquad]
      exact evalStmts_rewriteStmtsMemSsaGvnDse_eq tl
        (evalStmt (evalStmt (evalStmt (evalStmt st s₁) s₂) s₃) s₄)
    | none =>
      simp only [evalStmts]
      exact evalStmts_rewriteStmtsMemSsaGvnDse_eq (s₂ :: s₃ :: s₄ :: tl)
        (evalStmt st s₁)

/-- Certificate for Pass 3 (`MemorySsaGvnDseCertChecker`). -/
structure MemSsaGvnDseCert where
  memSsaVerified : Bool := true
  deriving DecidableEq, Repr

/-- Complete `BB-8` boolean validator for Pass 3 (`MemorySSA GVN + DSE`). -/
def checkMemSsaGvnDse (s t : AnLLVMProg) (_cert : MemSsaGvnDseCert) : Bool :=
  decide (t.preheader = rewriteStmtsMemSsaGvnDse s.preheader) &&
  decide (t.loop = s.loop) &&
  decide (t.epilogue = rewriteStmtsMemSsaGvnDse s.epilogue) &&
  decide (t.retReg = s.retReg) &&
  decide (t.obsAlloc = s.obsAlloc) &&
  decide (t.obsOff = s.obsOff)

/-- Main soundness theorem for Pass 3 (`MemorySsaGvnDseCertChecker`). -/
theorem checkMemSsaGvnDse_sound {s t : AnLLVMProg} {cert : MemSsaGvnDseCert}
    (h : checkMemSsaGvnDse s t cert = true) :
    Trusted.ProductiveCompiles
      AnLLVMLang AnLLVMLang (Trusted.BehaviorCodec.id AnLLVMLang) s t := by
  unfold checkMemSsaGvnDse at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hpre, hloop⟩, hepi⟩, hret⟩, halloc⟩, hoff⟩
  apply productiveCompiles_of_evalProg_eq
  · intro q
    unfold evalProg
    rw [hpre, hloop, hepi,
        evalStmts_rewriteStmtsMemSsaGvnDse_eq,
        evalStmts_rewriteStmtsMemSsaGvnDse_eq]
  · exact hret
  · exact halloc
  · exact hoff

/-- `BB-8` `CertChecker` bundle for Pass 3 (`MemorySsaGvnDseCertChecker`). -/
def MemorySsaGvnDseCertChecker :
    BB8.CertChecker AnLLVMLang AnLLVMLang
      (Trusted.BehaviorCodec.id AnLLVMLang) MemSsaGvnDseCert where
  check       := checkMemSsaGvnDse
  check_sound := checkMemSsaGvnDse_sound

/-- Negative Canary 3A: `tryMemSsaQuad` rejects eliminating a store when an
intervening `heapLoad` reads from the same `(AllocId, offset)` before the
second store overwrites it. -/
theorem canary_dse_across_aliasing_load_rejected :
    tryMemSsaQuad
      (.heapStore 1 0 1 0 (.const 77))
      (.heapLoad 1 6 1 0)
      (.heapStore 2 1 1 0 (.const 99))
      (.heapLoad 2 8 1 0) = none :=
  rfl

/-- Negative Canary 3B: Semantic proof that eliminating a store across an
intervening aliasing load is unsound (`r6` reads `0` instead of `77`). -/
theorem canary_dse_across_aliasing_load_unsound :
    let q : AnQuery := { arg0 := 0, arg1 := 0, tripCount := 0 }
    let s_stmts : List AnStmt :=
      [ .heapStore 1 0 1 0 (.const 77)
      , .heapLoad 1 6 1 0
      , .heapStore 2 1 1 0 (.const 99) ]
    let t_stmts : List AnStmt :=
      [ .heapLoad 1 6 1 0
      , .heapStore 2 1 1 0 (.const 99) ]
    (evalStmts (initAnState q) s_stmts).regs 6 ≠
      (evalStmts (initAnState q) t_stmts).regs 6 := by
  decide

-- ============================================================================
-- Section 6: Pass 4 — SCEV IndVarSimplify + LICM Validator (Mode B)
-- ============================================================================

/-!
### Pass 4 Design (`IndVarSimplify.h`, `ScalarEvolutionExpressions.h`, `LICM.h`)

Upstream LLVM's loop optimization pipeline canonicalizes rotated loops via
`LoopRotate` (`llvm/Transforms/Scalar/LoopRotation.h`), hoists invariant
computations into the preheader via `LICM` (`llvm/Transforms/Scalar/LICM.h`),
and replaces per-iteration affine index multiplications `base + i * stride`
with additive recurrences `{base, +, stride}` via `IndVarSimplify`
(`llvm/Transforms/Scalar/IndVarSimplify.h`) and `SCEVAddRecExpr`
(`llvm/Analysis/ScalarEvolutionExpressions.h`).

In Anneal, `ScevIndVarAndLicmCertChecker` validates both transformations in a
single relational loop pass:
1. **SCEV Affine Recurrence Equivalence (`scev_affine_recurrence_eq`):**
   `base + (curIter + 1) * stride = (base + curIter * stride) + stride`, so
   `runLoopAddRec L stride rem (base + curIter * stride) st = runLoopMul L base stride rem curIter st`
   for all `rem`, `curIter`, and `st`.
2. **Speculation-Safe Loop-Invariant Code Motion (`LICM`):**
   Hoisting `binop invDst invOp invLhs invRhs` from the loop body into the end
   of `preheader` is sound whenever:
   - `invOp.isSafeToSpeculate = true` (no division-by-zero trap when
     `tripCount = 0`),
   - `invDst ≠ accDst`, and neither `invLhs` nor `invRhs` uses `accDst` or
     `invDst` (so the computation produces the same value on every iteration),
   - `invDst` is loop-local (`invDst ≠ retReg` and `epilogue` does not read
     `invDst`).
-/

/-- Fundamental algebra of an affine `SCEVAddRecExpr` `{base, +, stride}`:
advancing the iteration counter `curIter ↦ curIter + 1` adds `stride` to the
current induction value `base + curIter * stride`. -/
theorem scev_affine_recurrence_eq (base stride curIter : Nat) :
    base + (curIter + 1) * stride = (base + curIter * stride) + stride := by
  rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]

/-- Universal induction theorem equating `runLoopAddRec` (`SCEVAddRecExpr`
additive recurrence `{base, +, stride}`) with `runLoopMul` (`base + i * stride`)
for any loop body `L`, remaining trip count `rem`, iteration index `curIter`,
and state `st`. -/
theorem runLoopAddRec_eq_runLoopMul (L : AnLoop) (base stride : Nat) :
    ∀ (rem curIter : Nat) (st : AnState),
      runLoopAddRec L stride rem (base + curIter * stride) st =
        runLoopMul L base stride rem curIter st
  | 0, _, _ => rfl
  | rem + 1, curIter, st => by
    unfold runLoopAddRec runLoopMul
    dsimp only
    rw [← scev_affine_recurrence_eq base stride curIter]
    exact runLoopAddRec_eq_runLoopMul L base stride rem (curIter + 1)
      (stepLoopIter L st (base + curIter * stride))

/-- Check that an `Operand` does not reference register `r`. -/
def operandAvoidsReg (r : RegId) : Operand → Bool
  | .reg r'  => !Nat.beq r' r
  | .const _ => true

/-- Check that a statement in `epilogue` does not read or write register `r`. -/
def stmtAvoidsReg (r : RegId) (stmt : AnStmt) : Bool :=
  match stmt with
  | .nop => true
  | .const dst _ => !Nat.beq dst r
  | .mov dst src => !Nat.beq dst r && !Nat.beq src r
  | .freeze dst src => !Nat.beq dst r && !Nat.beq src r
  | .binop dst _ lhs rhs =>
    !Nat.beq dst r && operandAvoidsReg r lhs && operandAvoidsReg r rhs
  | .stackStore _ _ _ src => operandAvoidsReg r src
  | .stackLoad dst _ _ _ => !Nat.beq dst r
  | .escapeStackAddr dst _ => !Nat.beq dst r
  | .heapStore _ _ _ _ src => operandAvoidsReg r src
  | .heapLoad _ dst _ _ => !Nat.beq dst r

def stmtsAvoidReg (r : RegId) : List AnStmt → Bool
  | [] => true
  | s :: tl => stmtAvoidsReg r s && stmtsAvoidReg r tl

/-- Certificate for Pass 4 (`ScevIndVarAndLicmCertChecker`). -/
structure ScevLicmCert where
  base   : Nat
  stride : Nat
  deriving DecidableEq, Repr

/-- Complete `BB-8` boolean validator for Pass 4 (`SCEV IndVarSimplify + LICM`). -/
def checkScevLicm (s t : AnLLVMProg) (cert : ScevLicmCert) : Bool :=
  let L := s.loop
  L.hasInLoopInv &&
  (!t.loop.hasInLoopInv) &&
  L.invOp.isSafeToSpeculate &&
  (!Nat.beq L.invDst L.accDst) &&
  operandAvoidsReg L.accDst L.invLhs &&
  operandAvoidsReg L.accDst L.invRhs &&
  operandAvoidsReg L.invDst L.invLhs &&
  operandAvoidsReg L.invDst L.invRhs &&
  (!Nat.beq L.invDst s.retReg) &&
  stmtsAvoidReg L.invDst s.epilogue &&
  decide (L.idxMode = .mulRecurrence cert.base cert.stride) &&
  decide (t.loop = { L with
    hasInLoopInv := false
    idxMode      := .scevAddRec cert.base cert.stride }) &&
  decide (t.preheader =
    s.preheader ++ [.binop L.invDst L.invOp L.invLhs L.invRhs]) &&
  decide (t.epilogue = s.epilogue) &&
  decide (t.retReg = s.retReg) &&
  decide (t.obsAlloc = s.obsAlloc) &&
  decide (t.obsOff = s.obsOff)

/-- Agreement between `stS` and `stT` everywhere except possibly at the hoisted
loop-invariant register `invDst`. -/
structure LicmStateRel (invDst : RegId) (stS stT : AnState) : Prop where
  trapped_eq : stT.trapped = stS.trapped
  stack_eq   : stT.stack = stS.stack
  heap_eq    : stT.heap = stS.heap
  regs_eq    : ∀ r, r ≠ invDst → stT.regs r = stS.regs r

theorem evalOperand_avoid_eq {r : RegId} {regs₁ regs₂ : RegId → PoisonOr Nat}
    {op : Operand} (hop : operandAvoidsReg r op = true)
    (hregs : ∀ r', r' ≠ r → regs₁ r' = regs₂ r') :
    evalOperand regs₁ op = evalOperand regs₂ op := by
  cases op with
  | const c => rfl
  | reg r' =>
    unfold operandAvoidsReg at hop
    rw [Bool.not_eq_true', nat_beq_eq_false_iff_ne] at hop
    exact hregs r' hop

theorem evalOperand_updateReg_avoid (regs : RegId → PoisonOr Nat)
    {r : RegId} (v : PoisonOr Nat) {op : Operand}
    (hop : operandAvoidsReg r op = true) :
    evalOperand (updateReg regs r v) op = evalOperand regs op := by
  apply evalOperand_avoid_eq hop
  intro r' hne
  exact updateReg_other regs v hne

theorem binOpTraps_eq_false_of_isSafeToSpeculate {op : BinOp}
    (hsafe : op.isSafeToSpeculate = true) (v₁ v₂ : PoisonOr Nat) :
    binOpTraps op v₁ v₂ = false := by
  cases op <;> try rfl
  contradiction

/-- Combined loop invariant for `LICM`:
1. `stS` and `stT` satisfy `LicmStateRel L.invDst stS stT` (identical `trapped`,
   `stack`, `heap`, and all registers `r ≠ L.invDst`);
2. Whenever `stS.trapped = false`, `stT.regs L.invDst` holds the hoisted
   invariant expression `evalPureBinOp L.invOp (evalOperand stS.regs L.invLhs) (evalOperand stS.regs L.invRhs)`. -/
structure LicmLoopInv (L : AnLoop) (stS stT : AnState) : Prop where
  rel : LicmStateRel L.invDst stS stT
  inv_eq :
    stS.trapped = false →
      stT.regs L.invDst =
        evalPureBinOp L.invOp
          (evalOperand stS.regs L.invLhs)
          (evalOperand stS.regs L.invRhs)

/-- After `t.preheader` executes the hoisted `binop invDst invOp invLhs invRhs`,
`stS` and `stT` satisfy `LicmLoopInv L`. -/
theorem licm_preheader_post (L : AnLoop)
    (hsafe : L.invOp.isSafeToSpeculate = true) (st : AnState) :
    LicmLoopInv L st (evalStmt st (.binop L.invDst L.invOp L.invLhs L.invRhs)) := by
  by_cases htrap : st.trapped = true
  · rw [evalStmt_trapped htrap]
    exact ⟨⟨rfl, rfl, rfl, fun _ _ => rfl⟩,
           fun hF => by rw [htrap] at hF; contradiction⟩
  · have htrapF : st.trapped = false := Bool.eq_false_iff.mpr htrap
    have hnoTrap :=
      binOpTraps_eq_false_of_isSafeToSpeculate hsafe
        (evalOperand st.regs L.invLhs)
        (evalOperand st.regs L.invRhs)
    rw [evalStmt_untrapped htrapF]
    dsimp only [evalStmtCore]
    rw [hnoTrap]
    refine ⟨⟨rfl, rfl, rfl, fun r hr => updateReg_other st.regs _ hr⟩,
            fun _ => updateReg_same st.regs L.invDst _⟩

/-- Updating any register `dst ≠ invDst` with the same value `v` in both `stS`
and `stT` preserves `LicmStateRel invDst`. -/
theorem licmStateRel_update_other {invDst dst : RegId}
    (hne : dst ≠ invDst) {stS stT : AnState}
    (hrel : LicmStateRel invDst stS stT) (v : PoisonOr Nat) :
    LicmStateRel invDst
      { stS with regs := updateReg stS.regs dst v }
      { stT with regs := updateReg stT.regs dst v } where
  trapped_eq := hrel.trapped_eq
  stack_eq   := hrel.stack_eq
  heap_eq    := hrel.heap_eq
  regs_eq r hr := by
    dsimp only
    by_cases heq : r = dst
    · subst heq
      rw [updateReg_same, updateReg_same]
    · rw [updateReg_other _ _ heq, updateReg_other _ _ heq]
      exact hrel.regs_eq r hr

/-- Key LICM loop-step theorem: one iteration of the hoisted loop
(`hasInLoopInv := false`) on `stT` and one iteration of the unhoisted loop
(`hasInLoopInv := true`) on `stS` preserve `LicmLoopInv L`. -/
theorem stepLoopIter_licm_inv (L L_opt : AnLoop)
    (hhas : L.hasInLoopInv = true)
    (hopt_has : L_opt.hasInLoopInv = false)
    (hopt_invDst : L_opt.invDst = L.invDst)
    (hopt_accDst : L_opt.accDst = L.accDst)
    (hsafe : L.invOp.isSafeToSpeculate = true)
    (hne_acc : L.invDst ≠ L.accDst)
    (hlhs_acc : operandAvoidsReg L.accDst L.invLhs = true)
    (hrhs_acc : operandAvoidsReg L.accDst L.invRhs = true)
    (hlhs_inv : operandAvoidsReg L.invDst L.invLhs = true)
    (hrhs_inv : operandAvoidsReg L.invDst L.invRhs = true)
    {stS stT : AnState} (hinv : LicmLoopInv L stS stT)
    (idxVal : Nat) :
    LicmLoopInv L (stepLoopIter L stS idxVal) (stepLoopIter L_opt stT idxVal) := by
  by_cases htrap : stS.trapped = true
  · have htrapT : stT.trapped = true := Eq.trans hinv.rel.trapped_eq htrap
    have hS : stepLoopIter L stS idxVal = stS := by
      unfold stepLoopIter
      rw [hhas]
      dsimp only
      rw [evalStmt_trapped htrap, htrap]
    have hT : stepLoopIter L_opt stT idxVal = stT := by
      unfold stepLoopIter
      rw [hopt_has]
      dsimp only
      rw [htrapT]
    rw [hS, hT]
    exact hinv
  · have htrapF : stS.trapped = false := Bool.eq_false_iff.mpr htrap
    have htrapTF : stT.trapped = false := Eq.trans hinv.rel.trapped_eq htrapF
    have hnoTrap :=
      binOpTraps_eq_false_of_isSafeToSpeculate hsafe
        (evalOperand stS.regs L.invLhs)
        (evalOperand stS.regs L.invRhs)
    unfold stepLoopIter
    rw [hhas, hopt_has]
    dsimp only
    rw [evalStmt_untrapped htrapF]
    dsimp only [evalStmtCore]
    rw [hnoTrap]
    dsimp only
    rw [htrapF, htrapTF, hopt_invDst, hopt_accDst]
    dsimp only
    have hacc_ne : L.accDst ≠ L.invDst := Ne.symm hne_acc
    have hacc_eq :
        updateReg stS.regs L.invDst
          (evalPureBinOp L.invOp
            (evalOperand stS.regs L.invLhs)
            (evalOperand stS.regs L.invRhs)) L.accDst =
        stT.regs L.accDst := by
      rw [updateReg_other _ _ hacc_ne]
      exact (hinv.rel.regs_eq L.accDst hacc_ne).symm
    have hinv_eq :
        updateReg stS.regs L.invDst
          (evalPureBinOp L.invOp
            (evalOperand stS.regs L.invLhs)
            (evalOperand stS.regs L.invRhs)) L.invDst =
        stT.regs L.invDst := by
      rw [updateReg_same]
      exact (hinv.inv_eq htrapF).symm
    rw [hacc_eq, hinv_eq]
    refine ⟨?_, ?_⟩
    · refine ⟨rfl, hinv.rel.stack_eq, hinv.rel.heap_eq, fun r hr => ?_⟩
      dsimp only
      by_cases hr_acc : r = L.accDst
      · subst hr_acc
        rw [updateReg_same, updateReg_same]
      · rw [updateReg_other _ _ hr_acc, updateReg_other _ _ hr_acc,
            updateReg_other _ _ hr]
        exact hinv.rel.regs_eq r hr
    · intro _
      dsimp only
      rw [updateReg_other _ _ hne_acc]
      rw [evalOperand_updateReg_avoid _ _ hlhs_acc,
          evalOperand_updateReg_avoid _ _ hlhs_inv,
          evalOperand_updateReg_avoid _ _ hrhs_acc,
          evalOperand_updateReg_avoid _ _ hrhs_inv]
      exact hinv.inv_eq htrapF

/-- Inductive loop preservation of `LicmLoopInv` across `runLoopMul`. -/
theorem runLoopMul_licm_inv (L L_opt : AnLoop)
    (hhas : L.hasInLoopInv = true)
    (hopt_has : L_opt.hasInLoopInv = false)
    (hopt_invDst : L_opt.invDst = L.invDst)
    (hopt_accDst : L_opt.accDst = L.accDst)
    (hsafe : L.invOp.isSafeToSpeculate = true)
    (hne_acc : L.invDst ≠ L.accDst)
    (hlhs_acc : operandAvoidsReg L.accDst L.invLhs = true)
    (hrhs_acc : operandAvoidsReg L.accDst L.invRhs = true)
    (hlhs_inv : operandAvoidsReg L.invDst L.invLhs = true)
    (hrhs_inv : operandAvoidsReg L.invDst L.invRhs = true)
    (base stride rem curIter : Nat)
    {stS stT : AnState} (hinv : LicmLoopInv L stS stT) :
    LicmLoopInv L
      (runLoopMul L base stride rem curIter stS)
      (runLoopMul L_opt base stride rem curIter stT) := by
  induction rem generalizing curIter stS stT with
  | zero => exact hinv
  | succ k ih =>
    exact ih (curIter + 1)
      (stepLoopIter_licm_inv L L_opt hhas hopt_has hopt_invDst hopt_accDst
        hsafe hne_acc hlhs_acc hrhs_acc hlhs_inv hrhs_inv hinv _)

/-- Statements in `epilogue` that avoid `invDst` preserve `LicmStateRel invDst`. -/
theorem evalStmt_licm_sim {invDst : RegId} {stS stT : AnState}
    (hrel : LicmStateRel invDst stS stT) (stmt : AnStmt)
    (havoid : stmtAvoidsReg invDst stmt = true) :
    LicmStateRel invDst (evalStmt stS stmt) (evalStmt stT stmt) := by
  by_cases htrap : stS.trapped = true
  · have htrapT := Eq.trans hrel.trapped_eq htrap
    rw [evalStmt_trapped htrap, evalStmt_trapped htrapT]
    exact hrel
  · have htrapF := Bool.eq_false_iff.mpr htrap
    have htrapTF := Eq.trans hrel.trapped_eq htrapF
    rw [evalStmt_untrapped htrapF, evalStmt_untrapped htrapTF]
    cases stmt with
    | nop =>
      exact hrel
    | const dst c =>
      unfold stmtAvoidsReg at havoid
      rw [Bool.not_eq_true', nat_beq_eq_false_iff_ne] at havoid
      dsimp only [evalStmtCore]
      exact licmStateRel_update_other havoid hrel (.val c)
    | mov dst src =>
      unfold stmtAvoidsReg at havoid
      simp only [Bool.and_eq_true, Bool.not_eq_true',
        nat_beq_eq_false_iff_ne] at havoid
      dsimp only [evalStmtCore]
      rw [hrel.regs_eq src havoid.2]
      exact licmStateRel_update_other havoid.1 hrel (stS.regs src)
    | freeze dst src =>
      unfold stmtAvoidsReg at havoid
      simp only [Bool.and_eq_true, Bool.not_eq_true',
        nat_beq_eq_false_iff_ne] at havoid
      dsimp only [evalStmtCore]
      rw [hrel.regs_eq src havoid.2]
      exact licmStateRel_update_other havoid.1 hrel _
    | binop dst op lhs rhs =>
      unfold stmtAvoidsReg at havoid
      simp only [Bool.and_eq_true, Bool.not_eq_true',
        nat_beq_eq_false_iff_ne] at havoid
      dsimp only [evalStmtCore]
      rw [evalOperand_avoid_eq havoid.1.2 hrel.regs_eq,
          evalOperand_avoid_eq havoid.2 hrel.regs_eq]
      split
      · exact ⟨rfl, hrel.stack_eq, hrel.heap_eq, hrel.regs_eq⟩
      · exact licmStateRel_update_other havoid.1.1 hrel _
    | stackStore alloc off sz src =>
      unfold stmtAvoidsReg at havoid
      dsimp only [evalStmtCore]
      rw [evalOperand_avoid_eq havoid hrel.regs_eq, hrel.stack_eq]
      exact ⟨hrel.trapped_eq, rfl, hrel.heap_eq, hrel.regs_eq⟩
    | stackLoad dst alloc off sz =>
      unfold stmtAvoidsReg at havoid
      rw [Bool.not_eq_true', nat_beq_eq_false_iff_ne] at havoid
      dsimp only [evalStmtCore]
      have hval : stT.stack alloc off = stS.stack alloc off := by
        rw [hrel.stack_eq]
      rw [hval]
      exact licmStateRel_update_other havoid hrel (stS.stack alloc off)
    | escapeStackAddr dst alloc =>
      unfold stmtAvoidsReg at havoid
      rw [Bool.not_eq_true', nat_beq_eq_false_iff_ne] at havoid
      dsimp only [evalStmtCore]
      exact licmStateRel_update_other havoid hrel (.val alloc)
    | heapStore _ _ alloc off src =>
      unfold stmtAvoidsReg at havoid
      dsimp only [evalStmtCore]
      rw [evalOperand_avoid_eq havoid hrel.regs_eq]
      cases evalOperand stS.regs src with
      | val v =>
        exact ⟨hrel.trapped_eq, hrel.stack_eq,
               by dsimp only; rw [hrel.heap_eq], hrel.regs_eq⟩
      | poison =>
        exact ⟨rfl, hrel.stack_eq, hrel.heap_eq, hrel.regs_eq⟩
    | heapLoad _ dst alloc off =>
      unfold stmtAvoidsReg at havoid
      rw [Bool.not_eq_true', nat_beq_eq_false_iff_ne] at havoid
      dsimp only [evalStmtCore]
      have hval : stT.heap alloc off = stS.heap alloc off := by
        rw [hrel.heap_eq]
      rw [hval]
      exact licmStateRel_update_other havoid hrel (.val (stS.heap alloc off))

theorem evalStmts_licm_sim {invDst : RegId} {stS stT : AnState}
    (hrel : LicmStateRel invDst stS stT) (stmts : List AnStmt)
    (havoid : stmtsAvoidReg invDst stmts = true) :
    LicmStateRel invDst (evalStmts stS stmts) (evalStmts stT stmts) := by
  induction stmts generalizing stS stT with
  | nil => exact hrel
  | cons hd tl ih =>
    unfold stmtsAvoidReg at havoid
    rw [Bool.and_eq_true] at havoid
    exact ih (evalStmt_licm_sim hrel hd havoid.1) havoid.2

/-- Main soundness theorem for Pass 4 (`ScevIndVarAndLicmCertChecker`):
whenever `checkScevLicm s t cert = true`, `t` productively compiles `s`. -/
theorem checkScevLicm_sound {s t : AnLLVMProg} {cert : ScevLicmCert}
    (h : checkScevLicm s t cert = true) :
    Trusted.ProductiveCompiles
      AnLLVMLang AnLLVMLang (Trusted.BehaviorCodec.id AnLLVMLang) s t := by
  unfold checkScevLicm at h
  simp only [Bool.and_eq_true, Bool.not_eq_true',
    nat_beq_eq_false_iff_ne, decide_eq_true_eq] at h
  rcases h with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hhas, _ht_has⟩, hsafe⟩, hne_acc⟩, hlhs_acc⟩,
      hrhs_acc⟩, hlhs_inv⟩, hrhs_inv⟩, hne_ret⟩, hepi_avoid⟩,
      hidx⟩, ht_loop⟩, ht_pre⟩, ht_epi⟩, ht_ret⟩, ht_alloc⟩, ht_off⟩
  apply productiveCompiles_of_extractObs_eq
  intro q out hs
  let st₀ := initAnState q
  let stS₁ := evalStmts st₀ s.preheader
  let stT₁ := evalStmt stS₁ (.binop s.loop.invDst s.loop.invOp s.loop.invLhs s.loop.invRhs)
  have hpre_eq : evalStmts st₀ t.preheader = stT₁ := by
    rw [ht_pre, evalStmts_append]
    rfl
  have hinv₁ : LicmLoopInv s.loop stS₁ stT₁ :=
    licm_preheader_post s.loop hsafe stS₁
  have hloop_T :
      evalLoop t.loop q.tripCount stT₁ =
        runLoopMul t.loop cert.base cert.stride q.tripCount 0 stT₁ := by
    unfold evalLoop
    rw [ht_loop]
    dsimp only
    have hmul :=
      runLoopAddRec_eq_runLoopMul
        { s.loop with
          hasInLoopInv := false
          idxMode := .scevAddRec cert.base cert.stride }
        cert.base cert.stride q.tripCount 0 stT₁
    simp only [Nat.zero_mul, Nat.add_zero] at hmul
    exact hmul
  have hloop_S :
      evalLoop s.loop q.tripCount stS₁ =
        runLoopMul s.loop cert.base cert.stride q.tripCount 0 stS₁ := by
    unfold evalLoop
    rw [hidx]
  have hinv₂ :
      LicmLoopInv s.loop
        (evalLoop s.loop q.tripCount stS₁)
        (evalLoop t.loop q.tripCount stT₁) := by
    rw [hloop_S, hloop_T]
    exact runLoopMul_licm_inv s.loop t.loop hhas
      (by rw [ht_loop])
      (by rw [ht_loop])
      (by rw [ht_loop])
      hsafe hne_acc hlhs_acc hrhs_acc hlhs_inv hrhs_inv
      cert.base cert.stride q.tripCount 0 hinv₁
  have hrel₃ :
      LicmStateRel s.loop.invDst
        (evalProg s q)
        (evalProg t q) := by
    change
      LicmStateRel s.loop.invDst
        (evalStmts (evalLoop s.loop q.tripCount stS₁) s.epilogue)
        (evalStmts (evalLoop t.loop q.tripCount (evalStmts st₀ t.preheader)) t.epilogue)
    rw [hpre_eq, ht_epi]
    exact evalStmts_licm_sim hinv₂.rel s.epilogue hepi_avoid
  unfold extractObs at hs ⊢
  rw [ht_ret, ht_alloc, ht_off,
      hrel₃.trapped_eq, hrel₃.heap_eq,
      hrel₃.regs_eq s.retReg (Ne.symm hne_ret)]
  exact hs

/-- `BB-8` `CertChecker` bundle for Pass 4 (`ScevIndVarAndLicmCertChecker`). -/
def ScevIndVarAndLicmCertChecker :
    BB8.CertChecker AnLLVMLang AnLLVMLang
      (Trusted.BehaviorCodec.id AnLLVMLang) ScevLicmCert where
  check       := checkScevLicm
  check_sound := checkScevLicm_sound

/-- Negative Canary 4A: `checkScevLicm` rejects an affine recurrence certificate
whose additive step `8` disagrees with the loop multiplication stride `4`. -/
theorem canary_scev_wrong_step_rejected :
    let s : AnLLVMProg := {
      preheader := []
      loop := {
        hasInLoopInv := true
        invDst       := 9
        invOp        := .add
        invLhs       := .reg 0
        invRhs       := .const 1
        idxMode      := .mulRecurrence 10 4
        accDst       := 3
      }
      epilogue  := []
      retReg    := 3
      obsAlloc  := 1
      obsOff    := 0
    }
    let t : AnLLVMProg := {
      s with
      preheader := [.binop 9 .add (.reg 0) (.const 1)]
      loop := {
        s.loop with
        hasInLoopInv := false
        idxMode      := .scevAddRec 10 8
      }
    }
    checkScevLicm s t { base := 10, stride := 8 } = false :=
  rfl

/-- Negative Canary 4B: `checkScevLicm` rejects hoisting a potentially trapping
division (`BinOp.udiv`, `isSafeToSpeculate = false`) out of a loop. -/
theorem canary_licm_trapping_div_rejected :
    let s : AnLLVMProg := {
      preheader := []
      loop := {
        hasInLoopInv := true
        invDst       := 9
        invOp        := .udiv
        invLhs       := .reg 0
        invRhs       := .const 0
        idxMode      := .mulRecurrence 0 4
        accDst       := 3
      }
      epilogue  := []
      retReg    := 3
      obsAlloc  := 1
      obsOff    := 0
    }
    let t : AnLLVMProg := {
      s with
      preheader := [.binop 9 .udiv (.reg 0) (.const 0)]
      loop := {
        s.loop with
        hasInLoopInv := false
        idxMode      := .scevAddRec 0 4
      }
    }
    checkScevLicm s t { base := 0, stride := 4 } = false :=
  rfl

/-- Negative Canary 4C: Semantic proof that hoisting `udiv r0 0` into the
preheader introduces immediate Undefined Behavior on a 0-trip loop
(`tripCount = 0`), whereas the unhoisted loop returns `some (0, 0)`. -/
theorem canary_licm_trapping_div_on_zero_trip_unsound :
    let q : AnQuery := { arg0 := 42, arg1 := 0, tripCount := 0 }
    let s : AnLLVMProg := {
      preheader := []
      loop := {
        hasInLoopInv := true
        invDst       := 9
        invOp        := .udiv
        invLhs       := .reg 0
        invRhs       := .const 0
        idxMode      := .mulRecurrence 0 4
        accDst       := 3
      }
      epilogue  := []
      retReg    := 3
      obsAlloc  := 1
      obsOff    := 0
    }
    let t : AnLLVMProg := {
      s with
      preheader := [.binop 9 .udiv (.reg 0) (.const 0)]
      loop := {
        s.loop with
        hasInLoopInv := false
        idxMode      := .scevAddRec 0 4
      }
    }
    extractObs s (evalProg s q) = some (0, 0) ∧
    extractObs t (evalProg t q) = none := by
  decide

-- ============================================================================
-- Section 7: End-to-End Composed AnLLVM -O2 Core Pipeline (BB-8 Composition)
-- ============================================================================

/-!
### End-to-End Composed Pipeline (`anllvmO2CorePipeline`)

We now compose all four verified passes via `BB8.PassCompiler.compId`:
1. **Stage 1 (`SroaAndMem2RegCertChecker`):** Promotes aggregate stack slices
   `[0, 4)` and `[4, 8)` of `alloc 0` into SSA registers `r4` and `r5`.
2. **Stage 2 (`InstCombineBdcePassCompiler`):** Applies demanded-bits `BDCE`
   (`(r11 | 16) & 15 ↦ r11 & 15` since `16 &&& 15 = 0`), freeze-guarded
   self-subtraction (`freeze r10 r7 ;; r10 := r10 - r10 ↦ r10 := 0`), and
   algebraic simplification (`r7 := r7 + 0 ↦ mov r7 r7`).
3. **Stage 3 (`MemorySsaGvnDseCertChecker`):** Eliminates an overwritten dead
   store to heap `(alloc 1, off 0)` across an intervening non-aliasing store to
   `(alloc 1, off 8)` (`DSE`) and forwards the live store into `r8` (`NewGVN`).
4. **Stage 4 (`ScevIndVarAndLicmCertChecker`):** Hoists the loop-invariant
   computation `r9 := r6 + r8` out of the loop into the preheader (`LICM`) and
   strength-reduces the loop index `10 + i * 4` into the additive recurrence
   `{10, +, 4}` (`IndVarSimplify / SCEV`).
-/

/-- Stage 0 (Source `AnLLVMProg` emitted by unoptimized MIR lowering):
Contains stack `alloca` stores/loads on two fields `[0, 4)` and `[4, 8)` of
`alloc 0`, redundant bitwise-OR masked by `15`, freeze-guarded self-cancel,
overwritten heap store across a non-aliasing store, redundant heap load, and a
loop with an invariant `add` and affine multiplication `10 + i * 4`. -/
def benchmarkKernelSrc : AnLLVMProg where
  preheader :=
    [ .stackStore 0 0 4 (.reg 0)
    , .stackStore 0 4 4 (.reg 1)
    , .stackLoad 11 0 0 4
    , .stackLoad 7 0 4 4
    , .binop 6 .bitOr (.reg 11) (.const 16)
    , .binop 6 .bitAnd (.reg 6) (.const 15)
    , .freeze 10 7
    , .binop 10 .sub (.reg 10) (.reg 10)
    , .binop 7 .add (.reg 7) (.const 0)
    , .heapStore 1 0 1 0 (.const 100)
    , .heapStore 2 1 1 8 (.const 200)
    , .heapStore 3 2 1 0 (.const 300)
    , .heapLoad 3 8 1 0 ]
  loop := {
    hasInLoopInv := true
    invDst       := 9
    invOp        := .add
    invLhs       := .reg 6
    invRhs       := .reg 8
    idxMode      := .mulRecurrence 10 4
    accDst       := 3
  }
  epilogue :=
    [ .binop 3 .add (.reg 3) (.reg 7) ]
  retReg   := 3
  obsAlloc := 1
  obsOff   := 0

/-- Certificate for Stage 1 (`SROA + PromoteMemToReg`): promotes `[0, 4)` to
`r4` and `[4, 8)` to `r5`. -/
def benchmarkSroaCert : SroaMem2RegCert where
  slices :=
    [ { alloc := 0, off := 0, sz := 4, ssaReg := 4 }
    , { alloc := 0, off := 4, sz := 4, ssaReg := 5 } ]

/-- Stage 1 output (`afterSroaProg`): all stack `alloca` operations replaced by
register moves on `r4` and `r5`. -/
def afterSroaProg : AnLLVMProg where
  preheader :=
    [ .mov 4 0
    , .mov 5 1
    , .mov 11 4
    , .mov 7 5
    , .binop 6 .bitOr (.reg 11) (.const 16)
    , .binop 6 .bitAnd (.reg 6) (.const 15)
    , .freeze 10 7
    , .binop 10 .sub (.reg 10) (.reg 10)
    , .binop 7 .add (.reg 7) (.const 0)
    , .heapStore 1 0 1 0 (.const 100)
    , .heapStore 2 1 1 8 (.const 200)
    , .heapStore 3 2 1 0 (.const 300)
    , .heapLoad 3 8 1 0 ]
  loop     := benchmarkKernelSrc.loop
  epilogue := benchmarkKernelSrc.epilogue
  retReg   := 3
  obsAlloc := 1
  obsOff   := 0

/-- Stage 2 output (`afterInstCombineProg`): demanded-bits `BDCE` simplifies
`r6 := r11 | 16 ;; r6 := r6 & 15 ↦ r6 := r11 & 15`, `freeze + sub` simplifies
to `const 10 0`, and `r7 + 0` simplifies to `mov 7 7`. -/
def afterInstCombineProg : AnLLVMProg :=
  passInstCombineBdce afterSroaProg

/-- Stage 3 output (`afterGvnDseProg`): `DSE` eliminates the dead store
`heapStore 1 0 1 0 (.const 100)` across the non-aliasing store to `(1, 8)`, and
`NewGVN` forwards `300` into `r8`. -/
def afterGvnDseProg : AnLLVMProg where
  preheader :=
    [ .mov 4 0
    , .mov 5 1
    , .mov 11 4
    , .mov 7 5
    , .binop 6 .bitAnd (.reg 11) (.const 15)
    , .const 10 0
    , .mov 7 7
    , .heapStore 2 1 1 8 (.const 200)
    , .heapStore 3 2 1 0 (.const 300)
    , .const 8 300 ]
  loop     := benchmarkKernelSrc.loop
  epilogue := benchmarkKernelSrc.epilogue
  retReg   := 3
  obsAlloc := 1
  obsOff   := 0

/-- Stage 4 output (`benchmarkKernelOpt`): `LICM` hoists `r9 := r6 + r8` into
`preheader` and `IndVarSimplify / SCEV` replaces `10 + i * 4` with `{10, +, 4}`. -/
def benchmarkKernelOpt : AnLLVMProg where
  preheader :=
    afterGvnDseProg.preheader ++
      [ .binop 9 .add (.reg 6) (.reg 8) ]
  loop := {
    benchmarkKernelSrc.loop with
    hasInLoopInv := false
    idxMode      := .scevAddRec 10 4
  }
  epilogue := afterGvnDseProg.epilogue
  retReg   := 3
  obsAlloc := 1
  obsOff   := 0

/-- Stage 1 `PassCompiler` instance (`SROA + PromoteMemToReg`). -/
def sroaPassCompiler :
    BB8.PassCompiler AnLLVMLang AnLLVMLang
      (Trusted.BehaviorCodec.id AnLLVMLang) :=
  SroaAndMem2RegCertChecker.toPassCompiler
    (fun _ => (afterSroaProg, benchmarkSroaCert))

/-- Stage 3 `PassCompiler` instance (`MemorySSA GVN + DSE`). -/
def gvnDsePassCompiler :
    BB8.PassCompiler AnLLVMLang AnLLVMLang
      (Trusted.BehaviorCodec.id AnLLVMLang) :=
  MemorySsaGvnDseCertChecker.toPassCompiler
    (fun _ => (afterGvnDseProg, { memSsaVerified := true }))

/-- Stage 4 `PassCompiler` instance (`SCEV IndVarSimplify + LICM`). -/
def scevLicmPassCompiler :
    BB8.PassCompiler AnLLVMLang AnLLVMLang
      (Trusted.BehaviorCodec.id AnLLVMLang) :=
  ScevIndVarAndLicmCertChecker.toPassCompiler
    (fun _ => (benchmarkKernelOpt, { base := 10, stride := 4 }))

/-- End-to-end 4-stage `AnLLVM` `-O2` core optimization pipeline composed via
`BB8.PassCompiler.compId`. -/
def anllvmO2CorePipeline :
    BB8.PassCompiler AnLLVMLang AnLLVMLang
      (Trusted.BehaviorCodec.id AnLLVMLang) :=
  ((sroaPassCompiler.compId InstCombineBdcePassCompiler).compId
    gvnDsePassCompiler).compId scevLicmPassCompiler

/-- Verification that `anllvmO2CorePipeline.run benchmarkKernelSrc` succeeds and
emits `some benchmarkKernelOpt` via pure kernel WHNF reduction. -/
theorem anllvmO2CorePipeline_runs :
    anllvmO2CorePipeline.run benchmarkKernelSrc = some benchmarkKernelOpt :=
  rfl

/-- Master end-to-end theorem: `benchmarkKernelOpt` productively compiles
`benchmarkKernelSrc` across all four composed `AnLLVM` middle-end passes
(`SROA + Mem2Reg`, `InstCombine + BDCE`, `MemorySSA GVN + DSE`, and
`SCEV IndVarSimplify + LICM`). -/
theorem anllvmO2CorePipeline_verified :
    Trusted.ProductiveCompiles
      AnLLVMLang AnLLVMLang (Trusted.BehaviorCodec.id AnLLVMLang)
      benchmarkKernelSrc benchmarkKernelOpt :=
  anllvmO2CorePipeline.run_sound anllvmO2CorePipeline_runs

-- ============================================================================
-- Section 8: Axiom Hygiene Audit (#guard_msgs in #print axioms)
-- ============================================================================

/-- info: 'AnLLVMMiddleEndProbe.checkTwoSlicesDisjoint_offsets_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkTwoSlicesDisjoint_offsets_ne

/-- info: 'AnLLVMMiddleEndProbe.checkSroaMem2Reg_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkSroaMem2Reg_sound

/-- info: 'AnLLVMMiddleEndProbe.nat_or_and_demanded_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nat_or_and_demanded_eq

/-- info: 'AnLLVMMiddleEndProbe.instCombineBdce_productiveCompiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms instCombineBdce_productiveCompiles

/-- info: 'AnLLVMMiddleEndProbe.updateHeap_dse_across_noalias' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms updateHeap_dse_across_noalias

/-- info: 'AnLLVMMiddleEndProbe.checkMemSsaGvnDse_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkMemSsaGvnDse_sound

/-- info: 'AnLLVMMiddleEndProbe.scev_affine_recurrence_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms scev_affine_recurrence_eq

/-- info: 'AnLLVMMiddleEndProbe.runLoopAddRec_eq_runLoopMul' depends on axioms: [propext] -/
#guard_msgs in
#print axioms runLoopAddRec_eq_runLoopMul

/-- info: 'AnLLVMMiddleEndProbe.checkScevLicm_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms checkScevLicm_sound

/-- info: 'AnLLVMMiddleEndProbe.anllvmO2CorePipeline_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms anllvmO2CorePipeline_verified

end AnLLVMMiddleEndProbe

