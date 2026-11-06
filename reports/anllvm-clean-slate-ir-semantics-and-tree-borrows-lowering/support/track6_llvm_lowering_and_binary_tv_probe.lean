-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Track 6 Probe: Verified LLVM IR Lowering (`AnLLVM`), Directional Peephole Refinement, and `seL4` `GraphLang` Binary Translation Validation

Standalone Lean 4.34.1 mechanization for Round 1 Track 6:
1. **Anneal Layer 1A & Layer 1B Refinement Core (`Trusted` & `Anneal`):**
   Exact mechanization of `Preorder`, `Partial`, `Behavior`, `Language`,
   `Compiles`, `Abstracts`, `Compiler`, `Compiler.SoundOn`, `Compiler.Verified`,
   `pass_trans`, and `Compiles.comp` from `trusted/lean/Trusted/Refinement.lean`
   and `theory/Anneal/Refinement.lean` (commit `e75556f57`).
2. **`AnLLVM` Dialect Semantics (`PoisonOr (BitVec 64)`, `freeze`, `gepInbounds`,
   `load`/`store` with `noundef`/`!range`, and `noalias`):**
   Models deferred UB (`PoisonOr`) vs. immediate UB (`Partial.ub`), proves a
   formal counterexample (`leanMLIR_freeze_unsound_canary`) showing why
   `opencompl/lean-mlir`'s deterministic `freeze poison = value 0`
   (`LeanMLIR/Dialects/LLVM/Semantics.lean:636-640`) is unsound for target
   refinement when hardware registers hold non-zero bitpatterns, and proves
   soundness of nondeterministic `freezeSem` (`Vellvm` `Freeze.v:32-111` /
   `Alive2` `ir/instr.cpp:3203-3207`).
3. **Axiom-Clean Directional Peephole / Instruction-Lowering Pass Driver
   (`DirectionalRewriteRefine`):**
   Replaces `opencompl/lean-mlir`'s `toPeepholeUNSOUND` (`axiom
   refinement_correctness {p : Prop} : p` in
   `SSA/Projects/LLVMRiscV/PeepholeRefine.lean:33-53`) with a monotone
   directional rewrite pass that lifts `PoisonOr.IsRefinedBy` directly into
   `Trusted.Compiles` and `Trusted.Compiler.Verified` with zero custom axioms.
4. **Verified `MonoMIR` to `AnLLVM` Lowering (`mirToAnLLVM_verified`) and
   Negative Miscompilation Canaries:**
   - Proves soundness of lowering `MaybeUninit` / `PassMode::Cast` uninitialized
     padding loads when `noundef` and `!range` are omitted and guarded by
     `freeze`, paired with `canary_uninit_noundef_refutes_compiles` proving
     that attaching `noundef` to a potentially uninitialized load refutes
     `Compiles`.
   - Proves soundness of lowering `&mut T` parameters when `noalias` is gated on
     `T: Unpin` (`rustc_middle/src/ty/layout.rs:1165`,
     `rustc_codegen_ssa/src/mir/retag.rs:208`), paired with
     `canary_self_referential_noalias_refutes_compiles` proving that attaching
     `noalias` to a self-referential `!Unpin` reference allows load-forwarding
     across an internal alias store that refutes `Compiles`.
5. **seL4 `GraphLang`-Style Binary Translation Validator
   (`checkBinaryGraphRefine`) and End-to-End Composition:**
   Formalizes cut-point `Split` validation (`seL4/graph-refine/check.py:154-355,
   512-565`) over loop headers, proves `checkBinaryGraphRefine_sound`, exhibits
   a negative canary showing why $2\times$ loop unrolling breaks $1:1$ cut-point
   matching without step-ratio scaling, and composes `MonoMIR` $\to$ `AnLLVM`
   $\to$ `MachineCode` via `Compiles.comp` and `pass_trans`.
-/

namespace Track6LlvmLoweringAndBinaryTvProbe

/-! ============================================================================
    SECTION 1: ANNEAL LAYER 1A & LAYER 1B REFINEMENT CORE
    (`trusted/lean/Trusted/Refinement.lean` & `theory/Anneal/Refinement.lean`)
    ============================================================================ -/

namespace Trusted

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder in which
    stronger propositions refine weaker ones. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces `A → B` with a
    refinement preorder whenever the codomain `B` is a `Preorder`. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- A partially defined value of type `B`, constructively representing
    $B \cup \{\mathsf{UB}\}$:
    - `defined : Prop` records whether the behavior is free of UB.
    - `val : defined → B` yields the underlying value in `B` when `defined`. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- The undefined element ($\mathsf{UB}$) of `Partial B` (`defined := False`),
    which acts as the top element under `instPreorderPartial`. -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Map a function `f : B₁ → B₂` over the defined payload of a `Partial B₁`. -/
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/-- Refinement preorder on `Partial B`: `p₁ ≤ p₂` holds when, whenever `p₂` is
    defined, `p₁` is also defined and `p₁.val h₁ ≤ p₂.val h₂`. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Order-preserving mapping between behavior preorders. -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- Canonical domain of query-indexed partial behaviors over `Query` and `Out`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A language bundling `Prog`, `Query`, `Out`, and `sem`. -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

/-- Behavior domain of a `Language`. -/
abbrev Language.Behavior (L : Language) : Type :=
  Trusted.Behavior L.Query L.Out

/-- Query-indexed specification on `L` with precondition `pre` and
    postcondition `post`. -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Unconditional specification on `L`. -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness specification on `L`. -/
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness specification on `L`. -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Compilation (refinement) pass from `L_src` to `L_tgt`. -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Verification (abstraction) pass from `L_src` to verifier language `L_v`. -/
abbrev Abstracts (L_v L_src : Language)
    (π_v : L_v.Behavior → L_src.Behavior)
    (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ π_v (L_v.sem v)

/-- A compiler lowering programs from `L_src` to `L_tgt` with behavior mapping
    `π : L_src.Behavior → L_tgt.Behavior`. -/
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Soundness of compiler `C` on an individual source program `s`. -/
def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

/-- End-to-end verification obligation for source program `s` and specification
    `spec` under compiler `C`. -/
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

end Trusted

namespace Anneal

open Trusted

/-- The identity behavior mapping is monotone. -/
theorem monotone_id {B : Type u} [Preorder B] : Monotone (id : B → B) :=
  fun _ _ h => h

/-- Composition of two monotone mappings is monotone. -/
theorem monotone_comp
    {B₁ : Type u} {B₂ : Type v} {B₃ : Type w}
    [Preorder B₁] [Preorder B₂] [Preorder B₃]
    {π₂ : B₂ → B₃} {π₁ : B₁ → B₂}
    (h₂ : Monotone π₂) (h₁ : Monotone π₁) :
    Monotone (fun b => π₂ (π₁ b)) :=
  fun _ _ h => h₂ (h₁ h)

/-- Transitive composition of two pass refinements (`Compiles` or `Abstracts`). -/
theorem pass_trans
    {B₁ : Type u} {B₂ : Type v} {B₃ : Type w}
    [Preorder B₁] [Preorder B₂] [Preorder B₃]
    {π₂ : B₁ → B₂} {π₁ : B₂ → B₃}
    (h_mono₁ : Monotone π₁)
    {b₁ : B₁} {b₂ : B₂} {b₃ : B₃}
    (h₂₃ : b₃ ≤ π₁ b₂)
    (h₁₂ : b₂ ≤ π₂ b₁) :
    b₃ ≤ π₁ (π₂ b₁) :=
  Preorder.le_trans h₂₃ (h_mono₁ h₁₂)

/-- Pipeline-ordered composition of two compilation passes. -/
theorem Compiles.comp
    {L₁ L₂ L₃ : Language}
    {π₁ : L₁.Behavior → L₂.Behavior} {π₂ : L₂.Behavior → L₃.Behavior}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ π₁ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ π₂ p₂ p₃)
    (h_mono₂ : Monotone π₂) :
    Compiles L₁ L₃ (fun b => π₂ (π₁ b)) p₁ p₃ :=
  pass_trans h_mono₂ h₂₃ h₁₂

/-- Discharge `C.Verified s spec` directly from compiler soundness on `s`
    (`C.SoundOn s`) and a source-level refinement proof (`L_src.sem s ≤ spec`). -/
theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_comp.2, Preorder.le_trans h_comp.2 (h_comp.1 h_src)⟩

/-- Compose two `Compiler` stages into a single pipeline `Compiler`. -/
def compCompilers {L₁ L₂ L₃ : Language}
    (C₁ : Compiler L₁ L₂) (C₂ : Compiler L₂ L₃) : Compiler L₁ L₃ where
  compile s := C₂.compile (C₁.compile s)
  π b := C₂.π (C₁.π b)

/-- If `C₁` is sound on `s` and `C₂` is sound on `C₁.compile s`, then
    `compCompilers C₁ C₂` is sound on `s`. -/
theorem Compiler.SoundOn.comp {L₁ L₂ L₃ : Language}
    {C₁ : Compiler L₁ L₂} {C₂ : Compiler L₂ L₃} {s : L₁.Prog}
    (h₁ : C₁.SoundOn s) (h₂ : C₂.SoundOn (C₁.compile s)) :
    (compCompilers C₁ C₂).SoundOn s :=
  ⟨fun _ _ h => h₂.1 (h₁.1 h), pass_trans h₂.1 h₂.2 h₁.2⟩

end Anneal

open Trusted Anneal

/-! ============================================================================
    SECTION 2: `AnLLVM` DIALECT SEMANTICS
    (`PoisonOr (BitVec 64)`, `freeze`, `gepInbounds`, `load`/`store` with
     `noundef`/`!range` metadata, and `noalias`)
    ============================================================================ -/

/-- Value-level deferred undefined behavior (`poison`), matching
    `opencompl/lean-mlir`'s `PoisonOr α` (`LeanMLIR/Util/Poison.lean:24-26`)
    and `Vellvm`'s `DVALUE_Poison` (`DynamicValues.v:214`). -/
inductive PoisonOr (α : Type) : Type where
  | poison : PoisonOr α
  | value (a : α) : PoisonOr α
  deriving DecidableEq

namespace PoisonOr

/-- `src.IsRefinedBy tgt` (`src ⊑ₒ tgt` in `opencompl/lean-mlir`,
    `LeanMLIR/Util/Poison.lean:105-108`) holds when `tgt` is at least as
    defined as `src`: `poison` is refined by any value, whereas `value a` is
    refined only by `value a`. -/
def IsRefinedBy (src tgt : PoisonOr α) : Prop :=
  match src with
  | .poison  => True
  | .value a => tgt = .value a

theorem isRefinedBy_refl (x : PoisonOr α) : IsRefinedBy x x := by
  cases x <;> first | trivial | rfl

theorem isRefinedBy_trans {x y z : PoisonOr α}
    (hxy : IsRefinedBy x y) (hyz : IsRefinedBy y z) : IsRefinedBy x z := by
  cases x with
  | poison => trivial
  | value a =>
    change y = .value a at hxy
    subst hxy
    exact hyz

/-- `IsRefinedBy` is directional (not symmetric): `.poison` is refined by
    `.value 0`, but `.value 0` is NOT refined by `.poison`. This asymmetry is
    why `opencompl/lean-mlir`'s symmetric `PeepholeRewrite` (`lhs.denote =
    rhs.denote`) cannot express poison-eliminating rewrites without an unsound
    axiom (`toPeepholeUNSOUND`). -/
theorem isRefinedBy_not_symm :
    IsRefinedBy (.poison : PoisonOr (BitVec 64)) (.value 0#64) ∧
    ¬ IsRefinedBy (.value 0#64) (.poison : PoisonOr (BitVec 64)) := by
  refine ⟨trivial, ?_⟩
  intro h
  nomatch h

/-- Monadic bind propagating `poison` (`LeanMLIR/Util/Poison.lean:36-39`). -/
def bind (x : PoisonOr α) (f : α → PoisonOr β) : PoisonOr β :=
  match x with
  | .poison  => .poison
  | .value a => f a

/-- Embed a `PoisonOr α` value at an observable boundary where `poison` triggers
    immediate UB (`Partial.ub`), matching `noundef` or branch-on-poison. -/
def toObservablePartial (x : PoisonOr α) : Partial (α → Prop) :=
  match x with
  | .poison  => Partial.ub
  | .value a => Partial.pure (fun out => out = a)

/-- Order-reversal correspondence between `PoisonOr.IsRefinedBy` (`src ⊑ₒ tgt`)
    and Anneal's `Partial` refinement preorder (`tgt ≤ src`): `src` is refined
    by `tgt` if and only if `toObservablePartial tgt ≤ toObservablePartial src`. -/
theorem isRefinedBy_iff_toObservablePartial_le (src tgt : PoisonOr α) :
    IsRefinedBy src tgt ↔ toObservablePartial tgt ≤ toObservablePartial src := by
  cases src with
  | poison =>
    constructor
    · intro _ h_def
      exact False.elim h_def
    · intro _
      trivial
  | value a =>
    cases tgt with
    | poison =>
      constructor
      · intro h
        nomatch h
      · intro h_le
        obtain ⟨h_def, _⟩ := h_le True.intro
        exact False.elim h_def
    | value b =>
      constructor
      · intro h_eq
        injection h_eq with h_ab
        subst h_ab
        exact Preorder.le_refl _
      · intro h_le
        obtain ⟨_, h_sub⟩ := h_le True.intro
        have h_ba : b = a := h_sub b rfl
        subst h_ba
        rfl

end PoisonOr

/-- `AnLLVM` 64-bit integer / pointer word (`PoisonOr (BitVec 64)`). -/
abbrev AnWord := PoisonOr (BitVec 64)

/-- `opencompl/lean-mlir`'s deterministic `freeze` definition
    (`LeanMLIR/Dialects/LLVM/Semantics.lean:636-640`), which collapses `.poison`
    to `.value 0#64`. -/
def freezeLeanMLIR (x : AnWord) : AnWord :=
  match x with
  | .poison  => .value 0#64
  | .value a => .value a

/-- Nondeterministic `freeze` semantics in `AnLLVM` (matching `Vellvm`
    `src/rocq/Semantics/Operations/Freeze.v:32-111` `draw_int` and `Alive2`
    `ir/instr.cpp:3203-3207` `State::freeze`): freezing `.poison` is well-defined
    (`defined := True`) and permits *any* concrete 64-bit bitvector outcome,
    whereas freezing `.value a` deterministically yields `a`. -/
def freezeSem (x : AnWord) : Partial (BitVec 64 → Prop) :=
  Partial.pure (fun out =>
    match x with
    | .poison  => True
    | .value a => out = a)

/-- Canary demonstrating the unsoundness of `freezeLeanMLIR` for target
    compilation: when a hardware register holds a non-zero garbage value
    (such as `42#64`) for an uninitialized (`poison`) SSA value, `freezeLeanMLIR`
    requires the output to equal `0#64`, refuting target refinement
    (`¬ (Partial.pure (fun out => out = 42#64) ≤ ...)`). -/
theorem leanMLIR_freeze_unsound_canary :
    ¬ (Partial.pure (fun out : BitVec 64 => out = 42#64) ≤
       PoisonOr.toObservablePartial (freezeLeanMLIR .poison)) := by
  intro h_le
  obtain ⟨_, h_sub⟩ := h_le True.intro
  have h_eq : (42#64 : BitVec 64) = 0#64 := h_sub 42#64 rfl
  nomatch h_eq

/-- Soundness of `AnLLVM`'s nondeterministic `freezeSem`: for *every* concrete
    hardware bitvector `v : BitVec 64` that refines `x` (`x.IsRefinedBy (.value v)`),
    returning `v` refines `freezeSem x` (`Partial.pure (· = v) ≤ freezeSem x`). -/
theorem freezeSem_refines_any_bitvec (x : AnWord) (v : BitVec 64)
    (h_ref : PoisonOr.IsRefinedBy x (.value v)) :
    Partial.pure (fun out => out = v) ≤ freezeSem x := by
  intro _
  refine ⟨True.intro, ?_⟩
  intro out h_out
  subst h_out
  cases x with
  | poison => trivial
  | value a =>
    change PoisonOr.value out = PoisonOr.value a at h_ref
    injection h_ref

/-- `AnLLVM` `getelementptr inbounds` semantics (`Vellvm` `Gep.v:58-77`,
    `Alive2` `ir/instr.cpp:4256-4274`): given a base offset `base`, displacement
    `offset`, and allocation size `allocSize`, returns `.value (base + offset)`
    if `base` is non-poison and `base + offset ≤ allocSize` (unsigned without
    wrap), and `.poison` otherwise. -/
def gepInbounds (base : AnWord) (offset allocSize : BitVec 64) : AnWord :=
  PoisonOr.bind base (fun b =>
    if (b + offset).toNat == b.toNat + offset.toNat &&
       (b + offset).toNat <= allocSize.toNat then
      .value (b + offset)
    else
      .poison)

/-- Load metadata and parameter attribute descriptor for `AnLLVM` loads,
    corresponding to `rustc_codegen_llvm/src/builder.rs:730-865`
    (`load_operand`, `scalar_load_metadata`, `!noundef`, and `!range`). -/
structure LoadMeta where
  noundef : Bool
  range   : Option (BitVec 64 × BitVec 64)

/-- Check whether a concrete `BitVec 64` satisfies an optional half-open
    `!range !(lo, hi)` metadata bound (`lo ≤ x < hi`). -/
def inRangeMeta (v : BitVec 64) (rng : Option (BitVec 64 × BitVec 64)) : Bool :=
  match rng with
  | none          => true
  | some (lo, hi) => decide (lo.toNat ≤ v.toNat ∧ v.toNat < hi.toNat)

/-- `AnLLVM` load semantics with `!noundef` and `!range` metadata, matching
    `Vellvm`'s `load_metadata_attrs` (`src/rocq/Semantics/Denotation.v:255-282`)
    and `Alive2`'s `AssumeVal::execute` (`ir/instr.cpp:3757-3894`):
    - Loading `.poison` when `loadMeta.noundef = true` triggers immediate UB
      (`Partial.ub`).
    - Loading `.value x` outside `loadMeta.range` yields `.poison`, which in turn
      triggers immediate UB (`Partial.ub`) when `loadMeta.noundef = true`. -/
def evalLoadMeta (cell : AnWord) (loadMeta : LoadMeta) : Partial (AnWord → Prop) :=
  match cell with
  | .poison =>
    if loadMeta.noundef then
      Partial.ub
    else
      Partial.pure (fun out => out = .poison)
  | .value x =>
    if inRangeMeta x loadMeta.range then
      Partial.pure (fun out => out = .value x)
    else if loadMeta.noundef then
      Partial.ub
    else
      Partial.pure (fun out => out = .poison)

/-! ============================================================================
    SECTION 3: AXIOM-CLEAN DIRECTIONAL PEEPHOLE / INSTRUCTION-LOWERING DRIVER
    (Replacing `opencompl/lean-mlir`'s `toPeepholeUNSOUND` with `DirectionalRewriteRefine`)
    ============================================================================ -/

/-- Hybrid `AnLLVM + RV64` straight-line instruction set for the directional
    peephole and instruction-lowering driver. -/
inductive HybridOp where
  /-- `llvm.add %x, %y overflow<nsw>` (returns `.poison` on signed overflow). -/
  | llvmAddNsw (lhs rhs : BitVec 64)
  /-- `riscv.add %x, %y` (always returns wrapping `.value (lhs + rhs)`). -/
  | rv64Add (lhs rhs : BitVec 64)
  /-- `llvm.gep inbounds %base, %offset, %allocSize`. -/
  | llvmGepInbounds (base offset allocSize : BitVec 64)
  /-- `riscv.add %base, %offset` (lowered address computation). -/
  | rv64AddrAdd (base offset : BitVec 64)

/-- Evaluate a `HybridOp` given an accumulator input `acc : AnWord`. -/
def evalHybridOp (op : HybridOp) (acc : AnWord) : AnWord :=
  PoisonOr.bind acc (fun a =>
    match op with
    | .llvmAddNsw lhs rhs =>
      let sum := a + lhs + rhs
      -- Toy signed-bound check modeling `nsw` poison on overflow:
      if a.toNat + lhs.toNat + rhs.toNat < 2 ^ 63 then
        .value sum
      else
        .poison
    | .rv64Add lhs rhs =>
      .value (a + lhs + rhs)
    | .llvmGepInbounds base offset allocSize =>
      gepInbounds (.value (a + base)) offset allocSize
    | .rv64AddrAdd base offset =>
      .value (a + base + offset))

/-- Monotonicity of `evalHybridOp` with respect to `PoisonOr.IsRefinedBy`:
    if `acc₁ ⊑ₒ acc₂`, then `evalHybridOp op acc₁ ⊑ₒ evalHybridOp op acc₂`. -/
theorem evalHybridOp_mono (op : HybridOp) {acc₁ acc₂ : AnWord}
    (h_acc : PoisonOr.IsRefinedBy acc₁ acc₂) :
    PoisonOr.IsRefinedBy (evalHybridOp op acc₁) (evalHybridOp op acc₂) := by
  cases acc₁ with
  | poison => trivial
  | value a =>
    change acc₂ = .value a at h_acc
    subst h_acc
    exact PoisonOr.isRefinedBy_refl _

/-- Evaluate a sequence of `HybridOp` instructions starting from `acc`. -/
def evalHybridProg : List HybridOp → AnWord → AnWord
  | [], acc        => acc
  | op :: ops, acc => evalHybridProg ops (evalHybridOp op acc)

/-- Monotonicity of `evalHybridProg` with respect to initial accumulator
    refinement (`acc₁ ⊑ₒ acc₂`). -/
theorem evalHybridProg_mono (ops : List HybridOp) {acc₁ acc₂ : AnWord}
    (h_acc : PoisonOr.IsRefinedBy acc₁ acc₂) :
    PoisonOr.IsRefinedBy (evalHybridProg ops acc₁) (evalHybridProg ops acc₂) := by
  induction ops generalizing acc₁ acc₂ with
  | nil => exact h_acc
  | cons op rest ih =>
    exact ih (evalHybridOp_mono op h_acc)

/-- A directional single-instruction rewrite rule `lhs ↦ rhs` carrying a proof
    that `rhs` refines `lhs` (`PoisonOr.IsRefinedBy (evalHybridOp lhs acc)
    (evalHybridOp rhs acc)`) for every accumulator `acc`. -/
structure DirectionalRewriteRefine where
  lhs : HybridOp
  rhs : HybridOp
  refines : ∀ acc : AnWord,
    PoisonOr.IsRefinedBy (evalHybridOp lhs acc) (evalHybridOp rhs acc)

/-- Rewrite the instruction at index `idx` if it matches `rule.lhs`
    (simplified structural matcher modeled via an explicit replacement witness). -/
def rewriteHybridAt (rhs : HybridOp) : Nat → List HybridOp → List HybridOp
  | _, []            => []
  | 0, _ :: ops      => rhs :: ops
  | n + 1, op :: ops => op :: rewriteHybridAt rhs n ops

/-- Core congruence theorem for directional instruction rewriting: if a program
    `ops` has `rule.lhs` at position `idx`, replacing that instruction with
    `rule.rhs` refines the whole program (`evalHybridProg`) under
    `PoisonOr.IsRefinedBy`, with zero unsound axioms. -/
theorem evalHybridProg_rewrite_refines
    (rule : DirectionalRewriteRefine) :
    ∀ (prefixOps suffixOps : List HybridOp) (acc : AnWord),
      PoisonOr.IsRefinedBy
        (evalHybridProg (prefixOps ++ rule.lhs :: suffixOps) acc)
        (evalHybridProg (prefixOps ++ rule.rhs :: suffixOps) acc)
  | [], suffixOps, acc => by
    simp only [List.nil_append, evalHybridProg]
    exact evalHybridProg_mono suffixOps (rule.refines acc)
  | op :: rest, suffixOps, acc => by
    simp only [List.cons_append, evalHybridProg]
    exact evalHybridProg_rewrite_refines rule rest suffixOps (evalHybridOp op acc)

/-- `Language` packaging `List HybridOp` where observable outputs require
    non-poison results (`PoisonOr.toObservablePartial`). -/
def HybridDialectLang : Language where
  Prog  := List HybridOp
  Query := BitVec 64
  Out   := BitVec 64
  sem p q := PoisonOr.toObservablePartial (evalHybridProg p (.value q))

/-- Map every instruction in a `HybridDialectLang` program using a total
    instruction lowering function `lowerOp : HybridOp → HybridOp`. -/
def lowerHybridProg (lowerOp : HybridOp → HybridOp) : List HybridOp → List HybridOp
  | []        => []
  | op :: ops => lowerOp op :: lowerHybridProg lowerOp ops

/-- If `lowerOp` refines every single instruction (`evalHybridOp op acc ⊑ₒ
    evalHybridOp (lowerOp op) acc`), then `lowerHybridProg lowerOp` refines the
    entire program (`evalHybridProg`). -/
theorem evalHybridProg_lower_refines
    (lowerOp : HybridOp → HybridOp)
    (h_op : ∀ op acc,
      PoisonOr.IsRefinedBy (evalHybridOp op acc) (evalHybridOp (lowerOp op) acc)) :
    ∀ (ops : List HybridOp) (acc : AnWord),
      PoisonOr.IsRefinedBy
        (evalHybridProg ops acc)
        (evalHybridProg (lowerHybridProg lowerOp ops) acc)
  | [], acc => PoisonOr.isRefinedBy_refl acc
  | op :: ops, acc => by
    simp only [lowerHybridProg, evalHybridProg]
    have h_step := h_op op acc
    have h_mono := evalHybridProg_mono ops h_step
    have h_ih := evalHybridProg_lower_refines lowerOp h_op ops (evalHybridOp (lowerOp op) acc)
    exact PoisonOr.isRefinedBy_trans h_mono h_ih

/-- Concrete instruction-lowering function from `AnLLVM` (`llvmAddNsw`,
    `llvmGepInbounds`) to pure `RV64` (`rv64Add`, `rv64AddrAdd`). -/
def lowerAnLLVMOpToRv64 : HybridOp → HybridOp
  | .llvmAddNsw lhs rhs                  => .rv64Add lhs rhs
  | .rv64Add lhs rhs                     => .rv64Add lhs rhs
  | .llvmGepInbounds base offset _       => .rv64AddrAdd base offset
  | .rv64AddrAdd base offset             => .rv64AddrAdd base offset

/-- Pointwise directional refinement for `lowerAnLLVMOpToRv64`: both `llvm.add nsw`
    $\to$ `rv64.add` and `llvm.gep inbounds` $\to$ `rv64.add` replace potential
    `.poison` on overflow/out-of-bounds with wrapping `BitVec 64` addition. -/
theorem lowerAnLLVMOpToRv64_refines (op : HybridOp) (acc : AnWord) :
    PoisonOr.IsRefinedBy
      (evalHybridOp op acc)
      (evalHybridOp (lowerAnLLVMOpToRv64 op) acc) := by
  cases acc with
  | poison => trivial
  | value a =>
    cases op with
    | llvmAddNsw lhs rhs =>
      simp only [lowerAnLLVMOpToRv64, evalHybridOp, PoisonOr.bind]
      split
      · rfl
      · trivial
    | rv64Add lhs rhs =>
      exact PoisonOr.isRefinedBy_refl _
    | llvmGepInbounds base offset allocSize =>
      simp only [lowerAnLLVMOpToRv64, evalHybridOp, PoisonOr.bind, gepInbounds]
      split
      · rfl
      · trivial
    | rv64AddrAdd base offset =>
      exact PoisonOr.isRefinedBy_refl _

/-- Axiom-clean directional instruction-lowering compiler from `AnLLVM` to
    `RV64` inside `HybridDialectLang`, replacing `opencompl/lean-mlir`'s
    `toPeepholeUNSOUND` (`SSA/Projects/LLVMRiscV/PeepholeRefine.lean:33-53`). -/
def directionalRewriteCompiler : Compiler HybridDialectLang HybridDialectLang where
  compile := lowerHybridProg lowerAnLLVMOpToRv64
  π       := id

/-- `directionalRewriteCompiler` satisfies `Compiles` on every program `p`. -/
theorem addNswToRv64Add_compiles (p : HybridDialectLang.Prog) :
    Compiles HybridDialectLang HybridDialectLang id
      p (directionalRewriteCompiler.compile p) := by
  intro q
  have h_ref :=
    evalHybridProg_lower_refines lowerAnLLVMOpToRv64
      lowerAnLLVMOpToRv64_refines p (.value q)
  exact (PoisonOr.isRefinedBy_iff_toObservablePartial_le _ _).mp h_ref

/-- `directionalRewriteCompiler` is sound (`Compiler.SoundOn`) and verified
    (`Compiler.Verified`) on every source program `p` and specification `spec`
    that `p` satisfies, with zero custom axioms. -/
theorem directionalRewriteCompiler_verified
    (p : HybridDialectLang.Prog) (spec : HybridDialectLang.Behavior)
    (h_src : HybridDialectLang.sem p ≤ spec) :
    directionalRewriteCompiler.Verified p spec :=
  Compiler.SoundOn.verify ⟨monotone_id, addNswToRv64Add_compiles p⟩ h_src

/-! ============================================================================
    SECTION 4: VERIFIED `MonoMIR` TO `AnLLVM` LOWERING & NEGATIVE CANARIES
    (Sub-part 4A: `MaybeUninit` / `PassMode::Cast` Padding & `freeze` vs. `noundef`;
     Sub-part 4B: `!Unpin` Self-Referential Aliasing vs. `noalias`)
    ============================================================================ -/

/-! ### Sub-part 4A: `MaybeUninit` / `PassMode::Cast` Padding Lowering -/

/-- A `MonoMIR` program that loads a potentially uninitialized stack slot
    (`MaybeUninit<u64>` or a `PassMode::Cast` scratch `alloca` containing
    padding bytes, cf. `rustc_codegen_ssa/src/mir/block.rs:2082-2103`) and adds
    a constant `addend`. -/
structure MirUninitProg where
  addend : BitVec 64

/-- In `MonoMIR`, reading a `MaybeUninit<u64>` or `PassMode::Cast` byte-copied
    chunk when the input query `q : Option (BitVec 64)` is `some v` yields
    `v + addend`; when `q = none` (uninitialized padding bytes), the read is
    well-defined (`defined := True`) and may yield `v + addend` for any concrete
    hardware bitpattern `v`. -/
def MonoMIRUninitLang : Language where
  Prog  := MirUninitProg
  Query := Option (BitVec 64)
  Out   := BitVec 64
  sem p q :=
    Partial.pure (fun out =>
      match q with
      | some v => out = v + p.addend
      | none   => ∃ v : BitVec 64, out = v + p.addend)

/-- An `AnLLVM` program lowered from `MirUninitProg`, parameterized by the
    load's `LoadMeta` (`noundef`, `range`) and whether `freeze` is inserted
    before observing the loaded word. -/
structure AnLLVMUninitProg where
  loadMeta  : LoadMeta
  useFreeze : Bool
  addend    : BitVec 64

/-- Convert the initial stack slot query `Option (BitVec 64)` into the initial
    `AnLLVM` memory cell (`some v ↦ .value v`, `none ↦ .poison`, matching
    `Vellvm` `MemoryBytes.v:101-115` `poison_memory_byte`). -/
def slotToAnWord : Option (BitVec 64) → AnWord
  | some v => .value v
  | none   => .poison

/-- Semantics of `AnLLVMUninitProg`:
    1. Executes `evalLoadMeta (slotToAnWord q) p.loadMeta`.
    2. If `p.useFreeze = true`, applies `freezeSem` (picking any concrete `v`
       when the loaded word is `.poison`) and returns `v + p.addend`.
    3. If `p.useFreeze = false`, observes `(loaded + p.addend)` directly via
       `PoisonOr.toObservablePartial` (so `.poison` triggers UB at observation). -/
def AnLLVMUninitLang : Language where
  Prog  := AnLLVMUninitProg
  Query := Option (BitVec 64)
  Out   := BitVec 64
  sem p q :=
    let loaded := evalLoadMeta (slotToAnWord q) p.loadMeta
    { defined :=
        loaded.defined ∧
        ∀ h : loaded.defined,
          ∀ w : AnWord, loaded.val h w →
            (if p.useFreeze then True else w ≠ .poison)
      val := fun h_def out =>
        ∃ w : AnWord,
          loaded.val h_def.1 w ∧
          match w with
          | .value v => out = v + p.addend
          | .poison  => p.useFreeze = true ∧ ∃ v : BitVec 64, out = v + p.addend }

/-- Verified `rustc_codegen_anneal_llvm` lowering for `MirUninitProg`: omits
    `noundef` and `!range` (`noundef := false, range := none`) and inserts
    `freeze` (`useFreeze := true`). -/
def mirToAnLLVMSafeCompiler : Compiler MonoMIRUninitLang AnLLVMUninitLang where
  compile p := {
    loadMeta  := { noundef := false, range := none }
    useFreeze := true
    addend    := p.addend
  }
  π := id

/-- Soundness of `mirToAnLLVMSafeCompiler`: omitting `noundef`/`!range` and
    inserting `freeze` refines `MonoMIRUninitLang` across both initialized
    (`some v`) and uninitialized/padding (`none`) queries. -/
theorem mirToAnLLVMSafe_compiles (p : MirUninitProg) :
    Compiles MonoMIRUninitLang AnLLVMUninitLang id
      p (mirToAnLLVMSafeCompiler.compile p) := by
  intro q _
  cases q with
  | some v =>
    refine ⟨⟨True.intro, fun _ _ _ => trivial⟩, ?_⟩
    intro out ⟨w, hw, hout⟩
    change w = .value v at hw
    subst hw
    exact hout
  | none =>
    refine ⟨⟨True.intro, fun _ _ _ => trivial⟩, ?_⟩
    intro out ⟨w, hw, hout⟩
    change w = .poison at hw
    subst hw
    exact hout.2

/-- End-to-end `Compiler.Verified` theorem for `mirToAnLLVMSafeCompiler` on
    `MonoMIRUninitLang.WellFormed`. -/
theorem mirToAnLLVMSafe_verified (p : MirUninitProg) :
    mirToAnLLVMSafeCompiler.Verified p MonoMIRUninitLang.WellFormed :=
  Compiler.SoundOn.verify
    ⟨monotone_id, mirToAnLLVMSafe_compiles p⟩
    (fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩)

/-- Naive lowering that attaches `noundef := true` to a load that may read
    uninitialized `MaybeUninit` or `PassMode::Cast` padding bytes. -/
def mirToAnLLVMNaiveNoundef (p : MirUninitProg) : AnLLVMUninitProg where
  loadMeta  := { noundef := true, range := none }
  useFreeze := false
  addend    := p.addend

/-- **Negative Canary 1 (`canary_uninit_noundef_refutes_compiles`):**
    Attaching `noundef := true` to a load of a potentially uninitialized
    `MaybeUninit` or `PassMode::Cast` padding slot triggers immediate UB
    (`defined = False`) at `q = none`, whereas the source `MonoMIR` program is
    well-defined (`defined = True`), refuting `Compiles`. -/
theorem canary_uninit_noundef_refutes_compiles (p : MirUninitProg) :
    ¬ Compiles MonoMIRUninitLang AnLLVMUninitLang id
        p (mirToAnLLVMNaiveNoundef p) := by
  intro h_comp
  obtain ⟨h_def, _⟩ := h_comp none True.intro
  exact h_def.1

/-! ### Sub-part 4B: `!Unpin` Self-Referential Aliasing vs. `noalias` -/

/-- Initial query state for a self-referential struct `S`:
    - `initVal`: initial value of `self.val`.
    - `aliasWritesToSelf`: whether the raw pointer `self.ptr` points to
      `self.val` (which is legal in Rust for `Pin<&mut S>` when `S: !Unpin`). -/
structure SelfRefQuery where
  initVal           : BitVec 64
  aliasWritesToSelf : Bool

/-- A `MonoMIR` function descriptor that takes `self: &mut S`, writes `write1`
    to `self.val`, writes `write2` through `self.ptr`, and returns `self.val`.
    `isUnpin` records whether `S: Unpin` holds (`rustc_middle/src/ty/layout.rs:1165`). -/
structure MirPinProg where
  isUnpin : Bool
  write1  : BitVec 64
  write2  : BitVec 64

/-- Semantics of `MirPinProg` in `MonoMIR` (matching Tree Borrows in
    `rustc_codegen_ssa/src/mir/retag.rs:208` `let is_protected = is_fn_entry &&
    (!is_mutable || is_unpin)`):
    - When `isUnpin = true` and `q.aliasWritesToSelf = true`, writing through a
      raw-pointer alias of a protected `Unpin` `&mut` triggers UB (`Partial.ub`).
    - When `isUnpin = false` (`!Unpin`), self-referential raw-pointer writes are
      well-defined and update `self.val` to `p.write2`. -/
def MonoMIRPinLang : Language where
  Prog  := MirPinProg
  Query := SelfRefQuery
  Out   := BitVec 64
  sem p q :=
    if p.isUnpin && q.aliasWritesToSelf then
      Partial.ub
    else
      Partial.pure (fun out =>
        out = if q.aliasWritesToSelf then p.write2 else p.write1)

/-- `AnLLVM` representation of `MirPinProg`, carrying the parameter attribute
    `noalias : Bool` on `self` and a flag `loadForwarded : Bool` recording
    whether LLVM's `ScopedNoAliasAA` / `GVN` load-forwarding pass forwarded
    `write1` across the store to `self.ptr`. -/
structure AnLLVMPinProg where
  noalias       : Bool
  loadForwarded : Bool
  write1        : BitVec 64
  write2        : BitVec 64

/-- Semantics of `AnLLVMPinProg`:
    - If `loadForwarded = true`, the function unconditionally returns `p.write1`
      (because `GVN` replaced the final load of `self.val` with `p.write1`).
    - Otherwise, it returns `if q.aliasWritesToSelf then p.write2 else p.write1`. -/
def AnLLVMPinLang : Language where
  Prog  := AnLLVMPinProg
  Query := SelfRefQuery
  Out   := BitVec 64
  sem p q :=
    Partial.pure (fun out =>
      if p.loadForwarded then
        out = p.write1
      else
        out = if q.aliasWritesToSelf then p.write2 else p.write1)

/-- Standard LLVM `GVN` / `DSE` load-forwarding optimization pass: when a pointer
    parameter carries `noalias = true`, LLVM assumes no raw pointer not derived
    from the parameter within the function can alias it, and forwards `write1`
    directly to the return value (`loadForwarded := true`). -/
def optNoAliasLoadForward (p : AnLLVMPinProg) : AnLLVMPinProg :=
  if p.noalias then
    { p with loadForwarded := true }
  else
    p

/-- Verified `rustc_codegen_anneal_llvm` lowering for `MirPinProg`: gates
    `noalias` on `p.isUnpin` (`noalias := p.isUnpin`), matching
    `rustc_middle/src/ty/layout.rs:1165` (`PointerKind::MutableRef { unpin }`),
    followed by `optNoAliasLoadForward`. -/
def mirToAnLLVMPinSafeCompiler : Compiler MonoMIRPinLang AnLLVMPinLang where
  compile p := optNoAliasLoadForward {
    noalias       := p.isUnpin
    loadForwarded := false
    write1        := p.write1
    write2        := p.write2
  }
  π := id

/-- Soundness of `mirToAnLLVMPinSafeCompiler`: gating `noalias` on `p.isUnpin`
    is sound even after `optNoAliasLoadForward` runs!
    - When `p.isUnpin = false` (`!Unpin`), `noalias` is `false`, so
      `optNoAliasLoadForward` is a no-op and self-referential writes return
      `p.write2`.
    - When `p.isUnpin = true` (`Unpin`), if `q.aliasWritesToSelf = false`,
      forwarding `p.write1` agrees with the unaliased execution; if
      `q.aliasWritesToSelf = true`, the source `MonoMIR` exhibits UB
      (`defined = False`), so `Compiles` holds vacuously! -/
theorem mirToAnLLVMPinSafe_compiles (p : MirPinProg) :
    Compiles MonoMIRPinLang AnLLVMPinLang id
      p (mirToAnLLVMPinSafeCompiler.compile p) := by
  rcases p with ⟨isUnpin, write1, write2⟩
  rcases isUnpin with _ | _
  · intro q _
    refine ⟨True.intro, ?_⟩
    intro out h_out
    exact h_out
  · intro q h_src_def
    rcases q with ⟨initVal, aliasWritesToSelf⟩
    rcases aliasWritesToSelf with _ | _
    · refine ⟨True.intro, ?_⟩
      intro out h_out
      exact h_out
    · exact False.elim h_src_def

/-- End-to-end `Compiler.Verified` theorem for `mirToAnLLVMPinSafeCompiler` on
    any `!Unpin` self-referential program (`p.isUnpin = false`). -/
theorem mirToAnLLVMPinSafe_verified (write1 write2 : BitVec 64) :
    let p : MirPinProg := { isUnpin := false, write1 := write1, write2 := write2 }
    mirToAnLLVMPinSafeCompiler.Verified p MonoMIRPinLang.WellFormed := by
  intro p
  exact Compiler.SoundOn.verify
    ⟨monotone_id, mirToAnLLVMPinSafe_compiles p⟩
    (fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩)

/-- Unsound lowering (pre-Issue #63818 `rustc_codegen_llvm` bug) that unconditionally
    attaches `noalias := true` to `&mut T` even when `T: !Unpin`. -/
def mirToAnLLVMPinUnsound (p : MirPinProg) : AnLLVMPinProg :=
  optNoAliasLoadForward {
    noalias       := true
    loadForwarded := false
    write1        := p.write1
    write2        := p.write2
  }

/-- Concrete `!Unpin` self-referential coroutine state test case: writes `10`
    to `self.val`, writes `20` via `self.ptr`, and returns `self.val`. -/
def selfRefPinCanaryProg : MirPinProg where
  isUnpin := false
  write1  := 10#64
  write2  := 20#64

/-- **Negative Canary 2 (`canary_self_referential_noalias_refutes_compiles`):**
    Unconditionally attaching `noalias := true` to `&mut S` when `S: !Unpin`
    allows `optNoAliasLoadForward` to forward `10#64` across the self-referential
    store of `20#64`, producing `10#64 ≠ 20#64` on `aliasWritesToSelf = true`
    and refuting `Compiles`! -/
theorem canary_self_referential_noalias_refutes_compiles :
    ¬ Compiles MonoMIRPinLang AnLLVMPinLang id
        selfRefPinCanaryProg (mirToAnLLVMPinUnsound selfRefPinCanaryProg) := by
  intro h_comp
  let q : SelfRefQuery := { initVal := 0#64, aliasWritesToSelf := true }
  obtain ⟨_, h_sub⟩ := h_comp q True.intro
  have h_tgt :
      (AnLLVMPinLang.sem (mirToAnLLVMPinUnsound selfRefPinCanaryProg) q).val
        True.intro 10#64 := rfl
  have h_src := h_sub 10#64 h_tgt
  change (10#64 : BitVec 64) = 20#64 at h_src
  nomatch h_src

/-! ============================================================================
    SECTION 5: seL4 `GraphLang`-STYLE BINARY TRANSLATION VALIDATOR
    (`checkBinaryGraphRefine`) AND END-TO-END `MonoMIR` → `AnLLVM` → `MachineCode`
    ============================================================================ -/

/-- A counted accumulation loop in `MonoMIR`:
    `for i in 0..bound { acc = acc + stepCoeff * i + stepBias; } return acc + exitBias`. -/
structure MirLoopProg where
  stepCoeff : Nat
  stepBias  : Nat
  exitBias  : Nat

/-- Tail-recursive loop execution helper shared by `MonoMIR`, `AnLLVM`, and
    `MachineCode` when step parameters match. -/
def runCountedLoop (coeff bias : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc        => acc
  | fuel + 1, i, acc =>
    runCountedLoop coeff bias fuel (i + 1) (acc + coeff * i + bias)

/-- Query for the loop languages: `(bound, initAcc)`. -/
structure LoopQuery where
  bound   : Nat
  initAcc : Nat

/-- `MonoMIR` loop language. -/
def MonoMIRLoopLang : Language where
  Prog  := MirLoopProg
  Query := LoopQuery
  Out   := Nat
  sem p q :=
    Partial.pure (fun out =>
      out = runCountedLoop p.stepCoeff p.stepBias q.bound 0 q.initAcc + p.exitBias)

/-- `AnLLVM` loop representation with explicit loop header cut-point parameters
    (`irStepCoeff`, `irStepBias`, `irExitBias`). -/
structure AnLLVMLoopProg where
  irStepCoeff : Nat
  irStepBias  : Nat
  irExitBias  : Nat

/-- `AnLLVM` loop language. -/
def AnLLVMLoopLang : Language where
  Prog  := AnLLVMLoopProg
  Query := LoopQuery
  Out   := Nat
  sem p q :=
    Partial.pure (fun out =>
      out = runCountedLoop p.irStepCoeff p.irStepBias q.bound 0 q.initAcc + p.irExitBias)

/-- Lower `MirLoopProg` to `AnLLVMLoopProg`. -/
def mirToAnLLVMLoopCompiler : Compiler MonoMIRLoopLang AnLLVMLoopLang where
  compile p := {
    irStepCoeff := p.stepCoeff
    irStepBias  := p.stepBias
    irExitBias  := p.exitBias
  }
  π := id

theorem mirToAnLLVMLoop_compiles (p : MirLoopProg) :
    Compiles MonoMIRLoopLang AnLLVMLoopLang id
      p (mirToAnLLVMLoopCompiler.compile p) :=
  fun _ => Preorder.le_refl _

/-- Compiled machine-code (`GraphLang` ASM) loop representation with explicit
    loop stride `asmUnrollFactor` (`l_step` vs. `r_step` in `seL4/graph-refine`,
    `check.py:154-205`), loop-body arithmetic coefficients `asmStepCoeff` and
    `asmStepBias`, and epilogue offset `asmExitBias`. -/
structure MachineLoopProg where
  asmUnrollFactor : Nat
  asmStepCoeff    : Nat
  asmStepBias     : Nat
  asmExitBias     : Nat
  deriving DecidableEq

/-- Execute the compiled `MachineLoopProg`:
    - When `asmUnrollFactor == 1`, each machine loop iteration advances `i` by `1`
      and updates `acc` by `asmStepCoeff * i + asmStepBias`.
    - When `asmUnrollFactor != 1`, the machine loop has been unrolled/vectorized
      by a factor $\neq 1$. -/
def MachineLoopLang : Language where
  Prog  := MachineLoopProg
  Query := LoopQuery
  Out   := Nat
  sem mc q :=
    Partial.pure (fun out =>
      if mc.asmUnrollFactor == 1 then
        out = runCountedLoop mc.asmStepCoeff mc.asmStepBias q.bound 0 q.initAcc +
              mc.asmExitBias
      else
        out = 0)

/-- seL4 `GraphLang`-style $1:1$ loop cut-point validator
    (`ProofNode('Split', ((l_split, (0, 1), eqs), (r_split, (0, 1), eqs), ...))`
    in `seL4/graph-refine/check.py:154-355, 512-565`):
    Checks that:
    1. The machine loop has $1:1$ cut-point stride (`mc.asmUnrollFactor == 1`),
    2. One iteration of the machine loop body from cut-point state `(i, acc)`
       establishes the same next-state polynomial as the `AnLLVM` loop body
       (`mc.asmStepCoeff == ir.irStepCoeff && mc.asmStepBias == ir.irStepBias`),
       and
    3. The loop-exit path to `Ret` matches (`mc.asmExitBias == ir.irExitBias`). -/
def checkBinaryGraphRefine (ir : AnLLVMLoopProg) (mc : MachineLoopProg) : Bool :=
  (mc.asmUnrollFactor == 1) &&
  (mc.asmStepCoeff == ir.irStepCoeff) &&
  (mc.asmStepBias == ir.irStepBias) &&
  (mc.asmExitBias == ir.irExitBias)

/-- Soundness of `checkBinaryGraphRefine`: whenever the binary translation
    validator returns `true`, the compiled `MachineLoopProg` refines the
    `AnLLVMLoopProg` (`Compiles AnLLVMLoopLang MachineLoopLang id ir mc`). -/
theorem checkBinaryGraphRefine_sound
    (ir : AnLLVMLoopProg) (mc : MachineLoopProg)
    (h_ok : checkBinaryGraphRefine ir mc = true) :
    Compiles AnLLVMLoopLang MachineLoopLang id ir mc := by
  rcases ir with ⟨irCoeff, irBias, irExit⟩
  rcases mc with ⟨asmUnroll, asmCoeff, asmBias, asmExit⟩
  simp only [checkBinaryGraphRefine, Bool.and_eq_true, beq_iff_eq] at h_ok
  rcases h_ok with ⟨⟨⟨h_unroll, h_coeff⟩, h_bias⟩, h_exit⟩
  subst h_unroll; subst h_coeff; subst h_bias; subst h_exit
  intro q _
  refine ⟨True.intro, ?_⟩
  intro out h_out
  exact h_out

/-- **Negative Canary 3 (`canary_unrolled_1to1_split_fails`):**
    When the compiler unrolls a loop by $2\times$ (`asmUnrollFactor := 2`, as in
    `seL4/graph-refine/loop-example/O2/ASM-annotated.txt` where `gcc -O2` emits a
    $2\times$ unrolled body at nodes `104..156`), a $1:1$ cut-point split check
    (`l_step = 1, r_step = 1`) fails (`checkBinaryGraphRefine = false`) unless
    the `Split` node scales the step ratio to `r_step = 2` and case-splits on
    the loop bound's parity. -/
theorem canary_unrolled_1to1_split_fails (ir : AnLLVMLoopProg) :
    checkBinaryGraphRefine ir {
      asmUnrollFactor := 2
      asmStepCoeff    := ir.irStepCoeff
      asmStepBias     := ir.irStepBias
      asmExitBias     := ir.irExitBias
    } = false := rfl

/-- Concrete compiler backend from `AnLLVMLoopLang` to `MachineLoopLang` that
    preserves loop cut-points (`asmUnrollFactor := 1`, corresponding to `-O1` or
    `-O2 -fno-unroll-loops -fno-vectorize`). -/
def anLLVMToMachineLoopCompiler : Compiler AnLLVMLoopLang MachineLoopLang where
  compile ir := {
    asmUnrollFactor := 1
    asmStepCoeff    := ir.irStepCoeff
    asmStepBias     := ir.irStepBias
    asmExitBias     := ir.irExitBias
  }
  π := id

/-- Every `AnLLVMLoopProg` compiled by `anLLVMToMachineLoopCompiler` passes
    `checkBinaryGraphRefine`. -/
theorem anLLVMToMachineLoop_passes_tv (ir : AnLLVMLoopProg) :
    checkBinaryGraphRefine ir (anLLVMToMachineLoopCompiler.compile ir) = true := by
  simp only [checkBinaryGraphRefine, anLLVMToMachineLoopCompiler,
             beq_self_eq_true, Bool.and_self]

/-- Soundness of `anLLVMToMachineLoopCompiler` proved via the binary translation
    validator (`checkBinaryGraphRefine_sound`). -/
theorem anLLVMToMachineLoop_compiles (ir : AnLLVMLoopProg) :
    Compiles AnLLVMLoopLang MachineLoopLang id
      ir (anLLVMToMachineLoopCompiler.compile ir) :=
  checkBinaryGraphRefine_sound ir
    (anLLVMToMachineLoopCompiler.compile ir)
    (anLLVMToMachineLoop_passes_tv ir)

/-- End-to-end composed compiler `MonoMIRLoopLang → AnLLVMLoopLang → MachineLoopLang`. -/
def endToEndLoopCompiler : Compiler MonoMIRLoopLang MachineLoopLang :=
  compCompilers mirToAnLLVMLoopCompiler anLLVMToMachineLoopCompiler

/-- End-to-end verification theorem (`Compiler.Verified`) composing verified
    `MonoMIR → AnLLVM` lowering (`mirToAnLLVMLoop_compiles`) with `seL4`
    `GraphLang`-style binary translation validation (`checkBinaryGraphRefine_sound`)
    via `Anneal.Compiler.SoundOn.comp` and `Anneal.pass_trans`. -/
theorem endToEnd_mir_to_machine_verified (p : MirLoopProg) :
    endToEndLoopCompiler.Verified p
      (MonoMIRLoopLang.Spec (fun q out =>
        out = runCountedLoop p.stepCoeff p.stepBias q.bound 0 q.initAcc + p.exitBias)) := by
  have h_sound₁ : mirToAnLLVMLoopCompiler.SoundOn p :=
    ⟨monotone_id, mirToAnLLVMLoop_compiles p⟩
  have h_sound₂ : anLLVMToMachineLoopCompiler.SoundOn (mirToAnLLVMLoopCompiler.compile p) :=
    ⟨monotone_id, anLLVMToMachineLoop_compiles (mirToAnLLVMLoopCompiler.compile p)⟩
  have h_sound_e2e : endToEndLoopCompiler.SoundOn p :=
    Compiler.SoundOn.comp h_sound₁ h_sound₂
  exact Compiler.SoundOn.verify h_sound_e2e (Preorder.le_refl _)

/-- Semantic `GraphLang` cut-point induction (`split_induct_step_checks` in
    `seL4/graph-refine/check.py:154-205`): given an arbitrary `AnLLVM` loop body
    `irStep : BitVec 64 → BitVec 64 → BitVec 64` and a register-allocated /
    instruction-selected `MachineCode` loop body
    `asmStep : BitVec 64 → BitVec 64 → BitVec 64`, execute `fuel` iterations from
    cut-point state `(i, acc)`. -/
def runBitVecLoop (step : BitVec 64 → BitVec 64 → BitVec 64) :
    Nat → BitVec 64 → BitVec 64 → BitVec 64
  | 0, _, acc        => acc
  | fuel + 1, i, acc => runBitVecLoop step fuel (i + 1#64) (step i acc)

/-- Inductive loop cut-point theorem (`SingleRevInduct` / `Split` induction in
    `seL4/graph-refine/check.py:175-205`): if the `MachineCode` loop body agrees
    with the `AnLLVM` loop body across a single cut-point traversal
    (`∀ i acc, asmStep i acc = irStep i acc`), then for every loop trip count
    `fuel : Nat` and entry cut-point state `(i, acc)`, the multi-step executions
    produce identical exit states. -/
theorem runBitVecLoop_cutpoint_induct
    (irStep asmStep : BitVec 64 → BitVec 64 → BitVec 64)
    (h_step : ∀ i acc, asmStep i acc = irStep i acc) :
    ∀ (fuel : Nat) (i acc : BitVec 64),
      runBitVecLoop asmStep fuel i acc = runBitVecLoop irStep fuel i acc
  | 0, _, _ => rfl
  | fuel + 1, i, acc => by
    simp only [runBitVecLoop, h_step i acc]
    exact runBitVecLoop_cutpoint_induct irStep asmStep h_step fuel (i + 1#64) (irStep i acc)

/-- Concrete instance of `runBitVecLoop_cutpoint_induct` where the `AnLLVM` loop
    body computes `(acc + i) + bias` and the compiled `MachineCode` loop body
    pre-associates the loop-invariant offset as `acc + (i + bias)`. -/
theorem reassociatedMachineLoop_eq_anLLVMLoop
    (bias : BitVec 64) (fuel : Nat) (i acc : BitVec 64) :
    runBitVecLoop (fun idx a => a + (idx + bias)) fuel i acc =
      runBitVecLoop (fun idx a => (a + idx) + bias) fuel i acc :=
  runBitVecLoop_cutpoint_induct
    (fun idx a => (a + idx) + bias)
    (fun idx a => a + (idx + bias))
    (fun idx a => (BitVec.add_assoc a idx bias).symm)
    fuel i acc

/-! ============================================================================
    SECTION 6: AXIOM FOOTPRINT VERIFICATION (`#guard_msgs in #print axioms`)
    Confirming zero `sorryAx` and zero `Lean.ofReduceBool`.
    ============================================================================ -/

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.PoisonOr.isRefinedBy_not_symm' does not depend on any axioms -/
#guard_msgs in
#print axioms PoisonOr.isRefinedBy_not_symm

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.leanMLIR_freeze_unsound_canary' does not depend on any axioms -/
#guard_msgs in
#print axioms leanMLIR_freeze_unsound_canary

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.freezeSem_refines_any_bitvec' does not depend on any axioms -/
#guard_msgs in
#print axioms freezeSem_refines_any_bitvec

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.directionalRewriteCompiler_verified' does not depend on any axioms -/
#guard_msgs in
#print axioms directionalRewriteCompiler_verified

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.mirToAnLLVMSafe_verified' does not depend on any axioms -/
#guard_msgs in
#print axioms mirToAnLLVMSafe_verified

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.canary_uninit_noundef_refutes_compiles' does not depend on any axioms -/
#guard_msgs in
#print axioms canary_uninit_noundef_refutes_compiles

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.mirToAnLLVMPinSafe_verified' does not depend on any axioms -/
#guard_msgs in
#print axioms mirToAnLLVMPinSafe_verified

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.canary_self_referential_noalias_refutes_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_self_referential_noalias_refutes_compiles

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.checkBinaryGraphRefine_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkBinaryGraphRefine_sound

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.canary_unrolled_1to1_split_fails' does not depend on any axioms -/
#guard_msgs in
#print axioms canary_unrolled_1to1_split_fails

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.endToEnd_mir_to_machine_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms endToEnd_mir_to_machine_verified

/-- info: 'Track6LlvmLoweringAndBinaryTvProbe.reassociatedMachineLoop_eq_anLLVMLoop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms reassociatedMachineLoop_eq_anLLVMLoop

end Track6LlvmLoweringAndBinaryTvProbe
