-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Forward-Compatible MIR Semantics vs. Pinned-`rustc` and Naive Fail-Closed Oracles

Standalone Lean 4 (`v4.34.1`) mechanization built on a self-contained
`Preorder` / `Partial` / `Behavior` / `Language` / `StepResult` /
`SmallStepMachine` refinement spine.

## Architectural Models Compared

1. **Model 1 (`Sem_PinnedRustc`, Pinned-`rustc` Single-Field Layout Oracle)**:
   - Evaluates type sizes and `transmute_copy` / `reinterpretVal` using a single
     `rustc`-extracted layout/payload oracle in which `#[repr(Rust)]` single-field
     structs (`struct ReprRustWrapper(pub u64)`) are emitted with
     `fields := [{ ty := .uint .u64, access := .pubSafe }]` because
     `tcx.layout_of(ReprRustWrapper) == tcx.layout_of(u64)` in `rustc 1.98.0`,
     while multi-field structs (`struct Pair(pub u32, pub u32)`) are emitted with
     `fields := []`.
   - **Theorem 1a (`model1_unsoundly_accepts_repr_rust_transmute`)**: Proves that
     Model 1 accepts `transmute_copy::<u64, ReprRustWrapper>(&x)` as UB-free
     (`≤ safeSpec`), violating forward-compatible soundness because the Rust
     Reference (`r[layout.repr.rust]`) guarantees neither `size_of == 8` nor the
     absence of uninitialized padding bytes in `#[repr(Rust)]` structs.
   - **Theorem 1b (`model1_multi_field_repr_rust_size_zero_bug`)**: Proves that
     when the extractor emits `fields := []` for a 2-field `struct Pair(u32, u32)`,
     the `fields.foldl` `tySizeStep` recurrence computes `tySize Pair = some 0`,
     causing `reinterpretVal` to accept transmuting `()` (0 bytes) into `Pair`
     (producing `Val.agg []`) and miscomputing `size_of::<Pair>() == 0`.

2. **Model 2 (`Sem_NaiveFailClosed`, Naive Fail-Closed `Option` Oracle)**:
   - Returns `none` (stepping to `StepResult.failed` / `.err`) from `tySize` /
     `layoutOf` whenever a type is `#[repr(Rust)]` or target-width-parametric
     `usize`.
   - **Theorem 2a (`model2_rejects_repr_rust_transmute_u64`)**: Proves that
     Model 2 rejects `transmute_copy::<u64, ReprRustWrapper>(&x)`.
   - **Theorem 2b (`model2_falsely_rejects_reflexive_and_polymorphic_ops`)**:
     Proves that Model 2 falsely rejects Reference-sound operations:
     - reflexive `transmute_copy::<ReprRustWrapper, ReprRustWrapper>(&w)`,
     - `copy_nonoverlapping::<ReprRustWrapper>(&src, &mut dst, 1)`,
     - `size_of::<ReprRustWrapper>() == size_of::<ReprRustWrapper>()`, and
     - safe `usize` arithmetic `1usize + 1usize`.

3. **Model 3 (`Sem_ForwardCompatible`, Demonic Quantification over
   `ReferenceAdmissible` Realizations + Authority Stratification)**:
   - Tags every `AdtDecl` with `ReprAttr` (`rust`, `transparent`, `c`,
     `primitiveInt`, `cAndInt`) and parameterizes execution by a deterministic
     `CompilerRealization` (`ptrWidthBytes`, `adtLayout`, `evalDeadBranchConsts`)
     constrained only by the normative `ReferenceAdmissible` predicate.
   - Defines `Sem_ForwardCompatible` both via step-0 `StepResult.choice` over
     `{ env // ReferenceAdmissible c targetCfg env }` and via query-enriched
     `ForwardQuery := { env // ReferenceAdmissible c targetCfg env } × ExecQuery MirState`,
     proving their constructive equivalence (`↔`).
   - Proves the five core theorems of Model 3 (`model3_rejects_repr_rust_u64_transmute`,
     `model3_accepts_repr_transparent_and_padding_free_repr_c_transmute`,
     `model3_accepts_reflexive_repr_rust_transmute_and_copy`,
     `model3_target_parametric_vs_cfg_gated_usize`, and
     `model3_refinement_bridge_and_tcb_stratification`).
-/

namespace ForwardCompatibleMirSemantics

/-!
## 1. Refinement Lattice and Small-Step Operational Spine
-/

/-- Reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting equips `A → B` with a refinement preorder. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructive partiality carrier representing `B ∪ {UB}`: `defined` is
`False` exactly when the computation exhibits undefined behavior. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Top element of `Partial B` representing unconditional UB (`defined := False`). -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val     := False.elim

/-- Demonic refinement on `Partial B`: `p₁ ≤ p₂` holds when, wherever `p₂` is
defined, `p₁` is also defined and refines it. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Query-indexed partial behaviors: for each query, either UB or a predicate
describing the set of permitted outcomes. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A semantic language. -/
structure Language where
  Prog  : Type
  Query : Type
  Out   : Type
  sem   : Prog → Behavior Query Out
  dom   : Prog → Query → Prop

/-- Behavior domain of `L`. -/
abbrev Language.Behavior (L : Language) : Type :=
  ForwardCompatibleMirSemantics.Behavior L.Query L.Out

/-- The specification "on queries satisfying `pre`, every outcome satisfies
`post`"; it is UB (undefined, hence unconstrained) outside `pre`. -/
def Language.SpecOn (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => ⟨pre q, fun _ => post q⟩

/-- Unconditional specification on `L` (`pre := fun _ => True`). -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness (UB-freedom) specification on `pre`. -/
abbrev Language.WellFormedOn (L : Language)
    (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness (UB-freedom) specification. -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Domain-intersected precondition non-vacuity. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  ∃ q, dom q ∧ pre q

/-- Dijkstra's Law of the Excluded Miracle. -/
def Language.ProductiveOn (L : Language)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog` against `(pre, post)`. -/
def Language.Verified (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn (L.dom prog) pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- Named proof obligation. -/
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

/-- Explicit unproved assumption obligation (`Obligation.assumed`). -/
abbrev Obligation.assumed {Id : Type} (id : Id) : Obligation Id :=
  ⟨id, False⟩

/-- Positive behavioral verification obligation (`Obligation.wellFormedAndSpecsOn`). -/
abbrev Obligation.wellFormedAndSpecsOn {Id : Type} (id : Id)
    (L : Language) (pre : L.Query → Prop) (specs : List L.Behavior)
    (prog : L.Prog) : Obligation Id :=
  ⟨id,
    L.Verified pre (fun _ _ => True) prog ∧
    AllHold (specs.map (fun spec =>
      NonVacuousOn (L.dom prog) (fun q => pre q ∧ (spec q).defined) ∧
      L.sem prog ≤ (fun q => ⟨pre q ∧ (spec q).defined,
        fun h o => (spec q).val h.2 o⟩)))⟩

/-- Policy governing which obligation identifiers `Id` may be waived. -/
structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

/-- Pairwise distinctness of the identifiers in `ids`. -/
def NoDupIds {Id : Type} (ids : List Id) : Prop :=
  (ids.foldr
    (fun id (acc : Prop × List Id) =>
      (AllHold (acc.2.map (fun id' => id ≠ id')) ∧ acc.1, id :: acc.2))
    (True, [])).1

/-- Waiver-aware verification envelope (`Trusted.VerificationResult`). -/
def VerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  NoDupIds (obligations.map Obligation.id) ∧
  NoDupIds waived ∧
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

/-- Distinguishes normal return from panic/unwind completion. -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind
  deriving DecidableEq, Repr

/-- Single-step transition outcome in a small-step operational machine. -/
inductive StepResult (State : Type) (Obs : Type := Empty) (Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed

/-- Deterministic silent (`τ`) internal step to `next` (emits no `Obs`). -/
def StepResult.silent {State Obs Val : Type}
    (next : State) : StepResult State Obs Val :=
  .choice (· = next)

/-- Alias `.err` for `.failed`. -/
abbrev StepResult.err {State Obs Val : Type} : StepResult State Obs Val :=
  .failed

/-- Alias `.ret` for normal return termination. -/
abbrev StepResult.ret {State Obs Val : Type}
    (v : Val) : StepResult State Obs Val :=
  .terminated (.normal v)

/-- Outcome recorded at the end of an `n`-step execution prefix. -/
inductive PrefixOutcome (State Val : Type) where
  | running (cur : State)
  | terminated (term : TerminationKind Val)
  | failed
  | stuck
  deriving DecidableEq, Repr

/-- A prefix outcome is safe when it neither fails (`.failed`) nor gets stuck
in an unmodeled state or empty choice (`.stuck`). -/
def PrefixOutcome.isSafe {State Val : Type} : PrefixOutcome State Val → Prop
  | .running _ => True
  | .terminated _ => True
  | .failed => False
  | .stuck => False

/-- Step-decoupled observable outcome of an operational execution. -/
inductive EventualOut (Obs : Type := Empty) (Val : Type) where
  | terminated (trace : List Obs) (term : TerminationKind Val)
  | diverges   (trace : List Obs)
  | reacts     (trace : List Obs)

/-- Small-step operational machine. -/
structure SmallStepMachine (Prog State : Type) (Obs : Type := Empty)
    (Val : Type) where
  initState : Prog → State → Prop
  step      : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of an `n`-step execution prefix from `s`. -/
inductive ReachesPrefix
    {Prog State Obs Val : Type}
    (step : Prog → State → StepResult State Obs Val → Prop) (p : Prog) :
    Nat → State → List Obs → PrefixOutcome State Val → Prop where
  | zero (s : State) :
      ReachesPrefix step p 0 s [] (.running s)
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome State Val) :
      step p s (.step obs s') →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome State Val) :
      step p s (.choice branches) →
      branches s' →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (branches : State → Prop) :
      step p s (.choice branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix step p (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      step p s (.terminated term) →
      ReachesPrefix step p (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) :
      step p s .failed →
      ReachesPrefix step p (n + 1) s [] .failed
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, step p s r) →
      ReachesPrefix step p (n + 1) s [] .stuck

/-- Step-decoupled eventual behavior of program `p` in machine `M`. -/
def EventualBehaviorOf {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    State → Partial (EventualOut Obs Val → Prop) :=
  fun init => {
    defined :=
      M.initState p init →
        ∀ n tr out,
          ReachesPrefix M.step p n init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p init ∧
      match out with
      | .terminated tr term =>
          ∃ n, ReachesPrefix M.step p n init tr (.terminated term)
      | .diverges tr =>
          ∃ n s, ReachesPrefix M.step p n init tr (.running s) ∧
            ∃ traj : Nat → State, traj 0 = s ∧
              ∀ k, ∃ m, ReachesPrefix M.step p (m + 1) (traj k) []
                (.running (traj (k + 1)))
      | .reacts tr =>
          tr ≠ [] ∧ ∃ n s, ReachesPrefix M.step p n init tr (.running s) ∧
            ∃ (traj : Nat → State) (segTrace : Nat → List Obs),
              traj 0 = s ∧
              ∀ k, segTrace k ≠ [] ∧
                ∃ m, ReachesPrefix M.step p (m + 1) (traj k) (segTrace k)
                  (.running (traj (k + 1)))
  }

/-- Package a `SmallStepMachine` as a `Language` using `EventualBehaviorOf`. -/
abbrev SmallStepMachine.toLanguage {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog  := Prog
  Query := State
  Out   := EventualOut Obs Val
  sem   := EventualBehaviorOf M
  dom   := M.initState

/-- Step-indexed prefix execution query (`ExecQuery State`), pairing an initial
state `init : State` with a step budget `steps : Nat`. -/
structure ExecQuery (State : Type) where
  init  : State
  steps : Nat

/-- Step-indexed prefix execution outcome (`ExecOut State Obs Val`). -/
structure ExecOut (State : Type) (Obs : Type := Empty) (Val : Type) where
  trace   : List Obs
  outcome : PrefixOutcome State Val

/-- Prefix behavior of program `p` in machine `M` over `ExecQuery State`. -/
def PrefixBehaviorOf {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut State Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M.step p q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M.step p q.steps q.init out.trace out.outcome
  }

/-- Package a `SmallStepMachine` as a prefix-indexed `Language` over `ExecQuery State`. -/
abbrev SmallStepMachine.toPrefixLanguage {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog  := Prog
  Query := ExecQuery State
  Out   := ExecOut State Obs Val
  sem   := PrefixBehaviorOf M
  dom   := fun p q => M.initState p q.init

/-!
## 2. Shared MIR AST with Explicit Representation Attributes (`ReprAttr`)
-/

/-- Fixed-width integer widths in Rust (`u8`..`u128`, `i8`..`i128`). -/
inductive IntWidth where
  | u8 | u16 | u32 | u64 | u128
  | i8 | i16 | i32 | i64 | i128
  deriving DecidableEq, Repr

/-- Exact byte size of a fixed-width Rust integer (`r[type.numeric.int.size]`). -/
def IntWidth.byteSize : IntWidth → Nat
  | .u8  | .i8  => 1
  | .u16 | .i16 => 2
  | .u32 | .i32 => 4
  | .u64 | .i64 => 8
  | .u128 | .i128 => 16

/-- Exact bit width of a fixed-width Rust integer. -/
def IntWidth.bitSize (w : IntWidth) : Nat :=
  w.byteSize * 8

/-- Explicit representation attribute on an `AdtDecl` (`r[layout.repr]`):
- `.rust`: default `#[repr(Rust)]` layout (`r[layout.repr.rust]`), with no
  cross-compiler or cross-version layout, field-order, or padding guarantees.
- `.transparent`: `#[repr(transparent)]` (`r[layout.repr.transparent]`),
  guaranteed to have the identical size, alignment, and validity as its single
  non-ZST field.
- `.c packed align`: `#[repr(C)]` with optional `#[repr(packed(N))]` and
  `#[repr(align(N))]` (`r[layout.repr.c]`).
- `.primitiveInt w`: `#[repr(u*)]` / `#[repr(i*)]` on fieldless or data-carrying
  enums (`r[layout.repr.primitive]`).
- `.cAndInt w`: combined `#[repr(C, u*)]` / `#[repr(C, i*)]`
  (`r[layout.repr.c-int]`). -/
inductive ReprAttr where
  | rust
  | transparent
  | c (packed : Option Nat) (align : Option Nat)
  | primitiveInt (w : IntWidth)
  | cAndInt (w : IntWidth)
  deriving DecidableEq, Repr

/-- MIR local variable index (`_0`, `_1`, ...). -/
structure LocalId where
  index : Nat
  deriving DecidableEq, Repr

/-- MIR type grammar covering fixed-width integers, target-width `usize`/`isize`,
`bool`, `()`, ADTs, references, and generic type parameters. -/
inductive MirTy where
  | usize
  | isize
  | uint (w : IntWidth)
  | int (w : IntWidth)
  | bool
  | unit
  | adt (name : String)
  | ref (inner : MirTy)
  | refMut (inner : MirTy)
  | param (idx : Nat)
  | unmodeled
  deriving DecidableEq, Repr

/-- Field visibility / safety classification. -/
inductive FieldAccess where
  | pubSafe
  | priv
  deriving DecidableEq, Repr

/-- Single field declaration inside an `AdtDecl`. -/
structure FieldDecl where
  ty     : MirTy
  access : FieldAccess := .pubSafe
  deriving DecidableEq, Repr

/-- Captured ADT declaration tagged with its explicit `ReprAttr`. -/
structure AdtDecl where
  name   : String
  repr   : ReprAttr := .rust
  fields : List FieldDecl
  deriving DecidableEq, Repr

/-- Whether safe downstream code can construct the struct directly with a
struct expression. -/
def AdtDecl.allFieldsPubSafe (decl : AdtDecl) : Bool :=
  decl.fields.all (fun f =>
    match f.access with
    | .pubSafe => true
    | .priv => false)

/-- Single-field payload type. -/
def AdtDecl.payloadTy (decl : AdtDecl) : Option MirTy :=
  match decl.fields with
  | [f] => some f.ty
  | _ => none

/-- Runtime MIR values. Includes both `.adt name inner` (single-field wrapper
form) and `.aggEmpty` (`Val.agg []`, the empty multi-field aggregate value
produced when `fields := []`). -/
inductive MirVal where
  | uninit
  | u64 (bits : Nat)
  | u32 (bits : Nat)
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | adt (name : String) (inner : MirVal)
  | aggEmpty
  | ref (loc : LocalId)
  deriving DecidableEq, Repr

/-- Multi-field aggregate constructor matching `Val.agg []`. -/
def MirVal.agg : List MirVal → MirVal
  | [] => .aggEmpty
  | v :: _ => v

/-- Alias `Val` for `MirVal`. -/
abbrev Val := MirVal

/-- Alias `Val.agg` for `MirVal.agg`. -/
abbrev Val.agg : List MirVal → MirVal := MirVal.agg

/-- Single-step MIR operations used across all three semantic models to compare
their treatment of `transmute_copy`, `copy_nonoverlapping`, `size_of`, and
`usize` arithmetic on identical syntax. -/
inductive MirOp where
  /-- `dst = core::mem::transmute_copy::<srcTy, dstTy>(&srcVal)` -/
  | transmuteCopy (srcTy dstTy : MirTy) (srcVal : MirVal)
  /-- `core::intrinsics::copy_nonoverlapping::<ty>(&srcVal, &mut dst, count)` -/
  | copyNonOverlapping (ty : MirTy) (srcVal : MirVal) (count : Nat)
  /-- `dst = core::mem::size_of::<ty>()` -/
  | sizeOf (ty : MirTy)
  /-- `dst = (core::mem::size_of::<ty1>() == core::mem::size_of::<ty2>())` -/
  | sizeOfEq (ty1 ty2 : MirTy)
  /-- Checked `usize` addition: `lhs + rhs` (UB / panic on unsigned overflow in
      checked/unchecked MIR arithmetic). -/
  | usizeAdd (lhs rhs : Nat)
  /-- Conditional branch with a dead `if false` branch carrying a required
      const evaluation obligation `deadConstSucceeded : Bool`. -/
  | branchWithDeadRequiredConst (deadConstSucceeded : Bool) (retVal : MirVal)
  deriving DecidableEq, Repr

/-- Crate declaration bundling captured `AdtDecl`s. -/
structure Crate where
  adts : List AdtDecl
  deriving DecidableEq, Repr

/-- Look up an `AdtDecl` by name in `c.adts`. -/
def Crate.findAdt (c : Crate) (name : String) : Option AdtDecl :=
  c.adts.find? (fun d => d.name == name)

/-!
### Standard Test ADTs and Crate Declarations
-/

/-- `#[repr(Rust)] pub struct ReprRustWrapper(pub u64);` -/
def reprRustWrapperDecl : AdtDecl where
  name   := "ReprRustWrapper"
  repr   := .rust
  fields := [{ ty := .uint .u64, access := .pubSafe }]

/-- `#[repr(transparent)] pub struct ReprTransparentWrapper(pub u64);` -/
def reprTransparentWrapperDecl : AdtDecl where
  name   := "ReprTransparentWrapper"
  repr   := .transparent
  fields := [{ ty := .uint .u64, access := .pubSafe }]

/-- `#[repr(C)] pub struct ReprCWrapper(pub u64);` -/
def reprCWrapperDecl : AdtDecl where
  name   := "ReprCWrapper"
  repr   := .c none none
  fields := [{ ty := .uint .u64, access := .pubSafe }]

/-- 2-field `#[repr(Rust)] pub struct Pair(pub u32, pub u32);` as emitted by an
extractor that only populates `fields` for single-field structs matching field
size and emits `fields := []` for all multi-field structs. -/
def pairDeclBuggy : AdtDecl where
  name   := "Pair"
  repr   := .rust
  fields := []

/-- 2-field `#[repr(Rust)] pub struct Pair(pub u32, pub u32);` with its true
field declarations preserved. -/
def pairDeclFull : AdtDecl where
  name   := "Pair"
  repr   := .rust
  fields := [
    { ty := .uint .u32, access := .pubSafe },
    { ty := .uint .u32, access := .pubSafe }
  ]

/-- Canonical test crate containing `ReprRustWrapper`, `ReprTransparentWrapper`,
`ReprCWrapper`, and `Pair` (with `fields := []` emission). -/
def testCrateModel1 : Crate where
  adts := [
    reprRustWrapperDecl,
    reprTransparentWrapperDecl,
    reprCWrapperDecl,
    pairDeclBuggy
  ]

/-- Canonical test crate with full field declarations for Model 2 and Model 3. -/
def testCrate : Crate where
  adts := [
    reprRustWrapperDecl,
    reprTransparentWrapperDecl,
    reprCWrapperDecl,
    pairDeclFull
  ]

/-!
## 3. Model 1: Pinned-`rustc` Single-Field Layout Oracle (`Sem_PinnedRustc`)

In Model 1:
1. The extractor checks `rustc_size == field_size` via `tcx.layout_of(...)` in the
   pinned `rustc` without checking `adt.repr().transparent()` or `adt.repr().c()`.
   Consequently, `ReprRustWrapper(u64)` is emitted with `fields := [u64]`, and
   `tySizeStep` computes its size as `some 8`—ignoring `decl.repr`.
2. For multi-field structs like `struct Pair(u32, u32)`, the extractor emits
   `fields := []`. Under the `fields.foldl` size recurrence,
   `tySizeStep` folds `[]` from `some 0` and computes `tySize Pair = some 0`,
   causing `reinterpretVal` to accept transmuting `()` (size 0) into `Pair`
   (producing `Val.agg []`) and miscomputing `size_of::<Pair>() == 0`.
-/

/-- Fuel-bounded `tySizeStep` recurrence in Model 1 (`fields.foldl` formulation
that sums `decl.fields` starting from `some 0` and ignores `decl.repr`). -/
def tySizeStepModel1 (c : Crate) : Nat → MirTy → Option Nat
  | 0, _ => none
  | _ + 1, .usize => some 8
  | _ + 1, .isize => some 8
  | _ + 1, .uint w => some w.byteSize
  | _ + 1, .int w => some w.byteSize
  | _ + 1, .bool => some 1
  | _ + 1, .unit => some 0
  | _ + 1, .ref _ => some 8
  | _ + 1, .refMut _ => some 8
  | fuel + 1, .adt name =>
    match c.findAdt name with
    | some decl =>
      decl.fields.foldl
        (fun accOpt f =>
          match accOpt, tySizeStepModel1 c fuel f.ty with
          | some acc, some sz => some (acc + sz)
          | _, _ => none)
        (some 0)
    | none => none
  | _ + 1, _ => none

/-- Top-level `tySize` in Model 1. -/
def tySizeModel1 (c : Crate) (ty : MirTy) : Option Nat :=
  tySizeStepModel1 c (c.adts.length + 2) ty

/-- Extract `(byteSize, bits)` from a source `MirVal` in Model 1. -/
def extractBitsModel1 (c : Crate) : MirVal → Option (Nat × Nat)
  | .u64 bits => some (8, bits)
  | .u32 bits => some (4, bits)
  | .usize bits => some (8, bits)
  | .bool b => some (1, if b then 1 else 0)
  | .unit => some (0, 0)
  | .adt name inner =>
    match c.findAdt name with
    | some _ => extractBitsModel1 c inner
    | none => none
  | .aggEmpty => some (0, 0)
  | _ => none

/-- Construct a target `MirVal` of type `dstTy` from `(dstSz, bits)` in Model 1:
- For a single-field struct (`decl.fields = [f]`) with `allFieldsPubSafe`,
  constructs `MirVal.adt name inner`.
- For an empty-field list (`decl.fields = []`, as emitted when erasing
  multi-field structs like `Pair(u32, u32)`), `allFieldsPubSafe` is vacuously
  `true` and `dstSz == 0` constructs `Val.agg []`! -/
def constructValModel1 (c : Crate) (dstSz bits : Nat) : Nat → MirTy → Option MirVal
  | 0, _ => none
  | _ + 1, .uint .u64 => if dstSz == 8 then some (.u64 bits) else none
  | _ + 1, .uint .u32 => if dstSz == 4 then some (.u32 bits) else none
  | _ + 1, .usize => if dstSz == 8 then some (.usize bits) else none
  | _ + 1, .unit => if dstSz == 0 then some .unit else none
  | fuel + 1, .adt name =>
    match c.findAdt name with
    | some decl =>
      if decl.allFieldsPubSafe then
        match decl.fields with
        | [f] =>
          (constructValModel1 c dstSz bits fuel f.ty).map (MirVal.adt name)
        | [] =>
          if dstSz == 0 then some (Val.agg []) else none
        | _ => none
      else
        none
    | none => none
  | _ + 1, _ => none

/-- Model 1 `reinterpretVal` / `evalTransmuteCopy`. -/
def reinterpretValModel1 (c : Crate) (srcTy dstTy : MirTy)
    (srcVal : MirVal) : Option MirVal :=
  match tySizeModel1 c srcTy, tySizeModel1 c dstTy, extractBitsModel1 c srcVal with
  | some srcSz, some dstSz, some (vSz, bits) =>
    if srcSz == dstSz && vSz == srcSz then
      constructValModel1 c dstSz bits (c.adts.length + 2) dstTy
    else
      none
  | _, _, _ => none

/-- Single-step evaluator for `MirOp` in Model 1. -/
def evalOpModel1 (c : Crate) : MirOp → StepResult Unit Empty MirVal
  | .transmuteCopy srcTy dstTy srcVal =>
    match reinterpretValModel1 c srcTy dstTy srcVal with
    | some v => .terminated (.normal v)
    | none => .failed
  | .copyNonOverlapping ty srcVal _count =>
    match tySizeModel1 c ty with
    | some _ => .terminated (.normal srcVal)
    | none => .failed
  | .sizeOf ty =>
    match tySizeModel1 c ty with
    | some sz => .terminated (.normal (.usize sz))
    | none => .failed
  | .sizeOfEq ty1 ty2 =>
    match tySizeModel1 c ty1, tySizeModel1 c ty2 with
    | some sz1, some sz2 => .terminated (.normal (.bool (sz1 == sz2)))
    | _, _ => .failed
  | .usizeAdd lhs rhs =>
    if lhs + rhs < 18446744073709551616 then
      .terminated (.normal (.usize (lhs + rhs)))
    else
      .failed
  | .branchWithDeadRequiredConst _deadConstSucceeded retVal =>
    .terminated (.normal retVal)

/-- Operational `SmallStepMachine` for Model 1. -/
def MachineModel1 (c : Crate) : SmallStepMachine MirOp Unit Empty MirVal where
  initState := fun _ s => s = ()
  step      := fun op _ r => r = evalOpModel1 c op

/-- Language packaging of Model 1 (`Sem_PinnedRustc`). -/
def LangModel1 (c : Crate) : Language :=
  (MachineModel1 c).toLanguage

/-- Behavior semantics `Sem_PinnedRustc` of Model 1. -/
abbrev Sem_PinnedRustc (c : Crate) (op : MirOp) :
    Behavior Unit (EventualOut Empty MirVal) :=
  (LangModel1 c).sem op

/-- Unconditional UB-freedom specification (`safeSpec`) on `Unit` state space. -/
def safeSpec (L : Language) : L.Behavior :=
  L.WellFormed

/-- Helper lemma: if `evalOp` returns `.terminated (.normal v)`, then every
reachable prefix in a 1-step deterministic machine is safe and refines `safeSpec`. -/
theorem deterministic_terminated_le_safeSpec
    (evalFn : MirOp → StepResult Unit Empty MirVal)
    (M : SmallStepMachine MirOp Unit Empty MirVal)
    (_h_init : M.initState = fun _ s => s = ())
    (h_step : M.step = fun op _ r => r = evalFn op)
    (op : MirOp) (v : MirVal)
    (h_eval : evalFn op = .terminated (.normal v)) :
    (M.toLanguage).sem op ≤ safeSpec M.toLanguage := by
  intro q _
  refine ⟨?_, ?_⟩
  · intro _ n tr out hreach
    cases hreach with
    | zero => exact True.intro
    | step _ _ _ _ _ _ hst _ =>
      rw [h_step] at hst
      rw [h_eval] at hst
      cases hst
    | choice _ _ _ _ _ _ hst _ _ =>
      rw [h_step] at hst
      rw [h_eval] at hst
      cases hst
    | emptyChoice _ _ _ hst _ =>
      rw [h_step] at hst
      rw [h_eval] at hst
      cases hst
    | terminated _ _ _ _ =>
      exact True.intro
    | failed _ _ hst =>
      rw [h_step] at hst
      rw [h_eval] at hst
      cases hst
    | noStep _ _ hno =>
      exact False.elim (hno ⟨evalFn op, by rw [h_step]⟩)
  · intro _ _
    exact True.intro

/-- Helper lemma: if `evalFn op = .failed`, then the machine reaches `.failed`
in 1 step and does NOT refine `safeSpec`. -/
theorem deterministic_failed_not_le_safeSpec
    (evalFn : MirOp → StepResult Unit Empty MirVal)
    (M : SmallStepMachine MirOp Unit Empty MirVal)
    (h_init : M.initState = fun _ s => s = ())
    (h_step : M.step = fun op _ r => r = evalFn op)
    (op : MirOp)
    (h_eval : evalFn op = .failed) :
    ReachesPrefix M.step op 1 () [] .failed ∧
    ¬ ((M.toLanguage).sem op ≤ safeSpec M.toLanguage) := by
  have h_reach : ReachesPrefix M.step op 1 () [] .failed := by
    apply ReachesPrefix.failed 0 ()
    rw [h_step]
    exact h_eval.symm
  refine ⟨h_reach, ?_⟩
  intro h_le
  have ⟨h_def, _⟩ := h_le () True.intro
  have h_init_unit : M.initState op () := by rw [h_init]
  have h_safe := h_def h_init_unit 1 [] .failed h_reach
  exact h_safe

/-- **Theorem 1a (`model1_unsoundly_accepts_repr_rust_transmute`)**:
Model 1 (`Sem_PinnedRustc`) computes `tySize ReprRustWrapper = some 8` and
accepts `transmute_copy::<u64, ReprRustWrapper>(&x)` as UB-free (`≤ safeSpec`),
producing `.adt "ReprRustWrapper" (.u64 x)`, even though `ReprRustWrapper` has
`repr = .rust` (`#[repr(Rust)]`) and the Rust Reference guarantees neither size
8 nor the absence of uninitialized padding bytes. -/
theorem model1_unsoundly_accepts_repr_rust_transmute (x : Nat) :
    reprRustWrapperDecl.repr = .rust ∧
    tySizeModel1 testCrateModel1 (.adt "ReprRustWrapper") = some 8 ∧
    reinterpretValModel1 testCrateModel1 (.uint .u64) (.adt "ReprRustWrapper") (.u64 x) =
      some (.adt "ReprRustWrapper" (.u64 x)) ∧
    Sem_PinnedRustc testCrateModel1
      (.transmuteCopy (.uint .u64) (.adt "ReprRustWrapper") (.u64 x)) ≤
      safeSpec (LangModel1 testCrateModel1) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact deterministic_terminated_le_safeSpec
    (evalOpModel1 testCrateModel1)
    (MachineModel1 testCrateModel1)
    rfl rfl
    (.transmuteCopy (.uint .u64) (.adt "ReprRustWrapper") (.u64 x))
    (.adt "ReprRustWrapper" (.u64 x))
    rfl

/-- **Theorem 1b (`model1_multi_field_repr_rust_size_zero_bug`)**:
When an extractor emits `fields := []` for the 2-field `#[repr(Rust)]` struct
`Pair(u32, u32)` (`pairDeclBuggy`), Model 1's `tySizeStep` computes
`tySize Pair = some 0`, causing:
1. `reinterpretVal` to accept transmuting `()` (0 bytes) into `Pair` and
   producing `Val.agg []`,
2. `size_of::<Pair>()` to evaluate to `.usize 0` instead of 8 bytes, and
3. `Sem_PinnedRustc` to accept `transmute_copy::<(), Pair>(&())` as UB-free
   (`≤ safeSpec`). -/
theorem model1_multi_field_repr_rust_size_zero_bug :
    pairDeclBuggy.fields = [] ∧
    tySizeModel1 testCrateModel1 (.adt "Pair") = some 0 ∧
    reinterpretValModel1 testCrateModel1 .unit (.adt "Pair") .unit =
      some (Val.agg []) ∧
    evalOpModel1 testCrateModel1 (.sizeOf (.adt "Pair")) =
      .terminated (.normal (.usize 0)) ∧
    Sem_PinnedRustc testCrateModel1
      (.transmuteCopy .unit (.adt "Pair") .unit) ≤
      safeSpec (LangModel1 testCrateModel1) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact deterministic_terminated_le_safeSpec
    (evalOpModel1 testCrateModel1)
    (MachineModel1 testCrateModel1)
    rfl rfl
    (.transmuteCopy .unit (.adt "Pair") .unit)
    (Val.agg [])
    rfl

/-!
## 4. Model 2: Naive Fail-Closed `Option` Oracle (`Sem_NaiveFailClosed`)

Model 2 attempts to fix Model 1 by returning `none` from `tySize` / `layoutOf`
whenever a type has `#[repr(Rust)]` (`decl.repr == .rust`) or is target-width
dependent (`usize` / `isize` without a pinned target pointer width). Because
`none` in `tySize` immediately transitions the small-step semantics to
`StepResult.failed` (`.err`), Model 2 conflates *compiler/target-parametric
layout* with *undefined behavior*.
-/

/-- Fuel-bounded `tySize` in Model 2 (`Sem_NaiveFailClosed`): returns `none`
for any `#[repr(Rust)]` ADT or unpinned `usize`/`isize`. -/
def tySizeStepModel2 (c : Crate) : Nat → MirTy → Option Nat
  | 0, _ => none
  | _ + 1, .usize => none
  | _ + 1, .isize => none
  | _ + 1, .uint w => some w.byteSize
  | _ + 1, .int w => some w.byteSize
  | _ + 1, .bool => some 1
  | _ + 1, .unit => some 0
  | _ + 1, .ref _ => none
  | _ + 1, .refMut _ => none
  | fuel + 1, .adt name =>
    match c.findAdt name with
    | some decl =>
      match decl.repr with
      | .rust => none
      | .transparent =>
        match decl.payloadTy with
        | some fty => tySizeStepModel2 c fuel fty
        | none => none
      | .c _ _ =>
        match decl.payloadTy with
        | some fty => tySizeStepModel2 c fuel fty
        | none => none
      | .primitiveInt w | .cAndInt w => some w.byteSize
    | none => none
  | _ + 1, _ => none

/-- Top-level `tySize` in Model 2. -/
def tySizeModel2 (c : Crate) (ty : MirTy) : Option Nat :=
  tySizeStepModel2 c (c.adts.length + 2) ty

/-- Model 2 `reinterpretVal`: fails closed whenever `tySizeModel2` is `none`. -/
def reinterpretValModel2 (c : Crate) (srcTy dstTy : MirTy)
    (srcVal : MirVal) : Option MirVal :=
  match tySizeModel2 c srcTy, tySizeModel2 c dstTy, extractBitsModel1 c srcVal with
  | some srcSz, some dstSz, some (vSz, bits) =>
    if srcSz == dstSz && vSz == srcSz then
      constructValModel1 c dstSz bits (c.adts.length + 2) dstTy
    else
      none
  | _, _, _ => none

/-- Single-step evaluator for `MirOp` in Model 2. -/
def evalOpModel2 (c : Crate) : MirOp → StepResult Unit Empty MirVal
  | .transmuteCopy srcTy dstTy srcVal =>
    match reinterpretValModel2 c srcTy dstTy srcVal with
    | some v => .terminated (.normal v)
    | none => .failed
  | .copyNonOverlapping ty srcVal _count =>
    match tySizeModel2 c ty with
    | some _ => .terminated (.normal srcVal)
    | none => .failed
  | .sizeOf ty =>
    match tySizeModel2 c ty with
    | some sz => .terminated (.normal (.usize sz))
    | none => .failed
  | .sizeOfEq ty1 ty2 =>
    match tySizeModel2 c ty1, tySizeModel2 c ty2 with
    | some sz1, some sz2 => .terminated (.normal (.bool (sz1 == sz2)))
    | _, _ => .failed
  | .usizeAdd _lhs _rhs =>
    -- Without a target pointer width, `tySizeModel2 c .usize = none`, so
    -- checked `usize` arithmetic fails closed to `.failed`.
    match tySizeModel2 c .usize with
    | some _ => .terminated (.normal (.usize 0))
    | none => .failed
  | .branchWithDeadRequiredConst deadConstSucceeded retVal =>
    if deadConstSucceeded then .terminated (.normal retVal) else .failed

/-- Operational `SmallStepMachine` for Model 2. -/
def MachineModel2 (c : Crate) : SmallStepMachine MirOp Unit Empty MirVal where
  initState := fun _ s => s = ()
  step      := fun op _ r => r = evalOpModel2 c op

/-- Language packaging of Model 2 (`Sem_NaiveFailClosed`). -/
def LangModel2 (c : Crate) : Language :=
  (MachineModel2 c).toLanguage

/-- Behavior semantics `Sem_NaiveFailClosed` of Model 2. -/
abbrev Sem_NaiveFailClosed (c : Crate) (op : MirOp) :
    Behavior Unit (EventualOut Empty MirVal) :=
  (LangModel2 c).sem op

/-- **Theorem 2a (`model2_rejects_repr_rust_transmute_u64`)**:
Model 2 (`Sem_NaiveFailClosed`) rejects `transmute_copy::<u64, ReprRustWrapper>(&x)`:
it steps to `StepResult.err` (`.failed`) in 1 step and does not refine `safeSpec`. -/
theorem model2_rejects_repr_rust_transmute_u64 (x : Nat) :
    tySizeModel2 testCrate (.adt "ReprRustWrapper") = none ∧
    evalOpModel2 testCrate
      (.transmuteCopy (.uint .u64) (.adt "ReprRustWrapper") (.u64 x)) =
      StepResult.err ∧
    ReachesPrefix (MachineModel2 testCrate).step
      (.transmuteCopy (.uint .u64) (.adt "ReprRustWrapper") (.u64 x))
      1 () [] .failed ∧
    ¬ (Sem_NaiveFailClosed testCrate
        (.transmuteCopy (.uint .u64) (.adt "ReprRustWrapper") (.u64 x)) ≤
        safeSpec (LangModel2 testCrate)) := by
  have h_fail := deterministic_failed_not_le_safeSpec
    (evalOpModel2 testCrate)
    (MachineModel2 testCrate)
    rfl rfl
    (.transmuteCopy (.uint .u64) (.adt "ReprRustWrapper") (.u64 x))
    rfl
  exact ⟨rfl, rfl, h_fail.1, h_fail.2⟩

/-- **Theorem 2b (`model2_falsely_rejects_reflexive_and_polymorphic_ops`)**:
Model 2 (`Sem_NaiveFailClosed`) **falsely rejects** (steps to `StepResult.err`
and fails `≤ safeSpec`) forward-compatible, Reference-sound operations:
1. Reflexive `transmute_copy::<ReprRustWrapper, ReprRustWrapper>(&w)`,
2. Byte-copying `copy_nonoverlapping::<ReprRustWrapper>(&src, &mut dst, 1)`,
3. Runtime evaluation of `size_of::<ReprRustWrapper>() == size_of::<ReprRustWrapper>()`, and
4. Safe `usize` arithmetic `1usize + 1usize`. -/
theorem model2_falsely_rejects_reflexive_and_polymorphic_ops (w : MirVal) :
    let opReflexiveTransmute :=
      MirOp.transmuteCopy (.adt "ReprRustWrapper") (.adt "ReprRustWrapper") w
    let opCopyNonOverlapping :=
      MirOp.copyNonOverlapping (.adt "ReprRustWrapper") w 1
    let opSizeOfEq :=
      MirOp.sizeOfEq (.adt "ReprRustWrapper") (.adt "ReprRustWrapper")
    let opUsizeAdd :=
      MirOp.usizeAdd 1 1
    evalOpModel2 testCrate opReflexiveTransmute = StepResult.err ∧
    evalOpModel2 testCrate opCopyNonOverlapping = StepResult.err ∧
    evalOpModel2 testCrate opSizeOfEq = StepResult.err ∧
    evalOpModel2 testCrate opUsizeAdd = StepResult.err ∧
    ¬ (Sem_NaiveFailClosed testCrate opReflexiveTransmute ≤
        safeSpec (LangModel2 testCrate)) ∧
    ¬ (Sem_NaiveFailClosed testCrate opCopyNonOverlapping ≤
        safeSpec (LangModel2 testCrate)) ∧
    ¬ (Sem_NaiveFailClosed testCrate opSizeOfEq ≤
        safeSpec (LangModel2 testCrate)) ∧
    ¬ (Sem_NaiveFailClosed testCrate opUsizeAdd ≤
        safeSpec (LangModel2 testCrate)) := by
  dsimp only
  have h1 := (deterministic_failed_not_le_safeSpec
    (evalOpModel2 testCrate) (MachineModel2 testCrate) rfl rfl
    (.transmuteCopy (.adt "ReprRustWrapper") (.adt "ReprRustWrapper") w) rfl).2
  have h2 := (deterministic_failed_not_le_safeSpec
    (evalOpModel2 testCrate) (MachineModel2 testCrate) rfl rfl
    (.copyNonOverlapping (.adt "ReprRustWrapper") w 1) rfl).2
  have h3 := (deterministic_failed_not_le_safeSpec
    (evalOpModel2 testCrate) (MachineModel2 testCrate) rfl rfl
    (.sizeOfEq (.adt "ReprRustWrapper") (.adt "ReprRustWrapper")) rfl).2
  have h4 := (deterministic_failed_not_le_safeSpec
    (evalOpModel2 testCrate) (MachineModel2 testCrate) rfl rfl
    (.usizeAdd 1 1) rfl).2
  exact ⟨rfl, rfl, rfl, rfl, h1, h2, h3, h4⟩

/-!
## 5. Model 3: Demonic Quantification over `ReferenceAdmissible` Realizations + Authority Stratification (`Sem_ForwardCompatible`)
-/

/-- Realized layout of an ADT in a specific `CompilerRealization` (`env`):
- `size`: realized byte size of the ADT (`size_of::<T>()`).
- `align`: realized byte alignment (`align_of::<T>()`).
- `fieldOffsets`: realized byte offset of each field in declaration order.
- `hasUninitPadding`: whether the realized layout contains any inter-field or
  trailing padding bytes (which hold uninitialized bytes when constructed or
  copied at runtime).
- `nicheBitPattern`: optional niche bit pattern reserved for layout optimization
  (e.g., in `Option<T>`). -/
structure AdtLayoutRealization where
  size             : Nat
  align            : Nat
  fieldOffsets     : List Nat
  hasUninitPadding : Bool
  nicheBitPattern  : Option Nat := none
  deriving DecidableEq, Repr

/-- Complete compiler and target realization (`env`) fixing the choices left
unspecified by the Rust Reference (`r[layout.repr.rust]`, `r[type.numeric.usize]`):
- `ptrWidthBytes`: target pointer / `usize` / `isize` byte width (`2`, `4`, or `8`).
- `adtLayout`: deterministic function mapping each ADT name to its realized
  `AdtLayoutRealization` in this compilation environment.
- `evalDeadBranchConsts`: whether unreached `Body::required_consts` in
  dynamically dead (`if false`) branches are evaluated at compile time during
  monomorphization. -/
structure CompilerRealization where
  ptrWidthBytes        : Nat
  adtLayout            : String → AdtLayoutRealization
  evalDeadBranchConsts : Bool := true

/-- Target configuration constraint active on the item being verified (for
example, from a verified `#[cfg(target_pointer_width = "64")]` attribute). -/
inductive TargetCfgConstraint where
  | any
  | ptrWidth16
  | ptrWidth32
  | ptrWidth64
  deriving DecidableEq, Repr

/-- Whether `n` is a power of two within the supported alignment range
(`1, 2, 4, 8, 16`). -/
def isPowerOfTwo (n : Nat) : Bool :=
  n == 1 || n == 2 || n == 4 || n == 8 || n == 16

/-- Round `offset` up to the next multiple of `align` (`r[layout.repr.c.struct]`). -/
def alignUp (offset align : Nat) : Nat :=
  if align == 0 then offset
  else
    let rem := offset % align
    if rem == 0 then offset else offset + (align - rem)

/-- Realized `(size, align, hasUninitPadding)` of a `MirTy` in environment `env`. -/
def tyLayoutInEnv (env : CompilerRealization) : MirTy → Option (Nat × Nat × Bool)
  | .usize | .isize | .ref _ | .refMut _ =>
    some (env.ptrWidthBytes, env.ptrWidthBytes, false)
  | .uint w | .int w =>
    some (w.byteSize, w.byteSize, false)
  | .bool =>
    some (1, 1, false)
  | .unit =>
    some (0, 1, false)
  | .adt name =>
    let L := env.adtLayout name
    some (L.size, L.align, L.hasUninitPadding)
  | .param _ | .unmodeled =>
    none

/-- Realized byte size of `ty` in `env`. -/
def tySizeInEnv (env : CompilerRealization) (ty : MirTy) : Option Nat :=
  (tyLayoutInEnv env ty).map (fun (sz, _, _) => sz)

/-- Deterministic `#[repr(C)]` forward offset accumulation recurrence
(`r[layout.repr.c.struct]`, `src/type-layout.md`):
Given the list of field `(size, align, hasPadding)` triples, accumulates:
- `curOffset`: current byte offset before the next field,
- `maxAlign`: running maximum alignment across fields (starting at `1`),
- `offsets`: list of field offsets in declaration order,
- `anyPadding`: `true` if any field has internal padding or if any inter-field
  or trailing alignment step inserts `> 0` padding bytes. -/
def reprCFieldLoop (env : CompilerRealization) :
    List FieldDecl → Nat → Nat → List Nat → Bool →
      Option AdtLayoutRealization
  | [], curOffset, maxAlign, offsets, anyPadding =>
    let totalSize := alignUp curOffset maxAlign
    let trailingPadding := !(totalSize == curOffset)
    some {
      size             := totalSize
      align            := maxAlign
      fieldOffsets     := offsets
      hasUninitPadding := anyPadding || trailingPadding
      nicheBitPattern  := none
    }
  | f :: fs, curOffset, maxAlign, offsets, anyPadding =>
    match tyLayoutInEnv env f.ty with
    | some (fSize, fAlign, fPad) =>
      let alignedOffset := alignUp curOffset fAlign
      let interPadding := !(alignedOffset == curOffset)
      let nextMaxAlign := if maxAlign ≤ fAlign then fAlign else maxAlign
      reprCFieldLoop env fs
        (alignedOffset + fSize)
        nextMaxAlign
        (offsets ++ [alignedOffset])
        (anyPadding || fPad || interPadding)
    | none => none

/-- Deterministic `#[repr(C)]` struct layout computed from `decl.fields` in `env`. -/
def reprCForwardLayout (env : CompilerRealization)
    (decl : AdtDecl) : Option AdtLayoutRealization :=
  reprCFieldLoop env decl.fields 0 1 [] false

/-- Sum of realized field byte sizes for `decl.fields` in `env`. -/
def sumFieldSizes (env : CompilerRealization) : List FieldDecl → Option Nat
  | [] => some 0
  | f :: fs =>
    match tySizeInEnv env f.ty, sumFieldSizes env fs with
    | some sz, some rest => some (sz + rest)
    | _, _ => none

/-- Target pointer width constraint check (`Law 1`). -/
def satisfiesTargetCfg (targetCfg : TargetCfgConstraint) (ptrWidthBytes : Nat) : Bool :=
  (ptrWidthBytes == 2 || ptrWidthBytes == 4 || ptrWidthBytes == 8) &&
  match targetCfg with
  | .any        => true
  | .ptrWidth16 => ptrWidthBytes == 2
  | .ptrWidth32 => ptrWidthBytes == 4
  | .ptrWidth64 => ptrWidthBytes == 8

/-- Per-ADT layout admissibility check in `env` encoding Laws 2, 3, 4, and 5
of the stable Rust Reference (`src/type-layout.md`):
- **Law 2 (`r[layout.properties]`)**: `align` is a power of two (`align ≥ 1`)
  and `size % align == 0`.
- **Law 3 (`r[layout.repr.transparent]`)**: For `#[repr(transparent)]` with
  single field `F`, `env.adtLayout decl.name` has the exact `size`, `align`,
  `fieldOffsets = [0]`, and `hasUninitPadding` of `F` in `env`.
- **Law 4 (`r[layout.repr.c.struct]`)**: For `#[repr(C)]` (`packed = none,
  align = none`), `env.adtLayout decl.name` equals the deterministic forward
  offset accumulation `reprCForwardLayout env decl`.
- **Law 5 (`r[layout.repr.rust]`)**: For `#[repr(Rust)]`, `env.adtLayout decl.name`
  is constrained *only* by Law 2 (`isPowerOfTwo L.align` and `L.size % L.align == 0`),
  `L.fieldOffsets.length == decl.fields.length`, and `sumFieldSizes ≤ L.size`
  (plus if `L.size > sumFieldSizes`, then `L.hasUninitPadding = true`), leaving
  `size`, `align`, `fieldOffsets`, and `hasUninitPadding` free to vary across
  admissible compiler realizations! -/
def checkAdtAdmissible (env : CompilerRealization) (decl : AdtDecl) : Bool :=
  let L := env.adtLayout decl.name
  let universalLaw :=
    isPowerOfTwo L.align && decide (L.size % L.align = 0)
  let reprLaw :=
    match decl.repr with
    | .transparent =>
      match decl.fields with
      | [f] =>
        match tyLayoutInEnv env f.ty with
        | some (fSz, fAlign, fPad) =>
          decide (L.size = fSz) &&
          decide (L.align = fAlign) &&
          decide (L.fieldOffsets = [0]) &&
          decide (L.hasUninitPadding = fPad)
        | none => false
      | _ => false
    | .c none none =>
      match reprCForwardLayout env decl with
      | some expected => decide (L = expected)
      | none => false
    | .c _ _ =>
      universalLaw
    | .primitiveInt w | .cAndInt w =>
      decide (L.size = w.byteSize) &&
      decide (L.align = w.byteSize) &&
      decide (L.hasUninitPadding = false)
    | .rust =>
      match sumFieldSizes env decl.fields with
      | some sumSz =>
        decide (sumSz ≤ L.size) &&
        decide (L.fieldOffsets.length = decl.fields.length) &&
        (if decide (sumSz < L.size) then decide (L.hasUninitPadding = true) else true)
      | none => false
  universalLaw && reprLaw

/-- Executable checker for `ReferenceAdmissible` across `c.adts`. -/
def checkReferenceAdmissible (c : Crate) (targetCfg : TargetCfgConstraint)
    (env : CompilerRealization) : Bool :=
  satisfiesTargetCfg targetCfg env.ptrWidthBytes &&
  c.adts.all (checkAdtAdmissible env)

/-- Normative admissibility predicate `ReferenceAdmissible c targetCfg env : Prop`
encoding the five laws guaranteed by the stable Rust Reference:
1. Target pointer width law (`env.ptrWidthBytes ∈ [2, 4, 8]` and `targetCfg`),
2. Universal layout law (`isPowerOfTwo align ∧ size % align = 0`),
3. `#[repr(transparent)]` law,
4. `#[repr(C)]` forward offset accumulation law, and
5. `#[repr(Rust)]` layout freedom law. -/
def ReferenceAdmissible (c : Crate) (targetCfg : TargetCfgConstraint)
    (env : CompilerRealization) : Prop :=
  satisfiesTargetCfg targetCfg env.ptrWidthBytes = true ∧
  ∀ decl, decl ∈ c.adts → checkAdtAdmissible env decl = true

/-- Helper lemma: `List.all p xs = true` implies `∀ x ∈ xs, p x = true`. -/
theorem list_all_iff_forall {α : Type} (p : α → Bool) :
    ∀ (xs : List α), xs.all p = true ↔ (∀ x, x ∈ xs → p x = true)
  | [] => by
    simp [List.all]
  | x :: xs => by
    simp only [List.all, Bool.and_eq_true, List.mem_cons]
    rw [list_all_iff_forall p xs]
    constructor
    · intro h y hy
      cases hy with
      | inl heq => subst heq; exact h.1
      | inr hmem => exact h.2 y hmem
    · intro h
      exact ⟨h x (Or.inl rfl), fun y hy => h y (Or.inr hy)⟩

/-- Soundness and completeness of the executable checker `checkReferenceAdmissible`
with respect to `ReferenceAdmissible`. -/
theorem checkReferenceAdmissible_iff (c : Crate) (targetCfg : TargetCfgConstraint)
    (env : CompilerRealization) :
    checkReferenceAdmissible c targetCfg env = true ↔
      ReferenceAdmissible c targetCfg env := by
  unfold checkReferenceAdmissible ReferenceAdmissible
  rw [Bool.and_eq_true, list_all_iff_forall]

/-- Soundness direction (`checkReferenceAdmissible_sound`) required by Theorem 5. -/
theorem checkReferenceAdmissible_sound (c : Crate) (targetCfg : TargetCfgConstraint)
    (env : CompilerRealization)
    (h : checkReferenceAdmissible c targetCfg env = true) :
    ReferenceAdmissible c targetCfg env :=
  (checkReferenceAdmissible_iff c targetCfg env).mp h

/-!
### Byte-Level Value Representation and `transmute_copy` in Environment `env`

In environment `env : CompilerRealization`:
- A scalar or padding-free wrapper (`hasUninitPadding = false` and
  `fieldOffsets = [0]`) encodes to `.initBits byteSz bits`.
- An ADT whose realized layout in `env` has `hasUninitPadding = true` or
  non-zero field offset encodes to `.paddedAdtBytes name L.size inner`: its byte
  representation carries uninitialized padding bytes that cannot be soundly read
  as an integer (`u64`), `bool`, or different ADT, **but** can be copied back into
  the *same* ADT (`transmute_copy::<T, T>` or `copy_nonoverlapping::<T>`) within
  the same environment `env`!
-/

/-- Abstract byte representation of a runtime value in realization `env`. -/
inductive ByteRepr where
  /-- `byteSz` fully initialized bytes carrying integer bit pattern `bits`. -/
  | initBits (byteSz : Nat) (bits : Nat)
  /-- `byteSz` bytes representing an instance of `adtName` whose layout in `env`
      contains uninitialized padding bytes (`hasUninitPadding = true`). -/
  | paddedAdtBytes (adtName : String) (byteSz : Nat) (inner : MirVal)
  deriving DecidableEq, Repr

/-- Byte length of a `ByteRepr`. -/
def ByteRepr.byteLen : ByteRepr → Nat
  | .initBits sz _ => sz
  | .paddedAdtBytes _ sz _ => sz

/-- Encode a `MirVal` of type `srcTy` into its `ByteRepr` in realization `env`. -/
def encodeValBytesInEnv (c : Crate) (env : CompilerRealization) :
    MirTy → MirVal → Option ByteRepr
  | .uint .u64, .u64 bits => some (.initBits 8 bits)
  | .uint .u32, .u32 bits => some (.initBits 4 bits)
  | .usize, .usize bits => some (.initBits env.ptrWidthBytes bits)
  | .bool, .bool b => some (.initBits 1 (if b then 1 else 0))
  | .unit, .unit => some (.initBits 0 0)
  | .adt name, .adt name' inner =>
    if decide (name = name') then
      match c.findAdt name with
      | some decl =>
        match decl.payloadTy with
        | some fty =>
          let L := env.adtLayout name
          if decide (L.hasUninitPadding = false) && decide (L.fieldOffsets = [0]) then
            match encodeValBytesInEnv c env fty inner with
            | some (.initBits fSz bits) =>
              if decide (L.size = fSz) then some (.initBits L.size bits) else none
            | _ => none
          else
            some (.paddedAdtBytes name L.size inner)
        | none => none
      | none => none
    else
      none
  | _, _ => none

/-- Decode a `ByteRepr` into a valid `MirVal` of type `dstTy` in realization `env`
with recursion depth `fuel`:
- Reading `.paddedAdtBytes` as a fixed-width integer (`u64`) is immediate UB
  (`none`), because reading uninitialized padding bytes as an integer is UB
  (`r[undefined.validity.scalar]`).
- Reading `.paddedAdtBytes srcName sz inner` at the *same* ADT `dstName == srcName`
  with matching realized size `L.size == sz` reconstructs `.adt dstName inner`
  (preserving uninitialized padding bytes across an untyped byte copy of `T` to `T`). -/
def decodeValBytesInEnv (c : Crate) (env : CompilerRealization) :
    Nat → MirTy → ByteRepr → Option MirVal
  | 0, _, _ => none
  | _ + 1, .uint .u64, .initBits 8 bits => some (.u64 bits)
  | _ + 1, .uint .u32, .initBits 4 bits => some (.u32 bits)
  | _ + 1, .usize, .initBits sz bits =>
    if decide (sz = env.ptrWidthBytes) then some (.usize bits) else none
  | _ + 1, .unit, .initBits 0 _ => some .unit
  | fuel + 1, .adt name, repr =>
    match c.findAdt name with
    | some decl =>
      if decl.allFieldsPubSafe then
        match decl.payloadTy with
        | some fty =>
          let L := env.adtLayout name
          match repr with
          | .initBits sz bits =>
            if decide (L.hasUninitPadding = false) &&
               decide (L.fieldOffsets = [0]) &&
               decide (L.size = sz) then
              (decodeValBytesInEnv c env fuel fty (.initBits sz bits)).map (MirVal.adt name)
            else
              none
          | .paddedAdtBytes srcName sz inner =>
            if decide (name = srcName) && decide (L.size = sz) &&
               !(decide (L.hasUninitPadding = false) && decide (L.fieldOffsets = [0])) then
              some (.adt name inner)
            else
              none
        | none => none
      else
        none
    | none => none
  | _ + 1, _, _ => none

/-- Evaluate `transmute_copy::<srcTy, dstTy>(&srcVal)` in realization `env`. -/
def evalTransmuteCopyInEnv (c : Crate) (env : CompilerRealization)
    (srcTy dstTy : MirTy) (srcVal : MirVal) : Option MirVal :=
  match tySizeInEnv env srcTy, tySizeInEnv env dstTy,
        encodeValBytesInEnv c env srcTy srcVal with
  | some srcSz, some dstSz, some bytes =>
    if decide (srcSz = dstSz) && decide (bytes.byteLen = srcSz) then
      decodeValBytesInEnv c env (c.adts.length + 2) dstTy bytes
    else
      none
  | _, _, _ => none

/-- Exclusive upper bound $2^{8 \cdot w}$ on unsigned `usize` values for pointer
byte width `ptrWidthBytes ∈ {2, 4, 8}`. -/
def usizeModulus (ptrWidthBytes : Nat) : Nat :=
  if ptrWidthBytes == 2 then 65536
  else if ptrWidthBytes == 4 then 4294967296
  else if ptrWidthBytes == 8 then 18446744073709551616
  else 0

/-- Single-step operational evaluation of `MirOp` in realization `env`. -/
def evalOpInEnv (c : Crate) (env : CompilerRealization) :
    MirOp → StepResult Unit Empty MirVal
  | .transmuteCopy srcTy dstTy srcVal =>
    match evalTransmuteCopyInEnv c env srcTy dstTy srcVal with
    | some v => .terminated (.normal v)
    | none => .failed
  | .copyNonOverlapping ty srcVal count =>
    if count == 1 then
      match evalTransmuteCopyInEnv c env ty ty srcVal with
      | some v => .terminated (.normal v)
      | none => .failed
    else
      .failed
  | .sizeOf ty =>
    match tySizeInEnv env ty with
    | some sz => .terminated (.normal (.usize sz))
    | none => .failed
  | .sizeOfEq ty1 ty2 =>
    match tySizeInEnv env ty1, tySizeInEnv env ty2 with
    | some sz1, some sz2 => .terminated (.normal (.bool (sz1 == sz2)))
    | _, _ => .failed
  | .usizeAdd lhs rhs =>
    let bound := usizeModulus env.ptrWidthBytes
    if lhs < bound && rhs < bound && lhs + rhs < bound then
      .terminated (.normal (.usize (lhs + rhs)))
    else
      .failed
  | .branchWithDeadRequiredConst deadConstSucceeded retVal =>
    if env.evalDeadBranchConsts && !deadConstSucceeded then
      .failed
    else
      .terminated (.normal retVal)

/-!
### Defining `Sem_ForwardCompatible` via Both Step-0 `StepResult.choice` and Query-Enriched `ForwardQuery`
-/

/-- Subtype of `CompilerRealization`s satisfying `ReferenceAdmissible c targetCfg`. -/
abbrev AdmissibleEnv (c : Crate) (targetCfg : TargetCfgConstraint) : Type :=
  { env : CompilerRealization // ReferenceAdmissible c targetCfg env }

/-- State of the step-0 `StepResult.choice` machine (`ChoiceState`):
- `.selectEnv`: initial state at step 0 before the demonic choice of
  `env : CompilerRealization` satisfying `ReferenceAdmissible c targetCfg env`.
- `.selected env`: state after step 0 has chosen `env`, ready to execute `MirOp`
  under `evalOpInEnv c env`. -/
inductive ChoiceState where
  | selectEnv
  | selected (env : CompilerRealization)

/-- Lift a unit-state `StepResult` into `ChoiceState` at `.selected env`. -/
def mapStepToChoice (env : CompilerRealization) :
    StepResult Unit Empty MirVal → StepResult ChoiceState Empty MirVal
  | .terminated term => .terminated term
  | .failed => .failed
  | .step obs _ => .step obs (.selected env)
  | .choice _ => .failed

/-- Step-0 `StepResult.choice` small-step machine (`MachineForwardChoice`):
- From `.selectEnv`, takes a demonic `StepResult.choice` over all `.selected env`
  where `ReferenceAdmissible c targetCfg env`.
- From `.selected env`, executes `evalOpInEnv c env op` directly. -/
def MachineForwardChoice (c : Crate) (targetCfg : TargetCfgConstraint) :
    SmallStepMachine MirOp ChoiceState Empty MirVal where
  initState := fun _ s => s = .selectEnv
  step := fun op s r =>
    match s with
    | .selectEnv =>
      r = .choice (fun s' =>
        ∃ env, ReferenceAdmissible c targetCfg env ∧ s' = .selected env)
    | .selected env =>
      r = mapStepToChoice env (evalOpInEnv c env op)

/-- Language packaging of `MachineForwardChoice` (`LangForwardChoice`). -/
def LangForwardChoice (c : Crate) (targetCfg : TargetCfgConstraint) : Language :=
  (MachineForwardChoice c targetCfg).toLanguage

/-- Step-0 `StepResult.choice` behavior semantics (`Sem_ForwardCompatible`). -/
abbrev Sem_ForwardCompatible (c : Crate) (targetCfg : TargetCfgConstraint)
    (op : MirOp) : Behavior ChoiceState (EventualOut Empty MirVal) :=
  (LangForwardChoice c targetCfg).sem op

/-- Deterministic small-step machine for a fixed realization `env` (`MachineEnv`). -/
def MachineEnv (c : Crate) (env : CompilerRealization) :
    SmallStepMachine MirOp Unit Empty MirVal where
  initState := fun _ s => s = ()
  step      := fun op _ r => r = evalOpInEnv c env op

/-- Query-enriched `ForwardQuery` packaging `{ env // ReferenceAdmissible c targetCfg env }`
with `ExecQuery Unit` (`Unit × Nat`), matching the prompt's
`ForwardQuery := { env // ReferenceAdmissible c targetCfg env } × ExecQuery MirState`. -/
abbrev ForwardQuery (c : Crate) (targetCfg : TargetCfgConstraint) : Type :=
  AdmissibleEnv c targetCfg × ExecQuery Unit

/-- Query-enriched `Language` over `ForwardQuery c targetCfg` (`LangForwardQuery`). -/
def LangForwardQuery (c : Crate) (targetCfg : TargetCfgConstraint) : Language where
  Prog  := MirOp
  Query := ForwardQuery c targetCfg
  Out   := ExecOut Unit Empty MirVal
  sem   := fun op (⟨env, _⟩, q) => PrefixBehaviorOf (MachineEnv c env) op q
  dom   := fun op (⟨env, _⟩, q) => (MachineEnv c env).initState op q.init

/-- Query-enriched behavior semantics (`Sem_ForwardCompatible_Query`). -/
abbrev Sem_ForwardCompatible_Query (c : Crate) (targetCfg : TargetCfgConstraint)
    (op : MirOp) :
    Behavior (ForwardQuery c targetCfg) (ExecOut Unit Empty MirVal) :=
  (LangForwardQuery c targetCfg).sem op

/-- Constructive equivalence theorem between Embedding A (`Sem_ForwardCompatible`,
using `StepResult.choice` over `{ env // ReferenceAdmissible c targetCfg env }`
at step 0) and Embedding B (`Sem_ForwardCompatible_Query`, using query-enriched
`ForwardQuery := { env // ReferenceAdmissible c targetCfg env } × ExecQuery Unit`)
for any postcondition `post : MirVal → Prop` on normal return outcomes! -/
def SpecChoiceReturn (c : Crate) (targetCfg : TargetCfgConstraint)
    (post : MirVal → Prop) : (LangForwardChoice c targetCfg).Behavior :=
  (LangForwardChoice c targetCfg).Spec (fun _ out =>
    match out with
    | .terminated _ (.normal v) => post v
    | _ => False)

def SpecQueryReturn (c : Crate) (targetCfg : TargetCfgConstraint)
    (post : MirVal → Prop) : (LangForwardQuery c targetCfg).Behavior :=
  (LangForwardQuery c targetCfg).Spec (fun _ out =>
    match out.outcome with
    | .running _ => True
    | .terminated (.normal v) => post v
    | _ => False)

/-- Exact characterization of `evalOpInEnv c env op`: every `MirOp` steps in
1 step to either `.terminated (.normal v)` or `.failed`. -/
theorem evalOpInEnv_dichotomy (c : Crate) (env : CompilerRealization) (op : MirOp) :
    (∃ v, evalOpInEnv c env op = .terminated (.normal v)) ∨
    evalOpInEnv c env op = .failed := by
  cases op with
  | transmuteCopy srcTy dstTy srcVal =>
    unfold evalOpInEnv
    dsimp only
    cases evalTransmuteCopyInEnv c env srcTy dstTy srcVal with
    | none => exact Or.inr rfl
    | some v => exact Or.inl ⟨v, rfl⟩
  | copyNonOverlapping ty srcVal count =>
    unfold evalOpInEnv
    dsimp only
    cases hc : (count == 1) with
    | false => exact Or.inr rfl
    | true =>
      cases evalTransmuteCopyInEnv c env ty ty srcVal with
      | none => exact Or.inr rfl
      | some v => exact Or.inl ⟨v, rfl⟩
  | sizeOf ty =>
    unfold evalOpInEnv
    dsimp only
    cases tySizeInEnv env ty with
    | none => exact Or.inr rfl
    | some sz => exact Or.inl ⟨.usize sz, rfl⟩
  | sizeOfEq ty1 ty2 =>
    unfold evalOpInEnv
    dsimp only
    cases tySizeInEnv env ty1 with
    | none => exact Or.inr rfl
    | some sz1 =>
      cases tySizeInEnv env ty2 with
      | none => exact Or.inr rfl
      | some sz2 => exact Or.inl ⟨.bool (sz1 == sz2), rfl⟩
  | usizeAdd lhs rhs =>
    unfold evalOpInEnv
    dsimp only
    split
    · exact Or.inl ⟨.usize (lhs + rhs), rfl⟩
    · exact Or.inr rfl
  | branchWithDeadRequiredConst deadConstSucceeded retVal =>
    unfold evalOpInEnv
    dsimp only
    split
    · exact Or.inr rfl
    · exact Or.inl ⟨retVal, rfl⟩

/-- Helper lemma: from `ChoiceState.selected env` when `evalOpInEnv c env op`
terminates, no `(m + 1)`-step execution can reach `.running s_next`. -/
theorem no_running_from_selected_terminated
    (c : Crate) (targetCfg : TargetCfgConstraint)
    (env : CompilerRealization) (op : MirOp) (v : MirVal)
    (h_term : evalOpInEnv c env op = .terminated (.normal v))
    (m : Nat) (tr : List Empty) (s_next : ChoiceState) :
    ¬ ReachesPrefix (MachineForwardChoice c targetCfg).step op (m + 1)
        (ChoiceState.selected env) tr (.running s_next) := by
  intro hreach
  have h_step_eq : ∀ r, (MachineForwardChoice c targetCfg).step op (ChoiceState.selected env) r ↔
      r = .terminated (.normal v) := by
    intro r
    show r = mapStepToChoice env (evalOpInEnv c env op) ↔ r = .terminated (.normal v)
    rw [h_term]
    rfl
  cases hreach with
  | step _ _ _ _ _ _ hst _ =>
    rw [h_step_eq] at hst; cases hst
  | choice _ _ _ _ _ _ hst _ _ =>
    rw [h_step_eq] at hst; cases hst

/-- Helper lemma: from `ChoiceState.selectEnv`, any `(m + 1)`-step execution
reaching `.running s_next` (when every admissible `env` terminates in 1 step)
must have `m = 0` and `s_next = ChoiceState.selected env` for some admissible `env`. -/
theorem running_from_selectEnv_is_selected
    (c : Crate) (targetCfg : TargetCfgConstraint)
    (op : MirOp) (post : MirVal → Prop)
    (h_adm_term : ∀ env, ReferenceAdmissible c targetCfg env →
      ∃ v, evalOpInEnv c env op = .terminated (.normal v) ∧ post v)
    (m : Nat) (tr : List Empty) (s_next : ChoiceState)
    (hreach : ReachesPrefix (MachineForwardChoice c targetCfg).step op (m + 1)
      ChoiceState.selectEnv tr (.running s_next)) :
    ∃ env, ReferenceAdmissible c targetCfg env ∧ s_next = ChoiceState.selected env := by
  cases hreach with
  | step _ _ _ _ _ _ hst _ => cases hst
  | choice _ _ s' branches _ _ hst hbr hreach' =>
    injection hst with hbranches
    subst hbranches
    rcases hbr with ⟨env, h_adm, rfl⟩
    rcases h_adm_term env h_adm with ⟨v, h_term, _⟩
    cases m with
    | zero =>
      cases hreach' with
      | zero => exact ⟨env, h_adm, rfl⟩
    | succ k =>
      exact False.elim
        (no_running_from_selected_terminated c targetCfg env op v h_term k tr s_next hreach')

/-- Constructive equivalence (`↔`) between the step-0 `StepResult.choice`
embedding (`Sem_ForwardCompatible`) and the query-enriched `ForwardQuery`
embedding (`Sem_ForwardCompatible_Query`) whenever at least one
`ReferenceAdmissible` realization exists (`∃ env, ReferenceAdmissible c targetCfg env`). -/
theorem sem_forwardCompatible_choice_iff_query
    (c : Crate) (targetCfg : TargetCfgConstraint)
    (h_nonempty : ∃ env, ReferenceAdmissible c targetCfg env)
    (op : MirOp) (post : MirVal → Prop) :
    (Sem_ForwardCompatible c targetCfg op ≤ SpecChoiceReturn c targetCfg post) ↔
    (Sem_ForwardCompatible_Query c targetCfg op ≤ SpecQueryReturn c targetCfg post) := by
  constructor
  · -- Direction 1: Choice ≤ SpecChoiceReturn → Query ≤ SpecQueryReturn
    intro h_choice ⟨⟨env, h_adm⟩, ⟨initUnit, steps⟩⟩ _
    have ⟨h_def_choice, h_val_choice⟩ := h_choice ChoiceState.selectEnv True.intro
    have h_not_failed : evalOpInEnv c env op ≠ .failed := by
      intro h_fail
      have h_step1 : (MachineForwardChoice c targetCfg).step op ChoiceState.selectEnv
          (.choice (fun s' => ∃ e, ReferenceAdmissible c targetCfg e ∧ s' = ChoiceState.selected e)) := rfl
      have h_step2 : (MachineForwardChoice c targetCfg).step op (ChoiceState.selected env) .failed := by
        show StepResult.failed = mapStepToChoice env (evalOpInEnv c env op)
        rw [h_fail]
        rfl
      have h_reach2 : ReachesPrefix (MachineForwardChoice c targetCfg).step op
          2 ChoiceState.selectEnv [] .failed :=
        ReachesPrefix.choice 1 ChoiceState.selectEnv (ChoiceState.selected env)
          (fun s' => ∃ e, ReferenceAdmissible c targetCfg e ∧ s' = ChoiceState.selected e)
          [] .failed h_step1 ⟨env, h_adm, rfl⟩
          (ReachesPrefix.failed 0 (ChoiceState.selected env) h_step2)
      exact h_def_choice rfl 2 [] .failed h_reach2
    rcases evalOpInEnv_dichotomy c env op with ⟨v, h_term⟩ | h_fail
    · have h_post : post v := by
        have h_step1 : (MachineForwardChoice c targetCfg).step op ChoiceState.selectEnv
            (.choice (fun s' => ∃ e, ReferenceAdmissible c targetCfg e ∧ s' = ChoiceState.selected e)) := rfl
        have h_step2 : (MachineForwardChoice c targetCfg).step op (ChoiceState.selected env)
            (.terminated (.normal v)) := by
          show StepResult.terminated (.normal v) = mapStepToChoice env (evalOpInEnv c env op)
          rw [h_term]
          rfl
        have h_reach2 : ReachesPrefix (MachineForwardChoice c targetCfg).step op
            2 ChoiceState.selectEnv [] (.terminated (.normal v)) :=
          ReachesPrefix.choice 1 ChoiceState.selectEnv (ChoiceState.selected env)
            (fun s' => ∃ e, ReferenceAdmissible c targetCfg e ∧ s' = ChoiceState.selected e)
            [] (.terminated (.normal v)) h_step1 ⟨env, h_adm, rfl⟩
            (ReachesPrefix.terminated 0 (ChoiceState.selected env) (.normal v) h_step2)
        exact h_val_choice (.terminated [] (.normal v)) ⟨rfl, ⟨2, h_reach2⟩⟩
      refine ⟨?_, ?_⟩
      · intro _ tr out hreach
        cases hreach with
        | zero => exact True.intro
        | step _ _ _ _ _ _ hst _ =>
          change _ = evalOpInEnv c env op at hst
          rw [h_term] at hst; cases hst
        | choice _ _ _ _ _ _ hst _ _ =>
          change _ = evalOpInEnv c env op at hst
          rw [h_term] at hst; cases hst
        | emptyChoice _ _ _ hst _ =>
          change _ = evalOpInEnv c env op at hst
          rw [h_term] at hst; cases hst
        | terminated _ _ _ _ => exact True.intro
        | failed _ _ hst =>
          change _ = evalOpInEnv c env op at hst
          rw [h_term] at hst; cases hst
        | noStep _ _ hno =>
          exact False.elim (hno ⟨evalOpInEnv c env op, rfl⟩)
      · intro ⟨tr, out⟩ ⟨_, hreach⟩
        cases hreach with
        | zero => exact True.intro
        | step _ _ _ _ _ _ hst _ =>
          change _ = evalOpInEnv c env op at hst
          rw [h_term] at hst; cases hst
        | choice _ _ _ _ _ _ hst _ _ =>
          change _ = evalOpInEnv c env op at hst
          rw [h_term] at hst; cases hst
        | emptyChoice _ _ _ hst _ =>
          change _ = evalOpInEnv c env op at hst
          rw [h_term] at hst; cases hst
        | terminated _ _ term hst =>
          change StepResult.terminated term = evalOpInEnv c env op at hst
          rw [h_term] at hst
          injection hst with hterm
          subst hterm
          exact h_post
        | failed _ _ hst =>
          change _ = evalOpInEnv c env op at hst
          rw [h_term] at hst; cases hst
        | noStep _ _ hno =>
          exact False.elim (hno ⟨evalOpInEnv c env op, rfl⟩)
    · exact False.elim (h_not_failed h_fail)
  · -- Direction 2: Query ≤ SpecQueryReturn → Choice ≤ SpecChoiceReturn
    intro h_query s _
    have h_adm_term : ∀ env, ReferenceAdmissible c targetCfg env →
        ∃ v, evalOpInEnv c env op = .terminated (.normal v) ∧ post v := by
      intro env h_adm
      have ⟨h_def_q, h_val_q⟩ :=
        h_query (⟨env, h_adm⟩, { init := (), steps := 1 }) True.intro
      rcases evalOpInEnv_dichotomy c env op with ⟨v, h_term⟩ | h_fail
      · refine ⟨v, h_term, ?_⟩
        have h_reach1 : ReachesPrefix (MachineEnv c env).step op 1 () []
            (.terminated (.normal v)) :=
          ReachesPrefix.terminated 0 () (.normal v) h_term.symm
        exact h_val_q ⟨[], .terminated (.normal v)⟩ ⟨rfl, h_reach1⟩
      · have h_reach_fail : ReachesPrefix (MachineEnv c env).step op 1 () [] .failed :=
          ReachesPrefix.failed 0 () h_fail.symm
        exact False.elim (h_def_q rfl [] .failed h_reach_fail)
    refine ⟨?_, ?_⟩
    · intro hs_init n tr out hreach
      subst hs_init
      cases hreach with
      | zero => exact True.intro
      | step _ _ _ _ _ _ hst _ => cases hst
      | choice m _ s' branches _ _ hst hbr hreach' =>
        injection hst with hbranches
        subst hbranches
        rcases hbr with ⟨env, h_adm, rfl⟩
        rcases h_adm_term env h_adm with ⟨v, h_term, _⟩
        have h_step_env : ∀ r, (MachineForwardChoice c targetCfg).step op (ChoiceState.selected env) r ↔
            r = .terminated (.normal v) := by
          intro r
          show r = mapStepToChoice env (evalOpInEnv c env op) ↔ r = .terminated (.normal v)
          rw [h_term]
          rfl
        cases hreach' with
        | zero => exact True.intro
        | step _ _ _ _ _ _ hst2 _ =>
          rw [h_step_env] at hst2; cases hst2
        | choice _ _ _ _ _ _ hst2 _ _ =>
          rw [h_step_env] at hst2; cases hst2
        | emptyChoice _ _ _ hst2 _ =>
          rw [h_step_env] at hst2; cases hst2
        | terminated _ _ _ _ => exact True.intro
        | failed _ _ hst2 =>
          rw [h_step_env] at hst2; cases hst2
        | noStep _ _ hno =>
          exact False.elim (hno ⟨.terminated (.normal v), (h_step_env _).mpr rfl⟩)
      | emptyChoice _ _ branches hst hemp =>
        injection hst with hbranches
        subst hbranches
        rcases h_nonempty with ⟨env₀, h_adm₀⟩
        exact False.elim (hemp ⟨ChoiceState.selected env₀, env₀, h_adm₀, rfl⟩)
      | terminated _ _ _ hst => cases hst
      | failed _ _ hst => cases hst
      | noStep _ _ hno =>
        exact False.elim (hno ⟨.choice (fun s' =>
          ∃ env, ReferenceAdmissible c targetCfg env ∧ s' = ChoiceState.selected env), rfl⟩)
    · intro out ⟨hs_init, h_ev⟩
      subst hs_init
      cases out with
      | terminated tr term =>
        rcases h_ev with ⟨n, hreach⟩
        cases hreach with
        | step _ _ _ _ _ _ hst _ => cases hst
        | terminated _ _ _ hst => cases hst
        | choice m _ s' branches _ _ hst hbr hreach' =>
          injection hst with hbranches
          subst hbranches
          rcases hbr with ⟨env, h_adm, rfl⟩
          rcases h_adm_term env h_adm with ⟨v, h_term, h_post⟩
          have h_step_env : ∀ r, (MachineForwardChoice c targetCfg).step op (ChoiceState.selected env) r ↔
              r = .terminated (.normal v) := by
            intro r
            show r = mapStepToChoice env (evalOpInEnv c env op) ↔ r = .terminated (.normal v)
            rw [h_term]
            rfl
          cases hreach' with
          | step _ _ _ _ _ _ hst2 _ =>
            rw [h_step_env] at hst2; cases hst2
          | choice _ _ _ _ _ _ hst2 _ _ =>
            rw [h_step_env] at hst2; cases hst2
          | terminated _ _ term' hst2 =>
            rw [h_step_env] at hst2
            injection hst2 with hterm
            subst hterm
            exact h_post
      | diverges tr =>
        rcases h_ev with ⟨n, s_run, hreach, traj, htraj0, htrajStep⟩
        cases hreach with
        | zero =>
          rcases htrajStep 0 with ⟨m0, hreach0⟩
          rw [htraj0] at hreach0
          rcases running_from_selectEnv_is_selected c targetCfg op post h_adm_term
            m0 [] (traj 1) hreach0 with ⟨env, h_adm, h_traj1⟩
          rcases h_adm_term env h_adm with ⟨v, h_term, _⟩
          rcases htrajStep 1 with ⟨m1, hreach1⟩
          rw [h_traj1] at hreach1
          exact no_running_from_selected_terminated c targetCfg env op v h_term
            m1 [] (traj 2) hreach1
        | step _ _ _ _ _ _ hst _ => cases hst
        | choice k _ s' branches _ _ hst hbr hreach' =>
          rcases running_from_selectEnv_is_selected c targetCfg op post h_adm_term
            k tr s_run (ReachesPrefix.choice k ChoiceState.selectEnv s' branches tr (.running s_run) hst hbr hreach')
            with ⟨env, h_adm, h_srun⟩
          rcases h_adm_term env h_adm with ⟨v, h_term, _⟩
          rcases htrajStep 0 with ⟨m0, hreach0⟩
          rw [htraj0, h_srun] at hreach0
          exact no_running_from_selected_terminated c targetCfg env op v h_term
            m0 [] (traj 1) hreach0
      | reacts tr =>
        rcases h_ev with ⟨htr_ne, n, s_run, hreach, traj, segTrace, htraj0, htrajStep⟩
        cases hreach with
        | zero => exact False.elim (htr_ne rfl)
        | step _ _ _ _ _ _ hst _ => cases hst
        | choice k _ s' branches _ _ hst hbr hreach' =>
          rcases running_from_selectEnv_is_selected c targetCfg op post h_adm_term
            k tr s_run (ReachesPrefix.choice k ChoiceState.selectEnv s' branches tr (.running s_run) hst hbr hreach')
            with ⟨env, h_adm, h_srun⟩
          rcases h_adm_term env h_adm with ⟨v, h_term, _⟩
          rcases htrajStep 0 with ⟨_, m0, hreach0⟩
          rw [htraj0, h_srun] at hreach0
          exact no_running_from_selected_terminated c targetCfg env op v h_term
            m0 (segTrace 0) (traj 1) hreach0

/-- Helper lemma: if for every `env` satisfying `ReferenceAdmissible c targetCfg env`,
`evalOpInEnv c env op = .terminated (.normal v)` with `post v`, then
`Sem_ForwardCompatible c targetCfg op ≤ SpecChoiceReturn c targetCfg post` and
`Sem_ForwardCompatible c targetCfg op ≤ safeSpec (LangForwardChoice c targetCfg)`. -/
theorem model3_universal_success_le_spec
    (c : Crate) (targetCfg : TargetCfgConstraint)
    (h_nonempty : ∃ env, ReferenceAdmissible c targetCfg env)
    (op : MirOp) (post : MirVal → Prop)
    (h_all : ∀ env, ReferenceAdmissible c targetCfg env →
      ∃ v, evalOpInEnv c env op = .terminated (.normal v) ∧ post v) :
    Sem_ForwardCompatible c targetCfg op ≤ SpecChoiceReturn c targetCfg post ∧
    Sem_ForwardCompatible c targetCfg op ≤ safeSpec (LangForwardChoice c targetCfg) := by
  have h_query : Sem_ForwardCompatible_Query c targetCfg op ≤
      SpecQueryReturn c targetCfg post := by
    intro ⟨⟨env, h_adm⟩, ⟨initUnit, steps⟩⟩ _
    rcases h_all env h_adm with ⟨v, h_term, h_post⟩
    refine ⟨?_, ?_⟩
    · intro _ tr out hreach
      cases hreach with
      | zero => exact True.intro
      | step _ _ _ _ _ _ hst _ =>
        change _ = evalOpInEnv c env op at hst; rw [h_term] at hst; cases hst
      | choice _ _ _ _ _ _ hst _ _ =>
        change _ = evalOpInEnv c env op at hst; rw [h_term] at hst; cases hst
      | emptyChoice _ _ _ hst _ =>
        change _ = evalOpInEnv c env op at hst; rw [h_term] at hst; cases hst
      | terminated _ _ _ _ => exact True.intro
      | failed _ _ hst =>
        change _ = evalOpInEnv c env op at hst; rw [h_term] at hst; cases hst
      | noStep _ _ hno =>
        exact False.elim (hno ⟨evalOpInEnv c env op, rfl⟩)
    · intro ⟨tr, out⟩ ⟨_, hreach⟩
      cases hreach with
      | zero => exact True.intro
      | step _ _ _ _ _ _ hst _ =>
        change _ = evalOpInEnv c env op at hst; rw [h_term] at hst; cases hst
      | choice _ _ _ _ _ _ hst _ _ =>
        change _ = evalOpInEnv c env op at hst; rw [h_term] at hst; cases hst
      | emptyChoice _ _ _ hst _ =>
        change _ = evalOpInEnv c env op at hst; rw [h_term] at hst; cases hst
      | terminated _ _ term hst =>
        change StepResult.terminated term = evalOpInEnv c env op at hst
        rw [h_term] at hst
        injection hst with hterm
        subst hterm
        exact h_post
      | failed _ _ hst =>
        change _ = evalOpInEnv c env op at hst; rw [h_term] at hst; cases hst
      | noStep _ _ hno =>
        exact False.elim (hno ⟨evalOpInEnv c env op, rfl⟩)
  have h_choice := (sem_forwardCompatible_choice_iff_query c targetCfg h_nonempty op post).mpr h_query
  have h_safe : Sem_ForwardCompatible c targetCfg op ≤ safeSpec (LangForwardChoice c targetCfg) := by
    intro s hs
    have ⟨h_def, _⟩ := h_choice s hs
    exact ⟨h_def, fun _ _ => True.intro⟩
  exact ⟨h_choice, h_safe⟩

/-- Helper lemma: if there exists a witness realization `env` satisfying
`ReferenceAdmissible c targetCfg env` in which `evalOpInEnv c env op = .failed`,
then `Sem_ForwardCompatible c targetCfg op` reaches `.failed` and does NOT
refine `safeSpec`. -/
theorem model3_witness_failure_not_le_safeSpec
    (c : Crate) (targetCfg : TargetCfgConstraint)
    (env : CompilerRealization)
    (h_adm : ReferenceAdmissible c targetCfg env)
    (op : MirOp)
    (h_fail : evalOpInEnv c env op = .failed) :
    ReachesPrefix (MachineForwardChoice c targetCfg).step op 2 ChoiceState.selectEnv [] .failed ∧
    ¬ (Sem_ForwardCompatible c targetCfg op ≤ safeSpec (LangForwardChoice c targetCfg)) := by
  have h_step1 : (MachineForwardChoice c targetCfg).step op ChoiceState.selectEnv
      (.choice (fun s' => ∃ e, ReferenceAdmissible c targetCfg e ∧ s' = ChoiceState.selected e)) := rfl
  have h_step2 : (MachineForwardChoice c targetCfg).step op (ChoiceState.selected env) .failed := by
    show StepResult.failed = mapStepToChoice env (evalOpInEnv c env op)
    rw [h_fail]
    rfl
  have h_reach2 : ReachesPrefix (MachineForwardChoice c targetCfg).step op
      2 ChoiceState.selectEnv [] .failed :=
    ReachesPrefix.choice 1 ChoiceState.selectEnv (ChoiceState.selected env)
      (fun s' => ∃ e, ReferenceAdmissible c targetCfg e ∧ s' = ChoiceState.selected e)
      [] .failed h_step1 ⟨env, h_adm, rfl⟩
      (ReachesPrefix.failed 0 (ChoiceState.selected env) h_step2)
  refine ⟨h_reach2, ?_⟩
  intro h_le
  have ⟨h_def, _⟩ := h_le ChoiceState.selectEnv True.intro
  exact h_def rfl 2 [] .failed h_reach2

/-!
### Concrete `ReferenceAdmissible` Realizations `env_8`, `env_16`, and `env_16bit`
-/

/-- Standard 8-byte unpadded layout (`size = 8, align = 8, fieldOffsets = [0],
hasUninitPadding = false`). -/
def layout8Unpadded : AdtLayoutRealization where
  size             := 8
  align            := 8
  fieldOffsets     := [0]
  hasUninitPadding := false

/-- Padded 16-byte layout for a single-field `#[repr(Rust)]` struct
(`size = 16, align = 8, fieldOffsets = [0], hasUninitPadding = true`), modeling
a conforming Rust compiler or `-Z randomize-layout` realization that inserts 8
bytes of uninitialized padding. -/
def layout16Padded : AdtLayoutRealization where
  size             := 16
  align            := 8
  fieldOffsets     := [0]
  hasUninitPadding := true

/-- Standard 8-byte layout for 2-field `Pair(u32, u32)`. -/
def layoutPair8 : AdtLayoutRealization where
  size             := 8
  align            := 4
  fieldOffsets     := [0, 4]
  hasUninitPadding := false

/-- Realization `env_8`: 64-bit target (`ptrWidthBytes = 8`) where
`ReprRustWrapper` happens to have `size = 8, hasUninitPadding = false` (matching
`rustc 1.98.0`'s unrandomized default). -/
def env_8 : CompilerRealization where
  ptrWidthBytes := 8
  adtLayout := fun name =>
    if name == "Pair" then layoutPair8
    else layout8Unpadded

/-- Realization `env_16`: 64-bit target (`ptrWidthBytes = 8`) where
`ReprRustWrapper` (`#[repr(Rust)]`) has `size = 16, hasUninitPadding = true`,
while `ReprTransparentWrapper` and `ReprCWrapper` have their Reference-mandated
8-byte unpadded layout. -/
def env_16 : CompilerRealization where
  ptrWidthBytes := 8
  adtLayout := fun name =>
    if name == "ReprRustWrapper" then layout16Padded
    else if name == "Pair" then layoutPair8
    else layout8Unpadded

/-- Realization `env_16bit`: 16-bit target (`ptrWidthBytes = 2`, i.e., 16-bit
`usize`) with 8-byte `u64` wrappers. -/
def env_16bit : CompilerRealization where
  ptrWidthBytes := 2
  adtLayout := fun name =>
    if name == "Pair" then layoutPair8
    else layout8Unpadded

/-- Proof that `env_8` is `ReferenceAdmissible` for `testCrate` under both
`.any` and `.ptrWidth64`. -/
theorem env_8_admissible_any :
    ReferenceAdmissible testCrate .any env_8 :=
  checkReferenceAdmissible_sound testCrate .any env_8 rfl

theorem env_8_admissible_ptr64 :
    ReferenceAdmissible testCrate .ptrWidth64 env_8 :=
  checkReferenceAdmissible_sound testCrate .ptrWidth64 env_8 rfl

/-- Proof that `env_16` is `ReferenceAdmissible` for `testCrate` under both
`.any` and `.ptrWidth64`. -/
theorem env_16_admissible_any :
    ReferenceAdmissible testCrate .any env_16 :=
  checkReferenceAdmissible_sound testCrate .any env_16 rfl

theorem env_16_admissible_ptr64 :
    ReferenceAdmissible testCrate .ptrWidth64 env_16 :=
  checkReferenceAdmissible_sound testCrate .ptrWidth64 env_16 rfl

/-- Proof that `env_16bit` is `ReferenceAdmissible` for `testCrate` under `.any`. -/
theorem env_16bit_admissible_any :
    ReferenceAdmissible testCrate .any env_16bit :=
  checkReferenceAdmissible_sound testCrate .any env_16bit rfl

/-!
### Five Core Theorems of Model 3
-/

/-- **Model 3 Theorem 1 (`model3_rejects_repr_rust_u64_transmute`)**:
1. Both `env_8` (`size = 8, hasUninitPadding = false`) and `env_16`
   (`size = 16, hasUninitPadding = true`) satisfy `ReferenceAdmissible testCrate .any`.
2. In `env_8`, `transmute_copy::<u64, ReprRustWrapper>(&x)` succeeds, whereas in
   `env_16` it steps to `StepResult.err` (`.failed`).
3. Consequently, `Sem_ForwardCompatible testCrate .any` rejects
   `transmute_copy::<u64, ReprRustWrapper>(&x)` (`¬ (Sem_ForwardCompatible ... ≤ safeSpec)`). -/
theorem model3_rejects_repr_rust_u64_transmute (x : Nat) :
    ReferenceAdmissible testCrate .any env_8 ∧
    ReferenceAdmissible testCrate .any env_16 ∧
    evalOpInEnv testCrate env_8
      (.transmuteCopy (.uint .u64) (.adt "ReprRustWrapper") (.u64 x)) =
      .terminated (.normal (.adt "ReprRustWrapper" (.u64 x))) ∧
    evalOpInEnv testCrate env_16
      (.transmuteCopy (.uint .u64) (.adt "ReprRustWrapper") (.u64 x)) =
      StepResult.err ∧
    ¬ (Sem_ForwardCompatible testCrate .any
        (.transmuteCopy (.uint .u64) (.adt "ReprRustWrapper") (.u64 x)) ≤
        safeSpec (LangForwardChoice testCrate .any)) := by
  have h_fail := (model3_witness_failure_not_le_safeSpec
    testCrate .any env_16 env_16_admissible_any
    (.transmuteCopy (.uint .u64) (.adt "ReprRustWrapper") (.u64 x)) rfl).2
  exact ⟨env_8_admissible_any, env_16_admissible_any, rfl, rfl, h_fail⟩

/-- Key structural lemma from Law 3 (`#[repr(transparent)]`) of
`ReferenceAdmissible`: in **every** `ReferenceAdmissible` environment `env`,
`env.adtLayout "ReprTransparentWrapper"` has `size = 8`, `align = 8`,
`fieldOffsets = [0]`, and `hasUninitPadding = false`. -/
theorem reprTransparentWrapper_layout_in_all_admissible
    (targetCfg : TargetCfgConstraint) (env : CompilerRealization)
    (h_adm : ReferenceAdmissible testCrate targetCfg env) :
    (env.adtLayout "ReprTransparentWrapper").size = 8 ∧
    (env.adtLayout "ReprTransparentWrapper").align = 8 ∧
    (env.adtLayout "ReprTransparentWrapper").fieldOffsets = [0] ∧
    (env.adtLayout "ReprTransparentWrapper").hasUninitPadding = false := by
  have h_decl := h_adm.2 reprTransparentWrapperDecl (by decide)
  unfold checkAdtAdmissible reprTransparentWrapperDecl tyLayoutInEnv IntWidth.byteSize at h_decl
  dsimp only at h_decl
  have h_right := (Bool.and_eq_true _ _).mp h_decl |>.2
  have h1 := (Bool.and_eq_true _ _).mp h_right
  have h2 := (Bool.and_eq_true _ _).mp h1.1
  have h3 := (Bool.and_eq_true _ _).mp h2.1
  exact ⟨of_decide_eq_true h3.1, of_decide_eq_true h3.2,
         of_decide_eq_true h2.2, of_decide_eq_true h1.2⟩

/-- Key structural lemma from Law 4 (`#[repr(C)]`) of `ReferenceAdmissible`: in
**every** `ReferenceAdmissible` environment `env`, `env.adtLayout "ReprCWrapper"`
equals `layout8Unpadded` (`size = 8, align = 8, fieldOffsets = [0],
hasUninitPadding = false`). -/
theorem reprCWrapper_layout_in_all_admissible
    (targetCfg : TargetCfgConstraint) (env : CompilerRealization)
    (h_adm : ReferenceAdmissible testCrate targetCfg env) :
    env.adtLayout "ReprCWrapper" = layout8Unpadded := by
  have h_decl := h_adm.2 reprCWrapperDecl (by decide)
  unfold checkAdtAdmissible reprCWrapperDecl reprCForwardLayout reprCFieldLoop
    tyLayoutInEnv IntWidth.byteSize alignUp at h_decl
  dsimp only at h_decl
  have h_right := (Bool.and_eq_true _ _).mp h_decl |>.2
  exact of_decide_eq_true h_right

/-- **Model 3 Theorem 2 (`model3_accepts_repr_transparent_and_padding_free_repr_c_transmute`)**:
Across **all** `env` satisfying `ReferenceAdmissible testCrate .any env`,
both `transmute_copy::<u64, ReprTransparentWrapper>(&x)` and
`transmute_copy::<u64, ReprCWrapper>(&x)` succeed and refine `safeSpec`
(and their exact value postconditions). -/
theorem model3_accepts_repr_transparent_and_padding_free_repr_c_transmute (x : Nat) :
    (∀ env, ReferenceAdmissible testCrate .any env →
      evalOpInEnv testCrate env
        (.transmuteCopy (.uint .u64) (.adt "ReprTransparentWrapper") (.u64 x)) =
        .terminated (.normal (.adt "ReprTransparentWrapper" (.u64 x))) ∧
      evalOpInEnv testCrate env
        (.transmuteCopy (.uint .u64) (.adt "ReprCWrapper") (.u64 x)) =
        .terminated (.normal (.adt "ReprCWrapper" (.u64 x)))) ∧
    Sem_ForwardCompatible testCrate .any
      (.transmuteCopy (.uint .u64) (.adt "ReprTransparentWrapper") (.u64 x)) ≤
      safeSpec (LangForwardChoice testCrate .any) ∧
    Sem_ForwardCompatible testCrate .any
      (.transmuteCopy (.uint .u64) (.adt "ReprCWrapper") (.u64 x)) ≤
      safeSpec (LangForwardChoice testCrate .any) := by
  have h_each : ∀ env, ReferenceAdmissible testCrate .any env →
      evalOpInEnv testCrate env
        (.transmuteCopy (.uint .u64) (.adt "ReprTransparentWrapper") (.u64 x)) =
        .terminated (.normal (.adt "ReprTransparentWrapper" (.u64 x))) ∧
      evalOpInEnv testCrate env
        (.transmuteCopy (.uint .u64) (.adt "ReprCWrapper") (.u64 x)) =
        .terminated (.normal (.adt "ReprCWrapper" (.u64 x))) := by
    intro env h_adm
    rcases reprTransparentWrapper_layout_in_all_admissible .any env h_adm with
      ⟨h_sz, _, h_off, h_pad⟩
    have h_c := reprCWrapper_layout_in_all_admissible .any env h_adm
    constructor
    · unfold evalOpInEnv evalTransmuteCopyInEnv tySizeInEnv tyLayoutInEnv
        encodeValBytesInEnv decodeValBytesInEnv ByteRepr.byteLen IntWidth.byteSize
      dsimp only [Crate.findAdt, testCrate, List.find?, List.length,
        reprRustWrapperDecl, reprTransparentWrapperDecl,
        AdtDecl.allFieldsPubSafe, List.all, AdtDecl.payloadTy]
      rw [h_sz, h_off, h_pad]
      rfl
    · unfold evalOpInEnv evalTransmuteCopyInEnv tySizeInEnv tyLayoutInEnv
        encodeValBytesInEnv decodeValBytesInEnv ByteRepr.byteLen IntWidth.byteSize
      dsimp only [Crate.findAdt, testCrate, List.find?,
        reprRustWrapperDecl, reprTransparentWrapperDecl, reprCWrapperDecl,
        AdtDecl.allFieldsPubSafe, List.all, AdtDecl.payloadTy]
      rw [h_c]
      rfl
  have h_trans_safe := (model3_universal_success_le_spec
    testCrate .any ⟨env_8, env_8_admissible_any⟩
    (.transmuteCopy (.uint .u64) (.adt "ReprTransparentWrapper") (.u64 x))
    (fun v => v = .adt "ReprTransparentWrapper" (.u64 x))
    (fun env h_adm => ⟨_, (h_each env h_adm).1, rfl⟩)).2
  have h_c_safe := (model3_universal_success_le_spec
    testCrate .any ⟨env_8, env_8_admissible_any⟩
    (.transmuteCopy (.uint .u64) (.adt "ReprCWrapper") (.u64 x))
    (fun v => v = .adt "ReprCWrapper" (.u64 x))
    (fun env h_adm => ⟨_, (h_each env h_adm).2, rfl⟩)).2
  exact ⟨h_each, h_trans_safe, h_c_safe⟩

/-- Key lemma for Theorem 3: in **every** `ReferenceAdmissible` environment `env`,
`ReprRustWrapper` has `L.size ≥ 8`. When `L.hasUninitPadding = false`,
Law 5 (`if 8 < L.size then decide (L.hasUninitPadding = true) else true`) forces `L.size = 8`! -/
theorem reprRustWrapper_size_eq_8_when_unpadded
    (targetCfg : TargetCfgConstraint) (env : CompilerRealization)
    (h_adm : ReferenceAdmissible testCrate targetCfg env)
    (h_unpad : (env.adtLayout "ReprRustWrapper").hasUninitPadding = false) :
    (env.adtLayout "ReprRustWrapper").size = 8 := by
  have h_decl := h_adm.2 reprRustWrapperDecl (by decide)
  unfold checkAdtAdmissible reprRustWrapperDecl sumFieldSizes
    tySizeInEnv tyLayoutInEnv IntWidth.byteSize at h_decl
  dsimp only [Option.map] at h_decl
  have h_right := (Bool.and_eq_true _ _).mp h_decl |>.2
  have h1 := (Bool.and_eq_true _ _).mp h_right
  have h2 := (Bool.and_eq_true _ _).mp h1.1
  have h_le : 8 ≤ (env.adtLayout "ReprRustWrapper").size := of_decide_eq_true h2.1
  have h_if := h1.2
  cases h_lt : decide (8 < (env.adtLayout "ReprRustWrapper").size) with
  | true =>
    rw [h_lt, h_unpad] at h_if
    cases h_if
  | false =>
    have h_nlt : ¬ (8 < (env.adtLayout "ReprRustWrapper").size) := of_decide_eq_false h_lt
    exact Nat.le_antisymm (Nat.le_of_not_lt h_nlt) h_le

/-- **Model 3 Theorem 3 (`model3_accepts_reflexive_repr_rust_transmute_and_copy`)**:
Across **all** `env` satisfying `ReferenceAdmissible testCrate .any env`:
1. Reflexive `transmute_copy::<ReprRustWrapper, ReprRustWrapper>(&w)` (for any
   valid `w = .adt "ReprRustWrapper" (.u64 x)`) succeeds and returns `w` unchanged,
2. `copy_nonoverlapping::<ReprRustWrapper>(&w, &mut dst, 1)` succeeds and
   returns `w` unchanged, and
3. `size_of::<ReprRustWrapper>() == size_of::<ReprRustWrapper>()` evaluates to
   `.bool true`,
because within every single `env`, the source and destination type share the
identical realized layout `env.adtLayout "ReprRustWrapper"`. -/
theorem model3_accepts_reflexive_repr_rust_transmute_and_copy (x : Nat) :
    let w := MirVal.adt "ReprRustWrapper" (.u64 x)
    let opReflexiveTransmute :=
      MirOp.transmuteCopy (.adt "ReprRustWrapper") (.adt "ReprRustWrapper") w
    let opCopyNonOverlapping :=
      MirOp.copyNonOverlapping (.adt "ReprRustWrapper") w 1
    let opSizeOfEq :=
      MirOp.sizeOfEq (.adt "ReprRustWrapper") (.adt "ReprRustWrapper")
    (∀ env, ReferenceAdmissible testCrate .any env →
      evalOpInEnv testCrate env opReflexiveTransmute = .terminated (.normal w) ∧
      evalOpInEnv testCrate env opCopyNonOverlapping = .terminated (.normal w) ∧
      evalOpInEnv testCrate env opSizeOfEq = .terminated (.normal (.bool true))) ∧
    Sem_ForwardCompatible testCrate .any opReflexiveTransmute ≤
      SpecChoiceReturn testCrate .any (fun v => v = w) ∧
    Sem_ForwardCompatible testCrate .any opCopyNonOverlapping ≤
      SpecChoiceReturn testCrate .any (fun v => v = w) ∧
    Sem_ForwardCompatible testCrate .any opSizeOfEq ≤
      SpecChoiceReturn testCrate .any (fun v => v = .bool true) := by
  dsimp only
  have h_eval_all : ∀ env, ReferenceAdmissible testCrate .any env →
      evalOpInEnv testCrate env
        (.transmuteCopy (.adt "ReprRustWrapper") (.adt "ReprRustWrapper")
          (.adt "ReprRustWrapper" (.u64 x))) =
        .terminated (.normal (.adt "ReprRustWrapper" (.u64 x))) ∧
      evalOpInEnv testCrate env
        (.copyNonOverlapping (.adt "ReprRustWrapper")
          (.adt "ReprRustWrapper" (.u64 x)) 1) =
        .terminated (.normal (.adt "ReprRustWrapper" (.u64 x))) ∧
      evalOpInEnv testCrate env
        (.sizeOfEq (.adt "ReprRustWrapper") (.adt "ReprRustWrapper")) =
        .terminated (.normal (.bool true)) := by
    intro env h_adm
    have h_trans : evalTransmuteCopyInEnv testCrate env
        (.adt "ReprRustWrapper") (.adt "ReprRustWrapper")
        (.adt "ReprRustWrapper" (.u64 x)) =
        some (.adt "ReprRustWrapper" (.u64 x)) := by
      change (
        let L := env.adtLayout "ReprRustWrapper"
        match some L.size, some L.size,
          (if (decide (L.hasUninitPadding = false) && decide (L.fieldOffsets = [0])) = true then
            if decide (L.size = 8) = true then some (ByteRepr.initBits L.size x) else none
           else some (ByteRepr.paddedAdtBytes "ReprRustWrapper" L.size (.u64 x))) with
        | some srcSz, some dstSz, some bytes =>
          if (decide (srcSz = dstSz) && decide (bytes.byteLen = srcSz)) = true then
            decodeValBytesInEnv testCrate env 6 (.adt "ReprRustWrapper") bytes
          else none
        | _, _, _ => none) = some (.adt "ReprRustWrapper" (.u64 x))
      dsimp only
      cases h_cond :
          (decide ((env.adtLayout "ReprRustWrapper").hasUninitPadding = false) &&
           decide ((env.adtLayout "ReprRustWrapper").fieldOffsets = [0])) with
      | true =>
        have h_and := (Bool.and_eq_true _ _).mp h_cond
        have h_unpad : (env.adtLayout "ReprRustWrapper").hasUninitPadding = false :=
          of_decide_eq_true h_and.1
        have h_sz8 := reprRustWrapper_size_eq_8_when_unpadded .any env h_adm h_unpad
        rw [h_sz8]
        change (if (decide (8 = 8) && decide (8 = 8)) = true then
          if (decide ((env.adtLayout "ReprRustWrapper").hasUninitPadding = false) &&
              decide ((env.adtLayout "ReprRustWrapper").fieldOffsets = [0]) &&
              decide ((env.adtLayout "ReprRustWrapper").size = 8)) = true then
            some (MirVal.adt "ReprRustWrapper" (MirVal.u64 x))
          else none
        else none) = some (MirVal.adt "ReprRustWrapper" (MirVal.u64 x))
        rw [h_cond, h_sz8]
        rfl
      | false =>
        have h_sz_eq : @decide ((env.adtLayout "ReprRustWrapper").size =
            (env.adtLayout "ReprRustWrapper").size) (Nat.decEq _ _) = true :=
          @decide_eq_true _ (Nat.decEq _ _) rfl
        change (if (decide ((env.adtLayout "ReprRustWrapper").size =
                    (env.adtLayout "ReprRustWrapper").size) &&
                  decide ((env.adtLayout "ReprRustWrapper").size =
                    (env.adtLayout "ReprRustWrapper").size)) = true then
          if (decide ("ReprRustWrapper" = "ReprRustWrapper") &&
              decide ((env.adtLayout "ReprRustWrapper").size =
                (env.adtLayout "ReprRustWrapper").size) &&
              !(decide ((env.adtLayout "ReprRustWrapper").hasUninitPadding = false) &&
                decide ((env.adtLayout "ReprRustWrapper").fieldOffsets = [0]))) = true then
            some (MirVal.adt "ReprRustWrapper" (MirVal.u64 x))
          else none
        else none) = some (MirVal.adt "ReprRustWrapper" (MirVal.u64 x))
        rw [h_cond, h_sz_eq]
        rfl
    refine ⟨?_, ?_, ?_⟩
    · unfold evalOpInEnv; dsimp only; rw [h_trans]
    · change (match evalTransmuteCopyInEnv testCrate env
          (.adt "ReprRustWrapper") (.adt "ReprRustWrapper")
          (.adt "ReprRustWrapper" (.u64 x)) with
        | some v => StepResult.terminated (.normal v)
        | none => StepResult.failed) =
        StepResult.terminated (.normal (.adt "ReprRustWrapper" (.u64 x)))
      rw [h_trans]
    · unfold evalOpInEnv tySizeInEnv tyLayoutInEnv
      dsimp only [Option.map]
      rw [beq_self_eq_true]
  have h1 := (model3_universal_success_le_spec
    testCrate .any ⟨env_8, env_8_admissible_any⟩
    (.transmuteCopy (.adt "ReprRustWrapper") (.adt "ReprRustWrapper")
      (.adt "ReprRustWrapper" (.u64 x)))
    (fun v => v = .adt "ReprRustWrapper" (.u64 x))
    (fun env h_adm => ⟨_, (h_eval_all env h_adm).1, rfl⟩)).1
  have h2 := (model3_universal_success_le_spec
    testCrate .any ⟨env_8, env_8_admissible_any⟩
    (.copyNonOverlapping (.adt "ReprRustWrapper")
      (.adt "ReprRustWrapper" (.u64 x)) 1)
    (fun v => v = .adt "ReprRustWrapper" (.u64 x))
    (fun env h_adm => ⟨_, (h_eval_all env h_adm).2.1, rfl⟩)).1
  have h3 := (model3_universal_success_le_spec
    testCrate .any ⟨env_8, env_8_admissible_any⟩
    (.sizeOfEq (.adt "ReprRustWrapper") (.adt "ReprRustWrapper"))
    (fun v => v = .bool true)
    (fun env h_adm => ⟨_, (h_eval_all env h_adm).2.2, rfl⟩)).1
  exact ⟨h_eval_all, h1, h2, h3⟩

/-- **Model 3 Theorem 4 (`model3_target_parametric_vs_cfg_gated_usize`)**:
1. Safe `1usize + 1usize` succeeds and produces `.usize 2` across **all**
   `ReferenceAdmissible` environments (`ptrWidthBytes ∈ {2, 4, 8}`), refining `safeSpec`.
2. `60000usize + 10000usize` steps to overflow `StepResult.err` (`.failed`) on
   16-bit targets (`env_16bit`, `ptrWidthBytes = 2`) under unconstrained
   `TargetCfgConstraint.any`, so `Sem_ForwardCompatible testCrate .any` rejects it.
3. Under `TargetCfgConstraint.ptrWidth64` (`#[cfg(target_pointer_width = "64")]`),
   `60000usize + 10000usize` succeeds and produces `.usize 70000` across **all**
   admissible environments, refining `safeSpec`. -/
theorem model3_target_parametric_vs_cfg_gated_usize :
    (∀ env, ReferenceAdmissible testCrate .any env →
      evalOpInEnv testCrate env (.usizeAdd 1 1) =
        .terminated (.normal (.usize 2))) ∧
    Sem_ForwardCompatible testCrate .any (.usizeAdd 1 1) ≤
      safeSpec (LangForwardChoice testCrate .any) ∧
    evalOpInEnv testCrate env_16bit (.usizeAdd 60000 10000) =
      StepResult.err ∧
    ¬ (Sem_ForwardCompatible testCrate .any (.usizeAdd 60000 10000) ≤
        safeSpec (LangForwardChoice testCrate .any)) ∧
    (∀ env, ReferenceAdmissible testCrate .ptrWidth64 env →
      evalOpInEnv testCrate env (.usizeAdd 60000 10000) =
        .terminated (.normal (.usize 70000))) ∧
    Sem_ForwardCompatible testCrate .ptrWidth64 (.usizeAdd 60000 10000) ≤
      safeSpec (LangForwardChoice testCrate .ptrWidth64) := by
  have h_small : ∀ env, ReferenceAdmissible testCrate .any env →
      evalOpInEnv testCrate env (.usizeAdd 1 1) =
        .terminated (.normal (.usize 2)) := by
    intro env h_adm
    have h_ptr := h_adm.1
    unfold satisfiesTargetCfg at h_ptr
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h_ptr
    rcases h_ptr.1 with (h2 | h4) | h8
    · unfold evalOpInEnv usizeModulus; rw [h2]; rfl
    · unfold evalOpInEnv usizeModulus; rw [h4]; rfl
    · unfold evalOpInEnv usizeModulus; rw [h8]; rfl
  have h_small_safe := (model3_universal_success_le_spec
    testCrate .any ⟨env_8, env_8_admissible_any⟩
    (.usizeAdd 1 1) (fun v => v = .usize 2)
    (fun env h_adm => ⟨_, h_small env h_adm, rfl⟩)).2
  have h_large_fail := (model3_witness_failure_not_le_safeSpec
    testCrate .any env_16bit env_16bit_admissible_any
    (.usizeAdd 60000 10000) rfl).2
  have h_large_64 : ∀ env, ReferenceAdmissible testCrate .ptrWidth64 env →
      evalOpInEnv testCrate env (.usizeAdd 60000 10000) =
        .terminated (.normal (.usize 70000)) := by
    intro env h_adm
    have h_ptr := h_adm.1
    unfold satisfiesTargetCfg at h_ptr
    simp only [Bool.and_eq_true, beq_iff_eq] at h_ptr
    have h8 : env.ptrWidthBytes = 8 := h_ptr.2
    unfold evalOpInEnv usizeModulus
    rw [h8]
    rfl
  have h_large_64_safe := (model3_universal_success_le_spec
    testCrate .ptrWidth64 ⟨env_8, env_8_admissible_ptr64⟩
    (.usizeAdd 60000 10000) (fun v => v = .usize 70000)
    (fun env h_adm => ⟨_, h_large_64 env h_adm, rfl⟩)).2
  exact ⟨h_small, h_small_safe, rfl, h_large_fail, h_large_64, h_large_64_safe⟩

/-!
### Model 3 Theorem 5: Refinement Bridge (`Sem_PinnedRustcEnv ≤ Sem_ForwardCompatible`) & Explicit Authority Stratification
-/

/-- Lift a single pinned compiler realization `env_rustc` into the `ChoiceState`
behavior lattice (`Sem_PinnedRustcEnv c env_rustc op`), where step 0
deterministically selects `env_rustc` (`StepResult.silent (.selected env_rustc)`). -/
def MachinePinnedRustcEnv (c : Crate) (env_rustc : CompilerRealization) :
    SmallStepMachine MirOp ChoiceState Empty MirVal where
  initState := fun _ s => s = .selectEnv
  step := fun op s r =>
    match s with
    | .selectEnv =>
      r = .choice (fun s' => s' = .selected env_rustc)
    | .selected env =>
      r = mapStepToChoice env (evalOpInEnv c env op)

/-- Behavior of the pinned-`rustc` realization `env_rustc` on `ChoiceState`. -/
abbrev Sem_PinnedRustcEnv (c : Crate) (env_rustc : CompilerRealization)
    (op : MirOp) : Behavior ChoiceState (EventualOut Empty MirVal) :=
  ((MachinePinnedRustcEnv c env_rustc).toLanguage).sem op

/-- Prefix reachability monotonicity: when `ReferenceAdmissible c targetCfg env_rustc`
holds, every `n`-step execution prefix of `MachinePinnedRustcEnv c env_rustc` from
`s` is also a valid `n`-step execution prefix of `MachineForwardChoice c targetCfg`
(except `.stuck` from `.emptyChoice`, which is impossible for `MachinePinnedRustcEnv`
because `∃ s', s' = .selected env_rustc` holds). -/
theorem reachesPrefix_pinned_imp_forward
    (c : Crate) (targetCfg : TargetCfgConstraint)
    (env_rustc : CompilerRealization)
    (h_adm : ReferenceAdmissible c targetCfg env_rustc)
    (op : MirOp) :
    ∀ n s tr out,
      ReachesPrefix (MachinePinnedRustcEnv c env_rustc).step op n s tr out →
      ReachesPrefix (MachineForwardChoice c targetCfg).step op n s tr out := by
  intro n s tr out hreach
  induction hreach with
  | zero s =>
    exact ReachesPrefix.zero s
  | step m s s' obs tr out hst _ ih =>
    cases s with
    | selectEnv => cases hst
    | selected env =>
      exact ReachesPrefix.step m (.selected env) s' obs tr out hst ih
  | choice m s s' branches tr out hst hbr _ ih =>
    cases s with
    | selectEnv =>
      injection hst with hbranches
      subst hbranches
      subst hbr
      exact ReachesPrefix.choice m .selectEnv (.selected env_rustc)
        (fun s' => ∃ env, ReferenceAdmissible c targetCfg env ∧ s' = .selected env)
        tr out rfl ⟨env_rustc, h_adm, rfl⟩ ih
    | selected env =>
      exact ReachesPrefix.choice m (.selected env) s' branches tr out hst hbr ih
  | emptyChoice m s branches hst hemp =>
    cases s with
    | selectEnv =>
      injection hst with hbranches
      subst hbranches
      exact False.elim (hemp ⟨ChoiceState.selected env_rustc, rfl⟩)
    | selected env =>
      exact ReachesPrefix.emptyChoice m (ChoiceState.selected env) branches hst hemp
  | terminated m s term hst =>
    cases s with
    | selectEnv => cases hst
    | selected env =>
      exact ReachesPrefix.terminated m (ChoiceState.selected env) term hst
  | failed m s hst =>
    cases s with
    | selectEnv => cases hst
    | selected env =>
      exact ReachesPrefix.failed m (ChoiceState.selected env) hst
  | noStep m s hno =>
    cases s with
    | selectEnv =>
      exact False.elim (hno ⟨.choice (fun s' => s' = ChoiceState.selected env_rustc), rfl⟩)
    | selected env =>
      exact ReachesPrefix.noStep m (ChoiceState.selected env) hno

/-- Explicit authority stratification (`AssumptionPolicy` / `ForwardTCBItem`)
distinguishing normative Rust Reference guarantees from compiler-specific or
documented-intent assumptions:
- `.normativeRustReference`: relies solely on `ReferenceAdmissible c targetCfg`
  (zero compiler-specific layout assumptions).
- `.rustcDocumentedIntent name`: relies on a documented `rustc` layout decision
  (such as `Option<&T>` null-pointer optimization or a specific `rustc` layout
  beyond the Reference), audited as an explicit waiver in `VerificationResult`.
- `.pinnedRustcRealization`: narrows verification to a single pinned `env_rustc`
  realization. -/
inductive ForwardTCBItem where
  | rustcLowering (fnName : String)
  | rustcDocumentedIntent (adtName : String)
  | pinnedRustcRealization (rustcCommit : String)
  deriving DecidableEq, Repr

/-- Strict forward-compatible trust policy: permits only unavoidable `rustcLowering`
assumptions, rejecting any unwaived `.rustcDocumentedIntent` or
`.pinnedRustcRealization` assumption unless explicitly opted in. -/
def forwardCompatibleTrustPolicy : TrustPolicy ForwardTCBItem where
  isAllowed := fun item =>
    match item with
    | .rustcLowering _ => True
    | .rustcDocumentedIntent _ => False
    | .pinnedRustcRealization _ => False

/-- Documented-intent trust policy (e.g., Zerocopy's opt-in documented-intent
tier): additionally permits audited `.rustcDocumentedIntent` items, while still
forbidding arbitrary unwaived `.pinnedRustcRealization` layout dependence. -/
def documentedIntentTrustPolicy : TrustPolicy ForwardTCBItem where
  isAllowed := fun item =>
    match item with
    | .rustcLowering _ => True
    | .rustcDocumentedIntent _ => True
    | .pinnedRustcRealization _ => False

/-- **Model 3 Theorem 5 (`model3_refinement_bridge_and_tcb_stratification`)**:
1. (`checkReferenceAdmissible_sound`): Any compiler realization `env_rustc`
   passing `checkReferenceAdmissible c targetCfg env_rustc = true` satisfies
   `ReferenceAdmissible c targetCfg env_rustc`.
2. (`Sem_PinnedRustcEnv ≤ Sem_ForwardCompatible`): For any `env_rustc` passing
   `checkReferenceAdmissible c targetCfg env_rustc = true`,
   `Sem_PinnedRustcEnv c env_rustc op ≤ Sem_ForwardCompatible c targetCfg op`
   in Anneal's `Behavior` refinement lattice!
3. (Refinement Preservation by Transitivity): Any specification `spec` proved
   against `Sem_ForwardCompatible c targetCfg op`
   (`Sem_ForwardCompatible c targetCfg op ≤ spec`) automatically holds for
   `Sem_PinnedRustcEnv c env_rustc op` (`Sem_PinnedRustcEnv c env_rustc op ≤ spec`)
   by `Preorder.le_trans`!
4. (TCB Stratification): `forwardCompatibleTrustPolicy` rejects
   `.pinnedRustcRealization` and `.rustcDocumentedIntent`, whereas
   `documentedIntentTrustPolicy` admits `.rustcDocumentedIntent` while still
   rejecting `.pinnedRustcRealization`. -/
theorem model3_refinement_bridge_and_tcb_stratification
    (c : Crate) (targetCfg : TargetCfgConstraint)
    (env_rustc : CompilerRealization)
    (h_check : checkReferenceAdmissible c targetCfg env_rustc = true)
    (op : MirOp)
    (spec : (LangForwardChoice c targetCfg).Behavior) :
    ReferenceAdmissible c targetCfg env_rustc ∧
    (Sem_PinnedRustcEnv c env_rustc op ≤ Sem_ForwardCompatible c targetCfg op) ∧
    (Sem_ForwardCompatible c targetCfg op ≤ spec →
      Sem_PinnedRustcEnv c env_rustc op ≤ spec) ∧
    (¬ forwardCompatibleTrustPolicy.isAllowed (.pinnedRustcRealization "1.98.0") ∧
     ¬ forwardCompatibleTrustPolicy.isAllowed (.rustcDocumentedIntent "ReprRustWrapper") ∧
     documentedIntentTrustPolicy.isAllowed (.rustcDocumentedIntent "OptionRef") ∧
     ¬ documentedIntentTrustPolicy.isAllowed (.pinnedRustcRealization "1.98.0")) := by
  have h_adm : ReferenceAdmissible c targetCfg env_rustc :=
    checkReferenceAdmissible_sound c targetCfg env_rustc h_check
  have h_refines :
      Sem_PinnedRustcEnv c env_rustc op ≤ Sem_ForwardCompatible c targetCfg op := by
    intro s h_def_fwd
    refine ⟨?_, ?_⟩
    · intro hs_init n tr out hreach_pin
      exact h_def_fwd hs_init n tr out
        (reachesPrefix_pinned_imp_forward c targetCfg env_rustc h_adm op n s tr out hreach_pin)
    · intro out ⟨hs_init, h_ev_pin⟩
      refine ⟨hs_init, ?_⟩
      cases out with
      | terminated tr term =>
        rcases h_ev_pin with ⟨n, hreach_pin⟩
        exact ⟨n, reachesPrefix_pinned_imp_forward c targetCfg env_rustc h_adm op
          n s tr (.terminated term) hreach_pin⟩
      | diverges tr =>
        rcases h_ev_pin with ⟨n, s_run, hreach_pin, traj, htraj0, htrajStep⟩
        refine ⟨n, s_run,
          reachesPrefix_pinned_imp_forward c targetCfg env_rustc h_adm op
            n s tr (.running s_run) hreach_pin,
          traj, htraj0, fun k => ?_⟩
        rcases htrajStep k with ⟨m, hstep_pin⟩
        exact ⟨m, reachesPrefix_pinned_imp_forward c targetCfg env_rustc h_adm op
          (m + 1) (traj k) [] (.running (traj (k + 1))) hstep_pin⟩
      | reacts tr =>
        rcases h_ev_pin with ⟨htr, n, s_run, hreach_pin, traj, segTrace, htraj0, htrajStep⟩
        refine ⟨htr, n, s_run,
          reachesPrefix_pinned_imp_forward c targetCfg env_rustc h_adm op
            n s tr (.running s_run) hreach_pin,
          traj, segTrace, htraj0, fun k => ?_⟩
        rcases htrajStep k with ⟨hseg, m, hstep_pin⟩
        exact ⟨hseg, m, reachesPrefix_pinned_imp_forward c targetCfg env_rustc h_adm op
          (m + 1) (traj k) (segTrace k) (.running (traj (k + 1))) hstep_pin⟩
  refine ⟨h_adm, h_refines, fun h_spec => Preorder.le_trans h_refines h_spec, ?_⟩
  exact ⟨id, id, True.intro, id⟩

/-- Dead-branch `Body::required_consts` discrimination theorem (`evalDeadBranchConsts`):
When a function contains a failing `required_consts` item inside a dynamically
dead `if false` branch (`.branchWithDeadRequiredConst false (.u64 42)`):
- In `env_8` (`evalDeadBranchConsts = true`, eager monomorphization PME checks),
  evaluation fails closed to `StepResult.err` (`.failed`).
- Consequently, `Sem_ForwardCompatible` rejects unguarded dead-branch PME
  failures unless `required_consts` succeeds across all admissible environments. -/
theorem model3_dead_branch_required_consts_discrimination :
    evalOpInEnv testCrate env_8
      (.branchWithDeadRequiredConst false (.u64 42)) = StepResult.err ∧
    evalOpInEnv testCrate { env_8 with evalDeadBranchConsts := false }
      (.branchWithDeadRequiredConst false (.u64 42)) =
      .terminated (.normal (.u64 42)) ∧
    ¬ (Sem_ForwardCompatible testCrate .any
        (.branchWithDeadRequiredConst false (.u64 42)) ≤
        safeSpec (LangForwardChoice testCrate .any)) := by
  have h_fail := (model3_witness_failure_not_le_safeSpec
    testCrate .any env_8 env_8_admissible_any
    (.branchWithDeadRequiredConst false (.u64 42)) rfl).2
  exact ⟨rfl, rfl, h_fail⟩

/-!
## 6. Normative Layout, Target ABI, and `UbChecks` Extensions

Formalizes four boundary properties of `ReferenceAdmissible` and Anneal's
refinement spine:

- **Extension Theorem A (`repr_rust_zst_vs_non_zst_discrimination`)**:
  Under `r[layout.repr.rust.struct-zst]` (`rust-lang/reference@82da570b`,
  `src/type-layout.md`), a `#[repr(Rust)]` struct whose fields all have
  `size == 0` (`struct RustZstWrapper(())`) IS normatively guaranteed to have
  `size == 0` and `hasUninitPadding = false` across all `ReferenceAdmissible`
  environments, whereas a `#[repr(Rust)]` struct with a non-ZST field
  (`ReprRustWrapper(u64)`) is not guaranteed `size == 8`.
- **Extension Theorem B (`repr_c_target_u64_alignment_and_aggregate_align_boundary`)**:
  Proves both:
  1. `reprC_withU64_padding_depends_on_target_i64_align`: Under
     `i64AlignBytes ∈ {4, 8}` (`4` on `i686-unknown-linux-gnu` vs. `8` on
     `x86_64-unknown-linux-gnu`), `reprCForwardLayout` for
     `#[repr(C)] struct WithU64 { a: u32, b: u64 }` yields
     `(size = 12, hasUninitPadding = false)` when `i64AlignBytes = 4` and
     `(size = 16, hasUninitPadding = true)` when `i64AlignBytes = 8`, so
     `transmute_copy::<WithU64, [u8; 16]>` steps to `StepResult.err` on both
     targets (from size mismatch on `i686` and uninitialized padding on `x86_64`).
  2. `custom_target_aggregate_align_gt_one_violates_transparent_law`: When a
     custom target JSON sets `aggregateAlignBytes = 4` (`-a:32`), `rustc`'s
     `univariant_biased` (`compiler/rustc_abi/src/layout.rs:1106-1114`) inflates
     `#[repr(transparent)] struct TransU8(u8)` to `size = 4, align = 4`,
     violating `ReferenceAdmissible` (`r[layout.repr.transparent]`), justifying
     the target precondition `ValidTargetSpec` (`aggregateAlignBytes = 1`).
- **Extension Theorem C (`in_memory_transmute_vs_extern_c_fn_abi_discrimination`)**:
  Models `callAbi : String → CallPassMode` in `CompilerRealization` (constrained
  by `ReferenceAdmissible` to match the inner field's `CallPassMode` for
  `.transparent` per `r[layout.repr.transparent.layout-abi]`, while allowed to
  be `.indirectSret` vs. `.directReg` for `.c` and `.rust` due to
  `ReprFlags::ABI_UNOPTIMIZABLE` on `i686` and `x86_64-pc-windows-msvc`), and
  proves that `Sem_ForwardCompatible` **accepts** `transmuteFnPtr` for
  `ReprTransparentWrapper` while **rejecting** `transmuteFnPtr` for
  `ReprCWrapper` (even though `transmute_copy` of values is accepted for both).
- **Extension Theorem D (`ub_checks_dual_soundness_trap_and_repair`)**:
  Formalizes the three interpretations of
  `assert_unsafe_precondition!(check_language_ub / check_library_ub, cond)` +
  `panic_nounwind_fmt` on Anneal's `WellFormed` / `Behavior` spine, proving that
  both `(UbChecks = true, panic_nounwind_fmt ↦ .terminated .unwind)` and
  `(UbChecks = false, skipping precondition_check)` falsely certify UB code as
  safe (`≤ safeUnwindOrNormalSpec` when `cond = false`), whereas the sound
  interpretation `(UbChecks = true, panic_nounwind_fmt ↦ StepResult.failed)`
  refines `safeUnwindOrNormalSpec` **if and only if** `cond = true`.
-/

/-!
### 6.1 Extension Theorem A: `r[layout.repr.rust.struct-zst]` vs. Non-ZST `#[repr(Rust)]`
-/

/-- `#[repr(Rust)] pub struct RustZstWrapper(pub ());` -/
def rustZstWrapperDecl : AdtDecl where
  name   := "RustZstWrapper"
  repr   := .rust
  fields := [{ ty := .unit, access := .pubSafe }]

/-- Test crate augmented with `RustZstWrapper(())`. -/
def testCrateWithZst : Crate where
  adts := [
    rustZstWrapperDecl,
    reprRustWrapperDecl,
    reprTransparentWrapperDecl,
    reprCWrapperDecl,
    pairDeclFull
  ]

/-- Refined per-ADT admissibility check incorporating `r[layout.repr.rust.struct-zst]`
(`rust-lang/reference@82da570b`, `type-layout.html:421-424`):
> "A struct with the default representation where all fields have a size of 0
> will also have a size of 0."

When `decl.repr == .rust` and `sumFieldSizes env decl.fields = some 0`,
`L.size` is forced to `0` and `L.hasUninitPadding` is forced to `false`. -/
def checkAdtAdmissibleWithZstLaw (env : CompilerRealization) (decl : AdtDecl) : Bool :=
  checkAdtAdmissible env decl &&
  match decl.repr with
  | .rust =>
    match sumFieldSizes env decl.fields with
    | some 0 => decide ((env.adtLayout decl.name).size = 0) &&
                decide ((env.adtLayout decl.name).hasUninitPadding = false)
    | _ => true
  | _ => true

/-- Normative admissibility predicate refined with `r[layout.repr.rust.struct-zst]`. -/
def ReferenceAdmissibleWithZstLaw (c : Crate) (targetCfg : TargetCfgConstraint)
    (env : CompilerRealization) : Prop :=
  satisfiesTargetCfg targetCfg env.ptrWidthBytes = true ∧
  ∀ decl, decl ∈ c.adts → checkAdtAdmissibleWithZstLaw env decl = true

/-- Canonical 0-byte unpadded ZST layout (`size = 0, align = 1, fieldOffsets = [0],
hasUninitPadding = false`). -/
def layout0Zst : AdtLayoutRealization where
  size             := 0
  align            := 1
  fieldOffsets     := [0]
  hasUninitPadding := false

/-- Realization `env_8_zst`: gives `RustZstWrapper` its Reference-mandated 0-byte
layout and `ReprRustWrapper` its 8-byte unpadded layout. -/
def env_8_zst : CompilerRealization where
  ptrWidthBytes := 8
  adtLayout := fun name =>
    if name == "RustZstWrapper" then layout0Zst
    else if name == "Pair" then layoutPair8
    else layout8Unpadded

/-- Realization `env_16_zst`: gives `RustZstWrapper` its Reference-mandated 0-byte
layout while giving `ReprRustWrapper(u64)` its valid 16-byte padded layout. -/
def env_16_zst : CompilerRealization where
  ptrWidthBytes := 8
  adtLayout := fun name =>
    if name == "RustZstWrapper" then layout0Zst
    else if name == "ReprRustWrapper" then layout16Padded
    else if name == "Pair" then layoutPair8
    else layout8Unpadded

/-- Executable checker for `ReferenceAdmissibleWithZstLaw`. -/
def checkReferenceAdmissibleWithZstLaw (c : Crate) (targetCfg : TargetCfgConstraint)
    (env : CompilerRealization) : Bool :=
  satisfiesTargetCfg targetCfg env.ptrWidthBytes &&
  c.adts.all (checkAdtAdmissibleWithZstLaw env)

theorem checkReferenceAdmissibleWithZstLaw_sound
    (c : Crate) (targetCfg : TargetCfgConstraint) (env : CompilerRealization)
    (h : checkReferenceAdmissibleWithZstLaw c targetCfg env = true) :
    ReferenceAdmissibleWithZstLaw c targetCfg env := by
  unfold checkReferenceAdmissibleWithZstLaw ReferenceAdmissibleWithZstLaw at *
  rw [Bool.and_eq_true, list_all_iff_forall] at h
  exact h

theorem env_8_zst_admissible :
    ReferenceAdmissibleWithZstLaw testCrateWithZst .any env_8_zst :=
  checkReferenceAdmissibleWithZstLaw_sound testCrateWithZst .any env_8_zst rfl

theorem env_16_zst_admissible :
    ReferenceAdmissibleWithZstLaw testCrateWithZst .any env_16_zst :=
  checkReferenceAdmissibleWithZstLaw_sound testCrateWithZst .any env_16_zst rfl

/-- **Extension Theorem A (`repr_rust_zst_vs_non_zst_discrimination`)**:
Under `ReferenceAdmissibleWithZstLaw` (`r[layout.repr.rust.struct-zst]`):
1. Across **all** admissible realizations `env`, `RustZstWrapper(())` is
   guaranteed to have `size = 0`, `hasUninitPadding = false`, and
   `evalOpInEnv testCrateWithZst env (.sizeOf (.adt "RustZstWrapper")) =
   .terminated (.normal (.usize 0))`.
2. By contrast, both `env_8_zst` (`size = 8`) and `env_16_zst` (`size = 16`)
   satisfy `ReferenceAdmissibleWithZstLaw testCrateWithZst .any`, refuting
   `size_of::<ReprRustWrapper>() == 8` in `env_16_zst`. -/
theorem repr_rust_zst_vs_non_zst_discrimination :
    (∀ env, ReferenceAdmissibleWithZstLaw testCrateWithZst .any env →
      (env.adtLayout "RustZstWrapper").size = 0 ∧
      (env.adtLayout "RustZstWrapper").hasUninitPadding = false ∧
      evalOpInEnv testCrateWithZst env (.sizeOf (.adt "RustZstWrapper")) =
        .terminated (.normal (.usize 0))) ∧
    ReferenceAdmissibleWithZstLaw testCrateWithZst .any env_8_zst ∧
    ReferenceAdmissibleWithZstLaw testCrateWithZst .any env_16_zst ∧
    evalOpInEnv testCrateWithZst env_8_zst (.sizeOf (.adt "ReprRustWrapper")) =
      .terminated (.normal (.usize 8)) ∧
    evalOpInEnv testCrateWithZst env_16_zst (.sizeOf (.adt "ReprRustWrapper")) =
      .terminated (.normal (.usize 16)) ∧
    (env_16_zst.adtLayout "ReprRustWrapper").size ≠ 8 := by
  refine ⟨?_, env_8_zst_admissible, env_16_zst_admissible, rfl, rfl, by decide⟩
  intro env h_adm
  have h_decl := h_adm.2 rustZstWrapperDecl (by decide)
  unfold checkAdtAdmissibleWithZstLaw rustZstWrapperDecl sumFieldSizes
    tySizeInEnv tyLayoutInEnv at h_decl
  dsimp only [Option.map] at h_decl
  have h_zst := (Bool.and_eq_true _ _).mp h_decl |>.2
  have h_pair := (Bool.and_eq_true _ _).mp h_zst
  have h_sz0 : (env.adtLayout "RustZstWrapper").size = 0 := of_decide_eq_true h_pair.1
  have h_pad : (env.adtLayout "RustZstWrapper").hasUninitPadding = false :=
    of_decide_eq_true h_pair.2
  refine ⟨h_sz0, h_pad, ?_⟩
  unfold evalOpInEnv tySizeInEnv tyLayoutInEnv
  dsimp only [Option.map]
  rw [h_sz0]

/-!
### 6.2 Extension Theorem B: Target `u64` Alignment (`i64AlignBytes ∈ {4, 8}`) & `aggregateAlignBytes` Boundary
-/

/-- `#[repr(C)] pub struct WithU64 { pub a: u32, pub b: u64 }` -/
def withU64Decl : AdtDecl where
  name   := "WithU64"
  repr   := .c none none
  fields := [
    { ty := .uint .u32, access := .pubSafe },
    { ty := .uint .u64, access := .pubSafe }
  ]

/-- Target-parameterized scalar `(size, align, hasUninitPadding)` where
`u64`/`i64` has byte alignment `i64AlignBytes` (`4` on `i686-unknown-linux-gnu`
vs. `8` on `x86_64-unknown-linux-gnu` across built-in
`rustc_target` specifications). -/
def tyLayoutWithI64Align (i64AlignBytes : Nat) : MirTy → Option (Nat × Nat × Bool)
  | .uint .u64 | .int .i64 => some (8, i64AlignBytes, false)
  | .uint w | .int w => some (w.byteSize, w.byteSize, false)
  | .bool => some (1, 1, false)
  | .unit => some (0, 1, false)
  | _ => none

/-- Target-parameterized `#[repr(C)]` forward offset accumulation recurrence
using `i64AlignBytes`. -/
def reprCFieldLoopWithI64Align (i64AlignBytes : Nat) :
    List FieldDecl → Nat → Nat → List Nat → Bool →
      Option AdtLayoutRealization
  | [], curOffset, maxAlign, offsets, anyPadding =>
    let totalSize := alignUp curOffset maxAlign
    let trailingPadding := !(totalSize == curOffset)
    some {
      size             := totalSize
      align            := maxAlign
      fieldOffsets     := offsets
      hasUninitPadding := anyPadding || trailingPadding
      nicheBitPattern  := none
    }
  | f :: fs, curOffset, maxAlign, offsets, anyPadding =>
    match tyLayoutWithI64Align i64AlignBytes f.ty with
    | some (fSize, fAlign, fPad) =>
      let alignedOffset := alignUp curOffset fAlign
      let interPadding := !(alignedOffset == curOffset)
      let nextMaxAlign := if maxAlign ≤ fAlign then fAlign else maxAlign
      reprCFieldLoopWithI64Align i64AlignBytes fs
        (alignedOffset + fSize)
        nextMaxAlign
        (offsets ++ [alignedOffset])
        (anyPadding || fPad || interPadding)
    | none => none

/-- Compute the `#[repr(C)]` layout of `decl` on a target with `i64AlignBytes`. -/
def reprCForwardLayoutWithI64Align (i64AlignBytes : Nat)
    (decl : AdtDecl) : Option AdtLayoutRealization :=
  reprCFieldLoopWithI64Align i64AlignBytes decl.fields 0 1 [] false

/-- Evaluate `transmute_copy::<WithU64, [u8; 16]>` on a target with
`i64AlignBytes`: succeeds only if `WithU64` has realized `size == 16` AND
`hasUninitPadding == false` (since reading uninitialized padding bytes into
initialized `[u8; 16]` is UB). -/
def evalTransmuteWithU64ToBytes16 (i64AlignBytes : Nat) :
    StepResult Unit Empty MirVal :=
  match reprCForwardLayoutWithI64Align i64AlignBytes withU64Decl with
  | some L =>
    if decide (L.size = 16) && decide (L.hasUninitPadding = false) then
      .terminated (.normal (.usize 16))
    else
      .failed
  | none => .failed

/-- **Theorem B.1 (`reprC_withU64_padding_depends_on_target_i64_align`)**:
1. On `i686-unknown-linux-gnu` (`i64AlignBytes = 4`), `reprCForwardLayout` for
   `#[repr(C)] struct WithU64 { a: u32, b: u64 }` yields `size = 12, align = 4,
   fieldOffsets = [0, 4], hasUninitPadding = false`.
2. On `x86_64-unknown-linux-gnu` (`i64AlignBytes = 8`), `reprCForwardLayout` for
   `WithU64` yields `size = 16, align = 8, fieldOffsets = [0, 8],
   hasUninitPadding = true` (4 bytes of inter-field padding at offsets `4..8`).
3. Consequently, across every valid target `i64AlignBytes ∈ [4, 8]`,
   `transmute_copy::<WithU64, [u8; 16]>` steps to `StepResult.err` (from size
   mismatch `12 ≠ 16` when `i64AlignBytes = 4`, and from uninitialized padding
   when `i64AlignBytes = 8`). -/
theorem reprC_withU64_padding_depends_on_target_i64_align :
    reprCForwardLayoutWithI64Align 4 withU64Decl =
      some {
        size := 12
        align := 4
        fieldOffsets := [0, 4]
        hasUninitPadding := false
        nicheBitPattern := none
      } ∧
    reprCForwardLayoutWithI64Align 8 withU64Decl =
      some {
        size := 16
        align := 8
        fieldOffsets := [0, 8]
        hasUninitPadding := true
        nicheBitPattern := none
      } ∧
    (∀ i64AlignBytes, (i64AlignBytes = 4 ∨ i64AlignBytes = 8) →
      evalTransmuteWithU64ToBytes16 i64AlignBytes = StepResult.err) := by
  refine ⟨rfl, rfl, ?_⟩
  intro i64AlignBytes h_cases
  rcases h_cases with rfl | rfl
  · rfl
  · rfl

/-- `#[repr(transparent)] pub struct TransU8(pub u8);` -/
def transU8Decl : AdtDecl where
  name   := "TransU8"
  repr   := .transparent
  fields := [{ ty := .uint .u8, access := .pubSafe }]

/-- Crate containing `TransU8(u8)`. -/
def crateTransU8 : Crate where
  adts := [transU8Decl]

/-- Target specification precondition (`ValidTargetSpec`): requires
`aggregateAlignBytes = 1` (satisfied by all 322 built-in `rustc_target`
specifications, where `a:0:64` is never set above 1 byte unless overridden via
a custom target JSON with `-a:32`). -/
structure TargetSpec where
  ptrWidthBytes       : Nat
  i64AlignBytes       : Nat
  aggregateAlignBytes : Nat
  deriving DecidableEq, Repr

def ValidTargetSpec (t : TargetSpec) : Prop :=
  (t.ptrWidthBytes = 2 ∨ t.ptrWidthBytes = 4 ∨ t.ptrWidthBytes = 8) ∧
  (t.i64AlignBytes = 4 ∨ t.i64AlignBytes = 8) ∧
  t.aggregateAlignBytes = 1

/-- Model of `rustc_abi::layout::univariant_biased`
(`compiler/rustc_abi/src/layout.rs:1106-1114`), which applies `dl.aggregate_align`
as a lower bound on the alignment of every struct—even `#[repr(transparent)]`
wrappers—and rounds the struct size up to that alignment. -/
def univariantBiasedLayout (aggregateAlignBytes innerSize innerAlign : Nat) :
    AdtLayoutRealization :=
  let align := if innerAlign ≤ aggregateAlignBytes then aggregateAlignBytes else innerAlign
  let size := alignUp innerSize align
  {
    size             := size
    align            := align
    fieldOffsets     := [0]
    hasUninitPadding := !(size == innerSize)
    nicheBitPattern  := none
  }

/-- Compiler realization induced by `univariantBiasedLayout` for a given
`aggregateAlignBytes`. -/
def envWithAggregateAlign (aggregateAlignBytes : Nat) : CompilerRealization where
  ptrWidthBytes := 8
  adtLayout := fun name =>
    if name == "TransU8" then
      univariantBiasedLayout aggregateAlignBytes 1 1
    else
      layout8Unpadded

/-- **Theorem B.2 (`custom_target_aggregate_align_gt_one_violates_transparent_law`)**:
1. When a custom target JSON sets `aggregateAlignBytes = 4` (`-a:32`),
   `univariantBiasedLayout 4 1 1` inflates `#[repr(transparent)] struct TransU8(u8)`
   to `size = 4, align = 4, hasUninitPadding = true`, which **violates**
   `ReferenceAdmissible crateTransU8 .any` (`r[layout.repr.transparent]`).
2. Under `ValidTargetSpec` (`aggregateAlignBytes = 1`), `univariantBiasedLayout 1 1 1`
   preserves `size = 1, align = 1, hasUninitPadding = false` and satisfies
   `ReferenceAdmissible crateTransU8 .any`. -/
theorem custom_target_aggregate_align_gt_one_violates_transparent_law :
    univariantBiasedLayout 4 1 1 = {
      size := 4
      align := 4
      fieldOffsets := [0]
      hasUninitPadding := true
      nicheBitPattern := none
    } ∧
    checkReferenceAdmissible crateTransU8 .any (envWithAggregateAlign 4) = false ∧
    ¬ ReferenceAdmissible crateTransU8 .any (envWithAggregateAlign 4) ∧
    (∀ t : TargetSpec, ValidTargetSpec t →
      ReferenceAdmissible crateTransU8 .any
        (envWithAggregateAlign t.aggregateAlignBytes)) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro h_adm
    have h_chk : checkReferenceAdmissible crateTransU8 .any (envWithAggregateAlign 4) = true :=
      (checkReferenceAdmissible_iff crateTransU8 .any (envWithAggregateAlign 4)).mpr h_adm
    have h_false : checkReferenceAdmissible crateTransU8 .any (envWithAggregateAlign 4) = false := rfl
    rw [h_false] at h_chk
    cases h_chk
  · intro t h_valid
    rw [h_valid.2.2]
    exact checkReferenceAdmissible_sound crateTransU8 .any (envWithAggregateAlign 1) rfl

/-- **Combined Extension Theorem B
(`repr_c_target_u64_alignment_and_aggregate_align_boundary`)**:
Packages both `reprC_withU64_padding_depends_on_target_i64_align` and
`custom_target_aggregate_align_gt_one_violates_transparent_law`. -/
theorem repr_c_target_u64_alignment_and_aggregate_align_boundary :
    ((∀ i64AlignBytes, (i64AlignBytes = 4 ∨ i64AlignBytes = 8) →
      evalTransmuteWithU64ToBytes16 i64AlignBytes = StepResult.err) ∧
     ¬ ReferenceAdmissible crateTransU8 .any (envWithAggregateAlign 4) ∧
     (∀ t : TargetSpec, ValidTargetSpec t →
      ReferenceAdmissible crateTransU8 .any
        (envWithAggregateAlign t.aggregateAlignBytes))) :=
  ⟨reprC_withU64_padding_depends_on_target_i64_align.2.2,
   custom_target_aggregate_align_gt_one_violates_transparent_law.2.2.1,
   custom_target_aggregate_align_gt_one_violates_transparent_law.2.2.2⟩

/-!
### 6.3 Extension Theorem C: In-Memory `transmute_copy` vs. `extern "C" fn` ABI Discrimination
-/

/-- Calling-convention return/argument passing mode (`rustc_target::callconv::PassMode`):
- `.directReg`: passed or returned directly in registers (e.g., `edx:eax` on
  `i686` or `rax` / `xmm0` on `x86_64`).
- `.indirectSret`: passed or returned indirectly in memory via a hidden stack
  pointer (`PassMode::Indirect { on_stack: true }` / `sret`, triggered by
  `ReprFlags::ABI_UNOPTIMIZABLE` on `#[repr(C)]` structs on `i686-unknown-linux-gnu`
  or integer-register aggregate rules on `x86_64-pc-windows-msvc`). -/
inductive CallPassMode where
  | directReg
  | indirectSret
  deriving DecidableEq, Repr

/-- Realized C calling-convention passing mode of a `MirTy` under a compiler's
`callAbi : String → CallPassMode` assignment. -/
def tyCallPassMode (callAbi : String → CallPassMode) : MirTy → Option CallPassMode
  | .usize | .isize | .uint _ | .int _ | .bool | .unit | .ref _ | .refMut _ =>
    some .directReg
  | .adt name =>
    some (callAbi name)
  | .param _ | .unmodeled =>
    none

/-- Normative calling-convention admissibility (`r[layout.repr.transparent.layout-abi]`):
A `#[repr(transparent)]` wrapper is guaranteed to have the exact same calling-convention
`CallPassMode` as its single non-ZST field, whereas `#[repr(C)]` and `#[repr(Rust)]`
wrappers may use `.indirectSret` even when their single field uses `.directReg`. -/
def checkAdtCallAbiAdmissible (callAbi : String → CallPassMode)
    (decl : AdtDecl) : Bool :=
  match decl.repr with
  | .transparent =>
    match decl.fields with
    | [f] =>
      match tyCallPassMode callAbi f.ty with
      | some fMode => decide (callAbi decl.name = fMode)
      | none => false
    | _ => false
  | _ => true

def CallAbiAdmissible (c : Crate) (callAbi : String → CallPassMode) : Prop :=
  ∀ decl, decl ∈ c.adts → checkAdtCallAbiAdmissible callAbi decl = true

/-- Evaluate transmuting and calling an `extern "C" fn() -> retTy1` as
`extern "C" fn() -> retTy2` (`r[undefined.call-abi]`):
Succeeds if and only if both return types have the identical `CallPassMode` and
in-memory byte size in `(env, callAbi)`; otherwise steps to `StepResult.failed`. -/
def evalExternCFnAbiTransmute (env : CompilerRealization)
    (callAbi : String → CallPassMode)
    (retTy1 retTy2 : MirTy) : StepResult Unit Empty MirVal :=
  match tySizeInEnv env retTy1, tySizeInEnv env retTy2,
        tyCallPassMode callAbi retTy1, tyCallPassMode callAbi retTy2 with
  | some sz1, some sz2, some mode1, some mode2 =>
    if decide (sz1 = sz2) && decide (mode1 = mode2) then
      .terminated (.normal .unit)
    else
      .failed
  | _, _, _, _ => .failed

/-- Concrete calling-convention realization for `i686-unknown-linux-gnu` (SysV
x86) where `ReprTransparentWrapper(u64)` returns in `.directReg` (`edx:eax`,
matching `u64`) while `ReprCWrapper(u64)` (`#[repr(C)]`) sets
`ReprFlags::ABI_UNOPTIMIZABLE` and returns via `.indirectSret` (`sret`). -/
def callAbi_i686_sysv : String → CallPassMode :=
  fun name =>
    if name == "ReprTransparentWrapper" then .directReg
    else .indirectSret

theorem callAbi_i686_sysv_admissible :
    CallAbiAdmissible testCrate callAbi_i686_sysv := by
  intro decl h_mem
  rcases List.mem_cons.mp h_mem with rfl | h1
  · rfl
  · rcases List.mem_cons.mp h1 with rfl | h2
    · rfl
    · rcases List.mem_cons.mp h2 with rfl | h3
      · rfl
      · rcases List.mem_cons.mp h3 with rfl | h4
        · rfl
        · cases h4

/-- **Extension Theorem C (`in_memory_transmute_vs_extern_c_fn_abi_discrimination`)**:
1. Across **all** `env` satisfying `ReferenceAdmissible testCrate .any env` and
   **all** `callAbi` satisfying `CallAbiAdmissible testCrate callAbi`:
   - In-memory `transmute_copy::<u64, ReprTransparentWrapper>(&x)` and
     `transmute_copy::<u64, ReprCWrapper>(&x)` both succeed, AND
   - `extern "C" fn() -> u64` $\to$ `extern "C" fn() -> ReprTransparentWrapper`
     ABI transmutation (`evalExternCFnAbiTransmute`) succeeds!
2. However, under the valid `i686-unknown-linux-gnu` calling-convention
   realization `callAbi_i686_sysv` (`CallAbiAdmissible testCrate callAbi_i686_sysv`),
   `extern "C" fn() -> u64` $\to$ `extern "C" fn() -> ReprCWrapper` steps to
   `StepResult.err` (`.failed`) because `ReprCWrapper` uses `.indirectSret`
   while `u64` uses `.directReg` (`r[undefined.call-abi]`). -/
theorem in_memory_transmute_vs_extern_c_fn_abi_discrimination (x : Nat) :
    (∀ env callAbi,
      ReferenceAdmissible testCrate .any env →
      CallAbiAdmissible testCrate callAbi →
      evalOpInEnv testCrate env
        (.transmuteCopy (.uint .u64) (.adt "ReprTransparentWrapper") (.u64 x)) =
        .terminated (.normal (.adt "ReprTransparentWrapper" (.u64 x))) ∧
      evalOpInEnv testCrate env
        (.transmuteCopy (.uint .u64) (.adt "ReprCWrapper") (.u64 x)) =
        .terminated (.normal (.adt "ReprCWrapper" (.u64 x))) ∧
      evalExternCFnAbiTransmute env callAbi (.uint .u64)
        (.adt "ReprTransparentWrapper") =
        .terminated (.normal .unit)) ∧
    CallAbiAdmissible testCrate callAbi_i686_sysv ∧
    evalExternCFnAbiTransmute env_8 callAbi_i686_sysv (.uint .u64)
      (.adt "ReprCWrapper") = StepResult.err := by
  refine ⟨?_, callAbi_i686_sysv_admissible, rfl⟩
  intro env callAbi h_adm h_abi
  have h_mem :=
    (model3_accepts_repr_transparent_and_padding_free_repr_c_transmute x).1 env h_adm
  rcases reprTransparentWrapper_layout_in_all_admissible .any env h_adm with
    ⟨h_sz, _, _, _⟩
  have h_abi_trans := h_abi reprTransparentWrapperDecl (by decide)
  unfold checkAdtCallAbiAdmissible reprTransparentWrapperDecl tyCallPassMode at h_abi_trans
  dsimp only at h_abi_trans
  have h_mode : callAbi "ReprTransparentWrapper" = .directReg :=
    of_decide_eq_true h_abi_trans
  refine ⟨h_mem.1, h_mem.2, ?_⟩
  unfold evalExternCFnAbiTransmute tySizeInEnv tyLayoutInEnv tyCallPassMode IntWidth.byteSize
  dsimp only [Option.map]
  rw [h_sz, h_mode]
  rfl

/-!
### 6.4 Extension Theorem D: `UbChecks` + `panic_nounwind_fmt` Dual Soundness Trap and Repair

In `core`, functions with language or library UB preconditions—such as
`hint::unreachable_unchecked`, `slice::get_unchecked`, `ptr::read`, and
`str::from_utf8_unchecked`—expand `assert_unsafe_precondition!(check_language_ub
/ check_library_ub, cond)` into MIR:
```text
_ub = UbChecks();
switchInt(_ub) -> [true: bb_check, false: bb_cont];
bb_check:
  switchInt(cond) -> [true: bb_cont, false: bb_fail];
bb_fail:
  core::panicking::panic_nounwind_fmt(...) -> unreachable;
bb_cont:
  // continuation (e.g., raw pointer/slice cast in from_utf8_unchecked)
```
Under `PrefixOutcome.isSafe`, both
`.terminated (.normal v)` and `.terminated .unwind` have `isSafe = True`, so
`safeSpec` (`Language.WellFormed`, which we alias as `safeUnwindOrNormalSpec` to
make its inclusion of `.unwind` explicit) permits normal unwinding panics while
forbidding `StepResult.failed` (`isSafe = False`).

We formalize the three interpretations of `(UbChecks, panic_nounwind_fmt)`:
1. **Broken Interpretation 1 (`evalUbCheck_BrokenUnwind`)**: `UbChecks = true`,
   and `panic_nounwind_fmt` transitions to `.terminated .unwind`.
2. **Broken Interpretation 2 (`evalUbCheck_BrokenSkip`)**: `UbChecks = false`,
   skipping `bb_check` and executing `bb_cont` directly (which for library-UB
   operations like `str::from_utf8_unchecked` is a valid raw pointer/slice
   cast that returns `.terminated (.normal retVal)` without checking `cond`).
3. **Sound Interpretation 3 (`evalUbCheck_SoundFailed`)**: `UbChecks = true`,
   and `panic_nounwind_fmt` (`UnwindAction::Unreachable`) transitions to
   `StepResult.failed` (`StepResult.err`).
-/

/-- Explicit alias emphasizing that `PrefixOutcome.isSafe`
treats both `.terminated (.normal v)` and `.terminated .unwind` as safe (`True`)
and only `.failed` / `.stuck` as unsafe (`False`). -/
abbrev safeUnwindOrNormalSpec (L : Language) : L.Behavior :=
  L.WellFormed

/-- Broken Interpretation 1 (`UbChecks = true`, `panic_nounwind_fmt` $\mapsto$
`.terminated .unwind`): when `cond = false`, steps to `.terminated .unwind`. -/
def evalUbCheck_BrokenUnwind (cond : Bool) (retVal : MirVal) :
    StepResult Unit Empty MirVal :=
  if cond then
    .terminated (.normal retVal)
  else
    .terminated .unwind

def MachineUbBrokenUnwind (cond : Bool) (retVal : MirVal) :
    SmallStepMachine Unit Unit Empty MirVal where
  initState := fun _ s => s = ()
  step      := fun _ _ r => r = evalUbCheck_BrokenUnwind cond retVal

abbrev LangUbBrokenUnwind (cond : Bool) (retVal : MirVal) : Language :=
  (MachineUbBrokenUnwind cond retVal).toLanguage

/-- Broken Interpretation 2 (`UbChecks = false`, skipping `precondition_check`):
for a library-UB operation such as `str::from_utf8_unchecked` whose continuation
body is a raw slice/pointer cast, skipping `bb_check` steps directly to
`.terminated (.normal retVal)` regardless of `cond`. -/
def evalUbCheck_BrokenSkip (_cond : Bool) (retVal : MirVal) :
    StepResult Unit Empty MirVal :=
  .terminated (.normal retVal)

def MachineUbBrokenSkip (cond : Bool) (retVal : MirVal) :
    SmallStepMachine Unit Unit Empty MirVal where
  initState := fun _ s => s = ()
  step      := fun _ _ r => r = evalUbCheck_BrokenSkip cond retVal

abbrev LangUbBrokenSkip (cond : Bool) (retVal : MirVal) : Language :=
  (MachineUbBrokenSkip cond retVal).toLanguage

/-- Sound Interpretation 3 (`UbChecks = true`, `panic_nounwind_fmt` /
`UnwindAction::Unreachable` $\mapsto$ `StepResult.failed`): when `cond = false`,
steps to `StepResult.failed` (`.err`). -/
def evalUbCheck_SoundFailed (cond : Bool) (retVal : MirVal) :
    StepResult Unit Empty MirVal :=
  if cond then
    .terminated (.normal retVal)
  else
    .failed

def MachineUbSoundFailed (cond : Bool) (retVal : MirVal) :
    SmallStepMachine Unit Unit Empty MirVal where
  initState := fun _ s => s = ()
  step      := fun _ _ r => r = evalUbCheck_SoundFailed cond retVal

abbrev LangUbSoundFailed (cond : Bool) (retVal : MirVal) : Language :=
  (MachineUbSoundFailed cond retVal).toLanguage

/-- **Extension Theorem D (`ub_checks_dual_soundness_trap_and_repair`)**:
1. **Trap 1 (`UbChecks = true`, `panic_nounwind_fmt ↦ .terminated .unwind`)**:
   Even when the UB precondition is violated (`cond = false`),
   `(LangUbBrokenUnwind false retVal).sem () ≤ safeUnwindOrNormalSpec _`,
   falsely certifying UB code as safe!
2. **Trap 2 (`UbChecks = false`, skipping `precondition_check`)**:
   Even when the library UB precondition is violated (`cond = false`),
   `(LangUbBrokenSkip false retVal).sem () ≤ safeUnwindOrNormalSpec _`,
   again falsely certifying library-UB code (`str::from_utf8_unchecked`) as safe!
3. **Sound Repair (`UbChecks = true`, `panic_nounwind_fmt ↦ StepResult.failed`)**:
   Under `LangUbSoundFailed cond retVal`,
   `(LangUbSoundFailed cond retVal).sem () ≤ safeUnwindOrNormalSpec _` holds
   **if and only if** `cond = true`! -/
theorem ub_checks_dual_soundness_trap_and_repair (retVal : MirVal) :
    ((LangUbBrokenUnwind false retVal).sem () ≤
      safeUnwindOrNormalSpec (LangUbBrokenUnwind false retVal)) ∧
    ((LangUbBrokenSkip false retVal).sem () ≤
      safeUnwindOrNormalSpec (LangUbBrokenSkip false retVal)) ∧
    (∀ cond : Bool,
      ((LangUbSoundFailed cond retVal).sem () ≤
        safeUnwindOrNormalSpec (LangUbSoundFailed cond retVal)) ↔
      cond = true) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Trap 1: `.terminated .unwind` is treated as `isSafe = True`
    intro s _
    refine ⟨?_, fun _ _ => True.intro⟩
    intro _ n tr out hreach
    cases hreach with
    | zero => exact True.intro
    | step _ _ _ _ _ _ hst _ => cases hst
    | choice _ _ _ _ _ _ hst _ _ => cases hst
    | emptyChoice _ _ _ hst _ => cases hst
    | terminated _ _ _ _ => exact True.intro
    | failed _ _ hst => cases hst
    | noStep _ _ hno =>
      exact False.elim (hno ⟨.terminated .unwind, rfl⟩)
  · -- Trap 2: skipping `precondition_check` steps to `.terminated (.normal retVal)`
    intro s _
    refine ⟨?_, fun _ _ => True.intro⟩
    intro _ n tr out hreach
    cases hreach with
    | zero => exact True.intro
    | step _ _ _ _ _ _ hst _ => cases hst
    | choice _ _ _ _ _ _ hst _ _ => cases hst
    | emptyChoice _ _ _ hst _ => cases hst
    | terminated _ _ _ _ => exact True.intro
    | failed _ _ hst => cases hst
    | noStep _ _ hno =>
      exact False.elim (hno ⟨.terminated (.normal retVal), rfl⟩)
  · -- Sound Repair: refines `safeUnwindOrNormalSpec` iff `cond = true`
    intro cond
    cases cond with
    | false =>
      constructor
      · intro h_le
        have ⟨h_def, _⟩ := h_le () True.intro
        have h_reach_fail :
            ReachesPrefix (MachineUbSoundFailed false retVal).step () 1 () [] .failed :=
          ReachesPrefix.failed 0 () rfl
        exact False.elim (h_def rfl 1 [] .failed h_reach_fail)
      · intro h_eq
        cases h_eq
    | true =>
      constructor
      · intro _
        rfl
      · intro _ s _
        refine ⟨?_, fun _ _ => True.intro⟩
        intro _ n tr out hreach
        cases hreach with
        | zero => exact True.intro
        | step _ _ _ _ _ _ hst _ => cases hst
        | choice _ _ _ _ _ _ hst _ _ => cases hst
        | emptyChoice _ _ _ hst _ => cases hst
        | terminated _ _ _ _ => exact True.intro
        | failed _ _ hst => cases hst
        | noStep _ _ hno =>
          exact False.elim (hno ⟨.terminated (.normal retVal), rfl⟩)

/-!
## 7. Axiom Verification (`#print axioms`)
-/

#print axioms model1_unsoundly_accepts_repr_rust_transmute
#print axioms model1_multi_field_repr_rust_size_zero_bug
#print axioms model2_rejects_repr_rust_transmute_u64
#print axioms model2_falsely_rejects_reflexive_and_polymorphic_ops
#print axioms checkReferenceAdmissible_iff
#print axioms checkReferenceAdmissible_sound
#print axioms sem_forwardCompatible_choice_iff_query
#print axioms model3_rejects_repr_rust_u64_transmute
#print axioms model3_accepts_repr_transparent_and_padding_free_repr_c_transmute
#print axioms model3_accepts_reflexive_repr_rust_transmute_and_copy
#print axioms model3_target_parametric_vs_cfg_gated_usize
#print axioms model3_refinement_bridge_and_tcb_stratification
#print axioms model3_dead_branch_required_consts_discrimination
#print axioms repr_rust_zst_vs_non_zst_discrimination
#print axioms reprC_withU64_padding_depends_on_target_i64_align
#print axioms custom_target_aggregate_align_gt_one_violates_transparent_law
#print axioms repr_c_target_u64_alignment_and_aggregate_align_boundary
#print axioms in_memory_transmute_vs_extern_c_fn_abi_discrimination
#print axioms ub_checks_dual_soundness_trap_and_repair

end ForwardCompatibleMirSemantics
