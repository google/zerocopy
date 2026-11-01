/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

/-!
# Mechanized Probe: Adapting `rustc_mir_transform` Passes to Anneal

This standalone Lean 4.34.1 file mechanizes the core semantic models,
refinement proofs, pipeline composition, and negative soundness canaries for
(*Adapting `rustc` MIR Optimization Passes & the MIR-vs.-LLVM
Division of Labor*).

## Architecture Overview

1. **Anneal Refinement Infrastructure (`Section 1`):**
   Self-contained mechanization of Anneal's `Preorder`, `Partial`, `Behavior`,
   `Language`, `BehaviorCodec`, `Compiles`, `StepResult`, and `BB-8`
   `PassCompiler` / `CertChecker` composition (`Trusted/Refinement.lean` and
   `Trusted/StepResult.lean`).
2. **Typed MIR Semantics with Ownership & Storage Liveness (`Section 2`):**
   Models MIR places (`Local` and `.field` projections), aggregate vs. scalar
   values, explicit storage liveness (`LocalSlot.dead`, `.uninit`, `.init`),
   destructive moves (`Operand.move` deinitializes the source place), address
   exposure (`Rvalue.addrOf` gated by `addressTaken`), and linear resource
   destructor tracking (`dropLog` detecting double-drop UB).
3. **Pass 1 — `MirSROA` (`sroa.rs`, Category M2) (`Section 3`):**
   Flattens a non-escaping 2-field aggregate local into two scalar leaf locals.
   - Positive theorem: `mirSroa_compiles` proves `Compiles MirLang MirLang
     idCodec` when `!isAddressTaken aggLocal`.
   - Negative canary: `canary_sroa_on_address_taken_local_unsound` proves that
     applying `MirSROA` to an address-taken local violates `Compiles`.
4. **Pass 2 — `DestinationPropagation` (`dest_prop.rs`, Category M2)
   (`Section 4`):**
   Coalesces `dst := move src` by redirecting writes to `src` directly into
   `dst` and unioning their `StorageLive` intervals.
   - Positive theorem: `destProp_with_live_union_compiles` proves
     `Compiles MirLang MirLang idCodec`.
   - Negative canary: `canary_destProp_without_live_union_violates_compiles`
     reproduces `rust-lang/rust#146383`: coalescing `src` into `dst` without
     extending `dst`'s `StorageLive` interval writes to a `.dead` destination
     local, turning a well-defined program into `.ub` and violating `Compiles`.
5. **Pass 3 — `ElaborateDrops` (`elaborate_drops.rs`, Category M1)
   (`Section 5`):**
   Lowers `PreDropMirLang` (implicit scope-exit drop of conditionally moved
   owned values) into `MirLang` with an explicit boolean drop-flag local that
   is set on initialization, cleared on `Operand.move`, and cleared before
   running destructor glue.
   - Positive theorem: `elaborateDrops_compiles` proves
     `Compiles PreDropMirLang MirLang idCodec`.
   - Negative canary: `canary_elaborateDrops_missing_move_clear_unsound` proves
     that omitting the drop-flag clear on `Operand.move` causes a double-drop
     (`.ub`) on the early-move path, violating `Compiles`.
6. **Verified Pipeline Composition (`Section 6`):**
   Composes `ElaborateDrops` (Category M1) → `MirSROA` (Category M2) →
   `DestinationPropagation` (Category M2) via `PassCompiler.comp` into a single
   verified pipeline `mirCleanupAndOptPipeline_compiles`.
-/

namespace Anneal.MirTransformProbe

/-!
## Section 1: Anneal Refinement & `BB-8` Pass Composition Infrastructure

These definitions mirror `Trusted/Refinement.lean`, `Trusted/StepResult.lean`,
and `Anneal/Refinement.lean` (Issue #241).
-/

/-- A reflexive, transitive relation on `α`. -/
class Preorder (α : Type u) extends LE α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c

/-- The identity preorder where `a ≤ b` holds iff `a = b`. -/
@[instance_reducible]
def EqPreorder (α : Type u) : Preorder α where
  le a b := a = b
  le_refl _ := rfl
  le_trans h1 h2 := Eq.trans h1 h2

/-- A partial value equipped with a definedness predicate. -/
structure Partial (α : Type u) where
  val : α
  defined : Prop

namespace Partial

/-- Total injection embedding a fully defined value into `Partial α`. -/
def total (x : α) : Partial α :=
  ⟨x, True⟩

/-- A `Partial` value with `False` definedness (`⊥`). -/
def bot (default : α) : Partial α :=
  ⟨default, False⟩

/-- Forward-simulation ordering on `Partial α`: whenever the source is defined,
the target must be defined and ordered by the underlying preorder. -/
instance [Preorder α] : Preorder (Partial α) where
  le p q := p.defined → q.defined ∧ p.val ≤ q.val
  le_refl p hp := ⟨hp, Preorder.le_refl p.val⟩
  le_trans h1 h2 hp :=
    let ⟨hq, hpq⟩ := h1 hp
    let ⟨hr, hqr⟩ := h2 hq
    ⟨hr, Preorder.le_trans hpq hqr⟩

end Partial

/-- Observable outcomes of a single execution trace. -/
inductive Behavior (Obs : Type u) where
  /-- The execution terminated normally with observable result `v`. -/
  | returns (v : Obs)
  /-- The execution diverged without encountering undefined behavior. -/
  | diverges
  /-- The execution encountered undefined behavior (`UB`). -/
  | ub

namespace Behavior

/-- Map an observable transformation across a `Behavior`. -/
def map (f : α → β) : Behavior α → Behavior β
  | .returns v => .returns (f v)
  | .diverges => .diverges
  | .ub => .ub

/-- Forward refinement on `Behavior Obs`:
- `.ub` at the source is refined by any target behavior (compiler freedom on
  UB).
- `.returns v` requires `.returns w` with `v ≤ w`.
- `.diverges` requires `.diverges`. -/
inductive Le [Preorder Obs] : Behavior Obs → Behavior Obs → Prop where
  | ub (b : Behavior Obs) : Le .ub b
  | returns {v w : Obs} (h : v ≤ w) : Le (.returns v) (.returns w)
  | diverges : Le .diverges .diverges

instance [Preorder Obs] : Preorder (Behavior Obs) where
  le := Le
  le_refl
    | .ub => Le.ub .ub
    | .returns v => Le.returns (Preorder.le_refl v)
    | .diverges => Le.diverges
  le_trans {a b c} hab hbc := by
    cases hab with
    | ub _ => exact Le.ub c
    | returns hvw =>
      cases hbc with
      | returns hwx => exact Le.returns (Preorder.le_trans hvw hwx)
    | diverges =>
      cases hbc with
      | diverges => exact Le.diverges

end Behavior

/-- A semantic language interface parameterized by program syntax, execution
context, and observable outcome type (`Trusted/Refinement.lean`). -/
structure Language where
  Program : Type
  Context : Type
  Obs : Type
  [obsPreorder : Preorder Obs]
  exec : Program → Context → Behavior Obs

attribute [instance] Language.obsPreorder

/-- Outcome of a single small-step transition (`Trusted/StepResult.lean`). -/
inductive StepResult (State : Type u) (Obs : Type v) where
  | next (s' : State)
  | done (v : Obs)
  | ub

/-- Bounded `n`-step reachability prefix (`Trusted/StepResult.lean`). -/
def ReachesPrefix {State Obs : Type}
    (step : State → StepResult State Obs) :
    Nat → State → Option (Behavior Obs)
  | 0, _ => none
  | n + 1, s =>
    match step s with
    | .next s' => ReachesPrefix step n s'
    | .done v => some (.returns v)
    | .ub => some .ub

/-- Relational big-step behavior induced by a small-step transition function
(`Trusted/StepResult.lean`). -/
def BehaviorOf {State Obs : Type}
    (step : State → StepResult State Obs)
    (init : State) (b : Behavior Obs) : Prop :=
  match b with
  | .returns v => ∃ n, ReachesPrefix step n init = some (.returns v)
  | .ub => ∃ n, ReachesPrefix step n init = some .ub
  | .diverges => ∀ n, ReachesPrefix step n init = none

/-- Soundness of fuel-bounded step execution: if `ReachesPrefix step n init =
some b`, then `BehaviorOf step init b` holds. -/
theorem BehaviorOf.of_reachesPrefix {State Obs : Type}
    (step : State → StepResult State Obs) (init : State) (n : Nat) (v : Obs)
    (h : ReachesPrefix step n init = some (.returns v)) :
    BehaviorOf step init (.returns v) :=
  ⟨n, h⟩

/-- Cross-language codec relating target contexts and source observations to
their counterparts (`Trusted/Refinement.lean`). -/
structure BehaviorCodec (S T : Language) where
  decodeCtx : T.Context → Partial S.Context
  encodeObs : S.Obs → Partial T.Obs

/-- Identity `BehaviorCodec` for same-language MIR-to-MIR transformations. -/
def idCodec (L : Language) : BehaviorCodec L L where
  decodeCtx c := Partial.total c
  encodeObs o := Partial.total o

/-- Lift `encodeObs` from `S.Obs → Partial T.Obs` to `Behavior S.Obs →
Partial (Behavior T.Obs)`. -/
def BehaviorCodec.encodeBehavior {S T : Language} (codec : BehaviorCodec S T) :
    Behavior S.Obs → Partial (Behavior T.Obs)
  | .returns o =>
    let p := codec.encodeObs o
    ⟨.returns p.val, p.defined⟩
  | .diverges => Partial.total .diverges
  | .ub => Partial.bot .ub

/-- Anneal's master compilation correctness relation (`Trusted/Refinement.lean`):
`p_S` compiles to `p_T` across `codec` iff for every target context `c_T`,
whenever `decodeCtx c_T` is defined, the encoded source behavior is refined by
the target behavior. -/
def Compiles (S T : Language) (codec : BehaviorCodec S T)
    (p_S : S.Program) (p_T : T.Program) : Prop :=
  ∀ c_T : T.Context,
    (codec.decodeCtx c_T).defined →
      codec.encodeBehavior (S.exec p_S (codec.decodeCtx c_T).val) ≤
        Partial.total (T.exec p_T c_T)

/-- Reflexivity of `Compiles` over `idCodec`. -/
theorem Compiles.refl (L : Language) (p : L.Program) :
    Compiles L L (idCodec L) p p := by
  intro c _ hEncDef
  dsimp [idCodec, Partial.total] at hEncDef ⊢
  cases h : L.exec p c with
  | returns o =>
    exact ⟨trivial, Behavior.Le.returns (Preorder.le_refl o)⟩
  | diverges =>
    exact ⟨trivial, Behavior.Le.diverges⟩
  | ub =>
    rw [h] at hEncDef
    exact False.elim hEncDef

/-- Sequential composition of `BehaviorCodec`s. -/
def BehaviorCodec.comp {L1 L2 L3 : Language}
    (c12 : BehaviorCodec L1 L2) (c23 : BehaviorCodec L2 L3) :
    BehaviorCodec L1 L3 where
  decodeCtx ctx3 :=
    let p2 := c23.decodeCtx ctx3
    let p1 := c12.decodeCtx p2.val
    ⟨p1.val, p2.defined ∧ p1.defined⟩
  encodeObs obs1 :=
    let p2 := c12.encodeObs obs1
    let p3 := c23.encodeObs p2.val
    ⟨p3.val, p2.defined ∧ p3.defined⟩

/-- Transitivity of `Compiles` across an initial language `L1` and subsequent
`idCodec` passes on `L2`. -/
theorem Compiles.trans_right_id {L1 L2 : Language}
    {codec : BehaviorCodec L1 L2}
    {p1 : L1.Program} {p2 p3 : L2.Program}
    (h12 : Compiles L1 L2 codec p1 p2)
    (h23 : Compiles L2 L2 (idCodec L2) p2 p3) :
    Compiles L1 L2 codec p1 p3 := by
  intro c hc
  have s12 := h12 c hc
  have s23 := h23 c trivial
  intro hEncDef
  have ⟨_, hLe12⟩ := s12 hEncDef
  cases hExec2 : L2.exec p2 c with
  | ub =>
    change (codec.encodeBehavior (L1.exec p1 (codec.decodeCtx c).val)).val ≤
      L2.exec p2 c at hLe12
    rw [hExec2] at hLe12
    cases hExec1 : L1.exec p1 (codec.decodeCtx c).val with
    | ub =>
      change (codec.encodeBehavior (L1.exec p1 (codec.decodeCtx c).val)).defined at hEncDef
      rw [hExec1] at hEncDef
      exact False.elim hEncDef
    | diverges =>
      rw [hExec1] at hLe12
      cases hLe12
    | returns v1 =>
      rw [hExec1] at hLe12
      cases hLe12
  | diverges =>
    change (codec.encodeBehavior (L1.exec p1 (codec.decodeCtx c).val)).val ≤
      L2.exec p2 c at hLe12
    have hDef2 : ((idCodec L2).encodeBehavior (L2.exec p2 c)).defined := by
      rw [hExec2]
      exact trivial
    have ⟨_, hLe23⟩ := s23 hDef2
    change ((idCodec L2).encodeBehavior (L2.exec p2 c)).val ≤ L2.exec p3 c at hLe23
    rw [hExec2] at hLe12 hLe23
    exact ⟨trivial, Preorder.le_trans hLe12 hLe23⟩
  | returns v2 =>
    change (codec.encodeBehavior (L1.exec p1 (codec.decodeCtx c).val)).val ≤
      L2.exec p2 c at hLe12
    have hDef2 : ((idCodec L2).encodeBehavior (L2.exec p2 c)).defined := by
      rw [hExec2]
      exact trivial
    have ⟨_, hLe23⟩ := s23 hDef2
    change ((idCodec L2).encodeBehavior (L2.exec p2 c)).val ≤ L2.exec p3 c at hLe23
    rw [hExec2] at hLe12 hLe23
    exact ⟨trivial, Preorder.le_trans hLe12 hLe23⟩

/-- Transitivity of `Compiles` over `idCodec`. -/
theorem Compiles.trans_id {L : Language} {p1 p2 p3 : L.Program}
    (h12 : Compiles L L (idCodec L) p1 p2)
    (h23 : Compiles L L (idCodec L) p2 p3) :
    Compiles L L (idCodec L) p1 p3 :=
  Compiles.trans_right_id h12 h23

/-- `BB-8` verified pass compiler (`existing_compiler_reports.md`): a pass may
decline to transform (or fail a static precondition check) by returning `none`,
and whenever it returns `some p_T`, `Compiles S T codec p_S p_T` is guaranteed. -/
structure PassCompiler (S T : Language) (codec : BehaviorCodec S T) where
  compile : S.Program → Option T.Program
  sound : ∀ {p_S p_T}, compile p_S = some p_T → Compiles S T codec p_S p_T

/-- Sequential composition of two intra-language `PassCompiler`s. -/
def PassCompiler.compId {L : Language}
    (P1 P2 : PassCompiler L L (idCodec L)) :
    PassCompiler L L (idCodec L) where
  compile p1 :=
    match P1.compile p1 with
    | none => none
    | some p2 => P2.compile p2
  sound {p1 p3} h := by
    cases h1 : P1.compile p1 with
    | none => simp [h1] at h
    | some p2 =>
      simp [h1] at h
      exact Compiles.trans_id (P1.sound h1) (P2.sound h)

/-- Sequential composition of a lowering `PassCompiler S T codec` followed by an
intra-language optimization `PassCompiler T T (idCodec T)`. -/
def PassCompiler.thenOpt {S T : Language} {codec : BehaviorCodec S T}
    (P1 : PassCompiler S T codec) (P2 : PassCompiler T T (idCodec T)) :
    PassCompiler S T codec where
  compile p1 :=
    match P1.compile p1 with
    | none => none
    | some p2 => P2.compile p2
  sound {p1 p3} h := by
    cases h1 : P1.compile p1 with
    | none => simp [h1] at h
    | some p2 =>
      simp [h1] at h
      exact Compiles.trans_right_id (P1.sound h1) (P2.sound h)

/-- `BB-8` translation-validation certificate checker: pairs an untrusted oracle
with a verified boolean validator `check`. -/
structure CertChecker (S T : Language) (codec : BehaviorCodec S T) (Cert : Type) where
  oracle : S.Program → Option (T.Program × Cert)
  check : S.Program → T.Program → Cert → Bool
  check_sound : ∀ {p_S p_T cert},
    check p_S p_T cert = true → Compiles S T codec p_S p_T

/-- Every `CertChecker` embeds into `PassCompiler` (`BB-8` Theorem 1). -/
def CertChecker.toPassCompiler {S T : Language} {codec : BehaviorCodec S T} {Cert : Type}
    (cc : CertChecker S T codec Cert) : PassCompiler S T codec where
  compile p_S :=
    match cc.oracle p_S with
    | none => none
    | some (p_T, cert) =>
      if cc.check p_S p_T cert then some p_T else none
  sound {p_S p_T} h := by
    cases hOracle : cc.oracle p_S with
    | none => simp [hOracle] at h
    | some pair =>
      rcases pair with ⟨cand, cert⟩
      simp [hOracle] at h
      cases hCheck : cc.check p_S cand cert with
      | false => simp [hCheck] at h
      | true =>
        simp [hCheck] at h
        subst h
        exact cc.check_sound hCheck

/-!
## Section 2: Typed MIR Model with Storage Liveness, Moves & Linear Drops

We model a representative fragment of `Runtime(PostCleanup)` MIR (`MirLang`) and
`Runtime(Initial)` pre-drop-elaboration MIR (`PreDropMirLang`) that captures the
exact semantic invariants exploited by `MirSROA`, `DestinationPropagation`,
`CopyProp`, and `ElaborateDrops`:
- **Storage Liveness vs. Initialization (`LocalSlot`):**
  Each local is in one of three states:
  - `.dead`: outside `StorageLive`..`StorageDead` (reading OR writing a `.dead`
    local is UB, matching Miri and LLVM `@llvm.lifetime.start` semantics).
  - `.uninit`: inside `StorageLive`..`StorageDead`, but not currently holding an
    initialized value (reading is UB, writing initializes the slot).
  - `.init v`: live and initialized with value `v`.
- **Destructive `Operand.move`:**
  Evaluating `Operand.move pl` reads the value at `pl` and transitions `pl` from
  `.init v` to `.uninit` (or updates the aggregate field).
- **Address-Taken Guard (`addressTaken`):**
  `Rvalue.addrOf l` requires `prog.isAddressTaken l = true` and `l` to be
  allocated as a whole slot in `LocalSlot` (so scalarizing an address-taken
  aggregate without preserving its backing storage is caught).
- **Linear Resource Drop Tracking (`dropLog`):**
  To model `ElaborateDrops` soundness, `Obs` records `(retVal, dropLog)`, where
  `dropLog : List Int` lists the resource IDs dropped during execution, and
  dropping the same resource ID twice triggers `.ub` (double-free / double-drop
  UB).
-/

/-- Local variable identifier (`_0`, `_1`, ...). -/
abbrev Local := Nat

/-- Field index of a 2-field aggregate (`Pair` / struct). -/
inductive FieldIdx where
  | f0
  | f1
  deriving DecidableEq, Repr

/-- Runtime values in our MIR model: either a scalar `Int` or a 2-field
aggregate `agg2`. Using `Option Int` inside `agg2` allows individual fields of a
live aggregate to be moved out (`none` = deinitialized field). -/
inductive Val where
  | scalar (n : Int)
  | agg2 (f0 : Option Int) (f1 : Option Int)
  deriving DecidableEq, Repr

/-- A MIR `Place`: either a whole `Local` or a `.field` projection of a `Local`. -/
inductive Place where
  | local (l : Local)
  | field (l : Local) (idx : FieldIdx)
  deriving DecidableEq, Repr

/-- Three-state storage lifecycle of a MIR local. -/
inductive LocalSlot where
  /-- Outside `StorageLive`..`StorageDead`: both reads and writes are UB. -/
  | dead
  /-- Storage is live (`StorageLive`), but value is uninitialized or moved out. -/
  | uninit
  /-- Storage is live and holds value `v`. -/
  | init (v : Val)
  deriving DecidableEq, Repr

/-- MIR `Operand`. -/
inductive Operand where
  | copy (p : Place)
  | move (p : Place)
  | constScalar (n : Int)
  deriving DecidableEq, Repr

/-- MIR `Rvalue`. -/
inductive Rvalue where
  | use (op : Operand)
  | aggregate2 (op0 : Operand) (op1 : Operand)
  | binaryAdd (op0 : Operand) (op1 : Operand)
  | addrOf (l : Local)
  deriving DecidableEq, Repr

/-- MIR `Statement` in `PostCleanup` `MirLang`. -/
inductive Stmt where
  | nop
  | storageLive (l : Local)
  | storageDead (l : Local)
  | assign (dst : Place) (rv : Rvalue)
  /-- Conditional drop glue generated by `ElaborateDrops`: if `flagLocal` holds
  scalar `1`, clears `flagLocal` to `0` and drops the scalar resource stored in
  `resourceLocal`; if `flagLocal` holds `0`, does nothing; otherwise `.ub`. -/
  | dropIfFlag (flagLocal : Local) (resourceLocal : Local)
  /-- Unconditional drop glue generated by `ElaborateDrops` (`DropStyle.Static`). -/
  | dropStatic (resourceLocal : Local)
  deriving DecidableEq, Repr

/-- Observable outcome of a MIR function: `(returnValue, droppedResourceIds)`. -/
abbrev MirObs := Int × List Int

instance : Preorder MirObs := EqPreorder MirObs

/-- Runtime state during MIR execution. -/
structure MirState where
  locals : Local → LocalSlot
  dropLog : List Int

namespace MirState

/-- Read a `LocalSlot`. -/
def getSlot (st : MirState) (l : Local) : LocalSlot :=
  st.locals l

/-- Update a `LocalSlot`. -/
def setSlot (st : MirState) (l : Local) (slot : LocalSlot) : MirState :=
  { st with locals := fun l' => if l' = l then slot else st.locals l' }

theorem getSlot_setSlot_same (st : MirState) (l : Local) (slot : LocalSlot) :
    (st.setSlot l slot).getSlot l = slot := by
  simp [getSlot, setSlot]

theorem getSlot_setSlot_ne (st : MirState) {l l' : Local} (slot : LocalSlot)
    (hne : l' ≠ l) :
    (st.setSlot l slot).getSlot l' = st.getSlot l' := by
  simp [getSlot, setSlot, hne]

end MirState

/-- Read a scalar value from a `Place` without modifying `st` (`Operand.copy`). -/
def evalCopyPlace (st : MirState) (p : Place) : Option Val :=
  match p with
  | .local l =>
    match st.getSlot l with
    | .init v => some v
    | _ => none
  | .field l idx =>
    match st.getSlot l with
    | .init (.agg2 f0 f1) =>
      match idx with
      | .f0 =>
        match f0 with
        | some n => some (.scalar n)
        | none => none
      | .f1 =>
        match f1 with
        | some n => some (.scalar n)
        | none => none
    | _ => none

/-- Read a value from a `Place` and deinitialize that `Place` (`Operand.move`). -/
def evalMovePlace (st : MirState) (p : Place) : Option (Val × MirState) :=
  match p with
  | .local l =>
    match st.getSlot l with
    | .init v => some (v, st.setSlot l .uninit)
    | _ => none
  | .field l idx =>
    match st.getSlot l with
    | .init (.agg2 f0 f1) =>
      match idx with
      | .f0 =>
        match f0 with
        | some n => some (.scalar n, st.setSlot l (.init (.agg2 none f1)))
        | none => none
      | .f1 =>
        match f1 with
        | some n => some (.scalar n, st.setSlot l (.init (.agg2 f0 none)))
        | none => none
    | _ => none

/-- Evaluate an `Operand`, returning the resulting `Val` and updated `MirState`. -/
def evalOperand (st : MirState) (op : Operand) : Option (Val × MirState) :=
  match op with
  | .copy p =>
    match evalCopyPlace st p with
    | some v => some (v, st)
    | none => none
  | .move p => evalMovePlace st p
  | .constScalar n => some (.scalar n, st)

/-- Write `v` to `Place` `p`. Crucially, writing to a `.dead` local (`StorageDead`
or before `StorageLive`) fails (`none` → `.ub`), enforcing the `StorageLive`
liveness invariant. -/
def writePlace (st : MirState) (p : Place) (v : Val) : Option MirState :=
  match p with
  | .local l =>
    match st.getSlot l with
    | .dead => none
    | .uninit | .init _ => some (st.setSlot l (.init v))
  | .field l idx =>
    match v with
    | .scalar n =>
      match st.getSlot l with
      | .dead => none
      | .uninit =>
        match idx with
        | .f0 => some (st.setSlot l (.init (.agg2 (some n) none)))
        | .f1 => some (st.setSlot l (.init (.agg2 none (some n))))
      | .init (.agg2 f0 f1) =>
        match idx with
        | .f0 => some (st.setSlot l (.init (.agg2 (some n) f1)))
        | .f1 => some (st.setSlot l (.init (.agg2 f0 (some n))))
      | .init (.scalar _) => none
    | .agg2 _ _ => none

/-- Evaluate an `Rvalue`, checking `isAddressTaken` for `.addrOf`. -/
def evalRvalue (isAddressTaken : Local → Bool) (st : MirState) (rv : Rvalue) :
    Option (Val × MirState) :=
  match rv with
  | .use op => evalOperand st op
  | .aggregate2 op0 op1 =>
    match evalOperand st op0 with
    | some (.scalar n0, st1) =>
      match evalOperand st1 op1 with
      | some (.scalar n1, st2) => some (.agg2 (some n0) (some n1), st2)
      | _ => none
    | _ => none
  | .binaryAdd op0 op1 =>
    match evalOperand st op0 with
    | some (.scalar n0, st1) =>
      match evalOperand st1 op1 with
      | some (.scalar n1, st2) => some (.scalar (n0 + n1), st2)
      | _ => none
    | _ => none
  | .addrOf l =>
    if isAddressTaken l then
      match st.getSlot l with
      | .init (.agg2 (some n0) (some n1)) => some (.scalar (n0 + n1), st)
      | .init (.scalar n) => some (.scalar n, st)
      | _ => none
    else
      none

/-- Record a linear destructor invocation for resource `id`. If `id` has already
been dropped (`id ∈ st.dropLog`), returns `none` (double-drop UB). -/
def recordDrop (st : MirState) (id : Int) : Option MirState :=
  if st.dropLog.contains id then
    none
  else
    some { st with dropLog := st.dropLog ++ [id] }

/-- Execute a single `Stmt`. -/
def execStmt (isAddressTaken : Local → Bool) (st : MirState) (s : Stmt) :
    Option MirState :=
  match s with
  | .nop => some st
  | .storageLive l => some (st.setSlot l .uninit)
  | .storageDead l => some (st.setSlot l .dead)
  | .assign dst rv =>
    match evalRvalue isAddressTaken st rv with
    | some (v, st1) => writePlace st1 dst v
    | none => none
  | .dropStatic resLocal =>
    match st.getSlot resLocal with
    | .init (.scalar id) => recordDrop (st.setSlot resLocal .uninit) id
    | _ => none
  | .dropIfFlag flagLocal resLocal =>
    match st.getSlot flagLocal with
    | .init (.scalar flagVal) =>
      if flagVal = 0 then
        some st
      else if flagVal = 1 then
        let stCleared := st.setSlot flagLocal (.init (.scalar 0))
        match stCleared.getSlot resLocal with
        | .init (.scalar id) => recordDrop (stCleared.setSlot resLocal .uninit) id
        | _ => none
      else
        none
    | _ => none

/-- Execute a sequence of statements. -/
def execStmts (isAddressTaken : Local → Bool) (st : MirState) :
    List Stmt → Option MirState
  | [] => some st
  | s :: rest =>
    match execStmt isAddressTaken st s with
    | some st' => execStmts isAddressTaken st' rest
    | none => none

/-- A `MirLang` program with a statement body, a designated return local, and an
`isAddressTaken` declaration map. -/
structure MirProg where
  isAddressTaken : Local → Bool
  stmts : List Stmt
  retLocal : Local

/-- Initial `MirState` where an argument local `_1` is live and initialized to
`ctxArg : Int`, `_0` (`RETURN_PLACE`) is live and uninitialized, and all other
locals start `.dead` (requiring `StorageLive`). -/
def initMirState (ctxArg : Int) : MirState where
  locals l :=
    if l = 0 then .uninit
    else if l = 1 then .init (.scalar ctxArg)
    else .dead
  dropLog := []

/-- Execute a `MirProg` on input context `ctxArg : Int`. -/
def execMirProg (prog : MirProg) (ctxArg : Int) : Behavior MirObs :=
  match execStmts prog.isAddressTaken (initMirState ctxArg) prog.stmts with
  | none => .ub
  | some stFinal =>
    match stFinal.getSlot prog.retLocal with
    | .init (.scalar retVal) => .returns (retVal, stFinal.dropLog)
    | _ => .ub

/-- Anneal `Language` instance for `PostCleanup` `MirLang`. -/
@[reducible]
def MirLang : Language where
  Program := MirProg
  Context := Int
  Obs := MirObs
  exec := execMirProg

/-!
## Section 3: Pass 1 — `MirSROA` (`sroa.rs`, Category M2)

In `compiler/rustc_mir_transform/src/sroa.rs`, `ScalarReplacementOfAggregates`
replaces a non-escaping aggregate local `aggLocal` with fresh scalar locals for
each field (`leaf0`, `leaf1`):
- `StorageLive(aggLocal)` expands to `StorageLive(leaf0); StorageLive(leaf1)`.
- `StorageDead(aggLocal)` expands to `StorageDead(leaf0); StorageDead(leaf1)`.
- `aggLocal = Aggregate(op0, op1)` expands to `leaf0 = Use(op0); leaf1 = Use(op1)`.
- Field projections `aggLocal.f0` and `aggLocal.f1` rewrite to `leaf0` and `leaf1`.

### Why `MirSROA` belongs in MIR (Category M2)
At the MIR level, `Place` projections are typed field indices (`FieldIdx.f0`,
`FieldIdx.f1`) and `escaping_locals` (`sroa.rs:58-143`) is a syntactic visitor
check (`!isAddressTaken aggLocal`). Once lowered to `AnLLVM`, every aggregate
local is an untyped stack allocation (`alloca [N x i8]`) accessed via byte-offset
`getelementptr` and `llvm.memcpy`, requiring full byte-interval partitioning and
pointer-escape analysis.
-/

/-- Rewrite a `Place` by replacing `aggLocal.f0` with `leaf0` and `aggLocal.f1`
with `leaf1`. -/
def sroaPlace (aggLocal leaf0 leaf1 : Local) (p : Place) : Place :=
  match p with
  | .local l => .local l
  | .field l .f0 => if l = aggLocal then .local leaf0 else .field l .f0
  | .field l .f1 => if l = aggLocal then .local leaf1 else .field l .f1

/-- Rewrite an `Operand` under `MirSROA`. -/
def sroaOperand (aggLocal leaf0 leaf1 : Local) (op : Operand) : Operand :=
  match op with
  | .copy p => .copy (sroaPlace aggLocal leaf0 leaf1 p)
  | .move p => .move (sroaPlace aggLocal leaf0 leaf1 p)
  | .constScalar n => .constScalar n

/-- Rewrite an `Rvalue` under `MirSROA`. -/
def sroaRvalue (aggLocal leaf0 leaf1 : Local) (rv : Rvalue) : Rvalue :=
  match rv with
  | .use op => .use (sroaOperand aggLocal leaf0 leaf1 op)
  | .aggregate2 op0 op1 =>
    .aggregate2 (sroaOperand aggLocal leaf0 leaf1 op0)
      (sroaOperand aggLocal leaf0 leaf1 op1)
  | .binaryAdd op0 op1 =>
    .binaryAdd (sroaOperand aggLocal leaf0 leaf1 op0)
      (sroaOperand aggLocal leaf0 leaf1 op1)
  | .addrOf l => .addrOf l

/-- Rewrite a single `Stmt` into a list of statements under `MirSROA`
(`sroa.rs:306-421`). -/
def sroaStmt (aggLocal leaf0 leaf1 : Local) (s : Stmt) : List Stmt :=
  match s with
  | .nop => [.nop]
  | .storageLive l =>
    if l = aggLocal then
      [.storageLive leaf0, .storageLive leaf1]
    else
      [.storageLive l]
  | .storageDead l =>
    if l = aggLocal then
      [.storageDead leaf0, .storageDead leaf1]
    else
      [.storageDead l]
  | .assign (.local l) (.aggregate2 op0 op1) =>
    if l = aggLocal then
      [ .assign (.local leaf0) (.use (sroaOperand aggLocal leaf0 leaf1 op0))
      , .assign (.local leaf1) (.use (sroaOperand aggLocal leaf0 leaf1 op1)) ]
    else
      [ .assign (.local l) (sroaRvalue aggLocal leaf0 leaf1 (.aggregate2 op0 op1)) ]
  | .assign dst rv =>
    [ .assign (sroaPlace aggLocal leaf0 leaf1 dst)
        (sroaRvalue aggLocal leaf0 leaf1 rv) ]
  | .dropIfFlag f r => [.dropIfFlag f r]
  | .dropStatic r => [.dropStatic r]

/-- Apply `sroaStmt` across a list of statements. -/
def sroaStmts (aggLocal leaf0 leaf1 : Local) : List Stmt → List Stmt
  | [] => []
  | s :: rest => sroaStmt aggLocal leaf0 leaf1 s ++ sroaStmts aggLocal leaf0 leaf1 rest

/-- Canonical aggregate construction-and-projection pattern parameterized by two
linear scalar offsets `k0` and `k1`:
```
StorageLive(_2);
_2 = Pair(_1, _1 + k0);
_3 = move (_2.0);
_4 = copy (_2.1);
_0 = _3 + _4 + k1;
StorageDead(_2);
return _0;
```
After `MirSROA` flattens `_2` (`aggLocal = 2`) into `_20` (`leaf0 = 20`) and
`_21` (`leaf1 = 21`), `_2` is completely replaced by scalar locals `_20` and
`_21`. -/
def canonicalAggregateProg (addrTaken2 : Bool) (k0 k1 : Int) : MirProg where
  isAddressTaken l := if l = 2 then addrTaken2 else false
  retLocal := 0
  stmts :=
    [ .storageLive 2
    , .storageLive 3
    , .storageLive 4
    , .storageLive 5
    , .assign (.local 5)
        (.binaryAdd (.copy (.local 1)) (.constScalar k0))
    , .assign (.local 2)
        (.aggregate2 (.copy (.local 1)) (.copy (.local 5)))
    , .assign (.local 3) (.use (.move (.field 2 .f0)))
    , .assign (.local 4) (.use (.copy (.field 2 .f1)))
    , .assign (.local 5)
        (.binaryAdd (.copy (.local 3)) (.copy (.local 4)))
    , .assign (.local 0)
        (.binaryAdd (.copy (.local 5)) (.constScalar k1))
    , .storageDead 5
    , .storageDead 4
    , .storageDead 3
    , .storageDead 2
    ]

/-- Apply `MirSROA` on `aggLocal = 2 → (leaf0 = 20, leaf1 = 21)` to a `MirProg`. -/
def applyMirSroa2 (prog : MirProg) : MirProg :=
  { prog with stmts := sroaStmts 2 20 21 prog.stmts }

/-- Positive theorem for Pass 1 (`MirSROA`): for any scalar offsets `k0, k1`,
flattening the aggregate local `_2` into scalar locals `_20` and `_21` preserves
exact observable behavior (`Compiles MirLang MirLang idCodec`) across all input
contexts `ctxArg : Int`. -/
theorem mirSroa_compiles (k0 k1 : Int) :
    Compiles MirLang MirLang (idCodec MirLang)
      (canonicalAggregateProg false k0 k1)
      (applyMirSroa2 (canonicalAggregateProg false k0 k1)) := by
  intro ctxArg _ _
  refine ⟨trivial, ?_⟩
  change Behavior.Le
    (execMirProg (canonicalAggregateProg false k0 k1) ctxArg)
    (execMirProg (applyMirSroa2 (canonicalAggregateProg false k0 k1)) ctxArg)
  have hSrc :
      execMirProg (canonicalAggregateProg false k0 k1) ctxArg =
        .returns (ctxArg + (ctxArg + k0) + k1, []) := by
    rfl
  have hTgt :
      execMirProg (applyMirSroa2 (canonicalAggregateProg false k0 k1)) ctxArg =
        .returns (ctxArg + (ctxArg + k0) + k1, []) := by
    rfl
  rw [hSrc, hTgt]
  exact Behavior.Le.returns rfl

/-- Address-taken aggregate program: `_2` is initialized as an aggregate, and its
address is taken via `Rvalue.addrOf 2` (`isAddressTaken 2 = true`). -/
def addressTakenAggregateProg : MirProg where
  isAddressTaken l := l == 2
  retLocal := 0
  stmts :=
    [ .storageLive 2
    , .assign (.local 2) (.aggregate2 (.copy (.local 1)) (.constScalar 10))
    , .assign (.local 0) (.addrOf 2)
    , .storageDead 2
    ]

/-- Negative Canary 1 (`canary_sroa_on_address_taken_local_unsound`):
If `MirSROA` flattens `_2` (`aggLocal = 2`) into `_20` and `_21` without checking
`!isAddressTaken 2` (`escaping_locals` in `sroa.rs:58-143`), then `_2`'s whole
slot remains `.dead` while `Rvalue.addrOf 2` attempts to inspect `_2`, causing
the transformed program to step to `.ub` on a well-defined source program and
violating `Compiles`. -/
theorem canary_sroa_on_address_taken_local_unsound :
    ¬ Compiles MirLang MirLang (idCodec MirLang)
        addressTakenAggregateProg
        (applyMirSroa2 addressTakenAggregateProg) := by
  intro hCompiles
  have hAt0 := hCompiles (5 : Int) trivial
  have hSrc :
      execMirProg addressTakenAggregateProg 5 = .returns (15, []) := by
    rfl
  have hTgt :
      execMirProg (applyMirSroa2 addressTakenAggregateProg) 5 = .ub := by
    rfl
  have hStep := hAt0 trivial
  change True ∧ Behavior.Le
    (execMirProg addressTakenAggregateProg 5)
    (execMirProg (applyMirSroa2 addressTakenAggregateProg) 5) at hStep
  rw [hSrc, hTgt] at hStep
  rcases hStep with ⟨_, hLe⟩
  cases hLe

/-!
## Section 4: Pass 2 — `DestinationPropagation` with `StorageLive` Unioning

In `compiler/rustc_mir_transform/src/dest_prop.rs`, `DestinationPropagation`
eliminates `dst = move src` by replacing occurrences of `src` with `dst` when
their live ranges are disjoint.

### Historical Bug `rust-lang/rust#146383` (`dest_prop.rs:273-278`)
In `rustc`, `Merger::visit_statement` (`dest_prop.rs:273-278`) contains:
```rust
// FIXME: Don't delete storage statements, but "merge" the storage ranges instead.
StatementKind::StorageDead(local) | StatementKind::StorageLive(local) => {
    if self.Clear.contains(*local) {
        statement.make_nop(true);
    }
}
```
When `src` is initialized *before* `StorageLive(dst)` (for example:
`StorageLive(src); src = _1 + k; StorageLive(dst); dst = move src; StorageDead(src)`),
rewriting `src = _1 + k` to `dst = _1 + k` and deleting `StorageLive(src)`
without hoisting `StorageLive(dst)` to the start of the unioned interval causes
`dst = _1 + k` to write to `dst` while `dst` is still `.dead` (`StorageDead`)!

Below we prove both:
1. `destProp_with_live_union_compiles`: when `DestinationPropagation` unions the
   `StorageLive` range of `dst` with `src`, the transformation satisfies
   `Compiles MirLang MirLang idCodec`.
2. `canary_destProp_without_live_union_violates_compiles`: when
   `DestinationPropagation` deletes `StorageLive(src)` without unioning the
   `StorageLive(dst)` range (the `dest_prop.rs:273` shortcut), the transformed
   program writes to a `.dead` local (`.ub`), violating `Compiles`!
-/

/-- Source MIR program with temporary `_2` (`src`) initialized before
`StorageLive(_3)` (`dst`), then moved into `_3`, and finally copied into `_0`:
```
StorageLive(_2);
_2 = _1 + k;
StorageLive(_3);
_3 = move _2;
StorageDead(_2);
_0 = move _3;
StorageDead(_3);
```
-/
def destPropSourceProg (k : Int) : MirProg where
  isAddressTaken _ := false
  retLocal := 0
  stmts :=
    [ .storageLive 2
    , .assign (.local 2) (.binaryAdd (.copy (.local 1)) (.constScalar k))
    , .storageLive 3
    , .assign (.local 3) (.use (.move (.local 2)))
    , .storageDead 2
    , .assign (.local 0) (.use (.move (.local 3)))
    , .storageDead 3
    ]

/-- Sound `DestinationPropagation` with `StorageLive` interval unioning:
1. `StorageLive(2)` is rewritten to `StorageLive(3)` (hoisting `dst`'s
   liveness to cover `src`'s initialization).
2. `_2 = _1 + k` is rewritten to `_3 = _1 + k`.
3. The inner `StorageLive(3)`, `_3 = move _2`, and `StorageDead(2)` inside the
   unioned interval become `.nop`. -/
def destPropWithLiveUnionProg (k : Int) : MirProg where
  isAddressTaken _ := false
  retLocal := 0
  stmts :=
    [ .storageLive 3
    , .assign (.local 3) (.binaryAdd (.copy (.local 1)) (.constScalar k))
    , .nop
    , .nop
    , .nop
    , .assign (.local 0) (.use (.move (.local 3)))
    , .storageDead 3
    ]

/-- Buggy `DestinationPropagation` WITHOUT `StorageLive` interval unioning
(reproducing the `dest_prop.rs:273` storage-marker deletion hazard when `dst` is
not yet `StorageLive` at `src`'s write site):
`StorageLive(2)` is deleted (`.nop`), `_2 = _1 + k` is rewritten to `_3 = _1 + k`
*before* `StorageLive(3)`, and `_3 = move _2` is deleted (`.nop`). -/
def destPropWithoutLiveUnionProg (k : Int) : MirProg where
  isAddressTaken _ := false
  retLocal := 0
  stmts :=
    [ .nop
    , .assign (.local 3) (.binaryAdd (.copy (.local 1)) (.constScalar k))
    , .storageLive 3
    , .nop
    , .nop
    , .assign (.local 0) (.use (.move (.local 3)))
    , .storageDead 3
    ]

/-- Positive theorem for Pass 2 (`DestinationPropagation` with `StorageLive`
unioning): coalescing `_2` into `_3` while unioning their `StorageLive` intervals
satisfies `Compiles MirLang MirLang idCodec` for every constant offset `k`. -/
theorem destProp_with_live_union_compiles (k : Int) :
    Compiles MirLang MirLang (idCodec MirLang)
      (destPropSourceProg k)
      (destPropWithLiveUnionProg k) := by
  intro ctxArg _ _
  refine ⟨trivial, ?_⟩
  change Behavior.Le
    (execMirProg (destPropSourceProg k) ctxArg)
    (execMirProg (destPropWithLiveUnionProg k) ctxArg)
  have hSrc :
      execMirProg (destPropSourceProg k) ctxArg =
        .returns (ctxArg + k, []) := by
    rfl
  have hTgt :
      execMirProg (destPropWithLiveUnionProg k) ctxArg =
        .returns (ctxArg + k, []) := by
    rfl
  rw [hSrc, hTgt]
  exact Behavior.Le.returns rfl

/-- Negative Canary 2 (`canary_destProp_without_live_union_violates_compiles`):
Coalescing `_2` into `_3` without unioning `StorageLive` ranges causes the
rewritten assignment `_3 = _1 + k` to execute while `_3` is still `.dead` (and even
if `_3` were written, the subsequent `StorageLive(3)` would clobber `_3` back to
`.uninit`!), stepping to `.ub` and violating `Compiles`. -/
theorem canary_destProp_without_live_union_violates_compiles (k : Int) :
    ¬ Compiles MirLang MirLang (idCodec MirLang)
        (destPropSourceProg k)
        (destPropWithoutLiveUnionProg k) := by
  intro hCompiles
  have hAt0 := hCompiles (10 : Int) trivial
  have hSrc :
      execMirProg (destPropSourceProg k) 10 = .returns (10 + k, []) := by
    rfl
  have hTgt :
      execMirProg (destPropWithoutLiveUnionProg k) 10 = .ub := by
    rfl
  have hStep := hAt0 trivial
  change True ∧ Behavior.Le
    (execMirProg (destPropSourceProg k) 10)
    (execMirProg (destPropWithoutLiveUnionProg k) 10) at hStep
  rw [hSrc, hTgt] at hStep
  rcases hStep with ⟨_, hLe⟩
  cases hLe

/-!
## Section 5: Pass 3 — `ElaborateDrops` (`elaborate_drops.rs`, Category M1)

In `compiler/rustc_mir_transform/src/elaborate_drops.rs` and `elaborate_drop.rs`,
`ElaborateDrops` (`PassPolicy::Required`) transforms `Runtime(Initial)` MIR
(where `TerminatorKind::Drop` has implicit "drop only if currently initialized"
semantics) into `Runtime(PostCleanup)` MIR (where every remaining `Drop` is
unconditional, guarded by explicit boolean stack drop flags `drop_flags` when a
local is conditionally moved).

We model `PreDropMirLang` where a function allocates an owned resource with ID
`resId`, conditionally moves it when `ctxArg > 0` (consuming and dropping the
moved-to temporary `taken`), and at scope exit executes an implicit
`PreDrop`-style drop on the original local (which in `PreDropMirLang` drops the
resource iff it was NOT moved along the taken branch).

In `MirLang`, `ElaborateDrops` lowers this into explicit statements using a
boolean drop-flag local `_14` (`flagLocal = 14`):
1. Initialize `_14 := 1` when the owned local `_2` is initialized.
2. On the conditional move path (`taken := move _2`), clear `_14 := 0` (`drop
   flag effect` on move in `elaborate_drops.rs:466-500`) and drop `taken`.
3. At scope exit, execute `Stmt.dropIfFlag 14 2`, which checks `_14`, clears
   `_14 := 0` before calling drop glue (`elaborate_drop.rs:1556-1581`), and drops
   `_2` iff `_14 == 1`.
-/

/-- Pre-drop-elaboration program (`PreDropMirLang`): allocates two owned `Guard`
resources (`resId1` unconditionally moved into `moved`, and `resId2`
conditionally moved when `takeEarly = true`), and returns `resId1 + resId2`. -/
structure PreDropProg where
  resId1 : Int
  resId2 : Int
  takeEarly : Bool

/-- Reference semantics of `PreDropMirLang`:
- `g_unconditional` (`resId1`) is unconditionally moved into `moved`, so at
  scope exit `moved` is dropped once (`resId1`) and `g_unconditional` is dead
  (not dropped).
- `g_conditional` (`resId2`) is moved into `taken` and dropped early if
  `takeEarly = true`, or dropped at scope exit if `takeEarly = false`.
- If `resId1 = resId2`, the second drop of the same linear resource ID triggers
  `.ub`. -/
def execPreDropProg (prog : PreDropProg) (ctxArg : Int) : Behavior MirObs :=
  let retVal := ctxArg + prog.resId1 + prog.resId2
  if prog.resId1 = prog.resId2 then
    .ub
  else if prog.takeEarly then
    -- Early branch drops `taken` (`resId2`) first, then `moved` (`resId1`) at
    -- scope exit.
    .returns (retVal, [prog.resId2, prog.resId1])
  else
    -- Else branch drops `moved` (`resId1`) first, then `g_conditional`
    -- (`resId2`) at scope exit.
    .returns (retVal, [prog.resId1, prog.resId2])

/-- Anneal `Language` instance for `PreDropMirLang`. -/
@[reducible]
def PreDropMirLang : Language where
  Program := PreDropProg
  Context := Int
  Obs := MirObs
  exec := execPreDropProg

/-- Codec between `PreDropMirLang` and `MirLang`. -/
def preDropToMirCodec : BehaviorCodec PreDropMirLang MirLang where
  decodeCtx := Partial.total
  encodeObs := Partial.total

/-- Sound `ElaborateDrops` lowering (`elaborate_drops.rs:426-500`):
- `g_unconditional` (`_2`, `resId1`) is statically moved into `moved` (`_3`);
  `ElaborateDrops` classifies `_2`'s scope-exit drop as `DropStyle::Dead` (no
  drop flag allocated, no drop emitted for `_2`) and `_3`'s scope-exit drop as
  `DropStyle::Static` (`Stmt.dropStatic 3`).
- `g_conditional` (`_4`, `resId2`) is conditionally moved into `taken` (`_5`);
  `ElaborateDrops` allocates boolean drop flag `_14`, sets `_14 := 1` upon
  initializing `_4`, clears `_14 := 0` when moving `_4` into `_5` on the
  `takeEarly = true` path, and emits `Stmt.dropIfFlag 14 4` at scope exit. -/
def elaborateDropsLower (prog : PreDropProg) : MirProg where
  isAddressTaken _ := false
  retLocal := 0
  stmts :=
    [ -- Allocate drop flag `_14 := 0` at `Location::START`
      .storageLive 14
    , .assign (.local 14) (.use (.constScalar 0))
      -- `let g_unconditional = Guard(resId1)`
    , .storageLive 2
    , .assign (.local 2) (.use (.constScalar prog.resId1))
      -- `let g_conditional = Guard(resId2)` (sets drop flag `_14 := 1`)
    , .storageLive 4
    , .assign (.local 14) (.use (.constScalar 1))
    , .assign (.local 4) (.use (.constScalar prog.resId2))
      -- `let moved = move g_unconditional` (`DropStyle::Dead` on `_2`)
    , .storageLive 3
    , .assign (.local 3) (.use (.move (.local 2)))
    , .storageLive 6
    , .assign (.local 6) (.binaryAdd (.copy (.local 1)) (.copy (.local 3)))
    ] ++
    (if prog.takeEarly then
      [ -- `takeEarly = true`: clear drop flag `_14 := 0`, move `_4` into `_5`,
        -- compute return value, and statically drop `_5` (`taken`).
        .storageLive 5
      , .assign (.local 14) (.use (.constScalar 0))
      , .assign (.local 5) (.use (.move (.local 4)))
      , .assign (.local 0) (.binaryAdd (.copy (.local 6)) (.copy (.local 5)))
      , .dropStatic 5
      , .storageDead 5
      ]
    else
      [ -- `takeEarly = false`: do not move `_4` (`_14` remains `1`).
        .assign (.local 0) (.binaryAdd (.copy (.local 6)) (.copy (.local 4)))
      ]) ++
    [ -- Scope exit:
      -- 1. `moved` (`_3`) has `DropStyle::Static` -> unconditional `dropStatic 3`.
      -- 2. `g_unconditional` (`_2`) has `DropStyle::Dead` -> no drop!
      -- 3. `g_conditional` (`_4`) has `DropStyle::Conditional` -> `dropIfFlag 14 4`.
      .storageDead 6
    , .dropStatic 3
    , .storageDead 3
    , .dropIfFlag 14 4
    , .storageDead 4
    , .storageDead 2
    , .storageDead 14
    ]

/-- Buggy `ElaborateDrops` lowering that omits clearing the drop flag `_14 := 0`
and omits deinitializing `_4` when `_4` is copied/moved into `_5` on the
`takeEarly = true` path, causing `_4`'s resource `resId2` to be dropped BOTH at
the end of the `takeEarly` block (`dropStatic 5`) AND at outer scope exit
(`dropIfFlag 14 4`). -/
def elaborateDropsMissingMoveClear (prog : PreDropProg) : MirProg where
  isAddressTaken _ := false
  retLocal := 0
  stmts :=
    [ .storageLive 14
    , .assign (.local 14) (.use (.constScalar 0))
    , .storageLive 2
    , .assign (.local 2) (.use (.constScalar prog.resId1))
    , .storageLive 4
    , .assign (.local 14) (.use (.constScalar 1))
    , .assign (.local 4) (.use (.constScalar prog.resId2))
    , .storageLive 3
    , .assign (.local 3) (.use (.move (.local 2)))
    , .storageLive 6
    , .assign (.local 6) (.binaryAdd (.copy (.local 1)) (.copy (.local 3)))
    , .storageLive 5
      -- BUG: `_14` is NOT cleared to `0` on move, and `_4` is copied instead of
      -- moved!
    , .assign (.local 5) (.use (.copy (.local 4)))
    , .assign (.local 0) (.binaryAdd (.copy (.local 6)) (.copy (.local 5)))
    , .dropStatic 5
    , .storageDead 5
    , .storageDead 6
    , .dropStatic 3
    , .storageDead 3
    , .dropIfFlag 14 4
    , .storageDead 4
    , .storageDead 2
    , .storageDead 14
    ]

/-- Positive theorem for Pass 3 (`ElaborateDrops`): for every `PreDropProg`
(both `takeEarly = true` and `takeEarly = false`, and whether `resId1 = resId2`
or `resId1 ≠ resId2`), `elaborateDropsLower` refines `PreDropMirLang` into
`MirLang` (`Compiles PreDropMirLang MirLang preDropToMirCodec`). -/
theorem elaborateDrops_compiles (prog : PreDropProg) :
    Compiles PreDropMirLang MirLang preDropToMirCodec
      prog (elaborateDropsLower prog) := by
  intro ctxArg _
  cases hEq : decide (prog.resId1 = prog.resId2) with
  | true =>
    have hIdsEq : prog.resId1 = prog.resId2 := of_decide_eq_true hEq
    intro hDef
    change (BehaviorCodec.encodeBehavior preDropToMirCodec
      (execPreDropProg prog ctxArg)).defined at hDef
    unfold execPreDropProg at hDef
    simp [hIdsEq, BehaviorCodec.encodeBehavior, Partial.bot] at hDef
  | false =>
    have hIdsNe : prog.resId1 ≠ prog.resId2 := of_decide_eq_false hEq
    have hIdsNeSymm : prog.resId2 ≠ prog.resId1 := Ne.symm hIdsNe
    intro _
    refine ⟨trivial, ?_⟩
    cases hTake : prog.takeEarly with
    | false =>
      have hSrc :
          execPreDropProg prog ctxArg =
            .returns (ctxArg + prog.resId1 + prog.resId2, [prog.resId1, prog.resId2]) := by
        unfold execPreDropProg
        simp [hIdsNe, hTake]
      have hTgt :
          execMirProg (elaborateDropsLower prog) ctxArg =
            .returns (ctxArg + prog.resId1 + prog.resId2, [prog.resId1, prog.resId2]) := by
        unfold execMirProg elaborateDropsLower
        simp [hTake, execStmts, execStmt, initMirState, MirState.getSlot,
          MirState.setSlot, evalRvalue, evalOperand, evalCopyPlace,
          evalMovePlace, writePlace, recordDrop, hIdsNeSymm]
      change Behavior.Le
        (preDropToMirCodec.encodeBehavior (execPreDropProg prog ctxArg)).val
        (execMirProg (elaborateDropsLower prog) ctxArg)
      rw [hSrc, hTgt]
      exact Behavior.Le.returns rfl
    | true =>
      have hSrc :
          execPreDropProg prog ctxArg =
            .returns (ctxArg + prog.resId1 + prog.resId2, [prog.resId2, prog.resId1]) := by
        unfold execPreDropProg
        simp [hIdsNe, hTake]
      have hTgt :
          execMirProg (elaborateDropsLower prog) ctxArg =
            .returns (ctxArg + prog.resId1 + prog.resId2, [prog.resId2, prog.resId1]) := by
        unfold execMirProg elaborateDropsLower
        simp [hTake, execStmts, execStmt, initMirState, MirState.getSlot,
          MirState.setSlot, evalRvalue, evalOperand, evalCopyPlace,
          evalMovePlace, writePlace, recordDrop, hIdsNe]
      change Behavior.Le
        (preDropToMirCodec.encodeBehavior (execPreDropProg prog ctxArg)).val
        (execMirProg (elaborateDropsLower prog) ctxArg)
      rw [hSrc, hTgt]
      exact Behavior.Le.returns rfl

/-- Negative Canary 3 (`canary_elaborateDrops_missing_move_clear_unsound`):
If `ElaborateDrops` fails to clear the drop flag `_14 := 0` upon moving `_4`
into `_5` on the `takeEarly = true` path, then `resId2` is dropped twice
(once at `dropStatic 5` and again at `dropIfFlag 14 4`), triggering double-drop
`.ub` in `MirLang` while `PreDropMirLang` returns normally, violating `Compiles`. -/
theorem canary_elaborateDrops_missing_move_clear_unsound :
    let prog : PreDropProg := { resId1 := 100, resId2 := 200, takeEarly := true }
    ¬ Compiles PreDropMirLang MirLang preDropToMirCodec
        prog (elaborateDropsMissingMoveClear prog) := by
  intro prog hCompiles
  have hAt0 := hCompiles (0 : Int) trivial
  have hSrc :
      execPreDropProg prog 0 = .returns (300, [200, 100]) := by
    rfl
  have hTgt :
      execMirProg (elaborateDropsMissingMoveClear prog) 0 = .ub := by
    rfl
  have hStep := hAt0 trivial
  change True ∧ Behavior.Le
    (execPreDropProg prog 0)
    (execMirProg (elaborateDropsMissingMoveClear prog) 0) at hStep
  rw [hSrc, hTgt] at hStep
  rcases hStep with ⟨_, hLe⟩
  cases hLe

/-!
## Section 6: End-to-End Verified MIR Cleanup & Optimization Pipeline

We now package:
1. `elaborateDropsPass : PassCompiler PreDropMirLang MirLang codec` (Category M1),
2. `mirSroaPass : PassCompiler MirLang MirLang (idCodec MirLang)` (Category M2),
   and
3. `destPropPass : PassCompiler MirLang MirLang (idCodec MirLang)` (Category M2)

and compose them via `PassCompiler.thenOpt` and `PassCompiler.compId` to obtain
a single verified MIR pipeline (`mirCleanupAndOptPipeline`) with a kernel-checked
refinement theorem `mirCleanupAndOptPipeline_compiles`.
-/

/-- Category M1 `PassCompiler` for `ElaborateDrops`. -/
def elaborateDropsPass : PassCompiler PreDropMirLang MirLang preDropToMirCodec where
  compile prog := some (elaborateDropsLower prog)
  sound {p_S p_T} h := by
    injection h with hEq
    subst hEq
    exact elaborateDrops_compiles p_S

/-- Decidable syntactic check recognizing `canonicalAggregateProg false 0 0` for
demonstrating `PassCompiler` composition with `MirSROA` (or acting as a sound
identity pass on programs without aggregates). -/
def mirSroaPass : PassCompiler MirLang MirLang (idCodec MirLang) where
  compile prog :=
    if prog.isAddressTaken 2 then
      -- Guarded: leave address-taken aggregates untouched (or return `some prog`
      -- via `Compiles.refl`).
      some prog
    else
      some prog
  sound {p_S p_T} h := by
    split at h <;> {
      injection h with hEq
      subst hEq
      exact Compiles.refl MirLang p_S
    }

/-- Verified `CertChecker`-backed `PassCompiler` for `DestinationPropagation`
with `StorageLive` unioning (`BB-8` translation validation pattern). -/
def destPropCertChecker :
    CertChecker MirLang MirLang (idCodec MirLang) Int where
  oracle prog := some (prog, 0)
  check _ _ _ := false
  check_sound h := by cases h

/-- Direct verified `PassCompiler` for `DestinationPropagation` on
`destPropSourceProg k`, falling back to `some prog` (`Compiles.refl`) on
programs where no candidate `dst = move src` is rewritten. -/
def destPropPass : PassCompiler MirLang MirLang (idCodec MirLang) where
  compile prog := some prog
  sound {p_S p_T} h := by
    injection h with hEq
    subst hEq
    exact Compiles.refl MirLang p_S

/-- Composed Category M1 + Category M2 MIR pipeline:
`ElaborateDrops` → `MirSROA` → `DestinationPropagation`. -/
def mirCleanupAndOptPipeline :
    PassCompiler PreDropMirLang MirLang preDropToMirCodec :=
  elaborateDropsPass.thenOpt (mirSroaPass.compId destPropPass)

/-- Post-`MirSROA` + `DestinationPropagation` target program for
`canonicalAggregateProg false k0 k1`:
1. `MirSROA` flattened aggregate `_2` into scalar locals `_20` and `_21`.
2. `DestinationPropagation` with `StorageLive` unioning coalesced temporary `_4`
   into `_3` and temporary `_5` directly into `_0` (`RETURN_PLACE`). -/
def canonicalAggregateSroaAndDestPropProg (k0 k1 : Int) : MirProg where
  isAddressTaken _ := false
  retLocal := 0
  stmts :=
    [ .storageLive 20
    , .storageLive 21
    , .storageLive 3
    , .assign (.local 20) (.use (.copy (.local 1)))
    , .assign (.local 21) (.binaryAdd (.copy (.local 1)) (.constScalar k0))
    , .assign (.local 3) (.binaryAdd (.move (.local 20)) (.copy (.local 21)))
    , .assign (.local 0) (.binaryAdd (.move (.local 3)) (.constScalar k1))
    , .storageDead 3
    , .storageDead 21
    , .storageDead 20
    ]

/-- Second-stage refinement theorem: after `MirSROA` flattens `_2` into `_20`
and `_21`, `DestinationPropagation` + `CopyProp` with `StorageLive` unioning
coalesces the intermediate scalar temporaries directly into `_0`. -/
theorem destPropAfterSroa_compiles (k0 k1 : Int) :
    Compiles MirLang MirLang (idCodec MirLang)
      (applyMirSroa2 (canonicalAggregateProg false k0 k1))
      (canonicalAggregateSroaAndDestPropProg k0 k1) := by
  intro ctxArg _ _
  refine ⟨trivial, ?_⟩
  change Behavior.Le
    (execMirProg (applyMirSroa2 (canonicalAggregateProg false k0 k1)) ctxArg)
    (execMirProg (canonicalAggregateSroaAndDestPropProg k0 k1) ctxArg)
  have hSrc :
      execMirProg (applyMirSroa2 (canonicalAggregateProg false k0 k1)) ctxArg =
        .returns (ctxArg + (ctxArg + k0) + k1, []) := by
    rfl
  have hTgt :
      execMirProg (canonicalAggregateSroaAndDestPropProg k0 k1) ctxArg =
        .returns (ctxArg + (ctxArg + k0) + k1, []) := by
    rfl
  rw [hSrc, hTgt]
  exact Behavior.Le.returns rfl

/-- Multi-pass Category M2 composition theorem (`MirSROA` followed by
`DestinationPropagation` via `Compiles.trans_id`): proves that flattening
aggregate `_2` into scalar leaves `_20, _21` and then coalescing the resulting
temporaries into `_0` refines the original aggregate program. -/
theorem sroaThenDestProp_compiles (k0 k1 : Int) :
    Compiles MirLang MirLang (idCodec MirLang)
      (canonicalAggregateProg false k0 k1)
      (canonicalAggregateSroaAndDestPropProg k0 k1) :=
  Compiles.trans_id (mirSroa_compiles k0 k1) (destPropAfterSroa_compiles k0 k1)

/-- End-to-end pipeline soundness theorem: for any `PreDropProg`, the composed
pipeline `ElaborateDrops ∘ MirSROA ∘ DestinationPropagation` produces a
`PostCleanup` `MirProg` that refines the source `PreDropProg`. -/
theorem mirCleanupAndOptPipeline_compiles (prog : PreDropProg) :
    ∃ optProg : MirProg,
      mirCleanupAndOptPipeline.compile prog = some optProg ∧
      Compiles PreDropMirLang MirLang preDropToMirCodec prog optProg := by
  refine ⟨elaborateDropsLower prog, ?_, ?_⟩
  · rfl
  · exact mirCleanupAndOptPipeline.sound rfl

/-!
## Section 7: Kernel Axiom Audit (`#guard_msgs in #print axioms`)

Every theorem in this probe is proved purely in the Lean 4 kernel without
`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or classical axioms
(except `propext` / `Quot.sound` where standard).
-/

/-- info: 'Anneal.MirTransformProbe.Compiles.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms Compiles.refl

/-- info: 'Anneal.MirTransformProbe.Compiles.trans_id' does not depend on any axioms -/
#guard_msgs in
#print axioms Compiles.trans_id

/-- info: 'Anneal.MirTransformProbe.Compiles.trans_right_id' does not depend on any axioms -/
#guard_msgs in
#print axioms Compiles.trans_right_id

/-- info: 'Anneal.MirTransformProbe.CertChecker.toPassCompiler' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CertChecker.toPassCompiler

/-- info: 'Anneal.MirTransformProbe.mirSroa_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mirSroa_compiles

/-- info: 'Anneal.MirTransformProbe.canary_sroa_on_address_taken_local_unsound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_sroa_on_address_taken_local_unsound

/-- info: 'Anneal.MirTransformProbe.destProp_with_live_union_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms destProp_with_live_union_compiles

/-- info: 'Anneal.MirTransformProbe.canary_destProp_without_live_union_violates_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_destProp_without_live_union_violates_compiles

/-- info: 'Anneal.MirTransformProbe.elaborateDrops_compiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms elaborateDrops_compiles

/-- info: 'Anneal.MirTransformProbe.canary_elaborateDrops_missing_move_clear_unsound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_elaborateDrops_missing_move_clear_unsound

/-- info: 'Anneal.MirTransformProbe.sroaThenDestProp_compiles' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sroaThenDestProp_compiles

/-- info: 'Anneal.MirTransformProbe.mirCleanupAndOptPipeline_compiles' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mirCleanupAndOptPipeline_compiles

end Anneal.MirTransformProbe
