-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Core

/-!
# Fuel Polarity, Structural vs. Environment Recursion, and Kernel Reduction in Anneal's TCB

Self-contained, `prelude`-only Lean 4.34.1 mechanization of the soundness
properties, contravariant vacuity hazards, structural-vs-fuel recursion spines,
AST indirection trade-offs, and kernel WHNF reduction laws governing `Nat` fuel
in Anneal's Trusted Computing Base (`Trusted/MirAst.lean`,
`Trusted/MirSemantics.lean`, and `theory/Anneal/MirLemmas.lean`).

Every declaration in this file is checked directly by the Lean 4 kernel under
`prelude` (importing only `Init.NotationExtra` and `Init.Core`) with zero
`sorry` axioms and zero `Classical.choice` dependencies.
-/

namespace AnnealFuelPolarityAndRecursionProbe

/-!
## Section 1: The Polarity Law of Fuel-Bounded Predicates

A fuel-bounded predicate `P : Nat → α → Prop` that returns `False` at `fuel = 0`
and grows monotonically with fuel is an **under-approximation** of its
unbounded limit `P_inf x := ∃ k, P k x`.
-/

/-- Unbounded limit of a fuel-indexed predicate family `P : Nat → α → Prop`. -/
def FuelLimit {α : Type u} (P : Nat → α → Prop) (x : α) : Prop :=
  ∃ k : Nat, P k x

/-- Every finite fuel level `k` under-approximates `FuelLimit P`.
    Consequently, in **positive (covariant)** positions—such as postconditions,
    return-value validity checks (`EnsuresRetLibInv`), or existential
    inhabitation witnesses (`NonVacuousOn`)—replacing `FuelLimit P` with `P k`
    is sound (fails closed when `k` is insufficient). -/
theorem fuel_positive_sound {α : Type u} (P : Nat → α → Prop) (k : Nat) (x : α)
    (h : P k x) : FuelLimit P x :=
  ⟨k, h⟩

/-- In **negative (contravariant)** positions—such as the antecedent of an
    implication `P k x → Q x`—under-approximating the antecedent weakens the
    implication (`(FuelLimit P x → Q x) → (P k x → Q x)`), which is the dual
    (**unsafe / fail-open**) direction if `P k x → Q x` is a theorem obligation
    or invariant admissibility check. -/
theorem fuel_negative_weakens {α : Type u} (P : Nat → α → Prop) (Q : α → Prop)
    (k : Nat) (x : α) (h_limit : FuelLimit P x → Q x) (h_fuel : P k x) : Q x :=
  h_limit ⟨k, h_fuel⟩

/-- When fuel `k` is exhausted on a valid element `x` (`FuelLimit P x` holds,
    but `¬ P k x`), any implication `P k x → Q x` with `P k x` in negative
    position holds **vacuously**, even when `Q x` is `False`. -/
theorem fuel_exhaustion_vacuous_antecedent {α : Type u} (P : Nat → α → Prop)
    (Q : α → Prop) (k : Nat) (x : α)
    (_h_valid_in_limit : FuelLimit P x) (h_exhausted : ¬ P k x) :
    P k x → Q x :=
  fun hp => False.elim (h_exhausted hp)

/-- Anneal's `NonVacuousOn` (`Trusted/Refinement.lean:141-142`) guards a single
    function's precondition by requiring positive inhabitation of the domain and
    precondition. This blocks *total* fuel exhaustion on that single domain. -/
def NonVacuousOn {State : Type u} (dom pre : State → Prop) : Prop :=
  ∃ s : State, dom s ∧ pre s

theorem nonVacuous_blocks_total_exhaustion {State : Type u}
    (dom : Nat → State → Prop) (pre : State → Prop) (k : Nat)
    (h_all_exhausted : ∀ s, ¬ dom k s) :
    ¬ NonVacuousOn (dom k) pre := by
  intro ⟨s, hdom, _⟩
  exact h_all_exhausted s hdom

/-- However, a global or per-function `NonVacuousOn` check on one type does
    **not** protect a universally quantified family of implications
    `∀ d : Decl, P k d → Q d` (such as `AdmissibleAdtInv`, which quantifies
    over every `decl ∈ adts`) if `P k d` exhausts fuel on a *specific*
    declaration `d_deep` while succeeding on a shallow declaration `d_shallow`. -/
theorem partial_exhaustion_bypasses_nonvacuity
    (P : Nat → Bool → Prop) (k : Nat)
    (h_shallow : P k false)
    (h_deep_valid : FuelLimit P true)
    (h_deep_exhausted : ¬ P k true) :
    (∃ b : Bool, P k b) ∧ (FuelLimit P true) ∧ (P k true → False) :=
  ⟨⟨false, h_shallow⟩, h_deep_valid, fun hp => h_deep_exhausted hp⟩

/-!
## Section 2: Concrete Contravariant Vacuity Exploit in `AdmissibleAdtInv` and the Two-Layer Structural/Fuel Fix

We now model the exact types and functions from `Trusted/MirAst.lean` and
`Trusted/MirSemantics.lean` at `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`.
-/

abbrev AdtId := Nat
abbrev Local := Nat

/-- First-order MIR type grammar (`Trusted/MirAst.lean:38-46`).
    Note that `MirTy` is an inductive tree: `.ref inner` shrinks `MirTy`
    structurally, whereas `.adt id` references an external table `adts`. -/
inductive MirTy where
  | usize
  | unit
  | never
  | rawPtr
  | ref (inner : MirTy)
  | adt (id : AdtId)
  deriving DecidableEq

/-- ADT declaration (`Trusted/MirAst.lean:72-86`). -/
structure AdtDecl where
  id : AdtId
  payloadTy : Option MirTy
  allFieldsPubSafe : Bool := false

/-- Reference metadata (`Trusted/MirSemantics.lean:245-256`). -/
structure RefVal where
  frameId : Nat
  loc : Local
  deriving DecidableEq

/-- Abstract MIR value (`Trusted/MirSemantics.lean:260-285`). -/
inductive MirVal where
  | uninit
  | zst
  | int (val : Nat)
  | adt (id : AdtId) (payload : MirVal)
  | ref (r : RefVal)
  deriving DecidableEq

/-- Saved caller frame (`Trusted/MirSemantics.lean:297-302`). -/
structure StackFrame where
  frameId : Nat
  locals : List MirVal

/-- Abstract execution state (`Trusted/MirSemantics.lean:321-332`). -/
structure MirState where
  frameId : Nat
  locals : List MirVal
  stack : List StackFrame

/-- Safe list indexing (`List.getElem?` in `prelude`). -/
def listGet? : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Safe list search (`List.find?` in `prelude`, structural on `List α`). -/
def listFind? (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x then some x else listFind? p xs

/-- Lookup an ADT declaration by `AdtId` (`Trusted/MirSemantics.lean:51-53`). -/
def lookupAdt (adts : List AdtDecl) (id : AdtId) : Option AdtDecl :=
  listFind? (fun d => Nat.beq d.id id) adts

/-!
### 2.1 Why `resolveRef` Requires Zero Fuel

In `Trusted/MirSemantics.lean:304-319`, `resolveRef` looks up a `RefVal` either
in the active frame (`s.frameId = r.frameId`) or in `s.stack : List StackFrame`.
Because `s.stack` is a finite inductive `List StackFrame`, scanning `s.stack`
by structural recursion (`listFind?`) terminates structurally with **zero fuel**.
We prove that a fueled stack scanner `resolveStackFueled (stack.length + 1)` is
extensionally identical to structural `listFind?`.
-/

/-- Fuel-free reference resolution (`Trusted/MirSemantics.lean:304-312`). -/
def resolveRef (s : MirState) (r : RefVal) : Option MirVal :=
  if Nat.beq r.frameId s.frameId then
    listGet? s.locals r.loc
  else
    match listFind? (fun f => Nat.beq f.frameId r.frameId) s.stack with
    | some frame => listGet? frame.locals r.loc
    | none => none

/-- Redundant fuel-bounded stack search using `fuel : Nat`. -/
def findFrameFueled : Nat → List StackFrame → Nat → Option StackFrame
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, f :: fs, targetId =>
    if Nat.beq f.frameId targetId then some f
    else findFrameFueled fuel fs targetId

/-- Proof that `findFrameFueled (stack.length + 1)` is identical to fuel-free
    structural recursion `listFind?` for every `stack : List StackFrame`. -/
theorem findFrameFueled_eq_listFind (stack : List StackFrame) (targetId : Nat) :
    findFrameFueled (stack.length + 1) stack targetId =
      listFind? (fun f => Nat.beq f.frameId targetId) stack := by
  induction stack with
  | nil => rfl
  | cons f fs ih =>
    simp only [findFrameFueled, listFind?, List.length, ih]

/-!
### 2.2 The Coupled-Fuel Bug in `MirVal.valid` and `AdmissibleAdtInv`

Suppose `MirVal.valid` is written with a single recursion parameter `fuel : Nat`
that decrements on **both** `.adt` and `.ref`, initialized with
`fuel := adts.length + 2` (or `adts.length + 1`).
-/

abbrev AdtInv := AdtId → MirVal → Prop

def defaultAdtInv : AdtInv := fun _ _ => True

/-- **Buggy single-layer coupled-fuel validity predicate**: decrements `fuel`
    on both `.adt` and `.ref`. -/
def validFuelCoupled (adts : List AdtDecl) (adtInv : AdtInv) (s : MirState)
    (localCount : Nat) : Nat → MirTy → MirVal → Prop
  | 0, _, _ => False
  | _ + 1, .usize, .int n => n < 18446744073709551616
  | _ + 1, .unit, .zst => True
  | fuel + 1, .ref inner, .ref r =>
    (if Nat.beq r.frameId s.frameId then r.loc < localCount else True) ∧
    match resolveRef s r with
    | some pointee => validFuelCoupled adts adtInv s localCount fuel inner pointee
    | none => False
  | fuel + 1, .adt id, .adt valId inner =>
    valId = id ∧
    adtInv id inner ∧
    match lookupAdt adts id with
    | some decl =>
      match decl.payloadTy with
      | none => inner = .zst
      | some payload =>
        validFuelCoupled adts adtInv s localCount fuel payload inner
    | none => False
  | _ + 1, _, _ => False

/-- Coupled-fuel entry point with `fuel := adts.length + 2`. -/
def validCoupled (adts : List AdtDecl) (adtInv : AdtInv) (s : MirState)
    (localCount : Nat) (ty : MirTy) (v : MirVal) : Prop :=
  validFuelCoupled adts adtInv s localCount (adts.length + 2) ty v

/-- `AdmissibleAdtInv` (`Trusted/MirSemantics.lean:1120-1126`) using
    `validCoupled` in the **negative (antecedent)** position. -/
def AdmissibleAdtInvCoupled (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=
  ∀ decl, decl ∈ adts →
    decl.allFieldsPubSafe = true →
    ∀ s payload inner,
      decl.payloadTy = some payload →
      validCoupled adts defaultAdtInv s 0 payload inner →
      adtInv decl.id inner

/-- A 3-deep shared reference type `&&&usize`. -/
def ref3Usize : MirTy := .ref (.ref (.ref .usize))

/-- A public safe wrapper struct `pub struct WrapRef3(pub &&&usize)` with
    `AdtId = 0`. -/
def pubRef3Adt : AdtDecl :=
  { id := 0, payloadTy := some ref3Usize, allFieldsPubSafe := true }

/-- **Theorem (Coupled Fuel Exhaustion on Acyclic Reference Chain):**
    When `adts = [pubRef3Adt]`, `adts.length + 2 = 3`. Evaluating
    `validCoupled [pubRef3Adt] defaultAdtInv s 0 (&&&usize) inner` consumes all
    3 units of fuel on the three `.ref` constructors and reaches `.usize` with
    `fuel = 0`, returning `False` for **every** state `s` and value `inner`! -/
theorem validCoupled_ref3_always_false (s : MirState) (inner : MirVal) :
    ¬ validCoupled [pubRef3Adt] defaultAdtInv s 0 ref3Usize inner := by
  intro h
  -- Unfold `validCoupled` with `[pubRef3Adt].length + 2 = 3` and `ref3Usize`:
  cases inner with
  | uninit => exact h
  | zst => exact h
  | int _ => exact h
  | adt _ _ => exact h
  | ref r1 =>
    have h1 := h.2
    revert h1
    cases resolveRef s r1 with
    | none => intro h1; exact h1
    | some v1 =>
      intro h1
      cases v1 with
      | uninit => exact h1
      | zst => exact h1
      | int _ => exact h1
      | adt _ _ => exact h1
      | ref r2 =>
        have h2 := h1.2
        revert h2
        cases resolveRef s r2 with
        | none => intro h2; exact h2
        | some v2 =>
          intro h2
          cases v2 with
          | uninit => exact h2
          | zst => exact h2
          | int _ => exact h2
          | adt _ _ => exact h2
          | ref r3 =>
            have h3 := h2.2
            revert h3
            cases resolveRef s r3 with
            | none => intro h3; exact h3
            | some v3 =>
              -- At the pointee `v3 : .usize`, remaining fuel is 0, so
              -- `validFuelCoupled ... 0 .usize v3` is definitionally `False`!
              intro h3
              exact h3

/-- **Theorem (Contravariant Vacuity Exploit in `AdmissibleAdtInvCoupled`):**
    Because `validCoupled` sits in the negative (antecedent) position of
    `AdmissibleAdtInvCoupled`, fuel exhaustion on `ref3Usize` makes
    `AdmissibleAdtInvCoupled [pubRef3Adt] badInv` hold **vacuously** for every
    `badInv : AdtInv`—including the contradictory invariant `fun _ _ => False`! -/
theorem admissibleAdtInvCoupled_vacuous_arbitrary (badInv : AdtInv) :
    AdmissibleAdtInvCoupled [pubRef3Adt] badInv := by
  intro decl hmem _hpub s payload inner hpayload hvalid
  cases hmem with
  | head =>
    injection hpayload with hpay_eq
    subst hpay_eq
    exact False.elim (validCoupled_ref3_always_false s inner hvalid)
  | tail _ hnil =>
    cases hnil

/-- Specifically, `fun _ _ => False` is accepted as an admissible ADT invariant
    for the public safe struct `pubRef3Adt`. -/
theorem admissibleAdtInvCoupled_accepts_false :
    AdmissibleAdtInvCoupled [pubRef3Adt] (fun _ _ => False) :=
  admissibleAdtInvCoupled_vacuous_arbitrary (fun _ _ => False)

/-!
### 2.3 The Exact Two-Layer Fix: Structural Recursion on `MirTy` + Fuel Only on `.adt`

In `Trusted/MirSemantics.lean:395-456` (`4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`),
Anneal separates:
1. `validStep`: structural recursion on `ty : MirTy` (consuming **0 fuel** on
   `.ref inner`, because `inner` is a strict subterm of `.ref inner` even though
   `pointee` is looked up in `s` and is not a subterm of `.ref r`), and
2. `validFuel`: fuel-bounded recursion on `fuel : Nat`, invoked **only** when
   unfolding `.adt id` via `lookupAdt adts id`.
-/

/-- Two-layer `validStep` + `validFuel`: `.ref inner` recurses structurally on
    `inner : MirTy` without consuming `fuel`, while `.adt id` consumes 1 unit of
    `fuel` per ADT unfolding step (`Trusted/MirSemantics.lean:395-456`). -/
def validStep (adts : List AdtDecl) (adtInv : AdtInv) (s : MirState)
    (localCount : Nat) (next : MirTy → MirVal → Prop) :
    MirTy → MirVal → Prop
  | .usize, .int n => n < 18446744073709551616
  | .unit, .zst => True
  | .ref inner, .ref r =>
    (if Nat.beq r.frameId s.frameId then r.loc < localCount else True) ∧
    match resolveRef s r with
    | some pointee => validStep adts adtInv s localCount next inner pointee
    | none => False
  | .adt id, .adt valId inner =>
    valId = id ∧
    adtInv id inner ∧
    match lookupAdt adts id with
    | some decl =>
      match decl.payloadTy with
      | none => inner = .zst
      | some payload => next payload inner
    | none => False
  | _, _ => False

def validFuel (adts : List AdtDecl) (adtInv : AdtInv) (s : MirState)
    (localCount : Nat) : Nat → MirTy → MirVal → Prop
  | 0, _, _ => False
  | fuel + 1, ty, v =>
    validStep adts adtInv s localCount
      (validFuel adts adtInv s localCount fuel) ty v

def valid (adts : List AdtDecl) (adtInv : AdtInv) (s : MirState)
    (localCount : Nat) (ty : MirTy) (v : MirVal) : Prop :=
  validFuel adts adtInv s localCount (adts.length + 1) ty v

def AdmissibleAdtInv (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=
  ∀ decl, decl ∈ adts →
    decl.allFieldsPubSafe = true →
    ∀ s payload inner,
      decl.payloadTy = some payload →
      valid adts defaultAdtInv s 0 payload inner →
      adtInv decl.id inner

/-- Concrete state holding a 3-deep reference chain in caller frame `frameId = 1`:
    `loc 0 = .int 42`, `loc 1 = .ref (1, 0)`, `loc 2 = .ref (1, 1)`. -/
def sampleState3 : MirState :=
  { frameId := 0
    locals := []
    stack := [{ frameId := 1
                locals := [.int 42,
                           .ref { frameId := 1, loc := 0 },
                           .ref { frameId := 1, loc := 1 }] }] }

def sampleRef3Val : MirVal :=
  .ref { frameId := 1, loc := 2 }

/-- **Theorem (`valid` Succeeds on 3-Deep Reference Under Two-Layer Split):**
    With `validStep` + `validFuel`, `sampleRef3Val` is valid at type
    `ref3Usize = &&&usize` even with `localCount = 0` and `adts = [pubRef3Adt]`. -/
theorem valid_ref3_holds :
    valid [pubRef3Adt] defaultAdtInv sampleState3 0 ref3Usize sampleRef3Val := by
  dsimp [valid, validFuel, validStep, resolveRef, listFind?, listGet?,
    sampleState3, sampleRef3Val, ref3Usize]
  refine ⟨trivial, trivial, trivial, ?_⟩
  decide

/-- **Theorem (Vacuity Exploit Eliminated):**
    Under the two-layer `validStep` + `validFuel` definition, the false
    invariant `fun _ _ => False` is **rejected** (`¬ AdmissibleAdtInv`) for
    `[pubRef3Adt]`. -/
theorem not_admissibleAdtInv_false :
    ¬ AdmissibleAdtInv [pubRef3Adt] (fun _ _ => False) := by
  intro hadm
  exact hadm pubRef3Adt (List.Mem.head []) rfl sampleState3 ref3Usize
    sampleRef3Val rfl valid_ref3_holds

/-- Furthermore, an arbitrary `n`-deep chain of shared references `&&...&usize`
    consumes **zero** ADT fuel: `validStep` never invokes its `next`
    continuation on `.ref` or `.usize`, so `validFuel ... (fuel + 1)` and
    `validFuel ... 1` are equal for every reference depth `n : Nat`! -/
def refChain : Nat → MirTy → MirTy
  | 0, base => base
  | n + 1, base => .ref (refChain n base)

theorem validStep_refChain_next_irrelevant (adts : List AdtDecl)
    (adtInv : AdtInv) (s : MirState) (localCount : Nat)
    (next1 next2 : MirTy → MirVal → Prop) :
    ∀ (n : Nat) (v : MirVal),
      validStep adts adtInv s localCount next1 (refChain n .usize) v =
        validStep adts adtInv s localCount next2 (refChain n .usize) v
  | 0, v => by cases v <;> rfl
  | n + 1, v => by
    cases v with
    | uninit | zst | int _ | adt _ _ => rfl
    | ref r =>
      dsimp [refChain, validStep]
      cases resolveRef s r with
      | none => rfl
      | some pointee =>
        dsimp
        rw [validStep_refChain_next_irrelevant adts adtInv s localCount
          next1 next2 n pointee]

/-- **Theorem (`validFuel` on `refChain n .usize` Requires Only `fuel = 1`):**
    For every reference depth `n : Nat` and every `fuel : Nat`,
    `validFuel ... (fuel + 1) (refChain n .usize) v` is equal to
    `validFuel ... 1 (refChain n .usize) v`. -/
theorem validFuel_refChain_fuel_irrelevant (adts : List AdtDecl)
    (adtInv : AdtInv) (s : MirState) (localCount fuel : Nat)
    (n : Nat) (v : MirVal) :
    validFuel adts adtInv s localCount (fuel + 1) (refChain n .usize) v =
      validFuel adts adtInv s localCount 1 (refChain n .usize) v :=
  validStep_refChain_next_irrelevant adts adtInv s localCount
    (validFuel adts adtInv s localCount fuel)
    (validFuel adts adtInv s localCount 0) n v

/-!
## Section 3: Taxonomy of the 5 Recursion Spines in `Trusted/MirSemantics.lean`

We exhibit the remaining recursion spines in `Trusted/MirSemantics.lean` and
prove why each either needs zero fuel or needs fuel on a specific non-inductive
graph edge:
1. `MirVal.isFullyInit` and `extractTransmuteBits`: structural on `v : MirVal`
   (**0 fuel**).
2. `evalProj`: dereferences `.ref r` via `resolveRef s r` (where `pointee` is
   NOT a subterm of `.ref r`), yet recurses structurally on
   `proj : List PlaceElem` (**0 fuel**).
3. `MirVal.returnRefsOk`: traverses `.adt` wrappers and dereferences `.ref r` in
   `s` **without** a `MirTy` or `List PlaceElem` spine; therefore `returnRefsStep`
   recurses structurally on `v : MirVal` for `.adt` (**0 fuel**) and spends
   `returnRefsFuel` (`5`) **only** on `.ref` hops, failing closed (`false`) in
   positive terminator position.
-/

/-- 1. Structural recursion directly on `v : MirVal` (`MirSemantics.lean:292-295`).
    Needs **0 fuel** even for arbitrarily nested `.adt` values! -/
def isFullyInit : MirVal → Bool
  | .uninit => false
  | .adt _ inner => isFullyInit inner
  | _ => true

/-- 2. Projection element (`Trusted/MirAst.lean:94-99`). -/
inductive PlaceElem where
  | deref
  | field (idx : Nat)
  deriving DecidableEq

/-- `evalProj` (`Trusted/MirSemantics.lean:522-530`): even though `.deref`
    replaces `v` with `pointee` from `resolveRef s r` (which is not structurally
    smaller than `v`), the projection list `proj : List PlaceElem` shrinks at
    every step, so `evalProj` requires **0 fuel**. -/
def evalProj (s : MirState) : MirVal → List PlaceElem → Option MirVal
  | v, [] => some v
  | .ref r, .deref :: rest =>
    match resolveRef s r with
    | some pointee => evalProj s pointee rest
    | none => none
  | .adt _ inner, .field 0 :: rest => evalProj s inner rest
  | _, _ => none

/-- 3. `returnRefsStep` + `returnRefsFuel` (`Trusted/MirSemantics.lean:334-354`):
    no `MirTy` or `List PlaceElem` is available at ` Terminator.return`, and
    the value graph in `s` can contain cyclic `RefVal` chains (`loc 0 -> loc 0`).
    Here `.adt _ inner` recurses structurally on `inner : MirVal` (0 fuel),
    while `.ref r` consumes 1 unit of `fuel` per pointer hop. -/
def returnRefsStep (s : MirState) (localCount : Nat) (next : MirVal → Bool) :
    MirVal → Bool
  | .ref r =>
    if Nat.beq r.frameId s.frameId then
      if decide (r.loc < localCount) then false
      else
        match listGet? s.locals r.loc with
        | some pointee => next pointee
        | none => false
    else
      match resolveRef s r with
      | some pointee => next pointee
      | none => false
  | .adt _ inner => returnRefsStep s localCount next inner
  | _ => true

def returnRefsFuel (s : MirState) (localCount : Nat) : Nat → MirVal → Bool
  | 0, _ => false
  | fuel + 1, v =>
    returnRefsStep s localCount (returnRefsFuel s localCount fuel) v

/-- Wrapping a reference inside arbitrarily many `.adt` constructors consumes
    **zero** `returnRefsFuel`: fuel 1 suffices regardless of ADT nesting depth! -/
def wrapAdtDepth : Nat → MirVal → MirVal
  | 0, v => v
  | n + 1, v => .adt n (wrapAdtDepth n v)

theorem returnRefsFuel_adt_depth_invariant (s : MirState) (localCount fuel : Nat)
    (n : Nat) (v : MirVal) :
    returnRefsFuel s localCount (fuel + 1) (wrapAdtDepth n v) =
      returnRefsFuel s localCount (fuel + 1) v := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [wrapAdtDepth, returnRefsFuel, returnRefsStep] at ih ⊢
    exact ih

/-!
## Section 4: AST Indirection (`BodyId`) vs. Fuel-Bounded `beqMirBodyFuel` (Category C)

At commit `5a48fba09794839a06cee0bc4fa56f98f1fbb38e`, `MirBody` embedded callee
`MirBody` trees directly inside `.call1`, forcing `beqMirBodyFuel 8` in
`theory/Anneal/MirLemmas.lean:3549-3609`. At commit
`4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`, replacing embedded `MirBody` with
`BodyId` indirection into `Crate.bodies : List BodyDecl` eliminated fuel from
`beqMirBody` and `MirBody.subst`.
-/

/-- Recursive `MirBodyRec` (modeling `5a48fba09794839a06cee0bc4fa56f98f1fbb38e`),
    where `.call1` embeds the callee `MirBodyRec` directly. -/
inductive MirBodyRec where
  | ret (localCount : Nat)
  | call1 (localCount : Nat) (callee : MirBodyRec)

/-- Fuel-bounded equality checker `beqMirBodyFuel` (`MirLemmas.lean:3549-3600`
    at `5a48fba09794839a06cee0bc4fa56f98f1fbb38e`). -/
def beqMirBodyFuel : Nat → MirBodyRec → MirBodyRec → Bool
  | 0, _, _ => false
  | _ + 1, .ret n1, .ret n2 => Nat.beq n1 n2
  | fuel + 1, .call1 n1 c1, .call1 n2 c2 =>
    Nat.beq n1 n2 && beqMirBodyFuel fuel c1 c2
  | _ + 1, _, _ => false

/-- Build a call chain of depth `d`. -/
def callChainRec : Nat → MirBodyRec
  | 0 => .ret 1
  | d + 1 => .call1 1 (callChainRec d)

/-- **Theorem (`beqMirBodyFuel` Violates Reflexivity at Depth `≥ fuel`):**
    For any fixed fuel budget `fuel : Nat` (such as `8`), `beqMirBodyFuel fuel`
    returns `false` when comparing `callChainRec fuel` to itself! -/
theorem beqMirBodyFuel_not_refl (fuel : Nat) :
    beqMirBodyFuel fuel (callChainRec fuel) (callChainRec fuel) = false := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
    simp [callChainRec, beqMirBodyFuel, Nat.beq_refl, ih]

/-- Flat `BodyId`-indexed `MirBodyFlat` (modeling `Trusted/MirAst.lean:160-200`
    at `4a7bcfdcc0f50274edd5874ba9b204cc2dac7032`). -/
abbrev BodyId := Nat

inductive MirBodyFlat where
  | ret (localCount : Nat)
  | call1 (localCount : Nat) (callee : BodyId)
  deriving DecidableEq

/-- Fuel-free structural equality checker on `MirBodyFlat`. -/
def beqMirBodyFlat : MirBodyFlat → MirBodyFlat → Bool
  | .ret n1, .ret n2 => Nat.beq n1 n2
  | .call1 n1 c1, .call1 n2 c2 => Nat.beq n1 n2 && Nat.beq c1 c2
  | _, _ => false

/-- **Theorem (`beqMirBodyFlat` is Unconditionally Reflexive and Exact):**
    Flattening `MirBody` via `BodyId` restores unconditional reflexivity
    (`beqMirBodyFlat b b = true`) and exact equivalence (`b1 = b2`) with zero
    fuel! -/
theorem beqMirBodyFlat_refl (b : MirBodyFlat) :
    beqMirBodyFlat b b = true := by
  cases b <;> simp [beqMirBodyFlat, Nat.beq_refl]

theorem beqMirBodyFlat_eq_iff (b1 b2 : MirBodyFlat) :
    beqMirBodyFlat b1 b2 = true ↔ b1 = b2 := by
  cases b1 <;> cases b2 <;>
    simp [beqMirBodyFlat, Nat.beq_eq]

/-!
## Section 5: Lean 4 Kernel `whnf` / `isDefEq` Reduction Asymmetry (`n + k` vs. `k + n`) (Category D)

In `Init/Prelude.lean:1773-1775` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`),
`Nat.add` is defined by structural recursion on its **second** argument:
```lean
protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```
Consequently, `adts.length + 1` is definitionally equal (`isDefEq` / `rfl`) to
`Nat.succ adts.length` even when `adts : List AdtDecl` is a free symbolic
variable! By contrast, `1 + adts.length` (`Nat.add 1 adts.length`) is stuck in
Weak Head Normal Form (WHNF) whenever `adts` is symbolic.
-/

def lookupTySize (tySizes : List (AdtId × Nat)) (id : AdtId) : Option Nat :=
  match listFind? (fun p => Nat.beq p.1 id) tySizes with
  | some (_, sz) => some sz
  | none => none

def tySizeStep (adts : List AdtDecl) (tySizes : List (AdtId × Nat))
    (next : MirTy → Option Nat) : MirTy → Option Nat
  | .usize | .rawPtr | .ref _ => some 8
  | .unit => some 0
  | .never => none
  | .adt id =>
    match lookupAdt adts id with
    | some decl =>
      match decl.payloadTy with
      | none => lookupTySize tySizes id
      | some payload =>
        match next payload, lookupTySize tySizes id with
        | some payloadSz, some sz =>
          if Nat.ble payloadSz sz then some sz else none
        | _, _ => none
    | none => none

def tySizeFuel (adts : List AdtDecl) (tySizes : List (AdtId × Nat)) :
    Nat → MirTy → Option Nat
  | 0, _ => none
  | fuel + 1, ty => tySizeStep adts tySizes (tySizeFuel adts tySizes fuel) ty

/-- Right-add fuel entry point (`adts.length + 1`, matching
    `Trusted/MirSemantics.lean:380-382`). -/
def tySize (adts : List AdtDecl) (tySizes : List (AdtId × Nat))
    (ty : MirTy) : Option Nat :=
  tySizeFuel adts tySizes (adts.length + 1) ty

/-- **Theorem (Kernel `rfl` Reduction on Symbolic `adts`):**
    Because `adts.length + 1` reduces in WHNF to `Nat.succ adts.length`,
    `tySize adts tySizes` reduces by `rfl` on scalar and reference types even
    when `adts` and `tySizes` are universally quantified symbolic variables! -/
theorem tySize_usize_symbolic_rfl (adts : List AdtDecl)
    (tySizes : List (AdtId × Nat)) :
    tySize adts tySizes .usize = some 8 :=
  rfl

theorem tySize_ref_chain_symbolic_rfl (adts : List AdtDecl)
    (tySizes : List (AdtId × Nat)) (inner : MirTy) :
    tySize adts tySizes (.ref inner) = some 8 :=
  rfl

/-- Moreover, `adts.length + 2` reduces in WHNF to
    `Nat.succ (Nat.succ adts.length)` by `rfl` for symbolic `adts`, allowing one
    full `.adt` unfolding plus its payload check before `adts.length` is ever
    inspected. -/
theorem right_add_two_defeq_succ_succ (n : Nat) :
    n + 2 = Nat.succ (Nat.succ n) :=
  rfl

/-- By contrast, left-addition `1 + adts.length` requires an explicit inductive
    rewrite (`Nat.succ_add` / induction on `adts.length`) before `tySizeFuel`
    can unfold its outer `fuel + 1` match on a symbolic list `adts`. -/
def tySizeLeftAdd (adts : List AdtDecl) (tySizes : List (AdtId × Nat))
    (ty : MirTy) : Option Nat :=
  tySizeFuel adts tySizes (1 + adts.length) ty

theorem nat_one_add_eq_add_one : ∀ n : Nat, 1 + n = n + 1
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (nat_one_add_eq_add_one n)

theorem tySizeLeftAdd_eq_tySize (adts : List AdtDecl)
    (tySizes : List (AdtId × Nat)) (ty : MirTy) :
    tySizeLeftAdd adts tySizes ty = tySize adts tySizes ty := by
  simp only [tySizeLeftAdd, tySize, nat_one_add_eq_add_one]

end AnnealFuelPolarityAndRecursionProbe
