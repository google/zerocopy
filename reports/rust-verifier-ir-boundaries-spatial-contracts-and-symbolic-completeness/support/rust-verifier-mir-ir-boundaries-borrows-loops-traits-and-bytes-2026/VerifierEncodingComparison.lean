-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Comparative Mechanization of Rust Verifier Semantic Encodings

This self-contained, zero-`sorry`, axiom-free Lean 4 module mechanizes the four
architectural boundaries analyzed in the companion report:

1. **Axis 1 — Mutable Borrows, Nested Reborrows, Path Lenses vs. Functional
   Prophecies (`lens_prophecy_equiv`):**
   Formalizes Anneal's Stage 2 operational frame-relative path-lens model
   (`MirVal.refVal frameId localIdx proj mutability`, resolved via
   `resolvePlace` and immediate root-tree writeback `writePlace`) alongside the
   Stage 3 functional backward-lens / prophetic loan model (used by Aeneas LLBC
   and Creusot Pearlite/Coma). Proves that for a two-field struct mutation via
   `&mut s.a` and nested reborrow `&mut *r`, Stage 2 operational path-lens
   execution produces the exact same terminal struct state as Stage 3 functional
   backward-lens composition (`lens_prophecy_equiv`). Also proves cross-frame
   writeback soundness (`cross_frame_ref_writeback_sound`), fail-closed
   dangling-reference rejection at root return (`escaping_ref_fails_closed`),
   and why co-live aliased references break independent functional backward
   lenses (`aliased_backward_lenses_clobber`).

2. **Axis 2 — Diamond CFG Joins, Branch-Local Temporaries, and State
   Canonicalization (`canonicalize_join_unifies`):**
   Formalizes a small-step unstructured MIR operational semantics (`MirState`,
   `evalStep`, `ExecNormal`) over a diamond CFG (`diamondRaw`) whose branches
   write to disjoint temporary locals (`_2` in `bb1`, `_3` in `bb2`) without
   `StorageDead`. Proves that the raw predecessor states arriving at join block
   `bb3` are unequal (`raw_diamond_join_states_ne : s_then ≠ s_else`), blocking
   a shared post-join `ExecNormal` proof; proves that asymmetric `StorageDead`
   equalizes `locals` while skewing `localGens`
   (`asymmetric_storageDead_gen_mismatch`); and proves that a Stage 3
   dead-local canonicalization pass (`canonicalizeLocals`) makes the join states
   definitionally identical (`canonicalize_join_unifies : s_then' = s_else'`)
   while preserving observable `MirReturn` behavior
   (`canonicalize_preserves_return` and `execNormal_diamond_joined`).

3. **Axis 3 — Polymorphic PME Layout Gates
   (`size_only_insufficient_for_ref_transmute` and `pme_ref_transmute_sound`):**
   Formalizes polymorphic type layout evaluation (`evalTyLayout`) for size and
   alignment, proving that size equality alone (`size_of::<Src>() ==
   size_of::<Dst>()`) is insufficient for reference transmutation when
   `align_of::<Dst>() > align_of::<Src>()`, whereas adding alignment
   divisibility (`dst.align ∣ src.align`) guarantees pointer alignment
   preservation across all valid source addresses.

4. **Axis 4 — Abstract Bytes, Struct Padding, and `IntoBytes` / `FromBytes`
   Boundaries (`intoBytes_iff_paddingFree` and
   `padded_transmute_to_int_reads_uninit`):**
   Formalizes MiniRust / Caesium's `AbstractByte` (`init byte prov | uninit`)
   alongside Anneal's structural `paddingBytes` accounting, proving that an
   initialized struct's byte encoding is completely initialized if and only if
   `paddingBytes == 0`, and that transmuting a padded struct to a scalar integer
   fails closed on `AbstractByte.uninit` while transmuting to
   `[MaybeUninit<u8>; N]` succeeds.
-/

namespace VerifierEncodingComparison

/-!
## Section 1: Axis 1 — Path Lenses vs. Functional Prophecies on Reborrows
-/

/-- Reference mutability tier in Stage 2 MIR values. -/
inductive Mutability where
  | shared
  | mut
  deriving DecidableEq, Repr

/-- Projection elements addressing a sub-place inside an owner local. -/
inductive PlaceElem where
  | deref
  | fieldA
  | fieldB
  deriving DecidableEq, Repr

/-- A MIR place consists of a root local index and a projection path. -/
structure Place where
  localIdx : Nat
  proj : List PlaceElem
  deriving DecidableEq, Repr

/-- Two-field struct value used to model partial field borrows (`&mut s.a`). -/
structure PairVal where
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

/-- Stage 2 MIR runtime value representation.
    `refVal frameId localIdx proj mutability` encodes a frame-relative path lens
    pointing to `proj` within `(frameId, localIdx)`. -/
inductive MirVal where
  | scalar (n : Nat)
  | pair (p : PairVal)
  | refVal (frameId : Nat) (localIdx : Nat) (proj : List PlaceElem)
      (mutability : Mutability)
  | uninit
  deriving DecidableEq, Repr

/-- Read a pure field projection (`fieldA` or `fieldB`) from a `MirVal` tree. -/
def evalFieldProj : MirVal → List PlaceElem → Option MirVal
  | v, [] => some v
  | .pair p, .fieldA :: rest => evalFieldProj (.scalar p.a) rest
  | .pair p, .fieldB :: rest => evalFieldProj (.scalar p.b) rest
  | _, _ => none

/-- Update a pure field projection (`fieldA` or `fieldB`) inside a `MirVal`
    tree, returning the rebuilt owner value. -/
def updateFieldProj : MirVal → List PlaceElem → MirVal → Option MirVal
  | _, [], newVal => some newVal
  | .pair p, .fieldA :: rest, newVal =>
    match updateFieldProj (.scalar p.a) rest newVal with
    | some (.scalar a') => some (.pair { p with a := a' })
    | _ => none
  | .pair p, .fieldB :: rest, newVal =>
    match updateFieldProj (.scalar p.b) rest newVal with
    | some (.scalar b') => some (.pair { p with b := b' })
    | _ => none
  | _, _, _ => none

/-- Call-stack frame store mapping `(frameId, localIdx)` to `Option MirVal`. -/
abbrev FrameStore := List (List (Option MirVal))

/-- Look up a slot in a list by index. -/
def listGetOpt : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGetOpt xs n

/-- Update a slot in a list by index, returning `none` if out of bounds. -/
def listSetOpt : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
    match listSetOpt xs n v with
    | some xs' => some (x :: xs')
    | none => none

/-- Read `(frameId, localIdx)` from a `FrameStore`. -/
def readLocal (store : FrameStore) (frameId localIdx : Nat) : Option MirVal :=
  match listGetOpt store frameId with
  | some locals =>
    match listGetOpt locals localIdx with
    | some (some v) => some v
    | _ => none
  | none => none

/-- Write `some v` to `(frameId, localIdx)` in a `FrameStore`. -/
def writeLocal (store : FrameStore) (frameId localIdx : Nat) (v : MirVal) :
    Option FrameStore :=
  match listGetOpt store frameId with
  | some locals =>
    match listSetOpt locals localIdx (some v) with
    | some locals' => listSetOpt store frameId locals'
    | none => none
  | none => none

/-- Resolved root target of a `Place` after chasing any `.deref` projections:
    `(targetFrameId, targetLocalIdx, fieldPath, requiresMut)`. -/
structure ResolvedTarget where
  frameId : Nat
  localIdx : Nat
  fieldPath : List PlaceElem
  requiresMut : Bool
  deriving DecidableEq, Repr

/-- Resolve a `Place` in `curFrame` by chasing `.deref` links up to `fuel` steps
    into its root `(frameId, localIdx, fieldPath)` lens. Any `.deref` of a
    non-`.refVal` or an uninitialized slot fails closed (`none`). -/
def resolvePlaceAux (fuel : Nat) (store : FrameStore) (curFrame localIdx : Nat)
    (accFields : List PlaceElem) (remProj : List PlaceElem) :
    Option ResolvedTarget :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match remProj with
    | [] =>
      some {
        frameId := curFrame
        localIdx := localIdx
        fieldPath := accFields
        requiresMut := false
      }
    | .deref :: rest =>
      match readLocal store curFrame localIdx with
      | some v =>
        match evalFieldProj v accFields with
        | some (.refVal targetFrame targetLocal targetProj .mut) =>
          resolvePlaceAux fuel' store targetFrame targetLocal targetProj rest
        | _ => none
      | none => none
    | .fieldA :: rest =>
      resolvePlaceAux fuel' store curFrame localIdx
        (accFields ++ [.fieldA]) rest
    | .fieldB :: rest =>
      resolvePlaceAux fuel' store curFrame localIdx
        (accFields ++ [.fieldB]) rest

/-- Resolve a `Place` in `curFrame` with default deref-chain fuel `8`. -/
def resolvePlace (store : FrameStore) (curFrame : Nat) (p : Place) :
    Option ResolvedTarget :=
  resolvePlaceAux 8 store curFrame p.localIdx [] p.proj

/-- Evaluate a `Place` to its current `MirVal` via `resolvePlace`. -/
def evalPlace (store : FrameStore) (curFrame : Nat) (p : Place) :
    Option MirVal :=
  match resolvePlace store curFrame p with
  | some tgt =>
    match readLocal store tgt.frameId tgt.localIdx with
    | some rootVal => evalFieldProj rootVal tgt.fieldPath
    | none => none
  | none => none

/-- Create a mutable borrow (`&mut p`) or nested reborrow (`&mut *r`) in
    `curFrame`: resolves `p` to its canonical root `(frameId, localIdx,
    fieldPath)` and constructs `MirVal.refVal`. -/
def evalRefMut (store : FrameStore) (curFrame : Nat) (p : Place) :
    Option MirVal :=
  match resolvePlace store curFrame p with
  | some tgt =>
    match evalPlace store curFrame p with
    | some _ =>
      some (.refVal tgt.frameId tgt.localIdx tgt.fieldPath .mut)
    | none => none
  | none => none

/-- Write `newVal` to `p` in `curFrame` by resolving `p` to its root owner local
    and immediately updating the owner tree in `store`. -/
def writePlace (store : FrameStore) (curFrame : Nat) (p : Place)
    (newVal : MirVal) : Option FrameStore :=
  match resolvePlace store curFrame p with
  | some tgt =>
    match readLocal store tgt.frameId tgt.localIdx with
    | some rootVal =>
      match updateFieldProj rootVal tgt.fieldPath newVal with
      | some rootVal' => writeLocal store tgt.frameId tgt.localIdx rootVal'
      | none => none
    | none => none
  | none => none

/-- Stage 2 operational execution of a two-field struct mutation via mutable
    field borrow and nested reborrow:
    ```rust
    let mut s = Pair { a: a0, b: b0 }; // local 1
    let r1 = &mut s.a;                 // local 2 = &mut (_1.fieldA)
    let r2 = &mut *r1;                 // local 3 = &mut (*_2)
    *r2 = v1;                          // write through nested reborrow r2
    *r1 = v2;                          // write through parent borrow r1
    ```
    Returns the final `PairVal` stored in local `1` of frame `0`. -/
def execStage2Reborrow (a0 b0 v1 v2 : Nat) : Option PairVal :=
  let initFrame : List (Option MirVal) :=
    [none, some (.pair ⟨a0, b0⟩), none, none]
  let store0 : FrameStore := [initFrame]
  match evalRefMut store0 0 { localIdx := 1, proj := [.fieldA] } with
  | none => none
  | some ref1 =>
    match writeLocal store0 0 2 ref1 with
    | none => none
    | some store1 =>
      match evalRefMut store1 0 { localIdx := 2, proj := [.deref] } with
      | none => none
      | some ref2 =>
        match writeLocal store1 0 3 ref2 with
        | none => none
        | some store2 =>
          match writePlace store2 0 { localIdx := 3, proj := [.deref] }
              (.scalar v1) with
          | none => none
          | some store3 =>
            match writePlace store3 0 { localIdx := 2, proj := [.deref] }
                (.scalar v2) with
            | none => none
            | some store4 =>
              match readLocal store4 0 1 with
              | some (.pair pFinal) => some pFinal
              | _ => none

/-- Stage 3 functional lens (`get` and backward `put` function), corresponding
    to Aeneas LLBC backward functions and FunctionalTranslation loan entries. -/
structure Lens (S A : Type) where
  get : S → A
  put : S → A → S

/-- Identity lens on `S` (used for dereference reborrows `&mut *r`). -/
def Lens.id (S : Type) : Lens S S where
  get s := s
  put _ a := a

/-- Sequential composition of a parent lens `Lens S A` and a child sub-lens
    `Lens A B`. -/
def Lens.comp (l1 : Lens S A) (l2 : Lens A B) : Lens S B where
  get s := l2.get (l1.get s)
  put s b := l1.put s (l2.put (l1.get s) b)

/-- Functional lens focusing on field `a` of `PairVal`. -/
def fieldALens : Lens PairVal Nat where
  get p := p.a
  put p a' := { p with a := a' }

/-- Functional lens focusing on field `b` of `PairVal`. -/
def fieldBLens : Lens PairVal Nat where
  get p := p.b
  put p b' := { p with b := b' }

/-- Standard lawful-lens identities (`get_put`, `put_get`, `put_put`) for
    `fieldALens` and its composition with the reborrow identity lens. -/
theorem lens_comp_laws (s : PairVal) (v1 v2 : Nat) :
    let reborrowLens := Lens.comp fieldALens (Lens.id Nat)
    reborrowLens.get (reborrowLens.put s v1) = v1 ∧
    reborrowLens.put s (reborrowLens.get s) = s ∧
    fieldALens.put (reborrowLens.put s v1) v2 = fieldALens.put s v2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Creusot / Pearlite prophetic borrow carrier `(cur, final)` together with
    Aeneas backward-function resolution: a reborrow `r2 = &mut *r1` inherits
    `r1.cur`, updates it to `v1`, and upon `r2`'s expiration hands `v1` back as
    `r1`'s updated current value before `*r1 = v2` resolves `r1`'s final
    prophecy to `v2` and writes it back into `s0` via `fieldALens.put`. -/
def execStage3Prophecy (a0 b0 v1 v2 : Nat) : PairVal :=
  let s0 : PairVal := ⟨a0, b0⟩
  let r1Cur0 : Nat := fieldALens.get s0
  let reborrowLens : Lens Nat Nat := Lens.id Nat
  let r2Cur0 : Nat := reborrowLens.get r1Cur0
  let _ := r2Cur0
  let r2Final : Nat := v1
  let r1Cur1 : Nat := reborrowLens.put r1Cur0 r2Final
  let _ := r1Cur1
  let r1Final : Nat := v2
  fieldALens.put s0 r1Final

/-- **Theorem 1 (`lens_prophecy_equiv`):**
    For all initial field values `(a0, b0)` and sequential reborrow updates
    `(v1, v2)`, Anneal's Stage 2 operational path-lens machine (`MirVal.refVal`
    + `writePlace`) and Stage 3's functional backward-lens / prophetic encoding
    produce the exact same terminal struct state `PairVal.mk v2 b0`. -/
theorem lens_prophecy_equiv (a0 b0 v1 v2 : Nat) :
    execStage2Reborrow a0 b0 v1 v2 =
      some (execStage3Prophecy a0 b0 v1 v2) := by
  rfl

/-- Stage 2 return-reference lifetime guard (`returnRefsOk`): a returned
    `MirVal` at frame `curFrame` (with `localCount` locals) is rejected if it
    contains any `refVal` pointing into the dying frame (`targetFrame ==
    curFrame ∧ targetLocal < localCount`) or any inner callee frame
    (`curFrame < targetFrame`). -/
def returnRefsOk (curFrame localCount : Nat) : MirVal → Bool
  | .scalar _ => true
  | .pair _ => true
  | .uninit => false
  | .refVal targetFrame targetLocal _ _ =>
    if curFrame == 0 then
      !(targetFrame == 0 && targetLocal < localCount) && !(0 < targetFrame)
    else
      targetFrame < curFrame

/-- Cross-frame mutable reference forwarding: when caller frame `0` passes
    `refVal 0 1 [.fieldA] .mut` into callee frame `1` (`store` has length 2) and
    callee frame `1` writes `vNew` through local `1` (`*_1 := vNew`), the write
    updates caller frame `0`'s struct field `a` directly while `returnRefsOk`
    permits returning the unit/scalar result. -/
theorem cross_frame_ref_writeback_sound (a0 b0 vNew : Nat) :
    let callerFrame : List (Option MirVal) :=
      [none, some (.pair ⟨a0, b0⟩)]
    let calleeFrame : List (Option MirVal) :=
      [some (.scalar 0), some (.refVal 0 1 [.fieldA] .mut)]
    let store0 : FrameStore := [callerFrame, calleeFrame]
    match writePlace store0 1 { localIdx := 1, proj := [.deref] }
        (.scalar vNew) with
    | some store1 =>
      readLocal store1 0 1 = some (.pair ⟨vNew, b0⟩) ∧
      returnRefsOk 1 2 (.scalar 0) = true
    | none => False := by
  exact ⟨rfl, rfl⟩

/-- Returning a `.refVal` that targets a local variable of the root frame
    (`curFrame = 0`, `targetFrame = 0`, `targetLocal = 1 < 4`) fails closed. -/
theorem escaping_ref_fails_closed :
    returnRefsOk 0 4 (.refVal 0 1 [.fieldA] .mut) = false := by
  rfl

/-- Negative boundary for Stage 3 functional lenses under raw-pointer aliasing:
    if two co-live handles use `fieldALens` simultaneously on `s0` without
    disjointness, retiring the second handle's backward function overwrites the
    first handle's mutation (`v1` is lost when `v1 ≠ v2`). -/
theorem aliased_backward_lenses_clobber (a0 b0 v1 v2 : Nat) (hne : v1 ≠ v2) :
    (fieldALens.put (fieldALens.put ⟨a0, b0⟩ v1) v2).a ≠ v1 := by
  intro hEq
  exact hne hEq.symm

/-!
## Section 2: Axis 2 — Diamond CFG Joins and State Canonicalization
-/

/-- Statement syntax for the small-step diamond CFG operational model. -/
inductive Stmt where
  | assignConst (dst : Nat) (val : Nat)
  | copyLocal (dst : Nat) (src : Nat)
  | storageDead (loc : Nat)
  | clearDead (locs : List Nat)
  deriving DecidableEq, Repr

/-- Terminator syntax for the small-step diamond CFG operational model. -/
inductive Terminator where
  | goto (target : Nat)
  | switchInt (discr : Nat) (thenBb : Nat) (elseBb : Nat)
  | return_
  deriving DecidableEq, Repr

/-- Basic block containing sequential statements and a single terminator. -/
structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator
  deriving DecidableEq, Repr

/-- First-order MIR body for intraprocedural CFG execution. -/
structure MirBody where
  localCount : Nat
  blocks : List BasicBlock
  deriving DecidableEq, Repr

/-- Small-step MIR machine state with list-backed `locals` and `localGens` so
    equality of machine states at CFG join points is decidable and
    transparent. -/
structure MirState where
  locals : List (Option MirVal)
  localGens : List Nat
  block : Nat
  stmtIdx : Nat
  deriving DecidableEq, Repr

/-- Small-step transition outcome (`silent`, `returned`, or `failed`). -/
inductive StepOutcome where
  | silent (next : MirState)
  | returned (ret : MirVal)
  | failed
  deriving DecidableEq, Repr

/-- Bump generation counter at `loc` in `localGens`. -/
def bumpGenList (gens : List Nat) (loc : Nat) : Option (List Nat) :=
  match listGetOpt gens loc with
  | some g => listSetOpt gens loc (g + 1)
  | none => none

/-- Clear a list of dead temporary locals to `none` without asymmetric
    generation skew. -/
def clearDeadList :
    List (Option MirVal) → List Nat → Option (List (Option MirVal))
  | locals, [] => some locals
  | locals, loc :: rest =>
    match listSetOpt locals loc none with
    | some locals' => clearDeadList locals' rest
    | none => none

/-- Execute one `Stmt` in `MirState`. Note that `storageDead loc` both clears
    `locals[loc]` to `none` and increments `localGens[loc]`, matching
    `Trusted/MirSemantics.lean`. -/
def evalStmt (s : MirState) (stmt : Stmt) : StepOutcome :=
  match stmt with
  | .assignConst dst val =>
    match listSetOpt s.locals dst (some (.scalar val)) with
    | some locals' =>
      .silent { s with locals := locals', stmtIdx := s.stmtIdx + 1 }
    | none => .failed
  | .copyLocal dst src =>
    match listGetOpt s.locals src with
    | some (some v) =>
      match listSetOpt s.locals dst (some v) with
      | some locals' =>
        .silent { s with locals := locals', stmtIdx := s.stmtIdx + 1 }
      | none => .failed
    | _ => .failed
  | .storageDead loc =>
    match listSetOpt s.locals loc none, bumpGenList s.localGens loc with
    | some locals', some gens' =>
      .silent {
        s with
        locals := locals'
        localGens := gens'
        stmtIdx := s.stmtIdx + 1
      }
    | _, _ => .failed
  | .clearDead locs =>
    match clearDeadList s.locals locs with
    | some locals' =>
      .silent { s with locals := locals', stmtIdx := s.stmtIdx + 1 }
    | none => .failed

/-- Execute a block `Terminator`. Jumping to `target` canonicalizes the program
    counter to `(block := target, stmtIdx := 0)`. -/
def evalTerminator (s : MirState) (term : Terminator) : StepOutcome :=
  match term with
  | .goto target =>
    .silent { s with block := target, stmtIdx := 0 }
  | .switchInt discr thenBb elseBb =>
    match listGetOpt s.locals discr with
    | some (some (.scalar n)) =>
      let target := if n != 0 then thenBb else elseBb
      .silent { s with block := target, stmtIdx := 0 }
    | _ => .failed
  | .return_ =>
    match listGetOpt s.locals 0 with
    | some (some retVal) => .returned retVal
    | _ => .failed

/-- Single small-step transition of `MirBody` from `s`. -/
def evalStep (body : MirBody) (s : MirState) : StepOutcome :=
  match listGetOpt body.blocks s.block with
  | none => .failed
  | some bb =>
    match listGetOpt bb.stmts s.stmtIdx with
    | some stmt => evalStmt s stmt
    | none => evalTerminator s bb.terminator

/-- Execute `k` silent steps from `s`, returning the resulting `MirState` if all
    `k` steps are `.silent`. -/
def runSilentSteps : Nat → MirBody → MirState → Option MirState
  | 0, _, s => some s
  | k + 1, body, s =>
    match evalStep body s with
    | .silent s' => runSilentSteps k body s'
    | _ => none

/-- Inductive normal-termination symbolic execution relation (`ExecNormal`),
    matching `Anneal.ExecNormal` in `theory/Anneal/MirLemmas.lean`. -/
inductive ExecNormal (body : MirBody) :
    MirState → (MirVal → Prop) → Prop where
  | step {s s' : MirState} {P : MirVal → Prop} :
      evalStep body s = .silent s' →
      ExecNormal body s' P →
      ExecNormal body s P
  | returned {s : MirState} {v : MirVal} {P : MirVal → Prop} :
      evalStep body s = .returned v →
      P v →
      ExecNormal body s P

/-- Uncanonicalized diamond CFG (`diamondRaw`):
    - `bb0`: `switchInt _1 -> [then: bb1, else: bb2]`
    - `bb1`: `StorageDead(_1); _2 = 42; _0 = copy _2; goto bb3` (omits
      `StorageDead` on branch-local temporary `_2`)
    - `bb2`: `StorageDead(_1); _3 = 42; _0 = copy _3; goto bb3` (omits
      `StorageDead` on branch-local temporary `_3`)
    - `bb3`: `return` -/
def diamondRaw : MirBody where
  localCount := 4
  blocks := [
    { stmts := []
      terminator := .switchInt 1 1 2 },
    { stmts := [.storageDead 1, .assignConst 2 42, .copyLocal 0 2]
      terminator := .goto 3 },
    { stmts := [.storageDead 1, .assignConst 3 42, .copyLocal 0 3]
      terminator := .goto 3 },
    { stmts := []
      terminator := .return_ }
  ]

/-- Initial entry state at `bb0` with `_1 = .scalar cond`. -/
def diamondInitState (cond : Nat) : MirState where
  locals := [none, some (.scalar cond), none, none]
  localGens := [0, 0, 0, 0]
  block := 0
  stmtIdx := 0

/-- State reached at join block `bb3` after taking the `then` branch
    (`cond = 1`, 5 silent steps: `switchInt`, `storageDead 1`, `_2 = 42`,
    `_0 = _2`, `goto 3`). -/
def rawThenJoinState : Option MirState :=
  runSilentSteps 5 diamondRaw (diamondInitState 1)

/-- State reached at join block `bb3` after taking the `else` branch
    (`cond = 0`, 5 silent steps: `switchInt`, `storageDead 1`, `_3 = 42`,
    `_0 = _3`, `goto 3`). -/
def rawElseJoinState : Option MirState :=
  runSilentSteps 5 diamondRaw (diamondInitState 0)

/-- **Negative Theorem (`raw_diamond_join_states_ne`):**
    Even though both branches of `diamondRaw` kill `_1`, assign the same return
    value `_0 = 42`, and jump to `bb3` (`block = 3, stmtIdx = 0`), their raw
    states at `bb3` are **not equal** (`rawThenJoinState ≠ rawElseJoinState`)
    because dead branch-local temporaries `_2` and `_3` retain asymmetric
    values in `locals`. -/
theorem raw_diamond_join_states_ne :
    rawThenJoinState ≠ rawElseJoinState := by
  decide

/-- Diamond CFG with asymmetric `StorageDead` (`bb1` runs `storageDead 2`, `bb2`
    runs `storageDead 3`). -/
def diamondAsymStorageDead : MirBody where
  localCount := 4
  blocks := [
    { stmts := []
      terminator := .switchInt 1 1 2 },
    { stmts := [.storageDead 1, .assignConst 2 42, .copyLocal 0 2,
        .storageDead 2]
      terminator := .goto 3 },
    { stmts := [.storageDead 1, .assignConst 3 42, .copyLocal 0 3,
        .storageDead 3]
      terminator := .goto 3 },
    { stmts := []
      terminator := .return_ }
  ]

/-- State reached at `bb3` on the `then` branch of `diamondAsymStorageDead`. -/
def asymThenJoinState : MirState where
  locals := [some (.scalar 42), none, none, none]
  localGens := [0, 1, 1, 0]
  block := 3
  stmtIdx := 0

/-- State reached at `bb3` on the `else` branch of `diamondAsymStorageDead`. -/
def asymElseJoinState : MirState where
  locals := [some (.scalar 42), none, none, none]
  localGens := [0, 1, 0, 1]
  block := 3
  stmtIdx := 0

/-- **Subtlety Theorem (`asymmetric_storageDead_gen_mismatch`):**
    When `StorageDead loc` increments `localGens[loc]` (as in Anneal's
    `Trusted/MirSemantics.lean`), emitting `storageDead 2` only in `bb1` and
    `storageDead 3` only in `bb2` makes `s_then.locals = s_else.locals` at
    `bb3`, but leaves `s_then.localGens ≠ s_else.localGens` (`[0, 1, 1, 0]` vs.
    `[0, 1, 0, 1]`), so full `MirState` equality still fails unless dead-local
    canonicalization is applied symmetrically across the dead temporary set. -/
theorem asymmetric_storageDead_gen_mismatch :
    runSilentSteps 6 diamondAsymStorageDead (diamondInitState 1) =
      some asymThenJoinState ∧
    runSilentSteps 6 diamondAsymStorageDead (diamondInitState 0) =
      some asymElseJoinState ∧
    asymThenJoinState.locals = asymElseJoinState.locals ∧
    asymThenJoinState.localGens ≠ asymElseJoinState.localGens ∧
    asymThenJoinState ≠ asymElseJoinState := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · decide
  · decide

/-- Stage 3 dead-local canonicalization pass (`canonicalizeLocals`): inserts
    symmetric `Stmt.storageDead` instructions across the branch-dead temporary
    set `deadTemps` before jumping to join block `joinBb`. -/
def canonicalizeLocals (joinBb : Nat) (deadTemps : List Nat)
    (body : MirBody) : MirBody where
  localCount := body.localCount
  blocks := body.blocks.map fun bb =>
    match bb.terminator with
    | .goto target =>
      if target == joinBb then
        { bb with stmts := bb.stmts ++ deadTemps.map Stmt.storageDead }
      else
        bb
    | _ => bb

/-- Canonicalized diamond CFG produced by Stage 3
    `canonicalizeLocals 3 [2, 3] diamondRaw`. -/
def diamondCanonical : MirBody :=
  canonicalizeLocals 3 [2, 3] diamondRaw

/-- Canonical join state at `bb3` where `_0 = .scalar 42`, dead temporaries
    `_1, _2, _3` are all `none`, and `localGens = [0, 1, 1, 1]`. -/
def canonicalJoinStateAtBb3 : MirState where
  locals := [some (.scalar 42), none, none, none]
  localGens := [0, 1, 1, 1]
  block := 3
  stmtIdx := 0

/-- **Theorem 2 (`canonicalize_join_unifies`):**
    After applying the Stage 3 dead-local canonicalization pass
    (`canonicalizeLocals 3 [2, 3]`), both the `then` branch (`cond = 1`) and the
    `else` branch (`cond = 0`) arrive at `bb3` in the **exact same** `MirState`
    (`canonicalJoinStateAtBb3`). -/
theorem canonicalize_join_unifies :
    runSilentSteps 7 diamondCanonical (diamondInitState 1) =
      some canonicalJoinStateAtBb3 ∧
    runSilentSteps 7 diamondCanonical (diamondInitState 0) =
      some canonicalJoinStateAtBb3 := by
  exact ⟨rfl, rfl⟩

/-- Shared post-join `ExecNormal` continuation lemma from
    `canonicalJoinStateAtBb3`: proved once at `bb3` and reused by both
    branches. -/
theorem execNormal_from_canonicalJoinState :
    ExecNormal diamondCanonical canonicalJoinStateAtBb3
      (fun ret => ret = .scalar 42) :=
  .returned rfl rfl

/-- Full diamond symbolic execution theorem (`execNormal_diamond_joined`):
    for every boolean branch selector `b : Bool`, `diamondCanonical` executes
    from `diamondInitState (if b then 1 else 0)` to `.returned (.scalar 42)` by
    merging both branches into `execNormal_from_canonicalJoinState` at `bb3`. -/
theorem execNormal_diamond_joined (b : Bool) :
    ExecNormal diamondCanonical (diamondInitState (if b then 1 else 0))
      (fun ret => ret = .scalar 42) := by
  cases b with
  | false =>
    exact .step rfl (.step rfl (.step rfl (.step rfl (.step rfl (.step rfl
      (.step rfl execNormal_from_canonicalJoinState))))))
  | true =>
    exact .step rfl (.step rfl (.step rfl (.step rfl (.step rfl (.step rfl
      (.step rfl execNormal_from_canonicalJoinState))))))

/-- Semantic preservation (`canonicalize_preserves_return`): on both branches,
    `diamondRaw` and `diamondCanonical` terminate with the exact same return
    value `.returned (.scalar 42)`. -/
theorem canonicalize_preserves_return (b : Bool) :
    (match runSilentSteps 5 diamondRaw
        (diamondInitState (if b then 1 else 0)) with
     | some sJoin => evalStep diamondRaw sJoin
     | none => .failed) =
    (match runSilentSteps 7 diamondCanonical
        (diamondInitState (if b then 1 else 0)) with
     | some sJoin => evalStep diamondCanonical sJoin
     | none => .failed) := by
  cases b <;> rfl

/-!
## Section 3: Axis 3 — Polymorphic Layout Gates (Size vs. Alignment)
-/

/-- Concrete layout pair `(size, align)` in bytes. -/
structure Layout where
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

/-- First-order polymorphic type syntax for Axis 3 layout checks. -/
inductive PolyTy where
  | u16
  | u32
  | array2 (elem : PolyTy)
  | param (idx : Nat)
  deriving DecidableEq, Repr

/-- Evaluate the `(size, align)` layout of a `PolyTy` under type-parameter
    environment `env : Nat → Layout`. -/
def evalTyLayout (env : Nat → Layout) : PolyTy → Layout
  | .u16 => { size := 2, align := 2 }
  | .u32 => { size := 4, align := 4 }
  | .array2 elem =>
    let l := evalTyLayout env elem
    { size := 2 * l.size, align := l.align }
  | .param idx => env idx

/-- Size-only PME check (`size_of::<Src>() == size_of::<Dst>()`). -/
def sizeOnlyGate (env : Nat → Layout) (src dst : PolyTy) : Bool :=
  (evalTyLayout env src).size == (evalTyLayout env dst).size

/-- Full reference-transmute PME gate (`size_of::<Src>() == size_of::<Dst>()`
    and `align_of::<Dst>() <= align_of::<Src>()` with power-of-two divisibility
    `align_of::<Dst>()` divides `align_of::<Src>()`). -/
def refTransmuteGate (env : Nat → Layout) (src dst : PolyTy) : Bool :=
  let ls := evalTyLayout env src
  let ld := evalTyLayout env dst
  (ls.size == ld.size) && (ld.align > 0) && (ls.align % ld.align == 0)

/-- **Axis 3 Boundary Theorem (`size_only_insufficient_for_ref_transmute`):**
    Instantiating `Src = [u16; 2]` (`size = 4, align = 2`) and `Dst = u32`
    (`size = 4, align = 4`) at address `addr = 2` satisfies `sizeOnlyGate` and
    source alignment (`addr % src.align == 0`), but violates destination
    reference alignment (`addr % dst.align != 0`) and is rejected by
    `refTransmuteGate`. -/
theorem size_only_insufficient_for_ref_transmute :
    let env : Nat → Layout := fun _ => { size := 2, align := 2 }
    let src := PolyTy.array2 (.param 0)
    let dst := PolyTy.u32
    let addr := 2
    sizeOnlyGate env src dst = true ∧
    addr % (evalTyLayout env src).align = 0 ∧
    addr % (evalTyLayout env dst).align ≠ 0 ∧
    refTransmuteGate env src dst = false := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  decide

/-- **Axis 3 Soundness Theorem (`pme_ref_transmute_sound`):**
    Whenever `srcAlign` is a multiple of `dstAlign` (`dstAlign ∣ srcAlign`) and
    `addr` is aligned to `srcAlign` (`srcAlign ∣ addr`), `addr` is guaranteed to
    be aligned to `dstAlign` (`dstAlign ∣ addr`). -/
theorem pme_ref_transmute_sound {srcAlign dstAlign addr : Nat}
    (hAlign : dstAlign ∣ srcAlign) (hAddr : srcAlign ∣ addr) :
    dstAlign ∣ addr :=
  Nat.dvd_trans hAlign hAddr

/-!
## Section 4: Axis 4 — Abstract Bytes, Padding, and `transmute` Boundaries
-/

/-- MiniRust / Caesium abstract byte representation: either initialized with a
    `UInt8` value and optional pointer provenance tag, or `.uninit` (as in
    struct padding and `MaybeUninit<T>`). -/
inductive AbstractByte where
  | init (byte : UInt8) (prov : Option Nat)
  | uninit
  deriving DecidableEq, Repr

/-- Whether every byte in a slice is initialized (`AbstractByte.init`). -/
def allBytesInit : List AbstractByte → Bool
  | [] => true
  | .init _ _ :: rest => allBytesInit rest
  | .uninit :: _ => false

/-- Decode a 4-byte sequence into a scalar `u32` (little-endian), failing closed
    (`none`) if any byte is `.uninit` (matching Rust Reference
    `[behavior.considered-undefined]` for integer reads of uninitialized
    padding). -/
def decodeU32Bytes : List AbstractByte → Option UInt32
  | [.init b0 _, .init b1 _, .init b2 _, .init b3 _] =>
    some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
      (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))
  | _ => none

/-- Decode a 4-byte sequence into `[MaybeUninit<u8>; 4]`, which accepts both
    `.init` and `.uninit` bytes as long as the byte length is 4. -/
def decodeMaybeUninit4 (bytes : List AbstractByte) :
    Option (List AbstractByte) :=
  if bytes.length == 4 then some bytes else none

/-- Encode a 2-field `#[repr(C)]` struct with `fieldBytes` and `padCount`
    inter-field padding bytes. -/
def encodeStructWithPadding (b0 b2 b3 : UInt8) (padCount : Nat) :
    List AbstractByte :=
  [.init b0 none] ++ List.replicate padCount AbstractByte.uninit ++
    [.init b2 none, .init b3 none]

/-- **Axis 4 Characterization Theorem (`intoBytes_iff_paddingFree`):**
    For a struct with initialized fields (`b0, b2, b3`) and `padCount` padding
    bytes, its byte representation is completely initialized (`allBytesInit =
    true`, the semantic prerequisite for `zerocopy::IntoBytes`) if and only if
    `padCount = 0`. -/
theorem intoBytes_iff_paddingFree (b0 b2 b3 : UInt8) (padCount : Nat) :
    allBytesInit (encodeStructWithPadding b0 b2 b3 padCount) = true ↔
      padCount = 0 := by
  cases padCount with
  | zero =>
    simp [encodeStructWithPadding, allBytesInit]
  | succ k =>
    simp [encodeStructWithPadding, List.replicate, allBytesInit]

/-- **Axis 4 Boundary Theorem (`padded_transmute_to_int_reads_uninit`):**
    For `#[repr(C)] struct Padded { a: u8, /* 1 pad byte */ b: u16 }`
    (`padCount = 1`), transmuting the 4-byte representation to `u32` fails
    closed (`decodeU32Bytes = none`) because byte 1 is `AbstractByte.uninit`,
    whereas transmuting to `[MaybeUninit<u8>; 4]` succeeds. -/
theorem padded_transmute_to_int_reads_uninit (b0 b2 b3 : UInt8) :
    let bytes := encodeStructWithPadding b0 b2 b3 1
    decodeU32Bytes bytes = none ∧
    decodeMaybeUninit4 bytes = some bytes := by
  exact ⟨rfl, rfl⟩

end VerifierEncodingComparison
