-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.Data.Option.Basic
public import Anneal.InitLemmas
public import Anneal.Backend.Rules

public section

/-!
# Contextual Facts and Guard Elision (`Anneal.Backend.CtxFact`)

Formalizes `TrustTier.proven` candidate filtering, value-evaluated runtime
assertion guards, and conditional execution refinement:

1. **Strict `TrustTier.proven` Filter (`extractProvenFacts`):** `fuzz` and
   `sorryStub` candidates are discarded structurally before guard checking or
   contextual rewrite validation.
2. **Value-Evaluated `CtxFact` and `GuardCond`:** Contextual invariants
   (`ltPow2`, `addNoOverflow`, `subNoUnderflow`) and runtime assertion guards
   (`addNoOverflow`, `subNoUnderflow`, `shiftLt64`, `ltPow2`) evaluate directly
   over DAG node values. A failed `GuardCond` yields a defined panic abort
   (`.aborted ()`) rather than undefined behavior.
3. **Conditional Refinement (`SemRefinesUnder`) and Guard Discharge
   (`checkGuardsDischarged_ne_false`):** Proves that whenever all filtered
   `CtxFact`s hold on an input environment, every discharged `GuardCond`
   evaluates to `true` whenever its operands are non-poison.
-/

namespace Anneal.Backend

open Anneal.InitLemmas

/-! ## 1. Total Structural List Lookup Helpers (`0` `._unsafe_rec`) -/

/-- Structural `List` indexing via `List.foldr` emitting zero `._unsafe_rec`
auxiliaries. -/
@[expose] def listNthOpt {α : Type} (xs0 : List α) (n0 : Nat) : Option α :=
  List.foldr
    (fun x ih n =>
      match n with
      | 0 => some x
      | k + 1 => ih k)
    (fun _ => none)
    xs0 n0

theorem listNthOpt_lt_of_some {α : Type} :
    ∀ (xs : List α) (n : Nat) {v : α},
      listNthOpt xs n = some v → n < xs.length
  | [] => fun _ _ h => by nomatch h
  | _ :: _ => fun n _ h =>
    match n with
    | 0 => Nat.zero_lt_succ _
    | k + 1 => Nat.succ_lt_succ (listNthOpt_lt_of_some _ k h)

theorem listNthOpt_append_left {α : Type} :
    ∀ (xs ys : List α) {n : Nat},
      n < xs.length → listNthOpt (xs ++ ys) n = listNthOpt xs n
  | [] => fun _ _ h => absurd h (Nat.not_lt_zero _)
  | _ :: xs => fun ys n h =>
    match n with
    | 0 => rfl
    | _k + 1 => listNthOpt_append_left xs ys (Nat.lt_of_succ_lt_succ h)

theorem listNthOpt_append_singleton {α : Type} :
    ∀ (xs : List α) (x : α), listNthOpt (xs ++ [x]) xs.length = some x
  | [] => fun _ => rfl
  | _ :: xs => fun x => listNthOpt_append_singleton xs x

/-! ## 2. `TrustTier.proven`-Only Fact Admission -/

/-- Provenance tier of a candidate invariant. Only `.proven` entries are
retained by `extractProvenFacts`. -/
inductive TrustTier where
  | proven
  | fuzz
  | sorryStub

/-- Value-level contextual invariants over DAG node IDs. -/
inductive CtxFact where
  | ltPow2 (nodeId : Nat) (exp : Nat)
  | addNoOverflow (lhsId rhsId : Nat)
  | subNoUnderflow (lhsId rhsId : Nat)

/-- An invariant candidate tagged with its verification tier. -/
structure CandidateFact where
  tier : TrustTier
  fact : CtxFact

/-- Retain strictly `TrustTier.proven` facts (`List.foldr`, `0` `._unsafe_rec`).
-/
@[expose] def extractProvenFacts (cs : List CandidateFact) : List CtxFact :=
  List.foldr
    (fun c acc =>
      match c.tier with
      | .proven => c.fact :: acc
      | .fuzz => acc
      | .sorryStub => acc)
    [] cs

/-- Every fact admitted by `extractProvenFacts` came from a `.proven` entry. -/
theorem extractProvenFacts_mem_proven :
    ∀ (cs : List CandidateFact) (f : CtxFact),
      f ∈ extractProvenFacts cs → CandidateFact.mk .proven f ∈ cs
  | [] => fun _ hMem => by cases hMem
  | c :: cs => fun f hMem => by
    cases c with
    | mk tier _fact =>
      cases tier with
      | proven =>
        dsimp only [extractProvenFacts, List.foldr] at hMem
        cases hMem with
        | head => exact List.Mem.head _
        | tail _ hTl =>
          exact List.Mem.tail _ (extractProvenFacts_mem_proven cs f hTl)
      | fuzz =>
        exact List.Mem.tail _ (extractProvenFacts_mem_proven cs f hMem)
      | sorryStub =>
        exact List.Mem.tail _ (extractProvenFacts_mem_proven cs f hMem)

/-! ## 3. Denotation of `CtxFact`s and Concrete Witness Evaluation -/

/-- Whether a `CtxFact` holds over evaluated DAG node values `vals`. -/
@[expose] def CtxFactHolds (vals : List (PoisonOr Nat)) : CtxFact → Prop
  | .ltPow2 nid exp =>
    ∀ v, listNthOpt vals nid = some (.val v) → v < Nat.pow 2 exp
  | .addNoOverflow lid rid =>
    ∀ a b, listNthOpt vals lid = some (.val a) →
      listNthOpt vals rid = some (.val b) → a + b < u64Mod
  | .subNoUnderflow lid rid =>
    ∀ a b, listNthOpt vals lid = some (.val a) →
      listNthOpt vals rid = some (.val b) → b ≤ a

/-- All contextual facts in `ctx` hold over `vals`. -/
@[expose] def AllCtxFactsHold (vals : List (PoisonOr Nat))
    (ctx : List CtxFact) : Prop :=
  ∀ idx f, listNthOpt ctx idx = some f → CtxFactHolds vals f

/-- Executable Boolean witness checker for concrete satisfiability proofs. -/
@[expose] def evalCtxFactConcrete (vals : List (PoisonOr Nat)) :
    CtxFact → Bool
  | .ltPow2 nid exp =>
    match listNthOpt vals nid with
    | none => false
    | some p =>
      match p with
      | .poison => false
      | .val w => Nat.blt w (Nat.pow 2 exp)
  | .addNoOverflow lid rid =>
    match listNthOpt vals lid with
    | none => false
    | some pa =>
      match pa with
      | .poison => false
      | .val wa =>
        match listNthOpt vals rid with
        | none => false
        | some pb =>
          match pb with
          | .poison => false
          | .val wb => Nat.blt (wa + wb) u64Mod
  | .subNoUnderflow lid rid =>
    match listNthOpt vals lid with
    | none => false
    | some pa =>
      match pa with
      | .poison => false
      | .val wa =>
        match listNthOpt vals rid with
        | none => false
        | some pb =>
          match pb with
          | .poison => false
          | .val wb => Nat.ble wb wa

@[expose] def evalCtxFactsConcrete (vals : List (PoisonOr Nat))
    (ctx : List CtxFact) : Bool :=
  List.foldr (fun f acc => evalCtxFactConcrete vals f && acc) true ctx

theorem evalCtxFactConcrete_sound (vals : List (PoisonOr Nat)) (f : CtxFact)
    (h : evalCtxFactConcrete vals f = true) : CtxFactHolds vals f := by
  revert h
  cases f with
  | ltPow2 nid exp =>
    dsimp only [evalCtxFactConcrete, CtxFactHolds]
    cases listNthOpt vals nid with
    | none => intro h; cases h
    | some p =>
      dsimp only
      cases p with
      | poison => intro h; cases h
      | val w =>
        dsimp only
        intro hBlt v hV
        injection hV with hPv
        injection hPv with hEq
        rw [← hEq]
        exact (nat_blt_iff _ _).1 hBlt
  | addNoOverflow lid rid =>
    dsimp only [evalCtxFactConcrete, CtxFactHolds]
    cases listNthOpt vals lid with
    | none => intro h; cases h
    | some pa =>
      dsimp only
      cases pa with
      | poison => intro h; cases h
      | val wa =>
        dsimp only
        cases listNthOpt vals rid with
        | none => intro h; cases h
        | some pb =>
          dsimp only
          cases pb with
          | poison => intro h; cases h
          | val wb =>
            dsimp only
            intro hBlt a b hVa hVb
            injection hVa with hPa
            injection hPa with hEqA
            injection hVb with hPb
            injection hPb with hEqB
            rw [← hEqA, ← hEqB]
            exact (nat_blt_iff _ _).1 hBlt
  | subNoUnderflow lid rid =>
    dsimp only [evalCtxFactConcrete, CtxFactHolds]
    cases listNthOpt vals lid with
    | none => intro h; cases h
    | some pa =>
      dsimp only
      cases pa with
      | poison => intro h; cases h
      | val wa =>
        dsimp only
        cases listNthOpt vals rid with
        | none => intro h; cases h
        | some pb =>
          dsimp only
          cases pb with
          | poison => intro h; cases h
          | val wb =>
            dsimp only
            intro hBle a b hVa hVb
            injection hVa with hPa
            injection hPa with hEqA
            injection hVb with hPb
            injection hPb with hEqB
            rw [← hEqA, ← hEqB]
            exact (nat_ble_iff _ _).1 hBle

theorem allCtxFactsHold_of_evalConcrete (vals : List (PoisonOr Nat)) :
    ∀ (ctx : List CtxFact),
      evalCtxFactsConcrete vals ctx = true → AllCtxFactsHold vals ctx
  | [] => fun _ _ _ hNth => by nomatch hNth
  | f :: fs => fun h idx fc hNth => by
    cases idx with
    | zero =>
      dsimp only [listNthOpt] at hNth
      injection hNth with hEq
      rw [← hEq]
      exact evalCtxFactConcrete_sound vals f (bool_and_left h)
    | succ k =>
      exact allCtxFactsHold_of_evalConcrete vals fs (bool_and_right h) k fc hNth

/-! ## 4. Conditional Execution Refinement (`SemRefinesUnder`) -/

/-- Observable outcomes of executing an expression block. -/
inductive ExecOutcome (Val Mem : Type) where
  | returned (v : Val) (m : Mem)
  | aborted (m : Mem)
  | faultUB
  | diverged

/-- Conditional refinement (`semSrc ⊒_P semTgt`): on every input satisfying
`EntryPre` where `semSrc` cannot fault with undefined behavior, `semTgt` cannot
fault with undefined behavior and every `semTgt` outcome is a `semSrc` outcome.
-/
@[expose] def SemRefinesUnder {Q Val Mem : Type} (EntryPre : Q → Prop)
    (semSrc semTgt : Q → ExecOutcome Val Mem → Prop) : Prop :=
  ∀ q, EntryPre q →
    (¬ semSrc q .faultUB) →
    (¬ semTgt q .faultUB) ∧
    (∀ out, semTgt q out → semSrc q out)

/-- Unconditional refinement over all inputs (`EntryPre := True`). -/
@[expose] def SemRefines {Q Val Mem : Type}
    (semSrc semTgt : Q → ExecOutcome Val Mem → Prop) : Prop :=
  SemRefinesUnder (fun _ => True) semSrc semTgt

theorem semRefinesUnder_refl {Q Val Mem : Type} (EntryPre : Q → Prop)
    (sem : Q → ExecOutcome Val Mem → Prop) :
    SemRefinesUnder EntryPre sem sem :=
  fun _ _ hNoUb => ⟨hNoUb, fun _ h => h⟩

theorem semRefinesUnder_trans {Q Val Mem : Type} {EntryPre : Q → Prop}
    {s1 s2 s3 : Q → ExecOutcome Val Mem → Prop}
    (h12 : SemRefinesUnder EntryPre s1 s2)
    (h23 : SemRefinesUnder EntryPre s2 s3) :
    SemRefinesUnder EntryPre s1 s3 := by
  intro q hPre hNoUb1
  have ⟨hNoUb2, hSub12⟩ := h12 q hPre hNoUb1
  have ⟨hNoUb3, hSub23⟩ := h23 q hPre hNoUb2
  exact ⟨hNoUb3, fun out h3 => hSub12 out (hSub23 out h3)⟩

theorem semRefines_refl {Q Val Mem : Type}
    (sem : Q → ExecOutcome Val Mem → Prop) : SemRefines sem sem :=
  semRefinesUnder_refl (fun _ => True) sem

theorem semRefines_trans {Q Val Mem : Type}
    {s1 s2 s3 : Q → ExecOutcome Val Mem → Prop}
    (h12 : SemRefines s1 s2) (h23 : SemRefines s2 s3) : SemRefines s1 s3 :=
  semRefinesUnder_trans h12 h23

/-! ## 5. Value-Evaluated Assertion Guards (`GuardCond`) and Discharge -/

/-- Runtime assertion guard evaluated over DAG node values:
- `addNoOverflow`: checked unsigned addition (`a + b < 2 ^ 64`);
- `subNoUnderflow`: checked unsigned subtraction (`b ≤ a`);
- `shiftLt64`: checked shift count (`amt < 64`);
- `ltPow2`: bounded range check (`v < 2 ^ exp`).
When a guard evaluates to `some false`, execution aborts cleanly (`.aborted ()`)
rather than faulting with `.faultUB`. -/
inductive GuardCond where
  | addNoOverflow (lhsId rhsId : Nat)
  | subNoUnderflow (lhsId rhsId : Nat)
  | shiftLt64 (amtId : Nat)
  | ltPow2 (nodeId exp : Nat)

@[expose] def GuardCond.beq : GuardCond → GuardCond → Bool
  | .addNoOverflow a1 b1, .addNoOverflow a2 b2 =>
    Nat.beq a1 a2 && Nat.beq b1 b2
  | .subNoUnderflow a1 b1, .subNoUnderflow a2 b2 =>
    Nat.beq a1 a2 && Nat.beq b1 b2
  | .shiftLt64 a1, .shiftLt64 a2 => Nat.beq a1 a2
  | .ltPow2 n1 e1, .ltPow2 n2 e2 => Nat.beq n1 n2 && Nat.beq e1 e2
  | _, _ => false

theorem guardCond_eq_of_beq :
    ∀ {g1 g2 : GuardCond}, GuardCond.beq g1 g2 = true → g1 = g2
  | .addNoOverflow _a1 _b1, .addNoOverflow _a2 _b2, h => by
    rw [nat_eq_of_beq (bool_and_left h), nat_eq_of_beq (bool_and_right h)]
  | .subNoUnderflow _a1 _b1, .subNoUnderflow _a2 _b2, h => by
    rw [nat_eq_of_beq (bool_and_left h), nat_eq_of_beq (bool_and_right h)]
  | .shiftLt64 _a1, .shiftLt64 _a2, h =>
    congrArg GuardCond.shiftLt64 (nat_eq_of_beq h)
  | .ltPow2 _n1 _e1, .ltPow2 _n2 _e2, h => by
    rw [nat_eq_of_beq (bool_and_left h), nat_eq_of_beq (bool_and_right h)]
  | .addNoOverflow _ _, .subNoUnderflow _ _, h
  | .addNoOverflow _ _, .shiftLt64 _, h
  | .addNoOverflow _ _, .ltPow2 _ _, h
  | .subNoUnderflow _ _, .addNoOverflow _ _, h
  | .subNoUnderflow _ _, .shiftLt64 _, h
  | .subNoUnderflow _ _, .ltPow2 _ _, h
  | .shiftLt64 _, .addNoOverflow _ _, h
  | .shiftLt64 _, .subNoUnderflow _ _, h
  | .shiftLt64 _, .ltPow2 _ _, h
  | .ltPow2 _ _, .addNoOverflow _ _, h
  | .ltPow2 _ _, .subNoUnderflow _ _, h
  | .ltPow2 _ _, .shiftLt64 _, h => nomatch h

@[expose] def guardListBeq (gs1 gs2 : List GuardCond) : Bool :=
  List.foldr
    (fun g1 ih ys =>
      match ys with
      | [] => false
      | g2 :: ys' => GuardCond.beq g1 g2 && ih ys')
    (fun ys =>
      match ys with
      | [] => true
      | _ :: _ => false)
    gs1 gs2

theorem eq_of_guardListBeq :
    ∀ (gs1 gs2 : List GuardCond), guardListBeq gs1 gs2 = true → gs1 = gs2
  | [] => fun gs2 h => by
    cases gs2 with
    | nil => rfl
    | cons _ _ => nomatch h
  | g1 :: gs1' => fun gs2 h => by
    cases gs2 with
    | nil => nomatch h
    | cons g2 gs2' =>
      dsimp only [guardListBeq, List.foldr] at h
      rw [guardCond_eq_of_beq (bool_and_left h),
        eq_of_guardListBeq gs1' gs2' (bool_and_right h)]

/-- Evaluate one `GuardCond` against `vals`: `none` if an operand is missing or
`.poison` (branching on poison), `some false` on panic abort, `some true` when
satisfied. -/
@[expose] def evalGuard (vals : List (PoisonOr Nat)) : GuardCond → Option Bool
  | .addNoOverflow lid rid =>
    match listNthOpt vals lid with
    | none => none
    | some pa =>
      match pa with
      | .poison => none
      | .val a =>
        match listNthOpt vals rid with
        | none => none
        | some pb =>
          match pb with
          | .poison => none
          | .val b => some (Nat.blt (a + b) u64Mod)
  | .subNoUnderflow lid rid =>
    match listNthOpt vals lid with
    | none => none
    | some pa =>
      match pa with
      | .poison => none
      | .val a =>
        match listNthOpt vals rid with
        | none => none
        | some pb =>
          match pb with
          | .poison => none
          | .val b => some (Nat.ble b a)
  | .shiftLt64 amtId =>
    match listNthOpt vals amtId with
    | none => none
    | some pa =>
      match pa with
      | .poison => none
      | .val a => some (Nat.blt a 64)
  | .ltPow2 nid exp =>
    match listNthOpt vals nid with
    | none => none
    | some pa =>
      match pa with
      | .poison => none
      | .val a => some (Nat.blt a (Nat.pow 2 exp))

/-- Evaluate sequential assertion guards left to right (`0` `._unsafe_rec`). -/
@[expose] def evalGuards (vals : List (PoisonOr Nat))
    (gs0 : List GuardCond) : Option Bool :=
  List.foldr
    (fun g acc =>
      match evalGuard vals g with
      | none => none
      | some b =>
        match b with
        | false => some false
        | true => acc)
    (some true)
    gs0

@[expose] def hasAddNoOverflowFact (lid rid : Nat)
    (ctx : List CtxFact) : Bool :=
  List.foldr
    (fun f acc =>
      let hit :=
        match f with
        | .addNoOverflow a b => Nat.beq a lid && Nat.beq b rid
        | _ => false
      hit || acc)
    false ctx

@[expose] def hasSubNoUnderflowFact (lid rid : Nat)
    (ctx : List CtxFact) : Bool :=
  List.foldr
    (fun f acc =>
      let hit :=
        match f with
        | .subNoUnderflow a b => Nat.beq a lid && Nat.beq b rid
        | _ => false
      hit || acc)
    false ctx

@[expose] def hasLtPow2BoundFact (nid maxExp : Nat)
    (ctx : List CtxFact) : Bool :=
  List.foldr
    (fun f acc =>
      let hit :=
        match f with
        | .ltPow2 fnid k => Nat.beq fnid nid && Nat.ble k maxExp
        | _ => false
      hit || acc)
    false ctx

theorem hasAddNoOverflowFact_sound (lid rid : Nat)
    (vals : List (PoisonOr Nat)) :
    ∀ (ctx : List CtxFact),
      AllCtxFactsHold vals ctx →
      hasAddNoOverflowFact lid rid ctx = true →
      CtxFactHolds vals (.addNoOverflow lid rid)
  | [] => fun _ h => nomatch h
  | f :: fs => fun hAll hHas => by
    cases f with
    | addNoOverflow a b =>
      change ((Nat.beq a lid && Nat.beq b rid) ||
        hasAddNoOverflowFact lid rid fs) = true at hHas
      cases hHit : (Nat.beq a lid && Nat.beq b rid) with
      | true =>
        have ha : a = lid := nat_eq_of_beq (bool_and_left hHit)
        have hb : b = rid := nat_eq_of_beq (bool_and_right hHit)
        have h0 := hAll 0 (.addNoOverflow a b) rfl
        rw [ha, hb] at h0
        exact h0
      | false =>
        rw [hHit, Bool.false_or] at hHas
        exact hasAddNoOverflowFact_sound lid rid vals fs
          (fun i fc hi => hAll (i + 1) fc hi) hHas
    | ltPow2 _ _ =>
      change hasAddNoOverflowFact lid rid fs = true at hHas
      exact hasAddNoOverflowFact_sound lid rid vals fs
        (fun i fc hi => hAll (i + 1) fc hi) hHas
    | subNoUnderflow _ _ =>
      change hasAddNoOverflowFact lid rid fs = true at hHas
      exact hasAddNoOverflowFact_sound lid rid vals fs
        (fun i fc hi => hAll (i + 1) fc hi) hHas

theorem hasSubNoUnderflowFact_sound (lid rid : Nat)
    (vals : List (PoisonOr Nat)) :
    ∀ (ctx : List CtxFact),
      AllCtxFactsHold vals ctx →
      hasSubNoUnderflowFact lid rid ctx = true →
      CtxFactHolds vals (.subNoUnderflow lid rid)
  | [] => fun _ h => nomatch h
  | f :: fs => fun hAll hHas => by
    cases f with
    | subNoUnderflow a b =>
      change ((Nat.beq a lid && Nat.beq b rid) ||
        hasSubNoUnderflowFact lid rid fs) = true at hHas
      cases hHit : (Nat.beq a lid && Nat.beq b rid) with
      | true =>
        have ha : a = lid := nat_eq_of_beq (bool_and_left hHit)
        have hb : b = rid := nat_eq_of_beq (bool_and_right hHit)
        have h0 := hAll 0 (.subNoUnderflow a b) rfl
        rw [ha, hb] at h0
        exact h0
      | false =>
        rw [hHit, Bool.false_or] at hHas
        exact hasSubNoUnderflowFact_sound lid rid vals fs
          (fun i fc hi => hAll (i + 1) fc hi) hHas
    | ltPow2 _ _ =>
      change hasSubNoUnderflowFact lid rid fs = true at hHas
      exact hasSubNoUnderflowFact_sound lid rid vals fs
        (fun i fc hi => hAll (i + 1) fc hi) hHas
    | addNoOverflow _ _ =>
      change hasSubNoUnderflowFact lid rid fs = true at hHas
      exact hasSubNoUnderflowFact_sound lid rid vals fs
        (fun i fc hi => hAll (i + 1) fc hi) hHas

theorem hasLtPow2BoundFact_sound (nid maxExp : Nat)
    (vals : List (PoisonOr Nat)) :
    ∀ (ctx : List CtxFact),
      AllCtxFactsHold vals ctx →
      hasLtPow2BoundFact nid maxExp ctx = true →
      CtxFactHolds vals (.ltPow2 nid maxExp)
  | [] => fun _ h => nomatch h
  | f :: fs => fun hAll hHas => by
    cases f with
    | ltPow2 fnid k =>
      change ((Nat.beq fnid nid && Nat.ble k maxExp) ||
        hasLtPow2BoundFact nid maxExp fs) = true at hHas
      cases hHit : (Nat.beq fnid nid && Nat.ble k maxExp) with
      | true =>
        have hId : fnid = nid := nat_eq_of_beq (bool_and_left hHit)
        have hLe : k ≤ maxExp := (nat_ble_iff _ _).1 (bool_and_right hHit)
        have h0 := hAll 0 (.ltPow2 fnid k) rfl
        dsimp only [CtxFactHolds] at h0
        rw [hId] at h0
        intro v hV
        exact Nat.lt_of_lt_of_le (h0 v hV) (nat_two_pow_le_of_le hLe)
      | false =>
        rw [hHit, Bool.false_or] at hHas
        exact hasLtPow2BoundFact_sound nid maxExp vals fs
          (fun i fc hi => hAll (i + 1) fc hi) hHas
    | addNoOverflow _ _ =>
      change hasLtPow2BoundFact nid maxExp fs = true at hHas
      exact hasLtPow2BoundFact_sound nid maxExp vals fs
        (fun i fc hi => hAll (i + 1) fc hi) hHas
    | subNoUnderflow _ _ =>
      change hasLtPow2BoundFact nid maxExp fs = true at hHas
      exact hasLtPow2BoundFact_sound nid maxExp vals fs
        (fun i fc hi => hAll (i + 1) fc hi) hHas

/-- Check whether a single `GuardCond` is entailed by `ctx`. -/
@[expose] def checkGuardDischarged (g : GuardCond)
    (ctx : List CtxFact) : Bool :=
  match g with
  | .addNoOverflow lid rid => hasAddNoOverflowFact lid rid ctx
  | .subNoUnderflow lid rid => hasSubNoUnderflowFact lid rid ctx
  | .shiftLt64 amtId => hasLtPow2BoundFact amtId 6 ctx
  | .ltPow2 nid exp => hasLtPow2BoundFact nid exp ctx

/-- Check that every runtime assertion in `gs` is entailed by `ctx`. -/
@[expose] def checkGuardsDischarged (gs : List GuardCond)
    (ctx : List CtxFact) : Bool :=
  List.foldr (fun g acc => checkGuardDischarged g ctx && acc) true gs

theorem checkGuardDischarged_ne_false (vals : List (PoisonOr Nat))
    (ctx : List CtxFact) (hAll : AllCtxFactsHold vals ctx) (g : GuardCond)
    (hChk : checkGuardDischarged g ctx = true) :
    evalGuard vals g ≠ some false := by
  cases g with
  | addNoOverflow lid rid =>
    have hFact := hasAddNoOverflowFact_sound lid rid vals ctx hAll hChk
    dsimp only [evalGuard]
    cases hL : listNthOpt vals lid with
    | none => intro h; cases h
    | some pa =>
      dsimp only
      cases pa with
      | poison => intro h; cases h
      | val a =>
        dsimp only
        cases hR : listNthOpt vals rid with
        | none => intro h; cases h
        | some pb =>
          dsimp only
          cases pb with
          | poison => intro h; cases h
          | val b =>
            dsimp only
            have hLt : a + b < u64Mod := hFact a b hL hR
            rw [(nat_blt_iff _ _).2 hLt]
            intro h
            cases h
  | subNoUnderflow lid rid =>
    have hFact := hasSubNoUnderflowFact_sound lid rid vals ctx hAll hChk
    dsimp only [evalGuard]
    cases hL : listNthOpt vals lid with
    | none => intro h; cases h
    | some pa =>
      dsimp only
      cases pa with
      | poison => intro h; cases h
      | val a =>
        dsimp only
        cases hR : listNthOpt vals rid with
        | none => intro h; cases h
        | some pb =>
          dsimp only
          cases pb with
          | poison => intro h; cases h
          | val b =>
            dsimp only
            have hLe : b ≤ a := hFact a b hL hR
            rw [(nat_ble_iff _ _).2 hLe]
            intro h
            cases h
  | shiftLt64 amtId =>
    have hFact := hasLtPow2BoundFact_sound amtId 6 vals ctx hAll hChk
    dsimp only [evalGuard]
    cases hA : listNthOpt vals amtId with
    | none => intro h; cases h
    | some pa =>
      dsimp only
      cases pa with
      | poison => intro h; cases h
      | val a =>
        dsimp only
        have hLt : a < 64 := hFact a hA
        rw [(nat_blt_iff _ _).2 hLt]
        intro h
        cases h
  | ltPow2 nid exp =>
    have hFact := hasLtPow2BoundFact_sound nid exp vals ctx hAll hChk
    dsimp only [evalGuard]
    cases hN : listNthOpt vals nid with
    | none => intro h; cases h
    | some pa =>
      dsimp only
      cases pa with
      | poison => intro h; cases h
      | val a =>
        dsimp only
        have hLt : a < Nat.pow 2 exp := hFact a hN
        rw [(nat_blt_iff _ _).2 hLt]
        intro h
        cases h

/-- When `AllCtxFactsHold vals ctx` holds, no discharged guard list can evaluate
to `some false` (a panic abort). -/
theorem checkGuardsDischarged_ne_false (vals : List (PoisonOr Nat))
    (ctx : List CtxFact) (hAll : AllCtxFactsHold vals ctx) :
    ∀ (gs : List GuardCond),
      checkGuardsDischarged gs ctx = true →
      evalGuards vals gs ≠ some false
  | [] => fun _ h => by cases h
  | g :: gs => fun hChk => by
    have hG := checkGuardDischarged_ne_false vals ctx hAll g
      (bool_and_left hChk)
    have hRest := checkGuardsDischarged_ne_false vals ctx hAll gs
      (bool_and_right hChk)
    dsimp only [evalGuards, List.foldr]
    cases hEv : evalGuard vals g with
    | none => intro h; cases h
    | some b =>
      dsimp only
      cases b with
      | false => exact False.elim (hG hEv)
      | true => exact hRest

end Anneal.Backend

end
