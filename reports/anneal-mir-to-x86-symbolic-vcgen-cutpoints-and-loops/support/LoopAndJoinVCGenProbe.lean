-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted
import Anneal

/-!
# Inductive Loop & $O(D)$ Cut-Point VCgen Probe (`LoopAndJoinVCGenProbe.lean`)

This module extends the syntax-directed weakest-precondition verifier (`wpX86`)
from Round 1 to support unbounded runtime loops and $O(D)$ diamond-join
verification inside `theory/` with zero changes to `trusted/`:

1. **Finite-Support Canonical State Normalization (`canonMemUpTo`,
   `canonState`, and `StateSubsumed`):**
   Normalizes any `X86State` stack frame up to `body.slotCount` into a canonical
   `updateSlot` spine without modifying `Trusted.X86State`. Because
   `evalX86Step` is monotone with respect to initialized stack slots
   (`StateSubsumed`), `StateSubsumed (canonState B s) s` holds unconditionally
   for all `B` and `s`, while erasing temporary slot history so converging CFG
   paths unify by `rfl`.
2. **Cut-Point Weakest Precondition (`wpX86Cut` and `wpX86Cut_sound`):**
   Steps from a state `cs` and discharges obligations either upon termination
   (`SafeAndEnsures P`) or upon arriving at a cut-point basic block
   (`s'.bb = cutBb ∧ s'.ip = 0 ∧ s'.curBody = none`) after at least one step,
   applying `canonState body.slotCount` at the cut-point.
3. **Composable Prefix-Safety Judgment (`AllPrefixesSafeAndEnsures`):**
   Unifies straight-line/tree symbolic execution (`byWpX86`), $O(D)$ cut-point
   and diamond-join composition (`byCutPoint`, `byExactCut`, `byIndexedCut`),
   and strong-induction loop verification (`byLoop`, `byIndexedLoop`) under a
   single composable semantic interface.
-/

namespace Anneal.LoopAndJoinVCGen

open Trusted
open Anneal

/-!
## 1. Entry-State Canonicalization and Elementary `Nat` Induction Helpers
-/

theorem nat_lt_or_ge (i k : Nat) : i < k ∨ k ≤ i := by
  induction i generalizing k with
  | zero =>
    cases k with
    | zero => exact Or.inr (Nat.le_refl 0)
    | succ k' => exact Or.inl (Nat.zero_lt_succ k')
  | succ i' ih =>
    cases k with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ k' =>
      cases ih k' with
      | inl hlt => exact Or.inl (Nat.succ_lt_succ hlt)
      | inr hle => exact Or.inr (Nat.succ_le_succ hle)

theorem nat_lt_or_eq_of_le {m n : Nat} (h : m ≤ n) : m < n ∨ m = n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => exact Or.inr rfl
    | succ n' => exact Or.inl (Nat.zero_lt_succ n')
  | succ m' ih =>
    cases n with
    | zero => cases h
    | succ n' =>
      cases ih (Nat.le_of_succ_le_succ h) with
      | inl hlt => exact Or.inl (Nat.succ_lt_succ hlt)
      | inr heq => exact Or.inr (congrArg Nat.succ heq)

/-- If `i ≤ n` and `¬ (i < n)`, then `i = n`. Used at loop exit branches where
    the loop invariant gives `i ≤ n` and the negated loop guard gives
    `decide (i < n) = false`. -/
theorem eq_of_le_of_not_lt {i n : Nat} (hle : i ≤ n) (hnotlt : ¬ (i < n)) :
    i = n := by
  cases nat_lt_or_eq_of_le hle with
  | inl hlt => exact False.elim (hnotlt hlt)
  | inr heq => exact heq

/-- Bounded strong induction helper proved by structural recursion on `k`. -/
theorem nat_strong_ind_aux (P : Nat → Prop)
    (hstep : ∀ n, (∀ m, m < n → P m) → P n) (k : Nat) :
    ∀ m, m ≤ k → P m := by
  induction k with
  | zero =>
    intro m hm
    cases m with
    | zero =>
      exact hstep 0 (fun _ hlt => by cases hlt)
    | succ _ => cases hm
  | succ k' ih =>
    intro m hm
    cases nat_lt_or_eq_of_le hm with
    | inl hlt => exact ih m (Nat.le_of_lt_succ hlt)
    | inr heq =>
      subst heq
      exact hstep (k' + 1) (fun m' hlt' => ih m' (Nat.le_of_lt_succ hlt'))

/-- Strong induction on `Nat`, derived solely from `prelude` structural
    recursion. -/
theorem nat_strong_ind (P : Nat → Prop)
    (hstep : ∀ n, (∀ m, m < n → P m) → P n) (n : Nat) : P n :=
  nat_strong_ind_aux P hstep n n (Nat.le_refl n)

theorem if_decide_false {α : Type} {c : Prop} [inst : Decidable c] {t e : α}
    (h : decide c = false) : (if c then t else e) = e := by
  cases inst with
  | isFalse _ => rfl
  | isTrue _ => cases h

theorem if_decide_true {α : Type} {c : Prop} [inst : Decidable c] {t e : α}
    (h : decide c = true) : (if c then t else e) = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse _ => cases h

theorem updateSlot_lt_succ {mem acc : Nat → Option X86Val} {k : Nat}
    {v : X86Val}
    (h_lt : ∀ i, i < k → mem i = acc i)
    (hk : mem k = some v) :
    ∀ i, i < k + 1 → mem i = updateSlot acc k (some v) i := by
  intro i hi
  dsimp [updateSlot]
  cases heq : i == k with
  | true =>
    have hik : i = k := eq_of_beq heq
    subst hik
    exact hk
  | false =>
    have hne : i ≠ k := ne_of_beq_false heq
    have hle : i ≤ k := Nat.le_of_lt_succ hi
    have hlt : i < k := Nat.lt_of_le_of_ne hle hne
    exact h_lt i hlt

theorem updateSlot_ge_succ {acc : Nat → Option X86Val} {k : Nat} {v : X86Val}
    (h_ge : ∀ i, k ≤ i → acc i = none) :
    ∀ i, k + 1 ≤ i → updateSlot acc k (some v) i = none := by
  intro i hi
  dsimp [updateSlot]
  cases heq : i == k with
  | true =>
    have hik : i = k := eq_of_beq heq
    subst hik
    exact False.elim (Nat.not_lt_of_ge hi (Nat.lt_succ_self i))
  | false =>
    exact h_ge i (Nat.le_trans (Nat.le_succ k) hi)

/-- Quantifier telescope over typed entry arguments starting at stack slot
    `k`. -/
noncomputable def forallTypedArgsAux (tySizes : Nat → Nat) (k : Nat)
    (argTys : List X86Ty) (acc : Nat → Option X86Val)
    (P : (Nat → Option X86Val) → Prop) : Prop :=
  match argTys with
  | [] => P acc
  | .usize :: tys =>
    ∀ (a : Nat),
      forallTypedArgsAux tySizes (k + 1) tys
        (updateSlot acc k (some (.word64 a))) P
  | .bool :: tys =>
    ∀ (b : Bool),
      forallTypedArgsAux tySizes (k + 1) tys
        (updateSlot acc k (some (.boolVal b))) P
  | .unit :: tys =>
      forallTypedArgsAux tySizes (k + 1) tys
        (updateSlot acc k (some .unit)) P
  | .adt id :: tys =>
    ∀ (a : Nat),
      forallTypedArgsAux tySizes (k + 1) tys
        (updateSlot acc k (some (.adt id (.word64 a)))) P
  | .param idx :: tys =>
    ∀ (bits : Nat),
      forallTypedArgsAux tySizes (k + 1) tys
        (updateSlot acc k (some (.bytes (tySizes idx) bits))) P
  | .refParam _ :: tys =>
    ∀ (slot : SlotId),
      forallTypedArgsAux tySizes (k + 1) tys
        (updateSlot acc k (some (.stackPtr slot))) P

/-- Top-level entry-argument quantifier telescope starting at slot `1`. -/
noncomputable def forallTypedArgs (tySizes : Nat → Nat) (argTys : List X86Ty)
    (P : (Nat → Option X86Val) → Prop) : Prop :=
  forallTypedArgsAux tySizes 1 argTys (fun _ => none) P

theorem forallTypedArgsAux_sound (tySizes : Nat → Nat) (argTys : List X86Ty)
    (mem : Nat → Option X86Val) (P : (Nat → Option X86Val) → Prop) :
    ∀ (k : Nat) (acc : Nat → Option X86Val),
      (∀ i, i < k → mem i = acc i) →
      (∀ i, k ≤ i → acc i = none) →
      argTys.foldr
        (fun ty rest idx =>
          (∃ v, mem idx = some v ∧ v.hasTy tySizes ty) ∧ rest (idx + 1))
        (fun idx => ∀ j, idx ≤ j → mem j = none)
        k →
      forallTypedArgsAux tySizes k argTys acc P →
      P mem := by
  induction argTys with
  | nil =>
    intro k acc h_lt h_ge h_rest hforall
    have hmem_eq : mem = acc := by
      funext i
      cases nat_lt_or_ge i k with
      | inl hlt => exact h_lt i hlt
      | inr hge => rw [h_rest i hge, h_ge i hge]
    rw [hmem_eq]
    exact hforall
  | cons ty tys ih =>
    intro k acc h_lt h_ge hfold hforall
    cases hfold with
    | intro hex hrest =>
      cases hex with
      | intro v hv =>
        have hk : mem k = some v := hv.1
        have hty : v.hasTy tySizes ty := hv.2
        cases ty with
        | usize =>
          cases v with
          | word64 a =>
            exact ih (k + 1) (updateSlot acc k (some (.word64 a)))
              (updateSlot_lt_succ h_lt hk) (updateSlot_ge_succ h_ge)
              hrest (hforall a)
          | boolVal _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hty
        | bool =>
          cases v with
          | boolVal b =>
            exact ih (k + 1) (updateSlot acc k (some (.boolVal b)))
              (updateSlot_lt_succ h_lt hk) (updateSlot_ge_succ h_ge)
              hrest (hforall b)
          | word64 _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hty
        | unit =>
          cases v with
          | unit =>
            exact ih (k + 1) (updateSlot acc k (some .unit))
              (updateSlot_lt_succ h_lt hk) (updateSlot_ge_succ h_ge)
              hrest hforall
          | word64 _ | boolVal _ | adt _ _ | bytes _ _ | stackPtr _ => cases hty
        | adt id =>
          cases v with
          | adt vId inner =>
            cases inner with
            | word64 a =>
              have hid : vId = id := hty
              subst hid
              exact ih (k + 1) (updateSlot acc k (some (.adt vId (.word64 a))))
                (updateSlot_lt_succ h_lt hk) (updateSlot_ge_succ h_ge)
                hrest (hforall a)
            | boolVal _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hty
          | word64 _ | boolVal _ | unit | bytes _ _ | stackPtr _ => cases hty
        | param idx =>
          cases v with
          | bytes sz bits =>
            have hsz : sz = tySizes idx := hty
            subst hsz
            exact ih (k + 1) (updateSlot acc k (some (.bytes (tySizes idx) bits)))
              (updateSlot_lt_succ h_lt hk) (updateSlot_ge_succ h_ge)
              hrest (hforall bits)
          | word64 _ | boolVal _ | unit | adt _ _ | stackPtr _ => cases hty
        | refParam idx =>
          cases v with
          | stackPtr slot =>
            exact ih (k + 1) (updateSlot acc k (some (.stackPtr slot)))
              (updateSlot_lt_succ h_lt hk) (updateSlot_ge_succ h_ge)
              hrest (hforall slot)
          | word64 _ | boolVal _ | unit | adt _ _ | bytes _ _ => cases hty

/-- Universal entry-state canonicalization theorem. -/
theorem initX86State_canonical (body : X86Body) (s : X86State)
    (P : X86State → Prop)
    (hinit : initX86State body s)
    (hcanonical : forallTypedArgs s.tySizes body.argTys (fun mem =>
      P { mem := mem, bb := 0, ip := 0, tySizes := s.tySizes })) :
    P s := by
  cases s with
  | mk mem0 bb0 ip0 tySizes0 curBody0 stack0 =>
    have hb : bb0 = 0 := hinit.1
    have hip : ip0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hm0 : mem0 0 = none := hinit.2.2.2.2.1
    have hargs : argsMatchStack tySizes0 body.argTys mem0 := hinit.2.2.2.2.2
    subst hb hip hc hst
    have h_lt1 : ∀ i, i < 1 → mem0 i = (fun _ => none) i := by
      intro i hi
      cases i with
      | zero => exact hm0
      | succ i' =>
        exact False.elim (Nat.not_lt_zero i' (Nat.lt_of_succ_lt_succ hi))
    exact forallTypedArgsAux_sound tySizes0 body.argTys mem0
      (fun mem => P { mem := mem, bb := 0, ip := 0, tySizes := tySizes0 })
      1 (fun _ => none) h_lt1 (fun _ _ => rfl) hargs hcanonical

/-- Quantifier-free unfolding of `argsSatisfyLibInv` over canonical memory. -/
noncomputable def allArgsLibInv (libInv : LibInv) (tySizes : Nat → Nat) (k : Nat)
    (argTys : List X86Ty) (mem : Nat → Option X86Val) : Prop :=
  match argTys with
  | [] => True
  | ty :: tys =>
    (match mem k with
     | some v => libInv tySizes ty v
     | none => False) ∧
    allArgsLibInv libInv tySizes (k + 1) tys mem

theorem argsSatisfyLibInv_imp_allArgsLibInv (libInv : LibInv)
    (tySizes : Nat → Nat) (argTys : List X86Ty) (mem : Nat → Option X86Val) :
    ∀ (k : Nat),
      argTys.foldr
        (fun ty rest idx =>
          (∃ v, mem idx = some v ∧ libInv tySizes ty v) ∧ rest (idx + 1))
        (fun _ => True)
        k →
      allArgsLibInv libInv tySizes k argTys mem := by
  induction argTys with
  | nil =>
    intro _ _
    exact True.intro
  | cons ty tys ih =>
    intro k hfold
    cases hfold with
    | intro hex hrest =>
      cases hex with
      | intro v hv =>
        refine ⟨?_, ih (k + 1) hrest⟩
        rw [hv.1]
        exact hv.2

/-!
## 2. Finite-Support Canonical Memory Spine & Simulation (`StateSubsumed`)
-/

/-- Memory `cm` is subsumed by `m` when every initialized slot `some v` in `cm`
    is also initialized to `some v` in `m`. -/
def MemSubsumed (cm m : Nat → Option X86Val) : Prop :=
  ∀ i v, cm i = some v → m i = some v

theorem MemSubsumed.refl (m : Nat → Option X86Val) : MemSubsumed m m :=
  fun _ _ h => h

theorem MemSubsumed.trans {m1 m2 m3 : Nat → Option X86Val}
    (h12 : MemSubsumed m1 m2) (h23 : MemSubsumed m2 m3) :
    MemSubsumed m1 m3 :=
  fun i v h => h23 i v (h12 i v h)

theorem memSubsumed_update_some {cm m : Nat → Option X86Val}
    (hsub : MemSubsumed cm m) (dst : Nat) (val : X86Val) :
    MemSubsumed (updateSlot cm dst (some val))
      (updateSlot m dst (some val)) := by
  intro i v hget
  dsimp [updateSlot] at hget ⊢
  cases h : i == dst with
  | true =>
    rw [h] at hget
    exact hget
  | false =>
    rw [h] at hget
    exact hsub i v hget

theorem memSubsumed_update_none {cm m : Nat → Option X86Val}
    (hsub : MemSubsumed cm m) (dst : Nat) :
    MemSubsumed (updateSlot cm dst none) (updateSlot m dst none) := by
  intro i v hget
  dsimp [updateSlot] at hget ⊢
  cases h : i == dst with
  | true =>
    rw [h] at hget
    cases hget
  | false =>
    rw [h] at hget
    exact hsub i v hget

/-- Rebuild a canonical `updateSlot` spine of depth `B` by sampling `m k` at
    each concrete slot index `k ∈ {0, ..., B - 1}`. -/
noncomputable def canonMemUpTo :
    Nat → (Nat → Option X86Val) → (Nat → Option X86Val)
  | 0, _ => fun _ => none
  | k + 1, m => updateSlot (canonMemUpTo k m) k (m k)

/-- Every initialized slot in `canonMemUpTo B m` is initialized to the exact
    same value in `m`, unconditionally for all `B` and `m`. -/
theorem memSubsumed_canonMemUpTo (B : Nat) (m : Nat → Option X86Val) :
    MemSubsumed (canonMemUpTo B m) m := by
  induction B with
  | zero =>
    intro i v h
    cases h
  | succ k ih =>
    intro i v h
    dsimp [canonMemUpTo, updateSlot] at h
    cases heq : i == k with
    | true =>
      rw [heq] at h
      have hik : i = k := eq_of_beq heq
      subst hik
      exact h
    | false =>
      rw [heq] at h
      exact ih i v h

/-- Frame-by-frame subsumption on saved caller stack frames. -/
inductive StackSubsumed : List X86CallFrame → List X86CallFrame → Prop where
  | nil : StackSubsumed [] []
  | cons {cf f : X86CallFrame} {cfs fs : List X86CallFrame} :
      cf.callerBody = f.callerBody →
      MemSubsumed cf.callerMem f.callerMem →
      cf.retSlot = f.retSlot →
      cf.retBlock = f.retBlock →
      StackSubsumed cfs fs →
      StackSubsumed (cf :: cfs) (f :: fs)

theorem StackSubsumed.refl (stk : List X86CallFrame) :
    StackSubsumed stk stk := by
  induction stk with
  | nil => exact .nil
  | cons f fs ih =>
    exact .cons rfl (MemSubsumed.refl f.callerMem) rfl rfl ih

theorem StackSubsumed.trans {s1 s2 s3 : List X86CallFrame}
    (h12 : StackSubsumed s1 s2) (h23 : StackSubsumed s2 s3) :
    StackSubsumed s1 s3 := by
  induction h12 generalizing s3 with
  | nil =>
    cases h23
    exact .nil
  | cons hb1 hm1 hsl1 hret1 _ ih =>
    cases h23 with
    | cons hb2 hm2 hsl2 hret2 hrest2 =>
      exact .cons (Eq.trans hb1 hb2) (MemSubsumed.trans hm1 hm2)
        (Eq.trans hsl1 hsl2) (Eq.trans hret1 hret2) (ih hrest2)

/-- Forward simulation relation between a canonical/symbolic `X86State` `cs` and
    a concrete execution state `s`. -/
structure StateSubsumed (cs s : X86State) : Prop where
  mem_sub : MemSubsumed cs.mem s.mem
  bb_eq : cs.bb = s.bb
  ip_eq : cs.ip = s.ip
  tySizes_eq : cs.tySizes = s.tySizes
  curBody_eq : cs.curBody = s.curBody
  stack_sub : StackSubsumed cs.stack s.stack

theorem StateSubsumed.refl (s : X86State) : StateSubsumed s s :=
  ⟨MemSubsumed.refl s.mem, rfl, rfl, rfl, rfl, StackSubsumed.refl s.stack⟩

theorem StateSubsumed.trans {s1 s2 s3 : X86State}
    (h12 : StateSubsumed s1 s2) (h23 : StateSubsumed s2 s3) :
    StateSubsumed s1 s3 :=
  ⟨MemSubsumed.trans h12.mem_sub h23.mem_sub,
   Eq.trans h12.bb_eq h23.bb_eq,
   Eq.trans h12.ip_eq h23.ip_eq,
   Eq.trans h12.tySizes_eq h23.tySizes_eq,
   Eq.trans h12.curBody_eq h23.curBody_eq,
   StackSubsumed.trans h12.stack_sub h23.stack_sub⟩

/-- Normalize `s.mem` up to slot bound `B` into a canonical `updateSlot`
    spine. -/
noncomputable def canonState (B : Nat) (s : X86State) : X86State :=
  { s with mem := canonMemUpTo B s.mem }

/-- `canonState B s` unconditionally subsumes `s` for every bound `B` and state
    `s`. -/
theorem canonState_subsumed (B : Nat) (s : X86State) :
    StateSubsumed (canonState B s) s :=
  ⟨memSubsumed_canonMemUpTo B s.mem, rfl, rfl, rfl, rfl,
   StackSubsumed.refl s.stack⟩

theorem evalX86Operand_subsumed {cm m : Nat → Option X86Val}
    (hsub : MemSubsumed cm m) (op : X86Operand) (v : X86Val)
    (cm' : Nat → Option X86Val)
    (heval : evalX86Operand cm op = some (v, cm')) :
    ∃ m', evalX86Operand m op = some (v, m') ∧ MemSubsumed cm' m' := by
  cases op with
  | stackSlot slot consume =>
    cases consume with
    | false =>
      dsimp [evalX86Operand] at heval
      cases hget : cm slot.index with
      | none => rw [hget] at heval; cases heval
      | some val =>
        rw [hget] at heval
        injection heval with hp
        injection hp with hv hcm'
        subst hv hcm'
        have hm := hsub slot.index val hget
        refine ⟨m, ?_, hsub⟩
        dsimp [evalX86Operand]
        rw [hm]
    | true =>
      dsimp [evalX86Operand] at heval
      cases hget : cm slot.index with
      | none => rw [hget] at heval; cases heval
      | some val =>
        rw [hget] at heval
        injection heval with hp
        injection hp with hv hcm'
        subst hv hcm'
        have hm := hsub slot.index val hget
        refine ⟨updateSlot m slot.index none, ?_,
          memSubsumed_update_none hsub slot.index⟩
        dsimp [evalX86Operand]
        rw [hm]
  | imm val =>
    injection heval with hp
    injection hp with hv hcm'
    subst hv hcm'
    exact ⟨m, rfl, hsub⟩

theorem evalX86Instr_subsumed {cs s : X86State}
    (hsub : StateSubsumed cs s) (instr : X86Instr) :
    (∀ cs', evalX86Instr cs instr = .step () cs' →
      ∃ s', evalX86Instr s instr = .step () s' ∧ StateSubsumed cs' s') ∧
    (∀ term, evalX86Instr cs instr = .terminated term →
      evalX86Instr s instr = .terminated term) := by
  constructor
  · intro cs' hstep
    cases instr with
    | mov dst src =>
      dsimp [evalX86Instr] at hstep
      cases h1 : evalX86Operand cs.mem src with
      | none => rw [h1] at hstep; cases hstep
      | some p =>
        rw [h1] at hstep
        cases p with
        | mk v cm' =>
          dsimp at hstep
          injection hstep with _ hcs'
          subst hcs'
          cases evalX86Operand_subsumed hsub.mem_sub src v cm' h1 with
          | intro m' hm' =>
            refine ⟨{ s with mem := updateSlot m' dst.index (some v),
                             ip := s.ip + 1 }, ?_, ?_⟩
            · dsimp [evalX86Instr]; rw [hm'.1]
            · exact ⟨memSubsumed_update_some hm'.2 dst.index v,
                hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
                hsub.curBody_eq, hsub.stack_sub⟩
    | alu op dst lhs rhs =>
      dsimp [evalX86Instr] at hstep
      cases h1 : evalX86Operand cs.mem lhs with
      | none => rw [h1] at hstep; cases hstep
      | some p1 =>
        rw [h1] at hstep
        cases p1 with
        | mk v1 cm1 =>
          dsimp at hstep
          cases h2 : evalX86Operand cm1 rhs with
          | none => rw [h2] at hstep; cases hstep
          | some p2 =>
            rw [h2] at hstep
            cases p2 with
            | mk v2 cm2 =>
              dsimp at hstep
              cases h3 : evalX86BinOp op v1 v2 with
              | none => rw [h3] at hstep; cases hstep
              | some outVal =>
                rw [h3] at hstep
                injection hstep with _ hcs'
                subst hcs'
                cases evalX86Operand_subsumed hsub.mem_sub lhs v1 cm1 h1 with
                | intro m1 hm1 =>
                  cases evalX86Operand_subsumed hm1.2 rhs v2 cm2 h2 with
                  | intro m2 hm2 =>
                    refine ⟨{ s with mem := updateSlot m2 dst.index (some outVal),
                                     ip := s.ip + 1 }, ?_, ?_⟩
                    · dsimp [evalX86Instr]
                      rw [hm1.1]; dsimp; rw [hm2.1]; dsimp; rw [h3]
                    · exact ⟨memSubsumed_update_some hm2.2 dst.index outVal,
                        hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
                        hsub.curBody_eq, hsub.stack_sub⟩
    | wrapAdt adtId dst src =>
      dsimp [evalX86Instr] at hstep
      cases h1 : evalX86Operand cs.mem src with
      | none => rw [h1] at hstep; cases hstep
      | some p =>
        rw [h1] at hstep
        cases p with
        | mk v cm' =>
          dsimp at hstep
          injection hstep with _ hcs'
          subst hcs'
          cases evalX86Operand_subsumed hsub.mem_sub src v cm' h1 with
          | intro m' hm' =>
            refine ⟨{ s with mem := updateSlot m' dst.index (some (.adt adtId v)),
                             ip := s.ip + 1 }, ?_, ?_⟩
            · dsimp [evalX86Instr]; rw [hm'.1]
            · exact ⟨memSubsumed_update_some hm'.2 dst.index (.adt adtId v),
                hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
                hsub.curBody_eq, hsub.stack_sub⟩
    | extractField0 dst src =>
      dsimp [evalX86Instr] at hstep
      cases h1 : cs.mem src.index with
      | none => rw [h1] at hstep; cases hstep
      | some v =>
        rw [h1] at hstep
        cases v with
        | adt adtId inner =>
          injection hstep with _ hcs'
          subst hcs'
          have hm1 := hsub.mem_sub src.index (.adt adtId inner) h1
          refine ⟨{ s with mem := updateSlot s.mem dst.index (some inner),
                           ip := s.ip + 1 }, ?_, ?_⟩
          · dsimp [evalX86Instr]; rw [hm1]
          · exact ⟨memSubsumed_update_some hsub.mem_sub dst.index inner,
              hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
              hsub.curBody_eq, hsub.stack_sub⟩
        | word64 _ | boolVal _ | unit | bytes _ _ | stackPtr _ => cases hstep
    | leaSlot dst target =>
      dsimp [evalX86Instr] at hstep
      cases h1 : cs.mem target.index with
      | none => rw [h1] at hstep; cases hstep
      | some v =>
        rw [h1] at hstep
        injection hstep with _ hcs'
        subst hcs'
        have hm1 := hsub.mem_sub target.index v h1
        refine ⟨{ s with mem := updateSlot s.mem dst.index (some (.stackPtr target)),
                         ip := s.ip + 1 }, ?_, ?_⟩
        · dsimp [evalX86Instr]; rw [hm1]
        · exact ⟨memSubsumed_update_some hsub.mem_sub dst.index (.stackPtr target),
            hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
            hsub.curBody_eq, hsub.stack_sub⟩
    | reborrowSlot dst srcPtr =>
      dsimp [evalX86Instr] at hstep
      cases h1 : cs.mem srcPtr.index with
      | none => rw [h1] at hstep; cases hstep
      | some pv =>
        rw [h1] at hstep
        cases pv with
        | stackPtr target =>
          dsimp at hstep
          cases h2 : cs.mem target.index with
          | none => rw [h2] at hstep; cases hstep
          | some tv =>
            rw [h2] at hstep
            injection hstep with _ hcs'
            subst hcs'
            have hm1 := hsub.mem_sub srcPtr.index (.stackPtr target) h1
            have hm2 := hsub.mem_sub target.index tv h2
            refine ⟨{ s with mem := updateSlot s.mem dst.index (some (.stackPtr target)),
                             ip := s.ip + 1 }, ?_, ?_⟩
            · dsimp [evalX86Instr]; rw [hm1]; dsimp; rw [hm2]
            · exact ⟨memSubsumed_update_some hsub.mem_sub dst.index (.stackPtr target),
                hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
                hsub.curBody_eq, hsub.stack_sub⟩
        | word64 _ | boolVal _ | unit | adt _ _ | bytes _ _ => cases hstep
    | allocSlot slot =>
      dsimp [evalX86Instr] at hstep
      injection hstep with _ hcs'
      subst hcs'
      exact ⟨_, rfl, ⟨memSubsumed_update_none hsub.mem_sub slot.index,
        hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
        hsub.curBody_eq, hsub.stack_sub⟩⟩
    | deallocSlot slot =>
      dsimp [evalX86Instr] at hstep
      injection hstep with _ hcs'
      subst hcs'
      exact ⟨_, rfl, ⟨memSubsumed_update_none hsub.mem_sub slot.index,
        hsub.bb_eq, by dsimp; rw [hsub.ip_eq], hsub.tySizes_eq,
        hsub.curBody_eq, hsub.stack_sub⟩⟩
    | nop =>
      dsimp [evalX86Instr] at hstep
      injection hstep with _ hcs'
      subst hcs'
      exact ⟨_, rfl, ⟨hsub.mem_sub, hsub.bb_eq, by dsimp; rw [hsub.ip_eq],
        hsub.tySizes_eq, hsub.curBody_eq, hsub.stack_sub⟩⟩
  · intro term hterm
    cases instr with
    | mov dst src =>
      dsimp [evalX86Instr] at hterm
      cases h1 : evalX86Operand cs.mem src <;> rw [h1] at hterm <;> cases hterm
    | alu op dst lhs rhs =>
      dsimp [evalX86Instr] at hterm
      cases h1 : evalX86Operand cs.mem lhs with
      | none => rw [h1] at hterm; cases hterm
      | some p1 =>
        rw [h1] at hterm
        cases p1 with
        | mk v1 cm1 =>
          dsimp at hterm
          cases h2 : evalX86Operand cm1 rhs with
          | none => rw [h2] at hterm; cases hterm
          | some p2 =>
            rw [h2] at hterm
            cases p2 with
            | mk v2 cm2 =>
              dsimp at hterm
              cases h3 : evalX86BinOp op v1 v2 <;>
                rw [h3] at hterm <;> cases hterm
    | wrapAdt adtId dst src =>
      dsimp [evalX86Instr] at hterm
      cases h1 : evalX86Operand cs.mem src <;> rw [h1] at hterm <;> cases hterm
    | extractField0 dst src =>
      dsimp [evalX86Instr] at hterm
      cases h1 : cs.mem src.index with
      | none => rw [h1] at hterm; cases hterm
      | some v =>
        rw [h1] at hterm
        cases v <;> cases hterm
    | leaSlot dst target =>
      dsimp [evalX86Instr] at hterm
      cases h1 : cs.mem target.index <;> rw [h1] at hterm <;> cases hterm
    | reborrowSlot dst srcPtr =>
      dsimp [evalX86Instr] at hterm
      cases h1 : cs.mem srcPtr.index with
      | none => rw [h1] at hterm; cases hterm
      | some pv =>
        rw [h1] at hterm
        cases pv with
        | stackPtr target =>
          dsimp at hterm
          cases h2 : cs.mem target.index <;> rw [h2] at hterm <;> cases hterm
        | word64 _ | boolVal _ | unit | adt _ _ | bytes _ _ => cases hterm
    | allocSlot _ | deallocSlot _ | nop => cases hterm

theorem evalRepMovsb_subsumed {tySizes : Nat → Nat} {cm m : Nat → Option X86Val}
    (hsub : MemSubsumed cm m) (srcTy dstTy : X86Ty) (ptrVal outVal : X86Val)
    (heval : evalRepMovsb tySizes cm srcTy dstTy ptrVal = some outVal) :
    evalRepMovsb tySizes m srcTy dstTy ptrVal = some outVal := by
  dsimp [evalRepMovsb] at heval ⊢
  cases hsz : decide (evalX86TyByteSize tySizes srcTy =
      evalX86TyByteSize tySizes dstTy) with
  | false => rw [hsz] at heval; cases heval
  | true =>
    rw [hsz] at heval
    dsimp at heval ⊢
    cases ptrVal with
    | stackPtr target =>
      dsimp at heval ⊢
      cases hget : cm target.index with
      | none => rw [hget] at heval; cases heval
      | some v =>
        rw [hget] at heval
        have hm := hsub target.index v hget
        rw [hm]
        exact heval
    | word64 _ | boolVal _ | unit | adt _ _ | bytes _ _ => cases heval

theorem evalX86Term_subsumed {cs s : X86State}
    (hsub : StateSubsumed cs s) (term : X86Term) :
    (∀ cs', evalX86Term cs term = .step () cs' →
      ∃ s', evalX86Term s term = .step () s' ∧ StateSubsumed cs' s') ∧
    (∀ tk, evalX86Term cs term = .terminated tk →
      evalX86Term s term = .terminated tk) := by
  cases cs with
  | mk cmem cbb cip cty ccur cstack =>
  cases s with
  | mk smem sbb sip sty scur sstack =>
  cases hsub with
  | mk hmem_sub hbb_eq hip_eq hty_eq hcur_eq hstack_sub =>
  dsimp at hmem_sub hbb_eq hip_eq hty_eq hcur_eq hstack_sub
  subst hbb_eq hip_eq hty_eq hcur_eq
  constructor
  · intro cs' hstep
    cases term with
    | ret =>
      dsimp [evalX86Term] at hstep
      cases h0 : cmem 0 with
      | none => rw [h0] at hstep; cases hstep
      | some retVal =>
        rw [h0] at hstep
        have hm0 := hmem_sub 0 retVal h0
        cases hstack_sub with
        | nil => cases hstep
        | @cons cf f cfs fs hbody hmem hslot hblk hrest =>
          dsimp at hstep
          injection hstep with _ hcs'
          subst hcs'
          refine ⟨{ mem := updateSlot f.callerMem f.retSlot.index (some retVal),
                    bb := f.retBlock, ip := 0, tySizes := cty,
                    curBody := f.callerBody, stack := fs }, ?_, ?_⟩
          · dsimp [evalX86Term]; rw [hm0]
          · refine ⟨?_, hblk, rfl, rfl, hbody, hrest⟩
            dsimp
            rw [hslot]
            exact memSubsumed_update_some hmem f.retSlot.index retVal
    | jmp target =>
      dsimp [evalX86Term] at hstep
      injection hstep with _ hcs'
      subst hcs'
      exact ⟨_, rfl, ⟨hmem_sub, rfl, rfl, rfl, rfl, hstack_sub⟩⟩
    | ud2 | abortPanic => cases hstep
    | jccBool cond falseTarget trueTarget =>
      dsimp [evalX86Term] at hstep
      cases h1 : evalX86Operand cmem cond with
      | none => rw [h1] at hstep; cases hstep
      | some p =>
        rw [h1] at hstep
        cases p with
        | mk cv cm' =>
          cases cv with
          | boolVal b =>
            cases b with
            | false =>
              dsimp at hstep
              injection hstep with _ hcs'
              subst hcs'
              cases evalX86Operand_subsumed hmem_sub cond (.boolVal false) cm' h1 with
              | intro m' hm' =>
                refine ⟨{ mem := m', bb := falseTarget.index, ip := 0,
                          tySizes := cty, curBody := ccur, stack := sstack },
                        ?_, ?_⟩
                · dsimp [evalX86Term]; rw [hm'.1]
                · exact ⟨hm'.2, rfl, rfl, rfl, rfl, hstack_sub⟩
            | true =>
              dsimp at hstep
              injection hstep with _ hcs'
              subst hcs'
              cases evalX86Operand_subsumed hmem_sub cond (.boolVal true) cm' h1 with
              | intro m' hm' =>
                refine ⟨{ mem := m', bb := trueTarget.index, ip := 0,
                          tySizes := cty, curBody := ccur, stack := sstack },
                        ?_, ?_⟩
                · dsimp [evalX86Term]; rw [hm'.1]
                · exact ⟨hm'.2, rfl, rfl, rfl, rfl, hstack_sub⟩
          | word64 _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hstep
    | movSizeOfJmp dst ty target =>
      dsimp [evalX86Term] at hstep
      injection hstep with _ hcs'
      subst hcs'
      exact ⟨_, rfl, ⟨memSubsumed_update_some hmem_sub dst.index
          (.word64 (evalX86TyByteSize cty ty)),
        rfl, rfl, rfl, rfl, hstack_sub⟩⟩
    | repMovsbJmp dst srcTy dstTy ptrOp target =>
      dsimp [evalX86Term] at hstep
      cases h1 : evalX86Operand cmem ptrOp with
      | none => rw [h1] at hstep; cases hstep
      | some p =>
        rw [h1] at hstep
        cases p with
        | mk ptrVal cm' =>
          dsimp at hstep
          cases h2 : evalRepMovsb cty cm' srcTy dstTy ptrVal with
          | none => rw [h2] at hstep; cases hstep
          | some outVal =>
            rw [h2] at hstep
            injection hstep with _ hcs'
            subst hcs'
            cases evalX86Operand_subsumed hmem_sub ptrOp ptrVal cm' h1 with
            | intro m' hm' =>
              have h2' := evalRepMovsb_subsumed hm'.2 srcTy dstTy ptrVal outVal h2
              refine ⟨{ mem := updateSlot m' dst.index (some outVal),
                        bb := target.index, ip := 0, tySizes := cty,
                        curBody := ccur, stack := sstack }, ?_, ?_⟩
              · dsimp [evalX86Term]; rw [hm'.1]; dsimp; rw [h2']
              · exact ⟨memSubsumed_update_some hm'.2 dst.index outVal,
                  rfl, rfl, rfl, rfl, hstack_sub⟩
    | call1 dst callee arg target =>
      dsimp [evalX86Term] at hstep
      cases h1 : evalX86Operand cmem arg with
      | none => rw [h1] at hstep; cases hstep
      | some p =>
        rw [h1] at hstep
        cases p with
        | mk argVal cm' =>
          dsimp at hstep
          injection hstep with _ hcs'
          subst hcs'
          cases evalX86Operand_subsumed hmem_sub arg argVal cm' h1 with
          | intro m' hm' =>
            refine ⟨{ mem := updateSlot (fun _ => none) 1 (some argVal),
                      bb := 0, ip := 0, tySizes := cty,
                      curBody := some callee,
                      stack := { callerBody := ccur, callerMem := m',
                                 retSlot := dst, retBlock := target.index } ::
                               sstack }, ?_, ?_⟩
            · dsimp [evalX86Term]; rw [hm'.1]
            · exact ⟨MemSubsumed.refl _, rfl, rfl, rfl, rfl,
                StackSubsumed.cons rfl hm'.2 rfl rfl hstack_sub⟩
  · intro tk hterm
    cases term with
    | ret =>
      dsimp [evalX86Term] at hterm
      cases h0 : cmem 0 with
      | none => rw [h0] at hterm; cases hterm
      | some retVal =>
        rw [h0] at hterm
        have hm0 := hmem_sub 0 retVal h0
        cases hstack_sub with
        | nil =>
          dsimp at hterm
          injection hterm with htk
          subst htk
          dsimp [evalX86Term]
          rw [hm0]
        | cons _ _ _ _ _ => cases hterm
    | jmp _ | ud2 | movSizeOfJmp _ _ _ => cases hterm
    | abortPanic =>
      dsimp [evalX86Term] at hterm
      injection hterm with htk
      subst htk
      rfl
    | jccBool cond _ _ =>
      dsimp [evalX86Term] at hterm
      cases h1 : evalX86Operand cmem cond with
      | none => rw [h1] at hterm; cases hterm
      | some p =>
        rw [h1] at hterm
        cases p with
        | mk cv cm' =>
          cases cv with
          | boolVal b => cases b <;> cases hterm
          | word64 _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hterm
    | repMovsbJmp _ srcTy dstTy ptrOp _ =>
      dsimp [evalX86Term] at hterm
      cases h1 : evalX86Operand cmem ptrOp with
      | none => rw [h1] at hterm; cases hterm
      | some p =>
        rw [h1] at hterm
        cases p with
        | mk pv cm' =>
          dsimp at hterm
          cases h2 : evalRepMovsb cty cm' srcTy dstTy pv <;>
            rw [h2] at hterm <;> cases hterm
    | call1 _ _ arg _ =>
      dsimp [evalX86Term] at hterm
      cases h1 : evalX86Operand cmem arg <;> rw [h1] at hterm <;> cases hterm

/-- Universal forward simulation of `evalX86Step` under `StateSubsumed`. -/
theorem evalX86Step_subsumed (rootBody : X86Body) {cs s : X86State}
    (hsub : StateSubsumed cs s) :
    (∀ cs', evalX86Step rootBody cs = .step () cs' →
      ∃ s', evalX86Step rootBody s = .step () s' ∧ StateSubsumed cs' s') ∧
    (∀ tk, evalX86Step rootBody cs = .terminated tk →
      evalX86Step rootBody s = .terminated tk) := by
  dsimp [evalX86Step]
  rw [← hsub.curBody_eq, ← hsub.bb_eq, ← hsub.ip_eq]
  cases (cs.curBody.getD rootBody).blocks[cs.bb]? with
  | none =>
    refine ⟨?_, ?_⟩ <;> intro _ h <;> cases h
  | some blk =>
    dsimp
    cases blk.instrs[cs.ip]? with
    | some instr => exact evalX86Instr_subsumed hsub instr
    | none => exact evalX86Term_subsumed hsub blk.term

/-- Step-inversion lemma for `ReachesPrefix` that preserves the strict
    step-budget decrease `n' < n` (`n = n' + 1`). -/
theorem reachesPrefix_of_step_lt
    {body : X86Body} {init s s' : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome X86Val}
    (hstep : evalX86Step body s = .step () s')
    (hreach : ReachesPrefix X86Machine body init n s tr out) :
    out = .running ∨
      ∃ n' tr', n' < n ∧ ReachesPrefix X86Machine body init n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step n' _ s₂ _ tr' _ h1 hr =>
    have h1' : StepResult.step () s₂ = evalX86Step body s := h1
    rw [hstep] at h1'
    injection h1' with _ hs
    subst hs
    exact Or.inr ⟨n', tr', Nat.lt_succ_self n', hr⟩
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ _ h1 =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_safeAndEnsures_of_step_lt
    {body : X86Body} {init s s' : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome X86Val} {P : X86Val → Prop}
    (hstep : evalX86Step body s = .step () s')
    (hreach : ReachesPrefix X86Machine body init n s tr out)
    (hnext : ∀ n' tr', n' < n →
      ReachesPrefix X86Machine body init n' s' tr' out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_step_lt hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hp => exact hnext n' tr' hp.1 hp.2

theorem reachesPrefix_safeAndEnsures_of_unwind
    {body : X86Body} {init s : X86State} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome X86Val} {P : X86Val → Prop}
    (hstep : evalX86Step body s = .terminated .unwind)
    (hreach : ReachesPrefix X86Machine body init n s tr out) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hterm =>
    subst hterm
    exact ⟨True.intro, fun _ h => by cases h⟩

/-!
## 3. Standard `wpX86` and Cut-Point Weakest Precondition (`wpX86Cut`)
-/

/-- Fuel-bounded weakest precondition generator for `Trusted.X86Body`. -/
noncomputable def wpX86 (fuel : Nat) (rootBody : X86Body) (s : X86State)
    (P : X86Val → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    let active := s.curBody.getD rootBody
    match active.blocks[s.bb]? with
    | none => False
    | some blk =>
      match blk.instrs[s.ip]? with
      | some instr =>
        match evalX86Instr s instr with
        | .step () s' => wpX86 fuel' rootBody s' P
        | .terminated (.normal v) => P v
        | .terminated .unwind => True
        | _ => False
      | none =>
        match blk.term with
        | .jccBool cond falseTarget trueTarget =>
          match evalX86Operand s.mem cond with
          | some (.boolVal b, mem') =>
            (b = false →
              wpX86 fuel' rootBody
                { s with mem := mem', bb := falseTarget.index, ip := 0 } P) ∧
            (b = true →
              wpX86 fuel' rootBody
                { s with mem := mem', bb := trueTarget.index, ip := 0 } P)
          | _ => False
        | .repMovsbJmp dst srcTy dstTy ptrOp target =>
          match evalX86Operand s.mem ptrOp with
          | some (.stackPtr slot, mem') =>
            match mem' slot.index with
            | some (.bytes vSz bits) =>
              let srcSz := evalX86TyByteSize s.tySizes srcTy
              let dstSz := evalX86TyByteSize s.tySizes dstTy
              srcSz = dstSz ∧
              vSz = srcSz ∧
              wpX86 fuel' rootBody {
                s with
                mem := updateSlot mem' dst.index (some (.bytes dstSz bits))
                bb := target.index
                ip := 0
              } P
            | _ => False
          | _ => False
        | term =>
          match evalX86Term s term with
          | .step () s' => wpX86 fuel' rootBody s' P
          | .terminated (.normal v) => P v
          | .terminated .unwind => True
          | _ => False

/-- Soundness of `wpX86` across `StateSubsumed cs s`. -/
theorem wpX86_subsumed_sound (fuel : Nat) (body : X86Body)
    (init cs s : X86State) (P : X86Val → Prop)
    (hsub : StateSubsumed cs s) (hwp : wpX86 fuel body cs P) :
    ∀ (n : Nat) (tr : List Unit) (out : PrefixOutcome X86Val),
      ReachesPrefix X86Machine body init n s tr out →
      SafeAndEnsures P out := by
  induction fuel generalizing cs s with
  | zero => cases hwp
  | succ fuel' ih =>
    intro n tr out hreach
    dsimp [wpX86] at hwp
    cases hblk : (cs.curBody.getD body).blocks[cs.bb]? with
    | none =>
      rw [hblk] at hwp
      cases hwp
    | some blk =>
      rw [hblk] at hwp
      dsimp at hwp
      cases hinstr : blk.instrs[cs.ip]? with
      | some instr =>
        rw [hinstr] at hwp
        dsimp at hwp
        have hstep_eq : evalX86Step body cs = evalX86Instr cs instr := by
          dsimp [evalX86Step]
          rw [hblk]
          dsimp
          rw [hinstr]
        cases hres : evalX86Instr cs instr with
        | step obs cs' =>
          cases obs
          rw [hres] at hwp hstep_eq
          cases (evalX86Step_subsumed body hsub).1 cs' hstep_eq with
          | intro s' hs' =>
            exact reachesPrefix_safeAndEnsures_of_step hs'.1 hreach
              (fun n' tr' hr' => ih cs' s' hs'.2 hwp n' tr' out hr')
        | terminated term =>
          cases term with
          | normal v =>
            rw [hres] at hwp hstep_eq
            have hs_term := (evalX86Step_subsumed body hsub).2 (.normal v) hstep_eq
            exact reachesPrefix_safeAndEnsures_of_normal hs_term hreach hwp
          | unwind =>
            rw [hres] at hstep_eq
            have hs_term := (evalX86Step_subsumed body hsub).2 .unwind hstep_eq
            exact reachesPrefix_safeAndEnsures_of_unwind hs_term hreach
        | failed _ | choice _ _ =>
          rw [hres] at hwp
          cases hwp
      | none =>
        rw [hinstr] at hwp
        dsimp at hwp
        have hstep_eq : evalX86Step body cs = evalX86Term cs blk.term := by
          dsimp [evalX86Step]
          rw [hblk]
          dsimp
          rw [hinstr]
        cases hterm : blk.term with
        | jccBool cond falseTarget trueTarget =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hcond : evalX86Operand cs.mem cond with
          | none =>
            rw [hcond] at hwp
            cases hwp
          | some p =>
            cases p with
            | mk v mem' =>
              cases v with
              | boolVal b =>
                rw [hcond] at hwp
                dsimp at hwp
                cases b with
                | false =>
                  have hstep_false :
                      evalX86Step body cs =
                        .step () { cs with mem := mem', bb := falseTarget.index, ip := 0 } := by
                    rw [hstep_eq]
                    dsimp [evalX86Term]
                    rw [hcond]
                  cases (evalX86Step_subsumed body hsub).1 _ hstep_false with
                  | intro s' hs' =>
                    exact reachesPrefix_safeAndEnsures_of_step hs'.1 hreach
                      (fun n' tr' hr' => ih _ s' hs'.2 (hwp.1 rfl) n' tr' out hr')
                | true =>
                  have hstep_true :
                      evalX86Step body cs =
                        .step () { cs with mem := mem', bb := trueTarget.index, ip := 0 } := by
                    rw [hstep_eq]
                    dsimp [evalX86Term]
                    rw [hcond]
                  cases (evalX86Step_subsumed body hsub).1 _ hstep_true with
                  | intro s' hs' =>
                    exact reachesPrefix_safeAndEnsures_of_step hs'.1 hreach
                      (fun n' tr' hr' => ih _ s' hs'.2 (hwp.2 rfl) n' tr' out hr')
              | word64 _ | unit | adt _ _ | bytes _ _ | stackPtr _ =>
                rw [hcond] at hwp
                cases hwp
        | repMovsbJmp dst srcTy dstTy ptrOp target =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hptr : evalX86Operand cs.mem ptrOp with
          | none =>
            rw [hptr] at hwp
            cases hwp
          | some p =>
            cases p with
            | mk ptrVal mem' =>
              cases ptrVal with
              | stackPtr slot =>
                rw [hptr] at hwp
                dsimp at hwp
                cases hslot : mem' slot.index with
                | none =>
                  rw [hslot] at hwp
                  cases hwp
                | some slotVal =>
                  cases slotVal with
                  | bytes vSz bits =>
                    rw [hslot] at hwp
                    dsimp at hwp
                    have hsrc_eq :
                        evalX86TyByteSize cs.tySizes srcTy =
                          evalX86TyByteSize cs.tySizes dstTy := hwp.1
                    have hv_eq :
                        vSz = evalX86TyByteSize cs.tySizes srcTy := hwp.2.1
                    have hwp_next := hwp.2.2
                    have hdec1 :
                        decide (evalX86TyByteSize cs.tySizes srcTy =
                          evalX86TyByteSize cs.tySizes dstTy) = true :=
                      decide_eq_true hsrc_eq
                    have hdec2 :
                        decide (vSz = evalX86TyByteSize cs.tySizes srcTy) = true :=
                      decide_eq_true hv_eq
                    have hstep_rep :
                        evalX86Step body cs =
                          .step () {
                            cs with
                            mem := updateSlot mem' dst.index
                              (some (.bytes (evalX86TyByteSize cs.tySizes dstTy) bits))
                            bb := target.index
                            ip := 0
                          } := by
                      rw [hstep_eq]
                      dsimp [evalX86Term, evalRepMovsb]
                      rw [hptr]; dsimp; rw [hdec1]; dsimp; rw [hslot]; dsimp
                      rw [hdec2]; rfl
                    cases (evalX86Step_subsumed body hsub).1 _ hstep_rep with
                    | intro s' hs' =>
                      exact reachesPrefix_safeAndEnsures_of_step hs'.1 hreach
                        (fun n' tr' hr' => ih _ s' hs'.2 hwp_next n' tr' out hr')
                  | word64 _ | boolVal _ | unit | adt _ _ | stackPtr _ =>
                    rw [hslot] at hwp
                    cases hwp
              | word64 _ | boolVal _ | unit | adt _ _ | bytes _ _ =>
                rw [hptr] at hwp
                cases hwp
        | ret | jmp _ | ud2 | abortPanic | movSizeOfJmp _ _ _ | call1 _ _ _ _ =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hres : evalX86Term cs blk.term with
          | step obs cs' =>
            cases obs
            rw [hterm] at hres
            rw [hres] at hwp hstep_eq
            cases (evalX86Step_subsumed body hsub).1 cs' hstep_eq with
            | intro s' hs' =>
              exact reachesPrefix_safeAndEnsures_of_step hs'.1 hreach
                (fun n' tr' hr' => ih cs' s' hs'.2 hwp n' tr' out hr')
          | terminated term =>
            cases term with
            | normal v =>
              rw [hterm] at hres
              rw [hres] at hwp hstep_eq
              have hs_term := (evalX86Step_subsumed body hsub).2 (.normal v) hstep_eq
              exact reachesPrefix_safeAndEnsures_of_normal hs_term hreach hwp
            | unwind =>
              rw [hterm] at hres
              rw [hres] at hstep_eq
              have hs_term := (evalX86Step_subsumed body hsub).2 .unwind hstep_eq
              exact reachesPrefix_safeAndEnsures_of_unwind hs_term hreach
          | failed _ | choice _ _ =>
            rw [hterm] at hres
            rw [hres] at hwp
            cases hwp

/-- Standard `wpX86_sound` on a single state `s`. -/
theorem wpX86_sound (fuel : Nat) (body : X86Body) (init s : X86State)
    (P : X86Val → Prop) (hwp : wpX86 fuel body s P) :
    ∀ (n : Nat) (tr : List Unit) (out : PrefixOutcome X86Val),
      ReachesPrefix X86Machine body init n s tr out →
      SafeAndEnsures P out :=
  wpX86_subsumed_sound fuel body init s s P (StateSubsumed.refl s) hwp

/-- Cut-point-aware, fuel-bounded weakest precondition generator (`wpX86Cut`).

    Steps from `s` just like `wpX86`, except that whenever a basic-block
    terminator transitions to the cut-point basic block `cutBb` at the root
    frame (`s'.bb == cutBb && s'.ip == 0 && s'.curBody.isNone`), symbolic
    execution stops unfolding and emits
    `Cut (canonState rootBody.slotCount s')`.

    Because `wpX86Cut` always executes at least one instruction or terminator
    step before checking whether the successor state `s'` is at `cutBb`, every
    reachability transition from `s` to `Cut` strictly decreases the
    `ReachesPrefix` step budget (`n' < n`). -/
noncomputable def wpX86Cut (fuel : Nat) (rootBody : X86Body) (cutBb : Nat)
    (s : X86State) (Cut : X86State → Prop) (P : X86Val → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    let active := s.curBody.getD rootBody
    match active.blocks[s.bb]? with
    | none => False
    | some blk =>
      match blk.instrs[s.ip]? with
      | some instr =>
        match evalX86Instr s instr with
        | .step () s' => wpX86Cut fuel' rootBody cutBb s' Cut P
        | .terminated (.normal v) => P v
        | .terminated .unwind => True
        | _ => False
      | none =>
        match blk.term with
        | .jccBool cond falseTarget trueTarget =>
          match evalX86Operand s.mem cond with
          | some (.boolVal b, mem') =>
            let sFalse : X86State :=
              { s with mem := mem', bb := falseTarget.index, ip := 0 }
            let sTrue : X86State :=
              { s with mem := mem', bb := trueTarget.index, ip := 0 }
            (b = false →
              if sFalse.bb == cutBb && sFalse.ip == 0 && sFalse.curBody.isNone then
                Cut (canonState rootBody.slotCount sFalse)
              else
                wpX86Cut fuel' rootBody cutBb sFalse Cut P) ∧
            (b = true →
              if sTrue.bb == cutBb && sTrue.ip == 0 && sTrue.curBody.isNone then
                Cut (canonState rootBody.slotCount sTrue)
              else
                wpX86Cut fuel' rootBody cutBb sTrue Cut P)
          | _ => False
        | .repMovsbJmp dst srcTy dstTy ptrOp target =>
          match evalX86Operand s.mem ptrOp with
          | some (.stackPtr slot, mem') =>
            match mem' slot.index with
            | some (.bytes vSz bits) =>
              let srcSz := evalX86TyByteSize s.tySizes srcTy
              let dstSz := evalX86TyByteSize s.tySizes dstTy
              let sNext : X86State := {
                s with
                mem := updateSlot mem' dst.index (some (.bytes dstSz bits))
                bb := target.index
                ip := 0
              }
              srcSz = dstSz ∧
              vSz = srcSz ∧
              (if sNext.bb == cutBb && sNext.ip == 0 && sNext.curBody.isNone then
                 Cut (canonState rootBody.slotCount sNext)
               else
                 wpX86Cut fuel' rootBody cutBb sNext Cut P)
            | _ => False
          | _ => False
        | term =>
          match evalX86Term s term with
          | .step () s' =>
            if s'.bb == cutBb && s'.ip == 0 && s'.curBody.isNone then
              Cut (canonState rootBody.slotCount s')
            else
              wpX86Cut fuel' rootBody cutBb s' Cut P
          | .terminated (.normal v) => P v
          | .terminated .unwind => True
          | _ => False

/-- Explicit disjunctive outcome of `wpX86Cut` on a finite prefix of length `n`:
    either the prefix completes safely without reaching `cutBb`
    (`SafeAndEnsures P out`), or it reaches `cutBb` after at least one step with
    a strictly smaller remaining budget `n' < n` in a state `s'` subsumed by a
    canonical state `cs'` satisfying `Cut cs'`. -/
def ReachesCutOrTerm (body : X86Body) (cutBb : Nat) (init : X86State)
    (n : Nat) (out : PrefixOutcome X86Val) (Cut : X86State → Prop)
    (P : X86Val → Prop) : Prop :=
  SafeAndEnsures P out ∨
  ∃ (cs' s' : X86State) (n' : Nat) (tr' : List Unit),
    n' < n ∧
    StateSubsumed cs' s' ∧
    cs'.bb = cutBb ∧
    cs'.ip = 0 ∧
    cs'.curBody = none ∧
    Cut cs' ∧
    ReachesPrefix X86Machine body init n' s' tr' out

theorem isNone_eq_true_iff {α : Type} {o : Option α} :
    o.isNone = true → o = none := by
  cases o with
  | none => intro _; rfl
  | some _ => intro h; cases h

theorem bool_and3_eq_true {a b c : Bool} (h : (a && b && c) = true) :
    a = true ∧ b = true ∧ c = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true =>
      cases c with
      | false => cases h
      | true => exact ⟨rfl, rfl, rfl⟩

/-- Single-step helper for `wpX86Cut_sound` at basic-block terminators. -/
theorem wpX86Cut_term_step_sound {fuel' : Nat} {body : X86Body} {cutBb : Nat}
    {init cs cs' s : X86State} {Cut : X86State → Prop} {P : X86Val → Prop}
    {n : Nat} {tr : List Unit} {out : PrefixOutcome X86Val}
    (hsub : StateSubsumed cs s)
    (hstep_cs : evalX86Step body cs = .step () cs')
    (hreach : ReachesPrefix X86Machine body init n s tr out)
    (hnext :
      if cs'.bb == cutBb && cs'.ip == 0 && cs'.curBody.isNone then
        Cut (canonState body.slotCount cs')
      else
        wpX86Cut fuel' body cutBb cs' Cut P)
    (ih : ∀ (cs' s' : X86State),
      StateSubsumed cs' s' →
      wpX86Cut fuel' body cutBb cs' Cut P →
      ∀ (n' : Nat) (tr' : List Unit),
        ReachesPrefix X86Machine body init n' s' tr' out →
        (∀ (cs'' s'' : X86State) (n'' : Nat) (tr'' : List Unit),
          n'' < n' →
          StateSubsumed cs'' s'' →
          cs''.bb = cutBb →
          cs''.ip = 0 →
          cs''.curBody = none →
          Cut cs'' →
          ReachesPrefix X86Machine body init n'' s'' tr'' out →
          SafeAndEnsures P out) →
        SafeAndEnsures P out)
    (hcut : ∀ (cs' s' : X86State) (n' : Nat) (tr' : List Unit),
      n' < n →
      StateSubsumed cs' s' →
      cs'.bb = cutBb →
      cs'.ip = 0 →
      cs'.curBody = none →
      Cut cs' →
      ReachesPrefix X86Machine body init n' s' tr' out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  cases (evalX86Step_subsumed body hsub).1 cs' hstep_cs with
  | intro s' hs' =>
    refine reachesPrefix_safeAndEnsures_of_step_lt hs'.1 hreach
      (fun n' tr' hlt hr' => ?_)
    cases hcond : (cs'.bb == cutBb && cs'.ip == 0 && cs'.curBody.isNone) with
    | true =>
      rw [hcond] at hnext
      dsimp at hnext
      have hand := bool_and3_eq_true hcond
      have hbb : cs'.bb = cutBb := eq_of_beq hand.1
      have hip : cs'.ip = 0 := eq_of_beq hand.2.1
      have hcur : cs'.curBody = none := isNone_eq_true_iff hand.2.2
      have hsub_canon : StateSubsumed (canonState body.slotCount cs') s' :=
        StateSubsumed.trans (canonState_subsumed body.slotCount cs') hs'.2
      exact hcut (canonState body.slotCount cs') s' n' tr' hlt hsub_canon
        hbb hip hcur hnext hr'
    | false =>
      rw [hcond] at hnext
      dsimp at hnext
      exact ih cs' s' hs'.2 hnext n' tr' hr'
        (fun cs'' s'' n'' tr'' hlt'' =>
          hcut cs'' s'' n'' tr'' (Nat.lt_trans hlt'' hlt))

/-- Continuation-passing soundness theorem for `wpX86Cut`: if
    `wpX86Cut fuel body cutBb cs Cut P` holds and `StateSubsumed cs s`, then any
    execution prefix from `s` of length `n` satisfies `SafeAndEnsures P out`
    provided that every cut-point state `cs'` reached with strictly smaller step
    budget `n' < n` satisfies `SafeAndEnsures P out`. -/
theorem wpX86Cut_sound (fuel : Nat) (body : X86Body) (cutBb : Nat)
    (init cs s : X86State) (Cut : X86State → Prop) (P : X86Val → Prop)
    (hsub : StateSubsumed cs s)
    (hwp : wpX86Cut fuel body cutBb cs Cut P) :
    ∀ (n : Nat) (tr : List Unit) (out : PrefixOutcome X86Val),
      ReachesPrefix X86Machine body init n s tr out →
      (∀ (cs' s' : X86State) (n' : Nat) (tr' : List Unit),
        n' < n →
        StateSubsumed cs' s' →
        cs'.bb = cutBb →
        cs'.ip = 0 →
        cs'.curBody = none →
        Cut cs' →
        ReachesPrefix X86Machine body init n' s' tr' out →
        SafeAndEnsures P out) →
      SafeAndEnsures P out := by
  induction fuel generalizing cs s with
  | zero => cases hwp
  | succ fuel' ih =>
    intro n tr out hreach hcut
    dsimp [wpX86Cut] at hwp
    cases hblk : (cs.curBody.getD body).blocks[cs.bb]? with
    | none =>
      rw [hblk] at hwp
      cases hwp
    | some blk =>
      rw [hblk] at hwp
      dsimp at hwp
      cases hinstr : blk.instrs[cs.ip]? with
      | some instr =>
        rw [hinstr] at hwp
        dsimp at hwp
        have hstep_eq : evalX86Step body cs = evalX86Instr cs instr := by
          dsimp [evalX86Step]
          rw [hblk]
          dsimp
          rw [hinstr]
        cases hres : evalX86Instr cs instr with
        | step obs cs' =>
          cases obs
          rw [hres] at hwp hstep_eq
          cases (evalX86Step_subsumed body hsub).1 cs' hstep_eq with
          | intro s' hs' =>
            exact reachesPrefix_safeAndEnsures_of_step_lt hs'.1 hreach
              (fun n' tr' hlt hr' =>
                ih cs' s' hs'.2 hwp n' tr' out hr'
                  (fun cs'' s'' n'' tr'' hlt'' =>
                    hcut cs'' s'' n'' tr'' (Nat.lt_trans hlt'' hlt)))
        | terminated term =>
          cases term with
          | normal v =>
            rw [hres] at hwp hstep_eq
            have hs_term := (evalX86Step_subsumed body hsub).2 (.normal v) hstep_eq
            exact reachesPrefix_safeAndEnsures_of_normal hs_term hreach hwp
          | unwind =>
            rw [hres] at hstep_eq
            have hs_term := (evalX86Step_subsumed body hsub).2 .unwind hstep_eq
            exact reachesPrefix_safeAndEnsures_of_unwind hs_term hreach
        | failed _ | choice _ _ =>
          rw [hres] at hwp
          cases hwp
      | none =>
        rw [hinstr] at hwp
        dsimp at hwp
        have hstep_eq : evalX86Step body cs = evalX86Term cs blk.term := by
          dsimp [evalX86Step]
          rw [hblk]
          dsimp
          rw [hinstr]
        cases hterm : blk.term with
        | jccBool cond falseTarget trueTarget =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hcond : evalX86Operand cs.mem cond with
          | none =>
            rw [hcond] at hwp
            cases hwp
          | some p =>
            cases p with
            | mk v mem' =>
              cases v with
              | boolVal b =>
                rw [hcond] at hwp
                dsimp at hwp
                cases b with
                | false =>
                  have hstep_false :
                      evalX86Step body cs =
                        .step () { cs with mem := mem', bb := falseTarget.index, ip := 0 } := by
                    rw [hstep_eq]
                    dsimp [evalX86Term]
                    rw [hcond]
                  exact wpX86Cut_term_step_sound hsub hstep_false hreach
                    (hwp.1 rfl) (fun cs' s' hsub' hwp' n' tr' hr' hc' =>
                      ih cs' s' hsub' hwp' n' tr' out hr' hc') hcut
                | true =>
                  have hstep_true :
                      evalX86Step body cs =
                        .step () { cs with mem := mem', bb := trueTarget.index, ip := 0 } := by
                    rw [hstep_eq]
                    dsimp [evalX86Term]
                    rw [hcond]
                  exact wpX86Cut_term_step_sound hsub hstep_true hreach
                    (hwp.2 rfl) (fun cs' s' hsub' hwp' n' tr' hr' hc' =>
                      ih cs' s' hsub' hwp' n' tr' out hr' hc') hcut
              | word64 _ | unit | adt _ _ | bytes _ _ | stackPtr _ =>
                rw [hcond] at hwp
                cases hwp
        | repMovsbJmp dst srcTy dstTy ptrOp target =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hptr : evalX86Operand cs.mem ptrOp with
          | none =>
            rw [hptr] at hwp
            cases hwp
          | some p =>
            cases p with
            | mk ptrVal mem' =>
              cases ptrVal with
              | stackPtr slot =>
                rw [hptr] at hwp
                dsimp at hwp
                cases hslot : mem' slot.index with
                | none =>
                  rw [hslot] at hwp
                  cases hwp
                | some slotVal =>
                  cases slotVal with
                  | bytes vSz bits =>
                    rw [hslot] at hwp
                    dsimp at hwp
                    have hsrc_eq :
                        evalX86TyByteSize cs.tySizes srcTy =
                          evalX86TyByteSize cs.tySizes dstTy := hwp.1
                    have hv_eq :
                        vSz = evalX86TyByteSize cs.tySizes srcTy := hwp.2.1
                    have hwp_next := hwp.2.2
                    have hdec1 :
                        decide (evalX86TyByteSize cs.tySizes srcTy =
                          evalX86TyByteSize cs.tySizes dstTy) = true :=
                      decide_eq_true hsrc_eq
                    have hdec2 :
                        decide (vSz = evalX86TyByteSize cs.tySizes srcTy) = true :=
                      decide_eq_true hv_eq
                    have hstep_rep :
                        evalX86Step body cs =
                          .step () {
                            cs with
                            mem := updateSlot mem' dst.index
                              (some (.bytes (evalX86TyByteSize cs.tySizes dstTy) bits))
                            bb := target.index
                            ip := 0
                          } := by
                      rw [hstep_eq]
                      dsimp [evalX86Term, evalRepMovsb]
                      rw [hptr]; dsimp; rw [hdec1]; dsimp; rw [hslot]; dsimp
                      rw [hdec2]; rfl
                    exact wpX86Cut_term_step_sound hsub hstep_rep hreach
                      hwp_next (fun cs' s' hsub' hwp' n' tr' hr' hc' =>
                        ih cs' s' hsub' hwp' n' tr' out hr' hc') hcut
                  | word64 _ | boolVal _ | unit | adt _ _ | stackPtr _ =>
                    rw [hslot] at hwp
                    cases hwp
              | word64 _ | boolVal _ | unit | adt _ _ | bytes _ _ =>
                rw [hptr] at hwp
                cases hwp
        | ret | jmp _ | ud2 | abortPanic | movSizeOfJmp _ _ _ | call1 _ _ _ _ =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hres : evalX86Term cs blk.term with
          | step obs cs' =>
            cases obs
            rw [hterm] at hres
            rw [hres] at hwp hstep_eq
            exact wpX86Cut_term_step_sound hsub hstep_eq hreach hwp
              (fun cs' s' hsub' hwp' n' tr' hr' hc' =>
                ih cs' s' hsub' hwp' n' tr' out hr' hc') hcut
          | terminated term =>
            cases term with
            | normal v =>
              rw [hterm] at hres
              rw [hres] at hwp hstep_eq
              have hs_term := (evalX86Step_subsumed body hsub).2 (.normal v) hstep_eq
              exact reachesPrefix_safeAndEnsures_of_normal hs_term hreach hwp
            | unwind =>
              rw [hterm] at hres
              rw [hres] at hstep_eq
              have hs_term := (evalX86Step_subsumed body hsub).2 .unwind hstep_eq
              exact reachesPrefix_safeAndEnsures_of_unwind hs_term hreach
          | failed _ | choice _ _ =>
            rw [hterm] at hres
            rw [hres] at hwp
            cases hwp

/-- Single-step helper for `wpX86Cut_reachesCutOrTerm` at basic-block
    terminators. -/
theorem wpX86Cut_term_step_reachesCutOrTerm {fuel' : Nat} {body : X86Body}
    {cutBb : Nat} {init cs cs' s : X86State} {Cut : X86State → Prop}
    {P : X86Val → Prop} {n : Nat} {tr : List Unit}
    {out : PrefixOutcome X86Val}
    (hsub : StateSubsumed cs s)
    (hstep_cs : evalX86Step body cs = .step () cs')
    (hreach : ReachesPrefix X86Machine body init n s tr out)
    (hnext :
      if cs'.bb == cutBb && cs'.ip == 0 && cs'.curBody.isNone then
        Cut (canonState body.slotCount cs')
      else
        wpX86Cut fuel' body cutBb cs' Cut P)
    (ih : ∀ (cs' s' : X86State),
      StateSubsumed cs' s' →
      wpX86Cut fuel' body cutBb cs' Cut P →
      ∀ (n' : Nat) (tr' : List Unit),
        ReachesPrefix X86Machine body init n' s' tr' out →
        ReachesCutOrTerm body cutBb init n' out Cut P) :
    ReachesCutOrTerm body cutBb init n out Cut P := by
  cases (evalX86Step_subsumed body hsub).1 cs' hstep_cs with
  | intro s' hs' =>
    cases reachesPrefix_of_step_lt hs'.1 hreach with
    | inl hrun =>
      subst hrun
      exact Or.inl ⟨True.intro, fun _ h => by cases h⟩
    | inr hex =>
      cases hex with
      | intro n' htr =>
        cases htr with
        | intro tr' hp =>
          cases hcond : (cs'.bb == cutBb && cs'.ip == 0 && cs'.curBody.isNone) with
          | true =>
            rw [hcond] at hnext
            dsimp at hnext
            have hand := bool_and3_eq_true hcond
            exact Or.inr ⟨canonState body.slotCount cs', s', n', tr', hp.1,
              StateSubsumed.trans (canonState_subsumed body.slotCount cs') hs'.2,
              eq_of_beq hand.1, eq_of_beq hand.2.1,
              isNone_eq_true_iff hand.2.2, hnext, hp.2⟩
          | false =>
            rw [hcond] at hnext
            dsimp at hnext
            cases ih cs' s' hs'.2 hnext n' tr' hp.2 with
            | inl hsafe => exact Or.inl hsafe
            | inr hcut =>
              cases hcut with
              | intro cs'' hex1 =>
                cases hex1 with
                | intro s'' hex2 =>
                  cases hex2 with
                  | intro n'' hex3 =>
                    cases hex3 with
                    | intro tr'' hrest =>
                      exact Or.inr ⟨cs'', s'', n'', tr'',
                        Nat.lt_trans hrest.1 hp.1, hrest.2⟩

/-- Explicit disjunctive soundness theorem for `wpX86Cut`: every finite prefix
    from `s` satisfies `ReachesCutOrTerm`. -/
theorem wpX86Cut_reachesCutOrTerm (fuel : Nat) (body : X86Body) (cutBb : Nat)
    (init cs s : X86State) (Cut : X86State → Prop) (P : X86Val → Prop)
    (hsub : StateSubsumed cs s)
    (hwp : wpX86Cut fuel body cutBb cs Cut P)
    (n : Nat) (tr : List Unit) (out : PrefixOutcome X86Val)
    (hreach : ReachesPrefix X86Machine body init n s tr out) :
    ReachesCutOrTerm body cutBb init n out Cut P := by
  induction fuel generalizing cs s n tr with
  | zero => cases hwp
  | succ fuel' ih =>
    dsimp [wpX86Cut] at hwp
    cases hblk : (cs.curBody.getD body).blocks[cs.bb]? with
    | none => rw [hblk] at hwp; cases hwp
    | some blk =>
      rw [hblk] at hwp
      dsimp at hwp
      cases hinstr : blk.instrs[cs.ip]? with
      | some instr =>
        rw [hinstr] at hwp
        dsimp at hwp
        have hstep_eq : evalX86Step body cs = evalX86Instr cs instr := by
          dsimp [evalX86Step]; rw [hblk]; dsimp; rw [hinstr]
        cases hres : evalX86Instr cs instr with
        | step obs cs' =>
          cases obs
          rw [hres] at hwp hstep_eq
          cases (evalX86Step_subsumed body hsub).1 cs' hstep_eq with
          | intro s' hs' =>
            cases reachesPrefix_of_step_lt hs'.1 hreach with
            | inl hrun =>
              subst hrun
              exact Or.inl ⟨True.intro, fun _ h => by cases h⟩
            | inr hex =>
              cases hex with
              | intro n' htr =>
                cases htr with
                | intro tr' hp =>
                  cases ih cs' s' hs'.2 hwp n' tr' hp.2 with
                  | inl hsafe => exact Or.inl hsafe
                  | inr hcut =>
                    cases hcut with
                    | intro cs'' hex1 =>
                      cases hex1 with
                      | intro s'' hex2 =>
                        cases hex2 with
                        | intro n'' hex3 =>
                          cases hex3 with
                          | intro tr'' hc =>
                            exact Or.inr ⟨cs'', s'', n'', tr'',
                              Nat.lt_trans hc.1 hp.1, hc.2⟩
        | terminated term =>
          cases term with
          | normal v =>
            rw [hres] at hwp hstep_eq
            have hs_term := (evalX86Step_subsumed body hsub).2 (.normal v) hstep_eq
            exact Or.inl (reachesPrefix_safeAndEnsures_of_normal hs_term hreach hwp)
          | unwind =>
            rw [hres] at hstep_eq
            have hs_term := (evalX86Step_subsumed body hsub).2 .unwind hstep_eq
            exact Or.inl (reachesPrefix_safeAndEnsures_of_unwind hs_term hreach)
        | failed _ | choice _ _ => rw [hres] at hwp; cases hwp
      | none =>
        rw [hinstr] at hwp
        dsimp at hwp
        have hstep_eq : evalX86Step body cs = evalX86Term cs blk.term := by
          dsimp [evalX86Step]; rw [hblk]; dsimp; rw [hinstr]
        cases hterm : blk.term with
        | jccBool cond falseTarget trueTarget =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hcond : evalX86Operand cs.mem cond with
          | none => rw [hcond] at hwp; cases hwp
          | some p =>
            cases p with
            | mk v mem' =>
              cases v with
              | boolVal b =>
                rw [hcond] at hwp
                dsimp at hwp
                cases b with
                | false =>
                  have hstep_false :
                      evalX86Step body cs =
                        .step () { cs with mem := mem', bb := falseTarget.index, ip := 0 } := by
                    rw [hstep_eq]; dsimp [evalX86Term]; rw [hcond]
                  exact wpX86Cut_term_step_reachesCutOrTerm hsub hstep_false
                    hreach (hwp.1 rfl) ih
                | true =>
                  have hstep_true :
                      evalX86Step body cs =
                        .step () { cs with mem := mem', bb := trueTarget.index, ip := 0 } := by
                    rw [hstep_eq]; dsimp [evalX86Term]; rw [hcond]
                  exact wpX86Cut_term_step_reachesCutOrTerm hsub hstep_true
                    hreach (hwp.2 rfl) ih
              | word64 _ | unit | adt _ _ | bytes _ _ | stackPtr _ =>
                rw [hcond] at hwp; cases hwp
        | repMovsbJmp dst srcTy dstTy ptrOp target =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hptr : evalX86Operand cs.mem ptrOp with
          | none => rw [hptr] at hwp; cases hwp
          | some p =>
            cases p with
            | mk ptrVal mem' =>
              cases ptrVal with
              | stackPtr slot =>
                rw [hptr] at hwp; dsimp at hwp
                cases hslot : mem' slot.index with
                | none => rw [hslot] at hwp; cases hwp
                | some slotVal =>
                  cases slotVal with
                  | bytes vSz bits =>
                    rw [hslot] at hwp; dsimp at hwp
                    have hdec1 :
                        decide (evalX86TyByteSize cs.tySizes srcTy =
                          evalX86TyByteSize cs.tySizes dstTy) = true :=
                      decide_eq_true hwp.1
                    have hdec2 :
                        decide (vSz = evalX86TyByteSize cs.tySizes srcTy) = true :=
                      decide_eq_true hwp.2.1
                    have hstep_rep :
                        evalX86Step body cs =
                          .step () {
                            cs with
                            mem := updateSlot mem' dst.index
                              (some (.bytes (evalX86TyByteSize cs.tySizes dstTy) bits))
                            bb := target.index
                            ip := 0
                          } := by
                      rw [hstep_eq]; dsimp [evalX86Term, evalRepMovsb]
                      rw [hptr]; dsimp; rw [hdec1]; dsimp; rw [hslot]; dsimp
                      rw [hdec2]; rfl
                    exact wpX86Cut_term_step_reachesCutOrTerm hsub hstep_rep
                      hreach hwp.2.2 ih
                  | word64 _ | boolVal _ | unit | adt _ _ | stackPtr _ =>
                    rw [hslot] at hwp; cases hwp
              | word64 _ | boolVal _ | unit | adt _ _ | bytes _ _ =>
                rw [hptr] at hwp; cases hwp
        | ret | jmp _ | ud2 | abortPanic | movSizeOfJmp _ _ _ | call1 _ _ _ _ =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hres : evalX86Term cs blk.term with
          | step obs cs' =>
            cases obs
            rw [hterm] at hres
            rw [hres] at hwp hstep_eq
            exact wpX86Cut_term_step_reachesCutOrTerm hsub hstep_eq hreach hwp ih
          | terminated term =>
            cases term with
            | normal v =>
              rw [hterm] at hres; rw [hres] at hwp hstep_eq
              have hs_term := (evalX86Step_subsumed body hsub).2 (.normal v) hstep_eq
              exact Or.inl (reachesPrefix_safeAndEnsures_of_normal hs_term hreach hwp)
            | unwind =>
              rw [hterm] at hres; rw [hres] at hstep_eq
              have hs_term := (evalX86Step_subsumed body hsub).2 .unwind hstep_eq
              exact Or.inl (reachesPrefix_safeAndEnsures_of_unwind hs_term hreach)
          | failed _ | choice _ _ =>
            rw [hterm] at hres; rw [hres] at hwp; cases hwp

/-!
## 4. Inductive Loop Verification & Composable Cut-Point Combinators

We now prove the strong-induction loop theorem
(`reachesPrefix_of_loop_invariant` and `wpX86_loop_sound`) and package terminal
execution (`byWpX86`), cut-point / diamond-join staging (`byCutPoint`,
`byExactCut`, `byIndexedCut`), and inductive loops (`byLoop`, `byIndexedLoop`)
into the composable judgment `AllPrefixesSafeAndEnsures`.
-/

/-- Strong-induction loop theorem at a loop header `headerBb`: if every
    canonical state `cs` at `(headerBb, 0, none)` satisfying `Inv cs` steps via
    `wpX86Cut` either to safe termination (`SafeAndEnsures P`) or back to
    `headerBb` satisfying `Inv`, then every finite prefix of any length
    `n : Nat` from any subsumed state `s` satisfies `SafeAndEnsures P out`. -/
theorem reachesPrefix_of_loop_invariant
    (iterFuel : Nat) (body : X86Body) (headerBb : Nat) (init : X86State)
    (Inv : X86State → Prop) (P : X86Val → Prop)
    (h_iter : ∀ (cs : X86State),
      cs.bb = headerBb →
      cs.ip = 0 →
      cs.curBody = none →
      Inv cs →
      wpX86Cut iterFuel body headerBb cs Inv P) :
    ∀ (n : Nat) (cs s : X86State) (tr : List Unit) (out : PrefixOutcome X86Val),
      StateSubsumed cs s →
      cs.bb = headerBb →
      cs.ip = 0 →
      cs.curBody = none →
      Inv cs →
      ReachesPrefix X86Machine body init n s tr out →
      SafeAndEnsures P out := by
  refine nat_strong_ind
    (fun n =>
      ∀ (cs s : X86State) (tr : List Unit) (out : PrefixOutcome X86Val),
        StateSubsumed cs s →
        cs.bb = headerBb →
        cs.ip = 0 →
        cs.curBody = none →
        Inv cs →
        ReachesPrefix X86Machine body init n s tr out →
        SafeAndEnsures P out)
    ?_
  intro n ih cs s tr out hsub hbb hip hcur hinv hreach
  exact wpX86Cut_sound iterFuel body headerBb init cs s Inv P hsub
    (h_iter cs hbb hip hcur hinv) n tr out hreach
    (fun cs' s' n' tr' hlt hsub' hbb' hip' hcur' hinv' hr' =>
      ih n' hlt cs' s' tr' out hsub' hbb' hip' hcur' hinv' hr')

/-- Combined entry + loop soundness theorem (`wpX86_loop_sound`). -/
theorem wpX86_loop_sound
    (entryFuel iterFuel : Nat) (body : X86Body) (headerBb : Nat)
    (init cs₀ s₀ : X86State) (Inv : X86State → Prop) (P : X86Val → Prop)
    (hsub₀ : StateSubsumed cs₀ s₀)
    (h_entry : wpX86Cut entryFuel body headerBb cs₀ Inv P)
    (h_iter : ∀ (cs : X86State),
      cs.bb = headerBb →
      cs.ip = 0 →
      cs.curBody = none →
      Inv cs →
      wpX86Cut iterFuel body headerBb cs Inv P) :
    ∀ (n : Nat) (tr : List Unit) (out : PrefixOutcome X86Val),
      ReachesPrefix X86Machine body init n s₀ tr out →
      SafeAndEnsures P out := by
  intro n tr out hreach
  exact wpX86Cut_sound entryFuel body headerBb init cs₀ s₀ Inv P hsub₀
    h_entry n tr out hreach
    (fun cs' s' n' tr' _ hsub' hbb' hip' hcur' hinv' hr' =>
      reachesPrefix_of_loop_invariant iterFuel body headerBb init Inv P h_iter
        n' cs' s' tr' out hsub' hbb' hip' hcur' hinv' hr')

/-- Composable semantic judgment asserting that every finite prefix reachable
    from any concrete state `s` subsumed by `cs` is safe and satisfies `P` on
    normal return. -/
def AllPrefixesSafeAndEnsures (body : X86Body) (cs : X86State)
    (P : X86Val → Prop) : Prop :=
  ∀ (init s : X86State) (n : Nat) (tr : List Unit) (out : PrefixOutcome X86Val),
    StateSubsumed cs s →
    ReachesPrefix X86Machine body init n s tr out →
    SafeAndEnsures P out

/-- Indexed family of canonical cut-point states `stateAt : α → X86State` gated
    by an index invariant `Inv : α → Prop`. -/
def IndexedCut {α : Type} (stateAt : α → X86State) (Inv : α → Prop)
    (cs : X86State) : Prop :=
  ∃ a : α, Inv a ∧ cs = stateAt a

/-- Discharge `AllPrefixesSafeAndEnsures` directly via `wpX86`. -/
theorem byWpX86 (fuel : Nat) {body : X86Body} {cs : X86State}
    {P : X86Val → Prop} (hwp : wpX86 fuel body cs P) :
    AllPrefixesSafeAndEnsures body cs P :=
  fun init s n tr out hsub hreach =>
    wpX86_subsumed_sound fuel body init cs s P hsub hwp n tr out hreach

/-- Stage a cut-point `cutBb` with predicate `Cut`: executes up to `cutBb` via
    `wpX86Cut` and continues from any `cs'` satisfying `Cut cs'` with
    `AllPrefixesSafeAndEnsures body cs' P`. -/
theorem byCutPoint (fuel : Nat) {body : X86Body} (cutBb : Nat)
    {cs : X86State} (Cut : X86State → Prop) {P : X86Val → Prop}
    (h_pre : wpX86Cut fuel body cutBb cs Cut P)
    (h_cont : ∀ cs', cs'.bb = cutBb → cs'.ip = 0 → cs'.curBody = none →
      Cut cs' → AllPrefixesSafeAndEnsures body cs' P) :
    AllPrefixesSafeAndEnsures body cs P :=
  fun init s n tr out hsub hreach =>
    wpX86Cut_sound fuel body cutBb init cs s Cut P hsub h_pre n tr out hreach
      (fun cs' s' n' tr' _ hsub' hbb' hip' hcur' hcut' hr' =>
        h_cont cs' hbb' hip' hcur' hcut' init s' n' tr' out hsub' hr')

/-- Stage a cut-point `cutBb` where all incoming branches normalize to the exact
    same canonical state `csJoin` (`cs' = csJoin` by `rfl`). -/
theorem byExactCut (fuel : Nat) {body : X86Body} (cutBb : Nat)
    {cs : X86State} (csJoin : X86State) {P : X86Val → Prop}
    (h_pre : wpX86Cut fuel body cutBb cs (fun cs' => cs' = csJoin) P)
    (h_cont : AllPrefixesSafeAndEnsures body csJoin P) :
    AllPrefixesSafeAndEnsures body cs P :=
  byCutPoint fuel cutBb (fun cs' => cs' = csJoin) h_pre
    (fun _ _ _ _ heq => heq ▸ h_cont)

/-- Stage a cut-point `cutBb` parameterized by an indexed family of canonical
    join states `stateAt : α → X86State` and predicate `Inv : α → Prop`. -/
theorem byIndexedCut {α : Type} (fuel : Nat) {body : X86Body} (cutBb : Nat)
    {cs : X86State} (stateAt : α → X86State) (Inv : α → Prop)
    {P : X86Val → Prop}
    (h_pre : wpX86Cut fuel body cutBb cs (IndexedCut stateAt Inv) P)
    (h_cont : ∀ a, Inv a → AllPrefixesSafeAndEnsures body (stateAt a) P) :
    AllPrefixesSafeAndEnsures body cs P :=
  byCutPoint fuel cutBb (IndexedCut stateAt Inv) h_pre
    (fun _ _ _ _ ⟨a, ha, heq⟩ => heq ▸ h_cont a ha)

/-- Discharge `AllPrefixesSafeAndEnsures` for a loop with state predicate `Inv`
    at `headerBb`. -/
theorem byLoop (entryFuel iterFuel : Nat) {body : X86Body} (headerBb : Nat)
    {cs : X86State} (Inv : X86State → Prop) {P : X86Val → Prop}
    (h_entry : wpX86Cut entryFuel body headerBb cs Inv P)
    (h_iter : ∀ cs', cs'.bb = headerBb → cs'.ip = 0 → cs'.curBody = none →
      Inv cs' → wpX86Cut iterFuel body headerBb cs' Inv P) :
    AllPrefixesSafeAndEnsures body cs P :=
  fun init s n tr out hsub hreach =>
    wpX86_loop_sound entryFuel iterFuel body headerBb init cs s Inv P
      hsub h_entry h_iter n tr out hreach

/-- Discharge `AllPrefixesSafeAndEnsures` for a loop with an indexed family of
    canonical header states `stateAt : α → X86State` and index invariant
    `Inv : α → Prop`. -/
theorem byIndexedLoop {α : Type} (entryFuel iterFuel : Nat)
    {body : X86Body} (headerBb : Nat) {cs : X86State}
    (stateAt : α → X86State) (Inv : α → Prop) {P : X86Val → Prop}
    (h_entry : wpX86Cut entryFuel body headerBb cs (IndexedCut stateAt Inv) P)
    (h_iter : ∀ a, Inv a →
      wpX86Cut iterFuel body headerBb (stateAt a) (IndexedCut stateAt Inv) P) :
    AllPrefixesSafeAndEnsures body cs P :=
  byLoop entryFuel iterFuel headerBb (IndexedCut stateAt Inv) h_entry
    (fun _ _ _ _ ⟨a, ha, heq⟩ => heq ▸ h_iter a ha)

/-!
## 5. Universal Entry-State Bridges (`verifyX86UniversalSpec`, etc.)
-/

theorem forallTypedArgsAux_mono (tySizes : Nat → Nat) (k : Nat)
    (argTys : List X86Ty) (acc : Nat → Option X86Val)
    (P₁ P₂ : (Nat → Option X86Val) → Prop)
    (h : forallTypedArgsAux tySizes k argTys acc P₁)
    (himp : ∀ m, P₁ m → P₂ m) :
    forallTypedArgsAux tySizes k argTys acc P₂ := by
  induction argTys generalizing k acc with
  | nil => exact himp acc h
  | cons ty tys ih =>
    cases ty with
    | usize => intro a; exact ih (k + 1) _ (h a)
    | bool => intro b; exact ih (k + 1) _ (h b)
    | unit => exact ih (k + 1) _ h
    | adt _ => intro a; exact ih (k + 1) _ (h a)
    | param _ => intro bits; exact ih (k + 1) _ (h bits)
    | refParam _ => intro slot; exact ih (k + 1) _ (h slot)

theorem forallTypedArgs_mono (tySizes : Nat → Nat) (argTys : List X86Ty)
    (P₁ P₂ : (Nat → Option X86Val) → Prop)
    (h : forallTypedArgs tySizes argTys P₁)
    (himp : ∀ m, P₁ m → P₂ m) :
    forallTypedArgs tySizes argTys P₂ :=
  forallTypedArgsAux_mono tySizes 1 argTys (fun _ => none) P₁ P₂ h himp

/-- Universal bridge for `X86Lang.Spec` backed by
    `AllPrefixesSafeAndEnsures`. -/
theorem verifyX86UniversalSpec (body : X86Body)
    (Q : X86State → X86Val → Prop)
    (hvc : ∀ (tySizes : Nat → Nat),
      forallTypedArgs tySizes body.argTys (fun mem =>
        let s₀ : X86State := { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        AllPrefixesSafeAndEnsures body s₀ (Q s₀))) :
    X86Sem body ≤ X86Lang.Spec (fun q out =>
      ∀ ret, out.outcome = .terminated (.normal ret) → Q q.init ret) := by
  refine behaviorOf_le_pure (M := X86Machine) ?_
  intro q out hpfx
  have hall : AllPrefixesSafeAndEnsures body q.init (Q q.init) :=
    initX86State_canonical body q.init
      (fun s₀ => AllPrefixesSafeAndEnsures body s₀ (Q s₀))
      hpfx.1 (hvc q.init.tySizes)
  exact hall q.init q.init q.steps out.trace out.outcome
    (StateSubsumed.refl q.init) hpfx.2

/-- Universal bridge for `EnsuresRetLibInv defaultLibInv` backed by
    `AllPrefixesSafeAndEnsures`. -/
theorem verifyUniversalDefaultRetLibInv (body : X86Body)
    (pre : ExecQuery X86State → Prop)
    (hvc : ∀ (tySizes : Nat → Nat),
      forallTypedArgs tySizes body.argTys (fun mem =>
        let s₀ : X86State := { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        AllPrefixesSafeAndEnsures body s₀
          (defaultLibInv tySizes body.retTy))) :
    X86Sem body ≤ EnsuresRetLibInv defaultLibInv body.retTy pre := by
  refine behaviorOf_le_specOn (M := X86Machine) ?_
  intro q out _ hpfx
  have hall :
      AllPrefixesSafeAndEnsures body q.init
        (defaultLibInv q.init.tySizes body.retTy) :=
    initX86State_canonical body q.init
      (fun s₀ =>
        AllPrefixesSafeAndEnsures body s₀ (defaultLibInv s₀.tySizes body.retTy))
      hpfx.1 (hvc q.init.tySizes)
  exact hall q.init q.init q.steps out.trace out.outcome
    (StateSubsumed.refl q.init) hpfx.2

/-- Universal bridge for `EnsuresRetLibInv` on a `pubSafe` function backed by
    `AllPrefixesSafeAndEnsures`. -/
theorem verifyUniversalPubSafeRetLibInv (libInv : LibInv) (fn : CapturedFn)
    (traitLaws : Prop) (hkind : fn.kind = .pubSafe traitLaws)
    (hvc : ∀ (tySizes : Nat → Nat),
      MonoAdmitted tySizes fn.prog →
      traitLaws →
      forallTypedArgs tySizes fn.prog.argTys (fun mem =>
        allArgsLibInv libInv tySizes 1 fn.prog.argTys mem →
        let s₀ : X86State := { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        AllPrefixesSafeAndEnsures fn.prog s₀
          (libInv tySizes fn.prog.retTy))) :
    X86Sem fn.prog ≤
      EnsuresRetLibInv libInv fn.prog.retTy (fn.effectivePre libInv) := by
  refine behaviorOf_le_specOn (M := X86Machine) ?_
  intro q out hpre hpfx
  have hmono : MonoAdmitted q.init.tySizes fn.prog := hpre.1
  have hrest := hpre.2
  rw [hkind] at hrest
  have htrait : traitLaws := hrest.1
  have hlib : allArgsLibInv libInv q.init.tySizes 1 fn.prog.argTys q.init.mem :=
    argsSatisfyLibInv_imp_allArgsLibInv libInv q.init.tySizes fn.prog.argTys
      q.init.mem 1 hrest.2
  have hall :
      AllPrefixesSafeAndEnsures fn.prog q.init
        (libInv q.init.tySizes fn.prog.retTy) :=
    initX86State_canonical fn.prog q.init
      (fun s₀ =>
        allArgsLibInv libInv s₀.tySizes 1 fn.prog.argTys s₀.mem →
        AllPrefixesSafeAndEnsures fn.prog s₀ (libInv s₀.tySizes fn.prog.retTy))
      hpfx.1 (hvc q.init.tySizes hmono htrait) hlib
  exact hall q.init q.init q.steps out.trace out.outcome
    (StateSubsumed.refl q.init) hpfx.2

/-!
## 6. Concrete Verified Loop Benchmarks

### Benchmark 1: `countUpLoopBody` (`while i < n { i = i + 1 } return i`)

Models the compiled x86-64 CFG of:
```rust
pub fn count_up(n: usize) -> usize {
    let mut i: usize = 0;
    while i < n {
        i = i + 1;
    }
    i
}
```
-/

def countUpLoopBody : X86Body where
  argTys := [.usize]
  retTy := .usize
  slotCount := 4
  blocks := [
    -- bb0 (entry: i := 0; jmp bb1)
    { instrs := [
        .allocSlot ⟨2⟩,
        .mov ⟨2⟩ (.imm (.word64 0))
      ]
      term := .jmp ⟨1⟩ },
    -- bb1 (loop header: cond := i < n; jccBool cond bb2 bb3)
    { instrs := [
        .allocSlot ⟨3⟩,
        .alu .lt ⟨3⟩ (.stackSlot ⟨2⟩ false) (.stackSlot ⟨1⟩ false)
      ]
      term := .jccBool (.stackSlot ⟨3⟩ true) ⟨2⟩ ⟨3⟩ },
    -- bb2 (loop exit: ret i)
    { instrs := [
        .deallocSlot ⟨3⟩,
        .mov ⟨0⟩ (.stackSlot ⟨2⟩ true),
        .deallocSlot ⟨2⟩
      ]
      term := .ret },
    -- bb3 (loop body: i := i + 1; jmp bb1)
    { instrs := [
        .deallocSlot ⟨3⟩,
        .alu .add ⟨2⟩ (.stackSlot ⟨2⟩ true) (.imm (.word64 1))
      ]
      term := .jmp ⟨1⟩ }
  ]

/-- Canonical state at loop header `bb1` of `countUpLoopBody` for parameter `n`
    and loop counter `i`. -/
noncomputable def countUpHeaderState (tySizes : Nat → Nat) (n i : Nat) :
    X86State :=
  canonState 4 {
    mem := updateSlot
      (updateSlot (fun _ => none) 1 (some (.word64 n)))
      2 (some (.word64 i))
    bb := 1
    ip := 0
    tySizes := tySizes
  }

/-- `countUpLoopBody` satisfies `EnsuresRetLibInv defaultLibInv .usize pre` in
    3 lines via `byIndexedLoop` with trivial index invariant `fun _ => True`. -/
theorem countUpLoopBody_retLibInv (pre : ExecQuery X86State → Prop) :
    X86Sem countUpLoopBody ≤ EnsuresRetLibInv defaultLibInv .usize pre :=
  verifyUniversalDefaultRetLibInv countUpLoopBody pre (fun tySizes n =>
    byIndexedLoop 10 10 1 (countUpHeaderState tySizes n) (fun _ => True)
      ⟨0, True.intro, rfl⟩
      (fun i _ => ⟨fun _ => True.intro, fun _ => ⟨i + 1, True.intro, rfl⟩⟩))

/-- Full functional specification (`EnsuresEqArg 1`: returns `.word64 n` for
    every runtime argument `n : Nat`) for `countUpLoopBody`. -/
theorem countUpLoopBody_ensures_eq_arg :
    X86Sem countUpLoopBody ≤ EnsuresEqArg 1 :=
  verifyX86UniversalSpec countUpLoopBody (fun s ret => s.mem 1 = some ret)
    (fun tySizes n =>
      byIndexedLoop 10 10 1 (countUpHeaderState tySizes n) (fun i => i ≤ n)
        ⟨0, Nat.zero_le n, rfl⟩
        (fun i hle =>
          ⟨fun hfalse =>
            congrArg (fun k => some (X86Val.word64 k))
              (eq_of_le_of_not_lt hle (of_decide_eq_false hfalse)).symm,
           fun htrue =>
            ⟨i + 1, of_decide_eq_true htrue, rfl⟩⟩))

/-- Unconditional all-prefix safety (`X86Lang.WellFormed`) for
    `countUpLoopBody`. -/
theorem countUpLoopBody_wellFormed :
    X86Sem countUpLoopBody ≤ X86Lang.WellFormed :=
  Preorder.le_trans countUpLoopBody_ensures_eq_arg (ensuresEqArg_le_wellFormed 1)

/-- End-to-end `Trusted.CrateTheorem` witness for `countUpLoopBody` with
    functional specification `EnsuresEqArg 1`. -/
theorem prove_count_up_loop_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := countUpLoopBody
        specs := [EnsuresEqArg 1]
      }]
      tcb := [TCBItem.assemblerLowering fnName countUpLoopBody]
    } :=
  verify_single_fn_crate fnName countUpLoopBody (EnsuresEqArg 1)
    (countUpLoopBody_retLibInv _)
    countUpLoopBody_ensures_eq_arg

/-!
### Benchmark 2: `sumLoopBody` (2-Arg Loop Mutating Temporary Scratch Slots)

Models a 2-argument loop that accumulates `x` (`slot 2`) into `acc` (`slot 4`)
`n` (`slot 1`) times while allocating, mutating, consuming, and deallocating
multiple temporary scratch slots (`slots 5, 6, 7`) inside the loop body on every
iteration:
```rust
pub fn repeat_add(n: usize, x: usize) -> usize {
    let mut i: usize = 0;
    let mut acc: usize = 0;
    while i < n {
        let t1 = x;
        let t2 = acc + t1;
        acc = t2;
        i = i + 1;
    }
    acc
}
```
At the back-edge `jmp ⟨1⟩` of `bb3`, `canonState 8` automatically erases all
temporary `updateSlot` layers on scratch slots `5, 6, 7`, unifying the back-edge
state with `sumHeaderState tySizes n x (i + 1, acc + x)` by **`rfl`**!
-/

def sumLoopBody : X86Body where
  argTys := [.usize, .usize]
  retTy := .usize
  slotCount := 8
  blocks := [
    -- bb0 (entry: i (slot 3) := 0; acc (slot 4) := 0; jmp bb1)
    { instrs := [
        .allocSlot ⟨3⟩,
        .mov ⟨3⟩ (.imm (.word64 0)),
        .allocSlot ⟨4⟩,
        .mov ⟨4⟩ (.imm (.word64 0))
      ]
      term := .jmp ⟨1⟩ },
    -- bb1 (loop header: cond (slot 5) := i < n; jccBool cond bb2 bb3)
    { instrs := [
        .allocSlot ⟨5⟩,
        .alu .lt ⟨5⟩ (.stackSlot ⟨3⟩ false) (.stackSlot ⟨1⟩ false)
      ]
      term := .jccBool (.stackSlot ⟨5⟩ true) ⟨2⟩ ⟨3⟩ },
    -- bb2 (loop exit: ret acc)
    { instrs := [
        .deallocSlot ⟨5⟩,
        .mov ⟨0⟩ (.stackSlot ⟨4⟩ true),
        .deallocSlot ⟨4⟩,
        .deallocSlot ⟨3⟩
      ]
      term := .ret },
    -- bb3 (loop body: mutate scratch slots 6 and 7, update acc and i, jmp bb1)
    { instrs := [
        .deallocSlot ⟨5⟩,
        .allocSlot ⟨6⟩,
        .mov ⟨6⟩ (.stackSlot ⟨2⟩ false),
        .allocSlot ⟨7⟩,
        .alu .add ⟨7⟩ (.stackSlot ⟨4⟩ true) (.stackSlot ⟨6⟩ true),
        .deallocSlot ⟨6⟩,
        .mov ⟨4⟩ (.stackSlot ⟨7⟩ true),
        .deallocSlot ⟨7⟩,
        .alu .add ⟨3⟩ (.stackSlot ⟨3⟩ true) (.imm (.word64 1))
      ]
      term := .jmp ⟨1⟩ }
  ]

/-- Canonical state at loop header `bb1` of `sumLoopBody` for parameters `n`
    (slot 1), `x` (slot 2), loop counter `p.1` (slot 3), and accumulator `p.2`
    (slot 4). -/
noncomputable def sumHeaderState (tySizes : Nat → Nat) (n x : Nat)
    (p : Nat × Nat) : X86State :=
  canonState 8 {
    mem := updateSlot
      (updateSlot
        (updateSlot
          (updateSlot (fun _ => none) 1 (some (.word64 n)))
          2 (some (.word64 x)))
        3 (some (.word64 p.1)))
      4 (some (.word64 p.2))
    bb := 1
    ip := 0
    tySizes := tySizes
  }

/-- `sumLoopBody` satisfies `EnsuresRetLibInv defaultLibInv .usize pre` in 3
    lines via `byIndexedLoop` with trivial index invariant `fun _ => True`. -/
theorem sumLoopBody_retLibInv (pre : ExecQuery X86State → Prop) :
    X86Sem sumLoopBody ≤ EnsuresRetLibInv defaultLibInv .usize pre :=
  verifyUniversalDefaultRetLibInv sumLoopBody pre (fun tySizes n x =>
    byIndexedLoop 15 15 1 (sumHeaderState tySizes n x) (fun _ => True)
      ⟨(0, 0), True.intro, rfl⟩
      (fun p _ =>
        ⟨fun _ => True.intro,
         fun _ => ⟨(p.1 + 1, p.2 + x), True.intro, rfl⟩⟩))

/-- Functional postcondition for `sumLoopBody`: returns `.word64 (x * n)` for
    every runtime argument pair `(n, x)`. -/
def EnsuresProductOfArgs : X86Lang.Behavior :=
  X86Lang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      ∀ n x,
        q.init.mem 1 = some (.word64 n) →
        q.init.mem 2 = some (.word64 x) →
        ret = .word64 (x * n))

theorem sumLoopBody_ensures_product :
    X86Sem sumLoopBody ≤ EnsuresProductOfArgs :=
  verifyX86UniversalSpec sumLoopBody
    (fun s ret =>
      ∀ n x,
        s.mem 1 = some (.word64 n) →
        s.mem 2 = some (.word64 x) →
        ret = .word64 (x * n))
    (fun tySizes n x =>
      byIndexedLoop 15 15 1 (sumHeaderState tySizes n x)
        (fun p => p.1 ≤ n ∧ p.2 = x * p.1)
        ⟨(0, 0), ⟨Nat.zero_le n, (Nat.mul_zero x).symm⟩, rfl⟩
        (fun p hp =>
          ⟨fun hfalse n' x' h1 h2 => by
            have h1' : n = n' := X86Val.word64.inj (Option.some.inj h1)
            have h2' : x = x' := X86Val.word64.inj (Option.some.inj h2)
            subst h1'; subst h2'
            have hi : p.1 = n :=
              eq_of_le_of_not_lt hp.1 (of_decide_eq_false hfalse)
            exact congrArg X86Val.word64 (hp.2.trans (congrArg (x * ·) hi)),
           fun htrue =>
            ⟨(p.1 + 1, p.2 + x),
             ⟨of_decide_eq_true htrue, by
               rw [hp.2, Nat.mul_succ]⟩,
             rfl⟩⟩))

/-- End-to-end `Trusted.CrateTheorem` witness for `sumLoopBody` with functional
    specification `EnsuresProductOfArgs`. -/
theorem prove_sum_loop_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := sumLoopBody
        specs := [EnsuresProductOfArgs]
      }]
      tcb := [TCBItem.assemblerLowering fnName sumLoopBody]
    } :=
  verify_single_fn_crate fnName sumLoopBody EnsuresProductOfArgs
    (sumLoopBody_retLibInv _)
    sumLoopBody_ensures_product

/-!
### Benchmark 3: `nonZeroLoopBody` (Loop Preserving `nonZeroLibInv`)

Models a `pubSafe` function on `NonZeroUsize` (`.adt 0`) whose loop preserves
`nonZeroLibInv` (`val = .adt 0 (.word64 acc)` with `acc ≠ 0`):
```rust
pub fn bump_nonzero(x: NonZeroUsize, n: usize) -> NonZeroUsize {
    let mut i: usize = 0;
    let mut acc: usize = x.0;
    while i < n {
        acc = acc + 1;
        i = i + 1;
    }
    NonZeroUsize(acc)
}
```
-/

def nonZeroLoopBody : X86Body where
  argTys := [.adt 0, .usize]
  retTy := .adt 0
  slotCount := 6
  blocks := [
    -- bb0 (entry: i (slot 3) := 0; acc (slot 4) := x.0 (slot 1); jmp bb1)
    { instrs := [
        .allocSlot ⟨3⟩,
        .mov ⟨3⟩ (.imm (.word64 0)),
        .allocSlot ⟨4⟩,
        .extractField0 ⟨4⟩ ⟨1⟩
      ]
      term := .jmp ⟨1⟩ },
    -- bb1 (loop header: cond (slot 5) := i < n (slot 2); jccBool cond bb2 bb3)
    { instrs := [
        .allocSlot ⟨5⟩,
        .alu .lt ⟨5⟩ (.stackSlot ⟨3⟩ false) (.stackSlot ⟨2⟩ false)
      ]
      term := .jccBool (.stackSlot ⟨5⟩ true) ⟨2⟩ ⟨3⟩ },
    -- bb2 (loop exit: wrap acc into NonZeroUsize (.adt 0) and ret)
    { instrs := [
        .deallocSlot ⟨5⟩,
        .wrapAdt 0 ⟨0⟩ (.stackSlot ⟨4⟩ true),
        .deallocSlot ⟨4⟩,
        .deallocSlot ⟨3⟩
      ]
      term := .ret },
    -- bb3 (loop body: acc := acc + 1; i := i + 1; jmp bb1)
    { instrs := [
        .deallocSlot ⟨5⟩,
        .alu .add ⟨4⟩ (.stackSlot ⟨4⟩ true) (.imm (.word64 1)),
        .alu .add ⟨3⟩ (.stackSlot ⟨3⟩ true) (.imm (.word64 1))
      ]
      term := .jmp ⟨1⟩ }
  ]

noncomputable def nonZeroHeaderState (tySizes : Nat → Nat) (x n : Nat)
    (p : Nat × Nat) : X86State :=
  canonState 6 {
    mem := updateSlot
      (updateSlot
        (updateSlot
          (updateSlot (fun _ => none) 1 (some (.adt 0 (.word64 x))))
          2 (some (.word64 n)))
        3 (some (.word64 p.1)))
      4 (some (.word64 p.2))
    bb := 1
    ip := 0
    tySizes := tySizes
  }

def nonZeroLoopFn (fnName : String) : CapturedFn where
  name := fnName
  prog := nonZeroLoopBody
  kind := .pubSafe True
  specs := []

/-- `nonZeroLoopFn` preserves `nonZeroLibInv` (`acc ≠ 0`) across an unbounded
    number of loop iterations via `byIndexedLoop`. -/
theorem nonZeroLoopFn_retLibInv (fnName : String) :
    X86Sem (nonZeroLoopFn fnName).prog ≤
      EnsuresRetLibInv nonZeroLibInv (nonZeroLoopFn fnName).prog.retTy
        ((nonZeroLoopFn fnName).effectivePre nonZeroLibInv) :=
  verifyUniversalPubSafeRetLibInv nonZeroLibInv (nonZeroLoopFn fnName) True rfl
    (fun tySizes _ _ x n hlib =>
      byIndexedLoop 10 10 1 (nonZeroHeaderState tySizes x n)
        (fun p => p.2 ≠ 0)
        ⟨(0, x), hlib.1, rfl⟩
        (fun p hp =>
          ⟨fun _ => hp,
           fun _ => ⟨(p.1 + 1, p.2 + 1), Nat.succ_ne_zero p.2, rfl⟩⟩))

/-- End-to-end `Trusted.CrateTheorem` for `nonZeroLoopFn` under
    `nonZeroAdtDecl` and `nonZeroLibInv`. -/
theorem prove_non_zero_loop_crate (fnName : String) :
    CrateTheorem {
      adts := [nonZeroAdtDecl]
      libInv := nonZeroLibInv
      functions := [nonZeroLoopFn fnName]
      tcb := [TCBItem.assemblerLowering fnName nonZeroLoopBody]
    } := by
  refine ⟨(by intro h; cases h), nonZeroLibInv_admissible, True.intro, ?_⟩
  refine ⟨⟨⟨True.intro, True.intro⟩, ?_⟩, True.intro⟩
  intro hTcb
  exact Compiler.Verified.with_wellFormedOn
    (Compiler.SoundOn.verify hTcb.1 (nonZeroLoopFn_retLibInv fnName))
    (ensuresRetLibInv_le_wellFormedOn _ _ _)
    hTcb.1.1

/-!
### Benchmark 4: `loopWithInternalDiamondBody` (Loop with Internal Diamond)

Models a loop whose body contains a data-dependent `if`/`else` branch where the
two branches allocate, mutate, and deallocate **different** temporary scratch
slots (`slot 6` in `bb4` vs. `slots 7, 8` in `bb5`) before jumping back to loop
header `bb1`:
```rust
pub fn count_weighted(n: usize, k: usize) -> usize {
    let mut i: usize = 0;
    let mut acc: usize = 0;
    while i < n {
        if i < k {
            let t1 = 1;
            let t2 = t1 + 1;
            acc = acc + t2;
        } else {
            let t0 = 1;
            acc = acc + t0;
        }
        i = i + 1;
    }
    acc
}
```
At both back-edges (`bb4 -> bb1` and `bb5 -> bb1`), `canonState 9` erases the
branch-specific temporary scratch history (`slot 6` vs. `slots 7, 8`), so both
branches unify with `sumHeaderState9 tySizes n k` by **`rfl`**!
-/

def loopWithInternalDiamondBody : X86Body where
  argTys := [.usize, .usize]
  retTy := .usize
  slotCount := 9
  blocks := [
    -- bb0 (entry: i (slot 3) := 0; acc (slot 4) := 0; jmp bb1)
    { instrs := [
        .allocSlot ⟨3⟩,
        .mov ⟨3⟩ (.imm (.word64 0)),
        .allocSlot ⟨4⟩,
        .mov ⟨4⟩ (.imm (.word64 0))
      ]
      term := .jmp ⟨1⟩ },
    -- bb1 (loop header: cond (slot 5) := i < n (slot 1); jccBool cond bb2 bb3)
    { instrs := [
        .allocSlot ⟨5⟩,
        .alu .lt ⟨5⟩ (.stackSlot ⟨3⟩ false) (.stackSlot ⟨1⟩ false)
      ]
      term := .jccBool (.stackSlot ⟨5⟩ true) ⟨2⟩ ⟨3⟩ },
    -- bb2 (loop exit: ret acc)
    { instrs := [
        .deallocSlot ⟨5⟩,
        .mov ⟨0⟩ (.stackSlot ⟨4⟩ true),
        .deallocSlot ⟨4⟩,
        .deallocSlot ⟨3⟩
      ]
      term := .ret },
    -- bb3 (loop body branch: b (slot 5) := i < k (slot 2); jccBool b bb4 bb5)
    { instrs := [
        .deallocSlot ⟨5⟩,
        .allocSlot ⟨5⟩,
        .alu .lt ⟨5⟩ (.stackSlot ⟨3⟩ false) (.stackSlot ⟨2⟩ false)
      ]
      term := .jccBool (.stackSlot ⟨5⟩ true) ⟨4⟩ ⟨5⟩ },
    -- bb4 (false branch: i >= k; uses slot 6; acc += 1; i += 1; jmp bb1)
    { instrs := [
        .deallocSlot ⟨5⟩,
        .allocSlot ⟨6⟩,
        .mov ⟨6⟩ (.imm (.word64 1)),
        .alu .add ⟨4⟩ (.stackSlot ⟨4⟩ true) (.stackSlot ⟨6⟩ true),
        .deallocSlot ⟨6⟩,
        .alu .add ⟨3⟩ (.stackSlot ⟨3⟩ true) (.imm (.word64 1))
      ]
      term := .jmp ⟨1⟩ },
    -- bb5 (true branch: i < k; uses slots 7 & 8; acc += 2; i += 1; jmp bb1)
    { instrs := [
        .deallocSlot ⟨5⟩,
        .allocSlot ⟨7⟩,
        .mov ⟨7⟩ (.imm (.word64 1)),
        .allocSlot ⟨8⟩,
        .alu .add ⟨8⟩ (.stackSlot ⟨7⟩ true) (.imm (.word64 1)),
        .deallocSlot ⟨7⟩,
        .alu .add ⟨4⟩ (.stackSlot ⟨4⟩ true) (.stackSlot ⟨8⟩ true),
        .deallocSlot ⟨8⟩,
        .alu .add ⟨3⟩ (.stackSlot ⟨3⟩ true) (.imm (.word64 1))
      ]
      term := .jmp ⟨1⟩ }
  ]

noncomputable def weightedLoopHeaderState (tySizes : Nat → Nat) (n k : Nat)
    (p : Nat × Nat) : X86State :=
  canonState 9 {
    mem := updateSlot
      (updateSlot
        (updateSlot
          (updateSlot (fun _ => none) 1 (some (.word64 n)))
          2 (some (.word64 k)))
        3 (some (.word64 p.1)))
      4 (some (.word64 p.2))
    bb := 1
    ip := 0
    tySizes := tySizes
  }

/-- `loopWithInternalDiamondBody` verified for `EnsuresRetLibInv` in 5 lines:
    both internal loop branches (`bb4` and `bb5`) normalize back to
    `weightedLoopHeaderState` at `bb1` by `rfl`. -/
theorem loopWithInternalDiamondBody_retLibInv
    (pre : ExecQuery X86State → Prop) :
    X86Sem loopWithInternalDiamondBody ≤
      EnsuresRetLibInv defaultLibInv .usize pre :=
  verifyUniversalDefaultRetLibInv loopWithInternalDiamondBody pre
    (fun tySizes n k =>
      byIndexedLoop 20 20 1 (weightedLoopHeaderState tySizes n k)
        (fun _ => True)
        ⟨(0, 0), True.intro, rfl⟩
        (fun p _ =>
          ⟨fun _ => True.intro,
           fun _ =>
            ⟨fun _ => ⟨(p.1 + 1, p.2 + 1), True.intro, rfl⟩,
             fun _ => ⟨(p.1 + 1, p.2 + 2), True.intro, rfl⟩⟩⟩))

/-- Functional postcondition for `loopWithInternalDiamondBody`: `ret ≥ n` (since
    each of the `n` iterations adds at least `1` to `acc`). -/
def EnsuresGeArg1 : X86Lang.Behavior :=
  X86Lang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      ∀ n, q.init.mem 1 = some (.word64 n) →
        ∃ m, ret = .word64 m ∧ n ≤ m)

theorem loopWithInternalDiamondBody_ensures_ge :
    X86Sem loopWithInternalDiamondBody ≤ EnsuresGeArg1 :=
  verifyX86UniversalSpec loopWithInternalDiamondBody
    (fun s ret =>
      ∀ n, s.mem 1 = some (.word64 n) →
        ∃ m, ret = .word64 m ∧ n ≤ m)
    (fun tySizes n k =>
      byIndexedLoop 20 20 1 (weightedLoopHeaderState tySizes n k)
        (fun p => p.1 ≤ n ∧ p.1 ≤ p.2)
        ⟨(0, 0), ⟨Nat.zero_le n, Nat.le_refl 0⟩, rfl⟩
        (fun p hp =>
          ⟨fun hfalse n' h1 => by
            have hn : n = n' := X86Val.word64.inj (Option.some.inj h1)
            subst hn
            have hi : p.1 = n :=
              eq_of_le_of_not_lt hp.1 (of_decide_eq_false hfalse)
            exact ⟨p.2, rfl, hi ▸ hp.2⟩,
           fun htrue =>
            ⟨fun _ =>
              ⟨(p.1 + 1, p.2 + 1),
               ⟨of_decide_eq_true htrue, Nat.succ_le_succ hp.2⟩,
               rfl⟩,
             fun _ =>
              ⟨(p.1 + 1, p.2 + 2),
               ⟨of_decide_eq_true htrue,
                Nat.le_trans (Nat.succ_le_succ hp.2) (Nat.le_succ (p.2 + 1))⟩,
               rfl⟩⟩⟩))

/-- End-to-end `Trusted.CrateTheorem` witness for `loopWithInternalDiamondBody`
    with functional specification `EnsuresGeArg1`. -/
theorem prove_loop_with_internal_diamond_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := loopWithInternalDiamondBody
        specs := [EnsuresGeArg1]
      }]
      tcb := [TCBItem.assemblerLowering fnName loopWithInternalDiamondBody]
    } :=
  verify_single_fn_crate fnName loopWithInternalDiamondBody EnsuresGeArg1
    (loopWithInternalDiamondBody_retLibInv _)
    loopWithInternalDiamondBody_ensures_ge

/-!
## 7. Concrete Verified $O(D)$ Diamond-Join Benchmarks

We now demonstrate that `byExactCut` and `byIndexedCut` eliminate the $O(2^D)$
diamond path explosion identified in Round 1 Cluster C (`REPORT.md` §5.2):
1. **`asymmetricDiamondJoinBody`**: Two branches (`bb1` and `bb2`) allocate,
   write, and deallocate **different** temporary scratch slots (`slot 4` vs.
   `slots 5, 6`) before jumping to `bb3`. Because `wpX86Cut` applies
   `canonState body.slotCount` at `bb3`, both branches normalize to the exact
   same canonical join state (`rfl`) or indexed join state, allowing the
   post-join continuation `bb3` to be verified **once**.
2. **`doubleDiamondChainBody`**: A 2-stage chained diamond CFG
   (`bb0 -> (bb1 | bb2) -> bb3 -> (bb4 | bb5) -> bb6`) with data-dependent
   branches and distinct temporary scratch slots in every branch. Instead of
   exploring $2 \times 2 = 4$ end-to-end paths ($O(2^D)$), `byIndexedCut` stages
   cut-point `bb3` and cut-point `bb6` sequentially ($O(D)$), verifying each
   diamond stage once.
-/

def asymmetricDiamondJoinBody : X86Body where
  argTys := [.bool, .usize]
  retTy := .usize
  slotCount := 7
  blocks := [
    -- bb0 (entry: allocate local y in slot 3, branch on b (slot 1) to bb1/bb2)
    { instrs := [
        .allocSlot ⟨3⟩
      ]
      term := .jccBool (.stackSlot ⟨1⟩ true) ⟨1⟩ ⟨2⟩ },
    -- bb1 (false branch: consumes x (slot 2) via scratch slot 4, sets y := 10)
    { instrs := [
        .allocSlot ⟨4⟩,
        .mov ⟨4⟩ (.stackSlot ⟨2⟩ true),
        .deallocSlot ⟨4⟩,
        .mov ⟨3⟩ (.imm (.word64 10))
      ]
      term := .jmp ⟨3⟩ },
    -- bb2 (true branch: consumes x (slot 2), uses slots 5 & 6, sets y := 10)
    { instrs := [
        .allocSlot ⟨5⟩,
        .mov ⟨5⟩ (.stackSlot ⟨2⟩ true),
        .deallocSlot ⟨5⟩,
        .allocSlot ⟨5⟩,
        .mov ⟨5⟩ (.imm (.word64 5)),
        .allocSlot ⟨6⟩,
        .alu .add ⟨6⟩ (.stackSlot ⟨5⟩ true) (.imm (.word64 5)),
        .deallocSlot ⟨5⟩,
        .mov ⟨3⟩ (.stackSlot ⟨6⟩ true),
        .deallocSlot ⟨6⟩
      ]
      term := .jmp ⟨3⟩ },
    -- bb3 (join block: verified ONCE despite asymmetric scratch in bb1/bb2)
    { instrs := [
        .alu .add ⟨0⟩ (.stackSlot ⟨3⟩ true) (.imm (.word64 32)),
        .deallocSlot ⟨3⟩
      ]
      term := .ret }
  ]

/-- Canonical state at join block `bb3` of `asymmetricDiamondJoinBody`: both
    `bb1` (which touched scratch slot 4) and `bb2` (which touched scratch slots
    5 and 6) normalize via `canonState 7` to this **identical** canonical state
    by `rfl`! -/
noncomputable def asymmetricJoinState (tySizes : Nat → Nat) : X86State :=
  canonState 7 {
    mem := updateSlot (fun _ => none) 3 (some (.word64 10))
    bb := 3
    ip := 0
    tySizes := tySizes
  }

/-- `asymmetricDiamondJoinBody` verified in $O(1)$ continuation work using
    `byExactCut`: both branches of the diamond reduce to `asymmetricJoinState`
    by `rfl`, and `bb3` is symbolically executed only once. -/
theorem asymmetricDiamondJoinBody_ensures :
    X86Sem asymmetricDiamondJoinBody ≤
      X86Lang.Spec (fun _ out =>
        ∀ ret, out.outcome = .terminated (.normal ret) → ret = .word64 42) :=
  verifyX86UniversalSpec asymmetricDiamondJoinBody
    (fun _ ret => ret = .word64 42)
    (fun tySizes _ _ =>
      byExactCut 15 3 (asymmetricJoinState tySizes)
        ⟨fun _ => rfl, fun _ => rfl⟩
        (byWpX86 10 rfl))

theorem asymmetricDiamondJoinBody_retLibInv (pre : ExecQuery X86State → Prop) :
    X86Sem asymmetricDiamondJoinBody ≤
      EnsuresRetLibInv defaultLibInv .usize pre :=
  verifyUniversalDefaultRetLibInv asymmetricDiamondJoinBody pre
    (fun tySizes _ _ =>
      byExactCut 15 3 (asymmetricJoinState tySizes)
        ⟨fun _ => rfl, fun _ => rfl⟩
        (byWpX86 10 True.intro))

/-- 2-stage chained data-dependent diamond CFG:
    - Stage 1 (`bb0 -> (bb1 | bb2) -> bb3`): tests `x < 10`, writes `y`
      (`slot 2`) while mutating distinct scratch slots (`slot 4` in `bb1`,
      `slots 5, 6` in `bb2`), and joins at cut-point `bb3`.
    - Stage 2 (`bb3 -> (bb4 | bb5) -> bb6`): tests `y < 20`, writes `z`
      (`slot 3`) while mutating distinct scratch slots (`slot 5` in `bb4`,
      `slot 6` in `bb5`), and joins at cut-point `bb6`.
    - Tail (`bb6`): computes `ret := z + 1` and returns. -/
def doubleDiamondChainBody : X86Body where
  argTys := [.usize]
  retTy := .usize
  slotCount := 7
  blocks := [
    -- bb0 (entry: allocate y (slot 2) and cond1 (slot 4 := x < 10))
    { instrs := [
        .allocSlot ⟨2⟩,
        .allocSlot ⟨4⟩,
        .alu .lt ⟨4⟩ (.stackSlot ⟨1⟩ false) (.imm (.word64 10))
      ]
      term := .jccBool (.stackSlot ⟨4⟩ true) ⟨1⟩ ⟨2⟩ },
    -- bb1 (stage 1 false: x >= 10; uses scratch slot 5; sets y := x)
    { instrs := [
        .deallocSlot ⟨4⟩,
        .allocSlot ⟨5⟩,
        .mov ⟨5⟩ (.stackSlot ⟨1⟩ true),
        .mov ⟨2⟩ (.stackSlot ⟨5⟩ true),
        .deallocSlot ⟨5⟩
      ]
      term := .jmp ⟨3⟩ },
    -- bb2 (stage 1 true: x < 10; uses scratch slots 5, 6; sets y := x + 10)
    { instrs := [
        .deallocSlot ⟨4⟩,
        .allocSlot ⟨5⟩,
        .mov ⟨5⟩ (.stackSlot ⟨1⟩ true),
        .allocSlot ⟨6⟩,
        .alu .add ⟨6⟩ (.stackSlot ⟨5⟩ true) (.imm (.word64 10)),
        .deallocSlot ⟨5⟩,
        .mov ⟨2⟩ (.stackSlot ⟨6⟩ true),
        .deallocSlot ⟨6⟩
      ]
      term := .jmp ⟨3⟩ },
    -- bb3 (join 1: allocate z (slot 3) and cond2 (slot 4 := y < 20))
    { instrs := [
        .allocSlot ⟨3⟩,
        .allocSlot ⟨4⟩,
        .alu .lt ⟨4⟩ (.stackSlot ⟨2⟩ false) (.imm (.word64 20))
      ]
      term := .jccBool (.stackSlot ⟨4⟩ true) ⟨4⟩ ⟨5⟩ },
    -- bb4 (stage 2 false: y >= 20; uses scratch slot 5; sets z := y)
    { instrs := [
        .deallocSlot ⟨4⟩,
        .allocSlot ⟨5⟩,
        .mov ⟨5⟩ (.stackSlot ⟨2⟩ true),
        .mov ⟨3⟩ (.stackSlot ⟨5⟩ true),
        .deallocSlot ⟨5⟩
      ]
      term := .jmp ⟨6⟩ },
    -- bb5 (stage 2 true: y < 20; uses scratch slot 6; sets z := y + 20)
    { instrs := [
        .deallocSlot ⟨4⟩,
        .allocSlot ⟨6⟩,
        .alu .add ⟨6⟩ (.stackSlot ⟨2⟩ true) (.imm (.word64 20)),
        .mov ⟨3⟩ (.stackSlot ⟨6⟩ true),
        .deallocSlot ⟨6⟩
      ]
      term := .jmp ⟨6⟩ },
    -- bb6 (join 2: ret := z + 1)
    { instrs := [
        .alu .add ⟨0⟩ (.stackSlot ⟨3⟩ true) (.imm (.word64 1)),
        .deallocSlot ⟨3⟩
      ]
      term := .ret }
  ]

/-- Canonical state at the first join point `bb3` of `doubleDiamondChainBody`,
    parameterized by the joined value `y` in slot 2. -/
noncomputable def diamondStage1JoinState (tySizes : Nat → Nat) (y : Nat) :
    X86State :=
  canonState 7 {
    mem := updateSlot (fun _ => none) 2 (some (.word64 y))
    bb := 3
    ip := 0
    tySizes := tySizes
  }

/-- Canonical state at the second join point `bb6` of `doubleDiamondChainBody`,
    parameterized by the joined value `z` in slot 3. -/
noncomputable def diamondStage2JoinState (tySizes : Nat → Nat) (z : Nat) :
    X86State :=
  canonState 7 {
    mem := updateSlot (fun _ => none) 3 (some (.word64 z))
    bb := 6
    ip := 0
    tySizes := tySizes
  }

/-- $O(D)$ staged verification of `doubleDiamondChainBody` for
    `EnsuresRetLibInv`: each diamond stage (`bb0 -> bb3`, `bb3 -> bb6`, and
    `bb6 -> ret`) is symbolically executed **once** via `byIndexedCut` rather
    than enumerating $2^2 = 4$ end-to-end paths. -/
theorem doubleDiamondChainBody_retLibInv (pre : ExecQuery X86State → Prop) :
    X86Sem doubleDiamondChainBody ≤
      EnsuresRetLibInv defaultLibInv .usize pre :=
  verifyUniversalDefaultRetLibInv doubleDiamondChainBody pre (fun tySizes x =>
    -- Stage 1: bb0 -> (bb1 | bb2) -> cut-point bb3
    byIndexedCut 15 3 (diamondStage1JoinState tySizes) (fun _ => True)
      ⟨fun _ => ⟨x, True.intro, rfl⟩,
       fun _ => ⟨x + 10, True.intro, rfl⟩⟩
      (fun y _ =>
        -- Stage 2: bb3 -> (bb4 | bb5) -> cut-point bb6 (verified ONCE!)
        byIndexedCut 15 6 (diamondStage2JoinState tySizes) (fun _ => True)
          ⟨fun _ => ⟨y, True.intro, rfl⟩,
           fun _ => ⟨y + 20, True.intro, rfl⟩⟩
          (fun _ _ =>
            -- Stage 3: bb6 -> ret (verified ONCE for all z!)
            byWpX86 10 True.intro)))

/-- $O(D)$ staged verification of a Strengthened Functional Postcondition on
    `doubleDiamondChainBody` (`ret = .word64 z` with `z > 20`):
    - Stage 1 establishes `y ≥ 10` at join point `bb3`,
    - Stage 2 establishes `z ≥ 20` at join point `bb6` (verified once for
      arbitrary `y ≥ 10`),
    - Stage 3 establishes `z + 1 > 20` at `ret` (verified once for arbitrary
      `z ≥ 20`). -/
def EnsuresGt20 : X86Lang.Behavior :=
  X86Lang.Spec (fun _ out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      ∃ k, ret = .word64 k ∧ k > 20)

theorem doubleDiamondChainBody_ensures_gt20 :
    X86Sem doubleDiamondChainBody ≤ EnsuresGt20 :=
  verifyX86UniversalSpec doubleDiamondChainBody
    (fun _ ret => ∃ k, ret = .word64 k ∧ k > 20)
    (fun tySizes x =>
      -- Stage 1: bb0 -> cut-point bb3 with invariant `y ≥ 10`
      byIndexedCut 15 3 (diamondStage1JoinState tySizes) (fun y => y ≥ 10)
        ⟨fun hfalse => ⟨x, Nat.le_of_not_lt (of_decide_eq_false hfalse), rfl⟩,
         fun _ => ⟨x + 10, Nat.le_add_left 10 x, rfl⟩⟩
        (fun y _ =>
          -- Stage 2: bb3 -> cut-point bb6 with invariant `z ≥ 20`
          byIndexedCut 15 6 (diamondStage2JoinState tySizes) (fun z => z ≥ 20)
            ⟨fun hfalse => ⟨y, Nat.le_of_not_lt (of_decide_eq_false hfalse), rfl⟩,
             fun _ => ⟨y + 20, Nat.le_add_left 20 y, rfl⟩⟩
            (fun z hz =>
              -- Stage 3: bb6 -> ret (`z + 1 > 20`)
              byWpX86 10 ⟨z + 1, rfl, Nat.lt_of_lt_of_le (by decide) (Nat.succ_le_succ hz)⟩)))

/-- End-to-end `Trusted.CrateTheorem` witness for `doubleDiamondChainBody` with
    functional specification `EnsuresGt20`. -/
theorem prove_double_diamond_chain_crate (fnName : String) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := doubleDiamondChainBody
        specs := [EnsuresGt20]
      }]
      tcb := [TCBItem.assemblerLowering fnName doubleDiamondChainBody]
    } :=
  verify_single_fn_crate fnName doubleDiamondChainBody EnsuresGt20
    (doubleDiamondChainBody_retLibInv _)
    doubleDiamondChainBody_ensures_gt20

end Anneal.LoopAndJoinVCGen

