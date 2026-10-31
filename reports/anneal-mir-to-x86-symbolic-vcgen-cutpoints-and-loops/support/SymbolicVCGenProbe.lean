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
# Syntax-Directed Symbolic Execution & VCgen Probe (`SymbolicVCGenProbe.lean`)

This module implements and kernel-checks a universal, fuel-bounded weakest
precondition (`wpX86`) and normal-termination necessity (`necX86Normal`)
generator for `Trusted.X86Body`, paired with a canonical initial-memory theorem
(`initX86State_canonical`) that eliminates per-statement tactical stepping and
hardcoded AST templates in `theory/Anneal/`.
-/

namespace Anneal.SymbolicVCGen

open Trusted
open Anneal

/-!
## 1. Canonical Stack-Frame Memory (`canonicalMem`) and Entry-State Equivalence

In `Trusted.initX86State`, initial stack memory `s.mem : Nat → Option X86Val`
is specified existentially via `argsMatchStack`: slot `0` is `none`, slots
`1 ..= argTys.length` hold type-valid `X86Val` arguments, and slots
`> argTys.length` are `none`.

If symbolic execution steps directly on an abstract `s.mem`, every load from a
parameter slot requires a manual `rw [hv_i]` tactic. Instead, we prove by
`funext` that `s.mem` is definitionally equal to a concrete nested `updateSlot`
chain (`forallTypedArgsAux`), and that every `X86Ty` in `body.argTys` determines
the head constructor of its `X86Val` (`word64`, `boolVal`, `unit`, `adt`,
`bytes`, `stackPtr`). Once `s` is replaced by its canonical form, `evalX86Step`
and `wpX86` reduce across the entire function body by kernel `whnf` / `rfl`.
-/

/-- Build a canonical stack memory map starting at slot `k` from `args`. -/
noncomputable def canonicalMemFrom (k : Nat) (args : List X86Val)
    (acc : Nat → Option X86Val) : Nat → Option X86Val :=
  match args with
  | [] => acc
  | v :: vs => canonicalMemFrom (k + 1) vs (updateSlot acc k (some v))

/-- Canonical stack memory map for function entry arguments `args` in slots
    `1 ..= args.length`, with all other slots `none`. -/
noncomputable def canonicalMem (args : List X86Val) : Nat → Option X86Val :=
  canonicalMemFrom 1 args (fun _ => none)

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

/-- Explicit 0-argument canonical memory equality (`s.mem = canonicalMem []`). -/
theorem mem_eq_canonical0 {mem : Nat → Option X86Val}
    (h0 : mem 0 = none)
    (hrest : ∀ j, 1 ≤ j → mem j = none) :
    mem = canonicalMem [] := by
  funext i
  cases i with
  | zero => exact h0
  | succ i1 => exact hrest (i1 + 1) (Nat.succ_le_succ (Nat.zero_le i1))

/-- Explicit 1-argument canonical memory equality
    (`s.mem = canonicalMem [v1]`). -/
theorem mem_eq_canonical1 {mem : Nat → Option X86Val} {v1 : X86Val}
    (h0 : mem 0 = none)
    (h1 : mem 1 = some v1)
    (hrest : ∀ j, 2 ≤ j → mem j = none) :
    mem = canonicalMem [v1] := by
  funext i
  cases i with
  | zero => exact h0
  | succ i1 =>
    cases i1 with
    | zero => exact h1
    | succ i2 => exact hrest (i2 + 2) (Nat.le_add_left 2 i2)

/-- Explicit 2-argument canonical memory equality
    (`s.mem = canonicalMem [v1, v2]`). -/
theorem mem_eq_canonical2 {mem : Nat → Option X86Val} {v1 v2 : X86Val}
    (h0 : mem 0 = none)
    (h1 : mem 1 = some v1)
    (h2 : mem 2 = some v2)
    (hrest : ∀ j, 3 ≤ j → mem j = none) :
    mem = canonicalMem [v1, v2] := by
  funext i
  cases i with
  | zero => exact h0
  | succ i1 =>
    cases i1 with
    | zero => exact h1
    | succ i2 =>
      cases i2 with
      | zero => exact h2
      | succ i3 => exact hrest (i3 + 3) (Nat.le_add_left 3 i3)

/-- Explicit 3-argument canonical memory equality
    (`s.mem = canonicalMem [v1, v2, v3]`). -/
theorem mem_eq_canonical3 {mem : Nat → Option X86Val} {v1 v2 v3 : X86Val}
    (h0 : mem 0 = none)
    (h1 : mem 1 = some v1)
    (h2 : mem 2 = some v2)
    (h3 : mem 3 = some v3)
    (hrest : ∀ j, 4 ≤ j → mem j = none) :
    mem = canonicalMem [v1, v2, v3] := by
  funext i
  cases i with
  | zero => exact h0
  | succ i1 =>
    cases i1 with
    | zero => exact h1
    | succ i2 =>
      cases i2 with
      | zero => exact h2
      | succ i3 =>
        cases i3 with
        | zero => exact h3
        | succ i4 => exact hrest (i4 + 4) (Nat.le_add_left 4 i4)

/-- Computable quantifier telescope over typed entry arguments starting at stack
    slot `k`. Each `X86Ty` constructor introduces the exact typed payload of its
    canonical `X86Val` and updates slot `k` in `acc`. -/
noncomputable def forallTypedArgsAux (tySizes : Nat → Nat) (k : Nat) (argTys : List X86Ty)
    (acc : Nat → Option X86Val) (P : (Nat → Option X86Val) → Prop) : Prop :=
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

/-- Top-level entry-argument quantifier telescope starting at slot `1` from an
    empty stack frame (`fun _ => none`). -/
noncomputable def forallTypedArgs (tySizes : Nat → Nat) (argTys : List X86Ty)
    (P : (Nat → Option X86Val) → Prop) : Prop :=
  forallTypedArgsAux tySizes 1 argTys (fun _ => none) P

/-- Universal soundness of `forallTypedArgsAux` for arbitrary `argTys : List
    X86Ty`. -/
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

/-- Universal entry-state canonicalization theorem: any property `P s` of an
    initial state `s` satisfying `initX86State body s` reduces to proving `P`
    over the canonical `updateSlot` memory generated by `forallTypedArgs`. -/
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

/-- Quantifier-free unfolding of `argsSatisfyLibInv` that reduces by `rfl` when
    applied to a canonical `updateSlot` memory map. -/
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
## 2. Syntax-Directed Weakest Precondition (`wpX86`) and Soundness (`wpX86_sound`)
-/

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

/-- Fuel-bounded, syntax-directed weakest precondition generator for
    `Trusted.X86Body`. -/
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

/-- Universal soundness theorem for `wpX86`: if `wpX86 fuel body s P` holds,
    every finite execution prefix reachable from `s` is free of UB/stuck states
    and satisfies `P` on normal termination. -/
theorem wpX86_sound (fuel : Nat) (body : X86Body) (init s : X86State)
    (P : X86Val → Prop) (hwp : wpX86 fuel body s P) :
    ∀ (n : Nat) (tr : List Unit) (out : PrefixOutcome X86Val),
      ReachesPrefix X86Machine body init n s tr out →
      SafeAndEnsures P out := by
  induction fuel generalizing s with
  | zero =>
    cases hwp
  | succ fuel' ih =>
    intro n tr out hreach
    dsimp [wpX86] at hwp
    cases hblk : (s.curBody.getD body).blocks[s.bb]? with
    | none =>
      rw [hblk] at hwp
      cases hwp
    | some blk =>
      rw [hblk] at hwp
      dsimp at hwp
      cases hinstr : blk.instrs[s.ip]? with
      | some instr =>
        rw [hinstr] at hwp
        dsimp at hwp
        have hstep_eq : evalX86Step body s = evalX86Instr s instr := by
          dsimp [evalX86Step]
          rw [hblk]
          dsimp
          rw [hinstr]
        cases hres : evalX86Instr s instr with
        | step obs s' =>
          cases obs
          rw [hres] at hwp hstep_eq
          exact reachesPrefix_safeAndEnsures_of_step hstep_eq hreach
            (fun n' tr' hr' => ih s' hwp n' tr' out hr')
        | terminated term =>
          cases term with
          | normal v =>
            rw [hres] at hwp hstep_eq
            exact reachesPrefix_safeAndEnsures_of_normal hstep_eq hreach hwp
          | unwind =>
            rw [hres] at hstep_eq
            exact reachesPrefix_safeAndEnsures_of_unwind hstep_eq hreach
        | failed _ =>
          rw [hres] at hwp
          cases hwp
        | choice _ _ =>
          rw [hres] at hwp
          cases hwp
      | none =>
        rw [hinstr] at hwp
        dsimp at hwp
        have hstep_eq : evalX86Step body s = evalX86Term s blk.term := by
          dsimp [evalX86Step]
          rw [hblk]
          dsimp
          rw [hinstr]
        cases hterm : blk.term with
        | jccBool cond falseTarget trueTarget =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hcond : evalX86Operand s.mem cond with
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
                      evalX86Step body s =
                        .step () { s with mem := mem', bb := falseTarget.index, ip := 0 } := by
                    rw [hstep_eq]
                    dsimp [evalX86Term]
                    rw [hcond]
                  exact reachesPrefix_safeAndEnsures_of_step hstep_false hreach
                    (fun n' tr' hr' => ih _ (hwp.1 rfl) n' tr' out hr')
                | true =>
                  have hstep_true :
                      evalX86Step body s =
                        .step () { s with mem := mem', bb := trueTarget.index, ip := 0 } := by
                    rw [hstep_eq]
                    dsimp [evalX86Term]
                    rw [hcond]
                  exact reachesPrefix_safeAndEnsures_of_step hstep_true hreach
                    (fun n' tr' hr' => ih _ (hwp.2 rfl) n' tr' out hr')
              | word64 _ | unit | adt _ _ | bytes _ _ | stackPtr _ =>
                rw [hcond] at hwp
                cases hwp
        | repMovsbJmp dst srcTy dstTy ptrOp target =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hptr : evalX86Operand s.mem ptrOp with
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
                        evalX86TyByteSize s.tySizes srcTy =
                          evalX86TyByteSize s.tySizes dstTy := hwp.1
                    have hv_eq :
                        vSz = evalX86TyByteSize s.tySizes srcTy := hwp.2.1
                    have hwp_next := hwp.2.2
                    have hdec1 :
                        decide (evalX86TyByteSize s.tySizes srcTy =
                          evalX86TyByteSize s.tySizes dstTy) = true :=
                      decide_eq_true hsrc_eq
                    have hdec2 :
                        decide (vSz = evalX86TyByteSize s.tySizes srcTy) = true :=
                      decide_eq_true hv_eq
                    have hstep_rep :
                        evalX86Step body s =
                          .step () {
                            s with
                            mem := updateSlot mem' dst.index
                              (some (.bytes (evalX86TyByteSize s.tySizes dstTy) bits))
                            bb := target.index
                            ip := 0
                          } := by
                      rw [hstep_eq]
                      dsimp [evalX86Term, evalRepMovsb]
                      rw [hptr]
                      dsimp
                      rw [hdec1]
                      dsimp
                      rw [hslot]
                      dsimp
                      rw [hdec2]
                      rfl
                    exact reachesPrefix_safeAndEnsures_of_step hstep_rep hreach
                      (fun n' tr' hr' => ih _ hwp_next n' tr' out hr')
                  | word64 _ | boolVal _ | unit | adt _ _ | stackPtr _ =>
                    rw [hslot] at hwp
                    cases hwp
              | word64 _ | boolVal _ | unit | adt _ _ | bytes _ _ =>
                rw [hptr] at hwp
                cases hwp
        | ret | jmp _ | ud2 | abortPanic | movSizeOfJmp _ _ _ | call1 _ _ _ _ =>
          rw [hterm] at hwp hstep_eq
          dsimp at hwp
          cases hres : evalX86Term s blk.term with
          | step obs s' =>
            cases obs
            rw [hterm] at hres
            rw [hres] at hwp hstep_eq
            exact reachesPrefix_safeAndEnsures_of_step hstep_eq hreach
              (fun n' tr' hr' => ih s' hwp n' tr' out hr')
          | terminated term =>
            cases term with
            | normal v =>
              rw [hterm] at hres
              rw [hres] at hwp hstep_eq
              exact reachesPrefix_safeAndEnsures_of_normal hstep_eq hreach hwp
            | unwind =>
              rw [hterm] at hres
              rw [hres] at hstep_eq
              exact reachesPrefix_safeAndEnsures_of_unwind hstep_eq hreach
          | failed _ =>
            rw [hterm] at hres
            rw [hres] at hwp
            cases hwp
          | choice _ _ =>
            rw [hterm] at hres
            rw [hres] at hwp
            cases hwp

/-!
## 3. Dual Normal-Termination Necessity Evaluator (`necX86Normal`) for CTFE/PME
-/

theorem reachesPrefix_normal_of_step
    {body : X86Body} {init s s' : X86State} {n : Nat} {tr : List Unit}
    {v : X86Val} {Q : X86Val → Prop}
    (hstep : evalX86Step body s = .step () s')
    (hreach : ReachesPrefix X86Machine body init n s tr (.terminated (.normal v)))
    (hnext : ∀ n' tr',
      ReachesPrefix X86Machine body init n' s' tr' (.terminated (.normal v)) →
      Q v) :
    Q v := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun => cases hrun
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_normal_of_failed
    {body : X86Body} {init s : X86State} {n : Nat} {tr : List Unit}
    {err : FailureKind} {v : X86Val}
    (hstep : evalX86Step body s = .failed err)
    (hreach : ReachesPrefix X86Machine body init n s tr (.terminated (.normal v))) :
    False := by
  cases hreach with
  | step _ _ _ _ _ _ h1 _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | choice _ _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = evalX86Step body s := h1
    rw [hstep] at h1'; cases h1'

/-- Dual symbolic necessity evaluator: computes a sufficient condition for every
    normal termination `.terminated (.normal v)` reachable from `s` to satisfy
    `Q v`. -/
noncomputable def necX86Normal (fuel : Nat) (rootBody : X86Body) (s : X86State)
    (Q : X86Val → Prop) : Prop :=
  match fuel with
  | 0 => False
  | fuel' + 1 =>
    let active := s.curBody.getD rootBody
    match active.blocks[s.bb]? with
    | none => True
    | some blk =>
      match blk.instrs[s.ip]? with
      | some instr =>
        match evalX86Instr s instr with
        | .step () s' => necX86Normal fuel' rootBody s' Q
        | .terminated (.normal v) => Q v
        | .terminated .unwind => True
        | .failed _ => True
        | .choice _ _ => False
      | none =>
        match blk.term with
        | .jccBool cond falseTarget trueTarget =>
          match evalX86Operand s.mem cond with
          | some (.boolVal b, mem') =>
            (b = false →
              necX86Normal fuel' rootBody
                { s with mem := mem', bb := falseTarget.index, ip := 0 } Q) ∧
            (b = true →
              necX86Normal fuel' rootBody
                { s with mem := mem', bb := trueTarget.index, ip := 0 } Q)
          | none => True
          | _ => False
        | term =>
          match evalX86Term s term with
          | .step () s' => necX86Normal fuel' rootBody s' Q
          | .terminated (.normal v) => Q v
          | .terminated .unwind => True
          | .failed _ => True
          | .choice _ _ => False

/-- Universal soundness theorem for `necX86Normal`. -/
theorem necX86Normal_sound (fuel : Nat) (body : X86Body) (init s : X86State)
    (Q : X86Val → Prop) (hnec : necX86Normal fuel body s Q) :
    ∀ (n : Nat) (tr : List Unit) (v : X86Val),
      ReachesPrefix X86Machine body init n s tr (.terminated (.normal v)) →
      Q v := by
  induction fuel generalizing s with
  | zero =>
    cases hnec
  | succ fuel' ih =>
    intro n tr v hreach
    dsimp [necX86Normal] at hnec
    cases hblk : (s.curBody.getD body).blocks[s.bb]? with
    | none =>
      have hfail : evalX86Step body s = .failed .ub := by
        dsimp [evalX86Step]
        rw [hblk]
      exact False.elim (reachesPrefix_normal_of_failed hfail hreach)
    | some blk =>
      rw [hblk] at hnec
      dsimp at hnec
      cases hinstr : blk.instrs[s.ip]? with
      | some instr =>
        rw [hinstr] at hnec
        dsimp at hnec
        have hstep_eq : evalX86Step body s = evalX86Instr s instr := by
          dsimp [evalX86Step]
          rw [hblk]
          dsimp
          rw [hinstr]
        cases hres : evalX86Instr s instr with
        | step obs s' =>
          cases obs
          rw [hres] at hnec hstep_eq
          exact reachesPrefix_normal_of_step hstep_eq hreach
            (fun n' tr' hr' => ih s' hnec n' tr' v hr')
        | terminated term =>
          cases term with
          | normal retVal =>
            rw [hres] at hnec hstep_eq
            cases reachesPrefix_of_terminated hstep_eq hreach with
            | inl hrun => cases hrun
            | inr hterm =>
              injection hterm with h1
              injection h1 with h2
              subst h2
              exact hnec
          | unwind =>
            rw [hres] at hstep_eq
            exact False.elim (reachesPrefix_not_normal_of_unwind hstep_eq hreach)
        | failed err =>
          rw [hres] at hstep_eq
          exact False.elim (reachesPrefix_normal_of_failed hstep_eq hreach)
        | choice _ _ =>
          rw [hres] at hnec
          cases hnec
      | none =>
        rw [hinstr] at hnec
        dsimp at hnec
        have hstep_eq : evalX86Step body s = evalX86Term s blk.term := by
          dsimp [evalX86Step]
          rw [hblk]
          dsimp
          rw [hinstr]
        cases hterm : blk.term with
        | jccBool cond falseTarget trueTarget =>
          rw [hterm] at hnec hstep_eq
          dsimp at hnec
          cases hcond : evalX86Operand s.mem cond with
          | none =>
            have hfail : evalX86Step body s = .failed .ub := by
              rw [hstep_eq]
              dsimp [evalX86Term]
              rw [hcond]
            exact False.elim (reachesPrefix_normal_of_failed hfail hreach)
          | some p =>
            cases p with
            | mk val mem' =>
              cases val with
              | boolVal b =>
                rw [hcond] at hnec
                dsimp at hnec
                cases b with
                | false =>
                  have hstep_false :
                      evalX86Step body s =
                        .step () { s with mem := mem', bb := falseTarget.index, ip := 0 } := by
                    rw [hstep_eq]
                    dsimp [evalX86Term]
                    rw [hcond]
                  exact reachesPrefix_normal_of_step hstep_false hreach
                    (fun n' tr' hr' => ih _ (hnec.1 rfl) n' tr' v hr')
                | true =>
                  have hstep_true :
                      evalX86Step body s =
                        .step () { s with mem := mem', bb := trueTarget.index, ip := 0 } := by
                    rw [hstep_eq]
                    dsimp [evalX86Term]
                    rw [hcond]
                  exact reachesPrefix_normal_of_step hstep_true hreach
                    (fun n' tr' hr' => ih _ (hnec.2 rfl) n' tr' v hr')
              | word64 _ | unit | adt _ _ | bytes _ _ | stackPtr _ =>
                rw [hcond] at hnec
                cases hnec
        | ret | jmp _ | ud2 | abortPanic | movSizeOfJmp _ _ _
        | repMovsbJmp _ _ _ _ _ | call1 _ _ _ _ =>
          rw [hterm] at hnec hstep_eq
          dsimp at hnec
          cases hres : evalX86Term s blk.term with
          | step obs s' =>
            cases obs
            rw [hterm] at hres
            rw [hres] at hnec hstep_eq
            exact reachesPrefix_normal_of_step hstep_eq hreach
              (fun n' tr' hr' => ih s' hnec n' tr' v hr')
          | terminated term =>
            cases term with
            | normal retVal =>
              rw [hterm] at hres
              rw [hres] at hnec hstep_eq
              cases reachesPrefix_of_terminated hstep_eq hreach with
              | inl hrun => cases hrun
              | inr hterm_eq =>
                injection hterm_eq with h1
                injection h1 with h2
                subst h2
                exact hnec
            | unwind =>
              rw [hterm] at hres
              rw [hres] at hstep_eq
              exact False.elim (reachesPrefix_not_normal_of_unwind hstep_eq hreach)
          | failed err =>
            rw [hterm] at hres
            rw [hres] at hstep_eq
            exact False.elim (reachesPrefix_normal_of_failed hstep_eq hreach)
          | choice _ _ =>
            rw [hterm] at hres
            rw [hres] at hnec
            cases hnec

/-!
## 4. Universal Entry-State Verification Bridges
-/

/-- Extract a compile-time PME fact `P` from `ConstSucceeds tySizes c` via
    `necX86Normal`. -/
theorem constSucceeds_extract (fuel : Nat) {tySizes : Nat → Nat} {c : X86Body}
    {P : Prop}
    (h : ConstSucceeds tySizes c)
    (hnec : forallTypedArgs tySizes c.argTys (fun mem =>
      necX86Normal fuel c { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        (fun _ => P))) :
    P := by
  cases h with
  | intro s₀ h1 =>
    cases h1 with
    | intro n h2 =>
      cases h2 with
      | intro tr h3 =>
        cases h3 with
        | intro v h4 =>
          have hts : s₀.tySizes = tySizes := h4.1
          have hinit : initX86State c s₀ := h4.2.1
          have hreach := h4.2.2
          have hnec_s₀ : necX86Normal fuel c s₀ (fun _ => P) := by
            refine initX86State_canonical c s₀
              (fun s => necX86Normal fuel c s (fun _ => P))
              hinit ?_
            rw [hts]
            exact hnec
          exact necX86Normal_sound fuel c s₀ s₀ (fun _ => P) hnec_s₀ n tr v hreach

/-- Unifying observation: `wpX86` itself also extracts `P` from
    `ConstSucceeds tySizes c` whenever `c` is UB-free (terminating either via
    `ret` or `abortPanic`). -/
theorem constSucceeds_of_wpX86 (fuel : Nat) {tySizes : Nat → Nat} {c : X86Body}
    {P : Prop}
    (h : ConstSucceeds tySizes c)
    (hwp : forallTypedArgs tySizes c.argTys (fun mem =>
      wpX86 fuel c { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        (fun _ => P))) :
    P := by
  cases h with
  | intro s₀ h1 =>
    cases h1 with
    | intro n h2 =>
      cases h2 with
      | intro tr h3 =>
        cases h3 with
        | intro v h4 =>
          have hts : s₀.tySizes = tySizes := h4.1
          have hinit : initX86State c s₀ := h4.2.1
          have hreach := h4.2.2
          have hwp_s₀ : wpX86 fuel c s₀ (fun _ => P) := by
            refine initX86State_canonical c s₀
              (fun s => wpX86 fuel c s (fun _ => P))
              hinit ?_
            rw [hts]
            exact hwp
          exact (wpX86_sound fuel c s₀ s₀ (fun _ => P) hwp_s₀ n tr
            (.terminated (.normal v)) hreach).2 v rfl

/-- Universal bridge for unconditional specifications (`X86Lang.Spec` /
    `EnsuresEqArg`, `EnsuresConst`, `EnsuresBinOp`). -/
theorem verifyX86Spec (fuel : Nat) (body : X86Body)
    (Q : X86State → X86Val → Prop)
    (hvc : ∀ (tySizes : Nat → Nat),
      forallTypedArgs tySizes body.argTys (fun mem =>
        let s₀ : X86State := { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        wpX86 fuel body s₀ (Q s₀))) :
    X86Sem body ≤ X86Lang.Spec (fun q out =>
      ∀ ret, out.outcome = .terminated (.normal ret) → Q q.init ret) := by
  refine behaviorOf_le_pure (M := X86Machine) ?_
  intro q out hpfx
  have hwp_init : wpX86 fuel body q.init (Q q.init) :=
    initX86State_canonical body q.init
      (fun s => wpX86 fuel body s (Q s))
      hpfx.1 (hvc q.init.tySizes)
  exact wpX86_sound fuel body q.init q.init (Q q.init) hwp_init
    q.steps out.trace out.outcome hpfx.2

/-- Universal bridge for precondition-gated specifications (`X86Lang.SpecOn`). -/
theorem verifyX86SpecOn (fuel : Nat) (body : X86Body)
    (pre : ExecQuery X86State → Prop)
    (Q : X86State → X86Val → Prop)
    (hvc : ∀ (tySizes : Nat → Nat) (steps : Nat),
      forallTypedArgs tySizes body.argTys (fun mem =>
        let s₀ : X86State := { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        pre { init := s₀, steps := steps } →
        wpX86 fuel body s₀ (Q s₀))) :
    X86Sem body ≤ X86Lang.SpecOn pre (fun q out =>
      ∀ ret, out.outcome = .terminated (.normal ret) → Q q.init ret) := by
  refine behaviorOf_le_specOn (M := X86Machine) ?_
  intro q out hpre hpfx
  have hwp_init : wpX86 fuel body q.init (Q q.init) :=
    initX86State_canonical body q.init
      (fun s => pre { init := s, steps := q.steps } → wpX86 fuel body s (Q s))
      hpfx.1 (hvc q.init.tySizes q.steps) hpre
  exact wpX86_sound fuel body q.init q.init (Q q.init) hwp_init
    q.steps out.trace out.outcome hpfx.2

/-- Universal bridge for `EnsuresRetLibInv defaultLibInv` under an arbitrary
    precondition `pre`. -/
theorem verifyDefaultRetLibInv (fuel : Nat) (body : X86Body)
    (pre : ExecQuery X86State → Prop)
    (hvc : ∀ (tySizes : Nat → Nat),
      forallTypedArgs tySizes body.argTys (fun mem =>
        wpX86 fuel body { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
          (defaultLibInv tySizes body.retTy))) :
    X86Sem body ≤ EnsuresRetLibInv defaultLibInv body.retTy pre := by
  refine behaviorOf_le_specOn (M := X86Machine) ?_
  intro q out _ hpfx
  have hwp_init :
      wpX86 fuel body q.init (defaultLibInv q.init.tySizes body.retTy) :=
    initX86State_canonical body q.init
      (fun s => wpX86 fuel body s (defaultLibInv s.tySizes body.retTy))
      hpfx.1 (hvc q.init.tySizes)
  exact wpX86_sound fuel body q.init q.init
    (defaultLibInv q.init.tySizes body.retTy) hwp_init
    q.steps out.trace out.outcome hpfx.2

/-- Universal bridge for `EnsuresRetLibInv` on a `pubSafe` function, providing
    `MonoAdmitted` and quantifier-free `allArgsLibInv` directly to the VC. -/
theorem verifyPubSafeRetLibInv (fuel : Nat) (libInv : LibInv) (fn : CapturedFn)
    (traitLaws : Prop) (hkind : fn.kind = .pubSafe traitLaws)
    (hvc : ∀ (tySizes : Nat → Nat),
      MonoAdmitted tySizes fn.prog →
      traitLaws →
      forallTypedArgs tySizes fn.prog.argTys (fun mem =>
        allArgsLibInv libInv tySizes 1 fn.prog.argTys mem →
        wpX86 fuel fn.prog { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
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
  have hwp_init :
      wpX86 fuel fn.prog q.init (libInv q.init.tySizes fn.prog.retTy) :=
    initX86State_canonical fn.prog q.init
      (fun s =>
        allArgsLibInv libInv s.tySizes 1 fn.prog.argTys s.mem →
        wpX86 fuel fn.prog s (libInv s.tySizes fn.prog.retTy))
      hpfx.1 (hvc q.init.tySizes hmono htrait) hlib
  exact wpX86_sound fuel fn.prog q.init q.init
    (libInv q.init.tySizes fn.prog.retTy) hwp_init
    q.steps out.trace out.outcome hpfx.2

/-- Universal bridge for `EnsuresRetLibInv` on a `pubUnsafe` function, providing
    `MonoAdmitted`, quantifier-free `allArgsLibInv`, and `safetyPre` over the
    canonical initial state directly to the VC. -/
theorem verifyPubUnsafeRetLibInv (fuel : Nat) (libInv : LibInv)
    (fn : CapturedFn) (traitLaws : Prop)
    (safetyPre : ExecQuery X86State → Prop)
    (hkind : fn.kind = .pubUnsafe traitLaws safetyPre)
    (hvc : ∀ (tySizes : Nat → Nat) (steps : Nat),
      MonoAdmitted tySizes fn.prog →
      traitLaws →
      forallTypedArgs tySizes fn.prog.argTys (fun mem =>
        let s₀ : X86State := { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        allArgsLibInv libInv tySizes 1 fn.prog.argTys mem →
        safetyPre { init := s₀, steps := steps } →
        wpX86 fuel fn.prog s₀ (libInv tySizes fn.prog.retTy))) :
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
      q.init.mem 1 hrest.2.1
  have hsafety : safetyPre q := hrest.2.2
  have hwp_init :
      wpX86 fuel fn.prog q.init (libInv q.init.tySizes fn.prog.retTy) :=
    initX86State_canonical fn.prog q.init
      (fun s =>
        allArgsLibInv libInv s.tySizes 1 fn.prog.argTys s.mem →
        safetyPre { init := s, steps := q.steps } →
        wpX86 fuel fn.prog s (libInv s.tySizes fn.prog.retTy))
      hpfx.1 (hvc q.init.tySizes q.steps hmono htrait) hlib hsafety
  exact wpX86_sound fuel fn.prog q.init q.init
    (libInv q.init.tySizes fn.prog.retTy) hwp_init
    q.steps out.trace out.outcome hpfx.2

/-!
## 5. Benchmark Suite 1: `id` Variants (Copy, Move, Extra Temps, Nops, Arbitrary `slotCount`)
-/

/-- `idCopyBody` (`EnsuresEqArg 1`) in 1 line via `verifyX86Spec`. -/
theorem idCopyBody_ensures_vcgen :
    X86Sem idCopyBody ≤ EnsuresEqArg 1 :=
  verifyX86Spec 10 idCopyBody (fun s ret => s.mem 1 = some ret)
    (fun _ _ => rfl)

/-- `idCopyBody` (`EnsuresRetLibInv`) in 1 line via `verifyDefaultRetLibInv`. -/
theorem idCopyBody_retLibInv_vcgen (pre : ExecQuery X86State → Prop) :
    X86Sem idCopyBody ≤ EnsuresRetLibInv defaultLibInv .usize pre :=
  verifyDefaultRetLibInv 10 idCopyBody pre (fun _ _ => True.intro)

/-- `idMoveBody` (`EnsuresEqArg 1`) in 1 line via `verifyX86Spec`. -/
theorem idMoveBody_ensures_vcgen :
    X86Sem idMoveBody ≤ EnsuresEqArg 1 :=
  verifyX86Spec 10 idMoveBody (fun s ret => s.mem 1 = some ret)
    (fun _ _ => rfl)

/-- `idMoveBody` (`EnsuresRetLibInv`) in 1 line via `verifyDefaultRetLibInv`. -/
theorem idMoveBody_retLibInv_vcgen (pre : ExecQuery X86State → Prop) :
    X86Sem idMoveBody ≤ EnsuresRetLibInv defaultLibInv .usize pre :=
  verifyDefaultRetLibInv 10 idMoveBody pre (fun _ _ => True.intro)

/-- Non-canonical `id` body with arbitrary `slotCount := k`, multiple temporary
    chains (`_1 -> _2 -> _5 -> _0`), interleaved `nop`s, and out-of-order
    `allocSlot`/`deallocSlot`. -/
def idMultiTempBody (k : Nat) : X86Body where
  argTys := [.usize]
  retTy := .usize
  slotCount := k
  blocks := [
    { instrs := [
        .nop,
        .allocSlot ⟨5⟩,
        .allocSlot ⟨2⟩,
        .mov ⟨2⟩ (.stackSlot ⟨1⟩ false),
        .nop,
        .mov ⟨5⟩ (.stackSlot ⟨2⟩ true),
        .deallocSlot ⟨2⟩,
        .mov ⟨0⟩ (.stackSlot ⟨5⟩ true),
        .deallocSlot ⟨5⟩,
        .nop
      ]
      term := .ret }
  ]

theorem idMultiTempBody_ensures_vcgen (k : Nat) :
    X86Sem (idMultiTempBody k) ≤ EnsuresEqArg 1 :=
  verifyX86Spec 15 (idMultiTempBody k) (fun s ret => s.mem 1 = some ret)
    (fun _ _ => rfl)

theorem idMultiTempBody_retLibInv_vcgen (k : Nat)
    (pre : ExecQuery X86State → Prop) :
    X86Sem (idMultiTempBody k) ≤ EnsuresRetLibInv defaultLibInv .usize pre :=
  verifyDefaultRetLibInv 15 (idMultiTempBody k) pre (fun _ _ => True.intro)

/-- `constUsizeBody c` (`EnsuresConst (.word64 c)`) in 1 line. -/
theorem constUsizeBody_ensures_vcgen (c : Nat) :
    X86Sem (constUsizeBody c) ≤ EnsuresConst (.word64 c) :=
  verifyX86Spec 10 (constUsizeBody c) (fun _ ret => ret = .word64 c)
    (fun _ _ => rfl)

/-!
## 6. Benchmark Suite 2: Binary ALU (All 8 Ops) & Comparison (All 6 Ops) + Non-Canonical Temp Chains
-/

/-- Helper discharging the `EnsuresBinOp` postcondition when `s₀.mem 1 = some v1`
    and `s₀.mem 2 = some v2` hold by `rfl`. -/
theorem ensuresBinOp_of_eq {op : X86BinOp} {v1 v2 ret : X86Val}
    {mem : Nat → Option X86Val}
    (hm1 : mem 1 = some v1)
    (hm2 : mem 2 = some v2)
    (heval : evalX86BinOp op v1 v2 = some ret) :
    ∀ w1 w2, mem 1 = some w1 → mem 2 = some w2 →
      evalX86BinOp op w1 w2 = some ret := by
  intro w1 w2 hw1 hw2
  rw [hm1] at hw1
  rw [hm2] at hw2
  injection hw1 with hw1'
  injection hw2 with hw2'
  subst hw1' hw2'
  exact heval

/-- Specialized `verifyX86Spec` wrapper for `EnsuresBinOp`. -/
theorem verifyEnsuresBinOp (fuel : Nat) (body : X86Body) (op : X86BinOp)
    (arg1Slot arg2Slot : Nat)
    (hvc : ∀ (tySizes : Nat → Nat),
      forallTypedArgs tySizes body.argTys (fun mem =>
        let s₀ : X86State := { mem := mem, bb := 0, ip := 0, tySizes := tySizes }
        wpX86 fuel body s₀ (fun ret =>
          ∀ v1 v2, s₀.mem arg1Slot = some v1 → s₀.mem arg2Slot = some v2 →
            evalX86BinOp op v1 v2 = some ret))) :
    X86Sem body ≤ EnsuresBinOp op arg1Slot arg2Slot :=
  verifyX86Spec fuel body
    (fun s ret => ∀ v1 v2, s.mem arg1Slot = some v1 →
      s.mem arg2Slot = some v2 → evalX86BinOp op v1 v2 = some ret)
    hvc

/-- All 8 binary `usize` ALU/shift operators (`add`, `sub`, `mul`, `bitAnd`,
    `bitOr`, `bitXor`, `shl`, `shr`) satisfy `EnsuresBinOp` via `verifyX86Spec`. -/
theorem binOpBody_alu_ensures_vcgen (op : BinOp) (hAlu : IsUsizeAluOp op) :
    X86Sem (binOpBody op .usize) ≤ EnsuresBinOp (compileBinOp op) 1 2 :=
  match op, hAlu with
  | _, .inl rfl | _, .inr (.inl rfl) | _, .inr (.inr (.inl rfl))
  | _, .inr (.inr (.inr (.inl rfl))) | _, .inr (.inr (.inr (.inr (.inl rfl))))
  | _, .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
  | _, .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  | _, .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))) =>
    verifyEnsuresBinOp 15 _ _ 1 2 (fun _ _ _ => ensuresBinOp_of_eq rfl rfl rfl)

/-- All 8 binary `usize` ALU/shift operators satisfy `EnsuresRetLibInv` via
    `verifyDefaultRetLibInv`. -/
theorem binOpBody_alu_retLibInv_vcgen (op : BinOp) (hAlu : IsUsizeAluOp op)
    (pre : ExecQuery X86State → Prop) :
    X86Sem (binOpBody op .usize) ≤ EnsuresRetLibInv defaultLibInv .usize pre :=
  match op, hAlu with
  | _, .inl rfl | _, .inr (.inl rfl) | _, .inr (.inr (.inl rfl))
  | _, .inr (.inr (.inr (.inl rfl))) | _, .inr (.inr (.inr (.inr (.inl rfl))))
  | _, .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
  | _, .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  | _, .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))) =>
    verifyDefaultRetLibInv 15 _ pre (fun _ _ _ => True.intro)

/-- All 6 binary `usize` comparison operators (`eq`, `ne`, `lt`, `le`, `gt`,
    `ge`) satisfy `EnsuresBinOp` via `verifyX86Spec`. -/
theorem binOpBody_cmp_ensures_vcgen (op : BinOp) (hCmp : IsUsizeCmpOp op) :
    X86Sem (binOpBody op .bool) ≤ EnsuresBinOp (compileBinOp op) 1 2 :=
  match op, hCmp with
  | _, .inl rfl | _, .inr (.inl rfl) | _, .inr (.inr (.inl rfl))
  | _, .inr (.inr (.inr (.inl rfl))) | _, .inr (.inr (.inr (.inr (.inl rfl))))
  | _, .inr (.inr (.inr (.inr (.inr rfl)))) =>
    verifyEnsuresBinOp 15 _ _ 1 2 (fun _ _ _ => ensuresBinOp_of_eq rfl rfl rfl)

/-- All 6 binary `usize` comparison operators satisfy `EnsuresRetLibInv` via
    `verifyDefaultRetLibInv`. -/
theorem binOpBody_cmp_retLibInv_vcgen (op : BinOp) (hCmp : IsUsizeCmpOp op)
    (pre : ExecQuery X86State → Prop) :
    X86Sem (binOpBody op .bool) ≤ EnsuresRetLibInv defaultLibInv .bool pre :=
  match op, hCmp with
  | _, .inl rfl | _, .inr (.inl rfl) | _, .inr (.inr (.inl rfl))
  | _, .inr (.inr (.inr (.inl rfl))) | _, .inr (.inr (.inr (.inr (.inl rfl))))
  | _, .inr (.inr (.inr (.inr (.inr rfl)))) =>
    verifyDefaultRetLibInv 15 _ pre (fun _ _ _ => True.intro)

/-- Non-canonical binary ALU body (`let tmp1 = x; let tmp2 = y; let res = tmp1 +
    tmp2; res`) with `slotCount := 9`, multi-block `jmp`, and reversed
    `deallocSlot` order that would fail AST unification with `binOpBody`. -/
def binOpExtraTempsBody (op : X86BinOp) : X86Body where
  argTys := [.usize, .usize]
  retTy := .usize
  slotCount := 9
  blocks := [
    { instrs := [
        .allocSlot ⟨3⟩,
        .mov ⟨3⟩ (.stackSlot ⟨1⟩ false),
        .allocSlot ⟨4⟩,
        .mov ⟨4⟩ (.stackSlot ⟨2⟩ false),
        .allocSlot ⟨5⟩,
        .mov ⟨5⟩ (.stackSlot ⟨3⟩ true),
        .allocSlot ⟨6⟩,
        .mov ⟨6⟩ (.stackSlot ⟨4⟩ true)
      ]
      term := .jmp ⟨1⟩ },
    { instrs := [
        .allocSlot ⟨7⟩,
        .alu op ⟨7⟩ (.stackSlot ⟨5⟩ true) (.stackSlot ⟨6⟩ true),
        .mov ⟨0⟩ (.stackSlot ⟨7⟩ true),
        .deallocSlot ⟨3⟩,
        .deallocSlot ⟨4⟩,
        .deallocSlot ⟨5⟩,
        .deallocSlot ⟨6⟩,
        .deallocSlot ⟨7⟩
      ]
      term := .ret }
  ]

theorem binOpExtraTemps_add_ensures_vcgen :
    X86Sem (binOpExtraTempsBody .add) ≤ EnsuresBinOp .add 1 2 :=
  verifyX86Spec 20 (binOpExtraTempsBody .add) (fun s ret =>
    ∀ v1 v2, s.mem 1 = some v1 → s.mem 2 = some v2 →
      evalX86BinOp .add v1 v2 = some ret)
    (fun _ _ _ => ensuresBinOp_of_eq rfl rfl rfl)

/-!
## 7. Benchmark Suite 3: Branching CFGs (`max_usize` Diamond & 3-Way `clamp_usize`)
-/

/-- `maxUsizeBody` (4-block diamond CFG with `jccBool`) satisfies
    `EnsuresRetLibInv` in 1 line (down from 132 lines in `MirLemmas.lean`!). -/
theorem maxUsizeBody_retLibInv_vcgen (pre : ExecQuery X86State → Prop) :
    X86Sem maxUsizeBody ≤ EnsuresRetLibInv defaultLibInv .usize pre :=
  verifyDefaultRetLibInv 20 maxUsizeBody pre
    (fun _ _ _ => ⟨fun _ => True.intro, fun _ => True.intro⟩)

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

/-- Full functional specification for `maxUsizeBody`: returns
    `.word64 (if a < b then b else a)`. Proved in 4 lines! -/
theorem maxUsizeBody_functional_spec_vcgen :
    X86Sem maxUsizeBody ≤ X86Lang.Spec (fun q out =>
      ∀ ret, out.outcome = .terminated (.normal ret) →
        ∀ a b, q.init.mem 1 = some (.word64 a) →
          q.init.mem 2 = some (.word64 b) →
          ret = .word64 (if a < b then b else a)) := by
  refine verifyX86Spec 20 maxUsizeBody
    (fun s ret => ∀ a b, s.mem 1 = some (.word64 a) →
      s.mem 2 = some (.word64 b) → ret = .word64 (if a < b then b else a))
    (fun _ a b => ⟨?_, ?_⟩)
  · intro hfalse a' b' ha hb
    cases ha; cases hb
    rw [if_decide_false hfalse]
  · intro htrue a' b' ha hb
    cases ha; cases hb
    rw [if_decide_true htrue]

/-- 3-argument, 6-block nested `if`/`else if`/`else` x86-64 CFG for
    `pub fn clamp_usize(x: usize, lo: usize, hi: usize) -> usize`:
    ```rust
    if x < lo { lo } else if hi < x { hi } else { x }
    ``` -/
def clampUsizeBody : X86Body where
  argTys := [.usize, .usize, .usize]
  retTy := .usize
  slotCount := 9
  blocks := [
    -- bb0: test x < lo
    { instrs := [
        .allocSlot ⟨4⟩,
        .allocSlot ⟨5⟩,
        .mov ⟨5⟩ (.stackSlot ⟨1⟩ false),
        .allocSlot ⟨6⟩,
        .mov ⟨6⟩ (.stackSlot ⟨2⟩ false),
        .alu .lt ⟨4⟩ (.stackSlot ⟨5⟩ true) (.stackSlot ⟨6⟩ true)
      ]
      term := .jccBool (.stackSlot ⟨4⟩ true) ⟨2⟩ ⟨1⟩ },
    -- bb1 (x < lo): return lo
    { instrs := [
        .deallocSlot ⟨6⟩,
        .deallocSlot ⟨5⟩,
        .mov ⟨0⟩ (.stackSlot ⟨2⟩ false)
      ]
      term := .jmp ⟨5⟩ },
    -- bb2 (¬(x < lo)): test hi < x
    { instrs := [
        .deallocSlot ⟨6⟩,
        .deallocSlot ⟨5⟩,
        .allocSlot ⟨7⟩,
        .mov ⟨7⟩ (.stackSlot ⟨3⟩ false),
        .allocSlot ⟨8⟩,
        .mov ⟨8⟩ (.stackSlot ⟨1⟩ false),
        .alu .lt ⟨4⟩ (.stackSlot ⟨7⟩ true) (.stackSlot ⟨8⟩ true)
      ]
      term := .jccBool (.stackSlot ⟨4⟩ true) ⟨4⟩ ⟨3⟩ },
    -- bb3 (hi < x): return hi
    { instrs := [
        .deallocSlot ⟨8⟩,
        .deallocSlot ⟨7⟩,
        .mov ⟨0⟩ (.stackSlot ⟨3⟩ false)
      ]
      term := .jmp ⟨5⟩ },
    -- bb4 (lo ≤ x ≤ hi): return x
    { instrs := [
        .deallocSlot ⟨8⟩,
        .deallocSlot ⟨7⟩,
        .mov ⟨0⟩ (.stackSlot ⟨1⟩ false)
      ]
      term := .jmp ⟨5⟩ },
    -- bb5: join & return
    { instrs := [.deallocSlot ⟨4⟩]
      term := .ret }
  ]

/-- `clampUsizeBody` (6-block nested conditional CFG) satisfies
    `EnsuresRetLibInv` in 2 lines. -/
theorem clampUsizeBody_retLibInv_vcgen (pre : ExecQuery X86State → Prop) :
    X86Sem clampUsizeBody ≤ EnsuresRetLibInv defaultLibInv .usize pre :=
  verifyDefaultRetLibInv 30 clampUsizeBody pre
    (fun _ _ _ _ =>
      ⟨fun _ => ⟨fun _ => True.intro, fun _ => True.intro⟩,
       fun _ => True.intro⟩)

/-- Full functional specification for `clampUsizeBody`: returns
    `.word64 (if x < lo then lo else if hi < x then hi else x)`. -/
theorem clampUsizeBody_functional_spec_vcgen :
    X86Sem clampUsizeBody ≤ X86Lang.Spec (fun q out =>
      ∀ ret, out.outcome = .terminated (.normal ret) →
        ∀ x lo hi,
          q.init.mem 1 = some (.word64 x) →
          q.init.mem 2 = some (.word64 lo) →
          q.init.mem 3 = some (.word64 hi) →
          ret = .word64 (if x < lo then lo else if hi < x then hi else x)) := by
  refine verifyX86Spec 30 clampUsizeBody
    (fun s ret => ∀ x lo hi,
      s.mem 1 = some (.word64 x) →
      s.mem 2 = some (.word64 lo) →
      s.mem 3 = some (.word64 hi) →
      ret = .word64 (if x < lo then lo else if hi < x then hi else x))
    (fun _ x lo hi => ⟨fun hlt1 => ⟨?_, ?_⟩, ?_⟩)
  · intro hlt2 x' lo' hi' hx hlo hhi
    cases hx; cases hlo; cases hhi
    rw [if_decide_false hlt1, if_decide_false hlt2]
  · intro hlt2 x' lo' hi' hx hlo hhi
    cases hx; cases hlo; cases hhi
    rw [if_decide_false hlt1, if_decide_true hlt2]
  · intro hlt1 x' lo' hi' hx hlo hhi
    cases hx; cases hlo; cases hhi
    rw [if_decide_true hlt1]

/-!
## 8. Benchmark Suite 4: PME Size-Checked Transmute (`slotCount = 5` & `6`, plus Interprocedural `call1`)
-/

/-- Variant of `sizeEqConstBody` emitted by `rustc -Z mir-opt-level=0` when the
    user writes `const { assert!(size_of::<Src>() == size_of::<Dst>()); }`
    *with* a trailing semicolon (`slotCount := 6` with an extra `_1: ()` local
    and shifted slot indices `2..5`). -/
def sizeEqConstSemicolonBody : X86Body where
  argTys := []
  retTy := .unit
  slotCount := 6
  blocks := [
    { instrs := [.allocSlot ⟨1⟩, .allocSlot ⟨2⟩, .allocSlot ⟨3⟩, .nop]
      term := .movSizeOfJmp ⟨3⟩ (.param 0) ⟨1⟩ },
    { instrs := [.allocSlot ⟨4⟩, .nop]
      term := .movSizeOfJmp ⟨4⟩ (.param 1) ⟨2⟩ },
    { instrs := [.alu .eq ⟨2⟩ (.stackSlot ⟨3⟩ true) (.stackSlot ⟨4⟩ true)]
      term := .jccBool (.stackSlot ⟨2⟩ true) ⟨4⟩ ⟨3⟩ },
    { instrs := [
        .deallocSlot ⟨4⟩,
        .deallocSlot ⟨3⟩,
        .mov ⟨1⟩ (.imm .unit),
        .deallocSlot ⟨2⟩,
        .mov ⟨0⟩ (.imm .unit),
        .deallocSlot ⟨1⟩
      ]
      term := .ret },
    { instrs := [.deallocSlot ⟨4⟩, .deallocSlot ⟨3⟩, .allocSlot ⟨5⟩, .nop]
      term := .abortPanic }
  ]

/-- PME necessity for `sizeEqConstBody` (`slotCount := 5`) in 1 line via
    `constSucceeds_extract` (down from 64 lines in `MirLemmas.lean`!). -/
theorem constSucceeds_sizeEqConstBody_vcgen (tySizes : Nat → Nat)
    (h : ConstSucceeds tySizes sizeEqConstBody) :
    tySizes 0 = tySizes 1 :=
  constSucceeds_extract 20 h ⟨fun _ => True.intro, of_decide_eq_true⟩

/-- PME necessity for `sizeEqConstSemicolonBody` (`slotCount := 6`) with the
    EXACT same 1-line proof! -/
theorem constSucceeds_sizeEqConstSemicolonBody_vcgen (tySizes : Nat → Nat)
    (h : ConstSucceeds tySizes sizeEqConstSemicolonBody) :
    tySizes 0 = tySizes 1 :=
  constSucceeds_extract 20 h ⟨fun _ => True.intro, of_decide_eq_true⟩

/-- Demonstration that `constSucceeds_of_wpX86` also discharges PME necessity
    using `wpX86` alone! -/
theorem constSucceeds_sizeEqConstBody_via_wp (tySizes : Nat → Nat)
    (h : ConstSucceeds tySizes sizeEqConstBody) :
    tySizes 0 = tySizes 1 :=
  constSucceeds_of_wpX86 20 h ⟨fun _ => True.intro, of_decide_eq_true⟩

/-- `transmuteCheckedBody` verified in 3 lines via `verifyPubSafeRetLibInv`
    (down from 95 lines in `MirLemmas.lean`!). -/
theorem transmuteCheckedBody_verified_vcgen (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := transmuteCheckedBody }
    X86Sem fn.prog ≤
      EnsuresRetLibInv defaultLibInv fn.prog.retTy
        (fn.effectivePre defaultLibInv) := by
  intro fn
  refine verifyPubSafeRetLibInv 20 defaultLibInv fn True rfl
    (fun tySizes hmono _ _ _ => ?_)
  have heq : tySizes 0 = tySizes 1 :=
    constSucceeds_sizeEqConstBody_vcgen tySizes
      (hmono sizeEqConstBody (.direct (.head _)))
  exact ⟨heq, rfl, rfl⟩

/-- `outerTransmuteBody` (which calls `transmuteCheckedBody` via `X86Term.call1`)
    verified in 4 lines via `verifyPubSafeRetLibInv` (down from 103 lines in
    `MirLemmas.lean`!). -/
theorem outerTransmuteBody_verified_vcgen (fnName : String) :
    let fn : CapturedFn := { name := fnName, prog := outerTransmuteBody }
    X86Sem fn.prog ≤
      EnsuresRetLibInv defaultLibInv fn.prog.retTy
        (fn.effectivePre defaultLibInv) := by
  intro fn
  refine verifyPubSafeRetLibInv 30 defaultLibInv fn True rfl
    (fun tySizes hmono _ _ _ => ?_)
  have hreq : RequiresConst outerTransmuteBody sizeEqConstBody :=
    .call1 (.head _) rfl (.direct (.head _))
  have heq : tySizes 0 = tySizes 1 :=
    constSucceeds_sizeEqConstBody_vcgen tySizes (hmono sizeEqConstBody hreq)
  exact ⟨heq, rfl, rfl⟩

/-!
## 9. Benchmark Suite 5: `NonZeroUsize` Library Contract + Interprocedural `call1` Client
-/

/-- `makeNonZeroBody` verified in 2 lines via `verifyPubSafeRetLibInv` (down
    from 77 lines in `MirLemmas.lean`!). -/
theorem makeNonZeroBody_verified_vcgen (fnName : String) :
    let fn : CapturedFn := {
      name := fnName
      prog := makeNonZeroBody
      kind := .pubSafe True
    }
    X86Sem fn.prog ≤
      EnsuresRetLibInv nonZeroLibInv fn.prog.retTy
        (fn.effectivePre nonZeroLibInv) := by
  intro fn
  refine verifyPubSafeRetLibInv 20 nonZeroLibInv fn True rfl
    (fun _ _ _ _ _ => ⟨of_decide_eq_false, fun _ => Nat.succ_ne_zero 0⟩)

/-- `newUncheckedBody` (`pub unsafe fn`) verified in 2 lines via
    `verifyPubUnsafeRetLibInv` (down from 54 lines in `MirLemmas.lean`!). -/
theorem newUncheckedBody_verified_vcgen (fnName : String) :
    let fn : CapturedFn := {
      name := fnName
      prog := newUncheckedBody
      kind := .pubUnsafe True newUncheckedSafetyPre
    }
    X86Sem fn.prog ≤
      EnsuresRetLibInv nonZeroLibInv fn.prog.retTy
        (fn.effectivePre nonZeroLibInv) := by
  intro fn
  refine verifyPubUnsafeRetLibInv 15 nonZeroLibInv fn True
    newUncheckedSafetyPre rfl
    (fun _ _ _ _ a _ hsafety => hsafety a rfl)

/-- `getUncheckedNonZeroBody` verified in 3 lines via `verifyPubSafeRetLibInv`
    (down from 75 lines in `MirLemmas.lean`!). -/
theorem getUncheckedNonZeroBody_verified_vcgen (fnName : String) :
    let fn : CapturedFn := {
      name := fnName
      prog := getUncheckedNonZeroBody
      kind := .pubSafe True
    }
    X86Sem fn.prog ≤
      EnsuresRetLibInv nonZeroLibInv fn.prog.retTy
        (fn.effectivePre nonZeroLibInv) := by
  intro fn
  refine verifyPubSafeRetLibInv 20 nonZeroLibInv fn True rfl
    (fun _ _ _ _ hlib =>
      ⟨fun _ => True.intro, fun htrue => hlib.1 (of_decide_eq_true htrue)⟩)

/-- Interprocedural `NonZeroUsize` client (`pub fn sanitize_nonzero(x: usize) ->
    usize { get_unchecked_nonzero(make_nonzero(x)) }`) chaining two `call1`
    calls across 3 basic blocks. -/
noncomputable def sanitizeNonZeroBody : X86Body where
  argTys := [.usize]
  retTy := .usize
  slotCount := 4
  blocks := [
    { instrs := [.allocSlot ⟨2⟩, .allocSlot ⟨3⟩, .mov ⟨3⟩ (.stackSlot ⟨1⟩ false)]
      term := .call1 ⟨2⟩ makeNonZeroBody (.stackSlot ⟨3⟩ true) ⟨1⟩ },
    { instrs := [.deallocSlot ⟨3⟩]
      term := .call1 ⟨0⟩ getUncheckedNonZeroBody (.stackSlot ⟨2⟩ true) ⟨2⟩ },
    { instrs := [.deallocSlot ⟨2⟩]
      term := .ret }
  ]

/-- `sanitizeNonZeroBody` verified across both `call1` calls (`makeNonZeroBody`
    and `getUncheckedNonZeroBody`) in 4 lines! -/
theorem sanitizeNonZeroBody_verified_vcgen (fnName : String) :
    let fn : CapturedFn := {
      name := fnName
      prog := sanitizeNonZeroBody
      kind := .pubSafe True
    }
    X86Sem fn.prog ≤
      EnsuresRetLibInv nonZeroLibInv fn.prog.retTy
        (fn.effectivePre nonZeroLibInv) := by
  intro fn
  refine verifyPubSafeRetLibInv 40 nonZeroLibInv fn True rfl
    (fun _ _ _ _ _ => ⟨?_, ?_⟩)
  · intro hfalse
    exact ⟨fun _ => True.intro,
           fun htrue => (of_decide_eq_false hfalse) (of_decide_eq_true htrue)⟩
  · intro _
    exact ⟨fun _ => True.intro,
           fun htrue => Nat.succ_ne_zero 0 (of_decide_eq_true htrue)⟩

/-!
## 10. End-to-End `Trusted.CrateTheorem` Witnesses via VCgen
-/

/-- End-to-end `CrateTheorem` witness for `idMultiTempBody k` (parametric in
    `slotCount := k` and containing extra `nop`s and multi-temp chain). -/
theorem prove_id_multi_temp_crate (fnName : String) (k : Nat) :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := idMultiTempBody k
        specs := [EnsuresEqArg 1]
      }]
      tcb := [TCBItem.assemblerLowering fnName (idMultiTempBody k)]
    } :=
  verify_single_fn_crate fnName (idMultiTempBody k) (EnsuresEqArg 1)
    (idMultiTempBody_retLibInv_vcgen k _)
    (idMultiTempBody_ensures_vcgen k)

/-- End-to-end `CrateTheorem` witness for `clampUsizeBody` (6-block nested
    conditional CFG). -/
theorem prove_clamp_usize_wf_crate (fnName : String) :
    CrateTheorem {
      functions := [{ name := fnName, prog := clampUsizeBody, specs := [] }]
      tcb := [TCBItem.assemblerLowering fnName clampUsizeBody]
    } :=
  verify_single_fn_wf_crate fnName clampUsizeBody
    (clampUsizeBody_retLibInv_vcgen _)

/-- End-to-end `CrateTheorem` witness for the 4-function `NonZeroUsize` library
    crate (`make_nonzero`, `new_unchecked`, `get_unchecked_nonzero`, and
    interprocedural `sanitize_nonzero`). -/
theorem prove_nonzero_four_fn_crate
    (fn1Name fn2Name fn3Name fn4Name : String) :
    CrateTheorem {
      adts := [nonZeroAdtDecl]
      libInv := nonZeroLibInv
      functions := [
        { name := fn1Name, prog := makeNonZeroBody, kind := .pubSafe True },
        { name := fn2Name, prog := newUncheckedBody, kind := .pubUnsafe True newUncheckedSafetyPre },
        { name := fn3Name, prog := getUncheckedNonZeroBody, kind := .pubSafe True },
        { name := fn4Name, prog := sanitizeNonZeroBody, kind := .pubSafe True }
      ]
      tcb := [
        TCBItem.assemblerLowering fn1Name makeNonZeroBody,
        TCBItem.assemblerLowering fn2Name newUncheckedBody,
        TCBItem.assemblerLowering fn3Name getUncheckedNonZeroBody,
        TCBItem.assemblerLowering fn4Name sanitizeNonZeroBody
      ]
    } := by
  refine ⟨(by intro h; cases h), nonZeroLibInv_admissible, True.intro, ?_⟩
  refine ⟨⟨⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩, ?_⟩,
          ⟨⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩, ?_⟩,
          ⟨⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩, ?_⟩,
          ⟨⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩, ?_⟩,
          True.intro⟩
  · intro hTcb
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hTcb.1 (makeNonZeroBody_verified_vcgen fn1Name))
      (ensuresRetLibInv_le_wellFormedOn _ _ _)
      hTcb.1.1
  · intro hTcb
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hTcb.2.1 (newUncheckedBody_verified_vcgen fn2Name))
      (ensuresRetLibInv_le_wellFormedOn _ _ _)
      hTcb.2.1.1
  · intro hTcb
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hTcb.2.2.1 (getUncheckedNonZeroBody_verified_vcgen fn3Name))
      (ensuresRetLibInv_le_wellFormedOn _ _ _)
      hTcb.2.2.1.1
  · intro hTcb
    exact Compiler.Verified.with_wellFormedOn
      (Compiler.SoundOn.verify hTcb.2.2.2.1 (sanitizeNonZeroBody_verified_vcgen fn4Name))
      (ensuresRetLibInv_le_wellFormedOn _ _ _)
      hTcb.2.2.2.1.1

end Anneal.SymbolicVCGen
