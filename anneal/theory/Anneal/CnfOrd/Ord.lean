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

public section
namespace Anneal.CnfOrd

/-!
# Constructive `< ω^ω` Cantor Normal Form Ordinals (`Anneal.CnfOrd.Ord`)

Zero-axiom (`[]`), foundation-only (`prelude` + `Init.*`), LCNF-computable
(`0` `noncomputable`, `0` `._unsafe_rec`, `0` `omega`) Cantor Normal Form
ordinal algebra below `ω^ω`:

1. **Canonical representation & strict linear order (`CnfOrd`, `isCanonicalCnf`,
   `cnfCmp`, `cnfLt`, `cnfBle`, `cnf_eq_of_coeff_eq`, `cnfLt_of_coeff_drop`):**
   Represents ordinals `< ω^ω` as `List (Nat × Nat)` terms `(exp, coeff)` with
   strictly descending exponents and positive coefficients, proving strict-order
   laws, canonical uniqueness by exponent coefficients, and strict `< ω^ω`
   descent from the highest differing exponent `q0`.
2. **Hessenberg natural addition (`cnfAddTerm`, `cnfNorm`, `cnfNatAdd`,
   `cnfAddOrd`):** Commutative, associative ordinal natural sum preserving
   `isCanonicalCnf` and right-hand `< ω^ω` inflation (`cnfLt_cnfAddOrd_of_lt`).
3. **Constructive Gentzen `< ω^ω` accessibility (`CnfAcc`, `cnfAcc_all`) &
   abstract fuel-free convergence (`CnfStepConverges`,
   `cnfStep_terminates_all`):** Proves `∀ ord, isCanonicalCnf ord = true →
   CnfAcc ord` via nested induction on exponent bound, leading coefficient, and
   tail accessibility (`[]` zero axioms) and lifts any `< ω^ω`-decreasing
   deterministic step system to fuel-free convergence plus constructive fuel
   extraction.
-/

/-! ## 1. Constructive `Bool` / `Nat` / `List` Preliminaries -/

private theorem boolFalseNeTrue (h : false = true) : False :=
  Bool.noConfusion h

private theorem boolTrueNeFalse (h : true = false) : False :=
  Bool.noConfusion h

private theorem bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => rfl

private theorem bandRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolFalseNeTrue h)
  | true => exact h

private theorem bandIntro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]
  rfl

private theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natEq_of_beq (a b : Nat) (h : Nat.beq a b = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrue h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact congrArg Nat.succ (ih b' h)

private theorem natBle_refl (a : Nat) : Nat.ble a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBle_zero_left (a : Nat) : Nat.ble 0 a = true := by
  cases a <;> rfl

private theorem natBle_zero_right (a : Nat) (h : Nat.ble a 0 = true) :
    a = 0 := by
  cases a with
  | zero => rfl
  | succ _ => exact False.elim (boolFalseNeTrue h)

private theorem natBle_succ_right (a b : Nat) (h : Nat.ble a b = true) :
    Nat.ble a (b + 1) = true := by
  revert b h
  induction a with
  | zero => intro _ _; rfl
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact ih b' h

private theorem natBle_trans (a b c : Nat)
    (h1 : Nat.ble a b = true) (h2 : Nat.ble b c = true) :
    Nat.ble a c = true := by
  revert b c
  induction a with
  | zero => intro _ c _ _; exact natBle_zero_left c
  | succ _ ih =>
    intro b c h1 h2
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h1)
    | succ b' =>
      cases c with
      | zero => exact False.elim (boolFalseNeTrue h2)
      | succ c' => exact ih b' c' h1 h2

private theorem natBle_antisym (a b : Nat)
    (h1 : Nat.ble a b = true) (h2 : Nat.ble b a = true) :
    a = b := by
  revert b
  induction a with
  | zero => intro b _ h2; exact (natBle_zero_right b h2).symm
  | succ _ ih =>
    intro b h1 h2
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h1)
    | succ b' => exact congrArg Nat.succ (ih b' h1 h2)

private theorem natAdd_zero_left (a : Nat) : 0 + a = a := by
  induction a with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natAdd_succ_left (a b : Nat) : (a + 1) + b = (a + b) + 1 := by
  induction b with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natAdd_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => exact natAdd_zero_left b
  | succ a' ih => exact Eq.trans (natAdd_succ_left a' b) (congrArg Nat.succ ih)

private theorem natAdd_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ _ ih => exact congrArg Nat.succ ih

private theorem natBle_add_right (a b : Nat) : Nat.ble a (a + b) = true := by
  induction b with
  | zero => exact natBle_refl a
  | succ _ ih => exact natBle_succ_right a _ ih

private theorem natBle_of_lt_false (a b : Nat) (h : Nat.blt a b = false) :
    Nat.ble b a = true := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolTrueNeFalse h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => rfl
    | succ b' => exact ih b' h

private theorem natBlt_irrefl (a : Nat) : Nat.blt a a = false := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

@[expose] def listFoldAux {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : List α × β :=
  List.foldr (fun x acc => (x :: acc.1, cons x acc.1 acc.2)) ([], nil) xs

private theorem listFoldAux_fst {α β : Type} (nil : β)
    (cons : α → List α → β → β) (xs : List α) :
    (listFoldAux nil cons xs).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (List.cons x) ih

@[expose] def listFold {α β : Type} (nil : β) (cons : α → List α → β → β)
    (xs : List α) : β :=
  (listFoldAux nil cons xs).2

private theorem listFold_cons {α β : Type} (nil : β)
    (cons : α → List α → β → β) (x : α) (tl : List α) :
    listFold nil cons (x :: tl) = cons x tl (listFold nil cons tl) := by
  dsimp only [listFold]
  change (cons x (listFoldAux nil cons tl).1 (listFoldAux nil cons tl).2) = _
  rw [listFoldAux_fst]

/-! ## 2. Three-Way Comparison & Canonical Cantor Normal Form `< ω^ω` -/

/-- Three-way ordering result (`lt`, `eq`, `gt`). -/
inductive Cmp3 where
  | lt
  | eq
  | gt

/-- Swaps `.lt` and `.gt`, fixing `.eq`. -/
@[expose] def cmpFlip (c : Cmp3) : Cmp3 :=
  match c with
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

/-- Computable strict inequality `a < b` (`Nat.ble (a + 1) b`). -/
@[expose] def natLt (a b : Nat) : Bool :=
  Nat.ble (a + 1) b

/-- Computable three-way comparison on `Nat`. -/
@[expose] def natCmp (a b : Nat) : Cmp3 :=
  match natLt a b with
  | true => .lt
  | false =>
    match natLt b a with
    | true => .gt
    | false => .eq

private theorem natBleOfLtFalse (a b : Nat) (h : natLt a b = false) :
    Nat.ble b a = true :=
  natBle_of_lt_false a b h

private theorem natLtIrrefl (a : Nat) : natLt a a = false :=
  natBlt_irrefl a

private theorem natLtZeroRightFalse (a : Nat) : natLt a 0 = false := by
  cases a <;> rfl

private theorem natLtTrans (a b c : Nat)
    (hab : natLt a b = true) (hbc : natLt b c = true) :
    natLt a c = true :=
  natBle_trans (a + 1) b c hab
    (natBle_trans b (b + 1) c (natBle_succ_right b b (natBle_refl b)) hbc)

private theorem natLtAsymm (a b : Nat) (hab : natLt a b = true) :
    natLt b a = false := by
  cases h : natLt b a with
  | false => rfl
  | true =>
    exact False.elim (boolTrueNeFalse
      (Eq.trans (Eq.symm (natLtTrans a b a hab h)) (natLtIrrefl a)))

private theorem natBeqFalseOfLt {a b : Nat} (h : natLt a b = true) :
    Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true =>
    rw [natEq_of_beq a b hb] at h
    exact False.elim (boolTrueNeFalse (Eq.trans (Eq.symm h) (natLtIrrefl b)))

private theorem natLtOfLtOfBle (a b c : Nat)
    (hab : natLt a b = true) (hbc : Nat.ble b c = true) :
    natLt a c = true :=
  natBle_trans (a + 1) b c hab hbc

private theorem natCmpGtToLt {a b : Nat} (h : natCmp a b = .gt) :
    natLt b a = true := by
  dsimp only [natCmp] at h
  cases h1 : natLt a b with
  | true => rw [h1] at h; exact False.elim (Cmp3.noConfusion h)
  | false =>
    rw [h1] at h
    dsimp only at h
    cases h2 : natLt b a with
    | true => rfl
    | false => rw [h2] at h; exact False.elim (Cmp3.noConfusion h)

private theorem natCmpLtToLt {a b : Nat} (h : natCmp a b = .lt) :
    natLt a b = true := by
  dsimp only [natCmp] at h
  cases h1 : natLt a b with
  | true => rfl
  | false =>
    rw [h1] at h
    dsimp only at h
    cases h2 : natLt b a with
    | true => rw [h2] at h; exact False.elim (Cmp3.noConfusion h)
    | false => rw [h2] at h; exact False.elim (Cmp3.noConfusion h)

private theorem natCmpEqEq {a b : Nat} (h : natCmp a b = .eq) : a = b := by
  dsimp only [natCmp] at h
  cases h1 : natLt a b with
  | true => rw [h1] at h; exact False.elim (Cmp3.noConfusion h)
  | false =>
    rw [h1] at h
    dsimp only at h
    cases h2 : natLt b a with
    | true => rw [h2] at h; exact False.elim (Cmp3.noConfusion h)
    | false =>
      exact natBle_antisym a b (natBleOfLtFalse b a h2) (natBleOfLtFalse a b h1)

private theorem natCmpRefl (a : Nat) : natCmp a a = .eq := by
  dsimp only [natCmp]
  rw [natLtIrrefl a]

private theorem natCmpFlip (a b : Nat) :
    natCmp b a = cmpFlip (natCmp a b) := by
  dsimp only [natCmp]
  cases h1 : natLt a b with
  | true => rw [natLtAsymm a b h1]; rfl
  | false =>
    cases natLt b a <;> rfl

/-- Cantor Normal Form ordinal `< ω^ω`: list of `(exponent, coefficient)` pairs
representing `∑_i ω^{exp_i} · coeff_i`. -/
abbrev CnfOrd : Type := List (Nat × Nat)

/-- `true` iff every term exponent in `xs` is strictly below `bound`. -/
@[expose] def cnfAllBelow (bound : Nat) (xs : CnfOrd) : Bool :=
  xs.foldr (fun p ih => natLt p.1 bound && ih) true

/-- `true` iff `xs` is in canonical Cantor Normal Form: strictly descending
exponents `e_0 > e_1 > ...` and strictly positive coefficients `c_i > 0`. -/
@[expose] def isCanonicalCnf (xs : CnfOrd) : Bool :=
  listFold true (fun p tl ih => natLt 0 p.2 && cnfAllBelow p.1 tl && ih) xs

/-- Unfolding equation for `isCanonicalCnf (p :: tl)`. -/
theorem isCanonicalCnf_cons (p : Nat × Nat) (tl : CnfOrd) :
    isCanonicalCnf (p :: tl) =
      (natLt 0 p.2 && cnfAllBelow p.1 tl && isCanonicalCnf tl) := by
  dsimp only [isCanonicalCnf]
  exact listFold_cons _ _ p tl

/-- Monotonicity of `cnfAllBelow` in the upper bound. -/
theorem cnfAllBelow_mono (b1 b2 : Nat) (xs : CnfOrd)
    (hb : Nat.ble b1 b2 = true) (h : cnfAllBelow b1 xs = true) :
    cnfAllBelow b2 xs = true := by
  induction xs with
  | nil => rfl
  | cons p _ ih =>
    exact bandIntro (natLtOfLtOfBle p.1 b1 b2 (bandLeft h) hb)
      (ih (bandRight h))

/-- Lexicographic three-way comparison on single `(exp, coeff)` CNF terms. -/
@[expose] def termCmp (a b : Nat × Nat) : Cmp3 :=
  match natCmp a.1 b.1 with
  | .lt => .lt
  | .gt => .gt
  | .eq => natCmp a.2 b.2

private theorem termCmpRefl (a : Nat × Nat) : termCmp a a = .eq := by
  dsimp only [termCmp]
  rw [natCmpRefl a.1, natCmpRefl a.2]

private theorem termCmpFlip (a b : Nat × Nat) :
    termCmp b a = cmpFlip (termCmp a b) := by
  dsimp only [termCmp]
  rw [natCmpFlip a.1 b.1]
  cases natCmp a.1 b.1 with
  | lt => rfl
  | gt => rfl
  | eq => exact natCmpFlip a.2 b.2

private theorem termCmpTransLtBle (a b c : Nat × Nat)
    (hab : termCmp a b = .lt)
    (hbc : (match termCmp b c with
      | .lt => true | .eq => true | .gt => false) = true) :
    termCmp a c = .lt := by
  dsimp only [termCmp] at hab hbc
  dsimp only [termCmp]
  cases h1 : natCmp a.1 b.1 with
  | gt => rw [h1] at hab; exact False.elim (Cmp3.noConfusion hab)
  | lt =>
    cases h2 : natCmp b.1 c.1 with
    | gt => rw [h2] at hbc; exact False.elim (boolFalseNeTrue hbc)
    | eq => rw [← natCmpEqEq h2, h1]
    | lt =>
      have hac := natLtTrans a.1 b.1 c.1 (natCmpLtToLt h1) (natCmpLtToLt h2)
      dsimp only [natCmp]
      rw [hac]
  | eq =>
    rw [h1] at hab
    dsimp only at hab
    rw [natCmpEqEq h1]
    cases h2 : natCmp b.1 c.1 with
    | gt => rw [h2] at hbc; exact False.elim (boolFalseNeTrue hbc)
    | lt => rfl
    | eq =>
      rw [h2] at hbc
      dsimp only at hbc
      cases h2v : natCmp b.2 c.2 with
      | gt => rw [h2v] at hbc; exact False.elim (boolFalseNeTrue hbc)
      | eq => rw [← natCmpEqEq h2v, hab]
      | lt =>
        have hac2 := natLtTrans a.2 b.2 c.2 (natCmpLtToLt hab)
          (natCmpLtToLt h2v)
        dsimp only [natCmp]
        rw [hac2]

/-- Lexicographic three-way comparison on `CnfOrd` term lists. -/
@[expose] def cnfCmp (xs ys : CnfOrd) : Cmp3 :=
  (xs.foldr
    (fun a ih rem =>
      match rem with
      | [] => .gt
      | b :: tl =>
        match termCmp a b with
        | .lt => .lt
        | .gt => .gt
        | .eq => ih tl)
    (fun rem =>
      match rem with
      | [] => .eq
      | _ :: _ => .lt)) ys

/-- Strict `< ω^ω` Cantor Normal Form ordinal ordering. -/
@[expose] def cnfLt (xs ys : CnfOrd) : Bool :=
  match cnfCmp xs ys with
  | .lt => true
  | .eq => false
  | .gt => false

/-- Reflexive `≤` ordering on `CnfOrd`. -/
@[expose] def cnfBle (xs ys : CnfOrd) : Bool :=
  match cnfCmp xs ys with
  | .lt => true
  | .eq => true
  | .gt => false

/-- Reflexivity of `cnfCmp`. -/
theorem cnfCmpRefl (xs : CnfOrd) : cnfCmp xs xs = .eq := by
  induction xs with
  | nil => rfl
  | cons a _ ih =>
    change (match termCmp a a with
      | Cmp3.lt => Cmp3.lt | Cmp3.gt => Cmp3.gt
      | Cmp3.eq => cnfCmp _ _) = Cmp3.eq
    rw [termCmpRefl a]
    exact ih

/-- Irreflexivity of `cnfLt`. -/
theorem cnfLt_irrefl (xs : CnfOrd) : cnfLt xs xs = false := by
  dsimp only [cnfLt]
  rw [cnfCmpRefl xs]

/-- No `CnfOrd` is strictly below `[]` (`0`). -/
theorem cnfLt_nil_right (xs : CnfOrd) : cnfLt xs [] = false := by
  cases xs <;> rfl

/-- Reflexivity of `cnfBle`. -/
theorem cnfBle_refl (xs : CnfOrd) : cnfBle xs xs = true := by
  dsimp only [cnfBle]
  rw [cnfCmpRefl xs]

/-- Anticommutativity of `cnfCmp` under `cmpFlip`. -/
theorem cnfCmpFlip (xs ys : CnfOrd) :
    cnfCmp ys xs = cmpFlip (cnfCmp xs ys) := by
  revert ys
  induction xs with
  | nil =>
    intro ys
    cases ys <;> rfl
  | cons a xtl ih =>
    intro ys
    cases ys with
    | nil => rfl
    | cons b ytl =>
      change (match termCmp b a with
        | Cmp3.lt => Cmp3.lt | Cmp3.gt => Cmp3.gt
        | Cmp3.eq => cnfCmp ytl xtl) =
        cmpFlip (match termCmp a b with
          | Cmp3.lt => Cmp3.lt | Cmp3.gt => Cmp3.gt
          | Cmp3.eq => cnfCmp xtl ytl)
      rw [termCmpFlip a b]
      cases termCmp a b with
      | lt => rfl
      | gt => rfl
      | eq => exact ih ytl

/-- Asymmetry of `cnfLt`. -/
theorem cnfLt_asymm (xs ys : CnfOrd) (h : cnfLt xs ys = true) :
    cnfLt ys xs = false := by
  dsimp only [cnfLt] at h
  dsimp only [cnfLt]
  rw [cnfCmpFlip xs ys]
  cases hc : cnfCmp xs ys with
  | lt => rfl
  | eq => rw [hc] at h; exact False.elim (boolFalseNeTrue h)
  | gt => rw [hc] at h; exact False.elim (boolFalseNeTrue h)

/-- Mixed transitivity `xs < ys → ys ≤ zs → xs < zs`. -/
theorem cnfLt_of_lt_of_ble (xs ys zs : CnfOrd)
    (hxy : cnfLt xs ys = true) (hyz : cnfBle ys zs = true) :
    cnfLt xs zs = true := by
  revert ys zs
  induction xs with
  | nil =>
    intro ys zs hxy hyz
    cases ys with
    | nil => exact False.elim (boolFalseNeTrue hxy)
    | cons _ _ =>
      cases zs with
      | nil => exact False.elim (boolFalseNeTrue hyz)
      | cons _ _ => rfl
  | cons a xtl ih =>
    intro ys zs hxy hyz
    cases ys with
    | nil => exact False.elim (boolFalseNeTrue hxy)
    | cons b ytl =>
      cases zs with
      | nil => exact False.elim (boolFalseNeTrue hyz)
      | cons c ztl =>
        dsimp only [cnfLt, cnfCmp, List.foldr] at hxy
        dsimp only [cnfBle, cnfCmp, List.foldr] at hyz
        dsimp only [cnfLt, cnfCmp, List.foldr]
        cases hTab : termCmp a b with
        | gt => rw [hTab] at hxy; exact False.elim (boolFalseNeTrue hxy)
        | lt =>
          cases hTbc : termCmp b c with
          | gt => rw [hTbc] at hyz; exact False.elim (boolFalseNeTrue hyz)
          | lt =>
            have hTac := termCmpTransLtBle a b c hTab (by rw [hTbc])
            rw [hTac]
          | eq =>
            have hTac := termCmpTransLtBle a b c hTab (by rw [hTbc])
            rw [hTac]
        | eq =>
          rw [hTab] at hxy
          dsimp only at hxy
          have hAbEq : a = b := by
            dsimp only [termCmp] at hTab
            cases h1 : natCmp a.1 b.1 with
            | lt => rw [h1] at hTab; exact False.elim (Cmp3.noConfusion hTab)
            | gt => rw [h1] at hTab; exact False.elim (Cmp3.noConfusion hTab)
            | eq =>
              rw [h1] at hTab
              dsimp only at hTab
              have e1 := natCmpEqEq h1
              have e2 := natCmpEqEq hTab
              cases a with
              | mk _ _ =>
                cases b with
                | mk _ _ =>
                  dsimp only at e1 e2
                  rw [e1, e2]
          rw [hAbEq]
          cases hTbc : termCmp b c with
          | gt => rw [hTbc] at hyz; exact False.elim (boolFalseNeTrue hyz)
          | lt => rfl
          | eq =>
            rw [hTbc] at hyz
            dsimp only at hyz
            exact ih ytl ztl
              (by dsimp only [cnfLt]; exact hxy)
              (by dsimp only [cnfBle]; exact hyz)

/-- Transitivity of strict `< ω^ω` ordering `cnfLt`. -/
theorem cnfLt_trans (xs ys zs : CnfOrd)
    (hxy : cnfLt xs ys = true) (hyz : cnfLt ys zs = true) :
    cnfLt xs zs = true :=
  cnfLt_of_lt_of_ble xs ys zs hxy (by
    dsimp only [cnfLt] at hyz
    dsimp only [cnfBle]
    cases h : cnfCmp ys zs with
    | lt => rfl
    | eq => rfl
    | gt => rw [h] at hyz; exact False.elim (boolFalseNeTrue hyz))

/-- Soundness of `cnfCmp a b = .eq`: structural list equality `a = b`. -/
theorem cnfCmp_eq_imp_eq (a b : CnfOrd) (hc : cnfCmp a b = .eq) : a = b := by
  revert b
  induction a with
  | nil =>
    intro b hc
    cases b with
    | nil => rfl
    | cons _ _ => exact False.elim (Cmp3.noConfusion hc)
  | cons x xtl ih =>
    intro b hc
    cases b with
    | nil => exact False.elim (Cmp3.noConfusion hc)
    | cons y ytl =>
      dsimp only [cnfCmp, List.foldr] at hc
      cases ht : termCmp x y with
      | lt => rw [ht] at hc; exact False.elim (Cmp3.noConfusion hc)
      | gt => rw [ht] at hc; exact False.elim (Cmp3.noConfusion hc)
      | eq =>
        rw [ht] at hc
        dsimp only at hc
        dsimp only [termCmp] at ht
        cases h1 : natCmp x.1 y.1 with
        | lt => rw [h1] at ht; exact False.elim (Cmp3.noConfusion ht)
        | gt => rw [h1] at ht; exact False.elim (Cmp3.noConfusion ht)
        | eq =>
          rw [h1] at ht
          dsimp only at ht
          have e1 := natCmpEqEq h1
          have e2 := natCmpEqEq ht
          have eTl := ih ytl hc
          cases x with
          | mk _ _ =>
            cases y with
            | mk _ _ =>
              dsimp only at e1 e2
              rw [e1, e2, eTl]

/-- Transitivity of `cnfBle`. -/
theorem cnfBle_trans (a b c : CnfOrd)
    (hab : cnfBle a b = true) (hbc : cnfBle b c = true) :
    cnfBle a c = true := by
  dsimp only [cnfBle] at hab
  cases hc : cnfCmp a b with
  | gt => rw [hc] at hab; exact False.elim (boolFalseNeTrue hab)
  | lt =>
    have hLt := cnfLt_of_lt_of_ble a b c (by dsimp only [cnfLt]; rw [hc]) hbc
    dsimp only [cnfLt] at hLt
    dsimp only [cnfBle]
    cases h2 : cnfCmp a c with
    | lt => rfl
    | eq => rfl
    | gt => rw [h2] at hLt; exact False.elim (boolFalseNeTrue hLt)
  | eq =>
    rw [cnfCmp_eq_imp_eq a b hc]
    exact hbc

/-- Antisymmetry of `cnfBle`. -/
theorem cnfBle_antisymm (a b : CnfOrd)
    (hab : cnfBle a b = true) (hba : cnfBle b a = true) :
    a = b := by
  dsimp only [cnfBle] at hab hba
  rw [cnfCmpFlip a b] at hba
  cases hc : cnfCmp a b with
  | eq => exact cnfCmp_eq_imp_eq a b hc
  | gt => rw [hc] at hab; exact False.elim (boolFalseNeTrue hab)
  | lt => rw [hc] at hba; exact False.elim (boolFalseNeTrue hba)

/-! ## 3. Coefficient Extraction & Highest-Differing-Exponent Descent -/

/-- Total coefficient of `ω^q` in `xs`. -/
@[expose] def cnfCoeffAt (q : Nat) (xs : CnfOrd) : Nat :=
  xs.foldr
    (fun p acc => match Nat.beq p.1 q with | true => p.2 + acc | false => acc)
    0

/-- Terms strictly below exponent `q` contribute `0` to `cnfCoeffAt q`. -/
theorem cnfCoeffAt_zero_of_allBelow (q : Nat) (xs : CnfOrd)
    (h : cnfAllBelow q xs = true) :
    cnfCoeffAt q xs = 0 := by
  induction xs with
  | nil => rfl
  | cons p tl ih =>
    change (match Nat.beq p.1 q with
      | true => p.2 + cnfCoeffAt q tl | false => cnfCoeffAt q tl) = 0
    rw [natBeqFalseOfLt (bandLeft h)]
    exact ih (bandRight h)

/-- Head term coefficient extraction when tail exponents lie below `a.1`. -/
theorem cnfCoeffAt_cons_head (a : Nat × Nat) (tl : CnfOrd)
    (hBel : cnfAllBelow a.1 tl = true) :
    cnfCoeffAt a.1 (a :: tl) = a.2 := by
  change (match Nat.beq a.1 a.1 with
    | true => a.2 + cnfCoeffAt a.1 tl | false => cnfCoeffAt a.1 tl) = a.2
  rw [natBeq_refl a.1, cnfCoeffAt_zero_of_allBelow a.1 tl hBel]
  rfl

/-- Canonical uniqueness: two canonical CNF ordinals with equal coefficients at
every exponent are structurally identical. -/
theorem cnf_eq_of_coeff_eq (xs ys : CnfOrd)
    (hX : isCanonicalCnf xs = true) (hY : isCanonicalCnf ys = true)
    (hEq : ∀ (q : Nat), cnfCoeffAt q xs = cnfCoeffAt q ys) :
    xs = ys := by
  revert ys hY hEq
  induction xs with
  | nil =>
    intro ys hY hEq
    cases ys with
    | nil => rfl
    | cons b ytl =>
      rw [isCanonicalCnf_cons] at hY
      have h0 := hEq b.1
      rw [cnfCoeffAt_cons_head b ytl (bandRight (bandLeft hY))] at h0
      have hPos := bandLeft (bandLeft hY)
      rw [← h0] at hPos
      exact False.elim (boolFalseNeTrue hPos)
  | cons a xtl ih =>
    intro ys hY hEq
    cases ys with
    | nil =>
      rw [isCanonicalCnf_cons] at hX
      have h0 := hEq a.1
      rw [cnfCoeffAt_cons_head a xtl (bandRight (bandLeft hX))] at h0
      have hPos := bandLeft (bandLeft hX)
      rw [h0] at hPos
      exact False.elim (boolFalseNeTrue hPos)
    | cons b ytl =>
      rw [isCanonicalCnf_cons] at hX
      rw [isCanonicalCnf_cons] at hY
      have haPos := bandLeft (bandLeft hX)
      have haBel := bandRight (bandLeft hX)
      have hXtl := bandRight hX
      have hbPos := bandLeft (bandLeft hY)
      have hbBel := bandRight (bandLeft hY)
      have hYtl := bandRight hY
      cases hCmp : natCmp a.1 b.1 with
      | lt =>
        have h1 := hEq b.1
        have hZab := cnfCoeffAt_zero_of_allBelow b.1 xtl
          (cnfAllBelow_mono a.1 b.1 xtl
            (natBle_trans _ (a.1 + 1) b.1
              (natBle_succ_right _ _ (natBle_refl _))
              (natCmpLtToLt hCmp)) haBel)
        change (match Nat.beq a.1 b.1 with
          | true => a.2 + cnfCoeffAt b.1 xtl
          | false => cnfCoeffAt b.1 xtl) = _ at h1
        rw [natBeqFalseOfLt (natCmpLtToLt hCmp), hZab,
          cnfCoeffAt_cons_head b ytl hbBel] at h1
        rw [← h1] at hbPos
        exact False.elim (boolFalseNeTrue hbPos)
      | gt =>
        have h1 := hEq a.1
        have hZba := cnfCoeffAt_zero_of_allBelow a.1 ytl
          (cnfAllBelow_mono b.1 a.1 ytl
            (natBle_trans _ (b.1 + 1) a.1
              (natBle_succ_right _ _ (natBle_refl _))
              (natCmpGtToLt hCmp)) hbBel)
        change _ = (match Nat.beq b.1 a.1 with
          | true => b.2 + cnfCoeffAt a.1 ytl
          | false => cnfCoeffAt a.1 ytl) at h1
        rw [natBeqFalseOfLt (natCmpGtToLt hCmp), hZba,
          cnfCoeffAt_cons_head a xtl haBel] at h1
        rw [h1] at haPos
        exact False.elim (boolFalseNeTrue haPos)
      | eq =>
        have habEq := natCmpEqEq hCmp
        have hcEq : a.2 = b.2 := by
          have h1 := hEq a.1
          rw [cnfCoeffAt_cons_head a xtl haBel, habEq,
            cnfCoeffAt_cons_head b ytl hbBel] at h1
          exact h1
        have hTailEq := ih hXtl ytl hYtl (fun q => by
          cases hAq : Nat.beq a.1 q with
          | true =>
            rw [← natEq_of_beq a.1 q hAq,
              cnfCoeffAt_zero_of_allBelow a.1 xtl haBel,
              habEq, cnfCoeffAt_zero_of_allBelow b.1 ytl hbBel]
          | false =>
            have h1 := hEq q
            change (match Nat.beq a.1 q with
              | true => a.2 + cnfCoeffAt q xtl
              | false => cnfCoeffAt q xtl) =
              (match Nat.beq b.1 q with
                | true => b.2 + cnfCoeffAt q ytl
                | false => cnfCoeffAt q ytl) at h1
            rw [← habEq, hAq] at h1
            exact h1)
        cases a with
        | mk _ _ =>
          cases b with
          | mk _ _ =>
            dsimp only at habEq hcEq
            rw [habEq, hcEq, hTailEq]

private theorem cnf_coeff_contradiction_at_head (a : Nat × Nat)
    (xtl ys : CnfOrd) (haPos : natLt 0 a.2 = true)
    (haBel : cnfAllBelow a.1 xtl = true) (q0 : Nat)
    (hDrop : natLt (cnfCoeffAt q0 (a :: xtl)) (cnfCoeffAt q0 ys) = true)
    (hAbove : ∀ (q : Nat), natLt q0 q = true →
      cnfCoeffAt q (a :: xtl) = cnfCoeffAt q ys)
    (hYsZero : ∀ (q : Nat), Nat.ble a.1 q = true → cnfCoeffAt q ys = 0) :
    False := by
  cases hCmpQ : natCmp a.1 q0 with
  | gt =>
    have hEq := hAbove a.1 (natCmpGtToLt hCmpQ)
    rw [cnfCoeffAt_cons_head a xtl haBel,
      hYsZero a.1 (natBle_refl a.1)] at hEq
    rw [hEq] at haPos
    exact boolFalseNeTrue haPos
  | eq =>
    have hAeq := natCmpEqEq hCmpQ
    rw [← hAeq, cnfCoeffAt_cons_head a xtl haBel,
      hYsZero a.1 (natBle_refl a.1), natLtZeroRightFalse] at hDrop
    exact boolFalseNeTrue hDrop
  | lt =>
    have hAq := natCmpLtToLt hCmpQ
    have hLeAq : Nat.ble a.1 q0 = true :=
      natBle_trans a.1 (a.1 + 1) q0
        (natBle_succ_right a.1 a.1 (natBle_refl a.1)) hAq
    have hAllX : cnfAllBelow q0 (a :: xtl) = true :=
      bandIntro hAq (cnfAllBelow_mono a.1 q0 xtl hLeAq haBel)
    rw [cnfCoeffAt_zero_of_allBelow q0 (a :: xtl) hAllX,
      hYsZero q0 hLeAq] at hDrop
    exact boolFalseNeTrue hDrop

/-- Highest-differing-exponent `< ω^ω` descent: if `xs` and `ys` are canonical,
agree on all exponents `q > q0`, and `cnfCoeffAt q0 xs < cnfCoeffAt q0 ys`,
then `cnfLt xs ys = true` regardless of arbitrarily large growth below `q0`. -/
theorem cnfLt_of_coeff_drop (xs ys : CnfOrd)
    (hX : isCanonicalCnf xs = true) (hY : isCanonicalCnf ys = true)
    (q0 : Nat)
    (hDrop : natLt (cnfCoeffAt q0 xs) (cnfCoeffAt q0 ys) = true)
    (hAbove : ∀ (q : Nat), natLt q0 q = true →
      cnfCoeffAt q xs = cnfCoeffAt q ys) :
    cnfLt xs ys = true := by
  revert ys hY hDrop hAbove
  induction xs with
  | nil =>
    intro ys _ hDrop _
    cases ys with
    | nil => exact False.elim (boolFalseNeTrue hDrop)
    | cons _ _ => rfl
  | cons a xtl ih =>
    intro ys hY hDrop hAbove
    rw [isCanonicalCnf_cons] at hX
    have haPos := bandLeft (bandLeft hX)
    have haBel := bandRight (bandLeft hX)
    have hXtl := bandRight hX
    cases ys with
    | nil =>
      exact False.elim
        (cnf_coeff_contradiction_at_head a xtl [] haPos haBel q0 hDrop hAbove
          (fun _ _ => rfl))
    | cons b ytl =>
      rw [isCanonicalCnf_cons] at hY
      have hbBel := bandRight (bandLeft hY)
      have hYtl := bandRight hY
      dsimp only [cnfLt, cnfCmp, List.foldr, termCmp]
      cases hCmp1 : natCmp a.1 b.1 with
      | lt => rfl
      | gt =>
        have hba := natCmpGtToLt hCmp1
        have hYsZero :
            ∀ (q : Nat), Nat.ble a.1 q = true →
              cnfCoeffAt q (b :: ytl) = 0 := by
          intro q hLeAq
          have hBq : natLt b.1 q = true := natLtOfLtOfBle b.1 a.1 q hba hLeAq
          have hLeBq : Nat.ble b.1 q = true :=
            natBle_trans b.1 (b.1 + 1) q
              (natBle_succ_right b.1 b.1 (natBle_refl b.1)) hBq
          exact cnfCoeffAt_zero_of_allBelow q (b :: ytl)
            (bandIntro hBq (cnfAllBelow_mono b.1 q ytl hLeBq hbBel))
        exact False.elim
          (cnf_coeff_contradiction_at_head a xtl (b :: ytl) haPos haBel q0
            hDrop hAbove hYsZero)
      | eq =>
        have hab1 := natCmpEqEq hCmp1
        dsimp only
        cases hCmp2 : natCmp a.2 b.2 with
        | lt => rfl
        | gt =>
          have hba2 := natCmpGtToLt hCmp2
          cases hCmpQ : natCmp a.1 q0 with
          | gt =>
            have hEq := hAbove a.1 (natCmpGtToLt hCmpQ)
            rw [cnfCoeffAt_cons_head a xtl haBel, hab1,
              cnfCoeffAt_cons_head b ytl hbBel] at hEq
            rw [hEq, natLtIrrefl] at hba2
            exact False.elim (boolFalseNeTrue hba2)
          | eq =>
            have hAeq := natCmpEqEq hCmpQ
            rw [← hAeq, cnfCoeffAt_cons_head a xtl haBel, hab1,
              cnfCoeffAt_cons_head b ytl hbBel] at hDrop
            rw [natLtAsymm b.2 a.2 hba2] at hDrop
            exact False.elim (boolFalseNeTrue hDrop)
          | lt =>
            have hAq := natCmpLtToLt hCmpQ
            have hLeAq : Nat.ble a.1 q0 = true :=
              natBle_trans a.1 (a.1 + 1) q0
                (natBle_succ_right a.1 a.1 (natBle_refl a.1)) hAq
            have hAllX : cnfAllBelow q0 (a :: xtl) = true :=
              bandIntro hAq (cnfAllBelow_mono a.1 q0 xtl hLeAq haBel)
            have hBq : natLt b.1 q0 = true := by rw [← hab1]; exact hAq
            have hLeBq : Nat.ble b.1 q0 = true := by rw [← hab1]; exact hLeAq
            have hAllY : cnfAllBelow q0 (b :: ytl) = true :=
              bandIntro hBq (cnfAllBelow_mono b.1 q0 ytl hLeBq hbBel)
            rw [cnfCoeffAt_zero_of_allBelow q0 (a :: xtl) hAllX,
              cnfCoeffAt_zero_of_allBelow q0 (b :: ytl) hAllY] at hDrop
            exact False.elim (boolFalseNeTrue hDrop)
        | eq =>
          have hab2 := natCmpEqEq hCmp2
          dsimp only
          have hAq0False : Nat.beq a.1 q0 = false := by
            cases hAq0 : Nat.beq a.1 q0 with
            | false => rfl
            | true =>
              have hEqQ := natEq_of_beq a.1 q0 hAq0
              rw [← hEqQ, cnfCoeffAt_cons_head a xtl haBel, hab1,
                cnfCoeffAt_cons_head b ytl hbBel, hab2, natLtIrrefl] at hDrop
              exact False.elim (boolFalseNeTrue hDrop)
          have hDropTl : natLt (cnfCoeffAt q0 xtl) (cnfCoeffAt q0 ytl) = true := by
            change natLt
              (match Nat.beq a.1 q0 with
                | true => a.2 + cnfCoeffAt q0 xtl
                | false => cnfCoeffAt q0 xtl)
              (match Nat.beq b.1 q0 with
                | true => b.2 + cnfCoeffAt q0 ytl
                | false => cnfCoeffAt q0 ytl) = true at hDrop
            rw [← hab1, hAq0False] at hDrop
            exact hDrop
          have hAboveTl : ∀ (q : Nat), natLt q0 q = true →
              cnfCoeffAt q xtl = cnfCoeffAt q ytl := by
            intro q hGt
            cases hAq : Nat.beq a.1 q with
            | true =>
              have hEqQ := natEq_of_beq a.1 q hAq
              rw [← hEqQ, cnfCoeffAt_zero_of_allBelow a.1 xtl haBel,
                hab1, cnfCoeffAt_zero_of_allBelow b.1 ytl hbBel]
            | false =>
              have hEq := hAbove q hGt
              change (match Nat.beq a.1 q with
                | true => a.2 + cnfCoeffAt q xtl
                | false => cnfCoeffAt q xtl) =
                (match Nat.beq b.1 q with
                  | true => b.2 + cnfCoeffAt q ytl
                  | false => cnfCoeffAt q ytl) at hEq
              rw [← hab1, hAq] at hEq
              exact hEq
          have hSub := ih hXtl ytl hYtl hDropTl hAboveTl
          change cnfLt xtl ytl = true
          exact hSub

/-! ## 4. Hessenberg Natural Addition (`cnfAddTerm`, `cnfNorm`, `cnfNatAdd`) -/

/-- Inserts or merges `ω^e · c` into canonical CNF list `xs` (skipping `c = 0`).
-/
@[expose] def cnfAddTerm (e c : Nat) (xs : CnfOrd) : CnfOrd :=
  match c with
  | 0 => xs
  | c' + 1 =>
    let k := c' + 1
    listFold [(e, k)]
      (fun p tl ih =>
        match natCmp p.1 e with
        | .gt => p :: ih
        | .eq => (p.1, p.2 + k) :: tl
        | .lt => (e, k) :: p :: tl)
      xs

/-- Normalizes an arbitrary `(exp, coeff)` term list into canonical `CnfOrd`. -/
@[expose] def cnfNorm (xs : CnfOrd) : CnfOrd :=
  xs.foldr (fun p acc => cnfAddTerm p.1 p.2 acc) []

/-- Hessenberg natural addition `xs ⊕ ys` on `CnfOrd`. -/
@[expose] def cnfNatAdd (xs ys : CnfOrd) : CnfOrd :=
  xs.foldr (fun p acc => cnfAddTerm p.1 p.2 acc) (cnfNorm ys)

/-- Alias for Hessenberg natural addition `cnfNatAdd`. -/
abbrev cnfAddOrd : CnfOrd → CnfOrd → CnfOrd := cnfNatAdd

private theorem cnfAllBelow_cnfAddTerm (b e c : Nat) (xs : CnfOrd)
    (heb : natLt e b = true) (hxs : cnfAllBelow b xs = true) :
    cnfAllBelow b (cnfAddTerm e c xs) = true := by
  cases c with
  | zero => exact hxs
  | succ _ =>
    dsimp only [cnfAddTerm]
    induction xs with
    | nil => exact bandIntro heb rfl
    | cons p tl ih =>
      rw [listFold_cons]
      have hp := bandLeft hxs
      have htl := bandRight hxs
      cases natCmp p.1 e with
      | gt => exact bandIntro hp (ih htl)
      | eq => exact bandIntro hp htl
      | lt => exact bandIntro heb (bandIntro hp htl)

/-- `cnfAddTerm` preserves `isCanonicalCnf`. -/
theorem isCanonicalCnf_cnfAddTerm (e c : Nat) (xs : CnfOrd)
    (hCanon : isCanonicalCnf xs = true) :
    isCanonicalCnf (cnfAddTerm e c xs) = true := by
  cases c with
  | zero => exact hCanon
  | succ c' =>
    dsimp only [cnfAddTerm]
    induction xs with
    | nil => rfl
    | cons p tl ih =>
      rw [isCanonicalCnf_cons] at hCanon
      rw [listFold_cons]
      have hpPos := bandLeft (bandLeft hCanon)
      have hpBelow := bandRight (bandLeft hCanon)
      have htl := bandRight hCanon
      cases hCmp : natCmp p.1 e with
      | gt =>
        rw [isCanonicalCnf_cons]
        exact bandIntro
          (bandIntro hpPos
            (cnfAllBelow_cnfAddTerm p.1 e (c' + 1) tl
              (natCmpGtToLt hCmp) hpBelow))
          (ih htl)
      | eq =>
        rw [isCanonicalCnf_cons]
        exact bandIntro
          (bandIntro
            (natLtOfLtOfBle 0 p.2 (p.2 + (c' + 1)) hpPos
              (natBle_add_right p.2 (c' + 1)))
            hpBelow)
          htl
      | lt =>
        have hpe := natCmpLtToLt hCmp
        rw [isCanonicalCnf_cons, isCanonicalCnf_cons]
        exact bandIntro
          (bandIntro rfl
            (bandIntro hpe
              (cnfAllBelow_mono p.1 e tl
                (natBle_trans p.1 (p.1 + 1) e
                  (natBle_succ_right p.1 p.1 (natBle_refl p.1)) hpe)
                hpBelow)))
          (bandIntro (bandIntro hpPos hpBelow) htl)

/-- Exponent-wise coefficient law for `cnfAddTerm`. -/
theorem cnfCoeffAt_cnfAddTerm (q e c : Nat) (xs : CnfOrd) :
    cnfCoeffAt q (cnfAddTerm e c xs) =
      (match Nat.beq e q with | true => c | false => 0) + cnfCoeffAt q xs := by
  cases c with
  | zero =>
    cases Nat.beq e q <;> (rw [natAdd_zero_left]; rfl)
  | succ c' =>
    dsimp only [cnfAddTerm]
    induction xs with
    | nil =>
      change (match Nat.beq e q with | true => (c' + 1) + 0 | false => 0) = _
      cases Nat.beq e q <;> rfl
    | cons p tl ih =>
      rw [listFold_cons]
      cases hCmp : natCmp p.1 e with
      | gt =>
        change (match Nat.beq p.1 q with
          | true => p.2 + cnfCoeffAt q _ | false => cnfCoeffAt q _) =
          (match Nat.beq e q with | true => c' + 1 | false => 0) +
            (match Nat.beq p.1 q with
              | true => p.2 + cnfCoeffAt q tl | false => cnfCoeffAt q tl)
        rw [ih]
        cases Nat.beq p.1 q with
        | false => rfl
        | true =>
          exact Eq.symm (Eq.trans
            (Eq.symm (natAdd_assoc _ p.2 (cnfCoeffAt q tl)))
            (Eq.trans
              (congrArg (fun z => z + cnfCoeffAt q tl) (natAdd_comm _ p.2))
              (natAdd_assoc p.2 _ (cnfCoeffAt q tl))))
      | eq =>
        change (match Nat.beq p.1 q with
          | true => (p.2 + (c' + 1)) + cnfCoeffAt q tl
          | false => cnfCoeffAt q tl) =
          (match Nat.beq e q with | true => c' + 1 | false => 0) +
            (match Nat.beq p.1 q with
              | true => p.2 + cnfCoeffAt q tl | false => cnfCoeffAt q tl)
        rw [natCmpEqEq hCmp]
        cases Nat.beq e q with
        | false => rw [natAdd_zero_left]
        | true =>
          exact Eq.trans (natAdd_assoc p.2 (c' + 1) (cnfCoeffAt q tl))
            (Eq.trans
              (congrArg (Nat.add p.2)
                (natAdd_comm (c' + 1) (cnfCoeffAt q tl)))
              (Eq.trans
                (Eq.symm (natAdd_assoc p.2 (cnfCoeffAt q tl) (c' + 1)))
                (natAdd_comm (p.2 + cnfCoeffAt q tl) (c' + 1))))
      | lt =>
        change (match Nat.beq e q with
          | true => (c' + 1) + cnfCoeffAt q (p :: tl)
          | false => cnfCoeffAt q (p :: tl)) =
          (match Nat.beq e q with | true => c' + 1 | false => 0) +
            cnfCoeffAt q (p :: tl)
        cases Nat.beq e q with
        | false => rw [natAdd_zero_left]
        | true => rfl

/-- `cnfNorm xs` is unconditionally canonical (`isCanonicalCnf`). -/
theorem isCanonicalCnf_cnfNorm (xs : CnfOrd) :
    isCanonicalCnf (cnfNorm xs) = true := by
  induction xs with
  | nil => rfl
  | cons p _ ih => exact isCanonicalCnf_cnfAddTerm p.1 p.2 _ ih

/-- `cnfNorm` preserves every exponent's total coefficient. -/
theorem cnfCoeffAt_cnfNorm (q : Nat) (xs : CnfOrd) :
    cnfCoeffAt q (cnfNorm xs) = cnfCoeffAt q xs := by
  induction xs with
  | nil => rfl
  | cons p _ ih =>
    change cnfCoeffAt q (cnfAddTerm p.1 p.2 (cnfNorm _)) =
      match Nat.beq p.1 q with
      | true => p.2 + cnfCoeffAt q _
      | false => cnfCoeffAt q _
    rw [cnfCoeffAt_cnfAddTerm, ih]
    cases Nat.beq p.1 q with
    | true => rfl
    | false => rw [natAdd_zero_left]

/-- `cnfNorm` is the identity on canonical CNF ordinals. -/
theorem cnfNorm_eq_of_canonical (xs : CnfOrd) (hCan : isCanonicalCnf xs = true) :
    cnfNorm xs = xs :=
  cnf_eq_of_coeff_eq (cnfNorm xs) xs (isCanonicalCnf_cnfNorm xs) hCan
    (fun q => cnfCoeffAt_cnfNorm q xs)

/-- `cnfNatAdd` always produces a canonical `CnfOrd`. -/
theorem isCanonicalCnf_cnfNatAdd (xs ys : CnfOrd) :
    isCanonicalCnf (cnfNatAdd xs ys) = true := by
  induction xs with
  | nil => exact isCanonicalCnf_cnfNorm ys
  | cons p _ ih => exact isCanonicalCnf_cnfAddTerm p.1 p.2 _ ih

/-- Exponent-wise additivity of Hessenberg natural addition `cnfNatAdd`. -/
theorem cnfCoeffAt_cnfNatAdd (q : Nat) (xs ys : CnfOrd) :
    cnfCoeffAt q (cnfNatAdd xs ys) = cnfCoeffAt q xs + cnfCoeffAt q ys := by
  induction xs with
  | nil =>
    exact Eq.trans (cnfCoeffAt_cnfNorm q ys)
      (Eq.symm (natAdd_zero_left (cnfCoeffAt q ys)))
  | cons p tl ih =>
    change cnfCoeffAt q (cnfAddTerm p.1 p.2 (cnfNatAdd tl ys)) =
      (match Nat.beq p.1 q with
        | true => p.2 + cnfCoeffAt q tl
        | false => cnfCoeffAt q tl) + cnfCoeffAt q ys
    rw [cnfCoeffAt_cnfAddTerm, ih]
    cases Nat.beq p.1 q with
    | true => exact Eq.symm (natAdd_assoc p.2 (cnfCoeffAt q tl) (cnfCoeffAt q ys))
    | false => rw [natAdd_zero_left]

/-- Commutativity of Hessenberg natural addition `cnfNatAdd`. -/
theorem cnfNatAdd_comm (xs ys : CnfOrd) :
    cnfNatAdd xs ys = cnfNatAdd ys xs :=
  cnf_eq_of_coeff_eq _ _
    (isCanonicalCnf_cnfNatAdd xs ys) (isCanonicalCnf_cnfNatAdd ys xs)
    (fun q => Eq.trans (cnfCoeffAt_cnfNatAdd q xs ys)
      (Eq.trans (natAdd_comm _ _) (Eq.symm (cnfCoeffAt_cnfNatAdd q ys xs))))

/-- Associativity of Hessenberg natural addition `cnfNatAdd`. -/
theorem cnfNatAdd_assoc (xs ys zs : CnfOrd) :
    cnfNatAdd (cnfNatAdd xs ys) zs = cnfNatAdd xs (cnfNatAdd ys zs) :=
  cnf_eq_of_coeff_eq _ _
    (isCanonicalCnf_cnfNatAdd _ zs) (isCanonicalCnf_cnfNatAdd xs _)
    (fun q => Eq.trans (cnfCoeffAt_cnfNatAdd q _ zs)
      (Eq.trans
        (congrArg (fun z => z + cnfCoeffAt q zs) (cnfCoeffAt_cnfNatAdd q xs ys))
        (Eq.trans (natAdd_assoc _ _ _)
          (Eq.trans
            (congrArg (Nat.add (cnfCoeffAt q xs))
              (Eq.symm (cnfCoeffAt_cnfNatAdd q ys zs)))
            (Eq.symm (cnfCoeffAt_cnfNatAdd q xs _))))))

/-- Inflation `xs ≤ cnfAddTerm e c xs`. -/
theorem cnfBle_cnfAddTerm (e c : Nat) (xs : CnfOrd) :
    cnfBle xs (cnfAddTerm e c xs) = true := by
  cases c with
  | zero => exact cnfBle_refl xs
  | succ c' =>
    dsimp only [cnfAddTerm]
    induction xs with
    | nil => rfl
    | cons p tl ih =>
      rw [listFold_cons]
      cases hCmp : natCmp p.1 e with
      | gt =>
        dsimp only [cnfBle, cnfCmp, List.foldr]
        rw [termCmpRefl p]
        exact ih
      | eq =>
        dsimp only [cnfBle, cnfCmp, List.foldr, termCmp]
        rw [natCmpRefl p.1]
        dsimp only [natCmp]
        have hLt2 : natLt p.2 (p.2 + (c' + 1)) = true := by
          dsimp only [natLt]
          have hAssocEq : p.2 + (c' + 1) = (p.2 + 1) + c' := by
            rw [natAdd_comm c' 1, ← natAdd_assoc p.2 1 c']
          rw [hAssocEq]
          exact natBle_add_right (p.2 + 1) c'
        rw [hLt2]
      | lt =>
        dsimp only [cnfBle, cnfCmp, List.foldr, termCmp]
        rw [hCmp]

/-- Inflation `inp ≤ cnfAddOrd ordSpent inp` for canonical `inp`. -/
theorem cnfBle_cnfAddOrd_right (ordSpent inp : CnfOrd)
    (hCan : isCanonicalCnf inp = true) :
    cnfBle inp (cnfAddOrd ordSpent inp) = true := by
  have hAux : cnfBle (cnfNorm inp) (cnfAddOrd ordSpent inp) = true := by
    induction ordSpent with
    | nil => exact cnfBle_refl (cnfNorm inp)
    | cons p _ ih =>
      exact cnfBle_trans _ _ _ ih (cnfBle_cnfAddTerm p.1 p.2 _)
  rw [cnfNorm_eq_of_canonical inp hCan] at hAux
  exact hAux

/-- Adding `ordSpent` to the right-hand side of `<` preserves `cnfLt`. -/
theorem cnfLt_cnfAddOrd_of_lt (ordSpent out inp : CnfOrd)
    (hCanIn : isCanonicalCnf inp = true) (hLt : cnfLt out inp = true) :
    cnfLt out (cnfAddOrd ordSpent inp) = true :=
  cnfLt_of_lt_of_ble out inp (cnfAddOrd ordSpent inp) hLt
    (cnfBle_cnfAddOrd_right ordSpent inp hCanIn)

/-! ## 5. Constructive Gentzen `< ω^ω` Accessibility & Abstract Convergence -/

/-- Constructive `< ω^ω` accessibility predicate over canonical `CnfOrd`. -/
inductive CnfAcc : CnfOrd → Prop where
  | intro (x : CnfOrd)
      (step : ∀ (y : CnfOrd),
        isCanonicalCnf y = true → cnfLt y x = true → CnfAcc y) :
      CnfAcc x

/-- `0` (`[]`) is `< ω^ω`-accessible. -/
theorem cnfAcc_nil : CnfAcc [] :=
  CnfAcc.intro [] (fun y _ hLt => by
    cases y <;> exact False.elim (boolFalseNeTrue hLt))

/-- Prepending `(b, m + 1)` preserves `CnfAcc` whenever all canonical ordinals
with exponents `< b` are `CnfAcc`. -/
theorem cnfAcc_prepend (b : Nat)
    (ihB : ∀ (xs : CnfOrd),
      isCanonicalCnf xs = true → cnfAllBelow b xs = true → CnfAcc xs) :
    ∀ (c m : Nat) (tl : CnfOrd),
      Nat.ble m c = true →
      isCanonicalCnf tl = true →
      cnfAllBelow b tl = true →
      CnfAcc tl →
      CnfAcc ((b, m + 1) :: tl) := by
  intro c
  induction c with
  | zero =>
    intro m tl hLe hCanTl hBelTl hAccTl
    induction hAccTl with
    | intro tlCur _ ihTl =>
      refine CnfAcc.intro ((b, m + 1) :: tlCur) (fun y hCanY hLtY => ?_)
      cases y with
      | nil => exact cnfAcc_nil
      | cons p ytl =>
        rw [isCanonicalCnf_cons] at hCanY
        have hpPos := bandLeft (bandLeft hCanY)
        have hpBel := bandRight (bandLeft hCanY)
        have hCanYtl := bandRight hCanY
        change (match
          match termCmp p (b, m + 1) with
          | Cmp3.lt => Cmp3.lt | Cmp3.gt => Cmp3.gt
          | Cmp3.eq => cnfCmp ytl tlCur with
          | Cmp3.lt => true | Cmp3.eq => false | Cmp3.gt => false) = true
          at hLtY
        dsimp only [termCmp] at hLtY
        cases hCmp1 : natCmp p.1 b with
        | gt => rw [hCmp1] at hLtY; exact False.elim (boolFalseNeTrue hLtY)
        | lt =>
          have hPb := natCmpLtToLt hCmp1
          exact ihB (p :: ytl)
            (by
              rw [isCanonicalCnf_cons]
              exact bandIntro (bandIntro hpPos hpBel) hCanYtl)
            (bandIntro hPb
              (cnfAllBelow_mono p.1 b ytl
                (natBle_trans _ (p.1 + 1) b
                  (natBle_succ_right _ _ (natBle_refl _)) hPb)
                hpBel))
        | eq =>
          have hpe := natCmpEqEq hCmp1
          rw [hCmp1] at hLtY
          dsimp only at hLtY
          cases hCmp2 : natCmp p.2 (m + 1) with
          | gt => rw [hCmp2] at hLtY; exact False.elim (boolFalseNeTrue hLtY)
          | lt =>
            have hP2m := natBle_trans (p.2 + 1) (m + 1) 1 (natCmpLtToLt hCmp2)
              (natBle_trans (m + 1) (0 + 1) 1 hLe (natBle_refl 1))
            cases hp2 : p.2 with
            | zero => rw [hp2] at hpPos; exact False.elim (boolFalseNeTrue hpPos)
            | succ _ =>
              rw [hp2] at hP2m
              exact False.elim (boolFalseNeTrue hP2m)
          | eq =>
            rw [hCmp2] at hLtY
            dsimp only at hLtY
            have hp2Eq := natCmpEqEq hCmp2
            have hSubLt : cnfLt ytl tlCur = true := by
              dsimp only [cnfLt]
              cases hc : cnfCmp ytl tlCur with
              | lt => rfl
              | eq => rw [hc] at hLtY; exact False.elim (boolFalseNeTrue hLtY)
              | gt => rw [hc] at hLtY; exact False.elim (boolFalseNeTrue hLtY)
            have hEqP : p = (b, m + 1) := by
              cases p with
              | mk _ _ => dsimp only at hpe hp2Eq; rw [hpe, hp2Eq]
            rw [hEqP]
            rw [hpe] at hpBel
            exact ihTl ytl hCanYtl hSubLt hCanYtl hpBel
  | succ c' ihC =>
    intro m tl hLe hCanTl hBelTl hAccTl
    induction hAccTl with
    | intro tlCur _ ihTl =>
      refine CnfAcc.intro ((b, m + 1) :: tlCur) (fun y hCanY hLtY => ?_)
      cases y with
      | nil => exact cnfAcc_nil
      | cons p ytl =>
        rw [isCanonicalCnf_cons] at hCanY
        have hpPos := bandLeft (bandLeft hCanY)
        have hpBel := bandRight (bandLeft hCanY)
        have hCanYtl := bandRight hCanY
        change (match
          match termCmp p (b, m + 1) with
          | Cmp3.lt => Cmp3.lt | Cmp3.gt => Cmp3.gt
          | Cmp3.eq => cnfCmp ytl tlCur with
          | Cmp3.lt => true | Cmp3.eq => false | Cmp3.gt => false) = true
          at hLtY
        dsimp only [termCmp] at hLtY
        cases hCmp1 : natCmp p.1 b with
        | gt => rw [hCmp1] at hLtY; exact False.elim (boolFalseNeTrue hLtY)
        | lt =>
          have hPb := natCmpLtToLt hCmp1
          exact ihB (p :: ytl)
            (by
              rw [isCanonicalCnf_cons]
              exact bandIntro (bandIntro hpPos hpBel) hCanYtl)
            (bandIntro hPb
              (cnfAllBelow_mono p.1 b ytl
                (natBle_trans _ (p.1 + 1) b
                  (natBle_succ_right _ _ (natBle_refl _)) hPb)
                hpBel))
        | eq =>
          have hpe := natCmpEqEq hCmp1
          rw [hCmp1] at hLtY
          dsimp only at hLtY
          cases hCmp2 : natCmp p.2 (m + 1) with
          | gt => rw [hCmp2] at hLtY; exact False.elim (boolFalseNeTrue hLtY)
          | lt =>
            have hP2 := natCmpLtToLt hCmp2
            cases hp2 : p.2 with
            | zero => rw [hp2] at hpPos; exact False.elim (boolFalseNeTrue hpPos)
            | succ p2' =>
              rw [hp2] at hP2
              have hP2LeC := natBle_trans (p2' + 1) m (c' + 1) hP2 hLe
              have hEqP : p = (b, p2' + 1) := by
                cases p with
                | mk _ _ => dsimp only at hpe hp2; rw [hpe, hp2]
              rw [hEqP]
              rw [hpe] at hpBel
              exact ihC p2' ytl hP2LeC hCanYtl hpBel (ihB ytl hCanYtl hpBel)
          | eq =>
            rw [hCmp2] at hLtY
            dsimp only at hLtY
            have hp2Eq := natCmpEqEq hCmp2
            have hSubLt : cnfLt ytl tlCur = true := by
              dsimp only [cnfLt]
              cases hc : cnfCmp ytl tlCur with
              | lt => rfl
              | eq => rw [hc] at hLtY; exact False.elim (boolFalseNeTrue hLtY)
              | gt => rw [hc] at hLtY; exact False.elim (boolFalseNeTrue hLtY)
            have hEqP : p = (b, m + 1) := by
              cases p with
              | mk _ _ => dsimp only at hpe hp2Eq; rw [hpe, hp2Eq]
            rw [hEqP]
            rw [hpe] at hpBel
            exact ihTl ytl hCanYtl hSubLt hCanYtl hpBel

/-- Every canonical `CnfOrd` with exponents `< bound` is `CnfAcc` (`< ω^bound`
accessibility). -/
theorem cnfAcc_below_bound (bound : Nat) :
    ∀ (xs : CnfOrd),
      isCanonicalCnf xs = true → cnfAllBelow bound xs = true → CnfAcc xs := by
  induction bound with
  | zero =>
    intro xs _ hBel
    cases xs with
    | nil => exact cnfAcc_nil
    | cons p tl =>
      change (natLt p.1 0 && cnfAllBelow 0 tl) = true at hBel
      have h0 := bandLeft hBel
      rw [natLtZeroRightFalse p.1] at h0
      exact False.elim (boolFalseNeTrue h0)
  | succ b ihB =>
    intro xs hCan hBel
    cases xs with
    | nil => exact cnfAcc_nil
    | cons p tl =>
      rw [isCanonicalCnf_cons] at hCan
      have hpPos := bandLeft (bandLeft hCan)
      have hpBel := bandRight (bandLeft hCan)
      have hCanTl := bandRight hCan
      cases hLtB : natLt p.1 b with
      | true =>
        exact ihB (p :: tl)
          (by
            rw [isCanonicalCnf_cons]
            exact bandIntro (bandIntro hpPos hpBel) hCanTl)
          (bandIntro hLtB
            (cnfAllBelow_mono p.1 b tl
              (natBle_trans _ (p.1 + 1) b
                (natBle_succ_right _ _ (natBle_refl _)) hLtB)
              hpBel))
      | false =>
        have hpEqB := natBle_antisym p.1 b (bandLeft hBel)
          (natBleOfLtFalse p.1 b hLtB)
        cases hp2 : p.2 with
        | zero => rw [hp2] at hpPos; exact False.elim (boolFalseNeTrue hpPos)
        | succ m =>
          have hEqP : p = (b, m + 1) := by
            cases p with
            | mk _ _ => dsimp only at hpEqB hp2; rw [hpEqB, hp2]
          rw [hEqP]
          rw [hpEqB] at hpBel
          exact cnfAcc_prepend b ihB m m tl (natBle_refl m) hCanTl hpBel
            (ihB tl hCanTl hpBel)

/-- Constructive Gentzen `< ω^ω` accessibility theorem (`[]` zero axioms):
every canonical `CnfOrd` is `CnfAcc`. -/
theorem cnfAcc_all (ord : CnfOrd) (hCan : isCanonicalCnf ord = true) :
    CnfAcc ord := by
  cases ord with
  | nil => exact cnfAcc_nil
  | cons p tl =>
    rw [isCanonicalCnf_cons] at hCan
    exact cnfAcc_below_bound (p.1 + 1) (p :: tl)
      (by rw [isCanonicalCnf_cons]; exact hCan)
      (bandIntro (natBle_refl (p.1 + 1))
        (cnfAllBelow_mono p.1 (p.1 + 1) tl
          (natBle_succ_right p.1 p.1 (natBle_refl p.1))
          (bandRight (bandLeft hCan))))

/-- Fuel-free inductive convergence judgment for an abstract partial step
function `step : α → Option α` (`none` = quiescent terminal state, `some s'` =
active step to `s'`) measured by `measure : α → CnfOrd`. -/
inductive CnfStepConverges {α : Type} (step : α → Option α)
    (measure : α → CnfOrd) : α → α → Prop where
  | quiescent (s : α) (hDone : step s = none) :
      CnfStepConverges step measure s s
  | step (s sNext sFinal : α)
      (hStep : step s = some sNext)
      (hLt : cnfLt (cnfNorm (measure sNext)) (cnfNorm (measure s)) = true)
      (hRest : CnfStepConverges step measure sNext sFinal) :
      CnfStepConverges step measure s sFinal

/-- Computable `@Nat.rec` bounded runner for `step : α → Option α`. -/
@[expose] def cnfStepRun {α : Type} (fuel : Nat) (step : α → Option α) (s : α) :
    Option α :=
  @Nat.rec (fun _ => α → Option α)
    (fun _ => none)
    (fun _ ih cur =>
      match step cur with
      | none => some cur
      | some next => ih next)
    fuel s

/-- Constructive fuel extraction from `CnfStepConverges`. -/
theorem cnfStepConverges_extract_fuel {α : Type} (step : α → Option α)
    (measure : α → CnfOrd) (s sFinal : α)
    (hConv : CnfStepConverges step measure s sFinal) :
    step sFinal = none ∧ ∃ fuel : Nat, cnfStepRun fuel step s = some sFinal := by
  induction hConv with
  | quiescent s0 hDone =>
    refine ⟨hDone, ⟨1, ?_⟩⟩
    change (match step s0 with | none => some s0 | some _ => none) = some s0
    rw [hDone]
  | step s0 s1 sf hSt _ _ ih =>
    cases ih.2 with
    | intro f hf =>
      refine ⟨ih.1, ⟨f + 1, ?_⟩⟩
      change (match step s0 with
        | none => some s0
        | some next => cnfStepRun f step next) = some sf
      rw [hSt]
      exact hf

/-- General `< ω^ω` termination theorem (`[]` zero axioms): any transition
system `step : α → Option α` preserving `Inv` and strictly decreasing
`cnfNorm (measure s)` reaches a quiescent `Inv` state in finite fuel. -/
theorem cnfStep_terminates_all {α : Type} (step : α → Option α)
    (measure : α → CnfOrd) (Inv : α → Prop)
    (hDesc : ∀ (s s' : α), Inv s → step s = some s' →
      Inv s' ∧ cnfLt (cnfNorm (measure s')) (cnfNorm (measure s)) = true)
    (s0 : α) (hInv0 : Inv s0) :
    ∃ sFinal : α,
      Inv sFinal ∧
      CnfStepConverges step measure s0 sFinal ∧
      step sFinal = none ∧
      (∃ fuel : Nat, cnfStepRun fuel step s0 = some sFinal) := by
  have hAux :
      ∀ (ord : CnfOrd), isCanonicalCnf ord = true →
      ∀ (s : α), Inv s → cnfNorm (measure s) = ord →
      ∃ sFinal : α, Inv sFinal ∧ CnfStepConverges step measure s sFinal := by
    intro ord hCan
    induction cnfAcc_all ord hCan with
    | intro x _ ih =>
      intro s hInv hMeas
      cases hSt : step s with
      | none => exact ⟨s, hInv, CnfStepConverges.quiescent s hSt⟩
      | some sNext =>
        have hStepOk := hDesc s sNext hInv hSt
        have hLtX : cnfLt (cnfNorm (measure sNext)) x = true := by
          rw [← hMeas]; exact hStepOk.2
        have hCanNext := isCanonicalCnf_cnfNorm (measure sNext)
        cases ih (cnfNorm (measure sNext)) hCanNext hLtX hCanNext
            sNext hStepOk.1 rfl with
        | intro sFinal hRest =>
          exact ⟨sFinal, hRest.1,
            CnfStepConverges.step s sNext sFinal hSt hStepOk.2 hRest.2⟩
  cases hAux (cnfNorm (measure s0)) (isCanonicalCnf_cnfNorm (measure s0))
      s0 hInv0 rfl with
  | intro sFinal hConv =>
    have hEx := cnfStepConverges_extract_fuel step measure s0 sFinal hConv.2
    exact ⟨sFinal, hConv.1, hConv.2, hEx.1, hEx.2⟩

end Anneal.CnfOrd

end
