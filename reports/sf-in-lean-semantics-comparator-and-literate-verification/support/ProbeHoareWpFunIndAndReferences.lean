-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Lean.Replay

set_option Elab.async false

/-!
# Hoare/WP VCs, Functional Induction, Store Typing, and Axiom Closures

This self-contained Lean `v4.34.1` probe (`lean --run`) mechanizes and measures:

1. **Part 1 (`HoareVCProbe`):**
   - Relational Hoare-rule composition (`hoare_seq`, `hoare_if`, `hoare_while`,
     `hoare_consequence`),
   - `HL/Hoare2.lean` Full Decorated Programs (`FullDCom`,
     `verificationConditions`, `full_verification_correct`),
   - `HL/Hoare2.lean` Sparse Annotations with backward weakest liberal
     preconditions (`SparseDCom`, `awp`, `verificationConditions`,
     `sparse_verification_correct`), evaluated across `diamondProg`,
     `chain8Prog`, and `loopProg`.

2. **Part 2 (`FunInductionProbe`):**
   - Multi-constructor AST optimization passes with wildcard fallthroughs
     (`| _ =>`), comparing structural `induction`/`cases` against Lean 4's
     `fun_induction` and `fun_cases` on:
     (a) a recursive 8-constructor arithmetic optimizer `optimizeAExp`, and
     (b) Anneal's non-recursive 4-level pattern match `optMirConstPropStmt`.

3. **Part 3 (`ReferencesProbe`):**
   - `TS/References.lean` (`STLCRef`) mutable store (`Store := List Tm`), store
     typing (`StoreTy := List Ty`, `StoreWellTyped`), monotonic store extension
     (`Extends`), `store_weakening`, `store_well_typed_alloc`,
     `assign_pres_store_typing`, `preservation`, and a 2-cell cyclic heap store
     well-typedness witness (`cyclic_store_well_typed`).

4. **Part 4 (`AxiomClosureProbe`):**
   - Exact transitive axiom closures and shortest dependency paths of `omega`,
     `lia`, and `grind` across atomic `Nat` addition (`omega_nat_add`), `Nat`
     subtraction (`omega_nat_sub`, `omega_nat_sub_fn`), and propositional
     conjunction (`omega_nat_conj`).
-/

namespace ProbeHoareWpFunIndAndReferences

/-!
## Part 1: Operational Semantics, Hoare Rules, and VCs (`HoareVCProbe`)
-/

namespace HoareVCProbe

abbrev State := Nat → Nat

def State.update (st : State) (x v : Nat) : State :=
  fun y => if y == x then v else st y

@[simp]
theorem State.update_eq (st : State) (x v : Nat) :
    State.update st x v x = v := by
  dsimp [State.update]
  have h : (x == x) = true := decide_eq_true rfl
  rw [h]
  rfl

@[simp]
theorem State.update_neq (st : State) (x y v : Nat) (h : y ≠ x) :
    State.update st x v y = st y := by
  dsimp [State.update]
  have hbeq : (y == x) = false := decide_eq_false h
  rw [hbeq]
  rfl

inductive AExp where
  | num (n : Nat)
  | var (x : Nat)
  | add (a1 a2 : AExp)
  | sub (a1 a2 : AExp)
  | mul (a1 a2 : AExp)
  | bitAnd (a1 a2 : AExp)
  | bitOr (a1 a2 : AExp)
  | shl (a1 a2 : AExp)

@[simp]
def AExp.eval (st : State) : AExp → Nat
  | .num n => n
  | .var x => st x
  | .add a1 a2 => a1.eval st + a2.eval st
  | .sub a1 a2 => a1.eval st - a2.eval st
  | .mul a1 a2 => a1.eval st * a2.eval st
  | .bitAnd a1 a2 => Nat.land (a1.eval st) (a2.eval st)
  | .bitOr a1 a2 => Nat.lor (a1.eval st) (a2.eval st)
  | .shl a1 a2 => (a1.eval st) <<< (a2.eval st)

inductive BExp where
  | btrue
  | bfalse
  | beq (a1 a2 : AExp)
  | ble (a1 a2 : AExp)
  | bnot (b : BExp)
  | band (b1 b2 : BExp)

@[simp]
theorem nat_ble_zero_eq_true (n : Nat) :
    (Nat.ble n 0 = true) ↔ n = 0 := by
  cases n <;> simp [Nat.ble]

@[simp]
theorem nat_ble_zero_eq_false (n : Nat) :
    (Nat.ble n 0 = false) ↔ 0 < n := by
  cases n with
  | zero => simp [Nat.ble]
  | succ k =>
    simp [Nat.ble, Nat.zero_lt_succ]

@[simp]
def BExp.eval (st : State) : BExp → Bool
  | .btrue => true
  | .bfalse => false
  | .beq a1 a2 => a1.eval st == a2.eval st
  | .ble a1 a2 => Nat.ble (a1.eval st) (a2.eval st)
  | .bnot b => !(b.eval st)
  | .band b1 b2 => b1.eval st && b2.eval st

inductive Com where
  | skip
  | asgn (x : Nat) (a : AExp)
  | seq (c1 c2 : Com)
  | cond (b : BExp) (c1 c2 : Com)
  | whileDo (b : BExp) (body : Com)

inductive CEval : Com → State → State → Prop where
  | skip (st : State) :
      CEval .skip st st
  | asgn (st : State) (x : Nat) (a : AExp) :
      CEval (.asgn x a) st (State.update st x (a.eval st))
  | seq {c1 c2 : Com} {st st' st'' : State} :
      CEval c1 st st' →
      CEval c2 st' st'' →
      CEval (.seq c1 c2) st st''
  | ifTrue {b : BExp} {c1 c2 : Com} {st st' : State} :
      b.eval st = true →
      CEval c1 st st' →
      CEval (.cond b c1 c2) st st'
  | ifFalse {b : BExp} {c1 c2 : Com} {st st' : State} :
      b.eval st = false →
      CEval c2 st st' →
      CEval (.cond b c1 c2) st st'
  | whileFalse {b : BExp} {body : Com} {st : State} :
      b.eval st = false →
      CEval (.whileDo b body) st st
  | whileTrue {b : BExp} {body : Com} {st st' st'' : State} :
      b.eval st = true →
      CEval body st st' →
      CEval (.whileDo b body) st' st'' →
      CEval (.whileDo b body) st st''

abbrev Assertion := State → Prop

@[reducible]
def AssertImplies (P Q : Assertion) : Prop :=
  ∀ st, P st → Q st

@[reducible]
def Assertion.subst (P : Assertion) (x : Nat) (a : AExp) : Assertion :=
  fun st => P (State.update st x (a.eval st))

def ValidHoareTriple (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ st st', CEval c st st' → P st → Q st'

theorem hoare_skip (P : Assertion) :
    ValidHoareTriple P .skip P := by
  intro st st' h hp
  cases h
  exact hp

theorem hoare_asgn (Q : Assertion) (x : Nat) (a : AExp) :
    ValidHoareTriple (Q.subst x a) (.asgn x a) Q := by
  intro st st' h hp
  cases h
  exact hp

theorem hoare_seq {P Q R : Assertion} {c1 c2 : Com}
    (h1 : ValidHoareTriple P c1 Q)
    (h2 : ValidHoareTriple Q c2 R) :
    ValidHoareTriple P (.seq c1 c2) R := by
  intro st st' h hp
  cases h with
  | seq hc1 hc2 =>
    exact h2 _ _ hc2 (h1 _ _ hc1 hp)

theorem hoare_consequence {P P' Q Q' : Assertion} {c : Com}
    (vt : ValidHoareTriple P' c Q')
    (hpre : AssertImplies P P')
    (hpost : AssertImplies Q' Q) :
    ValidHoareTriple P c Q := by
  intro st st' h hp
  exact hpost st' (vt st st' h (hpre st hp))

theorem hoare_consequence_pre {P P' Q : Assertion} {c : Com}
    (vt : ValidHoareTriple P' c Q)
    (hpre : AssertImplies P P') :
    ValidHoareTriple P c Q :=
  hoare_consequence vt hpre (fun _ h => h)

theorem hoare_if {P Q : Assertion} {b : BExp} {c1 c2 : Com}
    (h1 : ValidHoareTriple (fun st => P st ∧ b.eval st = true) c1 Q)
    (h2 : ValidHoareTriple (fun st => P st ∧ b.eval st = false) c2 Q) :
    ValidHoareTriple P (.cond b c1 c2) Q := by
  intro st st' h hp
  cases h with
  | ifTrue hb hc1 => exact h1 st st' hc1 ⟨hp, hb⟩
  | ifFalse hb hc2 => exact h2 st st' hc2 ⟨hp, hb⟩

theorem hoare_while {P : Assertion} {b : BExp} {body : Com}
    (hbody : ValidHoareTriple (fun st => P st ∧ b.eval st = true) body P) :
    ValidHoareTriple P (.whileDo b body)
      (fun st => P st ∧ b.eval st = false) := by
  intro st st' h hp
  generalize hw : Com.whileDo b body = w at h
  induction h with
  | skip => cases hw
  | asgn => cases hw
  | seq => cases hw
  | ifTrue => cases hw
  | ifFalse => cases hw
  | whileFalse hb =>
    injection hw with hb_eq _
    subst hb_eq
    exact ⟨hp, hb⟩
  | whileTrue hb hstep _ _ ih2 =>
    injection hw with hb_eq hbody_eq
    subst hb_eq
    subst hbody_eq
    exact ih2 (hbody _ _ hstep ⟨hp, hb⟩) rfl

/-!
### Architecture 2: `HL/Hoare2.lean` Full Decorated Programs (`FullDCom`)
-/

inductive FullDCom where
  | skip (Q : Assertion)
  | asgn (x : Nat) (a : AExp) (Q : Assertion)
  | seq (d1 d2 : FullDCom)
  | cond (b : BExp) (P1 : Assertion) (d1 : FullDCom)
      (P2 : Assertion) (d2 : FullDCom) (Q : Assertion)
  | whileDo (b : BExp) (Pbody : Assertion) (d : FullDCom) (Q : Assertion)

@[simp]
def FullDCom.erase : FullDCom → Com
  | .skip _ => .skip
  | .asgn x a _ => .asgn x a
  | .seq d1 d2 => .seq d1.erase d2.erase
  | .cond b _ d1 _ d2 _ => .cond b d1.erase d2.erase
  | .whileDo b _ d _ => .whileDo b d.erase

@[simp]
def FullDCom.post : FullDCom → Assertion
  | .skip Q => Q
  | .asgn _ _ Q => Q
  | .seq _ d2 => d2.post
  | .cond _ _ _ _ _ Q => Q
  | .whileDo _ _ _ Q => Q

@[simp]
def FullDCom.verificationConditions (P : Assertion) : FullDCom → Prop
  | .skip Q => AssertImplies P Q
  | .asgn x a Q => AssertImplies P (Q.subst x a)
  | .seq d1 d2 =>
    d1.verificationConditions P ∧ d2.verificationConditions d1.post
  | .cond b P1 d1 P2 d2 Q =>
    AssertImplies (fun st => P st ∧ b.eval st = true) P1 ∧
    AssertImplies (fun st => P st ∧ b.eval st = false) P2 ∧
    AssertImplies d1.post Q ∧
    AssertImplies d2.post Q ∧
    d1.verificationConditions P1 ∧
    d2.verificationConditions P2
  | .whileDo b Pbody d Q =>
    AssertImplies P d.post ∧
    AssertImplies (fun st => d.post st ∧ b.eval st = true) Pbody ∧
    AssertImplies (fun st => d.post st ∧ b.eval st = false) Q ∧
    d.verificationConditions Pbody

theorem full_verification_correct (d : FullDCom) (P : Assertion)
    (hvc : d.verificationConditions P) :
    ValidHoareTriple P d.erase d.post := by
  induction d generalizing P with
  | skip Q =>
    exact hoare_consequence_pre (hoare_skip Q) hvc
  | asgn x a Q =>
    exact hoare_consequence_pre (hoare_asgn Q x a) hvc
  | seq d1 d2 ih1 ih2 =>
    exact hoare_seq (ih1 P hvc.1) (ih2 d1.post hvc.2)
  | cond b P1 d1 P2 d2 Q ih1 ih2 =>
    rcases hvc with ⟨ht, hf, hq1, hq2, hvc1, hvc2⟩
    refine hoare_if ?_ ?_
    · exact hoare_consequence (ih1 P1 hvc1) ht hq1
    · exact hoare_consequence (ih2 P2 hvc2) hf hq2
  | whileDo b Pbody d Q ih =>
    rcases hvc with ⟨hinit, hbody_in, hexit, hvc_body⟩
    have hbody :
        ValidHoareTriple (fun st => d.post st ∧ b.eval st = true)
          d.erase d.post :=
      hoare_consequence_pre (ih Pbody hvc_body) hbody_in
    exact hoare_consequence (hoare_while hbody) hinit hexit

/-!
### Architecture 3: `HL/Hoare2.lean` Sparse Annotations + `awp` (`SparseDCom`)
-/

inductive SparseDCom where
  | skip
  | asgn (x : Nat) (a : AExp)
  | seq (d1 d2 : SparseDCom)
  | cond (b : BExp) (d1 d2 : SparseDCom)
  | whileDo (b : BExp) (inv : Assertion) (body : SparseDCom)

@[simp]
def SparseDCom.erase : SparseDCom → Com
  | .skip => .skip
  | .asgn x a => .asgn x a
  | .seq d1 d2 => .seq d1.erase d2.erase
  | .cond b d1 d2 => .cond b d1.erase d2.erase
  | .whileDo b _ body => .whileDo b body.erase

@[simp]
def SparseDCom.awp (Q : Assertion) : SparseDCom → Assertion
  | .skip => Q
  | .asgn x a => Q.subst x a
  | .seq d1 d2 => d1.awp (d2.awp Q)
  | .cond b d1 d2 =>
    fun st =>
      (b.eval st = true → d1.awp Q st) ∧
      (b.eval st = false → d2.awp Q st)
  | .whileDo _ inv _ => inv

@[simp]
def SparseDCom.verificationConditions (Q : Assertion) : SparseDCom → Prop
  | .skip => True
  | .asgn _ _ => True
  | .seq d1 d2 =>
    d1.verificationConditions (d2.awp Q) ∧ d2.verificationConditions Q
  | .cond _ d1 d2 =>
    d1.verificationConditions Q ∧ d2.verificationConditions Q
  | .whileDo b inv body =>
    (∀ st, inv st → b.eval st = false → Q st) ∧
    (∀ st, inv st → b.eval st = true → body.awp inv st) ∧
    body.verificationConditions inv

theorem sparse_awp_sound (d : SparseDCom) :
    ∀ (Q : Assertion),
      d.verificationConditions Q →
      ValidHoareTriple (d.awp Q) d.erase Q := by
  induction d with
  | skip =>
    intro Q _
    exact hoare_skip Q
  | asgn x a =>
    intro Q _
    exact hoare_asgn Q x a
  | seq d1 d2 ih1 ih2 =>
    intro Q hvc
    exact hoare_seq (ih1 (d2.awp Q) hvc.1) (ih2 Q hvc.2)
  | cond b d1 d2 ih1 ih2 =>
    intro Q hvc
    refine hoare_if ?_ ?_
    · refine hoare_consequence_pre (ih1 Q hvc.1) ?_
      intro st ⟨hpre, hb⟩
      exact hpre.1 hb
    · refine hoare_consequence_pre (ih2 Q hvc.2) ?_
      intro st ⟨hpre, hb⟩
      exact hpre.2 hb
  | whileDo b inv body ih =>
    intro Q hvc
    rcases hvc with ⟨hexit, hbody_in, hvc_body⟩
    have hbody :
        ValidHoareTriple (fun st => inv st ∧ b.eval st = true)
          body.erase inv := by
      refine hoare_consequence_pre (ih inv hvc_body) ?_
      intro st ⟨hinv, hb⟩
      exact hbody_in st hinv hb
    refine hoare_consequence (hoare_while hbody) (fun _ h => h) ?_
    intro st ⟨hinv, hb⟩
    exact hexit st hinv hb

theorem sparse_verification_correct (P : Assertion) (d : SparseDCom)
    (Q : Assertion) (hpre : AssertImplies P (d.awp Q))
    (hvc : d.verificationConditions Q) :
    ValidHoareTriple P d.erase Q :=
  hoare_consequence_pre (sparse_awp_sound d Q hvc) hpre

/-!
### Benchmark 1: 3-Statement + Branch Diamond Program (`diamondProg`)
-/

def diamondProg : Com :=
  .seq (.asgn 2 (.add (.var 1) (.num 4)))
    (.seq (.asgn 3 (.add (.var 2) (.num 6)))
      (.cond (.ble (.var 1) (.num 10))
        (.asgn 0 (.sub (.var 3) (.var 1)))
        (.asgn 0 (.num 10))))

def diamondPre : Assertion := fun _ => True
def diamondPost : Assertion := fun st => st 0 = 10

/-- Proof 1A: Relational Hoare-rule step-by-step chaining (`hoare_seq` +
    `hoare_if` + `hoare_consequence`). -/
theorem diamond_verified_hoare_rules :
    ValidHoareTriple diamondPre diamondProg diamondPost := by
  unfold diamondProg
  refine hoare_seq (Q := fun st => st 2 = st 1 + 4) ?_ ?_
  · refine hoare_consequence_pre
      (hoare_asgn (fun st => st 2 = st 1 + 4) 2 (.add (.var 1) (.num 4))) ?_
    intro st _
    simp [Assertion.subst]
  · refine hoare_seq (Q := fun st => st 3 = st 1 + 10) ?_ ?_
    · refine hoare_consequence_pre
        (hoare_asgn (fun st => st 3 = st 1 + 10) 3 (.add (.var 2) (.num 6))) ?_
      intro st h
      simp [Assertion.subst]
      omega
    · refine hoare_if ?_ ?_
      · refine hoare_consequence_pre
          (hoare_asgn diamondPost 0 (.sub (.var 3) (.var 1))) ?_
        intro st ⟨h, _⟩
        simp [diamondPost, Assertion.subst]
        omega
      · refine hoare_consequence_pre
          (hoare_asgn diamondPost 0 (.num 10)) ?_
        intro st _
        simp [diamondPost, Assertion.subst]

def diamondFullDCom : FullDCom :=
  .seq (.asgn 2 (.add (.var 1) (.num 4)) (fun st => st 2 = st 1 + 4))
    (.seq (.asgn 3 (.add (.var 2) (.num 6)) (fun st => st 3 = st 1 + 10))
      (.cond (.ble (.var 1) (.num 10))
        (fun st => st 3 = st 1 + 10)
        (.asgn 0 (.sub (.var 3) (.var 1)) diamondPost)
        (fun _ => True)
        (.asgn 0 (.num 10) diamondPost)
        diamondPost))

/-- Proof 1B: `HL/Hoare2.lean` Full `DCom` VC generation
    (`full_verification_correct`). -/
theorem diamond_verified_full_dcom :
    ValidHoareTriple diamondPre diamondFullDCom.erase diamondFullDCom.post := by
  apply full_verification_correct
  simp [FullDCom.verificationConditions, diamondFullDCom, diamondPre,
    diamondPost, AssertImplies, Assertion.subst]
  exact ⟨fun _ h _ => h, fun _ h => by omega⟩

def diamondSparseDCom : SparseDCom :=
  .seq (.asgn 2 (.add (.var 1) (.num 4)))
    (.seq (.asgn 3 (.add (.var 2) (.num 6)))
      (.cond (.ble (.var 1) (.num 10))
        (.asgn 0 (.sub (.var 3) (.var 1)))
        (.asgn 0 (.num 10))))

/-- Proof 1C: `HL/Hoare2.lean` Sparse `DCom` + `awp` VC generation
    (`sparse_verification_correct`), requiring zero intermediate assertions. -/
theorem diamond_verified_sparse_awp :
    ValidHoareTriple diamondPre diamondSparseDCom.erase diamondPost := by
  apply sparse_verification_correct
  · intro st _
    simp [diamondSparseDCom, diamondPost, SparseDCom.awp, Assertion.subst]
    intro _
    omega
  · simp [diamondSparseDCom, SparseDCom.verificationConditions]

/-!
### Benchmark 1b: 8-Statement Straight-Line + Branch Program (`chain8Prog`)
-/

def chain8Prog : Com :=
  .seq (.asgn 2 (.add (.var 1) (.num 1)))
    (.seq (.asgn 3 (.add (.var 2) (.num 2)))
      (.seq (.asgn 4 (.add (.var 3) (.num 3)))
        (.seq (.asgn 5 (.add (.var 4) (.num 4)))
          (.seq (.asgn 6 (.add (.var 5) (.num 5)))
            (.seq (.asgn 7 (.add (.var 6) (.num 6)))
              (.cond (.ble (.var 1) (.num 100))
                (.asgn 0 (.sub (.var 7) (.var 1)))
                (.asgn 0 (.num 21))))))))

def chain8Pre : Assertion := fun _ => True
def chain8Post : Assertion := fun st => st 0 = 21

/-- Proof 1b-A: Relational Hoare-rule step-by-step chaining on `chain8Prog`
    (requires 6 intermediate assertions + 7 `hoare_consequence_pre` steps). -/
theorem chain8_verified_hoare_rules :
    ValidHoareTriple chain8Pre chain8Prog chain8Post := by
  unfold chain8Prog
  refine hoare_seq (Q := fun st => st 2 = st 1 + 1) ?_ ?_
  · refine hoare_consequence_pre
      (hoare_asgn (fun st => st 2 = st 1 + 1) 2 (.add (.var 1) (.num 1))) ?_
    intro st _; simp [Assertion.subst]
  · refine hoare_seq (Q := fun st => st 3 = st 1 + 3) ?_ ?_
    · refine hoare_consequence_pre
        (hoare_asgn (fun st => st 3 = st 1 + 3) 3 (.add (.var 2) (.num 2))) ?_
      intro st h; simp [Assertion.subst]; omega
    · refine hoare_seq (Q := fun st => st 4 = st 1 + 6) ?_ ?_
      · refine hoare_consequence_pre
          (hoare_asgn (fun st => st 4 = st 1 + 6) 4 (.add (.var 3) (.num 3))) ?_
        intro st h; simp [Assertion.subst]; omega
      · refine hoare_seq (Q := fun st => st 5 = st 1 + 10) ?_ ?_
        · refine hoare_consequence_pre
            (hoare_asgn (fun st => st 5 = st 1 + 10) 5
              (.add (.var 4) (.num 4))) ?_
          intro st h; simp [Assertion.subst]; omega
        · refine hoare_seq (Q := fun st => st 6 = st 1 + 15) ?_ ?_
          · refine hoare_consequence_pre
              (hoare_asgn (fun st => st 6 = st 1 + 15) 6
                (.add (.var 5) (.num 5))) ?_
            intro st h; simp [Assertion.subst]; omega
          · refine hoare_seq (Q := fun st => st 7 = st 1 + 21) ?_ ?_
            · refine hoare_consequence_pre
                (hoare_asgn (fun st => st 7 = st 1 + 21) 7
                  (.add (.var 6) (.num 6))) ?_
              intro st h; simp [Assertion.subst]; omega
            · refine hoare_if ?_ ?_
              · refine hoare_consequence_pre
                  (hoare_asgn chain8Post 0 (.sub (.var 7) (.var 1))) ?_
                intro st ⟨h, _⟩; simp [chain8Post, Assertion.subst]; omega
              · refine hoare_consequence_pre
                  (hoare_asgn chain8Post 0 (.num 21)) ?_
                intro st _; simp [chain8Post, Assertion.subst]

def chain8FullDCom : FullDCom :=
  .seq (.asgn 2 (.add (.var 1) (.num 1)) (fun st => st 2 = st 1 + 1))
    (.seq (.asgn 3 (.add (.var 2) (.num 2)) (fun st => st 3 = st 1 + 3))
      (.seq (.asgn 4 (.add (.var 3) (.num 3)) (fun st => st 4 = st 1 + 6))
        (.seq (.asgn 5 (.add (.var 4) (.num 4)) (fun st => st 5 = st 1 + 10))
          (.seq (.asgn 6 (.add (.var 5) (.num 5)) (fun st => st 6 = st 1 + 15))
            (.seq (.asgn 7 (.add (.var 6) (.num 6)) (fun st => st 7 = st 1 + 21))
              (.cond (.ble (.var 1) (.num 100))
                (fun st => st 7 = st 1 + 21)
                (.asgn 0 (.sub (.var 7) (.var 1)) chain8Post)
                (fun _ => True)
                (.asgn 0 (.num 21) chain8Post)
                chain8Post))))))

/-- Proof 1b-B: `HL/Hoare2.lean` Full `DCom` VC generation on `chain8Prog`. -/
theorem chain8_verified_full_dcom :
    ValidHoareTriple chain8Pre chain8FullDCom.erase chain8FullDCom.post := by
  apply full_verification_correct
  simp [FullDCom.verificationConditions, chain8FullDCom, chain8Pre, chain8Post,
    AssertImplies, Assertion.subst]
  exact ⟨fun _ h _ => h, fun _ h => by omega⟩

def chain8SparseDCom : SparseDCom :=
  .seq (.asgn 2 (.add (.var 1) (.num 1)))
    (.seq (.asgn 3 (.add (.var 2) (.num 2)))
      (.seq (.asgn 4 (.add (.var 3) (.num 3)))
        (.seq (.asgn 5 (.add (.var 4) (.num 4)))
          (.seq (.asgn 6 (.add (.var 5) (.num 5)))
            (.seq (.asgn 7 (.add (.var 6) (.num 6)))
              (.cond (.ble (.var 1) (.num 100))
                (.asgn 0 (.sub (.var 7) (.var 1)))
                (.asgn 0 (.num 21))))))))

/-- Proof 1b-C: `HL/Hoare2.lean` Sparse `DCom` + `awp` on `chain8Prog` (zero
    intermediate assertions, single `omega` call). -/
theorem chain8_verified_sparse_awp :
    ValidHoareTriple chain8Pre chain8SparseDCom.erase chain8Post := by
  apply sparse_verification_correct
  · intro st _
    simp [chain8SparseDCom, chain8Post, SparseDCom.awp, Assertion.subst]
    intro _
    omega
  · simp [chain8SparseDCom, SparseDCom.verificationConditions]

/-!
### Benchmark 2: Countdown + Accumulator Loop (`loopProg`)
-/

def loopProg : Com :=
  .seq (.asgn 0 (.var 3))
    (.seq (.asgn 2 (.num 0))
      (.whileDo (.bnot (.ble (.var 0) (.num 0)))
        (.seq (.asgn 0 (.sub (.var 0) (.num 1)))
          (.asgn 2 (.add (.var 2) (.num 1))))))

def loopPre : Assertion := fun _ => True
def loopInv : Assertion := fun st => st 0 + st 2 = st 3
def loopPost : Assertion := fun st => st 0 = 0 ∧ st 2 = st 3

/-- Proof 2A: Relational Hoare-rule step-by-step chaining on `loopProg`. -/
theorem loop_verified_hoare_rules :
    ValidHoareTriple loopPre loopProg loopPost := by
  unfold loopProg
  refine hoare_seq (Q := fun st => st 0 = st 3) ?_ ?_
  · refine hoare_consequence_pre
      (hoare_asgn (fun st => st 0 = st 3) 0 (.var 3)) ?_
    intro st _
    simp [Assertion.subst]
  · refine hoare_seq (Q := loopInv) ?_ ?_
    · refine hoare_consequence_pre (hoare_asgn loopInv 2 (.num 0)) ?_
      intro st h
      simp [loopInv, Assertion.subst]
      omega
    · refine hoare_consequence (hoare_while (P := loopInv) ?_)
        (fun _ h => h) ?_
      · refine hoare_seq (Q := fun st => st 0 + (st 2 + 1) = st 3) ?_ ?_
        · refine hoare_consequence_pre
            (hoare_asgn (fun st => st 0 + (st 2 + 1) = st 3) 0
              (.sub (.var 0) (.num 1))) ?_
          intro st ⟨hinv, hb⟩
          simp [loopInv, BExp.eval, AExp.eval] at hinv hb
          simp [Assertion.subst]
          omega
        · refine hoare_consequence_pre
            (hoare_asgn loopInv 2 (.add (.var 2) (.num 1))) ?_
          intro st h
          simp [loopInv, Assertion.subst]
          omega
      · intro st ⟨hinv, hb⟩
        simp [loopInv, loopPost, BExp.eval, AExp.eval] at hinv hb ⊢
        omega

def loopSparseDCom : SparseDCom :=
  .seq (.asgn 0 (.var 3))
    (.seq (.asgn 2 (.num 0))
      (.whileDo (.bnot (.ble (.var 0) (.num 0))) loopInv
        (.seq (.asgn 0 (.sub (.var 0) (.num 1)))
          (.asgn 2 (.add (.var 2) (.num 1))))))

/-- Proof 2B: Sparse `DCom` + `awp` on `loopProg` discharging VCs with `omega`
    (which invokes `Classical.propDecidable` on the exit conjunction
    `st 0 = 0 ∧ st 2 = st 3`). -/
theorem loop_verified_sparse_awp :
    ValidHoareTriple loopPre loopSparseDCom.erase loopPost := by
  apply sparse_verification_correct
  · intro st _
    simp [loopSparseDCom, loopInv, SparseDCom.awp, Assertion.subst]
  · simp only [loopSparseDCom, SparseDCom.verificationConditions]
    refine ⟨trivial, trivial, ?_, ?_, trivial, trivial⟩
    · intro st hinv hb
      simp [loopInv, loopPost, BExp.eval, AExp.eval] at hinv hb ⊢
      omega
    · intro st hinv hb
      simp [loopInv, BExp.eval, AExp.eval] at hinv hb
      simp [SparseDCom.awp, loopInv, Assertion.subst]
      omega

/-- Proof 2C: Constructive Sparse `DCom` + `awp` on `loopProg` (eliminating
    `Nat.sub` via `cases st 0` instead of `omega`, achieving zero
    `Classical.choice` and zero `Quot.sound`). -/
theorem loop_verified_sparse_awp_constructive :
    ValidHoareTriple loopPre loopSparseDCom.erase loopPost := by
  apply sparse_verification_correct
  · intro st _
    simp [loopSparseDCom, loopInv, SparseDCom.awp, Assertion.subst]
  · simp only [loopSparseDCom, SparseDCom.verificationConditions]
    refine ⟨trivial, trivial, ?_, ?_, trivial, trivial⟩
    · intro st hinv hb
      simp [loopInv, loopPost, BExp.eval, AExp.eval] at hinv hb ⊢
      rw [hb, Nat.zero_add] at hinv
      exact ⟨hb, hinv⟩
    · intro st hinv hb
      simp [loopInv, BExp.eval, AExp.eval] at hinv hb
      simp [SparseDCom.awp, loopInv, Assertion.subst]
      cases h0 : st 0 with
      | zero =>
        rw [h0] at hb
        exact False.elim (Nat.lt_irrefl 0 hb)
      | succ k =>
        rw [h0] at hinv
        simp [Nat.add_assoc, Nat.add_comm 1 (st 2)] at hinv ⊢
        exact hinv

end HoareVCProbe

/-!
## Part 2: `fun_induction` / `fun_cases` vs. Structural `induction` / `cases`
-/

namespace FunInductionProbe

open HoareVCProbe

/-- Multi-constructor AST optimization pass with nested pattern matching and
    wildcard fallthrough arms (`| a1', a2' => ...`). -/
def optimizeAExp : AExp → AExp
  | .num n => .num n
  | .var x => .var x
  | .add a1 a2 =>
    match optimizeAExp a1, optimizeAExp a2 with
    | .num 0, a2' => a2'
    | a1', .num 0 => a1'
    | .num n1, .num n2 => .num (n1 + n2)
    | a1', a2' => .add a1' a2'
  | .sub a1 a2 =>
    match optimizeAExp a1, optimizeAExp a2 with
    | a1', .num 0 => a1'
    | .num n1, .num n2 => .num (n1 - n2)
    | a1', a2' => .sub a1' a2'
  | .mul a1 a2 =>
    match optimizeAExp a1, optimizeAExp a2 with
    | .num 1, a2' => a2'
    | a1', .num 1 => a1'
    | .num n1, .num n2 => .num (n1 * n2)
    | a1', a2' => .mul a1' a2'
  | .bitAnd a1 a2 => .bitAnd (optimizeAExp a1) (optimizeAExp a2)
  | .bitOr a1 a2 => .bitOr (optimizeAExp a1) (optimizeAExp a2)
  | .shl a1 a2 => .shl (optimizeAExp a1) (optimizeAExp a2)

/-- Approach 2A: Structural `induction a` on `optimizeAExp`. Because
    `optimizeAExp` has nested `match` arms with wildcard fallthroughs,
    structural `induction` must manually split on the recursive result terms
    and their numeric literals (`cases n1`, `cases n2`). -/
theorem optimizeAExp_sound_structural (st : State) (a : AExp) :
    (optimizeAExp a).eval st = a.eval st := by
  induction a with
  | num n => rfl
  | var x => rfl
  | add a1 a2 ih1 ih2 =>
    dsimp [optimizeAExp]
    rw [← ih1, ← ih2]
    cases optimizeAExp a1 with
    | num n1 =>
      cases n1 with
      | zero => simp [AExp.eval]
      | succ k1 =>
        cases optimizeAExp a2 with
        | num n2 =>
          cases n2 <;> simp [AExp.eval]
        | _ => simp [AExp.eval]
    | _ =>
      cases optimizeAExp a2 with
      | num n2 =>
        cases n2 <;> simp [AExp.eval]
      | _ => simp [AExp.eval]
  | sub a1 a2 ih1 ih2 =>
    dsimp [optimizeAExp]
    rw [← ih1, ← ih2]
    cases optimizeAExp a1 with
    | num n1 =>
      cases optimizeAExp a2 with
      | num n2 =>
        cases n2 <;> simp [AExp.eval]
      | _ => simp [AExp.eval]
    | _ =>
      cases optimizeAExp a2 with
      | num n2 =>
        cases n2 <;> simp [AExp.eval]
      | _ => simp [AExp.eval]
  | mul a1 a2 ih1 ih2 =>
    dsimp [optimizeAExp]
    rw [← ih1, ← ih2]
    cases optimizeAExp a1 with
    | num n1 =>
      cases n1 with
      | zero =>
        cases optimizeAExp a2 with
        | num n2 =>
          cases n2 with
          | zero => simp [AExp.eval]
          | succ k2 =>
            cases k2 <;> simp [AExp.eval]
        | _ => simp [AExp.eval]
      | succ k1 =>
        cases k1 with
        | zero => simp [AExp.eval]
        | succ m1 =>
          cases optimizeAExp a2 with
          | num n2 =>
            cases n2 with
            | zero => simp [AExp.eval]
            | succ k2 =>
              cases k2 <;> simp [AExp.eval]
          | _ => simp [AExp.eval]
    | _ =>
      cases optimizeAExp a2 with
      | num n2 =>
        cases n2 with
        | zero => simp [AExp.eval]
        | succ k2 =>
          cases k2 <;> simp [AExp.eval]
      | _ => simp [AExp.eval]
  | bitAnd a1 a2 ih1 ih2 =>
    simp [optimizeAExp, AExp.eval, ih1, ih2]
  | bitOr a1 a2 ih1 ih2 =>
    simp [optimizeAExp, AExp.eval, ih1, ih2]
  | shl a1 a2 ih1 ih2 =>
    simp [optimizeAExp, AExp.eval, ih1, ih2]

/-- Approach 2B: `symm; fun_induction <;> simp_all` (constructive, zero
    `Classical.choice`) on `optimizeAExp`. Orienting the goal via `symm`
    ensures `ih1 : a1.eval st = 0` rewrites `a1.eval st` in `simp_all`. -/
theorem optimizeAExp_sound_fun_ind_simp (st : State) (a : AExp) :
    (optimizeAExp a).eval st = a.eval st := by
  symm
  fun_induction optimizeAExp a <;> simp_all [AExp.eval]

/-- Approach 2C: `fun_induction <;> grind` on `optimizeAExp`. -/
theorem optimizeAExp_sound_fun_ind_grind (st : State) (a : AExp) :
    (optimizeAExp a).eval st = a.eval st := by
  fun_induction optimizeAExp a <;> grind [AExp.eval]

/-!
### Direct Comparison on Anneal's `optMirConstPropStmt` (`MirOptPasses.lean`)
-/

inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | adt (id : Nat) (inner : MirVal)

inductive Operand where
  | copy (src : Nat)
  | move (src : Nat)
  | constVal (val : MirVal)

inductive BinOp where
  | eq

inductive Rvalue where
  | use (op : Operand)
  | binaryOp (op : BinOp) (lhs rhs : Operand)
  | aggregate (adtId : Nat) (op : Operand)
  | field0 (src : Nat)
  | ref (src : Nat)
  | reborrow (src : Nat)
  | copyDeref (src : Nat)

inductive Stmt where
  | assign (dst : Nat) (rv : Rvalue)
  | storageLive (loc : Nat)
  | storageDead (loc : Nat)
  | nop

def evalOperand (locals : Nat → Option MirVal) : Operand → Option MirVal
  | .copy src => locals src
  | .move src => locals src
  | .constVal v => some v

def evalBinOp : BinOp → MirVal → MirVal → Option MirVal
  | .eq, .usize a, .usize b => some (.bool (decide (a = b)))
  | .eq, .bool a, .bool b => some (.bool (decide (a = b)))
  | .eq, .unit, .unit => some (.bool true)
  | .eq, _, _ => none

def evalMirStmt (locals : Nat → Option MirVal) (stmt : Stmt) :
    Option (Nat × Option MirVal) :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand locals op with
    | some v => some (dst, some v)
    | none => none
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalOperand locals lhs, evalOperand locals rhs with
    | some v1, some v2 =>
      match evalBinOp op v1 v2 with
      | some res => some (dst, some res)
      | none => none
    | _, _ => none
  | .assign dst (.aggregate id op) =>
    match evalOperand locals op with
    | some v => some (dst, some (.adt id v))
    | none => none
  | .assign _ _ => none
  | .storageLive loc => some (loc, none)
  | .storageDead loc => some (loc, none)
  | .nop => some (0, none)

def optMirConstPropStmt (stmt : Stmt) : Stmt :=
  match stmt with
  | .assign dst (.binaryOp .eq (.constVal (.usize a)) (.constVal (.usize b))) =>
    .assign dst (.use (.constVal (.bool (decide (a = b)))))
  | .assign dst (.binaryOp .eq (.constVal (.bool a)) (.constVal (.bool b))) =>
    .assign dst (.use (.constVal (.bool (decide (a = b)))))
  | .assign dst (.binaryOp .eq (.constVal .unit) (.constVal .unit)) =>
    .assign dst (.use (.constVal (.bool true)))
  | other => other

/-- Anneal's structural `cases` proof (`MirOptPasses.lean` L62–85). -/
theorem evalMirStmt_optMirConstPropStmt_structural
    (locals : Nat → Option MirVal) (stmt : Stmt) :
    evalMirStmt locals (optMirConstPropStmt stmt) =
      evalMirStmt locals stmt := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | binaryOp op lhs rhs =>
      cases op with
      | eq =>
        cases lhs with
        | copy _ => rfl
        | move _ => rfl
        | constVal v1 =>
          cases rhs with
          | copy _ =>
            cases v1 <;> rfl
          | move _ =>
            cases v1 <;> rfl
          | constVal v2 =>
            cases v1 <;> cases v2 <;> rfl
    | _ => rfl
  | storageLive _ => rfl
  | storageDead _ => rfl
  | nop => rfl

/-- Single-line `fun_cases` proof of the same theorem. -/
theorem evalMirStmt_optMirConstPropStmt_fun_cases
    (locals : Nat → Option MirVal) (stmt : Stmt) :
    evalMirStmt locals (optMirConstPropStmt stmt) =
      evalMirStmt locals stmt := by
  fun_cases optMirConstPropStmt stmt <;> rfl

end FunInductionProbe

/-!
## Part 3: `TS/References.lean` (`STLCRef`) Store Typing & Monotonicity
-/

namespace ReferencesProbe

inductive Ty where
  | unit
  | nat
  | fn (dom cod : Ty)
  | ref (inner : Ty)

inductive Tm where
  | unit
  | nat (n : Nat)
  | loc (l : Nat)
  | ref (t : Tm)
  | deref (t : Tm)
  | assign (lhs rhs : Tm)
  | seq (t1 t2 : Tm)

inductive IsValue : Tm → Prop where
  | unit : IsValue .unit
  | nat (n : Nat) : IsValue (.nat n)
  | loc (l : Nat) : IsValue (.loc l)

abbrev Store := List Tm
abbrev StoreTy := List Ty

inductive Step : Tm × Store → Tm × Store → Prop where
  | refVal {v : Tm} {ρ : Store} :
      IsValue v →
      Step (.ref v, ρ) (.loc ρ.length, ρ ++ [v])
  | refStep {t t' : Tm} {ρ ρ' : Store} :
      Step (t, ρ) (t', ρ') →
      Step (.ref t, ρ) (.ref t', ρ')
  | derefLoc {l : Nat} {v : Tm} {ρ : Store} :
      ρ[l]? = some v →
      Step (.deref (.loc l), ρ) (v, ρ)
  | derefStep {t t' : Tm} {ρ ρ' : Store} :
      Step (t, ρ) (t', ρ') →
      Step (.deref t, ρ) (.deref t', ρ')
  | assignVal {l : Nat} {v : Tm} {ρ : Store} :
      IsValue v →
      l < ρ.length →
      Step (.assign (.loc l) v, ρ) (.unit, ρ.set l v)
  | assignLhs {t1 t1' t2 : Tm} {ρ ρ' : Store} :
      Step (t1, ρ) (t1', ρ') →
      Step (.assign t1 t2, ρ) (.assign t1' t2, ρ')
  | assignRhs {v1 t2 t2' : Tm} {ρ ρ' : Store} :
      IsValue v1 →
      Step (t2, ρ) (t2', ρ') →
      Step (.assign v1 t2, ρ) (.assign v1 t2', ρ')
  | seqVal {v1 t2 : Tm} {ρ : Store} :
      IsValue v1 →
      Step (.seq v1 t2, ρ) (t2, ρ)
  | seqStep {t1 t1' t2 : Tm} {ρ ρ' : Store} :
      Step (t1, ρ) (t1', ρ') →
      Step (.seq t1 t2, ρ) (.seq t1' t2, ρ')

inductive HasType (δ : StoreTy) : Tm → Ty → Prop where
  | unit :
      HasType δ .unit .unit
  | nat (n : Nat) :
      HasType δ (.nat n) .nat
  | loc {l : Nat} {τ : Ty} :
      δ[l]? = some τ →
      HasType δ (.loc l) (.ref τ)
  | ref {t : Tm} {τ : Ty} :
      HasType δ t τ →
      HasType δ (.ref t) (.ref τ)
  | deref {t : Tm} {τ : Ty} :
      HasType δ t (.ref τ) →
      HasType δ (.deref t) τ
  | assign {lhs rhs : Tm} {τ : Ty} :
      HasType δ lhs (.ref τ) →
      HasType δ rhs τ →
      HasType δ (.assign lhs rhs) .unit
  | seq {t1 t2 : Tm} {τ : Ty} :
      HasType δ t1 .unit →
      HasType δ t2 τ →
      HasType δ (.seq t1 t2) τ

/-- Monotonic store-typing extension (`Extends δ' δ` means `δ` is a prefix of
    `δ'`). -/
inductive Extends : StoreTy → StoreTy → Prop where
  | nil (δ' : StoreTy) :
      Extends δ' []
  | cons (x : Ty) {δ' δ : StoreTy} :
      Extends δ' δ →
      Extends (x :: δ') (x :: δ)

theorem extends_refl : ∀ (δ : StoreTy), Extends δ δ
  | [] => .nil []
  | x :: δ => .cons x (extends_refl δ)

theorem extends_trans {δ₁ δ₂ δ₃ : StoreTy}
    (h12 : Extends δ₁ δ₂) (h23 : Extends δ₂ δ₃) :
    Extends δ₁ δ₃ := by
  induction h23 generalizing δ₁ with
  | nil => exact .nil δ₁
  | cons x _ ih =>
    cases h12 with
    | cons _ h12' => exact .cons x (ih h12')

theorem extends_lookup {l : Nat} {δ' δ : StoreTy} {τ : Ty}
    (hget : δ[l]? = some τ) (hext : Extends δ' δ) :
    δ'[l]? = some τ := by
  induction hext generalizing l with
  | nil => cases hget
  | cons x _ ih =>
    cases l with
    | zero => exact hget
    | succ k => exact ih hget

theorem extends_append_singleton (δ : StoreTy) (τ : Ty) :
    Extends (δ ++ [τ]) δ := by
  induction δ with
  | nil => exact .nil [τ]
  | cons x rest ih => exact .cons x ih

theorem store_weakening {δ' δ : StoreTy} {t : Tm} {τ : Ty}
    (hext : Extends δ' δ) (ht : HasType δ t τ) :
    HasType δ' t τ := by
  induction ht with
  | unit => exact .unit
  | nat n => exact .nat n
  | loc hget => exact .loc (extends_lookup hget hext)
  | ref _ ih => exact .ref ih
  | deref _ ih => exact .deref ih
  | assign _ _ ih1 ih2 => exact .assign ih1 ih2
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2

def StoreWellTyped (δ : StoreTy) (ρ : Store) : Prop :=
  δ.length = ρ.length ∧
  ∀ (l : Nat) (v : Tm) (τ : Ty),
    ρ[l]? = some v → δ[l]? = some τ → HasType δ v τ

theorem getElem?_append_singleton_lt {α : Type} :
    ∀ (xs : List α) (x : α) (l : Nat) (v : α),
      (xs ++ [x])[l]? = some v →
      (l < xs.length ∧ xs[l]? = some v) ∨ (l = xs.length ∧ v = x)
  | [], _, 0, _, h => by
    injection h with hv
    exact Or.inr ⟨rfl, hv.symm⟩
  | [], _, _ + 1, _, h => by
    cases h
  | _ :: rest, _, 0, _, h => by
    injection h with hv
    exact Or.inl ⟨Nat.zero_lt_succ rest.length, congrArg some hv⟩
  | _ :: rest, x, l + 1, v, h => by
    cases getElem?_append_singleton_lt rest x l v h with
    | inl hlt =>
      exact Or.inl ⟨Nat.succ_lt_succ hlt.1, hlt.2⟩
    | inr heq =>
      exact Or.inr ⟨congrArg Nat.succ heq.1, heq.2⟩

theorem getElem?_append_singleton_self {α : Type} :
    ∀ (xs : List α) (x : α),
      (xs ++ [x])[xs.length]? = some x
  | [], _ => rfl
  | _ :: rest, x => getElem?_append_singleton_self rest x

theorem store_well_typed_alloc {δ : StoreTy} {ρ : Store} {v : Tm} {τ : Ty}
    (hwt : StoreWellTyped δ ρ) (hv : HasType δ v τ) :
    StoreWellTyped (δ ++ [τ]) (ρ ++ [v]) := by
  refine ⟨by simp [hwt.1], ?_⟩
  intro l v' τ' hget_v hget_t
  have hv_case := getElem?_append_singleton_lt ρ v l v' hget_v
  have ht_case := getElem?_append_singleton_lt δ τ l τ' hget_t
  have hext : Extends (δ ++ [τ]) δ := extends_append_singleton δ τ
  cases hv_case with
  | inl hvl =>
    cases ht_case with
    | inl htl =>
      exact store_weakening hext (hwt.2 l v' τ' hvl.2 htl.2)
    | inr htr =>
      have hlen : l < ρ.length := hvl.1
      rw [← hwt.1, htr.1] at hlen
      exact False.elim (Nat.lt_irrefl _ hlen)
  | inr hvr =>
    cases ht_case with
    | inl htl =>
      have hlen : l < δ.length := htl.1
      rw [hwt.1, hvr.1] at hlen
      exact False.elim (Nat.lt_irrefl _ hlen)
    | inr htr =>
      rw [hvr.2, htr.2]
      exact store_weakening hext hv

theorem getElem?_set_cases {α : Type} :
    ∀ (xs : List α) (idx l : Nat) (x v : α),
      (xs.set idx x)[l]? = some v →
      (l = idx ∧ v = x) ∨ (l ≠ idx ∧ xs[l]? = some v)
  | [], _, _, _, _, h => by cases h
  | _ :: _, 0, 0, _, _, h => by
    injection h with hv
    exact Or.inl ⟨rfl, hv.symm⟩
  | _ :: _, 0, _ + 1, _, _, h =>
    Or.inr ⟨(fun h0 => nomatch h0), h⟩
  | _ :: _, _ + 1, 0, _, _, h =>
    Or.inr ⟨(fun h0 => nomatch h0), h⟩
  | _ :: rest, idx + 1, l + 1, x, v, h => by
    cases getElem?_set_cases rest idx l x v h with
    | inl heq =>
      exact Or.inl ⟨congrArg Nat.succ heq.1, heq.2⟩
    | inr hne =>
      exact Or.inr ⟨fun hs => hne.1 (Nat.succ.inj hs), hne.2⟩

theorem assign_pres_store_typing {δ : StoreTy} {ρ : Store} {l : Nat}
    {v : Tm} {τ : Ty} (hwt : StoreWellTyped δ ρ) (ht_loc : δ[l]? = some τ)
    (hv : HasType δ v τ) :
    StoreWellTyped δ (ρ.set l v) := by
  refine ⟨by simp [hwt.1], ?_⟩
  intro l' v' τ' hget_v hget_t
  cases getElem?_set_cases ρ l l' v v' hget_v with
  | inl heq =>
    rcases heq with ⟨hl, hv_eq⟩
    subst hl
    subst hv_eq
    have ht_eq : some τ = some τ' := ht_loc.symm.trans hget_t
    injection ht_eq with hτ
    subst hτ
    exact hv
  | inr hne =>
    exact hwt.2 l' v' τ' hne.2 hget_t

/-- Full `STLCRef` Type Preservation Theorem with Monotonic Store Extension
    (`Extends δ' δ`). -/
theorem preservation {δ : StoreTy} {ρ ρ' : Store} {t t' : Tm} {τ : Ty}
    (hwt : StoreWellTyped δ ρ)
    (ht : HasType δ t τ)
    (hstep : Step (t, ρ) (t', ρ')) :
    ∃ δ', Extends δ' δ ∧ HasType δ' t' τ ∧ StoreWellTyped δ' ρ' := by
  generalize hp : (t, ρ) = p at hstep
  generalize hp' : (t', ρ') = p' at hstep
  induction hstep generalizing δ t t' ρ ρ' τ with
  | refVal _ =>
    injection hp with ht_eq hρ_eq
    injection hp' with ht'_eq hρ'_eq
    subst ht_eq; subst hρ_eq; subst ht'_eq; subst hρ'_eq
    cases ht with
    | ref hsub =>
      refine ⟨δ ++ [_], extends_append_singleton δ _, ?_,
        store_well_typed_alloc hwt hsub⟩
      refine .loc ?_
      rw [← hwt.1]
      exact getElem?_append_singleton_self δ _
  | refStep _ ih =>
    injection hp with ht_eq hρ_eq
    injection hp' with ht'_eq hρ'_eq
    subst ht_eq; subst hρ_eq; subst ht'_eq; subst hρ'_eq
    cases ht with
    | ref hsub =>
      rcases ih hwt hsub rfl rfl with ⟨δ', hext, ht', hwt'⟩
      exact ⟨δ', hext, .ref ht', hwt'⟩
  | derefLoc hget_v =>
    injection hp with ht_eq hρ_eq
    injection hp' with ht'_eq hρ'_eq
    subst ht_eq; subst hρ_eq; subst ht'_eq; subst hρ'_eq
    cases ht with
    | deref hloc =>
      cases hloc with
      | loc hget_t =>
        exact ⟨δ, extends_refl δ, hwt.2 _ _ _ hget_v hget_t, hwt⟩
  | derefStep _ ih =>
    injection hp with ht_eq hρ_eq
    injection hp' with ht'_eq hρ'_eq
    subst ht_eq; subst hρ_eq; subst ht'_eq; subst hρ'_eq
    cases ht with
    | deref hsub =>
      rcases ih hwt hsub rfl rfl with ⟨δ', hext, ht', hwt'⟩
      exact ⟨δ', hext, .deref ht', hwt'⟩
  | assignVal _ _ =>
    injection hp with ht_eq hρ_eq
    injection hp' with ht'_eq hρ'_eq
    subst ht_eq; subst hρ_eq; subst ht'_eq; subst hρ'_eq
    cases ht with
    | assign hlhs hrhs =>
      cases hlhs with
      | loc hget_t =>
        exact ⟨δ, extends_refl δ, .unit,
          assign_pres_store_typing hwt hget_t hrhs⟩
  | assignLhs _ ih =>
    injection hp with ht_eq hρ_eq
    injection hp' with ht'_eq hρ'_eq
    subst ht_eq; subst hρ_eq; subst ht'_eq; subst hρ'_eq
    cases ht with
    | assign hlhs hrhs =>
      rcases ih hwt hlhs rfl rfl with ⟨δ', hext, hlhs', hwt'⟩
      exact ⟨δ', hext, .assign hlhs' (store_weakening hext hrhs), hwt'⟩
  | assignRhs _ _ ih =>
    injection hp with ht_eq hρ_eq
    injection hp' with ht'_eq hρ'_eq
    subst ht_eq; subst hρ_eq; subst ht'_eq; subst hρ'_eq
    cases ht with
    | assign hlhs hrhs =>
      rcases ih hwt hrhs rfl rfl with ⟨δ', hext, hrhs', hwt'⟩
      exact ⟨δ', hext, .assign (store_weakening hext hlhs) hrhs', hwt'⟩
  | seqVal _ =>
    injection hp with ht_eq hρ_eq
    injection hp' with ht'_eq hρ'_eq
    subst ht_eq; subst hρ_eq; subst ht'_eq; subst hρ'_eq
    cases ht with
    | seq _ ht2 =>
      exact ⟨δ, extends_refl δ, ht2, hwt⟩
  | seqStep _ ih =>
    injection hp with ht_eq hρ_eq
    injection hp' with ht'_eq hρ'_eq
    subst ht_eq; subst hρ_eq; subst ht'_eq; subst hρ'_eq
    cases ht with
    | seq ht1 ht2 =>
      rcases ih hwt ht1 rfl rfl with ⟨δ', hext, ht1', hwt'⟩
      exact ⟨δ', hext, .seq ht1' (store_weakening hext ht2), hwt'⟩

/-- Cyclic 2-cell heap store `cyclicStore`:
    - Cell `0` contains `!(loc 1); unit` (dereferencing cell `1`),
    - Cell `1` contains `!(loc 0); unit` (dereferencing cell `0`).
    Under `cyclicStoreTy = [.unit, .unit]`, `StoreWellTyped` holds by a finite
    derivation because `loc l` looks up `cyclicStoreTy[l]?` rather than
    re-typechecking `cyclicStore[l]`. -/
def cyclicStore : Store :=
  [.seq (.deref (.loc 1)) .unit, .seq (.deref (.loc 0)) .unit]

def cyclicStoreTy : StoreTy :=
  [.unit, .unit]

theorem cyclic_store_well_typed :
    StoreWellTyped cyclicStoreTy cyclicStore := by
  refine ⟨rfl, ?_⟩
  intro l v τ hget_v hget_t
  cases l with
  | zero =>
    injection hget_v with hv
    injection hget_t with hτ
    subst hv; subst hτ
    exact .seq (.deref (.loc rfl)) .unit
  | succ k =>
    cases k with
    | zero =>
      injection hget_v with hv
      injection hget_t with hτ
      subst hv; subst hτ
      exact .seq (.deref (.loc rfl)) .unit
    | succ m =>
      cases hget_v

end ReferencesProbe

/-!
## Part 4: Exact Transitive Axiom Closures of `omega`, `lia`, and `grind`
-/

namespace AxiomClosureProbe

theorem omega_nat_add (a b : Nat) (ha : a < 100) (hb : b < 100) :
    a + b < 200 := by
  omega

theorem omega_nat_sub (a b k : Nat) (h : a + b = k ∧ 0 < a) :
    (a - 1) + (b + 1) = k := by
  omega

theorem omega_nat_sub_fn (st : Nat → Nat) (hinv : st 0 + st 2 = st 3)
    (hb : 0 < st 0) :
    (st 0 - 1) + (st 2 + 1) = st 3 := by
  omega

theorem omega_nat_conj (st : Nat → Nat) (hinv : st 0 + st 2 = st 3)
    (hb : st 0 = 0) :
    st 0 = 0 ∧ st 2 = st 3 := by
  omega

theorem lia_nat_add (a b : Nat) (ha : a < 100) (hb : b < 100) :
    a + b < 200 := by
  lia

theorem lia_nat_sub (a b k : Nat) (h : a + b = k ∧ 0 < a) :
    (a - 1) + (b + 1) = k := by
  lia

theorem grind_nat_add (a b : Nat) (ha : a < 101) (hb : b < 101) :
    a + b < 202 := by
  grind

theorem grind_nat_sub (a b k : Nat) (h : a + b = k ∧ 1 < a) :
    (a - 2) + (b + 2) = k := by
  grind

end AxiomClosureProbe

end ProbeHoareWpFunIndAndReferences

/-!
## Part 5: Self-Contained Measurement and Kernel Replay Harness
-/

namespace ProbeHarness

open Lean Elab Command

def constDirectObjs (ci : ConstantInfo) : IO Nat := do
  let tyObjs ← (ShareCommon.shareCommon ci.type).numObjs
  let valObjs ← match ci.value? (allowOpaque := true) with
    | some v => (ShareCommon.shareCommon v).numObjs
    | none => pure 0
  return tyObjs + valObjs

def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def isLocalProbeConst (env : Environment) (n : Name) : Bool :=
  (env.getModuleIdxFor? n).isNone

partial def collectModuleClosure (env : Environment) (root : Name) :
    NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut modConsts : NameSet := {}
  let mut worklist : Array Name := #[root]
  while !worklist.isEmpty do
    let curr := worklist.back!
    worklist := worklist.pop
    if visited.contains curr then
      continue
    visited := visited.insert curr
    let some ci := env.find? curr | continue
    if isLocalProbeConst env curr then
      modConsts := modConsts.insert curr
      for u in ci.getUsedConstantsAsSet do
        if !visited.contains u then
          worklist := worklist.push u
  return modConsts

partial def collectAllAxioms (kEnv : Kernel.Environment) (root : Name) :
    Array Name × Nat := Id.run do
  let mut visited : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut worklist : Array Name := #[root]
  while !worklist.isEmpty do
    let curr := worklist.back!
    worklist := worklist.pop
    if visited.contains curr then
      continue
    visited := visited.insert curr
    let some ci := kEnv.find? curr | continue
    if ci matches .axiomInfo _ then
      unless axioms.contains curr do
        axioms := axioms.push curr
    for u in ci.getUsedConstantsAsSet do
      if !visited.contains u then
        worklist := worklist.push u
  return (axioms, visited.size)

partial def findShortestAxiomPath (kEnv : Kernel.Environment)
    (root targetAx : Name) : List Name := Id.run do
  let mut visited : NameSet := {}
  let mut parentMap : Std.HashMap Name Name := {}
  let mut queue : Array Name := #[root]
  visited := visited.insert root
  let mut qIdx := 0
  let mut found := false
  while qIdx < queue.size do
    let curr := queue[qIdx]!
    qIdx := qIdx + 1
    if curr == targetAx then
      found := true
      break
    if let some ci := kEnv.find? curr then
      for u in ci.getUsedConstantsAsSet do
        if !visited.contains u then
          visited := visited.insert u
          parentMap := parentMap.insert u curr
          queue := queue.push u
  if !found then
    return []
  let mut path : List Name := [targetAx]
  let mut walk := targetAx
  while walk != root do
    match parentMap.get? walk with
    | some p =>
      path := p :: path
      walk := p
    | none => break
  return path

def classifyAux (modConsts : NameSet) : (Nat × Nat × Nat × Nat) := Id.run do
  let mut eqCnt := 0
  let mut indCnt := 0
  let mut matchCnt := 0
  let mut proofCnt := 0
  for n in modConsts do
    let s := n.toString
    if hasSubstr s ".eq_" then eqCnt := eqCnt + 1
    if hasSubstr s ".induct" || hasSubstr s ".fun_cases" then
      indCnt := indCnt + 1
    if hasSubstr s ".match_" then matchCnt := matchCnt + 1
    if hasSubstr s "._proof_" then proofCnt := proofCnt + 1
  return (eqCnt, indCnt, matchCnt, proofCnt)

def measureTheoremLine (baseEnv fullEnv : Environment)
    (kEnv : Kernel.Environment) (iters : Nat) (thmName : Name) : IO String := do
  let some ci := fullEnv.find? thmName
    | throw <| IO.userError s!"Constant not found: {thmName}"
  let directObjs ← constDirectObjs ci
  let modConsts := collectModuleClosure fullEnv thmName
  let thmPrefix := thmName.toString ++ "."
  let mut marginalObjs := 0
  let mut transitiveObjs := 0
  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  let mut preMap : Std.HashMap Name ConstantInfo := {}
  let mut marginalMap : Std.HashMap Name ConstantInfo := {}
  for n in modConsts do
    if let some c := fullEnv.find? n then
      let objs ← constDirectObjs c
      transitiveObjs := transitiveObjs + objs
      replayMap := replayMap.insert n c
      if n == thmName || n.toString.startsWith thmPrefix then
        marginalObjs := marginalObjs + objs
        marginalMap := marginalMap.insert n c
      else
        preMap := preMap.insert n c
  let (eqCnt, indCnt, matchCnt, proofCnt) := classifyAux modConsts
  let (axioms, _) := collectAllAxioms kEnv thmName
  let kBase := baseEnv.toKernelEnv
  let kPre ← Lean.Kernel.Environment.replay preMap kBase
  let tm0 ← IO.monoNanosNow
  for _ in [0:iters] do
    let _ ← Lean.Kernel.Environment.replay marginalMap kPre
  let tm1 ← IO.monoNanosNow
  let marginalUs := ((tm1 - tm0) / 1000) / iters
  let t0 ← IO.monoNanosNow
  for _ in [0:iters] do
    let _ ← Lean.Kernel.Environment.replay replayMap kBase
  let t1 ← IO.monoNanosNow
  let fullUs := ((t1 - t0) / 1000) / iters
  return s!"{thmName} | {directObjs} | {marginalObjs} | {transitiveObjs} | {modConsts.size} | {eqCnt} | {indCnt} | {matchCnt} | {proofCnt} | {marginalUs} | {fullUs} | {axioms}"

elab "#synthesize_probe_report" : command => do
  let fullEnv := (← getEnv).setExporting false
  let kEnv := fullEnv.checked.get
  let out ← liftIO <| unsafe do
    let sysroot := (← IO.appDir).parent.getD (← findSysroot)
    initSearchPath sysroot
    enableInitializersExecution
    let baseEnv ← importModules #[{ module := `Init }] {}
      (trustLevel := 0) (loadExts := false)
    let mut lines : Array String := #[]
    lines := lines.push "=== 1. Equation-Compiler Unsafe/Splitter Constant Inventory ==="
    let localDecls : Array (Name × ConstantInfo) :=
      fullEnv.constants.foldStage2 (fun acc n ci => acc.push (n, ci)) #[]
    let mut unsafeRecs : Array Name := #[]
    let mut splitterSummary : Array String := #[]
    for (n, ci) in localDecls do
      let s := n.toString
      if hasSubstr s "ProbeHoareWpFunIndAndReferences" then
        if ci.isUnsafe || ci.isPartial then
          unsafeRecs := unsafeRecs.push n
        if hasSubstr s "optimizeAExp" || hasSubstr s "optMirConstPropStmt" then
          let objs ← constDirectObjs ci
          splitterSummary := splitterSummary.push
            s!"  {n} (directObjs={objs}, isUnsafe={ci.isUnsafe})"
    lines := lines.push
      s!"  Unsafe/partial constants in probe: {unsafeRecs}"
    for item in splitterSummary do
      lines := lines.push item

    lines := lines.push "\n=== 2. Theorem DAG Size, Auxiliary Constants, and Kernel Replay (10 Iterations) ==="
    lines := lines.push "Theorem | DirectObjs | MarginalObjs | TransModObjs | ModConsts | .eq_N | .induct/.fun_cases | .match_N | ._proof_N | MarginalReplayUs | FullReplayUs | Axioms"
    let targets : List Name := [
      `ProbeHoareWpFunIndAndReferences.HoareVCProbe.diamond_verified_hoare_rules,
      `ProbeHoareWpFunIndAndReferences.HoareVCProbe.diamond_verified_full_dcom,
      `ProbeHoareWpFunIndAndReferences.HoareVCProbe.diamond_verified_sparse_awp,
      `ProbeHoareWpFunIndAndReferences.HoareVCProbe.chain8_verified_hoare_rules,
      `ProbeHoareWpFunIndAndReferences.HoareVCProbe.chain8_verified_full_dcom,
      `ProbeHoareWpFunIndAndReferences.HoareVCProbe.chain8_verified_sparse_awp,
      `ProbeHoareWpFunIndAndReferences.HoareVCProbe.loop_verified_hoare_rules,
      `ProbeHoareWpFunIndAndReferences.HoareVCProbe.loop_verified_sparse_awp,
      `ProbeHoareWpFunIndAndReferences.HoareVCProbe.loop_verified_sparse_awp_constructive,
      `ProbeHoareWpFunIndAndReferences.FunInductionProbe.optimizeAExp_sound_structural,
      `ProbeHoareWpFunIndAndReferences.FunInductionProbe.optimizeAExp_sound_fun_ind_simp,
      `ProbeHoareWpFunIndAndReferences.FunInductionProbe.optimizeAExp_sound_fun_ind_grind,
      `ProbeHoareWpFunIndAndReferences.FunInductionProbe.evalMirStmt_optMirConstPropStmt_structural,
      `ProbeHoareWpFunIndAndReferences.FunInductionProbe.evalMirStmt_optMirConstPropStmt_fun_cases,
      `ProbeHoareWpFunIndAndReferences.ReferencesProbe.store_weakening,
      `ProbeHoareWpFunIndAndReferences.ReferencesProbe.store_well_typed_alloc,
      `ProbeHoareWpFunIndAndReferences.ReferencesProbe.assign_pres_store_typing,
      `ProbeHoareWpFunIndAndReferences.ReferencesProbe.preservation,
      `ProbeHoareWpFunIndAndReferences.ReferencesProbe.cyclic_store_well_typed
    ]
    for t in targets do
      let line ← measureTheoremLine baseEnv fullEnv kEnv 10 t
      lines := lines.push line

    lines := lines.push "\n=== 3. Exact Transitive Axiom Closures of `omega`, `lia`, and `grind` ==="
    let axTargets : List Name := [
      `ProbeHoareWpFunIndAndReferences.AxiomClosureProbe.omega_nat_add,
      `ProbeHoareWpFunIndAndReferences.AxiomClosureProbe.omega_nat_sub,
      `ProbeHoareWpFunIndAndReferences.AxiomClosureProbe.omega_nat_sub_fn,
      `ProbeHoareWpFunIndAndReferences.AxiomClosureProbe.omega_nat_conj,
      `ProbeHoareWpFunIndAndReferences.AxiomClosureProbe.lia_nat_add,
      `ProbeHoareWpFunIndAndReferences.AxiomClosureProbe.lia_nat_sub,
      `ProbeHoareWpFunIndAndReferences.AxiomClosureProbe.grind_nat_add,
      `ProbeHoareWpFunIndAndReferences.AxiomClosureProbe.grind_nat_sub
    ]
    for thm in axTargets do
      let (axs, visitedCnt) := collectAllAxioms kEnv thm
      lines := lines.push
        s!"  {thm}: axioms={axs}, reachableDecls={visitedCnt}"
      for ax in [``Classical.choice, ``Quot.sound] do
        if axs.contains ax then
          let p := findShortestAxiomPath kEnv thm ax
          lines := lines.push
            s!"    shortest path to {ax} ({p.length} hops): {p}"

    return String.intercalate "\n" lines.toList
  let id := mkIdent `generatedProbeReport
  elabCommand (← `(def $id : String := $(Syntax.mkStrLit out)))

#synthesize_probe_report

end ProbeHarness

def main : IO Unit := do
  IO.println ProbeHarness.generatedProbeReport
