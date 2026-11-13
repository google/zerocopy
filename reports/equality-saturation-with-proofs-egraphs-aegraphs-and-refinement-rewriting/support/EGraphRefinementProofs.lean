-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Equality Saturation with Proofs: Poison Unsoundness of Symmetric E-Classes and Sound Directed Refinement Certificates

This standalone Lean 4.34.1 mechanization proves:
1. Why treating directional poison refinement (`src ⊑ tgt`, where `.poison ⊑ .value v`)
   as symmetric equivalence inside an e-graph (`e-class` union) is **unsound**
   (`symmetric_eclass_poison_unsound` and `mul_zero_not_symmetric_eq`):
   unioning `x * 0` with `0` in a symmetric e-class allows rewriting a defined
   value (`0`) into `.poison` (`poison * 0`).
2. Why decomposing optimization rules into:
   - **Symmetric Poison-Exact Equalities** (`⟦lhs⟧ = ⟦rhs⟧` on `PoisonOr (BitVec 64)`,
     which hold inside symmetric e-classes), and
   - **Directed Poison-Monotonic Refinements** (`⟦lhs⟧ ⊑ ⟦rhs⟧`, checked along a
     directed post-extraction certificate spine `List DirectedRewriteStep`)
   is 100% sound (`checkDirectedRefinementTrace_sound`) with zero extra axioms.
-/

namespace EGraphRefinementProofs

/-- SSA value with deferred undefined behavior (`poison`). -/
inductive PoisonOr (α : Type) where
  | poison : PoisonOr α
  | value  : α → PoisonOr α
  deriving DecidableEq, Repr

namespace PoisonOr

/-- Directional refinement (`src ⊑ tgt`): `src` is refined by `tgt` iff either
`src` is `.poison` (so the compiler may refine it to any value or `.poison`) or
both are `.value v` with the same value. -/
def Refines {α : Type} (src tgt : PoisonOr α) : Prop :=
  match src, tgt with
  | .poison, _ => True
  | .value v1, .value v2 => v1 = v2
  | .value _, .poison => False

infix:50 " ⊑ " => Refines

theorem refines_refl {α : Type} (x : PoisonOr α) : x ⊑ x := by
  cases x <;> simp [Refines]

theorem refines_trans {α : Type} {x y z : PoisonOr α}
    (h1 : x ⊑ y) (h2 : y ⊑ z) : x ⊑ z := by
  cases x <;> cases y <;> cases z <;> simp [Refines] at h1 h2 ⊢
  exact Eq.trans h1 h2

/-- Refinement is strictly asymmetric: `.poison ⊑ .value v`, but not `.value v ⊑ .poison`. -/
theorem refines_not_symm (v : BitVec 64) :
    ((.poison : PoisonOr (BitVec 64)) ⊑ .value v) ∧
    ¬ ((.value v : PoisonOr (BitVec 64)) ⊑ .poison) := by
  exact ⟨trivial, fun h => h⟩

def map2 {α β γ : Type} (f : α → β → γ) (a : PoisonOr α) (b : PoisonOr β) : PoisonOr γ :=
  match a, b with
  | .value va, .value vb => .value (f va vb)
  | _, _ => .poison

def map1 {α β : Type} (f : α → β) (a : PoisonOr α) : PoisonOr β :=
  match a with
  | .value va => .value (f va)
  | .poison => .poison

theorem map2_mono {α β γ : Type} (f : α → β → γ)
    {a1 a2 : PoisonOr α} {b1 b2 : PoisonOr β}
    (ha : a1 ⊑ a2) (hb : b1 ⊑ b2) :
    map2 f a1 b1 ⊑ map2 f a2 b2 := by
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp [Refines, map2] at ha hb ⊢
  rw [ha, hb]

theorem map1_mono {α β : Type} (f : α → β) {a1 a2 : PoisonOr α} (ha : a1 ⊑ a2) :
    map1 f a1 ⊑ map1 f a2 := by
  cases a1 <;> cases a2 <;> simp [Refines, map1] at ha ⊢
  rw [ha]

end PoisonOr

open PoisonOr

/-- 64-bit expression AST with poison-producing and RISC-V `Zba`/`Zbb` operations. -/
inductive Expr where
  | var      : Nat → Expr
  | const    : BitVec 64 → Expr
  | poison   : Expr
  | addZero  : Expr → Expr
  | mulZero  : Expr → Expr
  | mulFour  : Expr → Expr
  | shlTwo   : Expr → Expr
  | add      : Expr → Expr → Expr
  | sub      : Expr → Expr → Expr
  | and_     : Expr → Expr → Expr
  | not_     : Expr → Expr
  | sh2add   : Expr → Expr → Expr
  | andn     : Expr → Expr → Expr
  deriving DecidableEq, Repr

abbrev Env := Nat → PoisonOr (BitVec 64)

def Expr.eval (env : Env) : Expr → PoisonOr (BitVec 64)
  | .var i       => env i
  | .const c     => .value c
  | .poison      => .poison
  | .addZero a   => map1 (fun (x : BitVec 64) => x + 0#64) (a.eval env)
  | .mulZero a   => map1 (fun (x : BitVec 64) => x * 0#64) (a.eval env)
  | .mulFour a   => map1 (fun (x : BitVec 64) => x * 4#64) (a.eval env)
  | .shlTwo a    => map1 (fun (x : BitVec 64) => x <<< 2) (a.eval env)
  | .add a b     => map2 (· + ·) (a.eval env) (b.eval env)
  | .sub a b     => map2 (· - ·) (a.eval env) (b.eval env)
  | .and_ a b    => map2 (· &&& ·) (a.eval env) (b.eval env)
  | .not_ a      => map1 (~~~ ·) (a.eval env)
  | .sh2add a b  => map2 (fun (x y : BitVec 64) => (x <<< 2) + y) (a.eval env) (b.eval env)
  | .andn a b    => map2 (fun (x y : BitVec 64) => x &&& ~~~y) (a.eval env) (b.eval env)

/-!
## Section 1: Unsoundness of Symmetric E-Graph Equivalence for Poison-Erasing Rules
-/

theorem mul_zero_refines_const_zero (env : Env) (x : Expr) :
    (Expr.mulZero x).eval env ⊑ (Expr.const 0#64).eval env := by
  simp only [Expr.eval]
  cases x.eval env with
  | poison => trivial
  | value v => simp [map1, Refines]

theorem mul_zero_not_symmetric_eq :
    ∃ (env : Env) (x : Expr),
      (Expr.mulZero x).eval env ≠ (Expr.const 0#64).eval env ∧
      ¬ ((Expr.const 0#64).eval env ⊑ (Expr.mulZero x).eval env) := by
  refine ⟨fun _ => .poison, .var 0, ?_, ?_⟩
  · decide
  · simp [Expr.eval, map1, Refines]

/-- Symmetric transitive closure of a set of directed refinement rules can relate
`const 0` to `.poison`, refuting soundness of undirected e-class merging. -/
inductive SymmEGraphEq : Expr → Expr → Prop where
  | mul_zero_fwd (x : Expr) : SymmEGraphEq (.mulZero x) (.const 0#64)
  | symm {a b : Expr} : SymmEGraphEq a b → SymmEGraphEq b a
  | trans {a b c : Expr} : SymmEGraphEq a b → SymmEGraphEq b c → SymmEGraphEq a c

theorem symmetric_eclass_poison_unsound :
    ∃ (src tgt : Expr) (env : Env),
      SymmEGraphEq src tgt ∧
      src.eval env = .value 0#64 ∧
      tgt.eval env = .poison ∧
      ¬ (src.eval env ⊑ tgt.eval env) := by
  refine ⟨.const 0#64, .mulZero .poison, fun _ => .value 0#64, ?_, rfl, rfl, ?_⟩
  · exact SymmEGraphEq.symm (SymmEGraphEq.mul_zero_fwd .poison)
  · simp [Expr.eval, map1, Refines]

/-!
## Section 2: Separating Poison-Exact Bidirectional Rules from Poison-Monotonic Directed Rules
-/

inductive BiEqRule where
  | addZero    -- addZero x <-> x
  | mulFourShl -- mulFour x <-> shlTwo x
  | sh2addFuse -- add (shlTwo x) y <-> sh2add x y
  | andnFuse   -- and_ x (not_ y) <-> andn x y
  | addComm    -- add x y <-> add y x
  deriving DecidableEq, Repr

inductive DirRefineRule where
  | mulZero    -- mulZero x -> 0
  | subSelf    -- sub x x -> 0
  deriving DecidableEq, Repr

def applyBiEqForward (r : BiEqRule) (e : Expr) : Option Expr :=
  match r, e with
  | .addZero, .addZero x => some x
  | .mulFourShl, .mulFour x => some (.shlTwo x)
  | .sh2addFuse, .add (.shlTwo x) y => some (.sh2add x y)
  | .andnFuse, .and_ x (.not_ y) => some (.andn x y)
  | .addComm, .add x y => some (.add y x)
  | _, _ => none

def applyDirRefine (r : DirRefineRule) (e : Expr) : Option Expr :=
  match r, e with
  | .mulZero, .mulZero _ => some (.const 0#64)
  | .subSelf, .sub x y => if x == y then some (.const 0#64) else none
  | _, _ => none

theorem bv64_mul_four_eq_shl_two (v : BitVec 64) :
    v * 4#64 = v <<< 2 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft]
  omega

theorem applyBiEqForward_eq (r : BiEqRule) (e e' : Expr) (env : Env)
    (h : applyBiEqForward r e = some e') :
    e.eval env = e'.eval env := by
  cases r with
  | addZero =>
    cases e <;> simp [applyBiEqForward] at h
    subst h
    simp only [Expr.eval]
    cases ‹Expr›.eval env <;> simp [map1]
  | mulFourShl =>
    cases e <;> simp [applyBiEqForward] at h
    subst h
    simp only [Expr.eval]
    cases ‹Expr›.eval env with
    | poison => rfl
    | value v =>
      simp only [map1]
      congr 1
      exact bv64_mul_four_eq_shl_two v
  | sh2addFuse =>
    cases e <;> simp [applyBiEqForward] at h
    rename_i a b
    cases a <;> simp at h
    subst h
    simp only [Expr.eval]
    cases ‹Expr›.eval env <;> cases b.eval env <;> rfl
  | andnFuse =>
    cases e <;> simp [applyBiEqForward] at h
    rename_i a b
    cases b <;> simp at h
    subst h
    simp only [Expr.eval]
    cases a.eval env <;> cases ‹Expr›.eval env <;> rfl
  | addComm =>
    cases e <;> simp [applyBiEqForward] at h
    rename_i a b
    subst h
    simp only [Expr.eval]
    cases a.eval env <;> cases b.eval env <;> simp [map2, BitVec.add_comm]

theorem applyDirRefine_refines (r : DirRefineRule) (e e' : Expr) (env : Env)
    (h : applyDirRefine r e = some e') :
    e.eval env ⊑ e'.eval env := by
  cases r with
  | mulZero =>
    cases e <;> simp [applyDirRefine] at h
    subst h
    exact mul_zero_refines_const_zero env _
  | subSelf =>
    cases e <;> simp [applyDirRefine] at h
    rcases h with ⟨hab, rfl⟩
    subst hab
    simp only [Expr.eval]
    cases ‹Expr›.eval env with
    | poison => trivial
    | value v => simp [map2, Refines]

/-!
## Section 3: Directed Refinement Certificate Checker with Subterm Paths
-/

inductive Dir where
  | left
  | right
  | unary
  deriving DecidableEq, Repr

abbrev Path := List Dir

inductive CertAction where
  | biFwd  : BiEqRule → CertAction
  | biBwd  : BiEqRule → Expr → CertAction
  | dirRef : DirRefineRule → CertAction
  deriving DecidableEq, Repr

structure DirectedRewriteStep where
  path   : Path
  action : CertAction
  deriving DecidableEq, Repr

def applyAtRoot (act : CertAction) (e : Expr) : Option Expr :=
  match act with
  | .biFwd r => applyBiEqForward r e
  | .biBwd r cand =>
    match applyBiEqForward r cand with
    | some e' => if e' == e then some cand else none
    | none => none
  | .dirRef r => applyDirRefine r e

theorem applyAtRoot_refines (act : CertAction) (e e' : Expr) (env : Env)
    (h : applyAtRoot act e = some e') :
    e.eval env ⊑ e'.eval env := by
  cases act with
  | biFwd r =>
    have heq := applyBiEqForward_eq r e e' env h
    rw [heq]
    exact refines_refl _
  | biBwd r cand =>
    simp only [applyAtRoot] at h
    cases hfwd : applyBiEqForward r cand with
    | none => simp [hfwd] at h
    | some target =>
      simp [hfwd] at h
      rcases h with ⟨rfl, rfl⟩
      have heq := applyBiEqForward_eq r cand target env hfwd
      rw [← heq]
      exact refines_refl _
  | dirRef r =>
    exact applyDirRefine_refines r e e' env h

def applyAtPath : Path → CertAction → Expr → Option Expr
  | [], act, e => applyAtRoot act e
  | .unary :: ps, act, .addZero a => (applyAtPath ps act a).map Expr.addZero
  | .unary :: ps, act, .mulZero a => (applyAtPath ps act a).map Expr.mulZero
  | .unary :: ps, act, .mulFour a => (applyAtPath ps act a).map Expr.mulFour
  | .unary :: ps, act, .shlTwo a  => (applyAtPath ps act a).map Expr.shlTwo
  | .unary :: ps, act, .not_ a    => (applyAtPath ps act a).map Expr.not_
  | .left :: ps, act, .add a b    => (applyAtPath ps act a).map (Expr.add · b)
  | .right :: ps, act, .add a b   => (applyAtPath ps act b).map (Expr.add a ·)
  | .left :: ps, act, .sub a b    => (applyAtPath ps act a).map (Expr.sub · b)
  | .right :: ps, act, .sub a b   => (applyAtPath ps act b).map (Expr.sub a ·)
  | .left :: ps, act, .and_ a b   => (applyAtPath ps act a).map (Expr.and_ · b)
  | .right :: ps, act, .and_ a b  => (applyAtPath ps act b).map (Expr.and_ a ·)
  | .left :: ps, act, .sh2add a b => (applyAtPath ps act a).map (Expr.sh2add · b)
  | .right :: ps, act, .sh2add a b => (applyAtPath ps act b).map (Expr.sh2add a ·)
  | .left :: ps, act, .andn a b   => (applyAtPath ps act a).map (Expr.andn · b)
  | .right :: ps, act, .andn a b  => (applyAtPath ps act b).map (Expr.andn a ·)
  | _, _, _ => none

theorem applyAtPath_refines (p : Path) (act : CertAction) (e e' : Expr) (env : Env)
    (h : applyAtPath p act e = some e') :
    e.eval env ⊑ e'.eval env := by
  induction p generalizing e e' with
  | nil => exact applyAtRoot_refines act e e' env h
  | cons d ps ih =>
    cases d <;> cases e <;> simp [applyAtPath] at h
    all_goals
      rcases h with ⟨sub', hsub, rfl⟩
      have ih_sub := ih _ _ hsub
      first
      | exact map2_mono _ ih_sub (refines_refl _)
      | exact map2_mono _ (refines_refl _) ih_sub
      | exact map1_mono _ ih_sub

def checkDirectedRefinementTrace (src : Expr) (trace : List DirectedRewriteStep) (dst : Expr) : Bool :=
  match trace with
  | [] => src == dst
  | step :: rest =>
    match applyAtPath step.path step.action src with
    | some mid => checkDirectedRefinementTrace mid rest dst
    | none => false

theorem checkDirectedRefinementTrace_sound (src : Expr) (trace : List DirectedRewriteStep) (dst : Expr)
    (h : checkDirectedRefinementTrace src trace dst = true) (env : Env) :
    src.eval env ⊑ dst.eval env := by
  induction trace generalizing src with
  | nil =>
    simp [checkDirectedRefinementTrace] at h
    subst h
    exact refines_refl _
  | cons step rest ih =>
    simp [checkDirectedRefinementTrace] at h
    cases hstep : applyAtPath step.path step.action src with
    | none => simp [hstep] at h
    | some mid =>
      simp [hstep] at h
      exact refines_trans (applyAtPath_refines step.path step.action src mid env hstep) (ih mid h)

/-- Concrete end-to-end verified refinement certificate combining poison-Exact `andnFuse`,
`mulFourShl`, `addZero`, and `sh2addFuse`. -/
def sampleSrc : Expr :=
  .add (.mulFour (.and_ (.var 0) (.not_ (.var 1))))
       (.addZero (.var 2))

def sampleDst : Expr :=
  .sh2add (.andn (.var 0) (.var 1)) (.var 2)

def sampleTrace : List DirectedRewriteStep :=
  [ { path := [.right],       action := .biFwd .addZero }
  , { path := [.left, .unary], action := .biFwd .andnFuse }
  , { path := [.left],        action := .biFwd .mulFourShl }
  , { path := [],             action := .biFwd .sh2addFuse }
  ]

theorem sampleTrace_verified (env : Env) :
    sampleSrc.eval env ⊑ sampleDst.eval env :=
  checkDirectedRefinementTrace_sound sampleSrc sampleTrace sampleDst rfl env

/-- info: 'EGraphRefinementProofs.symmetric_eclass_poison_unsound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms symmetric_eclass_poison_unsound

/-- info: 'EGraphRefinementProofs.checkDirectedRefinementTrace_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkDirectedRefinementTrace_sound

/-- info: 'EGraphRefinementProofs.sampleTrace_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sampleTrace_verified

end EGraphRefinementProofs
