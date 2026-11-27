// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Zero-false-positive regressions for compiler-generated specification
//! definitions in `prelude`, unpinned `Init`, and `module` modes.

use super::*;

const RICH_DERIVE_SPEC_BODY: &str = r#"namespace SpecDerive
inductive Color where
  | red
  | green
  | blue
  deriving BEq, DecidableEq, Repr, Inhabited, Ord, Hashable

structure Pair (α : Type) where
  fst : α
  snd : Nat
  deriving BEq, DecidableEq, Repr, Inhabited, Ord, Hashable

structure EmptyStruct where

structure Phantom (α : Type) where

structure PrivCtorStruct where
  private mk ::
  val : Nat

structure Config (α : Type) where
  limit : Nat := 10
  payload : α

structure ConfigChild (α : Type) extends Config α where
  limit := 20
  extra : Nat := 1

structure DepDefault (α : Type) where
  x : Nat := 1
  y : Nat := x + 1

structure PubWithPrivField (α : Type) where
  private limit : Nat := 10
  payload : α

structure PubWithPrivFieldChild (α : Type) extends PubWithPrivField α where
  extra : Nat := 1

structure Base where
structure Left extends Base where
structure Right extends Base where
structure Diamond extends Left, Right where

structure BaseVal (α : Type) where
  b : α
  sharedOpt : Nat := 5

structure LeftVal (α : Type) extends BaseVal α where
  l : Nat := 1

structure RightVal (α : Type) extends BaseVal α where
  r : Nat := 2

structure DiamondVal (α : Type) extends LeftVal α, RightVal α where
  sharedOpt := 9
  d : Nat := 3

structure IndirectSub0 (α : Type) where
  s0 : α
  deepOpt : Nat := 4

structure IndirectSub1 (α : Type) extends IndirectSub0 α where
  clash : Nat := 7

structure IndirectPeer (α : Type) where
  clash : Nat := 8

structure IndirectDiamond (α : Type) extends IndirectPeer α, IndirectSub1 α where
  deepOpt := 11

inductive SecretTag (α : Type) where
  | private a (n : Nat)
  | private b

def listSum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + listSum rest

private def privListSum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + privListSum rest

noncomputable def noncompSum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + noncompSum rest

def boundedSum (xs : List Nat) (n : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest =>
    if h : x < n then (⟨x, h⟩ : Fin n).val + boundedSum rest n
    else boundedSum rest n

def boundedElse (xs : List Nat) (n : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest =>
    if h : x < n then boundedElse rest n
    else
      have _ := h
      x + boundedElse rest n

theorem sumNonneg : ∀ xs, 0 ≤ listSum xs
  | [] => Nat.zero_le _
  | _ :: rest => by
    have ih := sumNonneg rest
    exact Nat.zero_le _

theorem listTriv : List Nat → True
  | [] => trivial
  | _ :: rest => listTriv rest

def tailOther (xs : List Nat) (acc : Nat) : Nat :=
  match xs with
  | [] => acc
  | x :: rest => tailOther rest (acc + x)

set_option linter.defProp false in
def weirdProp : Nat → True
  | 0 => trivial
  | n + 1 => weirdProp n

set_option linter.defProp false in
noncomputable def noncompPropProof (k : Nat) : List Nat → True
  | [] =>
    have _ := k
    trivial
  | _ :: rest => noncompPropProof k rest

set_option linter.defProp false in
noncomputable def propStructList (k : Nat) : List Nat → Prop
  | [] => k = k
  | x :: rest => x = x ∧ propStructList k rest

mutual
  noncomputable def propMutPassA (k : Nat) : List Nat → Prop
    | [] => k = k
    | _ :: xs => propMutPassB k xs

  noncomputable def propMutPassB (k : Nat) : List Nat → Prop
    | [] => True
    | _ :: xs => propMutPassA k xs
end

mutual
  def mutStructA : List Nat → Nat
    | [] => 0
    | x :: xs => x + mutStructB xs

  def mutStructB : List Nat → Nat
    | [] => 1
    | _ :: xs => mutStructA xs
end

mutual
  def mutPassA (k : Nat) : List Nat → Nat
    | [] => k
    | x :: xs => x + mutPassB k xs

  def mutPassB (k : Nat) : List Nat → Nat
    | [] => 0
    | _ :: xs => mutPassA k xs
end

mutual
  def mutDiteA (n : Nat) : List Nat → Nat
    | [] => 0
    | x :: xs =>
      if h : x < n then (⟨x, h⟩ : Fin n).val + mutDiteB n xs
      else mutDiteB n xs

  def mutDiteB (n : Nat) : List Nat → Nat
    | [] => 1
    | _ :: xs => mutDiteA n xs
end

mutual
  private def privMutPassA (k : Nat) : List Nat → Nat
    | [] => k
    | x :: xs => x + privMutPassB k xs

  private def privMutPassB (k : Nat) : List Nat → Nat
    | [] => 0
    | _ :: xs => privMutPassA k xs
end

structure BaseDef1 (α : Type) where
  req : α
  opt : Nat := 10

structure BaseDef2 (α : Type) where
  req2 : α
  c2 : Nat := 30

structure CopiedDefChild (α : Type) extends BaseDef1 α, BaseDef2 α where
  own : Nat := 1

inductive ExprAst where
  | lit (n : Nat)
  | add (l r : ExprAst)
  deriving BEq, DecidableEq, Repr, Inhabited

inductive Rose where
  | node (children : List Rose)

def roseHead : Rose → Nat
  | .node [] => 0
  | .node (r :: _) => 1 + roseHead r

mutual
  def roseSum (bound : Nat) : Rose → Nat
    | .node rs => roseListSum bound rs

  def roseListSum (bound : Nat) : List Rose → Nat
    | [] => 0
    | r :: rs =>
      let v := roseSum bound r
      (if v < bound then v else bound) + roseListSum bound rs
end

inductive Rose.ibelow where
  | x
  | y

mutual
  inductive EvenT where
    | zero
    | succ (o : OddT)
  inductive OddT where
    | succ (e : EvenT)
end

def evenDepth : EvenT → Nat
  | .zero => 0
  | .succ (.succ e) => 1 + evenDepth e

mutual
  inductive MutA where
    | mk (xs : List MutB)
  inductive MutB where
    | mk (a : MutA)
end

inductive PP : Prop where
  | z
  | s (p : PP)

def MyPred (α : Type) := α → Prop

inductive FamP : MyPred Nat where
  | zero : FamP 0

def wfCount (α : Type) (xs : List α) (n : Nat) : Nat :=
  match n with
  | 0 => xs.length
  | k + 1 => wfCount α xs k
termination_by n
decreasing_by exact Nat.lt_add_one _

mutual
  def wfEven : Nat → Bool
    | 0 => true
    | n + 1 => wfOdd n
  termination_by n => n
  decreasing_by exact Nat.lt_add_one _

  def wfOdd : Nat → Bool
    | 0 => false
    | n + 1 => wfEven n
  termination_by n => n
  decreasing_by exact Nat.lt_add_one _
end

mutual
  def wfTri1A (y : Nat) : Nat → Nat
    | 0 => y
    | k + 1 => wfTri1B y k
  termination_by x => (x, 2)

  def wfTri1B (y : Nat) : Nat → Nat
    | 0 => y
    | k + 1 => wfTri1C y k
  termination_by x => (x, 1)

  def wfTri1C (y : Nat) : Nat → Nat
    | 0 => y
    | k + 1 => wfTri1A y k
  termination_by x => (x, 0)
end

def sparseNat (n : Nat) : Nat :=
  match n with
  | 0 => 10
  | 40 => 20
  | _ => 30

private def privSparse (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 30 => 2
  | _ => 3

def overlapPub (x y : Nat) : Nat :=
  match x, y with
  | 0, _ => 1
  | _, 0 => 2
  | a + 1, b + 1 => a + b

theorem overlapSplit (x y : Nat) : overlapPub x y ≤ x + y + 2 := by
  unfold overlapPub
  split <;> simp_all <;> omega

private def privOverlap (x y : Nat) : Nat :=
  match x, y with
  | 0, _ => 1
  | _, 0 => 2
  | a + 1, b + 1 => a + b

private theorem privOverlapSplit (x y : Nat) : 0 ≤ privOverlap x y := by
  unfold privOverlap
  split <;> exact Nat.zero_le _

def nonOverlapPub (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => k + 2

theorem nonOverlapPubSplit (n : Nat) : 0 < nonOverlapPub n := by
  unfold nonOverlapPub
  split <;> omega

private def privNonOverlap (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => k + 2

private theorem privNonOverlapSplit (n : Nat) : 0 < privNonOverlap n := by
  unfold privNonOverlap
  split <;> omega

def structNestedMatch (xs : List Nat) (flag : Bool) : Nat :=
  match xs with
  | [] => 0
  | x :: rest =>
    match flag with
    | true => x + structNestedMatch rest false
    | false => structNestedMatch rest true

def wfMeasureSubexpr (u : Nat) (n : Nat) : Nat → Nat :=
  match n with
  | 0 => fun x => u + x
  | k + 1 => wfMeasureSubexpr u k
termination_by u + n

structure CallbackSpec where
  cb : (arg : Nat) → Bool

inductive ParamWithBinder (f : (x : Nat) → Type) where
  | c1 (v : f 0)
  | c2 (n : Nat)

structure CopiedP1 (P : (x : Nat) → Prop) where
  val : Nat := 1

structure CopiedP2 (P : (x : Nat) → Prop) where
  other : Nat := 2

structure CopiedDiamond (P : (x : Nat) → Prop) extends CopiedP1 P, CopiedP2 P where
  extra : (t : Nat) → Bool := fun _ => true

structure ArrowParent1 (α : Type) where
  a : Nat := 1

structure ArrowParent2 (α : Type) where
  b : Nat := 2

structure ChildArrowParent
    extends ArrowParent1 ((y : Nat) → Bool), ArrowParent2 ((y : Nat) → Bool) where

structure DepArrowDefault where
  f : (a : Nat) → Nat := fun x => x
  g : (b : Nat) → Nat := fun y => f y

set_option linter.defProp false in
def ppRecDef : PP → True
  | .z => trivial
  | .s p => ppRecDef p

mutual
  inductive EvenP : Prop where
    | zero
    | succ (o : OddP)
  inductive OddP : Prop where
    | succ (e : EvenP)
end

mutual
  noncomputable def evenPRec : EvenP → True
    | .zero => trivial
    | .succ o => oddPRec o

  noncomputable def oddPRec : OddP → True
    | .succ e => evenPRec e
end

set_option linter.defProp false in
def evenP2Step : EvenP → True
  | .zero => trivial
  | .succ (.succ e) => evenP2Step e

inductive IdxProp : Nat → Prop where
  | z : IdxProp 0
  | s {n : Nat} : IdxProp n → IdxProp (n + 1)

set_option linter.defProp false in
noncomputable def idxPropRec : ∀ {n}, IdxProp n → True
  | _, .z => trivial
  | _, .s h => idxPropRec h

inductive Big10 (α : Type) where
  | c0 (x : α) | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9
  deriving BEq, DecidableEq, Ord

inductive OneEnum where
  | only
  deriving DecidableEq

structure EmptyDec where
  deriving DecidableEq

set_option linter.defProp false in
def propWfSingle (n : Nat) : True :=
  match n with
  | 0 => trivial
  | k + 1 => propWfSingle k
termination_by n
decreasing_by exact Nat.lt_add_one _

set_option linter.defProp false in
def propWfUnary (u : Nat) (a b : Nat) : True :=
  match b with
  | 0 =>
    have _ := u
    have _ := a
    trivial
  | k + 1 => propWfUnary u (a + 1) k
termination_by b
decreasing_by exact Nat.lt_add_one _

mutual
  noncomputable def propWfMutA (x : Nat) : True :=
    match x with
    | 0 => trivial
    | k + 1 => propWfMutB k
  termination_by x
  decreasing_by exact Nat.lt_add_one _

  noncomputable def propWfMutB (x : Nat) : True :=
    match x with
    | 0 => trivial
    | k + 1 => propWfMutA k
  termination_by x
  decreasing_by exact Nat.lt_add_one _
end

set_option linter.defProp false in
def countUpProp (n i : Nat) : True :=
  if h : i < n then countUpProp n (i + 1) else trivial
termination_by n - i
end SpecDerive

def Spec.specs (p : BitVec 8) : Prop :=
  BitVec.and p p = p ∧ SpecDerive.sparseNat 0 = 10
"#;

/// Compiler-generated inductive, structure, diamond-coercion, `_flat_ctor`,
/// `_sunfold`, structural theorem/def, mutual structural, and well-founded
/// helpers must emit zero `unused_spec_binding` false positives in `prelude`
/// mode despite `loadExts := false`.
#[test]
fn gate_g4_suppresses_compiler_generated_prelude_spec_defs() {
    let proof_conj = "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
                      theorem Proof.verify : Expected.claim :=\n  \
                        ⟨rfl, BitVec.and_self, rfl, Or.inl rfl⟩\n";
    let mut f_prelude = Fixture::new(proof_conj);
    f_prelude.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
         structure ModelConfig (α : Type) where\n  limit : Nat := 10\n  payload : α\n\
         end Trusted.MirSemantics\n",
    );
    f_prelude.set(
        "SpecBare",
        TargetRole::Specification,
        "prelude\ninductive BareInd where | a | b\n\
         inductive BareParam (α : Type) where | a | b\n",
    );
    f_prelude.set(
        "Spec",
        TargetRole::Specification,
        r#"prelude
import Model
import Init.Data.List.Basic
import SpecBare

namespace SpecRich
inductive Color where
  | red
  | green
  | blue

inductive UnitInd where
  | mk

inductive EmptyInd where

structure EmptyStruct where

structure Phantom (α : Type) where

structure WithSub (n : Nat) where
  h : n = n

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α .zero
  | cons (n : Nat) : α → Vec α n → Vec α (.succ n)

structure Box where
  val : Nat

structure ZeroBox where
  val : Nat

structure Pair (α : Type) where
  fst : α
  snd : Nat

structure Child extends Pair Bool where
  extra : Nat

structure Base where
structure Left extends Base where
structure Right extends Base where
structure Diamond extends Left, Right where

structure Config (α : Type) where
  limit : Nat := 10
  payload : α

structure ConfigChild (α : Type) extends Config α where
  limit := 20
  extra : Nat := 2

structure DepDefault (α : Type) where
  x : Nat := 1
  y : Nat := x + 1

structure PubWithPrivField (α : Type) where
  private limit : Nat := 10
  payload : α

structure PubWithPrivFieldChild (α : Type) extends PubWithPrivField α where
  extra : Nat := 1

inductive SecretTag (α : Type) where
  | private a (n : Nat)
  | private b

def listSum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + listSum rest

private def privListSum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + privListSum rest

def boundedSum (xs : List Nat) (n : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest =>
    if h : x < n then (⟨x, h⟩ : Fin n).val + boundedSum rest n
    else boundedSum rest n

theorem sumNonneg : ∀ xs, 0 ≤ listSum xs
  | [] => Nat.zero_le _
  | _ :: rest => by
    have ih := sumNonneg rest
    exact Nat.zero_le _

theorem listTriv : List Nat → True
  | [] => trivial
  | _ :: rest => listTriv rest

def tailOther (xs : List Nat) (acc : Nat) : Nat :=
  match xs with
  | [] => acc
  | x :: rest => tailOther rest (acc + x)

set_option linter.defProp false in
def weirdProp : Nat → True
  | 0 => trivial
  | n + 1 => weirdProp n

set_option linter.defProp false in
noncomputable def noncompPropProof (k : Nat) : List Nat → True
  | [] =>
    have _ := k
    trivial
  | _ :: rest => noncompPropProof k rest

set_option linter.defProp false in
noncomputable def propStructList (k : Nat) : List Nat → Prop
  | [] => k = k
  | x :: rest => x = x ∧ propStructList k rest

mutual
  def mutStructA : List Nat → Nat
    | [] => 0
    | x :: xs => x + mutStructB xs

  def mutStructB : List Nat → Nat
    | [] => 1
    | _ :: xs => mutStructA xs
end

mutual
  def mutPassA (k : Nat) : List Nat → Nat
    | [] => k
    | x :: xs => x + mutPassB k xs

  def mutPassB (k : Nat) : List Nat → Nat
    | [] => 0
    | _ :: xs => mutPassA k xs
end

class HasTag (α : Type) where
  tag : α → Nat

class HasDefClass (α : Type) where
  num : Nat := 0
  payload : α

inductive ExprAst where
  | lit (n : Nat)
  | add (l r : ExprAst)

inductive Rose where
  | node (children : List Rose)

def roseHead : Rose → Nat
  | .node [] => 0
  | .node (r :: _) => 1 + roseHead r

mutual
  def roseSum (bound : Nat) : Rose → Nat
    | .node rs => roseListSum bound rs

  def roseListSum (bound : Nat) : List Rose → Nat
    | [] => 0
    | r :: rs =>
      let v := roseSum bound r
      (if v < bound then v else bound) + roseListSum bound rs
end

inductive Rose.ibelow where
  | x
  | y

mutual
  inductive EvenT where
    | zero
    | succ (o : OddT)
  inductive OddT where
    | succ (e : EvenT)
end

def evenDepth : EvenT → Nat
  | .zero => 0
  | .succ (.succ e) => 1 + evenDepth e

mutual
  inductive MutA where
    | mk (xs : List MutB)
  inductive MutB where
    | mk (a : MutA)
end

inductive PP : Prop where
  | z
  | s (p : PP)

def MyPred (α : Type) := α → Prop

inductive FamP : MyPred Nat where
  | zero : FamP 0

inductive POr (P Q : Prop) : Prop where
  | inl (h : P)
  | inr (h : Q)

def testMatch (c : Color) : Nat :=
  match c with
  | .red => 0
  | .green => 1
  | .blue => 2

private def privMatch (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | _ => 2

def useRose (r : Rose) : Nat :=
  match r with
  | .node xs => xs.length

def wfCount (α : Type) (xs : List α) (n : Nat) : Nat :=
  match n with
  | 0 => xs.length
  | k + 1 => wfCount α xs k
termination_by n
decreasing_by exact Nat.lt_add_one _

def wfAdd (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => wfAdd k
termination_by n
decreasing_by exact Nat.lt_add_one _

mutual
  def wfEven : Nat → Bool
    | 0 => true
    | n + 1 => wfOdd n
  termination_by n => n
  decreasing_by exact Nat.lt_add_one _

  def wfOdd : Nat → Bool
    | 0 => false
    | n + 1 => wfEven n
  termination_by n => n
  decreasing_by exact Nat.lt_add_one _
end

structure SpecFromModel (α : Type) extends Trusted.MirSemantics.ModelConfig α where
  extra : Nat := 1

structure CallbackSpec where
  cb : (arg : Nat) → Bool

inductive ParamWithBinder (f : (x : Nat) → Type) where
  | c1 (v : f 0)
  | c2 (n : Nat)

structure CopiedP1 (P : (x : Nat) → Prop) where
  val : Nat := 1

structure CopiedP2 (P : (x : Nat) → Prop) where
  other : Nat := 2

structure CopiedDiamond (P : (x : Nat) → Prop) extends CopiedP1 P, CopiedP2 P where
  extra : (t : Nat) → Bool := fun _ => true

set_option linter.defProp false in
def ppRecDef : PP → True
  | .z => trivial
  | .s p => ppRecDef p

set_option linter.defProp false in
def propWfUnary (u : Nat) (a b : Nat) : True :=
  match b with
  | 0 =>
    have _ := u
    have _ := a
    trivial
  | k + 1 => propWfUnary u (a + 1) k
termination_by b
decreasing_by exact Nat.lt_add_one _
end SpecRich

def Spec.specs (p : BitVec 8) : Prop :=
  BitVec.and p p = p ∧ SpecRich.testMatch .red = 0 ∧
    (BareInd.a = BareInd.a ∨ True)
"#,
    );
    let rep_prelude = f_prelude.run().unwrap();
    assert_eq!(rep_prelude["replay"], true);
    assert_eq!(rep_prelude["specWarnings"], serde_json::json!([]));
}

/// Unpinned `Init` + `deriving`, `split`-generated `.splitter` helpers,
/// diamond coercions, and mutual structural definitions emit zero false
/// positives in both non-`module` and `module` modes.
#[test]
fn gate_g4_suppresses_compiler_generated_init_and_module_spec_defs() {
    let mut f_init = Fixture::new(
        "import Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim := ⟨rfl, BitVec.and_self, rfl⟩\n",
    );
    f_init.set(
        "Spec",
        TargetRole::Specification,
        &format!("import Model\n{RICH_DERIVE_SPEC_BODY}"),
    );
    let mut checker_init = f_init.cargo_checker();
    checker_init.set_allow_unpinned_lean(true);
    let rep_init = checker_init.run_target(&f_init.request).unwrap();
    assert_eq!(rep_init["specWarnings"], serde_json::json!([]));

    let mut f_mod = Fixture::new(
        "module\nprelude\npublic import Expected\nimport Init.Data.BitVec.Lemmas\n\
         public theorem Proof.verify : Expected.claim := ⟨rfl, BitVec.and_self, rfl⟩\n",
    );
    f_mod.set(
        "Model",
        TargetRole::Model,
        "module\nprelude\npublic import Init.Data.BitVec.Basic\n\
         @[expose] public section\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
         end Trusted.MirSemantics\nend\n",
    );
    f_mod.set(
        "Captured",
        TargetRole::Capture,
        "module\nprelude\npublic import Model\n\
         @[expose] public section\n\
         def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n\
         end\n",
    );
    f_mod.set(
        "Spec",
        TargetRole::Specification,
        &format!(
            "module\npublic import Model\n@[expose] public section\n{RICH_DERIVE_SPEC_BODY}\nend\n"
        ),
    );
    f_mod.set(
        "Expected",
        TargetRole::Expected,
        "module\nprelude\npublic import Captured\npublic import Spec\n\
         @[expose] public section\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheorem \
             (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n\
         end\n",
    );
    let mut checker_mod = f_mod.cargo_checker();
    checker_mod.set_allow_unpinned_lean(true);
    let rep_mod = checker_mod.run_target(&f_mod.request).unwrap();
    assert_eq!(rep_mod["specWarnings"], serde_json::json!([]));
}
