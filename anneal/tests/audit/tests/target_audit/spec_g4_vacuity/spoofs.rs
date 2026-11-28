// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Adversarial suffix, private `.splitter`, diamond-coercion, `_sunfold`,
//! `_flat_ctor`, structural `dite`, and mutual structural spoof regressions.

use super::*;

/// Adversarial definitions mimicking compiler-generated names, private
/// internal details, lazy private `.splitter` helpers, zero-padded nested
/// suffixes, `Prop` recursor suffixes, `_sunfold`, `_flat_ctor`, `toCtorIdx`,
/// suppressed `ctorIdx`, structural `dite` unused binders, mutual structural
/// unused fixed parameters, and fake projections must all trigger
/// `unused_spec_binding`.
#[test]
fn gate_g4_catches_adversarial_compiler_suffix_and_private_spoofs() {
    let mut f = Fixture::new(SIMPLE_PROOF);
    f.set(
        "Model",
        TargetRole::Model,
        "prelude\nimport Init.Data.BitVec.Basic\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
         structure ModelParentCfg (α : Type) where\n  limit : Nat := 10\n  payload : α\n\
         end Trusted.MirSemantics\n",
    );
    f.set(
        "SpecBare",
        TargetRole::Specification,
        r#"prelude
inductive BareInd where
  | a
  | b

-- Positive control in 0-import `prelude`: Lean generates `BareInd.recOn`,
-- whereas `casesOn` and `mkAuxConstructions` / `SizeOf` helpers are omitted.
inductive BareParam (α : Type) where
  | a
  | b

-- `mkAuxConstructions` and `SizeOf` spoofs in 0-import `prelude`.
def BareInd.casesOn (u : BareInd) : Prop := ∀ (p : Prop), p → p
def BareInd.noConfusion (u : BareInd) : Prop := ∀ (p : Prop), p → p
def BareInd.noConfusionType (u : BareInd) : Prop := ∀ (p : Prop), p → p
def BareInd.ctorIdx (u : BareInd) : Prop := ∀ (p : Prop), p → p
def BareInd.ctorElim (u : BareInd) : Prop := ∀ (p : Prop), p → p
def BareInd.below (u : BareInd) : Prop := ∀ (p : Prop), p → p
def BareInd.brecOn (u : BareInd) : Prop := ∀ (p : Prop), p → p
def BareInd.a.elim (u : BareInd) : Prop := ∀ (p : Prop), p → p
def BareInd.a.noConfusion (u : BareInd) : Prop := ∀ (p : Prop), p → p
def BareInd._sizeOf_1 (u : BareInd) : Prop := ∀ (p : Prop), p → p
def BareInd._sizeOf_inst (u : BareInd) : Prop := ∀ (p : Prop), p → p
"#,
    );
    f.set(
        "SpecMatch",
        TargetRole::Specification,
        "prelude\nimport Init.Data.List.Basic\n\
         def pubSharedMatch (n : Nat) : Nat := match n with | 0 => 1 | _ => 2\n",
    );
    f.set(
        "Expected",
        TargetRole::Expected,
        "prelude\nimport Captured\nimport Spec\nimport SpecMatch\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheorem\n    \
             (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        r#"prelude
import Model
import Init.Data.List.Basic
import SpecBare

namespace Spoofs
inductive Color where
  | red
  | green

inductive UnitInd where
  | mk

inductive Wrap where
  | mk (n : Nat)

inductive OneCtor (f : Nat → Type) where
  | mk (val : Nat)

structure Box where
  val : Nat

structure ZeroBox where
  val : Nat

structure Pair (α : Type) where
  fst : α
  snd : Nat

structure Base where
structure Left extends Base where
structure Right extends Base where
structure Diamond extends Left, Right where

structure PlainBase where
structure PlainChild extends PlainBase where

structure Config (α : Type) where
  limit : Nat := 10
  payload : α

class HasTag (α : Type) where
  tag : α → Nat

inductive ExprAst where
  | lit (n : Nat)
  | add (l r : ExprAst)

mutual
  inductive EvenT where
    | zero
    | succ (o : OddT)
  inductive OddT where
    | succ (e : EvenT)
end

mutual
  inductive MA where
    | mk (xs : List MB)
  inductive MB where
    | mk (a : MA)
end

inductive Rose where
  | node (children : List Rose)

inductive PP : Prop where
  | z
  | s (p : PP)

private inductive PrivPP : Prop where
  | z
  | s (p : PrivPP)

def MyPred (α : Type) := α → Prop

inductive FamP : MyPred Nat where
  | zero : FamP 0

inductive POr (P Q : Prop) : Prop where
  | inl (h : P)
  | inr (h : Q)

def pubMatch (c : Color) : Nat :=
  match c with
  | .red => 0
  | .green => 1

private def myPrivMatch (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | _ => 2

private def myPrivMatch.match_1.splitter (unused : Nat) : Prop := True

theorem someThm : True := trivial
def nonStructDef (n : Nat) : Nat := n

theorem recThmForSunfold : List Nat → True
  | [] => trivial
  | _ :: xs => recThmForSunfold xs

set_option linter.defProp false in
def propProofForSunfold : List Nat → True
  | [] => trivial
  | _ :: xs => propProofForSunfold xs

-- `Prop` / WHNF-`Prop` inductive spoofs
def PP.ctorElim (u : Nat) : Prop := True
def PP.ctorElimType (u : Nat) : Prop := True
def PP.noConfusion (u : Nat) : Prop := True
def PP.noConfusionType (u : Nat) : Prop := True
def PP.ctorIdx (u : Nat) : Prop := True
def PP.ibelow (u : Nat) : Prop := True
def PP.binductionOn (u : Nat) : Prop := True
def PP.z.elim (u : Nat) : Prop := True
def PP.z.noConfusion (u : Nat) : Prop := True
def POr.ctorElim (u : Nat) : Prop := True
def POr.inl.elim (u : Nat) : Prop := True
def PP.below.below (u : Nat) : Prop := True
def PP.below.ctorElim (u : Nat) : Prop := True
def PP.below.recOn (u : Nat) : Prop := True
def PP.below.noConfusion (u : Nat) : Prop := True
private def PrivPP.below.recOn (u : Nat) : Prop := True
def FamP.noConfusion (u : Nat) : Prop := True
def FamP.noConfusionType (u : Nat) : Prop := True
def FamP.ctorIdx (u : Nat) : Prop := True
def FamP.ctorElim (u : Nat) : Prop := True
def FamP.zero.elim (u : Nat) : Prop := True
def FamP._sizeOf_1 (u : Nat) : Nat := 0

-- Zero-padded, out-of-bounds, class, and non-head mutual nested spoofs
def Rose.below_01 (u : Nat) : Prop := True
def Rose.brecOn_01 (u : Nat) : Prop := True
def Rose.below_99 (u : Nat) : Prop := True
def Rose.brecOn_99 (u : Nat) : Prop := True
def Color._sizeOf_2 (u : Nat) : Nat := 0
def Color._sizeOf_99 (u : Nat) : Nat := 0
def Color._sizeOf_01 (u : Nat) : Nat := 0
def EvenT._sizeOf_3 (u : Nat) : Nat := 0
def OddT._sizeOf_1 (u : Nat) : Nat := 0
def PP._sizeOf_1 (u : Nat) : Nat := 0
def PP._sizeOf_inst (u : Nat) : Nat := 0
def HasTag._sizeOf_1 (u : Nat) : Nat := 0
def HasTag._sizeOf_inst (u : Nat) : Nat := 0
def MB.below_1 (u : Nat) : Prop := True
def MB.brecOn_1 (u : Nat) : Prop := True
def MB.brecOn_1.go (u : Nat) : Prop := True

-- Non-recursive / single-ctor / `_flat_ctor` / `_sunfold` / `ofNat` / `ibelow`
def Color.below (u : Nat) : Prop := True
def Color.brecOn (u : Nat) : Prop := True
def Color.brecOn.go (u : Nat) : Prop := True
def UnitInd.ctorElim (u : Nat) : Prop := True
def UnitInd.ctorElimType (u : Nat) : Prop := True
def UnitInd.mk.elim (u : Nat) : Prop := True
def UnitInd.ofNat (u : Nat) : Prop := True
def Color.ofNat (u : Nat) : Color := .red
def Color.ofNat_ctorIdx (u : Nat) : Nat := 0
def ExprAst.ofNat (u v : Nat) : Nat := 0
def ExprAst.ofNat_ctorIdx (u : Nat) : Prop := True
def ExprAst.ibelow (u : Nat) : Prop := True
def ExprAst.binductionOn (u : Nat) : Prop := True
def Rose.ibelow (u : Nat) : Prop := True
def ExprAst.lit._flat_ctor (u : Nat) : Prop := True
def PP.z._flat_ctor (u : Nat) : Prop := True
def Wrap.mk._flat_ctor (u : Nat) : Wrap := Wrap.mk 0
def Wrap.toCtorIdx (u : Nat) : Nat := 0
def Color._sunfold (u : Nat) : Prop := True
def nonStructDef._sunfold (u : Nat) : Prop := True
def recThmForSunfold._sunfold (u : Nat) : Prop := True
def propProofForSunfold._sunfold (u : Nat) : Prop := True

-- Unbacked matcher / splitter / sparse / WF / structural / default spoofs
def T.userFoo.match_1 (u : Nat) : Prop := True
def T.userBar.proof_3 (u : Nat) : Prop := True
def T.fake.splitter (u : Nat) : Prop := True
private def priv.fake.splitter (u : Nat) : Prop := True
private def hid2.proof_1 (u : Nat) : Prop := True
private def hid3.match_7 (u : Nat) : Prop := True
private def UnitInd.below (u : Nat) : Prop := True
private def pubMatch.match_2 (u : Nat) : Prop := True
def _hidden (u : Nat) : Prop := True
def _sizeOf_1 (u : Nat) : Prop := True
def _sizeOf_inst (u : Nat) : Prop := True
def _flat_ctor (u : Nat) : Prop := True
def _sparseCasesOn_abc (u : Nat) : Prop := True
def _sparseCasesOn_01 (u : Nat) : Prop := True
private def Color._unary (u : Nat) : Prop := True
def Config._mutual (u : Nat) : Prop := True
def Color._f (u : Nat) : Prop := True
def PP._f (u : Nat) : Prop := True
def someThm._f (u : Nat) : Prop := True
def nonStructDef._f (u : Nat) : Prop := True

def structUnusedFixed (unused : Nat) (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + structUnusedFixed unused rest

def structUnusedOther (xs : List Nat) (unusedOther : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + structUnusedOther rest unusedOther

def structLetSpoof (xs : List Nat) : Nat :=
  match xs with
  | [] =>
    let unusedInLet := 0
    0
  | x :: rest => x + structLetSpoof rest

def structDiteUnused (xs : List Nat) (n : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest =>
    if h : x < n then x + structDiteUnused rest n
    else structDiteUnused rest n

def evenDepthSpoof : EvenT → Nat
  | .zero => (fun (f : Nat) => 0) 1
  | .succ (.succ e) => 1 + evenDepthSpoof e

set_option linter.defProp false in
noncomputable def propStructUnused (unused : Nat) : List Nat → Prop
  | [] => True
  | _ :: rest => propStructUnused unused rest

set_option linter.defProp false in
noncomputable def propProofStructUnused (unused : Nat) : List Nat → True
  | [] => trivial
  | _ :: rest => propProofStructUnused unused rest

set_option linter.defProp false in
noncomputable def propStructUnusedLet : List Nat → Prop
  | [] =>
    let badPropLet := 0
    True
  | _ :: rest => propStructUnusedLet rest

mutual
  def mutStructUnusedAllA (unused : Nat) : List Nat → Nat
    | [] => 0
    | x :: xs => x + mutStructUnusedAllB unused xs

  def mutStructUnusedAllB (unused : Nat) : List Nat → Nat
    | [] => 1
    | _ :: xs => mutStructUnusedAllA unused xs
end

mutual
  def mutLocalUnusedA (k : Nat) : List Nat → Nat
    | [] => k
    | x :: xs => x + mutLocalUnusedB k xs 0

  def mutLocalUnusedB (k : Nat) : List Nat → Nat → Nat
    | [], unusedVarying => 0
    | _ :: xs, _ => mutLocalUnusedA k xs
end

def Box.val._default (u : Nat) : Prop := True
def ZeroBox.val._default : Nat := @id (let unusedInIdTy := 0; Nat) 0
def Config.payload._default {unused : Nat} : Prop := @id Prop True
def Pair.snd._default {α : Type} : Prop := @id Prop True
structure NoDefChild (α : Type) extends Config α where
  limit := 20
def NoDefChild.payload._inherited_default {α : Type} : Prop := @id Prop True
def NoDefChild.limit._inherited_default {unused : Nat} : Prop := @id Prop True
structure NoDefChildExact (α : Type) extends Config α where
  limit := 20
def NoDefChildExact.limit._inherited_default {α : Type} : Nat := @id Nat 0
def Config.noSuch._default (u : Nat) : Prop := True
def Config.payload._autoParam (u : Nat) : Prop := True
def spoofPSigma : PSigma (fun (unusedSigma : Nat) => Nat) := PSigma.mk 0 0

def wfWithPSigmaSpoof (n : Nat) : Nat :=
  match n with
  | 0 => (@PSigma.mk Nat (fun (unused : Nat) => Nat) 0 0).1
  | k + 1 => wfWithPSigmaSpoof k
termination_by n
decreasing_by exact Nat.lt_add_one _

def wfFixSpoof (n : Nat) : Nat :=
  match n with
  | 0 =>
    @WellFounded.Nat.fix Nat (fun (unusedWf : Nat) => Nat) (fun x => x)
      (fun _ _ => 0) 0
  | k + 1 => wfFixSpoof k
termination_by n
decreasing_by exact Nat.lt_add_one _

-- Fake structure projection and diamond-coercion spoofs
def Box.fakeProj (u : Nat) (b : Box) : Nat := b.val
def Pair.fakeProj (u : Nat) (x : Pair Nat) : Nat := x.snd
def Pair.fakeProjDom (α : let unusedInDom := 0; Type) (self : Pair α) : Nat :=
  self.snd
def OneCtor.fakeProj1 (f : (unusedInDom : Nat) → Type) (b : OneCtor f) : Nat :=
  b.1
def PlainChild.toRight (self : PlainChild) : PlainBase := PlainBase.mk
def Diamond.fakeCoerce (self : Diamond) : Right := Right.mk Base.mk
def wfUnusedFixed (unused : Nat) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => wfUnusedFixed unused k
termination_by n
decreasing_by exact Nat.lt_add_one _

-- Alpha-equivalent / same-name `Ind.below` motive spoofs in structural defs
def structMotiveSpoof (xs : List Nat) : Nat :=
  let _ : List Nat → Type := fun (unused : List Nat) => Nat
  match xs with
  | [] => 0
  | x :: rest => x + structMotiveSpoof rest

def structSameNameMotiveSpoof (xs : List Nat) : Nat :=
  let _ : List Nat → Type := fun (xs : List Nat) => Nat
  match xs with
  | [] => 0
  | x :: rest => x + structSameNameMotiveSpoof rest

def structBelowArgMotiveSpoof (xs : List Nat) : Nat :=
  let _ : Type := @List.below Nat (fun (unusedBelowM : List Nat) => Nat) xs
  match xs with
  | [] => 0
  | x :: rest => x + structBelowArgMotiveSpoof rest

-- Cross-module `Model` parent wrong-type `_default` and unbacked `_inherited_default`
structure SpecChildFromModel (α : Type)
    extends Trusted.MirSemantics.ModelParentCfg α where
  limit := 20

def SpecChildFromModel.payload._default {α : Type} : Prop := @id Prop True
def SpecChildFromModel.payload._inherited_default {α : Type} : Prop :=
  @id Prop True

-- Named arrow field domain with injected unused let binder in `_default`
structure CallbackSpec where
  cb : (arg : Nat) → Bool

def CallbackSpec.cb._default : (let unusedLet := 0; (arg : Nat) → Bool) :=
  @id (let unusedLet := 0; (arg : Nat) → Bool) (fun _ => true)

-- Recursive `Prop` inductive unused bindings and manual `brecOn` spoof
set_option linter.defProp false in
def ppUnusedFixed (unused : Nat) : PP → True
  | .z => trivial
  | .s p => ppUnusedFixed unused p

set_option linter.defProp false in
def ppUnusedLet : PP → True
  | .z =>
    let badPPLet := 0
    trivial
  | .s p => ppUnusedLet p

set_option linter.defProp false in
def manualPPBrecSpoof (p : PP) : True :=
  @PP.brecOn (fun _ => True) p (fun t (unusedBelow : @PP.below (fun _ => True) t) => trivial)

-- Author-written `<thm>._f` spoofs paired with `brecOn` theorem / def callers
def spoofThmBrec._f (a : Nat) (f : @Nat.below (fun _ => True) a) : True :=
  (fun (spoofUnusedF : Nat) => trivial) 0

theorem spoofThmBrec (n : Nat) : True :=
  @Nat.brecOn (fun _ => True) n spoofThmBrec._f

set_option linter.defProp false in
noncomputable def spoofCallerBrec (n : Nat) : True :=
  @Nat.brecOn (fun _ => True) n spoofThmBrec._f

abbrev spoofAbbrevThmBrec._f (a : Nat) (f : @Nat.below (fun _ => True) a) : True :=
  (fun (spoofUnusedAbbrev : Nat) => trivial) 0

theorem spoofAbbrevThmBrec (n : Nat) : True :=
  @Nat.brecOn (fun _ => True) n spoofAbbrevThmBrec._f

abbrev evilPropThm._f (a : Nat) (f : @Nat.below (fun _ => True) a) : True :=
  (fun (spoofEvil : Nat) => trivial) 0

theorem evilPropThm : PP → True
  | .z => @Nat.brecOn (fun _ => True) 0 evilPropThm._f
  | .s p => evilPropThm p

-- Unbacked `.het`, 1-ctor enum `ofNat` without/with `ofNat_ctorIdx`, and `Prop` WF unused
def pubMatch.match_1.het (u : Nat) : Prop := True

inductive FakeOne where
  | only

abbrev FakeOne.ofNat : Nat → FakeOne := fun (n : Nat) => FakeOne.only

inductive FakeOneThm where
  | only

abbrev FakeOneThm.ofNat : Nat → FakeOneThm :=
  fun (n : Nat) =>
    let badInOfNat := 0
    FakeOneThm.only

theorem FakeOneThm.ofNat_ctorIdx : FakeOneThm.ofNat 0 = .only := rfl

set_option linter.defProp false in
def propWfUnusedFixed (unused : Nat) (a b : Nat) : True :=
  match b with
  | 0 =>
    have _ := a
    trivial
  | k + 1 => propWfUnusedFixed unused (a + 1) k
termination_by b
decreasing_by exact Nat.lt_add_one _

set_option linter.defProp false in
def propWfUnusedVarying (a b : Nat) : True :=
  match b with
  | 0 => trivial
  | k + 1 => propWfUnusedVarying 0 k
termination_by b
decreasing_by exact Nat.lt_add_one _

set_option linter.defProp false in
def propWfUnusedFixedInMeasure (u : Nat) (a b : Nat) : True :=
  match b with
  | 0 =>
    have _ := a
    trivial
  | k + 1 => propWfUnusedFixedInMeasure u (a + 1) k
termination_by u + b
decreasing_by exact Nat.add_lt_add_left (Nat.lt_add_one k) u
end Spoofs

def BareParam.casesOn (u : Nat) : Prop := True
def BareParam.noConfusion (u : Nat) : Prop := True
def BareParam.ctorElim (u : Nat) : Prop := True
def BareParam.below (u : Nat) : Prop := True
def BareParam.brecOn (u : Nat) : Prop := True
def BareParam.a.elim (u : Nat) : Prop := True
private def BareParam.ctorIdx (u : Nat) : Prop := True
def BareParam.noConfusionType (u : Nat) : Prop := True
def BareParam.ctorElimType (u : Nat) : Prop := True
def BareParam._sizeOf_inst (u : Nat) : Prop := True
def BareParam._sizeOf_1 (u : Nat) : Prop := True
private def pubSharedMatch.match_1 : Nat := 0
private def pubSharedMatch.match_1.splitter (unused : Nat) : Prop := True
def Spec._hiddenRoot (u : Nat) : Prop := True
def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p
"#,
    );
    let rep = f.run().unwrap();
    let expected: BTreeSet<String> = [
        "BareInd.casesOn",
        "BareInd.noConfusion",
        "BareInd.noConfusionType",
        "BareInd.ctorIdx",
        "BareInd.ctorElim",
        "BareInd.below",
        "BareInd.brecOn",
        "BareInd.a.elim",
        "BareInd.a.noConfusion",
        "BareInd._sizeOf_1",
        "BareInd._sizeOf_inst",
        "Spoofs.myPrivMatch.match_1.splitter",
        "Spoofs.PP.ctorElim",
        "Spoofs.PP.ctorElimType",
        "Spoofs.PP.noConfusion",
        "Spoofs.PP.noConfusionType",
        "Spoofs.PP.ctorIdx",
        "Spoofs.PP.ibelow",
        "Spoofs.PP.binductionOn",
        "Spoofs.PP.z.elim",
        "Spoofs.PP.z.noConfusion",
        "Spoofs.POr.ctorElim",
        "Spoofs.POr.inl.elim",
        "Spoofs.PP.below.below",
        "Spoofs.PP.below.ctorElim",
        "Spoofs.PP.below.recOn",
        "Spoofs.PP.below.noConfusion",
        "Spoofs.PrivPP.below.recOn",
        "Spoofs.FamP.noConfusion",
        "Spoofs.FamP.noConfusionType",
        "Spoofs.FamP.ctorIdx",
        "Spoofs.FamP.ctorElim",
        "Spoofs.FamP.zero.elim",
        "Spoofs.FamP._sizeOf_1",
        "Spoofs.Rose.below_01",
        "Spoofs.Rose.brecOn_01",
        "Spoofs.Rose.below_99",
        "Spoofs.Rose.brecOn_99",
        "Spoofs.Color._sizeOf_2",
        "Spoofs.Color._sizeOf_99",
        "Spoofs.Color._sizeOf_01",
        "Spoofs.EvenT._sizeOf_3",
        "Spoofs.OddT._sizeOf_1",
        "Spoofs.PP._sizeOf_1",
        "Spoofs.PP._sizeOf_inst",
        "Spoofs.HasTag._sizeOf_1",
        "Spoofs.HasTag._sizeOf_inst",
        "Spoofs.MB.below_1",
        "Spoofs.MB.brecOn_1",
        "Spoofs.MB.brecOn_1.go",
        "Spoofs.Color.below",
        "Spoofs.Color.brecOn",
        "Spoofs.Color.brecOn.go",
        "Spoofs.UnitInd.ctorElim",
        "Spoofs.UnitInd.ctorElimType",
        "Spoofs.UnitInd.mk.elim",
        "Spoofs.UnitInd.ofNat",
        "Spoofs.Color.ofNat",
        "Spoofs.Color.ofNat_ctorIdx",
        "Spoofs.ExprAst.ofNat",
        "Spoofs.ExprAst.ofNat_ctorIdx",
        "Spoofs.ExprAst.ibelow",
        "Spoofs.ExprAst.binductionOn",
        "Spoofs.Rose.ibelow",
        "Spoofs.ExprAst.lit._flat_ctor",
        "Spoofs.PP.z._flat_ctor",
        "Spoofs.Wrap.mk._flat_ctor",
        "Spoofs.Wrap.toCtorIdx",
        "Spoofs.Color._sunfold",
        "Spoofs.nonStructDef._sunfold",
        "Spoofs.recThmForSunfold._sunfold",
        "Spoofs.propProofForSunfold._sunfold",
        "Spoofs.T.userFoo.match_1",
        "Spoofs.T.userBar.proof_3",
        "Spoofs.T.fake.splitter",
        "Spoofs.priv.fake.splitter",
        "BareParam.casesOn",
        "BareParam.noConfusion",
        "BareParam.ctorElim",
        "BareParam.below",
        "BareParam.brecOn",
        "BareParam.a.elim",
        "BareParam.ctorIdx",
        "BareParam.noConfusionType",
        "BareParam.ctorElimType",
        "BareParam._sizeOf_inst",
        "BareParam._sizeOf_1",
        "pubSharedMatch.match_1.splitter",
        "Spoofs.hid2.proof_1",
        "Spoofs.hid3.match_7",
        "Spoofs.UnitInd.below",
        "Spoofs.pubMatch.match_2",
        "Spoofs._hidden",
        "Spoofs._sizeOf_1",
        "Spoofs._sizeOf_inst",
        "Spoofs._flat_ctor",
        "Spoofs._sparseCasesOn_abc",
        "Spoofs._sparseCasesOn_01",
        "Spoofs.Color._unary",
        "Spoofs.Config._mutual",
        "Spoofs.Color._f",
        "Spoofs.PP._f",
        "Spoofs.someThm._f",
        "Spoofs.nonStructDef._f",
        "Spoofs.structUnusedFixed",
        "Spoofs.structUnusedOther",
        "Spoofs.structLetSpoof",
        "Spoofs.structDiteUnused",
        "Spoofs.evenDepthSpoof",
        "Spoofs.propStructUnused",
        "Spoofs.propProofStructUnused",
        "Spoofs.propStructUnusedLet",
        "Spoofs.mutStructUnusedAllA",
        "Spoofs.mutStructUnusedAllB",
        "Spoofs.mutLocalUnusedB",
        "Spoofs.Box.val._default",
        "Spoofs.ZeroBox.val._default",
        "Spoofs.Config.payload._default",
        "Spoofs.Pair.snd._default",
        "Spoofs.NoDefChild.payload._inherited_default",
        "Spoofs.NoDefChild.limit._inherited_default",
        "Spoofs.NoDefChildExact.limit._inherited_default",
        "Spoofs.Config.noSuch._default",
        "Spoofs.Config.payload._autoParam",
        "Spoofs.spoofPSigma",
        "Spoofs.wfWithPSigmaSpoof",
        "Spoofs.wfFixSpoof",
        "Spoofs.Box.fakeProj",
        "Spoofs.Pair.fakeProj",
        "Spoofs.Pair.fakeProjDom",
        "Spoofs.OneCtor.fakeProj1",
        "Spoofs.PlainChild.toRight",
        "Spoofs.Diamond.fakeCoerce",
        "Spoofs.wfUnusedFixed",
        "Spoofs.structMotiveSpoof",
        "Spoofs.structSameNameMotiveSpoof",
        "Spoofs.structBelowArgMotiveSpoof",
        "Spoofs.SpecChildFromModel.payload._default",
        "Spoofs.SpecChildFromModel.payload._inherited_default",
        "Spoofs.CallbackSpec.cb._default",
        "Spoofs.ppUnusedFixed",
        "Spoofs.ppUnusedLet",
        "Spoofs.manualPPBrecSpoof",
        "Spoofs.spoofThmBrec._f",
        "Spoofs.spoofAbbrevThmBrec._f",
        "Spoofs.evilPropThm._f",
        "Spoofs.pubMatch.match_1.het",
        "Spoofs.FakeOne.ofNat",
        "Spoofs.FakeOneThm.ofNat",
        "Spoofs.propWfUnusedFixed",
        "Spoofs.propWfUnusedVarying",
        "Spoofs.propWfUnusedFixedInMeasure",
        "Spec._hiddenRoot",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let actual = unused_spec_binding_decls(&rep);
    assert_eq!(actual, expected, "specWarnings mismatch: {rep}");

    // Also verify `module` mode catches private and public spoofs while keeping
    // compiler-generated helpers clean.
    let mut f_mod_neg = Fixture::new(
        "module\nprelude\npublic import Expected\nimport Init.Data.BitVec.Lemmas\n\
         public theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f_mod_neg.set(
        "Model",
        TargetRole::Model,
        "module\nprelude\npublic import Init.Data.BitVec.Basic\n\
         @[expose] public section\n\
         namespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
         end Trusted.MirSemantics\nend\n",
    );
    f_mod_neg.set(
        "Captured",
        TargetRole::Capture,
        "module\nprelude\npublic import Model\n\
         @[expose] public section\n\
         def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n\
         end\n",
    );
    f_mod_neg.set(
        "Spec",
        TargetRole::Specification,
        r#"module
prelude
public import Model
public import Init.Data.List.Basic

@[expose] public section
namespace ModSpoof
inductive Rose where
  | node (children : List Rose)

inductive PP : Prop where
  | z
  | s (p : PP)

private def modPrivMatch (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | _ => 2

private def modPrivMatch.match_1.splitter (unused : Nat) : Prop := True

def Rose.below_01 (u : Nat) : Prop := True
def PP.ctorElim (u : Nat) : Prop := True
def _hiddenMod (u : Nat) : Prop := True
end ModSpoof

private def ModSpoof.hid.proof_1 (u : Nat) : Prop := True
def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p
end
"#,
    );
    f_mod_neg.set(
        "Expected",
        TargetRole::Expected,
        "module\nprelude\npublic import Captured\npublic import Spec\n\
         @[expose] public section\n\
         def Expected.claim : Prop :=\n  \
           Trusted.MirSemantics.UnitTheorem \
             (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n\
         end\n",
    );
    let rep_mod_neg = f_mod_neg.run().unwrap();
    let expected_mod: BTreeSet<String> = [
        "ModSpoof.modPrivMatch.match_1.splitter",
        "ModSpoof.Rose.below_01",
        "ModSpoof.PP.ctorElim",
        "ModSpoof._hiddenMod",
        "ModSpoof.hid.proof_1",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    assert_eq!(unused_spec_binding_decls(&rep_mod_neg), expected_mod, "{rep_mod_neg}");
}
