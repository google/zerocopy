// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Gate G4 specification-vacuity regressions (`isCompilerGeneratedSpecDef`).

use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

use anneal_audit::{
    Checker, Failure, Json, TargetAuditRequest, TargetBindings, TargetModule, TargetRole,
    sha256_bytes,
};
use anneal_testkit::{LeanAuditFixture, OleanCachePolicy};

struct Fixture {
    inner: LeanAuditFixture,
    root: PathBuf,
    request: TargetAuditRequest,
}

impl Fixture {
    fn new(proof: &str) -> Self {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let inner = LeanAuditFixture::with_cache_policy(
            &repo,
            "anneal-spec-g4-test-",
            None,
            true,
            OleanCachePolicy::Shared,
        )
        .unwrap();
        let root = inner.root().to_path_buf();
        let h = sha256_bytes(b"fixture compilation");
        let mut f = Self {
            inner,
            root,
            request: TargetAuditRequest {
                modules: vec![],
                theorem_module: "Proof".into(),
                theorem_name: "Proof.verify".into(),
                expected_module: "Expected".into(),
                expected_declaration: "Expected.claim".into(),
                canonical_root: "Trusted.MirSemantics.UnitTheorem".into(),
                subject_declaration: "Captured.program".into(),
                specification_declaration: "Spec.specs".into(),
                allow_sorry_in_proof: false,
                bindings: TargetBindings {
                    request_sha256: h.clone(),
                    capture_sha256: h.clone(),
                    model_manifest_sha256: h.clone(),
                    specification_manifest_sha256: h,
                },
            },
        };
        f.set(
            "Model",
            TargetRole::Model,
            "prelude\nimport Init.Data.BitVec.Basic\n\
             namespace Trusted.MirSemantics\n\
             structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
             def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n",
        );
        f.set(
            "Captured",
            TargetRole::Capture,
            "prelude\nimport Model\ndef Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
        );
        f.set(
            "Spec",
            TargetRole::Specification,
            "prelude\nimport Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        );
        f.set(
            "Expected",
            TargetRole::Expected,
            "prelude\nimport Captured\nimport Spec\n\
             def Expected.claim : Prop :=\n  \
               Trusted.MirSemantics.UnitTheorem\n    \
                 (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
        );
        f.set("Proof", TargetRole::Proof, proof);
        f
    }

    fn set(&mut self, name: &str, role: TargetRole, source: &str) {
        let (path, expected_sha256) = self.inner.write_input_lean(name, source).unwrap();
        self.request.modules.retain(|m| m.module != name);
        self.request.modules.push(TargetModule {
            module: name.into(),
            source: path,
            expected_sha256,
            role,
        });
    }

    fn checker(&self) -> Checker {
        let env = self.inner.checker_env().unwrap();
        Checker::new_with_env(&self.root, None, env).unwrap()
    }

    fn cargo_checker(&self) -> cargo_anneal::Checker {
        let env = self.inner.checker_env().unwrap();
        cargo_anneal::Checker::new_with_env(&self.root, None, env).unwrap()
    }

    fn run(&self) -> Result<Json, Failure> {
        self.checker().run_target(&self.request)
    }
}

const PROOF: &str = "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
                     theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n";

fn unused_spec_binding_decls(report: &Json) -> BTreeSet<String> {
    report["specWarnings"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|w| w["code"] == "unused_spec_binding")
        .map(|w| w["declaration"].as_str().unwrap().to_owned())
        .collect()
}

/// Compiler-generated inductive, structure, matcher, deriving, and `Prop`
/// recursor definitions must emit zero `unused_spec_binding` false positives
/// in both non-`module` and `module` modes despite `loadExts := false`.
#[test]
fn gate_g4_suppresses_compiler_generated_spec_defs_without_false_positives() {
    let proof_conj = "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
                      theorem Proof.verify : Expected.claim :=\n  \
                        ⟨rfl, BitVec.and_self, rfl, Or.inl rfl⟩\n";
    let mut f_prelude = Fixture::new(proof_conj);
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

def tailOther (xs : List Nat) (acc : Nat) : Nat :=
  match xs with
  | [] => acc
  | x :: rest => tailOther rest (acc + x)

set_option linter.defProp false in
def weirdProp : Nat → True
  | 0 => trivial
  | n + 1 => weirdProp n

mutual
  def mutStructA : List Nat → Nat
    | [] => 0
    | x :: xs => x + mutStructB xs

  def mutStructB : List Nat → Nat
    | [] => 1
    | _ :: xs => mutStructA xs
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
end SpecRich

def Spec.specs (p : BitVec 8) : Prop :=
  BitVec.and p p = p ∧ SpecRich.testMatch .red = 0 ∧
    (BareInd.a = BareInd.a ∨ True)
"#,
    );
    let rep_prelude = f_prelude.run().unwrap();
    assert_eq!(rep_prelude["replay"], true);
    assert_eq!(rep_prelude["specWarnings"], serde_json::json!([]));

    // Unpinned `Init` + `deriving` in non-`module` and `module` modes.
    let rich_body = r#"namespace SpecDerive
inductive Color where
  | red
  | green
  | blue
  deriving BEq, DecidableEq, Repr, Inhabited, Ord, Hashable

structure Pair (α : Type) where
  fst : α
  snd : Nat
  deriving BEq, DecidableEq, Repr, Inhabited, Ord, Hashable

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

def tailOther (xs : List Nat) (acc : Nat) : Nat :=
  match xs with
  | [] => acc
  | x :: rest => tailOther rest (acc + x)

set_option linter.defProp false in
def weirdProp : Nat → True
  | 0 => trivial
  | n + 1 => weirdProp n

mutual
  def mutStructA : List Nat → Nat
    | [] => 0
    | x :: xs => x + mutStructB xs

  def mutStructB : List Nat → Nat
    | [] => 1
    | _ :: xs => mutStructA xs
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

inductive Rose.ibelow where
  | x
  | y

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
end SpecDerive

def Spec.specs (p : BitVec 8) : Prop :=
  BitVec.and p p = p ∧ SpecDerive.sparseNat 0 = 10
"#;
    let mut f_init = Fixture::new(
        "import Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim := ⟨rfl, BitVec.and_self, rfl⟩\n",
    );
    f_init.set("Spec", TargetRole::Specification, &format!("import Model\n{rich_body}"));
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
        &format!("module\npublic import Model\n@[expose] public section\n{rich_body}\nend\n"),
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

    // Verify `TrustedBoundary.inspectSpecVacuity` directly against `.olean`
    // `loadExts := false` on multi-argument well-founded definitions whose
    // `ArgsPacker` lowers `termination_by (a, b)` to `PSigma` / `PSigma.mk`
    // (covering both single `wfLex` and mutual `wfMutA`/`wfMutB`), while still
    // flagging `wfUnusedFixed` and `PSigma` binder spoofs outside `WF`.
    let mut probe_checker = f_prelude.checker();
    let (inspector, lean_prefix) = {
        let adm = probe_checker.tool_admission().unwrap();
        (
            adm.inspector.clone(),
            adm.prefix.to_string_lossy().replace('\\', "\\\\").replace('"', "\\\""),
        )
    };
    let stage_dir = probe_checker.stage().to_path_buf();
    let wf_lean = stage_dir.join("WfSpec.lean");
    let wf_olean = stage_dir.join("WfSpec.olean");
    std::fs::write(
        &wf_lean,
        r#"namespace WfSpec
def wfSwap (a b : Nat) : Nat :=
  match b with
  | 0 => a
  | k + 1 => wfSwap (a + 1) k
termination_by b
decreasing_by exact Nat.lt_add_one _

def wfDepUsed (n : Nat) (h : n = n) (m : Nat) : Nat :=
  match m with
  | 0 => @Eq.rec Nat n (fun _ _ => Nat) n n h
  | k + 1 => wfDepUsed 0 rfl k
termination_by m
decreasing_by exact Nat.lt_add_one _

def walk (n : Nat) (i : Nat) (h : i ≤ n) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => i
  | k + 1 => if h2 : i ≠ n then walk n (i + 1) (by omega) k else i
termination_by fuel

def walkFixed (n : Nat) (hn : 0 < n) (i fuel : Nat) : Nat :=
  match fuel with
  | 0 => i
  | k + 1 =>
    walkFixed n hn ((⟨i % n, Nat.mod_lt _ (by omega)⟩ : Fin n).val) k
termination_by fuel

def countUp (n i : Nat) : Nat :=
  if h : i < n then countUp n (i + 1) + 1 else 0
termination_by n - i

def nonWfDiteUsed (n i : Nat) : Nat :=
  if h : i < n then (have _ := h; i + 1) else 0

def wfTrailingPSigmaUsed (x : Nat) (p : (_a : Nat) ×' Nat) : Nat :=
  match x with
  | 0 => p.1 + p.2
  | k + 1 => wfTrailingPSigmaUsed k p
termination_by x
decreasing_by exact Nat.lt_add_one _

def wfLex (u v : Nat) (a b : Nat) : Nat :=
  match a, b with
  | 0, _ => u + v
  | a + 1, 0 => wfLex u v a 1
  | a + 1, b + 1 => wfLex u v (a + 1) b
termination_by (a, b)

mutual
  def wfMutA (x y : Nat) : Nat :=
    match x, y with
    | 0, _ => 0
    | x + 1, 0 => wfMutB x 1
    | x + 1, y + 1 => wfMutA (x + 1) y
  termination_by (x, y)

  def wfMutB (x y : Nat) : Nat :=
    match x, y with
    | 0, _ => 0
    | x + 1, y => wfMutA x y
  termination_by (x, y)
end

def wfUnusedFixed (unused : Nat) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => wfUnusedFixed unused k
termination_by n
decreasing_by exact Nat.lt_add_one _

def wfUnusedFixedInMeasure (u v : Nat) (a b : Nat) : Nat :=
  match b with
  | 0 => v + a
  | k + 1 => wfUnusedFixedInMeasure u v (a + 1) k
termination_by u + b
decreasing_by exact Nat.add_lt_add_left (Nat.lt_add_one k) u

def wfUnusedFixedInLex (u v : Nat) (a b : Nat) : Nat :=
  match a, b with
  | 0, _ => v
  | a + 1, 0 => wfUnusedFixedInLex u v a 1
  | a + 1, b + 1 => wfUnusedFixedInLex u v (a + 1) b
termination_by (u + a, b)

def wfUnusedParam (u b : Nat) : Nat :=
  match b with
  | 0 => 0
  | k + 1 => wfUnusedParam 0 k
termination_by b
decreasing_by exact Nat.lt_add_one _

def wfUnusedLet (a b : Nat) : Nat :=
  let badLet := 0
  match b with
  | 0 => a
  | k + 1 => wfUnusedLet (a + 1) k
termination_by b
decreasing_by exact Nat.lt_add_one _

def wfNestedPSigmaSpoof (a b : Nat) : Nat :=
  let _ : Type := @PSigma Nat (fun (spoof : Nat) => Nat)
  match b with
  | 0 => a
  | k + 1 => wfNestedPSigmaSpoof (a + 1) k
termination_by b
decreasing_by exact Nat.lt_add_one _

def wfSameNamePSigmaSpoof (a b : Nat) : Nat :=
  let _ : Type := @PSigma Nat (fun (a : Nat) => Bool)
  match b with
  | 0 => a
  | k + 1 => wfSameNamePSigmaSpoof (a + 1) k
termination_by b
decreasing_by exact Nat.lt_add_one _

def wfExactClonePSigmaSpoof (a b : Nat) : Nat :=
  let _ := (@PSigma.mk Nat (fun (a : Nat) => Nat) 0 0).1
  match b with
  | 0 => a
  | k + 1 => wfExactClonePSigmaSpoof (a + 1) k
termination_by b
decreasing_by exact Nat.lt_add_one _

def wfPSumCasesOnSpoof (a b : Nat) : Nat :=
  let _ :=
    @PSum.casesOn Nat Nat (fun (unusedM : PSum Nat Nat) => Nat) (.inl 0)
      (fun x => x) (fun y => y)
  match b with
  | 0 => a
  | k + 1 => wfPSumCasesOnSpoof (a + 1) k
termination_by b
decreasing_by exact Nat.lt_add_one _

mutual
  def mutUnusedA (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | k + 1 => mutUnusedB 0 k
  termination_by n
  decreasing_by exact Nat.lt_add_one _

  def mutUnusedB (u n : Nat) : Nat :=
    let badMutLet := 0
    match n with
    | 0 => 0
    | k + 1 => mutUnusedA k
  termination_by n
  decreasing_by exact Nat.lt_add_one _
end

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

def nonWfDiteUnused (n i : Nat) : Nat :=
  if h : i < n then i + 1 else 0

def wfSingleVarUnusedFixedInMeasure (u : Nat) (x : Nat) : Nat :=
  match x with
  | 0 => 0
  | k + 1 => wfSingleVarUnusedFixedInMeasure u k + 1
termination_by x + u

def wfTrailingPSigmaUnused (x : Nat) (p : (_a : Nat) ×' Nat) : Nat :=
  match x with
  | 0 => 0
  | k + 1 => wfTrailingPSigmaUnused k ⟨0, 0⟩ + 1
termination_by x
decreasing_by exact Nat.lt_add_one _

def wfTrailingPSigmaMotiveSpoof (x : Nat) (p : (_a : Nat) ×' Nat) : Nat :=
  match x with
  | 0 =>
    @PSigma.casesOn Nat (fun _ => Nat)
      (fun (spoofM : (_a : Nat) ×' Nat) => Nat) p (fun a b => a + b)
  | k + 1 => wfTrailingPSigmaMotiveSpoof k p
termination_by x
decreasing_by exact Nat.lt_add_one _

def specs : Prop := True
end WfSpec
"#,
    )
    .unwrap();
    probe_checker
        .process(
            "compile-wf-spec",
            &[
                "-o".into(),
                wf_olean.to_string_lossy().into_owned(),
                wf_lean.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let mut probe_src = std::fs::read_to_string(inspector).unwrap();
    probe_src.push_str(&format!(
        "\n#eval show IO Unit from do\n  let leanPrefix := System.FilePath.mk \"{lean_prefix}\"\n"
    ));
    probe_src.push_str(
        r#"  let sp := match (← IO.getEnv "LEAN_PATH") with
    | some p => System.SearchPath.parse p
    | none => []
  TrustedBoundary.initHermeticSearchPath leanPrefix sp
  let originEnv ← Lean.importModules #[{ module := `WfSpec }] {} (loadExts := false)
  let checkedEnv := Lean.Environment.ofKernelEnv originEnv.toKernelEnv
  let allMatchers := TrustedBoundary.collectAllMatchers originEnv
  let wfModIdx? := originEnv.getModuleIdxFor? `WfSpec.specs
  let wfConsts : List Lean.Name := match wfModIdx? with
    | some idx =>
      (originEnv.header.moduleData[idx.toNat]?.map (fun d =>
        d.constNames.toList.filter fun n =>
          (Lean.Compiler.isUnsafeRecName? n).isNone)).getD []
    | none => []
  let warnings ← TrustedBoundary.inspectSpecVacuity checkedEnv originEnv allMatchers
    `WfSpec.specs `WfSpec.specs wfConsts
  let decls := (warnings.filter (·.code == "unused_spec_binding")).map (·.declaration)
  unless decls == #[
      "WfSpec.mutUnusedB",
      "WfSpec.nonWfDiteUnused",
      "WfSpec.spoofPSigma",
      "WfSpec.wfExactClonePSigmaSpoof",
      "WfSpec.wfFixSpoof",
      "WfSpec.wfNestedPSigmaSpoof",
      "WfSpec.wfPSumCasesOnSpoof",
      "WfSpec.wfSameNamePSigmaSpoof",
      "WfSpec.wfSingleVarUnusedFixedInMeasure",
      "WfSpec.wfTrailingPSigmaMotiveSpoof",
      "WfSpec.wfTrailingPSigmaUnused",
      "WfSpec.wfUnusedFixed",
      "WfSpec.wfUnusedFixedInLex",
      "WfSpec.wfUnusedFixedInMeasure",
      "WfSpec.wfUnusedLet",
      "WfSpec.wfUnusedParam",
      "WfSpec.wfWithPSigmaSpoof"
    ] do
    throw <| IO.userError s!"unexpected wf/PSigma unused_spec_binding warnings: {decls.toList}"
"#,
    );
    let probe_path = stage_dir.join("WfPSigmaProbe.lean");
    std::fs::write(&probe_path, probe_src).unwrap();
    probe_checker
        .process_with_path(
            "wf-psigma-probe",
            &[probe_path.to_string_lossy().into_owned()],
            Some(stage_dir.as_os_str()),
        )
        .unwrap();
}

/// Adversarial definitions mimicking compiler-generated names, private
/// internal details, zero-padded nested suffixes, `Prop` recursor suffixes,
/// `toCtorIdx`, `ofNat` `Prop` spoofs, and fake projections must all trigger
/// `unused_spec_binding`.
#[test]
fn gate_g4_catches_adversarial_compiler_suffix_and_private_spoofs() {
    let mut f = Fixture::new(PROOF);
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

-- Non-recursive / single-ctor / `_flat_ctor` / `ofNat` / `ibelow` /
-- `binductionOn` spoofs
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

-- Unbacked matcher / splitter / sparse / WF / structure-default / privacy
-- spoofs
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

-- Fake structure projection spoofs (non-structure, unused domain, wrong depth)
def Box.fakeProj (u : Nat) (b : Box) : Nat := b.val
def Pair.fakeProj (u : Nat) (x : Pair Nat) : Nat := x.snd
def Pair.fakeProjDom (α : let unusedInDom := 0; Type) (self : Pair α) : Nat :=
  self.snd
def OneCtor.fakeProj1 (f : (unusedInDom : Nat) → Type) (b : OneCtor f) : Nat :=
  b.1
def wfUnusedFixed (unused : Nat) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => wfUnusedFixed unused k
termination_by n
decreasing_by exact Nat.lt_add_one _
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
        "Spoofs.structUnusedFixed",
        "Spoofs.structUnusedOther",
        "Spoofs.structLetSpoof",
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
        "Spoofs.wfUnusedFixed",
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
