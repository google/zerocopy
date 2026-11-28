// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Multi-argument and `3+`-function mutual well-founded `ArgsPacker`
//! regressions plus forged cyclic/dangling `structureExt` `.olean` defense
//! regressions.

use super::*;

/// Verifies `inspectSpecVacuity` directly against `.olean` `loadExts := false`
/// across `ArgsPacker` `PSigma` / `PSum` lowering (including `3`-function
/// mutual WF and `>= 3`-varying-argument dependent WF) while still flagging
/// unused fixed/varying parameters, `termination_by`-only fixed parameters, and
/// inner `PSigma` / `PSum` / `WellFounded.fix` spoofs.
#[test]
fn gate_g4_audits_wf_argspacker_mutual3_and_dependent_psigma_spines() {
    let f = Fixture::new(SIMPLE_PROOF);
    let mut probe_checker = f.accepted_checker();
    let lean_prefix = probe_checker
        .admitted()
        .unwrap()
        .prefix
        .to_string_lossy()
        .replace('\\', "\\\\")
        .replace('"', "\\\"");
    let stage_dir = probe_checker.stage().to_path_buf();
    let wf_lean = stage_dir.join("WfSpec.lean");
    let wf_olean = stage_dir.join("WfSpec.olean");
    fs::write(
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
  | k + 1 =>
    if h2 : i ≠ n then
      walk n (i + 1) (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h h2)) k
    else i
termination_by fuel

def walkFixed (n : Nat) (hn : 0 < n) (i fuel : Nat) : Nat :=
  match fuel with
  | 0 => i
  | k + 1 =>
    walkFixed n hn ((⟨i % n, Nat.mod_lt _ hn⟩ : Fin n).val) k
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

def wfDep3 (a b c : Nat) : Fin (a + b + c + 1) :=
  match c with
  | 0 => ⟨0, Nat.zero_lt_succ _⟩
  | k + 1 =>
    let r := wfDep3 (a + 1) (b + 1) k
    ⟨r.val % (a + b + (k + 1) + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
termination_by c
decreasing_by exact Nat.lt_add_one _

def wfDep4 (a b c d : Nat) : Fin (a + b + c + d + 1) :=
  match d with
  | 0 => ⟨0, Nat.zero_lt_succ _⟩
  | k + 1 =>
    let r := wfDep4 (a + 1) (b + 1) (c + 1) k
    ⟨r.val % (a + b + c + (k + 1) + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
termination_by d
decreasing_by exact Nat.lt_add_one _

def wfDepVaryingParamTypes (a : Nat) (b : Fin (a + 1))
    (c : Fin (b.val + 1)) (d : Nat) : Fin (c.val + 1) :=
  match d with
  | 0 => ⟨0, Nat.zero_lt_succ _⟩
  | k + 1 =>
    let b' : Fin ((a + 1) + 1) := ⟨0, Nat.zero_lt_succ _⟩
    let c' : Fin (b'.val + 1) := ⟨0, Nat.zero_lt_succ _⟩
    let r := wfDepVaryingParamTypes (a + 1) b' c' k
    ⟨r.val % (c.val + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
termination_by d
decreasing_by exact Nat.lt_add_one _

def wfMeasureSubexpr (u : Nat) (n : Nat) : Nat → Nat :=
  match n with
  | 0 => fun x => u + x
  | k + 1 => wfMeasureSubexpr u k
termination_by u + n

mutual
  def wfMutDepA (a b c : Nat) : Fin (a + b + c + 1) :=
    match c with
    | 0 => ⟨0, Nat.zero_lt_succ _⟩
    | k + 1 =>
      let r := wfMutDepB (a + 1) (b + 1) k
      ⟨r.val % (a + b + (k + 1) + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
  termination_by c
  decreasing_by exact Nat.lt_add_one _

  def wfMutDepB (a b c : Nat) : Fin (a + b + c + 1) :=
    match c with
    | 0 => ⟨0, Nat.zero_lt_succ _⟩
    | k + 1 =>
      let r := wfMutDepA (a + 1) (b + 1) k
      ⟨r.val % (a + b + (k + 1) + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
  termination_by c
  decreasing_by exact Nat.lt_add_one _
end

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

mutual
  def wfTriA (x y : Nat) : Nat :=
    match x with
    | 0 => y
    | k + 1 => wfTriB k (y + 1)
  termination_by (x, 2)

  def wfTriB (x y : Nat) : Nat :=
    match x with
    | 0 => y
    | k + 1 => wfTriC k (y + 1)
  termination_by (x, 1)

  def wfTriC (x y : Nat) : Nat :=
    match x with
    | 0 => y
    | k + 1 => wfTriA k y
  termination_by (x, 0)
end

-- Negative WF cases that must still emit `unused_spec_binding`.
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

def wfDep3UnusedB (a b c : Nat) : Fin (a + 1) :=
  match c with
  | 0 => ⟨0, Nat.zero_lt_succ a⟩
  | k + 1 => wfDep3UnusedB a 0 k
termination_by c
decreasing_by exact Nat.lt_add_one _

def wfDep3UnusedFirst (a b c : Nat) : Fin (c + 1) :=
  match c with
  | 0 => ⟨b % 1, Nat.mod_lt b (Nat.zero_lt_succ 0)⟩
  | k + 1 =>
    let r := wfDep3UnusedFirst 0 (b + 1) k
    ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩
termination_by c
decreasing_by exact Nat.lt_add_one _

def wfDep3PSigmaSpoof (a b c : Nat) : Fin (a + b + c + 1) :=
  let _ := (@PSigma.mk Nat (fun (spoof : Nat) => Nat) 0 0).1
  match c with
  | 0 => ⟨0, Nat.zero_lt_succ _⟩
  | k + 1 =>
    let r := wfDep3PSigmaSpoof (a + 1) (b + 1) k
    ⟨r.val % (a + b + (k + 1) + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
termination_by c
decreasing_by exact Nat.lt_add_one _

def wfDep2AlphaSigmaMkSpoof (a b : Nat) : Fin (a + b + 1) :=
  let _ := (@PSigma.mk Nat (fun (spoof : Nat) => Nat) 0 0).1
  match b with
  | 0 => ⟨0, Nat.zero_lt_succ _⟩
  | k + 1 =>
    let r := wfDep2AlphaSigmaMkSpoof (a + 1) k
    ⟨r.val % (a + (k + 1) + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
termination_by b
decreasing_by exact Nat.lt_add_one _

def wfDep2SameNameSigmaMkSpoof (a b : Nat) : Fin (a + b + 1) :=
  let _ := (@PSigma.mk Nat (fun (a : Nat) => Nat) 0 0).1
  match b with
  | 0 => ⟨0, Nat.zero_lt_succ _⟩
  | k + 1 =>
    let r := wfDep2SameNameSigmaMkSpoof (a + 1) k
    ⟨r.val % (a + (k + 1) + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
termination_by b
decreasing_by exact Nat.lt_add_one _

mutual
  def wfTriUnusedA (x y : Nat) : Nat :=
    match x with
    | 0 => y
    | k + 1 => wfTriUnusedB k (y + 1)
  termination_by (x, 2)

  def wfTriUnusedB (x y : Nat) : Nat :=
    match x with
    | 0 => y
    | k + 1 => wfTriUnusedC 0 k (y + 1)
  termination_by (x, 1)

  def wfTriUnusedC (unusedTri x y : Nat) : Nat :=
    match x with
    | 0 => y
    | k + 1 => wfTriUnusedA k y
  termination_by (x, 0)
end

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
    let probe_src = format!(
        r#"import TrustedBoundary

namespace WfPSigmaProbe
def run : IO Unit := do
  let leanPrefix := System.FilePath.mk "{lean_prefix}"
  let sp := match (← IO.getEnv "LEAN_PATH") with
    | some p => System.SearchPath.parse p
    | none => []
  TrustedBoundary.initHermeticSearchPath leanPrefix sp
  let originEnv ← Lean.importModules #[{{ module := `WfSpec }}] {{}} (loadExts := false)
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
  let unusedWs := warnings.filter (·.code == "unused_spec_binding")
  let decls := unusedWs.map (·.declaration)
  unless decls == #[
      "WfSpec.mutUnusedB",
      "WfSpec.nonWfDiteUnused",
      "WfSpec.spoofPSigma",
      "WfSpec.wfDep2AlphaSigmaMkSpoof",
      "WfSpec.wfDep2SameNameSigmaMkSpoof",
      "WfSpec.wfDep3PSigmaSpoof",
      "WfSpec.wfDep3UnusedB",
      "WfSpec.wfDep3UnusedFirst",
      "WfSpec.wfExactClonePSigmaSpoof",
      "WfSpec.wfFixSpoof",
      "WfSpec.wfNestedPSigmaSpoof",
      "WfSpec.wfPSumCasesOnSpoof",
      "WfSpec.wfSameNamePSigmaSpoof",
      "WfSpec.wfSingleVarUnusedFixedInMeasure",
      "WfSpec.wfTrailingPSigmaMotiveSpoof",
      "WfSpec.wfTrailingPSigmaUnused",
      "WfSpec.wfTriUnusedC",
      "WfSpec.wfUnusedFixed",
      "WfSpec.wfUnusedFixedInLex",
      "WfSpec.wfUnusedFixedInMeasure",
      "WfSpec.wfUnusedLet",
      "WfSpec.wfUnusedParam",
      "WfSpec.wfWithPSigmaSpoof"
    ] do
    throw <| IO.userError s!"unexpected wf/PSigma unused_spec_binding warnings: {{decls.toList}}"
  let checkExactMsg (decl expectedBindings : String) : IO Unit := do
    let expectedMsg := s!"unused argument binding(s) in `{{decl}}`: {{expectedBindings}}"
    match unusedWs.find? (·.declaration == decl) with
    | some w =>
      unless w.message == expectedMsg do
        throw <| IO.userError s!"unexpected message for {{decl}}: {{w.message}}"
    | none =>
      throw <| IO.userError s!"missing warning for {{decl}}"
  checkExactMsg "WfSpec.wfDep3UnusedFirst" "a"
  checkExactMsg "WfSpec.wfDep3UnusedB" "b"
  checkExactMsg "WfSpec.wfDep3PSigmaSpoof" "spoof"
  checkExactMsg "WfSpec.wfDep2AlphaSigmaMkSpoof" "spoof"
  checkExactMsg "WfSpec.wfDep2SameNameSigmaMkSpoof" "a"

#eval run
end WfPSigmaProbe
"#
    );
    let probe_path = stage_dir.join("WfPSigmaProbe.lean");
    fs::write(&probe_path, probe_src).unwrap();
    let lean_path = std::env::join_paths([stage_dir.join("control"), stage_dir.clone()]).unwrap();
    probe_checker
        .process_with_path(
            "wf-psigma-probe",
            &[
                "-j1".into(),
                "-M4096".into(),
                probe_path.to_string_lossy().into_owned(),
            ],
            Some(lean_path.as_os_str()),
        )
        .unwrap();
}

/// Forged `.olean` `structureExt` and `WF.eqnInfoExt` entries containing mutual
/// `subobject?` cycles (`CycA` <-> `CycB`), self-cycles, dangling `subobject?`
/// targets (`Spec.DanglingMissingStruct`), and dangling/unreferenced WF heads
/// (`Spec.MissingWfHead`, `CycA.val`) alongside `._default`,
/// `._inherited_default`, `._unary`, replaced `._flat_ctor`, and wrong-type
/// `ctorIdx` spoofs must never panic, loop, or exempt unaudited definitions.
#[test]
fn target_audit_survives_forged_cyclic_and_dangling_structure_ext() {
    use anneal_audit::InspectorRequest;

    let mut f = Fixture::new(PROOF);
    f.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         structure CycA where\n  val : Nat := 1\n\
         structure CycB where\n  val : Nat := 2\n\
         inductive ForgedSingle where\n  | mk\n\
         def realWf (n : Nat) : Nat :=\n  \
           match n with\n  | 0 => 0\n  | k + 1 => realWf k\n\
         termination_by n\n\
         decreasing_by exact Nat.lt_add_one _\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let mut checker = f.accepted_checker();
    let spec_olean = checker.stage().join("lib/Spec.olean");
    let script = checker.stage().join("ForgeCyclicStructureExt.lean");
    run_lean_script(
        &mut checker,
        "forge-cyclic-structure-ext",
        &script,
        &format!(
            r#"import Lean
open Lean in
def main : IO Unit := do
  let p := System.FilePath.mk {:?}
  let (data, _) ← readModuleData p
  let cycAInfo : StructureInfo := {{
    structName := `CycA
    fieldNames := #[`toCycB, `toSelf, `toMissing]
    fieldInfo := #[
      {{ fieldName := `toCycB, projFn := `CycA.val, subobject? := some `CycB, binderInfo := .default }},
      {{ fieldName := `toSelf, projFn := `CycA.val, subobject? := some `CycA, binderInfo := .default }},
      {{ fieldName := `toMissing, projFn := `CycA.val, subobject? := some `Spec.DanglingMissingStruct, binderInfo := .default }}
    ]
    parentInfo := #[
      {{ structName := `CycB, subobject := true, projFn := `CycA.val }},
      {{ structName := `Spec.DanglingMissingStruct, subobject := true, projFn := `CycA.val }}
    ]
  }}
  let cycBInfo : StructureInfo := {{
    structName := `CycB
    fieldNames := #[`toCycA]
    fieldInfo := #[
      {{ fieldName := `toCycA, projFn := `CycB.val, subobject? := some `CycA, binderInfo := .default }}
    ]
    parentInfo := #[
      {{ structName := `CycA, subobject := true, projFn := `CycB.val }}
    ]
  }}
  let patchedEntries := data.entries.map fun (extName, objs) =>
    if extName == `Lean.structureExt then
      (extName, #[unsafe unsafeCast cycAInfo, unsafe unsafeCast cycBInfo])
    else if extName == `Lean.Elab.WF.eqnInfoExt then
      match objs.toList with
      | rawObj :: _ =>
        let (_, baseWf) : Name × Lean.Elab.WF.EqnInfo :=
          unsafe (@unsafeCast EnvExtensionEntry (Name × Lean.Elab.WF.EqnInfo) rawObj)
        let orphanWf : Name × Lean.Elab.WF.EqnInfo :=
          (`Spec.MissingWfHead,
            {{ baseWf with
              declName := `Spec.MissingWfHead
              declNames := #[`Spec.MissingWfHead]
              declNameNonRec := `Spec.forgedOrphanWf._unary }})
        let unrefWf : Name × Lean.Elab.WF.EqnInfo :=
          (`CycA.val,
            {{ baseWf with
              declName := `CycA.val
              declNames := #[`CycA.val]
              declNameNonRec := `Spec.forgedUnreferencedWf._unary }})
        let extra : Array EnvExtensionEntry :=
          #[unsafe (@unsafeCast _ EnvExtensionEntry orphanWf),
            unsafe (@unsafeCast _ EnvExtensionEntry unrefWf)]
        (extName, objs ++ extra)
      | [] => (extName, objs)
    else
      (extName, objs)
  let mkSpoof (nm domConst : Name) : ConstantInfo := .defnInfo {{
    name := nm
    levelParams := []
    type := .forallE `u (.const domConst []) (.sort .zero) .default
    value := .lam `u (.const domConst []) (.const `True []) .default
    hints := .abbrev
    safety := .safe
    all := [nm]
  }}
  let s1 := mkSpoof `CycA.ghost._default `Nat
  let s2 := mkSpoof `CycA.ghost._inherited_default `Nat
  let s3 := mkSpoof `Spec.forgedOrphanWf._unary `Nat
  let s4 := mkSpoof `Spec.forgedUnreferencedWf._unary `Nat
  let sFlat := mkSpoof `CycA.mk._flat_ctor `Nat
  let sCtorIdx := mkSpoof `ForgedSingle.ctorIdx `ForgedSingle
  let replacedConsts := data.constants.map fun ci =>
    if ci.name == sFlat.name then sFlat
    else if ci.name == sCtorIdx.name then sCtorIdx
    else ci
  saveModuleData p `Spec {{
    data with
    entries := patchedEntries
    constNames := data.constNames ++ #[s1.name, s2.name, s3.name, s4.name]
    constants := replacedConsts ++ #[s1, s2, s3, s4]
  }}
"#,
            spec_olean.to_string_lossy()
        ),
    );
    let rep = checker
        .inspect(InspectorRequest::TargetAudit { request: f.request.clone() })
        .unwrap();
    assert_eq!(rep["replay"], true, "{rep}");
    let expected: BTreeSet<String> = [
        "CycA.ghost._default",
        "CycA.ghost._inherited_default",
        "CycA.mk._flat_ctor",
        "ForgedSingle.ctorIdx",
        "Spec.forgedOrphanWf._unary",
        "Spec.forgedUnreferencedWf._unary",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    assert_eq!(unused_spec_binding_decls(&rep), expected, "{rep}");
}
