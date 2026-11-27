// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Library inventory reconciliation, discarded proof bodies, and kernel
//! result channels.

use super::*;

/// Exercise the inspector's final gate with serialized library artifacts.
/// The fixture deliberately bypasses hash admission after a successful public
/// run; it establishes inventory policy, not a public-input false-claim
/// exploit.
fn target_library_inventory_case(module: &str, mode: &str, rejection: Option<&str>) {
    use std::collections::BTreeMap;

    use anneal_audit::{ImportEdge, InspectorRequest, ModuleArtifacts, PARTS};
    use serde_json::json;

    let f = Fixture::new(PROOF);
    let mut checker = f.checker();
    checker.run_target(&f.request).unwrap();
    let adm = checker.admitted().unwrap();
    let foundation: Vec<_> = adm
        .foundation_modules()
        .into_iter()
        .map(str::to_string)
        .collect();
    let artifacts: Vec<_> = adm
        .artifacts
        .iter()
        .map(|(n, a)| json!([n, a.to_wire()]))
        .collect();
    let proof_output = adm.artifacts["Proof"].to_wire()[0][0].clone();
    let input = checker.stage().join("library-inventory-input.json");
    fs::write(
        &input,
        serde_json::to_vec(&json!({
            "sysroot": adm.prefix, "foundation": foundation, "artifacts": artifacts,
        }))
        .unwrap(),
    )
    .unwrap();
    let output = checker.stage().join("lib").join(format!("{module}.olean"));
    let producer = checker.stage().join("ForgeTargetLibrary.lean");
    fs::write(&producer, r#"
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let [input, output, proofOutput, moduleText, mode] := args
    | throw <| IO.userError "expected fixture paths and mode"
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile input)
  let sysroot ← IO.ofExcept <| j.getObjValAs? String "sysroot"
  initSearchPath sysroot
  let names ← IO.ofExcept <| j.getObjValAs? (Array String) "foundation"
  let roots := names.map fun n => { module := n.toName : Import }
  let entries ← IO.ofExcept <| j.getObjValAs?
    (Array (String × Array (Array String))) "artifacts"
  let arts := entries.foldl (init := ({} : NameMap ImportArtifacts)) fun acc (n, parts) =>
    acc.insert n.toName (.ofArrays (parts.map (·.map System.FilePath.mk)))
  let privateEnv ← importModules (roots.push {module := `Proof}) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
  let some (.thmInfo original) := privateEnv.checked.get.find? `List.drop.eq_def
    | throw <| IO.userError "missing genuine pinned theorem"
  let some (.thmInfo root) := privateEnv.checked.get.find? `Proof.verify
    | throw <| IO.userError "missing genuine target theorem"
  let module := moduleText.toName
  let publicEnv ← importModules roots {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .exported) (arts := arts)
  let publicEnv := publicEnv.setMainModule module |>.setExporting false
  if mode == "missing" || mode == "foundation-extra" then
    -- A new name gets its origin from the earlier IR-only module while its
    -- valid kernel declaration comes from a later module. Existing foundation
    -- names instead keep their prior origin and are an accepted control.
    let extraName := if mode == "missing" then `TargetInventoryWitness.logical else
      `List.drop.eq_def
    if publicEnv.header.isModule then
      let levels : Array OLeanLevel := #[.exported, .server, .private]
      let parts ← levels.mapM fun level => do
        let data ← mkModuleData publicEnv level
        let data := if level == .private then
          { data with extraConstNames := #[extraName] } else data
        pure (level.adjustFileName output, data)
      saveModuleDataParts module parts
    else
      let data ← mkModuleData publicEnv
      saveModuleData output module { data with extraConstNames := #[extraName] }
    if mode == "missing" then
      let provider := publicEnv.setMainModule `ZZZZInventoryProvider
      let declaration := Declaration.thmDecl {name := extraName, levelParams := [], type := mkConst `True, value := mkConst `True.intro}
      let provider ← match provider.addDeclCore 0 0 declaration none true with
        | .ok next => pure next
        | .error _ => throw <| IO.userError "valid inventory provider was rejected"
      writeModule provider ((System.FilePath.mk output).parent.get! / "ZZZZInventoryProvider.olean") false
  else
    let helper := if mode == "source-edge" then `Proof.verify else
      Name.str module "onlyAlternate"
    let helperType := if mode == "source-edge" then root.type else
      if mode == "extra-axiom" then mkConst `False else mkConst `True
    let helperDecl := if mode == "extra-axiom" then
      Declaration.axiomDecl {name := helper, levelParams := [], type := helperType, isUnsafe := false}
    else
      Declaration.thmDecl {name := helper, levelParams := [], type := helperType, value := mkConst `True.intro}
    let publicEnv ← if mode == "source-edge" then pure publicEnv else
      match publicEnv.addDeclCore 0 0 helperDecl none false with
      | .ok next => pure next
      | .error _ => throw <| IO.userError "could not add alternate-only helper"
    let metadataOnly := mode == "metadata-all" || mode == "metadata-levels"
    let value := if metadataOnly then original.value else
      if mode == "bad" then mkConst `True.intro else
        Expr.letE `_alternate helperType (mkConst helper) original.value false
    let all := if mode == "metadata-all" then original.all ++ [helper] else original.all
    let levelParams := if mode == "metadata-levels" then
      original.levelParams ++ [`metadataUnused] else original.levelParams
    let declaration := Declaration.thmDecl { original with value, all, levelParams }
    let publicEnv ← match publicEnv.addDeclCore 0 0 declaration none false with
      | .ok next => pure next
      | .error _ => throw <| IO.userError "could not add library inventory theorem"
    writeModule publicEnv output false
  -- Retain a genuine logical reference in the stored target proof. The body
  -- stays valid, but a mere unused import cannot make this regression pass.
  let levels := if mode == "missing" then [] else
    original.levelParams.map fun _ => Level.zero
  let referenceName := if mode == "missing" then `TargetInventoryWitness.logical else original.name
  let referenceType := if mode == "missing" then mkConst `True else
    original.type.instantiateLevelParams original.levelParams levels
  let proof := Expr.letE `_pinned referenceType (mkConst referenceName levels) root.value false
  let proofEnv ← importModules #[{module := `Expected}, {module := `Init.Data.BitVec.Lemmas}] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
  let proofEnv := proofEnv.setMainModule `Proof |>.setExporting false
  let proofEnv ← match proofEnv.addDeclCore 0 0 (.thmDecl {root with value := proof}) none false with
    | .ok next => pure next
    | .error _ => throw <| IO.userError "could not retain the logical library reference"
  writeModule proofEnv proofOutput false
"#).unwrap();
    checker
        .process(
            "library-inventory-fixture",
            &[
                "--run".into(),
                producer.to_string_lossy().into_owned(),
                input.to_string_lossy().into_owned(),
                output.to_string_lossy().into_owned(),
                proof_output,
                module.into(),
                mode.into(),
            ],
        )
        .unwrap();
    let libraries = if mode == "missing" {
        vec![module, "ZZZZInventoryProvider"]
    } else {
        vec![module]
    };
    for library in libraries {
        let mut available = BTreeMap::new();
        for part in PARTS {
            let path = output.parent().unwrap().join(format!("{library}.{part}"));
            if path.exists() {
                available.insert(part, path.to_string_lossy().into_owned());
            }
        }
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.insert(
            library.into(),
            ModuleArtifacts::from_available(&available, "fixture", || {
                "missing forged library artifact".into()
            })
            .unwrap(),
        );
        adm.library_modules.insert(library.into());
        adm.graph.insert(
            library.into(),
            foundation
                .iter()
                .cloned()
                .map(|module| ImportEdge {
                    module,
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                })
                .collect(),
        );
    }
    let result = checker.inspect(InspectorRequest::TargetAudit {
        request: f.request.clone(),
    });
    // Optional evidence retention lets another inspector replay the exact
    // serialized input. Ordinary tests retain nothing; requested fixtures stay
    // in the caller's temporary area until that caller removes them.
    if let Some(directory) = std::env::var_os("ANNEAL_AUDIT_RETAIN_FIXTURES") {
        let directory = PathBuf::from(directory);
        fs::create_dir_all(&directory).unwrap();
        fs::write(
            directory.join(format!("{module}-{mode}.json")),
            serde_json::to_vec_pretty(&json!({
                "stage": checker.stage(), "fixture": f.root,
                "result": result.as_ref().ok(),
                "failure": result.as_ref().err().map(ToString::to_string),
            }))
            .unwrap(),
        )
        .unwrap();
        std::mem::forget(checker);
        std::mem::forget(f);
    }
    match rejection {
        Some(message) => {
            let failure = result.unwrap_err();
            // Metadata-only conflicts fail in the pinned importer; bad proof
            // values fail in kernel checking. Both exception paths remain
            // operational, while explicit axiom/source-edge policy stays 1.
            let expected_code = if mode.starts_with("metadata-") || mode == "bad" {
                2
            } else {
                1
            };
            assert_eq!(failure.code, expected_code, "{failure}");
            assert!(failure.message.contains(message), "{failure}");
        }
        None => {
            let report = result.unwrap();
            assert_eq!(report["exactType"], true);
            if mode != "foundation-extra" {
                assert!(report["checkedAlternateProofs"].as_u64().unwrap() >= 2);
            }
        }
    }
}

#[test]
fn rejects_reached_library_name_missing_from_inventory() {
    target_library_inventory_case(
        "AAAAMissingInventory",
        "missing",
        Some("uninventoried target library dependency TargetInventoryWitness.logical"),
    );
}

#[test]
fn rejects_discarded_and_selected_library_proof_bodies() {
    for module in ["AAAAAlternate", "ZZZZAlternate"] {
        target_library_inventory_case(
            module,
            "bad",
            Some("alternate pinned theorem proof check List.drop.eq_def"),
        );
    }
}

#[test]
fn checks_alternate_only_dependencies_and_accepts_valid_proofs() {
    target_library_inventory_case("AAAAAlternate", "extra-axiom", Some("unapproved axiom"));
    target_library_inventory_case(
        "AAAAAlternate",
        "source-edge",
        Some("installed library List.drop.eq_def references target source Proof.verify"),
    );
    target_library_inventory_case("AAAAAlternate", "valid", None);
}

/// An IR-only reexport cannot replace the earlier foundation origin. Rejecting
/// this control would mistake harmless metadata for a missing library body.
#[test]
fn accepts_ir_extra_name_for_existing_foundation_declaration() {
    target_library_inventory_case("ZZZZFoundationExtra", "foundation-extra", None);
}

/// The importer rejects conflicting duplicate metadata before inventory policy
/// runs. Probe the actual staged helper directly so that prerequisite cannot
/// mask an early-return regression. Appending a unit probe leaves the inspected
/// implementation intact and adds no inspector mode or production API.
#[test]
fn reconciles_equal_theorem_bodies_before_discarding_inventory_metadata() {
    let fixture = Fixture::new(PROOF);
    let mut checker = fixture.checker();
    let inspector = checker.tool_admission().unwrap().inspector.clone();
    let mut source = fs::read_to_string(inspector).unwrap();
    source.push_str(
        r#"

#eval do
  let original : Lean.TheoremVal := {
    name := `MetadataWitness, levelParams := [], type := Lean.mkConst `True,
    value := Lean.mkConst `True.intro, all := [`MetadataWitness] }
  let stored := Lean.ConstantInfo.thmInfo original
  let unchanged ← TrustedBoundary.inventoryAlternates stored stored
  unless unchanged.isEmpty do throw <| IO.userError "identical theorem produced alternates"
  let changedProof := Lean.Expr.letE `h original.type original.value (.bvar 0) false
  let alternate := Lean.ConstantInfo.thmInfo { original with value := changedProof }
  let proofs ← TrustedBoundary.inventoryAlternates stored alternate
  unless proofs.size == 2 && proofs[0]!.value? true == stored.value? true &&
      proofs[1]!.value? true == alternate.value? true do
    throw <| IO.userError "different pinned proofs were not both retained"
  let deps ← TrustedBoundary.declarationEdges (.thmInfo {
    original with all := original.all ++ [`UnapprovedMetadataDependency] })
  unless deps.contains `UnapprovedMetadataDependency do
    throw <| IO.userError "metadata witness does not add a dependency edge"
  let mut accepted : Array String := #[]
  for (label, changed) in #[
      ("all", { original with all := original.all ++ [`UnapprovedMetadataDependency] }),
      ("levelParams", { original with levelParams := [`u] })] do
    let ci := Lean.ConstantInfo.thmInfo changed
    unless stored.type == ci.type && stored.value? true == ci.value? true do
      throw <| IO.userError "metadata fixture also changed the theorem expression"
    for (a, b) in #[(stored, ci), (ci, stored)] do
      let rejected ← try
        let _ ← TrustedBoundary.inventoryAlternates a b
        pure false
      catch error =>
        unless error.toString.startsWith "policy:inconsistent theorem metadata" do
          throw error
        pure true
      unless rejected do accepted := accepted.push label
  unless accepted.isEmpty do
    throw <| IO.userError s!"equal-body metadata was accepted: {accepted}"
"#,
    );
    let probe = checker.stage().join("TheoremMetadata.lean");
    fs::write(&probe, source).unwrap();
    checker
        .process(
            "theorem-metadata-unit",
            &[probe.to_string_lossy().into_owned()],
        )
        .unwrap();
}

/// This is an importer-refusal control, not an importer-reachable false-proof
/// exploit. The direct helper regression above tests Anneal's own invariant.
#[test]
fn pinned_importer_rejects_equal_body_metadata_conflicts() {
    for mode in ["metadata-all", "metadata-levels"] {
        target_library_inventory_case(
            "AAAAAlternate",
            mode,
            Some("environment already contains 'List.drop.eq_def'"),
        );
    }
}

/// Exercise typed result handling without a resource race or large allocation.
/// Existing invalid-proof fixtures separately exercise actual kernel/replay
/// exceptions through the inspector protocol.
#[test]
fn kernel_result_channels_preserve_success_mismatch_and_operational_error() {
    let fixture = Fixture::new(PROOF);
    let mut checker = fixture.checker();
    let inspector = checker.tool_admission().unwrap().inspector.clone();
    let mut source = fs::read_to_string(inspector).unwrap();
    source.push_str(
        r#"

#eval do
  TrustedBoundary.requireKernelEquality "success" "mismatch" (.ok true)
  let policy ← try
    TrustedBoundary.requireKernelEquality "false" "mismatch" (.ok false)
    pure false
  catch error => pure (error.toString == "policy:mismatch")
  unless policy do throw <| IO.userError "completed false equality lost policy status"
  let operational ← try
    TrustedBoundary.requireKernelEquality "resource" "mismatch" (.error .excessiveMemory)
    pure false
  catch error => pure (error.toString.startsWith "kernel operation failed (resource):")
  unless operational do throw <| IO.userError "kernel exception lost operational status"
  let value ← TrustedBoundary.kernelResult "value" (α := Nat) (.ok 7)
  unless value == 7 do throw <| IO.userError "kernel success value changed"
"#,
    );
    let probe = checker.stage().join("KernelResultChannels.lean");
    fs::write(&probe, source).unwrap();
    checker
        .process(
            "kernel-result-channels",
            &[probe.to_string_lossy().into_owned()],
        )
        .unwrap();
}
