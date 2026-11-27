// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Module header admission: module-system modifiers, Lean and Lake
//! imports, and files without `prelude`.

use super::*;

/// `"headers"` admits Lean 4 module-system headers (`module`, `public import`)
/// while rejecting `import all`, `meta import`, non-module import modifiers,
/// and `Lean.*`/`Lake.*` imports with exit code 1, and accepts omitted
/// `prelude` (synthetic non-meta + meta `Init` pair) in unpinned mode.
#[test]
fn headers_rejects_module_system_modifiers_and_lean_lake_and_allows_no_prelude() {
    for (label, header, expected) in [
        ("module-import-all", "module\nprelude\nimport all Model\n", "import modifiers"),
        (
            "module-meta-import",
            "module\nprelude\nmeta import Model\n",
            "unsupported syntax kind Lean.Parser.Module.meta",
        ),
        (
            "module-lean-import",
            "module\nprelude\npublic import Lean.Elab\nimport Model\n",
            "disallowed sysroot import",
        ),
        ("import-all", "prelude\nimport all Model\n", "header parser error"),
        ("public-import", "prelude\npublic import Model\n", "header parser error"),
        ("meta-import", "prelude\nmeta import Model\n", "header parser error"),
        ("lean-import", "prelude\nimport Lean.Elab\nimport Model\n", "disallowed sysroot import"),
        ("lake-import", "prelude\nimport Lake.Build\nimport Model\n", "disallowed sysroot import"),
    ] {
        let mut f = Fixture::new(PROOF);
        f.set(
            "Spec",
            TargetRole::Specification,
            &format!("{header}def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n"),
        );
        let err = f.run().unwrap_err();
        assert_eq!(err.code, 1, "{label}: {err}");
        assert_eq!(err.phase, "headers", "{label}: {err}");
        assert!(err.message.contains(expected), "{label}: {err}");
    }

    // Direct unit probe of `validateTargetImports` confirming both legacy
    // non-`module` and Lean 4 `module`-system import rules as well as
    // acceptance of the synthetic `!hasPrelude` Init pair and the bundled
    // `Anneal.*` `Init.Data.Nat.Bitwise.Basic` exception.
    let probe_fixture = Fixture::new(PROOF);
    let mut probe_checker = probe_fixture.checker();
    let empty_proof_export = probe_checker.stage().join("proof_export_empty.json");
    fs::write(
        &empty_proof_export,
        r#"{"schemaVersion":1,"names":[],"levels":[],"exprs":[],"modules":[],"compilerOverrides":{"implementedBy":[],"extern":[],"csimp":[],"export":[],"init":[],"builtinInit":[],"cpass":[],"constantFold":[],"postponedCompile":[]}}"#,
    )
    .unwrap();
    let empty_proof_export_lit = serde_json::to_string(
        &serde_json::json!({
            "mode": "target-export",
            "sysroot": "",
            "artifacts": [],
            "foundation": [],
            "libraries": [],
            "proofExportPath": empty_proof_export.to_string_lossy(),
            "target": {
                "modules": [{"module": "Spec", "expectedSha256": "0", "role": "specification"}],
                "theoremModule": "Proof",
                "theoremName": "Proof.verify",
                "expectedModule": "Expected",
                "expectedDeclaration": "Expected.claim",
                "canonicalRoot": "R",
                "subjectDeclaration": "S",
                "specificationDeclaration": "P",
                "allowSorryInProof": false,
                "bindings": {
                    "requestSha256": "0",
                    "captureSha256": "0",
                    "modelManifestSha256": "0",
                    "specificationManifestSha256": "0"
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    let forged_eq_export = probe_checker.stage().join("proof_export_forged_eq.json");
    fs::write(
        &forged_eq_export,
        serde_json::to_string(&serde_json::json!({
            "schemaVersion": 1,
            "names": [
                ["a"],
                ["s", 0, "Option"],
                ["s", 1, "map"],
                ["s", 2, "eq_1"],
                ["s", 0, "True"],
                ["s", 4, "intro"]
            ],
            "levels": [],
            "exprs": [
                ["c", 4, []],
                ["c", 5, []]
            ],
            "modules": [{
                "module": "Proof",
                "isModule": true,
                "imports": [{"module": "Init.Core", "importAll": false, "isExported": true, "isMeta": false}],
                "constNames": [3],
                "constants": [["thm", 3, [], 0, 1, [3]]]
            }],
            "compilerOverrides": {
                "implementedBy": [], "extern": [], "csimp": [],
                "export": [], "init": [], "builtinInit": [],
                "cpass": [], "constantFold": [], "postponedCompile": []
            }
        }))
        .unwrap(),
    )
    .unwrap();
    let forged_eq_req_lit = serde_json::to_string(
        &serde_json::json!({
            "mode": "target-audit",
            "sysroot": "",
            "artifacts": [],
            "graph": {
                "Proof": [{"module": "Init.Core", "importAll": false, "isExported": true, "isMeta": false}]
            },
            "foundation": ["Init.Control.Lawful.Instances", "Init.Core"],
            "libraries": [],
            "axioms": [
                ["Classical.choice", "Init.Prelude"],
                ["Quot.sound", "Init.Prelude"],
                ["propext", "Init.Core"]
            ],
            "proofExportPath": forged_eq_export.to_string_lossy(),
            "target": {
                "modules": [{"module": "Proof", "expectedSha256": "0", "role": "proof", "isModule": true}],
                "theoremModule": "Proof",
                "theoremName": "Proof.verify",
                "expectedModule": "Expected",
                "expectedDeclaration": "Expected.claim",
                "canonicalRoot": "R",
                "subjectDeclaration": "S",
                "specificationDeclaration": "P",
                "allowSorryInProof": false,
                "bindings": {
                    "requestSha256": "0",
                    "captureSha256": "0",
                    "modelManifestSha256": "0",
                    "specificationManifestSha256": "0"
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    let forged_dup_export = probe_checker.stage().join("proof_export_forged_dup.json");
    fs::write(
        &forged_dup_export,
        serde_json::to_string(&serde_json::json!({
            "schemaVersion": 1,
            "names": [
                ["a"],
                ["s", 0, "Shared"],
                ["s", 1, "dup"],
                ["s", 0, "True"],
                ["s", 3, "intro"],
                ["s", 0, "False"]
            ],
            "levels": [],
            "exprs": [
                ["c", 3, []],
                ["c", 4, []],
                ["c", 5, []]
            ],
            "modules": [
                {
                    "module": "HelperA",
                    "isModule": true,
                    "imports": [{"module": "Init.Core", "importAll": false, "isExported": true, "isMeta": false}],
                    "constNames": [2],
                    "constants": [["thm", 2, [], 0, 1, [2]]]
                },
                {
                    "module": "Proof",
                    "isModule": true,
                    "imports": [{"module": "Init.Core", "importAll": false, "isExported": true, "isMeta": false}],
                    "constNames": [2],
                    "constants": [["thm", 2, [], 2, 1, [2]]]
                }
            ],
            "compilerOverrides": {
                "implementedBy": [], "extern": [], "csimp": [],
                "export": [], "init": [], "builtinInit": [],
                "cpass": [], "constantFold": [], "postponedCompile": []
            }
        }))
        .unwrap(),
    )
    .unwrap();
    let forged_dup_req_lit = serde_json::to_string(
        &serde_json::json!({
            "mode": "target-audit",
            "sysroot": "",
            "artifacts": [],
            "graph": {},
            "foundation": ["Init.Control.Lawful.Instances", "Init.Core"],
            "libraries": [],
            "axioms": [
                ["Classical.choice", "Init.Prelude"],
                ["Quot.sound", "Init.Prelude"],
                ["propext", "Init.Core"]
            ],
            "proofExportPath": forged_dup_export.to_string_lossy(),
            "target": {
                "modules": [
                    {"module": "HelperA", "expectedSha256": "0", "role": "proof", "isModule": true},
                    {"module": "Proof", "expectedSha256": "0", "role": "proof", "isModule": true}
                ],
                "theoremModule": "Proof",
                "theoremName": "Proof.verify",
                "expectedModule": "Expected",
                "expectedDeclaration": "Expected.claim",
                "canonicalRoot": "R",
                "subjectDeclaration": "S",
                "specificationDeclaration": "P",
                "allowSorryInProof": false,
                "bindings": {
                    "requestSha256": "0",
                    "captureSha256": "0",
                    "modelManifestSha256": "0",
                    "specificationManifestSha256": "0"
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    let forged_anon_export = probe_checker.stage().join("proof_export_forged_anon.json");
    fs::write(
        &forged_anon_export,
        serde_json::to_string(&serde_json::json!({
            "schemaVersion": 1,
            "names": [
                ["a"],
                ["s", 0, "True"],
                ["s", 1, "intro"]
            ],
            "levels": [],
            "exprs": [
                ["c", 1, []],
                ["c", 2, []]
            ],
            "modules": [{
                "module": "Proof",
                "isModule": true,
                "imports": [{"module": "Init.Core", "importAll": false, "isExported": true, "isMeta": false}],
                "constNames": [0],
                "constants": [["thm", 0, [], 0, 1, [0]]]
            }],
            "compilerOverrides": {
                "implementedBy": [], "extern": [], "csimp": [],
                "export": [], "init": [], "builtinInit": [],
                "cpass": [], "constantFold": [], "postponedCompile": []
            }
        }))
        .unwrap(),
    )
    .unwrap();
    let forged_anon_req_lit = serde_json::to_string(
        &serde_json::json!({
            "mode": "target-audit",
            "sysroot": "",
            "artifacts": [],
            "graph": {},
            "foundation": ["Init.Control.Lawful.Instances", "Init.Core"],
            "libraries": [],
            "axioms": [
                ["Classical.choice", "Init.Prelude"],
                ["Quot.sound", "Init.Prelude"],
                ["propext", "Init.Core"]
            ],
            "proofExportPath": forged_anon_export.to_string_lossy(),
            "target": {
                "modules": [{"module": "Proof", "expectedSha256": "0", "role": "proof", "isModule": true}],
                "theoremModule": "Proof",
                "theoremName": "Proof.verify",
                "expectedModule": "Expected",
                "expectedDeclaration": "Expected.claim",
                "canonicalRoot": "R",
                "subjectDeclaration": "S",
                "specificationDeclaration": "P",
                "allowSorryInProof": false,
                "bindings": {
                    "requestSha256": "0",
                    "captureSha256": "0",
                    "modelManifestSha256": "0",
                    "specificationManifestSha256": "0"
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    let inspector = probe_checker.tool_admission().unwrap().inspector.clone();
    let mut probe_src = fs::read_to_string(inspector).unwrap();
    probe_src.push_str(
        r#"

#eval do
  let okPair : Array Lean.Import := #[
    { module := `Init, importAll := false, isExported := true, isMeta := false },
    { module := `Init, importAll := false, isExported := true, isMeta := true }
  ]
  TrustedBoundary.validateTargetImports "Spec" okPair
  let okModuleImps : Array Lean.Import := #[
    { module := `Init, importAll := false, isExported := false, isMeta := false },
    { module := `Init, importAll := false, isExported := false, isMeta := true },
    { module := `Model, importAll := false, isExported := true, isMeta := false },
    { module := `Helper, importAll := false, isExported := false, isMeta := false }
  ]
  TrustedBoundary.validateTargetImports "Spec" okModuleImps (allowModule := true)
  TrustedBoundary.validateTargetImports "Anneal.NatBitwise"
    #[{ module := `Init.Data.Nat.Bitwise.Basic, importAll := true, isExported := false, isMeta := false }]
    (allowModule := true) (allowTheoryImportAll := true)
  let badCases : Array (String × Bool × Bool × Array Lean.Import × String) := #[
    ("importAll", false, false, #[{ module := `Init, importAll := true, isExported := true, isMeta := false }], "import modifiers"),
    ("private", false, false, #[{ module := `Init, importAll := false, isExported := false, isMeta := false }], "import modifiers"),
    ("unpairedMetaInit", false, false, #[{ module := `Init, importAll := false, isExported := true, isMeta := true }], "meta import Init"),
    ("metaNonInit", false, false, #[{ module := `Init, importAll := false, isExported := true, isMeta := false }, { module := `Model, importAll := false, isExported := true, isMeta := true }], "meta import Model"),
    ("lean", false, false, #[{ module := `Lean.Elab, importAll := false, isExported := true, isMeta := false }], "disallowed sysroot import"),
    ("lake", false, false, #[{ module := `Lake, importAll := false, isExported := true, isMeta := false }], "disallowed sysroot import"),
    ("modImportAll", true, false, #[{ module := `Model, importAll := true, isExported := false, isMeta := false }], "import modifiers"),
    ("modTheoryNonBitwiseImportAll", true, true, #[{ module := `Model, importAll := true, isExported := false, isMeta := false }], "import modifiers"),
    ("modMetaNonInit", true, false, #[{ module := `Model, importAll := false, isExported := false, isMeta := true }], "meta import Model"),
    ("modLean", true, false, #[{ module := `Lean.Elab, importAll := false, isExported := true, isMeta := false }], "disallowed sysroot import"),
    ("modLake", true, false, #[{ module := `Lake, importAll := false, isExported := true, isMeta := false }], "disallowed sysroot import")
  ]
  for (label, allowMod, allowBitwiseAll, imps, want) in badCases do
    let ok ← try
      TrustedBoundary.validateTargetImports "Spec" imps
        (allowModule := allowMod) (allowTheoryImportAll := allowBitwiseAll)
      pure false
    catch e =>
      let msg := e.toString
      unless msg.startsWith "policy:" && (msg.splitOn want).length > 1 do
        throw <| IO.userError s!"{label}: unexpected error {msg}"
      pure true
    unless ok do
      throw <| IO.userError s!"{label}: unexpectedly accepted"
"#,
    );
    probe_src.push_str(&format!(
        r#"
  -- Realized theorem and generated-helper guards used by `"target-audit"`.
  let forgedEqBase ← IO.ofExcept <| Lean.Json.parse {forged_eq_req_lit}
  let initEnv : Lean.Environment ← TrustedBoundary.importEnv forgedEqBase #[`Init.Control.Lawful.Instances, `Init.Core]
  let helperName := `Option.map.eq_1
  let mkThm (lps : List Lean.Name) (ty val : Lean.Expr) : Lean.ConstantInfo :=
    .thmInfo {{ name := helperName, levelParams := lps, type := ty, value := val, all := [helperName] }}
  let base := mkThm [`u] (Lean.mkConst `True) (Lean.mkConst `True.intro)
  let altProof := mkThm [`u] (Lean.mkConst `True) (Lean.mkConst `trivial)
  unless TrustedBoundary.sameRealizedThmHeader base altProof do
    throw <| IO.userError "realized-thm: differing proof body rejected"
  let defnCopy : Lean.ConstantInfo :=
    .defnInfo {{ name := helperName, levelParams := [`u], type := Lean.mkConst `True, value := Lean.mkConst `True.intro, hints := .opaque, safety := .safe, all := [helperName] }}
  for (label, other) in #[
      ("levelParams", mkThm [`v] (Lean.mkConst `True) (Lean.mkConst `True.intro)),
      ("type", mkThm [`u] (Lean.mkConst `False) (Lean.mkConst `True.intro)),
      ("kind", defnCopy)
    ] do
    if TrustedBoundary.sameRealizedThmHeader base other then
      throw <| IO.userError s!"realized-thm: {{label}} difference accepted"
  unless TrustedBoundary.isRealizedOrCompilerHelper initEnv {{}} (· == `Option.map) base
      (allowUnimportedProofSparse := true) do
    throw <| IO.userError "lazy-helper: helper of admitted parent rejected"
  if TrustedBoundary.isRealizedOrCompilerHelper initEnv {{}} (fun _ => false) base
      (allowUnimportedProofSparse := true) then
    throw <| IO.userError "lazy-helper: helper of unknown parent accepted"
  let unknownEq : Lean.ConstantInfo :=
    .thmInfo {{ name := `X.f.eq_1, levelParams := [`u], type := Lean.mkConst `True, value := Lean.mkConst `True.intro, all := [`X.f.eq_1] }}
  if TrustedBoundary.isRealizedOrCompilerHelper initEnv {{}} (· == `X.f) unknownEq
      (allowUnimportedProofSparse := true) then
    throw <| IO.userError "lazy-helper: unreserved parent accepted"
  let nonHelper : Lean.ConstantInfo :=
    .thmInfo {{ name := `Option.map.dup, levelParams := [`u], type := Lean.mkConst `True, value := Lean.mkConst `True.intro, all := [`Option.map.dup] }}
  if TrustedBoundary.isRealizedOrCompilerHelper initEnv {{}} (· == `Option.map) nonHelper
      (allowUnimportedProofSparse := true) then
    throw <| IO.userError "lazy-helper: non-helper suffix accepted"
  let mut gEntries : List (String × Lean.Json) :=
    (initEnv.header.modules.zip initEnv.header.moduleData).toList.map fun ((m : Lean.EffectiveImport), (d : Lean.ModuleData)) =>
      (m.module.toString, Lean.toJson d.imports)
  gEntries := ("Proof", Lean.toJson #[({{ module := `Init.Core, importAll := false, isExported := true, isMeta := false }} : Lean.Import)]) :: gEntries
  let found := initEnv.header.modules.map (fun (m : Lean.EffectiveImport) => m.module)
  let forgedEqReq := forgedEqBase.setObjVal! "graph" (Lean.Json.mkObj gEntries)
  let forgedRejected ← try
    let _ ← TrustedBoundary.targetAudit forgedEqReq found
    pure false
  catch e =>
    let msg := e.toString
    unless (msg.splitOn "duplicate target declaration Option.map.eq_1").length > 1 do
      throw <| IO.userError s!"forged-wrong-type-lazy-helper: unexpected error {{msg}}"
    pure true
  unless forgedRejected do
    throw <| IO.userError "forged-wrong-type-lazy-helper: unexpectedly accepted"
  let forgedDupBase ← IO.ofExcept <| Lean.Json.parse {forged_dup_req_lit}
  let mut dupGEntries : List (String × Lean.Json) :=
    (initEnv.header.modules.zip initEnv.header.moduleData).toList.map fun ((m : Lean.EffectiveImport), (d : Lean.ModuleData)) =>
      (m.module.toString, Lean.toJson d.imports)
  let coreImp := Lean.toJson #[({{ module := `Init.Core, importAll := false, isExported := true, isMeta := false }} : Lean.Import)]
  dupGEntries := ("HelperA", coreImp) :: ("Proof", coreImp) :: dupGEntries
  let forgedDupReq := forgedDupBase.setObjVal! "graph" (Lean.Json.mkObj dupGEntries)
  let dupRejected ← try
    let _ ← TrustedBoundary.targetAudit forgedDupReq found
    pure false
  catch e =>
    let msg := e.toString
    unless (msg.splitOn "duplicate target declaration Shared.dup").length > 1 do
      throw <| IO.userError s!"forged-proof-dup: unexpected error {{msg}}"
    pure true
  unless dupRejected do
    throw <| IO.userError "forged-proof-dup: unexpectedly accepted"
  let forgedAnonBase ← IO.ofExcept <| Lean.Json.parse {forged_anon_req_lit}
  let forgedAnonReq := forgedAnonBase.setObjVal! "graph" (Lean.Json.mkObj gEntries)
  let assertPolicyErr (label want : String) (act : IO Unit) : IO Unit := do
    let rejected ← try
      act
      pure false
    catch e =>
      let msg := e.toString
      unless msg.startsWith "policy:" && (msg.splitOn want).length > 1 do
        throw <| IO.userError s!"{{label}}: unexpected error {{msg}}"
      pure true
    unless rejected do
      throw <| IO.userError s!"{{label}}: unexpectedly accepted"
  assertPolicyErr "forged-proof-anon" "anonymous declaration in target inventory Proof" do
    discard <| TrustedBoundary.targetAudit forgedAnonReq found
  assertPolicyErr "replay-map-key" "replay map key MismatchKey differs from Option.map.eq_1" do
    TrustedBoundary.validateReplayMap initEnv.toKernelEnv
      (({{}} : Std.HashMap Lean.Name Lean.ConstantInfo).insert `MismatchKey base) "probe"
  let some trueCi := initEnv.checked.get.find? `True
    | throw <| IO.userError "missing True in initEnv"
  assertPolicyErr "replay-base-shadow" "declaration True shadows base environment" do
    TrustedBoundary.validateReplayMap initEnv.toKernelEnv
      (({{}} : Std.HashMap Lean.Name Lean.ConstantInfo).insert `True trueCi) "probe"
  let omittedPartial : Lean.ConstantInfo := .defnInfo {{
    name := `OmittedPartial, levelParams := [], type := Lean.mkConst `True,
    value := Lean.mkConst `True.intro, hints := .opaque, safety := .partial,
    all := [`OmittedPartial] }}
  assertPolicyErr "replay-omitted" "declaration OmittedPartial omitted after kernel replay" do
    discard <| TrustedBoundary.replayKernelEnv initEnv.toKernelEnv
      (({{}} : Std.HashMap Lean.Name Lean.ConstantInfo).insert `OmittedPartial omittedPartial)
      "probe"
  let missingIsModReq ← IO.ofExcept <| Lean.Json.parse {empty_proof_export_lit}
  for (fnLabel, runner) in #[
      ("targetExport-missing-isModule", TrustedBoundary.targetExport missingIsModReq #[]),
      ("targetAudit-missing-isModule", TrustedBoundary.targetAudit missingIsModReq #[])
    ] do
    let rejected ← try
      let _ ← runner
      pure false
    catch e =>
      let msg := e.toString
      unless msg == "Bool expected" do
        throw <| IO.userError s!"{{fnLabel}}: unexpected error {{msg}}"
      pure true
    unless rejected do
      throw <| IO.userError s!"{{fnLabel}}: unexpectedly accepted"
"#,
    ));
    let probe_path = probe_checker.stage().join("ValidateTargetImports.lean");
    fs::write(&probe_path, probe_src).unwrap();
    probe_checker
        .process(
            "validate-target-imports-unit",
            &[probe_path.to_string_lossy().into_owned()],
        )
        .unwrap();

    // Unpinned mode: omitting `prelude` produces Lean 4's synthetic
    // `Init(isMeta = false)` + `Init(isMeta = true)` pair and must pass
    // `"headers"`, `"spec-preflight"`, and `"target-audit"` end-to-end.
    let mut f = Fixture::new(
        "import Expected\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f.set(
        "Spec",
        TargetRole::Specification,
        "import Model\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
    );
    let mut checker = f.cargo_checker();
    checker.set_allow_unpinned_lean(true);
    let report = checker.run_target(&f.request).unwrap();
    assert_eq!(report["replay"], true);
    assert_eq!(report["exactType"], true);
    assert_eq!(report["sorryDeclarations"], serde_json::json!([]));
}
