// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pass 1 audit of independently realized equation theorems and paired
//! `_unsafe_rec` helpers.

use super::*;

/// Pass-1 `"audit"` admits sibling modules independently realizing the same
/// equation theorem (`sameRealizedThmHeader`) and computable well-founded
/// recursive definitions (`wfStep._unsafe_rec` paired with safe `wfStep`),
/// while failing closed on logical references to `_unsafe_rec` helpers,
/// unpaired `partial` declarations, and mismatched duplicate theorems.
#[test]
fn audit_admits_diamond_realized_theorems_and_paired_unsafe_rec() {
    let trusted_wf = "-- anneal-trust-tier: vetted\n\
         prelude\n\
         import Init.NotationExtra\n\
         import Init.Data.Nat.Basic\n\
         import Init.SimpLemmas\n\
         namespace Trusted\n\
         def wfStep (n : Nat) : Nat :=\n  \
           if h : n = 0 then 0 else\n    \
             have : n - 1 < n := Nat.sub_one_lt h\n    \
             wfStep (n - 1)\n\
         end Trusted\n";
    let mut fix = TempFixture::new(Some(trusted_wf));
    fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.NotationExtra\nimport Anneal.Left\nimport Anneal.Right\n",
    )
    .unwrap();
    for side in ["Left", "Right"] {
        fs::write(
            fix.root.join(format!("theory/Anneal/{side}.lean")),
            format!(
                "prelude\n\
                 import Init.NotationExtra\n\
                 import Init.Data.Nat.Basic\n\
                 import Init.SimpLemmas\n\
                 import Trusted\n\
                 namespace Anneal.{side}\n\
                 theorem step_zero : Trusted.wfStep 0 = 0 := by\n  \
                   rw [Trusted.wfStep]\n  \
                   decide\n\
                 def localWf (n : Nat) : Nat :=\n  \
                   if h : n = 0 then 0 else\n    \
                     have : n - 1 < n := Nat.sub_one_lt h\n    \
                     localWf (n - 1)\n\
                 end Anneal.{side}\n"
            ),
        )
        .unwrap();
    }
    let report = fix.check_expected(None, None, None).unwrap();
    assert_eq!(report["replay"], serde_json::json!(true), "{report}");

    // Negative 1: logical reference to a paired `_unsafe_rec` helper fails
    // closed in Pass-1 `"audit"`. Compile a stub `Trusted` where
    // `wfStep._unsafe_rec` is a safe `def` so Lean accepts
    // `Anneal.ForgedRecRef`, then swap that `.olean` into `fix`'s real
    // `Trusted` environment (`wfStep._unsafe_rec` is `partial`) and run
    // `"audit"` directly.
    let fix_ok = TempFixture::new(Some(trusted_wf));
    fs::create_dir_all(fix_ok.root.join("theory")).unwrap();
    fs::write(
        fix_ok.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.NotationExtra\nimport Trusted\n",
    )
    .unwrap();
    let mut checker_ok = fix_ok.checker();
    checker_ok.set_require_mir_wp(false);
    checker_ok.run().unwrap();

    let fix_stub = TempFixture::new(Some(
        "-- anneal-trust-tier: vetted\n\
         prelude\n\
         import Init.NotationExtra\n\
         namespace Trusted\n\
         def wfStep (n : Nat) : Nat := n\n\
         def wfStep._unsafe_rec (n : Nat) : Nat := n\n\
         end Trusted\n",
    ));
    fs::create_dir_all(fix_stub.root.join("theory")).unwrap();
    fs::write(
        fix_stub.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.NotationExtra\nimport Trusted\n",
    )
    .unwrap();
    let mut stub_checker = fix_stub.checker();
    stub_checker.set_require_mir_wp(false);
    stub_checker.run().unwrap();
    let stub_lib = stub_checker.stage().join("lib");
    let forged_src = stub_checker.stage().join("src/forged-rec");
    compile_forged_module(
        &mut stub_checker,
        &forged_src,
        &stub_lib,
        &["Trusted"],
        "Anneal.ForgedRecRef",
        "prelude\n\
         import Init.Core\n\
         import Trusted\n\
         theorem Anneal.ForgedRecRef.bad (n : Nat) :\n  \
           Trusted.wfStep._unsafe_rec n = Trusted.wfStep._unsafe_rec n := rfl\n",
    );

    let forged_dst = checker_ok.stage().join("lib/Anneal/ForgedRecRef.olean");
    fs::create_dir_all(forged_dst.parent().unwrap()).unwrap();
    fs::copy(stub_lib.join("Anneal/ForgedRecRef.olean"), &forged_dst).unwrap();
    let edges = vec![
        ImportEdge {
            module: "Init.Core".to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        },
        ImportEdge {
            module: "Trusted".to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        },
    ];
    let avail = BTreeMap::from([("olean", forged_dst.to_string_lossy().into_owned())]);
    let forged_arts = ModuleArtifacts::from_available(&avail, "test", String::new).unwrap();
    let adm = checker_ok.admitted_mut().unwrap();
    adm.artifacts.insert("Anneal.ForgedRecRef".to_string(), forged_arts);
    adm.graph.insert("Anneal.ForgedRecRef".to_string(), edges);

    let rec_err = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: vec!["Anneal".to_string(), "Anneal.ForgedRecRef".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(rec_err.code, 1, "{rec_err}");
    assert_eq!(rec_err.phase, "audit", "{rec_err}");
    assert!(
        rec_err.message.contains("paired _unsafe_rec helper Trusted.wfStep._unsafe_rec"),
        "{rec_err}"
    );

    // Negative 2: unpaired `partial def` (parent is `.opaqueInfo` rather than
    // a safe `.defnInfo`) bypassing `"preflight"` fails closed in `"audit"`.
    // Drop `Anneal.ForgedRecRef` from `checker_ok` so the admitted graph
    // matches `[Trusted, Trusted.ForgedPartial, Anneal]`.
    let adm_mut = checker_ok.admitted_mut().unwrap();
    adm_mut.artifacts.remove("Anneal.ForgedRecRef");
    adm_mut.graph.remove("Anneal.ForgedRecRef");
    let forged_partial_src = checker_ok.stage().join("src/forged-partial");
    let ok_lib = checker_ok.stage().join("lib");
    compile_forged_module(
        &mut checker_ok,
        &forged_partial_src,
        &ok_lib,
        &[],
        "Trusted.ForgedPartial",
        "prelude\nimport Init.Core\n\
         partial def Trusted.ForgedPartial.barePartial : Nat → Nat\n  \
           | n => barePartial n\n",
    );
    let partial_err = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string(), "Trusted.ForgedPartial".to_string()],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.ForgedPartial".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(partial_err.code, 1, "{partial_err}");
    assert_eq!(partial_err.phase, "audit", "{partial_err}");
    assert!(partial_err.message.contains("unsafe/partial declaration"), "{partial_err}");

    // Negative 3: diamond siblings defining the same theorem header with an
    // ill-typed forged alternate proof pass Lean's `importModules`
    // (`subsumesInfo` ignores `.thmInfo.value`) and fail closed in Pass-1
    // `"audit"` via `inventoryAlternates` + `checkAlternateProofs`.
    let adm_mut = checker_ok.admitted_mut().unwrap();
    adm_mut.artifacts.remove("Trusted.ForgedPartial");
    adm_mut.graph.remove("Trusted.ForgedPartial");
    let left_src = checker_ok.stage().join("src/forged-dup-left");
    compile_forged_module(
        &mut checker_ok,
        &left_src,
        &ok_lib,
        &[],
        "Anneal.DupLeft",
        "prelude\nimport Init.Core\n\
         theorem Anneal.Shared.dup : True := True.intro\n",
    );
    let right_olean = ok_lib.join("Anneal/DupRight.olean");
    let right_script = checker_ok.stage().join("forge-dup-right.lean");
    run_lean_script(
        &mut checker_ok,
        "forge-dup-right",
        &right_script,
        &format!(
            "import Lean\n\
             open Lean\n\
             def main : IO Unit := do\n  \
               let ci : ConstantInfo := .thmInfo {{\n    \
                 name := `Anneal.Shared.dup\n    \
                 levelParams := []\n    \
                 type := .const `True []\n    \
                 value := .const `False []\n    \
                 all := [`Anneal.Shared.dup]\n  \
               }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false\n    \
                 imports := #[{{ module := `Init.Core }}]\n    \
                 constNames := #[`Anneal.Shared.dup]\n    \
                 constants := #[ci]\n    \
                 extraConstNames := #[]\n    \
                 entries := #[]\n  \
               }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.DupRight md\n",
            right_olean.to_string_lossy()
        ),
    );
    let core_edge = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let right_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", right_olean.to_string_lossy().into_owned())]),
        "test",
        String::new,
    )
    .unwrap();
    let adm_dup = checker_ok.admitted_mut().unwrap();
    adm_dup.artifacts.insert("Anneal.DupRight".to_string(), right_arts);
    adm_dup.graph.insert("Anneal.DupRight".to_string(), core_edge);
    let thm_err = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: vec![
                "Anneal".to_string(),
                "Anneal.DupLeft".to_string(),
                "Anneal.DupRight".to_string(),
            ],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(thm_err.phase, "audit", "{thm_err}");
    assert!(
        thm_err.message.contains("alternate pinned theorem proof check Anneal.Shared.dup"),
        "{thm_err}"
    );
}
