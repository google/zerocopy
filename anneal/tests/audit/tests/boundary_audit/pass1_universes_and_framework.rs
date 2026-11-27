// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Universe polymorphism, the theory umbrella and manifest, and Pass 1
//! replay of the trusted framework.

use super::*;

/// Verifies `requireClaimProof` universe-parameter rejection in both Pass 1
/// (`"audit"`) and Pass 2 (`"correspondence-audit"`): neither a required
/// `*Claim` definition nor its proof theorem may declare universe parameters.
#[test]
fn rejects_universe_polymorphic_claims_and_proofs() {
    // 1. Pass 1 (`Audit`): universe-polymorphic claim and theorem rejection.
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    checker.set_require_mir_wp(true);

    let stage = checker.stage().to_path_buf();
    let src = stage.join("src/univ-poly");
    let lib = stage.join("lib");
    let theory_lib = stage.join("theory-lib");

    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &[],
        "Trusted.MirAst",
        "prelude\nimport Init.Core\nnamespace Trusted.MirAst\ndef x : Nat := 0\nend Trusted.MirAst\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &theory_lib,
        &[],
        "Anneal.MirWp.Canaries",
        "prelude\nimport Init.Core\n",
    );
    let run_pass1_audit = |chk: &mut Checker| {
        chk.inspect(InspectorRequest::Audit {
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.MirAst".to_string(),
                "Trusted.MirSemantics".to_string(),
            ],
            theory: vec![
                "Anneal.MirWp".to_string(),
                "Anneal.MirWp.Canaries".to_string(),
            ],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.MirAst".to_string(), TrustTier::Candidate(CandidateFeature::MirAst)),
                (
                    "Trusted.MirSemantics".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
            ]),
        })
    };

    // 1a. Universe-polymorphic Pass 1 claim.
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &["Trusted.MirAst"],
        "Trusted.MirSemantics",
        "prelude\nimport Init.Core\nimport Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         def SatisfiesPost : Prop := True\n\
         def Diverges : Prop := True\n\
         def Behavior : Prop := True\n\
         def WpSoundnessClaim.{u} (_f : Nat) : Prop :=\n\
           (fun (_ : PUnit.{u + 1}) => And SatisfiesPost (And Diverges Behavior)) PUnit.unit\n\
         end Trusted.MirSemantics\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &theory_lib,
        &["Trusted.MirSemantics"],
        "Anneal.MirWp",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Anneal.MirWp\n\
         def wpProg : Nat := 0\n\
         theorem wellFormed_and_spec_of_wp : \
           Trusted.MirSemantics.WpSoundnessClaim.{0} wpProg := \
           And.intro True.intro (And.intro True.intro True.intro)\n\
         end Anneal.MirWp\n",
    );
    let err_claim_u = run_pass1_audit(&mut checker).unwrap_err();
    assert_eq!(err_claim_u.code, 1, "unexpected code: {err_claim_u}");
    assert_eq!(err_claim_u.phase, "audit");
    assert!(
        err_claim_u.message.contains(
            "claim Trusted.MirSemantics.WpSoundnessClaim must have no universe parameters"
        ),
        "unexpected Pass 1 poly-claim error: {err_claim_u}"
    );

    // 1b. Universe-polymorphic Pass 1 proof theorem.
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &["Trusted.MirAst"],
        "Trusted.MirSemantics",
        "prelude\nimport Init.Core\nimport Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         def SatisfiesPost : Prop := True\n\
         def Diverges : Prop := True\n\
         def Behavior : Prop := True\n\
         def WpSoundnessClaim (_f : Nat) : Prop := And SatisfiesPost (And Diverges Behavior)\n\
         end Trusted.MirSemantics\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &theory_lib,
        &["Trusted.MirSemantics"],
        "Anneal.MirWp",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Anneal.MirWp\n\
         def wpProg : Nat := 0\n\
         theorem wellFormed_and_spec_of_wp.{u} :\n\
           (fun (_ : PUnit.{u + 1}) => Trusted.MirSemantics.WpSoundnessClaim wpProg) PUnit.unit :=\n\
           And.intro True.intro (And.intro True.intro True.intro)\n\
         end Anneal.MirWp\n",
    );
    let err_thm_u = run_pass1_audit(&mut checker).unwrap_err();
    assert_eq!(err_thm_u.code, 1, "unexpected code: {err_thm_u}");
    assert_eq!(err_thm_u.phase, "audit");
    assert!(
        err_thm_u.message.contains(
            "theorem Anneal.MirWp.wellFormed_and_spec_of_wp must have no universe parameters"
        ),
        "unexpected Pass 1 poly-theorem error: {err_thm_u}"
    );

    // 2. Pass 2 (`CorrespondenceAudit`): universe-polymorphic claim and
    // theorem rejection.
    let vendor_lib = stage.join("univ-vendor-lib");
    let corr_lib = stage.join("univ-corr-lib");
    compile_forged_module(
        &mut checker,
        &src,
        &vendor_lib,
        &[],
        "Miri.UnivStub",
        "prelude\nimport Init.Core\n\
         namespace Miri.Interpreter.ExecutionMachine\n\
         def step : Nat := 0\n\
         def AllowedStep : Nat := 0\n\
         def withValidation : Nat := 0\n\
         def stepHooks : Nat := 0\n\
         def rvalueHooks : Nat := 0\n\
         def operandHooks : Nat := 0\n\
         def projectionHooks : Nat := 0\n\
         def discriminantHooks : Nat := 0\n\
         def scalarHooks : Nat := 0\n\
         end Miri.Interpreter.ExecutionMachine\n\
         namespace Miri.Interpreter.Step\n\
         def step : Nat := 0\n\
         def evalStatement : Nat := 0\n\
         end Miri.Interpreter.Step\n\
         namespace Miri.Interpreter.ControlFlow\n\
         def goToBlock : Nat := 0\n\
         def evalTerminator : Nat := 0\n\
         def returnFromCurrentFrame : Nat := 0\n\
         end Miri.Interpreter.ControlFlow\n\
         namespace Miri.Interpreter.ExecutionControl\n\
         def hooks : Nat := 0\n\
         end Miri.Interpreter.ExecutionControl\n\
         namespace Miri.Interpreter.MachineHooks\n\
         def storageLiveDyn : Nat := 0\n\
         def storageDead : Nat := 0\n\
         end Miri.Interpreter.MachineHooks\n\
         namespace Miri.Interpreter.OperandMachine\n\
         def evalOperand : Nat := 0\n\
         def evalPlaceToOp : Nat := 0\n\
         end Miri.Interpreter.OperandMachine\n\
         namespace Miri.Interpreter.PlaceMachine\n\
         def readImmediate : Nat := 0\n\
         def writeMemory : Nat := 0\n\
         end Miri.Interpreter.PlaceMachine\n\
         namespace Miri.Interpreter.ValidityVisitor\n\
         def validatePlace : Nat := 0\n\
         end Miri.Interpreter.ValidityVisitor\n\
         namespace Miri.Interpreter.ValidityMemory\n\
         def bind : Nat := 0\n\
         end Miri.Interpreter.ValidityMemory\n\
         namespace Miri.Interpreter\n\
         def evalRvalueIntoPlace : Nat := 0\n\
         def evalOperand : Nat := 0\n\
         end Miri.Interpreter\n\
         namespace Miri.Interpreter.TerminatorMachine\n\
         def beforeTerminatorWithChoice : Nat := 0\n\
         end Miri.Interpreter.TerminatorMachine\n\
         namespace Miri.Interpreter.ScalarOps\n\
         def binary : Nat := 0\n\
         def unary : Nat := 0\n\
         end Miri.Interpreter.ScalarOps\n\
         namespace Miri.Interpreter.IntegerOps\n\
         def binary : Nat := 0\n\
         def binaryBool : Nat := 0\n\
         def unary : Nat := 0\n\
         end Miri.Interpreter.IntegerOps\n\
         namespace Miri.Interpreter.Discriminant\n\
         def readDiscriminant : Nat := 0\n\
         def discriminantForVariant : Nat := 0\n\
         end Miri.Interpreter.Discriminant\n\
         namespace Miri.Memory.ScalarInt\n\
         def truncateFromUInt : Nat := 0\n\
         def tryFromUInt : Nat := 0\n\
         def tryToBool : Nat := 0\n\
         end Miri.Memory.ScalarInt\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &[],
        "Trusted.MirSemantics",
        "prelude\nimport Init.Core\n\
         namespace Trusted.MirSemantics\n\
         def WellFormed : Prop := True\n\
         def Behavior : Prop := True\n\
         def Diverges : Prop := True\n\
         end Trusted.MirSemantics\n",
    );
    let run_pass2_audit = |chk: &mut Checker| {
        chk.inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![lib.clone(), vendor_lib.clone(), corr_lib.clone()],
            trusted: vec!["Trusted".to_string(), "Trusted.MirSemantics".to_string()],
            corr_trusted: vec!["Trusted.Correspondence".to_string()],
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: vec!["Miri.UnivStub".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.MirSemantics".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
                (
                    "Trusted.Correspondence".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
            ]),
        })
    };

    // 2a. Universe-polymorphic `CorrespondenceClaim`.
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &["Trusted.MirSemantics"],
        "Trusted.Correspondence",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Trusted.Correspondence\n\
         def RefWellFormed : Prop := True\n\
         def RefBehavior : Prop := True\n\
         def RefDiverges : Prop := True\n\
         def encodeProg : Nat := 0\n\
         def CorrespondenceClaim.{u} : Prop :=\n\
           (fun (_ : PUnit.{u + 1}) =>\n\
             Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧\n\
             Trusted.MirSemantics.Behavior ∧ RefBehavior ∧\n\
             Trusted.MirSemantics.Diverges ∧ RefDiverges ∧ encodeProg = encodeProg) PUnit.unit\n\
         end Trusted.Correspondence\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &corr_lib,
        &["Trusted.Correspondence"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Init.Core\nimport Trusted.Correspondence\n\
         namespace Anneal.MirCorrespondenceProof\n\
         theorem correspondence_claim_holds : \
           Trusted.Correspondence.CorrespondenceClaim.{0} :=\n\
           ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, Eq.refl _⟩\n\
         end Anneal.MirCorrespondenceProof\n",
    );
    let err_p2_claim = run_pass2_audit(&mut checker).unwrap_err();
    assert_eq!(err_p2_claim.code, 1, "unexpected code: {err_p2_claim}");
    assert_eq!(err_p2_claim.phase, "correspondence-audit");
    assert!(
        err_p2_claim.message.contains(
            "claim Trusted.Correspondence.CorrespondenceClaim must have no universe parameters"
        ),
        "unexpected Pass 2 poly-claim error: {err_p2_claim}"
    );

    // 2b. Universe-polymorphic `correspondence_claim_holds`.
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &["Trusted.MirSemantics"],
        "Trusted.Correspondence",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Trusted.Correspondence\n\
         def RefWellFormed : Prop := True\n\
         def RefBehavior : Prop := True\n\
         def RefDiverges : Prop := True\n\
         def encodeProg : Nat := 0\n\
         def CorrespondenceClaim : Prop :=\n\
           Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧\n\
           Trusted.MirSemantics.Behavior ∧ RefBehavior ∧\n\
           Trusted.MirSemantics.Diverges ∧ RefDiverges ∧ encodeProg = encodeProg\n\
         end Trusted.Correspondence\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &corr_lib,
        &["Trusted.Correspondence"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Init.Core\nimport Trusted.Correspondence\n\
         namespace Anneal.MirCorrespondenceProof\n\
         theorem correspondence_claim_holds.{u} :\n\
           (fun (_ : PUnit.{u + 1}) => Trusted.Correspondence.CorrespondenceClaim) PUnit.unit :=\n\
           ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, Eq.refl _⟩\n\
         end Anneal.MirCorrespondenceProof\n",
    );
    let err_p2_thm = run_pass2_audit(&mut checker).unwrap_err();
    assert_eq!(err_p2_thm.code, 1, "unexpected code: {err_p2_thm}");
    assert_eq!(err_p2_thm.phase, "correspondence-audit");
    assert!(
        err_p2_thm.message.contains(
            "theorem Anneal.MirCorrespondenceProof.correspondence_claim_holds must have no universe parameters"
        ),
        "unexpected Pass 2 poly-theorem error: {err_p2_thm}"
    );
}

fn parse_lean_header_imports_for_test(source: &str) -> Vec<String> {
    let bytes = source.as_bytes();
    let mut pos = 0usize;
    let mut imports = Vec::new();
    let mut expecting_import_target = false;
    while pos < bytes.len() {
        while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
            pos += 1;
        }
        if pos >= bytes.len() {
            break;
        }
        if bytes[pos..].starts_with(b"--") {
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        if bytes[pos..].starts_with(b"/-") {
            pos += 2;
            let mut depth = 1usize;
            while pos < bytes.len() && depth > 0 {
                if bytes[pos..].starts_with(b"/-") {
                    depth += 1;
                    pos += 2;
                } else if bytes[pos..].starts_with(b"-/") {
                    depth -= 1;
                    pos += 2;
                } else {
                    pos += 1;
                }
            }
            continue;
        }
        let start = pos;
        while pos < bytes.len()
            && !bytes[pos].is_ascii_whitespace()
            && !bytes[pos..].starts_with(b"--")
            && !bytes[pos..].starts_with(b"/-")
        {
            pos += 1;
        }
        let token = &source[start..pos];
        if expecting_import_target {
            if token == "all" {
                continue;
            }
            imports.push(token.to_string());
            expecting_import_target = false;
        } else if token == "import" {
            expecting_import_target = true;
        } else if !matches!(token, "module" | "prelude" | "public" | "meta") {
            break;
        }
    }
    imports
}

/// Ensures `theory/Anneal.lean` is absent, all four domain umbrellas
/// (`Anneal.{Scalar,Wp,PureLift,Simd}`) exist in `theory/`,
/// `theory/bundle-manifest.json` includes `Scalar` and `Wp`, excludes
/// `*Canaries*`, and is transitively closed under `Anneal.*` header imports,
/// `Anneal.Scalar`'s closure stays free of `Trusted.*`, `MirWp*`, `LoopInv`,
/// `ClassicalEm`, and `BitTrieLrat`, zero non-canary `theory/` modules import
/// `*Canaries*`, and `scan_lean_tree` still discovers all decoupled
/// `*Canaries*.lean` files for Pass-1 repository `anneal-audit`.
#[test]
fn theory_umbrella_and_manifest_exclude_canaries_and_match() {
    let checkout = repo_root();
    assert!(
        !checkout.join("theory/Anneal.lean").exists(),
        "monolithic theory/Anneal.lean must stay retired in favor of domain umbrellas"
    );
    let (_, manifest) = bundle::load_theory_bundle_manifest(&checkout)
        .expect("load theory/bundle-manifest.json");
    let manifest_paths: BTreeSet<String> =
        manifest.modules.iter().map(|m| m.path.clone()).collect();
    assert!(
        !manifest_paths.iter().any(|p| p.contains("Canaries")),
        "bundle-manifest.json must exclude *Canaries* modules: {manifest_paths:?}"
    );
    assert!(
        manifest_paths.contains("theory/Anneal/Scalar.lean"),
        "bundle-manifest.json must bundle theory/Anneal/Scalar.lean"
    );
    assert!(
        manifest_paths.contains("theory/Anneal/Wp.lean"),
        "bundle-manifest.json must bundle theory/Anneal/Wp.lean"
    );
    assert!(
        manifest_paths.contains("theory/Anneal/Framework.lean"),
        "bundle-manifest.json must bundle theory/Anneal/Framework.lean"
    );

    let theory_modules =
        scan_lean_tree(&checkout.join("theory"), "Anneal").expect("scan_lean_tree on theory/");
    assert!(!theory_modules.contains_key("Anneal"));
    for domain_umbrella in ["Anneal.Scalar", "Anneal.Wp", "Anneal.PureLift", "Anneal.Simd"] {
        assert!(
            theory_modules.contains_key(domain_umbrella),
            "expected domain umbrella {domain_umbrella} in theory/"
        );
    }

    let canary_modules: BTreeSet<String> =
        theory_modules.keys().filter(|m| m.contains("Canaries")).cloned().collect();
    assert!(
        canary_modules.contains("Anneal.MirWp.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.MirWp.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.F2Simd.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.F2Simd.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.ByteRun.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.ByteRun.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.OverflowCastJoin.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.OverflowCastJoin.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.RefFrame.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.RefFrame.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.CallStackUnwind.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.CallStackUnwind.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.Framework.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.Framework.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.len() >= 17,
        "expected scan_lean_tree to discover all decoupled *Canaries*.lean modules dynamically, got {canary_modules:?}"
    );

    // Every non-canary module under `theory/` (including bundled and unbundled
    // domain umbrellas) must not import any `*Canaries*` module or monolithic
    // `Anneal`.
    for (module, path) in &theory_modules {
        if canary_modules.contains(module) {
            continue;
        }
        let src = fs::read_to_string(path).unwrap();
        let imps = parse_lean_header_imports_for_test(&src);
        assert!(
            !imps.iter().any(|dep| dep.contains("Canaries")),
            "non-canary theory module {module} must not import any *Canaries* module: {imps:?}"
        );
        assert!(
            !imps.iter().any(|dep| dep == "Anneal"),
            "theory module {module} must not import retired Anneal umbrella: {imps:?}"
        );
    }

    // `theory/bundle-manifest.json` must be transitively closed under
    // `Anneal.*` header imports so every bundled module's theory dependencies
    // are also bundled.
    for rel_path in &manifest_paths {
        let src = fs::read_to_string(checkout.join(rel_path)).unwrap();
        for dep in parse_lean_header_imports_for_test(&src) {
            if dep == "Anneal" || dep.starts_with("Anneal.") {
                let dep_rel = format!("theory/{}.lean", dep.replace('.', "/"));
                assert!(
                    manifest_paths.contains(&dep_rel),
                    "bundled module {rel_path} imports unbundled theory module {dep} ({dep_rel})"
                );
            }
        }
    }

    // Verify `Anneal.Scalar`'s transitive header import closure stays purely
    // constructive and model-independent (excluding `Trusted.*`, `MirWp*`,
    // `LoopInv`, `ClassicalEm`, and `BitTrieLrat`).
    let mut scalar_theory_visited = BTreeSet::new();
    let mut scalar_all_imports = BTreeSet::new();
    let mut queue = VecDeque::from([String::from("Anneal.Scalar")]);
    while let Some(module) = queue.pop_front() {
        if !scalar_theory_visited.insert(module.clone()) {
            continue;
        }
        let path = theory_modules
            .get(&module)
            .unwrap_or_else(|| panic!("missing theory source for {module}"));
        let src = fs::read_to_string(path).unwrap();
        for dep in parse_lean_header_imports_for_test(&src) {
            scalar_all_imports.insert(dep.clone());
            if dep.starts_with("Anneal.") && !scalar_theory_visited.contains(&dep) {
                queue.push_back(dep);
            }
        }
    }
    for imp in &scalar_all_imports {
        assert!(
            imp != "Trusted"
                && !imp.starts_with("Trusted.")
                && imp != "Anneal.MirWp"
                && !imp.starts_with("Anneal.MirWp.")
                && imp != "Anneal.LoopInv"
                && imp != "Anneal.ClassicalEm"
                && imp != "Anneal.BitTrieLrat"
                && !imp.contains("Canaries"),
            "Anneal.Scalar transitive closure must exclude {imp} (closure={scalar_all_imports:?})"
        );
    }
}

/// Verifies that `Trusted.Framework` (`candidate:refinement`) compiles,
/// passes `"preflight"` and Pass-1 kernel replay onto `foundation-lock.json`,
/// discharges a structured `EnvelopeTheorem` proof in `Anneal.*`, and remains
/// isolated from `vetted` modules.
#[test]
fn trusted_framework_pass1_replay_and_vetted_tier_isolation() {
    let checkout = repo_root();
    let framework_src =
        fs::read_to_string(checkout.join("trusted/lean/Trusted/Framework.lean")).unwrap();
    let mut fix = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(fix.root.join("trusted/lean/Trusted/Framework.lean"), &framework_src).unwrap();
    fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal/TrustedFrameworkTest.lean"),
        concat!(
            "module\n",
            "prelude\n",
            "public import Init.NotationExtra\n",
            "public import Init.Data.List.Basic\n",
            "public import Trusted.Framework\n",
            "public section\n",
            "namespace Anneal\n",
            "open Trusted.Framework\n",
            "def unitModel : ExecutionModel Unit Unit Unit Unit Unit Unit :=\n",
            "  { profileId := \"unit_v1\"\n",
            "    oracleGrade := .biFaultEquiv \"unit_ref\"\n",
            "    programAdmitted := fun _ => true\n",
            "    bodyAdmitted := fun _ _ => true\n",
            "    isPartialScope := fun _ => false\n",
            "    bodyAt := fun _ n => match n with | 0 => some () | _ => none\n",
            "    uniqueIdentities := fun _ => true\n",
            "    bodyIdentity := fun _ => \"fn_u\"\n",
            "    bodyIsUnsafe := fun _ => false\n",
            "    bodyIsExternal := fun _ => false\n",
            "    bodyMatchesSig := fun _ _ => true\n",
            "    modelGaps := []\n",
            "    requiredGaps := fun _ => []\n",
            "    claimShapeGaps := fun _ => []\n",
            "    entryDom := fun _ _ => True\n",
            "    returnValid := fun _ _ _ => True\n",
            "    memValid := fun _ => True\n",
            "    execForBody := fun p _ => p\n",
            "    wellFormed := fun _ _ => True\n",
            "    produces := fun _ _ out => out = .returned () ()\n",
            "    diverges := fun _ _ => False\n",
            "    faultsUB := fun _ _ => False }\n",
            "theorem nonEmptyUnitId : (\"unit_v1\" : String) ≠ \"\" := by\n",
            "  intro h\n",
            "  exact Nat.noConfusion\n",
            "    (congrArg (fun s => s.toByteArray.data.toList.length) h)\n",
            "theorem nonEmptyRefId : (\"unit_ref\" : String) ≠ \"\" := by\n",
            "  intro h\n",
            "  exact Nat.noConfusion\n",
            "    (congrArg (fun s => s.toByteArray.data.toList.length) h)\n",
            "theorem nonEmptyFnId : (\"fn_u\" : String) ≠ \"\" := by\n",
            "  intro h\n",
            "  exact Nat.noConfusion\n",
            "    (congrArg (fun s => s.toByteArray.data.toList.length) h)\n",
            "theorem unitEnvelopeOk :\n",
            "    EnvelopeTheorem (mkEnvelope unitModel ()\n",
            "      [{ identity := \"fn_u\"\n",
            "         sig := ()\n",
            "         contract := {\n",
            "           effects := {\n",
            "             terminates := true,\n",
            "             noUnwind := true,\n",
            "             noAbort := true } } }]\n",
            "      [] [] [.forallSafety, .termination] []) := by\n",
            "  refine ⟨⟨nonEmptyUnitId, rfl, (fun _ _ _ => rfl), rfl,\n",
            "           (fun h => Bool.noConfusion h), nonEmptyRefId, ?_,\n",
            "           (fun _ h => by cases h)⟩,\n",
            "          ?_, ⟨nonEmptyFnId, (fun _ h => by cases h), True.intro⟩,\n",
            "          ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩\n",
            "  · intro cs hMem\n",
            "    cases hMem with\n",
            "    | head => exact ⟨rfl, fun _ h => by cases h⟩\n",
            "    | tail _ h2 =>\n",
            "      cases h2 with\n",
            "      | head => exact ⟨rfl, fun _ h => by cases h⟩\n",
            "      | tail _ hNil => cases hNil\n",
            "  · intro _ _\n",
            "    exact ⟨List.Mem.head _,\n",
            "           fun _ => List.Mem.tail _ (List.Mem.head _)⟩\n",
            "  · intro e hMem\n",
            "    cases hMem with\n",
            "    | head =>\n",
            "      refine ⟨0, (), rfl, rfl, rfl, rfl, (fun _ h => by cases h),\n",
            "              (fun _ _ _ => True.intro), ?_, ?_⟩\n",
            "      · intro _ _ _\n",
            "        refine ⟨(fun _ hDiv => hDiv),\n",
            "                (fun _ _ _ => ⟨True.intro, True.intro⟩),\n",
            "                (fun _ h => by cases h),\n",
            "                (fun _ h => by cases h)⟩\n",
            "      · exact Or.inl ⟨rfl, Or.inl ⟨(), True.intro,\n",
            "          ⟨(fun h => Bool.noConfusion h), True.intro⟩⟩⟩\n",
            "    | tail _ hNil => cases hNil\n",
            "  · intro defId _ hGet\n",
            "    cases defId with\n",
            "    | zero => exact List.Mem.head _\n",
            "    | succ _ => cases hGet\n",
            "end Anneal\n",
            "end\n",
        ),
    )
    .unwrap();
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    let report = checker.run().unwrap();
    assert_eq!(report["replay"], json!(true), "{report}");
    let decls = report["declarations"].as_array().unwrap();
    let fw_decls: Vec<&Json> =
        decls.iter().filter(|d| d["module"] == json!("Trusted.Framework")).collect();
    assert!(!fw_decls.is_empty(), "expected Trusted.Framework declarations in report");
    for d in &fw_decls {
        assert_eq!(d["trustStatus"], json!("candidate:refinement"), "{d}");
    }
    // Non-vacuously inspect the compiled `Trusted/Framework.olean` via
    // `Lean.readModuleData` (since `report["declarations"]` excludes partial
    // paired `._unsafe_rec` helpers) to confirm zero `partial` / `._unsafe_rec`
    // constants are emitted for `NoDupStrings` or any other declaration.
    let fw_olean = checker.stage().join("lib/Trusted/Framework.olean");
    let check_script = checker.stage().join("CheckNoUnsafeRec.lean");
    run_lean_script(
        &mut checker,
        "check-no-unsafe-rec",
        &check_script,
        &format!(
            r#"import Lean
open Lean in
def main : IO Unit := do
  let (data, _) ← readModuleData (System.FilePath.mk {:?})
  unless data.constants.any (fun ci => ci.name == `Trusted.Framework.NoDupStrings) do
    throw (IO.userError "missing Trusted.Framework.NoDupStrings in compiled olean")
  for ci in data.constants do
    if ci.isPartial || ci.name.toString.endsWith "._unsafe_rec" then
      throw (IO.userError s!"unexpected partial/_unsafe_rec constant: {{ci.name}}")
  for n in data.extraConstNames do
    if n.toString.endsWith "._unsafe_rec" then
      throw (IO.userError s!"unexpected extra _unsafe_rec constant: {{n}}")
"#,
            fw_olean.to_string_lossy()
        ),
    );

    // Negative: a `vetted` module attempting to import `Trusted.Framework`
    // (`candidate:refinement`) fails closed in `"preflight"`.
    fs::write(
        fix.root.join("trusted/lean/Trusted/VettedImportsFramework.lean"),
        "-- anneal-trust-tier: vetted\n\
         module\n\
         prelude\n\
         public import Init.NotationExtra\n\
         public import Trusted.Framework\n",
    )
    .unwrap();
    let err = fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err.message.contains(
            "vetted module Trusted.VettedImportsFramework cannot import candidate:refinement module Trusted.Framework"
        ),
        "{err}"
    );
}
