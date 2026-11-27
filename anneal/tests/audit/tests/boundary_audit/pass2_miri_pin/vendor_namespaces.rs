// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Vendor constant namespaces and kernel checking of vendored modules.

use super::*;

/// Verifies that `"correspondence-audit"` rejects a `.vendorMiri` module that
/// declares a constant in the reserved `Trusted` or `Anneal` root namespace
/// (including a `private` declaration), declares an `axiom` or `unsafe`
/// constant, or directly references `sorryAx`, `Lean.ofReduceBool`, or
/// `Lean.trustCompiler`, while a benign vendor constant passes those checks
/// and standalone kernel replay and fails only later at unconditional
/// `closureCorr` (`unknown declaration origin:
/// Miri.Interpreter.ExecutionMachine.step`).
#[test]
fn rejects_vendor_constants_in_reserved_namespaces() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let trusted_lib = checker.stage().join("lib");
    let vendor_src = checker.stage().join("src/fake-miri");
    let vendor_lib = checker.stage().join("fake-miri-lib");
    let cases: [(&str, &str, Option<&str>); 12] = [
        (
            "Miri.SpoofTrusted",
            "namespace Trusted\ndef Spoof : Nat := 0\nend Trusted\n",
            Some(
                "external module Miri.SpoofTrusted cannot declare constant \
                 Trusted.Spoof in reserved Trusted namespace",
            ),
        ),
        (
            "Miri.SpoofAnneal",
            "namespace Anneal\ndef Spoof : Nat := 0\nend Anneal\n",
            Some(
                "external module Miri.SpoofAnneal cannot declare constant \
                 Anneal.Spoof in reserved Anneal namespace",
            ),
        ),
        (
            "Miri.SpoofPrivate",
            "namespace Trusted\nprivate def hidden : Nat := 0\nend Trusted\n",
            Some("in reserved Trusted namespace"),
        ),
        (
            "Miri.SpoofAxiom",
            "namespace Miri.SpoofAxiom\naxiom spoofAx : False\nend Miri.SpoofAxiom\n",
            Some("vendor Miri module Miri.SpoofAxiom cannot declare axiom Miri.SpoofAxiom.spoofAx"),
        ),
        (
            "Miri.SpoofUnsafe",
            "namespace Miri.SpoofUnsafe\nunsafe def evil : Nat := 0\nend Miri.SpoofUnsafe\n",
            Some(
                "vendor Miri module Miri.SpoofUnsafe cannot declare unsafe \
                 constant Miri.SpoofUnsafe.evil",
            ),
        ),
        (
            "Miri.SpoofSorry",
            "namespace Miri.SpoofSorry\ntheorem spoofSorry : False := sorry\nend Miri.SpoofSorry\n",
            Some(
                "vendor Miri module Miri.SpoofSorry constant Miri.SpoofSorry.spoofSorry \
                 references sorryAx",
            ),
        ),
        (
            "Miri.SpoofOfReduceBool",
            "namespace Miri.SpoofOfReduceBool\n\
             theorem spoof (h : Lean.reduceBool true = true) : true = true := \
             Lean.ofReduceBool true true h\n\
             end Miri.SpoofOfReduceBool\n",
            Some(
                "vendor Miri module Miri.SpoofOfReduceBool constant \
                 Miri.SpoofOfReduceBool.spoof references forbidden compiler primitive",
            ),
        ),
        (
            "Miri.SpoofTrustCompiler",
            "namespace Miri.SpoofTrustCompiler\n\
             theorem spoof : True := Lean.trustCompiler\n\
             end Miri.SpoofTrustCompiler\n",
            Some(
                "vendor Miri module Miri.SpoofTrustCompiler constant \
                 Miri.SpoofTrustCompiler.spoof references forbidden compiler primitive \
                 Lean.trustCompiler",
            ),
        ),
        (
            "Miri.Interpreter.ExecutionMachine",
            "namespace Miri.Interpreter.ExecutionMachine\nunsafe def step : Nat := 0\nend Miri.Interpreter.ExecutionMachine\n",
            Some(
                "vendor Miri module Miri.Interpreter.ExecutionMachine cannot declare \
                 unsafe constant Miri.Interpreter.ExecutionMachine.step",
            ),
        ),
        (
            "Miri.Interpreter.ExecutionMachine",
            "namespace Miri.Interpreter.ExecutionMachine\npartial def step (n : Nat) : Nat := step n\nend Miri.Interpreter.ExecutionMachine\n",
            Some(
                "opaque/partial vendor Miri constant Miri.Interpreter.ExecutionMachine.step \
                 from Miri.Interpreter.ExecutionMachine in correspondence dependency cone",
            ),
        ),
        (
            "Miri.Interpreter.ExecutionMachine",
            "namespace Miri.Interpreter.ExecutionMachine\nopaque step : Nat := 0\nend Miri.Interpreter.ExecutionMachine\n",
            Some(
                "opaque/partial vendor Miri constant Miri.Interpreter.ExecutionMachine.step \
                 from Miri.Interpreter.ExecutionMachine in correspondence dependency cone",
            ),
        ),
        ("Miri.Benign", "namespace Miri.Benign\ndef ok : Nat := 0\nend Miri.Benign\n", None),
    ];
    for (module, body, expected) in cases {
        let rel = module.replace('.', "/");
        let src = vendor_src.join(format!("{rel}.lean"));
        fs::create_dir_all(src.parent().unwrap()).unwrap();
        fs::write(&src, format!("prelude\nimport Init.Core\n{body}")).unwrap();
        let out = vendor_lib.join(format!("{rel}.olean"));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        checker
            .process(
                &format!("compile-{module}"),
                &[
                    "-j1".to_string(),
                    "-M2048".to_string(),
                    "-t0".to_string(),
                    "-R".to_string(),
                    vendor_src.to_string_lossy().into_owned(),
                    "-o".to_string(),
                    out.to_string_lossy().into_owned(),
                    src.to_string_lossy().into_owned(),
                ],
            )
            .unwrap();
        let err = checker
            .inspect(InspectorRequest::CorrespondenceAudit {
                search_path: vec![trusted_lib.clone(), vendor_lib.clone()],
                trusted: vec!["Trusted".to_string()],
                corr_trusted: Vec::new(),
                theory: Vec::new(),
                corr_theory: Vec::new(),
                vendor_miri: vec![module.to_string()],
                module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            })
            .unwrap_err();
        assert_eq!(err.code, 1, "unexpected error code for {module}: {err}");
        assert_eq!(err.phase, "correspondence-audit", "unexpected phase: {err}");
        match expected {
            Some(message) => {
                assert!(err.message.contains(message), "unexpected error for {module}: {err}")
            }
            None => {
                assert!(
                    !err.message.contains("reserved"),
                    "benign vendor module {module} was rejected: {err}"
                );
                assert!(
                    err.message.contains(
                        "unknown declaration origin: Miri.Interpreter.ExecutionMachine.step"
                    ),
                    "unexpected error for {module}: {err}"
                );
            }
        }
    }
}

/// Verifies end-to-end that standalone kernel replay in Pass 2
/// (`"correspondence-audit"`) rejects an ill-typed `.vendorMiri` `.olean`
/// compiled with a scoped `set_option debug.skipKernelTC true` override (even
/// when compiled with CLI `-Ddebug.skipKernelTC=false`), and that a valid
/// minimal vendor closure passes replay and reports `miriReplay: true` with a
/// positive `miriReplayedDeclarations` count.
#[test]
fn rejects_vendor_miri_skip_kernel_tc_during_replay() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    checker.ensure_sysroot_foundation().unwrap();
    let trusted_lib = checker.stage().join("lib");
    let vendor_src = checker.stage().join("src/skip-tc-miri");
    let vendor_lib = checker.stage().join("skip-tc-miri-lib");

    // 1. Compile a vendor module whose scoped `set_option debug.skipKernelTC
    // true` overrides CLI `-Ddebug.skipKernelTC=false` to emit an ill-typed
    // theorem (`Miri.SkipKernelTC.bogus : False := True.intro`) into the
    // `.olean` without using `axiom`, `sorryAx`, `unsafe`, or compiler
    // reflection primitives.
    let bogus_src = vendor_src.join("Miri/SkipKernelTC.lean");
    let bogus_out = vendor_lib.join("Miri/SkipKernelTC.olean");
    fs::create_dir_all(bogus_src.parent().unwrap()).unwrap();
    fs::create_dir_all(bogus_out.parent().unwrap()).unwrap();
    fs::write(
        &bogus_src,
        "import Lean.Elab.Command\n\
         namespace Miri.SkipKernelTC\n\
         set_option debug.skipKernelTC true in\n\
         run_cmd\n\
           Lean.Elab.Command.liftCoreM <| Lean.addDecl <| .thmDecl {\n\
             name := `Miri.SkipKernelTC.bogus\n\
             levelParams := []\n\
             type := Lean.mkConst `False\n\
             value := Lean.mkConst `True.intro\n\
           }\n\
         end Miri.SkipKernelTC\n",
    )
    .unwrap();
    checker
        .process(
            "compile-Miri.SkipKernelTC",
            &[
                "-j1".to_string(),
                "-M4096".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                bogus_out.to_string_lossy().into_owned(),
                bogus_src.to_string_lossy().into_owned(),
            ],
        )
        .expect(
            "Lean must accept scoped `set_option debug.skipKernelTC true` \
             at compile time to prove CLI `-Ddebug.skipKernelTC=false` alone \
             is insufficient",
        );

    let err_replay = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![trusted_lib.clone(), vendor_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.SkipKernelTC".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    // Kernel replay exceptions are operational errors (exit code `2`) so no
    // stringified `Kernel.Exception` can spoof `"policy:"`.
    assert_eq!(
        err_replay.code, 2,
        "expected operational exit code 2 on kernel replay failure: {err_replay}"
    );
    assert_eq!(err_replay.phase, "correspondence-audit", "unexpected phase: {err_replay}");
    assert!(
        err_replay.message.contains("vendor Miri kernel replay failed")
            && err_replay.message.contains("Miri.SkipKernelTC.bogus")
            && err_replay.message.contains("declaration type mismatch"),
        "expected kernel replay type-mismatch rejection, got: {err_replay}"
    );

    // 2. Verify the positive path: a valid minimal `.vendorMiri` module
    // defining the 21 `ExecutionMachine` cone roots passes standalone kernel
    // replay and returns `miriReplay: true` with `miriReplayedDeclarations`
    // positive, while vendor-only mode (no correspondence modules) reports
    // `correspondenceReplay: false` with zero correspondence declarations
    // replayed.
    let valid_src = vendor_src.join("Miri/Interpreter/ExecutionMachine.lean");
    let valid_out = vendor_lib.join("Miri/Interpreter/ExecutionMachine.olean");
    fs::create_dir_all(valid_src.parent().unwrap()).unwrap();
    fs::create_dir_all(valid_out.parent().unwrap()).unwrap();
    fs::write(
        &valid_src,
        "prelude\n\
         import Init.Core\n\
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
    )
    .unwrap();
    checker
        .process(
            "compile-Miri.Interpreter.ExecutionMachine",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                valid_out.to_string_lossy().into_owned(),
                valid_src.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();

    let ok_rep = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![trusted_lib, vendor_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Interpreter.ExecutionMachine".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap();
    assert_eq!(ok_rep.get("miriReplay"), Some(&json!(true)));
    assert_eq!(ok_rep.get("miriReplayedDeclarations").and_then(Json::as_u64), Some(36));
    assert_eq!(ok_rep.get("correspondenceReplay"), Some(&json!(false)));
    for zero_field in ["correspondenceDeclarations", "correspondenceReplayedDeclarations"] {
        assert_eq!(
            ok_rep.get(zero_field).and_then(Json::as_u64),
            Some(0),
            "unexpected {zero_field}: {ok_rep}"
        );
    }
    assert!(
        ok_rep
            .get("miriClosureReachableDeclarations")
            .and_then(Json::as_u64)
            .is_some_and(|n| n >= 36),
        "unexpected reachable declarations: {ok_rep}"
    );
    assert_eq!(ok_rep.get("miriClosureAxioms"), Some(&json!([])));
}
