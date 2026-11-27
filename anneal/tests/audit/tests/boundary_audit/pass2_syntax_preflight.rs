// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pass 2 rejection of Lean syntax extensions and scoped extensions.

use super::*;

/// Verifies Pass 2 compile-environment syntactic preflight
/// (`"correspondence-preflight"`): syntax registered by `Lean`/`Std` (via
/// `Miri.*` importing `Lean`), such as `throwError "x"`
/// (`Lean.termThrowError__`) and `m! "x"` (`Lean.termM!_`), slips past
/// foundation-only `"preflight"` as a plain application, but is rejected with
/// policy exit code `1` by `"correspondence-preflight"` in both
/// `correspondence/` and `trusted/correspondence/` modules before compilation.
#[test]
fn rejects_pass2_lean_syntax_extensions_in_correspondence_preflight() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    checker.ensure_sysroot_foundation().unwrap();

    let trusted_lib = checker.stage().join("lib");
    let vendor_src = checker.stage().join("src/lean-ext-miri");
    let vendor_lib = checker.stage().join("lean-ext-miri-lib");
    let miri_src = vendor_src.join("Miri/ImportLean.lean");
    let miri_out = vendor_lib.join("Miri/ImportLean.olean");
    fs::create_dir_all(miri_src.parent().unwrap()).unwrap();
    fs::create_dir_all(miri_out.parent().unwrap()).unwrap();
    fs::write(
        &miri_src,
        "import Lean.Exception\nnamespace Miri.ImportLean\ndef ok : Nat := 0\nend Miri.ImportLean\n",
    )
    .unwrap();
    checker
        .process(
            "compile-Miri.ImportLean",
            &[
                "-j1".to_string(),
                "-M4096".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                miri_out.to_string_lossy().into_owned(),
                miri_src.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();

    let corr_src = checker.stage().join("src/corr-preflight-test");
    fs::create_dir_all(corr_src.join("Anneal")).unwrap();
    fs::create_dir_all(corr_src.join("Trusted")).unwrap();

    let bad_throw_theory = corr_src.join("Anneal/BadThrowError.lean");
    fs::write(
        &bad_throw_theory,
        "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
         namespace Anneal.BadThrowError\n\
         def f := throwError \"x\"\n\
         end Anneal.BadThrowError\n",
    )
    .unwrap();

    let bad_throw_trusted = corr_src.join("Trusted/BadThrowError.lean");
    fs::write(
        &bad_throw_trusted,
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nimport Miri.ImportLean\n\
         namespace Trusted.BadThrowError\n\
         def f := throwError \"x\"\n\
         end Trusted.BadThrowError\n",
    )
    .unwrap();

    let bad_msg_theory = corr_src.join("Anneal/BadMsgData.lean");
    fs::write(
        &bad_msg_theory,
        "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
         namespace Anneal.BadMsgData\n\
         def f := m! \"x\"\n\
         end Anneal.BadMsgData\n",
    )
    .unwrap();

    let good_corr = corr_src.join("Anneal/GoodCorr.lean");
    fs::write(
        &good_corr,
        "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
         namespace Anneal.GoodCorr\n\
         theorem ok : True := by exact True.intro\n\
         end Anneal.GoodCorr\n",
    )
    .unwrap();

    // Confirm that foundation-only `"preflight"` parses `throwError "x"` as a
    // plain function application without rejecting it.
    checker
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Anneal.BadThrowError".to_string(), bad_throw_theory.clone())],
            base_trusted_sources: Vec::new(),
            allow_local_semireducible: false,
        })
        .expect("foundation-only preflight parses `throwError` as a plain identifier");

    let trusted_base_src = checker.modules()["Trusted"].clone();
    let run_corr_pf = |chk: &mut Checker, module: &str, path: &Path| {
        chk.inspect(InspectorRequest::CorrespondencePreflight {
            search_path: vec![trusted_lib.clone(), vendor_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.ImportLean".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![(module.to_string(), path.to_path_buf())],
        })
    };

    let err_throw =
        run_corr_pf(&mut checker, "Anneal.BadThrowError", &bad_throw_theory).unwrap_err();
    assert_eq!(err_throw.code, 1, "expected policy exit 1: {err_throw}");
    assert_eq!(err_throw.phase, "correspondence-preflight");
    assert!(
        err_throw.message.contains("unsupported syntax kind Lean.termThrowError__"),
        "expected Lean.termThrowError__ rejection, got: {err_throw}"
    );

    let err_trusted_throw =
        run_corr_pf(&mut checker, "Trusted.BadThrowError", &bad_throw_trusted).unwrap_err();
    assert_eq!(err_trusted_throw.code, 1, "expected policy exit 1: {err_trusted_throw}");
    assert_eq!(err_trusted_throw.phase, "correspondence-preflight");
    assert!(
        err_trusted_throw.message.contains("unsupported syntax kind Lean.termThrowError__"),
        "expected Lean.termThrowError__ rejection, got: {err_trusted_throw}"
    );

    let err_msg = run_corr_pf(&mut checker, "Anneal.BadMsgData", &bad_msg_theory).unwrap_err();
    assert_eq!(err_msg.code, 1, "expected policy exit 1: {err_msg}");
    assert_eq!(err_msg.phase, "correspondence-preflight");
    assert!(
        err_msg.message.contains("unsupported syntax kind Lean.termM!_"),
        "expected Lean.termM!_ rejection, got: {err_msg}"
    );

    // Benign correspondence proof module passes `"correspondence-preflight"`.
    run_corr_pf(&mut checker, "Anneal.GoodCorr", &good_corr)
        .expect("benign correspondence module must pass correspondence-preflight");
}

/// Verifies scoped-extension defense in `"correspondence-preflight"`: any
/// `open`, `open ... in`, `namespace`, relative nested `open`,
/// multi-component declaration (`expandNamespacedDeclaration`), or `mutual`
/// preamble targeting a namespace that registers scoped `ScopedEnvExtension`
/// entries (such as a synthetic vendor `scoped syntax`/`scoped macro_rules` or
/// `Lean`/`Init` scoped namespaces like `List` or `Lean.PostprocessTraces`) is
/// rejected with policy exit code `1` before compilation—including when an
/// unimported `theory/` module declares a decoy namespace with the same suffix
/// (1-step or chained 2-step shadowing in the union parser environment).
#[test]
fn rejects_scoped_syntax_and_extensions_in_preflight() {
    let fix = TempFixture::new(None);
    let decoy_path = fix.root.join("theory/Anneal/DecoyNs.lean");
    fs::create_dir_all(decoy_path.parent().unwrap()).unwrap();
    fs::write(fix.root.join("theory/Anneal.lean"), "prelude\nimport Init.Core\n").unwrap();
    fs::write(
        &decoy_path,
        "prelude\nimport Init.Core\n\
         namespace Anneal.Miri.ScopedSyntax\n\
         def decoy : Nat := 0\n\
         end Anneal.Miri.ScopedSyntax\n\
         namespace Anneal.Miri\n\
         def decoyMiri : Nat := 0\n\
         end Anneal.Miri\n\
         namespace Anneal.Lean.PostprocessTraces\n\
         def decoyTraces : Nat := 0\n\
         end Anneal.Lean.PostprocessTraces\n",
    )
    .unwrap();
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    checker.ensure_sysroot_foundation().unwrap();

    let trusted_lib = checker.stage().join("lib");
    let theory_lib = checker.stage().join("theory-lib");
    let vendor_src = checker.stage().join("src/scoped-miri");
    let vendor_lib = checker.stage().join("scoped-miri-lib");
    let miri_src = vendor_src.join("Miri/ScopedExt.lean");
    let miri_out = vendor_lib.join("Miri/ScopedExt.olean");
    fs::create_dir_all(miri_src.parent().unwrap()).unwrap();
    fs::create_dir_all(miri_out.parent().unwrap()).unwrap();
    fs::write(
        &miri_src,
        "import Lean.PostprocessTraces\n\
         namespace Miri.ScopedSyntax\n\
         scoped syntax \"sneaky_term\" : term\n\
         scoped macro_rules | `(sneaky_term) => `(0)\n\
         end Miri.ScopedSyntax\n\
         namespace Miri.ScopedOuter\n\
         def helper : Nat := 1\n\
         namespace ScopedInner\n\
         scoped syntax \"nested_term\" : term\n\
         scoped macro_rules | `(nested_term) => `(2)\n\
         end ScopedInner\n\
         end Miri.ScopedOuter\n",
    )
    .unwrap();
    checker
        .process(
            "compile-Miri.ScopedExt",
            &[
                "-j1".to_string(),
                "-M4096".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                miri_out.to_string_lossy().into_owned(),
                miri_src.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();

    let src_dir = checker.stage().join("src/scoped-tests");
    fs::create_dir_all(src_dir.join("Anneal")).unwrap();
    fs::create_dir_all(src_dir.join("Trusted")).unwrap();

    let trusted_base_src = checker.modules()["Trusted"].clone();
    let run_corr_pf = |chk: &mut Checker, module: &str, path: &Path| {
        chk.inspect(InspectorRequest::CorrespondencePreflight {
            search_path: vec![trusted_lib.clone(), theory_lib.clone(), vendor_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            theory: vec!["Anneal".to_string(), "Anneal.DecoyNs".to_string()],
            vendor_miri: vec!["Miri.ScopedExt".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![(module.to_string(), path.to_path_buf())],
        })
    };

    let cases: &[(&str, &str, &str, &str)] = &[
        (
            "Anneal.ScopedOpen",
            "Anneal/ScopedOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             open Miri.ScopedSyntax\n\
             def f : Nat := sneaky_term\n",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            "Trusted.ScopedOpen",
            "Trusted/ScopedOpen.lean",
            "-- anneal-trust-tier: candidate:mir_semantics\n\
             prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             open Miri.ScopedSyntax\n\
             def f : Nat := sneaky_term\n",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            "Anneal.ScopedOpenIn",
            "Anneal/ScopedOpenIn.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             open Miri.ScopedSyntax in\n\
             def f : Nat := 0\n",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            "Anneal.ScopedNamespace",
            "Anneal/ScopedNamespace.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Miri.ScopedSyntax\n\
             def f : Nat := sneaky_term\n\
             end Miri.ScopedSyntax\n",
            "cannot enter namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            "Anneal.ScopedRelativeOpen",
            "Anneal/ScopedRelativeOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             open Miri.ScopedOuter\n\
             open ScopedInner\n\
             def f : Nat := nested_term\n",
            "cannot open namespace Miri.ScopedOuter.ScopedInner with scoped syntax or extensions",
        ),
        (
            "Anneal.ScopedNestedNsOpen",
            "Anneal/ScopedNestedNsOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Miri.ScopedOuter\n\
             open ScopedInner\n\
             def f : Nat := nested_term\n\
             end Miri.ScopedOuter\n",
            "cannot open namespace Miri.ScopedOuter.ScopedInner with scoped syntax or extensions",
        ),
        (
            "Anneal.ScopedDeclPrefix",
            "Anneal/ScopedDeclPrefix.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             def Miri.ScopedSyntax.sneaky : Nat := sneaky_term\n",
            "cannot declare in namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            "Anneal.ScopedMutualOpen",
            "Anneal/ScopedMutualOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             mutual\n\
             open Miri.ScopedSyntax\n\
             def f : Nat := sneaky_term\n\
             end\n",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            "Anneal.ScopedListOpen",
            "Anneal/ScopedListOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             open List\n\
             def f : Nat := 0\n",
            "cannot open namespace List with scoped syntax or extensions",
        ),
        (
            "Anneal.BadEndScope",
            "Anneal/BadEndScope.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Foo\n\
             end Bar\n",
            "mismatched `end Bar`",
        ),
        // Decoy-namespace shadowing regressions: `Anneal.DecoyNs` is loaded in
        // the union parser environment (without being imported here), declaring
        // unscoped `Anneal.Miri.ScopedSyntax`, `Anneal.Miri`, and
        // `Anneal.Lean.PostprocessTraces`. Preflight must check all candidate
        // resolutions and reject every real scoped target.
        (
            "Anneal.DecoyScopedOpen",
            "Anneal/DecoyScopedOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Anneal\n\
             open Miri.ScopedSyntax\n\
             def f : Nat := sneaky_term\n\
             end Anneal\n",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            "Anneal.DecoyScopedOpenIn",
            "Anneal/DecoyScopedOpenIn.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Anneal\n\
             open Miri.ScopedSyntax in\n\
             def f : Nat := 0\n\
             end Anneal\n",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            "Anneal.DecoyChainedOpen",
            "Anneal/DecoyChainedOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Anneal\n\
             open Miri\n\
             open ScopedSyntax\n\
             def f : Nat := sneaky_term\n\
             end Anneal\n",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            "Anneal.DecoySameCmdChainedOpen",
            "Anneal/DecoySameCmdChainedOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Anneal\n\
             open Miri ScopedSyntax\n\
             def f : Nat := sneaky_term\n\
             end Anneal\n",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            "Anneal.DecoyLeanPostprocessTraces",
            "Anneal/DecoyLeanPostprocessTraces.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Anneal\n\
             open Lean.PostprocessTraces\n\
             def f : Nat := 0\n\
             end Anneal\n",
            "cannot open namespace Lean.PostprocessTraces with scoped syntax or extensions",
        ),
        (
            "Anneal.ChainedExportScopedOpen",
            "Anneal/ChainedExportScopedOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Anneal\n\
             export Miri (ScopedOuter)\n\
             open ScopedOuter.ScopedInner\n\
             def f : Nat := 0\n\
             end Anneal\n",
            "cannot open namespace Miri.ScopedOuter.ScopedInner with scoped syntax or extensions",
        ),
        (
            "Anneal.ChainedExportInScopedOpen",
            "Anneal/ChainedExportInScopedOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Anneal\n\
             export Miri (ScopedOuter)\n\
             open ScopedOuter.ScopedInner in\n\
             def f : Nat := 0\n\
             end Anneal\n",
            "cannot open namespace Miri.ScopedOuter.ScopedInner with scoped syntax or extensions",
        ),
        (
            "Anneal.ChainedExportMutualScopedOpen",
            "Anneal/ChainedExportMutualScopedOpen.lean",
            "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
             namespace Anneal\n\
             mutual\n\
             export Miri (ScopedOuter)\n\
             open ScopedOuter.ScopedInner\n\
             end\n\
             end Anneal\n",
            "cannot open namespace Miri.ScopedOuter.ScopedInner with scoped syntax or extensions",
        ),
    ];

    for (module, rel, body, expected_msg) in cases {
        let path = src_dir.join(rel);
        fs::write(&path, body).unwrap();
        let err = run_corr_pf(&mut checker, module, &path).unwrap_err();
        assert_eq!(err.code, 1, "expected policy exit 1 for {module}: {err}");
        assert_eq!(err.phase, "correspondence-preflight");
        assert!(
            err.message.contains(expected_msg),
            "expected `{expected_msg}` for {module}, got: {err}"
        );
    }

    // Benign lexical scopes (`namespace`, `section`, `end`, and `open` of a
    // namespace without scoped extensions) pass `"correspondence-preflight"`.
    let benign = src_dir.join("Anneal/BenignScopes.lean");
    fs::write(
        &benign,
        "prelude\nimport Init.Core\nimport Miri.ScopedExt\n\
         namespace Anneal.BenignScopes\n\
         section Helper\n\
         open Miri.ScopedOuter\n\
         def ok : Nat := helper\n\
         end Helper\n\
         end Anneal.BenignScopes\n",
    )
    .unwrap();
    run_corr_pf(&mut checker, "Anneal.BenignScopes", &benign)
        .expect("benign lexical scopes must pass correspondence-preflight");
}

/// End-to-end negative test of the production Pass 2 pipeline in
/// [`Checker::run_correspondence_with_closure`] (invoked by [`Checker::run`]):
/// verifies that the production `"correspondence-preflight"` call site rejects
/// compilable Pass 2 proof files using unscoped `Lean` syntax (`m! "x"`) or
/// opening a synthetic vendor scoped-syntax namespace
/// (`open Miri.ScopedSyntax`) with `code == 1`,
/// `phase == "correspondence-preflight"` BEFORE compiling any Pass 2 module
/// (`Trusted/Correspondence.olean` and `Anneal/MirCorrespondenceProof.olean`
/// are never produced). It also verifies that the Pass 2 foundation
/// `"preflight"` call site rejects the Pass 1 `theory/` `local semireducible`
/// exception with `phase == "preflight"`.
#[test]
fn rejects_pass2_syntax_and_scoped_extensions_in_run_correspondence_pipeline() {
    let fix = TempFixture::new(None);
    // Include an unimported Pass 1 `theory/` decoy module declaring unscoped
    // namespaces that shadow real scoped namespaces inside `namespace Anneal`.
    let decoy_path = fix.root.join("theory/Anneal/DecoyNs.lean");
    fs::create_dir_all(decoy_path.parent().unwrap()).unwrap();
    fs::write(fix.root.join("theory/Anneal.lean"), "prelude\nimport Init.Core\n").unwrap();
    fs::write(
        &decoy_path,
        "prelude\nimport Init.Core\n\
         namespace Anneal.Miri.ScopedSyntax\n\
         def decoy : Nat := 0\n\
         end Anneal.Miri.ScopedSyntax\n\
         namespace Anneal.Miri\n\
         def decoyMiri : Nat := 0\n\
         end Anneal.Miri\n\
         namespace Anneal.Lean.PostprocessTraces\n\
         def decoyTraces : Nat := 0\n\
         end Anneal.Lean.PostprocessTraces\n",
    )
    .unwrap();
    let vendor_dir = fix.root.join("synthetic-miri");
    let miri_rel = "Miri/ImportLean.lean";
    let miri_src_path = vendor_dir.join(miri_rel);
    fs::create_dir_all(miri_src_path.parent().unwrap()).unwrap();
    let miri_src = "import Lean.PostprocessTraces\n\
                    namespace Miri.ScopedSyntax\n\
                    scoped syntax \"sneaky_macro\" : term\n\
                    scoped macro_rules | `(sneaky_macro) => `(0)\n\
                    end Miri.ScopedSyntax\n\
                    namespace Miri.ImportLean\n\
                    abbrev Msg := Lean.MessageData\n\
                    def ok : Nat := 0\n\
                    end Miri.ImportLean\n";
    fs::write(&miri_src_path, miri_src).unwrap();
    let expected_sources =
        BTreeMap::from([(miri_rel.to_string(), sha256_bytes(miri_src.as_bytes()))]);

    // Compile `Miri.ImportLean` once in a probe checker to record its
    // deterministic `.olean` companion digests.
    let mut probe = fix.checker();
    probe.set_require_mir_wp(false);
    probe.run().unwrap();
    probe.ensure_sysroot_foundation().unwrap();
    let probe_out = probe.stage().join("probe-lib/Miri/ImportLean.olean");
    fs::create_dir_all(probe_out.parent().unwrap()).unwrap();
    probe
        .process(
            "probe-Miri.ImportLean",
            &[
                "-j1".to_string(),
                "-M4096".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_out.to_string_lossy().into_owned(),
                miri_src_path.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let probe_server = probe.stage().join("probe-lib/Miri/ImportLean.olean.server");
    let probe_private = probe.stage().join("probe-lib/Miri/ImportLean.olean.private");
    let miri_entry = MiriClosureEntry {
        module: "Miri.ImportLean".to_string(),
        path: miri_rel.to_string(),
        olean_sha256: sha256_file(&probe_out, "test").unwrap(),
        olean_server_sha256: probe_server
            .exists()
            .then(|| sha256_file(&probe_server, "test").unwrap()),
        olean_private_sha256: probe_private
            .exists()
            .then(|| sha256_file(&probe_private, "test").unwrap()),
    };

    let base_tiers = BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]);
    let corr_trusted_path = fix.root.join("trusted/correspondence/Trusted/Correspondence.lean");
    let corr_proof_path = fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean");

    let e2e_cases: &[(&str, &str, &str)] = &[
        (
            // Valid compilable `Miri.ImportLean.Msg` (`Lean.MessageData`) term
            // using `m!`: passes foundation preflight as an identifier/app, so
            // dropping `"correspondence-preflight"` would compile both Pass 2
            // modules.
            "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
             import Trusted.Correspondence\n\
             namespace Anneal.MirCorrespondenceProof\n\
             def f : Miri.ImportLean.Msg := m! \"x\"\n\
             end Anneal.MirCorrespondenceProof\n",
            "correspondence-preflight",
            "unsupported syntax kind Lean.termM!_",
        ),
        (
            // Valid compilable use of synthetic vendor scoped macro: passes
            // foundation preflight and would compile cleanly if
            // `"correspondence-preflight"` did not block scoped namespaces.
            "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
             import Trusted.Correspondence\n\
             open Miri.ScopedSyntax\n\
             namespace Anneal.MirCorrespondenceProof\n\
             def f : Nat := sneaky_macro\n\
             end Anneal.MirCorrespondenceProof\n",
            "correspondence-preflight",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            // Decoy-namespace shadowing attack (1-step): `Anneal.DecoyNs`
            // declares unscoped `Anneal.Miri.ScopedSyntax` in Pass 1 `theory/`
            // (not imported here). Under `namespace Anneal`, `lean` resolves
            // `open Miri.ScopedSyntax` to the real scoped namespace and would
            // expand `sneaky_macro`. Preflight must reject all candidates.
            "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
             import Trusted.Correspondence\n\
             namespace Anneal\n\
             open Miri.ScopedSyntax\n\
             def f : Nat := sneaky_macro\n\
             end Anneal\n",
            "correspondence-preflight",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            // Decoy-namespace shadowing attack (2-step chain): `Anneal.DecoyNs`
            // declares unscoped `Anneal.Miri` (not imported here). Opening
            // `Miri` then `ScopedSyntax` inside `namespace Anneal` must still
            // track real `Miri` and reject `Miri.ScopedSyntax`.
            "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
             import Trusted.Correspondence\n\
             namespace Anneal\n\
             open Miri\n\
             open ScopedSyntax\n\
             def f : Nat := sneaky_macro\n\
             end Anneal\n",
            "correspondence-preflight",
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            // Opening sysroot `Lean.PostprocessTraces` under `namespace Anneal`
            // (with decoy `Anneal.Lean.PostprocessTraces` in Pass 1 `theory/`)
            // is rejected during foundation `"preflight"` by the root `Lean.*`
            // namespace ban before Pass 2 compilation begins; direct
            // `"correspondence-preflight"` scoped-namespace precedence is
            // covered by `rejects_scoped_syntax_and_extensions_in_preflight`.
            "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
             import Trusted.Correspondence\n\
             namespace Anneal\n\
             open Lean.PostprocessTraces\n\
             def f : Nat := 0\n\
             end Anneal\n",
            "preflight",
            "cannot open forbidden namespace Lean.PostprocessTraces",
        ),
        (
            // Pass 2 sends foundation `"preflight"` without
            // `allow_local_semireducible`, so the Pass 1 `theory/` exception is
            // rejected there, before `"correspondence-preflight"` runs.
            "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
             import Trusted.Correspondence\n\
             attribute [local semireducible] _root_.Nat.bitwise in\n\
             def f : Nat := 0\n",
            "preflight",
            "only `open` and `variable` commands are permitted on the LHS of `in`",
        ),
    ];

    for (proof_src, expected_phase, expected_msg) in e2e_cases {
        // Run Pass 1 cleanly before placing Pass 2 directories in the checkout.
        let _ = fs::remove_dir_all(fix.root.join("trusted/correspondence"));
        let _ = fs::remove_dir_all(fix.root.join("correspondence"));
        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        checker.run().unwrap();

        fs::create_dir_all(corr_trusted_path.parent().unwrap()).unwrap();
        fs::create_dir_all(corr_proof_path.parent().unwrap()).unwrap();
        fs::write(
            &corr_trusted_path,
            "-- anneal-trust-tier: candidate:mir_semantics\n\
             prelude\nimport Init.Core\nimport Miri.ImportLean\n\
             namespace Trusted.Correspondence\n\
             def ok : Nat := Miri.ImportLean.ok\n\
             end Trusted.Correspondence\n",
        )
        .unwrap();
        fs::write(&corr_proof_path, proof_src).unwrap();

        let err = checker
            .run_correspondence_with_closure(
                &base_tiers,
                &vendor_dir,
                "synthetic-commit",
                std::slice::from_ref(&miri_entry),
                &expected_sources,
            )
            .unwrap_err();
        assert_eq!(err.code, 1, "expected policy exit 1: {err}");
        assert_eq!(err.phase, *expected_phase, "unexpected phase for error: {err}");
        assert!(err.message.contains(expected_msg), "expected `{expected_msg}`, got: {err}");
        assert!(
            !checker.stage().join("lib/Trusted/Correspondence.olean").exists(),
            "Pass 2 Trusted.Correspondence must not compile before correspondence-preflight"
        );
        assert!(
            !checker.stage().join("theory-lib/Anneal/MirCorrespondenceProof.olean").exists(),
            "Pass 2 Anneal.MirCorrespondenceProof must not compile before correspondence-preflight"
        );
    }
}
