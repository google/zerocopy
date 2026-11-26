// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for the `trusted/audit` repository boundary gate and
//! `TrustedBoundary.lean` kernel-environment inspector.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    env, fs,
    os::unix::fs::symlink,
    path::{Path, PathBuf},
    process::Command,
};

use anneal_audit::{
    CandidateFeature, Checker, ImportEdge, InspectorRequest, Json, MiriClosureEntry,
    ModuleArtifacts, PARTS, TrustTier, bundle, check_cargo_boundary, default_lean_path,
    ensure_miri_cache_outside_checkout, scan_lean_tree, sha256_bytes, sha256_file,
    verify_sysroot_foundation_dir,
};
use anneal_testkit::mir_wp_fixture::MirWpFixtureSpec;
use serde_json::json;

mod common;
use common::{
    HEADER, TempFixture, compile_forged_module, copy_cargo_workspace, copy_dir_all,
    correspondence_dsl::{
        ClaimsSpec, CorrAuditRequestBuilder, CorrespondenceHarness, ProofsSpec,
        REQUIRED_MIRI_PRIMITIVES, VALID_BYTES_CODEC_DEF, VALID_D11_DEF, VALID_D12_DEF,
        VALID_D13_DEF, assert_policy_rejection,
    },
    repo_root, run_lean_script,
};
/// Verifies that an empty `Trusted.lean` importing only locked `Init.*`
/// modules passes tool admission, preflight, compilation, and foundation
/// kernel replay with zero `Trusted` declarations and zero reached axioms.
#[test]
fn audits_empty_inventory_and_foundation_replay() {
    let mut fix = TempFixture::new(Some(HEADER));
    let rep = fix.check_expected(None, None, None).unwrap();
    assert_eq!(rep.get("kernelDeclarations").and_then(Json::as_i64), Some(0));
    assert_eq!(rep.get("axioms"), Some(&json!([])));
    assert_eq!(rep.get("replay"), Some(&json!(true)));
    assert_eq!(rep.get("vettedModules"), Some(&json!(["Trusted"])));
    assert_eq!(rep.get("candidateFeatures"), Some(&json!({})));
}

/// Verifies that `tests/fixtures/positive.lean` passes under hostile
/// `LEAN_PATH` and `LEAN_SYSROOT` environment variables pointing at corrupt
/// `.olean` files, and that `private` helpers, `opaque` definitions, recursors,
/// typeclass instances, and coercions are all recorded in the dependency
/// closure.
#[test]
fn audits_positive_fixture_under_hostile_ambient_paths() {
    let positive_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/positive.lean");
    let positive = fs::read_to_string(positive_path).unwrap();
    let fix = TempFixture::new(Some(&positive));
    let stale = fix.root.join("stale");
    fs::create_dir_all(&stale).unwrap();
    fs::write(stale.join("Trusted.olean"), b"not an olean").unwrap();

    let mut hostile_env: Vec<(String, String)> = env::vars().collect();
    hostile_env.push(("LEAN_PATH".to_string(), stale.to_string_lossy().into_owned()));
    hostile_env.push(("LEAN_SYSROOT".to_string(), stale.to_string_lossy().into_owned()));
    let mut checker = Checker::new_with_env(&fix.root, None, hostile_env).unwrap();
    checker.set_require_mir_wp(false);
    let rep = checker.run().unwrap();

    let decls = rep.get("declarations").and_then(Json::as_array).unwrap();
    let k_decls = rep.get("kernelDeclarations").and_then(Json::as_i64).unwrap();
    assert_eq!(k_decls, decls.len() as i64);
    assert!(decls.len() > 30);

    let mut decl_map: BTreeMap<String, &Json> = BTreeMap::new();
    for d in decls {
        let name = d.get("name").and_then(Json::as_str).unwrap().to_string();
        decl_map.insert(name, d);
    }
    let helper = decl_map
        .keys()
        .find(|n| n.starts_with("_private.") && n.ends_with(".Outside.helper"))
        .expect("missing private helper")
        .clone();
    let sealed_deps: BTreeSet<&str> = decl_map["Outside.sealed"]
        .get("dependencies")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    assert!(sealed_deps.contains(helper.as_str()));
    assert_eq!(decl_map["Outside.sealed"].get("kind").and_then(Json::as_str), Some("opaque"));
    assert!(decl_map.contains_key("Outside.Box.rec"));
    assert!(decl_map.contains_key("Outside.Indexed.rec"));
    assert!(decl_map.keys().any(|n| n.starts_with("Outside.Tree")));

    let inferred_deps: Vec<&str> = decl_map["Outside.inferred"]
        .get("dependencies")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    let coerced_deps: BTreeSet<&str> = decl_map["Outside.coerced"]
        .get("dependencies")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    let axioms: BTreeSet<&str> = rep
        .get("axioms")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .filter_map(Json::as_str)
        .collect();
    let expected_axioms: BTreeSet<&str> =
        ["Classical.choice", "Quot.sound", "propext"].into_iter().collect();
    assert!(inferred_deps.iter().any(|n| n.contains("instWrap")));
    assert!(coerced_deps.contains("Outside.Box.value"));
    assert!(decl_map.keys().any(|n| n.contains("instCoe")));
    assert!(decl_map.values().all(|d| d.get("module").and_then(Json::as_str) == Some("Trusted")));
    assert_eq!(axioms, expected_axioms);
}

/// Verifies that adding an `Init.*` module to `foundation-lock.json` is
/// sufficient to admit that module and track its typeclass instances in
/// dependency closures without modifying `audit.rs` or `TrustedBoundary.lean`.
#[test]
fn admits_lock_only_foundation_growth() {
    let src = format!(
        "{HEADER}import Init.Data.PLift\ndef usesExtra (x : PLift Nat) : Bool := decide (x = x)\n"
    );
    let mut fix = TempFixture::new(Some(&src));
    let lock_path = fix.root.join("trusted/lean/foundation-lock.json");
    let mut lock: Json = serde_json::from_str(&fs::read_to_string(&lock_path).unwrap()).unwrap();
    let extra = "Init.Data.PLift";
    lock["modules"].as_object_mut().unwrap().remove(extra);
    lock["graph"].as_object_mut().unwrap().remove(extra);
    fs::write(&lock_path, serde_json::to_vec(&lock).unwrap()).unwrap();
    let _ = fix.check_expected(Some(1), Some("preflight"), Some(false));

    let lean_exec = fs::canonicalize(default_lean_path()).unwrap();
    let prefix = lean_exec.parent().unwrap().parent().unwrap();
    let mut extra_parts = serde_json::Map::new();
    for part in PARTS {
        let p = prefix.join("lib/lean").join(format!("Init/Data/PLift.{part}"));
        if p.exists() {
            let digest = sha256_file(&p, "foundation").unwrap();
            extra_parts.insert(part.to_string(), json!(digest));
        } else {
            extra_parts.insert(part.to_string(), Json::Null);
        }
    }
    let src_digest =
        sha256_file(&prefix.join("src/lean/Init/Data/PLift.lean"), "foundation").unwrap();
    lock["modules"][extra] = json!({
        "sourceSha256": src_digest,
        "parts": extra_parts,
    });
    lock["graph"][extra] = json!([{
        "module": "Init.Core",
        "importAll": false,
        "isExported": true,
        "isMeta": false,
    }]);
    fs::write(&lock_path, serde_json::to_vec(&lock).unwrap()).unwrap();

    let rep = fix.check_expected(None, None, None).unwrap();
    let has_plift = rep
        .get("declarations")
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .find(|d| d.get("name").and_then(Json::as_str) == Some("usesExtra"))
        .and_then(|d| d.get("dependencies"))
        .and_then(Json::as_array)
        .unwrap()
        .iter()
        .any(|x| x.as_str() == Some("instDecidableEqPLift"));
    assert!(rep.get("graph").and_then(Json::as_object).unwrap().contains_key(extra));
    assert!(has_plift);
}

/// Verifies that Phase 1 (`"preflight"`) rejects forbidden headers, imports,
/// commands (`#eval`), terms (`unsafe`, `by_elab`), tactics (`native_decide`,
/// `decide +native`), attributes (`@[extern]`, `@[implemented_by]`), and
/// invalid or missing `-- anneal-trust-tier:` directives before Lean ever
/// compiles or executes the file (`execution_began == false`).
#[test]
fn rejects_forbidden_syntax_and_attributes_without_executing_eval() {
    let base_fix = TempFixture::new(None);
    let sentinel = base_fix.root.join("must-not-exist");
    let eval_sentinel_src =
        format!("{HEADER}#eval IO.FS.writeFile \"{}\" \"executed\"\n", sentinel.display());

    let full_run_negatives: Vec<(&str, String)> = vec![
        (
            "implicit default Init",
            "-- anneal-trust-tier: vetted\nimport Init.Core\ndef x : Nat := 0\n".to_string(),
        ),
        (
            "foreign namespace spoof",
            format!("{HEADER}import Foreign\nnamespace Trusted\ndef x : Nat := 0\nend Trusted\n"),
        ),
        ("Std import", "-- anneal-trust-tier: vetted\nprelude\nimport Std\n".to_string()),
        ("evaluation sentinel", eval_sentinel_src),
    ];

    for (_label, src) in &full_run_negatives {
        let mut f = TempFixture::new(Some(src));
        let _ = f.check_expected(Some(1), Some("preflight"), Some(false));
        assert!(!sentinel.exists(), "evaluation sentinel executed!");
    }

    let inspector_negatives: Vec<(&str, String)> = vec![
        (
            "trusted import all",
            "-- anneal-trust-tier: vetted\nmodule\nprelude\nimport all Init.Data.Nat.Bitwise.Basic\n"
                .to_string(),
        ),
        (
            "module meta import",
            "-- anneal-trust-tier: vetted\nmodule\nprelude\nmeta import Init.Core\n"
                .to_string(),
        ),
        (
            "module meta section",
            "-- anneal-trust-tier: vetted\nmodule\nprelude\npublic import Init.Core\nmeta section\nend\n"
                .to_string(),
        ),
        (
            "module noncomputable section",
            "-- anneal-trust-tier: vetted\nmodule\nprelude\npublic import Init.Core\nnoncomputable section\nend\n"
                .to_string(),
        ),
        (
            "direct meta import",
            "-- anneal-trust-tier: vetted\nprelude\nmeta import Init.Core\n"
                .to_string(),
        ),
        (
            "direct all import",
            "-- anneal-trust-tier: vetted\nprelude\nimport all Init.Core\n"
                .to_string(),
        ),
        (
            "public import",
            "-- anneal-trust-tier: vetted\nprelude\npublic import Init.Core\n"
                .to_string(),
        ),
        (
            "nested unsafe",
            format!("{HEADER}open Nat in\nunsafe def x : Nat := 0\n"),
        ),
        (
            "term unsafe generated hook",
            format!("{HEADER}def generatedUnsafe : Nat := unsafe 0\n"),
        ),
        (
            "mutual unsafe",
            format!("{HEADER}mutual\n unsafe def x : Nat := 0\nend\n"),
        ),
        (
            "nested forbidden command",
            format!("{HEADER}open Nat in\n#eval 0\n"),
        ),
        (
            "nested attribute",
            format!(
                "{HEADER}structure X where\n @[extern \"foreign\"] x : Nat\n"
            ),
        ),
        (
            "implemented_by",
            format!("{HEADER}@[implemented_by other] def x : Nat := 0\n"),
        ),
        (
            "attribute removal",
            format!("{HEADER}attribute [-extern] Nat.add\n"),
        ),
        (
            "deriving",
            format!("{HEADER}structure X where\n x : Nat\nderiving Repr\n"),
        ),
        ("open scoped", format!("{HEADER}open scoped Nat\n")),
        (
            "set_option wrapper",
            format!(
                "{HEADER}set_option debug.skipKernelTC true in\ndef x : Nat := 0\n"
            ),
        ),
        ("custom macro", format!("{HEADER}macro \"x\" : term => `(0)\n")),
        (
            "native shortcut",
            format!("{HEADER}theorem x : True := by native_decide\n"),
        ),
        (
            "native decide config",
            format!("{HEADER}theorem x : True := by decide +native\n"),
        ),
        (
            "by_elab",
            format!(
                "{HEADER}def x : Nat := by_elab return Lean.mkNatLit 0\n"
            ),
        ),
        (
            "missing module trust tier",
            "prelude\nimport Init.NotationExtra\ndef x : Nat := 0\n"
                .to_string(),
        ),
        (
            "unknown candidate feature",
            "-- anneal-trust-tier: candidate:nonexistent\nprelude\nimport Init.NotationExtra\n"
                .to_string(),
        ),
        (
            "multiple module trust tiers",
            "-- anneal-trust-tier: vetted\n-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\n"
                .to_string(),
        ),
        (
            "invalid module trust tier",
            "-- anneal-trust-tier: bogus\nprelude\nimport Init.NotationExtra\n"
                .to_string(),
        ),
        (
            "legacy declaration trust attribute",
            format!("{HEADER}@[vetted] def x : Nat := 0\n"),
        ),
        ("malformed recovery", format!("{HEADER}def broken : :=\n")),
        (
            "decide +kernel",
            format!("{HEADER}theorem x : True := by decide +kernel\n"),
        ),
        ("decideBang", format!("{HEADER}theorem x : True := by decide!\n")),
        (
            "bv_decide",
            format!("{HEADER}theorem x : True := by bv_decide\n"),
        ),
        ("rfl'", format!("{HEADER}theorem x : True := by rfl'\n")),
        (
            "grind set_option",
            format!(
                "{HEADER}theorem x : True := by grind => set_option debug.skipKernelTC true\n"
            ),
        ),
        (
            "include_str",
            format!(
                "{HEADER}def x : String := include_str \"Trusted.lean\"\n"
            ),
        ),
        (
            "noncomputable section",
            format!("{HEADER}noncomputable section\n"),
        ),
        (
            "_root_ escape",
            format!(
                "{HEADER}namespace Trusted\ndef _root_.Spoof : Nat := 0\nend Trusted\n"
            ),
        ),
        (
            "section inside in-command",
            format!("{HEADER}section S in\ndef x : Nat := 0\n"),
        ),
        (
            "namespace inside in-command",
            format!("{HEADER}namespace A in\ndef x : Nat := 0\n"),
        ),
        (
            "with_decl_name% term",
            format!("{HEADER}def f : Nat := with_decl_name% Foo 0\n"),
        ),
        (
            "private_decl% term",
            format!("{HEADER}def f : Name := private_decl% f\n"),
        ),
        (
            "decl_name% term",
            format!("{HEADER}def f : Name := decl_name%\n"),
        ),
        (
            "namespace on RHS of in-command",
            format!("{HEADER}open Nat in\nnamespace A\n"),
        ),
        (
            "empty French-quote identifier",
            format!("{HEADER}def «» : Nat := 0\n"),
        ),
        (
            "tactic block in Trusted module",
            format!("{HEADER}theorem x : Eq 0 0 := by rfl\n"),
        ),
    ];

    let mut checker = base_fix.checker();
    checker.tool_admission().unwrap();
    for (idx, (label, src)) in inspector_negatives.iter().enumerate() {
        let neg_path = checker.stage().join(format!("neg-{idx}.lean"));
        fs::write(&neg_path, src.as_bytes()).unwrap();
        let err = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Trusted".to_string(), neg_path)],
                base_trusted_sources: Vec::new(),
            })
            .expect_err(&format!("expected preflight rejection for {label}"));
        assert_eq!(err.code, 1, "unexpected code for {label}: {err}");
    }

    // Verify that `SourceRole.theory` (`Anneal`) admits allowed tactics (`by
    // rfl`) while still rejecting disallowed tactics and tactic configurations
    // (`native_decide`, `decide +native`, `decide +kernel`, `decide!`,
    // `bv_decide`, `rfl'`, `grind`, `sorry`).
    let theory_header = "prelude\nimport Init.NotationExtra\n";
    let theory_pos_path = checker.stage().join("theory-pos.lean");
    fs::write(
        &theory_pos_path,
        format!("{theory_header}theorem ok : Eq 0 0 := by rfl\n").as_bytes(),
    )
    .unwrap();
    checker
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Anneal".to_string(), theory_pos_path)],
            base_trusted_sources: Vec::new(),
        })
        .expect("expected theory module with `by rfl` to pass preflight");

    let theory_negatives: Vec<(&str, String)> = vec![
        ("theory native_decide", format!("{theory_header}theorem x : True := by native_decide\n")),
        (
            "theory decide +native",
            format!("{theory_header}theorem x : True := by decide +native\n"),
        ),
        (
            "theory decide +kernel",
            format!("{theory_header}theorem x : True := by decide +kernel\n"),
        ),
        ("theory decideBang", format!("{theory_header}theorem x : True := by decide!\n")),
        ("theory bv_decide", format!("{theory_header}theorem x : True := by bv_decide\n")),
        ("theory rfl'", format!("{theory_header}theorem x : True := by rfl'\n")),
        (
            "theory grind set_option",
            format!(
                "{theory_header}theorem x : True := by grind => set_option debug.skipKernelTC true\n"
            ),
        ),
        ("theory by sorry", format!("{theory_header}theorem x : False := by sorry\n")),
        ("theory term sorry", format!("{theory_header}theorem x : False := sorry\n")),
    ];
    for (idx, (label, src)) in theory_negatives.iter().enumerate() {
        let neg_path = checker.stage().join(format!("theory-neg-{idx}.lean"));
        fs::write(&neg_path, src.as_bytes()).unwrap();
        let err = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Anneal".to_string(), neg_path)],
                base_trusted_sources: Vec::new(),
            })
            .expect_err(&format!("expected preflight rejection for {label}"));
        assert_eq!(err.code, 1, "unexpected code for {label}: {err}");
    }
}

/// Verifies that `"preflight"` rejects surface `sorry` syntax before
/// compilation (`execution_began == false`), and that Phase 2 (`"audit"`)
/// rejects direct `sorryAx` applications (which use only allowed function
/// application syntax, so they reach Phase 2 where `sorryAx` is excluded from
/// `foundation-lock.json`'s axiom allowlist), both in `Trusted.lean` and in an
/// unimported `Trusted/Unused.lean` module discovered by `scan_lean_tree`.
#[test]
fn rejects_sorry_and_unreferenced_module_with_sorry() {
    let mut f_sorry = TempFixture::new(Some(&format!("{HEADER}theorem bad : False := by sorry\n")));
    let _ = f_sorry.check_expected(Some(1), Some("preflight"), Some(false));

    let mut f_sorry_ax =
        TempFixture::new(Some(&format!("{HEADER}theorem bad : False := sorryAx False true\n")));
    let _ = f_sorry_ax.check_expected(Some(1), Some("audit"), Some(true));

    let mut f_unused = TempFixture::new(None);
    fs::create_dir_all(f_unused.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_unused.root.join("trusted/lean/Trusted/Unused.lean"),
        format!("{HEADER}theorem unreferenced : False := sorryAx False true\n").as_bytes(),
    )
    .unwrap();
    let _ = f_unused.check_expected(Some(1), Some("audit"), Some(true));
}

/// Verifies that cyclic imports between modules are rejected during
/// `"preflight"` before compilation begins.
#[test]
fn rejects_source_import_cycles() {
    let mut fix = TempFixture::new(Some(&format!("{HEADER}import Trusted.Other\n")));
    fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix.root.join("trusted/lean/Trusted/Other.lean"),
        format!("{HEADER}import Trusted\n").as_bytes(),
    )
    .unwrap();
    let _ = fix.check_expected(Some(1), Some("preflight"), Some(false));
}

/// Verifies that `scan_lean_tree` rejects symlinks and pre-existing `.olean`
/// artifacts in the source tree, and `tool_admission` rejects `Init.*`
/// companion files on disk that are marked `null` in `foundation-lock.json`.
#[test]
fn rejects_symlinks_stale_oleans_and_unexpected_foundation_companions() {
    let mut f_sym = TempFixture::new(None);
    symlink(
        f_sym.root.join("trusted/lean/Trusted.lean"),
        f_sym.root.join("trusted/lean/Alias.lean"),
    )
    .unwrap();
    let _ = f_sym.check_expected(Some(1), Some("snapshot"), Some(false));

    let mut f_stale = TempFixture::new(None);
    fs::write(f_stale.root.join("trusted/lean/Trusted.olean"), b"stale").unwrap();
    let _ = f_stale.check_expected(Some(1), Some("snapshot"), Some(false));

    let mut f_companion = TempFixture::new(None);
    let lp = f_companion.root.join("trusted/lean/foundation-lock.json");
    let mut l: Json = serde_json::from_str(&fs::read_to_string(&lp).unwrap()).unwrap();
    l["modules"]["Init.Prelude"]["parts"]["olean.private"] = Json::Null;
    fs::write(&lp, serde_json::to_vec(&l).unwrap()).unwrap();
    let _ = f_companion.check_expected(Some(2), Some("foundation"), Some(false));

    let mut f_bad_sha = TempFixture::new(None);
    let lp_sha = f_bad_sha.root.join("trusted/lean/foundation-lock.json");
    let mut l_sha: Json = serde_json::from_str(&fs::read_to_string(&lp_sha).unwrap()).unwrap();
    l_sha["modules"]["Init.Prelude"]["parts"]["olean"] =
        json!("0000000000000000000000000000000000000000000000000000000000000000");
    fs::write(&lp_sha, serde_json::to_vec(&l_sha).unwrap()).unwrap();
    let err_sha = f_bad_sha.check_expected(Some(2), Some("foundation"), Some(false)).unwrap_err();
    assert!(
        err_sha.message.contains("foundation artifact SHA-256 mismatch for Init/Prelude.olean"),
        "unexpected error: {err_sha}"
    );

    let mut f_missing_root = TempFixture::new(None);
    fs::remove_file(f_missing_root.root.join("trusted/lean/Trusted.lean")).unwrap();
    fs::create_dir_all(f_missing_root.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(f_missing_root.root.join("trusted/lean/Trusted/Sub.lean"), HEADER.as_bytes())
        .unwrap();
    let err_missing_root =
        f_missing_root.check_expected(Some(1), Some("snapshot"), Some(false)).unwrap_err();
    assert!(
        err_missing_root.message.contains("missing Trusted.lean umbrella"),
        "unexpected error: {err_missing_root}"
    );

    let mut f_non_lean = TempFixture::new(None);
    fs::write(f_non_lean.root.join("trusted/lean/notes.txt"), b"unexpected").unwrap();
    let err_non_lean =
        f_non_lean.check_expected(Some(1), Some("snapshot"), Some(false)).unwrap_err();
    assert!(
        err_non_lean.message.contains("unexpected non-Lean file in source tree: notes.txt"),
        "unexpected error: {err_non_lean}"
    );

    let f_env = TempFixture::new(None);
    let chk_env = Checker::new_with_env(
        &f_env.root,
        None,
        vec![
            ("LD_PRELOAD".to_string(), "/tmp/evil.so".to_string()),
            ("LD_LIBRARY_PATH".to_string(), "/tmp".to_string()),
            ("RUSTC_WRAPPER".to_string(), "/tmp/evil".to_string()),
            ("HOME".to_string(), "/tmp/home".to_string()),
            ("PATH".to_string(), "/tmp/evil-bin".to_string()),
        ],
    )
    .unwrap();
    assert!(!chk_env.environment().contains_key("LD_PRELOAD"));
    assert!(!chk_env.environment().contains_key("LD_LIBRARY_PATH"));
    assert!(!chk_env.environment().contains_key("RUSTC_WRAPPER"));
    assert_eq!(chk_env.environment().get("HOME").map(String::as_str), Some("/tmp/home"));
    assert_eq!(chk_env.environment().get("PATH").map(String::as_str), Some("/usr/bin:/bin"));
}

#[cfg(unix)]
fn copy_sysroot_dir(src: &Path, dst: &Path) {
    fs::create_dir_all(dst).unwrap();
    for entry in fs::read_dir(src).unwrap() {
        let entry = entry.unwrap();
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());
        let ftype = fs::symlink_metadata(&src_path).unwrap().file_type();
        if ftype.is_dir() {
            copy_sysroot_dir(&src_path, &dst_path);
        } else if ftype.is_file() && fs::hard_link(&src_path, &dst_path).is_err() {
            fs::copy(&src_path, &dst_path).unwrap();
        }
    }
}

/// Verifies through both `anneal_audit::Checker::run()` and the external
/// `anneal-audit` binary that tampering with a sysroot artifact outside
/// `foundation-lock.json` (`Lean/Replay.{olean,ir,ir.sig}`) fails closed in
/// phase `"toolchain"` with policy exit code `1` before `TrustedBoundary.lean`
/// runs.
#[cfg(unix)]
#[test]
fn rejects_tampered_lean_sysroot_outside_foundation_lock() {
    use std::os::unix::fs::PermissionsExt;

    let fix = TempFixture::new(None);
    let real_lean = fs::canonicalize(default_lean_path()).unwrap();
    let real_prefix_out = Command::new(&real_lean).arg("--print-prefix").output().unwrap();
    assert!(real_prefix_out.status.success());
    let real_prefix = PathBuf::from(String::from_utf8(real_prefix_out.stdout).unwrap().trim());

    // Place the synthetic sysroot outside `fix.root` so `scan_lean_tree` and
    // `check_checkout_cargo_hygiene` inspect only the clean fixture checkout.
    let sysroot_dir = tempfile::Builder::new().prefix("anneal-sysroot-test-").tempdir().unwrap();
    let syn_prefix = fs::canonicalize(sysroot_dir.path()).unwrap().join("sysroot");
    let copied_lean = syn_prefix.join("bin/lean");
    fs::create_dir_all(copied_lean.parent().unwrap()).unwrap();
    fs::copy(&real_lean, &copied_lean).unwrap();
    fs::set_permissions(&copied_lean, fs::Permissions::from_mode(0o755)).unwrap();

    // `verify_sysroot_foundation_dir` forbids symlinks under
    // `lib/lean/{Init,Std,Lean}`, and compiling `TrustedBoundary.lean` in the
    // control run requires `Std`/`Lean` `.ir` companions alongside `.olean*`,
    // so those subtrees use `hard_link` with `copy` fallback. Each of
    // `Lean/Replay.{olean,ir,ir.sig}` is replaced after `remove_file`, never
    // mutating the real toolchain.
    copy_sysroot_dir(&real_prefix.join("src/lean/Init"), &syn_prefix.join("src/lean/Init"));
    let dst_lib_lean = syn_prefix.join("lib/lean");
    fs::create_dir_all(&dst_lib_lean).unwrap();
    for entry in fs::read_dir(real_prefix.join("lib/lean")).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        let src_path = entry.path();
        let dst_path = dst_lib_lean.join(&name);
        if matches!(name_str.as_ref(), "Init" | "Std" | "Lean") {
            copy_sysroot_dir(&src_path, &dst_path);
        } else if ["Init.", "Std.", "Lean."].iter().any(|p| name_str.starts_with(p)) {
            if fs::symlink_metadata(&src_path).unwrap().file_type().is_file() {
                fs::copy(&src_path, &dst_path).unwrap();
            }
        } else {
            symlink(&src_path, &dst_path).unwrap();
        }
    }

    // Control: untampered sysroot copy passes `anneal_audit::Checker::run()`.
    let mut control = fix.checker_with_lean(Some(&copied_lean));
    control.set_require_mir_wp(false);
    control.run().unwrap();

    // Attack: corrupt `Lean/Replay.{olean,ir,ir.sig}` while keeping `bin/lean`
    // and all `foundation-lock.json` (`Init.*`) files untouched.
    for rel in ["Lean/Replay.olean", "Lean/Replay.ir", "Lean/Replay.ir.sig"] {
        let artifact = dst_lib_lean.join(rel);
        assert!(artifact.is_file(), "missing {}", artifact.display());
        let saved = fs::read(&artifact).unwrap();
        fs::remove_file(&artifact).unwrap();
        fs::write(&artifact, b"tampered lean replay\n").unwrap();

        let mut tampered = fix.checker_with_lean(Some(&copied_lean));
        tampered.set_require_mir_wp(false);
        let err = tampered.run().unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "toolchain"), "{err}");
        assert!(!tampered.execution_began(), "inspector ran before sysroot check: {err}");
        assert!(
            err.message.contains("sysroot Init/Std/Lean .olean/.ir manifest SHA-256 mismatch"),
            "{rel}: {err}"
        );

        // Binary CLI entrypoint also fails closed with policy exit code `1`
        // and the toolchain mismatch diagnostic.
        let bin = env!("CARGO_BIN_EXE_anneal-audit-test-bin");
        let out = Command::new(bin)
            .arg("--anneal-root")
            .arg(repo_root())
            .arg("--lean")
            .arg(&copied_lean)
            .output()
            .unwrap();
        assert_eq!(
            out.status.code(),
            Some(1),
            "status: {:?}, stderr: {}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            stderr
                .contains("(toolchain): sysroot Init/Std/Lean .olean/.ir manifest SHA-256 mismatch")
                && stderr.contains("Target execution began: false"),
            "{rel} unexpected binary stderr: {stderr}"
        );

        fs::remove_file(&artifact).unwrap();
        fs::write(&artifact, saved).unwrap();
    }
}

/// Verifies defense-in-depth in Phase 2 (`"audit"`): even if a `.lean` file
/// declaring an `axiom` were compiled directly into a `.olean` (bypassing
/// `"preflight"`), `verifyAndCollectLocals` rejects the `.olean` because every
/// constant in `data.constants` is checked for `ci.isAxiom`, even when
/// unreferenced.
#[test]
fn rejects_unused_compiled_axiom() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.tool_admission().unwrap();
    let imports = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let setup_path = checker.write_setup_json("Trusted", &imports).unwrap();
    let unchecked = checker.stage().join("UnusedAxiom.lean");
    fs::write(
        &unchecked,
        b"prelude\nimport Init.Core\nnamespace AnyNamespace\naxiom unused : True\nend AnyNamespace\n",
    )
    .unwrap();
    let out = checker.stage().join("Trusted.olean");
    checker
        .process(
            "axiom-fixture",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "--setup".to_string(),
                setup_path.to_string_lossy().into_owned(),
                "-o".to_string(),
                out.to_string_lossy().into_owned(),
                unchecked.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.insert(
            "Trusted".to_string(),
            ModuleArtifacts {
                olean_parts: vec![out.to_string_lossy().into_owned()],
                ir_parts: Vec::new(),
            },
        );
        adm.graph.insert("Trusted".to_string(), imports);
    }
    let ax_err = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(ax_err.code, 1);
    assert!(
        ax_err.message.contains("Trusted axiom AnyNamespace.unused"),
        "unexpected error: {ax_err}"
    );
}

/// Verifies that `check_cargo_boundary` rejects Cargo workspace members
/// outside `trusted/` and `tests/`, rejects reverse `trusted/` -> `tests/` and
/// out-of-`trusted/` `path` dependencies, and enforces `publish = false` and
/// build-script prohibition on `tests/` crates.
#[test]
fn rejects_cargo_workspace_members_and_path_deps_outside_trusted() {
    let checkout = repo_root();
    let mut fix = TempFixture::new(None);
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
    for rel in [
        "trusted/audit/Cargo.toml",
        "tests/testkit/Cargo.toml",
        "tests/audit/Cargo.toml",
        "tests/cargo-anneal/Cargo.toml",
        "tests/itree_diff/Cargo.toml",
        "tests/rustc-capture/Cargo.toml",
    ] {
        let dest = fix.root.join(rel);
        fs::create_dir_all(dest.parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), dest).unwrap();
    }
    copy_dir_all(&checkout.join("trusted/rustc-capture"), &fix.root.join("trusted/rustc-capture"))
        .unwrap();
    copy_dir_all(&checkout.join("trusted/cargo-anneal"), &fix.root.join("trusted/cargo-anneal"))
        .unwrap();
    check_cargo_boundary(&fix.root).unwrap();

    fs::create_dir_all(fix.root.join("crates/untrusted-helper/src")).unwrap();
    fs::write(
        fix.root.join("crates/untrusted-helper/Cargo.toml"),
        b"[package]\nname = \"untrusted-helper\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(fix.root.join("crates/untrusted-helper/src/lib.rs"), b"").unwrap();
    fs::write(
        fix.root.join("Cargo.toml"),
        b"[workspace]\nresolver = \"2\"\nmembers = [\n    \"trusted/rustc-capture\",\n    \"trusted/cargo-anneal\",\n    \"crates/untrusted-helper\",\n]\n",
    )
    .unwrap();
    let err_member = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_member
            .message
            .contains("workspace member outside trusted/ or tests/: crates/untrusted-helper"),
        "unexpected error: {err_member}"
    );

    // Reverse edge `trusted/` -> `tests/` must be rejected in both
    // `[dependencies]` and `[dev-dependencies]`.
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
    for section in ["dependencies", "dev-dependencies"] {
        fs::write(
            fix.root.join("trusted/rustc-capture/Cargo.toml"),
            format!(
                "[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[{section}]\nanneal-audit-tests = {{ path = \"../../tests/audit\" }}\n"
            ),
        )
        .unwrap();
        let err_rev = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
        assert!(
            err_rev
                .message
                .contains("trusted/rustc-capture (Trusted) path dependency violates monotonic boundary targeting tests/audit (Tests)"),
            "unexpected error for {section}: {err_rev}"
        );
    }

    fs::write(
        fix.root.join("trusted/rustc-capture/Cargo.toml"),
        b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\nuntrusted-helper = { path = \"../../crates/untrusted-helper\" }\n",
    )
    .unwrap();
    let err_dep = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(err_dep.message.contains(
        "trusted/rustc-capture path dependency points outside trusted/ or tests/: crates/untrusted-helper"
    ));

    fs::copy(
        checkout.join("trusted/rustc-capture/Cargo.toml"),
        fix.root.join("trusted/rustc-capture/Cargo.toml"),
    )
    .unwrap();

    // Test crates under `tests/` must declare `publish = false`, forbid
    // `build.rs`, and reject path dependencies outside `trusted/` and `tests/`.
    fs::write(
        fix.root.join("tests/audit/Cargo.toml"),
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    let err_publish = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_publish
            .message
            .contains("non-trusted test crate must set publish = false in tests/audit/Cargo.toml"),
        "unexpected error: {err_publish}"
    );
    fs::write(
        fix.root.join("tests/audit/Cargo.toml"),
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\nuntrusted-helper = { path = \"../../crates/untrusted-helper\" }\n",
    )
    .unwrap();
    let err_test_dep =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_test_dep.message.contains(
            "tests/audit path dependency points outside trusted/ or tests/: crates/untrusted-helper"
        ),
        "unexpected error: {err_test_dep}"
    );
    fs::copy(checkout.join("tests/audit/Cargo.toml"), fix.root.join("tests/audit/Cargo.toml"))
        .unwrap();
    fs::write(fix.root.join("tests/audit/build.rs"), b"fn main() {}\n").unwrap();
    let err_test_build =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_test_build.message.contains("disallowed build script tests/audit/build.rs"),
        "unexpected error: {err_test_build}"
    );
    fs::remove_file(fix.root.join("tests/audit/build.rs")).unwrap();
    fs::create_dir_all(fix.root.join(".cargo")).unwrap();
    fs::write(fix.root.join(".cargo/config.toml"), b"[build]\nrustc-wrapper = \"evil\"\n").unwrap();
    let err_cargo_cfg =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_cargo_cfg
            .message
            .contains("forbidden Cargo/toolchain override at repository root: .cargo")
    );
    fs::remove_dir_all(fix.root.join(".cargo")).unwrap();

    fs::write(fix.root.join("rust-toolchain.toml"), b"[toolchain]\nchannel = \"nightly\"\n")
        .unwrap();
    let err_toolchain =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_toolchain
            .message
            .contains("forbidden Cargo/toolchain override at repository root: rust-toolchain.toml")
    );
    fs::remove_file(fix.root.join("rust-toolchain.toml")).unwrap();

    fs::write(
        fix.root.join("Cargo.toml"),
        b"[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\"]\n[patch.crates-io]\nserde = { path = \"crates/untrusted-helper\" }\n",
    )
    .unwrap();
    let err_patch = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_patch.message.contains("root Cargo.toml may contain only [workspace]"),
        "unexpected error: {err_patch}"
    );
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();

    fs::write(
        fix.root.join("Cargo.lock"),
        b"version = 4\n[[package]]\nname = \"evil\"\nversion = \"0.1.0\"\nsource = \"git+https://example.com/evil.git#deadbeef\"\n",
    )
    .unwrap();
    let err_lock = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(err_lock.message.contains("untrusted dependency source in Cargo.lock for evil"));
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();

    fs::write(
        fix.root.join("Cargo.lock"),
        b"version = 4\n[[package]]\nname = \"rogue-local\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let err_rogue_lock =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_rogue_lock
            .message
            .contains("untrusted local package without source in Cargo.lock: rogue-local"),
        "unexpected error: {err_rogue_lock}"
    );
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();

    fs::copy(checkout.join("Cargo.lock"), fix.root.join("Cargo.lock")).unwrap();
    fs::copy(checkout.join("flake.nix"), fix.root.join("flake.nix")).unwrap();
    fs::copy(checkout.join("flake.lock"), fix.root.join("flake.lock")).unwrap();
    fs::copy(
        checkout.join("trusted/root-manifest.sha256"),
        fix.root.join("trusted/root-manifest.sha256"),
    )
    .unwrap();
    check_cargo_boundary(&fix.root).unwrap();

    fs::write(fix.root.join("flake.nix"), b"{ }\n").unwrap();
    let err_manifest =
        fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(
        err_manifest.message.contains("root TCB manifest digest mismatch for flake.nix"),
        "unexpected error: {err_manifest}"
    );

    // Symlinked, oversized, or unreadable root-manifest.sha256 / Cargo.lock
    // must fail closed rather than silently skipping verification.
    fs::copy(checkout.join("flake.nix"), fix.root.join("flake.nix")).unwrap();

    // 1. Symlinked trusted/root-manifest.sha256 fails closed (`code == 1`)
    // inside `verify_root_manifest_sha256`.
    fs::remove_file(fix.root.join("trusted/root-manifest.sha256")).unwrap();
    symlink(
        checkout.join("trusted/root-manifest.sha256"),
        fix.root.join("trusted/root-manifest.sha256"),
    )
    .unwrap();
    let err_sym_manifest = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_sym_manifest.code, 1, "expected policy error: {err_sym_manifest}");
    assert!(
        (err_sym_manifest.message.contains("symbolic links")
            || err_sym_manifest.message.contains("expected a regular file"))
            && err_sym_manifest.message.contains("root-manifest.sha256"),
        "expected O_NOFOLLOW/regular-file guard for root-manifest.sha256, got: {err_sym_manifest}"
    );

    // 2. Oversized `trusted/root-manifest.sha256` (> 4 MiB) hits the size cap
    // (`code == 1`).
    fs::remove_file(fix.root.join("trusted/root-manifest.sha256")).unwrap();
    {
        let oversized = fs::File::create(fix.root.join("trusted/root-manifest.sha256")).unwrap();
        oversized.set_len(4 * 1024 * 1024 + 1).unwrap();
    }
    let err_cap_manifest = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_cap_manifest.code, 1, "expected policy error: {err_cap_manifest}");
    assert!(
        err_cap_manifest.message.contains("byte limit")
            && err_cap_manifest.message.contains("root-manifest.sha256"),
        "expected byte-limit guard for root-manifest.sha256, got: {err_cap_manifest}"
    );

    // 3. With `trusted/root-manifest.sha256` absent, `verify_cargo_lock` is
    // reached: symlinked `Cargo.lock` must be rejected by `verify_cargo_lock`
    // (`code == 1`).
    fs::remove_file(fix.root.join("trusted/root-manifest.sha256")).unwrap();
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();
    symlink(checkout.join("Cargo.lock"), fix.root.join("Cargo.lock")).unwrap();
    let err_sym_lock = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_sym_lock.code, 1, "expected policy error: {err_sym_lock}");
    assert!(
        (err_sym_lock.message.contains("symbolic links")
            || err_sym_lock.message.contains("expected a regular file"))
            && err_sym_lock.message.contains("Cargo.lock"),
        "expected O_NOFOLLOW/regular-file guard for Cargo.lock, got: {err_sym_lock}"
    );

    // 4. Oversized `Cargo.lock` (> 16 MiB) hits `verify_cargo_lock`'s 16 MiB
    // cap (`code == 1`).
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();
    {
        let oversized = fs::File::create(fix.root.join("Cargo.lock")).unwrap();
        oversized.set_len(16 * 1024 * 1024 + 1).unwrap();
    }
    let err_cap_lock = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_cap_lock.code, 1, "expected policy error: {err_cap_lock}");
    assert!(
        err_cap_lock.message.contains("byte limit") && err_cap_lock.message.contains("Cargo.lock"),
        "expected byte-limit guard for Cargo.lock, got: {err_cap_lock}"
    );
}

/// Exhaustively exercises all 12 positive and negative cases of the two-zone
/// monotonic Cargo workspace lattice (`WorkspaceZone::Trusted = 0 <
/// WorkspaceZone::Tests = 1`) inside a `anneal-testkit` `WorkspaceBuilder`.
#[test]
fn enforces_two_zone_monotonic_cargo_boundary_lattice() {
    use std::time::Duration;

    let checkout = repo_root();
    let mut ws =
        anneal_testkit::WorkspaceBuilder::new("anneal-lattice-audit-", Duration::from_secs(10))
            .unwrap();
    ws.seed_minimal_audit_locks(&checkout).unwrap();

    let base_root_toml = "\
[workspace]
resolver = \"2\"
members = [
    \"trusted/rustc-capture\",
    \"trusted/cargo-anneal\",
    \"trusted/audit\",
    \"tests/testkit\",
    \"tests/audit\",
]
";
    let reset_manifests = |ws: &mut anneal_testkit::WorkspaceBuilder| {
        ws.write_work_file("Cargo.toml", base_root_toml.as_bytes()).unwrap();
        ws.write_work_file(
            "trusted/rustc-capture/Cargo.toml",
            b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        ws.write_work_file(
            "trusted/cargo-anneal/Cargo.toml",
            b"[package]\nname = \"cargo-anneal\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        ws.write_work_file(
            "trusted/audit/Cargo.toml",
            b"[package]\nname = \"anneal-audit\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\ncargo-anneal = { path = \"../cargo-anneal\" }\n",
        )
        .unwrap();
        ws.write_work_file(
            "tests/testkit/Cargo.toml",
            b"[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n",
        )
        .unwrap();
        ws.write_work_file(
            "tests/audit/Cargo.toml",
            b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\nanneal-audit = { path = \"../../trusted/audit\" }\nanneal-testkit = { path = \"../testkit\" }\n",
        )
        .unwrap();
        ws.write_work_file("trusted/cargo-anneal/build.rs", b"fn main() {}\n").unwrap();
    };

    // Cases 1–3: `trusted/* -> trusted/*` (`0 <= 0`), `tests/* -> trusted/*`
    // (`0 <= 1`), and `tests/* -> tests/testkit` (`1 <= 1`) in `[dependencies]`
    // all pass.
    reset_manifests(&mut ws);
    check_cargo_boundary(ws.work_dir()).unwrap();

    // Case 4: `tests/* -> tests/testkit` across `[dev-dependencies]`,
    // `[dev_dependencies]`, and `[target.'cfg(unix)'.dev-dependencies]` passes.
    for section in ["dev-dependencies", "dev_dependencies", "target.'cfg(unix)'.dev-dependencies"] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "tests/audit/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[{section}]\nanneal-testkit = {{ path = \"../testkit\" }}\n"
            )
            .as_bytes(),
        )
        .unwrap();
        check_cargo_boundary(ws.work_dir()).unwrap();
    }

    // Cases 5–7: `trusted/* -> tests/testkit` (`1 <= 0` violated) fails across
    // every dependency table spelling (`dependencies`, `dev-dependencies`,
    // `dev_dependencies`, `build-dependencies`, `build_dependencies`, and
    // `[target.<cfg>.*]`).
    for section in [
        "dependencies",
        "dev-dependencies",
        "dev_dependencies",
        "build-dependencies",
        "build_dependencies",
        "target.'cfg(unix)'.dependencies",
        "target.'cfg(unix)'.dev-dependencies",
    ] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "trusted/cargo-anneal/Cargo.toml",
            format!(
                "[package]\nname = \"cargo-anneal\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[{section}]\nanneal-testkit = {{ path = \"../../tests/testkit\" }}\n"
            )
            .as_bytes(),
        )
        .unwrap();
        let err = check_cargo_boundary(ws.work_dir()).unwrap_err();
        assert_eq!(err.code, 1, "{section}: {err}");
        assert_eq!(err.phase, "cargo-boundary", "{section}: {err}");
        assert!(
            err.message.contains("violates monotonic boundary targeting tests/testkit"),
            "{section}: {err}"
        );
    }

    // Case 8: `tests/*` crates omitting `publish = false`, setting
    // `publish = true`,
    // or setting `publish = ["crates-io"]` are rejected.
    for publish_line in ["", "publish = true\n", "publish = [\"crates-io\"]\n"] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "tests/testkit/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\n{publish_line}"
            )
            .as_bytes(),
        )
        .unwrap();
        let err = check_cargo_boundary(ws.work_dir()).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("publish = false"), "{publish_line:?}: {err}");
    }

    // Case 9: `package.build`, `build.rs`, `proc-macro` targets (both
    // `proc-macro`/`proc_macro` and `crate-type`/`crate_type`), and target path
    // escapes (`../escape.rs`) fail closed in `tests/` (while explicit
    // `proc-macro = false` + `crate-type = ["rlib"]` is permitted).
    reset_manifests(&mut ws);
    ws.write_work_file(
        "tests/testkit/Cargo.toml",
        b"[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[lib]\nproc-macro = false\ncrate-type = [\"rlib\"]\n",
    )
    .unwrap();
    check_cargo_boundary(ws.work_dir()).unwrap();

    for (lib_lines, expected_err) in [
        ("proc-macro = true", "disallowed proc-macro target (lib.proc-macro)"),
        ("proc_macro = true", "disallowed proc-macro target (lib.proc_macro)"),
        ("proc-macro = \"false\"", "disallowed proc-macro target (lib.proc-macro)"),
        ("crate-type = [\"proc-macro\"]", "disallowed proc-macro crate-type (lib.crate-type)"),
        (
            "crate_type = [\"rlib\", \"proc-macro\"]",
            "disallowed proc-macro crate-type (lib.crate_type)",
        ),
        ("crate-type = \"rlib\"", "invalid lib.crate-type"),
    ] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "tests/testkit/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[lib]\n{lib_lines}\n"
            )
            .as_bytes(),
        )
        .unwrap();
        let err = check_cargo_boundary(ws.work_dir()).unwrap_err();
        assert_eq!(err.code, 1, "{lib_lines}: {err}");
        assert!(err.message.contains(expected_err), "{lib_lines}: {err}");
    }

    reset_manifests(&mut ws);
    ws.write_work_file(
        "tests/testkit/Cargo.toml",
        b"[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\nbuild = \"build.rs\"\n",
    )
    .unwrap();
    assert!(
        check_cargo_boundary(ws.work_dir())
            .unwrap_err()
            .message
            .contains("disallowed package.build")
    );

    reset_manifests(&mut ws);
    ws.write_work_file("tests/testkit/build.rs", b"fn main() {}\n").unwrap();
    assert!(
        check_cargo_boundary(ws.work_dir())
            .unwrap_err()
            .message
            .contains("disallowed build script tests/testkit/build.rs")
    );
    fs::remove_file(ws.work_dir().join("tests/testkit/build.rs")).unwrap();

    reset_manifests(&mut ws);
    ws.write_work_file(
        "tests/testkit/Cargo.toml",
        b"[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[lib]\npath = \"../escape.rs\"\n",
    )
    .unwrap();
    assert!(
        check_cargo_boundary(ws.work_dir())
            .unwrap_err()
            .message
            .contains("escapes member directory")
    );

    // Case 10: `git` and custom `registry` dependencies are rejected.
    for dep_spec in [
        "evil = { git = \"https://example.com/repo.git\" }",
        "evil = { version = \"0.1\", registry = \"custom\" }",
    ] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "tests/testkit/Cargo.toml",
            format!(
                "[package]\nname = \"anneal-testkit\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\n{dep_spec}\n"
            )
            .as_bytes(),
        )
        .unwrap();
        let err = check_cargo_boundary(ws.work_dir()).unwrap_err();
        assert!(err.message.contains("disallowed git or custom-registry"), "{err}");
    }

    // Case 11: Path dependencies pointing to non-member crates inside `tests/`,
    // outside `trusted/` & `tests/`, or escaping the checkout all fail closed.
    ws.write_work_file(
        "tests/unlisted/Cargo.toml",
        b"[package]\nname = \"unlisted\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n",
    )
    .unwrap();
    reset_manifests(&mut ws);
    ws.write_work_file(
        "tests/audit/Cargo.toml",
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\nunlisted = { path = \"../unlisted\" }\n",
    )
    .unwrap();
    let err_nonmember = check_cargo_boundary(ws.work_dir()).unwrap_err();
    assert!(
        err_nonmember.message.contains("points to non-member crate: tests/unlisted"),
        "{err_nonmember}"
    );

    // Create an actual directory outside `ws.work_dir()` so canonicalization
    // succeeds and exercises the `strip_prefix(checkout_canon)` escape guard.
    let outside_dir = ws.root_dir().join("outside");
    fs::create_dir_all(&outside_dir).unwrap();
    fs::write(
        outside_dir.join("Cargo.toml"),
        b"[package]\nname = \"outside\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n",
    )
    .unwrap();
    reset_manifests(&mut ws);
    ws.write_work_file(
        "tests/audit/Cargo.toml",
        b"[package]\nname = \"anneal-audit-tests\"\nversion = \"0.1.0\"\nedition = \"2024\"\npublish = false\n[dependencies]\nescape = { path = \"../../../outside\" }\n",
    )
    .unwrap();
    let err_escape = check_cargo_boundary(ws.work_dir()).unwrap_err();
    assert_eq!(err_escape.code, 1, "{err_escape}");
    assert!(
        err_escape.message.contains("escapes checkout"),
        "expected checkout-escape diagnostic, got: {err_escape}"
    );

    // Case 12: Unclean member paths (bare `trusted`, `tests`, trailing `/`,
    // or non-compliant `workspace.exclude` crates) are rejected.
    for (bad_member, expected_diag) in [
        ("trusted", "outside trusted/ or tests/: trusted"),
        ("tests", "outside trusted/ or tests/: tests"),
        ("trusted/", "unclean member path: trusted/"),
        ("tests/../trusted/audit", "unclean member path: tests/../trusted/audit"),
    ] {
        reset_manifests(&mut ws);
        ws.write_work_file(
            "Cargo.toml",
            format!(
                "[workspace]\nresolver = \"2\"\nmembers = [\"trusted/rustc-capture\", \"{bad_member}\"]\n"
            )
            .as_bytes(),
        )
        .unwrap();
        let err = check_cargo_boundary(ws.work_dir()).unwrap_err();
        assert_eq!(err.code, 1, "{bad_member}: {err}");
        assert!(err.message.contains(expected_diag), "{bad_member}: {err}");
    }

    reset_manifests(&mut ws);
    ws.write_work_file(
        "Cargo.toml",
        format!("{base_root_toml}exclude = [\"tests/unlisted\"]\n").as_bytes(),
    )
    .unwrap();
    ws.write_work_file(
        "tests/unlisted/Cargo.toml",
        b"[package]\nname = \"unlisted\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    let err_excl = check_cargo_boundary(ws.work_dir()).unwrap_err();
    assert!(err_excl.message.contains("publish = false"), "{err_excl}");

    ws.stage().unwrap().finish(Ok(())).unwrap();
}

/// Verifies module-level trust-tier non-contamination (both syntactic
/// `"preflight"` and compiled `.olean` `"audit"`) and `Trusted` namespace
/// hygiene:
/// - A `vetted` module importing a `candidate:<feature>` module—whether or not
///   it references any candidate constant—is rejected during `"preflight"`
///   before Lean compiles the file.
/// - Bypassing `"preflight"` to present a compiled `.olean` with a
///   declaration-free `vetted -> candidate` import is still rejected by
///   `RepoOrigin.importViolation?` in `"audit"`, and a forged `.olean` whose
///   header omits the import while referencing a candidate constant is still
///   rejected by `RepoOrigin.edgeViolation?`.
/// - A `vetted` umbrella importing only `vetted` submodules, with a
///   `candidate:<feature>` module importing a `vetted` submodule and
///   `theory/Anneal.lean` importing both directly, passes `"audit"`.
/// - A `theory/Anneal.lean` module attempting to declare a constant inside the
///   reserved `Trusted` namespace (or an `opaque` constant) is rejected during
///   `"audit"`.
#[test]
fn enforces_module_level_trust_tiers_and_namespace_hygiene() {
    // 1a. A vetted module (`Trusted.lean`) importing and referencing a
    // candidate constant in `Trusted/Cand.lean` is rejected during
    // `"preflight"` before compilation starts.
    let mut f_contam = TempFixture::new(Some(&format!(
        "{HEADER}import Trusted.Cand\nnamespace Trusted\ndef badVetted : Prop := candHelper\nend Trusted\n"
    )));
    fs::create_dir_all(f_contam.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_contam.root.join("trusted/lean/Trusted/Cand.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nnamespace Trusted\ndef candHelper : Prop := True\nend Trusted\n",
    )
    .unwrap();
    let err_contam = f_contam.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err_contam.message.contains(
            "vetted module Trusted cannot import candidate:mir_semantics module Trusted.Cand"
        ),
        "unexpected error: {err_contam}"
    );

    // 1b. Even a declaration-free `vetted` umbrella `Trusted.lean` importing a
    // `candidate:<feature>` module is rejected during `"preflight"` before
    // compilation starts.
    let mut f_decl_free = TempFixture::new(Some(&format!("{HEADER}import Trusted.Cand\n")));
    fs::create_dir_all(f_decl_free.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_decl_free.root.join("trusted/lean/Trusted/Cand.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nnamespace Trusted\ndef candHelper : Prop := True\nend Trusted\n",
    )
    .unwrap();
    let err_decl_free =
        f_decl_free.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err_decl_free.message.contains(
            "vetted module Trusted cannot import candidate:mir_semantics module Trusted.Cand"
        ),
        "unexpected error: {err_decl_free}"
    );

    // 1c. Direct Lean `"preflight"` sensitivity check (independent of Rust's
    // `check_preflight_tier_imports` in `preflight_and_order_modules`): calling
    // `InspectorRequest::Preflight` directly rejects declaration-free
    // `vetted -> candidate` and `vetted -> theory` imports inside
    // `TrustedBoundary.lean`'s `checkPreflightTierImports`.
    let mut checker_lean_pf = f_decl_free.checker();
    checker_lean_pf.tool_admission().unwrap();
    let lean_pf_trusted = checker_lean_pf.stage().join("pf-trusted.lean");
    let lean_pf_cand = checker_lean_pf.stage().join("pf-cand.lean");
    fs::write(&lean_pf_trusted, format!("{HEADER}import Trusted.Cand\n")).unwrap();
    fs::write(
        &lean_pf_cand,
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    let err_lean_pf = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![
                ("Trusted".to_string(), lean_pf_trusted),
                ("Trusted.Cand".to_string(), lean_pf_cand),
            ],
            base_trusted_sources: Vec::new(),
        })
        .unwrap_err();
    assert_eq!(err_lean_pf.code, 1, "unexpected code: {err_lean_pf}");
    assert_eq!(err_lean_pf.phase, "preflight", "unexpected phase: {err_lean_pf}");
    assert!(
        err_lean_pf.message.contains(
            "vetted module Trusted cannot import candidate:mir_semantics module Trusted.Cand"
        ),
        "unexpected Lean preflight error: {err_lean_pf}"
    );

    let lean_pf_trusted_theory = checker_lean_pf.stage().join("pf-trusted-theory.lean");
    let lean_pf_theory = checker_lean_pf.stage().join("pf-theory.lean");
    fs::write(&lean_pf_trusted_theory, format!("{HEADER}import Anneal.Helper\n")).unwrap();
    fs::write(&lean_pf_theory, b"prelude\nimport Init.NotationExtra\n").unwrap();
    let err_lean_pf_theory = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![
                ("Trusted".to_string(), lean_pf_trusted_theory),
                ("Anneal.Helper".to_string(), lean_pf_theory),
            ],
            base_trusted_sources: Vec::new(),
        })
        .unwrap_err();
    assert_eq!(err_lean_pf_theory.code, 1, "unexpected theory code: {err_lean_pf_theory}");
    assert_eq!(err_lean_pf_theory.phase, "preflight", "unexpected phase: {err_lean_pf_theory}");
    assert!(
        err_lean_pf_theory
            .message
            .contains("vetted module Trusted cannot import non-foundation module Anneal.Helper"),
        "unexpected Lean preflight theory error: {err_lean_pf_theory}"
    );

    // 1d. Authenticating staged `base_trusted_sources` (`"baseSources"`) in
    // `InspectorRequest::Preflight` accepts a `vetted` correspondence source
    // importing a `vetted` on-disk base module, rejects importing an on-disk
    // `candidate` base module, rejects non-`Trusted`, foundation-named,
    // malformed-syntax, or duplicate `base_trusted_sources` entries, and
    // rejects duplicate or base-colliding `sources`.
    let lean_pf_base_vetted = checker_lean_pf.stage().join("pf-base-vetted.lean");
    let lean_pf_base_cand = checker_lean_pf.stage().join("pf-base-cand.lean");
    let lean_pf_base_theory = checker_lean_pf.stage().join("pf-base-theory.lean");
    let lean_pf_base_tactic = checker_lean_pf.stage().join("pf-base-tactic.lean");
    fs::write(&lean_pf_base_vetted, HEADER.as_bytes()).unwrap();
    fs::write(
        &lean_pf_base_cand,
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    fs::write(&lean_pf_base_theory, b"prelude\nimport Init.NotationExtra\n").unwrap();
    fs::write(&lean_pf_base_tactic, format!("{HEADER}theorem bad : Eq 0 0 := by rfl\n")).unwrap();
    let pf_base_sources = vec![
        ("Trusted.Base".to_string(), lean_pf_base_vetted.clone()),
        ("Trusted.Cand".to_string(), lean_pf_base_cand.clone()),
    ];
    let lean_pf_corr_ok = checker_lean_pf.stage().join("pf-corr-ok.lean");
    fs::write(&lean_pf_corr_ok, format!("{HEADER}import Trusted.Base\n")).unwrap();
    checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_ok.clone())],
            base_trusted_sources: pf_base_sources.clone(),
        })
        .expect("vetted source importing vetted base module in baseSources must pass");

    let lean_pf_corr_bad = checker_lean_pf.stage().join("pf-corr-bad.lean");
    fs::write(&lean_pf_corr_bad, format!("{HEADER}import Trusted.Cand\n")).unwrap();
    let err_pf_base_cand = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_bad)],
            base_trusted_sources: pf_base_sources.clone(),
        })
        .unwrap_err();
    assert_eq!(err_pf_base_cand.code, 1, "unexpected code: {err_pf_base_cand}");
    assert_eq!(err_pf_base_cand.phase, "preflight");
    assert!(
        err_pf_base_cand.message.contains(
            "vetted module Trusted.Correspondence cannot import candidate:mir_semantics module Trusted.Cand"
        ),
        "unexpected base-candidate error: {err_pf_base_cand}"
    );

    let err_pf_non_trusted_base = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_ok.clone())],
            base_trusted_sources: vec![("Anneal.Helper".to_string(), lean_pf_base_theory)],
        })
        .unwrap_err();
    assert_eq!(err_pf_non_trusted_base.code, 1);
    assert_eq!(err_pf_non_trusted_base.phase, "preflight");
    assert!(
        err_pf_non_trusted_base.message.contains("non-Trusted base preflight source Anneal.Helper"),
        "unexpected non-Trusted base source error: {err_pf_non_trusted_base}"
    );

    let err_pf_foundation_base = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_ok.clone())],
            base_trusted_sources: vec![("Init.Core".to_string(), lean_pf_base_vetted.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_foundation_base.code, 1);
    assert_eq!(err_pf_foundation_base.phase, "preflight");
    assert!(
        err_pf_foundation_base.message.contains("non-Trusted base preflight source Init.Core"),
        "unexpected foundation base source error: {err_pf_foundation_base}"
    );

    let err_pf_dup_base = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_ok.clone())],
            base_trusted_sources: vec![
                ("Trusted.Base".to_string(), lean_pf_base_cand),
                ("Trusted.Base".to_string(), lean_pf_base_vetted),
            ],
        })
        .unwrap_err();
    assert_eq!(err_pf_dup_base.code, 1);
    assert_eq!(err_pf_dup_base.phase, "preflight");
    assert!(
        err_pf_dup_base.message.contains("duplicate base preflight source module Trusted.Base"),
        "unexpected duplicate base source error: {err_pf_dup_base}"
    );

    let err_pf_bad_base_syntax = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_ok)],
            base_trusted_sources: vec![("Trusted.Base".to_string(), lean_pf_base_tactic)],
        })
        .unwrap_err();
    assert_eq!(err_pf_bad_base_syntax.code, 1);
    assert_eq!(err_pf_bad_base_syntax.phase, "preflight");

    let lean_pf_override = checker_lean_pf.stage().join("pf-override.lean");
    fs::write(&lean_pf_override, HEADER.as_bytes()).unwrap();
    let lean_pf_user = checker_lean_pf.stage().join("pf-user.lean");
    fs::write(&lean_pf_user, format!("{HEADER}import Trusted.Cand\n")).unwrap();
    let err_pf_collision = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![
                ("Trusted.Cand".to_string(), lean_pf_override),
                ("Trusted.Correspondence".to_string(), lean_pf_user.clone()),
            ],
            base_trusted_sources: pf_base_sources,
        })
        .unwrap_err();
    assert_eq!(err_pf_collision.code, 1, "unexpected collision code: {err_pf_collision}");
    assert_eq!(err_pf_collision.phase, "preflight");
    assert!(
        err_pf_collision
            .message
            .contains("preflight source module Trusted.Cand collides with base module"),
        "unexpected base collision error: {err_pf_collision}"
    );

    let lean_pf_dup_cand = checker_lean_pf.stage().join("pf-dup-cand.lean");
    let lean_pf_dup_vetted = checker_lean_pf.stage().join("pf-dup-vetted.lean");
    let lean_pf_dup_caller = checker_lean_pf.stage().join("pf-dup-caller.lean");
    fs::write(
        &lean_pf_dup_cand,
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    fs::write(&lean_pf_dup_vetted, HEADER.as_bytes()).unwrap();
    fs::write(&lean_pf_dup_caller, format!("{HEADER}import Trusted.Dup\n")).unwrap();
    let err_pf_dup = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![
                ("Trusted.Dup".to_string(), lean_pf_dup_cand),
                ("Trusted.Dup".to_string(), lean_pf_dup_vetted),
                ("Trusted.DupCaller".to_string(), lean_pf_dup_caller),
            ],
            base_trusted_sources: Vec::new(),
        })
        .unwrap_err();
    assert_eq!(err_pf_dup.code, 1, "unexpected duplicate code: {err_pf_dup}");
    assert_eq!(err_pf_dup.phase, "preflight");
    assert!(
        err_pf_dup.message.contains("duplicate preflight source module Trusted.Dup"),
        "unexpected duplicate error: {err_pf_dup}"
    );

    // 2. `Trusted.lean` (`vetted`) importing only `Trusted.VettedSub`
    // (`vetted`), `Trusted.Cand` (`candidate:mir_semantics`) importing
    // `Trusted.VettedSub`, and `theory/Anneal.lean` importing `Trusted` and
    // `Trusted.Cand` directly passes cleanly.
    let mut f_ok = TempFixture::new(Some(&format!("{HEADER}import Trusted.VettedSub\n")));
    fs::create_dir_all(f_ok.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_ok.root.join("trusted/lean/Trusted/VettedSub.lean"),
        b"-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\nnamespace Trusted\ndef vettedProp : Prop := True\nend Trusted\n",
    )
    .unwrap();
    fs::write(
        f_ok.root.join("trusted/lean/Trusted/Cand.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.VettedSub\nnamespace Trusted\ndef candProp : Prop := vettedProp\nend Trusted\n",
    )
    .unwrap();
    fs::create_dir_all(f_ok.root.join("theory")).unwrap();
    fs::write(
        f_ok.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nimport Trusted.Cand\nnamespace Anneal\ntheorem uses_both : Trusted.candProp := True.intro\nend Anneal\n",
    )
    .unwrap();
    let mut checker_ok = f_ok.checker();
    checker_ok.set_require_mir_wp(false);
    let rep_ok = checker_ok.run().unwrap();
    assert_eq!(rep_ok.get("replay"), Some(&json!(true)));

    // 2b. Defense in depth in `"audit"`: bypassing `"preflight"` with a
    // compiled declaration-free `vetted` module whose `.olean` header imports
    // `Trusted.Cand` is rejected by `RepoOrigin.importViolation?`.
    let stage = checker_ok.stage().to_path_buf();
    let trusted_lib = stage.join("lib");
    compile_forged_module(
        &mut checker_ok,
        &stage.join("src/forged-tier"),
        &trusted_lib,
        &["Trusted.Cand"],
        "Trusted.VettedImportsCand",
        "prelude\nimport Init.Core\nimport Trusted.Cand\n",
    );
    let err_audit_imp = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.VettedSub".to_string(),
                "Trusted.Cand".to_string(),
                "Trusted.VettedImportsCand".to_string(),
            ],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.VettedSub".to_string(), TrustTier::Vetted),
                ("Trusted.Cand".to_string(), TrustTier::Candidate(CandidateFeature::MirSemantics)),
                ("Trusted.VettedImportsCand".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_audit_imp.code, 1, "unexpected code: {err_audit_imp}");
    assert_eq!(err_audit_imp.phase, "audit", "unexpected phase: {err_audit_imp}");
    assert!(
        err_audit_imp.message.contains(
            "vetted module Trusted.VettedImportsCand cannot import candidate:mir_semantics module Trusted.Cand"
        ),
        "unexpected audit import error: {err_audit_imp}"
    );

    // 2c. Defense in depth in `"audit"`: a forged `vetted` `.olean` whose
    // header imports only `Init.Core` (bypassing `RepoOrigin.importViolation?`)
    // while referencing `Trusted.candProp` is still rejected by
    // `RepoOrigin.edgeViolation?`.
    let forged_edge_mod = "Trusted.ForgedVettedEdge";
    let forged_edge_out = trusted_lib.join("Trusted/ForgedVettedEdge.olean");
    run_lean_script(
        &mut checker_ok,
        "gen-forged-vetted-edge",
        &stage.join("gen_forged_vetted_edge.lean"),
        &format!(
            "import Lean.Environment\n\
             open Lean\n\
             def main : IO Unit := do\n\
               let ci : ConstantInfo := .defnInfo {{\n\
                 name := `Trusted.ForgedVettedEdge.x\n\
                 levelParams := []\n\
                 type := .sort .zero\n\
                 value := .const `Trusted.candProp []\n\
                 hints := .abbrev\n\
                 safety := .safe\n\
                 all := [`Trusted.ForgedVettedEdge.x]\n\
               }}\n\
               let md : ModuleData := {{\n\
                 isModule := false\n\
                 imports := #[{{ module := `Init.Core }}]\n\
                 constNames := #[`Trusted.ForgedVettedEdge.x]\n\
                 constants := #[ci]\n\
                 extraConstNames := #[]\n\
                 entries := #[]\n\
               }}\n\
               saveModuleData (System.FilePath.mk {:?}) `Trusted.ForgedVettedEdge md\n",
            forged_edge_out.to_string_lossy()
        ),
    );
    let core_edge = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let forged_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", forged_edge_out.to_string_lossy().into_owned())]),
        "test",
        String::new,
    )
    .unwrap();
    {
        let adm = checker_ok.admitted_mut().unwrap();
        adm.graph.remove("Trusted.VettedImportsCand");
        adm.artifacts.remove("Trusted.VettedImportsCand");
        adm.graph.insert(forged_edge_mod.to_string(), core_edge);
        adm.artifacts.insert(forged_edge_mod.to_string(), forged_arts);
    }
    let err_audit_edge = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.VettedSub".to_string(),
                "Trusted.Cand".to_string(),
                forged_edge_mod.to_string(),
            ],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.VettedSub".to_string(), TrustTier::Vetted),
                ("Trusted.Cand".to_string(), TrustTier::Candidate(CandidateFeature::MirSemantics)),
                (forged_edge_mod.to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_audit_edge.code, 1, "unexpected code: {err_audit_edge}");
    assert_eq!(err_audit_edge.phase, "audit", "unexpected phase: {err_audit_edge}");
    assert!(
        err_audit_edge.message.contains(
            "vetted constant Trusted.ForgedVettedEdge.x references candidate:mir_semantics constant Trusted.candProp"
        ),
        "unexpected audit edge error: {err_audit_edge}"
    );

    // 3. `theory/Anneal.lean` attempting to declare a constant inside the
    // reserved `Trusted` namespace is rejected during `"audit"`.
    fs::write(
        f_ok.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Trusted\ndef Spoof : Nat := 0\nend Trusted\n",
    )
    .unwrap();
    let err_spoof = f_ok.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_spoof.message.contains(
            "non-Trusted module Anneal cannot declare constant Trusted.Spoof in Trusted namespace"
        ),
        "unexpected error: {err_spoof}"
    );

    // 4. `theory/Anneal.lean` attempting to declare an `opaque` constant is
    // rejected during `"audit"`.
    fs::write(
        f_ok.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\nopaque badOpaque : Nat := 0\nend Anneal\n",
    )
    .unwrap();
    let err_opaque = f_ok.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_opaque.message.contains(
            "opaque declaration Anneal.badOpaque in Anneal is not allowed outside Trusted"
        ),
        "unexpected error: {err_opaque}"
    );
}

/// Pins end-to-end Pass 2 `baseSources` forwarding across
/// [`Checker::run_correspondence_with_closure`] and
/// `preflight_and_order_modules`:
/// - a `vetted` Pass 2 module importing a `vetted` Pass 1 base module passes
///   Pass 2 `"preflight"`, `"correspondence-preflight"`, and sandboxed
///   compilation into `lib/` before failing later in `"correspondence-audit"`
///   on the synthetic empty Miri closure; and
/// - a `vetted` Pass 2 module importing a `candidate:*` Pass 1 base module is
///   rejected in phase `"preflight"` before Pass 2 compilation.
#[test]
fn preflights_pass2_vetted_imports_against_authenticated_pass1_base_sources() {
    let setup_pass1 = |corr_import: &str| {
        let fix = TempFixture::new(None);
        fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
        fs::write(
            fix.root.join("trusted/lean/Trusted/VettedBase.lean"),
            b"-- anneal-trust-tier: vetted\n\
              prelude\nimport Init.Core\n\
              namespace Trusted.VettedBase\n\
              def ok : Nat := 1\n\
              end Trusted.VettedBase\n",
        )
        .unwrap();
        fs::write(
            fix.root.join("trusted/lean/Trusted/CandBase.lean"),
            b"-- anneal-trust-tier: candidate:mir_semantics\n\
              prelude\nimport Init.Core\n\
              namespace Trusted.CandBase\n\
              def cand : Nat := 2\n\
              end Trusted.CandBase\n",
        )
        .unwrap();
        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        checker.run().unwrap();

        let vendor_dir = fix.root.join("synthetic-miri");
        fs::create_dir_all(&vendor_dir).unwrap();
        let corr_trusted = fix.root.join("trusted/correspondence/Trusted/Correspondence.lean");
        let corr_proof = fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean");
        fs::create_dir_all(corr_trusted.parent().unwrap()).unwrap();
        fs::create_dir_all(corr_proof.parent().unwrap()).unwrap();
        fs::write(
            &corr_trusted,
            format!(
                "-- anneal-trust-tier: vetted\n\
                 prelude\nimport Init.Core\nimport {corr_import}\n\
                 namespace Trusted.Correspondence\n\
                 def corrOk : Nat := 0\n\
                 end Trusted.Correspondence\n"
            ),
        )
        .unwrap();
        fs::write(
            &corr_proof,
            "prelude\nimport Init.Core\nimport Trusted.Correspondence\n\
             namespace Anneal.MirCorrespondenceProof\n\
             def proofOk : Nat := Trusted.Correspondence.corrOk\n\
             end Anneal.MirCorrespondenceProof\n",
        )
        .unwrap();
        let base_tiers = BTreeMap::from([
            ("Trusted".to_string(), TrustTier::Vetted),
            ("Trusted.VettedBase".to_string(), TrustTier::Vetted),
            ("Trusted.CandBase".to_string(), TrustTier::Candidate(CandidateFeature::MirSemantics)),
        ]);
        (fix, checker, vendor_dir, base_tiers)
    };

    // Case 1: `vetted` Pass 2 importing `vetted` Pass 1 base module passes
    // `"preflight"` and `"correspondence-preflight"` and compiles Pass 2.
    let (_fix_ok, mut checker_ok, vendor_ok, base_tiers_ok) = setup_pass1("Trusted.VettedBase");
    let err_ok = checker_ok
        .run_correspondence_with_closure(
            &base_tiers_ok,
            &vendor_ok,
            "synthetic-commit",
            &[],
            &BTreeMap::new(),
        )
        .unwrap_err();
    assert_eq!(err_ok.code, 1, "unexpected error: {err_ok}");
    assert_eq!(
        err_ok.phase, "correspondence-audit",
        "vetted -> vetted Pass 2 import must clear preflight and compile: {err_ok}"
    );
    assert!(
        checker_ok.stage().join("lib/Trusted/Correspondence.olean").exists(),
        "Pass 2 Trusted.Correspondence must compile when importing vetted Pass 1 module"
    );
    assert!(
        checker_ok.stage().join("theory-lib/Anneal/MirCorrespondenceProof.olean").exists(),
        "Pass 2 Anneal.MirCorrespondenceProof must compile after preflight passes"
    );

    // Case 2: `vetted` Pass 2 importing `candidate` Pass 1 base module fails in
    // phase `"preflight"` before Pass 2 compilation.
    let (_fix_bad, mut checker_bad, vendor_bad, base_tiers_bad) = setup_pass1("Trusted.CandBase");
    let err_bad = checker_bad
        .run_correspondence_with_closure(
            &base_tiers_bad,
            &vendor_bad,
            "synthetic-commit",
            &[],
            &BTreeMap::new(),
        )
        .unwrap_err();
    assert_eq!(err_bad.code, 1, "unexpected error: {err_bad}");
    assert_eq!(err_bad.phase, "preflight", "expected preflight failure: {err_bad}");
    assert!(
        err_bad.message.contains(
            "vetted module Trusted.Correspondence cannot import candidate:mir_semantics module Trusted.CandBase"
        ),
        "unexpected error: {err_bad}"
    );
    assert!(
        !checker_bad.stage().join("lib/Trusted/Correspondence.olean").exists(),
        "Pass 2 Trusted.Correspondence must not compile on vetted -> candidate import"
    );
}

#[test]
fn rejects_reserved_kernel_roots_and_user_splitter_children_in_theory() {
    let mut fix =
        TempFixture::new(Some("-- anneal-trust-tier: vetted\nprelude\nimport Init.Prelude\n"));
    fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\n\
          prelude\nimport Init.Prelude\n\
          namespace Trusted.MirAst\n\
          structure Place where\n  localId : Nat\n\
          end Trusted.MirAst\n",
    )
    .unwrap();
    fs::create_dir_all(fix.root.join("theory")).unwrap();

    // (a) `def Nat.gcd`, `theorem Nat.gcd` (kernel-accelerated),
    // `theorem Nat.fakeThm` (non-accelerated `.thmInfo` in `Nat`),
    // `private def Nat.privFake`, and `def Int8.fake` in `theory/` must all be
    // rejected by `validateRepoConstant` with exit code 1.
    for (theory_src, expected_msg) in [
        (
            "prelude\nimport Trusted\nnamespace Nat\ndef gcd : Nat := 0\nend Nat\n",
            "repository module Anneal cannot declare constant Nat.gcd in reserved kernel namespace Nat",
        ),
        (
            "prelude\nimport Trusted\nnamespace Nat\ntheorem gcd : True := True.intro\nend Nat\n",
            "repository module Anneal cannot declare constant Nat.gcd in reserved kernel namespace Nat",
        ),
        (
            "prelude\nimport Trusted\nnamespace Nat\ntheorem fakeThm : True := True.intro\nend Nat\n",
            "repository module Anneal cannot declare constant Nat.fakeThm in reserved kernel namespace Nat",
        ),
        (
            "prelude\nimport Trusted\nnamespace Nat\nprivate def privFake : Nat := 0\nend Nat\n",
            "in reserved kernel namespace Nat",
        ),
        (
            "prelude\nimport Trusted\nnamespace Int8\ndef fake : Nat := 0\nend Int8\n",
            "repository module Anneal cannot declare constant Int8.fake in reserved kernel namespace Int8",
        ),
        // (b) User-authored declaration beneath `<CompoundConst>.splitter`
        // (`Trusted.MirAst.Place` is an already-imported compound `Trusted`
        // constant) must be rejected by `isGeneratedSplitterSubtree`.
        (
            "prelude\nimport Trusted\nimport Trusted.MirAst\n\
             namespace Trusted.MirAst.Place.splitter\n\
             private def evil : Nat := 0\n\
             end Trusted.MirAst.Place.splitter\n",
            "non-Trusted module Anneal cannot declare constant",
        ),
    ] {
        fs::write(fix.root.join("theory/Anneal.lean"), theory_src).unwrap();
        let err = fix.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
        assert!(
            err.message.starts_with("policy:") && err.message.contains(expected_msg),
            "expected `{expected_msg}`, got: {err}"
        );
    }

    // `theorem Nat.land` collides with `foundation-lock.json`'s
    // `Init.Data.Nat.Bitwise.Basic` and is rejected even earlier by
    // `importModules`.
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Trusted\nnamespace Nat\ntheorem land : True := True.intro\nend Nat\n",
    )
    .unwrap();
    let err_land = fix.check_expected(Some(2), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_land.message.contains("already contains 'Nat.land'"),
        "expected Nat.land collision rejection, got: {err_land}"
    );
}

/// Verifies that `verify_upstream_pin` and `Checker::run()` enforce
/// `vendor/lean-miri/UPSTREAM_PIN.json` and reject whole-directory deletion,
/// missing manifests, modified or unlisted `.lean` files, symlinks,
/// unauthorized `patched_files`, and invalid `execution_machine_closure`
/// entries with policy exit code `1`.
#[test]
fn verifies_upstream_pin_and_rejects_tampering() {
    let checkout = repo_root();
    let pin = anneal_audit::verify_upstream_pin(&checkout.join("vendor/lean-miri")).unwrap();
    assert_eq!(pin.schema_version, 2);
    assert_eq!(pin.vendor_tree.file_count, 608);
    assert_eq!(pin.patched_files.len(), 13);
    assert_eq!(pin.execution_machine_closure.len(), 160);

    // 1. Deleting `vendor/` in a repository checkout fails `Checker::run()`
    // with policy exit code `1` (`miri-pin`).
    let mut fix_missing_dir = TempFixture::new(None);
    copy_cargo_workspace(&fix_missing_dir.root);
    let err_no_vendor =
        fix_missing_dir.check_expected(Some(1), Some("miri-pin"), Some(false)).unwrap_err();
    assert!(
        err_no_vendor.message.contains("expected regular vendor directory"),
        "unexpected error: {err_no_vendor}"
    );

    // Prepare a mutable copy of `vendor/lean-miri` for tampering tests.
    let tmp = tempfile::tempdir().unwrap();
    let vendor_copy = tmp.path().join("vendor/lean-miri");
    copy_dir_all(&checkout.join("vendor/lean-miri"), &vendor_copy).unwrap();
    let pin = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap();

    // 2. Modified `.lean` file digest mismatch is rejected.
    let target_lean = vendor_copy.join("Miri.lean");
    let orig_lean = fs::read(&target_lean).unwrap();
    fs::write(&target_lean, b"-- tampered\n").unwrap();
    let err_tamper = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_tamper.code, 1);
    assert!(
        err_tamper.message.contains("vendor file SHA-256 mismatch for Miri.lean"),
        "unexpected error: {err_tamper}"
    );
    fs::write(&target_lean, &orig_lean).unwrap();

    // 2b. Patched `.lean` files are verified against `patched_sha256`, never
    // exempted from on-disk digest checking.
    for patched_rel in ["Miri/Interpreter/Call.lean", "Miri/Memory/Allocation.lean"] {
        let patched_lean = vendor_copy.join(patched_rel);
        let orig_patched = fs::read(&patched_lean).unwrap();
        let expected_patched_sha = &pin
            .patched_files
            .iter()
            .find(|p| p.path == patched_rel)
            .unwrap_or_else(|| panic!("{patched_rel} must be listed in patched_files"))
            .patched_sha256;
        fs::write(&patched_lean, b"-- tampered patched file\n").unwrap();
        let err_patched_tamper = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
        assert_eq!(err_patched_tamper.code, 1);
        assert!(
            err_patched_tamper.message.contains(&format!(
                "vendor file SHA-256 mismatch for {patched_rel}: expected {expected_patched_sha}"
            )),
            "unexpected error: {err_patched_tamper}"
        );
        fs::write(&patched_lean, &orig_patched).unwrap();
    }

    // 3. Unlisted `.lean` file is rejected.
    let rogue_lean = vendor_copy.join("Miri/Rogue.lean");
    fs::write(&rogue_lean, b"def x := 1\n").unwrap();
    let err_unlisted = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_unlisted.code, 1);
    assert!(
        err_unlisted.message.contains("unlisted Lean file in vendor/lean-miri: Miri/Rogue.lean"),
        "unexpected error: {err_unlisted}"
    );
    fs::remove_file(&rogue_lean).unwrap();

    // 3b. Unlisted non-`.lean` file (e.g. a pre-compiled `.olean`) is rejected.
    let rogue_olean = vendor_copy.join("Miri/Rogue.olean");
    fs::write(&rogue_olean, b"fake-olean-bytes").unwrap();
    let err_rogue_olean = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_rogue_olean.code, 1);
    assert!(
        err_rogue_olean.message.contains("unlisted file in vendor/lean-miri: Miri/Rogue.olean"),
        "unexpected error: {err_rogue_olean}"
    );
    fs::remove_file(&rogue_olean).unwrap();

    // 3c. Deleted pinned `.lean` file is rejected.
    fs::remove_file(&target_lean).unwrap();
    let err_deleted_lean = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_deleted_lean.code, 1);
    assert!(
        err_deleted_lean.message.contains("missing pinned .lean file in vendor/lean-miri"),
        "unexpected error: {err_deleted_lean}"
    );
    fs::write(&target_lean, &orig_lean).unwrap();

    // 3d. Deleted pinned auxiliary file is rejected.
    let target_aux = vendor_copy.join("LICENSE-MIT");
    let orig_aux = fs::read(&target_aux).unwrap();
    fs::remove_file(&target_aux).unwrap();
    let err_deleted_aux = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_deleted_aux.code, 1);
    assert!(
        err_deleted_aux.message.contains("missing pinned auxiliary file in vendor/lean-miri"),
        "unexpected error: {err_deleted_aux}"
    );
    fs::write(&target_aux, &orig_aux).unwrap();

    // 4. Symlink inside `vendor/lean-miri` is rejected.
    #[cfg(unix)]
    {
        let link_path = vendor_copy.join("Miri/Symlink.lean");
        std::os::unix::fs::symlink(&target_lean, &link_path).unwrap();
        let err_symlink = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
        assert_eq!(err_symlink.code, 1);
        assert!(
            err_symlink.message.contains("symlink forbidden in vendor/lean-miri"),
            "unexpected error: {err_symlink}"
        );
        fs::remove_file(&link_path).unwrap();
    }

    // 5. Modifying `UPSTREAM_PIN.json` without updating
    // `LOCKED_UPSTREAM_PIN_SHA256` is rejected before JSON parsing (both for
    // structured edits and malformed JSON). Structural pin-bytes checks
    // (`patched_files`, `vendor_tree`, `execution_machine_closure`) are
    // covered directly via `verify_upstream_pin_bytes` in `miri_pin.rs`.
    let pin_path = vendor_copy.join("UPSTREAM_PIN.json");
    let orig_pin_bytes = fs::read(&pin_path).unwrap();
    let mut pin_notes_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
    pin_notes_json["notes"].as_array_mut().unwrap().push(json!("extra note"));
    fs::write(&pin_path, serde_json::to_vec(&pin_notes_json).unwrap()).unwrap();
    let err_pin_sha = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_pin_sha.code, 1);
    assert!(
        err_pin_sha.message.contains("UPSTREAM_PIN.json SHA-256 differs from locked digest"),
        "unexpected error: {err_pin_sha}"
    );

    fs::write(&pin_path, b"{not valid json").unwrap();
    let err_bad_json_sha = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_bad_json_sha.code, 1);
    assert!(
        err_bad_json_sha.message.contains("UPSTREAM_PIN.json SHA-256 differs from locked digest"),
        "unexpected error: {err_bad_json_sha}"
    );

    // 6. Missing `UPSTREAM_PIN.json` is rejected with policy exit code `1`.
    fs::remove_file(&pin_path).unwrap();
    let err_missing_pin = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_missing_pin.code, 1);
    assert!(
        err_missing_pin.message.contains("missing UPSTREAM_PIN.json"),
        "unexpected error: {err_missing_pin}"
    );
}

/// Verifies that `upstream/source-lock.json` conforms to `SourceLock`'s closed
/// schema (admitting only the upstream `c92d1d97` `null` `**HASH**` on
/// `upstream/rustc-source/Cargo.lock`) and rejects unknown top-level or nested
/// fields, stray `**HASH**` elsewhere, malformed digests, blank/padded
/// components, non-canonical paths, bad `schema_version`, and duplicate paths.
#[test]
fn verifies_source_lock_schema_and_rejects_malformed_records() {
    let checkout = repo_root();
    let source_lock_bytes =
        fs::read(checkout.join("vendor/lean-miri/upstream/source-lock.json")).unwrap();
    let parsed = anneal_audit::verify_source_lock_bytes(&source_lock_bytes).unwrap();
    assert_eq!(parsed.schema_version, 1);
    assert_eq!(parsed.files.len(), 707);
    assert_eq!(parsed.supporting_files.len(), 12);

    // Future upstream lockfiles that remove the legacy `"**HASH**": null` on
    // `upstream/rustc-source/Cargo.lock` must still validate cleanly.
    let mut cleaned_lock: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    cleaned_lock["supporting_files"][11].as_object_mut().unwrap().remove("**HASH**");
    anneal_audit::verify_source_lock_bytes(&serde_json::to_vec(&cleaned_lock).unwrap()).unwrap();

    let expect_policy = |val: &serde_json::Value, needle: &str| {
        let err =
            anneal_audit::verify_source_lock_bytes(&serde_json::to_vec(val).unwrap()).unwrap_err();
        assert_eq!(err.code, 1, "expected policy error for {needle}, got {err}");
        assert!(err.message.contains(needle), "expected {needle:?} in: {err}");
    };

    // On-disk modification of `upstream/source-lock.json` is rejected by
    // `verify_upstream_pin`.
    let tmp = tempfile::tempdir().unwrap();
    let vendor_copy = tmp.path().join("vendor/lean-miri");
    copy_dir_all(&checkout.join("vendor/lean-miri"), &vendor_copy).unwrap();
    let mut disk_lock: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    disk_lock["supporting_files"][0]
        .as_object_mut()
        .unwrap()
        .insert("**HASH**".to_string(), serde_json::Value::Null);
    fs::write(
        vendor_copy.join("upstream/source-lock.json"),
        serde_json::to_vec(&disk_lock).unwrap(),
    )
    .unwrap();
    let err_disk = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_disk.code, 1);
    assert!(
        err_disk.message.contains("vendor aux file SHA-256 mismatch for upstream/source-lock.json"),
        "unexpected error: {err_disk}"
    );

    // Stray `**HASH**` is rejected on any other record, when non-null on the
    // legacy record, or anywhere in `files`.
    expect_policy(&disk_lock, "unexpected `**HASH**` field in `supporting_files`");

    let mut non_null_legacy: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    non_null_legacy["supporting_files"][11]["**HASH**"] = serde_json::json!("override");
    expect_policy(&non_null_legacy, "unexpected `**HASH**` field in `supporting_files`");

    let mut file_stray: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    file_stray["files"][0]
        .as_object_mut()
        .unwrap()
        .insert("**HASH**".to_string(), serde_json::Value::Null);
    expect_policy(&file_stray, "unexpected `**HASH**` field in `files`");

    let mut moved_legacy: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    let legacy_record = moved_legacy["supporting_files"].as_array_mut().unwrap().pop().unwrap();
    assert_eq!(legacy_record["path"].as_str(), Some("upstream/rustc-source/Cargo.lock"));
    moved_legacy["files"].as_array_mut().unwrap().push(legacy_record);
    expect_policy(
        &moved_legacy,
        "unexpected `**HASH**` field in `files` record for upstream/rustc-source/Cargo.lock",
    );

    // Unknown fields at top level and across nested `deny_unknown_fields`
    // structs must fail closed.
    let mut top_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    top_extra.as_object_mut().unwrap().insert("unexpected".to_string(), serde_json::json!(true));
    expect_policy(&top_extra, "unknown field `unexpected`");

    let mut file_rec_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    file_rec_extra["files"][0]
        .as_object_mut()
        .unwrap()
        .insert("extra_file_key".to_string(), serde_json::json!(1));
    expect_policy(&file_rec_extra, "unknown field `extra_file_key`");

    let mut pins_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    pins_extra["pins"]
        .as_object_mut()
        .unwrap()
        .insert("extra_pins_key".to_string(), serde_json::json!(1));
    expect_policy(&pins_extra, "unknown field `extra_pins_key`");

    let mut pin_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    pin_extra["pins"]["rustc"]
        .as_object_mut()
        .unwrap()
        .insert("extra_pin_key".to_string(), serde_json::json!(1));
    expect_policy(&pin_extra, "unknown field `extra_pin_key`");

    let mut acq_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    acq_extra["acquisition"]
        .as_object_mut()
        .unwrap()
        .insert("extra_acq_key".to_string(), serde_json::json!(1));
    expect_policy(&acq_extra, "unknown field `extra_acq_key`");

    let mut sel_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    sel_extra["acquisition"]["rustc_selected_archive_paths"]
        .as_object_mut()
        .unwrap()
        .insert("extra_sel_key".to_string(), serde_json::json!(1));
    expect_policy(&sel_extra, "unknown field `extra_sel_key`");

    let mut ext_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    ext_extra["external_dependencies"]
        .as_object_mut()
        .unwrap()
        .insert("extra_ext_key".to_string(), serde_json::json!(1));
    expect_policy(&ext_extra, "unknown field `extra_ext_key`");

    let mut cargo_pkg_extra: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    cargo_pkg_extra["external_dependencies"]["cargo_packages"][0]
        .as_object_mut()
        .unwrap()
        .insert("extra_pkg_key".to_string(), serde_json::json!(1));
    expect_policy(&cargo_pkg_extra, "unknown field `extra_pkg_key`");

    let mut rustc_crate_extra: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    rustc_crate_extra["external_dependencies"]["rustc_private_crates"][0]
        .as_object_mut()
        .unwrap()
        .insert("extra_crate_key".to_string(), serde_json::json!(1));
    expect_policy(&rustc_crate_extra, "unknown field `extra_crate_key`");

    let mut res_extra: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    res_extra["external_dependencies"]["resolution_file"]
        .as_object_mut()
        .unwrap()
        .insert("extra_res_key".to_string(), serde_json::json!(1));
    expect_policy(&res_extra, "unknown field `extra_res_key`");

    // Schema version, acquisition, resolution file, and pin field validations.
    let mut bad_ver: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_ver["schema_version"] = serde_json::json!(2);
    expect_policy(&bad_ver, "unsupported upstream/source-lock.json schema_version: 2");

    let mut bad_acq: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_acq["acquisition"]["rustc_selected_archive_paths"]["count"] = serde_json::json!(0);
    expect_policy(&bad_acq, "invalid `acquisition` metadata");

    let mut bad_res: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_res["external_dependencies"]["resolution_file"]["sha256"] = serde_json::json!("bad");
    expect_policy(&bad_res, "invalid `resolution_file` record");

    let mut bad_pin: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_pin["pins"]["rustc"]["commit"] = serde_json::json!("short");
    expect_policy(&bad_pin, "invalid `rustc` pin record");

    // Malformed `files` and `supporting_files` records, non-canonical paths,
    // padded components, and intra/cross-section duplicate paths.
    let mut empty_files: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    empty_files["files"] = serde_json::json!([]);
    expect_policy(&empty_files, "upstream/source-lock.json `files` must not be empty");

    let mut bad_file_blob: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_file_blob["files"][0]["git_blob"] = serde_json::json!("bad-blob");
    expect_policy(&bad_file_blob, "invalid `files` git_blob");

    let mut bad_blob: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_blob["supporting_files"][0]["git_blob"] = serde_json::json!("not-a-40-hex-oid");
    expect_policy(&bad_blob, "invalid `supporting_files` git_blob");

    let mut bad_sha: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_sha["supporting_files"][0]["sha256"] = serde_json::json!("deadbeef");
    expect_policy(&bad_sha, "invalid `supporting_files` sha256");

    for bad_component in ["   ", " aes", "aes "] {
        let mut bad_comp: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
        bad_comp["supporting_files"][0]["component"] = serde_json::json!(bad_component);
        expect_policy(&bad_comp, "invalid `supporting_files` component name");
    }

    for non_canon in
        ["../escape", "upstream//a", "upstream/./a", "upstream/a/", "/abs/path", "upstream\\a"]
    {
        let mut dirty_path: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
        dirty_path["supporting_files"][0]["path"] = serde_json::json!(non_canon);
        expect_policy(&dirty_path, "invalid `supporting_files` path");
    }

    let mut dup_path: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    let dup_entry = dup_path["supporting_files"][0].clone();
    dup_path["supporting_files"].as_array_mut().unwrap().push(dup_entry);
    expect_policy(&dup_path, "duplicate `supporting_files` path");

    let mut cross_dup: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    let file_entry = cross_dup["files"][0].clone();
    cross_dup["supporting_files"].as_array_mut().unwrap().push(file_entry);
    expect_policy(&cross_dup, "duplicate `supporting_files` path");

    // Unknown component, unpaired manifest fields, non-canonical
    // `extracted_root`, malformed `pin_markers`, and blank metadata.
    let mut bad_component: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_component["files"][0]["component"] = serde_json::json!("unknown_dep");
    expect_policy(&bad_component, "invalid `files` component name");

    let mut unpaired_manifest: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    unpaired_manifest["pins"]["rustc"]
        .as_object_mut()
        .unwrap()
        .remove("extracted_paths_manifest_sha256");
    expect_policy(&unpaired_manifest, "invalid `rustc` pin record");

    let mut bad_extracted_root: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_extracted_root["pins"]["aes"]["extracted_root"] = serde_json::json!("../aes");
    expect_policy(&bad_extracted_root, "invalid `aes` pin record");

    let mut bad_marker: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_marker["acquisition"]["pin_markers"]["miri"] = serde_json::json!("/abs/miri.commit");
    expect_policy(&bad_marker, "invalid `acquisition` metadata");

    let mut empty_notes: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    empty_notes["scope_notes"] = serde_json::json!([]);
    expect_policy(&empty_notes, "invalid coverage or feature metadata");

    let mut empty_cargo_pkgs: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    empty_cargo_pkgs["external_dependencies"]["cargo_packages"] = serde_json::json!([]);
    expect_policy(&empty_cargo_pkgs, "invalid `external_dependencies` metadata");

    let mut blank_cargo_name: serde_json::Value =
        serde_json::from_slice(&source_lock_bytes).unwrap();
    blank_cargo_name["external_dependencies"]["cargo_packages"][0]["name"] =
        serde_json::json!(" ");
    expect_policy(&blank_cargo_name, "invalid `external_dependencies` metadata");

    let mut bad_rustc_sha: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_rustc_sha["external_dependencies"]["rustc_private_crates"][0]["checksum"] =
        serde_json::json!("not-a-sha256");
    expect_policy(&bad_rustc_sha, "invalid `external_dependencies` metadata");

    let mut bad_cov_root: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    bad_cov_root["external_dependencies"]["rustc_private_crates"][0]["coverage_roots"] =
        serde_json::json!(["../escape"]);
    expect_policy(&bad_cov_root, "invalid `external_dependencies` metadata");

    let mut blank_native: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
    blank_native["external_dependencies"]["toolchain_and_native"] = serde_json::json!([""]);
    expect_policy(&blank_native, "invalid `external_dependencies` metadata");

    // Each case violates exactly one admission predicate of an otherwise valid
    // lock, so deleting that predicate lets the case pass validation or fail
    // with a different message.
    const ACQ: &str = "invalid `acquisition` metadata";
    const EXT: &str = "invalid `external_dependencies` metadata";
    const COV: &str = "invalid coverage or feature metadata";
    const FILE_COMPONENT: &str = "invalid `files` component name";
    type Mutation = fn(&mut serde_json::Value);
    let cases: &[(&str, Mutation)] = &[
        (ACQ, |v| v["acquisition"]["note"] = serde_json::json!(" ")),
        (ACQ, |v| v["acquisition"]["note"] = serde_json::json!("note ")),
        (ACQ, |v| {
            v["acquisition"]["pin_markers"]["extra"] =
                serde_json::json!("upstream/.pins/extra.commit");
        }),
        (ACQ, |v| {
            let markers = v["acquisition"]["pin_markers"].as_object_mut().unwrap();
            let aes = markers.remove("aes").unwrap();
            markers.insert("aes2".to_owned(), aes);
        }),
        ("invalid `resolution_file` record", |v| {
            v["external_dependencies"]["resolution_file"]["note"] = serde_json::json!("");
        }),
        ("invalid `rustc_upstream_resolution_file` record", |v| {
            v["external_dependencies"]["rustc_upstream_resolution_file"]["note"] =
                serde_json::json!(" padded");
        }),
        (EXT, |v| v["external_dependencies"]["cargo_packages"][0]["scope"] = serde_json::json!("")),
        (EXT, |v| {
            v["external_dependencies"]["cargo_packages"][0]["version"] = serde_json::json!(" ");
        }),
        (EXT, |v| {
            v["external_dependencies"]["cargo_packages"][1]["requirement"] = serde_json::json!("");
        }),
        (EXT, |v| {
            let pkg = &mut v["external_dependencies"]["cargo_packages"][20];
            assert!(pkg.get("path").is_some(), "fixture package 20 must set `path`");
            pkg["path"] = serde_json::json!(" ");
        }),
        (EXT, |v| {
            v["external_dependencies"]["cargo_packages"][0]["features"] =
                serde_json::json!(["hazmat", " "]);
        }),
        (EXT, |v| v["external_dependencies"]["rustc_private_crates"] = serde_json::json!([])),
        (EXT, |v| {
            v["external_dependencies"]["rustc_private_crates"][0]["name"] = serde_json::json!("");
        }),
        (EXT, |v| {
            v["external_dependencies"]["rustc_private_crates"][0]["status"] =
                serde_json::json!(" ");
        }),
        (EXT, |v| {
            v["external_dependencies"]["rustc_private_crates"][0]["evidence"] =
                serde_json::json!("");
        }),
        (EXT, |v| {
            v["external_dependencies"]["rustc_private_crates"][1]["version"] =
                serde_json::json!(" ");
        }),
        (EXT, |v| {
            v["external_dependencies"]["rustc_private_crates"][1]["git_commit"] =
                serde_json::json!("short");
        }),
        (EXT, |v| v["external_dependencies"]["toolchain_and_native"] = serde_json::json!([])),
        (COV, |v| v["coverage_roots"] = serde_json::json!([])),
        (COV, |v| v["coverage_roots"][0] = serde_json::json!("upstream//escape")),
        (COV, |v| v["coverage_expected_rust_modules"] = serde_json::json!({})),
        (COV, |v| v["coverage_expected_rust_modules"]["upstream/./src"] = serde_json::json!(1)),
        (COV, |v| {
            let modules = v["coverage_expected_rust_modules"].as_object_mut().unwrap();
            *modules.values_mut().next().unwrap() = serde_json::json!(0);
        }),
        (COV, |v| v["features"] = serde_json::json!({})),
        (COV, |v| v["features"][" "] = serde_json::json!(["stack-cache"])),
        (COV, |v| v["features"]["default"] = serde_json::json!(["stack-cache", ""])),
        (COV, |v| v["scope_notes"] = serde_json::json!([" "])),
        ("invalid `rustc` pin record", |v| {
            v["pins"]["rustc"]["extracted_paths_manifest"] = serde_json::json!("../paths.txt");
        }),
        ("invalid `rustc` pin record", |v| {
            v["pins"]["rustc"].as_object_mut().unwrap().remove("extracted_paths_manifest");
        }),
        ("invalid `aes` pin record", |v| {
            v["pins"]["aes"]["checksum_source"] = serde_json::json!(" ");
        }),
        ("invalid `aes` pin record", |v| {
            v["pins"]["aes"]["package_version"] = serde_json::json!("");
        }),
        ("invalid `miri` pin record", |v| {
            v["pins"]["miri"]["commit_date_utc"] = serde_json::json!("");
        }),
        ("invalid `miri` pin record", |v| v["pins"]["miri"]["commit_url"] = serde_json::json!(" ")),
        ("invalid `miri` pin record", |v| v["pins"]["miri"]["pinned_via"] = serde_json::json!("")),
        ("invalid `miri` pin record", |v| {
            v["pins"]["miri"]["archive_url"] = serde_json::json!(" padded");
        }),
        ("invalid `miri` pin record", |v| {
            v["pins"]["miri"]["repository"] = serde_json::json!("padded ");
        }),
        ("invalid `rustc_apfloat` pin record", |v| {
            v["pins"]["rustc_apfloat"]["registry"] = serde_json::json!(" ");
        }),
        (FILE_COMPONENT, |v| v["files"][0]["component"] = serde_json::json!("rustc_")),
        (FILE_COMPONENT, |v| v["files"][0]["component"] = serde_json::json!("rustc_Abi")),
    ];
    for (needle, mutate) in cases {
        let mut lock: serde_json::Value = serde_json::from_slice(&source_lock_bytes).unwrap();
        mutate(&mut lock);
        expect_policy(&lock, needle);
    }
}

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

/// Verifies that cold `vendor/lean-miri/` compilation runs inside an OS-level
/// sandbox that prevents compile-time metaprograms (`run_cmd`) from writing to
/// the repository checkout, host directories, or auditor staging state
/// (including read-only `miri-lib`), and rejects unexpected extra files written
/// inside the isolated `/work/out` output directory before staging.
#[cfg(target_os = "linux")]
#[test]
fn sandboxes_cold_miri_compilation_against_host_and_stage_writes() {
    let fix = TempFixture::new(None);
    let vendor_dir = fix.root.join("fake-vendor");
    fs::create_dir_all(vendor_dir.join("Miri")).unwrap();

    // Case 1: A malicious `run_cmd` attempting to write to the repository
    // checkout fails inside the mount-isolated sandbox and leaves the checkout
    // untouched.
    let checkout_victim = fix.root.join("sandbox-escape-checkout.txt");
    let escape_checkout_src = format!(
        "import Lean.Elab.Command\n\
         namespace Miri.EscapeCheckout\n\
         run_cmd do\n\
           IO.FS.writeFile \"{}\" \"pwned\"\n\
         def x : Nat := 1\n\
         end Miri.EscapeCheckout\n",
        checkout_victim.display()
    );
    let escape_checkout_path = vendor_dir.join("Miri/EscapeCheckout.lean");
    fs::write(&escape_checkout_path, &escape_checkout_src).unwrap();
    let escape_checkout_entry = MiriClosureEntry {
        module: "Miri.EscapeCheckout".to_string(),
        path: "Miri/EscapeCheckout.lean".to_string(),
        olean_sha256: "0".repeat(64),
        olean_server_sha256: None,
        olean_private_sha256: None,
    };
    let escape_checkout_sources = BTreeMap::from([(
        "Miri/EscapeCheckout.lean".to_string(),
        sha256_bytes(escape_checkout_src.as_bytes()),
    )]);
    let mut c1 = fix.checker();
    c1.set_require_mir_wp(false);
    c1.run().unwrap();
    let err1 = c1
        .verify_and_stage_miri_entries(
            &vendor_dir,
            &[escape_checkout_entry],
            &escape_checkout_sources,
        )
        .unwrap_err();
    assert_eq!(err1.code, 2, "expected sandboxed compile error: {err1}");
    assert!(!checkout_victim.exists(), "sandboxed run_cmd must not be able to write to checkout");

    // Case 2: A malicious `run_cmd` attempting to write into the auditor's
    // read-only `/work/lp0` (`miri-lib` mount) or host `stage` fails with
    // `EROFS`/`ENOENT` and leaves both untouched.
    let mut c2 = fix.checker();
    c2.set_require_mir_wp(false);
    c2.run().unwrap();
    let stage_victim = c2.stage().join("sandbox-escape-stage.txt");
    let ro_lib_victim = c2.stage().join("miri-lib/sandbox-escape-ro.txt");
    let escape_stage_src = format!(
        "import Lean.Elab.Command\n\
         namespace Miri.EscapeStage\n\
         run_cmd do\n\
           try\n\
             IO.FS.writeFile \"{}\" \"pwned\"\n\
           catch _ =>\n\
             IO.FS.writeFile \"/work/lp0/sandbox-escape-ro.txt\" \"pwned\"\n\
         def x : Nat := 1\n\
         end Miri.EscapeStage\n",
        stage_victim.display()
    );
    let escape_stage_path = vendor_dir.join("Miri/EscapeStage.lean");
    fs::write(&escape_stage_path, &escape_stage_src).unwrap();
    let escape_stage_entry = MiriClosureEntry {
        module: "Miri.EscapeStage".to_string(),
        path: "Miri/EscapeStage.lean".to_string(),
        olean_sha256: "0".repeat(64),
        olean_server_sha256: None,
        olean_private_sha256: None,
    };
    let escape_stage_sources = BTreeMap::from([(
        "Miri/EscapeStage.lean".to_string(),
        sha256_bytes(escape_stage_src.as_bytes()),
    )]);
    let err2 = c2
        .verify_and_stage_miri_entries(&vendor_dir, &[escape_stage_entry], &escape_stage_sources)
        .unwrap_err();
    assert_eq!(err2.code, 2, "expected sandboxed compile error: {err2}");
    assert!(
        !stage_victim.exists() && !ro_lib_victim.exists(),
        "sandboxed run_cmd must not be able to write to stage or read-only miri-lib"
    );

    // Case 3: Even if a `run_cmd` drops an unexpected extra file inside the
    // sole writable sandbox output directory (`/work/out`) while producing a
    // digest-matching `.olean`, the outer auditor rejects the unexpected file
    // with policy exit code `1` and stages nothing into `miri-lib` or cache.
    let extra_out_src = "import Lean.Elab.Command\n\
        namespace Miri.ExtraOut\n\
        run_cmd do\n\
          IO.FS.writeFile \"out/unexpected-drop.txt\" \"junk\"\n\
        def x : Nat := 1\n\
        end Miri.ExtraOut\n";
    let extra_out_path = vendor_dir.join("Miri/ExtraOut.lean");
    fs::write(&extra_out_path, extra_out_src).unwrap();
    let mut probe = fix.checker();
    probe.set_require_mir_wp(false);
    probe.run().unwrap();
    let probe_out_dir = probe.stage().join("out");
    fs::create_dir_all(probe_out_dir.join("Miri")).unwrap();
    probe
        .process(
            "probe-extra-out",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_out_dir.join("Miri/ExtraOut.olean").to_string_lossy().into_owned(),
                extra_out_path.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let extra_olean_sha = sha256_file(&probe_out_dir.join("Miri/ExtraOut.olean"), "test").unwrap();
    let extra_server_sha = probe_out_dir
        .join("Miri/ExtraOut.olean.server")
        .exists()
        .then(|| sha256_file(&probe_out_dir.join("Miri/ExtraOut.olean.server"), "test").unwrap());
    let extra_private_sha = probe_out_dir
        .join("Miri/ExtraOut.olean.private")
        .exists()
        .then(|| sha256_file(&probe_out_dir.join("Miri/ExtraOut.olean.private"), "test").unwrap());

    let cache_dir =
        tempfile::Builder::new().prefix("anneal-sandbox-extra-cache-").tempdir().unwrap();
    let extra_entry = MiriClosureEntry {
        module: "Miri.ExtraOut".to_string(),
        path: "Miri/ExtraOut.lean".to_string(),
        olean_sha256: extra_olean_sha,
        olean_server_sha256: extra_server_sha,
        olean_private_sha256: extra_private_sha,
    };
    let extra_sources = BTreeMap::from([(
        "Miri/ExtraOut.lean".to_string(),
        sha256_bytes(extra_out_src.as_bytes()),
    )]);
    let mut c3 = fix.checker();
    c3.set_require_mir_wp(false);
    c3.set_miri_cache_dir(Some(cache_dir.path().to_path_buf()));
    c3.run().unwrap();
    let err3 =
        c3.verify_and_stage_miri_entries(&vendor_dir, &[extra_entry], &extra_sources).unwrap_err();
    assert_eq!(err3.code, 2, "expected Door 1 error for extra sandbox output: {err3}");
    assert!(
        err3.message.contains("unexpected compiler output unexpected-drop.txt"),
        "unexpected error message: {err3}"
    );
    assert!(
        !c3.stage().join("miri-lib/Miri/ExtraOut.olean").exists()
            && !cache_dir.path().join("Miri/ExtraOut.olean").exists(),
        "rejected sandbox output must not be staged or cached"
    );

    // Case 4: A real Lean 4 `module`-system vendored file
    // (`Miri.Memory.QSortProof`, which emits `.olean.{server,private}` plus
    // ephemeral `.ir`/`.ir.sig` sidecars) compiles cold inside the sandbox,
    // stages and caches only the digest-verified `.olean*` artifacts, and
    // discards `.ir`/`.ir.sig`.
    let checkout = repo_root();
    let real_vendor = checkout.join("vendor/lean-miri");
    let real_pin = anneal_audit::verify_upstream_pin(&real_vendor).unwrap();
    let qsort_entry = real_pin
        .execution_machine_closure
        .iter()
        .find(|e| e.module == "Miri.Memory.QSortProof")
        .expect("Miri.Memory.QSortProof must exist in closure")
        .clone();
    let qsort_src_sha = real_pin
        .vendor_tree
        .files
        .iter()
        .find(|f| f.path == qsort_entry.path)
        .expect("QSortProof.lean must exist in vendor_tree")
        .sha256
        .clone();
    let qsort_sources = BTreeMap::from([(qsort_entry.path.clone(), qsort_src_sha)]);
    let qsort_cache =
        tempfile::Builder::new().prefix("anneal-sandbox-qsort-cache-").tempdir().unwrap();
    let mut c4 = fix.checker();
    c4.set_require_mir_wp(false);
    c4.set_miri_cache_dir(Some(qsort_cache.path().to_path_buf()));
    c4.run().unwrap();
    let miri_lib =
        c4.verify_and_stage_miri_entries(&real_vendor, &[qsort_entry], &qsort_sources).unwrap();
    for ext in ["olean", "olean.server", "olean.private"] {
        let rel = format!("Miri/Memory/QSortProof.{ext}");
        assert!(miri_lib.join(&rel).is_file(), "expected staged {rel} in miri-lib");
        assert!(qsort_cache.path().join(&rel).is_file(), "expected cached {rel} in miri cache");
    }
    for ext in ["ir", "ir.sig"] {
        let rel = format!("Miri/Memory/QSortProof.{ext}");
        assert!(!miri_lib.join(&rel).exists(), "ephemeral {rel} must not be staged into miri-lib");
        assert!(
            !qsort_cache.path().join(&rel).exists(),
            "ephemeral {rel} must not be written to miri cache"
        );
    }

    // Case 5: A non-module cold compile (`olean_server_sha256` and
    // `olean_private_sha256` both `None`) that emits `.ir` or `.ir.sig`
    // alongside a digest-matching `.olean` must still be rejected with Door 1
    // operational exit code `2`, staging and caching nothing.
    for (module, stem, leaf, ext) in [
        ("Miri.ExtraIr", "Miri/ExtraIr", "ExtraIr", "ir"),
        ("Miri.ExtraIrSig", "Miri/ExtraIrSig", "ExtraIrSig", "ir.sig"),
    ] {
        let sidecar_rel = format!("{stem}.{ext}");
        let sidecar_leaf = format!("{leaf}.{ext}");
        let src = format!(
            "import Lean.Elab.Command\n\
             namespace {module}\n\
             run_cmd do\n\
               IO.FS.writeFile \"out/{sidecar_leaf}\" \"fake-ir\"\n\
             def x : Nat := 1\n\
             end {module}\n"
        );
        let src_rel = format!("{stem}.lean");
        let src_path = vendor_dir.join(&src_rel);
        fs::write(&src_path, &src).unwrap();

        let mut ir_probe = fix.checker();
        ir_probe.set_require_mir_wp(false);
        ir_probe.run().unwrap();
        let ir_probe_out = ir_probe.stage().join("out");
        fs::create_dir_all(ir_probe_out.join("Miri")).unwrap();
        let olean_rel = format!("{stem}.olean");
        ir_probe
            .process(
                "probe-nonmodule-ir",
                &[
                    "-j1".to_string(),
                    "-M2048".to_string(),
                    "-t0".to_string(),
                    "-DElab.async=false".to_string(),
                    "-Ddebug.skipKernelTC=false".to_string(),
                    "-R".to_string(),
                    vendor_dir.to_string_lossy().into_owned(),
                    "-o".to_string(),
                    ir_probe_out.join(&olean_rel).to_string_lossy().into_owned(),
                    src_path.to_string_lossy().into_owned(),
                ],
            )
            .unwrap();
        assert!(
            !ir_probe_out.join(format!("{stem}.olean.server")).exists()
                && !ir_probe_out.join(format!("{stem}.olean.private")).exists(),
            "{module} must compile as a non-module entry"
        );
        let olean_sha = sha256_file(&ir_probe_out.join(&olean_rel), "test").unwrap();

        let ir_cache = tempfile::Builder::new()
            .prefix("anneal-sandbox-nonmodule-ir-cache-")
            .tempdir()
            .unwrap();
        let ir_entry = MiriClosureEntry {
            module: module.to_string(),
            path: src_rel.clone(),
            olean_sha256: olean_sha,
            olean_server_sha256: None,
            olean_private_sha256: None,
        };
        let ir_sources = BTreeMap::from([(src_rel, sha256_bytes(src.as_bytes()))]);
        let mut c5 = fix.checker();
        c5.set_require_mir_wp(false);
        c5.set_miri_cache_dir(Some(ir_cache.path().to_path_buf()));
        c5.run().unwrap();
        let err5 =
            c5.verify_and_stage_miri_entries(&vendor_dir, &[ir_entry], &ir_sources).unwrap_err();
        assert_eq!(err5.code, 2, "expected Door 1 error for non-module {ext} sidecar: {err5}");
        assert_eq!(err5.phase, "door1");
        let expected_diag = format!("unexpected compiler output {sidecar_leaf}");
        assert!(err5.message.contains(&expected_diag), "expected `{expected_diag}`, got: {err5}");
        assert!(
            !c5.stage().join("miri-lib").join(&olean_rel).exists()
                && !c5.stage().join("miri-lib").join(&sidecar_rel).exists()
                && !ir_cache.path().join(&olean_rel).exists()
                && !ir_cache.path().join(&sidecar_rel).exists(),
            "rejected non-module {ext} output must not be staged or cached"
        );
    }
}

fn materialize_mir_wp(spec: &MirWpFixtureSpec) -> TempFixture {
    let fix = TempFixture::new(Some(HEADER));
    spec.materialize_into(&fix.inner).unwrap();
    fix
}

fn expect_mir_wp_audit_policy_err(spec: &MirWpFixtureSpec, expected_substring: &str) {
    let fix = materialize_mir_wp(spec);
    let mut checker = fix.checker();
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "expected exit code 1, got: {err}");
    assert_eq!(err.phase, "audit", "expected audit phase, got: {err}");
    assert!(checker.execution_began(), "expected Lean execution before audit failure: {err}");
    assert!(
        err.message.contains(expected_substring),
        "expected error containing {expected_substring:?}, got: {err}"
    );
}

/// Verifies every trigger and missing-module rejection branch of
/// `verifyMirWpCoreTheorems` (`TrustedBoundary.lean`): default
/// `require_mir_wp == true` on bare/partial checkouts, plus every individual
/// module trigger (`Anneal.PureLift`, `Anneal.MirWp`, `Trusted.MirSemantics`,
/// `Trusted.MirAst`) when `require_mir_wp == false`.
#[test]
fn enforces_mir_wp_non_backsliding() {
    // 0. With default `Checker::new` (`require_mir_wp == true`), even a
    // checkout with NONE of `Trusted.MirAst`, `Trusted.MirSemantics`,
    // `Anneal.MirWp`, or `Anneal.PureLift` is rejected fail-closed.
    let fix_missing_all = TempFixture::new(Some(HEADER));
    let mut checker_missing_all = fix_missing_all.checker();
    let err_missing_all = checker_missing_all.run().unwrap_err();
    assert_eq!(err_missing_all.code, 1);
    assert_eq!(err_missing_all.phase, "audit");
    assert!(
        err_missing_all.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err_missing_all}"
    );

    // 1. With default `Checker::new` (`require_mir_wp == true`), deleting both
    // `Trusted/MirSemantics.lean` and `Anneal/MirWp.lean` (even when
    // `Trusted/MirAst.lean` is present) is rejected fail-closed.
    let fix_missing_both = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_missing_both.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix_missing_both.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirAst\ndef placeholder : Nat := 0\nend Trusted.MirAst\n",
    )
    .unwrap();
    let mut checker_missing_both = fix_missing_both.checker();
    let err_missing_both = checker_missing_both.run().unwrap_err();
    assert_eq!(err_missing_both.code, 1);
    assert_eq!(err_missing_both.phase, "audit");
    assert!(
        err_missing_both.message.contains("missing required trusted module Trusted.MirSemantics"),
        "unexpected error: {err_missing_both}"
    );

    // 2. With `require_mir_wp == false`, presence of `Anneal.PureLift` alone
    // triggers `verifyMirWpCoreTheorems` and rejects with exit code 1.
    let mut fix_pure_lift_only = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_pure_lift_only.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix_pure_lift_only.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nimport Anneal.PureLift\n",
    )
    .unwrap();
    fs::write(
        fix_pure_lift_only.root.join("theory/Anneal/PureLift.lean"),
        b"prelude\nimport Init.NotationExtra\nnamespace Anneal.PureLift\ndef marker : Nat := 0\nend Anneal.PureLift\n",
    )
    .unwrap();
    let err_pure_lift =
        fix_pure_lift_only.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_pure_lift.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err_pure_lift}"
    );

    // 3. With `require_mir_wp == false`, presence of `Anneal.MirWp` alone
    // triggers `verifyMirWpCoreTheorems` and rejects with exit code 1.
    let mut fix_mir_wp_only = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_mir_wp_only.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix_mir_wp_only.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nimport Anneal.MirWp\n",
    )
    .unwrap();
    fs::write(
        fix_mir_wp_only.root.join("theory/Anneal/MirWp.lean"),
        b"prelude\nimport Init.NotationExtra\nnamespace Anneal.MirWp\ndef marker : Nat := 0\nend Anneal.MirWp\n",
    )
    .unwrap();
    let err_mir_wp_only =
        fix_mir_wp_only.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_mir_wp_only.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err_mir_wp_only}"
    );

    // 4. With `require_mir_wp == false`, presence of `Trusted.MirSemantics`
    // alone triggers `verifyMirWpCoreTheorems` and rejects with exit code 1.
    let mut fix_sem_only = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_sem_only.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix_sem_only
            .root
            .join("trusted/lean/Trusted/MirSemantics.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirSemantics\ndef placeholder : Nat := 0\nend Trusted.MirSemantics\n",
    )
    .unwrap();
    let err_sem_only = fix_sem_only.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_sem_only.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err_sem_only}"
    );

    // 5. With `require_mir_wp == false`, presence of `Trusted.MirAst` alone
    // triggers `verifyMirWpCoreTheorems` and rejects missing
    // `Trusted.MirSemantics`.
    let mut fix_ast_only = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_ast_only.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix_ast_only.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirAst\ndef placeholder : Nat := 0\nend Trusted.MirAst\n",
    )
    .unwrap();
    let err_ast_only = fix_ast_only.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_ast_only.message.contains("missing required trusted module Trusted.MirSemantics"),
        "unexpected error: {err_ast_only}"
    );

    // 6. With `require_mir_wp == false`, `Trusted.MirAst` and
    // `Trusted.MirSemantics` without `Anneal.MirWp` are rejected in `"audit"`.
    let mut fix_no_wp = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_no_wp.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix_no_wp.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\nnamespace Trusted.MirAst\ndef placeholder : Nat := 0\nend Trusted.MirAst\n",
    )
    .unwrap();
    fs::write(
        fix_no_wp.root.join("trusted/lean/Trusted/MirSemantics.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.MirAst\nnamespace Trusted.MirSemantics\ndef placeholder : Nat := 0\nend Trusted.MirSemantics\n",
    )
    .unwrap();
    let err_no_wp = fix_no_wp.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_no_wp.message.contains("missing required theory module Anneal.MirWp"),
        "unexpected error: {err_no_wp}"
    );

    // 7. Missing decoupled `Anneal.MirWp.Canaries` is rejected fail-closed even
    // when `Anneal` and `Anneal.MirWp` are present and neither imports it.
    let mut missing_canaries = MirWpFixtureSpec::valid();
    missing_canaries.include_canaries_module = false;
    expect_mir_wp_audit_policy_err(
        &missing_canaries,
        "missing required theory module Anneal.MirWp.Canaries",
    );

    // 8. With `require_mir_wp == false`, presence of `Anneal.MirWp.Canaries`
    // alone triggers `verifyMirWpCoreTheorems` and rejects fail-closed.
    let mut fix_canaries_only = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_canaries_only.root.join("theory/Anneal/MirWp")).unwrap();
    fs::write(
        fix_canaries_only.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\n",
    )
    .unwrap();
    fs::write(
        fix_canaries_only.root.join("theory/Anneal/MirWp/Canaries.lean"),
        b"prelude\nimport Init.NotationExtra\nnamespace Anneal.MirWp\ndef marker : Nat := 0\nend Anneal.MirWp\n",
    )
    .unwrap();
    let err_canaries_only =
        fix_canaries_only.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_canaries_only.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err_canaries_only}"
    );
}

/// Verifies every rejection branch of `requireClaimProof` (parameterized mode,
/// `argName? = some _`) in `TrustedBoundary.lean` (missing claim, missing
/// theorem, non-theorem proof, wrong-module proof, weakened/wrong-type proof,
/// non-definition claim, wrong-module claim, and claim bodies missing required
/// semantic constants) against a passing synthetic baseline.
#[test]
fn enforces_mir_wp_param_claim_proof_rules() {
    // Baseline: the unmutated synthetic fixture passes with default
    // `require_mir_wp == true`.
    let baseline = materialize_mir_wp(&MirWpFixtureSpec::valid());
    let mut checker = baseline.checker();
    let report = checker.run().unwrap();
    assert_eq!(report.get("replay"), Some(&json!(true)));

    // Missing `WpSoundnessClaim` from `Trusted.MirSemantics`.
    let mut missing_wp_claim = MirWpFixtureSpec::valid();
    missing_wp_claim.wp_soundness_claim = None;
    missing_wp_claim.wp_soundness_proof = None;
    expect_mir_wp_audit_policy_err(
        &missing_wp_claim,
        "missing required claim Trusted.MirSemantics.WpSoundnessClaim",
    );

    // Missing `wellFormed_and_spec_of_wp`.
    let mut missing_wp_thm = MirWpFixtureSpec::valid();
    missing_wp_thm.wp_soundness_proof = None;
    expect_mir_wp_audit_policy_err(
        &missing_wp_thm,
        "missing required theorem Anneal.MirWp.wellFormed_and_spec_of_wp",
    );

    // Missing `reaches_fault_and_exclusive_of_wpFault`.
    let mut missing_fault_thm = MirWpFixtureSpec::valid();
    missing_fault_thm.wp_fault_soundness_proof = None;
    expect_mir_wp_audit_policy_err(
        &missing_fault_thm,
        "missing required theorem Anneal.MirWp.reaches_fault_and_exclusive_of_wpFault",
    );

    // Non-theorem proof (`def` instead of `theorem`).
    let mut def_instead_of_thm = MirWpFixtureSpec::valid();
    def_instead_of_thm.wp_soundness_proof =
        Some("def wellFormed_and_spec_of_wp : Nat := 0".to_string());
    expect_mir_wp_audit_policy_err(
        &def_instead_of_thm,
        "expected Anneal.MirWp.wellFormed_and_spec_of_wp to be a theorem",
    );

    // Proof defined in `Anneal.Wp` instead of `Anneal.MirWp`.
    let mut wrong_proof_mod = MirWpFixtureSpec::valid();
    wrong_proof_mod.wp_soundness_proof = None;
    wrong_proof_mod.anneal_extra = "\
        namespace Anneal.MirWp\n\
        theorem wellFormed_and_spec_of_wp : \
            Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
          And.intro True.intro (And.intro True.intro True.intro)\n\
        end Anneal.MirWp"
        .to_string();
    expect_mir_wp_audit_policy_err(
        &wrong_proof_mod,
        "expected Anneal.MirWp.wellFormed_and_spec_of_wp to be defined in \
         Anneal.MirWp, found Anneal.Wp",
    );

    // Weakened / wrong-type proof (`True` instead of
    // `WpSoundnessClaim wpProg`).
    let mut weakened_wp_thm = MirWpFixtureSpec::valid();
    weakened_wp_thm.wp_soundness_proof =
        Some("theorem wellFormed_and_spec_of_wp : True := True.intro".to_string());
    expect_mir_wp_audit_policy_err(
        &weakened_wp_thm,
        "theorem Anneal.MirWp.wellFormed_and_spec_of_wp must prove \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg directly",
    );

    // Non-definition claim (`inductive` instead of `def`).
    let mut non_def_claim = MirWpFixtureSpec::valid();
    non_def_claim.wp_soundness_claim =
        Some("inductive WpSoundnessClaim (_f : Nat) : Prop where\n  | intro".to_string());
    non_def_claim.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
         Trusted.MirSemantics.WpSoundnessClaim.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &non_def_claim,
        "expected Trusted.MirSemantics.WpSoundnessClaim to be a definition",
    );

    // Claim defined in `Trusted.MirAst` instead of `Trusted.MirSemantics`.
    let mut wrong_claim_mod = MirWpFixtureSpec::valid();
    wrong_claim_mod.wp_soundness_claim = None;
    wrong_claim_mod.mir_ast_extra = "\
        namespace Trusted.MirSemantics\n\
        def WpSoundnessClaim (_f : Nat) : Prop := True\n\
        end Trusted.MirSemantics"
        .to_string();
    wrong_claim_mod.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := True.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &wrong_claim_mod,
        "expected Trusted.MirSemantics.WpSoundnessClaim to be defined in \
         Trusted.MirSemantics, found Trusted.MirAst",
    );

    // Claim body missing required `SatisfiesPost` reference
    // (`TrustedBoundary.lean` `requireClaimProof` `reqConsts` check).
    let mut missing_req_const = MirWpFixtureSpec::valid();
    missing_req_const.wp_soundness_claim =
        Some("def WpSoundnessClaim (_f : Nat) : Prop := And Diverges Behavior".to_string());
    missing_req_const.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &missing_req_const,
        "claim Trusted.MirSemantics.WpSoundnessClaim body must reference \
         Trusted.MirSemantics.SatisfiesPost",
    );

    // Claim body missing required `Diverges` reference (prevents silently
    // weakening the audited WP claim to partial correctness).
    let mut missing_diverges_const = MirWpFixtureSpec::valid();
    missing_diverges_const.wp_soundness_claim =
        Some("def WpSoundnessClaim (_f : Nat) : Prop := And SatisfiesPost Behavior".to_string());
    missing_diverges_const.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &missing_diverges_const,
        "claim Trusted.MirSemantics.WpSoundnessClaim body must reference \
         Trusted.MirSemantics.Diverges",
    );

    // Fault claim body missing required `Diverges` reference.
    let mut missing_fault_diverges_const = MirWpFixtureSpec::valid();
    missing_fault_diverges_const.wp_fault_soundness_claim = Some(
        "def WpFaultSoundnessClaim (_f : Nat) : Prop := And ReachesResult WellFormed".to_string(),
    );
    missing_fault_diverges_const.wp_fault_soundness_proof = Some(
        "theorem reaches_fault_and_exclusive_of_wpFault : \
         Trusted.MirSemantics.WpFaultSoundnessClaim Anneal.MirWp.wpFaultProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &missing_fault_diverges_const,
        "claim Trusted.MirSemantics.WpFaultSoundnessClaim body must reference \
         Trusted.MirSemantics.Diverges",
    );

    // Fault claim body missing required `WellFormed` reference.
    let mut missing_fault_req_const = MirWpFixtureSpec::valid();
    missing_fault_req_const.wp_fault_soundness_claim = Some(
        "def WpFaultSoundnessClaim (_f : Nat) : Prop := And ReachesResult Diverges".to_string(),
    );
    missing_fault_req_const.wp_fault_soundness_proof = Some(
        "theorem reaches_fault_and_exclusive_of_wpFault : \
         Trusted.MirSemantics.WpFaultSoundnessClaim Anneal.MirWp.wpFaultProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &missing_fault_req_const,
        "claim Trusted.MirSemantics.WpFaultSoundnessClaim body must reference \
         Trusted.MirSemantics.WellFormed",
    );

    // Missing Profile v2 `ExecSoundnessClaimV2` from `Trusted.MirSemantics`.
    let mut missing_v2_claim = MirWpFixtureSpec::valid();
    missing_v2_claim.exec_soundness_claim_v2 = None;
    missing_v2_claim.exec_soundness_proof_v2 = None;
    expect_mir_wp_audit_policy_err(
        &missing_v2_claim,
        "missing required claim Trusted.MirSemantics.ExecSoundnessClaimV2",
    );

    // Missing `wellFormed_and_spec_of_execV2`.
    let mut missing_v2_thm = MirWpFixtureSpec::valid();
    missing_v2_thm.exec_soundness_proof_v2 = None;
    expect_mir_wp_audit_policy_err(
        &missing_v2_thm,
        "missing required theorem Anneal.MirWp.wellFormed_and_spec_of_execV2",
    );

    // Weakened Profile v2 proof (`True` instead of
    // `ExecSoundnessClaimV2 execProgV2`).
    let mut weakened_v2_thm = MirWpFixtureSpec::valid();
    weakened_v2_thm.exec_soundness_proof_v2 =
        Some("theorem wellFormed_and_spec_of_execV2 : True := True.intro".to_string());
    expect_mir_wp_audit_policy_err(
        &weakened_v2_thm,
        "theorem Anneal.MirWp.wellFormed_and_spec_of_execV2 must prove \
         Trusted.MirSemantics.ExecSoundnessClaimV2 Anneal.MirWp.execProgV2 directly",
    );

    // Profile v2 claim bodies each missing one required semantic constant.
    for (body, dropped) in [
        ("And DivergesV2 BehaviorV2", "SatisfiesPostV2"),
        ("And SatisfiesPostV2 BehaviorV2", "DivergesV2"),
        ("And SatisfiesPostV2 DivergesV2", "BehaviorV2"),
    ] {
        let mut missing_v2_const = MirWpFixtureSpec::valid();
        missing_v2_const.exec_soundness_claim_v2 =
            Some(format!("def ExecSoundnessClaimV2 (_f : Nat) : Prop := {body}"));
        missing_v2_const.exec_soundness_proof_v2 = Some(
            "theorem wellFormed_and_spec_of_execV2 : \
             Trusted.MirSemantics.ExecSoundnessClaimV2 Anneal.MirWp.execProgV2 := \
             And.intro True.intro True.intro"
                .to_string(),
        );
        expect_mir_wp_audit_policy_err(
            &missing_v2_const,
            &format!(
                "claim Trusted.MirSemantics.ExecSoundnessClaimV2 body must reference \
                 Trusted.MirSemantics.{dropped}"
            ),
        );
    }

    // Missing Profile v2 `SafeContractSoundnessClaimV2`.
    let mut missing_sc_claim = MirWpFixtureSpec::valid();
    missing_sc_claim.safe_contract_soundness_claim_v2 = None;
    missing_sc_claim.safe_contract_soundness_proof_v2 = None;
    expect_mir_wp_audit_policy_err(
        &missing_sc_claim,
        "missing required claim Trusted.MirSemantics.SafeContractSoundnessClaimV2",
    );

    // Missing `safeContract_soundness_of_execV2`.
    let mut missing_sc_thm = MirWpFixtureSpec::valid();
    missing_sc_thm.safe_contract_soundness_proof_v2 = None;
    expect_mir_wp_audit_policy_err(
        &missing_sc_thm,
        "missing required theorem Anneal.MirWp.safeContract_soundness_of_execV2",
    );

    // `SafeContractSoundnessClaimV2` body missing one required constant.
    let mut missing_sc_const = MirWpFixtureSpec::valid();
    missing_sc_const.safe_contract_soundness_claim_v2 = Some(
        "def SafeContractSoundnessClaimV2 (_f : Nat) : Prop := \
         And EffectMaskV2 (And SafeContractV2 (And SafeContractV2.post \
         (And SatisfiesSafeContractV2 BodySatisfiesSafeContractV2)))"
            .to_string(),
    );
    missing_sc_const.safe_contract_soundness_proof_v2 = Some(
        "theorem safeContract_soundness_of_execV2 : \
         Trusted.MirSemantics.SafeContractSoundnessClaimV2 Anneal.MirWp.execProgV2 := \
         And.intro True.intro (And.intro True.intro (And.intro True.intro \
         (And.intro True.intro True.intro)))"
            .to_string(),
    );
    expect_mir_wp_audit_policy_err(
        &missing_sc_const,
        "claim Trusted.MirSemantics.SafeContractSoundnessClaimV2 body must reference \
         Trusted.MirSemantics.EffectMaskV2.noAbort",
    );
}

/// Verifies every rejection branch of `requireClaimProof` (exact-claim mode,
/// `argName? = none`) in `TrustedBoundary.lean` across the 25 canary claims
/// (missing claim, non-definition claim, wrong-module claim, non-`Prop` claim,
/// claim body missing required constant, missing canary theorem, non-theorem
/// proof, wrong-module proof, and weakened/wrong-type canary theorem).
#[test]
fn enforces_mir_wp_canary_claim_proof_rules() {
    // Missing canary claim from `Trusted.MirSemantics`.
    let mut missing_claim = MirWpFixtureSpec::valid();
    missing_claim.canary_claim_overrides.insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    missing_claim.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
    expect_mir_wp_audit_policy_err(
        &missing_claim,
        "missing required claim Trusted.MirSemantics.CanaryPositiveAddAnnealClaim",
    );

    // Non-definition canary claim (`inductive` instead of `def`).
    let mut non_def_claim = MirWpFixtureSpec::valid();
    non_def_claim.canary_claim_overrides.insert(
        "CanaryPositiveAddAnnealClaim".to_string(),
        Some("inductive CanaryPositiveAddAnnealClaim : Prop where\n  | intro".to_string()),
    );
    non_def_claim.canary_proof_overrides.insert(
        "canary_positive_add_anneal".to_string(),
        Some(
            "theorem canary_positive_add_anneal : \
             Trusted.MirSemantics.CanaryPositiveAddAnnealClaim := \
             Trusted.MirSemantics.CanaryPositiveAddAnnealClaim.intro"
                .to_string(),
        ),
    );
    expect_mir_wp_audit_policy_err(
        &non_def_claim,
        "expected Trusted.MirSemantics.CanaryPositiveAddAnnealClaim to be a definition",
    );

    // Canary claim defined in `Trusted.MirAst` instead of
    // `Trusted.MirSemantics`.
    let mut wrong_claim_mod = MirWpFixtureSpec::valid();
    wrong_claim_mod.canary_claim_overrides.insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    wrong_claim_mod.mir_ast_extra = "\
        namespace Trusted.MirSemantics\n\
        def CanaryPositiveAddAnnealClaim : Prop := True\n\
        end Trusted.MirSemantics"
        .to_string();
    expect_mir_wp_audit_policy_err(
        &wrong_claim_mod,
        "expected Trusted.MirSemantics.CanaryPositiveAddAnnealClaim to be defined in \
         Trusted.MirSemantics, found Trusted.MirAst",
    );

    // Canary claim declared inside decoupled `Anneal.MirWp.Canaries`
    // (rejected fail-closed by `Trusted` namespace isolation in
    // `validateRepoConstant`).
    let mut claim_in_theory = MirWpFixtureSpec::valid();
    claim_in_theory.canary_claim_overrides.insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    claim_in_theory.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
    claim_in_theory.canaries_extra = "\
        namespace Trusted.MirSemantics\n\
        def CanaryPositiveAddAnnealClaim : Prop := True\n\
        end Trusted.MirSemantics\n\
        namespace Anneal.MirWp\n\
        theorem canary_positive_add_anneal : \
            Trusted.MirSemantics.CanaryPositiveAddAnnealClaim := True.intro\n\
        end Anneal.MirWp"
        .to_string();
    expect_mir_wp_audit_policy_err(
        &claim_in_theory,
        "non-Trusted module Anneal.MirWp.Canaries cannot declare constant \
         Trusted.MirSemantics.CanaryPositiveAddAnnealClaim in Trusted namespace",
    );

    // Non-`Prop` canary claim (`Nat` instead of `Prop`).
    let mut non_prop_claim = MirWpFixtureSpec::valid();
    non_prop_claim.canary_claim_overrides.insert(
        "CanaryPositiveAddAnnealClaim".to_string(),
        Some("def CanaryPositiveAddAnnealClaim : Nat := 0".to_string()),
    );
    non_prop_claim.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
    expect_mir_wp_audit_policy_err(
        &non_prop_claim,
        "expected Trusted.MirSemantics.CanaryPositiveAddAnnealClaim to have type Prop",
    );

    // Canary claim body missing required `PositiveCanaryClaim` constant
    // (`TrustedBoundary.lean` `requireClaimProof` `reqConsts` check).
    let mut missing_req_const = MirWpFixtureSpec::valid();
    missing_req_const.canary_claim_overrides.insert(
        "CanaryPositiveAddAnnealClaim".to_string(),
        Some("def CanaryPositiveAddAnnealClaim : Prop := True".to_string()),
    );
    expect_mir_wp_audit_policy_err(
        &missing_req_const,
        "claim Trusted.MirSemantics.CanaryPositiveAddAnnealClaim body must reference \
         Trusted.MirSemantics.PositiveCanaryClaim",
    );

    // Missing canary theorem (first canary and last canary).
    let mut missing_first_canary = MirWpFixtureSpec::valid();
    missing_first_canary
        .canary_proof_overrides
        .insert("canary_positive_add_anneal".to_string(), None);
    expect_mir_wp_audit_policy_err(
        &missing_first_canary,
        "missing required theorem Anneal.MirWp.canary_positive_add_anneal",
    );

    let mut missing_last_canary = MirWpFixtureSpec::valid();
    missing_last_canary
        .canary_proof_overrides
        .insert("canary_crate_and_body_verified_anneal".to_string(), None);
    expect_mir_wp_audit_policy_err(
        &missing_last_canary,
        "missing required theorem Anneal.MirWp.canary_crate_and_body_verified_anneal",
    );

    // Non-theorem canary proof (`def` instead of `theorem`).
    let mut def_canary = MirWpFixtureSpec::valid();
    def_canary.canary_proof_overrides.insert(
        "canary_positive_add_anneal".to_string(),
        Some("def canary_positive_add_anneal : Nat := 0".to_string()),
    );
    expect_mir_wp_audit_policy_err(
        &def_canary,
        "expected Anneal.MirWp.canary_positive_add_anneal to be a theorem",
    );

    // Canary theorem defined in `Anneal.Wp` instead of `Anneal.MirWp.Canaries`.
    let mut wrong_proof_mod = MirWpFixtureSpec::valid();
    wrong_proof_mod.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
    wrong_proof_mod.anneal_extra = "\
        namespace Anneal.MirWp\n\
        theorem canary_positive_add_anneal : \
            Trusted.MirSemantics.CanaryPositiveAddAnnealClaim := True.intro\n\
        end Anneal.MirWp"
        .to_string();
    expect_mir_wp_audit_policy_err(
        &wrong_proof_mod,
        "expected Anneal.MirWp.canary_positive_add_anneal to be defined in \
         Anneal.MirWp.Canaries, found Anneal.Wp",
    );

    // Weakened / wrong-type canary theorem (`True` instead of the pinned
    // `CanaryPositiveAddAnnealClaim`).
    let mut weakened_canary = MirWpFixtureSpec::valid();
    weakened_canary.canary_proof_overrides.insert(
        "canary_positive_add_anneal".to_string(),
        Some("theorem canary_positive_add_anneal : True := True.intro".to_string()),
    );
    expect_mir_wp_audit_policy_err(
        &weakened_canary,
        "theorem Anneal.MirWp.canary_positive_add_anneal must prove \
         Trusted.MirSemantics.CanaryPositiveAddAnnealClaim directly",
    );

    // Memory-lifecycle canary claim that drops `forceAllocation` (so the
    // `.indirect`-local path is no longer exercised).
    let mut weak_memory_canary = MirWpFixtureSpec::valid();
    weak_memory_canary.canary_claim_overrides.insert(
        "CanaryMemoryLifecycleAnnealClaim".to_string(),
        Some(
            "def CanaryMemoryLifecycleAnnealClaim : Prop := \
             And PositiveCanaryClaim (And initState (And evalStep (And readBytes readBytes)))"
                .to_string(),
        ),
    );
    expect_mir_wp_audit_policy_err(
        &weak_memory_canary,
        "claim Trusted.MirSemantics.CanaryMemoryLifecycleAnnealClaim body must reference \
         Trusted.MirSemantics.forceAllocation",
    );

    // Crate/unit/body-verified, `char`, `BinOp.cmp`, overflow-pair, and
    // `IntToInt` cast canary claims that each replace one pinned constant with
    // a duplicate of another (so the operation, fixture, contract symbol, or UB
    // path is no longer exercised while the synthetic proof still type-checks).
    // Each weakened body keeps every other required constant, so the
    // rejection names exactly the dropped one.
    for (claim, weakened_body, dropped) in [
        (
            "CanaryCrateAndBodyVerifiedAnnealClaim",
            "And UnitTheorem (And UnitTheorem BodyVerified)",
            "Trusted.MirSemantics.CrateTheorem",
        ),
        (
            "CanaryCrateAndBodyVerifiedAnnealClaim",
            "And CrateTheorem (And CrateTheorem BodyVerified)",
            "Trusted.MirSemantics.UnitTheorem",
        ),
        (
            "CanaryCrateAndBodyVerifiedAnnealClaim",
            "And CrateTheorem (And UnitTheorem CrateTheorem)",
            "Trusted.MirSemantics.BodyVerified",
        ),
        (
            "CanaryPositiveCharAndCmpAnnealClaim",
            "And PositiveCanaryClaim (And mkBinOpProg (And mkBinOpProg \
             (And Trusted.MirAst.MirTy.char (And charVal \
             (And mkCmpDiscriminantProg progCharSwitch)))))",
            "Trusted.MirAst.BinOp.cmp",
        ),
        (
            "CanaryNegativeCharAndCmpAnnealClaim",
            "And NegativeCanaryClaim (And progInvalidCharConstUb \
             (And progInvalidCharConstUb (And mkBinOpProg \
             (And Trusted.MirAst.BinOp.cmp mkUnOpProg))))",
            "Trusted.MirSemantics.progInvalidCharSwitchCaseUb",
        ),
        (
            "CanaryPositiveOverflowOpsAnnealClaim",
            "And PositiveCanaryClaim (And mkBinOpProg (And overflowPairTy \
             (And Trusted.MirAst.BinOp.addWithOverflow \
             (And Trusted.MirAst.BinOp.subWithOverflow \
             Trusted.MirAst.BinOp.subWithOverflow))))",
            "Trusted.MirAst.BinOp.mulWithOverflow",
        ),
        (
            "CanaryPositiveIntToIntCastAnnealClaim",
            "And PositiveCanaryClaim (And charVal (And Trusted.MirAst.MirTy.char charVal))",
            "Trusted.MirSemantics.mkIntToIntCastProg",
        ),
        (
            "CanaryNegativeIntToIntCastAnnealClaim",
            "And NegativeCanaryClaim (And mkIntToIntCastProg \
             (And Trusted.MirAst.MirTy.char mkIntToIntCastProg))",
            "Trusted.MirSemantics.progCastUninitSourceUb",
        ),
    ] {
        let mut weak_canary = MirWpFixtureSpec::valid();
        weak_canary.canary_claim_overrides.insert(
            claim.to_string(),
            Some(format!("def {claim} : Prop := {weakened_body}")),
        );
        expect_mir_wp_audit_policy_err(
            &weak_canary,
            &format!("claim Trusted.MirSemantics.{claim} body must reference {dropped}"),
        );
    }

    // Missing, non-definition, non-abbrev, wrong-module, universe-polymorphic,
    // or un-wired `Trusted.{Crate, CrateTheorem, UnitTheorem}` public aliases
    // and their Profile v2 counterparts are rejected fail-closed by
    // `verifyMirWpCoreTheorems`.
    for alias in [
        "Crate",
        "CrateTheorem",
        "UnitTheorem",
        "CrateV2",
        "CrateTheoremV2",
        "UnitTheoremV2",
    ] {
        let mut missing_alias = MirWpFixtureSpec::valid();
        missing_alias.public_alias_overrides.insert(alias.to_string(), None);
        expect_mir_wp_audit_policy_err(
            &missing_alias,
            &format!("missing required MIR public alias Trusted.{alias}"),
        );

        let mut non_abbrev_alias = MirWpFixtureSpec::valid();
        non_abbrev_alias.public_alias_overrides.insert(
            alias.to_string(),
            Some(format!("def {alias} := Trusted.MirSemantics.{alias}")),
        );
        expect_mir_wp_audit_policy_err(
            &non_abbrev_alias,
            &format!("alias Trusted.{alias} must be an abbrev (ReducibilityHints.abbrev)"),
        );

        let mut rewired_alias = MirWpFixtureSpec::valid();
        rewired_alias
            .public_alias_overrides
            .insert(alias.to_string(), Some(format!("abbrev {alias} : Prop := True")));
        expect_mir_wp_audit_policy_err(
            &rewired_alias,
            &format!("alias Trusted.{alias} must directly alias Trusted.MirSemantics.{alias}"),
        );

        let mut non_def_alias = MirWpFixtureSpec::valid();
        non_def_alias
            .public_alias_overrides
            .insert(alias.to_string(), Some(format!("theorem {alias} : True := True.intro")));
        expect_mir_wp_audit_policy_err(
            &non_def_alias,
            &format!("expected Trusted.{alias} to be a definition"),
        );

        let mut poly_alias = MirWpFixtureSpec::valid();
        poly_alias.public_alias_overrides.insert(
            alias.to_string(),
            Some(format!("abbrev {alias}.{{u}} : Type u → Prop := fun _ => True")),
        );
        expect_mir_wp_audit_policy_err(
            &poly_alias,
            &format!("alias Trusted.{alias} must have no universe parameters"),
        );
    }

    let mut wrong_mod_alias = MirWpFixtureSpec::valid();
    wrong_mod_alias.public_alias_overrides.insert("UnitTheorem".to_string(), None);
    wrong_mod_alias.mir_ast_extra = "\
        namespace Trusted\n\
        abbrev UnitTheorem : Prop := True\n\
        end Trusted"
        .to_string();
    expect_mir_wp_audit_policy_err(
        &wrong_mod_alias,
        "expected Trusted.UnitTheorem to be defined in Trusted.MirSemantics, found Trusted.MirAst",
    );

    let mut cross_wired_alias = MirWpFixtureSpec::valid();
    cross_wired_alias.public_alias_overrides.insert(
        "UnitTheorem".to_string(),
        Some("noncomputable abbrev UnitTheorem := Trusted.MirSemantics.CrateTheorem".to_string()),
    );
    expect_mir_wp_audit_policy_err(
        &cross_wired_alias,
        "alias Trusted.UnitTheorem must directly alias Trusted.MirSemantics.UnitTheorem",
    );

    // A Profile v2 alias wired to its Profile v1 counterpart is rejected.
    for (alias, v1_target) in [
        ("CrateV2", "Crate"),
        ("CrateTheoremV2", "CrateTheorem"),
        ("UnitTheoremV2", "UnitTheorem"),
    ] {
        let mut v1_wired_alias = MirWpFixtureSpec::valid();
        v1_wired_alias.public_alias_overrides.insert(
            alias.to_string(),
            Some(format!(
                "noncomputable abbrev {alias} := Trusted.MirSemantics.{v1_target}"
            )),
        );
        expect_mir_wp_audit_policy_err(
            &v1_wired_alias,
            &format!("alias Trusted.{alias} must directly alias Trusted.MirSemantics.{alias}"),
        );
    }
}

/// Verifies Pass 2 non-backsliding enforcement (`--require-correspondence`):
/// missing correspondence directories, `verifyCorrespondenceClaims` across all
/// 38 required claims (including `CorrespondenceAtChoicesClaim`,
/// `FaultEquivalenceAtChoicesClaim`, `OperandMachine.evalOperand` wiring,
/// `RefStepSoundForAllowedStepClaim`, `BytesCodecMatchesMiriClaim`, and the
/// `D14`–`D17` `char`/`cmp`, cast, overflow, and call canaries), and
/// `verifyRefEvaluatorIndependence`
/// (all 39 required live `ExecutionMachine` Miri primitives on
/// `[evalRefStep, initRefState]` unmasked by `RefAllowedStep`,
/// `ExecutionMachine.AllowedStep` on `RefAllowedStep`, module-level import
/// isolation and modular placement checks on isolated
/// `Trusted.Correspondence.*` evaluator submodules, and rejection of
/// disallowed `Trusted` declarations).
#[test]
fn enforces_correspondence_non_backsliding() {
    // 1. When `require_correspondence` is enabled and correspondence
    // directories are absent, `Checker::run` rejects in `"correspondence"`.
    let fix_missing_corr = TempFixture::new(None);
    let mut checker = fix_missing_corr.checker();
    checker.set_require_mir_wp(false);
    checker.set_require_correspondence(true);
    assert_policy_rejection(
        checker.run(),
        "correspondence",
        "missing required correspondence directories",
    );

    // 2. Pass 2 (`InspectorRequest::CorrespondenceAudit`) enforces
    // `verifyCorrespondenceClaims` (required constant references across all 38
    // claims and exact claim-type proof checking) and
    // `verifyRefEvaluatorIndependence` (39 live `ExecutionMachine` Miri
    // primitives on `[evalRefStep, initRefState]` without `RefAllowedStep`
    // masking, `AllowedStep` on `RefAllowedStep`, fail-closed module-level
    // import isolation and modular placement checks on isolated
    // `Trusted.Correspondence.*` evaluator submodules, and closed
    // module-origin isolation across both cones).
    let mut harness = CorrespondenceHarness::new();

    // 2a. Weakened `CorrespondenceClaim` (drops `WellFormed`).
    harness.compile_trusted(
        &[],
        "Trusted.Correspondence",
        "prelude\nimport Init.Core\n\
         namespace Trusted.Correspondence\n\
         def CorrespondenceClaim : Prop := True\n\
         end Trusted.Correspondence\n",
    );
    harness.compile_corr_proof(
        &["Trusted.Correspondence"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Trusted.Correspondence\n\
         namespace Anneal.MirCorrespondenceProof\n\
         theorem correspondence_claim_holds : Trusted.Correspondence.CorrespondenceClaim := True.intro\n\
         end Anneal.MirCorrespondenceProof\n",
    );
    harness.assert_default_rejected(
        "claim Trusted.Correspondence.CorrespondenceClaim body must reference Trusted.MirSemantics.WellFormed",
    );

    // 2a-ii. Weakened choices, wiring, canary, and codec claims fail closed.
    let valid_claims_text = ClaimsSpec::valid().render();
    let valid_proofs = ProofsSpec::valid();
    let claim_weakenings: Vec<(ClaimsSpec, ProofsSpec, &str)> = vec![
        (
            ClaimsSpec { corr_choices: Some("True".to_string()), ..ClaimsSpec::valid() },
            ProofsSpec { corr_choices: "True.intro".to_string(), ..valid_proofs.clone() },
            "claim Trusted.Correspondence.CorrespondenceAtChoicesClaim body must reference Trusted.MirSemantics.WellFormed",
        ),
        (
            ClaimsSpec { fault_choices: Some("True".to_string()), ..ClaimsSpec::valid() },
            ProofsSpec { fault_choices: "True.intro".to_string(), ..valid_proofs.clone() },
            "claim Trusted.Correspondence.FaultEquivalenceAtChoicesClaim body must reference Trusted.MirSemantics.ReachesResultAtChoices",
        ),
        (
            ClaimsSpec {
                wiring: Some(
                    "Miri.Interpreter.ExecutionMachine.step = Miri.Interpreter.ExecutionMachine.stepHooks ∧\n\
                     Miri.Interpreter.Step.step = Miri.Interpreter.ExecutionMachine.withValidation ∧\n\
                     Miri.Interpreter.ExecutionMachine.operandHooks = Miri.Interpreter.evalOperand ∧\n\
                     Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit = Miri.Interpreter.MachineHooks.recordPendingMoveDeinit ∧\n\
                     Miri.Interpreter.FnArg.copyFnArg = Miri.Interpreter.Call.deinitInPlaceArg"
                        .to_string(),
                ),
                ..ClaimsSpec::valid()
            },
            ProofsSpec {
                wiring: "⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩".to_string(),
                ..valid_proofs.clone()
            },
            "claim Trusted.Correspondence.MiriMoveDeinitWiringClaim body must reference Miri.Interpreter.OperandMachine.evalOperand",
        ),
        (
            ClaimsSpec { d6: Some("True".to_string()), ..ClaimsSpec::valid() },
            ProofsSpec { d6: "True.intro".to_string(), ..valid_proofs.clone() },
            "claim Trusted.Correspondence.CanaryD6UseAfterMoveUbClaim body must reference Trusted.Correspondence.progUseAfterMoveD6",
        ),
        (
            ClaimsSpec { ref_step_allowed: Some("True".to_string()), ..ClaimsSpec::valid() },
            ProofsSpec { ref_step_allowed: "True.intro".to_string(), ..valid_proofs.clone() },
            "claim Trusted.Correspondence.RefStepSoundForAllowedStepClaim body must reference Trusted.Correspondence.RefStep",
        ),
        (
            ClaimsSpec::valid().with_replace(
                VALID_BYTES_CODEC_DEF,
                "def BytesCodecMatchesMiriClaim : Prop :=\n\
                 Miri.Memory.Allocation.writeScalar = Miri.Memory.Allocation.readScalar\n",
            ),
            ProofsSpec { bytes_codec: "Eq.refl _".to_string(), ..valid_proofs.clone() },
            "claim Trusted.Correspondence.BytesCodecMatchesMiriClaim body must reference Trusted.MirSemantics.encodeVal",
        ),
    ];
    for (claims, proofs, expected) in claim_weakenings {
        harness.publish(&claims, &proofs);
        harness.assert_default_rejected(expected);
    }

    // Weakening D11–D13 canary claims by dropping required fixtures/predicates.
    for (claim, valid_def, old_tok, replacement_tok, dropped) in [
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "Trusted.MirSemantics.progEnumExplicitReprU8",
            "Trusted.MirSemantics.progEnumSignedTagIsize",
            "Trusted.MirSemantics.progEnumExplicitReprU8",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "Trusted.MirSemantics.progEnumSignedTagIsize",
            "Trusted.MirSemantics.progEnumExplicitReprU8",
            "Trusted.MirSemantics.progEnumSignedTagIsize",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.Behavior",
            "Trusted.MirSemantics.WellFormed",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "Trusted.MirSemantics.Behavior",
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.Behavior",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "RefWellFormed",
            "RefBehavior",
            "Trusted.Correspondence.RefWellFormed",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "RefBehavior",
            "RefWellFormed",
            "Trusted.Correspondence.RefBehavior",
        ),
        (
            "CanaryD11EnumDiscriminantAndConstOkClaim",
            VALID_D11_DEF,
            "encodeProg = encodeProg",
            "Trusted.MirSemantics.progEnumExplicitReprU8 = Trusted.MirSemantics.progEnumExplicitReprU8",
            "Trusted.Correspondence.encodeProg",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "Trusted.MirSemantics.progZstSingleEnumImplicitRet",
            "Trusted.MirSemantics.progZstSingleEnumMoveAndDiscr",
            "Trusted.MirSemantics.progZstSingleEnumImplicitRet",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "Trusted.MirSemantics.progZstSingleEnumMoveAndDiscr",
            "Trusted.MirSemantics.progZstSingleEnumImplicitRet",
            "Trusted.MirSemantics.progZstSingleEnumMoveAndDiscr",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.Behavior",
            "Trusted.MirSemantics.WellFormed",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "Trusted.MirSemantics.Behavior",
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.Behavior",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "RefWellFormed",
            "RefBehavior",
            "Trusted.Correspondence.RefWellFormed",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "RefBehavior",
            "RefWellFormed",
            "Trusted.Correspondence.RefBehavior",
        ),
        (
            "CanaryD12ZstEnumMoveAndDiscrOkClaim",
            VALID_D12_DEF,
            "encodeProg = encodeProg",
            "Trusted.MirSemantics.progZstSingleEnumImplicitRet = Trusted.MirSemantics.progZstSingleEnumImplicitRet",
            "Trusted.Correspondence.encodeProg",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "Trusted.MirSemantics.progEnumInvalidTagConstUb",
            "Trusted.MirSemantics.progEnumUninitDiscrUb",
            "Trusted.MirSemantics.progEnumInvalidTagConstUb",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "Trusted.MirSemantics.progEnumUninitDiscrUb",
            "Trusted.MirSemantics.progEnumInvalidTagConstUb",
            "Trusted.MirSemantics.progEnumUninitDiscrUb",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "Trusted.MirSemantics.ReachesResult",
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.ReachesResult",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "Trusted.MirSemantics.WellFormed",
            "Trusted.MirSemantics.ReachesResult",
            "Trusted.MirSemantics.WellFormed",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "RefReachesOutcome",
            "Trusted.MirSemantics.WellFormed",
            "Trusted.Correspondence.RefReachesOutcome",
        ),
        (
            "CanaryD13EnumInvalidTagAndUninitUbClaim",
            VALID_D13_DEF,
            "encodeProg = encodeProg",
            "Trusted.MirSemantics.progEnumInvalidTagConstUb = Trusted.MirSemantics.progEnumInvalidTagConstUb",
            "Trusted.Correspondence.encodeProg",
        ),
    ] {
        assert_eq!(valid_claims_text.matches(valid_def).count(), 1, "synthetic {claim} drifted");
        assert_eq!(valid_def.matches(old_tok).count(), 1, "expected unique {old_tok} in {claim}");
        let weakened_def = valid_def.replace(old_tok, replacement_tok);
        harness.publish(&ClaimsSpec::valid().with_replace(valid_def, weakened_def), &valid_proofs);
        harness.assert_default_rejected(&format!(
            "claim Trusted.Correspondence.{claim} body must reference {dropped}"
        ));
    }

    // Weakening D14–D17 canary claims fails closed.
    for (claim, valid_conjunct, weakened_conjunct, dropped) in [
        (
            "CanaryD14CharCmpAndSwitchOkClaim",
            "Trusted.MirAst.BinOp.cmp = Trusted.MirAst.MirTy.char ∧",
            "Trusted.MirAst.MirTy.char = Trusted.MirAst.MirTy.char ∧",
            "Trusted.MirAst.BinOp.cmp",
        ),
        (
            "CanaryD15IntToIntCastClaim",
            "Trusted.MirSemantics.mkIntToIntCastProg = Trusted.MirAst.MirTy.char ∧",
            "Trusted.MirAst.MirTy.char = Trusted.MirAst.MirTy.char ∧",
            "Trusted.MirSemantics.mkIntToIntCastProg",
        ),
        (
            "CanaryD16WithOverflowOkClaim",
            "Trusted.MirAst.BinOp.addWithOverflow = Trusted.MirAst.BinOp.subWithOverflow ∧",
            "Trusted.MirAst.BinOp.subWithOverflow = Trusted.MirAst.BinOp.subWithOverflow ∧",
            "Trusted.MirAst.BinOp.addWithOverflow",
        ),
        (
            "CanaryD17CallAndSysrootCallClaim",
            "progDirectCallD17 = progSysrootUncheckedAddOkD17 ∧",
            "progSysrootUncheckedAddOkD17 = progSysrootUncheckedAddOkD17 ∧",
            "Trusted.Correspondence.progDirectCallD17",
        ),
        (
            "CanaryD17CallAndSysrootCallClaim",
            "queryU16_19 = Trusted.MirSemantics.queryEmpty ∧",
            "queryU16_19 = queryU16_19 ∧",
            "Trusted.MirSemantics.queryEmpty",
        ),
        (
            "CanaryD17AssertPanicAbortClaim",
            "Trusted.MirAst.PanicStrategy.abort = Trusted.MirAst.PanicStrategy.unwind ∧",
            "Trusted.MirAst.PanicStrategy.unwind = Trusted.MirAst.PanicStrategy.unwind ∧",
            "Trusted.MirAst.PanicStrategy.abort",
        ),
    ] {
        harness.publish(
            &ClaimsSpec::valid().with_replace(valid_conjunct, weakened_conjunct),
            &valid_proofs,
        );
        harness.assert_default_rejected(&format!(
            "claim Trusted.Correspondence.{claim} body must reference {dropped}"
        ));
    }

    // 2b. `verifyRefEvaluatorIndependence` requires all 39 Miri primitives.
    harness.publish(&ClaimsSpec::valid(), &valid_proofs);
    harness.assert_default_rejected(
        "reference evaluator cone is missing required Miri primitive Miri.Interpreter.ExecutionMachine.step",
    );

    for missing_miri in [
        "Miri.Interpreter.ExecutionMachine.step",
        "Miri.Interpreter.OperandMachine.evalOperand",
        "Miri.Interpreter.ValidityVisitor.validatePlace",
        "Miri.Interpreter.Discriminant.readDiscriminant",
        "Miri.Interpreter.Discriminant.discriminantForVariant",
        "Miri.Interpreter.IntegerOps.binaryChar",
        "Miri.Interpreter.Cast.cast",
        "Miri.Interpreter.IntegerCast.cast",
        "Miri.Memory.ScalarInt.toChar",
        "Miri.Memory.ScalarInt.ofChar",
    ] {
        let kept = REQUIRED_MIRI_PRIMITIVES
            .iter()
            .copied()
            .filter(|prim| *prim != missing_miri)
            .collect::<Vec<_>>()
            .join(", ");
        harness.publish(
            &ClaimsSpec::valid().with_eval_ref_step(format!("let _ := ({kept}); 0")),
            &valid_proofs,
        );
        harness.assert_default_rejected(&format!(
            "reference evaluator cone is missing required Miri primitive {missing_miri}"
        ));
    }

    let all_miri_tuple = REQUIRED_MIRI_PRIMITIVES.join(", ");

    // 2b-ii. `RefAllowedStep` cannot mask omitting `ExecutionMachine.step`.
    harness.publish(
        &ClaimsSpec::valid().with_ref_allowed_step(format!(
            "let _ := ({all_miri_tuple}, Miri.Interpreter.ExecutionMachine.AllowedStep); 0"
        )),
        &valid_proofs,
    );
    harness.assert_default_rejected(
        "reference evaluator cone is missing required Miri primitive Miri.Interpreter.ExecutionMachine.step",
    );

    // 2b-iii. `RefAllowedStep` itself must reach `AllowedStep`.
    harness.publish(
        &ClaimsSpec::valid()
            .with_eval_ref_step(format!("let _ := ({all_miri_tuple}); 0"))
            .with_ref_allowed_step("0"),
        &valid_proofs,
    );
    harness.assert_default_rejected(
        "RefAllowedStep cone is missing required Miri primitive Miri.Interpreter.ExecutionMachine.AllowedStep",
    );

    // Reference evaluator cone must not reference disallowed `Trusted` decls.
    for (init_expr, step_expr, expected_const, expected_mod) in [
        (
            "0",
            "Trusted.MirSemantics.evalStep",
            "Trusted.MirSemantics.evalStep",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.evalArithOp",
            "Trusted.MirSemantics.evalArithOp",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.evalShiftOp",
            "Trusted.MirSemantics.evalShiftOp",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.jumpToBlock",
            "Trusted.MirSemantics.jumpToBlock",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.enumAdmitted",
            "Trusted.MirSemantics.enumAdmitted",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.tagBitsToDiscrBits",
            "Trusted.MirSemantics.tagBitsToDiscrBits",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.isZstEnumTy",
            "Trusted.MirSemantics.isZstEnumTy",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.findDiscrVariant?",
            "Trusted.MirSemantics.findDiscrVariant?",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.unlistedAnnealHelper",
            "Trusted.MirSemantics.unlistedAnnealHelper",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "Trusted.MirSemantics.subEvalHelper",
            "Trusted.MirSemantics.subEvalHelper",
            "Trusted.MirSemantics.SubHelper",
        ),
        (
            "0",
            "Trusted.MirHelper.siblingHelper",
            "Trusted.MirHelper.siblingHelper",
            "Trusted.MirHelper",
        ),
        (
            "Trusted.MirSemantics.initState",
            "0",
            "Trusted.MirSemantics.initState",
            "Trusted.MirSemantics",
        ),
        (
            "0",
            "transitiveSubHelper",
            "Trusted.MirSemantics.subEvalHelper",
            "Trusted.MirSemantics.SubHelper",
        ),
    ] {
        harness.publish(
            &ClaimsSpec::valid()
                .with_init_ref_state(init_expr)
                .with_eval_ref_step(format!("let _ := ({all_miri_tuple}); {step_expr}")),
            &valid_proofs,
        );
        harness.assert_default_rejected(&format!(
            "reference evaluator cone illegally references disallowed Trusted declaration {expected_const} (defined in {expected_mod})"
        ));
    }

    // Referencing shared boundary data in `Trusted.MirModel` is admitted.
    harness.publish(
        &ClaimsSpec::valid().with_eval_ref_step(format!(
            "let _ := ({all_miri_tuple}); Trusted.MirSemantics.sharedModelData"
        )),
        &valid_proofs,
    );
    let ok_req = harness.base_request().build();
    harness
        .run_audit(ok_req)
        .expect("Trusted.MirModel boundary data should be admitted in reference evaluator cone");

    // 2c. Module import isolation: dead import in `Correspondence.Eval` fails.
    harness.compile_trusted(
        &["Trusted.MirSemantics"],
        "Trusted.Correspondence.Eval",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Trusted.Correspondence\ndef deadImportMarker : Nat := 0\nend Trusted.Correspondence\n",
    );
    let dead_req = CorrAuditRequestBuilder::empty(harness.search_paths.clone())
        .with_trusted_vetted("Trusted")
        .with_trusted_candidate("Trusted.MirModel")
        .with_trusted_candidate("Trusted.MirHelper")
        .with_trusted_candidate("Trusted.MirSemantics")
        .with_trusted_candidate("Trusted.MirSemantics.SubHelper")
        .with_corr_trusted_candidate("Trusted.Correspondence.Eval")
        .with_corr_trusted_candidate("Trusted.Correspondence")
        .with_corr_theory("Anneal.MirCorrespondenceProof")
        .with_vendor_miri("Miri.FakeStubs")
        .build();
    assert_policy_rejection(
        harness.run_audit(dead_req),
        "correspondence-audit",
        "reference evaluator module Trusted.Correspondence.Eval illegally imports disallowed module Trusted.MirSemantics",
    );

    // 2d. Transitive module import isolation via allowlisted module fails.
    harness.compile_trusted(
        &["Trusted.MirHelper"],
        "Trusted.MirAst.Decoy",
        "prelude\nimport Init.Core\nimport Trusted.MirHelper\n\
         namespace Trusted.MirAst\ndef decoyMarker : Nat := 0\nend Trusted.MirAst\n",
    );
    harness.compile_trusted(
        &["Trusted.MirAst.Decoy"],
        "Trusted.Correspondence.Eval",
        "prelude\nimport Init.Core\nimport Trusted.MirAst.Decoy\n\
         namespace Trusted.Correspondence\ndef transitiveDeadImportMarker : Nat := 0\nend Trusted.Correspondence\n",
    );
    let trans_req = CorrAuditRequestBuilder::empty(harness.search_paths.clone())
        .with_trusted_vetted("Trusted")
        .with_trusted_candidate("Trusted.MirModel")
        .with_trusted_candidate("Trusted.MirHelper")
        .with_trusted_candidate("Trusted.MirAst.Decoy")
        .with_trusted_candidate("Trusted.MirSemantics")
        .with_trusted_candidate("Trusted.MirSemantics.SubHelper")
        .with_corr_trusted_candidate("Trusted.Correspondence.Eval")
        .with_corr_trusted_candidate("Trusted.Correspondence")
        .with_corr_theory("Anneal.MirCorrespondenceProof")
        .with_vendor_miri("Miri.FakeStubs")
        .build();
    assert_policy_rejection(
        harness.run_audit(trans_req),
        "correspondence-audit",
        "reference evaluator module Trusted.Correspondence.Eval illegally imports disallowed module Trusted.MirHelper (via Trusted.MirAst.Decoy)",
    );

    // 2e. Placement check rejects `evalRefStep` in `Trusted.Correspondence`.
    harness.compile_trusted(
        &[],
        "Trusted.Correspondence.Eval",
        "prelude\nimport Init.Core\n\
         namespace Trusted.Correspondence\ndef cleanEvalMarker : Nat := 0\nend Trusted.Correspondence\n",
    );
    let misplaced_req = CorrAuditRequestBuilder::empty(harness.search_paths.clone())
        .with_trusted_vetted("Trusted")
        .with_trusted_candidate("Trusted.MirModel")
        .with_trusted_candidate("Trusted.MirHelper")
        .with_trusted_candidate("Trusted.MirSemantics")
        .with_trusted_candidate("Trusted.MirSemantics.SubHelper")
        .with_corr_trusted_candidate("Trusted.Correspondence.Eval")
        .with_corr_trusted_candidate("Trusted.Correspondence")
        .with_corr_theory("Anneal.MirCorrespondenceProof")
        .with_vendor_miri("Miri.FakeStubs")
        .build();
    assert_policy_rejection(
        harness.run_audit(misplaced_req),
        "correspondence-audit",
        "modular correspondence layout requires reference evaluator symbol Trusted.Correspondence.evalRefStep to be defined in an isolated evaluator module, found Trusted.Correspondence",
    );
}

/// Verifies the vendored `.olean` cache and compilation pipeline in
/// [`Checker::verify_and_stage_miri_entries`]:
/// 1. Staged source digest mismatch fails closed before consulting the cache or
///    invoking Lean.
/// 2. Compiled `.olean` digest mismatch fails closed and writes zero files to
///    the cache directory (write-after-verify).
/// 3. Cold compilation populates the cache with verified digests.
/// 4. Digest-gated cache restore succeeds without recompiling.
/// 5. Tampered cached `.olean` bytes are rejected (never blindly accepted),
///    forcing recompilation and healing the cache when valid source exists.
/// 6. Missing, mismatched, and unexpected compiled `.olean.server` /
///    `.olean.private` sidecars all fail closed with policy exit code `1`.
#[test]
fn verifies_miri_cache_and_rejects_unverified_oleans() {
    let fix = TempFixture::new(None);
    let cache_root = tempfile::Builder::new().prefix("anneal-miri-cache-test-").tempdir().unwrap();
    let vendor_dir = fix.root.join("fake-vendor");
    let src_path = vendor_dir.join("Miri/Tiny.lean");
    fs::create_dir_all(src_path.parent().unwrap()).unwrap();
    let valid_src =
        "prelude\nimport Init.Core\nnamespace Miri.Tiny\ndef x : Nat := 1\nend Miri.Tiny\n";
    let valid_src_sha = sha256_bytes(valid_src.as_bytes());
    let valid_sources = BTreeMap::from([("Miri/Tiny.lean".to_string(), valid_src_sha)]);
    fs::write(&src_path, valid_src).unwrap();

    // Compile once in a probe checker to obtain the deterministic `.olean`
    // companion digests for `Miri.Tiny`.
    let mut probe = fix.checker();
    probe.set_require_mir_wp(false);
    probe.run().unwrap();
    let probe_out = probe.stage().join("probe-lib/Miri/Tiny.olean");
    fs::create_dir_all(probe_out.parent().unwrap()).unwrap();
    probe
        .process(
            "probe-miri-tiny",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_out.to_string_lossy().into_owned(),
                src_path.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let expected_olean = sha256_file(&probe_out, "test").unwrap();
    let probe_server = probe.stage().join("probe-lib/Miri/Tiny.olean.server");
    let expected_server =
        probe_server.exists().then(|| sha256_file(&probe_server, "test").unwrap());
    let probe_private = probe.stage().join("probe-lib/Miri/Tiny.olean.private");
    let expected_private =
        probe_private.exists().then(|| sha256_file(&probe_private, "test").unwrap());

    let good_entry = MiriClosureEntry {
        module: "Miri.Tiny".to_string(),
        path: "Miri/Tiny.lean".to_string(),
        olean_sha256: expected_olean.clone(),
        olean_server_sha256: expected_server.clone(),
        olean_private_sha256: expected_private.clone(),
    };

    // Case 0: Staged source SHA-256 mismatch fails closed with exit code `1`.
    let wrong_sources = BTreeMap::from([("Miri/Tiny.lean".to_string(), "1".repeat(64))]);
    let mut c0 = fix.checker();
    c0.set_require_mir_wp(false);
    c0.run().unwrap();
    let err_src_sha = c0
        .verify_and_stage_miri_entries(
            &vendor_dir,
            std::slice::from_ref(&good_entry),
            &wrong_sources,
        )
        .unwrap_err();
    assert_eq!(err_src_sha.code, 1, "expected policy error: {err_src_sha}");
    assert!(
        err_src_sha.message.contains("staged Miri source SHA-256 mismatch for Miri/Tiny.lean"),
        "unexpected source-mismatch error: {err_src_sha}"
    );

    // Case 1: Compiled `.olean` digest mismatch fails closed AND writes
    // nothing into the empty cache directory (write-after-verify invariant).
    let cache_mismatch = cache_root.path().join("cache-mismatch");
    fs::create_dir_all(&cache_mismatch).unwrap();
    let mut bad_entry = good_entry.clone();
    bad_entry.olean_sha256 = "0".repeat(64);
    let mut c1 = fix.checker();
    c1.set_require_mir_wp(false);
    c1.set_miri_cache_dir(Some(cache_mismatch.clone()));
    c1.run().unwrap();
    let err =
        c1.verify_and_stage_miri_entries(&vendor_dir, &[bad_entry], &valid_sources).unwrap_err();
    assert_eq!(err.code, 1, "expected policy error: {err}");
    assert!(
        err.message.contains("compiled Miri .olean SHA-256 mismatch for Miri.Tiny"),
        "unexpected mismatch error: {err}"
    );
    assert!(
        !cache_mismatch.join("Miri/Tiny.olean").exists(),
        "unverified .olean must never be written to cache"
    );

    // Case 2: Cold compile verifies digests and populates the cache.
    let cache_dir = cache_root.path().join("cache-live");
    fs::create_dir_all(&cache_dir).unwrap();
    let mut c2 = fix.checker();
    c2.set_require_mir_wp(false);
    c2.set_miri_cache_dir(Some(cache_dir.clone()));
    c2.run().unwrap();
    c2.verify_and_stage_miri_entries(
        &vendor_dir,
        std::slice::from_ref(&good_entry),
        &valid_sources,
    )
    .unwrap();
    let cached_olean = cache_dir.join("Miri/Tiny.olean");
    assert_eq!(
        sha256_file(&cached_olean, "test").unwrap(),
        expected_olean,
        "cached .olean digest must match verified output"
    );

    // Case 3: Digest-gated cache hit restores `.olean` without compiling
    // source (proven by temporarily replacing source with invalid Lean while
    // updating the expected source digest so staging succeeds).
    let invalid_src = "this is intentionally invalid lean syntax !!!\n";
    let invalid_sources =
        BTreeMap::from([("Miri/Tiny.lean".to_string(), sha256_bytes(invalid_src.as_bytes()))]);
    fs::write(&src_path, invalid_src).unwrap();
    let mut c3 = fix.checker();
    c3.set_require_mir_wp(false);
    c3.set_miri_cache_dir(Some(cache_dir.clone()));
    c3.run().unwrap();
    c3.verify_and_stage_miri_entries(
        &vendor_dir,
        std::slice::from_ref(&good_entry),
        &invalid_sources,
    )
    .unwrap();

    // Case 4a: Tampered cached `.olean` is rejected (cannot serve cache hit;
    // with invalid source present, fallback compilation fails closed).
    let mut bytes = fs::read(&cached_olean).unwrap();
    bytes[0] ^= 0xFF;
    fs::write(&cached_olean, &bytes).unwrap();
    let mut c4a = fix.checker();
    c4a.set_require_mir_wp(false);
    c4a.set_miri_cache_dir(Some(cache_dir.clone()));
    c4a.run().unwrap();
    let err_tampered = c4a
        .verify_and_stage_miri_entries(
            &vendor_dir,
            std::slice::from_ref(&good_entry),
            &invalid_sources,
        )
        .unwrap_err();
    assert!(
        err_tampered.phase.contains("compile-Miri.Tiny"),
        "tampered cached .olean must trigger recompile, got: {err_tampered}"
    );

    // Case 4b: With valid source restored, tampered cache entry is bypassed,
    // recompiled, re-verified, and healed on disk.
    fs::write(&src_path, valid_src).unwrap();
    let mut c4b = fix.checker();
    c4b.set_require_mir_wp(false);
    c4b.set_miri_cache_dir(Some(cache_dir.clone()));
    c4b.run().unwrap();
    c4b.verify_and_stage_miri_entries(
        &vendor_dir,
        std::slice::from_ref(&good_entry),
        &valid_sources,
    )
    .unwrap();
    assert_eq!(
        sha256_file(&cached_olean, "test").unwrap(),
        expected_olean,
        "healed cache entry must match pinned digest"
    );

    // Case 5: Missing expected `.olean.server` sidecar fails closed without
    // contaminating a fresh cache directory.
    let cache_sidecar = cache_root.path().join("cache-sidecar");
    fs::create_dir_all(&cache_sidecar).unwrap();
    let mut bad_sidecar = good_entry;
    bad_sidecar.olean_server_sha256 = Some("f".repeat(64));
    let mut c5 = fix.checker();
    c5.set_require_mir_wp(false);
    c5.set_miri_cache_dir(Some(cache_sidecar.clone()));
    c5.run().unwrap();
    let err_sidecar =
        c5.verify_and_stage_miri_entries(&vendor_dir, &[bad_sidecar], &valid_sources).unwrap_err();
    assert_eq!(err_sidecar.code, 1, "expected policy error: {err_sidecar}");
    assert!(
        err_sidecar.message.contains("missing compiled Miri .olean.server sidecar for Miri.Tiny"),
        "unexpected missing-sidecar error: {err_sidecar}"
    );
    assert!(
        !cache_sidecar.join("Miri/Tiny.olean").exists(),
        "sidecar mismatch must not write to cache"
    );

    // Case 6: Unexpected compiled `.olean.server` / `.olean.private` sidecar
    // (present on disk when `UPSTREAM_PIN.json` expects `None`) and sidecar
    // SHA-256 mismatch both fail closed with policy exit code `1`.
    let mod_path = vendor_dir.join("Miri/WithSidecar.lean");
    let mod_src = "module\nprelude\npublic import Init.Core\n\
                   namespace Miri.WithSidecar\npublic def x : Nat := 1\n\
                   end Miri.WithSidecar\n";
    let mod_sources =
        BTreeMap::from([("Miri/WithSidecar.lean".to_string(), sha256_bytes(mod_src.as_bytes()))]);
    fs::write(&mod_path, mod_src).unwrap();
    let probe_mod_out = probe.stage().join("probe-lib/Miri/WithSidecar.olean");
    probe
        .process(
            "probe-miri-sidecar",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_mod_out.to_string_lossy().into_owned(),
                mod_path.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let mod_olean = sha256_file(&probe_mod_out, "test").unwrap();
    let mod_server = probe.stage().join("probe-lib/Miri/WithSidecar.olean.server");
    let mod_private = probe.stage().join("probe-lib/Miri/WithSidecar.olean.private");
    assert!(
        mod_server.exists(),
        "Lean `module` fixture must emit .olean.server to exercise sidecar checks"
    );
    let mod_server_sha = sha256_file(&mod_server, "test").unwrap();
    let mod_private_sha = mod_private.exists().then(|| sha256_file(&mod_private, "test").unwrap());

    // 6a. Unexpected `.olean.server` when entry expects `None`.
    let unexpected_server = MiriClosureEntry {
        module: "Miri.WithSidecar".to_string(),
        path: "Miri/WithSidecar.lean".to_string(),
        olean_sha256: mod_olean.clone(),
        olean_server_sha256: None,
        olean_private_sha256: mod_private_sha.clone(),
    };
    let mut c6a = fix.checker();
    c6a.set_require_mir_wp(false);
    c6a.run().unwrap();
    let err_unexpected_server = c6a
        .verify_and_stage_miri_entries(&vendor_dir, &[unexpected_server], &mod_sources)
        .unwrap_err();
    assert_eq!(err_unexpected_server.code, 1, "expected policy error: {err_unexpected_server}");
    assert!(
        err_unexpected_server
            .message
            .contains("unexpected Miri .olean.server sidecar for Miri.WithSidecar"),
        "unexpected sidecar error: {err_unexpected_server}"
    );

    // 6b. Mismatched `.olean.server` SHA-256 when entry expects `Some(...)`.
    let mismatched_server = MiriClosureEntry {
        module: "Miri.WithSidecar".to_string(),
        path: "Miri/WithSidecar.lean".to_string(),
        olean_sha256: mod_olean.clone(),
        olean_server_sha256: Some("e".repeat(64)),
        olean_private_sha256: mod_private_sha.clone(),
    };
    let mut c6b = fix.checker();
    c6b.set_require_mir_wp(false);
    c6b.run().unwrap();
    let err_mismatched_server = c6b
        .verify_and_stage_miri_entries(&vendor_dir, &[mismatched_server], &mod_sources)
        .unwrap_err();
    assert_eq!(err_mismatched_server.code, 1, "expected policy error: {err_mismatched_server}");
    assert!(
        err_mismatched_server
            .message
            .contains("compiled Miri .olean.server SHA-256 mismatch for Miri.WithSidecar"),
        "unexpected sidecar-mismatch error: {err_mismatched_server}"
    );

    // 6c. Unexpected `.olean.private` when emitted and entry expects `None`.
    if mod_private_sha.is_some() {
        let unexpected_private = MiriClosureEntry {
            module: "Miri.WithSidecar".to_string(),
            path: "Miri/WithSidecar.lean".to_string(),
            olean_sha256: mod_olean,
            olean_server_sha256: Some(mod_server_sha),
            olean_private_sha256: None,
        };
        let mut c6c = fix.checker();
        c6c.set_require_mir_wp(false);
        c6c.run().unwrap();
        let err_unexpected_private = c6c
            .verify_and_stage_miri_entries(&vendor_dir, &[unexpected_private], &mod_sources)
            .unwrap_err();
        assert_eq!(
            err_unexpected_private.code, 1,
            "expected policy error: {err_unexpected_private}"
        );
        assert!(
            err_unexpected_private
                .message
                .contains("unexpected Miri .olean.private sidecar for Miri.WithSidecar"),
            "unexpected private-sidecar error: {err_unexpected_private}"
        );
    }
}

/// Verifies that `--miri-cache-dir` / `Checker::set_miri_cache_dir` rejects
/// any cache directory located inside (or resolving inside) the repository
/// checkout as a policy error (exit code `1`), including non-existent paths,
/// parent traversals, and symlinks, while allowing sibling directories outside
/// the checkout.
#[test]
fn rejects_miri_cache_dir_inside_checkout() {
    let fix = TempFixture::new(None);
    let outside = tempfile::Builder::new().prefix("anneal-miri-outside-").tempdir().unwrap();

    let existing_inside = fix.root.join("existing-cache");
    fs::create_dir_all(&existing_inside).unwrap();
    let nonexistent_inside = fix.root.join(".evil-cache/nested");
    let traversed_inside = fix.root.join("sub/../.evil-cache");

    let link_into_checkout = outside.path().join("link-in");
    symlink(&existing_inside, &link_into_checkout).unwrap();
    let link_into_nested = link_into_checkout.join("deep");

    let dangling_into_checkout = outside.path().join("dangling-in");
    symlink(fix.root.join("does-not-exist"), &dangling_into_checkout).unwrap();

    let real_outside_cache = outside.path().join("real-cache");
    fs::create_dir_all(&real_outside_cache).unwrap();
    let link_out_of_checkout = fix.root.join("link-out");
    symlink(&real_outside_cache, &link_out_of_checkout).unwrap();

    let bad_paths = [
        fix.root.clone(),
        existing_inside,
        nonexistent_inside,
        traversed_inside,
        link_into_checkout,
        link_into_nested,
        dangling_into_checkout,
        link_out_of_checkout,
    ];
    for bad in &bad_paths {
        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        checker.set_miri_cache_dir(Some(bad.clone()));
        let err = checker.run().unwrap_err();
        assert_eq!(err.code, 1, "expected policy error for {}: {err}", bad.display());
        assert_eq!(err.phase, "miri-pin", "unexpected phase for {}: {err}", bad.display());
        assert!(
            !checker.execution_began(),
            "Lean execution must not begin when cache dir is inside checkout: {}",
            bad.display()
        );
    }

    // Sibling path sharing a string prefix with `checkout` is outside the
    // checkout and must be accepted by containment validation.
    let sibling_parent = outside.path().join("parent");
    let fake_repo = sibling_parent.join("repo");
    let sibling_cache = sibling_parent.join("repo-cache");
    fs::create_dir_all(&fake_repo).unwrap();
    ensure_miri_cache_outside_checkout(&fake_repo, &sibling_cache).unwrap();

    // Verify end-to-end CLI rejection with exit code `1`.
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-audit-test-bin"))
        .env_clear()
        .arg("--anneal-root")
        .arg(&fix.root)
        .arg("--miri-cache-dir")
        .arg(fix.root.join(".evil-cache"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "expected exit code 1 from CLI: {output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Miri .olean cache directory must reside outside the repository checkout"),
        "unexpected CLI stderr: {stderr}"
    );
}

/// Verifies negative cases for correspondence-audit rules in
/// `TrustedBoundary.lean` (`classifyCorrModules`,
/// `CorrOrigin.importViolation?`, `CorrOrigin.edgeViolation?`, and
/// `closureCorr` unapproved-axiom rejection) and for toolchain sysroot
/// manifest authentication (`verify_sysroot_foundation_dir`).
#[test]
fn rejects_correspondence_audit_violations_and_sysroot_mismatch() {
    let fix = TempFixture::new(None);

    // 1. Sysroot manifest mismatch & symlink rejection.
    let fake_lib = fix.root.join("fake-sysroot-lib");
    for pkg in ["Init", "Std", "Lean"] {
        fs::create_dir_all(fake_lib.join(pkg)).unwrap();
    }
    fs::write(fake_lib.join("Init/Dummy.olean"), b"dummy-olean").unwrap();
    let err_sysroot =
        verify_sysroot_foundation_dir(&fake_lib, &BTreeSet::new(), &"0".repeat(64)).unwrap_err();
    assert_eq!(err_sysroot.phase, "sysroot-foundation");
    assert!(
        err_sysroot.message.contains("sysroot Init/Std/Lean .olean/.ir manifest SHA-256 mismatch"),
        "unexpected sysroot mismatch error: {err_sysroot}"
    );
    symlink(fake_lib.join("Init/Dummy.olean"), fake_lib.join("Std/Link.olean")).unwrap();
    let err_sym =
        verify_sysroot_foundation_dir(&fake_lib, &BTreeSet::new(), &"0".repeat(64)).unwrap_err();
    assert!(
        err_sym.message.contains("symlink forbidden in sysroot"),
        "unexpected sysroot symlink error: {err_sym}"
    );

    // Prepare compiled synthetic modules for `TrustedBoundary.lean`
    // `"correspondence-audit"` negative cases.
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let trusted_lib = checker.stage().join("lib");
    let aux_src = checker.stage().join("src/corr-neg");
    let aux_path = env::join_paths([&trusted_lib]).unwrap();

    let compile_aux = |chk: &mut Checker, module: &str, body: &str| {
        let rel = module.replace('.', "/");
        let src = aux_src.join(format!("{rel}.lean"));
        fs::create_dir_all(src.parent().unwrap()).unwrap();
        fs::write(&src, body).unwrap();
        let out = trusted_lib.join(format!("{rel}.olean"));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        chk.process_with_path(
            &format!("compile-{module}"),
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-R".to_string(),
                aux_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                out.to_string_lossy().into_owned(),
                src.to_string_lossy().into_owned(),
            ],
            Some(&aux_path),
        )
        .unwrap();
    };

    compile_aux(
        &mut checker,
        "Miri.Child",
        "prelude\nimport Init.Core\nnamespace Miri.Child\ndef c : Nat := 1\nend Miri.Child\n",
    );
    compile_aux(
        &mut checker,
        "Miri.Parent",
        "prelude\nimport Init.Core\nimport Miri.Child\n\
         namespace Miri.Parent\ndef p : Nat := Miri.Child.c\nend Miri.Parent\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.CandHelper",
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nnamespace Trusted.CandHelper\ndef h : Nat := 1\nend Trusted.CandHelper\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.VettedRefsCand",
        "prelude\nimport Init.Core\nimport Trusted.CandHelper\n\
         namespace Trusted.VettedRefsCand\ndef x : Nat := Trusted.CandHelper.h\nend Trusted.VettedRefsCand\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.VettedRefsMiri",
        "prelude\nimport Init.Core\nimport Miri.Child\n\
         namespace Trusted.VettedRefsMiri\ndef x : Nat := Miri.Child.c\nend Trusted.VettedRefsMiri\n",
    );
    compile_aux(
        &mut checker,
        "Anneal.Helper",
        "prelude\nimport Init.Core\nnamespace Anneal.Helper\ndef t : Nat := 2\nend Anneal.Helper\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.CandRefsTheory",
        "prelude\nimport Init.Core\nimport Anneal.Helper\n\
         namespace Trusted.CandRefsTheory\ndef x : Nat := Anneal.Helper.t\nend Trusted.CandRefsTheory\n",
    );
    compile_aux(
        &mut checker,
        "Miri.Interpreter.ExecutionMachine",
        "prelude\nimport Init.Core\n\
         namespace Miri.Interpreter.ExecutionMachine\n\
         theorem step : (True ↔ True) → True = True := propext\n\
         end Miri.Interpreter.ExecutionMachine\n",
    );

    let search = vec![trusted_lib];

    // 2a. `classifyCorrModules`: overlapping module role.
    let err_overlap = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Trusted".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert!(
        err_overlap.message.contains("overlapping module role for Trusted"),
        "unexpected overlap error: {err_overlap}"
    );

    // 2b. `classifyCorrModules`: missing trust tier for Trusted module.
    let err_missing_tier = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::new(),
        })
        .unwrap_err();
    assert!(
        err_missing_tier.message.contains("missing trust tier for Trusted module Trusted"),
        "unexpected missing-tier error: {err_missing_tier}"
    );

    // 2c. `classifyCorrModules`: trust tier declared for non-Trusted module.
    let err_non_trusted_tier = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Miri.Child".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert!(
        err_non_trusted_tier
            .message
            .contains("trust tier declared for non-Trusted module Miri.Child"),
        "unexpected non-trusted-tier error: {err_non_trusted_tier}"
    );

    // 2d. `classifyCorrModules`: foreign module in correspondence environment
    // (`Miri.Parent` imports unlisted `Miri.Child`).
    let err_foreign = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Parent".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert!(
        err_foreign.message.contains("foreign module Miri.Child in correspondence environment"),
        "unexpected foreign-module error: {err_foreign}"
    );

    // 3a. `CorrOrigin.importViolation?`: vetted -> candidate (rejected before
    // `checkDeclarationEdges` inspects the constant reference).
    let err_vetted_cand = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.CandHelper".to_string(),
                "Trusted.VettedRefsCand".to_string(),
            ],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.CandHelper".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
                ("Trusted.VettedRefsCand".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_vetted_cand.code, 1, "unexpected vetted->cand code: {err_vetted_cand}");
    assert!(
        err_vetted_cand.message.contains(
            "vetted module Trusted.VettedRefsCand cannot import candidate:mir_semantics module Trusted.CandHelper"
        ),
        "unexpected vetted->cand error: {err_vetted_cand}"
    );

    // 3b. `CorrOrigin.importViolation?`: vetted -> vendorMiri (rejected before
    // `checkDeclarationEdges` inspects the constant reference).
    let err_vetted_miri = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.VettedRefsMiri".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.VettedRefsMiri".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_vetted_miri.code, 1, "unexpected vetted->miri code: {err_vetted_miri}");
    assert!(
        err_vetted_miri.message.contains(
            "vetted module Trusted.VettedRefsMiri cannot import non-foundation module Miri.Child"
        ),
        "unexpected vetted->miri error: {err_vetted_miri}"
    );

    // 3a-edge & 3b-edge. `CorrOrigin.edgeViolation?` defense in depth: forged
    // `vetted` `.olean` headers importing only `Init.Core` while referencing
    // `Trusted.CandHelper.h` or `Miri.Child.c` remain rejected by
    // `checkDeclarationEdges`.
    let stage = checker.stage().to_path_buf();
    for (forged_mod, ref_const, extra_trusted, expected_msg) in [
        (
            "Trusted.ForgedCorrVettedCand",
            "Trusted.CandHelper.h",
            true,
            "vetted constant Trusted.ForgedCorrVettedCand.x references candidate:mir_semantics constant Trusted.CandHelper.h",
        ),
        (
            "Trusted.ForgedCorrVettedMiri",
            "Miri.Child.c",
            false,
            "vetted constant Trusted.ForgedCorrVettedMiri.x references non-foundation constant Miri.Child.c",
        ),
    ] {
        let out = search[0].join(format!("{}.olean", forged_mod.replace('.', "/")));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        run_lean_script(
            &mut checker,
            &format!("gen-{forged_mod}"),
            &stage.join(format!("gen_{}.lean", forged_mod.replace('.', "_"))),
            &format!(
                "import Lean.Environment\n\
                 open Lean\n\
                 def main : IO Unit := do\n\
                   let ci : ConstantInfo := .defnInfo {{\n\
                     name := `{forged_mod}.x\n\
                     levelParams := []\n\
                     type := .const `Nat []\n\
                     value := .const `{ref_const} []\n\
                     hints := .abbrev\n\
                     safety := .safe\n\
                     all := [`{forged_mod}.x]\n\
                   }}\n\
                   let md : ModuleData := {{\n\
                     isModule := false\n\
                     imports := #[{{ module := `Init.Core }}]\n\
                     constNames := #[`{forged_mod}.x]\n\
                     constants := #[ci]\n\
                     extraConstNames := #[]\n\
                     entries := #[]\n\
                   }}\n\
                   saveModuleData (System.FilePath.mk {:?}) `{forged_mod} md\n",
                out.to_string_lossy()
            ),
        );
        let mut trusted_mods = vec!["Trusted".to_string(), forged_mod.to_string()];
        let mut tiers = BTreeMap::from([
            ("Trusted".to_string(), TrustTier::Vetted),
            (forged_mod.to_string(), TrustTier::Vetted),
        ]);
        if extra_trusted {
            trusted_mods.push("Trusted.CandHelper".to_string());
            tiers.insert(
                "Trusted.CandHelper".to_string(),
                TrustTier::Candidate(CandidateFeature::MirSemantics),
            );
        }
        let err_edge = checker
            .inspect(InspectorRequest::CorrespondenceAudit {
                search_path: search.clone(),
                trusted: trusted_mods,
                corr_trusted: Vec::new(),
                theory: Vec::new(),
                corr_theory: Vec::new(),
                vendor_miri: vec!["Miri.Child".to_string()],
                module_tiers: tiers,
            })
            .unwrap_err();
        assert_eq!(err_edge.code, 1, "unexpected forged edge code for {forged_mod}: {err_edge}");
        assert!(
            err_edge.message.contains(expected_msg),
            "unexpected forged edge error for {forged_mod}: {err_edge}"
        );
    }

    // 3d. `"correspondence-preflight"` rejects a declaration-free `vetted`
    // Pass 2 source importing a Pass 1 `candidate:mir_semantics` module, a
    // `vendor/lean-miri` module, or a Pass 1 `.repo .theory` module
    // (`Anneal.Helper`) before compilation, deriving Pass 1 base tiers
    // directly from staged `"baseSources"` rather than a caller map.
    let trusted_base_src = checker.modules()["Trusted"].clone();
    let cand_helper_src = aux_src.join("Trusted/CandHelper.lean");
    let corr_pf_dir = stage.join("src/corr-pf-tier");
    fs::create_dir_all(&corr_pf_dir).unwrap();
    let corr_vetted_cand_src = corr_pf_dir.join("CorrVettedCand.lean");
    fs::write(
        &corr_vetted_cand_src,
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Trusted.CandHelper\n",
    )
    .unwrap();
    let err_pf_cand = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandHelper".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted.CandHelper".to_string(), cand_helper_src.clone()),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_cand.code, 1, "unexpected corr-pf cand code: {err_pf_cand}");
    assert_eq!(err_pf_cand.phase, "correspondence-preflight");
    assert!(
        err_pf_cand.message.contains(
            "vetted module Trusted.CorrVettedCand cannot import candidate:mir_semantics module Trusted.CandHelper"
        ),
        "unexpected corr-pf cand error: {err_pf_cand}"
    );

    let corr_vetted_miri_src = corr_pf_dir.join("CorrVettedMiri.lean");
    fs::write(
        &corr_vetted_miri_src,
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Miri.Child\n",
    )
    .unwrap();
    let err_pf_miri = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.CorrVettedMiri".to_string(), corr_vetted_miri_src)],
        })
        .unwrap_err();
    assert_eq!(err_pf_miri.code, 1, "unexpected corr-pf miri code: {err_pf_miri}");
    assert_eq!(err_pf_miri.phase, "correspondence-preflight");
    assert!(
        err_pf_miri.message.contains(
            "vetted module Trusted.CorrVettedMiri cannot import non-foundation module Miri.Child"
        ),
        "unexpected corr-pf miri error: {err_pf_miri}"
    );

    let corr_vetted_theory_src = corr_pf_dir.join("CorrVettedTheory.lean");
    fs::write(
        &corr_vetted_theory_src,
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Anneal.Helper\n",
    )
    .unwrap();
    let err_pf_theory = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: vec!["Anneal.Helper".to_string()],
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.CorrVettedTheory".to_string(), corr_vetted_theory_src)],
        })
        .unwrap_err();
    assert_eq!(err_pf_theory.code, 1, "unexpected corr-pf theory code: {err_pf_theory}");
    assert_eq!(err_pf_theory.phase, "correspondence-preflight");
    assert!(
        err_pf_theory.message.contains(
            "vetted module Trusted.CorrVettedTheory cannot import non-foundation module Anneal.Helper"
        ),
        "unexpected corr-pf theory error: {err_pf_theory}"
    );

    // Reject a direct `"correspondence-preflight"` caller that submits a
    // vetted source colliding with an already-loaded Pass 1 `candidate`
    // module (`Trusted.CandHelper`), or submits missing, extra, duplicate,
    // non-`Trusted`, or tactic-contaminated `base_trusted_sources`.
    let corr_fake_cand_src = corr_pf_dir.join("FakeCandHelper.lean");
    fs::write(&corr_fake_cand_src, b"-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\n")
        .unwrap();
    let corr_vetted_cand_src2 = corr_pf_dir.join("CorrVettedCand2.lean");
    fs::write(
        &corr_vetted_cand_src2,
        b"-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Trusted.CandHelper\n",
    )
    .unwrap();
    let err_pf_cand_collision = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandHelper".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted.CandHelper".to_string(), cand_helper_src.clone()),
            ],
            sources: vec![
                ("Trusted.CandHelper".to_string(), corr_fake_cand_src),
                ("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src2),
            ],
        })
        .unwrap_err();
    assert_eq!(err_pf_cand_collision.code, 1, "unexpected collision code: {err_pf_cand_collision}");
    assert_eq!(err_pf_cand_collision.phase, "correspondence-preflight");
    assert!(
        err_pf_cand_collision
            .message
            .contains("preflight source module Trusted.CandHelper collides with base module"),
        "unexpected corr-pf collision error: {err_pf_cand_collision}"
    );

    let err_pf_missing_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandHelper".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_missing_base.code, 1);
    assert_eq!(err_pf_missing_base.phase, "correspondence-preflight");
    assert!(
        err_pf_missing_base
            .message
            .contains("missing base preflight source for Trusted module Trusted.CandHelper"),
        "unexpected corr-pf missing base error: {err_pf_missing_base}"
    );

    let err_pf_extra_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted.CandHelper".to_string(), cand_helper_src),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_extra_base.code, 1);
    assert_eq!(err_pf_extra_base.phase, "correspondence-preflight");
    assert!(
        err_pf_extra_base.message.contains(
            "extra base preflight source Trusted.CandHelper missing from trusted inventory"
        ),
        "unexpected corr-pf extra base error: {err_pf_extra_base}"
    );

    let err_pf_dup_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted".to_string(), trusted_base_src.clone()),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_dup_base.code, 1);
    assert_eq!(err_pf_dup_base.phase, "correspondence-preflight");
    assert!(
        err_pf_dup_base.message.contains("duplicate base preflight source module Trusted"),
        "unexpected corr-pf duplicate base error: {err_pf_dup_base}"
    );

    let err_pf_non_trusted_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src),
                ("Anneal.Helper".to_string(), aux_src.join("Anneal/Helper.lean")),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_non_trusted_base.code, 1);
    assert_eq!(err_pf_non_trusted_base.phase, "correspondence-preflight");
    assert!(
        err_pf_non_trusted_base.message.contains("non-Trusted base preflight source Anneal.Helper"),
        "unexpected corr-pf non-Trusted base error: {err_pf_non_trusted_base}"
    );

    let bad_base_tactic_src = corr_pf_dir.join("BadBaseTactic.lean");
    fs::write(
        &bad_base_tactic_src,
        b"-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\ntheorem bad : Eq 0 0 := by rfl\n",
    )
    .unwrap();
    let err_pf_tactic_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), bad_base_tactic_src)],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src)],
        })
        .unwrap_err();
    assert_eq!(err_pf_tactic_base.code, 1);
    assert_eq!(err_pf_tactic_base.phase, "correspondence-preflight");

    // 3c. `CorrOrigin.importViolation?`: candidate Trusted -> theory. The
    // compiled `.olean` header import of `Anneal.Helper` is rejected before
    // `checkDeclarationEdges` inspects the constant reference;
    // `rejects_forged_trusted_constant_referencing_theory` covers that
    // constant-edge rule with a forged header that omits the import.
    let err_cand_theory = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandRefsTheory".to_string()],
            corr_trusted: Vec::new(),
            theory: vec!["Anneal.Helper".to_string()],
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.CandRefsTheory".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_cand_theory.code, 1, "unexpected cand->theory code: {err_cand_theory}");
    assert!(
        err_cand_theory.message.contains(
            "Trusted module Trusted.CandRefsTheory cannot import non-Trusted module Anneal.Helper"
        ),
        "unexpected cand->theory error: {err_cand_theory}"
    );

    // 4. `closureCorr`: reachable unapproved axiom (`propext` from `Init.Core`
    // when omitted from the axiom allowlist) rejected after passing
    // `verifyAndCollectCorrLocals` and standalone kernel replay.
    checker.admitted_mut().unwrap().axioms.retain(|(ax, _)| ax != "propext");
    let err_axiom = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search,
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Interpreter.ExecutionMachine".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert!(
        err_axiom.message.contains("unapproved axiom propext from Init.Core"),
        "unexpected unapproved-axiom error: {err_axiom}"
    );
}

/// Pass 1 `"audit"` independently rejects a compiled `Trusted` module whose
/// `.olean` header imports a `theory/` module, even when the module was
/// compiled without repository `"preflight"` and references none of the
/// imported constants (so only `RepoOrigin.importViolation?` applies).
#[test]
fn rejects_compiled_trusted_header_import_of_theory() {
    let fix = TempFixture::new(None);
    fs::create_dir_all(fix.root.join("theory")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\ndef helper : Nat := 0\nend Anneal\n",
    )
    .unwrap();
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    compile_forged_module(
        &mut checker,
        &stage.join("src/forged"),
        &stage.join("lib"),
        &["Anneal"],
        "Trusted.Forged",
        "prelude\nimport Init.Core\nimport Anneal\nnamespace Trusted\ndef forged : Nat := 0\nend Trusted\n",
    );
    let err = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string(), "Trusted.Forged".to_string()],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.Forged".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "audit", "unexpected phase: {err}");
    assert!(
        err.message
            .contains("Trusted module Trusted.Forged cannot import non-Trusted module Anneal"),
        "unexpected error: {err}"
    );
}

/// Pass 1 `"audit"` and Pass 2 `"correspondence-audit"` both reject a
/// `Trusted` constant that references a `theory/` constant (the
/// `.repo (.trusted _), .repo .theory` arm of `RepoOrigin.edgeViolation?` and
/// `CorrOrigin.edgeViolation?`) with policy exit code `1`.
///
/// `Lean.saveModuleData` forges `Trusted.ForgedRef.olean`, whose header
/// imports only `Init.Core` (so `checkHeaderImports` admits it) while its
/// well-typed definition `Trusted.ForgedRef.x : Nat := Anneal.helper`
/// references the compiled `theory/` constant `Anneal.helper`. Only
/// `checkDeclarationEdges` can therefore reject it. Pass 1 audits the forged
/// module as `vetted` and Pass 2 as `candidate:mir_semantics`, covering both
/// tiers that the `.trusted _` pattern matches.
#[test]
fn rejects_forged_trusted_constant_referencing_theory() {
    let fix = TempFixture::new(None);
    fs::create_dir_all(fix.root.join("theory")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\ndef helper : Nat := 0\nend Anneal\n",
    )
    .unwrap();
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    // `Trusted.*` modules must share the search-path entry holding
    // `Trusted.olean`, so the forged module goes into the staged `lib/`.
    let stage = checker.stage().to_path_buf();
    let trusted_lib = stage.join("lib");
    let forged_module = "Trusted.ForgedRef";
    let forged_out = trusted_lib.join("Trusted/ForgedRef.olean");
    fs::create_dir_all(forged_out.parent().unwrap()).unwrap();
    run_lean_script(
        &mut checker,
        "gen-forged-ref",
        &stage.join("gen_forged_ref.lean"),
        &format!(
            "import Lean.Environment\n\
             open Lean\n\
             def main : IO Unit := do\n\
               let ci : ConstantInfo := .defnInfo {{\n\
                 name := `Trusted.ForgedRef.x\n\
                 levelParams := []\n\
                 type := .const `Nat []\n\
                 value := .const `Anneal.helper []\n\
                 hints := .abbrev\n\
                 safety := .safe\n\
                 all := [`Trusted.ForgedRef.x]\n\
               }}\n\
               let md : ModuleData := {{\n\
                 isModule := false\n\
                 imports := #[{{ module := `Init.Core }}]\n\
                 constNames := #[`Trusted.ForgedRef.x]\n\
                 constants := #[ci]\n\
                 extraConstNames := #[]\n\
                 entries := #[]\n\
               }}\n\
               saveModuleData (System.FilePath.mk {:?}) `Trusted.ForgedRef md\n",
            forged_out.to_string_lossy()
        ),
    );
    // Pass 1 loads modules from the admitted artifact map and compares their
    // headers with the admitted import graph.
    let core_edge = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", forged_out.to_string_lossy().into_owned())]),
        "test",
        String::new,
    )
    .unwrap();
    {
        let adm = checker.admitted_mut().unwrap();
        adm.graph.insert(forged_module.to_string(), core_edge);
        adm.artifacts.insert(forged_module.to_string(), arts);
    }

    let expected = "Trusted constant Trusted.ForgedRef.x references Anneal.helper \
                    from non-Trusted module Anneal";
    let err_audit = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string(), forged_module.to_string()],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (forged_module.to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_audit.code, 1, "unexpected Pass 1 code: {err_audit}");
    assert_eq!(err_audit.phase, "audit", "unexpected Pass 1 phase: {err_audit}");
    assert!(err_audit.message.contains(expected), "unexpected Pass 1 error: {err_audit}");

    let err_corr = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![trusted_lib, stage.join("theory-lib")],
            trusted: vec!["Trusted".to_string(), forged_module.to_string()],
            corr_trusted: Vec::new(),
            theory: vec!["Anneal".to_string()],
            corr_theory: Vec::new(),
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (forged_module.to_string(), TrustTier::Candidate(CandidateFeature::MirSemantics)),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_corr.code, 1, "unexpected Pass 2 code: {err_corr}");
    assert_eq!(err_corr.phase, "correspondence-audit", "unexpected Pass 2 phase: {err_corr}");
    assert!(err_corr.message.contains(expected), "unexpected Pass 2 error: {err_corr}");
}

/// Pass 2 `"preflight"` keeps `trusted/correspondence/` isolated from Pass 1
/// `theory/` modules. Pass 1 compiles the real `Trusted.MirAst`,
/// `Trusted.MirSemantics`, and `Anneal.MirWp` first, so `Anneal.MirWp` is an
/// admitted compiled artifact when Pass 2 starts; a `Trusted.Correspondence`
/// source importing it is still rejected before any Pass 2 module compiles.
#[test]
fn rejects_trusted_correspondence_import_of_theory_in_pass2_preflight() {
    let checkout = repo_root();
    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();
    let (_, theory_manifest) = anneal_audit::bundle::load_theory_bundle_manifest(&checkout)
        .expect("checkout theory bundle manifest");
    for rel in anneal_audit::bundle::TRUSTED_BUNDLE_SOURCES
        .iter()
        .copied()
        .chain(std::iter::once(anneal_audit::bundle::THEORY_BUNDLE_MANIFEST))
        .chain(theory_manifest.modules.iter().map(|entry| entry.path.as_str()))
        .chain(std::iter::once("theory/Anneal/MirWp/Canaries.lean"))
    {
        let dst = fix.root.join(rel);
        fs::create_dir_all(dst.parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), dst).unwrap();
    }
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        b"prelude\nimport Init.NotationExtra\nimport Trusted\nimport Anneal.MirWp\n",
    )
    .unwrap();
    for rel in anneal_audit::bundle::PROVENANCE_SOURCES {
        if rel.ends_with(".lean") {
            let dst = fix.root.join(rel);
            fs::create_dir_all(dst.parent().unwrap()).unwrap();
            let contents = if *rel == "trusted/correspondence/Trusted/Correspondence.lean" {
                "-- anneal-trust-tier: candidate:mir_semantics\n\
                 prelude\nimport Init.NotationExtra\nimport Anneal.MirWp\n"
            } else if rel.starts_with("trusted/correspondence/") {
                "-- anneal-trust-tier: candidate:mir_semantics\n\
                 prelude\nimport Init.NotationExtra\n"
            } else {
                "prelude\nimport Trusted.Correspondence\n"
            };
            fs::write(dst, contents.as_bytes()).unwrap();
        }
    }

    let mut checker = fix.checker();
    // Synthetic fixture overrides `trusted/correspondence/` and
    // `correspondence/` with 3-line stubs, so embedded-bundle parity is
    // disabled while `"audit"` still checks `Trusted.*` / `Anneal.MirWp`.
    checker.set_require_mir_wp(false);
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "preflight", "unexpected phase: {err}");
    assert!(
        err.message.contains("foreign/missing import Anneal.MirWp in Trusted.Correspondence"),
        "unexpected error: {err}"
    );
}

/// Pass 2 `"correspondence-audit"` independently rejects a compiled
/// `Trusted.Correspondence` whose `.olean` header imports the `theory/` module
/// `Anneal.MirWp`, even when the module was compiled without repository
/// `"preflight"` and references none of the imported constants (so only
/// `CorrOrigin.importViolation?` applies).
#[test]
fn rejects_trusted_correspondence_import_of_theory_in_correspondence_audit() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let src = stage.join("src/forged-corr");
    let trusted_lib = stage.join("lib");
    let corr_lib = stage.join("forged-corr-lib");
    let vendor_lib = stage.join("forged-vendor-lib");
    compile_forged_module(
        &mut checker,
        &stage.join("src/forged-vendor"),
        &vendor_lib,
        &[],
        "Miri.Forged",
        "prelude\nimport Init.Core\nnamespace Miri.Forged\ndef ok : Nat := 0\nend Miri.Forged\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &corr_lib,
        &[],
        "Anneal.MirWp",
        "prelude\nimport Init.Core\nnamespace Anneal.MirWp\ndef wpProg : Nat := 0\nend Anneal.MirWp\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &trusted_lib,
        &["Anneal.MirWp"],
        "Trusted.Correspondence",
        "prelude\nimport Init.Core\nimport Anneal.MirWp\nnamespace Trusted.Correspondence\ndef CorrespondenceClaim : Prop := True\nend Trusted.Correspondence\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &corr_lib,
        &["Trusted.Correspondence"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Init.Core\nimport Trusted.Correspondence\n",
    );
    let err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![trusted_lib, vendor_lib, corr_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: vec!["Trusted.Correspondence".to_string()],
            theory: vec!["Anneal.MirWp".to_string()],
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: vec!["Miri.Forged".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.Correspondence".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
            ]),
        })
        .unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "correspondence-audit", "unexpected phase: {err}");
    assert!(
        err.message.contains(
            "Trusted module Trusted.Correspondence cannot import non-Trusted module Anneal.MirWp"
        ),
        "unexpected error: {err}"
    );
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

/// Pass 2 `"correspondence-audit"` kernel-replays correspondence declarations:
/// a forged `Anneal.MirCorrespondenceProof.olean` holding the ill-typed theorem
/// `Anneal.MirCorrespondenceProof.bogus : False := True.intro` is rejected
/// with operational exit code `2` and `"correspondence kernel replay failed"`.
///
/// `Lean.saveModuleData` writes the theorem without elaborating or
/// kernel-checking it, and the theorem passes every inventory, origin, and
/// edge check, so only the correspondence replay in `replayCorrAndVendor`
/// rejects it. If that replay were skipped, a later Pass 2 policy check would
/// reject this fixture with exit code `1` instead.
#[test]
fn rejects_forged_ill_typed_correspondence_declaration_during_replay() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let corr_lib = stage.join("forged-corr-lib");
    let forged_out = corr_lib.join("Anneal/MirCorrespondenceProof.olean");
    fs::create_dir_all(forged_out.parent().unwrap()).unwrap();
    run_lean_script(
        &mut checker,
        "gen-bogus-corr-proof",
        &stage.join("gen_bogus_corr_proof.lean"),
        &format!(
            "import Lean.Environment\n\
             open Lean\n\
             def main : IO Unit := do\n\
               let ci : ConstantInfo := .thmInfo {{\n\
                 name := `Anneal.MirCorrespondenceProof.bogus\n\
                 levelParams := []\n\
                 type := .const `False []\n\
                 value := .const `True.intro []\n\
                 all := [`Anneal.MirCorrespondenceProof.bogus]\n\
               }}\n\
               let md : ModuleData := {{\n\
                 isModule := false\n\
                 imports := #[{{ module := `Init.Core }}]\n\
                 constNames := #[`Anneal.MirCorrespondenceProof.bogus]\n\
                 constants := #[ci]\n\
                 extraConstNames := #[]\n\
                 entries := #[]\n\
               }}\n\
               saveModuleData (System.FilePath.mk {:?}) `Anneal.MirCorrespondenceProof md\n",
            forged_out.to_string_lossy()
        ),
    );

    let err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![stage.join("lib"), corr_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    // Kernel replay exceptions are operational errors (exit code `2`) so no
    // stringified `Kernel.Exception` can spoof `"policy:"`.
    assert_eq!(
        err.code, 2,
        "expected operational exit code 2 on correspondence replay failure: {err}"
    );
    assert_eq!(err.phase, "correspondence-audit", "unexpected phase: {err}");
    assert!(
        err.message.contains("correspondence kernel replay failed")
            && err.message.contains("Anneal.MirCorrespondenceProof.bogus")
            && err.message.contains("declaration type mismatch"),
        "expected correspondence kernel replay rejection, got: {err}"
    );
}

/// Pass 2 `"correspondence-audit"` rejects a repository constant whose name
/// already belongs to the authenticated sysroot replay base with policy exit
/// code `1` (`"repository constant ... shadows vendor/sysroot declaration"`),
/// before `Kernel.Environment.replay` could skip it as a duplicate theorem.
///
/// `Lean.saveModuleData` forges a `Trusted.Correspondence.olean` (header
/// importing only `Init.Core`) whose sole constant is a verbatim copy of the
/// `.sysrootFoundation` theorem `Add.add_eq_hAdd` from `Init.MethodSpecsSimp`
/// (whose `Add` root is outside `reservedKernelRoots` so `validateRepoConstant`
/// admits it), and an empty `Anneal.MirCorrespondenceProof.olean` whose header
/// imports `Init.MethodSpecsSimp`. `Lean.importModules` admits the duplicate
/// theorem and attributes it to `Trusted.Correspondence`, which loads first,
/// so the inventory, origin, and edge checks pass and only the shadow check in
/// `replayCorrAndVendor` rejects it.
#[test]
fn rejects_repository_constant_shadowing_sysroot_declaration() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    // `Trusted.*` modules must share the search-path entry holding
    // `Trusted.olean`, so the forged umbrella goes into the staged `lib/`.
    let stage = checker.stage().to_path_buf();
    let prefix = checker.admitted().unwrap().prefix.clone();
    let trusted_lib = stage.join("lib");
    let corr_lib = stage.join("shadow-corr-lib");
    let corr_out = trusted_lib.join("Trusted/Correspondence.olean");
    let proof_out = corr_lib.join("Anneal/MirCorrespondenceProof.olean");
    for out in [&corr_out, &proof_out] {
        fs::create_dir_all(out.parent().unwrap()).unwrap();
    }
    run_lean_script(
        &mut checker,
        "gen-shadow-sysroot",
        &stage.join("gen_shadow_sysroot.lean"),
        &format!(
            "import Lean.Environment\n\
             open Lean\n\
             def main : IO Unit := do\n\
               initSearchPath (System.FilePath.mk {:?})\n\
               let env ← importModules #[{{ module := `Init.MethodSpecsSimp }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n\
               let some ci := env.checked.get.find? `Add.add_eq_hAdd \
                 | throw (IO.userError \"missing sysroot theorem Add.add_eq_hAdd\")\n\
               let corrMd : ModuleData := {{\n\
                 isModule := false\n\
                 imports := #[{{ module := `Init.Core }}]\n\
                 constNames := #[ci.name]\n\
                 constants := #[ci]\n\
                 extraConstNames := #[]\n\
                 entries := #[]\n\
               }}\n\
               saveModuleData (System.FilePath.mk {:?}) `Trusted.Correspondence corrMd\n\
               let proofMd : ModuleData := {{\n\
                 isModule := false\n\
                 imports := #[{{ module := `Init.MethodSpecsSimp }}]\n\
                 constNames := #[]\n\
                 constants := #[]\n\
                 extraConstNames := #[]\n\
                 entries := #[]\n\
               }}\n\
               saveModuleData (System.FilePath.mk {:?}) `Anneal.MirCorrespondenceProof proofMd\n",
            prefix.to_string_lossy(),
            corr_out.to_string_lossy(),
            proof_out.to_string_lossy()
        ),
    );

    let err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![trusted_lib, corr_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: vec!["Trusted.Correspondence".to_string()],
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.Correspondence".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
            ]),
        })
        .unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "correspondence-audit", "unexpected phase: {err}");
    assert!(
        err.message
            .contains("repository constant Add.add_eq_hAdd shadows vendor/sysroot declaration"),
        "unexpected error: {err}"
    );
}

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
/// are never produced).
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

    let e2e_cases: &[(&str, &str)] = &[
        (
            // Valid compilable `Lean.MessageData` term using `m!`: passes
            // foundation preflight as an identifier/app, so dropping
            // `"correspondence-preflight"` would compile both Pass 2 modules.
            "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
             import Trusted.Correspondence\n\
             namespace Anneal.MirCorrespondenceProof\n\
             def f : Lean.MessageData := m! \"x\"\n\
             end Anneal.MirCorrespondenceProof\n",
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
            "cannot open namespace Miri.ScopedSyntax with scoped syntax or extensions",
        ),
        (
            // Decoy-namespace shadowing attack against sysroot
            // `Lean.PostprocessTraces`: `Anneal.DecoyNs` declares unscoped
            // `Anneal.Lean.PostprocessTraces` in Pass 1 `theory/`.
            "prelude\nimport Init.Core\nimport Miri.ImportLean\n\
             import Trusted.Correspondence\n\
             namespace Anneal\n\
             open Lean.PostprocessTraces\n\
             def f : Nat := 0\n\
             end Anneal\n",
            "cannot open namespace Lean.PostprocessTraces with scoped syntax or extensions",
        ),
    ];

    for (proof_src, expected_msg) in e2e_cases {
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
        assert_eq!(err.phase, "correspondence-preflight");
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

/// Verifies Pass 1 foundation `"preflight"` rejects `open List` (an `Init.*`
/// namespace with scoped notations) in both `theory/` and `trusted/lean/`
/// before compilation—including when shadowed by a local decoy namespace.
#[test]
fn rejects_scoped_namespace_in_pass1_preflight() {
    let cases: &[(&str, &str)] = &[
        (
            "theory/Anneal/OpenList.lean",
            "prelude\nimport Init.Data.List.Basic\n\
             open List\n\
             def f : Nat := 0\n",
        ),
        (
            "trusted/lean/Trusted/OpenList.lean",
            "-- anneal-trust-tier: candidate:mir_semantics\n\
             prelude\nimport Init.Data.List.Basic\n\
             open List\n\
             def f : Nat := 0\n",
        ),
        (
            "theory/Anneal/OpenListDecoy.lean",
            "prelude\nimport Init.Data.List.Basic\n\
             namespace Anneal.List\n\
             def decoy : Nat := 0\n\
             end Anneal.List\n\
             namespace Anneal\n\
             open List\n\
             def f : Nat := 0\n\
             end Anneal\n",
        ),
    ];

    for (rel, body) in cases {
        let mut fix = TempFixture::new(None);
        let path = fix.root.join(rel);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        if rel.starts_with("theory/") {
            fs::write(fix.root.join("theory/Anneal.lean"), "prelude\nimport Init.Core\n").unwrap();
        }
        fs::write(&path, body).unwrap();
        let err = fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
        assert!(
            err.message.contains("cannot open namespace List with scoped syntax or extensions"),
            "expected scoped List rejection for {rel}, got: {err}"
        );
    }
}

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

/// Verifies `inventoryAlternates` and `checkAlternateProofs` in
/// `TrustedBoundary.lean`:
/// 1. Two pinned foundation modules exporting the same theorem with distinct
///    *valid* proof terms are accepted and both proofs are kernel-checked
///    (`checkedAlternateProofs == 2`).
/// 2. When the unselected alternate theorem carries a forged ill-typed proof
///    (accepted silently by `Lean.importModules`), `checkAlternateProofs`
///    rejects it under a fresh name with an operational kernel error
///    (exit code `2`, `"alternate pinned theorem proof check"`).
#[test]
fn validates_and_rejects_alternate_foundation_theorem_proofs() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let src = stage.join("src/alt-proofs");
    let lib = stage.join("alt-lib");
    let core_edge = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];

    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &[],
        "Init.AltA",
        "prelude\nimport Init.Core\ntheorem AltDup.thm : True := True.intro\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &[],
        "Init.AltB",
        "prelude\nimport Init.Core\ntheorem AltDup.thm : True := (fun x => x) True.intro\n",
    );
    {
        let adm = checker.admitted_mut().unwrap();
        adm.foundation_graph.insert("Init.AltA".to_string(), core_edge.clone());
        adm.foundation_graph.insert("Init.AltB".to_string(), core_edge.clone());
    }

    // 1. Positive case: two valid alternate proofs are both kernel-checked.
    let ok_rep = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .expect("valid alternate pinned theorem proofs must be accepted");
    assert_eq!(
        ok_rep.get("checkedAlternateProofs").and_then(Json::as_u64),
        Some(2),
        "expected both alternate proofs to be checked: {ok_rep}"
    );

    // 2. Negative case: synthesize `Init.AltBad.olean` containing the same
    // theorem `AltDup.thm : True` with a forged proof `Nat.zero` (only
    // importing `Init.Core`) via `Lean.saveModuleData`. `importModules` keeps
    // `Init.AltA`'s valid proof, and `checkAlternateProofs` must catch the
    // forged unselected alternate proof.
    let forged_out = lib.join("Init/AltBad.olean");
    let gen_script = stage.join("gen_alt_bad.lean");
    fs::write(
        &gen_script,
        format!(
            "import Lean.Environment\n\
             open Lean\n\
             def main : IO Unit := do\n\
               let ci : ConstantInfo := .thmInfo {{\n\
                 name := `AltDup.thm\n\
                 levelParams := []\n\
                 type := .const `True []\n\
                 value := .const `Nat.zero []\n\
                 all := [`AltDup.thm]\n\
               }}\n\
               let md : ModuleData := {{\n\
                 isModule := false\n\
                 imports := #[{{ module := `Init.Core }}]\n\
                 constNames := #[`AltDup.thm]\n\
                 constants := #[ci]\n\
                 extraConstNames := #[]\n\
                 entries := #[]\n\
               }}\n\
               saveModuleData (System.FilePath.mk {:?}) `Init.AltBad md\n",
            forged_out.to_string_lossy()
        ),
    )
    .unwrap();
    checker
        .process(
            "gen-alt-bad",
            &[
                "-j1".to_string(),
                "-M4096".to_string(),
                "--run".to_string(),
                gen_script.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let bad_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", forged_out.to_string_lossy().into_owned())]),
        "test",
        String::new,
    )
    .unwrap();
    {
        let adm = checker.admitted_mut().unwrap();
        adm.foundation_graph.remove("Init.AltB");
        adm.graph.remove("Init.AltB");
        adm.artifacts.remove("Init.AltB");
        adm.foundation_graph.insert("Init.AltBad".to_string(), core_edge.clone());
        adm.graph.insert("Init.AltBad".to_string(), core_edge);
        adm.artifacts.insert("Init.AltBad".to_string(), bad_arts);
    }

    let err_alt = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(
        err_alt.code, 2,
        "expected operational exit code 2 on forged alternate proof: {err_alt}"
    );
    assert_eq!(err_alt.phase, "audit");
    assert!(
        err_alt.message.contains("alternate pinned theorem proof check AltDup.thm")
            && err_alt.message.contains("declaration type mismatch"),
        "expected checkAlternateProofs rejection, got: {err_alt}"
    );
}

/// Verifies `Checker::run` rejects correspondence setups that are missing the
/// required `Trusted/Correspondence.lean` umbrella or
/// `Anneal/MirCorrespondenceProof.lean` entry module with policy exit code `1`.
#[test]
fn rejects_missing_correspondence_entry_modules() {
    let checkout = repo_root();
    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();
    fs::create_dir_all(fix.root.join("trusted/correspondence/Trusted")).unwrap();
    fs::create_dir_all(fix.root.join("correspondence/Anneal")).unwrap();

    // 1. Missing `Trusted/Correspondence.lean` umbrella.
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/Other.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean"),
        b"prelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    let mut checker1 = fix.checker();
    checker1.set_require_mir_wp(false);
    let err_missing_corr = checker1.run().unwrap_err();
    assert_eq!(err_missing_corr.code, 1);
    assert_eq!(err_missing_corr.phase, "snapshot");
    assert!(
        err_missing_corr
            .message
            .contains("missing Trusted/Correspondence.lean umbrella in trusted/correspondence"),
        "unexpected missing Trusted.Correspondence error: {err_missing_corr}"
    );

    // 2. Missing `Anneal/MirCorrespondenceProof.lean`.
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/Correspondence.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    fs::remove_file(fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean")).unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/Other.lean"),
        b"prelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    let mut checker2 = fix.checker();
    checker2.set_require_mir_wp(false);
    let err_missing_proof = checker2.run().unwrap_err();
    assert_eq!(err_missing_proof.code, 1);
    assert_eq!(err_missing_proof.phase, "snapshot");
    assert!(
        err_missing_proof
            .message
            .contains("missing Anneal/MirCorrespondenceProof.lean in correspondence"),
        "unexpected missing Anneal.MirCorrespondenceProof error: {err_missing_proof}"
    );
}

/// Verifies every external-origin branch of `CorrOrigin.importViolation?`
/// (`.vendorMiri -> .repo`, `.sysrootFoundation -> .vendorMiri/.repo`,
/// `.foundation -> .vendorMiri/.repo`) and `checkHeaderImports`'s defensive
/// `"foreign import"` rejection with policy exit code `1`.
#[test]
fn rejects_external_origin_header_imports_and_foreign_imports() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let trusted_lib = stage.join("lib");
    let ext_src = stage.join("src/ext-imp");
    let ext_path = env::join_paths([&trusted_lib]).unwrap();

    let compile_ext = |chk: &mut Checker, module: &str, body: &str| {
        let rel = module.replace('.', "/");
        let src = ext_src.join(format!("{rel}.lean"));
        fs::create_dir_all(src.parent().unwrap()).unwrap();
        fs::write(&src, body).unwrap();
        let out = trusted_lib.join(format!("{rel}.olean"));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        chk.process_with_path(
            &format!("compile-{module}"),
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-R".to_string(),
                ext_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                out.to_string_lossy().into_owned(),
                src.to_string_lossy().into_owned(),
            ],
            Some(&ext_path),
        )
        .unwrap();
    };

    compile_ext(
        &mut checker,
        "Miri.Child",
        "prelude\nimport Init.Core\nnamespace Miri.Child\ndef c : Nat := 1\nend Miri.Child\n",
    );
    compile_ext(
        &mut checker,
        "Miri.ImpTrusted",
        "prelude\nimport Init.Core\nimport Trusted\nnamespace Miri.ImpTrusted\ndef x : Nat := 0\nend Miri.ImpTrusted\n",
    );
    compile_ext(
        &mut checker,
        "FakeSysrootMiri",
        "prelude\nimport Init.Core\nimport Miri.Child\nnamespace FakeSysrootMiri\ndef x : Nat := 0\nend FakeSysrootMiri\n",
    );
    compile_ext(
        &mut checker,
        "Miri.UsesFakeSysrootMiri",
        "prelude\nimport Init.Core\nimport FakeSysrootMiri\nnamespace Miri.UsesFakeSysrootMiri\ndef x : Nat := 0\nend Miri.UsesFakeSysrootMiri\n",
    );
    compile_ext(
        &mut checker,
        "FakeSysrootRepo",
        "prelude\nimport Init.Core\nimport Trusted\nnamespace FakeSysrootRepo\ndef x : Nat := 0\nend FakeSysrootRepo\n",
    );
    compile_ext(
        &mut checker,
        "Miri.UsesFakeSysrootRepo",
        "prelude\nimport Init.Core\nimport FakeSysrootRepo\nnamespace Miri.UsesFakeSysrootRepo\ndef x : Nat := 0\nend Miri.UsesFakeSysrootRepo\n",
    );
    compile_ext(
        &mut checker,
        "FakeFoundMiri",
        "prelude\nimport Init.Core\nimport Miri.Child\nnamespace FakeFoundMiri\ndef x : Nat := 0\nend FakeFoundMiri\n",
    );
    compile_ext(
        &mut checker,
        "FakeFoundRepo",
        "prelude\nimport Init.Core\nimport Trusted\nnamespace FakeFoundRepo\ndef x : Nat := 0\nend FakeFoundRepo\n",
    );

    let search = vec![trusted_lib.clone()];

    // 1. `.vendorMiri` importing `.repo` (`Trusted`).
    let err_miri_repo = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.ImpTrusted".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err_miri_repo.code, 1);
    assert!(
        err_miri_repo.message.contains("vendor Miri module Miri.ImpTrusted cannot import Trusted"),
        "unexpected vendor->repo error: {err_miri_repo}"
    );

    // 2. `.sysrootFoundation` importing `.vendorMiri`.
    checker
        .set_sysroot_foundation_for_test(vec![
            "FakeSysrootMiri".to_string(),
            "FakeSysrootRepo".to_string(),
        ])
        .unwrap();
    let err_sys_miri = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string(), "Miri.UsesFakeSysrootMiri".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err_sys_miri.code, 1);
    assert!(
        err_sys_miri.message.contains("sysroot module FakeSysrootMiri cannot import Miri.Child"),
        "unexpected sysroot->vendor error: {err_sys_miri}"
    );

    // 3. `.sysrootFoundation` importing `.repo` (`Trusted`).
    let err_sys_repo = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.UsesFakeSysrootRepo".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err_sys_repo.code, 1);
    assert!(
        err_sys_repo.message.contains("sysroot module FakeSysrootRepo cannot import Trusted"),
        "unexpected sysroot->repo error: {err_sys_repo}"
    );

    // 4. `.foundation` importing `.vendorMiri`.
    checker
        .admitted_mut()
        .unwrap()
        .foundation_graph
        .insert("FakeFoundMiri".to_string(), Vec::new());
    let err_found_miri = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err_found_miri.code, 1);
    assert!(
        err_found_miri.message.contains("foundation module FakeFoundMiri cannot import Miri.Child"),
        "unexpected foundation->vendor error: {err_found_miri}"
    );
    checker.admitted_mut().unwrap().foundation_graph.remove("FakeFoundMiri");

    // 5. `.foundation` importing `.repo` (`Trusted`).
    checker
        .admitted_mut()
        .unwrap()
        .foundation_graph
        .insert("FakeFoundRepo".to_string(), Vec::new());
    let err_found_repo = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search,
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err_found_repo.code, 1);
    assert!(
        err_found_repo.message.contains("foundation module FakeFoundRepo cannot import Trusted"),
        "unexpected foundation->repo error: {err_found_repo}"
    );

    // 6. `checkHeaderImports` defensive `"foreign import"` rejection on a
    // `ModuleData` whose header imports a module absent from `roles`.
    let inspector_path = checker.admitted().unwrap().inspector.clone();
    let tb_lib = stage.join("tb-lib");
    fs::create_dir_all(&tb_lib).unwrap();
    let tb_olean = tb_lib.join("TrustedBoundary.olean");
    checker
        .process(
            "compile-TrustedBoundary",
            &[
                "-j1".to_string(),
                "-M4096".to_string(),
                "-t0".to_string(),
                "-R".to_string(),
                inspector_path.parent().unwrap().to_string_lossy().into_owned(),
                "-o".to_string(),
                tb_olean.to_string_lossy().into_owned(),
                inspector_path.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let driver = stage.join("check_foreign_import.lean");
    fs::write(
        &driver,
        "import TrustedBoundary\n\
         open TrustedBoundary\n\
         #eval show IO Unit from do\n\
           let roles : Std.HashMap Lean.Name RepoOrigin := {}\n\
           let md : Lean.ModuleData := {\n\
             isModule := false\n\
             imports := #[{ module := `Unlisted.Ghost }]\n\
             constNames := #[]\n\
             constants := #[]\n\
             extraConstNames := #[]\n\
             entries := #[]\n\
           }\n\
           checkHeaderImports roles `Trusted.Forged (.repo (.trusted .vetted)) \
             md RepoOrigin.importViolation?\n",
    )
    .unwrap();
    let tb_path = env::join_paths([&tb_lib]).unwrap();
    let err_foreign_imp = checker
        .process_with_path(
            "check-foreign-import",
            &["-j1".to_string(), "-M4096".to_string(), driver.to_string_lossy().into_owned()],
            Some(&tb_path),
        )
        .unwrap_err();
    assert!(
        err_foreign_imp.message.contains("policy:foreign import Unlisted.Ghost in Trusted.Forged"),
        "expected checkHeaderImports foreign-import rejection, got: {err_foreign_imp}"
    );

    // 7. `requireClaimProof` rejects an empty `reqConsts` list at runtime
    // with policy exit code `1`.
    let driver_req = stage.join("check_empty_req_consts.lean");
    fs::write(
        &driver_req,
        "import TrustedBoundary\n\
         open TrustedBoundary\n\
         #eval show IO Unit from do\n\
           let env ← Lean.mkEmptyEnvironment\n\
           let locals : Std.HashMap Lean.Name Lean.ConstantInfo := {}\n\
           requireClaimProof env locals `Trusted.Correspondence \
             `Anneal.MirCorrespondenceProof `Trusted.Correspondence.EmptyReq \
             none `Anneal.MirCorrespondenceProof.empty_req []\n",
    )
    .unwrap();
    let err_empty_req = checker
        .process_with_path(
            "check-empty-req-consts",
            &["-j1".to_string(), "-M4096".to_string(), driver_req.to_string_lossy().into_owned()],
            Some(&tb_path),
        )
        .unwrap_err();
    assert!(
        err_empty_req.message.contains(
            "policy:claim Trusted.Correspondence.EmptyReq requires a non-empty required-constants list"
        ),
        "expected requireClaimProof empty reqConsts rejection, got: {err_empty_req}"
    );
}

/// Verifies Pass 2 preflight rejects import cycles in both
/// `trusted/correspondence/` (`"Trusted correspondence import cycle"`) and
/// `correspondence/` (`"Correspondence proof import cycle"`) with policy exit
/// code `1` before compiling Miri or any Pass 2 module.
#[test]
fn rejects_pass2_correspondence_import_cycles() {
    let checkout = repo_root();
    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();
    fs::create_dir_all(fix.root.join("trusted/correspondence/Trusted")).unwrap();
    fs::create_dir_all(fix.root.join("correspondence/Anneal")).unwrap();

    // 1. Import cycle inside `trusted/correspondence/`.
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/Correspondence.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/CycleA.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.CycleB\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/CycleB.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.CycleA\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean"),
        b"prelude\nimport Trusted.Correspondence\n",
    )
    .unwrap();

    let mut checker1 = fix.checker();
    checker1.set_require_mir_wp(false);
    let err_trusted_cycle = checker1.run().unwrap_err();
    assert_eq!(err_trusted_cycle.code, 1);
    assert_eq!(err_trusted_cycle.phase, "preflight");
    assert!(
        err_trusted_cycle.message.contains("Trusted correspondence import cycle"),
        "unexpected trusted-correspondence cycle error: {err_trusted_cycle}"
    );

    // 2. Import cycle inside `correspondence/`.
    fs::remove_file(fix.root.join("trusted/correspondence/Trusted/CycleA.lean")).unwrap();
    fs::remove_file(fix.root.join("trusted/correspondence/Trusted/CycleB.lean")).unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/CycleA.lean"),
        b"prelude\nimport Init.NotationExtra\nimport Anneal.CycleB\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/CycleB.lean"),
        b"prelude\nimport Init.NotationExtra\nimport Anneal.CycleA\n",
    )
    .unwrap();

    let mut checker2 = fix.checker();
    checker2.set_require_mir_wp(false);
    let err_theory_cycle = checker2.run().unwrap_err();
    assert_eq!(err_theory_cycle.code, 1);
    assert_eq!(err_theory_cycle.phase, "preflight");
    assert!(
        err_theory_cycle.message.contains("Correspondence proof import cycle"),
        "unexpected correspondence-proof cycle error: {err_theory_cycle}"
    );
}

/// Keeps `LOCKED_LEAN_SHA256` and `LOCKED_LEAN_X86_64_LINUX_SHA256`
/// synchronized with `foundation-lock.json` `distributions` binary digests,
/// and validates `LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS` key hygiene.
#[test]
fn locked_lean_sha256_matches_foundation_lock_distributions() {
    let lock_bytes = fs::read(repo_root().join("trusted/lean/foundation-lock.json")).unwrap();
    let lock: Json = serde_json::from_slice(&lock_bytes).unwrap();
    let dists = lock["distributions"].as_object().unwrap();
    let expected: BTreeSet<String> =
        dists.values().map(|v| v.as_str().unwrap().to_ascii_lowercase()).collect();
    let actual: BTreeSet<String> =
        anneal_audit::LOCKED_LEAN_SHA256.iter().map(|s| s.to_ascii_lowercase()).collect();
    assert_eq!(actual, expected);

    let x86_64_linux_sha = dists
        .iter()
        .find_map(|(k, v)| k.contains("x86_64-unknown-linux-gnu").then(|| v.as_str().unwrap()))
        .expect("x86_64-unknown-linux-gnu entry in foundation-lock.json distributions");
    assert_eq!(
        anneal_audit::LOCKED_LEAN_X86_64_LINUX_SHA256.to_ascii_lowercase(),
        x86_64_linux_sha.to_ascii_lowercase()
    );
    let mut keys = Vec::with_capacity(anneal_audit::LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS.len());
    for &(rel, sha) in anneal_audit::LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS {
        assert!(anneal_audit::is_sha256_hex(sha), "invalid sha256 for {rel}");
        keys.push(rel);
    }
    let mut sorted = keys.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(keys, sorted, "runtime lib keys must be sorted and unique");
}

/// Verifies that Pass 2 `"correspondence-preflight"` and Pass 2 module
/// compilation run inside the isolated Linux `bwrap` sandbox: a vendored
/// `Miri.*` `[init]` initializer cannot write to the host checkout or stage
/// during `"correspondence-preflight"` or during Pass 2 elaboration, and any
/// extra file dropped into `/work/out` is rejected with policy exit code `1`.
#[cfg(target_os = "linux")]
#[test]
fn sandboxes_pass2_preflight_and_compilation_against_host_and_stage_writes() {
    let fix = TempFixture::new(None);
    let vendor_dir = fix.root.join("fake-vendor");
    fs::create_dir_all(vendor_dir.join("Miri")).unwrap();

    // Build a vendored `Miri.InitWriter` module whose `initialize` hook runs
    // whenever `importModules` loads extensions (both during
    // `"correspondence-preflight"` and during Pass 2 compilation) and attempts
    // to write to a host checkout path, plus a second module that drops an
    // unexpected file into `/work/out/sneaky-drop.txt`.
    let host_victim = fix.root.join("pass2-escape-host.txt");
    let init_host_src = format!(
        "prelude\n\
         import Init.System.IO\n\
         namespace Miri.InitHost\n\
         initialize _ : Unit ← do\n\
           IO.FS.writeFile \"{}\" \"pwned\"\n\
           pure ()\n\
         def ok : Nat := 1\n\
         end Miri.InitHost\n",
        host_victim.display()
    );
    fs::write(vendor_dir.join("Miri/InitHost.lean"), &init_host_src).unwrap();

    let mut prebuild = fix.checker();
    prebuild.set_require_mir_wp(false);
    prebuild.run().unwrap();
    prebuild.ensure_sysroot_foundation().unwrap();
    let probe_lib = prebuild.stage().join("probe-miri-lib");
    fs::create_dir_all(probe_lib.join("Miri")).unwrap();
    // Compile `Miri.InitHost` into a temporary `.olean` for digest capture
    // (the `initialize` hook does not execute while compiling its own module,
    // only when an importing process loads the `.olean` with `loadExts`).
    prebuild
        .process(
            "probe-init-host",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_lib.join("Miri/InitHost.olean").to_string_lossy().into_owned(),
                vendor_dir.join("Miri/InitHost.lean").to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    assert!(!host_victim.exists(), "compiling Miri.InitHost must not execute its initialize hook");

    // 1. `"correspondence-preflight"` runs inside `bwrap`: importing
    // `Miri.InitHost` with `loadExts := true` fails when the `[init]` hook
    // tries to write outside `/work/out`, leaving `host_victim` untouched.
    fs::create_dir_all(prebuild.stage().join("theory-lib")).unwrap();
    let src_dir = prebuild.stage().join("src/p2-sandbox-test");
    fs::create_dir_all(src_dir.join("Trusted")).unwrap();
    let sample_src = src_dir.join("Trusted/Correspondence.lean");
    fs::write(
        &sample_src,
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nimport Miri.InitHost\n\
         def c : Nat := Miri.InitHost.ok\n",
    )
    .unwrap();
    let trusted_base_src = prebuild.modules()["Trusted"].clone();
    let err_pf = prebuild
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: vec![
                prebuild.stage().join("lib"),
                prebuild.stage().join("theory-lib"),
                probe_lib.clone(),
            ],
            trusted: vec!["Trusted".to_string()],
            theory: vec![],
            vendor_miri: vec!["Miri.InitHost".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.Correspondence".to_string(), sample_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf.code, 2, "expected sandboxed correspondence-preflight failure: {err_pf}");
    assert!(
        !err_pf.message.contains("bwrap:"),
        "bwrap itself must launch Lean rather than failing on mount setup: {err_pf}"
    );
    assert!(
        err_pf.message.contains("pass2-escape-host.txt"),
        "expected failure from the malicious [init] host write attempt: {err_pf}"
    );
    assert!(
        !host_victim.exists(),
        "sandboxed correspondence-preflight must not write to host checkout"
    );

    // 2. Even if a vendored `[init]` drops an extra file inside the sole
    // writable `/work/out` directory during `"correspondence-preflight"`,
    // `anneal-audit` rejects it with policy exit code `1` before trusting
    // `result.json`.
    let init_drop_src = "prelude\n\
        import Init.System.IO\n\
        namespace Miri.InitDrop\n\
        initialize _ : Unit ← do\n\
          IO.FS.writeFile \"/work/out/sneaky-drop.txt\" \"junk\"\n\
          pure ()\n\
        def ok : Nat := 1\n\
        end Miri.InitDrop\n";
    fs::write(vendor_dir.join("Miri/InitDrop.lean"), init_drop_src).unwrap();
    prebuild
        .process(
            "probe-init-drop",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                probe_lib.join("Miri/InitDrop.olean").to_string_lossy().into_owned(),
                vendor_dir.join("Miri/InitDrop.lean").to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let sample_drop_src = src_dir.join("Trusted/DropTest.lean");
    fs::write(
        &sample_drop_src,
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nimport Miri.InitDrop\n\
         def c : Nat := Miri.InitDrop.ok\n",
    )
    .unwrap();
    let err_drop = prebuild
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: vec![
                prebuild.stage().join("lib"),
                prebuild.stage().join("theory-lib"),
                probe_lib.clone(),
            ],
            trusted: vec!["Trusted".to_string()],
            theory: vec![],
            vendor_miri: vec!["Miri.InitDrop".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src)],
            sources: vec![("Trusted.DropTest".to_string(), sample_drop_src)],
        })
        .unwrap_err();
    assert_eq!(
        err_drop.code, 2,
        "expected Door 1 rejection for unexpected file in /work/out: {err_drop}"
    );
    assert!(
        err_drop.message.contains("unexpected inspector outputs"),
        "unexpected error message: {err_drop}"
    );

    // 3. Pass 2 module compilation (`run_correspondence_with_closure`) runs
    // inside `bwrap`: a vendored `[init]` that stays silent during
    // `"correspondence-preflight"` (where `/work/src/corr-trusted` is absent)
    // and attempts to write to the host checkout during Pass 2 compilation
    // fails inside the sandbox, leaving `compile_host_victim` untouched.
    let compile_host_victim = fix.root.join("pass2-compile-escape-host.txt");
    let init_compile_host_src = format!(
        "prelude\n\
         import Init.System.IO\n\
         namespace Miri.InitCompileHost\n\
         initialize _ : Unit ← do\n\
           if ← System.FilePath.pathExists \"/work/src/corr-trusted\" then\n\
             IO.FS.writeFile \"{}\" \"pwned\"\n\
           pure ()\n\
         def ok : Nat := 1\n\
         end Miri.InitCompileHost\n",
        compile_host_victim.display()
    );
    fs::write(vendor_dir.join("Miri/InitCompileHost.lean"), &init_compile_host_src).unwrap();
    let compile_host_olean = probe_lib.join("Miri/InitCompileHost.olean");
    prebuild
        .process(
            "probe-init-compile-host",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                compile_host_olean.to_string_lossy().into_owned(),
                vendor_dir.join("Miri/InitCompileHost.lean").to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let compile_host_entry = MiriClosureEntry {
        module: "Miri.InitCompileHost".to_string(),
        path: "Miri/InitCompileHost.lean".to_string(),
        olean_sha256: sha256_file(&compile_host_olean, "test").unwrap(),
        olean_server_sha256: None,
        olean_private_sha256: None,
    };
    let compile_host_sources = BTreeMap::from([(
        "Miri/InitCompileHost.lean".to_string(),
        sha256_bytes(init_compile_host_src.as_bytes()),
    )]);
    // Run Pass 1 on fresh checkers before creating `trusted/correspondence/`
    // and `correspondence/` so `Checker::run()` completes Pass 1 without
    // demanding `vendor/lean-miri/upstream-pin.json`.
    let mut c3 = fix.checker();
    c3.set_require_mir_wp(false);
    c3.run().unwrap();
    let mut c4 = fix.checker();
    c4.set_require_mir_wp(false);
    c4.run().unwrap();
    fs::create_dir_all(fix.root.join("trusted/correspondence/Trusted")).unwrap();
    fs::create_dir_all(fix.root.join("correspondence/Anneal")).unwrap();
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/Correspondence.lean"),
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nimport Miri.InitCompileHost\n\
         def c : Nat := Miri.InitCompileHost.ok\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean"),
        "prelude\nimport Trusted.Correspondence\n\
         def p : Nat := c\n",
    )
    .unwrap();
    let err_compile_host = c3
        .run_correspondence_with_closure(
            &BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            &vendor_dir,
            "0000000000000000000000000000000000000000",
            &[compile_host_entry],
            &compile_host_sources,
        )
        .unwrap_err();
    assert_eq!(
        err_compile_host.code, 2,
        "expected sandboxed Pass 2 compile failure: {err_compile_host}"
    );
    assert_eq!(err_compile_host.phase, "compile-Trusted.Correspondence");
    assert!(
        !err_compile_host.message.contains("bwrap:"),
        "bwrap itself must launch Lean rather than failing on mount setup: {err_compile_host}"
    );
    assert!(
        err_compile_host.message.contains("pass2-compile-escape-host.txt"),
        "expected failure from the malicious [init] host write attempt: {err_compile_host}"
    );
    assert!(
        !compile_host_victim.exists(),
        "sandboxed Pass 2 compilation must not write to host checkout"
    );

    // 4. Even if a vendored `[init]` drops an extra file into `/work/out`
    // during Pass 2 compilation, `anneal-audit` Door 1 rejects it and stages
    // nothing into `lib/`.
    let init_compile_drop_src = "prelude\n\
        import Init.System.IO\n\
        namespace Miri.InitCompileDrop\n\
        initialize _ : Unit ← do\n\
          if ← System.FilePath.pathExists \"/work/src/corr-trusted\" then\n\
            IO.FS.writeFile \"/work/out/sneaky-pass2.txt\" \"junk\"\n\
          pure ()\n\
        def ok : Nat := 1\n\
        end Miri.InitCompileDrop\n";
    fs::write(vendor_dir.join("Miri/InitCompileDrop.lean"), init_compile_drop_src).unwrap();
    let compile_drop_olean = probe_lib.join("Miri/InitCompileDrop.olean");
    prebuild
        .process(
            "probe-init-compile-drop",
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-DElab.async=false".to_string(),
                "-Ddebug.skipKernelTC=false".to_string(),
                "-R".to_string(),
                vendor_dir.to_string_lossy().into_owned(),
                "-o".to_string(),
                compile_drop_olean.to_string_lossy().into_owned(),
                vendor_dir.join("Miri/InitCompileDrop.lean").to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let compile_drop_entry = MiriClosureEntry {
        module: "Miri.InitCompileDrop".to_string(),
        path: "Miri/InitCompileDrop.lean".to_string(),
        olean_sha256: sha256_file(&compile_drop_olean, "test").unwrap(),
        olean_server_sha256: None,
        olean_private_sha256: None,
    };
    let compile_drop_sources = BTreeMap::from([(
        "Miri/InitCompileDrop.lean".to_string(),
        sha256_bytes(init_compile_drop_src.as_bytes()),
    )]);
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/Correspondence.lean"),
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nimport Miri.InitCompileDrop\n\
         def c : Nat := Miri.InitCompileDrop.ok\n",
    )
    .unwrap();
    let err_compile_drop = c4
        .run_correspondence_with_closure(
            &BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            &vendor_dir,
            "0000000000000000000000000000000000000000",
            &[compile_drop_entry],
            &compile_drop_sources,
        )
        .unwrap_err();
    assert_eq!(
        err_compile_drop.code, 2,
        "expected Door 1 rejection for unexpected file in Pass 2 /work/out: {err_compile_drop}"
    );
    assert!(
        err_compile_drop.message.contains("unexpected compiler outputs"),
        "unexpected error message: {err_compile_drop}"
    );
    assert!(
        !c4.stage().join("lib/Trusted/Correspondence.olean").exists(),
        "rejected Pass 2 output must not be staged into lib/"
    );
}

#[test]
fn precompiled_inspector_cache_keys_on_inspector_source_digest() {
    let mut fix = TempFixture::isolated(Some(&format!("{HEADER}def ok : Nat := 1\n")));

    // 1. First run compiles `TrustedBoundary.lean` into `.olean` and populates
    // the in-process cache.
    fix.check_expected(None, None, None).unwrap();

    let orig_inspector = fs::read_to_string(fix.root.join("trusted/audit/TrustedBoundary.lean"))
        .expect("read staged TrustedBoundary.lean");

    // 2. A syntactically or type-invalid edit to `TrustedBoundary.lean` must
    // miss the cache and fail closed in `compile-inspector` rather than
    // reusing the cached `.olean`.
    fs::write(
        fix.root.join("trusted/audit/TrustedBoundary.lean"),
        format!("{orig_inspector}\ndef brokenInspectorType : Nat := \"not a nat\"\n"),
    )
    .unwrap();
    let err_compile =
        fix.check_expected(Some(2), Some("compile-inspector"), Some(false)).unwrap_err();
    assert!(
        err_compile.message.contains("Lean exited"),
        "expected compile-inspector failure, got: {err_compile}"
    );

    // 3. A valid edit to `TrustedBoundary.lean` that changes policy behavior
    // must recompile and execute the modified inspector rather than serving
    // stale cached `.olean` bytes.
    let needle = "  | \"preflight\" =>";
    let replacement =
        "  | \"preflight\" =>\n    throw <| IO.userError \"policy: mutated inspector sentinel\"";
    assert!(
        orig_inspector.contains(needle),
        "expected preflight dispatch arm in TrustedBoundary.lean"
    );
    fs::write(
        fix.root.join("trusted/audit/TrustedBoundary.lean"),
        orig_inspector.replacen(needle, replacement, 1),
    )
    .unwrap();
    let err_policy = fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err_policy.message.contains("mutated inspector sentinel"),
        "expected modified inspector policy error, got: {err_policy}"
    );
}

#[cfg(unix)]
#[test]
fn precompiled_inspector_handles_colon_in_tmpdir_and_drops_lean_path() {
    let fix = TempFixture::isolated(Some(&format!("{HEADER}def ok : Nat := 1\n")));

    // Construct a `TMPDIR` containing the Unix `LEAN_PATH` delimiter (`:`) and
    // place a corrupt decoy `TrustedBoundary.olean` at the split prefix so any
    // non-relative `LEAN_PATH` serialization fails immediately.
    let outer = tempfile::Builder::new().prefix("anneal-colon-tmp-").tempdir().unwrap();
    let split_prefix = outer.path().join("evil");
    fs::create_dir_all(&split_prefix).unwrap();
    fs::write(split_prefix.join("TrustedBoundary.olean"), b"corrupt-decoy").unwrap();
    let colon_tmpdir = outer.path().join("evil:sub");
    fs::create_dir_all(&colon_tmpdir).unwrap();

    // Run `anneal-audit` in a child process with `TMPDIR=<outer>/evil:sub`
    // (avoiding mutating the test binary's global `TMPDIR`) and verify the
    // relative `LEAN_PATH="control"` succeeds without touching the decoy.
    // Note: `TempFixture` omits `Trusted.MirAst`/`Anneal.MirWp`, so the binary
    // executes `"preflight"`, compiles `Trusted.lean`, and reaches `"audit"`
    // cleanly before `require_mir_wp` checks MIR modules; reaching the
    // `"audit"` phase proves both preflight and audit inspector runs succeeded
    // under the colon-containing `TMPDIR`.
    let lean = default_lean_path();
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-audit-test-bin"))
        .arg("--anneal-root")
        .arg(&fix.root)
        .arg("--lean")
        .arg(&lean)
        .env("TMPDIR", &colon_tmpdir)
        .output()
        .expect("run anneal-audit with colon TMPDIR");
    let combined = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        combined.contains("Trusted check failed (audit):") || output.status.success(),
        "expected inspector preflight+audit to run under colon TMPDIR, got {:?}: {combined}",
        output.status.code()
    );
    assert!(
        !combined.contains("unknown module prefix 'TrustedBoundary'")
            && !combined.contains("corrupt-decoy"),
        "colon TMPDIR must not split LEAN_PATH or read decoy prefix: {combined}"
    );

    // Part 2: verify `TrustedBoundary.initHermeticSearchPath` drops the
    // bootstrap `LEAN_PATH="control"` from `Lean.searchPathRef` before
    // `importCorrEnv` loads modules, so `control/TrustedBoundary.olean` is
    // never visible as an importable module.
    let mut checker = fix.checker_with_lean(Some(&lean));
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let sysroot = checker.admitted().unwrap().prefix.clone();
    let req_path = checker.stage().join("drop-lean-path-req.json");
    let res_path = checker.stage().join("drop-lean-path-res.json");
    let req = json!({
        "mode": "correspondence-preflight",
        "sysroot": sysroot.to_string_lossy(),
        "searchPath": [],
        "foundation": ["TrustedBoundary"],
        "sysrootFoundation": [],
        "trusted": [],
        "theory": [],
        "vendorMiri": [],
        "moduleTiers": [],
        "sources": [],
    });
    fs::write(&req_path, serde_json::to_vec(&req).unwrap()).unwrap();
    let drop_out = Command::new(&lean)
        .current_dir(checker.stage())
        .env_clear()
        .env("LEAN_PATH", "control")
        .args([
            "-j1",
            "-M2048",
            "--run",
            checker.stage().join("control/TrustedBoundaryEntry.lean").to_str().unwrap(),
            req_path.to_str().unwrap(),
            res_path.to_str().unwrap(),
        ])
        .output()
        .expect("run precompiled inspector for initHermeticSearchPath check");
    assert_eq!(
        drop_out.status.code(),
        Some(2),
        "expected exit code 2 when initHermeticSearchPath drops LEAN_PATH: stdout={} stderr={}",
        String::from_utf8_lossy(&drop_out.stdout),
        String::from_utf8_lossy(&drop_out.stderr),
    );
    let drop_res = fs::read_to_string(&res_path).expect("read inspector result json");
    assert!(
        drop_res.contains("unknown module prefix 'TrustedBoundary'"),
        "initHermeticSearchPath must drop LEAN_PATH before importCorrEnv, got: {drop_res}"
    );
}

/// Repository auditing (`Checker::run`) restricts imports in `trusted/lean/`
/// and `theory/` to `foundation-lock.json` even when
/// `trusted/audit/library-lock.json` is present (`library-lock.json` applies
/// exclusively to `targetAudit`), while `vetted` modules are rejected even
/// earlier at tier-import preflight for non-foundation `Init.*` imports.
#[test]
fn rejects_library_lock_imports_in_repository_audit() {
    let checkout = repo_root();

    let mut vetted_fix = TempFixture::new(Some(
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Data.BitVec.Lemmas\n",
    ));
    fs::copy(
        checkout.join("trusted/audit/library-lock.json"),
        vetted_fix.root.join("trusted/audit/library-lock.json"),
    )
    .unwrap();
    let err = vetted_fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err.message.contains(
            "vetted module Trusted cannot import non-foundation module Init.Data.BitVec.Lemmas"
        ),
        "unexpected error: {err}"
    );

    let mut cand_fix = TempFixture::new(Some(
        "-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.Data.BitVec.Lemmas\n",
    ));
    fs::copy(
        checkout.join("trusted/audit/library-lock.json"),
        cand_fix.root.join("trusted/audit/library-lock.json"),
    )
    .unwrap();
    let err = cand_fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err.message.contains("foreign/missing import Init.Data.BitVec.Lemmas in Trusted"),
        "unexpected error: {err}"
    );

    let mut theory_fix = TempFixture::new(Some(
        "-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.Core\n",
    ));
    fs::copy(
        checkout.join("trusted/audit/library-lock.json"),
        theory_fix.root.join("trusted/audit/library-lock.json"),
    )
    .unwrap();
    fs::create_dir_all(theory_fix.root.join("theory/Anneal")).unwrap();
    fs::write(
        theory_fix.root.join("theory/Anneal/Helper.lean"),
        "prelude\nimport Init.Data.BitVec.Lemmas\n",
    )
    .unwrap();
    fs::write(
        theory_fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Helper\n",
    )
    .unwrap();
    let err = theory_fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err.message.contains("foreign/missing import Init.Data.BitVec.Lemmas in Anneal.Helper"),
        "unexpected error: {err}"
    );
}

/// Default `Checker::new` (`require_mir_wp == true`) rejects Pass 1 fail-closed
/// even if *every* MIR and PureLift module (`Trusted.MirAst`,
/// `Trusted.MirSemantics`, `Anneal.MirWp`, `Anneal.PureLift`) is deleted at
/// once, leaving only `Trusted.lean`.
#[test]
fn default_checker_rejects_complete_mir_wp_deletion() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "audit", "unexpected phase: {err}");
    assert!(
        err.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err}"
    );
}

/// `verify_bundled_resources` accepts the real repository checkout and rejects
/// reintroduced legacy `bundled_resources.rs` or `bundled_theory.json`, any
/// checked-in `packaged/` staging directory, missing/symlinked `build.rs`,
/// `trusted_bundle.rs`, or `theory_bundle.rs`, drifted or symlinked
/// `theory/bundle-manifest.json` / `theory/` files, missing or symlinked
/// `TRUSTED_BUNDLE_SOURCES`, `THEORY_BUNDLE_MANIFEST`, and `PROVENANCE_SOURCES`
/// files and parent directories, invalid, tampered, duplicate, unsorted, or
/// out-of-tree theory manifest entries, and untracked `.lean` files under
/// `correspondence/` or `trusted/correspondence/` with policy exit code `1`.
/// Each symlink fixture points at byte-identical content, so only the
/// regular-file checks can reject it.
#[test]
fn enforces_bundled_resources_parity_and_regular_files() {
    use anneal_audit::{
        bundle::{
            LEGACY_BUNDLE_DESTINATION, LEGACY_THEORY_BUNDLE_DESTINATION,
            PACKAGED_BUNDLE_DESTINATION, PROVENANCE_SOURCES, THEORY_BUNDLE_MANIFEST,
            TRUSTED_BUNDLE_SOURCES, TheoryBundleManifest, load_theory_bundle_manifest,
            render_bundled_resources, render_bundled_theory,
        },
        verify_bundled_resources,
    };

    let checkout = repo_root();
    verify_bundled_resources(&checkout).unwrap();

    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path().join("repo");
    let (_, manifest) = load_theory_bundle_manifest(&checkout).unwrap();
    for rel in TRUSTED_BUNDLE_SOURCES
        .iter()
        .copied()
        .chain(PROVENANCE_SOURCES.iter().copied())
        .chain(std::iter::once(THEORY_BUNDLE_MANIFEST))
        .chain(manifest.modules.iter().map(|entry| entry.path.as_str()))
        .chain([
            "trusted/cargo-anneal/build.rs",
            "trusted/cargo-anneal/src/trusted_bundle.rs",
            "trusted/cargo-anneal/src/theory_bundle.rs",
        ])
    {
        let dst = root.join(rel);
        fs::create_dir_all(dst.parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), dst).unwrap();
    }
    let canonical = render_bundled_resources(&root).unwrap();
    let canonical_theory = render_bundled_theory(&root).unwrap();
    verify_bundled_resources(&root).unwrap();

    let expect_policy = |needle: &str| {
        let err = verify_bundled_resources(&root).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert_eq!(err.phase, "bundle-manifest", "{err}");
        assert!(err.message.contains(needle), "expected {needle:?}: {err}");
    };

    // 1. Reintroduced legacy `src/bundled_resources.rs` or
    // `src/bundled_theory.json` -> policy error.
    let legacy_dest = root.join(LEGACY_BUNDLE_DESTINATION);
    fs::write(&legacy_dest, canonical.as_bytes()).unwrap();
    expect_policy("legacy checked-in bundled_resources.rs must be absent");
    fs::remove_file(&legacy_dest).unwrap();
    let legacy_theory_dest = root.join(LEGACY_THEORY_BUNDLE_DESTINATION);
    fs::write(&legacy_theory_dest, canonical_theory.as_bytes()).unwrap();
    expect_policy("legacy checked-in bundled_theory.json must be absent");
    fs::remove_file(&legacy_theory_dest).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 2. Missing or symlinked `trusted/cargo-anneal/build.rs` -> policy error.
    let build_rs = root.join("trusted/cargo-anneal/build.rs");
    let outside_build_rs = tmp.path().join("outside-build.rs");
    fs::rename(&build_rs, &outside_build_rs).unwrap();
    expect_policy("missing canonical bundle source: trusted/cargo-anneal/build.rs");
    symlink(&outside_build_rs, &build_rs).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&build_rs).unwrap();
    fs::rename(&outside_build_rs, &build_rs).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 3. Missing or symlinked `src/trusted_bundle.rs` or `src/theory_bundle.rs`
    // -> policy error.
    let trusted_bundle_rs = root.join("trusted/cargo-anneal/src/trusted_bundle.rs");
    let outside_tb_rs = tmp.path().join("outside-trusted_bundle.rs");
    fs::rename(&trusted_bundle_rs, &outside_tb_rs).unwrap();
    expect_policy("missing canonical bundle source: trusted/cargo-anneal/src/trusted_bundle.rs");
    symlink(&outside_tb_rs, &trusted_bundle_rs).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&trusted_bundle_rs).unwrap();
    fs::rename(&outside_tb_rs, &trusted_bundle_rs).unwrap();
    let theory_bundle_rs = root.join("trusted/cargo-anneal/src/theory_bundle.rs");
    let outside_thb_rs = tmp.path().join("outside-theory_bundle.rs");
    fs::rename(&theory_bundle_rs, &outside_thb_rs).unwrap();
    expect_policy("missing canonical bundle source: trusted/cargo-anneal/src/theory_bundle.rs");
    symlink(&outside_thb_rs, &theory_bundle_rs).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&theory_bundle_rs).unwrap();
    fs::rename(&outside_thb_rs, &theory_bundle_rs).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 4. Checked-in transient `packaged/` staging dir -> policy error.
    let pkg_dest = root.join(PACKAGED_BUNDLE_DESTINATION);
    let pkg_dir = pkg_dest.parent().unwrap().to_path_buf();
    fs::create_dir_all(&pkg_dir).unwrap();
    fs::write(&pkg_dest, canonical.as_bytes()).unwrap();
    expect_policy("transient packaged/ staging directory must not be checked in");
    fs::remove_dir_all(&pkg_dir).unwrap();
    let outside_pkg_dir = tmp.path().join("outside-packaged");
    fs::create_dir_all(&outside_pkg_dir).unwrap();
    fs::write(outside_pkg_dir.join("bundled_resources.rs"), canonical.as_bytes()).unwrap();
    symlink(&outside_pkg_dir, &pkg_dir).unwrap();
    expect_policy("transient packaged/ staging directory must not be checked in");
    fs::remove_file(&pkg_dir).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 5. Symlinked theory source file -> policy rejection (code 1).
    let source = root.join("theory/Anneal/MirWp.lean");
    let outside_source = tmp.path().join("outside-MirWp.lean");
    fs::rename(&source, &outside_source).unwrap();
    symlink(&outside_source, &source).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&source).unwrap();
    fs::rename(&outside_source, &source).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 6. Symlinked parent directory of a theory source file -> policy
    // rejection (code 1).
    let source_dir = root.join("theory/Anneal");
    let outside_source_dir = tmp.path().join("outside-Anneal");
    fs::rename(&source_dir, &outside_source_dir).unwrap();
    symlink(&outside_source_dir, &source_dir).unwrap();
    expect_policy("bundle source parent must be a regular directory");
    fs::remove_file(&source_dir).unwrap();
    fs::rename(&outside_source_dir, &source_dir).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 7. Missing theory source file -> policy rejection (code 1).
    fs::remove_file(&source).unwrap();
    expect_policy("missing canonical bundle source: theory/Anneal/MirWp.lean");
    fs::copy(checkout.join("theory/Anneal/MirWp.lean"), &source).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 8. Symlinked `PROVENANCE_SOURCES` file -> policy rejection (code 1).
    let prov = root.join("trusted/correspondence/Trusted/Correspondence.lean");
    let outside_prov = tmp.path().join("outside-Correspondence.lean");
    fs::rename(&prov, &outside_prov).unwrap();
    symlink(&outside_prov, &prov).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&prov).unwrap();
    fs::rename(&outside_prov, &prov).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 9. Extra untracked `.lean` file in `correspondence/` -> policy rejection
    // (code 1) so Pass 2 certified files cannot silently drift out of the
    // provenance inventory.
    let extra_corr = root.join("correspondence/Anneal/ExtraProof.lean");
    fs::write(&extra_corr, b"prelude\n").unwrap();
    expect_policy("correspondence provenance inventory mismatch");
    fs::remove_file(&extra_corr).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 10. Extra untracked `.lean` file in `trusted/correspondence/` -> policy
    // rejection (code 1).
    let extra_trusted_corr = root.join("trusted/correspondence/Trusted/ExtraAdapter.lean");
    fs::write(&extra_trusted_corr, b"prelude\n").unwrap();
    expect_policy("correspondence provenance inventory mismatch");
    fs::remove_file(&extra_trusted_corr).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 11. Drifted theory source + manifest vs compiled-in
    // `EMBEDDED_THEORY_BUNDLE_JSON` -> policy rejection (code 1).
    let manifest_path = root.join(THEORY_BUNDLE_MANIFEST);
    let original_manifest_bytes = fs::read(&manifest_path).unwrap();
    let orig_mir_wp = fs::read(&source).unwrap();
    let drifted_mir_wp = format!("{}\n-- drifted\n", String::from_utf8_lossy(&orig_mir_wp));
    fs::write(&source, drifted_mir_wp.as_bytes()).unwrap();
    let mut drifted_manifest = manifest.clone();
    drifted_manifest
        .modules
        .iter_mut()
        .find(|m| m.path == "theory/Anneal/MirWp.lean")
        .unwrap()
        .sha256 = sha256_bytes(drifted_mir_wp.as_bytes());
    drifted_manifest.theory_merkle_root =
        Some(anneal_audit::bundle::compute_theory_merkle_root(&drifted_manifest.modules));
    fs::write(
        &manifest_path,
        format!("{}\n", serde_json::to_string_pretty(&drifted_manifest).unwrap()),
    )
    .unwrap();
    if cargo_anneal::EMBEDDED_THEORY_BUNDLE_JSON_OPT.is_some() {
        expect_policy("embedded cargo-anneal EMBEDDED_THEORY_BUNDLE_JSON differs");
    } else {
        // Under `default-features = false` (`bundled-theory` disabled),
        // consistent updates to `theory/` and `theory/bundle-manifest.json`
        // succeed without invalidating `cargo-anneal`.
        verify_bundled_resources(&root).unwrap();
    }
    fs::write(&source, &orig_mir_wp).unwrap();
    fs::write(&manifest_path, &original_manifest_bytes).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 12. Theory manifest fail-closed rejections: tampered hash, tampered
    // Merkle root, incompatible Trusted/ Merkle root, duplicate entry, unsorted
    // entry, out-of-tree / path-traversal / umbrella paths, missing required
    // `MirWp.lean`, unknown JSON field, wrong schema, symlink, and missing
    // manifest.
    let write_manifest = |m: &TheoryBundleManifest| {
        fs::write(&manifest_path, format!("{}\n", serde_json::to_string_pretty(m).unwrap()))
            .unwrap();
    };

    let mut bad_merkle = manifest.clone();
    bad_merkle.theory_merkle_root = Some("0".repeat(64));
    write_manifest(&bad_merkle);
    expect_policy("theory_merkle_root mismatch");

    let mut bad_trusted_compat = manifest.clone();
    bad_trusted_compat.compatible_trusted_merkle_roots = Some(vec!["f".repeat(64)]);
    write_manifest(&bad_trusted_compat);
    expect_policy("incompatible with embedded Ring-0 Trusted/ Merkle root");

    let mut bad_hash = manifest.clone();
    bad_hash.modules[0].sha256 = "0".repeat(64);
    bad_hash.theory_merkle_root =
        Some(anneal_audit::bundle::compute_theory_merkle_root(&bad_hash.modules));
    write_manifest(&bad_hash);
    expect_policy("theory bundle manifest SHA-256 mismatch");

    let mut dup = manifest.clone();
    let first = dup.modules[0].clone();
    dup.modules.push(first);
    write_manifest(&dup);
    expect_policy("duplicate theory bundle path");

    let mut unsorted = manifest.clone();
    unsorted.modules.swap(0, 1);
    write_manifest(&unsorted);
    expect_policy("unsorted theory bundle entry");

    let mut out_of_tree = manifest.clone();
    out_of_tree.modules[0].path = "trusted/lean/Trusted.lean".to_owned();
    write_manifest(&out_of_tree);
    expect_policy("must reside under theory/Anneal/");

    let mut traversal = manifest.clone();
    traversal.modules[0].path = "theory/Anneal/../Trusted.lean".to_owned();
    write_manifest(&traversal);
    expect_policy("invalid relative theory bundle path");

    let mut umbrella = manifest.clone();
    umbrella.modules[0].path = "theory/Anneal.lean".to_owned();
    write_manifest(&umbrella);
    expect_policy("must name a module under theory/Anneal/");

    let mut missing_mir_wp = manifest.clone();
    missing_mir_wp.modules.retain(|entry| entry.path != "theory/Anneal/MirWp.lean");
    write_manifest(&missing_mir_wp);
    expect_policy("missing required theory module: theory/Anneal/MirWp.lean");

    let mut wrong_schema = manifest.clone();
    wrong_schema.schema_version = 99;
    write_manifest(&wrong_schema);
    expect_policy("unsupported schema_version 99");

    fs::write(&manifest_path, b"{\"schema_version\": 1, \"modules\": [], \"extra\": true}\n")
        .unwrap();
    expect_policy("malformed theory/bundle-manifest.json");

    fs::remove_file(&manifest_path).unwrap();
    expect_policy("missing canonical bundle source: theory/bundle-manifest.json");

    let outside_manifest = tmp.path().join("outside-manifest.json");
    fs::write(&outside_manifest, &original_manifest_bytes).unwrap();
    symlink(&outside_manifest, &manifest_path).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&manifest_path).unwrap();
    fs::write(&manifest_path, &original_manifest_bytes).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 13. Drifted canonical trusted source or provenance file vs compiled-in
    // `cargo_anneal` bundle -> policy rejection (code 1).
    let trusted_entry = root.join("trusted/lean/Trusted.lean");
    let orig_trusted_entry = fs::read(&trusted_entry).unwrap();
    let drifted_entry = format!("{}\n-- drifted\n", String::from_utf8_lossy(&orig_trusted_entry));
    fs::write(&trusted_entry, drifted_entry).unwrap();
    expect_policy("embedded cargo-anneal BUNDLE entry trusted/lean/Trusted.lean differs");
    fs::write(&trusted_entry, &orig_trusted_entry).unwrap();
    verify_bundled_resources(&root).unwrap();

    // Pass-2 `correspondence/` edits with valid inventory no longer invalidate
    // `cargo-anneal` (since `CORRESPONDENCE_PROVENANCE_JSON` is decoupled from
    // `cargo-anneal`), while Ring-0 `Trusted.lean` edits still fail closed.
    let orig_prov = fs::read(&prov).unwrap();
    fs::write(&prov, format!("{}\n-- drifted\n", String::from_utf8_lossy(&orig_prov))).unwrap();
    verify_bundled_resources(&root).unwrap();
    fs::write(&prov, &orig_prov).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 14. Missing `PROVENANCE_SOURCES` file -> policy rejection (code 1).
    fs::remove_file(&prov).unwrap();
    expect_policy(
        "missing canonical bundle source: trusted/correspondence/Trusted/Correspondence.lean",
    );
}

/// `anneal-audit` rejects a checkout from which `trusted/cargo-anneal/build.rs`
/// was deleted, and `check_cargo_boundary` still rejects `package.build` in
/// `trusted/cargo-anneal` and `build.rs` in all other workspace members.
#[test]
fn rejects_deleted_build_generator_and_disallowed_build_scripts() {
    use anneal_audit::check_cargo_boundary;

    let checkout = repo_root();
    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();

    // Deleting `trusted/cargo-anneal/build.rs` fails `Checker::run`.
    let build_rs_path = fix.root.join("trusted/cargo-anneal/build.rs");
    let outside_dir = tempfile::tempdir().unwrap();
    let outside_build_rs = outside_dir.path().join("build.rs");
    fs::copy(&build_rs_path, &outside_build_rs).unwrap();
    fs::remove_file(&build_rs_path).unwrap();
    let mut checker = fix.checker();
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "cargo-boundary", "unexpected phase: {err}");
    assert!(
        err.message.contains("missing required build script trusted/cargo-anneal/build.rs"),
        "unexpected error: {err}"
    );
    assert!(!checker.execution_began());

    // Symlinked or directory `trusted/cargo-anneal/build.rs` also fails with
    // policy code 1 in `check_cargo_boundary`.
    symlink(&outside_build_rs, &build_rs_path).unwrap();
    let err_symlink = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_symlink.code, 1, "{err_symlink}");
    assert!(
        err_symlink.message.contains("build script must be a regular file"),
        "{err_symlink}"
    );
    fs::remove_file(&build_rs_path).unwrap();

    fs::create_dir(&build_rs_path).unwrap();
    let err_dir = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_dir.code, 1, "{err_dir}");
    assert!(
        err_dir.message.contains("build script must be a regular file"),
        "{err_dir}"
    );
    fs::remove_dir(&build_rs_path).unwrap();

    // Restore `build.rs`, then confirm `package.build` in `cargo-anneal` and
    // `build.rs` in `trusted/audit` are still rejected.
    fs::copy(&outside_build_rs, &build_rs_path).unwrap();
    check_cargo_boundary(&fix.root).unwrap();

    let cargo_anneal_toml = fix.root.join("trusted/cargo-anneal/Cargo.toml");
    let orig_toml = fs::read_to_string(&cargo_anneal_toml).unwrap();
    fs::write(
        &cargo_anneal_toml,
        orig_toml.replace("edition = \"2024\"\n", "edition = \"2024\"\nbuild = \"build.rs\"\n"),
    )
    .unwrap();
    let err_pkg_build = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_pkg_build.code, 1);
    assert!(err_pkg_build.message.contains("disallowed package.build"), "{err_pkg_build}");
    fs::write(&cargo_anneal_toml, orig_toml).unwrap();

    fs::write(fix.root.join("trusted/audit/build.rs"), b"fn main() {}\n").unwrap();
    let err_audit_build = check_cargo_boundary(&fix.root).unwrap_err();
    assert_eq!(err_audit_build.code, 1);
    assert!(
        err_audit_build.message.contains("disallowed build script trusted/audit/build.rs"),
        "{err_audit_build}"
    );
    fs::remove_file(fix.root.join("trusted/audit/build.rs")).unwrap();
}

/// `scan_lean_tree` admits `theory/bundle-manifest.json` without requiring a
/// monolithic `theory/Anneal.lean` umbrella (while still admitting synthetic
/// `theory/Anneal.lean` fixtures, rejecting any other non-Lean file in
/// `theory/` or `bundle-manifest.json` in `trusted/lean/`, and requiring
/// `Trusted.lean` in `trusted/lean/`), while `Checker::run` fails closed if
/// `theory/bundle-manifest.json` is deleted or legacy `src/bundled_theory.json`
/// is reintroduced.
#[test]
fn admits_only_theory_bundle_manifest_and_rejects_deleted_theory_bundle() {
    use anneal_audit::scan_lean_tree;

    let checkout = repo_root();
    let theory_mods = scan_lean_tree(&checkout.join("theory"), "Anneal").unwrap();
    assert!(!theory_mods.contains_key("Anneal"));
    assert!(theory_mods.contains_key("Anneal.Scalar"));
    assert!(theory_mods.contains_key("Anneal.Wp"));
    assert!(theory_mods.contains_key("Anneal.MirWp"));

    let tmp = tempfile::tempdir().unwrap();
    let theory_root = tmp.path().join("theory");
    fs::create_dir_all(theory_root.join("Anneal")).unwrap();
    fs::write(theory_root.join("Anneal/Scalar.lean"), b"prelude\n").unwrap();
    fs::write(theory_root.join("bundle-manifest.json"), b"{}\n").unwrap();
    let no_umbrella_mods = scan_lean_tree(&theory_root, "Anneal").unwrap();
    assert!(!no_umbrella_mods.contains_key("Anneal"));
    assert!(no_umbrella_mods.contains_key("Anneal.Scalar"));
    fs::write(theory_root.join("Anneal.lean"), b"prelude\n").unwrap();
    let with_umbrella_mods = scan_lean_tree(&theory_root, "Anneal").unwrap();
    assert!(with_umbrella_mods.contains_key("Anneal"));

    fs::write(theory_root.join("other.json"), b"{}\n").unwrap();
    let err = scan_lean_tree(&theory_root, "Anneal").unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert_eq!(err.phase, "snapshot", "{err}");
    assert!(err.message.contains("unexpected non-Lean file in source tree: other.json"), "{err}");

    let trusted_root = tmp.path().join("trusted_lean");
    fs::create_dir_all(&trusted_root).unwrap();
    fs::write(trusted_root.join("Trusted.lean"), HEADER).unwrap();
    fs::write(trusted_root.join("bundle-manifest.json"), b"{}\n").unwrap();
    let err = scan_lean_tree(&trusted_root, "Trusted").unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert_eq!(err.phase, "snapshot", "{err}");
    assert!(
        err.message.contains("unexpected non-Lean file in source tree: bundle-manifest.json"),
        "{err}"
    );

    let no_trusted_umbrella = tmp.path().join("trusted_lean_no_umbrella");
    fs::create_dir_all(no_trusted_umbrella.join("Trusted")).unwrap();
    fs::write(no_trusted_umbrella.join("Trusted/MirAst.lean"), HEADER).unwrap();
    let err = scan_lean_tree(&no_trusted_umbrella, "Trusted").unwrap_err();
    assert_eq!(err.code, 1, "{err}");
    assert_eq!(err.phase, "snapshot", "{err}");
    assert!(err.message.contains("missing Trusted.lean umbrella"), "{err}");

    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();
    for rel in anneal_audit::bundle::TRUSTED_BUNDLE_SOURCES
        .iter()
        .copied()
        .chain(anneal_audit::bundle::PROVENANCE_SOURCES.iter().copied())
    {
        let dst = fix.root.join(rel);
        fs::create_dir_all(dst.parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), dst).unwrap();
    }
    fs::create_dir_all(fix.root.join("theory")).unwrap();

    let mut checker = fix.checker();
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "bundle-manifest", "unexpected phase: {err}");
    assert!(
        err.message.contains("missing canonical bundle source: theory/bundle-manifest.json"),
        "unexpected error: {err}"
    );
    assert!(!checker.execution_began());

    fs::write(
        fix.root.join(anneal_audit::bundle::LEGACY_THEORY_BUNDLE_DESTINATION),
        b"{}\n",
    )
    .unwrap();
    let mut checker_legacy = Checker::new(&fix.root, None).unwrap();
    let err_legacy = checker_legacy.run().unwrap_err();
    assert_eq!(err_legacy.code, 1, "unexpected code: {err_legacy}");
    assert_eq!(err_legacy.phase, "bundle-manifest", "unexpected phase: {err_legacy}");
    assert!(
        err_legacy.message.contains("legacy checked-in bundled_theory.json must be absent"),
        "unexpected error: {err_legacy}"
    );
    assert!(!checker_legacy.execution_began());
}

/// Verifies multi-module parallel DAG compilation in
/// [`Checker::verify_and_stage_miri_entries`]:
/// 1. A 4-module diamond DAG (`Miri.DagRoot -> {Miri.DagLeft, Miri.DagRight}
///    -> Miri.DagTop`) compiles cold across workers, verifies digests, stages
///    into `miri-lib`, populates `miri_cache_dir`, and preserves transitive
///    ordering when an intermediate module (`Miri.DagLeft`/`Miri.DagRight`)
///    hits the cache while `Miri.DagRoot` and `Miri.DagTop` miss.
/// 2. When multiple modules fail concurrently (a dependent module at index 1
///    and an independent root at index 2), the earliest closure index's failure
///    is reported deterministically and dependent indices (`Miri.DagTop`) are
///    neither staged nor cached.
/// 3. Cyclic `Miri.*` imports (including cycles traversing a cached module) and
///    duplicate closure modules fail closed with policy exit code `1` before
///    compiling.
#[cfg(target_os = "linux")]
#[test]
fn compiles_cold_miri_closure_dag_in_parallel_and_preserves_failure_order() {
    let fix = TempFixture::new(None);
    let vendor_dir = fix.root.join("dag-vendor");
    fs::create_dir_all(vendor_dir.join("Miri")).unwrap();

    let dag_sources_raw = [
        (
            "Miri.DagRoot",
            "Miri/DagRoot.lean",
            "prelude\nimport Init.Prelude\nnamespace Miri.DagRoot\ndef r : Nat := 1\nend Miri.DagRoot\n",
        ),
        (
            "Miri.DagLeft",
            "Miri/DagLeft.lean",
            "prelude\nimport Miri.DagRoot\nnamespace Miri.DagLeft\ndef l : Nat := Miri.DagRoot.r\nend Miri.DagLeft\n",
        ),
        (
            "Miri.DagRight",
            "Miri/DagRight.lean",
            "prelude\nimport Miri.DagRoot\nnamespace Miri.DagRight\ndef rg : Nat := Miri.DagRoot.r\nend Miri.DagRight\n",
        ),
        (
            "Miri.DagTop",
            "Miri/DagTop.lean",
            "prelude\nimport Miri.DagLeft\nimport Miri.DagRight\nnamespace Miri.DagTop\ndef t : Nat := Miri.DagLeft.l\nend Miri.DagTop\n",
        ),
    ];

    let mut expected_sources = BTreeMap::new();
    for (_, rel, src) in &dag_sources_raw {
        fs::write(vendor_dir.join(rel), src).unwrap();
        expected_sources.insert((*rel).to_string(), sha256_bytes(src.as_bytes()));
    }

    let mut probe = fix.checker();
    probe.set_require_mir_wp(false);
    probe.run().unwrap();
    let probe_lib = probe.stage().join("dag-probe-lib");
    fs::create_dir_all(probe_lib.join("Miri")).unwrap();
    let mut entries = Vec::new();
    for (module, rel, _) in &dag_sources_raw {
        let out_olean = probe_lib.join(format!("{}.olean", module.replace('.', "/")));
        probe
            .process_with_path(
                &format!("probe-{module}"),
                &[
                    "-j1".to_string(),
                    "-M2048".to_string(),
                    "-t0".to_string(),
                    "-DElab.async=false".to_string(),
                    "-Ddebug.skipKernelTC=false".to_string(),
                    "-R".to_string(),
                    vendor_dir.to_string_lossy().into_owned(),
                    "-o".to_string(),
                    out_olean.to_string_lossy().into_owned(),
                    vendor_dir.join(rel).to_string_lossy().into_owned(),
                ],
                Some(probe_lib.as_os_str()),
            )
            .unwrap();
        entries.push(MiriClosureEntry {
            module: (*module).to_string(),
            path: (*rel).to_string(),
            olean_sha256: sha256_file(&out_olean, "test").unwrap(),
            olean_server_sha256: None,
            olean_private_sha256: None,
        });
    }

    // 1. Cold parallel DAG compilation succeeds and populates the cache.
    let cache_tmp = tempfile::Builder::new().prefix("anneal-dag-cache-").tempdir().unwrap();
    let cache_dir = cache_tmp.path().join("miri-cache");
    let mut c1 = fix.checker();
    c1.set_require_mir_wp(false);
    c1.set_miri_cache_dir(Some(cache_dir.clone()));
    c1.run().unwrap();
    let miri_lib =
        c1.verify_and_stage_miri_entries(&vendor_dir, &entries, &expected_sources).unwrap();
    for entry in &entries {
        let rel_olean = format!("{}.olean", entry.module.replace('.', "/"));
        assert_eq!(sha256_file(&miri_lib.join(&rel_olean), "test").unwrap(), entry.olean_sha256);
        assert_eq!(sha256_file(&cache_dir.join(&rel_olean), "test").unwrap(), entry.olean_sha256);
    }

    // 1b. Partial cache hit where intermediate modules (`Miri.DagLeft` and
    // `Miri.DagRight`) hit `cache_dir` while `Miri.DagRoot` and `Miri.DagTop`
    // (which does NOT directly import `Miri.DagRoot`) miss: `Miri.DagTop` must
    // still wait for `Miri.DagRoot` to compile and stage into `miri-lib`.
    fs::remove_file(cache_dir.join("Miri/DagRoot.olean")).unwrap();
    fs::remove_file(cache_dir.join("Miri/DagTop.olean")).unwrap();
    let mut c1_partial = fix.checker();
    c1_partial.set_require_mir_wp(false);
    c1_partial.set_miri_cache_dir(Some(cache_dir.clone()));
    c1_partial.run().unwrap();
    let partial_lib =
        c1_partial.verify_and_stage_miri_entries(&vendor_dir, &entries, &expected_sources).unwrap();
    for entry in &entries {
        let rel_olean = format!("{}.olean", entry.module.replace('.', "/"));
        assert_eq!(sha256_file(&partial_lib.join(&rel_olean), "test").unwrap(), entry.olean_sha256);
        assert_eq!(sha256_file(&cache_dir.join(&rel_olean), "test").unwrap(), entry.olean_sha256);
    }

    // 2. Concurrent multi-failure preserves deterministic earliest-index order:
    // index 1 (`Miri.DagLeft`, blocked behind `Miri.DagRoot`) and index 2 (an
    // independent root with a bad digest that finishes immediately) both fail;
    // index 1's failure must win and index 3 (`Miri.DagTop`) must not stage.
    let mut race_entries = vec![
        entries[0].clone(),
        MiriClosureEntry { olean_sha256: "0".repeat(64), ..entries[1].clone() },
        MiriClosureEntry { olean_sha256: "f".repeat(64), ..entries[2].clone() },
        entries[3].clone(),
    ];
    let ind_src = "prelude\nimport Init.Prelude\nnamespace Miri.DagRight\ndef rg : Nat := 1\nend Miri.DagRight\n";
    let race_vendor = fix.root.join("dag-race-vendor");
    copy_dir_all(&vendor_dir, &race_vendor).unwrap();
    fs::write(race_vendor.join("Miri/DagRight.lean"), ind_src).unwrap();
    let mut race_sources = expected_sources.clone();
    race_sources.insert("Miri/DagRight.lean".to_string(), sha256_bytes(ind_src.as_bytes()));
    let race_cache = cache_tmp.path().join("race-cache");
    let mut c2 = fix.checker();
    c2.set_require_mir_wp(false);
    c2.set_miri_cache_dir(Some(race_cache.clone()));
    c2.run().unwrap();
    let err_race =
        c2.verify_and_stage_miri_entries(&race_vendor, &race_entries, &race_sources).unwrap_err();
    assert_eq!(err_race.code, 1, "expected policy mismatch: {err_race}");
    assert!(
        err_race.message.contains("compiled Miri .olean SHA-256 mismatch for Miri.DagLeft"),
        "expected earliest index failure (Miri.DagLeft), got: {err_race}"
    );
    assert!(!race_cache.join("Miri/DagTop.olean").exists());

    // 2b. Non-topological `entries` slice (`Miri.DagLeft` at index 0 depending
    // on valid `Miri.DagRoot` at index 2, with independent failing root
    // `Miri.DagRight` at index 1): `min_cold_descendant` ensures `Miri.DagRoot`
    // is never pruned as "beaten" by index 1, so index 0's failure still wins.
    let non_topo_entries = [
        MiriClosureEntry { olean_sha256: "0".repeat(64), ..entries[1].clone() },
        MiriClosureEntry { olean_sha256: "f".repeat(64), ..entries[2].clone() },
        entries[0].clone(),
    ];
    let mut c2_nontopo = fix.checker();
    c2_nontopo.set_require_mir_wp(false);
    c2_nontopo.run().unwrap();
    let err_nontopo = c2_nontopo
        .verify_and_stage_miri_entries(&race_vendor, &non_topo_entries, &race_sources)
        .unwrap_err();
    assert_eq!(err_nontopo.code, 1, "expected policy mismatch: {err_nontopo}");
    assert!(
        err_nontopo.message.contains("compiled Miri .olean SHA-256 mismatch for Miri.DagLeft"),
        "expected index 0 failure (Miri.DagLeft) on non-topological slice, got: {err_nontopo}"
    );

    // Duplicate module entries fail closed with policy exit code `1`.
    race_entries[2] = race_entries[0].clone();
    let mut c_dup = fix.checker();
    c_dup.set_require_mir_wp(false);
    c_dup.run().unwrap();
    let err_dup = c_dup
        .verify_and_stage_miri_entries(&race_vendor, &race_entries, &race_sources)
        .unwrap_err();
    assert_eq!(err_dup.code, 1);
    assert!(err_dup.message.contains("duplicate Miri closure module Miri.DagRoot"));

    // 3. Cold `Miri.*` import cycles fail closed with policy exit code `1`.
    let cyc_vendor = fix.root.join("dag-cycle-vendor");
    fs::create_dir_all(cyc_vendor.join("Miri")).unwrap();
    let cyc_a = "prelude\nimport Miri.CycB\n";
    let cyc_b = "prelude\nimport Miri.CycA\n";
    fs::write(cyc_vendor.join("Miri/CycA.lean"), cyc_a).unwrap();
    fs::write(cyc_vendor.join("Miri/CycB.lean"), cyc_b).unwrap();
    let cyc_sources = BTreeMap::from([
        ("Miri/CycA.lean".to_string(), sha256_bytes(cyc_a.as_bytes())),
        ("Miri/CycB.lean".to_string(), sha256_bytes(cyc_b.as_bytes())),
    ]);
    let cyc_entries = [
        MiriClosureEntry {
            module: "Miri.CycA".to_string(),
            path: "Miri/CycA.lean".to_string(),
            olean_sha256: "0".repeat(64),
            olean_server_sha256: None,
            olean_private_sha256: None,
        },
        MiriClosureEntry {
            module: "Miri.CycB".to_string(),
            path: "Miri/CycB.lean".to_string(),
            olean_sha256: "0".repeat(64),
            olean_server_sha256: None,
            olean_private_sha256: None,
        },
    ];
    let mut c3 = fix.checker();
    c3.set_require_mir_wp(false);
    c3.run().unwrap();
    let err_cyc =
        c3.verify_and_stage_miri_entries(&cyc_vendor, &cyc_entries, &cyc_sources).unwrap_err();
    assert_eq!(err_cyc.code, 1, "expected policy cycle rejection: {err_cyc}");
    assert!(
        err_cyc.message.contains("import cycle in Miri closure modules"),
        "unexpected cycle error: {err_cyc}"
    );

    // 3b. Import cycle traversing cached intermediate modules even when only a
    // single module (`Miri.DagRoot`, rewritten to import `Miri.DagTop`) misses
    // `cache_dir` (`cold_indices.len() == 1`) fails closed with policy exit
    // code `1` before compiling.
    let cyc_cached_vendor = fix.root.join("dag-cycle-cached-vendor");
    copy_dir_all(&vendor_dir, &cyc_cached_vendor).unwrap();
    let cyc_root_src = "prelude\nimport Miri.DagTop\n";
    fs::write(cyc_cached_vendor.join("Miri/DagRoot.lean"), cyc_root_src).unwrap();
    let mut cyc_cached_sources = expected_sources.clone();
    cyc_cached_sources
        .insert("Miri/DagRoot.lean".to_string(), sha256_bytes(cyc_root_src.as_bytes()));
    fs::remove_file(cache_dir.join("Miri/DagRoot.olean")).unwrap();
    let mut c3_cached = fix.checker();
    c3_cached.set_require_mir_wp(false);
    c3_cached.set_miri_cache_dir(Some(cache_dir));
    c3_cached.run().unwrap();
    let err_cyc_cached = c3_cached
        .verify_and_stage_miri_entries(&cyc_cached_vendor, &entries, &cyc_cached_sources)
        .unwrap_err();
    assert_eq!(err_cyc_cached.code, 1, "expected policy cycle rejection: {err_cyc_cached}");
    assert!(
        err_cyc_cached.message.contains("import cycle in Miri closure modules"),
        "unexpected 1-cold cached-node cycle error: {err_cyc_cached}"
    );
}

/// Verifies Pass 1 parallel DAG compilation on a multi-branch `theory/`
/// diamond (`Anneal.Root` -> `{Anneal.Left, Anneal.Right}` -> `Anneal`) and
/// confirms deterministic earliest-order failure reporting when concurrent
/// sibling modules both fail compilation.
#[test]
fn compiles_pass1_diamond_dag_in_parallel_and_preserves_failure_order() {
    let fix = TempFixture::new(None);
    let theory_dir = fix.root.join("theory/Anneal");
    fs::create_dir_all(&theory_dir).unwrap();
    fs::write(
        theory_dir.join("Root.lean"),
        "prelude\nimport Init.Core\nimport Trusted\nnamespace Anneal.Root\ndef base : Nat := 1\nend Anneal.Root\n",
    )
    .unwrap();
    fs::write(
        theory_dir.join("Left.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Root\nnamespace Anneal.Left\ndef l : Nat := Anneal.Root.base\nend Anneal.Left\n",
    )
    .unwrap();
    fs::write(
        theory_dir.join("Right.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Root\nnamespace Anneal.Right\ndef r : Nat := Anneal.Root.base\nend Anneal.Right\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Left\nimport Anneal.Right\nnamespace Anneal\ndef top : Nat := Anneal.Left.l\nend Anneal\n",
    )
    .unwrap();

    let mut ok_checker = fix.checker();
    ok_checker.set_require_mir_wp(false);
    let report = ok_checker.run().unwrap();
    assert_eq!(report.get("replay"), Some(&json!(true)));

    // Both sibling leaves fail typechecking; `Anneal.Left` precedes
    // `Anneal.Right` in sorted topological order so its failure must win.
    fs::write(
        theory_dir.join("Left.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Root\nnamespace Anneal.Left\ndef l : Nat := true\nend Anneal.Left\n",
    )
    .unwrap();
    fs::write(
        theory_dir.join("Right.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Root\nnamespace Anneal.Right\ndef r : Nat := false\nend Anneal.Right\n",
    )
    .unwrap();
    let mut err_checker = fix.checker();
    err_checker.set_require_mir_wp(false);
    let err = err_checker.run().unwrap_err();
    assert_eq!(err.code, 2, "expected compile failure: {err}");
    assert_eq!(err.phase, "compile-Anneal.Left", "expected earliest sibling failure, got: {err}");
}

/// Verifies that Pass 2 `"correspondence-audit"` fails closed when a compiled
/// correspondence module imports a Pass 1 `theory/` module omitted from
/// `CorrespondenceAudit.theory` (the transitive import closure of
/// `correspondence/`).
#[test]
fn rejects_unadmitted_pass1_theory_import_in_correspondence_audit() {
    let fix = TempFixture::new(None);
    fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal/Unimported.lean"),
        "prelude\nimport Init.Core\nnamespace Anneal.Unimported\ndef hidden : Nat := 7\nend Anneal.Unimported\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Unimported\n",
    )
    .unwrap();

    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let src = stage.join("src/forged-unimported");
    let theory_lib = stage.join("theory-lib");
    compile_forged_module(
        &mut checker,
        &src,
        &theory_lib,
        &["Anneal.Unimported"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Init.Core\nimport Anneal.Unimported\nnamespace Anneal.MirCorrespondenceProof\ndef leak : Nat := Anneal.Unimported.hidden\nend Anneal.MirCorrespondenceProof\n",
    );

    let err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![stage.join("lib"), theory_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err.code, 1, "expected policy rejection: {err}");
    assert_eq!(err.phase, "correspondence-audit", "unexpected phase: {err}");
    assert!(
        err.message.contains("foreign module Anneal.Unimported in correspondence environment"),
        "unexpected error: {err}"
    );
}

/// Verifies that [`Checker::run_correspondence_with_closure`] rejects Pass 2
/// modules whose names collide with Pass 1 `theory/` or `trusted/lean/`
/// modules (`code == 1`, `phase == "snapshot"`) before Pass 2 preflight or
/// compilation can touch `<stage>/lib` or `<stage>/theory-lib`.
#[test]
fn rejects_overlapping_pass1_and_pass2_module_names() {
    // Case 1: Pass 1 `theory/Anneal/MirCorrespondenceProof.lean` collides with
    // Pass 2 `correspondence/Anneal/MirCorrespondenceProof.lean`.
    {
        let fix = TempFixture::new(None);
        fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
        fs::write(
            fix.root.join("theory/Anneal/MirCorrespondenceProof.lean"),
            "prelude\nimport Init.Core\nnamespace Anneal.MirCorrespondenceProof\ndef decoy : Nat := 1\nend Anneal.MirCorrespondenceProof\n",
        )
        .unwrap();
        fs::write(
            fix.root.join("theory/Anneal.lean"),
            "prelude\nimport Init.Core\nimport Anneal.MirCorrespondenceProof\n",
        )
        .unwrap();

        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        checker.run().unwrap();
        let pass1_olean = checker.stage().join("theory-lib/Anneal/MirCorrespondenceProof.olean");
        let pass1_sha = sha256_file(&pass1_olean, "test").unwrap();

        let vendor_dir = fix.root.join("synthetic-miri");
        fs::create_dir_all(&vendor_dir).unwrap();
        let corr_trusted = fix.root.join("trusted/correspondence/Trusted/Correspondence.lean");
        let corr_proof = fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean");
        fs::create_dir_all(corr_trusted.parent().unwrap()).unwrap();
        fs::create_dir_all(corr_proof.parent().unwrap()).unwrap();
        fs::write(
            &corr_trusted,
            "-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.Core\nnamespace Trusted.Correspondence\ndef ok : Nat := 0\nend Trusted.Correspondence\n",
        )
        .unwrap();
        fs::write(
            &corr_proof,
            "prelude\nimport Init.Core\nimport Trusted.Correspondence\nnamespace Anneal.MirCorrespondenceProof\ndef real : Nat := Trusted.Correspondence.ok\nend Anneal.MirCorrespondenceProof\n",
        )
        .unwrap();

        let base_tiers = BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]);
        let err = checker
            .run_correspondence_with_closure(
                &base_tiers,
                &vendor_dir,
                "synthetic-commit",
                &[],
                &BTreeMap::new(),
            )
            .unwrap_err();
        assert_eq!(err.code, 1, "expected policy exit 1: {err}");
        assert_eq!(err.phase, "snapshot", "expected snapshot rejection: {err}");
        assert!(
            err.message.contains("overlapping module role for Anneal.MirCorrespondenceProof"),
            "unexpected error: {err}"
        );
        assert_eq!(
            sha256_file(&pass1_olean, "test").unwrap(),
            pass1_sha,
            "Pass 1 theory .olean must not be overwritten on collision"
        );
        assert!(
            !checker.stage().join("lib/Trusted/Correspondence.olean").exists(),
            "Pass 2 Trusted.Correspondence must not compile on collision"
        );
    }

    // Case 2: Pass 1 `trusted/lean/Trusted/Correspondence.lean` collides with
    // Pass 2 `trusted/correspondence/Trusted/Correspondence.lean`.
    {
        let fix = TempFixture::new(None);
        fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
        fs::write(
            fix.root.join("trusted/lean/Trusted/Correspondence.lean"),
            "-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.Core\nnamespace Trusted.Correspondence\ndef decoy : Nat := 2\nend Trusted.Correspondence\n",
        )
        .unwrap();
        fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
        fs::write(
            fix.root.join("theory/Anneal.lean"),
            "prelude\nimport Init.Core\nimport Trusted.Correspondence\ndef reach : Nat := Trusted.Correspondence.decoy\n",
        )
        .unwrap();

        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        checker.run().unwrap();
        let pass1_olean = checker.stage().join("lib/Trusted/Correspondence.olean");
        let pass1_sha = sha256_file(&pass1_olean, "test").unwrap();

        let vendor_dir = fix.root.join("synthetic-miri");
        fs::create_dir_all(&vendor_dir).unwrap();
        let corr_trusted = fix.root.join("trusted/correspondence/Trusted/Correspondence.lean");
        let corr_proof = fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean");
        fs::create_dir_all(corr_trusted.parent().unwrap()).unwrap();
        fs::create_dir_all(corr_proof.parent().unwrap()).unwrap();
        fs::write(
            &corr_trusted,
            "-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.Core\nnamespace Trusted.Correspondence\ndef real : Nat := 0\nend Trusted.Correspondence\n",
        )
        .unwrap();
        fs::write(
            &corr_proof,
            "prelude\nimport Init.Core\nimport Trusted.Correspondence\nnamespace Anneal.MirCorrespondenceProof\ndef ok : Nat := Trusted.Correspondence.real\nend Anneal.MirCorrespondenceProof\n",
        )
        .unwrap();

        let base_tiers = BTreeMap::from([
            ("Trusted".to_string(), TrustTier::Vetted),
            (
                "Trusted.Correspondence".to_string(),
                TrustTier::parse("candidate:mir_semantics").unwrap(),
            ),
        ]);
        let err = checker
            .run_correspondence_with_closure(
                &base_tiers,
                &vendor_dir,
                "synthetic-commit",
                &[],
                &BTreeMap::new(),
            )
            .unwrap_err();
        assert_eq!(err.code, 1, "expected policy exit 1: {err}");
        assert_eq!(err.phase, "snapshot", "expected snapshot rejection: {err}");
        assert!(
            err.message.contains("overlapping module role for Trusted.Correspondence"),
            "unexpected error: {err}"
        );
        assert_eq!(
            sha256_file(&pass1_olean, "test").unwrap(),
            pass1_sha,
            "Pass 1 trusted .olean must not be overwritten on collision"
        );
    }
}

/// Pass 1 `"preflight"` and `"audit"` admit Lean 4 `module`-system `Trusted`
/// and `theory/` files (`public import`, `@[expose] public section`,
/// `public section` + `@[expose] def`, private `import`, and narrowly scoped
/// `import all Init.Data.Nat.Bitwise.Basic` in `theory/`), thread `isModule`
/// into `lean --setup`, and fail closed when a `theory/` module attempts
/// `import all` on any non-allowlisted foundation module.
#[test]
fn admits_module_system_pass1_and_restricts_import_all() {
    // Positive case: `Trusted` and `Anneal` both use Lean 4 `module` syntax,
    // including `import all Init.Data.Nat.Bitwise.Basic` in `Anneal`.
    {
        let fix = TempFixture::new(Some(
            "-- anneal-trust-tier: vetted\n\
             module\n\
             prelude\n\
             public import Init.Core\n\
             @[expose] public section\n\
             namespace Trusted\n\
             def seed : Nat := 7\n\
             end Trusted\n\
             end\n",
        ));
        fs::create_dir_all(fix.root.join("theory")).unwrap();
        fs::write(
            fix.root.join("theory/Anneal.lean"),
            "module\n\
             prelude\n\
             public import Init.Core\n\
             public import Init.Data.Nat.Bitwise.Basic\n\
             public import Trusted\n\
             import all Init.Data.Nat.Bitwise.Basic\n\
             public section\n\
             namespace Anneal\n\
             @[expose] def bump : Nat := Trusted.seed\n\
             theorem land_bridge (n m : Nat) : Nat.land n m = Nat.bitwise and n m := by rfl\n\
             end Anneal\n\
             end\n",
        )
        .unwrap();

        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        let report = checker.run().unwrap();
        assert_eq!(report["replay"], json!(true), "unexpected report: {report}");
        assert!(
            checker.stage().join("lib/Trusted.olean.private").exists(),
            "module-compiled Trusted must emit .olean.private"
        );
        assert!(
            checker.stage().join("theory-lib/Anneal.olean.private").exists(),
            "module-compiled Anneal must emit .olean.private"
        );
    }

    // Negative case: `theory/` cannot `import all` outside the narrow
    // `allowedTheoryImportAllModules` allowlist.
    {
        let fix = TempFixture::new(Some(
            "-- anneal-trust-tier: vetted\n\
             module\n\
             prelude\n\
             public import Init.Core\n\
             @[expose] public section\n\
             namespace Trusted\n\
             def seed : Nat := 7\n\
             end Trusted\n\
             end\n",
        ));
        fs::create_dir_all(fix.root.join("theory")).unwrap();
        fs::write(
            fix.root.join("theory/Anneal.lean"),
            "module\n\
             prelude\n\
             public import Init.Core\n\
             import all Init.Core\n\
             public section\n\
             theorem ok : True := True.intro\n\
             end\n",
        )
        .unwrap();

        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        let err = checker.run().unwrap_err();
        assert_eq!(err.code, 1, "expected policy exit 1: {err}");
        assert_eq!(err.phase, "preflight", "expected preflight rejection: {err}");
        assert!(
            err.message.contains("import modifiers are unsupported"),
            "unexpected error: {err}"
        );
    }
}

/// Negative and compatibility regressions at the `cargo_anneal::Checker`
/// boundary for prebuilt `.olean` `manifest.json` admission: malformed JSON,
/// unknown fields on `schema_version: 1`, and `schema_version: 2` entries
/// omitting `transitive_sha256` must all fail closed with exit code `2`
/// (`olean-cache`), whereas well-formed `schema_version: 1` manifests skip
/// cleanly by default and fail closed (`code = 2`) under
/// `--no-rebuild-bundled`.
#[test]
fn prebuilt_olean_manifest_admission_rejects_malformed_and_missing_transitive_sha256() {
    use std::os::unix::fs::PermissionsExt;

    let dir = tempfile::tempdir().unwrap();
    let base = fs::canonicalize(dir.path()).unwrap();
    let root = base.join("bundle");
    let prefix = base.join("sysroot");
    let prebuilt = base.join("prebuilt");
    let cache_home = base.join("xdg-cache");
    fs::create_dir_all(prefix.join("lib/lean/Init")).unwrap();
    fs::create_dir_all(&prebuilt).unwrap();
    fs::create_dir_all(&cache_home).unwrap();

    let inspector_src = root.join("trusted/audit/TrustedBoundary.lean");
    fs::create_dir_all(inspector_src.parent().unwrap()).unwrap();
    fs::write(&inspector_src, "-- synthetic inspector\n").unwrap();

    let lean = base.join("lean");
    fs::write(
        &lean,
        format!(
            r#"#!/bin/sh
case "$1" in
    --version) printf 'Lean 4.34.1\n'; exit ;;
    --print-prefix) printf '%s\n' '{}'; exit ;;
esac
out=""
while [ "$#" -gt 0 ]; do
    case "$1" in
        -o) out="$2"; shift 2 ;;
        *) shift ;;
    esac
done
if [ -n "$out" ]; then
    printf 'olean\0024.34.1\000synthetic' > "$out"
    exit 0
fi
exit 1
"#,
            prefix.display()
        ),
    )
    .unwrap();
    fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();

    let mod_src = base.join("MirAst.lean");
    fs::write(&mod_src, "prelude\n").unwrap();
    let order = vec!["Trusted.MirAst".to_owned()];
    let sources = BTreeMap::from([("Trusted.MirAst".to_owned(), mod_src)]);
    let imports = BTreeMap::from([("Trusted.MirAst".to_owned(), Vec::new())]);
    let is_module = BTreeMap::from([("Trusted.MirAst".to_owned(), false)]);

    let env_vars = [
        ("HOME".to_owned(), base.to_string_lossy().into_owned()),
        ("XDG_CACHE_HOME".to_owned(), cache_home.to_string_lossy().into_owned()),
    ];

    // 1. Malformed JSON, unknown top-level fields on `schema_version: 1`, and
    //    `schema_version: 2` entries omitting `transitive_sha256` must all fail
    //    closed with exit code `2` in phase `olean-cache`.
    for (case, bad_manifest) in [
        ("malformed-json", br#"{not json"#.as_slice()),
        ("v1-unknown-field", br#"{"schema_version":1,"entries":[],"bogus":1}"#.as_slice()),
        (
            "v2-missing-transitive-sha",
            br#"{"schema_version":2,"entries":[{"kind":"module","module":"M","lean_sha256":"a","sysroot_manifest_sha256":"b","source_sha256":"c","is_module":false,"flags":[],"imports":[{"module":"I","is_exported":true,"import_all":false,"is_meta":false,"part_sha256s":[]}],"parts":[]}]}"#.as_slice(),
        ),
    ] {
        fs::write(prebuilt.join("manifest.json"), bad_manifest).unwrap();
        let mut checker =
            cargo_anneal::Checker::new_with_env(&root, Some(&lean), env_vars.clone()).unwrap();
        checker.set_allow_unpinned_lean(true);
        checker.set_sandbox_mode(cargo_anneal::SandboxMode::Unsandboxed);
        checker.set_prebuilt_olean_dir(Some(prebuilt.clone()));
        checker.tool_admission().unwrap();
        let err = checker
            .compile_lean_modules_parallel(
                &order, &sources, &imports, &is_module, "lib", false, false, 1,
            )
            .unwrap_err();
        assert_eq!(err.code, 2, "{case}: expected exit code 2, got {err}");
        assert_eq!(err.phase, "olean-cache", "{case}: {err}");
        assert!(err.message.contains("invalid prebuilt olean manifest"), "{case}: {err}");
    }

    // 2. Well-formed `schema_version: 1` prebuilt manifest skips cleanly by
    //    default (falls back to compiling `Trusted.MirAst`) and fails closed
    //    with exit code `2` when `--no-rebuild-bundled` is active against an
    //    empty disk cache.
    let valid_v1 = json!({
        "schema_version": 1,
        "entries": [{
            "kind": "module",
            "module": "Trusted.MirAst",
            "lean_sha256": "a".repeat(64),
            "sysroot_manifest_sha256": "b".repeat(64),
            "source_sha256": "c".repeat(64),
            "is_module": false,
            "flags": [],
            "imports": [{
                "module": "Init.Core",
                "is_exported": true,
                "import_all": false,
                "is_meta": false,
                "part_sha256s": ["d".repeat(64)],
            }],
            "parts": [{
                "suffix": "olean",
                "path": "lib/Trusted/MirAst.olean",
                "sha256": "0".repeat(64),
            }],
        }],
    });
    fs::write(prebuilt.join("manifest.json"), serde_json::to_vec(&valid_v1).unwrap()).unwrap();

    let mut no_rebuild =
        cargo_anneal::Checker::new_with_env(&root, Some(&lean), env_vars.clone()).unwrap();
    no_rebuild.set_allow_unpinned_lean(true);
    no_rebuild.set_sandbox_mode(cargo_anneal::SandboxMode::Unsandboxed);
    no_rebuild.set_prebuilt_olean_dir(Some(prebuilt.clone()));
    no_rebuild.set_no_rebuild_bundled(true);
    no_rebuild.tool_admission().unwrap();
    let err = no_rebuild
        .compile_lean_modules_parallel(
            &order, &sources, &imports, &is_module, "lib", false, false, 1,
        )
        .unwrap_err();
    assert_eq!(err.code, 2, "{err}");
    assert_eq!(err.phase, "olean-cache", "{err}");
    assert!(err.message.contains("--no-rebuild-bundled"), "{err}");
    assert!(err.message.contains("schema_version 1 != 2"), "{err}");

    let mut default_checker =
        cargo_anneal::Checker::new_with_env(&root, Some(&lean), env_vars).unwrap();
    default_checker.set_allow_unpinned_lean(true);
    default_checker.set_sandbox_mode(cargo_anneal::SandboxMode::Unsandboxed);
    default_checker.set_prebuilt_olean_dir(Some(prebuilt));
    default_checker.tool_admission().unwrap();
    default_checker
        .compile_lean_modules_parallel(
            &order, &sources, &imports, &is_module, "lib", false, false, 1,
        )
        .unwrap();
}

/// Pass-1 `"preflight"` explicitly rejects `include_str`, `Init/Util.lean`'s
/// `lean_dbg_*` externs (`dbgSleep`, `dbgTrace`, `dbgTraceIfShared`,
/// `dbgStackTrace`), `Lean.LoadDynlib` / `loadDynlib`, `Init.System.*`, and
/// `Std.Internal.UV.*` in both `Trusted` and `theory/` modules.
#[test]
fn preflight_rejects_pure_signature_io_debug_dynlib_and_system_uv() {
    let cases = [
        (
            "include_str",
            "disallowed syntax",
            "def embedded : String := include_str \"Cargo.toml\"\n",
        ),
        ("dbgSleep", "disallowed reference", "def f : Nat := dbgSleep 0 (fun _ => 1)\n"),
        ("dbgTrace", "disallowed reference", "def f : Nat := dbgTrace \"leak\" (fun _ => 1)\n"),
        (
            "dbgTraceIfShared",
            "disallowed reference",
            "def f (x : Nat) : Nat := dbgTraceIfShared \"leak\" x\n",
        ),
        ("dbgStackTrace", "disallowed reference", "def f : Nat := dbgStackTrace (fun _ => 1)\n"),
        (
            "lean_dbg_trace",
            "disallowed reference",
            "def f : Nat := lean_dbg_trace \"leak\" (fun _ => 1)\n",
        ),
        (
            "lean_dbg_sleep",
            "disallowed reference",
            "def f : Nat := lean_dbg_sleep 0 (fun _ => 1)\n",
        ),
        ("loadDynlib", "disallowed reference", "def f : Nat → Nat := loadDynlib\n"),
        ("loadPlugin", "disallowed reference", "def f : Nat → Nat := loadPlugin\n"),
        ("lean_load_dynlib", "disallowed reference", "def f : Nat := Lean.LoadDynlib.foo\n"),
        ("init_system_ident", "disallowed reference", "def f := Init.System.FilePath.mk \".\"\n"),
        ("std_internal_uv_ident", "disallowed reference", "def f := Std.Internal.UV.Loop.mk\n"),
        (
            "open_init_system",
            "disallowed reference System.FilePath.mk",
            "open Init in\ndef f := System.FilePath.mk \".\"\n",
        ),
        (
            "open_std_internal_uv",
            "disallowed reference UV.Loop.mk",
            "open Std.Internal in\ndef f := UV.Loop.mk\n",
        ),
    ];
    for (label, expected_msg, body) in cases {
        let mut trusted_fix = TempFixture::new(Some(&format!("{HEADER}{body}")));
        let err = trusted_fix
            .check_expected(Some(1), Some("preflight"), Some(false))
            .expect_err(&format!("Trusted {label} must fail preflight"));
        assert!(err.message.contains(expected_msg), "Trusted {label}: {err}");

        let mut theory_fix = TempFixture::new(None);
        fs::create_dir_all(theory_fix.root.join("theory")).unwrap();
        fs::write(
            theory_fix.root.join("theory/Anneal.lean"),
            format!("prelude\nimport Init.NotationExtra\n{body}"),
        )
        .unwrap();
        let err = theory_fix
            .check_expected(Some(1), Some("preflight"), Some(false))
            .expect_err(&format!("Theory {label} must fail preflight"));
        assert!(err.message.contains(expected_msg), "Theory {label}: {err}");
    }

    for (label, imp) in [
        ("import_init_system_io", "import Init.System.IO\n"),
        ("import_std_internal_uv", "import Std.Internal.UV\n"),
        ("import_std_internal_uv_tcp", "import Std.Internal.UV.TCP\n"),
    ] {
        let mut theory_fix = TempFixture::new(None);
        fs::create_dir_all(theory_fix.root.join("theory")).unwrap();
        fs::write(
            theory_fix.root.join("theory/Anneal.lean"),
            format!("prelude\nimport Init.NotationExtra\n{imp}def ok : Nat := 0\n"),
        )
        .unwrap();
        let err = theory_fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
        assert!(err.message.contains("disallowed sysroot import"), "{label}: {err}");
    }
}

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

/// Ensures Pass 1 `anneal-audit` discovers, compiles, and fails closed on
/// policy violations in decoupled `*Canaries.lean` modules even when neither
/// `Anneal.lean` nor any runtime umbrella imports them.
#[test]
fn rejects_decoupled_unimported_canary_module_violations() {
    // 0. Positive control: a clean standalone unimported canary module is
    // discovered, compiled, audited, and recorded in the audit graph.
    let fix_ok = materialize_mir_wp(&MirWpFixtureSpec::valid());
    fs::create_dir_all(fix_ok.root.join("theory/Anneal/Subsys")).unwrap();
    fs::write(
        fix_ok.root.join("theory/Anneal/Subsys/Canaries.lean"),
        b"prelude\nimport Init.NotationExtra\ntheorem unimported_ok : True := True.intro\n",
    )
    .unwrap();
    let mut checker_ok = fix_ok.checker();
    let report = checker_ok.run().expect("clean decoupled canary must pass");
    assert!(
        report["graph"]
            .as_object()
            .expect("audit report graph object")
            .contains_key("Anneal.Subsys.Canaries"),
        "clean decoupled canary must appear in Pass-1 audit graph"
    );

    // 1. Standalone unimported canary with forbidden `sorry` syntax fails
    // preflight before Lean compilation.
    let fix_sorry = materialize_mir_wp(&MirWpFixtureSpec::valid());
    fs::create_dir_all(fix_sorry.root.join("theory/Anneal/Subsys")).unwrap();
    fs::write(
        fix_sorry.root.join("theory/Anneal/Subsys/Canaries.lean"),
        b"prelude\nimport Init.NotationExtra\ntheorem unimported_bad : False := by sorry\n",
    )
    .unwrap();
    let mut checker_sorry = fix_sorry.checker();
    let err_sorry = checker_sorry.run().unwrap_err();
    assert_eq!(err_sorry.code, 1, "expected policy exit 1: {err_sorry}");
    assert_eq!(err_sorry.phase, "preflight", "expected preflight rejection: {err_sorry}");
    assert!(
        !checker_sorry.execution_began(),
        "preflight must fail before compilation: {err_sorry}"
    );
    assert!(
        err_sorry.message.contains("tacticSorry"),
        "expected diagnostic to cite disallowed tacticSorry syntax: {err_sorry}"
    );

    // 2. Standalone unimported canary using `sorryAx` passes preflight and
    // fails closed during compilation (`-DwarningAsError=true`).
    let fix_sorry_ax = materialize_mir_wp(&MirWpFixtureSpec::valid());
    fs::create_dir_all(fix_sorry_ax.root.join("theory/Anneal/Subsys")).unwrap();
    fs::write(
        fix_sorry_ax.root.join("theory/Anneal/Subsys/Canaries.lean"),
        b"prelude\nimport Init.NotationExtra\n\
          theorem unimported_sorry_ax : False := sorryAx False true\n",
    )
    .unwrap();
    let mut checker_sorry_ax = fix_sorry_ax.checker();
    let err_sorry_ax = checker_sorry_ax.run().unwrap_err();
    assert_eq!(err_sorry_ax.code, 2, "expected compile exit 2: {err_sorry_ax}");
    assert_eq!(
        err_sorry_ax.phase, "compile-Anneal.Subsys.Canaries",
        "expected compilation of unimported canary: {err_sorry_ax}"
    );
    assert!(checker_sorry_ax.execution_began(), "expected compilation to run: {err_sorry_ax}");
    assert!(
        err_sorry_ax.message.contains("declaration uses `sorry`"),
        "expected Lean sorry diagnostic: {err_sorry_ax}"
    );

    // 3. Even if a standalone unimported canary `.olean` is compiled without
    // `-DwarningAsError=true`, Phase-2 `"audit"` independently rejects
    // `sorryAx`.
    let stage = checker_ok.stage().to_path_buf();
    let src = stage.join("src/decoupled-canary-audit");
    let theory_lib = stage.join("theory-lib");
    compile_forged_module(
        &mut checker_ok,
        &src,
        &theory_lib,
        &[],
        "Anneal.Subsys.Canaries",
        "prelude\nimport Init.NotationExtra\n\
         theorem unimported_sorry_ax : False := sorryAx False true\n",
    );
    let err_audit = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.MirAst".to_string(),
                "Trusted.MirSemantics".to_string(),
            ],
            theory: vec![
                "Anneal.Wp".to_string(),
                "Anneal.MirWp".to_string(),
                "Anneal.MirWp.Canaries".to_string(),
                "Anneal.Subsys.Canaries".to_string(),
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
        .unwrap_err();
    assert_eq!(err_audit.code, 1, "expected policy exit 1: {err_audit}");
    assert_eq!(err_audit.phase, "audit", "expected Phase-2 audit rejection: {err_audit}");
    assert!(
        err_audit.message.contains("sorryAx"),
        "expected diagnostic to cite disallowed axiom sorryAx: {err_audit}"
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
