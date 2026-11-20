// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Integration tests for the `trusted/audit` repository boundary gate and
//! `TrustedBoundary.lean` kernel-environment inspector.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::json;

use anneal_audit::{
    CandidateFeature, Checker, Failure, ImportEdge, InspectorRequest, Json, MiriClosureEntry,
    ModuleArtifacts, PARTS, TrustTier, check_cargo_boundary, default_lean_path,
    ensure_miri_cache_outside_checkout, sha256_bytes, sha256_file, verify_sysroot_foundation_dir,
};

const HEADER: &str = "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\n";

struct TempFixture {
    _dir: tempfile::TempDir,
    root: PathBuf,
}

impl TempFixture {
    fn new(source: Option<&str>) -> Self {
        let checkout = repo_root();
        let dir = tempfile::Builder::new()
            .prefix("anneal-boundary-test-")
            .tempdir()
            .unwrap();
        let root = dir.path().to_path_buf();
        fs::create_dir_all(root.join("trusted/audit")).unwrap();
        fs::create_dir_all(root.join("trusted/lean")).unwrap();
        fs::copy(
            checkout.join("trusted/lean/lean-toolchain"),
            root.join("trusted/lean/lean-toolchain"),
        )
        .unwrap();
        fs::copy(
            checkout.join("trusted/lean/foundation-lock.json"),
            root.join("trusted/lean/foundation-lock.json"),
        )
        .unwrap();
        fs::copy(
            checkout.join("trusted/audit/TrustedBoundary.lean"),
            root.join("trusted/audit/TrustedBoundary.lean"),
        )
        .unwrap();
        fs::write(
            root.join("trusted/lean/Trusted.lean"),
            source.unwrap_or(HEADER).as_bytes(),
        )
        .unwrap();
        Self { _dir: dir, root }
    }

    fn check_expected(
        &mut self,
        expected_code: Option<i32>,
        expected_phase: Option<&str>,
        expected_executed: Option<bool>,
    ) -> Result<Json, Failure> {
        let mut checker = Checker::new(&self.root, None).unwrap();
        checker.set_require_mir_wp(false);
        let outcome = checker.run();
        match &outcome {
            Err(err) => {
                assert_eq!(
                    Some(err.code),
                    expected_code,
                    "unexpected error code for {}: {err}",
                    err.phase
                );
                if let Some(phase) = expected_phase {
                    assert_eq!(err.phase, phase, "unexpected phase: {err}");
                }
                if let Some(exp_exec) = expected_executed {
                    assert_eq!(
                        checker.execution_began, exp_exec,
                        "unexpected execution_began for {err}"
                    );
                }
            }
            Ok(_) => {
                assert!(
                    expected_code.is_none(),
                    "expected rejection {:?}, got success",
                    expected_phase
                );
            }
        }
        outcome
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn copy_dir_all(src: &Path, dst: &Path) -> io::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        if ty.is_dir() {
            copy_dir_all(&entry.path(), &dst.join(entry.file_name()))?;
        } else {
            fs::copy(entry.path(), dst.join(entry.file_name()))?;
        }
    }
    Ok(())
}

/// Verifies that an empty `Trusted.lean` importing only locked `Init.*`
/// modules passes tool admission, preflight, compilation, and foundation
/// kernel replay with zero `Trusted` declarations and zero reached axioms.
#[test]
fn audits_empty_inventory_and_foundation_replay() {
    let mut fix = TempFixture::new(Some(HEADER));
    let rep = fix.check_expected(None, None, None).unwrap();
    assert_eq!(
        rep.get("kernelDeclarations").and_then(Json::as_i64),
        Some(0)
    );
    assert_eq!(rep.get("axioms"), Some(&json!([])));
    assert_eq!(rep.get("replay"), Some(&json!(true)));
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
    hostile_env.push((
        "LEAN_PATH".to_string(),
        stale.to_string_lossy().into_owned(),
    ));
    hostile_env.push((
        "LEAN_SYSROOT".to_string(),
        stale.to_string_lossy().into_owned(),
    ));
    let mut checker = Checker::new_with_env(&fix.root, None, hostile_env).unwrap();
    checker.set_require_mir_wp(false);
    let rep = checker.run().unwrap();

    let decls = rep.get("declarations").and_then(Json::as_array).unwrap();
    let k_decls = rep
        .get("kernelDeclarations")
        .and_then(Json::as_i64)
        .unwrap();
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
    assert_eq!(
        decl_map["Outside.sealed"]
            .get("kind")
            .and_then(Json::as_str),
        Some("opaque")
    );
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
    let expected_axioms: BTreeSet<&str> = ["Classical.choice", "Quot.sound", "propext"]
        .into_iter()
        .collect();
    assert!(inferred_deps.iter().any(|n| n.contains("instWrap")));
    assert!(coerced_deps.contains("Outside.Box.value"));
    assert!(decl_map.keys().any(|n| n.contains("instCoe")));
    assert!(
        decl_map
            .values()
            .all(|d| d.get("module").and_then(Json::as_str) == Some("Trusted"))
    );
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
        let p = prefix
            .join("lib/lean")
            .join(format!("Init/Data/PLift.{part}"));
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
    assert!(
        rep.get("graph")
            .and_then(Json::as_object)
            .unwrap()
            .contains_key(extra)
    );
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
    let eval_sentinel_src = format!(
        "{HEADER}#eval IO.FS.writeFile \"{}\" \"executed\"\n",
        sentinel.display()
    );

    let full_run_negatives: Vec<(&str, String)> = vec![
        (
            "implicit default Init",
            "-- anneal-trust-tier: vetted\nimport Init.Core\ndef x : Nat := 0\n".to_string(),
        ),
        (
            "foreign namespace spoof",
            format!("{HEADER}import Foreign\nnamespace Trusted\ndef x : Nat := 0\nend Trusted\n"),
        ),
        (
            "Std import",
            "-- anneal-trust-tier: vetted\nprelude\nimport Std\n".to_string(),
        ),
        ("evaluation sentinel", eval_sentinel_src),
    ];

    for (_label, src) in &full_run_negatives {
        let mut f = TempFixture::new(Some(src));
        let _ = f.check_expected(Some(1), Some("preflight"), Some(false));
        assert!(!sentinel.exists(), "evaluation sentinel executed!");
    }

    let inspector_negatives: Vec<(&str, String)> = vec![
        (
            "module header",
            "-- anneal-trust-tier: vetted\nmodule\nprelude\nimport Init.Core\n"
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

    let mut checker = Checker::new(&base_fix.root, None).unwrap();
    checker.tool_admission().unwrap();
    for (idx, (label, src)) in inspector_negatives.iter().enumerate() {
        let neg_path = checker.stage.join(format!("neg-{idx}.lean"));
        fs::write(&neg_path, src.as_bytes()).unwrap();
        let err = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Trusted".to_string(), neg_path)],
            })
            .expect_err(&format!("expected preflight rejection for {label}"));
        assert_eq!(err.code, 1, "unexpected code for {label}: {err}");
    }

    // Verify that `SourceRole.theory` (`Anneal`) admits allowed tactics (`by
    // rfl`) while still rejecting disallowed tactics and tactic configurations
    // (`native_decide`, `decide +native`, `decide +kernel`, `decide!`,
    // `bv_decide`, `rfl'`, `grind`, `sorry`).
    let theory_header = "prelude\nimport Init.NotationExtra\n";
    let theory_pos_path = checker.stage.join("theory-pos.lean");
    fs::write(
        &theory_pos_path,
        format!("{theory_header}theorem ok : Eq 0 0 := by rfl\n").as_bytes(),
    )
    .unwrap();
    checker
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Anneal".to_string(), theory_pos_path)],
        })
        .expect("expected theory module with `by rfl` to pass preflight");

    let theory_negatives: Vec<(&str, String)> = vec![
        (
            "theory native_decide",
            format!("{theory_header}theorem x : True := by native_decide\n"),
        ),
        (
            "theory decide +native",
            format!("{theory_header}theorem x : True := by decide +native\n"),
        ),
        (
            "theory decide +kernel",
            format!("{theory_header}theorem x : True := by decide +kernel\n"),
        ),
        (
            "theory decideBang",
            format!("{theory_header}theorem x : True := by decide!\n"),
        ),
        (
            "theory bv_decide",
            format!("{theory_header}theorem x : True := by bv_decide\n"),
        ),
        (
            "theory rfl'",
            format!("{theory_header}theorem x : True := by rfl'\n"),
        ),
        (
            "theory grind set_option",
            format!(
                "{theory_header}theorem x : True := by grind => set_option debug.skipKernelTC true\n"
            ),
        ),
        (
            "theory by sorry",
            format!("{theory_header}theorem x : False := by sorry\n"),
        ),
        (
            "theory term sorry",
            format!("{theory_header}theorem x : False := sorry\n"),
        ),
    ];
    for (idx, (label, src)) in theory_negatives.iter().enumerate() {
        let neg_path = checker.stage.join(format!("theory-neg-{idx}.lean"));
        fs::write(&neg_path, src.as_bytes()).unwrap();
        let err = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Anneal".to_string(), neg_path)],
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

    let mut f_sorry_ax = TempFixture::new(Some(&format!(
        "{HEADER}theorem bad : False := sorryAx False true\n"
    )));
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
    let err_sha = f_bad_sha
        .check_expected(Some(2), Some("foundation"), Some(false))
        .unwrap_err();
    assert!(
        err_sha
            .message
            .contains("foundation artifact SHA-256 mismatch for Init/Prelude.olean"),
        "unexpected error: {err_sha}"
    );

    let mut f_missing_root = TempFixture::new(None);
    fs::remove_file(f_missing_root.root.join("trusted/lean/Trusted.lean")).unwrap();
    fs::create_dir_all(f_missing_root.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_missing_root.root.join("trusted/lean/Trusted/Sub.lean"),
        HEADER.as_bytes(),
    )
    .unwrap();
    let err_missing_root = f_missing_root
        .check_expected(Some(1), Some("snapshot"), Some(false))
        .unwrap_err();
    assert!(
        err_missing_root
            .message
            .contains("missing Trusted.lean umbrella"),
        "unexpected error: {err_missing_root}"
    );

    let mut f_non_lean = TempFixture::new(None);
    fs::write(
        f_non_lean.root.join("trusted/lean/notes.txt"),
        b"unexpected",
    )
    .unwrap();
    let err_non_lean = f_non_lean
        .check_expected(Some(1), Some("snapshot"), Some(false))
        .unwrap_err();
    assert!(
        err_non_lean
            .message
            .contains("unexpected non-Lean file in source tree: notes.txt"),
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
    assert!(!chk_env.environment.contains_key("LD_PRELOAD"));
    assert!(!chk_env.environment.contains_key("LD_LIBRARY_PATH"));
    assert!(!chk_env.environment.contains_key("RUSTC_WRAPPER"));
    assert_eq!(
        chk_env.environment.get("HOME").map(String::as_str),
        Some("/tmp/home")
    );
    assert_eq!(
        chk_env.environment.get("PATH").map(String::as_str),
        Some("/usr/bin:/bin")
    );
}

/// Verifies defense-in-depth in Phase 2 (`"audit"`): even if a `.lean` file
/// declaring an `axiom` were compiled directly into a `.olean` (bypassing
/// `"preflight"`), `verifyAndCollectLocals` rejects the `.olean` because every
/// constant in `data.constants` is checked for `ci.isAxiom`, even when
/// unreferenced.
#[test]
fn rejects_unused_compiled_axiom() {
    let fix = TempFixture::new(None);
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.tool_admission().unwrap();
    let imports = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let setup_path = checker.write_setup_json("Trusted", &imports).unwrap();
    let unchecked = checker.stage.join("UnusedAxiom.lean");
    fs::write(
        &unchecked,
        b"prelude\nimport Init.Core\nnamespace AnyNamespace\naxiom unused : True\nend AnyNamespace\n",
    )
    .unwrap();
    let out = checker.stage.join("Trusted.olean");
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
/// outside `trusted/` and `path` dependencies from `trusted/` crates to paths
/// outside `trusted/`.
#[test]
fn rejects_cargo_workspace_members_and_path_deps_outside_trusted() {
    let checkout = repo_root();
    let mut fix = TempFixture::new(None);
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
    fs::copy(
        checkout.join("trusted/audit/Cargo.toml"),
        fix.root.join("trusted/audit/Cargo.toml"),
    )
    .unwrap();
    copy_dir_all(
        &checkout.join("trusted/rustc-capture"),
        &fix.root.join("trusted/rustc-capture"),
    )
    .unwrap();
    copy_dir_all(
        &checkout.join("trusted/cargo-anneal"),
        &fix.root.join("trusted/cargo-anneal"),
    )
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
    let err_member = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_member
            .message
            .contains("workspace member outside trusted/: crates/untrusted-helper")
    );

    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
    fs::write(
        fix.root.join("trusted/rustc-capture/Cargo.toml"),
        b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\nuntrusted-helper = { path = \"../../crates/untrusted-helper\" }\n",
    )
    .unwrap();
    let err_dep = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(err_dep.message.contains(
        "trusted/rustc-capture path dependency points outside trusted/: crates/untrusted-helper"
    ));

    fs::copy(
        checkout.join("trusted/rustc-capture/Cargo.toml"),
        fix.root.join("trusted/rustc-capture/Cargo.toml"),
    )
    .unwrap();
    fs::create_dir_all(fix.root.join(".cargo")).unwrap();
    fs::write(
        fix.root.join(".cargo/config.toml"),
        b"[build]\nrustc-wrapper = \"evil\"\n",
    )
    .unwrap();
    let err_cargo_cfg = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_cargo_cfg
            .message
            .contains("forbidden Cargo/toolchain override at repository root: .cargo")
    );
    fs::remove_dir_all(fix.root.join(".cargo")).unwrap();

    fs::write(
        fix.root.join("rust-toolchain.toml"),
        b"[toolchain]\nchannel = \"nightly\"\n",
    )
    .unwrap();
    let err_toolchain = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
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
    let err_patch = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_patch
            .message
            .contains("root Cargo.toml may contain only [workspace]"),
        "unexpected error: {err_patch}"
    );
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();

    fs::write(
        fix.root.join("Cargo.lock"),
        b"version = 4\n[[package]]\nname = \"evil\"\nversion = \"0.1.0\"\nsource = \"git+https://example.com/evil.git#deadbeef\"\n",
    )
    .unwrap();
    let err_lock = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_lock
            .message
            .contains("untrusted dependency source in Cargo.lock for evil")
    );
    fs::remove_file(fix.root.join("Cargo.lock")).unwrap();

    fs::write(
        fix.root.join("Cargo.lock"),
        b"version = 4\n[[package]]\nname = \"rogue-local\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let err_rogue_lock = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
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
    let err_manifest = fix
        .check_expected(Some(1), Some("cargo-boundary"), Some(false))
        .unwrap_err();
    assert!(
        err_manifest
            .message
            .contains("root TCB manifest digest mismatch for flake.nix"),
        "unexpected error: {err_manifest}"
    );
}

/// Verifies module-level trust-tier non-contamination and `Trusted` namespace
/// hygiene:
/// - A `vetted` module referencing a `candidate:<feature>` constant is rejected
///   during `"audit"`.
/// - A `candidate:<feature>` module referencing a `vetted` or `candidate:*`
///   constant passes during `"audit"`.
/// - A `theory/Anneal.lean` module attempting to declare a constant inside the
///   reserved `Trusted` namespace (or an `opaque` constant) is rejected during
///   `"audit"`.
#[test]
fn enforces_module_level_trust_tiers_and_namespace_hygiene() {
    // 1. A vetted module (`Trusted.lean`) referencing a candidate constant in
    // `Trusted/Cand.lean` is rejected during `"audit"`.
    let mut f_contam = TempFixture::new(Some(&format!(
        "{HEADER}import Trusted.Cand\nnamespace Trusted\ndef badVetted : Prop := candHelper\nend Trusted\n"
    )));
    fs::create_dir_all(f_contam.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_contam.root.join("trusted/lean/Trusted/Cand.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nnamespace Trusted\ndef candHelper : Prop := True\nend Trusted\n",
    )
    .unwrap();
    let err_contam = f_contam
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_contam.message.contains(
            "vetted constant Trusted.badVetted references candidate:mir_semantics constant Trusted.candHelper"
        ),
        "unexpected error: {err_contam}"
    );

    // 2. Umbrella `Trusted.lean` (`vetted`) importing `Trusted.VettedSub`
    // (`vetted`) and `Trusted.Cand` (`candidate:mir_semantics`), where
    // `Trusted.Cand` references `Trusted.VettedSub` and `theory/Anneal.lean`
    // references both, passes cleanly.
    let mut f_ok = TempFixture::new(Some(&format!(
        "{HEADER}import Trusted.VettedSub\nimport Trusted.Cand\n"
    )));
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
        b"prelude\nimport Trusted\nnamespace Anneal\ntheorem uses_both : Trusted.candProp := True.intro\nend Anneal\n",
    )
    .unwrap();
    let rep_ok = f_ok.check_expected(None, None, None).unwrap();
    assert_eq!(rep_ok.get("replay"), Some(&json!(true)));

    // 3. `theory/Anneal.lean` attempting to declare a constant inside the
    // reserved `Trusted` namespace is rejected during `"audit"`.
    fs::write(
        f_ok.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Trusted\ndef Spoof : Nat := 0\nend Trusted\n",
    )
    .unwrap();
    let err_spoof = f_ok
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
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
    let err_opaque = f_ok
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_opaque.message.contains(
            "opaque declaration Anneal.badOpaque in Anneal is not allowed outside Trusted"
        ),
        "unexpected error: {err_opaque}"
    );
}

/// Verifies that `verify_upstream_pin` and `Checker::run()` enforce
/// `vendor/lean-miri/UPSTREAM_PIN.json` and reject whole-directory deletion,
/// missing or tampered manifests (including before JSON parsing),
/// modified/deleted/unlisted `.lean` and non-`.lean` files, and symlinks with
/// policy exit code `1`.
#[test]
fn verifies_upstream_pin_and_rejects_tampering() {
    let checkout = repo_root();
    let pin = anneal_audit::verify_upstream_pin(&checkout.join("vendor/lean-miri")).unwrap();
    assert_eq!(pin.schema_version, 2);
    assert_eq!(pin.vendor_tree.file_count, 608);
    assert_eq!(pin.patched_files.len(), 10);
    assert_eq!(pin.execution_machine_closure.len(), 160);

    // 1. Deleting `vendor/` in a repository checkout fails `Checker::run()`
    // with policy exit code `1` (`miri-pin`).
    let mut fix_missing_dir = TempFixture::new(None);
    fs::copy(
        checkout.join("Cargo.toml"),
        fix_missing_dir.root.join("Cargo.toml"),
    )
    .unwrap();
    fs::copy(
        checkout.join("Cargo.lock"),
        fix_missing_dir.root.join("Cargo.lock"),
    )
    .unwrap();
    fs::copy(
        checkout.join("flake.nix"),
        fix_missing_dir.root.join("flake.nix"),
    )
    .unwrap();
    fs::copy(
        checkout.join("flake.lock"),
        fix_missing_dir.root.join("flake.lock"),
    )
    .unwrap();
    fs::copy(
        checkout.join("trusted/root-manifest.sha256"),
        fix_missing_dir.root.join("trusted/root-manifest.sha256"),
    )
    .unwrap();
    fs::copy(
        checkout.join("trusted/audit/Cargo.toml"),
        fix_missing_dir.root.join("trusted/audit/Cargo.toml"),
    )
    .unwrap();
    copy_dir_all(
        &checkout.join("trusted/rustc-capture"),
        &fix_missing_dir.root.join("trusted/rustc-capture"),
    )
    .unwrap();
    copy_dir_all(
        &checkout.join("trusted/cargo-anneal"),
        &fix_missing_dir.root.join("trusted/cargo-anneal"),
    )
    .unwrap();
    let err_no_vendor = fix_missing_dir
        .check_expected(Some(1), Some("miri-pin"), Some(false))
        .unwrap_err();
    assert!(
        err_no_vendor
            .message
            .contains("expected regular vendor directory"),
        "unexpected error: {err_no_vendor}"
    );

    // Prepare a mutable copy of `vendor/lean-miri` for tampering tests.
    let tmp = tempfile::tempdir().unwrap();
    let vendor_copy = tmp.path().join("vendor/lean-miri");
    copy_dir_all(&checkout.join("vendor/lean-miri"), &vendor_copy).unwrap();
    anneal_audit::verify_upstream_pin(&vendor_copy).unwrap();

    // 2. Modified `.lean` file digest mismatch is rejected.
    let target_lean = vendor_copy.join("Miri.lean");
    let orig_lean = fs::read(&target_lean).unwrap();
    fs::write(&target_lean, b"-- tampered\n").unwrap();
    let err_tamper = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_tamper.code, 1);
    assert!(
        err_tamper
            .message
            .contains("vendor file SHA-256 mismatch for Miri.lean"),
        "unexpected error: {err_tamper}"
    );
    fs::write(&target_lean, &orig_lean).unwrap();

    // 2b. A patched `.lean` file is verified against `patched_sha256`, never
    // exempted from on-disk digest checking.
    let patched_rel = "Miri/Interpreter/Call.lean";
    let patched_lean = vendor_copy.join(patched_rel);
    let orig_patched = fs::read(&patched_lean).unwrap();
    let expected_patched_sha = &pin
        .patched_files
        .iter()
        .find(|p| p.path == patched_rel)
        .expect("Call.lean must be listed in patched_files")
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

    // 3. Unlisted `.lean` file is rejected.
    let rogue_lean = vendor_copy.join("Miri/Rogue.lean");
    fs::write(&rogue_lean, b"def x := 1\n").unwrap();
    let err_unlisted = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_unlisted.code, 1);
    assert!(
        err_unlisted
            .message
            .contains("unlisted Lean file in vendor/lean-miri: Miri/Rogue.lean"),
        "unexpected error: {err_unlisted}"
    );
    fs::remove_file(&rogue_lean).unwrap();

    // 3b. Unlisted non-`.lean` file (e.g. a pre-compiled `.olean`) is rejected.
    let rogue_olean = vendor_copy.join("Miri/Rogue.olean");
    fs::write(&rogue_olean, b"fake-olean-bytes").unwrap();
    let err_rogue_olean = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_rogue_olean.code, 1);
    assert!(
        err_rogue_olean
            .message
            .contains("unlisted file in vendor/lean-miri: Miri/Rogue.olean"),
        "unexpected error: {err_rogue_olean}"
    );
    fs::remove_file(&rogue_olean).unwrap();

    // 3c. Deleted pinned `.lean` file is rejected.
    fs::remove_file(&target_lean).unwrap();
    let err_deleted_lean = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_deleted_lean.code, 1);
    assert!(
        err_deleted_lean
            .message
            .contains("missing pinned .lean file in vendor/lean-miri"),
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
        err_deleted_aux
            .message
            .contains("missing pinned auxiliary file in vendor/lean-miri"),
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
            err_symlink
                .message
                .contains("symlink forbidden in vendor/lean-miri"),
            "unexpected error: {err_symlink}"
        );
        fs::remove_file(&link_path).unwrap();
    }

    // 5. Modifying `UPSTREAM_PIN.json` without updating
    // `LOCKED_UPSTREAM_PIN_SHA256` is rejected before JSON parsing (both for
    // structured edits and malformed JSON).
    let pin_path = vendor_copy.join("UPSTREAM_PIN.json");
    let orig_pin_bytes = fs::read(&pin_path).unwrap();
    let mut pin_notes_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
    pin_notes_json["notes"]
        .as_array_mut()
        .unwrap()
        .push(json!("extra note"));
    fs::write(&pin_path, serde_json::to_vec(&pin_notes_json).unwrap()).unwrap();
    let err_pin_sha = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_pin_sha.code, 1);
    assert!(
        err_pin_sha
            .message
            .contains("UPSTREAM_PIN.json SHA-256 differs from locked digest"),
        "unexpected error: {err_pin_sha}"
    );

    fs::write(&pin_path, b"{not valid json").unwrap();
    let err_bad_json_sha = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_bad_json_sha.code, 1);
    assert!(
        err_bad_json_sha
            .message
            .contains("UPSTREAM_PIN.json SHA-256 differs from locked digest"),
        "unexpected error: {err_bad_json_sha}"
    );

    // 6. Missing `UPSTREAM_PIN.json` is rejected with policy exit code `1`.
    fs::remove_file(&pin_path).unwrap();
    let err_missing_pin = anneal_audit::verify_upstream_pin(&vendor_copy).unwrap_err();
    assert_eq!(err_missing_pin.code, 1);
    assert!(
        err_missing_pin
            .message
            .contains("missing UPSTREAM_PIN.json"),
        "unexpected error: {err_missing_pin}"
    );
}

/// Verifies that `"correspondence-audit"` rejects a `.vendorMiri` module that
/// declares a constant in the reserved `Trusted` or `Anneal` root namespace
/// (including a `private` declaration), declares an `axiom` or `unsafe`
/// constant, or directly references `sorryAx`, `Lean.ofReduceBool`, or
/// `Lean.trustCompiler`, while a benign vendor constant passes those checks
/// and standalone kernel replay and fails only later when the
/// `Miri.Interpreter.ExecutionMachine` cone is missing.
#[test]
fn rejects_vendor_constants_in_reserved_namespaces() {
    let fix = TempFixture::new(None);
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let trusted_lib = checker.stage.join("lib");
    let vendor_src = checker.stage.join("src/fake-miri");
    let vendor_lib = checker.stage.join("fake-miri-lib");
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
        (
            "Miri.Benign",
            "namespace Miri.Benign\ndef ok : Nat := 0\nend Miri.Benign\n",
            None,
        ),
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
            Some(message) => assert!(
                err.message.contains(message),
                "unexpected error for {module}: {err}"
            ),
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
    let cache_root = tempfile::Builder::new()
        .prefix("anneal-miri-cache-test-")
        .tempdir()
        .unwrap();
    let vendor_dir = fix.root.join("fake-vendor");
    let src_path = vendor_dir.join("Miri/Tiny.lean");
    fs::create_dir_all(src_path.parent().unwrap()).unwrap();
    let valid_src =
        "prelude\nimport Init.Core\nnamespace Miri.Tiny\ndef x : Nat := 1\nend Miri.Tiny\n";
    let valid_src_sha = sha256_bytes(valid_src.as_bytes());
    let valid_sources = BTreeMap::from([("Miri/Tiny.lean".to_string(), valid_src_sha.clone())]);
    fs::write(&src_path, valid_src).unwrap();

    // Compile once in a probe checker to obtain the deterministic `.olean`
    // companion digests for `Miri.Tiny`.
    let mut probe = Checker::new(&fix.root, None).unwrap();
    probe.set_require_mir_wp(false);
    probe.run().unwrap();
    let probe_out = probe.stage.join("probe-lib/Miri/Tiny.olean");
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
    let probe_server = probe.stage.join("probe-lib/Miri/Tiny.olean.server");
    let expected_server = probe_server
        .exists()
        .then(|| sha256_file(&probe_server, "test").unwrap());
    let probe_private = probe.stage.join("probe-lib/Miri/Tiny.olean.private");
    let expected_private = probe_private
        .exists()
        .then(|| sha256_file(&probe_private, "test").unwrap());

    let good_entry = MiriClosureEntry {
        module: "Miri.Tiny".to_string(),
        path: "Miri/Tiny.lean".to_string(),
        olean_sha256: expected_olean.clone(),
        olean_server_sha256: expected_server.clone(),
        olean_private_sha256: expected_private.clone(),
    };

    // Case 0: Staged source SHA-256 mismatch fails closed with exit code `1`.
    let wrong_sources = BTreeMap::from([("Miri/Tiny.lean".to_string(), "1".repeat(64))]);
    let mut c0 = Checker::new(&fix.root, None).unwrap();
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
        err_src_sha
            .message
            .contains("staged Miri source SHA-256 mismatch for Miri/Tiny.lean"),
        "unexpected source-mismatch error: {err_src_sha}"
    );

    // Case 1: Compiled `.olean` digest mismatch fails closed AND writes
    // nothing into the empty cache directory (write-after-verify invariant).
    let cache_mismatch = cache_root.path().join("cache-mismatch");
    fs::create_dir_all(&cache_mismatch).unwrap();
    let mut bad_entry = good_entry.clone();
    bad_entry.olean_sha256 = "0".repeat(64);
    let mut c1 = Checker::new(&fix.root, None).unwrap();
    c1.set_require_mir_wp(false);
    c1.set_miri_cache_dir(Some(cache_mismatch.clone()));
    c1.run().unwrap();
    let err = c1
        .verify_and_stage_miri_entries(&vendor_dir, &[bad_entry], &valid_sources)
        .unwrap_err();
    assert_eq!(err.code, 1, "expected policy error: {err}");
    assert!(
        err.message
            .contains("compiled Miri .olean SHA-256 mismatch for Miri.Tiny"),
        "unexpected mismatch error: {err}"
    );
    assert!(
        !cache_mismatch.join("Miri/Tiny.olean").exists(),
        "unverified .olean must never be written to cache"
    );

    // Case 2: Cold compile verifies digests and populates the cache.
    let cache_dir = cache_root.path().join("cache-live");
    fs::create_dir_all(&cache_dir).unwrap();
    let mut c2 = Checker::new(&fix.root, None).unwrap();
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
    let invalid_sources = BTreeMap::from([(
        "Miri/Tiny.lean".to_string(),
        sha256_bytes(invalid_src.as_bytes()),
    )]);
    fs::write(&src_path, invalid_src).unwrap();
    let mut c3 = Checker::new(&fix.root, None).unwrap();
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
    let mut c4a = Checker::new(&fix.root, None).unwrap();
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
    let mut c4b = Checker::new(&fix.root, None).unwrap();
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
    let mut c5 = Checker::new(&fix.root, None).unwrap();
    c5.set_require_mir_wp(false);
    c5.set_miri_cache_dir(Some(cache_sidecar.clone()));
    c5.run().unwrap();
    let err_sidecar = c5
        .verify_and_stage_miri_entries(&vendor_dir, &[bad_sidecar], &valid_sources)
        .unwrap_err();
    assert_eq!(err_sidecar.code, 1, "expected policy error: {err_sidecar}");
    assert!(
        err_sidecar
            .message
            .contains("missing compiled Miri .olean.server sidecar for Miri.Tiny"),
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
    let mod_sources = BTreeMap::from([(
        "Miri/WithSidecar.lean".to_string(),
        sha256_bytes(mod_src.as_bytes()),
    )]);
    fs::write(&mod_path, mod_src).unwrap();
    let probe_mod_out = probe.stage.join("probe-lib/Miri/WithSidecar.olean");
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
    let mod_server = probe.stage.join("probe-lib/Miri/WithSidecar.olean.server");
    let mod_private = probe.stage.join("probe-lib/Miri/WithSidecar.olean.private");
    assert!(
        mod_server.exists(),
        "Lean `module` fixture must emit .olean.server to exercise sidecar checks"
    );
    let mod_server_sha = sha256_file(&mod_server, "test").unwrap();
    let mod_private_sha = mod_private
        .exists()
        .then(|| sha256_file(&mod_private, "test").unwrap());

    // 6a. Unexpected `.olean.server` when entry expects `None`.
    let unexpected_server = MiriClosureEntry {
        module: "Miri.WithSidecar".to_string(),
        path: "Miri/WithSidecar.lean".to_string(),
        olean_sha256: mod_olean.clone(),
        olean_server_sha256: None,
        olean_private_sha256: mod_private_sha.clone(),
    };
    let mut c6a = Checker::new(&fix.root, None).unwrap();
    c6a.set_require_mir_wp(false);
    c6a.run().unwrap();
    let err_unexpected_server = c6a
        .verify_and_stage_miri_entries(&vendor_dir, &[unexpected_server], &mod_sources)
        .unwrap_err();
    assert_eq!(
        err_unexpected_server.code, 1,
        "expected policy error: {err_unexpected_server}"
    );
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
    let mut c6b = Checker::new(&fix.root, None).unwrap();
    c6b.set_require_mir_wp(false);
    c6b.run().unwrap();
    let err_mismatched_server = c6b
        .verify_and_stage_miri_entries(&vendor_dir, &[mismatched_server], &mod_sources)
        .unwrap_err();
    assert_eq!(
        err_mismatched_server.code, 1,
        "expected policy error: {err_mismatched_server}"
    );
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
        let mut c6c = Checker::new(&fix.root, None).unwrap();
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
    let outside = tempfile::Builder::new()
        .prefix("anneal-miri-outside-")
        .tempdir()
        .unwrap();

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
        let mut checker = Checker::new(&fix.root, None).unwrap();
        checker.set_miri_cache_dir(Some(bad.clone()));
        let err = checker.run().unwrap_err();
        assert_eq!(
            err.code,
            1,
            "expected policy error for {}: {err}",
            bad.display()
        );
        assert_eq!(
            err.phase,
            "miri-pin",
            "unexpected phase for {}: {err}",
            bad.display()
        );
        assert!(
            !checker.execution_began,
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
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-audit"))
        .env_clear()
        .arg("--anneal-root")
        .arg(&fix.root)
        .arg("--miri-cache-dir")
        .arg(fix.root.join(".evil-cache"))
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 from CLI: {output:?}"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Miri .olean cache directory must reside outside the repository checkout"),
        "unexpected CLI stderr: {stderr}"
    );
}

/// Verifies negative cases for correspondence-audit rules in
/// `TrustedBoundary.lean` (`classifyCorrModules`, `checkCorrTierReferences`,
/// and `closureCorr` unapproved-axiom rejection) and for toolchain sysroot
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
        err_sysroot
            .message
            .contains("sysroot Init/Std/Lean .olean manifest SHA-256 mismatch"),
        "unexpected sysroot mismatch error: {err_sysroot}"
    );
    symlink(
        fake_lib.join("Init/Dummy.olean"),
        fake_lib.join("Std/Link.olean"),
    )
    .unwrap();
    let err_sym =
        verify_sysroot_foundation_dir(&fake_lib, &BTreeSet::new(), &"0".repeat(64)).unwrap_err();
    assert!(
        err_sym.message.contains("symlink forbidden in sysroot"),
        "unexpected sysroot symlink error: {err_sym}"
    );

    // Prepare compiled synthetic modules for `TrustedBoundary.lean`
    // `"correspondence-audit"` negative cases.
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let trusted_lib = checker.stage.join("lib");
    let aux_src = checker.stage.join("src/corr-neg");
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
        "prelude\nimport Init.Core\nnamespace Trusted.CandHelper\ndef h : Nat := 1\nend Trusted.CandHelper\n",
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
        err_overlap
            .message
            .contains("overlapping module role for Trusted"),
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
        err_missing_tier
            .message
            .contains("missing trust tier for Trusted module Trusted"),
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
        err_foreign
            .message
            .contains("foreign module Miri.Child in correspondence environment"),
        "unexpected foreign-module error: {err_foreign}"
    );

    // 3a. `checkCorrTierReferences`: vetted -> candidate.
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
    assert!(
        err_vetted_cand.message.contains(
            "vetted constant Trusted.VettedRefsCand.x references candidate:mir_semantics constant"
        ),
        "unexpected vetted->cand error: {err_vetted_cand}"
    );

    // 3b. `checkCorrTierReferences`: vetted -> vendorMiri.
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
    assert!(
        err_vetted_miri.message.contains(
            "vetted constant Trusted.VettedRefsMiri.x references non-foundation constant Miri.Child.c"
        ),
        "unexpected vetted->miri error: {err_vetted_miri}"
    );

    // 3c. `checkCorrTierReferences`: candidate Trusted -> theory.
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
    assert!(
        err_cand_theory.message.contains(
            "Trusted constant Trusted.CandRefsTheory.x references Anneal.Helper.t from non-Trusted module Anneal.Helper"
        ),
        "unexpected cand->theory error: {err_cand_theory}"
    );

    // 4. `closureCorr`: reachable unapproved axiom (`propext` from `Init.Core`
    // when omitted from the axiom allowlist) rejected after passing
    // `verifyAndCollectCorrLocals` and standalone kernel replay.
    checker
        .admitted_mut()
        .unwrap()
        .axioms
        .retain(|(ax, _)| ax != "propext");
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
        err_axiom
            .message
            .contains("unapproved axiom propext from Init.Core"),
        "unexpected unapproved-axiom error: {err_axiom}"
    );
}

/// Verifies end-to-end that standalone kernel replay in Phase 3
/// (`"correspondence-audit"`) rejects an ill-typed `.vendorMiri` `.olean`
/// compiled with a scoped `set_option debug.skipKernelTC true` override (even
/// when compiled with CLI `-Ddebug.skipKernelTC=false`), and that a valid
/// minimal vendor closure passes replay and reports `miriReplay: true` with a
/// positive `miriReplayedDeclarations` count.
#[test]
fn rejects_vendor_miri_skip_kernel_tc_during_replay() {
    let fix = TempFixture::new(None);
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let trusted_lib = checker.stage.join("lib");
    let vendor_src = checker.stage.join("src/skip-tc-miri");
    let vendor_lib = checker.stage.join("skip-tc-miri-lib");

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
                "-M2048".to_string(),
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
    assert_eq!(
        err_replay.code, 1,
        "expected policy exit code 1 on replay rejection: {err_replay}"
    );
    assert_eq!(
        err_replay.phase, "correspondence-audit",
        "unexpected phase: {err_replay}"
    );
    assert!(
        err_replay
            .message
            .contains("vendor Miri kernel replay failed")
            && err_replay.message.contains("Miri.SkipKernelTC.bogus")
            && err_replay.message.contains("declaration type mismatch"),
        "expected kernel replay type-mismatch rejection, got: {err_replay}"
    );

    // 2. Verify the positive path: a valid minimal `.vendorMiri` module
    // defining the 21 `ExecutionMachine` cone roots passes standalone kernel
    // replay and returns `miriReplay: true` with `miriReplayedDeclarations`
    // positive.
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
         def withValidation : Nat := 0\n\
         def operandHooks : Nat := 0\n\
         end Miri.Interpreter.ExecutionMachine\n\
         namespace Miri.Interpreter.IntegerOps\n\
         def binary : Nat := 0\n\
         def binaryBool : Nat := 0\n\
         def unary : Nat := 0\n\
         end Miri.Interpreter.IntegerOps\n\
         namespace Miri.Memory.ScalarInt\n\
         def truncateFromUInt : Nat := 0\n\
         def tryFromUInt : Nat := 0\n\
         def tryToBool : Nat := 0\n\
         end Miri.Memory.ScalarInt\n\
         namespace Miri.Interpreter\n\
         def evalOperand : Nat := 0\n\
         def evalPlaceToOp : Nat := 0\n\
         def localToOp : Nat := 0\n\
         def placeWriteLocalImmediate : Nat := 0\n\
         def evalRvalueIntoPlace : Nat := 0\n\
         def runRvalue : Nat := 0\n\
         end Miri.Interpreter\n\
         namespace Miri.Interpreter.Step\n\
         def evalStatement : Nat := 0\n\
         end Miri.Interpreter.Step\n\
         namespace Miri.Interpreter.Frame\n\
         def storageLive : Nat := 0\n\
         def storageDead : Nat := 0\n\
         end Miri.Interpreter.Frame\n\
         namespace Miri.Interpreter.ControlFlow\n\
         def goToBlock : Nat := 0\n\
         def evalTerminator : Nat := 0\n\
         def returnFromCurrentFrame : Nat := 0\n\
         end Miri.Interpreter.ControlFlow\n",
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
    assert_eq!(
        ok_rep
            .get("miriReplayedDeclarations")
            .and_then(Json::as_u64),
        Some(21)
    );
    assert!(
        ok_rep
            .get("miriClosureReachableDeclarations")
            .and_then(Json::as_u64)
            .is_some_and(|n| n >= 21),
        "unexpected reachable declarations: {ok_rep}"
    );
    assert_eq!(ok_rep.get("miriClosureAxioms"), Some(&json!([])));
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
        "import Lean\n\
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
    let mut c1 = Checker::new(&fix.root, None).unwrap();
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
    assert!(
        !checkout_victim.exists(),
        "sandboxed run_cmd must not be able to write to checkout"
    );

    // Case 2: A malicious `run_cmd` attempting to write into the auditor's
    // read-only `/work/miri-lib` or host `stage` fails and leaves both
    // untouched.
    let mut c2 = Checker::new(&fix.root, None).unwrap();
    c2.set_require_mir_wp(false);
    c2.run().unwrap();
    let stage_victim = c2.stage.join("sandbox-escape-stage.txt");
    let ro_lib_victim = c2.stage.join("miri-lib/sandbox-escape-ro.txt");
    let escape_stage_src = format!(
        "import Lean\n\
         namespace Miri.EscapeStage\n\
         run_cmd do\n\
           try\n\
             IO.FS.writeFile \"{}\" \"pwned\"\n\
           catch _ =>\n\
             IO.FS.writeFile \"/work/miri-lib/sandbox-escape-ro.txt\" \"pwned\"\n\
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
    let extra_out_src = "import Lean\n\
        namespace Miri.ExtraOut\n\
        run_cmd do\n\
          IO.FS.writeFile \"out/unexpected-drop.txt\" \"junk\"\n\
        def x : Nat := 1\n\
        end Miri.ExtraOut\n";
    let extra_out_path = vendor_dir.join("Miri/ExtraOut.lean");
    fs::write(&extra_out_path, extra_out_src).unwrap();
    let mut probe = Checker::new(&fix.root, None).unwrap();
    probe.set_require_mir_wp(false);
    probe.run().unwrap();
    let probe_out_dir = probe.stage.join("out");
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
                probe_out_dir
                    .join("Miri/ExtraOut.olean")
                    .to_string_lossy()
                    .into_owned(),
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

    let cache_dir = tempfile::Builder::new()
        .prefix("anneal-sandbox-extra-cache-")
        .tempdir()
        .unwrap();
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
    let mut c3 = Checker::new(&fix.root, None).unwrap();
    c3.set_require_mir_wp(false);
    c3.set_miri_cache_dir(Some(cache_dir.path().to_path_buf()));
    c3.run().unwrap();
    let err3 = c3
        .verify_and_stage_miri_entries(&vendor_dir, &[extra_entry], &extra_sources)
        .unwrap_err();
    assert_eq!(
        err3.code, 1,
        "expected policy error for extra sandbox output: {err3}"
    );
    assert!(
        err3.message.contains(
            "unexpected file in sandboxed Miri output for Miri.ExtraOut: unexpected-drop.txt"
        ),
        "unexpected error message: {err3}"
    );
    assert!(
        !c3.stage.join("miri-lib/Miri/ExtraOut.olean").exists()
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
    let qsort_cache = tempfile::Builder::new()
        .prefix("anneal-sandbox-qsort-cache-")
        .tempdir()
        .unwrap();
    let mut c4 = Checker::new(&fix.root, None).unwrap();
    c4.set_require_mir_wp(false);
    c4.set_miri_cache_dir(Some(qsort_cache.path().to_path_buf()));
    c4.run().unwrap();
    let miri_lib = c4
        .verify_and_stage_miri_entries(&real_vendor, &[qsort_entry], &qsort_sources)
        .unwrap();
    for ext in ["olean", "olean.server", "olean.private"] {
        let rel = format!("Miri/Memory/QSortProof.{ext}");
        assert!(
            miri_lib.join(&rel).is_file(),
            "expected staged {rel} in miri-lib"
        );
        assert!(
            qsort_cache.path().join(&rel).is_file(),
            "expected cached {rel} in miri cache"
        );
    }
    for ext in ["ir", "ir.sig"] {
        let rel = format!("Miri/Memory/QSortProof.{ext}");
        assert!(
            !miri_lib.join(&rel).exists(),
            "ephemeral {rel} must not be staged into miri-lib"
        );
        assert!(
            !qsort_cache.path().join(&rel).exists(),
            "ephemeral {rel} must not be written to miri cache"
        );
    }

    // Case 5: A non-module cold compile (`olean_server_sha256` and
    // `olean_private_sha256` both `None`) that emits `.ir` or `.ir.sig`
    // alongside a digest-matching `.olean` must still be rejected with policy
    // exit code `1`, staging and caching nothing.
    for (module, stem, ext) in [
        ("Miri.ExtraIr", "Miri/ExtraIr", "ir"),
        ("Miri.ExtraIrSig", "Miri/ExtraIrSig", "ir.sig"),
    ] {
        let sidecar_rel = format!("{stem}.{ext}");
        let src = format!(
            "import Lean\n\
             namespace {module}\n\
             run_cmd do\n\
               IO.FS.writeFile \"out/{sidecar_rel}\" \"fake-ir\"\n\
             def x : Nat := 1\n\
             end {module}\n"
        );
        let src_rel = format!("{stem}.lean");
        let src_path = vendor_dir.join(&src_rel);
        fs::write(&src_path, &src).unwrap();

        let mut ir_probe = Checker::new(&fix.root, None).unwrap();
        ir_probe.set_require_mir_wp(false);
        ir_probe.run().unwrap();
        let ir_probe_out = ir_probe.stage.join("out");
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
        let mut c5 = Checker::new(&fix.root, None).unwrap();
        c5.set_require_mir_wp(false);
        c5.set_miri_cache_dir(Some(ir_cache.path().to_path_buf()));
        c5.run().unwrap();
        let err5 = c5
            .verify_and_stage_miri_entries(&vendor_dir, &[ir_entry], &ir_sources)
            .unwrap_err();
        assert_eq!(
            err5.code, 1,
            "expected policy error for non-module {ext} sidecar: {err5}"
        );
        assert_eq!(err5.phase, "miri-pin");
        let expected_diag =
            format!("unexpected file in sandboxed Miri output for {module}: {sidecar_rel}");
        assert!(
            err5.message.contains(&expected_diag),
            "expected `{expected_diag}`, got: {err5}"
        );
        assert!(
            !c5.stage.join("miri-lib").join(&olean_rel).exists()
                && !c5.stage.join("miri-lib").join(&sidecar_rel).exists()
                && !ir_cache.path().join(&olean_rel).exists()
                && !ir_cache.path().join(&sidecar_rel).exists(),
            "rejected non-module {ext} output must not be staged or cached"
        );
    }
}

const SYNTHETIC_CANARIES: &[(&str, &str, &str, &str)] = &[
    (
        "CanaryPositiveAddAnnealClaim",
        "canary_positive_add_anneal",
        "PositiveCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryPositiveEmptyUnitFnClaim",
        "canary_positive_empty_unit_fn",
        "PositiveCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryPositiveStmtsAndCfAnnealClaim",
        "canary_positive_stmts_and_cf_anneal",
        "PositiveCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryPositiveUnopAnnealClaim",
        "canary_positive_unop_anneal",
        "PositiveCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryPositiveAllBinopsAnnealClaim",
        "canary_positive_all_binops_anneal",
        "PositiveCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryPositiveAllIntWidthsAnnealClaim",
        "canary_positive_all_int_widths_anneal",
        "IntWidthBoundaryCanary",
        "True.intro",
    ),
    (
        "CanaryNegativeUbDivZeroAnnealClaim",
        "canary_negative_ub_div_zero_anneal",
        "NegativeCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryNegativeUbSignedRemOverflowI8Claim",
        "canary_negative_ub_signed_rem_overflow_i8",
        "NegativeCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryNegativeUnsupportedAnnealClaim",
        "canary_negative_unsupported_anneal",
        "NegativeCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryNegativeUbAddUncheckedOverflowU32Claim",
        "canary_negative_ub_add_unchecked_overflow_u32",
        "And NegativeCanaryClaim PositiveCanaryClaim",
        "And.intro True.intro True.intro",
    ),
    (
        "CanaryNegativeUbShiftUncheckedAtBitwidthAnnealClaim",
        "canary_negative_ub_shift_unchecked_at_bitwidth_anneal",
        "NegativeCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryNegativeUbStorageDeadReadAnnealClaim",
        "canary_negative_ub_storage_dead_read_anneal",
        "NegativeCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim",
        "canary_negative_ub_storage_dead_return_place_anneal",
        "NegativeCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryNegativeUbUnreachableAnnealClaim",
        "canary_negative_ub_unreachable_anneal",
        "NegativeCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryNegativeUnsupportedUnsignedNegAnnealClaim",
        "canary_negative_unsupported_unsigned_neg_anneal",
        "NegativeCanaryClaim",
        "True.intro",
    ),
];

/// Configurable synthetic fixture containing minimal `Trusted.MirAst`,
/// `Trusted.MirSemantics`, `Anneal`, and `Anneal.MirWp` modules that pass
/// `verifyMirWpCoreTheorems` out of the box so individual negative tests can
/// mutate a single admission check in isolation.
struct MirWpSyntheticSpec {
    mir_ast_extra: String,
    wp_soundness_claim: Option<String>,
    wp_fault_soundness_claim: Option<String>,
    canary_claim_overrides: BTreeMap<String, Option<String>>,
    anneal_extra: String,
    wp_soundness_proof: Option<String>,
    wp_fault_soundness_proof: Option<String>,
    canary_proof_overrides: BTreeMap<String, Option<String>>,
    mir_wp_extra: String,
}

impl MirWpSyntheticSpec {
    fn valid() -> Self {
        Self {
            mir_ast_extra: String::new(),
            wp_soundness_claim: Some(
                "def WpSoundnessClaim (_f : Nat) : Prop := And SatisfiesPost (And Diverges Behavior)"
                    .to_string(),
            ),
            wp_fault_soundness_claim: Some(
                "def WpFaultSoundnessClaim (_f : Nat) : Prop := And ReachesResult (And Diverges WellFormed)"
                    .to_string(),
            ),
            canary_claim_overrides: BTreeMap::new(),
            anneal_extra: String::new(),
            wp_soundness_proof: Some(
                "theorem wellFormed_and_spec_of_wp : \
                 Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
                 And.intro True.intro (And.intro True.intro True.intro)"
                    .to_string(),
            ),
            wp_fault_soundness_proof: Some(
                "theorem reaches_fault_and_exclusive_of_wpFault : \
                 Trusted.MirSemantics.WpFaultSoundnessClaim Anneal.MirWp.wpFaultProg := \
                 And.intro True.intro (And.intro True.intro True.intro)"
                    .to_string(),
            ),
            canary_proof_overrides: BTreeMap::new(),
            mir_wp_extra: String::new(),
        }
    }

    fn materialize(&self) -> TempFixture {
        let fix = TempFixture::new(Some(HEADER));
        fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
        fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();

        let mir_ast = format!(
            "-- anneal-trust-tier: candidate:mir_ast\n\
             prelude\n\
             import Init.NotationExtra\n\
             namespace Trusted.MirAst\n\
             def placeholder : Nat := 0\n\
             end Trusted.MirAst\n\
             {}\n",
            self.mir_ast_extra
        );
        fs::write(fix.root.join("trusted/lean/Trusted/MirAst.lean"), mir_ast).unwrap();

        let mut sem = String::from(
            "-- anneal-trust-tier: candidate:mir_semantics\n\
             prelude\n\
             import Init.NotationExtra\n\
             import Trusted.MirAst\n\
             namespace Trusted.MirSemantics\n\
             def SatisfiesPost : Prop := True\n\
             def Diverges : Prop := True\n\
             def Behavior : Prop := True\n\
             def ReachesResult : Prop := True\n\
             def WellFormed : Prop := True\n\
             def PositiveCanaryClaim : Prop := True\n\
             def NegativeCanaryClaim : Prop := True\n\
             def IntWidthBoundaryCanary : Prop := True\n",
        );
        if let Some(decl) = &self.wp_soundness_claim {
            sem.push_str(decl);
            sem.push('\n');
        }
        if let Some(decl) = &self.wp_fault_soundness_claim {
            sem.push_str(decl);
            sem.push('\n');
        }
        for &(claim, _, body, _) in SYNTHETIC_CANARIES {
            match self.canary_claim_overrides.get(claim) {
                Some(None) => {}
                Some(Some(custom)) => {
                    sem.push_str(custom);
                    sem.push('\n');
                }
                None => {
                    sem.push_str(&format!("def {claim} : Prop := {body}\n"));
                }
            }
        }
        sem.push_str("end Trusted.MirSemantics\n");
        fs::write(fix.root.join("trusted/lean/Trusted/MirSemantics.lean"), sem).unwrap();

        let mut wp = String::from(
            "prelude\n\
             import Init.NotationExtra\n\
             import Trusted\n\
             import Trusted.MirAst\n\
             import Trusted.MirSemantics\n\
             namespace Anneal.MirWp\n\
             def wpProg : Nat := 0\n\
             def wpFaultProg : Nat := 0\n",
        );
        if let Some(decl) = &self.wp_soundness_proof {
            wp.push_str(decl);
            wp.push('\n');
        }
        if let Some(decl) = &self.wp_fault_soundness_proof {
            wp.push_str(decl);
            wp.push('\n');
        }
        for &(claim, proof, _, proof_term) in SYNTHETIC_CANARIES {
            match self.canary_proof_overrides.get(proof) {
                Some(None) => {}
                Some(Some(custom)) => {
                    wp.push_str(custom);
                    wp.push('\n');
                }
                None => {
                    wp.push_str(&format!(
                        "theorem {proof} : Trusted.MirSemantics.{claim} := {proof_term}\n"
                    ));
                }
            }
        }
        wp.push_str("end Anneal.MirWp\n");
        if !self.mir_wp_extra.is_empty() {
            wp.push_str(&self.mir_wp_extra);
            wp.push('\n');
        }
        fs::write(fix.root.join("theory/Anneal/MirWp.lean"), wp).unwrap();

        let anneal = format!(
            "prelude\n\
             import Init.NotationExtra\n\
             import Trusted\n\
             import Trusted.MirAst\n\
             import Trusted.MirSemantics\n\
             import Anneal.MirWp\n\
             {}\n",
            self.anneal_extra
        );
        fs::write(fix.root.join("theory/Anneal.lean"), anneal).unwrap();
        fix
    }

    fn expect_audit_policy_err(&self, expected_substring: &str) {
        let fix = self.materialize();
        let mut checker = Checker::new(&fix.root, None).unwrap();
        let err = checker.run().unwrap_err();
        assert_eq!(err.code, 1, "expected exit code 1, got: {err}");
        assert_eq!(err.phase, "audit", "expected audit phase, got: {err}");
        assert!(
            checker.execution_began,
            "expected Lean execution before audit failure: {err}"
        );
        assert!(
            err.message.contains(expected_substring),
            "expected error containing {expected_substring:?}, got: {err}"
        );
    }
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
    let mut checker_missing_all = Checker::new(&fix_missing_all.root, None).unwrap();
    let err_missing_all = checker_missing_all.run().unwrap_err();
    assert_eq!(err_missing_all.code, 1);
    assert_eq!(err_missing_all.phase, "audit");
    assert!(
        err_missing_all
            .message
            .contains("missing required trusted module Trusted.MirAst"),
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
    let mut checker_missing_both = Checker::new(&fix_missing_both.root, None).unwrap();
    let err_missing_both = checker_missing_both.run().unwrap_err();
    assert_eq!(err_missing_both.code, 1);
    assert_eq!(err_missing_both.phase, "audit");
    assert!(
        err_missing_both
            .message
            .contains("missing required trusted module Trusted.MirSemantics"),
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
    let err_pure_lift = fix_pure_lift_only
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_pure_lift
            .message
            .contains("missing required trusted module Trusted.MirAst"),
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
    let err_mir_wp_only = fix_mir_wp_only
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_mir_wp_only
            .message
            .contains("missing required trusted module Trusted.MirAst"),
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
    let err_sem_only = fix_sem_only
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_sem_only
            .message
            .contains("missing required trusted module Trusted.MirAst"),
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
    let err_ast_only = fix_ast_only
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_ast_only
            .message
            .contains("missing required trusted module Trusted.MirSemantics"),
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
    let err_no_wp = fix_no_wp
        .check_expected(Some(1), Some("audit"), Some(true))
        .unwrap_err();
    assert!(
        err_no_wp
            .message
            .contains("missing required theory module Anneal.MirWp"),
        "unexpected error: {err_no_wp}"
    );
}

/// Verifies every rejection branch of `requireParamClaimProof` in
/// `TrustedBoundary.lean` (missing theorem, non-theorem proof, wrong-module
/// proof, weakened/wrong-type proof, non-definition claim, wrong-module claim,
/// and claim bodies missing required semantic constants) against a passing
/// synthetic baseline.
#[test]
fn enforces_mir_wp_param_claim_proof_rules() {
    // Baseline: the unmutated synthetic fixture passes with default
    // `require_mir_wp == true`.
    let baseline = MirWpSyntheticSpec::valid().materialize();
    let mut checker = Checker::new(&baseline.root, None).unwrap();
    let report = checker.run().unwrap();
    assert_eq!(report.get("replay"), Some(&json!(true)));

    // Missing `wellFormed_and_spec_of_wp`.
    let mut missing_wp_thm = MirWpSyntheticSpec::valid();
    missing_wp_thm.wp_soundness_proof = None;
    missing_wp_thm
        .expect_audit_policy_err("missing required theorem Anneal.MirWp.wellFormed_and_spec_of_wp");

    // Missing `reaches_fault_and_exclusive_of_wpFault`.
    let mut missing_fault_thm = MirWpSyntheticSpec::valid();
    missing_fault_thm.wp_fault_soundness_proof = None;
    missing_fault_thm.expect_audit_policy_err(
        "missing required theorem Anneal.MirWp.reaches_fault_and_exclusive_of_wpFault",
    );

    // Non-theorem proof (`def` instead of `theorem`).
    let mut def_instead_of_thm = MirWpSyntheticSpec::valid();
    def_instead_of_thm.wp_soundness_proof =
        Some("def wellFormed_and_spec_of_wp : Nat := 0".to_string());
    def_instead_of_thm
        .expect_audit_policy_err("expected Anneal.MirWp.wellFormed_and_spec_of_wp to be a theorem");

    // Proof defined in `Anneal` instead of `Anneal.MirWp`.
    let mut wrong_proof_mod = MirWpSyntheticSpec::valid();
    wrong_proof_mod.wp_soundness_proof = None;
    wrong_proof_mod.anneal_extra = "\
        namespace Anneal.MirWp\n\
        theorem wellFormed_and_spec_of_wp : \
            Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
          And.intro True.intro (And.intro True.intro True.intro)\n\
        end Anneal.MirWp"
        .to_string();
    wrong_proof_mod.expect_audit_policy_err(
        "expected Anneal.MirWp.wellFormed_and_spec_of_wp to be defined in Anneal.MirWp, found Anneal",
    );

    // Weakened / wrong-type proof (`True` instead of
    // `WpSoundnessClaim wpProg`).
    let mut weakened_wp_thm = MirWpSyntheticSpec::valid();
    weakened_wp_thm.wp_soundness_proof =
        Some("theorem wellFormed_and_spec_of_wp : True := True.intro".to_string());
    weakened_wp_thm.expect_audit_policy_err(
        "theorem Anneal.MirWp.wellFormed_and_spec_of_wp must prove \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg directly",
    );

    // Non-definition claim (`inductive` instead of `def`).
    let mut non_def_claim = MirWpSyntheticSpec::valid();
    non_def_claim.wp_soundness_claim =
        Some("inductive WpSoundnessClaim (_f : Nat) : Prop where\n  | intro".to_string());
    non_def_claim.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
         Trusted.MirSemantics.WpSoundnessClaim.intro"
            .to_string(),
    );
    non_def_claim.expect_audit_policy_err(
        "expected Trusted.MirSemantics.WpSoundnessClaim to be a definition",
    );

    // Claim defined in `Trusted.MirAst` instead of `Trusted.MirSemantics`.
    let mut wrong_claim_mod = MirWpSyntheticSpec::valid();
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
    wrong_claim_mod.expect_audit_policy_err(
        "expected Trusted.MirSemantics.WpSoundnessClaim to be defined in \
         Trusted.MirSemantics, found Trusted.MirAst",
    );

    // Claim body missing required `SatisfiesPost` reference
    // (`TrustedBoundary.lean` `requireParamClaimProof` `reqConsts` check).
    let mut missing_req_const = MirWpSyntheticSpec::valid();
    missing_req_const.wp_soundness_claim =
        Some("def WpSoundnessClaim (_f : Nat) : Prop := And Diverges Behavior".to_string());
    missing_req_const.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    missing_req_const.expect_audit_policy_err(
        "claim Trusted.MirSemantics.WpSoundnessClaim body must reference \
         Trusted.MirSemantics.SatisfiesPost",
    );

    // Claim body missing required `Diverges` reference (prevents silently
    // weakening the audited WP claim to partial correctness).
    let mut missing_diverges_const = MirWpSyntheticSpec::valid();
    missing_diverges_const.wp_soundness_claim =
        Some("def WpSoundnessClaim (_f : Nat) : Prop := And SatisfiesPost Behavior".to_string());
    missing_diverges_const.wp_soundness_proof = Some(
        "theorem wellFormed_and_spec_of_wp : \
         Trusted.MirSemantics.WpSoundnessClaim Anneal.MirWp.wpProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    missing_diverges_const.expect_audit_policy_err(
        "claim Trusted.MirSemantics.WpSoundnessClaim body must reference \
         Trusted.MirSemantics.Diverges",
    );

    // Fault claim body missing required `Diverges` reference.
    let mut missing_fault_diverges_const = MirWpSyntheticSpec::valid();
    missing_fault_diverges_const.wp_fault_soundness_claim = Some(
        "def WpFaultSoundnessClaim (_f : Nat) : Prop := And ReachesResult WellFormed".to_string(),
    );
    missing_fault_diverges_const.wp_fault_soundness_proof = Some(
        "theorem reaches_fault_and_exclusive_of_wpFault : \
         Trusted.MirSemantics.WpFaultSoundnessClaim Anneal.MirWp.wpFaultProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    missing_fault_diverges_const.expect_audit_policy_err(
        "claim Trusted.MirSemantics.WpFaultSoundnessClaim body must reference \
         Trusted.MirSemantics.Diverges",
    );

    // Fault claim body missing required `WellFormed` reference.
    let mut missing_fault_req_const = MirWpSyntheticSpec::valid();
    missing_fault_req_const.wp_fault_soundness_claim = Some(
        "def WpFaultSoundnessClaim (_f : Nat) : Prop := And ReachesResult Diverges".to_string(),
    );
    missing_fault_req_const.wp_fault_soundness_proof = Some(
        "theorem reaches_fault_and_exclusive_of_wpFault : \
         Trusted.MirSemantics.WpFaultSoundnessClaim Anneal.MirWp.wpFaultProg := \
         And.intro True.intro True.intro"
            .to_string(),
    );
    missing_fault_req_const.expect_audit_policy_err(
        "claim Trusted.MirSemantics.WpFaultSoundnessClaim body must reference \
         Trusted.MirSemantics.WellFormed",
    );
}

/// Verifies every rejection branch of `requireExactClaimProof` in
/// `TrustedBoundary.lean` across the 15 canary claims (missing claim,
/// non-definition claim, wrong-module claim, non-`Prop` claim, claim body
/// missing required constant, missing canary theorem, non-theorem proof,
/// wrong-module proof, and weakened/wrong-type canary theorem).
#[test]
fn enforces_mir_wp_canary_claim_proof_rules() {
    // Missing canary claim from `Trusted.MirSemantics`.
    let mut missing_claim = MirWpSyntheticSpec::valid();
    missing_claim
        .canary_claim_overrides
        .insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    missing_claim
        .canary_proof_overrides
        .insert("canary_positive_add_anneal".to_string(), None);
    missing_claim.expect_audit_policy_err(
        "missing required claim Trusted.MirSemantics.CanaryPositiveAddAnnealClaim",
    );

    // Non-definition canary claim (`inductive` instead of `def`).
    let mut non_def_claim = MirWpSyntheticSpec::valid();
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
    non_def_claim.expect_audit_policy_err(
        "expected Trusted.MirSemantics.CanaryPositiveAddAnnealClaim to be a definition",
    );

    // Canary claim defined in `Trusted.MirAst` instead of
    // `Trusted.MirSemantics`.
    let mut wrong_claim_mod = MirWpSyntheticSpec::valid();
    wrong_claim_mod
        .canary_claim_overrides
        .insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    wrong_claim_mod.mir_ast_extra = "\
        namespace Trusted.MirSemantics\n\
        def CanaryPositiveAddAnnealClaim : Prop := True\n\
        end Trusted.MirSemantics"
        .to_string();
    wrong_claim_mod.expect_audit_policy_err(
        "expected Trusted.MirSemantics.CanaryPositiveAddAnnealClaim to be defined in \
         Trusted.MirSemantics, found Trusted.MirAst",
    );

    // Canary claim declared inside `Anneal.MirWp` (rejected fail-closed by
    // `Trusted` namespace isolation in `validateLocalConstant`).
    let mut claim_in_theory = MirWpSyntheticSpec::valid();
    claim_in_theory
        .canary_claim_overrides
        .insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    claim_in_theory
        .canary_proof_overrides
        .insert("canary_positive_add_anneal".to_string(), None);
    claim_in_theory.mir_wp_extra = "\
        namespace Trusted.MirSemantics\n\
        def CanaryPositiveAddAnnealClaim : Prop := True\n\
        end Trusted.MirSemantics\n\
        namespace Anneal.MirWp\n\
        theorem canary_positive_add_anneal : \
            Trusted.MirSemantics.CanaryPositiveAddAnnealClaim := True.intro\n\
        end Anneal.MirWp"
        .to_string();
    claim_in_theory.expect_audit_policy_err(
        "non-Trusted module Anneal.MirWp cannot declare constant \
         Trusted.MirSemantics.CanaryPositiveAddAnnealClaim in Trusted namespace",
    );

    // Non-`Prop` canary claim (`Nat` instead of `Prop`).
    let mut non_prop_claim = MirWpSyntheticSpec::valid();
    non_prop_claim.canary_claim_overrides.insert(
        "CanaryPositiveAddAnnealClaim".to_string(),
        Some("def CanaryPositiveAddAnnealClaim : Nat := 0".to_string()),
    );
    non_prop_claim
        .canary_proof_overrides
        .insert("canary_positive_add_anneal".to_string(), None);
    non_prop_claim.expect_audit_policy_err(
        "expected Trusted.MirSemantics.CanaryPositiveAddAnnealClaim to have type Prop",
    );

    // Canary claim body missing required `PositiveCanaryClaim` constant
    // (`TrustedBoundary.lean` `requireExactClaimProof` `reqConsts` check).
    let mut missing_req_const = MirWpSyntheticSpec::valid();
    missing_req_const.canary_claim_overrides.insert(
        "CanaryPositiveAddAnnealClaim".to_string(),
        Some("def CanaryPositiveAddAnnealClaim : Prop := True".to_string()),
    );
    missing_req_const.expect_audit_policy_err(
        "claim Trusted.MirSemantics.CanaryPositiveAddAnnealClaim body must reference \
         Trusted.MirSemantics.PositiveCanaryClaim",
    );

    // Missing canary theorem (first canary and last canary).
    let mut missing_first_canary = MirWpSyntheticSpec::valid();
    missing_first_canary
        .canary_proof_overrides
        .insert("canary_positive_add_anneal".to_string(), None);
    missing_first_canary.expect_audit_policy_err(
        "missing required theorem Anneal.MirWp.canary_positive_add_anneal",
    );

    let mut missing_last_canary = MirWpSyntheticSpec::valid();
    missing_last_canary.canary_proof_overrides.insert(
        "canary_negative_unsupported_unsigned_neg_anneal".to_string(),
        None,
    );
    missing_last_canary.expect_audit_policy_err(
        "missing required theorem Anneal.MirWp.canary_negative_unsupported_unsigned_neg_anneal",
    );

    // Non-theorem canary proof (`def` instead of `theorem`).
    let mut def_canary = MirWpSyntheticSpec::valid();
    def_canary.canary_proof_overrides.insert(
        "canary_positive_add_anneal".to_string(),
        Some("def canary_positive_add_anneal : Nat := 0".to_string()),
    );
    def_canary.expect_audit_policy_err(
        "expected Anneal.MirWp.canary_positive_add_anneal to be a theorem",
    );

    // Canary theorem defined in `Anneal` instead of `Anneal.MirWp`.
    let mut wrong_proof_mod = MirWpSyntheticSpec::valid();
    wrong_proof_mod
        .canary_proof_overrides
        .insert("canary_positive_add_anneal".to_string(), None);
    wrong_proof_mod.anneal_extra = "\
        namespace Anneal.MirWp\n\
        theorem canary_positive_add_anneal : \
            Trusted.MirSemantics.CanaryPositiveAddAnnealClaim := True.intro\n\
        end Anneal.MirWp"
        .to_string();
    wrong_proof_mod.expect_audit_policy_err(
        "expected Anneal.MirWp.canary_positive_add_anneal to be defined in \
         Anneal.MirWp, found Anneal",
    );

    // Weakened / wrong-type canary theorem (`True` instead of the pinned
    // `CanaryPositiveAddAnnealClaim`).
    let mut weakened_canary = MirWpSyntheticSpec::valid();
    weakened_canary.canary_proof_overrides.insert(
        "canary_positive_add_anneal".to_string(),
        Some("theorem canary_positive_add_anneal : True := True.intro".to_string()),
    );
    weakened_canary.expect_audit_policy_err(
        "theorem Anneal.MirWp.canary_positive_add_anneal must prove \
         Trusted.MirSemantics.CanaryPositiveAddAnnealClaim directly",
    );
}
