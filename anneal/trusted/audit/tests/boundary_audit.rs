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

use serde_json::json;

use anneal_audit::{
    Checker, Failure, ImportEdge, InspectorRequest, Json, ModuleArtifacts, PARTS, TrustTier,
    check_cargo_boundary, default_lean_path, sha256_file,
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
