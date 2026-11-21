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
    collections::{BTreeMap, BTreeSet},
    env, fs, io,
    os::unix::fs::symlink,
    path::{Path, PathBuf},
    process::Command,
};

use anneal_audit::{
    CandidateFeature, Checker, Failure, ImportEdge, InspectorRequest, Json, MiriClosureEntry,
    ModuleArtifacts, PARTS, TrustTier, check_cargo_boundary, default_lean_path,
    ensure_miri_cache_outside_checkout, sha256_bytes, sha256_file, verify_sysroot_foundation_dir,
};
use serde_json::json;

const HEADER: &str = "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\n";

struct TempFixture {
    _dir: tempfile::TempDir,
    root: PathBuf,
}

impl TempFixture {
    fn new(source: Option<&str>) -> Self {
        let checkout = repo_root();
        let dir = tempfile::Builder::new().prefix("anneal-boundary-test-").tempdir().unwrap();
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
        fs::write(root.join("trusted/lean/Trusted.lean"), source.unwrap_or(HEADER).as_bytes())
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
                        checker.execution_began(),
                        exp_exec,
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
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap().to_path_buf()
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

/// Copies the root build files, `trusted/root-manifest.sha256`, and the Cargo
/// workspace member crates that `check_cargo_boundary` inspects from the real
/// checkout into `root`.
fn copy_cargo_workspace(root: &Path) {
    let checkout = repo_root();
    for rel in [
        "Cargo.toml",
        "Cargo.lock",
        "flake.nix",
        "flake.lock",
        "trusted/root-manifest.sha256",
        "trusted/audit/Cargo.toml",
    ] {
        fs::copy(checkout.join(rel), root.join(rel)).unwrap();
    }
    for rel in ["trusted/rustc-capture", "trusted/cargo-anneal"] {
        copy_dir_all(&checkout.join(rel), &root.join(rel)).unwrap();
    }
}

/// Compiles `body` as `module` into `out_dir` directly with `lean --setup`,
/// bypassing repository `"preflight"`, and registers the compiled `.olean` and
/// its import edges with the checker's admitted toolchain so later forged
/// modules and inspector requests can import it.
///
/// The setup descriptor lists `Init.Core` and every module in `imports`.
fn compile_forged_module(
    checker: &mut Checker,
    src_root: &Path,
    out_dir: &Path,
    imports: &[&str],
    module: &str,
    body: &str,
) {
    let rel = module.replace('.', "/");
    let src = src_root.join(format!("{rel}.lean"));
    fs::create_dir_all(src.parent().unwrap()).unwrap();
    fs::write(&src, body).unwrap();
    let out = out_dir.join(format!("{rel}.olean"));
    fs::create_dir_all(out.parent().unwrap()).unwrap();
    let edges: Vec<ImportEdge> = ["Init.Core"]
        .iter()
        .chain(imports)
        .map(|imp| ImportEdge {
            module: (*imp).to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        })
        .collect();
    let setup_path = checker.write_setup_json(module, &edges).unwrap();
    checker
        .process(
            &format!("compile-{module}"),
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "--setup".to_string(),
                setup_path.to_string_lossy().into_owned(),
                "-o".to_string(),
                out.to_string_lossy().into_owned(),
                src.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let available = BTreeMap::from([("olean", out.to_string_lossy().into_owned())]);
    let arts = ModuleArtifacts::from_available(&available, "test", String::new).unwrap();
    let adm = checker.admitted_mut().unwrap();
    adm.artifacts.insert(module.to_string(), arts);
    adm.graph.insert(module.to_string(), edges);
}

/// Writes `source` to `script` and runs it with `lean --run`.
///
/// Tests use such scripts to forge `.olean` files with `Lean.saveModuleData`,
/// which serializes arbitrary `ModuleData` without elaborating or
/// kernel-checking it, so only `TrustedBoundary.lean` can reject the result.
fn run_lean_script(checker: &mut Checker, label: &str, script: &Path, source: &str) {
    fs::write(script, source).unwrap();
    checker
        .process(
            label,
            &[
                "-j1".to_string(),
                "-M4096".to_string(),
                "--run".to_string(),
                script.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
}

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
        let neg_path = checker.stage().join(format!("neg-{idx}.lean"));
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
    let theory_pos_path = checker.stage().join("theory-pos.lean");
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
/// outside `trusted/` and `path` dependencies from `trusted/` crates to paths
/// outside `trusted/`.
#[test]
fn rejects_cargo_workspace_members_and_path_deps_outside_trusted() {
    let checkout = repo_root();
    let mut fix = TempFixture::new(None);
    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
    fs::copy(checkout.join("trusted/audit/Cargo.toml"), fix.root.join("trusted/audit/Cargo.toml"))
        .unwrap();
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
        err_member.message.contains("workspace member outside trusted/: crates/untrusted-helper")
    );

    fs::copy(checkout.join("Cargo.toml"), fix.root.join("Cargo.toml")).unwrap();
    fs::write(
        fix.root.join("trusted/rustc-capture/Cargo.toml"),
        b"[package]\nname = \"anneal-rustc-capture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[dependencies]\nuntrusted-helper = { path = \"../../crates/untrusted-helper\" }\n",
    )
    .unwrap();
    let err_dep = fix.check_expected(Some(1), Some("cargo-boundary"), Some(false)).unwrap_err();
    assert!(err_dep.message.contains(
        "trusted/rustc-capture path dependency points outside trusted/: crates/untrusted-helper"
    ));

    fs::copy(
        checkout.join("trusted/rustc-capture/Cargo.toml"),
        fix.root.join("trusted/rustc-capture/Cargo.toml"),
    )
    .unwrap();
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
    let err_contam = f_contam.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
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
    let mut f_ok =
        TempFixture::new(Some(&format!("{HEADER}import Trusted.VettedSub\nimport Trusted.Cand\n")));
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

#[test]
fn rejects_reserved_kernel_roots_and_user_splitter_children_in_theory() {
    let mut fix = TempFixture::new(Some(
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Prelude\nimport Trusted.MirAst\n",
    ));
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
            "prelude\nimport Trusted\n\
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
    fs::copy(checkout.join("Cargo.toml"), fix_missing_dir.root.join("Cargo.toml")).unwrap();
    fs::copy(checkout.join("Cargo.lock"), fix_missing_dir.root.join("Cargo.lock")).unwrap();
    fs::copy(checkout.join("flake.nix"), fix_missing_dir.root.join("flake.nix")).unwrap();
    fs::copy(checkout.join("flake.lock"), fix_missing_dir.root.join("flake.lock")).unwrap();
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
    assert!(!checkout_victim.exists(), "sandboxed run_cmd must not be able to write to checkout");

    // Case 2: A malicious `run_cmd` attempting to write into the auditor's
    // read-only `/work/miri-lib` or host `stage` fails and leaves both
    // untouched.
    let mut c2 = Checker::new(&fix.root, None).unwrap();
    c2.set_require_mir_wp(false);
    c2.run().unwrap();
    let stage_victim = c2.stage().join("sandbox-escape-stage.txt");
    let ro_lib_victim = c2.stage().join("miri-lib/sandbox-escape-ro.txt");
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
    let mut c3 = Checker::new(&fix.root, None).unwrap();
    c3.set_require_mir_wp(false);
    c3.set_miri_cache_dir(Some(cache_dir.path().to_path_buf()));
    c3.run().unwrap();
    let err3 =
        c3.verify_and_stage_miri_entries(&vendor_dir, &[extra_entry], &extra_sources).unwrap_err();
    assert_eq!(err3.code, 1, "expected policy error for extra sandbox output: {err3}");
    assert!(
        err3.message.contains(
            "unexpected file in sandboxed Miri output for Miri.ExtraOut: unexpected-drop.txt"
        ),
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
    let mut c4 = Checker::new(&fix.root, None).unwrap();
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
    // alongside a digest-matching `.olean` must still be rejected with policy
    // exit code `1`, staging and caching nothing.
    for (module, stem, ext) in
        [("Miri.ExtraIr", "Miri/ExtraIr", "ir"), ("Miri.ExtraIrSig", "Miri/ExtraIrSig", "ir.sig")]
    {
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
        let mut c5 = Checker::new(&fix.root, None).unwrap();
        c5.set_require_mir_wp(false);
        c5.set_miri_cache_dir(Some(ir_cache.path().to_path_buf()));
        c5.run().unwrap();
        let err5 =
            c5.verify_and_stage_miri_entries(&vendor_dir, &[ir_entry], &ir_sources).unwrap_err();
        assert_eq!(err5.code, 1, "expected policy error for non-module {ext} sidecar: {err5}");
        assert_eq!(err5.phase, "miri-pin");
        let expected_diag =
            format!("unexpected file in sandboxed Miri output for {module}: {sidecar_rel}");
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
    (
        "CanaryPositiveEnumExplicitReprAnnealClaim",
        "canary_positive_enum_explicit_repr_anneal",
        "PositiveCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryPositiveZstSingleEnumAnnealClaim",
        "canary_positive_zst_single_enum_anneal",
        "PositiveCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryNegativeUbEnumInvalidTagAndUninitAnnealClaim",
        "canary_negative_ub_enum_invalid_tag_and_uninit_anneal",
        "NegativeCanaryClaim",
        "True.intro",
    ),
    (
        "CanaryCrateAndBodyVerifiedAnnealClaim",
        "canary_crate_and_body_verified_anneal",
        "And CrateTheorem (And UnitTheorem BodyVerified)",
        "And.intro True.intro (And.intro True.intro True.intro)",
    ),
    (
        "CanaryMemoryLifecycleAnnealClaim",
        "canary_memory_lifecycle_anneal",
        "And PositiveCanaryClaim (And initState (And evalStep (And forceAllocation readBytes)))",
        "And.intro True.intro (And.intro True.intro (And.intro True.intro \
         (And.intro True.intro True.intro)))",
    ),
    (
        "CanaryPositiveCharAndCmpAnnealClaim",
        "canary_positive_char_and_cmp_anneal",
        "And PositiveCanaryClaim (And mkBinOpProg (And Trusted.MirAst.BinOp.cmp \
         (And Trusted.MirAst.MirTy.char (And charVal \
         (And mkCmpDiscriminantProg progCharSwitch)))))",
        "And.intro True.intro (And.intro True.intro (And.intro True.intro \
         (And.intro True.intro (And.intro True.intro \
         (And.intro True.intro True.intro)))))",
    ),
    (
        "CanaryNegativeCharAndCmpAnnealClaim",
        "canary_negative_char_and_cmp_anneal",
        "And NegativeCanaryClaim (And progInvalidCharConstUb \
         (And progInvalidCharSwitchCaseUb (And mkBinOpProg \
         (And Trusted.MirAst.BinOp.cmp mkUnOpProg))))",
        "And.intro True.intro (And.intro True.intro (And.intro True.intro \
         (And.intro True.intro (And.intro True.intro True.intro))))",
    ),
    (
        "CanaryPositiveOverflowOpsAnnealClaim",
        "canary_positive_overflow_ops_anneal",
        "And PositiveCanaryClaim (And mkBinOpProg (And overflowPairTy \
         (And Trusted.MirAst.BinOp.addWithOverflow \
         (And Trusted.MirAst.BinOp.subWithOverflow \
         Trusted.MirAst.BinOp.mulWithOverflow))))",
        "And.intro True.intro (And.intro True.intro (And.intro True.intro \
         (And.intro True.intro (And.intro True.intro True.intro))))",
    ),
    (
        "CanaryPositiveIntToIntCastAnnealClaim",
        "canary_positive_int_to_int_cast_anneal",
        "And PositiveCanaryClaim (And mkIntToIntCastProg \
         (And Trusted.MirAst.MirTy.char charVal))",
        "And.intro True.intro (And.intro True.intro (And.intro True.intro True.intro))",
    ),
    (
        "CanaryNegativeIntToIntCastAnnealClaim",
        "canary_negative_int_to_int_cast_anneal",
        "And NegativeCanaryClaim (And mkIntToIntCastProg \
         (And Trusted.MirAst.MirTy.char progCastUninitSourceUb))",
        "And.intro True.intro (And.intro True.intro (And.intro True.intro True.intro))",
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
             def BinOp.cmp : Prop := True\n\
             def BinOp.addWithOverflow : Prop := True\n\
             def BinOp.subWithOverflow : Prop := True\n\
             def BinOp.mulWithOverflow : Prop := True\n\
             def MirTy.char : Prop := True\n\
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
             def IntWidthBoundaryCanary : Prop := True\n\
             def CrateTheorem : Prop := True\n\
             def UnitTheorem : Prop := True\n\
             def BodyVerified : Prop := True\n\
             def initState : Prop := True\n\
             def evalStep : Prop := True\n\
             def forceAllocation : Prop := True\n\
             def readBytes : Prop := True\n\
             def mkBinOpProg : Prop := True\n\
             def mkUnOpProg : Prop := True\n\
             def charVal : Prop := True\n\
             def mkCmpDiscriminantProg : Prop := True\n\
             def progCharSwitch : Prop := True\n\
             def progInvalidCharConstUb : Prop := True\n\
             def progInvalidCharSwitchCaseUb : Prop := True\n\
             def overflowPairTy : Prop := True\n\
             def mkIntToIntCastProg : Prop := True\n\
             def progCastUninitSourceUb : Prop := True\n",
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
        assert!(checker.execution_began(), "expected Lean execution before audit failure: {err}");
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
    let mut checker_missing_both = Checker::new(&fix_missing_both.root, None).unwrap();
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
    let baseline = MirWpSyntheticSpec::valid().materialize();
    let mut checker = Checker::new(&baseline.root, None).unwrap();
    let report = checker.run().unwrap();
    assert_eq!(report.get("replay"), Some(&json!(true)));

    // Missing `WpSoundnessClaim` from `Trusted.MirSemantics`.
    let mut missing_wp_claim = MirWpSyntheticSpec::valid();
    missing_wp_claim.wp_soundness_claim = None;
    missing_wp_claim.wp_soundness_proof = None;
    missing_wp_claim
        .expect_audit_policy_err("missing required claim Trusted.MirSemantics.WpSoundnessClaim");

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
    // (`TrustedBoundary.lean` `requireClaimProof` `reqConsts` check).
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

/// Verifies every rejection branch of `requireClaimProof` (exact-claim mode,
/// `argName? = none`) in `TrustedBoundary.lean` across the 25 canary claims
/// (missing claim, non-definition claim, wrong-module claim, non-`Prop` claim,
/// claim body missing required constant, missing canary theorem, non-theorem
/// proof, wrong-module proof, and weakened/wrong-type canary theorem).
#[test]
fn enforces_mir_wp_canary_claim_proof_rules() {
    // Missing canary claim from `Trusted.MirSemantics`.
    let mut missing_claim = MirWpSyntheticSpec::valid();
    missing_claim.canary_claim_overrides.insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    missing_claim.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
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
    wrong_claim_mod.canary_claim_overrides.insert("CanaryPositiveAddAnnealClaim".to_string(), None);
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
    // `Trusted` namespace isolation in `validateRepoConstant`).
    let mut claim_in_theory = MirWpSyntheticSpec::valid();
    claim_in_theory.canary_claim_overrides.insert("CanaryPositiveAddAnnealClaim".to_string(), None);
    claim_in_theory.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
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
    non_prop_claim.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
    non_prop_claim.expect_audit_policy_err(
        "expected Trusted.MirSemantics.CanaryPositiveAddAnnealClaim to have type Prop",
    );

    // Canary claim body missing required `PositiveCanaryClaim` constant
    // (`TrustedBoundary.lean` `requireClaimProof` `reqConsts` check).
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
    missing_last_canary
        .canary_proof_overrides
        .insert("canary_crate_and_body_verified_anneal".to_string(), None);
    missing_last_canary.expect_audit_policy_err(
        "missing required theorem Anneal.MirWp.canary_crate_and_body_verified_anneal",
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
    wrong_proof_mod.canary_proof_overrides.insert("canary_positive_add_anneal".to_string(), None);
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

    // Memory-lifecycle canary claim that drops `forceAllocation` (so the
    // `.indirect`-local path is no longer exercised).
    let mut weak_memory_canary = MirWpSyntheticSpec::valid();
    weak_memory_canary.canary_claim_overrides.insert(
        "CanaryMemoryLifecycleAnnealClaim".to_string(),
        Some(
            "def CanaryMemoryLifecycleAnnealClaim : Prop := \
             And PositiveCanaryClaim (And initState (And evalStep (And readBytes readBytes)))"
                .to_string(),
        ),
    );
    weak_memory_canary.expect_audit_policy_err(
        "claim Trusted.MirSemantics.CanaryMemoryLifecycleAnnealClaim body must reference \
         Trusted.MirSemantics.forceAllocation",
    );

    // `char`, `BinOp.cmp`, overflow-pair, and `IntToInt` cast canary claims
    // that each replace one pinned constant with a duplicate of another (so
    // the new operation, fixture, or UB path is no longer exercised while the
    // synthetic proof still type-checks). Each weakened body keeps every other
    // required constant, so the rejection names exactly the dropped one.
    for (claim, weakened_body, dropped) in [
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
        let mut weak_canary = MirWpSyntheticSpec::valid();
        weak_canary.canary_claim_overrides.insert(
            claim.to_string(),
            Some(format!("def {claim} : Prop := {weakened_body}")),
        );
        weak_canary.expect_audit_policy_err(&format!(
            "claim Trusted.MirSemantics.{claim} body must reference {dropped}"
        ));
    }
}

/// Verifies Pass 2 non-backsliding enforcement (`--require-correspondence`):
/// missing correspondence directories, `verifyCorrespondenceClaims` across all
/// 37 required claims (including `CorrespondenceAtChoicesClaim`,
/// `FaultEquivalenceAtChoicesClaim`, `OperandMachine.evalOperand` wiring,
/// `RefStepSoundForAllowedStepClaim`, `BytesCodecMatchesMiriClaim`, and the
/// `D14`–`D16` `char`/`cmp`, cast, and overflow canaries), and
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
    let mut checker = Checker::new(&fix_missing_corr.root, None).unwrap();
    checker.set_require_mir_wp(false);
    checker.set_require_correspondence(true);
    let err_corr = checker.run().unwrap_err();
    assert_eq!(err_corr.code, 1);
    assert_eq!(err_corr.phase, "correspondence");
    assert!(
        err_corr.message.contains("missing required correspondence directories"),
        "unexpected error: {err_corr}"
    );

    // 2. Pass 2 (`InspectorRequest::CorrespondenceAudit`) enforces
    // `verifyCorrespondenceClaims` (required constant references across all 37
    // claims and exact claim-type proof checking) and
    // `verifyRefEvaluatorIndependence` (39 live `ExecutionMachine` Miri
    // primitives on `[evalRefStep, initRefState]` without `RefAllowedStep`
    // masking, `AllowedStep` on `RefAllowedStep`, fail-closed module-level
    // import isolation and modular placement checks on isolated
    // `Trusted.Correspondence.*` evaluator submodules, and closed
    // module-origin isolation across both cones).
    let fix_pass2 = TempFixture::new(None);
    let mut checker_pass2 = Checker::new(&fix_pass2.root, None).unwrap();
    checker_pass2.set_require_mir_wp(false);
    checker_pass2.run().unwrap();
    let trusted_lib = checker_pass2.stage().join("lib");
    let corr_src = checker_pass2.stage().join("src/fake-corr");
    let corr_lib = checker_pass2.stage().join("fake-corr-lib");
    let vendor_src = checker_pass2.stage().join("src/fake-vendor");
    let vendor_lib = checker_pass2.stage().join("fake-vendor-lib");
    let search_paths = vec![trusted_lib.clone(), vendor_lib.clone(), corr_lib.clone()];

    compile_forged_module(
        &mut checker_pass2,
        &vendor_src,
        &vendor_lib,
        &[],
        "Miri.FakeStubs",
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
         def takeLastPendingMoveDeinit : Nat := 0\n\
         def recordPendingMoveDeinit : Nat := 0\n\
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
         namespace Miri.Interpreter.FnArg\n\
         def copyFnArg : Nat := 0\n\
         end Miri.Interpreter.FnArg\n\
         namespace Miri.Interpreter.Call\n\
         def deinitInPlaceArg : Nat := 0\n\
         end Miri.Interpreter.Call\n\
         namespace Miri.Interpreter.ScalarOps\n\
         def binary : Nat := 0\n\
         def unary : Nat := 0\n\
         end Miri.Interpreter.ScalarOps\n\
         namespace Miri.Interpreter.IntegerOps\n\
         def binary : Nat := 0\n\
         def binaryBool : Nat := 0\n\
         def unary : Nat := 0\n\
         def binaryChar : Nat := 0\n\
         end Miri.Interpreter.IntegerOps\n\
         namespace Miri.Interpreter.Cast\n\
         def cast : Nat := 0\n\
         end Miri.Interpreter.Cast\n\
         namespace Miri.Interpreter.IntegerCast\n\
         def cast : Nat := 0\n\
         end Miri.Interpreter.IntegerCast\n\
         namespace Miri.Memory.ScalarInt\n\
         def truncateFromUInt : Nat := 0\n\
         def tryFromUInt : Nat := 0\n\
         def tryToBool : Nat := 0\n\
         def toChar : Nat := 0\n\
         def ofChar : Nat := 0\n\
         end Miri.Memory.ScalarInt\n\
         namespace Miri.Interpreter\n\
         def evalOperand : Nat := 0\n\
         def evalRvalueIntoPlace : Nat := 0\n\
         end Miri.Interpreter\n\
         namespace Miri.Interpreter.TerminatorMachine\n\
         def beforeTerminatorWithChoice : Nat := 0\n\
         end Miri.Interpreter.TerminatorMachine\n\
         namespace Miri.Interpreter.Discriminant\n\
         def readDiscriminant : Nat := 0\n\
         def discriminantForVariant : Nat := 0\n\
         end Miri.Interpreter.Discriminant\n\
         namespace Miri.Memory.Allocation\n\
         def writeScalar : Nat := 0\n\
         def getBytesUnchecked : Nat := 0\n\
         def readScalar : Nat := 0\n\
         def writeUninit : Nat := 0\n\
         end Miri.Memory.Allocation\n",
    );

    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &[],
        "Trusted.MirSemantics",
        "prelude\nimport Init.Core\n\
         namespace Trusted.MirSemantics\n\
         def WellFormed : Prop := True\n\
         def Behavior : Prop := True\n\
         def Diverges : Prop := True\n\
         def ReachesResult : Prop := True\n\
         def ValidPrefixAtChoices : Prop := True\n\
         def BehaviorAtChoices : Prop := True\n\
         def DivergesAtChoices : Prop := True\n\
         def ReachesResultAtChoices : Prop := True\n\
         def initState : Nat := 0\n\
         def Step : Prop := True\n\
         def Reaches : Prop := True\n\
         def progAddUncheckedU32 : Nat := 0\n\
         def progAddU32 : Nat := 0\n\
         def progEnumExplicitReprU8 : Nat := 0\n\
         def progEnumSignedTagIsize : Nat := 0\n\
         def progZstSingleEnumImplicitRet : Nat := 0\n\
         def progZstSingleEnumMoveAndDiscr : Nat := 0\n\
         def progEnumInvalidTagConstUb : Nat := 0\n\
         def progEnumUninitDiscrUb : Nat := 0\n\
         def evalShiftOp : Nat := 0\n\
         def evalArithOp : Nat := 0\n\
         def jumpToBlock : Nat := 0\n\
         def enumAdmitted : Nat := 0\n\
         def tagBitsToDiscrBits : Nat := 0\n\
         def isZstEnumTy : Nat := 0\n\
         def findDiscrVariant? : Nat := 0\n\
         def evalStep : Nat := 0\n\
         def encodeVal : Nat := 0\n\
         def decodeVal : Nat := 0\n\
         def profileTargetEndian : Nat := 0\n\
         def mkBinOpProg : Nat := 0\n\
         def mkCmpDiscriminantProg : Nat := 0\n\
         def progCharSwitch : Nat := 0\n\
         def mkIntToIntCastProg : Nat := 0\n\
         def overflowPairTy : Nat := 0\n\
         def unlistedAnnealHelper : Nat := 0\n\
         end Trusted.MirSemantics\n",
    );

    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &[],
        "Trusted.MirSemantics.SubHelper",
        "prelude\nimport Init.Core\n\
         namespace Trusted.MirSemantics\n\
         def subEvalHelper : Nat := 0\n\
         end Trusted.MirSemantics\n",
    );

    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &[],
        "Trusted.MirModel",
        "prelude\nimport Init.Core\n\
         namespace Trusted.MirSemantics\n\
         def sharedModelData : Nat := 0\n\
         end Trusted.MirSemantics\n\
         namespace Trusted.MirAst\n\
         def BinOp.cmp : Nat := 0\n\
         def BinOp.addWithOverflow : Nat := 0\n\
         def BinOp.subWithOverflow : Nat := 0\n\
         def MirTy.char : Nat := 0\n\
         end Trusted.MirAst\n",
    );

    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &[],
        "Trusted.MirHelper",
        "prelude\nimport Init.Core\n\
         namespace Trusted.MirHelper\n\
         def siblingHelper : Nat := 0\n\
         end Trusted.MirHelper\n",
    );

    // 2a. Weakened `CorrespondenceClaim` (missing
    // `Trusted.MirSemantics.WellFormed` reference) is rejected by
    // `verifyCorrespondenceClaims`.
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &[],
        "Trusted.Correspondence",
        "prelude\nimport Init.Core\n\
         namespace Trusted.Correspondence\n\
         def CorrespondenceClaim : Prop := True\n\
         end Trusted.Correspondence\n",
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &["Trusted.Correspondence"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Trusted.Correspondence\n\
         namespace Anneal.MirCorrespondenceProof\n\
         theorem correspondence_claim_holds : Trusted.Correspondence.CorrespondenceClaim := True.intro\n\
         end Anneal.MirCorrespondenceProof\n",
    );
    let run_corr_audit = |checker: &mut Checker| {
        checker.inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search_paths.clone(),
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.MirModel".to_string(),
                "Trusted.MirHelper".to_string(),
                "Trusted.MirSemantics".to_string(),
                "Trusted.MirSemantics.SubHelper".to_string(),
            ],
            corr_trusted: vec!["Trusted.Correspondence".to_string()],
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: vec!["Miri.FakeStubs".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.MirModel".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirHelper".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirSemantics".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirSemantics.SubHelper".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.Correspondence".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
            ]),
        })
    };
    let err_weak_claim = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_weak_claim.code, 1);
    assert_eq!(err_weak_claim.phase, "correspondence-audit");
    assert!(
        err_weak_claim.message.contains(
            "claim Trusted.Correspondence.CorrespondenceClaim body must reference Trusted.MirSemantics.WellFormed"
        ),
        "unexpected error: {err_weak_claim}"
    );

    // 2b. When all 37 required claims and proofs are present,
    // `verifyCorrespondenceClaims` succeeds and
    // `verifyRefEvaluatorIndependence` rejects an `evalRefStep` or
    // `initRefState` that omits any of the 39 required live `ExecutionMachine`
    // Miri primitives (even when `RefAllowedStep` reaches all of them), rejects
    // a `RefAllowedStep` omitting `ExecutionMachine.AllowedStep`, rejects
    // illegal references (directly or transitively) to any constant defined in
    // a non-allowlisted `Trusted` module (`Trusted.MirSemantics`,
    // `Trusted.MirSemantics.*`, or a sibling `Trusted.MirHelper`), and enforces
    // isolated evaluator module placement in modular layouts, while permitting
    // shared boundary data defined in `Trusted.MirModel`.
    let all_claims_src = |init_ref_state_body: &str,
                          eval_ref_step_body: &str,
                          ref_allowed_step_body: &str,
                          corr_choices_override: Option<&str>,
                          fault_choices_override: Option<&str>,
                          wiring_override: Option<&str>,
                          d6_override: Option<&str>,
                          ref_step_allowed_override: Option<&str>| {
        let corr_choices_def = corr_choices_override.unwrap_or(
            "Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧\n\
             RefValidPrefixAtChoices ∧ Trusted.MirSemantics.ValidPrefixAtChoices ∧\n\
             RefBehaviorAtChoices ∧ Trusted.MirSemantics.BehaviorAtChoices ∧\n\
             RefDivergesAtChoices ∧ Trusted.MirSemantics.DivergesAtChoices ∧\n\
             encodeProg = encodeProg",
        );
        let fault_choices_def = fault_choices_override.unwrap_or(
            "Trusted.MirSemantics.ReachesResultAtChoices ∧ RefReachesOutcomeAtChoices ∧\n\
             faultToRefOutcome = encodeProg",
        );
        let wiring_def = wiring_override.unwrap_or(
            "Miri.Interpreter.ExecutionMachine.step = Miri.Interpreter.ExecutionMachine.stepHooks ∧\n\
             Miri.Interpreter.Step.step = Miri.Interpreter.ExecutionMachine.withValidation ∧\n\
             Miri.Interpreter.ExecutionMachine.operandHooks = Miri.Interpreter.OperandMachine.evalOperand ∧\n\
             Miri.Interpreter.OperandMachine.evalPlaceToOp = Miri.Interpreter.evalOperand ∧\n\
             Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit = Miri.Interpreter.MachineHooks.recordPendingMoveDeinit ∧\n\
             Miri.Interpreter.FnArg.copyFnArg = Miri.Interpreter.Call.deinitInPlaceArg",
        );
        let d6_def = d6_override.unwrap_or(
            "progUseAfterMoveD6 = encodeProg ∧ Trusted.MirSemantics.ReachesResult ∧\n\
             Trusted.MirSemantics.WellFormed ∧ RefReachesOutcome",
        );
        let ref_step_allowed_def =
            ref_step_allowed_override.unwrap_or("RefStep ∧ RefAllowedStep = refReadReturnVal");
        format!(
            "prelude\nimport Init.Core\nimport Miri.FakeStubs\nimport Trusted.MirModel\nimport Trusted.MirHelper\nimport Trusted.MirSemantics\nimport Trusted.MirSemantics.SubHelper\n\
             namespace Trusted.Correspondence\n\
             def RefWellFormed : Prop := True\n\
             def RefBehavior : Prop := True\n\
             def RefDiverges : Prop := True\n\
             def RefValidPrefixAtChoices : Prop := True\n\
             def RefBehaviorAtChoices : Prop := True\n\
             def RefDivergesAtChoices : Prop := True\n\
             def RefReachesOutcomeAtChoices : Prop := True\n\
             def encodeProg : Nat := 0\n\
             def decodeProg : Nat := 0\n\
             def typesAreCanonical : Nat := 0\n\
             def encodeStmt : Nat := 0\n\
             def encodeRvalue : Nat := 0\n\
             def encodeOperand : Nat := 0\n\
             def encodePlace : Nat := 0\n\
             def SimulationInv : Prop := True\n\
             def stepResultToRefOutcome : Nat := 0\n\
             def mapStepRes : Nat := 0\n\
             def RefStep : Prop := True\n\
             def RefReaches : Prop := True\n\
             def RefReachesOutcome : Prop := True\n\
             def faultToRefOutcome : Nat := 0\n\
             def refReadReturnVal : Nat := 0\n\
             def progUseAfterMoveD6 : Nat := 0\n\
             def progBinOpCopyThenMoveD7a : Nat := 0\n\
             def progBinOpMoveThenCopyD7b : Nat := 0\n\
             def progBinOpMoveThenMoveD7c : Nat := 0\n\
             def progSelfMoveD8 : Nat := 0\n\
             def progMoveUnitZstD9 : Nat := 0\n\
             def transitiveSubHelper : Nat := Trusted.MirSemantics.subEvalHelper\n\
             def initRefState : Nat := {init_ref_state_body}\n\
             def evalRefStep : Nat := {eval_ref_step_body}\n\
             def RefAllowedStep : Nat := {ref_allowed_step_body}\n\
             def CorrespondenceClaim : Prop :=\n\
               Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefBehavior ∧\n\
               Trusted.MirSemantics.Diverges ∧ RefDiverges ∧ encodeProg = encodeProg\n\
             def FaultEquivalenceClaim : Prop :=\n\
               Trusted.MirSemantics.ReachesResult ∧ RefReachesOutcome ∧\n\
               faultToRefOutcome = encodeProg\n\
             def CorrespondenceAtChoicesClaim : Prop := {corr_choices_def}\n\
             def FaultEquivalenceAtChoicesClaim : Prop := {fault_choices_def}\n\
             def MiriMoveDeinitWiringClaim : Prop := {wiring_def}\n\
             def DecodeProgEncodeProgClaim : Prop := decodeProg = encodeProg\n\
             def EncodeProgTypesCanonicalClaim : Prop := typesAreCanonical = encodeProg\n\
             def EncodeStmtNoDormantNoopsClaim : Prop := encodeStmt = encodeStmt\n\
             def EncodeRvalueBinaryOpIffClaim : Prop := encodeRvalue = encodeOperand\n\
             def EncodeRvalueUnaryOpIffClaim : Prop := encodeRvalue = encodeOperand\n\
             def EncodeStmtAssignIffClaim : Prop :=\n\
               encodeStmt = encodePlace ∧ encodePlace = encodeRvalue\n\
             def StateUniqueOfSimulationInvClaim : Prop := SimulationInv\n\
             def RefStateUniqueOfSimulationInvClaim : Prop := SimulationInv\n\
             def InitRefStateSimClaim : Prop :=\n\
               decodeProg = Trusted.MirSemantics.initState ∧\n\
               initRefState = decodeProg ∧ SimulationInv\n\
             def EvalRefStepEqClaim : Prop :=\n\
               decodeProg = stepResultToRefOutcome ∧ mapStepRes = Trusted.MirSemantics.evalStep ∧\n\
               evalRefStep = evalRefStep\n\
             def SimOfRefStepClaim : Prop :=\n\
               decodeProg = decodeProg ∧ SimulationInv ∧ RefStep ∧ Trusted.MirSemantics.Step\n\
             def SimOfRefReachesClaim : Prop :=\n\
               decodeProg = decodeProg ∧ SimulationInv ∧ RefReaches ∧ Trusted.MirSemantics.Reaches\n\
             def RefWellFormedOfWellFormedClaim : Prop :=\n\
               Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧ encodeProg = encodeProg\n\
             def RefBehaviorOfBehaviorClaim : Prop :=\n\
               Trusted.MirSemantics.Behavior ∧ RefBehavior ∧ encodeProg = encodeProg\n\
             def BehaviorOfRefBehaviorClaim : Prop :=\n\
               RefBehavior ∧ Trusted.MirSemantics.Behavior ∧ encodeProg = encodeProg\n\
             def BehaviorIffRefBehaviorClaim : Prop :=\n\
               Trusted.MirSemantics.Behavior ∧ RefBehavior ∧ encodeProg = encodeProg\n\
             def DivergesIffRefDivergesClaim : Prop :=\n\
               Trusted.MirSemantics.Diverges ∧ RefDiverges ∧ encodeProg = encodeProg\n\
             def CanaryD6UseAfterMoveUbClaim : Prop := {d6_def}\n\
             def CanaryD7aBinopCopyThenMoveOkClaim : Prop :=\n\
               progBinOpCopyThenMoveD7a = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def CanaryD7bBinopMoveThenCopyUbClaim : Prop :=\n\
               progBinOpMoveThenCopyD7b = encodeProg ∧ Trusted.MirSemantics.ReachesResult ∧\n\
               Trusted.MirSemantics.WellFormed ∧ RefReachesOutcome\n\
             def CanaryD7cBinopMoveThenMoveUbClaim : Prop :=\n\
               progBinOpMoveThenMoveD7c = encodeProg ∧ Trusted.MirSemantics.ReachesResult ∧\n\
               Trusted.MirSemantics.WellFormed ∧ RefReachesOutcome\n\
             def CanaryD8SelfMoveOkClaim : Prop :=\n\
               progSelfMoveD8 = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def CanaryD9MoveUnitZstOkClaim : Prop :=\n\
               progMoveUnitZstD9 = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def CanaryD10AddUncheckedOverflowUbClaim : Prop :=\n\
               Trusted.MirSemantics.progAddUncheckedU32 = Trusted.MirSemantics.progAddU32 ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.ReachesResult ∧\n\
               Trusted.MirSemantics.WellFormed ∧ RefReachesOutcome ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefBehavior\n\
             def CanaryD11EnumDiscriminantAndConstOkClaim : Prop :=\n\
               Trusted.MirSemantics.progEnumExplicitReprU8 = Trusted.MirSemantics.progEnumSignedTagIsize ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def CanaryD12ZstEnumMoveAndDiscrOkClaim : Prop :=\n\
               Trusted.MirSemantics.progZstSingleEnumImplicitRet = Trusted.MirSemantics.progZstSingleEnumMoveAndDiscr ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def CanaryD13EnumInvalidTagAndUninitUbClaim : Prop :=\n\
               Trusted.MirSemantics.progEnumInvalidTagConstUb = Trusted.MirSemantics.progEnumUninitDiscrUb ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.ReachesResult ∧\n\
               Trusted.MirSemantics.WellFormed ∧ RefReachesOutcome\n\
             def CanaryD14CharCmpAndSwitchOkClaim : Prop :=\n\
               Trusted.MirSemantics.mkBinOpProg = Trusted.MirSemantics.mkCmpDiscriminantProg ∧\n\
               Trusted.MirAst.BinOp.cmp = Trusted.MirAst.MirTy.char ∧\n\
               Trusted.MirSemantics.progCharSwitch = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def CanaryD15IntToIntCastClaim : Prop :=\n\
               Trusted.MirSemantics.mkIntToIntCastProg = Trusted.MirAst.MirTy.char ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ Trusted.MirSemantics.ReachesResult ∧\n\
               RefWellFormed ∧ RefBehavior ∧ RefReachesOutcome\n\
             def CanaryD16WithOverflowOkClaim : Prop :=\n\
               Trusted.MirSemantics.mkBinOpProg = Trusted.MirSemantics.overflowPairTy ∧\n\
               Trusted.MirAst.BinOp.addWithOverflow = Trusted.MirAst.BinOp.subWithOverflow ∧\n\
               encodeProg = encodeProg ∧ Trusted.MirSemantics.WellFormed ∧\n\
               Trusted.MirSemantics.Behavior ∧ RefWellFormed ∧ RefBehavior\n\
             def RefStepSoundForAllowedStepClaim : Prop := {ref_step_allowed_def}\n\
             def BytesCodecMatchesMiriClaim : Prop :=\n\
               Trusted.MirSemantics.encodeVal = Trusted.MirSemantics.decodeVal ∧\n\
               Trusted.MirSemantics.profileTargetEndian = Miri.Memory.Allocation.writeScalar ∧\n\
               Miri.Memory.Allocation.getBytesUnchecked = Miri.Memory.Allocation.readScalar ∧\n\
               Miri.Memory.Allocation.writeUninit = Miri.Memory.Allocation.writeUninit\n\
             end Trusted.Correspondence\n"
        )
    };
    let all_proofs_src = |corr_choices_proof: &str,
                          fault_choices_proof: &str,
                          wiring_proof: &str,
                          d6_proof: &str,
                          ref_step_allowed_proof: &str| {
        format!(
            "prelude\nimport Trusted.Correspondence\n\
                 namespace Anneal.MirCorrespondenceProof\n\
                 open Trusted.Correspondence\n\
                 theorem correspondence_claim_holds : CorrespondenceClaim :=\n\
                   ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, Eq.refl _⟩\n\
                 theorem fault_equivalence_claim_holds : FaultEquivalenceClaim :=\n\
                   ⟨True.intro, True.intro, Eq.refl _⟩\n\
                 theorem correspondence_at_choices_claim_holds : CorrespondenceAtChoicesClaim :=\n\
                   {corr_choices_proof}\n\
                 theorem fault_equivalence_at_choices_claim_holds : FaultEquivalenceAtChoicesClaim :=\n\
                   {fault_choices_proof}\n\
                 theorem miri_move_deinit_wiring_claim_holds : MiriMoveDeinitWiringClaim :=\n\
                   {wiring_proof}\n\
                 theorem decodeProg_encodeProg : DecodeProgEncodeProgClaim := Eq.refl _\n\
                 theorem encodeProg_types_canonical : EncodeProgTypesCanonicalClaim := Eq.refl _\n\
                 theorem encodeStmt_no_dormant_noops : EncodeStmtNoDormantNoopsClaim := Eq.refl _\n\
                 theorem encodeRvalue_binaryOp_iff : EncodeRvalueBinaryOpIffClaim := Eq.refl _\n\
                 theorem encodeRvalue_unaryOp_iff : EncodeRvalueUnaryOpIffClaim := Eq.refl _\n\
                 theorem encodeStmt_assign_iff : EncodeStmtAssignIffClaim := ⟨Eq.refl _, Eq.refl _⟩\n\
                 theorem state_unique_of_simulationInv : StateUniqueOfSimulationInvClaim := True.intro\n\
                 theorem refState_unique_of_simulationInv : RefStateUniqueOfSimulationInvClaim := True.intro\n\
                 theorem initRefState_sim : InitRefStateSimClaim := ⟨Eq.refl _, Eq.refl _, True.intro⟩\n\
                 theorem evalRefStep_eq : EvalRefStepEqClaim := ⟨Eq.refl _, Eq.refl _, Eq.refl _⟩\n\
                 theorem sim_of_refStep : SimOfRefStepClaim := ⟨Eq.refl _, True.intro, True.intro, True.intro⟩\n\
                 theorem sim_of_refReaches : SimOfRefReachesClaim := ⟨Eq.refl _, True.intro, True.intro, True.intro⟩\n\
                 theorem refWellFormed_of_wellFormed : RefWellFormedOfWellFormedClaim := ⟨True.intro, True.intro, Eq.refl _⟩\n\
                 theorem refBehavior_of_behavior : RefBehaviorOfBehaviorClaim := ⟨True.intro, True.intro, Eq.refl _⟩\n\
                 theorem behavior_of_refBehavior : BehaviorOfRefBehaviorClaim := ⟨True.intro, True.intro, Eq.refl _⟩\n\
                 theorem behavior_iff_refBehavior : BehaviorIffRefBehaviorClaim := ⟨True.intro, True.intro, Eq.refl _⟩\n\
                 theorem diverges_iff_refDiverges : DivergesIffRefDivergesClaim := ⟨True.intro, True.intro, Eq.refl _⟩\n\
                 theorem canary_D6_use_after_move_ub : CanaryD6UseAfterMoveUbClaim := {d6_proof}\n\
                 theorem canary_D7a_binop_copy_then_move_ok : CanaryD7aBinopCopyThenMoveOkClaim :=\n\
                   ⟨Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D7b_binop_move_then_copy_ub : CanaryD7bBinopMoveThenCopyUbClaim :=\n\
                   ⟨Eq.refl _, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D7c_binop_move_then_move_ub : CanaryD7cBinopMoveThenMoveUbClaim :=\n\
                   ⟨Eq.refl _, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D8_self_move_ok : CanaryD8SelfMoveOkClaim :=\n\
                   ⟨Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D9_move_unit_zst_ok : CanaryD9MoveUnitZstOkClaim :=\n\
                   ⟨Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D10_add_unchecked_overflow_ub : CanaryD10AddUncheckedOverflowUbClaim :=\n\
                   ⟨Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D11_enum_discriminant_and_const_ok : CanaryD11EnumDiscriminantAndConstOkClaim :=\n\
                   ⟨Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D12_zst_enum_move_and_discr_ok : CanaryD12ZstEnumMoveAndDiscrOkClaim :=\n\
                   ⟨Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D13_enum_invalid_tag_and_uninit_ub : CanaryD13EnumInvalidTagAndUninitUbClaim :=\n\
                   ⟨Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D14_char_cmp_and_switch_ok : CanaryD14CharCmpAndSwitchOkClaim :=\n\
                   ⟨Eq.refl _, Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D15_int_to_int_cast : CanaryD15IntToIntCastClaim :=\n\
                   ⟨Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro, True.intro, True.intro⟩\n\
                 theorem canary_D16_with_overflow_ok : CanaryD16WithOverflowOkClaim :=\n\
                   ⟨Eq.refl _, Eq.refl _, Eq.refl _, True.intro, True.intro, True.intro, True.intro⟩\n\
                 theorem refStep_sound_for_allowedStep_holds : RefStepSoundForAllowedStepClaim :=\n\
                   {ref_step_allowed_proof}\n\
                 theorem bytes_codec_matches_miri : BytesCodecMatchesMiriClaim :=\n\
                   ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩\n\
                 end Anneal.MirCorrespondenceProof\n"
        )
    };
    let corr_choices_valid_proof = "⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, Eq.refl _⟩";
    let fault_choices_valid_proof = "⟨True.intro, True.intro, Eq.refl _⟩";
    let wiring_valid_proof = "⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩";
    let d6_valid_proof = "⟨Eq.refl _, True.intro, True.intro, True.intro⟩";
    let ref_step_allowed_valid_proof = "⟨True.intro, Eq.refl _⟩";
    let allowed_step_valid_body = "Miri.Interpreter.ExecutionMachine.AllowedStep";

    let corr_deps = [
        "Miri.FakeStubs",
        "Trusted.MirModel",
        "Trusted.MirHelper",
        "Trusted.MirSemantics",
        "Trusted.MirSemantics.SubHelper",
    ];
    let proof_deps = ["Trusted.Correspondence"];

    // 2a-ii. Weakening `CorrespondenceAtChoicesClaim`,
    // `FaultEquivalenceAtChoicesClaim`, `MiriMoveDeinitWiringClaim` (omitting
    // `OperandMachine.evalOperand`), `RefStepSoundForAllowedStepClaim`, or a
    // canary claim (`CanaryD6UseAfterMoveUbClaim := True`) is rejected by
    // `verifyCorrespondenceClaims`.
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src(
            "0",
            "0",
            allowed_step_valid_body,
            Some("True"),
            None,
            None,
            None,
            None,
        ),
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        &all_proofs_src(
            "True.intro",
            fault_choices_valid_proof,
            wiring_valid_proof,
            d6_valid_proof,
            ref_step_allowed_valid_proof,
        ),
    );
    let err_weak_corr_choices = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_weak_corr_choices.code, 1);
    assert_eq!(err_weak_corr_choices.phase, "correspondence-audit");
    assert!(
        err_weak_corr_choices.message.contains(
            "claim Trusted.Correspondence.CorrespondenceAtChoicesClaim body must reference Trusted.MirSemantics.WellFormed"
        ),
        "unexpected weakened CorrespondenceAtChoicesClaim error: {err_weak_corr_choices}"
    );

    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src(
            "0",
            "0",
            allowed_step_valid_body,
            None,
            Some("True"),
            None,
            None,
            None,
        ),
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        &all_proofs_src(
            corr_choices_valid_proof,
            "True.intro",
            wiring_valid_proof,
            d6_valid_proof,
            ref_step_allowed_valid_proof,
        ),
    );
    let err_weak_fault_choices = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_weak_fault_choices.code, 1);
    assert_eq!(err_weak_fault_choices.phase, "correspondence-audit");
    assert!(
        err_weak_fault_choices.message.contains(
            "claim Trusted.Correspondence.FaultEquivalenceAtChoicesClaim body must reference Trusted.MirSemantics.ReachesResultAtChoices"
        ),
        "unexpected weakened FaultEquivalenceAtChoicesClaim error: {err_weak_fault_choices}"
    );

    let wiring_missing_op_machine = "Miri.Interpreter.ExecutionMachine.step = Miri.Interpreter.ExecutionMachine.stepHooks ∧\n\
         Miri.Interpreter.Step.step = Miri.Interpreter.ExecutionMachine.withValidation ∧\n\
         Miri.Interpreter.ExecutionMachine.operandHooks = Miri.Interpreter.evalOperand ∧\n\
         Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit = Miri.Interpreter.MachineHooks.recordPendingMoveDeinit ∧\n\
         Miri.Interpreter.FnArg.copyFnArg = Miri.Interpreter.Call.deinitInPlaceArg";
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src(
            "0",
            "0",
            allowed_step_valid_body,
            None,
            None,
            Some(wiring_missing_op_machine),
            None,
            None,
        ),
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        &all_proofs_src(
            corr_choices_valid_proof,
            fault_choices_valid_proof,
            "⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩",
            d6_valid_proof,
            ref_step_allowed_valid_proof,
        ),
    );
    let err_weak_wiring = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_weak_wiring.code, 1);
    assert_eq!(err_weak_wiring.phase, "correspondence-audit");
    assert!(
        err_weak_wiring.message.contains(
            "claim Trusted.Correspondence.MiriMoveDeinitWiringClaim body must reference Miri.Interpreter.OperandMachine.evalOperand"
        ),
        "unexpected weakened MiriMoveDeinitWiringClaim error: {err_weak_wiring}"
    );

    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src(
            "0",
            "0",
            allowed_step_valid_body,
            None,
            None,
            None,
            Some("True"),
            None,
        ),
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        &all_proofs_src(
            corr_choices_valid_proof,
            fault_choices_valid_proof,
            wiring_valid_proof,
            "True.intro",
            ref_step_allowed_valid_proof,
        ),
    );
    let err_weak_d6 = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_weak_d6.code, 1);
    assert_eq!(err_weak_d6.phase, "correspondence-audit");
    assert!(
        err_weak_d6.message.contains(
            "claim Trusted.Correspondence.CanaryD6UseAfterMoveUbClaim body must reference Trusted.Correspondence.progUseAfterMoveD6"
        ),
        "unexpected weakened-canary error: {err_weak_d6}"
    );

    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src(
            "0",
            "0",
            allowed_step_valid_body,
            None,
            None,
            None,
            None,
            Some("True"),
        ),
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        &all_proofs_src(
            corr_choices_valid_proof,
            fault_choices_valid_proof,
            wiring_valid_proof,
            d6_valid_proof,
            "True.intro",
        ),
    );
    let err_weak_ref_step_allowed = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_weak_ref_step_allowed.code, 1);
    assert_eq!(err_weak_ref_step_allowed.phase, "correspondence-audit");
    assert!(
        err_weak_ref_step_allowed.message.contains(
            "claim Trusted.Correspondence.RefStepSoundForAllowedStepClaim body must reference Trusted.Correspondence.RefStep"
        ),
        "unexpected weakened RefStepSoundForAllowedStepClaim error: {err_weak_ref_step_allowed}"
    );

    // Weakening `BytesCodecMatchesMiriClaim` (dropping the
    // `Trusted.MirSemantics` byte codec it pins against `lean-miri`'s
    // `Allocation` scalar accesses) is rejected by
    // `verifyCorrespondenceClaims`.
    let valid_bytes_codec_def = "def BytesCodecMatchesMiriClaim : Prop :=\n\
               Trusted.MirSemantics.encodeVal = Trusted.MirSemantics.decodeVal ∧\n\
               Trusted.MirSemantics.profileTargetEndian = Miri.Memory.Allocation.writeScalar ∧\n\
               Miri.Memory.Allocation.getBytesUnchecked = Miri.Memory.Allocation.readScalar ∧\n\
               Miri.Memory.Allocation.writeUninit = Miri.Memory.Allocation.writeUninit\n";
    let valid_claims = all_claims_src(
        "0",
        "0",
        allowed_step_valid_body,
        None,
        None,
        None,
        None,
        None,
    );
    assert!(
        valid_claims.contains(valid_bytes_codec_def),
        "synthetic BytesCodecMatchesMiriClaim body drifted"
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &valid_claims.replace(
            valid_bytes_codec_def,
            "def BytesCodecMatchesMiriClaim : Prop :=\n\
               Miri.Memory.Allocation.writeScalar = Miri.Memory.Allocation.readScalar\n",
        ),
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        &all_proofs_src(
            corr_choices_valid_proof,
            fault_choices_valid_proof,
            wiring_valid_proof,
            d6_valid_proof,
            ref_step_allowed_valid_proof,
        )
        .replace(
            "⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩\n\
                 end Anneal.MirCorrespondenceProof",
            "Eq.refl _\n\
                 end Anneal.MirCorrespondenceProof",
        ),
    );
    let err_weak_bytes_codec = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_weak_bytes_codec.code, 1);
    assert_eq!(err_weak_bytes_codec.phase, "correspondence-audit");
    assert!(
        err_weak_bytes_codec.message.contains(
            "claim Trusted.Correspondence.BytesCodecMatchesMiriClaim body must reference Trusted.MirSemantics.encodeVal"
        ),
        "unexpected weakened BytesCodecMatchesMiriClaim error: {err_weak_bytes_codec}"
    );

    // Weakening a `D14`–`D16` canary claim (replacing the pinned `BinOp.cmp`,
    // `IntToInt` cast fixture, or `addWithOverflow` operation with a
    // duplicate of another constant so the synthetic proof still type-checks)
    // is rejected by `verifyCorrespondenceClaims`.
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
    ] {
        assert_eq!(
            valid_claims.matches(valid_conjunct).count(),
            1,
            "synthetic {claim} body drifted"
        );
        compile_forged_module(
            &mut checker_pass2,
            &corr_src,
            &trusted_lib,
            &corr_deps,
            "Trusted.Correspondence",
            &valid_claims.replace(valid_conjunct, weakened_conjunct),
        );
        compile_forged_module(
            &mut checker_pass2,
            &corr_src,
            &corr_lib,
            &proof_deps,
            "Anneal.MirCorrespondenceProof",
            &all_proofs_src(
                corr_choices_valid_proof,
                fault_choices_valid_proof,
                wiring_valid_proof,
                d6_valid_proof,
                ref_step_allowed_valid_proof,
            ),
        );
        let err_weak_canary = run_corr_audit(&mut checker_pass2).unwrap_err();
        assert_eq!(err_weak_canary.code, 1);
        assert_eq!(err_weak_canary.phase, "correspondence-audit");
        assert!(
            err_weak_canary.message.contains(&format!(
                "claim Trusted.Correspondence.{claim} body must reference {dropped}"
            )),
            "unexpected weakened {claim} error: {err_weak_canary}"
        );
    }

    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src(
            "0",
            "0",
            allowed_step_valid_body,
            None,
            None,
            None,
            None,
            None,
        ),
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        &all_proofs_src(
            corr_choices_valid_proof,
            fault_choices_valid_proof,
            wiring_valid_proof,
            d6_valid_proof,
            ref_step_allowed_valid_proof,
        ),
    );
    let err_missing_miri = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_missing_miri.code, 1);
    assert_eq!(err_missing_miri.phase, "correspondence-audit");
    assert!(
        err_missing_miri.message.contains(
            "reference evaluator cone is missing required Miri primitive Miri.Interpreter.ExecutionMachine.step"
        ),
        "unexpected error: {err_missing_miri}"
    );

    let required_miri_primitives = [
        "Miri.Interpreter.ExecutionMachine.step",
        "Miri.Interpreter.ExecutionMachine.withValidation",
        "Miri.Interpreter.ExecutionMachine.stepHooks",
        "Miri.Interpreter.ExecutionMachine.rvalueHooks",
        "Miri.Interpreter.ExecutionMachine.operandHooks",
        "Miri.Interpreter.ExecutionMachine.projectionHooks",
        "Miri.Interpreter.ExecutionMachine.discriminantHooks",
        "Miri.Interpreter.ExecutionMachine.scalarHooks",
        "Miri.Interpreter.Step.step",
        "Miri.Interpreter.Step.evalStatement",
        "Miri.Interpreter.ControlFlow.goToBlock",
        "Miri.Interpreter.ControlFlow.evalTerminator",
        "Miri.Interpreter.ControlFlow.returnFromCurrentFrame",
        "Miri.Interpreter.ExecutionControl.hooks",
        "Miri.Interpreter.MachineHooks.storageLiveDyn",
        "Miri.Interpreter.MachineHooks.storageDead",
        "Miri.Interpreter.OperandMachine.evalOperand",
        "Miri.Interpreter.OperandMachine.evalPlaceToOp",
        "Miri.Interpreter.PlaceMachine.readImmediate",
        "Miri.Interpreter.PlaceMachine.writeMemory",
        "Miri.Interpreter.ValidityVisitor.validatePlace",
        "Miri.Interpreter.ValidityMemory.bind",
        "Miri.Interpreter.evalRvalueIntoPlace",
        "Miri.Interpreter.TerminatorMachine.beforeTerminatorWithChoice",
        "Miri.Interpreter.ScalarOps.binary",
        "Miri.Interpreter.ScalarOps.unary",
        "Miri.Interpreter.IntegerOps.binary",
        "Miri.Interpreter.IntegerOps.binaryBool",
        "Miri.Interpreter.IntegerOps.unary",
        "Miri.Interpreter.IntegerOps.binaryChar",
        "Miri.Interpreter.Cast.cast",
        "Miri.Interpreter.IntegerCast.cast",
        "Miri.Interpreter.Discriminant.readDiscriminant",
        "Miri.Interpreter.Discriminant.discriminantForVariant",
        "Miri.Memory.ScalarInt.truncateFromUInt",
        "Miri.Memory.ScalarInt.tryFromUInt",
        "Miri.Memory.ScalarInt.tryToBool",
        "Miri.Memory.ScalarInt.toChar",
        "Miri.Memory.ScalarInt.ofChar",
    ];
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
        let kept_primitives = required_miri_primitives
            .iter()
            .copied()
            .filter(|prim| *prim != missing_miri)
            .collect::<Vec<_>>()
            .join(", ");
        let body = format!("let _ := ({kept_primitives}); 0");
        compile_forged_module(
            &mut checker_pass2,
            &corr_src,
            &trusted_lib,
            &corr_deps,
            "Trusted.Correspondence",
            &all_claims_src(
                "0",
                &body,
                allowed_step_valid_body,
                None,
                None,
                None,
                None,
                None,
            ),
        );
        compile_forged_module(
            &mut checker_pass2,
            &corr_src,
            &corr_lib,
            &proof_deps,
            "Anneal.MirCorrespondenceProof",
            &all_proofs_src(
                corr_choices_valid_proof,
                fault_choices_valid_proof,
                wiring_valid_proof,
                d6_valid_proof,
                ref_step_allowed_valid_proof,
            ),
        );
        let err_missing_discr = run_corr_audit(&mut checker_pass2).unwrap_err();
        assert_eq!(err_missing_discr.code, 1);
        assert_eq!(err_missing_discr.phase, "correspondence-audit");
        assert!(
            err_missing_discr.message.contains(&format!(
                "reference evaluator cone is missing required Miri primitive {missing_miri}"
            )),
            "unexpected error for {missing_miri}: {err_missing_discr}"
        );
    }

    let all_miri_tuple = required_miri_primitives.join(", ");

    // 2b-ii. `RefAllowedStep` cannot mask an `evalRefStep` that bypasses
    // `Miri.Interpreter.ExecutionMachine.step` (even when `RefAllowedStep`
    // transitively reaches all 39 primitives plus `AllowedStep`).
    let masking_allowed_step =
        format!("let _ := ({all_miri_tuple}, Miri.Interpreter.ExecutionMachine.AllowedStep); 0");
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src(
            "0",
            "0",
            &masking_allowed_step,
            None,
            None,
            None,
            None,
            None,
        ),
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        &all_proofs_src(
            corr_choices_valid_proof,
            fault_choices_valid_proof,
            wiring_valid_proof,
            d6_valid_proof,
            ref_step_allowed_valid_proof,
        ),
    );
    let err_masked_eval = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_masked_eval.code, 1);
    assert_eq!(err_masked_eval.phase, "correspondence-audit");
    assert!(
        err_masked_eval.message.contains(
            "reference evaluator cone is missing required Miri primitive Miri.Interpreter.ExecutionMachine.step"
        ),
        "unexpected RefAllowedStep-masking error: {err_masked_eval}"
    );

    // 2b-iii. `RefAllowedStep` itself must reach
    // `Miri.Interpreter.ExecutionMachine.AllowedStep` even when `evalRefStep`
    // reaches all 39 live primitives.
    let all_miri_step_only = format!("let _ := ({all_miri_tuple}); 0");
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src("0", &all_miri_step_only, "0", None, None, None, None, None),
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        &all_proofs_src(
            corr_choices_valid_proof,
            fault_choices_valid_proof,
            wiring_valid_proof,
            d6_valid_proof,
            ref_step_allowed_valid_proof,
        ),
    );
    let err_missing_allowed_step = run_corr_audit(&mut checker_pass2).unwrap_err();
    assert_eq!(err_missing_allowed_step.code, 1);
    assert_eq!(err_missing_allowed_step.phase, "correspondence-audit");
    assert!(
        err_missing_allowed_step.message.contains(
            "RefAllowedStep cone is missing required Miri primitive Miri.Interpreter.ExecutionMachine.AllowedStep"
        ),
        "unexpected missing AllowedStep error: {err_missing_allowed_step}"
    );

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
        let all_miri_plus_expr = format!("let _ := ({all_miri_tuple}); {step_expr}");
        compile_forged_module(
            &mut checker_pass2,
            &corr_src,
            &trusted_lib,
            &corr_deps,
            "Trusted.Correspondence",
            &all_claims_src(
                init_expr,
                &all_miri_plus_expr,
                allowed_step_valid_body,
                None,
                None,
                None,
                None,
                None,
            ),
        );
        compile_forged_module(
            &mut checker_pass2,
            &corr_src,
            &corr_lib,
            &proof_deps,
            "Anneal.MirCorrespondenceProof",
            &all_proofs_src(
                corr_choices_valid_proof,
                fault_choices_valid_proof,
                wiring_valid_proof,
                d6_valid_proof,
                ref_step_allowed_valid_proof,
            ),
        );
        let err_forbidden_anneal = run_corr_audit(&mut checker_pass2).unwrap_err();
        assert_eq!(err_forbidden_anneal.code, 1);
        assert_eq!(err_forbidden_anneal.phase, "correspondence-audit");
        assert!(
            err_forbidden_anneal.message.contains(&format!(
                "reference evaluator cone illegally references disallowed Trusted declaration {expected_const} (defined in {expected_mod})"
            )),
            "unexpected error for {expected_const}: {err_forbidden_anneal}"
        );
    }

    // Referencing shared boundary data defined in `Trusted.MirModel` (even
    // inside `namespace Trusted.MirSemantics`) is permitted when all required
    // Miri primitives are present and every `Trusted` declaration in the
    // reference evaluator cone comes from an allowlisted module.
    let all_miri_plus_model_data =
        format!("let _ := ({all_miri_tuple}); Trusted.MirSemantics.sharedModelData");
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &corr_deps,
        "Trusted.Correspondence",
        &all_claims_src(
            "0",
            &all_miri_plus_model_data,
            allowed_step_valid_body,
            None,
            None,
            None,
            None,
            None,
        ),
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &corr_lib,
        &proof_deps,
        "Anneal.MirCorrespondenceProof",
        &all_proofs_src(
            corr_choices_valid_proof,
            fault_choices_valid_proof,
            wiring_valid_proof,
            d6_valid_proof,
            ref_step_allowed_valid_proof,
        ),
    );
    run_corr_audit(&mut checker_pass2)
        .expect("Trusted.MirModel boundary data should be admitted in reference evaluator cone");

    // 2c. Module-level import isolation: even a dead
    // `import Trusted.MirSemantics` in `Trusted.Correspondence.Eval` (with zero
    // referenced constants from `Trusted.MirSemantics`) is rejected by
    // `verifyRefEvaluatorIndependence`.
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &["Trusted.MirSemantics"],
        "Trusted.Correspondence.Eval",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Trusted.Correspondence\n\
         def deadImportMarker : Nat := 0\n\
         end Trusted.Correspondence\n",
    );
    let err_dead_import = checker_pass2
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search_paths.clone(),
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.MirModel".to_string(),
                "Trusted.MirHelper".to_string(),
                "Trusted.MirSemantics".to_string(),
                "Trusted.MirSemantics.SubHelper".to_string(),
            ],
            corr_trusted: vec![
                "Trusted.Correspondence.Eval".to_string(),
                "Trusted.Correspondence".to_string(),
            ],
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: vec!["Miri.FakeStubs".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.MirModel".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirHelper".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirSemantics".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirSemantics.SubHelper".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.Correspondence.Eval".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.Correspondence".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_dead_import.code, 1);
    assert_eq!(err_dead_import.phase, "correspondence-audit");
    assert!(
        err_dead_import.message.contains(
            "reference evaluator module Trusted.Correspondence.Eval illegally imports disallowed module Trusted.MirSemantics"
        ),
        "unexpected dead-import error: {err_dead_import}"
    );

    // 2d. Transitive module-level import isolation: even an indirect dead
    // import via an allowlisted intermediate (`Trusted.MirAst.Decoy` ->
    // `Trusted.MirHelper`) is rejected fail-closed.
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &["Trusted.MirHelper"],
        "Trusted.MirAst.Decoy",
        "prelude\nimport Init.Core\nimport Trusted.MirHelper\n\
         namespace Trusted.MirAst\n\
         def decoyMarker : Nat := 0\n\
         end Trusted.MirAst\n",
    );
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &["Trusted.MirAst.Decoy"],
        "Trusted.Correspondence.Eval",
        "prelude\nimport Init.Core\nimport Trusted.MirAst.Decoy\n\
         namespace Trusted.Correspondence\n\
         def transitiveDeadImportMarker : Nat := 0\n\
         end Trusted.Correspondence\n",
    );
    let err_transitive_import = checker_pass2
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search_paths.clone(),
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.MirModel".to_string(),
                "Trusted.MirHelper".to_string(),
                "Trusted.MirAst.Decoy".to_string(),
                "Trusted.MirSemantics".to_string(),
                "Trusted.MirSemantics.SubHelper".to_string(),
            ],
            corr_trusted: vec![
                "Trusted.Correspondence.Eval".to_string(),
                "Trusted.Correspondence".to_string(),
            ],
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: vec!["Miri.FakeStubs".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.MirModel".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirHelper".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirAst.Decoy".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirSemantics".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirSemantics.SubHelper".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.Correspondence.Eval".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.Correspondence".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_transitive_import.code, 1);
    assert_eq!(err_transitive_import.phase, "correspondence-audit");
    assert!(
        err_transitive_import.message.contains(
            "reference evaluator module Trusted.Correspondence.Eval illegally imports disallowed module Trusted.MirHelper (via Trusted.MirAst.Decoy)"
        ),
        "unexpected transitive dead-import error: {err_transitive_import}"
    );

    // 2e. Modular layout placement check: when isolated evaluator submodules
    // are present (`Trusted.Correspondence.Eval`), defining `evalRefStep`
    // outside those isolated submodules (e.g., directly in the umbrella
    // `Trusted.Correspondence`) is rejected fail-closed.
    compile_forged_module(
        &mut checker_pass2,
        &corr_src,
        &trusted_lib,
        &[],
        "Trusted.Correspondence.Eval",
        "prelude\nimport Init.Core\n\
         namespace Trusted.Correspondence\n\
         def cleanEvalMarker : Nat := 0\n\
         end Trusted.Correspondence\n",
    );
    let err_misplaced_eval = checker_pass2
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search_paths.clone(),
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.MirModel".to_string(),
                "Trusted.MirHelper".to_string(),
                "Trusted.MirSemantics".to_string(),
                "Trusted.MirSemantics.SubHelper".to_string(),
            ],
            corr_trusted: vec![
                "Trusted.Correspondence.Eval".to_string(),
                "Trusted.Correspondence".to_string(),
            ],
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: vec!["Miri.FakeStubs".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.MirModel".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirHelper".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirSemantics".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.MirSemantics.SubHelper".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.Correspondence.Eval".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
                (
                    "Trusted.Correspondence".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_misplaced_eval.code, 1);
    assert_eq!(err_misplaced_eval.phase, "correspondence-audit");
    assert!(
        err_misplaced_eval.message.contains(
            "modular correspondence layout requires reference evaluator symbol Trusted.Correspondence.evalRefStep to be defined in an isolated evaluator module, found Trusted.Correspondence"
        ),
        "unexpected misplaced-eval error: {err_misplaced_eval}"
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
    let mut probe = Checker::new(&fix.root, None).unwrap();
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
        err_src_sha.message.contains("staged Miri source SHA-256 mismatch for Miri/Tiny.lean"),
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
    let invalid_sources =
        BTreeMap::from([("Miri/Tiny.lean".to_string(), sha256_bytes(invalid_src.as_bytes()))]);
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
    let mut c6a = Checker::new(&fix.root, None).unwrap();
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
    let mut c6b = Checker::new(&fix.root, None).unwrap();
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
        let mut checker = Checker::new(&fix.root, None).unwrap();
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
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-audit"))
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
        err_sysroot.message.contains("sysroot Init/Std/Lean .olean manifest SHA-256 mismatch"),
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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

    // 3a. `CorrOrigin.edgeViolation?`: vetted -> candidate.
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

    // 3b. `CorrOrigin.edgeViolation?`: vetted -> vendorMiri.
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
            "import Lean\n\
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
    for rel in [
        "trusted/audit/library-lock.json",
        "trusted/lean/Trusted.lean",
        "theory/Anneal/MirWp.lean",
    ] {
        let dst = fix.root.join(rel);
        fs::create_dir_all(dst.parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), dst).unwrap();
    }
    copy_dir_all(
        &checkout.join("trusted/lean/Trusted"),
        &fix.root.join("trusted/lean/Trusted"),
    )
    .unwrap();
    copy_dir_all(
        &checkout.join("theory/Anneal/MirWp"),
        &fix.root.join("theory/Anneal/MirWp"),
    )
    .unwrap();
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
    let canonical_bundle = anneal_audit::bundle::render_bundled_resources(&fix.root).unwrap();
    fs::write(fix.root.join(anneal_audit::bundle::BUNDLE_DESTINATION), canonical_bundle.as_bytes())
        .unwrap();

    let mut checker = Checker::new(&fix.root, None).unwrap();
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
            "import Lean\n\
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
/// `.sysrootFoundation` theorem `Prod.fst_swap` from `Init.Data.Prod`, and an
/// empty `Anneal.MirCorrespondenceProof.olean` whose header imports
/// `Init.Data.Prod`. `Lean.importModules` admits the duplicate theorem and
/// attributes it to `Trusted.Correspondence`, which loads first, so the
/// inventory, origin, and edge checks pass and only the shadow check in
/// `replayCorrAndVendor` rejects it.
#[test]
fn rejects_repository_constant_shadowing_sysroot_declaration() {
    let fix = TempFixture::new(None);
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
            "import Lean\n\
             open Lean\n\
             def main : IO Unit := do\n\
               initSearchPath (System.FilePath.mk {:?})\n\
               let env ← importModules #[{{ module := `Init.Data.Prod }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n\
               let some ci := env.checked.get.find? `Prod.fst_swap \
                 | throw (IO.userError \"missing sysroot theorem Prod.fst_swap\")\n\
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
                 imports := #[{{ module := `Init.Data.Prod }}]\n\
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
            .contains("repository constant Prod.fst_swap shadows vendor/sysroot declaration"),
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
        "import Lean\nnamespace Miri.ImportLean\ndef ok : Nat := 0\nend Miri.ImportLean\n",
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
        })
        .expect("foundation-only preflight parses `throwError` as a plain identifier");

    let run_corr_pf = |chk: &mut Checker, module: &str, path: &Path| {
        chk.inspect(InspectorRequest::CorrespondencePreflight {
            search_path: vec![trusted_lib.clone(), vendor_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.ImportLean".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
        "import Lean\n\
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

    let run_corr_pf = |chk: &mut Checker, module: &str, path: &Path| {
        chk.inspect(InspectorRequest::CorrespondencePreflight {
            search_path: vec![trusted_lib.clone(), theory_lib.clone(), vendor_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            theory: vec!["Anneal".to_string(), "Anneal.DecoyNs".to_string()],
            vendor_miri: vec!["Miri.ScopedExt".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
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
    let miri_src = "import Lean\n\
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
    let mut probe = Checker::new(&fix.root, None).unwrap();
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
        let mut checker = Checker::new(&fix.root, None).unwrap();
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
    let run_pass1_audit = |chk: &mut Checker| {
        chk.inspect(InspectorRequest::Audit {
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.MirAst".to_string(),
                "Trusted.MirSemantics".to_string(),
            ],
            theory: vec!["Anneal.MirWp".to_string()],
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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
            "import Lean\n\
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
    let mut checker1 = Checker::new(&fix.root, None).unwrap();
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
    let mut checker2 = Checker::new(&fix.root, None).unwrap();
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
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

    let mut checker1 = Checker::new(&fix.root, None).unwrap();
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

    let mut checker2 = Checker::new(&fix.root, None).unwrap();
    checker2.set_require_mir_wp(false);
    let err_theory_cycle = checker2.run().unwrap_err();
    assert_eq!(err_theory_cycle.code, 1);
    assert_eq!(err_theory_cycle.phase, "preflight");
    assert!(
        err_theory_cycle.message.contains("Correspondence proof import cycle"),
        "unexpected correspondence-proof cycle error: {err_theory_cycle}"
    );
}

/// Keeps `LOCKED_LEAN_SHA256` synchronized with `foundation-lock.json`
/// `distributions` binary digests.
#[test]
fn locked_lean_sha256_matches_foundation_lock_distributions() {
    let lock_bytes = fs::read(repo_root().join("trusted/lean/foundation-lock.json")).unwrap();
    let lock: Json = serde_json::from_slice(&lock_bytes).unwrap();
    let expected: BTreeSet<String> = lock["distributions"]
        .as_object()
        .unwrap()
        .values()
        .map(|v| v.as_str().unwrap().to_ascii_lowercase())
        .collect();
    let actual: BTreeSet<String> =
        anneal_audit::LOCKED_LEAN_SHA256.iter().map(|s| s.to_ascii_lowercase()).collect();
    assert_eq!(actual, expected);
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
        "import Lean\n\
         namespace Miri.InitHost\n\
         initialize _ : Unit ← do\n\
           IO.FS.writeFile \"{}\" \"pwned\"\n\
           pure ()\n\
         def ok : Nat := 1\n\
         end Miri.InitHost\n",
        host_victim.display()
    );
    fs::write(vendor_dir.join("Miri/InitHost.lean"), &init_host_src).unwrap();

    let mut prebuild = Checker::new(&fix.root, None).unwrap();
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
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
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
    let init_drop_src = "import Lean\n\
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
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            sources: vec![("Trusted.DropTest".to_string(), sample_drop_src)],
        })
        .unwrap_err();
    assert_eq!(
        err_drop.code, 1,
        "expected policy rejection for unexpected file in /work/out: {err_drop}"
    );
    assert!(
        err_drop.message.contains("unexpected file in sandboxed correspondence-preflight output"),
        "unexpected error message: {err_drop}"
    );

    // 3. Pass 2 module compilation (`run_correspondence_with_closure`) runs
    // inside `bwrap`: a vendored `[init]` that stays silent during
    // `"correspondence-preflight"` (where `/work/src/pass2` is absent) and
    // attempts to write to the host checkout during Pass 2 compilation fails
    // inside the sandbox, leaving `compile_host_victim` untouched.
    let compile_host_victim = fix.root.join("pass2-compile-escape-host.txt");
    let init_compile_host_src = format!(
        "import Lean\n\
         namespace Miri.InitCompileHost\n\
         initialize _ : Unit ← do\n\
           if ← System.FilePath.pathExists \"/work/src/pass2\" then\n\
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
    let mut c3 = Checker::new(&fix.root, None).unwrap();
    c3.set_require_mir_wp(false);
    c3.run().unwrap();
    let mut c4 = Checker::new(&fix.root, None).unwrap();
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
    // during Pass 2 compilation, `anneal-audit` rejects it with policy exit
    // code `1` and stages nothing into `lib/`.
    let init_compile_drop_src = "import Lean\n\
        namespace Miri.InitCompileDrop\n\
        initialize _ : Unit ← do\n\
          if ← System.FilePath.pathExists \"/work/src/pass2\" then\n\
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
        err_compile_drop.code, 1,
        "expected policy rejection for unexpected file in Pass 2 /work/out: {err_compile_drop}"
    );
    assert!(
        err_compile_drop.message.contains("unexpected file in sandboxed Pass 2 output"),
        "unexpected error message: {err_compile_drop}"
    );
    assert!(
        !c4.stage().join("lib/Trusted/Correspondence.olean").exists(),
        "rejected Pass 2 output must not be staged into lib/"
    );
}

#[test]
fn precompiled_inspector_cache_keys_on_inspector_source_digest() {
    let mut fix = TempFixture::new(Some(&format!("{HEADER}def ok : Nat := 1\n")));

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
    let fix = TempFixture::new(Some(&format!("{HEADER}def ok : Nat := 1\n")));

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
    // relative `LEAN_PATH="inspector-lib"` succeeds without touching the decoy.
    // Note: `TempFixture` omits `Trusted.MirAst`/`Anneal.MirWp`, so the binary
    // executes `"preflight"`, compiles `Trusted.lean`, and reaches `"audit"`
    // cleanly before `require_mir_wp` checks MIR modules; reaching the
    // `"audit"` phase proves both preflight and audit inspector runs succeeded
    // under the colon-containing `TMPDIR`.
    let lean = default_lean_path();
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-audit"))
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
    // bootstrap `LEAN_PATH="inspector-lib"` from `Lean.searchPathRef` before
    // `importCorrEnv` loads modules, so `inspector-lib/TrustedBoundary.olean`
    // is never visible as an importable module.
    let mut checker = Checker::new(&fix.root, Some(&lean)).unwrap();
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
        .env("LEAN_PATH", "inspector-lib")
        .args([
            "-j1",
            "-M2048",
            "--run",
            checker.stage().join("inspector-lib/Runner.lean").to_str().unwrap(),
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
/// exclusively to `targetAudit`).
#[test]
fn rejects_library_lock_imports_in_repository_audit() {
    let checkout = repo_root();
    let mut fix = TempFixture::new(Some(
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Data.BitVec.Lemmas\n",
    ));
    fs::copy(
        checkout.join("trusted/audit/library-lock.json"),
        fix.root.join("trusted/audit/library-lock.json"),
    )
    .unwrap();
    let err = fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err.message.contains("foreign/missing import Init.Data.BitVec.Lemmas in Trusted"),
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
    let mut checker = Checker::new(&fix.root, None).unwrap();
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "audit", "unexpected phase: {err}");
    assert!(
        err.message.contains("missing required trusted module Trusted.MirAst"),
        "unexpected error: {err}"
    );
}

/// `verify_bundled_resources` accepts the real repository checkout and rejects
/// tampered, deleted, or symlinked `bundled_resources.rs` files, symlinked
/// destination parents, missing or symlinked `BUNDLE_SOURCES` and
/// `PROVENANCE_SOURCES` files and parent directories, and untracked `.lean`
/// files under `correspondence/` or `trusted/correspondence/` with policy exit
/// code `1`. Each symlink fixture points at byte-identical content, so only
/// the regular-file checks can reject it.
#[test]
fn enforces_bundled_resources_parity_and_regular_files() {
    use anneal_audit::{
        bundle::{
            BUNDLE_DESTINATION, BUNDLE_SOURCES, PROVENANCE_SOURCES, render_bundled_resources,
        },
        verify_bundled_resources,
    };

    let checkout = repo_root();
    verify_bundled_resources(&checkout).unwrap();

    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path().join("repo");
    for rel in BUNDLE_SOURCES.iter().chain(PROVENANCE_SOURCES.iter()) {
        let dst = root.join(rel);
        fs::create_dir_all(dst.parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), dst).unwrap();
    }
    let dest = root.join(BUNDLE_DESTINATION);
    fs::create_dir_all(dest.parent().unwrap()).unwrap();
    let canonical = render_bundled_resources(&root).unwrap();
    fs::write(&dest, canonical.as_bytes()).unwrap();
    verify_bundled_resources(&root).unwrap();

    let expect_policy = |needle: &str| {
        let err = verify_bundled_resources(&root).unwrap_err();
        assert_eq!(err.code, 1, "{err}");
        assert_eq!(err.phase, "bundle-manifest", "{err}");
        assert!(err.message.contains(needle), "expected {needle:?}: {err}");
    };

    // 1. Stale/tampered bytes -> policy rejection (code 1).
    fs::write(&dest, format!("{canonical}// tampered\n")).unwrap();
    expect_policy("differs from canonical bundled sources");

    // 2. Missing `bundled_resources.rs` -> policy rejection (code 1).
    fs::remove_file(&dest).unwrap();
    expect_policy("missing bundled_resources.rs");

    // 3. Symlinked `bundled_resources.rs` -> policy rejection (code 1).
    let outside = tmp.path().join("outside.rs");
    fs::write(&outside, canonical.as_bytes()).unwrap();
    symlink(&outside, &dest).unwrap();
    expect_policy("bundle destination must be a regular file");
    fs::remove_file(&dest).unwrap();

    // 4. Symlinked parent directory of `bundled_resources.rs` -> policy
    // rejection (code 1).
    let dest_dir = dest.parent().unwrap().to_path_buf();
    let outside_dest_dir = tmp.path().join("outside-src");
    fs::rename(&dest_dir, &outside_dest_dir).unwrap();
    fs::write(outside_dest_dir.join("bundled_resources.rs"), canonical.as_bytes()).unwrap();
    symlink(&outside_dest_dir, &dest_dir).unwrap();
    expect_policy("bundle parent must be a regular directory");
    fs::remove_file(&dest_dir).unwrap();
    fs::rename(&outside_dest_dir, &dest_dir).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 5. Symlinked `BUNDLE_SOURCES` file -> policy rejection (code 1).
    let source = root.join("theory/Anneal/MirWp.lean");
    let outside_source = tmp.path().join("outside-MirWp.lean");
    fs::rename(&source, &outside_source).unwrap();
    symlink(&outside_source, &source).unwrap();
    expect_policy("bundle source must be a regular file");
    fs::remove_file(&source).unwrap();
    fs::rename(&outside_source, &source).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 6. Symlinked parent directory of a `BUNDLE_SOURCES` file -> policy
    // rejection (code 1).
    let source_dir = root.join("theory/Anneal");
    let outside_source_dir = tmp.path().join("outside-Anneal");
    fs::rename(&source_dir, &outside_source_dir).unwrap();
    symlink(&outside_source_dir, &source_dir).unwrap();
    expect_policy("bundle source parent must be a regular directory");
    fs::remove_file(&source_dir).unwrap();
    fs::rename(&outside_source_dir, &source_dir).unwrap();
    verify_bundled_resources(&root).unwrap();

    // 7. Missing `BUNDLE_SOURCES` file -> policy rejection (code 1).
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

    // 11. Missing `PROVENANCE_SOURCES` file -> policy rejection (code 1).
    fs::remove_file(&prov).unwrap();
    expect_policy(
        "missing canonical bundle source: trusted/correspondence/Trusted/Correspondence.lean",
    );
}

/// `anneal-audit` rejects a checkout from which both
/// `examples/regenerate_bundle.rs` and `src/bundled_resources.rs` were deleted.
/// `verify_bundled_resources` reads its source inventory from
/// `cargo_anneal::bundle`, not from either deleted file, so deleting the
/// generator cannot disable the parity check.
#[test]
fn rejects_dual_deletion_of_bundle_generator_and_output() {
    let checkout = repo_root();
    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();
    fs::remove_file(fix.root.join("trusted/cargo-anneal/examples/regenerate_bundle.rs")).unwrap();
    fs::remove_file(fix.root.join("trusted/cargo-anneal/src/bundled_resources.rs")).unwrap();

    let mut checker = Checker::new(&fix.root, None).unwrap();
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "bundle-manifest", "unexpected phase: {err}");
    assert!(err.message.contains("missing bundled_resources.rs"), "unexpected error: {err}");
    assert!(!checker.execution_began());
}
