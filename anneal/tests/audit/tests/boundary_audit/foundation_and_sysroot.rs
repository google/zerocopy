// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Foundation lock growth, Lean sysroot integrity, unused axioms,
//! alternate foundation theorem proofs, and specification preflight and
//! target-audit admission and namespace isolation.

use super::*;

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

/// Verifies specification preflight and target-audit isolation across preflight
/// (`"headers"`, `"spec-preflight"`) and compiled `.olean` `"target-audit"`:
/// - (a) `%`-elaborator term syntax macros (`default_or_ofNonempty% unsafe`,
///   `value_of%`, `type_of%`, `ensure_expected_type%`, `no_implicit_lambda%`).
/// - (b) `Std.Async.*` / `Std.Http.*` / `Std.Internal` / `Std` imports (both
///   direct `"headers"` and transitive `"target-audit"`), dotted/aliased
///   `open`/`export` (`open Std.Internal (UV.Loop.alive)`,
///   `open Std.Internal renaming UV.Loop.alive -> uvAlive`,
///   `export Std.Internal (UV.Loop.alive)`, `open Std (Async)`,
///   `open Std (Http)`, nested `open Std (Internal)`), and compiled
///   `Spec.olean` `Lean.aliasExtension` export of `opaque` or direct
///   `autoParam` dependency.
/// - (c) Reserved kernel/TCB root namespaces (`Expected`, `Captured`,
///   `SpecPreflight`, `TrustedBoundary`) in both `"spec-preflight"` and
///   compiled `.olean` `"target-audit"`.
#[test]
fn rejects_spec_preflight_and_target_audit_admission_and_namespace_violations() {
    use std::os::unix::fs::PermissionsExt;

    use anneal_audit::{TargetAuditRequest, TargetBindings, TargetModule, TargetRole};

    let checkout = repo_root();
    let helper_fix = TempFixture::new(None);
    let mut helper_chk = helper_fix.checker();
    helper_chk.set_require_mir_wp(false);
    helper_chk.run().unwrap();

    let target_dir = helper_chk.stage().join("spec-audit-target-root");
    for rel in [
        "trusted/audit/TrustedBoundary.lean",
        "trusted/audit/SpecPreflight.lean",
        "trusted/audit/library-lock.json",
        "trusted/lean/foundation-lock.json",
        "trusted/lean/lean-toolchain",
    ] {
        fs::create_dir_all(target_dir.join(rel).parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), target_dir.join(rel)).unwrap();
    }
    fs::create_dir_all(target_dir.join("trusted/lean")).unwrap();
    fs::write(target_dir.join("trusted/lean/Trusted.lean"), HEADER).unwrap();

    let inputs = target_dir.join("inputs");
    fs::create_dir_all(&inputs).unwrap();
    let h = sha256_bytes(b"spec admission regression fixture");

    let model_src = "prelude\nimport Init.Data.BitVec.Basic\n\
         import Init.Data.String.OrderInstances\nnamespace Trusted.MirSemantics\n\
         structure Crate where\n  program : BitVec 8\n  specs : BitVec 8 → Prop\n\
         def UnitTheorem (c : Crate) : Prop := c.program.toNat = 7 ∧ c.specs c.program\n\
         end Trusted.MirSemantics\n\
         namespace Model\n\
         opaque extOpq : Nat\n\
         end Model\n";
    let cap_src = "prelude\nimport Model\ndef Captured.program : BitVec 8 := BitVec.ofNat 8 7\n";
    let spec_ok_src =
        "prelude\nimport Model\ndef Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n";
    let exp_src = "prelude\nimport Captured\nimport Spec\ndef Expected.claim : Prop := \
         Trusted.MirSemantics.UnitTheorem (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n";
    let proof_src = "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n";

    let build_req = |spec_body: &str| {
        let mut modules = Vec::new();
        for (name, role, src) in [
            ("Model", TargetRole::Model, model_src),
            ("Captured", TargetRole::Capture, cap_src),
            ("Spec", TargetRole::Specification, spec_body),
            ("Expected", TargetRole::Expected, exp_src),
            ("Proof", TargetRole::Proof, proof_src),
        ] {
            let p = inputs.join(format!("{name}.lean"));
            fs::write(&p, src).unwrap();
            modules.push(TargetModule {
                module: name.into(),
                source: p,
                expected_sha256: sha256_bytes(src.as_bytes()),
                role,
            });
        }
        TargetAuditRequest {
            modules,
            theorem_module: "Proof".into(),
            theorem_name: "Proof.verify".into(),
            expected_module: "Expected".into(),
            expected_declaration: "Expected.claim".into(),
            canonical_root: "Trusted.MirSemantics.UnitTheorem".into(),
            subject_declaration: "Captured.program".into(),
            specification_declaration: "Spec.specs".into(),
            allow_sorry_in_proof: false,
            bindings: TargetBindings {
                request_sha256: h.clone(),
                capture_sha256: h.clone(),
                model_manifest_sha256: h.clone(),
                specification_manifest_sha256: h.clone(),
            },
        }
    };

    // 1. Positive control: valid target with `Captured` in `.capture` and
    //    `Expected` in `.expected` succeeds cleanly.
    let base_req = build_req(spec_ok_src);
    let checker_env = helper_fix.inner.checker_env().unwrap();
    let mut tgt_chk =
        cargo_anneal::Checker::new_with_env(&target_dir, None, checker_env.clone()).unwrap();
    tgt_chk.run_target(&base_req).unwrap();

    // 2. `"headers"` and `"spec-preflight"` negative checks for term-macro,
    //    library-import, scoped `open`/`export`, and reserved-namespace rules.
    let preflight_cases = [
        (
            "import_std_async_dns",
            "headers",
            "disallowed sysroot import Std.Async.DNS",
            "prelude\nimport Model\nimport Std.Async.DNS\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "import_std_async",
            "headers",
            "disallowed sysroot import Std.Async",
            "prelude\nimport Model\nimport Std.Async\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "import_std_http",
            "headers",
            "disallowed sysroot import Std.Http",
            "prelude\nimport Model\nimport Std.Http\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "import_std_internal",
            "headers",
            "disallowed sysroot import Std.Internal",
            "prelude\nimport Model\nimport Std.Internal\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "import_std",
            "headers",
            "disallowed sysroot import Std",
            "prelude\nimport Model\nimport Std\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "pct_default_or_ofNonempty",
            "spec-preflight",
            "disallowed syntax Lean.Parser.Term.defaultOrOfNonempty",
            "prelude\nimport Model\n\
             def Spec.specs (_p : BitVec 8) : Prop := (default_or_ofNonempty% unsafe : Nat) = 0\n",
        ),
        (
            "pct_value_of",
            "spec-preflight",
            "disallowed syntax Lean.Parser.Term.valueOf",
            "prelude\nimport Model\n\
             def Spec.helper : Nat := 0\n\
             def Spec.specs (_p : BitVec 8) : Prop := value_of% Spec.helper = 0\n",
        ),
        (
            "pct_type_of",
            "spec-preflight",
            "disallowed syntax Lean.Parser.Term.typeOf",
            "prelude\nimport Model\n\
             def Spec.helper : Nat := 0\n\
             def Spec.specs (_p : BitVec 8) : Prop := type_of% Spec.helper = Nat\n",
        ),
        (
            "pct_ensure_expected_type",
            "spec-preflight",
            "disallowed syntax Lean.Parser.Term.ensureExpectedType",
            "prelude\nimport Model\n\
             def Spec.specs (_p : BitVec 8) : Prop := ensure_expected_type% \"ctx\" True\n",
        ),
        (
            "pct_no_implicit_lambda",
            "spec-preflight",
            "disallowed syntax Lean.Parser.Term.noImplicitLambda",
            "prelude\nimport Model\n\
             def Spec.specs (_p : BitVec 8) : Prop := no_implicit_lambda% True\n",
        ),
        (
            "open_only_uv",
            "spec-preflight",
            "disallowed open item Std.Internal.UV.Loop.alive",
            "prelude\nimport Model\n\
             open Std.Internal (UV.Loop.alive)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "open_renaming_uv",
            "spec-preflight",
            "disallowed open item Std.Internal.UV.Loop.alive",
            "prelude\nimport Model\n\
             open Std.Internal renaming UV.Loop.alive -> uvAlive\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "export_uv",
            "spec-preflight",
            "disallowed export item Std.Internal.UV.Loop.alive",
            "prelude\nimport Model\n\
             export Std.Internal (UV.Loop.alive)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "open_std_async",
            "spec-preflight",
            "disallowed open item Std.Async",
            "prelude\nimport Model\n\
             open Std (Async)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "open_std_http",
            "spec-preflight",
            "disallowed open item Std.Http",
            "prelude\nimport Model\n\
             open Std (Http)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "open_std_internal_chained_uv",
            "spec-preflight",
            "disallowed open item Std.Internal.UV.Loop.alive",
            "prelude\nimport Model\n\
             open Std renaming Internal -> IntNs\n\
             open IntNs (UV.Loop.alive)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "open_renaming_chained_export_uv",
            "spec-preflight",
            "disallowed export item Std.Internal.UV.Loop.alive",
            "prelude\nimport Model\n\
             open Std renaming Internal -> IntNs\n\
             export IntNs (UV.Loop.alive)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "open_only_chained_scoped_tactic",
            "spec-preflight",
            "unsupported tactic",
            "prelude\nimport Model\nimport Init.Data.String.OrderInstances\n\
             open String (Internal)\n\
             open Internal\n\
             theorem Spec.t : True := by order\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "export_chained_scoped_tactic",
            "spec-preflight",
            "unsupported tactic",
            "prelude\nimport Model\nimport Init.Data.String.OrderInstances\n\
             export String (Internal)\n\
             open Internal\n\
             theorem Spec.t : True := by order\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "in_open_renaming_chained_open_uv",
            "spec-preflight",
            "disallowed open item Std.Internal.UV.Loop.alive",
            "prelude\nimport Model\n\
             open Std renaming Internal -> IntNs in\n\
             open IntNs (UV.Loop.alive) in\n\
             def Spec.bad : Nat := 0\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "mutual_open_renaming_chained_export_uv",
            "spec-preflight",
            "disallowed export item Std.Internal.UV.Loop.alive",
            "prelude\nimport Model\n\
             mutual\n\
             open Std renaming Internal -> IntNs\n\
             export IntNs (UV.Loop.alive)\n\
             end\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "open_renaming_alias_expected",
            "spec-preflight",
            "cannot open renaming alias reserved namespace Expected",
            "prelude\nimport Model\nnamespace Safe\ndef fakePred : Prop := True\nend Safe\n\
             open Safe renaming fakePred -> Expected.claim\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "open_renaming_alias_trusted",
            "spec-preflight",
            "cannot open renaming alias reserved namespace Trusted",
            "prelude\nimport Model\nnamespace Safe\ndef fakePred : Prop := True\nend Safe\n\
             open Safe renaming fakePred -> Trusted.MirSemantics.UnitTheorem\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "open_renaming_alias_opt_param",
            "spec-preflight",
            "disallowed open renaming alias optParam",
            "prelude\nimport Model\nnamespace Safe\ndef ok : Nat := 0\nend Safe\n\
             open Safe renaming ok -> optParam\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "open_renaming_alias_lean",
            "spec-preflight",
            "cannot open renaming alias forbidden namespace Lean",
            "prelude\nimport Model\nnamespace Safe\ndef ok : Nat := 0\nend Safe\n\
             open Safe renaming ok -> Lean.Parser.fake\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "ns_expected",
            "spec-preflight",
            "cannot enter reserved namespace Expected",
            "prelude\nimport Model\nnamespace Expected\ndef bad : Nat := 0\nend Expected\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "ns_captured",
            "spec-preflight",
            "cannot enter reserved namespace Captured",
            "prelude\nimport Model\nnamespace Captured\ndef bad : Nat := 0\nend Captured\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "ns_spec_preflight",
            "spec-preflight",
            "cannot enter reserved namespace SpecPreflight",
            "prelude\nimport Model\nnamespace SpecPreflight\ndef bad : Nat := 0\nend SpecPreflight\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "ns_trusted_boundary",
            "spec-preflight",
            "cannot enter reserved namespace TrustedBoundary",
            "prelude\nimport Model\nnamespace TrustedBoundary\ndef bad : Nat := 0\nend TrustedBoundary\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "decl_root_expected",
            "spec-preflight",
            "reserved namespace",
            "prelude\nimport Model\ndef Expected.bad : Nat := 0\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "decl_root_captured",
            "spec-preflight",
            "reserved namespace",
            "prelude\nimport Model\ndef Captured.bad : Nat := 0\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "export_alias_expected",
            "spec-preflight",
            "cannot export alias reserved namespace Expected",
            "prelude\nimport Model\nnamespace Safe.Expected\ndef claim : Prop := True\nend Safe.Expected\n\
             export Safe (Expected.claim)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "export_alias_trusted",
            "spec-preflight",
            "cannot export alias reserved namespace Trusted",
            "prelude\nimport Model\nnamespace Safe.Trusted\ndef fake : Nat := 0\nend Safe.Trusted\n\
             export Safe (Trusted.fake)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "export_alias_io",
            "spec-preflight",
            "cannot export alias forbidden namespace IO",
            "prelude\nimport Model\nnamespace Safe.IO\ndef println : Nat := 0\nend Safe.IO\n\
             export Safe (IO.println)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
        (
            "export_alias_opt_param",
            "spec-preflight",
            "disallowed export alias optParam",
            "prelude\nimport Model\nexport Model (optParam)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        ),
    ];
    // Exercise the full `run_target` pipeline end-to-end on representative
    // `"headers"` and `"spec-preflight"` rejections, then run the full
    // `preflight_cases` matrix directly on the already-admitted `tgt_chk` so
    // the test stays fast under CI's nextest timeout.
    for (label, expected_phase, expected_msg, spec_body) in [preflight_cases[0], preflight_cases[5]]
    {
        let req = build_req(spec_body);
        let mut chk =
            cargo_anneal::Checker::new_with_env(&target_dir, None, checker_env.clone()).unwrap();
        let err = chk.run_target(&req).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, expected_phase), "e2e {label}: {err}");
        assert!(err.message.contains(expected_msg), "e2e {label}: {err}");
    }

    let tstage = tgt_chk.stage().to_path_buf();
    let spec_pf_dir = tstage.join("src/spec-pf");
    fs::create_dir_all(&spec_pf_dir).unwrap();
    for (label, expected_phase, expected_msg, spec_body) in preflight_cases {
        let p = spec_pf_dir.join(format!("{label}.lean"));
        fs::write(&p, spec_body).unwrap();
        let err = if expected_phase == "headers" {
            tgt_chk.inspect_headers(&[("Spec".into(), p)]).unwrap_err()
        } else {
            tgt_chk.inspect_spec_preflight(&[("Spec".into(), p)]).unwrap_err()
        };
        assert_eq!((err.code, err.phase.as_str()), (1, expected_phase), "{label}: {err}");
        assert!(err.message.contains(expected_msg), "{label}: {err}");
    }

    // 3. Compiled `.olean` `"target-audit"` checks (direct `.olean` audit via
    //    `tgt_chk.inspect_target` with forged `Spec.olean` artifacts).
    let spec_olean = tstage.join("lib/Spec.olean");
    let clean_spec = tstage.join("CleanSpec.olean");
    fs::copy(&spec_olean, &clean_spec).unwrap();
    let forged_src = tstage.join("src/spec-forged");
    let forged_lib = tstage.join("forged-lib");
    fs::create_dir_all(&forged_lib).unwrap();
    let tstage_lib = tstage.join("lib");

    let lean_path_joined = env::join_paths([&tstage_lib, &forged_lib]).unwrap();
    let mut compile_forged_target = |mod_name: &str, body: &str, out_path: &Path| {
        let rel = mod_name.replace('.', "/");
        let s_path = forged_src.join(format!("{rel}.lean"));
        fs::create_dir_all(s_path.parent().unwrap()).unwrap();
        fs::create_dir_all(out_path.parent().unwrap()).unwrap();
        fs::write(&s_path, body).unwrap();
        helper_chk
            .process_with_path(
                &format!("compile-spec-{mod_name}"),
                &[
                    "-j1".to_string(),
                    "-M2048".to_string(),
                    "-t0".to_string(),
                    "-R".to_string(),
                    forged_src.to_string_lossy().into_owned(),
                    "-o".to_string(),
                    out_path.to_string_lossy().into_owned(),
                    s_path.to_string_lossy().into_owned(),
                ],
                Some(lean_path_joined.as_os_str()),
            )
            .unwrap();
    };

    let swap_spec_artifact = |chk: &mut cargo_anneal::Checker, src_olean: &Path| {
        #[cfg(unix)]
        if spec_olean.exists() {
            let _ = fs::set_permissions(&spec_olean, fs::Permissions::from_mode(0o600));
        }
        fs::copy(src_olean, &spec_olean).unwrap();
        let avail = BTreeMap::from([("olean", spec_olean.to_string_lossy().into_owned())]);
        let arts = ModuleArtifacts::from_available(&avail, "test", String::new).unwrap();
        chk.admitted_mut().unwrap().artifacts.insert("Spec".into(), arts);
    };

    // 3a. Forged `Spec.olean` reserving `Expected`, `Captured`,
    //     `SpecPreflight`, or `TrustedBoundary`, exporting `Model.extOpq` via
    //     `aliasExtension`, or referencing `autoParam` directly.
    for (label, body, expected_msg) in [
        (
            "ta_spec_reserved_expected",
            "prelude\nimport Model\n\
             def Expected.badDecl : Nat := 0\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "cannot declare constant Expected.badDecl",
        ),
        (
            "ta_spec_reserved_captured",
            "prelude\nimport Model\n\
             def Captured.badDecl : Nat := 0\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "cannot declare constant Captured.badDecl",
        ),
        (
            "ta_spec_reserved_spec_preflight",
            "prelude\nimport Model\n\
             def SpecPreflight.badDecl : Nat := 0\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "cannot declare constant SpecPreflight.badDecl",
        ),
        (
            "ta_spec_reserved_trusted_boundary",
            "prelude\nimport Model\n\
             def TrustedBoundary.badDecl : Nat := 0\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "cannot declare constant TrustedBoundary.badDecl",
        ),
        (
            "ta_spec_export_opaque_alias",
            "prelude\nimport Model\n\
             export Model (extOpq)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "references opaque declaration Model.extOpq",
        ),
    ] {
        let forged_out = forged_lib.join(format!("{label}_Spec.olean"));
        compile_forged_target("Spec", body, &forged_out);
        swap_spec_artifact(&mut tgt_chk, &forged_out);
        let err = tgt_chk.inspect_target(&base_req).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{label}: {err}");
        assert!(err.message.contains(expected_msg), "{label}: {err}");
        swap_spec_artifact(&mut tgt_chk, &clean_spec);
    }

    // 3b. Forged transitive `Std.Async.Fake` library admitted into
    //     `target-audit` with a `Spec.olean` importing it. Place
    //     `Std/Async/Fake.olean` inside `tstage_lib` so the sandbox mounts it
    //     cleanly.
    let async_fake_olean = tstage_lib.join("Std/Async/Fake.olean");
    compile_forged_target(
        "Std.Async.Fake",
        "prelude\nimport Init.Core\ndef Std.Async.Fake.x : Nat := 0\n",
        &async_fake_olean,
    );
    let async_spec_olean = forged_lib.join("ta_async_Spec.olean");
    compile_forged_target(
        "Spec",
        "prelude\nimport Model\nimport Std.Async.Fake\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        &async_spec_olean,
    );
    let orig_spec_graph = tgt_chk.admitted().unwrap().graph["Spec"].clone();
    {
        let async_avail =
            BTreeMap::from([("olean", async_fake_olean.to_string_lossy().into_owned())]);
        let async_arts =
            ModuleArtifacts::from_available(&async_avail, "test", String::new).unwrap();
        let adm = tgt_chk.admitted_mut().unwrap();
        adm.library_modules.insert("Std.Async.Fake".into());
        adm.artifacts.insert("Std.Async.Fake".into(), async_arts);
        adm.graph.insert(
            "Std.Async.Fake".into(),
            vec![ImportEdge {
                module: "Init.Core".into(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            }],
        );
        adm.graph.insert(
            "Spec".into(),
            vec![
                ImportEdge {
                    module: "Model".into(),
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                },
                ImportEdge {
                    module: "Std.Async.Fake".into(),
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                },
            ],
        );
    }
    swap_spec_artifact(&mut tgt_chk, &async_spec_olean);
    let err_async = tgt_chk.inspect_target(&base_req).unwrap_err();
    assert_eq!((err_async.code, err_async.phase.as_str()), (1, "target-audit"), "{err_async}");
    assert!(
        err_async.message.contains("disallowed transitive sysroot import Std.Async.Fake in target"),
        "{err_async}"
    );
    {
        let adm = tgt_chk.admitted_mut().unwrap();
        adm.graph.insert("Spec".into(), orig_spec_graph.clone());
        adm.library_modules.remove("Std.Async.Fake");
        adm.artifacts.remove("Std.Async.Fake");
        adm.graph.remove("Std.Async.Fake");
    }
    swap_spec_artifact(&mut tgt_chk, &clean_spec);

    // 3c. Exercise every remaining `targetAudit` `Lean.aliasExtension` branch
    //     plus pure `autoParam` references and allowlisted `.foundation`
    //     exports (`System.Platform.getNumBits`, `Nat.add`).
    let override_lib_olean = tstage_lib.join("Std/TestOverrideLib.olean");
    compile_forged_target(
        "Std.TestOverrideLib",
        "prelude\nimport Init.Core\n\
         namespace Std.TestOverrideLib\n\
         @[extern \"anneal_test_ext\"] def extFn : Nat := 0\n\
         def implTarget : Nat := 1\n\
         @[implemented_by implTarget] def implFn : Nat := 0\n\
         unsafe def unsafeFn : Nat := 0\n\
         partial def partialFn (n : Nat) : Nat := partialFn n\n\
         axiom unapprovedAx : Prop\n\
         def autoHelper (_h : 0 = 0 := by rfl) : Nat := 0\n\
         def bangHelper! : Nat := 0\n\
         def okDef : Nat := 0\n\
         end Std.TestOverrideLib\n",
        &override_lib_olean,
    );
    {
        let lib_avail =
            BTreeMap::from([("olean", override_lib_olean.to_string_lossy().into_owned())]);
        let lib_arts = ModuleArtifacts::from_available(&lib_avail, "test", String::new).unwrap();
        let adm = tgt_chk.admitted_mut().unwrap();
        adm.library_modules.insert("Std.TestOverrideLib".into());
        adm.artifacts.insert("Std.TestOverrideLib".into(), lib_arts);
        adm.graph.insert(
            "Std.TestOverrideLib".into(),
            vec![ImportEdge {
                module: "Init.Core".into(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            }],
        );
        adm.graph.insert(
            "Spec".into(),
            vec![
                ImportEdge {
                    module: "Model".into(),
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                },
                ImportEdge {
                    module: "Std.TestOverrideLib".into(),
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                },
            ],
        );
    }
    // Positive control: allowlisted `.foundation` exports (`Nat.add` and
    // `System.Platform.getNumBits`) pass `target-audit`.
    let ok_foundation_export_spec = forged_lib.join("ta_spec_export_foundation_ok_Spec.olean");
    compile_forged_target(
        "Spec",
        "prelude\nimport Model\nimport Std.TestOverrideLib\n\
         namespace MySpec\nexport System.Platform (getNumBits)\nexport Nat (add)\nend MySpec\n\
         def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
        &ok_foundation_export_spec,
    );
    swap_spec_artifact(&mut tgt_chk, &ok_foundation_export_spec);
    tgt_chk
        .inspect_target(&base_req)
        .expect("allowlisted foundation exports must pass target-audit");
    swap_spec_artifact(&mut tgt_chk, &clean_spec);

    for (label, body, expected_msg) in [
        (
            "ta_spec_export_extern_alias",
            "prelude\nimport Model\nimport Std.TestOverrideLib\n\
             export Std.TestOverrideLib (extFn)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "references compiler override declaration Std.TestOverrideLib.extFn",
        ),
        (
            "ta_spec_export_impl_by_alias",
            "prelude\nimport Model\nimport Std.TestOverrideLib\n\
             export Std.TestOverrideLib (implFn)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "references compiler override declaration Std.TestOverrideLib.implFn",
        ),
        (
            "ta_spec_export_unsafe_alias",
            "prelude\nimport Model\nimport Std.TestOverrideLib\n\
             export Std.TestOverrideLib (unsafeFn)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "references unsafe declaration Std.TestOverrideLib.unsafeFn",
        ),
        (
            "ta_spec_export_axiom_alias",
            "prelude\nimport Model\nimport Std.TestOverrideLib\n\
             export Std.TestOverrideLib (unapprovedAx)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "references unapproved axiom Std.TestOverrideLib.unapprovedAx",
        ),
        (
            "ta_spec_autoparam_ref",
            "prelude\nimport Model\nimport Std.TestOverrideLib\n\
             def Spec.useAuto := @Std.TestOverrideLib.autoHelper\n\
             def Spec.specs (p : BitVec 8) : Prop :=\n  \
               let _ := @Spec.useAuto\n  BitVec.and p p = p\n",
            "cannot reference autoParam",
        ),
        (
            "ta_spec_export_bad_alias_name",
            "prelude\nimport Model\nimport Std.TestOverrideLib\n\
             namespace MyHelperNs\ndef optParam : Nat := 0\nend MyHelperNs\n\
             export MyHelperNs (optParam)\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "specification module Spec cannot export alias optParam",
        ),
        (
            "ta_spec_export_trusted_root_alias",
            "prelude\nimport Model\nimport Std.TestOverrideLib\n\
             namespace Trusted\nexport Std.TestOverrideLib (okDef)\nend Trusted\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "cannot export alias Trusted.okDef in Trusted namespace",
        ),
        (
            "ta_spec_export_reserved_root_alias",
            "prelude\nimport Model\nimport Std.TestOverrideLib\n\
             namespace Expected\nexport Std.TestOverrideLib (okDef)\nend Expected\n\
             def Spec.specs (p : BitVec 8) : Prop := BitVec.and p p = p\n",
            "cannot export alias Expected.okDef in reserved kernel namespace Expected",
        ),
    ] {
        let forged_out = forged_lib.join(format!("{label}_Spec.olean"));
        compile_forged_target("Spec", body, &forged_out);
        swap_spec_artifact(&mut tgt_chk, &forged_out);
        let err = tgt_chk.inspect_target(&base_req).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{label}: {err}");
        assert!(err.message.contains(expected_msg), "{label}: {err}");
    }

    for (label, alias_pair, expected_msg) in [
        (
            "ta_spec_export_partial_alias",
            "(`MySpec.cleanPartial, `Std.TestOverrideLib.partialFn._unsafe_rec)",
            "references partial declaration Std.TestOverrideLib.partialFn._unsafe_rec",
        ),
        (
            "ta_spec_export_forbidden_alias",
            "(`MySpec.cleanForbidden, `Std.TestOverrideLib.bangHelper!)",
            "references disallowed declaration Std.TestOverrideLib.bangHelper!",
        ),
    ] {
        let forged_out = forged_lib.join(format!("{label}_Spec.olean"));
        fs::copy(&ok_foundation_export_spec, &forged_out).unwrap();
        let patch_script = forged_src.join(format!("{label}.lean"));
        fs::write(
            &patch_script,
            format!(
                "import Lean\nopen Lean in\ndef main : IO Unit := do\n  \
                   let p := System.FilePath.mk {:?}\n  \
                   let (data, _) ← readModuleData p\n  \
                   let e : Array EnvExtensionEntry := unsafe unsafeCast \
                     (#[{alias_pair}] : Array (Name × Name))\n  \
                   saveModuleData p `Spec \
                     {{ data with entries := data.entries.push (Lean.aliasExtension.name, e) }}\n",
                forged_out.to_string_lossy()
            ),
        )
        .unwrap();
        helper_chk
            .process(
                label,
                &["-j1".into(), "-M2048".into(), "--run".into(), patch_script.to_string_lossy().into()],
            )
            .unwrap();
        swap_spec_artifact(&mut tgt_chk, &forged_out);
        let err = tgt_chk.inspect_target(&base_req).unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "target-audit"), "{label}: {err}");
        assert!(err.message.contains(expected_msg), "{label}: {err}");
    }
    {
        let adm = tgt_chk.admitted_mut().unwrap();
        adm.graph.insert("Spec".into(), orig_spec_graph);
        adm.library_modules.remove("Std.TestOverrideLib");
        adm.artifacts.remove("Std.TestOverrideLib");
        adm.graph.remove("Std.TestOverrideLib");
    }
    swap_spec_artifact(&mut tgt_chk, &clean_spec);
}
