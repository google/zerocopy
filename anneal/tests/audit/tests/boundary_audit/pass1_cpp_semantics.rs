// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pass 1 replay, trust tiers, and root reachability of the C11 and C++20
//! operational semantics (`Trusted.CppAst`, `Trusted.CppSemantics`) and their
//! untrusted proof theory (`Anneal.CppEquiv`).

use super::*;

/// The `candidate:refinement` modules defining the C11 and C++20 AST and
/// operational semantics.
const CPP_TRUSTED_MODULES: [&str; 6] = [
    "Trusted.CppAst",
    "Trusted.CppSemantics",
    "Trusted.CppSemantics.Eval",
    "Trusted.CppSemantics.Memory",
    "Trusted.CppSemantics.State",
    "Trusted.CppSemantics.Step",
];

/// Maps a `Trusted.*` or `Anneal.*` module name to its repository-relative
/// source path; returns `None` for toolchain modules such as `Init.*`.
fn repo_module_path(module: &str) -> Option<String> {
    let rel = module.replace('.', "/");
    if module == "Trusted" || module.starts_with("Trusted.") {
        Some(format!("trusted/lean/{rel}.lean"))
    } else if module.starts_with("Anneal.") {
        Some(format!("theory/{rel}.lean"))
    } else {
        None
    }
}

/// Returns the modules named by the `import` commands in the header of
/// `source` (the header ends at the first non-blank, non-comment line that is
/// not a `module`, `prelude`, or `import` command).
fn header_imports(source: &str) -> Vec<String> {
    let mut imports = Vec::new();
    for line in source.lines().map(str::trim) {
        if line.is_empty() || line.starts_with("--") || line == "module" || line == "prelude" {
            continue;
        }
        match line.strip_prefix("public import ").or_else(|| line.strip_prefix("import ")) {
            Some(target) => imports.push(target.trim().to_string()),
            None => break,
        }
    }
    imports
}

/// Copies the transitive `Trusted.*` / `Anneal.*` import closure of `roots`
/// from `checkout` into `dst`, preserving repository-relative paths.
fn copy_import_closure(checkout: &Path, dst: &Path, roots: &[&str]) -> BTreeSet<String> {
    let mut seen = BTreeSet::new();
    let mut queue: VecDeque<String> = roots.iter().map(|r| r.to_string()).collect();
    while let Some(module) = queue.pop_front() {
        let Some(rel) = repo_module_path(&module) else { continue };
        if !seen.insert(module.clone()) {
            continue;
        }
        let src = fs::read_to_string(checkout.join(&rel))
            .unwrap_or_else(|e| panic!("read {rel} for {module}: {e}"));
        let out = dst.join(&rel);
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        fs::write(&out, &src).unwrap();
        queue.extend(header_imports(&src));
    }
    seen
}

/// Verifies that the six `Trusted.Cpp*` modules (`candidate:refinement`)
/// compile, pass `"preflight"` and Pass-1 kernel replay onto
/// `foundation-lock.json` together with their untrusted `Anneal.CppEquiv`
/// proofs, emit no `partial` / `._unsafe_rec` constants, keep every
/// declaration mechanically reachable from the planned model-pinned root
/// `Trusted.CppSemantics.CppEnvelopeTheorem`, and remain isolated from
/// `vetted` modules.
#[test]
fn trusted_cpp_semantics_pass1_replay_reachability_and_vetted_isolation() {
    let checkout = repo_root();
    let mut fix = TempFixture::new(Some(HEADER));
    // `Anneal.PureLift.CppBridge` is left out: it imports `Trusted.MirModel`,
    // and loading any MIR module makes the checker require the whole MIR
    // weakest-precondition stack. The repository `anneal-audit` run replays
    // it.
    let copied =
        copy_import_closure(&checkout, &fix.root, &["Trusted.CppSemantics", "Anneal.CppEquiv"]);
    for module in CPP_TRUSTED_MODULES {
        assert!(copied.contains(module), "fixture closure is missing {module}: {copied:?}");
    }
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    let report = checker.run().unwrap();
    assert_eq!(report["replay"], json!(true), "{report}");
    for ax in report["axioms"].as_array().unwrap() {
        let ax = ax.as_str().unwrap();
        assert!(
            ax != "sorryAx" && !ax.starts_with("Trusted.") && !ax.starts_with("Anneal."),
            "unexpected axiom {ax} in Trusted.CppSemantics closure: {report}"
        );
    }

    // Every declaration of the six modules carries the module's
    // `candidate:refinement` tier.
    let decls = report["declarations"].as_array().unwrap();
    let cpp_decls: BTreeSet<&str> = decls
        .iter()
        .filter(|d| CPP_TRUSTED_MODULES.iter().any(|m| d["module"] == json!(m)))
        .map(|d| {
            assert_eq!(d["trustStatus"], json!("candidate:refinement"), "{d}");
            d["name"].as_str().unwrap()
        })
        .collect();
    for expected in [
        "Trusted.CppAst.CppProgram",
        "Trusted.CppAst.CppProjElem.bitfield",
        "Trusted.CppAst.CppExpr.bitCast",
        "Trusted.CppAst.CppStmt.zeroInit",
        "Trusted.CppSemantics.evalStep",
        "Trusted.CppSemantics.CppProfileRung0",
        "Trusted.CppSemantics.CppEnvelopeTheorem",
    ] {
        assert!(cpp_decls.contains(expected), "missing {expected} in {cpp_decls:?}");
    }

    // Zero dead code: every `Trusted.Cpp*` declaration must be reachable over
    // `anneal-audit` inventory `dependencies` from the planned root. A
    // Lean-generated auxiliary (a constructor, or a name whose last component
    // is a generated suffix such as `rec`, `injEq`, or `_sunfold`) counts as
    // reachable when the declaration it was generated for is reachable.
    let deps: BTreeMap<&str, Vec<&str>> = decls
        .iter()
        .map(|d| {
            let ds = d["dependencies"].as_array().unwrap();
            (d["name"].as_str().unwrap(), ds.iter().map(|x| x.as_str().unwrap()).collect())
        })
        .collect();
    let kinds: BTreeMap<&str, &str> =
        decls.iter().map(|d| (d["name"].as_str().unwrap(), d["kind"].as_str().unwrap())).collect();
    let mut reachable = BTreeSet::new();
    let mut queue = VecDeque::from(["Trusted.CppSemantics.CppEnvelopeTheorem"]);
    while let Some(n) = queue.pop_front() {
        if reachable.insert(n) {
            queue.extend(deps.get(n).into_iter().flatten().copied());
        }
    }
    // Lean-reserved auxiliary suffixes. `elim`, `ctorElim`, `ctorElimType`, and
    // `eq` are not reserved names on their own, so they count only under the
    // declaration Lean generates them for: a constructor (`C.elim`), an
    // inductive (`T.ctorElim`, `T.ctorElimType`), or a `brecOn` auxiliary
    // (`T.brecOn.eq`).
    let is_generated = |parent: &str, last: &str| {
        let parent_kind = kinds.get(parent).copied();
        last.starts_with('_')
            || last.starts_with("match_")
            || last.starts_with("proof_")
            || last.starts_with("eq_")
            || [
                "rec",
                "recOn",
                "casesOn",
                "below",
                "brecOn",
                "binductionOn",
                "ibelow",
                "noConfusion",
                "noConfusionType",
                "ctorIdx",
                "inj",
                "injEq",
                "sizeOf_spec",
            ]
            .contains(&last)
            || (last == "elim" && parent_kind == Some("constructor"))
            || (["ctorElim", "ctorElimType"].contains(&last) && parent_kind == Some("inductive"))
            || (last == "eq" && parent.ends_with(".brecOn"))
    };
    // Constructors need no exemption: the inventory lists an inductive's
    // constructors among its dependencies. Only a constructor of a generated
    // auxiliary inductive (such as `CppReaches.below`) climbs with it.
    let unreachable: Vec<&&str> = cpp_decls
        .iter()
        .filter(|n| {
            let mut cur: &str = n;
            loop {
                if reachable.contains(cur) {
                    return false;
                }
                let Some((parent, last)) = cur.rsplit_once('.') else { return true };
                let generated_ctor = kinds.get(cur) == Some(&"constructor")
                    && parent.rsplit_once('.').is_some_and(|(pp, pl)| is_generated(pp, pl));
                if !(is_generated(parent, last) || generated_ctor) {
                    return true;
                }
                cur = parent;
            }
        })
        .collect();
    assert!(
        unreachable.is_empty(),
        "Trusted.Cpp* declarations unreachable from \
         Trusted.CppSemantics.CppEnvelopeTheorem: {unreachable:?}"
    );

    // Non-vacuously inspect the compiled `.olean` files: no trusted or theory
    // module emits a `partial` / `._unsafe_rec` constant, and the theory
    // module contains the determinism and C-ABI linking theorems.
    let stage = checker.stage().to_path_buf();
    let mut oleans: Vec<(String, Vec<&str>)> = CPP_TRUSTED_MODULES
        .iter()
        .map(|m| {
            let rel = m.replace('.', "/");
            (stage.join(format!("lib/{rel}.olean")).to_string_lossy().into_owned(), vec![])
        })
        .collect();
    oleans.push((
        stage.join("theory-lib/Anneal/CppEquiv.olean").to_string_lossy().into_owned(),
        vec![
            "Anneal.CppEquiv.cppTerminates_of_trace",
            "Anneal.CppEquiv.BiTotalEquiv",
            "Anneal.CppEquiv.mkCAbiSimConv",
            "Anneal.CppEquiv.mkCAbiSimConv_rejects_cxxItanium",
        ]
        .into_iter()
        .chain(CPP_CANARIES)
        .collect(),
    ));
    let check_script = stage.join("CheckCppOleans.lean");
    run_lean_script(&mut checker, "check-cpp-oleans", &check_script, &olean_check_script(&oleans));

    // Negative: a `vetted` module attempting to import `Trusted.CppSemantics`
    // (`candidate:refinement`) fails closed in `"preflight"`.
    fs::write(
        fix.root.join("trusted/lean/Trusted/VettedImportsCppSemantics.lean"),
        "-- anneal-trust-tier: vetted\n\
         module\n\
         prelude\n\
         public import Init.NotationExtra\n\
         public import Trusted.CppSemantics\n",
    )
    .unwrap();
    let err = fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err.message.contains(
            "vetted module Trusted.VettedImportsCppSemantics cannot import candidate:refinement module Trusted.CppSemantics"
        ),
        "{err}"
    );
}

/// Kernel-checked execution canaries in `Anneal.CppEquiv`.
const CPP_CANARIES: [&str; 20] = [
    "Anneal.CppEquiv.canary_isoUB_overflow",
    "Anneal.CppEquiv.canary_wrapv_wraps",
    "Anneal.CppEquiv.canary_dangling_read",
    "Anneal.CppEquiv.canary_live_read",
    "Anneal.CppEquiv.canary_packed_member",
    "Anneal.CppEquiv.canary_unpacked_misaligned",
    "Anneal.CppEquiv.canary_zeroInit_padded",
    "Anneal.CppEquiv.canary_padded_copy_unsupported",
    "Anneal.CppEquiv.canary_bitCast_bool_unsupported",
    "Anneal.CppEquiv.canary_bool_bitfield_padded",
    "Anneal.CppEquiv.canary_const_write",
    "Anneal.CppEquiv.canary_nonconst_write",
    "Anneal.CppEquiv.canary_overlap_copy",
    "Anneal.CppEquiv.canary_disjoint_copy",
    "Anneal.CppEquiv.canary_subobject_oob",
    "Anneal.CppEquiv.canary_subobject_inbounds",
    "Anneal.CppEquiv.canary_ptr_addr_bound",
    "Anneal.CppEquiv.canary_const_zeroInit_write",
    "Anneal.CppEquiv.canary_subobject_rel_unsupported",
    "Anneal.CppEquiv.canary_subobject_rel_same_array",
];

/// Returns a Lean script that, for each `(olean, required)` pair, checks that
/// the module declares every `required` constant and no `partial` or
/// `._unsafe_rec` constant.
fn olean_check_script(oleans: &[(String, Vec<&str>)]) -> String {
    let cases: Vec<String> = oleans
        .iter()
        .map(|(path, required)| {
            let names: Vec<String> = required.iter().map(|n| format!("`{n}")).collect();
            format!("({path:?}, [{}])", names.join(", "))
        })
        .collect();
    format!(
        r#"import Lean
open Lean in
def main : IO Unit := do
  for (path, required) in ([{}] : List (String × List Name)) do
    let (data, _) ← readModuleData (System.FilePath.mk path)
    for n in required do
      unless data.constants.any (fun ci => ci.name == n) do
        throw (IO.userError s!"missing {{n}} in {{path}}")
    for ci in data.constants do
      if ci.isPartial || ci.name.toString.endsWith "._unsafe_rec" then
        throw (IO.userError s!"unexpected partial/_unsafe_rec constant: {{ci.name}}")
    for n in data.extraConstNames do
      if n.toString.endsWith "._unsafe_rec" then
        throw (IO.userError s!"unexpected extra _unsafe_rec constant: {{n}}")
"#,
        cases.join(",\n      ")
    )
}

/// Verifies that `Anneal.PureLift.CppBridge`, which the Pass-1 fixture above
/// cannot load (its `Trusted.MirModel` import would make the checker require
/// the whole MIR weakest-precondition stack), compiles from its import closure
/// with the pinned Lean and emits no `partial` / `._unsafe_rec` constants.
/// Pass-1 audit admits paired `._unsafe_rec` helpers, so this check is the one
/// that rules them out.
#[test]
fn cpp_bridge_compiles_without_partial_or_unsafe_rec() {
    let checkout = repo_root();
    let lean = anneal_testkit::toolchain::default_lean_path().expect("resolve pinned lean");
    let prefix = anneal_testkit::toolchain::lean_prefix(&lean).expect("lean --print-prefix");
    let tmp = tempfile::tempdir().unwrap();
    let src = tmp.path().join("src");
    let lib = tmp.path().join("lib");
    fs::create_dir_all(&lib).unwrap();
    let modules = copy_import_closure(&checkout, &src, &["Anneal.PureLift.CppBridge"]);
    let deps: BTreeMap<&str, Vec<String>> = modules
        .iter()
        .map(|m| {
            let rel = repo_module_path(m).unwrap();
            let imports = header_imports(&fs::read_to_string(src.join(rel)).unwrap());
            (m.as_str(), imports.into_iter().filter(|d| modules.contains(d)).collect())
        })
        .collect();
    let lean_path = env::join_paths([lib.as_path(), prefix.join("lib/lean").as_path()]).unwrap();
    let mut done = BTreeSet::new();
    while done.len() < modules.len() {
        let ready: Vec<&str> = deps
            .iter()
            .filter(|(m, ds)| !done.contains(**m) && ds.iter().all(|d| done.contains(d.as_str())))
            .map(|(m, _)| *m)
            .collect();
        assert!(!ready.is_empty(), "import cycle among {modules:?}");
        for m in ready {
            let rel = repo_module_path(m).unwrap();
            let root = src.join(if m.starts_with("Trusted") { "trusted/lean" } else { "theory" });
            let olean = lib.join(m.replace('.', "/")).with_extension("olean");
            fs::create_dir_all(olean.parent().unwrap()).unwrap();
            let output = Command::new(&lean)
                .env("LEAN_PATH", &lean_path)
                .args(["-j1", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-R"])
                .arg(&root)
                .arg("-o")
                .arg(&olean)
                .arg(src.join(rel))
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "compiling {m} failed:\n{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            done.insert(m.to_string());
        }
    }
    let bridge = lib.join("Anneal/PureLift/CppBridge.olean").to_string_lossy().into_owned();
    let script = tmp.path().join("CheckCppBridge.lean");
    fs::write(
        &script,
        olean_check_script(&[(
            bridge,
            vec![
                "Anneal.PureLift.CppBridge.cppExec_of_execStepPred",
                "Anneal.PureLift.CppBridge.execStepPred_of_cppReaches",
                "Anneal.PureLift.CppBridge.cppFaultsUB_of_execStepPred",
                "Anneal.PureLift.CppBridge.evalExpr_readDeref",
                "Anneal.PureLift.CppBridge.evalStep_ret",
            ],
        )]),
    )
    .unwrap();
    let output = Command::new(&lean)
        .env("LEAN_PATH", &lean_path)
        .env("LEAN_SYSROOT", &prefix)
        .args(["-j1", "--run"])
        .arg(&script)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "CppBridge olean check failed:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
