// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    fs,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result, anyhow};
use walkdir::WalkDir;

use crate::{
    desugar::desugar_spec,
    orchestration::{run_aeneas, run_charon, run_lake_build},
    parser::{ParsedFunction, extract_blocks},
    translator::SignatureTranslator,
};

fn get_crate_name(
    manifest_path: Option<&Path>,
    crate_name: Option<String>,
    crate_root: &Path,
) -> Result<String> {
    if let Some(name) = crate_name {
        return Ok(name);
    }

    let mut cmd = cargo_metadata::MetadataCommand::new();
    if let Some(path) = manifest_path {
        if path.extension().is_some_and(|e| e == "rs") {
            return Ok(path.file_stem().unwrap().to_string_lossy().to_string());
        }
        cmd.manifest_path(path);
    } else {
        cmd.manifest_path(crate_root.join("Cargo.toml"));
    }

    cmd.no_deps();

    let metadata = cmd.exec().context("Failed to load cargo metadata")?;

    if let Some(path) = manifest_path {
        let canonical_manifest = fs::canonicalize(path).unwrap_or(path.to_path_buf());
        if let Some(pkg) = metadata.packages.iter().find(|p| {
            p.manifest_path
                .as_std_path()
                .canonicalize()
                .map_or(p.manifest_path.as_std_path() == canonical_manifest, |p| {
                    p == canonical_manifest
                })
        }) {
            return Ok(pkg.name.clone());
        }
    }

    if let Some(root) = metadata.root_package() {
        return Ok(root.name.clone());
    }

    let default_manifest = crate_root.join("Cargo.toml");
    let canonical_default = fs::canonicalize(&default_manifest).unwrap_or(default_manifest);
    if let Some(pkg) = metadata.packages.iter().find(|p| {
        p.manifest_path
            .as_std_path()
            .canonicalize()
            .map_or(p.manifest_path.as_std_path() == canonical_default, |p| p == canonical_default)
    }) {
        return Ok(pkg.name.clone());
    }

    Err(anyhow!("Could not determine crate name from Cargo.toml"))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sorry {
    AllowSorry,
    RejectSorry,
}

pub fn run_pipeline(
    crate_name: Option<String>,
    crate_root: &Path,
    dest: &Path,
    aeneas_path: Option<PathBuf>,
    manifest_path: Option<PathBuf>,
    sorry_mode: Sorry,
) -> Result<()> {
    let crate_name = get_crate_name(manifest_path.as_deref(), crate_name, crate_root)?;

    fs::create_dir_all(dest).context("Failed to create destination directory")?;

    let crate_name_snake = crate_name.replace('-', "_");
    let llbc_path = dest.join(format!("{}.llbc", crate_name_snake));

    if llbc_path.exists() {
        fs::remove_file(&llbc_path)?;
    }

    // Only pass manifest_path as source_file if it is an .rs file (script)
    let source_file = if let Some(path) = &manifest_path {
        if path.extension().is_some_and(|e| e == "rs") { Some(path.as_path()) } else { None }
    } else {
        None
    };

    log::info!("Step 1: Creating Shadow Crate...");
    let (shadow_crate_root, shadow_source_file, models) =
        crate::shadow::create_shadow_crate(crate_root, source_file)?;

    // Remap manifest path to use shadow crate
    let shadow_manifest_path = if let Some(shadow_file) = shadow_source_file {
        Some(shadow_file)
    } else if let Some(path) = &manifest_path {
        if let Ok(rel) = path.strip_prefix(crate_root) {
            Some(shadow_crate_root.join(rel))
        } else {
            Some(path.clone())
        }
    } else {
        None
    };

    // Prepend crate name to models
    let opaque_funcs: Vec<String> =
        models.iter().map(|m| format!("{}::{}", crate_name_snake, m)).collect();

    run_charon(&shadow_crate_root, &llbc_path, shadow_manifest_path.as_deref(), &opaque_funcs)?;

    if !llbc_path.exists() {
        return Err(anyhow!("Charon did not produce expected LLBC file: {:?}", llbc_path));
    }

    log::info!("Step 2: Running Aeneas...");
    run_aeneas(&llbc_path, dest)?;

    log::info!("Step 3: Stitching...");

    let camel_name: String = crate_name_snake
        .split('_')
        .map(|s| {
            let mut c = s.chars();
            match c.next() {
                None => String::new(),
                Some(f) => f.to_uppercase().to_string() + c.as_str(),
            }
        })
        .collect();

    let generated_camel = dest.join(format!("{}.lean", camel_name));
    if !generated_camel.exists() {
        return Err(anyhow!("Aeneas did not produce expected output file: {:?}", generated_camel));
    }

    stitch_user_proofs(&shadow_crate_root, &crate_name_snake, &camel_name, dest, sorry_mode)?;

    log::info!("Step 4: Verifying...");
    write_lakefile(dest, &crate_name_snake, &camel_name, aeneas_path, sorry_mode)?;
    run_lake_build(dest)?;

    log::info!("Verification Successful!");
    Ok(())
}

fn stitch_user_proofs(
    crate_root: &Path,
    crate_name_snake: &str,
    crate_name_camel: &str,
    dest: &Path,
    sorry_mode: Sorry,
) -> Result<()> {
    let mut all_functions = Vec::new();
    let mut all_structs = Vec::new();

    let src_dir = crate_root.join("src");
    if src_dir.exists() {
        for entry in WalkDir::new(src_dir) {
            let entry = entry?;
            if entry.path().extension().is_some_and(|ext| ext == "rs") {
                let content = fs::read_to_string(entry.path())?;
                let extracted = extract_blocks(&content)?;
                all_functions.extend(extracted.functions);
                all_structs.extend(extracted.structs);
            }
        }
    }

    generate_lean_file(
        dest,
        crate_name_snake,
        crate_name_camel,
        &all_functions,
        &all_structs,
        sorry_mode,
    )
}

fn generate_lean_file(
    dest: &Path,
    namespace_name: &str,
    import_name: &str,
    functions: &[ParsedFunction],
    structs: &[crate::parser::ParsedStruct],
    sorry_mode: Sorry,
) -> Result<()> {
    let mut user_proofs_content = String::new();
    let mut funs_external_content = String::new();

    let common_imports = format!(
        "import {}
import Aeneas
import Hermes.Std
open Aeneas Aeneas.Std Result Error
open Hermes.Std
open Hermes.Std.Memory
open Hermes.Std.Platform
open {}.hermes_std.ptr
set_option linter.unusedVariables false

",
        import_name, namespace_name
    );

    // FunsExternal needs to import Types? Yes, usually via `import_name` (e.g. ShadowModel or GenericId).
    // Actually, `import_name` usually imports `Funs` which imports `Types`.
    // But `Funs` imports `FunsExternal`. Cycle!
    // `FunsExternal` should only import `Types`.
    // We assume `import {import_name}` imports the top-level generic_id.lean which imports Funs/Types?
    // No, Aeneas structure:
    // {Crate}.lean imports Funs, Types.
    // Funs imports Types, FunsExternal.
    // So FunsExternal should import Types explicitly if needed.
    // `import_name` usually refers to the crate which might not verify yet if we are circular.
    // Aeneas typically generates module structure: `namespace.Types`, `namespace.Funs`.
    // We should import `{namespace_name}.Types`.

    funs_external_content.push_str(&format!("import {}.Types\n", namespace_name));
    funs_external_content.push_str("import Aeneas\n");
    funs_external_content.push_str("import Hermes.Std\n");
    funs_external_content.push_str("open Aeneas Aeneas.Std Result Error\n");
    funs_external_content.push_str("open Hermes.Std\n");
    funs_external_content.push_str(&format!("\nnamespace {}\n\n", namespace_name));

    user_proofs_content.push_str(&common_imports);
    user_proofs_content.push_str(&format!("namespace {}\n\n", namespace_name));

    // Write Hermes/Std.lean
    let hermes_std_path = dest.join("Hermes");
    fs::create_dir_all(&hermes_std_path)?;
    fs::write(hermes_std_path.join("Std.lean"), include_str!("include/Std.lean"))?;
    fs::write(dest.join("Hermes.lean"), include_str!("Hermes.lean"))?;

    // Struct Instances (UserProofs)
    // ... (keep struct logic)
    // Dedup structs just in case
    let mut unique_structs = Vec::new();
    let mut seen_structs = std::collections::HashSet::new();
    for st in structs {
        if seen_structs.insert(st.ident.to_string()) {
            unique_structs.push(st);
        }
    }

    for st in unique_structs {
        let name = &st.ident;
        let mut invariant = st.invariant.as_deref().unwrap_or("True");
        if invariant.is_empty() {
            invariant = "True";
        }

        // Handle Generics: [Verifiable T] for each T
        let mut generic_params = String::new();
        let mut generic_constraints = String::new();
        let mut type_args = String::new();

        for param in &st.generics.params {
            if let syn::GenericParam::Type(t) = param {
                generic_params.push_str(&format!("{{{}}} ", t.ident));
                generic_constraints.push_str(&format!("[Verifiable {}] ", t.ident));
                type_args.push_str(&format!("{} ", t.ident));
            }
        }

        let type_str = if type_args.is_empty() {
            name.to_string()
        } else {
            format!("({} {})", name, type_args.trim())
        };

        let header = format!(
            "instance {}{} : Verifiable {} where",
            generic_params, generic_constraints, type_str
        );
        user_proofs_content.push_str(&header);
        user_proofs_content.push_str(&format!("\n  is_valid self := {}\n\n", invariant));
    }

    // Process Functions
    for func in functions {
        let spec_content = match &func.spec {
            Some(s) => s,
            None => continue,
        };

        let fn_name = func.sig.ident.to_string();
        let inputs: Vec<syn::FnArg> = func.sig.inputs.iter().cloned().collect();
        let is_stateful = SignatureTranslator::detect_statefulness(&inputs);

        if func.is_model && is_stateful {
            anyhow::bail!(
                "Function '{}' is marked as a model but has mutable references. This is not supported.",
                fn_name
            );
        }

        let generics_context = SignatureTranslator::translate_generics(&func.sig.generics);
        let desugared = match desugar_spec(spec_content, &fn_name, &inputs, is_stateful) {
            Ok(d) => d,
            Err(e) => {
                log::warn!("Skipping function '{}' due to spec error: {}", fn_name, e);
                continue;
            }
        };

        let mut signature_args_full = Vec::new();
        if !generics_context.is_empty() {
            signature_args_full.push(generics_context.clone());
        }
        if let Some(args) = &desugared.signature_args {
            signature_args_full.push(args.clone());
        }

        if func.is_model {
            // Generate External Definition
            // 1. Spec Predicate
            // def foo_spec (args...) (ret...) : Prop := ...
            // The desugared.predicate contains the logic.
            // We need to construct the arguments for the spec.
            // desugared.signature_args has (x : T). destuared.binders has names of rets.
            // We need types for rets?
            // desugar doesn't infer types.
            // But usually spec is written like: `ensures |ret| ...`
            // In Lean, we can rely on inference if we use `exists ret, ...`
            // But for `def foo_spec args ret : Prop`, we need ret's Type.
            // Either we parse it from the signature (RetType) or we trust user provided it?
            // User provided `ensures |ret| ...`. No type info.
            // So `foo_spec` signature is hard to generate fully typed without more info.
            // However, we can define `foo_spec` as:
            // `def foo_spec args ret := logic`
            // relying on Lean to infer types from the logic body?
            // Or we just inline it in the `exists`.
            //
            // Let's rely on the `desugar.body` which is `exists ret, ...`.
            // Wait, `desugar.body` is designed for theorem statement: `foo_fwd ... = ...`.
            // It is NOT the predicate `P /\ Q`.
            // `desugared.predicate` IS the logic `P /\ Q`.
            //
            // Let's generate:
            // `noncomputable def foo (args...) : Result RetType :=`
            // `  if h : exists ret, (predicate_substituted) then`
            //
            // Problem: `predicate` uses binder names.
            // We need to say `exists ret, (logic with ret)`.
            //
            // `desugared.predicate` is `Some("logic")`.
            // `desugared.binders` is `["ret"]`.
            //
            // Content:
            // noncomputable def {fn_name} {signature_args} : Result {RetType} :=
            //   if h : exists {binders}, {predicate} then
            //     let v := Classical.choose h
            //     Result.ok v
            //   else
            //     Result.fail Error.panic
            //
            // We need `RetType`. `ParsedFunction` has `sig` which has `output`.
            // We can translate `output` to Lean type?
            // `translator.rs` doesn't have type translator yet.
            // BUT `desugar` might have extracted signature args? No.
            // `parsed_function` has `sig`.
            //
            // Use Aeneas naming?
            // Aeneas usually generates `def foo ... : Result T`.
            // If we redeclare it, we must match exactly.
            //
            // Alternative:
            // Reuse the `desugared.body` which was: `exists ret, foo_fwd ... = Result.ok ret /\ logic`.
            // This body asserts that the function matches the logic.
            // It doesn't help us DEFINE the function.
            //
            // We genuinely need the return type to write the signature of `noncomputable def`.
            //
            // Hack: Can we avoid explicit type?
            // `noncomputable def foo ... := ...` (infer return type?)
            // `Result.ok (Classical.choose h)` -> implies Result T.
            // Lean might infer it?
            //
            // Let's try omitting return type if possible?
            // `noncomputable def foo {signature_args} :=`
            //
            // Need to ensure `signature_args` covers all args.
            //
            // AND `desugared.binders`: if multiple (tuple), `Classical.choose h` returns a tuple.
            //
            // Let's construct it.

            let sig_str = signature_args_full.join(" ");
            // Note: `signature_args` usually is `(x : U32) ...`.

            let pred = desugared.predicate.as_deref().unwrap_or("True");
            let binders_str = desugared.binders.join(" "); // "ret" or "ret1 ret2"

            // "exists ret, P"
            let exists_clause = if desugared.binders.is_empty() {
                pred.to_string() // Just logic?
            } else {
                format!("exists {}, {}", binders_str, pred)
            };

            funs_external_content
                .push_str(&format!("noncomputable def {} {} :=\n", fn_name, sig_str));
            funs_external_content.push_str(&format!("  if h : {} then\n", exists_clause));
            if desugared.binders.is_empty() {
                funs_external_content.push_str("    Result.ok ()\n");
            } else {
                funs_external_content.push_str("    Result.ok (Classical.choose h)\n");
            }
            funs_external_content.push_str("  else\n    Result.fail Error.panic\n\n");
        }

        // Spec Generation (Common for Model and Verified)
        // Standard Verified Function or Model Spec
        let proof_body = match &func.proof {
            Some(p) => p.as_str(),
            None => match sorry_mode {
                Sorry::AllowSorry => "sorry",
                Sorry::RejectSorry => {
                    if func.is_model {
                        "axiom"
                    } else {
                        anyhow::bail!("Missing proof for '{}'.", fn_name)
                    }
                }
            },
        };

        // Signature parts for UserProofs
        let mut sig_parts = signature_args_full.clone();

        // Inject Argument Validity Checks
        for arg in &inputs {
            if let syn::FnArg::Typed(pat_type) = arg
                && let syn::Pat::Ident(pat_ident) = &*pat_type.pat
            {
                let name = &pat_ident.ident;
                sig_parts.push(format!("(h_{}_valid : Verifiable.is_valid {})", name, name));
            }
        }

        for req in &desugared.extra_args {
            sig_parts.push(req.clone());
        }

        let signature = sig_parts.join(" ");

        let decl_type = if func.is_model && func.proof.is_none() { "axiom" } else { "theorem" };
        // If proof_body is "axiom", decl_type is axiom.
        // Actually logic above:
        // if model and no proof -> "axiom" body? No, body is empty for axiom.

        user_proofs_content.push_str(&format!("{} {}_spec {}\n", decl_type, fn_name, signature));
        user_proofs_content.push_str(&format!("  : {}\n", desugared.body));

        if decl_type == "theorem" {
            user_proofs_content.push_str("  :=\n");
            user_proofs_content.push_str("  by\n");
            user_proofs_content.push_str(proof_body);
        }
        user_proofs_content.push_str("\n\n");
    }

    user_proofs_content.push_str(&format!("end {}\n", namespace_name));
    funs_external_content.push_str(&format!("end {}\n", namespace_name));

    fs::write(dest.join("UserProofs.lean"), user_proofs_content)?;

    // Only write FunsExternal if we have content?
    // Aeneas generates Template if it misses it.
    // If we write it, Aeneas should be happy.
    // Even if empty?
    if !funs_external_content.is_empty() {
        fs::write(dest.join("FunsExternal.lean"), funs_external_content)?;
    }

    Ok(())
}

fn write_lakefile(
    dest: &Path,
    crate_name_snake: &str,
    crate_name_camel: &str,
    aeneas_path: Option<PathBuf>,
    sorry_mode: Sorry,
) -> Result<()> {
    let lakefile_path = dest.join("lakefile.lean");
    let require_line = if let Some(path) = aeneas_path {
        format!("require aeneas from \"{}\"", path.display())
    } else {
        r#"require aeneas from git "https://github.com/AeneasVerif/aeneas" @ "main""#.to_string()
    };

    let more_lean_args = match sorry_mode {
        Sorry::RejectSorry => "\n  moreLeanArgs := #[\"-DwarningAsError=true\"]",
        Sorry::AllowSorry => "",
    };

    let content = format!(
        r#"
import Lake
open Lake DSL

package {}

{}

@[default_target]
lean_lib {} {{
  roots := #[`{}, `UserProofs, `Hermes]{}
}}
"#,
        crate_name_snake, require_line, crate_name_snake, crate_name_camel, more_lean_args
    );
    fs::write(lakefile_path, content).map_err(Into::into)
}
