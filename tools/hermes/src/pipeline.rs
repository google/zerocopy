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

/// Convert snake_case to CamelCase.
fn to_camel_case(snake: &str) -> String {
    snake
        .split('_')
        .map(|s| {
            let mut c = s.chars();
            match c.next() {
                None => String::new(),
                Some(f) => f.to_uppercase().to_string() + c.as_str(),
            }
        })
        .collect()
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
    let camel_name = to_camel_case(&crate_name_snake);

    if llbc_path.exists() {
        fs::remove_file(&llbc_path)?;
    }

    let source_file = if let Some(path) = &manifest_path {
        if path.extension().is_some_and(|e| e == "rs") { Some(path.as_path()) } else { None }
    } else {
        None
    };

    // Step 1: Create Shadow Crate
    log::info!("Step 1: Creating Shadow Crate...");
    let (shadow_crate_root, shadow_source_file, models, roots) =
        crate::shadow::create_shadow_crate(crate_root, source_file)?;

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

    let opaque_funcs: Vec<String> =
        models.iter().map(|m| format!("{}::{}", crate_name_snake, m)).collect();

    let mut start_from: Vec<String> =
        roots.iter().map(|r| format!("{}::{}", crate_name_snake, r)).collect();
    start_from.push(format!("{}::hermes_std", crate_name_snake));

    // Step 2: Run Charon
    log::info!("Step 2: Running Charon...");
    run_charon(
        &shadow_crate_root,
        &llbc_path,
        shadow_manifest_path.as_deref(),
        &opaque_funcs,
        &start_from,
    )?;

    if !llbc_path.exists() {
        return Err(anyhow!("Charon did not produce expected LLBC file: {:?}", llbc_path));
    }

    // Step 3: Run Aeneas
    log::info!("Step 3: Running Aeneas...");
    run_aeneas(&llbc_path, dest)?;

    // Step 3b: Fix directory structure
    //
    // Aeneas with -split-files -gen-lib-entry outputs flat files (Types.lean, Funs.lean, etc.)
    // plus a root CamelName.lean that imports CamelName.Funs. But the imports expect a
    // subdirectory structure: CamelName/Funs.lean, CamelName/Types.lean, etc.
    //
    // Move the split files into the subdirectory.
    let sub_dir = dest.join(&camel_name);
    fs::create_dir_all(&sub_dir)?;

    let split_files = ["Types.lean", "Funs.lean", "FunsExternal_Template.lean"];
    for filename in &split_files {
        let src = dest.join(filename);
        let dst = sub_dir.join(filename);
        if src.exists() {
            fs::rename(&src, &dst).with_context(|| {
                format!("Failed to move {} to {}/", filename, camel_name)
            })?;
        }
    }

    let generated_camel = dest.join(format!("{}.lean", camel_name));
    if !generated_camel.exists() {
        return Err(anyhow!("Aeneas did not produce expected output file: {:?}", generated_camel));
    }

    // Step 4: Stitching
    log::info!("Step 4: Stitching...");
    // Only count user models, not injected hermes_std models
    let has_user_models = models.iter().any(|m| !m.starts_with("hermes_std"));
    stitch_user_proofs(
        &shadow_crate_root,
        &crate_name_snake,
        &camel_name,
        dest,
        sorry_mode,
        source_file.is_some(),
        has_user_models,
    )?;

    // Step 4b: Handle FunsExternal.lean
    //
    // Always use the Aeneas-generated template — it provides correct axioms for all
    // opaque functions (including hermes_std models). The Hermes model generator
    // can produce malformed Lean for complex model signatures.
    let funs_ext_dest = sub_dir.join("FunsExternal.lean");
    let funs_ext_template = sub_dir.join("FunsExternal_Template.lean");
    let funs_ext_hermes = dest.join("FunsExternal.lean");

    if funs_ext_template.exists() {
        fs::copy(&funs_ext_template, &funs_ext_dest)?;
    }
    // Clean up any Hermes-generated FunsExternal at the top level
    if funs_ext_hermes.exists() {
        fs::remove_file(&funs_ext_hermes)?;
    }

    // Step 5: Verification (Lake Build)
    log::info!("Step 5: Verifying with Lake...");
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
    is_script_mode: bool,
    has_user_models: bool,
) -> Result<()> {
    let mut all_functions = Vec::new();
    let mut all_structs = Vec::new();

    let src_dir = crate_root.join("src");
    if src_dir.exists() {
        for entry in WalkDir::new(&src_dir) {
            let entry = entry?;
            if entry.path().extension().is_some_and(|ext| ext == "rs") {
                let relative = entry.path().strip_prefix(&src_dir)?;

                let components: Vec<_> = relative
                    .with_extension("")
                    .iter()
                    .map(|s| s.to_string_lossy().into_owned())
                    .collect();

                let mut mod_path = Vec::new();
                for (i, comp) in components.iter().enumerate() {
                    if i == components.len() - 1
                        && (comp == "mod" || comp == "lib" || comp == "main")
                    {
                        continue;
                    }
                    mod_path.push(comp.clone());
                }

                if is_script_mode && mod_path.len() == 1 && mod_path[0] == crate_name_snake {
                    mod_path.clear();
                }

                let content = fs::read_to_string(entry.path())?;
                let mut extracted = extract_blocks(&content)?;

                for func in &mut extracted.functions {
                    let mut full_path = mod_path.clone();
                    full_path.extend(func.path.drain(..));
                    func.path = full_path;
                }

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
        has_user_models,
    )
}

fn generate_lean_file(
    dest: &Path,
    namespace_name: &str,
    import_name: &str,
    functions: &[ParsedFunction],
    structs: &[crate::parser::ParsedStruct],
    sorry_mode: Sorry,
    has_user_models: bool,
) -> Result<()> {
    let mut user_proofs_content = String::new();
    let mut funs_external_content = String::new();

    // --- UserProofs.lean imports ---
    // Use CamelCase import name, not snake_case
    user_proofs_content.push_str(&format!("import {}\n", import_name));
    user_proofs_content.push_str("import Aeneas\n");

    // Only import Hermes.Std if we have structs with invariants or models
    let needs_hermes_std = has_user_models || structs.iter().any(|s| s.invariant.is_some());
    if needs_hermes_std {
        user_proofs_content.push_str("import Hermes.Std\n");
    }

    user_proofs_content.push_str("open Aeneas Aeneas.Std Result Error\n");

    if needs_hermes_std {
        user_proofs_content.push_str("open Hermes.Std\n");
        user_proofs_content.push_str("open Hermes.Std.Memory\n");
        user_proofs_content.push_str("open Hermes.Std.Platform\n");
    }

    user_proofs_content.push_str("set_option linter.unusedVariables false\n\n");
    user_proofs_content.push_str(&format!("namespace {}\n\n", namespace_name));

    // --- FunsExternal.lean imports ---
    // Use CamelCase import name for Types
    funs_external_content.push_str(&format!("import {}.Types\n", import_name));
    funs_external_content.push_str("import Aeneas\n");
    if needs_hermes_std {
        funs_external_content.push_str("import Hermes.Std\n");
    }
    funs_external_content.push_str("open Aeneas Aeneas.Std Result Error\n");
    if needs_hermes_std {
        funs_external_content.push_str("open Hermes.Std\n");
    }
    funs_external_content.push_str(&format!("\nnamespace {}\n\n", namespace_name));

    // Write Hermes/Std.lean (Static Library) — only if needed
    if needs_hermes_std {
        let hermes_std_path = dest.join("Hermes");
        fs::create_dir_all(&hermes_std_path)?;
        fs::write(hermes_std_path.join("Std.lean"), include_str!("include/Std.lean"))?;
        fs::write(dest.join("Hermes.lean"), include_str!("Hermes.lean"))?;
    }

    // --- Struct Verifiable instances ---
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

    // --- Process Functions ---
    for func in functions {
        // Skip hermes_std internal functions — they are handled by the Aeneas template
        if func.path.first().is_some_and(|p| p == "hermes_std") {
            continue;
        }

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

        // Open/Close namespaces
        let mut ns_openers = String::new();
        let mut ns_closers = String::new();
        for ns in &func.path {
            ns_openers.push_str(&format!("namespace {}\n", ns));
        }
        for ns in func.path.iter().rev() {
            ns_closers.push_str(&format!("end {}\n", ns));
        }

        let mut signature_args_full = Vec::new();
        if !generics_context.is_empty() {
            signature_args_full.push(generics_context.clone());
        }
        if let Some(args) = &desugared.signature_args {
            signature_args_full.push(args.clone());
        }

        // --- Handle Models ---
        if func.is_model {
            funs_external_content.push_str(&ns_openers);

            let sig_str = signature_args_full.join(" ");
            let pred = desugared.predicate.as_deref().unwrap_or("True");
            let binders_str = desugared.binders.join(" ");

            let exists_clause = if desugared.binders.is_empty() {
                pred.to_string()
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
            funs_external_content.push_str("  else\n    Result.fail Error.panic\n");

            funs_external_content.push_str(&ns_closers);
            funs_external_content.push_str("\n");
        }

        // --- Generate Spec/Theorem ---
        user_proofs_content.push_str(&ns_openers);

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

        // Build signature with validity arguments
        let mut sig_parts = signature_args_full.clone();
        // Only add validity arguments when Hermes.Std is in use
        if needs_hermes_std {
            for arg in &inputs {
                if let syn::FnArg::Typed(pat_type) = arg
                    && let syn::Pat::Ident(pat_ident) = &*pat_type.pat
                {
                    let name = &pat_ident.ident;
                    sig_parts.push(format!("(h_{}_valid : Verifiable.is_valid {})", name, name));
                }
            }
        }
        for req in &desugared.extra_args {
            sig_parts.push(req.clone());
        }
        let signature = sig_parts.join(" ");

        let decl_type = if func.is_model && func.proof.is_none() { "axiom" } else { "theorem" };

        user_proofs_content.push_str(&format!("{} {}_spec {}\n", decl_type, fn_name, signature));
        user_proofs_content.push_str(&format!("  : {}\n", desugared.body));

        if decl_type == "theorem" {
            user_proofs_content.push_str("  :=\n");
            user_proofs_content.push_str("  by\n");
            // Preserve indentation: each line from the proof gets 2-space indent
            for line in proof_body.lines() {
                if line.trim().is_empty() {
                    user_proofs_content.push('\n');
                } else {
                    user_proofs_content.push_str("  ");
                    user_proofs_content.push_str(line);
                    user_proofs_content.push('\n');
                }
            }
        }

        user_proofs_content.push('\n');
        user_proofs_content.push_str(&ns_closers);
        user_proofs_content.push('\n');
    }

    user_proofs_content.push_str(&format!("end {}\n", namespace_name));
    funs_external_content.push_str(&format!("end {}\n", namespace_name));

    fs::write(dest.join("UserProofs.lean"), user_proofs_content)?;

    // Only write FunsExternal if we have model content
    if has_user_models {
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

    // Only include Hermes in roots if the directory exists
    let hermes_dir = dest.join("Hermes");
    let hermes_root = if hermes_dir.exists() {
        ", `Hermes"
    } else {
        ""
    };

    let content = format!(
        r#"
import Lake
open Lake DSL

package {}

{}

@[default_target]
lean_lib {} {{
  roots := #[`{}, `UserProofs{}]{}
}}
"#,
        crate_name_snake, require_line, crate_name_snake, crate_name_camel, hermes_root, more_lean_args
    );
    fs::write(lakefile_path, content).map_err(Into::into)
}
