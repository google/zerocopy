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

/// Determines the name of the crate to verify.
///
/// This function attempts to resolve the crate name using the following precedence:
/// 1. Explicitly provided `crate_name` argument.
/// 2. `package.name` from the `Cargo.toml` pointed to by `manifest_path`.
/// 3. `package.name` from `Cargo.toml` in the `crate_root`.
///
/// # Arguments
/// * `manifest_path` - Optional path to a specific manifest or script.
/// * `crate_name` - Optional explicit override for the crate name.
/// * `crate_root` - The root directory of the invocation.
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
            // For single-file scripts, default to the filename as the crate name.
            return Ok(path.file_stem().unwrap().to_string_lossy().to_string());
        }
        cmd.manifest_path(path);
    } else {
        cmd.manifest_path(crate_root.join("Cargo.toml"));
    }

    cmd.no_deps();

    let metadata = cmd.exec().context("Failed to load cargo metadata")?;

    // If a specific manifest was requested, try to find the package corresponding to it.
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

    // Default to the root package if available.
    if let Some(root) = metadata.root_package() {
        return Ok(root.name.clone());
    }

    // Fallback: search for a package matching the default manifest path.
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

/// Controls the behavior when proofs are missing (`///@ proof` block is absent).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sorry {
    /// Substitute missing proofs with `sorry` (Lean's "trust me" keyword).
    ///
    /// This allows the verification to proceed and checking other proofs even if some are missing.
    AllowSorry,
    /// Fail the verification if any proof is missing.
    RejectSorry,
}

/// Executes the full Hermes verification pipeline.
///
/// # Arguments
/// * `crate_name` - Optional name override.
/// * `crate_root` - Path to the real crate root.
/// * `dest` - Destination directory for generated artifacts.
/// * `aeneas_path` - Path to local Aeneas installation.
/// * `manifest_path` - Path to specific Cargo.toml or script.
/// * `sorry_mode` - Whether to allow `sorry` for missing proofs.
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

    // Cleanup previous artifacts
    if llbc_path.exists() {
        fs::remove_file(&llbc_path)?;
    }

    // Only pass manifest_path as source_file if it is an .rs file (script)
    let source_file = if let Some(path) = &manifest_path {
        if path.extension().is_some_and(|e| e == "rs") { Some(path.as_path()) } else { None }
    } else {
        None
    };

    // Step 1: Create Shadow Crate
    //
    // This sanitizes the code (removing unsafe, mocking models) to prepare it for Charon.
    log::info!("Step 1: Creating Shadow Crate...");
    let (shadow_crate_root, shadow_source_file, models, roots) =
        crate::shadow::create_shadow_crate(crate_root, source_file)?;

    // Remap manifest path to use shadow crate
    // If it was a script, point to the shadow script.
    // If it was a Cargo manifest, point to the shadow Cargo manifest.
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

    // Prepend crate name to models to match Charon's fully qualified usage
    let opaque_funcs: Vec<String> =
        models.iter().map(|m| format!("{}::{}", crate_name_snake, m)).collect();

    // Prepend crate name to roots (start_from) for selective translation
    let mut start_from: Vec<String> =
        roots.iter().map(|r| format!("{}::{}", crate_name_snake, r)).collect();

    // Always include hermes_std and hermes_std::ptr to ensure they are available for valid imports.
    // Charon --start-from is recursive, so including the module root should be enough.
    start_from.push(format!("{}::hermes_std", crate_name_snake));

    // Step 2: Run Charon
    // Extracts the shadow crate to LLBC (Low-Level Borrow Calculus).
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
    //
    // Translates LLBC to Lean 4 models.
    log::info!("Step 2: Running Aeneas...");
    run_aeneas(&llbc_path, dest)?;

    // Step 4: Stitching
    //
    // Combines the generated Lean models with user-provided proofs extracted from doc comments.
    log::info!("Step 3: Stitching...");

    // Convert snake_case crate name to CamelCase for Lean module name
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

    stitch_user_proofs(
        &shadow_crate_root,
        &crate_name_snake,
        &camel_name,
        dest,
        sorry_mode,
        source_file.is_some(),
    )?;

    // Step 5: Verification (Lake Build)
    //
    // Compiles the generated Lean project.
    log::info!("Step 4: Verifying...");
    write_lakefile(dest, &crate_name_snake, &camel_name, aeneas_path, sorry_mode)?;
    run_lake_build(dest)?;

    log::info!("Verification Successful!");
    Ok(())
}

/// Parses the source code to extract user proofs and generates the corresponding Lean files.
///
/// This specific function walks the source tree, parses Rust files using `syn`, extracts
/// functions and structs, and then delegates to `generate_lean_file`.
fn stitch_user_proofs(
    crate_root: &Path,
    crate_name_snake: &str,
    crate_name_camel: &str,
    dest: &Path,
    sorry_mode: Sorry,
    is_script_mode: bool,
) -> Result<()> {
    let mut all_functions = Vec::new();
    let mut all_structs = Vec::new();

    let src_dir = crate_root.join("src");
    if src_dir.exists() {
        for entry in WalkDir::new(&src_dir) {
            let entry = entry?;
            if entry.path().extension().is_some_and(|ext| ext == "rs") {
                let relative = entry.path().strip_prefix(&src_dir)?;

                // Calculate file-based module path.
                //
                // e.g. `src/foo/bar.rs` -> `["foo", "bar"]`
                let components: Vec<_> = relative
                    .with_extension("")
                    .iter()
                    .map(|s| s.to_string_lossy().into_owned())
                    .collect();

                // Handle mod.rs/lib.rs conventions:
                // `src/lib.rs` -> `[]` (root)
                // `src/foo/mod.rs` -> `["foo"]` (not ["foo", "mod"])
                let mut mod_path = Vec::new();
                for (i, comp) in components.iter().enumerate() {
                    if i == components.len() - 1
                        && (comp == "mod" || comp == "lib" || comp == "main")
                    {
                        continue;
                    }
                    mod_path.push(comp.clone());
                }

                // If specialized for a script, and the file name matches the crate name,
                // we treat it as the root module.
                if is_script_mode && mod_path.len() == 1 && mod_path[0] == crate_name_snake {
                    mod_path.clear();
                }

                let content = fs::read_to_string(entry.path())?;
                let mut extracted = extract_blocks(&content)?;

                // Prepend the file's module path to the internal path associated with each item.
                // The `parser` extracts internal module paths (e.g. `mod inner { ... }`),
                // so we prefix the file path to that.
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
    )
}

/// Generates `UserProofs.lean` and `FunsExternal.lean` from the parsed artifacts.
///
/// # Arguments
/// * `dest` - Destination directory.
/// * `namespace_name` - The crate name in snake_case (used for Lean namespaces).
/// * `import_name` - The crate name in CamelCase (used for imports).
/// * `functions` - List of functions with specs/proofs.
/// * `structs` - List of structs (used for `Verifiable` instances).
/// * `sorry_mode` - Strategy for handling missing proofs.
fn generate_lean_file(
    dest: &Path,
    namespace_name: &str,
    import_name: &str,
    functions: &[ParsedFunction],
    structs: &[crate::parser::ParsedStruct],
    sorry_mode: Sorry,
) -> Result<()> {
    // `UserProofs.lean` will contain theorem statements and proofs.
    let mut user_proofs_content = String::new();
    // `FunsExternal.lean` will contain definitions for 'model' functions (infinite loops in Rust).
    let mut funs_external_content = String::new();

    // Standard imports needed for verification.
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

    // FunsExternal needs to import the Type definitions generated by Aeneas.
    // typically `${Namespace}.Types`.
    funs_external_content.push_str(&format!("import {}.Types\n", namespace_name));
    funs_external_content.push_str("import Aeneas\n");
    funs_external_content.push_str("import Hermes.Std\n");
    funs_external_content.push_str("open Aeneas Aeneas.Std Result Error\n");
    funs_external_content.push_str("open Hermes.Std\n");
    funs_external_content.push_str(&format!("\nnamespace {}\n\n", namespace_name));

    user_proofs_content.push_str(&common_imports);
    user_proofs_content.push_str(&format!("namespace {}\n\n", namespace_name));

    // Write Hermes/Std.lean (Static Library)
    let hermes_std_path = dest.join("Hermes");
    fs::create_dir_all(&hermes_std_path)?;
    fs::write(hermes_std_path.join("Std.lean"), include_str!("include/Std.lean"))?;
    fs::write(dest.join("Hermes.lean"), include_str!("Hermes.lean"))?;

    // --- Generate Verifiable Instances for Structs ---
    // Deduplicate structs just in case validation visited the same struct twice.
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

        // Generate instance definition
        // instance [Verifiable T] : Verifiable (MyStruct T) where
        //   is_valid self := ...
        let header = format!(
            "instance {}{} : Verifiable {} where",
            generic_params, generic_constraints, type_str
        );
        user_proofs_content.push_str(&header);
        user_proofs_content.push_str(&format!("\n  is_valid self := {}\n\n", invariant));
    }

    // --- Process Functions ---
    for func in functions {
        // Skip functions without Specs
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

        // Open/Close namespaces for this function (e.g. `namespace Foo`)
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

        // --- Handle Models (External Functions) ---
        if func.is_model {
            // Models are defined as `noncomputable def` in Lean, as they don't have a body extracted from Rust.
            // We model them using `Classical.choose` on their specification (if they return a value).
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
            // Use `if h : ... then Classical.choose h else panic` pattern to satisfy the return type
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
                        // Models without explicit proofs are axioms (we assume they behave as modeled).
                        "axiom"
                    } else {
                        anyhow::bail!("Missing proof for '{}'.", fn_name)
                    }
                }
            },
        };

        // Add validity arguments for inputs:
        // `(x : T) -> (h_x_valid : Verifiable.is_valid x)`
        let mut sig_parts = signature_args_full.clone();
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

        user_proofs_content.push_str(&format!("{} {}_spec {}\n", decl_type, fn_name, signature));
        user_proofs_content.push_str(&format!("  : {}\n", desugared.body));

        if decl_type == "theorem" {
            user_proofs_content.push_str("  :=\n");
            user_proofs_content.push_str("  by\n");
            user_proofs_content.push_str(proof_body);
        }

        user_proofs_content.push_str("\n");
        user_proofs_content.push_str(&ns_closers);
        user_proofs_content.push_str("\n");
    }

    user_proofs_content.push_str(&format!("end {}\n", namespace_name));
    funs_external_content.push_str(&format!("end {}\n", namespace_name));

    fs::write(dest.join("UserProofs.lean"), user_proofs_content)?;

    // Only write FunsExternal if we generated content?
    // Always good to write it to ensure imports work.
    if !funs_external_content.is_empty() {
        fs::write(dest.join("FunsExternal.lean"), funs_external_content)?;
    }

    Ok(())
}

/// Writes the `lakefile.lean` which configures the Lean build.
///
/// This file tells Lake how to build the project and where to find Aeneas.
fn write_lakefile(
    dest: &Path,
    crate_name_snake: &str,
    crate_name_camel: &str,
    aeneas_path: Option<PathBuf>,
    sorry_mode: Sorry,
) -> Result<()> {
    let lakefile_path = dest.join("lakefile.lean");
    // If aeneas_path is provided, use it (local development).
    // Otherwise, fetch from git.
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
