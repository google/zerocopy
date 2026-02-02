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
    orchestration::{run_aeneas, run_charon, run_lake_build},
    parser::{ParsedFunction, extract_blocks},
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
        // If it's a script, we just use the filename.
        if path.extension().map_or(false, |e| e == "rs") {
            return Ok(path.file_stem().unwrap().to_string_lossy().to_string());
        }

        cmd.manifest_path(path);
    } else {
        cmd.manifest_path(crate_root.join("Cargo.toml"));
    }

    // We don't need dependencies, just the root package info.
    cmd.no_deps();

    let metadata = cmd.exec().context("Failed to load cargo metadata")?;

    // If we have a specific manifest path, look for the package with that path
    if let Some(path) = manifest_path {
        let canonical_manifest = fs::canonicalize(path).unwrap_or(path.to_path_buf());
        if let Some(pkg) = metadata.packages.iter().find(|p| {
            // Try to canonicalize package manifest path for comparison
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

    // If no manifest path provided or not found, try root_package (works for non-virtual)
    if let Some(root) = metadata.root_package() {
        return Ok(root.name.clone());
    }

    // Try finding a package whose manifest is in crate_root/Cargo.toml
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

    // Clean up stale artifacts before running Charon. While it's not strictly
    // necessary under ideal conditions, it hedges against Charon failing to
    // produce a new file (or producing one with a different name), which would
    // result in us verifying a stale artifact.
    if llbc_path.exists() {
        fs::remove_file(&llbc_path)?;
    }

    run_charon(crate_root, &llbc_path, manifest_path.as_deref())?;

    if !llbc_path.exists() {
        return Err(anyhow!("Charon did not produce expected LLBC file: {:?}", llbc_path));
    }

    // 4. Run Aeneas
    println!("Step 2: Running Aeneas...");
    run_aeneas(&llbc_path, dest)?;

    // 4. Stitching
    println!("Step 3: Stitching...");

    // Aeneas enforces PascalCase (CamelCase) for generated files.
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
        &crate_root,
        &crate_name_snake,
        &camel_name,
        dest,
        manifest_path.as_deref(),
        sorry_mode,
    )?;

    // 5. Verify
    println!("Step 4: Verifying...");
    // ensure lakefile exists
    // Note: lakefile still uses snake_case for package name and roots, but `CamelCase` structure for imports
    write_lakefile(dest, &crate_name_snake, &camel_name, aeneas_path, sorry_mode)?;
    run_lake_build(dest)?;

    println!("Verification Successful!");
    Ok(())
}

fn stitch_user_proofs(
    crate_root: &Path,
    crate_name_snake: &str,
    crate_name_camel: &str,
    dest: &Path,
    source_file: Option<&Path>,
    sorry_mode: Sorry,
) -> Result<()> {
    let mut all_functions = Vec::new();

    if let Some(path) = source_file {
        // If a specific source file is provided (e.g. script), uses that.
        // We only scan this single file.
        if path.exists() {
            let content = fs::read_to_string(path)?;
            let extracted = extract_blocks(&content)?;
            all_functions.extend(extracted.functions);
        }
    } else {
        // Otherwise scan src dir
        let src_dir = crate_root.join("src");
        if src_dir.exists() {
            for entry in WalkDir::new(src_dir) {
                let entry = entry?;
                if entry.path().extension().map_or(false, |ext| ext == "rs") {
                    let content = fs::read_to_string(entry.path())?;
                    let extracted = extract_blocks(&content)?;
                    all_functions.extend(extracted.functions);
                }
            }
        }
    }

    generate_lean_file(dest, crate_name_snake, crate_name_camel, &all_functions, sorry_mode)
}

fn generate_lean_file(
    dest: &Path,
    namespace_name: &str,
    import_name: &str,
    functions: &[ParsedFunction],
    sorry_mode: Sorry,
) -> Result<()> {
    let mut content = String::new();
    content.push_str(&format!("import {}\n", import_name));
    content.push_str("import Aeneas\n");
    content.push_str("open Aeneas Aeneas.Std Result Error\n\n");
    content.push_str(&format!("open {}\n\n", namespace_name));

    for func in functions {
        // Only generate for functions that have a spec.
        let spec_body = match &func.spec {
            Some(s) => s,
            None => continue,
        };

        let proof_body = match (&func.proof, sorry_mode) {
            (Some(proof), _) => proof.as_str(),
            (None, Sorry::AllowSorry) => "sorry",
            (None, Sorry::RejectSorry) => anyhow::bail!(
                "Missing proof for function '{}'. Use --allow-sorry to fallback to sorry.",
                func.fn_name
            ),
        };

        // Context Injection
        let context = extract_generics_context(&func.generics);

        // Transform the spec body into a valid Lean theorem type.
        // If the body contains "ensures", we format it as a return type check.
        //
        // Example Input: "ensures |ret| ..."
        // Example Output: ": ensures |ret| ..."
        let body = if spec_body.contains("ensures") && !spec_body.contains(": ensures") {
            spec_body.replacen("ensures", ": ensures", 1)
        } else {
            spec_body.clone()
        };

        content.push_str(&format!("theorem {}_spec {} {}\n", func.fn_name, context, body));
        content.push_str("  :=\n");
        content.push_str("  by\n");
        content.push_str(proof_body);
        content.push_str("\n\n");
    }

    fs::write(dest.join("UserProofs.lean"), content).map_err(Into::into)
}

fn extract_generics_context(generics: &syn::Generics) -> String {
    let mut context = String::new();
    for param in &generics.params {
        if let syn::GenericParam::Type(type_param) = param {
            let name = &type_param.ident;
            // {T : Type}
            context.push_str(&format!("{{{name} : Type}} "));

            // Bounds
            // Simplistic mapping: T: Foo -> [inst : Foo T]
            for bound in &type_param.bounds {
                if let syn::TypeParamBound::Trait(trait_bound) = bound {
                    // This is tricky if it's a complex path, but let's try to get the last segment
                    if let Some(segment) = trait_bound.path.segments.last() {
                        let trait_name = &segment.ident;
                        context
                            .push_str(&format!("[inst{name}{trait_name} : {trait_name} {name}] "));
                    }
                }
            }
        }
    }
    context
}

fn write_lakefile(
    dest: &Path,
    crate_name_snake: &str,
    crate_name_camel: &str,
    aeneas_path: Option<PathBuf>,
    sorry_mode: Sorry,
) -> Result<()> {
    let lakefile_path = dest.join("lakefile.lean");
    // Only create if missing. If the user wants to force regen, they should delete it or we add a flag.
    let require_line = if let Some(path) = aeneas_path {
        format!("require aeneas from \"{}\"", path.display())
    } else {
        r#"require aeneas from git "https://github.com/AeneasVerif/aeneas" @ "main""#.to_string()
    };

    let more_lean_args = match sorry_mode {
        // If sorry is NOT allowed, we want to fail on warnings (like
        // 'declaration uses sorry')
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
  roots := #[`{}, `UserProofs]{}
}}
"#,
        crate_name_snake, require_line, crate_name_snake, crate_name_camel, more_lean_args
    );
    fs::write(lakefile_path, content).map_err(Into::into)
}
