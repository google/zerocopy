// Orchestration of Aeneas translation and Lean project management.
//
// This module handles the entire lifecycle of the Lean verification
// project generation:
// 1. Setting up the directory structure.
// 2. Optimizing setup using valid integration test caches (if available).
// 3. Invoking `aeneas` to translate LLBC to Lean.
// 4. Generating the `lakefile.lean` and other boilerplate.
// 5. Building the Lean project using `lake`.
// 6. Running custom diagnostic scripts to verify proofs and report errors
//    back to Rust.

use std::{
    fmt::Write,
    fs,
    io::{BufRead, BufReader},
    path::Path,
    process::{Command, Stdio},
    sync::{Arc, Mutex},
};

use anyhow::{Context, Result, bail};
use indicatif::{ProgressBar, ProgressStyle};
use walkdir::WalkDir;

use crate::{generate, resolve::LockedRoots, scanner::AnnealArtifact, setup::Tool};

const ANNEAL_PRELUDE: &str = include_str!("Anneal.lean");

/// Orchestrates the Aeneas translation and Lean verification process.
///
/// This function is the main entry point for the "backend" phase of Anneal.
/// It assumes that Charon has already run and produced valid LLBC files.
///
/// It requires `LockedRoots` to ensure safe, exclusive access to the
/// `lean` and `generated` output directories.
pub fn run_aeneas(
    roots: &LockedRoots,
    artifacts: &[AnnealArtifact],
    args: &crate::resolve::Args,
) -> Result<()> {
    let llbc_root = roots.llbc_root();

    // 1. Setup Lean Project Root (Temporary)
    //
    // We generate into a temporary directory first to ensure atomic updates.
    // If the process crashes during generation, the existing `lean` directory
    // will remain untouched (or if it didn't exist, we won't leave a half-baked one).
    let lean_root = roots.lean_generated_root().parent().unwrap().to_path_buf();
    let tmp_lean_root = lean_root.with_extension("tmp");
    let lean_generated_root = tmp_lean_root.join("generated");

    // Start with a clean slate in tmp
    if tmp_lean_root.exists() {
        std::fs::remove_dir_all(&tmp_lean_root).context("Failed to cleanup stale tmp directory")?;
    }
    std::fs::create_dir_all(tmp_lean_root.join("anneal"))?;

    // 2. Write Standard Library & Configuration
    let config_content = if args.allow_sorry { "axiom Anneal.allow_sorry : True\n" } else { "" };
    write_if_changed(&tmp_lean_root.join("anneal").join("Config.lean"), config_content)
        .context("Failed to write Config.lean")?;

    let mut prelude = String::new();
    prelude.push_str("import Config\n");
    if !args.allow_sorry {
        prelude.push_str("import Lean\n");
    }
    prelude.push_str(ANNEAL_PRELUDE);

    if !args.allow_sorry {
        prelude.push_str("\n\n");
        prelude.push_str("open Lean Elab Tactic Term\n\n");
        prelude.push_str("elab (priority := high) \"sorry\" : tactic =>\n");
        prelude.push_str(
            "  throwError \"The 'sorry' tactic is forbidden; use --allow-sorry to allow it.\"\n\n",
        );
        prelude.push_str("elab (priority := high) \"sorry\" : term =>\n");
        prelude.push_str(
            "  throwError \"The 'sorry' term is forbidden; use --allow-sorry to allow it.\"\n",
        );
    }

    write_if_changed(&tmp_lean_root.join("anneal").join("Anneal.lean"), &prelude)
        .context("Failed to write Anneal prelude")?;

    // 3. Write Toolchain
    write_if_changed(
        &tmp_lean_root.join("lean-toolchain"),
        &format!("{}\n", env!("ANNEAL_LEAN_TOOLCHAIN")),
    )
    .context("Failed to write Lean toolchain")?;

    let mut lake_roots = vec!["Generated".to_string()];

    for artifact in artifacts {
        if artifact.start_from.is_empty() {
            log::debug!(
                "Skipping artifact '{}' because it has no entry points",
                artifact.name.target_name
            );
            continue;
        }

        log::debug!("Invoking Aeneas on artifact '{}'...", artifact.name.target_name);

        let llbc_path = llbc_root.join(artifact.llbc_file_name());
        let slug = artifact.artifact_slug();
        // Output to `generated/<Slug>`
        let output_dir = lean_generated_root.join(&slug);

        // STALE OUTPUT CLEANUP:
        // We must ensure that the output directory is clean before running Aeneas.
        // If stale files (e.g., `Funs.lean` from a previous run) persist, they might be used
        // by Anneal even if Aeneas doesn't regenerate them (e.g. if the function was deleted).
        if output_dir.exists() {
            log::debug!("Cleaning stale output directory: {}", output_dir.display());
            std::fs::remove_dir_all(&output_dir).context("Failed to clean output directory")?;
        }

        std::fs::create_dir_all(&output_dir).context("Failed to create Aeneas output directory")?;

        let toolchain = crate::setup::Toolchain::resolve()?;
        let mut cmd = toolchain.command(Tool::Aeneas);

        cmd.args(["-backend", "lean"])
            .arg("-dest")
            .arg(&output_dir)
            .args(["-split-files", "-abort-on-error"])
            .arg(&llbc_path);

        log::debug!("Command: {:?}", cmd);

        let start = std::time::Instant::now();
        let output = cmd.output().context("Failed to spawn aeneas")?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            bail!(
                "Aeneas failed for package '{}' with status: {}\nstderr:\n{}",
                artifact.name.package_name,
                output.status,
                stderr
            );
        } else {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            log::trace!("Aeneas stdout:\n{}", stdout);
            log::trace!("Aeneas stderr:\n{}", stderr);
        }
        log::trace!("Aeneas for '{}' took {:.2?}", artifact.name.target_name, start.elapsed());

        // Aeneas might not generate Funs.lean or Types.lean if there are no
        // functions/types. However, `Specs.lean` and `Generated.lean` expect
        // them to exist (as imports).
        //
        // If Anneal found items that *should* result in these files being
        // generated, but they are missing, this indicates an Aeneas failure
        // (e.g. valid Rust code that Aeneas failed to translate). In this
        // case, we error out rather than creating an empty file to prevent
        // silent failures.
        let funs_path = output_dir.join("Funs.lean");
        if !funs_path.exists() {
            if artifact.has_functions() {
                bail!(
                    "Aeneas failed to generate Funs.lean for '{}', but Anneal found function/impl items in the source.\n\
                     This indicates that Aeneas silently failed to translate some items.",
                    slug
                );
            }
            log::debug!(
                "Funs.lean missing for {}, creating empty file. (No functions found by Anneal)",
                slug
            );
            std::fs::write(&funs_path, "def dummy := ()\n").context("Failed to create empty Funs.lean")?;
        } else {
            // Aeneas generates `def` for all functions. If a function calls an opaque
            // translated function (which emits as an `axiom`), Lean's bytecode compiler
            // will reject it unless it's marked `noncomputable`. Since Anneal verification
            // never executes these functions directly in Lean, we safely wrap the entire
            // `Funs.lean` file in a `noncomputable section` to suppress these errors.
            let content =
                std::fs::read_to_string(&funs_path).context("Failed to read Funs.lean")?;
            let patched = patch_funs(&content);
            std::fs::write(&funs_path, patched).context("Failed to write patched Funs.lean")?;
        }

        let types_path = output_dir.join("Types.lean");
        if !types_path.exists() {
            if artifact.has_types() {
                bail!(
                    "Aeneas failed to generate Types.lean for '{}', but Anneal found type/trait items in the source.\n\
                     This indicates that Aeneas silently failed to translate some items.",
                    slug
                );
            }
            log::debug!(
                "Types.lean missing for {}, creating empty file. (No types found by Anneal)",
                slug
            );
            std::fs::write(&types_path, "def dummy := ()\n").context("Failed to create empty Types.lean")?;
        } else {
            // We patch the generated `Types.lean` file because Aeneas's code generator
            // outputs `@[discriminant]` without the requisite type argument. The Lean
            // `Aeneas.Discriminant` module expects this attribute to be parameterized
            // by an integer type (e.g., `@[discriminant isize]`). We textually replace
            // the bare attribute with the parameterized one so that Lean can successfully
            // process the file.
            let content =
                std::fs::read_to_string(&types_path).context("Failed to read Types.lean")?;
            let patched = patch_discriminants(&content);
            if patched != content {
                std::fs::write(&types_path, patched)
                    .context("Failed to write patched Types.lean")?;
            }
        }

        // Note: we let types and funs lack Prefix imports here because `aeneas_only`
        // doesn't write `Generated.lean` or `Specs.lean`, which expect them as imports.

        // Check for `FunsExternal_Template.lean`.
        //
        // This file is generated by Aeneas for functions marked as opaque (i.e.
        // `unsafe(axiom)`). It contains the type signatures of these opaque
        // functions as axioms. We copy it to `FunsExternal.lean` if it doesn't
        // exist to provide a default implementation (as axioms) so that the
        // Lean project can build successfully. Aeneas's intention with this
        // file is that users can then modify `FunsExternal.lean` if they wish
        // to provide manual implementations or proofs. In our case, that's not
        // relevant.
        let external_template_path = output_dir.join("FunsExternal_Template.lean");
        if external_template_path.exists() {
            let external_path = output_dir.join("FunsExternal.lean");
            if !external_path.exists() {
                std::fs::copy(&external_template_path, &external_path)
                    .context("Failed to copy FunsExternal_Template.lean to FunsExternal.lean")?;
            }

            lake_roots.push(format!("{}.FunsExternal", slug));
        }

        // Check for `TypesExternal_Template.lean`.
        //
        // Similar to `FunsExternal_Template.lean`, this is generated by Aeneas
        // for opaque types or traits.
        let types_external_template_path = output_dir.join("TypesExternal_Template.lean");
        if types_external_template_path.exists() {
            let types_external_path = output_dir.join("TypesExternal.lean");
            if !types_external_path.exists() {
                std::fs::copy(&types_external_template_path, &types_external_path)
                    .context("Failed to copy TypesExternal_Template.lean to TypesExternal.lean")?;
            }

            lake_roots.push(format!("{}.TypesExternal", slug));
        }

        // Register the generated modules as roots for the Lake library.
        //
        // The `slug` is guaranteed to be PascalCase and alphanumeric (see
        // `AnnealArtifact::artifact_slug`), so it is always a valid Lean identifier.
        // We can safely append `.Funs` and `.Types` without needing complex escaping
        // or guillemets (`«...»`) in the Lake configuration.
        //
        // These roots will be prefixed with a backtick (e.g., `Slug.Funs) in
        // the generated Lakefile, which is the standard syntax for Name literals in Lean.
        lake_roots.push(format!("{}.Funs", slug));
        lake_roots.push(format!("{}.Types", slug));
    }

    // 4. Write Lakefile
    //
    // If `ANNEAL_AENEAS_DIR` is set (e.g., in CI or local development via Docker),
    // we use it. Otherwise, we default to the managed toolchain directory.
    let toolchain = crate::setup::Toolchain::resolve()?;
    let path = toolchain.root.display();
    let aeneas_dep = format!(
        r#"require aeneas from git "file://{path}/backends/lean" @ "main" -- {}"#,
        env!("ANNEAL_AENEAS_REV")
    );

    let roots_str = lake_roots.iter().map(|r| format!("`{}", r)).collect::<Vec<_>>().join(", ");

    let lakefile = format!(
        r#"
import Lake
open Lake DSL

{aeneas_dep}

package anneal_verification

@[default_target]
lean_lib «Generated» where
  srcDir := "generated"
  roots := #[{roots_str}]

@[default_target]
lean_lib «Anneal» where
  srcDir := "anneal"
  roots := #[`Config, `Anneal]

lean_lib «User» where
  srcDir := "user"
"#
    );
    write_if_changed(&tmp_lean_root.join("lakefile.lean"), &lakefile)
        .context("Failed to write Lakefile")?;

    // ATOMIC SWAP: If we successfully generated everything, we now swap the
    // temporary directory with the real one.
    let lean_root = roots.lean_root();
    if lean_root.exists() {
        // Preserve the `.lake` directory and manifest to prevent re-downloading
        // dependencies (like Mathlib) on subsequent runs.
        let old_lake = lean_root.join(".lake");
        let old_manifest = lean_root.join("lake-manifest.json");
        if old_lake.exists() {
            fs::rename(&old_lake, tmp_lean_root.join(".lake"))?;
        }
        if old_manifest.exists() {
            fs::rename(&old_manifest, tmp_lean_root.join("lake-manifest.json"))?;
        }

        // Remove the existing directory before renaming the temporary directory.
        // Note: `fs::rename` on Unix typically requires the target directory to be
        // empty if it exists. While not strictly atomic (there is a brief window
        // where the directory is missing), this prevents a half-written state.
        log::debug!("Removing existing lean directory: {}", lean_root.display());
        fs::remove_dir_all(&lean_root).context("Failed to remove existing lean directory")?;
    }

    log::debug!("Renaming {} to {}", tmp_lean_root.display(), lean_root.display());
    fs::rename(&tmp_lean_root, &lean_root)
        .context("Failed to rename temporary lean directory to target")?;

    Ok(())
}

/// Generates Anneal `Specs.lean` and writes `Generated.lean`, but does not run the `lake build`.
pub fn generate_lean_workspace(roots: &LockedRoots, artifacts: &[AnnealArtifact]) -> Result<()> {
    let lean_generated_root = roots.lean_generated_root();
    let mut generated_imports = String::new();

    for artifact in artifacts {
        if artifact.start_from.is_empty() {
            continue;
        }

        let slug = artifact.artifact_slug();
        let output_dir = lean_generated_root.join(&slug);

        // Generate Anneal specs
        let generated = generate::generate_artifact(artifact);
        let specs_path = output_dir.join(artifact.lean_spec_file_name());
        let map_path = output_dir.join(format!("{}.lean.map", artifact.artifact_slug()));

        std::fs::write(&specs_path, &generated.code)
            .with_context(|| format!("Failed to write specs to {}", specs_path.display()))?;

        // Write Source Map
        let map_json = serde_json::to_string(&generated.mappings)
            .context("Failed to serialize source mappings")?;
        std::fs::write(&map_path, map_json)
            .with_context(|| format!("Failed to write source map to {}", map_path.display()))?;

        // Build imports for Generated.lean
        writeln!(generated_imports, "import «{}».Funs", slug).unwrap();
        writeln!(generated_imports, "import «{}».Types", slug).unwrap();

        if output_dir.join("FunsExternal.lean").exists() {
            writeln!(generated_imports, "import «{}».FunsExternal", slug).unwrap();
        }
        if output_dir.join("TypesExternal.lean").exists() {
            writeln!(generated_imports, "import «{}».TypesExternal", slug).unwrap();
        }
    }

    write_if_changed(&lean_generated_root.join("Generated.lean"), &generated_imports)
        .context("Failed to write Generated.lean")?;

    // To avoid a slow full rebuild of dependencies in the newly generated
    // workspace, we manually materialize the dependencies and fix up Lake's
    // build trace files.
    //
    // Lake records absolute paths in its trace files. By default, when we
    // generate a workspace and run `lake build`, Lake clones the dependencies
    // into the workspace's `.lake/packages` directory. Since the paths in the
    // clone do not match the paths in the toolchain where dependencies were
    // pre-built, Lake considers the traces invalid and rebuilds everything.
    //
    // We bypass this by:
    // - Manually writing the manifest with local file URLs.
    // - Copying the pre-built dependency directories directly from the
    //   toolchain to avoid cloning.
    // - Post-processing the trace files to replace toolchain paths with
    //   workspace paths.

    // We read the `lake-manifest.json` generated during toolchain setup,
    // modify it to include Aeneas as a dependency, and write it directly to
    // the workspace. This prevents Lake from running dependency resolution
    // and post-update hooks that would attempt to download external assets.
    println!("Writing modified manifest to generated workspace...");
    let lean_root = roots.lean_root();
    let toolchain = crate::setup::Toolchain::resolve()?;
    let toolchain_manifest_path =
        toolchain.root.join("backends").join("lean").join("lake-manifest.json");
    let user_manifest_path = lean_root.join("lake-manifest.json");

    if toolchain_manifest_path.exists() {
        let content = fs::read_to_string(&toolchain_manifest_path)
            .context("Failed to read toolchain manifest")?;
        let mut manifest: serde_json::Value =
            serde_json::from_str(&content).context("Failed to parse toolchain manifest")?;

        // Change name to anneal_verification
        manifest["name"] = serde_json::Value::String("anneal_verification".to_string());

        // Read actual HEAD commit of Aeneas in toolchain
        let toolchain_aeneas_dir = toolchain.root.join("backends").join("lean");
        let output = Command::new("git")
            .args(["rev-parse", "HEAD"])
            .current_dir(&toolchain_aeneas_dir)
            .output()
            .context("Failed to run `git rev-parse HEAD` in toolchain Aeneas")?;

        if !output.status.success() {
            bail!("`git rev-parse HEAD` failed in toolchain Aeneas");
        }
        let aeneas_rev = String::from_utf8(output.stdout)
            .context("Failed to parse git output")?
            .trim()
            .to_string();

        // Inject aeneas dependency
        let aeneas_dep = serde_json::json!({
            "configFile": "lakefile.lean",
            "inherited": false,
            "inputRev": "main",
            "manifestFile": "lake-manifest.json",
            "name": "aeneas",
            "rev": aeneas_rev,
            "scope": "",
            "subDir": null,
            "type": "git",
            "url": format!("file://{}", toolchain_aeneas_dir.to_str().unwrap())
        });

        if let Some(packages) = manifest["packages"].as_array_mut() {
            packages.insert(0, aeneas_dep);
        } else {
            bail!("Manifest packages is not an array");
        }

        let new_content = serde_json::to_string_pretty(&manifest)
            .context("Failed to serialize modified manifest")?;
        fs::write(&user_manifest_path, new_content).context("Failed to write user manifest")?;
    } else {
        bail!("Toolchain manifest missing at {}", toolchain_manifest_path.display());
    }

    // We manually copy the Aeneas package and all resolved dependencies from
    // the toolchain into the workspace's `.lake/packages` directory. This
    // populates the clones with the pre-built `.lake/build` artifacts.
    // We also update the Git remote URL in each clone to match the local
    // file URLs in the manifest, preventing Lake from deleting them due to
    // a URL mismatch.
    println!("Materializing packages by copying from toolchain...");
    let user_project_packages = lean_root.join(".lake").join("packages");

    // Ensure .lake/packages exists
    fs::create_dir_all(&user_project_packages)
        .context("Failed to create .lake/packages directory")?;

    // Copy Aeneas
    let toolchain_aeneas_dir = toolchain.root.join("backends").join("lean");
    let user_aeneas_dir = user_project_packages.join("aeneas");

    if toolchain_aeneas_dir.exists() {
        if user_aeneas_dir.exists() {
            fs::remove_dir_all(&user_aeneas_dir)
                .context("Failed to remove existing Aeneas directory in workspace")?;
        }
        let status = Command::new("cp")
            .args(["-r", toolchain_aeneas_dir.to_str().unwrap(), user_aeneas_dir.to_str().unwrap()])
            .status()
            .context("Failed to copy Aeneas directory")?;
        if !status.success() {
            bail!("Failed to copy Aeneas directory from toolchain to workspace");
        }

        // Add Git remote 'origin' to match manifest
        let status = Command::new("git")
            .args([
                "remote",
                "add",
                "origin",
                &format!("file://{}", toolchain_aeneas_dir.to_str().unwrap()),
            ])
            .current_dir(&user_aeneas_dir)
            .status()
            .context("Failed to run `git remote add` in Aeneas clone")?;
        if !status.success() {
            bail!("`git remote add` failed in Aeneas clone");
        }
    }

    // Copy dependencies
    let toolchain_packages_dir = toolchain.root.join("packages");
    if toolchain_packages_dir.exists() {
        for entry in fs::read_dir(&toolchain_packages_dir)
            .context("Failed to read toolchain packages directory")?
        {
            let entry = entry.context("Failed to read directory entry")?;
            let path = entry.path();
            if path.is_dir() {
                let pkg_name = path.file_name().unwrap().to_str().unwrap();
                let user_pkg_dir = user_project_packages.join(pkg_name);

                if user_pkg_dir.exists() {
                    fs::remove_dir_all(&user_pkg_dir)
                        .context("Failed to remove existing package directory in workspace")?;
                }
                let status = Command::new("cp")
                    .args(["-r", path.to_str().unwrap(), user_pkg_dir.to_str().unwrap()])
                    .status()
                    .context("Failed to copy package directory")?;
                if !status.success() {
                    bail!("Failed to copy package directory for {}", pkg_name);
                }

                // Update Git remote URL to match manifest
                let status = Command::new("git")
                    .args([
                        "remote",
                        "set-url",
                        "origin",
                        &format!("file://{}", path.to_str().unwrap()),
                    ])
                    .current_dir(&user_pkg_dir)
                    .status()
                    .context("Failed to run `git remote set-url` in package clone")?;
                if !status.success() {
                    bail!("`git remote set-url` failed in package clone for {}", pkg_name);
                }
            }
        }
    }

    // Finally, we fix the non-portable absolute paths embedded in Lake's
    // `.trace` files. We replace all occurrences of paths pointing to the
    // toolchain with the corresponding paths in the workspace's clone
    // directory. This convinces Lake that the pre-built artifacts are valid
    // for the current workspace location.
    println!("Post-processing traces in the clone...");
    let toolchain_aeneas = toolchain.root.join("backends").join("lean");
    let toolchain_aeneas_str = toolchain_aeneas.to_str().unwrap();
    let user_project_aeneas = user_project_packages.join("aeneas");
    let user_project_aeneas_str = user_project_aeneas.to_str().unwrap();
    let toolchain_packages_str = toolchain_packages_dir.to_str().unwrap();
    let user_project_packages_str = user_project_packages.to_str().unwrap();

    let process_build_dir = |dir: &Path| -> Result<()> {
        if dir.exists() {
            let walker = WalkDir::new(dir).into_iter();
            for entry in walker {
                let entry = entry.context("Failed to walk build directory")?;
                let path = entry.path();
                if path.is_file() && path.extension().map_or(false, |ext| ext == "trace") {
                    let content = fs::read_to_string(path).context("Failed to read trace file")?;
                    let mut new_content =
                        content.replace(toolchain_aeneas_str, user_project_aeneas_str);
                    new_content =
                        new_content.replace(toolchain_packages_str, user_project_packages_str);

                    if new_content != content {
                        fs::write(path, new_content).context("Failed to write trace file")?;
                    }
                }
            }
        }
        Ok(())
    };

    // Process all packages in .lake/packages
    if user_project_packages.exists() {
        for entry in
            fs::read_dir(&user_project_packages).context("Failed to read user project packages")?
        {
            let entry = entry.context("Failed to read directory entry")?;
            let path = entry.path();
            if path.is_dir() {
                process_build_dir(&path.join(".lake").join("build"))?;
            }
        }
    }

    Ok(())
}

/// Completes Lean verification by generating Anneal `Specs.lean`, writing `Generated.lean`,
/// and running `lake build` + diagnostics.
pub fn verify_lean_workspace(roots: &LockedRoots, artifacts: &[AnnealArtifact], args: &crate::resolve::Args) -> Result<()> {
    generate_lean_workspace(roots, artifacts)?;
    run_lake(roots, artifacts, args)
}

/// Runs the Lean build process and diagnostics.
///
/// This function:
/// 1. Patches `lake-manifest.json` if `ANNEAL_AENEAS_DIR` is set (for local dev).
/// 2. Fetches Mathlib cache to avoid rebuilding it.
/// 3. Builds the project with `lake build`.
/// 4. Executes the `Diagnostics.lean` script to check proofs.
/// 5. Parses JSON output from the script and maps it back to Rust source.
fn run_lake(roots: &LockedRoots, artifacts: &[AnnealArtifact], args: &crate::resolve::Args) -> Result<()> {
    let generated = roots.lean_generated_root();
    let lean_root = generated.parent().unwrap();
    log::info!("Running 'lake build' in {}", lean_root.display());

    if !lean_root.join(".lake/packages/mathlib").exists() {
        let toolchain = crate::setup::Toolchain::resolve()?;
        // 1. Run 'lake exe cache get' to fetch pre-built Mathlib artifacts
        // This prevents compiling Mathlib from source, which is slow and disk-heavy.
        let mut cache_cmd = toolchain.command(Tool::Lake);
        cache_cmd.args(["exe", "cache", "get"]);
        cache_cmd.current_dir(lean_root);
        cache_cmd.stdout(Stdio::piped());
        cache_cmd.stderr(Stdio::piped());

        log::debug!("Running 'lake exe cache get'...");
        let start = std::time::Instant::now();
        if let Ok(output) = cache_cmd.output() {
            if !output.status.success() {
                log::warn!(
                    " 'lake exe cache get' failed (status={}). Falling back to full build.\nstderr: {}",
                    output.status,
                    String::from_utf8_lossy(&output.stderr)
                );
            }
        } else {
            log::warn!("Failed to spawn 'lake exe cache get'");
        }
        log::trace!("'lake exe cache get' took {:.2?}", start.elapsed());
    }

    // 2. Build the project (dependencies only)
    let toolchain = crate::setup::Toolchain::resolve()?;
    let mut cmd = toolchain.command(Tool::Lake);
    cmd.args(["build", "Generated", "Anneal"]);
    cmd.current_dir(lean_root);
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());

    let start = std::time::Instant::now();
    let mut child = cmd.spawn().context("Failed to spawn lake")?;

    // Capture stderr in background
    let stderr_buffer = Arc::new(Mutex::new(Vec::new()));
    let stderr_clone = stderr_buffer.clone();
    let stderr_handle = child.stderr.take().map(|stderr| {
        std::thread::spawn(move || {
            let reader = BufReader::new(stderr);
            for line in reader.lines().map_while(Result::ok) {
                stderr_clone.lock().unwrap().push(line);
            }
        })
    });

    // UI Spinner
    let pb = ProgressBar::new_spinner();
    pb.set_style(ProgressStyle::default_spinner().template("{spinner:.green} {msg}").unwrap());
    pb.enable_steady_tick(std::time::Duration::from_millis(100));
    pb.set_message("Building Lean dependencies...");

    // Capture stdout in background (while ticking progress bar)
    let stdout_buffer = Arc::new(Mutex::new(Vec::new()));
    let stdout_clone = stdout_buffer.clone();
    let pb_clone = pb.clone();

    let stdout_handle = child.stdout.take().map(|stdout| {
        std::thread::spawn(move || {
            let reader = BufReader::new(stdout);
            for line in reader.lines().map_while(Result::ok) {
                stdout_clone.lock().unwrap().push(line);
                pb_clone.tick();
            }
        })
    });

    let status = child.wait().context("Failed to wait for lake")?;
    pb.finish_and_clear();
    log::trace!("'lake build' took {:.2?}", start.elapsed());

    // Join the threads to ensure we have all logs
    if let Some(handle) = stderr_handle
        && let Err(e) = handle.join()
    {
        log::error!("Stderr reading thread panicked: {:?}", e);
    }
    if let Some(handle) = stdout_handle
        && let Err(e) = handle.join()
    {
        log::error!("Stdout reading thread panicked: {:?}", e);
    }

    if !status.success() {
        let stderr = stderr_buffer.lock().unwrap().join("\n");
        let stdout = stdout_buffer.lock().unwrap().join("\n");
        bail!("Lean build failed\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }

    // 3. Run Diagnostics
    log::info!("Running Lean diagnostics...");
    let mut has_errors = false;
    let mut mapper = crate::diagnostics::DiagnosticMapper::new(roots.workspace().clone());

    for artifact in artifacts {
        let slug = artifact.artifact_slug();
        // The path in generated file is `generated/Slug/Specs.lean`
        // We construct the relative path from the Lake root (which is `target/anneal/<hash>/lean`)
        let specs_rel_path = format!("generated/{}/{}", slug, artifact.lean_spec_file_name());

        let toolchain = crate::setup::Toolchain::resolve()?;
        let mut cmd = toolchain.command(Tool::Lake);
        cmd.args(["env", "lean", "--json", &specs_rel_path]);
        cmd.current_dir(lean_root);
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());

        let output = cmd.output().context("Failed to run lean compiler")?;

        let output_str = format!("{}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
        let specs_abs_path = lean_root.join(&specs_rel_path);
        let specs_source = std::fs::read_to_string(&specs_abs_path).unwrap_or_default();

        let mut diags = Vec::new();
        for line in output_str.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            match serde_json::from_str::<NativeLeanDiagnostic>(line) {
                Ok(diag) => diags.push(diag),
                Err(e) => {
                    log::warn!("Failed to parse JSON from lean diagnostic: {e}");
                    log::debug!("Raw line:\n{line}");
                }
            }
        }

        if !output.status.success() && diags.is_empty() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            if !stderr.trim().is_empty() {
                if !(args.allow_sorry && stderr.contains("sorry")) {
                    eprintln!("Lean compiler failed or produced stderr for {slug}.");
                    eprintln!("STDERR:\n{stderr}");
                    has_errors = true;
                }
            }
        }

        // Load Source Map
        let map_path = lean_root.join(format!("generated/{}/{}.lean.map", slug, slug));
        let mappings: Vec<crate::generate::SourceMapping> = if map_path.exists() {
            let f = std::fs::File::open(&map_path)
                .with_context(|| format!("Failed to open source map {}", map_path.display()));
            match f {
                Ok(f) => serde_json::from_reader(f).unwrap_or_else(|e| {
                    log::warn!("Failed to parse source map: {}", e);
                    Vec::new()
                }),
                Err(e) => {
                    log::warn!("Source map error: {}", e);
                    Vec::new()
                }
            }
        } else {
            Vec::new()
        };

        for nat_diag in diags {
            let level = match nat_diag.severity.as_str() {
                "error" => crate::diagnostics::DiagnosticLevel::Error,
                "warning" => crate::diagnostics::DiagnosticLevel::Warning,
                "information" => crate::diagnostics::DiagnosticLevel::Note,
                _ => crate::diagnostics::DiagnosticLevel::Note,
            };

            if matches!(level, crate::diagnostics::DiagnosticLevel::Error) {
                if !(args.allow_sorry && nat_diag.data.contains("sorry")) {
                    has_errors = true;
                }
            }

            let byte_start =
                resolve_byte_offset(&specs_source, nat_diag.pos.line, nat_diag.pos.column);
            let byte_end = if let Some(end_pos) = &nat_diag.end_pos {
                resolve_byte_offset(&specs_source, end_pos.line, end_pos.column)
            } else {
                byte_start
            };

            let diag = LeanDiagnostic {
                file_name: nat_diag.file_name.clone(),
                byte_start,
                byte_end,
                line_start: nat_diag.pos.line,
                column_start: nat_diag.pos.column,
                line_end: nat_diag.end_pos.as_ref().map_or(nat_diag.pos.line, |p| p.line),
                column_end: nat_diag.end_pos.as_ref().map_or(nat_diag.pos.column, |p| p.column),
                message: nat_diag.data.clone(),
            };

            // Map span
            // We look for the first mapping that overlaps with the diagnostic span.
            // Diagnostic span: [d_start, d_end)
            // Mapping span: [m.lean_start, m.lean_end)
            // Overlap: m.lean_start < d_end && m.lean_end > d_start
            let (file, start, end) = resolve_mapping(&diag, &mappings);
            mapper.render_raw(&file, diag.message, level, start, end, |s| eprintln!("{s}"));
        }
    }

    if has_errors {
        let cmd = if std::env::var("__ZEROCOPY_LOCAL_DEV").is_ok() {
            "cargo run generate"
        } else {
            "cargo anneal generate"
        };
        bail!(
            "Lean verification failed. Consider running `{cmd}`, iterating on generated `.lean` files, and copying results back to `.rs` files."
        );
    }

    Ok(())
}

/// Resolves a Lean diagnostic to a Rust source location.
///
/// This uses the JSON source map generated during `src/generate.rs` to map
/// the byte range in the generated Lean file back to the original Rust file.
///
/// It also implements a heuristic to redirect "declaration uses `sorry`" errors from the
/// synthetic function spec name to the `proof` or `axiom` keyword, which is more
/// intuitive for the user.
fn resolve_mapping(
    diag: &LeanDiagnostic,
    mappings: &[crate::generate::SourceMapping],
) -> (String, usize, usize) {
    let overlapping: Vec<_> = mappings
        .iter()
        .filter(|m| {
            let i_start = std::cmp::max(m.lean_start, diag.byte_start);
            let i_end = std::cmp::min(m.lean_end, diag.byte_end);
            i_start < i_end
        })
        .collect();

    let mapping = overlapping.first().copied();

    // Certain diagnostics, such as "declaration uses `sorry`", are reported on
    // the synthetic theorem name rather than the proof block itself. To improve
    // the user experience, we attempt to redirect these diagnostics to the
    // relevant keyword (e.g., `proof` or `axiom`) if a corresponding mapping
    // exists in the same file.
    let (is_redirected, mapping) = match mapping {
        Some(m)
            if diag.message.contains("declaration uses `sorry`")
                && matches!(m.kind, crate::generate::MappingKind::Synthetic) =>
        {
            // Find a Keyword mapping that is physically located inside this synthetic
            // theorem's generated Lean code.
            let next_synthetic_lean_start = mappings
                .iter()
                .filter(|m3| {
                    matches!(m3.kind, crate::generate::MappingKind::Synthetic)
                        && m3.lean_start > m.lean_end
                })
                .map(|m3| m3.lean_start)
                .min()
                .unwrap_or(usize::MAX);

            let redirected = mappings
                .iter()
                .find(|m2| {
                    matches!(m2.kind, crate::generate::MappingKind::Keyword)
                        && m2.source_file == m.source_file
                        && m2.lean_start > m.lean_end
                        && m2.lean_start < next_synthetic_lean_start
                })
                .or(Some(m));
            (true, redirected)
        }
        _ => (false, mapping),
    };

    if let Some(m) = mapping {
        if !is_redirected && overlapping.len() > 1 {
            let first = m;
            let last = overlapping
                .iter()
                .rev()
                .find(|m2| m2.source_file == first.source_file)
                .unwrap_or(&first);

            let i_start = std::cmp::max(first.lean_start, diag.byte_start);
            let offset_start = i_start - first.lean_start;
            let s_start = first.source_start + offset_start;

            let i_end = std::cmp::min(last.lean_end, diag.byte_end);
            let offset_end = i_end - last.lean_start;
            let s_end = last.source_start + offset_end;

            (first.source_file.to_string_lossy().to_string(), s_start, s_end)
        } else {
            // Calculate the intersection of the mapping span and the diagnostic
            // span to determine the precise source location.
            let i_start = std::cmp::max(m.lean_start, diag.byte_start);
            let i_end = std::cmp::min(m.lean_end, diag.byte_end);

            if i_end > i_start {
                let offset = i_start - m.lean_start;
                let len = i_end - i_start;
                let s_start = m.source_start + offset;
                let s_end = s_start + len;
                (m.source_file.to_string_lossy().to_string(), s_start, s_end)
            } else {
                // If there is no overlap (e.g., due to redirection), fallback to
                // the full mapping source span.
                (m.source_file.to_string_lossy().to_string(), m.source_start, m.source_end)
            }
        }
    } else {
        (diag.file_name.clone(), diag.byte_start, diag.byte_end)
    }
}

#[derive(Debug)]
struct LeanDiagnostic {
    file_name: String,
    byte_start: usize,
    byte_end: usize,
    #[allow(dead_code)]
    line_start: usize,
    #[allow(dead_code)]
    column_start: usize,
    #[allow(dead_code)]
    line_end: usize,
    #[allow(dead_code)]
    column_end: usize,
    message: String,
}

#[derive(serde::Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct NativeLeanDiagnostic {
    file_name: String,
    data: String,
    severity: String,
    pos: LeanPos,
    end_pos: Option<LeanPos>,
}

#[derive(serde::Deserialize, Debug)]
struct LeanPos {
    line: usize,
    column: usize,
}

fn resolve_byte_offset(source: &str, lean_line: usize, lean_column: usize) -> usize {
    if lean_line == 0 {
        return 0;
    }
    let mut current_line = 1;

    let mut iter = source.char_indices();
    while current_line < lean_line {
        if let Some((_, c)) = iter.next() {
            if c == '\n' {
                current_line += 1;
            }
        } else {
            return source.len();
        }
    }

    let mut current_col = 0;
    for (idx, c) in iter {
        if c == '\n' || current_col == lean_column {
            return idx;
        }
        current_col += 1;
    }

    source.len()
}

/// Patches the generated Types.lean file to fix Aeneas discriminant generation.
/// Aeneas generates `@[discriminant]` without a type argument, but the Lean
/// `Aeneas.Discriminant` module expects this attribute to be parameterized.
fn patch_discriminants(content: &str) -> String {
    content.replace("@[discriminant]", "@[discriminant isize]")
}

/// Patches the generated Funs.lean file to suppress bytecode compilation errors
/// for functions that invoke opaque axioms (such as `core::mem::size_of`).
fn patch_funs(content: &str) -> String {
    // Aeneas misses `show` keyword when renaming arguments in Lean.
    // We manually rename it to `show1` to match Aeneas's convention for other keywords.
    let content = content.replace("(show :", "(show1 :");

    let mut lines: Vec<&str> = content.split('\n').collect();
    let mut insert_idx = 0;
    for (i, line) in lines.iter().enumerate() {
        if line.starts_with("import ") {
            insert_idx = i + 1;
        }
    }
    lines.insert(insert_idx, "noncomputable section\n");
    lines.join("\n")
}

/// Helper to write file content only if it has changed.
///
/// This prevents updating the file's modification time (mtime) if the content is identical,
/// which helps avoid triggering unnecessary rebuilds in build systems like `lake`.
fn write_if_changed(path: &std::path::Path, content: &str) -> Result<()> {
    if path.exists() {
        let current = std::fs::read_to_string(path)?;
        if current == content {
            return Ok(()); // Skip write to preserve mtime
        }
    }
    std::fs::write(path, content).context(format!("Failed to write {:?}", path))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;
    use crate::generate::{MappingKind, SourceMapping};

    fn mk_diag(msg: &str, start: usize, end: usize) -> LeanDiagnostic {
        LeanDiagnostic {
            file_name: "test.lean".into(),
            byte_start: start,
            byte_end: end,
            line_start: 0,
            column_start: 0,
            line_end: 0,
            column_end: 0,
            message: msg.into(),
        }
    }

    fn mk_mapping(
        lean_start: usize,
        lean_end: usize,
        source_start: usize,
        source_end: usize,
        kind: MappingKind,
        file: &str,
    ) -> SourceMapping {
        SourceMapping {
            lean_start,
            lean_end,
            source_file: PathBuf::from(file),
            source_start,
            source_end,
            kind,
        }
    }

    #[test]
    fn test_resolve_mapping_cross_function_success() {
        // Function A: Proof Keyword at 100, Spec at 200
        // Diagnostic at 200 (Spec)
        // Function A: Spec name at 200 (Diagnostic Here)
        // Generated Lean: ... theorem spec ... by ...
        // Spec mapping: [50, 60) -> [200, 210)
        // Keyword mapping: [70, 80) -> [100, 110)

        let mappings = vec![
            mk_mapping(50, 60, 200, 210, MappingKind::Synthetic, "file.rs"), // spec name
            mk_mapping(70, 80, 100, 110, MappingKind::Keyword, "file.rs"),   // proof keyword
        ];
        let diag = mk_diag("declaration uses `sorry`", 50, 60);

        let (_, start, _) = resolve_mapping(&diag, &mappings);
        assert_eq!(start, 100, "Should redirect to keyword");
    }

    #[test]
    fn test_resolve_mapping_cross_file_failure() {
        // Function A (File A): Spec at 200.
        // Function B (File B): Proof Keyword at 100.
        // `m2.source_start (100) <= m.source_start (200)` is TRUE.
        // But files differ. Should NOT redirect.

        let mappings = vec![
            mk_mapping(50, 60, 200, 210, MappingKind::Synthetic, "file_a.rs"), // Func A Spec
            mk_mapping(70, 80, 100, 110, MappingKind::Keyword, "file_b.rs"),   // Func B Proof
        ];
        let diag = mk_diag("declaration uses `sorry`", 50, 60);

        let (file, start, _) = resolve_mapping(&diag, &mappings);
        assert_eq!(file, "file_a.rs");
        assert_eq!(start, 200, "Should NOT redirect across files");
    }

    #[test]
    fn test_resolve_mapping_partial_overlap() {
        // We simulate a mapping for `have h : x = 0 := by decide` from `[10, 30)` in Lean and `[100, 120)` in Rust.
        // The Lean diagnostic highlights `[5, 25)`, starting 5 bytes before the mapped code (e.g. whitespace).
        // The overlap intersection is `[10, 25)`, which has a length of 15.
        // It should map to `[100, 115)` in the Rust file.
        let mappings = vec![mk_mapping(10, 30, 100, 120, MappingKind::Source, "file.rs")];

        // 1. Overlapping from the left: Lean `[5, 25)` overlaps `[10, 30)`.
        let diag1 = mk_diag("error", 5, 25);
        let (_, start1, end1) = resolve_mapping(&diag1, &mappings);
        assert_eq!((start1, end1), (100, 115), "Should trim left non-overlapping part");

        // 2. Overlapping from the right: Lean `[20, 35)` overlaps `[10, 30)`.
        // The overlap is `[20, 30)`, length 10. Offset into Source = 10.
        // Should map to `[110, 120)`
        let diag2 = mk_diag("error", 20, 35);
        let (_, start2, end2) = resolve_mapping(&diag2, &mappings);
        assert_eq!((start2, end2), (110, 120), "Should trim right non-overlapping part");

        // 3. Complete subsumption (Lean error larger than mapping): Lean `[5, 35)` completely covers `[10, 30)`.
        // The overlap is `[10, 30)`.
        // Should map to the entire Rust bounds `[100, 120)`.
        let diag3 = mk_diag("error", 5, 35);
        let (_, start3, end3) = resolve_mapping(&diag3, &mappings);
        assert_eq!((start3, end3), (100, 120), "Should clamp completely subsuming errors");

        // 4. Exact subset: Lean `[15, 20)` is inside `[10, 30)`.
        // Overlap `[15, 20)`. length 5. Offset 5.
        // Should map to `[105, 110)`.
        let diag4 = mk_diag("error", 15, 20);
        let (_, start4, end4) = resolve_mapping(&diag4, &mappings);
        assert_eq!((start4, end4), (105, 110), "Should map exact subsets perfectly");

        // 5. Zero overlap but adjacent: Lean `[0, 10)` adjacent to `[10, 30)`.
        // i_start (10) < i_end (10) is FALSE. Should not match.
        // Fallback to "test.lean"
        let diag5 = mk_diag("error", 0, 10);
        let (file5, start5, end5) = resolve_mapping(&diag5, &mappings);
        assert_eq!(file5, "test.lean", "Should not match 0-length adjacent overlap");
        assert_eq!((start5, end5), (0, 10));
    }

    #[test]
    fn test_patch_discriminants() {
        // Standard replacement for Aeneas enum generation
        assert_eq!(
            patch_discriminants("attribute @[discriminant]\ninductive Foo"),
            "attribute @[discriminant isize]\ninductive Foo"
        );
        // EDGE CASE: If a string or doc block contains the literal it will be replaced maliciously.
        assert_eq!(
            patch_discriminants("def doc := \"This uses @[discriminant]\""),
            "def doc := \"This uses @[discriminant isize]\""
        );
        // EDGE CASE: Different `repr` attributes from Rust aren't inspected.
        assert_eq!(
            patch_discriminants("attribute @[discriminant]\n-- #[repr(u8)]"),
            "attribute @[discriminant isize]\n-- #[repr(u8)]"
        );
    }

    #[test]
    fn test_resolve_mapping_cross_function_reordering() {
        // Suppose Aeneas reorders Function A and Function B such that
        // A comes before B in Lean, but A was after B in Rust.
        let mappings = vec![
            // Func B Spec (Lean 50, Rust 200)
            mk_mapping(50, 60, 200, 210, MappingKind::Synthetic, "file.rs"),
            // Func A Spec (Lean 300, Rust 100)
            mk_mapping(300, 310, 100, 110, MappingKind::Synthetic, "file.rs"),
            // Func A Proof (Lean 350, Rust 150)
            mk_mapping(350, 360, 150, 160, MappingKind::Keyword, "file.rs"),
        ];
        let diag = mk_diag("declaration uses `sorry`", 50, 60);
        let (_, start, _) = resolve_mapping(&diag, &mappings);
        assert_eq!(
            start, 200,
            "Diagnostic should not redirect to a different function's proof keyword due to reordering"
        );
    }
}
