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
    ffi::OsString,
    fmt::Write,
    fs,
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
    process::Stdio,
    sync::{Arc, Mutex},
};

use anyhow::{Context, Result, bail, ensure};
use indicatif::{ProgressBar, ProgressStyle};
use serde_json::{Value, json};

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
    let final_lean_root = roots.lean_generated_root().parent().unwrap().to_path_buf();
    let tmp_lean_root = final_lean_root.with_extension("tmp");
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
    let toolchain = crate::setup::Toolchain::resolve()?;

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
            std::fs::write(&funs_path, "").context("Failed to create empty Funs.lean")?;
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
            std::fs::write(&types_path, "").context("Failed to create empty Types.lean")?;
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
    // Aeneas and its Lean dependencies are used directly from the managed
    // archive. The generated manifest below keeps Lake on the locked dependency
    // loading path, so package config/build caches can stay read-only.
    let path = toolchain.aeneas_lean_dir();
    let aeneas_dep = format!(
        r#"-- Aeneas rev: {}
require aeneas from "{}""#,
        env!("ANNEAL_AENEAS_REV"),
        path.display()
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
    write_lake_manifest(&tmp_lean_root, &final_lean_root, &toolchain)
        .context("Failed to write Lake manifest")?;

    // ATOMIC SWAP: If we successfully generated everything, we now swap the
    // temporary directory with the real one.
    let lean_root = roots.lean_root();
    if lean_root.exists() {
        // Preserve the `.lake` directory for generated-workspace build/config
        // caches. The Lake manifest is regenerated in the temporary directory
        // above because it records paths to the installed toolchain relative
        // to this generated workspace.
        let old_lake = lean_root.join(".lake");
        if old_lake.exists() {
            fs::rename(&old_lake, tmp_lean_root.join(".lake"))?;
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

fn write_lake_manifest(
    manifest_root: &Path,
    final_workspace_root: &Path,
    toolchain: &crate::setup::Toolchain,
) -> Result<()> {
    // We stage `lake-manifest.json` in the temporary workspace, but Lake reads
    // it after that directory has been renamed to `final_workspace_root`.
    //
    // The final `lean` directory is not the stable object here: it is absent on
    // first runs, and on reruns it is the old workspace that will be replaced.
    // Canonicalize the parent and append the final leaf so manifest paths are
    // relative to the post-rename workspace location.
    let final_workspace_root = canonical_path_after_create_or_replace(final_workspace_root)
        .with_context(|| {
            format!("Failed to resolve final Lean workspace {}", final_workspace_root.display())
        })?;
    let manifest = generated_lake_manifest(&final_workspace_root, toolchain)?;
    let mut contents =
        serde_json::to_string_pretty(&manifest).context("Failed to serialize Lake manifest")?;
    contents.push('\n');
    write_if_changed(&manifest_root.join("lake-manifest.json"), &contents)
}

fn generated_lake_manifest(
    workspace_root: &Path,
    toolchain: &crate::setup::Toolchain,
) -> Result<Value> {
    let aeneas_lean_dir = fs::canonicalize(toolchain.aeneas_lean_dir()).with_context(|| {
        format!(
            "Failed to resolve Aeneas Lake package directory {}",
            toolchain.aeneas_lean_dir().display()
        )
    })?;
    let aeneas_manifest_path = aeneas_lean_dir.join("lake-manifest.json");
    let aeneas_manifest_file = fs::File::open(&aeneas_manifest_path)
        .with_context(|| format!("Failed to open {}", aeneas_manifest_path.display()))?;
    let aeneas_manifest: Value = serde_json::from_reader(aeneas_manifest_file)
        .with_context(|| format!("Failed to parse {}", aeneas_manifest_path.display()))?;
    let aeneas_packages =
        aeneas_manifest.get("packages").and_then(Value::as_array).with_context(|| {
            format!(
                "Aeneas Lake manifest {} is missing a packages array",
                aeneas_manifest_path.display()
            )
        })?;

    let mut packages = Vec::with_capacity(aeneas_packages.len() + 1);
    let aeneas_lean_dir_manifest_path =
        path_to_manifest_string(&relative_manifest_path(&aeneas_lean_dir, workspace_root)?);
    packages.push(json!({
        "type": "path",
        "name": "aeneas",
        "dir": aeneas_lean_dir_manifest_path,
        "inherited": false,
    }));

    for entry in aeneas_packages {
        let mut entry = entry
            .as_object()
            .cloned()
            .context("Aeneas Lake manifest package entry is not an object")?;
        let package_name = entry.get("name").and_then(Value::as_str).unwrap_or("<unknown>");
        let package_type = entry.get("type").and_then(Value::as_str).with_context(|| {
            format!("Aeneas Lake manifest package entry {package_name} is missing type")
        })?;
        ensure!(
            package_type == "path",
            "Aeneas Lake manifest package entry {package_name} is {package_type:?}, not a path dependency"
        );
        let package_dir = entry.get("dir").and_then(Value::as_str).with_context(|| {
            format!("Aeneas Lake manifest package entry {package_name} is missing dir")
        })?;
        let package_dir = Path::new(package_dir);
        let package_dir = if package_dir.is_absolute() {
            package_dir.to_path_buf()
        } else {
            aeneas_lean_dir.join(package_dir)
        };
        let package_dir = fs::canonicalize(&package_dir)
            .with_context(|| format!("Failed to resolve Lake package {}", package_dir.display()))?;
        let package_dir_manifest_path =
            path_to_manifest_string(&relative_manifest_path(&package_dir, workspace_root)?);
        entry.insert("dir".to_string(), json!(package_dir_manifest_path));
        entry.insert("inherited".to_string(), json!(true));
        packages.push(Value::Object(entry));
    }

    Ok(json!({
        "version": "1.2.0",
        "packagesDir": ".lake/packages",
        "packages": packages,
        "name": "anneal_verification",
        "lakeDir": ".lake",
        "fixedToolchain": false,
    }))
}

/// Resolves the path a child will have once it is created under its current parent.
///
/// This canonicalizes ancestors without resolving the final component, which
/// may be missing or may name an old object that is about to be replaced.
fn canonical_path_after_create_or_replace(path: &Path) -> Result<PathBuf> {
    let parent = path.parent().with_context(|| format!("Path {} has no parent", path.display()))?;
    let parent = fs::canonicalize(parent)
        .with_context(|| format!("Failed to resolve parent {}", parent.display()))?;
    let file_name =
        path.file_name().with_context(|| format!("Path {} has no file name", path.display()))?;
    Ok(parent.join(file_name))
}

fn relative_manifest_path(path: &Path, base: &Path) -> Result<PathBuf> {
    pathdiff::diff_paths(path, base).with_context(|| {
        format!("Failed to compute relative path from {} to {}", base.display(), path.display())
    })
}

fn path_to_manifest_string(path: &Path) -> String {
    path.to_string_lossy().into_owned()
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

    Ok(())
}

/// Completes Lean verification by generating Anneal `Specs.lean`, writing `Generated.lean`,
/// and running `lake build` + diagnostics.
pub fn verify_lean_workspace(roots: &LockedRoots, artifacts: &[AnnealArtifact]) -> Result<()> {
    generate_lean_workspace(roots, artifacts)?;
    run_lake(roots, artifacts)
}

/// Runs the Lean build process and diagnostics.
///
/// This function builds the generated project, runs Lean diagnostics, and maps
/// diagnostics back to Rust source.
fn run_lake(roots: &LockedRoots, artifacts: &[AnnealArtifact]) -> Result<()> {
    let generated = roots.lean_generated_root();
    let lean_root = generated.parent().unwrap();
    log::info!("Running 'lake build' in {}", lean_root.display());

    // 2. Build the project (dependencies only)
    let toolchain = crate::setup::Toolchain::resolve()?;
    let mut cmd = std::process::Command::new(toolchain.lean_bin().join("lake"));
    cmd.args(["--keep-toolchain", "--old", "build", "Generated", "Anneal"]);
    cmd.current_dir(lean_root);
    configure_lake_command(&mut cmd, &toolchain)?;
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

        let mut cmd = std::process::Command::new(toolchain.lean_bin().join("lake"));
        cmd.args(["--keep-toolchain", "env", "lean", "--json", &specs_rel_path]);
        cmd.current_dir(lean_root);
        configure_lake_command(&mut cmd, &toolchain)?;
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());

        let output = cmd.output().context("Failed to run lean compiler")?;

        let output_str = String::from_utf8_lossy(&output.stdout);
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
                eprintln!("Lean compiler failed or produced stderr for {slug}.");
                eprintln!("STDERR:\n{stderr}");
            }
            has_errors = true;
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
                has_errors = true;
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

fn configure_lake_command(
    cmd: &mut std::process::Command,
    toolchain: &crate::setup::Toolchain,
) -> Result<()> {
    // FIXME: Replace this with a cleaner toolchain/archive contract.
    //
    // The Nix-built archive contains prebuilt Lake outputs for the vendored
    // Aeneas package, and generated verification workspaces require that
    // package directly from the installed archive. That is only sound if Lake
    // evaluates Aeneas with the same build configuration that was used when the
    // archive was produced.
    //
    // Aeneas' Lakefile currently makes one of those build settings depend on
    // the ambient `CI` environment variable:
    //
    //     precompileModules := (IO.getEnv "CI").isNone
    //
    // Our archive is built without `CI` in the environment, but GitHub Actions
    // sets `CI=true` for normal workflow steps. If we let that variable reach
    // this child process, Lake observes a different Aeneas package config than
    // the one recorded in the archive traces. It then invalidates the prebuilt
    // cache and attempts to rebuild/remove files below the installed archive's
    // read-only `.lake/build`.
    //
    // Scrubbing `CI` here keeps local runs, example CI jobs, and the integration
    // test harness aligned with the archive build environment. A cleaner future
    // solution would make the archive's Lake configuration explicit and
    // environment-independent, or otherwise arrange for Anneal to request the
    // exact same Aeneas build variant that the archive contains.
    cmd.env_remove("CI");

    cmd.env("LEAN_SYSROOT", toolchain.lean_sysroot());
    cmd.env("MATHLIB_NO_CACHE_ON_UPDATE", "1");
    cmd.env("PATH", prepend_paths_to_env_var("PATH", &[toolchain.lean_bin()])?);

    let lib_env_var =
        if cfg!(target_os = "macos") { "DYLD_LIBRARY_PATH" } else { "LD_LIBRARY_PATH" };
    cmd.env(
        lib_env_var,
        prepend_paths_to_env_var(
            lib_env_var,
            &[toolchain.lean_sysroot().join("lib"), toolchain.lean_sysroot().join("lib/lean")],
        )?,
    );

    Ok(())
}

fn prepend_paths_to_env_var(var_name: &str, new_paths: &[PathBuf]) -> Result<OsString> {
    let mut paths = new_paths.to_vec();
    if let Some(existing) = std::env::var_os(var_name) {
        paths.extend(std::env::split_paths(&existing));
    }
    std::env::join_paths(paths).with_context(|| format!("Failed to prepend paths to {var_name}"))
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
    use std::path::{Path, PathBuf};

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

    #[test]
    fn generated_lake_manifest_locks_archive_path_dependencies_relative_to_future_workspace() {
        let temp = tempfile::tempdir().unwrap();
        let workspace_root = temp.path().join("workspace/target/anneal/hash/lean");
        let toolchain_root = temp.path().join("toolchain");
        let aeneas_lean = toolchain_root.join("aeneas/backends/lean");
        let mathlib = toolchain_root.join("aeneas/packages/mathlib");
        let qq = toolchain_root.join("aeneas/packages/Qq");
        std::fs::create_dir_all(workspace_root.parent().unwrap()).unwrap();
        std::fs::create_dir_all(&aeneas_lean).unwrap();
        std::fs::create_dir_all(&mathlib).unwrap();
        std::fs::create_dir_all(&qq).unwrap();
        std::fs::write(
            aeneas_lean.join("lake-manifest.json"),
            serde_json::to_string(&json!({
                "version": "1.2.0",
                "packagesDir": ".lake/packages",
                "packages": [
                    {
                        "type": "path",
                        "name": "mathlib",
                        "dir": "../../packages/mathlib",
                        "inherited": false,
                    },
                    {
                        "type": "path",
                        "name": "Qq",
                        "dir": "../../packages/Qq",
                        "inherited": true,
                        "scope": "",
                    },
                ],
                "name": "aeneas",
                "lakeDir": ".lake",
                "fixedToolchain": false,
            }))
            .unwrap(),
        )
        .unwrap();

        let toolchain = crate::setup::Toolchain { root: toolchain_root };
        let workspace_root = canonical_path_after_create_or_replace(&workspace_root).unwrap();
        let manifest = generated_lake_manifest(&workspace_root, &toolchain).unwrap();
        let packages = manifest.get("packages").unwrap().as_array().unwrap();

        // The manifest is written before the workspace leaf exists. Create it
        // now to verify that the relative paths resolve after the tmp directory
        // is renamed into place.
        std::fs::create_dir_all(&workspace_root).unwrap();

        assert_eq!(packages.len(), 3);
        assert_eq!(packages[0]["name"], "aeneas");
        assert_manifest_dir_resolves(&workspace_root, &packages[0], &aeneas_lean);
        assert_eq!(packages[0]["inherited"], false);

        assert_eq!(packages[1]["name"], "mathlib");
        assert_manifest_dir_resolves(&workspace_root, &packages[1], &mathlib);
        assert_eq!(packages[1]["inherited"], true);

        assert_eq!(packages[2]["name"], "Qq");
        assert_manifest_dir_resolves(&workspace_root, &packages[2], &qq);
        assert_eq!(packages[2]["inherited"], true);
    }

    fn assert_manifest_dir_resolves(workspace_root: &Path, entry: &Value, expected: &Path) {
        let dir = entry.get("dir").unwrap().as_str().unwrap();
        assert!(Path::new(dir).is_relative(), "manifest dir should be relative: {dir}");
        assert_eq!(
            std::fs::canonicalize(workspace_root.join(dir)).unwrap(),
            std::fs::canonicalize(expected).unwrap()
        );
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
