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

use std::{fmt::Write, fs, path::Path};

use anyhow::{Context, Result, bail, ensure};
use indicatif::{ProgressBar, ProgressStyle};

use crate::{
    generate,
    lean_sdk::{LakeLibrary, LakeOperation, LeanOperation, Workspace, filesystem_folds_ascii_case},
    resolve::LockedRoots,
    scanner::AnnealArtifact,
    setup::Tool,
};

const ANNEAL_PRELUDE: &str = include_str!("Anneal.lean");
const SOURCE_ROOTS: &[&str] = &["anneal", "generated", "user"];

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
    let final_lean_root = roots.lean_root();
    let parent = final_lean_root.parent().context("Lean workspace has no parent")?;
    fs::create_dir_all(parent)?;
    let toolchain = crate::setup::Toolchain::resolve()?;
    let selected_sdk = toolchain.lean_sdk()?;
    ensure!(
        !path_entry_exists(&final_lean_root.with_extension("previous"))?,
        "Interrupted workspace swap at {}; recover preserved sources/outputs before retry",
        final_lean_root.with_extension("previous").display()
    );
    let existing = if final_lean_root.try_exists()? {
        let workspace = Workspace::from_root(&final_lean_root)?;
        ensure!(workspace.sdk().id() == selected_sdk.id(), "Workspace SDK identity changed");
        Some(workspace)
    } else {
        None
    };
    // A Rust-only archive change may install identical Lean inputs at a new
    // distribution path. Keep the original physical SDK binding and outputs;
    // a different Lean identity already selects a fresh workspace leaf.
    let sdk = existing.as_ref().map_or(selected_sdk, |workspace| workspace.sdk().clone());
    let old_snapshot = existing.as_ref().map(Workspace::source_snapshot).transpose()?;
    let stage = tempfile::Builder::new().prefix(".anneal-stage-").tempdir_in(parent)?;
    let tmp_lean_root = stage.path().join("workspace");
    Workspace::stage(&sdk, &tmp_lean_root, &final_lean_root, existing.as_ref(), SOURCE_ROOTS)?;
    fs::create_dir(tmp_lean_root.join("anneal"))?;
    if let Some(existing) = &existing {
        let user = existing.root().join("user");
        if user.try_exists()? {
            copy_source_tree(&user, &tmp_lean_root.join("user"))?;
        }
    }
    let lean_generated_root = tmp_lean_root.join("generated");

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
        &format!("{}\n", sdk.root().to_str().context("SDK path is not UTF-8")?),
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

    // Shared modules belong to the installation, never Lake path packages.
    fs::create_dir_all(tmp_lean_root.join("user"))?;
    let folds_case = filesystem_folds_ascii_case(&tmp_lean_root.join(".anneal-sdk.json"))?;
    let user_modules = local_module_names(&tmp_lean_root.join("user"), folds_case)?;
    Workspace::write_lakefile(
        &sdk,
        &tmp_lean_root,
        &[
            LakeLibrary { name: "Generated", source_root: "generated", modules: &lake_roots },
            LakeLibrary {
                name: "Anneal",
                source_root: "anneal",
                modules: &["Config".into(), "Anneal".into()],
            },
            LakeLibrary { name: "User", source_root: "user", modules: &user_modules },
        ],
    )?;
    write_if_changed(&tmp_lean_root.join("lake-manifest.json"), EMPTY_MANIFEST)?;
    generate_sources(&lean_generated_root, artifacts)?;
    crate::lean_gateway::write_editor_gateway(&tmp_lean_root, &final_lean_root)?;
    Workspace::admit_stage(&sdk, &tmp_lean_root, &final_lean_root)?;
    if let Some(existing) = &existing {
        preserve_unchanged_mtimes(existing.root(), &tmp_lean_root)?;
        existing.admit()?;
    }
    // Generation failures discard only the new stage. Once output transfer
    // begins, retain that stage on error so owned incremental outputs survive.
    let recovery = stage.keep();
    install_stage(
        &tmp_lean_root,
        &final_lean_root,
        existing.is_some(),
        || {
            if let (Some(existing), Some(baseline)) = (&existing, &old_snapshot) {
                ensure!(
                    existing.source_stamp()? == baseline.stamp(),
                    "Lean inputs changed during generation; preserve the edited old workspace"
                );
            }
            Ok(())
        },
        |backup| {
            if let (Some(existing), Some(baseline)) = (&existing, &old_snapshot) {
                ensure!(
                    existing.source_stamp_at(backup, baseline)? == baseline.stamp(),
                    "Lean inputs changed during isolation; preserve the edited old workspace"
                );
            }
            Ok(())
        },
    )
    .with_context(|| format!("Workspace swap failed; recoverable stage: {}", recovery.display()))?;
    fs::remove_dir(recovery)?;
    Workspace::open(&sdk, &final_lean_root)?;
    Ok(())
}

const EMPTY_MANIFEST: &str = r#"{
  "version": "1.2.0", "packagesDir": ".lake/packages", "packages": [],
  "name": "anneal_verification", "lakeDir": ".lake", "fixedToolchain": true
}
"#;

fn local_module_names(root: &Path, folds_case: bool) -> Result<Vec<String>> {
    let mut modules = Vec::new();
    for entry in walkdir::WalkDir::new(root).follow_links(false) {
        let entry = entry?;
        ensure!(!entry.file_type().is_symlink(), "Local source contains a symlink");
        if entry.file_type().is_file()
            && entry
                .path()
                .extension()
                .and_then(|s| s.to_str())
                .is_some_and(|s| s == "lean" || (folds_case && s.eq_ignore_ascii_case("lean")))
        {
            let relative = entry.path().strip_prefix(root)?.with_extension("");
            let parts = relative
                .iter()
                .map(|part| part.to_str().context("Non-UTF8 Lean module path"))
                .collect::<Result<Vec<_>>>()?;
            ensure!(
                parts.iter().all(|part| !part.contains('.')),
                "Lean module filename components cannot contain dots: {}",
                entry.path().display()
            );
            modules.push(parts.join("."));
        }
    }
    modules.sort();
    Ok(modules)
}

fn copy_source_tree(source: &Path, destination: &Path) -> Result<()> {
    ensure!(fs::symlink_metadata(source)?.is_dir(), "Source directory is not physical");
    fs::create_dir(destination)?;
    for entry in fs::read_dir(source)? {
        let entry = entry?;
        let kind = entry.file_type()?;
        ensure!(!kind.is_symlink(), "Source contains a symlink");
        if kind.is_dir() {
            copy_source_tree(&entry.path(), &destination.join(entry.file_name()))?;
        } else {
            ensure!(kind.is_file(), "Source contains a special file");
            fs::copy(entry.path(), destination.join(entry.file_name()))?;
        }
    }
    Ok(())
}

fn preserve_unchanged_mtimes(old: &Path, stage: &Path) -> Result<()> {
    for entry in walkdir::WalkDir::new(stage).follow_links(false) {
        let entry = entry?;
        if !entry.file_type().is_file() {
            continue;
        }
        let path = entry.path();
        let prior = old.join(path.strip_prefix(stage)?);
        if prior.is_file() && fs::read(&prior)? == fs::read(path)? {
            let modified = fs::metadata(prior)?.modified()?;
            fs::File::options()
                .write(true)
                .open(path)?
                .set_times(fs::FileTimes::new().set_modified(modified))?;
        }
    }
    Ok(())
}

fn path_entry_exists(path: &Path) -> Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error.into()),
    }
}

/// A same-SDK source replacement transfers whole owned output trees. A failed
/// transfer leaves named recovery objects; it never adopts a partial workspace.
fn install_stage(
    stage: &Path,
    final_root: &Path,
    existing: bool,
    validate_live: impl FnOnce() -> Result<()>,
    validate_isolated: impl FnOnce(&Path) -> Result<()>,
) -> Result<()> {
    let backup = final_root.with_extension("previous");
    ensure!(
        !path_entry_exists(&backup)?,
        "Interrupted workspace swap at {}; preserve/recover it before retry",
        backup.display()
    );
    if !existing {
        fs::rename(stage, final_root)?;
        return Ok(());
    }
    // Compare the complete live snapshot before our rename changes the root's
    // metadata. The post-isolation check still catches saves across this boundary.
    validate_live().context("Source replacement refused before workspace isolation")?;
    fs::rename(final_root, &backup)?;
    if let Err(error) = validate_isolated(&backup) {
        // Normal editor saves no longer reach this tree. Check it only after
        // isolation, and restore it before moving any incremental outputs.
        // If another writer recreated the old path, retain both trees.
        if !path_entry_exists(final_root)? {
            fs::rename(&backup, final_root).context("Failed to restore edited workspace")?;
        }
        return Err(error).context(format!(
            "Source replacement refused; edited sources retained at {} or {}",
            final_root.display(),
            backup.display()
        ));
    }
    for private in [".lake", ".runtime"] {
        fs::rename(backup.join(private), stage.join(private)).with_context(|| {
            format!(
                "Output transfer failed; old sources at {}, new stage at {}",
                backup.display(),
                stage.display()
            )
        })?;
    }
    prune_orphan_outputs(stage)?;
    fs::rename(stage, final_root).with_context(|| {
        format!("New workspace install failed; old sources at {}", backup.display())
    })?;
    fs::remove_dir_all(&backup).with_context(|| {
        format!("Workspace installed, but old source cleanup failed at {}", backup.display())
    })?;
    Ok(())
}

/// LEAN_PATH puts these owned outputs first, so every reused module needs a
/// current local source provider. Keep the artifacts of surviving modules and
/// remove deleted modules' compiler outputs and Lake traces together.
fn prune_orphan_outputs(stage: &Path) -> Result<()> {
    let folds_case = filesystem_folds_ascii_case(&stage.join(".anneal-sdk.json"))?;
    let mut modules = std::collections::BTreeSet::new();
    for source_root in SOURCE_ROOTS {
        let source_root = stage.join(source_root);
        if source_root.try_exists()? {
            modules.extend(local_module_names(&source_root, folds_case)?);
        }
    }
    for output_root in [".lake/build/lib/lean", ".lake/build/ir"] {
        let output_root = stage.join(output_root);
        if !output_root.try_exists()? {
            continue;
        }
        for entry in walkdir::WalkDir::new(&output_root).follow_links(false) {
            let entry = entry?;
            ensure!(!entry.file_type().is_symlink(), "Private output contains a symlink");
            if !entry.file_type().is_file() {
                continue;
            }
            let relative = entry.path().strip_prefix(&output_root)?;
            let leaf =
                relative.file_name().and_then(|s| s.to_str()).context("Non-UTF8 output path")?;
            let Some((module_leaf, _)) = leaf.split_once('.') else { continue };
            let module = relative
                .with_file_name(module_leaf)
                .iter()
                .map(|part| part.to_str().context("Non-UTF8 output path"))
                .collect::<Result<Vec<_>>>()?
                .join(".");
            // Resolve source paths on their actual filesystem; this also
            // handles case aliases on an insensitive output/source volume.
            let source = relative.with_file_name(format!("{module_leaf}.lean"));
            let present = modules.contains(&module)
                || SOURCE_ROOTS.iter().any(|root| stage.join(root).join(&source).is_file());
            if !present {
                fs::remove_file(entry.path())?;
            }
        }
    }
    Ok(())
}

fn generate_sources(lean_generated_root: &Path, artifacts: &[AnnealArtifact]) -> Result<()> {
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

        write_if_changed(&specs_path, &generated.code)
            .with_context(|| format!("Failed to write specs to {}", specs_path.display()))?;

        // Write Source Map
        let map_json = serde_json::to_string(&generated.mappings)
            .context("Failed to serialize source mappings")?;
        write_if_changed(&map_path, &map_json)
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

    let workspace = Workspace::from_root(lean_root)?;
    let stamp = workspace.source_stamp()?;
    let targets = ["Generated".into(), "Anneal".into()];
    let mut cmd = workspace.lake_command(LakeOperation::Build(&targets))?;

    let start = std::time::Instant::now();
    let pb = ProgressBar::new_spinner();
    pb.set_style(ProgressStyle::default_spinner().template("{spinner:.green} {msg}").unwrap());
    pb.enable_steady_tick(std::time::Duration::from_millis(100));
    pb.set_message("Building Lean dependencies...");
    // Command::output drains both streams while waiting and propagates capture
    // failures. A reader error or panic must not become a successful build.
    let output = cmd.output();
    pb.finish_and_clear();
    let output = output.context("Failed to capture lake output")?;
    log::trace!("'lake build' took {:.2?}", start.elapsed());
    if !output.status.success() {
        bail!(
            "Lean build failed\nSTDOUT:\n{}\nSTDERR:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
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

        // Setup-file builds the actual saved transitive local imports, including
        // user imports absent from the generated default roots. Direct startup
        // alone could otherwise verify stale private OLeans.
        crate::lean_gateway::setup_saved_imports(&workspace, Path::new(&specs_rel_path))?;
        ensure!(
            workspace.source_stamp()? == stamp,
            "Lean inputs changed during build; verification is obsolete"
        );
        let output = workspace
            .lean_command(LeanOperation::Check { file: Path::new(&specs_rel_path), json: true })?
            .output()
            .context("Failed to run Lean compiler")?;
        ensure!(
            workspace.source_stamp()? == stamp,
            "Lean inputs changed during verification; result is obsolete"
        );

        let (diags, failed) = diagnostic_output(&output)?;
        has_errors |= failed;
        let specs_abs_path = lean_root.join(&specs_rel_path);
        let specs_source = std::fs::read_to_string(&specs_abs_path)
            .with_context(|| format!("Failed to read {}", specs_abs_path.display()))?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            if !stderr.trim().is_empty() {
                eprintln!("Lean compiler failed or produced stderr for {slug}.");
                eprintln!("STDERR:\n{stderr}");
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

/// Process status and structured error diagnostics are independent failure
/// witnesses. Informational output cannot make a failed compiler successful.
fn diagnostic_output(output: &std::process::Output) -> Result<(Vec<NativeLeanDiagnostic>, bool)> {
    let stdout = std::str::from_utf8(&output.stdout).context("Lean output was not UTF-8")?;
    let mut failed = !output.status.success();
    let mut diagnostics = Vec::new();
    for line in stdout.lines().filter(|line| !line.trim().is_empty()) {
        let diagnostic: NativeLeanDiagnostic =
            serde_json::from_str(line).context("Lean emitted malformed diagnostic JSON")?;
        ensure!(
            matches!(diagnostic.severity.as_str(), "error" | "warning" | "information"),
            "Lean emitted an unknown diagnostic severity"
        );
        failed |= diagnostic.severity == "error";
        diagnostics.push(diagnostic);
    }
    Ok((diagnostics, failed))
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

    #[test]
    fn local_module_names_follow_source_paths() {
        let temp = tempfile::tempdir().unwrap();
        fs::create_dir(temp.path().join("Shared")).unwrap();
        fs::write(temp.path().join("Shared/Local.lean"), "def localValue := 1").unwrap();
        fs::write(temp.path().join("README.txt"), "ignored").unwrap();
        let modules = local_module_names(temp.path(), false).unwrap();
        assert_eq!(modules, ["Shared.Local"]);
        fs::write(temp.path().join("Shared.Ambiguous.lean"), "").unwrap();
        assert!(local_module_names(temp.path(), false).is_err());
    }

    #[test]
    fn local_module_enumeration_uses_suffix_equivalence_without_changing_module_spelling() {
        let temp = tempfile::tempdir().unwrap();
        fs::create_dir(temp.path().join("MiXeD")).unwrap();
        for name in ["LoWeR.lean", "MiDdLe.LeAn", "UpPeR.LEAN", "Ignored.LEAN.bak"] {
            fs::write(temp.path().join("MiXeD").join(name), "def localValue := 1\n").unwrap();
        }
        let exact = local_module_names(temp.path(), false).unwrap();
        assert_eq!(exact, ["MiXeD.LoWeR"]);
        let folded = local_module_names(temp.path(), true).unwrap();
        assert_eq!(folded, ["MiXeD.LoWeR", "MiXeD.MiDdLe", "MiXeD.UpPeR"]);

        // This toy fixture observes only filesystem equivalence; it is not an
        // admitted workspace or an executable SDK/configuration binding.
        let marker = temp.path().join(".anneal-sdk.json");
        fs::write(&marker, "case-probe fixture").unwrap();
        let measured = filesystem_folds_ascii_case(&marker).unwrap();
        if !measured {
            // Existence of a differently cased sibling must not turn an exact
            // filesystem into a folding one: the probe compares dev/inode.
            fs::write(temp.path().join(".ANNEAL-SDK.JSON"), "distinct case-probe fixture").unwrap();
            assert!(!filesystem_folds_ascii_case(&marker).unwrap());
        }
        assert_eq!(
            local_module_names(temp.path(), measured).unwrap(),
            if measured { folded } else { exact }
        );
    }

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

    #[cfg(unix)]
    #[test]
    fn compiler_failure_cannot_be_hidden_by_informational_output() {
        let message = r#"{"fileName":"Specs.lean","data":"a theorem was printed","severity":"information","pos":{"line":1,"column":0},"endPos":null}"#;
        let output = std::process::Command::new("/bin/sh")
            .args(["-c", "printf '%s\\n' \"$1\"; exit 1", "lean-result-test", message])
            .output()
            .unwrap();
        let (diagnostics, failed) = diagnostic_output(&output).unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert!(failed, "a failed compiler is not verification success");
    }

    #[cfg(unix)]
    #[test]
    fn malformed_compiler_output_cannot_be_ignored() {
        let output = std::process::Command::new("/bin/sh")
            .args(["-c", "printf 'not a Lean diagnostic\\n'"])
            .output()
            .unwrap();
        assert!(diagnostic_output(&output).is_err());
    }

    #[test]
    fn interrupted_swap_preserves_both_owned_output_trees() {
        let temp = tempfile::tempdir().unwrap();
        let old = temp.path().join("workspace");
        let stage = temp.path().join("stage");
        fs::create_dir_all(old.join(".lake")).unwrap();
        fs::write(old.join(".lake/unique"), b"incremental").unwrap();
        fs::create_dir_all(old.join(".runtime")).unwrap();
        fs::create_dir_all(stage.join(".runtime")).unwrap();
        fs::write(stage.join(".runtime/collision"), b"foreign").unwrap();
        assert!(install_stage(&stage, &old, true, || Ok(()), |_| Ok(())).is_err());
        assert_eq!(fs::read(stage.join(".lake/unique")).unwrap(), b"incremental");
        assert!(old.with_extension("previous").join(".runtime").exists());
        assert!(!old.exists());
    }

    #[test]
    fn interrupted_swap_cannot_be_retried_as_a_fresh_workspace() {
        let temp = tempfile::tempdir().unwrap();
        let final_root = temp.path().join("workspace");
        let stage = temp.path().join("stage");
        fs::create_dir_all(final_root.with_extension("previous").join("user")).unwrap();
        fs::create_dir_all(&stage).unwrap();
        fs::write(stage.join("new"), "generated").unwrap();
        assert!(install_stage(&stage, &final_root, false, || Ok(()), |_| Ok(())).is_err());
        assert!(!final_root.exists());
        assert!(stage.join("new").exists());
        assert!(final_root.with_extension("previous").join("user").exists());
    }

    #[test]
    fn successful_swap_keeps_outputs_and_unchanged_source_mtime() {
        let temp = tempfile::tempdir().unwrap();
        let old = temp.path().join("workspace");
        let stage = temp.path().join("stage");
        fs::create_dir_all(old.join(".lake")).unwrap();
        fs::create_dir_all(old.join(".runtime")).unwrap();
        fs::create_dir(&stage).unwrap();
        // Filesystem-only swap fixture: provide the existing stage marker used
        // for case observation without claiming SDK/workspace admission.
        fs::write(stage.join(".anneal-sdk.json"), "case-probe fixture").unwrap();
        for root in [&old, &stage] {
            fs::write(root.join("Local.lean"), "def x := 1\n").unwrap();
        }
        let before = fs::metadata(old.join("Local.lean")).unwrap().modified().unwrap();
        preserve_unchanged_mtimes(&old, &stage).unwrap();
        fs::write(old.join(".lake/unique"), "outputs").unwrap();
        install_stage(&stage, &old, true, || Ok(()), |_| Ok(())).unwrap();
        assert_eq!(fs::metadata(old.join("Local.lean")).unwrap().modified().unwrap(), before);
        assert_eq!(fs::read_to_string(old.join(".lake/unique")).unwrap(), "outputs");
        assert!(!old.with_extension("previous").exists());
    }

    #[test]
    fn live_snapshot_rejection_preserves_editable_sources_and_outputs() {
        let temp = tempfile::tempdir().unwrap();
        let old = temp.path().join("workspace");
        let stage = temp.path().join("stage");
        fs::create_dir_all(old.join("user")).unwrap();
        fs::create_dir_all(old.join(".lake")).unwrap();
        fs::create_dir_all(old.join(".runtime")).unwrap();
        fs::create_dir_all(stage.join("user")).unwrap();
        fs::write(old.join("user/Proof.lean"), "old proof").unwrap();
        let baseline = fs::read(old.join("user/Proof.lean")).unwrap();
        fs::write(stage.join("user/Proof.lean"), &baseline).unwrap();
        fs::write(old.join(".lake/unique"), "outputs").unwrap();
        fs::write(old.join("user/Proof.lean"), "new saved proof").unwrap();
        let result = install_stage(
            &stage,
            &old,
            true,
            || {
                assert!(old.exists(), "the live check must precede isolation");
                assert!(!old.with_extension("previous").exists());
                ensure!(fs::read(old.join("user/Proof.lean"))? == baseline, "snapshot changed");
                Ok(())
            },
            |_| panic!("a rejected live snapshot must not reach the isolated check"),
        );
        assert!(result.is_err());
        assert_eq!(fs::read_to_string(old.join("user/Proof.lean")).unwrap(), "new saved proof");
        assert_eq!(fs::read_to_string(old.join(".lake/unique")).unwrap(), "outputs");
        assert!(old.join(".runtime").exists());
        assert!(!old.with_extension("previous").exists());
        assert!(stage.join("user/Proof.lean").is_file());
        assert!(!stage.join(".lake").exists());
    }

    #[test]
    fn edit_at_isolation_is_restored_before_outputs_move() {
        let temp = tempfile::tempdir().unwrap();
        let old = temp.path().join("workspace");
        let stage = temp.path().join("stage");
        fs::create_dir_all(old.join("user")).unwrap();
        fs::create_dir_all(old.join(".lake")).unwrap();
        fs::create_dir_all(old.join(".runtime")).unwrap();
        fs::create_dir_all(stage.join("user")).unwrap();
        fs::write(old.join("user/Proof.lean"), "old proof").unwrap();
        let baseline = fs::read(old.join("user/Proof.lean")).unwrap();
        fs::write(stage.join("user/Proof.lean"), "staged old proof").unwrap();
        fs::write(old.join(".lake/unique"), "outputs").unwrap();
        let result = install_stage(
            &stage,
            &old,
            true,
            || {
                assert!(old.exists(), "validate the complete live tree before isolation");
                ensure!(fs::read(old.join("user/Proof.lean"))? == baseline, "snapshot changed");
                Ok(())
            },
            |backup| {
                assert!(!old.exists(), "the editable path must be isolated first");
                // Model a save to an already-open file after the live check.
                fs::write(backup.join("user/Proof.lean"), "new saved proof")?;
                ensure!(fs::read(backup.join("user/Proof.lean"))? == baseline, "snapshot changed");
                Ok(())
            },
        );
        assert!(result.is_err());
        assert_eq!(fs::read_to_string(old.join("user/Proof.lean")).unwrap(), "new saved proof");
        assert_eq!(fs::read_to_string(old.join(".lake/unique")).unwrap(), "outputs");
        assert!(stage.join("user/Proof.lean").is_file());
        assert!(!stage.join(".lake").exists());
    }

    #[test]
    fn isolated_snapshot_rejection_preserves_both_trees_on_restore_collision() {
        let temp = tempfile::tempdir().unwrap();
        let old = temp.path().join("workspace");
        let stage = temp.path().join("stage");
        fs::create_dir_all(old.join("user")).unwrap();
        fs::create_dir_all(old.join(".lake")).unwrap();
        fs::create_dir_all(old.join(".runtime")).unwrap();
        fs::create_dir_all(&stage).unwrap();
        fs::write(old.join("user/Proof.lean"), "old proof").unwrap();
        fs::write(old.join(".lake/unique"), "outputs").unwrap();
        let result = install_stage(
            &stage,
            &old,
            true,
            || Ok(()),
            |backup| {
                fs::write(backup.join("user/Proof.lean"), "new saved proof")?;
                // A different writer recreates the editable path. Neither tree
                // may be overwritten when restoring the rejected snapshot.
                fs::create_dir_all(old.join("user"))?;
                fs::write(old.join("user/Proof.lean"), "independent saved proof")?;
                bail!("source snapshot changed")
            },
        );
        assert!(result.is_err());
        let backup = old.with_extension("previous");
        assert_eq!(
            fs::read_to_string(old.join("user/Proof.lean")).unwrap(),
            "independent saved proof"
        );
        assert_eq!(fs::read_to_string(backup.join("user/Proof.lean")).unwrap(), "new saved proof");
        assert_eq!(fs::read_to_string(backup.join(".lake/unique")).unwrap(), "outputs");
        assert!(backup.join(".runtime").exists());
        assert!(!stage.join(".lake").exists());
        assert!(!stage.join(".runtime").exists());
    }

    #[test]
    fn replacement_removes_deleted_module_artifacts_and_keeps_surviving_outputs() {
        let temp = tempfile::tempdir().unwrap();
        let old = temp.path().join("workspace");
        let stage = temp.path().join("stage");
        fs::create_dir_all(old.join(".runtime")).unwrap();
        fs::create_dir_all(stage.join("user/Shared")).unwrap();
        fs::write(stage.join(".anneal-sdk.json"), "case-probe fixture").unwrap();
        fs::write(stage.join("user/Shared/Current.lean"), "import Shared.Deleted\n").unwrap();
        for root in [".lake/build/lib/lean", ".lake/build/ir"] {
            fs::create_dir_all(old.join(root).join("Shared")).unwrap();
            for module in ["Current", "Deleted"] {
                for extension in [
                    "olean",
                    "olean.server",
                    "olean.private",
                    "ilean",
                    "ir",
                    "trace",
                    "c",
                    "c.o.export",
                    "setup.json",
                    "ltar.hash",
                ] {
                    fs::write(
                        old.join(root).join(format!("Shared/{module}.{extension}")),
                        "compiled",
                    )
                    .unwrap();
                }
            }
        }
        let surviving = old.join(".lake/build/lib/lean/Shared/Current.olean");
        let before = fs::metadata(&surviving).unwrap().modified().unwrap();
        install_stage(&stage, &old, true, || Ok(()), |_| Ok(())).unwrap();
        assert_eq!(fs::metadata(&surviving).unwrap().modified().unwrap(), before);
        for entry in
            walkdir::WalkDir::new(old.join(".lake/build")).into_iter().filter_map(Result::ok)
        {
            assert!(!entry.file_name().to_string_lossy().starts_with("Deleted."));
        }
        assert!(old.join(".lake/build/ir/Shared/Current.c.o.export").is_file());
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
