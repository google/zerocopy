use std::{
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{bail, Context as _, Result};

use crate::resolve::{Args, Roots};

/// # Panics
///
/// Panics if `start_from` is empty.
pub fn run_charon(args: &Args, roots: &Roots, start_from: &[String]) -> Result<()> {
    let shadow_root = roots.shadow_root();
    let charon_root = roots.charon_root();

    // 1. Ensure the artifact directory exists
    std::fs::create_dir_all(&charon_root).context("Failed to create charon output directory")?;

    // 2. Construct the command
    let mut cmd = Command::new("charon");
    cmd.arg("cargo");

    // Output artifacts to target/hermes/<hash>/charon
    cmd.arg("--dest").arg(&charon_root);

    // Fail fast on errors
    cmd.arg("--abort-on-error");

    assert!(!start_from.is_empty(), "No entry points provided");
    cmd.arg("--start-from").arg(start_from.join(","));

    // Separator for the underlying cargo command
    cmd.arg("--");

    // 3. Handle Manifest Path & Working Directory
    // CRITICAL: We must rewrite paths to point to the shadow crate
    if let Some(original_manifest) = &args.manifest.manifest_path {
        let abs_manifest =
            std::fs::canonicalize(original_manifest).unwrap_or_else(|_| original_manifest.clone());

        // Try to rebase the manifest path onto the shadow root
        if let Ok(relative_path) = abs_manifest.strip_prefix(&roots.workspace) {
            let shadow_manifest = shadow_root.join(relative_path);
            cmd.arg("--manifest-path").arg(shadow_manifest);
        } else {
            // Fallback: This shouldn't happen if check_for_external_deps passed
            log::warn!(
                "Manifest path is outside workspace, passing as-is: {:?}",
                original_manifest
            );
            cmd.arg("--manifest-path").arg(original_manifest);
        }
    } else {
        // If no manifest specified, run inside the shadow root
        cmd.current_dir(&shadow_root);
    }

    // 4. Forward Workspace/Package Selection
    if args.workspace.workspace || args.workspace.all {
        cmd.arg("--workspace");
    }
    for pkg in &args.workspace.package {
        cmd.arg("-p").arg(pkg);
    }
    for exc in &args.workspace.exclude {
        cmd.arg("--exclude").arg(exc);
    }

    // 5. Forward Target Selection
    if args.lib {
        cmd.arg("--lib");
    }
    if args.bins {
        cmd.arg("--bins");
    }
    for bin in &args.bin {
        cmd.arg("--bin").arg(bin);
    }
    if args.examples {
        cmd.arg("--examples");
    }
    for example in &args.example {
        cmd.arg("--example").arg(example);
    }
    if args.tests {
        cmd.arg("--tests");
    }
    for test in &args.test {
        cmd.arg("--test").arg(test);
    }

    // 6. Forward Features
    if args.features.all_features {
        cmd.arg("--all-features");
    }
    if args.features.no_default_features {
        cmd.arg("--no-default-features");
    }
    for feature in &args.features.features {
        cmd.arg("--features").arg(feature);
    }

    // 7. Environment Setup
    // Reuse the main target directory for dependencies to save time
    cmd.env("CARGO_TARGET_DIR", &roots.cargo_target_dir);

    // 8. Execute
    log::info!("Invoking Charon on shadow crate...");
    log::debug!("Command: {:?}", cmd);

    let status = cmd.status().context("Failed to execute charon")?;

    if !status.success() {
        bail!("Charon failed with status: {}", status);
    }

    Ok(())
}
