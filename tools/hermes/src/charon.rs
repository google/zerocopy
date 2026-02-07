use std::process::Command;

use anyhow::{bail, Context as _, Result};

use crate::{
    resolve::{Args, HermesTargetKind, Roots},
    shadow::HermesArtifact,
};

pub fn run_charon(args: &Args, roots: &Roots, packages: &[HermesArtifact]) -> Result<()> {
    let charon_root = roots.charon_root();

    std::fs::create_dir_all(&charon_root).context("Failed to create charon output directory")?;

    for artifact in packages {
        if artifact.start_from.is_empty() {
            continue;
        }

        log::info!("Invoking Charon on package '{}'...", artifact.name.package_name);

        let mut cmd = Command::new("charon");
        cmd.arg("cargo");

        // Output artifacts to target/hermes/<hash>/charon
        let llbc_path = charon_root.join(artifact.llbc_file_name());
        log::debug!("Writing .llbc file to {}", llbc_path.display());
        cmd.arg("--dest-file").arg(llbc_path);

        // Fail fast on errors
        cmd.arg("--abort-on-error");

        // Start translation from specific entry points
        cmd.arg("--start-from").arg(artifact.start_from.join(","));

        // Separator for the underlying cargo command
        cmd.arg("--");

        cmd.arg("--manifest-path").arg(&artifact.shadow_manifest_path);

        match artifact.target_kind {
            HermesTargetKind::Lib
            | HermesTargetKind::RLib
            | HermesTargetKind::ProcMacro
            | HermesTargetKind::CDyLib
            | HermesTargetKind::DyLib
            | HermesTargetKind::StaticLib => {
                cmd.arg("--lib");
            }
            HermesTargetKind::Bin => {
                cmd.arg("--bin").arg(&artifact.name.target_name);
            }
            HermesTargetKind::Example => {
                cmd.arg("--example").arg(&artifact.name.target_name);
            }
            HermesTargetKind::Test => {
                cmd.arg("--test").arg(&artifact.name.target_name);
            }
        }

        // Forward all feature-related flags.
        if args.features.all_features {
            cmd.arg("--all-features");
        }
        if args.features.no_default_features {
            cmd.arg("--no-default-features");
        }
        for feature in &args.features.features {
            cmd.arg("--features").arg(feature);
        }

        // Reuse the main target directory for dependencies to save time.
        cmd.env("CARGO_TARGET_DIR", &roots.cargo_target_dir);

        log::debug!("Command: {:?}", cmd);

        let status = cmd.status().context("Failed to execute charon")?;

        if !status.success() {
            bail!("Charon failed with status: {}", status);
        }
    }

    Ok(())
}
