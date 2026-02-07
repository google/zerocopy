use std::process::Command;

use anyhow::{bail, Context as _, Result};

use crate::{
    resolve::{Args, Roots},
    shadow::HermesTargetPackage,
};

pub fn run_charon(args: &Args, roots: &Roots, packages: &[HermesTargetPackage]) -> Result<()> {
    let charon_root = roots.charon_root();

    std::fs::create_dir_all(&charon_root).context("Failed to create charon output directory")?;

    for pkg in packages {
        if pkg.start_from.is_empty() {
            continue;
        }

        log::info!("Invoking Charon on package '{}'...", pkg.name);

        let mut cmd = Command::new("charon");
        cmd.arg("cargo");

        // Output artifacts to target/hermes/<hash>/charon
        let llbc_path = charon_root.join(pkg.llbc_file_name());
        log::debug!("Writing .llbc file to {}", llbc_path.display());
        cmd.arg("--dest-file").arg(llbc_path);

        // Fail fast on errors
        cmd.arg("--abort-on-error");

        // Start translation from specific entry points
        cmd.arg("--start-from").arg(pkg.start_from.join(","));

        // Separator for the underlying cargo command
        cmd.arg("--");

        cmd.arg("--manifest-path").arg(&pkg.shadow_manifest_path);

        // NOTE: We do not forward --workspace, -p, or --exclude, as we are
        // manually iterating over the selected packages.
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
