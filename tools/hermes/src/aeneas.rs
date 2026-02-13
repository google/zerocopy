use std::process::Command;

use anyhow::{bail, Context, Result};

use crate::{resolve::Roots, scanner::HermesArtifact};

pub fn run_aeneas(roots: &Roots, artifacts: &[HermesArtifact]) -> Result<()> {
    let llbc_root = roots.llbc_root();
    let lean_generated_root = roots.lean_generated_root();

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
        let output_dir = lean_generated_root.join(artifact.artifact_slug());

        std::fs::create_dir_all(&output_dir).context("Failed to create Aeneas output directory")?;

        let spec_code = crate::generate::generate_artifact(artifact);
        let spec_path = output_dir.join("Hermes.lean");
        std::fs::write(&spec_path, spec_code).context("Failed to write Hermes.lean")?;

        let mut cmd = Command::new("aeneas");

        cmd.args(["-backend", "lean"]).arg("-dest").arg(&output_dir).args([
            "-split-files",
            "-no-lean-default-lakefile",
            "-decreases-clauses",
            "-abort-on-error",
        ]);

        // TODO: Handle opaque functions (`unsafe(axiom)`).
        // We need to parse these from the AST and pass them as `-opaque module::params::...`
        cmd.arg(&llbc_path);

        log::debug!("Command: {:?}", cmd);

        let output = cmd.output().context("Failed to spawn aeneas")?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            bail!(
                "Aeneas failed for package '{}' with status: {}\nstderr:\n{}",
                artifact.name.package_name,
                output.status,
                stderr
            );
        }
    }

    Ok(())
}
