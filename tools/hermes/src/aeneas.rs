use std::process::Command;

use anyhow::{bail, Context, Result};

use crate::{resolve::Roots, scanner::HermesArtifact};

const HERMES_PRELUDE: &str = include_str!("Hermes.lean");

pub fn run_aeneas(roots: &Roots, artifacts: &[HermesArtifact]) -> Result<()> {
    let llbc_root = roots.llbc_root();
    let lean_generated_root = roots.lean_generated_root();

    // 1. Setup Lean Project Root
    let lean_root = lean_generated_root.parent().unwrap(); // target/hermes/<hash>/lean
    std::fs::create_dir_all(lean_root.join("hermes"))?;

    // 2. Write Standard Library
    std::fs::write(lean_root.join("hermes").join("Hermes.lean"), HERMES_PRELUDE)
        .context("Failed to write Hermes prelude")?;

    // 3. Write Toolchain
    std::fs::write(lean_root.join("lean-toolchain"), "leanprover/lean4:v4.15.0\n")?;

    // 4. Write Lakefile
    let lakefile = r#"
import Lake
open Lake DSL

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends/lean"

package hermes_verification

lean_lib «Generated» where
  srcDir := "generated"

lean_lib «Hermes» where
  srcDir := "hermes"

lean_lib «User» where
  srcDir := "user"
"#;
    std::fs::write(lean_root.join("lakefile.lean"), lakefile)?;

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
        // CHANGED: Output filename to Specs.lean
        let spec_path = output_dir.join("Specs.lean");
        std::fs::write(&spec_path, spec_code).context("Failed to write Specs.lean")?;

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
