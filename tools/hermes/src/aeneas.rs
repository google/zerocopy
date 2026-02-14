use std::process::Command;

use anyhow::{bail, Context, Result};

use crate::{resolve::Roots, scanner::HermesArtifact};

const HERMES_PRELUDE: &str = include_str!("Hermes.lean");

use std::io::{BufRead, BufReader};

pub fn run_aeneas(roots: &Roots, artifacts: &[HermesArtifact]) -> Result<()> {
    let llbc_root = roots.llbc_root();
    let lean_generated_root = roots.lean_generated_root();

    // 1. Setup Lean Project Root
    let lean_root = lean_generated_root.parent().unwrap(); // target/hermes/<hash>/lean
    std::fs::create_dir_all(lean_root.join("hermes"))?;

    // 2. Write Standard Library
    write_if_changed(&lean_root.join("hermes").join("Hermes.lean"), HERMES_PRELUDE)
        .context("Failed to write Hermes prelude")?;

    // 3. Write Toolchain
    write_if_changed(&lean_root.join("lean-toolchain"), "leanprover/lean4:v4.28.0-rc1\n")
        .context("Failed to write Lean toolchain")?;

    // 4. Write Lakefile
    let aeneas_dep = if let Ok(path) = std::env::var("HERMES_AENEAS_DIR") {
        format!(r#"require aeneas from git "file://{}" @ "main" / "backends/lean""#, path)
    } else {
        r#"require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends/lean""#
            .to_string()
    };

    let lakefile = format!(
        r#"
import Lake
open Lake DSL

{}

package hermes_verification

lean_lib «Generated» where
  srcDir := "generated"

lean_lib «Hermes» where
  srcDir := "hermes"

lean_lib «User» where
  srcDir := "user"
"#,
        aeneas_dep
    );
    write_if_changed(&lean_root.join("lakefile.lean"), &lakefile)
        .context("Failed to write Lakefile")?;

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
        write_if_changed(&spec_path, &spec_code).context("Failed to write Specs.lean")?;

        let mut cmd = Command::new("aeneas");

        cmd.args(["-backend", "lean"])
            .arg("-dest")
            .arg(&output_dir)
            .args(["-split-files", "-abort-on-error"]);

        // TODO: Handle opaque functions (`unsafe(axiom)`).
        // We need to parse these from the AST and pass them as `-opaque module::params::...`
        cmd.arg(&llbc_path);

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
        }
        log::trace!("Aeneas for '{}' took {:.2?}", artifact.name.target_name, start.elapsed());
    }

    run_lake(roots)
}

fn run_lake(roots: &Roots) -> Result<()> {
    let generated = roots.lean_generated_root();
    let lean_root = generated.parent().unwrap();
    log::info!("Running 'lake build' in {}", lean_root.display());

    if !lean_root.join(".lake/packages/mathlib").exists() {
        // 1. Run 'lake exe cache get' to fetch pre-built Mathlib artifacts
        // This prevents compiling Mathlib from source, which is slow and disk-heavy.
        let mut cache_cmd = Command::new("lake");
        cache_cmd.args(["exe", "cache", "get"]);
        cache_cmd.current_dir(&lean_root);
        // Suppress output unless it fails, or maybe just log it?
        // Using piped output to avoid spamming the console
        cache_cmd.stdout(std::process::Stdio::piped());
        cache_cmd.stderr(std::process::Stdio::piped());

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

    let mut cmd = Command::new("lake");
    cmd.arg("build");
    cmd.current_dir(&lean_root);
    cmd.stdout(std::process::Stdio::piped());
    cmd.stderr(std::process::Stdio::piped());

    let start = std::time::Instant::now();
    let mut child = cmd.spawn().context("Failed to spawn lake")?;

    // Capture stderr in background
    let stderr_buffer = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let stderr_clone = stderr_buffer.clone();
    if let Some(stderr) = child.stderr.take() {
        std::thread::spawn(move || {
            let reader = BufReader::new(stderr);
            for line in reader.lines().map_while(Result::ok) {
                stderr_clone.lock().unwrap().push(line);
            }
        });
    }

    // UI Spinner
    let pb = indicatif::ProgressBar::new_spinner();
    pb.set_style(
        indicatif::ProgressStyle::default_spinner().template("{spinner:.green} {msg}").unwrap(),
    );
    pb.enable_steady_tick(std::time::Duration::from_millis(100));
    pb.set_message("Verifying Lean proofs...");

    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        for _ in reader.lines() {
            // Just tick the spinner on output
            pb.tick();
        }
    }

    let status = child.wait().context("Failed to wait for lake")?;
    pb.finish_and_clear();
    log::trace!("'lake build' took {:.2?}", start.elapsed());

    if !status.success() {
        let stderr = stderr_buffer.lock().unwrap().join("\n");
        eprintln!("{}", stderr); // Print build errors to user
        bail!("Lean verification failed");
    }

    Ok(())
}

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
