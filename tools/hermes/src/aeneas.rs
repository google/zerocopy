use std::{
    fmt::Write,
    io::{BufRead, BufReader},
    process::{Command, Stdio},
    sync::{Arc, Mutex},
};

use anyhow::{bail, Context, Result};
use indicatif::{ProgressBar, ProgressStyle};

use crate::{generate, resolve::Roots, scanner::HermesArtifact};

const HERMES_PRELUDE: &str = include_str!("Hermes.lean");
const HERMES_DIAGNOSTICS_TEMPLATE: &str = include_str!("Diagnostics.lean");

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

    let mut generated_imports = String::new();
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

        std::fs::create_dir_all(&output_dir).context("Failed to create Aeneas output directory")?;

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

        let mut cmd = Command::new("aeneas");

        cmd.args(["-backend", "lean"])
            .arg("-dest")
            .arg(&output_dir)
            .args(["-split-files", "-abort-on-error"]);

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

        // Add to Generated.lean imports (no prefix)

        writeln!(generated_imports, "import «{}».Funs", slug).unwrap();
        writeln!(generated_imports, "import «{}».Types", slug).unwrap();

        // Add to Lake roots
        // Note: We need to use `«Slug».Funs` syntax if sticking to strict naming,
        // but Lake roots usually expect identifiers.
        // If slug has underscores, it is a valid identifier.
        // But if it had hyphens (it doesn't), we'd need quotes.
        // We use the slug as is.
        lake_roots.push(format!("{}.Funs", slug));
        lake_roots.push(format!("{}.Types", slug));
    }

    // 4. Write Lakefile
    let aeneas_dep = if let Ok(path) = std::env::var("HERMES_AENEAS_DIR") {
        format!(r#"require aeneas from git "file://{path}" @ "main" / "backends/lean""#)
    } else {
        r#"require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends/lean""#
            .to_string()
    };

    let roots_str = lake_roots.iter().map(|r| format!("`{}", r)).collect::<Vec<_>>().join(", ");

    let lakefile = format!(
        r#"
import Lake
open Lake DSL

{aeneas_dep}

package hermes_verification

lean_lib «Generated» where
  srcDir := "generated"
  roots := #[{roots_str}]

lean_lib «Hermes» where
  srcDir := "hermes"

lean_lib «User» where
  srcDir := "user"
"#
    );
    write_if_changed(&lean_root.join("lakefile.lean"), &lakefile)
        .context("Failed to write Lakefile")?;

    write_if_changed(&lean_generated_root.join("Generated.lean"), &generated_imports)
        .context("Failed to write Generated.lean")?;

    run_lake(roots, artifacts)
}

fn run_lake(roots: &Roots, artifacts: &[HermesArtifact]) -> Result<()> {
    let generated = roots.lean_generated_root();
    let lean_root = generated.parent().unwrap();
    log::info!("Running 'lake build' in {}", lean_root.display());

    if !lean_root.join(".lake/packages/mathlib").exists() {
        // 1. Run 'lake exe cache get' to fetch pre-built Mathlib artifacts
        // This prevents compiling Mathlib from source, which is slow and disk-heavy.
        let mut cache_cmd = Command::new("lake");
        cache_cmd.args(["exe", "cache", "get"]);
        cache_cmd.current_dir(&lean_root);
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
    let mut cmd = Command::new("lake");
    cmd.args(["build", "Generated", "Hermes"]);
    cmd.current_dir(&lean_root);
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());

    let start = std::time::Instant::now();
    let mut child = cmd.spawn().context("Failed to spawn lake")?;

    // Capture stderr in background
    let stderr_buffer = Arc::new(Mutex::new(Vec::new()));
    let stderr_clone = stderr_buffer.clone();
    let stderr_handle = if let Some(stderr) = child.stderr.take() {
        Some(std::thread::spawn(move || {
            let reader = BufReader::new(stderr);
            for line in reader.lines().map_while(Result::ok) {
                stderr_clone.lock().unwrap().push(line);
            }
        }))
    } else {
        None
    };

    // UI Spinner
    let pb = ProgressBar::new_spinner();
    pb.set_style(ProgressStyle::default_spinner().template("{spinner:.green} {msg}").unwrap());
    pb.enable_steady_tick(std::time::Duration::from_millis(100));
    pb.set_message("Building Lean dependencies...");

    // Capture stdout in background (while ticking progress bar)
    let stdout_buffer = Arc::new(Mutex::new(Vec::new()));
    let stdout_clone = stdout_buffer.clone();
    let pb_clone = pb.clone();

    let stdout_handle = if let Some(stdout) = child.stdout.take() {
        Some(std::thread::spawn(move || {
            let reader = BufReader::new(stdout);
            for line in reader.lines().map_while(Result::ok) {
                stdout_clone.lock().unwrap().push(line);
                pb_clone.tick();
            }
        }))
    } else {
        None
    };

    let status = child.wait().context("Failed to wait for lake")?;
    pb.finish_and_clear();
    log::trace!("'lake build' took {:.2?}", start.elapsed());

    // Join the threads to ensure we have all logs
    if let Some(handle) = stderr_handle {
        if let Err(e) = handle.join() {
            log::error!("Stderr reading thread panicked: {:?}", e);
        }
    }
    if let Some(handle) = stdout_handle {
        if let Err(e) = handle.join() {
            log::error!("Stdout reading thread panicked: {:?}", e);
        }
    }

    if !status.success() {
        let stderr = stderr_buffer.lock().unwrap().join("\n");
        let stdout = stdout_buffer.lock().unwrap().join("\n");
        bail!("Lean build failed\nSTDOUT:\n{}\nSTDERR:\n{}", stdout, stderr);
    }

    // 3. Run Diagnostics
    log::info!("Running Lean diagnostics...");
    let mut has_errors = false;
    let mut mapper = crate::diagnostics::DiagnosticMapper::new(roots.workspace.clone());

    for artifact in artifacts {
        let slug = artifact.artifact_slug();
        // The path in generated file is `generated/Slug/Specs.lean`
        // We construct the relative path from the Lake root (which is `target/hermes/<hash>/lean`)
        let specs_rel_path = format!("generated/{}/{}", slug, artifact.lean_spec_file_name());

        let diag_script = HERMES_DIAGNOSTICS_TEMPLATE.replace("__TARGET_FILE__", &specs_rel_path);
        let diag_path = lean_root.join("Diagnostics.lean");
        write_if_changed(&diag_path, &diag_script).context("Failed to write Diagnostics.lean")?;

        let mut cmd = Command::new("lake");
        cmd.args(["env", "lean", "--run", "Diagnostics.lean"]);
        cmd.current_dir(&lean_root);
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());

        let output = cmd.output().context("Failed to run diagnostic script")?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            eprintln!("Diagnostic script failed for {slug}.");
            eprintln!("STDERR:\n{stderr}");
            eprintln!("STDOUT:\n{stdout}");
            has_errors = true;
            continue;
        }

        let output = String::from_utf8_lossy(&output.stdout);
        let diags: Vec<LeanDiagnostic> = match serde_json::from_str(&output) {
            Ok(d) => d,
            Err(e) => {
                // TODO: Should we be returning a non-zero exit code here?
                log::warn!("Failed to parse JSON from diagnostic script: {e}");
                log::debug!("Raw output:\n{output}");
                continue;
            }
        };

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

        for diag in diags {
            let level = match diag.level.as_str() {
                "error" => crate::diagnostics::DiagnosticLevel::Error,
                "warning" => crate::diagnostics::DiagnosticLevel::Warning,
                "info" => crate::diagnostics::DiagnosticLevel::Note,
                _ => crate::diagnostics::DiagnosticLevel::Note,
            };

            if matches!(level, crate::diagnostics::DiagnosticLevel::Error) {
                has_errors = true;
            }

            // Map span
            // We look for the first mapping that overlaps with the diagnostic span.
            // Diagnostic span: [d_start, d_end)
            // Mapping span: [m.lean_start, m.lean_end)
            // Overlap: m.lean_start < d_end && m.lean_end > d_start
            let mapping = mappings
                .iter()
                .filter(|m| m.lean_start < diag.byte_end && m.lean_end > diag.byte_start)
                .min_by_key(|m| m.lean_start);

            let (file, start, end) = if let Some(m) = mapping {
                // intersection
                let i_start = std::cmp::max(m.lean_start, diag.byte_start);
                let i_end = std::cmp::min(m.lean_end, diag.byte_end);
                let offset = i_start - m.lean_start;
                let len = i_end - i_start;
                let s_start = m.source_start + offset;
                let s_end = s_start + len;
                (m.source_file.to_string_lossy().to_string(), s_start, s_end)
            } else {
                (diag.file_name.clone(), diag.byte_start, diag.byte_end)
            };

            mapper.render_raw(&file, diag.message, level, start, end, |s| eprintln!("{s}"));
        }
    }

    if has_errors {
        bail!("Lean verification failed");
    }

    Ok(())
}

#[derive(serde::Deserialize, Debug)]
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
    level: String,
    message: String,
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
