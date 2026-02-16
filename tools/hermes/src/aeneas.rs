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

pub fn run_aeneas(
    roots: &Roots,
    artifacts: &[HermesArtifact],
    args: &crate::resolve::Args,
) -> Result<()> {
    let llbc_root = roots.llbc_root();
    let lean_generated_root = roots.lean_generated_root();

    // 1. Setup Lean Project Root
    let lean_root = lean_generated_root.parent().unwrap(); // target/hermes/<hash>/lean
    std::fs::create_dir_all(lean_root.join("hermes"))?;

    // Optimization: If HERMES_INTEGRATION_TEST_LEAN_CACHE_DIR is set, copy the .lake directory
    // from there using hardlinks. This avoids re-downloading/re-building Mathlib.
    restore_from_integration_cache(lean_root)?;

    // 2. Write Standard Library
    let mut prelude = String::new();
    if !args.allow_sorry {
        prelude.push_str("import Lean\n");
    }
    prelude.push_str(HERMES_PRELUDE);

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

    write_if_changed(&lean_root.join("hermes").join("Hermes.lean"), &prelude)
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
        } else {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            log::trace!("Aeneas stdout:\n{}", stdout);
            log::trace!("Aeneas stderr:\n{}", stderr);
        }
        log::trace!("Aeneas for '{}' took {:.2?}", artifact.name.target_name, start.elapsed());

        // Aeneas might not generate Funs.lean or Types.lean if there are no functions/types.
        // However, `Specs.lean` and `Generated.lean` expect them to exist (as imports).
        // We create empty files if they are missing to satisfy the compiler.
        let funs_path = output_dir.join("Funs.lean");
        if !funs_path.exists() {
            log::debug!("Funs.lean missing for {}, creating empty file", slug);
            std::fs::write(&funs_path, "").context("Failed to create empty Funs.lean")?;
        }

        let types_path = output_dir.join("Types.lean");
        if !types_path.exists() {
            log::debug!("Types.lean missing for {}, creating empty file", slug);
            std::fs::write(&types_path, "").context("Failed to create empty Types.lean")?;
        }

        // Add to Generated.lean imports (no prefix)

        writeln!(generated_imports, "import «{}».Funs", slug).unwrap();
        writeln!(generated_imports, "import «{}».Types", slug).unwrap();

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

            writeln!(generated_imports, "import «{}».FunsExternal", slug).unwrap();
            lake_roots.push(format!("{}.FunsExternal", slug));
        }

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
        // Use a path dependency to avoid git cloning
        format!(r#"require aeneas from "{path}/backends/lean""#)
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

    // If lake-manifest.json exists (copied from cache), we manually inject the `aeneas` dependency.
    // This avoids running `lake update`, which would trigger `mathlib`'s post-update hook (cache download).
    if lean_root.join("lake-manifest.json").exists() {
        if let Ok(aeneas_dir) = std::env::var("HERMES_AENEAS_DIR") {
            let aeneas_url = format!("{}/backends/lean", aeneas_dir);
            let manifest_path = lean_root.join("lake-manifest.json");

            match std::fs::read_to_string(&manifest_path) {
                Ok(content) => match serde_json::from_str::<serde_json::Value>(&content) {
                    Ok(mut json) => {
                        if let Some(packages) =
                            json.get_mut("packages").and_then(|v| v.as_array_mut())
                        {
                            if !packages
                                .iter()
                                .any(|p| p.get("name").and_then(|n| n.as_str()) == Some("aeneas"))
                            {
                                log::debug!(
                                    "Patching lake-manifest.json to add aeneas dependency..."
                                );
                                let entry = serde_json::json!({
                                    "dir": aeneas_url,
                                    "type": "path",
                                    "name": "aeneas",
                                    "subDir": null,
                                    "scope": "",
                                    "rev": null,
                                    "inputRev": null,
                                    "inherited": false,
                                    "configFile": "lakefile.lean",
                                    "manifestFile": "lake-manifest.json"
                                });
                                packages.push(entry);

                                if let Ok(new_content) = serde_json::to_string_pretty(&json) {
                                    if let Err(e) = std::fs::write(&manifest_path, new_content) {
                                        log::warn!("Failed to write patched manifest: {}", e);
                                    }
                                }
                            }
                        }
                    }
                    Err(e) => log::warn!("Failed to parse lake-manifest.json: {}", e),
                },
                Err(e) => log::warn!("Failed to read lake-manifest.json: {}", e),
            }
        }
    }

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
            let (file, start, end) = resolve_mapping(&diag, &mappings);
            mapper.render_raw(&file, diag.message, level, start, end, |s| eprintln!("{s}"));
        }
    }

    if has_errors {
        bail!("Lean verification failed");
    }

    Ok(())
}

fn resolve_mapping(
    diag: &LeanDiagnostic,
    mappings: &[crate::generate::SourceMapping],
) -> (String, usize, usize) {
    let mapping =
        mappings.iter().find(|m| m.lean_start <= diag.byte_start && m.lean_end >= diag.byte_end);

    // Certain diagnostics, such as "declaration uses `sorry`", are reported on
    // the synthetic theorem name rather than the proof block itself. To improve
    // the user experience, we attempt to redirect these diagnostics to the
    // relevant keyword (e.g., `proof` or `axiom`) if a corresponding mapping
    // exists in the same file.
    let mapping = match mapping {
        Some(m)
            if diag.message.contains("declaration uses `sorry`")
                && matches!(m.kind, crate::generate::MappingKind::Synthetic) =>
        {
            mappings
                .iter()
                .find(|m2| {
                    matches!(m2.kind, crate::generate::MappingKind::Keyword)
                        && m2.lean_start > m.lean_end
                        && m2.source_start <= m.source_start
                        && m2.source_file == m.source_file
                })
                .or(Some(m))
        }
        _ => mapping,
    };

    if let Some(m) = mapping {
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
    } else {
        (diag.file_name.clone(), diag.byte_start, diag.byte_end)
    }
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

mod integration {
    use super::*;

    /// Restores the `.lake` directory, which contains build artifacts and package
    /// sources.
    ///
    /// We use `cp -rl` to create hardlinks instead of deep copying. This is crucial
    /// for performance because the `.lake` directory (especially with `mathlib`) can
    /// be very large and contain thousands of files. Hardlinking is nearly
    /// instantaneous and consumes negligible additional disk space.
    pub fn restore_lake_directory(
        cache_path: &std::path::Path,
        lean_root: &std::path::Path,
    ) -> Result<()> {
        let source_lake = cache_path.join(".lake");
        let target_lake = lean_root.join(".lake");

        if !source_lake.exists() || target_lake.exists() {
            return Ok(());
        }

        log::debug!(
            "Initializing .lake from {} to {}",
            source_lake.display(),
            target_lake.display()
        );

        // Use `cp -rl` to recursively hardlink the directory structure.
        let status = Command::new("cp")
            .args(["-rl", source_lake.to_str().unwrap(), target_lake.to_str().unwrap()])
            .status()
            .with_context(|| "Failed to execute cp -rl for .lake cache")?;

        if !status.success() {
            log::warn!("'cp -rl' failed with status: {}", status);
            return Ok(());
        }

        // Fix up Git metadata to ensure each test runs in isolation.
        let packages_dir = target_lake.join("packages");
        if !packages_dir.exists() {
            return Ok(());
        }

        let entries =
            std::fs::read_dir(&packages_dir).context("Failed to read .lake/packages directory")?;

        for entry in entries.flatten() {
            let pkg_name = entry.file_name();
            let target_pkg = entry.path();
            let source_pkg = source_lake.join("packages").join(&pkg_name);

            fixup_git_metadata(&target_pkg, &source_pkg, &pkg_name)?;
        }

        Ok(())
    }

    /// Fixes up the `.git` directory within a cached package to prevent race
    /// conditions.
    ///
    /// When multiple tests run in parallel, they share the underlying hardlinked
    /// Git objects, which is safe because Git objects are immutable. However, the
    /// Git index (`.git/index`), `HEAD`, and refs are mutable. If these were
    /// hardlinked, one test modifying the index (e.g., via `git status` or an
    /// internal Lake command) would corrupt the state for other tests.
    ///
    /// This function breaks the hardlinks for mutable metadata by replacing them
    /// with deep copies, ensuring each test has its own independent view of the Git
    /// repository state.
    fn fixup_git_metadata(
        target_pkg: &std::path::Path,
        source_pkg: &std::path::Path,
        pkg_name: &std::ffi::OsStr,
    ) -> Result<()> {
        let target_git = target_pkg.join(".git");
        let source_git = source_pkg.join(".git");

        if !target_git.exists() || !source_git.exists() {
            return Ok(());
        }

        // Break hardlinks for mutable git metadata.
        let git_entries =
            std::fs::read_dir(&target_git).context("Failed to read .git directory in package")?;

        for git_entry in git_entries.flatten() {
            let name = git_entry.file_name();
            if name == "objects" {
                // Keep `.git/objects` hardlinked. These files are
                // content-addressable and immutable, so sharing them is safe and
                // saves significant disk space.
                continue;
            }

            let target_elem = git_entry.path();
            let source_elem = source_git.join(&name);

            if target_elem.is_dir() {
                let _ = std::fs::remove_dir_all(&target_elem);
                // Recursively copy the directory to break hardlinks.
                let _ = Command::new("cp")
                    .args(["-r", source_elem.to_str().unwrap(), target_elem.to_str().unwrap()])
                    .status();
            } else {
                let _ = std::fs::remove_file(&target_elem);
                let _ = std::fs::copy(&source_elem, &target_elem);
            }
        }

        // Update the Git index to match the current working directory.
        //
        // Since we hardlinked the working tree files, their inodes and ctime/mtime
        // metadata may not match what is recorded in the copied `.git/index`. This
        // discrepancy causes Git to believe that files have been modified locally.
        // We run `git update-index --refresh` to update the index with the current
        // file definition, suppressing "local changes" warnings.
        let status = Command::new("git")
            .args(["update-index", "-q", "--refresh"])
            .current_dir(target_pkg)
            .status();

        if let Ok(s) = status {
            if !s.success() {
                log::warn!("git update-index failed for {}", pkg_name.to_string_lossy());
            }
        }

        Ok(())
    }
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
            level: "warning".into(),
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
    fn test_resolve_mapping_cross_function_failure_order() {
        // Function A: Spec at 200 (Diagnostic Here)
        // Function B: Proof Keyword at 300 (which is > 200, so valid for redirection if we didn't check source order?)
        // Wait, current logic requires `m2.lean_start > m.lean_end`.
        // So let's say Function A Spec is at lean 50..60.
        // Function B Proof Keyword is at lean 70..80.
        // Logic: finds keyword AFTER spec in Lean.
        // But source order: Func A Spec at 200. Func B Proof Keyword at 300.
        // `m2.source_start (300) <= m.source_start (200)` is FALSE.
        // So it should NOT redirect.

        let mappings = vec![
            mk_mapping(50, 60, 200, 210, MappingKind::Synthetic, "file.rs"), // Func A Spec
            mk_mapping(70, 80, 300, 310, MappingKind::Keyword, "file.rs"),   // Func B Proof
        ];
        let diag = mk_diag("declaration uses `sorry`", 50, 60);

        let (_, start, _) = resolve_mapping(&diag, &mappings);
        assert_eq!(start, 200, "Should NOT redirect to subsequent function");
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
}

/// Restores the Lean build artifacts from a shared integration test cache.
///
/// This optimization significantly reduces test execution time by avoiding
/// redundant downloads and compilations of standard Lean dependencies (like
/// `mathlib`).
fn restore_from_integration_cache(lean_root: &std::path::Path) -> Result<()> {
    let cache_dir = match std::env::var("HERMES_INTEGRATION_TEST_LEAN_CACHE_DIR") {
        Ok(d) => d,
        Err(_) => return Ok(()),
    };

    let cache_path = std::path::Path::new(&cache_dir);

    // Copy `lake-manifest.json` to signal that dependencies are resolved.
    copy_lake_manifest(cache_path, lean_root)?;

    // Restore the `.lake` directory using hardlinks for performance.
    integration::restore_lake_directory(cache_path, lean_root)?;

    Ok(())
}

/// Copies `lake-manifest.json` from the cache to the target directory.
///
/// Presence of this file informs the Lake build tool that dependencies have
/// already been resolved, preventing it from attempting to update the manifest
/// or query the network for package updates.
fn copy_lake_manifest(cache_path: &std::path::Path, lean_root: &std::path::Path) -> Result<()> {
    let source_manifest = cache_path.join("lake-manifest.json");
    let target_manifest = lean_root.join("lake-manifest.json");

    if source_manifest.exists() && !target_manifest.exists() {
        log::debug!(
            "Copying lake-manifest.json from {} to {}",
            source_manifest.display(),
            target_manifest.display()
        );
        std::fs::copy(&source_manifest, &target_manifest)
            .context("Failed to copy lake-manifest.json from cache")?;
    }
    Ok(())
}
