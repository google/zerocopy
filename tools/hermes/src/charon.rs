// Orchestration of Charon extraction.
//
// This module handles the invocation of the `charon` tool to extract Low-Level Borrow Calculus (LLBC)
// from Rust crates. It manages:
// - Setting up the Charon command and arguments (including features, targets, and output paths).
// - Handling `unsafe(axiom)` functions by marking them as opaque to Charon.
// - Streaming and filtering compiler output to provide user-friendly feedback via `indicatif` and `miette`.
// - Validating the extraction result.

use std::{
    io::{BufRead, BufReader},
    process::Command,
};

use anyhow::{bail, Context as _, Result};
use cargo_metadata::{diagnostic::DiagnosticLevel, Message};

use crate::{
    parse::{attr::FunctionBlockInner, ParsedItem},
    resolve::{Args, HermesTargetKind, LockedRoots},
    scanner::HermesArtifact,
};

/// Runs Charon on the specified packages to generate LLBC artifacts.
///
/// This function requires `LockedRoots` to ensure that it has exclusive access
/// to the `llbc` output directory. It iterates over each `HermesArtifact`,
/// constructs the appropriate `charon` command, and executes it.
///
/// It handles:
/// - **Opaque Functions**: identifying `unsafe(axiom)` functions and passing `--opaque` to Charon.
/// - **Entry Points**: passing the computed `start_from` roots to Charon to minimize extraction scope.
/// - **Output Handling**: capturing stdout/stderr, parsing JSON compiler messages, and rendering them
///   using `DiagnosticMapper`.
pub fn run_charon(args: &Args, roots: &LockedRoots, packages: &[HermesArtifact]) -> Result<()> {
    let llbc_root = roots.llbc_root();
    std::fs::create_dir_all(&llbc_root).context("Failed to create LLBC output directory")?;

    check_charon_version()?;

    for artifact in packages {
        if artifact.start_from.is_empty() {
            continue;
        }

        log::info!("Invoking Charon on package '{}'...", artifact.name.package_name);

        let mut cmd = Command::new("charon");
        cmd.arg("cargo");
        cmd.arg("--preset=aeneas");

        // Output artifacts to target/hermes/<hash>/llbc
        let llbc_path = artifact.llbc_path(roots);
        log::debug!("Writing .llbc file to {}", llbc_path.display());
        cmd.arg("--dest-file").arg(llbc_path);

        // Fail fast on errors
        cmd.arg("--abort-on-error");

        for item in &artifact.items {
            if let ParsedItem::Function(func) = &item.item {
                // Check if the function body is an Axiom (unsafe)
                if let FunctionBlockInner::Axiom { .. } = func.hermes.inner {
                    // Mark `unsafe(axiom)` functions as opaque in Charon. This
                    // instructs Aeneas to treat the function as external and
                    // generate a template file (`FunsExternal_Template.lean`)
                    // containing the type signature as an axiom, rather than
                    // attempting to translate the body. This allows users to
                    // mechanically verify the composition of safe code while
                    // manually vouching for the correctness of unsafe leaf
                    // functions.
                    let mut opaque_name = item.module_path.join("::");
                    opaque_name.push_str("::");
                    opaque_name.push_str(func.item.name());

                    cmd.args(["--opaque", &opaque_name]);
                }
            }
        }

        // Start translation from specific entry points. Sort to ensure
        // deterministic ordering for testing. Determinism is important for
        // production too, because the order of arguments can affect the order
        // of generated definitions in Lean, which we want to be stable to
        // minimize churn.
        let mut start_from = artifact.start_from.iter().map(String::as_ref).collect::<Vec<_>>();
        start_from.sort_unstable(); // Slightly faster than `sort`, and equivalent for strings.

        let start_from_str = start_from.join(",");
        // OS command-line length limits (Windows is ~32k; Linux `ARG_MAX` is
        // usually larger, but variable)
        const ARG_CHAR_LIMIT: usize = 32_768;
        if start_from_str.len() > ARG_CHAR_LIMIT {
            // FIXME: Pass the list of entry points to Charon via a file instead
            // of the command line.
            bail!(
                "The list of Hermes entry points for package '{}' is too large ({} bytes). \n\
                 This exceeds safe OS command-line limits.",
                artifact.name.package_name,
                start_from_str.len()
            );
        }

        cmd.arg("--start-from").arg(start_from_str);

        // Separator for the underlying cargo command
        cmd.arg("--");

        // Ensure cargo emits json msgs which charon-driver natively generates
        cmd.arg("--message-format=json");

        cmd.arg("--manifest-path").arg(&artifact.manifest_path);

        use HermesTargetKind::*;
        match artifact.target_kind {
            Lib | RLib | ProcMacro | CDyLib | DyLib | StaticLib => cmd.arg("--lib"),
            Bin => cmd.args(["--bin", &artifact.name.target_name]),
            Example => cmd.args(["--example", &artifact.name.target_name]),
            Test => cmd.args(["--test", &artifact.name.target_name]),
        };

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
        cmd.env("CARGO_TARGET_DIR", &roots.cargo_target_dir());

        log::debug!("Command: {:?}", cmd);

        cmd.stdout(std::process::Stdio::piped());
        cmd.stderr(std::process::Stdio::piped());
        let start = std::time::Instant::now();
        let mut child = cmd.spawn().context("Failed to spawn charon")?;

        let mut output_error = false;

        let safety_buffer = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let safety_buffer_clone = std::sync::Arc::clone(&safety_buffer);
        if let Some(stderr) = child.stderr.take() {
            std::thread::spawn(move || {
                use std::io::{BufRead, BufReader};
                let reader = BufReader::new(stderr);
                for line in reader.lines().map_while(Result::ok) {
                    safety_buffer_clone.lock().unwrap().push(line);
                }
            });
        }

        let pb = indicatif::ProgressBar::new_spinner();
        pb.set_style(
            indicatif::ProgressStyle::default_spinner().template("{spinner:.green} {msg}").unwrap(),
        );
        pb.enable_steady_tick(std::time::Duration::from_millis(100));
        pb.set_message("Compiling...");

        if let Some(stdout) = child.stdout.take() {
            let reader = BufReader::new(stdout);

            let mut mapper = crate::diagnostics::DiagnosticMapper::new(roots.workspace().clone());
            for line in reader.lines().map_while(Result::ok) {
                if let Ok(msg) = serde_json::from_str::<cargo_metadata::Message>(&line) {
                    match msg {
                        Message::CompilerArtifact(a) => {
                            pb.set_message(format!("Compiling {}", a.target.name));
                        }
                        Message::CompilerMessage(msg) => {
                            pb.suspend(|| {
                                mapper.render_miette(&msg.message, |s| eprintln!("{}", s));
                            });
                            if matches!(
                                msg.message.level,
                                DiagnosticLevel::Error | DiagnosticLevel::Ice
                            ) {
                                output_error = true;
                            }
                        }
                        Message::TextLine(t) => {
                            safety_buffer.lock().unwrap().push(t);
                        }
                        _ => {}
                    }
                } else {
                    safety_buffer.lock().unwrap().push(line);
                }
            }
        }

        pb.finish_and_clear();

        let status = child.wait().context("Failed to wait for charon")?;
        log::trace!("Charon for '{}' took {:.2?}", artifact.name.package_name, start.elapsed());

        // FIXME: There's a subtle edge case here – if we get error output AND
        // Rustc ICE's, there's a good chance that the JSON error messages we
        // print won't include all relevant information – some will be printed
        // via stderr. In this case, `output_error = true` and so we bail and
        // discard stderr, which will swallow information from the user.
        if output_error {
            bail!("Diagnostic error in charon");
        } else if !status.success() {
            // "Silent Death" dump
            for line in safety_buffer.lock().unwrap().iter() {
                eprintln!("{}", line);
            }
            bail!("Charon failed with status: {}", status);
        }
    }

    Ok(())
}

/// Checks that the available `charon` binary matches the expected version.
///
/// This check ensures that the installed `charon` tool is compatible with
/// Hermes. Mismatched versions can lead to subtle errors during LLBC
/// generation or parsing due to format changes.
///
/// The expected version is defined in `Cargo.toml` and baked into the binary
/// via `build.rs` and the `HERMES_CHARON_EXPECTED_VERSION` environment
/// variable.
fn check_charon_version() -> Result<()> {
    let output = Command::new("charon")
        .arg("version")
        .output()
        .context("Failed to execute `charon version`")?;

    if !output.status.success() {
        bail!("`charon version` failed with status: {}", output.status);
    }

    let version = String::from_utf8_lossy(&output.stdout).trim().to_string();
    let expected = env!("HERMES_CHARON_EXPECTED_VERSION");

    if version != expected {
        bail!(
            "Charon version mismatch.\n\
             Expected: {}\n\
             Found:    {}\n\
             Please ensure you are using the correct version of Charon.",
            expected,
            version
        );
    }

    Ok(())
}
