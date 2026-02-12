use std::{
    io::{BufRead, BufReader},
    process::Command,
};

use anyhow::{bail, Context as _, Result};
use cargo_metadata::{diagnostic::DiagnosticLevel, Message};

use crate::{
    resolve::{Args, HermesTargetKind, Roots},
    scanner::HermesArtifact,
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

        // Start translation from specific entry points. Sort to ensure
        // deterministic ordering for testing (not important in production).
        let mut start_from = artifact.start_from.clone();
        start_from.sort();

        // NOTE: This is an optimization that is relevant because, when we
        // encounter items which we can't name (which carry Hermes annotations),
        // we add their parent module to the list of entrypoints. If there are
        // multiple items in the same module, this can lead to duplication in
        // the list of entrypoints.
        start_from.dedup();

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

        cmd.stdout(std::process::Stdio::piped());
        cmd.stderr(std::process::Stdio::piped());
        let mut child = cmd.spawn().context("Failed to spawn charon")?;

        let mut output_error = false;

        let safety_buffer = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let safety_buffer_clone = std::sync::Arc::clone(&safety_buffer);
        if let Some(stderr) = child.stderr.take() {
            std::thread::spawn(move || {
                use std::io::{BufRead, BufReader};
                let reader = BufReader::new(stderr);
                for line in reader.lines() {
                    if let Ok(line) = line {
                        if let Ok(mut buf) = safety_buffer_clone.lock() {
                            buf.push(line);
                        }
                    }
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

            let mut mapper = crate::diagnostics::DiagnosticMapper::new(roots.workspace.clone());
            for line in reader.lines() {
                if let Ok(line) = line {
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
                                if let Ok(mut buf) = safety_buffer.lock() {
                                    buf.push(t);
                                }
                            }
                            _ => {}
                        }
                    } else {
                        if let Ok(mut buf) = safety_buffer.lock() {
                            buf.push(line);
                        }
                    }
                }
            }
        }

        pb.finish_and_clear();

        let status = child.wait().context("Failed to wait for charon")?;

        // FIXME: There's a subtle edge case here – if we get error output AND
        // Rustc ICE's, there's a good chance that the JSON error messages we
        // print won't include all relevant information – some will be printed
        // via stderr. In this case, `output_error = true` and so we bail and
        // discard stderr, which will swallow information from the user.
        if output_error {
            bail!("Diagnostic error in charon");
        } else if !status.success() {
            // "Silent Death" dump
            if let Ok(buf) = safety_buffer.lock() {
                for line in buf.iter() {
                    eprintln!("{}", line);
                }
            }
            bail!("Charon failed with status: {}", status);
        }
    }

    Ok(())
}
