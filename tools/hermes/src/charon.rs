use std::{
    io::{BufRead, BufReader},
    process::Command,
};

use anyhow::{bail, Context as _, Result};
use cargo_metadata::{diagnostic::DiagnosticLevel, Message};

use crate::{
    parse::{attr::FunctionBlockInner, ParsedItem},
    resolve::{Args, HermesTargetKind, Roots},
    scanner::HermesArtifact,
};

pub fn run_charon(args: &Args, roots: &Roots, packages: &[HermesArtifact]) -> Result<()> {
    let llbc_root = roots.llbc_root();

    std::fs::create_dir_all(&llbc_root).context("Failed to create LLBC output directory")?;

    for artifact in packages {
        if artifact.start_from.is_empty() {
            continue;
        }

        log::info!("Invoking Charon on package '{}'...", artifact.name.package_name);

        let mut cmd = Command::new("charon");
        cmd.arg("cargo");
        cmd.arg("--preset=aeneas");

        // Output artifacts to target/hermes/<hash>/llbc
        let llbc_path = llbc_root.join(artifact.llbc_file_name());
        log::debug!("Writing .llbc file to {}", llbc_path.display());
        cmd.arg("--dest-file").arg(llbc_path);

        // Fail fast on errors
        cmd.arg("--abort-on-error");

        for item in &artifact.items {
            if let ParsedItem::Function(func) = &item.item {
                // Check if the function body is an Axiom (unsafe)
                if let FunctionBlockInner::Axiom { .. } = func.hermes.inner {
                    // Construct the fully qualified name: Crate::Mod::Func
                    let mut full_path = vec!["crate"];
                    full_path.extend(item.module_path.iter().map(|s| s.as_str()));
                    full_path.push(func.item.name());

                    let opaque_name = full_path.join("::");

                    cmd.args(["--opaque", &opaque_name]);
                }
            }
        }

        // Start translation from specific entry points. Sort to ensure
        // deterministic ordering for testing (not important in production).
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

            let mut mapper = crate::diagnostics::DiagnosticMapper::new(roots.workspace.clone());
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
