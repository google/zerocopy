// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{path::Path, process::Command};

use anyhow::{Context, Result, anyhow};

/// Runs the Charon tool to extract LLBC (Low-Level Borrow Calculus) from the crate.
///
/// # Arguments
/// * `crate_root` - Path to the root of the crate to analyze.
/// * `dest_file` - Destination path for the LLBC file (e.g. `.../crate.llbc`).
/// * `manifest_path` - Optional path to a specific Cargo.toml or script file.
pub fn run_charon(crate_root: &Path, dest_file: &Path, manifest_path: Option<&Path>) -> Result<()> {
    let crate_root = crate_root.to_str().unwrap();
    let dest_file = dest_file.to_str().unwrap();

    println!("Running charon in {:?}", crate_root);
    let mut cmd = Command::new("charon");
    cmd.current_dir(crate_root);
    cmd.arg("cargo");

    // Charon args first
    args(&mut cmd, &["--dest-file", dest_file, "--preset", "aeneas"]);

    if let Some(path) = manifest_path {
        cmd.arg("--");
        if path.extension().map_or(false, |e| e == "rs") {
            cmd.arg("-Zscript");
        }
        cmd.arg("--manifest-path");
        cmd.arg(path);
    }

    let status = cmd.status().context("Failed to execute charon. Ensure it is in your PATH.")?;
    if !status.success() {
        return Err(anyhow!("charon failed with exit code: {}", status));
    }
    Ok(())
}

/// Runs the Aeneas tool to translate LLBC files into Lean code.
///
/// # Arguments
/// * `llbc_path` - Path to the input LLBC file.
/// * `dest` - Destination directory for the generated Lean files.
pub fn run_aeneas(llbc_path: &Path, dest: &Path) -> Result<()> {
    let llbc_path = llbc_path.to_str().unwrap();
    let dest = dest.to_str().unwrap();

    let mut cmd = Command::new("aeneas");
    args(&mut cmd, &["-backend", "lean", llbc_path, "-dest", dest]);
    let status = cmd.status().context("Failed to execute aeneas. Ensure it is in your PATH.")?;

    if !status.success() {
        return Err(anyhow!("aeneas failed with exit code: {}", status));
    }
    Ok(())
}

/// Runs `lake build` to compile and verify the generated Lean code.
///
/// # Arguments
/// * `dir` - Directory containing the `lakefile.lean`.
pub fn run_lake_build(dir: &Path) -> Result<()> {
    let status = Command::new("lake")
        .current_dir(dir)
        .arg("build")
        .status()
        .context("Failed to execute lake. Ensure Lean 4 is installed.")?;

    if !status.success() {
        return Err(anyhow!("lake build failed with exit code: {}", status));
    }
    Ok(())
}

fn args(cmd: &mut Command, args: &[&str]) {
    for arg in args {
        cmd.arg(arg);
    }
}
