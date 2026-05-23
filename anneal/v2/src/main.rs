// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use anyhow::Context as _;
use clap::Parser as _;

mod charon;
mod diagnostics;
mod resolve;
mod scanner;
mod setup;
mod util;

/// Anneal
#[derive(clap::Parser, Debug)]
#[command(name = "cargo-anneal", version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(clap::Subcommand, Debug)]
enum Commands {
    /// Setup Anneal dependencies
    Setup(SetupArgs),
    /// Expand a crate (runs Charon)
    Expand(ExpandArgs),

    /// Helper to acquire shared or exclusive locks for multi-process integration testing (dev only)
    #[cfg(feature = "exocrate_tests")]
    TestLockHelper {
        /// The role to run as: 'reader-a', 'reader-b', 'writer-a', or 'reader-exclusion'
        #[arg(long)]
        role: String,
        /// Path to the directory to lock
        #[arg(long)]
        lock_dir: std::path::PathBuf,
        /// Path to the shared log file where lock transitions are appended
        #[arg(long)]
        log_file: std::path::PathBuf,
        /// Path to the temporary synchronization signal file
        #[arg(long)]
        sig_file: std::path::PathBuf,
    },
}

#[derive(clap::Parser, Debug)]
pub struct SetupArgs {
    /// Path to a local dependency archive to use instead of downloading
    #[arg(long, value_name = "path-to-local-archive")]
    pub local_archive: Option<std::path::PathBuf>,
}

#[derive(clap::Parser, Debug)]
pub struct ExpandArgs {
    #[command(flatten)]
    pub resolve_args: crate::resolve::Args,

    /// Controls where LLBC output is placed on the filesystem
    #[arg(long, value_name = "output-dir")]
    pub output_dir: Option<std::path::PathBuf>,

    /// Do not show compilation progress bars
    #[arg(long)]
    pub no_progress: bool,
}

fn setup(args: SetupArgs) -> anyhow::Result<()> {
    crate::setup::run_setup(crate::setup::SetupArgs { local_archive: args.local_archive })
        .context("Failed to setup toolchain")
}

fn expand(args: ExpandArgs) -> anyhow::Result<()> {
    let roots = crate::resolve::resolve_roots(&args.resolve_args)?;
    let packages = crate::scanner::scan_workspace(&roots)?;
    if packages.is_empty() {
        log::warn!("No targets found to expand.");
        return Ok(());
    }
    let mut locked_roots = roots.lock_run_root()?;
    if let Some(output_dir) = args.output_dir {
        locked_roots.llbc_override = Some(output_dir);
    }
    let toolchain = crate::setup::Toolchain::resolve()?;
    let show_progress = !args.no_progress;
    crate::charon::run_charon(
        &args.resolve_args,
        &toolchain,
        &locked_roots,
        &packages,
        show_progress,
    )?;
    Ok(())
}

fn main() -> anyhow::Result<()> {
    // Suppressing timestamps removes a source of nondeterminism that is
    // difficult to work around in integration tests.
    env_logger::builder().format_timestamp(None).init();

    let mut args_iter = std::env::args_os().peekable();
    let bin_name = args_iter.next().unwrap_or_else(|| "cargo-anneal".into());
    // If we're being run as a cargo plugin, the second argument will be "anneal".
    if args_iter.peek().is_some_and(|arg| arg == "anneal") {
        args_iter.next();
    }
    let args = Cli::parse_from(std::iter::once(bin_name).chain(args_iter));

    match args.command {
        Commands::Setup(args) => setup(args),
        Commands::Expand(args) => expand(args),

        #[cfg(feature = "exocrate_tests")]
        Commands::TestLockHelper { role, lock_dir, log_file, sig_file } => {
            crate::util::run_test_lock_helper(&role, &lock_dir, &log_file, &sig_file)
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "exocrate_tests")]
    mod exocrate_tests {
        use std::{
            ffi::OsString,
            fs, io,
            path::{Path, PathBuf},
            process::Command,
            sync::OnceLock,
        };

        use serde_json::{Value, json};

        const LOCAL_ARCHIVE: &str = "target/anneal-exocrate.tar.zst";
        static INSTALLATION_DIR: OnceLock<PathBuf> = OnceLock::new();

        #[test]
        fn test_setup() {
            install_local_archive();
        }

        #[test]
        fn test_setup_and_toolchain_paths() {
            install_local_archive();

            let toolchain =
                crate::setup::Toolchain::resolve().expect("Failed to resolve toolchain");

            assert!(toolchain.root().is_dir(), "root is not a directory: {:?}", toolchain.root());
            assert!(
                toolchain.aeneas_bin_dir().is_dir(),
                "aeneas_bin_dir is not a directory: {:?}",
                toolchain.aeneas_bin_dir()
            );
            assert!(
                toolchain.rust_sysroot().is_dir(),
                "rust_sysroot is not a directory: {:?}",
                toolchain.rust_sysroot()
            );
            assert!(
                toolchain.rust_bin().is_dir(),
                "rust_bin is not a directory: {:?}",
                toolchain.rust_bin()
            );
            assert!(
                toolchain.rust_lib().is_dir(),
                "rust_lib is not a directory: {:?}",
                toolchain.rust_lib()
            );
        }

        #[test]
        fn test_archive_lake_cache_reuse() {
            let installation_dir = install_local_archive();
            let temp = tempfile::Builder::new()
                .prefix("anneal-v2-archive-cache-reuse-")
                .tempdir()
                .expect("failed to create archive cache reuse tempdir");
            assert_archive_lake_cache_reuse(&installation_dir, temp.path())
                .expect("archive Lake cache reuse test failed");
        }

        fn install_local_archive() -> PathBuf {
            // ASSUMPTION: The CI dependency builder downloads the Nix-built
            // archive artifact to this path before running v2 tests.
            INSTALLATION_DIR
                .get_or_init(|| {
                    super::super::setup(super::super::SetupArgs {
                        local_archive: Some(LOCAL_ARCHIVE.into()),
                    })
                    .expect("Failed to run setup");
                    crate::setup::Toolchain::resolve()
                        .expect("Failed to resolve toolchain")
                        .root()
                        .to_path_buf()
                })
                .clone()
        }

        fn assert_archive_lake_cache_reuse(
            toolchain_root: &Path,
            temp_root: &Path,
        ) -> Result<(), Box<dyn std::error::Error>> {
            let aeneas_root = toolchain_root.join("aeneas");
            let aeneas_lean = aeneas_root.join("backends/lean");
            let lean_root = toolchain_root.join("lean");
            let workspace = temp_root.join("generated-workspace");

            assert_no_write_bits(&aeneas_root)?;

            fs::create_dir_all(workspace.join("generated"))?;
            fs::copy(aeneas_lean.join("lean-toolchain"), workspace.join("lean-toolchain"))?;
            fs::write(workspace.join("generated/Generated.lean"), "import Aeneas\n")?;
            fs::write(
                workspace.join("lakefile.lean"),
                format!(
                    r#"import Lake
open Lake DSL

require aeneas from "{}"

package anneal_verification

@[default_target]
lean_lib Generated where
  srcDir := "generated"
  roots := #[`Generated]
"#,
                    lake_string(&aeneas_lean)
                ),
            )?;
            write_relative_archive_manifest(&workspace, &aeneas_lean)?;

            // The Nix archive must support fresh generated workspaces without
            // reconfiguring packages or rebuilding read-only Lake artifacts.
            run_lake_archive_command(
                &workspace,
                &lean_root,
                &["--keep-toolchain", "--old", "build", "Generated"],
            )?;
            run_lake_archive_command(
                &workspace,
                &lean_root,
                &["--keep-toolchain", "env", "lean", "--json", "generated/Generated.lean"],
            )?;

            Ok(())
        }

        fn assert_no_write_bits(root: &Path) -> Result<(), Box<dyn std::error::Error>> {
            let metadata = fs::symlink_metadata(root)?;
            if metadata.file_type().is_symlink() {
                return Ok(());
            }
            if has_write_bits(&metadata.permissions()) {
                panic!("archive path should be read-only: {}", root.display());
            }
            if metadata.is_dir() {
                for entry in fs::read_dir(root)? {
                    assert_no_write_bits(&entry?.path())?;
                }
            }
            Ok(())
        }

        #[cfg(unix)]
        fn has_write_bits(permissions: &fs::Permissions) -> bool {
            use std::os::unix::fs::PermissionsExt as _;
            permissions.mode() & 0o222 != 0
        }

        #[cfg(not(unix))]
        fn has_write_bits(permissions: &fs::Permissions) -> bool {
            !permissions.readonly()
        }

        fn write_relative_archive_manifest(
            workspace: &Path,
            aeneas_lean: &Path,
        ) -> Result<(), Box<dyn std::error::Error>> {
            let aeneas_lean = fs::canonicalize(aeneas_lean)?;
            let workspace = fs::canonicalize(workspace)?;
            let manifest_path = aeneas_lean.join("lake-manifest.json");
            let manifest: Value = serde_json::from_reader(fs::File::open(&manifest_path)?)?;
            let aeneas_packages =
                manifest.get("packages").and_then(Value::as_array).ok_or_else(|| {
                    invalid_data(format!(
                        "Aeneas Lake manifest {} is missing packages",
                        manifest_path.display()
                    ))
                })?;

            let aeneas_dir = relative_manifest_string(&aeneas_lean, &workspace)?;
            let mut packages = vec![json!({
                "type": "path",
                "name": "aeneas",
                "dir": aeneas_dir,
                "inherited": false,
            })];

            for entry in aeneas_packages {
                let mut entry = entry.as_object().cloned().ok_or_else(|| {
                    invalid_data("Aeneas Lake manifest package entry is not an object")
                })?;
                let package_type = entry.get("type").and_then(Value::as_str).ok_or_else(|| {
                    invalid_data("Aeneas Lake manifest package entry is missing type")
                })?;
                if package_type != "path" {
                    return Err(invalid_data(format!(
                        "Aeneas Lake manifest package entry is {package_type:?}, not a path dependency"
                    ))
                    .into());
                }
                let package_dir = entry.get("dir").and_then(Value::as_str).ok_or_else(|| {
                    invalid_data("Aeneas Lake manifest package entry is missing dir")
                })?;
                let package_dir = Path::new(package_dir);
                let package_dir = if package_dir.is_absolute() {
                    package_dir.to_path_buf()
                } else {
                    aeneas_lean.join(package_dir)
                };
                let package_dir = fs::canonicalize(package_dir)?;
                entry.insert(
                    "dir".to_string(),
                    json!(relative_manifest_string(&package_dir, &workspace)?),
                );
                entry.insert("inherited".to_string(), json!(true));
                packages.push(Value::Object(entry));
            }

            let manifest = json!({
                "version": "1.2.0",
                "packagesDir": ".lake/packages",
                "packages": packages,
                "name": "anneal_verification",
                "lakeDir": ".lake",
                "fixedToolchain": false,
            });
            fs::write(
                workspace.join("lake-manifest.json"),
                format!("{}\n", serde_json::to_string_pretty(&manifest)?),
            )?;
            Ok(())
        }

        fn relative_manifest_string(
            path: &Path,
            base: &Path,
        ) -> Result<String, Box<dyn std::error::Error>> {
            let path = pathdiff::diff_paths(path, base).ok_or_else(|| {
                invalid_data(format!(
                    "failed to compute relative path from {} to {}",
                    base.display(),
                    path.display()
                ))
            })?;
            Ok(path.to_string_lossy().into_owned())
        }

        fn lake_string(path: &Path) -> String {
            path.to_string_lossy().replace('\\', "\\\\").replace('"', "\\\"")
        }

        fn run_lake_archive_command(
            workspace: &Path,
            lean_root: &Path,
            args: &[&str],
        ) -> Result<(), Box<dyn std::error::Error>> {
            let lean_bin = lean_root.join("bin");
            let mut cmd = Command::new(lean_bin.join("lake"));
            cmd.args(args)
                .current_dir(workspace)
                .env_remove("CI")
                .env("LEAN_SYSROOT", lean_root)
                .env("MATHLIB_NO_CACHE_ON_UPDATE", "1")
                .env("PATH", prepend_env_paths("PATH", &[lean_bin])?);

            let lib_var =
                if cfg!(target_os = "macos") { "DYLD_LIBRARY_PATH" } else { "LD_LIBRARY_PATH" };
            cmd.env(
                lib_var,
                prepend_env_paths(lib_var, &[lean_root.join("lib"), lean_root.join("lib/lean")])?,
            );

            let output = cmd.output()?;
            if !output.status.success() {
                return Err(io::Error::other(format!(
                    "lake {:?} failed with status {}\nstdout:\n{}\nstderr:\n{}",
                    args,
                    output.status,
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                ))
                .into());
            }
            Ok(())
        }

        fn prepend_env_paths(
            var_name: &str,
            new_paths: &[PathBuf],
        ) -> Result<OsString, Box<dyn std::error::Error>> {
            let mut paths = new_paths.to_vec();
            if let Some(existing) = std::env::var_os(var_name) {
                paths.extend(std::env::split_paths(&existing));
            }
            Ok(std::env::join_paths(paths)?)
        }

        fn invalid_data(message: impl Into<String>) -> io::Error {
            io::Error::new(io::ErrorKind::InvalidData, message.into())
        }
    }
}
