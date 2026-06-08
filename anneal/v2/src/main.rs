// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use clap::Parser as _;

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
}

#[derive(clap::Parser, Debug)]
pub struct SetupArgs {
    /// Path to a local dependency archive to use instead of downloading.
    #[arg(long, value_name = "path-to-local-archive")]
    pub local_archive: Option<std::path::PathBuf>,
}

exocrate::config! {
    const CONFIG: Config = Config {
        rel_dir_path: [".anneal", "toolchain"],
        versioned_files: &["../Cargo.toml", "../Cargo.lock"],
    };
}

exocrate::parse_remote_archive! {
    const REMOTE: RemoteArchive = "Cargo.toml" [
        (linux, x86_64),
        (macos, x86_64),
        (linux, aarch64),
        (macos, aarch64),
    ];
}

fn setup_installation_dir(args: SetupArgs) -> std::path::PathBuf {
    let location = if std::env::var("__ANNEAL_LOCAL_DEV").is_ok() {
        exocrate::Location::LocalDev
    } else {
        exocrate::Location::UserGlobal
    };
    let source = match args.local_archive {
        Some(local_archive) => exocrate::Source::Local(local_archive),
        None => exocrate::Source::Remote(REMOTE),
    };

    CONFIG
        .resolve_installation_dir_or_install(location, source)
        // FIXME: Implement unified error reporting (e.g., via `anyhow`).
        .expect("failed to resolve-or-install dependencies")
}

fn setup(args: SetupArgs) {
    let installation_dir = setup_installation_dir(args);
    log::info!("anneal toolchain is installed at {:?}", installation_dir);
}

fn main() {
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
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "exocrate_tests")]
    mod exocrate_tests {
        use std::{
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
                    super::super::setup_installation_dir(super::super::SetupArgs {
                        local_archive: Some(LOCAL_ARCHIVE.into()),
                    })
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
            cmd.args(args).current_dir(workspace).env_clear();

            let lib_var =
                if cfg!(target_os = "macos") { "DYLD_LIBRARY_PATH" } else { "LD_LIBRARY_PATH" };
            cmd.env(
                lib_var,
                std::env::join_paths([lean_root.join("lib"), lean_root.join("lib/lean")])?,
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

        fn invalid_data(message: impl Into<String>) -> io::Error {
            io::Error::new(io::ErrorKind::InvalidData, message.into())
        }
    }
}
