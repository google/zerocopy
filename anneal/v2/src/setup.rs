// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use anyhow::Context as _;

pub struct SetupArgs {
    pub local_archive: Option<std::path::PathBuf>,
}

exocrate::config! {
    pub const CONFIG: Config = Config {
        rel_dir_path: [".anneal", "toolchain"],
        versioned_files: &["../Cargo.toml", "../Cargo.lock"],
    };
}

exocrate::parse_remote_archive! {
    pub const REMOTE: RemoteArchive = "Cargo.toml" [
        (linux, x86_64),
        (macos, x86_64),
        (linux, aarch64),
        (macos, aarch64),
    ];
}

pub enum Tool {
    Charon,
}

impl Tool {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Charon => "charon",
        }
    }

    pub fn path(&self, toolchain: &Toolchain) -> std::path::PathBuf {
        match self {
            Self::Charon => toolchain.aeneas_bin_dir().join(self.name()),
        }
    }
}

const AENEAS_DIR: &str = "aeneas";
const RUST_SYSROOT: &str = "rust";
const AENEAS_BIN_DIR: &str = "bin";
const RUST_BIN_DIR: &str = "bin";
const RUST_LIB_DIR: &str = "lib";

pub struct Toolchain {
    root: std::path::PathBuf,
}

impl Toolchain {
    pub fn resolve() -> anyhow::Result<Self> {
        let location = resolve_location();
        let root = CONFIG
            .resolve_installation_dir(location)
            .context("Toolchain not installed. Please run 'cargo anneal setup' first.")?;
        Ok(Self { root })
    }

    #[allow(dead_code)]
    pub fn root(&self) -> &std::path::Path {
        &self.root
    }

    pub fn aeneas_bin_dir(&self) -> std::path::PathBuf {
        self.root.join(AENEAS_DIR).join(AENEAS_BIN_DIR)
    }

    pub fn rust_sysroot(&self) -> std::path::PathBuf {
        self.root.join(RUST_SYSROOT)
    }

    pub fn rust_bin(&self) -> std::path::PathBuf {
        self.rust_sysroot().join(RUST_BIN_DIR)
    }

    pub fn rust_lib(&self) -> std::path::PathBuf {
        self.rust_sysroot().join(RUST_LIB_DIR)
    }

    pub fn command(&self, tool: Tool) -> anyhow::Result<std::process::Command> {
        let mut cmd = std::process::Command::new(tool.path(self));
        cmd.env_clear();
        match tool {
            Tool::Charon => {
                // The archive supplies `rustc`, but not `cargo` or host build
                // tools such as the linker. Keep the caller's `PATH` after
                // our Rust bin directory so Cargo builds use the managed Rust
                // toolchain while still finding those host tools.
                cmd.env("CHARON_TOOLCHAIN_IS_IN_PATH", "1")
                    .env("PATH", prepend_current_path(self.rust_bin())?)
                    .env(rust_library_path_env_var(), self.rust_lib());
            }
        }
        Ok(cmd)
    }
}

fn prepend_current_path(path: std::path::PathBuf) -> anyhow::Result<std::ffi::OsString> {
    let mut paths = vec![path];
    if let Some(current_path) = std::env::var_os("PATH") {
        paths.extend(std::env::split_paths(&current_path));
    }
    std::env::join_paths(paths).context("failed to construct PATH for tool command")
}

fn rust_library_path_env_var() -> &'static str {
    if cfg!(target_os = "macos") { "DYLD_LIBRARY_PATH" } else { "LD_LIBRARY_PATH" }
}

pub fn run_setup(args: SetupArgs) -> anyhow::Result<()> {
    let location = resolve_location();
    let source = match args.local_archive {
        Some(local_archive) => exocrate::Source::Local(local_archive),
        None => exocrate::Source::Remote(REMOTE),
    };

    let installation_dir = CONFIG
        .resolve_installation_dir_or_install(location, source)
        .context("failed to resolve-or-install dependencies")?;
    if let exocrate::ResolveOrInstallResult::AlreadyInstalled(_) = installation_dir {
        log::warn!("anneal toolchain was already installed at {:?}", installation_dir);
    } else {
        log::info!("anneal toolchain freshly installed at {:?}", installation_dir);
    }
    Ok(())
}

fn resolve_location() -> exocrate::Location {
    if std::env::var("__ANNEAL_LOCAL_DEV").is_ok() {
        exocrate::Location::LocalDev
    } else {
        exocrate::Location::UserGlobal
    }
}
