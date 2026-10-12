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
    Cargo,
    Charon,
    Rustc,
}

impl Tool {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Cargo => "cargo",
            Self::Charon => "charon",
            Self::Rustc => "rustc",
        }
    }

    pub fn path(&self, toolchain: &Toolchain) -> std::path::PathBuf {
        match self {
            Self::Cargo | Self::Rustc => toolchain.rust_bin().join(self.name()),
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

    #[cfg(all(test, feature = "exocrate_tests"))]
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
            Tool::Cargo | Tool::Rustc => {}
            Tool::Charon => {
                copy_cargo_build_environment(&mut cmd);

                // The archive supplies Rust tools, but not host build tools
                // such as the linker. Keep the caller's `PATH` after our Rust
                // bin directory so Cargo builds use the managed Rust toolchain
                // while still finding those host tools.
                cmd.env("CHARON_TOOLCHAIN_IS_IN_PATH", "1")
                    .env("PATH", prepend_current_path(self.rust_bin())?)
                    // Override compiler and workspace-wrapper settings that
                    // may otherwise come from the copied `CARGO_HOME` config.
                    .env("RUSTC", Tool::Rustc.path(self))
                    .env("RUSTC_WORKSPACE_WRAPPER", "")
                    .env(rust_library_path_env_var(), self.rust_lib());
            }
        }
        Ok(cmd)
    }
}

/// Copies the documented Cargo inputs that can affect a build.
///
/// Charon launches Cargo as a child process, so clearing its environment must
/// not silently discard build configuration such as `RUSTFLAGS`,
/// `CARGO_HOME`, target-specific linker settings, or registry configuration.
/// We intentionally do not copy arbitrary variables: Anneal starts from an
/// empty environment and admits only variables documented in Cargo's
/// [environment-variable reference].
///
/// Tool-selection and output-directory variables are deliberately absent.
/// Anneal supplies the pinned Rust toolchain through `PATH`, Charon owns the
/// compiler wrappers used to intercept rustc, and `run_charon` supplies an
/// isolated `CARGO_TARGET_DIR`.
///
/// [environment-variable reference]: https://doc.rust-lang.org/cargo/reference/environment-variables.html
fn copy_cargo_build_environment(cmd: &mut std::process::Command) {
    cmd.envs(std::env::vars_os().filter(|(name, _)| is_cargo_build_environment_variable(name)));
}

fn is_cargo_build_environment_variable(name: &std::ffi::OsStr) -> bool {
    let Some(name) = name.to_str() else {
        return false;
    };

    // These are documented configuration families whose variable portions
    // are profile names, target triples, or registry names.
    const PREFIXES: &[&str] = &[
        "CARGO_CACHE_",
        "CARGO_CREDENTIAL_ALIAS_",
        "CARGO_HTTP_",
        "CARGO_NET_",
        "CARGO_PROFILE_",
        "CARGO_REGISTRIES_",
        "CARGO_REGISTRY_",
        "CARGO_RESOLVER_",
        "CARGO_TARGET_",
        "CARGO_TERM_",
    ];

    // Anneal owns these despite their matching a family above.
    const MANAGED: &[&str] = &[
        "CARGO_BUILD_BUILD_DIR",
        "CARGO_BUILD_RUSTC",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_TARGET_DIR",
        "CARGO_TARGET_DIR",
    ];
    if MANAGED.contains(&name) {
        return false;
    }

    const EXACT: &[&str] = &[
        "CARGO_BUILD_DEP_INFO_BASEDIR",
        "CARGO_BUILD_INCREMENTAL",
        "CARGO_BUILD_JOBS",
        "CARGO_BUILD_RUSTDOCFLAGS",
        "CARGO_BUILD_RUSTFLAGS",
        "CARGO_BUILD_TARGET",
        "CARGO_BUILD_WARNINGS",
        "CARGO_CACHE_RUSTC_INFO",
        "CARGO_ENCODED_RUSTDOCFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_FUTURE_INCOMPAT_REPORT_FREQUENCY",
        "CARGO_HOME",
        "CARGO_INCREMENTAL",
        "CARGO_LOG",
        "CARGO_MAKEFLAGS",
        "HTTP_PROXY",
        "HTTPS_PROXY",
        "HTTP_TIMEOUT",
        "RUSTDOCFLAGS",
        "RUSTFLAGS",
        "TERM",
        "http_proxy",
        "https_proxy",
    ];

    EXACT.contains(&name) || PREFIXES.iter().any(|prefix| name.starts_with(prefix))
}

fn prepend_current_path(path: std::path::PathBuf) -> anyhow::Result<std::ffi::OsString> {
    let mut paths = vec![path];
    if let Some(current_path) = std::env::var_os("PATH") {
        paths.extend(std::env::split_paths(&current_path));
    }
    std::env::join_paths(paths).context("failed to construct PATH for tool command")
}

/// Returns the platform library search path variable used by Rust tools.
pub(crate) fn rust_library_path_env_var() -> &'static str {
    if cfg!(target_os = "macos") { "DYLD_LIBRARY_PATH" } else { "LD_LIBRARY_PATH" }
}

pub fn run_setup(args: SetupArgs) -> anyhow::Result<()> {
    let location = resolve_location();
    let source = match args.local_archive {
        Some(local_archive) => exocrate::Source::Local(local_archive),
        None => exocrate::Source::Remote(REMOTE),
    };

    let (installation_dir, status) = CONFIG
        .resolve_installation_dir_or_install(location, source)
        .context("failed to resolve-or-install dependencies")?;
    match status {
        exocrate::ResolvedOrInstalled::ResolvedExisting => {
            log::warn!("anneal toolchain was already installed at {:?}", installation_dir);
        }
        exocrate::ResolvedOrInstalled::NewlyInstalled => {
            log::info!("anneal toolchain freshly installed at {:?}", installation_dir);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::is_cargo_build_environment_variable;

    #[test]
    fn cargo_build_environment_filter() {
        for name in [
            "RUSTFLAGS",
            "CARGO_HOME",
            "CARGO_BUILD_JOBS",
            "CARGO_PROFILE_RELEASE_LTO",
            "CARGO_REGISTRIES_PRIVATE_TOKEN",
            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER",
            "https_proxy",
        ] {
            assert!(
                is_cargo_build_environment_variable(name.as_ref()),
                "expected {name} to be copied"
            );
        }

        for name in [
            "HOME",
            "ANNEAL_TEST_BUILD_INPUT",
            "CARGO_PKG_NAME",
            "RUSTC",
            "RUSTC_WRAPPER",
            "CARGO_BUILD_RUSTC",
            "CARGO_BUILD_RUSTC_WRAPPER",
            "CARGO_BUILD_TARGET_DIR",
            "CARGO_TARGET_DIR",
        ] {
            assert!(
                !is_cargo_build_environment_variable(name.as_ref()),
                "expected {name} to remain cleared"
            );
        }
    }
}

fn resolve_location() -> exocrate::Location {
    if std::env::var("__ANNEAL_LOCAL_DEV").is_ok() {
        exocrate::Location::LocalDev
    } else {
        exocrate::Location::UserGlobal
    }
}
