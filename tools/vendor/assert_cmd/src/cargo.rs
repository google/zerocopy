//! Simplify running `bin`s in a Cargo project.
//!
//! [`CommandCargoExt`] is an extension trait for [`Command`] to easily launch a crate's
//! binaries.
//!
//! # Examples
//!
//! Simple case:
//!
//! ```rust,no_run
//! use assert_cmd::prelude::*;
//! use assert_cmd::pkg_name;
//!
//! use std::process::Command;
//!
//! let mut cmd = Command::cargo_bin(pkg_name!())
//!     .unwrap();
//! let output = cmd.unwrap();
//! ```
//!
//! # Limitations
//!
//! - Only works within the context of integration tests.  See [`escargot`] for a more
//!   flexible API.
//! - Only reuses your existing feature flags, targets, or build mode.
//! - Only works with cargo binaries (`cargo test` ensures they are built).
//!
//! If you run into these limitations, we recommend trying out [`escargot`]:
//!
//! ```rust,no_run
//! use assert_cmd::prelude::*;
//!
//! use std::process::Command;
//!
//! let bin_under_test = escargot::CargoBuild::new()
//!     .bin("bin_fixture")
//!     .current_release()
//!     .current_target()
//!     .run()
//!     .unwrap();
//! let mut cmd = bin_under_test.command();
//! let output = cmd.unwrap();
//! println!("{:?}", output);
//! ```
//!
//! Notes:
//! - There is a [noticeable per-call overhead][cargo-overhead] for `CargoBuild`.  We recommend
//!   caching the binary location (`.path()` instead of `.command()`) with [`lazy_static`].
//! - `.current_target()` improves platform coverage at the cost of [slower test runs if you don't
//!   explicitly pass `--target <TRIPLET>` on the command line][first-call].
//!
//! [`lazy_static`]: https://crates.io/crates/lazy_static
//! [`Command`]: std::process::Command
//! [`escargot`]: https://crates.io/crates/escargot
//! [cargo-overhead]: https://github.com/assert-rs/assert_cmd/issues/6
//! [first-call]: https://github.com/assert-rs/assert_cmd/issues/57

use std::env;
use std::error::Error;
use std::fmt;
use std::path;
use std::process;

#[doc(inline)]
pub use crate::cargo_bin;
#[doc(inline)]
pub use crate::cargo_bin_cmd;

/// Create a [`Command`] for a `bin` in the Cargo project.
///
/// `CommandCargoExt` is an extension trait for [`Command`][std::process::Command] to easily launch a crate's
/// binaries.
///
/// See the [`cargo` module documentation][super::cargo] for caveats and workarounds.
///
/// # Examples
///
/// ```rust,no_run
/// use assert_cmd::prelude::*;
/// use assert_cmd::pkg_name;
///
/// use std::process::Command;
///
/// let mut cmd = Command::cargo_bin(pkg_name!())
///     .unwrap();
/// let output = cmd.unwrap();
/// println!("{:?}", output);
/// ```
///
/// [`Command`]: std::process::Command
pub trait CommandCargoExt
where
    Self: Sized,
{
    /// Create a [`Command`] to run a specific binary of the current crate.
    ///
    /// See the [`cargo` module documentation][crate::cargo] for caveats and workarounds.
    ///
    /// The [`Command`] created with this method may run the binary through a runner, as configured
    /// in the `CARGO_TARGET_<TRIPLET>_RUNNER` environment variable.  This is useful for running
    /// binaries that can't be launched directly, such as cross-compiled binaries. When using
    /// this method with [cross](https://github.com/cross-rs/cross), no extra configuration is
    /// needed.
    ///
    /// Cargo support:
    /// - `>1.94`: works
    /// - `>=1.91,<=1.93`: works with default `build-dir`
    /// - `<=1.92`: works
    ///
    /// # Panic
    ///
    /// Panicks if no binary is found
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use assert_cmd::prelude::*;
    /// use assert_cmd::pkg_name;
    ///
    /// use std::process::Command;
    ///
    /// let mut cmd = Command::cargo_bin(pkg_name!())
    ///     .unwrap();
    /// let output = cmd.unwrap();
    /// println!("{:?}", output);
    /// ```
    ///
    /// ```rust,no_run
    /// use assert_cmd::prelude::*;
    ///
    /// use std::process::Command;
    ///
    /// let mut cmd = Command::cargo_bin("bin_fixture")
    ///     .unwrap();
    /// let output = cmd.unwrap();
    /// println!("{:?}", output);
    /// ```
    ///
    /// [`Command`]: std::process::Command
    fn cargo_bin<S: AsRef<str>>(name: S) -> Result<Self, CargoError>;
}

impl CommandCargoExt for crate::cmd::Command {
    fn cargo_bin<S: AsRef<str>>(name: S) -> Result<Self, CargoError> {
        crate::cmd::Command::cargo_bin(name)
    }
}

impl CommandCargoExt for process::Command {
    fn cargo_bin<S: AsRef<str>>(name: S) -> Result<Self, CargoError> {
        cargo_bin_cmd(name)
    }
}

pub(crate) fn cargo_bin_cmd<S: AsRef<str>>(name: S) -> Result<process::Command, CargoError> {
    let path = cargo_bin(name);
    if path.is_file() {
        if let Some(runner) = cargo_runner() {
            let mut cmd = process::Command::new(&runner[0]);
            cmd.args(&runner[1..]).arg(path);
            Ok(cmd)
        } else {
            Ok(process::Command::new(path))
        }
    } else {
        Err(CargoError::with_cause(NotFoundError { path }))
    }
}

pub(crate) fn cargo_runner() -> Option<Vec<String>> {
    let runner_env = format!(
        "CARGO_TARGET_{}_RUNNER",
        CURRENT_TARGET.replace('-', "_").to_uppercase()
    );
    let runner = env::var(runner_env).ok()?;
    Some(runner.split(' ').map(str::to_string).collect())
}

/// Error when finding crate binary.
#[derive(Debug)]
pub struct CargoError {
    cause: Option<Box<dyn Error + Send + Sync + 'static>>,
}

impl CargoError {
    /// Wrap the underlying error for passing up.
    pub fn with_cause<E>(cause: E) -> Self
    where
        E: Error + Send + Sync + 'static,
    {
        let cause = Box::new(cause);
        Self { cause: Some(cause) }
    }
}

impl Error for CargoError {}

impl fmt::Display for CargoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ref cause) = self.cause {
            writeln!(f, "Cause: {cause}")?;
        }
        Ok(())
    }
}

/// Error when finding crate binary.
#[derive(Debug)]
struct NotFoundError {
    path: path::PathBuf,
}

impl Error for NotFoundError {}

impl fmt::Display for NotFoundError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Cargo command not found: {}", self.path.display())
    }
}

/// Look up the path to a cargo-built binary within an integration test
///
/// Cargo support:
/// - `>1.94`: works
/// - `>=1.91,<=1.93`: works with default `build-dir`
/// - `<=1.92`: works
///
/// # Panic
///
/// Panicks if no binary is found
pub fn cargo_bin<S: AsRef<str>>(name: S) -> path::PathBuf {
    cargo_bin_str(name.as_ref())
}

fn cargo_bin_str(name: &str) -> path::PathBuf {
    let env_var = format!("{CARGO_BIN_EXE_}{name}");
    env::var_os(env_var)
        .map(|p| p.into())
        .or_else(|| legacy_cargo_bin(name))
        .unwrap_or_else(|| missing_cargo_bin(name))
}

const CARGO_BIN_EXE_: &str = "CARGO_BIN_EXE_";

fn missing_cargo_bin(name: &str) -> ! {
    let possible_names: Vec<_> = env::vars_os()
        .filter_map(|(k, _)| k.into_string().ok())
        .filter_map(|k| k.strip_prefix(CARGO_BIN_EXE_).map(|s| s.to_owned()))
        .collect();
    if possible_names.is_empty() {
        panic!("`CARGO_BIN_EXE_{name}` is unset
help: if this is running within a unit test, move it to an integration test to gain access to `CARGO_BIN_EXE_{name}`")
    } else {
        let mut names = String::new();
        for (i, name) in possible_names.iter().enumerate() {
            use std::fmt::Write as _;
            if i != 0 {
                let _ = write!(&mut names, ", ");
            }
            let _ = write!(&mut names, "\"{name}\"");
        }
        panic!(
            "`CARGO_BIN_EXE_{name}` is unset
help: available binary names are {names}"
        )
    }
}

fn legacy_cargo_bin(name: &str) -> Option<path::PathBuf> {
    let target_dir = target_dir()?;
    let bin_path = target_dir.join(format!("{}{}", name, env::consts::EXE_SUFFIX));
    if !bin_path.exists() {
        return None;
    }
    Some(bin_path)
}

// Adapted from
// https://github.com/rust-lang/cargo/blob/485670b3983b52289a2f353d589c57fae2f60f82/tests/testsuite/support/mod.rs#L507
fn target_dir() -> Option<path::PathBuf> {
    let mut path = env::current_exe().ok()?;
    let _test_bin_name = path.pop();
    if path.ends_with("deps") {
        let _deps = path.pop();
    }
    Some(path)
}

/// The current process' target triplet.
const CURRENT_TARGET: &str = include_str!(concat!(env!("OUT_DIR"), "/current_target.txt"));

#[test]
#[should_panic = "`CARGO_BIN_EXE_non-existent` is unset
help: if this is running within a unit test, move it to an integration test to gain access to `CARGO_BIN_EXE_non-existent`"]
fn cargo_bin_in_unit_test() {
    cargo_bin("non-existent");
}
