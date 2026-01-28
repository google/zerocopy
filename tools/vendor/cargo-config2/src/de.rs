// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Cargo configuration that environment variables, config overrides, and
//! target-specific configurations have not been resolved.

#[path = "gen/de.rs"]
mod generated;

use core::{fmt, iter, slice, str::FromStr};
use std::{
    borrow::Cow,
    collections::BTreeMap,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
};

use serde::{
    de::{self, Deserialize, Deserializer},
    ser::{Serialize, Serializer},
};
use serde_derive::{Deserialize, Serialize};

pub use crate::value::{Definition, Value};
use crate::{
    easy,
    error::{Context as _, Error, Result},
    merge::Merge,
    resolve::{ResolveContext, TargetTripleRef},
    value::SetPath,
    walk,
};

/// Cargo configuration that environment variables, config overrides, and
/// target-specific configurations have not been resolved.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct Config {
    // TODO: paths
    /// The `[alias]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#alias)
    #[serde(default)]
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub alias: BTreeMap<String, StringList>,
    /// The `[build]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#build)
    #[serde(default)]
    #[serde(skip_serializing_if = "BuildConfig::is_none")]
    pub build: BuildConfig,
    /// The `[credential-alias]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#credential-alias)
    #[serde(default)]
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub credential_alias: BTreeMap<String, PathAndArgs>,
    /// The `[doc]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#doc)
    #[serde(default)]
    #[serde(skip_serializing_if = "DocConfig::is_none")]
    pub doc: DocConfig,
    /// The `[env]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#env)
    #[serde(default)]
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub env: BTreeMap<String, EnvConfigValue>,
    /// The `[future-incompat-report]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#future-incompat-report)
    #[serde(default)]
    #[serde(skip_serializing_if = "FutureIncompatReportConfig::is_none")]
    pub future_incompat_report: FutureIncompatReportConfig,
    /// The `[cargo-new]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#cargo-new)
    #[serde(default)]
    #[serde(skip_serializing_if = "CargoNewConfig::is_none")]
    pub cargo_new: CargoNewConfig,
    /// The `[http]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#http)
    #[serde(default)]
    #[serde(skip_serializing_if = "HttpConfig::is_none")]
    pub http: HttpConfig,
    // TODO: install
    /// The `[net]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#net)
    #[serde(default)]
    #[serde(skip_serializing_if = "NetConfig::is_none")]
    pub net: NetConfig,
    // TODO: patch
    // TODO: profile
    /// The `[registries]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registries)
    #[serde(default)]
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub registries: BTreeMap<String, RegistriesConfigValue>,
    /// The `[registry]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registry)
    #[serde(default)]
    #[serde(skip_serializing_if = "RegistryConfig::is_none")]
    pub registry: RegistryConfig,
    /// The `[source]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#source)
    #[serde(default)]
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub source: BTreeMap<String, SourceConfigValue>,
    /// The `[target]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#target)
    #[serde(default)]
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    pub target: BTreeMap<String, TargetConfig>,
    /// The `[term]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#term)
    #[serde(default)]
    #[serde(skip_serializing_if = "TermConfig::is_none")]
    pub term: TermConfig,
}

impl Config {
    /// Reads config files hierarchically from the current directory and merges them.
    pub fn load() -> Result<Self> {
        Self::load_with_cwd(std::env::current_dir().context("failed to get current directory")?)
    }

    /// Reads config files hierarchically from the given directory and merges them.
    pub fn load_with_cwd<P: AsRef<Path>>(cwd: P) -> Result<Self> {
        let cwd = cwd.as_ref();
        Self::_load_with_options(cwd, walk::cargo_home_with_cwd(cwd).as_deref())
    }

    /// Reads config files hierarchically from the given directory and merges them.
    pub fn load_with_options<P: AsRef<Path>, Q: Into<Option<PathBuf>>>(
        cwd: P,
        cargo_home: Q,
    ) -> Result<Self> {
        Self::_load_with_options(cwd.as_ref(), cargo_home.into().as_deref())
    }
    pub(crate) fn _load_with_options(
        current_dir: &Path,
        cargo_home: Option<&Path>,
    ) -> Result<Config> {
        let mut base = None;
        for path in crate::walk::WalkInner::with_cargo_home(current_dir, cargo_home) {
            let config = Self::_load_file(&path)?;
            match &mut base {
                None => base = Some((path, config)),
                Some((base_path, base)) => base.merge(config, false).with_context(|| {
                    format!(
                        "failed to merge config from `{}` into `{}`",
                        path.display(),
                        base_path.display()
                    )
                })?,
            }
        }
        Ok(base.map(|(_, c)| c).unwrap_or_default())
    }

    /// Reads cargo config file at the given path.
    ///
    /// **Note:** Note: This just reads a file at the given path and does not
    /// respect the hierarchical structure of the cargo config.
    pub fn load_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        Self::_load_file(path.as_ref())
    }
    fn _load_file(path: &Path) -> Result<Self> {
        let buf = fs::read_to_string(path)
            .with_context(|| format!("failed to read `{}`", path.display()))?;
        let mut config: Config = toml::de::from_str(&buf).with_context(|| {
            format!("failed to parse `{}` as cargo configuration", path.display())
        })?;
        config.set_path(path);
        Ok(config)
    }

    /// Merges the given config into this config.
    ///
    /// If `force` is `false`, this matches the way cargo [merges configs in the
    /// parent directories](https://doc.rust-lang.org/nightly/cargo/reference/config.html#hierarchical-structure).
    ///
    /// If `force` is `true`, this matches the way cargo's `--config` CLI option
    /// overrides config.
    pub(crate) fn merge(&mut self, low: Self, force: bool) -> Result<()> {
        crate::merge::Merge::merge(self, low, force)
    }

    pub(crate) fn set_path(&mut self, path: &Path) {
        crate::value::SetPath::set_path(self, path);
    }

    #[allow(clippy::ref_option)]
    pub(crate) fn resolve_target(
        cx: &ResolveContext,
        target_configs: &BTreeMap<String, TargetConfig>,
        override_target_rustflags: bool,
        build_rustflags: &Option<Flags>,
        override_target_rustdocflags: bool,
        build_rustdocflags: &Option<Flags>,
        target_triple: &TargetTripleRef<'_>,
        build_config: &easy::BuildConfig,
    ) -> Result<Option<TargetConfig>> {
        let target = target_triple.triple();
        if target.starts_with("cfg(") {
            bail!("'{target}' is not valid target triple");
        }
        let mut target_config = None;

        if let Some(config) = target_configs.get(target) {
            target_config = Some(TargetConfig {
                linker: config.linker.clone(),
                runner: config.runner.clone(),
                rustflags: config.rustflags.clone(),
                rustdocflags: config.rustdocflags.clone(),
                rest: BTreeMap::new(), // skip cloning rest
            });
        } else if let Some((before, rest)) = target.split_once('.') {
            if let Some(config) = target_configs.get(before) {
                let mut rest_target_configs = &config.rest;
                let mut rest_target = rest;
                loop {
                    if let Some(config) = rest_target_configs.get(rest_target) {
                        if let TargetConfigRestValue::Config(config) = config {
                            target_config = Some(TargetConfig {
                                linker: config.linker.clone(),
                                runner: config.runner.clone(),
                                rustflags: config.rustflags.clone(),
                                rustdocflags: config.rustdocflags.clone(),
                                rest: BTreeMap::new(), // skip cloning rest
                            });
                        }
                        break;
                    }
                    if let Some((before, rest)) = rest_target.split_once('.') {
                        if let Some(TargetConfigRestValue::Config(config)) =
                            rest_target_configs.get(before)
                        {
                            rest_target_configs = &config.rest;
                            rest_target = rest;
                            continue;
                        }
                    }
                    break;
                }
            }
        }

        let target_u_upper = target_u_upper(target);
        let mut target_linker = target_config.as_mut().and_then(|c| c.linker.take());
        let mut target_runner = target_config.as_mut().and_then(|c| c.runner.take());
        let mut target_rustflags: Option<Flags> =
            target_config.as_mut().and_then(|c| c.rustflags.take());
        let mut target_rustdocflags: Option<Flags> =
            target_config.as_mut().and_then(|c| c.rustdocflags.take());
        if let Some(linker) = cx.env_dyn(&format!("CARGO_TARGET_{target_u_upper}_LINKER"))? {
            target_linker = Some(linker);
        }
        if let Some(runner) = cx.env_dyn(&format!("CARGO_TARGET_{target_u_upper}_RUNNER"))? {
            target_runner = Some(
                PathAndArgs::from_string(&runner.val, runner.definition.as_ref())
                    .context("invalid length 0, expected at least one element")?,
            );
        }
        if let Some(rustflags) = cx.env_dyn(&format!("CARGO_TARGET_{target_u_upper}_RUSTFLAGS"))? {
            let mut rustflags =
                Flags::from_space_separated(&rustflags.val, rustflags.definition.as_ref());
            match &mut target_rustflags {
                Some(target_rustflags) => {
                    target_rustflags.flags.append(&mut rustflags.flags);
                }
                target_rustflags @ None => *target_rustflags = Some(rustflags),
            }
        }
        if let Some(rustdocflags) =
            cx.env_dyn(&format!("CARGO_TARGET_{target_u_upper}_RUSTDOCFLAGS"))?
        {
            let mut rustdocflags =
                Flags::from_space_separated(&rustdocflags.val, rustdocflags.definition.as_ref());
            match &mut target_rustdocflags {
                Some(target_rustdocflags) => {
                    target_rustdocflags.flags.append(&mut rustdocflags.flags);
                }
                target_rustdocflags @ None => *target_rustdocflags = Some(rustdocflags),
            }
        }
        for (k, v) in target_configs {
            if !k.starts_with("cfg(") {
                continue;
            }
            if cx.eval_cfg(k, target_triple, build_config)? {
                // https://github.com/rust-lang/cargo/pull/12535
                if target_linker.is_none() {
                    if let Some(linker) = v.linker.as_ref() {
                        target_linker = Some(linker.clone());
                    }
                }
                // Priorities (as of 1.68.0-nightly (2022-12-23)):
                // 1. CARGO_TARGET_<triple>_RUNNER
                // 2. target.<triple>.runner
                // 3. target.<cfg>.runner
                if target_runner.is_none() {
                    if let Some(runner) = v.runner.as_ref() {
                        target_runner = Some(runner.clone());
                    }
                }
                // Applied order (as of 1.68.0-nightly (2022-12-23)):
                // 1. target.<triple>.rustflags
                // 2. CARGO_TARGET_<triple>_RUSTFLAGS
                // 3. target.<cfg>.rustflags
                if let Some(rustflags) = v.rustflags.as_ref() {
                    match &mut target_rustflags {
                        Some(target_rustflags) => {
                            target_rustflags.flags.extend_from_slice(&rustflags.flags);
                        }
                        target_rustflags @ None => *target_rustflags = Some(rustflags.clone()),
                    }
                }
            }
        }
        if let Some(linker) = target_linker {
            target_config.get_or_insert_with(TargetConfig::default).linker = Some(linker);
        }
        if let Some(runner) = target_runner {
            target_config.get_or_insert_with(TargetConfig::default).runner = Some(runner);
        }
        if override_target_rustflags {
            target_config
                .get_or_insert_with(TargetConfig::default)
                .rustflags
                .clone_from(build_rustflags);
        } else if let Some(rustflags) = target_rustflags {
            target_config.get_or_insert_with(TargetConfig::default).rustflags = Some(rustflags);
        } else {
            target_config
                .get_or_insert_with(TargetConfig::default)
                .rustflags
                .clone_from(build_rustflags);
        }
        if override_target_rustdocflags {
            target_config
                .get_or_insert_with(TargetConfig::default)
                .rustdocflags
                .clone_from(build_rustdocflags);
        } else if let Some(rustdocflags) = target_rustdocflags {
            target_config.get_or_insert_with(TargetConfig::default).rustdocflags =
                Some(rustdocflags);
        } else {
            target_config
                .get_or_insert_with(TargetConfig::default)
                .rustdocflags
                .clone_from(build_rustdocflags);
        }
        Ok(target_config)
    }
}

/// The `[build]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#build)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct BuildConfig {
    /// Sets the maximum number of compiler processes to run in parallel.
    /// If negative, it sets the maximum number of compiler processes to the
    /// number of logical CPUs plus provided value. Should not be 0.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildjobs)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub jobs: Option<Value<i32>>,
    /// Sets the executable to use for `rustc`.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustc)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc: Option<Value<String>>,
    /// Sets a wrapper to execute instead of `rustc`.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustc-wrapper)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc_wrapper: Option<Value<String>>,
    /// Sets a wrapper to execute instead of `rustc`, for workspace members only.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustc-workspace-wrapper)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc_workspace_wrapper: Option<Value<String>>,
    /// Sets the executable to use for `rustdoc`.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustdoc)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustdoc: Option<Value<String>>,
    /// The default target platform triples to compile to.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildtarget)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target: Option<StringOrArray>,
    /// The path to where all compiler output is placed. The default if not
    /// specified is a directory named target located at the root of the workspace.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildtarget)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_dir: Option<Value<String>>,
    /// The path to where all compiler intermediate artifacts are placed. The default if not
    /// specified is the value of build.target-dir
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#build-dir)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub build_dir: Option<Value<String>>,
    /// Extra command-line flags to pass to rustc. The value may be an array
    /// of strings or a space-separated string.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustflags)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustflags: Option<Flags>,
    /// Extra command-line flags to pass to `rustdoc`. The value may be an array
    /// of strings or a space-separated string.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustdocflags)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustdocflags: Option<Flags>,
    /// Whether or not to perform incremental compilation.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildincremental)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub incremental: Option<Value<bool>>,
    /// Strips the given path prefix from dep info file paths.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#builddep-info-basedir)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dep_info_basedir: Option<Value<String>>,

    // Resolve contexts. Completely ignored in serialization and deserialization.
    #[serde(skip)]
    pub(crate) override_target_rustflags: bool,
    #[serde(skip)]
    pub(crate) override_target_rustdocflags: bool,
}

// https://github.com/rust-lang/cargo/blob/0.80.0/src/cargo/util/context/target.rs
/// A `[target.<triple>]` or `[target.<cfg>]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#target)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct TargetConfig {
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#targettriplelinker)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub linker: Option<Value<String>>,
    /// [reference (`target.<triple>.runner`)](https://doc.rust-lang.org/nightly/cargo/reference/config.html#targettriplerunner)
    ///
    /// [reference (`target.<cfg>.runner`)](https://doc.rust-lang.org/nightly/cargo/reference/config.html#targetcfgrunner)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub runner: Option<PathAndArgs>,
    /// [reference (`target.<triple>.rustflags`)](https://doc.rust-lang.org/nightly/cargo/reference/config.html#targettriplerustflags)
    ///
    /// [reference (`target.<cfg>.rustflags`)](https://doc.rust-lang.org/nightly/cargo/reference/config.html#targetcfgrustflags)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustflags: Option<Flags>,
    /// [reference (`target.<triple>.rustdocflags`)](https://doc.rust-lang.org/nightly/cargo/reference/config.html#targettriplerustdocflags)
    ///
    /// [reference (`target.<cfg>.rustdocflags`)](https://doc.rust-lang.org/nightly/cargo/reference/config.html#targetcfgrustdocflags)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustdocflags: Option<Flags>,
    // TODO: links: https://doc.rust-lang.org/nightly/cargo/reference/config.html#targettriplelinks
    #[serde(flatten)]
    pub(crate) rest: BTreeMap<String, TargetConfigRestValue>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub(crate) enum TargetConfigRestValue {
    Config(TargetConfig),
    Other(toml::Value),
}

impl Merge for TargetConfigRestValue {
    fn merge(&mut self, low: Self, force: bool) -> Result<()> {
        match (self, low) {
            (Self::Config(this), Self::Config(low)) => this.merge(low, force),
            (this @ Self::Other(_), low @ Self::Config(_)) => {
                *this = low;
                Ok(())
            }
            (_, Self::Other(_)) => Ok(()),
        }
    }
}
impl SetPath for TargetConfigRestValue {
    fn set_path(&mut self, path: &Path) {
        match self {
            Self::Config(v) => {
                v.set_path(path);
            }
            Self::Other(_) => {}
        }
    }
}

/// The `[doc]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#doc)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct DocConfig {
    /// This option sets the browser to be used by `cargo doc`, overriding the
    /// `BROWSER` environment variable when opening documentation with the `--open` option.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#docbrowser)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub browser: Option<PathAndArgs>,
}

// TODO: hide internal repr, change to struct
/// A value of the `[env]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#env)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
#[non_exhaustive]
pub enum EnvConfigValue {
    Value(Value<String>),
    Table {
        value: Value<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        force: Option<Value<bool>>,
        #[serde(skip_serializing_if = "Option::is_none")]
        relative: Option<Value<bool>>,
    },
}

impl EnvConfigValue {
    pub(crate) const fn kind(&self) -> &'static str {
        match self {
            Self::Value(..) => "string",
            Self::Table { .. } => "table",
        }
    }

    pub(crate) fn resolve(&self, current_dir: &Path) -> Cow<'_, OsStr> {
        match self {
            Self::Value(v) => OsStr::new(&v.val).into(),
            Self::Table { value, relative, .. } => {
                if relative.as_ref().is_some_and(|v| v.val) {
                    if let Some(def) = &value.definition {
                        return def.root(current_dir).join(&value.val).into_os_string().into();
                    }
                }
                OsStr::new(&value.val).into()
            }
        }
    }
}

/// The `[future-incompat-report]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#future-incompat-report)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct FutureIncompatReportConfig {
    /// Controls how often we display a notification to the terminal when a future incompat report is available.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#future-incompat-reportfrequency)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub frequency: Option<Value<Frequency>>,
}

/// The `[cargo-new]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#cargo-new)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct CargoNewConfig {
    /// Specifies the source control system to use for initializing a new repository.
    /// Valid values are git, hg (for Mercurial), pijul, fossil or none to disable this behavior.
    /// Defaults to git, or none if already inside a VCS repository. Can be overridden with the --vcs CLI option.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vcs: Option<Value<VersionControlSoftware>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum VersionControlSoftware {
    /// Git
    Git,
    /// Mercurial
    #[serde(rename = "hg")]
    Mercurial,
    /// Pijul
    Pijul,
    /// Fossil
    Fossil,
    /// No VCS
    None,
}

impl VersionControlSoftware {
    pub const fn as_str(self) -> &'static str {
        match self {
            VersionControlSoftware::Git => "git",
            VersionControlSoftware::Mercurial => "hg",
            VersionControlSoftware::Pijul => "pijul",
            VersionControlSoftware::Fossil => "fossil",
            VersionControlSoftware::None => "none",
        }
    }
}

impl FromStr for VersionControlSoftware {
    type Err = Error;

    fn from_str(vcs: &str) -> Result<Self, Self::Err> {
        match vcs {
            "git" => Ok(Self::Git),
            "hg" => Ok(Self::Mercurial),
            "pijul" => Ok(Self::Pijul),
            "fossil" => Ok(Self::Fossil),
            "none" => Ok(Self::None),
            other => bail!("must be git, hg, pijul, fossil, none, but found `{other}`"),
        }
    }
}

/// The `[http]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#http)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct HttpConfig {
    /// If true, enables debugging of HTTP requests.
    /// The debug information can be seen by setting the `CARGO_LOG=network=debug` environment variable
    /// (or use `network=trace` for even more information).
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpdebug)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub debug: Option<Value<bool>>,
    /// Sets an HTTP and HTTPS proxy to use. The format is in libcurl format as in `[protocol://]host[:port]`.
    /// If not set, Cargo will also check the http.proxy setting in your global git configuration.
    /// If none of those are set, the HTTPS_PROXY or https_proxy environment variables set the proxy for HTTPS requests,
    /// and http_proxy sets it for HTTP requests.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpproxy)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proxy: Option<Value<String>>,
    /// Sets the timeout for each HTTP request, in seconds.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httptimeout)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timeout: Option<Value<u32>>,
    /// Path to a Certificate Authority (CA) bundle file, used to verify TLS certificates.
    /// If not specified, Cargo attempts to use the system certificates.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpcainfo)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cainfo: Option<Value<String>>,
    /// This determines whether or not TLS certificate revocation checks should be performed.
    /// This only works on Windows.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpcheck-revoke)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub check_revoke: Option<Value<bool>>,
    // TODO: handle ssl-version
    /// This setting controls timeout behavior for slow connections.
    /// If the average transfer speed in bytes per second is below the given value
    /// for `http.timeout` seconds (default 30 seconds), then the connection is considered too slow and Cargo will abort and retry.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httplow-speed-limit)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub low_speed_limit: Option<Value<u32>>,
    /// When true, Cargo will attempt to use the HTTP2 protocol with multiplexing.
    /// This allows multiple requests to use the same connection, usually improving performance when fetching multiple files.
    /// If false, Cargo will use HTTP 1.1 without pipelining.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpmultiplexing)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub multiplexing: Option<Value<bool>>,
    /// Specifies a custom user-agent header to use.
    /// The default if not specified is a string that includes Cargo’s version.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpuser-agent)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub user_agent: Option<Value<String>>,
}

/// The `[net]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#net)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct NetConfig {
    /// Number of times to retry possibly spurious network errors.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#netretry)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub retry: Option<Value<u32>>,
    /// If this is `true`, then Cargo will use the `git` executable to fetch
    /// registry indexes and git dependencies. If `false`, then it uses a
    /// built-in `git` library.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#netgit-fetch-with-cli)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub git_fetch_with_cli: Option<Value<bool>>,
    /// If this is `true`, then Cargo will avoid accessing the network, and
    /// attempt to proceed with locally cached data. If `false`, Cargo will
    /// access the network as needed, and generate an error if it encounters a
    /// network error.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#netoffline)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub offline: Option<Value<bool>>,
}

/// A value of the `[registries]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registries)
#[derive(Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct RegistriesConfigValue {
    /// Specifies the URL of the git index for the registry.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registriesnameindex)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub index: Option<Value<String>>,
    /// Specifies the authentication token for the given registry.
    ///
    /// Note: This library does not read any values in the
    /// [credentials](https://doc.rust-lang.org/nightly/cargo/reference/config.html#credentials)
    /// file.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registriesnametoken)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub token: Option<Value<String>>,
    /// Specifies the credential provider for the given registry.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registriesnamecredential-provider)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub credential_provider: Option<CredentialProvider>,
    /// Specifies the protocol used to access crates.io.
    /// Not allowed for any registries besides crates.io.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registriescrates-ioprotocol)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub protocol: Option<Value<RegistriesProtocol>>,
}

impl fmt::Debug for RegistriesConfigValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { index, credential_provider, token, protocol } = self;
        let redacted_token = token
            .as_ref()
            .map(|token| Value { val: "[REDACTED]", definition: token.definition.clone() });
        f.debug_struct("RegistriesConfigValue")
            .field("index", &index)
            .field("token", &redacted_token)
            .field("credential_provider", credential_provider)
            .field("protocol", &protocol)
            .finish()
    }
}

/// Specifies the protocol used to access crates.io.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registriescrates-ioprotocol)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub enum RegistriesProtocol {
    /// Causes Cargo to clone the entire index of all packages ever published to
    /// [crates.io](https://crates.io/) from <https://github.com/rust-lang/crates.io-index/>.
    Git,
    /// A newer protocol which uses HTTPS to download only what is necessary from
    /// <https://index.crates.io/>.
    Sparse,
}

impl FromStr for RegistriesProtocol {
    type Err = Error;

    fn from_str(protocol: &str) -> Result<Self, Self::Err> {
        match protocol {
            "git" => Ok(Self::Git),
            "sparse" => Ok(Self::Sparse),
            other => bail!("must be git or sparse, but found `{other}`"),
        }
    }
}

/// The `[registry]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registry)
#[derive(Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct RegistryConfig {
    /// The name of the registry (from the
    /// [`registries` table](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registries))
    /// to use by default for registry commands like
    /// [`cargo publish`](https://doc.rust-lang.org/nightly/cargo/commands/cargo-publish.html).
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registrydefault)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub default: Option<Value<String>>,
    /// Specifies the credential provider for crates.io. If not set, the providers in
    /// [`registry.global-credential-providers`]((https://doc.rust-lang.org/nightly/cargo/reference/config.html#registryglobal-credential-providers))
    /// will be used.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registrycredential-provider)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub credential_provider: Option<CredentialProvider>,
    /// Specifies the authentication token for [crates.io](https://crates.io/).
    ///
    /// Note: This library does not read any values in the
    /// [credentials](https://doc.rust-lang.org/nightly/cargo/reference/config.html#credentials)
    /// file.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registrytoken)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub token: Option<Value<String>>,
    /// Specifies the list of global credential providers.
    /// If credential provider is not set for a specific registry using
    /// [`registries.<name>.credential-provider`](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registriesnamecredential-provider),
    /// Cargo will use the credential providers in this list.
    /// Providers toward the end of the list have precedence.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registryglobal-credential-providers)
    #[serde(default)]
    #[serde(skip_serializing_if = "GlobalCredentialProviders::is_none")]
    pub global_credential_providers: GlobalCredentialProviders,
}

impl fmt::Debug for RegistryConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { default, credential_provider, token, global_credential_providers } = self;
        let redacted_token = token
            .as_ref()
            .map(|token| Value { val: "[REDACTED]", definition: token.definition.clone() });
        f.debug_struct("RegistryConfig")
            .field("default", &default)
            .field("credential_provider", credential_provider)
            .field("token", &redacted_token)
            .field("global_credential_providers", global_credential_providers)
            .finish()
    }
}

/// A value of the `[source]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#source)
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct SourceConfigValue {
    /// If set, replace this source with the given named source or named registry.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamereplace-with)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub replace_with: Option<Value<String>>,
    /// Sets the path to a directory to use as a directory source.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamedirectory)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub directory: Option<Value<String>>,
    /// Sets the URL to use for a registry source.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenameregistry)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub registry: Option<Value<String>>,
    /// Sets the path to a directory to use as a local registry source.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamelocal-registry)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub local_registry: Option<Value<String>>,
    /// Sets the URL to use for a git source.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamegit)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub git: Option<Value<String>>,
    /// Sets the branch name to use for a git repository.
    /// If none of branch, tag, or rev is set, defaults to the master branch.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamebranch)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch: Option<Value<String>>,
    /// Sets the tag name to use for a git repository.
    /// If none of branch, tag, or rev is set, defaults to the master branch.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenametag)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tag: Option<Value<String>>,
    /// Sets the revision to use for a git repository.
    /// If none of branch, tag, or rev is set, defaults to the master branch.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamerev)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rev: Option<Value<String>>,
}

/// Global credential providers.
///
/// [Cargo Reference](https://doc.rust-lang.org/cargo/reference/config.html#registryglobal-credential-providers)
#[derive(Clone, Debug, Default)]
pub struct GlobalCredentialProviders(pub(crate) Vec<CredentialProvider>);

impl GlobalCredentialProviders {
    pub(crate) fn is_none(&self) -> bool {
        self.0.is_empty()
    }
}

impl GlobalCredentialProviders {
    pub(crate) fn from_list<T>(
        list: impl IntoIterator<Item = T>,
        definition: Option<&Definition>,
    ) -> Result<Self, Error>
    where
        T: AsRef<str>,
    {
        Ok(Self(
            list.into_iter()
                .map(|v| CredentialProvider::from_string(v.as_ref(), definition))
                .collect::<Result<_, _>>()?,
        ))
    }
}

impl AsRef<[CredentialProvider]> for GlobalCredentialProviders {
    fn as_ref(&self) -> &[CredentialProvider] {
        &self.0
    }
}

impl Serialize for GlobalCredentialProviders {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for GlobalCredentialProviders {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // TODO: use visitor?
        Ok(Self(
            <Vec<String>>::deserialize(deserializer)?
                .iter()
                .map(|s| CredentialProvider::from_string(s, None))
                .collect::<Result<_, _>>()
                .map_err(de::Error::custom)?,
        ))
    }
}

/// A registry's credential provider.
///
/// [Cargo Reference](https://doc.rust-lang.org/cargo/reference/registry-authentication.html)
#[derive(Clone, Debug)]
pub struct CredentialProvider {
    pub kind: CredentialProviderKind,
    deserialized_repr: StringListDeserializedRepr,
}

/// The kind of a registry's credential provider.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum CredentialProviderKind {
    /// Uses Cargo’s credentials file to store tokens unencrypted in plain text.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/cargo/reference/registry-authentication.html#cargotoken)
    CargoToken,
    /// Uses the Windows Credential Manager to store tokens.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/cargo/reference/registry-authentication.html#cargowincred)
    CargoWincred,
    /// Uses the macOS Keychain to store tokens.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/cargo/reference/registry-authentication.html#cargomacos-keychain)
    CargoMacosKeychain,
    /// Uses libsecret to store tokens.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/cargo/reference/registry-authentication.html#cargolibsecret)
    CargoLibsecret,
    /// Launch a subprocess that returns a token on stdout. Newlines will be trimmed.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/cargo/reference/registry-authentication.html#cargotoken-from-stdout-command-args)
    CargoTokenFromStdout(PathAndArgs),
    /// For credential provider plugins that follow Cargo’s credential provider protocol,
    /// the configuration value should be a string with the path to the executable (or the executable name if on the PATH).
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/cargo/reference/registry-authentication.html#credential-plugins)
    Plugin(PathAndArgs),
    /// Maybe an alias, otherwise a plugin command.
    MaybeAlias(Value<String>),
}

impl CredentialProvider {
    pub(crate) fn from_string(value: &str, definition: Option<&Definition>) -> Result<Self, Error> {
        Ok(Self {
            kind: CredentialProviderKind::from_list(
                split_space_separated(value)
                    .map(|v| Value { val: v.to_owned(), definition: definition.cloned() }),
                StringListDeserializedRepr::String,
            )?,
            deserialized_repr: StringListDeserializedRepr::String,
        })
    }

    pub(crate) fn from_array(list: Vec<Value<String>>) -> Result<Self, Error> {
        Ok(Self {
            kind: CredentialProviderKind::from_list(list, StringListDeserializedRepr::Array)?,
            deserialized_repr: StringListDeserializedRepr::Array,
        })
    }
}

impl SetPath for CredentialProviderKind {
    fn set_path(&mut self, path: &Path) {
        match self {
            Self::CargoToken
            | Self::CargoWincred
            | Self::CargoMacosKeychain
            | Self::CargoLibsecret => {}
            Self::CargoTokenFromStdout(command) | Self::Plugin(command) => command.set_path(path),
            Self::MaybeAlias(s) => s.set_path(path),
        }
    }
}

impl Serialize for CredentialProvider {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self.deserialized_repr {
            StringListDeserializedRepr::String => {
                let mut s = String::new();

                let command = match &self.kind {
                    CredentialProviderKind::CargoToken => {
                        return "cargo:token".serialize(serializer);
                    }
                    CredentialProviderKind::CargoWincred => {
                        return "cargo:wincred".serialize(serializer);
                    }
                    CredentialProviderKind::CargoMacosKeychain => {
                        return "cargo:macos-keychain".serialize(serializer);
                    }
                    CredentialProviderKind::CargoLibsecret => {
                        return "cargo:libsecret".serialize(serializer);
                    }
                    CredentialProviderKind::CargoTokenFromStdout(command) => {
                        s.push_str("cargo:token-from-stdout ");

                        command
                    }
                    CredentialProviderKind::Plugin(command) => command,
                    CredentialProviderKind::MaybeAlias(value) => {
                        return value.serialize(serializer);
                    }
                };

                command.serialize_to_string(&mut s);

                s.serialize(serializer)
            }
            StringListDeserializedRepr::Array => {
                let mut array = vec![];

                let command = match &self.kind {
                    CredentialProviderKind::CargoToken => {
                        return ["cargo:token"].serialize(serializer);
                    }
                    CredentialProviderKind::CargoWincred => {
                        return ["cargo:wincred"].serialize(serializer);
                    }
                    CredentialProviderKind::CargoMacosKeychain => {
                        return ["cargo:macos-keychain"].serialize(serializer);
                    }
                    CredentialProviderKind::CargoLibsecret => {
                        return ["cargo:libsecret"].serialize(serializer);
                    }
                    CredentialProviderKind::CargoTokenFromStdout(command) => {
                        array.push("cargo:token-from-stdout");

                        command
                    }
                    CredentialProviderKind::Plugin(command) => command,
                    CredentialProviderKind::MaybeAlias(value) => {
                        return [value].serialize(serializer);
                    }
                };

                command.serialize_to_array(&mut array);

                array.serialize(serializer)
            }
        }
    }
}

impl<'de> Deserialize<'de> for CredentialProvider {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // TODO: use visitor?
        match StringOrArray::deserialize(deserializer)? {
            StringOrArray::String(s) => Self::from_string(&s.val, s.definition.as_ref()),
            StringOrArray::Array(v) => Self::from_array(v),
        }
        .map_err(de::Error::custom)
    }
}

impl CredentialProviderKind {
    fn from_list<T>(list: T, deserialized_repr: StringListDeserializedRepr) -> Result<Self, Error>
    where
        T: IntoIterator<Item = Value<String>>,
    {
        let mut iter = list.into_iter().peekable();
        let first = iter
            .next()
            .ok_or_else(|| format_err!("invalid length 0, expected at least one element"))?;

        let empty_args = |kind: Self, mut iter: iter::Peekable<T::IntoIter>| {
            if iter.next().is_some() {
                bail!(
                    "args should be empty for credential provider of kind {:?}",
                    kind.builtin_kind().unwrap(),
                );
            }

            Ok(kind)
        };

        match &*first.val {
            "cargo:token" => empty_args(Self::CargoToken, iter),
            "cargo:wincred" => empty_args(Self::CargoWincred, iter),
            "cargo:macos-keychain" => empty_args(Self::CargoMacosKeychain, iter),
            "cargo:libsecret" => empty_args(Self::CargoLibsecret, iter),
            "cargo:token-from-stdout" => {
                let command = PathAndArgs::from_list(
                    iter,
                    deserialized_repr,
                ).ok_or_else(|| format_err!(r#"invalid length 1, expected at least two elements for registry of kind "cargo:token-from-stdout""#))?;

                Ok(Self::CargoTokenFromStdout(command))
            }
            _ if iter.peek().is_none() => Ok(Self::MaybeAlias(first)),
            _ => Ok(Self::Plugin(
                PathAndArgs::from_list(iter::once(first).chain(iter), deserialized_repr).unwrap(),
            )),
        }
    }

    fn builtin_kind(&self) -> Option<&'static str> {
        Some(match self {
            Self::CargoToken => "cargo:token",
            Self::CargoWincred => "cargo:wincred",
            Self::CargoMacosKeychain => "cargo:macos-keychain",
            Self::CargoLibsecret => "cargo:libsecret",
            Self::CargoTokenFromStdout(_) => "cargo:token-from-stdout",
            Self::Plugin(_) | Self::MaybeAlias(_) => return None,
        })
    }
}

/// The `[term]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#term)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct TermConfig {
    /// Controls whether or not log messages are displayed by Cargo.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#termquiet)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub quiet: Option<Value<bool>>,
    /// Controls whether or not extra detailed messages are displayed by Cargo.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#termverbose)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verbose: Option<Value<bool>>,
    /// Controls whether or not colored output is used in the terminal.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#termcolor)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub color: Option<Value<Color>>,
    #[serde(default)]
    #[serde(skip_serializing_if = "TermProgress::is_none")]
    pub progress: TermProgress,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct TermProgress {
    /// Controls whether or not progress bar is shown in the terminal.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#termprogresswhen)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub when: Option<Value<When>>,
    /// Sets the width for progress bar.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#termprogresswidth)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub width: Option<Value<u32>>,
}

#[allow(clippy::exhaustive_enums)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Color {
    /// (default) Automatically detect if color support is available on the terminal.
    #[default]
    Auto,
    /// Always display colors.
    Always,
    /// Never display colors.
    Never,
}

impl Color {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Always => "always",
            Self::Never => "never",
        }
    }
}

impl FromStr for Color {
    type Err = Error;

    fn from_str(color: &str) -> Result<Self, Self::Err> {
        match color {
            "auto" => Ok(Self::Auto),
            "always" => Ok(Self::Always),
            "never" => Ok(Self::Never),
            other => bail!("must be auto, always, or never, but found `{other}`"),
        }
    }
}

#[allow(clippy::exhaustive_enums)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum When {
    /// (default) Intelligently guess whether to show progress bar.
    #[default]
    Auto,
    /// Always show progress bar.
    Always,
    /// Never show progress bar.
    Never,
}

impl When {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Always => "always",
            Self::Never => "never",
        }
    }
}

impl FromStr for When {
    type Err = Error;

    fn from_str(color: &str) -> Result<Self, Self::Err> {
        match color {
            "auto" => Ok(Self::Auto),
            "always" => Ok(Self::Always),
            "never" => Ok(Self::Never),
            other => bail!("must be auto, always, or never, but found `{other}`"),
        }
    }
}

#[allow(clippy::exhaustive_enums)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Frequency {
    /// (default) Always display a notification when a command (e.g. `cargo build`)
    /// produces a future incompat report.
    #[default]
    Always,
    /// Never display a notification.
    Never,
}

impl Frequency {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Always => "always",
            Self::Never => "never",
        }
    }
}

impl FromStr for Frequency {
    type Err = Error;

    fn from_str(color: &str) -> Result<Self, Self::Err> {
        match color {
            "always" => Ok(Self::Always),
            "never" => Ok(Self::Never),
            other => bail!("must be always or never, but found `{other}`"),
        }
    }
}

/// A representation of rustflags and rustdocflags.
#[derive(Debug, Clone, Serialize)]
#[serde(transparent)]
pub struct Flags {
    pub flags: Vec<Value<String>>,
    // for merge
    #[serde(skip)]
    pub(crate) deserialized_repr: StringListDeserializedRepr,
}

impl Flags {
    /// Creates a rustflags from a string separated with ASCII unit separator ('\x1f').
    ///
    /// This is a valid format for the following environment variables:
    ///
    /// - `CARGO_ENCODED_RUSTFLAGS` (Cargo 1.55+)
    /// - `CARGO_ENCODED_RUSTDOCFLAGS` (Cargo 1.55+)
    ///
    /// See also `encode`.
    pub(crate) fn from_encoded(s: &Value<String>) -> Self {
        Self {
            flags: split_encoded(&s.val)
                .map(|v| Value { val: v.to_owned(), definition: s.definition.clone() })
                .collect(),
            // Encoded rustflags cannot be serialized as a string because they may contain spaces.
            deserialized_repr: StringListDeserializedRepr::Array,
        }
    }

    /// Creates a rustflags from a string separated with space (' ').
    ///
    /// This is a valid format for the following environment variables:
    ///
    /// - `RUSTFLAGS`
    /// - `CARGO_TARGET_<triple>_RUSTFLAGS`
    /// - `CARGO_BUILD_RUSTFLAGS`
    /// - `RUSTDOCFLAGS`
    /// - `CARGO_TARGET_<triple>_RUSTDOCFLAGS`
    /// - `CARGO_BUILD_RUSTDOCFLAGS`
    ///
    /// And the following configs:
    ///
    /// - `target.<triple>.rustflags`
    /// - `target.<cfg>.rustflags`
    /// - `build.rustflags`
    /// - `target.<triple>.rustdocflags` (Cargo 1.78+)
    /// - `build.rustdocflags`
    ///
    /// See also `encode_space_separated`.
    pub(crate) fn from_space_separated(s: &str, def: Option<&Definition>) -> Self {
        Self {
            flags: split_space_separated(s)
                .map(|v| Value { val: v.to_owned(), definition: def.cloned() })
                .collect(),
            deserialized_repr: StringListDeserializedRepr::String,
        }
    }

    pub(crate) fn from_array(flags: Vec<Value<String>>) -> Self {
        Self { flags, deserialized_repr: StringListDeserializedRepr::Array }
    }
}

impl<'de> Deserialize<'de> for Flags {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // TODO: use visitor?
        let v: StringOrArray = Deserialize::deserialize(deserializer)?;
        match v {
            StringOrArray::String(s) => {
                Ok(Self::from_space_separated(&s.val, s.definition.as_ref()))
            }
            StringOrArray::Array(v) => Ok(Self::from_array(v)),
        }
    }
}

// https://github.com/rust-lang/cargo/blob/0.80.0/src/cargo/util/context/path.rs
#[derive(Debug, Deserialize, PartialEq, Clone)]
#[serde(transparent)]
pub struct ConfigRelativePath(pub(crate) Value<String>);

impl ConfigRelativePath {
    /// Returns the underlying value.
    pub fn value(&self) -> &Value<String> {
        &self.0
    }

    /// Returns the raw underlying configuration value for this key.
    pub fn raw_value(&self) -> &str {
        &self.0.val
    }

    // /// Resolves this configuration-relative path to an absolute path.
    // ///
    // /// This will always return an absolute path where it's relative to the
    // /// location for configuration for this value.
    // pub(crate) fn resolve_path(&self, current_dir: &Path) -> Cow<'_, Path> {
    //     self.0.resolve_as_path(current_dir)
    // }

    /// Resolves this configuration-relative path to either an absolute path or
    /// something appropriate to execute from `PATH`.
    ///
    /// Values which don't look like a filesystem path (don't contain `/` or
    /// `\`) will be returned as-is, and everything else will fall through to an
    /// absolute path.
    pub(crate) fn resolve_program(&self, current_dir: &Path) -> Cow<'_, Path> {
        self.0.resolve_as_program_path(current_dir)
    }
}

/// An executable path with arguments.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#executable-paths-with-arguments)
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct PathAndArgs {
    pub path: ConfigRelativePath,
    pub args: Vec<Value<String>>,

    // for merge
    pub(crate) deserialized_repr: StringListDeserializedRepr,
}

impl PathAndArgs {
    pub(crate) fn from_string(value: &str, definition: Option<&Definition>) -> Option<Self> {
        Self::from_list(
            split_space_separated(value)
                .map(|v| Value { val: v.to_owned(), definition: definition.cloned() }),
            StringListDeserializedRepr::String,
        )
    }

    pub(crate) fn from_array(list: Vec<Value<String>>) -> Option<Self> {
        Self::from_list(list, StringListDeserializedRepr::Array)
    }

    fn from_list(
        list: impl IntoIterator<Item = Value<String>>,
        deserialized_repr: StringListDeserializedRepr,
    ) -> Option<Self> {
        let mut iter = list.into_iter();

        Some(Self {
            path: ConfigRelativePath(iter.next()?),
            args: iter.collect(),
            deserialized_repr,
        })
    }

    fn serialize_to_string(&self, s: &mut String) {
        s.push_str(self.path.raw_value());

        for arg in &self.args {
            s.push(' ');
            s.push_str(&arg.val);
        }
    }

    fn array_len(&self) -> usize {
        1 + self.args.len()
    }

    fn serialize_to_array<'a>(&'a self, v: &mut Vec<&'a str>) {
        v.push(self.path.raw_value());

        for arg in &self.args {
            v.push(&arg.val);
        }
    }
}

impl Serialize for PathAndArgs {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self.deserialized_repr {
            StringListDeserializedRepr::String => {
                let mut s = String::new();

                self.serialize_to_string(&mut s);
                s.serialize(serializer)
            }
            StringListDeserializedRepr::Array => {
                let mut v = Vec::with_capacity(self.array_len());

                self.serialize_to_array(&mut v);
                v.serialize(serializer)
            }
        }
    }
}
impl<'de> Deserialize<'de> for PathAndArgs {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // TODO: use visitor?
        match StringOrArray::deserialize(deserializer)? {
            StringOrArray::String(s) => Self::from_string(&s.val, s.definition.as_ref()),
            StringOrArray::Array(v) => Self::from_array(v),
        }
        .ok_or_else(|| de::Error::invalid_length(0, &"at least one element"))
    }
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct StringList {
    pub list: Vec<Value<String>>,

    // for merge
    pub(crate) deserialized_repr: StringListDeserializedRepr,
}

impl Default for StringList {
    fn default() -> Self {
        Self { list: vec![], deserialized_repr: StringListDeserializedRepr::Array }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum StringListDeserializedRepr {
    String,
    Array,
}
impl StringListDeserializedRepr {
    pub(crate) const fn as_str(self) -> &'static str {
        match self {
            Self::String => "string",
            Self::Array => "array",
        }
    }
}

impl StringList {
    pub(crate) fn from_string(value: &str, definition: Option<&Definition>) -> Self {
        Self {
            list: split_space_separated(value)
                .map(|v| Value { val: v.to_owned(), definition: definition.cloned() })
                .collect(),
            deserialized_repr: StringListDeserializedRepr::String,
        }
    }
    pub(crate) fn from_array(list: Vec<Value<String>>) -> Self {
        Self { list, deserialized_repr: StringListDeserializedRepr::Array }
    }
}

impl Serialize for StringList {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self.deserialized_repr {
            StringListDeserializedRepr::String => {
                let mut s = String::with_capacity(
                    self.list.len().saturating_sub(1)
                        + self.list.iter().map(|v| v.val.len()).sum::<usize>(),
                );
                for arg in &self.list {
                    if !s.is_empty() {
                        s.push(' ');
                    }
                    s.push_str(&arg.val);
                }
                s.serialize(serializer)
            }
            StringListDeserializedRepr::Array => self.list.serialize(serializer),
        }
    }
}
impl<'de> Deserialize<'de> for StringList {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // TODO: use visitor?
        let v: StringOrArray = Deserialize::deserialize(deserializer)?;
        match v {
            StringOrArray::String(s) => Ok(Self::from_string(&s.val, s.definition.as_ref())),
            StringOrArray::Array(v) => Ok(Self::from_array(v)),
        }
    }
}

/// A string or array of strings.
#[allow(clippy::exhaustive_enums)]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum StringOrArray {
    String(Value<String>),
    Array(Vec<Value<String>>),
}

impl StringOrArray {
    pub(crate) const fn kind(&self) -> &'static str {
        match self {
            Self::String(..) => "string",
            Self::Array(..) => "array",
        }
    }

    // pub(crate) fn string(&self) -> Option<&Value<String>> {
    //     match self {
    //         Self::String(s) => Some(s),
    //         Self::Array(_) => None,
    //     }
    // }
    // pub(crate) fn array(&self) -> Option<&[Value<String>]> {
    //     match self {
    //         Self::String(_) => None,
    //         Self::Array(v) => Some(v),
    //     }
    // }
    pub(crate) fn as_array_no_split(&self) -> &[Value<String>] {
        match self {
            Self::String(s) => slice::from_ref(s),
            Self::Array(v) => v,
        }
    }
}

fn target_u_lower(target: &str) -> String {
    target.replace(['-', '.'], "_")
}
pub(crate) fn target_u_upper(target: &str) -> String {
    let mut target = target_u_lower(target);
    target.make_ascii_uppercase();
    target
}

pub(crate) fn split_encoded(s: &str) -> impl Iterator<Item = &str> {
    s.split('\x1f')
}
pub(crate) fn split_space_separated(s: &str) -> impl Iterator<Item = &str> {
    // TODO: tab/line?
    // https://github.com/rust-lang/cargo/blob/0.80.0/src/cargo/util/context/path.rs#L89
    s.split(' ').map(str::trim).filter(|s| !s.is_empty())
}
