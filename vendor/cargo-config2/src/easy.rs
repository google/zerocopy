// SPDX-License-Identifier: Apache-2.0 OR MIT

use core::{cell::RefCell, fmt, ops};
use std::{
    borrow::Cow,
    collections::BTreeMap,
    ffi::{OsStr, OsString},
    path::{Path, PathBuf},
    process::Command,
};

use serde::ser::{Serialize, Serializer};
use serde_derive::Serialize;

use crate::{
    de::{
        self, Color, Frequency, RegistriesProtocol, VersionControlSoftware, When, split_encoded,
        split_space_separated,
    },
    error::{Context as _, Result},
    process::ProcessBuilder,
    resolve::{
        CargoVersion, ResolveContext, ResolveOptions, RustcVersion, TargetTriple,
        TargetTripleBorrow, TargetTripleRef,
    },
    value::Value,
};

/// Cargo configuration.
#[derive(Debug, Clone, Serialize)]
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
    /// The resolved `[target]` table.
    #[serde(skip_deserializing)]
    #[serde(skip_serializing_if = "ref_cell_bree_map_is_empty")]
    target: RefCell<BTreeMap<TargetTripleBorrow<'static>, TargetConfig>>,
    /// The unresolved `[target]` table.
    #[serde(default)]
    #[serde(skip_serializing)]
    #[serde(rename = "target")]
    de_target: BTreeMap<String, de::TargetConfig>,

    /// The `[term]` table.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#term)
    #[serde(default)]
    #[serde(skip_serializing_if = "TermConfig::is_none")]
    pub term: TermConfig,

    // Resolve contexts. Completely ignored in serialization and deserialization.
    #[serde(skip)]
    cx: ResolveContext,
}

fn ref_cell_bree_map_is_empty<K, V>(map: &RefCell<BTreeMap<K, V>>) -> bool {
    map.borrow().is_empty()
}

impl Config {
    /// Reads config files hierarchically from the current directory and merges them.
    pub fn load() -> Result<Self> {
        Self::load_with_cwd(std::env::current_dir().context("failed to get current directory")?)
    }

    /// Reads config files hierarchically from the given directory and merges them.
    pub fn load_with_cwd<P: AsRef<Path>>(cwd: P) -> Result<Self> {
        let cwd = cwd.as_ref();
        Self::load_with_options(cwd, ResolveOptions::default())
    }

    /// Reads config files hierarchically from the given directory and merges them.
    pub fn load_with_options<P: AsRef<Path>>(cwd: P, options: ResolveOptions) -> Result<Self> {
        let cwd = cwd.as_ref();
        let cx = options.into_context(cwd.to_owned());

        let de = de::Config::_load_with_options(&cx.current_dir, cx.cargo_home(cwd))?;
        Self::from_unresolved(de, cx)
    }

    fn from_unresolved(mut de: de::Config, cx: ResolveContext) -> Result<Self> {
        de.apply_env(&cx)?;

        let mut alias = BTreeMap::new();
        for (k, v) in de.alias {
            alias.insert(k, StringList::from_unresolved(v));
        }
        let build = BuildConfig::from_unresolved(de.build, &cx.current_dir);
        let mut credential_alias = BTreeMap::new();
        for (k, v) in de.credential_alias {
            credential_alias.insert(k, PathAndArgs::from_unresolved(v, &cx.current_dir));
        }
        let doc = DocConfig::from_unresolved(de.doc, &cx.current_dir);
        let mut env = BTreeMap::new();
        for (k, v) in de.env {
            env.insert(k, EnvConfigValue::from_unresolved(v, &cx.current_dir));
        }
        let future_incompat_report =
            FutureIncompatReportConfig::from_unresolved(de.future_incompat_report);
        let cargo_new = CargoNewConfig::from_unresolved(de.cargo_new);
        let http = HttpConfig::from_unresolved(de.http);
        let net = NetConfig::from_unresolved(de.net);
        let mut registries = BTreeMap::new();
        for (k, v) in de.registries {
            registries.insert(
                k,
                RegistriesConfigValue::from_unresolved(v, &credential_alias, &cx.current_dir),
            );
        }
        let mut source = BTreeMap::new();
        for (k, v) in de.source {
            source.insert(k, SourceConfigValue::from_unresolved(v, &cx.current_dir));
        }
        let registry =
            RegistryConfig::from_unresolved(de.registry, &credential_alias, &cx.current_dir);
        let term = TermConfig::from_unresolved(de.term);

        Ok(Self {
            alias,
            build,
            credential_alias,
            doc,
            env,
            future_incompat_report,
            cargo_new,
            http,
            net,
            registries,
            source,
            registry,
            target: RefCell::new(BTreeMap::new()),
            de_target: de.target,
            term,
            cx,
        })
    }

    /// Selects target triples to build.
    ///
    /// The targets returned are based on the order of priority in which cargo
    /// selects the target to be used for the build.
    ///
    /// 1. `--target` option (`targets`)
    /// 2. `CARGO_BUILD_TARGET` environment variable
    /// 3. `build.target` config
    /// 4. [host triple](Self::host_triple)
    ///
    /// **Note:** The result of this function is intended to handle target-specific
    /// configurations and is not always appropriate to propagate directly to Cargo.
    /// See [`build_target_for_cli`](Self::build_target_for_cli) for more.
    ///
    /// ## Multi-target support
    ///
    /// [Cargo 1.64+ supports multi-target builds](https://blog.rust-lang.org/2022/09/22/Rust-1.64.0.html#cargo-improvements-workspace-inheritance-and-multi-target-builds).
    ///
    /// Therefore, this function may return multiple targets if multiple targets
    /// are specified in `targets` or `build.target` config.
    ///
    /// ## Custom target support
    ///
    /// rustc allows you to build a custom target by specifying a target-spec file.
    /// If a target-spec file is specified as the target, rustc considers the
    /// [file stem](Path::file_stem) of that file to be the target triple name.
    ///
    /// Since target-specific configs are referred by target triple name, this
    /// function also converts the target specified in the path to a target triple name.
    ///
    /// ## Examples
    ///
    /// With single-target:
    ///
    /// ```no_run
    /// use anyhow::bail;
    /// use clap::Parser;
    ///
    /// #[derive(Parser)]
    /// struct Args {
    ///     #[clap(long)]
    ///     target: Option<String>,
    /// }
    ///
    /// let args = Args::parse();
    /// let config = cargo_config2::Config::load()?;
    ///
    /// let mut targets = config.build_target_for_config(args.target.as_ref())?;
    /// if targets.len() != 1 {
    ///     bail!("multi-target build is not supported: {targets:?}");
    /// }
    /// let target = targets.pop().unwrap();
    ///
    /// println!("{:?}", config.rustflags(target));
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    ///
    /// With multi-target:
    ///
    /// ```no_run
    /// use clap::Parser;
    ///
    /// #[derive(Parser)]
    /// struct Args {
    ///     #[clap(long)]
    ///     target: Vec<String>,
    /// }
    ///
    /// let args = Args::parse();
    /// let config = cargo_config2::Config::load()?;
    ///
    /// let targets = config.build_target_for_config(&args.target)?;
    ///
    /// for target in targets {
    ///     println!("{:?}", config.rustflags(target)?);
    /// }
    /// # Ok::<(), anyhow::Error>(())
    /// ```
    pub fn build_target_for_config<'a, I: IntoIterator<Item = T>, T: Into<TargetTripleRef<'a>>>(
        &self,
        targets: I,
    ) -> Result<Vec<TargetTriple>> {
        let targets: Vec<_> = targets.into_iter().map(|v| v.into().into_owned()).collect();
        if !targets.is_empty() {
            return Ok(targets);
        }
        let config_targets = self.build.target.clone().unwrap_or_default();
        if !config_targets.is_empty() {
            return Ok(config_targets);
        }
        Ok(vec![TargetTripleRef::from(self.cx.host_triple(&self.build)?).into_owned()])
    }

    /// Selects target triples to pass to CLI.
    ///
    /// The targets returned are based on the order of priority in which cargo
    /// selects the target to be used for the build.
    ///
    /// 1. `--target` option (`targets`)
    /// 2. `CARGO_BUILD_TARGET` environment variable
    /// 3. `build.target` config
    ///
    /// Unlike [`build_target_for_config`](Self::build_target_for_config),
    /// host triple is not referenced. This is because the behavior of Cargo
    /// changes depending on whether or not `--target` option (or one of the
    /// above) is set.
    /// Also, Unlike [`build_target_for_config`](Self::build_target_for_config)
    /// the target name specified in path is preserved.
    #[allow(clippy::unnecessary_wraps)] // TODO: change in next breaking release?
    pub fn build_target_for_cli<I: IntoIterator<Item = S>, S: AsRef<str>>(
        &self,
        targets: I,
    ) -> Result<Vec<String>> {
        let targets: Vec<_> = targets.into_iter().map(|t| t.as_ref().to_owned()).collect();
        if !targets.is_empty() {
            return Ok(targets);
        }
        let config_targets = self.build.target.as_deref().unwrap_or_default();
        if !config_targets.is_empty() {
            return Ok(config_targets.iter().map(|t| t.cli_target_string().into_owned()).collect());
        }
        Ok(vec![])
    }

    fn init_target_config(&self, target: &TargetTripleRef<'_>) -> Result<()> {
        let mut target_configs = self.target.borrow_mut();
        if !target_configs.contains_key(target.cli_target()) {
            let target_config = TargetConfig::from_unresolved(
                de::Config::resolve_target(
                    &self.cx,
                    &self.de_target,
                    self.build.override_target_rustflags,
                    &self.build.de_rustflags,
                    self.build.override_target_rustdocflags,
                    &self.build.de_rustdocflags,
                    target,
                    &self.build,
                )?
                .unwrap_or_default(),
                &self.cx.current_dir,
            );
            target_configs.insert(TargetTripleBorrow(target.clone().into_owned()), target_config);
        }
        Ok(())
    }
    /// Returns the resolved `[target]` table for the given target.
    pub fn target<'a, T: Into<TargetTripleRef<'a>>>(&self, target: T) -> Result<TargetConfig> {
        let target = target.into();
        self.init_target_config(&target)?;
        Ok(self.target.borrow()[target.cli_target()].clone())
    }
    /// Returns the resolved linker path for the given target.
    pub fn linker<'a, T: Into<TargetTripleRef<'a>>>(&self, target: T) -> Result<Option<PathBuf>> {
        let target = target.into();
        self.init_target_config(&target)?;
        Ok(self.target.borrow()[target.cli_target()].linker.clone())
    }
    /// Returns the resolved runner path and args for the given target.
    pub fn runner<'a, T: Into<TargetTripleRef<'a>>>(
        &self,
        target: T,
    ) -> Result<Option<PathAndArgs>> {
        let target = target.into();
        self.init_target_config(&target)?;
        Ok(self.target.borrow()[target.cli_target()].runner.clone())
    }
    /// Returns the resolved rustflags for the given target.
    pub fn rustflags<'a, T: Into<TargetTripleRef<'a>>>(&self, target: T) -> Result<Option<Flags>> {
        let target = target.into();
        self.init_target_config(&target)?;
        Ok(self.target.borrow()[target.cli_target()].rustflags.clone())
    }
    /// Returns the resolved rustdocflags for the given target.
    pub fn rustdocflags<'a, T: Into<TargetTripleRef<'a>>>(
        &self,
        target: T,
    ) -> Result<Option<Flags>> {
        let target = target.into();
        self.init_target_config(&target)?;
        Ok(self.target.borrow()[target.cli_target()].rustdocflags.clone())
    }

    /// Returns the path and args that calls `rustc`.
    ///
    /// If [`RUSTC_WRAPPER`](BuildConfig::rustc_wrapper) or
    /// [`RUSTC_WORKSPACE_WRAPPER`](BuildConfig::rustc_workspace_wrapper) is set,
    /// the path is the wrapper path and the argument is the rustc path.
    /// Otherwise, the path is the rustc path.
    ///
    /// If you set `rustc` path by [`ResolveOptions::rustc`], this returns the path set by it.
    pub fn rustc(&self) -> &PathAndArgs {
        self.cx.rustc(&self.build)
    }
    /// Returns the path to `cargo`.
    ///
    /// The returned path is the value of the `CARGO` environment variable if it is set. Otherwise, "cargo".
    ///
    /// If you set `cargo` path by [`ResolveOptions::cargo`], this returns the path set by it.
    pub fn cargo(&self) -> &OsStr {
        &self.cx.cargo
    }
    /// Returns the host triple.
    pub fn host_triple(&self) -> Result<&str> {
        self.cx.host_triple(&self.build)
    }
    /// Returns the version of the [current rustc](Self::rustc).
    ///
    /// The result is usually the same as [`cargo_version`](Self::cargo_version),
    /// but it may differ if a different rustc is specified in config or if the
    /// [user is manipulating the output of the rustc](https://github.com/taiki-e/cargo-minimal-versions/issues/29).
    ///
    /// # rustc_version vs cargo_version
    ///
    /// Which is the preferred to use depends on the situation:
    ///
    /// - You will need to know the **rustc** version to determine whether options passed to rustc
    ///   via RUSTFLAGS or RUSTDOCFLAGS like `-C instrument-coverage` are available.
    /// - You will need to know the **cargo** version to determine whether fields in `Cargo.toml`
    ///   or cargo's CLI options are available.
    pub fn rustc_version(&self) -> Result<RustcVersion> {
        self.cx.rustc_version(&self.build)
    }
    /// Returns the version of the [current cargo](Self::cargo).
    ///
    /// See also [`rustc_version`](Self::rustc_version).
    pub fn cargo_version(&self) -> Result<CargoVersion> {
        self.cx.cargo_version(&self.build)
    }

    // TODO: add override instead?
    // /// Merges the given config into this config.
    // ///
    // /// If `force` is `false`, this matches the way cargo [merges configs in the
    // /// parent directories](https://doc.rust-lang.org/nightly/cargo/reference/config.html#hierarchical-structure).
    // ///
    // /// If `force` is `true`, this matches the way cargo's `--config` CLI option
    // /// overrides config.
    // pub fn merge(&mut self, low: Self, force: bool) -> Result<()> {
    //     merge::Merge::merge(self, low, force)
    // }
}

/// The `[build]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#build)
#[derive(Debug, Clone, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct BuildConfig {
    /// Sets the maximum number of compiler processes to run in parallel.
    /// If negative, it sets the maximum number of compiler processes to the
    /// number of logical CPUs plus provided value. Should not be 0.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildjobs)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub jobs: Option<i32>,
    /// Sets the executable to use for `rustc`.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustc)
    ///
    /// **Note:** If a wrapper is set, cargo's actual rustc call goes through
    /// the wrapper, so you may want to use [`Config::rustc`], which respects
    /// that behavior instead of referencing this value directly.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc: Option<PathBuf>,
    /// Sets a wrapper to execute instead of `rustc`.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustc-wrapper)
    ///
    /// **Note:** If a wrapper is set, cargo's actual rustc call goes through
    /// the wrapper, so you may want to use [`Config::rustc`], which respects
    /// that behavior instead of referencing this value directly.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc_wrapper: Option<PathBuf>,
    /// Sets a wrapper to execute instead of `rustc`, for workspace members only.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustc-workspace-wrapper)
    ///
    /// **Note:** If a wrapper is set, cargo's actual rustc call goes through
    /// the wrapper, so you may want to use [`Config::rustc`], which respects
    /// that behavior instead of referencing this value directly.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc_workspace_wrapper: Option<PathBuf>,
    /// Sets the executable to use for `rustdoc`.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustdoc)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustdoc: Option<PathBuf>,
    /// The default target platform triples to compile to.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildtarget)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target: Option<Vec<TargetTriple>>,
    /// The path to where all compiler output is placed. The default if not
    /// specified is a directory named target located at the root of the workspace.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildtarget)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_dir: Option<PathBuf>,
    /// The path to where all compiler intermediate artifacts are placed. The default if not
    /// specified is the value of build.target-dir
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#build-dir)
    ///
    /// **Note:** If a template variable is used the path will be unresolved. For available template
    /// variables see the Cargo reference.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub build_dir: Option<PathBuf>,
    /// Extra command-line flags to pass to rustc. The value may be an array
    /// of strings or a space-separated string.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustflags)
    ///
    /// **Note:** This field does not reflect the target-specific rustflags
    /// configuration, so you may want to use [`Config::rustflags`] which respects
    /// the target-specific rustflags configuration.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustflags: Option<Flags>,
    /// Extra command-line flags to pass to `rustdoc`. The value may be an array
    /// of strings or a space-separated string.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildrustdocflags)
    ///
    /// **Note:** This field does not reflect the target-specific rustdocflags
    /// configuration, so you may want to use [`Config::rustdocflags`] which respects
    /// the target-specific rustdocflags configuration.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustdocflags: Option<Flags>,
    /// Whether or not to perform incremental compilation.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#buildincremental)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub incremental: Option<bool>,
    /// Strips the given path prefix from dep info file paths.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#builddep-info-basedir)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dep_info_basedir: Option<PathBuf>,

    // Resolve contexts. Completely ignored in serialization and deserialization.
    #[serde(skip)]
    override_target_rustflags: bool,
    #[serde(skip)]
    de_rustflags: Option<de::Flags>,
    #[serde(skip)]
    override_target_rustdocflags: bool,
    #[serde(skip)]
    de_rustdocflags: Option<de::Flags>,
}

impl BuildConfig {
    pub(crate) fn from_unresolved(de: de::BuildConfig, current_dir: &Path) -> Self {
        let jobs = de.jobs.map(|v| v.val);
        let rustc = de.rustc.map(|v| v.resolve_as_program_path(current_dir).into_owned());
        let rustc_wrapper =
            de.rustc_wrapper.map(|v| v.resolve_as_program_path(current_dir).into_owned());
        let rustc_workspace_wrapper =
            de.rustc_workspace_wrapper.map(|v| v.resolve_as_program_path(current_dir).into_owned());
        let rustdoc = de.rustdoc.map(|v| v.resolve_as_program_path(current_dir).into_owned());
        let target = de.target.map(|t| {
            t.as_array_no_split()
                .iter()
                .map(|v| {
                    TargetTriple::new(
                        v.val.clone().into(),
                        v.definition.as_ref(),
                        Some(current_dir),
                    )
                })
                .collect()
        });
        let target_dir = de.target_dir.map(|v| v.resolve_as_path(current_dir).into_owned());
        let build_dir = de.build_dir.map(|v| {
            if v.val.starts_with("{workspace-root}") || v.val.starts_with("{cargo-cache-home}") {
                return PathBuf::from(v.val);
            }

            v.resolve_as_path(current_dir).into_owned()
        });
        let de_rustflags = de.rustflags.clone();
        let rustflags =
            de.rustflags.map(|v| Flags { flags: v.flags.into_iter().map(|v| v.val).collect() });
        let de_rustdocflags = de.rustdocflags.clone();
        let rustdocflags =
            de.rustdocflags.map(|v| Flags { flags: v.flags.into_iter().map(|v| v.val).collect() });
        let incremental = de.incremental.map(|v| v.val);
        let dep_info_basedir =
            de.dep_info_basedir.map(|v| v.resolve_as_path(current_dir).into_owned());
        let override_target_rustflags = de.override_target_rustflags;
        let override_target_rustdocflags = de.override_target_rustdocflags;
        Self {
            jobs,
            rustc,
            rustc_wrapper,
            rustc_workspace_wrapper,
            rustdoc,
            target,
            target_dir,
            build_dir,
            rustflags,
            rustdocflags,
            incremental,
            dep_info_basedir,
            override_target_rustflags,
            de_rustflags,
            override_target_rustdocflags,
            de_rustdocflags,
        }
    }
}

// https://github.com/rust-lang/cargo/blob/0.80.0/src/cargo/util/context/target.rs
/// A `[target.<triple>]` or `[target.<cfg>]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#target)
#[derive(Debug, Clone, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct TargetConfig {
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#targettriplelinker)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub linker: Option<PathBuf>,
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
}

impl TargetConfig {
    fn from_unresolved(de: de::TargetConfig, current_dir: &Path) -> Self {
        let linker = de.linker.map(|v| v.resolve_as_program_path(current_dir).into_owned());
        let runner = match de.runner {
            Some(v) => Some(PathAndArgs {
                path: v.path.resolve_program(current_dir).into_owned(),
                args: v.args.into_iter().map(|v| v.val.into()).collect(),
            }),
            None => None,
        };
        let rustflags =
            de.rustflags.map(|v| Flags { flags: v.flags.into_iter().map(|v| v.val).collect() });
        let rustdocflags =
            de.rustdocflags.map(|v| Flags { flags: v.flags.into_iter().map(|v| v.val).collect() });
        Self { linker, runner, rustflags, rustdocflags }
    }
}

/// The `[doc]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#doc)
#[derive(Debug, Clone, Default, Serialize)]
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

impl DocConfig {
    fn from_unresolved(de: de::DocConfig, current_dir: &Path) -> Self {
        let browser = de.browser.map(|v| PathAndArgs::from_unresolved(v, current_dir));
        Self { browser }
    }
}

/// A value of the `[env]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#env)
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct EnvConfigValue {
    pub value: OsString,
    pub force: bool,
    pub relative: bool,
}

impl EnvConfigValue {
    fn from_unresolved(de: de::EnvConfigValue, current_dir: &Path) -> Self {
        if let de::EnvConfigValue::Table {
            force, relative: Some(Value { val: true, .. }), ..
        } = &de
        {
            return Self {
                value: de.resolve(current_dir).into_owned(),
                force: force.as_ref().is_some_and(|v| v.val),
                // Since we resolved the value, it is no longer relative.
                relative: false,
            };
        }
        match de {
            de::EnvConfigValue::Value(value) => {
                Self { value: value.val.into(), force: false, relative: false }
            }
            de::EnvConfigValue::Table { value, force, .. } => Self {
                value: value.val.into(),
                force: force.is_some_and(|v| v.val),
                relative: false,
            },
        }
    }
}

impl Serialize for EnvConfigValue {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        #[derive(Serialize)]
        #[serde(untagged)]
        enum EnvRepr<'a> {
            Value(Cow<'a, str>),
            Table {
                value: Cow<'a, str>,
                #[serde(skip_serializing_if = "ops::Not::not")]
                force: bool,
                #[serde(skip_serializing_if = "ops::Not::not")]
                relative: bool,
            },
        }
        match self {
            Self { value, force: false, relative: false } => {
                EnvRepr::Value(value.to_string_lossy()).serialize(serializer)
            }
            Self { value, force, relative, .. } => EnvRepr::Table {
                value: value.to_string_lossy(),
                force: *force,
                relative: *relative,
            }
            .serialize(serializer),
        }
    }
}

/// The `[future-incompat-report]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#future-incompat-report)
#[derive(Debug, Clone, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct FutureIncompatReportConfig {
    /// Controls how often we display a notification to the terminal when a future incompat report is available.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#future-incompat-reportfrequency)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub frequency: Option<Frequency>,
}

impl FutureIncompatReportConfig {
    fn from_unresolved(de: de::FutureIncompatReportConfig) -> Self {
        let frequency = de.frequency.map(|v| v.val);
        Self { frequency }
    }
}

/// The `[cargo-new]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#cargo-new)
#[derive(Debug, Clone, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct CargoNewConfig {
    /// Specifies the source control system to use for initializing a new repository.
    /// Valid values are git, hg (for Mercurial), pijul, fossil or none to disable this behavior.
    /// Defaults to git, or none if already inside a VCS repository. Can be overridden with the --vcs CLI option.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vcs: Option<VersionControlSoftware>,
}

impl CargoNewConfig {
    fn from_unresolved(de: de::CargoNewConfig) -> Self {
        Self { vcs: de.vcs.map(|v| v.val) }
    }
}

/// The `[http]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#http)
#[derive(Debug, Clone, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct HttpConfig {
    /// If true, enables debugging of HTTP requests.
    /// The debug information can be seen by setting the `CARGO_LOG=network=debug` environment variable
    /// (or use `network=trace` for even more information).
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpdebug)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub debug: Option<bool>,
    /// Sets an HTTP and HTTPS proxy to use. The format is in libcurl format as in `[protocol://]host[:port]`.
    /// If not set, Cargo will also check the http.proxy setting in your global git configuration.
    /// If none of those are set, the HTTPS_PROXY or https_proxy environment variables set the proxy for HTTPS requests,
    /// and http_proxy sets it for HTTP requests.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpproxy)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proxy: Option<String>,
    /// Sets the timeout for each HTTP request, in seconds.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httptimeout)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timeout: Option<u32>,
    /// Path to a Certificate Authority (CA) bundle file, used to verify TLS certificates.
    /// If not specified, Cargo attempts to use the system certificates.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpcainfo)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cainfo: Option<String>,
    /// This determines whether or not TLS certificate revocation checks should be performed.
    /// This only works on Windows.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpcheck-revoke)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub check_revoke: Option<bool>,
    // TODO: Add ssl-version
    /// This setting controls timeout behavior for slow connections.
    /// If the average transfer speed in bytes per second is below the given value
    /// for `http.timeout` seconds (default 30 seconds), then the connection is considered too slow and Cargo will abort and retry.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httplow-speed-limit)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub low_speed_limit: Option<u32>,
    /// When true, Cargo will attempt to use the HTTP2 protocol with multiplexing.
    /// This allows multiple requests to use the same connection, usually improving performance when fetching multiple files.
    /// If false, Cargo will use HTTP 1.1 without pipelining.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpmultiplexing)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub multiplexing: Option<bool>,
    /// Specifies a custom user-agent header to use.
    /// The default if not specified is a string that includes Cargo’s version.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#httpuser-agent)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub user_agent: Option<String>,
}

impl HttpConfig {
    fn from_unresolved(de: de::HttpConfig) -> Self {
        Self {
            debug: de.debug.map(|v| v.val),
            proxy: de.proxy.map(|v| v.val),
            timeout: de.timeout.map(|v| v.val),
            cainfo: de.cainfo.map(|v| v.val),
            check_revoke: de.check_revoke.map(|v| v.val),
            low_speed_limit: de.low_speed_limit.map(|v| v.val),
            multiplexing: de.multiplexing.map(|v| v.val),
            user_agent: de.user_agent.map(|v| v.val),
        }
    }
}

/// The `[net]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#net)
#[derive(Debug, Clone, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct NetConfig {
    /// Number of times to retry possibly spurious network errors.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#netretry)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub retry: Option<u32>,
    /// If this is `true`, then Cargo will use the `git` executable to fetch
    /// registry indexes and git dependencies. If `false`, then it uses a
    /// built-in `git` library.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#netgit-fetch-with-cli)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub git_fetch_with_cli: Option<bool>,
    /// If this is `true`, then Cargo will avoid accessing the network, and
    /// attempt to proceed with locally cached data. If `false`, Cargo will
    /// access the network as needed, and generate an error if it encounters a
    /// network error.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#netoffline)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub offline: Option<bool>,
}

impl NetConfig {
    fn from_unresolved(de: de::NetConfig) -> Self {
        let retry = de.retry.map(|v| v.val);
        let git_fetch_with_cli = de.git_fetch_with_cli.map(|v| v.val);
        let offline = de.offline.map(|v| v.val);
        Self { retry, git_fetch_with_cli, offline }
    }
}

/// A value of the `[registries]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registries)
#[derive(Clone, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct RegistriesConfigValue {
    /// Specifies the URL of the git index for the registry.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registriesnameindex)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub index: Option<String>,
    /// Specifies the authentication token for the given registry.
    ///
    /// Note: This library does not read any values in the
    /// [credentials](https://doc.rust-lang.org/nightly/cargo/reference/config.html#credentials)
    /// file.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registriesnametoken)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub token: Option<String>,
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
    pub protocol: Option<RegistriesProtocol>,
}

impl RegistriesConfigValue {
    fn from_unresolved(
        de: de::RegistriesConfigValue,
        credential_alias: &BTreeMap<String, PathAndArgs>,
        current_dir: &Path,
    ) -> Self {
        let index = de.index.map(|v| v.val);
        let token = de.token.map(|v| v.val);
        let credential_provider = de
            .credential_provider
            .map(|v| CredentialProvider::from_unresolved(v, credential_alias, current_dir));
        let protocol = de.protocol.map(|v| match v.val {
            de::RegistriesProtocol::Git => RegistriesProtocol::Git,
            de::RegistriesProtocol::Sparse => RegistriesProtocol::Sparse,
        });
        Self { index, token, credential_provider, protocol }
    }
}

impl fmt::Debug for RegistriesConfigValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { index, token, credential_provider, protocol } = self;
        let redacted_token = token.as_ref().map(|_| "[REDACTED]");
        f.debug_struct("RegistriesConfigValue")
            .field("index", &index)
            .field("token", &redacted_token)
            .field("credential_provider", credential_provider)
            .field("protocol", &protocol)
            .finish_non_exhaustive()
    }
}

/// The `[registry]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#registry)
#[derive(Clone, Default, Serialize)]
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
    pub default: Option<String>,
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
    pub token: Option<String>,
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

impl RegistryConfig {
    fn from_unresolved(
        de: de::RegistryConfig,
        credential_alias: &BTreeMap<String, PathAndArgs>,
        current_dir: &Path,
    ) -> Self {
        let default = de.default.map(|v| v.val);
        let credential_provider = de
            .credential_provider
            .map(|v| CredentialProvider::from_unresolved(v, credential_alias, current_dir));
        let token = de.token.map(|v| v.val);
        let global_credential_providers = GlobalCredentialProviders(
            de.global_credential_providers
                .0
                .into_iter()
                .map(|provider| {
                    CredentialProvider::from_unresolved(provider, credential_alias, current_dir)
                })
                .collect(),
        );
        Self { default, credential_provider, token, global_credential_providers }
    }
}

impl fmt::Debug for RegistryConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { default, credential_provider, token, global_credential_providers } = self;
        let redacted_token = token.as_ref().map(|_| "[REDACTED]");
        f.debug_struct("RegistryConfig")
            .field("default", &default)
            .field("credential_provider", credential_provider)
            .field("token", &redacted_token)
            .field("global_credential_providers", &global_credential_providers.0)
            .finish()
    }
}

/// A value of the `[source]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#source)
#[derive(Debug, Clone, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct SourceConfigValue {
    /// If set, replace this source with the given named source or named registry.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamereplace-with)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub replace_with: Option<String>,
    /// Sets the path to a directory to use as a directory source.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamedirectory)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub directory: Option<PathBuf>,
    /// Sets the URL to use for a registry source.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenameregistry)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub registry: Option<String>,
    /// Sets the path to a directory to use as a local registry source.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamelocal-registry)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub local_registry: Option<PathBuf>,
    /// Sets the URL to use for a git source.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamegit)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub git: Option<String>,
    /// Sets the branch name to use for a git repository.
    /// If none of branch, tag, or rev is set, defaults to the master branch.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamebranch)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub branch: Option<String>,
    /// Sets the tag name to use for a git repository.
    /// If none of branch, tag, or rev is set, defaults to the master branch.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenametag)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tag: Option<String>,
    /// Sets the revision to use for a git repository.
    /// If none of branch, tag, or rev is set, defaults to the master branch.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#sourcenamerev)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rev: Option<String>,
}

impl SourceConfigValue {
    fn from_unresolved(de: de::SourceConfigValue, current_dir: &Path) -> Self {
        let replace_with = de.replace_with.map(|v| v.val);
        let directory = de.directory.map(|v| v.resolve_as_path(current_dir).into_owned());
        let registry = de.registry.map(|v| v.val);
        let local_registry = de.local_registry.map(|v| v.resolve_as_path(current_dir).into_owned());
        let git = de.git.map(|v| v.val);
        let branch = de.branch.map(|v| v.val);
        let tag = de.tag.map(|v| v.val);
        let rev = de.rev.map(|v| v.val);

        Self { replace_with, directory, registry, local_registry, git, branch, tag, rev }
    }
}

/// List of global credential providers.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GlobalCredentialProviders(Vec<CredentialProvider>);

impl GlobalCredentialProviders {
    pub(crate) fn is_none(&self) -> bool {
        self.0.is_empty()
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

impl AsRef<[CredentialProvider]> for GlobalCredentialProviders {
    fn as_ref(&self) -> &[CredentialProvider] {
        &self.0
    }
}

impl From<Vec<CredentialProvider>> for GlobalCredentialProviders {
    fn from(list: Vec<CredentialProvider>) -> Self {
        Self(list)
    }
}

/// The kind of a registry's credential provider.
#[derive(Clone, Debug, PartialEq)]
#[non_exhaustive]
pub enum CredentialProvider {
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
    /// An alias, to be looked up in the `[credential-alias]` table.
    Alias(String),
}

impl Serialize for CredentialProvider {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut v = vec![];

        let command = match self {
            Self::CargoToken => return ["cargo:token"].serialize(serializer),
            Self::CargoWincred => return ["cargo:wincred"].serialize(serializer),
            Self::CargoMacosKeychain => return ["cargo:macos-keychain"].serialize(serializer),
            Self::CargoLibsecret => return ["cargo:libsecret"].serialize(serializer),
            Self::CargoTokenFromStdout(command) => {
                v.push("cargo:token-from-stdout".to_owned());

                command
            }
            Self::Plugin(command) => command,
            Self::Alias(alias) => return [alias].serialize(serializer),
        };

        command.serialize_to_array(&mut v);
        v.serialize(serializer)
    }
}

impl CredentialProvider {
    fn from_unresolved(
        de: de::CredentialProvider,
        credential_alias: &BTreeMap<String, PathAndArgs>,
        current_dir: &Path,
    ) -> Self {
        match de.kind {
            de::CredentialProviderKind::CargoToken => Self::CargoToken,
            de::CredentialProviderKind::CargoWincred => Self::CargoWincred,
            de::CredentialProviderKind::CargoMacosKeychain => Self::CargoMacosKeychain,
            de::CredentialProviderKind::CargoLibsecret => Self::CargoLibsecret,
            de::CredentialProviderKind::CargoTokenFromStdout(command) => {
                Self::CargoTokenFromStdout(PathAndArgs::from_unresolved(command, current_dir))
            }
            de::CredentialProviderKind::Plugin(command) => {
                Self::Plugin(PathAndArgs::from_unresolved(command, current_dir))
            }
            de::CredentialProviderKind::MaybeAlias(value) => {
                if credential_alias.contains_key(&value.val) {
                    Self::Alias(value.val)
                } else {
                    Self::Plugin(PathAndArgs::from_unresolved(
                        de::PathAndArgs::from_string(&value.val, value.definition.as_ref())
                            .unwrap(),
                        current_dir,
                    ))
                }
            }
        }
    }
}

/// The `[term]` table.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#term)
#[derive(Debug, Clone, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct TermConfig {
    /// Controls whether or not log messages are displayed by Cargo.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#termquiet)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub quiet: Option<bool>,
    /// Controls whether or not extra detailed messages are displayed by Cargo.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#termverbose)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub verbose: Option<bool>,
    /// Controls whether or not colored output is used in the terminal.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#termcolor)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub color: Option<Color>,
    #[serde(default)]
    #[serde(skip_serializing_if = "TermProgressConfig::is_none")]
    pub progress: TermProgressConfig,
}

impl TermConfig {
    fn from_unresolved(de: de::TermConfig) -> Self {
        let quiet = de.quiet.map(|v| v.val);
        let verbose = de.verbose.map(|v| v.val);
        let color = de.color.map(|v| v.val);
        let progress = TermProgressConfig::from_unresolved(de.progress);
        Self { quiet, verbose, color, progress }
    }
}

#[derive(Debug, Clone, Default, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct TermProgressConfig {
    /// Controls whether or not progress bar is shown in the terminal.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#termprogresswhen)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub when: Option<When>,
    /// Sets the width for progress bar.
    ///
    /// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#termprogresswidth)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub width: Option<u32>,
}

impl TermProgressConfig {
    fn from_unresolved(de: de::TermProgress) -> Self {
        let when = de.when.map(|v| v.val);
        let width = de.width.map(|v| v.val);
        Self { when, width }
    }
}

/// A representation of rustflags or rustdocflags.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
#[serde(transparent)]
#[non_exhaustive]
pub struct Flags {
    pub flags: Vec<String>,
}

impl Flags {
    /// Creates a rustflags or rustdocflags from a string separated with ASCII unit separator ('\x1f').
    ///
    /// This is a valid format for the following environment variables:
    ///
    /// - `CARGO_ENCODED_RUSTFLAGS` (Cargo 1.55+)
    /// - `CARGO_ENCODED_RUSTDOCFLAGS` (Cargo 1.55+)
    ///
    /// See also [`encode`](Self::encode).
    pub fn from_encoded(s: &str) -> Self {
        Self { flags: split_encoded(s).map(str::to_owned).collect() }
    }

    /// Creates a rustflags or rustdocflags from a string separated with space (' ').
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
    /// See also [`encode_space_separated`](Self::encode_space_separated).
    pub fn from_space_separated(s: &str) -> Self {
        Self { flags: split_space_separated(s).map(str::to_owned).collect() }
    }

    /// Concatenates this rustflags or rustdocflags with ASCII unit separator ('\x1f').
    ///
    /// This is a valid format for the following environment variables:
    ///
    /// - `CARGO_ENCODED_RUSTFLAGS` (Cargo 1.55+)
    /// - `CARGO_ENCODED_RUSTDOCFLAGS` (Cargo 1.55+)
    ///
    /// # Errors
    ///
    /// This returns an error if any of flag contains ASCII unit separator ('\x1f').
    ///
    /// This is because even if you do not intend it to be interpreted as a
    /// separator, Cargo will interpret it as a separator.
    ///
    /// Since it is not easy to insert an ASCII unit separator in a toml file or
    /// Shell environment variable, this usually occurs when this rustflags or rustdocflags
    /// is created in the wrong way ([`from_encoded`](Self::from_encoded) vs
    /// [`from_space_separated`](Self::from_space_separated)) or when a flag
    /// containing a separator is written in the rust code ([`push`](Self::push),
    /// `into`, `from`, etc.).
    pub fn encode(&self) -> Result<String> {
        self.encode_internal('\x1f')
    }

    /// Concatenates this rustflags or rustdocflags with space (' ').
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
    /// # Errors
    ///
    /// This returns an error if any of flag contains space (' ').
    ///
    /// This is because even if you do not intend it to be interpreted as a
    /// separator, Cargo will interpret it as a separator.
    ///
    /// If you run into this error, consider using a more robust
    /// [`CARGO_ENCODED_*` flags](Self::encode).
    pub fn encode_space_separated(&self) -> Result<String> {
        self.encode_internal(' ')
    }

    fn encode_internal(&self, sep: char) -> Result<String> {
        let mut buf = String::with_capacity(
            self.flags.len().saturating_sub(1) + self.flags.iter().map(String::len).sum::<usize>(),
        );
        for flag in &self.flags {
            if flag.contains(sep) {
                bail!("flag in rustflags must not contain its separator ({sep:?})");
            }
            if !buf.is_empty() {
                buf.push(sep);
            }
            buf.push_str(flag);
        }
        Ok(buf)
    }

    /// Appends a flag to the back of this rustflags or rustdocflags.
    pub fn push<S: Into<String>>(&mut self, flag: S) {
        self.flags.push(flag.into());
    }
}

impl From<Vec<String>> for Flags {
    fn from(value: Vec<String>) -> Self {
        Self { flags: value }
    }
}
impl From<&[String]> for Flags {
    fn from(value: &[String]) -> Self {
        Self { flags: value.to_owned() }
    }
}
impl From<&[&str]> for Flags {
    fn from(value: &[&str]) -> Self {
        Self { flags: value.iter().map(|&v| v.to_owned()).collect() }
    }
}
impl<const N: usize> From<[String; N]> for Flags {
    fn from(value: [String; N]) -> Self {
        Self { flags: value[..].to_owned() }
    }
}
impl<const N: usize> From<[&str; N]> for Flags {
    fn from(value: [&str; N]) -> Self {
        Self { flags: value[..].iter().map(|&v| v.to_owned()).collect() }
    }
}

/// An executable path with arguments.
///
/// [Cargo Reference](https://doc.rust-lang.org/nightly/cargo/reference/config.html#executable-paths-with-arguments)
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct PathAndArgs {
    pub path: PathBuf,
    pub args: Vec<OsString>,
}

impl PathAndArgs {
    /// Creates a new program.
    pub fn new<P: Into<PathBuf>>(path: P) -> Self {
        Self { path: path.into(), args: vec![] }
    }
    /// Adds an argument to pass to the program.
    pub fn arg<S: Into<OsString>>(&mut self, arg: S) -> &mut Self {
        self.args.push(arg.into());
        self
    }
    /// Adds multiple arguments to pass to the program.
    pub fn args<I: IntoIterator<Item = S>, S: Into<OsString>>(&mut self, args: I) -> &mut Self {
        self.args.extend(args.into_iter().map(Into::into));
        self
    }
    fn from_unresolved(de: de::PathAndArgs, current_dir: &Path) -> Self {
        Self {
            path: de.path.resolve_program(current_dir).into_owned(),
            args: de.args.into_iter().map(|v| v.val.into()).collect(),
        }
    }

    fn serialize_to_array(&self, v: &mut Vec<String>) {
        v.push(self.path.to_string_lossy().into_owned());

        for arg in &self.args {
            v.push(arg.to_string_lossy().into_owned());
        }
    }
}

impl Serialize for PathAndArgs {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut v = Vec::with_capacity(1 + self.args.len());
        v.push(self.path.to_string_lossy().into_owned());
        for arg in &self.args {
            v.push(arg.to_string_lossy().into_owned());
        }
        v.serialize(serializer)
    }
}

impl From<PathAndArgs> for Command {
    fn from(value: PathAndArgs) -> Self {
        Self::from(&value)
    }
}
impl From<&PathAndArgs> for Command {
    fn from(value: &PathAndArgs) -> Self {
        let mut cmd = Command::new(&value.path);
        cmd.args(&value.args);
        cmd
    }
}
impl From<&PathAndArgs> for ProcessBuilder {
    fn from(value: &PathAndArgs) -> Self {
        ProcessBuilder::from_std(Command::from(value))
    }
}

/// A list of string.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
#[serde(transparent)]
#[non_exhaustive]
pub struct StringList {
    pub list: Vec<String>,
}

impl StringList {
    fn from_string(value: &str) -> Self {
        Self { list: split_space_separated(value).map(str::to_owned).collect() }
    }
    fn from_array(list: Vec<String>) -> Self {
        Self { list }
    }
    fn from_unresolved(value: de::StringList) -> Self {
        Self { list: value.list.into_iter().map(|v| v.val).collect() }
    }
}

impl From<String> for StringList {
    fn from(value: String) -> Self {
        Self::from_string(&value)
    }
}
impl From<&String> for StringList {
    fn from(value: &String) -> Self {
        Self::from_string(value)
    }
}
impl From<&str> for StringList {
    fn from(value: &str) -> Self {
        Self::from_string(value)
    }
}
impl From<Vec<String>> for StringList {
    fn from(value: Vec<String>) -> Self {
        Self::from_array(value)
    }
}
impl From<&[String]> for StringList {
    fn from(value: &[String]) -> Self {
        Self::from_array(value.to_owned())
    }
}
impl From<&[&str]> for StringList {
    fn from(value: &[&str]) -> Self {
        Self::from_array(value.iter().map(|&v| v.to_owned()).collect())
    }
}
impl<const N: usize> From<[String; N]> for StringList {
    fn from(value: [String; N]) -> Self {
        Self::from_array(value[..].to_owned())
    }
}
impl<const N: usize> From<[&str; N]> for StringList {
    fn from(value: [&str; N]) -> Self {
        Self::from_array(value[..].iter().map(|&v| v.to_owned()).collect())
    }
}
