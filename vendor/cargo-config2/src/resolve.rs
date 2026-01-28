// SPDX-License-Identifier: Apache-2.0 OR MIT

use core::{
    cell::{OnceCell, RefCell},
    cmp,
    hash::Hash,
    iter,
    str::FromStr,
};
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    ffi::{OsStr, OsString},
    path::{Path, PathBuf},
};

use serde::{
    de::{Deserialize, Deserializer},
    ser::{Serialize, Serializer},
};
use serde_derive::{Deserialize, Serialize};

use crate::{
    PathAndArgs,
    cfg_expr::expr::{Expression, Predicate},
    easy,
    error::{Context as _, Error, Result},
    process::ProcessBuilder,
    value::{Definition, Value},
    walk,
};

#[derive(Debug, Clone, Default)]
#[must_use]
pub struct ResolveOptions {
    env: Option<HashMap<String, OsString>>,
    rustc: Option<PathAndArgs>,
    cargo: Option<OsString>,
    #[allow(clippy::option_option)]
    cargo_home: Option<Option<PathBuf>>,
    host_triple: Option<String>,
}

impl ResolveOptions {
    /// Sets `rustc` path and args.
    ///
    /// # Default value
    ///
    /// [`Config::rustc`](crate::Config::rustc)
    pub fn rustc<P: Into<PathAndArgs>>(mut self, rustc: P) -> Self {
        self.rustc = Some(rustc.into());
        self
    }
    /// Sets `cargo` path.
    ///
    /// # Default value
    ///
    /// The value of the `CARGO` environment variable if it is set. Otherwise, "cargo".
    pub fn cargo<S: Into<OsString>>(mut self, cargo: S) -> Self {
        self.cargo = Some(cargo.into());
        self
    }
    /// Sets `CARGO_HOME` path.
    ///
    /// # Default value
    ///
    /// [`home::cargo_home_with_cwd`] if the current directory was specified when
    /// loading config. Otherwise, [`home::cargo_home`].
    ///
    /// [`home::cargo_home_with_cwd`]: https://docs.rs/home/latest/home/fn.cargo_home_with_cwd.html
    /// [`home::cargo_home`]: https://docs.rs/home/latest/home/fn.cargo_home.html
    pub fn cargo_home<P: Into<Option<PathBuf>>>(mut self, cargo_home: P) -> Self {
        self.cargo_home = Some(cargo_home.into());
        self
    }
    /// Sets host target triple.
    ///
    /// # Default value
    ///
    /// Parse the version output of `cargo` specified by [`Self::cargo`].
    pub fn host_triple<S: Into<String>>(mut self, triple: S) -> Self {
        self.host_triple = Some(triple.into());
        self
    }
    /// Sets the specified key-values as environment variables to be read during
    /// config resolution.
    ///
    /// This is mainly intended for use in tests where it is necessary to adjust
    /// the kinds of environment variables that are referenced.
    ///
    /// # Default value
    ///
    /// [`std::env::vars_os`]
    pub fn env<I: IntoIterator<Item = (K, V)>, K: Into<OsString>, V: Into<OsString>>(
        mut self,
        vars: I,
    ) -> Self {
        let mut env = HashMap::default();
        for (k, v) in vars {
            if let Ok(k) = k.into().into_string() {
                if k.starts_with("CARGO") || k.starts_with("RUST") || k == "BROWSER" {
                    env.insert(k, v.into());
                }
            }
        }
        self.env = Some(env);
        self
    }

    #[doc(hidden)] // Not public API.
    pub fn into_context(mut self, current_dir: PathBuf) -> ResolveContext {
        if self.env.is_none() {
            self = self.env(std::env::vars_os());
        }
        let env = self.env.unwrap();
        let rustc = match self.rustc {
            Some(rustc) => OnceCell::from(rustc),
            None => OnceCell::new(),
        };
        let cargo = match self.cargo {
            Some(cargo) => cargo,
            None => env.get("CARGO").cloned().unwrap_or_else(|| "cargo".into()),
        };
        let cargo_home = match self.cargo_home {
            Some(cargo_home) => OnceCell::from(cargo_home),
            None => OnceCell::new(),
        };
        let host_triple = match self.host_triple {
            Some(host_triple) => OnceCell::from(host_triple),
            None => OnceCell::new(),
        };

        ResolveContext {
            env,
            rustc,
            cargo,
            cargo_home,
            host_triple,
            rustc_version: OnceCell::new(),
            cargo_version: OnceCell::new(),
            cfg: RefCell::default(),
            current_dir,
        }
    }
}

#[doc(hidden)] // Not public API.
#[allow(unknown_lints, unnameable_types)] // Not public API. unnameable_types is available on Rust 1.79+
#[derive(Debug, Clone)]
#[must_use]
pub struct ResolveContext {
    pub(crate) env: HashMap<String, OsString>,
    rustc: OnceCell<easy::PathAndArgs>,
    pub(crate) cargo: OsString,
    cargo_home: OnceCell<Option<PathBuf>>,
    host_triple: OnceCell<String>,
    rustc_version: OnceCell<RustcVersion>,
    cargo_version: OnceCell<CargoVersion>,
    cfg: RefCell<CfgMap>,
    pub(crate) current_dir: PathBuf,
}

impl ResolveContext {
    pub(crate) fn rustc(&self, build_config: &easy::BuildConfig) -> &PathAndArgs {
        self.rustc.get_or_init(|| {
            // https://github.com/rust-lang/cargo/pull/10896
            // https://github.com/rust-lang/cargo/pull/13648
            let rustc =
                build_config.rustc.as_ref().map_or_else(|| rustc_path(&self.cargo), PathBuf::from);
            let rustc_wrapper = build_config.rustc_wrapper.clone();
            let rustc_workspace_wrapper = build_config.rustc_workspace_wrapper.clone();
            let mut rustc =
                rustc_wrapper.into_iter().chain(rustc_workspace_wrapper).chain(iter::once(rustc));
            PathAndArgs {
                path: rustc.next().unwrap(),
                args: rustc.map(PathBuf::into_os_string).collect(),
            }
        })
    }
    pub(crate) fn rustc_for_version(&self, build_config: &easy::BuildConfig) -> PathAndArgs {
        // Do not apply RUSTC_WORKSPACE_WRAPPER: https://github.com/cuviper/autocfg/issues/58#issuecomment-2067625980
        let rustc =
            build_config.rustc.as_ref().map_or_else(|| rustc_path(&self.cargo), PathBuf::from);
        let rustc_wrapper = build_config.rustc_wrapper.clone();
        let mut rustc = rustc_wrapper.into_iter().chain(iter::once(rustc));
        PathAndArgs {
            path: rustc.next().unwrap(),
            args: rustc.map(PathBuf::into_os_string).collect(),
        }
    }
    pub(crate) fn cargo_home(&self, cwd: &Path) -> Option<&Path> {
        self.cargo_home.get_or_init(|| walk::cargo_home_with_cwd(cwd)).as_deref()
    }
    pub(crate) fn host_triple(&self, build_config: &easy::BuildConfig) -> Result<&str> {
        if let Some(host) = self.host_triple.get() {
            return Ok(host);
        }
        let cargo_host = verbose_version(cmd!(&self.cargo)).and_then(|ref vv| {
            let r = self.cargo_version.set(cargo_version(vv)?);
            debug_assert!(r.is_ok());
            host_triple(vv)
        });
        let host = match cargo_host {
            Ok(host) => host,
            Err(_) => {
                let vv = &verbose_version((&self.rustc_for_version(build_config)).into())?;
                let r = self.rustc_version.set(rustc_version(vv)?);
                debug_assert!(r.is_ok());
                host_triple(vv)?
            }
        };
        Ok(self.host_triple.get_or_init(|| host))
    }
    pub(crate) fn rustc_version(&self, build_config: &easy::BuildConfig) -> Result<RustcVersion> {
        if let Some(&rustc_version) = self.rustc_version.get() {
            return Ok(rustc_version);
        }
        let _ = self.host_triple(build_config);
        if let Some(&rustc_version) = self.rustc_version.get() {
            return Ok(rustc_version);
        }
        let vv = &verbose_version((&self.rustc_for_version(build_config)).into())?;
        let rustc_version = rustc_version(vv)?;
        Ok(*self.rustc_version.get_or_init(|| rustc_version))
    }
    pub(crate) fn cargo_version(&self, build_config: &easy::BuildConfig) -> Result<CargoVersion> {
        if let Some(&cargo_version) = self.cargo_version.get() {
            return Ok(cargo_version);
        }
        let _ = self.host_triple(build_config);
        if let Some(&cargo_version) = self.cargo_version.get() {
            return Ok(cargo_version);
        }
        let vv = &verbose_version(cmd!(&self.cargo))?;
        let cargo_version = cargo_version(vv)?;
        Ok(*self.cargo_version.get_or_init(|| cargo_version))
    }

    // micro-optimization for static name -- avoiding name allocation can speed up
    // de::Config::apply_env by up to 40% because most env var names we fetch are static.
    pub(crate) fn env(&self, name: &'static str) -> Result<Option<Value<String>>> {
        match self.env.get(name) {
            None => Ok(None),
            Some(v) => Ok(Some(Value {
                val: v.clone().into_string().map_err(|var| Error::env_not_unicode(name, var))?,
                definition: Some(Definition::Environment(name.into())),
            })),
        }
    }
    pub(crate) fn env_redacted(&self, name: &'static str) -> Result<Option<Value<String>>> {
        match self.env.get(name) {
            None => Ok(None),
            Some(v) => Ok(Some(Value {
                val: v
                    .clone()
                    .into_string()
                    .map_err(|_var| Error::env_not_unicode_redacted(name))?,
                definition: Some(Definition::Environment(name.into())),
            })),
        }
    }
    pub(crate) fn env_parse<T>(&self, name: &'static str) -> Result<Option<Value<T>>>
    where
        T: FromStr,
        T::Err: std::error::Error + Send + Sync + 'static,
    {
        match self.env(name)? {
            Some(v) => Ok(Some(
                v.parse()
                    .with_context(|| format!("failed to parse environment variable `{name}`"))?,
            )),
            None => Ok(None),
        }
    }
    pub(crate) fn env_dyn(&self, name: &str) -> Result<Option<Value<String>>> {
        match self.env.get(name) {
            None => Ok(None),
            Some(v) => Ok(Some(Value {
                val: v.clone().into_string().map_err(|var| Error::env_not_unicode(name, var))?,
                definition: Some(Definition::Environment(name.to_owned().into())),
            })),
        }
    }

    pub(crate) fn eval_cfg(
        &self,
        expr: &str,
        target: &TargetTripleRef<'_>,
        build_config: &easy::BuildConfig,
    ) -> Result<bool> {
        let expr = Expression::parse(expr).map_err(Error::new)?;
        let mut cfg_map = self.cfg.borrow_mut();
        cfg_map.eval_cfg(&expr, target, || self.rustc(build_config).into())
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct CfgMap {
    map: HashMap<TargetTripleBorrow<'static>, Cfg>,
}

impl CfgMap {
    pub(crate) fn eval_cfg(
        &mut self,
        expr: &Expression,
        target: &TargetTripleRef<'_>,
        rustc: impl FnOnce() -> ProcessBuilder,
    ) -> Result<bool> {
        let cfg = match self.map.get(target.cli_target()) {
            Some(cfg) => cfg,
            None => {
                let cfg = Cfg::from_rustc(rustc(), target)?;
                self.map.insert(TargetTripleBorrow(target.clone().into_owned()), cfg);
                &self.map[target.cli_target()]
            }
        };
        Ok(expr.eval(|pred| match pred {
            Predicate::Flag(flag) => {
                match *flag {
                    // https://github.com/rust-lang/cargo/pull/7660
                    "test" | "debug_assertions" | "proc_macro" => false,
                    flag => cfg.flags.contains(flag),
                }
            }
            Predicate::KeyValue { key, val } => {
                match *key {
                    // https://github.com/rust-lang/cargo/pull/7660
                    "feature" => false,
                    key => cfg.key_values.get(key).is_some_and(|values| values.contains(*val)),
                }
            }
        }))
    }
}

#[derive(Debug, Clone)]
struct Cfg {
    flags: HashSet<String>,
    key_values: HashMap<String, HashSet<String>>,
}

impl Cfg {
    fn from_rustc(mut rustc: ProcessBuilder, target: &TargetTripleRef<'_>) -> Result<Self> {
        let list =
            rustc.args(["--print", "cfg", "--target", &*target.cli_target_string()]).read()?;
        Ok(Self::parse(&list))
    }

    fn parse(list: &str) -> Self {
        let mut flags = HashSet::default();
        let mut key_values = HashMap::<String, HashSet<String>>::default();

        for line in list.lines() {
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            match line.split_once('=') {
                None => {
                    flags.insert(line.to_owned());
                }
                Some((name, value)) => {
                    if value.len() < 2 || !value.starts_with('"') || !value.ends_with('"') {
                        if cfg!(test) {
                            panic!("invalid value '{value}'");
                        }
                        continue;
                    }
                    let value = &value[1..value.len() - 1];
                    if value.is_empty() {
                        continue;
                    }
                    if let Some(values) = key_values.get_mut(name) {
                        values.insert(value.to_owned());
                    } else {
                        let mut values = HashSet::default();
                        values.insert(value.to_owned());
                        key_values.insert(name.to_owned(), values);
                    }
                }
            }
        }

        Self { flags, key_values }
    }
}

#[derive(Debug, Clone)]
pub struct TargetTripleRef<'a> {
    triple: Cow<'a, str>,
    spec_path: Option<Cow<'a, Path>>,
}

pub type TargetTriple = TargetTripleRef<'static>;

impl PartialEq for TargetTripleRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cli_target() == other.cli_target()
    }
}
impl Eq for TargetTripleRef<'_> {}
impl PartialOrd for TargetTripleRef<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TargetTripleRef<'_> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.cli_target().cmp(other.cli_target())
    }
}
impl Hash for TargetTripleRef<'_> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.cli_target().hash(state);
    }
}

// This wrapper is needed to support pre-1.63 Rust.
// In pre-1.63 Rust you can't use TargetTripleRef<'non_static> as an index of
// HashMap<TargetTripleRef<'static>, _> without this trick.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub(crate) struct TargetTripleBorrow<'a>(pub(crate) TargetTripleRef<'a>);
impl core::borrow::Borrow<OsStr> for TargetTripleBorrow<'_> {
    fn borrow(&self) -> &OsStr {
        self.0.cli_target()
    }
}

fn is_spec_path(triple_or_spec_path: &str) -> bool {
    Path::new(triple_or_spec_path).extension() == Some(OsStr::new("json"))
        || triple_or_spec_path.contains('/')
        || triple_or_spec_path.contains('\\')
}
fn resolve_spec_path(
    spec_path: &str,
    def: Option<&Definition>,
    current_dir: Option<&Path>,
) -> Option<PathBuf> {
    if let Some(def) = def {
        if let Some(root) = def.root_opt(current_dir) {
            return Some(root.join(spec_path));
        }
    }
    None
}

impl<'a> TargetTripleRef<'a> {
    pub(crate) fn new(
        triple_or_spec_path: Cow<'a, str>,
        def: Option<&Definition>,
        current_dir: Option<&Path>,
    ) -> Self {
        // Handles custom target
        if is_spec_path(&triple_or_spec_path) {
            let triple = match &triple_or_spec_path {
                // `triple_or_spec_path` is valid UTF-8, so unwrap here will never panic.
                &Cow::Borrowed(v) => Path::new(v).file_stem().unwrap().to_str().unwrap().into(),
                Cow::Owned(v) => {
                    Path::new(v).file_stem().unwrap().to_str().unwrap().to_owned().into()
                }
            };
            Self {
                triple,
                spec_path: Some(match resolve_spec_path(&triple_or_spec_path, def, current_dir) {
                    Some(v) => v.into(),
                    None => match triple_or_spec_path {
                        Cow::Borrowed(v) => Path::new(v).into(),
                        Cow::Owned(v) => PathBuf::from(v).into(),
                    },
                }),
            }
        } else {
            Self { triple: triple_or_spec_path, spec_path: None }
        }
    }

    pub fn into_owned(self) -> TargetTriple {
        TargetTripleRef {
            triple: self.triple.into_owned().into(),
            spec_path: self.spec_path.map(|v| v.into_owned().into()),
        }
    }

    pub fn triple(&self) -> &str {
        &self.triple
    }
    pub fn spec_path(&self) -> Option<&Path> {
        self.spec_path.as_deref()
    }
    pub(crate) fn cli_target_string(&self) -> Cow<'_, str> {
        // Cargo converts spec path containing non-UTF8 byte to string with
        // to_string_lossy before passing it to rustc.
        // This is not good behavior but we just follow the behavior of cargo for now.
        //
        // ```
        // $ pwd
        // /tmp/��/a
        // $ cat .cargo/config.toml
        // [build]
        // target = "avr-unknown-gnu-atmega2560.json"
        // ```
        // $ cargo build
        // error: target path "/tmp/��/a/avr-unknown-gnu-atmega2560.json" is not a valid file
        //
        // Caused by:
        //   No such file or directory (os error 2)
        // ```
        self.cli_target().to_string_lossy()
    }
    pub(crate) fn cli_target(&self) -> &OsStr {
        match self.spec_path() {
            Some(v) => v.as_os_str(),
            None => OsStr::new(self.triple()),
        }
    }
}

impl<'a> From<&'a TargetTripleRef<'_>> for TargetTripleRef<'a> {
    fn from(value: &'a TargetTripleRef<'_>) -> Self {
        TargetTripleRef {
            triple: value.triple().into(),
            spec_path: value.spec_path().map(Into::into),
        }
    }
}
impl From<String> for TargetTripleRef<'static> {
    fn from(value: String) -> Self {
        Self::new(value.into(), None, None)
    }
}
impl<'a> From<&'a String> for TargetTripleRef<'a> {
    fn from(value: &'a String) -> Self {
        Self::new(value.into(), None, None)
    }
}
impl<'a> From<&'a str> for TargetTripleRef<'a> {
    fn from(value: &'a str) -> Self {
        Self::new(value.into(), None, None)
    }
}

impl Serialize for TargetTripleRef<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.cli_target_string().serialize(serializer)
    }
}
impl<'de> Deserialize<'de> for TargetTripleRef<'static> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(Self::new(String::deserialize(deserializer)?.into(), None, None))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct RustcVersion {
    pub major: u32,
    pub minor: u32,
    pub patch: Option<u32>,
    pub nightly: bool,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct CargoVersion {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
    pub nightly: bool,
}

impl RustcVersion {
    /// Returns the pair of the major and minor versions.
    ///
    /// This is useful for comparing versions: `version.major_minor() < (1, 70)`
    pub fn major_minor(&self) -> (u32, u32) {
        (self.major, self.minor)
    }
}
impl CargoVersion {
    /// Returns the pair of the major and minor versions.
    ///
    /// This is useful for comparing versions: `version.major_minor() < (1, 70)`
    pub fn major_minor(&self) -> (u32, u32) {
        (self.major, self.minor)
    }
}

fn verbose_version(mut rustc_or_cargo: ProcessBuilder) -> Result<(String, ProcessBuilder)> {
    // Use verbose version output because the packagers add extra strings to the normal version output.
    // Do not use long flags (--version --verbose) because clippy-deriver doesn't handle them properly.
    // -vV is also matched with that cargo internally uses: https://github.com/rust-lang/cargo/blob/0.80.0/src/cargo/util/rustc.rs#L65
    rustc_or_cargo.arg("-vV");
    let verbose_version = rustc_or_cargo.read()?;
    Ok((verbose_version, rustc_or_cargo))
}

fn parse_version(verbose_version: &str) -> Option<(u32, u32, Option<u32>, bool)> {
    let release = verbose_version.lines().find_map(|line| line.strip_prefix("release: "))?;
    let (version, channel) = release.split_once('-').unwrap_or((release, ""));
    let mut digits = version.splitn(3, '.');
    let major = digits.next()?.parse::<u32>().ok()?;
    let minor = digits.next()?.parse::<u32>().ok()?;
    let patch = match digits.next() {
        Some(p) => Some(p.parse::<u32>().ok()?),
        None => None,
    };
    let nightly = channel == "nightly" || channel == "dev";
    Some((major, minor, patch, nightly))
}

fn rustc_version((verbose_version, cmd): &(String, ProcessBuilder)) -> Result<RustcVersion> {
    let (major, minor, patch, nightly) = parse_version(verbose_version)
        .ok_or_else(|| format_err!("unexpected version output from {cmd}: {verbose_version}"))?;
    let nightly = match std::env::var_os("RUSTC_BOOTSTRAP") {
        // When -1 is passed rustc works like stable, e.g., cfg(target_feature = "unstable_target_feature") will never be set. https://github.com/rust-lang/rust/pull/132993
        Some(v) if v == "-1" => false,
        _ => nightly,
    };
    Ok(RustcVersion { major, minor, patch, nightly })
}
fn cargo_version((verbose_version, cmd): &(String, ProcessBuilder)) -> Result<CargoVersion> {
    let (major, minor, patch, nightly) = parse_version(verbose_version)
        .and_then(|(major, minor, patch, nightly)| Some((major, minor, patch?, nightly)))
        .ok_or_else(|| format_err!("unexpected version output from {cmd}: {verbose_version}"))?;
    Ok(CargoVersion { major, minor, patch, nightly })
}

/// Gets host triple of the given `rustc` or `cargo`.
fn host_triple((verbose_version, cmd): &(String, ProcessBuilder)) -> Result<String> {
    let host = verbose_version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .ok_or_else(|| format_err!("unexpected version output from {cmd}: {verbose_version}"))?
        .to_owned();
    Ok(host)
}

fn rustc_path(cargo: &OsStr) -> PathBuf {
    // When toolchain override shorthand (`+toolchain`) is used, `rustc` in
    // PATH and `CARGO` environment variable may be different toolchains.
    // When Rust was installed using rustup, the same toolchain's rustc
    // binary is in the same directory as the cargo binary, so we use it.
    let mut rustc = PathBuf::from(cargo);
    rustc.pop(); // cargo
    rustc.push(format!("rustc{}", std::env::consts::EXE_SUFFIX));
    if rustc.exists() { rustc } else { "rustc".into() }
}

#[allow(clippy::std_instead_of_alloc, clippy::std_instead_of_core)]
#[cfg(test)]
mod tests {
    use std::{
        fmt::Write as _,
        io::{self, Write as _},
    };

    use fs_err as fs;

    use super::*;

    fn fixtures_dir() -> &'static Path {
        Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures"))
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri doesn't support pipe2 (inside std::process::Command::output)
    fn version_and_host() {
        let rustc_vv = &verbose_version(cmd!("rustc")).unwrap();
        let cargo_vv = &verbose_version(cmd!("cargo")).unwrap();
        let rustc_version = rustc_version(rustc_vv).unwrap();
        let cargo_version = cargo_version(cargo_vv).unwrap();
        {
            let mut out = String::new();
            let _ = writeln!(out, "rustc version: {rustc_version:?}");
            let _ = writeln!(out, "rustc host: {:?}", host_triple(rustc_vv).unwrap());
            let _ = writeln!(out, "cargo version: {cargo_version:?}");
            let _ = writeln!(out, "cargo host: {:?}", host_triple(cargo_vv).unwrap());
            let mut stderr = io::stderr().lock(); // Not buffered because it is written at once.
            let _ = stderr.write_all(out.as_bytes());
            let _ = stderr.flush();
        }

        assert_eq!(rustc_version.major_minor(), (rustc_version.major, rustc_version.minor));
        assert!(rustc_version.major_minor() < (2, 0));
        assert!(rustc_version.major_minor() < (1, u32::MAX));
        assert!(rustc_version.major_minor() >= (1, 70));
        assert!(rustc_version.major_minor() > (1, 0));
        assert!(rustc_version.major_minor() > (0, u32::MAX));

        assert_eq!(cargo_version.major_minor(), (cargo_version.major, cargo_version.minor));
        assert!(cargo_version.major_minor() < (2, 0));
        assert!(cargo_version.major_minor() < (1, u32::MAX));
        assert!(cargo_version.major_minor() >= (1, 70));
        assert!(cargo_version.major_minor() > (1, 0));
        assert!(cargo_version.major_minor() > (0, u32::MAX));
    }

    #[test]
    fn target_triple() {
        let t = TargetTripleRef::from("x86_64-unknown-linux-gnu");
        assert_eq!(t.triple, "x86_64-unknown-linux-gnu");
        assert!(matches!(t.triple, Cow::Borrowed(..)));
        assert!(t.spec_path.is_none());
    }

    #[rustversion::attr(not(nightly), ignore)]
    #[test]
    #[cfg_attr(miri, ignore)] // Miri doesn't support pipe2 (inside std::process::Command::output)
    fn parse_cfg_list() {
        // builtin targets
        for target in cmd!("rustc", "--print", "target-list").read().unwrap().lines() {
            let _cfg = Cfg::from_rustc(cmd!("rustc"), &target.into()).unwrap();
        }
        // custom targets
        for spec_path in
            fs::read_dir(fixtures_dir().join("target-specs")).unwrap().map(|e| e.unwrap().path())
        {
            let _cfg = Cfg::from_rustc(cmd!("rustc"), &spec_path.to_str().unwrap().into()).unwrap();
        }
    }

    #[test]
    fn env_filter() {
        // NB: sync with bench in bench/bench.rs
        let env_list = [
            ("CARGO_BUILD_JOBS", "-1"),
            ("RUSTC", "rustc"),
            ("CARGO_BUILD_RUSTC", "rustc"),
            ("RUSTC_WRAPPER", "rustc_wrapper"),
            ("CARGO_BUILD_RUSTC_WRAPPER", "rustc_wrapper"),
            ("RUSTC_WORKSPACE_WRAPPER", "rustc_workspace_wrapper"),
            ("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "rustc_workspace_wrapper"),
            ("RUSTDOC", "rustdoc"),
            ("CARGO_BUILD_RUSTDOC", "rustdoc"),
            ("CARGO_BUILD_TARGET", "triple"),
            ("CARGO_TARGET_DIR", "target"),
            ("CARGO_BUILD_TARGET_DIR", "target"),
            ("CARGO_ENCODED_RUSTFLAGS", "1"),
            ("RUSTFLAGS", "1"),
            ("CARGO_BUILD_RUSTFLAGS", "1"),
            ("CARGO_ENCODED_RUSTDOCFLAGS", "1"),
            ("RUSTDOCFLAGS", "1"),
            ("CARGO_BUILD_RUSTDOCFLAGS", "1"),
            ("CARGO_INCREMENTAL", "false"),
            ("CARGO_BUILD_INCREMENTAL", "1"),
            ("CARGO_BUILD_DEP_INFO_BASEDIR", "1"),
            ("BROWSER", "1"),
            ("CARGO_FUTURE_INCOMPAT_REPORT_FREQUENCY", "always"),
            ("CARGO_CARGO_NEW_VCS", "git"),
            ("CARGO_HTTP_DEBUG", "true"),
            ("CARGO_HTTP_PROXY", "-"),
            ("CARGO_HTTP_TIMEOUT", "1"),
            ("CARGO_HTTP_CAINFO", "-"),
            ("CARGO_HTTP_CHECK_REVOKE", "true"),
            ("CARGO_HTTP_LOW_SPEED_LIMIT", "1"),
            ("CARGO_HTTP_MULTIPLEXING", "true"),
            ("CARGO_HTTP_USER_AGENT", "-"),
            ("CARGO_NET_RETRY", "1"),
            ("CARGO_NET_GIT_FETCH_WITH_CLI", "false"),
            ("CARGO_NET_OFFLINE", "false"),
            ("CARGO_REGISTRIES_crates-io_INDEX", "https://github.com/rust-lang/crates.io-index"),
            ("CARGO_REGISTRIES_crates-io_TOKEN", "00000000000000000000000000000000000"),
            ("CARGO_REGISTRY_DEFAULT", "crates-io"),
            ("CARGO_REGISTRY_TOKEN", "00000000000000000000000000000000000"),
            ("CARGO_REGISTRIES_CRATES_IO_PROTOCOL", "git"),
            ("CARGO_TERM_QUIET", "false"),
            ("CARGO_TERM_VERBOSE", "false"),
            ("CARGO_TERM_COLOR", "auto"),
            ("CARGO_TERM_PROGRESS_WHEN", "auto"),
            ("CARGO_TERM_PROGRESS_WIDTH", "100"),
        ];
        let mut config = crate::de::Config::default();
        let cx =
            &ResolveOptions::default().env(env_list).into_context(std::env::current_dir().unwrap());
        config.apply_env(cx).unwrap();

        // ResolveOptions::env attempts to avoid pushing unrelated envs.
        let mut env_list = env_list.to_vec();
        env_list.push(("A", "B"));
        let cx = &ResolveOptions::default()
            .env(env_list.iter().copied())
            .into_context(std::env::current_dir().unwrap());
        for (k, v) in env_list {
            if k == "A" {
                assert!(!cx.env.contains_key(k));
            } else {
                assert_eq!(cx.env[k], v, "key={k},value={v}");
            }
        }
    }

    #[test]
    fn rustc_wrapper() {
        for (env_list, expected) in [
            (
                &[
                    ("RUSTC", "rustc"),
                    ("CARGO_BUILD_RUSTC", "cargo_build_rustc"),
                    ("RUSTC_WRAPPER", "rustc_wrapper"),
                    ("CARGO_BUILD_RUSTC_WRAPPER", "cargo_build_rustc_wrapper"),
                    ("RUSTC_WORKSPACE_WRAPPER", "rustc_workspace_wrapper"),
                    ("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "cargo_build_rustc_workspace_wrapper"),
                ][..],
                PathAndArgs {
                    path: "rustc_wrapper".into(),
                    args: vec!["rustc_workspace_wrapper".into(), "rustc".into()],
                },
            ),
            (
                &[
                    ("RUSTC", "rustc"),
                    ("CARGO_BUILD_RUSTC", "cargo_build_rustc"),
                    ("RUSTC_WRAPPER", ""),
                    ("CARGO_BUILD_RUSTC_WRAPPER", "cargo_build_rustc_wrapper"),
                    ("RUSTC_WORKSPACE_WRAPPER", "rustc_workspace_wrapper"),
                    ("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "cargo_build_rustc_workspace_wrapper"),
                ][..],
                PathAndArgs { path: "rustc_workspace_wrapper".into(), args: vec!["rustc".into()] },
            ),
            (
                &[
                    ("RUSTC", "rustc"),
                    ("CARGO_BUILD_RUSTC", "cargo_build_rustc"),
                    ("RUSTC_WRAPPER", "rustc_wrapper"),
                    ("CARGO_BUILD_RUSTC_WRAPPER", "cargo_build_rustc_wrapper"),
                    ("RUSTC_WORKSPACE_WRAPPER", ""),
                    ("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "cargo_build_rustc_workspace_wrapper"),
                ][..],
                PathAndArgs { path: "rustc_wrapper".into(), args: vec!["rustc".into()] },
            ),
            (
                &[
                    ("CARGO_BUILD_RUSTC", "cargo_build_rustc"),
                    ("CARGO_BUILD_RUSTC_WRAPPER", "cargo_build_rustc_wrapper"),
                    ("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "cargo_build_rustc_workspace_wrapper"),
                ],
                PathAndArgs {
                    path: "cargo_build_rustc_wrapper".into(),
                    args: vec![
                        "cargo_build_rustc_workspace_wrapper".into(),
                        "cargo_build_rustc".into(),
                    ],
                },
            ),
            (
                &[
                    ("RUSTC", "rustc"),
                    ("RUSTC_WRAPPER", "rustc_wrapper"),
                    ("RUSTC_WORKSPACE_WRAPPER", "rustc_workspace_wrapper"),
                ],
                PathAndArgs {
                    path: "rustc_wrapper".into(),
                    args: vec!["rustc_workspace_wrapper".into(), "rustc".into()],
                },
            ),
            (
                &[
                    ("RUSTC", "rustc"),
                    ("RUSTC_WRAPPER", "rustc_wrapper"),
                    ("RUSTC_WORKSPACE_WRAPPER", ""),
                ],
                PathAndArgs { path: "rustc_wrapper".into(), args: vec!["rustc".into()] },
            ),
            (
                &[
                    ("RUSTC", "rustc"),
                    ("RUSTC_WRAPPER", ""),
                    ("RUSTC_WORKSPACE_WRAPPER", "rustc_workspace_wrapper"),
                ],
                PathAndArgs { path: "rustc_workspace_wrapper".into(), args: vec!["rustc".into()] },
            ),
            (&[("RUSTC", "rustc"), ("RUSTC_WRAPPER", "rustc_wrapper")], PathAndArgs {
                path: "rustc_wrapper".into(),
                args: vec!["rustc".into()],
            }),
            (
                &[("RUSTC", "rustc"), ("RUSTC_WORKSPACE_WRAPPER", "rustc_workspace_wrapper")],
                PathAndArgs { path: "rustc_workspace_wrapper".into(), args: vec!["rustc".into()] },
            ),
            (&[("RUSTC", "rustc"), ("RUSTC_WRAPPER", "")], PathAndArgs {
                path: "rustc".into(),
                args: vec![],
            }),
            (&[("RUSTC", "rustc"), ("RUSTC_WORKSPACE_WRAPPER", "")], PathAndArgs {
                path: "rustc".into(),
                args: vec![],
            }),
        ] {
            let mut config = crate::de::Config::default();
            let cx = &ResolveOptions::default()
                .env(env_list.iter().copied())
                .into_context(std::env::current_dir().unwrap());
            config.apply_env(cx).unwrap();
            let build = crate::easy::BuildConfig::from_unresolved(config.build, &cx.current_dir);
            assert_eq!(*cx.rustc(&build), expected);
        }
    }

    #[cfg(unix)]
    #[test]
    fn env_non_utf8() {
        use std::{ffi::OsStr, os::unix::prelude::OsStrExt as _};

        let cx = &ResolveOptions::default()
            .env([("CARGO_ALIAS_a", OsStr::from_bytes(&[b'f', b'o', 0x80, b'o']))])
            .cargo_home(None)
            .rustc(PathAndArgs::new("rustc"))
            .into_context(std::env::current_dir().unwrap());
        assert_eq!(
            cx.env("CARGO_ALIAS_a").unwrap_err().to_string(),
            "failed to parse environment variable `CARGO_ALIAS_a`"
        );
        assert_eq!(
            format!("{:#}", anyhow::Error::from(cx.env("CARGO_ALIAS_a").unwrap_err())),
            "failed to parse environment variable `CARGO_ALIAS_a`: environment variable was not valid unicode: \"fo\\x80o\""
        );
    }

    // #[test]
    // fn dump_all_env() {
    //     let mut config = crate::de::Config::default();
    //     let cx = &mut ResolveContext::no_env();
    //     config.apply_env(cx).unwrap();
    // }
}
