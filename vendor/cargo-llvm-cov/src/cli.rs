// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::{ffi::OsString, mem, str::FromStr};

use anyhow::{Error, Result, bail, format_err};
use camino::{Utf8Path, Utf8PathBuf};
use lexopt::{
    Arg::{Long, Short, Value},
    ValueExt as _,
};

use crate::{
    env,
    process::ProcessBuilder,
    term::{self, Coloring},
};

// TODO: add --config option and passthrough to cargo-config: https://github.com/rust-lang/cargo/pull/10755/

#[derive(Debug)]
pub(crate) struct Args {
    pub(crate) subcommand: Subcommand,

    pub(crate) cov: LlvmCovOptions,
    pub(crate) show_env: ShowEnvOptions,

    // https://doc.rust-lang.org/nightly/unstable-book/compiler-flags/instrument-coverage.html#including-doc-tests
    /// Including doc tests (unstable)
    ///
    /// This flag is unstable.
    /// See <https://github.com/taiki-e/cargo-llvm-cov/issues/2> for more.
    pub(crate) doctests: bool,

    // -------------------------------------------------------------------------
    // `cargo test` options
    // https://doc.rust-lang.org/nightly/cargo/commands/cargo-test.html
    // /// Generate coverage report without running tests
    // pub(crate) no_run: bool,
    // /// Run all tests regardless of failure
    // pub(crate) no_fail_fast: bool,
    /// Run all tests regardless of failure and generate report
    ///
    /// If tests failed but report generation succeeded, exit with a status of 0.
    pub(crate) ignore_run_fail: bool,
    // /// Display one character per test instead of one line
    // pub(crate) quiet: bool,
    /// Test only this package's library unit tests
    pub(crate) lib: bool,
    /// Test only the specified binary
    pub(crate) bin: Vec<String>,
    /// Test all binaries
    pub(crate) bins: bool,
    /// Test only the specified example
    pub(crate) example: Vec<String>,
    /// Test all examples
    pub(crate) examples: bool,
    /// Test only the specified test target
    pub(crate) test: Vec<String>,
    /// Test all tests
    pub(crate) tests: bool,
    /// Test only the specified bench target
    pub(crate) bench: Vec<String>,
    /// Test all benches
    pub(crate) benches: bool,
    /// Test all targets
    pub(crate) all_targets: bool,
    /// Test only this library's documentation (unstable)
    ///
    /// This flag is unstable because it automatically enables --doctests flag.
    /// See <https://github.com/taiki-e/cargo-llvm-cov/issues/2> for more.
    pub(crate) doc: bool,
    // /// Package to run tests for
    // pub(crate) package: Vec<String>,
    /// Test all packages in the workspace
    pub(crate) workspace: bool,
    /// Exclude packages from both the test and report
    pub(crate) exclude: Vec<String>,
    /// Exclude packages from the test (but not from the report)
    pub(crate) exclude_from_test: Vec<String>,
    /// Exclude packages from the report (but not from the test)
    pub(crate) exclude_from_report: Vec<String>,

    // /// Number of parallel jobs, defaults to # of CPUs
    // // i32 or string "default": https://github.com/rust-lang/cargo/blob/0.80.0/src/cargo/core/compiler/build_config.rs#L84-L97
    // pub(crate) jobs: Option<i32>,
    /// Build artifacts in release mode, with optimizations
    pub(crate) release: bool,
    /// Build artifacts with the specified profile
    ///
    /// On `cargo llvm-cov nextest`/`cargo llvm-cov nextest-archive` this is the
    /// value of `--cargo-profile` option, otherwise this is the value of  `--profile` option.
    pub(crate) cargo_profile: Option<String>,
    // /// Space or comma separated list of features to activate
    // pub(crate) features: Vec<String>,
    // /// Activate all available features
    // pub(crate) all_features: bool,
    // /// Do not activate the `default` feature
    // pub(crate) no_default_features: bool,
    /// Build for the target triple
    ///
    /// When this option is used, coverage for proc-macro and build script will
    /// not be displayed because cargo does not pass RUSTFLAGS to them.
    pub(crate) target: Option<String>,
    /// Activate coverage reporting only for the target triple
    ///
    /// Activate coverage reporting only for the target triple specified via `--target`.
    /// This is important, if the project uses multiple targets via the cargo
    /// bindeps feature, and not all targets can use `instrument-coverage`,
    /// e.g. a microkernel, or an embedded binary.
    pub(crate) coverage_target_only: bool,
    // TODO: Currently, we are using a subdirectory of the target directory as
    //       the actual target directory. What effect should this option have
    //       on its behavior?
    // /// Directory for all generated artifacts
    // target_dir: Option<Utf8PathBuf>,
    /// Use verbose output
    ///
    /// Use -vv (-vvv) to propagate verbosity to cargo.
    pub(crate) verbose: u8,
    /// Coloring
    // This flag will be propagated to both cargo and llvm-cov.
    pub(crate) color: Option<Coloring>,

    /// Use --remap-path-prefix for workspace root
    ///
    /// Note that this does not fully compatible with doctest.
    pub(crate) remap_path_prefix: bool,
    /// Include coverage of C/C++ code linked to Rust library/binary
    ///
    /// Note that `CC`/`CXX`/`LLVM_COV`/`LLVM_PROFDATA` environment variables
    /// must be set to Clang/LLVM compatible with the LLVM version used in rustc.
    // TODO: support specifying languages like: --include-ffi=c,  --include-ffi=c,c++
    pub(crate) include_ffi: bool,
    /// Build without cleaning any old build artifacts.
    ///
    /// Note that this can cause false positives/false negatives due to old build artifacts.
    pub(crate) no_clean: bool,
    /// Clean only profraw files
    pub(crate) profraw_only: bool,

    pub(crate) manifest: ManifestOptions,

    pub(crate) nextest_archive_file: Option<String>,

    pub(crate) cargo_args: Vec<String>,
    /// Arguments for the test binary
    pub(crate) rest: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum Subcommand {
    /// Run tests and generate coverage report.
    None,

    /// Run tests and generate coverage report.
    Test,

    /// Run a binary or example and generate coverage report.
    Run,

    /// Generate coverage report.
    Report {
        nextest_archive_file: bool,
    },

    /// Remove artifacts that cargo-llvm-cov has generated in the past
    Clean,

    /// Output the environment set by cargo-llvm-cov to build Rust projects.
    ShowEnv,

    /// Run tests with cargo nextest
    Nextest {
        archive_file: bool,
    },

    /// Build and archive tests with cargo nextest
    NextestArchive,

    // internal (unstable)
    Demangle,
}

static CARGO_LLVM_COV_USAGE: &str = include_str!("../docs/cargo-llvm-cov.txt");
static CARGO_LLVM_COV_TEST_USAGE: &str = include_str!("../docs/cargo-llvm-cov-test.txt");
static CARGO_LLVM_COV_RUN_USAGE: &str = include_str!("../docs/cargo-llvm-cov-run.txt");
static CARGO_LLVM_COV_REPORT_USAGE: &str = include_str!("../docs/cargo-llvm-cov-report.txt");
static CARGO_LLVM_COV_CLEAN_USAGE: &str = include_str!("../docs/cargo-llvm-cov-clean.txt");
static CARGO_LLVM_COV_SHOW_ENV_USAGE: &str = include_str!("../docs/cargo-llvm-cov-show-env.txt");
static CARGO_LLVM_COV_NEXTEST_USAGE: &str = include_str!("../docs/cargo-llvm-cov-nextest.txt");
static CARGO_LLVM_COV_NEXTEST_ARCHIVE_USAGE: &str =
    include_str!("../docs/cargo-llvm-cov-nextest-archive.txt");

impl Subcommand {
    fn can_passthrough(subcommand: Self) -> bool {
        matches!(subcommand, Self::Test | Self::Run | Self::Nextest { .. } | Self::NextestArchive)
    }

    fn help_text(subcommand: Self) -> &'static str {
        match subcommand {
            Self::None => CARGO_LLVM_COV_USAGE,
            Self::Test => CARGO_LLVM_COV_TEST_USAGE,
            Self::Run => CARGO_LLVM_COV_RUN_USAGE,
            Self::Report { .. } => CARGO_LLVM_COV_REPORT_USAGE,
            Self::Clean => CARGO_LLVM_COV_CLEAN_USAGE,
            Self::ShowEnv => CARGO_LLVM_COV_SHOW_ENV_USAGE,
            Self::Nextest { .. } => CARGO_LLVM_COV_NEXTEST_USAGE,
            Self::NextestArchive => CARGO_LLVM_COV_NEXTEST_ARCHIVE_USAGE,
            Self::Demangle => "", // internal API
        }
    }

    fn as_str(self) -> &'static str {
        match self {
            Self::None => "",
            Self::Test => "test",
            Self::Run => "run",
            Self::Report { .. } => "report",
            Self::Clean => "clean",
            Self::ShowEnv => "show-env",
            Self::Nextest { .. } => "nextest",
            Self::NextestArchive => "nextest-archive",
            Self::Demangle => "demangle",
        }
    }

    pub(crate) fn call_cargo_nextest(self) -> bool {
        matches!(self, Self::Nextest { .. } | Self::NextestArchive)
    }
    pub(crate) fn read_nextest_archive(self) -> bool {
        matches!(
            self,
            Self::Nextest { archive_file: true } | Self::Report { nextest_archive_file: true }
        )
    }
}

impl FromStr for Subcommand {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "test" | "t" => Ok(Self::Test),
            "run" | "r" => Ok(Self::Run),
            "report" => Ok(Self::Report { nextest_archive_file: false }),
            "clean" => Ok(Self::Clean),
            "show-env" => Ok(Self::ShowEnv),
            "nextest" => Ok(Self::Nextest { archive_file: false }),
            "nextest-archive" => Ok(Self::NextestArchive),
            "demangle" => Ok(Self::Demangle),
            _ => bail!("unrecognized subcommand {s}"),
        }
    }
}

#[derive(Debug, Default)]
pub(crate) struct LlvmCovOptions {
    /// Export coverage data in "json" format
    ///
    /// If --output-path is not specified, the report will be printed to stdout.
    ///
    /// This internally calls `llvm-cov export -format=text`.
    /// See <https://llvm.org/docs/CommandGuide/llvm-cov.html#llvm-cov-export> for more.
    pub(crate) json: bool,
    /// Export coverage data in "lcov" format
    ///
    /// If --output-path is not specified, the report will be printed to stdout.
    ///
    /// This internally calls `llvm-cov export -format=lcov`.
    /// See <https://llvm.org/docs/CommandGuide/llvm-cov.html#llvm-cov-export> for more.
    pub(crate) lcov: bool,

    /// Export coverage data in "cobertura" XML format
    ///
    /// If --output-path is not specified, the report will be printed to stdout.
    ///
    /// This internally calls `llvm-cov export -format=lcov` and then converts to cobertura.xml.
    /// See <https://llvm.org/docs/CommandGuide/llvm-cov.html#llvm-cov-export> for more.
    pub(crate) cobertura: bool,

    /// Export coverage data in "Codecov Custom Coverage" format
    ///
    /// If --output-path is not specified, the report will be printed to stdout.
    ///
    /// This internally calls `llvm-cov export -format=json` and then converts to codecov.json.
    /// See <https://llvm.org/docs/CommandGuide/llvm-cov.html#llvm-cov-export> for more.
    pub(crate) codecov: bool,

    /// Generate coverage report in "text" format
    ///
    /// If --output-path or --output-dir is not specified, the report will be printed to stdout.
    ///
    /// This internally calls `llvm-cov show -format=text`.
    /// See <https://llvm.org/docs/CommandGuide/llvm-cov.html#llvm-cov-show> for more.
    pub(crate) text: bool,
    /// Generate coverage report in "html" format
    ///
    /// If --output-dir is not specified, the report will be generated in `target/llvm-cov/html` directory.
    ///
    /// This internally calls `llvm-cov show -format=html`.
    /// See <https://llvm.org/docs/CommandGuide/llvm-cov.html#llvm-cov-show> for more.
    pub(crate) html: bool,
    /// Generate coverage reports in "html" format and open them in a browser after the operation.
    ///
    /// See --html for more.
    pub(crate) open: bool,

    /// Export only summary information for each file in the coverage data
    ///
    /// This flag can only be used together with --json, --lcov, --cobertura, or --codecov.
    // If the format flag is not specified, this flag is no-op because the only summary is displayed anyway.
    pub(crate) summary_only: bool,

    /// Specify a file to write coverage data into.
    ///
    /// This flag can only be used together with --json, --lcov, --cobertura, --codecov, or --text.
    /// See --output-dir for --html and --open.
    pub(crate) output_path: Option<Utf8PathBuf>,
    /// Specify a directory to write coverage report into (default to `target/llvm-cov`).
    ///
    /// This flag can only be used together with --text, --html, or --open.
    /// See also --output-path.
    // If the format flag is not specified, this flag is no-op.
    pub(crate) output_dir: Option<Utf8PathBuf>,

    /// Fail if `any` or `all` profiles cannot be merged (default to `any`)
    pub(crate) failure_mode: Option<String>,
    /// Skip source code files with file paths that match the given regular expression.
    pub(crate) ignore_filename_regex: Option<String>,
    // For debugging (unstable)
    pub(crate) disable_default_ignore_filename_regex: bool,
    /// Show instantiations in report
    pub(crate) show_instantiations: bool,
    /// Unset cfg(coverage), which is enabled when code is built using cargo-llvm-cov.
    pub(crate) no_cfg_coverage: bool,
    /// Unset cfg(coverage_nightly), which is enabled when code is built using cargo-llvm-cov and nightly compiler.
    pub(crate) no_cfg_coverage_nightly: bool,
    /// Run tests, but don't generate coverage report
    pub(crate) no_report: bool,
    /// Exit with a status of 1 if the total function coverage is less than MIN percent.
    pub(crate) fail_under_functions: Option<f64>,
    /// Exit with a status of 1 if the total line coverage is less than MIN percent.
    pub(crate) fail_under_lines: Option<f64>,
    /// Exit with a status of 1 if the total region coverage is less than MIN percent.
    pub(crate) fail_under_regions: Option<f64>,
    /// Exit with a status of 1 if the uncovered lines are greater than MAX.
    pub(crate) fail_uncovered_lines: Option<u64>,
    /// Exit with a status of 1 if the uncovered regions are greater than MAX.
    pub(crate) fail_uncovered_regions: Option<u64>,
    /// Exit with a status of 1 if the uncovered functions are greater than MAX.
    pub(crate) fail_uncovered_functions: Option<u64>,
    /// Show lines with no coverage.
    pub(crate) show_missing_lines: bool,
    /// Include build script in coverage report.
    pub(crate) include_build_script: bool,
    /// Show coverage of the specified dependency instead of the crates in the current workspace. (unstable)
    pub(crate) dep_coverage: Option<String>,
    /// Skip functions in coverage report.
    pub(crate) skip_functions: bool,
    /// Enable branch coverage. (unstable)
    pub(crate) branch: bool,
    /// Enable mcdc coverage. (unstable)
    pub(crate) mcdc: bool,
}

impl LlvmCovOptions {
    pub(crate) const fn show(&self) -> bool {
        self.text || self.html
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) enum ShowEnvFormat {
    /// Each line: key=<escaped value>, escaped using [`shell_escape::escape`].
    #[default]
    EscapedKeyValuePair,
    /// Prepend "export " to each line, so that the output is suitable to be sourced by bash.
    UnixExport,
    /// Each value: "$env:{key}={value}", where {value} is PowerShell Unicode escaped e.g. "`u{72}".
    Pwsh,
}

impl ShowEnvFormat {
    pub(crate) fn new(export_prefix: bool, with_pwsh_env_prefix: bool) -> Result<Self> {
        if export_prefix && with_pwsh_env_prefix {
            conflicts("--export-prefix", "--with-pwsh-env-prefix")?;
        }

        Ok(if export_prefix {
            ShowEnvFormat::UnixExport
        } else if with_pwsh_env_prefix {
            ShowEnvFormat::Pwsh
        } else {
            ShowEnvFormat::EscapedKeyValuePair
        })
    }

    pub(crate) fn export_string(&self, key: &str, value: &str) -> String {
        match self {
            ShowEnvFormat::EscapedKeyValuePair => {
                format!("{key}={}", shell_escape::escape(value.into()))
            }
            ShowEnvFormat::UnixExport => {
                format!("export {key}={}", shell_escape::escape(value.into()))
            }
            ShowEnvFormat::Pwsh => {
                // PowerShell 6+ expects encoded UTF-8 text. Some env vars like CARGO_ENCODED_RUSTFLAGS
                // have non-printable binary characters. We can work around this and any other escape
                // related considerations by just escaping all characters. Rust's Unicode escape is
                // of form "\u{<code>}", but PowerShell expects "`u{<code>}". A replace call fixes
                // this.
                let value = value.escape_unicode().to_string().replace('\\', "`");
                format!("$env:{key}=\"{value}\"")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct ShowEnvOptions {
    pub(crate) show_env_format: ShowEnvFormat,
}

// https://doc.rust-lang.org/nightly/cargo/commands/cargo-test.html#manifest-options
#[derive(Debug, Default)]
pub(crate) struct ManifestOptions {
    /// Path to Cargo.toml
    pub(crate) manifest_path: Option<Utf8PathBuf>,
    /// Require Cargo.lock and cache are up to date
    pub(crate) frozen: bool,
    /// Require Cargo.lock is up to date
    pub(crate) locked: bool,
    /// Run without accessing the network
    pub(crate) offline: bool,
}

impl ManifestOptions {
    pub(crate) fn cargo_args(&self, cmd: &mut ProcessBuilder) {
        // Skip --manifest-path because it is set based on Workspace::current_manifest.
        if self.frozen {
            cmd.arg("--frozen");
        }
        if self.locked {
            cmd.arg("--locked");
        }
        if self.offline {
            cmd.arg("--offline");
        }
    }
}

pub(crate) fn merge_config_to_args(
    ws: &crate::cargo::Workspace,
    target: &mut Option<String>,
    verbose: &mut u8,
    color: &mut Option<Coloring>,
) {
    // CLI flags are prefer over config values.
    if target.is_none() {
        target.clone_from(&ws.target_for_cli);
    }
    if *verbose == 0 {
        *verbose = ws.config.term.verbose.unwrap_or(false) as u8;
    }
    if color.is_none() {
        *color = ws.config.term.color.map(Into::into);
    }
}

impl Args {
    pub(crate) fn parse() -> Result<Option<Self>> {
        const SUBCMD: &str = "llvm-cov";

        // rustc/cargo args must be valid Unicode
        // https://github.com/rust-lang/rust/blob/1.84.0/compiler/rustc_driver_impl/src/args.rs#L121
        // TODO: https://github.com/rust-lang/cargo/pull/11118
        fn handle_args(
            args: impl IntoIterator<Item = impl Into<OsString>>,
        ) -> impl Iterator<Item = Result<String>> {
            args.into_iter().enumerate().map(|(i, arg)| {
                arg.into().into_string().map_err(|arg| {
                    #[allow(clippy::unnecessary_debug_formatting)]
                    {
                        format_err!("argument {} is not valid Unicode: {arg:?}", i + 1)
                    }
                })
            })
        }

        let mut raw_args = handle_args(env::args_os());
        raw_args.next(); // cargo
        match raw_args.next().transpose()? {
            Some(arg) if arg == SUBCMD => {}
            Some(arg) => bail!("expected subcommand '{SUBCMD}', found argument '{arg}'"),
            None => bail!("expected subcommand '{SUBCMD}'"),
        }
        let mut args = vec![];
        for arg in &mut raw_args {
            let arg = arg?;
            if arg == "--" {
                break;
            }
            args.push(arg);
        }
        let rest = raw_args.collect::<Result<Vec<_>>>()?;

        let mut cargo_args = vec![];
        let mut subcommand = Subcommand::None;
        let mut after_subcommand = false;

        let mut manifest_path = None;
        let mut frozen = false;
        let mut locked = false;
        let mut offline = false;
        let mut color = None;

        let mut doctests = false;
        let mut no_run = false;
        let mut no_fail_fast = false;
        let mut ignore_run_fail = false;
        let mut lib = false;
        let mut bin = vec![];
        let mut bins = false;
        let mut example = vec![];
        let mut examples = false;
        let mut test = vec![];
        let mut tests = false;
        let mut bench = vec![];
        let mut benches = false;
        let mut all_targets = false;
        let mut doc = false;

        let mut package: Vec<String> = vec![];
        let mut workspace = false;
        let mut exclude = vec![];
        let mut exclude_from_test = vec![];
        let mut exclude_from_report = vec![];

        // llvm-cov options
        let mut json = false;
        let mut lcov = false;
        let mut cobertura = false;
        let mut codecov = false;
        let mut text = false;
        let mut html = false;
        let mut open = false;
        let mut summary_only = false;
        let mut output_path = None;
        let mut output_dir = None;
        let mut failure_mode = None;
        let mut ignore_filename_regex = None;
        let mut disable_default_ignore_filename_regex = false;
        let mut show_instantiations = false;
        let mut no_cfg_coverage = false;
        let mut no_cfg_coverage_nightly = false;
        let mut no_report = false;
        let mut fail_under_functions = None;
        let mut fail_under_lines = None;
        let mut fail_under_regions = None;
        let mut fail_uncovered_lines = None;
        let mut fail_uncovered_regions = None;
        let mut fail_uncovered_functions = None;
        let mut show_missing_lines = false;
        let mut include_build_script = false;
        let mut dep_coverage = None;
        let mut skip_functions = false;
        let mut branch = false;
        let mut mcdc = false;

        // build options
        let mut release = false;
        let mut target = None;
        let mut coverage_target_only = false;
        let mut remap_path_prefix = false;
        let mut include_ffi = false;
        let mut verbose: usize = 0;
        let mut no_clean = false;

        // clean options
        let mut profraw_only = false;

        // show-env options
        let mut export_prefix = false;
        let mut with_pwsh_env_prefix = false;

        // options ambiguous between nextest-related and others
        let mut profile = None;
        let mut cargo_profile = None;
        let mut archive_file = None;
        let mut nextest_archive_file = None;

        let mut parser = lexopt::Parser::from_args(args.clone());
        while let Some(arg) = parser.next()? {
            macro_rules! parse_opt {
                ($opt:tt $(,)?) => {{
                    if Store::is_full(&$opt) {
                        multi_arg(&arg)?;
                    }
                    Store::push(&mut $opt, &parser.value()?.into_string().unwrap())?;
                    after_subcommand = false;
                }};
            }
            macro_rules! parse_opt_passthrough {
                ($opt:tt $(,)?) => {{
                    if Store::is_full(&$opt) {
                        multi_arg(&arg)?;
                    }
                    match arg {
                        Long(flag) => {
                            let flag = format!("--{}", flag);
                            if let Some(val) = parser.optional_value() {
                                let val = val.into_string().unwrap();
                                Store::push(&mut $opt, &val)?;
                                cargo_args.push(format!("{}={}", flag, val));
                            } else {
                                let val = parser.value()?.into_string().unwrap();
                                Store::push(&mut $opt, &val)?;
                                cargo_args.push(flag);
                                cargo_args.push(val);
                            }
                        }
                        Short(flag) => {
                            if let Some(val) = parser.optional_value() {
                                let val = val.into_string().unwrap();
                                Store::push(&mut $opt, &val)?;
                                cargo_args.push(format!("-{}{}", flag, val));
                            } else {
                                let val = parser.value()?.into_string().unwrap();
                                Store::push(&mut $opt, &val)?;
                                cargo_args.push(format!("-{}", flag));
                                cargo_args.push(val);
                            }
                        }
                        Value(_) => unreachable!(),
                    }
                    after_subcommand = false;
                }};
            }
            macro_rules! parse_flag {
                ($flag:ident $(,)?) => {{
                    if mem::replace(&mut $flag, true) {
                        multi_arg(&arg)?;
                    }
                    #[allow(unused_assignments)]
                    {
                        after_subcommand = false;
                    }
                }};
            }
            macro_rules! parse_flag_passthrough {
                ($flag:ident $(,)?) => {{
                    parse_flag!($flag);
                    passthrough!();
                }};
            }
            macro_rules! passthrough {
                () => {{
                    match arg {
                        Long(flag) => {
                            let flag = format!("--{}", flag);
                            if let Some(val) = parser.optional_value() {
                                cargo_args.push(format!("{}={}", flag, val.string()?));
                            } else {
                                cargo_args.push(flag);
                            }
                        }
                        Short(flag) => {
                            if let Some(val) = parser.optional_value() {
                                cargo_args.push(format!("-{}{}", flag, val.string()?));
                            } else {
                                cargo_args.push(format!("-{}", flag));
                            }
                        }
                        Value(_) => unreachable!(),
                    }
                    after_subcommand = false;
                }};
            }

            match arg {
                Long("color") => parse_opt_passthrough!(color),
                Long("manifest-path") => parse_opt!(manifest_path),
                Long("frozen") => parse_flag_passthrough!(frozen),
                Long("locked") => parse_flag_passthrough!(locked),
                Long("offline") => parse_flag_passthrough!(offline),

                Long("doctests") => parse_flag!(doctests),
                Long("ignore-run-fail") => parse_flag!(ignore_run_fail),
                Long("no-run") => parse_flag!(no_run),
                Long("no-fail-fast") => parse_flag_passthrough!(no_fail_fast),

                Long("lib") => parse_flag_passthrough!(lib),
                Long("bin") => parse_opt_passthrough!(bin),
                Long("bins") => parse_flag_passthrough!(bins),
                Long("example") => parse_opt_passthrough!(example),
                Long("examples") => parse_flag_passthrough!(examples),
                Long("test") => parse_opt_passthrough!(test),
                Long("tests") => parse_flag_passthrough!(tests),
                Long("bench") => parse_opt_passthrough!(bench),
                Long("benches") => parse_flag_passthrough!(benches),
                Long("all-targets") => parse_flag_passthrough!(all_targets),
                Long("doc") => parse_flag_passthrough!(doc),

                Short('p') | Long("package") => parse_opt_passthrough!(package),
                Long("workspace" | "all") => parse_flag_passthrough!(workspace),
                Long("exclude") => parse_opt_passthrough!(exclude),
                Long("exclude-from-test") => parse_opt!(exclude_from_test),
                Long("exclude-from-report") => parse_opt!(exclude_from_report),

                // build options
                Short('r') | Long("release") => parse_flag!(release),
                // ambiguous between nextest-related and others will be handled later
                Long("profile") => parse_opt!(profile),
                Long("cargo-profile") => parse_opt!(cargo_profile),
                Long("target") => parse_opt!(target),
                Long("coverage-target-only") => parse_flag!(coverage_target_only),
                Long("remap-path-prefix") => parse_flag!(remap_path_prefix),
                Long("include-ffi") => parse_flag!(include_ffi),
                Long("no-clean") => parse_flag!(no_clean),

                // clean options
                Long("profraw-only") => parse_flag!(profraw_only),

                // report options
                Long("json") => parse_flag!(json),
                Long("lcov") => parse_flag!(lcov),
                Long("cobertura") => parse_flag!(cobertura),
                Long("codecov") => parse_flag!(codecov),
                Long("text") => parse_flag!(text),
                Long("html") => parse_flag!(html),
                Long("open") => parse_flag!(open),
                Long("summary-only") => parse_flag!(summary_only),
                Long("skip-functions") => parse_flag!(skip_functions),
                Long("branch") => parse_flag!(branch),
                Long("mcdc") => parse_flag!(mcdc),
                Long("output-path") => parse_opt!(output_path),
                Long("output-dir") => parse_opt!(output_dir),
                Long("failure-mode") => parse_opt!(failure_mode),
                Long("ignore-filename-regex") => parse_opt!(ignore_filename_regex),
                Long("disable-default-ignore-filename-regex") => {
                    parse_flag!(disable_default_ignore_filename_regex);
                }
                Long("show-instantiations") => parse_flag!(show_instantiations),
                Long("hide-instantiations") => {
                    // The following warning is a hint, so it should not be promoted to an error.
                    let _guard = term::warn::ignore();
                    warn!("--hide-instantiations is now enabled by default");
                }
                Long("no-cfg-coverage") => parse_flag!(no_cfg_coverage),
                Long("no-cfg-coverage-nightly") => parse_flag!(no_cfg_coverage_nightly),
                Long("no-report") => parse_flag!(no_report),
                Long("fail-under-functions") => parse_opt!(fail_under_functions),
                Long("fail-under-lines") => parse_opt!(fail_under_lines),
                Long("fail-under-regions") => parse_opt!(fail_under_regions),
                Long("fail-uncovered-lines") => parse_opt!(fail_uncovered_lines),
                Long("fail-uncovered-regions") => parse_opt!(fail_uncovered_regions),
                Long("fail-uncovered-functions") => parse_opt!(fail_uncovered_functions),
                Long("show-missing-lines") => parse_flag!(show_missing_lines),
                Long("include-build-script") => parse_flag!(include_build_script),
                Long("dep-coverage") => parse_opt!(dep_coverage),

                // show-env options
                Long("export-prefix") => parse_flag!(export_prefix),
                Long("with-pwsh-env-prefix") => parse_flag!(with_pwsh_env_prefix),

                // ambiguous between nextest-related and others will be handled later
                Long("archive-file") => parse_opt_passthrough!(archive_file),
                Long("nextest-archive-file") => parse_opt!(nextest_archive_file),

                Short('v') | Long("verbose") => {
                    verbose += 1;
                    after_subcommand = false;
                }
                Short('h') | Long("help") => {
                    print!("{}", Subcommand::help_text(subcommand));
                    return Ok(None);
                }
                Short('V') | Long("version") => {
                    if subcommand == Subcommand::None {
                        println!("{} {}", env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"));
                        return Ok(None);
                    }
                    unexpected("--version", subcommand)?;
                }

                // TODO: Currently, we are using a subdirectory of the target directory as
                //       the actual target directory. What effect should this option have
                //       on its behavior?
                Long("target-dir") => unexpected(&format_arg(&arg), subcommand)?,

                // Handle known options for can_passthrough=false subcommands
                Short('Z') => parse_opt_passthrough!(()),
                Short('F' | 'j') | Long("features" | "jobs")
                    if matches!(
                        subcommand,
                        Subcommand::None
                            | Subcommand::Test
                            | Subcommand::Run
                            | Subcommand::Nextest { .. }
                            | Subcommand::NextestArchive
                    ) =>
                {
                    parse_opt_passthrough!(());
                }
                Short('q') | Long("quiet") => passthrough!(),
                Long(
                    "all-features"
                    | "no-default-features"
                    | "--keep-going"
                    | "--ignore-rust-version",
                ) if matches!(
                    subcommand,
                    Subcommand::None
                        | Subcommand::Test
                        | Subcommand::Run
                        | Subcommand::Nextest { .. }
                        | Subcommand::NextestArchive
                ) =>
                {
                    passthrough!();
                }

                // passthrough
                Long(_) | Short(_) if Subcommand::can_passthrough(subcommand) => passthrough!(),
                Value(val)
                    if subcommand == Subcommand::None
                        || Subcommand::can_passthrough(subcommand) =>
                {
                    let val = val.into_string().unwrap();
                    if subcommand == Subcommand::None {
                        subcommand = val.parse::<Subcommand>()?;
                        if subcommand == Subcommand::Demangle && args.len() != 1 {
                            unexpected(
                                args.iter().find(|&arg| arg != "demangle").unwrap(),
                                subcommand,
                            )?;
                        }
                        after_subcommand = true;
                    } else {
                        if after_subcommand
                            && matches!(subcommand, Subcommand::Nextest { .. })
                            && matches!(
                                val.as_str(),
                                // from `cargo nextest --help`
                                "list" | "run" | "archive" | "show-config" | "self" | "help"
                            )
                        {
                            // The following warning is a hint, so it should not be promoted to an error.
                            let _guard = term::warn::ignore();
                            warn!(
                                "note that `{val}` is treated as test filter instead of subcommand \
                                 because `cargo llvm-cov nextest` internally calls \
                                 `cargo nextest run`; if you want to use `nextest archive`, \
                                 please use `cargo llvm-cov nextest-archive`"
                            );
                        }
                        cargo_args.push(val);
                        after_subcommand = false;
                    }
                }
                _ => unexpected(&format_arg(&arg), subcommand)?,
            }
        }

        term::set_coloring(&mut color);

        // unexpected options
        let show_env_format = match subcommand {
            Subcommand::ShowEnv => ShowEnvFormat::new(export_prefix, with_pwsh_env_prefix)?,
            _ => {
                if export_prefix {
                    unexpected("--export-prefix", subcommand)?;
                }
                if with_pwsh_env_prefix {
                    unexpected("--with-pwsh-env-prefix", subcommand)?;
                }
                ShowEnvFormat::default()
            }
        };
        if doc || doctests {
            let flag = if doc { "--doc" } else { "--doctests" };
            match subcommand {
                Subcommand::None | Subcommand::Test => {}
                Subcommand::ShowEnv | Subcommand::Report { .. } if doctests => {}
                Subcommand::Nextest { .. } | Subcommand::NextestArchive => {
                    bail!("doctest is not supported for nextest")
                }
                _ => unexpected(flag, subcommand)?,
            }
        }
        match subcommand {
            Subcommand::None | Subcommand::Nextest { .. } | Subcommand::NextestArchive => {}
            Subcommand::Test => {
                if no_run {
                    unexpected("--no-run", subcommand)?;
                }
            }
            _ => {
                if lib {
                    unexpected("--lib", subcommand)?;
                }
                if bins {
                    unexpected("--bins", subcommand)?;
                }
                if examples {
                    unexpected("--examples", subcommand)?;
                }
                if !test.is_empty() {
                    unexpected("--test", subcommand)?;
                }
                if tests {
                    unexpected("--tests", subcommand)?;
                }
                if !bench.is_empty() {
                    unexpected("--bench", subcommand)?;
                }
                if benches {
                    unexpected("--benches", subcommand)?;
                }
                if all_targets {
                    unexpected("--all-targets", subcommand)?;
                }
                if no_run {
                    unexpected("--no-run", subcommand)?;
                }
                if no_fail_fast {
                    unexpected("--no-fail-fast", subcommand)?;
                }
                if !exclude.is_empty() {
                    unexpected("--exclude", subcommand)?;
                }
                if !exclude_from_test.is_empty() {
                    unexpected("--exclude-from-test", subcommand)?;
                }
            }
        }
        match subcommand {
            Subcommand::None
            | Subcommand::Test
            | Subcommand::Run
            | Subcommand::Nextest { .. }
            | Subcommand::NextestArchive => {}
            _ => {
                if !bin.is_empty() {
                    unexpected("--bin", subcommand)?;
                }
                if !example.is_empty() {
                    unexpected("--example", subcommand)?;
                }
                if !exclude_from_report.is_empty() {
                    unexpected("--exclude-from-report", subcommand)?;
                }
                if no_report {
                    unexpected("--no-report", subcommand)?;
                }
                if no_clean {
                    unexpected("--no-clean", subcommand)?;
                }
                if ignore_run_fail {
                    unexpected("--ignore-run-fail", subcommand)?;
                }
            }
        }
        match subcommand {
            Subcommand::None
            | Subcommand::Test
            | Subcommand::Run
            | Subcommand::Nextest { .. }
            | Subcommand::NextestArchive
            | Subcommand::ShowEnv => {}
            _ => {
                if no_cfg_coverage {
                    unexpected("--no-cfg-coverage", subcommand)?;
                }
                if no_cfg_coverage_nightly {
                    unexpected("--no-cfg-coverage-nightly", subcommand)?;
                }
            }
        }
        match subcommand {
            Subcommand::None
            | Subcommand::Test
            | Subcommand::Nextest { .. }
            | Subcommand::NextestArchive
            | Subcommand::Clean => {}
            _ => {
                if workspace {
                    unexpected("--workspace", subcommand)?;
                }
            }
        }
        // TODO: check more

        // requires
        if !workspace {
            // TODO: This is the same behavior as cargo, but should we allow it to be used
            // in the root of a virtual workspace as well?
            if !exclude.is_empty() {
                requires("--exclude", &["--workspace"])?;
            }
            if !exclude_from_test.is_empty() {
                requires("--exclude-from-test", &["--workspace"])?;
            }
        }
        if coverage_target_only && target.is_none() {
            requires("--coverage-target-only", &["--target"])?;
        }

        // conflicts
        if no_report && no_run {
            conflicts("--no-report", "--no-run")?;
        }
        if no_report || no_run {
            let flag = if no_report { "--no-report" } else { "--no-run" };
            if no_clean {
                // --no-report/--no-run implicitly enable --no-clean.
                conflicts(flag, "--no-clean")?;
            }
        }
        if ignore_run_fail && no_fail_fast {
            // --ignore-run-fail implicitly enable --no-fail-fast.
            conflicts("--ignore-run-fail", "--no-fail-fast")?;
        }
        if doc || doctests {
            let flag = if doc { "--doc" } else { "--doctests" };
            if lib {
                conflicts(flag, "--lib")?;
            }
            if !bin.is_empty() {
                conflicts(flag, "--bin")?;
            }
            if bins {
                conflicts(flag, "--bins")?;
            }
            if !example.is_empty() {
                conflicts(flag, "--example")?;
            }
            if examples {
                conflicts(flag, "--examples")?;
            }
            if !test.is_empty() {
                conflicts(flag, "--test")?;
            }
            if tests {
                conflicts(flag, "--tests")?;
            }
            if !bench.is_empty() {
                conflicts(flag, "--bench")?;
            }
            if benches {
                conflicts(flag, "--benches")?;
            }
            if all_targets {
                conflicts(flag, "--all-targets")?;
            }
        }
        if !package.is_empty() && workspace {
            // cargo allows the combination of --package and --workspace, but
            // we reject it because the situation where both flags are specified is odd.
            conflicts("--package", "--workspace")?;
        }
        // TODO: handle these mutual exclusions elegantly.
        if lcov {
            let flag = "--lcov";
            if json {
                conflicts(flag, "--json")?;
            }
        }
        if cobertura {
            let flag = "--cobertura";
            if json {
                conflicts(flag, "--json")?;
            }
            if lcov {
                conflicts(flag, "--lcov")?;
            }
            if codecov {
                conflicts(flag, "--codecov")?;
            }
        }
        if codecov {
            let flag = "--codecov";
            if json {
                conflicts(flag, "--json")?;
            }
            if lcov {
                conflicts(flag, "--lcov")?;
            }
            if cobertura {
                conflicts(flag, "--cobertura")?;
            }
        }
        if text {
            let flag = "--text";
            if json {
                conflicts(flag, "--json")?;
            }
            if lcov {
                conflicts(flag, "--lcov")?;
            }
            if cobertura {
                conflicts(flag, "--cobertura")?;
            }
            if codecov {
                conflicts(flag, "--codecov")?;
            }
        }
        if html || open {
            let flag = if html { "--html" } else { "--open" };
            if json {
                conflicts(flag, "--json")?;
            }
            if lcov {
                conflicts(flag, "--lcov")?;
            }
            if cobertura {
                conflicts(flag, "--cobertura")?;
            }
            if codecov {
                conflicts(flag, "--codecov")?;
            }
            if text {
                conflicts(flag, "--text")?;
            }
        }
        if summary_only || output_path.is_some() {
            let flag = if summary_only { "--summary-only" } else { "--output-path" };
            if html {
                conflicts(flag, "--html")?;
            }
            if open {
                conflicts(flag, "--open")?;
            }
        }
        if skip_functions {
            let flag = "--skip-functions";
            if html {
                conflicts(flag, "--html")?;
            }
        }
        if output_dir.is_some() {
            let flag = "--output-dir";
            if json {
                conflicts(flag, "--json")?;
            }
            if lcov {
                conflicts(flag, "--lcov")?;
            }
            if cobertura {
                conflicts(flag, "--cobertura")?;
            }
            if codecov {
                conflicts(flag, "--codecov")?;
            }
            if output_path.is_some() {
                conflicts(flag, "--output-path")?;
            }
        }

        // forbid_empty_values
        if ignore_filename_regex.as_deref() == Some("") {
            bail!("empty string is not allowed in --ignore-filename-regex")
        }
        if output_path.as_deref() == Some(Utf8Path::new("")) {
            bail!("empty string is not allowed in --output-path")
        }
        if output_dir.as_deref() == Some(Utf8Path::new("")) {
            bail!("empty string is not allowed in --output-dir")
        }

        if no_run {
            // The following warnings should not be promoted to an error.
            let _guard = term::warn::ignore();
            warn!("--no-run is deprecated, use `cargo llvm-cov report` subcommand instead");
        }

        // If `-vv` is passed, propagate `-v` to cargo.
        if verbose > 1 {
            cargo_args.push(format!("-{}", "v".repeat(verbose - 1)));
        }

        // For subsequent processing
        if no_report || no_run {
            // --no-report and --no-run implies --no-clean
            no_clean = true;
        }
        if doc {
            // --doc implies --doctests
            doctests = true;
        }
        if no_run {
            // --no-run is deprecated alias for report
            subcommand = Subcommand::Report { nextest_archive_file: false };
        }

        if profraw_only && !matches!(subcommand, Subcommand::Clean) {
            bail!(
                "'--profraw-only' is clean-specific option and not supported for this subcommand"
            );
        }

        // nextest-related
        if subcommand.call_cargo_nextest() {
            if let Some(profile) = profile {
                // nextest profile will be propagated
                cargo_args.push("--profile".to_owned());
                cargo_args.push(profile);
            }
            if nextest_archive_file.is_some() {
                bail!(
                    "'--nextest-archive-file' is report-specific option; did you mean '--archive-file'?"
                );
            }
            nextest_archive_file = archive_file;
            if let Subcommand::Nextest { archive_file: f } = &mut subcommand {
                *f = nextest_archive_file.is_some();
            }
        } else {
            if cargo_profile.is_some() {
                bail!("'--cargo-profile' is nextest-specific option; did you mean '--profile'?");
            }
            cargo_profile = profile;
            if let Subcommand::Report { nextest_archive_file: f } = &mut subcommand {
                if archive_file.is_some() {
                    bail!(
                        "'--archive-file' is nextest-specific option; did you mean '--nextest-archive-file'?"
                    );
                }
                *f = nextest_archive_file.is_some();
            } else {
                if archive_file.is_some() {
                    bail!(
                        "'--archive-file' is nextest-specific option and not supported for this subcommand"
                    );
                }
                if nextest_archive_file.is_some() {
                    bail!(
                        "'--nextest-archive-file' is report-specific option and not supported for this subcommand"
                    );
                }
            }
        }

        Ok(Some(Self {
            subcommand,
            cov: LlvmCovOptions {
                json,
                lcov,
                cobertura,
                codecov,
                text,
                html,
                open,
                summary_only,
                output_path,
                output_dir,
                failure_mode,
                ignore_filename_regex,
                disable_default_ignore_filename_regex,
                show_instantiations,
                no_cfg_coverage,
                no_cfg_coverage_nightly,
                no_report,
                fail_under_functions,
                fail_under_lines,
                fail_under_regions,
                fail_uncovered_lines,
                fail_uncovered_regions,
                fail_uncovered_functions,
                show_missing_lines,
                include_build_script,
                dep_coverage,
                skip_functions,
                branch,
                mcdc,
            },
            show_env: ShowEnvOptions { show_env_format },
            doctests,
            ignore_run_fail,
            lib,
            bin,
            bins,
            example,
            examples,
            test,
            tests,
            bench,
            benches,
            all_targets,
            doc,
            workspace,
            exclude,
            exclude_from_test,
            exclude_from_report,
            release,
            cargo_profile,
            target,
            coverage_target_only,
            verbose: verbose.try_into().unwrap_or(u8::MAX),
            color,
            remap_path_prefix,
            include_ffi,
            no_clean,
            profraw_only,
            manifest: ManifestOptions { manifest_path, frozen, locked, offline },
            nextest_archive_file,
            cargo_args,
            rest,
        }))
    }
}

trait Store<T> {
    fn is_full(&self) -> bool {
        false
    }
    fn push(&mut self, val: &str) -> Result<()>;
}
impl Store<OsString> for () {
    fn push(&mut self, _: &str) -> Result<()> {
        Ok(())
    }
}
impl<T: FromStr> Store<T> for Option<T>
where
    Error: From<T::Err>,
{
    fn is_full(&self) -> bool {
        self.is_some()
    }
    fn push(&mut self, val: &str) -> Result<()> {
        *self = Some(val.parse()?);
        Ok(())
    }
}
impl<T: FromStr> Store<T> for Vec<T>
where
    Error: From<T::Err>,
{
    fn push(&mut self, val: &str) -> Result<()> {
        self.push(val.parse()?);
        Ok(())
    }
}

fn format_arg(arg: &lexopt::Arg<'_>) -> String {
    match arg {
        Long(flag) => format!("--{flag}"),
        Short(flag) => format!("-{flag}"),
        Value(val) => val.parse().unwrap(),
    }
}

#[cold]
#[inline(never)]
fn multi_arg(flag: &lexopt::Arg<'_>) -> Result<()> {
    let flag = &format_arg(flag);
    bail!("the argument '{flag}' was provided more than once, but cannot be used multiple times");
}

// `flag` requires one of `requires`.
#[cold]
#[inline(never)]
fn requires(flag: &str, requires: &[&str]) -> Result<()> {
    let with = match requires.len() {
        0 => unreachable!(),
        1 => requires[0].to_owned(),
        2 => format!("either {} or {}", requires[0], requires[1]),
        _ => {
            let mut with = String::new();
            for f in requires.iter().take(requires.len() - 1) {
                with += f;
                with += ", ";
            }
            with += "or ";
            with += requires.last().unwrap();
            with
        }
    };
    bail!("{flag} can only be used together with {with}");
}

#[cold]
#[inline(never)]
fn conflicts(a: &str, b: &str) -> Result<()> {
    bail!("{a} may not be used together with {b}");
}

#[cold]
#[inline(never)]
fn unexpected(arg: &str, subcommand: Subcommand) -> Result<()> {
    if arg.starts_with('-') && !arg.starts_with("---") && arg != "--" {
        if subcommand == Subcommand::None {
            bail!("invalid option '{arg}'");
        }
        bail!("invalid option '{arg}' for subcommand '{}'", subcommand.as_str());
    }
    Err(lexopt::Error::UnexpectedArgument(arg.into()).into())
}
