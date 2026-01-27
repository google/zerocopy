// SPDX-License-Identifier: Apache-2.0 OR MIT

#![forbid(unsafe_code)]

// Refs:
// - https://doc.rust-lang.org/nightly/rustc/instrument-coverage.html
// - https://llvm.org/docs/CommandGuide/llvm-profdata.html
// - https://llvm.org/docs/CommandGuide/llvm-cov.html

use std::{
    collections::{BTreeSet, HashMap},
    ffi::{OsStr, OsString},
    fmt::Write as _,
    io::{self, BufRead as _, BufWriter, Read as _, Write as _},
    path::Path,
    process::ExitCode,
    time::SystemTime,
};

use anyhow::{Context as _, Result, bail};
use camino::{Utf8Path, Utf8PathBuf};
use cargo_config2::Flags;
use cargo_llvm_cov::json::{CodeCovJsonExport, CoverageKind, LlvmCovJsonExport};
use regex::Regex;
use serde_derive::Deserialize;
use tar::Archive;
use walkdir::WalkDir;

use crate::{
    cargo::Workspace,
    cli::{Args, ShowEnvOptions, Subcommand},
    context::Context,
    metadata::Metadata,
    process::ProcessBuilder,
    regex_vec::{RegexVec, RegexVecBuilder},
    term::Coloring,
};

#[macro_use]
mod term;

#[macro_use]
mod process;

mod cargo;
mod clean;
mod cli;
mod context;
mod env;
mod fs;
mod metadata;
mod regex_vec;

fn main() -> ExitCode {
    term::init_coloring();
    if let Err(e) = try_main() {
        error!("{e:#}");
    }
    if term::error() || term::warn() && env::var_os("CARGO_LLVM_COV_DENY_WARNINGS").is_some() {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

fn try_main() -> Result<()> {
    let Some(mut args) = Args::parse()? else { return Ok(()) };
    term::verbose::set(args.verbose != 0);

    match args.subcommand {
        Subcommand::Demangle => {
            let mut stdout = BufWriter::new(io::stdout().lock()); // Buffered because it is written many times.
            rustc_demangle::demangle_stream(&mut io::stdin().lock(), &mut stdout, false)?;
            stdout.flush()?;
        }
        Subcommand::Clean => clean::run(&mut args)?,
        Subcommand::ShowEnv => {
            let cx = &Context::new(args)?;
            let writer = &mut ShowEnvWriter {
                writer: BufWriter::new(io::stdout().lock()), // Buffered because it is written with newline many times.
                options: cx.args.show_env.clone(),
            };
            set_env(cx, writer, IsNextest(true))?; // Include envs for nextest.
            writer.set("CARGO_LLVM_COV_TARGET_DIR", cx.ws.metadata.target_directory.as_str())?;
            writer.set("CARGO_LLVM_COV_BUILD_DIR", cx.ws.metadata.build_directory().as_str())?;
            writer.writer.flush()?;
        }
        Subcommand::Report { .. } => {
            let cx = &Context::new(args)?;
            create_dirs(cx)?;
            generate_report(cx)?;
        }
        Subcommand::Run => {
            let cx = &Context::new(args)?;
            clean::clean_partial(cx)?;
            create_dirs(cx)?;
            run_run(cx)?;
            if !cx.args.cov.no_report {
                generate_report(cx)?;
            }
        }
        Subcommand::Nextest { .. } => {
            let cx = &Context::new(args)?;
            clean::clean_partial(cx)?;
            create_dirs(cx)?;
            run_nextest(cx)?;
            if !cx.args.cov.no_report {
                generate_report(cx)?;
            }
        }
        Subcommand::NextestArchive => {
            let cx = &Context::new(args)?;
            clean::clean_partial(cx)?;
            create_dirs(cx)?;
            archive_nextest(cx)?;
        }
        Subcommand::None | Subcommand::Test => {
            let cx = &Context::new(args)?;
            clean::clean_partial(cx)?;
            create_dirs(cx)?;
            run_test(cx)?;
            if !cx.args.cov.no_report {
                generate_report(cx)?;
            }
        }
    }
    Ok(())
}

fn create_dirs(cx: &Context) -> Result<()> {
    fs::create_dir_all(&cx.ws.target_dir)?;

    if let Some(output_dir) = &cx.args.cov.output_dir {
        fs::create_dir_all(output_dir)?;
        if cx.args.cov.html {
            fs::create_dir_all(output_dir.join("html"))?;
        }
        if cx.args.cov.text {
            fs::create_dir_all(output_dir.join("text"))?;
        }
    }

    if cx.args.doctests {
        fs::create_dir_all(&cx.ws.doctests_dir)?;
    }
    Ok(())
}

trait EnvTarget {
    fn set(&mut self, key: &str, value: &str) -> Result<()>;
    fn unset(&mut self, key: &str) -> Result<()>;
}

impl EnvTarget for ProcessBuilder {
    fn set(&mut self, key: &str, value: &str) -> Result<()> {
        self.env(key, value);
        Ok(())
    }
    fn unset(&mut self, key: &str) -> Result<()> {
        self.env_remove(key);
        Ok(())
    }
}

struct ShowEnvWriter<W: io::Write> {
    writer: W,
    options: ShowEnvOptions,
}

impl<W: io::Write> EnvTarget for ShowEnvWriter<W> {
    fn set(&mut self, key: &str, value: &str) -> Result<()> {
        writeln!(self.writer, "{}", self.options.show_env_format.export_string(key, value))
            .context("failed to write env to stdout")
    }
    fn unset(&mut self, key: &str) -> Result<()> {
        if env::var_os(key).is_some() {
            warn!("cannot unset environment variable `{key}`");
        }
        Ok(())
    }
}

struct IsNextest(bool);

fn set_env(cx: &Context, env: &mut dyn EnvTarget, IsNextest(is_nextest): IsNextest) -> Result<()> {
    fn push_common_flags(cx: &Context, flags: &mut Flags) {
        if cx.ws.stable_coverage {
            flags.push("-C");
            // TODO: if user already set -C instrument-coverage=..., respect it
            // https://doc.rust-lang.org/rustc/instrument-coverage.html#-c-instrument-coverageoptions
            flags.push("instrument-coverage");
        } else {
            flags.push("-Z");
            flags.push("instrument-coverage");
            if cx.ws.target_for_config.triple().contains("-windows") {
                // `-C codegen-units=1` is needed to work around link error on windows
                // https://github.com/rust-lang/rust/issues/85461
                // https://github.com/microsoft/windows-rs/issues/1006#issuecomment-887789950
                // This has been fixed in https://github.com/rust-lang/rust/pull/91470,
                // but old nightly compilers still need this.
                flags.push("-C");
                flags.push("codegen-units=1");
            }
        }
        if cx.args.cov.mcdc {
            // Tracking issue: https://github.com/rust-lang/rust/issues/124144
            // TODO: Unstable MC/DC support has been removed in https://github.com/rust-lang/rust/pull/144999
            flags.push("-Z");
            flags.push("coverage-options=mcdc");
        } else if cx.args.cov.branch {
            // Tracking issue: https://github.com/rust-lang/rust/issues/79649
            flags.push("-Z");
            flags.push("coverage-options=branch");
        }
        // Workaround for https://github.com/rust-lang/rust/issues/91092.
        // Unnecessary since https://github.com/rust-lang/rust/pull/111469.
        let needs_atomic_counter_workaround = if cx.ws.rustc_version.nightly {
            cx.ws.rustc_version.major_minor() <= (1, 71)
        } else {
            cx.ws.rustc_version.major_minor() < (1, 71)
        };
        if needs_atomic_counter_workaround {
            flags.push("-C");
            flags.push("llvm-args=--instrprof-atomic-counter-update-all");
        }
        if !cx.args.cov.no_cfg_coverage {
            flags.push("--cfg=coverage");
        }
        if cx.ws.rustc_version.nightly && !cx.args.cov.no_cfg_coverage_nightly {
            flags.push("--cfg=coverage_nightly");
        }
        if cx.ws.target_for_config.triple().ends_with("-windows-gnullvm") {
            // https://github.com/taiki-e/cargo-llvm-cov/issues/254#issuecomment-3700090953
            flags.push("-C");
            flags.push("link-arg=-Wl,--no-gc-sections");
        }
    }

    let llvm_profile_file_name =
        if let Some(llvm_profile_file_name) = env::var("LLVM_PROFILE_FILE_NAME")? {
            if !llvm_profile_file_name.ends_with(".profraw") {
                bail!("extension of LLVM_PROFILE_FILE_NAME must be 'profraw'");
            }
            llvm_profile_file_name
        } else {
            // TODO: remove %p (for nextest?) by default? https://github.com/taiki-e/cargo-llvm-cov/issues/335#issuecomment-1890349373
            let mut llvm_profile_file_name = format!("{}-%p", cx.ws.name);
            if is_nextest {
                // https://github.com/taiki-e/cargo-llvm-cov/issues/258
                // https://clang.llvm.org/docs/SourceBasedCodeCoverage.html#running-the-instrumented-program
                // Select the number of threads that is the same as the one nextest uses by default here.
                // https://github.com/nextest-rs/nextest/blob/c54694dfe7be016993983b5dedbcf2b50d4b1a6e/nextest-runner/src/config/test_threads.rs
                // https://github.com/nextest-rs/nextest/blob/c54694dfe7be016993983b5dedbcf2b50d4b1a6e/nextest-runner/src/config/config_impl.rs#L30
                // TODO: should we respect custom test-threads?
                // - If the number of threads specified by the user is negative or
                //   less or equal to available cores, it should not really be a problem
                //   because it does not exceed the number of available cores.
                // - Even if the number of threads specified by the user is greater than
                //   available cores, it is expected that the number of threads that can
                //   write simultaneously will not exceed the number of available cores.
                let _ = write!(
                    llvm_profile_file_name,
                    "-%{}m",
                    // TODO: clamp to 1..=9?
                    // https://doc.rust-lang.org/rustc/instrument-coverage.html#running-the-instrumented-binary-to-generate-raw-coverage-profiling-data
                    // > N must be between 1 and 9
                    std::thread::available_parallelism().map_or(1, usize::from)
                );
            } else {
                llvm_profile_file_name.push_str("-%m");
            }
            llvm_profile_file_name.push_str(".profraw");
            llvm_profile_file_name
        };
    let llvm_profile_file = cx.ws.target_dir.join(llvm_profile_file_name);

    let rustflags = &mut cx.ws.config.rustflags(&cx.ws.target_for_config)?.unwrap_or_default();
    push_common_flags(cx, rustflags);
    if cx.args.remap_path_prefix {
        rustflags.push("--remap-path-prefix");
        rustflags.push(format!("{}/=", cx.ws.metadata.workspace_root));
    }
    if cx.args.target.is_none() {
        // https://github.com/dtolnay/trybuild/pull/121
        // https://github.com/dtolnay/trybuild/issues/122
        // https://github.com/dtolnay/trybuild/pull/123
        rustflags.push("--cfg=trybuild_no_target");
    }

    // https://doc.rust-lang.org/nightly/rustc/instrument-coverage.html#including-doc-tests
    let rustdocflags = &mut cx.ws.config.rustdocflags(&cx.ws.target_for_config)?;
    if cx.args.doctests {
        let rustdocflags = rustdocflags.get_or_insert_with(Flags::default);
        push_common_flags(cx, rustdocflags);
        rustdocflags.push("-Z");
        rustdocflags.push("unstable-options");
        rustdocflags.push("--persist-doctests");
        rustdocflags.push(cx.ws.doctests_dir.as_str());
    }

    match (cx.args.coverage_target_only, &cx.args.target) {
        (true, Some(coverage_target)) => {
            env.set(
                &format!("CARGO_TARGET_{}_RUSTFLAGS", target_u_upper(coverage_target)),
                &rustflags.encode_space_separated()?,
            )?;
            env.unset("RUSTFLAGS")?;
            env.unset("CARGO_ENCODED_RUSTFLAGS")?;
        }
        _ => {
            // First, try with RUSTFLAGS because `nextest` subcommand sometimes doesn't work well with encoded flags.
            if let Ok(v) = rustflags.encode_space_separated() {
                env.set("RUSTFLAGS", &v)?;
                env.unset("CARGO_ENCODED_RUSTFLAGS")?;
            } else {
                env.set("CARGO_ENCODED_RUSTFLAGS", &rustflags.encode()?)?;
            }
        }
    }

    if let Some(rustdocflags) = rustdocflags {
        // First, try with RUSTDOCFLAGS because `nextest` subcommand sometimes doesn't work well with encoded flags.
        if let Ok(v) = rustdocflags.encode_space_separated() {
            env.set("RUSTDOCFLAGS", &v)?;
            env.unset("CARGO_ENCODED_RUSTDOCFLAGS")?;
        } else {
            env.set("CARGO_ENCODED_RUSTDOCFLAGS", &rustdocflags.encode()?)?;
        }
    }
    if cx.args.include_ffi {
        // https://github.com/rust-lang/cc-rs/blob/1.0.73/src/lib.rs#L2347-L2365
        // Environment variables that use hyphens are not available in many environments, so we ignore them for now.
        let target_u = target_u_lower(cx.ws.target_for_config.triple());
        let cflags_key = &format!("CFLAGS_{target_u}");
        // Use std::env instead of crate::env to match cc-rs's behavior.
        // https://github.com/rust-lang/cc-rs/blob/1.0.73/src/lib.rs#L2740
        let mut cflags = match std::env::var(cflags_key) {
            Ok(cflags) => cflags,
            Err(_) => match std::env::var("TARGET_CFLAGS") {
                Ok(cflags) => cflags,
                Err(_) => std::env::var("CFLAGS").unwrap_or_default(),
            },
        };
        let cxxflags_key = &format!("CXXFLAGS_{target_u}");
        let mut cxxflags = match std::env::var(cxxflags_key) {
            Ok(cxxflags) => cxxflags,
            Err(_) => match std::env::var("TARGET_CXXFLAGS") {
                Ok(cxxflags) => cxxflags,
                Err(_) => std::env::var("CXXFLAGS").unwrap_or_default(),
            },
        };
        let clang_flags = " -fprofile-instr-generate -fcoverage-mapping -fprofile-update=atomic";
        cflags.push_str(clang_flags);
        cxxflags.push_str(clang_flags);
        env.set(cflags_key, &cflags)?;
        env.set(cxxflags_key, &cxxflags)?;
    }
    env.set("LLVM_PROFILE_FILE", llvm_profile_file.as_str())?;
    env.set("CARGO_LLVM_COV", "1")?;
    if cx.args.subcommand == Subcommand::ShowEnv {
        env.set("CARGO_LLVM_COV_SHOW_ENV", "1")?;
    }
    Ok(())
}

fn has_z_flag(args: &[String], name: &str) -> bool {
    let mut iter = args.iter().map(String::as_str);
    while let Some(mut arg) = iter.next() {
        if arg == "-Z" {
            arg = iter.next().unwrap();
        } else if let Some(a) = arg.strip_prefix("-Z") {
            arg = a;
        } else {
            continue;
        }
        if let Some(rest) = arg.strip_prefix(name) {
            if rest.is_empty() || rest.starts_with('=') {
                return true;
            }
        }
    }
    false
}

fn run_test(cx: &Context) -> Result<()> {
    let mut cargo = cx.cargo();

    set_env(cx, &mut cargo, IsNextest(false))?;

    cargo.arg("test");
    if cx.ws.need_doctest_in_workspace && !has_z_flag(&cx.args.cargo_args, "doctest-in-workspace") {
        // https://github.com/rust-lang/cargo/issues/9427
        cargo.arg("-Z");
        cargo.arg("doctest-in-workspace");
    }

    if cx.args.ignore_run_fail {
        {
            let mut cargo = cargo.clone();
            cargo.arg("--no-run");
            cargo::test_or_run_args(cx, &mut cargo);
            if term::verbose() {
                status!("Running", "{cargo}");
                cargo.stdout_to_stderr().run()?;
            } else {
                // Capture output to prevent duplicate warnings from appearing in two runs.
                cargo.run_with_output()?;
            }
        }

        cargo.arg("--no-fail-fast");
        cargo::test_or_run_args(cx, &mut cargo);
        if term::verbose() {
            status!("Running", "{cargo}");
        }
        stdout_to_stderr(cx, &mut cargo);
        if let Err(e) = cargo.run() {
            warn!("{e:#}");
        }
    } else {
        cargo::test_or_run_args(cx, &mut cargo);
        if term::verbose() {
            status!("Running", "{cargo}");
        }
        stdout_to_stderr(cx, &mut cargo);
        cargo.run()?;
    }

    Ok(())
}

fn archive_nextest(cx: &Context) -> Result<()> {
    let mut cargo = cx.cargo();

    set_env(cx, &mut cargo, IsNextest(true))?;

    cargo.arg("nextest").arg("archive");

    cargo::test_or_run_args(cx, &mut cargo);
    if term::verbose() {
        status!("Running", "{cargo}");
    }
    stdout_to_stderr(cx, &mut cargo);
    cargo.run()?;

    Ok(())
}

fn run_nextest(cx: &Context) -> Result<()> {
    let mut cargo = cx.cargo();

    set_env(cx, &mut cargo, IsNextest(true))?;

    cargo.arg("nextest").arg("run");

    if cx.args.ignore_run_fail {
        {
            let mut cargo = cargo.clone();
            cargo.arg("--no-run");
            cargo::test_or_run_args(cx, &mut cargo);
            if term::verbose() {
                status!("Running", "{cargo}");
                cargo.stdout_to_stderr().run()?;
            } else {
                // Capture output to prevent duplicate warnings from appearing in two runs.
                cargo.run_with_output()?;
            }
        }

        cargo.arg("--no-fail-fast");
        cargo::test_or_run_args(cx, &mut cargo);
        if term::verbose() {
            status!("Running", "{cargo}");
        }
        stdout_to_stderr(cx, &mut cargo);
        if let Err(e) = cargo.run() {
            warn!("{e:#}");
        }
    } else {
        cargo::test_or_run_args(cx, &mut cargo);
        if term::verbose() {
            status!("Running", "{cargo}");
        }
        stdout_to_stderr(cx, &mut cargo);
        cargo.run()?;
    }
    Ok(())
}

fn run_run(cx: &Context) -> Result<()> {
    let mut cargo = cx.cargo();

    set_env(cx, &mut cargo, IsNextest(false))?;

    if cx.args.ignore_run_fail {
        {
            let mut cargo = cargo.clone();
            cargo.arg("build");
            cargo::test_or_run_args(cx, &mut cargo);
            if term::verbose() {
                status!("Running", "{cargo}");
                cargo.stdout_to_stderr().run()?;
            } else {
                // Capture output to prevent duplicate warnings from appearing in two runs.
                cargo.run_with_output()?;
            }
        }

        cargo.arg("run");
        cargo::test_or_run_args(cx, &mut cargo);
        if term::verbose() {
            status!("Running", "{cargo}");
        }
        stdout_to_stderr(cx, &mut cargo);
        if let Err(e) = cargo.run() {
            warn!("{e:#}");
        }
    } else {
        cargo.arg("run");
        cargo::test_or_run_args(cx, &mut cargo);
        if term::verbose() {
            status!("Running", "{cargo}");
        }
        stdout_to_stderr(cx, &mut cargo);
        cargo.run()?;
    }
    Ok(())
}

fn stdout_to_stderr(cx: &Context, cargo: &mut ProcessBuilder) {
    if cx.args.cov.no_report
        || cx.args.cov.output_dir.is_some()
        || cx.args.cov.output_path.is_some()
    {
        // Do not redirect if unnecessary.
    } else {
        // Redirect stdout to stderr as the report is output to stdout by default.
        cargo.stdout_to_stderr();
    }
}

fn generate_report(cx: &Context) -> Result<()> {
    merge_profraw(cx).context("failed to merge profile data")?;

    let object_files = object_files(cx).context("failed to collect object files")?;
    let ignore_filename_regex = ignore_filename_regex(cx, &object_files)?;
    let format = Format::from_args(cx);
    format
        .generate_report(cx, &object_files, ignore_filename_regex.as_deref())
        .context("failed to generate report")?;

    if cx.args.cov.fail_under_functions.is_some()
        || cx.args.cov.fail_under_lines.is_some()
        || cx.args.cov.fail_under_regions.is_some()
        || cx.args.cov.fail_uncovered_functions.is_some()
        || cx.args.cov.fail_uncovered_lines.is_some()
        || cx.args.cov.fail_uncovered_regions.is_some()
        || cx.args.cov.show_missing_lines
    {
        let format = Format::Json;
        let json = format
            .get_json(cx, &object_files, ignore_filename_regex.as_ref())
            .context("failed to get json")?;

        if let Some(fail_under_functions) = cx.args.cov.fail_under_functions {
            // Handle --fail-under-functions.
            let functions_percent = json
                .get_coverage_percent(CoverageKind::Functions)
                .context("failed to get function coverage")?;
            if functions_percent < fail_under_functions {
                term::error::set(true);
            }
        }

        if let Some(fail_under_lines) = cx.args.cov.fail_under_lines {
            // Handle --fail-under-lines.
            let lines_percent = json
                .get_coverage_percent(CoverageKind::Lines)
                .context("failed to get line coverage")?;
            if lines_percent < fail_under_lines {
                term::error::set(true);
            }
        }

        if let Some(fail_under_regions) = cx.args.cov.fail_under_regions {
            // Handle --fail-under-regions.
            let regions_percent = json
                .get_coverage_percent(CoverageKind::Regions)
                .context("failed to get region coverage")?;
            if regions_percent < fail_under_regions {
                term::error::set(true);
            }
        }

        if let Some(fail_uncovered_functions) = cx.args.cov.fail_uncovered_functions {
            // Handle --fail-uncovered-functions.
            let uncovered =
                json.count_uncovered_functions().context("failed to count uncovered functions")?;
            if uncovered > fail_uncovered_functions {
                term::error::set(true);
            }
        }
        if let Some(fail_uncovered_lines) = cx.args.cov.fail_uncovered_lines {
            // Handle --fail-uncovered-lines.
            let uncovered_files = json.get_uncovered_lines(ignore_filename_regex.as_deref());
            let uncovered = uncovered_files
                .iter()
                .fold(0_u64, |uncovered, (_, lines)| uncovered + lines.len() as u64);

            if uncovered > fail_uncovered_lines {
                term::error::set(true);
            }
        }
        if let Some(fail_uncovered_regions) = cx.args.cov.fail_uncovered_regions {
            // Handle --fail-uncovered-regions.
            let uncovered =
                json.count_uncovered_regions().context("failed to count uncovered regions")?;
            if uncovered > fail_uncovered_regions {
                term::error::set(true);
            }
        }

        if cx.args.cov.show_missing_lines {
            // Handle --show-missing-lines.
            let uncovered_files = json.get_uncovered_lines(ignore_filename_regex.as_deref());
            if !uncovered_files.is_empty() {
                let mut stdout = BufWriter::new(io::stdout().lock()); // Buffered because it is written with newline many times.
                writeln!(stdout, "Uncovered Lines:")?;
                for (file, lines) in &uncovered_files {
                    let lines: Vec<_> = lines.iter().map(ToString::to_string).collect();
                    writeln!(stdout, "{file}: {}", lines.join(", "))?;
                }
                stdout.flush()?;
            }
        }
    }

    if cx.args.cov.open {
        let path = &cx.args.cov.output_dir.as_ref().unwrap().join("html/index.html");
        status!("Opening", "{path}");
        open_report(cx, path)?;
    }
    Ok(())
}

fn open_report(cx: &Context, path: &Utf8Path) -> Result<()> {
    match &cx.ws.config.doc.browser {
        Some(browser) => {
            cmd!(&browser.path)
                .args(&browser.args)
                .arg(path)
                .run()
                .with_context(|| format!("couldn't open report with {}", browser.path.display()))?;
        }
        None => opener::open(path).context("couldn't open report")?,
    }
    Ok(())
}

fn merge_profraw(cx: &Context) -> Result<()> {
    // Convert raw profile data.
    let profraw_files = glob::glob(
        Utf8Path::new(&glob::Pattern::escape(cx.ws.target_dir.as_str())).join("*.profraw").as_str(),
    )?
    .filter_map(Result::ok)
    .collect::<Vec<_>>();
    if profraw_files.is_empty() {
        if cx.ws.profdata_file.exists() {
            return Ok(());
        }
        warn!(
            "not found *.profraw files in {}; this may occur if target directory is accidentally \
             cleared, or running report subcommand without running any tests or binaries",
            cx.ws.target_dir
        );
    }
    let mut input_files = String::new();
    for path in profraw_files {
        input_files.push_str(path.to_str().with_context(|| {
            #[allow(clippy::unnecessary_debug_formatting)]
            {
                format!("{} ({:?}) contains invalid utf-8 data", path.display(), path.as_os_str())
            }
        })?);
        input_files.push('\n');
    }
    let input_files_path = &cx.ws.target_dir.join(format!("{}-profraw-list", cx.ws.name));
    fs::write(input_files_path, input_files)?;
    let mut cmd = cx.process(&cx.llvm_profdata);
    cmd.args(["merge", "-sparse"])
        .arg("-f")
        .arg(input_files_path)
        .arg("-o")
        .arg(&cx.ws.profdata_file);
    if let Some(mode) = &cx.args.cov.failure_mode {
        cmd.arg(format!("-failure-mode={mode}"));
    }
    if let Some(flags) = &cx.llvm_profdata_flags {
        cmd.args(flags.split(' ').filter(|s| !s.trim_start().is_empty()));
    }
    if term::verbose() {
        status!("Running", "{cmd}");
    }
    cmd.stdout_to_stderr().run()?;
    Ok(())
}

fn object_files(cx: &Context) -> Result<Vec<OsString>> {
    fn walk_target_dir<'a>(
        cx: &'a Context,
        target_dir: &Utf8Path,
    ) -> impl Iterator<Item = walkdir::DirEntry> + 'a {
        WalkDir::new(target_dir)
            .into_iter()
            .filter_entry(move |e| {
                let p = e.path();
                // Refs: https://github.com/rust-lang/cargo/blob/0.85.0/src/cargo/core/compiler/layout.rs.
                if p.is_dir() {
                    if p.file_name().is_some_and(|f| {
                        f == "incremental"
                            || f == ".fingerprint"
                            || if cx.args.cov.include_build_script {
                                f == "out"
                            } else {
                                f == "build"
                            }
                    }) {
                        // Ignore incremental compilation related files and output from build scripts.
                        return false;
                    }
                } else if cx.args.cov.include_build_script {
                    if let (Some(stem), Some(p)) = (p.file_stem(), p.parent()) {
                        fn in_build_dir(p: &Path) -> bool {
                            let Some(p) = p.parent() else { return false };
                            let Some(f) = p.file_name() else { return false };
                            f == "build"
                        }
                        if in_build_dir(p) {
                            if stem == "build-script-build"
                                || stem
                                    .to_str()
                                    .unwrap_or_default()
                                    .starts_with("build_script_build-")
                            {
                                let dir = p.file_name().unwrap().to_string_lossy();
                                if !cx.build_script_re.is_match(&dir) {
                                    return false;
                                }
                            } else {
                                return false;
                            }
                        }
                    }
                }
                true
            })
            .filter_map(Result::ok)
    }
    fn is_object(cx: &Context, f: &Path) -> bool {
        let ext = f.extension().unwrap_or_default();
        // We check extension instead of using is_executable crate because it always return true on WSL:
        // - https://github.com/taiki-e/cargo-llvm-cov/issues/316
        // - https://github.com/taiki-e/cargo-llvm-cov/issues/342
        if ext == "d" || ext == "rlib" || ext == "rmeta" || f.ends_with(".cargo-lock") {
            return false;
        }
        let target_is_windows = cx.ws.target_for_config.triple().contains("-windows");
        if target_is_windows
            && !(ext.eq_ignore_ascii_case("exe") || ext.eq_ignore_ascii_case("dll"))
        {
            return false;
        }
        // Using std::fs instead of fs-err is okay here since we ignore error contents
        #[allow(clippy::disallowed_methods)]
        let Ok(metadata) = std::fs::metadata(f) else {
            return false;
        };
        if !metadata.is_file() {
            return false;
        }
        if target_is_windows {
            true
        } else {
            #[cfg(unix)]
            {
                // This is useless on WSL, but check for others just in case.
                use std::os::unix::fs::PermissionsExt as _;
                metadata.permissions().mode() & 0o111 != 0
            }
            #[cfg(not(unix))]
            true
        }
    }

    let re = pkg_hash_re(&cx.ws)?;
    let mut files = vec![];
    let mut searched_dir = String::new();
    // To support testing binary crate like tests that use the CARGO_BIN_EXE
    // environment variable, pass all compiled executables.
    // This is not the ideal way, but the way unstable book says it is cannot support them.
    // https://doc.rust-lang.org/nightly/rustc/instrument-coverage.html#tips-for-listing-the-binaries-automatically
    let mut target_dir = cx.ws.target_dir.clone();
    let mut build_dir = cx.ws.build_dir.clone();
    let mut auto_detect_profile = false;
    if cx.args.subcommand.read_nextest_archive() {
        // TODO: build-dir
        #[derive(Debug, Deserialize)]
        #[serde(rename_all = "kebab-case")]
        struct BinariesMetadata {
            rust_build_meta: RustBuildMeta,
        }
        #[derive(Debug, Deserialize)]
        #[serde(rename_all = "kebab-case")]
        struct RustBuildMeta {
            base_output_directories: Vec<String>,
        }
        target_dir.push("target");
        let archive_file = cx.args.nextest_archive_file.as_ref().unwrap();
        let file = fs::File::open(archive_file)?; // TODO: Buffering?
        let decoder = ruzstd::decoding::StreamingDecoder::new(file)?;
        let mut archive = Archive::new(decoder);
        let mut binaries_metadata = vec![];
        for entry in archive.entries()? {
            let mut entry = entry?;
            let path = entry.path()?;
            if path.ends_with("target/nextest/binaries-metadata.json") {
                entry.read_to_end(&mut binaries_metadata)?;
                break;
            }
        }
        if binaries_metadata.is_empty() {
            warn!("not found binaries-metadata.json in nextest archive {archive_file:?}");
        } else {
            match serde_json::from_slice::<BinariesMetadata>(&binaries_metadata) {
                // TODO: what multiple base_output_directories means?
                Ok(binaries_metadata)
                    if binaries_metadata.rust_build_meta.base_output_directories.len() == 1 =>
                {
                    if cx.args.target.is_some() {
                        info!(
                            "--target flag is no longer needed because detection from nextest archive is now supported"
                        );
                    }
                    if cx.args.release {
                        info!(
                            "--release flag is no longer needed because detection from nextest archive is now supported"
                        );
                    }
                    if cx.args.cargo_profile.is_some() {
                        info!(
                            "--cargo-profile flag is no longer needed because detection from nextest archive is now supported"
                        );
                    }
                    target_dir.push(&binaries_metadata.rust_build_meta.base_output_directories[0]);
                    auto_detect_profile = true;
                }
                res => {
                    warn!(
                        "found binaries-metadata.json in nextest archive {archive_file:?}, but has unsupported or incompatible format: {res:?}"
                    );
                }
            }
        }
    }
    if !auto_detect_profile {
        // https://doc.rust-lang.org/nightly/cargo/reference/build-cache.html
        if let Some(target) = &cx.args.target {
            target_dir.push(target);
            if let Some(build_dir) = &mut build_dir {
                build_dir.push(target);
            }
        }
        // https://doc.rust-lang.org/nightly/cargo/reference/profiles.html#custom-profiles
        let profile = match cx.args.cargo_profile.as_deref() {
            None if cx.args.release => "release",
            Some("release" | "bench") => "release",
            None | Some("dev" | "test") => "debug",
            Some(p) => p,
        };
        target_dir.push(profile);
        if let Some(build_dir) = &mut build_dir {
            build_dir.push(profile);
        }
    }
    for f in walk_target_dir(cx, &target_dir) {
        let f = f.path();
        if is_object(cx, f) {
            if let Some(file_stem) = fs::file_stem_recursive(f).unwrap().to_str() {
                if re.is_match(file_stem) {
                    files.push(make_relative(cx, f).to_owned().into_os_string());
                }
            }
        }
    }
    searched_dir.push_str(target_dir.as_str());
    if let Some(build_dir) = &build_dir {
        if target_dir != *build_dir {
            for f in walk_target_dir(cx, build_dir) {
                let f = f.path();
                if is_object(cx, f) {
                    if let Some(file_stem) = fs::file_stem_recursive(f).unwrap().to_str() {
                        if re.is_match(file_stem) {
                            files.push(make_relative(cx, f).to_owned().into_os_string());
                        }
                    }
                }
            }
            searched_dir.push(',');
            searched_dir.push_str(build_dir.as_str());
        }
    }
    if cx.args.doctests {
        for f in glob::glob(
            Utf8Path::new(&glob::Pattern::escape(cx.ws.doctests_dir.as_str()))
                .join("*/rust_out")
                .as_str(),
        )?
        .filter_map(Result::ok)
        {
            if is_object(cx, &f) {
                files.push(make_relative(cx, &f).to_owned().into_os_string());
            }
        }
        searched_dir.push(',');
        searched_dir.push_str(cx.ws.doctests_dir.as_str());
    }

    // trybuild
    let mut trybuild_target_dir = cx.ws.trybuild_target_dir();
    if let Some(target) = &cx.args.target {
        trybuild_target_dir.push(target);
    }
    // Currently, trybuild always use debug build.
    trybuild_target_dir.push("debug");
    if trybuild_target_dir.is_dir() {
        let mut trybuild_targets = vec![];
        for metadata in trybuild_metadata(&cx.ws, &cx.ws.metadata.target_directory)? {
            for package in metadata.packages.into_values() {
                for target in package.targets {
                    trybuild_targets.push(target.name);
                }
            }
        }
        if !trybuild_targets.is_empty() {
            let re =
                Regex::new(&format!("^({})(-[0-9a-f]+)?$", trybuild_targets.join("|"))).unwrap();
            for entry in walk_target_dir(cx, &trybuild_target_dir) {
                let path = make_relative(cx, entry.path());
                if let Some(file_stem) = fs::file_stem_recursive(path).unwrap().to_str() {
                    if re.is_match(file_stem) {
                        continue;
                    }
                }
                if is_object(cx, path) {
                    files.push(path.to_owned().into_os_string());
                }
            }
            searched_dir.push(',');
            searched_dir.push_str(trybuild_target_dir.as_str());
        }
    }

    // This sort is necessary to make the result of `llvm-cov show` match between macOS and Linux.
    files.sort_unstable();

    if files.is_empty() {
        bail!(
            "not found object files (searched directories: {searched_dir}); this may occur if \
             show-env subcommand is used incorrectly (see docs or other warnings), or unsupported \
             commands or configs are used",
        );
    }
    Ok(files)
}

fn pkg_hash_re(ws: &Workspace) -> Result<RegexVec> {
    let mut targets = BTreeSet::new();
    for id in &ws.metadata.workspace_members {
        let pkg = &ws.metadata.packages[id];
        targets.insert(&pkg.name);
        for t in &pkg.targets {
            targets.insert(&t.name);
        }
    }
    let mut re = RegexVecBuilder::new("^(lib)?(", ")(-[0-9a-f]+)?$");
    for &t in &targets {
        re.or(&t.replace('-', "(-|_)"));
    }
    re.build()
}

/// Collects metadata for packages generated by trybuild. If the trybuild test
/// directory is not found, it returns an empty vector.
fn trybuild_metadata(ws: &Workspace, target_dir: &Utf8Path) -> Result<Vec<Metadata>> {
    // https://github.com/dtolnay/trybuild/pull/219
    let mut trybuild_dir = target_dir.join("tests").join("trybuild");
    if !trybuild_dir.is_dir() {
        trybuild_dir.pop();
        if !trybuild_dir.is_dir() {
            return Ok(vec![]);
        }
    }
    let mut metadata = vec![];
    for entry in fs::read_dir(trybuild_dir)?.filter_map(Result::ok) {
        let manifest_path = &entry.path().join("Cargo.toml");
        if !manifest_path.is_file() {
            continue;
        }
        metadata.push(Metadata::new(manifest_path, ws.config.cargo())?);
    }
    Ok(metadata)
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Format {
    /// `llvm-cov report`
    None,
    /// `llvm-cov export -format=text`
    Json,
    /// `llvm-cov export -format=lcov`
    LCov,
    /// `llvm-cov export -format=lcov` later converted to XML
    Cobertura,
    /// `llvm-cov show -format=lcov` later converted to Codecov JSON
    Codecov,
    /// `llvm-cov show -format=text`
    Text,
    /// `llvm-cov show -format=html`
    Html,
}

impl Format {
    fn from_args(cx: &Context) -> Self {
        if cx.args.cov.json {
            Self::Json
        } else if cx.args.cov.lcov {
            Self::LCov
        } else if cx.args.cov.cobertura {
            Self::Cobertura
        } else if cx.args.cov.codecov {
            Self::Codecov
        } else if cx.args.cov.text {
            Self::Text
        } else if cx.args.cov.html {
            Self::Html
        } else {
            Self::None
        }
    }

    const fn llvm_cov_args(self) -> &'static [&'static str] {
        match self {
            Self::None => &["report"],
            Self::Json | Self::Codecov => &["export", "-format=text"],
            Self::LCov | Self::Cobertura => &["export", "-format=lcov"],
            Self::Text => &["show", "-format=text"],
            Self::Html => &["show", "-format=html"],
        }
    }

    fn use_color(self, cx: &Context) -> Option<&'static str> {
        if matches!(self, Self::Json | Self::LCov | Self::Html) {
            // `llvm-cov export` doesn't have `-use-color` flag.
            // https://llvm.org/docs/CommandGuide/llvm-cov.html#llvm-cov-export
            // Color output cannot be disabled when generating html.
            return None;
        }
        if self == Self::Text && cx.args.cov.output_dir.is_some() {
            return Some("-use-color=0");
        }
        match cx.args.color {
            Some(Coloring::Auto) | None => None,
            Some(Coloring::Always) => Some("-use-color=1"),
            Some(Coloring::Never) => Some("-use-color=0"),
        }
    }

    fn generate_report(
        self,
        cx: &Context,
        object_files: &[OsString],
        ignore_filename_regex: Option<&str>,
    ) -> Result<()> {
        let mut cmd = cx.process(&cx.llvm_cov);

        cmd.args(self.llvm_cov_args());
        cmd.args(self.use_color(cx));
        cmd.arg(format!("-instr-profile={}", cx.ws.profdata_file));
        cmd.args(object_files.iter().flat_map(|f| [OsStr::new("-object"), f]));
        if let Some(ignore_filename_regex) = ignore_filename_regex {
            cmd.arg("-ignore-filename-regex");
            cmd.arg(ignore_filename_regex);
        }

        match self {
            Self::Text | Self::Html => {
                cmd.args([
                    &format!("-show-instantiations={}", cx.args.cov.show_instantiations),
                    "-show-line-counts-or-regions",
                    "-show-expansions",
                    "-show-branches=count",
                ]);
                if cmd!(&cx.llvm_cov, "show", "--help")
                    .read()
                    .unwrap_or_default()
                    .contains("-show-mcdc")
                {
                    // -show-mcdc requires LLVM 18+
                    cmd.arg("-show-mcdc");
                }
                cmd.args([
                    &format!("-Xdemangler={}", cx.current_exe.display()),
                    "-Xdemangler=llvm-cov",
                    "-Xdemangler=demangle",
                ]);
                if let Some(output_dir) = &cx.args.cov.output_dir {
                    if self == Self::Html {
                        cmd.arg(format!("-output-dir={}", output_dir.join("html")));
                    } else {
                        cmd.arg(format!("-output-dir={}", output_dir.join("text")));
                    }
                }
            }
            Self::Json | Self::LCov | Self::Cobertura | Self::Codecov => {
                if cx.args.cov.summary_only {
                    cmd.arg("-summary-only");
                }
                if cx.args.cov.skip_functions {
                    cmd.arg("-skip-functions");
                }
            }
            Self::None => {}
        }

        if let Some(flags) = &cx.llvm_cov_flags {
            cmd.args(flags.split(' ').filter(|s| !s.trim_start().is_empty()));
        }

        if cx.args.cov.cobertura {
            if term::verbose() {
                status!("Running", "{cmd}");
            }
            let lcov = cmd.read()?;
            // Convert to XML
            let cdata = lcov2cobertura::parse_lines(
                lcov.as_bytes().lines(),
                &cx.ws.metadata.workspace_root,
                &[],
            )?;
            let demangler = lcov2cobertura::RustDemangler::new();
            let now = SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .context("SystemTime before UNIX EPOCH!")?
                .as_secs();
            let out = lcov2cobertura::coverage_to_string(&cdata, now, demangler)?;

            if let Some(output_path) = &cx.args.cov.output_path {
                fs::write(output_path, out)?;
                eprintln!();
                status!("Finished", "report saved to {output_path}");
            } else {
                // write XML to stdout
                println!("{out}");
            }
            return Ok(());
        }

        if cx.args.cov.codecov {
            if term::verbose() {
                status!("Running", "{cmd}");
            }
            let cov = cmd.read()?;
            let cov: LlvmCovJsonExport = serde_json::from_str(&cov)?;
            let cov = CodeCovJsonExport::from_llvm_cov_json_export(cov, ignore_filename_regex);
            let out = serde_json::to_string(&cov)?;

            if let Some(output_path) = &cx.args.cov.output_path {
                fs::write(output_path, out)?;
                eprintln!();
                status!("Finished", "report saved to {output_path}");
            } else {
                // write JSON to stdout
                println!("{out}");
            }
            return Ok(());
        }

        if let Some(output_path) = &cx.args.cov.output_path {
            if term::verbose() {
                status!("Running", "{cmd}");
            }

            let out = cmd.read()?;
            if self == Self::Json {
                let mut cov = serde_json::from_str::<LlvmCovJsonExport>(&out)?;
                cov.inject(cx.ws.current_manifest.clone());
                fs::write(output_path, serde_json::to_string(&cov)?)?;
            } else {
                fs::write(output_path, out)?;
            }

            eprintln!();
            status!("Finished", "report saved to {output_path}");
            return Ok(());
        }

        if term::verbose() {
            status!("Running", "{cmd}");
        }

        if self == Self::Json {
            let out = cmd.read()?;
            let mut cov = serde_json::from_str::<LlvmCovJsonExport>(&out)?;
            cov.inject(cx.ws.current_manifest.clone());

            let mut stdout = BufWriter::new(io::stdout().lock()); // Buffered because it is written many times.
            serde_json::to_writer(&mut stdout, &cov)?;
            stdout.flush()?;
        } else {
            cmd.run()?;
        }

        if matches!(self, Self::Html | Self::Text) {
            if let Some(output_dir) = &cx.args.cov.output_dir {
                eprintln!();
                if self == Self::Html {
                    status!("Finished", "report saved to {}", output_dir.join("html"));
                } else {
                    status!("Finished", "report saved to {}", output_dir.join("text"));
                }
            }
        }
        Ok(())
    }

    /// Generates JSON to perform further analysis on it.
    fn get_json(
        self,
        cx: &Context,
        object_files: &[OsString],
        ignore_filename_regex: Option<&String>,
    ) -> Result<LlvmCovJsonExport> {
        if let Self::Json = self {
        } else {
            bail!("requested JSON for non-JSON type");
        }

        let mut cmd = cx.process(&cx.llvm_cov);
        cmd.args(self.llvm_cov_args());
        cmd.arg(format!("-instr-profile={}", cx.ws.profdata_file));
        cmd.args(object_files.iter().flat_map(|f| [OsStr::new("-object"), f]));
        if let Some(ignore_filename_regex) = ignore_filename_regex {
            cmd.arg("-ignore-filename-regex");
            cmd.arg(ignore_filename_regex);
        }
        if term::verbose() {
            status!("Running", "{cmd}");
        }
        let cmd_out = cmd.read()?;
        let json = serde_json::from_str::<LlvmCovJsonExport>(&cmd_out)
            .context("failed to parse json from llvm-cov")?;
        Ok(json)
    }
}

fn ignore_filename_regex(cx: &Context, object_files: &[OsString]) -> Result<Option<String>> {
    // On Windows, we should escape the separator.
    const SEPARATOR: &str = if cfg!(windows) { "\\\\" } else { "/" };

    #[derive(Default)]
    struct Out(String);

    impl Out {
        fn push(&mut self, s: impl AsRef<str>) {
            if !self.0.is_empty() {
                self.0.push('|');
            }
            self.0.push_str(s.as_ref());
        }

        fn push_abs_path(&mut self, path: impl AsRef<Path>) {
            let path = regex::escape(&path.as_ref().to_string_lossy());
            let path = format!("^{path}($|{SEPARATOR})");
            self.push(path);
        }
    }

    let mut out = Out::default();

    if let Some(ignore_filename) = &cx.args.cov.ignore_filename_regex {
        out.push(ignore_filename);
    }
    if !cx.args.cov.disable_default_ignore_filename_regex {
        let vendor_dirs =
            cx.ws.config.source.iter().filter_map(|(_, source)| source.directory.as_deref());

        // On Windows, file paths in cargo config.toml's can use `/` or `\` (when escaped as `\\`).
        // This value is going to be passed through into a regex, not through a path resolution step
        // that is agnostic to slash direction. llvm-cov uses paths with backslashes, which will
        // fail to match against a vendor directory like: `vendor/rust`. Both slash types are
        // reserved characters for file paths, meaning a naive string replacement can safely correct
        // the paths.
        #[cfg(windows)]
        let vendor_dirs = vendor_dirs
            .map(|dir| std::path::PathBuf::from(dir.to_string_lossy().replace("/", "\\")));

        vendor_dirs.for_each(|directory| out.push_abs_path(directory));

        if let Some(dep) = &cx.args.cov.dep_coverage {
            let format = Format::Json;
            let json = format.get_json(cx, object_files, None).context("failed to get json")?;
            let crates_io_re = Regex::new(&format!(
                "{SEPARATOR}registry{SEPARATOR}src{SEPARATOR}index\\.crates\\.io-[0-9a-f]+{SEPARATOR}[0-9A-Za-z-_]+-[0-9]+\\.[0-9]+\\.[0-9]+(-[0-9A-Za-z\\.-]+)?(\\+[0-9A-Za-z\\.-]+)?{SEPARATOR}"
            ))?;
            let dep_re = Regex::new(&format!(
                "{SEPARATOR}registry{SEPARATOR}src{SEPARATOR}index\\.crates\\.io-[0-9a-f]+{SEPARATOR}{dep}-[0-9]+\\.[0-9]+\\.[0-9]+(-[0-9A-Za-z\\.-]+)?(\\+[0-9A-Za-z\\.-]+)?{SEPARATOR}"
            ))?;
            let mut set = BTreeSet::new();
            for data in &json.data {
                for file in &data.files {
                    // TODO: non-crates-io
                    if let Some(crates_io) = crates_io_re.find(&file.filename) {
                        if !dep_re.is_match(crates_io.as_str()) {
                            set.insert(crates_io.as_str());
                        }
                    } else {
                        // TODO: dedup
                        set.insert(&file.filename);
                    }
                }
            }
            for f in set {
                out.push(f);
            }
        } else {
            // TODO: Should we use the actual target path instead of using `tests|examples|benches`?
            //       We may have a directory like tests/support, so maybe we need both?
            if cx.args.remap_path_prefix {
                out.push(format!(
                    r"(^|{SEPARATOR})(rustc{SEPARATOR}([0-9a-f]+|[0-9]+\.[0-9]+\.[0-9]+)|tests|examples|benches){SEPARATOR}|{SEPARATOR}(tests\.rs|[0-9a-zA-Z_-]+[_-]tests\.rs)$"
                ));
            } else {
                out.push(format!(
                    r"{SEPARATOR}rustc{SEPARATOR}([0-9a-f]+|[0-9]+\.[0-9]+\.[0-9]+){SEPARATOR}|^{workspace_root}({SEPARATOR}.*)?{SEPARATOR}(tests|examples|benches){SEPARATOR}|^{workspace_root}({SEPARATOR}.*)?{SEPARATOR}(tests\.rs|[0-9a-zA-Z_-]+[_-]tests\.rs)$",
                    workspace_root = regex::escape(cx.ws.metadata.workspace_root.as_str())
                ));
            }
            out.push_abs_path(&cx.ws.target_dir);
            if let Some(build_dir) = &cx.ws.build_dir {
                if *build_dir != cx.ws.target_dir {
                    out.push_abs_path(build_dir);
                }
            }
            if cx.args.remap_path_prefix {
                if let Some(path) = env::home_dir() {
                    out.push_abs_path(path);
                }
            }
            if let Some(path) = env::cargo_home_with_cwd(&cx.current_dir) {
                let path = regex::escape(&path.as_os_str().to_string_lossy());
                let path = format!("^{path}{SEPARATOR}(registry|git){SEPARATOR}");
                out.push(path);
            }
            if let Some(path) = env::rustup_home_with_cwd(&cx.current_dir) {
                out.push_abs_path(path.join("toolchains"));
            }
            for path in resolve_excluded_paths(cx) {
                out.push_abs_path(path);
            }
        }
    }

    if out.0.is_empty() { Ok(None) } else { Ok(Some(out.0)) }
}

fn resolve_excluded_paths(cx: &Context) -> Vec<Utf8PathBuf> {
    let excluded: Vec<_> = cx
        .workspace_members
        .excluded
        .iter()
        .map(|id| cx.ws.metadata.packages[id].manifest_path.parent().unwrap())
        .collect();
    let included = cx
        .workspace_members
        .included
        .iter()
        .map(|id| cx.ws.metadata.packages[id].manifest_path.parent().unwrap());
    let mut excluded_path = vec![];
    let mut contains: HashMap<&Utf8Path, Vec<_>> = HashMap::default();
    for included in included {
        for &excluded in excluded.iter().filter(|e| included.starts_with(e)) {
            if let Some(v) = contains.get_mut(&excluded) {
                v.push(included);
            } else {
                contains.insert(excluded, vec![included]);
            }
        }
    }
    if contains.is_empty() {
        for &manifest_dir in &excluded {
            let package_path =
                manifest_dir.strip_prefix(&cx.ws.metadata.workspace_root).unwrap_or(manifest_dir);
            excluded_path.push(package_path.to_owned());
        }
        return excluded_path;
    }

    for &excluded in &excluded {
        let Some(included) = contains.get(&excluded) else {
            let package_path =
                excluded.strip_prefix(&cx.ws.metadata.workspace_root).unwrap_or(excluded);
            excluded_path.push(package_path.to_owned());
            continue;
        };

        for _ in WalkDir::new(excluded).into_iter().filter_entry(|e| {
            let p = e.path();
            if !p.is_dir() {
                if p.extension().is_some_and(|e| e == "rs") {
                    let p = p.strip_prefix(&cx.ws.metadata.workspace_root).unwrap_or(p);
                    excluded_path.push(p.to_owned().try_into().unwrap());
                }
                return false;
            }

            let mut contains = false;
            for included in included {
                if included.starts_with(p) {
                    if p.starts_with(included) {
                        return false;
                    }
                    contains = true;
                }
            }
            if contains {
                // continue to walk
                return true;
            }
            let p = p.strip_prefix(&cx.ws.metadata.workspace_root).unwrap_or(p);
            excluded_path.push(p.to_owned().try_into().unwrap());
            false
        }) {}
    }
    excluded_path
}

fn target_u_lower(target: &str) -> String {
    target.replace(['-', '.'], "_")
}
fn target_u_upper(target: &str) -> String {
    let mut target = target_u_lower(target);
    target.make_ascii_uppercase();
    target
}

/// Make the path relative if it's a descendent of the current working dir, otherwise just return
/// the original path
fn make_relative<'a>(cx: &Context, p: &'a Path) -> &'a Path {
    p.strip_prefix(&cx.current_dir).unwrap_or(p)
}
