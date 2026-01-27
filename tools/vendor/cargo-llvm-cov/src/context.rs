// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::{
    ffi::OsString,
    io::{self, Write as _},
    path::PathBuf,
};

use anyhow::{Result, bail};
use camino::Utf8PathBuf;

use crate::{
    cargo::Workspace,
    cli::{self, Args, Subcommand},
    env,
    metadata::{Metadata, PackageId},
    process::ProcessBuilder,
    regex_vec::{RegexVec, RegexVecBuilder},
    term,
};

pub(crate) struct Context {
    pub(crate) ws: Workspace,

    pub(crate) args: Args,

    pub(crate) workspace_members: WorkspaceMembers,
    pub(crate) build_script_re: RegexVec,
    pub(crate) current_dir: PathBuf,

    // Paths to executables.
    pub(crate) current_exe: PathBuf,
    // Path to llvm-cov, can be overridden with `LLVM_COV` environment variable.
    pub(crate) llvm_cov: PathBuf,
    // Path to llvm-profdata, can be overridden with `LLVM_PROFDATA` environment variable.
    pub(crate) llvm_profdata: PathBuf,

    /// `LLVM_COV_FLAGS` environment variable to pass additional flags to llvm-cov.
    /// (value: space-separated list)
    pub(crate) llvm_cov_flags: Option<String>,
    /// `LLVM_PROFDATA_FLAGS` environment variable to pass additional flags to llvm-profdata.
    /// (value: space-separated list)
    pub(crate) llvm_profdata_flags: Option<String>,
}

impl Context {
    pub(crate) fn new(mut args: Args) -> Result<Self> {
        let show_env = args.subcommand == Subcommand::ShowEnv;
        let ws = Workspace::new(
            &args.manifest,
            args.target.as_deref(),
            args.doctests,
            args.cov.branch,
            args.cov.mcdc,
            show_env,
        )?;
        cli::merge_config_to_args(&ws, &mut args.target, &mut args.verbose, &mut args.color);
        term::set_coloring(&mut args.color);
        term::verbose::set(args.verbose != 0);

        args.cov.html |= args.cov.open;
        if args.cov.output_dir.is_some() && !args.cov.show() {
            // If the format flag is not specified, this flag is no-op.
            args.cov.output_dir = None;
        }
        {
            // The following warnings should not be promoted to an error.
            let _guard = term::warn::ignore();
            if args.cov.disable_default_ignore_filename_regex {
                warn!("--disable-default-ignore-filename-regex option is unstable");
            }
            if args.cov.dep_coverage.is_some() {
                warn!("--dep-coverage option is unstable");
            }
            if args.cov.branch {
                warn!("--branch option is unstable");
            }
            if args.cov.mcdc {
                warn!("--mcdc option is unstable");
            }
            if args.cov.mcdc && args.cov.branch {
                warn!("the `--mcdc` option takes precedence over `--branch`");
            }
            if args.doc {
                warn!("--doc option is unstable");
            } else if args.doctests {
                warn!("--doctests option is unstable");
            }
        }
        if args.target.is_some() {
            info!(
                "when --target option is used, coverage for proc-macro and build script will \
                 not be displayed because cargo does not pass RUSTFLAGS to them"
            );
        }
        if !matches!(args.subcommand, Subcommand::Report { .. } | Subcommand::Clean)
            && (!args.cov.no_cfg_coverage
                || ws.rustc_version.nightly && !args.cov.no_cfg_coverage_nightly)
        {
            let mut cfgs = String::new();
            let mut flags = String::new();
            if !args.cov.no_cfg_coverage {
                cfgs.push_str("cfg(coverage)");
                flags.push_str("--no-cfg-coverage");
            }
            if ws.rustc_version.nightly && !args.cov.no_cfg_coverage_nightly {
                if cfgs.is_empty() {
                    cfgs.push_str("cfg(coverage_nightly)");
                    flags.push_str("--no-cfg-coverage-nightly");
                } else {
                    cfgs.push_str(" and cfg(coverage_nightly)");
                    flags.push_str(" and --no-cfg-coverage-nightly");
                }
            }
            info!("cargo-llvm-cov currently setting {cfgs}; you can opt-out it by passing {flags}");
        }
        if args.cov.output_dir.is_none() && args.cov.html {
            args.cov.output_dir = Some(ws.output_dir.clone());
        }
        if !matches!(args.subcommand, Subcommand::Report { .. } | Subcommand::Clean)
            && env::var_os("CARGO_LLVM_COV_SHOW_ENV").is_some()
        {
            warn!(
                "cargo-llvm-cov subcommands other than report and clean may not work correctly \
                 in context where environment variables are set by show-env; consider using \
                 normal {} commands",
                if args.subcommand.call_cargo_nextest() { "cargo-nextest" } else { "cargo" }
            );
        }
        if ws.config.build.build_dir.is_some()
            && matches!(
                args.subcommand,
                Subcommand::Nextest { archive_file: true } | Subcommand::NextestArchive
            )
        {
            warn!("nextest archive may not work with Cargo build-dir");
        }

        let (llvm_cov, llvm_profdata): (PathBuf, PathBuf) = match (
            env::var_os("LLVM_COV").map(PathBuf::from),
            env::var_os("LLVM_PROFDATA").map(PathBuf::from),
        ) {
            (Some(llvm_cov), Some(llvm_profdata)) => (llvm_cov, llvm_profdata),
            (llvm_cov_env, llvm_profdata_env) => {
                if llvm_cov_env.is_some() {
                    warn!(
                        "setting only LLVM_COV environment variable may not work properly; consider setting both LLVM_COV and LLVM_PROFDATA environment variables"
                    );
                } else if llvm_profdata_env.is_some() {
                    warn!(
                        "setting only LLVM_PROFDATA environment variable may not work properly; consider setting both LLVM_COV and LLVM_PROFDATA environment variables"
                    );
                }
                // --print target-libdir (without --target flag) returns $sysroot/lib/rustlib/$host_triple/lib
                // llvm-tools exists in $sysroot/lib/rustlib/$host_triple/bin
                // https://github.com/rust-lang/rust/issues/85658
                // https://github.com/rust-lang/rust/blob/1.84.0/src/bootstrap/src/core/build_steps/dist.rs#L454
                let mut rustlib: PathBuf = ws.rustc_print("target-libdir")?.into();
                rustlib.pop(); // lib
                rustlib.push("bin");
                let llvm_cov = rustlib.join(format!("llvm-cov{}", env::consts::EXE_SUFFIX));
                let llvm_profdata =
                    rustlib.join(format!("llvm-profdata{}", env::consts::EXE_SUFFIX));
                // Check if required tools are installed.
                if !llvm_cov.exists() || !llvm_profdata.exists() {
                    let sysroot: Utf8PathBuf = ws.rustc_print("sysroot")?.into();
                    let toolchain = sysroot.file_name().unwrap();
                    if cmd!("rustup", "toolchain", "list")
                        .read()
                        .is_ok_and(|t| t.contains(toolchain))
                    {
                        // If toolchain is installed from rustup and llvm-tools-preview is not installed,
                        // suggest installing llvm-tools-preview via rustup.
                        // Include --toolchain flag because the user may be using toolchain
                        // override shorthand (+toolchain).
                        // Note: In some toolchain versions llvm-tools-preview can also be installed as llvm-tools,
                        // but it is an upstream bug. https://github.com/rust-lang/rust/issues/119164
                        let cmd = cmd!(
                            "rustup",
                            "component",
                            "add",
                            "llvm-tools-preview",
                            "--toolchain",
                            toolchain
                        );
                        let ask = match env::var_os("CARGO_LLVM_COV_SETUP") {
                            None => true,
                            Some(ref v) if v == "yes" => false,
                            Some(v) => {
                                if v != "no" {
                                    warn!(
                                        "CARGO_LLVM_COV_SETUP must be yes or no, but found `{v:?}`"
                                    );
                                }
                                bail!(
                                    "failed to find llvm-tools-preview, please install llvm-tools-preview \
                                     with `rustup component add llvm-tools-preview --toolchain {toolchain}`",
                                );
                            }
                        };
                        ask_to_run(
                            &cmd,
                            ask,
                            "install the `llvm-tools-preview` component for the selected toolchain",
                        )?;
                    } else {
                        bail!(
                            "failed to find llvm-tools-preview, please install llvm-tools-preview, or set LLVM_COV and LLVM_PROFDATA environment variables",
                        );
                    }
                }
                (llvm_cov_env.unwrap_or(llvm_cov), llvm_profdata_env.unwrap_or(llvm_profdata))
            }
        };

        let workspace_members =
            WorkspaceMembers::new(&args.exclude, &args.exclude_from_report, &ws.metadata);
        if workspace_members.included.is_empty() {
            bail!("no crates to be measured for coverage");
        }

        let build_script_re = pkg_hash_re(&ws, &workspace_members.included);

        let mut llvm_cov_flags = env::var("LLVM_COV_FLAGS")?;
        if llvm_cov_flags.is_none() {
            llvm_cov_flags = env::var("CARGO_LLVM_COV_FLAGS")?;
            if llvm_cov_flags.is_some() {
                warn!("CARGO_LLVM_COV_FLAGS is deprecated; consider using LLVM_COV_FLAGS instead");
            }
        }
        let mut llvm_profdata_flags = env::var("LLVM_PROFDATA_FLAGS")?;
        if llvm_profdata_flags.is_none() {
            llvm_profdata_flags = env::var("CARGO_LLVM_PROFDATA_FLAGS")?;
            if llvm_profdata_flags.is_some() {
                warn!(
                    "CARGO_LLVM_PROFDATA_FLAGS is deprecated; consider using LLVM_PROFDATA_FLAGS instead"
                );
            }
        }

        Ok(Self {
            ws,
            args,
            workspace_members,
            build_script_re,
            current_dir: env::current_dir().unwrap(),
            current_exe: match env::current_exe() {
                Ok(exe) => exe,
                Err(e) => {
                    let exe = format!("cargo-llvm-cov{}", env::consts::EXE_SUFFIX);
                    warn!(
                        "failed to get current executable, assuming {exe} in PATH as current executable: {e}"
                    );
                    exe.into()
                }
            },
            llvm_cov,
            llvm_profdata,
            llvm_cov_flags,
            llvm_profdata_flags,
        })
    }

    pub(crate) fn process(&self, program: impl Into<OsString>) -> ProcessBuilder {
        let mut cmd = cmd!(program);
        // cargo displays env vars only with -vv.
        if self.args.verbose > 1 {
            cmd.display_env_vars();
        }
        cmd
    }

    pub(crate) fn cargo(&self) -> ProcessBuilder {
        self.ws.cargo(self.args.verbose)
    }
}

fn pkg_hash_re(ws: &Workspace, pkg_ids: &[PackageId]) -> RegexVec {
    let mut re = RegexVecBuilder::new("^(", ")-[0-9a-f]+$");
    for id in pkg_ids {
        re.or(&ws.metadata.packages[id].name);
    }
    re.build().unwrap()
}

pub(crate) struct WorkspaceMembers {
    pub(crate) excluded: Vec<PackageId>,
    pub(crate) included: Vec<PackageId>,
}

impl WorkspaceMembers {
    fn new(exclude: &[String], exclude_from_report: &[String], metadata: &Metadata) -> Self {
        let mut excluded = vec![];
        let mut included = vec![];
        if !exclude.is_empty() || !exclude_from_report.is_empty() {
            for id in &metadata.workspace_members {
                // --exclude flag doesn't handle `name:version` format
                if exclude.contains(&metadata.packages[id].name)
                    || exclude_from_report.contains(&metadata.packages[id].name)
                {
                    excluded.push(id.clone());
                } else {
                    included.push(id.clone());
                }
            }
        } else {
            for id in &metadata.workspace_members {
                included.push(id.clone());
            }
        }

        Self { excluded, included }
    }
}

// Adapted from https://github.com/rust-lang/miri/blob/dba35d2be72f4b78343d1a0f0b4737306f310672/cargo-miri/src/util.rs#L181-L204
fn ask_to_run(cmd: &ProcessBuilder, ask: bool, text: &str) -> Result<()> {
    // Disable interactive prompts in CI (GitHub Actions, Travis, AppVeyor, etc).
    // Azure doesn't set `CI` though (nothing to see here, just Microsoft being Microsoft),
    // so we also check their `TF_BUILD`.
    let is_ci = env::var_os("CI").is_some() || env::var_os("TF_BUILD").is_some();
    if ask && !is_ci {
        let mut buf = String::new();
        print!("I will run {cmd} to {text}.\nProceed? [Y/n] ");
        io::stdout().flush()?;
        io::stdin().read_line(&mut buf)?;
        match buf.trim().to_lowercase().as_str() {
            // Proceed.
            "" | "y" | "yes" => {}
            "n" | "no" => bail!("aborting as per your request"),
            a => bail!("invalid answer `{a}`"),
        }
    } else {
        info!("running {} to {}", cmd, text);
    }

    cmd.run()?;
    Ok(())
}
