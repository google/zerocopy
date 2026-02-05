#[cfg(feature = "rustc")]
use crate::{
    aux_builds::AuxBuilder, custom_flags::edition::Edition,
    custom_flags::revision_args::RustcRevisionArgs, custom_flags::run::Run,
    custom_flags::rustfix::RustfixMode, custom_flags::Flag, filter::Match,
};
use crate::{
    diagnostics::{self, Diagnostics},
    parser::CommandParserFunc,
    per_test_config::{Comments, Condition, TestConfig},
    CommandBuilder, Error, Errored, Errors,
};
use color_eyre::eyre::Result;
use regex::bytes::Regex;
use spanned::Spanned;
use std::{
    collections::BTreeMap,
    num::NonZeroUsize,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::{atomic::AtomicBool, Arc},
};

mod args;
pub use args::{Args, Format};

#[derive(Debug, Clone)]
/// Central datastructure containing all information to run the tests.
pub struct Config {
    /// Host triple; usually will be auto-detected.
    pub host: Option<String>,
    /// `None` to run on the host, otherwise a target triple
    pub target: Option<String>,
    /// The folder in which to start searching for .rs files
    pub root_dir: PathBuf,
    /// The binary to actually execute.
    pub program: CommandBuilder,
    /// What to do in case the stdout/stderr output differs from the expected one.
    pub output_conflict_handling: OutputConflictHandling,
    /// The recommended command to bless failing tests.
    pub bless_command: Option<String>,
    /// Where to dump files like the binaries compiled from tests.
    /// Defaults to `target/ui/index_of_config` in the current directory.
    pub out_dir: PathBuf,
    /// Skip test files whose names contain any of these entries.
    pub skip_files: Vec<String>,
    /// Only test files whose names contain any of these entries.
    pub filter_files: Vec<String>,
    /// Override the number of threads to use.
    pub threads: Option<NonZeroUsize>,
    /// Nextest emulation: only list the test itself, not its components.
    pub list: bool,
    /// Only run the tests that are ignored.
    pub run_only_ignored: bool,
    /// Filters must match exactly instead of just checking for substrings.
    pub filter_exact: bool,
    /// The default settings settable via `@` comments
    pub comment_defaults: Comments,
    /// The symbol(s) that signify the start of a comment.
    pub comment_start: &'static str,
    /// Custom comment parsers
    pub custom_comments: BTreeMap<&'static str, CommandParserFunc>,
    /// Custom diagnostic extractor (invoked on the output of tests)
    pub diagnostic_extractor: fn(&Path, &[u8]) -> Diagnostics,
    /// Handle to the global abort check.
    pub abort_check: AbortCheck,
}

/// An atomic bool that can be set to `true` to abort all tests.
/// Will not cancel child processes, but if set from a Ctrl+C handler,
/// the pressing of Ctrl+C will already have cancelled child processes.
#[derive(Clone, Debug, Default)]
pub struct AbortCheck(Arc<AtomicBool>);

impl AbortCheck {
    /// Whether any test has been aborted.
    pub fn aborted(&self) -> bool {
        self.0.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Inform everyone that an abort has been requested
    pub fn abort(&self) {
        self.0.store(true, std::sync::atomic::Ordering::Relaxed)
    }
}

/// Function that performs the actual output conflict handling.
pub type OutputConflictHandling = fn(&Path, &[u8], &mut Errors, &TestConfig);

impl Config {
    /// Create a blank configuration that doesn't do anything interesting
    pub fn dummy() -> Self {
        let mut comment_defaults = Comments::default();
        comment_defaults.base().require_annotations = Spanned::dummy(true).into();
        Self {
            host: Default::default(),
            target: Default::default(),
            root_dir: Default::default(),
            program: CommandBuilder::cmd(""),
            output_conflict_handling: error_on_output_conflict,
            bless_command: Default::default(),
            out_dir: Default::default(),
            skip_files: Default::default(),
            filter_files: Default::default(),
            threads: Default::default(),
            list: Default::default(),
            run_only_ignored: Default::default(),
            filter_exact: Default::default(),
            comment_defaults,
            comment_start: "//",
            custom_comments: Default::default(),
            diagnostic_extractor: diagnostics::default_diagnostics_extractor,
            abort_check: Default::default(),
        }
    }

    /// Create a configuration for testing the output of running
    /// `rustc` on the test files.
    #[cfg(feature = "rustc")]
    pub fn rustc(root_dir: impl Into<PathBuf>) -> Self {
        let mut comment_defaults = Comments::default();

        #[derive(Debug)]
        struct NeedsAsmSupport;

        impl Flag for NeedsAsmSupport {
            fn must_be_unique(&self) -> bool {
                true
            }
            fn clone_inner(&self) -> Box<dyn Flag> {
                Box::new(NeedsAsmSupport)
            }
            fn test_condition(
                &self,
                config: &Config,
                _comments: &Comments,
                _revision: &str,
            ) -> bool {
                let target = config.target.as_ref().unwrap();
                static ASM_SUPPORTED_ARCHS: &[&str] = &[
                    "x86", "x86_64", "arm", "aarch64", "riscv32",
                    "riscv64",
                    // These targets require an additional asm_experimental_arch feature.
                    // "nvptx64", "hexagon", "mips", "mips64", "spirv", "wasm32",
                ];
                !ASM_SUPPORTED_ARCHS.iter().any(|arch| target.contains(arch))
            }
        }

        comment_defaults
            .base()
            .add_custom("rustc-revision-args", RustcRevisionArgs);
        comment_defaults
            .base()
            .add_custom("edition", Edition("2021".into()));
        comment_defaults
            .base()
            .add_custom("rustfix", RustfixMode::MachineApplicable);
        let filters = vec![
            (Match::PathBackslash, b"/".to_vec()),
            #[cfg(windows)]
            (Match::Exact(vec![b'\r']), b"".to_vec()),
            #[cfg(windows)]
            (Match::Exact(br"\\?\".to_vec()), b"".to_vec()),
        ];
        comment_defaults
            .base()
            .normalize_stderr
            .clone_from(&filters);
        comment_defaults.base().normalize_stdout = filters;
        comment_defaults.base().exit_status = Spanned::dummy(1).into();
        comment_defaults.base().require_annotations = Spanned::dummy(true).into();
        let mut config = Self {
            host: None,
            target: None,
            root_dir: root_dir.into(),
            program: CommandBuilder::rustc(),
            output_conflict_handling: error_on_output_conflict,
            bless_command: None,
            out_dir: std::env::var_os("CARGO_TARGET_DIR")
                .map(PathBuf::from)
                .unwrap_or_else(|| std::env::current_dir().unwrap().join("target"))
                .join("ui"),
            skip_files: Vec::new(),
            filter_files: Vec::new(),
            threads: None,
            list: false,
            run_only_ignored: false,
            filter_exact: false,
            comment_defaults,
            comment_start: "//",
            custom_comments: Default::default(),
            diagnostic_extractor: diagnostics::rustc::rustc_diagnostics_extractor,
            abort_check: Default::default(),
        };
        config
            .custom_comments
            .insert("no-rustfix", |parser, _args, span| {
                // args are ignored (can be used as comment)
                parser.set_custom_once("no-rustfix", (), span);
            });

        config
            .custom_comments
            .insert("edition", |parser, args, _span| {
                parser.set_custom_once("edition", Edition((*args).into()), args.span());
            });

        config
            .custom_comments
            .insert("needs-asm-support", |parser, _args, span| {
                // args are ignored (can be used as comment)
                parser.set_custom_once("needs-asm-support", NeedsAsmSupport, span);
            });

        config.custom_comments.insert("run", |parser, args, span| {
            let set = |exit_code| {
                parser.set_custom_once(
                    "run",
                    Run {
                        exit_code,
                        output_conflict_handling: None,
                    },
                    args.span(),
                );
                parser.exit_status = Spanned::new(0, span.clone()).into();
                parser.require_annotations = Spanned::new(false, span.clone()).into();

                let prev = parser
                    .custom
                    .insert("no-rustfix", Spanned::new(vec![Box::new(())], span.clone()));
                parser.check(span, prev.is_none(), "`run` implies `no-rustfix`");
            };
            if args.is_empty() {
                set(0);
            } else {
                match args.content.parse() {
                    Ok(exit_code) => {
                        set(exit_code);
                    }
                    Err(err) => parser.error(args.span(), err.to_string()),
                }
            }
        });
        config.custom_comments.insert("aux-build", |parser, args, span| {
            let name = match args.split_once(":") {
                Some((name, rest)) => {
                    parser.error(rest.span(), "proc macros are now auto-detected, you can remove the `:proc-macro` after the file name");
                    name
                },
                None => args,
            };

            parser
                .add_custom_spanned("aux-build", AuxBuilder { aux_file: name.map(|n| n.into())}, span);
        });
        config
    }

    /// Create a configuration for testing the output of running
    /// `cargo` on the test `Cargo.toml` files.
    #[cfg(feature = "rustc")]
    pub fn cargo(root_dir: impl Into<PathBuf>) -> Self {
        let mut this = Self {
            program: CommandBuilder::cargo(),
            custom_comments: Default::default(),
            diagnostic_extractor: diagnostics::rustc::cargo_diagnostics_extractor,
            comment_start: "#",
            ..Self::rustc(root_dir)
        };
        this.comment_defaults.base().custom.clear();
        this
    }

    /// Populate the config with the values from parsed command line arguments.
    pub fn with_args(&mut self, args: &Args) {
        let Args {
            ref filters,
            check,
            bless,
            list,
            exact,
            ignored,
            format: _,
            threads,
            ref skip,
        } = *args;

        self.threads = threads.or(self.threads);

        self.filter_files.extend_from_slice(filters);
        self.skip_files.extend_from_slice(skip);
        self.run_only_ignored = ignored;
        self.filter_exact = exact;

        self.list = list;

        if check {
            self.output_conflict_handling = error_on_output_conflict;
        } else if bless {
            self.output_conflict_handling = bless_output_files;
        }
    }

    /// Replace all occurrences of a path in stderr/stdout with a byte string.
    #[track_caller]
    pub fn path_filter(&mut self, path: &Path, replacement: &'static (impl AsRef<[u8]> + ?Sized)) {
        self.path_stderr_filter(path, replacement);
        self.path_stdout_filter(path, replacement);
    }

    /// Replace all occurrences of a path in stderr with a byte string.
    #[track_caller]
    pub fn path_stderr_filter(
        &mut self,
        path: &Path,
        replacement: &'static (impl AsRef<[u8]> + ?Sized),
    ) {
        let pattern = path.canonicalize().unwrap();
        self.comment_defaults.base().normalize_stderr.push((
            pattern.parent().unwrap().into(),
            replacement.as_ref().to_owned(),
        ));
    }

    /// Replace all occurrences of a path in stdout with a byte string.
    #[track_caller]
    pub fn path_stdout_filter(
        &mut self,
        path: &Path,
        replacement: &'static (impl AsRef<[u8]> + ?Sized),
    ) {
        let pattern = path.canonicalize().unwrap();
        self.comment_defaults.base().normalize_stdout.push((
            pattern.parent().unwrap().into(),
            replacement.as_ref().to_owned(),
        ));
    }

    /// Replace all occurrences of a regex pattern in stderr/stdout with a byte string.
    #[track_caller]
    pub fn filter(&mut self, pattern: &str, replacement: &'static (impl AsRef<[u8]> + ?Sized)) {
        self.stderr_filter(pattern, replacement);
        self.stdout_filter(pattern, replacement);
    }

    /// Replace all occurrences of a regex pattern in stderr with a byte string.
    #[track_caller]
    pub fn stderr_filter(
        &mut self,
        pattern: &str,
        replacement: &'static (impl AsRef<[u8]> + ?Sized),
    ) {
        self.comment_defaults.base().normalize_stderr.push((
            Regex::new(pattern).unwrap().into(),
            replacement.as_ref().to_owned(),
        ));
    }

    /// Replace all occurrences of a regex pattern in stdout with a byte string.
    #[track_caller]
    pub fn stdout_filter(
        &mut self,
        pattern: &str,
        replacement: &'static (impl AsRef<[u8]> + ?Sized),
    ) {
        self.comment_defaults.base().normalize_stdout.push((
            Regex::new(pattern).unwrap().into(),
            replacement.as_ref().to_owned(),
        ));
    }

    /// Make sure we have the host and target triples.
    pub fn fill_host_and_target(&mut self) -> Result<()> {
        if self.host.is_none() {
            self.host = Some(
                rustc_version::VersionMeta::for_command(std::process::Command::new(
                    &self.program.program,
                ))
                .map_err(|err| {
                    color_eyre::eyre::Report::new(err).wrap_err(format!(
                        "failed to parse rustc version info: {}",
                        self.program.display().to_string().replace('\\', "/")
                    ))
                })?
                .host,
            );
        }
        if self.target.is_none() {
            self.target = Some(self.host.clone().unwrap());
        }
        Ok(())
    }

    /// Check whether the host is the specified string
    pub fn host_matches_target(&self) -> bool {
        self.host.as_ref().expect("host should have been filled in")
            == self
                .target
                .as_ref()
                .expect("target should have been filled in")
    }

    pub(crate) fn get_pointer_width(&self) -> u8 {
        // Taken 1:1 from compiletest-rs
        fn get_pointer_width(triple: &str) -> u8 {
            if (triple.contains("64")
                && !triple.ends_with("gnux32")
                && !triple.ends_with("gnu_ilp32"))
                || triple.starts_with("s390x")
            {
                64
            } else if triple.starts_with("avr") {
                16
            } else {
                32
            }
        }
        get_pointer_width(self.target.as_ref().unwrap())
    }

    pub(crate) fn test_condition(&self, condition: &Condition) -> bool {
        let target = self.target.as_ref().unwrap();
        match condition {
            Condition::Bitwidth(bits) => bits.iter().any(|bits| self.get_pointer_width() == *bits),
            Condition::Target(t) => t.iter().any(|t| target.contains(&**t)),
            Condition::Host(t) => t.iter().any(|t| self.host.as_ref().unwrap().contains(&**t)),
            Condition::OnHost => self.host_matches_target(),
        }
    }

    /// Returns whether according to the in-file conditions, this file should be run.
    pub fn test_file_conditions(&self, comments: &Comments, revision: &str) -> bool {
        if comments
            .for_revision(revision)
            .flat_map(|r| r.ignore.iter())
            .any(|c| self.test_condition(c))
        {
            return self.run_only_ignored;
        }
        if comments.for_revision(revision).any(|r| {
            r.custom.values().any(|flags| {
                flags
                    .content
                    .iter()
                    .any(|flag| flag.test_condition(self, comments, revision))
            })
        }) {
            return self.run_only_ignored;
        }
        comments
            .for_revision(revision)
            .flat_map(|r| r.only.iter())
            .all(|c| self.test_condition(c))
            ^ self.run_only_ignored
    }

    pub(crate) fn aborted(&self) -> Result<(), Errored> {
        if self.abort_check.aborted() {
            Err(Errored::aborted())
        } else {
            Ok(())
        }
    }

    pub(crate) fn run_command(&self, cmd: &mut Command) -> Result<Output, Errored> {
        self.aborted()?;

        let output = cmd.output().map_err(|err| Errored {
            errors: vec![],
            stderr: err.to_string().into_bytes(),
            stdout: format!("could not spawn `{:?}` as a process", cmd.get_program()).into_bytes(),
            command: format!("{cmd:?}"),
        })?;

        self.aborted()?;

        Ok(output)
    }
}

/// Fail the test when mismatches are found, if provided the command string
/// in [`Config::bless_command`] will be suggested as a way to bless the
/// test.
pub fn error_on_output_conflict(
    path: &Path,
    output: &[u8],
    errors: &mut Errors,
    config: &TestConfig,
) {
    let normalized = config.normalize(output, &path.extension().unwrap().to_string_lossy());
    let expected = std::fs::read(path).unwrap_or_default();
    if normalized != expected {
        errors.push(Error::OutputDiffers {
            path: path.to_path_buf(),
            actual: normalized,
            output: output.to_vec(),
            expected,
            bless_command: config.config.bless_command.clone(),
        });
    }
}

/// Ignore mismatches in the stderr/stdout files.
pub fn ignore_output_conflict(
    _path: &Path,
    _output: &[u8],
    _errors: &mut Errors,
    _config: &TestConfig,
) {
}

/// Instead of erroring if the stderr/stdout differs from the expected
/// automatically replace it with the found output (after applying filters).
pub fn bless_output_files(path: &Path, output: &[u8], _errors: &mut Errors, config: &TestConfig) {
    if output.is_empty() {
        let _ = std::fs::remove_file(path);
    } else {
        let actual = config.normalize(output, &path.extension().unwrap().to_string_lossy());
        std::fs::write(path, actual).unwrap();
    }
}
