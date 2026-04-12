use crate::{diagnostics::Message, display, Error, Errors};

use crate::github_actions;
use bstr::ByteSlice;
use spanned::{Span, Spanned};
use std::{
    fmt::{Debug, Write as _},
    io::Write as _,
    num::NonZeroUsize,
    path::{Path, PathBuf},
};

use super::{RevisionStyle, StatusEmitter, Summary, TestStatus};
fn gha_error(error: &Error, test_path: &str, revision: &str) {
    let file = Spanned::read_from_file(test_path).transpose().unwrap();
    let line = |span: &Span| {
        let line = file[..=span.bytes.start].lines().count();
        NonZeroUsize::new(line).unwrap_or(NonZeroUsize::MIN)
    };
    match error {
        Error::ExitStatus {
            status,
            expected,
            reason,
        } => {
            let mut err = github_actions::error(
                test_path,
                format!("test{revision} got {status}, but expected {expected}"),
            );
            err.write_str(reason).unwrap();
        }
        Error::Command { kind, status } => {
            github_actions::error(test_path, format!("{kind}{revision} failed with {status}"));
        }
        Error::PatternNotFound { pattern, .. } => {
            github_actions::error(test_path, format!("Pattern not found{revision}"))
                .line(line(&pattern.span));
        }
        Error::CodeNotFound { code, .. } => {
            github_actions::error(test_path, format!("Diagnostic code not found{revision}"))
                .line(line(&code.span));
        }
        Error::NoPatternsFound => {
            github_actions::error(
                test_path,
                format!("expexted error patterns, but found none{revision}"),
            );
        }
        Error::PatternFoundInPassTest { .. } => {
            github_actions::error(
                test_path,
                format!("error pattern found in pass test{revision}"),
            );
        }
        Error::OutputDiffers {
            path: output_path,
            actual,
            output: _,
            expected,
            bless_command,
        } => {
            if expected.is_empty() {
                let mut err = github_actions::error(
                    test_path,
                    "test generated output, but there was no output file",
                );
                if let Some(bless_command) = bless_command {
                    writeln!(
                        err,
                        "you likely need to bless the tests with `{bless_command}`"
                    )
                    .unwrap();
                }
                return;
            }

            let mut line = 1;
            for r in
                prettydiff::diff_lines(expected.to_str().unwrap(), actual.to_str().unwrap()).diff()
            {
                use prettydiff::basic::DiffOp::*;
                match r {
                    Equal(s) => {
                        line += s.len();
                        continue;
                    }
                    Replace(l, r) => {
                        let mut err = github_actions::error(
                            display(output_path),
                            "actual output differs from expected",
                        )
                        .line(NonZeroUsize::new(line + 1).unwrap());
                        writeln!(err, "this line was expected to be `{}`", r[0]).unwrap();
                        line += l.len();
                    }
                    Remove(l) => {
                        let mut err = github_actions::error(
                            display(output_path),
                            "extraneous lines in output",
                        )
                        .line(NonZeroUsize::new(line + 1).unwrap());
                        writeln!(
                            err,
                            "remove this line and possibly later ones by blessing the test"
                        )
                        .unwrap();
                        line += l.len();
                    }
                    Insert(r) => {
                        let mut err =
                            github_actions::error(display(output_path), "missing line in output")
                                .line(NonZeroUsize::new(line + 1).unwrap());
                        writeln!(err, "bless the test to create a line containing `{}`", r[0])
                            .unwrap();
                        // Do not count these lines, they don't exist in the original file and
                        // would thus mess up the line number.
                    }
                }
            }
        }
        Error::ErrorsWithoutPattern { path, msgs } => {
            if let Some((path, line)) = path.as_ref() {
                let path = display(path);
                let mut err =
                    github_actions::error(path, format!("Unmatched diagnostics{revision}"))
                        .line(*line);
                for Message {
                    level,
                    message,
                    line: _,
                    span: _,
                    code: _,
                } in msgs
                {
                    writeln!(err, "{level:?}: {message}").unwrap();
                }
            } else {
                let mut err = github_actions::error(
                    test_path,
                    format!("Unmatched diagnostics outside the testfile{revision}"),
                );
                for Message {
                    level,
                    message,
                    line: _,
                    span: _,
                    code: _,
                } in msgs
                {
                    writeln!(err, "{level:?}: {message}").unwrap();
                }
            }
        }
        Error::InvalidComment { msg, span } => {
            let mut err = github_actions::error(test_path, format!("Could not parse comment"))
                .line(line(span));
            writeln!(err, "{msg}").unwrap();
        }
        Error::MultipleRevisionsWithResults { kind, lines } => {
            github_actions::error(test_path, format!("multiple {kind} found"))
                .line(line(&lines[0]));
        }
        Error::Bug(_) => {}
        Error::Aux {
            path: aux_path,
            errors,
        } => {
            github_actions::error(test_path, format!("Aux build failed"))
                .line(line(&aux_path.span));
            for error in errors {
                gha_error(error, &display(aux_path), "")
            }
        }
        Error::Rustfix(error) => {
            github_actions::error(
                test_path,
                format!("failed to apply suggestions with rustfix: {error}"),
            );
        }
        Error::ConfigError(msg) => {
            github_actions::error(test_path, msg.clone());
        }
    }
}

/// Emits Github Actions Workspace commands to show the failures directly in the github diff view.
/// If the [`Self::group`] boolean is `true`, also emit `::group` commands.
pub struct Gha {
    /// Show a specific name for the final summary.
    pub name: String,
    /// Use github grouping/folding feature to collapse individual test outputs and entire test suites.
    pub group: bool,
}

#[derive(Clone)]
struct PathAndRev {
    path: PathBuf,
    revision: String,
    group: bool,
}

impl TestStatus for PathAndRev {
    fn path(&self) -> &Path {
        &self.path
    }

    fn for_revision(&self, revision: &str, _style: RevisionStyle) -> Box<dyn TestStatus> {
        Box::new(Self {
            path: self.path.clone(),
            revision: revision.to_owned(),
            group: self.group,
        })
    }

    fn for_path(&self, path: &Path) -> Box<dyn TestStatus> {
        Box::new(Self {
            path: path.to_path_buf(),
            revision: self.revision.clone(),
            group: self.group,
        })
    }

    fn failed_test(&self, _cmd: &str, _stderr: &[u8], _stdout: &[u8]) -> Box<dyn Debug> {
        if self.group {
            Box::new(github_actions::group(format_args!(
                "{}:{}",
                display(&self.path),
                self.revision
            )))
        } else {
            Box::new(())
        }
    }

    fn revision(&self) -> &str {
        &self.revision
    }
}

impl StatusEmitter for Gha {
    fn register_test(&self, path: PathBuf) -> Box<dyn TestStatus> {
        Box::new(PathAndRev {
            path,
            revision: String::new(),
            group: self.group,
        })
    }

    fn finalize(
        &self,
        _failures: usize,
        succeeded: usize,
        ignored: usize,
        filtered: usize,
        // Can't aborted on gha
        _aborted: bool,
    ) -> Box<dyn Summary> {
        struct Summarizer {
            failures: Vec<String>,
            succeeded: usize,
            ignored: usize,
            filtered: usize,
            name: String,
        }

        impl Summary for Summarizer {
            fn test_failure(&mut self, status: &dyn TestStatus, errors: &Errors) {
                let revision = if status.revision().is_empty() {
                    "".to_string()
                } else {
                    format!(" (revision: {})", status.revision())
                };
                for error in errors {
                    gha_error(error, &display(status.path()), &revision);
                }
                self.failures
                    .push(format!("{}{revision}", display(status.path())));
            }
        }
        impl Drop for Summarizer {
            fn drop(&mut self) {
                if let Some(mut file) = github_actions::summary() {
                    writeln!(file, "### {}", self.name).unwrap();
                    for line in &self.failures {
                        writeln!(file, "* {line}").unwrap();
                    }
                    writeln!(file).unwrap();
                    writeln!(file, "| failed | passed | ignored | filtered out |").unwrap();
                    writeln!(file, "| --- | --- | --- | --- |").unwrap();
                    writeln!(
                        file,
                        "| {} | {} | {} | {} |",
                        self.failures.len(),
                        self.succeeded,
                        self.ignored,
                        self.filtered,
                    )
                    .unwrap();
                }
            }
        }

        Box::new(Summarizer {
            failures: vec![],
            succeeded,
            ignored,
            filtered,
            name: self.name.clone(),
        })
    }
}
