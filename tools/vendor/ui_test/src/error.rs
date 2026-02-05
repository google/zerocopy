use crate::{
    diagnostics::Message,
    parser::{Pattern, Span, Spanned},
};
use std::{num::NonZeroUsize, path::PathBuf, process::ExitStatus};

/// All the ways in which a test can fail.
#[derive(Debug)]
#[must_use]
pub enum Error {
    /// Got an invalid exit status.
    ExitStatus {
        /// The exit status of the command.
        status: ExitStatus,
        /// The expected exit status as set in the file or derived from the mode.
        expected: i32,
        /// A reason for why the expected exit status was expected
        reason: Spanned<String>,
    },
    /// A pattern was declared but had no matching error.
    PatternNotFound {
        /// The pattern that was not found, and the span of where that pattern was declared.
        pattern: Spanned<Pattern>,
        /// Can be `None` when it is expected outside the current file
        expected_line: Option<NonZeroUsize>,
    },
    /// A diagnostic code matcher was declared but had no matching error.
    CodeNotFound {
        /// The code that was not found, and the span of where that code was declared.
        code: Spanned<String>,
        /// Can be `None` when it is expected outside the current file
        expected_line: Option<NonZeroUsize>,
    },
    /// A ui test checking for failure does not have any failure patterns
    NoPatternsFound,
    /// A ui test checking for success has failure patterns
    PatternFoundInPassTest {
        /// Span of a flag changing the mode (if changed from default).
        mode: Span,
        /// Span of the pattern
        span: Span,
    },
    /// Stderr/Stdout differed from the `.stderr`/`.stdout` file present.
    OutputDiffers {
        /// The file containing the expected output that differs from the actual output.
        path: PathBuf,
        /// The normalized output from the command.
        actual: Vec<u8>,
        /// The unnormalized output from the command.
        output: Vec<u8>,
        /// The contents of the file.
        expected: Vec<u8>,
        /// A command, that when run, causes the output to get blessed instead of erroring.
        bless_command: Option<String>,
    },
    /// There were errors that don't have a pattern.
    ErrorsWithoutPattern {
        /// The main message of the error.
        msgs: Vec<Message>,
        /// File and line information of the error.
        path: Option<(PathBuf, NonZeroUsize)>,
    },
    /// A comment failed to parse.
    InvalidComment {
        /// The comment
        msg: String,
        /// The character range in which it was defined.
        span: Span,
    },
    /// An invalid setting was used.
    ConfigError(String),
    /// Conflicting comments
    MultipleRevisionsWithResults {
        /// The comment being looked for
        kind: String,
        /// The lines where conflicts happened
        lines: Vec<Span>,
    },
    /// A subcommand (e.g. rustfix) of a test failed.
    Command {
        /// The name of the subcommand (e.g. "rustfix").
        kind: String,
        /// The exit status of the command.
        status: ExitStatus,
    },
    /// This catches crashes of ui tests and reports them along the failed test.
    Bug(String),
    /// An auxiliary build failed with its own set of errors.
    Aux {
        /// Path to the aux file.
        path: Spanned<PathBuf>,
        /// The errors that occurred during the build of the aux file.
        errors: Vec<Error>,
    },
    /// An error occured applying [`rustfix`] suggestions
    Rustfix(anyhow::Error),
}

pub(crate) type Errors = Vec<Error>;
