//! Data structures for handling diagnostic output from tests.

use cargo_metadata::diagnostic::DiagnosticLevel;

#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq)]
/// The different levels of diagnostic messages and their relative ranking.
pub enum Level {
    /// internal compiler errors
    Ice = 5,
    /// ´error´ level messages
    Error = 4,
    /// ´warn´ level messages
    Warn = 3,
    /// ´help´ level messages
    Help = 2,
    /// ´note´ level messages
    Note = 1,
    /// Only used for "For more information about this error, try `rustc --explain EXXXX`".
    FailureNote = 0,
}

impl From<DiagnosticLevel> for Level {
    fn from(value: DiagnosticLevel) -> Self {
        match value {
            DiagnosticLevel::Ice => Level::Ice,
            DiagnosticLevel::Error => Level::Error,
            DiagnosticLevel::Warning => Level::Warn,
            DiagnosticLevel::FailureNote => Level::FailureNote,
            DiagnosticLevel::Note => Level::Note,
            DiagnosticLevel::Help => Level::Help,
            other => panic!("rustc got a new kind of diagnostic level: {other:?}"),
        }
    }
}

impl std::str::FromStr for Level {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "ERROR" | "error" => Ok(Self::Error),
            "WARN" | "warning" => Ok(Self::Warn),
            "HELP" | "help" => Ok(Self::Help),
            "NOTE" | "note" => Ok(Self::Note),
            "failure-note" => Ok(Self::FailureNote),
            "error: internal compiler error" => Ok(Self::Ice),
            _ => Err(format!("unknown level `{s}`")),
        }
    }
}

#[derive(Debug)]
/// A diagnostic message.
pub struct Message {
    /// The diagnostic level at which this message was emitted
    pub level: Level,
    /// The main message of the diagnostic (what will be matched for with `//~`)
    pub message: String,
    /// Information about where in the file the message was emitted
    pub line: Option<usize>,
    /// Exact span information of the message
    pub span: Option<spanned::Span>,
    /// Identifier of the message (E0XXX for rustc errors, or lint names)
    pub code: Option<String>,
}

#[derive(Debug)]
/// All the diagnostics that were emitted in a test
pub struct Diagnostics {
    /// Rendered and concatenated version of all diagnostics.
    /// This is equivalent to non-json diagnostics.
    pub rendered: Vec<u8>,
    /// Per line, a list of messages for that line.
    pub messages: Vec<Vec<Message>>,
    /// Messages not on any line (usually because they are from libstd)
    pub messages_from_unknown_file_or_line: Vec<Message>,
}
