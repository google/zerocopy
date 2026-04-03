//! Data structures for handling diagnostic output from tests.

use std::path::Path;

#[cfg(feature = "rustc")]
pub mod rustc;

/// Default diagnostics extractor that does nothing.
pub fn default_diagnostics_extractor(_path: &Path, _stderr: &[u8]) -> Diagnostics {
    Diagnostics::default()
}

/// The different levels of diagnostic messages and their relative ranking.
#[derive(Copy, Clone, Debug, PartialOrd, Ord, PartialEq, Eq)]
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

impl std::str::FromStr for Level {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "ERROR" | "error" => Ok(Self::Error),
            "WARN" | "warning" => Ok(Self::Warn),
            "HELP" | "help" => Ok(Self::Help),
            "NOTE" | "note" => Ok(Self::Note),
            "failure-note" => Ok(Self::FailureNote),
            "ICE" | "ice" => Ok(Self::Ice),
            _ => Err(format!("unknown level `{s}`")),
        }
    }
}

/// A diagnostic message.
#[derive(Debug)]
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

/// All the diagnostics that were emitted in a test.
#[derive(Default, Debug)]
pub struct Diagnostics {
    /// Rendered and concatenated version of all diagnostics.
    /// This is equivalent to non-json diagnostics.
    pub rendered: Vec<u8>,
    /// Per line, a list of messages for that line.
    pub messages: Vec<Vec<Message>>,
    /// Messages not on any line (usually because they are from libstd)
    pub messages_from_unknown_file_or_line: Vec<Message>,
}
