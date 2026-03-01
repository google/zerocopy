use miette::{Diagnostic, NamedSource, SourceSpan};
use thiserror::Error;

#[derive(Clone, Debug, Error, Diagnostic)]
pub enum HermesError {
    #[error("Syntax error in Rust source: {msg}")]
    #[diagnostic(code(hermes::syn_error))]
    SynError {
        #[source_code]
        src: NamedSource<String>,
        #[label("here")]
        span: SourceSpan,
        msg: String,
    },
    #[error("Documentation block error: {msg}")]
    #[diagnostic(code(hermes::doc_block))]
    DocBlockError {
        #[source_code]
        src: NamedSource<String>,
        #[label("problematic block")]
        span: SourceSpan,
        msg: String,
    },
}
