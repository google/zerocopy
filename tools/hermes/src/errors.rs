use miette::{Diagnostic, NamedSource, SourceSpan};
use thiserror::Error;

#[derive(Clone, Debug, Error, Diagnostic)]
pub enum HermesError {
    #[error("Syntax error in Rust source: {msg}")]
    #[diagnostic(code(hermes::syn_error))]
    Syn {
        #[source_code]
        src: NamedSource<String>,
        #[label("here")]
        span: SourceSpan,
        msg: String,
    },
    #[error("Documentation block error: {msg}")]
    #[diagnostic(code(hermes::doc_block))]
    DocBlock {
        #[source_code]
        src: NamedSource<String>,
        #[label("problematic block")]
        span: SourceSpan,
        msg: String,
    },
    #[error("Nested item error: {msg}")]
    #[diagnostic(code(hermes::nested_item))]
    NestedItem {
        #[source_code]
        src: NamedSource<String>,
        #[label("this item is defined inside a function body")]
        span: SourceSpan,
        msg: String,
    },
}
