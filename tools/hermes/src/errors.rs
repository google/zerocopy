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

pub fn span_to_miette(span: proc_macro2::Span, source: &str) -> SourceSpan {
    {
        let range = span.byte_range();
        {
            let offset = range.start;
            let len = range.end - range.start;
            return SourceSpan::new(offset.into(), len);
        }
    }

    // Fallback
    let start = span.start();
    let end = span.end();

    let mut byte_offset = 0;
    for (i, line) in source.lines().enumerate() {
        if i + 1 == start.line {
            byte_offset += start.column;
            break;
        }
        byte_offset += line.len() + 1;
    }

    let mut end_offset = 0;
    for (i, line) in source.lines().enumerate() {
        if i + 1 == end.line {
            end_offset += end.column;
            break;
        }
        end_offset += line.len() + 1;
    }

    let len = end_offset.saturating_sub(byte_offset);
    SourceSpan::new(byte_offset.into(), len)
}
