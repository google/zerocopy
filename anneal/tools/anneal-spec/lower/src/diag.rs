// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Diagnostics with exact UTF-8 source spans.

use std::fmt;

use proc_macro2::Span;

/// A source range in one input file.
///
/// Byte offsets index the UTF-8 text. Lines are 1-based. Columns are 1-based
/// and count Unicode scalar values, not bytes or display cells, so a span
/// after `é` (two bytes, one scalar) starts one column later, not two.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SrcSpan {
    pub start_byte: usize,
    pub end_byte: usize,
    pub lo_line: usize,
    pub lo_col: usize,
    pub hi_line: usize,
    pub hi_col: usize,
}

impl SrcSpan {
    /// Returns the smallest span covering both `self` and `other`.
    pub fn join(self, other: SrcSpan) -> SrcSpan {
        let (lo, hi) = (
            if other.start_byte < self.start_byte { other } else { self },
            if other.end_byte > self.end_byte { other } else { self },
        );
        SrcSpan {
            start_byte: lo.start_byte,
            end_byte: hi.end_byte,
            lo_line: lo.lo_line,
            lo_col: lo.lo_col,
            hi_line: hi.hi_line,
            hi_col: hi.hi_col,
        }
    }
}

/// Maps `proc_macro2` line/column locations back to byte offsets in one file.
pub struct SourceMap<'a> {
    text: &'a str,
    line_starts: Vec<usize>,
}

impl<'a> SourceMap<'a> {
    pub fn new(text: &'a str) -> Self {
        let mut line_starts = vec![0];
        line_starts.extend(text.match_indices('\n').map(|(i, _)| i + 1));
        SourceMap { text, line_starts }
    }

    /// `proc_macro2` reports 1-based lines and 0-based columns counted in
    /// Unicode scalar values; convert one such location to a byte offset.
    fn byte_of(&self, line: usize, col: usize) -> usize {
        let Some(&start) = self.line_starts.get(line.saturating_sub(1)) else {
            return self.text.len();
        };
        let rest = &self.text[start..];
        rest.char_indices()
            .nth(col)
            .map_or(self.text.len().min(start + rest.len()), |(i, _)| start + i)
    }

    pub fn span(&self, span: Span) -> SrcSpan {
        let (lo, hi) = (span.start(), span.end());
        SrcSpan {
            start_byte: self.byte_of(lo.line, lo.column),
            end_byte: self.byte_of(hi.line, hi.column),
            lo_line: lo.line,
            lo_col: lo.column + 1,
            hi_line: hi.line,
            hi_col: hi.column + 1,
        }
    }
}

/// A fail-closed frontend error. Every code is stable and documented in
/// `README.md`.
#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub code: &'static str,
    pub message: String,
    pub span: Span,
    pub help: Option<String>,
}

impl Diagnostic {
    pub fn new(code: &'static str, span: Span, message: impl Into<String>) -> Self {
        Diagnostic { code, message: message.into(), span, help: None }
    }

    pub fn help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    /// Renders `rustc`-style text: header, `--> file:line:col`, the source
    /// line, and a caret underline.
    pub fn render(&self, file: &str, map: &SourceMap<'_>) -> String {
        let s = map.span(self.span);
        let line_text = map.text.lines().nth(s.lo_line.saturating_sub(1)).unwrap_or("");
        let width =
            if s.hi_line == s.lo_line { s.hi_col.saturating_sub(s.lo_col).max(1) } else { 1 };
        let gutter = s.lo_line.to_string().len();
        let pad = " ".repeat(gutter);
        let mut out = format!(
            "error[{}]: {}\n{pad}--> {file}:{}:{}\n{pad} |\n{} | {line_text}\n{pad} | {}{}\n",
            self.code,
            self.message,
            s.lo_line,
            s.lo_col,
            s.lo_line,
            " ".repeat(s.lo_col - 1),
            "^".repeat(width),
        );
        if let Some(help) = &self.help {
            out.push_str(&format!("{pad} = help: {help}\n"));
        }
        out
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error[{}]: {}", self.code, self.message)?;
        if let Some(help) = &self.help {
            write!(f, " (help: {help})")?;
        }
        Ok(())
    }
}

impl From<syn::Error> for Diagnostic {
    fn from(err: syn::Error) -> Self {
        Diagnostic::new("E_ANNEAL_SPEC_SYNTAX", err.span(), err.to_string())
    }
}
