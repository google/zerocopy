// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use syn::{Attribute, Expr, ExprLit, Lit, Meta};

/// Extracts the string content of a `#[doc = "..."]` or `/// ...` attribute.
///
/// Returns `None` if the attribute is not a doc comment.
pub fn parse_doc_attr(attr: &Attribute) -> Option<String> {
    if !attr.path().is_ident("doc") {
        return None;
    }

    match &attr.meta {
        Meta::NameValue(nv) => match &nv.value {
            Expr::Lit(ExprLit { lit: Lit::Str(s), .. }) => Some(s.value()),
            _ => None,
        },
        _ => None,
    }
}

/// Parses a specific Hermes tag from a line.
///
/// Checks if the line starts with `///@ <tag>` or `///@<tag>`.
/// Returns `Some(content)` with the content trimmed if there is a match.
///
/// # Example
///
/// `parse_hermes_tag("@ lean spec foo", "lean spec")` -> `Some("foo")`
pub fn parse_hermes_tag<'a>(line: &'a str, tag: &str) -> Option<&'a str> {
    let trimmed = line.trim();
    if !trimmed.starts_with('@') {
        return None;
    }

    // Check for "@ <tag>" (with space)
    let prefix_space = format!("@ {}", tag);
    if let Some(rest) = trimmed.strip_prefix(&prefix_space) {
        return Some(rest.trim());
    }

    // Check for "@<tag>" (no space)
    let prefix_nospace = format!("@{}", tag);
    if let Some(rest) = trimmed.strip_prefix(&prefix_nospace) {
        return Some(rest.trim());
    }

    None
}

/// Checks if a line is a Hermes directive (starts with `@`).
///
/// This is used to filter lines from doc comments that are intended for Hermes
/// rather than for standard Rust documentation.
pub fn is_hermes_directive(line: &str) -> bool {
    line.trim().starts_with('@')
}

/// Iterates over all doc attributes of an item, parses them, splits them into lines,
/// and yields only those lines that are Hermes directives (start with `@`).
///
/// This helper abstracts away the complexity of parsing `#[doc = "..."]` attributes
/// and filtering for irrelevant comments.
pub fn iter_hermes_lines(attrs: &[Attribute]) -> impl Iterator<Item = String> + '_ {
    attrs.iter().flat_map(|attr| {
        if let Some(doc) = parse_doc_attr(attr) {
            doc.lines()
                .map(|line| line.trim().to_string())
                .filter(|line| is_hermes_directive(line))
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        }
    })
}
