// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use syn::{Attribute, Expr, ExprLit, Lit, Meta};

/// Extracts the string content of a `#[doc = "..."]` or `/// ...` attribute.
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

/// Helper to check if a line is a Hermes directive.
/// Returns the trimmed content if it matches the prefix, otherwise None.
/// This handles the `///@` syntax.
/// Parses a specific Hermes tag from a line.
/// Returns `Some(content)` if the line starts with `///@ <tag>` or `///@<tag>`.
/// Content is trimmed.
/// Example: `parse_hermes_tag("@ lean spec", "lean spec")` -> `Some(...)`
pub fn parse_hermes_tag<'a>(line: &'a str, tag: &str) -> Option<&'a str> {
    let trimmed = line.trim();
    if !trimmed.starts_with('@') {
        return None;
    }

    // Check for "@ <tag>" or "@<tag>"
    // We expect usage like "@ lean spec"
    let prefix_space = format!("@ {}", tag);
    if let Some(rest) = trimmed.strip_prefix(&prefix_space) {
        return Some(rest.trim());
    }

    let prefix_nospace = format!("@{}", tag);
    if let Some(rest) = trimmed.strip_prefix(&prefix_nospace) {
        return Some(rest.trim());
    }

    None
}

/// Checks if a line is a Hermes directive (starts with `@`).
pub fn is_hermes_directive(line: &str) -> bool {
    line.trim().starts_with('@')
}
/// Iterates over all doc attributes, parsing them, splitting into lines,
/// and yielding only those that are Hermes directives (start with `@`).
/// Returns trimmed lines.
pub fn iter_hermes_lines(attrs: &[Attribute]) -> impl Iterator<Item = String> + '_ {
    attrs.iter().flat_map(|attr| {
        if let Some(doc) = parse_doc_attr(attr) {
            // We must collect to separate lifetime from `doc`
            doc.lines()
                .map(|line| line.trim().to_string())
                .filter(|line| is_hermes_directive(line))
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        }
    })
}
