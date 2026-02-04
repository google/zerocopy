// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use anyhow::{Context, Result, anyhow};
use syn::FnArg;

/// Represents the output of desugaring a spec string.
#[derive(Debug, Clone)]
pub struct DesugaredSpec {
    /// The full body of the Lean theorem/def.
    pub body: String,
    /// Arguments for the function signature that enforce preconditions (e.g. `(h_valid : ...)`).
    pub signature_args: Option<String>,
    /// The precondition predicate extracted from `requires`.
    pub predicate: Option<String>,
    /// Binders extracted from `forall`.
    pub binders: Vec<String>,
    /// Additional arguments required by the spec (e.g. ghosts).
    pub extra_args: Vec<String>,
}

/// Transforms a raw spec (from `///@ lean spec`) into a structured Lean definition.
///
/// Supported clauses:
/// - `requires: ...` -> Precondition.
/// - `ensures: ...` -> Postcondition (standard Return variant).
/// - `ensures match: ...` -> Postcondition with pattern matching on result.
/// - `forall: ...` -> Universal quantification over variables.
///
/// # Arguments
/// * `spec_content` - The raw string content of the spec.
/// * `fn_name` - The name of the function being specified.
/// * `args` - The arguments of the function (used to generate validity checks).
/// * `is_stateful` - Whether the function is stateful (takes `&mut`).
pub fn desugar_spec(
    spec_content: &str,
    fn_name: &str,
    args: &[FnArg],
    _is_stateful: bool,
) -> Result<DesugaredSpec> {
    let mut requires = None;
    let mut ensures = None;
    let mut binders = Vec::new();
    let mut signature_args = None;
    // extra_args currently not fully implemented in parsing, but struct supports it.
    let extra_args = Vec::new();

    for line in spec_content.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        // Helper to strip prefix with logical flexibility
        let strip_keyword = |s: &str, keyword: &str| -> Option<String> {
            if let Some(rest) = s.strip_prefix(keyword) {
                if let Some(rest) = rest.strip_prefix(':') {
                    return Some(rest.trim().to_string());
                }
                if rest.starts_with(char::is_whitespace) {
                    return Some(rest.trim().to_string());
                }
            }
            None
        };

        if let Some(req) = strip_keyword(line, "requires") {
            requires = Some(req);
        } else if let Some(ens) = strip_keyword(line, "ensures") {
            ensures = Some(ens);
        } else if let Some(forall) = strip_keyword(line, "forall") {
            // "i j k" -> ["i", "j", "k"]
            let vars: Vec<String> = forall.split_whitespace().map(|s| s.to_string()).collect();
            binders.extend(vars);
        } else if signature_args.is_none()
            && let Some(start) = line.find('(')
        {
            // Heuristic for function signature found in `lean model`
            // Only capture if we haven't found one yet and it looks like a model def.
            // e.g. "read(src : ConstPtr T)" -> "(src : ConstPtr T)"
            if let Some(end) = line.rfind(')') {
                if end > start {
                    signature_args = Some(line[start..=end].to_string());
                }
            }
        }
    }

    let predicate = requires.clone();

    // Argument processing for the lambda
    let mut arg_names = Vec::new();
    for arg in args {
        if let FnArg::Typed(pat) = arg {
            if let syn::Pat::Ident(i) = &*pat.pat {
                arg_names.push(i.ident.to_string());
            }
        }
    }

    let mut sb = String::new();

    if !binders.is_empty() {
        sb.push_str("forall ");
        for b in &binders {
            sb.push_str(b);
            sb.push(' ');
        }
        sb.push_str(",\n");
    }

    // Precondition
    if let Some(req) = &requires {
        // If the requirement has a binder (contains ':'), wrap it in parens for Lean dependent arrow.
        // e.g. "h : x > 0" -> "(h : x > 0) ->"
        if req.contains(':') {
            sb.push_str(&format!("  ({}) ->\n", req));
        } else {
            sb.push_str(&format!("  {} ->\n", req));
        }
    }

    // Postcondition
    let call_expr = if arg_names.is_empty() {
        fn_name.to_string()
    } else {
        format!("{} {}", fn_name, arg_names.join(" "))
    };

    if let Some(ens) = &ensures {
        // Check if `ens` starts with `match` keyword for custom matching
        if ens.starts_with("match") {
            sb.push_str(&format!("  match {} with \n  {}\n", call_expr, ens));
        } else {
            // Check for Binder Syntax: `|ret| ...`
            // If present, use that binder name. Otherwise default to `ret`.
            let (binder, body) = if let Some(rest) = ens.strip_prefix('|') {
                if let Some((name, rest)) = rest.split_once('|') {
                    (name.trim(), rest.trim())
                } else {
                    ("ret", ens.as_str())
                }
            } else {
                ("ret", ens.as_str())
            };

            // "Result.ok" wrapper
            sb.push_str(&format!("  match {} with\n", call_expr));
            sb.push_str(&format!("  | .ok {} => {}\n", binder, body));
            sb.push_str("  | .fail _ => False\n");
            sb.push_str("  | .div => False\n");
        }
    } else {
        // Default: just succeed?
        sb.push_str(&format!(
            "  match {} with | .ok _ => True | .fail _ => False | .div => False\n",
            call_expr
        ));
    }

    Ok(DesugaredSpec {
        body: sb,
        signature_args, // Validity args are handled by `generate_lean_file` via `h_valid` arguments.
        predicate,
        binders,
        extra_args,
    })
}

#[cfg(test)]
mod tests {
    use syn::parse_quote;

    use super::*;

    #[test]
    fn test_desugar_simple() {
        let spec = "requires: x > 0\nensures: ret = x + 1";
        let args: Vec<FnArg> = vec![parse_quote!(x: u32)];
        let d = desugar_spec(spec, "add_one", &args, false).unwrap();

        assert!(d.body.contains("x > 0 ->"));
        assert!(d.body.contains("| .ok ret => ret = x + 1"));
    }

    #[test]
    fn test_desugar_forall() {
        let spec = "forall: n\nensures: ret = n";
        let args: Vec<FnArg> = vec![];
        let d = desugar_spec(spec, "get_n", &args, false).unwrap();

        assert!(d.body.contains("forall n ,"));
    }
}
