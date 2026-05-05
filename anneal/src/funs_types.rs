//! Parses Aeneas-generated `Funs.lean` signatures.
//!
//! Anneal's spec generator re-derives types from the Rust AST, losing
//! qualification for `use`-imported names (e.g., `Ordering` instead of
//! `core.sync.atomic.Ordering`). This module provides a lookup table from the
//! Aeneas output as a corrective.

use std::collections::HashMap;

/// A function signature parsed from Aeneas-generated Lean.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FunsSignature {
    pub params: Vec<(String, String)>,
    pub ret: Option<String>,
}

/// Function name → Aeneas-generated function signature.
pub type FunsTypeMap = HashMap<String, FunsSignature>;

/// Parses `def` signatures from `Funs.lean`.
///
/// This extracts explicit parameter types and return types while skipping
/// implicit `{}` parameters. Malformed signatures are ignored.
pub fn parse_funs_types(content: &str) -> FunsTypeMap {
    let mut map = FunsTypeMap::new();
    let lines: Vec<&str> = content.lines().collect();

    for i in 0..lines.len() {
        let Some(rest) = lines[i].trim().strip_prefix("def ") else {
            continue;
        };
        let name = rest.split([' ', '(', '{', ':']).next().unwrap_or("");
        if name.is_empty() {
            continue;
        }

        // Collect signature lines until `:=`.
        let mut sig = String::from(rest);
        for j in (i + 1)..lines.len() {
            if sig.contains(":=") {
                break;
            }
            sig.push(' ');
            sig.push_str(lines[j].trim());
        }

        let params = extract_params(&sig);
        let ret = extract_return_type(&sig);
        if !params.is_empty() || ret.is_some() {
            map.insert(name.to_string(), FunsSignature { params, ret });
        }
    }
    map
}

/// Extracts `(name : type)` bindings, skipping `{implicit}` params.
fn extract_params(sig: &str) -> Vec<(String, String)> {
    let mut params = Vec::new();
    let mut chars = sig.chars().peekable();

    while let Some(&c) = chars.peek() {
        match c {
            '(' => {
                chars.next();
                if let Some(pair) = parse_binding(&collect_delimited(&mut chars, ')')) {
                    params.push(pair);
                }
            }
            '{' => {
                chars.next();
                collect_delimited(&mut chars, '}');
            }
            ':' => break,
            _ => {
                chars.next();
            }
        }
    }
    params
}

/// Extracts the function return type.
fn extract_return_type(sig: &str) -> Option<String> {
    let return_start = top_level_return_colon(sig)? + 1;
    let return_end = sig[return_start..].find(":=").map(|i| return_start + i).unwrap_or(sig.len());
    let ret = sig[return_start..return_end].trim();
    if ret.is_empty() {
        return None;
    }
    Some(ret.strip_prefix("Result ").unwrap_or(ret).trim().to_string())
}

/// Finds the colon that separates the parameter list from the return type.
fn top_level_return_colon(sig: &str) -> Option<usize> {
    let mut paren_depth = 0u32;
    let mut brace_depth = 0u32;
    for (i, c) in sig.char_indices() {
        match c {
            '(' => paren_depth += 1,
            ')' => paren_depth = paren_depth.saturating_sub(1),
            '{' => brace_depth += 1,
            '}' => brace_depth = brace_depth.saturating_sub(1),
            ':' if paren_depth == 0 && brace_depth == 0 => return Some(i),
            _ => {}
        }
    }
    None
}

/// Reads chars until the matching `close` delimiter, handling nesting.
fn collect_delimited(chars: &mut std::iter::Peekable<std::str::Chars<'_>>, close: char) -> String {
    let open = if close == ')' { '(' } else { '{' };
    let mut depth = 1u32;
    let mut buf = String::new();
    for c in chars.by_ref() {
        if c == open {
            depth += 1;
        } else if c == close {
            depth -= 1;
            if depth == 0 {
                return buf;
            }
        }
        buf.push(c);
    }
    buf
}

/// Splits `"name : type"` on the first ` : `.
fn parse_binding(s: &str) -> Option<(String, String)> {
    let s = s.trim();
    let i = s.find(" : ")?;
    let (name, ty) = (s[..i].trim(), s[i + 3..].trim());
    (!name.is_empty() && !ty.is_empty()).then_some((name.to_string(), ty.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple() {
        let m = parse_funs_types("def hash_key (k : Std.Usize) : Result Std.Usize := do\n");
        assert_eq!(m["hash_key"].params, [("k".into(), "Std.Usize".into())]);
        assert_eq!(m["hash_key"].ret.as_deref(), Some("Std.Usize"));
    }

    #[test]
    fn multiline() {
        let m = parse_funs_types(
            "def frame.AtomicFrameState.load\n\
             \x20 (self : frame.AtomicFrameState) (order : core.sync.atomic.Ordering) :\n\
             \x20 Result frame.FrameState\n\
             \x20 := do\n",
        );
        let p = &m["frame.AtomicFrameState.load"].params;
        assert_eq!(p[0], ("self".into(), "frame.AtomicFrameState".into()));
        assert_eq!(p[1], ("order".into(), "core.sync.atomic.Ordering".into()));
        assert_eq!(m["frame.AtomicFrameState.load"].ret.as_deref(), Some("frame.FrameState"));
    }

    #[test]
    fn skips_implicits() {
        let m = parse_funs_types(
            "def HashMap.alloc {T : Type} (slots : alloc.vec.Vec T) (n : Std.Usize) :\n\
             \x20 Result Unit := do\n",
        );
        let p = &m["HashMap.alloc"].params;
        assert_eq!(p.len(), 2);
        assert_eq!(p[0].0, "slots");
        assert_eq!(p[1], ("n".into(), "Std.Usize".into()));
    }

    #[test]
    fn multiple_ordering_params() {
        let m = parse_funs_types(
            "def f.compare_exchange\n\
             \x20 (self : f.T) (expected : f.S)\n\
             \x20 (success : core.sync.atomic.Ordering)\n\
             \x20 (failure : core.sync.atomic.Ordering) :\n\
             \x20 Result Unit := do\n",
        );
        let p = &m["f.compare_exchange"].params;
        assert_eq!(p.len(), 4);
        assert_eq!(p[2].1, "core.sync.atomic.Ordering");
        assert_eq!(p[3].1, "core.sync.atomic.Ordering");
    }

    #[test]
    fn preserves_escaped_keyword_params() {
        let m = parse_funs_types("def f (show1 : core.sync.atomic.Ordering) : Result Unit := do\n");
        assert_eq!(m["f"].params, [("show1".into(), "core.sync.atomic.Ordering".into())]);
    }

    #[test]
    fn parses_return_type() {
        let m = parse_funs_types(
            "def f (order : core.sync.atomic.Ordering) :\n\
             \x20 Result core.sync.atomic.Ordering\n\
             \x20 := do\n",
        );
        assert_eq!(m["f"].ret.as_deref(), Some("core.sync.atomic.Ordering"));
    }

    #[test]
    fn trait_instance_no_params() {
        let m = parse_funs_types("def Foo.Clone : core.clone.Clone Foo := {\n  clone := x\n}\n");
        assert!(m["Foo.Clone"].params.is_empty());
        assert_eq!(m["Foo.Clone"].ret.as_deref(), Some("core.clone.Clone Foo"));
    }
}
