// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Bounded-depth rendering of long Lean lists.
//!
//! A Lean list literal with hundreds of elements in one definition makes the
//! elaborator recurse once per element and hits `maxRecDepth` (512 by
//! default). Splitting the list into short leaves, joined by a balanced tree of
//! `_root_.List.append`, keeps the depth logarithmic; hoisting each leaf into
//! its own definition also keeps every definition small. `List.append` lives in
//! `Init.Prelude` and reduces by `rfl`, so kernel evaluation of the joined list
//! is unaffected.

/// Elements per hoisted leaf.
pub const LEAF_LEN: usize = 16;

/// Lists at most this long are left to the caller's inline rendering.
pub const INLINE_LIMIT: usize = 64;

/// Joins already-rendered `parts` into a balanced binary tree of `join_op`
/// applications, or `empty` when there are none.
pub fn join_balanced(parts: &[String], empty: &str, join_op: &str) -> String {
    match parts {
        [] => empty.to_owned(),
        [single] => single.clone(),
        _ => {
            let (left, right) = parts.split_at(parts.len() / 2);
            format!(
                "({join_op} {} {})",
                join_balanced(left, empty, join_op),
                join_balanced(right, empty, join_op)
            )
        }
    }
}

/// A list split into hoisted leaf definitions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoistedList {
    /// Leaf definitions, to be emitted before the definition that uses `expr`.
    pub defs: Vec<String>,
    /// Term denoting the whole list.
    pub expr: String,
}

/// Splits the rendered `items` into `LEAF_LEN`-element leaves named
/// `{prefix}_{i} : List {elem_ty}` and joins them with a balanced
/// `_root_.List.append` tree.
pub fn hoist_list(prefix: &str, elem_ty: &str, items: &[String]) -> HoistedList {
    let mut defs = Vec::new();
    let mut leaf_names = Vec::new();
    for (i, leaf) in items.chunks(LEAF_LEN).enumerate() {
        let name = format!("{prefix}_{i}");
        defs.push(format!("def {name} : List {elem_ty} := [\n  {}\n]\n", leaf.join(",\n  ")));
        leaf_names.push(name);
    }
    HoistedList { defs, expr: join_balanced(&leaf_names, "[]", "_root_.List.append") }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn balanced_join_has_logarithmic_depth() {
        let parts: Vec<String> = (0..8).map(|i| format!("x{i}")).collect();
        assert_eq!(
            join_balanced(&parts, "[]", "f"),
            "(f (f (f x0 x1) (f x2 x3)) (f (f x4 x5) (f x6 x7)))"
        );
        assert_eq!(join_balanced(&[], "[]", "f"), "[]");
    }

    #[test]
    fn hoisting_bounds_every_literal() {
        let items: Vec<String> = (0..700).map(|i| i.to_string()).collect();
        let h = hoist_list("big", "Nat", &items);
        assert_eq!(h.defs.len(), 700usize.div_ceil(LEAF_LEN));
        for d in &h.defs {
            assert!(d.matches(',').count() < LEAF_LEN);
        }
        assert!(h.expr.starts_with("(_root_.List.append (_root_.List.append"));
        assert!(h.expr.contains("big_0 big_1") && h.expr.contains("big_43"));
    }
}
