//! Basic diff functions
use crate::lcs;
use owo_colors::OwoColorize;
use std::fmt;

/// Single change in original slice needed to get new slice
#[derive(Debug, PartialEq, Eq)]
pub enum DiffOp<'a, T: 'a> {
    /// Appears only in second slice
    Insert(&'a [T]),
    /// Appears in both slices, but changed
    Replace(&'a [T], &'a [T]),
    /// Appears only in first slice
    Remove(&'a [T]),
    /// Appears on both slices
    Equal(&'a [T]),
}

/// Diffs any slices which implements PartialEq
pub fn diff<'a, T: PartialEq>(x: &'a [T], y: &'a [T]) -> Vec<DiffOp<'a, T>> {
    let mut ops: Vec<DiffOp<T>> = Vec::new();
    let table = lcs::Table::new(x, y);

    let mut i = 0;
    let mut j = 0;

    for m in table.matches_zero() {
        let x_seq = &x[i..m.x];
        let y_seq = &y[j..m.y];

        if i < m.x && j < m.y {
            ops.push(DiffOp::Replace(x_seq, y_seq));
        } else if i < m.x {
            ops.push(DiffOp::Remove(x_seq));
        } else if j < m.y {
            ops.push(DiffOp::Insert(y_seq));
        }

        i = m.x + m.len;
        j = m.y + m.len;

        if m.len > 0 {
            ops.push(DiffOp::Equal(&x[m.x..i]));
        }
    }
    ops
}

/// Container for slice diff result.  Can be pretty-printed by Display trait.
#[derive(Debug, PartialEq, Eq)]
pub struct SliceChangeset<'a, T> {
    pub diff: Vec<DiffOp<'a, T>>,
}

impl<T: fmt::Display> SliceChangeset<'_, T> {
    pub fn format(&self, skip_same: bool) -> String {
        let mut out: Vec<String> = Vec::with_capacity(self.diff.len());
        for op in &self.diff {
            match op {
                DiffOp::Equal(a) => {
                    if !skip_same || a.len() == 1 {
                        for i in a.iter() {
                            out.push(format!("    {}", i))
                        }
                    } else if a.len() > 1 {
                        out.push(format!("    ... skip({}) ...", a.len()));
                    }
                }

                DiffOp::Insert(a) => {
                    for i in a.iter() {
                        out.push((format!("+   {}", i).green()).to_string());
                    }
                }

                DiffOp::Remove(a) => {
                    for i in a.iter() {
                        out.push(format!("-   {}", i).red().to_string());
                    }
                }
                DiffOp::Replace(a, b) => {
                    let min_len = std::cmp::min(a.len(), b.len());
                    let max_len = std::cmp::max(a.len(), b.len());

                    for i in 0..min_len {
                        out.push(format!("~   {} -> {}", a[i], b[i]).yellow().to_string());
                    }
                    for i in min_len..max_len {
                        if max_len == a.len() {
                            out.push(format!("-   {}", a[i]).red().to_string());
                        } else {
                            out.push(format!("+   {}", b[i]).green().to_string());
                        }
                    }
                }
            }
        }
        format!("[\n{}\n]", out.join(",\n"))
    }
}

impl<T: fmt::Display> fmt::Display for SliceChangeset<'_, T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "{}", self.format(true))
    }
}

/// Diff two arbitary slices with elements that support Display trait
pub fn diff_slice<'a, T: PartialEq + std::fmt::Display>(
    x: &'a [T],
    y: &'a [T],
) -> SliceChangeset<'a, T> {
    let diff = diff(x, y);
    SliceChangeset { diff }
}

#[test]
fn test_basic() {
    assert_eq!(
        diff(&[1, 2, 3, 4, 5, 6], &[2, 3, 5, 7]),
        vec![
            DiffOp::Remove(&[1]),
            DiffOp::Equal(&[2, 3]),
            DiffOp::Remove(&[4]),
            DiffOp::Equal(&[5]),
            DiffOp::Replace(&[6], &[7]),
        ]
    );

    assert_eq!(
        diff_slice(
            &["q", "a", "b", "x", "c", "d"],
            &["a", "b", "y", "c", "d", "f"],
        )
        .diff,
        vec![
            DiffOp::Remove(&["q"]),
            DiffOp::Equal(&["a", "b"]),
            DiffOp::Replace(&["x"], &["y"]),
            DiffOp::Equal(&["c", "d"]),
            DiffOp::Insert(&["f"]),
        ]
    );

    assert_eq!(
        diff(&["a", "c", "d", "b"], &["a", "e", "b"]),
        vec![
            DiffOp::Equal(&["a"]),
            DiffOp::Replace(&["c", "d"], &["e"]),
            DiffOp::Equal(&["b"]),
        ]
    );
    println!("Diff: {}", diff_slice(&[1, 2, 3, 4, 5, 6], &[2, 3, 5, 7]));
    println!(
        "Diff: {}",
        diff_slice(
            &["q", "a", "b", "x", "c", "d"],
            &["a", "b", "y", "c", "d", "f"]
        )
    );
    println!(
        "Diff: {}",
        diff_slice(&["a", "c", "d", "b"], &["a", "e", "b"])
    );
}
