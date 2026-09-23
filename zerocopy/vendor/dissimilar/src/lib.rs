//! [![github]](https://github.com/dtolnay/dissimilar)&ensp;[![crates-io]](https://crates.io/crates/dissimilar)&ensp;[![docs-rs]](https://docs.rs/dissimilar)
//!
//! [github]: https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//! [crates-io]: https://img.shields.io/badge/crates.io-fc8d62?style=for-the-badge&labelColor=555555&logo=rust
//! [docs-rs]: https://img.shields.io/badge/docs.rs-66c2a5?style=for-the-badge&labelColor=555555&logo=docs.rs
//!
//! <br>
//!
//! ## Diff library with semantic cleanup, based on Google's diff-match-patch
//!
//! This library is a port of the Diff component of [Diff Match Patch] to Rust.
//! The diff implementation is based on [Myers' diff algorithm] but includes
//! some [semantic cleanups] to increase human readability by factoring out
//! commonalities which are likely to be coincidental.
//!
//! Diff Match Patch was originally built in 2006 to power Google Docs.
//!
//! # Interface
//!
//! Here is the entire API of the Rust implementation. It operates on borrowed
//! strings and the return value of the diff algorithm is a vector of chunks
//! pointing into slices of those input strings.
//!
//! ```
//! pub enum Chunk<'a> {
//!     Equal(&'a str),
//!     Delete(&'a str),
//!     Insert(&'a str),
//! }
//!
//! # const IGNORE: &str = stringify! {
//! pub fn diff(text1: &str, text2: &str) -> Vec<Chunk>;
//! # };
//! ```
//!
//! [Diff Match Patch]: https://github.com/google/diff-match-patch
//! [Myers' diff algorithm]: https://neil.fraser.name/writing/diff/myers.pdf
//! [semantic cleanups]: https://neil.fraser.name/writing/diff/

#![doc(html_root_url = "https://docs.rs/dissimilar/1.0.10")]
#![allow(
    clippy::blocks_in_conditions,
    clippy::bool_to_int_with_if,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cloned_instead_of_copied, // https://github.com/rust-lang/rust-clippy/issues/7127
    clippy::collapsible_else_if,
    clippy::comparison_chain,
    clippy::implied_bounds_in_impls,
    clippy::items_after_test_module, // https://github.com/rust-lang/rust-clippy/issues/10713
    clippy::let_underscore_untyped,
    clippy::match_same_arms,
    clippy::module_name_repetitions,
    clippy::must_use_candidate,
    clippy::new_without_default,
    clippy::octal_escapes,
    clippy::shadow_unrelated,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::unseparated_literal_suffix,
    unused_parens, // false positive on Some(&(mut diff)) pattern
)]

mod find;
mod range;

#[cfg(test)]
mod tests;

use crate::range::{slice, Range};
use std::cmp;
use std::collections::VecDeque;
use std::fmt::{self, Debug, Display, Write};

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Chunk<'a> {
    Equal(&'a str),
    Delete(&'a str),
    Insert(&'a str),
}

#[derive(Copy, Clone)]
enum Diff<'a, 'b> {
    Equal(Range<'a>, Range<'b>),
    Delete(Range<'a>),
    Insert(Range<'b>),
}

impl<'tmp, 'a: 'tmp, 'b: 'tmp> Diff<'a, 'b> {
    fn text(&self) -> Range<'tmp> {
        match *self {
            Diff::Equal(range, _) | Diff::Delete(range) | Diff::Insert(range) => range,
        }
    }

    fn grow_left(&mut self, increment: usize) {
        self.for_each(|range| {
            range.offset -= increment;
            range.len += increment;
        });
    }

    fn grow_right(&mut self, increment: usize) {
        self.for_each(|range| range.len += increment);
    }

    fn shift_left(&mut self, increment: usize) {
        self.for_each(|range| range.offset -= increment);
    }

    fn shift_right(&mut self, increment: usize) {
        self.for_each(|range| range.offset += increment);
    }

    fn for_each(&mut self, f: impl Fn(&mut Range)) {
        match self {
            Diff::Equal(range1, range2) => {
                f(range1);
                f(range2);
            }
            Diff::Delete(range) => f(range),
            Diff::Insert(range) => f(range),
        }
    }
}

pub fn diff<'a>(text1: &'a str, text2: &'a str) -> Vec<Chunk<'a>> {
    let chars1: Vec<char> = text1.chars().collect();
    let chars2: Vec<char> = text2.chars().collect();
    let range1 = Range::new(&chars1, ..);
    let range2 = Range::new(&chars2, ..);

    let mut solution = main(range1, range2);
    cleanup_char_boundary(&mut solution);
    cleanup_semantic(&mut solution);
    cleanup_merge(&mut solution);

    let mut chunks = Vec::new();
    let mut pos1 = 0;
    let mut pos2 = 0;
    for diff in solution.diffs {
        chunks.push(match diff {
            Diff::Equal(range, _) => {
                let len = range.len_bytes();
                let chunk = Chunk::Equal(&text1[pos1..pos1 + len]);
                pos1 += len;
                pos2 += len;
                chunk
            }
            Diff::Delete(range) => {
                let len = range.len_bytes();
                let chunk = Chunk::Delete(&text1[pos1..pos1 + len]);
                pos1 += len;
                chunk
            }
            Diff::Insert(range) => {
                let len = range.len_bytes();
                let chunk = Chunk::Insert(&text2[pos2..pos2 + len]);
                pos2 += len;
                chunk
            }
        });
    }
    chunks
}

struct Solution<'a, 'b> {
    text1: Range<'a>,
    text2: Range<'b>,
    diffs: Vec<Diff<'a, 'b>>,
}

fn main<'a, 'b>(mut text1: Range<'a>, mut text2: Range<'b>) -> Solution<'a, 'b> {
    let whole1 = text1;
    let whole2 = text2;

    // Trim off common prefix.
    let common_prefix_len = common_prefix(text1, text2);
    let common_prefix = Diff::Equal(
        text1.substring(..common_prefix_len),
        text2.substring(..common_prefix_len),
    );
    text1 = text1.substring(common_prefix_len..);
    text2 = text2.substring(common_prefix_len..);

    // Trim off common suffix.
    let common_suffix_len = common_suffix(text1, text2);
    let common_suffix = Diff::Equal(
        text1.substring(text1.len - common_suffix_len..),
        text2.substring(text2.len - common_suffix_len..),
    );
    text1 = text1.substring(..text1.len - common_suffix_len);
    text2 = text2.substring(..text2.len - common_suffix_len);

    // Compute the diff on the middle block.
    let mut solution = Solution {
        text1: whole1,
        text2: whole2,
        diffs: compute(text1, text2),
    };

    // Restore the prefix and suffix.
    if common_prefix_len > 0 {
        solution.diffs.insert(0, common_prefix);
    }
    if common_suffix_len > 0 {
        solution.diffs.push(common_suffix);
    }

    cleanup_merge(&mut solution);

    solution
}

// Find the differences between two texts. Assumes that the texts do not have
// any common prefix or suffix.
fn compute<'a, 'b>(text1: Range<'a>, text2: Range<'b>) -> Vec<Diff<'a, 'b>> {
    match (text1.is_empty(), text2.is_empty()) {
        (true, true) => return Vec::new(),
        (true, false) => return vec![Diff::Insert(text2)],
        (false, true) => return vec![Diff::Delete(text1)],
        (false, false) => {}
    }

    // Check for entire shorter text inside the longer text.
    if text1.len > text2.len {
        if let Some(i) = text1.find(text2) {
            return vec![
                Diff::Delete(text1.substring(..i)),
                Diff::Equal(text1.substring(i..i + text2.len), text2),
                Diff::Delete(text1.substring(i + text2.len..)),
            ];
        }
    } else {
        if let Some(i) = text2.find(text1) {
            return vec![
                Diff::Insert(text2.substring(..i)),
                Diff::Equal(text1, text2.substring(i..i + text1.len)),
                Diff::Insert(text2.substring(i + text1.len..)),
            ];
        }
    }

    if text1.len == 1 || text2.len == 1 {
        // Single character string.
        // After the previous check, the character can't be an equality.
        return vec![Diff::Delete(text1), Diff::Insert(text2)];
    }

    bisect(text1, text2)
}

// Find the 'middle snake' of a diff, split the problem in two and return the
// recursively constructed diff.
//
// See Myers 1986 paper: An O(ND) Difference Algorithm and Its Variations.
fn bisect<'a, 'b>(text1: Range<'a>, text2: Range<'b>) -> Vec<Diff<'a, 'b>> {
    let max_d = (text1.len + text2.len + 1) / 2;
    let v_offset = max_d;
    let v_len = 2 * max_d;
    let mut v1 = vec![-1isize; v_len];
    let mut v2 = vec![-1isize; v_len];
    v1[v_offset + 1] = 0;
    v2[v_offset + 1] = 0;
    let delta = text1.len as isize - text2.len as isize;
    // If the total number of characters is odd, then the front path will
    // collide with the reverse path.
    let front = delta % 2 != 0;
    // Offsets for start and end of k loop.
    // Prevents mapping of space beyond the grid.
    let mut k1start = 0;
    let mut k1end = 0;
    let mut k2start = 0;
    let mut k2end = 0;
    for d in 0..max_d as isize {
        // Walk the front path one step.
        let mut k1 = -d + k1start;
        while k1 <= d - k1end {
            let k1_offset = (v_offset as isize + k1) as usize;
            let mut x1 = if k1 == -d || (k1 != d && v1[k1_offset - 1] < v1[k1_offset + 1]) {
                v1[k1_offset + 1]
            } else {
                v1[k1_offset - 1] + 1
            } as usize;
            let mut y1 = (x1 as isize - k1) as usize;
            if let (Some(s1), Some(s2)) = (text1.get(x1..), text2.get(y1..)) {
                let advance = common_prefix(s1, s2);
                x1 += advance;
                y1 += advance;
            }
            v1[k1_offset] = x1 as isize;
            if x1 > text1.len {
                // Ran off the right of the graph.
                k1end += 2;
            } else if y1 > text2.len {
                // Ran off the bottom of the graph.
                k1start += 2;
            } else if front {
                let k2_offset = v_offset as isize + delta - k1;
                if k2_offset >= 0 && k2_offset < v_len as isize && v2[k2_offset as usize] != -1 {
                    // Mirror x2 onto top-left coordinate system.
                    let x2 = text1.len as isize - v2[k2_offset as usize];
                    if x1 as isize >= x2 {
                        // Overlap detected.
                        return bisect_split(text1, text2, x1, y1);
                    }
                }
            }
            k1 += 2;
        }

        // Walk the reverse path one step.
        let mut k2 = -d + k2start;
        while k2 <= d - k2end {
            let k2_offset = (v_offset as isize + k2) as usize;
            let mut x2 = if k2 == -d || (k2 != d && v2[k2_offset - 1] < v2[k2_offset + 1]) {
                v2[k2_offset + 1]
            } else {
                v2[k2_offset - 1] + 1
            } as usize;
            let mut y2 = (x2 as isize - k2) as usize;
            if x2 < text1.len && y2 < text2.len {
                let advance = common_suffix(
                    text1.substring(..text1.len - x2),
                    text2.substring(..text2.len - y2),
                );
                x2 += advance;
                y2 += advance;
            }
            v2[k2_offset] = x2 as isize;
            if x2 > text1.len {
                // Ran off the left of the graph.
                k2end += 2;
            } else if y2 > text2.len {
                // Ran off the top of the graph.
                k2start += 2;
            } else if !front {
                let k1_offset = v_offset as isize + delta - k2;
                if k1_offset >= 0 && k1_offset < v_len as isize && v1[k1_offset as usize] != -1 {
                    let x1 = v1[k1_offset as usize] as usize;
                    let y1 = v_offset + x1 - k1_offset as usize;
                    // Mirror x2 onto top-left coordinate system.
                    x2 = text1.len - x2;
                    if x1 >= x2 {
                        // Overlap detected.
                        return bisect_split(text1, text2, x1, y1);
                    }
                }
            }
            k2 += 2;
        }
    }
    // Number of diffs equals number of characters, no commonality at all.
    vec![Diff::Delete(text1), Diff::Insert(text2)]
}

// Given the location of the 'middle snake', split the diff in two parts and
// recurse.
fn bisect_split<'a, 'b>(
    text1: Range<'a>,
    text2: Range<'b>,
    x: usize,
    y: usize,
) -> Vec<Diff<'a, 'b>> {
    let (text1a, text1b) = text1.split_at(x);
    let (text2a, text2b) = text2.split_at(y);

    // Compute both diffs serially.
    let mut diffs = main(text1a, text2a).diffs;
    diffs.extend(main(text1b, text2b).diffs);

    diffs
}

// Determine the length of the common prefix of two strings.
fn common_prefix(text1: Range, text2: Range) -> usize {
    for (i, (b1, b2)) in text1.chars().zip(text2.chars()).enumerate() {
        if b1 != b2 {
            return i;
        }
    }
    cmp::min(text1.len, text2.len)
}

// Determine the length of the common suffix of two strings.
fn common_suffix(text1: Range, text2: Range) -> usize {
    for (i, (b1, b2)) in text1.chars().rev().zip(text2.chars().rev()).enumerate() {
        if b1 != b2 {
            return i;
        }
    }
    cmp::min(text1.len, text2.len)
}

// Determine if the suffix of one string is the prefix of another.
//
// Returns the number of characters common to the end of the first string and
// the start of the second string.
fn common_overlap(mut text1: Range, mut text2: Range) -> usize {
    // Eliminate the null case.
    if text1.is_empty() || text2.is_empty() {
        return 0;
    }
    // Truncate the longer string.
    if text1.len > text2.len {
        text1 = text1.substring(text1.len - text2.len..);
    } else if text1.len < text2.len {
        text2 = text2.substring(..text1.len);
    }
    // Quick check for the worst case.
    if slice(text1) == slice(text2) {
        return text1.len;
    }

    // Start by looking for a single character match
    // and increase length until no match is found.
    // Performance analysis: https://neil.fraser.name/news/2010/11/04/
    let mut best = 0;
    let mut length = 1;
    loop {
        let pattern = text1.substring(text1.len - length..);
        let found = match text2.find(pattern) {
            Some(found) => found,
            None => return best,
        };
        length += found;
        if found == 0
            || slice(text1.substring(text1.len - length..)) == slice(text2.substring(..length))
        {
            best = length;
            length += 1;
        }
    }
}

fn cleanup_char_boundary(solution: &mut Solution) {
    fn is_segmentation_boundary(doc: &[char], pos: usize) -> bool {
        // FIXME: use unicode-segmentation crate?
        let _ = doc;
        let _ = pos;
        true
    }

    fn boundary_down(doc: &[char], pos: usize) -> usize {
        let mut adjust = 0;
        while !is_segmentation_boundary(doc, pos - adjust) {
            adjust += 1;
        }
        adjust
    }

    fn boundary_up(doc: &[char], pos: usize) -> usize {
        let mut adjust = 0;
        while !is_segmentation_boundary(doc, pos + adjust) {
            adjust += 1;
        }
        adjust
    }

    fn skip_overlap<'a>(prev: &Range<'a>, range: &mut Range<'a>) {
        let prev_end = prev.offset + prev.len;
        if prev_end > range.offset {
            let delta = cmp::min(prev_end - range.offset, range.len);
            range.offset += delta;
            range.len -= delta;
        }
    }

    let mut read = 0;
    let mut retain = 0;
    let mut last_delete = Range::empty();
    let mut last_insert = Range::empty();
    while let Some(&(mut diff)) = solution.diffs.get(read) {
        read += 1;
        match &mut diff {
            Diff::Equal(range1, range2) => {
                let adjust = boundary_up(range1.doc, range1.offset);
                // If the whole range is sub-character, skip it.
                if range1.len <= adjust {
                    continue;
                }
                range1.offset += adjust;
                range1.len -= adjust;
                range2.offset += adjust;
                range2.len -= adjust;
                let adjust = boundary_down(range1.doc, range1.offset + range1.len);
                range1.len -= adjust;
                range2.len -= adjust;
                last_delete = Range::empty();
                last_insert = Range::empty();
            }
            Diff::Delete(range) => {
                skip_overlap(&last_delete, range);
                if range.len == 0 {
                    continue;
                }
                let adjust = boundary_down(range.doc, range.offset);
                range.offset -= adjust;
                range.len += adjust;
                let adjust = boundary_up(range.doc, range.offset + range.len);
                range.len += adjust;
                last_delete = *range;
            }
            Diff::Insert(range) => {
                skip_overlap(&last_insert, range);
                if range.len == 0 {
                    continue;
                }
                let adjust = boundary_down(range.doc, range.offset);
                range.offset -= adjust;
                range.len += adjust;
                let adjust = boundary_up(range.doc, range.offset + range.len);
                range.len += adjust;
                last_insert = *range;
            }
        }
        solution.diffs[retain] = diff;
        retain += 1;
    }

    solution.diffs.truncate(retain);
}

// Reduce the number of edits by eliminating semantically trivial equalities.
fn cleanup_semantic(solution: &mut Solution) {
    let mut diffs = &mut solution.diffs;
    if diffs.is_empty() {
        return;
    }

    let mut changes = false;
    let mut equalities = VecDeque::new(); // Double-ended queue of equalities.
    let mut last_equality = None; // Always equal to equalities.peek().text
    let mut pointer = 0;
    // Number of characters that changed prior to the equality.
    let mut len_insertions1 = 0;
    let mut len_deletions1 = 0;
    // Number of characters that changed after the equality.
    let mut len_insertions2 = 0;
    let mut len_deletions2 = 0;
    while let Some(&this_diff) = diffs.get(pointer) {
        match this_diff {
            Diff::Equal(text1, text2) => {
                equalities.push_back(pointer);
                len_insertions1 = len_insertions2;
                len_deletions1 = len_deletions2;
                len_insertions2 = 0;
                len_deletions2 = 0;
                last_equality = Some((text1, text2));
                pointer += 1;
                continue;
            }
            Diff::Delete(text) => len_deletions2 += text.len,
            Diff::Insert(text) => len_insertions2 += text.len,
        }
        // Eliminate an equality that is smaller or equal to the edits on both
        // sides of it.
        if last_equality.map_or(false, |(last_equality, _)| {
            last_equality.len <= cmp::max(len_insertions1, len_deletions1)
                && last_equality.len <= cmp::max(len_insertions2, len_deletions2)
        }) {
            // Jump back to offending equality.
            pointer = equalities.pop_back().unwrap();

            // Replace equality with a delete.
            diffs[pointer] = Diff::Delete(last_equality.unwrap().0);
            // Insert a corresponding insert.
            diffs.insert(pointer + 1, Diff::Insert(last_equality.unwrap().1));

            len_insertions1 = 0; // Reset the counters.
            len_insertions2 = 0;
            len_deletions1 = 0;
            len_deletions2 = 0;
            last_equality = None;
            changes = true;

            // Throw away the previous equality (it needs to be reevaluated).
            equalities.pop_back();
            if let Some(back) = equalities.back() {
                // There is a safe equality we can fall back to.
                pointer = *back;
            } else {
                // There are no previous equalities, jump back to the start.
                pointer = 0;
                continue;
            }
        }
        pointer += 1;
    }

    // Normalize the diff.
    if changes {
        cleanup_merge(solution);
    }
    cleanup_semantic_lossless(solution);
    diffs = &mut solution.diffs;

    // Find any overlaps between deletions and insertions.
    // e.g: <del>abcxxx</del><ins>xxxdef</ins>
    //   -> <del>abc</del>xxx<ins>def</ins>
    // e.g: <del>xxxabc</del><ins>defxxx</ins>
    //   -> <ins>def</ins>xxx<del>abc</del>
    // Only extract an overlap if it is as big as the edit ahead or behind it.
    let mut pointer = 1;
    while let Some(&this_diff) = diffs.get(pointer) {
        let prev_diff = diffs[pointer - 1];
        if let (Diff::Delete(deletion), Diff::Insert(insertion)) = (prev_diff, this_diff) {
            let overlap_len1 = common_overlap(deletion, insertion);
            let overlap_len2 = common_overlap(insertion, deletion);
            let overlap_min = cmp::min(deletion.len, insertion.len);
            if overlap_len1 >= overlap_len2 && 2 * overlap_len1 >= overlap_min {
                // Overlap found. Insert an equality and trim the surrounding edits.
                diffs.insert(
                    pointer,
                    Diff::Equal(
                        deletion.substring(deletion.len - overlap_len1..deletion.len),
                        insertion.substring(..overlap_len1),
                    ),
                );
                diffs[pointer - 1] =
                    Diff::Delete(deletion.substring(..deletion.len - overlap_len1));
                diffs[pointer + 1] = Diff::Insert(insertion.substring(overlap_len1..));
            } else if overlap_len1 < overlap_len2 && 2 * overlap_len2 >= overlap_min {
                // Reverse overlap found.
                // Insert an equality and swap and trim the surrounding edits.
                diffs.insert(
                    pointer,
                    Diff::Equal(
                        deletion.substring(..overlap_len2),
                        insertion.substring(insertion.len - overlap_len2..insertion.len),
                    ),
                );
                diffs[pointer - 1] =
                    Diff::Insert(insertion.substring(..insertion.len - overlap_len2));
                diffs[pointer + 1] = Diff::Delete(deletion.substring(overlap_len2..));
            }
            pointer += 1;
        }
        pointer += 1;
    }
}

// Look for single edits surrounded on both sides by equalities which can be
// shifted sideways to align the edit to a word boundary.
//
// e.g: The c<ins>at c</ins>ame. -> The <ins>cat </ins>came.
fn cleanup_semantic_lossless(solution: &mut Solution) {
    let diffs = &mut solution.diffs;
    let mut pointer = 1;
    while let Some(&next_diff) = diffs.get(pointer + 1) {
        let prev_diff = diffs[pointer - 1];
        if let (
            Diff::Equal(mut prev_equal1, mut prev_equal2),
            Diff::Equal(mut next_equal1, mut next_equal2),
        ) = (prev_diff, next_diff)
        {
            // This is a single edit surrounded by equalities.
            let mut edit = diffs[pointer];

            // First, shift the edit as far left as possible.
            let common_offset = common_suffix(prev_equal1, edit.text());
            let original_prev_len = prev_equal1.len;
            prev_equal1.len -= common_offset;
            prev_equal2.len -= common_offset;
            edit.shift_left(common_offset);
            next_equal1.offset -= common_offset;
            next_equal1.len += common_offset;
            next_equal2.offset -= common_offset;
            next_equal2.len += common_offset;

            // Second, step character by character right, looking for the best fit.
            let mut best_prev_equal = (prev_equal1, prev_equal2);
            let mut best_edit = edit;
            let mut best_next_equal = (next_equal1, next_equal2);
            let mut best_score = cleanup_semantic_score(prev_equal1, edit.text())
                + cleanup_semantic_score(edit.text(), next_equal1);
            while !edit.text().is_empty()
                && !next_equal1.is_empty()
                && edit.text().chars().next().unwrap() == next_equal1.chars().next().unwrap()
            {
                prev_equal1.len += 1;
                prev_equal2.len += 1;
                edit.shift_right(1);
                next_equal1.offset += 1;
                next_equal1.len -= 1;
                next_equal2.offset += 1;
                next_equal2.len -= 1;
                let score = cleanup_semantic_score(prev_equal1, edit.text())
                    + cleanup_semantic_score(edit.text(), next_equal1);
                // The >= encourages trailing rather than leading whitespace on edits.
                if score >= best_score {
                    best_score = score;
                    best_prev_equal = (prev_equal1, prev_equal2);
                    best_edit = edit;
                    best_next_equal = (next_equal1, next_equal2);
                }
            }

            if original_prev_len != best_prev_equal.0.len {
                // We have an improvement, save it back to the diff.
                if best_next_equal.0.is_empty() {
                    diffs.remove(pointer + 1);
                } else {
                    diffs[pointer + 1] = Diff::Equal(best_next_equal.0, best_next_equal.1);
                }
                diffs[pointer] = best_edit;
                if best_prev_equal.0.is_empty() {
                    diffs.remove(pointer - 1);
                    pointer -= 1;
                } else {
                    diffs[pointer - 1] = Diff::Equal(best_prev_equal.0, best_prev_equal.1);
                }
            }
        }
        pointer += 1;
    }
}

// Given two strings, compute a score representing whether the internal boundary
// falls on logical boundaries.
//
// Scores range from 6 (best) to 0 (worst).
fn cleanup_semantic_score(one: Range, two: Range) -> usize {
    if one.is_empty() || two.is_empty() {
        // Edges are the best.
        return 6;
    }

    // Each port of this function behaves slightly differently due to subtle
    // differences in each language's definition of things like 'whitespace'.
    // Since this function's purpose is largely cosmetic, the choice has been
    // made to use each language's native features rather than force total
    // conformity.
    let char1 = one.chars().next_back().unwrap();
    let char2 = two.chars().next().unwrap();
    let non_alphanumeric1 = !char1.is_ascii_alphanumeric();
    let non_alphanumeric2 = !char2.is_ascii_alphanumeric();
    let whitespace1 = non_alphanumeric1 && char1.is_ascii_whitespace();
    let whitespace2 = non_alphanumeric2 && char2.is_ascii_whitespace();
    let line_break1 = whitespace1 && char1.is_control();
    let line_break2 = whitespace2 && char2.is_control();
    let blank_line1 =
        line_break1 && (one.ends_with(['\n', '\n']) || one.ends_with(['\n', '\r', '\n']));
    let blank_line2 =
        line_break2 && (two.starts_with(['\n', '\n']) || two.starts_with(['\r', '\n', '\r', '\n']));

    if blank_line1 || blank_line2 {
        // Five points for blank lines.
        5
    } else if line_break1 || line_break2 {
        // Four points for line breaks.
        4
    } else if non_alphanumeric1 && !whitespace1 && whitespace2 {
        // Three points for end of sentences.
        3
    } else if whitespace1 || whitespace2 {
        // Two points for whitespace.
        2
    } else if non_alphanumeric1 || non_alphanumeric2 {
        // One point for non-alphanumeric.
        1
    } else {
        0
    }
}

// Reorder and merge like edit sections. Merge equalities. Any edit section can
// move as long as it doesn't cross an equality.
fn cleanup_merge(solution: &mut Solution) {
    let diffs = &mut solution.diffs;
    while !diffs.is_empty() {
        diffs.push(Diff::Equal(
            solution.text1.substring(solution.text1.len..),
            solution.text2.substring(solution.text2.len..),
        )); // Add a dummy entry at the end.
        let mut pointer = 0;
        let mut count_delete = 0;
        let mut count_insert = 0;
        let mut text_delete = Range::empty();
        let mut text_insert = Range::empty();
        while let Some(&this_diff) = diffs.get(pointer) {
            match this_diff {
                Diff::Insert(text) => {
                    count_insert += 1;
                    if text_insert.is_empty() {
                        text_insert = text;
                    } else {
                        text_insert.len += text.len;
                    }
                }
                Diff::Delete(text) => {
                    count_delete += 1;
                    if text_delete.is_empty() {
                        text_delete = text;
                    } else {
                        text_delete.len += text.len;
                    }
                }
                Diff::Equal(text, _) => {
                    let count_both = count_delete + count_insert;
                    if count_both > 1 {
                        let both_types = count_delete != 0 && count_insert != 0;
                        // Delete the offending records.
                        diffs.drain(pointer - count_both..pointer);
                        pointer -= count_both;
                        if both_types {
                            // Factor out any common prefix.
                            let common_length = common_prefix(text_insert, text_delete);
                            if common_length != 0 {
                                if pointer > 0 {
                                    match &mut diffs[pointer - 1] {
                                        Diff::Equal(this_diff1, this_diff2) => {
                                            this_diff1.len += common_length;
                                            this_diff2.len += common_length;
                                        }
                                        _ => unreachable!(
                                            "previous diff should have been an equality"
                                        ),
                                    }
                                } else {
                                    diffs.insert(
                                        pointer,
                                        Diff::Equal(
                                            text_delete.substring(..common_length),
                                            text_insert.substring(..common_length),
                                        ),
                                    );
                                    pointer += 1;
                                }
                                text_insert = text_insert.substring(common_length..);
                                text_delete = text_delete.substring(common_length..);
                            }
                            // Factor out any common suffix.
                            let common_length = common_suffix(text_insert, text_delete);
                            if common_length != 0 {
                                diffs[pointer].grow_left(common_length);
                                text_insert.len -= common_length;
                                text_delete.len -= common_length;
                            }
                        }
                        // Insert the merged records.
                        if !text_delete.is_empty() {
                            diffs.insert(pointer, Diff::Delete(text_delete));
                            pointer += 1;
                        }
                        if !text_insert.is_empty() {
                            diffs.insert(pointer, Diff::Insert(text_insert));
                            pointer += 1;
                        }
                    } else if pointer > 0 {
                        if let Some(Diff::Equal(prev_equal1, prev_equal2)) =
                            diffs.get_mut(pointer - 1)
                        {
                            // Merge this equality with the previous one.
                            prev_equal1.len += text.len;
                            prev_equal2.len += text.len;
                            diffs.remove(pointer);
                            pointer -= 1;
                        }
                    }
                    count_insert = 0;
                    count_delete = 0;
                    text_delete = Range::empty();
                    text_insert = Range::empty();
                }
            }
            pointer += 1;
        }
        if diffs.last().unwrap().text().is_empty() {
            diffs.pop(); // Remove the dummy entry at the end.
        }

        // Second pass: look for single edits surrounded on both sides by equalities
        // which can be shifted sideways to eliminate an equality.
        // e.g: A<ins>BA</ins>C -> <ins>AB</ins>AC
        let mut changes = false;
        let mut pointer = 1;
        // Intentionally ignore the first and last element (don't need checking).
        while let Some(&next_diff) = diffs.get(pointer + 1) {
            let prev_diff = diffs[pointer - 1];
            let this_diff = diffs[pointer];
            if let (Diff::Equal(prev_diff, _), Diff::Equal(next_diff, _)) = (prev_diff, next_diff) {
                // This is a single edit surrounded by equalities.
                if this_diff.text().ends_with(prev_diff) {
                    // Shift the edit over the previous equality.
                    diffs[pointer].shift_left(prev_diff.len);
                    diffs[pointer + 1].grow_left(prev_diff.len);
                    diffs.remove(pointer - 1); // Delete prev_diff.
                    changes = true;
                } else if this_diff.text().starts_with(next_diff) {
                    // Shift the edit over the next equality.
                    diffs[pointer - 1].grow_right(next_diff.len);
                    diffs[pointer].shift_right(next_diff.len);
                    diffs.remove(pointer + 1); // Delete next_diff.
                    changes = true;
                }
            }
            pointer += 1;
        }
        // If shifts were made, the diff needs reordering and another shift sweep.
        if !changes {
            return;
        }
    }
}

impl Debug for Chunk<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let (name, text) = match *self {
            Chunk::Equal(text) => ("Equal", text),
            Chunk::Delete(text) => ("Delete", text),
            Chunk::Insert(text) => ("Insert", text),
        };
        write!(formatter, "{}({:?})", name, text)
    }
}

impl Debug for Diff<'_, '_> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let (name, range) = match *self {
            Diff::Equal(range, _) => ("Equal", range),
            Diff::Delete(range) => ("Delete", range),
            Diff::Insert(range) => ("Insert", range),
        };
        formatter.write_str(name)?;
        formatter.write_str("(\"")?;
        for ch in range.chars() {
            if ch == '\'' {
                // escape_debug turns this into "\'" which is unnecessary.
                formatter.write_char(ch)?;
            } else {
                Display::fmt(&ch.escape_debug(), formatter)?;
            }
        }
        formatter.write_str("\")")?;
        Ok(())
    }
}
