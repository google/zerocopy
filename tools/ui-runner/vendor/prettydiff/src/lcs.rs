//! Common functions for [Longest common subsequences](https://en.wikipedia.org/wiki/Longest_common_subsequence_problem)
//! on slice.

cfg_prettytable! {
    use crate::format_table;
    use prettytable::{Cell, Row};
}
use std::cmp::max;

#[derive(Debug)]
pub struct Table<'a, T: 'a> {
    x: &'a [T],
    y: &'a [T],
    table: Vec<Vec<usize>>,
}

/// Implements Longest Common Subsequences Table
/// Memory requirement: O(N^2)
///
/// Based on [Wikipedia article](https://en.wikipedia.org/wiki/Longest_common_subsequence_problem)
impl<'a, T> Table<'a, T>
where
    T: PartialEq,
{
    /// Creates new table for search common subsequences in x and y
    pub fn new(x: &'a [T], y: &'a [T]) -> Table<'a, T> {
        let x_len = x.len() + 1;
        let y_len = y.len() + 1;
        let mut table = vec![vec![0; y_len]; x_len];

        for i in 1..x_len {
            for j in 1..y_len {
                table[i][j] = if x[i - 1] == y[j - 1] {
                    table[i - 1][j - 1] + 1
                } else {
                    max(table[i][j - 1], table[i - 1][j])
                };
            }
        }

        Table { x, y, table }
    }

    fn seq_iter(&self) -> TableIter<T> {
        TableIter {
            x: self.x.len(),
            y: self.y.len(),
            table: self,
        }
    }
    fn get_match(&self, x: usize, y: usize, len: usize) -> Match<T> {
        Match {
            x,
            y,
            len,
            table: self,
        }
    }

    /// Returns matches between X and Y
    pub fn matches(&self) -> Vec<Match<T>> {
        let mut matches: Vec<Match<T>> = Vec::new();
        for (x, y) in self.seq_iter() {
            if let Some(last) = matches.last_mut() {
                if last.x == x + 1 && last.y == y + 1 {
                    last.x = x;
                    last.y = y;
                    last.len += 1;
                    continue;
                }
            }
            matches.push(self.get_match(x, y, 1));
        }
        matches.reverse();
        matches
    }

    /// Returns matches between X and Y with zero-len match at the end
    pub fn matches_zero(&self) -> Vec<Match<T>> {
        let mut matches = self.matches();
        matches.push(self.get_match(self.x.len(), self.y.len(), 0));
        matches
    }

    /// Find longest sequence
    pub fn longest_seq(&self) -> Vec<&T> {
        self.matches();
        let mut common: Vec<_> = self.seq_iter().map(|(x, _y)| &self.x[x]).collect();
        common.reverse();
        common
    }
}

#[cfg(feature = "prettytable-rs")]
/// Prints pretty-table for LCS
impl<'a, T> std::fmt::Display for Table<'a, T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut table = format_table::new();
        let mut header = vec!["".to_string(), "Ø".to_string()];
        for i in self.x {
            header.push(format!("{}", i));
        }

        table.set_titles(Row::new(
            header.into_iter().map(|i| Cell::new(&i)).collect(),
        ));
        for j in 0..=self.y.len() {
            let mut row = vec![if j == 0 {
                "Ø".to_string()
            } else {
                format!("{}", self.y[j - 1])
            }];
            for i in 0..=self.x.len() {
                row.push(format!("{}", self.table[i][j]));
            }
            table.add_row(row.into_iter().map(|i| Cell::new(&i)).collect());
        }
        write!(formatter, "\n{}", table)
    }
}

struct TableIter<'a, T: 'a> {
    x: usize,
    y: usize,
    table: &'a Table<'a, T>,
}

impl<'a, T> Iterator for TableIter<'a, T> {
    type Item = (usize, usize);
    fn next(&mut self) -> Option<Self::Item> {
        let table = &self.table.table;

        while self.x != 0 && self.y != 0 {
            let cur = table[self.x][self.y];

            if cur == table[self.x - 1][self.y] {
                self.x -= 1;
                continue;
            }
            self.y -= 1;
            if cur == table[self.x][self.y] {
                continue;
            }
            self.x -= 1;
            return Some((self.x, self.y));
        }
        None
    }
}

pub struct Match<'a, T: 'a> {
    pub x: usize,
    pub y: usize,
    pub len: usize,
    table: &'a Table<'a, T>,
}

impl<'a, T> Match<'a, T> {
    /// Returns matched sequence
    pub fn seq(&self) -> &[T] {
        &self.table.x[self.x..(self.x + self.len)]
    }
}

#[test]
fn test_table() {
    let x = vec!["A", "G", "C", "A", "T"];
    let y = vec!["G", "A", "C"];

    let table = Table::new(&x, &y);
    assert_eq!(
        format!("{}", table),
        r#"
┌───┬───┬───┬───┬───┬───┬───┐
│   │ Ø │ A │ G │ C │ A │ T │
├───┼───┼───┼───┼───┼───┼───┤
│ Ø │ 0 │ 0 │ 0 │ 0 │ 0 │ 0 │
├───┼───┼───┼───┼───┼───┼───┤
│ G │ 0 │ 0 │ 1 │ 1 │ 1 │ 1 │
├───┼───┼───┼───┼───┼───┼───┤
│ A │ 0 │ 1 │ 1 │ 1 │ 2 │ 2 │
├───┼───┼───┼───┼───┼───┼───┤
│ C │ 0 │ 1 │ 1 │ 2 │ 2 │ 2 │
└───┴───┴───┴───┴───┴───┴───┘
"#
    );
    assert_eq!(table.longest_seq(), vec![&"A", &"C"]);
}

#[test]

fn test_table_match() {
    let test_v = vec![
        (
            "The quick brown fox jumps over the lazy dog",
            "The quick brown dog leaps over the lazy cat",
            "The quick brown o ps over the lazy ",
            vec!["The quick brown ", "o", " ", "ps over the lazy "],
        ),
        ("ab:c", "ba:b:c", "ab:c", vec!["a", "b:c"]),
        (
            "The red brown fox jumped over the rolling log",
            "The brown spotted fox leaped over the rolling log",
            "The brown fox ped over the rolling log",
            vec!["The ", "brown ", "fox ", "ped over the rolling log"],
        ),
    ];
    for (x_str, y_str, exp_str, match_exp) in test_v {
        let x: Vec<_> = x_str.split("").collect();
        let y: Vec<_> = y_str.split("").collect();

        // Trim empty elements
        let table = Table::new(&x[1..(x.len() - 1)], &y[1..(y.len() - 1)]);
        let seq = table
            .longest_seq()
            .iter()
            .map(|i| i.to_string())
            .collect::<Vec<String>>()
            .join("");
        assert_eq!(seq, exp_str);
        let matches: Vec<_> = table.matches().iter().map(|m| m.seq().join("")).collect();
        assert_eq!(matches, match_exp);
    }
}
