use colored::*;
use prettydiff::{basic::DiffOp, basic::DiffOp::*, diff_lines, diff_words};

/// How many lines of context are displayed around the actual diffs
const CONTEXT: usize = 2;

fn skip(skipped_lines: &[&str]) {
    // When the amount of skipped lines is exactly `CONTEXT * 2`, we already
    // print all the context and don't actually skip anything.
    match skipped_lines.len().checked_sub(CONTEXT * 2) {
        Some(skipped @ 2..) => {
            // Print an initial `CONTEXT` amount of lines.
            for line in &skipped_lines[..CONTEXT] {
                println!(" {line}");
            }
            println!("... {skipped} lines skipped ...");
            // Print `... n lines skipped ...` followed by the last `CONTEXT` lines.
            for line in &skipped_lines[skipped + CONTEXT..] {
                println!(" {line}");
            }
        }
        _ => {
            // Print all the skipped lines if the amount of context desired is less than the amount of lines
            for line in skipped_lines {
                println!(" {line}");
            }
        }
    }
}

fn row(row: DiffOp<'_, &str>) {
    match row {
        Remove(l) => {
            for l in l {
                println!("{}{}", "-".red(), l.red());
            }
        }
        Equal(l) => {
            skip(l);
        }
        Replace(l, r) => {
            for (l, r) in l.iter().zip(r) {
                print_line_diff(l, r);
            }
        }
        Insert(r) => {
            for r in r {
                println!("{}{}", "+".green(), r.green());
            }
        }
    }
}

fn print_line_diff(l: &str, r: &str) {
    let diff = diff_words(l, r);
    let diff = diff.diff();
    if has_both_insertions_and_deletions(&diff)
        || !colored::control::SHOULD_COLORIZE.should_colorize()
    {
        // The line both adds and removes chars, print both lines, but highlight their differences instead of
        // drawing the entire line in red/green.
        print!("{}", "-".red());
        for char in &diff {
            match *char {
                Replace(l, _) | Remove(l) => {
                    for l in l {
                        print!("{}", l.to_string().on_red())
                    }
                }
                Insert(_) => {}
                Equal(l) => {
                    for l in l {
                        print!("{l}")
                    }
                }
            }
        }
        println!();
        print!("{}", "+".green());
        for char in diff {
            match char {
                Remove(_) => {}
                Replace(_, r) | Insert(r) => {
                    for r in r {
                        print!("{}", r.to_string().on_green())
                    }
                }
                Equal(r) => {
                    for r in r {
                        print!("{r}")
                    }
                }
            }
        }
        println!();
    } else {
        // The line only adds or only removes chars, print a single line highlighting their differences.
        print!("{}", "~".yellow());
        for char in diff {
            match char {
                Remove(l) => {
                    for l in l {
                        print!("{}", l.to_string().on_red())
                    }
                }
                Equal(w) => {
                    for w in w {
                        print!("{w}")
                    }
                }
                Insert(r) => {
                    for r in r {
                        print!("{}", r.to_string().on_green())
                    }
                }
                Replace(l, r) => {
                    for l in l {
                        print!("{}", l.to_string().on_red())
                    }
                    for r in r {
                        print!("{}", r.to_string().on_green())
                    }
                }
            }
        }
        println!();
    }
}

fn has_both_insertions_and_deletions(diff: &[DiffOp<'_, &str>]) -> bool {
    let mut seen_l = false;
    let mut seen_r = false;
    for char in diff {
        let is_whitespace = |s: &[&str]| s.iter().any(|s| s.chars().any(|s| s.is_whitespace()));
        match char {
            Insert(l) if !is_whitespace(l) => seen_l = true,
            Remove(r) if !is_whitespace(r) => seen_r = true,
            Replace(l, r) if !is_whitespace(l) && !is_whitespace(r) => return true,
            _ => {}
        }
    }
    seen_l && seen_r
}

pub fn print_diff(expected: &[u8], actual: &[u8]) {
    let expected_str = String::from_utf8_lossy(expected);
    let actual_str = String::from_utf8_lossy(actual);

    if expected_str.as_bytes() != expected || actual_str.as_bytes() != actual {
        println!(
            "{}",
            "Non-UTF8 characters in output, diff may be imprecise.".red()
        );
    }

    let pat = |c: char| c.is_whitespace() && c != ' ' && c != '\n' && c != '\r';
    let expected_str = expected_str.replace(pat, "░");
    let actual_str = actual_str.replace(pat, "░");

    for r in diff_lines(&expected_str, &actual_str).diff() {
        row(r);
    }
    println!()
}
