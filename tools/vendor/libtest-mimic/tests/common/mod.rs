use std::{path::Path, iter::repeat_with, collections::HashMap};
use pretty_assertions::assert_eq;

use libtest_mimic::{run, Arguments, Conclusion, Trial};


const TEMPDIR: &str = env!("CARGO_TARGET_TMPDIR");

pub fn args<const N: usize>(args: [&str; N]) -> Arguments {
    let mut v = vec!["<dummy-executable>"];
    v.extend(args);
    Arguments::from_iter(v)
}

pub fn do_run(mut args: Arguments, tests: Vec<Trial>) -> (Conclusion, String) {
    // Create path to temporary file.
    let suffix = repeat_with(fastrand::alphanumeric).take(10).collect::<String>();
    let path = Path::new(&TEMPDIR).join(format!("libtest_mimic_output_{suffix}.txt"));

    args.logfile = Some(path.display().to_string());

    let c = run(&args, tests);
    let output = std::fs::read_to_string(&path)
        .expect("Can't read temporary logfile");
    std::fs::remove_file(&path)
        .expect("Can't remove temporary logfile");
    (c, output)
}

/// Removes shared indentation so that at least one line has no indentation
/// (no leading spaces).
pub fn clean_expected_log(s: &str) -> String {
    let shared_indent = s.lines()
        .filter(|l| l.contains(|c| c != ' '))
        .map(|l| l.bytes().take_while(|b| *b == b' ').count())
        .min()
        .expect("empty expected");

    let mut out = String::new();
    for line in s.lines() {
        use std::fmt::Write;
        let cropped = if line.len() <= shared_indent {
            line
        } else {
            &line[shared_indent..]
        };
        writeln!(out, "{}", cropped).unwrap();
    }

    out
}

/// Best effort tool to check certain things about a log that might have all
/// tests randomly ordered.
pub fn assert_reordered_log(actual: &str, num: u64, expected_lines: &[&str], tail: &str) {
    let actual = actual.trim();
    let (first_line, rest) = actual.split_once('\n').expect("log has too few lines");
    let (middle, last_line) = rest.rsplit_once('\n').expect("log has too few lines");


    assert_eq!(first_line, &format!("running {} test{}", num, if num == 1 { "" } else { "s" }));
    assert!(last_line.contains(tail));

    let mut actual_lines = HashMap::new();
    for line in middle.lines().map(|l| l.trim()).filter(|l| !l.is_empty()) {
        *actual_lines.entry(line).or_insert(0) += 1;
    }

    for expected in expected_lines.iter().map(|l| l.trim()).filter(|l| !l.is_empty()) {
        match actual_lines.get_mut(expected) {
            None | Some(0) => panic!("expected line \"{expected}\" not in log"),
            Some(num) => *num -= 1,
        }
    }

    actual_lines.retain(|_, v| *v != 0);
    if !actual_lines.is_empty() {
        panic!("Leftover output in log: {actual_lines:#?}");
    }
}

/// Like `assert_eq`, but cleans the expected string (removes indendation). Also
/// normalizes the "finished in" time if `$expected` ends with "finished in
/// 0.00s".
#[macro_export]
macro_rules! assert_log {
    ($actual:expr, $expected:expr) => {
        let mut actual = $actual.trim().to_owned();
        let expected = crate::common::clean_expected_log($expected);
        let expected = expected.trim();

        if expected.ends_with("finished in 0.00s") {
            // If we don't find that pattern, the assert below will fail anyway.
            if let Some(pos) = actual.rfind("finished in") {
                actual.truncate(pos);
                actual.push_str("finished in 0.00s");
            }
        }

        if let Some(pos) = actual.rfind("\"exec_time\":") {
            actual.truncate(pos);
            actual.push_str("\"exec_time\": 0.000000000 }");
        }

        assert_eq!(actual, expected);
    };
}

pub fn check(
    mut args: Arguments,
    mut tests: impl FnMut() -> Vec<Trial>,
    num_running_tests: u64,
    expected_conclusion: Conclusion,
    expected_output: &str,
) {
    // Run in single threaded mode
    args.test_threads = Some(1);
    let (c, out) = do_run(args.clone(), tests());
    let expected = crate::common::clean_expected_log(expected_output);
    let actual = {
        let lines = out.trim().lines().skip(1).collect::<Vec<_>>();
        lines[..lines.len() - 1].join("\n")
    };
    assert_eq!(actual.trim(), expected.trim());
    assert_eq!(c, expected_conclusion);

    // Run in multithreaded mode.
    let (c, out) = do_run(args, tests());
    assert_reordered_log(
        &out,
        num_running_tests,
        &expected_output.lines().collect::<Vec<_>>(),
        &conclusion_to_output(&c),
    );
    assert_eq!(c, expected_conclusion);
}

fn conclusion_to_output(c: &Conclusion) -> String {
    let Conclusion { num_filtered_out, num_passed, num_failed, num_ignored, num_measured } = *c;
    format!(
        "test result: {}. {} passed; {} failed; {} ignored; {} measured; {} filtered out;",
        if num_failed > 0 { "FAILED" } else { "ok" },
        num_passed,
        num_failed,
        num_ignored,
        num_measured,
        num_filtered_out,
    )
}
