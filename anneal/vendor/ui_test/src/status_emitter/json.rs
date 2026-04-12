use super::RevisionStyle;
use super::StatusEmitter;
use super::Summary;
use super::TestStatus;
use crate::test_result::TestResult;
use crate::TestOk;

use std::boxed::Box;
use std::fmt::Debug;
use std::path::{Path, PathBuf};

use bstr::ByteSlice;

// MAINTENANCE REGION START

// When integrating with a new libtest version, update all xxx_event functions.

fn suite_end_event(
    failed: usize,
    filtered_out: usize,
    ignored: usize,
    passed: usize,
    status: &str,
) -> String {
    // Adapted from test::formatters::json::write_run_finish().
    format!(
        r#"{{ "type": "suite", "event": "{status}", "passed": {passed}, "failed": {failed}, "ignored": {ignored}, "measured": 0, "filtered_out": {filtered_out} }}"#
    )
}

fn suite_start_event() -> String {
    // Adapted from test::formatters::json::write_run_start().
    String::from(r#"{ "type": "suite", "event": "started" }"#)
}

fn test_end_event(name: &str, revision: &str, path: &Path, status: &str, diags: &str) -> String {
    let name_attribute = make_name_attribute(name, revision, path);
    let stdout_attribute = make_stdout_attribute(diags);

    // Adapted from test::formatters::json::write_event().
    format!(r#"{{ "type": "test", "event": "{status}"{name_attribute}{stdout_attribute} }}"#)
}

fn test_start_event(name: &str, revision: &str, path: &Path) -> String {
    let name_attribute = make_name_attribute(name, revision, path);

    // Adapted from test::formatters::json::write_test_start().
    format!(r#"{{ "type": "test", "event": "started"{name_attribute} }}"#)
}

// MAINTENANCE REGION END

fn make_name_attribute(name: &str, revision: &str, path: &Path) -> String {
    let path_display = path.display();
    let escaped_value =
        serde_json::to_string(&format!("{name} ({revision}) - {path_display}")).unwrap();
    format!(r#", "name": {escaped_value}"#)
}

fn make_stdout_attribute(diags: &str) -> String {
    if diags.is_empty() {
        String::new()
    } else {
        let escaped_diags = serde_json::to_string(diags).unwrap();
        format!(r#", "stdout": {escaped_diags}"#)
    }
}

/// A JSON output emitter.
#[derive(Clone)]
pub struct JSON {}

impl JSON {
    /// Create a new instance of a JSON output emitter.
    pub fn new() -> Self {
        println!("{}", suite_start_event());

        JSON {}
    }
}

impl Default for JSON {
    fn default() -> Self {
        Self::new()
    }
}

impl StatusEmitter for JSON {
    /// Create a report about the entire test run at the end.
    fn finalize(
        &self,
        failed: usize,
        succeeded: usize,
        ignored: usize,
        filtered: usize,
        aborted: bool,
    ) -> Box<dyn Summary> {
        let status = if aborted || failed > 0 {
            "failed"
        } else {
            "ok"
        };

        println!(
            "{}",
            suite_end_event(failed, filtered, ignored, succeeded, status)
        );

        Box::new(())
    }

    /// Invoked the moment we know a test will later be run.
    /// Emits a JSON start event.
    fn register_test(&self, path: PathBuf) -> Box<dyn TestStatus + 'static> {
        let name = path.to_str().unwrap().to_string();
        let revision = String::new();

        println!("{}", test_start_event(&name, &revision, &path));

        Box::new(JSONStatus {
            name,
            path,
            revision: String::new(),
            style: RevisionStyle::Show,
        })
    }
}

/// Information about a specific test run.
pub struct JSONStatus {
    name: String,
    path: PathBuf,
    revision: String,
    style: RevisionStyle,
}

impl TestStatus for JSONStatus {
    /// A test has finished, handle the result immediately.
    fn done(&self, result: &TestResult, aborted: bool) {
        let status = if aborted {
            "timeout"
        } else {
            match result {
                Ok(TestOk::Ignored) => "ignored",
                Ok(TestOk::Ok) => "ok",
                Err(_) => "failed",
            }
        };
        let diags = if let Err(errored) = result {
            let command = errored.command.as_str();
            let stdout = errored.stderr.to_str_lossy();
            let stderr = errored.stdout.to_str_lossy();

            format!(r#"command: <{command}> stdout: <{stdout}> stderr: <{stderr}>"#)
        } else {
            String::new()
        };

        println!(
            "{}",
            test_end_event(&self.name, &self.revision, self.path(), status, &diags)
        );
    }

    /// Invoked before each failed test prints its errors along with a drop guard that can
    /// get invoked afterwards.
    fn failed_test<'a>(
        &'a self,
        _cmd: &'a str,
        _stderr: &'a [u8],
        _stdout: &'a [u8],
    ) -> Box<dyn Debug + 'a> {
        Box::new(())
    }

    /// Create a copy of this test for a new path.
    fn for_path(&self, path: &Path) -> Box<dyn TestStatus> {
        let status = JSONStatus {
            name: self.name.clone(),
            path: path.to_path_buf(),
            revision: self.revision.clone(),
            style: self.style,
        };
        Box::new(status)
    }

    /// Create a copy of this test for a new revision.
    fn for_revision(&self, revision: &str, style: RevisionStyle) -> Box<dyn TestStatus> {
        let status = JSONStatus {
            name: self.name.clone(),
            path: self.path.clone(),
            revision: revision.to_owned(),
            style,
        };
        Box::new(status)
    }

    /// The path of the test file.
    fn path(&self) -> &Path {
        &self.path
    }

    /// The revision, usually an empty string.
    fn revision(&self) -> &str {
        &self.revision
    }
}

#[test]
fn suite_end_event_constructs_event() {
    assert_eq!(
        suite_end_event(
            12, // failed
            34, // filtered_out
            56, // ignored
            78, // passed
            "status"
        ),
        r#"{ "type": "suite", "event": "status", "passed": 78, "failed": 12, "ignored": 56, "measured": 0, "filtered_out": 34 }"#
    );
}

#[test]
fn suite_start_event_constructs_event() {
    assert_eq!(
        suite_start_event(),
        r#"{ "type": "suite", "event": "started" }"#
    );
}

#[test]
fn test_end_event_constructs_event() {
    assert_eq!(
        test_end_event("name", "revision", Path::new("aaa/bbb"), "status", "diags"),
        r#"{ "type": "test", "event": "status", "name": "name (revision) - aaa/bbb", "stdout": "diags" }"#
    );
}

#[test]
fn test_end_event_constructs_event_with_escapes() {
    assert_eq!(
        test_end_event(
            r#"aaa\bbb"#,
            r#"ccc ddd\eee"#,
            Path::new(r#"fff\ggg"#),
            "status",
            r#""rustc" "--error-format=json""#
        ),
        r#"{ "type": "test", "event": "status", "name": "aaa\\bbb (ccc ddd\\eee) - fff\\ggg", "stdout": "\"rustc\" \"--error-format=json\"" }"#
    );
}

#[test]
fn test_end_event_constructs_event_without_revision() {
    assert_eq!(
        test_end_event("name", "", Path::new("aaa/bbb"), "status", "diags"),
        r#"{ "type": "test", "event": "status", "name": "name () - aaa/bbb", "stdout": "diags" }"#
    );
}

#[test]
fn test_end_event_constructs_event_without_stdout() {
    assert_eq!(
        test_end_event("name", "revision", Path::new("aaa/bbb"), "status", ""),
        r#"{ "type": "test", "event": "status", "name": "name (revision) - aaa/bbb" }"#
    );
}

#[test]
fn test_start_event_constructs_event() {
    assert_eq!(
        test_start_event("name", "revision", Path::new("aaa/bbb")),
        r#"{ "type": "test", "event": "started", "name": "name (revision) - aaa/bbb" }"#
    );
}

#[test]
fn test_start_event_constructs_event_with_escapes() {
    assert_eq!(
        test_start_event(r#"aaa\bbb"#, r#"ccc ddd\eee"#, Path::new(r#"fff\ggg"#)),
        r#"{ "type": "test", "event": "started", "name": "aaa\\bbb (ccc ddd\\eee) - fff\\ggg" }"#
    );
}
