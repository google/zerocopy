// Copyright (c) The nextest Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use chrono::DateTime;
use goldenfile::Mint;
use owo_colors::OwoColorize;
use pretty_assertions::assert_eq;
use quick_junit::{
    NonSuccessKind, Property, Report, TestCase, TestCaseStatus, TestRerun, TestSuite,
};
use std::time::Duration;

#[test]
fn fixtures() {
    let mut mint = Mint::new("tests/fixtures");

    let f = mint
        .new_goldenfile("basic_report.xml")
        .expect("creating new goldenfile succeeds");

    let basic_report = basic_report();
    basic_report
        .serialize(f)
        .expect("serializing basic_report succeeds");
}

fn basic_report() -> Report {
    let mut report = Report::new("my-test-run");
    report.set_timestamp(
        DateTime::parse_from_rfc2822("Thu, 1 Apr 2021 10:52:37 -0800")
            .expect("valid RFC2822 datetime"),
    );
    report.set_time(Duration::new(42, 235_000_000));

    let mut test_suite = TestSuite::new("testsuite0");
    test_suite.set_timestamp(
        DateTime::parse_from_rfc2822("Thu, 1 Apr 2021 10:52:39 -0800")
            .expect("valid RFC2822 datetime"),
    );

    // ---

    let test_case_status = TestCaseStatus::success();
    let mut test_case = TestCase::new("testcase0", test_case_status);
    test_case.set_system_out("testcase0-output");
    test_suite.add_test_case(test_case);

    // ---

    let mut test_case_status = TestCaseStatus::non_success(NonSuccessKind::Failure);
    test_case_status
        .set_description("this is the failure description")
        .set_message("testcase1-message");
    let mut test_case = TestCase::new("testcase1", test_case_status);
    test_case
        .set_system_err("some sort of failure output")
        .set_time(Duration::from_millis(4242));
    test_suite.add_test_case(test_case);

    // ---

    let mut test_case_status = TestCaseStatus::non_success(NonSuccessKind::Error);
    test_case_status
        .set_description("testcase2 error description")
        .set_type("error type");
    let mut test_case = TestCase::new("testcase2", test_case_status);
    test_case.set_time(Duration::from_millis(421580));
    test_suite.add_test_case(test_case);

    // ---

    let mut test_case_status = TestCaseStatus::skipped();
    test_case_status
        .set_type("skipped type")
        .set_message("skipped message");
    // no description to test that.
    let mut test_case = TestCase::new("testcase3", test_case_status);
    test_case
        .set_timestamp(
            DateTime::parse_from_rfc2822("Thu, 1 Apr 2021 11:52:41 -0700")
                .expect("valid RFC2822 datetime"),
        )
        .set_assertions(20)
        .set_system_out("testcase3 output")
        .set_system_err("testcase3 error");
    test_suite.add_test_case(test_case);

    // ---

    let mut test_case_status = TestCaseStatus::success();

    let mut test_rerun = TestRerun::new(NonSuccessKind::Failure);
    test_rerun
        .set_type("flaky failure type")
        .set_description("this is a flaky failure description");
    test_case_status.add_rerun(test_rerun);

    let mut test_rerun = TestRerun::new(NonSuccessKind::Error);
    test_rerun
        .set_type("flaky error type")
        .set_system_out("flaky system output")
        .set_system_err(format!(
            "flaky system error with {}",
            "ANSI escape codes".blue()
        ))
        .set_stack_trace("flaky stack trace")
        .set_description("flaky error description");
    test_case_status.add_rerun(test_rerun);

    let mut test_case = TestCase::new("testcase4", test_case_status);
    test_case.set_time(Duration::from_millis(661661));
    test_suite.add_test_case(test_case);

    // ---

    let mut test_case_status = TestCaseStatus::non_success(NonSuccessKind::Failure);
    test_case_status.set_description("main test failure description");

    let mut test_rerun = TestRerun::new(NonSuccessKind::Failure);
    test_rerun.set_type("retry failure type");
    test_case_status.add_rerun(test_rerun);

    let mut test_rerun = TestRerun::new(NonSuccessKind::Error);
    test_rerun
        .set_type("retry error type")
        .set_system_out("retry error system output")
        .set_stack_trace("retry error stack trace");
    test_case_status.add_rerun(test_rerun);

    let mut test_case = TestCase::new("testcase5", test_case_status);
    test_case.set_time(Duration::from_millis(156));
    test_suite.add_test_case(test_case);

    let test_case_status = TestCaseStatus::success();
    let mut test_case = TestCase::new("testcase6", test_case_status);
    test_case.add_property(Property::new("step", "foobar"));
    test_suite.add_test_case(test_case);

    test_suite.add_property(Property::new("env", "FOOBAR"));

    report.add_test_suite(test_suite);

    report
}

#[test]
fn serialize_roundtrip_examples() {
    // Create a report, serialize it, then deserialize it, and verify they match
    let original_report = basic_report();

    let serialized = original_report.to_string().expect("serialization succeeds");

    let deserialized_report =
        Report::deserialize_from_str(&serialized).expect("deserialization succeeds");

    // Verify top-level attributes.
    assert_eq!(deserialized_report.name, original_report.name);
    assert_eq!(deserialized_report.tests, original_report.tests);
    assert_eq!(deserialized_report.failures, original_report.failures);
    assert_eq!(deserialized_report.errors, original_report.errors);
    assert_eq!(deserialized_report.timestamp, original_report.timestamp);
    assert_eq!(deserialized_report.time, original_report.time);

    assert_eq!(
        deserialized_report.test_suites.len(),
        original_report.test_suites.len()
    );

    assert_eq!(deserialized_report.test_suites, original_report.test_suites);
}

#[test]
fn deserialize_minimal_report() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="minimal" tests="0" failures="0" errors="0">
</testsuites>
"#;

    let report = Report::deserialize_from_str(xml).expect("deserializing minimal report succeeds");
    assert_eq!(report.name.as_str(), "minimal");
    assert_eq!(report.tests, 0);
    assert_eq!(report.failures, 0);
    assert_eq!(report.errors, 0);
    assert_eq!(report.test_suites.len(), 0);
}

#[test]
fn deserialize_empty_test_suite() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0">
    <testsuite name="empty-suite" tests="0" disabled="0" errors="0" failures="0"/>
</testsuites>
"#;

    let report =
        Report::deserialize_from_str(xml).expect("deserializing report with empty suite succeeds");
    assert_eq!(report.test_suites.len(), 1);
    assert_eq!(report.test_suites[0].name.as_str(), "empty-suite");
    assert_eq!(report.test_suites[0].test_cases.len(), 0);
}

#[test]
fn deserialize_with_extra_attributes() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0" custom-attr="custom-value">
        <testcase name="test" custom-test-attr="test-value"/>
    </testsuite>
</testsuites>
"#;

    let report = Report::deserialize_from_str(xml)
        .expect("deserializing report with extra attributes succeeds");
    let suite = &report.test_suites[0];

    // Verify extra attributes are captured
    assert_eq!(suite.extra.len(), 1);
    assert_eq!(
        suite.extra.get("custom-attr").unwrap().as_str(),
        "custom-value"
    );

    let test_case = &suite.test_cases[0];
    assert_eq!(test_case.extra.len(), 1);
    assert_eq!(
        test_case.extra.get("custom-test-attr").unwrap().as_str(),
        "test-value"
    );
}

#[test]
fn deserialize_error_handling() {
    // Test missing required attribute
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites tests="0" failures="0" errors="0">
</testsuites>
"#;
    let result = Report::deserialize_from_str(xml);
    assert!(result.is_err());

    // Test invalid XML
    let xml = r#"<testsuites name="test" tests="0">"#;
    let result = Report::deserialize_from_str(xml);
    assert!(result.is_err());

    // Test invalid integer
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="not-a-number" failures="0" errors="0">
</testsuites>
"#;
    let result = Report::deserialize_from_str(xml);
    assert!(result.is_err());
}
