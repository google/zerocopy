// Copyright (c) The nextest Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Tests for whitespace trimming in XML text content.

use quick_junit::Report;

#[test]
fn test_failure_description_with_leading_trailing_whitespace() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure>
                Test failed with error
            </failure>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with whitespace");
    let test_case = &report.test_suites[0].test_cases[0];

    if let quick_junit::TestCaseStatus::NonSuccess {
        kind: _,
        message: _,
        ty: _,
        description,
        reruns: _,
    } = &test_case.status
    {
        assert_eq!(
            description.as_ref().unwrap().as_str(),
            "Test failed with error"
        );
    } else {
        panic!("Expected NonSuccess status");
    }
}

#[test]
fn test_error_description_with_whitespace() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="1">
    <testsuite name="suite" tests="1" disabled="0" errors="1" failures="0">
        <testcase name="test">
            <error>   Stack trace here   </error>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with whitespace");
    let test_case = &report.test_suites[0].test_cases[0];

    if let quick_junit::TestCaseStatus::NonSuccess {
        kind: _,
        message: _,
        ty: _,
        description,
        reruns: _,
    } = &test_case.status
    {
        assert_eq!(description.as_ref().unwrap().as_str(), "Stack trace here");
    } else {
        panic!("Expected NonSuccess status");
    }
}

#[test]
fn test_system_out_with_whitespace() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out>
                Output line 1
                Output line 2
            </system-out>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with whitespace");
    let test_case = &report.test_suites[0].test_cases[0];

    let output = test_case.system_out.as_ref().unwrap().as_str();
    // Should be trimmed of leading/trailing whitespace
    assert_eq!(output, "Output line 1\n                Output line 2");
}

#[test]
fn test_system_err_with_whitespace() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-err>  Error output  </system-err>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with whitespace");
    let test_case = &report.test_suites[0].test_cases[0];

    let output = test_case.system_err.as_ref().unwrap().as_str();
    assert_eq!(output, "Error output");
}

#[test]
fn test_stack_trace_with_whitespace() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure>Initial failure</failure>
            <rerunFailure>
                <stackTrace>
                    at line 1
                    at line 2
                </stackTrace>
            </rerunFailure>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with stack trace");
    let test_case = &report.test_suites[0].test_cases[0];

    if let quick_junit::TestCaseStatus::NonSuccess {
        kind: _,
        message: _,
        ty: _,
        description: _,
        reruns,
    } = &test_case.status
    {
        assert_eq!(reruns.len(), 1, "Should have one rerun");
        let stack_trace = reruns[0].stack_trace.as_ref().unwrap().as_str();
        assert_eq!(stack_trace, "at line 1\n                    at line 2");
    } else {
        panic!("Expected NonSuccess status");
    }
}

#[test]
fn test_cdata_description_with_whitespace() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure><![CDATA[
                CDATA content with whitespace
            ]]></failure>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse CDATA with whitespace");
    let test_case = &report.test_suites[0].test_cases[0];

    if let quick_junit::TestCaseStatus::NonSuccess {
        kind: _,
        message: _,
        ty: _,
        description,
        reruns: _,
    } = &test_case.status
    {
        assert_eq!(
            description.as_ref().unwrap().as_str(),
            "CDATA content with whitespace"
        );
    } else {
        panic!("Expected NonSuccess status");
    }
}

#[test]
fn test_testsuite_system_out_with_whitespace() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0">
    <testsuite name="suite" tests="0" disabled="0" errors="0" failures="0">
        <system-out>
            Suite output
        </system-out>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse testsuite system-out");
    let suite = &report.test_suites[0];

    let output = suite.system_out.as_ref().unwrap().as_str();
    assert_eq!(output, "Suite output");
}
