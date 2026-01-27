// Copyright (c) The nextest Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Tests for CDATA section handling in deserialization.

use quick_junit::Report;

#[test]
fn test_cdata_in_system_out() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out><![CDATA[Output with <special> characters & symbols]]></system-out>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let test_case = &report.test_suites[0].test_cases[0];
    assert_eq!(
        test_case.system_out.as_ref().map(|s| s.as_str()),
        Some("Output with <special> characters & symbols")
    );
}

#[test]
fn test_cdata_in_system_err() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-err><![CDATA[Error with <tags> and & ampersands]]></system-err>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let test_case = &report.test_suites[0].test_cases[0];
    assert_eq!(
        test_case.system_err.as_ref().map(|s| s.as_str()),
        Some("Error with <tags> and & ampersands")
    );
}

#[test]
fn test_cdata_in_failure_message() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure type="AssertionError" message="Test failed"><![CDATA[
Stack trace with <xml> tags:
  at function() line 10
  Expected: <value>
  Got: <different>
]]></failure>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let test_case = &report.test_suites[0].test_cases[0];

    match &test_case.status {
        quick_junit::TestCaseStatus::NonSuccess { description, .. } => {
            let desc = description.as_ref().unwrap().as_str();
            assert!(desc.contains("Stack trace with <xml> tags"));
            assert!(desc.contains("Expected: <value>"));
            assert!(desc.contains("Got: <different>"));
        }
        _ => panic!("Expected NonSuccess status"),
    }
}

#[test]
fn test_cdata_in_error_description() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="1">
    <testsuite name="suite" tests="1" disabled="0" errors="1" failures="0">
        <testcase name="test">
            <error type="Exception" message="Error occurred"><![CDATA[Exception details:
<Error> & <Details>
Line 1: Something went wrong
]]></error>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let test_case = &report.test_suites[0].test_cases[0];

    match &test_case.status {
        quick_junit::TestCaseStatus::NonSuccess { description, .. } => {
            let desc = description.as_ref().unwrap().as_str();
            assert!(desc.contains("Exception details"));
            assert!(desc.contains("<Error> & <Details>"));
        }
        _ => panic!("Expected NonSuccess status"),
    }
}

#[test]
fn test_cdata_with_special_characters() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out><![CDATA[<test>
  Special: & < > " '
  Math: 2 < 3 && 4 > 1
  XML: <tag attr="value">content</tag>
]]></system-out>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let test_case = &report.test_suites[0].test_cases[0];
    let output = test_case.system_out.as_ref().unwrap().as_str();

    assert!(output.contains("Special: & < > \" '"));
    assert!(output.contains("Math: 2 < 3 && 4 > 1"));
    assert!(output.contains("<tag attr=\"value\">content</tag>"));
}

#[test]
fn test_cdata_with_nested_cdata_end_marker() {
    // CDATA sections cannot contain "]]>" but this tests handling of content
    // that looks similar
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out><![CDATA[Text with ]] and > symbols separately]]></system-out>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let test_case = &report.test_suites[0].test_cases[0];
    assert_eq!(
        test_case.system_out.as_ref().map(|s| s.as_str()),
        Some("Text with ]] and > symbols separately")
    );
}

#[test]
fn test_mixed_text_and_cdata() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out>Regular text <![CDATA[<CDATA content>]]> more text</system-out>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let test_case = &report.test_suites[0].test_cases[0];
    assert_eq!(
        test_case.system_out.as_ref().map(|s| s.as_str()),
        Some("Regular text <CDATA content> more text")
    );
}

#[test]
fn test_empty_cdata() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out><![CDATA[]]></system-out>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let test_case = &report.test_suites[0].test_cases[0];
    assert_eq!(test_case.system_out.as_ref().map(|s| s.as_str()), Some(""));
}

#[test]
fn test_cdata_in_testsuite_system_out() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <system-out><![CDATA[Suite output with <special> chars]]></system-out>
        <testcase name="test" />
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let suite = &report.test_suites[0];
    assert_eq!(
        suite.system_out.as_ref().map(|s| s.as_str()),
        Some("Suite output with <special> chars")
    );
}

#[test]
fn test_cdata_in_testsuite_system_err() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <system-err><![CDATA[Suite error with & and <brackets>]]></system-err>
        <testcase name="test" />
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let suite = &report.test_suites[0];
    assert_eq!(
        suite.system_err.as_ref().map(|s| s.as_str()),
        Some("Suite error with & and <brackets>")
    );
}

#[test]
fn test_cdata_with_multiline_content() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out><![CDATA[Line 1
Line 2 with <tags>
Line 3 with & symbols
Line 4]]></system-out>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let test_case = &report.test_suites[0].test_cases[0];
    let output = test_case.system_out.as_ref().unwrap().as_str();

    assert!(output.contains("Line 1\n"));
    assert!(output.contains("Line 2 with <tags>\n"));
    assert!(output.contains("Line 3 with & symbols\n"));
    assert!(output.contains("Line 4"));
}

#[test]
fn test_cdata_roundtrip() {
    // Test that we can parse CDATA and the content remains correct
    // (Note: we don't necessarily serialize back to CDATA, we just need the content to be correct)
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out><![CDATA[<xml>&content</xml>]]></system-out>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).expect("should parse XML with CDATA");
    let test_case = &report.test_suites[0].test_cases[0];
    assert_eq!(
        test_case.system_out.as_ref().map(|s| s.as_str()),
        Some("<xml>&content</xml>")
    );

    // Verify we can serialize (it will use proper escaping)
    let serialized = report.to_string().expect("should serialize report");

    // When we serialize, special characters should be escaped
    assert!(serialized.contains("&lt;xml&gt;&amp;content&lt;/xml&gt;"));

    // And we should be able to parse it back
    let report2 =
        Report::deserialize_from_str(&serialized).expect("should re-parse serialized XML");
    let test_case2 = &report2.test_suites[0].test_cases[0];
    assert_eq!(
        test_case2.system_out.as_ref().map(|s| s.as_str()),
        Some("<xml>&content</xml>")
    );
}
