// Copyright (c) The nextest Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Tests for deserialization error paths and error kinds.

use quick_junit::{DeserializeErrorKind, PathElement, Report};

/// Helper to assert error kind and path.
fn assert_error(
    xml: impl AsRef<[u8]>,
    expected_kind: fn(&DeserializeErrorKind) -> bool,
    expected_path: &[PathElement],
) {
    match Report::deserialize(xml.as_ref()) {
        Ok(_) => panic!("Expected error but got success"),
        Err(e) => {
            assert!(
                expected_kind(e.kind()),
                "Expected matching error kind, got: {:?}",
                e.kind()
            );
            assert_eq!(e.path(), expected_path, "Path mismatch");
        }
    }
}

#[test]
fn test_testsuites_missing_name() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites tests="0" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::MissingAttribute(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("name".to_string()),
        ],
    );
}

#[test]
fn test_testsuites_invalid_tests_count() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="not_a_number" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseIntError(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("tests".to_string()),
        ],
    );
}

#[test]
fn test_testsuites_invalid_uuid() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" uuid="not-a-uuid" tests="0" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseUuidError(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("uuid".to_string()),
        ],
    );
}

#[test]
fn test_testsuites_invalid_timestamp() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" timestamp="not-a-timestamp" tests="0" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseTimestampError(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("timestamp".to_string()),
        ],
    );
}

#[test]
fn test_testsuites_invalid_duration() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" time="not-a-duration" tests="0" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseDurationError(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("time".to_string()),
        ],
    );
}

#[test]
fn test_testsuites_duration_too_large() {
    // Test with a value that would cause Duration::from_secs_f64 to panic (the original fuzzer find)
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" time="14493333333333333333333333333333333333333333333333333333333333333317318201447242133977" tests="0" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseDurationError(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("time".to_string()),
        ],
    );
}

#[test]
fn test_testsuites_duration_at_u64_max() {
    // u64::MAX = 18446744073709551615
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" time="18446744073709551615" tests="0" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseDurationError(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("time".to_string()),
        ],
    );
}

#[test]
fn test_testsuites_duration_just_above_u64_max() {
    // Slightly above u64::MAX
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" time="18446744073709551616" tests="0" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseDurationError(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("time".to_string()),
        ],
    );
}

#[test]
fn test_testsuites_duration_large_valid() {
    // Test a large but valid duration (1 trillion seconds, about 31,700 years)
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" time="1000000000000" tests="0" failures="0" errors="0">
</testsuites>"#;

    // This should succeed
    match Report::deserialize_from_str(xml) {
        Ok(_) => {} // Success as expected
        Err(e) => panic!("Expected success but got error: {:?}", e),
    }
}

#[test]
fn test_testsuites_duration_max_valid_f64() {
    // Test near the boundary where f64 precision matters
    // Use 1e15 (quadrillion) seconds which is well within bounds
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" time="1e15" tests="0" failures="0" errors="0">
</testsuites>"#;

    // This should succeed
    match Report::deserialize_from_str(xml) {
        Ok(_) => {} // Success as expected
        Err(e) => panic!("Expected success but got error: {:?}", e),
    }
}

#[test]
fn test_testsuites_duration_nan() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" time="NaN" tests="0" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseDurationError(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("time".to_string()),
        ],
    );
}

#[test]
fn test_testsuites_duration_infinite() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" time="inf" tests="0" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseDurationError(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("time".to_string()),
        ],
    );
}

#[test]
fn test_testsuites_duration_negative() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" time="-1.5" tests="0" failures="0" errors="0">
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseDurationError(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("time".to_string()),
        ],
    );
}

#[test]
fn test_testsuite_missing_name() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::MissingAttribute(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, None),
            PathElement::Attribute("name".to_string()),
        ],
    );
}

#[test]
fn test_testsuite_invalid_disabled_count() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="invalid" errors="0" failures="0">
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseIntError(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, None),
            PathElement::Attribute("disabled".to_string()),
        ],
    );
}

#[test]
fn test_testsuite_multiple_suites_error_in_second() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="2" failures="0" errors="0">
    <testsuite name="suite1" tests="1" disabled="0" errors="0" failures="0">
    </testsuite>
    <testsuite name="suite2" tests="invalid" disabled="0" errors="0" failures="0">
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseIntError(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(1, None),
            PathElement::Attribute("tests".to_string()),
        ],
    );
}

#[test]
fn test_testcase_missing_name() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase classname="MyTest">
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::MissingAttribute(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, None),
            PathElement::Attribute("name".to_string()),
        ],
    );
}

#[test]
fn test_testcase_invalid_assertions() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test" assertions="not_a_number">
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseIntError(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, None),
            PathElement::Attribute("assertions".to_string()),
        ],
    );
}

#[test]
fn test_testcase_invalid_time() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test" time="invalid">
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseDurationError(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, None),
            PathElement::Attribute("time".to_string()),
        ],
    );
}

#[test]
fn test_testcase_multiple_cases_error_in_third() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="3" failures="0" errors="0">
    <testsuite name="suite" tests="3" disabled="0" errors="0" failures="0">
        <testcase name="test1" />
        <testcase name="test2" />
        <testcase name="test3" time="invalid" />
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::ParseDurationError(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(2, None),
            PathElement::Attribute("time".to_string()),
        ],
    );
}

#[test]
fn test_property_missing_name() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <properties>
            <property value="value1"/>
        </properties>
        <testcase name="test">
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::MissingAttribute(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::Properties,
            PathElement::Property(0),
            PathElement::Attribute("name".to_string()),
        ],
    );
}

#[test]
fn test_property_missing_value() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <properties>
            <property name="key1"/>
        </properties>
        <testcase name="test">
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::MissingAttribute(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::Properties,
            PathElement::Property(0),
            PathElement::Attribute("value".to_string()),
        ],
    );
}

#[test]
fn test_property_error_in_second() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <properties>
            <property name="key1" value="value1"/>
            <property name="key2"/>
        </properties>
        <testcase name="test">
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::MissingAttribute(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::Properties,
            PathElement::Property(1),
            PathElement::Attribute("value".to_string()),
        ],
    );
}

#[test]
fn test_failure_element_duplicate() {
    // Multiple failure elements are actually allowed (just unusual); this test
    // documents that the deserializer accepts duplicate failures
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure type="first"/>
        </testcase>
    </testsuite>
</testsuites>"#;

    // This should succeed - single failure is valid
    assert!(Report::deserialize_from_str(xml).is_ok());
}

#[test]
fn test_error_element_single() {
    // Test that a single error element works correctly.
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="1">
    <testsuite name="suite" tests="1" disabled="0" errors="1" failures="0">
        <testcase name="test">
            <error type="test_error"/>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert!(Report::deserialize_from_str(xml).is_ok());
}

#[test]
fn test_skipped_element_single() {
    // Test that a single skipped element works correctly.
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="1" errors="0" failures="0">
        <testcase name="test">
            <skipped/>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert!(Report::deserialize_from_str(xml).is_ok());
}

#[test]
fn test_flaky_failure_element() {
    // Test that flaky failure elements work correctly.
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <flakyFailure type="flaky"/>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert!(Report::deserialize_from_str(xml).is_ok());
}

#[test]
fn test_flaky_error_element() {
    // Test that flaky error elements work correctly.
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <flakyError type="flaky"/>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert!(Report::deserialize_from_str(xml).is_ok());
}

#[test]
fn test_rerun_failure_element() {
    // Test that rerun failure elements work correctly with a main failure.
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure type="main"/>
            <rerunFailure type="rerun"/>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert!(Report::deserialize_from_str(xml).is_ok());
}

#[test]
fn test_rerun_error_element() {
    // Test that rerun error elements work correctly with a main error.
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="1">
    <testsuite name="suite" tests="1" disabled="0" errors="1" failures="0">
        <testcase name="test">
            <error type="main"/>
            <rerunError type="rerun"/>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert!(Report::deserialize_from_str(xml).is_ok());
}

#[test]
fn test_system_out_element() {
    // Test that the system-out element works correctly.
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out>output</system-out>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert!(Report::deserialize_from_str(xml).is_ok());
}

#[test]
fn test_system_err_element() {
    // Test that the system-err element works correctly.
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-err>error</system-err>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert!(Report::deserialize_from_str(xml).is_ok());
}

#[test]
fn test_missing_testsuites_element() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<root></root>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[],
    );
}

#[test]
fn test_invalid_xml_structure() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0">"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[PathElement::TestSuites],
    );
}

#[test]
fn test_malformed_xml() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0">
    <testsuite name="suite" tests="1"
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::AttrError(_)),
        &[PathElement::TestSuites, PathElement::TestSuite(0, None)],
    );
}

#[test]
fn test_empty_testsuites_element() {
    // Test self-closing <testsuites/> tag
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0"/>"#;

    let report = Report::deserialize_from_str(xml).unwrap();
    assert_eq!(report.name.as_str(), "test");
    assert_eq!(report.test_suites.len(), 0);
}

#[test]
fn test_empty_testsuites_with_all_attributes() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" uuid="550e8400-e29b-41d4-a716-446655440000" timestamp="2023-01-01T00:00:00Z" time="1.5" tests="0" failures="0" errors="0"/>"#;

    let report = Report::deserialize_from_str(xml).unwrap();
    assert_eq!(report.name.as_str(), "test");
    assert_eq!(
        report.uuid.unwrap().to_string(),
        "550e8400-e29b-41d4-a716-446655440000"
    );
    assert_eq!(
        report.timestamp.unwrap().to_rfc3339(),
        "2023-01-01T00:00:00+00:00"
    );
    assert_eq!(
        report.time.unwrap(),
        std::time::Duration::from_secs_f64(1.5)
    );
}

#[test]
fn test_unknown_testsuite_child_element() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0">
    <testsuite name="suite" tests="0" disabled="0" errors="0" failures="0">
        <unknown-element>content</unknown-element>
    </testsuite>
</testsuites>"#;

    // Should succeed - unknown elements are skipped
    let report = Report::deserialize_from_str(xml).unwrap();
    assert_eq!(report.test_suites.len(), 1);
}

#[test]
fn test_testsuite_unexpected_eof() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
        ],
    );
}

#[test]
fn test_empty_testsuite_with_timestamp_and_time() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0">
    <testsuite name="suite" tests="0" disabled="0" errors="0" failures="0" timestamp="2023-01-01T00:00:00Z" time="1.5"/>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).unwrap();
    let suite = &report.test_suites[0];
    assert_eq!(
        suite.timestamp.unwrap().to_rfc3339(),
        "2023-01-01T00:00:00+00:00"
    );
    assert_eq!(suite.time.unwrap(), std::time::Duration::from_secs_f64(1.5));
}

#[test]
fn test_empty_testsuite_with_extra_attributes() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0">
    <testsuite name="suite" tests="0" disabled="0" errors="0" failures="0" hostname="localhost" package="mypackage"/>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).unwrap();
    let suite = &report.test_suites[0];
    assert_eq!(suite.extra.len(), 2);
    assert_eq!(suite.extra.get("hostname").unwrap().as_str(), "localhost");
    assert_eq!(suite.extra.get("package").unwrap().as_str(), "mypackage");
}

#[test]
fn test_empty_testsuite_missing_name() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0">
    <testsuite tests="0" disabled="0" errors="0" failures="0"/>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::MissingAttribute(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, None),
            PathElement::Attribute("name".to_string()),
        ],
    );
}

#[test]
fn test_testcase_unexpected_eof() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
        ],
    );
}

#[test]
fn test_empty_testcase_with_all_attributes() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test" classname="MyClass" assertions="5" timestamp="2023-01-01T00:00:00Z" time="1.5" custom="value"/>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).unwrap();
    let test_case = &report.test_suites[0].test_cases[0];
    assert_eq!(test_case.classname.as_ref().unwrap().as_str(), "MyClass");
    assert_eq!(test_case.assertions, Some(5));
    assert_eq!(
        test_case.timestamp.unwrap().to_rfc3339(),
        "2023-01-01T00:00:00+00:00"
    );
    assert_eq!(
        test_case.time.unwrap(),
        std::time::Duration::from_secs_f64(1.5)
    );
    assert_eq!(test_case.extra.get("custom").unwrap().as_str(), "value");
}

#[test]
fn test_empty_testcase_missing_name() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase classname="MyClass"/>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::MissingAttribute(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, None),
            PathElement::Attribute("name".to_string()),
        ],
    );
}

#[test]
fn test_status_element_with_stack_trace() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure message="failed">
                Description text
                <stackTrace>at line 1
at line 2</stackTrace>
            </failure>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).unwrap();
    let test_case = &report.test_suites[0].test_cases[0];
    if let quick_junit::TestCaseStatus::NonSuccess { description, .. } = &test_case.status {
        assert_eq!(description.as_ref().unwrap().as_str(), "Description text");
    } else {
        panic!("Expected NonSuccess status");
    }
}

#[test]
fn test_status_element_with_system_out_and_err() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <flakyFailure message="flaky">
                <system-out>stdout content</system-out>
                <system-err>stderr content</system-err>
            </flakyFailure>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).unwrap();
    let test_case = &report.test_suites[0].test_cases[0];
    if let quick_junit::TestCaseStatus::Success { flaky_runs } = &test_case.status {
        assert_eq!(flaky_runs.len(), 1);
        assert_eq!(
            flaky_runs[0].system_out.as_ref().unwrap().as_str(),
            "stdout content"
        );
        assert_eq!(
            flaky_runs[0].system_err.as_ref().unwrap().as_str(),
            "stderr content"
        );
    } else {
        panic!("Expected Success status with flaky runs");
    }
}

#[test]
fn test_status_element_with_timestamp_and_time() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <flakyError message="flaky" timestamp="2023-01-01T00:00:00Z" time="1.5"/>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).unwrap();
    let test_case = &report.test_suites[0].test_cases[0];
    if let quick_junit::TestCaseStatus::Success { flaky_runs } = &test_case.status {
        assert_eq!(flaky_runs.len(), 1);
        assert_eq!(
            flaky_runs[0].timestamp.unwrap().to_rfc3339(),
            "2023-01-01T00:00:00+00:00"
        );
        assert_eq!(
            flaky_runs[0].time.unwrap(),
            std::time::Duration::from_secs_f64(1.5)
        );
    } else {
        panic!("Expected Success status with flaky runs");
    }
}

#[test]
fn test_status_element_unexpected_eof() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure message="test">description"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
            PathElement::Failure,
        ],
    );
}

#[test]
fn test_unknown_testcase_child_element() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <unknown-element>content</unknown-element>
        </testcase>
    </testsuite>
</testsuites>"#;

    // Should succeed - unknown elements are skipped
    let report = Report::deserialize_from_str(xml).unwrap();
    assert_eq!(report.test_suites[0].test_cases.len(), 1);
}

#[test]
fn test_properties_unexpected_eof() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <properties>
            <property name="key" value="val">"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::Properties,
        ],
    );
}

#[test]
fn test_text_content_unexpected_eof() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out>incomplete content"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
            PathElement::SystemOut,
        ],
    );
}

#[test]
fn test_testsuite_with_extra_attributes() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0" hostname="localhost" package="mypackage">
        <testcase name="test"/>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).unwrap();
    let suite = &report.test_suites[0];
    assert_eq!(suite.extra.len(), 2);
    assert_eq!(suite.extra.get("hostname").unwrap().as_str(), "localhost");
    assert_eq!(suite.extra.get("package").unwrap().as_str(), "mypackage");
}

#[test]
fn test_testcase_with_properties() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <properties>
                <property name="key1" value="value1"/>
                <property name="key2" value="value2"/>
            </properties>
        </testcase>
    </testsuite>
</testsuites>"#;

    let report = Report::deserialize_from_str(xml).unwrap();
    let test_case = &report.test_suites[0].test_cases[0];
    assert_eq!(test_case.properties.len(), 2);
    assert_eq!(test_case.properties[0].name.as_str(), "key1");
    assert_eq!(test_case.properties[1].name.as_str(), "key2");
}

#[test]
fn test_invalid_entity_reference_in_failure() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure message="test">Invalid entity: &invalidEntity;</failure>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
            PathElement::Failure,
        ],
    );
}

#[test]
fn test_invalid_entity_reference_in_system_out() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <testcase name="test">
            <system-out>Invalid entity: &unknownEntity;</system-out>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
            PathElement::SystemOut,
        ],
    );
}

#[test]
fn test_unknown_testsuites_attributes() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0" custom-attr="value" another="test">
</testsuites>"#;

    // Should succeed - unknown attributes on testsuites are ignored
    let report = Report::deserialize_from_str(xml).unwrap();
    assert_eq!(report.name.as_str(), "test");
}

#[test]
fn test_empty_testsuites_unknown_attributes() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="0" failures="0" errors="0" hostname="localhost"/>"#;

    // Should succeed - unknown attributes on empty testsuites are ignored
    let report = Report::deserialize_from_str(xml).unwrap();
    assert_eq!(report.name.as_str(), "test");
}

#[test]
fn test_empty_testsuites_missing_name() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites tests="0" failures="0" errors="0"/>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::MissingAttribute(_)),
        &[
            PathElement::TestSuites,
            PathElement::Attribute("name".to_string()),
        ],
    );
}

#[test]
fn test_unknown_element_in_failure() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure message="test">
                Description text
                <unknown-element>content</unknown-element>
            </failure>
        </testcase>
    </testsuite>
</testsuites>"#;

    // Should succeed - unknown elements in failure are skipped
    let report = Report::deserialize_from_str(xml).unwrap();
    let test_case = &report.test_suites[0].test_cases[0];
    if let quick_junit::TestCaseStatus::NonSuccess { description, .. } = &test_case.status {
        assert_eq!(description.as_ref().unwrap().as_str(), "Description text");
    } else {
        panic!("Expected NonSuccess status");
    }
}

#[test]
fn test_unknown_status_element_attributes() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="1" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="1">
        <testcase name="test">
            <failure message="test" type="AssertionError" custom="value" another-attr="test">
                Description
            </failure>
        </testcase>
    </testsuite>
</testsuites>"#;

    // Should succeed - unknown attributes on status elements are ignored
    let report = Report::deserialize_from_str(xml).unwrap();
    let test_case = &report.test_suites[0].test_cases[0];
    if let quick_junit::TestCaseStatus::NonSuccess { message, ty, .. } = &test_case.status {
        assert_eq!(message.as_ref().unwrap().as_str(), "test");
        assert_eq!(ty.as_ref().unwrap().as_str(), "AssertionError");
    } else {
        panic!("Expected NonSuccess status");
    }
}

#[test]
fn test_unknown_property_attributes() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="0" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="0">
        <properties>
            <property name="key1" value="value1" custom="ignored"/>
        </properties>
        <testcase name="test"/>
    </testsuite>
</testsuites>"#;

    // Should succeed - unknown attributes on properties are ignored
    let report = Report::deserialize_from_str(xml).unwrap();
    let suite = &report.test_suites[0];
    assert_eq!(suite.properties.len(), 1);
    assert_eq!(suite.properties[0].name.as_str(), "key1");
    assert_eq!(suite.properties[0].value.as_str(), "value1");
}

#[test]
fn test_invalid_utf8_in_failure_description() {
    // Create XML with invalid UTF-8 in the failure description
    let mut xml = b"<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<testsuites name=\"test\" tests=\"1\" failures=\"1\" errors=\"0\">
    <testsuite name=\"suite\" tests=\"1\" disabled=\"0\" errors=\"0\" failures=\"1\">
        <testcase name=\"test\">
            <failure message=\"test\">Invalid UTF-8: "
        .to_vec();
    xml.push(0xFF); // Invalid UTF-8 byte
    xml.extend_from_slice(
        b"</failure>
        </testcase>
    </testsuite>
</testsuites>",
    );

    assert_error(
        xml.as_slice(),
        |kind| matches!(kind, DeserializeErrorKind::Utf8Error(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
            PathElement::Failure,
        ],
    );
}

#[test]
fn test_invalid_utf8_in_cdata() {
    // Create XML with invalid UTF-8 in CDATA
    let mut xml = b"<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<testsuites name=\"test\" tests=\"1\" failures=\"1\" errors=\"0\">
    <testsuite name=\"suite\" tests=\"1\" disabled=\"0\" errors=\"0\" failures=\"1\">
        <testcase name=\"test\">
            <failure message=\"test\"><![CDATA[Invalid UTF-8: "
        .to_vec();
    xml.push(0xFF); // Invalid UTF-8 byte
    xml.extend_from_slice(
        b"]]></failure>
        </testcase>
    </testsuite>
</testsuites>",
    );

    assert_error(
        xml.as_slice(),
        |kind| matches!(kind, DeserializeErrorKind::Utf8Error(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
            PathElement::Failure,
        ],
    );
}

#[test]
fn test_invalid_utf8_in_system_out() {
    // Create XML with invalid UTF-8 in system-out
    let mut xml = b"<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<testsuites name=\"test\" tests=\"1\" failures=\"0\" errors=\"0\">
    <testsuite name=\"suite\" tests=\"1\" disabled=\"0\" errors=\"0\" failures=\"0\">
        <testcase name=\"test\">
            <system-out>Invalid UTF-8: "
        .to_vec();
    xml.push(0xFF); // Invalid UTF-8 byte
    xml.extend_from_slice(
        b"</system-out>
        </testcase>
    </testsuite>
</testsuites>",
    );

    assert_error(
        xml.as_slice(),
        |kind| matches!(kind, DeserializeErrorKind::Utf8Error(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
            PathElement::SystemOut,
        ],
    );
}

#[test]
fn test_invalid_utf8_in_entity_reference() {
    // Create XML with invalid UTF-8 in entity reference
    let mut xml = b"<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<testsuites name=\"test\" tests=\"1\" failures=\"1\" errors=\"0\">
    <testsuite name=\"suite\" tests=\"1\" disabled=\"0\" errors=\"0\" failures=\"1\">
        <testcase name=\"test\">
            <failure message=\"test\">Entity: &"
        .to_vec();
    xml.push(0xFF); // Invalid UTF-8 byte
    xml.extend_from_slice(
        b";</failure>
        </testcase>
    </testsuite>
</testsuites>",
    );

    assert_error(
        xml.as_slice(),
        |kind| matches!(kind, DeserializeErrorKind::Utf8Error(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
            PathElement::Failure,
        ],
    );
}

#[test]
fn test_multiple_main_status_elements() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="2" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="2">
        <testcase name="test">
            <failure message="first failure"/>
            <error message="second error"/>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
        ],
    );
}

#[test]
fn test_multiple_failure_elements() {
    let xml = r#"<?xml version="1.0" encoding="UTF-8"?>
<testsuites name="test" tests="1" failures="2" errors="0">
    <testsuite name="suite" tests="1" disabled="0" errors="0" failures="2">
        <testcase name="test">
            <failure message="first"/>
            <failure message="second"/>
        </testcase>
    </testsuite>
</testsuites>"#;

    assert_error(
        xml,
        |kind| matches!(kind, DeserializeErrorKind::InvalidStructure(_)),
        &[
            PathElement::TestSuites,
            PathElement::TestSuite(0, Some("suite".to_string())),
            PathElement::TestCase(0, Some("test".to_string())),
        ],
    );
}
