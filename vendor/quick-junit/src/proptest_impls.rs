// Copyright (c) The nextest Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Proptest `Arbitrary` implementations for quick-junit types.
//!
//! These implementations enable property-based testing of serialization and deserialization.

use crate::{
    NonSuccessKind, Property, Report, ReportUuid, TestCase, TestCaseStatus, TestSuite, XmlString,
};
use chrono::{DateTime, FixedOffset};
use proptest::{
    arbitrary::Arbitrary,
    collection, option,
    prelude::*,
    strategy::{BoxedStrategy, Map, Strategy},
};
use std::time::Duration;

impl Arbitrary for XmlString {
    type Parameters = <String as Arbitrary>::Parameters;
    type Strategy = Map<<String as Arbitrary>::Strategy, fn(String) -> XmlString>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        String::arbitrary_with(args).prop_map(|s| {
            // Strip leading and trailing whitespace since XML isn't intended to
            // preserve that.
            XmlString::new(s.trim())
        })
    }
}

pub(crate) fn text_node_strategy() -> impl Strategy<Value = XmlString> {
    any::<XmlString>().prop_filter("Non-empty string", |s| !s.is_empty())
}

/// Strategy for generating realistic test case names like "module::submodule::test_name"
pub(crate) fn test_name_strategy() -> impl Strategy<Value = XmlString> {
    // Generate alphanumeric identifier
    let ident = "[a-z][a-z0-9_]{0,15}";

    // Generate 1-4 segments joined by ::
    collection::vec(ident, 1..=4).prop_map(|segments| XmlString::new(segments.join("::")))
}

/// Strategy for generating valid XML attribute names (alphanumeric, no special chars)
pub(crate) fn xml_attr_name_strategy() -> impl Strategy<Value = XmlString> {
    // XML attribute names: must start with letter or underscore, followed by letters, digits, hyphens, underscores, or periods
    "[a-zA-Z_][a-zA-Z0-9_.-]{0,15}".prop_map(XmlString::new)
}

/// Strategy for generating arbitrary DateTime<FixedOffset>
pub(crate) fn datetime_strategy() -> impl Strategy<Value = DateTime<FixedOffset>> {
    // Generate timestamps within a reasonable range (2000-2100)
    // to avoid edge cases with very old or very future dates
    // Generate offsets in minute increments only (RFC 3339 doesn't preserve seconds in offsets)
    (946684800i64..4102444800i64, -1440i32..1440i32).prop_map(|(secs, offset_minutes)| {
        let offset_secs = offset_minutes * 60;
        let offset =
            FixedOffset::east_opt(offset_secs).unwrap_or(FixedOffset::east_opt(0).unwrap());
        DateTime::from_timestamp(secs, 0)
            .unwrap()
            .with_timezone(&offset)
    })
}

/// Strategy for generating arbitrary Duration
pub(crate) fn duration_strategy() -> impl Strategy<Value = Duration> {
    // Generate durations up to 1 hour, in milliseconds to avoid precision issues
    (0u64..3_600_000u64).prop_map(Duration::from_millis)
}

/// Strategy for generating an IndexMap with XML attribute names as keys
pub(crate) fn xml_attr_index_map_strategy(
) -> impl Strategy<Value = indexmap::IndexMap<XmlString, XmlString>> {
    collection::hash_map(xml_attr_name_strategy(), any::<XmlString>(), 0..3)
        .prop_map(|hm| hm.into_iter().collect())
}

impl Arbitrary for TestSuite {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        (
            test_name_strategy(),
            option::of(datetime_strategy()),
            option::of(duration_strategy()),
            collection::vec(any::<TestCase>(), 0..10),
            collection::vec(any::<Property>(), 0..5),
            any::<Option<XmlString>>(),
            any::<Option<XmlString>>(),
            collection::hash_map(xml_attr_name_strategy(), any::<XmlString>(), 0..5),
        )
            .prop_map(
                |(name, timestamp, time, test_cases, properties, system_out, system_err, extra)| {
                    // Compute counts from test_cases
                    let tests = test_cases.len();
                    let mut failures = 0;
                    let mut errors = 0;
                    let mut disabled = 0;

                    for test_case in &test_cases {
                        match &test_case.status {
                            TestCaseStatus::Success { .. } => {}
                            TestCaseStatus::NonSuccess { kind, .. } => match kind {
                                NonSuccessKind::Failure => failures += 1,
                                NonSuccessKind::Error => errors += 1,
                            },
                            TestCaseStatus::Skipped { .. } => disabled += 1,
                        }
                    }

                    TestSuite {
                        name,
                        tests,
                        disabled,
                        errors,
                        failures,
                        timestamp,
                        time,
                        test_cases,
                        properties,
                        system_out,
                        system_err,
                        extra: extra.into_iter().collect(),
                    }
                },
            )
            .boxed()
    }
}

impl Arbitrary for Report {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        (
            test_name_strategy(),
            any::<Option<ReportUuid>>(),
            option::of(datetime_strategy()),
            option::of(duration_strategy()),
            collection::vec(any::<TestSuite>(), 0..5),
        )
            .prop_map(|(name, uuid, timestamp, time, test_suites)| {
                // Compute counts from test_suites
                let tests = test_suites.iter().map(|ts| ts.tests).sum();
                let failures = test_suites.iter().map(|ts| ts.failures).sum();
                let errors = test_suites.iter().map(|ts| ts.errors).sum();

                Report {
                    name,
                    uuid,
                    timestamp,
                    time,
                    tests,
                    failures,
                    errors,
                    test_suites,
                }
            })
            .boxed()
    }
}
