// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Small helpers for focused audits of literal workflow fixtures.

use std::collections::BTreeSet;

use super::{PlannedAdapterViolations, ViolationSink};
use crate::workflow_protocol::{BUILD_JOB, MIRI_JOB, WORKFLOW_PATH};

pub(super) fn audit_feature(
    source: &str,
    audit: impl FnOnce(&[&str], &mut ViolationSink),
) -> Result<(), PlannedAdapterViolations> {
    let mut errors = ViolationSink::default();
    if source.contains('\r') {
        errors.push(WORKFLOW_PATH, "workflow must use canonical LF line endings");
    }
    let lines = source.lines().collect::<Vec<_>>();
    audit(&lines, &mut errors);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.finish())
    }
}

pub(super) fn assert_rejected(
    label: &str,
    result: Result<(), PlannedAdapterViolations>,
    expected: &str,
) {
    let error = match result {
        Ok(()) => panic!("{label}: mutation was accepted"),
        Err(error) => error,
    };
    assert!(error.to_string().contains(expected), "{label}: {error}");
}

pub(super) fn replace_in_job(source: &str, job: &str, from: &str, to: &str) -> String {
    let marker = format!("  {job}:\n");
    let start = source.find(&marker).unwrap_or_else(|| panic!("missing fixture job {job}"));
    let remainder = &source[start + marker.len()..];
    let end = remainder
        .match_indices('\n')
        .find_map(|(offset, _)| {
            let next = &remainder[offset + 1..];
            (next.starts_with("  ") && !next.starts_with("   "))
                .then_some(start + marker.len() + offset + 1)
        })
        .unwrap_or(source.len());
    let block = &source[start..end];
    assert!(block.contains(from), "job {job} did not contain {from:?}");
    format!("{}{}{}", &source[..start], block.replacen(from, to, 1), &source[end..])
}

pub(super) fn canonical_planned_jobs() -> BTreeSet<(String, String)> {
    [BUILD_JOB, MIRI_JOB]
        .into_iter()
        .map(|job| (WORKFLOW_PATH.to_owned(), job.to_owned()))
        .collect()
}
