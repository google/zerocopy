// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Fail-closed audits of the handwritten bridge from typed plans to Actions.
//!
//! The general workflow inventory in [`crate::workflow`] proves that every job
//! has a reviewed role, but it intentionally does not inspect job behavior.
//! The plan producer is a smaller handwritten boundary: it must publish the
//! planner's exact outputs through one unconditional singleton job and one
//! bounded step. A missing output, changed producer, no-op interpreter, or
//! stale CLI command could otherwise silently reduce coverage while the Rust
//! plan and job-ID inventory remained valid.
//!
//! This module is deliberately not a YAML or GitHub Actions interpreter. It
//! recognizes the canonical source forms which carry the planned-job workflow
//! bridge and rejects ambiguous or extended forms. `action-validator`
//! continues to own the complete workflow schema.

use std::{collections::BTreeSet, error::Error, fmt};

use thiserror::Error;

mod planner;
mod source;

/// Audits the checked workflow's typed plan publication bridge.
///
/// `workflow` must be the exact source retained by the earlier workflow
/// inventory pass. Taking source rather than a path prevents this behavioral
/// audit from reopening a replacement file after its job IDs were approved.
pub(crate) fn audit_planned_adapter(workflow: &str) -> Result<(), PlannedAdapterAuditError> {
    audit_source(workflow)?;
    Ok(())
}

fn audit_source(workflow: &str) -> Result<(), PlannedAdapterViolations> {
    let mut errors = ViolationSink::default();
    let Some(lines) = source::canonical_workflow_lines(workflow, &mut errors) else {
        return Err(errors.finish());
    };
    planner::audit(&lines, &mut errors);

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.finish())
    }
}

/// A failure reading or validating the planned-job workflow bridge.
#[derive(Debug, Error)]
pub enum PlannedAdapterAuditError {
    /// The handwritten bridge no longer publishes the typed plan exactly.
    #[error(transparent)]
    Invalid(#[from] PlannedAdapterViolations),
}

/// Deterministically ordered planned-job workflow audit violations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlannedAdapterViolations(Vec<PlannedAdapterViolation>);

impl PlannedAdapterViolations {
    /// Returns all violations in location and message order.
    pub fn violations(&self) -> &[PlannedAdapterViolation] {
        &self.0
    }
}

impl fmt::Display for PlannedAdapterViolations {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(formatter, "planned-job workflow audit has {} violation(s):", self.0.len())?;
        for violation in &self.0 {
            writeln!(formatter, "- {}: {}", violation.location, violation.message)?;
        }
        Ok(())
    }
}

impl Error for PlannedAdapterViolations {}

/// One actionable mismatch in the planned-job workflow bridge.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PlannedAdapterViolation {
    location: String,
    message: String,
}

impl PlannedAdapterViolation {
    /// Returns the workflow field which must be repaired.
    pub fn location(&self) -> &str {
        &self.location
    }

    /// Returns a plain-language repair diagnostic.
    pub fn message(&self) -> &str {
        &self.message
    }
}

#[derive(Default)]
struct ViolationSink(BTreeSet<PlannedAdapterViolation>);

impl ViolationSink {
    fn push(&mut self, location: impl Into<String>, message: impl Into<String>) {
        self.0.insert(PlannedAdapterViolation {
            location: source::escape_control_characters(&location.into()),
            message: source::escape_control_characters(&message.into()),
        });
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn finish(self) -> PlannedAdapterViolations {
        PlannedAdapterViolations(self.0.into_iter().collect())
    }
}
