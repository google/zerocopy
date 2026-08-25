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
//! The plan producer and its ordinary build and Miri consumers form a smaller
//! handwritten boundary. The producer must publish exact outputs through one
//! unconditional singleton job. Each planned matrix job must consume the
//! matching output, run only its exact checkout and image setup, prove that
//! setup left the expected checkout unchanged, and pass every selector through
//! a real Docker invocation to the typed executor. Repository-owned actions,
//! the Dockerfile, and the image context are mutable too, so this boundary
//! resolves every source inside the checkout and requires its complete contents
//! to match an independent reviewed snapshot. The required-check aggregate
//! must then depend on the planner, all typed-plan consumers, and the remaining
//! dependency-inventory audit while enforcing every optional planned
//! conclusion. A missing output, changed matrix expression, substituted setup
//! step, modified checkout, no-op interpreter, conditional step, or dropped
//! selector could otherwise silently reduce coverage while the Rust plan and
//! job-ID inventory remained valid.
//!
//! This module is deliberately not a YAML or GitHub Actions interpreter. It
//! recognizes the canonical source forms which carry the planned-job workflow
//! bridge and rejects ambiguous or extended forms. `action-validator`
//! continues to own the complete workflow schema.

use std::{
    collections::BTreeSet,
    error::Error,
    fmt, io,
    path::{Path, PathBuf},
};

use thiserror::Error;

use crate::{
    inventory::RepositoryInventory, workflow::ReviewedWorkflowJobs,
    workflow_protocol::WORKFLOW_PATH,
};

mod aggregate;
mod image;
mod matrix;
mod planner;
mod reviewed_source;
mod source;
#[cfg(test)]
mod test_support;

/// Audits the checked planned-job workflow and local-action bridge.
///
/// `workflow` must be the exact source retained by the earlier workflow
/// inventory pass. Taking source rather than a path prevents this behavioral
/// audit from reopening a replacement file after its job IDs were approved.
/// `repository_root` remains necessary for the other reviewed adapter sources.
pub(crate) fn audit_planned_adapter(
    repository_root: &Path,
    workflow: &str,
    reviewed_jobs: &ReviewedWorkflowJobs,
    repository: &RepositoryInventory,
) -> Result<(), PlannedAdapterAuditError> {
    let reviewed_planned_jobs = reviewed_jobs
        .planned_jobs()
        .map(|job| (job.workflow.as_str().to_owned(), job.job.as_str().to_owned()))
        .collect::<BTreeSet<_>>();
    audit_source(workflow, &reviewed_planned_jobs)?;
    // Audit every mutable source and every independent review copy in one
    // identity set. Keeping this aggregation here prevents two modules from
    // accidentally accepting hard-linked evidence because each saw only its
    // own subset of files.
    let reviewed_sources = matrix::reviewed_sources()
        .iter()
        .chain(image::reviewed_sources())
        .copied()
        .collect::<Vec<_>>();
    reviewed_source::audit_reviewed_sources(repository_root, &reviewed_sources)?;
    image::audit_context_shape(repository_root)?;
    let mut errors = ViolationSink::default();
    image::audit_toolchain_defaults(repository.toolchain_versions(), &mut errors);
    if !errors.is_empty() {
        return Err(PlannedAdapterAuditError::Invalid(errors.finish()));
    }
    Ok(())
}

fn audit_source(
    workflow: &str,
    reviewed_planned_jobs: &BTreeSet<(String, String)>,
) -> Result<(), PlannedAdapterViolations> {
    let mut errors = ViolationSink::default();
    // Source-level checks intentionally require one canonical spelling. The
    // repository read boundary has already normalized a pre-existing Windows
    // worktree's well-formed CRLF, while .gitattributes and ci.rs require LF in
    // Git's index. Direct parser callers and bare carriage returns still fail.
    if workflow.contains('\r') {
        errors.push(WORKFLOW_PATH, "workflow must use canonical LF line endings");
    }
    let lines = workflow.lines().collect::<Vec<_>>();
    planner::audit(&lines, &mut errors);
    image::audit(&lines, &mut errors);
    matrix::audit(&lines, reviewed_planned_jobs, &mut errors);
    aggregate::audit(&lines, &mut errors);

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.finish())
    }
}

/// A failure reading or validating the planned-job workflow bridge.
#[derive(Debug, Error)]
pub enum PlannedAdapterAuditError {
    /// A fixed reviewed source could not be resolved or inspected.
    #[error("failed to inspect reviewed CI source `{path}`: {source}")]
    InspectReviewedSource {
        /// Repository-relative audit path joined to the canonical root.
        path: PathBuf,
        /// Underlying file-system failure.
        #[source]
        source: io::Error,
    },
    /// A fixed reviewed source path contains a symbolic link.
    #[error("reviewed CI source path contains symbolic link `{path}`")]
    ReviewedSourceSymlink {
        /// First symbolic-link component found beneath the canonical root.
        path: PathBuf,
    },
    /// A fixed reviewed source resolved outside the canonical checkout.
    #[error(
        "reviewed CI source `{path}` resolves outside repository `{repository_root}` to `{resolved}`"
    )]
    ReviewedSourceOutsideRepository {
        /// Repository-relative audit path joined to the canonical root.
        path: PathBuf,
        /// Canonical target reached through any symlinks.
        resolved: PathBuf,
        /// Canonical repository root which must contain the target.
        repository_root: PathBuf,
    },
    /// A fixed reviewed source path resolved to something other than a file.
    #[error("reviewed CI source `{path}` is not a regular file")]
    ReviewedSourceNotFile {
        /// Canonical path which was inspected.
        path: PathBuf,
    },
    /// A fixed reviewed source could not be read as repository text.
    #[error("failed to read reviewed CI source `{path}`: {source}")]
    ReadReviewedSource {
        /// Canonical audit path.
        path: PathBuf,
        /// Underlying file-system or text-normalization failure.
        #[source]
        source: io::Error,
    },
    /// A reviewed source's cross-platform file identity could not be read.
    #[error("failed to inspect reviewed CI source identity `{path}`: {source}")]
    ReviewedSourceIdentity {
        /// Reviewed source path.
        path: PathBuf,
        /// Underlying file-system failure.
        #[source]
        source: io::Error,
    },
    /// A reviewed source changed between containment and identity checks.
    #[error(
        "reviewed CI source `{path}` changed while it was opened: first resolved to `{first}`, then to `{second}`"
    )]
    ReviewedSourceChangedDuringOpen {
        /// Direct reviewed path below the repository root.
        path: PathBuf,
        /// Canonical destination checked before opening.
        first: PathBuf,
        /// Canonical destination checked after opening.
        second: PathBuf,
    },
    /// Two supposedly independent reviewed sources are the same file.
    #[error("reviewed CI sources `{first_path}` and `{second_path}` resolve to the same file")]
    DuplicateReviewedSource {
        /// First path encountered for this file identity.
        first_path: PathBuf,
        /// Later path with the same file identity.
        second_path: PathBuf,
    },
    /// The handwritten bridge no longer publishes or executes typed plans exactly.
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
