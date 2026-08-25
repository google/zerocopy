// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! One checked boundary between repository state and CI planning.
//!
//! Loading CI inputs is intentionally all-or-nothing. A caller cannot obtain a
//! [`CiInputs`] until the policy is valid, its references agree with live Cargo
//! metadata and repository files, every workflow job has an exact reviewed
//! role, the handwritten matrix jobs exactly publish and consume typed plans,
//! the handwritten semver preparation/action pair exactly implements typed
//! policy, every independently recorded legacy baseline parses canonically,
//! and the typed execution model exactly reproduces that legacy evidence.
//! Planners therefore consume checked data rather than remembering which
//! validation passes must precede which lookups.

use std::{
    fs, io,
    path::{Path, PathBuf},
};

use thiserror::Error;

use crate::{
    baseline::{BaselineError, LegacyBaselinePaths, LegacyBaselines},
    execution::{audit_execution, ExecutionAuditError},
    inventory::{AuditError, RepositoryInventory},
    planned_adapter::{audit_planned_adapter, PlannedAdapterAuditError},
    policy::{Policy, ReadPolicyError},
    semver_adapter::{audit_semver_adapter, SemverAdapterAuditError},
    workflow::{audit_workflows, ReviewedWorkflowJobs, WorkflowAuditError, WORKFLOW_REGISTRY_PATH},
};

/// The repository-relative location of the typed CI policy.
pub const POLICY_PATH: &str = "ci/zc.toml";

/// All repository-owned inputs accepted for CI planning.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CiInputs {
    repository_root: PathBuf,
    policy: Policy,
    repository: RepositoryInventory,
    workflow_jobs: ReviewedWorkflowJobs,
    legacy: LegacyBaselines,
}

impl CiInputs {
    /// Loads and checks every planning input below `repository_root`.
    pub fn load(repository_root: impl AsRef<Path>) -> Result<Self, LoadCiError> {
        let supplied_root = repository_root.as_ref();
        let repository_root = supplied_root.canonicalize().map_err(|source| {
            LoadCiError::RepositoryRoot { path: supplied_root.to_path_buf(), source }
        })?;
        let policy_path = resolve_input_file(&repository_root, Path::new(POLICY_PATH))?;
        let policy = Policy::read(policy_path).map_err(LoadCiError::Policy)?;
        // The registry is a fixed runtime input rather than a policy-selected
        // path. Resolve it through the same containment boundary before the
        // workflow module opens it, so a checked-in symlink cannot redirect
        // the reviewed role assignments outside this checkout.
        let workflow_registry =
            resolve_input_file(&repository_root, Path::new(WORKFLOW_REGISTRY_PATH))?;
        let workflow_jobs = audit_workflows(&repository_root, workflow_registry)
            .map_err(|error| LoadCiError::Workflow(Box::new(error)))?;
        // Job-ID inventory cannot prove that a planned job publishes or
        // consumes its typed matrix through the complete checked CLI. Audit
        // that small planned-job workflow bridge while both checks refer to
        // the same fixed file.
        audit_planned_adapter(&repository_root, &workflow_jobs)
            .map_err(LoadCiError::PlannedAdapter)?;
        let repository = RepositoryInventory::audit(&repository_root, &policy)
            .map_err(LoadCiError::Inventory)?;
        // `audit_workflows` deliberately recognizes jobs, not arbitrary YAML
        // steps. GitHub requires the semver action reference to remain literal,
        // so check its canonical preparation/action adapter only after policy
        // and Cargo inventory are trustworthy. Its full-event target-set proof
        // may rely on the preceding planned-adapter audit, which established
        // that `build_test` consumes the exact typed projection for every
        // event.
        audit_semver_adapter(&repository_root, &policy, &repository)
            .map_err(LoadCiError::SemverAdapter)?;
        let baselines = policy.baselines();
        let paths = LegacyBaselinePaths {
            manifest: resolve_input_file(&repository_root, baselines.manifest().as_path())?,
            build_reduced: resolve_input_file(
                &repository_root,
                baselines.build_reduced().as_path(),
            )?,
            build_full: resolve_input_file(&repository_root, baselines.build_full().as_path())?,
            miri_reduced: resolve_input_file(&repository_root, baselines.miri_reduced().as_path())?,
            miri_full: resolve_input_file(&repository_root, baselines.miri_full().as_path())?,
            logical_obligations: resolve_input_file(
                &repository_root,
                baselines.logical_obligations().as_path(),
            )?,
            standalone_obligations: resolve_input_file(
                &repository_root,
                baselines.standalone_obligations().as_path(),
            )?,
            command_goldens: resolve_input_file(
                &repository_root,
                baselines.command_goldens().as_path(),
            )?,
        };
        let legacy = LegacyBaselines::read(&paths).map_err(LoadCiError::Baseline)?;
        let inputs = Self { repository_root, policy, repository, workflow_jobs, legacy };
        // Keep the pure parity proof inside this checked boundary. Returning a
        // `CiInputs` without this call would make correctness depend on every
        // planner and CLI entry point remembering a second validation pass.
        audit_execution(&inputs).map_err(LoadCiError::Execution)?;
        Ok(inputs)
    }

    /// Returns the checked coverage policy.
    pub fn policy(&self) -> &Policy {
        &self.policy
    }

    /// Returns facts collected from the live checkout.
    pub fn repository(&self) -> &RepositoryInventory {
        &self.repository
    }

    /// Returns the checked role assignment for every live workflow job.
    pub fn workflow_jobs(&self) -> &ReviewedWorkflowJobs {
        &self.workflow_jobs
    }

    /// Returns the independent description of legacy CI behavior.
    pub fn legacy(&self) -> &LegacyBaselines {
        &self.legacy
    }

    /// Returns the canonical checkout root which supplied every checked input.
    ///
    /// Execution uses this crate-private authority instead of accepting an
    /// unrelated caller-supplied path after validation has completed.
    pub(crate) fn repository_root(&self) -> &Path {
        &self.repository_root
    }
}

/// Resolves a repository input once and rejects symlink escapes before use.
///
/// Policy syntax already rejects absolute paths and `..`, and fixed runtime
/// paths are repository-relative constants. A Git-tracked symlink can still
/// point outside the checkout. Canonical containment is a separate file-system
/// invariant and belongs at the boundary which opens the file. Callers use the
/// returned canonical path rather than reopening the unchecked spelling.
fn resolve_input_file(repository_root: &Path, configured: &Path) -> Result<PathBuf, LoadCiError> {
    let path = repository_root.join(configured);
    let resolved = path
        .canonicalize()
        .map_err(|source| LoadCiError::InputPath { path: path.clone(), source })?;
    if !resolved.starts_with(repository_root) {
        return Err(LoadCiError::InputOutsideRepository {
            path,
            resolved,
            repository_root: repository_root.to_path_buf(),
        });
    }
    let metadata = fs::metadata(&resolved)
        .map_err(|source| LoadCiError::InputPath { path: resolved.clone(), source })?;
    if !metadata.is_file() {
        return Err(LoadCiError::InputNotFile { path: resolved });
    }
    Ok(resolved)
}

/// A failure loading one layer of CI planning input.
#[derive(Debug, Error)]
pub enum LoadCiError {
    /// The supplied repository root could not be resolved.
    #[error("failed to resolve repository root `{path}`: {source}")]
    RepositoryRoot {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    /// A configured input could not be resolved or inspected.
    #[error("failed to resolve CI input `{path}`: {source}")]
    InputPath {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    /// A configured input resolved outside the checkout.
    #[error("CI input `{path}` resolves to `{resolved}`, outside repository `{repository_root}`")]
    InputOutsideRepository { path: PathBuf, resolved: PathBuf, repository_root: PathBuf },
    /// A configured input resolved to a directory or other non-file object.
    #[error("CI input `{path}` is not a regular file")]
    InputNotFile { path: PathBuf },
    /// The typed policy was unreadable or invalid.
    #[error(transparent)]
    Policy(ReadPolicyError),
    /// Live repository state did not satisfy the policy.
    #[error(transparent)]
    Inventory(AuditError),
    /// Workflow files or their reviewed role assignments were invalid.
    #[error(transparent)]
    Workflow(Box<WorkflowAuditError>),
    /// The planned-job workflow bridge did not publish or execute plans exactly.
    #[error(transparent)]
    PlannedAdapter(PlannedAdapterAuditError),
    /// The literal semver preparation/action adapter did not implement policy.
    #[error(transparent)]
    SemverAdapter(SemverAdapterAuditError),
    /// The frozen legacy evidence was unreadable or noncanonical.
    #[error(transparent)]
    Baseline(BaselineError),
    /// Typed execution behavior differed from frozen legacy evidence.
    #[error(transparent)]
    Execution(ExecutionAuditError),
}

#[cfg(test)]
mod tests {
    use std::{path::Path, process::Command};

    use super::{resolve_input_file, CiInputs, LoadCiError};

    #[test]
    fn loads_every_current_planning_input_together() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let inputs = CiInputs::load(root).unwrap();

        assert_eq!(inputs.legacy().build_reduced().len(), 60);
        assert_eq!(inputs.legacy().build_full().len(), 182);
        assert!(inputs.legacy().miri_reduced().is_empty());
        assert_eq!(inputs.legacy().miri_full().len(), 64);
        assert_eq!(inputs.repository().policy_packages().len(), 2);
    }

    #[test]
    fn repository_attributes_keep_semantic_ci_inputs_lf() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        // These paths represent every semantic extension consumed by CiInputs.
        // The hypothetical YAML path keeps the currently unused `*.yaml` rule
        // checked as well. Keep the set coordinated with `.gitattributes` when
        // a new source-level input format is introduced.
        let paths = [
            ".github/workflows/ci.yml",
            "ci/future-input.yaml",
            "ci/zc.toml",
            "ci/workflow-jobs.tsv",
            "ci/baselines/command-goldens.tsv",
            "zerocopy/Cargo.toml",
        ];
        let output = Command::new("git")
            .current_dir(&root)
            .args(["check-attr", "eol", "--"])
            .args(paths)
            .output()
            .unwrap();
        assert!(output.status.success(), "git check-attr failed: {output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        let expected = paths.map(|path| format!("{path}: eol: lf"));
        assert_eq!(stdout.lines().collect::<Vec<_>>(), expected);

        // Assigning `eol=lf` does not retroactively rewrite blobs which are
        // already in Git's index. If one of those blobs still contains CRLF,
        // a fresh checkout writes an LF worktree copy and immediately reports
        // it as different from the index. Check the indexed representation as
        // well as the effective attributes so adding or broadening a rule
        // cannot leave fresh CI worktrees dirty.
        let output =
            Command::new("git").current_dir(&root).args(["ls-files", "--eol"]).output().unwrap();
        assert!(output.status.success(), "git ls-files --eol failed: {output:?}");
        let stdout = String::from_utf8(output.stdout).unwrap();
        let governed =
            stdout.lines().filter(|line| line.contains("attr/text eol=lf")).collect::<Vec<_>>();
        assert!(!governed.is_empty(), "no tracked paths are governed by eol=lf");
        for line in governed {
            assert!(
                line.starts_with("i/lf"),
                "tracked path governed by eol=lf is not normalized: {line}"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn rejects_an_input_symlink_which_escapes_the_repository() {
        use std::{
            fs,
            os::unix::fs::symlink,
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary =
            std::env::temp_dir().join(format!("zerocopy-ci-input-test-{}-{unique}", process::id()));
        let repository = temporary.join("repository");
        let outside = temporary.join("outside.tsv");
        fs::create_dir_all(repository.join("ci")).unwrap();
        fs::write(&outside, "external\n").unwrap();
        symlink(&outside, repository.join("ci/baseline.tsv")).unwrap();
        let repository = repository.canonicalize().unwrap();

        let error = resolve_input_file(&repository, Path::new("ci/baseline.tsv")).unwrap_err();
        assert!(matches!(error, LoadCiError::InputOutsideRepository { .. }));

        fs::remove_dir_all(temporary).unwrap();
    }
}
