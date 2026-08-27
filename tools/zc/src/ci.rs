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
//! the complete standalone semver job consumes its typed target matrix and
//! exactly implements policy, the required check exactly aggregates their
//! conclusions, every independently recorded legacy baseline parses
//! canonically, and the typed execution model exactly reproduces that legacy
//! evidence. Planners therefore consume checked data rather than remembering
//! which validation passes must precede which lookups.

use std::{
    collections::HashMap,
    io,
    path::{Path, PathBuf},
};

use thiserror::Error;

use crate::{
    baseline::{BaselineError, LegacyBaselineFiles, LegacyBaselinePaths, LegacyBaselines},
    execution::{audit_execution, ExecutionAuditError},
    inventory::{AuditError, RepositoryInventory},
    planned_adapter::{audit_planned_adapter, PlannedAdapterAuditError},
    policy::{Baselines, Policy, ReadPolicyError},
    repository_file::{self, OpenRepositoryFileError, OpenedRepositoryFile},
    semver_adapter::{audit_semver_adapter, SemverAdapterAuditError},
    workflow::{
        audit_workflows, ReviewedWorkflowJobs, WorkflowAuditError, WorkflowRegistryError,
        WORKFLOW_REGISTRY_PATH,
    },
    workflow_protocol::WORKFLOW_PATH,
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
        let policy_file = open_repository_file(&repository_root, Path::new(POLICY_PATH))?;
        let policy_source = policy_file.read_to_string().map_err(|source| {
            LoadCiError::Policy(ReadPolicyError::Read {
                path: policy_file.path().to_path_buf(),
                source,
            })
        })?;
        let policy = Policy::parse(&policy_source).map_err(|source| {
            LoadCiError::Policy(ReadPolicyError::Policy {
                path: policy_file.path().to_path_buf(),
                source,
            })
        })?;
        // The registry is a fixed runtime input rather than a policy-selected
        // path. Open it through the same containment boundary, then give the
        // workflow module only the parsed registry. A checked-in or concurrent
        // replacement therefore cannot redirect or change the reviewed role
        // assignments after validation.
        let workflow_registry =
            open_repository_file(&repository_root, Path::new(WORKFLOW_REGISTRY_PATH))?;
        let workflow_registry_source = workflow_registry.read_to_string().map_err(|source| {
            LoadCiError::Workflow(Box::new(WorkflowAuditError::Registry(
                WorkflowRegistryError::Read {
                    path: workflow_registry.path().to_path_buf(),
                    source,
                },
            )))
        })?;
        let reviewed_workflow_jobs =
            ReviewedWorkflowJobs::parse(workflow_registry.path(), &workflow_registry_source)
                .map_err(|error| {
                    LoadCiError::Workflow(Box::new(WorkflowAuditError::Registry(error)))
                })?;
        let (workflow_jobs, workflow_sources) =
            audit_workflows(&repository_root, reviewed_workflow_jobs)
                .map_err(|error| LoadCiError::Workflow(Box::new(error)))?;
        // Job-ID inventory cannot prove that a planned job publishes or
        // consumes its typed matrix through the complete checked CLI, or that
        // those conclusions reach the required check. Audit that bridge using
        // the exact bytes retained by the inventory pass, rather than reopening
        // a possibly replaced path. The image producer also consumes validated
        // inventory so its preinstalled compiler pins cannot drift from the
        // toolchains selected by the typed plan.
        let workflow_source = workflow_sources.source(WORKFLOW_PATH).ok_or_else(|| {
            LoadCiError::RequiredWorkflowMissing { path: WORKFLOW_PATH.to_owned() }
        })?;
        let repository = RepositoryInventory::audit(&repository_root, &policy)
            .map_err(LoadCiError::Inventory)?;
        audit_planned_adapter(&repository_root, workflow_source, &workflow_jobs, &repository)
            .map_err(LoadCiError::PlannedAdapter)?;
        // `audit_workflows` deliberately recognizes jobs, not arbitrary YAML
        // steps. GitHub requires the semver action reference to remain literal,
        // so check the complete standalone job only after policy and Cargo
        // inventory are trustworthy. The preceding planned-adapter audit has
        // already established exact planner publication and reviewed ownership;
        // this focused audit checks semver's target-only matrix consumer, fresh
        // runner boundary, checkout, preparation, and literal action.
        audit_semver_adapter(workflow_source, &policy, &repository)
            .map_err(LoadCiError::SemverAdapter)?;
        let baseline_files = OpenLegacyBaselineFiles::open(&repository_root, policy.baselines())?;
        let paths = baseline_files.paths();
        // Policy validation rejects two fields with the same lexical path.
        // This check establishes the stronger file-system identity used at
        // runtime. Keep both checks: symlinks and hard links can give one file
        // different in-tree names, which would make supposedly independent
        // review evidence alias.
        reject_duplicate_baseline_inputs(&baseline_files)?;
        let legacy = LegacyBaselines::read_open(&paths, baseline_files.files())
            .map_err(LoadCiError::Baseline)?;
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

/// The complete open-handle counterpart to [`LegacyBaselinePaths`].
///
/// Keep this field list, [`Self::paths`], [`Self::files`], [`Self::named`], and
/// [`LegacyBaselineFiles`] synchronized. Repeating the shape explicitly is
/// intentional: adding a new independent evidence role must fail to compile or
/// require a visible edit at every identity and parsing boundary.
struct OpenLegacyBaselineFiles {
    manifest: OpenedRepositoryFile,
    build_reduced: OpenedRepositoryFile,
    build_full: OpenedRepositoryFile,
    miri_reduced: OpenedRepositoryFile,
    miri_full: OpenedRepositoryFile,
    logical_obligations: OpenedRepositoryFile,
    standalone_obligations: OpenedRepositoryFile,
    command_goldens: OpenedRepositoryFile,
}

impl OpenLegacyBaselineFiles {
    fn open(repository_root: &Path, baselines: &Baselines) -> Result<Self, LoadCiError> {
        let configured = LegacyBaselinePaths {
            manifest: baselines.manifest().as_path().to_path_buf(),
            build_reduced: baselines.build_reduced().as_path().to_path_buf(),
            build_full: baselines.build_full().as_path().to_path_buf(),
            miri_reduced: baselines.miri_reduced().as_path().to_path_buf(),
            miri_full: baselines.miri_full().as_path().to_path_buf(),
            logical_obligations: baselines.logical_obligations().as_path().to_path_buf(),
            standalone_obligations: baselines.standalone_obligations().as_path().to_path_buf(),
            command_goldens: baselines.command_goldens().as_path().to_path_buf(),
        };
        Self::open_paths(repository_root, &configured)
    }

    fn open_paths(
        repository_root: &Path,
        paths: &LegacyBaselinePaths,
    ) -> Result<Self, LoadCiError> {
        Ok(Self {
            manifest: open_repository_file(repository_root, &paths.manifest)?,
            build_reduced: open_repository_file(repository_root, &paths.build_reduced)?,
            build_full: open_repository_file(repository_root, &paths.build_full)?,
            miri_reduced: open_repository_file(repository_root, &paths.miri_reduced)?,
            miri_full: open_repository_file(repository_root, &paths.miri_full)?,
            logical_obligations: open_repository_file(repository_root, &paths.logical_obligations)?,
            standalone_obligations: open_repository_file(
                repository_root,
                &paths.standalone_obligations,
            )?,
            command_goldens: open_repository_file(repository_root, &paths.command_goldens)?,
        })
    }

    fn paths(&self) -> LegacyBaselinePaths {
        LegacyBaselinePaths {
            manifest: self.manifest.path().to_path_buf(),
            build_reduced: self.build_reduced.path().to_path_buf(),
            build_full: self.build_full.path().to_path_buf(),
            miri_reduced: self.miri_reduced.path().to_path_buf(),
            miri_full: self.miri_full.path().to_path_buf(),
            logical_obligations: self.logical_obligations.path().to_path_buf(),
            standalone_obligations: self.standalone_obligations.path().to_path_buf(),
            command_goldens: self.command_goldens.path().to_path_buf(),
        }
    }

    fn files(&self) -> LegacyBaselineFiles<'_> {
        LegacyBaselineFiles {
            manifest: self.manifest.file(),
            build_reduced: self.build_reduced.file(),
            build_full: self.build_full.file(),
            miri_reduced: self.miri_reduced.file(),
            miri_full: self.miri_full.file(),
            logical_obligations: self.logical_obligations.file(),
            standalone_obligations: self.standalone_obligations.file(),
            command_goldens: self.command_goldens.file(),
        }
    }

    fn named(&self) -> [(&'static str, &OpenedRepositoryFile); 8] {
        [
            ("baselines.manifest", &self.manifest),
            ("baselines.build_reduced", &self.build_reduced),
            ("baselines.build_full", &self.build_full),
            ("baselines.miri_reduced", &self.miri_reduced),
            ("baselines.miri_full", &self.miri_full),
            ("baselines.logical_obligations", &self.logical_obligations),
            ("baselines.standalone_obligations", &self.standalone_obligations),
            ("baselines.command_goldens", &self.command_goldens),
        ]
    }
}

/// Rejects baseline fields which identify the same already-open file.
///
/// The identity handle and parsed byte handle were cloned from one open file.
/// Keeping both alive through comparison and parsing prevents a replacement
/// path from changing either the alias relation or the accepted evidence.
fn reject_duplicate_baseline_inputs(inputs: &OpenLegacyBaselineFiles) -> Result<(), LoadCiError> {
    let mut first_input_by_identity = HashMap::new();
    for (field, input) in inputs.named() {
        if let Some((first_field, first_path)) =
            first_input_by_identity.insert(input.identity(), (field, input.path()))
        {
            return Err(LoadCiError::DuplicateBaselineInput {
                first_field,
                first_path: first_path.to_path_buf(),
                second_field: field,
                second_path: input.path().to_path_buf(),
            });
        }
    }
    Ok(())
}

fn open_repository_file(
    repository_root: &Path,
    configured: &Path,
) -> Result<OpenedRepositoryFile, LoadCiError> {
    repository_file::open(repository_root, configured).map_err(|error| match error {
        OpenRepositoryFileError::Path { path, source } => LoadCiError::InputPath { path, source },
        OpenRepositoryFileError::Identity { path, source } => {
            LoadCiError::InputIdentity { path, source }
        }
        OpenRepositoryFileError::ChangedDuringOpen { path, first, second } => {
            LoadCiError::InputChangedDuringOpen { path, first, second }
        }
        OpenRepositoryFileError::OutsideRepository { path, resolved, repository_root } => {
            LoadCiError::InputOutsideRepository { path, resolved, repository_root }
        }
        OpenRepositoryFileError::NotFile { path } => LoadCiError::InputNotFile { path },
    })
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
    /// A configured input's stable file-system identity could not be read.
    #[error("failed to inspect filesystem identity of CI input `{path}`: {source}")]
    InputIdentity {
        path: PathBuf,
        #[source]
        source: io::Error,
    },
    /// A path no longer named the file which was opened and retained.
    #[error(
        "CI input `{path}` changed while it was opened: first resolved to `{first}`, then to `{second}`"
    )]
    InputChangedDuringOpen {
        /// Configured path joined to the repository root.
        path: PathBuf,
        /// Canonical destination checked before opening.
        first: PathBuf,
        /// Canonical destination checked after opening.
        second: PathBuf,
    },
    /// A configured input resolved outside the checkout.
    #[error("CI input `{path}` resolves to `{resolved}`, outside repository `{repository_root}`")]
    InputOutsideRepository { path: PathBuf, resolved: PathBuf, repository_root: PathBuf },
    /// A configured input resolved to a directory or other non-file object.
    #[error("CI input `{path}` is not a regular file")]
    InputNotFile { path: PathBuf },
    /// Two independently reviewed baseline fields identify the same file.
    #[error(
        "CI baseline inputs `{first_field}` (`{first_path}`) and `{second_field}` (`{second_path}`) identify the same file"
    )]
    DuplicateBaselineInput {
        first_field: &'static str,
        first_path: PathBuf,
        second_field: &'static str,
        second_path: PathBuf,
    },
    /// The typed policy was unreadable or invalid.
    #[error(transparent)]
    Policy(ReadPolicyError),
    /// Live repository state did not satisfy the policy.
    #[error(transparent)]
    Inventory(AuditError),
    /// Workflow files or their reviewed role assignments were invalid.
    #[error(transparent)]
    Workflow(Box<WorkflowAuditError>),
    /// A behavioral audit expected a workflow absent from the checked tree.
    #[error("required CI workflow `{path}` was not discovered")]
    RequiredWorkflowMissing { path: String },
    /// The planned-job workflow bridge did not publish or execute plans exactly.
    #[error(transparent)]
    PlannedAdapter(PlannedAdapterAuditError),
    /// The standalone literal semver job did not implement policy.
    #[error(transparent)]
    SemverAdapter(SemverAdapterAuditError),
    /// The frozen legacy evidence was unreadable or noncanonical.
    #[error(transparent)]
    Baseline(BaselineError),
    /// Typed execution behavior differed from legacy or current-state evidence.
    #[error(transparent)]
    Execution(ExecutionAuditError),
}

#[cfg(test)]
mod tests {
    use std::{fs, path::Path, process::Command};

    use super::{
        open_repository_file, reject_duplicate_baseline_inputs, CiInputs, LoadCiError,
        OpenLegacyBaselineFiles,
    };
    use crate::baseline::LegacyBaselinePaths;

    /// Creates the complete input shape consumed by
    /// `reject_duplicate_baseline_inputs`, with one distinct regular file per
    /// field. Keep this list coordinated with `LegacyBaselinePaths` and the
    /// production field-name list in that function.
    fn write_distinct_baselines(repository: &Path) -> LegacyBaselinePaths {
        let paths = LegacyBaselinePaths {
            manifest: repository.join("manifest.tsv"),
            build_reduced: repository.join("build-reduced.tsv"),
            build_full: repository.join("build-full.tsv"),
            miri_reduced: repository.join("miri-reduced.tsv"),
            miri_full: repository.join("miri-full.tsv"),
            logical_obligations: repository.join("logical.tsv"),
            standalone_obligations: repository.join("standalone.tsv"),
            command_goldens: repository.join("commands.tsv"),
        };
        for path in [
            &paths.manifest,
            &paths.build_reduced,
            &paths.build_full,
            &paths.miri_reduced,
            &paths.miri_full,
            &paths.logical_obligations,
            &paths.standalone_obligations,
            &paths.command_goldens,
        ] {
            fs::write(path, format!("{}\n", path.display())).unwrap();
        }
        paths
    }

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
    fn repository_attributes_keep_ci_inputs_and_bootstrap_scripts_lf() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        // These paths represent every semantic extension consumed by CiInputs
        // plus the shell code which must run before the Rust reader exists. The
        // hypothetical YAML path keeps the currently unused `*.yaml` rule
        // checked as well. Keep the set coordinated with `.gitattributes` when
        // a new source-level input or bootstrap format is introduced.
        let paths = [
            "tools/toolchain.sh",
            "githooks/pre-push",
            ".github/ci-image/.dockerignore",
            ".github/ci-image/Dockerfile",
            ".github/workflows/ci.yml",
            "ci/future-input.yaml",
            "ci/zc.toml",
            "ci/workflow-jobs.tsv",
            "ci/baselines/command-goldens.tsv",
            "tools/zc/testdata/ci-image.Dockerfile",
            "tools/zc/testdata/ci-image.dockerignore",
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

        // Assigning `eol=lf` does not retroactively rewrite blobs already in
        // Git's index, and changing the attribute does not rewrite an existing
        // Windows worktree. `repository_text` handles the latter by
        // normalizing well-formed CRLF at the read boundary. Check the index
        // separately so adding or broadening a rule cannot leave a fresh
        // checkout dirty. A `w/crlf` worktree report is intentionally allowed.
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

        let error = open_repository_file(&repository, Path::new("ci/baseline.tsv")).unwrap_err();
        assert!(matches!(error, LoadCiError::InputOutsideRepository { .. }));

        fs::remove_dir_all(temporary).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn path_replacement_cannot_change_bytes_read_from_an_open_input() {
        use std::{
            os::unix::fs::symlink,
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-ci-open-handle-test-{}-{unique}", process::id()));
        let repository = temporary.join("repository");
        let configured = repository.join("ci/input.txt");
        let retained = repository.join("ci/retained.txt");
        let outside = temporary.join("outside.txt");
        fs::create_dir_all(configured.parent().unwrap()).unwrap();
        fs::write(&configured, "validated bytes\n").unwrap();
        fs::write(&outside, "replacement bytes\n").unwrap();
        let repository = repository.canonicalize().unwrap();

        let input = open_repository_file(&repository, Path::new("ci/input.txt")).unwrap();
        fs::rename(&configured, &retained).unwrap();
        symlink(&outside, &configured).unwrap();

        assert_eq!(input.read_to_string().unwrap(), "validated bytes\n");

        drop(input);
        fs::remove_dir_all(temporary).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn baseline_identity_and_bytes_share_the_retained_handles() {
        use std::{
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-ci-baseline-retained-handle-test-{}-{unique}", process::id()));
        fs::create_dir_all(&temporary).unwrap();
        let repository = temporary.canonicalize().unwrap();
        let paths = write_distinct_baselines(&repository);
        fs::write(&paths.build_reduced, "first bytes\n").unwrap();
        fs::write(&paths.build_full, "second bytes\n").unwrap();
        let inputs = OpenLegacyBaselineFiles::open_paths(&repository, &paths).unwrap();

        fs::remove_file(&paths.build_full).unwrap();
        fs::hard_link(&paths.build_reduced, &paths.build_full).unwrap();

        // The path names now alias, but the retained handles still identify
        // and read the two distinct files which were originally opened.
        reject_duplicate_baseline_inputs(&inputs).unwrap();
        assert_eq!(inputs.build_reduced.read_to_string().unwrap(), "first bytes\n");
        assert_eq!(inputs.build_full.read_to_string().unwrap(), "second bytes\n");

        drop(inputs);
        fs::remove_dir_all(temporary).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn rejects_baseline_fields_which_identify_one_file_through_a_symlink() {
        use std::{
            os::unix::fs::symlink,
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-ci-baseline-alias-test-{}-{unique}", process::id()));
        let repository = temporary.join("repository");
        fs::create_dir_all(&repository).unwrap();
        let repository = repository.canonicalize().unwrap();
        let paths = write_distinct_baselines(&repository);
        fs::remove_file(&paths.build_full).unwrap();
        symlink("build-reduced.tsv", &paths.build_full).unwrap();

        let inputs = OpenLegacyBaselineFiles::open_paths(&repository, &paths).unwrap();
        let resolved = inputs.paths();
        assert_eq!(resolved.build_reduced, resolved.build_full);

        let error = reject_duplicate_baseline_inputs(&inputs).unwrap_err();
        assert!(matches!(
            error,
            LoadCiError::DuplicateBaselineInput {
                first_field: "baselines.build_reduced",
                first_path,
                second_field: "baselines.build_full",
                second_path,
            } if first_path == resolved.build_reduced && second_path == resolved.build_full
        ));

        drop(inputs);
        fs::remove_dir_all(temporary).unwrap();
    }

    #[test]
    fn rejects_hard_linked_baseline_fields() {
        use std::{
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-ci-baseline-hard-link-test-{}-{unique}", process::id()));
        fs::create_dir_all(&temporary).unwrap();
        let repository = temporary.canonicalize().unwrap();
        let paths = write_distinct_baselines(&repository);
        fs::remove_file(&paths.build_full).unwrap();
        fs::hard_link(&paths.build_reduced, &paths.build_full).unwrap();

        let inputs = OpenLegacyBaselineFiles::open_paths(&repository, &paths).unwrap();
        let resolved = inputs.paths();
        assert_ne!(resolved.build_reduced, resolved.build_full);

        let error = reject_duplicate_baseline_inputs(&inputs).unwrap_err();
        assert!(matches!(
            error,
            LoadCiError::DuplicateBaselineInput {
                first_field: "baselines.build_reduced",
                first_path,
                second_field: "baselines.build_full",
                second_path,
            } if first_path == resolved.build_reduced && second_path == resolved.build_full
        ));

        drop(inputs);
        fs::remove_dir_all(temporary).unwrap();
    }

    #[test]
    fn accepts_distinct_baseline_files_with_identical_contents() {
        use std::{
            process,
            sync::atomic::{AtomicU64, Ordering},
        };

        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir().join(format!(
            "zerocopy-ci-baseline-identical-content-test-{}-{unique}",
            process::id()
        ));
        fs::create_dir_all(&temporary).unwrap();
        let repository = temporary.canonicalize().unwrap();
        let paths = write_distinct_baselines(&repository);
        fs::write(&paths.build_reduced, "identical\n").unwrap();
        fs::write(&paths.build_full, "identical\n").unwrap();

        let inputs = OpenLegacyBaselineFiles::open_paths(&repository, &paths).unwrap();
        reject_duplicate_baseline_inputs(&inputs).unwrap();

        drop(inputs);
        fs::remove_dir_all(temporary).unwrap();
    }
}
