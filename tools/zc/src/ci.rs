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
//! role, every independently recorded legacy baseline parses canonically, and
//! the typed execution model exactly reproduces that legacy evidence. Planners
//! therefore consume checked data rather than remembering which validation
//! passes must precede which lookups.

use std::{
    collections::HashMap,
    fs::File,
    io::{self, Read},
    path::{Path, PathBuf},
};

use same_file::Handle;
use thiserror::Error;

use crate::{
    baseline::{BaselineError, LegacyBaselineFiles, LegacyBaselinePaths, LegacyBaselines},
    execution::{audit_execution, ExecutionAuditError},
    inventory::{AuditError, RepositoryInventory},
    policy::{Baselines, Policy, ReadPolicyError},
    workflow::{
        audit_workflows, ReviewedWorkflowJobs, WorkflowAuditError, WorkflowRegistryError,
        WORKFLOW_REGISTRY_PATH,
    },
};

/// The repository-relative location of the typed CI policy.
pub const POLICY_PATH: &str = "ci/zc.toml";

/// All repository-owned inputs accepted for CI planning.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CiInputs {
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
            LoadCiError::Policy(ReadPolicyError::Read { path: policy_file.path.clone(), source })
        })?;
        let policy = Policy::parse(&policy_source).map_err(|source| {
            LoadCiError::Policy(ReadPolicyError::Policy { path: policy_file.path.clone(), source })
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
                WorkflowRegistryError::Read { path: workflow_registry.path.clone(), source },
            )))
        })?;
        let reviewed_workflow_jobs =
            ReviewedWorkflowJobs::parse(&workflow_registry.path, &workflow_registry_source)
                .map_err(|error| {
                    LoadCiError::Workflow(Box::new(WorkflowAuditError::Registry(error)))
                })?;
        let (workflow_jobs, _workflow_sources) =
            audit_workflows(&repository_root, reviewed_workflow_jobs)
                .map_err(|error| LoadCiError::Workflow(Box::new(error)))?;
        let repository = RepositoryInventory::audit(&repository_root, &policy)
            .map_err(LoadCiError::Inventory)?;
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
        let inputs = Self { policy, repository, workflow_jobs, legacy };
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
}

/// One repository input whose containment, type, identity, and bytes all come
/// from one retained operating-system handle.
#[derive(Debug)]
struct OpenedRepositoryFile {
    path: PathBuf,
    file: File,
    identity: Handle,
}

impl OpenedRepositoryFile {
    fn read_to_string(&self) -> io::Result<String> {
        let mut source = String::new();
        let mut reader = &self.file;
        reader.read_to_string(&mut source)?;
        Ok(source)
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
            manifest: self.manifest.path.clone(),
            build_reduced: self.build_reduced.path.clone(),
            build_full: self.build_full.path.clone(),
            miri_reduced: self.miri_reduced.path.clone(),
            miri_full: self.miri_full.path.clone(),
            logical_obligations: self.logical_obligations.path.clone(),
            standalone_obligations: self.standalone_obligations.path.clone(),
            command_goldens: self.command_goldens.path.clone(),
        }
    }

    fn files(&self) -> LegacyBaselineFiles<'_> {
        LegacyBaselineFiles {
            manifest: &self.manifest.file,
            build_reduced: &self.build_reduced.file,
            build_full: &self.build_full.file,
            miri_reduced: &self.miri_reduced.file,
            miri_full: &self.miri_full.file,
            logical_obligations: &self.logical_obligations.file,
            standalone_obligations: &self.standalone_obligations.file,
            command_goldens: &self.command_goldens.file,
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
            first_input_by_identity.insert(&input.identity, (field, input.path.as_path()))
        {
            return Err(LoadCiError::DuplicateBaselineInput {
                first_field,
                first_path: first_path.to_path_buf(),
                second_field: field,
                second_path: input.path.clone(),
            });
        }
    }
    Ok(())
}

/// Opens one repository input and rejects static redirection.
///
/// Policy syntax already rejects absolute paths and `..`, and fixed runtime
/// paths are repository-relative constants. A Git-tracked symlink can still
/// point outside the checkout. Canonical containment is a separate file-system
/// invariant and belongs at the boundary which opens the file. Resolve once,
/// open that spelling, then resolve and compare identity again. The second
/// lookup detects ordinary replacement observed while the file is opened, and
/// a later path replacement cannot affect the retained handle which supplies
/// the accepted bytes.
///
/// These path operations are not one atomic filesystem transaction. This
/// boundary assumes that no hostile process is deliberately racing each
/// lookup; enforcing containment against such a writer would require
/// platform-specific, capability-relative opening rather than canonical paths.
fn open_repository_file(
    repository_root: &Path,
    configured: &Path,
) -> Result<OpenedRepositoryFile, LoadCiError> {
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
    let file = File::open(&resolved)
        .map_err(|source| LoadCiError::InputPath { path: resolved.clone(), source })?;
    let metadata = file
        .metadata()
        .map_err(|source| LoadCiError::InputPath { path: resolved.clone(), source })?;
    if !metadata.is_file() {
        return Err(LoadCiError::InputNotFile { path: resolved });
    }
    let identity_file = file
        .try_clone()
        .map_err(|source| LoadCiError::InputIdentity { path: resolved.clone(), source })?;
    let identity = Handle::from_file(identity_file)
        .map_err(|source| LoadCiError::InputIdentity { path: resolved.clone(), source })?;

    let rechecked = path
        .canonicalize()
        .map_err(|source| LoadCiError::InputPath { path: path.clone(), source })?;
    if !rechecked.starts_with(repository_root) {
        return Err(LoadCiError::InputOutsideRepository {
            path,
            resolved: rechecked,
            repository_root: repository_root.to_path_buf(),
        });
    }
    let current_identity = Handle::from_path(&rechecked)
        .map_err(|source| LoadCiError::InputIdentity { path: rechecked.clone(), source })?;
    if rechecked != resolved || current_identity != identity {
        return Err(LoadCiError::InputChangedDuringOpen {
            path,
            first: resolved,
            second: rechecked,
        });
    }
    Ok(OpenedRepositoryFile { path: rechecked, file, identity })
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
    /// The frozen legacy evidence was unreadable or noncanonical.
    #[error(transparent)]
    Baseline(BaselineError),
    /// Typed execution behavior differed from frozen legacy evidence.
    #[error(transparent)]
    Execution(ExecutionAuditError),
}

#[cfg(test)]
mod tests {
    use std::{fs, path::Path};

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
