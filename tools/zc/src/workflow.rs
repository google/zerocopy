// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Fail-closed inventory of GitHub workflow files and top-level job IDs.
//!
//! Most CI policy should be derived from Cargo metadata and [`crate::policy`].
//! Workflow files are the unavoidable exception: GitHub discovers them by
//! filename, and a newly added job can bypass a typed planner unless something
//! inventories the handwritten YAML boundary itself.
//!
//! This module parses YAML only to locate the root `jobs` mapping and its keys;
//! `action-validator` remains responsible for the full Actions schema. A real
//! YAML parser is important at this trust boundary: comments, multiline
//! scalars, flow collections, aliases, tags, and document boundaries must not
//! make the inventory disagree with GitHub about which jobs exist.
//! The inventory then proves that every discovered job ID is present in a small
//! reviewed registry.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    fs::{self, File},
    io::{self, Read},
    path::{Path, PathBuf},
};

use thiserror::Error;

const WORKFLOW_DIRECTORY: &str = ".github/workflows";
const REGISTRY_HEADER: &str = "workflow\tjob\trole";

/// The repository-relative reviewed classification of every workflow job.
///
/// Keep this path coordinated with [`crate::ci::CiInputs::load`], which sends
/// it through the same canonical containment check as every other planning
/// input before this module reads it.
pub const WORKFLOW_REGISTRY_PATH: &str = "ci/workflow-jobs.tsv";

/// A slash-separated path beneath `.github/workflows`.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct WorkflowPath(String);

impl WorkflowPath {
    fn parse(value: &str) -> Result<Self, String> {
        let prefix = format!("{WORKFLOW_DIRECTORY}/");
        let Some(name) = value.strip_prefix(&prefix) else {
            return Err(format!("must start with `{prefix}`"));
        };
        if name.is_empty() || name.contains('/') || name.contains('\\') {
            return Err("must name one file directly under the workflow directory".into());
        }
        let extension = workflow_extension(Path::new(name));
        if !matches!(extension, Some("yml" | "yaml")) {
            return Err("must end in `.yml` or `.yaml`".into());
        }
        if value.chars().any(char::is_control) {
            return Err("must not contain control characters".into());
        }
        Ok(Self(value.to_owned()))
    }

    /// Returns the repository-relative path with `/` separators.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for WorkflowPath {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// A canonical GitHub Actions job ID.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct JobId(String);

impl JobId {
    fn parse(value: &str) -> Result<Self, String> {
        let mut bytes = value.bytes();
        let Some(first) = bytes.next() else {
            return Err("must not be empty".into());
        };
        if !(first.is_ascii_alphabetic() || first == b'_') {
            return Err("must start with an ASCII letter or underscore".into());
        }
        if !bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-')) {
            return Err("may contain only ASCII letters, digits, `_`, and `-`".into());
        }
        Ok(Self(value.to_owned()))
    }

    /// Returns the job ID exactly as GitHub sees it.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for JobId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// The top-level jobs discovered in one workflow file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WorkflowInventory {
    /// Repository-relative workflow path.
    pub path: WorkflowPath,
    /// Every job ID declared directly beneath the top-level `jobs:` key.
    pub jobs: BTreeSet<JobId>,
}

/// The exact bytes and job inventory read from one workflow-tree snapshot.
///
/// The source map is intentionally kept beside the inventories derived from
/// it. Behavioral audits must consume these stored bytes instead of reopening
/// a path after the job inventory has already approved a different version.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct WorkflowSources {
    inventories: Vec<WorkflowInventory>,
    sources: BTreeMap<WorkflowPath, String>,
}

impl WorkflowSources {
    /// Returns the already-read source for one GitHub-visible workflow path.
    #[cfg(test)]
    pub(crate) fn source(&self, path: &str) -> Option<&str> {
        self.sources
            .iter()
            .find_map(|(candidate, source)| (candidate.as_str() == path).then_some(source.as_str()))
    }

    fn into_inventories(self) -> Vec<WorkflowInventory> {
        self.inventories
    }
}

/// One workflow/job pair, used as the exact registry key.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct WorkflowJob {
    /// Repository-relative workflow path.
    pub workflow: WorkflowPath,
    /// Top-level job ID.
    pub job: JobId,
}

/// Why a handwritten workflow job remains in the Actions security boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WorkflowJobRole {
    /// The typed planner is intended to produce this job's safe matrix data.
    Planned,
    /// Handwritten, unprivileged CI outside the generated test matrices.
    StaticCi,
    /// A required-check job which aggregates other job conclusions.
    Aggregate,
    /// Anneal work, which retains a separate Nix-backed migration path.
    Anneal,
    /// Credentialed or externally publishing release work.
    Release,
    /// Repository maintenance which is not part of pull-request validation.
    Maintenance,
    /// Documentation build or deployment work.
    Documentation,
    /// A security scanner or dependency policy check.
    Security,
}

impl WorkflowJobRole {
    fn parse(value: &str) -> Option<Self> {
        Some(match value {
            "planned" => Self::Planned,
            "static-ci" => Self::StaticCi,
            "aggregate" => Self::Aggregate,
            "anneal" => Self::Anneal,
            "release" => Self::Release,
            "maintenance" => Self::Maintenance,
            "documentation" => Self::Documentation,
            "security" => Self::Security,
            _ => return None,
        })
    }
}

/// Exact reviewed classification of every workflow job.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReviewedWorkflowJobs {
    jobs: BTreeMap<WorkflowJob, WorkflowJobRole>,
}

impl ReviewedWorkflowJobs {
    /// Reads the line-oriented workflow registry at `path`.
    pub fn read(path: impl AsRef<Path>) -> Result<Self, WorkflowRegistryError> {
        let path = path.as_ref();
        let source = fs::read_to_string(path)
            .map_err(|source| WorkflowRegistryError::Read { path: path.to_path_buf(), source })?;
        Self::parse(path, &source)
    }

    fn parse(path: &Path, source: &str) -> Result<Self, WorkflowRegistryError> {
        let mut saw_header = false;
        let mut previous: Option<WorkflowJob> = None;
        let mut jobs = BTreeMap::new();

        for (line_index, line) in source.lines().enumerate() {
            let line_number = line_index + 1;
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if !saw_header {
                if line != REGISTRY_HEADER {
                    return Err(WorkflowRegistryError::Header {
                        path: path.to_path_buf(),
                        line: line_number,
                        found: escape_control_characters(line),
                    });
                }
                saw_header = true;
                continue;
            }

            let fields = line.split('\t').collect::<Vec<_>>();
            if fields.len() != 3 {
                return Err(WorkflowRegistryError::FieldCount {
                    path: path.to_path_buf(),
                    line: line_number,
                    found: fields.len(),
                });
            }
            let workflow = WorkflowPath::parse(fields[0]).map_err(|reason| {
                WorkflowRegistryError::WorkflowPath {
                    path: path.to_path_buf(),
                    line: line_number,
                    value: escape_control_characters(fields[0]),
                    reason,
                }
            })?;
            let job = JobId::parse(fields[1]).map_err(|reason| WorkflowRegistryError::JobId {
                path: path.to_path_buf(),
                line: line_number,
                value: escape_control_characters(fields[1]),
                reason,
            })?;
            let role =
                WorkflowJobRole::parse(fields[2]).ok_or_else(|| WorkflowRegistryError::Role {
                    path: path.to_path_buf(),
                    line: line_number,
                    value: escape_control_characters(fields[2]),
                })?;
            let key = WorkflowJob { workflow, job };

            if let Some(previous) = &previous {
                if &key <= previous {
                    return Err(WorkflowRegistryError::Order {
                        path: path.to_path_buf(),
                        line: line_number,
                        previous: Box::new(previous.clone()),
                        current: Box::new(key),
                    });
                }
            }
            previous = Some(key.clone());
            jobs.insert(key, role);
        }

        if !saw_header {
            return Err(WorkflowRegistryError::MissingHeader { path: path.to_path_buf() });
        }
        if jobs.is_empty() {
            return Err(WorkflowRegistryError::Empty { path: path.to_path_buf() });
        }
        Ok(Self { jobs })
    }

    /// Returns the reviewed role for `job`, if the exact key is registered.
    pub fn role(&self, job: &WorkflowJob) -> Option<WorkflowJobRole> {
        self.jobs.get(job).copied()
    }
}

/// Checks every live workflow job against its reviewed role assignment.
///
/// `reviewed_registry` must be the canonical path returned by the CI input
/// boundary's containment check. Keeping resolution there prevents a caller
/// from validating one path and reopening a different spelling here. This
/// function then performs the remaining workflow-specific boundary exactly
/// once: it reads the strict registry, scans every workflow, and reports all
/// missing or unreviewed jobs together in deterministic order.
// This validator deliberately lands before the all-input boundary in `ci.rs`
// so its scanner and reviewed registry can be examined independently. The
// later wiring commit removes this temporary allowance when production code
// begins calling it; tests exercise it in the meantime.
#[allow(dead_code)]
pub(crate) fn audit_workflows(
    repository_root: impl AsRef<Path>,
    reviewed_registry: impl AsRef<Path>,
) -> Result<ReviewedWorkflowJobs, WorkflowAuditError> {
    let reviewed = ReviewedWorkflowJobs::read(reviewed_registry)?;
    let actual = read_workflow_sources(repository_root)?;
    let violations = compare_with_reviewed(&actual.inventories, &reviewed);
    if violations.is_empty() {
        Ok(reviewed)
    } else {
        Err(WorkflowAuditError::Violations(WorkflowAuditViolations(violations)))
    }
}

/// Discovers every Actions workflow and scans its top-level job IDs.
pub fn discover_workflows(
    repository_root: impl AsRef<Path>,
) -> Result<Vec<WorkflowInventory>, WorkflowInventoryError> {
    Ok(read_workflow_sources(repository_root)?.into_inventories())
}

/// Opens every workflow once and scans the exact bytes retained for later
/// behavioral audits.
fn read_workflow_sources(
    repository_root: impl AsRef<Path>,
) -> Result<WorkflowSources, WorkflowInventoryError> {
    let supplied_root = repository_root.as_ref();
    let repository_root = supplied_root.canonicalize().map_err(|source| {
        WorkflowInventoryError::ResolveRepositoryRoot { path: supplied_root.to_path_buf(), source }
    })?;
    let directory = repository_root.join(WORKFLOW_DIRECTORY);
    let resolved_directory = directory.canonicalize().map_err(|source| {
        WorkflowInventoryError::ReadDirectory { path: directory.clone(), source }
    })?;
    // GitHub discovers workflows from this exact repository-tree directory; it
    // does not interpret a checked-in symlink as a directory. Require the local
    // checkout to have the same shape. Exact equality also rejects an
    // intermediate `.github` symlink, including one whose target stays inside
    // the checkout.
    if resolved_directory != directory {
        return Err(WorkflowInventoryError::RedirectedWorkflowDirectory {
            path: directory,
            resolved: resolved_directory,
        });
    }
    let entries = fs::read_dir(&directory).map_err(|source| {
        WorkflowInventoryError::ReadDirectory { path: directory.clone(), source }
    })?;
    let mut entries = entries.collect::<Result<Vec<_>, _>>().map_err(|source| {
        WorkflowInventoryError::ReadDirectoryEntry { path: directory.clone(), source }
    })?;
    // `read_dir` explicitly makes no ordering guarantee. Validate candidates
    // only after sorting so two malformed names report the same first error on
    // every checkout and filesystem.
    entries.sort_by_key(|entry| entry.path());
    let mut workflow_files = Vec::new();

    for entry in entries {
        let path = entry.path();
        if !is_workflow_path(&path)? {
            continue;
        }
        let file_name = path.file_name().and_then(|value| value.to_str()).ok_or_else(|| {
            WorkflowInventoryError::NonUtf8Path {
                display_path: diagnostic_path(&path),
                path: path.clone(),
            }
        })?;
        let workflow_path = WorkflowPath::parse(&format!("{WORKFLOW_DIRECTORY}/{file_name}"))
            .map_err(|reason| WorkflowInventoryError::InvalidWorkflowPath {
                display_path: diagnostic_path(&path),
                path: path.clone(),
                reason,
            })?;
        let file_type = entry.file_type().map_err(|source| {
            WorkflowInventoryError::InspectWorkflow { path: path.clone(), source }
        })?;
        if !file_type.is_file() {
            return Err(WorkflowInventoryError::NotAFile { path });
        }
        workflow_files.push((path, workflow_path));
    }
    workflow_files.sort();
    if workflow_files.is_empty() {
        return Err(WorkflowInventoryError::NoWorkflowFiles { path: directory });
    }

    let mut inventories = Vec::with_capacity(workflow_files.len());
    let mut sources = BTreeMap::new();
    for (path, workflow_path) in workflow_files {
        let file = File::open(&path).map_err(|source| WorkflowInventoryError::ReadWorkflow {
            path: path.clone(),
            source,
        })?;
        let metadata = file.metadata().map_err(|source| {
            WorkflowInventoryError::InspectWorkflow { path: path.clone(), source }
        })?;
        // Recheck the opened object, rather than relying only on the earlier
        // directory-entry observation. An ordinary replacement which changes
        // the candidate to a directory or special file must not be read.
        if !metadata.is_file() {
            return Err(WorkflowInventoryError::NotAFile { path });
        }
        let source = read_open_workflow(&file).map_err(|source| {
            WorkflowInventoryError::ReadWorkflow { path: path.clone(), source }
        })?;
        let inventory = scan_workflow(workflow_path.clone(), &source)?;
        inventories.push(inventory);
        assert!(sources.insert(workflow_path, source).is_none());
    }
    Ok(WorkflowSources { inventories, sources })
}

fn read_open_workflow(file: &File) -> io::Result<String> {
    let mut file = file;
    let mut source = String::new();
    file.read_to_string(&mut source)?;
    Ok(source)
}

fn is_workflow_path(path: &Path) -> Result<bool, WorkflowInventoryError> {
    let extension = workflow_extension(path);
    match extension {
        Some("yml" | "yaml") => Ok(true),
        Some(extension) if matches!(extension.to_ascii_lowercase().as_str(), "yml" | "yaml") => {
            Err(WorkflowInventoryError::NonCanonicalExtension {
                display_path: diagnostic_path(path),
                path: path.to_path_buf(),
                extension: extension.to_owned(),
            })
        }
        _ => Ok(false),
    }
}

/// Returns the final extension, including an extension-only filename.
///
/// `Path::extension` deliberately treats a leading dot as part of a Unix
/// filename rather than as an extension separator. GitHub does not make that
/// distinction when it discovers workflow YAML, so `.yml` and `.yaml` must
/// pass through the same inventory and canonical-case checks as `ci.yml`.
/// Keep `Path::extension` as the first choice so a non-UTF-8 stem with an
/// ASCII YAML extension remains a candidate and receives the existing
/// non-UTF-8-path diagnostic later in discovery.
fn workflow_extension(path: &Path) -> Option<&str> {
    path.extension().and_then(|value| value.to_str()).or_else(|| {
        path.file_name().and_then(|value| value.to_str()).and_then(|name| name.strip_prefix('.'))
    })
}

/// Parses one workflow's top-level `jobs` mapping.
pub fn scan_workflow(
    path: WorkflowPath,
    source: &str,
) -> Result<WorkflowInventory, WorkflowInventoryError> {
    // Use the parser's generic representation rather than deserializing into
    // ordinary Rust maps. `yaml_serde::Mapping` rejects duplicate YAML keys
    // instead of silently selecting one, including nested duplicates in
    // `jobs`, while the parser itself resolves aliases and bounds recursion and
    // alias replay. A direct `from_str` also rejects a second YAML document.
    let document: yaml_serde::Value = yaml_serde::from_str(source).map_err(|source| {
        WorkflowInventoryError::ParseWorkflowYaml { path: path.clone(), source }
    })?;
    let yaml_serde::Value::Mapping(root) = document else {
        return Err(WorkflowInventoryError::RootNotMapping { path });
    };
    let jobs_value = root
        .get("jobs")
        .ok_or_else(|| WorkflowInventoryError::MissingJobsKey { path: path.clone() })?;
    let yaml_serde::Value::Mapping(jobs_mapping) = jobs_value else {
        return Err(WorkflowInventoryError::JobsNotMapping { path });
    };

    let mut jobs = BTreeSet::new();
    for key in jobs_mapping.keys() {
        let yaml_serde::Value::String(key) = key else {
            return Err(WorkflowInventoryError::UnsupportedJobId {
                path,
                key: format!("{key:?}"),
                reason: "must be a YAML string".into(),
            });
        };
        let job = JobId::parse(key).map_err(|reason| WorkflowInventoryError::UnsupportedJobId {
            path: path.clone(),
            key: format!("{key:?}"),
            reason,
        })?;
        // `yaml_serde::Mapping` already rejects duplicate YAML keys. Retain a
        // typed backstop so a future representation cannot silently weaken the
        // inventory's one-job-ID-per-workflow invariant or turn drift into a
        // panic.
        if !jobs.insert(job.clone()) {
            return Err(WorkflowInventoryError::DuplicateJobId { path, job });
        }
    }
    if jobs.is_empty() {
        return Err(WorkflowInventoryError::EmptyJobs { path });
    }
    Ok(WorkflowInventory { path, jobs })
}

fn escape_control_characters(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for character in value.chars() {
        if character.is_control() {
            escaped.extend(character.escape_default());
        } else {
            escaped.push(character);
        }
    }
    escaped
}

fn diagnostic_path(path: &Path) -> String {
    escape_control_characters(&path.to_string_lossy())
}

/// Compares discovered workflow jobs with the exact reviewed registry.
pub fn compare_with_reviewed(
    actual: &[WorkflowInventory],
    reviewed: &ReviewedWorkflowJobs,
) -> Vec<WorkflowInventoryViolation> {
    let actual = actual
        .iter()
        .flat_map(|workflow| {
            workflow
                .jobs
                .iter()
                .cloned()
                .map(|job| WorkflowJob { workflow: workflow.path.clone(), job })
        })
        .collect::<BTreeSet<_>>();
    let expected = reviewed.jobs.keys().cloned().collect::<BTreeSet<_>>();

    expected
        .difference(&actual)
        .cloned()
        .map(WorkflowInventoryViolation::Missing)
        .chain(actual.difference(&expected).cloned().map(WorkflowInventoryViolation::Unreviewed))
        .collect()
}

/// A mismatch between the live workflow tree and its reviewed registry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WorkflowInventoryViolation {
    /// A reviewed job disappeared from the workflow tree.
    Missing(WorkflowJob),
    /// A live job has no reviewed classification.
    Unreviewed(WorkflowJob),
}

impl fmt::Display for WorkflowInventoryViolation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Missing(job) => write!(
                formatter,
                "reviewed job `{}/{}` is absent; restore it or remove its stale row from `{WORKFLOW_REGISTRY_PATH}`",
                job.workflow, job.job,
            ),
            Self::Unreviewed(job) => write!(
                formatter,
                "live job `{}/{}` has no reviewed role; add a sorted row to `{WORKFLOW_REGISTRY_PATH}`",
                job.workflow, job.job,
            ),
        }
    }
}

/// Deterministically ordered workflow-registry differences.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WorkflowAuditViolations(Vec<WorkflowInventoryViolation>);

impl WorkflowAuditViolations {
    /// Returns every missing or unreviewed workflow job.
    pub fn as_slice(&self) -> &[WorkflowInventoryViolation] {
        &self.0
    }
}

impl fmt::Display for WorkflowAuditViolations {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for violation in &self.0 {
            writeln!(formatter, "- {violation}")?;
        }
        Ok(())
    }
}

/// A failure at the checked workflow-inventory boundary.
#[derive(Debug, Error)]
pub enum WorkflowAuditError {
    /// The reviewed job registry was unreadable or noncanonical.
    #[error(transparent)]
    Registry(#[from] WorkflowRegistryError),
    /// Live workflow files could not be discovered or narrowly scanned.
    #[error(transparent)]
    Inventory(#[from] WorkflowInventoryError),
    /// Live jobs and reviewed role assignments differed.
    #[error("live workflow jobs do not match their reviewed roles:\n{0}")]
    Violations(WorkflowAuditViolations),
}

/// An error discovering or scanning live workflow files.
#[derive(Debug, Error)]
pub enum WorkflowInventoryError {
    /// The supplied repository root could not be resolved before containment
    /// checks.
    #[error("failed to resolve repository root `{path}`: {source}")]
    ResolveRepositoryRoot {
        /// Repository root supplied by the caller.
        path: PathBuf,
        /// Underlying filesystem error.
        #[source]
        source: io::Error,
    },
    /// The workflow directory could not be listed.
    #[error("failed to read workflow directory `{path}`: {source}")]
    ReadDirectory {
        /// Workflow directory.
        path: PathBuf,
        /// Underlying filesystem error.
        #[source]
        source: io::Error,
    },
    /// A symlink made the local workflow directory differ from the Git tree.
    #[error("workflow directory `{path}` resolves to redirected path `{resolved}`")]
    RedirectedWorkflowDirectory {
        /// Exact repository-tree path GitHub inspects.
        path: PathBuf,
        /// Canonical local target which must not be followed.
        resolved: PathBuf,
    },
    /// One directory entry could not be read.
    #[error("failed to read an entry in workflow directory `{path}`: {source}")]
    ReadDirectoryEntry {
        /// Workflow directory.
        path: PathBuf,
        /// Underlying filesystem error.
        #[source]
        source: io::Error,
    },
    /// A candidate workflow's file type could not be inspected.
    #[error("failed to inspect workflow `{path}`: {source}")]
    InspectWorkflow {
        /// Candidate path.
        path: PathBuf,
        /// Underlying filesystem error.
        #[source]
        source: io::Error,
    },
    /// A `.yml` or `.yaml` entry was not a regular file.
    #[error("workflow candidate `{path}` is not a regular file")]
    NotAFile {
        /// Candidate path.
        path: PathBuf,
    },
    /// A YAML-like filename used uppercase characters in its extension.
    #[error(
        "workflow candidate `{display_path}` uses noncanonical extension `.{extension}`; use lowercase `.yml` or `.yaml`"
    )]
    NonCanonicalExtension {
        /// Candidate path.
        path: PathBuf,
        /// Candidate path with control characters escaped for diagnostics.
        display_path: String,
        /// Extension as found on disk.
        extension: String,
    },
    /// No workflow files were discovered.
    #[error("workflow directory `{path}` contains no .yml or .yaml files")]
    NoWorkflowFiles {
        /// Workflow directory.
        path: PathBuf,
    },
    /// A workflow filename was not valid UTF-8.
    #[error("workflow path `{display_path}` is not valid UTF-8")]
    NonUtf8Path {
        /// Candidate path.
        path: PathBuf,
        /// Candidate path with control characters escaped for diagnostics.
        display_path: String,
    },
    /// A workflow filename could not be represented by the registry path type.
    #[error("workflow candidate `{display_path}` has an unsupported path: {reason}")]
    InvalidWorkflowPath {
        /// Candidate path.
        path: PathBuf,
        /// Candidate path with control characters escaped for diagnostics.
        display_path: String,
        /// Plain-language validation failure.
        reason: String,
    },
    /// A workflow file could not be read.
    #[error("failed to read workflow `{path}`: {source}")]
    ReadWorkflow {
        /// Workflow path.
        path: PathBuf,
        /// Underlying filesystem error.
        #[source]
        source: io::Error,
    },
    /// A workflow was not one well-formed YAML document.
    #[error("failed to parse workflow `{path}` as one YAML document: {source}")]
    ParseWorkflowYaml {
        /// Workflow path.
        path: WorkflowPath,
        /// YAML syntax or representation error.
        #[source]
        source: yaml_serde::Error,
    },
    /// The workflow document's root was not a mapping.
    #[error("workflow `{path}` has a non-mapping YAML document root")]
    RootNotMapping {
        /// Workflow path.
        path: WorkflowPath,
    },
    /// The top-level `jobs` key was missing.
    #[error("workflow `{path}` has no top-level `jobs` key")]
    MissingJobsKey {
        /// Workflow path.
        path: WorkflowPath,
    },
    /// The top-level `jobs` value was not a mapping.
    #[error("workflow `{path}` has a non-mapping top-level `jobs` value")]
    JobsNotMapping {
        /// Workflow path.
        path: WorkflowPath,
    },
    /// A jobs-mapping key was not a canonical GitHub Actions job ID.
    #[error("workflow `{path}` has unsupported job ID {key}: {reason}")]
    UnsupportedJobId {
        /// Workflow path.
        path: WorkflowPath,
        /// Parsed YAML key, formatted for diagnostics.
        key: String,
        /// Plain-language validation failure.
        reason: String,
    },
    /// Two YAML keys normalized to the same canonical job ID.
    #[error("workflow `{path}` repeats job ID `{job}`")]
    DuplicateJobId {
        /// Workflow path.
        path: WorkflowPath,
        /// Repeated canonical job ID.
        job: JobId,
    },
    /// The jobs mapping was empty.
    #[error("workflow `{path}` declares no jobs")]
    EmptyJobs {
        /// Workflow path.
        path: WorkflowPath,
    },
}

/// An error reading the reviewed workflow registry.
#[derive(Debug, Error)]
pub enum WorkflowRegistryError {
    /// The registry file could not be read.
    #[error("failed to read workflow registry `{path}`: {source}")]
    Read {
        /// Registry path.
        path: PathBuf,
        /// Underlying filesystem error.
        #[source]
        source: io::Error,
    },
    /// The registry had no header.
    #[error("workflow registry `{path}` has no `{REGISTRY_HEADER}` header")]
    MissingHeader {
        /// Registry path.
        path: PathBuf,
    },
    /// The first data-like line was not the exact header.
    #[error("workflow registry `{path}` has invalid header at line {line}: {found}")]
    Header {
        /// Registry path.
        path: PathBuf,
        /// One-based source line.
        line: usize,
        /// Text found instead.
        found: String,
    },
    /// A row did not have three tab-separated fields.
    #[error("workflow registry `{path}` row {line} has {found} fields, expected 3")]
    FieldCount {
        /// Registry path.
        path: PathBuf,
        /// One-based source line.
        line: usize,
        /// Observed field count.
        found: usize,
    },
    /// A row contained an invalid workflow path.
    #[error("workflow registry `{path}` row {line} has invalid path `{value}`: {reason}")]
    WorkflowPath {
        /// Registry path.
        path: PathBuf,
        /// One-based source line.
        line: usize,
        /// Invalid value.
        value: String,
        /// Plain-language reason.
        reason: String,
    },
    /// A row contained an invalid job ID.
    #[error("workflow registry `{path}` row {line} has invalid job `{value}`: {reason}")]
    JobId {
        /// Registry path.
        path: PathBuf,
        /// One-based source line.
        line: usize,
        /// Invalid value.
        value: String,
        /// Plain-language reason.
        reason: String,
    },
    /// A row contained an unknown role.
    #[error("workflow registry `{path}` row {line} has unknown role `{value}`")]
    Role {
        /// Registry path.
        path: PathBuf,
        /// One-based source line.
        line: usize,
        /// Invalid value.
        value: String,
    },
    /// Rows were duplicated or not sorted by workflow and job.
    #[error(
        "workflow registry `{path}` is not strictly sorted at line {line}: `{current:?}` follows `{previous:?}`"
    )]
    Order {
        /// Registry path.
        path: PathBuf,
        /// One-based source line.
        line: usize,
        /// Previous key.
        previous: Box<WorkflowJob>,
        /// Current key.
        current: Box<WorkflowJob>,
    },
    /// The registry had no rows.
    #[error("workflow registry `{path}` contains no jobs")]
    Empty {
        /// Registry path.
        path: PathBuf,
    },
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::Path,
        process,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::{
        audit_workflows, compare_with_reviewed, discover_workflows, read_workflow_sources,
        scan_workflow, JobId, ReviewedWorkflowJobs, WorkflowAuditError, WorkflowInventoryError,
        WorkflowInventoryViolation, WorkflowJob, WorkflowPath, WORKFLOW_REGISTRY_PATH,
    };

    static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    fn temporary_directory(label: &str) -> std::path::PathBuf {
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir().join(format!("zerocopy-workflow-{label}-{}-{unique}", process::id()))
    }

    fn path() -> WorkflowPath {
        WorkflowPath::parse(".github/workflows/test.yml").unwrap()
    }

    #[test]
    fn scans_canonical_job_declarations() {
        let inventory = scan_workflow(
            path(),
            "name: Josh's Test\non: [push]\npermissions: {}\njobs:\n  alpha:\n    runs-on: ubuntu-latest\n    steps:\n      - run: |\n          printf '\"{\n  beta-2:\n    uses: ./job.yml\n",
        )
        .unwrap();
        assert_eq!(
            inventory.jobs.into_iter().map(|job| job.0).collect::<Vec<_>>(),
            ["alpha", "beta-2"]
        );
    }

    #[test]
    fn accepts_one_leading_yaml_byte_order_mark() {
        for line_ending in ["\n", "\r\n"] {
            let source = format!(
                "\u{feff}jobs:{line_ending}  expected:{line_ending}    runs-on: ubuntu-latest{line_ending}"
            );
            let inventory = scan_workflow(path(), &source).unwrap();
            assert_eq!(inventory.jobs, [JobId::parse("expected").unwrap()].into_iter().collect());
        }
    }

    #[test]
    fn accepts_crlf_and_lone_cr_line_endings() {
        let canonical =
            "name: Test\non:\n  push:\njobs:\n  expected:\n    runs-on: ubuntu-latest\n";
        for source in [canonical.replace('\n', "\r\n"), canonical.replace('\n', "\r")] {
            let inventory = scan_workflow(path(), &source).unwrap();
            assert_eq!(inventory.jobs, [JobId::parse("expected").unwrap()].into_iter().collect());
        }
    }

    #[test]
    fn yaml_line_breaks_cannot_hide_a_replacement_jobs_mapping() {
        // YAML recognizes more line breaks than Rust's `str::lines`. This
        // exact shape was an adversarial regression for the former
        // line-oriented lexer: it could see only `expected` while a YAML
        // parser saw a second top-level `jobs` mapping. The real parser must
        // either detect the duplicate or reject the separator, never accept
        // an inventory containing only `expected`.
        for separator in ["\r", "\u{85}", "\u{2028}", "\u{2029}"] {
            let source = format!(
                "jobs:\n  expected:\n    runs-on: ubuntu-latest{separator}jobs :{separator}  hidden:\n"
            );
            let error = scan_workflow(path(), &source).unwrap_err();
            assert!(
                matches!(error, WorkflowInventoryError::ParseWorkflowYaml { .. }),
                "unexpected error for {separator:?}: {error:?}"
            );
        }
    }

    #[test]
    fn parses_one_explicit_document_and_rejects_multiple_documents() {
        let source = "--- { name: \"\njobs:\n  reviewed:\n    scalar\", \"on\": push, jobs: { hidden: { runs-on: ubuntu-latest } } }\n";
        let inventory = scan_workflow(path(), source).unwrap();
        assert_eq!(inventory.jobs, [JobId::parse("hidden").unwrap()].into_iter().collect());

        let error =
            scan_workflow(path(), "---\njobs: { expected: {} }\n---\njobs: { hidden: {} }\n")
                .unwrap_err();
        assert!(matches!(error, WorkflowInventoryError::ParseWorkflowYaml { .. }));
        assert!(error.to_string().contains("more than one document"), "{error:?}");
    }

    #[test]
    fn rejects_invalid_workflow_shapes_and_job_ids() {
        let cases = [
            ("- scalar\n", "non-mapping YAML document root"),
            ("name: Test\n", "no top-level `jobs`"),
            ("jobs: scalar\n", "non-mapping top-level `jobs`"),
            ("jobs: {}\n", "declares no jobs"),
            ("jobs: { 1: {} }\n", "must be a YAML string"),
            ("jobs: { 'not a job': {} }\n", "may contain only ASCII"),
            ("jobs: { -bad: {} }\n", "must start with an ASCII"),
        ];
        for (source, expected) in cases {
            let error = scan_workflow(path(), source).unwrap_err();
            assert!(error.to_string().contains(expected), "{error:?} did not contain {expected:?}");
        }
    }

    #[test]
    fn parses_multiline_yaml_without_treating_content_as_jobs() {
        let inventory = scan_workflow(
            path(),
            "name: \"\njobs:\n  hidden-in-double-quote:\n\"\nnote: '\njobs:\n  hidden-in-single-quote:\n'\njobs:\n  expected:\n    strategy:\n      matrix:\n        toolchain: [\n          \"stable\",\n\n          # A comment and blank line remain safely nested.\n          \"nightly\",\n        ]\n        target: &targets [\n          \"x86_64-unknown-linux-gnu\",\n        ]\n        include: [\n          { os: \"linux\", target: \"x86_64-unknown-linux-gnu\" },\n        ]\n        tagged: !!str \"first\n          second\"\n    run: |\n      jobs:\n        hidden-in-block-scalar:\n",
        )
        .unwrap();

        assert_eq!(inventory.jobs, [JobId::parse("expected").unwrap()].into_iter().collect());
    }

    #[test]
    fn parses_hashes_inside_quoted_block_scalar_keys() {
        // This exact shape exposed a bug in the former handwritten lexer. The
        // hash belongs to the quoted mapping key, so neither it nor the block
        // scalar's apparent job declaration can change workflow structure.
        let inventory = scan_workflow(
            path(),
            "jobs:\n  expected:\n    strategy:\n      matrix:\n        include:\n          - \"label # one\": |\n              jobs:\n                hidden:\n    runs-on: ubuntu-latest\n",
        )
        .unwrap();

        assert_eq!(inventory.jobs, [JobId::parse("expected").unwrap()].into_iter().collect());
    }

    #[test]
    fn recognizes_comments_after_flow_punctuation() {
        // A comment can begin directly after flow punctuation. The closing
        // brace and apparent `hidden` job are comment/flow-mapping content, not
        // workflow structure. This exact case fooled the former handwritten
        // lexer.
        let inventory = scan_workflow(
            path(),
            "jobs:\n  expected:\n    env: { FOO: bar,# } scanner-only close\n  hidden:\n    fake,\n        }\n    runs-on: ubuntu-latest\n",
        )
        .unwrap();
        assert_eq!(inventory.jobs, [JobId::parse("expected").unwrap()].into_iter().collect());
    }

    #[test]
    fn duplicate_keys_fail_instead_of_selecting_one_mapping() {
        for source in [
            "jobs: { first: {} }\njobs: { hidden: {} }\n",
            "jobs:\n  repeated: {}\n  repeated: {}\n",
            "jobs:\n  repeated: {}\n  'repeated': {}\n",
            "jobs:\n  repeated: {}\n  !!str repeated: {}\n",
            "name: &job repeated\njobs:\n  repeated: {}\n  *job: {}\n",
        ] {
            let error = scan_workflow(path(), source).unwrap_err();
            assert!(
                matches!(error, WorkflowInventoryError::ParseWorkflowYaml { .. }),
                "unexpected error: {error:?}"
            );
            assert!(error.to_string().contains("duplicate entry"), "{error:?}");
        }
    }

    #[test]
    fn aliases_are_resolved_but_merge_keys_fail_closed() {
        let inventory = scan_workflow(
            path(),
            "name: &job_id expected\njobs:\n  *job_id: &shared { runs-on: ubuntu-latest }\n  aliased: *shared\n",
        )
        .unwrap();
        assert_eq!(
            inventory.jobs,
            [JobId::parse("aliased").unwrap(), JobId::parse("expected").unwrap()]
                .into_iter()
                .collect()
        );

        let error = scan_workflow(
            path(),
            "shared: &shared\n  hidden: { runs-on: ubuntu-latest }\njobs:\n  <<: *shared\n",
        )
        .unwrap_err();
        assert!(matches!(error, WorkflowInventoryError::UnsupportedJobId { .. }));

        let error = scan_workflow(path(), "shared: &shared\n  jobs: { hidden: {} }\n<<: *shared\n")
            .unwrap_err();
        assert!(matches!(error, WorkflowInventoryError::MissingJobsKey { .. }));
    }

    #[test]
    fn parser_bounds_recursive_alias_expansion() {
        // Keep a valid `jobs` mapping in the document so this fixture tests
        // the YAML parser's resource bound rather than an inventory-shape
        // diagnostic. `yaml_serde::Value` traverses every value, including
        // unrelated top-level values, before `scan_workflow` inspects `jobs`.
        let error = scan_workflow(
            path(),
            "recursive: &recursive { child: *recursive }\njobs: { expected: {} }\n",
        )
        .unwrap_err();
        assert!(
            matches!(error, WorkflowInventoryError::ParseWorkflowYaml { .. }),
            "unexpected error: {error:?}"
        );
        assert!(error.to_string().contains("recursion limit exceeded"), "{error:?}");
    }

    #[test]
    fn parser_bounds_repeated_alias_expansion() {
        // This is the small deterministic "billion laughs" fixture from
        // yaml_serde's own test suite. Each anchor repeats the prior anchor
        // nine times, which must hit the parser's alias-replay bound before
        // exponentially expanding into memory.
        let error = scan_workflow(
            path(),
            concat!(
                "a: &a ~\n",
                "b: &b [*a,*a,*a,*a,*a,*a,*a,*a,*a]\n",
                "c: &c [*b,*b,*b,*b,*b,*b,*b,*b,*b]\n",
                "d: &d [*c,*c,*c,*c,*c,*c,*c,*c,*c]\n",
                "e: &e [*d,*d,*d,*d,*d,*d,*d,*d,*d]\n",
                "f: &f [*e,*e,*e,*e,*e,*e,*e,*e,*e]\n",
                "g: &g [*f,*f,*f,*f,*f,*f,*f,*f,*f]\n",
                "h: &h [*g,*g,*g,*g,*g,*g,*g,*g,*g]\n",
                "i: &i [*h,*h,*h,*h,*h,*h,*h,*h,*h]\n",
                "jobs: { expected: {} }\n",
            ),
        )
        .unwrap_err();
        assert!(
            matches!(error, WorkflowInventoryError::ParseWorkflowYaml { .. }),
            "unexpected error: {error:?}"
        );
        assert!(error.to_string().contains("repetition limit exceeded"), "{error:?}");
    }

    #[test]
    fn uses_yaml_1_2_boolean_resolution_and_handles_tags_deliberately() {
        let document: yaml_serde::Value =
            yaml_serde::from_str("on: push\ntrue: value\njobs: !!map { expected: !!map {} }\n")
                .unwrap();
        let root = document.as_mapping().unwrap();
        assert!(root.contains_key("on"));
        assert!(root.contains_key(yaml_serde::Value::Bool(true)));

        let inventory =
            scan_workflow(path(), "on: push\njobs: !!map { expected: !!map {} }\n").unwrap();
        assert_eq!(inventory.jobs, [JobId::parse("expected").unwrap()].into_iter().collect());

        // A repository-specific tag on a structural key is not equivalent to
        // the ordinary string key GitHub's workflow schema requires.
        let error = scan_workflow(path(), "!custom jobs: { hidden: {} }\n").unwrap_err();
        assert!(matches!(error, WorkflowInventoryError::MissingJobsKey { .. }));

        let error = scan_workflow(path(), "jobs: !custom { hidden: {} }\n").unwrap_err();
        assert!(matches!(error, WorkflowInventoryError::JobsNotMapping { .. }));

        let error = scan_workflow(path(), "jobs: { !custom hidden: {} }\n").unwrap_err();
        assert!(matches!(error, WorkflowInventoryError::UnsupportedJobId { .. }));
    }

    #[test]
    fn quoted_structural_keys_preserve_canonical_job_values() {
        let inventory =
            scan_workflow(path(), "\"jobs\":\n  'alpha': {}\n  \"beta-2\": {}\n").unwrap();
        assert_eq!(
            inventory.jobs.into_iter().map(|job| job.0).collect::<Vec<_>>(),
            ["alpha", "beta-2"]
        );
    }

    #[test]
    fn current_workflows_exactly_match_the_reviewed_registry() {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let repository_root = manifest.join("../..");
        let registry = repository_root.join(WORKFLOW_REGISTRY_PATH);

        audit_workflows(repository_root, registry).unwrap();
    }

    #[test]
    fn checked_audit_rejects_an_unregistered_live_job() {
        let repository = temporary_directory("audit-test");
        let workflow_directory = repository.join(".github/workflows");
        let registry = repository.join(WORKFLOW_REGISTRY_PATH);
        fs::create_dir_all(&workflow_directory).unwrap();
        fs::create_dir_all(registry.parent().unwrap()).unwrap();
        fs::write(
            workflow_directory.join("test.yml"),
            "name: Test\non:\n  push:\njobs:\n  expected:\n    runs-on: ubuntu-latest\n  surprise:\n    runs-on: ubuntu-latest\n",
        )
        .unwrap();
        fs::write(
            &registry,
            "workflow\tjob\trole\n.github/workflows/test.yml\texpected\tstatic-ci\n",
        )
        .unwrap();

        let error = audit_workflows(&repository, &registry).unwrap_err();
        let WorkflowAuditError::Violations(violations) = &error else {
            panic!("expected workflow violations, got {error:?}");
        };
        assert_eq!(
            violations.as_slice(),
            [WorkflowInventoryViolation::Unreviewed(WorkflowJob {
                workflow: path(),
                job: JobId::parse("surprise").unwrap(),
            })]
        );
        assert!(error.to_string().contains("add a sorted row to `ci/workflow-jobs.tsv`"));

        fs::remove_dir_all(repository).unwrap();
    }

    #[test]
    fn comparison_reports_missing_and_unreviewed_jobs() {
        let registry = ReviewedWorkflowJobs::parse(
            Path::new("registry.tsv"),
            "workflow\tjob\trole\n.github/workflows/test.yml\texpected\tstatic-ci\n",
        )
        .unwrap();
        let actual = [super::WorkflowInventory {
            path: path(),
            jobs: [JobId::parse("unreviewed").unwrap()].into_iter().collect(),
        }];
        assert_eq!(
            compare_with_reviewed(&actual, &registry),
            [
                WorkflowInventoryViolation::Missing(WorkflowJob {
                    workflow: path(),
                    job: JobId::parse("expected").unwrap(),
                }),
                WorkflowInventoryViolation::Unreviewed(WorkflowJob {
                    workflow: path(),
                    job: JobId::parse("unreviewed").unwrap(),
                }),
            ]
        );
    }

    #[test]
    fn registry_rejects_unknown_roles_and_unsorted_rows() {
        let unknown = ReviewedWorkflowJobs::parse(
            Path::new("registry.tsv"),
            "workflow\tjob\trole\n.github/workflows/test.yml\tjob\tunknown\n",
        )
        .unwrap_err();
        assert!(unknown.to_string().contains("unknown role"));

        let unsorted = ReviewedWorkflowJobs::parse(
            Path::new("registry.tsv"),
            "workflow\tjob\trole\n.github/workflows/test.yml\tz\tstatic-ci\n.github/workflows/test.yml\ta\tstatic-ci\n",
        )
        .unwrap_err();
        assert!(unsorted.to_string().contains("not strictly sorted"));
    }

    #[test]
    fn discovery_errors_are_not_empty_inventories() {
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-workflow-inventory-missing-{}", std::process::id()));
        let error = discover_workflows(&temporary).unwrap_err();
        assert!(matches!(error, WorkflowInventoryError::ResolveRepositoryRoot { .. }));
    }

    #[test]
    fn yaml_like_extensions_must_use_the_canonical_lowercase_form() {
        assert!(super::is_workflow_path(Path::new("ci.yml")).unwrap());
        assert!(super::is_workflow_path(Path::new("ci.yaml")).unwrap());
        assert!(super::is_workflow_path(Path::new(".yml")).unwrap());
        assert!(super::is_workflow_path(Path::new(".yaml")).unwrap());
        assert!(!super::is_workflow_path(Path::new("Dockerfile")).unwrap());

        for name in ["ci.YML", ".YML", ".Yaml"] {
            let error = super::is_workflow_path(Path::new(name)).unwrap_err();
            assert!(matches!(error, WorkflowInventoryError::NonCanonicalExtension { .. }));
        }

        let escaped = super::is_workflow_path(Path::new("bad\u{7}.YML")).unwrap_err();
        assert!(escaped.to_string().contains(r"\u{7}"));
        assert!(!escaped.to_string().contains('\u{7}'));
    }

    #[test]
    fn discovery_inventories_extension_only_workflow_names() {
        let repository = temporary_directory("extension-only");
        let workflows = repository.join(".github/workflows");
        fs::create_dir_all(&workflows).unwrap();
        let source = "name: CI\non:\n  push:\njobs:\n  test:\n    runs-on: ubuntu-latest\n";
        fs::write(workflows.join(".yml"), source).unwrap();
        fs::write(workflows.join(".yaml"), source).unwrap();

        let discovered = discover_workflows(&repository).unwrap();
        assert_eq!(
            discovered.iter().map(|workflow| workflow.path.as_str()).collect::<Vec<_>>(),
            [".github/workflows/.yaml", ".github/workflows/.yml"]
        );

        fs::remove_dir_all(repository).unwrap();
    }

    #[test]
    fn discovered_source_does_not_follow_a_replaced_path() {
        let repository = temporary_directory("retained-source");
        let workflows = repository.join(".github/workflows");
        fs::create_dir_all(&workflows).unwrap();
        let path = workflows.join("ci.yml");
        let retained = workflows.join("retained.txt");
        let original = "name: CI\non:\n  push:\njobs:\n  original:\n    runs-on: ubuntu-latest\n";
        let replacement =
            "name: CI\non:\n  push:\njobs:\n  replacement:\n    runs-on: ubuntu-latest\n";
        fs::write(&path, original).unwrap();

        let discovered = read_workflow_sources(&repository).unwrap();
        fs::rename(&path, &retained).unwrap();
        fs::write(&path, replacement).unwrap();

        assert_eq!(discovered.source(".github/workflows/ci.yml"), Some(original));
        assert!(discovered.source(".github/workflows/missing.yml").is_none());
        assert_eq!(
            discovered.inventories[0].jobs,
            [JobId::parse("original").unwrap()].into_iter().collect()
        );

        fs::remove_dir_all(repository).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn workflow_directory_redirects_are_rejected_inside_and_outside_the_repository() {
        use std::os::unix::fs::symlink;

        for target_inside_repository in [false, true] {
            let temporary = temporary_directory("redirect");
            let repository = temporary.join("repository");
            let github = repository.join(".github");
            let target = if target_inside_repository {
                repository.join("redirected-workflows")
            } else {
                temporary.join("outside-workflows")
            };
            fs::create_dir_all(&github).unwrap();
            fs::create_dir_all(&target).unwrap();
            fs::write(
                target.join("ci.yml"),
                "name: CI\non:\n  push:\njobs:\n  test:\n    runs-on: ubuntu-latest\n",
            )
            .unwrap();
            symlink(&target, github.join("workflows")).unwrap();

            let error = discover_workflows(&repository).unwrap_err();
            assert!(matches!(error, WorkflowInventoryError::RedirectedWorkflowDirectory { .. }));

            fs::remove_dir_all(temporary).unwrap();
        }
    }

    #[cfg(unix)]
    #[test]
    fn invalid_workflow_filenames_return_escaped_typed_errors() {
        for file_name in ["bad\\name.yml", "bad\u{7}name.yml"] {
            let repository = temporary_directory("invalid-name");
            let workflows = repository.join(".github/workflows");
            fs::create_dir_all(&workflows).unwrap();
            fs::write(
                workflows.join(file_name),
                "name: CI\non:\n  push:\njobs:\n  test:\n    runs-on: ubuntu-latest\n",
            )
            .unwrap();

            let error = discover_workflows(&repository).unwrap_err();
            let WorkflowInventoryError::InvalidWorkflowPath { path, .. } = &error else {
                panic!("expected an invalid workflow path, got {error:?}");
            };
            assert_eq!(path.file_name().unwrap(), file_name);
            assert!(!error.to_string().contains('\u{7}'));
            if file_name.contains('\u{7}') {
                assert!(error.to_string().contains(r"\u{7}"));
            }

            fs::remove_dir_all(repository).unwrap();
        }
    }

    #[cfg(unix)]
    #[test]
    fn non_utf8_workflow_filenames_also_escape_controls() {
        use std::{ffi::OsString, os::unix::ffi::OsStringExt};

        let repository = temporary_directory("non-utf8-name");
        let workflows = repository.join(".github/workflows");
        fs::create_dir_all(&workflows).unwrap();
        let file_name = OsString::from_vec(b"bad\x07\xff.yml".to_vec());
        fs::write(
            workflows.join(&file_name),
            "name: CI\non:\n  push:\njobs:\n  test:\n    runs-on: ubuntu-latest\n",
        )
        .unwrap();

        let error = discover_workflows(&repository).unwrap_err();
        assert!(matches!(error, WorkflowInventoryError::NonUtf8Path { .. }));
        assert!(error.to_string().contains(r"\u{7}"));
        assert!(!error.to_string().contains('\u{7}'));

        fs::remove_dir_all(repository).unwrap();
    }

    #[test]
    fn candidate_errors_follow_path_order_not_directory_iteration_order() {
        let repository = temporary_directory("ordered-errors");
        let workflows = repository.join(".github/workflows");
        fs::create_dir_all(&workflows).unwrap();
        // Create these in reverse lexical order. `read_dir` does not promise
        // to retain either creation or lexical order.
        fs::write(workflows.join("z.YML"), "").unwrap();
        fs::write(workflows.join("a.YAML"), "").unwrap();

        let error = discover_workflows(&repository).unwrap_err();
        let WorkflowInventoryError::NonCanonicalExtension { path, .. } = error else {
            panic!("expected a noncanonical extension error, got {error:?}");
        };
        assert_eq!(path.file_name().unwrap(), "a.YAML");

        fs::remove_dir_all(repository).unwrap();
    }

    #[test]
    fn source_and_registry_diagnostics_escape_control_characters() {
        let workflow_error = scan_workflow(path(), "jobs:\n  \"bad\\a\": {}\n").unwrap_err();
        assert!(workflow_error.to_string().contains(r"\u{7}"));
        assert!(!workflow_error.to_string().contains('\u{7}'));

        let registry_error = ReviewedWorkflowJobs::parse(
            Path::new("registry.tsv"),
            "workflow\tjob\trole\n.github/workflows/test.yml\tjob\tbad\u{1b}\n",
        )
        .unwrap_err();
        assert!(registry_error.to_string().contains(r"\u{1b}"));
        assert!(!registry_error.to_string().contains('\u{1b}'));
    }
}
