// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! A narrow, deterministic bridge from a checked CI plan to GitHub Actions.
//!
//! Planning and workflow authority deliberately remain separate. The planner
//! decides which ordinary build and Miri cells belong to an event. This module
//! serializes only those selectors and their documented execution meaning. It
//! cannot choose runner labels, permissions, secrets, environments, actions,
//! or shell commands; those choices remain visible in hand-written workflow
//! YAML.
//!
//! There are two deliberately different JSON forms:
//!
//! - compact matrices contain only the exact selectors accepted by the typed
//!   cell executors and intended for `ci.yml`; and
//! - the pretty artifact records every candidate and its decision for people
//!   diagnosing CI coverage.
//!
//! Both forms use explicit, versioned transport structs below. Do not derive
//! `Serialize` on the planner's core types: adding an internal field must not
//! silently change a workflow input or the review artifact.

use std::{
    fs::{self, File, OpenOptions},
    io::{self, Write},
    path::{Path, PathBuf},
    process,
    sync::atomic::{AtomicU64, Ordering},
};

use serde::Serialize;
use thiserror::Error;

use crate::{
    ci::CiInputs,
    plan::{
        BuildPlanCell, CellDecision, DecisionReason, EventClass, ExecutionMode, FeatureSelection,
        MiriPlanCell, PlanError, PlanExplanation,
    },
};

/// The artifact schema emitted by this version of `zc`.
///
/// Increment this before making an incompatible change to the pretty JSON
/// document. The compact matrix is a separate contract coordinated directly
/// with `.github/workflows/ci.yml`.
pub const PROJECTION_SCHEMA_VERSION: u32 = 1;

/// The fixed output name consumed by the ordinary build job.
///
/// Keep the producer and consumer expressions in the workflow coordinated
/// with this value.
pub const BUILD_MATRIX_OUTPUT: &str = "build_matrix";

/// The fixed output name consumed by the Miri job.
///
/// This has the same producer/consumer contract as
/// [`BUILD_MATRIX_OUTPUT`].
pub const MIRI_MATRIX_OUTPUT: &str = "miri_matrix";

/// The fixed job gate derived from whether the Miri matrix is nonempty.
///
/// The workflow must not independently classify events when deciding whether
/// to run or require Miri.
pub const MIRI_ENABLED_OUTPUT: &str = "miri_enabled";

/// JSON ready for GitHub Actions plus a detailed review artifact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GitHubProjection {
    build_matrix_json: String,
    miri_matrix_json: String,
    miri_enabled: bool,
    artifact: Vec<u8>,
    output_records: Vec<u8>,
    output_utf16_bytes: u64,
}

impl GitHubProjection {
    /// Plans `event` once and projects that explanation into both JSON forms.
    ///
    /// Using one [`PlanExplanation`] is important: the compact selected cells
    /// and the artifact's selected/excluded decisions cannot come from
    /// different evaluations of repository state.
    pub fn create(inputs: &CiInputs, event: &str) -> Result<Self, ProjectionError> {
        let explanation = PlanExplanation::create(inputs, event)?;
        project(
            &explanation,
            inputs.policy().schema_version(),
            inputs.policy().limits().max_matrix_cells(),
            inputs.policy().limits().max_job_output_utf16_bytes(),
        )
    }

    /// Returns the compact ordinary build `include` matrix.
    pub fn build_matrix_json(&self) -> &str {
        &self.build_matrix_json
    }

    /// Returns the compact Miri `include` matrix.
    pub fn miri_matrix_json(&self) -> &str {
        &self.miri_matrix_json
    }

    /// Returns whether the projected Miri matrix contains any selected cells.
    pub fn miri_enabled(&self) -> bool {
        self.miri_enabled
    }

    /// Returns deterministic, pretty JSON suitable for a workflow artifact.
    pub fn artifact_bytes(&self) -> &[u8] {
        &self.artifact
    }

    /// Returns GitHub's UTF-16 size estimate for all output records.
    pub fn output_utf16_bytes(&self) -> u64 {
        self.output_utf16_bytes
    }

    /// Appends the three checked `name=value` records to `GITHUB_OUTPUT`.
    ///
    /// The caller supplies the path rather than this library reading ambient
    /// environment state. Names are fixed constants, the gate is a Rust
    /// boolean, and compact JSON never contains a literal newline, so plan data
    /// cannot inject another output.
    pub fn append_to_github_output(
        &self,
        github_output: impl AsRef<Path>,
    ) -> Result<(), ProjectionWriteError> {
        let path = github_output.as_ref();
        let mut output =
            OpenOptions::new().create(true).append(true).open(path).map_err(|source| {
                ProjectionWriteError::OpenGitHubOutput { path: path.to_path_buf(), source }
            })?;
        output.write_all(&self.output_records).map_err(|source| {
            ProjectionWriteError::AppendGitHubOutput { path: path.to_path_buf(), source }
        })?;
        output.flush().map_err(|source| ProjectionWriteError::AppendGitHubOutput {
            path: path.to_path_buf(),
            source,
        })
    }

    /// Creates the pretty artifact without exposing a partial file.
    ///
    /// `path` must not already exist. A temporary file is written and synced in
    /// the destination directory, then atomically linked at `path`. Refusing to
    /// replace a destination gives the same clear contract on Unix and Windows
    /// and avoids hiding a prior artifact unexpectedly.
    pub fn write_artifact_atomically(
        &self,
        path: impl AsRef<Path>,
    ) -> Result<(), ProjectionWriteError> {
        write_atomically(path.as_ref(), &self.artifact)
    }
}

/// A failure creating deterministic GitHub-facing data.
#[derive(Debug, Error)]
pub enum ProjectionError {
    /// Planning or legacy-parity validation failed.
    #[error(transparent)]
    Plan(#[from] PlanError),
    /// A repository-relative manifest could not be represented exactly in JSON.
    #[error("manifest path `{path}` is not valid UTF-8")]
    NonUtf8Manifest {
        /// The rejected repository-relative path.
        path: PathBuf,
    },
    /// A manifest selector was not a safe repository-relative path.
    #[error("manifest path `{path}` is not a safe repository-relative path")]
    UnsafeManifest {
        /// The rejected path, rendered for an actionable diagnostic.
        path: String,
    },
    /// A configured shard size could not contain even one cell.
    #[error("limits.max_matrix_cells must be at least 1, but is {maximum}")]
    InvalidMatrixLimit {
        /// The rejected maximum.
        maximum: u64,
    },
    /// The configured shard size cannot be represented on this platform.
    #[error(
        "limits.max_matrix_cells ({maximum}) cannot be represented as an in-memory collection size on this platform"
    )]
    MatrixLimitTooLarge {
        /// The rejected maximum.
        maximum: u64,
    },
    /// Today's workflow has only one matrix output for this kind of work.
    #[error(
        "{matrix} has {cells} cells and needs {shards} shards at limits.max_matrix_cells={maximum}; update `.github/workflows/ci.yml` to consume multiple {matrix} shards before increasing this plan"
    )]
    WorkflowNeedsMoreShards {
        /// The human-readable matrix name.
        matrix: &'static str,
        /// The selected cell count.
        cells: usize,
        /// The configured maximum cells per shard.
        maximum: u64,
        /// The number of shards required.
        shards: usize,
    },
    /// An explicit transport struct could not be serialized.
    #[error("failed to serialize {document}: {source}")]
    Serialize {
        /// The compact matrix or artifact being serialized.
        document: &'static str,
        /// The JSON serializer failure.
        #[source]
        source: serde_json::Error,
    },
    /// The exact output records exceeded the configured UTF-16 estimate.
    #[error(
        "GitHub output records require {actual} UTF-16 bytes, above limits.max_job_output_utf16_bytes ({maximum})"
    )]
    JobOutputTooLarge {
        /// The exact estimate for both `name=value` records and newlines.
        actual: u64,
        /// The configured maximum.
        maximum: u64,
    },
}

/// A failure publishing an already checked projection to local files.
#[derive(Debug, Error)]
pub enum ProjectionWriteError {
    /// `GITHUB_OUTPUT` could not be opened for append.
    #[error("failed to open GitHub output file `{path}`: {source}")]
    OpenGitHubOutput {
        /// The supplied output path.
        path: PathBuf,
        /// The file-system failure.
        #[source]
        source: io::Error,
    },
    /// The complete pair of output records could not be appended.
    #[error("failed to append GitHub output file `{path}`: {source}")]
    AppendGitHubOutput {
        /// The supplied output path.
        path: PathBuf,
        /// The file-system failure.
        #[source]
        source: io::Error,
    },
    /// The artifact path has no final file name.
    #[error("artifact path `{path}` has no file name")]
    InvalidArtifactPath {
        /// The rejected destination.
        path: PathBuf,
    },
    /// Refusing to replace a prior artifact preserves fail-closed publication.
    #[error("artifact destination `{path}` already exists; refusing to replace it")]
    ArtifactAlreadyExists {
        /// The occupied destination.
        path: PathBuf,
    },
    /// No collision-free temporary file name could be allocated.
    #[error("failed to allocate a temporary artifact in `{directory}`")]
    TemporaryNameExhausted {
        /// The destination directory.
        directory: PathBuf,
    },
    /// The temporary artifact could not be created.
    #[error("failed to create temporary artifact `{path}`: {source}")]
    CreateTemporaryArtifact {
        /// The attempted temporary path.
        path: PathBuf,
        /// The file-system failure.
        #[source]
        source: io::Error,
    },
    /// The complete artifact could not be written and synced.
    #[error("failed to write temporary artifact `{path}`: {source}")]
    WriteTemporaryArtifact {
        /// The temporary path.
        path: PathBuf,
        /// The file-system failure.
        #[source]
        source: io::Error,
    },
    /// The complete temporary file could not be atomically published.
    #[error("failed to publish artifact `{path}` from `{temporary}`: {source}")]
    PublishArtifact {
        /// The intended destination.
        path: PathBuf,
        /// The complete temporary file.
        temporary: PathBuf,
        /// The file-system failure.
        #[source]
        source: io::Error,
    },
}

#[derive(Serialize)]
struct CompactMatrix<T> {
    include: Vec<T>,
}

// These transport structs deliberately repeat only the selectors accepted by
// `execute-build-cell` and `execute-miri-cell`. The executors load the checked
// repository inputs and resolve feature arguments, target behavior, and Miri
// flags themselves. Putting those derived details in the compact matrix would
// create a second execution contract which could drift from that resolution.
// Keep the handwritten Actions jobs and byte-for-byte compact-schema tests
// below coordinated with any deliberate transport change.
#[derive(Serialize)]
struct CompactBuildCell<'a> {
    #[serde(rename = "crate")]
    package: &'a str,
    toolchain: &'a str,
    feature_profile: &'a str,
    target: &'a str,
}

#[derive(Serialize)]
struct CompactMiriCell<'a> {
    #[serde(rename = "crate")]
    package: &'a str,
    toolchain: &'a str,
    feature_profile: &'a str,
    target: &'a str,
    miri_model: &'a str,
}

#[derive(Serialize)]
struct ArtifactDocument<'a> {
    schema_version: u32,
    policy_schema_version: u32,
    event: &'a str,
    event_class: ArtifactEventClass,
    counts: ArtifactCounts,
    build_cells: Vec<ArtifactBuildCell<'a>>,
    miri_cells: Vec<ArtifactMiriCell<'a>>,
}

#[derive(Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum ArtifactEventClass {
    Reduced,
    Full,
}

#[derive(Serialize)]
struct ArtifactCounts {
    total: DecisionCounts,
    build: DecisionCounts,
    miri: DecisionCounts,
}

#[derive(Clone, Copy, Serialize)]
struct DecisionCounts {
    selected: usize,
    excluded: usize,
}

#[derive(Serialize)]
struct ArtifactBuildCell<'a> {
    package: ArtifactPackage<'a>,
    toolchain: ArtifactToolchain<'a>,
    features: ArtifactFeatures<'a>,
    target: ArtifactBuildTarget<'a>,
    decision: ArtifactDecision,
}

#[derive(Serialize)]
struct ArtifactMiriCell<'a> {
    package: ArtifactPackage<'a>,
    toolchain: ArtifactToolchain<'a>,
    features: ArtifactFeatures<'a>,
    target: ArtifactMiriTarget<'a>,
    model: ArtifactMiriModel<'a>,
    decision: ArtifactDecision,
}

#[derive(Serialize)]
struct ArtifactPackage<'a> {
    id: &'a str,
    manifest: String,
}

#[derive(Serialize)]
struct ArtifactToolchain<'a> {
    id: &'a str,
    version: &'a str,
}

#[derive(Serialize)]
struct ArtifactFeatures<'a> {
    profile: &'a str,
    selection: ArtifactFeatureSelection<'a>,
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum ArtifactFeatureSelection<'a> {
    Default,
    NoDefault,
    StableAggregate { feature: &'a str },
    All,
}

#[derive(Serialize)]
struct ArtifactBuildTarget<'a> {
    triple: &'a str,
    mode: ArtifactExecutionMode,
}

#[derive(Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum ArtifactExecutionMode {
    Native,
    Cross,
    Thumb,
}

#[derive(Serialize)]
struct ArtifactMiriTarget<'a> {
    triple: &'a str,
    execution: ArtifactMiriExecution,
}

#[derive(Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum ArtifactMiriExecution {
    MiriInterpreted,
}

#[derive(Serialize)]
struct ArtifactMiriModel<'a> {
    name: &'a str,
    flags: &'a [String],
}

#[derive(Serialize)]
struct ArtifactDecision {
    selected: bool,
    code: ArtifactDecisionCode,
    reason: String,
}

#[derive(Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum ArtifactDecisionCode {
    FullEventIncludesBuild,
    ReducedEventIncludesEligibleTarget,
    ReducedEventExcludesIneligibleTarget,
    MiriEventCategoryMatches,
    MiriEventCategoryDoesNotMatch,
}

fn project(
    explanation: &PlanExplanation,
    policy_schema_version: u32,
    max_matrix_cells: u64,
    max_job_output_utf16_bytes: u64,
) -> Result<GitHubProjection, ProjectionError> {
    let selected_builds = explanation
        .builds()
        .iter()
        .filter(|cell| cell.decision().is_included())
        .collect::<Vec<_>>();
    let selected_miri =
        explanation.miri().iter().filter(|cell| cell.decision().is_included()).collect::<Vec<_>>();

    // Sharding is deterministic and ready to reuse, but the current workflow
    // exposes one output and one consumer job for each matrix. Fail here until
    // YAML is deliberately extended; returning only the first shard would
    // silently drop coverage.
    let selected_builds =
        one_workflow_shard("ordinary build matrix", &selected_builds, max_matrix_cells)?;
    let selected_miri = one_workflow_shard("Miri matrix", &selected_miri, max_matrix_cells)?;
    let miri_enabled = !selected_miri.is_empty();

    let compact_builds = CompactMatrix {
        include: selected_builds
            .iter()
            .map(|explained| compact_build_cell(explained.cell()))
            .collect(),
    };
    let compact_miri = CompactMatrix {
        include: selected_miri
            .iter()
            .map(|explained| compact_miri_cell(explained.cell()))
            .collect(),
    };
    let build_matrix_json = compact_json("ordinary build matrix", &compact_builds)?;
    let miri_matrix_json = compact_json("Miri matrix", &compact_miri)?;

    let artifact = artifact_document(explanation, policy_schema_version)?;
    let mut artifact = serde_json::to_vec_pretty(&artifact)
        .map_err(|source| ProjectionError::Serialize { document: "CI plan artifact", source })?;
    artifact.push(b'\n');

    let output_records = format!(
        "{BUILD_MATRIX_OUTPUT}={build_matrix_json}\n{MIRI_MATRIX_OUTPUT}={miri_matrix_json}\n{MIRI_ENABLED_OUTPUT}={miri_enabled}\n"
    );
    let output_utf16_bytes = utf16_bytes(&output_records);
    if output_utf16_bytes > max_job_output_utf16_bytes {
        return Err(ProjectionError::JobOutputTooLarge {
            actual: output_utf16_bytes,
            maximum: max_job_output_utf16_bytes,
        });
    }

    Ok(GitHubProjection {
        build_matrix_json,
        miri_matrix_json,
        miri_enabled,
        artifact,
        output_records: output_records.into_bytes(),
        output_utf16_bytes,
    })
}

fn compact_json<T: Serialize>(
    document: &'static str,
    value: &T,
) -> Result<String, ProjectionError> {
    serde_json::to_string(value).map_err(|source| ProjectionError::Serialize { document, source })
}

fn compact_build_cell(cell: &BuildPlanCell) -> CompactBuildCell<'_> {
    CompactBuildCell {
        package: cell.package().id(),
        toolchain: cell.toolchain().id(),
        feature_profile: cell.features().profile(),
        target: cell.target().triple(),
    }
}

fn compact_miri_cell(cell: &MiriPlanCell) -> CompactMiriCell<'_> {
    CompactMiriCell {
        package: cell.package().id(),
        toolchain: cell.toolchain().id(),
        feature_profile: cell.features().profile(),
        target: cell.target().triple(),
        miri_model: cell.model().id(),
    }
}

fn artifact_document<'a>(
    explanation: &'a PlanExplanation,
    policy_schema_version: u32,
) -> Result<ArtifactDocument<'a>, ProjectionError> {
    let build_counts = decision_counts(explanation.builds().iter().map(|cell| cell.decision()));
    let miri_counts = decision_counts(explanation.miri().iter().map(|cell| cell.decision()));
    let counts = ArtifactCounts {
        total: DecisionCounts {
            selected: build_counts.selected + miri_counts.selected,
            excluded: build_counts.excluded + miri_counts.excluded,
        },
        build: build_counts,
        miri: miri_counts,
    };

    let build_cells = explanation
        .builds()
        .iter()
        .map(|explained| {
            let cell = explained.cell();
            Ok(ArtifactBuildCell {
                package: artifact_package(cell.package().id(), cell.package().manifest())?,
                toolchain: ArtifactToolchain {
                    id: cell.toolchain().id(),
                    version: cell.toolchain().version(),
                },
                features: artifact_features(cell.features().profile(), cell.features().selection()),
                target: ArtifactBuildTarget {
                    triple: cell.target().triple(),
                    mode: execution_mode_for_artifact(cell.target().mode()),
                },
                decision: artifact_decision(explained.decision()),
            })
        })
        .collect::<Result<Vec<_>, ProjectionError>>()?;
    let miri_cells = explanation
        .miri()
        .iter()
        .map(|explained| {
            let cell = explained.cell();
            Ok(ArtifactMiriCell {
                package: artifact_package(cell.package().id(), cell.package().manifest())?,
                toolchain: ArtifactToolchain {
                    id: cell.toolchain().id(),
                    version: cell.toolchain().version(),
                },
                features: artifact_features(cell.features().profile(), cell.features().selection()),
                target: ArtifactMiriTarget {
                    triple: cell.target().triple(),
                    // This is intentionally not the ordinary target mode. A
                    // Miri cell always interprets tests, even for a target that
                    // an ordinary build treats as cross-compiled.
                    execution: ArtifactMiriExecution::MiriInterpreted,
                },
                model: ArtifactMiriModel { name: cell.model().id(), flags: cell.model().flags() },
                decision: artifact_decision(explained.decision()),
            })
        })
        .collect::<Result<Vec<_>, ProjectionError>>()?;

    Ok(ArtifactDocument {
        schema_version: PROJECTION_SCHEMA_VERSION,
        policy_schema_version,
        event: explanation.event(),
        event_class: match explanation.class() {
            EventClass::Reduced => ArtifactEventClass::Reduced,
            EventClass::Full => ArtifactEventClass::Full,
        },
        counts,
        build_cells,
        miri_cells,
    })
}

fn artifact_package<'a>(
    id: &'a str,
    manifest: &Path,
) -> Result<ArtifactPackage<'a>, ProjectionError> {
    Ok(ArtifactPackage { id, manifest: slash_normalized_path(manifest)? })
}

fn artifact_features<'a>(
    profile: &'a str,
    selection: &'a FeatureSelection,
) -> ArtifactFeatures<'a> {
    let selection = match selection {
        FeatureSelection::Default => ArtifactFeatureSelection::Default,
        FeatureSelection::NoDefault => ArtifactFeatureSelection::NoDefault,
        FeatureSelection::StableAggregate { feature } => {
            ArtifactFeatureSelection::StableAggregate { feature }
        }
        FeatureSelection::All => ArtifactFeatureSelection::All,
    };
    ArtifactFeatures { profile, selection }
}

fn artifact_decision(decision: CellDecision) -> ArtifactDecision {
    let code = match decision.reason() {
        DecisionReason::FullEventIncludesBuild => ArtifactDecisionCode::FullEventIncludesBuild,
        DecisionReason::ReducedEventIncludesEligibleTarget => {
            ArtifactDecisionCode::ReducedEventIncludesEligibleTarget
        }
        DecisionReason::ReducedEventExcludesIneligibleTarget => {
            ArtifactDecisionCode::ReducedEventExcludesIneligibleTarget
        }
        DecisionReason::MiriEventCategoryMatches => ArtifactDecisionCode::MiriEventCategoryMatches,
        DecisionReason::MiriEventCategoryDoesNotMatch => {
            ArtifactDecisionCode::MiriEventCategoryDoesNotMatch
        }
    };
    ArtifactDecision {
        selected: decision.is_included(),
        code,
        reason: decision.reason().to_string(),
    }
}

fn decision_counts(decisions: impl Iterator<Item = CellDecision>) -> DecisionCounts {
    let mut counts = DecisionCounts { selected: 0, excluded: 0 };
    for decision in decisions {
        if decision.is_included() {
            counts.selected += 1;
        } else {
            counts.excluded += 1;
        }
    }
    counts
}

fn execution_mode_for_artifact(mode: ExecutionMode) -> ArtifactExecutionMode {
    match mode {
        ExecutionMode::Native => ArtifactExecutionMode::Native,
        ExecutionMode::Cross => ArtifactExecutionMode::Cross,
        ExecutionMode::Thumb => ArtifactExecutionMode::Thumb,
    }
}

fn slash_normalized_path(path: &Path) -> Result<String, ProjectionError> {
    let Some(text) = path.to_str() else {
        return Err(ProjectionError::NonUtf8Manifest { path: path.to_path_buf() });
    };
    let normalized = text.replace('\\', "/");
    let unsafe_path = normalized.is_empty()
        || normalized.starts_with('/')
        || normalized
            .split('/')
            .any(|component| component.is_empty() || component == "." || component == "..")
        || normalized.split('/').next().is_some_and(|component| component.contains(':'));
    if unsafe_path {
        return Err(ProjectionError::UnsafeManifest { path: normalized });
    }
    Ok(normalized)
}

fn shard_cells<T>(cells: &[T], maximum: u64) -> Result<Vec<&[T]>, ProjectionError> {
    if maximum == 0 {
        return Err(ProjectionError::InvalidMatrixLimit { maximum });
    }
    let maximum =
        usize::try_from(maximum).map_err(|_| ProjectionError::MatrixLimitTooLarge { maximum })?;
    if cells.is_empty() {
        return Ok(vec![cells]);
    }
    Ok(cells.chunks(maximum).collect())
}

fn one_workflow_shard<'a, T>(
    matrix: &'static str,
    cells: &'a [T],
    maximum: u64,
) -> Result<&'a [T], ProjectionError> {
    let shards = shard_cells(cells, maximum)?;
    if shards.len() != 1 {
        return Err(ProjectionError::WorkflowNeedsMoreShards {
            matrix,
            cells: cells.len(),
            maximum,
            shards: shards.len(),
        });
    }
    Ok(shards[0])
}

fn utf16_bytes(text: &str) -> u64 {
    u64::try_from(text.encode_utf16().count()).unwrap_or(u64::MAX).saturating_mul(2)
}

fn write_atomically(path: &Path, contents: &[u8]) -> Result<(), ProjectionWriteError> {
    if path.file_name().is_none() {
        return Err(ProjectionWriteError::InvalidArtifactPath { path: path.to_path_buf() });
    }
    let directory = path.parent().unwrap_or_else(|| Path::new("."));
    let (temporary, mut file) = create_temporary_artifact(directory)?;
    let mut cleanup = RemoveOnDrop(Some(temporary.clone()));

    file.write_all(contents).and_then(|()| file.sync_all()).map_err(|source| {
        ProjectionWriteError::WriteTemporaryArtifact { path: temporary.clone(), source }
    })?;
    drop(file);
    match fs::hard_link(&temporary, path) {
        Ok(()) => {}
        Err(source) if source.kind() == io::ErrorKind::AlreadyExists => {
            return Err(ProjectionWriteError::ArtifactAlreadyExists { path: path.to_path_buf() });
        }
        Err(source) => {
            return Err(ProjectionWriteError::PublishArtifact {
                path: path.to_path_buf(),
                temporary,
                source,
            });
        }
    }
    // Remove the temporary name, leaving the complete inode reachable only by
    // its requested artifact name. The cleanup guard also does this if removal
    // reports an error, for example because an antivirus briefly holds it on
    // Windows.
    if fs::remove_file(&temporary).is_ok() {
        cleanup.0 = None;
    }
    Ok(())
}

fn create_temporary_artifact(directory: &Path) -> Result<(PathBuf, File), ProjectionWriteError> {
    static NEXT_TEMPORARY: AtomicU64 = AtomicU64::new(0);
    const ATTEMPTS: usize = 1_024;

    for _ in 0..ATTEMPTS {
        let sequence = NEXT_TEMPORARY.fetch_add(1, Ordering::Relaxed);
        let path = directory.join(format!(".zc-ci-plan-{}-{sequence}.tmp", process::id()));
        match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(file) => return Ok((path, file)),
            Err(source) if source.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(source) => {
                return Err(ProjectionWriteError::CreateTemporaryArtifact { path, source });
            }
        }
    }
    Err(ProjectionWriteError::TemporaryNameExhausted { directory: directory.to_path_buf() })
}

struct RemoveOnDrop(Option<PathBuf>);

impl Drop for RemoveOnDrop {
    fn drop(&mut self) {
        if let Some(path) = self.0.take() {
            let _ = fs::remove_file(path);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeSet,
        fs,
        path::{Path, PathBuf},
        process,
        sync::{
            atomic::{AtomicU64, Ordering},
            OnceLock,
        },
    };

    use serde_json::{json, Value};

    use super::{
        one_workflow_shard, project, shard_cells, slash_normalized_path, utf16_bytes,
        CompactBuildCell, CompactMiriCell, GitHubProjection, ProjectionError, ProjectionWriteError,
        BUILD_MATRIX_OUTPUT, MIRI_ENABLED_OUTPUT, MIRI_MATRIX_OUTPUT, PROJECTION_SCHEMA_VERSION,
    };
    use crate::{
        ci::CiInputs,
        plan::{Plan, PlanExplanation},
    };

    fn inputs() -> &'static CiInputs {
        static INPUTS: OnceLock<CiInputs> = OnceLock::new();
        INPUTS.get_or_init(|| {
            let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
            CiInputs::load(root).unwrap()
        })
    }

    fn parse(value: &str) -> Value {
        serde_json::from_str(value).unwrap()
    }

    #[test]
    fn projects_all_current_events() {
        for (event, builds, miri) in [
            ("pull_request", 60, 0),
            ("merge_group", 182, 64),
            ("push", 182, 64),
            ("workflow_dispatch", 182, 64),
        ] {
            let projection = GitHubProjection::create(inputs(), event).unwrap();
            assert_eq!(
                parse(projection.build_matrix_json())["include"].as_array().unwrap().len(),
                builds
            );
            assert_eq!(
                parse(projection.miri_matrix_json())["include"].as_array().unwrap().len(),
                miri
            );
            assert_eq!(projection.miri_enabled(), miri != 0);

            let artifact: Value = serde_json::from_slice(projection.artifact_bytes()).unwrap();
            assert_eq!(artifact["schema_version"], PROJECTION_SCHEMA_VERSION);
            assert_eq!(artifact["policy_schema_version"], inputs().policy().schema_version());
            assert_eq!(artifact["event"], event);
            assert_eq!(artifact["counts"]["build"]["selected"], builds);
            assert_eq!(artifact["counts"]["miri"]["selected"], miri);
        }
    }

    #[test]
    fn compact_projection_selects_exactly_the_plan() {
        for event in ["pull_request", "merge_group", "push", "workflow_dispatch"] {
            let plan = Plan::create(inputs(), event).unwrap();
            let projection = GitHubProjection::create(inputs(), event).unwrap();

            let expected_builds = plan
                .builds()
                .iter()
                .map(|cell| {
                    json!({
                        "crate": cell.package().id(),
                        "toolchain": cell.toolchain().id(),
                        "feature_profile": cell.features().profile(),
                        "target": cell.target().triple(),
                    })
                })
                .collect::<Vec<_>>();
            let expected_miri = plan
                .miri()
                .iter()
                .map(|cell| {
                    json!({
                        "crate": cell.package().id(),
                        "toolchain": cell.toolchain().id(),
                        "feature_profile": cell.features().profile(),
                        "target": cell.target().triple(),
                        "miri_model": cell.model().id(),
                    })
                })
                .collect::<Vec<_>>();

            assert_eq!(
                parse(projection.build_matrix_json())["include"],
                Value::Array(expected_builds)
            );
            assert_eq!(
                parse(projection.miri_matrix_json())["include"],
                Value::Array(expected_miri)
            );
        }
    }

    #[test]
    fn compact_cell_schemas_are_exact_executor_selectors() {
        let build = CompactBuildCell {
            package: "package",
            toolchain: "toolchain",
            feature_profile: "profile",
            target: "target",
        };
        assert_eq!(
            serde_json::to_string(&build).unwrap(),
            r#"{"crate":"package","toolchain":"toolchain","feature_profile":"profile","target":"target"}"#
        );

        let miri = CompactMiriCell {
            package: "package",
            toolchain: "toolchain",
            feature_profile: "profile",
            target: "target",
            miri_model: "model",
        };
        assert_eq!(
            serde_json::to_string(&miri).unwrap(),
            r#"{"crate":"package","toolchain":"toolchain","feature_profile":"profile","target":"target","miri_model":"model"}"#
        );
    }

    #[test]
    fn serialization_is_byte_for_byte_deterministic() {
        let first = GitHubProjection::create(inputs(), "merge_group").unwrap();
        let second = GitHubProjection::create(inputs(), "merge_group").unwrap();

        assert_eq!(first.build_matrix_json(), second.build_matrix_json());
        assert_eq!(first.miri_matrix_json(), second.miri_matrix_json());
        assert_eq!(first.miri_enabled(), second.miri_enabled());
        assert_eq!(first.artifact_bytes(), second.artifact_bytes());
        assert!(first.artifact_bytes().ends_with(b"\n"));
    }

    #[test]
    fn pull_requests_emit_an_empty_miri_include_matrix() {
        let projection = GitHubProjection::create(inputs(), "pull_request").unwrap();

        assert_eq!(projection.miri_matrix_json(), r#"{"include":[]}"#);
        assert!(!projection.miri_enabled());
    }

    #[test]
    fn a_nonempty_miri_matrix_enables_its_consumer() {
        let projection = GitHubProjection::create(inputs(), "merge_group").unwrap();

        assert_ne!(projection.miri_matrix_json(), r#"{"include":[]}"#);
        assert!(projection.miri_enabled());
    }

    #[test]
    fn sharding_has_an_exact_256_cell_boundary() {
        let cells = (0..257).collect::<Vec<_>>();

        assert_eq!(shard_cells(&cells[..256], 256).unwrap().len(), 1);
        let shards = shard_cells(&cells, 256).unwrap();
        assert_eq!(shards.len(), 2);
        assert_eq!(shards[0], &cells[..256]);
        assert_eq!(shards[1], &cells[256..]);
        assert_eq!(shard_cells::<()>(&[], 256).unwrap(), vec![&[][..]]);
    }

    #[test]
    fn a_lower_configured_limit_fails_until_yaml_has_another_shard() {
        let cells = (0..60).collect::<Vec<_>>();
        let error = one_workflow_shard("ordinary build matrix", &cells, 59).unwrap_err();

        assert!(matches!(
            error,
            ProjectionError::WorkflowNeedsMoreShards {
                matrix: "ordinary build matrix",
                cells: 60,
                maximum: 59,
                shards: 2,
            }
        ));
        assert!(error.to_string().contains("update `.github/workflows/ci.yml`"));
    }

    #[test]
    fn output_accounting_uses_utf16_code_units() {
        assert_eq!(utf16_bytes("matrix=é😀\n"), 22);

        let projection = GitHubProjection::create(inputs(), "pull_request").unwrap();
        let records = format!(
            "{BUILD_MATRIX_OUTPUT}={}\n{MIRI_MATRIX_OUTPUT}={}\n{MIRI_ENABLED_OUTPUT}={}\n",
            projection.build_matrix_json(),
            projection.miri_matrix_json(),
            projection.miri_enabled(),
        );
        assert_eq!(projection.output_utf16_bytes(), utf16_bytes(&records));

        // These sizes make growth in the compact workflow contract visible.
        // A deliberate coverage change can update them, but adding derived
        // execution details to every cell should not pass unnoticed.
        assert_eq!(projection.output_utf16_bytes(), 14_832);
        assert_eq!(
            GitHubProjection::create(inputs(), "merge_group").unwrap().output_utf16_bytes(),
            60_834
        );
    }

    #[test]
    fn output_limit_accepts_the_exact_size_and_rejects_one_byte_less() {
        let explanation = PlanExplanation::create(inputs(), "pull_request").unwrap();
        let schema = inputs().policy().schema_version();
        let maximum_cells = inputs().policy().limits().max_matrix_cells();
        let unbounded = project(&explanation, schema, maximum_cells, u64::MAX).unwrap();
        let exact = unbounded.output_utf16_bytes();

        assert!(project(&explanation, schema, maximum_cells, exact).is_ok());
        let error = project(&explanation, schema, maximum_cells, exact - 1).unwrap_err();
        assert!(matches!(
            error,
            ProjectionError::JobOutputTooLarge { actual, maximum }
                if actual == exact && maximum == exact - 1
        ));
    }

    #[test]
    fn manifest_paths_are_slash_normalized_and_repository_relative() {
        assert_eq!(
            slash_normalized_path(Path::new(r"zerocopy\zerocopy-derive\Cargo.toml")).unwrap(),
            "zerocopy/zerocopy-derive/Cargo.toml"
        );
        assert!(matches!(
            slash_normalized_path(Path::new("../Cargo.toml")),
            Err(ProjectionError::UnsafeManifest { .. })
        ));

        let projection = GitHubProjection::create(inputs(), "merge_group").unwrap();
        let artifact: Value = serde_json::from_slice(projection.artifact_bytes()).unwrap();
        for cell in artifact["build_cells"].as_array().unwrap() {
            let manifest = cell["package"]["manifest"].as_str().unwrap();
            assert!(!manifest.contains('\\'));
            assert!(!Path::new(manifest).is_absolute());
        }
    }

    #[test]
    fn artifact_records_semantics_and_has_no_workflow_authority() {
        let projection = GitHubProjection::create(inputs(), "merge_group").unwrap();
        let artifact: Value = serde_json::from_slice(projection.artifact_bytes()).unwrap();

        let nightly_stable = artifact["build_cells"]
            .as_array()
            .unwrap()
            .iter()
            .find(|cell| {
                cell["package"]["id"] == "zerocopy"
                    && cell["toolchain"]["id"] == "nightly"
                    && cell["features"]["profile"] == "stable"
                    && cell["target"]["triple"] == "x86_64-unknown-linux-gnu"
            })
            .unwrap();
        assert_eq!(nightly_stable["toolchain"]["version"], "nightly-2026-01-25");
        assert_eq!(nightly_stable["features"]["selection"]["kind"], "stable_aggregate");
        assert_eq!(nightly_stable["target"]["mode"], "native");
        assert_eq!(nightly_stable["decision"]["code"], "full_event_includes_build");
        assert!(nightly_stable["decision"]["reason"].as_str().unwrap().contains("full events"));

        let tree = artifact["miri_cells"]
            .as_array()
            .unwrap()
            .iter()
            .find(|cell| cell["model"]["name"] == "tree")
            .unwrap();
        assert_eq!(tree["target"]["execution"], "miri_interpreted");
        assert_eq!(tree["model"]["flags"], json!(["-Zmiri-tree-borrows"]));

        let mut keys = BTreeSet::new();
        collect_keys(&artifact, &mut keys);
        collect_keys(&parse(projection.build_matrix_json()), &mut keys);
        collect_keys(&parse(projection.miri_matrix_json()), &mut keys);
        for forbidden in [
            "permissions",
            "secrets",
            "runs-on",
            "runner",
            "environment",
            "uses",
            "action",
            "shell",
        ] {
            assert!(!keys.contains(forbidden), "authority-bearing key `{forbidden}` escaped");
        }
    }

    fn collect_keys(value: &Value, keys: &mut BTreeSet<String>) {
        match value {
            Value::Object(object) => {
                for (key, value) in object {
                    keys.insert(key.clone());
                    collect_keys(value, keys);
                }
            }
            Value::Array(values) => {
                for value in values {
                    collect_keys(value, keys);
                }
            }
            _ => {}
        }
    }

    #[test]
    fn file_helpers_append_checked_records_and_publish_complete_artifacts() {
        let directory = temporary_directory();
        fs::create_dir(&directory).unwrap();
        let github_output = directory.join("github-output");
        fs::write(&github_output, "existing=value\n").unwrap();
        let artifact = directory.join("ci-plan.json");
        let projection = GitHubProjection::create(inputs(), "pull_request").unwrap();

        projection.append_to_github_output(&github_output).unwrap();
        projection.write_artifact_atomically(&artifact).unwrap();

        let prior_artifact = fs::read(&artifact).unwrap();
        let replacement = GitHubProjection::create(inputs(), "merge_group").unwrap();
        let error = replacement.write_artifact_atomically(&artifact).unwrap_err();
        assert!(matches!(
            error,
            ProjectionWriteError::ArtifactAlreadyExists { path } if path == artifact
        ));
        assert_eq!(fs::read(&artifact).unwrap(), prior_artifact);

        let output = fs::read_to_string(github_output).unwrap();
        assert!(output.starts_with("existing=value\n"));
        assert!(
            output.contains(&format!("{BUILD_MATRIX_OUTPUT}={}\n", projection.build_matrix_json()))
        );
        assert!(
            output.contains(&format!("{MIRI_MATRIX_OUTPUT}={}\n", projection.miri_matrix_json()))
        );
        assert!(output.ends_with(&format!("{MIRI_ENABLED_OUTPUT}={}\n", projection.miri_enabled())));
        assert_eq!(fs::read(artifact).unwrap(), projection.artifact_bytes());
        assert_eq!(fs::read_dir(&directory).unwrap().count(), 2);

        fs::remove_dir_all(directory).unwrap();
    }

    fn temporary_directory() -> PathBuf {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir()
            .join(format!("zerocopy-github-projection-test-{}-{sequence}", process::id()))
    }
}
