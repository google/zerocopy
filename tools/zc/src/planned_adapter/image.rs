// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exact production audit for the Docker image trusted by typed executors.
//!
//! Matrix consumers already prove which artifact they download and how they
//! invoke the loaded image. That does not establish that `build_docker_env`
//! built the reviewed Dockerfile or uploaded its export. This module closes
//! that upstream boundary: the producer job, its five steps, both mutable local
//! actions, Dockerfile, and build-context ignore file are all exact contracts.
//!
//! This is a repository-source proof, not cryptographic attestation against a
//! hostile checkout or mutable external registry content. A future design can
//! obtain that stronger property by publishing an image from trusted main and
//! consuming it by digest. Until then, failing on any unreviewed producer edit
//! prevents ordinary CI maintenance from silently replacing typed execution
//! with an arbitrary or no-op image.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use super::{
    reviewed_source::ReviewedSource,
    source::{
        audit_exact_job_fields, audit_exact_mapping, audit_exact_scalar_field,
        audit_host_job_contract, audited_steps_block, exact_step_lines, find_job,
        job_field_location, job_fields, MappingExpectation,
    },
    PlannedAdapterAuditError, ViolationSink,
};
use crate::workflow_protocol::{
    image_artifact_producer_expression, IMAGE_ARTIFACT_OUTPUT, IMAGE_JOB, IMAGE_UPLOAD_STEP_ID,
};

const JOB_FIELDS: &[&str] = &["name", "runs-on", "outputs", "permissions", "steps"];
const JOB_NAME: &str = "Build Docker image";

const SETUP_ACTION_PATH: &str = ".github/actions/setup-docker-with-retry/action.yml";
const SETUP_ACTION_SNAPSHOT_PATH: &str = "tools/zc/testdata/setup-docker-with-retry.action.yml";
const SETUP_ACTION_EXPECTED: &str =
    include_str!("../../testdata/setup-docker-with-retry.action.yml");
const UPLOAD_ACTION_PATH: &str = ".github/actions/upload-file-artifact/action.yml";
const UPLOAD_ACTION_SNAPSHOT_PATH: &str = "tools/zc/testdata/upload-file-artifact.action.yml";
const UPLOAD_ACTION_EXPECTED: &str = include_str!("../../testdata/upload-file-artifact.action.yml");
const IMAGE_CONTEXT_PATH: &str = ".github/ci-image";
const DOCKERFILE_PATH: &str = ".github/ci-image/Dockerfile";
const DOCKERFILE_SNAPSHOT_PATH: &str = "tools/zc/testdata/ci-image.Dockerfile";
const DOCKERFILE_EXPECTED: &str = include_str!("../../testdata/ci-image.Dockerfile");
const DOCKERIGNORE_PATH: &str = ".github/ci-image/.dockerignore";
const DOCKERIGNORE_SNAPSHOT_PATH: &str = "tools/zc/testdata/ci-image.dockerignore";
const DOCKERIGNORE_EXPECTED: &str = include_str!("../../testdata/ci-image.dockerignore");
const IMAGE_CONTEXT_ENTRIES: &[&str] = &[".dockerignore", "Dockerfile"];
const TOOLCHAIN_ARGUMENTS: &[(&str, &str)] = &[
    ("msrv", "ZC_MSRV_TOOLCHAIN"),
    ("stable", "ZC_STABLE_TOOLCHAIN"),
    ("nightly", "ZC_NIGHTLY_TOOLCHAIN"),
];

const REVIEWED_SOURCES: &[ReviewedSource] = &[
    ReviewedSource {
        live_path: SETUP_ACTION_PATH,
        snapshot_path: SETUP_ACTION_SNAPSHOT_PATH,
        expected: SETUP_ACTION_EXPECTED,
    },
    ReviewedSource {
        live_path: UPLOAD_ACTION_PATH,
        snapshot_path: UPLOAD_ACTION_SNAPSHOT_PATH,
        expected: UPLOAD_ACTION_EXPECTED,
    },
    ReviewedSource {
        live_path: DOCKERFILE_PATH,
        snapshot_path: DOCKERFILE_SNAPSHOT_PATH,
        expected: DOCKERFILE_EXPECTED,
    },
    ReviewedSource {
        live_path: DOCKERIGNORE_PATH,
        snapshot_path: DOCKERIGNORE_SNAPSHOT_PATH,
        expected: DOCKERIGNORE_EXPECTED,
    },
];

const CHECKOUT_STEP: &[&str] = &[
    "      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1 # v7.0.1",
    "        with:",
    "          persist-credentials: false",
];
const SETUP_STEP: &[&str] = &[
    "      - name: Set up Docker",
    "        uses: ./.github/actions/setup-docker-with-retry",
    "        with:",
    "          registry: ghcr.io",
    "          username: ${{ github.actor }}",
    "          password: ${{ secrets.GITHUB_TOKEN }}",
];
const TAG_STEP: &[&str] = &[
    "      - name: Generate sanitized Docker tag",
    "        id: docker_tag",
    "        env:",
    "          REF_NAME: ${{ github.ref_name }}",
    "        shell: bash",
    "        run: |",
    r#"          echo "tag=${REF_NAME//\//-}" >> "$GITHUB_OUTPUT""#,
];
const BUILD_STEP: &[&str] = &[
    "      - name: Build, cache, and export image",
    "        uses: docker/build-push-action@53b7df96c91f9c12dcc8a07bcb9ccacbed38856a # v7.3.0",
    "        with:",
    "          context: .github/ci-image",
    "          file: .github/ci-image/Dockerfile",
    "          tags: ${{ env.ZC_CI_IMAGE }}",
    "          provenance: false",
    "          outputs: type=docker,dest=${{ runner.temp }}/${{ env.ZC_CI_IMAGE_ARCHIVE }},compression=gzip",
    "          cache-from: |",
    "            type=registry,ref=ghcr.io/google/zerocopy/zerocopy-ci-cache:${{ steps.docker_tag.outputs.tag }}",
    "            type=registry,ref=ghcr.io/google/zerocopy/zerocopy-ci-cache:main",
    "          cache-to: ${{ (github.event_name != 'pull_request' || github.event.pull_request.head.repo.full_name == github.repository) && format('type=registry,ref=ghcr.io/google/zerocopy/zerocopy-ci-cache:{0},mode=max', steps.docker_tag.outputs.tag) || '' }}",
];
fn expected_steps() -> Vec<Vec<String>> {
    let owned = |step: &[&str]| step.iter().map(|line| (*line).to_owned()).collect();
    let upload = vec![
        "      - name: Upload image for matrix jobs".to_owned(),
        format!("        id: {IMAGE_UPLOAD_STEP_ID}"),
        "        uses: ./.github/actions/upload-file-artifact".to_owned(),
        "        with:".to_owned(),
        "          name: ${{ env.ZC_CI_IMAGE_ARCHIVE }}".to_owned(),
        "          path: ${{ runner.temp }}/${{ env.ZC_CI_IMAGE_ARCHIVE }}".to_owned(),
    ];
    vec![owned(CHECKOUT_STEP), owned(SETUP_STEP), owned(TAG_STEP), owned(BUILD_STEP), upload]
}

pub(super) fn reviewed_sources() -> &'static [ReviewedSource] {
    REVIEWED_SOURCES
}

/// Requires the image's cache seeds to follow the validated compiler pins.
///
/// The Dockerfile intentionally contains no `COPY` instruction and executes
/// no checkout code. Its three argument defaults are therefore the complete
/// repository-derived input to toolchain installation. Keeping the defaults
/// here, rather than passing mutable build arguments in the workflow, leaves
/// the exact producer audit in control of which values reach rustup. Comparing
/// them with inventory makes a manifest or policy change fail closed instead
/// of merely turning a preinstalled compiler into a cache miss.
pub(super) fn audit_toolchain_defaults(
    toolchains: &BTreeMap<String, String>,
    errors: &mut ViolationSink,
) {
    for &(toolchain, argument) in TOOLCHAIN_ARGUMENTS {
        let Some(version) = toolchains.get(toolchain) else {
            errors.push(
                format!("{DOCKERFILE_PATH}.ARG.{argument}"),
                format!("image cache requires validated `{toolchain}` toolchain inventory"),
            );
            continue;
        };
        let prefix = format!("ARG {argument}=");
        let declarations = DOCKERFILE_EXPECTED
            .lines()
            .filter(|line| line.starts_with(&prefix))
            .collect::<Vec<_>>();
        let expected = format!("{prefix}{version}");
        if declarations.as_slice() != [expected.as_str()] {
            errors.push(
                format!("{DOCKERFILE_PATH}.ARG.{argument}"),
                format!(
                    "image cache must declare exactly `{expected}` for validated toolchain `{toolchain}`, found {declarations:?}"
                ),
            );
        }
    }
}

pub(super) fn audit(lines: &[&str], errors: &mut ViolationSink) {
    let Some(job) = find_job(lines, IMAGE_JOB, errors) else {
        return;
    };
    let fields = job_fields(lines, job.clone(), IMAGE_JOB, errors);
    audit_exact_job_fields(&fields, IMAGE_JOB, JOB_FIELDS, errors);
    audit_exact_scalar_field(&fields, IMAGE_JOB, "name", JOB_NAME, errors);
    audit_host_job_contract(&fields, IMAGE_JOB, errors);

    let outputs =
        BTreeMap::from([(IMAGE_ARTIFACT_OUTPUT.to_owned(), image_artifact_producer_expression())]);
    audit_exact_mapping(
        lines,
        job.end,
        &fields,
        MappingExpectation { job: IMAGE_JOB, field: "outputs", values: &outputs },
        errors,
    );
    let permissions = BTreeMap::from([
        ("contents".to_owned(), "read".to_owned()),
        ("packages".to_owned(), "write".to_owned()),
    ]);
    audit_exact_mapping(
        lines,
        job.end,
        &fields,
        MappingExpectation { job: IMAGE_JOB, field: "permissions", values: &permissions },
        errors,
    );

    if let Some(steps) = audited_steps_block(&fields, job, IMAGE_JOB, 6, errors) {
        let actual = exact_step_lines(lines, &steps);
        let expected_steps = expected_steps();
        if actual.len() != expected_steps.len() {
            errors.push(
                job_field_location(IMAGE_JOB, "steps"),
                format!(
                    "image producer must contain exactly {} steps, found {}",
                    expected_steps.len(),
                    actual.len()
                ),
            );
        }
        for (index, expected) in expected_steps.iter().enumerate() {
            let matches = actual.get(index).is_some_and(|actual| {
                actual.iter().copied().eq(expected.iter().map(String::as_str))
            });
            if !matches {
                errors.push(
                    job_field_location(IMAGE_JOB, "steps"),
                    format!(
                        "image producer step {} must match the exact canonical contract {:?}",
                        index + 1,
                        expected
                    ),
                );
            }
        }
    }
}

/// Requires the Docker build context to contain only its two reviewed files.
///
/// This is a structural authority boundary rather than a blacklist of current
/// Dockerfile instructions. `COPY`, `ADD`, a BuildKit context bind, or an
/// `ONBUILD` trigger in a future base image cannot reach the repository when
/// no other repository file enters the context. The exact `.dockerignore`
/// independently excludes every path; the directory inventory makes adding a
/// candidate input fail before a coordinated Rust review expands the boundary.
pub(super) fn audit_context_shape(repository_root: &Path) -> Result<(), PlannedAdapterAuditError> {
    let path = repository_root.join(IMAGE_CONTEXT_PATH);
    let metadata = fs::symlink_metadata(&path).map_err(|source| {
        PlannedAdapterAuditError::InspectReviewedSource { path: path.clone(), source }
    })?;
    if !metadata.is_dir() {
        let mut errors = ViolationSink::default();
        errors.push(IMAGE_CONTEXT_PATH, "image context must be one ordinary directory");
        return Err(PlannedAdapterAuditError::Invalid(errors.finish()));
    }

    let entries = fs::read_dir(&path)
        .map_err(|source| PlannedAdapterAuditError::InspectReviewedSource {
            path: path.clone(),
            source,
        })?
        .map(|entry| {
            entry.map(|entry| entry.file_name()).map_err(|source| {
                PlannedAdapterAuditError::InspectReviewedSource { path: path.clone(), source }
            })
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    let expected =
        IMAGE_CONTEXT_ENTRIES.iter().map(|entry| (*entry).into()).collect::<BTreeSet<_>>();
    if entries == expected {
        return Ok(());
    }

    let display = entries.iter().map(|entry| entry.to_string_lossy()).collect::<Vec<_>>();
    let mut errors = ViolationSink::default();
    errors.push(
        IMAGE_CONTEXT_PATH,
        format!("image context must contain exactly {IMAGE_CONTEXT_ENTRIES:?}, found {display:?}"),
    );
    Err(PlannedAdapterAuditError::Invalid(errors.finish()))
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeMap,
        fs,
        path::Path,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::{
        audit, audit_context_shape, audit_toolchain_defaults, reviewed_sources,
        IMAGE_CONTEXT_ENTRIES, IMAGE_CONTEXT_PATH,
    };
    use crate::{
        planned_adapter::{
            reviewed_source::audit_exact_source,
            test_support::{assert_rejected, audit_feature, replace_in_job},
            ViolationSink,
        },
        workflow_protocol::IMAGE_JOB,
    };

    const LIVE_WORKFLOW: &str = include_str!("../../../../.github/workflows/ci.yml");

    fn audit_image(source: &str) -> Result<(), super::super::PlannedAdapterViolations> {
        audit_feature(source, audit)
    }

    fn rejected(label: &str, source: &str, expected: &str) {
        assert_rejected(label, audit_image(source), expected);
    }

    fn replace(from: &str, to: &str) -> String {
        replace_in_job(LIVE_WORKFLOW, IMAGE_JOB, from, to)
    }

    #[test]
    fn accepts_the_live_image_producer() {
        audit_image(LIVE_WORKFLOW).unwrap();
    }

    #[test]
    fn producer_job_shape_outputs_and_permissions_are_exact() {
        for (label, source, expected) in [
            (
                "job name",
                replace("    name: Build Docker image", "    name: Build something else"),
                ".name",
            ),
            (
                "runner",
                replace("    runs-on: ubuntu-latest", "    runs-on: self-hosted"),
                ".runs-on",
            ),
            (
                "condition",
                replace(
                    "    name: Build Docker image\n",
                    "    name: Build Docker image\n    if: always()\n",
                ),
                ".if",
            ),
            (
                "output producer",
                replace(
                    "      image_artifact_id: ${{ steps.upload_image.outputs.artifact-id }}",
                    "      image_artifact_id: ${{ steps.other.outputs.artifact-id }}",
                ),
                ".outputs.image_artifact_id",
            ),
            (
                "extra output",
                replace(
                    "      image_artifact_id: ${{ steps.upload_image.outputs.artifact-id }}",
                    "      image_artifact_id: ${{ steps.upload_image.outputs.artifact-id }}\n      other: value",
                ),
                ".outputs.other",
            ),
            (
                "package permission",
                replace("      packages: write", "      packages: read"),
                ".permissions.packages",
            ),
            (
                "extra permission",
                replace("      contents: read", "      actions: write\n      contents: read"),
                ".permissions.actions",
            ),
        ] {
            rejected(label, &source, expected);
        }
    }

    #[test]
    fn producer_build_export_and_upload_steps_are_exact() {
        let mutations = [
            (
                "checkout pin",
                "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
                "actions/checkout@0000000000000000000000000000000000000000",
            ),
            (
                "setup action",
                "uses: ./.github/actions/setup-docker-with-retry",
                "uses: ./.github/actions/other-setup",
            ),
            ("setup registry", "registry: ghcr.io", "registry: example.invalid"),
            (
                "tag command",
                "echo \"tag=${REF_NAME//\\//-}\" >> \"$GITHUB_OUTPUT\"",
                "echo tag=other >> \"$GITHUB_OUTPUT\"",
            ),
            (
                "builder pin",
                "docker/build-push-action@53b7df96c91f9c12dcc8a07bcb9ccacbed38856a",
                "docker/build-push-action@0000000000000000000000000000000000000000",
            ),
            (
                "build context",
                "context: .github/ci-image",
                "context: unexpected",
            ),
            (
                "Dockerfile",
                "file: .github/ci-image/Dockerfile",
                "file: unexpected.Dockerfile",
            ),
            ("image tag", "tags: ${{ env.ZC_CI_IMAGE }}", "tags: other:latest"),
            ("provenance", "provenance: false", "provenance: true"),
            (
                "export path",
                "outputs: type=docker,dest=${{ runner.temp }}/${{ env.ZC_CI_IMAGE_ARCHIVE }},compression=gzip",
                "outputs: type=docker,dest=/tmp/other.tar",
            ),
            (
                "cache source",
                "type=registry,ref=ghcr.io/google/zerocopy/zerocopy-ci-cache:main",
                "type=local,src=/tmp/cache",
            ),
            (
                "upload action",
                "uses: ./.github/actions/upload-file-artifact",
                "uses: ./.github/actions/other-upload",
            ),
            ("upload ID", "id: upload_image", "id: other"),
            (
                "upload path",
                "path: ${{ runner.temp }}/${{ env.ZC_CI_IMAGE_ARCHIVE }}",
                "path: /tmp/other.tar",
            ),
        ];
        for (label, from, to) in mutations {
            rejected(label, &replace(from, to), ".steps");
        }

        let extra = replace(
            "    steps:\n      - uses: actions/checkout@",
            "    steps:\n      - run: echo unexpected\n      - uses: actions/checkout@",
        );
        rejected("extra step", &extra, "exactly 5 steps");

        // YAML permits this alternate sequence spelling. The shared source
        // scanner must expose it as an item boundary rather than hiding it
        // before the exact producer comparison.
        let bare_item = replace(
            "    steps:\n      - uses: actions/checkout@",
            "    steps:\n      -\n        run: echo unexpected\n      - uses: actions/checkout@",
        );
        rejected("bare sequence item", &bare_item, "exactly 5 steps");

        // This line starts like a YAML comment, but inside `cache-from: |` it
        // is literal action input. The shared scanner must not discard it.
        let scalar_data = replace(
            "            type=registry,ref=ghcr.io/google/zerocopy/zerocopy-ci-cache:main",
            "            type=registry,ref=ghcr.io/google/zerocopy/zerocopy-ci-cache:main\n            # ${{ github.token }}",
        );
        rejected("comment-looking block scalar data", &scalar_data, ".steps");
    }

    #[test]
    fn image_toolchain_defaults_match_validated_inventory() {
        let matching = BTreeMap::from([
            ("msrv".to_owned(), "1.56.0".to_owned()),
            ("stable".to_owned(), "1.93.1".to_owned()),
            ("nightly".to_owned(), "nightly-2026-01-25".to_owned()),
        ]);
        let mut errors = ViolationSink::default();
        audit_toolchain_defaults(&matching, &mut errors);
        assert!(errors.is_empty());

        for (label, inventory, expected) in [
            (
                "changed pin",
                BTreeMap::from([
                    ("msrv".to_owned(), "1.56.0".to_owned()),
                    ("stable".to_owned(), "1.94.0".to_owned()),
                    ("nightly".to_owned(), "nightly-2026-01-25".to_owned()),
                ]),
                "ARG ZC_STABLE_TOOLCHAIN=1.94.0",
            ),
            (
                "missing semantic toolchain",
                BTreeMap::from([
                    ("stable".to_owned(), "1.93.1".to_owned()),
                    ("nightly".to_owned(), "nightly-2026-01-25".to_owned()),
                ]),
                "requires validated `msrv`",
            ),
        ] {
            let mut errors = ViolationSink::default();
            audit_toolchain_defaults(&inventory, &mut errors);
            let error = errors.finish().to_string();
            assert!(error.contains(expected), "{label}: {error}");
        }
    }

    #[test]
    fn every_mutable_producer_source_has_a_complete_compiled_snapshot() {
        for reviewed in reviewed_sources() {
            audit_exact_source(
                reviewed.expected,
                reviewed.live_path,
                reviewed.expected,
                reviewed.snapshot_path,
            )
            .unwrap();

            let changed = format!("{}# changed after review\n", reviewed.expected);
            let error = audit_exact_source(
                &changed,
                reviewed.live_path,
                reviewed.expected,
                reviewed.snapshot_path,
            )
            .unwrap_err()
            .to_string();
            assert!(error.contains(reviewed.live_path), "{error}");
            assert!(error.contains(reviewed.snapshot_path), "{error}");
        }
    }

    #[test]
    fn image_context_contains_only_the_reviewed_inputs() {
        static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let temporary = std::env::temp_dir()
            .join(format!("zerocopy-image-context-{}-{unique}", std::process::id(),));
        fs::create_dir_all(&temporary).unwrap();
        let root = temporary.canonicalize().unwrap();
        let context = root.join(IMAGE_CONTEXT_PATH);
        fs::create_dir_all(&context).unwrap();
        for entry in IMAGE_CONTEXT_ENTRIES {
            fs::write(context.join(entry), "reviewed\n").unwrap();
        }
        audit_context_shape(&root).unwrap();

        let unexpected = context.join("checkout-input");
        fs::write(&unexpected, "unreviewed\n").unwrap();
        let error = audit_context_shape(&root).unwrap_err().to_string();
        assert!(error.contains(IMAGE_CONTEXT_PATH), "{error}");
        assert!(error.contains("checkout-input"), "{error}");
        assert!(error.contains("must contain exactly"), "{error}");

        fs::remove_dir_all(Path::new(&temporary)).unwrap();
    }
}
