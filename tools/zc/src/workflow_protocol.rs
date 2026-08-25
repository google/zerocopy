// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Private spellings shared by the typed CI CLI, projection, and workflow audit.
//!
//! This leaf module contains no parsing or policy. Keeping the handwritten
//! workflow protocol here makes a producer, consumer, or CLI rename one atomic
//! Rust change while the planned-job workflow audit checks the literal YAML.

pub(crate) const WORKFLOW_PATH: &str = ".github/workflows/ci.yml";

pub(crate) const PLAN_JOB: &str = "plan_ci";

pub(crate) const PLAN_STEP_NAME: &str = "Validate inputs and project the plan";
pub(crate) const PLAN_STEP_ID: &str = "plan";

pub(crate) const GITHUB_PLAN_COMMAND: &str = "github-plan";
pub(crate) const EXECUTE_BUILD_CELL_COMMAND: &str = "execute-build-cell";
pub(crate) const EXECUTE_MIRI_CELL_COMMAND: &str = "execute-miri-cell";

pub(crate) const CI_EVENT_OPTION: &str = "--event";
pub(crate) const GITHUB_OUTPUT_OPTION: &str = "--github-output";
pub(crate) const PLAN_ARTIFACT_OPTION: &str = "--artifact";
pub(crate) const CELL_PACKAGE_OPTION: &str = "--package";
pub(crate) const CELL_TOOLCHAIN_OPTION: &str = "--toolchain";
pub(crate) const CELL_FEATURE_PROFILE_OPTION: &str = "--feature-profile";
pub(crate) const CELL_TARGET_OPTION: &str = "--target";
pub(crate) const CELL_MIRI_MODEL_OPTION: &str = "--miri-model";

pub(crate) const BUILD_MATRIX_OUTPUT: &str = "build_matrix";
pub(crate) const MIRI_MATRIX_OUTPUT: &str = "miri_matrix";
pub(crate) const MIRI_ENABLED_OUTPUT: &str = "miri_enabled";

pub(crate) const HOST_RUNNER: &str = "ubuntu-latest";
pub(crate) const REPOSITORY_WORKING_DIRECTORY: &str = "zerocopy";
pub(crate) const TRUSTED_SHELL: &str = "/usr/bin/env -u BASH_ENV -u ENV -u SHELLOPTS -u BASHOPTS /bin/bash --noprofile --norc -p -euo pipefail -- {0}";
pub(crate) const PLANNER_PATH: &str = "/home/runner/.cargo/bin:/usr/local/bin:/usr/bin:/bin";
