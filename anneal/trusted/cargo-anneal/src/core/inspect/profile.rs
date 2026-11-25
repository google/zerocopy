// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! 6-axis orthogonal assurance profile derived purely from a Receipt Schema v3.

use serde::Serialize;

/// Axis 1: Verification taint state.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TaintAxis {
    /// No relaxation taint flags were recorded on the receipt.
    Untainted,
    /// One or more relaxation taint atoms were recorded.
    Tainted {
        /// Canonical sorted list of taint atoms from `taint_reasons`.
        reasons: Vec<String>,
    },
}

/// Axis 2: Verified subject scope.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ScopeAxis {
    /// Whole-crate scope verification (`scope.kind == "crate"`).
    WholeCrate {
        /// Count of selected bodies covered by the crate theorem.
        selected_bodies: usize,
        /// Total compiler census items recorded during capture.
        census_items: usize,
    },
    /// Scoped verification targeting explicit selected roots (`selected_unit`).
    SelectedUnits {
        /// Number of explicitly selected scope roots.
        roots: usize,
        /// Number of explicit generic instantiations in scope.
        instantiations: usize,
        /// Count of selected bodies within the scope closure.
        selected_bodies: usize,
        /// Total compiler census items recorded during capture.
        census_items: usize,
    },
    /// Verification did not reach a verified receipt state.
    Failed {
        /// Receipt failure status string (`unsupported`, `proof_failed`, etc.).
        status: String,
    },
}

/// Axis 3: Elaboration OS containment mode.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ContainmentAxis {
    /// Lean elaboration executed inside an OS containment backend.
    Sandboxed {
        /// Recorded backend name (`linux_bwrap` or `linux_landlock_seccomp`).
        mode: String,
    },
    /// Lean elaboration executed without OS containment (`none`).
    Unsandboxed,
    /// Containment mode was not reached or not recorded before failure.
    Unknown,
}

/// Axis 4: Kernel replay and audit quorum coverage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ReplayAxis {
    /// Single-kernel Lean replay completed.
    SingleKernel {
        /// Count of replayed declarations checked by the kernel.
        replayed_declarations: u64,
    },
    /// Multi-kernel replay quorum telemetry recorded.
    MultiKernel {
        /// Count of replayed declarations checked by the primary kernel.
        replayed_declarations: u64,
        /// Replay kernels that accepted the exported closure.
        kernels_passed: Vec<String>,
        /// Replay kernels explicitly skipped during audit.
        kernels_skipped: Vec<String>,
    },
    /// Verification failed before kernel replay completed.
    NotReached,
}

/// Axis 5: Reached axiom posture.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AxiomAxis {
    /// Only foundational Lean axioms (`propext`, `Classical.choice`,
    /// `Quot.sound`) were reached.
    StrictFoundation {
        /// Distinct axiom names recorded in `audit.axioms`.
        axioms: Vec<String>,
    },
    /// `sorryAx` or sorry-containing declarations were reached.
    ContainsSorry {
        /// Distinct axiom names recorded in `audit.axioms`.
        axioms: Vec<String>,
        /// Number of sorry declarations recorded.
        sorry_count: usize,
    },
    /// Unexpected non-foundational axioms were recorded in `audit.axioms`.
    Unexpected {
        /// Distinct axiom names recorded in `audit.axioms`.
        axioms: Vec<String>,
    },
    /// Verification failed before axiom extraction completed.
    NotReached,
}

/// Axis 6: Retained artifact verification state.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ArtifactAxis {
    /// Receipt recorded no retained artifact directory (`artifacts == null`).
    Omitted,
    /// Receipt recorded an artifacts path that was not checked locally.
    RetainedPathRecorded {
        /// Recorded `artifacts` path string from the receipt.
        path: String,
    },
    /// Local retained artifact digests matched the receipt under
    /// `--verify-artifacts`.
    VerifiedLocal {
        /// Directory verified locally.
        path: String,
        /// Number of retained regular files hashed and verified.
        checked_files: usize,
    },
}

/// Orthogonal 6-axis assurance profile reported by `cargo anneal inspect`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AssuranceProfile {
    /// Verification taint posture.
    pub taint: TaintAxis,
    /// Subject verification coverage scope.
    pub scope: ScopeAxis,
    /// OS elaborator containment posture.
    pub containment: ContainmentAxis,
    /// Kernel replay coverage posture.
    pub replay: ReplayAxis,
    /// Reached logical axiom posture.
    pub axioms: AxiomAxis,
    /// Retained artifact verification state.
    pub artifacts: ArtifactAxis,
}
