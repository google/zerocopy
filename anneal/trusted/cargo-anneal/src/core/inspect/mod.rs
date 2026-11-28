// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure, OS-I/O-free Receipt Schema v3 parser, validator, comparator, and
//! sanitized renderer (`cargo_anneal::core::inspect`).

#![forbid(unsafe_code)]

pub mod diff;
pub mod profile;
pub mod render;
pub mod schema;
pub mod strict_json;

pub use diff::{DiffChange, DiffTier, ReceiptDiff, diff_receipts};
pub use profile::{AssuranceProfile, AxiomAxis, ContainmentAxis, ReplayAxis, ScopeAxis, TaintAxis};
pub use render::{
    ColorChoice, InspectFormat, InspectSection, RenderOptions, render_diff, render_inspection,
};
pub use schema::{
    FailureReceipt, HorizonRecord, ImportedSpecModuleRef, InspectParseError, ModelSystemRelation,
    ParsedReceipt, PolicyRequirements, ProvenanceQualifiers, ReceiptEnvelope, ReceiptShardEntry,
    ReceiptShardsManifest, SpecClosureGolden, SpecEntrySummary, SpecEnvelopeSummary, SpecLawHead,
    SpecModuleGolden, SpecUserDecl, SpecWarningEntry, SuccessReceipt, TcbShimEntry,
    VALID_SPEC_USER_DECL_KINDS, parse_and_validate_receipt,
    parse_and_validate_receipt_with_max_bytes,
};
pub use strict_json::{
    DEFAULT_MAX_RECEIPT_JSON_BYTES, MAX_CONFIGURABLE_RECEIPT_JSON_BYTES, MAX_JSON_DEPTH,
    MAX_RECEIPT_JSON_BYTES, StrictJsonDom, validate_max_receipt_json_bytes,
};
