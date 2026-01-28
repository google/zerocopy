// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use snapbox::{Data, data::DataFormat};
use target_spec::errors::CustomTripleCreateError;
use target_spec_miette::IntoMietteDiagnostic;

#[test]
fn unavailable_snapshot() {
    // SAFETY: Tests are run under nextest where it's safe to alter the
    // environment.
    unsafe { std::env::set_var("CLICOLOR_FORCE", "1") };

    // Test that the unavailable diagnostic shows properly as a report.
    let report = miette::Report::new(CustomTripleCreateError::Unavailable.into_diagnostic());
    // Use the Debug format to get the report ace the fancy displayer would show
    // it.
    let actual = format!("{report:?}");

    let b = snapbox::Assert::new().action_env("SNAPSHOTS");

    // Store SVG and ANSI snapshots. Use the binary representation to ensure
    // that no post-processing of text happens.
    b.eq(
        Data::binary(actual.clone()).coerce_to(DataFormat::TermSvg),
        snapbox::file!["snapshots/unavailable.svg"],
    );
    b.eq(
        Data::binary(actual),
        snapbox::file!["snapshots/unavailable.ansi"],
    );
}
