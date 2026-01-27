// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::helpers::snapbox_assert_ansi;
use datatest_stable::Utf8Path;
use target_spec_miette::IntoMietteDiagnostic;

pub(crate) fn expr_invalid(path: &Utf8Path, contents: String) -> datatest_stable::Result<()> {
    // SAFETY: Tests run under nextest where it is safe to alter the
    // environment.
    unsafe {
        std::env::set_var("CLICOLOR_FORCE", "1");
    }

    let error = target_spec::TargetSpec::new(contents.trim_end().to_owned())
        .expect_err("expected input to fail");

    let diagnostic = error.into_diagnostic();
    // Use Debug output on the report to get the nicely formatted output.
    let output = format!("{:?}", miette::Report::new_boxed(diagnostic));

    snapbox_assert_ansi("expr-invalid", path, output);
    Ok(())
}
