// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use datatest_stable::Utf8Path;
use snapbox::{Data, data::DataFormat};
use std::path::PathBuf;

pub(crate) fn snapbox_assert_ansi(test_name: &str, path: &Utf8Path, actual_ansi: String) {
    // Currently assuming all files are in a single directory.
    let b = snapbox::Assert::new().action_env("SNAPSHOTS");
    let file_name = path.file_name().unwrap();

    // Store SVG and ANSI snapshots. Use the binary representation to ensure
    // that no post-processing of text happens.
    b.eq(
        Data::binary(actual_ansi.clone()).coerce_to(DataFormat::TermSvg),
        Data::read_from(
            &snapshot_path(test_name, file_name, "svg"),
            Some(DataFormat::TermSvg),
        ),
    );
    b.eq(
        Data::binary(actual_ansi),
        Data::read_from(&snapshot_path(test_name, file_name, "ansi"), None),
    );
}

fn snapshot_path(test_name: &str, file_name: &str, ext: &str) -> PathBuf {
    snapbox::utils::current_dir!()
        .join("snapshots")
        .join(test_name)
        .join(file_name)
        .with_extension(ext)
}
