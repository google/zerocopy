// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Passing the layout as an argument keeps the rounding decoder and checked
// sizing arithmetic at runtime, rather than folding a type's constant layout.
#[unsafe(no_mangle)]
fn bench_size_for_metadata_runtime_layout(
    metadata: usize,
    layout: zerocopy::DstLayout,
) -> Option<usize> {
    zerocopy::PointerMetadata::size_for_metadata(metadata, layout)
}
