<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# lean-miri source provenance

Anneal vendors the Lean implementation and its authenticated pin. The
[source lock](../vendor/lean-miri/upstream/source-lock.json) describes
the reference source snapshot in the pinned upstream lean-miri checkout.
The acquisition scripts, reference source trees, and release archives
live upstream. Zerocopy's proof checks consume the separately pinned
Lean source and module closure.

Use the [pinned upstream directory][upstream] for the Rust, Miri, AES,
and rustc_apfloat coverage roots. The source lock records the archive
URLs and SHA-256 digests in its pins. The [acquisition script][fetch]
matches the lock's acquisition procedure digest. The [rustc file
list][paths] at the pinned commit matches
pins.rustc.extracted_paths_manifest_sha256. Its digest differs from
the value in acquisition.rustc_selected_archive_paths.sha256. Use
the file list at the pinned commit and the Rust pin's digest when
checking the extracted rustc paths.

[upstream]: https://github.com/proofs-rs/lean-miri/tree/c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a/upstream
[fetch]: https://github.com/proofs-rs/lean-miri/blob/c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a/upstream/fetch-sources.sh
[paths]: https://github.com/proofs-rs/lean-miri/blob/c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a/upstream/rustc-selected-files.txt
