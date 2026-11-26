<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Installing the Toolchain

`cargo anneal setup` installs or reuses the versioned Rust and Lean 4 toolchain
bundle that Anneal uses during verification.

## Inspecting `setup` options

Check the supported options for `cargo anneal setup`:

```console
{{#include ../../examples/cli/setup-help/transcript.txt}}
```

Without `--local-archive`, `cargo anneal setup` reuses an existing cached
installation for the current `cargo-anneal` version or downloads the pinned
remote archive. Pass `--clear-old` in scripts and CI to remove older cached
toolchain directories without interactive prompts.

When testing a locally built toolchain archive—or working before a remote
release archive is published for your revision—pass `--local-archive <path>`
(see
[Developing Anneal](https://github.com/google/zerocopy/blob/main/anneal/docs/README.md)
and
[Alpha Usage](https://github.com/google/zerocopy/blob/main/anneal/docs/alpha.md)
on GitHub for instructions on building the archive with Nix). Builds compiled
with `--no-default-features` omit `setup` and instead accept explicit
`--capture`, `--sysroot`, and `--lean` paths on `cargo anneal verify`.

## Fail-closed archive handling

If a supplied local archive is corrupted or unreadable, `cargo anneal setup`
fails closed with a non-zero exit status rather than leaving a partial
installation:

```console
{{#include ../../examples/cli/setup-invalid-archive/transcript.txt}}
```
