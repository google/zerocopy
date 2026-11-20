<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# CLI Reference

`cargo-anneal` can be invoked either as a Cargo subcommand (`cargo anneal ...`)
or directly as `cargo-anneal ...`. Every transcript below is verified against
the current `cargo-anneal` binary in CI.

## Top-level command

```console
{{#include ../../examples/cli/help/transcript.txt}}
```

## `cargo anneal setup`

```console
{{#include ../../examples/cli/setup-help/transcript.txt}}
```

## Argument error diagnostics

Unrecognized subcommands or flags exit with status `2` and print usage guidance
to standard error:

```console
{{#include ../../examples/cli/unknown-command/transcript.txt}}
```
