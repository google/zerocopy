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

## `cargo anneal skill`

`cargo anneal skill` prints the bundled verification skill for the installed
CLI version, and `cargo anneal skill --example` prints a complete working Rust,
request, and Lean 4 starter example:

```console
{{#include ../../examples/cli/skill-help/transcript.txt}}
```

## `cargo anneal verify`

`cargo anneal verify` captures Rust MIR for the configured target and checks an
authored Lean 4 proof against the generated claim. It accepts a JSON request
(`--request`), a dependency-free Cargo library (`--manifest-path` plus
`--proof-dir`), or direct compiler inputs via `verify rustc`.

On Linux, Lean elaboration and auditing run inside an OS sandbox (`ExecSeal`)
by default. Verification writes a JSON Receipt Schema v3 (`schema_version: 3`)
to standard output and exits with:

- `0`: verification succeeded (`selected_unit_verified` or `crate_verified`, or
  a `tainted_*` status when `taint_reasons` is non-empty).
- `1`: proof or profile rejection (`proof_failed` or `unsupported`).
- `2`: compilation, tool, sandbox, setup, artifact, or CLI usage error
  (`compiler_failed`, `tool_failed`, or argument diagnostics on standard error).

Flags that relax verification guarantees (`--allow-unpinned-lean`,
`--allow-unsandboxed-elaboration`, and `--allow-sorry-in-proof`) print
`TAINTED` to standard error and record `"unpinned_lean"`,
`"unsandboxed_elaboration"`, or `"sorry_in_proof"` in `taint_reasons` alongside
`elaboration_sandbox`.

```console
{{#include ../../examples/cli/verify-help/transcript.txt}}
```

## `cargo anneal verify rustc`

Build systems that resolve crate sources and Lean module mappings directly (for
example, Bazel or GN) can invoke `cargo anneal verify rustc` without writing an
intermediate `request.json`:

```console
{{#include ../../examples/cli/verify-rustc-help/transcript.txt}}
```

## Argument error diagnostics

Unrecognized subcommands or flags exit with status `2` and print usage guidance
to standard error:

```console
{{#include ../../examples/cli/unknown-command/transcript.txt}}
```
