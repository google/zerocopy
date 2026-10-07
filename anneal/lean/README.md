# Shared Rust models for Lean

This Lake package contains mathematical models used by Anneal and zerocopy's
Aeneas verification. Its modules live in the `Rust` namespace. The package
imports Lean's standard library and has no dependency on a Rust frontend or
Aeneas, so consumers can check the same sources with their own compatible Lean
pins.

- `Rust.Layout` describes alignment, padding, and trailing-slice sizes using
  unbounded natural numbers.
- `Rust.Memory` describes numerical allocation and referent bounds. These
  structures do not themselves establish pointer provenance, ownership, or
  permission to access memory.
- `Rust.Bytes` gives positional little- and big-endian integer encodings,
  including exact-length, bound, truncation, and round-trip theorems.

These are models, not a claim that every Rust operation obeys them. A consumer
must connect an operation's actual extracted implementation to its intended
model through a checked contract. Frontend annotations, machine word carriers,
and external Rust correspondence premises stay in that consumer. This package
introduces no axioms about the Rust compiler or its abstract machine.

## Check the package

From this directory, with the pinned Lean toolchain installed:

```sh
lake build Rust RustTests RustBytesTests
lake env lean -DwarningAsError=true RustTests.lean
```

`RustTests` and `RustBytesTests` check concrete boundary cases and use the
universal theorems independently of any frontend. `RustTests` also audits every
compiled library declaration, including unused helpers, and rejects assumptions
beyond Lean's standard logical axioms. The second command reruns that audit even
when Lake can reuse its compiled test module.

## Distribution and repository use

Anneal's omnibus dependency archive contains the package at `rust-model/`,
including source and precompiled artifacts built with the archive's Lean pin.
`cargo anneal setup` installs that archive through exocrate. Generated Anneal
workspaces require the installed package, rather than copying its definitions
into each frontend. Archive tests import it from a relocated, read-only
installation.

Repository consumers can use a Lake path dependency on `anneal/lean`. A
consumer with a different compatible Lean pin recompiles these sources; it must
not reuse artifacts compiled by another Lean version. The archive's build and
CI cache inputs include this source tree.

Until a new release archive includes this package, unpublished source checkouts
must install a locally built omnibus archive with
`cargo run setup --local-archive /path/to/archive.tar.zst` from `anneal/v1`.
Use a fresh `ANNEAL_TOOLCHAIN_DIR` when replacing a previously installed archive;
setup reuses existing installations even when the local archive changes.
The current remote metadata points to an older archive without `rust-model/`.
For the next release, use the existing manually dispatched Anneal release
workflow: it builds the platform archives and prepares the version/metadata PR
with their actual URLs and hashes before crate publication.
