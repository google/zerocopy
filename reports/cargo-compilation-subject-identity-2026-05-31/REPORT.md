# Cargo compilation-subject identity at the Anneal-era 2026-05-31 toolchain

## Summary

Cargo does not identify a compilation subject by package name, target name, source
file, feature set, target triple, or profile alone. At
`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, Cargo's internal
`Unit` is the object that represents one build unit. Its source documentation says
that a unit has enough information for Cargo to know how to build it, and its
equality/hash identity includes the package, Cargo target, effective profile,
host-versus-target compilation kind, compilation mode, activated features,
per-unit rustc/rustdoc flags, native-link overrides, standard-library status,
dependency identity, and artifact-related state.

This means a Cargo *target* is not a compilation subject. The same library target
can participate in several distinct units in one command: for example, a normal
library build and a `--test` library build have different compilation modes and
can have different effective profiles and dependency/feature contexts. Under
resolver version 2 or 3, the same dependency package can also be compiled more
than once with different features when its normal, build/proc-macro, target, or
development contexts differ.

Cargo's stable `cargo metadata` output is therefore insufficient to identify the
actual compiler units for a particular build. Cargo's own documentation says that
metadata cannot represent the relationship between features of different
dependency kinds once feature resolution depends on the command, selected
packages, and selected targets.

The closest machine-readable representation is the nightly-only
`--unit-graph -Z unstable-options` output. Version 1 of that JSON exposes each
unit's package ID, Cargo target, effective profile, host/target platform,
compilation mode, per-unit features, standard-library marker, dependencies, and
the graph roots selected by the command. Cargo documents each unit in this graph
as corresponding to a compiler execution, with the representation also containing
`run-custom-build` units for build-script execution.

The unit-graph JSON is not a stable or complete serialization of Cargo's internal
`Unit`. It is explicitly unstable, and the serializer omits fields that
participate in internal unit identity, including rustc/rustdoc flags, link
overrides, the dependency hash used to distinguish otherwise-equal units with
different dependencies, and artifact-specific state. Consequently this Cargo
revision exposes no stable canonical external identifier for an exact compilation
subject. An external tool that needs Cargo-equivalent subject identity must
preserve enough context to distinguish the dimensions in the internal `Unit`;
package + target, or even the current unit-graph projection alone, is not the full
internal identity.

No fresh Cargo execution was performed for this report. The conclusions above are
established from the exact Cargo source and its checked-in reference
documentation. A small executable unit-graph matrix is described under
**Revalidation** for confirming observable behavior on a later toolchain.

## Applicability

The Cargo implementation examined is
`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`. The Rust source
tree `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` records that exact
Cargo revision as its `src/tools/cargo` submodule.

This revision is relevant to Anneal's pinned toolchain era. At
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`,
`anneal/flake.nix` sets `rustDate = "2026-05-31"` and constructs the bundled
Rust toolchain from the `cargo`, `rustc`, `rust-std`, `rustc-dev`,
`llvm-tools`, `miri`, and `rust-src` distributions for that date. The
Aeneas-pinned Charon source
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` independently records
`channel = "nightly-2026-05-31"` in `rust-toolchain`.

The report's Cargo-behavior claims apply directly to the exact Cargo source
revision named above. The observation environment did not independently decode
the Rust static-distribution manifest to prove that the `cargo-nightly` archive
downloaded from the 2026-05-31 distribution was built byte-for-byte from
`fbb61be3…`. The Rust source integration and matching date establish the source
revision examined and its relevance; they are not presented as reproducible-build
or binary-provenance evidence.

The term *Cargo target* follows Cargo's manifest model: a package can contain a
library, binaries, examples, integration tests, benchmarks, and a custom build
script. The term *target platform* or *target triple* means the compilation
architecture and is a separate dimension. Cargo's `UnitInner` source explicitly
warns against confusing these two senses of “target.”

The term *compilation subject* in this report means the identity of one Cargo
build unit sufficiently precisely that two builds which Cargo treats as different
units are not accidentally conflated. It does not assert an Anneal-specific
result schema or choose how Anneal should persist such an identity.

## Findings

### Package selection chooses roots, not complete compilation identity

A Cargo command first selects packages. For build-like commands, the selected
manifest is determined by `--manifest-path` or by Cargo's workspace discovery
from the working directory. With no explicit package-selection flags, Cargo uses
the workspace's default members. A virtual workspace with no explicit
`workspace.default-members` defaults to all members; a non-virtual workspace
defaults to its root package. `-p/--package`, `--workspace`, and
`--exclude` alter that root-package set.

The implementation mirrors the documentation. `Packages::Default` maps
`Workspace::default_members()` to package IDs; `Packages::All` selects all
workspace members; `Packages::OptOut` removes explicit package specs/patterns;
and `Packages::Packages` resolves the requested package specs or globs.

A package ID is stronger than a package name. Cargo's metadata format uses
package IDs to distinguish concrete packages and explicitly treats their textual
representation as opaque. Metadata also records each package's absolute
`manifest_path`, its targets, and workspace membership. The package ID is
therefore the appropriate Cargo-level handle for a selected package, while the
manifest path is important provenance for path/workspace packages.

Basis: **documentation** + **source**.

### A Cargo target names a crate source/configuration, not one compiler execution

A package may contain a library, binaries, examples, integration tests,
benchmarks, and a custom build script. The target descriptor includes such
information as target kind, crate types, name, source path, edition, test/doctest
settings, and required features.

For ordinary `cargo build` and `cargo check`, the default root targets are
library and binary targets of the selected packages. Named target flags
(`--lib`, `--bin`, `--example`, `--test`, `--bench`) and plural/all
variants replace the default target filter. A target with unsatisfied
`required-features` may be skipped when it was selected implicitly, whereas a
specifically named target is treated as requiring those features and produces an
error if they are unavailable.

`cargo test` demonstrates why a target cannot identify a compilation subject.
Its default roots include the library as a normal linkable library, the library
again as a unit-test target, binaries as unit tests when enabled, integration-test
targets, examples for compile checking, and library doctests. Cargo's
`UnitGenerator` assigns different `CompileMode` values to these uses. Thus one
manifest target can deliberately correspond to more than one build unit.

Basis: **documentation** (`cargo-targets.md`, `cargo-build.md`,
`cargo-test.md`) + **source** (`compile_filter.rs`, `unit_generator.rs`).

### Command intent determines default root targets and compilation modes

The source-level `UserIntent` affects default target selection:

- `Build` and `Check` select binary and library targets by default.
- `Test` selects targets whose manifest `test` flag is enabled and also
  examples, which are normally compiled to prevent bit-rot.
- `Bench` selects targets whose `bench` flag is enabled.
- `Doc` selects documented targets, with special handling to avoid documenting
  a binary whose crate name duplicates the library.
- doctesting follows a separate mode.

The serialized unit graph distinguishes at least `build`, `check`, `test`,
`doc`, `doctest`, and `run-custom-build` modes. Changing the Cargo command
or target-selection options can therefore change the root units even when the
workspace and manifests are identical.

Basis: **source** + **documentation**.

### Host-versus-target compilation is part of unit identity

`UnitInner.kind` records whether a unit is for the host or a requested target
architecture. This distinction matters under cross compilation because build
scripts and procedural macros execute on the build host even when ordinary code
is being compiled for another target.

Root-unit generation starts from the command's requested compilation kinds.
Without an explicit `--target`, Cargo normally behaves like a host build,
subject to per-package target configuration. With `--target`, ordinary target
units use that requested target, while `kind.for_target(target)` preserves the
host treatment required by host-executed target kinds.

The unit-graph JSON exposes this dimension as `platform`: `null` means host;
otherwise the value is the target triple. The internal field is richer than a
single global command-line target because different units in one graph can be
host and target units.

Basis: **source** + **documentation**.

### The effective profile, not just a profile name, distinguishes units

`UnitInner.profile` is an effective `Profile` value. Cargo's unit-graph
documentation warns that the serialized profile can differ from the literal
profile defined in `Cargo.toml`. Tests are the clearest example: Cargo adjusts
panic behavior for test/benchmark units and their relevant dependencies because
the Rust test harness requires unwinding in the ordinary configuration.

Root-unit generation computes the effective profile from package identity,
whether the package is a workspace member/local package, the use of the unit
(normal/test/compiler), and the compilation kind. Profile overrides can likewise
make dependencies or selected packages use settings that differ from a simple
“dev” or “release” label.

Therefore an identity containing only `profile = dev` or
`profile = release` is insufficient. Cargo's internal unit identity contains the
effective profile value.

Basis: **source** + **documentation**.

### Activated features are per unit, not merely per package graph

`UnitInner.features` is the sorted feature vector enabled for that unit.
`UnitGenerator` queries `ResolvedFeatures::activated_features` for the
package and a `FeaturesFor` context, then includes the resulting vector when it
interns the unit.

Resolver version 2 changes feature unification in ways that directly create
distinct compilation subjects. In particular:

- target-specific dependency features are ignored when their target is not being
  built;
- build dependencies and proc macros do not unify their features with normal
  uses of the same package;
- development-dependency features are not unified into normal builds unless the
  development dependency is actually active, such as for tests/examples.

Resolver version 3, which is the default for edition 2024, retains the resolver-2
feature behavior and changes incompatible-`rust-version` selection policy.

Cargo explicitly documents that `cargo metadata` cannot represent these
per-dependency-kind feature relationships. The enabled features depend on which
command runs and which packages and targets are selected. The unit graph was
introduced in part to expose this information per build unit.

Basis: **documentation** + **source**.

### Cargo's internal `Unit` is the implementation's equivalence class

At the examined revision, `Unit` wraps a reference-counted `UnitInner`.
`UnitInner` derives `Hash`, `PartialEq`, `Eq`, `PartialOrd`, and `Ord`.
Its identity-bearing fields are:

- `pkg`: the concrete package;
- `target`: the specific Cargo target within that package;
- `profile`: effective compilation profile;
- `kind`: host or target compilation kind;
- `mode`: build/check/test/doc/doctest/etc.;
- `features`: sorted activated features;
- `rustflags`: extra rustc flags for the unit;
- `rustdocflags`: extra rustdoc flags for the unit;
- `links_overrides`: build-script/native-link overrides;
- `is_std`: whether this is an unstable build-std unit;
- `dep_hash`: a hash Cargo fills after dependency construction to distinguish
  otherwise identical units which link different dependency units;
- artifact-dependency state, including the artifact feature target;
- the compile-time-dependency filtering state present in this revision.

`UnitInterner` manufactures units and guarantees that each equivalent
`UnitInner` value is produced only once in the interner. This is direct source
evidence that these fields, rather than a package/target tuple, define Cargo's
internal notion of equivalent units.

The `dep_hash` field is especially important. Cargo's comment says it exists
because two units which are otherwise identical may still need to link different
dependencies—for example when normal and build dependency contexts build a
shared dependency with different features. Cargo performs a second pass after
dependency construction to fill this discriminator.

Basis: **source** (`src/cargo/core/compiler/unit.rs`).

### The unit graph is the closest external representation, but is deliberately incomplete

Cargo's unstable `--unit-graph` flag is available to build-like commands and
prints JSON instead of compiling. Cargo documents it as its internal unit graph
and says each unit corresponds to a compiler execution; the representation also
has `run-custom-build` units for executing build scripts.

Version 1 serializes:

- `pkg_id`;
- the Cargo target descriptor;
- the effective profile;
- host/target `platform`;
- compilation `mode`;
- per-unit `features`;
- `is_std`;
- dependency edges, including the dependency unit's index and extern-crate name;
- graph-root indices.

This is materially more precise than `cargo metadata`: it captures command-
specific roots, intra-package units such as tests/build scripts, per-unit feature
sets, host/target distinctions, and effective profiles.

However, `SerializedUnit` is not a serialization of every `UnitInner` field.
The source omits rustflags, rustdocflags, link overrides, `dep_hash`, artifact
flags/targets, and compile-time filtering state. It also deliberately omits the
internal `unit_for` value on dependency edges. The feature itself is listed
under Cargo's unstable features and requires `-Z unstable-options`.

Accordingly:

1. the unit graph is the best machine-readable Cargo-provided description of
   compiler units in this revision;
2. it is not a stable API;
3. it is not a lossless external encoding of Cargo's internal unit identity.

Basis: **documentation** + **source**
(`src/cargo/core/compiler/unit_graph.rs` and
`src/doc/src/reference/unstable.md`).

### A minimum external discriminator follows from the `Unit` fields

For reasoning about whether two Cargo compilation subjects can safely be treated
as the same, the source establishes a lower bound on the distinctions that matter.
An external representation must at least account for the dimensions that Cargo
uses to distinguish units: concrete package, Cargo target, effective profile,
host/target kind, compilation mode, activated features, and dependency context.
If exact compiler semantics matter, per-unit compiler/rustdoc flags and relevant
overrides are also part of Cargo's own unit equality.

This is a **derived** conclusion about the information required to avoid
collapsing Cargo-distinct units. It is not a recommendation for Anneal's result
schema. Anneal may choose a different representation or reconstruct some fields
mechanically, provided it does not mistake Cargo-distinct subjects for one
another when that distinction affects the claim being made.

### Manifest path is selection/provenance, not sufficient unit identity

`--manifest-path` changes the manifest/workspace from which package selection is
resolved. `cargo metadata` records an absolute `manifest_path` for each
package and absolute source paths for targets. These paths are useful for locating
the source that produced a package/target description.

But the path alone cannot identify a compilation subject: the same manifest may
produce many package targets, target platforms, feature sets, profiles, modes,
and dependency graphs. Conversely, registry/Git packages are primarily
distinguished by Cargo package/source identity rather than by whichever local
cache path happens to hold their source.

Basis: **documentation** + **derived** conclusion from the unit model.

## Boundaries

- **No fresh execution was performed.** The report does not claim that a newly
  generated `--unit-graph` transcript was observed on this execution surface.
  The unit-graph schema and selection behavior are established from the exact
  Cargo source and its checked-in documentation.
- **The exact 2026-05-31 distribution archive was not mapped independently to a
  Cargo commit.** Anneal and Charon both pin the date, and the examined Rust
  source revision points to Cargo `fbb61be3…`, but this report does not claim
  reproducible binary provenance from the static Rust archive to that source.
- **This is not the full Cargo unit-graph/rustc-invocation report.** It identifies
  the dimensions defining a compilation unit and the unit-graph projection. It
  does not exhaustively document dependency-unit generation, build-script
  invocation, rustc wrapper environment variables, exact rustc command
  construction, or all host/target dependency edges. Those remain appropriate
  for the separate “Cargo unit graphs and rustc invocations” subject in #3720.
- **Feature resolution is covered only as needed for subject identity.** The
  report establishes that activated features are per-unit and why resolver
  contexts can split units. It does not fully specify Cargo's dependency/feature
  resolution algorithm or provide a procedure for reconstructing the entire
  active build configuration from metadata. The separate #3720 feature-resolution
  subject remains open.
- **Unstable artifact dependencies and build-std are not exhaustively analyzed.**
  Their identity-bearing fields are recorded because they occur in `UnitInner`,
  but their behavior deserves separate treatment if Anneal begins depending on
  them.
- **“Canonical” is implementation-relative here.** The internal `Unit` is
  Cargo's equivalence object at the pinned revision. Cargo does not promise
  `UnitInner` as a stable external API, and the unstable unit-graph schema may
  change with future Cargo revisions.

## Evidence

**Source — Anneal.**
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`,
`anneal/flake.nix`: `rustDate = "2026-05-31"`; `fetchRustToolchain`
downloads and combines the dated `cargo`, `rustc`, `rust-std`,
`rustc-dev`, `llvm-tools`, `miri`, and `rust-src` components.

**Source — Charon toolchain pin.**
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
`rust-toolchain`: `channel = "nightly-2026-05-31"`.

**Source — Rust/Cargo integration.**
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`,
`src/tools/cargo` is the Git submodule
`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`.

**Source — Cargo unit identity.**
`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`,
`src/cargo/core/compiler/unit.rs`, especially `Unit`, `UnitInner`, and
`UnitInterner::intern`. The source comments describe `Unit` as containing all
information needed for Cargo to build a unit and explain `dep_hash`'s role in
distinguishing otherwise-identical units with different dependencies.

**Source — root-unit generation and target selection.**
Same Cargo revision:
`src/cargo/ops/cargo_compile/unit_generator.rs`,
`src/cargo/ops/cargo_compile/compile_filter.rs`, and
`src/cargo/ops/cargo_compile/packages.rs`.

**Source — unit-graph serialization.**
Same Cargo revision:
`src/cargo/core/compiler/unit_graph.rs`. `SerializedUnit` contains
`pkg_id`, target, profile, platform, mode, features, `is_std`, and
dependencies; comparison with `UnitInner` establishes the fields that are not
serialized.

**Documentation — Cargo reference and command documentation at the same source
revision.**
`src/doc/src/reference/unstable.md` (“unit-graph”),
`src/doc/src/reference/cargo-targets.md`,
`src/doc/src/reference/workspaces.md`,
`src/doc/src/reference/features.md`,
`src/doc/src/reference/resolver.md`,
`src/doc/src/reference/profiles.md`,
`src/doc/src/commands/cargo-build.md`,
`src/doc/src/commands/cargo-test.md`, and
`src/doc/src/commands/cargo-metadata.md`.

**Derived.**
Because Cargo's equality/interner distinguish the full `UnitInner` state while
the unstable unit graph emits only a projection, no package/target tuple and no
current stable Cargo metadata record is a complete canonical external
compilation-subject identity at this revision.

## Revalidation

For a later Cargo revision, the cheapest source-level revalidation is:

1. Resolve the Cargo source revision associated with the toolchain under study.
2. Diff `src/cargo/core/compiler/unit.rs` and enumerate the fields participating
   in `UnitInner` equality/hash; inspect the `UnitInterner::intern` call
   signature and any post-construction identity mutation such as `dep_hash`.
3. Diff `src/cargo/core/compiler/unit_graph.rs` and the “unit-graph” section of
   `src/doc/src/reference/unstable.md`; compare the serialized fields against
   internal `UnitInner`.
4. Diff `unit_generator.rs`, `compile_filter.rs`, and `packages.rs` for
   changes to package/target defaults, host/target selection, modes, feature
   contexts, or effective profiles.
5. Recheck resolver-version documentation for new feature-unification contexts.

On a surface capable of executing the pinned toolchain, preserve one compact
discriminating fixture: a workspace containing a library, binary, integration
test, example, build script, and a proc-macro/build dependency used again as a
normal dependency. Give that dependency different feature requests in normal and
build contexts. Record:

- `cargo +<toolchain> build --unit-graph -Z unstable-options`;
- the same command with an explicit `--target`;
- `cargo +<toolchain> test --no-run --unit-graph -Z unstable-options`;
- a feature-selected build;
- a non-default profile build.

Compare root-unit indices and the tuple
`(pkg_id, target, profile, platform, mode, features, dependencies)`. The probe
should demonstrate command-dependent duplicate units and host/target splitting.
It would validate the observable unit-graph projection for that fixture; it would
still not establish that the projection contains every field in Cargo's internal
unit identity.
