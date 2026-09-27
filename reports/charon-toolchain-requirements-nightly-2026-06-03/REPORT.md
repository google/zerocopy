# Charon Rust toolchain requirements at Aeneas nightly-2026.06.03

## Summary

The Charon binary bundled by Aeneas `nightly-2026.06.03` is built from
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, and that exact Charon
source pins Rust `nightly-2026-05-31`. The coupling is not merely documentation:
`charon/src/bin/charon/toolchain.rs` embeds `charon/rust-toolchain` into the
wrapper binary with `include_str!`, and `charon-driver` uses unstable
`rustc_private` APIs and dynamically links rustc libraries. Charon therefore has
an exact compiler-toolchain dependency at this revision.

In its ordinary rustup mode, the `charon` wrapper ignores the caller's selected
Rust toolchain and explicitly runs Cargo, rustc, and `charon-driver` through
`rustup run nightly-2026-05-31`. If that toolchain cannot run `rustc --version`,
the wrapper attempts to install the channel and then add the components named in
the embedded file. In its Nix mode, however, Charon sets no version guard: the
environment variable `CHARON_TOOLCHAIN_IS_IN_PATH` makes the wrapper execute the
tools already on `PATH` and trust the caller to provide the matching rustc
libraries.

Current Anneal source at
`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` satisfies that trusted-PATH
contract deliberately. `anneal/flake.nix` packages Rust `nightly-2026-05-31`, and
`Toolchain::command(Tool::Charon)` sets `CHARON_TOOLCHAIN_IS_IN_PATH=1`, prepends
that managed Rust `bin` directory to `PATH`, and points the platform library
search path at the managed Rust libraries before invoking `aeneas/bin/charon`.
Thus the source-defined Anneal path uses the Rust nightly required by Aeneas's
bundled Charon.

The identically dated Charon release label is a separate subject. Charon's own
`nightly-2026.06.03` tag resolves to `0c91ca1a…`, whose
`charon/rust-toolchain` pins `nightly-2026-06-01`, not May 31. This reinforces the
existing corpus finding that Aeneas's Charon pin and Charon's same-date release
tag do not denote the same source or toolchain.

At the Aeneas-pinned revision, `charon toolchain-path` exposes the effective
sysroot, but there is no `toolchain-version` subcommand. The intended channel is
recoverable directly from the pinned source file and is compiled into the
wrapper binary. In trusted-PATH mode Charon does not compare the effective rustc
version against that embedded channel, so a mismatch has no dedicated
source-defined "wrong toolchain" diagnostic. Exact failure behavior for a
mismatched runtime toolchain was not executed on this surface and is deliberately
left unclaimed.

No fresh Charon, rustc, Cargo, rustup, Nix, or dynamic-linker execution was
performed. The conclusions below come from immutable source, existing pinned
corpus identities, and release/dependency state.

## Applicability

The primary runtime subject is Charon
`a535e914f74db4fd9e6be7048f4233270d8945c0`, version `0.1.210`, because Aeneas
`nightly-2026.06.03` pins that commit and its release recipe supplies the Charon
executables Anneal packages. Its `charon/rust-toolchain` file contains:

- channel `nightly-2026-05-31`;
- components `rustc-dev`, `llvm-tools-preview`, `rust-src`, and `miri`;
- a list of supported/preinstalled target triples.

The corresponding Rust compiler revision already identified elsewhere in this
corpus is `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.

The second Charon subject, `0c91ca1a…`, is included only to distinguish Charon's
own `nightly-2026.06.03` tag from Aeneas's pin. Current Anneal locks a Rust
`charon_lib` dependency to that later revision, but live Anneal source does not
use that library. This report does not treat its `nightly-2026-06-01` toolchain as
the runtime requirement of the current Anneal path.

The report describes the wrapper/toolchain behavior encoded by these exact
sources. It does not infer continuity to later Charon revisions, where the CLI
and toolchain machinery have already changed.

## Findings

### Charon's exact Rust nightly is source state, not an ambient project choice

At `a535e914…`, the real toolchain file is `charon/rust-toolchain`; the repository
root `rust-toolchain` entry points to it. The file pins
`nightly-2026-05-31` and names the rustc-internal components needed by the Charon
development/runtime environment.

`charon/src/bin/charon/toolchain.rs` then executes:

`include_str!("../../../rust-toolchain")`

from the `charon/src/bin/charon/` directory, which resolves to
`charon/rust-toolchain`. The parsed channel and component list are therefore
compiled into the `charon` wrapper. Changing a neighboring toolchain file after
the binary is built does not change the embedded selection.

Basis: pinned Charon **source**.

### The driver requires rustc-private implementation interfaces

`charon-driver` enables `#![feature(rustc_private)]` and imports crates such as
`rustc_driver`. Charon's manifest describes that binary as a rustc driver that
dynamically links rust dylibs, including `librustc_driver`, and instructs users to
invoke the `charon` wrapper rather than the driver directly so the wrapper can set
up the correct paths.

The `rustc` default feature also pulls in Charon's rustc-facing trait-elaboration
crate. Charon can build its library with that feature disabled on stable Rust,
but that does not produce the normal rustc-driving executable path.

The exact nightly coupling is therefore structural: Charon is compiled against
unstable compiler-private APIs and libraries, not merely against the stable Rust
language surface.

Basis: pinned Charon **source**, especially `charon/Cargo.toml`,
`charon/src/bin/charon-driver/main.rs`, and rustc-facing driver source.

### Ordinary wrapper execution uses the embedded nightly explicitly

Without `CHARON_TOOLCHAIN_IS_IN_PATH`, `Toolchain::run` constructs commands of the
form:

`rustup run nightly-2026-05-31 <program>`

Both `charon cargo` and `charon rustc` reach their compiler tools through this
mechanism. Cargo mode also sets `RUSTC_WRAPPER` to Charon's driver so the selected
Cargo process invokes `charon-driver` for the target crate.

This means a project's local `rust-toolchain`, a shell's default rustup toolchain,
or an already-selected stable compiler does not silently become Charon's compiler
in the ordinary path. The wrapper names the pinned channel explicitly.

Basis: pinned Charon **source**.

### Missing rustup toolchains are installed best-effort, but the installation check is narrow

Before using rustup, the wrapper asks whether `rustup run <channel> rustc
--version` succeeds. If not, it runs `rustup install <channel>` and then adds each
component listed in the embedded file with `rustup component add --toolchain
<channel> <component>`.

The source itself records a limitation: `is_installed` has a FIXME noting that it
does not check whether the right components are installed. The runtime
`Toolchain` struct also deserializes only `channel` and `components`; it does not
read the `targets` array from the toolchain file, and `install` does not issue
`rustup target add` commands.

Accordingly, the source establishes automatic channel/component installation,
but not complete reconciliation of every toolchain-file requirement. A missing
component or target can still surface later through the invoked tools.

Basis: pinned Charon **source**.

### Nix mode deliberately replaces rustup selection with a trusted environment

When `CHARON_TOOLCHAIN_IS_IN_PATH` is present, `in_toolchain` does not call rustup.
It simply invokes the requested program by name/path. The source comment says
this mode is for the Nix development/build environment, where the correct
compiler is already on `PATH` and the driver is correctly dynamically linked.

Charon's Nix build implements that contract by deriving `rustToolchain` directly
from `./rust-toolchain`. Its wrapped `charon` executable sets
`CHARON_TOOLCHAIN_IS_IN_PATH=1`, prepends that toolchain's binaries to `PATH`, and
adds the toolchain libraries to the dynamic-library search path; macOS also adds
an rpath to `charon-driver`.

This is not a second version-negotiation protocol. It is an escape hatch from
rustup in which environment construction becomes responsible for exact coupling.

Basis: pinned Charon **source**, `flake.nix` and `nix/charon.nix`.

### Current Anneal constructs the same trusted environment with the May 31 nightly

Anneal's current `anneal/flake.nix` sets `rustDate = "2026-05-31"` and builds its
managed Rust sysroot from that nightly. Its installed toolchain archive contains
both that Rust sysroot and the Aeneas release containing Charon.

When Anneal constructs a command for `Tool::Charon`, it:

- invokes `aeneas/bin/charon`;
- clears the inherited environment;
- sets `CHARON_TOOLCHAIN_IS_IN_PATH=1`;
- prepends the managed `rust/bin` directory to `PATH` while retaining host tools
  such as the linker after it;
- points `LD_LIBRARY_PATH` or `DYLD_LIBRARY_PATH` at the managed Rust libraries.

The May 31 date is therefore not an accidental neighbor of the Aeneas release.
It matches the embedded requirement of Aeneas's pinned Charon exactly.

Basis: current Anneal **source** + pinned Charon **source**; the final matching
conclusion is **derived** from the two exact channel strings.

### Charon's same-date release tag requires a different nightly

The existing compatibility report establishes that Charon's own
`nightly-2026.06.03` tag resolves to `0c91ca1a…`, 15 commits after Aeneas's pin.
Its `charon/rust-toolchain` file pins `nightly-2026-06-01` while Aeneas's
`a535e914…` pin uses `nightly-2026-05-31`.

Thus the string `nightly-2026.06.03` cannot be used as a transitive Rust-toolchain
identity across the Aeneas and Charon repositories. A consumer must resolve the
actual Charon commit and inspect that commit's toolchain state.

Basis: exact Charon **source** at both revisions + existing immutable tag/pin
resolution; conclusion **derived**.

### The pinned revision exposes the effective sysroot, not a version command

The CLI at `a535e914…` has `toolchain-path`, which runs the effective `rustc
--print=sysroot` through the same `in_toolchain` selection logic and prints the
resulting sysroot. Its test verifies that the path exists and contains
`bin/rustc`.

That revision has no `toolchain-version` subcommand. The strongest cheap ways to
discover the intended version are therefore to inspect the exact
`charon/rust-toolchain` source (or release source identity) and, for a running
installation, use `toolchain-path` to locate the effective sysroot and inspect
that rustc separately. Later Charon source has added a dedicated version command,
but that later interface must not be back-projected onto this pin.

Basis: pinned Charon **source** + preserved CLI test; later-source comparison is
**source** context only.

### Trusted-PATH mismatch is not explicitly detected at this revision

When `CHARON_TOOLCHAIN_IS_IN_PATH` is set, Charon performs no comparison between
the embedded channel and the `rustc` or rustc libraries supplied by the
environment. The source-defined path therefore has no dedicated mismatch error.

A mismatched environment is still risky because `charon-driver` was compiled
against rustc-private APIs and rustc dynamic libraries. Source inspection alone
does not establish which mismatch fails at dynamic linking, startup, compiler
invocation, or translation, nor whether every nearby mismatch necessarily fails.
Those are empirical questions.

Basis: pinned Charon **source** for the absence of a check and the rustc-private
coupling; exact failure behavior is intentionally **not established**.

### Charon documentation at this pin contains a stale filename

`docs/usage.md` correctly says Charon requires a pinned Rust nightly because it
implements a rustc driver, but links readers to `rust-toolchain.template`. At
`a535e914…`, the operative file is `charon/rust-toolchain` (with the repository
root entry pointing to it), and the wrapper embeds that file directly.

Future agents should therefore prefer the source path used by `include_str!` over
the stale documentation filename when identifying the exact compiler pin.

Basis: pinned Charon **documentation** + **source**.

## Boundaries

- No fresh Charon build, rustup installation, Cargo invocation, rustc invocation,
  Nix build, dynamic-link test, or translation was performed.
- The report establishes Charon's requested/embedded toolchain and the selection
  logic that source implements. It does not prove that every component of a
  release artifact was built reproducibly from those sources.
- The exact runtime behavior of deliberately setting
  `CHARON_TOOLCHAIN_IS_IN_PATH` while supplying a different nightly remains
  unmeasured. Source proves there is no explicit version check; it does not prove
  the first concrete failure mode.
- `rustup install` behavior is characterized only as Charon invokes it. This
  report does not claim rustup will always be able to download an old nightly or
  every named component indefinitely.
- The wrapper does not install the toolchain file's target list in its fallback
  installer. This report does not inventory which translation targets need an
  installed standard library versus `no_std`/custom-sysroot handling.
- Charon's own `nightly-2026.06.03` tag is compared only to prevent identity
  confusion. Its June 1 compiler pin is not current Anneal's runtime compiler
  requirement because the associated `charon_lib` is unused by live Anneal
  source at the examined commit.
- No adjacent-version continuity is inferred for Charon's CLI. In particular,
  the later `toolchain-version` command is not present at `a535e914…`.

## Evidence

**Charon source — Aeneas pin.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `charon/rust-toolchain`: `nightly-2026-05-31`, components, and target list.
- repository-root `rust-toolchain`: navigation entry pointing to the crate-local
  toolchain file used by development tooling.
- `charon/src/bin/charon/toolchain.rs`: compile-time embedding, rustup selection,
  best-effort install, trusted-PATH bypass, driver command, and sysroot query.
- `charon/src/bin/charon/main.rs`: Cargo and direct-rustc invocation through the
  toolchain helper.
- `charon/src/bin/charon/cli.rs`: available subcommands at this pin.
- `charon/Cargo.toml` and `charon/src/bin/charon-driver/main.rs`: rustc-driver,
  dynamic-library, and `rustc_private` requirements.
- `flake.nix` and `nix/charon.nix`: Nix toolchain derivation and environment
  wrapper.
- `charon/tests/cli.rs`: preserved source test for `toolchain-path`.
- `docs/usage.md`: **documentation** of the nightly requirement, including the
  stale `rust-toolchain.template` filename.

**Charon source — same-date Charon tag.**
`AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, the commit named by
Charon's own `nightly-2026.06.03` tag: `charon/rust-toolchain` pins
`nightly-2026-06-01`.

**Aeneas source/release identity.**
`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`: the existing corpus
compatibility report records the exact `charon-pin`, matching locked Charon input,
and release recipe that supplies the `a535e914…` binaries.

**Anneal source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `anneal/flake.nix`: Rust date `2026-05-31`, managed sysroot construction, and
  combined toolchain archive.
- `anneal/src/setup.rs`: `Tool::Charon` path and environment construction with
  `CHARON_TOOLCHAIN_IS_IN_PATH`, `PATH`, and platform library path.

**Rust source identity.** The corpus's pinned Rust/MIR reports identify
`nightly-2026-05-31` as
`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`; that commit identity was
re-read during this observation.

No evidence in this report is fresh **execution**.

## Revalidation

For a later Anneal/Aeneas pin, the cheapest source-only discriminator is:

1. resolve Aeneas's exact Charon commit;
2. read that commit's `charon/rust-toolchain` and the `include_str!` path in
   `charon/src/bin/charon/toolchain.rs`;
3. inspect `in_toolchain` for any new version negotiation or bypass rules;
4. inspect the current Charon CLI for a direct toolchain-version query;
5. compare Anneal's packaged Rust channel and Charon command environment against
   the resolved Charon requirement.

On an execution-capable surface, preserve a two-part mismatch probe. First run the
pinned Charon binary normally with rustup and record `charon toolchain-path`, the
resolved `rustc -Vv`, and a one-function extraction. Then set
`CHARON_TOOLCHAIN_IS_IN_PATH=1` while supplying (a) the matching nightly and (b)
one deliberately adjacent nightly, with the corresponding library search path.
Record startup output, dynamic-linker diagnostics, `rustc -Vv`, Charon exit
status, stderr, and whether LLBC is produced. That experiment would establish the
actual first failure mode for the tested mismatch; it would not justify a general
compatibility range for other rustc revisions.