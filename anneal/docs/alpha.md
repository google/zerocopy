<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# MIR verifier alpha

> [!WARNING]
> **Stage 0 Alpha — Not Yet Audited:** Anneal is an early alpha that can
> increase confidence on small scalar Rust crates, **not** an audited soundness
> guarantee. The verifier (`trusted/audit/`, `trusted/rustc-capture/`,
> `trusted/cargo-anneal/`) and its Receipt v3 TCB audit log have not yet
> completed independent audit, so a passing run does not guarantee that every
> remaining assumption is accounted for. Track maturity across
> [Stage 0 (Alpha usability, `#4095`)](https://github.com/google/zerocopy/issues/4095)
> -> [Stage 1 (Audited trust boundary and TCB accounting, `#4012`)](https://github.com/google/zerocopy/issues/4012)
> -> [Stage 2 (Broad systems coverage and TCB reduction, `#4096`)](https://github.com/google/zerocopy/issues/4096).

The developer alpha checks selected Rust functions or scalar library crates on
x86-64 Linux with glibc, such as Ubuntu 24.04. It compiles a dependency-free
library with the pinned compiler and checks the authored Lean proof against the
captured MIR, the stated specification, and Anneal's safety obligations. A
successful receipt (`"schema_version": 3`) identifies the verified scope,
compilation configuration, input digests, containment backend, and assumptions.

On Linux, `ExecSeal` isolates target Lean preflight, elaboration, and audit by
default inside Tier 1 `linux_bwrap` or Tier 2 `linux_landlock_seccomp`
(recorded in `elaboration_sandbox`, failing closed when unavailable unless
`--allow-unsandboxed-elaboration` is passed; see
[elaborator containment](elaborator-containment-design.md)). Rust compilation
(`rustc`) still runs as the caller, so supply a separate isolated execution
environment when processing untrusted Rust crates or build scripts, on
non-Linux hosts, or with `--allow-unsandboxed-elaboration`.

## Try a proof

From the Zerocopy checkout, build and install the pinned tools with Nix.
Keep the same installation cache for setup and verification.

```sh
cd anneal
mkdir -p target
nix build .#omnibus-archive --max-jobs 1 --cores 2 --out-link target/omnibus-link
export XDG_CACHE_HOME="$(mktemp -d)"
cargo run --locked -p cargo-anneal -- setup --local-archive target/omnibus-link
cargo run --locked -p cargo-anneal -- verify \
  --request trusted/cargo-anneal/tests/fixtures/scalar/request.json
```

The example proves that `zero()` returns zero. To experiment, make a copy of
the fixture directory and change its Rust function to return one. The same
proof then fails. `--artifacts <new-directory>` retains the captured Lean
program, bound claim, and diagnostic evidence for proof development.

In `request.json`, each `source_root` resolves relative to the directory
containing the request file or to an existing out-of-tree directory, and
declared inputs must be clean relative regular-file paths inside their
canonicalized `source_root`. Set `scope` to
`{"kind": "selected_unit", "roots": ["module::function"]}` (`UnitTheorem`,
returning `selected_unit_verified`) or `{"kind": "crate"}` (`CrateTheorem`,
returning `crate_verified`), and list the `specification` and `proof` Lean
modules under `proof.sources`. For a dependency-free, feature-free Cargo
library, `--manifest-path <Cargo.toml> --proof-dir <dir>` (with optional
`--select <path>`) constructs the same request automatically.

## Stage 0 / MIR Profile v1: supported vs. refused

The alpha runs on the x86-64 Linux scalar MIR profile (Profile v1) with
`-Zmir-preserve-ub` enforced during capture (`#4114`). Any construct outside
this profile returns an explicit fail-closed refusal rather than approximating
semantics.

| Category | Supported today (Profile v1) | Refused today (fail-closed) |
| :--- | :--- | :--- |
| **Types** | `bool`, `char`, 8- through 128-bit and pointer-sized integers (`i8`..`i128`, `isize`, `u8`..`u128`, `usize` on 64-bit targets), `()`, `!`, `core::cmp::Ordering`, `(T, bool)` overflowing-arithmetic pairs (via `core::intrinsics::*_with_overflow`), and non-generic inhabited crate-local fieldless enums (without explicit discriminant `AnonConst` items in whole-crate scope). | References and raw pointers (`&T`, `&mut T`, `*const T`, `*mut T`), slices, arrays, structs, unions, enums with payloads, uninhabited zero-variant enums, floats, general tuples, and generic types. |
| **Statements & rvalues** | `Assign` (`Use` on retag-noop scalar types, unary `Not`/`Neg`, binary bitwise/shift/wrapping-arithmetic/`*WithOverflow`/comparison/`Cmp`/unchecked `Div`/`Rem`, `CastKind::IntToInt`, `Discriminant`), `StorageLive`, `StorageDead`, bare unprojected `PlaceMention`, and `Nop`. | Place projections (fields, indexing, dereferencing, projected `PlaceMention`), `Aggregate` rvalues, `PtrMetadata`, pointer/float/`Transmute` casts, and inline assembly. |
| **Terminators & operands** | `Goto`, `SwitchInt`, `Return`, `Unreachable`; `Copy`/`Move` on unprojected locals; already-evaluated integer scalar or `ZeroSized` unit/single-variant-enum constants. | `Call` terminators (including `overflowing_*` methods under `-Copt-level=0`, and `CallSource::Use`), runtime `Assert` terminators (including ordinary Rust `/` and `%`), `Drop`, unwind/abort terminators, and unevaluated constants. |
| **Crate scope & items** | Dependency-free, feature-free library crates (`Scope::Crate` or `Scope::SelectedUnit`); non-generic free and associated functions. | External crate dependencies, Cargo features, generics, closures, `const`/`static`/`trait`/`impl`/`AnonConst` owners in whole-crate scope, global assembly, and proc-macro crates. |

For a realistic scalar example, `ci/verify_starnix_e2e.py` checks Starnix's
`ebpf_core` endianness conversion using symbolic MIR helpers in `Anneal.MirWp`.

### Bundled proof libraries and specification boundaries

- **Proof modules:** May import any of the bundled 3-axiom `Anneal.*` proof
  libraries listed in
  [`theory/bundle-manifest.json`](../theory/bundle-manifest.json) (such as
  `Anneal.MirWp`, `Anneal.LoopInv`, `Anneal.BitVec`, and `Anneal.ClassicalEm`),
  which are compiled and audited on demand when imported. Other experimental
  modules under `theory/Anneal/` that are not in `theory/bundle-manifest.json`
  are not bundled into `cargo-anneal`.
- **Specification modules:** Stay restricted to `Trusted.*`, `Init.*`/`Std.*`,
  and declared `specification` helpers.

Verify the stated compilation configuration in the receipt when comparing a
result with a deployed binary. See the [threat model](../THREAT_MODEL.md) for
the verification assumptions.

## Build-system and toolchain options

Build systems such as Bazel or GN that already resolve crate inputs and Lean
module mappings can invoke `verify rustc` directly instead of writing a
`request.json` file:

```sh
cargo anneal verify rustc /path/to/src/lib.rs \
  --crate-name scalar --edition 2024 \
  --source-file /path/to/src/helper.rs \
  --spec-file Spec=/path/to/spec/Spec.lean \
  --proof-file Proof=/path/to/proof/Proof.lean \
  --spec-decl Spec:Spec.specs --theorem Proof:Proof.verify \
  --select module::function --artifacts /path/to/evidence
```

`verify rustc` dereferences symlinks when staging regular source files so
symlinked runfiles trees work directly, while still rejecting special files and
concurrent source edits. Additional flags support build-system and custom
toolchain integration:

- `--export-lean-lib` (requires `--artifacts <directory>`): atomically stages
  Door-1-verified target `.olean` files inside the private work directory and
  retains them under `<artifacts>/lean-lib/` after target audit passes; omits
  authored `proof` `.olean`s on `proof_failed` (exit `1`), and exports nothing
  on `tool_failed` (exit `2`).
- `--lean-memory-mb <MB>`: sets Lean's `-M<MB>` memory limit (`resolve-imports`
  enforces a `4096` MiB floor).
- `--no-default-features`: building `cargo-anneal` without its default `setup`
  feature omits remote archive download support (`exocrate`); pass explicit
  `--capture`, `--sysroot`, and `--lean` paths when running `verify`.

Each `--allow-*` relaxation flag follows Receipt Schema v3's Uniform
Flag-Driven Taint Law: passing the flag prints a `TAINTED` warning banner on
stderr, adds its sorted entry to `taint_reasons` even on clean runs, and
switches passing status to `tainted_crate_verified` or
`tainted_selected_unit_verified`:

- `--allow-unpinned-lean` (requires explicit `--lean <path>`): adds
  `"unpinned_lean"`, dynamically discovers and hashes the minimal `Init.*` and
  `Std.*` sysroot import closure (recorded in `unpinned_lean` and
  `audit.unpinnedLean`), and marks `correspondence_provenance.applicable` as
  `false`.
- `--allow-unsandboxed-elaboration`: adds `"unsandboxed_elaboration"`, disables
  `ExecSeal` (`"elaboration_sandbox": "none"`), and retains `"hostile Lean
  elaborator effects"` in `deferred`.
- `--allow-sorry-in-proof`: adds `"sorry_in_proof"`, permits `sorry` strictly
  in authored `proof` modules outside Phase 1 (never in `specification`,
  `Model`, `Capture`, or `Expected` modules; `"spec-preflight"` also enforces
  pure declarative syntax on `specification` modules), and records
  `sorry`-using proof declarations in `sorry_declarations`.

## Install a published alpha

Replace `<version>` with the latest published prerelease tag on GitHub Releases
(for example, `0.2.0-alpha.6`; `main` tracks unreleased development versions
whose archive digest is intentionally zeroed until release preparation):

```sh
cargo install --locked cargo-anneal@<version>
cargo anneal setup
cargo anneal verify --request /path/to/scalar/request.json
```

To install the alpha alongside an earlier version of `cargo-anneal`, use
`cargo install --root <directory>` and invoke
`<directory>/bin/cargo-anneal` directly.

## Cut the release

Before the first publication, create the GitHub environment `anneal-release`
with required reviewers and a deployment branch rule allowing only `main`.
In the crates.io settings for `cargo-anneal`, add a
trusted publisher for `google/zerocopy`, workflow `release.yml`, and
environment `anneal-release`.
Verify that the `zerocopy` and `zerocopy-derive` registrations for
`release.yml` explicitly require their `release` environment. These
environment bindings keep credentials scoped to each publication job.
See [crates.io Trusted Publishing](https://crates.io/docs/trusted-publishing).

1. Run **Release** on `main`. Select `anneal`, enter the
   desired alpha version, and keep the target branch set to `main`. The
   workflow prepares that version, builds and hosts its Linux toolchain
   archive, and opens one PR with the version and archive digest.
2. Review the source commit and digest on the toolchain release, then merge
   the PR. A push to `main` that introduces a pinned release starts
   qualification on Ubuntu 24.04. The job checks archive provenance and
   environment protections, then installs the packaged crate and runs the
   scalar checks with the downloaded archive.
3. After qualification succeeds, approve the `anneal-release` deployment to
   publish `cargo-anneal` to crates.io. The workflow then tags the published
   source as `anneal-v<version>` and creates a GitHub prerelease with release
   notes and a link to the toolchain archive.

Rerun preparation to recover the PR for a published archive whose build
inputs still match. Recovery trusts the repository's release writers to
preserve the tag and asset provenance. If qualification or GitHub release
publication fails, rerun the failed jobs on the push that merged the release
PR.
