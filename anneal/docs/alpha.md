<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# MIR verifier alpha

> [!WARNING]
> **This is alpha software!** Anneal (`0.2.0-alpha`, Stage 0) is an
> experimental verifier under active development and has **not** yet completed
> an independent audit of its Trusted Computing Base (TCB). Today it verifies
> only a small, pointer-free scalar subset of Rust without returning calls
> (`x86_64-unknown-linux-gnu` Profile v1) across selected functions or
> monomorphizations (`UnitTheorem`) or single library or binary crates with no
> required normal or build dependencies (`CrateTheorem`). Passing results depend
> on an intact build host (`rustc`—and any `build.rs` or proc-macro run to
> produce inputs—executes outside the Lean sandbox) as well as human review of
> stated specifications (the declared primary specification module, every
> `specification`-role module, and their transitive meaning dependencies),
> compilation and scope configuration (`request.json` or `verify rustc`
> flags), and TCB audit logs (complete review-surface reporting remains under
> active development). Do not rely on alpha runs as a production security or
> soundness guarantee, and expect frequent breaking changes. Track maturity
> across
> [Stage 0 (`#4095`)](https://github.com/google/zerocopy/issues/4095) ->
> [Stage 1 (`#4012`)](https://github.com/google/zerocopy/issues/4012) ->
> [Stage 2 (`#4096`)](https://github.com/google/zerocopy/issues/4096).

The developer alpha checks selected Rust functions or scalar crates on x86-64
Linux with glibc, such as Ubuntu 24.04. It compiles a library or single binary
target with no required normal or build dependencies (dev-dependencies and
inactive optional dependencies are ignored) using the pinned compiler and
checks the authored Lean proof against the captured MIR, the stated
specification, and Anneal's safety obligations. A successful receipt
(`"schema_version": 3`) identifies the verified scope, compilation
configuration, input digests, containment backend, and assumptions.

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
  --request trusted/cargo-anneal/assets/scalar/request.json
```

The example proves that `zero()` returns zero (`cargo anneal init
--standalone --proof-dir <new-directory>` scaffolds the same four starter
files outside the repository). To experiment, make a copy of the fixture
directory and change its Rust function to return one. The same proof then fails
(`"status": "proof_failed"`, exit code `1`). `--artifacts <new-directory>`
retains the captured Lean program, bound claim, and diagnostic evidence for
proof development; `verify` rejects a path that already exists, or whose parent
is not an existing directory, before it starts any verification work.

In `request.json`, each `source_root` resolves relative to the directory
containing the request file or to an existing out-of-tree directory, and
declared inputs must be clean relative regular-file paths inside their
canonicalized `source_root`. Set `scope` to
`{"kind": "selected_unit", "roots": ["module::function"]}` (with optional
`"instantiations": [{"path": "module::generic", "args": ["usize"]}]` for
explicit concrete monomorphizations; `UnitTheorem`, returning
`selected_unit_verified`) or `{"kind": "crate"}` (`CrateTheorem`, returning
`crate_verified`), and list the `specification` and `proof` Lean modules under
`proof.sources`. For a Cargo crate with a single library or binary target and
no required normal or build dependencies (dev-dependencies and inactive
optional dependencies are ignored), `--manifest-path <Cargo.toml>
--proof-dir <dir>` (with optional `--no-default-features`, `--features <list>`,
`--all-features`, `--panic unwind|abort`, `--select <path>`, and
`--instantiate <JSON>`) constructs the same request automatically.

## Stage 0 / MIR Profile v1: supported vs. refused

The alpha runs on the x86-64 Linux scalar MIR profile (Profile v1) with
`-Zmir-preserve-ub` enforced during capture (`#4114`). Any construct outside
this profile returns an explicit fail-closed refusal rather than approximating
semantics, unless it belongs to the experimental
[Profile v2](#experimental-mir-profile-v2-borrowed-slices-and-raw-pointers).

| Category | Supported today (Profile v1) | Refused today (fail-closed) |
| :--- | :--- | :--- |
| **Types** | `bool`, `char`, 8- through 128-bit and pointer-sized integers (`i8`..`i128`, `isize`, `u8`..`u128`, `usize` on 64-bit targets), `()`, `!`, `core::cmp::Ordering`, `(T, bool)` overflowing-arithmetic pairs (via `core::intrinsics::*_with_overflow`), and non-generic inhabited crate-local fieldless enums (including pure scalar explicit discriminants). | References and raw pointers (`&T`, `&mut T`, `*const T`, `*mut T`), slices, arrays, structs, unions, enums with payloads, uninhabited zero-variant enums, enums whose size or alignment differs from their tag's (such as `#[repr(u8, align(4))]` or `#[repr(align(8))]`), floats, general tuples, and generic types. |
| **Statements & rvalues** | `Assign` (`Use` on retag-noop scalar types, unary `Not`/`Neg`, binary bitwise/shift/wrapping-arithmetic/`*WithOverflow`/comparison/`Cmp`/unchecked `Div`/`Rem`, `CastKind::IntToInt`, `Discriminant`), `StorageLive`, `StorageDead`, bare unprojected `PlaceMention`, and `Nop`. | Place projections (fields, indexing, dereferencing, projected `PlaceMention`), `Aggregate` rvalues, `PtrMetadata`, pointer/float/`Transmute` casts, and inline assembly. |
| **Terminators & operands** | `Goto`, `SwitchInt`, `Return`, `Unreachable`, and diverging calls (`TerminatorKind::Call` with `target: None` and non-`Use` `CallSource`, lowered to fail-closed `unsupported` when reachable); `Copy`/`Move` on unprojected locals; scalar constants (including `Const::Unevaluated`, `Const::Ty(Value)`, and read-only provenance-free `.rodata` `ConstValue::Indirect` / `GlobalAlloc::Memory` scalars evaluated via CTFE alongside `required_consts`) and `ZeroSized` unit/single-variant-enum constants. | Returning `Call` terminators (`target: Some(_)`, including `overflowing_*` methods under `-Copt-level=0`) and `CallSource::Use`, runtime `Assert` terminators (including ordinary Rust `/` and `%`), `Drop`, unwind/abort terminators, and constants whose CTFE evaluation fails or refers to `static`, mutable, or provenance-bearing memory. |
| **Crate scope & items** | Single `lib` or `bin` crates with no required normal or build dependencies (dev-dependencies and inactive optional dependencies are ignored; `Scope::Crate` or `Scope::SelectedUnit`, Cargo `[features]` via `--features`/`--all-features`/`--no-default-features`, configurable `--panic unwind|abort`, and crate-local `#[panic_handler]` in `bin` selected-unit scope), plus opt-in `--stdlib-crate core` (requires `Scope::SelectedUnit`, a `lib` crate, `crate_name == "core"`, a compilation that loads no other crate, no `cfg(miri)`, and any crate-local `Ordering` language item to have the modeled shape; admits `core`'s own `#[lang]` items and skips object emission); non-generic free and associated functions (and, in `Scope::Crate`, safe `trait` declarations, safe `impl` blocks, bodyless safe Rust-ABI trait methods, non-generic pure-value `const`/`assoc const` items, and pure scalar `AnonConst` items), plus explicitly requested concrete monomorphizations (`instantiations` / `--instantiate`) in `Scope::SelectedUnit`. | Required normal or build external crate dependencies, multi-target crates, uninstantiated polymorphic generics, closures, crate-local `#[lang]` items without `--stdlib-crate` (except `#[panic_handler]` in `bin` selected-unit scope), `struct`/`union`/`static`/`InlineConst` owners, bodyless free functions, and `unsafe`/unmodeled `trait`/`impl`/`const`/`AnonConst` items in whole-crate scope, global assembly, and proc-macro crates. |

For a realistic scalar example, `ci/verify_starnix_e2e.py` checks Starnix's
`ebpf_core` endianness conversion using symbolic MIR helpers in `Anneal.MirWp`.

## Experimental MIR Profile v2: borrowed slices and raw pointers

Capture selects Profile v2 (`mirProfileVersion = 2`) for the whole captured
program when any captured body uses one of its additions; a program without
them stays on Profile v1. Every body of a Profile v2 program, including
scalar-only ones, is checked against `UnitTheoremV2` or `CrateTheoremV2`. Its
receipt lists an "experimental Profile v2 MIR semantics" assumption and marks
`correspondence_provenance` inapplicable, because Pass 2 relates only Profile
v1 rules to `vendor/lean-miri/`.

| Category | Added by Profile v2 | Refused (fail-closed) |
| :--- | :--- | :--- |
| **Types** | General tuples; single-level `&T`, `&mut T`, `*const T`, and `*mut T` whose pointee is a Profile v1 scalar, `()`, an admitted enum, or an integer slice `[T]`; `RangeTo<usize>` and `RangeFrom<usize>`; lifetime-only generic signatures. | Nested references or pointers (`&&T`, `*const &T`, `&[&T]`), references and pointers to overflow pairs `(T, bool)` (whose unspecified tuple layout capture does not check, so overflow pairs are never addressable), `str`, structs, arrays, and the remaining Profile v1 refusals. |
| **Bodies** | Bodies whose locals include references or raw pointers, but not both. | Bodies whose locals mix references and raw pointers, because Profile v2 does not model Rust's pointer aliasing rules (Stacked or Tree Borrows). For example, `<&mut [u8] as SplitByteSlice>::split_at_unchecked`, which uses `as_mut_ptr` and `from_raw_parts_mut`, is refused. |
| **Statements & rvalues** | `Ref` of locals and of dereferenced references, `RawPtr` (address-of) of locals and of dereferenced raw pointers, assignment through dereferenced places, raw-to-raw `PtrToPtr` casts that do not add mutability, `IntToPtr` casts, `PtrMetadata`, `Offset`, `RangeTo`/`RangeFrom` aggregates, copy reads of tuple, overflow-pair, and range fields, and `Use` with retags. | Reference-to-raw-pointer and raw-pointer-to-reference conversions (refused with the mixed-locals rule), `*const T` to `*mut T` casts (Profile v2 cannot tell whether the pointee is an immutable binding, which the cast would let the body mutate), other pointer casts, index projections, field projections after a dereference, moves out of a projected place (`move (*p)`, `move (t.0)`), and other aggregates. |
| **Terminators** | `Assert` and returning calls to a closed set of `core` functions: `<[T]>::len`, `<[T]>::get_unchecked` (with `..n` or `n..`), `<*const T>::add`, `<*mut T>::add`, and `usize::unchecked_sub`. The captured `UnwindAction` (`Continue`, `Unreachable`, or `Terminate`) is recorded as is. | Every other call (including `<[T]>::{as_ptr, as_mut_ptr}` and `core::slice::from_raw_parts{,_mut}`, which convert between references and raw pointers), calls in crates that shadow `core`, and cleanup unwinds. |

Each query (`Query`) supplies caller memory (`callerMem`) alongside its
arguments. `SpecsV2` pairs per-function safety preconditions (`safety`,
required only of `unsafe` functions) with a whole-program `property`.
`ValidEntryArgsV2` requires live, in-bounds, aligned, initialized reference
arguments in caller allocations whose bytes decode to valid pointee values,
and disjoint mutable references. This applies to `unsafe` functions too, so a
receipt says nothing about callers that pass an `unsafe` function a reference
to uninitialized or invalid memory; receipts state this assumption.
Raw pointer arguments are unconstrained, so an `unsafe` function's `safety`
precondition must state their liveness, bounds, alignment, initialization, and
mutability. Mutability here means the allocation's mutability: Profile v2
does not track pointer aliasing permissions, so callers must also pass raw
pointers whose provenance permits the accesses the function makes (for
example, not a pointer derived from a live `&T` that the function writes
through). Profile v2 encodes memory little-endian and assumes natural ABI
alignment (1, 2, 4, 8, and 16 bytes for `i8` through `i128`, 8 bytes for
`isize` and pointers, and no added aggregate alignment). Capture admits only
targets whose data layout matches.

`tests/cargo-anneal/tests/profile_v2_e2e.rs` verifies the unmodified
`zerocopy/src/byte_slice.rs` `<&[u8] as SplitByteSlice>::split_at_unchecked`
under `UnitTheoremV2`, plus raw-pointer load and store fixtures under
`CrateTheoremV2`.

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

When building `cargo-anneal` itself with Cargo's `--no-default-features` flag
(for example, `cargo install --locked --no-default-features cargo-anneal`), the
default `setup` feature and remote archive download support (`exocrate`) are
omitted, so pass explicit `--capture`, `--sysroot`, and `--lean` paths to
`verify`. On `cargo anneal verify --manifest-path`, `--no-default-features`
instead disables default features of the target crate being verified.

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

Replace `<version>` with the semver version from a published `anneal-v<version>`
prerelease tag on GitHub Releases (for example, `0.2.0-alpha.11`, without the
`anneal-v` prefix; `main` stays at `0.0.0-dev` with an all-zero archive digest
rather than tracking published release metadata, so when running from a source
checkout use `cargo anneal setup --local-archive target/omnibus-link` as shown
in [Try a proof](#try-a-proof) above):

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

1. Run **Release** (`workflow_dispatch`) on `main`. Select `anneal`, enter the
   desired `0.2.0-alpha.<N>` version (such as `0.2.0-alpha.13`), keep `branch`
   set to `main`, and optionally pass a 40-character first-parent `main`
   `commit` SHA (leave blank to release current `main` `HEAD`). On `main`,
   `trusted/cargo-anneal/Cargo.toml` and `Cargo.lock` remain at `0.0.0-dev`
   with an all-zero archive digest; cutting a release opens no pull request and
   pushes no commits to `main`.
2. Wait for `anneal-build-archive`, `anneal-host-archive`, and
   `anneal-qualify-package` to finish on Ubuntu 24.04. Running release
   scripts and composite actions from the dispatched `main` workflow revision,
   the workflow resolves and pins the target commit SHA, builds the
   `x86_64-unknown-linux-gnu` omnibus archive from an isolated detached
   checkout of that commit, publishes it to a commit-and-digest-addressed
   GitHub prerelease (`anneal-toolchain-<commit12>-<sha256_16>`) after
   verifying GitHub's asset SHA-256, checks `anneal-release` environment
   protections, stamps the isolated target checkout in place, installs the
   packaged `.crate`, runs remote `cargo anneal setup` twice, and runs
   `ci/probe_alpha.py`.
3. Verify the resolved commit SHA, hosted toolchain digest, and qualification
   log, then approve the `anneal-release` deployment. Because `main` remains
   unpinned (`anneal-v<version>` tags commit `C`), `anneal-release` approvers
   act as the human review gate for the stamped release metadata before
   crates.io upload. `anneal-publish-crate` re-verifies SemVer ordering, live
   hosted archive integrity, and exact packaged source parity, publishes
   `cargo-anneal` from a freshly stamped clean checkout via OIDC, and verifies
   the uploaded `.crate` and crates.io checksum; `anneal-publish-github` tags
   `C` as `anneal-v<version>` and publishes path-scoped GitHub Release notes.

Concurrent merges to `main` do not disturb an in-flight release, and failed
qualification or rejected deployment approvals leave the SemVer version
reusable on a subsequent commit. `resolve-and-validate` checks `anneal-v*` Git
tags on `origin/main` first-parent history against un-yanked `crates.io`
versions: it fails closed if the target `anneal-v<version>` tag already exists
without a matching `crates.io` release or if any un-yanked `crates.io` release
strictly above the highest existing `anneal-v*` tag (`0.2.0-alpha.11` and
subsequent tagged releases) lacks a first-parent `anneal-v*` tag on `main`,
while tolerating four older untagged historical releases below that
high-water mark (`0.1.0-alpha.10`, `0.1.0-alpha.11`, `0.1.0-alpha.24`, and
`0.2.0-alpha.1`).
Post-crate recovery re-dispatch applies to commit-bound releases
(`anneal-toolchain-<C12>-<D16>`): if a transient failure occurs during archive
hosting, qualification, or GitHub Release creation, rerun the failed jobs within
the 24-hour (`retention-days: 1`) `upload-file-artifact` window; once that
artifact expires (or after `cargo publish` succeeds), dispatch **Release** again
for the same commit and version to rebuild or complete `anneal-v<version>`
against the published crate's commit and toolchain digest. If any un-yanked
`crates.io` release strictly above the highest `anneal-v*` tag lacked its
`anneal-v<version>` tag, push that tag onto its first-parent release commit
manually before dispatching a newer version.
