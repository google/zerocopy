# Anneal host-platform matrix at `google/zerocopy@41f5b37`

## Summary

Current Anneal's packaged-toolchain host intersection is exactly four systems:

| Nix host | Aeneas asset | Rust host triple | Lean archive platform | native `leantar` |
| --- | --- | --- | --- | --- |
| `x86_64-linux` | `aeneas-linux-x86_64.tar.gz` | `x86_64-unknown-linux-gnu` | `linux` | `x86_64-unknown-linux-musl` |
| `aarch64-linux` | `aeneas-linux-aarch64.tar.gz` | `aarch64-unknown-linux-gnu` | `linux_aarch64` | `aarch64-unknown-linux-musl` |
| `x86_64-darwin` | `aeneas-macos-x86_64.tar.gz` | `x86_64-apple-darwin` | `darwin` | `x86_64-apple-darwin` |
| `aarch64-darwin` | `aeneas-macos-aarch64.tar.gz` | `aarch64-apple-darwin` | `darwin_aarch64` | `aarch64-apple-darwin` |

`anneal/flake.nix` has explicit mappings for all four and throws for any other `system`. Aeneas's selected release workflow publishes the same four platform families. The ordinary Anneal archive then combines the platform-matched Aeneas release with a separately downloaded Rust `nightly-2026-05-31` host toolchain, Lean `v4.30.0-rc2`, and platform-matched `leantar`.

The matrix is not a blanket claim that every upstream component supports only these four systems. Charon's checked-in Rust toolchain names additional compilation targets, and upstream projects may build elsewhere. The table states the current **Anneal-packaged host surface**: the systems for which current source provides all required acquisition names/hashes and archive assembly logic.

Two source-level caveats are especially important. First, Charon's `charon-portable` Linux packaging unconditionally attempts to set `/lib64/ld-linux-x86-64.so.2` as the ELF interpreter even when the Nix host is Linux AArch64. Aeneas's release workflow does publish an AArch64 Linux archive, but its smoke test runs only `./aeneas --help`, not bundled `charon`. Current Anneal does not simply trust that interpreter: its final Linux staging pass rewrites ELF interpreters to `/lib64/ld-linux-x86-64.so.2` on x86-64 and `/lib/ld-linux-aarch64.so.1` on AArch64. That makes the final Anneal archive's Linux host story stronger than a source-only inspection of the upstream Aeneas tarball.

Second, Anneal records that Lean `v4.30.0-rc2`'s `linux_aarch64` archive carries an unusable x86-64 `leantar` helper. Anneal fetches `leantar` `0.1.16` separately for the actual host architecture instead of trusting the Lean-bundled copy. This is a helper-binary packaging defect, not evidence that the Lean AArch64 compiler itself is unsupported.

No fresh build or execution matrix was run for this report. The support levels below distinguish source-declared packaging, upstream release construction, smoke-test coverage, and gaps that still require execution.

## Applicability

The primary subject is `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. The selected upstream subjects are Aeneas `nightly-2026.06.03` at `ac9f1bc…`, its pinned Charon `a535e914…`, Rust `nightly-2026-05-31`, and Lean `v4.30.0-rc2`.

“Supported” in this report has a narrow meaning: current Anneal source has a complete host mapping for the component and can construct the corresponding package graph in principle. A stronger status requires execution evidence.

The report therefore uses four evidence levels:

- **Anneal mapped:** current `anneal/flake.nix` has an explicit platform mapping and fixed-output identity.
- **Upstream release-produced:** the selected Aeneas release workflow has an explicit build/archive matrix entry.
- **Upstream smoke-tested:** that workflow executes the named smoke command on the built archive.
- **Anneal integration-executed:** a current exact-platform Anneal omnibus build/setup/use path has been run and preserved as execution evidence.

This investigation establishes the first three from source where applicable. It does not establish the fourth.

The matrix is about **host platforms**, not Rust compilation targets. A Rust toolchain can contain target standard libraries for architectures other than the machine on which `rustc` itself runs. Charon's `rust-toolchain` `targets` list must not be read as the host-support list.

Detailed ELF/RPATH repair, Mach-O dependency/signing behavior, and the cross-architecture Lean helper anomaly are separate checklist subjects. They are mentioned only where they affect the host-support conclusion.

## Findings

### Anneal explicitly maps four and only four Nix host systems

`anneal/flake.nix` computes four upstream naming schemes from the current Nix `system`:

- `rustPlatform`
- `leanPlatform`
- `aeneasTarget`
- `leantarPlatform`

Every mapping has cases for:

```text
x86_64-linux
aarch64-linux
x86_64-darwin
aarch64-darwin
```

and an `else throw "Unsupported system: ${system}"`.

The same file supplies a platform-specific hash for the Aeneas release asset, Rust toolchain, Lean toolchain, `leantar`, and Mathlib cache materialization. Therefore a fifth Nix system cannot merely fall through to an upstream default; the current expression has no complete acquisition identity for it.

Basis: current Anneal **source**.

### The upstream Aeneas release publishes the same four platform families

At Aeneas `ac9f1bc…`, `.github/workflows/release.yml` has four build-matrix entries:

| Runner | Artifact | Nix package |
| --- | --- | --- |
| self-hosted Linux/Nix | `aeneas-linux-x86_64` | `aeneas-static-release` |
| `ubuntu-24.04-arm` | `aeneas-linux-aarch64` | `aeneas-static-release` |
| `macos-15-intel` | `aeneas-macos-x86_64` | `aeneas-release` |
| `macos-latest` | `aeneas-macos-aarch64` | `aeneas-release` |

Each job rebuilds the release staging tree, precompiles the Lean backend, creates `aeneas-{platform}.tar.gz`, and uploads that artifact to the nightly release.

Anneal's four `aeneasTarget` names match those four artifact names exactly.

Basis: pinned Aeneas **release workflow** + current Anneal **source**.

### Aeneas smoke-tests `aeneas`, but not the bundled Charon executables

The Aeneas workflow unpacks the just-created tarball and runs:

```text
./aeneas --help
```

That is useful per-platform evidence that the packaged Aeneas executable starts on the build runner.

The same release archive also contains `charon` and `charon-driver`, copied from Charon's `charon-portable` package. The release workflow does not run either binary in its archive smoke step.

Therefore the selected Aeneas release gives stronger direct execution evidence for the Aeneas frontend than for the bundled Charon executables. The latter have source/build evidence but are not covered by this release smoke command.

Basis: pinned Aeneas **workflow/source**.

### Linux AArch64 exposes a Charon-portable interpreter caveat

At Charon `a535e914…`, `charon-portable` copies `charon` and `charon-driver` and then, on any Linux host, attempts:

```text
patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2
```

The condition checks only whether the host-system string contains `linux`; the path itself is x86-64-specific. The command is followed by `|| true`.

This is a source-level portability hazard for a Linux AArch64 `charon-portable` output. It does not by itself prove the published `aeneas-linux-aarch64.tar.gz` Charon binary fails: this report did not execute the archive, and later packaging steps can rewrite ELF metadata. It does establish that Charon's portable-package source alone is not sufficient evidence for a correct AArch64 loader path.

The gap is material because the Aeneas release smoke test runs only `aeneas`, not `charon`.

Basis: pinned Charon **source** + pinned Aeneas **workflow**; failure risk is **derived**.

### Anneal's final Linux archive rewrites the interpreter per host

Current Anneal defines:

```text
x86_64-linux  -> /lib64/ld-linux-x86-64.so.2
aarch64-linux -> /lib/ld-linux-aarch64.so.1
```

During final omnibus staging, it walks executable files. For ELF64 inputs whose interpreter can be queried, it sets the platform-specific interpreter and removes RPATH.

Thus the final Anneal archive has an explicit host-aware repair after the upstream Aeneas archive has been unpacked and staged. On Linux AArch64 this is exactly the kind of operation needed to override the x86-64 path attempted by Charon's generic Linux `charon-portable` derivation.

This is source-defined repair logic, not fresh proof that every executable's dynamic dependencies are valid after repair. The dedicated ELF/RPATH report should own that stronger claim.

Basis: current Anneal **source** + **derived** relation to the Charon packaging caveat.

### Rust host acquisition covers the same four hosts

Anneal maps the four Nix systems to Rust distribution host triples:

```text
x86_64-linux   -> x86_64-unknown-linux-gnu
aarch64-linux  -> aarch64-unknown-linux-gnu
x86_64-darwin  -> x86_64-apple-darwin
aarch64-darwin -> aarch64-apple-darwin
```

For each host it downloads and merges `cargo`, `rustc`, `rust-std`, `rustc-dev`, `llvm-tools`, and `miri`, plus the architecture-independent `rust-src` archive, for date `2026-05-31`.

The Aeneas-pinned Charon source independently selects `nightly-2026-05-31`, so the host package and the driver requirement agree on the nightly date.

Charon's own `rust-toolchain` also lists several `targets`. That list includes, for example, Windows, i686 Linux, PowerPC64 Linux, and RISC-V bare metal. Those are requested **compilation targets**, not evidence that current Anneal packages native Charon/Aeneas/Lean hosts for those systems.

Basis: current Anneal **source** + pinned Charon **source**; host/target distinction is **derived** from rustup semantics encoded by the file shape.

### Lean host acquisition covers the same four hosts

Anneal maps:

```text
x86_64-linux   -> lean-4.30.0-rc2-linux.tar.zst
aarch64-linux  -> lean-4.30.0-rc2-linux_aarch64.tar.zst
x86_64-darwin  -> lean-4.30.0-rc2-darwin.tar.zst
aarch64-darwin -> lean-4.30.0-rc2-darwin_aarch64.tar.zst
```

and supplies a distinct fixed-output hash for each selected archive.

Aeneas's checked-in Lean project independently selects the same Lean release. Its release workflow precompiles the Lean library on all four Aeneas matrix runners before repackaging the Aeneas tarball.

The source therefore has two pieces of platform evidence: Anneal knows how to fetch a native Lean distribution for each of its four hosts, and the selected Aeneas release workflow runs the Lean precompile step on corresponding Linux/macOS x86-64/AArch64 runners.

Basis: current Anneal **source** + pinned Aeneas **workflow/source**.

### Linux AArch64 needs a separately selected `leantar`

Anneal contains an explicit comment that Lean `v4.30.0-rc2`'s `linux_aarch64` archive accidentally bundles an x86-64 `leantar`.

Rather than relying on that helper, Anneal fetches `leantar` version `0.1.16` separately with a native platform mapping:

```text
x86_64-linux   -> x86_64-unknown-linux-musl
aarch64-linux  -> aarch64-unknown-linux-musl
x86_64-darwin  -> x86_64-apple-darwin
aarch64-darwin -> aarch64-apple-darwin
```

The Mathlib-cache unpacking path then uses this separately fetched binary.

This narrows the Lean AArch64 support claim correctly: the selected Lean compiler archive can be used as part of Anneal's host graph, but one bundled helper is deliberately bypassed because its architecture is wrong.

Basis: current Anneal **source**. The detailed upstream anomaly remains a separate subject.

### Linux and macOS Aeneas artifacts are not packaged identically

Aeneas's release workflow uses `aeneas-static-release` on both Linux hosts and `aeneas-release` on both macOS hosts.

The Aeneas flake's release constructor additionally runs `dylibbundler` on the Aeneas executable when `pkgs.stdenv.isDarwin`, placing copied libraries under `libs/` and rewriting the executable to use `@executable_path/libs`.

No equivalent Darwin bundling command in this release constructor targets Charon's two binaries. Linux uses the static Aeneas derivation but still packages separately produced `charon-portable` binaries.

Consequently, “Aeneas release supports four hosts” does not mean the binary composition is uniform across them. Platform-specific dynamic-library handling is part of the support story and deserves separate validation.

Basis: pinned Aeneas **source/workflow**.

### Current Anneal's effective matrix is the intersection, not any one upstream's maximum

The current host matrix can be stated mechanically:

```text
Anneal supported host
  = host with Aeneas release mapping+hash
  ∩ host with Rust distribution mapping+hash
  ∩ host with Lean distribution mapping+hash
  ∩ host with native leantar mapping+hash
  ∩ host accepted by Anneal's final archive logic
```

At `41f5b37…`, that intersection is the four systems in the summary table.

This is safer than deriving Anneal support from any one component. For example, Charon's Rust toolchain knows compilation targets outside this set, while Anneal has no corresponding Aeneas/Lean archive mapping for them.

Basis: **derived** from current Anneal's explicit platform-selection source.

### Source-declared support is not the same as end-to-end execution coverage

The exact current evidence can be summarized as:

| Host | Anneal mapped | Aeneas release-produced | Aeneas smoke-tested | Aeneas Lean precompile step | Final Anneal integration executed here |
| --- | --- | --- | --- | --- | --- |
| x86_64 Linux | yes | yes | `aeneas --help` | yes | no |
| AArch64 Linux | yes | yes | `aeneas --help` | yes | no |
| x86_64 macOS | yes | yes | `aeneas --help` | yes | no |
| AArch64 macOS | yes | yes | `aeneas --help` | yes | no |

The first four columns are source/workflow facts. The last column is deliberately `no`: this investigation did not build the current Anneal omnibus archive or execute Charon/Aeneas/Lean from it on any host.

For Linux AArch64, the absence of an archived Charon smoke test matters more because of the loader-path caveat above. A future execution matrix should include `aeneas --help`, `charon --help` or a minimal translation, `lean --version`, `lake --version`, and one minimal Aeneas→Lean flow from the final Anneal archive.

Basis: pinned **source/workflow** + explicit absence of fresh execution.

## Boundaries

**This is the current Anneal host surface, not the upstream support universe.** Upstream Rust, Charon, Aeneas, Lean, Nix, or Lake may support hosts that Anneal does not package.

**Rust target triples are not host support.** Charon's `rust-toolchain` target list includes architectures outside Anneal's four hosts; that does not create native Aeneas/Lean artifacts for those systems.

**No fresh platform execution.** The report did not build or run the final omnibus archive on any platform.

**The Linux AArch64 Charon concern is source-level, not a demonstrated failure.** `charon-portable` attempts to set an x86-64 interpreter on Linux generally, but current Anneal later rewrites ELF interpreters by host. Only an execution inspection of the final archive can settle the end-to-end result.

**The Lean `leantar` anomaly is not a claim that Lean AArch64 is unusable.** Current Anneal deliberately substitutes a native helper.

**Windows is not an Anneal host.** A Windows Rust compilation target appears in Charon's toolchain target list, but current Anneal has no Windows Aeneas/Lean/archive mapping and rejects unrecognized Nix systems.

**Detailed relocation is separate.** This report identifies where Linux and macOS packaging differs; ELF interpreter/RPATH and Mach-O/signing correctness are separate checklist items.

**Aeneas smoke coverage is narrow.** The release workflow's archive smoke test starts `aeneas`; it does not prove Charon, Lean, Lake, or a complete translation/proof flow from the released tarball.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

**Anneal.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: four Nix systems; Aeneas/Rust/Lean/`leantar` platform mappings and hashes; Linux dynamic-linker selection; final ELF patching; Lean AArch64 `leantar` workaround.
- `anneal/flake.lock`, blob `92ac56b0a777d280f0a76e28f163b20ff6fb2003`: build-system input identities.

**Aeneas.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`):

- `.github/workflows/release.yml`, blob `e248e9fdbecb3809f54ef58456db3faee448175f`: four release matrix entries, per-platform Nix package selection, Lean precompile step, repackaging, `aeneas --help` smoke test.
- `flake.nix`, blob `05e71549416ac622d6f12edc1fc7c74e338949ba`: `charon-portable` inclusion, Linux static Aeneas package, Darwin `dylibbundler`, copied Charon toolchain file.
- `backends/lean/lean-toolchain`, blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`: Lean `v4.30.0-rc2`.

**Charon.** `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`:

- `flake.nix`, blob `844a2ca996e86acb053bbecd52ff251134341da8`: `charon-portable` construction and Linux interpreter rewrite.
- `rust-toolchain`: Rust `nightly-2026-05-31`, required components, and compilation-target list.

No fresh **execution** evidence was collected.

## Revalidation

For a later Anneal revision, rebuild the matrix from the current source rather than assuming that one platform list applies to every component.

1. Enumerate every `system` case in `anneal/flake.nix` for Aeneas, Rust, Lean, helper binaries, fixed-output hashes, and OS-specific patching. The supported host set is their complete intersection.
2. Resolve the selected Aeneas release and inspect its release workflow. Verify a matching artifact matrix entry exists for every Anneal host.
3. Inspect Aeneas's release constructor to determine whether Linux and Darwin use different package/linkage strategies and whether bundled Charon executables receive the same portability treatment as Aeneas.
4. At the pinned Charon revision, inspect `charon-portable` and `rust-toolchain`. Keep host architecture separate from rustup compilation targets.
5. Check Lean archive naming and every helper binary Anneal invokes. Do not assume a tool bundled inside a Lean archive has the same architecture as the compiler merely because the outer archive name is correct.
6. On Linux, inspect the final staged ELF interpreter and RPATH of `aeneas`, `charon`, `charon-driver`, `lean`, `lake`, and any native helper. On macOS, inspect architectures, load commands, copied dylibs, and code-signing behavior as required by the dedicated relocation report.
7. Execute at least one discriminating final-archive probe on every claimed host:
   - `aeneas --help`;
   - `charon --help` and a minimal Rust→LLBC extraction;
   - `lean --version` and `lake --version`;
   - native `leantar` invocation;
   - one minimal generated Lean file importing Aeneas and elaborating under the packaged Lake graph.
8. Preserve commands, host kernel/architecture, exact archive hash, tool versions, binary architecture/interpreter observations, and outputs.

The Linux AArch64 probe should be treated as high priority until the final archive's bundled Charon is directly demonstrated to start, because current upstream Charon packaging source contains an x86-64-specific interpreter path while current Anneal relies on a later host-specific repair.
