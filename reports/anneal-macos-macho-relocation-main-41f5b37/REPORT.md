# Anneal macOS Mach-O relocation and signing at `google/zerocopy@41f5b37`

## Summary

Current Anneal does not perform a final Mach-O relocation or code-signing pass when it constructs the macOS omnibus archive. The final `omnibus-tar` stage copies the already-produced Lean, Rust, and Aeneas trees into `dist_staging`; its only binary-rewriting loop is guarded by `stdenv.isLinux` and operates on ELF files with `patchelf` and `strip`. On Darwin, the stage proceeds directly from the copies to trace-path checks, timestamp normalization, read-only permissions, and tar creation.

That absence is not equivalent to "no relocation mechanism." Relocatability on macOS is currently the composition of earlier component packaging and Anneal's runtime environment:

- The pinned Aeneas release builder explicitly runs `dylibbundler` on `aeneas`, copies its dylibs under `./libs`, and rewrites those dependencies to the `@executable_path/libs` prefix. The pinned release workflow builds both x86-64 and AArch64 macOS artifacts, extracts each final tarball, and runs `./aeneas --help`.
- The pinned Charon `charon-portable` derivation has an explicit Linux `patchelf` branch but no corresponding Darwin relocation step. Source inspection therefore does not establish that the standalone `charon` and `charon-driver` Mach-O load commands are free of Nix-store or other build-time paths.
- Anneal invokes Rust/Charon and Lean/Lake/Aeneas with macOS-specific `DYLD_LIBRARY_PATH` values pointing into the installed archive. Those environment settings are part of the effective runtime contract and can satisfy library lookup that is not encoded solely in Mach-O load commands.

Current source and CI also establish no final-archive code-signing invariant. Anneal does not invoke `codesign`, inspect embedded signatures, or validate Mach-O load commands after final staging. Apple documents that modifying signed executable code requires signing to occur after the modification. Consequently, any future Anneal-side `install_name_tool`, `dylibbundler`, strip, or equivalent Mach-O mutation must define and validate a signing policy after the last mutation rather than assuming an earlier signature survives.

The unresolved question is concrete, not conceptual: the exact macOS omnibus archive has not been scanned with `otool`/`codesign` in this report. A compact final-archive probe can close that gap by checking every Mach-O image for non-relocatable load paths and signatures, then executing the relocated toolchain from a path outside the Nix store.

## Applicability

The Anneal findings apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, including its macOS mappings for `x86_64-darwin` and `aarch64-darwin` and the omnibus archive construction in `anneal/flake.nix`.

The upstream packaging findings apply to:

- `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, the revision selected as Aeneas release `nightly-2026.06.03`;
- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, Charon `0.1.210`, selected by that Aeneas revision.

The Apple dynamic-loader and code-signing material is used to interpret the consequences of the inspected packaging. It describes macOS mechanisms rather than the byte-level state of Anneal's current archive.

No current macOS omnibus archive was built or executed for this report. Source-controlled release workflow steps are execution *instructions* and preserved CI policy, not fresh execution evidence from this investigation. The Aeneas workflow's smoke test is therefore evidence that the release process is designed to launch the repackaged `aeneas` binary on its macOS builders; this report does not independently replay that run or attest to a specific release artifact hash.

## Findings

### The final Anneal archive has a Linux binary-rewrite pass and no Darwin analogue

`packages.omnibus-tar` first copies the selected Lean toolchain, Rust toolchain, and compiled Aeneas tree into `$TMPDIR/dist_staging`. It then conditionally appends a binary-rewrite loop only when `pkgs.stdenv.isLinux` is true. That loop selects executable ELF64 files, may replace the interpreter, empties RPATH, and strips the file.

There is no corresponding `stdenv.isDarwin` branch in this final staging phase. The Darwin path does not invoke `install_name_tool`, `dylibbundler`, `codesign`, `otool`, or a Mach-O scanner before tar creation. The common tail checks only staged Lake trace files for selected absolute path prefixes, normalizes Aeneas source/config mtimes, makes the staging tree read-only, and writes the tar.

This makes the current macOS contract structurally different from Linux. Linux attempts to normalize binary loader metadata at the final composition boundary. macOS currently trusts the loader metadata produced by the component-specific earlier stages.

**Basis:** source.

### Aeneas deliberately relocates its own macOS executable around `@executable_path`

The pinned Aeneas `mk-aeneas-release` derivation adds `macdylibbundler` on Darwin. After copying `aeneas`, Charon, and the Lean backend into the release tree, it makes `aeneas` writable and runs:

```text
dylibbundler -od -b -x ./aeneas -d ./libs -p @executable_path/libs
```

The comments in the pinned source describe `-b` as fixing dependencies of the bundled libraries, `-d` as the bundled-library directory, and `-p` as the prefix written into load commands. Apple documents `@executable_path` as a dynamic-loader-relative prefix resolved from the main executable's directory. The intended result is therefore a self-contained Aeneas executable whose bundled non-system libraries live next to it under `libs/` rather than at their Nix build locations.

The corresponding release workflow has separate macOS x86-64 and AArch64 jobs. After precompiling the Lean library, it re-tars `dist_staging`, extracts the resulting tarball, and executes `./aeneas --help`. That smoke step exercises the repackaged Aeneas executable, not merely the Nix-store result.

This evidence is specific to `aeneas`. The release derivation passes only `./aeneas` as `dylibbundler -x`; it does not establish the standalone Charon binaries' loader metadata.

**Basis:** source + documentation.

### Charon's explicit portable fixup is Linux-only

At the pinned Charon revision, `charon-portable` copies `charon` and `charon-driver` from the unwrapped build. Its only explicit post-copy binary rewrite is inside a host-system check for Linux, where it uses `patchelf` to replace the ELF interpreter and remove RPATH.

There is no explicit Darwin branch in `charon-portable`. The Aeneas release builder copies those Charon binaries into its release tree but applies its Darwin `dylibbundler` command only to `aeneas`.

Two stronger conclusions would therefore be unjustified from the inspected source:

1. that Charon is non-relocatable on macOS; or
2. that Charon is already fully relocatable on macOS.

The underlying Nix/crane build can affect Mach-O install names and RPATHs before `charon-portable` copies the files, and no exact `otool` dump was captured here. The durable conclusion is narrower: there is no explicit Charon-specific Darwin relocation step in the pinned portable packaging, and the Aeneas release smoke test does not launch Charon.

**Basis:** source + derived.

### Rust and Lean are copied through the final stage, while Anneal supplies macOS library search paths at runtime

Anneal's fixed-output toolchain downloader deliberately disables patching and stripping in the download derivation. The final omnibus stage copies the selected Rust and Lean trees and, on macOS, does not subsequently rewrite their Mach-O images.

Anneal compensates at invocation time for at least two classes of dynamic-library lookup:

- `Toolchain::command(Tool::Charon)` clears the environment, sets `CHARON_TOOLCHAIN_IS_IN_PATH=1`, places the installed Rust `bin` first in `PATH`, and on macOS sets `DYLD_LIBRARY_PATH` to the installed Rust library directory.
- The Lake/Aeneas paths use `DYLD_LIBRARY_PATH` on macOS for the installed Lean `lib` and `lib/lean` directories. The V1 Aeneas invocation also sets `LEAN_SYSROOT` and prepends the installed Lean `bin` directory.

These environment variables are not evidence that any particular Mach-O load command is wrong. They are evidence that current operation is intentionally not defined solely by self-relative Mach-O metadata. A relocation test that launches binaries directly without Anneal's environment can therefore test a stronger property than the application currently relies on.

**Basis:** source.

### The archive-layout check does not validate Mach-O relocation or signing

`packages.omnibus-archive-layout-check` decompresses the archive listing and checks top-level names, required paths, the presence of Mathlib `.olean` files, and path-shape constraints such as rejecting absolute or parent-relative archive entries. It does not inspect executable file contents.

In particular, the current check does not establish any of the following:

- absence of `/nix/store/...` in `LC_LOAD_*`, `LC_ID_DYLIB`, or `LC_RPATH` commands;
- correspondence between referenced `@executable_path`, `@loader_path`, or `@rpath` libraries and files present in the archive;
- absence of build-directory paths in Mach-O load commands;
- validity, identity, or absence of embedded Mach-O code signatures;
- successful launch of the final **Anneal** macOS omnibus archive after relocation to an arbitrary install directory.

The trace-path check is similarly narrower: it scans selected `*.trace` files for absolute build paths, not executable loader metadata.

**Basis:** source.

### Mach-O load-command mutation and code signing have an ordering constraint

Apple describes dynamic-library install names and runtime paths as Mach-O load-command data. `LC_LOAD_DYLIB` identifies imported libraries; `LC_ID_DYLIB` identifies a dylib itself; `LC_RPATH` contributes runtime search directories; and `install_name_tool` can change these values in an existing Mach-O image.

Apple's code-signing guidance separately states that signing modifies an executable and that code should not be modified after it has been signed; when signed content must be modified, it must be signed again afterward.

For Anneal, the derived engineering constraint is straightforward:

1. perform all Mach-O load-command or binary-content rewrites first;
2. apply whatever signing policy Anneal chooses second;
3. verify loader metadata and signing state on the final bytes that will be archived.

Current Anneal does not implement such a final macOS sequence because it performs no final Mach-O rewrite and no explicit signing step. This report does **not** infer that current binaries are unsigned or invalidly signed; that requires inspecting the actual files.

**Basis:** documentation + derived.

### The highest-value missing evidence is a final-archive scan, not more source reconstruction

A bounded probe can determine the remaining relocation facts for each macOS architecture:

1. Build `.#omnibus-archive-ci` for x86-64 macOS and AArch64 macOS.
2. Extract each archive to a fresh path that contains no Nix-store prefix.
3. Identify every Mach-O executable and dylib, including fat Mach-O files.
4. Record `otool -L` and the relevant `otool -l` load commands for each file.
5. Classify each dependency/install-name/RPATH entry:
   - system absolute paths such as `/usr/lib/...` and `/System/Library/...`;
   - relative dynamic-loader paths using `@executable_path`, `@loader_path`, or `@rpath`;
   - archive-external absolute paths such as `/nix/store/...` or a build directory.
6. For any embedded signature, record `codesign -d` metadata and run strict verification on the final archived bytes. Record unsigned files distinctly rather than treating "unsigned" and "invalid signature" as the same state.
7. From the relocated extraction, run at least the packaged Aeneas, Charon, Rust, Lean, and Lake entry points under the same environment Anneal uses. Add a no-extra-environment launch only if testing the stronger self-contained-binary property.
8. Preserve the command output and archive SHA-256 with the report.

This probe directly distinguishes loader-path correctness, signing state, and successful runtime behavior. It also catches regressions that a source-only assertion about current packaging structure would miss.

**Basis:** derived.

## Boundaries

**Not examined:** No x86-64 or AArch64 Anneal macOS omnibus archive was built, extracted, scanned, or executed in this investigation.

**Unknown:** The exact `LC_LOAD_*`, `LC_ID_DYLIB`, and `LC_RPATH` contents of the Charon, Rust, Lean, and other Mach-O files in the current final archive are not established here.

**Unknown:** The exact embedded code-signature state of current archive binaries is not established. Absence of an Anneal `codesign` command does not imply absence of signatures, because upstream toolchains, linkers, or earlier packaging stages may produce or preserve them.

**Known not to apply:** Anneal's final `patchelf`/`strip` cleanup is Linux-only. It does not provide a macOS relocation or signing guarantee.

**Known not to apply:** The Aeneas release workflow's `./aeneas --help` smoke test does not establish that Charon, Rust, Lean, Lake, or the later Anneal-composed omnibus archive launches after arbitrary relocation.

**Not claimed:** This report does not treat `DYLD_LIBRARY_PATH` as equivalent to rewriting Mach-O load commands. It records the environment because Anneal's actual invocation paths depend on it.

**Not claimed:** This report does not require Anneal's command-line binaries to be Developer ID signed or notarized. The relevant current gap is that no signing state or policy is validated at the final composition boundary. Product-distribution policy is a separate decision.

**Not claimed:** No adjacent Aeneas, Charon, Lean, Rust, Nixpkgs, or macOS version inherits these findings automatically.

## Evidence

### Anneal

`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`

- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`
  - platform mappings near the top-level `system` dispatch;
  - `fetchToolchainAsset` with `dontPatchELF = true` and `dontStrip = true`;
  - `packages.omnibus-tar`: final staging copies and the Linux-only `patchelf`/`strip` loop;
  - `packages.omnibus-archive-layout-check`: archive-entry checks with no Mach-O inspection.
- `anneal/src/setup.rs`, blob `9e17911f4d1e7695cc63fe9f8b2b20b2f0322f00`
  - `Toolchain::command`;
  - `rust_library_path_env_var`.
- `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`
  - `run_lake_archive_command`, including the macOS `DYLD_LIBRARY_PATH` setup.
- `anneal/v1/src/charon.rs`, blob `7e33bda392770d04397f7172296d9a7f25c6e180`
  - Charon invocation environment.
- `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`
  - Aeneas/Lean invocation environment.

Evidence role: **source**.

### Aeneas

`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`

- `flake.nix`, blob `05e71549416ac622d6f12edc1fc7c74e338949ba`
  - `mk-aeneas-release`;
  - Darwin `macdylibbundler` input;
  - `dylibbundler -od -b -x ./aeneas -d ./libs -p @executable_path/libs`.
- `.github/workflows/release.yml`, blob `e248e9fdbecb3809f54ef58456db3faee448175f`
  - macOS x86-64 and AArch64 release matrix;
  - final tar reconstruction;
  - extract-and-run `./aeneas --help` smoke step.

Evidence role: **source**.

### Charon

`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`

- `flake.nix`, blob `844a2ca996e86acb053bbecd52ff251134341da8`
  - `charon-portable`;
  - Linux-only `patchelf` interpreter/RPATH rewrite;
  - no corresponding explicit Darwin branch in that portable wrapper.

Evidence role: **source**.

### macOS dynamic loader

Apple Developer Technical Support, “Dynamic Library Identification”:

- https://developer.apple.com/forums/thread/736719
- observed 2026-09-27;
- documents install names, `LC_ID_DYLIB`, `LC_LOAD_DYLIB`, `LC_RPATH`, `@executable_path`, `@rpath`, `otool`, and `install_name_tool`.

Apple, “Run-Path Dependent Libraries”:

- https://developer.apple.com/library/archive/documentation/DeveloperTools/Conceptual/DynamicLibraries/100-Articles/RunpathDependentLibraries.html
- observed 2026-09-27.

Evidence role: **documentation**.

### macOS code signing

Apple Technical Note TN2206, “macOS Code Signing In Depth”:

- https://developer.apple.com/library/archive/technotes/tn2206/
- observed 2026-09-27;
- documents that signing modifies executable bytes and that modification should precede signing; modified signed code must be re-signed.

Evidence role: **documentation**.

No fresh execution evidence is included in this package.

## Revalidation

For an Anneal source change, first inspect the smallest controlling regions:

1. `anneal/flake.nix` around `fetchToolchainAsset`, `packages.omnibus-tar`, and `packages.omnibus-archive-layout-check`;
2. the selected Aeneas `mk-aeneas-release` Darwin branch;
3. the selected Charon `charon-portable` wrapper;
4. Anneal's `DYLD_LIBRARY_PATH` construction in setup/Charon/Aeneas/Lake invocation paths.

If those regions are unchanged and the pinned subjects are unchanged, the source-structure findings remain cheap to recover. A dependency revision change requires re-reading the corresponding upstream packaging rather than assuming continuity.

For the stronger runtime property, run the final-archive probe described under **Findings** on both supported macOS architectures. Preserve:

- omnibus archive SHA-256;
- extraction path;
- every Mach-O file found;
- `otool -L` and relevant `otool -l` output;
- signature presence and `codesign --verify --strict` result;
- launch commands and environment;
- stdout/stderr and exit status.

Treat a clean source diff as insufficient evidence for byte-level relocation. Treat a successful `aeneas --help` as insufficient evidence for the rest of the composed toolchain. The exact final archive is the authority for the final loader/signature state.
