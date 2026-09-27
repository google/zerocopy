# ELF interpreter and RPATH fixups in Anneal's Linux omnibus archive

## Summary

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, Anneal does not rely on Nix store ELF metadata surviving into the distributed Linux toolchain archive. The final `omnibus-tar` derivation copies the staged Lean, Rust, and Aeneas trees into a writable temporary tree and then performs a broad best-effort rewrite over executable 64-bit ELF files. For binaries that have an ELF interpreter, it replaces that interpreter with a conventional host loader path: `/lib64/ld-linux-x86-64.so.2` on x86-64 Linux or `/lib/ld-linux-aarch64.so.1` on AArch64 Linux. It then sets the RPATH to the empty string and strips the file.

That final pass has two distinct jobs. First, it removes Nix-specific dynamic-loader and search-path references so the archive is not tied to the Nix store. Second, on AArch64 it repairs a concrete upstream Charon packaging defect: the pinned Charon `charon-portable` derivation writes the x86-64 loader path on every Linux host. Anneal's later host-specific pass overwrites that path when the Charon binaries reach the omnibus staging tree.

The current implementation should not be interpreted as a proved relocation invariant. Every mutating command in the final ELF loop is guarded with `|| true`, the loop only visits regular files that have an executable bit and whose `file` output contains `ELF 64-bit`, and no later check asserts that the interpreter or RPATH has the desired value. The archive layout check verifies names and path safety, not ELF metadata. The build can therefore succeed even if a candidate file was skipped or a `patchelf`/`strip` operation failed.

Clearing RPATH is also broader than merely deleting `/nix/store/...`: it removes relative search paths such as `$ORIGIN/...` as well. Anneal compensates for some of that loss at runtime. Its Lean/Lake execution paths explicitly provide the installed Lean `lib` and `lib/lean` directories through `LD_LIBRARY_PATH`, and Charon execution supplies the installed Rust `lib` directory while prepending the managed Rust `bin` directory to `PATH`. Thus relocation is partly encoded in the archive's ELF metadata and partly in Anneal's process environment.

Current preserved execution evidence is strongest on x86-64 Linux. The main Anneal CI builds the omnibus archive on `ubuntu-latest`, installs that exact archive into V1 jobs, and runs V1 tests and example verification. The V2 archive-cache test also executes the archived Lake/Lean toolchain, but it explicitly sets `LD_LIBRARY_PATH`. Upstream Aeneas separately smoke-tests its own Linux x86-64 and AArch64 release archives before Anneal's final transformation. No current source inspected here provides an equivalent post-Anneal AArch64 omnibus execution test.

No fresh Nix build, archive extraction, `readelf`, or executable probe was run for this report. The conclusions above are source- and CI-contract facts. A compact exact-archive probe is given below for revalidation.

## Applicability

This report applies to the current Anneal omnibus archive construction at:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`;
- `anneal/flake.nix` blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`;
- locked nixpkgs revision `549bd84d6279f9852cae6225e372cc67fb91a4c1`, which provides PatchELF 0.15.2;
- Aeneas `nightly-2026.06.03`, revision `ac9f1bc5262a5e4ff1e24ca78617121382202727`;
- Charon `0.1.210`, revision `a535e914f74db4fd9e6be7048f4233270d8945c0`.

The report covers Linux ELF interpreter/RPATH handling for the final Anneal archive. It does not cover Mach-O relocation/signing, archive checksums, extraction security, archive byte reproducibility, or the general host-platform matrix except where those topics constrain the ELF facts.

Two layers must be kept separate:

1. **producer transformation** — what Nix/Anneal writes into executable ELF metadata before compression; and
2. **consumer environment** — what Anneal adds to `PATH` and `LD_LIBRARY_PATH` when it runs tools from the extracted archive.

A binary can depend on either layer or both.

## Findings

### The final archive deliberately performs its own Linux ELF rewrite

`packages.omnibus-tar` copies the three toolchain trees into `$TMPDIR/dist_staging`:

- Lean into `dist_staging/lean`;
- Rust into `dist_staging/rust`;
- the compiled Aeneas payload into `dist_staging/aeneas`.

On Linux, the derivation adds `patchelf` and `file` to `nativeBuildInputs` and then walks:

```text
find $TMPDIR/dist_staging -type f -executable
```

For each file whose `file` output contains `ELF 64-bit`, the stage:

1. asks whether `patchelf --print-interpreter` succeeds;
2. if so, calls `patchelf --set-interpreter <host-loader>`;
3. calls `patchelf --set-rpath ""`;
4. calls `strip`.

The two configured loader paths are:

| Anneal Nix system | Installed ELF interpreter |
| --- | --- |
| `x86_64-linux` | `/lib64/ld-linux-x86-64.so.2` |
| `aarch64-linux` | `/lib/ld-linux-aarch64.so.1` |

Darwin systems do not run this loop.

This is an explicit portability boundary. The final distributed archive is intended to use ordinary host loader locations rather than a dynamic loader under `/nix/store`.

Basis: pinned **source** in `google/zerocopy:anneal/flake.nix`.

### Anneal preserves the downloaded Rust and Lean toolchain bytes until its later staging pass

The helper used to construct downloaded Rust and Lean toolchains sets:

- `dontPatchShebangs = true`;
- `dontPatchELF = true`;
- `dontStrip = true`.

The separately fetched `leantar` derivation does the same.

The reason stated in the source is to keep downloaded toolchains byte-for-byte independent of the Nix builder. Anneal therefore does not ask Nix's ordinary fixup machinery to make those downloaded assets Nix-native and then accidentally treat those mutations as upstream content. Their ELF rewrite is instead deferred to the later omnibus staging pass.

This distinction is important when diagnosing provenance. For the Rust/Lean asset derivations, an interpreter/RPATH observed before `omnibus-tar` should be attributed to the upstream archive. An interpreter/RPATH observed after `omnibus-tar` may have been rewritten by Anneal.

The Aeneas path is different. `aeneas-unpacked` is a normal derivation that extracts the release archive and does not carry the same explicit `dontPatchELF`/`dontStrip` declarations. Nix's generic fixup phase is documented in the pinned stdenv as the place that performs package-independent stripping and PatchELF work. Whether a particular Aeneas output file is changed by that phase is therefore an execution question; this report does not infer exact intermediate bytes from source alone. The final omnibus pass is the authoritative explicit rewrite before Anneal compression.

Basis: pinned **source** in Anneal's `flake.nix` and nixpkgs `pkgs/stdenv/generic/setup.sh`.

### The final pass repairs the pinned Charon AArch64 interpreter defect

Pinned Charon's `charon-portable` package copies `charon` and `charon-driver` into a portable output. On every Linux system it then executes:

```text
patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2
patchelf --remove-rpath
```

The condition tests only whether the host system name contains `linux`; it does not distinguish x86-64 from AArch64.

Aeneas selects that `charon-portable` output for its release package. Its Linux release workflow builds both `aeneas-linux-x86_64` and `aeneas-linux-aarch64`. The AArch64 artifact therefore inherits a source-level risk from Charon's hard-coded x86-64 loader unless a later transformation corrects it.

Anneal has such a later transformation. The omnibus stage identifies its own `system`, and on `aarch64-linux` replaces the interpreter of executable ELF files that expose one with `/lib/ld-linux-aarch64.so.1`. For Charon binaries that reach that loop, this later write supersedes the upstream `charon-portable` setting.

This is stronger than merely noting that Anneal has an AArch64 loader constant: the upstream and downstream transformations are ordered, and the downstream one is architecture-specific.

The remaining qualification is the best-effort nature of the final loop. If a Charon file were skipped by the selection predicate or `patchelf --set-interpreter` failed, the archive build would not fail solely for that reason.

Basis: pinned **source** in Charon `flake.nix`, Aeneas `flake.nix`/release workflow, and Anneal `flake.nix`.

### The rewrite is intentionally broader than removing Nix-store RPATH entries

PatchELF 0.15.2 defines `--set-interpreter` as replacing the dynamic loader and `--set-rpath` as replacing the executable/library RPATH. Anneal calls:

```text
patchelf --set-rpath ""
```

It does not call `--shrink-rpath` with an allowed-prefix policy, nor does it preserve relative `$ORIGIN` entries selectively.

The resulting semantic rule is therefore simple but broad: for every selected ELF file, Anneal attempts to make the RPATH empty.

That removes Nix-store search paths, but it can also remove a legitimate upstream relative lookup path. A tool that needs private libraries from its own archive cannot rely on an upstream RPATH surviving this pass unless the file is outside the selection set or the patch fails.

This point matters when evaluating future archive composition. Adding a dynamically linked helper with an `$ORIGIN/../lib` contract would not automatically be safe merely because it is "already portable" upstream; the omnibus pass would attempt to erase that contract.

Basis: pinned Anneal source plus PatchELF 0.15.2 documentation.

### Runtime environment variables carry part of the relocation contract

Anneal's consumer code supplies explicit library paths for important tool invocations.

For Charon, the current toolchain command path:

- sets `CHARON_TOOLCHAIN_IS_IN_PATH=1`;
- prepends the installed Rust `bin` directory to `PATH`; and
- sets the platform library-path variable to the installed Rust `lib` directory (`LD_LIBRARY_PATH` on Linux).

The root resolver likewise points Cargo metadata at the archive's Cargo/Rustc and sets the Rust library path.

For Lean/Lake, current execution code sets:

- `LEAN_SYSROOT` to the installed Lean root;
- `PATH` to include the installed Lean `bin`;
- `LD_LIBRARY_PATH` on Linux to include installed `lean/lib` and `lean/lib/lean`.

The V2 archive-cache test follows the same pattern for Lake, clearing the environment and then explicitly setting the installed Lean library paths.

These environment settings explain why removing an RPATH is not equivalent to removing the ability to find private libraries. The supported execution path can restore library lookup through process configuration.

They also establish a boundary: **the archive is not demonstrated to be a collection of independently relocatable executables that work under an empty environment.** Some tools are expected to be launched through Anneal's environment construction.

Basis: pinned **source** in `anneal/src/setup.rs`, `anneal/src/resolve.rs`, `anneal/v1/src/charon.rs`, `anneal/v1/src/aeneas.rs`, and the V2 test in `anneal/src/main.rs`.

### The final ELF rewrite is best-effort rather than fail-closed

Three properties make the final pass non-assertive.

First, the selection set is narrower than "all ELF files." A file must be:

- a regular file;
- marked executable; and
- classified by `file` with text matching `ELF 64-bit`.

Second, each mutating command tolerates failure:

```text
patchelf --set-interpreter ... || true
patchelf --set-rpath "" ... || true
strip ... || true
```

Third, no later stage reopens the archive and checks that:

- every dynamic executable has the configured host interpreter;
- no selected file has a nonempty RPATH/RUNPATH;
- no ELF metadata contains `/nix/store`; or
- no required `$ORIGIN` path was accidentally removed.

The existing `omnibus-archive-layout-check` decompresses the archive and verifies top-level names, required paths, absence of parent/absolute tar paths, and selected cache entries. It does not inspect ELF dynamic sections.

Accordingly, the source establishes an **attempted normalization algorithm**, not a fail-closed archive invariant. This is the most important distinction for future regression tests.

Basis: pinned **source** in Anneal `flake.nix`.

### Executable-bit filtering is a real coverage boundary

The loop starts with `find ... -type f -executable`. That is practical for command-line tools, but dynamic ELF objects do not semantically require the executable bit.

An ELF shared library or helper that lacks execute permission is outside the pass even if it contains an RPATH/RUNPATH or another absolute store reference. Conversely, an executable-bit ELF shared object can enter the pass; `--print-interpreter` should fail for a normal shared library, so the interpreter rewrite is skipped, while the RPATH rewrite is still attempted.

The current archive may happen to contain suitable modes. Source inspection alone cannot upgrade that observation into a complete-file guarantee. An exact archive audit should enumerate ELF files independently of mode, then compare that universe with the loop's selected universe.

Basis: **derived consequence** of the pinned selection expression and PatchELF operation split.

### The loader paths encode a glibc/FHS host assumption

Anneal does not set the interpreter to a Nix store path. It chooses two conventional absolute loader paths:

- `/lib64/ld-linux-x86-64.so.2`;
- `/lib/ld-linux-aarch64.so.1`.

Those paths make the archive independent of the Nix store, but not independent of the host's ABI/filesystem convention. A Linux environment using a different C library, loader placement, container policy, or non-FHS layout can still fail before `main`.

This is consistent with the current supported-host design. Anneal's Nix build itself uses an FHS environment for Linux Lean commands, and the bundled upstream Linux artifacts are glibc-oriented where dynamically linked. The important reference fact is that "relocated" means **relocated from Nix to the expected host ABI**, not "fully self-contained."

Basis: pinned Anneal source; no broader host-compatibility claim is made.

### Existing CI gives useful but asymmetric execution evidence

The current workflow builds `.#omnibus-archive-ci` in an `ubuntu-latest` job. It then publishes that exact file as a workflow artifact.

V1 test jobs download and install that archive and run the V1 test suite. Separate V1 example jobs install the same archive and run verification examples. These paths provide real post-packaging execution coverage for the x86-64 Linux archive in GitHub Actions.

The V2 job also downloads the archive and runs all features. Its archive-cache integration test executes archived Lake/Lean after explicitly setting the archive's Lean library directories.

Aeneas's own release workflow independently builds:

- `aeneas-linux-x86_64` with `aeneas-static-release`;
- `aeneas-linux-aarch64` with `aeneas-static-release`;

and smoke-tests each extracted upstream release with `./aeneas --help`.

These are different evidence layers. The Aeneas smoke test occurs **before** Anneal copies and rewrites the payload. Anneal's current CI archive builder runs on x86-64 Linux. The inspected workflow does not provide a post-Anneal AArch64 omnibus smoke test equivalent to the x86-64 one.

Basis: pinned **CI configuration** in `google/zerocopy:.github/workflows/anneal.yml` and `AeneasVerif/aeneas:.github/workflows/release.yml`.

### A fail-closed revalidation probe is cheap

A future exact-archive check does not need to run every compiler workload before it can validate ELF metadata.

For each supported Linux archive:

1. extract the exact final archive into a temporary directory;
2. enumerate **all** ELF files using `file` or ELF magic, without pre-filtering on execute permission;
3. record mode, ELF type, interpreter, RPATH/RUNPATH, and `DT_NEEDED`;
4. for every file with `PT_INTERP`, require the expected architecture-specific loader;
5. decide explicitly whether RPATH/RUNPATH must be empty or whether a small allowlist of relative entries is valid;
6. fail on `/nix/store` references in ELF interpreter/RPATH/RUNPATH;
7. separately report ELF files that the build-time `-executable` selector would have skipped;
8. run at least `rustc --version`, `cargo --version`, `charon --help`, `charon-driver --help`, `aeneas --help`, `lean --version`, and `lake --version` under the exact environment Anneal intends to support;
9. repeat a minimal Charon/Lean end-to-end operation that exercises private library loading.

Steps 2–7 turn the current best-effort transformation into an observable invariant. Steps 8–9 verify that removing RPATH did not discard a necessary runtime search path.

For AArch64, the Charon interpreter check is especially high value because it directly guards the pinned upstream x86-64 hard-code.

This probe is a **derived revalidation recommendation**. It was not executed for this report.

## Boundaries

**No fresh binary inspection.** No current omnibus archive was extracted and no `file`, `readelf`, `patchelf --print-*`, or executable command was run. Exact output metadata remains an execution fact.

**No claim that every Aeneas intermediate is or is not Nix-patched.** The Aeneas unpack derivation does not have the same explicit `dontPatchELF` declaration as the Rust/Lean download helper, and pinned Nix stdenv runs generic fixups. The final Anneal pass is explicit; exact intermediate Aeneas bytes require inspection.

**No Mach-O claim.** macOS relocation/signing has a distinct upstream `dylibbundler` path and is a separate inventory subject.

**No complete dynamic dependency proof.** This report identifies the library-path environments that current Anneal sets. It does not resolve every `DT_NEEDED` entry in every final binary.

**No musl portability claim.** The installed loader paths are glibc/FHS paths. The separately downloaded `leantar` uses a musl-targeted upstream asset on Linux, but that does not make the whole omnibus archive musl-host independent.

**No guarantee from `strip`.** The final loop attempts `strip` and ignores failures. This report does not depend on stripping for relocation correctness.

**No inference from archive layout validation.** The existing layout check is not an ELF validation pass.

**Current source only.** The exact algorithm, loader paths, candidate selection, and CI coverage can change independently.

## Evidence

Primary current Anneal source:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`
  - `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba` — host loader constants; byte-preserving Rust/Lean fetches; Aeneas compilation; final `omnibus-tar` ELF loop; layout check.
  - `anneal/flake.lock`, blob `92ac56b0a777d280f0a76e28f163b20ff6fb2003` — locked nixpkgs revision.
  - `anneal/src/setup.rs`, blob `9e17911f4d1e7695cc63fe9f8b2b20b2f0322f00` — installed Rust/Charon command locations and runtime library environment.
  - `anneal/src/resolve.rs`, blob `a87fa5cde060d5fbf59d47f68b5ed0823fe001c5` — Cargo/Rustc metadata execution with the managed Rust library path.
  - `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63` — archive-cache test and explicit Lean library-path environment.
  - `anneal/v1/src/charon.rs`, blob `7e33bda392770d04397f7172296d9a7f25c6e180` — Charon invocation with managed Rust paths.
  - `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4` — Lake invocation environment for the installed Lean toolchain.
  - `.github/workflows/anneal.yml`, blob `39f648acb45681707bb5f51624c279b44fa2e832` — current omnibus producer and post-install x86-64 CI consumers.

Upstream package source:

- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`
  - `flake.nix`, blob `844a2ca996e86acb053bbecd52ff251134341da8` — `charon-portable` hard-coded Linux x86-64 interpreter and RPATH removal.
- `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`
  - `flake.nix`, blob `05e71549416ac622d6f12edc1fc7c74e338949ba` — release assembly from `charon-portable`; Linux static Aeneas variant.
  - `.github/workflows/release.yml`, blob `e248e9fdbecb3809f54ef58456db3faee448175f` — per-platform release matrix and extracted `aeneas --help` smoke test.

Pinned tooling:

- `NixOS/nixpkgs@549bd84d6279f9852cae6225e372cc67fb91a4c1`
  - `pkgs/development/tools/misc/patchelf/default.nix`, blob `086e18e941858c130e684a5476d2f2bc681a4eea` — PatchELF 0.15.2 selected by the locked nixpkgs.
  - `pkgs/stdenv/generic/setup.sh`, blob `1c5c82be25b7db7ff5889356978f13a3cdd83049` — generic fixup phase explicitly described as performing stripping and PatchELF work.
- `NixOS/patchelf@0.15.2`
  - `README.md`, blob `0b4337714062dfde78dd9cdff0f56ea620e01f6a` — interpreter and RPATH mutation semantics.

Current inventory anchor:

- `google/zerocopy` issue #3720, observed 2026-09-27 — `ELF interpreter/RPATH fixups for Linux archives.` remained unchecked when this candidate was selected.

## Revalidation

After any change to Anneal archive construction, the pinned Aeneas/Charon release, or nixpkgs:

1. Re-read the host-to-loader mapping in `anneal/flake.nix`.
2. Re-read every `dontPatchELF`/`dontStrip` decision in toolchain acquisition and intermediate derivations.
3. Search the complete archive-production path for `patchelf`, `autoPatchelf`, `strip`, `RPATH`, `RUNPATH`, and interpreter rewrites.
4. Re-check the pinned Charon `charon-portable` package. In particular, determine whether Linux AArch64 still inherits an x86-64 interpreter before Anneal's final pass.
5. Re-check Aeneas release assembly and whether Linux artifacts remain static for Aeneas itself while carrying Charon portable binaries.
6. Re-check Anneal consumer environments for `LD_LIBRARY_PATH`, `DYLD_LIBRARY_PATH`, `LEAN_SYSROOT`, `CHARON_TOOLCHAIN_IS_IN_PATH`, and managed `PATH` composition.
7. Re-check workflow host coverage. Do not infer AArch64 post-Anneal execution from an upstream Aeneas AArch64 smoke test.
8. Build the exact final archive for each supported Linux architecture and run the fail-closed metadata/runtime probe above.
9. Preserve the probe output with the report if a future claim depends on exact final ELF state rather than source control flow.

If the build-time implementation becomes fail-closed—for example by enumerating all ELF files and asserting the desired interpreter/RPATH after mutation—update this report's best-effort boundary rather than carrying it forward mechanically.
