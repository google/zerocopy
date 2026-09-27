# Anneal omnibus archive read-only behavior at main 41f5b37

## Summary

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, Anneal's omnibus packager removes write permission bits from the entire staged `lean`, `rust`, and `aeneas` payload before creating the tar archive. The selected Exocrate installer then unpacks that archive into a staging directory and atomically renames the directory into place without adding write permission bits back. Anneal's v2 archive-cache test makes the intended consumer contract explicit: it recursively requires the installed `aeneas` subtree to have no write bits, then builds and checks a separate writable generated workspace that imports the installed Aeneas package without reconfiguring or rebuilding those read-only Lake artifacts.

That contract is narrower than "the installation is immutable." Exocrate creates the installation root itself; that root is not an entry from Anneal's tar and is not made read-only by the installer. The current test checks only the installed `aeneas` subtree and deliberately skips symlinks. Exocrate also treats an existing installation directory as resolved without revalidating its contents or permissions. The read-only property is therefore an archive-payload permission invariant used to catch accidental writes and support reuse, not a security boundary or tamper-evidence mechanism.

## Applicability

This report applies to the omnibus archive construction, Exocrate installer, and v2 archive-cache reuse test at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. The flake uses `flake-utils.lib.eachDefaultSystem` and defines platform mappings for `x86_64-linux`, `aarch64-linux`, `x86_64-darwin`, and `aarch64-darwin`. Anneal's Exocrate metadata and `parse_remote_archive!` invocation likewise enumerate Linux/macOS on x86-64/AArch64.

The directly inspected installation code is the in-tree Exocrate implementation used through Anneal's path dependency. This report describes source-defined construction and test expectations. No fresh archive was built or extracted during this investigation, so it does not promote the test's intended invariant into new execution evidence.

The separate #3720 subjects for archive checksum semantics, archive extraction security, timestamp normalization/Lake reuse, and atomic staging/rename have related code paths but different questions. They are referenced here only where they delimit what "read-only" means.

## Findings

### Anneal removes write bits only after the payload is fully staged

`packages.omnibus-tar` copies the selected Lean, Rust, and Aeneas derivations into `$TMPDIR/dist_staging/{lean,rust,aeneas}`. On Linux it then patches executable ELF interpreters/RPATHs and strips binaries. It checks staged Lake traces, performs its final Aeneas source/config timestamp adjustment, and only then runs:

```sh
chmod -R a-w $TMPDIR/dist_staging
cd $TMPDIR/dist_staging
tar -cf $out *
```

The permission transformation therefore covers the staged payload that the raw tar command consumes. `a-w` removes write permission for user, group, and other while preserving existing read and execute bits; it does not intentionally make binaries non-executable. Compression is a later derivation over the raw tar and does not mutate extracted permissions.

Basis: **source** — `anneal/flake.nix`, `packages.omnibus-tar` and `packages.omnibus-archive`.

### Exocrate does not add a second read-only enforcement pass

Anneal's setup command resolves either a local archive or the configured remote archive through `CONFIG.resolve_installation_dir_or_install`. Exocrate creates a managed staging directory, passes that directory to its installation callback, and then renames the populated staging directory to the final versioned path.

The install callback wraps the source in a zstd decoder and calls `tar::Archive::unpack(target_dir)`. There is no subsequent recursive `chmod`, `set_permissions`, or equivalent read-only transformation in the inspected installer. The final rename also changes only the directory name/location. Consequently, the current design relies on the archive payload's stored modes and the tar extraction implementation to carry the packaged no-write-bit state into payload entries; Exocrate does not reconstruct that invariant independently.

Basis: **source** — `exocrate/src/lib.rs::install` and `exocrate/src/sync.rs::ManagedDirName::check_exists_or_create`.

### The installation root itself is outside the archive permission invariant

Exocrate creates `<final-name>.staging` with `fs::create_dir_all` before extraction. Anneal's tar contains the top-level payload entries `aeneas`, `lean`, and `rust`; the staging directory that contains those entries is not itself an archive member. Exocrate later renames that staging directory to the final installation path without changing its permissions.

Thus the packaged `chmod -R a-w $TMPDIR/dist_staging` does not establish the permissions of Exocrate's final installation-root directory. The source-defined invariant is about extracted payload entries beneath that root, not about every inode in the installation path. A future consumer that needs the root directory itself to be non-writable must enforce or test that separately.

Basis: **source** — the final tar layout in `anneal/flake.nix` plus the staging-directory creation and rename in `exocrate/src/sync.rs`; **derived** conclusion about the root being outside the tar member set.

### The v2 test checks the Aeneas payload recursively, then keeps generated writes elsewhere

The feature-gated `test_archive_lake_cache_reuse` installs the Nix-built archive through the same `setup_installation_dir` path used by `cargo anneal setup`. It then calls `assert_no_write_bits` on `toolchain_root/aeneas` before invoking Lean/Lake.

On Unix, `assert_no_write_bits` rejects any non-symlink entry whose mode has `0o222` set and recursively descends into directories. The helper deliberately returns immediately for symlinks. The test therefore defines a strong recursive no-write-bit expectation for ordinary entries in the Aeneas subtree, but it does not assert that symlink metadata is read-only.

The test creates `generated-workspace` in a separate temporary directory, copies `lean-toolchain` into that workspace, writes generated Lean source and a Lake file there, and constructs a workspace-local manifest. It then runs `lake --keep-toolchain --old build Generated` followed by `lake --keep-toolchain env lean --json ...`. Its comment states the intended property directly: a fresh generated workspace must work without reconfiguring packages or rebuilding read-only Lake artifacts.

This is the important architectural boundary. The installed archive supplies executable/toolchain/package/cache state; mutable generated state belongs to the consumer workspace.

Basis: **source/test contract** — `anneal/src/main.rs::test_archive_lake_cache_reuse`, `assert_archive_lake_cache_reuse`, and `assert_no_write_bits`. No fresh **execution** evidence was acquired.

### Current test coverage does not prove every archive subtree is read-only after installation

The packager applies `chmod -R a-w` to the entire `dist_staging` tree, so the source construction intends the same no-write-bit property for `lean` and `rust` as for `aeneas`. The v2 test, however, calls `assert_no_write_bits` only on `aeneas_root`. It uses the installed Lean toolchain to run commands but does not recursively assert permissions beneath `lean` or `rust`.

Accordingly, there are two different evidence strengths:

- **source construction** supports the intended whole-payload no-write-bit transformation before tar creation;
- **test contract** explicitly checks the post-install invariant only for the Aeneas subtree.

Do not cite the current test as direct coverage of all three top-level payloads.

Basis: **source** — `anneal/flake.nix` and `anneal/src/main.rs`; **derived** distinction between construction coverage and test coverage.

### Existing installations are trusted as existing, not revalidated as read-only

`resolve_installation_dir_or_install` asks `ManagedDirName::check_exists` whether the final path is already a directory. If so, it returns that directory as `ResolvedExisting` and does not reopen the archive or rerun installation. `check_exists` checks directory existence/type; it does not walk the payload, compare modes, or repair permissions.

The read-only property is therefore established, at most, when the archive is initially constructed/extracted and by any external filesystem policy. Exocrate does not continuously enforce it. Manual permission changes or content changes to an existing installation are outside this invariant and are not detected merely by resolving the installation again.

This observation is about permission revalidation only. Remote/local checksum policy and extraction-security guarantees are separate report subjects.

Basis: **source** — `exocrate/src/lib.rs::Config::resolve_installation_dir_or_install` and `exocrate/src/sync.rs::ManagedDirName::check_exists`.

### "Read-only" is an accidental-write guard, not a security boundary

The implementation removes ordinary write bits from archive payload entries and tests those bits on the supported Unix hosts. It does not mount the installation read-only, apply an immutable filesystem flag, sandbox writers, or cryptographically attest the extracted tree on each use. The final installation root is not itself covered by the tar's payload modes, and Exocrate does not revalidate an existing tree.

Therefore the supported conclusion is operational: ordinary tools should be able to consume the packaged Aeneas/Lake state without writing back into it, and accidental attempts to do so should encounter filesystem permission restrictions under ordinary Unix permission enforcement. The evidence does not support treating the installed archive as protected against a user/process that can deliberately change permissions or otherwise mutate its filesystem state.

Basis: **derived** from the source-defined permission mechanism and absence of a stronger enforcement mechanism in the inspected paths.

## Boundaries

**No fresh extraction was performed.** This report does not claim a newly observed mode listing from a current `.tar.zst` or installed Exocrate directory. The current v2 source contains the recursive post-install assertion, but that is test code rather than execution evidence gathered here.

**Symlink permission metadata is intentionally outside the current assertion.** `assert_no_write_bits` skips symlinks. This report makes no claim that symlink mode metadata is normalized or meaningful across the supported hosts.

**The installation root is not claimed read-only.** The root is created by Exocrate around the archive payload and is not itself an archive member. The report does not infer its exact numeric mode beyond the source fact that Exocrate does not apply Anneal's recursive `a-w` operation to it.

**Windows is out of Anneal's current supported archive matrix.** The test helper has a non-Unix branch using `Permissions::readonly()`, but current Anneal archive metadata and flake mappings enumerate Linux and macOS. This report does not generalize the Unix mode-bit result to Windows installation semantics.

**Read-only is not integrity.** Remote checksum verification, local archive trust, malicious archive extraction, and post-install tamper detection are separate questions. The existence fast path is relevant here only because it does not revalidate permissions.

**Read-only is not Lake freshness.** Timestamp normalization and `lake --old` reuse determine whether Lake accepts prebuilt artifacts without rebuilding. Permission removal then ensures that a consumer cannot silently repair a bad freshness situation by writing into the packaged dependency tree. The two mechanisms should not be conflated.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary source revision: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`: `eachDefaultSystem` platform construction; `packages.omnibus-tar` staging, Linux fixups, final timestamp adjustment, `chmod -R a-w`, and raw tar creation; `packages.omnibus-archive` compression.
- `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`: `setup_installation_dir`; feature-gated local-archive installation test; recursive Aeneas no-write-bit assertion; generated workspace and Lake/Lean invocations.
- `anneal/Cargo.toml`, blob `9edee13427fd5e3699abd3709cc9f33d7652873e`: supported Exocrate remote platform metadata and in-tree `exocrate` path dependency.
- `exocrate/src/lib.rs`, blob `88cc0d5dd91082070b6ef475a32bf42c25f52115`: existing-installation fast path, local/remote source handling, zstd+tar extraction, and no post-extraction permission repair.
- `exocrate/src/sync.rs`, blob `85b6e203522e963af13d88ab4d3e7684ebb29252`: writable staging-directory creation, populate callback, atomic rename, and directory-existence semantics.

Related durable candidate evidence exists for archive timestamp normalization/Lake reuse and byte-level archive reproducibility. Those reports answer different questions: mtimes/freshness and exact archive bytes, respectively.

Evidence roles here are **source**, **source/test contract**, and **derived**. There is no fresh **execution** evidence.

## Revalidation

For another Anneal revision, first inspect the final `omnibus-tar` staging commands. The decisive construction check is whether every intended payload root still passes through a recursive no-write-bit transformation after all build/fixup steps and before tar creation.

Then inspect Exocrate's extraction and managed-directory paths. Confirm whether extraction still preserves archive modes without a later permission rewrite, whether the final installation root is still created outside the archive member set, and whether the existing-directory fast path has gained any content/permission validation.

The cheapest execution probe for this exact revision is:

1. build the exact `omnibus-archive-ci` artifact for one supported system;
2. inspect raw tar member modes before extraction;
3. install it through Anneal's `setup --local-archive`/Exocrate path into a fresh location;
4. recursively record mode bits for the installation root and each of `aeneas`, `lean`, and `rust`, treating symlinks separately;
5. run the existing archive-cache reuse test or equivalent generated-workspace Lake/Lean commands;
6. verify that the installed payload tree's metadata and content are unchanged by those consumers.

Repeat the mode/extraction probe on macOS if cross-host permission preservation matters. If the installation root itself must become non-writable, add an explicit root-level invariant and test rather than inferring it from the tar payload.
