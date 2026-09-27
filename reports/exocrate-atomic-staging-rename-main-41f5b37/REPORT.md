# Exocrate atomic staging and rename behavior at `google/zerocopy@41f5b37`

## Summary

Current Exocrate keeps a managed installation path out of view while it populates a sibling staging directory, then installs that directory with one filesystem `rename`. Cooperating cross-process writers serialize through a persistent sibling lock file. After taking the lock, a writer rechecks whether another process already installed the target; otherwise it removes stale staging state, creates `<target>.staging`, populates it, and renames it to `<target>` only after population succeeds.

For Anneal's remote archive path, SHA-256 verification is inside that population operation. Exocrate extracts and drains the complete compressed input into staging, compares the final SHA-256, and returns an error on mismatch. The final target rename therefore occurs only after extraction and hash verification have succeeded. A normal error or Rust panic before rename triggers a guard that removes staging and unlocks the lock file.

The guarantee is narrower than a transactional package database. `check_exists` accepts any directory at the final path as a complete installation; there is no completion marker or content revalidation. The design relies on cooperating writers being the only creators of that final directory. The implementation explicitly says same-process concurrent calls are unsupported. It also performs no `fsync`/`sync_all` of payload files, staging, or the parent directory, so the source establishes atomic namespace publication, not power-loss durability.

## Applicability

These findings apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, specifically the `exocrate` crate used by current Anneal setup.

They cover `ManagedDirName::check_exists_or_create`, the `install` path that unpacks `.tar.zst` input into the supplied staging directory, and the public `Config::resolve_installation_dir_or_install` sequence.

The report distinguishes three kinds of concurrency:

- **cooperating processes:** intended to synchronize through the persistent lock file;
- **multiple calls in one process:** explicitly unsupported by the current implementation;
- **external/manual mutation:** outside the managed-writer protocol and therefore outside the atomic-completeness invariant.

No fresh fault-injection, process-kill, filesystem, or concurrency execution was performed. Checked-in tests are implementation evidence, not new execution evidence.

## Findings

### The final path is a publication point, not the workspace used for extraction

`Config::resolve_installation_dir_or_install` first resolves the final versioned path. If it already exists as a directory, it immediately returns `ResolvedExisting`. Otherwise it opens the requested source and calls `install`.

`install` delegates directory creation to `ManagedDirName::check_exists_or_create`. The managed-directory implementation computes two sibling paths from the final name:

- `<target>.lock`
- `<target>.staging`

It populates only `<target>.staging`. The final `<target>` name is created by renaming that completed staging directory.

Under the intended managed-writer protocol, readers that only use the final target name therefore do not observe the extraction progressing file by file. Before publication the final target is absent; after publication it names the populated tree.

**Basis:** source.

### Cross-process writers lock, then recheck before doing work

The implementation has an unlocked fast path: if the target is already a directory, it returns it immediately.

If the fast path misses, Exocrate creates the parent directory, opens the persistent sibling lock file, and takes an exclusive `fs2` lock. It then creates a cleanup guard and checks the final target **again** while holding the lock. This second check handles the ordinary race in which another process completes installation while the current process is waiting for the lock.

If the target now exists, the current writer marks its guard complete and returns the existing directory without populating staging.

The lock file intentionally remains on disk after unlock. A checked-in lockfile-semantics test documents the reason: stable lock-file identity avoids inode-replacement races between independently running versions of the library.

**Basis:** source.

### Staging recovery is idempotent for failed managed attempts

Once a writer owns the lock and confirms that the final target is absent, it removes the fixed sibling staging path if one remains from an earlier failed attempt, creates a fresh staging directory, and invokes the caller-supplied population closure.

A `StagingGuard` owns the staging path and lock. Unless marked complete, its destructor best-effort removes the staging directory and unlocks the lock file. The source explicitly constructs this guard before invoking `populate`, with a comment that cleanup must also occur if `populate` panics.

Checked-in tests cover:

- an ordinary population error after writing a partial file;
- a panic after writing a partial file;
- a conflicting non-directory destination causing the final rename to fail.

In each tested failure, the final target does not become a successful managed installation and staging is removed, aside from the intentionally persistent lock file.

A hard process termination does not run Rust destructors. The implementation compensates only on the next managed attempt: after obtaining the lock, it unconditionally removes any old sibling staging directory before creating a new one. This is recovery from stale staging, not evidence of synchronous cleanup at crash time.

**Basis:** source + derived.

### Remote hash verification precedes final publication

For a remote source, `install` wraps the input in a hashing reader and streams decompression/tar extraction into the staging directory. After tar extraction returns, it drains any trailing compressed-stream bytes into a sink so they are included in the archive hash. It then finalizes SHA-256 and compares it with the configured expected value.

A mismatch returns `InvalidData` from the population closure. Because the closure has not returned successfully, `check_exists_or_create` never performs the final rename and its guard cleans staging during ordinary unwinding.

Thus, for the managed remote path, successful final-name publication follows both successful extraction and successful checksum verification.

For a local archive, current Exocrate supplies no expected checksum; successful extraction is the population gate before rename.

**Basis:** source.

### The final operation is a sibling-directory rename

After `populate` succeeds, the implementation calls:

```text
fs::rename(<target>.staging, <target>)
```

The staging path is constructed by changing only the target file name, so staging and target have the same parent. That design avoids intentionally staging on a different filesystem, where a rename could fail because it crosses filesystem boundaries.

The source describes the resulting managed directory as "atomic": if a managed directory exists, it has already been fully populated. That statement depends on the managed-writer protocol and on filesystem rename semantics; it is not a claim that arbitrary external mutation cannot create misleading state.

After rename succeeds, the guard is marked complete and the function returns the managed final path.

**Basis:** source + derived.

### Directory existence is the only completion marker

`ManagedDirName::check_exists` treats the final path as valid when `Path::is_dir()` is true. If something exists there but is not a directory, it returns `AlreadyExists`; if nothing exists, it returns `NotFound`.

There is no manifest, sentinel, expected-file check, checksum record, or version contents check at resolution time. `Config::resolve_installation_dir` and the fast path of `resolve_installation_dir_or_install` inherit this behavior.

Consequently, "if it exists, it is complete" is an invariant maintained by Exocrate's publication protocol, not independently verified state. A manually created final directory, an incompatible actor that bypasses the lock/staging protocol, or corruption after installation can be accepted as `ResolvedExisting`.

**Basis:** source.

### Same-process concurrent installation is outside the current guarantee

The implementation documentation on `check_exists_or_create` explicitly states that concurrent calls from the same process are not concurrency-safe.

This matters because the high-level phrase "locked install" is otherwise easy to over-generalize. The lock protocol is intended to coordinate separate processes; current Exocrate does not claim that two same-process callers targeting the same installation can safely race through this path.

The #3720 inventory tracks same-process concurrency separately. This report records the boundary but does not attempt to solve or characterize every possible interleaving.

**Basis:** source.

### Atomic visibility is not crash-durable commit

No inspected installation path calls `File::sync_all`, `sync_data`, or an equivalent parent-directory fsync before or after rename. The implementation therefore does not establish that a sudden power loss after a successful return will preserve every payload write and the directory rename on all supported filesystems.

This is a different property from namespace atomicity. The staging/rename protocol prevents ordinary cooperating readers from observing a partially populated final name, while explicit syncing would be needed to make a stronger persistence claim about abrupt system failure.

The checked-in cleanup guard likewise handles Rust unwinding, not `SIGKILL`, process abort, kernel failure, or power loss.

**Basis:** source + derived.

### Source acquisition can begin before the installation lock

At the public level, `resolve_installation_dir_or_install` performs an initial existence check and, after a miss, opens the source before entering `install` and acquiring the managed-directory lock.

For a remote source, `open_source` performs the HTTP request before the lock. Two processes that both miss the initial existence check can therefore initiate source acquisition concurrently even though only one will later populate/install after the lock and recheck.

This does not violate the atomic final-directory invariant. It means the locking boundary serializes installation work, not necessarily all network or file-open work preceding it.

**Basis:** source + derived.

## Boundaries

**Known not to apply:** same-process concurrent `check_exists_or_create` calls are explicitly outside the current concurrency guarantee.

**Known not to apply:** external/manual writers that create or replace the final directory without following the lock/staging protocol are not made safe by the managed-directory design.

**Not established:** power-loss durability. No explicit payload/staging/parent filesystem synchronization was found.

**Not established:** content integrity after installation. Existing directories are accepted based on directory existence, without a completion manifest or checksum revalidation.

**Not established:** security of tar extraction. Archive path/symlink handling is a separate #3720 subject.

**Not established:** remote/local checksum trust policy beyond its ordering relative to rename. The detailed checksum semantics are separate inventory subjects.

**Not established:** whether every filesystem supported by Rust/Anneal provides identical failure behavior for directory replacement. The implementation reports rename failures as manual modification, concurrency bugs, or, on Windows, open handles; this report does not generalize beyond the source contract.

**Not claimed:** source acquisition is serialized. It occurs before the managed-directory lock.

## Evidence

### Exocrate public installation path

`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`

- `exocrate/src/lib.rs`, blob `88cc0d5dd91082070b6ef475a32bf42c25f52115`
  - `Config::resolve_installation_dir`
  - `Config::resolve_installation_dir_or_install`
  - `Config::open_source`
  - `install`

The `install` function shows the ordering between extraction, optional remote checksum validation, population closure success, and managed-directory publication.

Evidence role: **source**.

### Managed-directory protocol

Same repository/revision:

- `exocrate/src/sync.rs`, blob `85b6e203522e963af13d88ab4d3e7684ebb29252`
  - `ManagedDirName::check_exists`
  - `ManagedDirName::check_exists_or_create`
  - `ManagedDirName::staging`
  - `ManagedDirName::lock_path`
  - checked-in tests for success, existing target, error cleanup, panic cleanup, rename failure, and stable lockfile semantics.

Evidence role: **source**.

### Dependency context

Same repository/revision:

- `exocrate/Cargo.toml`, blob `b6cd1948ac4ae66b25a33ed93c10ee23de9b35b3`
  - `fs2 = "0.4.3"`
  - `tar = "0.4.45"`
  - `zstd = "0.13.3"`

Evidence role: **source**.

No fresh execution evidence is included.

## Revalidation

For source-level revalidation, inspect `exocrate/src/sync.rs` first. The discriminating questions are:

1. Does the implementation still populate a sibling path rather than the final path?
2. Is the lock still acquired before staging cleanup/population and held through rename?
3. Does it still recheck the final target after acquiring the lock?
4. Is the final publication still one sibling-directory rename?
5. Does the cleanup guard still remove staging on ordinary error/panic?
6. Is same-process concurrency still explicitly unsupported?
7. Has any completion marker/content validation or filesystem synchronization been added?

Then inspect `exocrate/src/lib.rs` to confirm that remote hash verification still occurs inside population before successful return to the rename step, and whether source acquisition still precedes the lock.

For stronger operational evidence, add a fault/concurrency probe around a temporary custom location:

- two separate processes race to install different instrumented payloads;
- one process is terminated during extraction, then a new process retries;
- population returns an error after writing partial staging;
- a hash mismatch occurs after extraction;
- a conflicting final path appears before rename;
- readers repeatedly poll the final name during population and publication.

Record directory listings, target contents, staging/lock state, and exit statuses. A separate durability probe would require filesystem-specific crash/power-loss methodology; ordinary process termination does not establish that property.
