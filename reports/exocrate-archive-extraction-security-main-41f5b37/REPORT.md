# Exocrate archive extraction security at Anneal main 41f5b37

## Summary

Current Anneal uses Exocrate's `tar::Archive::unpack` path for both local and remote `.tar.zst` toolchain archives. The resolved `tar 0.4.46` implementation provides substantial **best-effort extraction-root containment**: it rejects `..` path components, canonicalizes parents before writes, validates hard-link targets inside the destination, and revalidates paths reached through archive-created symlinks before later entries use them. It explicitly does **not** defend against concurrent mutation of the destination tree.

A separate and more important installation-integrity problem remains present in the exact current Exocrate source. Remote archives are unpacked into a deterministic staging directory **before** their pinned SHA-256 is accepted. Failure cleanup ignores `remove_dir_all` errors, and the next attempt again ignores stale-staging cleanup failure before extracting into the same tree. Consequently, the September 2026 rejected-archive advisory (#3612) still describes the current source-level state transition: an unauthenticated archive can leave residue which a later correctly authenticated archive does not contain, yet which can be promoted with that later archive if cleanup is blocked. The advisory's demonstrated permission-based residue mechanism requires no path-traversal failure in `tar`.

Three follow-up commits referenced from #3612 implement authentication-before-extraction and stronger staging protocols, but all three are one-commit side branches from the advisory's vulnerable revision and are not ancestors of current `main`. Current `main` retains the vulnerable extraction-before-hash and ignored-cleanup structure.

## Applicability

The Exocrate findings apply to `google/zerocopy` revision `41f5b37afe7060fd9fe08c00b200672cd76d77b9`, specifically `exocrate/src/lib.rs` and `exocrate/src/sync.rs`. Current Anneal v2 at the same revision selects that local Exocrate crate and resolves `tar 0.4.46` at `composefs/tar-rs@fc459c149f83bf4daceaa52e17d351989002e1a9` through `anneal/Cargo.lock`.

Anneal v2's `setup` path selects `Source::Remote(REMOTE)` unless the caller supplies `--local-archive`. Its current `Cargo.toml` still labels the remote URLs and hashes as placeholders that must be replaced before publishing the crate. Therefore, the current v2 source **contains and would exercise** the vulnerable remote-install protocol once real remote metadata is supplied, but the placeholder configuration is not evidence of a presently usable production download origin. The historical #3612 reproduction was performed against Exocrate at `2dad389b030e9268d6645ac0bf0626b867e96068` through Anneal v1's real remote-archive path.

`Source::Local` has no expected SHA-256 in Exocrate. For that mode, archive authenticity is deliberately outside this checksum mechanism; extraction-root containment still matters, but “authenticate before extraction” has no meaning unless the caller supplies an independent trust boundary for the local file.

The tar containment claims apply to ordinary extraction without concurrent hostile mutation of the destination namespace. `tar 0.4.46`'s own crate-level security documentation expressly excludes concurrent destination-tree mutation from its threat model.

## Findings

### 1. Current remote installation mutates the staging tree before authentication

For `Source::Remote`, `Config::open_source` returns the response stream plus the configured expected SHA-256. `install` wraps that stream in a hashing reader, then immediately places the hashing reader under a zstd decoder and `tar::Archive`, and calls `archive.unpack(target_dir)`. Only after extraction completes does Exocrate drain any compressed trailing bytes, finalize SHA-256, and compare it to the expected digest.

This ordering means the digest gates **promotion**, not filesystem effects inside the staging directory. A wrong-hash archive can create files, directories, permissions, and symlinks in staging before `install` returns `InvalidData`.

Basis: source.

### 2. The deterministic staging protocol can reuse residue from a rejected archive

Current `ManagedDirName::check_exists_or_create` uses a stable sibling path `<target>.staging`. Before population it executes `remove_dir_all(staging)` and discards the result, then calls `create_dir_all(staging)`. On an unsuccessful population, `StagingGuard::drop` again calls `remove_dir_all(staging)` and discards the result.

If a failed archive leaves a staging subtree which the installing process cannot remove, the next attempt can therefore proceed with the same nonempty staging tree. `tar::Archive::unpack` documents that unpacking into an existing directory merges content. If the new archive can be extracted successfully without needing to overwrite the protected residue, its hash authenticates only the new compressed input stream; the final `rename(staging, target)` can then promote both the authenticated files and older unauthenticated residue.

Basis: source + derived state-transition analysis; corroborated by the preserved public advisory reproduction.

### 3. The advisory's permission technique is consistent with the resolved tar implementation

`tar 0.4.46` delays directory entries until after non-directory descendants are extracted. It does so specifically so restrictive directory permissions do not prevent descendants from being created. The delayed directory application then sets the archive-specified permissions.

That behavior enables the #3612 demonstration without any extraction-root escape: the malicious archive first places a file beneath `unexpected/`, then applies a non-writable mode to `unexpected/`. A checksum mismatch occurs after those effects. For an unprivileged installing process on a filesystem enforcing Unix permissions, ordinary recursive deletion can then fail, preserving the child file for the next attempt.

The advisory separately demonstrated that a rejected protected subtree can instead cause a later authentic installation to fail persistently. Which outcome occurs depends on how the authentic archive interacts with the protected residue.

Basis: source + historical execution evidence in #3612.

### 4. The resolved tar crate blocks ordinary `..` traversal and checks canonical parents

`EntryFields::unpack_in` rebuilds each archive path component-by-component beneath `dst`. Prefix/root/current-directory components are ignored; any `ParentDir` component causes the entry to be skipped; normal components are appended below `dst`.

Before extraction, tar creates required parents while repeatedly validating existing ancestors. It canonicalizes the target parent and destination root and requires the canonical parent to start with the canonical destination. This catches ordinary attempts to reach outside the extraction root through an already-present or archive-created symlink in an ancestor path.

Basis: source + upstream security documentation.

### 5. Symlinks may point outside the archive root, but later writes through them are checked

A symlink archive entry is allowed to create the link with the archive-provided target; tar does not require the link target string itself to remain inside `dst`. The containment boundary instead applies when a later archive entry attempts to use a path whose parent traverses that link: canonical-parent validation must still resolve inside `dst`.

Thus the extractor can legitimately leave an outward-pointing symlink in the extracted tree. Whether a later Anneal/toolchain consumer following such a symlink is acceptable is a **consumer-level archive-content policy** question, not something `tar::Archive::unpack` prevents.

Hard links are stricter during unpacking: when `unpack_in` supplies a destination base, tar joins the hard-link target under that base and runs the same canonical-inside-destination check before `fs::hard_link`.

Basis: source.

### 6. tar's extraction containment is explicitly best-effort, not capability-safe

The crate-level security documentation states that concurrent mutation of the destination tree is outside the threat model. A second process can create a time-of-check/time-of-use race, such as atomically swapping a symlink after validation. The implementation uses path canonicalization and ordinary filesystem operations, not directory-capability/openat-style handles throughout extraction.

Exocrate's normal staging location is protected by its own cooperative target lock against other compatible Exocrate processes for the same target, but that is not a sandbox against unrelated local actors who can mutate the installation parent. Current Exocrate documentation does not establish that such actors are excluded from the staging namespace.

Basis: upstream documentation + source + derived composition boundary.

### 7. tar does not create arbitrary device nodes for unrecognized typeflags

The unpack implementation has special handling for directories, hard links, symlinks, PAX/GNU metadata entries, and regular-file data. After those cases, it follows the documented POSIX compatibility rule that an unrecognized typeflag is written as a regular file. In this resolved implementation, the generic fallthrough opens a new ordinary file and writes entry data; there is no `mknod`/`mkfifo` path in the examined extraction code.

This narrows one common archive-extraction concern, but it does not make arbitrary archive contents safe for later execution. Executable bits, symlinks, filenames, and ordinary file bytes can still be attacker-selected before a remote checksum is accepted in current Exocrate.

Basis: source.

### 8. The proposed #3612 repairs are not current authority

Issue #3612 references three commits with the same parent, `2dad389b030e9268d6645ac0bf0626b867e96068`:

- `7c15c7984a20b0c8f8b76574c052581f1abcfc8a`;
- `1ef6ed4b53f162352336dae0d73dd4d362796f57`;
- `4d866f8381fb79cec80e7257f15f95674441da0e`.

They are successive design variants, not merged history. Each changes Exocrate to spool/authenticate the complete compressed stream before parsing it and strengthens staging cleanup/namespace rules. GitHub ancestry comparison against current `main` reports each commit as diverged with merge base `2dad389b030e9268d6645ac0bf0626b867e96068`; current `main` is thirty commits ahead of that merge base while each proposal is one commit on the other side. Exact current source independently confirms that none of those repair semantics is present.

The issue remains open. Future work should therefore treat those commits as useful design/history evidence, not as the current Exocrate contract.

Basis: repository history + current source.

## Boundaries

- **No fresh exploit execution in this report.** The persistence exploit is source-revalidated against current Exocrate and historically execution-demonstrated in #3612, but this report did not rerun the reproducer against current `main`.
- **Current v2 remote metadata is placeholder-only.** The report establishes current code-path semantics, not that the placeholder `example.com` configuration constitutes a deployed vulnerable release channel.
- **No claim about hostile concurrent local mutation.** tar explicitly excludes concurrent destination mutation from its containment threat model. Exocrate's cooperative lock does not by itself establish protection against unrelated local namespace mutation.
- **Outward symlinks are not automatically an extraction escape.** tar permits them as extracted objects while checking subsequent extraction writes. Whether their presence is safe for later consumers is not established here.
- **Local archives are not authenticated by Exocrate.** A caller choosing `Source::Local` must supply whatever provenance/integrity guarantee its threat model requires.
- **Checksum trust policy is separate.** This report does not assess how release hashes are generated, signed, distributed, or updated; it only describes when Exocrate applies a configured hash relative to extraction.
- **Atomic publication is separate.** Exocrate's final rename and cross-process locking are covered by a separate atomic-staging report. They do not repair unauthenticated residue already incorporated into the staging tree.
- **Power-loss durability is not established.** Neither this report nor current Exocrate establishes an fsync-based durability protocol for archive bytes, staging contents, or rename metadata.

## Evidence

Primary current-source evidence, observed 2026-09-27:

- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `exocrate/src/lib.rs`, blob `88cc0d5dd91082070b6ef475a32bf42c25f52115`: `Source`, `Config::open_source`, `install`, and tests around invalid archives/hash mismatch.
- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `exocrate/src/sync.rs`, blob `85b6e203522e963af13d88ab4d3e7684ebb29252`: `ManagedDirName::check_exists_or_create`, deterministic staging path, ignored cleanup errors, rename publication.
- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63`: v2 setup chooses remote source unless `--local-archive` is supplied.
- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/Cargo.toml`, blob `9edee13427fd5e3699abd3709cc9f33d7652873e`: Exocrate dependency and placeholder remote archive metadata.
- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/Cargo.lock`, blob `eeaa3f7119369d79b735d8c4836fc08bcc7f7e6d`: resolves `tar 0.4.46`, crates.io checksum `3f6221d9a6003c78398e3b239969f352578258df48c8eb051caadae0015bc840`.

Resolved tar implementation:

- `composefs/tar-rs@fc459c149f83bf4daceaa52e17d351989002e1a9` (`tar 0.4.46`), `src/lib.rs`, blob `8a848f28ba58cf7e3cf2018c3a5e14f4751781eb`: crate-level security contract and concurrent-mutation exclusion.
- Same revision, `src/archive.rs`, blob `bffeb6f1b931e44afdb636532eef085b1db65ae0`: `Archive::_unpack`, including deferred directory application.
- Same revision, `src/entry.rs`, blob `1a4c4e9b2f045afdc42b47a9dd7eb7bea462cdeb`: `EntryFields::unpack_in`, `validate_inside_dst`, symlink/hard-link handling, ordinary-file fallthrough.
- Same revision, `Cargo.toml`, blob `258f3abda123c1abfe64532c1ff485b50f81095a`: package version `0.4.46`.

Historical advisory and repair attempts:

- `google/zerocopy#3612`, created 2026-09-04 and still open when rechecked on 2026-09-27: “Security Advisory: Rejected Exocrate archives leave attacker files in later authenticated installations.” The issue contains the macOS arm64 reproduction against `google/zerocopy@2dad389b030e9268d6645ac0bf0626b867e96068`, plus the permission-residue root-cause analysis.
- Proposed repair commits `7c15c7984a20b0c8f8b76574c052581f1abcfc8a`, `1ef6ed4b53f162352336dae0d73dd4d362796f57`, and `4d866f8381fb79cec80e7257f15f95674441da0e`; each has parent `2dad389b030e9268d6645ac0bf0626b867e96068` and is not an ancestor of current `main`.

The report package preserves a compact machine-readable `security-model.json` and `source-map.json` so later agents can recheck the state transition and exact evidence coordinates without reconstructing this research path.

## Revalidation

For a later Anneal/Exocrate revision, the cheapest discriminating checks are:

1. Inspect `exocrate/src/lib.rs::install`. If a remote stream can reach zstd/tar parsing before the expected digest is finalized and accepted, the pre-authentication filesystem-effect finding remains applicable. If the complete compressed stream is authenticated first and extraction consumes those exact authenticated bytes, this part has changed materially.
2. Inspect `exocrate/src/sync.rs` around staging acquisition and failure cleanup. Determine whether every population attempt begins with a demonstrably empty staging directory and whether cleanup failure is fail-closed rather than ignored/reused. A randomized or claim-bearing staging protocol must be checked for aliasing and stale-state rules, not merely for a different filename.
3. Check whether #3612 has been closed by a commit that is actually an ancestor of the examined revision. Do not infer repair from the existence of the three historical side-branch commits.
4. Re-resolve the tar crate from the examined Anneal lockfile. If its version/revision changes, recheck the crate-level security statement, `unpack_in` path normalization/canonicalization, link handling, and directory-application ordering.
5. For high assurance, rerun the #3612 two-download reproducer as an ordinary unprivileged user on at least one Unix filesystem: first serve the wrong-hash archive which leaves a protected directory, then the authentic archive with the pinned digest. A repaired implementation should reject the first archive without allowing its contents to become part of any later successful installation.
