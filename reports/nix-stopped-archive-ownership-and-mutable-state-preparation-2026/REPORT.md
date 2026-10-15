# Stopped Docker archive ownership and bounded Nix mutable-state preparation

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

On the examined stopped container, ordinary stdin-tar `docker cp - CID:/work` preserved requested numeric owners, modes, file bytes, a symlink and an in-archive hardlink. Adding `--archive` instead produced UID/GID 0 for the UID/GID 1000 fixture despite command success: the inspected Engine branch substitutes the container's explicit `Config.User=0:0`. A separate directory-header fixture changed an existing directory's owner 1000→1001→1000 while preserving its children. These are finite fixture observations, not successful Nix preparation.

A root process with every capability dropped then failed an ordinary recursive `du` on the deliberately UID1000/mode0700 fixture. Narrowing acquisition to the required Nix trees allowed a bounded census of 2,339 top-level store entries and acquisition of complete stopped mutable-state backups. Actual Nix ownership preparation, HOME removal, a nonroot Nix probe and a new dependency build never ran. The subject remained stopped at the final recorded inspection.

## Applicability

The exact container, image and source revisions appear in `REPORT.json`. The container had explicit User `0:0`, Entrypoint null, and a pinned coreutils 9.8 `sleep infinity` command. Its inspection records show no mounts, `CapDrop=[ALL]`, no-new-privileges and empty attached networks. HostConfig's `bridge` network-mode string is not by itself evidence of an attached endpoint. Metadata acquisition briefly started this known idle command, invoked pinned utilities as UID0, then stopped it. Runtime execution was AArch64 Linux with Nix 2.34.8; the container's reported storage driver was `overlayfs`. These observations do not generalize to arbitrary configured users, user mappings, engines or filesystems.

Docker CLI reported revision prefix `9d7ad9f`, resolved by the primary GitHub commit API to `9d7ad9ff180b43ae5577d048a7bac1159ce7bacf`; Engine reported `daa0cb7f23594cdbcce5002e370027d3fd36ffd7`. The retained implementation bodies are identified by saved byte counts and SHA256 in [source identities](support/docker-source-identities.json), with immutable upstream coordinates. This is implementation interpretation at reported source identifiers, not proof that either executable was built from those bytes.

The earlier failed offline Jasmin dependency build and sandbox fallback are documented in [the already-published dependency report](../jasmin-offline-dependency-build-sandbox-fallback-and-partial-store-2026/REPORT.md). This report concerns later preparation evidence and proposals; it does not turn that earlier partial build into a completed one.

## Findings

### Successful copy status does not establish requested ownership

Basis: execution + source + derived.

The original smoke test used stdin tar with `docker cp --archive - CID:/work`. Both UID0 and UID1000 copy commands and raw readbacks returned status 0. Both readbacks were byte-identical and all returned fixture members were UID/GID0. Thus command success was insufficient for the intended ownership assertion. Original receipt statuses, input hashes and archive-header projections are preserved under [the smoke evidence](support/nix-archive-ownership-smoke-20261015/put-1000.json); the failed expectation remains part of the record.

The CLI forwards its archive flag as `CopyUIDGID`. The Engine's extraction path chooses `tarCopyOptions` when that flag is set. With an explicit configured user, that function resolves the configured UID/GID and sets `ChownOpts`; here it selected 0:0. The ordinary path uses `defaultTarCopyOptions` with an ID map and no forced `ChownOpts`. The CLI's container-to-stdout branch directly streams the Engine tar response. Those branches explain the observed difference without attributing it to host extraction normalization. The exact repositories, revisions, file paths and symbols are in the source identity manifest.

The corrected trial removed `--archive` and updated only the existing four-member `/work/anneal-ownership-probe-20261015` fixture. [Its result](support/nix-archive-ownership-corrected-fixture-20261015/RESULTS.json) records UID/GID1000 for all members, directory mode0700, regular/hardlink mode0600, symlink mode0777, unchanged seven-byte content, the relative symlink target, and an in-archive hardlink. The historical wrong-UID result was explicitly rejected. This establishes the corrected path for this fixture and configuration only.

The subsequent [directory-header trial](support/nix-directory-header-fixture-20261015/RESULTS.json) used header-only archives on that existing directory and observed owner sequence 1000→1001→1000. Children retained content, owners, modes, symlink and hardlink topology. It did not establish preservation of native inode numbers, ctime, ACLs/xattrs or cross-archive hardlinks, and it did not modify Nix state.

### Capability removal applies to metadata observers too

Basis: execution + derived.

The first metadata acquisition ran a combined `du --bytes --summarize` over `/nix/var/nix`, `/nix/var/log/nix`, `/homeless-shelter` and `/work`. It returned [status 1](support/nix-preparation-metadata-20261015/preparation-tree-sizes.json), with [permission denied](support/nix-preparation-metadata-20261015/preparation-tree-sizes.stderr) naming the fixture. UID0 with cap-drop-ALL lacked the DAC override needed to traverse the UID1000/mode0700 directory. The combined operation did not establish full successful size coverage, and the top-level store census did not run in that failed attempt. The controller preserved failure and stopped the exact container; it did not add capabilities.

The narrowed acquisition omitted unrelated `/work` recursion and [passed](support/nix-preparation-metadata-20261015-v2/RESULTS.json). Its `du` outputs were 10,958,925 apparent bytes for `/nix/var/nix`, 2,817 for `/nix/var/log/nix` and zero for HOME. These are utility-reported apparent tree sizes, not archive sizes or physical disk usage. The top-level store name list and exact-argv stat batches cover 2,339 entries, plus explicitly selected directory metadata. The three observed top-level output locks were root-owned regular mode0600 zero-byte files. Owning the parent directory alone would not allow UID1000 to open those existing files read/write.

The observer transferred names and metadata, not immutable store payloads. Its receipts preserve the pinned utility paths, hashes, exact argument lists, output hashes and statuses. Reads can alter atime and container start/stop alters lifecycle metadata; read-only intent does not imply a byte-for-byte unchanged experiment subject.

### Complete mutable-state archives are distinct from a DB-only snapshot

Basis: execution.

The final acquisition used stopped-container archive readbacks. [The backup summary](support/nix-stopped-state-backups-20261015/RESULTS.json) binds all archive hashes and sizes; per-command receipts and generated header projections retain status and member metadata:

| Source | Members | Tar bytes | Regular payload bytes |
| --- | ---: | ---: | ---: |
| `/nix/var/nix` | 27 | 10,974,720 | 10,958,666 |
| `/nix/var/log/nix` | 6 | 7,680 | 2,817 |
| `/homeless-shelter` | 11 | 6,656 | 0 |
| each of three existing output locks | 1 | 1,536 | 0 |

HOME's eleven members were directories; the three locks were zero-byte files. These archives coherently captured those complete directory trees while stopped. The older DB-only archive cannot substitute for the complete mutable-state tree. Full state/log archives and the prior SQLite payload remain private: this package contains header/hash summaries and receipts, never the payload archives or database. A tar checksum authenticates captured bytes; it does not establish complete native metadata coverage or literal inode restoration.

### Minimal ownership scope remains a source-supported proposal

Basis: source + derived; no successful Nix execution.

At Nix revision `f3f1c3c5b8ad91850e0f7c590cf177f7ab022024`, the inspected normal-build path can skip already-valid outputs, canonicalizes newly built outputs, and requires mutable local-store database/lock state. The proposed finite delta therefore owns the `/nix/store` directory inode, `.links` directory inode if present, exact existing output locks, mutable state/log trees, and assigned client/work directories as UID1000. It leaves registered immutable store objects, sources, derivations and pinned executables root-owned. Automatic optimisation is explicitly disabled (`auto-optimise-store=false`) to avoid the inspected `.links` hardlink path; automatic GC is disabled (`min-free=0`). This does not promise arbitrary GC, repair, rebuild/check or package-specific hardlink behavior.

The [preserved source-only delta](support/proposal/MINIMAL-OWNERSHIP-DELTA.md) supplies pinned source paths and line ranges for local-store initialization, AlreadyValid behavior, canonicalization, optimisation and output locks. Its source identity manifests are retained alongside it. The [two-phase method](support/proposal/stopped-archive-method/METHOD.md) is an unexecuted proposal, including gates still unmet: recursive affected-state inode/link/metadata census; supported ACL/xattr coverage; in-set alias counts compared with native nlink; detection of cross-archive/external hardlinks; invalid residual output/scratch paths; fresh coherent backups reconciled with the census; exact new-path inventory and rollback list. External or unresolved aliases require exclusion or stopping, not silent broadening of ownership changes.

The proposed client HOME/XDG paths move under `/work/nix-client`, while builder HOME stays `/homeless-shelter` and derivation bytes stay fixed. Exactly eleven verified empty HOME directories would be removed deepest first using finite `rmdir`, with `/` remaining root-owned0755. Archive omission does not delete entries. Actual Nix invocation would explicitly use UID:GID1000:1000, no capabilities, no-new-privileges, local store, empty builders/build-users-group and disabled UID allocation. A fresh-output probe must show actual builder startup/registration while reading an unchanged root-owned input; cached success cannot test that path. None of these proposed preparation/removal/probe steps occurred.

## Boundaries

Not examined: real mutable-state ownership conversion, nonroot SQLite/local-store open, fresh-output Nix probe, new dependency build, theorem completion, package-specific hardlink behavior and an inner Nix namespace sandbox. The source-only plans are proposals, not successful experiments. Tiny archive fixtures do not establish those outcomes.

Unknown: complete ACL/xattr/sparse metadata coverage, external or cross-archive hardlink closure, native inode rollback, package-specific immutable-input mutation, and actual overlay copy-up cost. Tar restoration cannot restore inode numbers or ctime and does not remove newly created entries; rollback would require an explicit complete effect list. The bounded top-level census did not recursively hash or copy immutable payloads and cannot prove equality of all cached payload bytes. No physical disk-saving claim follows from a smaller proposed ownership scope or apparent-byte counts.

The final stopped-state inspection is historical evidence for the acquisition endpoint, not a live-state attestation after unrelated later actions. This report introduces no new experiment, cleanup or continuation authorization.

## Evidence

Evidence was acquired on 2026-10-15. Support subdirectories correspond to the six retained execution stages; names are evidence handles, not instructions. Each stage keeps raw command JSON receipts and text outputs, with tar payloads replaced by generated member-header JSON. The projection manifest records each original byte count/hash, public hash and exact transformation. The host Docker executable and home-directory prefixes become `<DOCKER_CLI>` and `<HOST_HOME>/`; container paths and subject identifiers are retained. These projections preserve statuses and arguments but are not identical original receipts. Hash-only source identities avoid republishing upstream source bodies; Docker and Nix source attribution remains with their upstream projects.

[Docker source identities](support/docker-source-identities.json) distinguish immutable source coordinates from saved-body hashes and the possible retrieval-added final newline. [CLI resolution](support/cli-revision-resolution.json) records the primary GitHub response's revision identity without retaining its unrelated commit diff. [Projection manifest](support/projection-manifest.json) binds the public evidence to original local bytes. The package manifest freezes all published package files except itself; its own hash is supplied in the handoff.

## Revalidation

No revalidation experiment was run while preparing this report. For another subject, first inspect the configured user and the implementation branches in the pinned Docker coordinates. The cheapest discriminating execution checks would be the same tiny stdin-tar UID fixture with and without `--archive`, followed by the existing-directory header/child-preservation check; success still establishes only their finite tar-visible properties. Do not substitute copy exit status for raw ownership readback.

A later Nix continuation would need the unmet census, link/metadata and rollback gates above before any mutation, then a real UID1000 local-store open and uncached fresh-output probe. Review the pinned Nix regions if the source changes. Neither those checks nor this report establish full dependency or theorem completion. While paused, the package's receipts, identities and manifests can be reviewed without starting the subject or rerunning research.
