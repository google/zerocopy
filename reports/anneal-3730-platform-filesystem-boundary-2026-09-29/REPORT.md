# Scratch publication semantics on APFS and a cached Linux overlayfs container

## Summary

The host already had Docker/OrbStack and a cached Ubuntu 24.04 image, allowing a bounded second-OS probe without installation, download, or host-volume mount. On the macOS APFS scratch volume and inside an ephemeral Linux overlayfs container, a descriptor opened before same-directory replacement still read the old file, a fresh path read the new file, and a descriptor opened before unlink still read its file after the pathname disappeared. A second process could not acquire a nonblocking exclusive `flock` while held, and could acquire it after release. In each of two retained trials per environment, 300 staged renames under two concurrent readers produced 2,400 sampled reads with **zero missing or partial values**; both old and new values were actually observed.

This extends the earlier APFS-only `.olean` fixture with a Linux VFS observation. It does **not** establish universal atomicity, crash durability, mapped-artifact behavior, Windows/network filesystem semantics, or Anneal/Lake worker correctness. The Linux container ran on OrbStack's overlayfs in a VM ultimately hosted by the same Mac, not on a separately provisioned physical filesystem.

## Applicability

The host was macOS 26.6.2 build 25G83, Darwin 25.6.0 arm64. `df -h` placed the chosen conversation scratch directory on `/dev/disk3s1`, mounted at `/System/Volumes/Data`; targeted `diskutil info /System/Volumes/Data` identified APFS. The host probe created only a uniquely named child directory under `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731`. It removed that child after successful assertions. No backup volume was read, mounted, written, or used as a test target. Only selected data-volume identity lines from `diskutil` were retained; unrelated local snapshot metadata was discarded.

The second environment was Docker through OrbStack. Docker reported `OSType=linux`, `Architecture=aarch64`, storage driver `overlayfs`, kernel `7.0.14-orbstack-00380-ga7e0a2dc9535`. The cached `ubuntu:24.04` manifest digest was `sha256:224a1869083a311ef3f13648a154ba79832fbef6364d31493642ca03082da254`; its selected Linux/amd64 image ID was `sha256:a61567bd31828687156d735ea8eb01ba4e37636e225dd6a48ba94136a70d9d61`. The container reported Ubuntu 24.04.4, `uname -m=x86_64`, and `/tmp` as `overlayfs`; this amd64 userland ran under an arm64-hosted Linux VM. Every `docker run` specified `--pull=never --network=none --rm`, with **no bind mount** and `/tmp` as the disposable test root. The Perl probe was delivered by stdin, not by mounting the host checkout.

The read-only inventory found `docker` and `orbctl` installed; `orbctl list` returned no listed extra VMs. It found no callable `podman`, `colima`, `limactl`/`lima`, `nerdctl`, `container`, QEMU system binaries, or `multipass`. Docker listed two cached images: `ubuntu:24.04` (117 MB in `docker image ls`) and `rust-cmark-gate-b:ubuntu24-amd64` (1.53 GB); only Ubuntu was used. This is an inventory of these executable paths and Docker's currently visible image store, not a scan of all possible disk images or all VM applications. The host scratch volume had about 52 GiB available at inspection; the probe creates only tiny text files.

## Findings

### Open descriptors, replacement and unlink

The same `support/fs_probe.pl` ran under host Perl and container Perl. It wrote `OLD_GENERATION` to `current`, opened a read descriptor, wrote `NEW_GENERATION` to `staged`, and invoked Perl `rename(staged,current)` in the same directory. The old descriptor then read `OLD_GENERATION`, while opening the replaced pathname read `NEW_GENERATION`. It opened a descriptor to the new file, unlinked `current`, and read `NEW_GENERATION` through that descriptor; `-e current` was false. Both environments passed both retained runs. Basis: **execution**.

These observations mean pathname selection and an already-open descriptor can name different generations. An Anneal publication design should therefore keep a complete generation identity with each reader/request rather than infer its imported bytes from the current pathname. That is a **derived** design implication; the probe did not use `.olean`, Lake, `mmap`, or a Lean server. The prior [`APFS sharing report`](../anneal-3730-filesystem-sharing-apfs-v4-30-0-rc2/REPORT.md) supplies a separate resident Lean import/read experiment on this host, but not a Linux Lean import.

### Advisory lock and sampled concurrent rename reads

The parent Perl process held an exclusive nonblocking `flock` on one scratch lock file. A forked child closed its inherited descriptor, opened the lock file independently, and failed to acquire its own nonblocking exclusive lock (`0`); after the parent released, a fresh child acquired it (`1`). This tests one file and local advisory `flock` API on each environment. It does not test POSIX byte-range locks, lock recovery after crash, NFS/SMB lock servers, or whether all Anneal participants honor the lock. Basis: **execution**.

Two independent forked readers each performed 1,200 complete path reads while the parent staged and renamed 300 alternating old/new files over `current`. The bounded observations were:

| Environment | Trial | Old reads | New reads | Missing | Other/partial |
| --- | ---: | ---: | ---: | ---: | ---: |
| macOS/APFS | 1 | 1,519 | 881 | 0 | 0 |
| macOS/APFS | 2 | 1,528 | 872 | 0 | 0 |
| Linux/overlayfs | 1 | 1,981 | 419 | 0 | 0 |
| Linux/overlayfs | 2 | 2,011 | 389 | 0 | 0 |

Every row totals 2,400 reads and saw both generations. The difference in old/new counts reflects scheduling and does not measure relative filesystem performance; the Linux userland was emulated and the loops used short sleeps. The absence of missing/partial values in these 9,600 sampled reads supports only this staged same-directory rename path under these schedules. It does not prove crash persistence, atomicity for all workloads, or coherent publication of multiple files. Basis: **execution**.

### Exact I124 residual

The new evidence covers **one APFS volume and one Linux overlayfs container**, with scratch-only rename, unlink, descriptor and advisory-lock controls. I124 still requires, where those platforms/filesystems enter the supported scope:

- A selected native Linux filesystem (for example ext4 or XFS) and actual generated Lean/Lake artifacts with open or memory-mapped readers, worker restart, and multi-file publication/cleanup.
- Windows/NTFS sharing and replace/delete behavior, including handles opened without delete sharing, plus antivirus/indexer interference if Windows support is chosen.
- Network filesystems only if in scope, with their real client cache, lock, replace, disconnect and recovery behavior.
- Crash/power-loss durability and `fsync`/directory-sync ordering, plus lock-holder crash and stale-lock cleanup, in any production-supported configuration.

No such extra environment/image was available for this no-install/no-pull task; the Docker cached image gives a bounded second-OS control, not a substitute for those cells. The result can be used as an acceptance fixture when those environments are later available: run the same descriptor/rename/lock checks, then run a Lean artifact and full generation reader against the platform's actual storage and interference conditions.

## Boundaries

- The Linux container's overlayfs is inside an OrbStack VM on this Mac. It is neither host APFS nor a separate native ext4/XFS machine; the Docker host architecture is arm64 while the selected cached image is linux/amd64. The reported Linux VFS behavior is meaningful for this container configuration only.
- The replacement involved **one regular file** in one directory. The script did not call `fsync`, simulate a crash, replace a directory tree, publish an artifact family, keep a mapped file open, or run Lean/Lake/Anneal in the container.
- The stress loop is bounded, uses Perl `rename`, and sampled path reads. Zero observed tears/misses is not a proof that all concurrent readers see a linearizable generation or that directory entries are durable.
- The lock test uses cooperative advisory `flock`. It does not prevent processes that ignore the lock from reading or writing. Lock semantics for other APIs or network filesystems are untested.
- The runtime inventory checked executable paths, OrbStack's visible VM list, and Docker's image list. It did not search private VM disk directories or backup volumes. No install, image pull, download, mount of host paths, or backup-volume access was performed.

## Evidence

- Executable probe `support/fs_probe.pl`, SHA-256 `05e619e1fd3c6241070f5b3c421c66d5f84803c66a1e26e8a8623bc2eb98d54a`. It asserts every descriptor, unlink, lock, and sampled-read result, then deletes only its own scratch child. Its Perl `rename` call gives the exact replacement operation instead of relying on `mv` behavior. Basis: **execution**.
- Inventory/runner `support/collect.py`, SHA-256 `22756102867d2153626ae04418205db85dc0dc51346b89d9c87b9ab08d5f2bb5`, and `support/results.json`, SHA-256 `4186a6359bf40ac50e1923102a42331fd6a830f2e68c7c5fcfa57c6dd81b03ae`. The results retain exact `uname`, `sw_vers`, `df`, targeted `diskutil`, Docker info/image-inspection, OrbStack list, container OS/filesystem commands, four probe command lines, outputs and exits. `$SCRATCH` and `$PROBE` replace local absolute paths; the full `diskutil` text was reduced to relevant volume identity lines and its raw-output hash. Basis: **execution**.
- The existing [`APFS sharing report`](../anneal-3730-filesystem-sharing-apfs-v4-30-0-rc2/REPORT.md) examined a Lake-built `.olean`, path aliases, APFS clone/copy, resident Lean imports and unlink/replace. It is a different artifact-level fixture; this report does not rerun it.
- [Issue #3731](https://github.com/google/zerocopy/issues/3731) I124 requests platform-specific rename, locking and open-file checks. Its Windows and network cases are conditional, and this report does not mark them executed.

## Revalidation

From this package, set `ANNEAL_PROBE_SCRATCH` to an existing owned directory on the target host and run `python3 support/collect.py`. It performs read-only inventory, two host Perl trials, and two cached-image Linux trials using `docker run --pull=never --network=none --rm` without host mounts. Compare the descriptor strings, lock outcomes, both-generation read counts, zero missing/partial reads, and cleanup marker with `support/results.json`; exact old/new counts will vary with scheduling. Inspect `diskutil`/`df` and `stat -f -c %T /tmp` again before applying this result to a changed volume or Docker storage driver. On a new supported platform, run the same scratch-only probe there and add an actual generated-artifact/mapped-reader publication matrix before generalizing Anneal's cleanup policy.
