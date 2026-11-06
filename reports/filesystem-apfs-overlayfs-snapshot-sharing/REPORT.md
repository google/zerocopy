# Filesystem Sharing, Coherent Tree Capture, Path Aliasing, and Reader Lifetimes on APFS and Linux OverlayFS

## Summary

Sharing compiled Lean artifacts (`.olean`, `.ilean`) and capturing multi-file workspace snapshots across macOS APFS and Linux container `overlayfs` environments require distinguishing path aliases from copy-on-write clones, pinning immutable generation roots during multi-file capture, and separating open/mapped reader lifetimes from pathname replacement. Across five empirical packages tested on macOS arm64 APFS (`Darwin 25.6.0`) with Lean/Lake `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and inside an isolated Ubuntu `24.04` `overlayfs` container (`sha256:224a1869083a311ef3f13648a154ba79832fbef6364d31493642ca03082da254`):

1. **Sharing isolation vs. mutable path/inode aliasing (`support/filesystem-sharing-apfs-v4-30-0-rc2/`):** When sharing a Lake-built `4,608`-byte `Dep.olean` (`depValue : Nat := 7`, SHA-256 `5a4030a600a43d13aa4b111bb81daae47c22636143a273da5e07dedc5916032f`), consumer writes through a **symlink** or **hardlink** to a writable producer file overwrite the producer's `.olean` in place (`19d2d9c8...`), breaking subsequent fresh Lean imports. Conversely, an APFS copy-on-write clone (`/bin/cp -c`) or an ordinary full copy allocates a distinct inode so consumer writes corrupt only the consumer's alias while leaving the producer's `.olean` intact. Setting mode `0444` on a directly shared producer file blocks unprivileged in-place writes (`PermissionError`, `errno 13`) while permitting Lean reads, though it does not prevent directory-level unlink/replace or `chmod` by the file owner.
2. **Divergent storage accounting across APFS and `overlayfs` (`support/apfs-overlayfs-resource-accounting/`):** Across an `11`-file (`2,147,019` logical bytes, `2,158,592` `st_blocks * 512` bytes) proof workspace fixture containing real `Dep.olean` and `Plugin.olean` artifacts plus eight `256 KiB` incompressible blobs, both `/bin/cp -c` on APFS and `cp -a --reflink=always` on container `overlayfs` succeeded (`exit 0`) and isolated the base tree from a `4 KiB` clone overwrite. However, per-file `st_blocks * 512` sums increased by a full tree (`+2,158,592 B`) on both filesystems after cloning; APFS `statvfs` volume-free delta charged only `8,192 B` (`8 KiB`) for the clone (`+16,384 B` after the `4 KiB` write), whereas GNU `du -B1` and Docker writable-layer `SizeRw` on `overlayfs` charged the full `2,158,592 B` at clone time and `0 B` on the subsequent `4 KiB` write. Adding a read-only hardlink to `Dep.olean` (`4,552 B` logical, `8,192 B` blocks) inflated path-summed bytes without changing APFS volume-free space or Docker `SizeRw`.
3. **Coherent multi-file tree capture under concurrent mutations (`support/large-tree-coherent-capture/`):** Capturing a `291`-entry workspace (`256` `4 KiB` source files, `32` `4 KiB` generated outputs, `2` target files, and `1` relative symlink) while a concurrent writer switches the `current` generation symlink from `A` to `B` after `128` file reads produced a torn, unattributable inventory when `current` was re-resolved per file (`src/200.dat` missing after rename to `src/200-renamed.dat`, combined with `A`'s first `128` files and `B`'s `generated/010.bin` and retargeted symlink). Resolving `current` once to immutable directory `A` captured the exact `A` manifest (`c0c9132e1a83...`) despite concurrent live edits; however, mutating `src/220.dat` inside `A` during the walk broke the manifest hash check, confirming that single-point resolution requires an immutable backing directory plus post-read manifest verification.
4. **Cross-platform path aliasing, atomic rename, and open/mapped reader lifetimes (`support/platform-filesystem-boundary/`, `support/real-lean-filesystem-lifetimes/`):** On both APFS and Linux `overlayfs`, file descriptors and read-only `mmap` regions opened on `Dep.olean` (generation `7`, `4,552 B`, SHA-256 `7ae55077...`) before same-directory `rename` replacement (with generation `9`, `4,456 B`, SHA-256 `0f0fbd52...`) and subsequent `unlink` continued to read generation `7` bytes without error, and a resident `lean --json` process that had already imported `Dep` evaluated `7` after pathname replacement or deletion. Fresh `lean --json` processes resolved the new pathname to generation `9` after rename and failed with `unknown module prefix 'Dep'` while unlinked. In a `300`-rename stress loop with two concurrent forked readers (`2,400` reads/trial $\times$ `2` trials/OS = `9,600` total reads), zero missing or torn values occurred on either APFS or `overlayfs`. Case-folded (`Case` vs. `case`) and Unicode-normalized (NFC `é` vs. NFD `e\u0301`) `LEAN_PATH` directory names aliased the same inode on default case-insensitive APFS (`case=1 unicode=1`) and served fresh Lean imports interchangeably, whereas `overlayfs` treated them as distinct directories (`case=0 unicode=0`).

## Applicability

The empirical findings apply to:
- **Lean 4 and Lake (`leanprover/lean4`):** revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`, running on macOS `26.6.2` (`Darwin 25.6.0` arm64) over an APFS Data volume (`/System/Volumes/Data`).
- **Linux `overlayfs` container environment:** `ubuntu:24.04` image digest `sha256:224a1869083a311ef3f13648a154ba79832fbef6364d31493642ca03082da254` (selected `linux/amd64` image ID `sha256:a61567bd31828687156d735ea8eb01ba4e37636e225dd6a48ba94136a70d9d61`) running under OrbStack (`kernel 7.0.14-orbstack-00380-ga7e0a2dc9535`, storage driver `overlayfs`) with `--pull=never --network=none --memory=512m --cpus=1` and the container's disposable `overlayfs` scratch directory.

## Findings

### 1. APFS Sharing Isolation vs. Symlink and Hardlink Aliasing (`support/filesystem-sharing-apfs-v4-30-0-rc2/`)

[`support/filesystem-sharing-apfs-v4-30-0-rc2/probe.py`](support/filesystem-sharing-apfs-v4-30-0-rc2/probe.py) built a `4,608`-byte `Dep.olean` (`def depValue : Nat := 7`, SHA-256 `5a4030a600a43d13aa4b111bb81daae47c22636143a273da5e07dedc5916032f`), verified that a direct Lean consumer imported `depValue = 7` across five sharing modes, and then opened the consumer-visible path with `r+b` to overwrite byte `0` (`fsync`):

| Sharing Mode | Pre-Write Inventory (Producer / Alias) | Consumer In-Place Write Result | Producer `Dep.olean` After Consumer Write | Fresh Lean Consumer Read After Write |
| --- | --- | --- | --- | --- |
| Direct producer file (`0444`) | `1` file (`4,608 B` logical, `8,192 B` `st_blocks`) / no alias | `PermissionError` (`errno 13`) | Unchanged (`5a4030a6...`) | Succeeds (`7`) |
| Symlink to writable producer | `1` file (`4,608 B`) / `1` symlink (`0 B` blocks) | Succeeded | **Corrupted** (`19d2d9c8...`) | Fails (`exit 1` on both producer and alias) |
| Hardlink to writable producer | `1` file (`4,608 B`) / `1` file (`4,608 B`), shared inode (`nlink = 2`) | Succeeded | **Corrupted** (`19d2d9c8...`) | Fails (`exit 1` on both producer and alias) |
| APFS clone (`/bin/cp -c`) | `1` file (`4,608 B`) / `1` file (`4,608 B`), distinct inodes | Succeeded | **Unchanged** (`5a4030a6...`) | Producer succeeds (`7`); corrupted clone fails (`exit 1`) |
| Ordinary full copy | `1` file (`4,608 B`) / `1` file (`4,608 B`), distinct inodes | Succeeded | **Unchanged** (`5a4030a6...`) | Producer succeeds (`7`); corrupted copy fails (`exit 1`) |

**Basis: execution** in [`support/filesystem-sharing-apfs-v4-30-0-rc2/raw.json`](support/filesystem-sharing-apfs-v4-30-0-rc2/raw.json). Neither symlinks nor hardlinks isolate a shared producer `.olean` from a consumer that opens its target path for in-place mutation; only distinct-inode copies (`/bin/cp -c` clones or full copies) or read-only permissions (when consumers do not `chmod` or `unlink` the shared file) preserve producer bytes.

### 2. APFS vs. Linux `overlayfs` Clone, Reflink, and Hardlink Resource Accounting (`support/apfs-overlayfs-resource-accounting/`)

[`support/apfs-overlayfs-resource-accounting/probe.py`](support/apfs-overlayfs-resource-accounting/probe.py) constructed an `11`-file base workspace (`2,147,019` logical bytes, `2,158,592` `st_blocks * 512` bytes: `Dep.olean`, `Plugin.olean`, `Proof.lean`, and eight `256 KiB` incompressible blobs) on macOS APFS and inside the Ubuntu `24.04` `overlayfs` container, then sequentially added a full copy, a clone/reflink copy (`/bin/cp -c` on APFS; `cp -a --reflink=always` on `overlayfs`), a read-only hardlink to `Dep.olean` (`4,552` logical bytes, `8,192` block bytes), and a `4 KiB` in-place write to one cloned blob:

| Workspace Phase | Cumulative Logical Bytes | Summed `st_blocks * 512` (APFS or `overlayfs`) | APFS `statvfs` Volume-Free Delta | Docker `overlayfs` `SizeRw` Delta |
| --- | ---: | ---: | ---: | ---: |
| 1. Base tree (`11` files) | `2,147,019 B` | `2,158,592 B` | `2,162,688 B` | `2,158,592 B` |
| 2. Full copy added (`22` files) | `4,294,038 B` | `4,317,184 B` | `2,162,688 B` | `2,158,592 B` |
| 3. Clone / `--reflink=always` added (`33` files) | `6,441,057 B` | `6,475,776 B` | **`8,192 B`** | **`2,158,592 B`** |
| 4. `Dep.olean` hardlink added (`34` paths) | `6,445,609 B` | `6,483,968 B` | `0 B` | `0 B` |
| 5. `4 KiB` write to cloned blob | `6,445,609 B` | `6,483,968 B` | `16,384 B` | `0 B` |

- On **APFS**, per-file `st_blocks` charged a full `2,158,592 B` for the `/bin/cp -c` clone even though volume-free bytes dropped by only `8,192 B` (`8 KiB`) on clone creation and `16,384 B` (`16 KiB`) after dirtying `4 KiB`.
- On **container `overlayfs`**, `cp -a --reflink=always` succeeded (`exit 0`) and isolated the base blob from the `4 KiB` mutation, but `st_blocks`, GNU `du -B1`, and Docker `inspect --size` (`SizeRw`) all charged a full `2,158,592 B` at reflink creation and `0 B` on the subsequent `4 KiB` mutation.
- On **both filesystems**, summing `st_blocks` across directory paths double-counted the `8,192 B` hardlinked `Dep.olean` inode (`nlink = 2`), which consumed `0 B` of additional volume or layer space.

### 3. Coherent Multi-File Capture Under Concurrent Edits (`support/large-tree-coherent-capture/`)

[`support/large-tree-coherent-capture/probe.py`](support/large-tree-coherent-capture/probe.py) tested three capture strategies across a `291`-entry tree (`256` `4 KiB` source files `src/000.dat`..`src/255.dat`, `32` `4 KiB` generated outputs `generated/000.bin`..`generated/031.bin`, `targets/alpha`, `targets/beta`, and relative symlink `link`) while a concurrent writer thread paused after `128` reader file opens, modified `src/128.dat`..`src/255.dat`, renamed `src/200.dat` $\rightarrow$ `src/200-renamed.dat`, updated `generated/010.bin`, retargeted `link` from `targets/alpha` to `targets/beta`, and atomically flipped `current` from generation `A` to `B`:

| Capture Strategy | Observed Inventory & Manifest Outcome | Technical Cause |
| --- | --- | --- |
| Re-resolve `current` symlink on every file open | **Torn / Mixed (matches neither `A` nor `B`):** `src/200.dat` missing; `src/000..127.dat` from `A`; `generated/010.bin` and `link -> targets/beta` from `B` | Resolving `current` per file crossed the atomic pointer swap mid-walk. |
| Resolve `current` once to immutable directory `A` | **Coherent `A` snapshot:** all `291` entries captured with exact `A` manifest digest `c0c9132e1a83...` | Opening relative to the pinned immutable `A` root isolated the reader from the `current -> B` swap and live-tree mutations. |
| Resolve `current` once to `A`, but mutate `A/src/220.dat` mid-walk | **Detected violation:** manifest digest matched neither `A` nor `B` (`src/220.dat` hash mismatch) | Pinning a directory path does not prevent in-place mutation if the backing directory remains writable; post-capture manifest verification caught the write. |

### 4. Path Aliasing, Atomic Rename, Advisory Locks, and Open/Mapped Reader Lifetimes (`support/platform-filesystem-boundary/`, `support/real-lean-filesystem-lifetimes/`)

Two cross-platform probes tested file replacement, locking, path aliases, and compiled `.olean` reader lifetimes on macOS APFS and Ubuntu `24.04` `overlayfs`:

1. **Descriptor/mmap persistence, advisory `flock`, and `300`-rename stress (`support/platform-filesystem-boundary/`):** Running [`support/platform-filesystem-boundary/fs_probe.pl`](support/platform-filesystem-boundary/fs_probe.pl) twice on APFS and twice in container `overlayfs`:
   - A file descriptor opened to `current` (`OLD_GENERATION`) before same-directory `rename(staged, current)` continued reading `OLD_GENERATION` while fresh opens of `current` read `NEW_GENERATION`; a descriptor opened to `NEW_GENERATION` before `unlink(current)` continued reading `NEW_GENERATION` after the pathname disappeared.
   - An exclusive nonblocking `flock` held by the parent process blocked an independent child open from acquiring `flock` (`0`) until the parent released the descriptor (`1`).
   - Across `300` alternating staged same-directory renames with `2` concurrent forked readers (`2,400` complete file reads per trial), all four trials observed both generations (`1,519/881` and `1,528/872` old/new on APFS; `1,981/419` and `2,011/389` on `overlayfs`) with **zero missing (`ENOENT`) or torn/partial reads**.
2. **Real compiled `.olean` and macro-plugin reader lifetimes (`support/real-lean-filesystem-lifetimes/`):** [`support/real-lean-filesystem-lifetimes/probe.py`](support/real-lean-filesystem-lifetimes/probe.py) compiled `Dep7.olean` (`4,552 B`, `depValue = 7`, SHA-256 `7ae5507721d0d228cfdb0c2399d6ef858bc918e48376470954b3600e40862cb3`), `Dep9.olean` (`4,456 B`, `depValue = 9`, SHA-256 `0f0fbd523ef1ce3fce88465a688f7a786beb38969ff690b97c51778d5da30ec0`), and `Plugin.olean` (`45,272 B` macro tactic `probe_decide`, SHA-256 `24d1cf9fcaa36b2d918eb2985e5137958e7f4393bfbf768966a2084bbc`):
   - **APFS `LEAN_PATH` alias resolution:** Fresh `lean --json` processes imported `Dep` and `Plugin` and proved `depValue = 7` via `probe_decide` across relative `LEAN_PATH=live`, directory symlink, hardlink directory, case-folded (`Case` vs. `case`), and Unicode-normalized (NFC `é` vs. NFD `e\u0301`) roots. On APFS, `Case`/`case` and NFC/NFD resolved to the identical directory (`case=1 unicode=1`), whereas on Linux `overlayfs` they created separate directories (`case=0 unicode=0`).
   - **Live Lean import, open fd, and read-only `mmap` across replacement and unlink:** On APFS, after same-directory `rename` replaced `live/Dep.olean` (inode `24422673`, generation `7`) with generation `9` (inode `24422690`) and after subsequent `unlink`, a resident `lean --json` process that had already imported `Dep` still evaluated `7` (`exit 0`), and both an open file descriptor and a read-only `mmap` (`support/real-lean-filesystem-lifetimes/host_reader.py`) continued yielding the exact generation-7 SHA-256 (`7ae55077...`). Meanwhile, fresh `lean --json` processes proved `depValue = 9` after rename, failed (`unknown module prefix 'Dep'`) while `live/Dep.olean` was unlinked, and proved `7` when pointed at the retained hardlink to old inode `24422673`.
   - **Linux `overlayfs` `mmap` and round-trip verification:** Inside the `overlayfs` container (`support/real-lean-filesystem-lifetimes/overlay_reader.pl`, reading `mmap` pages via `/proc/self/mem`), open descriptors and read-only `mmap` mappings of `Dep7.olean` retained generation-7 bytes (`7ae55077...`) across both same-directory rename to `Dep9.olean` and `unlink`. Copying the replaced `overlayfs` pathname, old hardlink, and `Plugin.olean` back to APFS preserved all SHA-256 digests and passed fresh host `lean --json` proof checks for both generation `9` and generation `7`.

## Boundaries

- **OrbStack VM `overlayfs` vs. bare-metal Linux filesystems:** The Linux container observations executed on `overlayfs` inside an arm64-hosted OrbStack Linux VM (`linux/amd64` container userland), not on a bare-metal `ext4`, `XFS`, or `btrfs` volume. Moreover, Lean was not installed inside the container, so `overlayfs` reader tests operated on genuine `.olean` bytes via Perl `mmap`/fd probes and round-trip host Lean checks rather than invoking a Linux `lean` binary inside the container.
- **Macro `.olean` vs. native `.dylib`/`.so` `dlopen` lifetimes:** `Plugin.olean` is a compiled Lean macro extension loaded through `LEAN_PATH`, not a native shared library loaded via `dlopen` (`--load-dynlib` / `precompileModules`).
- **No crash-durability or Windows/network-filesystem coverage:** The staged rename loops tested live process concurrency without `fsync` crash/power-loss injection, Windows NTFS delete-sharing semantics (`FILE_SHARE_DELETE`), or NFS/SMB attribute-cache behavior.

## Evidence

- **APFS `.olean` sharing and mutation isolation (`support/filesystem-sharing-apfs-v4-30-0-rc2/`):** [`support/filesystem-sharing-apfs-v4-30-0-rc2/probe.py`](support/filesystem-sharing-apfs-v4-30-0-rc2/probe.py) (SHA-256 `0a6de307f62e5334171360eaac343afcdae6ad58761ed02a9419f7fc9739d40b`) and [`support/filesystem-sharing-apfs-v4-30-0-rc2/raw.json`](support/filesystem-sharing-apfs-v4-30-0-rc2/raw.json) (SHA-256 `f487d10afd24d1f41e19c4637778ef95134ca75153925b8e905de52e897fa795`).
- **APFS vs. `overlayfs` clone/reflink/hardlink accounting (`support/apfs-overlayfs-resource-accounting/`):** [`support/apfs-overlayfs-resource-accounting/probe.py`](support/apfs-overlayfs-resource-accounting/probe.py), [`support/apfs-overlayfs-resource-accounting/verify.py`](support/apfs-overlayfs-resource-accounting/verify.py), [`support/apfs-overlayfs-resource-accounting/results.json`](support/apfs-overlayfs-resource-accounting/results.json), and fixture artifacts under [`support/apfs-overlayfs-resource-accounting/fixture/`](support/apfs-overlayfs-resource-accounting/fixture/).
- **Coherent multi-file tree capture (`support/large-tree-coherent-capture/`):** [`support/large-tree-coherent-capture/probe.py`](support/large-tree-coherent-capture/probe.py) (SHA-256 `fd362b30590020adbcf5cddcbd469bae78c346180d790cb17be5953ed3fa159c`), [`support/large-tree-coherent-capture/check.py`](support/large-tree-coherent-capture/check.py), and [`support/large-tree-coherent-capture/results.json`](support/large-tree-coherent-capture/results.json) (SHA-256 `8ac2a81b4190b5a1a4bcd8fa1595530a41d0fdf5776e257525317d4b5d470218`).
- **Cross-platform rename, lock, and `.olean` reader lifetimes (`support/platform-filesystem-boundary/`, `support/real-lean-filesystem-lifetimes/`):**
  - [`support/platform-filesystem-boundary/fs_probe.pl`](support/platform-filesystem-boundary/fs_probe.pl), [`support/platform-filesystem-boundary/collect.py`](support/platform-filesystem-boundary/collect.py), and [`support/platform-filesystem-boundary/results.json`](support/platform-filesystem-boundary/results.json).
  - [`support/real-lean-filesystem-lifetimes/probe.py`](support/real-lean-filesystem-lifetimes/probe.py), [`support/real-lean-filesystem-lifetimes/host_reader.py`](support/real-lean-filesystem-lifetimes/host_reader.py), [`support/real-lean-filesystem-lifetimes/overlay_reader.pl`](support/real-lean-filesystem-lifetimes/overlay_reader.pl), [`support/real-lean-filesystem-lifetimes/results.json`](support/real-lean-filesystem-lifetimes/results.json), and [`support/real-lean-filesystem-lifetimes/artifacts/`](support/real-lean-filesystem-lifetimes/artifacts/).

## Revalidation

To verify the retained offline results and ledger invariants:

```sh
python3 support/apfs-overlayfs-resource-accounting/verify.py
python3 support/large-tree-coherent-capture/check.py
```

To re-execute the live filesystem probes on an APFS host with Lean `v4.30.0-rc2` and the cached `ubuntu:24.04` Docker image available:

```sh
python3 support/filesystem-sharing-apfs-v4-30-0-rc2/probe.py
python3 support/apfs-overlayfs-resource-accounting/probe.py --work /path/to/new/apfs/scratch
ANNEAL_PROBE_SCRATCH=/path/to/existing/scratch python3 support/large-tree-coherent-capture/probe.py
ANNEAL_PROBE_SCRATCH=/path/to/existing/scratch python3 support/platform-filesystem-boundary/collect.py
python3 support/real-lean-filesystem-lifetimes/probe.py --work /path/to/new/apfs/scratch
```
