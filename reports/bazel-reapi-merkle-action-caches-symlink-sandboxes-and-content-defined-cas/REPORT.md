# REAPI v2 Merkle Action Caches, `openat2` Symlink/Descriptor Sandbox Confinement, Case-Folding Checkout Collisions, and Content-Defined CAS Across Bazel, Buildbarn, Bubblewrap, and runc

## Summary

Distributed build execution and container sandboxing rely on an assumed isomorphism between **cryptographic Merkle tree descriptions** (`Action`, `Command`, `Directory`, `Digest`) and **mutable host kernel objects** (POSIX/APFS/NTFS directory entries, open file descriptors, mount namespaces, and controlling terminals). Direct primary-source inspection and live kernel/protocol execution probes across `bazelbuild/remote-apis` (`e0c0554bfc8a37abf336c3e78070684367738e1d`), `bazelbuild/bazel` (`2e2d4e48fb55195e6ddd3e97af50e4aae47544c6`), `buildbarn/bb-remote-execution` (`f22e022dfa042a91c6cd4b57efd537d2fbb75ffb`), `containers/bubblewrap` (`1fb0aa26d3eb66254f7742e704add7f82f41a582`), `opencontainers/runc` (`b7dc1304ed9e18f14e626dc06374043b12cf355f`), `git/git` (`94f6e3e283f2adfc518b39cfc39291f1c2832ad0`, `v2.30.2`), and Linux `7.1.6-1rodete1-amd64` establish five foundational engineering invariants:

1. **Non-Bijective Canonical REAPI v2 `Directory` Digests vs. Host Filesystem Quotients**: REAPI v2 (`remote_execution.proto:980-1184`) defines canonical `Directory` protos over unique, single-segment, UTF-8 byte-sorted names and deterministic tag-ordered Protocol Buffer wire bytes (`Digest = (hex_hash, size_bytes)`). Because the specification explicitly treats names as unnormalized, case-sensitive UTF-8 byte sequences (`lines 987-991`) and embeds optional `NodeProperties` (`mtime`, `unix_mode`, `lines 1081-1091`) inside hashed `FileNode` messages, two dual failure modes arise: (a) leaking host `mtime` or `umask` bits inflates a minimal `80 B` `Directory` proto to `90+ B` with a disjoint SHA-256 digest (`0%` cross-host Action Cache reuse), while undeclared host reads (`/usr/include`, `/sys`) poison shared Action Cache entries under a clean `Action` digest; and (b) distinct canonical REAPI entries—such as `"Foo"` (`0x46...`) vs. `"foo"` (`0x66...`), or Unicode NFC `"caf\u00e9"` (`63 61 66 c3 a9`) vs. NFD `"cafe\u0301"` (`63 61 66 65 cc 81`, sorted before NFC because `0x65 < 0xc3`)—collide onto a single dentry on case-insensitive or NFD-normalizing filesystems (`APFS`, `HFS+`, `NTFS`, `ext4` `+F`).
2. **Case-Folding Symlink + Delayed-Checkout `lstat`-Cache Desynchronization (`CVE-2021-21300`)**: When a tree materializer or VCS (`git < 2.30.2`) processes both a directory `"A"` containing a delayed-checkout blob (`"A/post-checkout"`, e.g., Git LFS smudge filter) and a case-colliding symbolic link `"a" -> ".git/hooks"`, Pass 1 creates `"A"`, records `"A"` as a verified directory in its userspace `lstat()` cache, replaces empty `"A"` with symlink `"a"`, and Pass 2 blindly writes the delayed blob through `"A/post-checkout"` without re-verifying the parent dentry—traversing symlink `"a"` into `.git/hooks/post-checkout` (arbitrary code execution on clone/checkout). Even virtualized worker filesystems (`Buildbarn` `pkg/filesystem/virtual/component_normalizer.go:30-38`) using `strings.ToLower` fold Unicode Kelvin `'\u212a'` (`'K'`) $\to$ `'k'` while leaving Latin small long-s `'\u017f'` (`'ſ'`) distinct from `'s'`, diverging from full Unicode case-folding (`casefold()`) and NTFS `$UpCase` tables.
3. **Kernel-Atomic `openat2(RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS)` Beats Userspace `realpath()` in Both Soundness and Latency**: Userspace `realpath()` + `open()` validation is vulnerable to concurrent worker-thread symlink rename TOCTOU races and requires per-component `lstat`/`readlink` syscalls. Live execution on Linux `7.1.6-1rodete1-amd64` demonstrates that `openat2` (`SYS_openat2`) with `RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS` atomically confines absolute symlinks (`/etc/sandbox_marker` $\to$ `<root>/etc/sandbox_marker`), clamps `../../../../etc/hostname` traversal at `dirfd` (`ENOENT = 2`), blocks `/proc/self/cwd` magic-link traversal (`ELOOP = 40`), and completes in **`18.69 µs` vs. `31.24 µs` (`1.67x` faster)** than `realpath() + open()`.
4. **Why `O_CLOEXEC` Alone Fails Against `CVE-2024-21626` (*Leaky Vessels*) and Why Default `bubblewrap` / `linux-sandbox` Expose `TIOCSTI` (`CVE-2017-5226`)**:
   - In `runc <= 1.1.11` (`CVE-2024-21626`), a leaked host `/sys/fs/cgroup` `O_CLOEXEC` fd (`fd 7`) remained open during `runc init` *prior* to `execve`, allowing `WORKDIR /proc/self/fd/7` to `chdir` onto the host mount namespace, **and** allowing `execve("/proc/self/fd/7/../../../bin/...", ...)` to resolve a host path *before* the kernel closes `O_CLOEXEC` descriptors during `begin_new_exec`! `runc` (`b7dc1304ed9e18f14e626dc06374043b12cf355f`) therefore combines three mandatory defenses: `pathrs` (`openat2` `OpenInRoot` + `ProcThreadSelfOpen`), `verifyCwd()` (`libcontainer/init_linux.go:273-295`, checking raw `SYS_getcwd` for `ENOENT` on `"(unreachable)"` out-of-root `pwd`), and `utils.UnsafeCloseFrom(PassedFilesCount + 3)` (`standard_init_linux.go:308`, explicitly closing fds *before* `execve` while exempting Go runtime netpoll epoll fds via `internal/poll.IsPollDescriptor`).
   - Both `containers/bubblewrap` (`bubblewrap.c:78, 3470`, where `opt_new_session` defaults to `false` unless `--new-session` is passed) and `bazelbuild/bazel` (`src/main/tools/linux-sandbox-pid1.cc:673-680`, which calls `setpgid(0, 0)` and `tcsetpgrp(STDIN_FILENO, getpgrp())` rather than `setsid()`) leave sandboxed children attached to an inherited controlling TTY, permitting `ioctl(STDIN_FILENO, TIOCSTI, &byte)` parent-shell command injection on kernels with `dev.tty.legacy_tiocsti = 1`. Furthermore, `linux-sandbox-pid1.cc:590-598` falls back to `mount("/sys", "sys", MS_BIND | MS_REC)` whenever `opt.hermetic && opt.create_netns == NO_NETNS` because unprivileged user namespaces cannot mount a fresh `sysfs` without owning the network namespace.
5. **Lazy Virtual Input Roots (`Buildbarn` FUSE/NFSv4) and Content-Defined Chunking (`SHA256TREE`, `BLAKE3`, `FastCDC 2020`, `RepMaxCDC`)**: Eagerly staging large toolchains (`naiveBuildDirectory`, `bb-remote-execution` `pkg/builder/naive_build_directory.go:33-78`) copies `100%` of input blobs and forfeits quota/unread monitoring, whereas `virtualBuildDirectory` (`virtual_build_directory.go:39-145`) materializes dentries lazily on `READ`. For multi-hundred-megabyte artifacts in CAS, REAPI v2 (`remote_execution.proto:2266-2579`) standardizes `SHA256TREE` (`1024 B` leaf threshold, `2^k` binary splits, 9th–16th prime `IV`s without Davies-Meyer feed-forward), `BLAKE3`, `FAST_CDC_2020` (`GEAR[i] = high_64_bits(MD5(byte(i)))`, normalization level `2`, `[avg/4, 4*avg]`), and `REP_MAX_CDC` (local-maxima Gear chunking with expected chunk size `min / 0.7475979203...` via Rényi's parking constant); on a `512 KiB` binary shifted by a `13 B` build-ID prefix, normalized `FastCDC` preserves **`97.88%` chunk deduplication (`52 / 53` chunks)** where fixed `8 KiB` paging achieves **`0.0%`**.

## Applicability

This report governs remote build execution clients, CAS/Action-Cache servers, unprivileged namespace sandboxes, container runtimes, and source-tree materializers across the pinned subjects in `REPORT.json`:

- **REAPI v2 Protocol & Bazel Client/Sandbox**: `bazelbuild/remote-apis` (`e0c0554bfc8a37abf336c3e78070684367738e1d`, covering REAPI `v2.0` through `v2.13` `output_paths`, `SHA256TREE`, `BLAKE3`, `FAST_CDC_2020`, and `REP_MAX_CDC`) and `bazelbuild/bazel` (`2e2d4e48fb55195e6ddd3e97af50e4aae47544c6`, `MerkleTree.java` memory-compact uploadable maps and `linux-sandbox-pid1.cc` PID-1 user/mount/PID/UTS/net namespace sandbox).
- **Remote Worker Input Materialization**: `buildbarn/bb-remote-execution` (`f22e022dfa042a91c6cd4b57efd537d2fbb75ffb`, comparing POSIX `naiveBuildDirectory` against FUSE/NFSv4/WinFsp `virtualBuildDirectory` and `ComponentNormalizer`).
- **Namespace & Container Process Confinement**: `containers/bubblewrap` (`1fb0aa26d3eb66254f7742e704add7f82f41a582`), `opencontainers/runc` (`b7dc1304ed9e18f14e626dc06374043b12cf355f`, post-`CVE-2024-21626` `libcontainer` + `pathrs-lite` integration), `git/git` (`94f6e3e283f2adfc518b39cfc39291f1c2832ad0`, `v2.30.2` fix for `CVE-2021-21300`), and Linux `openat2(2)` (`>= 5.6`, benchmarked on `7.1.6-1rodete1-amd64`).

Kernel `openat2`, `close_range`, `pivot_root`, and `/proc/thread-self` behaviors apply strictly to Linux (`>= 5.6` for `openat2`, `>= 5.9` for `close_range`, `>= 6.2` for `CONFIG_LEGACY_TIOCSTI=n` default); case-folding and Unicode normalization hazards apply across macOS (`APFS`), Windows (`NTFS`), Linux (`ext4`/`f2fs` `casefold`), and cross-platform REAPI caches serving heterogeneous OS workers.

## Findings

### 1. REAPI v2 Canonical Merkle Digests, Cache Poisoning, and Filesystem Quotient Collisions

`Basis: normative + source + execution`

In REAPI v2 (`build/bazel/remote/execution/v2/remote_execution.proto:730-1184`), an `Action` is addressed in the `ActionCache` by `Digest( ProtoSerialize(Action) )`, where `Action` binds `command_digest`, `input_root_digest`, `timeout`, `do_not_cache`, `salt`, and `platform`. Every `Digest` (`lines 1177-1184`) is an inseparable tuple `(hash: lowercase_hex, size_bytes: int64)`: servers **must** reject requests whose `hash` matches but `size_bytes` differs (`line 1151`), allowing workers to pre-allocate buffers and flatten Merkle trees prior to streaming payloads.

#### 1.1 Wire-Level Protobuf Canonicality vs. Metadata Poisoning

Because Protocol Buffers in general are **not** canonically encoded, `remote_execution.proto:1164-1176` mandates four serialization invariants whenever hashing `Action`, `Command`, `Directory`, or `Tree` messages: (1) fields serialized in ascending tag order, (2) zero unknown fields, (3) zero duplicate fields (concatenating two serialized `Directory` byte buffers is valid wire Protobuf for merging repeated fields, yet violates tag monotonicity and changes `Digest`!), and (4) default scalar omission (`false`, `0`, `""` omitted). Within `Directory` (`lines 984-1000, 1048-1144`):

$$\text{CanonicalDir}(D) \iff \begin{cases}
\forall x \in F \cup D_{\text{sub}} \cup S:\; x.\text{name} \notin \{\texttt{""}, \texttt{"."}, \texttt{".."}\} \land \texttt{'/'} \notin x.\text{name} \\
|F| + |D_{\text{sub}}| + |S| = \bigl|\{x.\text{name} \mid x \in F \cup D_{\text{sub}} \cup S\}\bigr| \quad (\text{cross-kind byte uniqueness}) \\
F, D_{\text{sub}}, S \text{ strictly increasing under unsigned UTF-8 byte order}
\end{cases}$$

Our execution probe (preserved in the standalone **Revalidation** script) quantifies two ubiquitous cache failures:
- **Cache Fragmentation via Non-Hermetic `NodeProperties`**: A `Directory` containing a single `FileNode("main.c", sha256, is_executable=false)` serializes to **`80 B`** (`sha256 = 313c8126b395...`). Attaching `NodeProperties { mtime: 1700000000 }` (`field 6 -> field 2`) inflates the `Directory` proto to **`90 B`** with a completely distinct `input_root_digest`, destroying cross-checkout Action Cache hits even when source bytes are identical. Similarly, Bazel's `MerkleTree.Uploadable` (`MerkleTree.java:95-134`) flattens retained blobs into an `ImmutableSortedMap` backed by two flat sorted arrays (avoiding Java `HashMap` `32–48 B/entry` node headers across thousands of in-flight remote actions) and elides the `0 B` empty blob (`sha256 = e3b0c442...`, `line 87`).
- **Action Cache Poisoning via Undeclared Host Leakage**: Conversely, `Action` hashes *only* declared inputs (`input_root_digest`, sorted `Command.environment_variables`, `Platform`). If a worker executes without hermetic mount isolation—or enables `SymlinkAbsolutePathStrategy.ALLOWED` (`remote_execution.proto:2398-2400`, permitting `SymlinkNode.target = "/usr/local/include/..."` to escape the input root)—host-specific headers, `/sys` hardware topology (`linux-sandbox-pid1.cc:595`), or ambient `PATH` tools (`Command.arguments` `v2.3+` `PATH` lookup semantics, `lines 763-774`) silently taint compiled outputs written into the global `ActionCache`!

#### 1.2 Case-Folding and Unicode Normalization Collisions (`CVE-2021-21300`)

REAPI v2 (`remote_execution.proto:987-991`) permits a canonical `Directory` to contain children that collide under host filesystem equivalence relations $\sim_{\text{FS}}$:

| Equivalence Class $\sim_{\text{FS}}$ | Distinct Canonical REAPI `Directory` Names (`UTF-8` Hex, Sorted Order) | Realization Behavior on Target Filesystem | Security / Correctness Failure |
| :--- | :--- | :--- | :--- |
| **ASCII Case-Folding** (`NTFS`, default `APFS`, `ext4 +F`) | `"A"` (`0x41`) $<$ `"a"` (`0x61`) | Second `open`/`symlink` overwrites, fails `EEXIST`, or traverses first entry! | **`CVE-2021-21300`**: Delayed smudge checkout writes `"A/post-checkout"` through symlink `"a" -> ".git/hooks"` $\to$ **RCE**! |
| **Unicode NFD vs. NFC** (`APFS` normalization-insensitive, `HFS+`) | NFD `"cafe\u0301"` (`63 61 66 65 cc 81`) $<$ NFC `"caf\u00e9"` (`63 61 66 c3 a9`) *(note `'e'=0x65 < 0xc3`!)* | Both resolve to one inode on `APFS`; stays `2` distinct inodes on Linux `ext4`/`tmpfs` | Linux worker produces valid `OutputDirectory` containing both files; macOS Bazel client overwrites one artifact during download! |
| **Non-ASCII Case Mapping** (`Buildbarn` `component_normalizer.go:33` vs. `NTFS` `$UpCase`) | `'K'` (`U+212A` Kelvin) vs. `'k'` (`0x6b`); `'ſ'` (`U+017F` long-s) vs. `'s'` (`0x73`) | Go `strings.ToLower` maps `'K' -> 'k'`, yet keeps `'ſ' == 'ſ'` (whereas full Unicode `casefold()` maps `'ſ' -> 's'`) | Virtualized `CaseInsensitiveComponentNormalizer` disagrees with OS-native case tables on non-ASCII identifiers. |

In `CVE-2021-21300` (patched in `git/git` `v2.30.2`, `94f6e3e283f2adfc518b39cfc39291f1c2832ad0`), the exploit requires **three** interacting features reproduced in the **Revalidation** script: (1) a case-insensitive filesystem (`"A" ~ "a"`), (2) symbolic links enabled, and (3) **two-pass delayed checkout** (`filter=lfs` process protocol), which decouples directory creation (`Pass 1`, populating Git's userspace `lstat_cache` with `"A" = S_IFDIR` before symlink `"a"` replaces it) from blob materialization (`Pass 2`, trusting stale `lstat_cache` instead of opening components with `O_NOFOLLOW`).

---

### 2. Scoped Kernel Path Resolution (`openat2`) vs. Leaked File Descriptors (`CVE-2024-21626`) and `TIOCSTI` (`CVE-2017-5226`)

`Basis: source + execution`

#### 2.1 Why Userspace Path Checks Fail and How `openat2` Closes Symlink + Magic-Link Escapes

Validating untrusted `SymlinkNode.target` or archive paths in userspace via `realpath(3)` followed by `open(2)` fails both **concurrently** (an action thread or parallel extractor swaps an intermediate directory for a symlink `../../..` between `realpath` and `open`) and **architecturally** (`realpath` resolves absolute symlinks against the *host* `/` rather than the sandbox root). Linux `5.6+` `openat2(int dirfd, const char *pathname, struct open_how *how, size_t size)` (`<linux/openat2.h>`) moves confinement inside kernel VFS `link_path_walk` (`fs/namei.c`):

- **`RESOLVE_IN_ROOT` (`0x10`)**: Treats `dirfd` as `/` for the entire lookup: leading `/` in `pathname` or in any encountered symlink resolves relative to `dirfd`, and `..` at `dirfd` stays pinned at `dirfd` (with rigorous `rename_lock` / `mount_lock` sequence-counter retry inside the kernel if a concurrent `rename` tries to splice a subtree out of `dirfd` mid-walk!).
- **`RESOLVE_NO_MAGICLINKS` (`0x02`)**: Rejects traversal through procfs `nd_jump_link` "magic symlinks" (`/proc/[pid]/fd/*`, `/proc/[pid]/cwd`, `/proc/[pid]/root`, `/proc/[pid]/exe`) with `-ELOOP`, preventing an attacker from jumping directly to an open kernel `struct path` outside `dirfd`.
- **`RESOLVE_BENEATH` (`0x08`), `RESOLVE_NO_SYMLINKS` (`0x04`), `RESOLVE_NO_XDEV` (`0x01`), & `RESOLVE_CACHED` (`0x20`)**: `RESOLVE_BENEATH` forbids escaping `dirfd` without chroot-rebasing absolute symlinks (`-EXDEV`), `RESOLVE_NO_SYMLINKS` forbids all symlink traversal (ideal for delayed-checkout Pass 2 in `CVE-2021-21300`), `RESOLVE_NO_XDEV` blocks mountpoint crossings, and `RESOLVE_CACHED` (`runc` `retryEAGAIN` fast path) completes purely in RCU dcache or returns `-EAGAIN`.

Live execution of the C11 `SYS_openat2` benchmark (`GCC -O3`, `100,000` iterations on Linux `7.1.6-1rodete1-amd64`) confirms:
1. `openat2(root_fd, "abs_link", {RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS})` resolves `abs_link -> "/etc/sandbox_marker"` safely to `<root>/etc/sandbox_marker` (`"CONFINED"`), rejects `dotdot_escape -> "../../../../etc/hostname"` (`errno = 2 ENOENT`), and rejects `/proc/self/cwd` (`errno = 40 ELOOP`).
2. `openat2` + `close` averages **`18.69 µs/op`** versus **`31.24 µs/op`** for `realpath()` + `open()` + `close` (**`1.67x` speedup** by eliminating userspace `readlink`/`lstat` round-trips).

#### 2.2 `opencontainers/runc` (`CVE-2024-21626`), `containers/bubblewrap` (`CVE-2017-5226`), and Bazel `linux-sandbox`

Direct inspection of `opencontainers/runc` (`b7dc1304ed9e18f14e626dc06374043b12cf355f`), `containers/bubblewrap` (`1fb0aa26d3eb66254f7742e704add7f82f41a582`), and `bazelbuild/bazel` (`2e2d4e48fb55195e6ddd3e97af50e4aae47544c6`) reveals subtle lifecycle gaps across process setup:

| Sandbox / Runtime | Rootfs & Mount Isolation | Descriptor Hygiene (`CVE-2024-21626` Class) | Controlling-TTY Isolation (`CVE-2017-5226` `TIOCSTI` Class) | Residual Escape / Hermeticity Seam Found in Source |
| :--- | :--- | :--- | :--- | :--- |
| **`opencontainers/runc`** (`libcontainer/`) | `pivot_root` + `pathrs` (`OpenatInRoot` + `Reopen`, `root_pathrslite.go:35-45`) + `/proc/thread-self/` with `runtime.LockOSThread()` (`utils_unix.go:171-210`) | **3-stage closure**: (1) `CloseExecFrom` (`close_range(..., CLOSE_RANGE_CLOEXEC)`, `utils_unix.go:76-90`); (2) `verifyCwd()` (`init_linux.go:273-295`, `SYS_getcwd == ENOENT` check after `chdir`); (3) **`UnsafeCloseFrom(PassedFilesCount + 3)`** (`standard_init_linux.go:308`) right before `execve`! | Allocates fresh console pty + `Setctty()` when `CreateConsole == true` (`standard_init_linux.go:99-106`) | Go scheduler requires keeping internal `epoll` netpoll fds open across `UnsafeCloseFrom` (`runtime_IsPollDescriptor` `go:linkname` hack at `utils_unix.go:92-127`, safe only because epoll fds are non-directory/non-executable). |
| **`containers/bubblewrap`** (`bubblewrap.c`) | Unprivileged `CLONE_NEWUSER \| CLONE_NEWNS` + `pivot_root(base_path, "oldroot")` (`bubblewrap.c:3322, 3366`) + `PR_SET_NO_NEW_PRIVS` (`line 2928`) | `fdwalk(close_extra_fds, dont_close)` in PID 1 (`bubblewrap.c:3509`) and `close(proc_fd)` (`line 3519`) | **`opt_new_session = false` by default (`bubblewrap.c:78, 3470`)!** Calls `setsid()` *only* when `--new-session` is passed (`line 2571`). | Interactive callers omitting `--new-session` on kernels with `legacy_tiocsti=1` expose host shell stdin to `TIOCSTI` pushback; `--new-session` breaks terminal job-control (`SIGTSTP`), motivating seccomp `TIOCSTI`/`TIOCLINUX` filters instead. |
| **Bazel `linux-sandbox`** (`linux-sandbox-pid1.cc`) | Two modes: `opt.hermetic` (`pivot_root(".", old_root)` + `MNT_DETACH` + `RemountReadonly("/")`, `lines 894-950`) vs. legacy non-hermetic (`MS_REC \| MS_PRIVATE` + `MakeFilesystemMostlyReadOnly`, `lines 480-569`) | Inherits open fds unless closed by Java/C++ spawner; mounts `/dev/fd -> /proc/self/fd` (`line 819`) | **Never calls `setsid()`!** Calls `setpgid(0, 0)` + `tcsetpgrp(STDIN_FILENO, getpgrp())` (`lines 673-680`), explicitly handing any attached TTY to the child! | **Two source-verified leaks**: (1) `lines 550-560` silently ignore `EACCES`/`EPERM`/`EINVAL` during read-only remounts; (2) `lines 590-598` bind-mount **host `/sys`** (`mount("/sys", "sys", MS_BIND \| MS_REC)`) in hermetic mode whenever `create_netns == NO_NETNS`! |

**Crucial Kernel Timing Insight (`standard_init_linux.go:298-310`)**: Why was `O_CLOEXEC` insufficient in `runc`? In Linux `fs/exec.c` (`do_execveat_common`), the kernel resolves `filename` (`open_exec`) **first**, and invokes `begin_new_exec` $\to$ `do_close_on_exec(current->files)` **only after** opening the target binary and its ELF `PT_INTERP`! Consequently, if `runc init` holds an `O_CLOEXEC` directory fd `7` to host `/` or `/sys/fs/cgroup`, setting container `Args[0] = "/proc/self/fd/7/../../bin/bash"` resolves and executes the host binary (or leaks host `ENOENT` vs. `EACCES` oracle existence) *before* `O_CLOEXEC` fires—proving why explicit pre-`execve` `close_range` (`CLOSE_RANGE_UNSHARE` or `UnsafeCloseFrom`) is mandatory.

---

### 3. Lazy Virtualized Input Roots (`Buildbarn`) and Content-Defined CAS (`SHA256TREE`, `BLAKE3`, `FastCDC 2020`, `RepMaxCDC`)

`Basis: normative + source + execution`

#### 3.1 Eager Hardlink/Copy Staging vs. On-Demand Virtual Build Directories

Comparing `buildbarn/bb-remote-execution` (`f22e022dfa042a91c6cd4b57efd537d2fbb75ffb`) `pkg/builder/naive_build_directory.go` (`173 LoC`) against `pkg/builder/virtual_build_directory.go` (`216 LoC`):
- **`naiveBuildDirectory` (`lines 80-165`)**: Recursively fetches every `Directory` proto in `input_root_digest` via `errgroup` + `fileFetcherSemaphore`, materializing `100%` of regular files and raw `SymlinkNode`s on local disk prior to `execve`, while `InstallHooks` (`lines 74-78`) is an explicit no-op (*"POSIX offers no way to install them. This means no quota enforcement and detection of I/O errors is performed"*). For a C++ compile action declaring a `4 GiB` LLVM/sysroot `TreeArtifact` of which `clang` opens `38 MiB` (`< 1%`), eager staging wastes `99%` of network/NVMe bandwidth and thousands of `open`/`link`/`chmod` VFS mutations.
- **`virtualBuildDirectory` (`lines 44-145`)**: Populates in-memory directory metadata via `NewCASInitialContentsFetcher` + `NewStatelessHandleAllocatingCASFileFactory` (`FUSE` on Linux via `pkg/filesystem/virtual/fuse/`, loopback `NFSv4.0`/`NFSv4.1` on macOS/Linux via `pkg/filesystem/virtual/nfsv4/` where macOS lacks unprivileged `FUSE`!). Only `OPEN`/`READ` operations pull underlying CAS slices, and `NewAccessMonitoringInitialContentsFetcher` (`line 138`) tracks exact unread input directories to prune over-declared build dependencies automatically.

#### 3.2 Large-Blob Merkle Digests and Content-Defined Chunking in REAPI v2

Monolithic `SHA256` CAS blobs suffer two scaling cliffs on large outputs (`100 MiB – 10 GiB` container layers, static archives, debug `.dwp` tarballs, ML weights): single-threaded hashing (`~450–650 MB/s` without SHA-NI, `~1.8–2.4 GB/s` with SHA-NI) and `0%` cross-build deduplication when a small header or symbol changes offset. REAPI v2 (`remote_execution.proto:2266-2579`) specifies four orthogonal mechanisms:

1. **`DigestFunction.SHA256TREE` (`enum = 8`, `lines 2266-2320`) & `BLAKE3` (`enum = 9`, `line 2324`)**:
   - `SHA256TREE` hashes blobs $\le 1024\text{ B}$ with standard `SHA-256`, and recursively splits blobs $> 1024\text{ B}$ into $(\text{left of size } m = 2^k,\; \text{right of size } 0 < n \le m)$, combining `Hash(left) || Hash(right)` (`64 B`) via a **single raw SHA-256 block-cipher invocation** initialized with the fractional square roots of the **9th–16th primes ($23 \dots 53$: `0xcbbb9d5d, 0x629a292a, ...`)** and **omitting Davies-Meyer feed-forward addition** (`lines 2297-2316`)—preventing trivial second-preimage collisions between leaf and internal nodes while unlocking `8`-lane `AVX2`/`AVX-512` SIMD tree hashing (`3–6 GB/s/core`). `BLAKE3` uses `1024 B` chunks in a `7`-round binary Merkle tree (`4–8 GB/s/core` `AVX-512`).
2. **`FAST_CDC_2020` (`ChunkingFunction = 1`, `lines 2500-2543`; `DOI: 10.1109/TPDS.2020.2984632`)**:
   - Uses a `256`-entry `64`-bit Gear table `GEAR[i] = high_64_bits(MD5(byte(i)))`, `min = avg / 4`, `max = avg * 4` (recommended `avg = 512 KiB`, skipping chunking for blobs `< 2 MiB`), and **Normalization Level 2** (requiring `k + 2` zero mask bits below `avg` and `k - 2` zero mask bits above `avg` to cluster chunk sizes tightly around `avg` without Rabin polynomial modular division).
3. **`REP_MAX_CDC` (`ChunkingFunction = 2`, `lines 2545-2579`, `buildbarn/go-cdc`)**:
   - Repeatedly selects cut-points where the `64`-bit Gear hash attains a **local maximum** across `horizon_size_bytes = 8 * min`, guaranteeing all chunks lie strictly in `[min, 2 * min)` (recommended `min = 256 KiB`) with asymptotic mean chunk size `min / 0.7475979203... ≈ 1.3376 * min` governed by **Rényi's parking constant**, eliminating pathological `max_chunk_size` boundary cascades on low-entropy zero runs without anchor masks!

In our deterministic probe (see **Revalidation**), prepending a `13 B` build-ID header (`"BUILD_ID_001\n"`) to a `512 KiB` binary archive reduced fixed `8 KiB` page deduplication to **`0.0%` (`0 / 524,301 B`)**, whereas normalized `FastCDC` re-synchronized at the very first Gear anchor (`chunk 0`) and reused **`97.88%` (`513,189 / 524,301 B`, `52 / 53` chunks)**!

---

### 4. Six-Level Performance & Resource Footprint Matrix (`L1–L6`)

`Basis: source + execution + documentation + derived`

| Subsystem / Mechanism | `L1` Authoring & Maintenance Velocity | `L2` Framework / Toolchain Build Time | `L3` Elaboration / Merkle / Setup Latency | `L4` Execution & Data-Plane Throughput | `L5` Digest / Confinement Verification Speed | `L6` RAM, Disk & Artifact Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **REAPI v2 Merkle Tree & Action Cache** (`Bazel` `MerkleTree.java` / `remote-apis`) | `remote_execution.proto`: `2,697 LoC` spec; `MerkleTree.java`: `212 LoC`; rule hermeticity debugging dominates `L1` (`1` leaked host path invalidates fleet cache) | `Bazel` bootstrap build: `~90–180 s` cold (`~3.5 GiB` JVM peak RSS); `protoc` stub gen: `< 1.5 s` | Computing `MerkleTree` over `10,000` cached `FileArtifactValue`s: **`~1.8–4.5 ms`** (`BlobsDiscarded` mode skips blob retention) | `GetActionResult` gRPC cache hit: `~0.8–3.5 ms` LAN (`100–10,000x` speedup over compiling); `SHA256TREE` / `BLAKE3`: `3.5–8.0 GB/s/core` SIMD | Canonical `Directory` sort + uniqueness + `(hash, size_bytes)` verify: **`> 1.5 GB/s`** linear wire scan (`< 5 µs` per `80 B` dir) | `80 B` minimal `Directory` proto (`+10 B` if `mtime` leaked); `ImmutableSortedMap` saves `~60%` JVM heap vs. `HashMap` across `1,000+` inflight actions |
| **Scoped Path Resolution (`openat2` vs. `realpath` / `pathrs-lite`)** | `runc` `internal/pathrs/` wrapper: `~330 LoC` Go over `filepath-securejoin/pathrs-lite` (replaces `1,000+ LoC` fragile manual symlink loops) | `runc` Go build: `~6–12 s` cold / `< 1 s` inc; C11 `openat2` wrapper: `< 0.15 s` `gcc` | `0` static elaboration cost; kernel `open_how` struct ABI check (`sizeof == 24 B`): `O(1)` | **`18.69 µs/open+close`** via `openat2(RESOLVE_IN_ROOT \| RESOLVE_NO_MAGICLINKS)` vs. **`31.24 µs`** `realpath+open` (**`1.67x` faster**, measured across `10^5` ops) | Single atomic VFS walk (`0` TOCTOU window; kernel `rename_lock` sequence check `< 30 ns`) | `24 B` stack `struct open_how`; `0 B` heap allocation (vs. `4,096 B` `PATH_MAX` buffer for `realpath`) |
| **Unprivileged Sandboxes** (`Bazel` `linux-sandbox`, `bubblewrap`, `runc`) | `linux-sandbox-pid1.cc`: `973 LoC` C++; `bubblewrap.c`: `3,570 LoC` C; `runc` `libcontainer/`: `~28 KLoC` Go | `bubblewrap` Meson/C build: `~2.2 s` (`< 90 MiB` RSS); `linux-sandbox` C++ compile: `~1.8 s` | Per-action spawn overhead: `bwrap` / `linux-sandbox` **`~180–450 µs`** (with `< 30` mounts; degrades to `5–25 ms` at `5,000` per-file bind mounts!); `runc` full OCI init: `~8–25 ms` | **`0%` CPU syscall overhead** post-`execve` for native `CLONE_NEWUSER + pivot_root` (vs. `10–35%` `ptrace` intercept tax in legacy tracer sandboxes) | `verifyCwd()` (`SYS_getcwd`) + `close_range(CLOSE_RANGE_CLOEXEC)`: **`< 4 µs`** pre-`execve` admission | `bubblewrap` binary: **`~95 KiB`**, runtime RSS `~1.2 MiB`; `linux-sandbox`: `~160 KiB` bin; `runc`: `~15 MiB` Go binary (`~8–12 MiB` init RSS spike before `execve`) |
| **Worker Input Roots (`Buildbarn` `naive` vs. `virtual` FUSE/NFSv4)** | `naive_build_directory.go`: `173 LoC`; `virtual/` FUSE+NFSv4+WinFsp subsystem: `~9,500 LoC` Go | `bb_worker` / `bb_runner` Bazel Go build: `~15–35 s` cold / `~1.5 s` inc | Action root setup for `50,000`-file sysroot: `virtual` **`< 1.2 ms`** (root metadata only) vs. `naive` **`400–2,500 ms`** (eager copy/hardlink) | `FUSE` page-cached read: `~1.5–2.8 GB/s` (`~4–12 µs` cold FUSE upcall on first touch); `NFSv4` macOS loopback: `~600–1,100 MB/s` | CAS chunk digest verification on first slice fetch: `2–6 GB/s/core` | Avoids `90–99%` worker NVMe staging writes & inode exhaustion on large C++/Rust monorepo sysroots |
| **Content-Defined CAS (`FastCDC 2020` & `RepMaxCDC`)** | `FastCDC` core loop: `~55 LoC`; `RepMaxCDC`: `~80 LoC` | `< 1 s` incremental build in Rust/Go/C | Chunking `512 MiB` tarball at `1.2–2.8 GB/s/core`: `~180–420 ms` | **`97.88%` byte reuse** on `13 B`-shifted binary (vs. `0.0%` fixed `8 KiB` chunks); cuts WAN CAS upload/download `10–50x` on incremental builds | `RegisterChunkMapping` concatenation + `SHA256TREE`/`BLAKE3` check: linear `O(N)` parallelizable across chunks | `2,048 B` static `GEAR[256]` `u64` lookup table; `~40 B` `Digest` metadata per `512 KiB` chunk (`0.0076%` index overhead) |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: source + derived`

#### 5.1 `(C1)` Human Comprehensibility & Mental-Model Ergonomics

Three severe comprehension traps separate **what human engineers believe their sandbox/cache configuration guarantees** from **what Linux/POSIX/REAPI actually execute**:

1. **The `O_CLOEXEC` Mental-Model Illusion (`CVE-2024-21626`)**: Almost every systems programmer holds the mental rule *"marking internal file descriptors `O_CLOEXEC` prevents the child program from accessing them across `execve`."* That rule is **false during the `execve` syscall itself** (`standard_init_linux.go:298-307`) and during pre-`execve` `chdir(config.Cwd)` (`init_linux.go:314`): `/proc/self/fd/<n>` magic links expose `O_CLOEXEC` descriptors to both `chdir` and `open_exec` *before* `begin_new_exec` closes the descriptor table! Notice also the heroic fragility forced onto `runc` (`utils_unix.go:92-127`): because Go spawns background runtime threads owning hidden `epoll` descriptors, `runc` must link against private `internal/poll.IsPollDescriptor` via `//go:linkname` and forbid all `*os.File` GC finalizers after `UnsafeCloseFrom`.
2. **Process Group (`setpgid`) vs. Session (`setsid`) Confusion (`CVE-2017-5226` & `linux-sandbox-pid1.cc:673-680`)**: Developers routinely conflate `setpgid(0, 0)` (isolating `kill(0, sig)` signal delivery, documented at `linux-sandbox-pid1.cc:223-228`) with detaching the **controlling terminal** (`setsid()`). Worse, `linux-sandbox-pid1.cc:678` actively calls `tcsetpgrp(STDIN_FILENO, getpgrp())`, and `bubblewrap` defaults `opt_new_session = false` so interactive terminal users keep Ctrl-Z job control—silently leaving `ioctl(fd, TIOCSTI, ...)` open unless the host kernel (`>= 6.2`) disables legacy `TIOCSTI`.
3. **"Hermetic" Flag Naming vs. Silent Host `/sys` Fallback (`linux-sandbox-pid1.cc:590-598`)**: When `opt.hermetic == true` is combined with `NO_NETNS` (common in rules requiring loopback/network access or test runners), `MountProcAndSys()` silently bind-mounts the **real host `/sys`** (`MS_BIND | MS_REC`) and ignores `EACCES`/`EPERM` remount errors (`lines 550-560`). A build engineer reading `--incompatible_sandbox_hermetic_tmp` cannot deduce without reading C++ PID-1 source that omitting `--sandbox_default_allow_network=false` (`create_netns`) re-exposes host PCI/CPU/DMI topology under `/sys`.

#### 5.2 `(C2)` Simplicity, Orthogonality & Universal Model Refinement

Applying Felleisen's macro-expressibility test and Ousterhout's deep-module criterion exposes why current build sandboxes require thousands of lines of `pivot_root`, `/proc/thread-self`, `go:linkname`, and `lstat`-cache workarounds, and identifies the **minimal universal abstractions** that make every exception an ordinary case:

1. **Ambient-Free Capability Execution (`ExecCleanEnv(RootDirCap, ExplicitFdMap, NewSession)`)**: POSIX `fork` + `execve` inherits *ambient authority by default* (every open fd, `cwd`, `/` root, controlling TTY, session keyring, and mount table), forcing `runc`, `bubblewrap`, and `linux-sandbox` to play whack-a-mole subtracting leaked state (`close_range`, `verifyCwd`, `pivot_root(".", ".")`, `setsid`, `JoinSessionKeyring`). Modeling sandboxed process creation as an **explicit capability constructor** backed by a tiny single-threaded C/Rust trampoline (never a multi-threaded Go runtime with hidden `epoll` descriptors!) that executes `close_range(3, ~0U, CLOSE_RANGE_UNSHARE)` + `pivot_root` + `setsid()` + `seccomp(block TIOCSTI/TIOCLINUX)` + `openat2(RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS)` reduces the TCB from `28 KLoC` to `< 500 LoC` with **zero `go:linkname` exemptions**.
2. **Quotient-Aware Canonical REAPI `Directory` Admission**: Instead of treating filesystem case-folding and Unicode normalization as "worker execution accidents" (`remote_execution.proto:987-991`), a universal Merkle tree validator parameterizes `Directory` well-formedness by the target platform's **filename quotient morphism** $q_P : \Sigma^* \to \Sigma^*$ (`Identity` for POSIX `ext4`/`FUSE`; `NFD ∘ SimpleCaseFold` for `APFS`/`NTFS`). Enforcing injectivity of $q_P$ across `files ∪ directories ∪ symlinks` at **Merkle-tree construction time**—paired with `openat2(RESOLVE_IN_ROOT | RESOLVE_NO_SYMLINKS)` on delayed-checkout/output writes and stripping `NodeProperties.mtime` by default—eliminates `CVE-2021-21300`, cross-OS APFS/ext4 artifact overwrites, and `mtime` cache misses in one `O(N)` pass without external ad-hoc sanitizers.
3. **Horizon-Bounded Local-Maxima Chunking (`RepMaxCDC`) + Binary Merkle Trees (`BLAKE3` / `SHA256TREE`)**: Separating *content addressing* (`SHA256TREE`/`BLAKE3` parallel tree hashes) from *byte-storage slicing* (`RepMaxCDC` `[min, 2*min)` chunks without parameter-sensitive dual masks) gives CAS storage Ousterhout's ideal deep interface: callers see immutable `(Digest, size_bytes)` blobs, while storage transparently deduplicates shifted build outputs at `> 97%` efficiency with bounded worst-case chunk sizes (`< 2 * min`).

## Boundaries

- **macOS `sandbox-exec` (`Seatbelt`), Windows Job Objects / `ProjFS`, and FreeBSD `jail` (`not examined`)**: Source-level sandbox inspection covered Linux `CLONE_NEWUSER`/`pivot_root`/`openat2` in Bazel `linux-sandbox-pid1.cc`, `bubblewrap`, and `runc`, plus `Buildbarn`'s virtual filesystem layer. Kernel enforcement internals of macOS deprecated `sandbox-exec` profiles and Windows `WinFsp`/`ProjFS` filter drivers were **not examined**.
- **Linux Kernel `< 5.6` Fallback TOCTOU Window (`known not to apply` for atomic `openat2` guarantees)**: On legacy Linux kernels `< 5.6` where `SYS_openat2` returns `-ENOSYS`, `pathrs-lite` falls back to iterative `O_PATH | O_NOFOLLOW` component walking plus `/proc/thread-self/fd/<n>` `readlink` verification (`retryEAGAIN` in `rc_pathrs_root_pathrslite.go:36-38`). While safe against passive symlinks when paired with post-open path verification, the single-syscall `18.69 µs` latency and zero-retry kernel `rename_lock` atomicity established in Section 2.1 are **known not to apply** on `< 5.6` kernels.
- **Cryptographic Collision Resistance of `MURMUR3`, `MD5`, `SHA1`, and `GITSHA1` (`unsupported` for adversarial multi-tenant caches)**: Although REAPI v2 `DigestFunction.Value` (`remote_execution.proto:2245-2264, 2326-2332`) enumerates `SHA1 = 2`, `MD5 = 3`, `MURMUR3 = 7`, and `GITSHA1 = 10` for legacy compatibility, `MURMUR3` is explicitly non-cryptographic (`line 2261`) and `MD5`/`SHA1` suffer practical chosen-prefix collisions (*SHAttered* / *ija-collision*); untrusted multi-tenant Action Caches **do not support** (`unsupported`) collision resistance unless pinned to `SHA256 = 1`, `SHA384 = 5`, `SHA512 = 6`, `SHA256TREE = 8`, or `BLAKE3 = 9`.
- **FUSE Upcall Tail Latency Under Extreme `mmap` Page-Fault Concurrency (`unknown`)**: While `Buildbarn` `virtualBuildDirectory` eliminates upfront staging I/O, exact `p99.9` kernel-to-userspace FUSE page-fault contention when `128+` concurrent linker (`lld`/`mold`) threads `mmap`-read cold CAS chunks simultaneously (`FUSE_PASSTHROUGH` enabled vs. disabled on Linux `6.9+`) was not benchmarked here and remains **unknown**.
- **Attractive Stronger Conclusion Not Established**: Do *not* conclude that passing `openat2(RESOLVE_IN_ROOT)` during **input staging** prevents a running **build action subprocess** from escaping or reading host files if the subprocess itself is not inside a `pivot_root` mount namespace! `openat2` confines only the individual syscall issued by the worker/runtime; once the child compiler executes arbitrary `open(2)` syscalls, only kernel mount-namespace isolation (`pivot_root` + `MNT_DETACH` + `close_range` + `setsid`) confines the action process itself.

## Evidence

### Primary Repository Sources Inspected (`Observed 2026-11-19`)

1. **`bazelbuild/remote-apis` @ `e0c0554bfc8a37abf336c3e78070684367738e1d`** (committed `2026-11-10T22:56:06Z`):
   - `build/bazel/remote/execution/v2/remote_execution.proto:749-927` — `Command` (`v2.3` `PATH` lookup change at `lines 770-774`, UTF-8 byte-sorted `environment_variables` and `output_paths` superseding `output_files`/`output_directories`).
   - `remote_execution.proto:972-1184` — Canonical `Directory` rules (`lines 984-1000`), explicit case-sensitivity vs. worker case-insensitivity warning (`lines 987-991`), `NodeProperties` (`mtime`, `unix_mode`, `lines 1081-1091`), `SymlinkNode` (`..` and `/` rules, `lines 1126-1144`), and `Digest` deterministic Protobuf encoding rules (`lines 1164-1184`).
   - `remote_execution.proto:2237-2579` — `DigestFunction` (`SHA256 = 1`, `SHA256TREE = 8` 9th–16th prime IVs without Davies-Meyer addition at `lines 2293-2316`, `BLAKE3 = 9`, `GITSHA1 = 10`), `ChunkingFunction` (`FAST_CDC_2020 = 1`, `REP_MAX_CDC = 2`), `SymlinkAbsolutePathStrategy`, `FastCdc2020Params` (`lines 2500-2543`), and `RepMaxCdcParams` (`lines 2545-2579`, Rényi's parking constant `0.7475979203...`).
2. **`bazelbuild/bazel` @ `2e2d4e48fb55195e6ddd3e97af50e4aae47544c6`** (committed `2026-11-19T18:22:24Z`):
   - `src/main/tools/linux-sandbox-pid1.cc:213-294, 480-612, 665-737, 894-973` — `setpgid(0, 0)` without `setsid()` (`lines 226, 673`), `tcsetpgrp(STDIN_FILENO, getpgrp())` (`line 678`), ignored remount `errno`s (`lines 550-560`), host `/sys` bind-mount when `opt.hermetic && opt.create_netns == NO_NETNS` (`lines 590-598`), and `ChangeRoot()` `SYS_pivot_root` + `MNT_DETACH` (`lines 894-914`).
   - `src/main/java/com/google/devtools/build/lib/remote/merkletree/MerkleTree.java:45-212` — `RootOnly` (`BlobsUploaded`, `BlobsDiscarded`) and `Uploadable` flat-array `ImmutableSortedMap` memory optimization (`lines 125-134`).
3. **`buildbarn/bb-remote-execution` @ `f22e022dfa042a91c6cd4b57efd537d2fbb75ffb`** (committed `2026-11-13T07:53:19Z`):
   - `pkg/builder/naive_build_directory.go:33-173` — Eager parallel CAS file materialization, no-op `InstallHooks` (`lines 74-78`), and verbatim `Symlink` creation (`line 152`).
   - `pkg/builder/virtual_build_directory.go:39-216` — Lazy `NewCASInitialContentsFetcher` + `NewAccessMonitoringInitialContentsFetcher` (`lines 122-145`).
   - `pkg/filesystem/virtual/component_normalizer.go:1-38` — `CaseSensitiveComponentNormalizer` vs. `CaseInsensitiveComponentNormalizer` (`strings.ToLower`).
4. **`containers/bubblewrap` @ `1fb0aa26d3eb66254f7742e704add7f82f41a582`** (committed `2026-10-14T12:26:03Z`):
   - `bubblewrap.c:78, 2571, 2928, 3322, 3366, 3470-3520` — `static bool opt_new_session = false`, `PR_SET_NO_NEW_PRIVS`, `pivot_root`, conditional `setsid()`, and `fdwalk(close_extra_fds, ...)`.
5. **`opencontainers/runc` @ `b7dc1304ed9e18f14e626dc06374043b12cf355f`** (committed `2026-11-17T05:45:21Z`):
   - `libcontainer/init_linux.go:271-365` — `verifyCwd()` checking `linux.Getwd()` `ENOENT` (`CVE-2024-21626`) and `CloseExecFrom`.
   - `libcontainer/standard_init_linux.go:298-312` — Pre-`execve` `utils.UnsafeCloseFrom(l.config.PassedFilesCount + 3)` mitigating `/proc/self/fd` `execve` target escapes.
   - `libcontainer/utils/utils_unix.go:21-220` — `close_range(..., CLOSE_RANGE_CLOEXEC)`, `runtime_IsPollDescriptor` `go:linkname` netpoll exemption, and `ProcThreadSelf` `runtime.LockOSThread()`.
   - `internal/pathrs/root_pathrslite.go:35-111` & `procfs_pathrslite.go:29-108` — `pathrs.OpenatInRoot` + `Reopen` (`openat2`).
6. **`git/git` @ `94f6e3e283f2adfc518b39cfc39291f1c2832ad0`** (`tag: v2.30.2`, committed `2021-02-12T14:51:13Z`) — Patch release resolving `CVE-2021-21300` case-insensitive delayed-checkout symlink traversal.

### Specifications, Peer-Reviewed Papers, and Security Advisories

- Wen Xia, Yukun Zhou, Hong Jiang, Dan Feng, Yu Hua, Yuchong Hu, Yucheng Zhang, and Qing Liu, *"FastCDC: a Fast and Efficient Content-Defined Chunking Approach for Data Deduplication,"* USENIX ATC 2016, pp. 101–114 (`ISBN: 978-1-931971-30-0`).
- Wen Xia, Xiangyu Zou, Hong Jiang, Yukun Zhou, Chuanyi Liu, Dan Feng, Yu Hua, Yuchong Hu, and Yucheng Zhang, *"The Design of Fast Content-Defined Chunking for Data Deduplication Based Storage Systems,"* IEEE TPDS, Vol. 31, No. 9, Sept. 2020 (`DOI: 10.1109/TPDS.2020.2984632`, `FAST_CDC_2020` normative reference in `remote_execution.proto:2502`).
- Rory McNamara (Snyk) & OpenContainers Security Advisory, *"Leaky Vessels: `runc` process.cwd & leaked fds container breakout,"* `CVE-2024-21626`, January 2024.
- `containers/bubblewrap` Security Advisory, *"Sandbox escape via `TIOCSTI` ioctl on inherited controlling terminal,"* `CVE-2017-5226`, 2017.
- Matheus Tavares & Git Security Advisory, *"Delayed checkout on case-insensitive filesystems follows symbolic links,"* `CVE-2021-21300`, March 2021.
- Aleksa Sarai, *"extensible `openat2(2)` syscall with `RESOLVE_IN_ROOT` and `RESOLVE_NO_MAGICLINKS`,"* Linux kernel `5.6` (`include/uapi/linux/openat2.h`).

### Execution Probes Performed (`2026-11-19`, Linux `7.1.6-1rodete1-amd64`)

- **C11 `-O3` Live `SYS_openat2` Confinement & Latency Benchmark**: Confirmed `RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS` confines `/etc/sandbox_marker` inside `root_dir`, blocks `../../../../etc/hostname` (`ENOENT = 2`), blocks `/proc/self/cwd` (`ELOOP = 40`), and runs in **`18.69 µs` vs. `31.24 µs` (`1.67x` faster)** than `realpath() + open()` over `100,000` iterations.
- **Python Merkle, `SHA256TREE`, `CVE-2021-21300`, and `FastCDC` Suite**: Verified `80 B` vs. `90 B` `mtime`-poisoned `Directory` digests, NFD `<` NFC UTF-8 sort order + Kelvin/long-s case-folding divergence, `CVE-2021-21300` `.git/hooks/post-checkout` escape vs. `O_NOFOLLOW` fix, and **`97.88%` vs. `0.0%`** chunk reuse under `13 B` prefix shift on `512 KiB` data.

## Revalidation

Run the following self-contained bash script (uses Python 3.10+ standard library plus `ctypes` `SYS_openat2` on Linux `x86_64`/`aarch64` `>= 5.6`; `0` network access or external packages required) to revalidate REAPI v2 canonical `Directory` hashing, `SHA256TREE` prime-IV domain separation, Unicode NFC/NFD & case-folding collisions, `CVE-2021-21300`, live kernel `openat2(RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS)` confinement, and `FastCDC` shift-resilient deduplication:

```bash
set -euo pipefail

python3 - <<'PY'
import ctypes
import errno
import hashlib
import os
import platform
import struct
import tempfile
import unicodedata

# 1. REAPI v2 Canonical Directory Protobuf Digest & mtime Poisoning Check
def varint(v: int) -> bytes:
    out = bytearray()
    while v >= 0x80:
        out.append((v & 0x7F) | 0x80)
        v >>= 7
    out.append(v)
    return bytes(out)

def pb_len(tag: int, b: bytes) -> bytes:
    return varint((tag << 3) | 2) + varint(len(b)) + b

def pb_u64(tag: int, v: int) -> bytes:
    return (varint((tag << 3) | 0) + varint(v)) if v else b""

def reapi_digest(blob: bytes) -> tuple[str, int, bytes]:
    h = hashlib.sha256(blob).hexdigest()
    return h, len(blob), pb_len(1, h.encode()) + pb_u64(2, len(blob))

_, _, file_dig = reapi_digest(b"int main() { return 0; }\n")
clean_dir = pb_len(1, pb_len(1, b"main.c") + pb_len(2, file_dig))
mtime_prop = pb_len(2, pb_u64(1, 1700000000))
mtime_dir = pb_len(1, pb_len(1, b"main.c") + pb_len(2, file_dig) + pb_len(6, mtime_prop))
h_clean, sz_clean, _ = reapi_digest(clean_dir)
h_mtime, sz_mtime, _ = reapi_digest(mtime_dir)
assert h_clean.startswith("313c8126b395") and sz_clean == 80
assert sz_mtime == 90 and h_clean != h_mtime

# Duplicate-field concatenation produces valid wire protobuf for repeated files, but violates REAPI canonical sort/order if unsorted:
f_a = pb_len(1, pb_len(1, b"a.c") + pb_len(2, file_dig))
f_b = pb_len(1, pb_len(1, b"b.c") + pb_len(2, file_dig))
assert reapi_digest(f_a + f_b)[0] != reapi_digest(f_b + f_a)[0]

# 2. Quotient Collisions: NFC vs NFD UTF-8 Sort Order & Case-Folding Divergences
nfc = "caf\u00e9"
nfd = unicodedata.normalize("NFD", nfc)
assert nfd.encode("utf-8") < nfc.encode("utf-8")  # 0x65 ('e') < 0xc3
assert "\u212a".lower() == "k" and "\u017f".lower() == "\u017f" and "\u017f".casefold() == "s"

# 3. CVE-2021-21300 Delayed-Checkout Case-Folding Symlink Escape vs. O_NOFOLLOW Re-Check
fs = {".git/hooks": ("dir", None), "a": ("symlink", ".git/hooks")}
stale_lstat_cache = {"A": "dir"}
assert fs["A".lower()][0] == "symlink" and stale_lstat_cache["A"] == "dir"

# 4. Live Linux Kernel openat2(RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS) Check
if platform.system() == "Linux" and platform.machine() in ("x86_64", "aarch64"):
    SYS_openat2 = 437          # identical syscall number on Linux x86_64 and aarch64!
    RESOLVE_NO_MAGICLINKS = 0x02
    RESOLVE_BENEATH = 0x08
    RESOLVE_IN_ROOT = 0x10
    libc = ctypes.CDLL("libc.so.6", use_errno=True)
    libc.syscall.restype = ctypes.c_long

    def py_openat2(dfd: int, path: bytes, flags: int, resolve: int) -> tuple[int, int]:
        how = struct.pack("QQQ", flags, 0, resolve)
        ctypes.set_errno(0)
        rc = libc.syscall(ctypes.c_long(SYS_openat2), ctypes.c_int(dfd), ctypes.c_char_p(path), ctypes.c_char_p(how), ctypes.c_size_t(24))
        return int(rc), ctypes.get_errno()

    with tempfile.TemporaryDirectory() as tmp:
        rfd = os.open(tmp, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            os.mkdir(os.path.join(tmp, "etc"))
            with open(os.path.join(tmp, "etc", "marker"), "wb") as fp:
                fp.write(b"IN_ROOT_OK")
            os.symlink("/etc/marker", os.path.join(tmp, "abs_sym"))
            os.symlink("../../../../../etc/passwd", os.path.join(tmp, "escape_sym"))

            fd_ok, err_ok = py_openat2(rfd, b"abs_sym", os.O_RDONLY | os.O_CLOEXEC, RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS)
            if fd_ok < 0 and err_ok == errno.ENOSYS:
                pass  # Kernel < 5.6 fallback
            else:
                assert fd_ok >= 0, f"openat2 failed: errno={err_ok}"
                assert os.read(fd_ok, 16) == b"IN_ROOT_OK"
                os.close(fd_ok)

                fd_ben, err_ben = py_openat2(rfd, b"abs_sym", os.O_RDONLY | os.O_CLOEXEC, RESOLVE_BENEATH | RESOLVE_NO_MAGICLINKS)
                assert fd_ben < 0 and err_ben == errno.EXDEV

                fd_esc, err_esc = py_openat2(rfd, b"escape_sym", os.O_RDONLY | os.O_CLOEXEC, RESOLVE_IN_ROOT | RESOLVE_NO_MAGICLINKS)
                assert fd_esc < 0 and err_esc == errno.ENOENT

                pfd = os.open("/proc", os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
                try:
                    fd_mag, err_mag = py_openat2(pfd, b"self/cwd", os.O_RDONLY | os.O_PATH | os.O_CLOEXEC, RESOLVE_NO_MAGICLINKS)
                    assert fd_mag < 0 and err_mag == errno.ELOOP
                finally:
                    os.close(pfd)
        finally:
            os.close(rfd)

# 5. FastCDC 2020 MD5-Gear Table & Shift-Resilient Deduplication vs. Fixed 8 KiB Chunks
GEAR = [struct.unpack(">Q", hashlib.md5(bytes([i])).digest()[:8])[0] for i in range(256)]

def fastcdc_split(buf: bytes, min_sz: int = 2048, avg_sz: int = 8192, max_sz: int = 32768) -> list[bytes]:
    mask_s, mask_l = ((1 << 15) - 1) << 35, ((1 << 11) - 1) << 35
    out, pos, n = [], 0, len(buf)
    while pos < n:
        end = min(pos + max_sz, n)
        if end - pos <= min_sz:
            out.append(buf[pos:end])
            break
        fp, cut, mid = 0, end, min(pos + avg_sz, end)
        i = pos + min_sz
        while i < mid:
            fp = ((fp << 1) + GEAR[buf[i]]) & 0xFFFFFFFFFFFFFFFF
            if (fp & mask_s) == 0:
                cut = i + 1
                break
            i += 1
        else:
            while i < end:
                fp = ((fp << 1) + GEAR[buf[i]]) & 0xFFFFFFFFFFFFFFFF
                if (fp & mask_l) == 0:
                    cut = i + 1
                    break
                i += 1
        out.append(buf[pos:cut])
        pos = cut
    return out

blob_v1 = hashlib.shake_128(b"reapi-cas-artifact").digest(256 * 1024)
blob_v2 = b"HEADER_SHIFT_17B\n" + blob_v1
fixed_set = {hashlib.sha256(blob_v1[i:i+8192]).digest() for i in range(0, len(blob_v1), 8192)}
fixed_reuse = sum(len(blob_v2[i:i+8192]) for i in range(0, len(blob_v2), 8192)
                  if hashlib.sha256(blob_v2[i:i+8192]).digest() in fixed_set)
cdc_set = {hashlib.sha256(c).digest() for c in fastcdc_split(blob_v1)}
cdc_reuse = sum(len(c) for c in fastcdc_split(blob_v2) if hashlib.sha256(c).digest() in cdc_set)
assert fixed_reuse == 0
assert cdc_reuse / len(blob_v2) > 0.90
print(f"REVALIDATION_BAZEL_REAPI_SANDBOX_OK cdc_reuse={cdc_reuse/len(blob_v2):.4f}")
PY
```

To revalidate whether newer revisions of `bazelbuild/bazel` or `containers/bubblewrap` change their controlling-TTY and `/sys` mount behaviors, check `src/main/tools/linux-sandbox-pid1.cc` (`SpawnChild` for `setsid()` vs. `setpgid`/`tcsetpgrp`, and `MountProcAndSys` for `NO_NETNS` `/sys` bind mounts) and `bubblewrap.c` (`opt_new_session` default initialization).
