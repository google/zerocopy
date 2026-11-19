# POSIX VFS RCU-Walk, SibylFS Executable Oracles, FUSE Reclaim Deadlocks, and CoW Checksummed Filesystems

## Summary

Operating-system filesystems sit at the intersection of lockless path-resolution concurrency, ambiguous POSIX syscall semantics, kernel–userspace memory-reclaim inversions, and copy-on-write (`CoW`) crash-consistency space accounting. Primary-source inspection of `torvalds/linux`, `sibylfs/sibylfs_src`, `libfuse/libfuse`, and `openzfs/zfs` establishes four load-bearing invariants:

1. **Linux VFS Lockless `RCU-walk`, `d_seq` Seqlocks, and Cross-Directory `s_vfs_rename_mutex` Cycle Prevention:** Pathname lookup begins in `RCU-walk` (`LOOKUP_RCU`) under `rcu_read_lock()` with zero reference-count or spinlock cache-line writes, validating every hop via per-dentry `seqcount_spinlock_t d_seq`, global `seqlock_t rename_lock`, and `mount_lock` (`m_seq`), and falling back monotonically to `REF-walk` via `try_to_unlazy()` / `-ECHILD`. Cross-directory renames (`p1 != p2`) MUST hold per-superblock `s_vfs_rename_mutex` before `lock_two_directories` walks ancestor chains; omitting superblock-wide serialization allows concurrent moves (`rename("/a/b", "/c/d/b")` and `rename("/c/d", "/a/b/d")`) to both pass local ancestor checks and detach a live cyclic directory subgraph unreachable from `/` (verified by Probe 2A). Symlink traversal enforces `MAXSYMLINKS` (`-ELOOP`) and scoped confinement (`LOOKUP_BENEATH` / `LOOKUP_NO_XDEV` returning `-EXDEV`).
2. **Set-Valued Executable POSIX Oracles (`SibylFS`):** POSIX.1-2024 permits substantial nondeterminism (error precedence, inode numbers, `readdir` ordering, partial I/O), and mainstream OSes (`Linux`, `macOS`, `FreeBSD`) diverge systematically on edge cases such as `open(..., O_NOFOLLOW)` (`ELOOP` vs. non-POSIX behaviors), trailing slashes, and `rename` error codes. `SibylFS` (`sibylfs/sibylfs_src`) models filesystem transitions in Lem as a **set-valued** function `fs_trans : ... -> finset (monad_state 'impl ret_value)` parameterized by an explicit `ty_arch` record (`ARCH_LINUX | ARCH_POSIX | ARCH_MAC_OS_X | ARCH_FREEBSD`), rejecting point-equality testing in favor of trace membership adjudication.
3. **FUSE Upcalls and Kernel Memory-Reclaim Writeback Deadlocks:** When `FUSE_WRITEBACK_CACHE` is active, a userspace FUSE daemon handling a kernel `FUSE_WRITE` upcall can allocate memory and enter kernel direct reclaim; if reclaim blocks waiting for that same FUSE writeback to finish, the system deadlocks. While historical kernels mitigated this by copying every dirty page into a temporary bounce page and immediately ending writeback, modern Linux (`torvalds/linux` @ `4405c18c`) eliminates bounce-page copying by submitting page-cache folios directly through `iomap_writepages` and tagging the mapping with `mapping_set_writeback_may_deadlock_on_reclaim(&inode->i_data)` (`fs/fuse/file.c:3177`), combined with `BDI_CAP_STRICTLIMIT` (capping each FUSE mount to 1% of global dirty+writeback thresholds), `GFP_NOFS | __GFP_NOFAIL` fallback in `fuse_send_writepage`, and `congestion_threshold` throttling. `FUSE_PASSTHROUGH` and `FUSE_WRITEBACK_CACHE` remain mutually exclusive.
4. **CoW Checksummed Trees (`Btrfs` & `OpenZFS`) and Space-Credit Solutions to the 100%-Full `unlink()` `ENOSPC` Paradox:** Unlike in-place redo-journaled `ext4`/`jbd2`, CoW filesystems must allocate **new** metadata blocks along modified leaf-to-root paths **before** transaction commit can free deleted blocks—causing `unlink()` to fail with `ENOSPC` on a physically 100%-full volume unless space credits are withheld upfront. `Btrfs` solves this via `global_block_rsv` (capped at `SZ_512M` = 512 MiB) used as fallback by `btrfs_unlink` (`BTRFS_UNLINK_METADATA_UNITS = 6`, reserving up to `768 KiB` per worst-case unlink at 16 KiB `nodesize` and `BTRFS_MAX_LEVEL = 8`). `OpenZFS` solves this via `spa_get_slop_space` ($1/32 = 3.125\%$ of pool, clamped to `[128 MiB, 128 GiB]`, never exceeding 50%) divided into tiered gates in `dsl_pool_adjustedsize`: normal writes stop at `slop`, `unlink` may use `slop/2` (`ZFS_SPACE_CHECK_RESERVED`), and `zfs destroy` may use `3/4 * slop` (`ZFS_SPACE_CHECK_EXTRA_RESERVED`)—a third tier required because snapshot-pinned unlinks consume CoW metadata without freeing any physical extents (Probe 2B).

## Applicability

This report covers four closely interacting storage and OS-interface layers across the immutable subjects pinned in `REPORT.json`:

- **Linux VFS, FUSE Kernel Client, Btrfs, and `jbd2`:** Directly inspected at `torvalds/linux` revision `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`. Findings on FUSE bounce-page elimination (`iomap_writepages` + `mapping_set_writeback_may_deadlock_on_reclaim`) apply specifically to modern folio/iomap-based Linux kernels containing that architecture and explicitly contrast with pre-6.13/6.15 bounce-page kernels. Findings on `Btrfs` assume default 16 KiB `nodesize` and `BTRFS_MAX_LEVEL = 8` (parametric formulas are given for other node sizes).
- **Executable POSIX Specifications & Syscall Standards:** `sibylfs/sibylfs_src` (`30675bc3b91e73f7133d0c30f18857bb1f4df8fa`, SOSP 2015, DOI `10.1145/2815400.2815411`) interpreted alongside normative `IEEE Std 1003.1-2024` (POSIX.1-2024 / Issue 8). Findings apply to single-host POSIX filesystem syscall traces and path-resolution error semantics (`open`, `rename`, `unlink`, `symlink`, `ELOOP`).
- **Userspace FUSE Protocol & Library:** `libfuse/libfuse` (`6a484ac67fba410d722473e5e107da9b804fc40d`), paired with `torvalds/linux` `fs/fuse/` to characterize the exact kernel↔userspace ABI (`fuse_kernel.h` protocol revisions 7.23 through 7.41+, `FUSE_WRITEBACK_CACHE`, `FUSE_PASSTHROUGH`, `max_background`, `congestion_threshold`).
- **OpenZFS & Btrfs CoW Storage Engines:** `openzfs/zfs` (`cde5d598eb44b5d6efe8167666d988a496346657`) and `Btrfs` (`torvalds/linux` @ `4405c18c`; Rodeh, Bacik, Mason, ACM TOS 2013, DOI `10.1145/2501620.2501623`), contrasted with `ext4` `jbd2` (`torvalds/linux/fs/jbd2/commit.c`).
- **Relationship Across Subjects:** A POSIX syscall (e.g., `openat2`, `renameat2`, `unlink`, `fsync`) traverses the VFS `dcache` (`RCU-walk`/`REF-walk`, `s_vfs_rename_mutex`), optionally crosses a kernel→userspace FUSE upcall boundary (introducing VM reclaim feedback loops), and terminates in a concrete filesystem persistence engine (`ext4`/`jbd2`, `Btrfs`, or `OpenZFS`) whose on-disk checksum, transaction-group, and space-reservation invariants determine both crash atomicity and `ENOSPC` liveness.

## Findings

### 1. Linux VFS Lockless `dcache` `RCU-walk`, `d_seq` Seqlocks, and Rename-Cycle Prevention

*Basis: documentation (`Documentation/filesystems/path-lookup.rst`) + source (`torvalds/linux` @ `4405c18c`: `include/linux/dcache.h`, `fs/dcache.c`, `fs/namei.c`) + execution (Probe 2A).*

#### 1.1 `RCU-walk` Invariants, Dual-Seqlock Validation, and Monotonic `try_to_unlazy` Fallback

On multi-core Linux systems, taking a per-dentry reference count (`dget`/`dput`) or spinlock (`d_lock`) on root `/` and `/usr` dentries during every pathname lookup causes severe cache-line bouncing. Linux's `dcache` eliminates read-side writes via **two-mode path lookup** (`Documentation/filesystems/path-lookup.rst:595-699`):
- **`RCU-walk` (`LOOKUP_RCU`):** Runs entirely inside `rcu_read_lock()`. Invariant: **RCU-walk never sleeps and never writes to any shared dentry/mount cache line** (no `d_lock`, no refcount increment).
- **`REF-walk`:** Traditional reference-counted traversal (`dget`, `mntget`, sleeping allowed). Once a lookup drops from `RCU-walk` to `REF-walk`, it **never transitions back to `RCU-walk`** (`path-lookup.rst:669`).

Each `struct dentry` embeds `seqcount_spinlock_t d_seq` (`include/linux/dcache.h:93-101`), paired with two global seqlocks: `seqlock_t rename_lock` (`dcache.h:249`) and `mount_lock` (`nd->m_seq`). During `RCU-walk`:
1. The lookup samples `nd->seq` from the parent's `d_seq` and searches the lockless RCU hash list (`d_hash`) for the child component.
2. It validates the parent's `d_seq` (`fs/namei.c:1867-1869`) to prove the parent directory did not undergo rename/unlink/rehash while inspecting the child, and checks `dentry->d_seq` on the child when reading `d_inode` / `d_flags`.
3. Whenever `RCU-walk` hits a cache miss, a filesystem requiring blocking permission checks or `->d_revalidate`, or a mountpoint needing automount, it attempts an in-place upgrade to `REF-walk` via `try_to_unlazy(nd)` or `try_to_unlazy_next(nd, dentry)` (`fs/namei.c:941-983`). These call `__legitimize_path(path, seq, mseq)` (`fs/namei.c:871-891`), which atomically checks `m_seq` and `d_seq` *after* acquiring refcounts; if any concurrent rename or unmount raced, legitimization fails and returns `-ECHILD`, causing top-level `path_lookupat` to restart the entire lookup in `REF-walk` mode.

#### 1.2 Why `s_vfs_rename_mutex` and Ancestor-Order Locking Are Mandatory Against Directory Cycles

Moving a directory across two different parents (`rename("/a/b", "/c/d/b")`) creates two hazards: (a) **lock-order AB-BA deadlock** between directory inode mutexes, and (b) **disconnected directory cycle detachment**.

In `fs/namei.c:3753-3847`:
- **Intra-directory fast path (`p1 == p2`, `lock_rename` lines `3790-3793`):** Acquires only `inode_lock_nested(p1->d_inode, I_MUTEX_PARENT)`, bypassing `s_vfs_rename_mutex` completely (similarly `lock_rename_child`, lines `3802-3838`, optimistically checks `READ_ONCE(c1->d_parent) == p2` before touching `s_vfs_rename_mutex`).
- **Cross-directory slow path (`p1 != p2`, `lock_rename` lines `3795-3796`):** Must acquire **`mutex_lock(&p1->d_sb->s_vfs_rename_mutex)`** first, then call `lock_two_directories(p1, p2)` (`lines 3753-3783`):
  1. Walks up from `p1` to root `p`, checking whether `p2` is an ancestor of `p1`; if so, locks `p2` (`I_MUTEX_PARENT`) before `p1` (`I_MUTEX_PARENT2`) and returns the trap child of `p2`.
  2. Otherwise walks up from `p2` to `p`, checking whether `p1` is an ancestor of `p2`; if so, locks `p1` before `p2` and returns the trap child `q` of `p1`.
  3. If both share ancestor `p`, locks `p1` then `p2` and returns `NULL`; if no common ancestor exists (`r != p`), unlocks `s_vfs_rename_mutex` and returns `-EXDEV` (`lines 3779-3782`).

**Why Per-Superblock `s_vfs_rename_mutex` Cannot Be Replaced by Per-Directory Locks Alone (`Basis: source + execution`, Probe 2A):** Suppose thread `T1` executes `rename("/a/b", "/c/d/b")` while `T2` executes `rename("/c/d", "/a/b/d")`. Initially neither `b` nor `d` is an ancestor of the other. Without `s_vfs_rename_mutex`, both `T1` and `T2` pass their `is_subdir` ancestor checks concurrently and update `parent[b] = d` and `parent[d] = b`, producing a detached cyclic component `b <-> d` unreachable from `/` (leaking all inodes and causing infinite parent walks). Holding `s_vfs_rename_mutex` serializes topology mutations across the superblock so whichever thread enters second deterministically observes the ancestor relation and returns `-EINVAL`.

During the actual dentry pointer swap in `__d_move(dentry, target, exchange)` (`fs/dcache.c:3255-3375`), `d_move` / `d_exchange` wrap the update in `write_seqlock(&rename_lock)`, `write_seqcount_begin(&dentry->d_seq)`, and `write_seqcount_begin_nested(&target->d_seq, DENTRY_D_LOCK_NESTED)` (`lines 3292-3293, 3351-3353`), unhash both dentries, mutate `d_parent`/`d_name`, rehash, and end seqcounts. Probe 2A exhaustively evaluates all 20 reader/writer interleavings against `__d_move`: **6/20** schedules yield false `-ENOENT` or torn parent/name reads without seqcount validation, whereas Linux's dual `d_seq` + `rename_lock` protocol reduces surviving torn observations to **0/20**. Additionally, remote/network filesystems calling `d_splice_alias` (`fs/dcache.c:3456-3463`) re-check `d_ancestor(new, dentry)` under `write_seqlock(&rename_lock)` and abort with `-ELOOP` if a server-side directory loop is detected.

#### 1.3 Symlink Loops (`MAXSYMLINKS`) and Scoped `openat2` Confinement (`LOOKUP_BENEATH`)

- **Symlink Depth & Loop Bound (`fs/namei.c:804-810, 1568-1569, 1986-1999`):** `namei.c` increments `nd->total_link_count` on every symlink or automount jump and returns `-ELOOP` once `nd->total_link_count >= MAXSYMLINKS` (40 in Linux). To avoid heap allocation on shallow paths, `nameidata` embeds `EMBEDDED_LEVELS` (2) symlink stack slots (`nd->internal`), dynamically allocating `kmalloc_objs(struct saved, MAXSYMLINKS, ...)` using `GFP_ATOMIC` under `LOOKUP_RCU` (falling back to `try_to_unlazy` + `GFP_KERNEL` on allocation failure).
- **Scoped Confinement (`fs/namei.c:1074-1147`):** For `openat2(2)` flags `RESOLVE_BENEATH` (`LOOKUP_BENEATH`), `RESOLVE_IN_ROOT` (`LOOKUP_IN_ROOT`), `RESOLVE_NO_XDEV` (`LOOKUP_NO_XDEV`), and `RESOLVE_NO_SYMLINKS`, `namei.c` tracks `LOOKUP_IS_SCOPED`, rejects absolute symlinks or `..` escapes out of `nd->root` with `-EXDEV`, and cross-checks `path_is_under` / `rename_lock` so a concurrent `rename()` moving an active directory above the confinement root cannot smuggle a process out of the sandbox!

---

### 2. SibylFS Executable POSIX Oracle Specification and Cross-OS Divergences

*Basis: normative (`IEEE Std 1003.1-2024`, SOSP 2015 paper) + source (`sibylfs/sibylfs_src` @ `30675bc3`).*

Prose POSIX specifications (`IEEE Std 1003.1-2024`, Base Specifications Issue 8) leave numerous corners intentionally implementation-defined or nondeterministic, while real filesystems violate even unambiguous POSIX rules for historical compatibility. Testing a filesystem against a single "reference" implementation (point-equality differential testing) falsely flags valid nondeterministic behaviors and misses shared bugs.

`SibylFS` (`sibylfs/sibylfs_src`, Ridge et al., SOSP 2015) resolves this via a **mechanized, set-valued small-step operational semantics** written in Lem (`fs_spec/src/t_fs_spec.lem_cppo`), extracted to OCaml for automated trace checking and to Isabelle/HOL/Coq for theorem proving:

```ocaml
(* sibylfs/sibylfs_src @ 30675bc3, fs_spec/src/t_fs_spec.lem_cppo:4483-4492 *)
val fs_trans: forall 'dir_ref 'file_ref 'impl.
   environment 'dir_ref 'file_ref 'impl ->
   'impl ->
   ty_fs_command 'dir_ref 'file_ref ->
   finset (monad_state 'impl ret_value)
let fs_trans env s0 cmd = (
  let m = ty_fs_command_to_fsmonad env cmd in
  let rs = run_fsmonad m s0 in
  rs)
```

Key architectural properties observed in `t_fs_spec.lem_cppo`:
1. **Relational (`finset`) Trace Adjudication (`lines 4483-4492, 5506-5683`):** Every syscall transition returns a **finite set** of permitted `(post_state, return_value_or_errno)` pairs, wrapped in a multi-process labeled transition system `os_trans` (`line 5683`) supporting process creation/destruction (`os_trans_pcreate_destroy`) and silent internal steps (`os_trans_tau`). A real execution trace passes the oracle iff at least one valid path remains in the symbolic state set after consuming every observed `(call, return)` event.
2. **Explicit Architecture Parameterization (`lines 908-922`):** Rather than conflating POSIX with Linux, `t_fs_spec.lem_cppo` defines `type ty_arch = ARCH_LINUX | ARCH_POSIX | ARCH_MAC_OS_X | ARCH_FREEBSD` with a trait record `architecture` capturing platform-specific allowances (e.g., `arch_abs_path_slash_slash` for POSIX's implementation-defined `//` leading double-slash, OS-specific `open` flag mappings, and seek semantics).
3. **Normative POSIX.1-2024 Path/Symlink Semantics vs. Real-World Divergences:**

| Syscall / Edge Case | Normative POSIX.1-2024 (`IEEE Std 1003.1-2024`) | Observed Implementation / SibylFS Divergence (`t_fs_spec.lem_cppo` + SOSP 2015) |
|---|---|---|
| `open(sym, O_NOFOLLOW \| O_WRONLY)` | Must fail with `ELOOP` (`t_fs_spec.lem_cppo:2107`) | FreeBSD historically returned `EMLINK`; `t_fs_spec.lem_cppo:3040` explicitly notes macOS HFS+ non-POSIX behavior (`hfsplus_loop/open/...`) |
| `unlink(sym)` vs. `unlink("loop/x")` | `unlink(sym)` removes symlink itself without following; prefix loop returns `ELOOP` (`SC_SYMLOOP_MAX`, `t_fs_spec.lem_cppo:2213`) | Consistent across Linux/BSD/macOS on final component, but trailing slash (`unlink("sym/")`) diverges (`ENOTDIR` vs `EISDIR` vs `ENOENT`) |
| `symlink(target, linkpath)` | `target` is stored as raw string (never resolved); prefix of `linkpath` is resolved (can fail with `ELOOP`) | Empty `target` `""` rejected on Linux (`ENOENT`) in historical kernels vs permitted on some BSDs |
| `rename(old, new)` over non-empty dir | Permits **either** `EEXIST` or `ENOTEMPTY` | Linux returns `ENOTEMPTY`, Solaris/some POSIX stacks return `EEXIST`; SibylFS's `finset` accepts both |
| Multi-error precedence (e.g., `EACCES` + `ENOENT` + `ENOTDIR`) | Unspecified which applicable errno is returned | Linux `ext4`/`tmpfs`/`btrfs`, macOS `HFS+`, and FreeBSD `UFS` check permissions vs path existence in different orders; requires set-valued oracle |
| `O_CREAT \| O_EXCL` on dangling symlink | Must fail with `EEXIST` (do not follow dangling symlink) | Historically misimplemented in several FUSE/network filesystems that follow before checking `O_EXCL` |

---

### 3. FUSE Upcalls and Kernel Dirty-Page Memory-Reclaim Writeback Deadlocks

*Basis: source (`torvalds/linux` @ `4405c18c`: `fs/fuse/file.c`, `fs/fuse/inode.c`; `libfuse/libfuse` @ `6a484ac6`: `include/fuse_kernel.h`).*

#### 3.1 Anatomy of the Kernel↔Userspace Reclaim Deadlock

When a FUSE daemon negotiates `FUSE_WRITEBACK_CACHE` (`libfuse/include/fuse_kernel.h:430, 484`, protocol 7.23+), `write(2)` calls dirty kernel page-cache folios rather than issuing synchronous `FUSE_WRITE` upcalls. Flushing those dirty folios requires sending `FUSE_WRITE` requests over `/dev/fuse` to a **userspace daemon**, which may perform arbitrary heap allocations, page faults, socket sends, or disk I/O before replying. This creates a **circular dependency under memory pressure**:

```text
  [Kernel MM Direct Reclaim / kswapd]
        │  1. Needs free RAM; waits on FUSE folio marked PG_writeback
        ▼
  [FUSE Writeback Queue (/dev/fuse)]
        │  2. Sends FUSE_WRITE upcall to userspace FUSE daemon
        ▼
  [Userspace FUSE Daemon Process]
        │  3. Calls malloc() / page-faults / allocates socket skb -> GFP_KERNEL
        ▼
  [Kernel MM Direct Reclaim]  ──► DEADLOCK (waits on step 1!)
```

A second deadlock path occurs on `fuse_send_writepage` itself (`fs/fuse/file.c:1995-2000`): allocating the background request struct with `GFP_KERNEL` inside writeback could recurse back into filesystem reclaim. Notice `fs/fuse/file.c:150` also flags a `no_open` reclaim hazard (`fc->no_open` must handle release/reclaim without blocking).

#### 3.2 Architectural Evolution: Bounce-Page Copying vs. `AS_WRITEBACK_MAY_DEADLOCK_ON_RECLAIM`

| Mechanism | Historical Linux FUSE (Pre-6.13/6.15) | Modern Upstream Linux FUSE (`torvalds/linux` @ `4405c18c`) |
|---|---|---|
| **Writeback folio ownership** | Allocated a temporary bounce page per dirty page, copied payload, immediately called `end_page_writeback()` on the cache page | Submits original page-cache folios directly via `iomap_writepages(&wpc)` (`fs/fuse/file.c:2327-2354`); ends writeback in `fuse_writepage_finish` via `iomap_finish_folio_write` (`line 1959`) only upon daemon reply |
| **Memory-reclaim deadlock guard** | Cache page was no longer `PG_writeback`, so reclaim never waited on daemon (but allocating bounce pages itself pressured RAM under OOM!) | `fuse_init_file_inode` calls `mapping_set_writeback_may_deadlock_on_reclaim(&inode->i_data)` (`fs/fuse/file.c:3176-3177`), instructing VM reclaim not to synchronously stall waiting on these writeback folios |
| **Dirty-ratio containment** | `BDI_CAP_STRICTLIMIT` capping dirty + writeback to 1% | Retained: `sb->s_bdi->capabilities |= BDI_CAP_STRICTLIMIT` (`fs/fuse/inode.c:1595-1602`, comments: `max 1% of dirty + writeback threshold`) |
| **Background queue throttling** | `max_background` & `congestion_threshold` | Retained: non-`CAP_SYS_ADMIN` clamped to `max_user_bgreq` / `max_user_congthresh` (`fs/fuse/inode.c:1266-1280`); `WB_SYNC_NONE` returns `0` immediately when `fuse_chan_num_background >= congestion_threshold` (`fs/fuse/file.c:2349-2351`) |
| **Request allocation safety** | `GFP_NOFS` / `GFP_ATOMIC` | `fuse_send_writepage` tries `GFP_ATOMIC`, then falls back to `GFP_NOFS \| __GFP_NOFAIL` (`fs/fuse/file.c:1995-2000`) |
| **Passthrough interaction** | N/A | `FUSE_PASSTHROUGH` (protocol 7.40+, `fuse_kernel.h:216, 506`) is **mutually exclusive** with `FUSE_WRITEBACK_CACHE` (`fs/fuse/inode.c:1415-1424`) |

**Unprivileged Containment Invariant (`Basis: source`):** Because an unprivileged user can mount a FUSE filesystem (via `fusermount3` or user namespaces) and deliberately stall replies to `FUSE_WRITE`, `BDI_CAP_STRICTLIMIT` (1% dirty+writeback cap) and unprivileged `max_user_bgreq` / `max_user_congthresh` caps are security-critical DoS boundaries preventing a single hung FUSE daemon from pinning global page-cache dirty ratios and starving unrelated processes.

---

### 4. Copy-on-Write Checksummed Trees (`Btrfs` & `OpenZFS`), `ext4`/`jbd2`, and the `ENOSPC` Deletion Paradox

*Basis: normative (ACM TOS 2013 paper) + source (`torvalds/linux` @ `4405c18c`: `fs/btrfs/`, `fs/jbd2/`; `openzfs/zfs` @ `cde5d598`: `include/sys/spa.h`, `module/zfs/{txg,zil,spa_misc,dsl_pool}.c`) + execution (Probe 2B).*

#### 4.1 Merkle Checksums, Crash Atomicity, and Write-Ahead Journaling Compared

| Architectural Dimension | OpenZFS (`openzfs/zfs` @ `cde5d598`) | Btrfs (`torvalds/linux` @ `4405c18c`) | `ext4` + `jbd2` (`torvalds/linux` @ `4405c18c`) |
|---|---|---|---|
| **Update Discipline** | Copy-on-Write DMU object tree (no overwrite of live blocks) | Reference-counted CoW B-trees (`BTRFS_MAX_LEVEL = 8`, `btrfs_ctree.h:50`) | In-place overwrite + write-ahead physical redo journal (`jbd2`) |
| **Checksum Placement & Threat Model** | **True Merkle tree:** 128-byte parent `blkptr_t` (`spa.h:389-397`) stores 256-bit `zio_cksum_t blk_cksum` of child + `BP_GET_CHECKSUM` + up to 3 `dva_t`s (detects bit-rot, torn writes, **and misdirected/phantom writes**) | Metadata: self-checksum in `btrfs_header` + parent-checked `generation` (detects misdirected metadata writes). Data: checksums stored separately in CoW `csum_tree` (`btrfs_fs.h:894`) | Optional metadata checksums (`metadata_csum`) + journal checksums; **no end-to-end user-data checksums** |
| **Atomic Commit Protocol** | Pipelined 3-state **Transaction Groups (`TXG`)**: `open -> quiescing -> syncing` (`txg.c:30-95`). Multi-pass sync converges by deferring frees, stopping compression, and overwriting same-TXG-freed blocks before atomic uberblock switch | CoW transaction commit atomically updates superblock root pointers; delayed references (`delayed_refs_rsv`) batch extent-tree updates | `jbd2_journal_commit_transaction` (`jbd2/commit.c:376-1157`): `T_LOCKED -> T_FLUSH -> T_COMMIT -> T_COMMIT_DFLUSH -> T_COMMIT_JFLUSH -> T_COMMIT_CALLBACK` |
| **Low-Latency `fsync()` Fast Path** | Per-dataset **ZFS Intent Log (`ZIL`)** (`zil.c:50-87`): dynamically allocated chained `lwb` blocks (preferring dedicated `SLOG` vdev), each holding a `blkptr_t` to the next `lwb`; replayed only on crash before TXG syncs | Per-subvolume **tree-log** (`BTRFS_TREE_LOG_OBJECTID`, `treelog_rsv`, `block-rsv.c:429-430`) flushed without full transaction commit | `jbd2` Fast Commit (`JBD2_FAST_COMMIT_ONGOING`, `jbd2/commit.c:438-453`) or full journal commit (ordered data flush first in `data=ordered`) |
| **100%-Full `unlink()` `ENOSPC` Mitigation** | Tiered `spa_slop_space` (`spa_misc.c:348-384, 2075-2107`; `dsl_pool.c:943-973`) | Pre-reserved `global_block_rsv` (`SZ_512M` cap, `block-rsv.c:316-398`) + `btrfs_start_transaction_fallback_global_rsv` (`btrfs_inode.c:4482-4488`) | In-place update needs zero new data/tree blocks; only bounded `jbd2` journal credits (preallocated journal ring) |

#### 4.2 Mathematical Anatomy of the 100%-Full CoW `unlink()` `ENOSPC` Paradox

On a CoW B-tree, deleting a file (`unlink(2)`) **cannot overwrite metadata in place** without breaking crash atomicity (or mutating blocks shared with snapshots). Consequently, `unlink()` must allocate fresh CoW blocks for every modified node from leaf to root across the filesystem tree, extent/free-space trees, and orphan items **before** the committing transaction can safely release the unlinked file's old metadata and data extents.

1. **Btrfs `GlobalReserve` Mechanism (`fs/btrfs/block-rsv.c:316-398`, `fs/btrfs/inode.c:4482-4529`, `fs/btrfs/fs.h:112, 1046-1056`):**
   - `btrfs_unlink` starts its transaction via `__unlink_start_trans` -> `btrfs_start_transaction_fallback_global_rsv(root, BTRFS_UNLINK_METADATA_UNITS)` where `BTRFS_UNLINK_METADATA_UNITS = 6`.
   - `btrfs_calc_metadata_size` (`btrfs_fs.h:1056`) computes `nodesize * BTRFS_MAX_LEVEL * num_items`. At default `nodesize = 16 KiB` and `BTRFS_MAX_LEVEL = 8`, a single worst-case unlink requires **`16 KiB × 8 × 6 = 768 KiB` (`786,432` bytes)** of transient metadata space!
   - `btrfs_update_global_block_rsv` (`block-rsv.c:316-398`) sizes `fs_info->global_block_rsv` dynamically from metadata tree footprints (including `min_items += BTRFS_UNLINK_METADATA_UNITS`, lines `372-383`), capped at `SZ_512M` (`512 MiB`, line `388`), and charges it to `space_info->bytes_may_use`. Normal writes observe `ENOSPC` once unreserved metadata runs out, leaving `global_block_rsv` intact so `btrfs_unlink` can fall back to it and reclaim disk space.

2. **OpenZFS Tiered `spa_slop_space` Architecture (`module/zfs/spa_misc.c:348-384, 2075-2107`, `module/zfs/dsl_pool.c:943-983`):**
   - `spa_get_slop_space` computes:
     $$\text{slop} = \max\!\Big(\min(\text{space} \gg 5,\; 128\text{ GiB}) - \min(\text{embedded\_log},\; \text{slop}_0 / 2),\; \min(\text{space}/2,\; 128\text{ MiB})\Big)$$
     with `spa_slop_shift = 5` ($1/32 = 3.125\%$), `spa_min_slop = 128 MiB`, and `spa_max_slop = 128 GiB`.
   - `dsl_pool_adjustedsize(dp, slop_policy)` (`dsl_pool.c:943-973`) enforces four strictly nested space-credit tiers (subtracting `spa_get_checkpoint_space` and `spa_deferred_frees` first):
     - **`ZFS_SPACE_CHECK_NORMAL` (`resv = slop`):** Regular `write`/`create` hits `ENOSPC` when free space drops below `slop` (`3.125%` on 64 GiB–1 TiB pools; `12.5%` on 1 GiB; `50%` on 100 MiB; `0.12%` on 100 TiB; Probe 2B).
     - **`ZFS_SPACE_CHECK_RESERVED` (`resv = slop >> 1`):** `unlink()` and most admin commands can burn up to **half** of `slop`, only returning `ENOSPC` below `slop / 2`.
     - **`ZFS_SPACE_CHECK_EXTRA_RESERVED` (`resv = slop >> 2`):** Operations almost guaranteed to reclaim space (`zfs destroy`) can burn up to **three-quarters** of `slop`, leaving `slop / 4` as final safety margin.
     - **`ZFS_SPACE_CHECK_NONE` (`resv = 0`):** Emergency `dsl_sync_task`s always run; `spa_misc.c:367-369` explicitly warns that if a `CHECK_NONE` operation causes a net space increase, the pool can hit 0 physical free bytes and lock up permanently read-only!

3. **The Snapshot-Pinned Paradox (`Basis: source + execution`, Probe 2B):**
   Both Btrfs's `GlobalReserve` and OpenZFS's `slop/2` tier break down if a **live snapshot pins all extents of the files being unlinked**! In that regime, every `unlink()` allocates fresh CoW B-tree nodes in the active dataset to record the deletion while freeing **zero** physical data blocks or old tree nodes at commit (because the snapshot still references them). Probe 2B demonstrates that on a 100%-full volume with snapshot-pinned files, a 16 MiB `GlobalReserve` exhausts to `ENOSPC` after only **21** worst-case unlinks, and a 64 GiB OpenZFS pool's `slop/2` (1024 MiB) exhausts after **1,365** unlinks! This explains both why `rm` can still fail with `ENOSPC` on snapshot-heavy CoW volumes and why OpenZFS specifically reserves the deeper `ZFS_SPACE_CHECK_EXTRA_RESERVED` (`3/4 * slop`) credit tier to allow `zfs destroy <snapshot>` (or `truncate -s 0` / Btrfs subvolume deletion) to recover the pool.

## Boundaries

- **POSIX Crash-Consistency (`fsync` / `rename` / directory persistence) Beyond Single-Crash-Free Traces (`not examined`):** `SibylFS` (`sibylfs/sibylfs_src` @ `30675bc3`) specifies runtime POSIX syscall semantics across normal executions (`os_trans`); power-loss crash-consistency models (e.g., `CrashMonkey`, `FSCQ`, `Yggdrasil`, disk write-reordering barriers `REQ_PREFLUSH`/`REQ_FUA`) and `ext4` `data=journal` vs. `data=writeback` crash anomalies were **not examined** in depth here.
- **Linux `io_uring` / `FUSE-over-io_uring` Zero-Copy and `FUSE_VDAX` (`not examined`):** While `libfuse/include/fuse_kernel.h:394` (`FOPEN_IO_URING_ZERO_COPY`) and `torvalds/linux/fs/fuse/file.c:3186-3189` (`FUSE_IS_VDAX`) appear in the pinned revisions, their memory-reclaim and page-pinning interactions were **not examined**; Section 3 findings apply specifically to standard `/dev/fuse` `FUSE_WRITEBACK_CACHE` buffered writeback.
- **Linux VFS OverlayFS, FUSE `d_revalidate` Stale Negative Dentries, and NFS Re-export Loops (`not examined`):** Findings on Linux `dcache` `RCU-walk` and `rename_lock` cover core VFS (`fs/namei.c`, `fs/dcache.c`); filesystem-specific `d_op->d_revalidate` behaviors on networked or stacked filesystems (`overlayfs`, `nfs`, `ceph`) were **not examined**.
- **Btrfs Chunk Allocation Metadata/Data Split (`ENOSPC` With Unallocated Data Space) (`known not to apply` to simple free-byte sums):** In Btrfs, metadata and data occupy separate block groups (`BTRFS_BLOCK_GROUP_METADATA` vs. `BTRFS_BLOCK_GROUP_DATA`, `btrfs_block-rsv.c:445-456`). Consequently, `btrfs_unlink` can hit `ENOSPC` even when `df` shows gigabytes of free *data* space if 100% of raw device chunks are allocated to data block groups and no unallocated chunk exists to grow metadata block groups (requiring `btrfs balance` or empty-block-group reclamation). OpenZFS avoids this specific split by allocating metadata and data dynamically from unified metaslabs.
- **ZFS Pool Checkpoints & Deferred Frees (`unknown` exact worst-case bound under fragmentation):** `dsl_pool_adjustedsize` (`dsl_pool.c:947-951`) subtracts both `spa_get_checkpoint_space` and `spa_deferred_bpobj.bpo_phys->bpo_bytes` before applying slop tiers; exact worst-case `zfs destroy` metadata amplification under severe gang-block fragmentation (`DVA_GET_GANG`) is workload-dependent and **unknown** from static source inspection alone.
- **Attractive Stronger Conclusion Not Established:** Eliminating bounce-page copying via `mapping_set_writeback_may_deadlock_on_reclaim` prevents kernel direct reclaim from deadlocking on FUSE writeback folios, but does **not** make an unprivileged FUSE daemon immune to self-deadlock if the daemon performs blocking filesystem I/O back onto its own mountpoint or exhausts userspace memory while holding internal daemon locks needed to complete `FUSE_WRITE`.

## Evidence

### Primary Repositories Inspected (All Acquired `2026-11-19`)

1. **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:**
   - `Documentation/filesystems/path-lookup.rst:151`, `217-242` (`rename_lock`), `595-699` (`RCU-walk` invariants and monotonic `REF-walk` fallback).
   - `include/linux/dcache.h:93-101` (`struct dentry`, `seqcount_spinlock_t d_seq`), `249` (`extern seqlock_t rename_lock`).
   - `fs/namei.c:804-810` (`MAXSYMLINKS` stack allocation), `871-983` (`__legitimize_path`, `try_to_unlazy`, `try_to_unlazy_next`), `1074-1147` (`LOOKUP_IS_SCOPED`, `LOOKUP_BENEATH`, `LOOKUP_NO_XDEV`), `1568-1569` & `1986-1999` (`MAXSYMLINKS` -> `-ELOOP`), `3753-3847` (`lock_two_directories`, `lock_rename`, `lock_rename_child`, `s_vfs_rename_mutex`, `unlock_rename`).
   - `fs/dcache.c:3255-3375` (`__d_move`, `d_move`, `d_exchange`, `write_seqlock(&rename_lock)`, `write_seqcount_begin(&dentry->d_seq)`), `3455-3485` (`d_ancestor` loop check returning `-ELOOP`).
   - `fs/fuse/file.c:150` (`no_open` reclaim comment), `1953-2014` (`fuse_writepage_finish`, `iomap_finish_folio_write`, `fuse_send_writepage` `GFP_ATOMIC` -> `GFP_NOFS | __GFP_NOFAIL`), `2260-2354` (`fuse_iomap_writeback_range`, `fuse_writepages`, `congestion_threshold` check), `3168-3185` (`fuse_init_file_inode`, `mapping_set_writeback_may_deadlock_on_reclaim`).
   - `fs/fuse/inode.c:987`, `1266-1280` (`max_background`, `congestion_threshold`, non-`CAP_SYS_ADMIN` clamp), `1357-1358` (`FUSE_WRITEBACK_CACHE`), `1415-1430` (`FUSE_PASSTHROUGH` vs `FUSE_WRITEBACK_CACHE` mutual exclusion), `1595-1602` (`BDI_CAP_STRICTLIMIT`, 1% dirty+writeback cap).
   - `fs/btrfs/fs.h:112` (`BTRFS_UNLINK_METADATA_UNITS = 6`), `544` (`global_block_rsv`), `894` (`csum_size`), `1046-1056` (`nodesize * BTRFS_MAX_LEVEL * ...`).
   - `fs/btrfs/ctree.h:50-60` (`BTRFS_MAX_LEVEL`), `486` (`btrfs_header`).
   - `fs/btrfs/block-rsv.c:289-398` (`btrfs_block_rsv_use_bytes`, `btrfs_update_global_block_rsv`, `SZ_512M` cap, `min_items += BTRFS_UNLINK_METADATA_UNITS`), `429-466` (`treelog_rsv`, `btrfs_init_global_block_rsv`).
   - `fs/btrfs/inode.c:4482-4529` (`__unlink_start_trans`, `btrfs_start_transaction_fallback_global_rsv`, `btrfs_unlink`).
   - `fs/jbd2/commit.c:376-1157` (`jbd2_journal_commit_transaction`, `T_LOCKED -> T_FLUSH -> T_COMMIT -> T_COMMIT_DFLUSH -> T_COMMIT_JFLUSH -> T_COMMIT_CALLBACK`, `JBD2_FAST_COMMIT_ONGOING`).
2. **`sibylfs/sibylfs_src` @ `30675bc3b91e73f7133d0c30f18857bb1f4df8fa`:**
   - `fs_spec/src/t_fs_spec.lem_cppo:194` (`ELOOP`), `908-922` (`ty_arch`, `architecture`), `2107`, `2213` (`SC_SYMLOOP_MAX`), `3040` (`O_NOFOLLOW` + macOS HFS+ divergence note), `4483-4492` (`fs_trans` returning `finset`), `5506-5683` (`os_trans`).
3. **`libfuse/libfuse` @ `6a484ac67fba410d722473e5e107da9b804fc40d`:**
   - `include/fuse_kernel.h:136-142` (protocol 7.23 `FUSE_WRITEBACK_CACHE`), `215-220` (protocol 7.40 `FUSE_PASSTHROUGH`), `390-396` (`FOPEN_*`), `429-511` (`FUSE_WRITEBACK_CACHE`, `FUSE_PASSTHROUGH`, `FUSE_HAS_RESEND`), `919-936` (`fuse_init_in`, `fuse_init_out`).
4. **`openzfs/zfs` @ `cde5d598eb44b5d6efe8167666d988a496346657`:**
   - `include/sys/spa.h:389-458` (`blkptr_t`, `dva_t`, `DVA_GET_GANG`, `zio_cksum_t blk_cksum`, `BP_GET_CHECKSUM`).
   - `module/zfs/txg.c:30-95` (`TXG` open/quiescing/syncing pipeline and multi-pass convergence).
   - `module/zfs/zil.c:50-87` (per-dataset `ZIL` header, chained `lwb` `blkptr_t`s, `SLOG` allocation, `zfs_commit_timeout_pct`).
   - `module/zfs/spa_misc.c:348-384` (`spa_slop_shift = 5`, `spa_min_slop = 128 MiB`, `spa_max_slop = 128 GiB`, tiered slop rationale), `2075-2107` (`spa_get_slop_space`).
   - `module/zfs/dsl_pool.c:943-983` (`dsl_pool_adjustedsize`, `ZFS_SPACE_CHECK_NORMAL`/`RESERVED`/`EXTRA_RESERVED`/`NONE`, `dsl_pool_unreserved_space`).

### Executable Micro-Probes and Recorded Outputs (`2026-11-19`, Python 3, Linux x86_64)

#### Probe 2A: Cross-Directory Rename Cycle Detachment and RCU-Walk `d_seq`/`rename_lock` Validation

```python
# Save as /tmp/probe_vfs_rename_rcu.py and run: python3 /tmp/probe_vfs_rename_rcu.py
def is_ancestor(pm, anc, node):
    cur, seen = node, set()
    while True:
        if cur == anc: return True
        if cur in seen or pm[cur] == cur: return False
        seen.add(cur); cur = pm[cur]

def has_cycle(pm, root="/"):
    for n in pm:
        cur, seen = n, set()
        while cur != root:
            if cur in seen: return True, f"cycle containing {cur}"
            seen.add(cur); cur = pm[cur]
    return False, "acyclic tree rooted at /"

tree = {"/": "/", "a": "/", "b": "a", "c": "/", "d": "c"}
t1, t2 = is_ancestor(tree, "b", "d"), is_ancestor(tree, "d", "b")
print("=== 1. Concurrent Cross-Directory Rename Cycle Detachment ===")
print(f"Unsynchronized: T1 is_ancestor(b, d)={t1}, T2 is_ancestor(d, b)={t2} (both pass!)")
tree["b"], tree["d"] = "d", "b"
cyc, msg = has_cycle(tree)
print(f"After concurrent moves without s_vfs_rename_mutex: detached_cycle={cyc} ({msg}), tree={tree}")
for first in ("T1_first", "T2_first"):
    t = {"/": "/", "a": "/", "b": "a", "c": "/", "d": "c"}
    if first == "T1_first":
        if not is_ancestor(t, "b", "d"): t["b"] = "d"
        blk = is_ancestor(t, "d", "b")
        print(f"Serialized ({first}): T2 rejected with EINVAL={blk}, result={has_cycle(t)[1]}")
    else:
        if not is_ancestor(t, "d", "b"): t["d"] = "b"
        blk = is_ancestor(t, "b", "d")
        print(f"Serialized ({first}): T1 rejected with EINVAL={blk}, result={has_cycle(t)[1]}")

states = [
    {"step": 0, "rseq": 0, "dseq": 0, "hashed": True,  "parent": "dir1", "name": "foo"},
    {"step": 1, "rseq": 1, "dseq": 1, "hashed": False, "parent": "dir1", "name": "foo"},
    {"step": 2, "rseq": 1, "dseq": 1, "hashed": True,  "parent": "dir2", "name": "bar"},
    {"step": 3, "rseq": 2, "dseq": 2, "hashed": True,  "parent": "dir2", "name": "bar"},
]
bad_no_seq = bad_with_seq = total = 0
for i in range(4):
    for j in range(i, 4):
        for k in range(j, 4):
            total += 1
            si, sj, sk = states[i], states[j], states[k]
            if not (sj["hashed"] and sj["parent"] == "dir1" and sj["name"] == "foo") and sj["step"] == 1:
                bad_no_seq += 1
            if si["rseq"] % 2 == 0 and sk["rseq"] == si["rseq"] and sj["dseq"] % 2 == 0 and sk["dseq"] == sj["dseq"]:
                if sj["step"] in (1, 2): bad_with_seq += 1
print(f"\n=== 2. RCU-Walk Lookup vs Concurrent __d_move (d_seq & rename_lock) ===\nSchedules tested: {total}")
print(f"  False ENOENT / torn read without seqcount+rename_lock: {bad_no_seq}/{total}")
print(f"  Torn observations surviving Linux d_seq+rename_lock   : {bad_with_seq}/{total}")
```

Recorded output (`exit 0`):
```text
=== 1. Concurrent Cross-Directory Rename Cycle Detachment ===
Unsynchronized: T1 is_ancestor(b, d)=False, T2 is_ancestor(d, b)=False (both pass!)
After concurrent moves without s_vfs_rename_mutex: detached_cycle=True (cycle containing b), tree={'/': '/', 'a': '/', 'b': 'd', 'c': '/', 'd': 'b'}
Serialized (T1_first): T2 rejected with EINVAL=True, result=acyclic tree rooted at /
Serialized (T2_first): T1 rejected with EINVAL=True, result=acyclic tree rooted at /

=== 2. RCU-Walk Lookup vs Concurrent __d_move (d_seq & rename_lock) ===
Schedules tested: 20
  False ENOENT / torn read without seqcount+rename_lock: 6/20
  Torn observations surviving Linux d_seq+rename_lock   : 0/20
```

#### Probe 2B: CoW `unlink()` `ENOSPC` Paradox, Btrfs `GlobalReserve`, and OpenZFS `spa_slop_space`

```python
# Save as /tmp/probe_cow_enospc.py and run: python3 /tmp/probe_cow_enospc.py
SPA_SLOP_SHIFT, SPA_MIN_SLOP, SPA_MAX_SLOP = 5, 128<<20, 128<<30
def zfs_slop(sz, emb=0):
    sl = min(sz >> SPA_SLOP_SHIFT, SPA_MAX_SLOP)
    sl -= min(emb, sl >> 1)
    return max(sl, min(sz >> 1, SPA_MIN_SLOP))

btrfs_unlink = (16<<10) * 8 * 6  # nodesize * BTRFS_MAX_LEVEL * BTRFS_UNLINK_METADATA_UNITS = 768 KiB
def sim(free_b, resv_b, cow_b, file_b, pinned, n):
    phys = resv_b  # volume filled to 100% of normal usable space
    for i in range(n):
        if phys < cow_b: return i, phys, "ENOSPC"
        phys -= cow_b
        if not pinned: phys += cow_b + file_b
    return n, phys, "OK"

print("=== 1. OpenZFS Tiered Slop-Space Reserve Across Pool Sizes ===")
print(f"{'Pool Size':>12} | {'Slop (NORMAL)':>14} | {'Unlink (slop/2)':>15} | {'Destroy (3/4)':>14} | {'Slop %':>7}")
for label, sz in [("100 MiB", 100<<20), ("1 GiB", 1<<30), ("64 GiB", 64<<30), ("1 TiB", 1<<40), ("16 TiB", 16<<40), ("100 TiB", 100<<40)]:
    sl = zfs_slop(sz)
    print(f"{label:>12} | {sl/(1<<20):10.1f} MiB | {(sl>>1)/(1<<20):11.1f} MiB | {(sl-(sl>>2))/(1<<20):10.1f} MiB | {100.0*sl/sz:6.2f}%")
print("\n=== 2. Btrfs CoW Unlink Transient Metadata Reserve ===")
print(f"nodesize=16 KiB, BTRFS_MAX_LEVEL=8, BTRFS_UNLINK_METADATA_UNITS=6\nWorst-case single unlink reservation: {btrfs_unlink//1024} KiB ({btrfs_unlink:,} bytes)\nglobal_block_rsv hard cap (SZ_512M) : 512 MiB")
print("\n=== 3. CoW Volume at 100% Normal Capacity: Unlink Outcome ===")
for label, resv, pinned in [
    ("No reserve (0 B), unpinned", 0, False),
    ("Btrfs GlobalReserve (16 MiB), unpinned", 16<<20, False),
    ("Btrfs GlobalReserve (16 MiB), SNAPSHOT-PINNED", 16<<20, True),
    ("OpenZFS 64 GiB pool slop/2 (1024 MiB), SNAPSHOT-PINNED", zfs_slop(64<<30)>>1, True),
]:
    ok, rem, st = sim(64<<30, resv, btrfs_unlink, 1<<20, pinned, 2000)
    print(f"  {label:56s} -> unlinks={ok:4d}/2000, status={st}, phys_free={rem/(1<<20):7.2f} MiB")
```

Recorded output (`exit 0`):
```text
=== 1. OpenZFS Tiered Slop-Space Reserve Across Pool Sizes ===
   Pool Size |  Slop (NORMAL) | Unlink (slop/2) |  Destroy (3/4) |  Slop %
     100 MiB |       50.0 MiB |        25.0 MiB |       37.5 MiB |  50.00%
       1 GiB |      128.0 MiB |        64.0 MiB |       96.0 MiB |  12.50%
      64 GiB |     2048.0 MiB |      1024.0 MiB |     1536.0 MiB |   3.12%
       1 TiB |    32768.0 MiB |     16384.0 MiB |    24576.0 MiB |   3.12%
      16 TiB |   131072.0 MiB |     65536.0 MiB |    98304.0 MiB |   0.78%
     100 TiB |   131072.0 MiB |     65536.0 MiB |    98304.0 MiB |   0.12%

=== 2. Btrfs CoW Unlink Transient Metadata Reserve ===
nodesize=16 KiB, BTRFS_MAX_LEVEL=8, BTRFS_UNLINK_METADATA_UNITS=6
Worst-case single unlink reservation: 768 KiB (786,432 bytes)
global_block_rsv hard cap (SZ_512M) : 512 MiB

=== 3. CoW Volume at 100% Normal Capacity: Unlink Outcome ===
  No reserve (0 B), unpinned                               -> unlinks=   0/2000, status=ENOSPC, phys_free=   0.00 MiB
  Btrfs GlobalReserve (16 MiB), unpinned                   -> unlinks=2000/2000, status=OK, phys_free=2016.00 MiB
  Btrfs GlobalReserve (16 MiB), SNAPSHOT-PINNED            -> unlinks=  21/2000, status=ENOSPC, phys_free=   0.25 MiB
  OpenZFS 64 GiB pool slop/2 (1024 MiB), SNAPSHOT-PINNED   -> unlinks=1365/2000, status=ENOSPC, phys_free=   0.25 MiB
```

## Revalidation

1. **Upstream Kernel & Storage Source Checks:**
   - **Linux VFS (`torvalds/linux`):** Diff `fs/namei.c` (`lock_rename`, `lock_two_directories`, `try_to_unlazy`, `LOOKUP_BENEATH`) and `fs/dcache.c` (`__d_move`). Any future attempt to replace per-superblock `s_vfs_rename_mutex` with finer-grained directory locking requires re-checking cycle-detachment soundness (Probe 2A).
   - **Linux FUSE (`torvalds/linux` & `libfuse/libfuse`):** Check `fs/fuse/file.c` (`mapping_set_writeback_may_deadlock_on_reclaim`, `fuse_writepages`, `fuse_send_writepage`) and `fs/fuse/inode.c` (`BDI_CAP_STRICTLIMIT`, `FUSE_PASSTHROUGH` vs. `FUSE_WRITEBACK_CACHE` check). If future Linux kernels allow `FUSE_PASSTHROUGH` alongside `FUSE_WRITEBACK_CACHE`, re-evaluate the mutual-exclusion note.
   - **Btrfs & OpenZFS Space Credits:** Diff `fs/btrfs/block-rsv.c` (`btrfs_update_global_block_rsv`, `SZ_512M`), `fs/btrfs/fs.h` (`BTRFS_UNLINK_METADATA_UNITS`), `module/zfs/spa_misc.c` (`spa_slop_shift`, `spa_min_slop`, `spa_max_slop`, `spa_get_slop_space`), and `module/zfs/dsl_pool.c` (`dsl_pool_adjustedsize`).
2. **Executable Probes & Full Oracle Testing:**
   - Re-run Probes 2A and 2B (`python3 /tmp/probe_vfs_rename_rcu.py && python3 /tmp/probe_cow_enospc.py`) whenever evaluating modified rename locking rules or alternative CoW reserve formulas.
   - Because Probe 2B models metadata reservations analytically, validating live `ENOSPC` unlink recovery on a concrete filesystem build requires running loop-device fill-and-unlink tests (e.g., `xfstests` `btrfs/*` ENOSPC cases or OpenZFS `zfs-tests` `slop_space` cases) alongside `sibylfs` trace suites against the target kernel build.
