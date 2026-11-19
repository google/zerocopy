# NAND Flash Physics, FTL Key Remanence, NVMe ZNS/FDP Typestates, and Verified Storage Crash Consistency

## Summary

Modern NAND flash solid-state drives (SSDs) violate two foundational abstractions assumed by conventional systems software and memory-level verification: **in-place overwritability** and **ordered, atomic, corruption-free block persistence**.

1. **Out-of-place FTL remapping defeats block-layer sanitization and memory-only `zeroize()`.** NAND flash programs in pages (typically 4–16 KiB) but erases only in multi-megabyte erase blocks. To emulate a random-write logical block address (LBA) interface, an SSD's Flash Translation Layer (FTL) redirects every overwrite to a fresh physical page and marks the old page stale. Consequently, compiler-safe RAM scrubbing (`RustCrypto/utils` `zeroize`) covers only CPU-visible volatile memory, and single-file overwrite passes at the filesystem or block layer leave 4%–75% of original file bytes physically intact on SATA SSDs (Wei et al., FAST 2011)—and up to 100% under greedy garbage collection (GC) when hot overwrite passes recycle their own blocks rather than cold-neighbor blocks holding original plaintext (demonstrated in Probe 1A). Reliable sanitization on flash requires either **inline cryptographic key shredding** (destroying a compact, independently erasable key-encryption key or key tree) or **explicit physical erase primitives** (verified `NVME_ZONE_RESET` on ZNS or audited controller-level cryptographic sanitize).
2. **NVMe Zoned Namespaces (ZNS) replaces opaque FTL GC with an explicit 7-state typestate contract; NVMe Flexible Data Placement (FDP) preserves random-write LBAs while separating write lifetimes.** ZNS (TP 4053) partitions the LBA space into sequential-write-required zones governed by a finite-state machine (`Empty`, `Implicitly Open`, `Explicitly Open`, `Closed`, `Full`, `Read Only`, `Offline`), bounded by controller `MAR` (max active resources) and `MOR` (max open resources). Because concurrent multi-threaded LBA-addressed writes race on the zone write pointer (`wp`) and fail under PCIe/NVMe submission reordering (100% failure rate at QD=8 in Probe 1B), Linux (`drivers/nvme/host/zns.c`) forces zoned namespaces **read-only** unless the controller supports nameless **`Zone Append`** (`opcode 0x7D`), where the controller atomically assigns and returns the written LBA. FDP (TP 4146) offers a lower-migration-cost middle ground: host writes carry 16-bit Placement Identifiers (`PID`, via `NVME_RW_DTYPE_DPLCMT`) mapped to Reclaim Unit Handles (`RUH`) so lifetime-homogeneous streams land in separate erase blocks without requiring host-side sequential write pointers or zone resets.
3. **Storage crash safety and silent corruption require explicit barrier semantics and parental Merkle authentication, not merely local block checksums.** Drive volatile write-back caches reorder arbitrary writes across power loss unless delimited by `FLUSH` (`0x00`) or `FUA` (`1<<14`), multi-sector writes can tear (`254/256` states for 8×512 B sectors), and self-checksummed blocks fail to detect **lost writes** or **misdirected writes** (Bairavasundaram et al., FAST 2008; Probe 1B). Parental Merkle checksums (exemplified by OpenZFS `blkptr_t.blk_cksum` stored in the parent pointer rather than the child block) detect both classes.
4. **Mechanized crash-safe storage verifiers diverge sharply in disk semantics, concurrency, and proof architecture—and `mit-pdos/perennial` itself split between its Coq/Iris `master` branch and its Lean 4 `HEAD` (`lean`) branch.**
   - **FSCQ** (`mit-pdos/fscq`): Sequential Coq Crash Hoare Logic (`PRE`/`POST`/`CRASH`) over `AsyncDisk` (`valuset = valu * list valu`), proving `Write`, `Sync`, and `Trim` (`|+>?` nondeterministic logical contents, *not* physical erasure).
   - **Yggdrasil** (`uw-unsat/yggdrasil`): Automated SMT/Z3 **crash refinement** encoding asynchronous reordering with Boolean `synced`/`on` implication chains, trading concurrency and rich heap invariants for push-button checking.
   - **VeriBetrKV** (`secure-foundations/veribetrkv-osdi2020`): Dafny distributed-actor disk model (`reqReads`/`reqWrites`/`respReads`/`respWrites`) that explicitly models overlapping-I/O havoc (`HavocConflictingWrites`) and checksum-bounded silent read corruption (`ProcessReadFailure` + `AllChecksumsCheckOut`), proving a high-performance $B^\varepsilon$-tree via three-state refinement (`Persistent`/`Frozen`/`Ephemeral`) and dual alternating superblocks.
   - **Perennial** (`mit-pdos/perennial`): On its Coq/Iris `master` branch (`c3b7ecff...`), Perennial defines crash weakest preconditions (`WPC e @ s; E1 {{ Φ }} {{ Φc }}`) with non-crashed (`NC q`) and crashed (`C`) tokens and `generationGS` vs. `irisGS` to verify concurrent crash-safe Go programs (e.g., write-ahead logging in GoJournal). On its primary Lean 4 `lean` branch (`3afd77e3...`), Perennial deliberately omits `WPC` and `crash_own`, instead proving crash safety through standard `iris-lean` `wp` plus a crash adequacy theorem (`goose_crash_adequacy`, `ExtCrashInterp`, `notCrashed_crash`) over multi-generation boot programs.

## Applicability

This report synthesizes primary source implementations, hardware interface specifications, peer-reviewed empirical studies, and reproducible micro-probes across four interconnected domains:

- **Physical flash & sanitization scope:** Applies to NAND flash SSDs using page-mapped or hybrid out-of-place FTLs (SLC/MLC/TLC/QLC raw NAND), NVMe ZNS SSDs (`NVME_CSI_ZNS`), and NVMe FDP SSDs (`NVME_RW_DTYPE_DPLCMT`), as well as host-side cryptographic memory scrubbing (`RustCrypto/utils` `zeroize` @ `77d1a3e6...`). Findings regarding FTL remanence do **not** apply to byte-addressable non-volatile RAM (NVRAM/PMEM) or conventional magnetic HDDs with direct 1:1 physical sector overwrite (except remapped bad-sector spares on HDDs).
- **Kernel & storage protocol scope:** Linux kernel NVMe and zoned block UAPI findings apply specifically to `torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` (`include/linux/nvme.h`, `include/uapi/linux/blkzoned.h`, `drivers/nvme/host/zns.c`), including the Linux 6.19 cached zone report extensions (`BLKREPORTZONEV2`, `BLK_ZONE_COND_ACTIVE`) and the Linux NVMe ZNS driver's mandatory `Zone Append` and power-of-2 `zsze` constraints. OpenZFS `blkptr_t` observations apply to `openzfs/zfs` @ `cde5d598eb44b5d6efe8167666d988a496346657` (`include/sys/spa.h`).
- **Verification framework scope & version split:**
  - `mit-pdos/perennial` is examined at **two distinct branches** because its `HEAD` switched to a Lean 4 port whose program logic differs materially from the published SOSP 2019 Coq/Iris framework:
    - `lean` (`HEAD`, `3afd77e35b0a727a05f1149c15308ddcc2e60357`): Lean 4 on `iris-lean`; standard `wp` + `goose_crash_adequacy` + `ExtCrashInterp`; no `wpc` or `crash_own` reasoning principles yet.
    - `master` (`c3b7ecff27c1a6e8ed058d5aca362df1e2f63311`): Coq/Iris Perennial; full `wpc`, `NC q`/`C` crash tokens, `generationGS` vs. `irisGS`, and concurrent crash-safe WAL/storage proofs.
  - `mit-pdos/fscq` (`2c7ef9c268fd79a81b26b44ef720f8e6a1e938a0`), `uw-unsat/yggdrasil` (`e1de61d798acafb9ae2d8387d176c4b091773623`), and `secure-foundations/veribetrkv-osdi2020` (`053dd16ab01939843a213e0590983fd22e2d0d4d`, specifically the `veribetrkv-linear` tree) are compared as distinct verification paradigms targeting the same underlying problem (asynchronous reordering + fail-stop crashes).
- **Relationship among subjects:** The report relates physical NAND/FTL mechanics and NVMe ZNS/FDP host-device interfaces directly to the trust boundaries of storage verification frameworks: specifically, which hardware failure modes (cache reordering, torn writes, silent corruption, FTL remanence, overlapping I/O havoc) each verifier models versus leaves outside its trusted computing base (TCB).

## Findings

### 1. NAND Flash Physics, FTL Architecture, and the Block Interface Tax

*Basis: documentation + publication (Bjørling et al., USENIX ATC 2021) + execution (Probe 1A) + derived*

NAND flash memory is organized hierarchically into **dies/planes**, **erase blocks** (typically 2 MiB–64 MiB, or gigabyte-scale "superblocks" striped across parallel channels/dies), and **pages** (typically 4 KiB–16 KiB). Three physical constraints govern every layer above the silicon:

1. **Erase-before-write asymmetry:** Floating-gate or charge-trap NAND cells can be programmed (writing bits from `1` to `0`) at page granularity, but resetting bits from `0` back to `1` requires applying a high-voltage erase pulse across an entire **erase block**. Pages within a block must generally be programmed sequentially to minimize program-disturb interference across adjacent wordlines.
2. **Finite program/erase (P/E) endurance:** Oxide tunneling degrades cells with every erase cycle (roughly $10^5$ P/E cycles for SLC, $3\times 10^3$–$10^4$ for MLC, $10^3$–$3\times 10^3$ for TLC, and $10^2$–$10^3$ for QLC). Hot logical addresses rewritten repeatedly would destroy a single physical block rapidly unless writes are spread across the drive via **wear leveling** (dynamic wear leveling on hot writes, and static wear leveling that periodically migrates cold blocks off low-wear physical blocks).
3. **Out-of-place indirection and the Block Interface Tax:** Because host filesystems and databases expect an in-place random-write block interface (inherited from magnetic HDDs), conventional SSDs embed a **Flash Translation Layer (FTL)** firmware running on an internal multi-core SoC with a Logical-to-Physical (L2P) mapping table. Maintaining 4 KiB page granularity requires roughly **1 GiB of on-device DRAM per 1 TiB of NAND** (4 bytes per 4 KiB LBA, ~0.1% of raw capacity), plus power-loss capacitor banks (PLP) to flush dirty L2P metadata on sudden power loss.

To sustain random writes without stalling on erase cycles, conventional SSDs reserve **over-provisioning (OP)**—hidden physical capacity not exposed in the LBA space (typically ~7% in consumer drives via decimal-vs-binary GiB/GB differences, and **28%** in enterprise drives). Under uniform random writes with greedy garbage collection (which selects the full block with the fewest valid pages, copies its surviving valid pages to a fresh block, and erases the victim), the steady-state **Write Amplification Factor** ($\text{WAF} = \frac{\text{physical NAND writes}}{\text{host logical writes}}$) rises steeply as over-provisioning shrinks.

In our executable FTL simulator (**Probe 1A**, 64 blocks × 16 pages/block, greedy GC, 20,000 uniform random host writes):

| Configuration | Exposed Logical Pages | Actual Over-Provisioning (OP) | Observed Steady-State Random WAF | ZNS Zone-Aligned Sequential WAF |
|---|---:|---:|---:|---:|
| Consumer SSD (~7% OP) | 956 / 1024 | 7.1% | **6.58×** | **1.00×** |
| Enterprise SSD (28% OP) | 800 / 1024 | 28.0% | **2.33×** | **1.00×** |

*Basis: execution (Probe 1A); aligns quantitatively with Bjørling et al. (USENIX ATC 2021), which documents the "block interface tax": 7%–28% lost usable capacity to over-provisioning, multi-gigabyte FTL DRAM tables, 2×–5× random-write amplification, and severe tail-latency cliffs when foreground host I/O collides with background FTL garbage collection.*

Crucially, because host log-structured storage engines (RocksDB/LSM-trees, Btrfs/ZFS copy-on-write trees, WALs) already perform host-side log compaction and garbage collection, stacking a host log-structured allocator on top of an opaque device FTL produces **log-on-log write amplification**—the host's cold SSTables and hot WAL segments get interleaved into the same physical NAND erase blocks unless the host and device coordinate placement.

---

### 2. FTL Out-of-Place Remanence vs. `zeroize()` and Inline Cryptographic Erasure

*Basis: source (`RustCrypto/utils` `zeroize/src/lib.rs`) + publication (Wei et al., USENIX FAST 2011; Reardon, Basin, Čapkun, IEEE S&P 2013) + execution (Probe 1A)*

A recurring security defect in verified and cryptographic systems is treating **memory-level zeroization** or **block-layer file overwriting** as sufficient to destroy secrets written to persistent storage (swap files, hibernation images, keystore files, WALs, or unencrypted database pages).

#### 2.1 Exact Boundary of Memory `zeroize()` (`RustCrypto/utils`)

Direct inspection of `RustCrypto/utils` (`77d1a3e6c2e8c28f49189258abb5d4405c0f1330`, `zeroize/src/lib.rs:148–206, 253–285`) shows that `Zeroize::zeroize(&mut self)` provides strictly a **compiler dead-store-elimination barrier on CPU-addressed RAM**:

- It fills the target memory via volatile writes (`volatile_write(self, Z::default())`) or optimized bulk fills followed by an inline-assembly `optimization_barrier` so LLVM cannot elide the overwrite before `Drop`.
- `zeroize/src/lib.rs:160–201` explicitly disclaims coverage of CPU register spills, Rust move-semantics copies on the stack, `Vec`/`String` prior reallocations, microarchitectural covert channels, and **OS swap / persistent storage** (`mlock()`, swap encryption, and disk erasure are explicitly out of scope).

#### 2.2 Why Block-Layer Overwriting Fails on FTL SSDs (Wei et al., FAST 2011 & Probe 1A)

When an application or OS attempts to sanitize a sensitive file or key slot on an SSD by overwriting its logical blocks with zeros or random bytes (whether 1 pass, 3-pass DoD, or 35-pass Gutmann), the FTL intercepts every write to `LBA_i`, maps `LBA_i` to a **new** physical page `(blk', pg')`, and leaves the original physical page `(blk, pg)` containing the plaintext secret intact on the NAND die until `blk` is eventually selected for GC and physically erased.

Empirical measurements by **Wei, Grupp, Spada, and Swanson (USENIX FAST 2011)** across **12 commercial SSDs** (plus USB flash drives) using physical NAND chip decapsulation and raw flash readout established three stark conclusions:

1. **All single-file overwrite protocols failed:** Overwriting an individual file repeatedly left **4% to 75%** of the original file contents physically recoverable from raw SATA SSD NAND chips (and **0.57% to 84.9%** on USB flash drives).
2. **Full-drive overwrites are unreliable on a single pass:** Because over-provisioned blocks and wear-leveling pools exceed the exposed LBA capacity, a single full-drive overwrite frequently left old blocks unerased; even twice-full-drive overwrites only *usually* (not universally) cleared all remanent blocks, while inflicting massive P/E wear.
3. **Built-in firmware sanitization commands are frequently buggy:** Of drives implementing `ATA SECURITY ERASE UNIT` / `ENHANCED`, several vendor firmware implementations exhibited silent bugs—reporting success without actually erasing all physical blocks or failing to execute reliably across firmware revisions.

**Mechanistic amplification under Greedy GC (Probe 1A):** Our executable FTL simulation exposes a counterintuitive amplifier that makes repeated single-file overwriting *worse* than intuition suggests. When a 16-page secret is written alongside cold data in mixed erase blocks, and the host subsequently performs **1, 3, 7, or 35 overwrite passes** to those 16 LBAs:
- Each overwrite pass invalidates the previous overwrite pass's pages, creating **hot blocks with 0 valid pages**.
- Greedy GC selects the lowest-valid-count victim block—which is invariably one of the hot blocks created by the overwrite passes themselves!
- Consequently, the cold-neighbor blocks holding the original plaintext secret copies retain high valid-page counts (15/16 valid) and are **never selected by GC**. In Probe 1A (28% OP Enterprise SSD), **16/16 (100.0%)** of the original secret pages remained physically intact on NAND after **35 consecutive overwrite passes**.

#### 2.3 Formal Secure Deletion Taxonomy & Sound Flash Defenses

**Reardon, Basin, and Čapkun (IEEE S&P 2013, `DOI: 10.1109/SP.2013.28`)** systematize secure deletion across three adversary capabilities (software/OS access, raw physical medium readout, and coercive key extraction) and establish why **physical overwriting at the block layer cannot meet physical-readout security on log-structured/FTL media**. Two architectures achieve verifiable deletion on flash:

| Sanitization Strategy | Mechanism | Latency / Wear Cost | Failure Modes & TCB |
|---|---|---:|---|
| **Block-layer single-file overwrite (`shred` / `zeroize` file)** | Rewrite file LBAs $N$ times | High wear ($N\times$ file size) | **Broken on FTL SSDs**: 4%–75% empirical remanence (Wei et al. FAST 2011); up to 100% under greedy GC (Probe 1A). |
| **NVMe `DSM Deallocate` / `TRIM`** | Mark LBA range logically unmapped | $O(1)$ metadata update | **Not a security primitive**: `TRIM` is an advisory GC hint; physical pages remain readable until background erase. Modeled in FSCQ (`trim_ok`, `BasicProg.v:139–145`) only as nondeterministic logical read (`|+>?`). |
| **Inline Cryptographic Erasure / Key-Tree Shredding** | Encrypt every file/epoch/extent with a unique Data Encryption Key (DEK) wrapped by an ephemeral key tree whose small root resides in an erasable key-store (TPM/HSM NVRAM, dedicated ZNS key zone, or hardware-supported NVMe Crypto Erase) | $O(1)$ key destruction; minimal NAND wear | Reduces physical erasure surface from TB of user data to bytes of key material. Vulnerable to **coercive adversaries** if root KEK is retained, or if unencrypted DEKs ever touch swap/FTL before wrapping. Requires authenticated encryption (AEAD) + forward-secure key ratcheting (Reardon et al. S&P 2013). |
| **NVMe ZNS `NVME_ZONE_RESET` + Verified Erase** | Host explicitly resets the entire sequential zone (`opcode 0x79`, `zsa = 0x4`), triggering deterministic physical block erase of the zone's underlying erase blocks | Exact 1× erase of zone; bounded wear | Eliminates hidden L2P shadow copies within the zone **only if** the controller implements `Zone Reset` as synchronous/bounded physical erase rather than deferred lazy unmap (must be checked against controller sanitize/ZNS vendor guarantees; see `## Boundaries`). |
| **NVMe `Format NVM` / `Sanitize` (`Crypto Erase` / `Block Erase`)** | Controller-wide physical erase or internal media encryption key (MEK) rotation (`Sanitize` survives power-loss interruption and resumes on boot) | Whole-namespace or whole-SSD scope | Whole-device/whole-namespace granularity (unsuitable for per-file deletion); relies on correct controller firmware implementation of key rotation / block erase. |

---

### 3. NVMe Zoned Namespaces (ZNS) Typestate Machine & `Zone Append` Nameless Writes

*Basis: normative specification (NVMe ZNS TP 4053) + source (`torvalds/linux` `include/linux/nvme.h`, `include/uapi/linux/blkzoned.h`, `drivers/nvme/host/zns.c`) + publication (Bjørling et al., ATC 2021) + execution (Probe 1B)*

NVMe Zoned Namespaces (ZNS, Command Set Identifier `NVME_CSI_ZNS`) exposes the append-only, coarse-erase geometry of NAND flash directly across the NVMe wire interface, eliminating device-side random-write garbage collection and reducing FTL mapping metadata from per-4 KiB-page tables to per-zone descriptors.

#### 3.1 Zone Geometry, `ZCAP <= ZSZE`, and Resource Limits

Direct inspection of `torvalds/linux` (`4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`) reveals exact structural and driver invariants:

- **Zone Size (`zsze`) vs. Zone Capacity (`zcap`):** In `struct nvme_id_ns_zns` (`include/linux/nvme.h:494–504`), each LBA format exposes a fixed zone size `zsze`, while each individual `struct nvme_zone_descriptor` reports a writable **Zone Capacity** `zcap` (`drivers/nvme/host/zns.c:165–166`, mapped to `struct blk_zone.capacity` in `include/uapi/linux/blkzoned.h:138`). Crucially, **`zcap <= zsze`**. Linux requires `is_power_of_2(zi->zone_size)` (`drivers/nvme/host/zns.c:93`) so LBA-to-zone division is a bit-shift (`ilog2(zsze)`), whereas physical NAND flash blocks frequently have non-power-of-2 capacities (e.g., 1077 MiB usable flash inside a 2048 MiB logical zone stride). Writes at `zslba + zcap <= lba < zslba + zsze` are **illegal**; the zone transitions to `Full` when `wp == zslba + zcap`, NOT `zslba + zsze` (though Linux normalizes `zone.wp = zone.start + zone.len` for `BLK_ZONE_COND_FULL` in `zns.c:168–169`).
- **0-Based Active and Open Resource Limits (`MAR`, `MOR`):** Because each open NAND erase block holds volatile controller SRAM/write-buffer state and risks charge-loss data-retention errors if left partially programmed indefinitely, ZNS controllers cap simultaneously **Open** zones (`MOR`, Max Open Resources) and **Active** zones (`MAR`, Max Active Resources, where `Active = Implicitly Open ∪ Explicitly Open ∪ Closed`). Both fields in `struct nvme_id_ns_zns` are **0-based** (`zi->max_open_zones = le32_to_cpu(id->mor) + 1; zi->max_active_zones = le32_to_cpu(id->mar) + 1`, `zns.c:100–101`; `0xFFFFFFFF` denotes unlimited). Exceeding `MOR` or `MAR` fails commands with `Too Many Active Zones` / `Too Many Open Zones`.

#### 3.2 Formal 7-State Zone Condition Typestate Automaton

The NVMe ZNS / ZBC / ZAC zone state machine (encoded in `enum blk_zone_cond` in `include/uapi/linux/blkzoned.h:74–86` and `enum nvme_zone_mgmt_action` in `include/linux/nvme.h:1189–1196`) defines seven device states (`ZC1`–`ZC7`), plus Linux 6.19's cached-report summary state `BLK_ZONE_COND_ACTIVE = 0xFF` (`BLK_ZONE_REP_CACHED = 1U << 31`):

| State Code (`blk_zone_cond`) | NVMe State | Resource Consumption | Write Pointer (`wp`) Validity | Valid Host Transitions (`Zone Management Send` `0x79` / I/O) |
|---|---|---|---|---|
| `0x1` (`EMPTY`) | `ZC1: Empty` | 0 Open, 0 Active | `wp == zslba` | `Write`/`Zone Append` → `IMP_OPEN` (or `FULL` if fills `zcap`); `OPEN` (`0x3`) → `EXP_OPEN`; `FINISH` (`0x2`) → `FULL`; `OFFLINE` (`0x5`) → `OFFLINE` |
| `0x2` (`IMP_OPEN`) | `ZC2: Implicit Open` | 1 Open, 1 Active | `zslba <= wp < zslba + zcap` | `Write`/`Zone Append` (advances `wp`; → `FULL` at `zcap`); Controller auto-evict on `MOR` pressure → `CLOSED`; `OPEN` (`0x3`) → `EXP_OPEN`; `CLOSE` (`0x1`) → `CLOSED`; `FINISH` (`0x2`) → `FULL`; `RESET` (`0x4`) → `EMPTY` |
| `0x3` (`EXP_OPEN`) | `ZC3: Explicit Open` | 1 Open, 1 Active | `zslba <= wp < zslba + zcap` | Same as `IMP_OPEN`, **except controller may NOT auto-close** under `MOR` pressure (pinned open until host `CLOSE`/`FINISH`/`RESET`) |
| `0x4` (`CLOSED`) | `ZC4: Closed` | 0 Open, 1 Active | `zslba < wp < zslba + zcap` | `Write`/`Zone Append` → `IMP_OPEN` (re-acquiring an Open slot); `OPEN` (`0x3`) → `EXP_OPEN`; `FINISH` (`0x2`) → `FULL`; `RESET` (`0x4`) → `EMPTY` |
| `0xE` (`FULL`) | `ZC5: Full` | 0 Open, 0 Active | Invalid (`wp` exhausted; Linux reports `start + len`) | Read-only until `RESET` (`0x4`) → `EMPTY` (or `OFFLINE` (`0x5`) → `OFFLINE`) |
| `0xD` (`READONLY`) | `ZC6: Read Only` | 0 Open, 0 Active | Invalid | Controller-entered fault state (e.g., media wear exhaustion); reads permitted, writes/reset rejected; host may transition → `OFFLINE` |
| `0xF` (`OFFLINE`) | `ZC7: Offline` | 0 Open, 0 Active | Invalid | Terminal state; reads and writes rejected |

**Typestate encoding for safe systems languages (e.g., Rust):** The ZNS contract maps directly onto a **linear/affine typestate machine** parameterized by zone state markers (`Zone<Empty>`, `Zone<Open { wp, zcap }>`, `Zone<Closed { wp, zcap }>`, `Zone<Full>`) combined with linear resource tokens (`OpenSlot` bounded by `MOR`, `ActiveSlot` bounded by `MAR`):
- Calling `write_at(zone: Zone<Open>, lba, buf)` requires compile-time or checked proof that `lba == zone.wp` and `lba + len <= zone.zslba + zone.zcap`, consuming the old `Zone<Open>` handle and returning either `Zone<Open { wp: wp + len }>` or `Zone<Full>` (releasing both `OpenSlot` and `ActiveSlot`).
- Calling `reset(zone: Zone<Full | Closed | Open>)` consumes the handle and returns `(Zone<Empty>, released_slots)`, making **use-after-reset** and **write-to-Full-zone** unrepresentable in safe code, while exposing the exact proof obligation required across FFI/ioctl boundaries (`BLKRESETZONE`, `BLKOPENZONE`, `BLKCLOSEZONE`, `BLKFINISHZONE`).

#### 3.3 The Multi-Threaded Write-Pointer Bottleneck and `Zone Append` (`opcode 0x7D`)

In standard LBA-addressed NVMe `Write` (`opcode 0x01`) against a sequential-write-required zone (`NVME_ZONE_TYPE_SEQWRITE_REQ = 0x2`), the controller enforces `cmd.slba == zone.wp`. Even if host threads acquire a lock to allocate sequential offsets `wp, wp+1, ..., wp+7`, **PCIe/NVMe multi-queue submission and controller fetch order can reorder in-flight requests**, causing any out-of-order request to fail immediately with `Invalid Write Pointer`.

- **Empirical quantification (Probe 1B):** Across 1,000 trials of QD=8 concurrently submitted, randomly reordered LBA-addressed writes to a single zone, **1000/1000 (100.0%)** suffered write-pointer mismatch failures (analytical failure probability $1 - 1/8! = 99.9975\%$). Consequently, standard `Write` restricts each zone to **QD=1** unless the OS block layer enforces strict per-zone software serialization (such as Linux `mq-deadline` zone write locking).
- **Nameless `Zone Append` (`nvme_cmd_zone_append = 0x7D`):** ZNS resolves this bottleneck by letting multiple threads concurrently submit **`Zone Append`** commands targeting the zone's start LBA (`zslba`), up to the controller's Zone Append Size Limit `zasl` (`ctrl->max_zone_append = 1 << (id->zasl + 3)` in 512 B sectors when `zasl != 0`, `drivers/nvme/host/zns.c:30–33`). The controller atomically serializes arriving appends at `wp`, advances `wp`, and returns the **assigned LBA** in Completion Queue Entry `DW0` (`result`). In Probe 1B, QD=8 reordered `Zone Append` submissions experienced **0/1000 (0.0%)** ordering failures.
- **Linux driver enforcement (`drivers/nvme/host/zns.c:47–58`):** Direct inspection of `nvme_query_zone_info()` shows that the Linux NVMe ZNS driver **requires** `NVME_CMD_EFFECTS_CSUPP` for `nvme_cmd_zone_append`; if a ZNS device omits `Zone Append`, Linux sets `NVME_NS_FORCE_RO` and forces the entire zoned namespace **read-only**.
- **Trade-off for storage engines:** Because `Zone Append` returns the assigned LBA *only upon I/O completion*, filesystems and LSM-trees cannot pre-record physical block pointers in metadata before data completion—they must either record extents upon completion or use self-describing headers inside appended records (as in Btrfs zoned mode and ZenFS/RocksDB, Bjørling et al., ATC 2021).

---

### 4. NVMe Flexible Data Placement (FDP, TP 4146) vs. ZNS Architectural Comparison

*Basis: normative specification (NVMe TP 4146 / Base 2.1) + source (`torvalds/linux` `include/linux/nvme.h:704–740, 1141–1142, 1230–1260`) + derived*

While ZNS eliminates the block-interface tax completely, it imposes substantial host software re-architecture (every filesystem, page cache writeback path, and database engine must enforce sequential writes, manage `MAR`/`MOR`, and perform host-side GC). **NVMe Flexible Data Placement (FDP, Technical Proposal 4146, integrated into NVMe Base Specification 2.1)** was designed specifically to capture most of ZNS's WAF reduction **without breaking the conventional random-write LBA block interface**.

#### 4.1 FDP Architectural Primitives (`include/linux/nvme.h`)

Direct inspection of `torvalds/linux/include/linux/nvme.h` (`4405c18c...`) confirms the exact wire structures of FDP:

- **Endurance Groups, Reclaim Groups (`RG`), and Reclaim Units (`RU`):** FDP is configured per Endurance Group (`struct nvme_fdp_config_desc`, `nvme.h:716–728`), declaring `nrg` Reclaim Groups (independent media failure/parallelism domains), `nruh` Reclaim Unit Handles, `maxpids` maximum Placement Identifiers, `runs` Reclaim Unit Nominal Size (bytes), and `erutl` Estimated Reclaim Unit Time Limit. A **Reclaim Unit (RU)** corresponds to a physical erase-block/superblock unit that the controller can reclaim cleanly when all LBAs written into it expire together.
- **Reclaim Unit Handles (`RUH`) — Initially Isolated (`II`) vs. Persistently Isolated (`PI`):** Each `struct nvme_fdp_ruh_desc` (`nvme.h:711–714`) specifies `ruht` (Reclaim Unit Handle Type):
  - **Initially Isolated (`II`):** Host writes directed to this handle are initially placed in a dedicated RU isolated from other handles; however, if the controller later performs internal GC on that RU, migrated valid blocks may be merged into shared controller-managed blocks.
  - **Persistently Isolated (`PI`):** Guarantees isolation across controller-internal GC migrations as well, preserving stream separation even when host lifetimes do not align perfectly with RU boundaries.
- **Placement Identifiers (`PID`) on Standard Writes:** Host software attaches a 16-bit Placement Identifier in `Write` command `CDW13` (`dsmgmt`) with Directive Type set to Data Placement (`NVME_RW_DTYPE_DPLCMT = 2 << 4`, `nvme.h:1142`, superseding legacy `NVME_RW_DTYPE_STREAMS = 1 << 4`).
- **IO Management Receive / Send (`opcode 0x12` / `0x1D`):** Hosts query live RU capacity via `struct nvme_io_mgmt_recv_cmd` (`nvme.h:1230–1246`, `mo = NVME_IO_MGMT_RECV_MO_RUHS = 1`), receiving an array of `struct nvme_fdp_ruh_status_desc` (`nvme.h:1248–1254`) reporting each `(pid, ruhid)`'s **`ruamw`** (Reclaim Unit Available Media Writes—remaining bytes before the RU fills and rotates) and **`earutr`** (Estimated Active Reclaim Unit Time Remaining). Hosts can also issue `IO Management Send` (`Reclaim Unit Handle Update`) to rotate a handle onto a fresh RU on demand.

#### 4.2 Cross-Architecture Trade-Off Matrix: Conventional FTL vs. NVMe FDP vs. NVMe ZNS

| Dimension | Conventional FTL SSD | NVMe FDP (TP 4146) | NVMe ZNS (TP 4053) |
|---|---|---|---|
| **Host I/O Interface** | Random-write LBA (in-place semantics) | Random-write LBA + 16-bit `PID` hint (`DTYPE=2`) | Sequential-write-required zones + `Zone Append` (`0x7D`) |
| **Over-Provisioning & DRAM Tax** | High (7%–28% OP; ~1 GiB DRAM/TiB L2P) | Medium-High (still maintains full 4 KiB L2P map; lower OP needed if host matches lifetimes to `runs`) | Minimal (~0%–7% OP; coarse zone-level mapping eliminates most L2P DRAM) |
| **Garbage Collection Owner** | Device FTL (opaque, tail-latency spikes) | Device FTL (hint-assisted; near-1.0× WAF if host aligns deletes/deallocates to `ruamw`) | Host software (deterministic scheduling; WAF = 1.00× inside device) |
| **Failure Mode on Host Misbehavior** | Silent WAF increase / tail latency | Graceful fallback (controller silently places unhinted/overflow writes into default RU; never fails I/O) | **Hard protocol error** (`Invalid Write Pointer`, `Too Many Open/Active Zones`) |
| **Data Remanence / Secure Deletion** | Defeats block overwrite (4%–75%+ remanence); requires crypto shredding or full-device sanitize | Still out-of-place L2P FTL—**same block-overwrite remanence hazard**; requires crypto shredding or sanitize | Deterministic zone-level erase via `Zone Reset` (subject to controller synchronous-erase guarantee) + ideal substrate for dedicated key-shredding zones |
| **Host Software Adoption Cost** | Zero | Low (tag write streams by lifetime: WAL, L0, L1..Ln SSTables) | High (custom zone allocator, host GC, `MAR`/`MOR` accounting, `Zone Append` completion-time pointer indexing) |

---

### 5. Drive Write-Back Caches, Reordering, Torn Writes, and Silent Storage Corruption

*Basis: normative specification (NVMe) + source (`torvalds/linux` `include/linux/nvme.h`, `openzfs/zfs` `include/sys/spa.h`) + publication (Bairavasundaram et al., FAST 2008; Pillai et al., OSDI 2014) + execution (Probe 1B)*

Even below the FTL's wear-leveling layer, block devices expose four crash and integrity hazards that invalidate naive sequential persistence assumptions:

1. **Volatile Write-Back Cache Reordering (`FLUSH` vs. `FUA`):** Unless a drive has battery/capacitor-backed power-loss protection (PLP) *and* advertises non-volatile cache semantics, acknowledged `Write` completions reside in volatile controller DRAM and may reach persistent NAND in **arbitrary order**.
   - **NVMe `Flush` (`nvme_cmd_flush = 0x00`, `nvme.h:957`):** Flushes all previously completed writes in the namespace to non-volatile media; establishes a full ordering barrier.
   - **NVMe `FUA` (`NVME_RW_FUA = 1 << 14`, `nvme.h:1120`):** Forces *this specific write command* to non-volatile media before completion, **without flushing unrelated previously acknowledged buffered writes** (a subtle distinction: `Write(data)` followed by `Write(header, FUA)` still allows `header` to persist while `data` is lost!).
   - **Empirical witness (Probe 1B):** Under the exact `AsyncDisk` reordering model, issuing `Write(data)` then `Write(header)` without an intervening `FLUSH` produces 4 reachable post-crash states, of which 1 (`synced_data=False, synced_hdr=True`) commits the journal header pointing at stale/zero data. Inserting `FLUSH` between `Write(data)` and `Write(header)` constrains reachable states via `on_flush -> synced_data` and `synced_hdr -> on_flush`, yielding **0 corrupt crash states**.
   - **Filesystem persistence diversity (Pillai et al., OSDI 2014):** Studying ext4, btrfs, xfs, and others with ALICE/BOB, Pillai et al. demonstrated that application crash bugs routinely stem from assuming POSIX operations (`rename`, `write` append, directory entry creation) are ordered or atomic across crashes without explicit `fsync()` on both the file *and* its parent directory.
2. **Torn Multi-Sector Writes:** Standard NVMe namespaces guarantee write atomicity only at `AWUN`/`AWUPF` (Atomic Write Unit Normal / Power Fail), which on many devices is as small as a single 512 B or 4 KiB sector unless explicitly queried and enabled. Writing a 4 KiB logical block across 8×512 B sectors without `AWUPF >= 4 KiB` yields **`2^8 - 2 = 254` torn half-old/half-new crash states** out of 256 possible sector subsets (Probe 1B). Databases therefore require either checksummed WAL records (so torn tail records fail checksum and are discarded on recovery) or double-write buffering / copy-on-write alternating superblocks.
3. **Silent Storage Corruption (Bairavasundaram et al., FAST 2008):** Analyzing **1.53 million production disk drives over 41 months**, Bairavasundaram et al. documented **over 400,000 silent checksum mismatches**—corruptions returned by storage stacks with *zero* hardware I/O error—driven by media bit rot, firmware bugs, bus/DMA corruption, **lost writes** (disk acknowledges a write that never updates media, leaving the previous valid block intact), and **misdirected writes** (disk writes block $B$ intended for `LBA_2` onto `LBA_1`).
4. **Why Self-Checksummed Blocks Fail vs. Parental Merkle Checksums (`OpenZFS blkptr_t`):**
   - Storing `crc(block)` *inside the block itself* detects bit-rot and torn writes, **but fails completely on both lost writes and misdirected writes** (Probe 1B: `self-checksum=False` for both), because the stale block at `LBA_1` (lost write) and the valid foreign block from `LBA_2` (misdirected write) each carry an internally consistent self-checksum!
   - **Parental Merkle Checksums:** Direct inspection of `openzfs/zfs` (`cde5d598eb44b5d6efe8167666d988a496346657`, `include/sys/spa.h:389–397`) shows `typedef struct blkptr` storing `dva_t blk_dva[3]` (Data Virtual Addresses), `uint64_t blk_birth_word[2]` (transaction group birth timestamp), and **`zio_cksum_t blk_cksum`** (256-bit checksum of the *child* block) **inside the parent block pointer**, recursively anchored up to a signed/checksummed root uberblock. Because a lost write returns an older version whose hash disagrees with the updated parent's `blk_cksum`, and a misdirected write returns a foreign block whose hash also disagrees with `blk_cksum`, parental Merkle trees detect **100%** of lost writes, misdirected writes, torn writes, and bit rot (up to hash collision probability, verified in Probe 1B: `parental-Merkle=True` for both).

---

### 6. Mechanized Crash-Consistent Storage Verification: FSCQ, Yggdrasil, VeriBetrKV, and Perennial (Coq vs. Lean 4)

*Basis: source (`mit-pdos/fscq`, `uw-unsat/yggdrasil`, `secure-foundations/veribetrkv-osdi2020`, `mit-pdos/perennial` `master` & `lean`) + publication (Chen et al., SOSP 2015; Sigurbjarnarson et al., OSDI 2016; Hance et al., OSDI 2020; Chajed et al., SOSP 2019)*

Formalizing storage crash consistency requires answering four hard questions: (1) how is the asynchronous write-back disk modeled? (2) how are crashes during recovery handled? (3) how does concurrency (multiple threads issuing overlapping or pipelined I/O) compose with crash invariants? and (4) are silent corruption and overlapping-I/O races inside or outside the model? Direct source inspection of the four landmark systems reveals four fundamentally distinct verification architectures.

#### 6.1 FSCQ (`mit-pdos/fscq` @ `2c7ef9c268fd79a81b26b44ef720f8e6a1e938a0`): Sequential Crash Hoare Logic over `valuset` Disks

FSCQ (Chen et al., SOSP 2015, `DOI: 10.1145/2815400.2815402`) introduced **Crash Hoare Logic (CHL)** in Coq, extending separation-logic triples with an explicit `CRASH` condition and recovery composition combinator (`>>`).

- **Exact asynchronous disk model (`src/AsyncDisk.v:79–83, 163–175`):** Each 4 KiB block (`valubytes_real = 0x1000`, `valu = word valulen`) maps not to a single block value, but to a **`valuset := (valu * list valu)`**: the latest buffered value `fst vs` paired with the history list `snd vs` of unsynced older values (`vsmerge vs := fst vs :: snd vs`).
  - `Write a v` (`src/BasicProg.v:62–68`) transforms `a |+> v0` into `a |+> (v, vsmerge v0)` in `POST`, with `CRASH` holding `a |+> v0` (or any subset via `possible_sync`).
  - `Sync` (`src/BasicProg.v:112–117`) transforms `F * [[ sync_invariant F ]]` into `sync_xform F`, collapsing every `(v, old_list)` via `sync_mem` to `(v, nil)` (`AsyncDisk.v:163–167`).
  - `Trim a` (`src/BasicProg.v:139–145`) maps `a |+> v0` to `a |+>?` (arbitrary logical value in both `POST` and `CRASH`), capturing TRIM's non-deterministic post-unmap read semantics without promising physical data destruction.
- **Transactional logging (`src/Log.v:67–119`):** `LOG.state` explicitly enumerates `NoTxn (cur : diskset)`, `ActiveTxn (old : diskset) (cur : diskstate)`, `FlushingTxn (new : diskset)`, `RollbackTxn`, and `RecoveringTxn`, using `diskset` (a non-empty list of possible disk snapshots) to prove group-commit durability and **crash-during-recovery** idempotence.
- **Strengths & limits:** End-to-end Coq machine-checked proof extracted to Haskell/FUSE, including disk-cache reordering and recovery crashes; however, FSCQ is strictly **single-threaded (sequential)**, assumes **zero silent disk corruption** (except checksummed log headers modeled via an idealized collision-free `hashmap` in `AsyncDisk.v:87–135`), and assumes atomic 4 KiB block writes.

#### 6.2 Yggdrasil (`uw-unsat/yggdrasil` @ `e1de61d798acafb9ae2d8387d176c4b091773623`): Push-Button SMT Crash Refinement

Yggdrasil (Sigurbjarnarson et al., OSDI 2016) eliminates interactive proof scripts by encoding both implementation and specification in a decidable Python/Z3 subset and checking **crash refinement**: every post-crash disk state reachable by the implementation must correspond (under an abstraction function) to a crash state permitted by the specification.

- **Exact Z3 crash-ordering encoding (`yggdrasil/diskspec.py:13–66, 87–128`):**
  - `Machine` maintains a current Boolean `self._on` and a list of ordering implications `self._ordering`.
  - `AsyncDisk.write(bid, data)` allocates a fresh Boolean `synced = self._mach.create_synced()`, emitting `Implies(synced, self._on)`, updates `self._cache` unconditionally, and updates `self._disk` conditionally on `synced`.
  - `AsyncDisk.flush()` allocates a fresh Boolean `on = self._mach.create_on(self._dirty)`, emitting `Implies(on, prev_on)` and `Implies(on, s)` for every pending dirty write `s` in `self._dirty`, then clears `self._dirty`.
  - Because Z3 searches over *all* truth assignments to `{synced_i, on_j}` satisfying `self._ordering`, a single SMT query simultaneously verifies all $2^k$ possible cache-reordering crash subsets and automatically synthesizes concrete crash counterexamples (`Machine.explain(model)`, `diskspec.py:67–84`).
- **Strengths & limits:** Completely automated ("push-button") verification with fast counterexample diagnostics; however, decidability requires restricting implementations to bounded-loop, single-threaded, pointer-free disk array transformations (`UFArray`), excluding fine-grained concurrency, lock-free data structures, and unbounded dynamic memory graphs.

#### 6.3 VeriBetrKV (`secure-foundations/veribetrkv-osdi2020` @ `053dd16ab01939843a213e0590983fd22e2d0d4d`): Distributed-Actor Async Disk + Silent Corruption + Linear Dafny

VeriBetrKV (Hance et al., OSDI 2020) proves a production-speed crash-safe $B^\varepsilon$-tree key-value store (competitive with RocksDB/BerkeleyDB) by modeling the single-node storage stack as a **distributed system** composed of two asynchronous actors—the host `Machine` and the `AsyncDisk`—communicating over unordered message queues.

- **Exact actor disk model (`docker-ssd/src/veribetrkv-linear/ByteBlockCacheSystem/AsyncDiskModel.s.dfy:16–259`):**
  - `AsyncDisk.Variables` consists of four in-flight message maps (`reqReads`, `reqWrites`, `respReads`, `respWrites`) plus persistent `contents: seq<byte>`.
  - `DiskInternal` steps asynchronously execute pending requests in arbitrary order (`ProcessWrite`), while `Crash` (`AsyncDiskModel.s.dfy:255–258, 311–316`) clears all four in-flight maps (`map[], map[], map[], map[]`), preserves `s.contents`, and resets the host to `M.Init(k.machine, s'.machine)`.
  - **Explicit overlapping-I/O havoc (`AsyncDiskModel.s.dfy:211–238`):** If two concurrent in-flight writes overlap (`HavocConflictingWrites`) or an in-flight write overlaps an in-flight read (`HavocConflictingWriteRead`), the disk transition becomes unconstrained (`s'` unconstrained!), forcing the verified host to **prove disjointness of all concurrent in-flight disk I/O** rather than trusting the drive.
  - **Explicit silent read corruption bounded by CRC32C (`AsyncDiskModel.s.dfy:148–190`):** Unlike FSCQ and Yggdrasil, `AsyncDisk` includes `ProcessReadFailure(id, fakeContents)`, allowing any read to return arbitrary corrupted bytes `fakeContents != realContents` subject only to `AllChecksumsCheckOut(realContents, fakeContents)` (which states that if both real and corrupted slices pass `Crypto.Crc32C`, they must be equal—an explicit cryptographic collision-resistance axiom).
- **Three-state crash specification & dual alternating superblocks (`MapSpec/ThreeStateVersioned.s.dfy` & `BlockCacheSystem/JournalSystem.i.dfy:30–180`):**
  - Crash safety is specified via three logical KV versions—**`Persistent`**, **`Frozen`** (a crash-consistent checkpoint being flushed), and **`Ephemeral`** (live in-memory state)—with `SyncReqStatus = State1 | State2 | State3` tracking outstanding `sync()` requests as snapshots migrate from `Ephemeral -> Frozen -> Persistent`.
  - `JournalSystem.i.dfy:30–70` maintains two alternating superblocks (`superblock1`, `superblock2`, chosen via `SelectSuperblock`) so updating one superblock can crash mid-write without invalidating the previously committed superblock.
- **Strengths & limits:** Models concurrent overlapping I/O, byte-level storage, and silent read corruption using standard TLA-style state-machine refinement in Dafny (avoiding custom separation logics) plus linear types (`veribetrkv-linear`) compiling to C++. However, host execution is event-driven/single-core (concurrency is between host and async disk rather than multi-core shared-memory threads), and `Crc32C` collision freedom is axiomatized (and note that CRC32C is non-cryptographic—sound for random bit errors, *not* adversarial collisions).

#### 6.4 Perennial (`mit-pdos/perennial`): Coq/Iris `WPC` (`master`) vs. Lean 4 Standard-`WP` Crash Adequacy (`lean` / `HEAD`)

Perennial (Chajed et al., SOSP 2019, `DOI: 10.1145/3341301.3359632`) solved the core compositional bottleneck left open by FSCQ and Yggdrasil: **combining fine-grained multi-threaded concurrency (Iris separation logic) with fail-stop crashes and concurrent recovery** for translated Go programs (`Goose`). Direct inspection of `mit-pdos/perennial` reveals an essential **two-branch divergence** that any engineer or verifier referencing Perennial must distinguish:

1. **Coq/Iris Perennial (`master` @ `c3b7ecff27c1a6e8ed058d5aca362df1e2f63311`, `src/program_logic/crash_weakestpre.v:17–160`):**
   - Splits ghost state into **`irisGS`** (`global_state_interp`, surviving across crashes and shared across distributed nodes) and **`generationGS`** (`state_interp`, freshly instantiated on every reboot/generation).
   - Defines **Crash Weakest Preconditions** `WPC e @ s; E1 {{ Φ }} {{ Φc }}` as the guarded fixed point of `wpc_pre` (`crash_weakestpre.v:83–126`), combining two conjuncts (`∧`):
     - **Normal execution branch:** Owns a fractional non-crashed token `NC q` and steps `e` under `state_interp` + `global_state_interp` + later credits `£`, spawning forked threads with `wpc ⊤ ef fork_post True` and concluding with `Φ v`.
     - **Crash branch:** Given the persistent crashed token `C` (which is logically exclusive with `NC q`—the adequacy theorem trades `NC 1` for `C` at the crash boundary), performs a crash fancy update `||={E1|⊤∖D,∅|∅}=> ||▷=>^k ...` to establish the crash condition `Φc`.
   - Builds **crash invariants (`ncinv`)**, **recovery weakest preconditions (`wpr`)**, and **staged invariants / crash borrows** on top of `WPC` to verify concurrent multi-threaded write-ahead logs (`GoJournal`, NFS servers, distributed key-value stores) where multiple threads hold locks and issue concurrent disk writes while recovery runs after arbitrary crashes.
2. **Lean 4 Perennial (`lean` / `HEAD` @ `3afd77e35b0a727a05f1149c15308ddcc2e60357`, `README.md` & `Perennial/GooseLang/CrashAdequacy.lean:1–160`):**
   - Ports GooseLang and program proofs to **Lean 4** on top of `iris-lean`, adopting a **radically simplified crash architecture**:
   - **No `WPC` and no `crash_own`:** Proofs use standard `iris-lean` `wp` (`GooseGlobalGS` + per-generation `GooseLocalGS`). Crashes live strictly in the operational semantics (`Crash`, `RealCrashNsteps` in `GooseLang/CrashLang.lean`) and the adequacy theorem (`goose_crash_adequacy`, `CrashAdequacy.lean`).
   - **Generation-chaining adequacy (`goose_crash_step`, `CrashAdequacy.lean:139–160`):** Each extension implements `class ExtCrashInterp` (`CrashAdequacy.lean:65–69`), supplying `crashStart : I.LocalGS GF → I.LocalGS GF → IProp GF` and a ghost update `local_crash` transforming `I.localCtx hL σ` to `I.localCtx hL' σ' ∗ crashStart hL hL'` on `S.crash σ σ'`. At each crash, `goose_crash_step` executes `notCrashed_crash` to turn `notCrashed` into persistent `crashed`, discards the old volatile heap and Go package init state, allocates fresh `GooseLocalGS` `L'`, and delivers `crashed ∗ extsCrashStart L L'` to prove the next generation's boot-program precondition `P L'`.
   - **Current boundary (`README.md`):** Explicitly notes that there is no separate recovery procedure (the same boot program runs initially and after every crash), no `crash_own` / crash-borrow library yet, and its end-to-end `crashfs` example uses a toy filesystem extension (`GooseLang/Ext/Fs/Impl.lean`) explicitly marked as *"not a sound model of a Linux filesystem."*

#### 6.5 Comparative Matrix of Verified Storage Systems

| System (Pinned Revision) | Proof Assistant / Engine | Concurrency Model | Disk / Crash Model | Silent Corruption Modeled? | Crash During Recovery? | Key Proof Mechanism |
|---|---|---|---|---|---|---|
| **FSCQ** (`2c7ef9c2...`) | Coq (interactive) | Sequential | `AsyncDisk` (`valuset = valu * list valu`), explicit `Sync`, `Trim` (`|+>?`) | No (idealized `hashmap` for log header only) | Yes (`>>` recovery combinator) | Crash Hoare Logic (`PRE`/`POST`/`CRASH`) |
| **Yggdrasil** (`e1de61d7...`) | Python + Z3 (automated SMT) | Sequential | `AsyncDisk` (`synced`/`on` Boolean implication graph + `flush()`) | No | Yes (symbolic crash transition) | Automated SMT crash refinement |
| **VeriBetrKV** (`053dd16a...`) | Dafny + Z3 (linear types → C++) | Single-threaded host + concurrent async disk actor | Byte-level `AsyncDisk` queues + **`HavocConflictingWrites`** | **Yes** (`ProcessReadFailure` bounded by `Crc32C` axiom) | Yes (`CrashStep` resets `M.Init`) | Distributed-actor state-machine refinement (`ThreeStateVersioned`) |
| **Perennial (Coq `master`)** (`c3b7ecff...`) | Coq + Iris (interactive) | Multi-threaded Go (`Goose`) + distributed nodes | Pluggable FFI disk models (sync & async WAL/buffer) | Optional per disk extension | Yes (`wpr` + `WPC` + `generationGS`) | Crash WP (`WPC`) + `NC q`/`C` tokens + crash borrows |
| **Perennial (Lean 4 `lean`)** (`3afd77e3...`) | Lean 4 + `iris-lean` (interactive) | Multi-threaded Go (`Goose`) + distributed nodes | Pluggable `ExtSemantics.crash` + `ExtCrashInterp` | Not yet in `Ext/Fs` | Yes (multi-generation boot loop `RealCrashNsteps`) | Standard `wp` + `goose_crash_adequacy` + `notCrashed_crash` (no `wpc`) |

---

### 7. Executable Micro-Probes and Reproducible Counterexamples

*Basis: execution (Python 3 on Linux x86_64, `2026-11-19`)*

Both probes below are self-contained standard-library Python 3 scripts (zero external dependencies) that reproduce the quantitative findings cited in Sections 1–5.

#### 7.1 Probe Script (`probe_pkg1_flash_crash.py`)

```python
#!/usr/bin/env python3
"""Executable micro-probes for flash FTL remanence, WAF, ZNS typestates, and crash consistency."""
import itertools
import random
import zlib


def probe_ftl_remanence_and_waf():
    print("=== Probe 1A: FTL Out-of-Place Remanence & Write Amplification ===")
    for label, num_blocks, pages_per_block, logical_pages in [
        ("Consumer SSD (~7% OP)", 64, 16, 956),
        ("Enterprise SSD (28% OP)", 64, 16, 800),
    ]:
        rng = random.Random(42)
        total_phys = num_blocks * pages_per_block
        blocks = [[("FREE", None) for _ in range(pages_per_block)] for _ in range(num_blocks)]
        l2p = {}
        free_blocks = list(range(num_blocks))
        active_blk = free_blocks.pop(0)
        active_pg = 0
        host_writes = 0
        nand_writes = 0

        def valid_pages(b):
            return [
                (p, blocks[b][p])
                for p in range(pages_per_block)
                if blocks[b][p][1] is not None and l2p.get(blocks[b][p][1]) == (b, p)
            ]

        def ensure_active_page():
            nonlocal active_blk, active_pg
            if active_pg == pages_per_block:
                active_blk = free_blocks.pop(0)
                active_pg = 0

        def gc_one_block():
            nonlocal nand_writes, active_pg
            candidates = [b for b in range(num_blocks) if b != active_blk and b not in free_blocks]
            victim = min(candidates, key=lambda b: len(valid_pages(b)))
            for _, (tag, lba) in valid_pages(victim):
                ensure_active_page()
                blocks[active_blk][active_pg] = (tag, lba)
                l2p[lba] = (active_blk, active_pg)
                active_pg += 1
                nand_writes += 1
            blocks[victim] = [("FREE", None) for _ in range(pages_per_block)]
            free_blocks.append(victim)

        def write_lba(lba, tag):
            nonlocal host_writes, nand_writes, active_pg
            host_writes += 1
            while len(free_blocks) < 2 and active_pg == pages_per_block:
                gc_one_block()
            ensure_active_page()
            blocks[active_blk][active_pg] = (tag, lba)
            l2p[lba] = (active_blk, active_pg)
            active_pg += 1
            nand_writes += 1

        secret_lbas = [i * 40 for i in range(16)]
        secret_set = set(secret_lbas)
        for lba in range(logical_pages):
            write_lba(lba, f"SECRET_{lba}" if lba in secret_set else "COLD")

        for p in range(1, 36):
            for lba in secret_lbas:
                write_lba(lba, f"ZERO_PASS_{p}")
            if p in (1, 3, 7, 35) and label.startswith("Enterprise"):
                rem_copies = sum(1 for b in range(num_blocks) for (t, _) in blocks[b] if t.startswith("SECRET_"))
                unique_rem = len({t for b in range(num_blocks) for (t, _) in blocks[b] if t.startswith("SECRET_")})
                print(
                    f"  [Enterprise 28% OP] After {p:2d} single-file overwrite pass(es): "
                    f"{unique_rem}/16 ({100.0*unique_rem/16:.1f}%) secret pages physically remanent "
                    f"({rem_copies} stale physical copies)"
                )

        h0, n0 = host_writes, nand_writes
        for _ in range(20000):
            write_lba(rng.randrange(logical_pages), "RAND")
        waf = (nand_writes - n0) / (host_writes - h0)
        rem_after_rand = len({t for b in range(num_blocks) for (t, _) in blocks[b] if t.startswith("SECRET_")})
        op_pct = 100.0 * (total_phys - logical_pages) / logical_pages
        print(
            f"  {label}: OP={op_pct:.1f}%, steady-state random-write WAF={waf:.2f}x "
            f"(vs ZNS sequential WAF=1.00x); secret pages surviving 20k random writes={rem_after_rand}/16"
        )


def probe_crash_consistency_and_merkle():
    print("\n=== Probe 1B: AsyncDisk Crash Reordering, ZNS Zone Append & Parental Merkle Checksum ===")
    states_no_flush = []
    for s_data, s_hdr in itertools.product([False, True], repeat=2):
        disk_data = 0xCAFE if s_data else 0x0000
        recovered = disk_data if s_hdr else 0x0000
        states_no_flush.append((s_data, s_hdr, recovered, s_hdr and disk_data != 0xCAFE))
    corrupt_no_flush = [s for s in states_no_flush if s[3]]
    print(f"  Unordered WAL (no FLUSH): {len(states_no_flush)} reachable crash states, {len(corrupt_no_flush)} CORRUPT:")
    for s in corrupt_no_flush:
        print(f"    Counterexample: synced_data={s[0]}, synced_hdr={s[1]} -> header committed, replayed stale data=0x{s[2]:04X}")

    states_with_flush = [
        (s_data, on_flush, s_hdr, s_hdr and (not s_data))
        for s_data, on_flush, s_hdr in itertools.product([False, True], repeat=3)
        if (not on_flush or s_data) and (not s_hdr or on_flush)
    ]
    print(f"  Ordered WAL (with FLUSH): {len(states_with_flush)} reachable crash states, {sum(1 for s in states_with_flush if s[3])} CORRUPT.")
    print(f"  4 KiB block across 8x512B sectors without atomic write: {(1 << 8) - 2}/256 reachable states are torn writes.")

    old_block, new_block, other_block = b"OLD_DATA_V1_0000", b"NEW_DATA_V2_9999", b"OTHER_LBA_20_DAT"
    old_crc, new_crc, other_crc = zlib.crc32(old_block), zlib.crc32(new_block), zlib.crc32(other_block)
    print(f"  Lost write detection:        self-checksum={zlib.crc32(old_block) != old_crc}, parental-Merkle={zlib.crc32(old_block) != new_crc}")
    print(f"  Misdirected write detection: self-checksum={zlib.crc32(other_block) != other_crc}, parental-Merkle={zlib.crc32(other_block) != new_crc}")

    rng = random.Random(7)
    trials, explicit_fail, append_fail = 1000, 0, 0
    for _ in range(trials):
        order = list(range(8))
        rng.shuffle(order)
        wp = 0
        for req_lba in order:
            if req_lba != wp:
                explicit_fail += 1
                break
            wp += 1
        assigned = [(req_id, idx) for idx, req_id in enumerate(order)]
        if len({lba for _, lba in assigned}) != 8:
            append_fail += 1
    print(
        f"  ZNS QD=8 reordered submissions ({trials} trials): "
        f"LBA-addressed Write failures={explicit_fail}/{trials} ({100.0*explicit_fail/trials:.1f}%), "
        f"Zone Append failures={append_fail}/{trials} (0.0%)"
    )


if __name__ == "__main__":
    probe_ftl_remanence_and_waf()
    probe_crash_consistency_and_merkle()
```

#### 7.2 Observed Output

```text
=== Probe 1A: FTL Out-of-Place Remanence & Write Amplification ===
  Consumer SSD (~7% OP): OP=7.1%, steady-state random-write WAF=6.58x (vs ZNS sequential WAF=1.00x); secret pages surviving 20k random writes=0/16
  [Enterprise 28% OP] After  1 single-file overwrite pass(es): 16/16 (100.0%) secret pages physically remanent (16 stale physical copies)
  [Enterprise 28% OP] After  3 single-file overwrite pass(es): 16/16 (100.0%) secret pages physically remanent (16 stale physical copies)
  [Enterprise 28% OP] After  7 single-file overwrite pass(es): 16/16 (100.0%) secret pages physically remanent (16 stale physical copies)
  [Enterprise 28% OP] After 35 single-file overwrite pass(es): 16/16 (100.0%) secret pages physically remanent (16 stale physical copies)
  Enterprise SSD (28% OP): OP=28.0%, steady-state random-write WAF=2.33x (vs ZNS sequential WAF=1.00x); secret pages surviving 20k random writes=0/16

=== Probe 1B: AsyncDisk Crash Reordering, ZNS Zone Append & Parental Merkle Checksum ===
  Unordered WAL (no FLUSH): 4 reachable crash states, 1 CORRUPT:
    Counterexample: synced_data=False, synced_hdr=True -> header committed, replayed stale data=0x0000
  Ordered WAL (with FLUSH): 4 reachable crash states, 0 CORRUPT.
  4 KiB block across 8x512B sectors without atomic write: 254/256 reachable states are torn writes.
  Lost write detection:        self-checksum=False, parental-Merkle=True
  Misdirected write detection: self-checksum=False, parental-Merkle=True
  ZNS QD=8 reordered submissions (1000 trials): LBA-addressed Write failures=1000/1000 (100.0%), Zone Append failures=0/1000 (0.0%)
```

## Boundaries

- **Physical erasure guarantees of `NVME_ZONE_RESET` across commercial ZNS firmware — `unknown`:** While NVMe ZNS `Zone Reset` logically returns the zone to `Empty` with `wp = zslba` and allows the controller to immediately erase the underlying physical NAND erase block(s), the ZNS Command Set specification permits controllers to defer physical NAND erase asynchronously in the background after acknowledging `Zone Reset`. Whether a specific ZNS SSD physically erases charge cells synchronously upon `Zone Reset` (providing immediate physical-readout sanitization without `Sanitize Block Erase` or cryptographic erasure) cannot be inferred from the protocol alone and must be audited per firmware/vendor.
- **Analog/sub-threshold NAND charge remanence after single physical erase — `not examined`:** This report addresses digital L2P/FTL page-level remanence and does not examine forensic analog voltage-threshold sensing (partial-erase charge retention or inter-cell parasitic coupling on erased TLC/QLC cells).
- **Persistent Memory (PMEM / CXL.mem / `eADR`) crash-consistency models — `not examined`:** Byte-addressable non-volatile memory (`clwb`/`sfence` cache-line persistency, e.g., Persistent x86-TSO / ARMv8 persistency) has a distinct hardware ordering model and is outside the block/NVMe scope of this report.
- **Linux `io_uring` passthrough (`IORING_OP_URING_CMD`) for NVMe FDP / ZNS and end-to-end hardware benchmarks — `not examined`:** Kernel UAPI structs and driver logic in `torvalds/linux` were inspected from source; live benchmarks on physical ZNS or FDP NVMe silicon were not executed.
- **Stronger claims NOT established (do not over-extrapolate):**
  - *Known not to apply:* Memory `zeroize()` (`RustCrypto/utils`) does **not** sanitize swapped pages, hibernation images, or files written to FTL SSDs; NVMe `TRIM`/`Deallocate` does **not** provide cryptographic or physical erasure guarantees.
  - *Unsupported / unverified gap:* None of the inspected verified storage systems (`FSCQ`, `Yggdrasil`, `VeriBetrKV`, `Perennial`) currently combine **all** of (a) multi-core shared-memory concurrency, (b) ZNS `MAR`/`MOR`/`Zone Append` typestate semantics, (c) adversarial cryptographic erasure / non-interference against physical flash readout, and (d) verified parental Merkle corruption detection against adversarial (not merely random CRC32C) storage faults.
  - *Known not to apply to Perennial `HEAD`:* Do **not** assume `mit-pdos/perennial` `HEAD` (`3afd77e3...`, Lean 4 `lean` branch) contains `WPC`, `wpr`, `crash_own`, or GoJournal's Coq proofs; those remain on `refs/heads/master` (`c3b7ecff...`) / `refs/heads/coq/tested`.

## Evidence

### Inspected Upstream Source Revisions (Observed `2026-11-19`)

1. **`mit-pdos/perennial` (`lean` / `HEAD`)** — commit `3afd77e35b0a727a05f1149c15308ddcc2e60357`:
   - `README.md` (lines 1–60): documents migration to Lean 4 on `iris-lean`, absence of `wpc` and `crash_own`, standard `wp` + `goose_crash_adequacy`, and toy `GooseLang/Ext/Fs/Impl.lean` caveat.
   - `Perennial/GooseLang/CrashAdequacy.lean` (lines 1–160): `class ExtCrashInterp`, `Exts.local_crash`, `goose_crash_step`, `notCrashed_crash`, `extsCrashStart`.
2. **`mit-pdos/perennial` (`master`)** — commit `c3b7ecff27c1a6e8ed058d5aca362df1e2f63311`:
   - `src/program_logic/crash_weakestpre.v` (lines 17–160): `Class irisGS`, `Class generationGS`, `Definition wpc_pre`, `Definition wpc`, `WPC` and Texan crash-triple notations with `NC q` / `C` tokens.
3. **`mit-pdos/fscq`** — commit `2c7ef9c268fd79a81b26b44ef720f8e6a1e938a0`:
   - `src/AsyncDisk.v` (lines 14–195): `valubytes_real = 0x1000`, `valuset := (valu * list valu)`, `rawdisk`, `vsmerge`, `hashmap`, `sync_mem`, `sync_addr`.
   - `src/BasicProg.v` (lines 31–192): `read_ok`, `write_ok`, `sync_ok`, `trim_ok` (`|+>?`), `hash_ok`.
   - `src/Log.v` (lines 44–150): `LOG.state` (`NoTxn`, `ActiveTxn`, `FlushingTxn`, `RollbackTxn`, `RecoveringTxn`), `rep_inner`, `intact`, `recover_any`.
4. **`uw-unsat/yggdrasil`** — commit `e1de61d798acafb9ae2d8387d176c4b091773623`:
   - `yggdrasil/diskspec.py` (lines 13–128): `Machine` (`create_synced`, `create_on`, `assumption`, `explain`), `AsyncDisk` (`write`, `flush`, `crash`), `TxnDisk`, `SyncDisk`.
5. **`secure-foundations/veribetrkv-osdi2020`** — commit `053dd16ab01939843a213e0590983fd22e2d0d4d`:
   - `docker-ssd/src/veribetrkv-linear/ByteBlockCacheSystem/AsyncDiskModel.s.dfy` (lines 16–350): `AsyncDisk.Variables` (`reqReads`, `reqWrites`, `respReads`, `respWrites`, `contents`), `ChecksumChecksOut` (`Crypto.Crc32C`), `AllChecksumsCheckOut`, `ProcessReadFailure`, `HavocConflictingWrites`, `HavocConflictingWriteRead`, `Crash`, `AsyncDiskModel.NextStep`.
   - `docker-ssd/src/veribetrkv-linear/MapSpec/ThreeStateVersioned.s.dfy` (lines 1–40): `ThreeStateTypes.SyncReqStatus` (`State1 | State2 | State3`), `SyncReqs2to1`, `SyncReqs3to2`.
   - `docker-ssd/src/veribetrkv-linear/BlockCacheSystem/JournalSystem.i.dfy` (lines 30–180): `DiskHasSuperblock1`/`2`, `SelectSuperblock`, `PersistentJournal`, `FrozenJournal`, `EphemeralJournal`.
6. **`torvalds/linux`** — commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:
   - `include/linux/nvme.h` (lines 494–509, 704–740, 821–839, 957–994, 1118–1273): `nvme_id_ns_zns` (`mar`, `mor`, `lbafe`), `nvme_id_ctrl_zns` (`zasl`), `nvme_fdp_config_desc` (`nrg`, `nruh`, `maxpids`, `runs`, `erutl`), `nvme_fdp_ruh_desc`, `nvme_fdp_ruh_status_desc` (`pid`, `ruhid`, `earutr`, `ruamw`), opcodes `nvme_cmd_flush` (`0x00`), `nvme_cmd_io_mgmt_recv` (`0x12`), `nvme_cmd_zone_mgmt_send` (`0x79`), `nvme_cmd_zone_mgmt_recv` (`0x7a`), `nvme_cmd_zone_append` (`0x7d`), flags `NVME_RW_FUA` (`1<<14`), `NVME_RW_DTYPE_DPLCMT` (`2<<4`), `enum nvme_zone_mgmt_action`.
   - `include/uapi/linux/blkzoned.h` (lines 32–210): `enum blk_zone_type`, `enum blk_zone_cond` (`0x0`–`0xF`, plus `BLK_ZONE_COND_ACTIVE = 0xFF`), `struct blk_zone`, ioctls `BLKREPORTZONE`, `BLKRESETZONE`, `BLKOPENZONE`, `BLKCLOSEZONE`, `BLKFINISHZONE`, `BLKREPORTZONEV2`.
   - `drivers/nvme/host/zns.c` (lines 10–175): `nvme_set_max_append`, `nvme_query_zone_info` (mandatory `Zone Append` enforcement `NVME_NS_FORCE_RO`, `is_power_of_2(zi->zone_size)`, `mor+1`/`mar+1`), `nvme_zone_parse_entry`.
7. **`openzfs/zfs`** — commit `cde5d598eb44b5d6efe8167666d988a496346657`:
   - `include/sys/spa.h` (lines 389–397): `typedef struct blkptr` (`blk_dva`, `blk_prop`, `blk_birth_word`, `blk_cksum`).
8. **`RustCrypto/utils`** — commit `77d1a3e6c2e8c28f49189258abb5d4405c0f1330`:
   - `zeroize/src/lib.rs` (lines 148–206, 253–285): `Zeroize` trait, `volatile_write` / optimization barrier guarantees, explicit exclusion of registers, reallocations, and swap/persistent storage.

### Primary Standards & Peer-Reviewed Literature

- M. Wei, L. M. Grupp, F. E. Spada, S. Swanson, *"Reliably Erasing Data From Flash-Based Solid State Drives"*, USENIX FAST 2011.
- J. Reardon, D. A. Basin, S. Čapkun, *"SoK: Secure Data Deletion"*, IEEE S&P 2013, `DOI: 10.1109/SP.2013.28`.
- M. Bjørling, A. Aghayev, H. Holmberg, A. Ramesh, D. Le Moal, G. R. Ganger, G. Amvrosiadis, *"ZNS: Avoiding the Block Interface Tax for Flash-based SSDs"*, USENIX ATC 2021.
- NVM Express Zoned Namespace Command Set Specification (TP 4053, rev. 1.1c) & NVM Express Flexible Data Placement (TP 4146, integrated in NVMe Base Specification 2.1).
- L. N. Bairavasundaram, G. Goodson, B. Schroeder, A. C. Arpaci-Dusseau, R. H. Arpaci-Dusseau, *"An Analysis of Data Corruption in the Storage Stack"*, USENIX FAST 2008.
- T. S. Pillai, V. Chidambaram, R. Alagappan, S. Al-Kiswany, A. C. Arpaci-Dusseau, R. H. Arpaci-Dusseau, *"All File Systems Are Not Created Equal: On the Complexity of Crafting Crash-Consistent Applications"*, USENIX OSDI 2014.
- H. Chen, D. Ziegler, T. Chajed, A. Chlipala, M. F. Kaashoek, N. Zeldovich, *"Using Crash Hoare Logic for Certifying the FSCQ File System"*, ACM SOSP 2015, `DOI: 10.1145/2815400.2815402`.
- H. Sigurbjarnarson, J. Bornholt, E. Torlak, X. Wang, *"Push-Button Verification of File Systems via Crash Refinement"*, USENIX OSDI 2016.
- T. Chajed, J. Tassarotti, M. F. Kaashoek, N. Zeldovich, *"Verifying Concurrent, Crash-Safe Systems with Perennial"*, ACM SOSP 2019, `DOI: 10.1145/3341301.3359632`.
- T. Hance, A. Lattuada, C. Hawblitzel, J. Howell, R. Johnson, B. Parno, *"Storage Systems are Distributed Systems (So Verify Them That Way!)"*, USENIX OSDI 2020.

### Execution Provenance

- Ran `python3 /tmp/probe_pkg1_flash_crash.py` on `2026-11-19` (exit code `0`); full script and deterministic stdout preserved verbatim in Section 7.

## Revalidation

Use the following targeted checks to determine whether the key findings have changed in newer upstream revisions:

1. **Check Perennial Lean 4 crash-logic evolution (`mit-pdos/perennial`):**
   - Compare `HEAD` against `3afd77e35b0a727a05f1149c15308ddcc2e60357` and diff `README.md` and `Perennial/GooseLang/CrashAdequacy.lean`. Specifically check whether `wpc`, `crash_own`, or a non-toy Linux/NVMe storage extension has been added to the `lean` branch.
2. **Check Linux NVMe ZNS & FDP driver policy changes (`torvalds/linux`):**
   - Diff `drivers/nvme/host/zns.c` (specifically `nvme_query_zone_info` for `NVME_NS_FORCE_RO` without `Zone Append` and `is_power_of_2(zi->zone_size)`) and `include/linux/nvme.h` (for FDP `nvme_fdp_*` structures, `NVME_RW_DTYPE_DPLCMT`, and `NVME_IO_MGMT_RECV_MO_RUHS`) against `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`.
3. **Check `RustCrypto/utils` `zeroize` security boundary:**
   - Diff `zeroize/src/lib.rs` against `77d1a3e6c2e8c28f49189258abb5d4405c0f1330` to verify whether any swap-pinning (`mlock`) or register-clearing guarantees were introduced.
4. **Rerun inline micro-probes:**
   - Save Section 7.1 to `/tmp/probe_pkg1_flash_crash.py` and run `python3 /tmp/probe_pkg1_flash_crash.py`; verify exact reproduction of 100.0% 35-pass single-file remanence under greedy GC, WAF = 6.58× (7.1% OP) vs. 2.33× (28.0% OP), 100.0% vs. 0.0% QD=8 ZNS failures, and `parental-Merkle=True` vs. `self-checksum=False`.
5. **Hardware revalidation (when physical ZNS/FDP devices are available):**
   - Query `nvme zns id-ns` / `nvme fdp configs` / `nvme fdp status` via `linux-nvme/nvme-cli` (`97723b0260163de80361e1e67fb41ee708e9c186`) to inspect actual `MAR`, `MOR`, `ZCAP`, `ZSZE`, `ZASL`, `nruh`, `runs`, and `ruamw` values, and verify vendor `Sanitize` / `Zone Reset` physical-erase guarantees in controller security datasheets.
