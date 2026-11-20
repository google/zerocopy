# CRUSH straw2 Placement, Erasure-Coded Repair under Silent Corruption, and NFSv4 / SMB3 Delegation and Lease Revocation: Executed and Source-Level Invariants in Ceph, MinIO, klauspost/reedsolomon, NFS-Ganesha and Samba

## Summary

Three layers of a distributed storage stack each rest on an assumption that is cheap to state and easy to violate: placement assumes its pseudo-random draws are fair and that retries always find a slot; erasure-coded repair assumes every surviving shard it reads is correct; delegation and lease protocols assume a revoked holder stops writing. This report records what the pinned upstream code does about each assumption, with executed probes where the code could be run.

- **straw2 is fair and movement-optimal as measured on the unmodified upstream C code.** Over 10^6 inputs, selection frequencies match weights to within 0.1 percentage points, re-weighting one item moves exactly the ideal fraction (0.05455) and nothing moves between unchanged items. Draw ties occur at about 2 x 10^-5, so fixed-point precision is not a practical source of skew. The draw's entropy is 16 bits, not 48: the hash is masked with `0xffff` before the logarithm.
- **A straw2 item weight at or above 0x80000000 (32768.0 in 16.16 fixed point) wins every draw.** The weight is passed through an `int` parameter and becomes negative. The C builder accepts such weights and the text map compiler limits bucket weights only at 65535.0.
- **Retry exhaustion is measurable at default tunables.** With exactly as many failure domains as shards (6 hosts, 6 shards), 151 of 10^6 mappings are left with a hole at the default 50 tries and none at 100. A classic two-step rule that places several shards per host cannot re-map around a failed host at all (75% of mappings lose two slots with one of four hosts out); the multi-step-retry (MSR) rule type has zero incomplete mappings in the same scenario.
- **Erasure-only Reed-Solomon decoding propagates silent corruption.** In a validated re-implementation of the default klauspost/reedsolomon code, one flipped bit in one surviving shard makes the rebuilt shard wrong in 24 of 30 single-erasure cases; with as many erasures as parity shards it is wrong in 60 of 60 and parity can no longer even detect it. Regenerating parity from the wrong data yields a stripe that verifies. Checking each shard against its own checksum before decoding turns the error into an erasure and restores correct recovery.
- **The examined systems place that check differently.** MinIO verifies a HighwayHash of every shard block on every read, before decode. Ceph relies on BlueStore's per-block checksum (default `crc32c`) to turn bit rot into a read error; one of its two erasure-code paths (`ECBackendL.cc`) adds a whole-chunk hash check only for pools without overwrites and only for full-chunk reads. The Reed-Solomon library itself states that it "does not know which parts are invalid".
- **Revocation without storage-side fencing is unsafe; the standards say so only for pNFS.** RFC 8881 lets a server revoke an unreturned delegation after one lease period and *requires* fencing at data servers for pNFS layouts "without relying on a precise client lease timer". NFS-Ganesha revokes after one lease period (default 60 s) from a successful recall or two from the first attempt, using wall-clock `time(NULL)`. Samba waits 35 s for a lease-break acknowledgment and then downgrades the lease to none, "replying anyway". In a toy model, a stale holder's in-flight write overwrites the new holder's acknowledged write unless the storage target rejects the old epoch *before* the new grant.

## Applicability

**Subjects and how they relate.** Five repository revisions and one RFC were read directly. They are independent systems; the report compares how each discharges the same three obligations and does not describe a deployment that combines them.

| Subject | Role | Scope examined |
| --- | --- | --- |
| `ceph/ceph` | CRUSH placement; erasure-code backends; scrub and checksum defaults | `src/crush/{mapper.c,mapper.h,builder.c,crush.h,hash.c,crush.c,CrushCompiler.cc,CrushWrapper.h}`, `src/osd/{ECBackend.cc,ECBackendL.cc}`, `src/common/options/{global,osd}.yaml.in`, `doc/rados/**` pages named in Evidence |
| `klauspost/reedsolomon` | GF(2^8) Reed-Solomon library used by MinIO | `reedsolomon.go`, `matrix.go`, `galois.go`, `reedsolomon_test.go`, `README.md` |
| `minio/minio` | Object store with per-shard bit-rot hashes | `cmd/{bitrot.go,bitrot-streaming.go,erasure-decode.go,erasure-coding.go,xl-storage-format-v1.go}`, `README.md` |
| `nfs-ganesha/nfs-ganesha` | User-space NFSv4 server: leases, delegation recall and revocation | `src/SAL/{nfs4_lease.c,state_deleg.c,nfs4_recovery.c}`, `src/FSAL_UP/fsal_up_top.c`, `src/FSAL/FSAL_CEPH/main.c`, `src/support/nfs_read_conf.c`, `src/include/{gsh_config.h,connection_manager.h}`, `src/config_samples/config.txt` |
| `samba-team/samba` | SMB2/3 server: lease breaks, epochs, persistent handles | `source3/smbd/{smb2_oplock.c,smb2_break.c,smb2_create.c}`, `source3/locking/leases_db.c`, `source3/include/local.h` |
| RFC 8881 | Normative NFSv4.1 text | sections 8.4.3, 10.4.5, 10.4.6, 12.7.2, 12.7.3, 13.11 |

**Corrections to commonly stated premises**, each established by the evidence below:

- RFC 8881 specifies NFS version 4 minor version **1**. NFSv4.2 is a separate document that was not examined.
- MinIO has no `internal/xl-storage/` directory at the pinned revision; the storage and bit-rot code is under `cmd/`. Its repository README is headed "THIS REPOSITORY IS NO LONGER MAINTAINED."
- None of the examined systems uses BLAKE3 for shard verification: MinIO's default is HighwayHash256S (BLAKE2b-512 and SHA-256 remain selectable), Ceph's is CRC-32C.
- NFS-Ganesha's default lease is 60 s; 90 s is its default *grace* period.

**Exact observation versus extension.** CRUSH results come from executing unmodified upstream C files in a small harness and hold for the pinned revision of those files. The Reed-Solomon results come from an independent Python re-implementation checked against one upstream golden vector; they are properties of the code construction, not measurements of the Go library or of MinIO. The lease results come from a toy model. Nothing was run against a Ceph cluster, a MinIO server, an NFS or SMB server, a fault-injecting block device or a deterministic simulator.

## Findings

### 1. CRUSH straw2 placement

#### 1.1 The draw as coded

Basis: source (`src/crush/mapper.c`; lines quoted with comments elided).

```c
static inline __s64 generate_exponential_distribution(int type, int x, int y, int z, 
                                                      int weight)
{
	unsigned int u = crush_hash32_3(type, x, y, z);
	u &= 0xffff;
	__s64 ln = crush_ln(u) - 0x1000000000000ll;
	return div64_s64(ln, weight);
}

/* in bucket_straw2_choose(), with __u32 *weights: */
		if (weights[i]) {
			draw = generate_exponential_distribution(bucket->h.hash, x, ids[i], r, weights[i]);
		} else {
			draw = S64_MIN;
		}

		if (i == 0 || draw > high_draw) {
			high = i;
			high_draw = draw;
		}
```

So `u` has 16 bits of entropy, `ln` is non-positive (about `2^44 * log2((u+1)/65536)`), the weight is 16.16 fixed point, the largest draw wins and the strict comparison keeps the lowest index on ties.

`crush_ln` is a two-level table lookup returning a 48-bit fixed-point logarithm. The source comment explains the design: dividing a negative log-uniform value by the weight makes "a larger weight" give "a larger (less negative) value for draw", i.e. each item draws from an exponential distribution with rate proportional to its weight and the maximum wins.

#### 1.2 Executed properties of the unmodified upstream code

Basis: execution (the CRUSH probe: upstream `mapper.c`, `hash.c`, `builder.c`, `crush.c` compiled unmodified; `mapper.c` is textually included so that its static functions can be called).

| Property | Result |
| --- | --- |
| `crush_ln` range | `crush_ln(0) = 0`, `crush_ln(0xffff) = 0xfffff0000000` (2^28 short of 2^48) |
| `crush_ln` accuracy | maximum error against `log2(u+1)` is 4.4 x 10^-5 (in log2 units) |
| `crush_ln` monotonicity | 1 adjacent decrease and 10,007 adjacent equal pairs over the 65,536 inputs |
| Proportionality, weights 1:2:3:4, 10^6 inputs | 0.09933 / 0.19970 / 0.30079 / 0.40018 |
| Re-weighting one item 4 -> 5 | fraction moved 0.05455 (ideal 5/11 - 4/10 = 0.05455); moves between unchanged items: 0 |
| Ties between two equal-weight items | 17 per 10^6 at weight 1.0 and 128.0; 29 per 10^6 at weight 16384.0; lower index share 0.50012-0.50013 |
| All weights zero | item at index 0 is returned |
| Item weight `0x7fffffff` versus `0x7fffffff` | shares 0.50014 / 0.49986 |
| Item weight `0x80000000` versus `0x7fffffff` | the `0x80000000` item is chosen for 1,000,000 of 1,000,000 inputs |

Three consequences.

1. **Precision is not the weak point.** The table logarithm has one non-monotone step and about 15% plateaus, yet the measured distribution and the movement property are indistinguishable from ideal at 10^6 samples, and ties are at the 1/65536 scale expected from a 16-bit `u`. Claims that 48-bit fixed-point "saturation" skews placement are not supported by this evidence; at weight 16384.0 the tie rate less than doubles.
2. **The signed weight parameter is a real cliff.** `generate_exponential_distribution(int type, int x, int y, int z, int weight)` receives the `__u32` item weight as `int`. From `0x80000000` upward the divisor is negative, the draw becomes non-negative and beats every ordinary (negative) draw. `crush_addition_is_unsafe()` in `builder.c` guards only 32-bit unsigned overflow of sums, and `CrushCompiler.cc` rejects an item that is itself a bucket only above `CRUSH_MAX_BUCKET_WEIGHT`, defined in `crush.h` as `(65535u * 0x10000u)`, with an error composed as `"bucket weight limited to " << CRUSH_MAX_BUCKET_WEIGHT / 0x10000 << " to prevent overflow"`; device items are capped separately at `CRUSH_MAX_DEVICE_WEIGHT` (100.0), so through the text compiler the hazardous range is reachable only for a nested bucket. Weights from 32768.0 up to and including 65535.0 therefore pass both checks (provided the parent bucket's 32-bit weight sum does not overflow); the probe shows the draw inverted at the lower end, and the same sign argument applies across the range. Under the common convention of one weight unit per TiB (a convention, not something the mapper enforces), that range starts at a 32 PiB subtree. The probe exercised the draw with leaf items for simplicity; the draw function is the same whether the item is a device or a bucket. Whether any monitor-side command path rejects such weights earlier was not examined, and no upstream issue describing this was identified.
3. **An all-zero bucket still returns its first item.** Rejection then depends on the later `is_out()` test, which consults the separate per-device reweight vector (a device is out if its entry is 0, in if at least `0x10000`, otherwise in with probability `entry / 65536` using a 16-bit hash).

#### 1.3 Retry exhaustion and failure-domain shortage

Basis: execution (the CRUSH probe, upstream `crush_do_rule`, default tunables from `set_optimal_crush_map()`: `choose_total_tries = 50`, `chooseleaf_descend_once = 1`, `chooseleaf_vary_r = 1`, `chooseleaf_stable = 1`).

| Scenario (hosts x 4 OSDs) | Rule | Incomplete mappings |
| --- | --- | --- |
| 6 hosts, all in | erasure, `chooseleaf indep 6 type host`, 50 tries | 151 / 10^6 (1.5 x 10^-4), one hole each |
| 6 hosts, all in | same with `set_choose_tries 100` | 0 / 10^6 |
| 6 hosts, all in | replicated, `chooseleaf firstn 3 type host` | 0 / 10^6 |
| 7 hosts, all in | erasure 6 | 0 / 10^6 |
| 7 hosts, one host out (reweight 0) | erasure 6 | 566 / 10^6 (5.7 x 10^-4) |
| 4 hosts, all in | classic `choose indep 3 type host` then `choose indep 2 type osd` | 0 / 200,000 |
| 4 hosts, one host out | same classic rule | 150,063 / 200,000 (75%), two holes each |
| 4 hosts, one host out | MSR `choosemsr 3 type host` then `choosemsr 2 type osd` | 0 / 200,000 |

The first row is the behaviour Ceph's troubleshooting guide calls "CRUSH Gives up too Soon": "If the Ceph cluster has just enough OSDs to map the PG ... it is possible that CRUSH gives up before finding a mapping", with `set_choose_tries 100` as the documented remedy (Basis: documentation). A hole appears in an erasure-coded mapping as `CRUSH_ITEM_NONE` (`0x7fffffff`) at a fixed position, leaving that placement group undersized although every device is healthy. As a rough consistency check only (not a derivation of the retry algorithm): if the last slot needed one specific host of six on each of 50 independent tries, the miss probability would be (5/6)^50 = 1.1 x 10^-4, the same order as the measured 1.5 x 10^-4.

The 75% row is structural, not statistical. The upstream comment on `crush_msr_do_rule` explains it: with two `choose` steps, "If all of the OSDs on a host are marked down, the PGs will simply be degraded and unable to remap until the host is removed from the CRUSH heirarchy or reweighted to 0", because conventional rules "do not retry steps outside of a CHOOSELEAF step". MSR rules re-run the whole descent. They require the map tunables `msr_descents` and `msr_collision_tries`; the C builder leaves both at 0 (every MSR mapping then fails), while `CrushWrapper::set_default_msr_tunables()` sets both to 100, the value used in the probe.

#### 1.4 Variance and capacity-imbalanced failure domains

Basis: execution (the CRUSH probe).

| Scenario | Per-OSD placement count |
| --- | --- |
| 144 OSDs, 4,096 PGs x 3 replicas | mean 85.3, min 63, max 111, standard deviation 8.77, max/mean 1.30 |
| 144 OSDs, 65,536 PGs x 3 replicas | mean 1365.3, min 1256, max 1455, standard deviation 40.3, max/mean 1.07 |
| three failure domains weighted 4 : 4 : 8, three replicas, one per domain | replica shares 0.333 / 0.333 / 0.333; fill relative to weight 1.33 / 1.33 / 0.67 |

The first two rows are ordinary multinomial spread (standard deviation close to the square root of the mean): at about 85 placements per device the fullest device carries 30% more than average with a perfectly fair hash. The third row is a constraint effect: when the rule demands one replica per domain and there are exactly as many domains as replicas, weights inside the domain level are irrelevant and the small domains fill 33% faster than their capacity share. Neither effect is a straw2 defect; both are reasons operators add explicit placement overrides, which were not examined here.

### 2. Erasure-coded reads, scrub and repair under silent corruption

#### 2.1 What an erasure-only decoder guarantees

Basis: source (`klauspost/reedsolomon`) + execution (the Reed-Solomon probe, an independent re-implementation, not the upstream Go code).

The library builds its default coding matrix as a Vandermonde matrix `V[r][c] = r^c` over GF(2^8) (field polynomial `generatingPolynomial = 29`, i.e. 0x11d) multiplied by the inverse of its top square so that data shards are stored unchanged (`buildMatrix` in `reedsolomon.go`). `Reconstruct` takes shards with missing entries marked nil, inverts the sub-matrix for "the rows of the matrix that correspond to" the **first** `dataShards` valid indices (`for subMatrixRow, validIndex := range validIndices[:r.dataShards]`) and recomputes the missing shards. It never examines the content of a present shard. The README is explicit: "The encoder *does not know which parts are invalid*, so if data corruption is a likely scenario, you need to implement a hash check for each shard. If a byte has changed in your set, and you don't know which it is, there is no way to reconstruct the data set."

The Reed-Solomon probe re-implements that construction in Python and first checks it against the upstream golden vector in `reedsolomon_test.go` (`TestOneEncode`, 5+5: data `{0,1},{4,5},{2,3},{6,7},{8,9}` must give parity `{12,13},{10,11},{14,15},{90,91},{94,95}`); the re-implementation matches. On a 4+2 stripe of 64-byte shards:

| Experiment | Result |
| --- | --- |
| One bit flipped in shard 1, shard 0 erased, decode from shards 1-4 | rebuilt shard 0 has 1 wrong byte; `Verify` on the stripe is false because the unused parity shard disagrees |
| Then regenerate all parity from the (wrong) data | `Verify` is true; shards 0, 1 and 5 now differ from the original |
| Same fault, but each shard is first checked against its own checksum | erasures become {0, 1}; decode from shards 2-5; all six shards correct |
| All 30 (erased, corrupted) pairs, one flipped bit | rebuilt shard wrong in 24/30; post-rebuild `Verify` false in 30/30 |
| All 60 (two erased, one corrupted) cases | rebuilt shards wrong in 60/60; `Verify` false in 0/60 |
| Locate the culprit from parity alone, no erasure | exactly one consistent candidate: locatable |
| Locate the culprit with one erasure | five consistent candidates: not locatable |

The table is the classical bound made concrete: a code with `m` parity shards handles `e` erasures and `t` errors when `e + 2t <= m`. An erasure-only decoder spends nothing on `t`, so (i) while a spare shard remains (`e < m`) corruption is *detectable* by re-verification but not *locatable*; (ii) at `e = m` it is not even detectable; (iii) the 6 of 30 "lucky" cases are those where the corrupted shard happened not to be among the first `k` used. A per-shard checksum converts each error into an erasure, doubling what the same parity can absorb. The second row is the mechanism by which a repair makes damage permanent: once parity is recomputed from wrong data, every shard agrees on a wrong codeword and no later scrub can tell.

#### 2.2 Where each system puts the per-shard check

Basis: source, except where marked documentation.

| System | Check | When | On mismatch |
| --- | --- | --- | --- |
| MinIO | `streamingBitrotReader.ReadAt` reads a stored hash, then the shard block, and compares `b.h.Sum(nil)` with `b.hashBytes`; `DefaultBitrotAlgorithm = HighwayHash256S` (the algorithm table also lists `sha256`, `blake2b` and `highwayhash256`) | every shard-block read, before any decode | returns `errFileCorrupt`; `parallelReader.Read` sets the bit-rot heal flag, drops that reader (`p.readers[i] = nil`) and triggers another read, so the block enters `ReconstructData` as an erasure |
| Ceph, object store | BlueStore data checksums; option `bluestore_csum_type` default `crc32c`, with `none` selectable (documentation: "BlueStore checksums all metadata and all data written to disk") | every read of a block | read error surfaces to the erasure-code backend, which records it per shard so that "other chunks could substitute" |
| Ceph, older erasure-code path (`ECBackendL.cc`, kept alongside `ECBackend.cc`) | whole-chunk CRC kept in the object's hash-info attribute | only `if (!get_parent()->get_pool().allows_ecoverwrites())` and only when the read covers the entire chunk from offset 0 | logs "Bad hash for ..." and returns `-EIO` for that shard |
| Ceph, newer erasure-code path (`ECBackend.cc`) | no chunk-hash comparison found in this file; the sub-read relies on the object store's error ("Allow EIO return"); deep scrub passes a computed digest onward when `sinfo.supports_encode_decode_crcs()` or more than one zone | read; deep scrub | per-shard error reply |
| klauspost/reedsolomon | none; `Verify` only recomputes parity | caller-driven | boolean |

The Ceph source comment at the `ECBackendL.cc` check states its own limit: "This shows that we still need deep scrub because large enough files are read in sections, so the digest check here won't be done here." With `bluestore_csum_type = none`, or on an object store without block checksums, Ceph's erasure-coded read and recovery paths are in the position of section 2.1. Deep scrub is the backstop: defaults at the pinned revision are `osd_scrub_min_interval` 1 day, `osd_scrub_max_interval` 7 days, `osd_deep_scrub_interval` 7 days, and `osd_scrub_auto_repair` false (automatic repair, when enabled, is skipped above `osd_scrub_auto_repair_num_errors` = 5).

Basis: documentation (BlueStore configuration reference at the pinned revision). The cost and strength of the check are tunable: a checksum "usually 4 bytes" per block, with undetected-corruption odds of "about one in four billion" for 32 bits, "1 in 65,536" for 16 and "1 in 256" for 8.

#### 2.3 Local reconstruction codes

Basis: documentation (Ceph LRC plugin page at the pinned revision; Huang et al., "Erasure Coding in Windows Azure Storage", USENIX ATC 2012, via secondary summary).

Ceph's `lrc` plugin "creates local parity chunks to enable recovery using fewer surviving OSDs": with `k=8, m=4, l=4` a single lost chunk "can be recovered with only four OSDs instead of eight". With `k=4, m=2, l=3` the six chunks form two groups of three, each with one extra local parity, eight chunks in all: storage overhead 2.0x against 1.5x for plain 4+2 (derived). The Azure (12, 2, 2) code stores 16 fragments for 12 data fragments (1.33x) and repairs a single data fragment from 6 fragments instead of 12.

Derived consequence for corruption: a local group is a small code with one parity, so it has `m = 1` *locally*. A local repair that reads a silently corrupted group member has `e = 1 = m`: by section 2.1 the corruption is neither locatable nor detectable inside the group. Local repair is therefore the cheapest path and also the one with the least redundancy against unverified inputs; it is safe only when every group member is checksum-verified first, or when the result is cross-checked against global parity. This was not executed against the Ceph plugin.

### 3. Delegations, leases and revocation

#### 3.1 What the standard requires

Basis: normative (RFC 8881, read in full text).

- Section 10.4.5: a client "may be unaware of a failure in the backchannel. This lack of awareness could result in the client finding out long after the failure that its delegation has been revoked, and another client has modified the data for which the client had a delegation." And: "servers SHOULD revoke delegations that are not returned in a period of time equal to the lease period."
- Section 8.4.3: after a partition longer than the lease, locks of an expired lease "do not prevent such a conflicting lock from being granted but MUST be revoked as necessary", and "all I/O submitted by the client with the now invalid stateids will fail with the server returning the error NFS4ERR_EXPIRED."
- Section 12.7.2 states the in-flight problem directly: "While clients SHOULD NOT send I/Os to storage devices that may extend past the lease expiration time period, this is not always possible, for example, an extended network partition that starts after the I/O is sent and does not heal until the I/O request is received by the storage device. Thus, the metadata server and/or storage devices are responsible for protecting themselves from I/Os that are both sent before the lease expires and arrive after the lease expires." Section 12.7.3 concludes that the metadata server and its storage devices "MUST solve this by fencing the client."
- Section 13.11 (pNFS file layouts): fencing "can prevent all I/Os to data servers from being executed after lease expiration ... without relying on a precise client lease timer and without requiring data servers to maintain lease timers", and "once a client's layout has been revoked, the pNFS server MUST prevent the client from sending I/O for the affected file from and to all data servers".

The asymmetry is the finding: where the client reaches storage *through* the server (plain NFSv4.1), rejecting the stale stateid at the server is the fence. Where the client reaches storage *directly* (pNFS), the standard demands a fence at the storage device and explicitly declines to rely on clocks.

Basis: documentation (MS-SMB2 via secondary summary; the Microsoft document was not retrieved). An SMB2 server arms a lease-break acknowledgment timer (35 s in Windows behaviour); on expiry it sets the lease state to none and completes the waiting operation. Lease version 2 carries a 16-bit epoch incremented on each state change so that a client can discard out-of-order break notifications.

#### 3.2 NFS-Ganesha

Basis: source.

| Aspect | Behaviour | Location |
| --- | --- | --- |
| Lease lifetime | default 60 s; accepted range 1-180 in code, documented as 1-120 in the sample configuration | `LEASE_LIFETIME_DEFAULT 60`; `CONF_ITEM_UI32("Lease_Lifetime", 1, 180, ...)`; `config.txt`: "range 1 to 120" |
| Grace period | default 90 s; range 0-270 in code, documented 0-180 | `GRACE_PERIOD_DEFAULT 90`; `CONF_ITEM_UI32("Grace_Period", 0, 270, ...)` |
| Delegations | off by default | `CONF_ITEM_BOOL("Delegations", false, ...)` |
| Lease validity clock | wall clock: `t = time(NULL); if (clientid->cid_last_renew + nfs_param.nfsv4_param.lease_lifetime > t)` | `_valid_lease()` in `nfs4_lease.c` |
| Grace period clock | monotonic: `clock_gettime(CLOCK_MONOTONIC, &current_grace)` | `nfs4_recovery.c` |
| Revocation rule | revoke if more than one lease lifetime since the recall was successfully sent, or more than two since the first attempt (both measured with `time(NULL)`) | `eval_deleg_revoke()` in `fsal_up_top.c` |
| Repeat offenders | no new delegation to a client with more than two revocations | `state_deleg.c`: `if (client->num_revokes > 2)` |
| Storage-side timeout (CephFS backend) | `dt = lease_lifetime * 2 + 5` passed to `ceph_set_deleg_timeout()` | `FSAL_CEPH/main.c` |

The CephFS comment states the fencing relationship directly: the timeout is "long enough to give ganesha a chance to kick out a misbehaving client, but shorter than ceph cluster-wide MDS session timeout. Exceeding the MDS session timeout may result in the client (ganesha) being blacklisted in the cluster." So the storage-side fence exists, but its subject is the *gateway*, not the NFS client: the file system evicts a gateway that fails to return a delegation, and the gateway in turn revokes its own client one to two lease periods after recall.

Two derived observations. First, the sample-configuration ranges disagree with the parser's (120 versus 180, 180 versus 270); the code governs. Second, lease expiry and revocation are computed from `time(NULL)` while grace uses the monotonic clock: a backward wall-clock step extends every lease and delays revocation by the step size, a forward step expires leases early. Nothing in the examined files compensates for that.

The clustering header (`connection_manager.h`) documents a failover hazard of the same family in its own words: a client moves to a second server while a slow third server delays draining; "The lease times-out, and Server 1 releases the Client's lock", "Another client takes that lock", and the original client "won't be able to RECLAIM their lock". The stated fix is to extend the lease to `now + Lease_Lifetime + "Max time before kicking-out non-responsive servers"`, a time-based guard rather than a fence.

#### 3.3 Samba

Basis: source.

- `OPLOCK_BREAK_TIMEOUT` is 35 s (`source3/include/local.h`: "Timeout (in seconds) to wait for an oplock break message to return from the client"); the lease-break timer is armed with `timeval_current_ofs(OPLOCK_BREAK_TIMEOUT, 0)`.
- On expiry, `lease_timeout_handler()` in `smb2_oplock.c` logs "lease break timed out for file %s -- replying anyway" and calls `downgrade_lease(..., SMB2_LEASE_NONE)`. The server proceeds with the conflicting open; the previous holder's handle is not closed by this path.
- The handler samples `uint16_t old_epoch = lease->lease.lease_epoch` and, after refreshing lease state, returns without acting if the epoch changed ("lease break timeout race (epoch) ... ignoring"), then likewise if the break-in-progress flag cleared. The epoch here guards the *server's own* timer against a concurrent state change; it is not a storage fence.
- Break notifications carry the epoch only for version-2 leases (`if (fsp->lease->lease.lease_version > 1) new_epoch = fsp->lease->lease.lease_epoch; else new_epoch = 0;` in `smb2_break.c`). The field is 16 bits throughout (`leases_db.c`), so it wraps after 65,536 state changes of one lease.
- Persistent handles are considered only when the durable-v2 request sets the persistent flag, the server advertises `SMB2_CAP_PERSISTENT_HANDLES`, the share advertises continuous availability, and the request asks for no oplock or for a lease; the comment reads "Dont grant Persistent Handles with oplocks as they're broken on Windows and no one knows how they should behave."

An SMB client cannot bypass the server to reach storage, so, as with plain NFSv4.1, the server is the fence for one server. Across a clustered failover the question becomes whether the *new* node can reject I/O that the *old* node still has in flight; the clustering database code was not examined.

#### 3.4 Toy model: what fencing must order, and what clocks alone cost

Basis: execution (lease toy model written for this report; not NFS-Ganesha, Samba or Ceph code).

Events: the manager gives up on holder A (revoke), optionally raises the minimum epoch at the storage target (fence), grants to B, B reads, B writes (acknowledged), and A's earlier write (tagged with the old epoch) arrives at any point. Invariants: I1, B's acknowledged write is not overwritten; I2, while B holds the exclusive grant the stored value changes only through B.

| Storage behaviour | Schedules | I1 violated | I2 violated |
| --- | --- | --- | --- |
| accepts any write | 5 | 1 | 2 |
| raises the epoch on B's first write | 5 | 0 | 1 |
| epoch raised before the grant | 6 | 0 | 0 |

Fencing on first use repairs the lost update but still lets A's write land between B's read and B's write, silently staling B's exclusive cache. Only fence-before-grant is clean, which is the ordering RFC 8881 section 13.11 prescribes ("it must make sure that all layout state from that previous instance are invalidated at the data servers" before acting).

Without a fence, safety must be bought with time. If clocks drift by at most a fraction `rho` and a message takes at most `D`, a holder that stops sending when its own clock reads `L - g_c` and a manager that grants at `L + g_s` on its clock are safe iff `(L - g_c)/(1 - rho) + D < (L + g_s)/(1 + rho)`. For a server-only guard that is `g_s > L * 2*rho/(1 - rho) + D*(1 + rho)`. With `L` = 60 s, `rho` = 1%, `D` = 0.5 s the probe finds 1718 ms as the smallest safe integer guard (closed form 1717.1 ms); zero guard and a 500 ms guard are both unsafe. The bound is linear in `D`, and `D` is unbounded for a write already queued behind a partition, which is why time alone cannot give the guarantee the fence gives.

### 4. Cross-cutting assessment

#### 4.1 Performance and resource footprint (L1-L6)

Basis: execution where a probe is named, source for line counts and defaults, documentation for upstream-reported throughput. No figure here is a benchmark of a deployed cluster.

| Level | CRUSH placement | Erasure coding and scrub | Leases and delegations |
| --- | --- | --- | --- |
| L1 authoring effort | `mapper.c` 2,053 lines, `builder.c` 1,530; probe harness 114 lines of C. No mechanised proofs upstream; LLM or person-month budgets not examined | `ECBackend.cc` 1,904 and `ECBackendL.cc` 1,882 lines; `ErasureCodeLrc.cc` 1,194; reedsolomon 28,582 lines of Go in 47 top-level files; MinIO `bitrot-streaming.go` 215; probe 87 lines of Python | Ganesha `nfs4_lease.c` 287, `state_deleg.c` 1,266, `fsal_up_top.c` 2,213; Samba `smb2_oplock.c` 2,066; probe 47 lines |
| L2 toolchain build | four upstream C files plus harness: 1.3 s with gcc 15.2 `-O2`, 36.8 KB of text | not built (no Go toolchain available) | not built |
| L3 analysis latency | full CRUSH probe (about 6 x 10^6 rule evaluations and 10^7 direct bucket draws) 28.9 s | Reed-Solomon probe 0.1 s | lease probe under 0.1 s (16 schedules) |
| L4 runtime | measured: `crush_do_rule` 3.4 us per three-replica mapping over 12 hosts x 12 OSDs, about 2.9 x 10^5 mappings/s on one EPYC 7B12 core | upstream-reported (README): "speeds exceeding 1GB/s/cpu core"; e.g. `BenchmarkEncodeAligned100x20x10000-32 ... 34084.15 MB/s`. Not measured here. Local repair reads 4 chunks instead of 8 (LRC `k=8,m=4,l=4`) | timers, not throughput: 60 s lease, 60-120 s to revocation, 35 s SMB break timeout, 125 s CephFS delegation timeout at defaults |
| L5 verification speed | not applicable (no certificate) | deep scrub re-reads all data every 7 days by default; hash throughput not measured | not applicable |
| L6 memory / disk | measured: CRUSH workspace 1,004 bytes for that map | 4 bytes of CRC per BlueStore block (documentation); 32-byte HighwayHash per MinIO shard block; LRC `k=4,m=2,l=3` stores 2.0x against 1.5x for 4+2 | lease epoch 16 bits; per-client revoke counter; memory per lease not examined |

#### 4.2 Human comprehensibility and model simplicity (C1-C2)

Basis: derived.

**C1, comprehensibility.** straw2 is locally comprehensible: one loop, one comparison, and its fairness and movement properties can be checked by a 100-line harness. The retry machinery is not: whether a mapping is complete depends on six tunables, the rule's step structure and the reweight vector, and the failure signature is a sentinel integer (`2147483647`) in a result list. The signed-weight cliff is a hidden footgun in the literal sense: nothing at the call site, in the builder or in the compiler's error text suggests that 32768.0 is special. For erasure coding the hazard is an *absent* precondition: `Reconstruct(shards)` has the same type whether or not its inputs were verified, and the README sentence that states the obligation is prose. For leases, the reader must combine three clocks (client, server wall clock, server monotonic clock), two timeouts per protocol and a storage-layer eviction rule that lives in a different project; Ganesha's CephFS comment and `connection_manager.h` narrative are the only places the cross-layer argument is written down. An automated agent can enumerate these facts quickly, but that is execution ease, not comprehension: each hazard above is a cross-module obligation that neither a person nor an agent can see from the local code.

**C2, simplicity.** The three obligations reduce to two primitives. (i) *Only verified inputs enter a reconstruction*: whether the object is a shard, a replica or a parity block, a decode consumes values carrying evidence of integrity, and an unverified value is simply an erasure. That makes "bit rot" and "missing disk" the same case, removes the special scrub-versus-read distinction (the `ECBackendL.cc` check differs between whole-chunk and partial reads only because the evidence is whole-chunk), and gives the exact tolerance `e <= m` instead of `e + 2t <= m`. (ii) *A grant is an epoch, and the resource enforces epochs*: delegation, lease, layout and placement-map version are all monotone tokens; a write is admissible iff its token is not older than the newest the target has been told about. Under that model revocation is "tell the target, then grant", pNFS fencing and gateway eviction are ordinary cases, and clock guards become an optimisation rather than the safety argument. What the model does not absorb, and must not be hidden in adapters: the 16-bit epoch wrap, signed versus unsigned weights, and the `k`-of-`n` choice of *which* verified shards to read are medium-specific quirks; and moving verification into "the storage layer" merely relocates the obligation unless the decode interface refuses unverified shards by construction.

#### 4.3 How solutions in each area are validated (V1-V4)

| | CRUSH placement | Erasure coding and scrub | Leases and delegations |
| --- | --- | --- | --- |
| V1 specification adequacy and mutation | Basis: execution. The proportionality and exact-movement checks in the CRUSH probe are property tests of the specification itself; the `0x80000000` case is a boundary-value mutant of the weight domain that the upstream builder accepts | Basis: execution. The Reed-Solomon probe is validated against an upstream golden vector, then shows the decode contract is vacuous about input integrity (24/30 and 60/60 wrong outputs satisfy it) | Basis: execution (toy). Three storage behaviours act as mutants of the fencing rule; the invariant I2 kills "fence on first write", which I1 alone does not |
| V2 lowering and checker soundness | not examined: no differential run against the kernel client's copy of the mapper | not examined: the Go assembly kernels were not run, so no differential test of vectorised against scalar GF(2^8) arithmetic was possible; the Reed-Solomon probe is a third implementation suitable as an oracle for one | not examined |
| V3 concurrency, crash and fault injection | Basis: execution. Device-out injection through the reweight vector (one host out) in the CRUSH probe. Map-change races not examined | Basis: execution (re-implementation). Single-bit rot injection over all shard positions. Torn-write and power-cut permutation testing (CrashMonkey-style) and deterministic partition simulation were **not** performed | Basis: execution (toy). Exhaustive schedules of one stale write; drift and delay bounds in closed form. No real server was partitioned |
| V4 plant-level replay and human factors | not performed: no production cluster map was replayed; the capacity-imbalance row is synthetic | not performed: no field corruption trace was replayed. Field data exist (Bairavasundaram et al., FAST 2008: over 400,000 checksum mismatches across 1.53 million drives in 41 months, per secondary summary) | not performed; operator comprehension of lease/grace interplay was not tested |

## Boundaries

- **Not examined: the CRUSH paper's text** (Weil, Brandt, Miller, Maltzahn, SC 2006, DOI 10.1145/1188455.1188582). Bibliographic data were confirmed by search; straw2 post-dates that paper and is characterised here from code only.
- **Unknown: whether a live Ceph monitor can be brought to store a straw2 item weight of 32768.0 or more.** The C builder and the text compiler accept it and the mapper then selects that item for every input; command-path validation and existing clusters' weights were not examined. The observation is about the library, not a demonstrated production fault.
- **Not examined: `pg-upmap` overrides, the balancer, choose-args weight sets, device classes, straw (version 1), list, tree and uniform buckets, and the kernel client's mapper.**
- **Known not to apply: the Reed-Solomon results to MinIO's or Ceph's shipped read paths as configured by default.** MinIO verifies a hash before decode; Ceph's default object store checksums every block. The results apply to any caller that hands unverified shards to an erasure-only decoder, and to Ceph with `bluestore_csum_type = none`.
- **Not examined: which Ceph pools use the `ECBackendL.cc` path and which the `ECBackend.cc` path**; the two files are described separately and neither is claimed to be the default.
- **Not executed: the upstream Go library, its SIMD kernels, the Leopard GF(2^16) mode, MinIO's healing code, Ceph's erasure-code plugins and scrub.** No Go toolchain or cluster was available.
- **Not established: any claim about the Ceph LRC plugin's behaviour on corrupted group members**; section 2.3 is a derived argument from code-independent coding theory.
- **Not examined: NFSv4.2 (RFC 7862), MS-SMB2 first-hand, Samba's clustering database and persistent-handle recovery path, Ganesha's RADOS-backed clustered grace database beyond locating it, CephFS MDS session eviction.**
- **Known not to apply: the toy lease model to any specific server.** It has one stale write and no reconnect, reclaim or grace logic. It shows an ordering requirement, not a defect in Ganesha or Samba; in both, a single server rejects stale state itself.
- **Unknown: whether Ganesha's use of `time(NULL)` for lease expiry has caused field incidents**; the sensitivity to wall-clock steps is derived from the code.
- **Not performed: CrashMonkey, MadSim or any partition, power-cut or bit-rot injection against real systems.** Every fault in this report was injected into a probe.

## Evidence

**Repositories (read on 2026-11-19 US Pacific time; fetch timestamps 2026-11-20 01:39-02:30 UTC).** Files were fetched by exact commit from `raw.githubusercontent.com` or as commit tarballs.

- `ceph/ceph` at `97fcfa4cf9275628d83119f60e6c526f4145f979` (committed 2026-11-19): `src/crush/mapper.c` lines 229-272 (`crush_ln`), 315-340, 342-366, 405-419 (`is_out`), 1724-1799; `src/crush/mapper.h` lines 62-77; `src/crush/crush.h` lines 29-30, 36, 97-100, 424-428; `src/crush/builder.c` lines 15-25, 1478-1484, 1518-1529; `src/crush/CrushCompiler.cc` lines 716-724; `src/crush/CrushWrapper.h` lines 243-246; `src/osd/ECBackendL.cc` lines 1118-1158; `src/osd/ECBackend.cc` lines 535, 559-563, 1630-1638; `src/common/options/global.yaml.in` lines 4866-4881; `src/common/options/osd.yaml.in` lines 361-383, 490-507, 519-524; `doc/rados/troubleshooting/troubleshooting-pg.rst` lines 751-768 and 907-920; `doc/rados/operations/erasure-code-lrc.rst` lines 5-15 and 92-97; `doc/rados/configuration/bluestore-config-ref.rst` lines 256-276.
- `klauspost/reedsolomon` at `25e5c5227103dc948f3e1888a8c9d62be1bafd1e` (committed 2026-11-03): `README.md` lines 4, 84-90, 164-165; `reedsolomon.go` lines 259-281 and 665-697; `matrix.go` lines 270-281; `galois.go` line 26; `reedsolomon_test.go` lines 1121-1153.
- `minio/minio` at `7aac2a2c5b7c882e68c1ce017d8256be2feea27f` (committed 2026-02-12): `README.md` lines 1-2; `cmd/bitrot.go` lines 39-43; `cmd/bitrot-streaming.go` lines 161-199; `cmd/erasure-decode.go` lines 192-211; `cmd/erasure-coding.go` lines 94-107; `cmd/xl-storage-format-v1.go` line 158. Absence of `internal/xl-storage/` checked in the commit tarball.
- `nfs-ganesha/nfs-ganesha` at `f7a6811d936f776261bce0fd08570e214fe0b061` (commit message "V15.12", 2026-11-12): `src/include/gsh_config.h` lines 626 and 631; `src/support/nfs_read_conf.c` lines 962-964 and 994; `src/config_samples/config.txt` lines 304-306; `src/SAL/nfs4_lease.c` lines 58-77; `src/SAL/nfs4_recovery.c` line 675; `src/FSAL_UP/fsal_up_top.c` lines 1044-1072; `src/SAL/state_deleg.c` line 420; `src/FSAL/FSAL_CEPH/main.c` lines 706-724; `src/include/connection_manager.h` lines 62-76.
- `samba-team/samba` at `380971e84f8136e46448f880a421b4b57a15619c` (committed 2026-11-19): `source3/include/local.h` lines 103-106; `source3/smbd/smb2_oplock.c` lines 303-367 and 414; `source3/smbd/smb2_break.c` lines 465-481; `source3/smbd/smb2_create.c` lines 1492-1500; `source3/locking/leases_db.c` line 204.

**Specification read first-hand.** RFC 8881, "Network File System (NFS) Version 4 Minor Version 1 Protocol", August 2020 (obsoletes RFC 5661), `https://www.rfc-editor.org/rfc/rfc8881.txt`, sections 8.4.3, 10.4.5, 10.4.6, 12.7.2, 12.7.3 and 13.11.

**Second-hand sources (web search summaries, 2026-11-20 UTC; not verified against the primary documents).** Weil et al., SC 2006, DOI 10.1145/1188455.1188582; Huang et al., USENIX ATC 2012; Bairavasundaram et al., FAST 2008; MS-SMB2 lease-break timer behaviour.

**Environment.** Linux x86-64, AMD EPYC 7B12, gcc 15.2.0, CPython 3.13.15.

**CRUSH probe (executes unmodified upstream C).** Place the ten upstream files `mapper.c mapper.h hash.c hash.h builder.c builder.h crush.c crush.h crush_compat.h crush_ln_table.h` from `src/crush/` at the pinned commit in `up/crush/`, the upstream `src/include/int_types.h` in `up/include/`, and an empty `shim/acconfig.h`. Then `gcc -O2 -w -I up -I shim -o probe probe.c up/crush/hash.c up/crush/builder.c up/crush/crush.c -lm && ./probe` (28.9 s).

```c
/* CRUSH probe: compiles UNMODIFIED ceph src/crush/{mapper,hash,builder,crush}.c.
 * mapper.c is textually included so its static functions are callable. */
#include "crush/mapper.c"
#include "crush/builder.h"
#include <math.h>
#define W(x) ((int)((x) * 0x10000))
static void *ws(struct crush_map *m, int n){ void *c = malloc(crush_work_size(m, n)); crush_init_workspace(m, c); return c; }

static void exp_ln(void){
  static __u64 v[65536]; int inv = 0, eq = 0; __u64 maxdrop = 0; double maxerr = 0;
  for (unsigned u = 0; u <= 0xffff; u++){ v[u] = crush_ln(u); double e = fabs((double)v[u] / 17592186044416.0 - log2(u + 1.0)); if (e > maxerr) maxerr = e;
    if (u && v[u] < v[u-1]){ inv++; if (v[u-1] - v[u] > maxdrop) maxdrop = v[u-1] - v[u]; } if (u && v[u] == v[u-1]) eq++; }
  printf("A1 crush_ln: ln(0)=0x%llx ln(0xffff)=0x%llx (2^48=0x1000000000000) adjacent_decreases=%d adjacent_equal=%d max_decrease=0x%llx max|v/2^44-log2(u+1)|=%.3e\n",
         (unsigned long long)v[0], (unsigned long long)v[0xffff], inv, eq, (unsigned long long)maxdrop, maxerr);
}
static struct crush_bucket *flat(struct crush_map *m, int n, int *wts, int *id){
  int items[64]; for (int i = 0; i < n; i++) items[i] = i;
  struct crush_bucket *b = crush_make_bucket(m, CRUSH_BUCKET_STRAW2, CRUSH_HASH_RJENKINS1, 1, n, items, wts);
  if (!b) return NULL; crush_add_bucket(m, 0, b, id); return b;
}
static void exp_straw2(void){
  enum { N = 1000000 };
  int w1[4] = { W(1), W(2), W(3), W(4) }, w2[4] = { W(1), W(2), W(3), W(5) }, id;
  struct crush_map *m = crush_create(); struct crush_bucket *b = flat(m, 4, w1, &id);
  long cnt[4] = {0}, moved = 0, moved_to_other = 0; static int first[N];
  for (int x = 0; x < N; x++){ first[x] = bucket_straw2_choose((struct crush_bucket_straw2 *)b, x, 0, NULL, 0); cnt[first[x]]++; }
  printf("A2 straw2 weights 1:2:3:4 over %d x: ", N); for (int i = 0; i < 4; i++) printf("%.5f ", (double)cnt[i] / N); printf("(ideal .1 .2 .3 .4)\n");
  ((struct crush_bucket_straw2 *)b)->item_weights[3] = W(5);
  for (int x = 0; x < N; x++){ int n = bucket_straw2_choose((struct crush_bucket_straw2 *)b, x, 0, NULL, 0); if (n != first[x]){ moved++; if (n != 3) moved_to_other++; } }
  printf("A3 reweight item3 4->5: moved=%.5f (ideal 5/11-4/10=%.5f) moved_to_unchanged_items=%ld\n", (double)moved / N, 5.0/11 - 0.4, moved_to_other);
  (void)w2;
  /* A4: ties between two equal-weight items (strict '>' keeps the lower index) */
  for (int sh = 16; sh <= 30; sh += 7){ long ties = 0, lo = 0; int w = 1 << sh;
    for (int x = 0; x < N; x++){ __s64 a = generate_exponential_distribution(0, x, 0, 0, w), c = generate_exponential_distribution(0, x, 1, 0, w); if (a == c) ties++; if (a >= c) lo++; }
    printf("A4 two equal items weight=2^%d (%.0f units): draw ties=%ld/%d (%.2e) index0 share=%.5f\n", sh, w / 65536.0, ties, N, (double)ties / N, (double)lo / N); }
  /* A5: all-zero weights, and weight >= 2^31 seen through the 'int weight' parameter */
  int z[3] = { 0, 0, 0 }, id2; struct crush_map *m2 = crush_create(); struct crush_bucket *bz = flat(m2, 3, z, &id2);
  printf("A5 all-zero-weight bucket selects item %d for x=7\n", bucket_straw2_choose((struct crush_bucket_straw2 *)bz, 7, 0, NULL, 0));
  unsigned big[2] = { 0x7fffffffu, 0x80000000u };
  for (int k = 0; k < 2; k++){ int wb[2] = { (int)big[k], (int)0x7fffffff }, id3; struct crush_map *m3 = crush_create(); struct crush_bucket *bb = flat(m3, 2, wb, &id3);
    long c0 = 0; for (int x = 0; x < N; x++) c0 += bucket_straw2_choose((struct crush_bucket_straw2 *)bb, x, 0, NULL, 0) == 0;
    printf("A5 item0 weight=0x%08x vs item1 weight=0x7fffffff: builder %s, item0 share=%.5f (bucket weight field=0x%08x)\n", big[k], bb ? "accepted" : "rejected", (double)c0 / N, bb->weight); }
}
/* root -> H hosts -> D osds each; host i weight = hw[i] spread over D osds */
static struct crush_map *tree(int H, int D, const double *hw, int *rootid){
  struct crush_map *m = crush_create(); int hid[64], hwt[64];
  for (int h = 0; h < H; h++){ int it[64], wt[64]; for (int d = 0; d < D; d++){ it[d] = h * D + d; wt[d] = W((hw ? hw[h] : 1.0 * D) / D); }
    struct crush_bucket *b = crush_make_bucket(m, CRUSH_BUCKET_STRAW2, CRUSH_HASH_RJENKINS1, 1, D, it, wt); crush_add_bucket(m, 0, b, &hid[h]); hwt[h] = b->weight; }
  struct crush_bucket *r = crush_make_bucket(m, CRUSH_BUCKET_STRAW2, CRUSH_HASH_RJENKINS1, 2, H, hid, hwt); crush_add_bucket(m, 0, r, rootid); return m;
}
static int rule(struct crush_map *m, int type, int root, int op1, int n1, int t1, int op2, int n2, int t2, int tries){
  int len = 3 + (op2 ? 1 : 0) + (tries ? 1 : 0), p = 0; struct crush_rule *r = crush_make_rule(len, type);
  if (tries) crush_rule_set_step(r, p++, CRUSH_RULE_SET_CHOOSE_TRIES, tries, 0);
  crush_rule_set_step(r, p++, CRUSH_RULE_TAKE, root, 0); crush_rule_set_step(r, p++, op1, n1, t1);
  if (op2) crush_rule_set_step(r, p++, op2, n2, t2);
  crush_rule_set_step(r, p++, CRUSH_RULE_EMIT, 0, 0); return crush_add_rule(m, r, -1);
}
static void run(const char *tag, struct crush_map *m, int rno, int size, int nosd, const __u32 *rew, int NX){
  void *c = ws(m, size); long holes = 0, bad = 0, shortres = 0; long *per = calloc(nosd, sizeof(long));
  for (int x = 0; x < NX; x++){ int res[16], n = crush_do_rule(m, rno, x, res, size, rew, nosd, c, NULL), h = 0;
    for (int i = 0; i < n; i++){ if (res[i] == CRUSH_ITEM_NONE) h++; else per[res[i]]++; }
    if (n < size) shortres++; if (h || n < size) bad++; holes += h + (size - n); }
  double mean = 0, var = 0; long mn = 1L << 60, mx = 0; int live = 0;
  for (int i = 0; i < nosd; i++) if (rew[i]){ live++; mean += per[i]; if (per[i] < mn) mn = per[i]; if (per[i] > mx) mx = per[i]; }
  mean /= live; for (int i = 0; i < nosd; i++) if (rew[i]) var += (per[i] - mean) * (per[i] - mean);
  printf("%s: x=%d size=%d incomplete_mappings=%ld (%.3e) missing_slots=%ld short_results=%ld | per-OSD mean=%.1f min=%ld max=%ld sd=%.2f (max/mean=%.3f)\n",
         tag, NX, size, bad, (double)bad / NX, holes, shortres, mean, mn, mx, sqrt(var / live), mx / mean);
  free(c); free(per);
}
int main(void){
  exp_ln(); exp_straw2();
  __u32 rew[256]; int root;
  for (int i = 0; i < 256; i++) rew[i] = 0x10000;
  /* B1/B2: EC 4+2 = 6 shards, chooseleaf indep over exactly 6 hosts x 4 osds, default vs 100 tries */
  struct crush_map *m = tree(6, 4, NULL, &root);
  int r50 = rule(m, CRUSH_RULE_TYPE_ERASURE, root, CRUSH_RULE_CHOOSELEAF_INDEP, 6, 1, 0, 0, 0, 0);
  int r100 = rule(m, CRUSH_RULE_TYPE_ERASURE, root, CRUSH_RULE_CHOOSELEAF_INDEP, 6, 1, 0, 0, 0, 100);
  int rrep = rule(m, CRUSH_RULE_TYPE_REPLICATED, root, CRUSH_RULE_CHOOSELEAF_FIRSTN, 3, 1, 0, 0, 0, 0);
  crush_finalize(m);
  run("B1 6 hosts, EC6 chooseleaf indep host, tries=50(default)", m, r50, 6, 24, rew, 1000000);
  run("B2 6 hosts, EC6 chooseleaf indep host, set_choose_tries 100", m, r100, 6, 24, rew, 1000000);
  run("B3 6 hosts, replicated 3 chooseleaf firstn host", m, rrep, 3, 24, rew, 1000000);
  /* B4: 7 hosts, one host fully out -> 6 usable hosts */
  struct crush_map *m7 = tree(7, 4, NULL, &root);
  int q = rule(m7, CRUSH_RULE_TYPE_ERASURE, root, CRUSH_RULE_CHOOSELEAF_INDEP, 6, 1, 0, 0, 0, 0); crush_finalize(m7);
  run("B4a 7 hosts all in, EC6", m7, q, 6, 28, rew, 1000000);
  for (int d = 0; d < 4; d++) rew[d] = 0;
  run("B4b 7 hosts, host0 out (reweight 0), EC6", m7, q, 6, 28, rew, 1000000);
  for (int d = 0; d < 4; d++) rew[d] = 0x10000;
  /* B5: 2 shards per host on 4 hosts x 4 osds (6 shards on 3 hosts): classic vs MSR rule, one host out */
  struct crush_map *m4 = tree(4, 4, NULL, &root); m4->msr_descents = 100; m4->msr_collision_tries = 100;
  int cl = rule(m4, CRUSH_RULE_TYPE_ERASURE, root, CRUSH_RULE_CHOOSE_INDEP, 3, 1, CRUSH_RULE_CHOOSE_INDEP, 2, 0, 0);
  int ms = rule(m4, CRUSH_RULE_TYPE_MSR_INDEP, root, CRUSH_RULE_CHOOSE_MSR, 3, 1, CRUSH_RULE_CHOOSE_MSR, 2, 0, 0);
  crush_finalize(m4);
  run("B5a classic choose indep 3 host / choose indep 2 osd, all in", m4, cl, 6, 16, rew, 200000);
  run("B5b MSR     choosemsr 3 host / choosemsr 2 osd, all in", m4, ms, 6, 16, rew, 200000);
  for (int d = 0; d < 4; d++) rew[d] = 0;
  run("B5c classic rule, host0 out", m4, cl, 6, 16, rew, 200000);
  run("B5d MSR rule, host0 out", m4, ms, 6, 16, rew, 200000);
  for (int d = 0; d < 4; d++) rew[d] = 0x10000;
  /* C1: statistical spread, 12 hosts x 12 osds, 4096 PGs x 3 replicas */
  struct crush_map *mc = tree(12, 12, NULL, &root);
  int rc = rule(mc, CRUSH_RULE_TYPE_REPLICATED, root, CRUSH_RULE_CHOOSELEAF_FIRSTN, 3, 1, 0, 0, 0, 0); crush_finalize(mc);
  run("C1 144 osds, 4096 PGs x3", mc, rc, 3, 144, rew, 4096);
  run("C1 144 osds, 65536 PGs x3", mc, rc, 3, 144, rew, 65536);
  /* C2: three failure domains with capacity 1:1:2, 3 replicas, one per domain */
  double hw[3] = { 4, 4, 8 }; struct crush_map *mi = tree(3, 4, hw, &root);
  int ri = rule(mi, CRUSH_RULE_TYPE_REPLICATED, root, CRUSH_RULE_CHOOSELEAF_FIRSTN, 3, 1, 0, 0, 0, 0); crush_finalize(mi);
  void *c = ws(mi, 3); long dom[3] = {0};
  for (int x = 0; x < 300000; x++){ int res[3], n = crush_do_rule(mi, ri, x, res, 3, rew, 12, c, NULL); for (int i = 0; i < n; i++) if (res[i] != CRUSH_ITEM_NONE) dom[res[i] / 4]++; }
  printf("C2 domains weight 4:4:8, size 3 one-per-domain: replica share %.4f %.4f %.4f (weight share .25 .25 .50) -> fill ratio vs weight %.2f %.2f %.2f\n",
         dom[0] / 900000.0, dom[1] / 900000.0, dom[2] / 900000.0, dom[0] / 900000.0 / .25, dom[1] / 900000.0 / .25, dom[2] / 900000.0 / .5);
  return 0;
}
```

Output:

```text
A1 crush_ln: ln(0)=0x0 ln(0xffff)=0xfffff0000000 (2^48=0x1000000000000) adjacent_decreases=1 adjacent_equal=10007 max_decrease=0xd61ad10 max|v/2^44-log2(u+1)|=4.369e-05
A2 straw2 weights 1:2:3:4 over 1000000 x: 0.09933 0.19970 0.30079 0.40018 (ideal .1 .2 .3 .4)
A3 reweight item3 4->5: moved=0.05455 (ideal 5/11-4/10=0.05455) moved_to_unchanged_items=0
A4 two equal items weight=2^16 (1 units): draw ties=17/1000000 (1.70e-05) index0 share=0.50012
A4 two equal items weight=2^23 (128 units): draw ties=17/1000000 (1.70e-05) index0 share=0.50012
A4 two equal items weight=2^30 (16384 units): draw ties=29/1000000 (2.90e-05) index0 share=0.50013
A5 all-zero-weight bucket selects item 0 for x=7
A5 item0 weight=0x7fffffff vs item1 weight=0x7fffffff: builder accepted, item0 share=0.50014 (bucket weight field=0xfffffffe)
A5 item0 weight=0x80000000 vs item1 weight=0x7fffffff: builder accepted, item0 share=1.00000 (bucket weight field=0xffffffff)
B1 6 hosts, EC6 chooseleaf indep host, tries=50(default): x=1000000 size=6 incomplete_mappings=151 (1.510e-04) missing_slots=151 short_results=0 | per-OSD mean=249993.7 min=249291 max=250822 sd=354.22 (max/mean=1.003)
B2 6 hosts, EC6 chooseleaf indep host, set_choose_tries 100: x=1000000 size=6 incomplete_mappings=0 (0.000e+00) missing_slots=0 short_results=0 | per-OSD mean=250000.0 min=249300 max=250823 sd=353.10 (max/mean=1.003)
B3 6 hosts, replicated 3 chooseleaf firstn host: x=1000000 size=3 incomplete_mappings=0 (0.000e+00) missing_slots=0 short_results=0 | per-OSD mean=125000.0 min=124525 max=125497 sd=257.05 (max/mean=1.004)
B4a 7 hosts all in, EC6: x=1000000 size=6 incomplete_mappings=0 (0.000e+00) missing_slots=0 short_results=0 | per-OSD mean=214285.7 min=213648 max=214948 sd=347.52 (max/mean=1.003)
B4b 7 hosts, host0 out (reweight 0), EC6: x=1000000 size=6 incomplete_mappings=566 (5.660e-04) missing_slots=566 short_results=0 | per-OSD mean=249976.4 min=249095 max=250741 sd=427.13 (max/mean=1.003)
B5a classic choose indep 3 host / choose indep 2 osd, all in: x=200000 size=6 incomplete_mappings=0 (0.000e+00) missing_slots=0 short_results=0 | per-OSD mean=75000.0 min=74787 max=75467 sd=159.04 (max/mean=1.006)
B5b MSR     choosemsr 3 host / choosemsr 2 osd, all in: x=200000 size=6 incomplete_mappings=0 (0.000e+00) missing_slots=0 short_results=0 | per-OSD mean=75000.0 min=74648 max=75523 sd=235.64 (max/mean=1.007)
B5c classic rule, host0 out: x=200000 size=6 incomplete_mappings=150063 (7.503e-01) missing_slots=300126 short_results=0 | per-OSD mean=74989.5 min=74787 max=75467 sd=179.69 (max/mean=1.006)
B5d MSR rule, host0 out: x=200000 size=6 incomplete_mappings=0 (0.000e+00) missing_slots=0 short_results=0 | per-OSD mean=100000.0 min=99791 max=100234 sd=121.93 (max/mean=1.002)
C1 144 osds, 4096 PGs x3: x=4096 size=3 incomplete_mappings=0 (0.000e+00) missing_slots=0 short_results=0 | per-OSD mean=85.3 min=63 max=111 sd=8.77 (max/mean=1.301)
C1 144 osds, 65536 PGs x3: x=65536 size=3 incomplete_mappings=0 (0.000e+00) missing_slots=0 short_results=0 | per-OSD mean=1365.3 min=1256 max=1455 sd=40.27 (max/mean=1.066)
C2 domains weight 4:4:8, size 3 one-per-domain: replica share 0.3333 0.3333 0.3333 (weight share .25 .25 .50) -> fill ratio vs weight 1.33 1.33 0.67
```

Throughput figure (same build flags; a 22-line loop calling `crush_do_rule` 2 x 10^6 times on a 12 x 12 map with a replicated `chooseleaf firstn 3 type host` rule): `crush_do_rule: 2000000 mappings in 6.873 s = 290974 mappings/s (3437 ns each), workspace=1004 bytes, checksum=143049998`.

**Reed-Solomon probe (independent re-implementation; `python3 rs_probe.py`, 0.1 s).**

```python
#!/usr/bin/env python3
"""Independent GF(2^8) Reed-Solomon re-implementation of the default klauspost/reedsolomon
construction (field polynomial 0x11d, Vandermonde rows r^c made systematic by multiplying with
the inverse of the top k x k square). NOT the upstream Go/assembly code; validated against the
upstream golden vector in reedsolomon_test.go TestOneEncode."""
import itertools, random, zlib
EXP = [0] * 512; LOG = [0] * 256; x = 1
for i in range(255):
    EXP[i] = x; LOG[x] = i; x <<= 1
    if x & 0x100: x ^= 0x11d
for i in range(255, 512): EXP[i] = EXP[i - 255]
mul = lambda a, b: 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]
inv = lambda a: EXP[255 - LOG[a]]
def gexp(a, n): return 1 if n == 0 else (0 if a == 0 else EXP[(LOG[a] * n) % 255])
def matmul(A, B): return [[__import__('functools').reduce(lambda s, t: s ^ t, (mul(A[i][k], B[k][j]) for k in range(len(B))), 0) for j in range(len(B[0]))] for i in range(len(A))]
def matinv(M):
    n = len(M); A = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c]); A[c], A[p] = A[p], A[c]
        s = inv(A[c][c]); A[c] = [mul(v, s) for v in A[c]]
        for r in range(n):
            if r != c and A[r][c]:
                f = A[r][c]; A[r] = [v ^ mul(f, w) for v, w in zip(A[r], A[c])]
    return [row[n:] for row in A]
def build(k, n):
    vm = [[gexp(r, c) for c in range(k)] for r in range(n)]
    return matmul(vm, matinv(vm[:k]))
def encode(M, k, data):
    L = len(data[0]); return [bytes(__import__('functools').reduce(lambda s, t: s ^ t, (mul(M[r][j], data[j][b]) for j in range(k)), 0) for b in range(L)) for r in range(k, len(M))]
def reconstruct(M, k, shards):
    """Erasure-only decode, as in Reconstruct(): uses the FIRST k present shards, never checks them."""
    present = [i for i, s in enumerate(shards) if s is not None][:k]
    D = matinv([M[i] for i in present]); L = len(shards[present[0]])
    data = [bytes(__import__('functools').reduce(lambda s, t: s ^ t, (mul(D[j][c], shards[present[c]][b]) for c in range(k)), 0) for b in range(L)) for j in range(k)]
    full = data + encode(M, k, data)
    return [s if s is not None else full[i] for i, s in enumerate(shards)], present
def verify(M, k, shards): return encode(M, k, shards[:k]) == shards[k:]

# E1: upstream golden vector (reedsolomon_test.go TestOneEncode, 5 data + 5 parity)
M = build(5, 10); par = encode(M, 5, [bytes(v) for v in ([0, 1], [4, 5], [2, 3], [6, 7], [8, 9])])
print("E1 golden TestOneEncode parity:", [list(p) for p in par], "match =", [list(p) for p in par] == [[12, 13], [10, 11], [14, 15], [90, 91], [94, 95]])

k, m, L = 4, 2, 64; M = build(k, k + m); rnd = random.Random(20261119)
data = [bytes(rnd.randrange(256) for _ in range(L)) for _ in range(k)]; good = data + encode(M, k, data)
crc = [zlib.crc32(s) for s in good]
# E2: one silently corrupted survivor (1 flipped bit in shard 1) + one erased shard (shard 0)
bad = [bytearray(s) for s in good]; bad[1][17] ^= 0x04; bad = [bytes(s) for s in bad]
st = bad[:]; st[0] = None; rec, used = reconstruct(M, k, st)
diff = lambda a, b: sum(x != y for x, y in zip(a, b))
print("E2 unverified reconstruct of shard0 using shards", used, ": wrong bytes in rebuilt shard0 =", diff(rec[0], good[0]), "| Verify(stripe) =", verify(M, k, rec))
healed = rec[:k] + encode(M, k, rec[:k])   # 'repair' that trusts data shards and regenerates all parity
print("E2 after parity regeneration from (wrong) data: Verify =", verify(M, k, healed), "| shards differing from original =", [i for i in range(k + m) if healed[i] != good[i]])
# E3: same fault, but every shard is checked against its own checksum first -> corruption becomes an erasure
st = [s if zlib.crc32(s) == crc[i] else None for i, s in enumerate(bad)]; st[0] = None
rec, used = reconstruct(M, k, st)
print("E3 checksum-gated reconstruct: erasures =", [i for i, s in enumerate(st) if s is None], "used", used, "| all shards correct =", rec == good)
# E4: exhaustive (erased e, corrupted c != e) over the 6 shards, one flipped bit, unverified decode
wrong = total = detect = 0
for e, c in itertools.permutations(range(k + m), 2):
    b = [bytearray(s) for s in good]; b[c][5] ^= 0x80; st = [bytes(s) for s in b]; st[e] = None
    rec, used = reconstruct(M, k, st); total += 1
    if rec[e] != good[e]: wrong += 1
    if not verify(M, k, rec): detect += 1
print(f"E4 4+2, all (erased, corrupted) pairs: rebuilt shard silently wrong in {wrong}/{total}; post-rebuild Verify flags inconsistency in {detect}/{total}")
# E5: can parity alone LOCATE the corrupt shard? candidate s is 'consistent' if erasing s (plus known erasures) yields a codeword agreeing with all other present shards
def candidates(shards, erased):
    out = []
    for s in range(k + m):
        if s in erased: continue
        st = [None if (i == s or i in erased) else v for i, v in enumerate(shards)]
        if sum(v is not None for v in st) < k: continue
        rec, _ = reconstruct(M, k, st)
        full = rec[:k] + encode(M, k, rec[:k])
        if all(full[i] == shards[i] for i in range(k + m) if i != s and i not in erased): out.append(s)
    return out
b = [bytearray(s) for s in good]; b[3][9] ^= 1; b = [bytes(s) for s in b]
print("E5 m=2, 0 erasures, shard3 corrupt -> consistent culprit candidates:", candidates(b, set()), "(unique => locatable, 2t+e=2<=m)")
print("E5 m=2, shard0 erased, shard3 corrupt -> consistent culprit candidates:", candidates(b, {0}), "(ambiguous => not locatable, 2t+e=3>m)")
# E6: erasures == m (no spare shard): is a corrupted survivor even detectable by parity?
wrong = total = detect = 0
for e in itertools.combinations(range(k + m), 2):
    for c in set(range(k + m)) - set(e):
        b = [bytearray(s) for s in good]; b[c][5] ^= 0x80; st = [bytes(s) for s in b]
        for i in e: st[i] = None
        rec, used = reconstruct(M, k, st); total += 1
        wrong += any(rec[i] != good[i] for i in e); detect += not verify(M, k, rec)
print(f"E6 4+2, two erasures + one corrupted survivor: rebuilt shards wrong in {wrong}/{total}; Verify flags inconsistency in {detect}/{total}")
```

Output:

```text
E1 golden TestOneEncode parity: [[12, 13], [10, 11], [14, 15], [90, 91], [94, 95]] match = True
E2 unverified reconstruct of shard0 using shards [1, 2, 3, 4] : wrong bytes in rebuilt shard0 = 1 | Verify(stripe) = False
E2 after parity regeneration from (wrong) data: Verify = True | shards differing from original = [0, 1, 5]
E3 checksum-gated reconstruct: erasures = [0, 1] used [2, 3, 4, 5] | all shards correct = True
E4 4+2, all (erased, corrupted) pairs: rebuilt shard silently wrong in 24/30; post-rebuild Verify flags inconsistency in 30/30
E5 m=2, 0 erasures, shard3 corrupt -> consistent culprit candidates: [3] (unique => locatable, 2t+e=2<=m)
E5 m=2, shard0 erased, shard3 corrupt -> consistent culprit candidates: [1, 2, 3, 4, 5] (ambiguous => not locatable, 2t+e=3>m)
E6 4+2, two erasures + one corrupted survivor: rebuilt shards wrong in 60/60; Verify flags inconsistency in 0/60
```

**Lease probe (toy model; `python3 lease_probe.py`).**

```python
#!/usr/bin/env python3
"""Toy model (not NFS-Ganesha, Samba or Ceph code): exhaustive interleavings of a revoked
write-lease holder A whose write is still in flight, a lease manager G, a new holder B and a
storage target S. Checks (I1) B's acknowledged write is the final value and (I2) while B holds
the exclusive lease, S changes only through B."""
import itertools
def run(order, variant):
    val, s_epoch, b_cache, viol = "v0", 1, None, set()
    b_holds = False; b_wrote = False
    for ev in order:
        if ev == "revoke": pass                       # G gives up on A (recall/break timed out)
        elif ev == "fence": s_epoch = 2               # G raises the minimum epoch accepted by S
        elif ev == "grantB": b_holds = True
        elif ev == "B.read": b_cache = val
        elif ev == "B.write":
            if variant == "fence-on-first-write": s_epoch = 2
            val, b_wrote, b_cache = "wB", True, "wB"
        elif ev == "A.write":                         # stale holder's delayed write, tagged epoch 1
            accepted = (variant == "none") or s_epoch <= 1
            if accepted:
                if b_holds and b_cache is not None and b_cache != "wA": viol.add("I2 holder cache stale")
                if b_wrote: viol.add("I1 acked write overwritten")
                val = "wA"
    return viol
base = ["revoke", "grantB", "B.read", "B.write"]
for variant in ("none", "fence-on-first-write", "fence-before-grant"):
    evs = base + (["fence"] if variant == "fence-before-grant" else []) + ["A.write"]
    n = bad1 = bad2 = 0
    for p in itertools.permutations(evs):
        pos = {e: i for i, e in enumerate(p)}
        if not (pos["revoke"] < pos["grantB"] < pos["B.read"] < pos["B.write"]): continue
        if variant == "fence-before-grant" and not (pos["revoke"] < pos["fence"] < pos["grantB"]): continue
        v = run(p, variant); n += 1; bad1 += any(x.startswith("I1") for x in v); bad2 += any(x.startswith("I2") for x in v)
    print(f"F1 storage fencing={variant:22s}: schedules={n} I1(lost acked write)={bad1} I2(stale exclusive cache)={bad2}")

# F2: time-based safety WITHOUT storage fencing. Integer ticks. A renews at real time 0 and may keep
# sending until its local clock reads L - g_c; clocks drift by at most rho (parts per 100); a message
# takes at most D ticks. G grants to B at real time L + g_s after the last renewal it saw (worst case 0).
def unsafe(L, rho, D, g_c, g_s):
    last_send_real = (L - g_c) * 100 / (100 - rho)     # slow client clock stretches real time
    grant_real = (L + g_s) * 100 / (100 + rho)         # fast server clock shortens real time
    return last_send_real + D >= grant_real
L, rho, D = 60000, 1, 500                              # 60 s lease in ms, 1 % drift, 0.5 s max delay
for g_c, g_s in ((0, 0), (0, 500), (600, 0), (1200, 600), (0, 1750), (1700, 0), (900, 900)):
    print(f"F2 L={L}ms rho={rho}% D={D}ms client_guard={g_c} server_guard={g_s}: stale write can land after grant = {unsafe(L, rho, D, g_c, g_s)}")
need = next(g for g in range(0, 5000) if not unsafe(L, rho, D, 0, g))
print("F2 minimal server-only guard (ms) for these bounds:", need, "| closed form L*2rho/(1-rho)+D*(1+rho) =", round(L * 2 * 0.01 / 0.99 + D * 1.01, 1))
```

Output:

```text
F1 storage fencing=none                  : schedules=5 I1(lost acked write)=1 I2(stale exclusive cache)=2
F1 storage fencing=fence-on-first-write  : schedules=5 I1(lost acked write)=0 I2(stale exclusive cache)=1
F1 storage fencing=fence-before-grant    : schedules=6 I1(lost acked write)=0 I2(stale exclusive cache)=0
F2 L=60000ms rho=1% D=500ms client_guard=0 server_guard=0: stale write can land after grant = True
F2 L=60000ms rho=1% D=500ms client_guard=0 server_guard=500: stale write can land after grant = True
F2 L=60000ms rho=1% D=500ms client_guard=600 server_guard=0: stale write can land after grant = True
F2 L=60000ms rho=1% D=500ms client_guard=1200 server_guard=600: stale write can land after grant = False
F2 L=60000ms rho=1% D=500ms client_guard=0 server_guard=1750: stale write can land after grant = False
F2 L=60000ms rho=1% D=500ms client_guard=1700 server_guard=0: stale write can land after grant = False
F2 L=60000ms rho=1% D=500ms client_guard=900 server_guard=900: stale write can land after grant = False
F2 minimal server-only guard (ms) for these bounds: 1718 | closed form L*2rho/(1-rho)+D*(1+rho) = 1717.1
```

## Revalidation

- **straw2 properties.** Rebuild the CRUSH probe against a newer `src/crush/`; rows A2-A4 should stay within sampling noise. Row A5 changes if `generate_exponential_distribution` takes an unsigned or 64-bit weight, or if the builder or compiler starts rejecting weights at or above `0x80000000`; `grep -n "int weight" src/crush/mapper.c` and the two `CRUSH_MAX_*_WEIGHT` macros decide it without running anything.
- **Retry exhaustion.** Rows B1/B2 depend on `choose_total_tries` in `set_optimal_crush_map()`; a changed default changes the 1.5 x 10^-4 figure roughly as (5/6)^tries. Rows B5c/B5d depend on MSR rule support (`CRUSH_RULE_TYPE_MSR_INDEP`) and on the two MSR tunables being non-zero.
- **Decoder contract.** Check that `reedsolomon.go` still selects `validIndices[:r.dataShards]` and that the README sentence about invalid parts is still present; rerun the Reed-Solomon probe (the golden-vector line must print `match = True` before any other line is trusted). With a Go toolchain, the same seven experiments can be run against the real library through `Encode`, `Reconstruct` and `Verify`.
- **Where the check sits.** MinIO: confirm `streamingBitrotReader.ReadAt` still compares before returning data. Ceph: `grep -n "bluestore_csum_type" -A 12 src/common/options/global.yaml.in` for the default, and `grep -n "Bad hash\|allows_ecoverwrites" src/osd/ECBackend*.cc` for the erasure-code-level check.
- **Lease behaviour.** Ganesha: `grep -n "LEASE_LIFETIME_DEFAULT\|GRACE_PERIOD_DEFAULT" src/include/gsh_config.h`, read `eval_deleg_revoke()`, and check whether `_valid_lease()` still calls `time(NULL)`. Samba: `grep -n "OPLOCK_BREAK_TIMEOUT" source3/include/local.h` and read `lease_timeout_handler()`.
- **Standard.** A successor to RFC 8881 should be checked at the sections cited; the SHOULD in 10.4.5 and the MUSTs in 12.7.3 and 13.11 carry the argument of section 3.
- **What these checks do not cover.** A passing probe confirms library arithmetic and toy-model orderings only. Confirming the storage-level claims on real systems requires the fault-injection experiments listed under Boundaries.
