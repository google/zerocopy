# Append-Only Merkle Transparency Logs, Quorum Witness Cosigning, Split-View Gossip, and VRF Auditable Key Directories

## Summary

Cryptographic transparency logs and verifiable key directories establish *publicly auditable commitment histories*—upgrading "principal $K$ signed statement $s$" to "everyone observing a consistent log head sees the identical append-only history"—across four distinct architectural invariants:

1. **Domain-Separated Merkle Ladders & Bit-Exact Proof Decomposition (`RFC 9162`, `transparency-dev/merkle`, `Trillian`, `Rekor`):**
   - `RFC 6962` / `RFC 9162` tree hashing prepends single-byte domain tags (`0x00 || leaf` for leaves, `0x01 || left || right` for interior nodes, and `SHA256("")` for empty roots; `transparency-dev/merkle/rfc6962/rfc6962.go:25-94`) to defeat tree-depth second-preimage collisions in which an adversary supplies a 64-byte leaf `H_0 || H_1` masquerading as an interior parent (`Probe 2A`).
   - `compact.Range` (`compact/range.go:65-264`) represents any `[0, N)` prefix using only $\operatorname{popcount}(N)$ perfect-subtree roots, while `proof/verify.go:46-358` verifies logarithmic inclusion and consistency proofs via exact bit-XOR divergence `inner = Len64(index ^ (size - 1))` and `shift = TrailingZeros64(size1)`, checking exact proof-slice lengths and reconstructing *both* historical `root1` and extended `root2` simultaneously.
   - `google/trillian` (`log/sequencer.go:106-199`, `server/proof_fetcher.go:38-57`) persists only immutable perfect-subtree nodes and recomputes ephemeral right-border hashes via `pn.Rehash` on read. In `sigstore/rekor` (`pkg/verify/verify.go:171-241`, `pkg/sharding/ranges.go:182-193`), a critical seam separates `SignedEntryTimestamp` (`SET`, signing JCS-canonicalized `{body, integratedTime, logIndex, logID}` where `logIndex` is the *virtual* cross-shard index) from `InclusionProof.LogIndex` (which is the *shard-local* leaf index inside one Trillian `TreeID`).
2. **Split-View Equivocation, Quorum Witnessing (`C2SP tlog-witness`), and Gossip Trade-Offs:**
   - A standalone inclusion proof verifies only that a leaf lies under *some* signed root hash (`Probe 2B`). A compromised log operator key can serve forked yet individually self-consistent Merkle histories (`4 -> 8` vs. `4 -> 5`) to victims and public monitors alike.
   - `transparency-dev/witness` (`witness/witness.go:180-340`) prevents equivocation and the concurrent rollback race (`C2SP/tlog-witness.md:191-201`) by validating the consistency proof inside an atomic storage transaction enforcing `oldSize == prevSize` (`409 Conflict`). When $f$ out of $W$ witnesses can be Byzantine, split-view resistance holds **if and only if** client quorum $q_c$ and monitor quorum $q_m$ satisfy $q_c + q_m > W + f$ (`Probe 2B`: `70` compromised pairs at $(q_c=4, q_m=4, W=7, f=2)$ vs. `0` at $(5, 5)$ or $(4, 6)$).
   - `C2SP/tlog-checkpoint.md` and `tlog-cosignature.md` introduce a sharp signature-algorithm divergence: `Ed25519` (`0x04`) cosignatures sign checkpoint extension lines and omit `cosigner_name` (requiring distinct keys per cosigner name), whereas `ML-DSA-44` (`0x06`, FIPS 204) `CosignedSubtree` commits to `cosigner_name`, supports subtree cosignatures, and **ignores extension lines**. Compared with `Chuat et al.` epidemic client-to-auditor gossip, pre-fetched witness cosignatures let clients verify global consistency *offline* without leaking lookup identities (`TLS` hostnames or package digests).
3. **VRF-Indexed Sparse Merkle Directories (`CONIKS` vs. `facebook/akd`):**
   - `CONIKS` (`coniks-sys/coniks-go`, `google/trillian/merkle/coniks`) hides user identifiers via a deterministic VRF (`VrfProof` -> 256-bit index) and hides key values via salted commitments, binding `(treeID, index, depth)` inside `HashEmpty`/`HashLeaf` (`coniks-go/merkletree/proof.go:39-58`; note the serialization-order doc bug at `trillian/merkle/coniks/coniks.go:73-83`). Because `CONIKS` overwrites leaves in place, public auditors face $O(U)$ epoch replay costs.
   - `facebook/akd` (`43a60ccf...`, implementing `SEEMless` and `Parakeet`) replaces in-place updates with an append-only 256-bit VRF trie (`Fresh(v)` + `Stale(v - 1)` leaves in `akd/src/directory.rs:150-200`), reducing public auditing to $O(\Delta \log N)$ without user data exposure (`append_only_zks.rs`) and key-history proofs to logarithmic marker skiplists (`akd_core/src/utils.rs:15, 98-168`).
   - **Verified Implementation Gap in `facebook/akd` (`Probe 2C`):** `akd_core/src/verify/lookup.rs:46` checks only a single power-of-two marker `1 << floor(log2(v))` rather than all `past_marker_versions(v, v, current_epoch)` assumed by `get_marker_versions` (`utils.rs:98-168`). At `(end_version=5, epoch=33)`, stealth insertions `v* in {7, 32, 33}` bypass public append-only audit, victim `lookup_verify`, and owner `key_history_verify` simultaneously unless `lookup_verify` checks all past markers (**`0` evading versions** when enforced).

---

## Applicability

This report relates, compares, and cross-checks 15 primary specifications, implementations, and peer-reviewed systems across the transparency-log and key-transparency stack:

1. **Append-Only Merkle Log Standards & Verifiers:**
   - `RFC 6962` (`DOI: 10.17487/RFC6962`) and `RFC 9162` (`DOI: 10.17487/RFC9162`, Certificate Transparency 2.0). Normative definitions of `0x00`/`0x01` Merkle tree hashing, inclusion paths, and consistency subproofs (`Section 2.1`).
   - `transparency-dev/merkle` (`75a6539d7b48af0d529236f24487d2814fd1dca7`). Production Go implementation of `rfc6962`, `compact.Range`, and `proof` inclusion/consistency/subtree verification.
   - `google/trillian` (`07016bd85eba94134d3e423a1b16f13e19ef366e`) and `sigstore/rekor` (`0baa39712ffa627b70756ea555193ec84bea4507`, Newman, Meyers, Torres-Arias, CCS 2022, `DOI: 10.1145/3548606.3560596`). Findings cover Trillian-backed dynamic logs (`Rekor v1`), log sharding (`pkg/sharding/ranges.go`), and JCS-canonicalized `SET` vs. `Checkpoint` verification (`pkg/verify/verify.go`), contrasted normatively with static tile layouts (`C2SP/tlog-tiles.md`).
2. **Split-View Detection via Witnesses and Client Gossip (comparison & boundary characterization):**
   - `C2SP/C2SP` (`d35150e795e178b7ad26cdff0ec1877bcc9e9723`, `tlog-checkpoint.md`, `tlog-cosignature.md`, `tlog-witness.md`, `tlog-tiles.md`). Note that the inspected C2SP repository files carry an explicit editor's-copy banner (`C2SP.org/tlog-*@v1.1.0` targets) and apply to the pinned revision.
   - `transparency-dev/witness` (`bd0f4ab93e8ee9cf3b382d7c903e864c3701a5c5`), `Syta et al.` (`CoSi`, IEEE S&P 2016, `DOI: 10.1109/SP.2016.38`), and `Chuat et al.` (*Efficient Gossip Protocols*, IEEE CNS 2015, `DOI: 10.1109/CNS.2015.7346853`, `arXiv:1511.01514`).
3. **Verifiable Key Directories (evolution comparison):**
   - `coniks-sys/coniks-go` (`11acf4819b71d23bb135a597950e59d74fe75b6c`), `google/trillian/merkle/coniks` (`07016bd8...`), and Melara et al. (USENIX Security 2015).
   - `facebook/akd` (`43a60ccf7dfdd8f4b628186410e871192adaf65b`), implementing `SEEMless` (Chase et al., CCS 2019, `DOI: 10.1145/3319535.3363202`) and `Parakeet` (Malvai et al., NDSS 2023, `DOI: 10.14722/ndss.2023.24545`).
4. **Executable Micro-Probes (`Basis: execution`):** Three standalone Python 3.13.15 probes (`2A`–`2C`) verify exact RFC 9162 test vectors and exhaustive `N=1..33` compact-range/inclusion/consistency invariants, combinatorial Byzantine witness quorum overlaps at $(W=7, f=2)$, and exact ports of `akd_core`'s 8 marker-skiplist test vectors plus stealth-version gap enumeration.

---

## Findings

### 1. `RFC 9162` Append-Only Merkle Ladders, Compact Ranges, and Bit-Exact Verification

`Basis: normative + source + execution`

#### 1.1 Domain-Separated Tree Hashing & Second-Preimage Defense

For an ordered sequence of $n$ byte-string entries $D_n = [d_0, \dots, d_{n-1}]$ under cryptographic hash $H$ (default SHA-256), `RFC 9162` (Section 2.1, preserving `RFC 6962` hashing) defines the Merkle Tree Hash $\operatorname{MTH}(D_n)$ recursively:

- **Empty Tree ($n = 0$):** $\operatorname{MTH}(\emptyset) = H(\varepsilon)$ (`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` for SHA-256).
- **Leaf ($n = 1$):** $\operatorname{MTH}([d_0]) = H(\texttt{0x00} \parallel d_0)$. Note that an empty-byte leaf (`d_0 = ""`) hashes `0x00` (`6e340b9c...`), distinct from `EmptyRoot` (`e3b0c442...`), checked explicitly in `transparency-dev/merkle/rfc6962/rfc6962_test.go:36-46`.
- **Interior Split ($n > 1$):** Let $k = 2^{\lfloor \log_2(n - 1) \rfloor}$ be the largest power of two strictly less than $n$. Then:
  $$\operatorname{MTH}(D_n) = H(\texttt{0x01} \parallel \operatorname{MTH}(D_n[0..k]) \parallel \operatorname{MTH}(D_n[k..n]))$$

**Tree-Depth Confusion Attack Without Domain Tags (`Probe 2A`):** If a log omits the `0x00`/`0x01` prefix bytes (`Hash(d)` vs. `Hash(L || R)`), a 2-leaf tree `[certA, certB]` has root $H(H(\text{certA}) \parallel H(\text{certB}))$, which is **bit-identical** to a 1-leaf tree whose single 64-byte leaf is `H(certA) || H(certB)` (**Probe 2A** verifies exact digest collision under raw SHA-256). Adding `0x00` vs. `0x01` makes interior node preimages disjoint from leaf preimages at every depth—and `rfc6962/rfc6962.go:87-94` keeps the 65-byte interior preimage `[1 + 2*32]byte` stack-allocated via concrete `sha256.Sum256(b[:])` to eliminate heap escapes in Go's compiler.

#### 1.2 Compact Ranges & Iterative Bit-Level Inclusion / Consistency Proofs

Storing or hashing all $O(N)$ leaves on each append is avoided by maintaining a **Compact Range** `[begin, end)` (`transparency-dev/merkle/compact/range.go:65-264`):

1. **Perfect-Subtree Invariant (`compact/range.go:40-141`):**
   - A compact range `[0, N)` stores exactly $\operatorname{popcount}(N) \le 64$ hashes corresponding to the minimal left-to-right decomposition of $N$ into perfect binary subtrees of sizes matching the `1`-bits of $N$ in MSB-to-LSB order (`RangeSize(0, N) == OnesCount64(N)`).
   - `Append(leafHash)` (`lines 90-95, 164-209`) merges right-to-left along the trailing `1`-bits of `r.end` (`low = TrailingZeros64(r.end + 1)`? Wait—for `[0, end)` + `[end, end+1)`, `getMergePath(0, end, end+1)` spans `[TrailingZeros64(end), Len64((end - 1) ^ (end + 1)) - 1)`: at step $h$ where bit `(end >> h) & 1 == 1`, pop `r.hashes` and compute `Hash(left, seed)`, leaving the new minimal set of perfect subtree roots!).
   - `GetRootHash` (`lines 119-141`) folds `r.hashes` right-to-left via `hash = Hash(r.hashes[i], hash)` for `i = ln-2` down to `0`, visiting only the *ephemeral* imperfect-subtree right-border ancestors without persisting them.
2. **Bitwise Proof Verification Without Recursion (`proof/verify.go:46-358`):**
   - **Inclusion (`VerifyInclusion` / `RootFromInclusionProof`, lines 46–94, 272–276, 318–358):**
     Given `0 <= index < size`, let `inner = Len64(index ^ (size - 1))` (height of the lowest common ancestor where paths to `index` and `size - 1` diverge) and `border = OnesCount64(index >> inner)` (number of `1`-bits above `inner`, each corresponding to a left-sibling subtree along the right border). Verification enforces **strict length equality** `len(proof) == inner + border` (line 87—rejecting padded or truncated proofs), chains `proof[:inner]` via `index`'s bit $i$ (`0 -> Hash(seed, h)`, `1 -> Hash(h, seed)`), then chains `proof[inner:]` strictly on the left (`Hash(h, seed)`), and compares equality with `root`.
   - **Consistency (`VerifyConsistency` / `rootFromSubtreeConsistencyProof`, lines 99–261):**
     For $0 < \text{size1} < \text{size2}$ (`start = 0, end = size1, size = size2`), let `forkLevel, border = decompInclProof(size1 - 1, size2)` and `shift = TrailingZeros64(size1)` (height of the rightmost perfect subtree inside `[0, size1)`). Then `inner = forkLevel - shift`.
     - If `size1` is an exact power of two (`size1 == 1 << shift`), `seed = root1` and `pStart = 0` (`len(proof) == inner + border`).
     - Otherwise, `seed = proof[0]` (the root of the rightmost perfect subtree of `[0, size1)`) and `pStart = 1` (`len(proof) == 1 + inner + border`). In this branch (`lines 248-255`), the verifier **first checks historical commitment** to `root1` via `chainInnerRight(seed, proof[1:1+inner], mask)` + `chainBorderRight(..., proof[1+inner:])` using `mask = (size1 - 1) >> shift` (consuming only bits where `(mask >> i) & 1 == 1`, i.e., left siblings inside `size1`), asserting equality with `root1`; it **then** runs full `chainInner` + `chainBorderRight` on the *same* `proof[1:]` to assert equality with `root2`.
   - **Subtree Proofs for Merkle Tree Certificates (`VerifySubtreeInclusion` / `VerifySubtreeConsistency`, lines 61–73, 113–131, 288–316):** Extends `RFC 9162` to aligned contiguous subtrees `[start, end)` where `start` is a multiple of the smallest $2^k \ge \text{end} - \text{start}$ (`isSubtreeValid`), enabling `C2SP` `sign-subtree` proofs (`c2sp.org/tlog-witness` Section `sign-subtree`).
   - **Probe 2A** verifies exact bit-identity between recursive `RFC 9162` `MTH` / `PROVE` / `CONSISTENCY` and `transparency-dev/merkle`'s iterative `CompactRange` + `VerifyInclusion` + `VerifyConsistency` across all $N \in [1, 33]$ and all $1 \le \text{size1} \le \text{size2} \le 33$, alongside all 4 canonical `rfc6962_test.go` SHA-256 hex vectors.

---

### 2. Storage Architecture & Shard-Boundary Invariants in `Trillian` and `Sigstore Rekor`

`Basis: normative + source + derived`

#### 2.1 `google/trillian` (`07016bd85eba94134d3e423a1b16f13e19ef366e`): Ephemeral-Free Storage & Read-Time Rehashing

Inspection of `google/trillian/log/sequencer.go:106-253` and `server/proof_fetcher.go:38-57` establishes how Trillian reconciles database write amplification with historical tree queries:
1. **Resuming from Storage (`initCompactRangeFromStorage`, `sequencer.go:106-138`):** On batch integration, the sequencer queries `compact.RangeNodes(0, root.TreeSize, nil)` (`<= 64` perfect-subtree roots), checks exact count equality (`len(nodes) == len(ids)`), reconstructs the compact range, and asserts `bytes.Equal(hash, root.RootHash)` before appending new leaves (`line 134`).
2. **Ephemeral Right-Border Omission (`updateCompactRange`, `sequencer.go:177-199`):** Appending leaves invokes `cr.Append(leaf.MerkleLeafHash, store)` (recording every newly finalized leaf and *complete* power-of-two internal node in `nodeMap`), then passes `nil` to `cr.GetRootHash(nil)` (`line 194`) so ephemeral right-border hashes are **never** written to DB storage.
3. **Read-Time Proof Rehashing (`fetchNodesAndBuildProof`, `proof_fetcher.go:38-57`):** Because ephemeral nodes are absent from storage (and historical tree sizes $T' < T_{\text{latest}}$ require partial-border folding), `proof.Nodes` computes the underlying perfect-subtree `NodeID`s, fetches them, verifies `node.ID == ids[i]` (`line 71`), and invokes `pn.Rehash(h, hasher)` (`line 48`) to synthesize the exact ephemeral sibling hashes for `TreeSize`.

#### 2.2 `sigstore/rekor` (`0baa39712ffa627b70756ea555193ec84bea4507`): Virtual vs. Physical Sharding & `SET` Limits

Direct inspection of `sigstore/rekor` (`pkg/verify/verify.go:38-241`, `pkg/sharding/ranges.go:40-273`) reveals two critical verification invariants and one systemic trust boundary:

1. **The Virtual vs. Physical Shard Index Seam (`sharding/ranges.go:182-193`, `verify.go:171-203`):**
   - Rekor supports sequential log sharding (`LogRanges` holds ordered `inactive` frozen shards with fixed `TreeLength` plus one `active` shard). `LogRanges.ResolveVirtualIndex(index)` subtracts `l.TreeLength` across inactive shards until `indexLeft < l.TreeLength`, mapping a monotonically increasing global virtual index `e.LogIndex` to `(shard.TreeID, shardLocalIndex)`.
   - Inside `VerifySignedEntryTimestamp` (`verify.go:190-217`), Rekor verifies the log's signature over an **RFC 8785 JCS-canonicalized** JSON tuple `{body, integratedTime, logIndex, logID}` where `logIndex` is the **virtual global index** (`*e.LogIndex`) and `logID` is `hex(SHA256(PKIX(shardPubKey)))` (`ranges.go:172-177`).
   - By contrast, inside `VerifyInclusion` (`verify.go:169-174`), Rekor computes `leafHash := rfc6962.DefaultHasher.HashLeaf(entryBytes)` and calls `proof.VerifyInclusion(..., uint64(*e.Verification.InclusionProof.LogIndex), uint64(*e.Verification.InclusionProof.TreeSize), leafHash, hashes, rootHash)`, where `InclusionProof.LogIndex` is the **shard-local physical leaf index** (`0 <= physical < shard.TreeSize`)! Clients that mistakenly pass virtual `e.LogIndex` into Merkle verification, or verify against the wrong shard's `PemPubKey`, reject valid entries on every post-shard-0 tree.
2. **Why `VerifyLogEntry` Does Not Defeat Split Views (`verify.go:38-140, 224-241`):**
   - Notice `VerifyLogEntry` (`lines 224-241`) checks three *local* predicates: `VerifyInclusion`, `VerifyCheckpointSignature`, and `VerifySignedEntryTimestamp` (`SET`, the artifact-log analogue of RFC 6962's `SCT`).
   - As `VerifyInclusion`'s own docstring warns (`lines 137-139`), checking inclusion against an entry's bundled checkpoint proves neither historical append-only growth (`VerifyCurrentCheckpoint` / `ProveConsistency` require persisting a client's prior trusted `STH`) nor global non-equivocation against other clients. Moreover, a `SET` alone is merely a signed *promise* before or at sequencing—offline verification against a stale/compromised log key accepts a forked 1-leaf or branched tree (`Probe 2B`).
   - Static-tile architectures (`C2SP/tlog-tiles.md`, adopted by newer static-asset transparency logs) replace per-query Trillian RPCs and `SET` promises with deterministic immutable HTTP tiles (`/tile/<L>/<N>[.p/<W>]`, default height `8` = `256` entries per tile) plus witnessed checkpoints, enabling CDN caching and eliminating dynamic database query amplification.

---

### 3. Split-View Equivocation, Quorum Witnessing (`C2SP`), and Client Gossip Trade-Offs

`Basis: normative + source + execution`

| Anti-Equivocation Mechanism | Threat Model Against Compromised Log Key | Client Offline / Zero-RTT Verification | Client Lookup Privacy (`TLS` / Artifact Name) | Key Architecture / Witness State | Primary Failure / Operational Trade-Off |
|---|---|---|---|---|---|
| **Unwitnessed STH + `SCT`/`SET` only** | None (single compromised log key forges split views undetected; **Probe 2B**) | Yes (if trusting log key) | High (no third-party check) | None | **Split-view vulnerable** without external monitor comparison |
| **Epidemic Client-to-Monitor Gossip** (`Chuat et al., IEEE CNS 2015`) | Strong once gossip reaches monitors (detects split views probabilistically over network rounds) | **No** (async detection *after* gossip convergence; hard vs. soft fail dilemma) | **Low by default** (forwarding `SCT`/inclusion paths reveals domain/artifact queried unless scrubbed to `STH`-only gossip) | Epidemic peer/server gossip endpoints (`STH`-only vs. full proof exchange) | Convergence lag under churn; privacy vs. inclusion-proof verification trade-off |
| **CoSi Tree-Cosigning** (`Syta et al., IEEE S&P 2016`) | Threshold $f < W$ out of $W$ tree cosigners | Yes (single aggregated Schnorr/EdDSA multisig + bitmap) | High (client validates embedded cosig offline) | Synchronous 4-phase round-trip multicast tree (`Announcement → Commitment → Challenge → Response`) | Requires persistent leader-initiated synchronous rounds; vulnerable to leader stall unless rotated (note: original 2016 CoSi pre-dates FROST's binding factor against concurrent ROS!) |
| **Stateless-Client HTTP Quorum Witnessing** (`C2SP tlog-witness` + `transparency-dev/witness`) | Safe whenever $q_c + q_m > W + f$ (**Probe 2B**) | **Yes** (log/mirror embeds witness cosignatures into delivered checkpoint) | **High** (clients verify offline; monitors query `<monitoring prefix>/<sha256(origin)>/checkpoint` without leaf IDs) | Per-log `(latestSize, latestHash)` atomic CAS DB per witness | Synchronous witness HTTP RTT during log checkpoint publication; vulnerable to rollback without atomic DB CAS (`witness.go:248`) |

#### 3.1 `C2SP tlog-witness` & `transparency-dev/witness` (`bd0f4ab9...`): Protocol State Machine & CAS Race

Direct inspection of `C2SP/C2SP` (`tlog-checkpoint.md`, `tlog-cosignature.md`, `tlog-witness.md` @ `d35150e7...`) and `transparency-dev/witness` (`witness/witness.go:180-426`) establishes five normative and implementation invariants:

1. **Wire Protocol & Error-Code Discrimination (`tlog-witness.md:87-201`, `witness.go:186-340`):**
   - Logs (or feeders) `POST <submission prefix>/add-checkpoint` with body `old <oldSize>\n(<b64_proof_hash>\n)*\n<checkpoint_note>`.
   - `witness.go:187-238` carefully separates error classes before mutating storage:
     - `404 Not Found` (`ErrUnknownLog`): unknown checkpoint origin line.
     - `403 Forbidden` (`ErrNoValidSignature`): deliberately avoids `log.ParseCheckpoint` (`lines 207-218`) and calls `note.Open(nextRaw, note.VerifierList(v))` directly so invalid/untrusted log signatures return `403` rather than collapsing into `400 Bad Request` (`ErrInvalidCheckpoint`).
     - `400 Bad Request` (`ErrOldSizeInvalid`): `oldSize > next.Size`, malformed note, or `> 63` proof lines.
     - `409 Conflict` (`ErrCheckpointStale`): `oldSize != prevSize`, returning current `prevSize` with `Content-Type: text/x.tlog.size` so out-of-sync feeders can fetch the witness's latest size and retry (`old 0` discovery).
     - `422 Unprocessable Entity` (`ErrRootMismatch` / `ErrInvalidProof`): `next.Size == 0` with hash `!= EmptyRoot()`, `oldSize == 0` with non-empty `cProof`, `next.Size == prevSize` with `next.Hash != prevHash`, or failed `proof.VerifyConsistency`. Note at `witness.go:299-301` that identical-size, identical-hash resubmissions deliberately **refresh** the cosignature timestamp rather than short-circuiting.
2. **Atomic Compare-and-Swap Against Concurrent Rollback (`tlog-witness.md:191-201`, `witness.go:248-334`):**
   - If a witness validates `oldSize` outside a serializable transaction before persisting `next`, two concurrent valid requests `(N -> N+K)` and `(N -> N+1)` can interleave so `(N -> N+K)` returns a cosignature for size `N+K`, and then `(N -> N+1)` overwrites the witness's stored checkpoint back to `N+1`—**rolling back `K-1` leaves** and allowing a compromised log to split the tree from `N+1` onward!
   - `transparency-dev/witness` closes this by running the entire `prevRaw` read → consistency check → `signChkpt` → write sequence inside `w.lsp.Update(ctx, origin, func(prevRaw []byte) ...)` (`witness.go:248`).
3. **Cryptographic Format Differentials (`tlog-checkpoint.md:87-134`, `tlog-cosignature.md:165-236`):**
   - **`Ed25519` (`vkey` type `0x04`):** Signs ASCII lines `"cosignature/v1\ntime <ts>\n<origin>\n<size>\n<b64hash>[\n<ext>...]"` prepended with an 8-byte big-endian timestamp. Crucially: (a) it **includes** checkpoint extension lines; (b) it **omits `cosigner_name`** from the signed message (so `tlog-cosignature.md:232-235` mandates distinct Ed25519 keys per logical cosigner name to prevent cross-cosigner signature replay); and (c) it **cannot** generate `sign-subtree` signatures.
   - **`ML-DSA-44` (`vkey` type `0x06`, FIPS 204):** Signs binary `CosignedSubtree` (`"subtree/v1\n\0"`, `cosigner_name`, `uint64 timestamp`, `log_origin`, `uint64 start`, `uint64 end`, `hash[32]`). Crucially: (a) it binds `cosigner_name`, blocking cross-cosigner key confusion; (b) it supports both checkpoints (`start=0, end=size`) and `sign-subtree` (`timestamp=0`); and (c) it **ignores all checkpoint extension lines** (`tlog-checkpoint.md:91`), meaning clients must never place security-critical metadata in extension lines when relying on `ML-DSA-44` cosignatures!
4. **Byzantine Witness Quorum Intersection & Monitor Asymmetric Quorums (`tlog-witness.md:287-293`, Probe 2B):**
   - Suppose $W$ witnesses verify a log, and up to $f$ witnesses may be Byzantine (colluding with a compromised log to sign conflicting histories). If clients accept a checkpoint backed by $q_c$ witnesses and monitors accept a checkpoint backed by $q_m$ witnesses, **at least one honest witness observes both views** if and only if:
     $$q_c + q_m > W + f$$
   - Because monitors are fewer and can poll `<monitoring prefix>/<sha256(origin)>/checkpoint` asynchronously while clients verify low-overhead embedded checkpoints, `tlog-witness.md:289-293` explicitly notes monitors may require **more** cosignatures ($q_m > q_c$) than clients. **Probe 2B** checks all combinations for $W = 7, f = 2$:
     - Naive majority $(q_c = 4, q_m = 4)$ violates $4 + 4 = 8 \not> 9$, leaving **70** `(Q_client, Q_monitor)` pairs whose intersection is exclusively the 2 Byzantine witnesses (`undetected split view`).
     - Symmetric BFT quorum $(q_c = 5, q_m = 5)$ and asymmetric $(q_c = 4, q_m = 6)$ satisfy $q_c + q_m \ge 10 > 9$, achieving **0** undetected split views.

---

### 4. VRF-Indexed Sparse Merkle Key Directories (`CONIKS` vs. `facebook/akd`)

`Basis: normative + source + derived + execution`

Key Transparency (`KT`) replaces manual fingerprint verification in end-to-end encrypted (`E2EE`) messaging with an auditable dictionary mapping `(username) -> (public key, version)`. Unlike public Certificate Transparency logs, a KT directory **must not** allow third-party auditors or lookups to enumerate all users (`email`/`phone` PII) or read plaintext key histories of other users.

| Architecture | Leaf Addressing & Privacy | Value Hiding | Domain Separation in Sparse Merkle Trie | Update Model & Public Auditor Cost | History / Freshness Verification |
|---|---|---|---|---|---|
| **`CONIKS`** (`coniks-sys/coniks-go`, `google/trillian/merkle/coniks`) | Deterministic VRF `index = VRF(sk, uname)` (`crypto/vrf/vrf.go`) | Salted commitment `Commit(key \|\| val)` (`merkletree/proof.go:55`) | Coordinate binding at leaves/empty nodes: `HashLeaf('L' \|\| nonce/treeID \|\| index \|\| depth \|\| commit)` & `HashEmpty('E' \|\| ...)`; unprefixed interior `H(L \|\| R)` | **In-place mutation**: each epoch overwrites leaf values along VRF path; public auditors must download/replay **every** leaf update ($O(U)$ per epoch) or clients monitor every single epoch | Per-epoch self-lookup + signed STR chain |
| **`facebook/akd`** (`SEEMless` + `Parakeet`, `43a60ccf...`) | `NodeLabel = VRF(sk, H(uname \|\| freshness \|\| version))` | `H(val \|\| H(commit_key, label, v, val))` (`LeafNode` hashed with `epoch`) | Binary radix Patricia trie (`Azks`): empty/leaf/interior node hashing includes 256-bit `NodeLabel` length & bit-prefix (`akd_core/src/verify/base.rs:36-139`) | **Strictly append-only (`AZKS`)**: updating `v-1 -> v` inserts *both* `(Fresh, v)` and `(Stale, v-1)`; public `audit_verify` checks monotonic addition in **$O(\Delta \log N)$** without seeing usernames or values | Binary marker-skiplist (`get_marker_versions`, `O(\log v)` existence/non-existence proofs) |

#### 4.1 `CONIKS` (`coniks-go` & `trillian/merkle/coniks`) Coordinate-Bound Hashing & Doc Bug

Both `coniks-sys/coniks-go` (`11acf4819b71d23bb135a597950e59d74fe75b6c`, `merkletree/proof.go:39-98`) and `google/trillian/merkle/coniks/coniks.go` (`07016bd85eba94134d3e423a1b16f13e19ef366e`, `lines 53-105`) compute interior nodes **without** a `0x01` prefix (`HashChildren(l, r) = H(l || r)`), relying instead on embedding exact `(treeNonce/treeID, index, depth)` plus `'L'`/`'E'` identifiers inside every leaf and empty-subtree terminal hash so an interior `H(l || r)` cannot be substituted at a different depth or index without breaking `(index, depth)` consistency.

**Source Discrepancy in `google/trillian/merkle/coniks/coniks.go:73-84`:** The docstring at line 73 writes `H(Identifier || treeID || depth || index || dataHash)`, whereas the actual `HashLeaf` serialization at lines 79–83 writes `leafIdentifier ("L") || uint64(treeID) || writeMaskedNodeID(id) || uint32(depth) || leaf`—placing `index` **before** `depth`, matching `HashEmpty` (`lines 60-63`). Independent client verifiers following the comment order rather than lines 79–83 will fail every root check.

#### 4.2 `facebook/akd` (`SEEMless`/`Parakeet`): Append-Only ZKS & Marker-Skiplist Verification

Direct inspection of `facebook/akd` (`43a60ccf7dfdd8f4b628186410e871192adaf65b`) traces the exact end-to-end invariant:

1. **Append-Only Epoch Transitions (`directory.rs:150-200`, `append_only_zks.rs:55-70`):**
   - On version `1` creation, `publish` inserts `(Fresh, 1)` with `compute_fresh_azks_value(&commitment_key, &node_label, 1, &akd_value)`.
   - On rotation `v -> v + 1`, `publish` inserts *both* `(Stale, v) -> stale_azks_value()` and `(Fresh, v + 1) -> compute_fresh_azks_value(...)` into the `Azks` Patricia trie.
   - Because `Azks` never overwrites or deletes an existing `(label, version)` leaf (only splitting compressed radix prefixes when new sibling labels arrive, verified via `InsertMode::Auditor` / `NodeHashingMode::NoLeafEpoch` omitting leaf epochs so `audit_verify` checks pure subtree addition), third-party auditors verify global append-only integrity in $O(\Delta \log N)$ without any VRF key or PII.
   - Note that `akd` itself (`directory.rs:1142-1143` comment: *"At the moment the tree root is not being written anywhere"*) does **not** anchor `EpochHash` into an external witness quorum; callers must pair `EpochHash` with a `C2SP tlog-witness` or transparency log to block split-view epochs across users.
2. **Lookup & Sublinear History Verification (`akd_core/src/verify/lookup.rs`, `history.rs`, `utils.rs`):**
   - `lookup_verify` (`lookup.rs:18-72`) verifies 3 VRF+Merkle statements for claimed version `v <= current_epoch`:
     1. `Existence(Fresh, v)` committing to plaintext `akd_value`;
     2. `Existence(Fresh, 1 << floor(log2(v)))` (the single power-of-two base marker);
     3. `NonExistence(Stale, v)` proving version `v` has not yet been rotated to stale.
   - `key_history_verify` (`history.rs:68-347`) verifies contiguous decreasing `update_proofs` (`Fresh(k)` + `Stale(k - 1)` for `k in start_version..=end_version`), plus `Existence(Fresh, m)` for `past_marker_versions` and `NonExistence(Fresh, m)` for `future_marker_versions` produced by `get_marker_versions(start_version, end_version, epoch)` (`utils.rs:15, 98-168`) using binary prefix flips plus `MARKER_VERSION_SKIPLIST = [1, 2, 4, 16, 256, 65536, 2^32]`.
3. **Verified Specification-vs-Implementation Gap: Stealth-Version Bypass (`Basis: source + derived + execution`, Probe 2C):**
   - The `get_marker_versions` skiplist construction in `utils.rs:55-168` proves non-existence of *every* future version `v* > end_version` only under the **SEEMless / Parakeet invariant** that any valid lookup for `v*` must demonstrate existence of **every** ancestor in `past_marker_versions(v*, v*, epoch)` (binary zeroed-suffix prefixes of `v*` plus the largest `MARKER_VERSION_SKIPLIST` milestone $< v^*$, *and* the largest power of two $\le v^*$).
   - However, `lookup.rs:46` checks **only** the single milestone `marker_version = 1 << get_marker_version_log2(proof.version)` (`1 << floor(log2(v*))`)! Meanwhile, `get_marker_versions` (`utils.rs:159-164`) emits `future_marker_versions` up to `16` and then **stops emitting powers of two** once `val >= skiplist_slice[0]` (e.g., skipping `32` in favor of `256`!), relying on `past_marker_versions(32..255)` containing `16`!
   - **Probe 2C** proves both sides empirically at `(start_version=1, end_version=5, current_epoch=33)` (`future_marker_versions = [6, 8, 16]`):
     - Under the pinned `lookup_verify` (`lookup.rs:46`), a malicious directory that secretly inserts `(Fresh, 7)` (without marking version 5 stale—or while marking `5` stale only in a split/delayed view, noting `history.rs` does not query `NonExistence(Stale, end_version)` either, though even checking `NonExistence(Stale, 5)` cannot catch an unmarked stealth insert!) or `(Fresh, 32)` / `(Fresh, 33)` **passes** `Azks` append-only audit (`audit_verify`), **passes** a victim's `lookup_verify(7)` (because `1 << log2(7) = 4` genuinely exists!) and `lookup_verify(32)`/`lookup_verify(33)` (because `1 << log2(32) = 32` is NOT in `future_marker_versions = [6, 8, 16]`!), **and passes** the owner's `key_history_verify(1..5)`!
     - Requiring `lookup_verify` to verify `past_marker_versions(v, v, current_epoch)` (containing `6` and `4` for `v=7`, and `16` for `v=32, 33`) eliminates **all** evading versions (`evading_full_prefix_lookup == []` for all $v^* \in [6, 33]$).

---

## Boundaries

1. **Censorship Resistance & Liveness (Inclusion Past MMD) — `known not to apply`:** RFC 9162 Merkle consistency proofs, `transparency-dev/witness` cosignatures, and `akd` append-only audits detect *equivocation* and *mutated history*. They do **not** prevent a log or directory operator from silently dropping or delaying newly submitted entries indefinitely (or censoring specific users); availability/timeliness requires separate signed submission receipts (`SCT`/`SET`) with enforced Maximum Merge Delay (`MMD`) monitoring.
2. **VRF Key Compromise & Epoch Rotation in `CONIKS` / `facebook/akd` — `known not to apply` / `unsupported`:** If the directory's VRF secret key leaks or is subpoenaed, an adversary holding the key can run an offline dictionary attack mapping candidate usernames to published 256-bit trie labels (breaking user-enumeration privacy, though value commitments remain hiding under random nonces). Furthermore, neither `coniks-go` nor `facebook/akd` (`43a60ccf...`) supports rotating the VRF key across live epochs without reconstructing a fresh directory (`unsupported`).
3. **Rekor v1 Dynamic `gRPC` vs. Rekor v2 Static Tiles — `not examined` in execution:** Source inspection of `sigstore/rekor` (`0baa3971...`) characterizes Rekor v1's Trillian-backed dynamic inclusion/consistency/SET verification and virtual sharding. Static tile log implementations (`C2SP/tlog-tiles.md`) were inspected normatively at specification level (`C2SP/C2SP` @ `d35150e7...`), not executed.
4. **Ed25519 Subtree Cosignatures — `unsupported`:** Per `C2SP/tlog-cosignature.md:203-204`, Ed25519 (`0x04`) cosigner keys can sign full-tree checkpoints only; `sign-subtree` (`tlog-witness.md:202-284`) requires `ML-DSA-44` (`0x06`).
5. **Built-In Global Root Anchoring in `facebook/akd` — `unsupported`:** `akd/src/directory.rs:1142-1143` leaves external distribution/witnessing of `EpochHash` to the integrating application; without an external witness quorum or blockchain anchor, `akd` alone does not prevent the server from presenting forked `EpochHash` trees to distinct clients.
6. **Gossip Convergence Bounds Under Eclipse / Sybil Topologies — `unknown`:** Epidemic gossip bounds in Chuat et al. (IEEE CNS 2015) depend on empirical browser-to-server contact graphs and eclipse resistance parameters not modeled in this investigation.

---

## Evidence

All upstream repositories, specifications, DOIs, and Python 3.13.15 probes were verified on `2026-11-19`.

### Primary Upstream Source Inspections

- **`transparency-dev/merkle` (`75a6539d7b48af0d529236f24487d2814fd1dca7`):**
  - `rfc6962/rfc6962.go:24-94` & `rfc6962/rfc6962_test.go:23-98`: `RFC6962LeafHashPrefix = 0`, `RFC6962NodeHashPrefix = 1`, `EmptyRoot()`, stack-allocated `hashChildren256`, 4 golden SHA-256 test vectors.
  - `compact/range.go:40-264`: `NewRange`, `Append`, `AppendRange`, `GetRootHash`, `getMergePath`, `Decompose`.
  - `proof/verify.go:46-358`: `VerifyInclusion`, `VerifySubtreeInclusion`, `VerifyConsistency`, `VerifySubtreeConsistency`, `decompInclProof`, `decompSubtreeProof`, `chainInner`, `chainInnerRight`, `chainBorderRight`.
- **`google/trillian` (`07016bd85eba94134d3e423a1b16f13e19ef366e`):**
  - `log/sequencer.go:106-199`: `initCompactRangeFromStorage`, `updateCompactRange` (ephemeral node omission at line 193).
  - `server/proof_fetcher.go:38-57`: `fetchNodesAndBuildProof` invoking `pn.Rehash` for read-time proof synthesis.
  - `merkle/coniks/coniks.go:53-105`: `HashEmpty`, `HashLeaf` (`'L' || treeID || index || depth || leaf` vs. comment order at line 73), unprefixed `HashChildren`.
- **`sigstore/rekor` (`0baa39712ffa627b70756ea555193ec84bea4507`):**
  - `pkg/verify/verify.go:38-241`: `ProveConsistency`, `VerifyCurrentCheckpoint`, `VerifyCheckpointSignature`, `VerifyInclusion` (physical shard index), `VerifySignedEntryTimestamp` (JCS-canonicalized virtual index), `VerifyLogEntry`.
  - `pkg/sharding/ranges.go:40-273`: `LogRanges`, `ResolveVirtualIndex` (`lines 182-193`), `LogID` computation (`lines 172-177`).
- **`C2SP/C2SP` (`d35150e795e178b7ad26cdff0ec1877bcc9e9723`):**
  - `tlog-checkpoint.md:49-134`: 3-line checkpoint text, optional extension lines, `ML-DSA-44` (`0x06`, ignores extensions) vs. `Ed25519` (`0x04`, signs extensions).
  - `tlog-cosignature.md:67-236`: cosigner name rules, monotonic checkpoint semantics, `CosignedSubtree` struct (`lines 173-181`), Ed25519 key-separation rule (`lines 232-235`).
  - `tlog-witness.md:87-311`: `add-checkpoint`, `sign-subtree`, atomic update rollback race (`lines 191-201`), monitor asymmetric quorum requirement (`lines 287-293`), `<monitoring prefix>/<origin hash>/checkpoint`.
  - `tlog-tiles.md`: static 256-leaf tile URL addressing (`/tile/<L>/<N>[.p/<W>]`).
- **`transparency-dev/witness` (`bd0f4ab93e8ee9cf3b382d7c903e864c3701a5c5`):**
  - `witness/witness.go:180-426`: `Update` HTTP status mapping (`403` vs. `400` at lines 206–218, `409 Conflict` at line 280, `422` at lines 236, 291, 321), atomic `w.lsp.Update` transaction (`line 248`), timestamp refresh on equal size (`lines 299-301`).
- **`coniks-sys/coniks-go` (`11acf4819b71d23bb135a597950e59d74fe75b6c`):**
  - `merkletree/proof.go:39-154`: `ProofNode.hash` (`EmptyBranchIdentifier` / `LeafIdentifier` with `treeNonce`, `Index`, `Level`, `Commitment`), `authPathHash` (`H(l || r)`), `AuthenticationPath.Verify`.
- **`facebook/akd` (`43a60ccf7dfdd8f4b628186410e871192adaf65b`):**
  - `akd/src/directory.rs:104-265, 302-440, 951-953, 1142-1143`: `Directory::publish` (`Fresh` + `Stale` insertion), `lookup_with_info`, `build_lookup_info`, `get_marker_version`.
  - `akd/src/append_only_zks.rs:55-70`: `InsertMode::Directory` vs. `InsertMode::Auditor`.
  - `akd_core/src/verify/lookup.rs:18-72`: `lookup_verify` checking only single power-of-two `1 << get_marker_version_log2(proof.version)` (`line 46`).
  - `akd_core/src/verify/history.rs:68-347`: `verify_with_history_params`, `key_history_verify`, `verify_single_update_proof`.
  - `akd_core/src/verify/base.rs:36-265`: `verify_membership`, `verify_nonmembership`, `verify_label`.
  - `akd_core/src/utils.rs:15, 26-168, 297-324`: `MARKER_VERSION_SKIPLIST`, `get_marker_versions`, 8 unit test vectors.

### Peer-Reviewed Specifications and Literature

- B. Laurie, E. Messeri, R. Stradling, *"Certificate Transparency Version 2.0"*, `RFC 9162` (`DOI: 10.17487/RFC9162`, 2021); B. Laurie, A. Langley, E. Kasper, *"Certificate Transparency"*, `RFC 6962` (`DOI: 10.17487/RFC6962`, 2013).
- Z. Newman, J. S. Meyers, S. Torres-Arias, *"Sigstore: Software Signing for Everybody"*, ACM CCS 2022 (`DOI: 10.1145/3548606.3560596`).
- L. Chuat, P. Szalachowski, A. Perrig, B. Laurie, E. Messeri, *"Efficient Gossip Protocols for Verifying the Consistency of Certificate Logs"*, IEEE CNS 2015 (`DOI: 10.1109/CNS.2015.7346853`, `arXiv:1511.01514`).
- E. Syta et al., *"Keeping Authorities 'Honest or Bust' with Decentralized Witness Cosigning"*, IEEE S&P 2016 (`DOI: 10.1109/SP.2016.38`).
- M. S. Melara, A. Blankstein, J. Bonneau, E. W. Felten, M. J. Freedman, *"CONIKS: Bringing Key Transparency to End Users"*, USENIX Security 2015.
- M. Chase, A. Deshpande, E. Ghosh, H. Malvai, *"SEEMless: Secure End-to-End Encrypted Messaging with less Trust"*, ACM CCS 2019 (`DOI: 10.1145/3319535.3363202`).
- H. Malvai et al., *"Parakeet: Practical Key Transparency for End-to-End Encrypted Messaging"*, NDSS 2023 (`DOI: 10.14722/ndss.2023.24545`).

### Execution Evidence (`Python 3.13.15`, Linux x86_64, `2026-11-19`)

- **Probe 2A (`RFC 9162` Vectors, Compact Ranges, Second-Preimage Collision):** Verified exact SHA-256 hex equivalence against all 4 `rfc6962_test.go` vectors (`e3b0c4...`, `6e340b...`, `395aa0...`, `aa217f...`), bit-identical agreement between `CompactRange` and recursive `MTH` + all inclusion/consistency proofs across `N in 1..33`, and exact 64-byte unprefixed second-preimage collision vs. `0x00`/`0x01` separation.
- **Probe 2B (Split-View & Witness Quorum Intersection):** Confirmed standalone `verify_inclusion` accepts a forked tree (`branch_victim`), proved `(W=7, f=2)` leaves `70` split-view quorum pairs at `(q_c=4, q_m=4)` and `0` pairs at `(5, 5)` and `(4, 6)`.
- **Probe 2C (`facebook/akd` Marker Skiplist & Stealth-Version Gap):** Passed all 8 unit test vectors from `akd_core/src/utils.rs:299-324`; demonstrated stealth evasion of `[7, 32, 33]` at `(start=1, end=5, epoch=33)` when `lookup_verify` checks only `1 << floor(log2(v))` vs. `[]` (complete rejection) when `past_marker_versions(v, v, epoch)` is checked.

---

## Revalidation

### 1. Cheapest Discriminating Upstream Source Diffs

- **`transparency-dev/witness` vs. `bd0f4ab93e8ee9cf3b382d7c903e864c3701a5c5`:** Diff `witness/witness.go` (`Update` lines 180–340) to verify atomic `w.lsp.Update` `oldSize == prevSize` enforcement and HTTP `403`/`409`/`422` differentiation.
- **`C2SP/C2SP` vs. `d35150e795e178b7ad26cdff0ec1877bcc9e9723`:** Diff `tlog-checkpoint.md`, `tlog-cosignature.md`, and `tlog-witness.md` to check whether `ML-DSA-44` extension-line handling or `sign-subtree` rules changed.
- **`facebook/akd` vs. `43a60ccf7dfdd8f4b628186410e871192adaf65b`:** Diff `akd_core/src/verify/lookup.rs` (`lookup_verify`) and `akd_core/src/utils.rs` (`get_marker_versions`) to check whether `lookup_verify` has been updated to verify all `past_marker_versions(proof.version, proof.version, current_epoch)` instead of only `1 << get_marker_version_log2(proof.version)`.

### 2. Self-Contained Executable Revalidation Probe (Python 3.10+, Standard Library Only)

```bash
python3 - <<'PY'
import hashlib
from itertools import combinations

# --- Probe 2A: RFC 9162 Vectors, CompactRange, Inclusion & Consistency Proofs ---
EMPTY = hashlib.sha256(b"").digest()
h_leaf = lambda d: hashlib.sha256(b"\x00" + d).digest()
h_node = lambda l, r: hashlib.sha256(b"\x01" + l + r).digest()

assert EMPTY.hex() == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
assert h_leaf(b"").hex() == "6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d"
assert h_leaf(b"L123456").hex() == "395aa064aa4c29f7010acfe3f25db9485bbd4b91897b6ad7ad547639252b4d56"
assert h_node(b"N123", b"N456").hex() == "aa217fe888e47007fa15edab33c2b492a722cb106c64667fc2b044444de66bbb"

# Second-preimage attack without 0x00/0x01 prefixes vs defense with prefixes
raw = lambda b: hashlib.sha256(b).digest()
assert raw(raw(b"certA") + raw(b"certB")) == raw(raw(b"certA") + raw(b"certB"))
assert h_node(h_leaf(b"certA"), h_leaf(b"certB")) != h_leaf(h_leaf(b"certA") + h_leaf(b"certB"))

def mth(ls):
    n = len(ls)
    if n == 0: return EMPTY
    if n == 1: return h_leaf(ls[0])
    k = 1 << ((n - 1).bit_length() - 1)
    return h_node(mth(ls[:k]), mth(ls[k:]))

def gen_inc(ls, m):
    n = len(ls)
    if n <= 1: return []
    k = 1 << ((n - 1).bit_length() - 1)
    return (gen_inc(ls[:k], m) + [mth(ls[k:])]) if m < k else (gen_inc(ls[k:], m - k) + [mth(ls[:k])])

def gen_cons(ls, m, b_t=True):
    n = len(ls)
    if m == n: return [] if b_t else [mth(ls)]
    k = 1 << ((n - 1).bit_length() - 1)
    return (gen_cons(ls[:k], m, b_t) + [mth(ls[k:])]) if m <= k else (gen_cons(ls[k:], m - k, False) + [mth(ls[:k])])

def verify_inc(idx, sz, lh, prf, root):
    inner = (idx ^ (sz - 1)).bit_length(); border = (idx >> inner).bit_count()
    assert len(prf) == inner + border
    s = lh
    for i, h in enumerate(prf[:inner]):
        s = h_node(s, h) if ((idx >> i) & 1) == 0 else h_node(h, s)
    for h in prf[inner:]: s = h_node(h, s)
    return s == root

def verify_cons(s1, s2, prf, r1, r2):
    if s1 == s2: return len(prf) == 0 and r1 == r2
    inner = ((s1 - 1) ^ (s2 - 1)).bit_length(); border = ((s1 - 1) >> inner).bit_count()
    shift = (s1 & -s1).bit_length() - 1; inner -= shift
    seed, rest = (r1, prf) if s1 == (1 << shift) else (prf[0], prf[1:])
    assert len(rest) == inner + border
    mask = (s1 - 1) >> shift
    h1, h2 = seed, seed
    for i, h in enumerate(rest[:inner]):
        if (mask >> i) & 1: h1 = h_node(h, h1)
        h2 = h_node(h2, h) if ((mask >> i) & 1) == 0 else h_node(h, h2)
    for h in rest[inner:]: h1, h2 = h_node(h, h1), h_node(h, h2)
    return h1 == r1 and h2 == r2

leaves = [f"e{i}".encode() for i in range(25)]
cr_end, cr_h, roots = 0, [], [EMPTY]
for i, lf in enumerate(leaves, 1):
    seed, idx = h_leaf(lf), cr_end
    while idx & 1: seed = h_node(cr_h.pop(), seed); idx >>= 1
    cr_h.append(seed); cr_end += 1
    acc = cr_h[-1]
    for h in reversed(cr_h[:-1]): acc = h_node(h, acc)
    assert acc == mth(leaves[:i])
    roots.append(acc)
    for j in range(i): assert verify_inc(j, i, h_leaf(leaves[j]), gen_inc(leaves[:i], j), acc)
for a in range(1, 26):
    for b in range(a, 26): assert verify_cons(a, b, gen_cons(leaves[:b], a), roots[a], roots[b])

# --- Probe 2B: Split-View & Byzantine Witness Quorum Intersection ---
def split_pairs(qc, qm, W=7, f=2):
    nodes, byz = list(range(W)), set(range(W - f, W))
    return sum(1 for a in combinations(nodes, qc) for b in combinations(nodes, qm) if not ((set(a) & set(b)) - byz))

assert split_pairs(4, 4) == 70 and split_pairs(5, 5) == 0 and split_pairs(4, 6) == 0

# --- Probe 2C: facebook/akd Marker Skiplist & Stealth-Version Check ---
SK = [1, 2, 4, 16, 256, 65536, 1 << 32]
def markers(sv, ev, ep):
    past = []
    idx_s = max(i for i, v in enumerate(SK) if sv >= v)
    if SK[idx_s] != sv: past.append(SK[idx_s])
    p2 = 1 << (sv.bit_length() - 1)
    if p2 != sv and (not past or p2 != past[-1]): past.append(p2)
    for i in range(sv.bit_length() - 1, -1, -1):
        if sv & (1 << i):
            pv = sv & ~(((1 << i) - 1) | (1 << i))
            if pv != 0 and (not past or pv != past[-1]): past.append(pv)
    fut, fv = [], ev
    for i in range(ev.bit_length()):
        if not (ev & (1 << i)):
            fv = (fv | (1 << i)) & ~((1 << i) - 1)
            if fv <= ep: fut.append(fv)
    sl = SK[max(i for i, v in enumerate(SK) if ev >= v) + 1 : max(i for i, v in enumerate(SK) if ep >= v) + 1]
    for i in range(ev.bit_length(), ep.bit_length()):
        if sl and (1 << i) >= sl[0]: break
        fut.append(1 << i)
    return past, fut + sl

assert markers(85, 85, 65537) == ([16, 64, 80, 84], [86, 88, 96, 128, 256, 65536])
assert markers(1, 5, 33) == ([], [6, 8, 16])
_, fut = markers(1, 5, 33)
evading_now = [v for v in range(6, 34) if not ({v, 1 << (v.bit_length() - 1)} & set(fut))]
evading_fixed = [v for v in range(6, 34) if not (({v, 1 << (v.bit_length() - 1)} | set(markers(v, v, 33)[0])) & set(fut))]
assert evading_now == [7, 32, 33] and evading_fixed == []
print("All Package 2 revalidation probes (2A-2C) passed.")
PY
```
