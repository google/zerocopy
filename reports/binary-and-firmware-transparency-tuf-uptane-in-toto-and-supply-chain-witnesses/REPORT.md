# End-to-End Binary and Firmware Transparency, Compromise-Resilient Update Distribution, Supply-Chain Attestation, and Witnessing

## Summary

End-to-end software and firmware supply-chain integrity does not arise from any single cryptographic primitive. Rather, an authoritative trust verdict decomposes into **five orthogonal verification planes**, each answering a strictly distinct security question:

1. **Global Log Inclusion (`RFC 6962` / `RFC 9162` Merkle Logs, Google FT, Go `sumdb`):** Proves that an immutable artifact digest, firmware measurement, or module zip summary hash was appended to a publicly inspectable tree at leaf index $i$ under a signed tree head $(N, H_N)$. Alone, log inclusion **does not** prove the log did not serve a split view, nor that the logged artifact was honestly built or free of vulnerabilities.
2. **Non-Equivocation via Quorum Witnesses (`C2SP/tlog-witness`, `transparency-dev/witness`, `Chainiac` CoSi Skipchains):** Prevents a compromised log operator from serving forked, mutually inconsistent Merkle histories to targeted victims by requiring threshold cosignatures over monotonic consistency transitions $(N_{\text{old}}, H_{\text{old}}) \preceq (N_{\text{new}}, H_{\text{new}})$.
3. **Compromise-Resilient Update Distribution (`TUF`, `Uptane`):** Defends clients and heterogeneous vehicle ECUs against key compromise, repository compromise, freeze, rollback, slow-retrieval, endless-data, and mix-and-match attacks through strict four-role key separation (`root`, `targets`, `snapshot`, `timestamp`), threshold signatures, short expiration windows, and (in `Uptane`) dual-repository cross-verification (`Director` vs. `Image` repositories).
4. **Pipeline Step & Build-Service Attestation (`in-toto`, `SLSA`):** Enforces that every authorized pipeline stage (`steps` / `inspect` in `in-toto`) or an isolated hosted control plane (`SLSA` Build L3 `builder.id` + `externalParameters`) observed the exact input-to-output digest transformations—yet **does not** independently prove deterministic source-to-binary reproducibility unless coupled with multi-builder consensus.
5. **Reproducible Build Cosigning & Verifiable Key Directories (`Chainiac`, `AKD`, Apple KT/PCC):** Bridges source revisions to identical bit-for-bit artifacts across independent verifiers (`Chainiac` software/verifier skipchains) or binds public identities and encrypted service releases (`facebook/akd` VRF-indexed AZKS tries; Apple Contact Key Verification and Private Cloud Compute Image4 logs) without exposing full user directories.

Crucially, composing these planes exposes sharp boundary failure modes documented directly in upstream codebases: pairwise consistency verification between `(bundle, witness)` and `(bundle, map)` permits undetected forks between `witness` and `map` unless anchored to a globally monotonic highest checkpoint; `in-toto` step command alignment is explicitly *advisory* (logged as a warning rather than failing verification); `SLSA` v1.0 Build L2–L3 deliberately allows tenant-controlled `subject` digests; and verifiable sparse Merkle/Patricia directories (`AKD`) must guard against interior-node prefix collisions during append-only proof partitioning.

## Applicability

This report synthesizes specifications, reference implementations, and peer-reviewed protocols across thirteen pinned upstream subjects (all observed on `2026-11-19`) together with primary academic papers:

- **Firmware & Binary Merkle Logs and Witnesses:** `google/trillian-examples` (`binary_transparency/firmware`, commit `6931e636566371f9fa8b9e664594ab05fcacaa08`), `transparency-dev/witness` (`bd0f4ab93e8ee9cf3b382d7c903e864c3701a5c5`), `C2SP/C2SP` (`tlog-checkpoint`, `tlog-cosignature`, `tlog-witness` at `d35150e795e178b7ad26cdff0ec1877bcc9e9723`), and `lowRISC/opentitan` (`sw/device/silicon_creator/lib/manifest.h` at `b9e9ccd9e959071f8be21c20fa9ffc4eaa06a8f5`). Findings here characterize log-backed firmware deployment, witness cosigning, and hardware device-constraint manifests.
- **Compromise-Resilient Update Frameworks:** `theupdateframework/specification` (`tuf-spec.md` at `e2bc7d83d0740aaae8dd7133dd4f237ce3d86b16`), `theupdateframework/python-tuf` (`tuf/ngclient/updater.py` at `8e8a78a113b5d691672af4549d0a7abefe92b055`), Samuel et al. (ACM CCS 2010), `uptane/uptane-standard` (`uptane-standard.md` at `a02f9cace9e842dbc33f2151b47620a50ccc9151`), and Kuppusamy et al. (escar 2016 / IEEE Veh. Technol. Mag. 2018). Applicability distinguishes general repository clients (`python-tuf`) from automotive multi-ECU networks (`Uptane` Primary vs. Full/Partial Secondary ECUs).
- **Supply-Chain Provenance & Reproducible Cosigning:** `in-toto/in-toto` (`e352b43ad7cb8915d84c36d791aa61346152a0a3`), `in-toto/attestation` (`50bf01716982189898823e90586075f37cd9bb7d`), Torres-Arias et al. (USENIX Security 2019), `slsa-framework/slsa` (`8c3161670b7a6cf7bd6d858b2332ae7eb0838b0c`, SLSA Build Levels v1.x), `dedis/cothority` (`skipchain` at `e0c9afbb847b070e1bda6f54561a4082b803db80`), and Nikitin et al. (`Chainiac`, USENIX Security 2017).
- **Ecosystem Checksum & Key/Release Transparency:** `golang/mod` (`sumdb` and `sumdb/dirhash` at `2b553c8b61bf9bfb6f7e92f5cca8ccdf153835cc`), `facebook/akd` (`akd/src/auditor.rs` and WhatsApp KT auditor at `43a60ccf7dfdd8f4b628186410e871192adaf65b`), plus vendor documentation for Apple Contact Key Verification and Private Cloud Compute release transparency.

All claims apply to the specific pinned revisions and architectures; relationships across systems are comparative and compositional (showing which security invariants each layer supplies and where cross-layer composition gaps persist).

## Findings

### 1. Compositional Security Model and Cross-System Guarantee Matrix

Basis: normative + source + derived

An end-to-end "source-to-device" transparency claim $\mathcal{V}(\text{src}, \text{bin}, \text{dev})$ requires five distinct predicates to hold simultaneously. No single system in the surveyed ecosystem establishes all five alone:

$$\mathcal{V}(\text{src}, \text{bin}, \text{dev}) \iff \underbrace{\text{ValidDist}(\text{bin})}_{\text{TUF / Uptane}} \;\wedge\; \underbrace{\text{StepProv}(\text{src} \leadsto \text{bin})}_{\text{in-toto / SLSA}} \;\wedge\; \underbrace{\text{ReproEquiv}(\text{src}, \text{bin})}_{\text{Chainiac / Rebuilders}} \;\wedge\; \underbrace{\text{LogIncl}(N, H_N, i, \text{stmt})}_{\text{FT / sumdb / Rekor}} \;\wedge\; \underbrace{\text{NoSplitView}_{k/n}(H_N)}_{\text{C2SP Witness / Gossip}}$$

Where:
- **Distribution Compromise Resilience ($\text{ValidDist}$):** Prevents an attacker holding compromised online transport, mirror, or automated signing keys from forcing stale, rolled-back, partial, or mismatched artifacts onto targets.
- **Provenance & Workflow Integrity ($\text{StepProv}$):** Binds output digests to authenticated pipeline steps (`in-toto`) or an isolated control plane (`SLSA` L3).
- **Source-to-Binary Reproducibility ($\text{ReproEquiv}$):** Requires $k$-of-$n$ independent verifiers to rebuild $\text{src}$ deterministically and confirm byte equality with $\text{bin}$, eliminating single-builder trust.
- **Public Append-Only Visibility ($\text{LogIncl}$):** Forces every distributed digest or release measurement into a publicly auditable Merkle log so malware or targeted backdoors cannot remain hidden from monitors.
- **Split-View Prevention ($\text{NoSplitView}_{k/n}$):** Ensures the log's tree head $(N, H_N)$ lies on a single global linear prefix verified by independent witnesses or BFT forward links.

| System | Threat Boundary Addressed | Key Separation / Quorum | Anti-Split-View Mechanism | Anti-Rollback / Anti-Freeze | Reproducible Build Enforcement |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Google FT (`trillian-examples`)** | Hidden/unlogged firmware & binary distribution | Publisher key + Log signer + Witness key + Annotator keys | Witness checkpoint consistency + external monitors | Client device checkpoint monotonicity (`dc.Size <= pc.Size`) | Out-of-scope (monitors scan images post-publish) |
| **TUF (`python-tuf`)** | Compromised mirrors, repository key compromise, MITM | 4 roles (`root`, `targets`, `snapshot`, `timestamp`), $(k,n)$ thresholds | Out-of-scope (relies on monotonic version + offline `root`) | `timestamp` & `snapshot` short `expires`; strict monotonic `version` | Out-of-scope |
| **Uptane (`uptane-standard`)** | Automotive OTA & compromised online Director / ECU mix-and-match | Offline `Image` repo + online `Director` repo + per-ECU identity keys | Optional repository mapping; relies on dual-repo cross-check | `release_counter` monotonicity, secure attested time, `Vehicle Version Manifest` | Out-of-scope |
| **`in-toto` (`in-toto`)** | Compromised CI step, skipped QA/review, unauthorized artifact mutation | Layout root key(s) + per-step functionary $(k,n)$ keys | Out-of-scope (offline layout + link bundle verification) | `Layout.expires` timestamp; step material-to-product chaining | Only if an explicit rebuild inspection step is configured |
| **SLSA v1.0 (`slsa-framework/slsa`)** | Tampered CI inputs, multi-tenant build cross-contamination | Isolated control-plane signing key vs. untrusted tenant steps (L3) | Recommended external transparency log / timestamping | Rely on consumer policy + `externalParameters` pinning | **No** (L3 isolates builder, does not verify determinism) |
| **Chainiac (`dedis/cothority`)** | Compromised developer/build server, split-view release feeds | Developer threshold + independent `verifier` BFT roster (`Skipchain`) | BFT collectives (`CoSi`) + cryptographic forward-links | Skipchain monotonic index & forward-link finality | **Yes** (core invariant: independent verifiers rebuild before cosigning) |
| **Go `sumdb` (`golang/mod`)** | Poisoned GOPROXY / upstream tag mutation after release | `sum.golang.org` signed note key + `GONOSUMDB` exclusion list | Client-cached monotonic `latest` STH + `CheckTree` misbehavior proof + external `witness` feeders | Immutable module version records; monotonic `tree.N` | Content-addressed `h1:` zip/dir hash (zip metadata stripped) |
| **Meta `AKD` / WhatsApp KT** | Equivocating E2EE public-key server injecting ghost devices | Directory operator + independent offline/third-party auditors (`AuditBlob`) | Epoch-by-epoch `SingleAppendOnlyProof` AZKS tree verification | Monotonic epochs + key-history proofs per VRF-blinded label | N/A (key-binding directory, not binary builder) |

---

### 2. Google Binary & Firmware Transparency (`trillian-examples` FT) and OpenTitan Manifests

Basis: source + normative

In `google/trillian-examples` (`binary_transparency/firmware`, commit `6931e636566371f9fa8b9e664594ab05fcacaa08`), Firmware Transparency separates *firmware authenticity* (signed by the publisher) from *public log commitment* (signed by the FT personality) and *device state continuity* (checked by an offline or connected `flash_tool`).

#### Firmware Metadata, Proof Bundles, and Boot-Time Measurement Binding

Each firmware release is described by `api.FirmwareMetadata` (`binary_transparency/firmware/api/firmware_metadata.go:20-47`):

- `DeviceID` (`string`): target hardware class.
- `FirmwareRevision` (`uint64`): monotonic firmware counter.
- `FirmwareImageSHA512` (`[]byte`): exact SHA-512 digest of the update payload as delivered to devices.
- `ExpectedFirmwareMeasurement` (`[]byte`): expected post-install hardware measurement (e.g., TPM PCR / RoT boot measurement).
- `BuildTimestamp` (`string`, RFC 3339).

An OTA payload `api.UpdatePackage` (`api/update_package.go:18-34`) bundles `FirmwareImage []byte` together with a serialized `ProofBundle` containing three fields: `ManifestStatement` (an `api.SignedStatement` wrapping the JSON-marshaled `FirmwareMetadata` signed by `crypto.Publisher`), `Checkpoint` (a `signed note` tree head), and `InclusionProof` (`LeafIndex` + audit path hashes).

Verification in `internal/verify/bundle.go:40-149` executes two distinct entrypoints:
1. **`BundleForUpdate`** (`bundle.go:40-68`): Validates the checkpoint note signature (`logSigVerifier`), checks the publisher signature on `ManifestStatement` and verifies `Statement.Type == api.FirmwareMetadataType`, computes the RFC 6962 leaf hash `HashLeaf(pb.ManifestStatement)` (`0x00`-prefixed) and verifies `proof.VerifyInclusion(...)`, checks `sha512(FirmwareImage) == fwMeta.FirmwareImageSHA512`, and—if the device already holds a non-zero checkpoint `dc.Size > 0`—verifies a Merkle **consistency proof** (`proof.VerifyConsistency`) from `dc` to `pc`.
2. **`BundleForBoot`** (`bundle.go:101-111`): Re-verifies the `ProofBundle` and checks `bytes.Equal(measurement, fwMeta.ExpectedFirmwareMeasurement)`, bridging on-device measured boot (UEFI/BMC/RoT hardware attestation) to the publicly logged release manifest.

For hardware roots of trust such as OpenTitan (`lowRISC/opentitan` `sw/device/silicon_creator/lib/manifest.h` at `b9e9ccd9e959071f8be21c20fa9ffc4eaa06a8f5`), hardware-enforced manifest structures bind firmware stages directly to device lifecycle constraints before execution: `manifest_usage_constraints_t` (`manifest.h:37-78`) selects OTP `DEVICE_ID` words (bits 0–7), creator/owner manufacturing status (`bits 8–9`), and lifecycle state (`bit 10`), defaulting unselected constraint words to `MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL` (`0xA5A5A5A5`, `manifest.h:83`) alongside `security_version` anti-rollback checks and ECDSA-P256 / SPHINCS+ / ML-DSA-87 key fields (`manifest.h:17-20`). Logging the canonical image hash and expected OpenTitan `ROM_EXT` measurement in FT ensures any firmware accepted by silicon ROM also has an auditable global log entry.

#### Monitor Annotation & Pairwise-Consistency Hazard in `flash_tool.go`

In `cmd/ft_monitor/impl/ft_monitor.go:128-201`, independent monitors tail checkpoints via `NewLogFollower`, fetch the raw firmware image corresponding to `FirmwareImageSHA512`, confirm the SHA-512 digest matches the log statement (`ft_monitor.go:149-152`), run static inspection/keyword matchers, and optionally publish signed `api.MalwareStatement` annotations (`Good: !malwareDetected`) into a verifiable map/annotation pipeline.

Crucially, source inspection of `cmd/flash_tool/impl/flash_tool.go:226-250` reveals a subtle **split-view graph edge flaw** documented directly in the implementation comments (`flash_tool.go:244-247`): `flash_tool` verifies `BundleForUpdate` (device checkpoint $\to$ bundle checkpoint), then optionally `verifyWitness` (witness checkpoint $\leftrightarrow$ bundle checkpoint), and then `verifyAnnotations` (map checkpoint $\leftrightarrow$ bundle checkpoint). Checking consistency of `bundle` against `witness` and `bundle` against `map` independently **does not guarantee consistency between `witness` and `map`** if `bundle` lies at a smaller tree size $N_b < \min(N_w, N_m)$ prior to a fork! A strict linear ordering requires anchoring all checkpoints monotonically against the *largest observed checkpoint* across witness, map, and device state.

---

### 3. C2SP Checkpoints, Witness Cosigning (`transparency-dev/witness`), and Split-View Defenses

Basis: normative + source + execution

To eliminate bespoke log checkpoint formats, `C2SP/C2SP` (`d35150e795e178b7ad26cdff0ec1877bcc9e9723`) standardizes three composable specifications derived from Go `sumdb` signed notes:

1. **`tlog-checkpoint.md:49-134`:** Defines a canonical multi-line note body:
   - Line 1: log `origin` (schema-less UTF-8 string $\le 255$ bytes, no spaces/`+`/control chars).
   - Line 2: `tree size` (base-10 ASCII decimal, `"0"` for empty).
   - Line 3: canonical RFC 4648 base64 `root hash` of the RFC 6962 Merkle tree at that size.
   - Optional non-empty extension lines (discouraged because ML-DSA-44 cosignatures ignore extension lines).
   - Signature lines use key ID `SHA-256(<cosigner name> || "\n" || <type_byte> || <pubkey>)[:4]`, supporting Ed25519 log signatures, timestamped Ed25519 cosignatures (`0x04`, covering extension lines + 8-byte big-endian POSIX timestamp), and post-quantum **ML-DSA-44** checkpoint cosignatures (`0x06`, 1312-byte public key, covering only lines 1–3 + 8-byte timestamp).
2. **`tlog-cosignature.md:115-141`:** Enforces **monotonic checkpoint semantics**: if a cosigner signs a checkpoint at size $N$, every subsequent checkpoint cosignature for that `(cosigner, log)` tuple MUST satisfy $N' \ge N$ and remain consistent with size $N$. Subtree cosignatures additionally attest to `[start, end)` subtree roots without timestamps (`draft-ietf-plants-merkle-tree-certs`).
3. **`tlog-witness.md:87-160`:** Defines the synchronous `POST <submission prefix>/add-checkpoint` HTTP protocol. The client supplies `old <prev_size>`, up to 63 base64 RFC 6962 consistency proof nodes, a blank line, and the candidate checkpoint. The witness enforces strict HTTP error semantics:
   - `404 Not Found` for unknown log origin;
   - `403 Forbidden` if no valid trusted log signature is present or a known key ID has an invalid signature;
   - `400 Bad Request` if `old_size > new_size`;
   - **`409 Conflict`** with `Content-Type: text/x.tlog.size` returning the witness's true latest tree size if `old_size` mismatches the witness's persisted size (allowing logs/feeders to resynchronize after network partitions);
   - `422 Unprocessable Entity` if `new_size == 0` with non-empty root hash or if the RFC 6962 consistency proof fails.

In `transparency-dev/witness` (`bd0f4ab93e8ee9cf3b382d7c903e864c3701a5c5`), `cmd/omniwitness/monolith.go` and `cmd/feedwitness/feeder/pixelbt/pixel_feeder.go:32-124` demonstrate how independent witnesses continuously poll heterogeneous production logs—including Go `sumdb`, Sigstore `rekor_v1`, serverless tlogs, and **Google Pixel Binary Transparency (`pixelbt`)** (`tileHeight = 1`, `checkpoint.txt` + `tile/<H>/<L>/<N>[.p/<W>]` static tiles)—and publish cosignatures back to logs or distributors so end devices verify offline `ProofBundle`s using an embedded $k$-of-$n$ witness policy without contacting the log online.

---

### 4. The Update Framework (`python-tuf`) and Automotive Uptane (`uptane-standard`)

Basis: normative + source + documentation + execution

Whereas Merkle logs detect *equivocation* and *hidden releases*, they do not protect clients from *stale/frozen metadata*, *partial dependency mix-and-match*, or *key compromise* on an active update server. Samuel et al. (ACM CCS 2010, *Survivable Key Compromise in Software Update Systems*, `DOI: 10.1145/1866307.1866315`) established the design axioms of **The Update Framework (TUF)** (`theupdateframework/specification` @ `e2bc7d83d0740aaae8dd7133dd4f237ce3d86b16`), realized in `theupdateframework/python-tuf` (`8e8a78a113b5d691672af4549d0a7abefe92b055`).

#### TUF Four-Role Separation & Client Refresh Workflow (`tuf/ngclient/updater.py`)

TUF separates trust into four roles with disjoint compromise blast radii and configurable `(threshold, keyids)` multisig policies:

1. **`Root` (offline / longest expiry):** Establishes the trusted public keys and signature thresholds for all four top-level roles and `consistent_snapshot` mode. `Updater._load_root` (`updater.py:387-432`) rotates keys strictly sequentially (`version + 1` up to `max_root_rotations`) so an expired intermediate root can still validate successor rotation up to `root_max_length` bytes (defending against endless-data DoS).
2. **`Timestamp` (online / shortest expiry—minutes to hours):** Signs only the hash, length, and version of the latest `Snapshot` metadata. `Updater._load_timestamp` (`updater.py:433-454`) requires `version >= prev_version` (silently ignoring `EqualVersionNumberError`) and rejects expired timestamps—stopping **freeze attacks** (where a mirror keeps re-serving an old signed release indefinitely).
3. **`Snapshot` (semi-online or online):** Records the exact `(version, length, hashes)` of `Targets` and *all* delegated targets files. `Updater._load_snapshot` (`updater.py:455-474`) enforces consistent cross-role views—stopping **mix-and-match attacks** where an attacker combines an older signed `targets-a.json` with a newer `targets-b.json`.
4. **`Targets` & Delegated Roles (offline developer/CI keys):** Maps target paths to exact lengths and cryptographic hashes (`TargetFile.verify_length_and_hashes` in `updater.py:248, 306`). `Updater._preorder_depth_first_walk` (`updater.py:513-581`) traverses delegations in declaration order up to `max_delegations`, respecting `terminating` flags (`updater.py:563-566`) to prevent lower-priority roles from overriding high-trust paths.

#### Uptane Dual-Repository Split for Heterogeneous Vehicle ECUs

Vehicles present two constraints that break stock TUF (`uptane/uptane-standard` @ `a02f9cace9e842dbc33f2151b47620a50ccc9151`, *Uptane: Securing Software Updates for Automobiles*, Kuppusamy et al., escar 2016; IEEE VTM 2018): (i) OTA campaigns must dynamically bundle *per-VIN/per-ECU* dependencies, forcing private keys online, and (ii) Secondary ECUs on CAN/LIN/FlexRay buses lack megabytes of flash/RAM for full multi-role signature verification or direct Internet access.

Uptane solves this via **dual-repository cross-verification** (`uptane-standard.md:554-796`):

- **Offline `Image Repository` (`uptane-standard.md:563-576`):** Controlled infrequently by human/OEM release authorities (with supplier delegations). It holds the canonical catalog of *all* legitimate OEM-approved images, their lengths, cryptographic hashes, and valid hardware IDs.
- **Online `Director Repository` (`uptane-standard.md:577-619`):** Receives a signed **`Vehicle Version Manifest`** (`uptane-standard.md:665-698`) from the vehicle's **Primary ECU**, containing per-ECU signed **ECU Version Reports** (`ECU ID`, installed filename/length/hashes, attack-detection flags, attested time, and a **per-cycle nonce/counter** preventing manifest replay). The Director resolves dependencies/conflicts against a private **Inventory Database** (`VIN`, `ECU serial`, `ECU key`, `hardware_id`) and generates custom per-vehicle `Targets`, `Snapshot`, and `Timestamp` metadata on demand.
- **Full vs. Partial Verification (`uptane-standard.md:628-638, 703-786`):**
  - **Primary ECU (Full Verification):** Downloads and verifies all 4 TUF roles from **both** the `Director` and `Image` repositories independently (`download_meta_primary`), plus verifies that for every target selected by the `Director`, the target exists in the `Image` repository with identical `length` and **all** listed digests (`download_images_primary`). Thus, even a **100% compromised online Director** holding valid Director signing keys *cannot* cause a Primary ECU to install malicious firmware not already signed by the offline Image Repository!
  - **Partial-Verification Secondary ECU:** Stores only `Director` `Root` and `Targets` metadata (`build-time prerequisite`, `uptane-standard.md:637`) and verifies the image's signature (via Director Targets), `hardware_id` equality (`verify_image` step 3, blocking **mix-and-match incompatible flashing** across hardware revisions), wildcard path authorization (step 4), monotonic `release_counter >= prev_release_counter` (step 5), and exact `length` + hashes (steps 7, `uptane-standard.md:767-783`). Note the precise architectural boundary: a compromised Director *can* still cause a partial-verification Secondary (absent full Image repo validation on the Primary or if the Primary itself is also compromised) to accept a valid-signed but unauthorized Image binary if the Primary is bypassed—hence `uptane-standard.md:628` recommends Full Verification for safety-critical ECUs wherever hardware permits.

---

### 5. `in-toto` Supply-Chain Layouts, `SLSA` Build Provenance, and `Chainiac` Cosigned Rebuilds

Basis: normative + source + documentation

#### `in-toto` Multi-Step Policy Verification (`in_toto/verifylib.py`)

Introduced by Torres-Arias et al. (USENIX Security 2019, *in-toto: Providing farm-to-table guarantees for bits and bytes*), `in-toto` (`in-toto/in-toto` @ `e352b43ad7cb8915d84c36d791aa61346152a0a3`) models a software supply chain as a signed **`Layout`** (`in_toto/models/layout.py`) specifying authorized `steps` (executed remotely by functionaries producing signed **`Link`** metadata containing `materials` and `products` hashes) and local **`inspect`** checks run by the verifier.

Examining `in_toto/verifylib.py:1484-1642` reveals four critical implementation semantics that determine verification strength:

1. **Strict 11-Stage Execution Order (`verifylib.py:1498-1511`):**
   1. Verify layout signatures (`verify_metadata_signatures`) and expiration (`verify_layout_expiration`).
   2. Substitute layout parameters (`substitute_parameters`).
   3. Load `STEP-NAME.KEYID-PREFIX.link` files and enforce functionary $(k, n)$ signature thresholds (`verify_link_signature_thresholds`), recursing into sublayouts (`verify_sublayouts`).
   4. **Command Alignment Is Non-Fatal (`verifylib.py:1504-1507, 1612`):** `verify_all_steps_command_alignment` checks `link.command` against `step.expected_command` and logs a warning on mismatch—it **does not raise an error**. Security relies on `materials`/`products` artifact rules rather than CLI string equality.
   5. **Threshold Agreement (`verify_threshold_constraints`, `verifylib.py:1190-1279`):** When `threshold > 1`, at least `threshold` distinct authorized functionaries must report identical `materials` and `products` digests; `reduce_chain_links` discards unagreed links.
   6. **Artifact Rule Queue State Machine (`verifylib.py:1014-1188`):** Each step/inspection starts with `artifacts_queue = set(materials)` (for material rules) or `set(products)` (for product rules). Rules (`MATCH`, `CREATE`, `DELETE`, `MODIFY`, `ALLOW`, `DISALLOW`, `REQUIRE`) are evaluated sequentially, consuming matched paths from `artifacts_queue`! A `DISALLOW *` rule at the end of a rule list rejects any unconsumed artifact—failing closed against unexpected file injections—while omitting `DISALLOW *` leaves unconsumed files silently allowed.
   7. **Step Rules Before Inspections (`verifylib.py:1618-1635`):** Step product/material rules execute *before* `run_all_inspections`, ensuring local verification commands do not run on untrusted files that already violated upstream provenance.
2. **Offline Isolation (`verifylib.py:1513-1521`):** `in-toto` intentionally performs zero external PGP/PKI keyserver or revocation lookups; key revocation requires signing and distributing a new `Layout`.

#### `SLSA` v1.0 Build Levels vs. Deterministic Reproducibility

Modern `in-toto` attestations standardize the JSON `Statement/v1` envelope (`in-toto/attestation/spec/v1/statement.md:9-66`), pairing immutable `subject` digests (`[{"name": ..., "digest": {"sha256": ...}}]`) with a typed `predicateType`. The SLSA provenance predicate (`https://slsa.dev/provenance/v1`, `slsa-framework/slsa/spec/build-provenance.md:16-99` at `8c3161670b7a6cf7bd6d858b2332ae7eb0838b0c`) distinguishes:
- **`builder.id`**: Identifies the transitive closure of the trusted build control plane.
- **`externalParameters`**: Untrusted user-facing trigger inputs (e.g., git repo URI, tag, workflow path) that **MUST** be populated by the trusted control plane and **MUST** be verified by downstream policy (`build-provenance.md:73-75`).
- **`internalParameters`**: Platform-set parameters that need not be checked by consumers.
- **`resolvedDependencies`**: Concrete pinned commit SHAs and fetched materials.

Inspection of `slsa-framework/slsa/spec/build-requirements.md:30-67, 213-256` clarifies a widespread misconception: **SLSA Build L3 guarantees control-plane isolation and unforgeable provenance signing, NOT build reproducibility or build-script cleanliness**:
- At Build L2 and L3, `spec/build-requirements.md:224-228` explicitly permits the **tenant build step** (not just the control plane) to generate output `subject` digests (because an adversarial tenant already controls the binary bytes built by its own code, whereas it cannot forge `builder.id` or `externalParameters` like source repo URI).
- Thus, SLSA Build L3 proves *"isolated builder $B$ ran workflow $W$ from repo $R$ at commit $C$ and produced digest $D$"*, **not** *"anyone rebuilding commit $C$ will obtain digest $D$"* and **not** *"builder $B$ itself wasn't compromised."*

#### `Chainiac`: Collectively Signed Skipchains and Verified Builds

`Chainiac` (Nikitin et al., USENIX Security 2017, ISBN `978-1-931971-40-9`, implemented for skipchains in `dedis/cothority/skipchain` @ `e0c9afbb847b070e1bda6f54561a4082b803db80`) directly addresses both single-builder compromise and unverified build non-determinism:
1. **Verified Reproducible Builds (`ReproEquiv`):** Before a release enters the authoritative software skipchain, $t$-of-$n$ independent `verifier` nodes fetch the signed source release, deterministically rebuild the binary inside isolated build sandboxes, and refuse to cosign unless their independent output digest equals the developer-submitted release digest.
2. **Collectively Signed (`CoSi`) Skipchains (`skipchain/README.md:57-146`):** Instead of a single-key log or PoW chain, each `SkipBlock` embeds `Index`, `Height` (deterministic `height(i) = 1 + height(i / BaseHeight)` when `i % BaseHeight == 0`, capped at `MaximumHeight`), `BackLinkIDs`, current BFT `Roster`, and `ForwardLink` signatures issued retroactively by the `Roster` via BLS/Schnorr collective signing (`CoSi`).
3. **O(log N) Genesis-to-Latest Verification (`skipchain/README.md:38-41`):** A client pinned only to the genesis `SkipBlockID` verifies the latest software release in $O(\log N)$ forward-link hops without trusting mirrors or downloading intermediate release payloads, eliminating split-view forks under the BFT quorum threshold.

---

### 6. Go Checksum Database (`sum.golang.org`), Verifiable Key Directories (`AKD`), and Apple KT/PCC

Basis: source + documentation + execution

#### Go Module Checksum Database (`golang/mod/sumdb`)

In `golang/mod` (`2b553c8b61bf9bfb6f7e92f5cca8ccdf153835cc`), `sumdb` closes the TOFU gap of local `go.sum` files using an append-only Merkle tile log (`sumdb/client.go` + `sumdb/tlog/tile.go`):
- **Deterministic Archive-Independent Hashing (`sumdb/dirhash/hash.go:44-135`):** `dirhash.HashZip` opens the module zip and passes virtual file streams (ignoring zip compression, timestamps, permissions, and file ordering) to `dirhash.Hash1`. `Hash1` sorts paths with `slices.Sort`, rejects any filename containing `\n` (`hash.go:49-51`), formats `"%x  %s\n"` per file (`SHA-256`), and emits `"h1:" + base64(SHA-256(summary))`. Two independently re-packed zips with identical source files always produce the identical `h1:` hash.
- **Record Format & Client Fork Proof Generation (`sumdb/client.go:209-525`):** `Client.Lookup` queries `/lookup/<escaped_path>@<escaped_vers>` (both module zip hash and `go.mod` hash share one log leaf), validates `checkRecord(id, text)` against `tlog.RecordHash(data)`, verifies `checkRecordLines` so no unexpected module versions piggyback on the record, and calls `mergeLatest` $\to$ `checkTrees` (`client.go:448-494`). If a newly observed checkpoint conflicts with the client's cached `latest` tree head, `checkTrees` constructs and prints a **self-contained cryptographic proof of misbehavior** (both inconsistent signed notes + the `tlog.ProveTree` hash trace demonstrating $H_{\text{new}}[0..N_{\text{old}}) \neq H_{\text{old}}$) and aborts via `c.ops.SecurityError` (`ErrSecurity`).
- **Offline Privacy vs. Online Lookup Trade-off:** Because `Client.Lookup` queries `/lookup/...` over HTTPS (unless matched by `GONOSUMDB`), Go `sumdb` relies on client STH caching plus `transparency-dev/witness` (`cmd/feedwitness/feeder/sumdb/sumdb_feeder.go`) rather than blind VRF queries, trading module-name privacy at fetch time for zero-setup verification.

#### Verifiable Key & Release Directories (`facebook/akd`, WhatsApp KT, Apple KT/PCC)

Key transparency and encrypted release transparency address a harder privacy constraint than binary transparency: clients must verify *every* lookup (`user_id -> public_key`) against a global append-only log **without allowing monitors or third parties to enumerate user identifiers or phone numbers**.

- **Meta `AKD` & WhatsApp KT Auditor (`facebook/akd` @ `43a60ccf7dfdd8f4b628186410e871192adaf65b`):** Implements an Auditable Zero-Knowledge Set (**AZKS**) over a Merkle Patricia Trie indexed by Verifiable Random Function (**VRF**) outputs of `(username, version)` labels with cryptographic commitments on leaf values. Clients verify `LookupProof` and `HistoryProof`, while independent auditors (`examples/src/whatsapp_kt_auditor/auditor.rs:22-75`) fetch sequential contiguous `AuditBlob`s (`epoch -> epoch + 1`) and invoke `akd::auditor::audit_verify`. Critically, `akd/src/auditor.rs:130-226` demonstrates a non-trivial verification invariant verified in regression tests (`test_auditor_rejects_prefix_collision_value_rewrite`): if an unchanged interior node's `NodeLabel` is a strict bit-prefix of a newly inserted leaf's `NodeLabel`, a careless partition step could drop the unchanged node and allow a malicious server to silently rewrite `val1 -> val2` without changing `end_hash`! `verify_consecutive_append_only` prevents this by separately reconstructing both `start_hash` (from `unchanged_nodes`) and `end_hash` (from `unchanged_nodes` union epoch-committed `inserted` leaves).
- **Apple Contact Key Verification & Private Cloud Compute (PCC):** Apple applies two complementary transparency mechanisms documented in vendor security specifications:
  1. *iMessage Contact Key Verification:* Uses a VRF-protected auditable key directory with compact consistency milestones so devices verify account key timelines and receive automated alerts if an unexpected key change enters the directory without user enumeration.
  2. *Private Cloud Compute Release Transparency:* Every OS and cryptex software bundle (canonicalized **Image4** tickets on Apple Silicon nodes; software/firmware measurements on cloud nodes) must be published to a public append-only Merkle log **before** client devices release encrypted prompts. User devices request remote attestation bundles and verify Merkle inclusion proofs **through anonymizing OHTTP/MASQUE third-party relays** so log operators cannot correlate a user's prompt timing or identity with inclusion-proof queries.

---

### 7. Reproducible Verification Micro-Probe Results

Basis: execution

A standalone Python 3 standard-library probe verified three core algorithmic invariants on `2026-11-19`: (1) `golang/mod/sumdb/dirhash.Hash1` canonical sorting and newline filename rejection; (2) RFC 9162 domain-separated Merkle inclusion verification plus $2$-of-$3$ witness checkpoint quorum rejecting a same-size ($N=5$) split-view fork; and (3) TUF/Uptane multi-role verification deterministically rejecting freeze (`timestamp.expires < now`), rollback (`snapshot.version < prev`), ECU `hardware_id` mix-and-match, and single-repository `Director` forgery when `Director` and `Image` digests diverge:

```text
dirhash_h1=h1:V3cYbTFeXkFIHX7HjIDsUFA8iUS/kc7YlClYctEkj6c= order_invariant=True newline_rejected=True
rfc9162_incl=True proof_len=3 real=True:quorum_ok(3/2) fork=False:split-view_detected_by_w1
uptane_valid=True:accept:ecuA-v2.bin@2
uptane_freeze=False:reject:timestamp_expired(freeze_defense)
uptane_rollback=False:reject:snapshot_rollback
uptane_hw_mismatch=False:reject:hardware_id_mismatch(mix_and_match_defense)
uptane_dir_forge=False:reject:director_image_digest_mismatch
```

## Boundaries

- **Known not to apply:**
  - *Log inclusion $\neq$ software safety or honesty:* Merkle inclusion (`Google FT`, `sum.golang.org`, `Rekor`) proves only public commit-time visibility; it does not prevent an authorized publisher from signing and logging vulnerable or malicious code without external reproducible-build verification (`Chainiac`) or post-publish analyzer annotations (`ft_monitor`).
  - *SLSA Build L3 $\neq$ reproducible builds:* Per `slsa-framework/slsa/spec/build-requirements.md:224-228`, Build L3 isolates build execution and prevents tenants from forging `builder.id`/`externalParameters`, yet intentionally permits tenant-supplied `subject` digests and non-deterministic toolchains.
  - *`in-toto` step command mismatch $\neq$ hard failure:* In `in-toto/in-toto/in_toto/verifylib.py:1504-1507`, `verify_all_steps_command_alignment` only emits a warning on command mismatch; security rests exclusively on step `materials`/`products` digest rules and terminating `DISALLOW *` rules.
  - *Partial-verification Secondary ECUs in Uptane:* A Secondary ECU performing only Partial Verification (`Director` `Root` + `Targets`) cannot independently reject a malicious image signed by a compromised online `Director` unless the `Primary` ECU (performing Full Verification against the offline `Image` repository) enforces cross-check consistency prior to relaying.
- **Not examined / Unsupported:**
  - *Proprietary closed-source server internals:* Apple iMessage Key Transparency and Private Cloud Compute server internals and exact wire schemas were **not examined** beyond published architectural documentation; only open-source implementations (`google/trillian-examples`, `transparency-dev/witness`, `theupdateframework/python-tuf`, `in-toto/in-toto`, `golang/mod`, `facebook/akd`, `dedis/cothority`, `lowRISC/opentitan`) were verified directly in source.
  - *Automated runtime key revocation in `in-toto`:* **Unsupported** by design (`verifylib.py:1513-1521` performs zero external keyserver/CRL/OCSP lookups; key revocation requires issuing a newly signed `Layout`).
  - *Dynamic witness network gossip latency & Sybil resistance:* Real-world deployment SLA convergence bounds across decentralized `C2SP/tlog-witness` deployments were **not examined** experimentally.

## Evidence

All primary sources and outputs were verified on `2026-11-19`:

- **GitHub Pinned Source & Specification Citations:**
  - `google/trillian-examples` @ `6931e636566371f9fa8b9e664594ab05fcacaa08`:
    - `binary_transparency/firmware/api/firmware_metadata.go:20-52` (`FirmwareMetadata`)
    - `binary_transparency/firmware/api/update_package.go:18-34` (`UpdatePackage`, `ProofBundle`)
    - `binary_transparency/firmware/api/witness.go:17-23` (`WitnessGetCheckpoint`)
    - `binary_transparency/firmware/internal/verify/bundle.go:40-149` (`BundleForUpdate`, `BundleConsistency`, `BundleForBoot`, `verifyBundle`)
    - `binary_transparency/firmware/cmd/ft_monitor/impl/ft_monitor.go:128-201` (`processEntry`, `MalwareStatement`)
    - `binary_transparency/firmware/cmd/flash_tool/impl/flash_tool.go:180-250` (`verifyUpdate`, `verifyWitness`, `verifyAnnotations` pairwise-consistency `TODO`)
  - `C2SP/C2SP` @ `d35150e795e178b7ad26cdff0ec1877bcc9e9723`:
    - `tlog-checkpoint.md:49-134`, `tlog-cosignature.md:53-160`, `tlog-witness.md:87-160`
  - `transparency-dev/witness` @ `bd0f4ab93e8ee9cf3b382d7c903e864c3701a5c5`:
    - `cmd/omniwitness/monolith.go`, `cmd/feedwitness/feeder/pixelbt/pixel_feeder.go:32-124` (`tileHeight = 1`, `FetchProof`)
  - `theupdateframework/specification` @ `e2bc7d83d0740aaae8dd7133dd4f237ce3d86b16`: `tuf-spec.md`
  - `theupdateframework/python-tuf` @ `8e8a78a113b5d691672af4549d0a7abefe92b055`:
    - `tuf/ngclient/updater.py:156-581` (`refresh`, `_load_root`, `_load_timestamp`, `_load_snapshot`, `_load_targets`, `_preorder_depth_first_walk`)
  - `uptane/uptane-standard` @ `a02f9cace9e842dbc33f2151b47620a50ccc9151`:
    - `uptane-standard.md:554-796` (`Image repository`, `Director repository`, `Inventory Database`, `Vehicle version manifest`, `ECU version report`, `verify_image`)
  - `in-toto/in-toto` @ `e352b43ad7cb8915d84c36d791aa61346152a0a3`:
    - `in_toto/verifylib.py:1190-1642` (`verify_threshold_constraints`, `in_toto_verify`), `in_toto/rulelib.py:29-120` (`unpack_rule`), `in_toto/models/layout.py`
  - `in-toto/attestation` @ `50bf01716982189898823e90586075f37cd9bb7d`:
    - `spec/v1/statement.md:9-73` (`https://in-toto.io/Statement/v1`)
  - `slsa-framework/slsa` @ `8c3161670b7a6cf7bd6d858b2332ae7eb0838b0c`:
    - `spec/build-requirements.md:30-260`, `spec/build-provenance.md:16-120` (`https://slsa.dev/provenance/v1`)
  - `dedis/cothority` @ `e0c9afbb847b070e1bda6f54561a4082b803db80`:
    - `skipchain/README.md:31-175` (`SkipBlock`, deterministic `height(i)`, `ForwardLink` O(log N) traversal)
  - `golang/mod` @ `2b553c8b61bf9bfb6f7e92f5cca8ccdf153835cc`:
    - `sumdb/dirhash/hash.go:44-135` (`Hash1`, `HashZip`), `sumdb/client.go:209-525` (`Lookup`, `checkTrees`, `checkRecord`)
  - `facebook/akd` @ `43a60ccf7dfdd8f4b628186410e871192adaf65b`:
    - `akd/src/auditor.rs:24-180` (`audit_verify`, `verify_consecutive_append_only`, `test_auditor_rejects_prefix_collision_value_rewrite`), `examples/src/whatsapp_kt_auditor/auditor.rs:22-75`
  - `lowRISC/opentitan` @ `b9e9ccd9e959071f8be21c20fa9ffc4eaa06a8f5`:
    - `sw/device/silicon_creator/lib/manifest.h:37-160` (`manifest_usage_constraints_t`, `MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL`)
- **Primary Peer-Reviewed Literature & Vendor Documentation:**
  - Justin Samuel, Nick Mathewson, Justin Cappos, Roger Dingledine, *"Survivable Key Compromise in Software Update Systems"*, ACM CCS 2010, `DOI: 10.1145/1866307.1866315`.
  - Trishank Karthik Kuppusamy et al., *"Uptane: Securing Software Updates for Automobiles"*, escar Europe 2016; *"Uptane: Security and Customizability of Software Updates for Vehicles"*, IEEE Vehicular Technology Magazine, March 2018.
  - Kirill Nikitin et al., *"CHAINIAC: Proactive Software-Update Transparency via Collectively Signed Skipchains and Verified Builds"*, 26th USENIX Security Symposium (2017), pp. 1271–1287, ISBN `978-1-931971-40-9`.
  - Santiago Torres-Arias et al., *"in-toto: Providing farm-to-table guarantees for bits and bytes"*, 28th USENIX Security Symposium (2019).
  - Apple Security Engineering & Architecture: *Private Cloud Compute: A new frontier for AI privacy in the cloud* (release transparency over Image4 tickets & OHTTP/MASQUE relays) and *iMessage Contact Key Verification* documentation.

## Revalidation

To cheaply revalidate the core compositional claims against future upstream changes without repeating the full multi-repo survey:

1. **Re-run the Self-Contained Verification Probe** (Python 3.10+ standard library only, zero external dependencies):
   ```bash
   python3 - <<'EOF'
   import base64, hashlib, hmac

   def dirhash_h1(files):
       lines = [f"{hashlib.sha256(files[k]).hexdigest()}  {k}\n".encode() for k in sorted(files)]
       return "h1:" + base64.b64encode(hashlib.sha256(b"".join(lines)).digest()).decode()

   def hash_leaf(d): return hashlib.sha256(b"\x00" + d).digest()
   def hash_children(l, r): return hashlib.sha256(b"\x01" + l + r).digest()
   def mth(leaves):
       n = len(leaves)
       if n == 1: return hash_leaf(leaves[0])
       k = 1 << (n - 1).bit_length() - 1
       return hash_children(mth(leaves[:k]), mth(leaves[k:]))

   def inc_proof(leaves, idx):
       n = len(leaves)
       if n == 1: return []
       k = 1 << (n - 1).bit_length() - 1
       return (inc_proof(leaves[:k], idx) + [mth(leaves[k:])]) if idx < k else (inc_proof(leaves[k:], idx - k) + [mth(leaves[:k])])

   def verify_inc(leaf, idx, size, proof, root):
       fn, sn, r = idx, size - 1, hash_leaf(leaf)
       for p in proof:
           if (fn & 1) or fn == sn:
               r = hash_children(p, r)
               while fn and not (fn & 1): fn >>= 1; sn >>= 1
           else:
               r = hash_children(r, p)
           fn >>= 1; sn >>= 1
       return sn == 0 and r == root

   assert dirhash_h1({"go.mod": b"module example.com/fw\n", "main.go": b"package main\n"}) == "h1:V3cYbTFeXkFIHX7HjIDsUFA8iUS/kc7YlClYctEkj6c="
   leaves = [f"fw-manifest-v{i}".encode() for i in range(5)]
   r5 = mth(leaves)
   assert verify_inc(leaves[3], 3, 5, inc_proof(leaves, 3), r5)
   print("revalidation_ok=True")
   EOF
   ```
   Expected output: `revalidation_ok=True` (exit `0`).
2. **Targeted Upstream Diff Checks:**
   - Diff `flash_tool.go` in `google/trillian-examples` around `verifyAnnotations` to verify whether pairwise consistency checks have been upgraded to enforce global transitive ordering across device, witness, and map checkpoints.
   - Check `slsa-framework/slsa` specification updates past `8c3161670b7a6cf7bd6d858b2332ae7eb0838b0c` for whether reproducible-build or hermeticity levels are reinstated as normative producer requirements.
   - Check `in-toto/in-toto` `verifylib.py` around `verify_all_steps_command_alignment` to verify whether expected-command mismatches remain advisory warnings or become strict errors.
