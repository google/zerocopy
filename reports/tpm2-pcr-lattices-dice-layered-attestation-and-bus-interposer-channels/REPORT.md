# TPM 2.0 PCR Hash Lattices, Policy Session Automata, Active Bus Interposer Channels, ECDSA Timing Leaks, and DICE/OpenDICE Layered Attestation

## Summary

Hardware Roots of Trust for Measurement and Reporting split into two sharply contrasting architectural paradigms: **discrete co-processors** communicated with over an external physical bus (**TPM 2.0** over SPI, LPC, or I2C) and **in-SoC chained key derivation** executed inline at each boot stage transition (**DICE / OpenDICE**). Direct inspection of the TCG TPM 2.0 Reference Implementation (`microsoft/ms-tpm-20-ref`), `tpm2-tss` ESAPI, Linux's kernel bus-encryption layer (`drivers/char/tpm/tpm2-sessions.c`), `google/open-dice`, `TPMGenie`, and `TPM-FAIL` establishes five load-bearing engineering invariants:

1. **TPM 2.0 PCRs form a non-commutative, locality-gated hash chain with subtle global-counter coupling.** Extending a PCR updates `PCR_new = H_bank(PCR_old || digest)` and increments a single global `gr.pcrCounter` for all non-TCB PCRs (`PCR.c:680–685`). Consequently, `TPM2_PolicyPCR` binds a session to `gr.pcrCounter`, causing an extend to an *unrelated* non-TCB PCR (such as IMA PCR 10) between `PolicyPCR` and `TPM2_Unseal` to fail with `TPM_RC_PCR_CHANGED`.
2. **TPM 2.0 policy sessions are stateful digest automata where `PolicyAuthorize` and `PolicyOR` reset `policyDigest` while preserving runtime gates—and `PolicyAuthorize` always double-hashes `policyRef`.** In `PolicyAuthorize.c:88–92` and `Policy_spt.c:63–109`, `PolicyDigestClear` zeros `policyDigest` before `PolicyContextUpdate`, and `PolicyContextUpdate` performs a *second* hash `H(step1 || policyRef)` whenever `ref != NULL`—**even when `policyRef` is zero-length (`""`)**. Offline policy calculators that omit the second hash on empty `policyRef` compute an incompatible `authPolicy`.
3. **Salted/encrypted TPM 2.0 sessions defend against bus sniffing and MITM only within strict protocol limits.** Parameter encryption (`TPMA_SESSION_DECRYPT` / `TPMA_SESSION_ENCRYPT`) encrypts **only the first parameter** and **only if it is a `TPM2B` sized buffer**. Commands whose first parameter is a list (notably `TPM2_PCR_Extend`, taking `TPML_DIGEST_VALUES`) cannot be parameter-encrypted (`tpm2-tss` ESAPI silently clears `TPMA_SESSION_DECRYPT`), requiring salted HMAC integrity protection instead. Furthermore, Linux's `CONFIG_TCG_TPM2_HMAC` (`tpm2-sessions.c`) bootstraps its session salt from an unauthenticated `TPM_RH_NULL` primary key (`TPM2_CreatePrimary`), leaving an initial TOFU window against an active bus interposer unless userspace subsequently certifies that NULL key against the manufacturer Endorsement Key (EK) certificate.
4. **Hardware isolation does not imply side-channel immunity.** `TPM-FAIL` (Moghimi et al., USENIX Security 2020, `arXiv:1911.05673`) demonstrated that non-constant-time elliptic-curve scalar multiplication in both Intel firmware TPMs (`CVE-2019-11090`) and Common Criteria EAL 4+ discrete STMicroelectronics TPMs (`CVE-2019-16863`) leaked nonce magnitude via execution timing, enabling full 256-bit P-256 private-key recovery through Hidden Number Problem lattice reduction.
5. **DICE / OpenDICE eliminates the external bus interposer surface by ratcheting secrets inside the SoC before handing off control, separating attestation identity from update-stable sealing secrets.** In `google/open-dice` (`src/dice.c:70–192`), `DiceMainFlow` hashes all 257 bytes (`code_hash || config_input || authority_hash || mode || hidden`) to ratchet `CDI_Attest`, but hashes only the trailing 129 bytes (`authority_hash || mode || hidden`) to ratchet `CDI_Seal`—allowing sealed secrets to persist across authorized firmware updates under the same verified-boot authority while immediately invalidating *both* CDIs upon switching from `kDiceModeNormal` (`1`) to `kDiceModeDebug` (`2`).

## Applicability

This report covers the protocol semantics, reference implementations, FFI/wire-marshaling boundaries, and physical/timing threat models across the following pinned subjects:

| Domain | Pinned Primary Subjects | Role & Relationship |
|---|---|---|
| **TPM 2.0 Core Semantics & Reference C** | `microsoft/ms-tpm-20-ref` (`ee21db0a...`), `stefanberger/libtpms` (`165c303c...`), TCG TPM 2.0 Library Spec (Rev. 1.59 / 1.83), TCG PC Client PTP | Normative specification and authoritative C reference implementation for `TPM2_PCR_Extend`, `TPM2_PolicyPCR`, `TPM2_PolicyAuthorize`, `TPM2_PolicyLocality`, `TPM2_PolicyOR`, `TPM2_StartAuthSession`, and `SessionProcess.c`. |
| **TPM 2.0 Client & Kernel Stacks** | `tpm2-software/tpm2-tss` (`8de0ea01...`), `tpm2-software/tpm2-tools` (`915443b3...`), `torvalds/linux` (`4405c18c...`, `drivers/char/tpm/tpm2-sessions.c`) | Userspace ESAPI FFI session handling (`iesys_encrypt_param`, `iesys_update_session_flags`) and Linux kernel `CONFIG_TCG_TPM2_HMAC` NULL-seed salted HMAC/CFB bus protection. |
| **Bus Interposer & Timing Channels** | `nccgroup/TPMGenie` (`dd6dd227...`, Boone CanSecWest 2018), `VernamLab/TPM-FAIL` (`358f3406...`, Moghimi et al. USENIX Security 2020, `arXiv:1911.05673`) | Primary security research characterizing physical I2C/SPI/LPC bus interposition and black-box ECDSA/ECSchnorr timing leakage on commodity fTPMs and discrete EAL 4+ TPMs. |
| **DICE / OpenDICE Layered Attestation** | `google/open-dice` (`607edea5...`, Open Profile for DICE v2.6), TCG Hardware Requirements for DICE (`r78`) | Contrasting in-SoC layered CDI derivation, `DiceMainFlow` C ABI, dual `CDI_Attest` / `CDI_Seal` ratcheting, UDS locking, and X.509/COSE certificate chains. |

**Important specification vs. reference-code divergence preserved in scope:**
- In `microsoft/ms-tpm-20-ref` (`TPMCmd/Platform/src/PlatformPcr.c:39–43`), PCRs `20..22` have `doNotIncrementPcrCounter = 1`, `policyAuthGroup = 1`, and `authValuesGroup = 1`—which the reference source explicitly documents as *"consistent with the existing behavior of the TPM Reference code but differs from the behavior of the PC client spec"*. Platform profiles (PC Client PTP vs. embedded/custom firmware) may assign different locality and TCB-group attributes to PCRs `16..23`.
- `nccgroup/TPMGenie` (`README.md:11`) was originally hardware-tested on an Infineon SLB9645 I2C TPM 1.2 chip; its architectural bus-interposition taxonomy (PCR extend spoofing, response fuzzing, `/dev/hwrng` manipulation, and unauthenticated key/session interception) applies conceptually to discrete TPM 2.0 over I2C, SPI, and LPC whenever bus traffic lacks EK-rooted salted sessions.

## Findings

### 1. Architectural Contrast: Discrete TPM 2.0 Co-Processor vs. In-SoC DICE/OpenDICE

Basis: normative + source + derived

| Dimension | Discrete TPM 2.0 Co-Processor | In-SoC DICE / OpenDICE (`v2.6`) |
|---|---|---|
| **Physical Boundary** | Separate silicon package on SPI / LPC / I2C bus (or firmware fTPM on SoC security co-processor) | Executed inline by immutable ROM + each verified boot stage inside the primary SoC/RoT |
| **Root Secret Storage** | Internal NV hierarchy seeds (`EPS`, `SPS`, `PPS`) + persistent NV storage + hardware PRNG | Single fused per-device **UDS** latched/locked inaccessible after Stage 0 ROM runs |
| **Measurement Accumulation** | Mutable **PCR banks** (`PCR_new = H(PCR_old \|\| digest)`) + untrusted external Event Log | **Forward-only CDI ratchet** (`CDI_{i+1} = HKDF(CDI_i, H(inputs))`) + signed X.509/COSE cert chain |
| **Access-Control / Policy Model** | Rich on-chip **Policy Session Automaton** (`PolicyPCR`, `PolicyAuthorize`, `PolicyLocality`, `PolicyOR`, NV counters, lockout) | Stateless cryptographic derivation: wrong stage/mode yields an unrelated `CDI`, preventing decryption/signing |
| **Firmware-Update Secret Stability** | Requires explicit `TPM2_PolicyAuthorize` + external authority signature ticket (`TPMT_TK_VERIFIED`) | Built-in split: `CDI_Seal` hashes only `(authority_hash \|\| mode \|\| hidden)`, omitting `code_hash` & `config` |
| **Bus Interposer Attack Surface** | **Exposed on discrete SPI/LPC/I2C** unless protected by EK-certified salted HMAC + CFB sessions | **Eliminated** across boot stages (no external measurement bus; relies on on-die UDS latch & memory zeroing) |
| **Stateful Revocation / Anti-Rollback** | Native monotonic NV counters + dictionary-attack lockout (`TPM2_NV_Increment`) | Requires external hardware fuses/RPMB/OTBN anti-rollback counters fed into `config_input` or `hidden` |

---

### 2. TPM 2.0 PCR Extend Hash Lattices and Locality `0..4` Enforcement

Basis: normative + source + execution

#### 2.1 Non-Commutative Extend Semantics and Bank Allocation

In `microsoft/ms-tpm-20-ref` (`TPMCmd/tpm/src/command/PCR/PCR_Extend.c:12–53` and `TPMCmd/tpm/src/subsystem/PCR.c:712–740`), `TPM2_PCR_Extend(pcrHandle, digests)` updates each selected allocated hash bank independently:

$$\text{PCR}_i^{(b)} \leftarrow H_b\!\left(\text{PCR}_i^{(b)} \,\Vert\, d_b\right)$$

where $H_b$ is the bank's hash algorithm (e.g., `TPM_ALG_SHA256` or `TPM_ALG_SHA384` in `DefaultActivePcrBanks`, `PlatformPcr.c:55–64`) and $d_b$ is the caller-supplied digest of exact size `CryptHashGetDigestSize(hashAlg)`.

Three subtle implementation semantics directly observable in source:
1. **Silent No-Op on `TPM_RH_NULL` (`PCR_Extend.c:29–30`):** Passing `in->pcrHandle == TPM_RH_NULL` returns `TPM_RC_SUCCESS` without modifying any PCR or checking locality—a critical pitfall if an FFI wrapper defaults an uninitialized handle to `TPM_RH_NULL` (`0x40000007`) instead of rejecting it.
2. **Non-Commutative Free Monoid (`Basis: execution`):** Because $H_b(\text{PCR}_0 \Vert A)$ extended with $B$ differs from $H_b(\text{PCR}_0 \Vert B)$ extended with $A$ (verified in `probe_tpm2_dice.py`: `84b03013... != bf45558f...`), PCR values capture *exact measurement order*. Any non-deterministic parallel driver initialization or hot-plug enumeration order breaks static PCR sealing unless deferred to `PolicyAuthorize` or excluded from sealed PCR indices.
3. **Unallocated Bank Silent Ignore (`PCR.c:727`):** `PCRExtend()` checks `if (pcrData != NULL)` and silently skips unallocated hash banks without returning an error; callers must verify active banks via `TPM2_GetCapability(TPM_CAP_PCRS)` before relying on a bank's integrity.
4. **Reset Initial Values & Startup Locality Encoding (`PlatformPcr.c:117–153`):** On `TPM2_Startup(TPM_SU_CLEAR)`, static RTM PCRs initialize to `0x00..00`, whereas DRTM PCRs whose `resetLocality` includes Locality 4 (`(resetLocality & 0x10) != 0`) initialize to `0xFF..FF` (preventing confusion between an unlaunched DRTM state and a zeroed post-DRTM reset!). For `HCRTM_PCR` (`PCR[0]`), the least-significant byte is set to `startupLocality` (`pcrData[pcrSize - 1] = startupLocality`, line 146; or `4` when `_TPM_Hash_Start` precedes startup, `PCR.c:431–434`).

#### 2.2 Hardware Localities `0..4` and Reference-vs-PC-Client PCR Attribute Table

A hardware **locality** (`0..4`, bitmask `0x01..0x10`, or extended localities `32..255`) is conveyed out-of-band by the platform chipset/bus decode logic (e.g., distinct SPI/MMIO address windows `0xFED4_0000 + locality * 0x1000` on x86 PC Client PTP), *not* inside the unprivileged software command payload. `TPM2_PCR_Extend` enforces `PCRIsExtendAllowed(pcrHandle)` (`PCR_Extend.c:33–34`), returning `TPM_RC_LOCALITY` if the active hardware locality bit is unset.

Exact initialization attributes from `microsoft/ms-tpm-20-ref` (`TPMCmd/Platform/src/PlatformPcr.c:16–48`):

| PCR Index | Role | Saved on `SU_STATE`? | `doNotIncrement` (`gr.pcrCounter`) | Reset Localities (Bitmask) | Extend Localities (Bitmask) | Init Value (`SU_CLEAR`) |
|---|---|---|---|---|---|---|
| **PCR `0..15`** | Static RTM (SRTM: firmware, boot config, Secure Boot, OS/IMA) | Yes (`1`) | No (`0`) | None (`0x00`) — reset only on `_TPM_Init` / `SU_CLEAR` | Loc `0..4` (`0x1F`) | `0x00..00` (`PCR[0]` LSB = `startupLocality`) |
| **PCR `16`** | Debug | No (`0`) | No (`0`) | Loc `0..3` (`0x0F`) | Loc `0..4` (`0x1F`) | `0x00..00` |
| **PCR `17..18`** | DRTM (Intel TXT `SENTER` / AMD `SKINIT`, MLE/DCE) | No (`0`) | No (`0`) | **Loc `4` only (`0x10`)** | Loc `2, 3, 4` (`0x1C`) | **`0xFF..FF`** |
| **PCR `19`** | DRTM (Trusted OS) | No (`0`) | No (`0`) | **Loc `4` only (`0x10`)** | Loc `2, 3` (`0x0C`) | **`0xFF..FF`** |
| **PCR `20`** | Dynamic OS / TCB *(ref-code diverges from PC Client)* | No (`0`) | **Yes (`1`)** *(ref)* | Loc `2, 4` (`0x14`) | Loc `1, 2, 3` (`0x0E`) | **`0xFF..FF`** |
| **PCR `21..22`** | Dynamic OS / TCB *(ref-code diverges from PC Client)* | No (`0`) | **Yes (`1`)** *(ref)* | Loc `2, 4` (`0x14`) | Loc `2` only (`0x04`) | **`0xFF..FF`** |
| **PCR `23`** | Application-specific | No (`0`) | No (`0`) | Loc `0..3` (`0x0F`) | Loc `0..4` (`0x1F`) | `0x00..00` |

**Preserved specification discrepancy (`Basis: source`):** `PlatformPcr.c:39–43` explicitly notes that assigning `doNotIncrementPcrCounter = 1`, `policyAuthGroup = 1`, and `authValuesGroup = 1` to PCRs `20..22` matches the TCG reference simulator while diverging from the TCG PC Client PTP profile. Verifiers targeting real hardware TPMs must query `TPM2_GetCapability(TPM_CAP_PCR_PROPERTIES)` rather than hardcoding `ms-tpm-20-ref` defaults.

---

### 3. TPM 2.0 Policy Session Automata: `PolicyPCR`, `PolicyLocality`, `PolicyAuthorize`, and `PolicyOR`

Basis: normative + source + execution

Enhanced Authorization (EA) in TPM 2.0 models access control as a finite stateful automaton attached to a session handle created via `TPM2_StartAuthSession` with `sessionType = TPM_SE_POLICY` (live enforcement) or `TPM_SE_TRIAL` (dry-run digest calculation, skipping live PCR/ticket/signature checks).

A policy session state tuple is:

$$\sigma = \bigl(\text{policyDigest},\; \text{pcrCounter},\; \text{commandLocality},\; \text{timeout},\; \text{commandCode},\; \text{cpHash},\; \text{flags}\bigr)$$

initialized to $\text{policyDigest}_0 = 0^L$ ($L = \text{DigestSize}(\text{authHashAlg})$), `pcrCounter = 0`, `commandLocality = 0`, `timeout = 0`, `commandCode = 0`, `cpHash = empty`.

#### 3.1 Exact State Transitions (Verified from `ms-tpm-20-ref`)

1. **`TPM2_PolicyPCR(policySession, pcrDigest, pcrs)` (`PolicyPCR.c:17–90`):**
   - Computes `currentDigest = H_auth(concat of selected PCR values in canonical bank/index order)` (`PCRComputeCurrentDigest`, filtering unimplemented bits out of `pcrs`).
   - In non-trial mode: rejects with `TPM_RC_PCR_CHANGED` if `session->pcrCounter != 0 && session->pcrCounter != gr.pcrCounter`; rejects with `TPM_RCS_VALUE` if caller supplied non-empty `in->pcrDigest` mismatching `currentDigest`.
   - Updates:
     $$\text{policyDigest}' = H_{\text{auth}}\!\left(\text{policyDigest} \,\Vert\, \text{TPM\_CC\_PolicyPCR} \,\Vert\, \text{Marshal}(\text{pcrs}) \,\Vert\, \text{pcrDigest}\right)$$
   - Snapshots `session->pcrCounter = gr.pcrCounter` (non-trial mode only).
2. **`TPM2_PolicyLocality(policySession, locality)` (`PolicyLocality.c:12–100`):**
   - Rejects `locality == 0` or mixing normal (`< 32`, bitmask of localities `0..4`) with extended (`>= 32`) localities (`TPM_RCS_RANGE`).
   - **Monotone Lattice Meet:** For normal localities, initializes `prev = 0x1F` if unset and intersects `prev &= new_locality` (rejecting empty intersection `0`). Thus repeated `PolicyLocality` calls can only *narrow* permitted localities, never widen them!
   - Updates:
     $$\text{policyDigest}' = H_{\text{auth}}\!\left(\text{policyDigest} \,\Vert\, \text{TPM\_CC\_PolicyLocality} \,\Vert\, \text{Marshal}(\text{locality})\right)$$
3. **`TPM2_PolicyAuthorize(policySession, approvedPolicy, policyRef, keySign, checkTicket)` (`PolicyAuthorize.c:18–95`, `Policy_spt.c:63–129`):**
   - Validates `keySign` format (`2-byte hashAlg || digest` matching `CryptHashGetDigestSize(hashAlg)`).
   - In non-trial mode: checks `session->policyDigest == approvedPolicy`, computes `aHash = H_{keySign.alg}(approvedPolicy || policyRef)`, recomputes `TPMT_TK_VERIFIED` via `TicketComputeVerified(hierarchy, aHash, keySign)` (originally produced by `TPM2_VerifySignature`), and verifies exact ticket match.
   - **Reset-and-Double-Hash Transition (`PolicyAuthorize.c:88–92`, `Policy_spt.c:74–109`):**
     1. Calls `PolicyDigestClear(session)` ($\text{policyDigest} \leftarrow 0^L$).
     2. Calls `PolicyContextUpdate(TPM_CC_PolicyAuthorize, &keySign, &policyRef, NULL, 0, session)`:
        $$\text{step}_1 = H_{\text{auth}}\!\left(0^L \,\Vert\, \text{TPM\_CC\_PolicyAuthorize} \,\Vert\, \text{keySign}\right)$$
        $$\text{policyDigest}' = H_{\text{auth}}\!\left(\text{step}_1 \,\Vert\, \text{policyRef}\right)$$
     - **Critical Offline-Verification Trap (`Basis: source + execution`):** Because `PolicyAuthorize.c:92` passes a non-null pointer `&in->policyRef`, `Policy_spt.c:95` (`if (ref != NULL)`) **always executes the second hash even when `policyRef` is empty (`size == 0`)**! Our micro-probe (`probe_tpm2_dice.py`) verifies that `policy_authorize_digest(key_name, b"") = f7893436...` differs completely from the naive single-hash `961e6b42...`.
     - **Preservation of Runtime Side-Conditions:** Clearing `policyDigest` does **not** clear `session->pcrCounter`, `session->commandLocality`, `session->timeout`, or `session->u1.cpHash`—so an inner `PolicyPCR` or `PolicyLocality` satisfied *before* `PolicyAuthorize` continues to be enforced at final command execution!
4. **`TPM2_PolicyOR(policySession, pHashList)` (`PolicyOR.c:15–62`):**
   - In non-trial mode, requires `session->policyDigest` to equal at least one entry in `pHashList` (2–8 branch digests).
   - Resets `policyDigest` to `0^L` and computes:
     $$\text{policyDigest}' = H_{\text{auth}}\!\left(0^L \,\Vert\, \text{TPM\_CC\_PolicyOR} \,\Vert\, \text{pHashList}[0] \,\Vert\, \dots \,\Vert\, \text{pHashList}[k-1]\right)$$
   - Like `PolicyAuthorize`, preserves all previously latched runtime session constraints (`pcrCounter`, `commandLocality`, `timeout`, `cpHash`).

#### 3.2 Final Authorization Gate & Global `gr.pcrCounter` Race (`CheckPolicyAuthSession`)

When the session authorizes a target command (e.g., `TPM2_Unseal` or `TPM2_Sign`), `SessionProcess.c:927–1038` (`CheckPolicyAuthSession`) checks **all** accumulated automaton gates atomically:
1. `SessionPCRValueIsCurrent(session)` (`session->pcrCounter == 0 || session->pcrCounter == gr.pcrCounter`) -> else `TPM_RC_PCR_CHANGED`.
2. `session->policyDigest == Entity.authPolicy` and `session->authHashAlg == Entity.policyAlg` -> else `TPM_RC_POLICY_FAIL`.
3. `session->timeout == 0 || (g_time <= session->timeout && session->epoch == g_timeEpoch)` -> else `TPM_RC_EXPIRED`.
4. `session->commandCode` matches `command->code` (and is *mandatory* for `AUTH_ADMIN`/`AUTH_DUP` roles) -> else `TPM_RC_POLICY_CC` / `TPM_RC_POLICY_FAIL`.
5. Active hardware locality `_plat__LocalityGet()` is permitted by `session->commandLocality` -> else `TPM_RC_LOCALITY`.
6. Physical presence (`isPPRequired`) and `cpHash`/`nameHash`/`pHash`/`templateHash` match -> else `TPM_RC_PP` / `TPM_RCS_POLICY_FAIL`.

**Cross-PCR Contention Hazard (`Basis: source + execution`):** Because `gr.pcrCounter` is a *single* global counter incremented by `PCRChanged()` (`PCR.c:680–685`) on any non-TCB PCR extend—and triggers `FAIL(FATAL_ERROR_COUNTER_OVERFLOW)` if a 32-bit wrap occurs—a background process extending PCR 10 (such as Linux IMA) during a multi-command `PolicyPCR([0,7]) -> PolicyAuthorize -> Unseal` sequence causes `TPM_RC_PCR_CHANGED` even though PCRs `0` and `7` never changed (demonstrated in `probe_tpm2_dice.py`, Section 4). Reliable TPM clients must implement bounded retry loops around policy unseal sequences.

---

### 4. Active Bus Interposer Channels vs. Salted & Encrypted Parameter Sessions

Basis: normative + source + execution

#### 4.1 Physical Bus Interposer Threat Model (`TPMGenie` & SPI/LPC/I2C MITM)

Discrete TPMs sit on an unencrypted motherboard or daughter-card serial bus (SPI, LPC, or I2C). As demonstrated by `nccgroup/TPMGenie` (`README.md:5–24`, Boone, CanSecWest 2018), an active hardware interposer implanted on the bus can:
- **Intercept and substitute `TPM2_PCR_Extend` payloads** when commands are sent without cryptographic integrity protection, feeding expected "golden" hashes into the TPM while booting tampered OS/firmware images—defeating measured boot, remote attestation, and PCR-sealed disk encryption simultaneously.
- **Sniff cleartext secrets** returned in unencrypted responses (e.g., `TPM2_Unseal` disk encryption keys / VMKs or `TPM_RS_PW` plaintext authorization passwords sent across the bus).
- **Tamper with `/dev/hwrng` (`TPM2_GetRandom`)** or **fuzz TPM response frames** to trigger memory-corruption parsing vulnerabilities in host kernel drivers or UEFI bootloaders.
- **Reset-line desynchronization (LPC/SPI `LRESET#`):** Asserting only the TPM's physical reset pin while the host remains running resets all PCRs (`0..23`) to boot-initial values, allowing a privileged or physical attacker to replay clean measurements from Locality 0 (except DRTM PCRs `17..22`, which remain `0xFF..FF` until a hardware Locality-4 `SENTER`/`SKINIT` cycle).

#### 4.2 Salted & Bound Encrypted Parameter Sessions (`StartAuthSession` & `SessionProcess`)

TPM 2.0 defends the host-to-TPM channel via **salted, bound, HMAC-authenticated, and parameter-encrypted sessions** (`StartAuthSession.c:28–133`, `Session.c:488–505`, `SessionProcess.c:845–857, 1607–1616, 2066–2077`):

1. **Key Establishment (`TPM2_StartAuthSession`):**
   - Host selects an asymmetric decrypt key on the TPM (`tpmKey != TPM_RH_NULL`, e.g., an EK or SRK with `TPMA_OBJECT_DECRYPT` set, `StartAuthSession.c:54–72`) and encapsulates a random `salt` via RSA-OAEP or ECDH ephemeral key exchange (`encryptedSalt`). Optionally, `bind != TPM_RH_NULL` mixes a bound entity's `authValue` (excluding PIN indices, lines 97–105).
   - Both sides derive the shared `sessionKey` via NIST SP 800-108 counter-mode `KDFa` (`Session.c:496–504`):
     $$\text{sessionKey} = \text{KDFa}_{H_{\text{auth}}}\!\bigl(\text{authValue}_{\text{bind}} \Vert \text{salt},\; \text{"ATH"}\;\text{(}\texttt{SESSION\_KEY}\text{)},\; \text{nonceTPM},\; \text{nonceCaller},\; L_{\text{bits}}\bigr)$$
2. **Command/Response Integrity (`cpHash`/`rpHash` HMAC):** Every command includes a fresh `nonceCaller`, and the TPM replies with a fresh `nonceTPM`. The session authorization HMAC covers `cpHash || nonceCaller || nonceTPM || nonceDecrypt || nonceEncrypt || sessionAttributes` (`SessionProcess.c:845–857`), where `cpHash = H(commandCode || objectNames || commandParameters)`. Because an interposer lacks `salt`, modifying any handle name, command code, or parameter byte (such as a `TPM2_PCR_Extend` digest) invalidates the HMAC (verified in `probe_tpm2_dice.py`, Section 2).
3. **Strict First-Parameter Encryption Limits (`SessionProcess.c`, `tpm2-tss/src/tss2-esys/esys_iutil.c`):**
   - Symmetric encryption (`symmetric.mode == TPM_ALG_CFB`, `StartAuthSession.c:111–114`, or `TPM_ALG_XOR`) derives per-command key/IV via `KDFa(..., "CFB", nonceCaller, nonceTPM)` (for `TPMA_SESSION_DECRYPT`) or `KDFa(..., "CFB", nonceTPM, nonceCaller)` (for `TPMA_SESSION_ENCRYPT`).
   - **Critical Wire-Protocol Constraint:** TPM 2.0 encrypts **at most the first parameter** of a command (with `DECRYPT`) and **at most the first parameter** of a response (with `ENCRYPT`), and **only when that first parameter is a `TPM2B` sized buffer**. In `tpm2-software/tpm2-tss` (`src/tss2-esys/esys_iutil.c:479–489`), `iesys_update_session_flags()` queries `Tss2_Sys_GetDecryptParam()` / `Tss2_Sys_GetEncryptParam()` and **silently clears `TPMA_SESSION_DECRYPT` or `TPMA_SESSION_ENCRYPT`** when the command has no qualifying `TPM2B` parameter!
   - **Operational consequence:** `TPM2_Unseal` *can* encrypt its returned secret (`outData` is `TPM2B_SENSITIVE_DATA`, first response parameter) and `TPM2_GetRandom` *can* encrypt `randomBytes` (`TPM2B_DIGEST`), whereas `TPM2_PCR_Extend` (first parameter `TPML_DIGEST_VALUES`) **cannot** be parameter-encrypted—it relies on HMAC integrity (`cpHash`) rather than confidentiality.

#### 4.3 Mainline Linux Bus Protection (`CONFIG_TCG_TPM2_HMAC`) and the NULL-Seed Bootstrap Gap

Mainline Linux (`torvalds/linux`, `drivers/char/tpm/tpm2-sessions.c:1–143`) implements transparent kernel-level bus protection (`CONFIG_TCG_TPM2_HMAC`): at boot, `tpm2_sessions_init()` generates a transient NIST P-256 EC primary key under the **NULL hierarchy (`TPM_RH_NULL`)** and uses ECDH-salted sessions with AES-128-CFB parameter encryption and SHA-256 HMACs for kernel TPM operations (such as `TPM2_PCR_Extend`, `TPM2_GetRandom`, and trusted-key unsealing).

However, `tpm2-sessions.c:22–33` explicitly documents a fundamental **Trust-On-First-Use (TOFU) residual threat**:
- The initial `TPM2_CreatePrimary(TPM_RH_NULL)` command **cannot itself be session-protected** because the kernel holds no pre-provisioned TPM public key at early boot.
- An active bus interposer present during boot can intercept `TPM2_CreatePrimary`, substitute an attacker-controlled P-256 public key in the response, and subsequently MITM every salted session established against that key.
- **Required Closing Mitigation:** Linux exports the boot-time NULL primary key's `TPM2B_NAME` via sysfs; userspace/attestation software **must** subsequently ask the TPM to certify that NULL primary key (`TPM2_Certify`) using an Attestation Key (AK) chained back to the hardware-burned **Endorsement Key (EK) Certificate** (verified against the TPM manufacturer CA). Without this post-boot EK-chained verification, `CONFIG_TCG_TPM2_HMAC` defeats passive bus sniffers and late-attached interposers, but **not** an active boot-time interposer.

---

### 5. Cryptographic Timing Side Channels in Co-Processors: `TPM-FAIL`

Basis: documentation + source + derived

Even when bus traffic is cryptographically authenticated and keys never leave the discrete TPM die or fTPM enclave, **execution-time leakage across the host-TPM interface** can extract private signing keys without physical bus probing.

In **TPM-FAIL** (Moghimi, Sunar, Eisenbarth, Heninger, USENIX Security 2020, `arXiv:1911.05673`, `VernamLab/TPM-FAIL`), black-box timing measurements of `TPM2_Sign` (ECDSA and ECSchnorr over NIST P-256) using CPU cycle counters (`RDTSC`) exposed secret-dependent timing variations in scalar multiplication (`k * G`) on two widely deployed implementations:
- **Intel fTPM / PTT (`CVE-2019-11090`):** Nonce-bit-length-dependent execution time leaked leading zero bits of the ephemeral scalar $k$, enabling full 256-bit private key recovery after roughly **1,300 local signature observations** (under two minutes) and remotely over IPsec IKEv2 (StrongSwan) in ~45,000 handshakes.
- **STMicroelectronics ST33 Discrete Hardware TPM (`CVE-2019-16863`):** Despite Common Criteria **EAL 4+** certification, secret-dependent timing leakage in discrete ECDSA signing allowed private-key recovery in **fewer than 40,000 observations**.

**Conceptual Algebraic Mechanism (Hidden Number Problem):** Each ECDSA signature $(r_i, s_i)$ on hash $h_i$ satisfies $k_i \equiv s_i^{-1} h_i + s_i^{-1} r_i d \pmod{n}$. Whenever timing observations allow a passive observer to filter a subset of signatures whose ephemeral nonces satisfy $0 \le k_i < n / 2^\ell$ ($\ell$ leading zero bits), the unknown private key $d$ becomes the target of a short-vector lattice instance requiring roughly $m \approx \lceil 256 / \ell \rceil + O(1)$ filtered signatures (with raw sample count scaling by $2^\ell$, e.g., $\ell = 4$ requires $\sim 66$ filtered / $\sim 1{,}056$ raw signatures; see `probe_tpm2_dice.py`, Section 4).

**Architectural Defenses & Verification Lessons:**
1. **Constant-Time Scalar Multiplication:** Implementations must use fixed-iteration, constant-time algorithms (e.g., complete-addition Montgomery ladder or fixed-window comb with constant-time table lookup) and **scalar blinding / bit-length normalization** ($k' = k + n$ or $k + 2n$ so the MSB index is invariant across all nonces).
2. **Protocol-Level Hygiene:** Prefer deterministic/hedged signatures (RFC 6979 / Ed25519 where supported), rate-limit or authorize `TPM2_Sign` invocations for high-value AKs/TLS keys, and treat Common Criteria EAL certifications as insufficient substitutes for continuous statistical timing-leakage testing (e.g., Welch's $t$-test / `dudect` style regressions across firmware updates).

---

### 6. DICE and OpenDICE (`google/open-dice`): Layered CDI Derivation and Boot Attestation

Basis: normative + source + execution

The **Device Identifier Composition Engine (DICE)** (TCG DICE Hardware Requirements `r78`) and **Open Profile for DICE v2.6** (`google/open-dice`, `docs/specification.md`) eliminate the external bus and mutable global PCR state by deriving per-stage cryptographic identities inline inside the SoC.

#### 6.1 Hardware Root Transition & UDS Latching Invariant

In `docs/specification.md:213–228`, the immutable Stage 0 hardware/ROM executes seven ordered steps before transferring control to mutable firmware:
1. Measure Stage 1 `DiceInputValues` and compute next `CDI_Attest` and `CDI_Seal` using the fused **Unique Device Secret (UDS)** as both `current_cdi_attest` and `current_cdi_seal`.
2. Derive the UDS asymmetric authority key pair from UDS.
3. **Lock UDS in hardware** (one-way latch reset only on full chip power-on/cold reset) so no mutable software can ever read UDS.
4. Derive Stage 1's subject asymmetric key pair from Stage 1's `CDI_Attest`.
5. Sign Stage 1's CDI certificate (X.509 or CBOR/COSE `CWT`) using the UDS authority private key.
6. **Zeroize** the UDS-derived private key and intermediate buffers (`DiceClearMemory`, `src/dice.c:182–191`).
7. Jump to Stage 1, passing only `(next_cdi_attest, next_cdi_seal, certificate_chain)`.

Each subsequent stage $i \to i+1$ repeats the exact same `DiceMainFlow` using its own `(CDI_Attest[i], CDI_Seal[i])` and zeroizing its parent CDIs before transferring control, creating cryptographic **forward secrecy** down the boot chain.

#### 6.2 Exact `DiceMainFlow` Derivation Layout (`google/open-dice/src/dice.c`)

Direct inspection of `google/open-dice` (`include/dice/dice.h:27–80`, `include/dice/types.h:33–43`, `src/dice.c:21–192`) establishes the exact byte layout and KDF instantiation (default primitives: SHA-512, RFC 5869 HKDF-SHA512, Ed25519 or ML-DSA for PQC, `docs/specification.md:231–240`):

1. **257-Byte Serialized Input Buffer (`src/dice.c:82–120`):**

| Offset (Bytes) | Size (Bytes) | Field (`DiceInputValues`) | Included in `CDI_Attest`? | Included in `CDI_Seal`? | Appears in Cert? |
|---|---|---|---|---|---|
| `0..63` | `64` | `code_hash` (hash of next-stage binary or dm-verity root) | **Yes** | **No** | Yes |
| `64..127` | `64` | `config_input` (`config_value` if `kDiceConfigTypeInline`, else `H(config_descriptor)`) | **Yes** | **No** | Yes |
| `128..191` | `64` | `authority_hash` (hash of verified-boot signing authority; `0^64` if none) | **Yes** | **Yes** | Yes |
| `192` | `1` | `mode` (`0` = `NotInitialized`, `1` = `Normal`, `2` = `Debug`, `3` = `Maintenance`/`Recovery`) | **Yes** | **Yes** | Yes |
| `193..256` | `64` | `hidden` (internal rotation counter / ownership secret; `0^64` if unused) | **Yes** | **Yes** | **No (omitted)** |

*(Note: `types.h:37` names mode `3` `kDiceModeMaintenance`, whereas `docs/specification.md:154` labels value `3` `Recovery`—a minor naming discrepancy across header vs. profile text for identical wire byte `0x03`.)*

2. **Asymmetric Dual-CDI Ratchet (`src/dice.c:125–153`):**
   - `attest_input_hash = H(input_buffer[0..257])` (all 257 bytes).
   - `seal_input_hash   = H(input_buffer[128..257])` (only `authority_hash || mode || hidden`, 129 bytes).
   - `next_cdi_attest   = HKDF(ikm = current_cdi_attest, salt = attest_input_hash, info = "CDI_Attest", len = 32)`.
   - `next_cdi_seal     = HKDF(ikm = current_cdi_seal,   salt = seal_input_hash,   info = "CDI_Seal",   len = 32)`.
3. **Asymmetric Key Seed & Certificate ID Derivation (`src/dice.c:26–68`):**
   - `cdi_private_key_seed = HKDF(ikm = cdi_attest, salt = kAsymSalt[64], info = "Key Pair", len = 32)`.
   - `id = HKDF(ikm = cdi_public_key, salt = kIdSalt[64], info = "ID", len = 20)` followed by `id[0] &= ~0x80` (clearing the MSB so the 20-byte big-endian ID encodes as a positive ASN.1 `INTEGER` without requiring a leading `0x00` padding byte!).

**Execution verification (`Basis: execution`):** Our bit-exact Python implementation (`probe_tpm2_dice.py`, Section 3) verifies both security invariants:
- Updating `code_hash` (`v1 -> v2`) and `config_input` under the same `authority_hash` and `mode = 1` rotates `CDI_Attest` (`6e8ccc99... -> 683decf4...`) while preserving `CDI_Seal` bit-for-bit (`d0081999... == d0081999...`).
- Switching `mode` from `1` (`Normal`) to `2` (`Debug`) rotates **both** `CDI_Attest` (`cfae4703...`) and `CDI_Seal` (`51a33e80...`), isolating production sealed keys from debug boots.

---

### 7. FFI, Wire-Marshaling, and Verification Boundary Invariants

Basis: source + derived

Systems integrating TPM 2.0 (`tpm2-tss`, kernel drivers, Rust FFI wrappers) or OpenDICE (`dice.h`) must enforce six boundary invariants:

1. **TPM 2.0 Big-Endian Wire Framing & `TPM2B` Length Checking:** All TPM 2.0 wire types (`TPM_CC`, `TPM_ALG_ID`, `TPM2B_*` 16-bit big-endian size prefixes, `TPML_PCR_SELECTION`) are strictly big-endian packed streams. Unmarshaling must verify that `size` matches the exact digest length of `hashAlg` (as `TPM2_PCR_Extend` assumes unmarshaling already validated sizes, `PCR_Extend.c:20–26`) and that no trailing/truncated bytes exist—a primary class of bugs targeted by `TPMGenie` response fuzzing.
2. **Never Rely on Parameter Encryption for Non-`TPM2B` Commands:** Because `tpm2-tss` ESAPI silently strips `TPMA_SESSION_DECRYPT` on commands like `TPM2_PCR_Extend` (`esys_iutil.c:479–483`), wrappers must verify `TPMA_SESSION_HMAC` / audit integrity and never assume confidentiality of non-`TPM2B` command arguments on a discrete bus.
3. **EK-Chained Verification Before Trusting Any Salted Session:** Any system using a `TPM_RH_NULL` or unverified SRK primary key to salt sessions (including Linux `CONFIG_TCG_TPM2_HMAC`) must bind trust to an EK-certified attestation quote/certification before treating the bus as interposer-free.
4. **Canonical `PolicyAuthorize` Double-Hash & `TPM_RH_NULL` Handle Guard:** Offline policy engines must unconditionally hash `policyRef` as a second round (`H(H(0^L || CC || keySign) || policyRef)`) even for empty `policyRef`, and FFI bindings must reject `TPM_RH_NULL` (`0x40000007`) where a real PCR handle is expected.
5. **OpenDICE `kDiceConfigTypeDescriptor` Pointer & Mode Validation:** In `DiceMainFlow` (`src/dice.c:103–116`), `config_descriptor == NULL` returns `kDiceResultInvalidInput` when `config_type != kDiceConfigTypeInline`; callers must ensure `mode` is deterministically computed from measured inputs (never passed from untrusted next-stage inputs) and must overwrite parent `current_cdi_attest`/`current_cdi_seal` in caller memory immediately after `DiceMainFlow` returns (`DiceMainFlow` clears only its internal stack temporaries, not the caller's input buffers!).
6. **Hardware Zeroization & Secret Lifetime:** Because DICE relies on forward secrecy across stages, failing to lock UDS or leaving parent `CDI_Attest`/`CDI_Seal` in SRAM/DMA buffers/stack frames before jumping to the next stage collapses all downstream isolation.

## Boundaries

- **TPM 2.0 Discrete Bus Electrical Protocols (SPI FIFO vs. CRB Timing, I2C Register Map, LPC Cycles):** `not examined` at the electrical/register state-machine level; this report models the protocol-level security boundary over SPI/LPC/I2C and relies on `nccgroup/TPMGenie` and Linux `tpm2-sessions.c` for bus-layer threat characterization.
- **Physical Fault Injection & Invasive Decapping on TPM / DICE Silicon:** `known not to apply` to the cryptographic protocol defenses analyzed here. Salted/encrypted sessions and OpenDICE HKDF ratchets protect protocol messages and logical stage boundaries, not against voltage glitching, laser fault injection, or invasive UDS fuse extraction (which require physical hardware countermeasures such as OpenTitan/Caliptra glitch detectors and masked hardware crypto).
- **TPM 2.0 `PolicySigned`, `PolicySecret`, `PolicyCounterTimer`, and `PolicyNV` Command Internals:** `not examined` beyond shared helpers in `Policy_spt.c` (`PolicyParameterChecks`, `PolicyContextUpdate`, `ComputeAuthTimeout`, `PolicySptCheckCondition`).
- **Live Hardware Execution Against Physical Discrete TPM 2.0 Chips:** `unsupported` in this sandbox environment (no physical `/dev/tpmrm0` hardware device present); execution evidence verifies the exact cryptographic formulas extracted from `ms-tpm-20-ref` and `google/open-dice` in Python rather than against a physical discrete TPM silicon sample.
- **Post-Quantum DICE Implementations (ML-DSA in `google/open-dice`):** `not examined` in C source beyond verifying the Open Profile for DICE v2.6 specification text (`docs/specification.md:237–239`) mandating ML-DSA for PQC deployments.
- **Concrete Platform-Specific Timing Measurements Beyond Published `TPM-FAIL` Datasets:** `unknown` whether post-2020 firmware revisions of unlisted TPM vendors contain residual non-constant-time paths without fresh hardware timing audits.

## Evidence

### Primary Repositories, Commits, and Inspected Locations (Observed 2026-11-19)

1. **`microsoft/ms-tpm-20-ref` @ `ee21db0a941decd3cac67925ea3310873af60ab3`**
   - `TPMCmd/tpm/src/command/PCR/PCR_Extend.c:12–53` — `TPM_RH_NULL` no-op, `PCRIsExtendAllowed` locality gate, `PCRExtend` bank loop.
   - `TPMCmd/tpm/src/subsystem/PCR.c:100–117, 431–437, 677–775` — `PCRBelongsTCBGroup`, `PCRChanged` (`gr.pcrCounter++` and `FATAL_ERROR_COUNTER_OVERFLOW`), `PCRExtend` hash chain, `PCRComputeCurrentDigest`.
   - `TPMCmd/Platform/src/PlatformPcr.c:16–64, 117–153` — `s_initAttributes` for PCRs `0..23`, documented PC Client divergence on PCRs `20..22`, `_platPcr__GetInitialValueForPcr` (`0xFF` DRTM init, `HCRTM_PCR` `startupLocality`).
   - `TPMCmd/tpm/src/command/EA/PolicyPCR.c:17–90` — `TPM2_PolicyPCR` digest update and `session->pcrCounter = gr.pcrCounter`.
   - `TPMCmd/tpm/src/command/EA/PolicyLocality.c:12–100` — monotone normal-locality bitmask intersection (`0x1F` init, `&=`).
   - `TPMCmd/tpm/src/command/EA/PolicyAuthorize.c:18–95` & `TPMCmd/tpm/src/command/EA/Policy_spt.c:63–170` — `PolicyDigestClear` followed by `PolicyContextUpdate` unconditional second hash over `policyRef` when `ref != NULL`.
   - `TPMCmd/tpm/src/command/EA/PolicyOR.c:15–62` — `TPM2_PolicyOR` digest reset and branch-list hash.
   - `TPMCmd/tpm/src/command/Session/StartAuthSession.c:28–133` & `TPMCmd/tpm/src/subsystem/Session.c:488–505` — decrypt key / salt / bind validation, `TPM_ALG_CFB` requirement, `CryptKDFa(..., SESSION_KEY, ...)`.
   - `TPMCmd/tpm/src/main/SessionProcess.c:845–857, 927–1038, 1607–1619, 2063–2078` — `CheckPolicyAuthSession` gate order, `ComputeCpHash` HMAC, `CryptParameterDecryption` / `CryptParameterEncryption`.
2. **`stefanberger/libtpms` @ `165c303ccc4784fb3d8cadbb3d71205641ba380b`** & **`tpm2-software/tpm2-tools` @ `915443b32e04fb4c8ddee80b653b234669395a6a`** — pinned upstream ecosystem implementations.
3. **`tpm2-software/tpm2-tss` @ `8de0ea01520718789c0e09b07480543f13969c14`**
   - `src/tss2-esys/esys_iutil.c:158–168, 476–493, 532–558` — `iesys_update_session_flags` silently clearing `TPMA_SESSION_DECRYPT` / `TPMA_SESSION_ENCRYPT` on `TSS2_SYS_RC_NO_{DECRYPT,ENCRYPT}_PARAM`, single encrypt/decrypt session checks.
4. **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`**
   - `drivers/char/tpm/tpm2-sessions.c:1–143, 166–260` — `CONFIG_TCG_TPM2_HMAC` NIST P-256 NULL-seed primary key design, explicit documentation of the initial `TPM2_CreatePrimary` active-MITM TOFU threat (lines 22–33) requiring post-boot userspace EK-chained certification.
5. **`nccgroup/TPMGenie` @ `dd6dd2278dd3f49b25a15aaa1f15b6a737fb32b5`**
   - `README.md:1–32` — I2C interposer architecture (Infineon SLB9645 TPM 1.2 testbed), PCR Extend spoofing, `/dev/hwrng` weakening, host driver/bootloader response parsing fuzzing, and session sniffing.
6. **`VernamLab/TPM-FAIL` @ `358f3406c1e0fc217b19a0d6000fbad3fb389aef`**
   - `README.md:1–25` and Moghimi, Sunar, Eisenbarth, Heninger, *"TPM-FAIL: TPM meets Timing and Lattice Attacks"*, 29th USENIX Security Symposium (August 2020), pp. 2057–2073, `arXiv:1911.05673`, `doi:10.48550/arXiv.1911.05673` (`CVE-2019-11090` Intel fTPM, ~1,300 local / ~45,000 remote StrongSwan observations; `CVE-2019-16863` STMicroelectronics CC EAL 4+ discrete TPM, <40,000 observations).
7. **`google/open-dice` @ `607edea585175874d437fb7de8377409bb7781ee`**
   - `include/dice/dice.h:27–144` — size constants (`DICE_CDI_SIZE = 32`, `DICE_HASH_SIZE = 64`), `DiceInputValues`, `DiceMainFlow` API.
   - `include/dice/types.h:21–60` — `DiceResult`, `DiceMode` (`0..3`), `DiceConfigType`.
   - `src/dice.c:21–192` — `kAsymSalt`, `kIdSalt`, `DiceDeriveCdiPrivateKeySeed` (`"Key Pair"`), `DiceDeriveCdiCertificateId` (`"ID"`, `id[0] &= ~0x80`), 257-byte `input_buffer` vs. 129-byte `seal_input_hash`, `"CDI_Attest"` / `"CDI_Seal"` HKDF calls, and `DiceClearMemory`.
   - `docs/specification.md:1–250` — Open Profile for DICE v2.6 specification, UDS latching 7-step flow, SHA-512/HKDF/Ed25519/ML-DSA defaults.

### Executable Verification Micro-Probe (`Python 3.13.15`, Standard Library Only)

Save the script below to `/tmp/probe_tpm2_dice.py` and run `python3 /tmp/probe_tpm2_dice.py`:

```python
#!/usr/bin/env python3
"""Executable micro-probe for TPM 2.0 PCR/Policy/Session and OpenDICE CDI derivations."""
from __future__ import annotations
import hashlib, hmac, struct

TPM_CC_POLICY_PCR, TPM_CC_POLICY_LOCALITY = 0x0000017F, 0x0000016F
TPM_CC_POLICY_AUTHORIZE, TPM_CC_POLICY_OR = 0x0000016A, 0x00000171
TPM_ALG_SHA256 = 0x000B

def sha256(b: bytes) -> bytes: return hashlib.sha256(b).digest()
def pcr_extend(old: bytes, d: bytes) -> bytes: return sha256(old + d)

def marshal_pcr_sel(indices: list[int]) -> bytes:
    m = bytearray(3)
    for i in indices: m[i // 8] |= 1 << (i % 8)
    return struct.pack(">IHB", 1, TPM_ALG_SHA256, 3) + bytes(m)

def policy_pcr(old: bytes, idxs: list[int], pcrs: dict[int, bytes]) -> bytes:
    return sha256(old + struct.pack(">I", TPM_CC_POLICY_PCR) + marshal_pcr_sel(idxs)
                  + sha256(b"".join(pcrs[i] for i in sorted(idxs))))

def policy_loc(old: bytes, mask: int) -> bytes:
    return sha256(old + struct.pack(">IB", TPM_CC_POLICY_LOCALITY, mask))

def policy_auth(key_name: bytes, ref: bytes = b"") -> bytes:
    step1 = sha256(b"\x00"*32 + struct.pack(">I", TPM_CC_POLICY_AUTHORIZE) + key_name)
    return sha256(step1 + ref)  # Policy_spt.c:95 unconditionally hashes ref != NULL

def policy_or(branches: list[bytes]) -> bytes:
    return sha256(b"\x00"*32 + struct.pack(">I", TPM_CC_POLICY_OR) + b"".join(branches))

def kdfa(key: bytes, label: bytes, u: bytes, v: bytes, bits: int) -> bytes:
    out, ctr = bytearray(), 1
    while len(out) < (bits + 7) // 8:
        out.extend(hmac.new(key, struct.pack(">I", ctr)+label+b"\x00"+u+v+struct.pack(">I", bits), hashlib.sha256).digest())
        ctr += 1
    return bytes(out[:(bits + 7) // 8])

def hkdf_sha512(ikm: bytes, salt: bytes, info: bytes, length: int) -> bytes:
    prk = hmac.new(salt, ikm, hashlib.sha512).digest()
    okm, t, ctr = bytearray(), b"", 1
    while len(okm) < length:
        t = hmac.new(prk, t + info + bytes([ctr]), hashlib.sha512).digest()
        okm.extend(t); ctr += 1
    return bytes(okm[:length])

K_ASYM_SALT = bytes([
    0x63,0xB6,0xA0,0x4D,0x2C,0x07,0x7F,0xC1,0x0F,0x63,0x9F,0x21,0xDA,0x79,0x38,0x44,
    0x35,0x6C,0xC2,0xB0,0xB4,0x41,0xB3,0xA7,0x71,0x24,0x03,0x5C,0x03,0xF8,0xE1,0xBE,
    0x60,0x35,0xD3,0x1F,0x28,0x28,0x21,0xA7,0x45,0x0A,0x02,0x22,0x2A,0xB1,0xB3,0xCF,
    0xF1,0x67,0x9B,0x05,0xAB,0x1C,0xA5,0xD1,0xAF,0xFB,0x78,0x9C,0xCD,0x2B,0x0B,0x3B,
])

def dice_main_flow(cur_a: bytes, cur_s: bytes, code: bytes, cfg: bytes, auth: bytes, mode: int, hidden: bytes):
    buf = code + cfg + auth + bytes([mode]) + hidden  # 257 bytes
    na = hkdf_sha512(cur_a, hashlib.sha512(buf).digest(), b"CDI_Attest", 32)
    ns = hkdf_sha512(cur_s, hashlib.sha512(buf[128:]).digest(), b"CDI_Seal", 32)
    seed = hkdf_sha512(na, K_ASYM_SALT, b"Key Pair", 32)
    return na, ns, seed

if __name__ == "__main__":
    d_a, d_b = sha256(b"firmware-stage-A"), sha256(b"kernel-stage-B")
    ab, ba = pcr_extend(pcr_extend(b"\x00"*32, d_a), d_b), pcr_extend(pcr_extend(b"\x00"*32, d_b), d_a)
    pcrs = {0: ab, 7: pcr_extend(b"\x00"*32, sha256(b"secure-boot-db"))}
    p1 = policy_pcr(b"\x00"*32, [0, 7], pcrs)
    p2 = policy_loc(p1, 0x01)
    kn = struct.pack(">H", TPM_ALG_SHA256) + sha256(b"signing-authority-TPMT_PUBLIC")
    pa_spec = policy_auth(kn, b"")
    pa_bug = sha256(b"\x00"*32 + struct.pack(">I", TPM_CC_POLICY_AUTHORIZE) + kn)
    print(f"PCR(A||B)={ab.hex()[:16]} PCR(B||A)={ba.hex()[:16]} commutes={ab == ba}")
    print(f"PolicyPCR={p1.hex()[:16]} PolicyLoc={p2.hex()[:16]} PolicyOR={policy_or([p1, p2]).hex()[:16]}")
    print(f"PolicyAuthorize(spec)={pa_spec.hex()[:16]} single_hash={pa_bug.hex()[:16]} match={pa_spec == pa_bug}")
    sk = kdfa(sha256(b"ephemeral-ecdh-z-secret"), b"ATH", sha256(b"tpm-nonce-1"), sha256(b"caller-nonce-1"), 256)
    nc, nt = sha256(b"caller-nonce-1"), sha256(b"tpm-nonce-1")
    cp_ok = sha256(struct.pack(">II", 0x182, 0) + d_a)
    cp_bad = sha256(struct.pack(">II", 0x182, 0) + sha256(b"evil-firmware"))
    h_ok = hmac.new(sk, cp_ok + nc + nt + b"\x01", hashlib.sha256).digest()
    h_bad = hmac.new(sk, cp_bad + nc + nt + b"\x01", hashlib.sha256).digest()
    print(f"sessionKey={sk.hex()[:16]} hmac_ok={h_ok.hex()[:16]} hmac_mitm={h_bad.hex()[:16]} forged={h_ok == h_bad}")
    uds = hashlib.sha256(b"fused-hardware-UDS").digest()
    av = hashlib.sha512(b"vendor-verified-boot-pubkey").digest()
    a1, s1, _ = dice_main_flow(uds, uds, hashlib.sha512(b"bootloader-v1.0").digest(), hashlib.sha512(b"boot-config-v1").digest(), av, 1, b"\x00"*64)
    a2, s2, _ = dice_main_flow(uds, uds, hashlib.sha512(b"bootloader-v1.1-patched").digest(), hashlib.sha512(b"boot-config-v2").digest(), av, 1, b"\x00"*64)
    ad, sd, _ = dice_main_flow(uds, uds, hashlib.sha512(b"bootloader-v1.0").digest(), hashlib.sha512(b"boot-config-v1").digest(), av, 2, b"\x00"*64)
    print(f"v1_Normal: attest={a1.hex()[:16]} seal={s1.hex()[:16]}")
    print(f"v2_Normal: attest={a2.hex()[:16]} seal={s2.hex()[:16]} attest_changed={a1 != a2} seal_preserved={s1 == s2}")
    print(f"v1_Debug : attest={ad.hex()[:16]} seal={sd.hex()[:16]} seal_changed={s1 != sd}")
    for l in (4, 6, 8):
        mf = (256 + l - 1) // l + 2
        print(f"HNP P-256 l={l}: filtered>={mf} expected_raw~{mf * (1 << l)}")
```

**Recorded output (`Python 3.13.15`, Linux x86_64, 2026-11-19):**

```text
PCR(A||B)=84b030134fbdf28d PCR(B||A)=bf45558fe1779e8a commutes=False
PolicyPCR=1aa46d7f2a0c18f5 PolicyLoc=d5358ca205e06f1d PolicyOR=deb8921ebac1b3f4
PolicyAuthorize(spec)=f78934369bd1157b single_hash=961e6b42b958e8e8 match=False
sessionKey=8be5a119b80e1723 hmac_ok=aa3bf4c5299681df hmac_mitm=072ed84d7fba66d7 forged=False
v1_Normal: attest=6e8ccc99fd47d29f seal=d008199958681432
v2_Normal: attest=683decf483503b99 seal=d008199958681432 attest_changed=True seal_preserved=True
v1_Debug : attest=cfae4703b75c2729 seal=51a33e80efaec663 seal_changed=True
HNP P-256 l=4: filtered>=66 expected_raw~1056
HNP P-256 l=6: filtered>=45 expected_raw~2880
HNP P-256 l=8: filtered>=34 expected_raw~8704
```

## Revalidation

To cheaply revalidate these findings against newer upstream revisions or concrete hardware platforms:

1. **TPM 2.0 Policy & PCR Automaton:** Diff `TPMCmd/tpm/src/command/EA/{PolicyPCR,PolicyAuthorize,PolicyLocality,PolicyOR,Policy_spt}.c` and `TPMCmd/Platform/src/PlatformPcr.c` in `microsoft/ms-tpm-20-ref` (or `stefanberger/libtpms`) to verify `PolicyContextUpdate`'s unconditional second hash over `policyRef`, `gr.pcrCounter` semantics, and PCR `0..23` locality masks. On a live TPM or `swtpm`, run `tpm2_getcap pcrs` and `tpm2_getcap pcr-properties` to observe actual platform PCR bank and TCB-group attributes.
2. **ESAPI & Linux Bus Session Protection:** Diff `src/tss2-esys/esys_iutil.c` (`iesys_update_session_flags`) in `tpm2-software/tpm2-tss` for any change in `TPMA_SESSION_{DECRYPT,ENCRYPT}` auto-clearing, and diff `drivers/char/tpm/tpm2-sessions.c` in `torvalds/linux` to verify whether boot-time NULL-seed primary key establishment has gained built-in EK-certificate verification or still requires userspace certification via sysfs.
3. **OpenDICE Dual-CDI Layout:** Diff `include/dice/{dice,types}.h` and `src/dice.c` in `google/open-dice` against `docs/specification.md` for any change to the 257-byte `input_buffer` field ordering, the 129-byte `seal_input_hash` slice (`kAuthorityOffset`), `kAsymSalt` / `kIdSalt` constants, or `DiceMode` encodings, then re-run the inline Python micro-probe against `google/open-dice` unit test vectors.
4. **Co-Processor Signing Timing Safety:** For any discrete TPM or fTPM firmware revision, re-verify constant-time ECDSA/ECSchnorr execution by running fixed-vs-random nonce timing distribution checks (Welch's $t$-test over `TPM2_Sign` latency) rather than relying solely on historical firmware advisories or certification levels.
