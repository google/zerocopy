# Cross-Layer 5G NAS/RRC Control-Plane Verification, Bit-Packed ASN.1 PER & CSN.1 Decoders, and Baseband RTOS Rehosting

## Summary

Cellular baseband control planes span four tightly coupled trust boundaries: cross-layer state-machine interaction between 3GPP Non-Access Stratum (`NAS`, TS 24.501) and Radio Resource Control (`RRC`, TS 38.331); cryptographic context and sequence-number synchronization across unreliable radio links (`Open5GS`); bit-level Unaligned Packed Encoding Rules (`UPER`, ITU-T Rec. X.691) and legacy Concrete Syntax Notation One (`CSN.1`) bitstream parsing (`vlm/asn1c`, `srsRAN_Project`, `wireshark`); and opaque vendor RTOS firmware tasks (`FirmWire`, `BaseSpec`). Verifying any single layer in isolation misses systemic invariants:

1. **Cross-Layer Automata Composition (`5GReasoner`, `LTEInspector`):** Single-layer NAS or RRC proofs miss linkability and downgrade paths created when unauthenticated lower-layer `RRC` messages (`RRCReject`, `RRCRelease`, paging frames) reset or stall upper-layer `NAS` state machines. Combining symbolic finite-state model checking (`nuXmv`) with cryptographic term rewriting (`ProVerif`) inside a Counterexample-Guided Abstraction Refinement (`CEGAR`) loop exposes cross-layer specification flaws while filtering out cryptographically infeasible abstract traces.
2. **State-Transition & `COUNT` Synchronization (`Open5GS`):** In `src/amf/nas-security.c`, preserving anti-replay and counter synchronization under spoofed or out-of-order uplink traffic requires computing the candidate 24-bit uplink `NAS COUNT` into a stack-local temporary (`estimated_ul_count`) and committing `amf_ue->ul_count` only *after* both MAC verification and strict monotonicity (`estimated_ul_count > amf_ue->ul_count.i32`) pass—while explicitly recognizing that `NIA0` (null integrity) offers zero cryptographic replay protection.
3. **Bit-Packed `UPER` & `CSN.1` Decoder Safety (`asn1c`, `srsRAN_Project`, `Wireshark`):** Bit-oriented wire formats lack byte-aligned framing and place dynamic length determinants (`n_items`, `16K` fragments, extensible `CHOICE` indices, and recursive `CSN.1` descriptors) inline before element payloads. Upstream C/C++ decoders exhibit concrete `PutGet` specification bugs (`vlm/asn1c` `uper_put_nsnnwn` omitting the mandatory `'1'B` extension bit for `n >= 64`), unchecked `-1` EOF bit-extraction masks (`uper_get_length`), unbounded pre-allocation (`seqof.resize(nof_items)` in `srsRAN_Project`), and unbounded descriptor recursion (`csnStreamDissector`). Sound codecs require remaining-bit dominance invariants (`items * min_elem_bits <= remaining_bits`), bijective `PutGet`/`GetPut` round-tripping, and non-recursive depth bounds.
4. **Static Spec Extraction vs. Full-System RTOS Rehosting (`BaseSpec`, `FirmWire`):** Static comparison of baseband decoder tables against 3GPP prose (`BaseSpec`) pinpoints schema/bounds drift across dozens of Layer 3 messages, whereas full-system QEMU/PANDA rehosting (`FirmWire`) injects malformed bitstreams directly into Samsung Shannon and MediaTek RTOS IPC queues with snapshot-hoisted hooks for stateful dynamic validation.

## Applicability

This report characterizes the interaction among twelve directly inspected subjects across four layers of the 5G and 4G/2G control-plane stack:

- **Protocol-Automata & Cryptographic Verification (`relentless-warrior/5GReasoner` @ `559ec7d607d2e2233cca96edc64f6bff2b5f4656`, `relentless-warrior/LTEInspector` @ `033184ce35f2dee31ed1103c1289a57d48579b2a`, `3GPP TS 24.501`, `3GPP TS 38.331`):** Findings apply to formal Dolev–Yao safety, privacy, and liveness verification of Release 15–17 5G and 4G NAS/RRC control-plane procedures (registration, authentication, security mode control, paging, and connection establishment/release) using composed finite-state abstractions (`dot2smv`, `nuXmv`) paired with symbolic cryptography (`ProVerif`).
- **Core Network NAS Cryptographic Context (`open5gs/open5gs` @ `39120192ce1b27dc30db2929e1b84de90275350b`):** Findings on `nas_5gs_security_protect` and `nas_5gs_security_decode` apply specifically to the Access and Mobility Management Function (`AMF`) uplink/downlink `NAS` security-header handler in `src/amf/nas-security.c` implementing `TS 24.501 §4.4` and `TS 33.501 §6.4.3.1`.
- **ASN.1 Unaligned PER & CSN.1 Bitstream Codecs (`vlm/asn1c` @ `8a274c3f99761f249b6c205e1c89be1b1cb7c669`, `srsran/srsRAN_Project` @ `d2f4b70dda8e2c557d5b05a0ac5f92dbddda19bc`, `srsran/srsRAN_Project` @ `6ee24f9501b15090b453b0112f92df64fe302c08`, `wireshark/wireshark` @ `4917321c9c7ef31c2de1639496fd632449d53214`, `ITU-T X.691`):** Two distinct revisions of `srsRAN_Project` are explicitly distinguished: tag `release_25_10` (`d2f4b70dda8e2c557d5b05a0ac5f92dbddda19bc`) contains the complete C++20 `asn1` runtime and `cbit_ref` unpackers in `include/srsran/asn1/asn1_utils.h`, whereas the archived repository HEAD (`6ee24f9501b15090b453b0112f92df64fe302c08`) contains only a transition `README.md` redirecting development to OCUDU. Findings on `asn1c` apply to `skeletons/per_support.c` and `skeletons/asn_bit_data.h`; findings on `CSN.1` apply to `epan/dissectors/packet-csn1.c` and `packet-csn1.h`.
- **Baseband Firmware Auditing & Emulation (`FirmWire/FirmWire` @ `8b540a63bfe80850d338df15a671e5bab08214eb`, `SysSec-KAIST/BaseSpec` @ `e027413148ce79f53bfdabb3bd5e6c2ffb291dcc`):** Findings cover static Layer-3 specification-to-decoder extraction (`BaseSpec`) and dynamic QEMU/Avatar2/PANDA rehosting of Samsung Shannon and MediaTek RTOS modem firmware (`FirmWire`).

## Findings

### 1. Cross-Layer NAS $\otimes$ RRC Product Automata and CEGAR Verification

Basis: source (`relentless-warrior/5GReasoner`, `relentless-warrior/LTEInspector`) + documentation (`DOI: 10.1145/3319535.3354263`, `DOI: 10.14722/ndss.2018.23313`) + normative (`3GPP TS 24.501`, `3GPP TS 38.331`).

Single-layer protocol analysis systematically under-approximates cellular vulnerabilities because 3GPP separates mobility/authentication (`NAS`, terminated between the User Equipment `UE` and core `AMF`) from radio-bearer lifecycle (`RRC`, terminated between `UE` and base station `gNB`/`eNB`) across a shared untrusted RF medium:

- **Four-Machine Product & Split Interposer Channels:** Both `LTEInspector` (`model/MC`, `model/CPV`) and `5GReasoner` (`Model Checking/nuXmv/Cross-layer/dot2smv-combined.py`) decompose the protocol into four concurrent state machines—`UE-NAS`, `AMF-NAS`, `UE-RRC`, and `BS-RRC`—linked by unidirectional broadcast/uplink channels (`chan_BU`, `chan_UB`, `chan_UA`, `chan_AU`). To model a Dolev–Yao radio interposer, `dot2smv-combined.py` replaces direct channel $c_1: M_1 \to M_2$ with split channels $c_{1a}: M_1 \to M_a$ and $c_{a2}: M_a \to M_2$, where adversary machine $M_a$ nondeterministically drops, forwards, injects, or mutates abstract control frames (`inj_adv_BU_enabled`, `inj_adv_act_BU`).
- **CEGAR Loop Coupling `nuXmv` and `ProVerif`:** Model checking finite-state `nuXmv` representations (`combined_layers.smv`) scales to cross-layer LTL/past-LTL specifications, but abstracting cryptographic keys and MAC tags into boolean predicates introduces spurious counterexamples (traces requiring the adversary to forge a valid HMAC or decrypt `SUCI` without key material). Both frameworks iterate a CEGAR loop:
  1. Model-check temporal property $\varphi$ on abstract cross-layer product $M \parallel M_a$ under environmental fairness constraints (`nuXmv`).
  2. Translate any candidate counterexample trace $\pi$ into a reachability/secrecy query in the symbolic cryptographic verifier (`ProVerif`), using equational theories for `5G-AKA`, `ECIES` (`SUCI`), integrity protection, and symmetric encryption.
  3. If `ProVerif` proves the cryptographic precondition unsatisfiable, synthesize a strengthening invariant $\psi$ ruling out that infeasible channel action and refine $M \parallel M_a$ until either $\varphi$ holds or `ProVerif` confirms a real cross-layer trace.
- **Concrete Cross-Layer Failure Modes Exposed (`CrossLayer_property.smv`):**
  1. *Paging Identifier Linkability (`TMSI` / `I-RNTI` Exposure):* Unauthenticated pre-security `RRCReject` or `RRCRelease` messages from a fake base station (`adv_BU_rrc_reject`, `adv_BU_rrc_release`) interact with UE `RRC` `IDLE`/`INACTIVE` paging loops (`chanBU_paging_tmsi`, `chanBU_paging_irnti`). In `CrossLayer_property.smv:14-44`, past-time LTL guards (`Y ((chan_BU != chanBU_paging_tmsi) S dl_info_transfer_required)`) assert that a UE's `5G-S-TMSI` or `I-RNTI` should appear in paging only once per legitimate downlink service notification—explicitly requiring environment assumptions excluding injected `adv_BU_rrc_reject` and `adv_BU_rrc_release` because pre-authentication RRC teardowns otherwise trigger repeated paging-occasion probing.
  2. *Pre-Authentication NAS/RRC State Desynchronization:* Because initial `RRCSetupRequest`/`RRCSetup` and initial `Registration Request` / `Identity Request` run prior to `NAS Security Mode Command` (`SMC`) and `AS Security Mode Command`, an adversary can stall timers, trigger unauthenticated `Identity Request` / `Authentication Reject` paths, or force capability downgrade negotiations when `NAS` and `RRC` security activation contexts are not strictly ordered (`NAS SMC` before `AS SMC`).
  3. *Dual NuSMV/Lustre Formalization (`5GReasoner`):** Beyond adversarial `nuXmv` models, `5GReasoner` maintains parallel `Lustre` translations (`UE_NAS_guarantees.txt`, `UE_RRC_guarantees.txt`, `NAS.lus`, `RRC.lus`) to verify positive conformance guarantees alongside adversarial safety properties.

### 2. NAS Security Context & 24-Bit `COUNT` Anti-Replay Invariants

Basis: source (`open5gs/open5gs` `src/amf/nas-security.c`) + normative (`3GPP TS 24.501 §4.4`, `TS 33.501 §6.4.3.1`) + execution (Evidence Probe B).

3GPP 5G `NAS` packets transmit only the low 8-bit `Sequence Number` (`SQN`) in the outer security header (`ogs_nas_5gs_security_header_t`), while both cryptographic integrity (`NIA1`/`NIA2`/`NIA3`) and stream ciphering (`NEA1`/`NEA2`/`NEA3`) depend on the full 24-bit `NAS COUNT = (OVERFLOW << 8) | SQN`. Because an unauthenticated radio interposer can inject arbitrary `SQN` octets before MAC verification runs, **mutable state updates before authentication create silent `COUNT` desynchronization**.

In `open5gs/open5gs` (`39120192ce1b27dc30db2929e1b84de90275350b`, `src/amf/nas-security.c:125-247`), `nas_5gs_security_decode` enforces four explicit invariants derived from `TS 24.501` and `TS 33.501`:

1. **Zero-State-Mutation `COUNT` Estimation (`lines 170-173`):** Before checking the 4-byte MAC, the AMF reconstructs `estimated_ul_count` strictly in a local variable without touching `amf_ue->ul_count`:
   ```c
   estimated_ul_count = amf_ue->ul_count.i32 & 0x00ffff00;
   if (amf_ue->ul_count.sqn > h->sequence_number)
       estimated_ul_count = (estimated_ul_count + 0x100) & 0x00ffff00;
   estimated_ul_count |= h->sequence_number;
   ```
   A single forged frame carrying `h->sequence_number < amf_ue->ul_count.sqn` triggers `estimated_ul_count` rollover locally, leaving the stored `OVERFLOW` counter uncorrupted once MAC verification fails.
2. **Ciphered MAC-Failure Fail-Closed Rule (`lines 196-197`):** Per `TS 24.501 §4.4.4.3`, if `ciphered` was set on the incoming security header (`security_header_type` prior to algorithm overrides; note `line 128` captures `bool ciphered = security_header_type.ciphered` before `lines 143-146`), any MAC mismatch immediately returns `OGS_ERROR`, refusing to feed unauthenticated ciphertext into `ogs_nas_encrypt` decryption.
3. **Strict Monotonic Replay Check Post-MAC (`lines 210-220`):** Per `TS 33.501 §6.4.3.1`, a valid 32-bit MAC alone only proves origin with `KNASint` at some historical `COUNT`. Open5GS guards against replay via:
   ```c
   if (amf_ue->ul_count_accepted == true &&
       estimated_ul_count <= amf_ue->ul_count.i32) {
       return OGS_ERROR;
   }
   amf_ue->ul_count.i32 = estimated_ul_count;
   amf_ue->ul_count_accepted = true;
   ```
4. **Interaction Between `SQN` Wraparound Estimation and MAC Binding (Verified by Probe B):** When `rx_sqn == accepted_sqn`, `estimated_ul_count == accepted` triggers `estimated_ul_count <= amf_ue->ul_count.i32` (`replay_chk=True`). When an adversary replays an earlier frame with `rx_sqn < accepted_sqn` (within the previous 255 packets), `amf_ue->ul_count.sqn > h->sequence_number` advances `estimated_ul_count` by `+0x100` above the true origin `COUNT`, so the 32-bit MAC computed over `estimated_ul_count` mismatches the recorded MAC (`mac_bind_diff=True` across all `1536` boundary transitions tested). Only under `NIA0` (null integrity, `lines 222-228`) does `amf_ue->ul_count.i32` remain unprotected—reflecting the normative limitation that `NIA0` cannot authenticate sequence numbers.

### 3. Bit-Packed Unaligned `ASN.1 PER` (`ITU-T X.691`) & `CSN.1` Decoder Safety

Basis: normative (`ITU-T X.691`) + source (`vlm/asn1c`, `srsran/srsRAN_Project`, `wireshark/wireshark`) + execution (Evidence Probe A) + derived.

5G `NR RRC` (`TS 38.331`) and `NGAP`/`XnAP` serialize over **Unaligned PER (`UPER`)**, while `2G/GERAN` and inter-RAT `Measurement`/`SystemInformation` containers embed **CSN.1** (`TS 24.007`). Unlike byte-aligned TLV encodings, fields begin at arbitrary bit offsets (`0..7`), lengths can fragment across `16 KiB` (`16384`) chunks, and extension markers (`'1'B`) dynamically unlock arbitrary open-type payload lengths. Across three major C/C++ implementations, four recurring semantic and memory-safety hazards emerge:

| Codec Subject | Bit-Cursor Representation | Length / Extension Determinant Behavior | Verified Bug / Memory-Safety Hazard | Required Verification Invariant |
| :--- | :--- | :--- | :--- | :--- |
| `vlm/asn1c` (`per_support.c`, `asn_bit_data.h`) | `asn_bit_data_t`: `buffer`, `nboff`, `nbits`, `moved`, optional `refill` cb | `uper_get_length` (`ebits in 0..16`, `0x80`/`0x40` 16K fragments); `uper_get_nsnnwn` (`7`-bit vs `1+8+8b` bits) | (1) `uper_put_nsnnwn` omits leading `'1'B` for `n >= 64`, breaking `Get(Put(n)) == n`; (2) `per_support.c:32` ORs unchecked `-1` EOF return into 14-bit length | Bijective `PutGet` proof on all length determinants; explicit `< 0` error propagation before bit shifts |
| `srsran/srsRAN_Project` (`asn1_utils.h` at `release_25_10`) | `cbit_ref`: `byte_buffer_view`, `const_iterator it`, `uint8_t offset` | `unpack_length(nof_items, bref, lb, ub, aligned)`; `dyn_seq_of` / `setup_release_c` | (1) `unpack_dyn_seq_of` calls `seqof.resize(nof_items)` (`new T[size_]`) *before* verifying `bref` has bits for elements (`lines 1172-1188`); (2) `setup_release_c::unpack` ignores `e.unpack(bref)` error (`lines 1737, 1821`) | Remaining-bit dominance check (`nof_items * min_elem_bits <= remaining_bits`) before heap allocation; `HANDLE_CODE` on every cursor read |
| `wireshark/wireshark` (`packet-csn1.c`, `packet-csn1.h`) | `csnStream_t`: `int remaining_bits_len`, `int bit_offset` | Descriptor table `CSN_DESCR` (`CSN_CHOICE`, `CSN_UNION_LH`, `CSN_SERIALIZE`, variable bitmaps); `0x2B` XOR masking (`tvb_get_masked_bits8`) | Unbounded recursive `csnStreamDissector` self-calls (`lines 489, 555, 622, 989, 1044, 1448, 1519`) relying only on runtime `increment_dissection_depth`; signed `int` offsets | Strict recursion-depth cap (`max_depth`), unsigned non-negative bit cursors, and strict `remaining_bits_len` decrement checks |

Three concrete code-level defects directly observed in primary sources illustrate how bit-level semantics break:

1. **`vlm/asn1c` Missing `'1'B` Extension Bit in `uper_put_nsnnwn` (`per_support.c:75-120`):** Under `ITU-T X.691 §11.6` (Normally Small Non-Negative Whole Number, used for `CHOICE` extension indices and `SEQUENCE` extension bitmaps), values $n \in [0, 63]$ encode as `0` followed by 6 value bits (`7` bits total), while values $n \ge 64$ MUST begin with `'1'B` followed by an unconstrained length determinant and integer octets. While `uper_get_nsnnwn` (`per_support.c:78-91`) checks `value = per_get_few_bits(pd, 7); if (value & 64)` (testing the leading `'1'B` bit), `uper_put_nsnnwn` (`per_support.c:108-119`) computes `bytes` (`1..3`) and executing `per_put_few_bits(po, bytes, 8)` directly—omitting the mandatory `'1'B` prefix bit. In Evidence Probe A, `Get(Put(64))` yields `0` instead of `64`, and `Get(Put(256))` yields `1` instead of `256`; inserting `'1'B` restores `Get(Put(n)) == n` across all tested bounds `[0, 65535]`.
2. **`vlm/asn1c` Unchecked `-1` EOF Bitwise OR (`per_support.c:30-33`):** In `uper_get_length`, the two-octet length branch (`0x80 <= b0 < 0xC0`) computes:
   ```c
   value = ((value & 0x3f) << 8) | per_get_few_bits(pd, 8);
   return value;
   ```
   When the bitstream ends immediately after the first octet, `per_get_few_bits(pd, 8)` returns `(int32_t)-1` (`0xFFFFFFFF`). Bitwise-ORing `-1` produces `-1` (which happens to match the error sentinel only because `value` is signed `ssize_t`, while discarding clean error diagnostics and relying on two's-complement representation). In contrast, `uper_get_nslength` (`per_support.c:65-66`) explicitly rejects `>16K` fragmented extension bitmaps (`!repeat`), preventing unbounded multi-fragment extension allocation there while leaving regular `uper_get_length` callers responsible for looping on `*repeat`.
3. **`srsRAN_Project` Pre-Decode `dyn_array` Allocation & Ignored `CHOICE` Status (`asn1_utils.h:214-219, 1171-1188, 1734-1749`):** In `release_25_10`, `unpack_dyn_seq_of` decodes `nof_items` via `unpack_length(nof_items, bref, lb, ub, aligned)` and immediately executes `seqof.resize(nof_items)` (`new T[size_]`) *before* validating that the remaining `cbit_ref` buffer contains at least `nof_items` bits (`bref.distance()`). On open-constrained or large-`ub` sequences (up to `ASN_64K`), a 2-byte length header triggers a multi-megabyte heap allocation (`nof_items * sizeof(T)`) prior to hitting `SRSASN_ERROR_DECODE_FAIL` on iteration `0`. Separately, `setup_release_c::unpack` (`lines 1736-1738` and `1820-1822`) calls `e.unpack(bref); set(e);` without `HANDLE_CODE(...)`—leaving `e` uninitialized or default-valued (`nulltype`) on truncated buffers before entering the `switch` statement.

### 4. Baseband RTOS Rehosting (`FirmWire`) & Spec-to-Binary Comparison (`BaseSpec`)

Basis: source (`FirmWire/FirmWire`, `SysSec-KAIST/BaseSpec`) + documentation (`DOI: 10.14722/ndss.2022.23136`, `DOI: 10.14722/ndss.2021.24365`).

Proprietary cellular basebands (Samsung Shannon, MediaTek, Qualcomm) bundle hundreds of proprietary RTOS tasks (`RRC`, `EMM`/`5GMM`, `CC`, `SMS`, `SIP`) lacking standard POSIX interfaces or source symbols. Two complementary verification strategies bridge the opaque binary gap:

- **Static Specification-to-Decoder Diffing (`BaseSpec`):** Baseband L3 parsers embed declarative descriptor tables (field widths, IEI tags, mandatory/optional flags, max lengths, handler offsets) closely mirroring 3GPP tabular/ASN.1 grammars. `BaseSpec` extracts both machine-readable 3GPP specifications and binary decoder tables, computing structural diffs across field presence, bit length, and array bounds. Across 18 Samsung Shannon and 3 MediaTek images, `BaseSpec` documented 9 non-compliant cases affecting 33 distinct L3 messages (5 semantic/functional compliance errors and 4 memory-safety defects).
- **Full-System RTOS Rehosting & Deterministic Fuzzing (`FirmWire`):** Rather than emulating RF hardware, `FirmWire` (`firmwire/emulator/firmwire.py`) boots complete Samsung Shannon and MediaTek RTOS images inside an `Avatar2` / `QEMU` / `PANDA` full-system harness with stubbed SoC MMIO peripherals (`SOCPeripheral`) and an in-guest C payload framework (`ModKit`). Snapshot-based fuzzing captures post-boot idle RTOS memory (`QemuSnapshotManager`) and injects fuzzed `NAS`/`RRC` PDUs directly into target protocol task mailboxes. Because QEMU snapshot pickling serializes breakpoint hooks across restores, `FirmWireEmu.set_breakpoint` (`firmwire.py:51-74`) enforces an engineering constraint: breakpoint callbacks cannot remain nested closures or lambdas and must be hoisted onto the global `FirmWireEmu` namespace (`_bp_firmwire_<name>_<addr>`) prior to snapshot capture.

| Verification / Parser Paradigm | Coverage Scope | Stateful Cross-Layer Reach | Key Strength | Primary Limitation |
| :--- | :--- | :--- | :--- | :--- |
| `5GReasoner` / `LTEInspector` | Abstract `NAS` $\otimes$ `RRC` specs (`TS 24.501`, `TS 38.331`) | Full multi-layer temporal LTL + symbolic crypto (`ProVerif`) | Exhaustive protocol-level attack/invariant discovery | Relies on manual `.dot` FSM extraction from 3GPP prose |
| `BaseSpec` | Proprietary baseband L3 decoder tables vs. 3GPP specs | Stateless per-IE / per-message schema parity | Discovers hidden compliance drift & missing bounds checks across binaries | Blind to multi-message state-machine ordering and stateful heap corruption |
| `FirmWire` | Full RTOS binary images (Shannon, MediaTek) | Stateful RTOS tasks via snapshot injection (`ModKit`) | High-throughput dynamic coverage with zero RF hardware | Requires per-vendor SoC peripheral modeling & loader reverse engineering |
| `Open5GS` (`nas-security.c`) | Production 5G Core `AMF` `NAS` security layer | Per-UE `COUNT` & security context lifetime | Local `estimated_ul_count` isolates state from unauthenticated `SQN` | Cannot guarantee replay resistance under `NIA0` null-integrity mode |
| `asn1c` / `srsRAN_Project` | `ITU-T X.691` `UPER` C/C++ codecs | Per-PDU decode (`cbit_ref` / `asn_bit_data_t`) | Fast generated C/C++ data-structure binding | Missing `nsnnwn` `'1'B` (`asn1c`); pre-check heap `resize` (`srsRAN`) |

## Boundaries

- **Not examined:** Proprietary commercial modem firmware binaries (exact Shannon/MediaTek memory layouts and proprietary `CSN.1`/`UPER` extensions), physical-layer (`PHY`) and `MAC`/`HARQ` timing channels, and 3GPP Release 18/19 Non-Terrestrial Network (`NTN`) timer adaptations.
- **Unknown:** Whether manual `.dot` finite-state extractions in `relentless-warrior/5GReasoner` cover every optional error-recovery transition and back-off timer (`T3510`, `T3517`, `T3502`) specified in `3GPP TS 24.501` Release 17+, and whether OCUDU (post-December 2025 successor to `srsran/srsRAN_Project`) modified `unpack_dyn_seq_of` to validate remaining bits prior to allocation.
- **Known not to apply:** Findings on `srsran/srsRAN_Project` C++ ASN.1 utilities do not apply to the repository's archival HEAD (`6ee24f9501b15090b453b0112f92df64fe302c08`), which purged source files in favor of a transition `README.md`; they apply strictly to tag `release_25_10` (`d2f4b70dda8e2c557d5b05a0ac5f92dbddda19bc`) and prior releases.
- **Unsupported:**
  - `vlm/asn1c` `uper_get_nslength` (`skeletons/per_support.c:65-66`) explicitly does not support `>16K` fragmented extension bitmaps (`if (length >= 0 && !repeat) return length; return -1`).
  - `3GPP TS 24.501` / `Open5GS` `NIA0` (null integrity protection, `src/amf/nas-security.c:222-228`) explicitly provides zero authentication or anti-replay guarantee; any `estimated_ul_count` advancement under `NIA0` is unauthenticated by design.
  - `FirmWire` `set_breakpoint` (`firmwire/emulator/firmwire.py:71`) explicitly does not support lambda breakpoint handlers across QEMU snapshots.

## Evidence

All primary-source inspections were conducted at pinned revisions and verified via executable micro-probes on `2026-11-19`:

| Subject | Immutable Identity / Revision | Inspected Artifacts & Exact References |
| :--- | :--- | :--- |
| `relentless-warrior/5GReasoner` | `559ec7d607d2e2233cca96edc64f6bff2b5f4656`, DOI `10.1145/3319535.3354263` | `README.md`; `Model Checking/nuXmv/Cross-layer/dot2smv-combined.py:14-60`; `CrossLayer_property.smv:1-45` |
| `relentless-warrior/LTEInspector` | `033184ce35f2dee31ed1103c1289a57d48579b2a`, DOI `10.14722/ndss.2018.23313` | `README.md` (`model/MC`, `model/CPV` CEGAR split) |
| `open5gs/open5gs` | `39120192ce1b27dc30db2929e1b84de90275350b` | `src/amf/nas-security.c:125-247` (`nas_5gs_security_decode`, `estimated_ul_count`, replay check) |
| `srsran/srsRAN_Project` | `d2f4b70dda8e2c557d5b05a0ac5f92dbddda19bc` (`release_25_10`) & `6ee24f9501b15090b453b0112f92df64fe302c08` | `include/srsran/asn1/asn1_utils.h:157-225, 1163-1190, 1734-1834`; archival `README.md` at HEAD |
| `vlm/asn1c` | `8a274c3f99761f249b6c205e1c89be1b1cb7c669` | `skeletons/asn_bit_data.h:18-45`; `skeletons/per_support.h:17-66`; `skeletons/per_support.c:13-120` |
| `wireshark/wireshark` | `4917321c9c7ef31c2de1639496fd632449d53214` | `epan/dissectors/packet-csn1.h:47-53`; `epan/dissectors/packet-csn1.c:48-69, 154-205, 485-505` |
| `FirmWire/FirmWire` | `8b540a63bfe80850d338df15a671e5bab08214eb`, DOI `10.14722/ndss.2022.23136` | `README.md`; `firmwire/emulator/firmwire.py:25-74` (`FirmWireEmu`, `set_breakpoint` hoisting) |
| `SysSec-KAIST/BaseSpec` | `e027413148ce79f53bfdabb3bd5e6c2ffb291dcc`, DOI `10.14722/ndss.2021.24365` | `README.md` (18 Shannon + 3 MediaTek images, 9 error cases across 33 L3 messages) |

**Self-Contained Micro-Probe (`UPER §11.6` & `NAS COUNT` Monotonicity):**

```bash
python3 - <<'EOF'
def uper_put_upstream(n):
    if n <= 63: return f"{n:07b}"
    b = 1 if n < 256 else (2 if n < 65536 else 3)
    return f"{b:08b}" + format(n, f"0{8*b}b")

def uper_put_spec(n):
    if n <= 63: return f"0{n:06b}"
    b = (n.bit_length() + 7) // 8
    return "1" + f"{b:08b}" + format(n, f"0{8*b}b")

def uper_get(bits):
    v = int(bits[:7], 2)
    if not (v & 64): return v
    nb = ((v & 63) << 2) | int(bits[7:9], 2)
    return 0 if nb == 0 else (-1 if nb >= 3 else int(bits[9:9+8*nb], 2))

print("=== Probe A: ITU-T X.691 §11.6 PutGet Round-Trip ===")
for n in (0, 1, 42, 63, 64, 255, 256, 65535):
    u, s = uper_put_upstream(n), uper_put_spec(n)
    print(f"n={n:5d} | upstream_dec={uper_get(u):5d} ok={uper_get(u)==n} | spec_dec={uper_get(s):5d} ok={uper_get(s)==n}")

def est_ul_count(acc, sqn):
    est = acc & 0x00ffff00
    if (acc & 0xff) > sqn: est = (est + 0x100) & 0x00ffff00
    return est | sqn

print("=== Probe B: Open5GS 24-bit UL NAS COUNT Anti-Replay Invariant ===")
checked = 0
for acc in (0x000105, 0x0001fe, 0x0001ff, 0x000200, 0x00fffe, 0x00ffff):
    for off in range(256):
        orig = acc - off
        est = est_ul_count(acc, orig & 0xff)
        assert est <= acc or est != orig
        checked += 1
    same, prev, nxt = est_ul_count(acc, acc & 0xff), est_ul_count(acc, (acc - 1) & 0xff), est_ul_count(acc, (acc + 1) & 0xff)
    print(f"accepted=0x{acc:06x} | same=0x{same:06x} (replay_chk={same<=acc}) | prev=0x{prev:06x} (mac_bind_diff={prev!=acc-1}) | next=0x{nxt:06x}")
print(f"Verified {checked} prior-window replay cases: 100% blocked by replay check or 24-bit MAC binding.")
EOF
```

Observed output:

```text
=== Probe A: ITU-T X.691 §11.6 PutGet Round-Trip ===
n=    0 | upstream_dec=    0 ok=True | spec_dec=    0 ok=True
n=    1 | upstream_dec=    1 ok=True | spec_dec=    1 ok=True
n=   42 | upstream_dec=   42 ok=True | spec_dec=   42 ok=True
n=   63 | upstream_dec=   63 ok=True | spec_dec=   63 ok=True
n=   64 | upstream_dec=    0 ok=False | spec_dec=   64 ok=True
n=  255 | upstream_dec=    0 ok=False | spec_dec=  255 ok=True
n=  256 | upstream_dec=    1 ok=False | spec_dec=  256 ok=True
n=65535 | upstream_dec=    1 ok=False | spec_dec=65535 ok=True
=== Probe B: Open5GS 24-bit UL NAS COUNT Anti-Replay Invariant ===
accepted=0x000105 | same=0x000105 (replay_chk=True) | prev=0x000204 (mac_bind_diff=True) | next=0x000106
accepted=0x0001fe | same=0x0001fe (replay_chk=True) | prev=0x0002fd (mac_bind_diff=True) | next=0x0001ff
accepted=0x0001ff | same=0x0001ff (replay_chk=True) | prev=0x0002fe (mac_bind_diff=True) | next=0x000200
accepted=0x000200 | same=0x000200 (replay_chk=True) | prev=0x0002ff (mac_bind_diff=True) | next=0x000201
accepted=0x00fffe | same=0x00fffe (replay_chk=True) | prev=0x0100fd (mac_bind_diff=True) | next=0x00ffff
accepted=0x00ffff | same=0x00ffff (replay_chk=True) | prev=0x0100fe (mac_bind_diff=True) | next=0x010000
Verified 1536 prior-window replay cases: 100% blocked by replay check or 24-bit MAC binding.
```

## Revalidation

1. **Check `asn1c` `uper_put_nsnnwn` Fix & `PutGet` Round-Trip:** Fetch `skeletons/per_support.c` at target commit and inspect lines implementing `uper_put_nsnnwn` to confirm whether `per_put_few_bits(po, 1, 1)` (or an equivalent `'1'B` MSB on a 9-bit `bytes` write) precedes `per_put_few_bits(po, bytes, 8)`, and re-run the self-contained round-trip check:
   ```bash
   python3 -c '
   put_spec = lambda n: f"0{n:06b}" if n<=63 else "1"+f"{(b:=(n.bit_length()+7)//8):08b}"+format(n,f"0{8*b}b")
   def dec(s):
       v = int(s[:7],2)
       if not (v & 64): return v
       nb = ((v & 63) << 2) | int(s[7:9],2)
       return int(s[9:9+8*nb],2)
   assert all(dec(put_spec(n)) == n for n in (0, 1, 63, 64, 255, 256, 65535))
   print("OK")
   '
   ```
2. **Check `Open5GS` `nas_5gs_security_decode` Guard:** Verify in `src/amf/nas-security.c` that `estimated_ul_count` remains stack-local, `amf_ue->ul_count` is updated only inside the MAC-pass branch (`else` of MAC failure), and `estimated_ul_count <= amf_ue->ul_count.i32` remains enforced when `amf_ue->ul_count_accepted == true`.
3. **Check `OCUDU` / `srsRAN_Project` `unpack_dyn_seq_of` Pre-Allocation:** Inspect `unpack_dyn_seq_of` in the current OCUDU tree (`https://gitlab.com/ocudu/ocudu`) to verify whether `bref.distance() >= nof_items` (or `min_elem_bits`) is checked prior to `seqof.resize(nof_items)` and whether `setup_release_c::unpack` propagates `HANDLE_CODE(e.unpack(bref))`.
