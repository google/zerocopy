# Intel SGX Memory Integrity Trees, DCAP TCB Recovery, IETF RATS/EAT, and Project Oak Endorsements

## Summary

Intel SGX hardware isolation partitions physical DRAM into an Enclave Page Cache (`EPC`) tracked by a trusted Enclave Page Cache Map (`EPCM`), decoupling hardware access control from untrusted OS page tables. Client SGX platforms protect EPC DRAM confidentiality, integrity, and freshness via a Memory Encryption Engine (`MEE`) combining counter-mode AES with a Bonsai Merkle tree of monotonic 56-bit counters anchored in on-die SRAM (adding ~14.3% DRAM tree storage and $O(\log N)$ tree walks per cache miss), whereas Xeon Scalable SGX scales EPC capacity to hundreds of gigabytes by replacing integrity trees with stateless physical-address-tweaked AES-XTS, sacrificing cryptographic DRAM replay protection. Across both generations, transient-execution, architectural MMIO, undervolting, and timer-stepping breaks (`Foreshadow`, `SGAxe`, `ÆPIC Leak`, `Plundervolt`, `SGX-Step`) motivated microcode patches, TCB Recovery epochs (`CPUSVN`/`ISVSVN`), and decentralized ECDSA-P256 DCAP attestation (`intel/SGXDataCenterAttestationPrimitives`). Modern confidential-computing stacks generalize hardware attestation into IETF RATS (`RFC 9334`) and Entity Attestation Token (`RFC 9711`) architectures—instantiated in `keylime/keylime` for continuous TPM 2.0 appraisal and in `project-oak/oak` for layered TCG DICE CBOR/COSE/CWT chains (`Stage0` -> Restricted Kernel -> penultimate-signed `ApplicationKeys`) backed by transparent in-toto endorsements in Rekor, C2SP witness logs, and TSA-stamped registries.

## Applicability

This report covers SGX enclave memory protection, DCAP quote generation/verification APIs, IETF RATS/EAT standardization, and downstream TPM/TEE attestation architectures across ten pinned primary sources:

| Subject | Pinned Identity | Covered Scope |
| --- | --- | --- |
| `intel/SGXDataCenterAttestationPrimitives` | `72f800e9696f382464bc8ef243311edf8bd7dc13` | ECDSA attestation key sealing blobs, `sgx_qv_verify_quote`, `tdx_qv_verify_quote` |
| `intel/linux-sgx` | `3ab6a6bdb97adc76f690c0083c618bb98992fde7` | SGX SDK runtime and architectural enclave primitives |
| `keylime/keylime` | `8df08745bf81884af841c5235d8194db98d5e22e` | TPM 2.0 `Registrar`/`Verifier`/`Agent` background-check flow (`cloud_verifier_common.py`) |
| `project-oak/oak` | `29129bbe07fcf3da96de399d4d49192bb24f3c31` | Layered DICE `Evidence`, `SignedEndorsement`, `TLogReferenceValues`, `verifier.rs` |
| IETF RATS Architecture (`RFC 9334`) | `10.17487/RFC9334` | Attester/Verifier/Relying Party roles; Passport and Background-Check topologies |
| IETF EAT (`RFC 9711`) | `10.17487/RFC9711` | CBOR/JSON attestation claim structures (`submods`, `ueid`, `measurements`) |
| Costan & Devadas (2016) | `https://eprint.iacr.org/2016/086` | SGX1/SGX2 EPCM invariants, `ENCLS`/`ENCLU` lifecycle, `EGETKEY` |
| Gueron (2016) | `https://eprint.iacr.org/2016/204` | Client MEE AES-CTR + 56-bit counter Bonsai Merkle tree geometry |
| Murdock et al. (`Plundervolt`, 2020) | `10.1109/SP40000.2020.00057` | Privileged DVFS voltage fault injection upstream of MEE writeback |
| Van Bulck et al. (`SGX-Step`, 2017) | `10.1145/3152701.3152706` | Untrusted APIC timer single-stepping across `AEX` enclave exits |

All source findings apply directly to the pinned revisions above. Protocol and hardware comparisons distinguish client MEE SGX from server Xeon Scalable AES-XTS SGX, and note where `project-oak/oak` supports `AMD_SEV_SNP` / `INTEL_TDX` rather than Ring-3 SGX enclaves.

## Findings

### 1. SGX1/SGX2 EPCM Isolation and Client MEE vs. Xeon Scalable Memory Encryption

- **EPCM orthogonality to untrusted page tables** (`Basis: documentation`): In `Costan & Devadas (IACR 2016/086)`, physical DRAM reserved at boot via Processor Reserved Memory (`PRM`) holds the Enclave Page Cache (`EPC`). Every 4 KiB EPC page carries an entry in the hardware-private Enclave Page Cache Map (`EPCM`) recording ownership (`SECS` pointer), virtual linear address, page type (`PT_SECS`, `PT_TCS`, `PT_REG`, `PT_VA`), and hardware-enforced `R/W/X` permissions. On every TLB miss or enclave memory translation, the CPU checks both the untrusted OS page table walk and the EPCM entry, preventing an adversarial OS from aliasing two enclave virtual addresses to one physical EPC page, remapping pages across enclaves, or violating `W^X` without triggering an EPCM fault (`#PF`/abort-page semantics). SGX2 extends static SGX1 page allocation with `ENCLS[EAUG]`, `ENCLS[EMODPR]`, and `ENCLS[EMODT]`, requiring the enclave itself to execute `ENCLU[EACCEPT]` so untrusted OS memory additions or permission relaxations cannot take effect without explicit enclave consent.
- **Client MEE Bonsai Merkle trees vs. Xeon Scalable AES-XTS** (`Basis: documentation + execution + derived`): Client SGX (`Skylake`–`Coffee Lake`) implements the Memory Encryption Engine (`MEE`, `Gueron IACR 2016/204`) over a `128 MiB`–`256 MiB` PRM region using AES-128-CTR seeded with per-cache-line 56-bit monotonic counters, paired with a 56-bit Carter-Wegman MAC and an 8-ary Bonsai Merkle tree (`8 × 56-bit` counters + `64-bit` MAC per 64 B tree node) rooted in on-die SRAM. Server Xeon Scalable SGX scales EPC to `512 GiB`+ by replacing MEE integrity trees with stateless AES-XTS-128 keyed per domain with physical-address tweaks:

| Memory Protection Property | Client SGX MEE (Bonsai Merkle Tree) | Xeon Scalable SGX (Stateless AES-XTS) |
| --- | --- | --- |
| Confidentiality primitive | AES-128-CTR (`PA \|\| 56-bit counter`) | AES-XTS-128 (`PA` tweak) |
| Cryptographic integrity / MAC | 56-bit Carter-Wegman MAC over `(ciphertext, counter)` | None beyond DRAM ECC / Chipkill bits |
| Anti-replay / freshness root | Monotonic counter tree rooted in on-die SRAM | None (physical-bus interposer out of threat model) |
| Evaluated tree geometry (`probe`) | `128 MiB`: `7` levels, `19,173,888 B` (`14.29%`) DRAM tree; `256 MiB`: `8` levels | `0 B` tree overhead; scales linearly to `512 GiB`+ (`MEE` at `512 GiB` would require `11` levels, `78.54 GB`) |

  Our sizing probe (`sgx_oak_probe.py`) confirms that preserving an 8-ary 64 B-node counter tree up to `512 GiB` EPC requires `11` tree levels (`~78.54 GB` of DRAM metadata plus 11 serialized cache-line reads on a cold tree miss), explaining why datacenter SGX drops DRAM integrity/replay trees in favor of AES-XTS.

### 2. Microarchitectural and Architectural SGX Isolation Breaks

| Break & Primary Source | Violated SGX Invariant | Architectural / TCB Remediation |
| --- | --- | --- |
| **Foreshadow / L1TF** (Van Bulck et al., USENIX Security 2018) | Transient out-of-order loads from L1D bypass PTE `Present`/reserved checks before EPCM abort semantics squash the value | Microcode `L1D_FLUSH` on enclave exit and `VMENTRY`; SMT disablement required for strict sibling-thread isolation |
| **SGAxe** (van Schaik et al., 2020) | L1D cache eviction leaks sealed ECDSA/EPID quoting keys from Intel's Quoting Enclave (`QE`) | Cache-eviction microcode patches (`CacheOut` mitigation) + platform-wide TCB Recovery key revocation |
| **ÆPIC Leak** (Borrello et al., USENIX Security 2022, `CVE-2022-21233`) | Architectural (non-speculative) reads of undefined xAPIC MMIO offsets expose stale superqueue/cache data, including attestation keys | Microcode patch disabling undefined APIC MMIO reads + mandatory `CPUSVN` bump |
| **Plundervolt** (Murdock et al., IEEE S&P 2020, `DOI: 10.1109/SP40000.2020.00057`) | Ring-0 `MSR 0x150` voltage undervolting induces ALU computation faults inside registers before MEE MAC sealing | Microcode mailbox lock disabling software voltage/frequency interfaces when SGX is active + `CPUSVN` bump |
| **SGX-Step** (Van Bulck et al., SysTEX 2017, `DOI: 10.1145/3152701.3152706`) | Untrusted OS APIC timer interrupts force deterministic single-instruction stepping across `AEX` exits + PTE `Accessed` page tracking | Constant-time branchless execution (`CMOV`), oblivious RAM (`ORAM`), and interrupt-rate anomaly checks inside enclaves |

Each hardware/microcode vulnerability breaks the assumption that an untrusted Ring-0 OS cannot observe or perturb CPU-internal register/cache state between enclave entry (`EENTER`/`ERESUME`) and DRAM encryption (`Basis: documentation + derived`).

### 3. EPID vs. Intel ECDSA DCAP and TCB Recovery Epochs

- **Architectural shift from EPID to DCAP** (`Basis: source + documentation`): Legacy SGX1 EPID relied on group zero-knowledge signatures verified exclusively by the Intel Attestation Service (`IAS`), creating an online single point of verification and linking datacenter deployments to Intel-hosted availability. DCAP (`intel/SGXDataCenterAttestationPrimitives`) replaces EPID with ECDSA-P256 attestation keys certified by a Provisioning Certification Key (`PCK`) issued per platform by Intel's Provisioning Certification Service (`PCS`) and cached locally (`PCCS`). In `QuoteGeneration/quote_wrapper/common/inc/ecdsa_quote.h:61-81`, `ref_plaintext_ecdsa_data_sdk_t` seals and authenticates the ECDSA attestation key alongside `cert_cpu_svn`, `cert_qe_isv_svn`, `cert_pce_info`, `qe_report`, `qe_report_cert_key_sig`, and `ecdsa_att_public_key`, separating long-lived PCK platform identity from replaceable Quoting Enclave (`QE3`) keys.
- **Trusted QvE vs. untrusted QVL boundary** (`Basis: source`): In `QuoteVerification/dcap_quoteverify/inc/sgx_dcap_quoteverify.h:111-120, 230-244`, `sgx_qv_verify_quote` (and `tdx_qv_verify_quote`) accept `p_qve_report_info`:

```c
quote3_error_t sgx_qv_verify_quote(
    const uint8_t *p_quote, uint32_t quote_size,
    const sgx_ql_qve_collateral_t *p_quote_collateral,
    const time_t expiration_check_date,
    uint32_t *p_collateral_expiration_status,
    sgx_ql_qv_result_t *p_quote_verification_result,
    sgx_ql_qe_report_info_t *p_qve_report_info,
    uint32_t supplemental_data_size, uint8_t *p_supplemental_data);
```

  As explicitly documented in `sgx_dcap_quoteverify.h:96-98`, passing `p_qve_report_info != NULL` executes verification inside Intel's signed Quote Verification Enclave (`QvE`), returning a hardware-signed `sgx_report_t` over `(nonce, verification_result)`; passing `p_qve_report_info == NULL` falls back to the host user-space `QVL` library, whose `p_quote_verification_result` is **not cryptographically authenticated** against a compromised local OS unless the verifier itself runs on an independent trusted host.
- **TCB Recovery epochs (`CPUSVN` / `ISVSVN`)** (`Basis: documentation + derived`): Hardware fuses and microcode patch levels determine a 16-byte `CPUSVN`, while `PCE_ISVSVN` and enclave `ISVSVN` track architectural and application security versions. Following any TCB Recovery event (e.g., after Foreshadow, SGAxe, or ÆPIC Leak), Intel publishes signed `TCBInfo` collateral mapping `(CPUSVN, PCE_ISVSVN)` tuples to `UpToDate`, `SWHardeningNeeded`, `ConfigurationAndSWHardeningNeeded`, `OutOfDate`, or `Revoked`. Simultaneously, `ENCLU[EGETKEY]` enforces monotonicity on hardware key derivation: an enclave executing on an older unpatched `CPUSVN` cannot derive keys sealed at a newer `CPUSVN`, preventing rollback of sealed credentials after microcode updates.

### 4. IETF RATS (`RFC 9334`), EAT (`RFC 9711`), Keylime, and Project Oak Endorsements

- **IETF RATS and EAT standardization** (`Basis: normative`): `RFC 9334` (`DOI: 10.17487/RFC9334`) partitions remote attestation into five distinct conceptual roles—**Attester** (producing signed *Evidence*), **Endorser** (signing hardware/firmware provenance *Endorsements*), **Reference Value Provider** (supplying golden *Reference Values*), **Verifier** (evaluating *Appraisal Policy for Evidence* to emit signed *Attestation Results*), and **Relying Party** (enforcing *Appraisal Policy for Attestation Results*)—supporting both **Background-Check** (Relying Party relays Evidence + nonce to Verifier) and **Passport** (Attester obtains reusable Attestation Results from Verifier first) topologies. `RFC 9711` (`DOI: 10.17487/RFC9711`) standardizes the **Entity Attestation Token (EAT)** as a CBOR Web Token (`CWT`) or JSON Web Token (`JWT`) carrying claims such as `ueid`, `oemid`, `hwmodel`, `secboot`, `dbgstat`, `measurements`, and recursive `submods` for composite TEE/TPM systems.
- **Keylime TPM 2.0 continuous background-check attestation** (`Basis: source`): `keylime/keylime` (`README.md:26-135`, `keylime/cloud_verifier_common.py:35-140`) implements an operational RATS Background-Check workflow over TPM 2.0: the **Registrar** stores TPM Endorsement Keys (`EK`) and Attestation Identity Keys (`AIK`), the **Agent** supplies TPM quotes alongside Linux IMA runtime measurement lists and UEFI measured-boot event logs (`ima_measurement_list`, `mb_measurement_list` at `cloud_verifier_common.py:57-60`), and the **Verifier** validates `hash_alg`, `enc_alg`, `sign_alg`, PCR digests, and IMA policy continuously over mTLS (`cloud_verifier_common.py:101-140`) prior to releasing encrypted payload shares (`V`).
- **Project Oak layered DICE and transparent endorsements** (`Basis: source + execution`): `project-oak/oak` (`29129bbe07fcf3da96de399d4d49192bb24f3c31`) maps RATS Evidence, Endorsements, and Reference Values across Confidential VMs (`AMD_SEV_SNP`, `INTEL_TDX`, or test `TEE_PLATFORM_NONE` in `proto/attestation/evidence.proto:38-43`):
  1. **Layered DICE Evidence (`evidence.proto:49-150`)**: `RootLayerEvidence` wraps the hardware TEE attestation report signing Layer0's SEC1 `eca_public_key`. Subsequent boot stages (`Stage0` -> `Oak Restricted Kernel` / `Oak Containers`) emit sequential CBOR/COSE/CWT `LayerEvidence` certificates (`RFC 8392`) signed by the preceding layer. Critically, `ApplicationKeys` (`evidence.proto:77-103, 120-127`) are signed by the *penultimate* layer's ECA key so raw private ECA keys never enter the untrusted application address space; the application accesses encryption/signing capabilities only via an IPC/API boundary, preventing application compromise from minting forged DICE certificates.
  2. **Transparent Endorsements (`endorsement.proto:28-242`)**: `SignedEndorsement` pairs JSON in-toto `Endorsement` statements with optional transparency proofs across three independent verification channels: `rekor_log_entry` (Sigstore Rekor Merkle inclusion), `c2sp_tlog_proof` (`C2SP tlog-proof` witness quorum), and `pes_confirmation` (Public Endorsement Service signatures optionally gated by `RFC 3161` `TimeStampToken`s in `reference_value.proto:126-195`).
  3. **Two critical verifier edge cases in source** (`Basis: source + execution`):
     - *Vacuous truth on empty `TLogReferenceValues.all`* (`proto/attestation/reference_value.proto:202-228`): `TLogReferenceValues` documents that `strategy = all` requires every populated t-log check to pass; if zero t-log verifiers are populated, `all` reduces vacuously to `skip` (confirmed by `sgx_oak_probe.py`: `OAK_TLOG_EMPTY_ALL: True`), whereas `strategy = any` fails closed (`OAK_TLOG_EMPTY_ANY: False`).
     - *COSE AAD legacy fallback* (`oak_attestation_verification/src/verifier.rs:49-73`): `verify_cose_sign1_signature` first verifies the signature using domain-separated AAD (`DICE_LAYER_ADDITIONAL_DATA`, `APPLICATION_KEYS_ADDITIONAL_DATA`, `USER_DATA_ADDITIONAL_DATA`), and falls back to empty `LEGACY_ADDITIONAL_DATA` (`b""`) when `expected_aad` fails, preserving backward compatibility while preventing strict domain separation unless callers reject legacy AAD certificates.

## Boundaries

- **Unsupported**:
  - `project-oak/oak` (`proto/attestation/evidence.proto:38-43`) defines `TeePlatform` for `AMD_SEV_SNP`, `INTEL_TDX`, and `TEE_PLATFORM_NONE`; Ring-3 Intel SGX enclaves are unsupported as a root DICE platform in the inspected Oak revision.
  - Passing `p_qve_report_info == NULL` to `sgx_qv_verify_quote` or `tdx_qv_verify_quote` (`sgx_dcap_quoteverify.h:96-98`) executes unauthenticated host-library verification and does not provide hardware-signed attestation results.
- **Known not to apply**:
  - Client SGX MEE anti-replay guarantees (56-bit Bonsai Merkle counter tree in `IACR 2016/204`) do not apply to Xeon Scalable AES-XTS SGX, which omits DRAM integrity and counter trees to scale EPC capacity (`14.29%` 8-ary DRAM metadata avoided).
  - Setting `TLogReferenceValues.strategy = all` with no `rekor`, `c2sp`, or `pes` entries configured does not enforce any transparency-log check (`reference_value.proto:209-212`, confirmed by `sgx_oak_probe.py`).
- **Not examined**:
  - Live hardware `ENCLU[EGETKEY]` execution, live PCCS collateral retrieval, and Keylime's separate `rust-keylime` agent repository.

## Evidence

- **Normative & academic specifications**:
  - IETF `RFC 9334`, *"Remote ATtestation procedureS (RATS) Architecture"* (`DOI: 10.17487/RFC9334`).
  - IETF `RFC 9711`, *"The Entity Attestation Token (EAT)"* (`DOI: 10.17487/RFC9711`).
  - Victor Costan and Srinivas Devadas, *"Intel SGX Explained"*, IACR ePrint `2016/086` (`https://eprint.iacr.org/2016/086`).
  - Shay Gueron, *"A Memory Encryption Engine Suitable for General Purpose Processors"*, IACR ePrint `2016/204` (`https://eprint.iacr.org/2016/204`).
  - Jo Van Bulck et al., *"Foreshadow: Extracting the Keys to the Intel SGX Kingdom with Transient Out-of-Order Execution"*, USENIX Security 2018.
  - Stephan van Schaik, Andrew Kwong, Daniel Genkin, Yuval Yarom, *"SGAxe: How SGX Fails in Practice"*, 2020.
  - Pietro Borrello et al., *"ÆPIC Leak: Architecturally Leaking Uninitialized Data from the Microarchitecture"*, USENIX Security 2022 (`CVE-2022-21233`).
  - Kit Murdock et al., *"Plundervolt: Software-based Fault Injection Attacks against Intel SGX"*, IEEE S&P 2020 (`DOI: 10.1109/SP40000.2020.00057`).
  - Jo Van Bulck, Frank Piessens, Raoul Strackx, *"SGX-Step: A Practical Attack Framework for Precise Enclave Execution Control"*, SysTEX 2017 (`DOI: 10.1145/3152701.3152706`).
- **Source inspection**:
  - `intel/SGXDataCenterAttestationPrimitives` @ `72f800e9696f382464bc8ef243311edf8bd7dc13`: `QuoteGeneration/quote_wrapper/common/inc/ecdsa_quote.h` (`ref_plaintext_ecdsa_data_sdk_t`, lines 61–81), `QuoteGeneration/quote_wrapper/common/inc/sgx_ql_ecdsa_quote.h` (`ECDSA256Quote`, lines 49–85), `QuoteVerification/dcap_quoteverify/inc/sgx_dcap_quoteverify.h` (`sgx_qv_verify_quote`, `tee_verify_quote_qvt`, `tdx_qv_verify_quote`, lines 96–250).
  - `keylime/keylime` @ `8df08745bf81884af841c5235d8194db98d5e22e`: `README.md` (lines 26–135), `keylime/cloud_verifier_common.py` (`process_quote_response`, lines 35–140).
  - `project-oak/oak` @ `29129bbe07fcf3da96de399d4d49192bb24f3c31`: `proto/attestation/evidence.proto` (`TeePlatform`, `RootLayerEvidence`, `LayerEvidence`, `ApplicationKeys`, `Evidence`, lines 38–150), `proto/attestation/endorsement.proto` (`SignedEndorsement`, `TransparentReleaseEndorsement`, lines 28–242), `proto/attestation/reference_value.proto` (`TLogReferenceValues`, `PesReferenceValue`, `TsaReferenceValue`, lines 113–228), `oak_attestation_verification/src/verifier.rs` (`verify_cose_sign1_signature`, lines 49–73), `oak_attestation_verification/src/lib.rs` (lines 51–109).
- **Execution probe (`2026-11-19`)**:
  - `python3 sgx_oak_probe.py` computed exact 8-ary Bonsai Merkle tree geometry (`128 MiB -> height 7, 19,173,888 B DRAM, 14.29%`, `256 MiB -> height 8, 38,347,904 B`, `512 GiB -> height 11, 78,536,544,768 B`) and evaluated `TLogReferenceValues` edge cases (`OAK_TLOG_EMPTY_ALL: True`, `OAK_TLOG_EMPTY_ANY: False`).

## Revalidation

To revalidate the DCAP API boundary and Project Oak verifier invariants on newer revisions:

1. Check `QuoteVerification/dcap_quoteverify/inc/sgx_dcap_quoteverify.h` in `intel/SGXDataCenterAttestationPrimitives` for whether `sgx_qv_verify_quote` and `tdx_qv_verify_quote` still permit `p_qve_report_info == NULL` unauthenticated host verification, and check `QuoteGeneration/quote_wrapper/common/inc/ecdsa_quote.h` for changes to `ref_plaintext_ecdsa_data_sdk_t` SVN fields.
2. Check `proto/attestation/reference_value.proto` (`TLogReferenceValues`) and `oak_attestation_verification/src/verifier.rs` (`verify_cose_sign1_signature`) in `project-oak/oak` for whether empty `all` t-log strategies or `LEGACY_ADDITIONAL_DATA` AAD fallbacks have been tightened:
```bash
python3 - <<'EOF'
import math
def mee(epc_mib):
    n = (epc_mib * 1024 * 1024) // 64
    lv = []
    nodes = math.ceil(n / 8)
    while nodes > 1:
        lv.append(nodes * 64)
        nodes = math.ceil(nodes / 8)
    lv.append(64)
    return len(lv), sum(lv[:-1])
assert mee(128) == (7, 19173888)
assert mee(256) == (8, 38347904)
print("SGX MEE tree revalidation passed")
EOF
```
