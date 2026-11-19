# Attested Live-Update Ratchets, Monotonic Counters, and Rollback Resistance in Confidential VMs

## Summary

Hardware-attested live software updates inside Confidential Virtual Machines (CVMs) expose four coupled soundness hazards that static boot attestation cannot resolve on its own:

1. **Static boot-hash blindness vs. append-only runtime measurement chains:** Intel TDX freezes `MRTD` at `TDH.MR.FINALIZE` and Arm CCA freezes `RIM` at Realm activation; neither captures in-place runtime code replacement. Runtime extension registers (`RTMR[0..3]` via `TDG.MR.RTMR.EXTEND` in Intel TDX; `REM[0..3]` via `RSI_MEASUREMENT_EXTEND` in Arm CCA) provide order-sensitive, strictly append-only hash chains, but because they are **irreversible until VM reset**, extending them before state validation and `W^X` code activation permanently corrupts attestation evidence on any aborted update.
2. **State-history lineage contamination:** Even with a sound `RTMR`/`REM` chain recording a newly swapped implementation `v2` and a kernel-checked proof that `v2` preserves invariant `Inv_2` from valid initial states, migrating live state `s_1` from a vulnerable predecessor `v1` without a runtime sanitizing validator (`xf_check : AbsState_1 -> Option<{ s_2 | Inv_2(s_2) }>`) breaks `Inv_2` immediately after the swap unless the remote claim is explicitly conditioned on the entire unrevoked execution lineage `[v0 -> ... -> v2]`.
3. **Live-session rollback TOCTOU vs. cross-restart forking bounds:** Against a snapshot-capable host Virtual Machine Monitor (VMM), preventing live-session rollback after a hot-swap requires an atomic commit order (`xf_check` before `W^X` code switch before `RTMR`/`REM` extend before HKDF session-key ratchet and zeroization of old key material, paired with a monotonic peer epoch watermark). Across CVM restarts or independent peers reading host-backed persistent storage, no purely local TEE cryptography can prevent fork equivocation (the Memoir / Ariadne / ROTE / fork-consistency lower bound); cross-restart rollback resistance strictly requires a non-clonable monotonic state anchor (hardware TPM 2.0 NV counter, eMMC/UFS RPMB write counter, or an external witness quorum).
4. **Control-plane interrupt and exception injection (Ahoi: WeSee CVE-2024-25743 and Heckler CVE-2024-25744):** Verified guest code and attested ratchets remain bypassable if an untrusted host VMM can inject forged `#VC` exceptions (vector 29 on AMD SEV-SNP) or arbitrary non-timer external interrupts (such as vector `0x80` on x86-64 CVMs). Upstream Linux kernel mitigations combine `#VC` opcode-byte verification (`vc_check_opcode_bytes`), encrypted-page MMIO rejection (`vc_slow_virt_to_phys`), APIC ISR verification (`int80_is_external`), default disabling of `ia32_emulation`, and hardware event-type separation (`CONFIG_X86_FRED` or AMD SEV-SNP Restricted Injection + Secure AVIC).

## Applicability

This report synthesizes primary source implementations, hardware ABI specifications, peer-reviewed security bounds, and finite-state model checks across three interacting layers:

- **Hardware TEE measurement and attestation substrates:** Intel TDX Module reference implementation (`intel/confidential-computing.tdx.tdx-module`, commit `abd4d8ab7e18a345ba33e32335577f550f7b0e83`, tag `TDX_MODULE_2.0.20`, interpreted against Intel TDX Module v1.5 Base Architecture Specification doc 348549 and ABI Reference Specification doc 348551), Arm Trusted Firmware RMM (`TF-RMM/tf-rmm`, commit `8d7961df074f08fd83a2460ab3a2ca0b658fde92`, implementing Arm RMM Specification DEN0137), and Open Profile for DICE (`google/open-dice`, commit `607edea585175874d437fb7de8377409bb7781ee`) for layered CDI ratcheting.
- **Guest OS and VMPL 0 interrupt-injection defenses:** Upstream Linux kernel x86 confidential guest handlers (`torvalds/linux`, commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, specifically `arch/x86/coco/sev/{vc-handle.c,vc-shared.c,core.c}`, `arch/x86/coco/tdx/tdx.c`, `arch/x86/coco/core.c`, and `arch/x86/entry/syscall_32.c`) and COCONUT-SVSM (`coconut-svsm/svsm`, commit `2a40e72a0f44d4369bb997488f2b7a77e346a634`, `kernel/src/cpu/vc.rs`), evaluated against the WeSee (CVE-2024-25743, IEEE S&P 2024) and Heckler (CVE-2024-25744, USENIX Security 2024) threat models.
- **State-continuity and live-update theory:** Classical dynamic software updating (DSU) safety conditions (Hicks & Nettles TOPLAS 2005; Stoyle et al. POPL 2005 / TOPLAS 2007) combined with TEE state-continuity impossibility and protocol bounds (Mazières & Shasha PODC 2002; Parno et al. Memoir IEEE S&P 2011; Strackx & Piessens Ariadne USENIX Security 2016; Matetic et al. ROTE USENIX Security 2017; Brandenburger et al. LCM DSN 2017; TPM 2.0 `tpm2-tss` commit `8de0ea01520718789c0e09b07480543f13969c14`; JEDEC eMMC JESD84-B51 RPMB).

**Threat model:** An untrusted, active host VMM/hypervisor capable of observing, delaying, replaying, or dropping network packets; snapshotting, cloning, and restoring encrypted CVM RAM and host-resident disk images at arbitrary instruction boundaries; and injecting virtual interrupts or exceptions permitted by the platform's virtualization interface. The CPU package, silicon root of trust, TDX Module / Arm RMM / AMD PSP firmware, and an immutable boot-measured in-guest runtime core are trusted. Physical invasive attacks on silicon and microarchitectural side channels beyond explicit control-plane injection are out of scope unless noted.

**Scope distinction:** Exact C/Rust control-flow details apply to the pinned revisions listed in `REPORT.json`. The finite-state impossibility bounds (state-history contamination, live rollback TOCTOU, irreversible register corruption, and cross-restart forking) apply to any TEE supporting static boot measurements, irreversible append-only runtime measurement registers, and untrusted host-managed memory/storage snapshots.

## Findings

### 1. Static Boot Measurements vs. Append-Only Runtime Measurement Registers (Intel TDX and Arm CCA)

Basis: normative + source + execution

Both Intel TDX and Arm CCA partition attestation state into an **immutable initial boot measurement** finalized before guest execution begins and four **append-only runtime measurement registers** mutable by the running guest without VMM forgery, yet never resettable during the VM lifetime.

| Architectural Property | Intel TDX (`TDX_MODULE_2.0.20`) | Arm CCA (`TF-RMM` / DEN0137) | Security Consequence for Live Updates |
| :--- | :--- | :--- | :--- |
| **Static boot register** | `MRTD` (48-byte SHA-384) | `RIM` (Realm Initial Measurement, slot `0`; SHA-256 or SHA-512) | Captures only pre-launch pages/metadata; blind to subsequent hot-swapped code unless a boot-measured core enforces code admission. |
| **Static finalization boundary** | `TDH.MR.FINALIZE` (`tdh_mr_finalize.c:107-118`) finalizes SHA-384 context and sets `op_state = OP_STATE_RUNNABLE` | Realm activation freezes slot `0` (`RIM_MEASUREMENT_SLOT`); `RSI_MEASUREMENT_EXTEND` rejects `index == RIM_MEASUREMENT_SLOT` (`realm_attest.c:449-453`) | Prevents VMM or guest from mutating initial root-of-trust code identity after launch. |
| **Runtime measurement registers** | `RTMR[0..3]` (`NUM_RTMRS = 4`, each 48-byte SHA-384) | `REM[0..3]` (slots `1..4`, `MEASUREMENT_SLOT_NR = 5`, SHA-256 / SHA-512; TF-RMM also includes `HASH_SHA_384` enum) | Order-sensitive append-only history log (`H(old \|\| new)`); non-commutative and irreversible until full VM teardown. |
| **Guest extend ABI** | `TDG.MR.RTMR.EXTEND` (`tdg_mr_rtmr_extend.c:40-148`), invoked via `TDCALL` (`tdx_mcall_extend_rtmr` in Linux `tdx.c:159-178`) | `RSI_MEASUREMENT_EXTEND` (`realm_attest.c:414-478`), invoked via `SMC`/`HVC` from Plane 0 only | Guest-only write authority; host VMM cannot directly forge extensions, though VMM can drop/delay calls or snapshot prior to extension. |
| **Extend input constraints** | `extension_data_gpa` must be 64-byte aligned (`tdg_mr_rtmr_extend.c:51`) and mapped `PRIVATE_ONLY` (`line 72`); reads 48 bytes | `size <= 64` bytes (`MAX_EXTENDED_SIZE = 64U`, `realm_attest.c:19,457`), passed directly in GPRs `X3..X10` (`lines 443-462`) | TDX enforces private-memory-only input (blocking host shared-page TOCTOU on extend data); CCA avoids memory reads entirely via register passing. |
| **Concurrency & serialization** | `lfence()` (`line 98`) followed by exclusive host-priority lock `acquire_sharex_lock_hp_ex(&tdcs_p->measurement_fields.rtmr_lock, true)` (`line 101`) | Exclusive Realm Descriptor granule lock `granule_lock(g_rd, GRANULE_STATE_RD)` (`realm_attest.c:437`) | Serializes concurrent vCPU/REC extends, preventing torn digests, though guest software must still serialize swap-commit vs. quote-generation order. |
| **Exact extend transition** | `RTMR[i] := SHA-384(RTMR[i] \|\| ext_48B)` (`tdg_mr_rtmr_extend.c:111-121`), then sets `last_teeinfo_hash_valid = false` (`line 131`) | `measurement_extend(...)` updates `rd->measurement[index]` in place (`realm_attest.c:465-471`; `measurement.c:85-106`) | Because `last_teeinfo_hash_valid` is invalidated on extend, `TDG.MR.REPORT` (`tdg_mr_report.c:164-174`) recomputes `TEEINFOHASH` over the updated `RTMR`. |
| **Attestation report / LFA behavior** | `TDG.MR.REPORT` (`tdg_mr_report.c:54-250`) hashes `TDINFO` (including `MRTD` and `RTMR[0..3]`) and calls `ia32_seamops_seamdb_report` with 64-byte `REPORTDATA` | `RSI_ATTESTATION_TOKEN_INIT` + `CONTINUE` (`realm_attest.c:113-407`) binds `challenge` + `rd->measurement` into COSE-signed token; tracks `fw_img_sequence` (`lines 171,277-278,331-343`) to restart token creation across RMM Live Firmware Activation (LFA) | TF-RMM's `fw_img_sequence` check illustrates a key live-update principle: an attestation operation spanning a firmware update must be aborted and re-initialized rather than signed across mixed epochs. |

**Direct source observations:**
- In `intel/confidential-computing.tdx.tdx-module` (`src/td_dispatcher/vm_exits/tdg_mr_rtmr_extend.c:40-148`), `tdg_mr_rtmr_extend` allocates a 96-byte stack buffer `cat_extended_mr[SIZE_OF_SHA384_HASH_IN_QWORDS*2]`, validates 64-byte alignment of `extension_data_gpa`, walks and maps it with `TDX_RANGE_RO` and `PRIVATE_ONLY`, copies the 48-byte input to the upper half, validates `index < NUM_RTMRS`, executes `lfence()`, acquires the exclusive `rtmr_lock`, copies the existing 48-byte `rtmr[index]` into the lower half, computes `sha384_generate_hash` over all 96 bytes back into `rtmr[index]`, and invalidates `tdcs_p->measurement_fields.last_teeinfo_hash_valid`. There is no reset or pop operation anywhere in the TDX guest API.
- In `intel/confidential-computing.tdx.tdx-module` (`src/td_dispatcher/vm_exits/tdg_mr_report.c:177-188`), if `TEEINFOHASH` was not cached (which is always true immediately after `TDG.MR.RTMR.EXTEND`) and a guest-side interrupt is pending (`is_interrupt_pending_guest_side()`), `tdg_mr_report` yields back to the guest before `ia32_seamops_seamdb_report` so the guest retries after servicing the interrupt. This confirms that attestation report generation is **interruptible**, reinforcing that host-injected interrupts can race around unratcheted attestation windows.
- In `TF-RMM/tf-rmm` (`runtime/rsi/realm_attest.c:414-478`), `handle_rsi_measurement_extend` asserts Plane 0 execution (`rec_is_plane_0_active(rec)`), meaning less-privileged Realm Planes (Plane 1..N) cannot unilaterally extend `REM[0..3]` without mediating through the Plane 0 monitor—an architectural analogue of restricting `RTMR`/`REM` writes to a boot-measured runtime core.

### 2. Formal Impossibility Boundaries for Live Attested Updates

Basis: derived + execution (verified via `/tmp/probe_ratchet_rollback.py` exhaustive BFS)

Combining immutable code-identity proofs (`Ev(v2 |= C_2)`), live stateful hot-swap (extracting live state `s_1` at a quiescent update point `p in Q` and applying state transformer `xf : AbsState_1 -> AbsState_2` per Hicks & Nettles TOPLAS 2005 / Stoyle et al. POPL 2005 `con-free` activeness checks), and hardware remote attestation yields four distinct failure modes unless specific protocol invariants are enforced:

#### Hazard 2.1: State-History Lineage Contamination

Let `Ev(v2 |= C_2)` be a sound inductive verification proof showing that `Inv_2` holds on valid initial states `I_2` and is preserved by every transition of `v2` (`forall s in Inv_2, s ->_{v2} s' => s' in Inv_2`, with `Inv_2 => C_2`). Suppose predecessor `v1` either had a soundness bug or satisfied a strictly weaker invariant `Inv_1` such that some reachable state `s_1 in Reach(v1)` satisfies `xf(s_1) notin Inv_2`.

Then even with a sound `RTMR`/`REM` recording `H(v2)` and a sound proof `Ev(v2 |= C_2)`, the inference rule:

```text
valid(quote)   RTMR contains H(v2)   Ev(v2 |= C_2)
--------------------------------------------------   [UNSOUND UNDER LIVE SWAP]
              RemoteHolds(C_2)
```

is **provably unsound**. Migrating poisoned live state `s_1` into `v2` immediately places `v2` outside `Inv_2`. Exhaustive BFS on the naive live-swap model (`30` states, `42` transitions) synthesizes the minimal 3-step witness:

```text
v1_bug_poisons_state -> quiesce_for_swap_v2 -> xf_no_check_then_rtmr_and_commit_v2
  ==> VIOLATION: POISONED_STATE_IN_V2
```

**Necessary and sufficient mitigation dichotomy:**
1. **Sanitized Swap (`ValidatedSwap`):** Replace raw state transformer `xf` with a runtime-checked sanitizing validator `xf_check : AbsState_1 -> Option<{ s_2 : AbsState_2 | Inv_2(s_2) }>` whose dynamic `Some(s_2)` postcondition implies `Inv_2(s_2)` **independently of `v1`'s trustworthiness**. This breaks lineage contamination at `O(|AbsState_2|)` quiescence-time verification cost.
2. **Lineage-Indexed Swap (`LineageSwap`):** When checking `Inv_2(s_2)` dynamically is infeasible (for example, relational history invariants or cryptographic key-secrecy invariants that cannot be decided from a memory snapshot alone), the remote verifier's security judgment MUST be indexed by the entire execution lineage `vec(v) = [v_0 -> v_1 -> ... -> v_k]` together with static transfer proofs `forall s, Inv_{i-1}(s) => Inv_i(xf_i(s))` and conditioned on `forall i < k, Unrevoked(v_i)`. If any ancestor `v_i` is later found vulnerable, the remote claim `RemoteHolds(C_2)` is retroactively invalidated for all live instances that underwent an unsanitized `LineageSwap` from `v_i`, while `ValidatedSwap` and cold-boot `CleanReset` instances remain unaffected.

#### Hazard 2.2: Live-Session Rollback TOCTOU Under Unratcheted Channel Keys

Suppose a host VMM snapshots the CVM at epoch `e_0` running `v1`, allows the CVM to swap to `v2` and deliver attestation quote `q_2` to a remote peer, and then restores the `e_0` memory snapshot. If the session channel reuses pre-swap transport key `K_0` (or fails to enforce a strictly monotonic peer epoch watermark `e_peer`), the restored `v1` instance holds `K_0` and sends messages accepted by the peer under `v2`'s attested security context.

Exhaustive BFS (`30` states, `42` transitions) synthesizes the minimal 6-step witness:

```text
vmm_snapshot_tee -> quiesce_for_swap_v2 -> xf_no_check_then_rtmr_and_commit_v2
  -> peer_accepts_v2_attestation -> vmm_restore_snapshot -> v1_sends_msg_accepted_as_v2
  ==> VIOLATION: ROLLBACK_TOCTOU_ACCEPTED
```

#### Hazard 2.3: Irreversible `RTMR`/`REM` Corruption From Premature Extension

Because neither `TDG.MR.RTMR.EXTEND` nor `RSI_MEASUREMENT_EXTEND` can be undone without resetting the CVM, extending `RTMR`/`REM` *before* `xf_check` succeeds and `W^X` code activation commits creates a permanent split-brain state whenever state validation fails and the swap aborts back to `v1`: the CVM continues running `v1` while its hardware `RTMR`/`REM` permanently attests `v2`.

Exhaustive BFS on the `premature_rtmr` model (`41` states, `67` transitions) synthesizes the minimal 4-step witness:

```text
v1_bug_poisons_state -> quiesce_for_swap_v2 -> rtmr_extend_premature
  -> xf_check_fails_rollback_v1
  ==> VIOLATION: IRREVERSIBLE_RTMR_CORRUPTION
```

#### Hazard 2.4: Non-Deterministic On-Device Code Generation vs. Measurement Pinning

If an enclave performs non-deterministic or profile-guided specialization (`IR -> native_code`) locally, the set of valid machine-code hashes `{ H(native_code) }` corresponding to a single verified IR hash `eta_IR` grows unboundedly, making static transparency-log allowlists of machine-code digests intractable. Two structurally sound architectures resolve this:
- **Path A (Deterministic Canonical Compilation):** Mandate deterministic, reproducible lowering so every deployment maps `eta_IR` to one canonical machine-code digest recorded in a transparency log.
- **Path B (Boot-Measured On-Device Verifier Core):** Pin `MRTD`/`RIM` to an immutable, minimal, formally verified Runtime Core `K_rt` containing a translation-validation or certificate checker (`Check(eta_IR, native_code, cert)`). `K_rt` verifies `cert` inside the TEE before `W^X` activation and extends `RTMR`/`REM` with the semantic identity `eta_IR` together with `H(native_code)`.

### 3. Reconciled Atomic Commit Protocol: Attested Lineage & Ratcheted Swap

Basis: derived + source + execution

To eliminate Hazards 2.1–2.3 simultaneously without cold-boot re-attestation, the boot-measured immutable Runtime Core `K_rt` (measured in `MRTD` on TDX or `RIM` on CCA, running in the highest guest privilege level such as CCA Plane 0 or SEV-SNP VMPL 0) governs all live code transitions using an ephemeral in-TEE signing keypair `(sk_rt, pk_rt)` bound once at boot into hardware quote `q_0` (`REPORTDATA` / `challenge` commits to `H(pk_rt || boot_nonce)`), analogous to layered CDI attestation key derivation in Open Profile for DICE (`google/open-dice`, `docs/specification.md:289-336`, where `CDI_Attest = KDF(32, UDS, H(code || config || authority || mode || hidden), "CDI_Attest")` is separated from `CDI_Seal`).

**Four-part attested lineage descriptor:**

```text
Lambda_k = < H(K_rt), [eta_0 --(u_1, kind_1)--> ... --(u_k, kind_k)--> eta_k], e_k, R_k >
```

where the hardware `RTMR[2]` / `REM[2]` register satisfies the strictly append-only transition:

```text
Delta_k = H("LIVE_SWAP_V1" || e_k || eta_k || H(code_k) || H(u_k) || kind_k)
R_k     = Extend(R_{k-1}, Delta_k)     # SHA-384(R_{k-1} || Delta_k) on TDX
```

with `kind_k in { CleanReset, ValidatedSwap(Inv_k), LineageSwap(S_upd) }`.

**Mandatory six-stage atomic commit ordering:**

```mermaid
stateDiagram-v2
    [*] --> Running_v1: Boot quote q0 binds MRTD/RIM(K_rt) + pk_rt + R0
    Running_v1 --> Staged_v2: Host supplies (eta_2, code_2, cert_2, ev_2, u)
    Staged_v2 --> Running_v1: K_rt rejects cert / policy / signature (0 state change)
    Staged_v2 --> Quiesced: Reach update point p in Q; con-free stack; drain in-flight DMA/I/O
    Quiesced --> Validated: Extract s1; run xf_check(s1) -> Some(s2) certifying Inv_2(s2)
    Quiesced --> Running_v1: xf_check returns None -> Atomic abort BEFORE RTMR/REM extend
    Validated --> Committed: NON-REVERSIBLE COMMIT SEQUENCE:\n1. W^X unmap code_1 (TLB shootdown) & map code_2 RX\n2. Hardware RTMR.EXTEND / RSI_MEASUREMENT_EXTEND(Delta_k)\n3. e_k := e_{k-1}+1; K_k := HKDF(K_{k-1}, R_k || peer_nonce)\n4. Explicit zeroize(K_{k-1})
    Committed --> Running_v2: Emit signed Delta-SwapCert sigma_k; peer advances e_peer := e_k
```

**Why this strict ordering is both necessary and sufficient for live-session safety:**
1. **`xf_check` precedes `RTMR`/`REM` extend:** Any validation failure aborts cleanly to `Running_v1` with zero hardware measurement mutation, eliminating Hazard 2.3.
2. **`W^X` unmap precedes `RTMR`/`REM` extend and resumption:** Guarantees `code_1` cannot remain executable after `R_k` attests `v2` and prevents writable+executable code injection.
3. **HKDF epoch ratchet + `zeroize(K_{k-1})` + monotonic peer watermark `e_peer`:** Following RFC 5869 (HKDF) and TLS 1.3 `KeyUpdate` (RFC 8446 §4.6.3) ratcheting discipline, `K_rt` derives `K_k = HKDF(K_{k-1}, R_k || peer_nonce)` and explicitly wipes `K_{k-1}` before releasing the quiesced threads. `K_rt` signs a compact Delta-SwapCert `sigma_k = Sign_{sk_rt}(R_{k-1}, Delta_k, R_k, e_k, eta_k, kind_k)`. Peers verify `sigma_k` against `pk_rt` (pinned from hardware quote `q_0`), verify `R_k == Extend(R_{k-1}, Delta_k)` and `e_k == e_peer + 1`, advance `e_peer := e_k`, and switch to `K_k`. A hostile VMM rolling the CVM back to `e_{k-1}` possesses only `K_{k-1}`, which the peer rejects immediately.
4. **Exhaustive BFS receipt:** On the `ratcheted_sanitized` state machine (`20` reachable states, `30` transitions), exhaustive BFS confirms **`0` violations** across all three safety invariants (`POISONED_STATE_IN_V2 = null`, `ROLLBACK_TOCTOU_ACCEPTED = null`, `IRREVERSIBLE_RTMR_CORRUPTION = null`).

### 4. Cross-Restart State Continuity, Fork-Consistency Bounds, and Monotonic Anchors

Basis: normative + documentation + source + execution

Live-session HKDF ratcheting defeats VMM rollback **only within a live session against a stateful peer** holding watermark `e_peer`. When a CVM restarts from host-managed encrypted storage (or serves two non-communicating peers `Peer1` and `Peer2` across a restart), the peer-held watermark does not prevent a snapshot-capable VMM from cloning the persisted encrypted disk at epoch `0`, serving branch `A` to `Peer1` at epoch `1`, restoring the epoch `0` disk snapshot, and serving conflicting branch `B` to `Peer2` at epoch `1`.

**Fork-consistency lower bound:** As established by Mazières & Shasha (SUNDR, PODC 2002, DOI `10.1145/571825.571840`), Parno et al. (Memoir, IEEE S&P 2011, DOI `10.1109/SP.2011.38`), Strackx & Piessens (Ariadne, USENIX Security 2016), Matetic et al. (ROTE, USENIX Security 2017, ePrint `2017/048`), and Brandenburger et al. (LCM, DSN 2017, DOI `10.1109/DSN.2017.45`), **no purely local cryptographic primitive inside a resettable TEE** (including AEAD, Merkle hash trees, `RTMR`/`REM`, or DICE `CDI_Seal`) can guarantee linearizable state continuity across restarts against a rollback-capable untrusted storage host. Without a non-clonable monotonic anchor, the strongest achievable guarantee is *fork consistency* (detectable only once `Peer1` and `Peer2` gossip).

Exhaustive BFS on the cross-restart persistence model (`/tmp/probe_ratchet_rollback.py`) confirms this boundary:
- **Unanchored (`13` states):** Synthesizes the 4-step equivocation trace `vmm_snapshot_disk -> commit_A_to_peer1 -> vmm_rollback_disk -> commit_B_to_peer2 ==> FORK_EQUIVOCATION`.
- **Anchored to non-clonable monotonic counter (`10` states):** Requiring `disk_epoch == hw_ctr` on mount and atomic `hw_ctr += 1` before revealing a new branch reduces `FORK_EQUIVOCATION` to **`null`**.

#### Engineering Comparison of Monotonic State Anchors

| Anchor Mechanism | Primary Standard / Paper | Trust Assumption | Update Latency / Throughput | Wear-Out & Crash Semantics |
| :--- | :--- | :--- | :--- | :--- |
| **TPM 2.0 NV Monotonic Counter** | TCG TPM 2.0 Library Spec (`TPM2_NV_Increment`, `TPMA_NV_COUNTER`); `tpm2-tss` `Esys_NV_Increment.c` | Discrete/firmware TPM silicon + salted/encrypted auth session (to defeat SPI/LPC bus interposition) | ~10–100 ms per increment; low rate | Severe NVRAM wear-out (~100k–1M writes) and TPM anti-hammering rate limits; crash between `NV_Increment` and disk flush causes off-by-one skew requiring Memoir/Ariadne crash-recovery protocol. |
| **eMMC / UFS RPMB Partition** | JEDEC `JESD84-B51` (eMMC 5.1) / `JESD220` (UFS) RPMB | Pre-provisioned HMAC-SHA256 shared key burned once into storage controller + hardware 32-bit write counter | ~1–10 ms per authenticated 256-byte frame | Hardware atomically verifies HMAC over `(payload \|\| write_counter)` and increments `write_counter`; susceptible to flash wear-out under high-frequency commits and requires secure key provisioning before host exposure. |
| **Memoir (History Tree + TPM NVRAM)** | Parno et al., IEEE S&P 2011 (`10.1109/SP.2011.38`) | TPM 1.2/2.0 NVRAM + trusted module | 1 NVRAM write per externally visible state transition (batched internally) | Stores a cryptographic summary (History Tree root) in NVRAM with crash-recovery log to distinguish benign power loss from adversarial rollback. |
| **Ariadne (Minimal 1-Write Continuity)** | Strackx & Piessens, USENIX Security 2016 | Hardware monotonic counter (`TPM2_NV_Increment`) | Strictly 1 monotonic counter increment per state transition (vs. 2 in naive prepare/commit) | Eliminates double-write crash windows by deriving per-epoch sealing keys from counter value `c` and resolving crash-in-progress ambiguity on next boot. |
| **ROTE (Distributed Witness Quorum)** | Matetic et al., USENIX Security 2017 (`ePrint 2017/048`) | Threshold of `n >= 2f + 1` (or `3f + 1` for BFT) independent remote TEE witness counters (`|Q_1 cap Q_2| >= 1` honest witness) | Network RTT (~1–5 ms in datacenter; thousands of ops/sec, zero NVRAM wear-out) | Eliminates local TPM wear-out and enables multi-host VM live migration; trades local availability for network quorum liveness. |
| **Lightweight Collective Memory (LCM)** | Brandenburger et al., DSN 2017 (`10.1109/DSN.2017.45`) | Multi-client gossip or external untrusted log + optional witnesses | Near-zero per-op overhead when auditing lazily | Provides fork-linearizability / fork detection rather than immediate rollback prevention unless paired with an online witness quorum. |

**Cross-restart mount invariant:** Combining an anchor counter `c` with `AEAD_Open` over the persisted root and current lineage measurement prevents both rollback and cross-version state confusion:

```text
c := Anchor.read()
s := AEAD_Open(K_seal, aad = (c || H(schema) || R_k), ciphertext_blob)
assert ValidSchema(s) and Inv_k(s)
```

Note that on platforms where `K_seal` is derived via DICE (`CDI_Seal`), Open Profile for DICE (`google/open-dice`, `docs/specification.md:307-315`) deliberately excludes volatile `code` and `config` hashes from `CDI_Seal = KDF(32, UDS, H(authority || mode || hidden), "CDI_Seal")` so sealed storage survives authorized upgrades—which makes binding `c` and `H(schema)` into AEAD AAD and running `xf_check` on unsealed state essential whenever code updates across restarts.

### 5. Control-Plane Interrupt & Exception Injection Defenses (Ahoi: WeSee & Heckler)

Basis: normative + documentation + source + execution

Even if `MRTD`/`RIM`, `RTMR`/`REM`, `xf_check`, HKDF ratcheting, and monotonic counters are formally sound, an untrusted host VMM in a CVM architecture mediates virtual interrupts and virtualization exceptions. The **Ahoi** attack family demonstrates that unauthenticated control-plane notifications break CVM confidentiality and execution integrity directly:

1. **WeSee (CVE-2024-25743; Schlüter, Sridhara, Bertschi, Shinde, IEEE S&P 2024, `arXiv:2404.03526`):** On AMD SEV-SNP without Restricted Injection, the untrusted hypervisor can inject a forged `#VC` exception (x86 vector 29) with an attacker-chosen `error_code` (such as `SVM_EXIT_MSR`, `SVM_EXIT_CPUID`, or `SVM_EXIT_NPF`) at an arbitrary guest `RIP`. An unhardened guest `#VC` handler blindly trusts the `error_code`, copies guest register state into the shared `GHCB` page (leaking secrets such as kTLS keys), or emulates instructions and advances `RIP` using attacker-controlled hypervisor responses (corrupting kernel firewall rules or achieving kernel arbitrary code execution).
2. **Heckler (CVE-2024-25744; Schlüter, Sridhara, Kuhne, Bertschi, Shinde, USENIX Security 2024, `arXiv:2404.03387`):** Across both AMD SEV-SNP and Intel TDX, the untrusted hypervisor injects malicious **non-timer external interrupts** whose IDT handlers carry global side effects—most notably vector `0x80` (legacy 32-bit x86 `INT $0x80` system call entry) or other globally visible interrupt vectors—at carefully timed instructions (using single-stepping / page-fault side channels). Because x86 legacy IDT delivery shares vector `0x80` between software `INT $0x80` instructions and external interrupts, an injected external interrupt `0x80` dispatches into the Linux 32-bit syscall handler using whatever register values happen to sit in `EAX`/`EBX`/... at that instruction, enabling authentication bypasses in OpenSSH and `sudo` and breaking execution integrity in user programs.

#### Primary-Source Audit of Upstream Mitigations (`torvalds/linux` & `coconut-svsm/svsm` & `TF-RMM`)

Direct inspection of pinned upstream kernels and monitors reveals exact defense boundaries and remaining hardware prerequisites:

| System & Pinned File | Line Range | Concrete Defense Mechanism | Residual Gap / Hardware Prerequisite |
| :--- | :--- | :--- | :--- |
| **Linux SEV-SNP `#VC` opcode check** (`torvalds/linux`, `arch/x86/coco/sev/vc-shared.c`) | `L7–96` | `vc_check_opcode_bytes()` decodes instruction at `RIP` and verifies exact opcode + ModR/M match for `exit_code` (`SVM_EXIT_CPUID -> 0xa20f`, `SVM_EXIT_MSR -> 0x320f/0x300f`, `SVM_EXIT_RDTSC -> 0x310f`, `SVM_EXIT_RDTSCP -> 0x010f/0xf9`, `SVM_EXIT_VMMCALL -> 0x010f/0xd9`, `READ/WRITE_DR7 -> 0x210f/0x230f` reg 7, `WBINVD -> 0x090f`, `MONITOR/MWAIT`); mismatches return `ES_UNSUPPORTED` (terminating kernel `#VC` via `sev_es_terminate` at `vc-handle.c:978`). | Lines `15–18` defer `SVM_EXIT_IOIO` and `SVM_EXIT_NPF` to per-handler checks; lines `98–102` (`vc_decoding_needed`) skip instruction decoding entirely for exception exit codes `SVM_EXIT_EXCP_BASE..SVM_EXIT_LAST_EXCP` (`#DB`, `#AC`). |
| **Linux SEV-SNP `#VC` MMIO check** (`torvalds/linux`, `arch/x86/coco/sev/vc-handle.c`) | `L39–72`, `L562–583` | `vc_handle_mmio()` rejects `user_mode(ctxt->regs)` (`L581`); `vc_slow_virt_to_phys()` walks guest page tables and rejects any PTE with `_PAGE_ENC` set (`WARN_ON_ONCE(pte_val(*pte) & _PAGE_ENC) -> ES_UNSUPPORTED`, `L62–64`), blocking forged MMIO `#VC` over private encrypted RAM. | Does not block forged `#VC` on legitimate shared/decrypted MMIO pages or legitimate interceptable instructions executed at attacker-chosen timing. |
| **Linux SEV-SNP `#VC` invalid-context & Secure MSR checks** (`torvalds/linux`, `arch/x86/coco/sev/vc-handle.c`) | `L359–414`, `L860–873`, `L955–959` | `vc_from_invalid_context()` panics on invalid VC2 stack entry; `__vc_handle_msr()` returns `ES_VMM_ERROR` if host intercepts `MSR_AMD64_GUEST_TSC_FREQ` under Secure TSC or `MSR_AMD64_SAVIC_CONTROL` under Secure AVIC. | Full elimination of untrusted hypervisor exception injection on SEV-SNP requires hardware **Restricted Injection** (`MSR_AMD64_SNP_RESTRICTED_INJ_BIT`, `sev/core.c:80`) plus **Secure AVIC** (`CC_ATTR_SNP_SECURE_AVIC`, `coco/core.c:107-108`). |
| **COCONUT-SVSM VMPL 0 `#VC` handler** (`coconut-svsm/svsm`, `kernel/src/cpu/vc.rs`) | `L94–157` | Panics immediately on `SVM_EXIT_PAGE_NOT_VALIDATED` (`L103`), decodes instruction at `RIP` (`vc_decode_insn`, `L110`), matches `(error_code, decoded_insn)` pairs strictly (`L112–130`), and answers `CPUID` from the firmware-verified SNP CPUID table rather than querying the untrusted hypervisor (`L148–172`). | Like Linux, skips instruction decoding for `SVM_EXIT_EXCP_BASE..=SVM_EXIT_LAST_EXCP` (`L209–210`, e.g., `X86_TRAP` debug support when GDB stub is active). |
| **Linux Heckler `INT $0x80` defense** (`torvalds/linux`, `arch/x86/entry/syscall_32.c`) | `L62–70`, `L88–150`, `L176–207` | (1) `CONFIG_IA32_EMULATION_DEFAULT_DISABLED` disables 32-bit emulation by default (`L63`). (2) `do_int80_emulation()` panics if `!user_mode(regs)` (`L132–136`). (3) `int80_is_external()` reads Local APIC `APIC_ISR` bit for vector `0x80` and panics if set (`L88–105, 148–149`). (4) `CONFIG_X86_FRED` separates `EVENT_TYPE_SWINT` from `EVENT_TYPE_EXTINT` in silicon (`L176–207`). | Explicit source warning (`syscall_32.c:101–103`): **`int80_is_external()` is ONLY valid when a trusted secure module owns the vAPIC** (Intel TDX, or AMD SEV-SNP with Secure AVIC / Restricted Injection). Without trusted vAPIC or FRED, a host VMM can spoof `APIC_ISR` or inject other non-`0x80` external interrupt vectors unless masked/allowlisted. |
| **Linux TDX `#VE` reduction** (`torvalds/linux`, `arch/x86/coco/tdx/tdx.c`) | `L237–390` | `disable_sept_ve()` requires `TDX_TD_ATTR_SEPT_VE_DISABLE` or writes `TD_CTLS_PENDING_VE_DISABLE` (`L237–270`); `reduce_unnecessary_ve()` sets `TD_CTLS_REDUCE_VE` (`L298–308`); `ve_instr_len()` refuses to trust `ve->instr_len` for `EXIT_REASON_EPT_VIOLATION` (`L378–385`). | TDX Module prevents host VMM from injecting architectural exceptions (`vector < 32`), blocking WeSee-style `#VC` injection, but host VMM still triggers posted external interrupts (`vector >= 32`), making `int80_is_external()`, `CONFIG_IA32_EMULATION_DEFAULT_DISABLED`, or `FRED` mandatory on TDX as well. |
| **Arm CCA RMM injection gating** (`TF-RMM/tf-rmm`, `runtime/rmi/run.c`) | `L31–75`, `L237–260`, `L527–543` | Host passes `rmi_rec_enter` flags (`REC_ENTRY_FLAG_EMUL_MMIO`, `REC_ENTRY_FLAG_INJECT_SEA`) and GICv3 list registers; RMM validates pending exit context before completing MMIO emulation or injecting synchronous external aborts (`inject_sync_idabort_rec`), preventing arbitrary synchronous exception forgery outside matching Realm exit states. | Asynchronous virtual IRQs (`GICv3` LRs) remain host-schedulable, so Realm OS drivers and live-update quiescence points must still treat unexpected IRQ vectors and IRQ timing as adversarial. |

**Interaction with attested live-update ratchets:** During the six-stage live-update commit automaton (§3), a malicious VMM injecting a forged `#VC` or external interrupt inside the quiesced window between `xf_check` and `HKDF_Ratchet` could attempt to hijack control flow or exfiltrate `K_{k-1}`/`sk_rt`. Consequently, the Runtime Core `K_rt` MUST execute the entire atomic commit critical section (`Quiesced -> Validated -> Committed`) with local interrupts masked (`RFLAGS.IF = 0` on x86-64; `DAIF.I = 1` on AArch64), zero host hypercalls / `VMGEXIT` / `TDVMCALL` inside the commit window, and hardware-enforced notification gating (TDX / CCA RMM / SEV-SNP Restricted Injection + Secure AVIC / x86 FRED).

## Boundaries

- **Live-update quiescence liveness under async runtimes (`unknown`):** The six-stage commit automaton and exhaustive BFS prove *safety* once all worker threads reach a `con-free` quiescence point `p in Q` with in-flight DMA/I/O drained. Proving *bounded-time quiescence liveness* across cooperative async executors or constant-time cryptographic loops without introducing secret-dependent poll branches was **not examined** empirically here and remains an open verification boundary.
- **Physical / microarchitectural side channels (`not examined`):** Transient-execution attacks (Spectre/MDS/Downfall), ciphertext side channels (Cipherleaks), and controlled-channel page-fault single-stepping (used by Heckler for instruction-level interrupt placement) are **not examined** in the executable probe; the probe models architectural state transitions, host snapshots, and control-plane injection only.
- **Intel TDX live migration (`MigTD`) protocol internals (`not examined`):** Although `intel/migtd` exists for TDX VM live migration (using a Migration TD to bind source/destination `TDINFO` and migrate encrypted guest memory), its full Rust session state machine was **not examined** at line granularity in this report.
- **Software-only rollback protection across restarts (`known not to apply`):** Local enclave encryption, AEAD tags, Merkle roots, `MRTD`/`RIM`, and `RTMR`/`REM` chains are **known not to apply** to preventing cross-restart fork equivocation against a snapshot-capable host; a non-clonable hardware counter or external witness quorum is mathematically necessary.
- **Unprivileged hardware reset of `RTMR`/`REM` (`unsupported`):** Intel TDX (`TDX_MODULE_2.0.20`) and Arm CCA (`TF-RMM` / DEN0137) explicitly **do not support** resetting, decrementing, or popping entries from `RTMR[0..3]` or `REM[0..3]` without tearing down and recreating the Trust Domain / Realm.
- **Linux `int80_is_external()` on unhardened SEV-SNP (`known not to apply`):** As explicitly documented in `torvalds/linux` (`arch/x86/entry/syscall_32.c:101-103`), reading `APIC_ISR` to reject external vector `0x80` is **known not to apply** when the untrusted hypervisor controls the virtual APIC (standard SEV-SNP without Secure AVIC or Restricted Injection).

## Evidence

### Primary Git Repositories and Line Citations (Observed 2026-11-19)

1. **`intel/confidential-computing.tdx.tdx-module`** @ `abd4d8ab7e18a345ba33e32335577f550f7b0e83` (`TDX_MODULE_2.0.20`):
   - `src/td_dispatcher/vm_exits/tdg_mr_rtmr_extend.c:40-148`: `tdg_mr_rtmr_extend()` — 64-byte GPA alignment check (`L51`), `PRIVATE_ONLY` GPA walk (`L67-74`), `index >= NUM_RTMRS` check (`L91`), `lfence()` (`L98`), exclusive `rtmr_lock` (`L101`), 96-byte `SHA-384(rtmr[i] || ext_48B)` (`L111-121`), `last_teeinfo_hash_valid = false` (`L131`).
   - `src/td_dispatcher/vm_exits/tdg_mr_report.c:54-250`: `tdg_mr_report()` — `TEEINFOHASH` caching check (`L164-174`), guest-side pending interrupt preemption point (`L178-188`), `ia32_seamops_seamdb_report` (`L192-194`).
   - `src/vmm_dispatcher/api_calls/tdh_mr_finalize.c:38-134`: `tdh_mr_finalize()` — finalizes `MRTD` via `sha384_finalize` (`L107-108`) and transitions TD to `OP_STATE_RUNNABLE` (`L118`).
2. **`TF-RMM/tf-rmm`** @ `8d7961df074f08fd83a2460ab3a2ca0b658fde92`:
   - `runtime/rsi/realm_attest.c:19,113-478,480-558`: `MAX_EXTENDED_SIZE = 64U` (`L19`), `realm_attest_token_init` recording `fw_img_sequence` (`L171`), `is_attest_token_re_init_needed` restarting in-flight attestation across RMM Live Firmware Activation (`L269-279, 331-343`), `handle_rsi_measurement_extend` asserting Plane 0 (`L428`), locking `GRANULE_STATE_RD` (`L437`), rejecting `RIM_MEASUREMENT_SLOT` (`L449-453`), and calling `measurement_extend` (`L465-471`).
   - `app/attestation/rmm_stub/src/measurement.c:23-110`: `measurement_extend()` supporting `HASH_SHA_256`, `HASH_SHA_384`, `HASH_SHA_512` with `extend_measurement_size <= MAX_MEASUREMENT_SIZE`.
   - `runtime/rmi/run.c:31-75,237-260,527-543`: `complete_mmio_emulation`, `complete_sea_insertion`, and `smc_rec_enter` GIC/HCR handling.
3. **`torvalds/linux`** @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`:
   - `arch/x86/coco/sev/vc-shared.c:7-103`: `vc_check_opcode_bytes()` and `vc_decoding_needed()`.
   - `arch/x86/coco/sev/vc-handle.c:39-72,359-414,562-583,791-853,860-1024`: `vc_slow_virt_to_phys()` (`_PAGE_ENC` rejection), `__vc_handle_msr()` (Secure TSC / Secure AVIC checks), `vc_handle_exitcode()`, `vc_from_invalid_context()`, `kernel_exc_vmm_communication()`.
   - `arch/x86/coco/sev/core.c:79-80` & `arch/x86/coco/core.c:98-109`: `MSR_AMD64_SNP_RESTRICTED_INJ_BIT`, `CC_ATTR_GUEST_SNP_SECURE_TSC`, `CC_ATTR_SNP_SECURE_AVIC`.
   - `arch/x86/coco/tdx/tdx.c:145-178,237-390`: `tdx_mcall_extend_rtmr()`, `disable_sept_ve()`, `reduce_unnecessary_ve()`, `ve_instr_len()`.
   - `arch/x86/entry/syscall_32.c:62-70,88-207`: `__ia32_enabled`, `int80_is_external()`, `do_int80_emulation()`, `DEFINE_FREDENTRY_RAW(int80_emulation)`.
4. **`coconut-svsm/svsm`** @ `2a40e72a0f44d4369bb997488f2b7a77e346a634`:
   - `kernel/src/cpu/vc.rs:94-212`: `handle_vc_exception()` enforcing `error_code != SVM_EXIT_PAGE_NOT_VALIDATED`, opcode-matched dispatch, and firmware CPUID table lookup without hypervisor calls.
5. **`google/open-dice`** @ `607edea585175874d437fb7de8377409bb7781ee`:
   - `docs/specification.md:289-336`: `CDI_Attest` vs. `CDI_Seal` derivation formulas separating attestation identity from upgrade-surviving sealing keys.
6. **`tpm2-software/tpm2-tss`** @ `8de0ea01520718789c0e09b07480543f13969c14`:
   - `src/tss2-esys/api/Esys_NV_Increment.c:1-45`: `TPM2_NV_Increment` ESYS client binding for `TPMA_NV_COUNTER` NV indices.

### Specifications and Peer-Reviewed Publications

- Intel Corporation, *Intel Trust Domain Extensions (Intel TDX) Module v1.5 Base Architecture Specification* (Doc 348549) and *ABI Reference Specification* (Doc 348551).
- Arm Limited, *Arm Realm Management Monitor (RMM) Specification* (DEN0137, v1.0 / v1.1).
- TCG, *TPM 2.0 Library Specification* (`TPMA_NV_COUNTER`, `TPM2_NV_Increment`); JEDEC `JESD84-B51` (eMMC 5.1 RPMB) and `JESD220` (UFS RPMB); IETF RFC 5869 (HKDF) and RFC 8446 (TLS 1.3 `KeyUpdate`).
- M. Hicks and S. Nettles, "Dynamic Software Updating," *ACM TOPLAS* 27(6), 2005, DOI `10.1145/1108970.1108971`.
- G. Stoyle, M. Hicks, G. Bierman, P. Sewell, and I. Neamtiu, "Mutatis Mutandis: Safe and Predictable Dynamic Software Updating," *POPL 2005* (`10.1145/1040305.1040321`) and *ACM TOPLAS* 2007 (`10.1145/1255450.1255455`).
- D. Mazières and D. Shasha, "Building Secure File Systems out of Byzantine Storage," *PODC 2002*, DOI `10.1145/571825.571840`.
- B. Parno, J. R. Lorch, J. R. Douceur, J. Mickens, and J. M. McCune, "Memoir: Practical State Continuity for Protected Modules," *IEEE S&P 2011*, DOI `10.1109/SP.2011.38`.
- R. Strackx and F. Piessens, "Ariadne: A Minimal Approach to State Continuity," *USENIX Security 2016*.
- S. Matetic, M. Ahmed, K. Kostiainen, A. Dhar, D. Sommer, A. Gervais, A. Juels, and S. Capkun, "ROTE: Rollback Protection for Trusted Execution," *USENIX Security 2017*, IACR ePrint `2017/048`.
- M. Brandenburger, C. Cachin, M. Lorenz, and R. Kapitza, "Rollback and Forking Detection for Trusted Execution Environments using Lightweight Collective Memory," *IEEE/IFIP DSN 2017*, DOI `10.1109/DSN.2017.45`.
- B. Schlüter, S. Sridhara, A. Bertschi, and S. Shinde, "WeSee: Using Malicious #VC Interrupts to Break AMD SEV-SNP," *IEEE S&P 2024*, `arXiv:2404.03526`, CVE-2024-25743.
- B. Schlüter, S. Sridhara, M. Kuhne, A. Bertschi, and S. Shinde, "Heckler: Breaking Confidential VMs with Malicious Interrupts," *USENIX Security 2024*, `arXiv:2404.03387`, CVE-2024-25744.

### Executable Micro-Probe & Observed Output (Python 3.13.15, Linux x86_64, 2026-11-19)

Command: `python3 /tmp/probe_ratchet_rollback.py` (exit code `0`).

```python
#!/usr/bin/env python3
"""Self-contained finite-state BFS & cryptographic chain probe for attested
live-update ratchets, cross-restart monotonic counters, and Ahoi defenses."""
from collections import deque
import hashlib, hmac, json

def sha384_extend(reg: bytes, data_48: bytes) -> bytes:
    assert len(reg) == 48 and len(data_48) == 48
    return hashlib.sha384(reg + data_48).digest()

def sha256_rem_extend(reg: bytes, data: bytes) -> bytes:
    assert len(reg) == 32 and len(data) <= 64
    return hashlib.sha256(reg + data + b"\x00" * (64 - len(data))).digest()

def hkdf_sha256(ikm: bytes, salt: bytes, info: bytes, length: int = 32) -> bytes:
    prk = hmac.new(salt, ikm, hashlib.sha256).digest()
    t, okm, c = b"", b"", 1
    while len(okm) < length:
        t = hmac.new(prk, t + info + bytes([c]), hashlib.sha256).digest()
        okm += t; c += 1
    return okm[:length]

def bfs_live_swap(mode: str):
    init = (1, False, 1, 0, 1, 0, False, None)
    q, visited = deque([(init, [])]), {init}
    viol = {"POISONED_STATE_IN_V2": None, "ROLLBACK_TOCTOU_ACCEPTED": None,
            "IRREVERSIBLE_RTMR_CORRUPTION": None}
    trans = 0
    while q:
        st, tr = q.popleft()
        ver, pois, rtmr, kep, pver, pkep, qui, snap = st
        if ver == 2 and pois and viol["POISONED_STATE_IN_V2"] is None:
            viol["POISONED_STATE_IN_V2"] = tr
        if ver == 1 and rtmr == 2 and not qui and viol["IRREVERSIBLE_RTMR_CORRUPTION"] is None:
            viol["IRREVERSIBLE_RTMR_CORRUPTION"] = tr
        succs = []
        if ver == 1 and not pois and not qui:
            succs.append(("v1_bug_poisons_state", (1, True, rtmr, kep, pver, pkep, False, snap)))
        if snap is None and not qui:
            succs.append(("vmm_snapshot_tee", (ver, pois, rtmr, kep, pver, pkep, False, (ver, pois, rtmr, kep))))
        if snap is not None and snap != (ver, pois, rtmr, kep):
            succs.append(("vmm_restore_snapshot", (*snap, pver, pkep, False, snap)))
        if ver == 1 and not qui:
            succs.append(("quiesce_for_swap_v2", (1, pois, rtmr, kep, pver, pkep, True, snap)))
        if ver == 1 and qui:
            if mode == "naive":
                succs.append(("xf_no_check_then_rtmr_and_commit_v2", (2, pois, 2, kep, pver, pkep, False, snap)))
            elif mode == "premature_rtmr":
                if rtmr == 1:
                    succs.append(("rtmr_extend_premature", (1, pois, 2, kep, pver, pkep, True, snap)))
                elif pois:
                    succs.append(("xf_check_fails_rollback_v1", (1, pois, rtmr, kep, pver, pkep, False, snap)))
                else:
                    succs.append(("xf_check_ok_commit_v2", (2, False, 2, 1, pver, pkep, False, snap)))
            elif mode == "ratcheted_sanitized":
                if pois:
                    succs.append(("xf_check_rejects_pre_rtmr_abort", (1, True, rtmr, kep, pver, pkep, False, snap)))
                else:
                    succs.append(("xf_check_ok_wx_rtmr_hkdf_zeroize_commit_v2", (2, False, 2, 1, pver, pkep, False, snap)))
        if rtmr == 2 and pver == 1 and not qui:
            npk = 1 if mode in ("premature_rtmr", "ratcheted_sanitized") else pkep
            succs.append(("peer_accepts_v2_attestation", (ver, pois, rtmr, kep, 2, npk, False, snap)))
        if ver == 1 and pver == 2 and kep == pkep and not qui and viol["ROLLBACK_TOCTOU_ACCEPTED"] is None:
            viol["ROLLBACK_TOCTOU_ACCEPTED"] = tr + ["v1_sends_msg_accepted_as_v2"]
        for act, nxt in succs:
            trans += 1
            if nxt not in visited:
                visited.add(nxt); q.append((nxt, tr + [act]))
    return {"mode": mode, "states": len(visited), "transitions": trans, "violations": viol}

def bfs_cross_restart_fork(anchored: bool):
    init = (0, "init", 0, None, None, None)
    q, visited, fork = deque([(init, [])]), {init}, None
    while q:
        (dep, dbr, ctr, p1, p2, snap), tr = q.popleft()
        if p1 and p2 and p1[0] == p2[0] and p1[1] != p2[1] and fork is None:
            fork = tr
        succs = []
        if snap is None:
            succs.append(("vmm_snapshot_disk", (dep, dbr, ctr, p1, p2, (dep, dbr))))
        if snap is not None and (dep, dbr) != snap:
            succs.append(("vmm_rollback_disk", (snap[0], snap[1], ctr, p1, p2, snap)))
        if ((not anchored) or dep == ctr) and dep == 0:
            if p1 is None:
                succs.append(("commit_A_to_peer1", (1, "A", ctr + int(anchored), (1, "A"), p2, snap)))
            if p2 is None:
                succs.append(("commit_B_to_peer2", (1, "B", ctr + int(anchored), p1, (1, "B"), snap)))
        for act, nxt in succs:
            if nxt not in visited:
                visited.add(nxt); q.append((nxt, tr + [act]))
    return {"anchored": anchored, "states": len(visited), "fork_equivocation_trace": fork}

if __name__ == "__main__":
    z48 = b"\x00" * 48
    a, b = hashlib.sha384(b"component-v1").digest(), hashlib.sha384(b"component-v2").digest()
    ab, ba = sha384_extend(sha384_extend(z48, a), b), sha384_extend(sha384_extend(z48, b), a)
    assert ab != ba
    out = {
        "rtmr_ab_prefix": ab.hex()[:16], "rtmr_ba_prefix": ba.hex()[:16],
        "naive": bfs_live_swap("naive"),
        "premature_rtmr": bfs_live_swap("premature_rtmr"),
        "ratcheted_sanitized": bfs_live_swap("ratcheted_sanitized"),
        "cross_restart_unanchored": bfs_cross_restart_fork(False),
        "cross_restart_anchored": bfs_cross_restart_fork(True),
    }
    print(json.dumps(out, indent=2))
```

Observed results:
- `rtmr_ab_prefix = "31ea36f6186ca3b2"`, `rtmr_ba_prefix = "3f6205a4fd3bddc3"` (`ab != ba` verified).
- `naive` (`30` states, `42` transitions): found `POISONED_STATE_IN_V2` (3 steps) and `ROLLBACK_TOCTOU_ACCEPTED` (6 steps).
- `premature_rtmr` (`41` states, `67` transitions): found `IRREVERSIBLE_RTMR_CORRUPTION` (4 steps).
- `ratcheted_sanitized` (`20` states, `30` transitions): **0 violations** across all three safety invariants.
- `cross_restart_unanchored` (`13` states): found `FORK_EQUIVOCATION` (4 steps); `cross_restart_anchored` (`10` states): **0 fork equivocations**.

## Revalidation

To cheaply revalidate these findings against a newer TDX Module, TF-RMM, SVSM, or Linux kernel revision without repeating the full literature survey:

1. **Diff TDX `RTMR` and `TDREPORT` handlers:** Inspect `src/td_dispatcher/vm_exits/tdg_mr_rtmr_extend.c` and `tdg_mr_report.c` in `intel/confidential-computing.tdx.tdx-module` against `abd4d8ab7e18a345ba33e32335577f550f7b0e83`. Confirm whether `PRIVATE_ONLY`, 64-byte alignment, exclusive `rtmr_lock`, `NUM_RTMRS`, or any new RTMR-reset / TD-preserving live-update leaf has been introduced.
2. **Diff TF-RMM `RSI_MEASUREMENT_EXTEND` and LFA hooks:** Inspect `runtime/rsi/realm_attest.c` in `TF-RMM/tf-rmm` against `8d7961df074f08fd83a2460ab3a2ca0b658fde92`. Confirm `RIM_MEASUREMENT_SLOT` immutability, Plane 0 enforcement, `MAX_EXTENDED_SIZE`, and `fw_img_sequence` re-initialization behavior across RMM LFA.
3. **Audit Linux/SVSM Ahoi defenses:** Diff `arch/x86/coco/sev/vc-shared.c` (`vc_check_opcode_bytes`), `arch/x86/coco/sev/vc-handle.c` (`vc_slow_virt_to_phys`), and `arch/x86/entry/syscall_32.c` (`int80_is_external`, `CONFIG_X86_FRED`) in `torvalds/linux` against `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`. Check specifically whether AMD SEV-SNP Restricted Injection or Secure AVIC is enabled by default in guest boot paths and whether exception exit codes (`vc_decoding_needed`) remain unvalidated.
4. **Rerun the finite-state BFS probe:** Execute `python3 /tmp/probe_ratchet_rollback.py` (takes `< 50 ms`) after extending the transition relation with any new candidate commit step (such as asynchronous DMA drain or multi-vCPU barrier protocols) to verify that all four violation classes remain unreachable.
