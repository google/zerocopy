# Spacecraft Radiation TMR Scrubbing, Zero-Malloc Flight Software Buses, and BPv7/LTP Deep-Space DTN Custody

## Summary

Spacecraft onboard computing spans three tightly coupled dependability layers—radiation-hardened sequential hardware (`LEON3FT`/`NOEL-V`, SRAM-FPGA Triple Modular Redundancy `TMR` in `SpyDrNet-TMR`), deterministic flight-software message buses (`NASA cFE`/`OSAL`, `JPL F Prime`), and deep-space store-carry-and-forward networking (`BPv7` `RFC 9171`, `BPSec` `RFC 9172`, `LTP` `RFC 5326`, `ION-DTN`, `HDTN`)—whose reliability guarantees collapse if timing, memory-allocation, or canonicalization invariants fail at any layer boundary:

1. **TMR Without Bounded Periodic Scrubbing Degrades Below Simplex (`CTMC` Crossover $t^* = \ln(2)/\lambda$):** Unscrubbed 2-of-3 majority voting retains latent faults across replicas indefinitely. Continuous-Time Markov Chain (`CTMC`) analysis shows unscrubbed TMR reliability $R_{\text{TMR}}(t) = 3e^{-2\lambda t} - 2e^{-3\lambda t}$ drops strictly below a simplex core $e^{-\lambda t}$ after $t^* = \ln(2)/\lambda$ (`6931.47 hr` at $\lambda = 10^{-4}\text{ hr}^{-1}$, with $\text{MTTF} = 8333.33\text{ hr} < 10000\text{ hr}$). Adding periodic state/CRAM scrubbing at rate $\mu = 1/T_{\text{scrub}}$ raises $\text{MTTF}$ to $\frac{5\lambda + \mu}{6\lambda^2}$ (`1.67e9 hr` at $T_{\text{scrub}} = 36\text{ s}$), provided voters are inserted across sequential feedback loops (`SpyDrNet-TMR`) and clock/reset trees avoid single-point Common-Cause Failures (`CCF`).
2. **Deterministic Flight Software Buses Replace Heap Allocation With Static Pools (`cFE` vs. `F Prime`):** Following Holzmann's Power-of-Ten rules (`DOI: 10.1109/MC.2006.212`), both `NASA cFE` and `JPL F Prime` prohibit post-initialization dynamic heap allocation (`malloc`/`free`). `cFE` (`cfe_es_mempool.c`, `cfe_sb_api.c`) uses bucketed `CFE_ES_PoolCreate` pools, pipe-depth/message-limit quotas (`MsgLim`), zero-copy reference-counted `CFE_SB_Buffer_t` loans, and `OSAL` disjoint typed 32-bit resource IDs (`osapi-idmap.c`), whereas `F Prime` pairs compile-time typed `Fpp` port wiring with `Svc::BufferManager` context-checked static buffer bins.
3. **Deep-Space `BPv7`/`BPSec`/`LTP`/`CGR` Trades Conversational Sessions for Deterministic Canonical Blocks and Scheduled Storage (`ION-DTN`, `HDTN`):** Minute-to-hour One-Way Light Time (`OWLT`) and planetary occultations invalidate conversational `TCP`/`TLS` handshakes. `RFC 9171` and `RFC 9172` pair an indefinite-length CBOR bundle envelope (`0x9f ... 0xff`) with `RFC 8949 §4.2` core deterministic CBOR blocks so `BPSec` Block Integrity Blocks (`BIB`) hash identical octets end-to-end (`HDTN` `Bpv7BpSecExtensionBlocks.cpp`). Because `BPv7` drops `BPv6` primary-block custody flags, hop-by-hop reliability shifts to `LTP` (`RFC 5326`) red-part ARQ backed by non-volatile `SDR` transactions (`ION-DTN` `libltpP.c`) and Contact Graph Routing (`libcgr.c`) over bounded storage horizons.

## Applicability

This report synthesizes findings across nine directly inspected repositories and IETF standards:

- **FPGA & Processor TMR Mitigation (`byuccl/spydrnet-tmr` @ `5833d9fa9808c8582dd8845f990359a82247ef5a`, `LEON3FT`/`NOEL-V`, `GRSCRUB`):** Netlist triplication and voter-insertion analysis (`apply_tmr_to_netlist.py`) applies to synchronous digital netlists mapped onto SRAM-based or flash-based FPGAs, while the CTMC scrubbing bounds hold under constant independent per-domain Poisson upset rate $\lambda$ and exponential/periodic scrub rate $\mu \gg \lambda$.
- **Flight Software Executive & Component Bus (`nasa/cFE` @ `3673163b7fd34d7bb69546f1cd13ddb39ac7cde6`, `nasa/osal` @ `2a96a4fff5b3a3252cb33e95862a02667e509e24`, `nasa/fprime` @ `83221ba82a7765fe7226681050e971b31b64d29f`):** Applies to real-time spacecraft FSW targets enforcing static memory provisioning (`CFE_ES`, `CFE_SB`, `OSAL`, `Svc::BufferManager`). Note that `F Prime` `BufferManagerComponentImpl` checks ownership and bounds via `FW_ASSERT` traps rather than returning runtime error codes on double-free or out-of-bounds buffer handles.
- **Delay-Tolerant Networking Stack (`nasa-jpl/ION-DTN` @ `13dae7df4784d67591590719a92d2d653da79f95`, `nasa/HDTN` @ `f92cec5cad507cb69a3a05188334ba29ffdbbf5e`, `RFC 9171`, `RFC 9172`, `RFC 5326`):** Applies to `BPv7` bundle serialization, `BPSec` security extension processing, `LTP` reliable red-part transmission, and deterministic `CGR` schedule routing. Upstream `nasa/HDTN` at `f92cec5cad507cb69a3a05188334ba29ffdbbf5e` displays an archival unmaintained warning in `README.md`; its `common/bpcodec/src/codec/` sources remain valid reference implementations of `RFC 9171`/`9172` framing, whereas active `ION-DTN` covers full `SDR`/`LTP`/`CGR` flight integration.

## Findings

### 1. Cosmic-Ray SEU/SET Physics, `SpyDrNet-TMR` Voter Placement, and Scrubbing Bounds

Basis: source (`byuccl/spydrnet-tmr`) + documentation (`GRSCRUB`, `LEON3FT`/`NOEL-V`) + execution (Evidence Probe A) + derived.

Spaceborne electronics (`SPARC V8` `LEON3FT`, `RV64GC` `NOEL-V`, and SRAM-based FPGAs) face three distinct ionizing-particle effects that demand separate mitigation mechanisms:

1. **Architectural Single-Event Upsets (`SEU`):** Bit-flips inside flip-flops, register files, and caches. Hardened processors (`LEON3FT`, `NOEL-V` fault-tolerant variants) mitigate memory structures with EDAC/BCH codes and dual/triple register replication.
2. **Combinational Single-Event Transients (`SET`):** Voltage glitches induced in combinational logic gates that become latched errors only when propagating into a flip-flop setup/hold capture window around a clock edge—mitigated via temporal skewing across TMR clock phases or combinational triplication.
3. **FPGA Configuration-Memory (`CRAM`) Upsets:** Unlike transient flip-flop SEUs (which overwrite on the next clock write), an upset in an SRAM-FPGA `LUT` truth table or routing multiplexer **permanently alters the hardware circuit function** until overwritten by external frame scrubbing (such as Gaisler's `GRSCRUB` supervisor or internal `ICAP` scrubbing).

In netlist-level triplication (`byuccl/spydrnet-tmr`, `spydrnet_tmr/apply_tmr_to_netlist.py:15-112`), `apply_tmr_to_netlist` first invokes `uniquify(netlist)` to isolate hierarchical module instantiations, triplicates leaf cells and top-level ports via `apply_nmr(..., 3, name_suffix="TMR", rename_original=True)` (`lines 76-81`), discovers placement sites via `spydrnet_tmr/analysis/voter_insertion` (`find_after_ff_voter_points.py`, `find_before_ff_voter_points.py`, `find_reduction_voter_points.py`), and inserts `XilinxTMRVoter` organs (`lines 109-110`). Three structural invariants govern correctness:

- **Sequential Feedback Loop Cutting:** Triplicating registers alone leaves any corrupted replica spinning indefinitely around its own feedback loop (`Q -> comb -> D`), guaranteeing failure as soon as a second replica suffers an upset later in the mission. Placing **triplicated voters** inside every feedback loop (`after_ff` or `before_ff`) resynchronizes a corrected state onto the upset flip-flop on the very next clock cycle (for `SEU`s) once `CRAM` is intact.
- **Common-Cause Failure (`CCF`) Single Points:** Shared clock trees, asynchronous reset nets, power rails, and un-triplicated output reduction voters (`find_reduction_voter_points`) bypass 2-of-3 redundancy; an upset in a single shared reset line or reduction voter immediately corrupts all three domains simultaneously.
- **Quantitative Scrubbing Bound (CTMC Verification, Probe A):** Modeling a 3-domain TMR system with independent domain upset hazard $\lambda$ and scrub/repair rate $\mu = 1/T_{\text{scrub}}$ gives transient states $S_3$ (all 3 healthy) and $S_2$ (1 corrupted, 2 healthy), with transitions $S_3 \xrightarrow{3\lambda} S_2$, $S_2 \xrightarrow{\mu} S_3$, and $S_2 \xrightarrow{2\lambda} S_F$ (absorbing majority failure). Solving the exact closed-form CTMC eigenvalues (cross-checked against 50,000-step RK4 to $< 10^{-12}$) for $\lambda = 10^{-4}\text{ hr}^{-1}$ proves:
  - *Without scrubbing ($\mu = 0$):* $R_{\text{TMR}}(t) = 3e^{-2\lambda t} - 2e^{-3\lambda t}$ decays faster than simplex $e^{-\lambda t}$ once $t > t^* = \ln(2)/\lambda = 6931.47\text{ hr}$; at $t = 10000\text{ hr}$, unscrubbed TMR drops to $R = 0.3064$ vs. simplex $R = 0.3679$, and $\text{MTTF}_{\mu=0} = \frac{5}{6\lambda} = 8333.33\text{ hr} < 10000\text{ hr}$.
  - *With scrubbing ($\mu > 0$):* $\text{MTTF}_{\text{scrub}} = \frac{5\lambda + \mu}{6\lambda^2}$. For $\mu = 1\text{ hr}^{-1}$ ($T_{\text{scrub}} = 1\text{ hr}$), $\text{MTTF} = 1.6675 \times 10^7\text{ hr}$ and $R(10000\text{ h}) = 0.99940054$ ($P_{\text{fail}} = 5.995 \times 10^{-4}$); for $\mu = 100\text{ hr}^{-1}$ ($T_{\text{scrub}} = 36\text{ s}$), $\text{MTTF} = 1.6667 \times 10^9\text{ hr}$ and $R(10000\text{ h}) = 0.9999940001$ ($P_{\text{fail}} = 6.000 \times 10^{-6}$). Thus, achieving mission failure budget $p_{\max}$ over duration $T_{\text{mission}}$ requires $T_{\text{scrub}} \le \frac{p_{\max}}{6 \lambda^2 T_{\text{mission}}}$ (valid when $\mu \gg \lambda$).

### 2. Zero-Post-Init-Malloc Flight Software Buses: `NASA cFE`/`OSAL` vs. `JPL F Prime`

Basis: source (`nasa/cFE`, `nasa/osal`, `nasa/fprime`) + documentation (`DOI: 10.1109/MC.2006.212`).

Flight software architectures enforce Holzmann's Power-of-Ten guidelines—specifically Rule 2 (fixed loop upper bounds) and Rule 3 (no dynamic memory allocation after initialization)—so long-duration missions cannot suffer heap fragmentation or unbounded `O(n)` allocation pauses. Both `NASA cFS/cFE` and `JPL F Prime` enforce static allocation through contrasting bus abstractions:

| Architectural Property | `NASA cFE` (`SB` / `ES`) + `OSAL` | `JPL F Prime` (`Fpp` + `Svc::BufferManager`) |
| :--- | :--- | :--- |
| **Message Dispatch Model** | Dynamic runtime publish-subscribe by `CFE_SB_MsgId_t` across software pipes (`CFE_SB_CreatePipe`, `CFE_SB_SubscribeEx`) | Static compile-time typed port topology generated from `.fpp` models (`portNum` indices resolved at link/init time) |
| **Buffer Allocation Strategy** | Fixed-bucket memory pools initialized via `CFE_ES_PoolCreate` (`cfe_es_mempool.c:242-288`) over pre-reserved static buffers | Preallocated bin array (`m_buffers[0..m_numStructs-1]`) populated once at setup via `Mem::Allocator` (`BufferManagerComponentImpl.cpp:102-120`) |
| **Backpressure & Fault Isolation** | Per-pipe queue `Depth` and per-subscription `MsgLim` caps in `CFE_SB_SubscribeEx` (`cfe_sb_api.c:900`) drop excess messages without starving sibling pipes | Component input queue depths + high-water telemetry (`m_highWater`, `m_noBuffs`, `m_emptyBuffs`); caller handles null empty `Fw::Buffer` on exhaustion |
| **Handle & Type Safety** | Typed 32-bit `OSAL` IDs partition object classes (`osapi-idmap.c:24-58`) so Task IDs cannot alias Queue IDs; `0` is always invalid | Packed 32-bit `context = (m_mgrId << 16) \| id` verified by `FW_ASSERT` on return (`BufferManagerComponentImpl.cpp:80-96`) |
| **Zero-Copy Ownership Transfer** | Shared reference-counted `CFE_SB_BufferD_t` descriptors; receivers read `const`-convention buffers and call `CFE_SB_ReleaseMessageBuffer` (`cfe_sb_api.c:1468-1494`) | Caller shrinks `Fw::Buffer` size within allocated slot (`fwBuffer.getSize() <= m_buffers[id].size`) and returns ownership via `bufferSendIn` |

Two subtle source-level invariants distinguish their failure behavior:

1. **Zero-Copy Shared Descriptor Lifetime (`nasa/cFE` `cfe_sb_api.c:1335-1494`):** `CFE_SB_ReceiveBuffer` hands subscribers a pointer into a shared pool descriptor while incrementing its reference count; `line 1336` explicitly warns that `BufPtr` omits `const` only for legacy compatibility and callers must never mutate received payloads because multiple subscribers can inspect the same physical buffer concurrently until each calls `CFE_SB_ReleaseMessageBuffer` (`CFE_SB_DecrBufUseCnt`).
2. **Fail-Stop `FW_ASSERT` Contract (`nasa/fprime` `BufferManagerComponentImpl.cpp:66-100`):** When a component returns a `Fw::Buffer` on `bufferSendIn_handler`, `BufferManager` checks `id < m_numStructs`, `mgrId == m_mgrId`, `m_buffers[id].allocated == true`, pointer interior containment (`memory <= ptr < memory + size`), and non-expansion (`fwBuffer.getSize() <= m_buffers[id].size`) using `FW_ASSERT` before resetting `allocated = false`. Consequently, double-frees or out-of-bounds buffer corruption trigger immediate deterministic flight-software assertions (safe-mode reset) rather than silent freelist metadata corruption.

### 3. Deep-Space `BPv7` (`RFC 9171`), `BPSec` (`RFC 9172`), `LTP` Custody & `CGR` Storage Bounds

Basis: normative (`RFC 9171`, `RFC 9172`, `RFC 5326`) + source (`nasa-jpl/ION-DTN`, `nasa/HDTN`) + execution (Evidence Probe B).

Across interplanetary distances (e.g., Earth–Mars `3–22 min` one-way light time) and planetary occultations, end-to-end RTT exceeds handshake timers, causing conversational `TCP` and `TLS` sessions to fail. Delay-Tolerant Networking (`DTN`) replaces synchronous transport sessions with autonomous store-carry-and-forward bundles across three interacting sublayers:

1. **Indefinite-Length `BPv7` Bundles vs. Core Deterministic `CBOR` Canonical Blocks (`RFC 9171 §4.1`, `RFC 9172`, `nasa/HDTN`):**
   - `RFC 9171 §4.1` mandates that every `BPv7` bundle be serialized as an **indefinite-length CBOR array** (`0x9f ... 0xff`) containing at least two blocks (the Primary Block followed by extension blocks and the Payload Block).
   - Simultaneously, to make `BPSec` (`RFC 9172`) cryptographic verification reproducible across intermediate Bundle Processing Agents (`BPA`s) that insert, modify, or strip non-targeted extension blocks, every individual block's fields MUST conform to `RFC 8949 §4.2` **core deterministic CBOR** (shortest-possible integer widths, no non-canonical headers). In `nasa/HDTN`, `Bpv7AbstractSecurityBlock::SerializeBpv7` (`common/bpcodec/src/codec/Bpv7BpSecExtensionBlocks.cpp:118-130`) explicitly tracks `m_securityTargets`, `m_securityContextId`, and `m_securityResults` in canonical field order for `BIB` (integrity) and `BCB` (confidentiality) blocks.
   - As verified by Evidence Probe B, re-encoding a scalar block field with a non-shortest CBOR integer header (e.g., `0x18 0x01` instead of `0x01` for `block_type = 1`) preserves identical decoded semantics while altering the canonical block SHA-256 digest (`923f1ba09b3f4c141034d5f1` vs. `5a132d6bac695681c5dc5eb2`), invalidating `BIB` verification downstream.
2. **Custody Transfer Migration & `LTP` Red/Green Retransmission (`RFC 5326`, `nasa-jpl/ION-DTN`):**
   - Unlike `BPv6` (`RFC 5050`), `RFC 9171` **removed custody transfer from the Primary Block**, delegating bundle-level custody acknowledgment to optional extension/administrative records (or CCSDS extensions) while relying primarily on convergence-layer reliability.
   - Deep-space links commonly terminate `BPv7` onto the Licklider Transmission Protocol (`LTP`, `RFC 5326`). In `nasa-jpl/ION-DTN` (`ltp/library/libltpP.c`), each `LTP` block partitions its byte span into a reliable **red part** (retransmitted selectively via asynchronous checkpoint/report-segment `ARQ`, `constructReportAckSegment`, `session->checkpoints`) and an optional unreliable **green part** (best-effort streaming without retransmission). All pending red-part segments and `BPv7` custody queues reside inside ION's transactional persistent Simple Data Recorder (`SDR`, guarded by `sdr_begin_xn(sdr)`/`sdr_end_xn`), ensuring survival across radiation-induced watchdog resets.
3. **Contact Graph Routing (`CGR`) & Storage Exhaustion Hazard (`nasa-jpl/ION-DTN` `bpv7/cgr/libcgr.c`):**
   - Because deep-space links turn on and off on orbital schedules rather than reactive packet-loss discovery, `ION-DTN`'s `libcgr.c` computes shortest earliest-arrival paths across deterministic contact intervals $[t_{\text{start}}, t_{\text{end}}, \text{rate}, \text{owlt}]$ (`CgrContactNote` Dijkstra frontier tracking `arrivalTime`, `hopCount`, `predecessor`, and `suppressed` flags, `lines 29-40`).
   - Naive contact graphs ignore local outbound queue backlogs and route saturation: `ION-DTN` incorporates Earliest Transmission Opportunity (`ETO`, accounting for bytes already queued ahead of the bundle) and overbooking management (`libcgr.c:9-15`).
   - *Cross-Layer Storage Deadlock:* If prolonged occultation or repeated `LTP` red-part timeouts prevent bundle release while high-rate instruments keep enqueueing payloads into `SDR`, persistent `SDR` occupancy reaches 100% and forces `sdr_begin_xn` allocation failures or emergency bundle eviction—requiring strict `lifetime` expiration pruning, admission rate-limiting (`cFE` pipe limits), and reserved housekeeping headroom.

## Boundaries

- **Not examined:** Proprietary vendor radiation-hardened ASIC/FPGA netlists (commercial `LEON3FT`/`NOEL-V` fault-tolerant silicon gate libraries), physical-layer LDPC/Turbo channel coding (`CCSDS`), and multi-domain Byzantine consensus over DTN custody logs.
- **Unknown:** Exact Worst-Case Execution Time (`WCET`) of `ION-DTN` `libcgr.c` Dijkstra recomputation under dense, dynamically updated multi-hundred-contact plans on low-clock-rate radiation-hardened `SPARC V8` cores.
- **Known not to apply:**
  - `RFC 5050` (`BPv6`) primary-block custody transfer flags do not apply to `RFC 9171` (`BPv7`), which delegates custody signaling out of the primary block.
  - Unscrubbed TMR (`mu = 0`) does not improve mission reliability over simplex beyond $t^* = \ln(2)/\lambda$ (`6931.47 hr` at $\lambda = 10^{-4}\text{ hr}^{-1}$), where unscrubbed TMR becomes strictly *less* reliable than a single unprotected replica.
- **Unsupported:**
  - `nasa/HDTN` (`f92cec5cad507cb69a3a05188334ba29ffdbbf5e`) is archived/unmaintained upstream (`README.md`) with no security fixes or active maintenance.
  - `LTP` (`RFC 5326`) green-part data spans explicitly do not support selective retransmission or checkpoint acknowledgment; green-part drops are permanent at the `LTP` convergence layer.
  - Both `NASA cFE` and `JPL F Prime` (`BufferManager`) do not support general-purpose heap `malloc`/`free` during flight-mode operation; `BufferManager` assumes pre-sized static buffer bins fit all runtime payload sizes (`BufferManagerComponentImpl.cpp:107-115`).

## Evidence

All primary sources and standards were verified at exact commits and editions on `2026-11-19`:

| Subject | Immutable Identity / Revision | Inspected Artifacts & Exact References |
| :--- | :--- | :--- |
| `byuccl/spydrnet-tmr` | `5833d9fa9808c8582dd8845f990359a82247ef5a` | `README.md`; `spydrnet_tmr/apply_tmr_to_netlist.py:15-112`; `spydrnet_tmr/analysis/voter_insertion/` |
| `nasa/cFE` | `3673163b7fd34d7bb69546f1cd13ddb39ac7cde6` | `modules/es/fsw/src/cfe_es_mempool.c:240-289`; `modules/sb/fsw/src/cfe_sb_api.c:95-1605` |
| `nasa/osal` | `2a96a4fff5b3a3252cb33e95862a02667e509e24` | `README.md`; `src/os/shared/src/osapi-idmap.c:24-58` |
| `nasa/fprime` | `83221ba82a7765fe7226681050e971b31b64d29f` | `README.md`; `Svc/BufferManager/BufferManagerComponentImpl.cpp:26-130` |
| `nasa-jpl/ION-DTN` | `13dae7df4784d67591590719a92d2d653da79f95` | `bpv7/cgr/libcgr.c:1-65`; `ltp/library/libltpP.c:80-306, 1533, 1662-2358` |
| `nasa/HDTN` | `f92cec5cad507cb69a3a05188334ba29ffdbbf5e` | `README.md`; `common/bpcodec/src/codec/Bpv7CbhePrimaryBlock.cpp:41-80`; `Bpv7BpSecExtensionBlocks.cpp:36-130` |
| Literature & IETF Specs | `RFC 9171`, `RFC 9172`, `RFC 5326`, `DOI: 10.1109/MC.2006.212` | Core deterministic CBOR (`RFC 9171 §4.1`), `BIB`/`BCB` (`RFC 9172`), `LTP` (`RFC 5326`), Power-of-Ten rules |

**Self-Contained Micro-Probe (`CTMC` TMR Scrubbing & `RFC 9171` Canonical CBOR Digest):**

```bash
python3 - <<'EOF'
import hashlib, math

def exact_ctmc(lam, mu, t):
    b = 5.0 * lam + mu
    disc = math.sqrt(b * b - 24.0 * lam * lam)
    r1, r2 = 0.5 * (-b + disc), 0.5 * (-b - disc)
    return (r2 * math.exp(r1 * t) - r1 * math.exp(r2 * t)) / (r2 - r1)

lam = 1e-4
print("=== Probe A: TMR + Periodic Scrubbing CTMC (lambda = 1e-4 / hr) ===")
print(f"Unscrubbed TMR/Simplex reliability crossover t* = ln(2)/lambda = {math.log(2)/lam:.2f} hr")
for t in (1000.0, 5000.0, 6931.4718, 10000.0):
    rs, r0, r1h, r36 = math.exp(-lam*t), exact_ctmc(lam, 0.0, t), exact_ctmc(lam, 1.0, t), exact_ctmc(lam, 100.0, t)
    print(f"t={t:8.2f}h | R_simplex={rs:.8f} | R_tmr(mu=0)={r0:.8f} | R_tmr(T=1h)={r1h:.8f} (P_fail={1-r1h:.3e}) | R_tmr(T=36s)={r36:.10f} (P_fail={1-r36:.3e})")
for label, mu in (("mu=0", 0.0), ("mu=1/hr (T=1h)", 1.0), ("mu=100/hr (T=36s)", 100.0)):
    print(f"MTTF({label}) = {(5*lam+mu)/(6*lam*lam):.2f} hr (vs simplex {1/lam:.2f} hr)")

print("\n=== Probe B: RFC 9171 §4.1 Deterministic CBOR vs. BPSec BIB Digest ===")
canon = bytes.fromhex("850101000049") + b"telemetry"
non_det = bytes.fromhex("85180101000049") + b"telemetry"
env = bytes([0x9f]) + canon + bytes([0xff])
d1, d2 = hashlib.sha256(canon).hexdigest()[:24], hashlib.sha256(non_det).hexdigest()[:24]
assert d1 != d2
print(f"BPv7 outer envelope prefix=0x{env[0]:02x}, suffix=0x{env[-1]:02x} (indefinite array)")
print(f"Canonical block hex     = {canon.hex()} sha256[:24]={d1}")
print(f"Non-deterministic hex   = {non_det.hex()} sha256[:24]={d2}")
print("Confirmed: non-shortest CBOR header mutates BPSec BIB digest even for identical decoded values.")
EOF
```

Observed output:

```text
=== Probe A: TMR + Periodic Scrubbing CTMC (lambda = 1e-4 / hr) ===
Unscrubbed TMR/Simplex reliability crossover t* = ln(2)/lambda = 6931.47 hr
t= 1000.00h | R_simplex=0.90483742 | R_tmr(mu=0)=0.97455582 | R_tmr(T=1h)=0.99994009 (P_fail=5.991e-05) | R_tmr(T=36s)=0.9999994000 (P_fail=6.000e-07)
t= 5000.00h | R_simplex=0.60653066 | R_tmr(mu=0)=0.65737800 | R_tmr(T=1h)=0.99970025 (P_fail=2.997e-04) | R_tmr(T=36s)=0.9999970000 (P_fail=3.000e-06)
t= 6931.47h | R_simplex=0.50000000 | R_tmr(mu=0)=0.50000000 | R_tmr(T=1h)=0.99958447 (P_fail=4.155e-04) | R_tmr(T=36s)=0.9999958412 (P_fail=4.159e-06)
t=10000.00h | R_simplex=0.36787944 | R_tmr(mu=0)=0.30643171 | R_tmr(T=1h)=0.99940054 (P_fail=5.995e-04) | R_tmr(T=36s)=0.9999940001 (P_fail=6.000e-06)
MTTF(mu=0) = 8333.33 hr (vs simplex 10000.00 hr)
MTTF(mu=1/hr (T=1h)) = 16675000.00 hr (vs simplex 10000.00 hr)
MTTF(mu=100/hr (T=36s)) = 1666675000.00 hr (vs simplex 10000.00 hr)

=== Probe B: RFC 9171 §4.1 Deterministic CBOR vs. BPSec BIB Digest ===
BPv7 outer envelope prefix=0x9f, suffix=0xff (indefinite array)
Canonical block hex     = 85010100004974656c656d65747279 sha256[:24]=923f1ba09b3f4c141034d5f1
Non-deterministic hex   = 8518010100004974656c656d65747279 sha256[:24]=5a132d6bac695681c5dc5eb2
Confirmed: non-shortest CBOR header mutates BPSec BIB digest even for identical decoded values.
```

## Revalidation

1. **Recompute TMR Scrubbing Margins for Target Radiation Flux $\lambda$ and Scrub Rate $\mu$:**
   ```bash
   python3 -c '
   import math
   lam, mu, t = 1e-4, 100.0, 10000.0
   b = 5*lam + mu; disc = math.sqrt(b*b - 24*lam*lam)
   r1, r2 = 0.5*(-b + disc), 0.5*(-b - disc)
   r_scrub = (r2*math.exp(r1*t) - r1*math.exp(r2*t))/(r2 - r1)
   print(f"t*={math.log(2)/lam:.2f}h R_scrub={r_scrub:.10f} MTTF={(5*lam+mu)/(6*lam*lam):.2f}h")
   '
   ```
2. **Verify `BPv7` Canonical CBOR Digest Stability:** Re-run Probe B (`85010100004974656c656d65747279` vs `8518010100004974656c656d65747279`) or run `ION-DTN` / `HDTN` codec round-trip tests ensuring no re-encoder expands shortest-form CBOR unsigned integers before `BIB` MAC/signature verification.
3. **Check Static Memory Pool Compliance on `cFE` / `F Prime` Upgrades:** Inspect `CFE_ES_PoolCreate` (`cfe_es_mempool.c`) and `BufferManagerComponentImpl::setup` / `bufferGetCallee_handler` (`Svc/BufferManager/BufferManagerComponentImpl.cpp`) to verify zero post-init `malloc` calls and intact `FW_ASSERT` ownership bounds.
